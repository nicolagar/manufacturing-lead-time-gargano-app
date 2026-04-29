
(function(global){
  function uniqSorted(nums){ return [...new Set(nums)].sort((a,b)=>a-b); }

  function buildHierarchy(schedule){
    const byParent={};
    (schedule||[]).forEach(r=>{
      const p=r.refines||'';
      (byParent[p]||(byParent[p]=[])).push(r);
    });
    Object.values(byParent).forEach(arr=>arr.sort((a,b)=>(a.earliest_start??0)-(b.earliest_start??0)||String(a.process).localeCompare(String(b.process))));
    return byParent;
  }

  function edgesForParent(graph, scheduleMap, parent){
    return (graph.edges||[]).filter(e => (scheduleMap[e.from]?.refines||'')===parent && (scheduleMap[e.to]?.refines||'')===parent);
  }

  function buildMaps(rows, edges){
    const ids=rows.map(r=>r.process);
    const preds={}, succs={};
    ids.forEach(id=>{preds[id]=[]; succs[id]=[];});
    edges.forEach(e=>{
      if(preds[e.to] && succs[e.from]){
        preds[e.to].push(e.from);
        succs[e.from].push(e.to);
      }
    });
    return {preds,succs};
  }

  function computeLevels(rows, edges, childCounts){
    const {preds,succs}=buildMaps(rows, edges);
    const levels={};
    const queue=rows.map(r=>r.process).filter(id=>preds[id].length===0).sort();
    queue.forEach(id=>levels[id]=0);
    while(queue.length){
      const id=queue.shift();
      succs[id].forEach(nxt=>{
        levels[nxt]=Math.max(levels[nxt]??0, (levels[id]??0)+1);
        preds[nxt]=preds[nxt].filter(x=>x!==id);
        if(preds[nxt].length===0) queue.push(nxt);
      });
    }
    rows.forEach(r=>{ if(levels[r.process]===undefined) levels[r.process]=0; });

    // leaf sinks with no children shift one extra level right so they do not align with sink-parents
    const {succs:succMap}=buildMaps(rows, edges);
    const anyChildful = rows.some(r => (childCounts[r.process]||0) > 0);
    rows.forEach(r=>{
      if((succMap[r.process]||[]).length===0 && (childCounts[r.process]||0)===0 && anyChildful){
        levels[r.process] += 1;
      }
    });
    return levels;
  }

  function computeChildLanes(rows, edges, childCounts){
    const {preds}=buildMaps(rows, edges);
    const levels=computeLevels(rows, edges, childCounts||{});
    const rowsByLevel={};
    rows.forEach(r=>{ const lvl=levels[r.process]||0; (rowsByLevel[lvl]||(rowsByLevel[lvl]=[])).push(r.process); });
    const lane={}, used={};
    Object.keys(rowsByLevel).map(Number).sort((a,b)=>a-b).forEach(lvl=>{
      rowsByLevel[lvl].sort();
      rowsByLevel[lvl].forEach(id=>{
        const ps=(preds[id]||[]).filter(p=>lane[p]!==undefined);
        let pref=ps.length ? Math.round(ps.reduce((s,p)=>s+lane[p],0)/ps.length) : 0;
        let ln=pref;
        while((used[lvl]||(used[lvl]=new Set())).has(ln)) ln++;
        used[lvl].add(ln);
        lane[id]=ln;
      });
    });
    return {levels, lanes: lane};
  }

  function computeTopLevelLanes(rows, edges, dominantPath){
    const {preds,succs}=buildMaps(rows, edges);
    const levels=computeLevels(rows, edges, {});
    const rowMap={}; rows.forEach(r=>{ rowMap[r.process]=r; });
    const ids=rows.map(r=>r.process);
    const desired={};
    const dominant = new Set(dominantPath || []);

    const roots=ids.filter(id=>(preds[id]||[]).length===0).sort((a,b)=>{
      const da = dominant.has(a) ? 0 : 1;
      const db = dominant.has(b) ? 0 : 1;
      return da-db || (rowMap[a].earliest_start??0)-(rowMap[b].earliest_start??0) || a.localeCompare(b);
    });

    let nextRootLane=2;
    roots.forEach(id=>{
      if(desired[id]!==undefined) return;
      if(dominant.has(id)) desired[id]=0;
      else desired[id]=nextRootLane++;
    });

    const topo=ids.slice().sort((a,b)=>
      (levels[a]||0)-(levels[b]||0) ||
      (rowMap[a].earliest_start??0)-(rowMap[b].earliest_start??0) ||
      a.localeCompare(b)
    );

    topo.forEach(id=>{
      if(desired[id]===undefined){
        const parentLanes=(preds[id]||[]).filter(p=>desired[p]!==undefined).map(p=>desired[p]);
        desired[id]=parentLanes.length ? Math.min(...parentLanes) : nextRootLane++;
      }
      const outs=(succs[id]||[]).slice().sort((a,b)=>
        (rowMap[a].earliest_start??0)-(rowMap[b].earliest_start??0) || a.localeCompare(b)
      );
      outs.forEach((sid, idx)=>{
        const proposal = outs.length===1 ? desired[id] : desired[id] + idx;
        if(desired[sid]===undefined) desired[sid]=proposal;
        else desired[sid]=Math.min(desired[sid], proposal);
      });
    });

    const lane={}, used={};
    topo.forEach(id=>{
      const lvl=levels[id]||0;
      const usedSet=(used[lvl]||(used[lvl]=new Set()));
      let ln=desired[id]??0;
      const ps=preds[id]||[];
      if(ps.length===1){
        const pred=ps[0];
        if((succs[pred]||[]).length===1 && lane[pred]!==undefined){
          ln=lane[pred];
        }
      }
      while(usedSet.has(ln)) ln++;
      usedSet.add(ln);
      lane[id]=ln;
    });

    return lane;
  }

  function descendantsOf(root, byParent){
    const out=new Set();
    function dfs(p){
      (byParent[p]||[]).forEach(r=>{
        out.add(r.process);
        dfs(r.process);
      });
    }
    dfs(root);
    return out;
  }

  function rect(x,y,w,h,depth,parent){ return {x,y,w,h,depth,parent}; }
  function rightMid(b){ return {x:b.x+b.w, y:b.y+b.h/2}; }
  function leftMid(b){ return {x:b.x, y:b.y+b.h/2}; }
  function topAnchor(b,slot,total){
    const span=Math.max(24,b.w*0.55), start=b.x+(b.w-span)/2, step=total>1?span/(total-1):0;
    return {x:start+slot*step, y:b.y};
  }
  function bottomAnchor(b,slot,total){
    const span=Math.max(24,b.w*0.55), start=b.x+(b.w-span)/2, step=total>1?span/(total-1):0;
    return {x:start+slot*step, y:b.y+b.h};
  }
  function rectContainsPoint(rc, p, pad=0){
    return p.x > rc.x+pad && p.x < rc.x+rc.w-pad && p.y > rc.y+pad && p.y < rc.y+rc.h-pad;
  }
  function segIntersectsRect(a,b,rc,pad=0){
    if(a.x===b.x){
      const x=a.x, y0=Math.min(a.y,b.y), y1=Math.max(a.y,b.y);
      return x>rc.x+pad && x<rc.x+rc.w-pad && !(y1<=rc.y+pad || y0>=rc.y+rc.h-pad);
    }
    if(a.y===b.y){
      const y=a.y, x0=Math.min(a.x,b.x), x1=Math.max(a.x,b.x);
      return y>rc.y+pad && y<rc.y+rc.h-pad && !(x1<=rc.x+pad || x0>=rc.x+rc.w-pad);
    }
    return true;
  }
  function pathIntersectsRects(points, rects, pad=2){
    for(let i=0;i<points.length-1;i++){
      for(const rc of rects){
        if(segIntersectsRect(points[i], points[i+1], rc, pad)) return true;
      }
    }
    return false;
  }
  function simplify(points){
    const out=[points[0]];
    for(let i=1;i<points.length;i++){
      const p=points[i], q=out[out.length-1];
      if(p.x!==q.x || p.y!==q.y) out.push(p);
    }
    return out;
  }
  function samePoint(a,b){ return a.x===b.x && a.y===b.y; }

  
  function rectsOverlap(a,b,pad=0){
    return !(a.x+a.w+pad <= b.x || b.x+b.w+pad <= a.x || a.y+a.h+pad <= b.y || b.y+b.h+pad <= a.y);
  }

  function isAncestorBox(boxes, anc, node){
    let cur = boxes[node] ? (boxes[node].parent||'') : '';
    while(cur){
      if(cur===anc) return true;
      cur = boxes[cur] ? (boxes[cur].parent||'') : '';
    }
    return false;
  }

  function resolveBoxOverlaps(boxes, containers, shiftFn){
    const ids = Object.keys(boxes);
    let changed=true, guard=0;
    while(changed && guard < 30){
      changed=false; guard++;
      for(let i=0;i<ids.length;i++){
        for(let j=i+1;j<ids.length;j++){
          const a=ids[i], b=ids[j];
          const A=boxes[a], B=boxes[b];
          if(!A || !B) continue;
          if(isAncestorBox(boxes,a,b) || isAncestorBox(boxes,b,a)) continue;
          if(!rectsOverlap(A,B,6)) continue;

          // keep x/order stable; separate vertically by moving the later/lower-priority box downward
          const moveId = (A.y < B.y || (A.y===B.y && A.x <= B.x)) ? b : a;
          const stayId = moveId===b ? a : b;
          const stay = boxes[stayId], move = boxes[moveId];
          const dy = (stay.y + stay.h + 28) - move.y;
          shiftFn(moveId, 0, dy);
          changed=true;
        }
      }
    }

    // refresh container extents after shifts
    Object.keys(containers).forEach(pid=>{
      const node=boxes[pid];
      if(!node) return;
      const desc = Object.keys(boxes).filter(id => isAncestorBox(boxes, pid, id));
      if(!desc.length) return;
      const c=containers[pid];
      const right = Math.max(node.x+node.w, ...desc.map(id=>boxes[id].x+boxes[id].w)) + 12;
      const bottom = Math.max(node.y+node.h+90, ...desc.map(id=>boxes[id].y+boxes[id].h)) + 12;
      const left = Math.min(node.x-12, ...desc.map(id=>boxes[id].x-12));
      const top = Math.min(node.y-10, c.y);
      containers[pid] = {...c, x:left, y:top, w:right-left, h:bottom-top};
    });
  }

function buildRecursiveRouteModel(data){
    const schedule=data.schedule||[];
    const scheduleMap={}; schedule.forEach(r=>scheduleMap[r.process]=r);
    const graph=data.graph||{edges:[]};
    const byParent=buildHierarchy(schedule);
    const childCounts={};
    Object.keys(byParent).forEach(k=>{ childCounts[k]=byParent[k].length; });

    const dominantPath=(data.dominant_path||[]).slice();
    const dominantEdges=(data.critical_edges||[]).map(e=>`${e.from}__${e.to}`);

    const boxes={};         // process -> top-left rect
    const containers={};    // process -> top-left container rect
    const routes=[];

    function shiftSubtree(root, dx, dy){
      const desc=descendantsOf(root, byParent);
      desc.add(root);
      desc.forEach(id=>{
        if(boxes[id]){ boxes[id].x += dx; boxes[id].y += dy; }
        if(containers[id]){ containers[id].x += dx; containers[id].y += dy; }
      });
      routes.forEach(r=>{
        if(desc.has(r.from) || desc.has(r.to)){
          r.points = r.points.map(p=>({x:p.x+dx, y:p.y+dy}));
        }
      });
    }

    function rectsOverlap(a,b,pad=0){
      return !(a.x + a.w + pad <= b.x || b.x + b.w + pad <= a.x || a.y + a.h + pad <= b.y || b.y + b.h + pad <= a.y);
    }
    function isAncestorNode(anc, node){
      let cur = boxes[node] ? (boxes[node].parent||'') : '';
      while(cur){
        if(cur===anc) return true;
        cur = boxes[cur] ? (boxes[cur].parent||'') : '';
      }
      return false;
    }
    function relatedNodes(a,b){
      return a===b || isAncestorNode(a,b) || isAncestorNode(b,a);
    }
    function resolveProcessOverlaps(maxPasses=40){
      const gapX=36, gapY=36;
      let moved=false;
      for(let pass=0; pass<maxPasses; pass++){
        let changed=false;
        const ids=Object.keys(boxes).sort((ida,idb)=>
          (boxes[ida].depth||0)-(boxes[idb].depth||0) ||
          boxes[ida].y-boxes[idb].y ||
          boxes[ida].x-boxes[idb].x ||
          ida.localeCompare(idb)
        );
        for(let i=0;i<ids.length;i++){
          for(let j=i+1;j<ids.length;j++){
            const a=ids[i], b=ids[j];
            if(relatedNodes(a,b)) continue;
            if(!boxes[a] || !boxes[b]) continue;
            if(!rectsOverlap(boxes[a], boxes[b], 0)) continue;

            const sameParent = (boxes[a].parent||'') === (boxes[b].parent||'');
            const moveId = b;
            const move = boxes[moveId];
            const other = boxes[a];

            let dx=0, dy=0;
            if(sameParent){
              // prefer vertical separation inside the same scope to preserve left-to-right reading order
              dy = (other.y + other.h + gapY) - move.y;
              if(dy < 0) dy = 0;
            } else {
              // for unrelated different-scope boxes, prefer moving right if possible, else down
              dx = (other.x + other.w + gapX) - move.x;
              if(dx < 0) dx = 0;
              if(dx === 0){
                dy = (other.y + other.h + gapY) - move.y;
                if(dy < 0) dy = 0;
              }
            }
            if(dx!==0 || dy!==0){
              shiftSubtree(moveId, dx, dy);
              changed=true;
              moved=true;
            }
          }
        }
        if(!changed) break;
      }
      return moved;
    }

    function layoutLevel(parentKey, originX, originY, depth){
      const rows=(byParent[parentKey]||[]).slice();
      if(!rows.length) return {w:0,h:0};

      const edges=edgesForParent(graph, scheduleMap, parentKey);
      const cardW=depth===0 ? 176 : depth===1 ? 148 : 108;
      const cardH=depth===0 ? 76 : depth===1 ? 64 : 56;
      const colGap=depth===0 ? 260 : depth===1 ? 80 : 26;
      const laneGap=depth===0 ? 110 : depth===1 ? 56 : 34;
      const marginX=depth===0 ? 60 : 18;
      const marginY=depth===0 ? 60 : 20;
      const childIndent=depth===0 ? 24 : 14;
      const childTopGap=depth===0 ? 48 : 24;
      const containerPad=depth===0 ? 12 : 8;
      const headerPad=depth===0 ? 18 : 14;

      let levels, lanes;
      if(parentKey===''){
        levels=computeLevels(rows, edges, childCounts);
        lanes=computeTopLevelLanes(rows, edges, dominantPath);
      } else {
        const tmp=computeChildLanes(rows, edges, childCounts);
        levels=tmp.levels; lanes=tmp.lanes;
      }

      // place boxes
      let maxRight=0, maxBottom=0;
      rows.forEach(r=>{
        const id=r.process;
        const x=originX + marginX + (levels[id]||0)*(cardW+colGap);
        const y=originY + marginY + (lanes[id]||0)*(cardH+laneGap);
        boxes[id]=rect(x,y,cardW,cardH,depth,parentKey);
        maxRight=Math.max(maxRight, x+cardW);
        maxBottom=Math.max(maxBottom, y+cardH);
      });

      // recursively place children and containers
      rows.forEach(r=>{
        const id=r.process;
        const kids=(byParent[id]||[]).slice();
        if(!kids.length) return;
        const node=boxes[id];
        const childOriginX=node.x + childIndent;
        const childOriginY=node.y + node.h + childTopGap;
        const childDims=layoutLevel(id, childOriginX, childOriginY, depth+1);

        // tight container around node and direct child region only
        const directIds=kids.map(k=>k.process);
        const directBoxes=directIds.map(cid=>boxes[cid]).filter(Boolean);
        const directContainers=directIds.map(cid=>containers[cid]).filter(Boolean);
        const left=Math.min(node.x, ...(directBoxes.map(b=>b.x)), ...(directContainers.map(c=>c.x))) - containerPad;
        const top=node.y - containerPad;
        const right=Math.max(node.x+node.w, ...(directBoxes.map(b=>b.x+b.w)), ...(directContainers.map(c=>c.x+c.w))) + containerPad;
        const bottom=Math.max(node.y+node.h, ...(directBoxes.map(b=>b.y+b.h)), ...(directContainers.map(c=>c.y+c.h))) + containerPad;
        containers[id]={x:left,y:top,w:right-left,h:bottom-top,headerH:node.h+headerPad,depth:depth+1,parent:parentKey};
        maxRight=Math.max(maxRight,right);
        maxBottom=Math.max(maxBottom,bottom);
      });

      // top-level separation rules after container sizes known
      if(parentKey===''){
        const topIds=rows.map(r=>r.process);
        const domTop=dominantPath.filter(id=>topIds.includes(id));
        // Keep dominant path on upper lane and ensure successor after childful parent starts right of container
        for(let i=0;i<domTop.length-1;i++){
          const a=domTop[i], b=domTop[i+1];
          if(!boxes[a] || !boxes[b]) continue;
          const aBox=boxes[a];
          const aContainer=containers[a];
          const requiredX=(aContainer ? aContainer.x+aContainer.w+90 : aBox.x+aBox.w+90);
          if(boxes[b].x < requiredX){
            shiftSubtree(b, requiredX-boxes[b].x, aBox.y-boxes[b].y);
          } else if(boxes[b].y !== aBox.y){
            shiftSubtree(b, 0, aBox.y-boxes[b].y);
          }
        }
        // Non-dominant top-level boxes that overlap childful parent containers go below them
        topIds.forEach(id=>{
          if(dominantPath.includes(id)) return;
          rows.forEach(r=>{
            const pid=r.process;
            if(id===pid) return;
            if((byParent[pid]||[]).length===0) return;
            const desc=descendantsOf(pid, byParent);
            if(desc.has(id)) return;
            const c=containers[pid];
            if(!c || !boxes[id]) return;
            const b=boxes[id];
            const overlapX = !(b.x+b.w <= c.x-30 || b.x >= c.x+c.w+30);
            const overlapY = !(b.y+b.h <= c.y-30 || b.y >= c.y+c.h+30);
            if(overlapX && overlapY){
              const newY = c.y + c.h + 70;
              shiftSubtree(id, 0, newY - b.y);
            }
          });
        });
        // specifically move merge feeder branches lower if they end at a dominant node to keep parent corridor clean
        edges.forEach(e=>{
          if(!dominantPath.includes(e.from) && dominantPath.includes(e.to)){
            const target=boxes[e.to], source=boxes[e.from];
            if(source && target && source.y < target.y + 90){
              shiftSubtree(e.from, 0, (target.y + 150) - source.y);
            }
          }
        });
        // update max extents
        maxRight=Math.max(...Object.values(boxes).filter(b=>b.parent==='').map(b=>b.x+b.w).concat(Object.values(containers).filter(c=>c.parent==='').map(c=>c.x+c.w), [maxRight]));
        maxBottom=Math.max(...Object.values(boxes).filter(b=>b.parent==='').map(b=>b.y+b.h).concat(Object.values(containers).filter(c=>c.parent==='').map(c=>c.y+c.h), [maxBottom]));
      }

      // hard non-overlap rule for all non-ancestor process boxes
      resolveBoxOverlaps(boxes, containers, shiftSubtree);
      maxRight=Math.max(maxRight, ...Object.values(boxes).map(b=>b.x+b.w), ...Object.values(containers).map(c=>c.x+c.w));
      maxBottom=Math.max(maxBottom, ...Object.values(boxes).map(b=>b.y+b.h), ...Object.values(containers).map(c=>c.y+c.h));

      // routing assignments for this level
      const localBoxes=rows.map(r=>boxes[r.process]);
      const {preds,succs}=buildMaps(rows, edges);
      const incomingByTarget={};
      const outgoingBySource={};
      edges.forEach(e=>{
        (incomingByTarget[e.to]||(incomingByTarget[e.to]=[])).push(e);
        (outgoingBySource[e.from]||(outgoingBySource[e.from]=[])).push(e);
      });

      const assignments={};
      Object.entries(incomingByTarget).forEach(([target, arr])=>{
        const tgt=boxes[target];
        const tgtCy=tgt.y+tgt.h/2;
        const buckets={top:[], left:[], bottom:[]};
        arr.forEach(e=>{
          const src=boxes[e.from];
          const srcCy=src.y+src.h/2;
          if(arr.length===1) buckets.left.push(e);
          else if(srcCy < tgtCy-20) buckets.top.push(e);
          else if(srcCy > tgtCy+20) buckets.bottom.push(e);
          else buckets.left.push(e);
        });
        if(arr.length>1 && buckets.left.length===0){
          if(buckets.bottom.length) buckets.left.push(buckets.bottom.shift());
          else if(buckets.top.length) buckets.left.push(buckets.top.shift());
        }
        ['top','left','bottom'].forEach(side=>{
          const total=buckets[side].length;
          buckets[side].forEach((e,idx)=>{
            const key=`${e.from}__${e.to}`;
            const prev=assignments[key]||{};
            assignments[key]={...prev, side, slotIn:idx, totalIn:total};
          });
        });
      });
      Object.entries(outgoingBySource).forEach(([source, arr])=>{
        arr.sort((a,b)=>{
          const ay=boxes[a.to].y+boxes[a.to].h/2;
          const by=boxes[b.to].y+boxes[b.to].h/2;
          return ay-by || String(a.to).localeCompare(String(b.to));
        });
        arr.forEach((e,idx)=>{
          const key=`${e.from}__${e.to}`;
          const prev=assignments[key]||{};
          assignments[key]={...prev, succIndex:idx, succTotal:arr.length};
        });
      });

      function leftSlotAnchor(b, slot, total){
        if(total<=1) return {x:b.x, y:b.y+b.h/2};
        const span=Math.max(18, Math.min(b.h-12, b.h*0.60));
        const startY=b.y+(b.h-span)/2;
        const step=total>1 ? span/(total-1) : 0;
        return {x:b.x, y:startY + slot*step};
      }

      function forbiddenRectsFor(edge){
        const from=edge.from, to=edge.to;
        const rects=[];
        rows.forEach(r=>{
          const id=r.process;
          if(id===from || id===to) return;
          rects.push(boxes[id]);
        });
        rows.forEach(r=>{
          const id=r.process;
          if(id===from || id===to) return;
          if(containers[id]) rects.push(containers[id]);
        });
        return rects.filter(Boolean);
      }

function routeEdge(edge){
  const from=boxes[edge.from], to=boxes[edge.to];
  const assign=assignments[`${edge.from}__${edge.to}`] || {side:'left',slotIn:0,totalIn:1,succIndex:0,succTotal:1,midShift:0,corridorShift:0};

  const multiOut = (assign.succTotal||1) > 1;
  const startYOffset = multiOut ? Math.min(14, (assign.succIndex||0) * 8) : 0;
  const start = {x: from.x + from.w, y: clamp(from.y + from.h/2 + startYOffset, from.y+6, from.y+from.h-6)};
  let end;
  if(assign.side==='left') end=leftSlotAnchor(to, assign.slotIn||0, assign.totalIn||1);
  else if(assign.side==='top') end=topAnchor(to, assign.slotIn||0, Math.max(assign.totalIn||1, 1));
  else end=bottomAnchor(to, assign.slotIn||0, Math.max(assign.totalIn||1, 1));

  // dedicated parent header corridor for parent-with-children top-level continuation
  if(parentKey==='' && (byParent[edge.from]||[]).length>0 && dominantPath.includes(edge.from) && dominantPath.includes(edge.to)){
    const c=containers[edge.from];
    const corridorY = c ? c.y + 18 : start.y;
    const midX = Math.max(start.x + 24, to.x - 70) + (assign.midShift||0);
    return simplify([start, {x:midX,y:start.y}, {x:midX,y:corridorY}, {x:to.x-50,y:corridorY}, {x:to.x-50,y:end.y}, end]);
  }

  const obstacles=forbiddenRectsFor(edge);
  const attempts=[];
  const midShift = assign.midShift || 0;
  const corridorShift = assign.corridorShift || 0;
  const sameHeight = Math.abs(start.y - end.y) < 8;
  const side = assign.side;

  if(side==='left'){
    const splitX = start.x + 38 + (assign.succIndex||0)*26 + midShift;
    const targetMidX = end.x - 28;

    // horizontal tree layout preference:
    // one successor -> successor on same height
    // more than one successor -> first same height, others below
    if((assign.succTotal||1)===1){
      if(sameHeight){
        attempts.push(simplify([start, {x:end.x, y:start.y}, end]));
      }
      attempts.push(simplify([start, {x:splitX,y:start.y}, {x:splitX,y:end.y}, end]));
    } else {
      if((assign.succIndex||0)===0){
        // first successor stays aligned with predecessor if possible
        if(sameHeight){
          attempts.push(simplify([start, {x:end.x, y:start.y}, end]));
        }
        attempts.push(simplify([start, {x:splitX,y:start.y}, {x:splitX,y:end.y}, end]));
      } else {
        // additional successors branch downward into their own horizontal lane
        const branchY = Math.max(start.y, end.y) + 36 + (assign.succIndex||0)*18 + Math.max(0,corridorShift);
        attempts.push(simplify([start, {x:splitX,y:start.y}, {x:splitX,y:branchY}, {x:targetMidX,y:branchY}, {x:targetMidX,y:end.y}, end]));
        const lowerY = branchY + 28;
        attempts.push(simplify([start, {x:splitX+18,y:start.y}, {x:splitX+18,y:lowerY}, {x:targetMidX,y:lowerY}, {x:targetMidX,y:end.y}, end]));
      }
    }

    // generic fallback upper/lower corridors
    const lowerLane = Math.max(start.y,end.y) + 40 + Math.max(0, corridorShift);
    attempts.push(simplify([start, {x:start.x+40,y:start.y}, {x:start.x+40,y:lowerLane}, {x:targetMidX,y:lowerLane}, {x:targetMidX,y:end.y}, end]));
    const upperLane = Math.min(start.y,end.y) - 40 - Math.max(0, -corridorShift);
    attempts.push(simplify([start, {x:start.x+40,y:start.y}, {x:start.x+40,y:upperLane}, {x:targetMidX,y:upperLane}, {x:targetMidX,y:end.y}, end]));
  } else if(side==='top'){
    const ay = to.y - 38 - (assign.slotIn||0)*14 - corridorShift;
    const bx = Math.max(start.x+40, end.x - 30) + midShift;
    attempts.push(simplify([start, {x:bx,y:start.y}, {x:bx,y:ay}, {x:end.x,y:ay}, end]));
    attempts.push(simplify([start, {x:start.x+40+midShift,y:start.y}, {x:start.x+40+midShift,y:ay}, {x:end.x,y:ay}, end]));
  } else {
    const ay = to.y + to.h + 38 + (assign.slotIn||0)*14 + corridorShift;
    const bx = Math.max(start.x+40, end.x - 30) + midShift;
    attempts.push(simplify([start, {x:bx,y:start.y}, {x:bx,y:ay}, {x:end.x,y:ay}, end]));
    attempts.push(simplify([start, {x:start.x+40+midShift,y:start.y}, {x:start.x+40+midShift,y:ay}, {x:end.x,y:ay}, end]));
  }

  for(const pts of attempts){
    if(!pathIntersectsRects(pts, obstacles, 2)) return pts;
  }
  return attempts[0];
}

const localRoutes={};
edges.forEach(e=>{ localRoutes[`${e.from}__${e.to}`]=routeEdge(e); });

// crossing repair priority:
// 1) different target side
// 2) different reserved vertical lane
// 3) different reserved horizontal corridor
// 4) slight node movement
function pathSegs(points){ const arr=[]; for(let i=0;i<points.length-1;i++) arr.push([points[i],points[i+1]]); return arr; }
function segConflict(s1,s2){
  const [a,b]=s1,[c,d]=s2;
  const aV=a.x===b.x, cV=c.x===d.x;
  if(aV!==cV){
    const v=aV?[a,b]:[c,d], h=aV?[c,d]:[a,b];
    const vx=v[0].x, hy=h[0].y;
    const vy0=Math.min(v[0].y,v[1].y), vy1=Math.max(v[0].y,v[1].y);
    const hx0=Math.min(h[0].x,h[1].x), hx1=Math.max(h[0].x,h[1].x);
    return vx>hx0 && vx<hx1 && hy>vy0 && hy<vy1;
  }
  if(aV && cV && a.x===c.x){
    const a0=Math.min(a.y,b.y), a1=Math.max(a.y,b.y);
    const c0=Math.min(c.y,d.y), c1=Math.max(c.y,d.y);
    return Math.min(a1,c1) - Math.max(a0,c0) > 1;
  }
  if(!aV && !cV && a.y===c.y){
    const a0=Math.min(a.x,b.x), a1=Math.max(a.x,b.x);
    const c0=Math.min(c.x,d.x), c1=Math.max(c.x,d.x);
    return Math.min(a1,c1) - Math.max(a0,c0) > 1;
  }
  return false;
}
function validateLocal(){
  const keys=Object.keys(localRoutes);
  for(let i=0;i<keys.length;i++){
    for(let j=i+1;j<keys.length;j++){
      const a=pathSegs(localRoutes[keys[i]]), b=pathSegs(localRoutes[keys[j]]);
      for(const sa of a){ for(const sb of b){ if(segConflict(sa,sb)) return {ok:false,a:keys[i],b:keys[j]}; } }
    }
  }
  return {ok:true};
}
function routeCrossesOthers(key, pts){
  const segA = pathSegs(pts);
  return Object.keys(localRoutes).some(otherKey=>{
    if(otherKey===key) return false;
    const segB=pathSegs(localRoutes[otherKey]);
    for(const sa of segA){ for(const sb of segB){ if(segConflict(sa,sb)) return true; } }
    return false;
  });
}
function edgePriority(key){
  let score=0;
  if(dominantEdges.includes(key)) score += 1000;
  const [f,t]=key.split('__');
  if(dominantPath.includes(f)) score += 200;
  if(dominantPath.includes(t)) score += 100;
  return score;
}
function tryCandidate(key, patch){
  const prev = assignments[key] || {side:'left',slotIn:0,totalIn:1,succIndex:0,succTotal:1,midShift:0,corridorShift:0};
  assignments[key] = {...prev, ...patch};
  const [f,t]=key.split('__');
  const pts = routeEdge({from:f,to:t});
  if(!routeCrossesOthers(key, pts)){
    localRoutes[key] = pts;
    return true;
  }
  assignments[key] = prev;
  return false;
}
function rerouteKey(key){
  const [f,t]=key.split('__');
  localRoutes[key] = routeEdge({from:f,to:t});
}
for(let rep=0; rep<30; rep++){
  const chk=validateLocal();
  if(chk.ok) break;

  const loser = edgePriority(chk.a) <= edgePriority(chk.b) ? chk.a : chk.b;
  const [f,t]=loser.split('__');
  const current = assignments[loser] || {side:'left',slotIn:0,totalIn:1,succIndex:0,succTotal:1,midShift:0,corridorShift:0};

  let resolved=false;

  // 1) different target side
  const sideOrder = ['left','top','bottom'].filter(s=>s!==current.side);
  for(const side of sideOrder){
    if(tryCandidate(loser, {side, slotIn:0, midShift:0, corridorShift:0})){ resolved=true; break; }
  }
  if(resolved) continue;

  // 2) different reserved vertical lane
  for(const midShift of [-180,-120,-60,60,120,180]){
    if(tryCandidate(loser, {side: current.side, midShift, corridorShift: current.corridorShift||0})){ resolved=true; break; }
  }
  if(resolved) continue;

  // 3) different reserved horizontal corridor
  for(const corridorShift of [60,120,180,-60,-120,-180]){
    if(tryCandidate(loser, {side: current.side, midShift: current.midShift||0, corridorShift})){ resolved=true; break; }
  }
  if(resolved) continue;

  // 4) slight node movement then reroute edges touching the moved node
  const moveNode = boxes[t] ? t : f;
  const beforeY = boxes[moveNode] ? boxes[moveNode].y : 0;
  shiftSubtree(moveNode, 0, 72);
  edges.forEach(e=>{
    if(e.from===moveNode || e.to===moveNode){
      rerouteKey(`${e.from}__${e.to}`);
    }
  });

  const post = validateLocal();
  if(post.ok) break;

  // if downward move did not help enough, try a small right shift too
  if(beforeY === (boxes[moveNode] ? boxes[moveNode].y - 72 : beforeY)){
    shiftSubtree(moveNode, 48, 0);
    edges.forEach(e=>{
      if(e.from===moveNode || e.to===moveNode){
        rerouteKey(`${e.from}__${e.to}`);
      }
    });
  }
}

edges.forEach(e=>routes.push({from:e.from,to:e.to,parent:parentKey,assign:{...(assignments[`${e.from}__${e.to}`]||{})},points:localRoutes[`${e.from}__${e.to}`]}));

return {w:maxRight-originX+30, h:maxBottom-originY+30};

    }

    const root = layoutLevel('', 0, 0, 0);
    resolveProcessOverlaps();

    // Re-anchor all route endpoints to the current box geometry after overlap resolution.
    function inferTargetSideForCurrentRoute(route, targetBox){
      const last = route.points[route.points.length-1];
      if(Math.abs(last.x - targetBox.x) <= 1) return 'left';
      if(Math.abs(last.y - targetBox.y) <= 1) return 'top';
      if(Math.abs(last.y - (targetBox.y + targetBox.h)) <= 1) return 'bottom';
      // fallback based on relative position
      const srcBox = boxes[route.from];
      const srcCy = srcBox.y + srcBox.h/2;
      const tgtCy = targetBox.y + targetBox.h/2;
      if(srcCy < targetBox.y - 10) return 'top';
      if(srcCy > targetBox.y + targetBox.h + 10) return 'bottom';
      return 'left';
    }
    function leftSlotAnchorForBox(b, slot, total){
      if((total||1)<=1) return {x:b.x, y:clamp(b.y+b.h/2, b.y+4, b.y+b.h-4)};
      const span=Math.max(18, Math.min(b.h-12, b.h*0.60));
      const startY=b.y+(b.h-span)/2;
      const step=total>1 ? span/(total-1) : 0;
      return {x:b.x, y:clamp(startY + slot*step, b.y+4, b.y+b.h-4)};
    }
    function anchorOnBoxStart(id, preferY, assign={}){
      const b=boxes[id];
      const off=(assign.succTotal||1)>1 ? Math.min(14, (assign.succIndex||0)*8) : 0;
      const y=clamp((preferY ?? (b.y+b.h/2)) + off, b.y+4, b.y+b.h-4);
      return {x:b.x+b.w, y};
    }
    function anchorOnBoxEnd(id, side, preferPoint, assign={}){
      const b=boxes[id];
      if(side==='left') return leftSlotAnchorForBox(b, assign.slotIn||0, assign.totalIn||1);
      if(side==='top'){
        const x=clamp(preferPoint?.x ?? (b.x+b.w/2), b.x+8, b.x+b.w-8);
        return {x, y:b.y};
      }
      const x=clamp(preferPoint?.x ?? (b.x+b.w/2), b.x+8, b.x+b.w-8);
      return {x, y:b.y+b.h};
    }
function rebuildOrthPath(start,end,side,assign={},opts={}){
  const midShift = opts.midShift || assign.midShift || 0;
  const corridorShift = opts.corridorShift || assign.corridorShift || 0;
  if(side==='left'){
    const splitX = start.x + 38 + (assign.succIndex||0)*26 + midShift;
    const targetMidX = end.x - 28;
    const sameHeight = Math.abs(start.y-end.y) < 8;
    const attempts=[];
    if((assign.succTotal||1)===1){
      if(sameHeight) attempts.push(simplify([start,{x:end.x,y:start.y},end]));
      attempts.push(simplify([start,{x:splitX,y:start.y},{x:splitX,y:end.y},end]));
    } else {
      if((assign.succIndex||0)===0){
        if(sameHeight) attempts.push(simplify([start,{x:end.x,y:start.y},end]));
        attempts.push(simplify([start,{x:splitX,y:start.y},{x:splitX,y:end.y},end]));
      } else {
        const branchY = Math.max(start.y,end.y) + 36 + (assign.succIndex||0)*18 + Math.max(0,corridorShift);
        attempts.push(simplify([start,{x:splitX,y:start.y},{x:splitX,y:branchY},{x:targetMidX,y:branchY},{x:targetMidX,y:end.y},end]));
      }
    }
    const lowerLane = Math.max(start.y,end.y) + 40 + Math.max(0,corridorShift);
    attempts.push(simplify([start,{x:start.x+40,y:start.y},{x:start.x+40,y:lowerLane},{x:targetMidX,y:lowerLane},{x:targetMidX,y:end.y},end]));
    const upperLane = Math.min(start.y,end.y) - 40 - Math.max(0,-corridorShift);
    attempts.push(simplify([start,{x:start.x+40,y:start.y},{x:start.x+40,y:upperLane},{x:targetMidX,y:upperLane},{x:targetMidX,y:end.y},end]));
    return attempts[0];
  }
  if(side==='top'){
    const upperY=(opts.corridorY !== undefined ? opts.corridorY : end.y-44-corridorShift);
    const bendX=(opts.midX !== undefined ? opts.midX : Math.max(start.x+40, end.x)) + midShift;
    return simplify([start,{x:bendX,y:start.y},{x:bendX,y:upperY},{x:end.x,y:upperY},end]);
  }
  const lowerY=(opts.corridorY !== undefined ? opts.corridorY : end.y+44+corridorShift);
  const bendX=(opts.midX !== undefined ? opts.midX : Math.max(start.x+40, end.x)) + midShift;
  return simplify([start,{x:bendX,y:start.y},{x:bendX,y:lowerY},{x:end.x,y:lowerY},end]);
}
routes.forEach(route=>{
      const sourceCompound = false;
      const targetCompound = false;
      if(sourceCompound || targetCompound) return;
      const side=(route.assign && route.assign.side) || inferTargetSideForCurrentRoute(route, boxes[route.to]);
      const start=anchorOnBoxStart(route.from, route.points[0]?.y, route.assign||{});
      const end=anchorOnBoxEnd(route.to, side, route.points[route.points.length-1], route.assign||{});
      route.points = rebuildOrthPath(start,end,side,route.assign||{});
    });

    const contentW = Math.max(
      Math.max(...Object.values(boxes).map(b=>b.x+b.w), 0),
      Math.max(...Object.values(containers).map(c=>c.x+c.w), 0),
      root.w
    ) + 120;
    const contentH = Math.max(
      Math.max(...Object.values(boxes).map(b=>b.y+b.h), 0),
      Math.max(...Object.values(containers).map(c=>c.y+c.h), 0),
      root.h
    ) + 140;

    // Merge parent process box and expanded container/content region for compound nodes.
    const originalBoxes={};
    Object.entries(boxes).forEach(([id,b])=>{ originalBoxes[id]={...b}; });
    const compoundSet=new Set(Object.keys(containers));

    function clamp(v, lo, hi){ return Math.max(lo, Math.min(hi, v)); }
    function attachY(rc, preferY){
      const top = rc.y + 6;
      const bottom = rc.y + Math.max(12, Math.min(rc.h - 6, (rc.headerH || rc.h) - 8));
      return clamp(preferY ?? (rc.y + rc.h/2), top, bottom);
    }
    function attachX(rc, preferX){
      const left = rc.x + 10;
      const right = rc.x + rc.w - 10;
      return clamp(preferX ?? (rc.x + rc.w/2), left, right);
    }
    function inferTargetSide(route, targetBox){
      if(route.assign && route.assign.side) return route.assign.side;
      const last = route.points[route.points.length-1];
      if(Math.abs(last.x - targetBox.x) <= 1) return 'left';
      if(Math.abs(last.y - targetBox.y) <= 1) return 'top';
      return 'bottom';
    }
    function startAnchor(id, preferY, assign={}){
      const rc = boxes[id];
      const off=(assign.succTotal||1)>1 ? Math.min(14, (assign.succIndex||0)*8) : 0;
      return {x: rc.x + rc.w, y: attachY(rc, (preferY ?? (rc.y+rc.h/2)) + off)};
    }
    function endAnchor(id, side, preferPoint, assign={}){
      const rc = boxes[id];
      if(side==='left'){
        if((assign.totalIn||1)<=1) return {x: rc.x, y: attachY(rc, preferPoint?.y)};
        const span=Math.max(18, Math.min(rc.h-12, rc.h*0.60));
        const startY=rc.y+(rc.h-span)/2;
        const step=(assign.totalIn||1)>1 ? span/((assign.totalIn||1)-1) : 0;
        return {x: rc.x, y: attachY(rc, startY + (assign.slotIn||0)*step)};
      }
      if(side==='top') return {x: attachX(rc, preferPoint?.x), y: rc.y};
      return {x: attachX(rc, preferPoint?.x), y: rc.y + rc.h};
    }
    function orthogonalPath(start, end, side, assign={}, opts={}){
      if(opts.corridorY !== undefined){
        const corridorY = opts.corridorY;
        const preX = Math.max(start.x + 40, end.x - 40);
        return simplify([start, {x:start.x+40,y:start.y}, {x:start.x+40,y:corridorY}, {x:end.x-40,y:corridorY}, {x:end.x-40,y:end.y}, end]);
      }
      if(side==='left'){
        const splitX = start.x + 38 + (assign.succIndex||0)*26 + (opts.midShift || assign.midShift || 0);
        const targetMidX = end.x - 28;
        const sameHeight = Math.abs(start.y-end.y) < 8;
        if((assign.succTotal||1)===1){
          if(sameHeight) return simplify([start,{x:end.x,y:start.y},end]);
          return simplify([start,{x:splitX,y:start.y},{x:splitX,y:end.y},end]);
        }
        if((assign.succIndex||0)===0){
          if(sameHeight) return simplify([start,{x:end.x,y:start.y},end]);
          return simplify([start,{x:splitX,y:start.y},{x:splitX,y:end.y},end]);
        }
        const branchY = Math.max(start.y,end.y) + 36 + (assign.succIndex||0)*18 + Math.max(0,(opts.corridorShift || assign.corridorShift || 0));
        return simplify([start,{x:splitX,y:start.y},{x:splitX,y:branchY},{x:targetMidX,y:branchY},{x:targetMidX,y:end.y},end]);
      }
      if(side==='top'){
        const upperY = opts.corridorY !== undefined ? opts.corridorY : end.y - 44;
        const bendX = opts.midX !== undefined ? opts.midX : Math.max(start.x + 40, end.x);
        return simplify([start, {x:bendX,y:start.y}, {x:bendX,y:upperY}, {x:end.x,y:upperY}, end]);
      }
      const lowerY = opts.corridorY !== undefined ? opts.corridorY : end.y + 44;
      const bendX = opts.midX !== undefined ? opts.midX : Math.max(start.x + 40, end.x);
      return simplify([start, {x:bendX,y:start.y}, {x:bendX,y:lowerY}, {x:end.x,y:lowerY}, end]);
    }

    // Merge boxes with containers for compounds.
    Object.entries(containers).forEach(([id,c])=>{
      boxes[id] = {
        x:c.x, y:c.y, w:c.w, h:c.h,
        depth:c.depth, parent:c.parent, headerH:c.headerH, merged:true
      };
    });

    // Re-anchor routes that touch compound nodes to the merged container boundary.
    routes.forEach(route=>{
      const side = inferTargetSide(route, originalBoxes[route.to] || boxes[route.to]);
      const start = startAnchor(route.from, route.points[0]?.y, route.assign||{});
      const end = endAnchor(route.to, side, route.points[route.points.length-1], route.assign||{});
      const sourceCompound = compoundSet.has(route.from);
      const targetCompound = compoundSet.has(route.to);

      if(sourceCompound || targetCompound){
        if(route.parent==='' && sourceCompound && dominantPath.includes(route.from) && dominantPath.includes(route.to)){
          const c = boxes[route.from];
          route.points = orthogonalPath(start, end, side, route.assign||{}, {corridorY: c.y + 18});
        } else {
          route.points = orthogonalPath(start, end, side, route.assign||{});
        }
      }
    });

    // Keep unrelated connectors outside compound container/content regions.
    Object.entries(containers).forEach(([pid, c])=>{
      const owned = descendantsOf(pid, byParent);
      owned.add(pid);
      routes.forEach(route=>{
        if(owned.has(route.from) || owned.has(route.to)) return;
        const touches = pathIntersectsRects(route.points, [c], 2) || route.points.some(p=>rectContainsPoint(c, p, 2));
        if(!touches) return;

        const side = inferTargetSide(route, boxes[route.to]);
        const start = startAnchor(route.from, route.points[0]?.y, route.assign||{});
        const end = endAnchor(route.to, side, route.points[route.points.length-1], route.assign||{});

        const avgY = (start.y + end.y) / 2;
        const corridorY = avgY < c.y + c.h/2 ? c.y - 46 : c.y + c.h + 46;

        let sideX;
        if(start.x <= c.x && end.x <= c.x) sideX = c.x - 46;
        else if(start.x >= c.x + c.w && end.x >= c.x + c.w) sideX = c.x + c.w + 46;
        else sideX = start.x < c.x ? c.x - 46 : c.x + c.w + 46;

        route.points = simplify([
          start,
          {x:sideX, y:start.y},
          {x:sideX, y:corridorY},
          {x:end.x, y:corridorY},
          {x:end.x, y:end.y},
          end
        ]);
      });
    });


function finalSegs(points){ const out=[]; for(let i=0;i<points.length-1;i++) out.push([points[i],points[i+1]]); return out; }
function finalSegConflict(s1,s2){
  const [a,b]=s1,[c,d]=s2;
  const aV=a.x===b.x, cV=c.x===d.x;
  if(aV!==cV){
    const v=aV?[a,b]:[c,d], h=aV?[c,d]:[a,b];
    const vx=v[0].x, hy=h[0].y;
    const vy0=Math.min(v[0].y,v[1].y), vy1=Math.max(v[0].y,v[1].y);
    const hx0=Math.min(h[0].x,h[1].x), hx1=Math.max(h[0].x,h[1].x);
    return vx>hx0 && vx<hx1 && hy>vy0 && hy<vy1;
  }
  if(aV && cV && a.x===c.x){
    const a0=Math.min(a.y,b.y), a1=Math.max(a.y,b.y);
    const c0=Math.min(c.y,d.y), c1=Math.max(c.y,d.y);
    return Math.min(a1,c1) - Math.max(a0,c0) > 1;
  }
  if(!aV && !cV && a.y===c.y){
    const a0=Math.min(a.x,b.x), a1=Math.max(a.x,b.x);
    const c0=Math.min(c.x,d.x), c1=Math.max(c.x,d.x);
    return Math.min(a1,c1) - Math.max(a0,c0) > 1;
  }
  return false;
}
function routePriority(route){
  const key=`${route.from}__${route.to}`;
  let score=0;
  if(dominantEdges.includes(key)) score += 1000;
  if(dominantPath.includes(route.from)) score += 200;
  if(dominantPath.includes(route.to)) score += 100;
  return score;
}
function relatedNode(id, other){
  return id===other || isAncestorBox(boxes,id,other) || isAncestorBox(boxes,other,id);
}
function forbiddenGlobalRects(route){
  const rects=[];
  Object.entries(boxes).forEach(([id,b])=>{
    if(relatedNode(id, route.from) || relatedNode(id, route.to)) return;
    rects.push(b);
  });
  Object.entries(containers).forEach(([id,c])=>{
    if(relatedNode(id, route.from) || relatedNode(id, route.to)) return;
    rects.push(c);
  });
  return rects;
}
function routeCrossesGlobal(route, pts){
  const segA=finalSegs(pts);
  return routes.some(other=>{
    if(other===route) return false;
    const segB=finalSegs(other.points);
    for(const sa of segA){ for(const sb of segB){ if(finalSegConflict(sa,sb)) return true; } }
    return false;
  });
}
function routeHitsGlobalObstacles(route, pts){
  return pathIntersectsRects(pts, forbiddenGlobalRects(route), 2);
}
function buildFinalCandidate(route, patch){
  const currentAssign = route.assign || {};
  const mergedAssign = {...currentAssign, ...patch};
  const currentSide = inferTargetSide(route, boxes[route.to]);
  const side = patch.side || currentSide;
  const start = startAnchor(route.from, route.points[0]?.y, mergedAssign);
  const end = endAnchor(route.to, side, route.points[route.points.length-1], mergedAssign);
  if(route.parent==='' && compoundSet.has(route.from) && dominantPath.includes(route.from) && dominantPath.includes(route.to) && !patch.side && !patch.corridorShift && !patch.midShift){
    const c = boxes[route.from];
    return orthogonalPath(start, end, side, mergedAssign, {corridorY: c.y + 18});
  }
  return rebuildOrthPath(start, end, side, mergedAssign, patch);
}
function tryFinalPatch(route, patch){
  const pts = buildFinalCandidate(route, patch);
  if(routeHitsGlobalObstacles(route, pts)) return false;
  if(routeCrossesGlobal(route, pts)) return false;
  route.points = pts;
  return true;
}
function firstGlobalCrossing(){
  for(let i=0;i<routes.length;i++){
    for(let j=i+1;j<routes.length;j++){
      const a=finalSegs(routes[i].points), b=finalSegs(routes[j].points);
      for(const sa of a){ for(const sb of b){ if(finalSegConflict(sa,sb)) return {a:routes[i], b:routes[j]}; } }
    }
  }
  return null;
}

for(let rep=0; rep<40; rep++){
  const hit = firstGlobalCrossing();
  if(!hit) break;
  const loser = routePriority(hit.a) <= routePriority(hit.b) ? hit.a : hit.b;
  const baseSide = inferTargetSide(loser, boxes[loser.to]);
  let fixed=false;

  // 1) try different target side
  for(const side of ['left','top','bottom'].filter(s=>s!==baseSide)){
    if(tryFinalPatch(loser, {side})){ fixed=true; break; }
  }
  if(fixed) continue;

  // 2) try different reserved vertical lane
  for(const midShift of [-220,-160,-100,100,160,220]){
    if(tryFinalPatch(loser, {side:baseSide, midShift})){ fixed=true; break; }
  }
  if(fixed) continue;

  // 3) try different reserved horizontal corridor
  for(const corridorShift of [80,140,200,-80,-140,-200]){
    if(tryFinalPatch(loser, {side:baseSide, corridorShift})){ fixed=true; break; }
  }
  if(fixed) continue;

  // 4) only if still needed, slightly move nodes
  const moveNode = boxes[loser.to] ? loser.to : loser.from;
  shiftSubtree(moveNode, 0, 84);
  routes.forEach(r=>{
    if(r.from===moveNode || r.to===moveNode){
      r.points = buildFinalCandidate(r, {});
    }
  });
  const hitAfterDown = firstGlobalCrossing();
  if(!hitAfterDown) break;

  shiftSubtree(moveNode, 56, 0);
  routes.forEach(r=>{
    if(r.from===moveNode || r.to===moveNode){
      r.points = buildFinalCandidate(r, {});
    }
  });
}

    // bottom-left coordinate data
    const boxCoords={};
    Object.entries(boxes).forEach(([id,b])=>{
      boxCoords[id]={
        x0:b.x,
        y0:contentH-(b.y+b.h),
        x1:b.x+b.w,
        y1:contentH-b.y,
        corners:[
          {x:b.x,y:contentH-(b.y+b.h)},
          {x:b.x+b.w,y:contentH-(b.y+b.h)},
          {x:b.x+b.w,y:contentH-b.y},
          {x:b.x,y:contentH-b.y}
        ]
      };
    });
    const routeSegments=routes.map(r=>{
      const segs=[];
      for(let i=0;i<r.points.length-1;i++){
        segs.push({
          x0:r.points[i].x, y0:contentH-r.points[i].y,
          x1:r.points[i+1].x, y1:contentH-r.points[i+1].y
        });
      }
      return {from:r.from,to:r.to,segments:segs};
    });

    return {
      boxes, containers, routes,
      dominantEdges, dominantPath,
      scheduleMap,
      contentW, contentH,
      boxCoords, routeSegments
    };
  }

  const api = { buildRecursiveRouteModel };
  if (typeof module!=='undefined' && module.exports) module.exports = api;
  global.ProvenRouter = api;
})(typeof window!=='undefined' ? window : globalThis);
