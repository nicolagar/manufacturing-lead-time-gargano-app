
(function(global){
  function clone(obj){ return JSON.parse(JSON.stringify(obj)); }
  function sortRows(rows){
    return (rows||[]).slice().sort((a,b)=>
      (Number(a.earliest_start)||0) - (Number(b.earliest_start)||0) ||
      String(a.process).localeCompare(String(b.process))
    );
  }
  function buildHierarchy(schedule){
    const byParent={};
    (schedule||[]).forEach(r=>{
      const p=r.refines||'';
      (byParent[p]||(byParent[p]=[])).push(r);
    });
    Object.keys(byParent).forEach(k=>{ byParent[k]=sortRows(byParent[k]); });
    return byParent;
  }
  function buildScheduleMap(schedule){
    const out={};
    (schedule||[]).forEach(r=>{ out[r.process]=r; });
    return out;
  }
  function edgesForParent(graph, scheduleMap, parent){
    return (graph.edges||[]).filter(e => (scheduleMap[e.from]?.refines||'')===parent && (scheduleMap[e.to]?.refines||'')===parent);
  }
  function buildMaps(rows, edges){
    const ids=rows.map(r=>r.process);
    const preds={}, succs={};
    ids.forEach(id=>{ preds[id]=[]; succs[id]=[]; });
    (edges||[]).forEach(e=>{
      if(preds[e.to] && succs[e.from]){
        preds[e.to].push(e.from);
        succs[e.from].push(e.to);
      }
    });
    Object.keys(preds).forEach(k=>{ preds[k].sort(); succs[k].sort(); });
    return {preds, succs};
  }
  function topoOrder(rows, edges){
    const {preds,succs}=buildMaps(rows, edges);
    const rowMap={}; rows.forEach(r=>{ rowMap[r.process]=r; });
    const indeg={}; Object.keys(preds).forEach(k=>{ indeg[k]=preds[k].length; });
    const q=Object.keys(indeg).filter(id=>indeg[id]===0).sort((a,b)=>
      (Number(rowMap[a]?.earliest_start)||0) - (Number(rowMap[b]?.earliest_start)||0) ||
      String(a).localeCompare(String(b))
    );
    const out=[];
    while(q.length){
      const id=q.shift();
      out.push(id);
      (succs[id]||[]).forEach(nxt=>{
        indeg[nxt]-=1;
        if(indeg[nxt]===0){
          q.push(nxt);
          q.sort((a,b)=>
            (Number(rowMap[a]?.earliest_start)||0) - (Number(rowMap[b]?.earliest_start)||0) ||
            String(a).localeCompare(String(b))
          );
        }
      });
    }
    rows.forEach(r=>{ if(!out.includes(r.process)) out.push(r.process); });
    return out;
  }
  function computeLevels(rows, edges){
    const {preds}=buildMaps(rows, edges);
    const order=topoOrder(rows, edges);
    const level={};
    order.forEach(id=>{
      const ps=preds[id]||[];
      level[id]=ps.length ? Math.max(...ps.map(p=>level[p]||0))+1 : 0;
    });
    return level;
  }
  function assignLanes(rows, edges){
    const {preds,succs}=buildMaps(rows, edges);
    const order=topoOrder(rows, edges);
    const rowMap={}; rows.forEach(r=>{ rowMap[r.process]=r; });
    const desired={};
    let nextRootLane=0;

    order.forEach(id=>{
      if((preds[id]||[]).length===0 && desired[id]===undefined){
        desired[id]=nextRootLane;
        nextRootLane += 2;
      }
      const explicitSucc=(rowMap[id]?.successors||[]).slice();
      const orderMap={}; explicitSucc.forEach((sid,idx)=>{ orderMap[sid]=idx; });
      const outs=(succs[id]||[]).slice().sort((a,b)=>
        (orderMap[a] ?? 1e9) - (orderMap[b] ?? 1e9) ||
        (Number(rowMap[a]?.earliest_start)||0) - (Number(rowMap[b]?.earliest_start)||0) ||
        String(a).localeCompare(String(b))
      );
      outs.forEach((sid, idx)=>{
        const prop = outs.length===1 ? desired[id] : desired[id] + idx;
        if(desired[sid]===undefined) desired[sid]=prop;
        else desired[sid]=Math.min(desired[sid], prop);
      });
    });

    const level=computeLevels(rows, edges);
    const usedByLevel={};
    const lane={};

    order.forEach(id=>{
      const lvl=level[id]||0;
      const used=(usedByLevel[lvl]||(usedByLevel[lvl]=new Set()));
      const ps=preds[id]||[];
      let pref = desired[id];
      if(pref===undefined){
        if(ps.length===0) pref=nextRootLane++;
        else if(ps.length===1 && (succs[ps[0]]||[]).length===1) pref=lane[ps[0]];
        else if(ps.length>1) pref=Math.max(...ps.map(p=>lane[p]||0));
        else pref=0;
      } else if(ps.length===1 && (succs[ps[0]]||[]).length===1){
        pref=lane[ps[0]];
      } else if(ps.length>1){
        pref=Math.max(pref, Math.max(...ps.map(p=>lane[p]||0)));
      }
      let ln=pref;
      while(used.has(ln)) ln += 1;
      used.add(ln);
      lane[id]=ln;
    });

    const minLane=Math.min(...Object.values(lane), 0);
    if(minLane<0){
      Object.keys(lane).forEach(k=>{ lane[k]-=minLane; });
    }
    return lane;
  }

  function rect(x,y,w,h,depth,parent,headerH,childField){
    return {x,y,w,h,depth,parent,headerH:headerH||0,childField:childField||null};
  }
  function simplify(points){
    if(!points || !points.length) return [];
    const out=[points[0]];
    for(let i=1;i<points.length;i++){
      const p=points[i], q=out[out.length-1];
      if(p.x!==q.x || p.y!==q.y) out.push(p);
    }
    return out;
  }
  function boxIntersects(a,b,pad){
    pad = pad||0;
    return !(a.x+a.w+pad <= b.x || b.x+b.w+pad <= a.x || a.y+a.h+pad <= b.y || b.y+b.h+pad <= a.y);
  }
  function segIntersectsRect(a,b,r,pad){
    pad = pad||0;
    if(a.x===b.x){
      const x=a.x, y0=Math.min(a.y,b.y), y1=Math.max(a.y,b.y);
      return x>r.x+pad && x<r.x+r.w-pad && !(y1<=r.y+pad || y0>=r.y+r.h-pad);
    }
    if(a.y===b.y){
      const y=a.y, x0=Math.min(a.x,b.x), x1=Math.max(a.x,b.x);
      return y>r.y+pad && y<r.y+r.h-pad && !(x1<=r.x+pad || x0>=r.x+r.w-pad);
    }
    return true;
  }
  function pathHitsRects(points, rects){
    for(let i=0;i<points.length-1;i++){
      for(const rc of rects){
        if(segIntersectsRect(points[i], points[i+1], rc, 0)) return true;
      }
    }
    return false;
  }
  function pathSegs(points){
    const out=[];
    for(let i=0;i<points.length-1;i++) out.push([points[i],points[i+1]]);
    return out;
  }
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
      return Math.min(a1,c1)-Math.max(a0,c0) > 1;
    }
    if(!aV && !cV && a.y===c.y){
      const a0=Math.min(a.x,b.x), a1=Math.max(a.x,b.x);
      const c0=Math.min(c.x,d.x), c1=Math.max(c.x,d.x);
      return Math.min(a1,c1)-Math.max(a0,c0) > 1;
    }
    return false;
  }
  function shiftScopeTree(model, rootId, dx, dy){
    const ids=[rootId];
    let changed=true;
    while(changed){
      changed=false;
      Object.keys(model.boxes).forEach(id=>{
        if(ids.includes(id)) return;
        let cur=model.boxes[id] ? (model.boxes[id].parent||'') : '';
        while(cur){
          if(ids.includes(cur)){ ids.push(id); changed=true; break; }
          cur=model.boxes[cur] ? (model.boxes[cur].parent||'') : '';
        }
      });
    }
    ids.forEach(id=>{
      if(model.boxes[id]){
        model.boxes[id].x += dx; model.boxes[id].y += dy;
        if(model.boxes[id].childField){
          model.boxes[id].childField.x += dx; model.boxes[id].childField.y += dy;
        }
      }
      if(model.containers[id]){
        model.containers[id].x += dx; model.containers[id].y += dy;
        if(model.containers[id].childField){
          model.containers[id].childField.x += dx; model.containers[id].childField.y += dy;
        }
      }
    });
    model.routes.forEach(r=>{
      if(ids.includes(r.from) || ids.includes(r.to)){
        r.points=r.points.map(p=>({x:p.x+dx, y:p.y+dy}));
      }
    });
  }
  function mergeInto(target, source){
    Object.assign(target.boxes, source.boxes);
    Object.assign(target.containers, source.containers);
    target.routes.push(...source.routes);
  }

  function buildRecursiveRouteModel(data){
    const schedule=data.schedule||[];
    const graph=data.graph||{edges:[]};
    const scheduleMap=buildScheduleMap(schedule);
    const byParent=buildHierarchy(schedule);
    const dominantPath=(data.dominant_path||[]).slice();
    const dominantSet=new Set(dominantPath);
    const dominantEdges=(data.critical_edges||[]).map(e=>`${e.from}__${e.to}`);

    function isCompound(id){ return (byParent[id]||[]).length>0; }
    function dimsFor(depth, id){
      const child=isCompound(id);
      if(depth===0) return child ? {baseW:280, minH:180, headerH:42, padX:18, padTop:20, padBottom:20} : {baseW:140, minH:56, headerH:0, padX:0, padTop:0, padBottom:0};
      if(depth===1) return child ? {baseW:220, minH:150, headerH:38, padX:16, padTop:18, padBottom:18} : {baseW:120, minH:46, headerH:0, padX:0, padTop:0, padBottom:0};
      return child ? {baseW:190, minH:130, headerH:32, padX:14, padTop:16, padBottom:16} : {baseW:108, minH:38, headerH:0, padX:0, padTop:0, padBottom:0};
    }

    function buildRoutesForScope(rows, edges, directBoxes, parentKey, depth, shiftPass=0){
      const {preds,succs}=buildMaps(rows, edges);
      const incoming={}, outgoing={};
      edges.forEach(e=>{
        (incoming[e.to]||(incoming[e.to]=[])).push(e);
        (outgoing[e.from]||(outgoing[e.from]=[])).push(e);
      });
      const rowMap={}; rows.forEach(r=>{ rowMap[r.process]=r; });
      function branchRight(startIds, excludeId){
        const seen=new Set();
        let maxRight=0;
        const stack=(startIds||[]).filter(id=>id && id!==excludeId);
        while(stack.length){
          const id=stack.pop();
          if(seen.has(id)) continue;
          seen.add(id);
          if(directBoxes[id]) maxRight=Math.max(maxRight, directBoxes[id].x + directBoxes[id].w);
          (succs[id]||[]).forEach(nxt=>{ if(!seen.has(nxt)) stack.push(nxt); });
        }
        return maxRight;
      }

      function orderEdges(arr, kind){
        return (arr||[]).slice().sort((a,b)=>{
          if(kind==='out'){
            const explicit=(rowMap[a.from]?.successors||[]).slice();
            const orderMap={}; explicit.forEach((sid,idx)=>{ orderMap[sid]=idx; });
            const diff=(orderMap[a.to] ?? 1e9) - (orderMap[b.to] ?? 1e9);
            if(diff!==0) return diff;
          }
          const aBox=kind==='out' ? directBoxes[a.to] : directBoxes[a.from];
          const bBox=kind==='out' ? directBoxes[b.to] : directBoxes[b.from];
          const ay=aBox.y+aBox.h/2, by=bBox.y+bBox.h/2;
          return ay-by || `${a.from}->${a.to}`.localeCompare(`${b.from}->${b.to}`);
        });
      }

      const assigns={};
      Object.keys(outgoing).forEach(src=>{
        const arr=orderEdges(outgoing[src],'out');
        arr.forEach((e, idx)=>{
          const key=`${e.from}__${e.to}`;
          assigns[key] = {...(assigns[key]||{}), succIndex: idx, succTotal: arr.length};
        });
      });
      Object.keys(incoming).forEach(tgt=>{
        const arr=orderEdges(incoming[tgt],'in');
        const tgtBox=directBoxes[tgt];
        const tgtCy=tgtBox.y+tgtBox.h/2;
        const srcCys=arr.map(e=>directBoxes[e.from].y + directBoxes[e.from].h/2);
        const allAbove = arr.length>1 && srcCys.every(y=>y < tgtCy-18);
        const allBelow = arr.length>1 && srcCys.every(y=>y > tgtCy+18);
        const buckets={left:[], top:[], bottom:[]};
        if(allAbove) buckets.top.push(...arr);
        else if(allBelow) buckets.bottom.push(...arr);
        else {
          arr.forEach(e=>{
            const srcBox=directBoxes[e.from];
            const srcCy=srcBox.y+srcBox.h/2;
            if(arr.length===1) buckets.left.push(e);
            else if(srcCy < tgtCy-18) buckets.top.push(e);
            else if(srcCy > tgtCy+18) buckets.bottom.push(e);
            else buckets.left.push(e);
          });
        }
        ['left','top','bottom'].forEach(side=>{
          const total=buckets[side].length;
          buckets[side].forEach((e, idx)=>{
            const key=`${e.from}__${e.to}`;
            const lockedSide = arr.length>1;
            assigns[key] = {...(assigns[key]||{}), side, slotIn: idx, totalIn: total, lockedSide};
          });
        });
      });

      function startAnchor(box, assign){
        const total=assign.succTotal||1, idx=assign.succIndex||0;
        if(total<=1) return {x:box.x+box.w, y:box.y+box.h/2};
        const span=Math.max(16, Math.min(box.h-12, box.h*0.60));
        const startY=box.y+(box.h-span)/2;
        const step=total>1 ? span/(total-1) : 0;
        return {x:box.x+box.w, y:startY + idx*step};
      }
      function leftAnchor(box, slot, total){
        if((total||1)<=1) return {x:box.x, y:box.y+box.h/2};
        const span=Math.max(16, Math.min(box.h-12, box.h*0.60));
        const startY=box.y+(box.h-span)/2;
        const step=total>1 ? span/(total-1) : 0;
        return {x:box.x, y:startY + slot*step};
      }
      function topAnchor(box, slot, total){
        if((total||1)<=1) return {x:box.x+box.w/2, y:box.y};
        const span=Math.max(24, Math.min(box.w-16, box.w*0.60));
        const startX=box.x+(box.w-span)/2;
        const step=total>1 ? span/(total-1) : 0;
        const idx=((total||1)-1-(slot||0));
        return {x:startX + idx*step, y:box.y};
      }
      function bottomAnchor(box, slot, total){
        if((total||1)<=1) return {x:box.x+box.w/2, y:box.y+box.h};
        const span=Math.max(24, Math.min(box.w-16, box.w*0.60));
        const startX=box.x+(box.w-span)/2;
        const step=total>1 ? span/(total-1) : 0;
        return {x:startX + slot*step, y:box.y+box.h};
      }
      function sideOrderFor(edge){
        const src=directBoxes[edge.from], tgt=directBoxes[edge.to];
        const srcCy=src.y+src.h/2, tgtCy=tgt.y+tgt.h/2;
        if(Math.abs(srcCy-tgtCy)<=10) return ['left','top','bottom'];
        return srcCy < tgtCy ? ['left','top','bottom'] : ['left','bottom','top'];
      }
      function obstaclesFor(edge){
        const rects=[];
        Object.entries(directBoxes).forEach(([id,b])=>{
          if(id===edge.from || id===edge.to) return;
          rects.push({x:b.x-6,y:b.y-6,w:b.w+12,h:b.h+12});
        });
        return rects;
      }
      function routeCrossesOthers(key, pts, currentRoutes){
        const segA=pathSegs(pts);
        return Object.keys(currentRoutes).some(otherKey=>{
          if(otherKey===key) return false;
          const segB=pathSegs(currentRoutes[otherKey]);
          for(const sa of segA){ for(const sb of segB){ if(segConflict(sa,sb)) return true; } }
          return false;
        });
      }
      function buildCandidate(edge, assign, currentRoutes){
        const from=directBoxes[edge.from], to=directBoxes[edge.to];
        const start=startAnchor(from, assign);
        const side=assign.side||'left';
        const end=side==='left' ? leftAnchor(to, assign.slotIn||0, assign.totalIn||1)
          : side==='top' ? topAnchor(to, assign.slotIn||0, assign.totalIn||1)
          : bottomAnchor(to, assign.slotIn||0, assign.totalIn||1);

        const xGap=Math.max(36, Math.min(120, (to.x - (from.x+from.w))/2));
        const slotShift=((assign.side==='top' || assign.side==='bottom')
          ? ((assign.totalIn||1)-1-(assign.slotIn||0))
          : (assign.slotIn||0)) * 18;
        const midX=Math.max(start.x+24, Math.min(to.x-24, from.x+from.w+xGap+(assign.midShift||0)+slotShift));
        const targetX=Math.min(to.x-24, Math.max(start.x+24, to.x-32 + (assign.midShift||0) - slotShift));
        const sameHeight=Math.abs(start.y-end.y) < 8;
        const attempts=[];

        if(parentKey==='' && dominantSet.has(edge.from) && dominantSet.has(edge.to) && directBoxes[edge.from].headerH){
          const headerY=directBoxes[edge.from].y + 18 + (assign.corridorShift||0);
          attempts.push(simplify([start,{x:start.x+18,y:start.y},{x:start.x+18,y:headerY},{x:end.x-18,y:headerY},{x:end.x-18,y:end.y},end]));
        }

        if((assign.succTotal||1)>1 && (assign.succIndex||0)>0 && (side==='top' || side==='bottom')){
          const siblingTargets=(outgoing[edge.from]||[]).map(e=>directBoxes[e.to]).filter(Boolean);
          const siblingRight=Math.max(branchRight((outgoing[edge.from]||[]).map(e=>e.to), edge.to), ...siblingTargets.map(b=>b.x+b.w), end.x);
          const siblingTop=Math.min(...siblingTargets.map(b=>b.y), start.y);
          const siblingBottom=Math.max(...siblingTargets.map(b=>b.y+b.h), end.y);
          const baseOuterX=Math.max(siblingRight + 48 + (assign.succIndex||0)*28 + (assign.midShift||0), start.x + 60);
          for(const dx of [0,60,120,180]){
            const outerX=baseOuterX + dx;
            if(side==='top'){
              const escapeY=Math.max(12, Math.min(start.y, siblingTop) - 28 - Math.abs(assign.corridorShift||0));
              const preTargetY=end.y - 24;
              attempts.push(simplify([start,{x:start.x,y:escapeY},{x:outerX,y:escapeY},{x:outerX,y:preTargetY},{x:end.x,y:preTargetY},end]));
            } else {
              const escapeY=Math.max(start.y, siblingBottom) + 28 + Math.abs(assign.corridorShift||0);
              const preTargetY=end.y + 24;
              attempts.push(simplify([start,{x:start.x,y:escapeY},{x:outerX,y:escapeY},{x:outerX,y:preTargetY},{x:end.x,y:preTargetY},end]));
            }
          }
        }

        if(side==='left'){
          if((assign.succTotal||1)===1){
            if(sameHeight) attempts.push(simplify([start,{x:end.x,y:start.y},end]));
            attempts.push(simplify([start,{x:midX,y:start.y},{x:midX,y:end.y},end]));
            const upperY=Math.min(start.y,end.y)-36+(assign.corridorShift||0)-slotShift;
            attempts.push(simplify([start,{x:start.x+24,y:start.y},{x:start.x+24,y:upperY},{x:targetX,y:upperY},{x:targetX,y:end.y},end]));
            const lowerY=Math.max(start.y,end.y)+36+(assign.corridorShift||0)+slotShift;
            attempts.push(simplify([start,{x:start.x+24,y:start.y},{x:start.x+24,y:lowerY},{x:targetX,y:lowerY},{x:targetX,y:end.y},end]));
          } else {
            const idx=assign.succIndex||0;
            if(idx===0){
              if(sameHeight) attempts.push(simplify([start,{x:end.x,y:start.y},end]));
              attempts.push(simplify([start,{x:midX,y:start.y},{x:midX,y:end.y},end]));
            } else {
              const siblingTargets=(outgoing[edge.from]||[]).map(e=>directBoxes[e.to]).filter(Boolean);
              const siblingBottom=Math.max(...siblingTargets.map(b=>b.y+b.h), end.y);
              const siblingRight=Math.max(branchRight((outgoing[edge.from]||[]).map(e=>e.to), edge.to), ...siblingTargets.map(b=>b.x+b.w), end.x);
              const siblingTop=Math.min(...siblingTargets.map(b=>b.y), start.y);
              const branchY=Math.max(start.y, end.y, siblingBottom) + 34 + idx*28 + (assign.corridorShift||0) + slotShift;
              const outerX=Math.max(siblingRight + 48 + idx*28 + (assign.midShift||0), start.x + 60);
              const escapeY=Math.max(12, Math.min(start.y, siblingTop) - 28 - Math.abs(assign.corridorShift||0));
              const nearX=Math.max(start.x + 22 + idx*8, start.x + 18);
              const nearAttempts=[
                simplify([start,{x:nearX,y:start.y},{x:nearX,y:end.y},{x:end.x,y:end.y},end]),
                simplify([start,{x:nearX,y:start.y},{x:nearX,y:branchY},{x:end.x,y:branchY},{x:end.x,y:end.y},end]),
              ];
              const lowerY=branchY+30;
              const outerAttempts=[
                simplify([start,{x:outerX,y:start.y},{x:outerX,y:escapeY},{x:end.x,y:escapeY},{x:end.x,y:end.y},end]),
                simplify([start,{x:outerX,y:start.y},{x:outerX,y:branchY},{x:end.x,y:branchY},{x:end.x,y:end.y},end]),
                simplify([start,{x:outerX,y:start.y},{x:outerX,y:lowerY},{x:outerX,y:end.y},end]),
              ];
              (assign.midShift||assign.corridorShift ? outerAttempts.concat(nearAttempts) : nearAttempts.concat(outerAttempts)).forEach(p=>attempts.push(p));
            }
          }
        } else if(side==='top'){
          const corridorY=to.y - 32 - (assign.corridorShift||0) - slotShift;
          attempts.push(simplify([start,{x:midX,y:start.y},{x:midX,y:corridorY},{x:end.x,y:corridorY},end]));
          const upperY=corridorY-28;
          attempts.push(simplify([start,{x:start.x+24,y:start.y},{x:start.x+24,y:upperY},{x:end.x,y:upperY},{x:end.x,y:end.y},end]));
        } else {
          const corridorY=to.y + to.h + 32 + (assign.corridorShift||0) + slotShift;
          attempts.push(simplify([start,{x:midX,y:start.y},{x:midX,y:corridorY},{x:end.x,y:corridorY},end]));
          const lowerY=corridorY+28;
          attempts.push(simplify([start,{x:start.x+24,y:start.y},{x:start.x+24,y:lowerY},{x:end.x,y:lowerY},{x:end.x,y:end.y},end]));
        }

        const obstacles=obstaclesFor(edge);
        for(const pts of attempts){
          if(pathHitsRects(pts, obstacles)) continue;
          if(routeCrossesOthers(`${edge.from}__${edge.to}`, pts, currentRoutes)) continue;
          return pts;
        }
        return attempts[0] || [start,end];
      }

      const localRoutes={};
      const edgeOrder=edges.slice().sort((a,b)=>{
        const ak=(dominantSet.has(a.from)||dominantSet.has(a.to)?1000:0)+(scheduleMap[a.from]?.critical?50:0);
        const bk=(dominantSet.has(b.from)||dominantSet.has(b.to)?1000:0)+(scheduleMap[b.from]?.critical?50:0);
        return bk-ak || (directBoxes[a.from].x-directBoxes[b.from].x) || `${a.from}->${a.to}`.localeCompare(`${b.from}->${b.to}`);
      });

      edgeOrder.forEach(edge=>{
        const key=`${edge.from}__${edge.to}`;
        const base={...(assigns[key]||{})};
        let genericSides=sideOrderFor(edge);
        if((base.succTotal||1)>1 && (base.succIndex||0)>0){
          const src=directBoxes[edge.from], tgt=directBoxes[edge.to];
          genericSides = (src.y+src.h/2) < (tgt.y+tgt.h/2) ? ['top','left','bottom'] : ['bottom','left','top'];
        }
        const sides=base.lockedSide
          ? [base.side||genericSides[0]||'left']
          : (((base.succTotal||1)>1 && (base.succIndex||0)>0)
              ? genericSides
              : (base.side ? [base.side].concat(genericSides.filter(s=>s!==base.side)) : genericSides));
        let chosen=null;
        for(const side of sides){
          const pts=buildCandidate(edge, {...base, side}, localRoutes);
          if(!routeCrossesOthers(key, pts, localRoutes)){ chosen=pts; base.side=side; break; }
        }
        if(!chosen){
          base.side=base.side||sides[0]||'left';
          chosen=buildCandidate(edge, base, localRoutes);
        }
        assigns[key]=base;
        localRoutes[key]=chosen;
      });

      function firstIssue(){
        const keys=Object.keys(localRoutes);
        for(let i=0;i<keys.length;i++){
          for(let j=i+1;j<keys.length;j++){
            const a=pathSegs(localRoutes[keys[i]]), b=pathSegs(localRoutes[keys[j]]);
            for(const sa of a){ for(const sb of b){ if(segConflict(sa,sb)) return {a:keys[i], b:keys[j]}; } }
          }
        }
        return null;
      }
      function priority(key){
        const [f,t]=key.split('__');
        let score=0;
        if(dominantSet.has(f)||dominantSet.has(t)) score+=1000;
        if(scheduleMap[f]?.critical) score+=100;
        if(scheduleMap[t]?.critical) score+=50;
        return score;
      }
      function tryPatch(key, patch){
        const [f,t]=key.split('__');
        const merged={...(assigns[key]||{}), ...patch};
        const pts=buildCandidate({from:f,to:t}, merged, localRoutes);
        if(routeCrossesOthers(key, pts, localRoutes)) return false;
        localRoutes[key]=pts;
        assigns[key]=merged;
        return true;
      }

      for(let rep=0; rep<80; rep++){
        const issue=firstIssue();
        if(!issue) break;
        const loser=priority(issue.a) <= priority(issue.b) ? issue.a : issue.b;
        const current=assigns[loser]||{};
        let fixed=false;
        const sideCandidates = current.lockedSide ? [] : ['left','top','bottom'].filter(s=>s!==(current.side||'left'));
        for(const side of sideCandidates){
          if(tryPatch(loser,{side})){ fixed=true; break; }
        }
        if(fixed) continue;
        for(const midShift of [-240,-180,-120,-80,80,120,180,240,300,420,600]){
          if(tryPatch(loser,{midShift})){ fixed=true; break; }
        }
        if(fixed) continue;
        for(const corridorShift of [60,120,180,-60,-120,-180]){
          if(tryPatch(loser,{corridorShift})){ fixed=true; break; }
        }
        if(fixed) continue;
        if(shiftPass < 3){
          const [sf,st]=loser.split('__');
          const moveIds=new Set([sf]);
          const stack=[sf];
          while(stack.length){
            const cur=stack.pop();
            (succs[cur]||[]).forEach(nxt=>{ if(rowMap[nxt] && !moveIds.has(nxt)){ moveIds.add(nxt); stack.push(nxt); } });
          }
          const deltaY = depth===0 ? 120 : 84;
          Array.from(moveIds).forEach(id=>{ if(directBoxes[id]) directBoxes[id].y += deltaY; });
          return buildRoutesForScope(rows, edges, directBoxes, parentKey, depth, shiftPass+1);
        }
        break;
      }

      return edgeOrder.map(e=>({from:e.from,to:e.to,parent:parentKey,assign:assigns[`${e.from}__${e.to}`]||{},points:localRoutes[`${e.from}__${e.to}`]}));
    }

    function layoutScope(parentKey, depth){
      const rows=sortRows(byParent[parentKey]||[]);
      const model={boxes:{}, containers:{}, routes:[], width:0, height:0};
      if(!rows.length) return model;
      const edges=edgesForParent(graph, scheduleMap, parentKey);
      const level=computeLevels(rows, edges);
      const lane=assignLanes(rows, edges);
      const childModels={};
      const nodeDims={};

      rows.forEach(r=>{
        const id=r.process;
        if(isCompound(id)) childModels[id]=layoutScope(id, depth+1);
        const conf=dimsFor(depth, id);
        if(childModels[id]){
          const child=childModels[id];
          nodeDims[id]={w:Math.max(conf.baseW, child.width + conf.padX*2), h:Math.max(conf.minH, conf.headerH + conf.padTop + child.height + conf.padBottom), headerH:conf.headerH, padX:conf.padX, padTop:conf.padTop};
        } else {
          nodeDims[id]={w:conf.baseW, h:conf.minH, headerH:0, padX:0, padTop:0};
        }
      });

      const maxLevel=Math.max(...rows.map(r=>level[r.process]||0),0);
      const colWidth={}; for(let lvl=0; lvl<=maxLevel; lvl++){ colWidth[lvl]=Math.max(...rows.filter(r=>(level[r.process]||0)===lvl).map(r=>nodeDims[r.process].w), 0); }
      const marginX=depth===0?60:18;
      const marginY=depth===0?40:18;
      const colGap=depth===0?120:depth===1?84:56;
      const laneStep=Math.max(...rows.map(r=>nodeDims[r.process].h), depth===0?56:42) + (depth===0?58:(depth===1?38:28));
      const xByLevel={};
      let curX=marginX;
      for(let lvl=0; lvl<=maxLevel; lvl++){
        xByLevel[lvl]=curX;
        curX += colWidth[lvl] + colGap;
      }

      const directBoxes={};

      rows.forEach(r=>{
        const id=r.process;
        const d=nodeDims[id];
        const x=xByLevel[level[id]||0];
        const y=marginY + (lane[id]||0) * laneStep;
        if(childModels[id]){
          const child=childModels[id];
          const childOriginX=x+d.padX;
          const childOriginY=y+d.headerH+d.padTop;
          shiftScopeTree(child, null, childOriginX, childOriginY); // null root means shift whole child model
          mergeInto(model, child);
          const childField={x:childOriginX, y:childOriginY, w:child.width, h:child.height};
          const outer=rect(x,y,d.w,d.h,depth+1,parentKey,d.headerH,childField);
          model.boxes[id]=clone(outer);
          model.containers[id]=clone(outer);
          directBoxes[id]=model.boxes[id];
        } else {
          const outer=rect(x,y,d.w,d.h,depth,parentKey,0,null);
          model.boxes[id]=clone(outer);
          directBoxes[id]=model.boxes[id];
        }
      });

      // de-overlap direct boxes in this scope, shifting whole subtrees
      let changed=true, guard=0;
      while(changed && guard<50){
        changed=false; guard++;
        const ids=rows.map(r=>r.process);
        for(let i=0;i<ids.length;i++){
          for(let j=i+1;j<ids.length;j++){
            const a=ids[i], b=ids[j];
            if(!boxIntersects(directBoxes[a], directBoxes[b], 10)) continue;
            const move = directBoxes[a].y <= directBoxes[b].y ? b : a;
            const stay = move===b ? a : b;
            const dy=(directBoxes[stay].y + directBoxes[stay].h + (depth===0?48:32)) - directBoxes[move].y;
            // shift direct box and whole descendant subtree
            shiftScopeTree(model, move, 0, dy);
            directBoxes[move]=model.boxes[move];
            changed=true;
          }
        }
      }

      const scopeRoutes=buildRoutesForScope(rows, edges, directBoxes, parentKey, depth, 0);
      model.routes.push(...scopeRoutes);

      const allRects=Object.values(model.boxes).concat(Object.values(model.containers));
      const routePts=model.routes.flatMap(r=>r.points||[]);
      const maxRight=Math.max(...allRects.map(r=>r.x+r.w), ...(routePts.length?routePts.map(p=>p.x):[0]), 0);
      const maxBottom=Math.max(...allRects.map(r=>r.y+r.h), ...(routePts.length?routePts.map(p=>p.y):[0]), 0);
      model.width=maxRight + (depth===0?60:26);
      model.height=maxBottom + (depth===0?60:26);
      return model;
    }

    // allow shifting whole child model when rootId is null
    const _shiftOrig=shiftScopeTree;
    shiftScopeTree=function(model, rootId, dx, dy){
      if(rootId===null){
        Object.values(model.boxes).forEach(b=>{ b.x+=dx; b.y+=dy; if(b.childField){ b.childField.x+=dx; b.childField.y+=dy; }});
        Object.values(model.containers).forEach(c=>{ c.x+=dx; c.y+=dy; if(c.childField){ c.childField.x+=dx; c.childField.y+=dy; }});
        (model.routes||[]).forEach(r=>{ r.points=r.points.map(p=>({x:p.x+dx, y:p.y+dy})); });
        return;
      }
      return _shiftOrig(model, rootId, dx, dy);
    };

    const root=layoutScope('',0);
    const contentW=Math.max(root.width+40, 1400);
    const contentH=Math.max(root.height+40, 760);

    const boxCoords={};
    Object.entries(root.boxes).forEach(([id,b])=>{
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
    const routeSegments=root.routes.map(r=>{
      const segs=[];
      for(let i=0;i<r.points.length-1;i++){
        segs.push({x0:r.points[i].x, y0:contentH-r.points[i].y, x1:r.points[i+1].x, y1:contentH-r.points[i+1].y});
      }
      return {from:r.from,to:r.to,segments:segs};
    });

    return {
      boxes: root.boxes,
      containers: root.containers,
      routes: root.routes,
      dominantEdges,
      dominantPath,
      scheduleMap,
      contentW,
      contentH,
      boxCoords,
      routeSegments
    };
  }

  const api={buildRecursiveRouteModel};
  if(typeof module!=='undefined' && module.exports) module.exports=api;
  global.ProvenRouter=api;
})(typeof window!=='undefined' ? window : globalThis);
