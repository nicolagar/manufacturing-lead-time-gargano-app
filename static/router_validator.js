
(function(global){
  function segs(points){ const out=[]; for(let i=0;i<points.length-1;i++) out.push([points[i],points[i+1]]); return out; }
  function conflict(s1,s2){
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
  function inside(rc, p, pad=0){
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
  function isAncestor(boxes, anc, node){
    let cur = boxes[node] ? (boxes[node].parent||'') : '';
    while(cur){
      if(cur===anc) return true;
      cur = boxes[cur] ? (boxes[cur].parent||'') : '';
    }
    return false;
  }
  function rectOverlap(a,b,pad=0){
    return !(a.x + a.w + pad <= b.x || b.x + b.w + pad <= a.x || a.y + a.h + pad <= b.y || b.y + b.h + pad <= a.y);
  }

  function validateRecursiveRouteModel(model){
    const issues=[];
    const boxes=model.boxes, containers=model.containers;
    const topIds=Object.keys(boxes).filter(id=>(boxes[id].parent||'')==='');

    model.routes.forEach(r=>{
      const from=boxes[r.from], to=boxes[r.to];
      const first=r.points[0], last=r.points[r.points.length-1];
      if(first.x !== from.x + from.w) issues.push(`start-not-right:${r.from}->${r.to}`);
      const onLeft = last.x===to.x && last.y>=to.y && last.y<=to.y+to.h;
      const onTop = last.y===to.y && last.x>=to.x && last.x<=to.x+to.w;
      const onBottom = last.y===to.y+to.h && last.x>=to.x && last.x<=to.x+to.w;
      if(!(onLeft||onTop||onBottom)) issues.push(`bad-end-side:${r.from}->${r.to}`);
    });

    model.routes.forEach(r=>{
      Object.entries(boxes).forEach(([id,b])=>{
        const allowed =
          id===r.from || id===r.to ||
          isAncestor(boxes, id, r.from) || isAncestor(boxes, id, r.to) ||
          isAncestor(boxes, r.from, id) || isAncestor(boxes, r.to, id) ||
          (boxes[r.from] && boxes[id] && boxes[r.from].parent===boxes[id].parent && boxes[id].parent===boxes[r.to]?.parent);
        if(allowed) return;
        r.points.forEach(p=>{ if(inside(b,p,1)) issues.push(`point-inside-box:${r.from}->${r.to}:${id}`); });
        for(let i=0;i<r.points.length-1;i++){
          if(segIntersectsRect(r.points[i], r.points[i+1], b, 1)) issues.push(`segment-through-box:${r.from}->${r.to}:${id}`);
        }
      });
    });

    topIds.forEach(id=>{
      const b=boxes[id];
      Object.entries(containers).forEach(([pid,c])=>{
        if(id===pid) return;
        if(b.parent===pid) return;
        if(isAncestor(boxes, id, pid)) return;
        const overlap=!(b.x+b.w<=c.x || b.x>=c.x+c.w || b.y+b.h<=c.y || b.y>=c.y+c.h);
        if(overlap) issues.push(`top-box-inside-container:${id}:${pid}`);
      });
    });


    const ids=Object.keys(boxes);
    for(let i=0;i<ids.length;i++){
      for(let j=i+1;j<ids.length;j++){
        const a=ids[i], b=ids[j];
        if(a===b) continue;
        if(isAncestor(boxes,a,b) || isAncestor(boxes,b,a)) continue;
        if(rectOverlap(boxes[a], boxes[b], 0)) issues.push(`box-overlap:${a}:${b}`);
      }
    }

    for(let i=0;i<model.routes.length;i++){
      for(let j=i+1;j<model.routes.length;j++){
        const ra=model.routes[i], rb=model.routes[j];
        for(const sa of segs(ra.points)){
          for(const sb of segs(rb.points)){
            if(conflict(sa,sb)) issues.push(`crossing-or-overlap:${ra.from}->${ra.to}:${rb.from}->${rb.to}`);
          }
        }
      }
    }

    return {ok: issues.length===0, issues};
  }

  const api={validateRecursiveRouteModel};
  if(typeof module!=='undefined' && module.exports) module.exports=api;
  global.RouterValidator=api;
})(typeof window!=='undefined' ? window : globalThis);
