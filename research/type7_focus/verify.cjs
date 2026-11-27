// Exact finite checks for the Type 7 rigidity and ray_4 symmetry reductions.
// Node.js, no external packages. Run: node verify.cjs
// Completeness of the input orientation archives is checked by the earlier
// verify_projection.py and verify_full_ring4.py, not by this program.
const fs = require('node:fs');
const path = require('node:path');
const load = file => JSON.parse(fs.readFileSync(path.join(__dirname, '../linking_checkpoint', file), 'utf8'));
function verify(models, faces, cases, Z) {
  const check=(b,m)=>{if(!b)throw Error(m)};
  const V=[0,1,2,3,4,5,6,7], partner=V.map(i=>(i+4)%8);
  const F=faces["7"].split(/\s+/).map(s=>[...s].map(Number));
  const key=q=>q.slice().sort((a,b)=>a-b).join("");
  const combos=(a,k)=>k===0?[[]]:a.flatMap((x,i)=>combos(a.slice(i+1),k-1).map(t=>[x,...t]));
  const edges=new Set(F.flatMap(t=>combos(t,2).map(key)));
  check(edges.size===24 && combos(V,2).every(([i,j])=>edges.has(key([i,j]))===(partner[i]!==j)),"graph");
  const Q=combos(V,4), C=Q.filter(q=>q.every(i=>!q.includes(partner[i])));
  check(JSON.stringify(C)===JSON.stringify(Z.cliques),"clique order");
  const ci=new Map(C.map((q,i)=>[key(q),i])), qi=new Map(Q.map((q,i)=>[key(q),i]));
  const inv=q=>q.reduce((s,x,i)=>s+q.slice(i+1).filter(y=>x>y).length,0);
  const sign=(m,q,ix)=>{const i=ix.get(key(q));check(i!==undefined,"minor index");return (m[i]==="+"?1:-1)*(inv(q)%2?-1:1)};
  const heights=(m,a,ix)=>a.map(v=>{const f=a.filter(x=>x!==v);return sign(m,[...f,v],ix)*sign(m,[...f,partner[v]],ix)>0?"+":"-"}).join("");
  const unanimous=s=>s==="++++"||s==="----";
  check(Z.patterns.length===316 && new Set(Z.patterns).size===316 && Z.patterns.every(m=>m.length===16 && m[0]==="+"),"clique patterns");
  const ps=new Set(Z.patterns);
  const twist=m=>C.map((q,i)=>q.filter(v=>v>=4).length%2===0?m[i]:(m[i]==="+"?"-":"+")).join("");
  const hist={}, exceptions=[], twisted=[];
  for (const m of Z.patterns) {
    const n=C.filter(a=>unanimous(heights(m,a,ci))).length;
    hist[n]=(hist[n]||0)+1;
    if(n===0) { exceptions.push(m); check(!ps.has(twist(m)),"exception has twist partner"); }
    if(ps.has(twist(m))) twisted.push(m);
  }
  check(exceptions.length===8 && twisted.length===4,"exception and twist counts");
  check(twisted.every(m=>C.some(a=>unanimous(heights(m,a,ci)))),"twist pair has no unanimous anchor");
  const perms=a=>a.length===0?[[]]:a.flatMap((x,i)=>perms(a.filter((_,j)=>i!==j)).map(p=>[x,...p]));
  const fs=new Set(F.map(key)), aut=perms(V).filter(p=>F.every(f=>fs.has(key(f.map(i=>p[i])))));
  check(aut.length===32,"automorphism order");
  const sym=[(m,n)=>[m,n],(m,n)=>[-m,-n],(m,n)=>[m+n,-n],(m,n)=>[-m-n,n]];
  const add=(a,b)=>[a[0]+b[0],a[1]+b[1]], sub=(a,b)=>[a[0]-b[0],a[1]-b[1]];
  const stab=c=>{
    const K={};
    for(const {edge:[i,j],shift:s} of c.edge_shifts){K[`${i}${j}`]=s;K[`${j}${i}`]=s.map(v=>-v)}
    return aut.filter(p=>sym.some(g=>{
      const d={0:[0,0]};
      for(let pass=0;pass<8;pass++)for(const [e,s] of Object.entries(K)){
        const [i,j]=[...e].map(Number);
        if(d[i]&&!d[j])d[j]=add(d[i],sub(K[`${p[i]}${p[j]}`],g(...s)));
      }
      return Object.entries(K).every(([e,s])=>{const [i,j]=[...e].map(Number);return sub(sub(K[`${p[i]}${p[j]}`],g(...s)),sub(d[j],d[i])).every(x=>x===0)});
    }));
  };
  const type7=cases.filter(c=>c.type===7&&c.sharp);
  check(type7.length===4,"markings");
  const st=type7.map(c=>stab(c));
  check(JSON.stringify(st.map(a=>a.length))===JSON.stringify([16,16,32,32]),"stabilizer orders");
  const ray4=type7.findIndex(c=>c.file==="t7_ray_4.smt2");
  check(ray4!==-1,"ray4");
  const act=(m,p)=>{
    const s=Q.map(q=>sign(m,q.map(i=>p[i]),qi)>0?"+":"-").join("");
    return s[0]==="+"?s:[...s].map(x=>x==="+"?"-":"+").join("");
  };
  check(models.length===16&&new Set(models).size===16&&models.every(m=>m.length===70&&m[0]==="+"),"full signs");
  const remaining=new Set(models), orbits=[];
  while(remaining.size){
    const m=[...remaining][0],o=new Set(st[ray4].map(p=>act(m,p)));
    check([...o].every(s=>remaining.has(s)),"orbit closure");
    orbits.push([...o].map(s=>models.indexOf(s)+1).sort((a,b)=>a-b));
    for(const s of o)remaining.delete(s);
  }
  check(orbits.length===2&&orbits.every(o=>o.length===8),"two ray4 orbits");
  const A=[0,1,2,7], roots=orbits.map(o=>heights(models[o[0]-1],A,qi));
  check(JSON.stringify(roots)===JSON.stringify(["----","++++"]),"canonical relative height signs");
  // The full models need only match actual nonclique signs weakly. The four
  // relative signs here use exclusively K4 minors and are therefore strict.
  return {cliquePatterns:Z.patterns.length,unanimousAnchorHistogram:hist,noUnanimousAnchor:exceptions,patternsWithTwistPartner:twisted,markingStabilizers:st.map(a=>a.length),ray4Orbits:orbits,canonicalAnchor:A,canonicalRelativeHeightSigns:roots};
}
const result = verify(load('ring4_full_signs.json'), load('lutz_faces.json'), load('cases.json'), load('clique_signs7.json'));
console.log(JSON.stringify(result, null, 2));
console.log('PASS Type 7 exact finite checks');
