// Exact Type 5 final-polynomial checker. No floating arithmetic or solver.
function verify(archive,cases,facesData,branches){
 const assert=(v,m="assertion failed")=>{if(!v)throw Error(m)};
 const V=[0,1,2,3,4,5,6,7];
 function comb(a,k){if(k===0)return [[]];return a.flatMap((x,i)=>comb(a.slice(i+1),k-1).map(y=>[x,...y]))}
 function perm(a){if(!a.length)return [[]];return a.flatMap((x,i)=>perm(a.filter((_,j)=>i!==j)).map(y=>[x,...y]))}
 const F=facesData["5"].trim().split(/\s+/).map(x=>[...x].map(Number));
 const fs=new Set(F.map(f=>f.slice().sort().join("")));
 const E=new Set(F.flatMap(f=>comb(f.slice().sort(),2).map(e=>e.join(""))));
 const Q=comb(V,4),keys=Q.map(q=>q.join("")),ix=new Map(keys.map((q,i)=>[q,i]));
 const target="+----++-+-++++-+++--+++++++-+--------+-+----++-+--++-++++-+-------++--";
 assert(target.length===70&&archive.length===751&&archive.includes(target));
 function sign(p,q){let s=1;for(let i=0;i<q.length;i++)for(let j=i+1;j<q.length;j++)if(q[i]>q[j])s=-s;return s*(p[ix.get(q.slice().sort().join(""))]==="+"?1:-1)}
 const clique=q=>comb(q,2).every(e=>E.has(e.join("")));
 const strict=new Set(Q.filter(clique).map(q=>q.join("")));
 assert(strict.size===23);
 const simplices=new Set([...V.map(String),...E,...fs]);const rounds=[];
 const neighbor=(a,b)=>E.has([a,b].sort().join(""));
 while(true){
  const next=[];
  for(const q of Q){const k=q.join("");if(strict.has(k))continue;
   for(const w of V){if(q.includes(w))continue;
    const S=[...q,w].sort(),cof=new Map(S.map((v,i)=>[v,(-1)**i*sign(target,S.filter(x=>x!==v))]));
    if(!q.some(v=>strict.has(S.filter(x=>x!==v).join(""))))continue;
    const a=q.filter(v=>cof.get(v)>0),b=q.filter(v=>cof.get(v)<0);
    if(!a.length||!b.length||(simplices.has(a.join(""))&&simplices.has(b.join("")))||(a.length===1&&b.every(v=>neighbor(a[0],v)))||(b.length===1&&a.every(v=>neighbor(b[0],v)))){next.push(k);break}
   }
  }
  if(!next.length)break;next.forEach(k=>strict.add(k));rounds.push(next.length);
 }
 assert(rounds.join(",")==="33,4"&&strict.size===60);
 const terms=[
  ["0145","0257","0125","0457","0157","0245"],
  ["0157","3457","0457","1357","0357","1457"],
  ["0245","0467","0246","0457","0247","0456"],
  ["0247","0357","0237","0457","0257","0347"],
  ["0347","4567","0457","3467","0467","3457"],
  ["0456","1457","0457","1456","0145","4567"]
 ];
 const GP=new Set();
 function key(a,b){return [a,b].sort().join("*")}
 for(const s of comb(V,2))for(const [a,b,c,d] of comb(V.filter(x=>!s.includes(x)),4)){
  const rel=[[s.concat(a,b),s.concat(c,d)],[s.concat(a,c),s.concat(b,d)],[s.concat(a,d),s.concat(b,c)]];
  const ss=rel.map(([u,v],i)=>(-1)**i*sign(target,u)*sign(target,v));
  assert(Math.abs(ss.reduce((a,b)=>a+b,0))===1);
  const k=ss.indexOf(-ss.reduce((a,b)=>a+b,0));
  const prod=rel.map(([u,v])=>key(u.slice().sort().join(""),v.slice().sort().join("")));
  const other=prod.filter((_,i)=>i!==k).sort();
  GP.add(other.join("+")+"="+prod[k]);
 }
 for(const t of terms)assert(GP.has([key(t[0],t[1]),key(t[2],t[3])].sort().join("+")+"="+key(t[4],t[5])),"signed GP identity");
 const factors=new Set(terms.flatMap(t=>[...t.slice(0,2),...t.slice(4)]));
 assert([...factors].filter(k=>!strict.has(k)).sort().join(",")==="0347,0467");
 let changed=true;while(changed){changed=false;for(const t of terms){if((strict.has(t[0])&&strict.has(t[1]))||(strict.has(t[2])&&strict.has(t[3]))){for(const k of t.slice(4))if(!strict.has(k)){strict.add(k);changed=true}}}}
 assert([...factors].every(k=>strict.has(k)));
 assert(strict.has("0125")&&strict.has("0457"));
 assert(terms.flatMap(t=>t.slice(0,2)).sort().join(",")===terms.flatMap(t=>t.slice(4)).sort().join(","));
 const aut=perm(V).filter(p=>F.every(f=>fs.has(f.map(i=>p[i]).sort().join(""))));
 assert(aut.length===6);
 const expand=pat=>aut.map(p=>{const s=Q.map(q=>sign(pat,q.map(i=>p[i])));return s.map(x=>x*s[0]>0?"+":"-").join("")});
 const all=new Set(archive.flatMap(expand)),orbit=new Set(expand(target));
 assert(all.size===4506&&orbit.size===6);
 assert([...orbit].every(p=>all.has(p)));
 const removed=branches.map(b=>[b.id,b.chambers.filter(p=>orbit.has(p)).length]);
 assert(JSON.stringify(removed)==='[["B1.1",0],["B1.2",0],["B1.3",0],["B1.4",0],["B1.5",1],["B1.6",0]]');
 const b15=branches.find(b=>b.id==="B1.5");assert(b15.chambers.length===42&&b15.chambers[14]===target);
 const ca=cases.find(c=>c.type===5&&c.sharp),K=new Map();
 for(const {edge:[i,j],shift:[m,n]} of ca.edge_shifts){K.set(""+i+j,[m,n]);K.set(""+j+i,[-m,-n])}
 const triangles=comb(V,3).filter(q=>q.every((v,i)=>K.has(""+v+q[(i+1)%3]))).filter(q=>{const h=q.reduce((s,v,i)=>s.map((x,k)=>x+K.get(""+v+q[(i+1)%3])[k]),[0,0]);return Math.abs(h[0])===1&&h[1]===0});
 const pairs=comb(triangles,2).filter(([a,b])=>a.every(x=>!b.includes(x)));assert(pairs.length===5);
 function lk(p,A,B){let n=0;for(let i=0;i<B.length;i++){
  const u=B[i],v=B[(i+1)%B.length],S=[...A,u,v].sort();
  const pos=S.filter((_,j)=>(-1)**j*sign(p,S.filter((_,k)=>j!==k))>0);
  if((pos.length===3&&pos.every(x=>A.includes(x)))||(pos.length===2&&pos.every(x=>x===u||x===v)))n+=sign(p,[...A,v]);
 }return n}
 const unlinked=[...all].filter(p=>pairs.every(([a,b])=>lk(p,a,b)===0));
 assert(unlinked.length===3004&&unlinked.filter(p=>orbit.has(p)).length===4);
 return {status:"PASS",target,rounds,removed,unlinked:unlinked.length,excluded:[...orbit]};
}
const fs=require('fs'), path=require('path');
const read=p=>JSON.parse(fs.readFileSync(path.join(__dirname,p),'utf8'));
console.log(JSON.stringify(verify(read('full_sign_orbits5.json'),read('cases.json'),read('lutz_faces.json'),read('branch_ledger/branches.json')),null,2));
