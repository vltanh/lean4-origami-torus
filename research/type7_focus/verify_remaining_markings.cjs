// Exact checks for the new metric localization and sign-only witnesses.
// Run: node verify_remaining_markings.cjs
const fs=require('node:fs'),path=require('node:path');
const read=name=>JSON.parse(fs.readFileSync(path.join(__dirname,'../linking_checkpoint',name),'utf8'));
function check(cases,faces){
 const V=[0,1,2,3,4,5,6,7],mod=x=>(x%8+8)%8,comb=(v,k)=>k===0?[[]]:v.flatMap((a,i)=>comb(v.slice(i+1),k-1).map(b=>[a,...b])),perms=a=>a.length===0?[[]]:a.flatMap((v,i)=>perms(a.filter((_,j)=>i!==j)).map(p=>[v,...p]));
 const key=q=>[...q].sort((a,b)=>a-b).join(""),Q=comb(V,4),faces7=faces["7"].split(" ").map(s=>[...s].map(Number)),T=new Set(faces7.map(key)),E=new Set(faces7.flatMap(f=>comb(f,2).map(key)));
 const assert=(cond,msg)=>{if(!cond)throw Error(msg)};
 const sum=(a,b)=>a.map((x,i)=>x+b[i]),sub=(a,b)=>a.map((x,i)=>x-b[i]),scale=(a,c)=>a.map(x=>x*c);
 const edges=c=>c.map((v,i)=>[v,c[(i+1)%c.length]]);
 const getK=t=>{const c=cases.find(c=>c.file===`t7_ray_${t}.smt2`);assert(c!==undefined,"case");const K={};for(const {edge:[i,j],shift:s} of c.edge_shifts){K[`${i}${j}`]=s;K[`${j}${i}`]=scale(s,-1)}return (i,j)=>K[`${i}${j}`]};
 const wind=(c,K)=>edges(c).reduce((a,[i,j])=>sum(a,K(i,j)),[0,0]);
 const zero=a=>a.every(v=>v===0);
 for(const t of [1,2]){
  const K=getK(t);
  for(const i of V)for(const k of [2,3]){
   const s=Array.from({length:k},(_,j)=>K(mod(i+j),mod(i+j+1))).reduce(sum,[0,0]);
   assert(zero(sub(sub(K(i,mod(i+k)),s),[1,0])),"constant correction");
  }
  assert(wind(V,K)[1]===1,"vertical Hamiltonian winding");
  assert(JSON.stringify(wind(V,K))===JSON.stringify([t===1?-4:-3,1]),"Hamiltonian period");
  assert(V.every(i=>JSON.stringify(wind([i,mod(i+1),mod(i+2)],K))==="[-1,0]"),"short triangle windings");
 }
 const A=[0,2,4,6],B=[1,3,5,7],K3=getK(3);
 const x=Array(8).fill(0),y=Array(8).fill(0); // 2x and 2y baseline coordinates
 for(const R of [A,B]){
  assert(JSON.stringify(wind(R,K3))==="[1,-2]","ray3 long period");
  for(let k=0;k<3;k++){const i=R[k],j=R[k+1],[m,n]=K3(i,j);x[j]=x[i]-2*m-n;y[j]=y[i]-1-2*n}
 }
 const CX=A.map(i=>B.map(j=>{const [m,n]=K3(i,j);return x[j]-x[i]+2*m+n}));
 const CY=A.map(i=>B.map(j=>{const [m,n]=K3(i,j);return y[j]-y[i]+2*n}));
 assert(CX.every(r=>r.every(v=>v===0||v===1)&&r.reduce((a,b)=>a+b,0)===2)&&B.every((_,j)=>CX.reduce((s,r)=>s+r[j],0)===2),"horizontal shifts");
 assert(CY.every(r=>r.every(v=>v===0||v===-1)&&r.reduce((a,b)=>a+b,0)===-2)&&B.every((_,j)=>CY.reduce((s,r)=>s+r[j],0)===-2),"vertical shifts");
 const partitions=[[[0,1,4,5],[2,3,6,7]],[[0,3,4,7],[1,2,5,6]]];
 for(let h=0;h<2;h++){
  const [C,D]=partitions[h];assert([C,D].every(R=>JSON.stringify(wind(R,K3))==="[-1,0]"),"short ring periods");
  assert(A.every((i,k)=>B.every((j,l)=>(CY[k][l]+h===0)===((C.includes(i)&&C.includes(j))||(D.includes(i)&&D.includes(j))))),"partition from cross shifts");
 }
 // Each vertex has six neighbors, generic affine circuits certify both
 // embeddedness and strict local support for the exact integer witnesses.
 const R1=[[0,0,0],[1000,0,0],[0,1000,0],[209,197,-47],[596,-297,309],[215,428,294],[47,-4953,5000],[0,0,1000]];
 const R3=[[0,0,0],[1000,0,0],[0,1000,0],[495,-726,643],[2305,-5000,-150],[-2336,5000,-3336],[693,-441,597],[0,0,1000]];
 const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
 const det=(R,q)=>{const [a,b,c,d]=q.map(i=>R[i].map(BigInt));const v=cross(sub(b,a),sub(c,a));return v.reduce((z,x,i)=>z+x*(d[i]-a[i]),0n)};
 const sgn=x=>x>0n?1:x<0n?-1:0;
 const cycles=[];for(let k=3;k<=5;k++)for(const a of comb(V,k))for(const b of perms(a.slice(1))){if(b[0]>b.at(-1))continue;const c=[a[0],...b];if(edges(c).every(e=>E.has(key(e))))cycles.push(c);}
 const subset=(a,b)=>a.every(x=>b.includes(x));
 const results=[];
 for(const [t,R] of [[1,R1],[2,R1],[3,R3]]){
  const K=getK(t);assert(Q.every(q=>det(R,q)!==0n),"generic witness");
  const D=q=>sgn(det(R,q));
  const circuits=comb(V,5).map(S=>{const P=[],N=[];S.forEach((v,i)=>((i%2?-1:1)*D(S.filter((_,k)=>k!==i))>0?P:N).push(v));return [P,N]});
  for(const [P,N] of circuits){
   assert(P.length&&N.length,"acyclic");
   for(const [a,b] of [[P,N],[N,P]]){
    assert(!(a.length===2&&E.has(key(a))&&b.length===3&&T.has(key(b))),"edge-face crossing");
    assert(!(a.length===1&&b.every(v=>E.has(key([a[0],v])))),"support failure");
   }
  }
  for(const v of V){assert(faces7.some(f=>f.includes(v)&&(()=>{const s=V.filter(w=>!f.includes(w)&&E.has(key([v,w]))).map(w=>D([...f,w]));return s.includes(1)&&s.includes(-1)})()),"mixed-side failure")}
  const canon=c=>{let h=wind(c,K);if(h[0]<0||(h[0]===0&&h[1]<0))return [[c[0],...c.slice(1).reverse()],scale(h,-1)];return [c,h]};
  const pierce=(tri,u,v)=>{const S=[...tri,u,v].sort((a,b)=>a-b);const p=S.filter((_,i)=>(i%2?-1:1)*D(S.filter((_,k)=>k!==i))>0);return key(p)===key(tri)||key(S.filter(x=>!p.includes(x)))===key(tri)};
  const link=(a,b)=>{let z=0;for(let i=1;i<a.length-1;i++){const tri=[a[0],a[i],a[i+1]];for(const [u,v] of edges(b))if(pierce(tri,u,v))z+=D([...tri,v])}return z};
  const slopes=new Map();let count=0;
  for(let i=0;i<cycles.length;i++)for(let j=i+1;j<cycles.length;j++){if(cycles[i].some(v=>cycles[j].includes(v)))continue;
   const [a,h]=canon(cycles[i]),[b,g]=canon(cycles[j]);const l=link(a,b);count++;
   if(zero(h)||zero(g)){assert(l===0,"contractible pair");continue}
   assert(zero(sub(h,g)),"parallel slopes");const k=h.join(",");assert(!slopes.has(k)||slopes.get(k)===l,"link consistency");slopes.set(k,l);
  }
  const qs=[];for(let k=-3;k<=3;k++)for(const s of [-1,1])if([...slopes].every(([h,l])=>{const [m,n]=h.split(",").map(Number);return l===n*(k*n+s*m)}))qs.push([k,s]);
  assert(qs.length>0,"linking quadratic form");
  const sep=(a,b)=>!circuits.some(([p,n])=>(subset(p,a)&&subset(n,b))||(subset(p,b)&&subset(n,a)));
  const short=cycles.filter(c=>{const h=wind(c,K);return Math.abs(h[0])===1&&h[1]===0});
  let pairs=[];for(let i=0;i<short.length;i++)for(let j=i+1;j<short.length;j++)if(!short[i].some(v=>short[j].includes(v)))pairs.push([short[i],short[j]]);
  const shortest=Math.min(...pairs.map(([a,b])=>a.length+b.length));pairs=pairs.filter(([a,b])=>a.length+b.length===shortest);
  const separated=pairs.filter(([a,b])=>sep(a,b));assert(separated.length>0,"separated shortest cycles");
  results.push({marking:t,disjointCyclePairs:count,quadraticForms:qs,separatedShortPairs:separated.length,totalShortPairs:pairs.length});
 }
 return {CX,CY,results};
}
console.log(JSON.stringify(check(read('cases.json'),read('lutz_faces.json')),null,2));
console.log('PASS exact winding, gauge, generic embedding, support, and linking checks');

// Cyclic rotation preserves each marking up to an integral vertex gauge.
const V=[0,1,2,3,4,5,6,7], mod=i=>(i%8+8)%8;
for(const t of [1,2,3]){
 const c=read('cases.json').find(c=>c.file===`t7_ray_${t}.smt2`),K={};
 for(const {edge:[i,j],shift:a} of c.edge_shifts){K[`${i}${j}`]=a;K[`${j}${i}`]=a.map(x=>-x)}
 const g=[[0,0]],diff=(i,j)=>K[`${mod(i+1)}${mod(j+1)}`].map((x,k)=>x-K[`${i}${j}`][k]);
 for(let i=0;i<7;i++)g.push(g[i].map((x,k)=>x+diff(i,i+1)[k]));
 for(const e of Object.keys(K)){const [i,j]=[...e].map(Number);if(!diff(i,j).every((x,k)=>x===g[j][k]-g[i][k]))throw Error('rotation gauge')}
}
const masks=new Set();
for(let m=1;m<256;m++){
 const s=V.filter(i=>(m>>i)&1), left=new Set(s);let cc=0;
 while(left.size){let stack=[[...left][0]];left.delete(stack[0]);cc++;
  while(stack.length){const i=stack.pop();for(const j of [...left])if(Math.min(mod(i-j),mod(j-i))<=2){left.delete(j);stack.push(j)}}
 }
 if(cc===2)masks.add(V.map(k=>s.map(v=>mod(v+k)).sort((a,b)=>a-b).join('')).sort()[0]);
}
const expected=['03','04','014','015','025','0125','0145'];
if(masks.size!==7||!expected.every(s=>masks.has(s)))throw Error('mask orbits');
console.log('PASS seven cyclic large-step mask orbits:',expected.join(' '));
