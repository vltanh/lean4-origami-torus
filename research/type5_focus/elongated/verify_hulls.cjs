// Exact necessary sign filter; no claim to re-prove the archived SAT enumeration.
const fs=require('fs'), path=require('path'), assert=require('assert');
const read=name=>JSON.parse(fs.readFileSync(path.join(__dirname,'..',name),'utf8'));
const orbits=read('full_sign_orbits5.json'),cas=read('cases.json').find(c=>c.type===5&&c.sharp),faces=read('lutz_faces.json')['5'].trim().split(/\s+/).map(f=>[...f].map(Number));
function comb(a,k){if(k===0)return [[]];return a.flatMap((x,i)=>comb(a.slice(i+1),k-1).map(y=>[x,...y]))}
function perm(a){if(!a.length)return [[]];return a.flatMap((x,i)=>perm(a.filter((_,j)=>i!==j)).map(y=>[x,...y]))}
const V=[0,1,2,3,4,5,6,7],Q=comb(V,4),idx=new Map(Q.map((q,i)=>[q.join(''),i])),F=new Set(faces.map(f=>f.slice().sort().join(''))),aut=perm(V).filter(p=>faces.every(f=>F.has(f.map(i=>p[i]).sort().join(''))));
function sign(pat,q){let s=1;for(let i=0;i<q.length;i++)for(let j=i+1;j<q.length;j++)if(q[i]>q[j])s=-s;return s*(pat[idx.get(q.slice().sort().join(''))]==='+'?1:-1)}
let P=new Set();for(let pat of orbits)for(let p of aut){let s=Q.map(q=>sign(pat,q.map(i=>p[i])));P.add(s.map(x=>x*s[0]>0?'+':'-').join(''))}
assert.equal(orbits.length,751);assert.equal(aut.length,6);assert.equal(P.size,4506);
const K=new Map();for(let {edge:[i,j],shift:[m,n]} of cas.edge_shifts){K.set(''+i+j,[m,n]);K.set(''+j+i,[-m,-n])}
let tri=comb(V,3).filter(q=>q.every((v,i)=>K.has(''+v+q[(i+1)%3]))).filter(q=>{let p=q.reduce((s,v,i)=>s.map((x,k)=>x+K.get(''+v+q[(i+1)%3])[k]),[0,0]);return p[1]===0&&Math.abs(p[0])===1});
let pairs=comb(tri,2).filter(([a,b])=>a.every(x=>!b.includes(x)));assert.equal(pairs.length,5);
function pierce(pat,A,u,v){let s=[...A,u,v].sort(),pos=s.filter((_,i)=>((-1)**i)*sign(pat,s.filter((_,j)=>i!==j))>0);return (pos.length===3&&pos.every(x=>A.includes(x)))||(pos.length===2&&pos.every(x=>x===u||x===v))}
function lk(pat,a,b){let n=0;for(let i=0;i<b.length;i++){let u=b[i],v=b[(i+1)%b.length];if(pierce(pat,a,u,v))n+=sign(pat,[...a,v])}return n}
const unlinked=[...P].filter(pat=>pairs.every(([a,b])=>lk(pat,a,b)===0));assert.equal(unlinked.length,3004);
function hull(pat,q,other){let s=other.map(v=>sign(pat,[...q,v]));return s.every(x=>x===s[0])}
const labels=['00120221','00220231','00230232','01200202'],expected=[0,60,130,40];
for(let i=0;i<labels.length;i++){let label=labels[i],caps=['0','2'].map(t=>V.filter(i=>label[i]===t));let both=unlinked.filter(p=>caps.every(cap=>comb(cap,3).some(q=>hull(p,q,V.filter(i=>!cap.includes(i))))));assert.equal(both.length,expected[i]);console.log(label,caps,both.length);}
console.log('PASS: 4506 labeled models; 3004 short-unlinked; both-spanning-cap filter 0,60,130,40');
