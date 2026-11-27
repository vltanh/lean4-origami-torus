// Exact integer checks only; no LP solver needed.
const fs=require('node:fs');const path=require('node:path');
const models=JSON.parse(fs.readFileSync(path.join(__dirname,'../linking_checkpoint/ring4_full_signs.json'),'utf8'));
function verify(models, certs){
 const V=Array.from({length:8},(_,i)=>i),combos=(a,k)=>k===0?[[]]:a.flatMap((v,i)=>combos(a.slice(i+1),k-1).map(c=>[v,...c])),Q=combos(V,4),key=q=>[...q].sort((a,b)=>a-b).join(""),idx=new Map(Q.map((q,i)=>[key(q),i]));
 const parity=q=>q.reduce((n,x,i)=>n+q.slice(i+1).filter(y=>x>y).length,0)%2?-1:1;
 const sign=(m,q)=>parity(q)*(m[idx.get(key(q))]==="+"?1:-1);
 const assert=(b,s)=>{if(!b)throw Error(s)};
 const perms=a=>a.length===0?[[]]:a.flatMap((v,i)=>perms(a.filter((_,j)=>i!==j)).map(p=>[v,...p]));
 const F="356 325 364 302 341 310 506 524 547 570 674 601 617 214 207 271".split(" ").map(s=>[...s].map(Number));const fs=new Set(F.map(f=>key(f)));
 const aut=perms(V).filter(p=>F.every(f=>fs.has(key(f.map(i=>p[i])))));
 assert(aut.length===32,"aut count");
 const act=(m,p)=>{let s=Q.map(q=>sign(m,q.map(i=>p[i]))>0?"+":"-").join("");return s[0]==="+"?s:[...s].map(x=>x==="+"?"-":"+").join("");};
 let covered=new Set();
 for (const [mi,cert] of certs){
  const m=models[mi];const tally=new Map();
  for(const [l,[a,b,c,d],i,j] of cert){
   const pp=[[l.concat(a,b),l.concat(c,d)],[l.concat(a,c),l.concat(b,d)],[l.concat(a,d),l.concat(b,c)]];
   const ss=pp.map((p,k)=>(k===1?-1:1)*sign(m,p[0])*sign(m,p[1]));
   assert(i!==j&&ss.filter(x=>x===ss[j]).length===1&&ss[i]===-ss[j],"GP inequality");
   for(const q of pp[i])tally.set(key(q),(tally.get(key(q))||0)+1);
   for(const q of pp[j])tally.set(key(q),(tally.get(key(q))||0)-1);
  }
  assert([...tally.values()].every(x=>x===0),"multiplicative cancellation");
  let orbit=new Set(aut.map(p=>act(m,p)));assert(orbit.size===8,"orbit size");for(const s of orbit)covered.add(s);
 }
 assert(covered.size===16&&models.every(s=>covered.has(s)),"complete orientation coverage");
 return "PASS: six exact GP inequalities per representative, identical products, all 16 archived models covered.";
}
const certs=[
  [
    0,
    [
      [
        [
          0,
          1
        ],
        [
          3,
          5,
          6,
          7
        ],
        1,
        2
      ],
      [
        [
          0,
          5
        ],
        [
          1,
          4,
          6,
          7
        ],
        1,
        2
      ],
      [
        [
          1,
          3
        ],
        [
          0,
          2,
          6,
          7
        ],
        2,
        1
      ],
      [
        [
          2,
          3
        ],
        [
          1,
          4,
          6,
          7
        ],
        2,
        1
      ],
      [
        [
          2,
          4
        ],
        [
          3,
          5,
          6,
          7
        ],
        2,
        1
      ],
      [
        [
          4,
          5
        ],
        [
          0,
          2,
          6,
          7
        ],
        1,
        2
      ]
    ]
  ],
  [
    2,
    [
      [
        [
          1,
          4
        ],
        [
          0,
          3,
          5,
          7
        ],
        0,
        2
      ],
      [
        [
          2,
          7
        ],
        [
          0,
          3,
          4,
          5
        ],
        1,
        0
      ],
      [
        [
          3,
          4
        ],
        [
          0,
          1,
          5,
          6
        ],
        2,
        0
      ],
      [
        [
          3,
          6
        ],
        [
          0,
          4,
          5,
          7
        ],
        2,
        0
      ],
      [
        [
          3,
          7
        ],
        [
          0,
          2,
          5,
          6
        ],
        0,
        2
      ],
      [
        [
          4,
          7
        ],
        [
          0,
          1,
          2,
          5
        ],
        0,
        1
      ]
    ]
  ]
];
console.log(verify(models,certs));
