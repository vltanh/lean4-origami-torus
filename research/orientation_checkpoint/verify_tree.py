from satgeom import *
for t in (4,5,7):
 z=json.loads((Path(__file__).resolve().parent / f'clique_signs{t}.json').read_text());cl=[tuple(q) for q in z['cliques']];tree=[tuple(q) for q in z['true_tree_cliques']];S=[ids[q] for q in tree];n,C,T,E,N=formula(t);s=SAT(n,C);seen=set()
 for a in it.product((-1,1),repeat=4):
  v=a+(-1,);s.push()
  for k,p in zip(S,v):s.add([k*p])
  # global orientation normalization [0123]>0 can exclude representative with last negative;
  # also try reflected signs.
  b=s.check();s.pop()
  if b==-1:
   s.push()
   for k,p in zip(S,v):s.add([-k*p])
   b=s.check();s.pop()
  assert b in (-1,1)
  if b==1:seen.add(''.join('+' if a>0 else '-' for a in v))
 assert seen==set(z['true_tree_signs']),(t,seen,z['true_tree_signs'])
 for a in sorted(seen):
  v=[1 if b=='+' else -1 for b in a];C.extend([[-k*p for k,p in zip(S,v)],[k*p for k,p in zip(S,v)]])
 P=Path(__file__).resolve().parent / f'blocked_tree_{t}.cnf';P.write_text(f'p cnf {n} {len(C)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in C));assert SAT(n,C).check()==-1
 print(t,len(seen),'branches; blocked formula UNSAT',n,len(C),flush=True)
