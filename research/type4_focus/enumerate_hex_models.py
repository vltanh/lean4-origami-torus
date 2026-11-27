#!/usr/bin/env python3
"""Enumerate the full generic sign models over each joint hexagonal clique orbit.
The generic models are necessary sign chambers; use weak signs on noncliques
when applying them to actual (possibly nongeneric) metric configurations.
"""
import sys
from pathlib import Path
from contextlib import redirect_stdout
import io,runpy,json

here=Path(__file__).resolve().parent
with redirect_stdout(io.StringIO()):
    data=runpy.run_path(str(here/'verify_hex_orbits.py'))
sys.path.insert(0,str(here.parent/'orientation_checkpoint'))
from satgeom import formula,SAT,ids,Q
n,C,*_=formula(4)
assert C[0]==[1]
# Reflection in the older formula is normalized at 0123. That quadruple
# is not a clique. Normalize instead at the first clique (0124), as in
# verify_hex_orbits.py, to preserve coplanar nonclique configurations.
C=C[1:]
cliques=data['cliques']
orbits=data['orbits']
records=[]
for k,orb in enumerate(orbits,1):
    s=orb[0]
    solver=SAT(n,C+[[ids[q]*(1 if a=='+' else -1)] for q,a in zip(cliques,s)])
    models=[]
    while True:
        status=solver.check()
        if status==-1:break
        assert status==1, 'inconclusive SAT enumeration'
        signs=solver.model()
        models.append(''.join('+' if a==1 else '-' for a in signs))
        solver.add([-a*(i+1) for i,a in enumerate(signs)])
    assert len(models)==len(set(models)) and models
    records.append({'id':'H%02d'%k,'clique_signs':s,'full_signs':sorted(models)})
    print(records[-1]['id'],len(models),flush=True)
counts=[len(r['full_signs']) for r in records]
assert counts==[26,25,108,76,51,202,151,27,191,86,13,15,1,103,33,72,20,242,6,166,21,10,26,34,18,157,18,420,22,44,21]
assert sum(counts)==2405
(here/'hex_models.json').write_text(json.dumps(records,indent=2)+'\n')
print('31 clique classes, 2405 full generic models; H13 is unique')
