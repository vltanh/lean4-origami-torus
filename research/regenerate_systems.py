#!/usr/bin/env python3
"""Recreate omitted generated SAT/SMT files using the archived generators."""
from pathlib import Path
import subprocess
import sys
import shutil

root = Path(__file__).resolve().parent
def run(p):
    subprocess.run([sys.executable, str(p)], cwd=p.parent, check=True)

for p in sorted(root.rglob("generate_cnf.py")):
    run(p)
finite = root / "torus_finite_reduction_certificate" / "torus_finite_reduction"
run(finite / "generate.py")
near = root / "torus_near_universal_certificate" / "torus_near_universal_certificate" / "remaining_markings"
(near / "systems").mkdir(exist_ok=True)
(near / "hex").mkdir(exist_ok=True)
for p in sorted((finite / "systems").glob("*.smt2")):
    if p.name.startswith("t4_interior_"):
        continue
    shutil.copyfile(p, near / "systems" / p.name)
for t, indices in ((4, (1,)), (5, (1,)), (7, (1, 2))):
    for i in indices:
        source = near / "systems" / f"t{t}_ray_{i}.smt2"
        target = near / "hex" / f"t{t}_hex_{i}.smt2"
        s = source.read_text()
        assert s.count("(check-sat)") == 1
        target.write_text(s.replace("(check-sat)", "(assert (= w (/ 3 4)))\n(check-sat)"))
print("Restored DIMACS and 15 original, 9 remaining, 4 hexagonal SMT systems.")
