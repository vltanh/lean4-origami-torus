#!/usr/bin/env python3
"""Necessary strict constraints for complete Type 5 cell systems.

The reusable functions accept squared spatial distances as SMT expressions,
and an arbitrary coherent intrinsic squared-lift function.  Units therefore
need not match the historical normalized Gram generator.  No metric variable
is fixed and no positive numerical lower bound is inserted.

CLI: coverage_constraints.py OUTPUT_DIRECTORY [CELL_ID ...] [--necessary]
By default it augments the existing FULL 18-variable Gram formulation; use
--necessary explicitly to omit its simplex-intersection conditions.
See coverage.md for the necessity proof and exact scope.
Use --check-square to replay compatibility with the existing exact positive
square-torus construction using its integer interval arithmetic.
"""
from itertools import combinations, product
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
MISSING = ((0, 6), (0, 7), (3, 4), (6, 7))
SHIFTS = tuple(product((-1, 0, 1), repeat=2))


def _distance(d, i, j):
    return d[i, j] if (i, j) in d else d[j, i]


def noncollinearity_constraints(d, triples=None):
    """21 strict 2-by-2 Gram minors, using squared distance expressions d.

    The omitted triple 067 has no asserted obstruction.  Clique triples are
    already nondegenerate in the existing model's 23 strict K4 conditions.
    """
    if triples is None:
        data = json.loads((HERE / "coverage.json").read_text())
        triples = data["nonclique_triples_with_antipodal_obstruction"]
    result = []
    for v, i, j in triples:
        a, b, c = (_distance(d, v, i), _distance(d, v, j), _distance(d, i, j))
        h = f"(- (+ {a} {b}) {c})"
        result.append(f"(assert (> (- (* 4 {a} {b}) (* {h} {h})) 0))")
    return result


def unique_lift_constraints(d, squared_lift, shifts=SHIFTS):
    """No two distinct lifts of a missing edge can both saturate contraction.

    squared_lift(i,j,(m,n)) must use the same units as d[i,j].  The base model
    must retain the individual nonnegative contraction slacks.  These strict
    sums eliminate their simultaneous zero boundary without excluding a
    single saturated lift.
    """
    assert len(set(shifts)) == len(shifts)
    result = []
    for i, j in MISSING:
        target = _distance(d, i, j)
        lifts = [squared_lift(i, j, k) for k in shifts]
        for a, b in combinations(lifts, 2):
            result.append(f"(assert (> (- (+ {a} {b}) (* 2 {target})) 0))")
    return result


def augment(smt, d, squared_lift):
    """Insert both sound strengthenings, preserving the original full model."""
    assert smt.count("(check-sat)") == 1
    extra = ["; Type 5: 21 noncollinear nonclique triples; no numerical margin."]
    extra += noncollinearity_constraints(d)
    extra += ["; Type 5: unique saturated lift for all four missing pairs."]
    extra += unique_lift_constraints(d, squared_lift)
    return smt.replace("(check-sat)", "\n".join(extra) + "\n(check-sat)")


def check_square():
    """Independent positive compatibility check; no optimizer or floats."""
    import contextlib
    import io
    import runpy
    source = HERE.parent / "torus_type5_reconstruction_certificate/type5_algebraic_certificate/verify.py"
    with contextlib.redirect_stdout(io.StringIO()):
        model = runpy.run_path(str(source))
    p, r = dict(model["p"]), dict(model["r"])
    for v, (_, intrinsic, spatial) in zip(model["L"], model["wins"][0]):
        p[v], r[v] = intrinsic, spatial
    sub, add, sq = (model[name] for name in ("sub", "add", "sq"))
    d = {(i, j): sq(sub(r[j], r[i])) for i, j in combinations(range(8), 2)}
    triples = json.loads((HERE / "coverage.json").read_text())["nonclique_triples_with_antipodal_obstruction"]
    for v, i, j in triples:
        a, b, c = (_distance(d, v, i), _distance(d, v, j), _distance(d, i, j))
        h = a + b - c
        assert (4 * a * b - h * h).l > 0, (v, i, j)
    for i, j in MISSING:
        slacks = [sq(add(sub(p[j], p[i]), k)) - d[i, j] for k in SHIFTS]
        assert all(s.l >= 0 for s in slacks), (i, j, "individual contraction")
        assert all((a + b).l > 0 for a, b in combinations(slacks, 2)), (i, j, "lift ties")
    print("PASS: exact square witness satisfies all 21 new minors and 144 strict lift-tie sums.")


def main():
    args = sys.argv[1:]
    if args == ["--check-square"]:
        check_square()
        return
    necessary = "--necessary" in args
    args = [a for a in args if a != "--necessary"]
    if not args:
        raise SystemExit(__doc__)
    out = Path(args[0])
    requested = set(args[1:])
    path = HERE.parent / "type5_focus/fixed_elongated/generate.py"
    spec = importlib.util.spec_from_file_location("type5_fixed_gram", path)
    base = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base)
    cells = {"".join(map(str, a)): (a, q) for a, q in base.rep}
    if requested - cells.keys():
        raise SystemExit(f"Unknown cells: {sorted(requested - cells.keys())}")
    out.mkdir(parents=True, exist_ok=True)
    d = {(i, j): f"d{i}{j}" for i, j in combinations(range(8), 2)}
    x = {i: "0" if i == 1 else f"x{i}" for i in range(8)}
    b = {i: "0" if i == 1 else f"b{i}" for i in range(8)}

    def squared_lift(i, j, k):
        xx = base.add(base.sub(x[j], x[i]), base.num(base.F(k[0]) + base.F(k[1], 2)))
        bb = base.add(base.sub(b[j], b[i]), base.num(k[1]))
        return base.add(base.mul(base.num(base.F(1, base.W)), xx, xx), base.mul(bb, bb))

    for label in sorted(requested or cells.keys()):
        a, q = cells[label]
        old = base.generate(a, q, full=not necessary)
        new = augment(old, d, squared_lift)
        assert new.count("(declare-fun") == 18
        assert new.count("(assert ") - old.count("(assert ") == 21 + 4 * 36
        (out / (label + ".smt2")).write_text(new)
        print(label, "18 variables; 165 added strict inequalities; full=", not necessary)


if __name__ == "__main__":
    main()
