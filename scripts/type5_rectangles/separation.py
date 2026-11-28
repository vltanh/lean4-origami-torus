"""A finite determinant-sign implication, with coplanarity allowed."""

from itertools import combinations, product
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory

from scripts.type5_planar_masks import check_rup


def check_implication(complex_, signs):
    # Two Boolean variables encode strict positivity and strict negativity.
    clauses = []
    last = 0

    def fresh():
        nonlocal last
        last += 1
        return last

    def sign_pair():
        pos, neg = fresh(), fresh()
        clauses.append([-pos, -neg])
        return pos, neg

    variables = {q: sign_pair() for q in combinations(range(8), 4)}

    def bracket(labels):
        pair = variables[tuple(sorted(labels))]
        inversions = sum(a > b for a, b in combinations(labels, 2))
        return pair[::-1] if inversions % 2 else pair

    def multiply(a, b):
        pair = sign_pair()
        for i, j in product(range(2), repeat=2):
            clauses.append([-a[i], -b[j], pair[i ^ j]])
        for v in pair:
            clauses.extend([[-v, *a], [-v, *b]])
        return pair

    def zero_sum(terms):
        # A strict sign in a sum equal to zero needs an opposite strict sign.
        for pos, neg in terms:
            clauses.append([-pos, *(q[1] for q in terms if q != (pos, neg))])
            clauses.append([-neg, *(q[0] for q in terms if q != (pos, neg))])

    for a, b in combinations(range(8), 2):
        for c, d, e, f in combinations(sorted(set(range(8))-{a, b}), 4):
            zero_sum([multiply(bracket((a,b,c,d)), bracket((a,b,e,f))),
                      multiply(bracket((a,b,c,e))[::-1], bracket((a,b,d,f))),
                      multiply(bracket((a,b,c,f)), bracket((a,b,d,e)))])
    for labels in combinations(range(8), 5):
        zero_sum([bracket(labels[:i]+labels[i+1:])[::(-1)**i] for i in range(5)])

    failures = []
    for edge, face in complex_.disjoint:
        labels = tuple(sorted((*edge, *face)))
        cofactors = [bracket(labels[:i]+labels[i+1:])[::(-1)**i*(1 if v in edge else -1)]
                     for i, v in enumerate(labels)]
        for i in range(2):
            failure = fresh()
            failures.append(failure)
            clauses.extend([[-failure, -pair[i]] for pair in cofactors])
    clauses.append(failures)
    for labels, sign in signs.items():
        if sign not in (-1, 1):
            raise ArithmeticError(f"missing strict base-point sign for {labels}")
        clauses.append([variables[labels][int(sign < 0)]])

    refute(clauses, last)


def refute(clauses, variable_count):
    """Require a propositional refutation and replay its individual inferences."""
    solver = shutil.which("cadical") or str(Path(subprocess.check_output(
        ["lean", "--print-prefix"], text=True).strip()) / "bin" / "cadical")
    with TemporaryDirectory() as directory:
        cnf = Path(directory)/"separation.cnf"
        proof = Path(directory)/"separation.lrat"
        cnf.write_text(f"p cnf {variable_count} {len(clauses)}\n" +
                       "".join(" ".join(map(str, row))+" 0\n" for row in clauses))
        result = subprocess.run([solver, "--lrat", "--no-binary", "--quiet", cnf, proof],
                                capture_output=True)
        if result.returncode != 20:
            raise ArithmeticError("the determinant-sign clauses admit no certified refutation")
        check_rup(clauses, proof)
