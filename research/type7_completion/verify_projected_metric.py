#!/usr/bin/env python3
"""Check the projected-area encoding by exact independent vector algebra.

Run with Python, SymPy, and shared libz3, with assertions enabled.  This
checks identities, scaling, the 24-case list, and parsing of the full
query.  It neither invokes an SMT search nor proves ray-3 infeasibility.
"""

import ctypes as ct
import ctypes.util
from fractions import Fraction as F
from itertools import combinations, product

import sympy as s

import projected_metric as p


def check_identity():
    e = s.Matrix(s.symbols("e0:3"))
    a = s.Matrix(s.symbols("a0:3"))
    b = s.Matrix(s.symbols("b0:3"))
    gram = s.Matrix([[u.dot(v) for v in (e, a, b)] for u in (e, a, b)])
    triple = e.dot(a.cross(b))
    assert s.expand(gram.det() - triple ** 2) == 0
    # Area of the orthogonal projections: no assumption about a or b
    # being transverse, independent, or nonzero is made.
    en = e.dot(e)
    pa = en * a - e.dot(a) * e
    pb = en * b - e.dot(b) * e
    assert all(s.expand(c) == 0 for c in pa.cross(pb) - en * triple * e)
    print("PASS exact Gram/orthogonal-projection identities")


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def parse(text):
    tokens = text.replace("(", " ( ").replace(")", " ) ").split()
    pos = 0

    def term():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token != "(":
            return token
        result = []
        while tokens[pos] != ")":
            result.append(term())
        pos += 1
        return result

    result = []
    while pos < len(tokens):
        result.append(term())
    return result


def evaluate(term, env):
    if isinstance(term, str):
        return env[term] if term in env else F(term)
    op, *args = term
    vals = [evaluate(a, env) for a in args]
    if op == "+":
        return sum(vals)
    if op == "-":
        return -vals[0] if len(vals) == 1 else vals[0] - vals[1]
    if op == "*":
        value = F(1)
        for v in vals:
            value *= v
        return value
    if op == "/":
        return vals[0] / vals[1]
    if op == "<=":
        return vals[0] <= vals[1]
    if op == ">=":
        return vals[0] >= vals[1]
    if op == "or":
        return any(vals)
    raise ValueError(op)


def check_cases_and_scale():
    expected_triangles = {
        q for cap in ((0, 1, 4, 5), (2, 3, 6, 7))
        for q in combinations(cap, 3)
    }
    rows = p.determinant_pairs()
    assert {tuple(map(int, name[4:])) for name, _, _ in rows[:8]} == expected_triangles
    assert {(a, b) for _, a, b in rows[8:]} == set(product(
        ((0, 1), (1, 4), (4, 5), (5, 0)),
        ((2, 3), (3, 6), (6, 7), (7, 2))))
    relative = p.relative_comparisons()
    assert relative[1] == ("cap_015", (5, 0), (0, 1))
    assert relative[5] == ("cap_237", (7, 2), (2, 3))
    short = set(p.ring_edges(p.CAP_A) + p.ring_edges(p.CAP_B))
    assert all(a in short and b in short for _, a, b in relative)
    # A non-axis-aligned longitudinal vector prevents a coordinate-plane
    # area from accidentally passing as an orthogonal-projection area.
    configurations = [
        [(7, -2, 11), (2, 3, 5), (10, 2, 23), (1, -4, 2),
         (3, 8, 1), (-5, 7, 6), (9, -1, 3), (0, 6, -7)],
        # Includes exactly zero projected areas and collinear cap edges.
        [(0, 0, 0), (1, 2, 3), (3, 4, 12), (6, 8, 24),
         (2, 4, 6), (4, 8, 12), (-3, -4, -12), (9, 12, 36)],
    ]
    for y, points in product((8, 17, 10 ** 6), configurations):
        lines, _ = p.projected_constraints(y)
        origin = points[0]
        r = [sub(v, origin) for v in points]
        env = {f"G{i}{j}": F(dot(r[i], r[j]), y * y)
               for i in range(1, 8) for j in range(i, 8)}
        e = sub(r[2], r[0])
        ee = dot(e, e)
        assert ee > 0
        env["D02"] = F(ee, y * y)
        for n, edge in enumerate(p.ring_edges(p.CAP_A) + p.ring_edges(p.CAP_B)):
            i, j = edge
            h = F(1, n + 3)
            sign = 1 if i < j else -1
            env[f"X{min(i, j)}{max(i, j)}"] = -sign * h
            env[f"V{min(i, j)}{max(i, j)}"] = sign * h / (4 * y * y)
        for form in parse("\n".join(p.relative_edge_constraints(y))):
            op, a, b = form[1]
            lhs, rhs = evaluate(a, env), evaluate(b, env)
            assert lhs < rhs if op == "<" else lhs > rhs
        parsed = parse("\n".join(lines))
        for form in parsed[:-1]:
            if form[0] == "define-fun":
                env[form[1]] = evaluate(form[4], env)
            else:
                assert form[0] == "assert" and evaluate(form[1], env)
        union = parsed[-1][1]
        actual_small = []
        for (name, (i, j), (k, l)), test in zip(rows, union[1:]):
            a, b = sub(r[j], r[i]), sub(r[l], r[k])
            area_squared = F(dot(e, cross(a, b)) ** 2, ee)
            encoded_area_squared = y ** 4 * env["projected_gram_" + name] / env["D02"]
            assert encoded_area_squared == area_squared
            is_small = area_squared <= F(160000, y ** 4)
            assert evaluate(test, env) == is_small
            actual_small.append(is_small)
        assert evaluate(union, env) == any(actual_small)
        relative_tests = parse(p.relative_projected_union(y))[0][1]
        for (name, a, b), test, (_, old_a, old_b) in zip(relative, relative_tests[1:], rows):
            pa, pb = sub(r[a[1]], r[a[0]]), sub(r[b[1]], r[b[0]])
            old_pa, old_pb = sub(r[old_a[1]], r[old_a[0]]), sub(r[old_b[1]], r[old_b[0]])
            # Consecutive-edge triangle areas equal the old first-vertex
            # areas, but their horizontal weight must use actual edges.
            assert dot(e, cross(pa, pb)) == dot(e, cross(old_pa, old_pb))
            h, k = (-evaluate(parse(p.directed_symbol("X", edge))[0], env) for edge in (a, b))
            area_squared = F(dot(e, cross(pa, pb)) ** 2, ee)
            assert evaluate(test, env) == (area_squared <= F(1296, y ** 4) * h * h * k * k)
    for invalid in (0, 4, 7, 8.0, True):
        try:
            p.projected_constraints(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError(invalid)
    print("PASS all 24 absolute/relative scaled terms, including zero projected areas")
    print("PASS cap-triangle weights use consecutive ring edges; all eight relative slope cuts")


def check_query():
    text, metadata = p.generate()
    assert metadata["real_variables"] == 18
    assert metadata["boolean_variables"] == 312
    assert metadata["cnf_clauses"] == 8075
    assert metadata["circuit_partitions"] == 524
    assert metadata["projected_determinants"] == 24
    assert metadata["physical_area_bound"] == "1/2500000000"
    assert metadata["scaled_gram_coefficient"] == str(10 ** 48)
    assert text.count("(check-sat)") == 1
    assert "(assert (> D02 0))" in text
    assert text.count("(declare-fun ") == 18 + 312
    # Parse all assertions with the native API, without calling check_sat.
    z = ct.CDLL(ctypes.util.find_library("z3"))
    ptr = ct.c_void_p
    funcs = [
        ("Z3_mk_config", ptr, []),
        ("Z3_mk_context", ptr, [ptr]),
        ("Z3_del_config", None, [ptr]),
        ("Z3_del_context", None, [ptr]),
        ("Z3_parse_smtlib2_string", ptr,
         [ptr, ct.c_char_p, ct.c_uint, ptr, ptr, ct.c_uint, ptr, ptr]),
        ("Z3_ast_vector_size", ct.c_uint, [ptr, ptr]),
        ("Z3_get_error_code", ct.c_uint, [ptr]),
    ]
    for name, result, args in funcs:
        fn = getattr(z, name)
        fn.restype, fn.argtypes = result, args
    config = z.Z3_mk_config()
    ctx = z.Z3_mk_context(config)
    z.Z3_del_config(config)
    try:
        body = text.removesuffix("(check-sat)\n").encode()
        assertions = z.Z3_parse_smtlib2_string(ctx, body, 0, None, None, 0, None, None)
        assert z.Z3_get_error_code(ctx) == 0
        count = z.Z3_ast_vector_size(ctx, assertions)
        assert count == text.count("(assert ")
    finally:
        z.Z3_del_context(ctx)
    print(f"PASS full query parses: {count} assertions; 18 reals, 312 Booleans")


if __name__ == "__main__":
    check_identity()
    check_cases_and_scale()
    check_query()
    print("No solver search or Type 7 marking exclusion is claimed.")
