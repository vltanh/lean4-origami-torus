#!/usr/bin/env python3
"""Exact checks for the direct ray-3 chart; no SMT feasibility search."""

import ctypes as ct
import ctypes.util
import re
from fractions import Fraction as F
from itertools import product

import sympy as s

import direct_metric as d
import verify_projected_metric as v


def check_reconstruction():
    t, L = s.symbols("t L", positive=True)
    xx, dg, dr, u, vv = s.symbols("xx dg dr u vv", real=True)
    c0, den = L ** 2 - 1 / (4 * t), 4 * t * L ** 2
    for ell in (-1, 0, 1):
        for ky in (s.Rational(-1, 2), s.Rational(1, 2)) if ell else (s.Integer(0),):
            physical = u ** 2 + vv ** 2 + (L * ell + dr / (2 * L)) ** 2
            intrinsic = xx ** 2 + (ky + t * dg) ** 2 / t
            residual = den * (u ** 2 + vv ** 2 + ell * dr + ell ** 2 * c0
                              - xx ** 2 - 2 * ky * dg - t * dg ** 2) + t * dr ** 2
            assert s.expand(residual - den * (physical - intrinsic)) == 0
    rho, cap = s.symbols("rho cap", real=True)
    assert s.expand((den / L) * (L * cap + rho / (2 * L))
                    - (den * cap + 2 * t * rho)) == 0
    px1, py3 = s.symbols("px1 py3", real=True)
    W = s.Matrix([[px1, 0, s.Symbol("z1")], [0, 0, den],
                  [s.Symbol("px3"), py3, s.Symbol("z3")]])
    assert s.expand(W.det() + px1 * den * py3) == 0
    print("PASS exact metric/reconstruction identities and anchor orientation")


def symbolic(term, env):
    if isinstance(term, str):
        return env[term] if term in env else s.Rational(term)
    op, *args = term
    xs = [symbolic(a, env) for a in args]
    if op == "+":
        return sum(xs)
    if op == "-":
        return -xs[0] if len(xs) == 1 else xs[0] - xs[1]
    if op == "*":
        return s.prod(xs)
    if op == "/":
        return xs[0] / xs[1]
    raise ValueError(op)


def check_emitted_polynomials():
    text, metadata = d.generate()
    forms = v.parse(text)
    env = {}
    variables = []
    degrees = {}
    for form in forms:
        if form[0] == "declare-fun" and form[3] == "Real":
            variable = s.Symbol(form[1])
            variables.append(variable)
            env[form[1]] = variable
        if form[0] == "define-fun" and (form[1].startswith(("X", "V", "metric", "rho"))
                                       or form[1] in ("c0", "den")):
            env[form[1]] = s.expand(symbolic(form[4], env))
            if form[1].startswith("metric"):
                degrees[form[1]] = s.Poly(env[form[1]], *variables).total_degree()
    assert len(variables) == 27 and len(degrees) == 19
    assert max(degrees.values()) == 4
    assert metadata["circuit_partitions"] == 524
    assert metadata["boolean_variables"] == 312
    assert metadata["cnf_clauses"] == 8075
    assert not re.search(r"\bG[1-7][1-7]\b", text)
    print("PASS 19 emitted metric polynomials have degree at most four")


def check_emitted_minors():
    _, _, edges, _, _, kx, ky = d.load_data()
    for y, planar_caps in product((8, 10 ** 6), (False, True)):
        t = F(1, y * y)
        text, _ = d.generate(y)
        forms = v.parse(text)
        env = {}
        for form in forms:
            if form[0] == "declare-fun" and form[3] == "Real":
                # Exact deliberately nonsymmetric rational coordinates.
                name = form[1]
                env[name] = F((sum(map(ord, name)) % 29) - 13, 7)
        # Make the physical anchor length rational, with nonzero c0.
        env["x2"], env["gamma2"] = F(3 * y, 8) - kx[0, 2], F(0)
        L = F(5 * y, 8)
        if planar_caps:
            for i in d.V[1:]:
                env[f"x{i}"] = env[f"gamma{i}"] = F(0)
            env["gamma1"], env["gamma5"] = F(1, 4), F(-1, 4)
            env["rho4"] = env["rho6"] = F(0)
            L = F(y, 2)
        for form in forms:
            if form[0] == "define-fun" and form[1] != "long_link":
                env[form[1]] = v.evaluate(form[4], env)
        P = {0: (F(0), F(0)), 2: (F(0), F(0))} | {
            i: (env[f"px{i}"], F(0) if i == 1 else env[f"py{i}"])
            for i in d.OTHER}
        rho = {0: F(0), 2: F(0)} | {i: env[f"rho{i}"] for i in d.OTHER}
        points = {i: (*P[i], L * int(i in d.p.CAP_B) + rho[i] / (2 * L)) for i in d.V}
        minor_count = metric_count = area_count = 0
        for form in forms:
            if form[0] != "define-fun" or form[1] == "long_link":
                continue
            name = form[1]
            env[name] = v.evaluate(form[4], env)
            if name == "den":
                assert env[name] == 4 * t * L * L
            match = re.fullmatch(r"a([0-7]+)c([012]+)", name)
            if match:
                indices, axes = [tuple(map(int, q)) for q in match.groups()]
                a, *rest = indices
                actual = s.Matrix([[points[i][k] - points[a][k] for k in axes]
                                   for i in rest]).det()
                if 2 in axes:
                    actual *= env["den"] / L
                    if len({i in d.p.CAP_B for i in indices}) == 1:
                        actual /= 2 * t
                assert env[name] == actual, (y, planar_caps, name)
                minor_count += 1
            if name.startswith("metric"):
                i, j = map(int, name[6:])
                physical = sum((points[j][k] - points[i][k]) ** 2 for k in range(3))
                intrinsic = env[f"X{i}{j}"] ** 2 + y * y * env[f"V{i}{j}"] ** 2
                assert env[name] == env["den"] * (physical - intrinsic)
                metric_count += 1
            if name.startswith("projected_area_"):
                key = name.removeprefix("projected_area_")
                _, (i, j), (k, l) = next(row for row in d.p.determinant_pairs() if row[0] == key)
                a, b = v.sub(P[j], P[i]), v.sub(P[l], P[k])
                assert env[name] == a[0] * b[1] - a[1] * b[0]
                area_count += 1
        assert minor_count == 322 and metric_count == 19 and area_count == 24
        for i in d.ELIMINATED_HEIGHTS:
            def intrinsic(a, b):
                xx = env[f"x{b}"] if b else F(0)
                xx -= env[f"x{a}"] if a else F(0)
                gg = env[f"gamma{b}"] if b else F(0)
                gg -= env[f"gamma{a}"] if a else F(0)
                return (xx + kx[a, b]) ** 2 + y * y * (ky[a, b] + t * gg) ** 2
            physical_difference = sum((points[i][k] - points[0][k]) ** 2
                                      - (points[i][k] - points[2][k]) ** 2 for k in range(3))
            assert physical_difference == intrinsic(0, i) - intrinsic(2, i)
        if planar_caps:
            assert all(value == 0 for value in rho.values())
            assert env["a0145c012"] == env["a2367c012"] == 0
    print("PASS all 322 incidence minors, 19 metrics, and 24 areas against exact physical points")
    print("PASS four exact height eliminations recover the dropped anchor-edge equations")
    print("PASS exactly planar caps remain in the chart; no zero determinant is divided out")


def check_parse():
    text, _ = d.generate()
    z = ct.CDLL(ctypes.util.find_library("z3"))
    ptr = ct.c_void_p
    for name, result, args in [
        ("Z3_mk_config", ptr, []), ("Z3_mk_context", ptr, [ptr]),
        ("Z3_del_config", None, [ptr]), ("Z3_del_context", None, [ptr]),
        ("Z3_parse_smtlib2_string", ptr,
         [ptr, ct.c_char_p, ct.c_uint, ptr, ptr, ct.c_uint, ptr, ptr]),
        ("Z3_ast_vector_size", ct.c_uint, [ptr, ptr]),
        ("Z3_get_error_code", ct.c_uint, [ptr]),
    ]:
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
    print(f"PASS full direct query parses: {count} assertions; 27 reals, 312 Booleans")


if __name__ == "__main__":
    check_reconstruction()
    check_emitted_polynomials()
    check_emitted_minors()
    check_parse()
    print("No Type 7 marking exclusion is claimed.")
