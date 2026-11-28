#!/usr/bin/env python3
"""Check the uniform C0 transport identities, without claiming exclusion.

This replays the complete marked metric binding, binds the section walks
to the actual faces, and verifies the circulation and adjacent-swap
identities exactly. No search, branch refinement, or feasibility verdict
is performed. See geometric_transport.md for the geometric proof and gap.
"""

from itertools import combinations
import json

import sympy as s

import exhaustive_remaining_axis as axis
import remaining_c0_nested_quadrilaterals as source
import solver_remaining_c1_geometry as horizontal
import solver_remaining_limit as reduction


HALF = s.Rational(1, 2)
DIRECT = ((0, 1), (0, 3), (0, 2), (2, 7), (1, 7), (1, 6))
LOWER = ((3, 6), (5, 6), (0, 5), (5, 7), (4, 7), (4, 6))
UPPER = ((3, 6), (3, 5), (2, 5), (2, 4), (1, 4), (3, 4))
MIDDLE_ALPHA_FIRST = ((3, 6), (5, 6), (0, 5), (5, 7),
                      (4, 5), (2, 4), (1, 4), (3, 4))
MIDDLE_BETA_FIRST = ((3, 6), (3, 5), (2, 5), (4, 5), (4, 7), (4, 6))


def zero(value):
    assert s.cancel(value) == 0


def section(points, levels, edges, tau):
    return [points[i] + (tau - levels[i]) / (levels[j] - levels[i])
            * (points[j] - points[i]) for i, j in edges]


def circulation(polygon, lengths, tau, dot):
    """Integral of P_sigma dot P_tau; no division by a shrinking side."""
    sigma = s.Integer(0)
    answer = s.Integer(0)
    for index, length in enumerate(lengths):
        edge = polygon[(index + 1) % len(polygon)] - polygon[index]
        answer += dot(edge, polygon[index].diff(tau)) - length * s.diff(sigma, tau)
        sigma += length
    return s.cancel(answer)


def universal_identities():
    c = s.Symbol('c')
    u = s.Matrix(s.symbols('u0:2'))
    tangent = s.Matrix(s.symbols('t0:2'))
    v = tangent - c * u
    trace = c * u.dot(v) + v.dot(v) / 2
    zero(trace - (tangent.dot(tangent) - c*c) / 2
         + c*c * (u.dot(u) - 1) / 2)

    length, width, dl, dm, cosine = s.symbols('length width dl dm cosine')
    # Terms from the moving block origin and the external arclength offset
    # agree in the two orders and cancel.
    first_then_second = width * dl * (cosine - 1)
    second_then_first = length * dm * (cosine - 1)
    zero(second_then_first - first_then_second
         - (width * dl - length * dm) * (1 - cosine))
    a, b, tau = s.symbols('a b tau')
    zero((width * dl - length * dm).subs(
        {length: a*tau, width: b*(1-tau), dl: a, dm: -b}) - a*b)

    # The row/column identities use only unit total lengths and the two
    # vector closures. Check the algebra before imposing those premises.
    aa = s.symbols('a0:3')
    bb = s.symbols('b0:3')
    ee = [s.Matrix(s.symbols(f'e{i}_0:2')) for i in range(3)]
    ff = [s.Matrix(s.symbols(f'f{i}_0:2')) for i in range(3)]
    weights = [[aa[i]*bb[j]*(1-ee[i].dot(ff[j])) for j in range(3)]
               for i in range(3)]
    closure_e = sum((aa[i]*ee[i] for i in range(3)), s.zeros(2, 1))
    closure_f = sum((bb[j]*ff[j] for j in range(3)), s.zeros(2, 1))
    for i in range(3):
        zero(sum(weights[i]) - aa[i]*(sum(bb)-ee[i].dot(closure_f)))
    for j in range(3):
        zero(sum(weights[i][j] for i in range(3))
             - bb[j]*(sum(aa)-ff[j].dot(closure_e)))
    zero(sum(map(sum, weights)) - sum(aa)*sum(bb) + closure_e.dot(closure_f))
    return {'crease_trace_identity': True, 'adjacent_swap_identity': True,
            'swap_weight_row_column_and_total_identities': True}


def face_and_section_bindings():
    alpha, beta, tau = s.symbols('alpha beta tau')
    levels = (0, 1, 1, 1, alpha, beta, 0, 0)
    points = [s.zeros(2, 1), s.zeros(2, 1)]
    points += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    _, oriented_faces, edges = axis.case_data(1)
    faces = {frozenset(face) for face in oriented_faces}
    actual_edges = {frozenset(edge) for edge in edges}
    used = {}
    for name, walk in [('direct', DIRECT), ('lower', LOWER), ('upper', UPPER),
                       ('alpha_first', MIDDLE_ALPHA_FIRST), ('beta_first', MIDDLE_BETA_FIRST)]:
        polygon = section(points, levels, walk, tau)
        face_set = set()
        for index, (i, j) in enumerate(walk):
            assert frozenset((i, j)) in actual_edges
            fraction = (tau-levels[i])/(levels[j]-levels[i])
            zero((1-fraction)*levels[i] + fraction*levels[j] - tau)
            for coordinate in polygon[index] - ((1-fraction)*points[i]+fraction*points[j]):
                zero(coordinate)
            face = frozenset(walk[index]) | frozenset(walk[(index+1) % len(walk)])
            assert len(face) == 3 and face in faces
            face_set.add(face)
        used[name] = face_set
    assert len(used['direct']) == 6
    complement = faces - used['direct']
    assert len(complement) == 10
    assert used['lower'] | used['upper'] == complement
    assert used['alpha_first'] <= complement and used['beta_first'] <= complement
    cap_edges = {frozenset(edge) for cap in ((1, 2, 3), (0, 6, 7))
                 for edge in combinations(cap, 2)}
    for annulus in (used['direct'], complement):
        counts = {edge: sum(edge <= face for face in annulus)
                  for face in annulus for edge in map(frozenset, combinations(face, 2))}
        assert {edge for edge, count in counts.items() if count == 1} == cap_edges
    return {'actual_faces_bound': 16, 'section_walks_bound': 5,
            'both_distinct_height_orders_bound': True}


def face_horizontal_norms():
    """Every horizontal face direction has norm one by the full source."""
    u, v = s.symbols('u v')
    matrix = reduction.original_system((HALF, HALF, HALF, 1-u, -v, 0))
    _, faces, edges = axis.case_data(1)
    levels = (0, HALF, HALF, HALF, u, v, 0, 0)
    for face in faces:
        i, j, k = face
        a, b = levels[k]-levels[i], levels[j]-levels[i]
        row = [s.Integer(0)] * 29
        for edge, coefficient in [((i, j), a*(a-b)),
                                  ((i, k), b*(b-a)), ((j, k), a*b)]:
            row[edges.index(tuple(sorted(edge)))] += coefficient
        if set(face) == {2, 4, 5}:
            row[25] -= (u-v)/2
        if set(face) == {4, 5, 7}:
            row[28] -= (u-v)/2
        assert all(s.expand(value) == 0 for value in s.Matrix([row])*matrix)
    # The stress is exactly the horizontal-vector squared-norm residual.
    a, b, x, y, tij, tik, tjk = s.symbols('a b x y tij tik tjk')
    numerator_norm = a*a*(x*x+tij) + b*b*(y*y+tik)
    numerator_norm -= a*b*(x*x+tij+y*y+tik-(y-x)**2-tjk)
    zero(numerator_norm-(a*x-b*y)**2
         - (a*(a-b)*tij+b*(b-a)*tik+a*b*tjk))
    return {'horizontal_face_norm_stresses': len(faces), 'all_q_syzygies_retained': True}


def circulation_identities():
    alpha, beta, tau = s.symbols('alpha beta tau')
    h = s.symbols('h0:8')
    d = [HALF-value for value in h]
    L, M = 1-h[1]-h[2], 1-h[6]-h[7]
    D = h[3]+h[4]+h[5]-1
    r, radius5 = h[3]-(1-alpha)*D, h[5]-beta*D
    points = [s.zeros(6, 1), s.zeros(6, 1)]
    points += [s.eye(6)[:, i] for i in range(6)]
    gram = s.zeros(6, 6)
    for i in range(6):
        for j in range(i, 6):
            gram[i, j] = gram[j, i] = s.Symbol(f'g{i+2}{j+2}')
    for i, value in [(0, h[1]**2), (1, L**2), (4, M**2), (5, h[7]**2)]:
        gram[i, i] = value
    gram[0, 1] = gram[1, 0] = (h[1]**2+L**2-h[2]**2)/2
    gram[4, 5] = gram[5, 4] = (M**2+h[7]**2-h[6]**2)/2
    gram[0, 5] = gram[5, 0] = d[0]-h[1]*h[7]
    dot = lambda first, second: (first.T*gram*second)[0]
    levels = (0, 1, 1, 1, alpha, beta, 0, 0)
    E, F = points[3]-points[2], points[7]-points[6]
    Q4 = points[4]-alpha*points[3]-(1-alpha)*points[6]
    Q5 = points[5]-beta*points[3]-(1-beta)*points[6]

    direct_lengths = [tau*L, tau*h[2], (1-tau)*h[7],
                      tau*h[1], (1-tau)*h[6], (1-tau)*M]
    direct = section(points, levels, DIRECT, tau)
    zero(sum(direct_lengths)-1)
    zero(circulation(direct, direct_lengths, tau, dot) - (d[0]-HALF))

    lower_middle_speed = (1-h[6]-radius5)/beta + (h[6]-r)/alpha
    lower_lengths = [tau*radius5/beta, (1-tau/beta)*M,
                     (1-tau/beta)*h[7], tau*lower_middle_speed,
                     (1-tau/alpha)*h[6], tau*r/alpha]
    lower = section(points, levels, LOWER, tau)
    zero(sum(lower_lengths)-1)
    lower_endpoint = circulation(lower, lower_lengths, tau, dot).subs(tau, 0)
    lower_formula = (h[6]*r-dot(F, Q4))/alpha
    lower_formula += (dot(F, Q5)+HALF-h[6]-(1-h[6])*radius5)/beta
    zero(lower_endpoint-lower_formula)
    lambda_f = dot(F, beta*Q4-alpha*Q5)-h[6]*(beta*r+alpha*radius5)
    lambda_f += alpha*(h[6]-d[5])
    zero(lower_formula-D+lambda_f/(alpha*beta))

    upper_middle_speed = (h[2]-radius5)/(1-beta) + (1-h[2]-r)/(1-alpha)
    upper_lengths = [(1-tau)*radius5/(1-beta), (tau-beta)*h[2]/(1-beta),
                     (1-tau)*upper_middle_speed, (tau-alpha)*h[1]/(1-alpha),
                     (tau-alpha)*L/(1-alpha), (1-tau)*r/(1-alpha)]
    upper = section(points, levels, UPPER, tau)
    zero(sum(upper_lengths)-1)
    upper_endpoint = circulation(upper, upper_lengths, tau, dot).subs(tau, 1)
    upper_formula = (dot(E, Q5)+h[2]*radius5)/(1-beta)
    upper_formula += (HALF-h[2]-dot(E, Q4)-(1-h[2])*r)/(1-alpha)
    zero(upper_endpoint-upper_formula)
    lambda_e = dot(E, (1-beta)*Q4-(1-alpha)*Q5)
    lambda_e -= h[2]*((1-beta)*r+(1-alpha)*radius5)
    lambda_e += (1-beta)*(h[2]-d[3])
    zero(upper_formula-D+lambda_e/((1-alpha)*(1-beta)))

    N = points[4]-points[5]
    zero((lambda_e/(1-beta)).subs(beta, alpha)
         - (dot(E, N)+h[2]*h[4]-d[3]))
    zero((lambda_f/alpha).subs(beta, alpha)
         - (dot(F, N)+h[6]*h[4]-d[5]))
    zero(D-h[4]*(1-h[2]-h[6])+dot(E+F, N)
         - ((lambda_e/(1-beta)).subs(beta, alpha)+(lambda_f/alpha).subs(beta, alpha)))
    zero(((r+radius5)**2-2*d[4]-h[4]**2).subs(beta, alpha))

    X = horizontal.horizontal_displacements(h)
    zero(X[0, 1]+h[0])
    zero(-X[3, 6]-D)
    for mark in (1, 2):
        budget = {h[7]: s.Rational(9, 2)-mark-sum(h[:7])}
        zero((d[0]+L+M-D-(mark-1)).subs(budget))
    return {'direct_circulation': 'd0-1/2', 'complement_circulation': 'D',
            'lower_and_upper_endpoint_formulas': True,
            'diagonal_dot_formula': True, 'anchor_phase_cocycle_bindings': 2,
            'marking_values': {'ray1': 0, 'ray2': 1}}


def verify():
    return {'source': source.metric_checks(),
            'sections': face_and_section_bindings(),
            'face_norms': face_horizontal_norms(),
            'universal': universal_identities(),
            'circulation': circulation_identities(),
            'phase_window_proved': False,
            'degenerate_cap_or_height_endpoint_exclusion': False,
            'new_exclusion_claimed': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    print(json.dumps(verify(), sort_keys=True))
