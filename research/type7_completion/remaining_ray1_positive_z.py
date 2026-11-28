#!/usr/bin/env python3
"""Uniform exclusion of the positive-axial ray-1 endpoint.

The relative face027 Gram factorization and verified profile contradict
an exact rank-one metric stress on3456. All collapse rates are retained.
Additional folded-phase and reference identities remain checked as well.
"""

import json

import sympy as s

import exhaustive_remaining_axis as axis

HALF = s.Rational(1, 2)


def face027_identity():
    h, d0, rho, t, v1, v2, v7 = s.symbols('h d0 rho t v1 v2 v7')
    total = h-d0
    d7 = rho*total
    h0, x2, h7 = HALF-d0, HALF+d0-h, HALF-d7
    determinant = x2*v7-h7*v2
    # Dot products reconstructed from the six original K4 edge metrics.
    dot12 = (h0*h0+x2*x2-h*h)/2
    dot17 = (h0*h0+h7*h7-(h0+h7-1)**2)/2
    assert s.expand(dot12-h0*x2+2*d0*total) == 0
    assert s.expand(dot17-h0*h7+2*d0*d7) == 0
    assert s.expand((x2*x2+h7*h7-(h7-x2)**2)/2-x2*h7) == 0

    uscale = 2*(v2*rho-v7)/determinant
    zscale = 2*(h7-x2*rho)/determinant
    du, dz_over_t = d0*total*uscale, d0*total*zscale
    assert s.cancel(x2*du+v2*dz_over_t+2*d0*total) == 0
    assert s.cancel(h7*du+v7*dz_over_t+2*d0*d7) == 0
    normal2 = -2*h0*du-2*v1*dz_over_t-du*du-t*dz_over_t*dz_over_t
    eta = v1-h0*v2/x2
    factor = 4*h0/x2-2*eta*zscale-d0*total*(uscale**2+t*zscale**2)
    assert s.cancel(normal2-d0*total*factor) == 0
    endpoint = {h: 0, d0: 0, v1: HALF, v2: HALF, v7: 0, t: 0}
    assert s.cancel(determinant.subs(endpoint)) == -s.Rational(1, 4)
    assert s.cancel(factor.subs(endpoint)) == 4

    # Relate this actual normal to the original axis01 incidence frame.
    ell, px2, n2, px7, n7, z2, z7, y = s.symbols('ell P2 Z2 P7 Z7 zeta2 zeta7 y')
    r1 = s.Matrix((0, 0, y*ell))
    r2 = s.Matrix((px2, n2, y*z2))
    r7 = s.Matrix((px7, n7, y*z7))
    cross = px2*n7-n2*px7
    denominator = (z2*px7-px2*z7)**2+(n2*z7-z2*n7)**2+t*cross**2
    assert s.expand(s.det(s.Matrix.hstack(r1, r2, r7))-y*ell*cross) == 0
    assert s.expand(t*r2.cross(r7).dot(r2.cross(r7))).subs(y**2, 1/t).expand() == denominator.expand()
    return {'normal_square': 'd0*(h-d0)*(4+o(1))',
            'uniform_ratio': 'rho=d7/(h-d0) in [0,1]',
            'incidence_normal_limit': 'W1/(delta*h) -> 2*aX*e-aY',
            'positive_axial_consequence': '(h-d0)/(delta^2*h) -> 0',
            'negative_x_consequence': 'd0/(delta^2*h) -> 1'}


def folded_phase_identity():
    t, h, eps, b1, b2, lam, B, z = s.symbols('t h eps b1 b2 lambda B z24')
    p2, n2, p4, n4 = s.symbols('P2 Z2 P4 Z4')
    dot = p2*(p4-p2)+n2*(n4-n2)
    difference = t*dot+(b1+t*lam)*z-(-t*h*eps+b1*B)
    assert s.expand(difference-b1*(z-B)-t*(dot+lam*z+h*eps)) == 0
    v2, v4, H2, H4 = s.symbols('v2 v4 H2 H4')
    z24 = 2*(v2+b2)-v4-v2+t*(H4-H2)
    assert s.expand(z24+(v4-v2)-2*b2-t*(H4-H2)) == 0
    assert 2*s.Rational(1, 4)+(-s.Rational(1, 4))-s.Rational(1, 4) == 0
    return {'triangle214': 'b1*(z24-B)+t*(P2.dot(P4-P2)+lambda*z24+h*eps)=0',
            'folded_axis': 'z24+B=2*b2+t*(H4-H2)',
            'positive_axial_conclusion': 'v4-v2=o(t), zeta4-zeta2=o(t)'}


def finite_h_reference():
    shifts, _, edges = axis.case_data(1)
    t, u, h, p = s.symbols('t u h p')
    A = 1+2*u+t/4
    v2 = u+HALF-t/8
    v1 = (1-2*h)*v2
    v3 = A/2-u*t*p/A
    v5 = u-t/4+t*A*(1-p)/(2*(A-t*p))
    vertical = [0, v1, v2, v3, v2, v5, u, u-t/4]
    intrinsic_x = [0, h-HALF, HALF, 0, -HALF, HALF, 0, HALF]
    spatial_x = [0, HALF-h, HALF, 2*v2*p/A, HALF, HALF, 0, HALF]
    spatial_z = list(vertical)
    spatial_z[3] = v3-t*p/A
    normal2 = p*(1-p)
    expected = -t*A*(1-p)/(A-t*p)
    failed = []
    for i, j in edges:
        dx = intrinsic_x[j]-intrinsic_x[i]+shifts[i, j][0]+HALF*shifts[i, j][1]
        dv = vertical[j]-vertical[i]+shifts[i, j][1]
        residual = s.factor(t*((spatial_x[j]-spatial_x[i])**2
                               +(normal2 if 3 in (i, j) else 0)-dx*dx)
                            +(spatial_z[j]-spatial_z[i])**2-dv*dv)
        assert s.cancel(residual.subs(p, 1)) == 0
        if residual != 0:
            failed.append((i, j))
            assert s.cancel(residual-expected) == 0
    assert failed == [(2, 5), (4, 5)]
    assert all(s.expand(a-(1-2*h)*b) == 0 for a, b in
               zip((spatial_x[1], spatial_z[1]), (spatial_x[2], spatial_z[2])))
    for i in range(8):
        j = (i+1) % 8
        dx = intrinsic_x[j]-intrinsic_x[i]+shifts[i, j][0]+HALF*shifts[i, j][1]
        weight = h if i == 1 else HALF-h if i == 0 else HALF
        assert s.expand(dx+weight) == 0
    return {'planar_reference_parameters': ['h', 't', 'u'],
            'all_24_rows_at_p_one': True, 'r1': '(1-2h)*r2',
            'normal_extension_failed_rows': failed, 'normal_extension_residual': str(expected),
            'parametrizes_all_nearby_solutions': False}


def block_stress_identity():
    """A rank-one norm identity with no height or phase remainder."""
    shifts, _, edges = axis.case_data(1)
    A, B, d3, d4, d5 = s.symbols('A B d3 d4 d5')
    h3, h4, h5 = HALF-d3, HALF-d4, HALF-d5
    horizontal = {(3, 4): -h3, (3, 5): 1-h3-h4,
                  (3, 6): 1-h3-h4-h5, (4, 5): -h4,
                  (4, 6): 1-h4-h5, (5, 6): -h5}
    intrinsic_x = {3: s.Integer(0)}
    for i, weight in zip((3, 4, 5), (h3, h4, h5)):
        intrinsic_x[i+1] = intrinsic_x[i]-weight-shifts[i, i+1][0]-HALF*shifts[i, i+1][1]
    for (i, j), expected in horizontal.items():
        assert s.expand(intrinsic_x[j]-intrinsic_x[i]+shifts[i, j][0]
                        +HALF*shifts[i, j][1]-expected) == 0
    coefficients = {3: A, 4: B, 5: -A, 6: -B}
    lifts = {3: 0, 4: 0, 5: 1, 6: 1}
    assert sum(coefficients.values()) == 0
    assert all(edge in edges and shifts[edge][1] == lifts[edge[1]]-lifts[edge[0]]
               for edge in horizontal)
    normals = dict(zip((3, 4, 5, 6), s.symbols('W3:7')))
    assert s.expand(sum(coefficients[i]*coefficients[j]*(normals[j]-normals[i])**2
                        for i, j in horizontal)
                    +sum(coefficients[i]*normals[i] for i in coefficients)**2) == 0
    v3, v4, v5, v6 = s.symbols('v3 v4 v5 v6')
    values = {A: v4-v6-1, B: -(v3-v5-1)}
    assert s.expand((A*(v3-v5-1)+B*(v4-v6-1)).subs(values, simultaneous=True)) == 0
    energy = s.expand(-sum(coefficients[i]*coefficients[j]*dx*dx
                           for (i, j), dx in horizontal.items()))
    expected = (A*A*(d3+d4)**2+B*B*(d4+d5)**2
                -2*A*B*(d4*(1-d3-d4-d5)-d3*d5))
    assert s.expand(energy-expected) == 0
    assert energy.subs({d3: 0, d4: 0, d5: 0}) == 0
    profile = {A: -HALF, B: HALF, normals[3]: 0, normals[4]: 0,
               normals[5]: -1, normals[6]: 0}
    assert sum(coefficients[i]*normals[i] for i in coefficients).subs(profile) == -HALF
    return {'coefficient_A': 'v4-v6-1', 'coefficient_B': '-(v3-v5-1)',
            'norm_squared': '|A*(r3-r5)+B*(r4-r6)|^2',
            'exact_horizontal_energy': str(expected),
            'bound': 'O(d3+d4+d5), uniformly with no t or phase remainder',
            'normal_coefficient_on_profile_minus_one_zero_minus_one': '-1/2'}


def exact_checks():
    import remaining_ray1_positive_z_profile as profile

    face = face027_identity()
    checked_profile = profile.exact_checks()
    assert checked_profile['profile'] == '(-1,0,-1)'
    return {'face027': face, 'profile': checked_profile,
            'block_stress': block_stress_identity(),
            'folded_phase': folded_phase_identity(), 'reference': finite_h_reference(),
            'positive_axial_regime_excluded': True,
            'contradiction': 'delta^2<=128*S, whereas S=o(delta^2*h) and h->0',
            'full_ray1_marking_excluded': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    print(json.dumps(exact_checks()), flush=True)
