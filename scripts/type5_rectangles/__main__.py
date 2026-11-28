"""Check the rectangular, oblique and rhombic Type 5 certificates."""

import argparse
from fractions import Fraction
import sys

from .chart import Complex, KNOTS, TAIL_PARAMETERS, core, finite_parameters
from .interval import Interval
from .taylor import Taylor


COMPACT_SHEAR = Fraction(1, 2**120)
OBLIQUE = {
    (Fraction(12, 25), Fraction(22, 25), 80): (
        ("0.019891161904990746", "-0.5817588155845147"),
        ("0.49999999999999734", "0.2817420190055172"),
        ("-0.12104360695345573", "0.10048855819277763"),
        ("-0.4800959964698668", "-0.29986883077356985"),
    ),
    (Fraction(7, 16), Fraction(1), 52): (
        ("0.06011228735338294", "-0.6220022506114622"),
        ("0.4999999999184797", "0.24561879534331862"),
        ("-0.13640522488670823", "0.23470153525286963"),
        ("-0.4392572491769257", "-0.37130785831765245"),
    ),
}


def finite_bin(complex_, index):
    lo = max(k for k in KNOTS if k <= index)
    hi = min(k for k in KNOTS if k > index)
    order = 16 if index < 7 else 10 if index < 17 else 6
    stack = [(Fraction(index, 64), Fraction(index+1, 64), 0)]
    certified = 0
    while stack:
        left, right, depth = stack.pop()
        t = Taylor.variable(left, right, order)
        x = t.constant(Interval.between(-COMPACT_SHEAR, COMPACT_SHEAR))
        params = finite_parameters(t, lo, hi, t.constant)
        try:
            placement = complex_.reconstruct(core(t, x, params), x, 1/t, Taylor.sqrt)
            if complex_.certifies_embedding(*placement, Taylor.sign):
                certified += 1
                continue
        except ValueError:
            pass  # An interval containing zero needs subdivision.
        if depth == 18:
            raise ArithmeticError(f"could not certify t in [{left}, {right}]")
        mid = (left+right)/2
        stack.extend([(mid, right, depth+1), (left, mid, depth+1)])
    return certified


def cusp_cell(complex_, index):
    from .laurent import Laurent, System
    from .shear import ShearArithmetic

    interval = Interval.between(Fraction(index, 16384), Fraction(index+1, 16384))
    field = ShearArithmetic(interval)
    system = System(field, Fraction(1, 32))
    t, x = system.t, system.lift(field.variable())
    params = list(map(system.constant, TAIL_PARAMETERS))
    placement = complex_.reconstruct(core(t, x, params), x, 1/t, Laurent.sqrt)
    if not complex_.certifies_embedding(*placement, Laurent.sign):
        raise ArithmeticError(f"cusp sign check failed on shear cell {index}")


def oblique(complex_):
    scalar = Taylor.variable(Fraction(0), Fraction(0), 2).constant
    for (x, y, exponent), rows in OBLIQUE.items():
        p = {1: (0, 0)}
        for i, row in enumerate(rows, 2):
            p[i] = tuple(scalar(Fraction(s)) for s in row)
        radius = Fraction(1, 2**exponent)
        X = scalar(Interval.between(x-radius, x+radius))
        Y = scalar(Interval.between(y-radius, y+radius))
        placement = complex_.reconstruct(p, X, Y, Taylor.sqrt)
        if not complex_.certifies_embedding(*placement, Taylor.sign):
            raise ArithmeticError(f"oblique witness failed at ({x}, {y})")
        print(f"Certified the box of radius 2^-{exponent} about ({x}, {y}).", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("part", choices=("all", "finite", "cusp", "oblique", "rhombic", "reduced", "separation", "sharp", "generic", "core-bounds", "opening", "height-cones", "sharp-embeddings", "hex-angles", "hex-hinge"),
                        default="all", nargs="?")
    args = parser.parse_args()
    if not __debug__:
        sys.exit("Run without Python optimization so incidence assertions are checked.")
    complex_ = Complex()
    if args.part in ("all", "oblique"):
        oblique(complex_)
    if args.part in ("all", "separation"):
        from .projections import verify
        verify(complex_)
    if args.part in ("all", "sharp"):
        from .sharp import verify
        verify(complex_)
    if args.part in ("all", "hex-angles"):
        from .hex_angles import verify
        verify(complex_)
    if args.part in ("all", "hex-hinge"):
        from .hex_hinge import verify
        verify(complex_)
    if args.part in ("all", "sharp-embeddings"):
        from .sharp_embeddings import verify
        verify(complex_)
    if args.part in ("all", "opening"):
        from .sharp_opening import verify
        verify(complex_)
    if args.part in ("all", "height-cones"):
        from .height_cones import verify
        verify(complex_)
    if args.part in ("all", "core-bounds"):
        from .sharp_core_bounds import verify
        verify(complex_)
    if args.part in ("all", "generic"):
        from .general_position import verify
        verify(complex_)
    if args.part in ("all", "reduced"):
        from .reduced import verify
        verify(complex_)
    if args.part in ("all", "rhombic"):
        from .rhombic import verify
        verify(complex_)
    if args.part in ("all", "finite"):
        count = 0
        for i in range(2, 64):
            count += finite_bin(complex_, i)
            print(f"Certified {i}/64 <= t <= {i+1}/64", flush=True)
        print(f"Compact band certified in {count} intervals.", flush=True)
    if args.part in ("all", "cusp"):
        for i in range(-4, 4):
            cusp_cell(complex_, i)
            print(f"Certified {i}/16384 <= x <= {i+1}/16384 in the cusp.", flush=True)


if __name__ == "__main__":
    main()
