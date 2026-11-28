#!/usr/bin/env python3
"""Export a necessary Boolean filter from independently replayed metric proofs.

This does not assert that a geometric limit has nonzero brackets.  It
blocks the generic sign completions of actual configurations excluded by
the finite weak-chamber certificates.  All 16 phase symmetries and both
global spatial orientations are retained.
"""

import argparse
from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path

import solver_chambers as compiler
import solver_verify

CERTIFICATE_KEYS = (
    'final_polynomial', 'metric_certificate', 'metric_difference_certificate',
    'metric_product_certificate', 'metric_quadratic_certificate',
    'metric_quotient_certificate',
)


def required_height(key, proof):
    if key == 'final_polynomial':
        return 8
    text = proof['valid_for']
    assert text.startswith('y>=') and text[3:].isdigit()
    return max(8, int(text[3:]))


def build(directory, height=10**6):
    """Return checked additional clauses and their exact certificate binding.

    Existing geometry CNFs use primary variables 1..70 in the same sorted
    four-subset order as the chamber compiler.  They may fix either global
    orientation or neither.  The returned clauses introduce no variables.
    Callers must separately justify their geometric limiting formula.
    """
    directory = Path(directory)
    assert isinstance(height, int) and not isinstance(height, bool) and height >= 8
    # Replay the complete manifest, including every proof, strictness trace,
    # exact symmetry, and the binding to the independent coverage CNF.  The
    # RUP proof remains necessary to claim enumeration completeness; blocking
    # these individually certified cases does not require completeness.
    log = StringIO()
    with redirect_stdout(log):
        solver_verify.main(directory)
    source = json.loads((directory / 'chambers.json').read_text())
    phase = tuple(tuple(row['permutation']) for row in source['symmetries']
                  if row['phase_preserving'])
    assert len(set(phase)) == 16
    excluded = {}
    selected = []
    for row in source['chambers']:
        proofs = [key for key in CERTIFICATE_KEYS
                  if key in row and required_height(key, row[key]) <= height]
        if not proofs:
            continue
        minimum = min(required_height(key, row[key]) for key in proofs)
        proof = next(key for key in proofs if required_height(key, row[key]) == minimum)
        model = tuple(1 if value == '+' else -1 for value in row['signs'])
        selected.append({'chamber': row['id'], 'proof': proof, 'height': minimum})
        for permutation in phase:
            image = compiler.transformed_model(model, permutation)
            for orientation in (-1, 1):
                oriented = tuple(orientation * value for value in image)
                excluded.setdefault(oriented, {
                    'chamber': row['id'], 'proof': proof,
                    'permutation': permutation, 'orientation': orientation,
                })
    models = tuple(sorted(excluded))
    clauses = [[-(i + 1) * value for i, value in enumerate(model)] for model in models]
    normalized = {model for model in models if model[0] == 1}
    all_models = {tuple(1 if value == '+' else -1 for value in text)
                  for text in source['all_models']}
    assert normalized <= all_models
    assert len(models) == 2 * len(normalized)
    assert all(tuple(-value for value in model) in excluded for model in models)
    ledger = {
        'height': height, 'valid_for': f'y>={max(row["height"] for row in selected)}',
        'excluded_chambers': selected,
        'excluded_normalized_models': len(normalized),
        'remaining_normalized_models': len(all_models - normalized),
        'variables': 70,
        'blocks': [{'signs': ''.join('+' if v > 0 else '-' for v in model),
                    **excluded[model]} for model in models],
    }
    return clauses, ledger


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--height', type=int, default=10**6)
    args = parser.parse_args()
    clauses, ledger = build(args.manifest, args.height)
    args.output.mkdir(parents=True, exist_ok=True)
    compiler.write_cnf(args.output / 'metric_filter.cnf', 70, clauses)
    (args.output / 'metric_filter.json').write_text(json.dumps(ledger, indent=2) + '\n')
    print(f'PASS {len(ledger["excluded_chambers"])} exact chamber proofs; '
          f'{ledger["excluded_normalized_models"]} normalized models excluded, '
          f'{ledger["remaining_normalized_models"]} remain; '
          f'{len(clauses)} blocks with both orientations; {ledger["valid_for"]}')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
