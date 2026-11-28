#!/usr/bin/env python3
"""Produce and independently replay RUP certificates for generated CNFs.

Usage:
  python solver_cnf_certificates.py OUTPUT --checker CHECKER INPUT...
  python solver_cnf_certificates.py OUTPUT --checker CHECKER --replay-only

INPUT may be a CNF file or a directory of CNFs. Identical clause multisets
share one proof. Proof-only replay uses the Python standard library and
the independent checker; it never loads Z3 or a numerical library.
"""

import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import time


# A bounded alternative when the default SAT simplifications emit steps
# that the deliberately narrower independent RUP checker cannot accept.
# This profile is not trusted to produce RUP: every resulting step is
# still replayed from the original CNF by the unchanged checker.
RUP_FOCUSED_OPTIONS = {
    'sat.elim_vars': False,
    'sat.elim_vars_bdd': False,
    'sat.scc': False,
    'sat.asymm_branch': False,
    'sat.ate': False,
    'sat.probing': False,
    'sat.probing_binary': False,
    'sat.subsumption': False,
    'sat.simplify.delay': 2147483647,
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def normalize(data):
    """Validate DIMACS, preserving every clause and literal multiplicity."""
    header, clauses, pending = None, [], []
    for line in data.decode('ascii').splitlines():
        words = line.split()
        if not words or words[0] == 'c':
            continue
        if words[0] == 'p':
            if header is not None or clauses or pending or len(words) != 4 or words[1] != 'cnf':
                raise ValueError('invalid or repeated DIMACS header')
            header = int(words[2]), int(words[3])
            if header[0] <= 0 or header[1] < 0:
                raise ValueError('invalid DIMACS dimensions')
            continue
        if header is None:
            raise ValueError('clause before DIMACS header')
        for word in words:
            literal = int(word)
            if literal == 0:
                clauses.append(tuple(pending))
                pending = []
            else:
                if abs(literal) > header[0]:
                    raise ValueError('literal exceeds declared variable count')
                pending.append(literal)
    if header is None or pending or len(clauses) != header[1]:
        raise ValueError('incomplete clause or incorrect DIMACS clause count')
    text = f'p cnf {header[0]} {len(clauses)}\n'+''.join(
        ' '.join(map(str, clause))+' 0\n'
        for clause in sorted(tuple(sorted(clause)) for clause in clauses))
    return header[0], clauses, text.encode('ascii')


def dimacs(n, clauses):
    # Preserve producer order: sorting is used only for the mathematical
    # identity of a packet, since clause order can change SAT heuristics.
    return (f'p cnf {n} {len(clauses)}\n'+''.join(
        ' '.join(map(str, clause))+' 0\n' for clause in clauses)).encode('ascii')


def produce_trace(n, clauses, path, milliseconds, options=None):
    # Keep the same guarded variable mapping as solver_chambers.write_proof.
    # The independent checker validates every logged input, including any
    # simplification added by the producer, against this exact CNF.
    import ctypes
    from ctypes.util import find_library

    z = ctypes.CDLL(find_library('z3'))
    pointer, string = ctypes.c_void_p, ctypes.c_char_p
    for name, result, arguments in (
        ('Z3_mk_config', pointer, ()), ('Z3_mk_context', pointer, (pointer,)),
        ('Z3_del_config', None, (pointer,)), ('Z3_del_context', None, (pointer,)),
        ('Z3_eval_smtlib2_string', string, (pointer, string)),
    ):
        function = getattr(z, name)
        function.restype, function.argtypes = result, arguments
    # SMT-LIB strings double their embedded quotation marks.
    filename = str(path).replace('"', '""')
    lines = [f'(set-option :timeout {milliseconds})',
             f'(set-option :sat.drat.file "{filename}")',
             '(set-option :sat.drat.binary false)']
    lines += [f'(set-option :{name} {str(value).lower()})'
              for name, value in (options or {}).items()]
    lines += [f'(declare-const x{i} Bool)' for i in range(1, n+1)]
    lines += ['(declare-const guard Bool)']
    lines += [f'(assert (or guard x{i}))' for i in range(1, n+1)]
    lines += ['(assert (or '+' '.join(f'x{i}' if i > 0 else f'(not x{-i})'
                                     for i in clause)+'))' for clause in clauses]
    lines += ['(assert guard)', '(check-sat-using sat)']
    configuration = z.Z3_mk_config()
    context = z.Z3_mk_context(configuration)
    z.Z3_del_config(configuration)
    try:
        answer = z.Z3_eval_smtlib2_string(context, '\n'.join(lines).encode()).decode().strip()
    finally:
        z.Z3_del_context(context)
    if answer != 'unsat':
        raise RuntimeError(f'no UNSAT certificate produced: {answer[:200]}')


def check_packet(job):
    directory, identity, checker, seconds, replay, expected = job
    directory = Path(directory)/identity
    cnf, proof = directory/'input.cnf', directory/'proof.drat'
    started = time.monotonic()
    attempts = []
    try:
        data = cnf.read_bytes()
        n, clauses, normalized = normalize(data)
        if digest(normalized) != identity:
            raise ValueError('CNF hash does not match packet identity')
        if dimacs(n, clauses) != data:
            raise ValueError('packet CNF is not normalized DIMACS')
        if replay:
            if digest(data) != expected['input_sha256']:
                raise ValueError('CNF hash does not match verified manifest')
            if digest(proof.read_bytes()) != expected['proof_sha256']:
                raise ValueError('proof hash does not match verified manifest')
        orders = [('replay' if replay else 'source', clauses,
                   'replay' if replay else 'default', {})]
        canonical_order = sorted(tuple(sorted(clause)) for clause in clauses)
        if not replay and canonical_order != clauses:
            orders.append(('canonical', canonical_order, 'default', {}))
        if not replay:
            orders.append(('source', clauses, 'rup_focused', RUP_FOCUSED_OPTIONS))
        for order, candidate, profile, options in orders:
            attempt_started = time.monotonic()
            if not replay:
                proof.unlink(missing_ok=True)
                produce_trace(n, candidate, proof, int(1000*seconds), options)
            produced = time.monotonic()
            result = subprocess.run([checker, str(cnf), str(proof)], capture_output=True,
                                    text=True, timeout=seconds, check=False)
            verified = result.returncode == 0 and result.stdout.startswith('PASS UNSAT: ')
            attempts.append({'order': order, 'producer_profile': profile,
                             'sat_options': dict(options), 'verified': verified,
                             'producer_seconds': 0 if replay else produced-attempt_started,
                             'checker_seconds': time.monotonic()-produced,
                             'checker_result': (result.stdout+' '+result.stderr).strip()})
            if verified:
                break
            # Only a specifically rejected non-RUP step permits another
            # deterministic producer. SAT/UNKNOWN, parser/hash errors,
            # invalid inputs, checker crashes and timeouts never do.
            # The final alternative disables optional SAT simplifications;
            # all attempts prove the identical CNF from the beginning.
            if result.returncode != 1 or not result.stderr.startswith('non-RUP proof step '):
                break
        if not attempts[-1]['verified']:
            raise RuntimeError('independent replay failed: '+attempts[-1]['checker_result'])
        return {'id': identity, 'verified': True, 'variables': n, 'clauses': len(clauses),
                'input_sha256': digest(data),
                'proof_sha256': digest(proof.read_bytes()), 'proof_bytes': proof.stat().st_size,
                'producer_seconds': sum(row['producer_seconds'] for row in attempts),
                'checker_seconds': sum(row['checker_seconds'] for row in attempts),
                'attempts': attempts, 'checker_result': result.stdout.strip()}
    except Exception as error:
        return {'id': identity, 'verified': False, 'error': str(error),
                'elapsed_seconds': time.monotonic()-started, 'attempts': attempts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('inputs', nargs='*', type=Path)
    parser.add_argument('--checker', required=True, type=Path)
    parser.add_argument('--seconds', type=float, default=30)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--replay-only', action='store_true')
    args = parser.parse_args()
    if not 0 < args.seconds <= 60 or not 1 <= args.jobs <= 8:
        parser.error('seconds must be in (0,60], jobs in [1,8]')
    checker = args.checker.resolve()
    if not checker.is_file():
        parser.error('the independent checker executable does not exist')
    output = args.output.resolve()
    manifest = output/'manifest.json'
    if args.replay_only:
        if args.inputs:
            parser.error('replay-only reads the existing packet manifest; omit INPUT')
        original = json.loads(manifest.read_text())
        if original.get('format') != 1 or not original.get('verified'):
            parser.error('the manifest is not a completely verified certificate set')
        sources = original['sources']
        expected = {row['id']: row for row in original['certificates']}
        if set(expected) != {row['certificate'] for row in sources}:
            parser.error('manifest source and certificate sets differ')
    else:
        if not args.inputs:
            parser.error('provide at least one CNF file or directory')
        paths = sorted({path.resolve() for item in args.inputs
                        for path in (item.rglob('*.cnf') if item.is_dir() else [item])})
        if not paths:
            parser.error('no CNF inputs were found')
        sources, expected = [], {}
        for path in paths:
            data = path.read_bytes()
            n, clauses, canonical = normalize(data)
            identity = digest(canonical)
            directory = output/identity
            directory.mkdir(parents=True, exist_ok=True)
            if identity not in expected:
                (directory/'input.cnf').write_bytes(dimacs(n, clauses))
            expected[identity] = None
            sources.append({'path': str(path), 'sha256': digest(data), 'certificate': identity})
    jobs = [(str(output), key, str(checker), args.seconds, args.replay_only, value)
            for key, value in sorted(expected.items())]
    started = time.monotonic()
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        records = list(pool.map(check_packet, jobs))
    success = bool(records) and all(row['verified'] for row in records)
    report = {'format': 1, 'verified': success, 'checker_sha256': digest(checker.read_bytes()),
              'elapsed_seconds': time.monotonic()-started, 'sources': sources, 'certificates': records}
    destination = output/('replay.json' if args.replay_only else 'manifest.json')
    destination.write_text(json.dumps(report, indent=2)+'\n')
    if not success:
        for row in records:
            if not row['verified']:
                print('FAIL', row['id'], row['error'], flush=True)
        raise SystemExit(1)
    print(f'PASS {len(sources)} CNFs, {len(records)} distinct independently checked proofs; '
          f'{report["elapsed_seconds"]:.3f} seconds; {destination}')


if __name__ == '__main__':
    main()
