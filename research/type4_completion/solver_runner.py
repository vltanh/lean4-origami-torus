#!/usr/bin/env python3
"""Prepare and run the eight complete Type 4 domains without a solver timeout.

Only preparation needs SymPy. Solving uses the system Z3 shared library through
its C API. Each worker is isolated, memory bounded, and fully logged. See
solver_runner.md for the distinction between a solver decision and a proof.
"""
import argparse
import ctypes as ct
import ctypes.util
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import time
import traceback


ORDER = ['ray2_2', 'ray2_1'] + [f'ray1_{i}' for i in range(1, 7)]


def utc():
    return datetime.now(timezone.utc).isoformat()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def write_json(path, value):
    temporary = path.with_name(path.name + f'.tmp-{os.getpid()}')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def prepare(args):
    import direct_metric
    destination = args.directory.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    if any(destination.iterdir()):
        raise ValueError('prepare requires an empty directory; run resumes existing inputs')
    (destination / 'inputs').mkdir()
    generator = Path(direct_metric.__file__).resolve()
    repository = generator.parents[2]
    revision = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=repository, text=True).strip()
    sources = [generator, repository / 'research/type4_focus/type4_fixed_cubic.py',
               repository / 'research/type4_focus/type4_gap_enum.py']
    manifest = {
        'schema': 1, 'prepared_at': utc(), 'generator_revision': revision,
        'generator_sources': {str(p.relative_to(repository)): digest(p.read_bytes())
                              for p in sources},
        'formulation': 'full quartic domains, strict support and mixed faces',
        'cases': [],
    }
    available = {name: (K, cell) for name, K, cell in direct_metric.cases()}
    for name in ORDER:
        formula, metadata = direct_metric.build(*available[name], full=True,
                                               support_cuts=True, mixed_faces=True)
        payload = (formula + '(check-sat)\n').encode()
        relative = f'inputs/{name}.smt2'
        (destination / relative).write_bytes(payload)
        manifest['cases'].append(dict(metadata, name=name, input=relative,
                                      input_bytes=len(payload), input_sha256=digest(payload)))
        print(name, metadata['assertions'], digest(payload), flush=True)
    runner = Path(__file__).read_bytes()
    (destination / 'runner.py').write_bytes(runner)
    manifest['runner_sha256'] = digest(runner)
    write_json(destination / 'manifest.json', manifest)
    print('Prepared', destination, flush=True)


def load_manifest(directory):
    manifest = read_json(directory / 'manifest.json')
    if manifest.get('schema') != 1 or not manifest.get('cases'):
        raise ValueError('invalid or empty manifest')
    names = set()
    for case in manifest['cases']:
        name = case['name']
        if not re.fullmatch(r'[a-zA-Z0-9_-]+', name) or name in names:
            raise ValueError(f'invalid or duplicate case name: {name}')
        names.add(name)
        path = (directory / case['input']).resolve()
        if not path.is_relative_to(directory) or digest(path.read_bytes()) != case['input_sha256']:
            raise ValueError(f'input path or SHA-256 mismatch: {name}')
    snapshot = directory / 'runner.py'
    if digest(snapshot.read_bytes()) != manifest['runner_sha256']:
        raise ValueError('runner snapshot SHA-256 mismatch')
    return manifest


class Z3:
    """Small, explicitly typed C API binding; no concurrent access to a context."""

    def __init__(self):
        self.library_path = ctypes.util.find_library('z3')
        if not self.library_path:
            raise RuntimeError('Z3 shared library not found; install libz3')
        self.lib = ct.CDLL(self.library_path)
        p, s, u = ct.c_void_p, ct.c_char_p, ct.c_uint
        signatures = [
            ('get_full_version', s, []), ('mk_config', p, []),
            ('set_param_value', None, [p, s, s]), ('del_config', None, [p]),
            ('mk_context', p, [p]), ('del_context', None, [p]),
            ('set_error_handler', None, [p, p]), ('get_error_code', ct.c_int, [p]),
            ('get_error_msg', s, [p, ct.c_int]), ('set_ast_print_mode', None, [p, ct.c_int]),
            ('mk_string_symbol', p, [p, s]), ('mk_solver_for_logic', p, [p, p]),
            ('solver_inc_ref', None, [p, p]), ('solver_dec_ref', None, [p, p]),
            ('solver_from_string', None, [p, p, s]), ('solver_check', ct.c_int, [p, p]),
            ('solver_get_reason_unknown', s, [p, p]), ('solver_get_model', p, [p, p]),
            ('model_inc_ref', None, [p, p]), ('model_dec_ref', None, [p, p]),
            ('model_to_string', s, [p, p]), ('solver_get_statistics', p, [p, p]),
            ('stats_inc_ref', None, [p, p]), ('stats_dec_ref', None, [p, p]),
            ('stats_size', u, [p, p]), ('stats_get_key', s, [p, p, u]),
            ('stats_is_uint', ct.c_bool, [p, p, u]),
            ('stats_get_uint_value', u, [p, p, u]),
            ('stats_get_double_value', ct.c_double, [p, p, u]),
        ]
        for name, result, arguments in signatures:
            function = getattr(self.lib, 'Z3_' + name)
            function.restype, function.argtypes = result, arguments
            setattr(self, name, function)

    def check_error(self, context):
        code = self.get_error_code(context)
        if code:
            raise RuntimeError(self.get_error_msg(context, code).decode())


def worker(args):
    directory = args.directory.resolve()
    attempt = directory / args.attempt
    started, monotonic_start = utc(), time.monotonic()
    record = {'case': args.case, 'pid': os.getpid(), 'started_at': started,
              'state': 'starting', 'solver_status': None,
              'timeout_ms': args.timeout_ms, 'rlimit': 0,
              'memory_limit_mib': args.memory_mb, 'engine': 'QF_NRA portfolio',
              'proof_generation': False, 'validation': 'not independently certified'}
    context = solver = None
    z3 = None
    try:
        if args.memory_mb:
            bound = args.memory_mb * 1024 * 1024
            resource.setrlimit(resource.RLIMIT_AS, (bound, bound))
        manifest = load_manifest(directory)
        case = next(c for c in manifest['cases'] if c['name'] == args.case)
        payload = (directory / case['input']).read_bytes()
        if digest(payload) != case['input_sha256']:
            raise ValueError(f'input changed while starting worker: {args.case}')
        record.update(input_sha256=case['input_sha256'], input_bytes=len(payload),
                      runner_sha256=manifest['runner_sha256'])
        z3 = Z3()
        record.update(solver_version=z3.get_full_version().decode(),
                      solver_library=z3.library_path)
        configuration = z3.mk_config()
        for key, value in [('timeout', str(args.timeout_ms)), ('rlimit', '0'),
                           ('model', 'true'), ('proof', 'false')]:
            z3.set_param_value(configuration, key.encode(), value.encode())
        context = z3.mk_context(configuration)
        z3.del_config(configuration)
        if not context:
            raise RuntimeError('Z3 context creation failed')
        # NULL disables the default process-exiting error handler. Check errors
        # after each fallible API operation before interpreting its result.
        z3.set_error_handler(context, None)
        z3.set_ast_print_mode(context, 2)  # Z3_PRINT_SMTLIB2_COMPLIANT
        solver = z3.mk_solver_for_logic(context, z3.mk_string_symbol(context, b'QF_NRA'))
        z3.check_error(context)
        z3.solver_inc_ref(context, solver)
        # The input snapshot keeps check-sat for standalone Z3 reproduction.
        # The API makes that call itself, after recording the running state.
        formula = payload.rstrip()
        if formula.endswith(b'(check-sat)'):
            formula = formula[:-len(b'(check-sat)')]
        z3.solver_from_string(context, solver, formula)
        z3.check_error(context)
        record.update(state='running', check_started_at=utc())
        write_json(attempt / 'result.json', record)
        print(json.dumps(record), flush=True)
        decision = z3.solver_check(context, solver)
        z3.check_error(context)
        record.update(state='finished', solver_status={1: 'SAT', -1: 'UNSAT', 0: 'UNKNOWN'}[decision],
                      check_finished_at=utc(), elapsed_seconds=time.monotonic() - monotonic_start)
        if decision == 0:
            record['reason_unknown'] = z3.solver_get_reason_unknown(context, solver).decode()
        # Preserve the decision even if optional model/statistics export fails.
        write_json(attempt / 'result.json', record)
        if decision == 1:
            model = z3.solver_get_model(context, solver)
            z3.check_error(context)
            if not model:
                raise RuntimeError('Z3 returned SAT without a model')
            z3.model_inc_ref(context, model)
            try:
                model_text = z3.model_to_string(context, model).decode()
                z3.check_error(context)
            finally:
                z3.model_dec_ref(context, model)
            (attempt / 'model.smt2').write_text(model_text + '\n')
            record['model_sha256'] = digest((model_text + '\n').encode())
        statistics = z3.solver_get_statistics(context, solver)
        z3.check_error(context)
        if not statistics:
            raise RuntimeError('Z3 returned no statistics')
        z3.stats_inc_ref(context, statistics)
        try:
            values = {}
            for index in range(z3.stats_size(context, statistics)):
                key = z3.stats_get_key(context, statistics, index).decode()
                values[key] = (z3.stats_get_uint_value(context, statistics, index)
                               if z3.stats_is_uint(context, statistics, index)
                               else z3.stats_get_double_value(context, statistics, index))
            z3.check_error(context)
        finally:
            z3.stats_dec_ref(context, statistics)
        write_json(attempt / 'statistics.json', values)
    except BaseException as error:
        record['state'] = 'export_error' if record['solver_status'] else 'error'
        record['error'] = f'{type(error).__name__}: {error}'
        traceback.print_exc()
    finally:
        usage = resource.getrusage(resource.RUSAGE_SELF)
        record.update(finished_at=utc(), elapsed_seconds=time.monotonic() - monotonic_start,
                      cpu_seconds=usage.ru_utime + usage.ru_stime, peak_rss_kib=usage.ru_maxrss)
        write_json(attempt / 'result.json', record)
        print(json.dumps(record), flush=True)
        if z3 and context:
            if solver:
                z3.solver_dec_ref(context, solver)
            z3.del_context(context)
    return 0 if record['state'] == 'finished' else 1


def process_usage(pid):
    try:
        status = Path(f'/proc/{pid}/status').read_text()
        values = {key: int(value) for key, value in
                  re.findall(r'^(VmRSS|VmSize):\s+(\d+) kB$', status, re.M)}
        fields = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
        ticks = os.sysconf('SC_CLK_TCK')
        return {'rss_kib': values.get('VmRSS', 0), 'virtual_kib': values.get('VmSize', 0),
                'cpu_seconds': (int(fields[11]) + int(fields[12])) / ticks}
    except (FileNotFoundError, ProcessLookupError):
        return {}


def matching_worker(pid, directory, attempt):
    if not isinstance(pid, int):
        return False
    try:
        arguments = Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
        return all(str(value).encode() in arguments for value in
                   (directory / 'runner.py', '_worker', directory, attempt))
    except (FileNotFoundError, ProcessLookupError):
        return False


def run(args):
    directory = args.directory.resolve()
    manifest = load_manifest(directory)
    lock = (directory / '.run.lock').open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise RuntimeError('another supervisor already owns this run directory')
    stop = {'signal': None}
    for signum in (signal.SIGINT, signal.SIGTERM):
        signal.signal(signum, lambda number, frame: stop.update(signal=number))
    queue, cases, active = [], {}, {}
    for case in manifest['cases']:
        name = case['name']
        case_directory = directory / name
        case_directory.mkdir(exist_ok=True)
        attempts = sorted(case_directory.glob('attempt-*'))
        last = attempts[-1] / 'result.json' if attempts else None
        previous = read_json(last) if last and last.exists() else {}
        if attempts:
            startup_file = attempts[-1] / 'started.json'
            startup = read_json(startup_file) if startup_file.exists() else {}
            pid = previous.get('pid', startup.get('pid'))
            if matching_worker(pid, directory, attempts[-1].relative_to(directory)):
                raise RuntimeError(f'previous worker for {name} is still alive (PID {pid}); stop it before resuming')
        for key, expected in [('case', name), ('input_sha256', case['input_sha256']),
                              ('runner_sha256', manifest['runner_sha256'])]:
            if (previous.get('solver_status') or key in previous) and previous.get(key) != expected:
                raise ValueError(f'cached result provenance mismatch: {name} ({key})')
        terminal = previous.get('state') in ('finished', 'error', 'export_error', 'interrupted', 'process_error')
        solved = previous.get('solver_status') in ('SAT', 'UNSAT')
        if terminal and (solved or not args.retry_incomplete):
            cases[name] = dict(previous, attempt=str(last.parent.relative_to(directory)))
        else:
            cases[name] = {'case': name, 'state': 'queued', 'solver_status': None,
                           'input_sha256': case['input_sha256']}
            queue.append(case)
    configuration = {'supervisor_pid': os.getpid(), 'started_at': utc(), 'jobs': args.jobs,
                     'timeout_ms': args.timeout_ms, 'rlimit': 0, 'memory_limit_mib': args.memory_mb,
                     'engine': 'QF_NRA portfolio', 'runner_sha256': manifest['runner_sha256']}
    started = time.monotonic()
    last_report = -float('inf')
    samples = (directory / 'resources.jsonl').open('a', buffering=1)

    def report(state):
        snapshot = dict(configuration, updated_at=utc(), state=state,
                        elapsed_seconds=time.monotonic() - started, cases=cases)
        write_json(directory / 'status.json', snapshot)
        samples.write(json.dumps(snapshot, sort_keys=True) + '\n')
        summary = ' '.join(f'{name}:{item.get("solver_status") or item["state"]}'
                           for name, item in cases.items())
        print(snapshot['updated_at'], summary, flush=True)

    try:
        while queue or active:
            if stop['signal'] is not None:
                break
            while queue and len(active) < args.jobs:
                case = queue.pop(0)
                name = case['name']
                case_directory = directory / name
                number = max([int(p.name.split('-')[-1]) for p in case_directory.glob('attempt-*')] or [0]) + 1
                attempt = case_directory / f'attempt-{number:04d}'
                attempt.mkdir()
                relative = str(attempt.relative_to(directory))
                command = [sys.executable, str(directory / 'runner.py'), '_worker', str(directory),
                           '--case', name, '--attempt', relative,
                           '--timeout-ms', str(args.timeout_ms), '--memory-mb', str(args.memory_mb)]
                log = (attempt / 'worker.log').open('w', buffering=1)
                process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
                active[name] = (process, log, attempt, time.monotonic())
                cases[name] = {'case': name, 'state': 'starting', 'solver_status': None,
                               'pid': process.pid, 'attempt': relative, 'command': command,
                               'started_at': utc(), 'input_sha256': case['input_sha256']}
                write_json(attempt / 'started.json', cases[name])
            for name, (process, log, attempt, launch) in list(active.items()):
                result_file = attempt / 'result.json'
                if result_file.exists():
                    cases[name].update(read_json(result_file))
                cases[name].update(elapsed_seconds=time.monotonic() - launch,
                                   resources=process_usage(process.pid))
                code = process.poll()
                if code is not None:
                    # A worker may finish between the earlier read and poll.
                    if result_file.exists():
                        cases[name].update(read_json(result_file))
                    cases[name]['exit_code'] = code
                    if cases[name]['state'] in ('starting', 'running'):
                        cases[name].update(state='process_error', finished_at=utc(),
                                           error=f'worker exited without a decision (exit {code}); see worker.log')
                        write_json(result_file, cases[name])
                    log.close()
                    del active[name]
                    last_report = -float('inf')
            if time.monotonic() - last_report >= args.poll_seconds:
                report('running')
                last_report = time.monotonic()
            if queue or active:
                time.sleep(min(1.0, args.poll_seconds))
    finally:
        # Stop only our own children. A killed/interrupted process is never
        # relabeled as a solver-produced UNKNOWN or UNSAT.
        for process, _, _, _ in active.values():
            if process.poll() is None:
                process.terminate()
        for name, (process, log, attempt, launch) in active.items():
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            result_file = attempt / 'result.json'
            if result_file.exists():
                cases[name].update(read_json(result_file))
            if not cases[name].get('solver_status'):
                cases[name].update(state='interrupted', solver_status=None, finished_at=utc())
            cases[name].update(exit_code=process.returncode, elapsed_seconds=time.monotonic() - launch)
            write_json(result_file, cases[name])
            log.close()
        report('interrupted' if active or stop['signal'] else 'finished')
        samples.close()
        lock.close()
    if stop['signal']:
        return 128 + stop['signal']
    return 0 if all(c.get('solver_status') in ('SAT', 'UNSAT') for c in cases.values()) else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    prepare_parser = commands.add_parser('prepare', help='generate all eight full inputs and a frozen runner')
    prepare_parser.add_argument('directory', type=Path)
    for name in ('run', '_worker'):
        sub = commands.add_parser(name)
        sub.add_argument('directory', type=Path)
        sub.add_argument('--timeout-ms', type=int, default=0,
                         help='total solver limit in ms; 0 means no timeout (default)')
        sub.add_argument('--memory-mb', type=int, default=3072,
                         help='per-worker Linux address-space limit in MiB; 0 disables it')
        if name == 'run':
            sub.add_argument('--jobs', type=int, default=2)
            sub.add_argument('--poll-seconds', type=float, default=15)
            sub.add_argument('--retry-incomplete', action='store_true',
                             help='retry previous UNKNOWN/error/interrupted attempts; preserve their logs')
        else:
            sub.add_argument('--case', required=True)
            sub.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if args.command != 'prepare' and (args.timeout_ms < 0 or args.memory_mb < 0):
        parser.error('timeout and memory limits must be nonnegative')
    if args.command == 'run' and (args.jobs < 1 or args.poll_seconds <= 0):
        parser.error('jobs and poll-seconds must be positive')
    if args.command == 'prepare':
        prepare(args)
        return 0
    return run(args) if args.command == 'run' else worker(args)


if __name__ == '__main__':
    sys.exit(main())
