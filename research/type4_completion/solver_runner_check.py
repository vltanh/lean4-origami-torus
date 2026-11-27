#!/usr/bin/env python3
"""Scratch-only integration checks for the isolated Z3 solver runner."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

RUNNER=Path(__file__).with_name('solver_runner.py')
SAT='''(set-logic QF_NRA)
(declare-const x Real)
(assert (> x 0))
(assert (= (* x x) 2))
(check-sat)
'''
UNSAT='''(set-logic QF_NRA)
(declare-const x Real)
(assert (> x 0))
(assert (< x 0))
(check-sat)
'''
BAD='(set-logic QF_NRA)\n(assert (= undeclared_name 0))\n(check-sat)\n'


def digest(payload):return hashlib.sha256(payload).hexdigest()
def read(path):return json.loads(path.read_text())
def write(path,value):path.write_text(json.dumps(value,indent=2)+'\n')


def snapshot(directory,cases):
    directory.mkdir()
    (directory/'inputs').mkdir()
    runner=RUNNER.read_bytes()
    (directory/'runner.py').write_bytes(runner)
    manifest={'schema':1,'runner_sha256':digest(runner),'cases':[]}
    for name,formula in cases.items():
        payload=formula.encode()
        relative=f'inputs/{name}.smt2'
        (directory/relative).write_bytes(payload)
        manifest['cases'].append({'name':name,'input':relative,'input_sha256':digest(payload)})
    write(directory/'manifest.json',manifest)
    return directory


def command(directory,*extra):
    return [sys.executable,str(directory/'runner.py'),'run',str(directory),
            '--jobs','2','--poll-seconds','0.05','--memory-mb','256',*map(str,extra)]


def cleanup(process):
    try:os.killpg(process.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    try:process.wait(timeout=4)
    except subprocess.TimeoutExpired:
        try:os.killpg(process.pid,signal.SIGKILL)
        except ProcessLookupError:pass
        process.wait(timeout=4)


def run(directory,*extra,deadline=20):
    process=subprocess.Popen(command(directory,*extra),stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT,text=True,start_new_session=True)
    try:
        stdout,_=process.communicate(timeout=deadline)
        return process.returncode,stdout
    finally:
        if process.poll() is None:cleanup(process)


def result(directory,name):
    attempts=sorted((directory/name).glob('attempt-*'))
    assert attempts,name
    return read(attempts[-1]/'result.json'),attempts


def pigeonhole(holes=20):
    lines=['(set-logic QF_NRA)']
    for pigeon in range(holes+1):
        for hole in range(holes):lines.append(f'(declare-const p{pigeon}_{hole} Bool)')
        lines.append('(assert (or '+' '.join(f'p{pigeon}_{h}' for h in range(holes))+'))')
    for hole in range(holes):
        for first in range(holes+1):
            for second in range(first+1,holes+1):
                lines.append(f'(assert (or (not p{first}_{hole}) (not p{second}_{hole})))')
    return '\n'.join(lines)+'\n(check-sat)\n'


def smoke(root):
    directory=snapshot(root/'smoke',{'algebraic':SAT,'impossible':UNSAT,'malformed':BAD})
    code,stdout=run(directory,'--timeout-ms',0)
    assert code==1,(code,stdout)
    sat,sat_attempts=result(directory,'algebraic')
    unsat,_=result(directory,'impossible')
    bad,_=result(directory,'malformed')
    assert sat['state']=='finished' and sat['solver_status']=='SAT',sat
    assert unsat['state']=='finished' and unsat['solver_status']=='UNSAT',unsat
    assert bad['state']=='error' and bad['solver_status'] is None,bad
    model=(sat_attempts[-1]/'model.smt2').read_text()
    assert 'root-obj' in model and '?' not in model,model
    assert digest(model.encode())==sat['model_sha256']
    assert sat['timeout_ms']==0 and sat['rlimit']==0 and sat['memory_limit_mib']==256
    for name in ('algebraic','impossible','malformed'):
        record,_=result(directory,name)
        case=next(c for c in read(directory/'manifest.json')['cases'] if c['name']==name)
        assert record['input_sha256']==case['input_sha256']
    print('PASS exact algebraic SAT export, UNSAT, parser ERROR, and zero timeout/resource budget',flush=True)

    mismatch=snapshot(root/'input-mismatch',{'algebraic':SAT})
    path=mismatch/'inputs/algebraic.smt2';path.write_text(path.read_text()+'\n')
    code,stdout=run(mismatch)
    assert code!=0 and 'SHA-256 mismatch' in stdout,stdout
    assert not list(mismatch.glob('*/attempt-*'))
    print('PASS mutated input rejected before any worker starts',flush=True)

    cached=snapshot(root/'cached-provenance',{'algebraic':SAT})
    assert run(cached)[0]==0
    record,attempts=result(cached,'algebraic')
    record['input_sha256']='0'*64
    write(attempts[-1]/'result.json',record)
    code,stdout=run(cached)
    updated,new_attempts=result(cached,'algebraic')
    assert code!=0 or (len(new_attempts)>len(attempts) and updated['input_sha256']!=record['input_sha256']),stdout
    print('PASS cached terminal decision cannot survive changed input provenance',flush=True)


def diagnostics(root):
    timeout=snapshot(root/'timeout',{'hard':pigeonhole()})
    code,stdout=run(timeout,'--timeout-ms',1)
    record,_=result(timeout,'hard')
    assert code==1 and record['state']=='finished' and record['solver_status']=='UNKNOWN',(record,stdout)
    assert record.get('reason_unknown'),record
    assert record['timeout_ms']==1
    print('PASS bounded timeout remains UNKNOWN with a reason:',record['reason_unknown'],flush=True)

    memory=snapshot(root/'memory',{'algebraic':SAT})
    code,stdout=run(memory,'--timeout-ms',0,'--memory-mb',32)
    record,_=result(memory,'algebraic')
    assert code!=0 and record.get('solver_status') not in ('SAT','UNSAT'),(record,stdout)
    assert record['timeout_ms']==0 and record['memory_limit_mib']==32,record
    assert record['state'] in ('error','process_error') or record.get('solver_status')=='UNKNOWN',record
    print('PASS address-space bound remains active with no solver time limit',flush=True)


def wait_running(directory,n=2,deadline=8):
    end=time.monotonic()+deadline
    while time.monotonic()<end:
        status=directory/'status.json'
        if status.exists():
            value=read(status)
            running={name:case for name,case in value['cases'].items() if case['state']=='running'}
            if len(running)>=n:return value,running
        time.sleep(.05)
    raise AssertionError('workers did not enter their running states')


def interruption(root):
    directory=snapshot(root/'interruption',{'hard_a':pigeonhole(),'hard_b':pigeonhole(),'tail':SAT})
    log=(directory/'supervisor-test.log').open('w')
    process=subprocess.Popen(command(directory,'--timeout-ms',0),stdout=log,stderr=subprocess.STDOUT,
                             start_new_session=True)
    try:
        _,running=wait_running(directory)
        assert len(running)==2
        killed=next(iter(running));os.kill(running[killed]['pid'],signal.SIGKILL)
        deadline=time.monotonic()+5
        while time.monotonic()<deadline:
            current=read(directory/'status.json')
            if current['cases'][killed]['state']=='process_error':break
            time.sleep(.05)
        else:raise AssertionError('crashed worker did not become process_error')
        assert current['cases'][killed].get('solver_status') is None
        process.send_signal(signal.SIGTERM);process.wait(timeout=6)
    finally:
        cleanup(process);log.close()
    for name in ('hard_a','hard_b'):
        record,_=result(directory,name)
        assert record['state'] in ('interrupted','process_error') and record.get('solver_status') is None,record
    code,stdout=run(directory,'--timeout-ms',1,'--retry-incomplete')
    assert code==1,(code,stdout)
    for name in ('hard_a','hard_b'):
        record,attempts=result(directory,name)
        assert len(attempts)==2 and record['solver_status']=='UNKNOWN',record
    for line in (directory/'resources.jsonl').read_text().splitlines():
        snapshot_state=json.loads(line)
        assert sum(c['state'] in ('starting','running') for c in snapshot_state['cases'].values())<=2
    print('PASS two-worker queue, crashed/interrupted distinctions, and explicit unresolved resume',flush=True)


def live_resume(root):
    directory=snapshot(root/'live-resume',{'hard_a':pigeonhole(),'hard_b':pigeonhole()})
    log=(directory/'orphan-test.log').open('w')
    process=subprocess.Popen(command(directory,'--timeout-ms',0),stdout=log,stderr=subprocess.STDOUT,
                             start_new_session=True)
    resumed=None
    try:
        wait_running(directory)
        process.kill();process.wait(timeout=3)
        resumed=subprocess.Popen(command(directory,'--timeout-ms',1),stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT,text=True,start_new_session=True)
        try:
            stdout,_=resumed.communicate(timeout=2)
            assert resumed.returncode!=0,stdout
        except subprocess.TimeoutExpired:
            pass  # adopting existing workers is also safe; duplicating is not
        assert all(len(list((directory/name).glob('attempt-*')))==1 for name in ('hard_a','hard_b'))
    finally:
        if resumed is not None:cleanup(resumed)
        cleanup(process);log.close()
    print('PASS live workers cannot be duplicated by supervisor resume',flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path)
    parser.add_argument('--smoke',action='store_true')
    args=parser.parse_args()
    root=args.directory or Path(tempfile.mkdtemp(prefix='type4-runner-check-'))
    root.mkdir(parents=True,exist_ok=True)
    print('Scratch evidence:',root,flush=True)
    smoke(root)
    if not args.smoke:
        diagnostics(root)
        interruption(root)
        live_resume(root)
    print('PASS solver runner integration checks',flush=True)


if __name__=='__main__':main()
