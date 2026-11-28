"""Trusted receipt validation and release for the manual coverage trial."""
from enum import IntEnum
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import sys
import tempfile

TOOLS = Path(__file__).resolve().parent
V2 = runpy.run_path(str(TOOLS / 'read-col0-v2-replay.py'))
WORKER = runpy.run_path(str(TOOLS / 'read-col0-v3-worker.py'))
ARCHIVE = {
    'read-decision.py': 'read-col0-v3-candidate.py',
    'outside-read.py': 'read-col0-v3-outside.py',
    'read-col0.py': 'read-col0-v3-grammar.py',
}
PRODUCERS = (
    '.github/workflows/read-diagnostic.yml', '.github/workflows/authoritative.yml',
    '.github/scripts/outside-guard.mjs', 'tools/read-decision.py', 'tools/outside-read.py',
    'tools/read-parse.sh', 'tools/read-receipt.sh', 'tools/read-sandbox.sh', 'tools/check-lean.mjs',
    'tools/read-col0-v2-replay.py', 'tools/read-col0-v3.py', 'tools/read-col0-v3-worker.py',
    *(f'tools/{name}' for name in ARCHIVE.values()),
)
WORKFLOW = '.github/workflows/read-diagnostic.yml'
MAX_MEMBERS = 4096
MAX_MANIFEST = 160000


class Status(IntEnum):
    PIN_MISMATCH = 1
    NO_SECRET = 2
    MANIFEST_MISMATCH = 3
    MEMBER_REFUSED = 4
    RAN_SUPPRESSED = 5
    RELEASED = 6


HEX40 = re.compile('[0-9a-f]{40}')
HEX64 = re.compile('[0-9a-f]{64}')


def require(condition):
    if not condition:
        raise ValueError


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def wire(status, cleared=-1, total=-1):
    require(type(status) is Status)
    if status is Status.RELEASED:
        require(type(cleared) is int and type(total) is int and 5 <= cleared <= total - 5
                and 50 <= total <= MAX_MEMBERS)
    else:
        require(cleared == total == -1)
    return f'[3,{int(status)},{cleared},{total}]\n'.encode('ascii')


def support(cell, files, contributors):
    return len(cell) >= files and len({owner for _, owner in cell}) >= contributors


def release(cells, joint_safe=True):
    forced, held, cleared = cells
    cohort = forced + held + cleared
    if (joint_safe and support(cohort, 50, 10) and support(cleared, 5, 5)
            and support(held, 5, 5)):
        return wire(Status.RELEASED, len(cleared), len(cohort))
    return wire(Status.RAN_SUPPRESSED)


def pins():
    return {path: blob((TOOLS.parent / path).read_bytes()) for path in PRODUCERS}


def members(doc):
    rows = doc['members']
    require(type(rows) is list and 0 < len(rows) <= MAX_MEMBERS)
    result, deliveries, proofs = {}, {}, {}
    for row in rows:
        require(set(row) == {'proof', 'stem', 'head', 'digest', 'blob', 'owner', 'inventory',
                             'run', 'attempt', 'verdict'})
        for key, pattern in [('head', HEX40), ('blob', HEX40), ('digest', HEX64), ('inventory', HEX64),
                             ('stem', re.compile('[A-Za-z0-9_]{1,200}')),
                             ('run', re.compile('[1-9][0-9]{0,15}')), ('attempt', re.compile('[1-9][0-9]{0,3}'))]:
            require(pattern.fullmatch(row[key]))
        for key in ('owner', 'proof'):
            require(type(row[key]) is int and 0 < row[key] < 2**63)
        require(row['verdict'] == 'ACCEPTED')
        identity = row['proof']
        require(deliveries.setdefault(identity, row) == row)
        require(proofs.setdefault(row['stem'], identity) == identity)
        digest = row['digest']
        canonical = result.setdefault(digest, row)
        require(all(canonical[field] == row[field] for field in ('owner', 'blob', 'inventory', 'stem')))
    require(type(doc['total']) is int and doc['total'] == len(result))
    return list(result.values())


def jailed(raw, judge, row):
    with tempfile.TemporaryDirectory() as work:
        jail = Path(work) / 'jail'
        for dirname in ('baseline', 'candidate', 'tools', 'in'):
            (jail / dirname).mkdir(parents=True, mode=0o755)

        def stage(path, content):
            path.write_bytes(content)
            path.chmod(0o444)

        for name in ('read-decision.py', 'outside-read.py'):
            stage(jail / 'baseline' / name, (TOOLS / name).read_bytes())
        for name, archived in ARCHIVE.items():
            stage(jail / 'candidate' / name, (TOOLS / archived).read_bytes())
        stage(jail / 'candidate/worker.py', (TOOLS / 'read-col0-v3-worker.py').read_bytes())
        (jail / 'tools/read-decision.py').symlink_to('../candidate/worker.py')
        stage(jail / 'in/proof.lean', raw)
        context = {key: row[key] for key in ('inventory', 'run', 'attempt', 'stem')}
        stage(jail / 'in/context.json', WORKER['canonical'](context))
        with tempfile.TemporaryFile(dir=work) as capture:
            cmd = ['/usr/bin/sudo', '-n', '/usr/bin/env', '-i', 'PATH=/usr/bin:/bin',
                   '/bin/sh', TOOLS / 'read-sandbox.sh', jail, judge]
            proc = subprocess.run(cmd, env={'PATH': '/usr/bin:/bin'}, stdin=subprocess.DEVNULL,
                                  stdout=capture, stderr=subprocess.DEVNULL, timeout=110)
            capture.seek(0)
            data = capture.read(3)
        require(proc.returncode == 0 and data in (b'0\n', b'1\n', b'2\n'))
        return int(data)



def reservation(env):
    """Select only the one authorized slot. All other invocations are silent."""
    number = env.get('GITHUB_RUN_NUMBER', '')
    ref = env.get('GITHUB_REF', '')
    return (env.get('COL0_V3_ENABLED') == 'true'
            and env.get('COL0_V3_SELECTION') == 'col0-v3-count'
            and env.get('GITHUB_EVENT_NAME') == 'workflow_dispatch'
            and env.get('GITHUB_REF_TYPE') == 'tag'
            and re.fullmatch(r'refs/tags/col0-v3-count-[A-Za-z0-9_-]+', ref)
            and ref == env.get('COL0_V3_TAG_REF')
            and env.get('GITHUB_REPOSITORY') == env.get('COL0_V3_REPOSITORY')
            and re.fullmatch(r'[1-9][0-9]{0,14}', number) and int(number) > 2
            and number == env.get('COL0_V3_RUN_NUMBER') and env.get('GITHUB_RUN_ATTEMPT') == '1')


def json_object(raw):
    return json.loads(raw, object_pairs_hook=V2['unique_fields'])


def binding(env):
    return {key: env[name] for key, name in (
        ('repository', 'GITHUB_REPOSITORY'), ('ref', 'GITHUB_REF'),
        ('commit', 'GITHUB_SHA'), ('run_number', 'GITHUB_RUN_NUMBER'),
        ('attempt', 'GITHUB_RUN_ATTEMPT'))} | {'workflow': WORKFLOW, 'tag_type': 'lightweight'}


def git(*args):
    return subprocess.check_output(['git', '-C', TOOLS.parent, *args], stderr=subprocess.DEVNULL,
                                   env={'PATH': '/usr/bin:/bin'}, text=True).strip()


def tag_identity(ref):
    direct = git('rev-parse', '--verify', ref)
    return git('rev-parse', 'HEAD'), git('cat-file', '-t', direct), direct, git('rev-parse', ref + '^{commit}')


def identity(env, private=False, producer_pins=pins, resolve_tag=tag_identity):
    """Authenticate the external descriptor against founder-controlled configuration."""
    raw = env['COL0_V3_DESCRIPTOR'].encode('ascii')
    digest = sha(raw)
    require(len(raw) <= 8192 and digest == env['COL0_V3_DESCRIPTOR_SHA256'])
    doc = json_object(raw)
    require(set(doc) == {'binding', 'producers', 'manifest_sha256'} and WORKER['canonical'](doc) == raw)
    expected = binding(env)
    commit, repo, ref = (expected[k] for k in ('commit', 'repository', 'ref'))
    require(HEX40.fullmatch(commit) and commit == env['COL0_V3_PEELED_COMMIT'])
    require(re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repo))
    require(env['COL0_V3_TAG_TYPE'] == 'lightweight' and doc['binding'] == expected)
    require(env['GITHUB_WORKFLOW_REF'] == f'{repo}/{WORKFLOW}@{ref}' and env['GITHUB_WORKFLOW_SHA'] == commit)
    require(resolve_tag(ref) == (commit, 'commit', commit, commit))
    require(doc['producers'] == producer_pins() and HEX64.fullmatch(doc['manifest_sha256']))
    if private:
        require(env['COL0_V3_PROTECTED_DESCRIPTOR_SHA256'] == digest
                and env['COL0_V3_PROTECTED_TAG_REF'] == ref
                and env['COL0_V3_PROTECTED_TAG_TYPE'] == 'lightweight'
                and env['COL0_V3_PROTECTED_PEELED_COMMIT'] == commit)
    return doc


def protected_binding(descriptor):
    return {'authorization': 'founder-approved-v3-count',
            'descriptor_sha256': sha(WORKER['canonical'](descriptor)),
            'manifest_sha256': descriptor['manifest_sha256']}


def run(secret, descriptor, raw, fetch, evaluate=jailed):
    if not secret:
        return wire(Status.NO_SECRET)
    try:
        require(len(secret) <= 1024 and json_object(secret) == protected_binding(descriptor))
        require(0 < len(raw) <= MAX_MANIFEST and sha(raw) == descriptor['manifest_sha256'])
        doc = json_object(raw)
        require(set(doc) == {'version', 'cutoff', 'total', 'members', 'joint_safe'})
        require(type(doc['version']) is int and doc['version'] == 3)
        require(re.fullmatch(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z', doc['cutoff']))
        require(type(doc['joint_safe']) is bool)
        rows = members(doc)
    except Exception:
        return wire(Status.MANIFEST_MISMATCH)
    cells = [[], [], []]
    try:
        judge = descriptor['producers']['tools/check-lean.mjs']
        for row in rows:
            source = fetch(row)
            require(0 < len(source) <= 524288 and sha(source) == row['digest'] and blob(source) == row['blob'])
            outcome = evaluate(source, judge, row)
            require(type(outcome) is int and 0 <= outcome <= 2)
            cells[outcome].append((row['digest'], row['owner']))
        require(sum(map(len, cells)) == doc['total'])
    except Exception:
        return wire(Status.MEMBER_REFUSED)
    return release(cells, doc['joint_safe'])


def reserved(env, private, resolve_tag=tag_identity, producer_pins=pins, fetch=None, evaluate=jailed):
    if not reservation(env):
        return b'', False
    try:
        descriptor = identity(env, private, producer_pins, resolve_tag)
    except Exception:
        return wire(Status.PIN_MISMATCH), False
    if not private:
        return b'', True
    raw = ''.join(env.get(f'COL0_V3_MANIFEST_{i}', '') for i in range(1, 5)).encode('utf-8')
    if fetch is None:
        def fetch(row):
            return V2['hosted_bytes'](descriptor['binding']['repository'],
                (row['digest'], row['owner'], row['head'], row['stem']))
    return run(env.get('COL0_V3_BINDING', '').encode('utf-8'), descriptor, raw, fetch, evaluate), False


def main(args):
    if args == ['--team-fixtures']:
        fixtures = runpy.run_path(str(TOOLS / 'read-col0-v3-fixtures.py'))
        doc, sources = fixtures['rehearsal'](sha, blob, WORKER['canonical'])
        return fixtures['run_rehearsal'](globals(), doc, sources)
    if args in (['--preflight'], ['--reserved']):
        output, authorized = reserved(os.environ, args == ['--reserved'])
        if authorized:
            with open(os.environ['GITHUB_OUTPUT'], 'a', encoding='ascii') as channel:
                channel.write('authorized=true\n')
        return output
    return b''


if __name__ == '__main__':
    try:
        sys.stdout.buffer.write(main(sys.argv[1:]))
    except Exception:
        sys.exit(1)
