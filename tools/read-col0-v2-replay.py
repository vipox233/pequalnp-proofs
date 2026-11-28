"""Trusted receipt boundary for the manually selected diagnostic. Stdout is one histogram."""
import hashlib
import http.client
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
# Set only at landing, from the single reviewed, private receipt export.
# It commits to the release run number as well as membership and attribution.
FROZEN_MANIFEST_SHA256 = 'acb49acf2171398c20ba027ab8a274a717823d1f56dfecacae30abcb7a227535'
MAX_MANIFEST = 48 * 1024
MAX_FILES = 4096
MAX_SOURCE = 524288
LIMIT = 5
HIDDEN = -1
SUPPRESSED = b'[2,[-1,-1,-1,-1,-1,-1],-1]\n'
BIN_WIRE = tuple(f'[2,{i}]\n'.encode('ascii') for i in range(6))
UNKNOWN = 4


class InvalidCohort(ValueError):
    pass


def require(condition):
    if not condition:
        raise InvalidCohort


def supported(cell):
    return len(cell) >= LIMIT and len(set(cell.values())) >= LIMIT


def histogram(cells):
    counts = [len(cell) if supported(cell) else HIDDEN for cell in cells]
    masked = [i for i, value in enumerate(counts) if value == HIDDEN]
    pool = HIDDEN
    if masked:
        # A pool must itself qualify and conceal at least two occupied cells.
        # If needed, fold in complementary supported cells in frozen enum order.
        pooled = {}
        for i in masked:
            pooled.update(cells[i])
        occupied = sum(bool(cells[i]) for i in masked)
        for i, count in enumerate(counts):
            if occupied >= 2 and supported(pooled):
                break
            if count != HIDDEN:
                counts[i] = HIDDEN
                pooled.update(cells[i])
                occupied += 1
        if occupied < 2 or not supported(pooled) or counts == [HIDDEN] * 6:
            return SUPPRESSED
        pool = len(pooled)
    return (json.dumps([2, counts, pool], separators=(',', ':')) + '\n').encode('ascii')


def unique_fields(pairs):
    obj = dict(pairs)
    require(len(obj) == len(pairs))
    return obj


def frozen_members(raw, pin, repo, number, attempt):
    require(0 < len(raw) <= MAX_MANIFEST and hashlib.sha256(raw).hexdigest() == pin)
    manifest = json.loads(raw, object_pairs_hook=unique_fields)
    require(set(manifest) == {'v', 'repo', 'run_number', 'members'})
    require(type(manifest['v']) is int and manifest['v'] == 2 and manifest['repo'] == repo)
    require(re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repo))
    release = manifest['run_number']
    require(type(release) is int and release > 0 and str(release) == number and attempt == '1')
    rows = manifest['members']
    require(type(rows) is list and 0 < len(rows) <= MAX_FILES)
    owners = {}
    for row in rows:
        require(type(row) is list and len(row) == 4)
        digest, owner, head, stem = row
        require(re.fullmatch('[0-9a-f]{64}', digest) and re.fullmatch('[0-9a-f]{40}', head))
        require(type(owner) is int and 0 < owner < 2**63)
        require(re.fullmatch('[A-Za-z0-9_]{1,200}', stem))
        require(owners.setdefault(digest, owner) == owner)
    return rows


def hosted_bytes(repo, row):
    # The approved receipt selected this immutable object. No PR discovery,
    # checkout, parser, redirects, tokens, disk cache or network inside the jail.
    _, _, head, stem = row
    connection = http.client.HTTPSConnection('raw.githubusercontent.com', timeout=30)
    try:
        connection.request('GET', f'/{repo}/{head}/lean/PEqualNP/Outside/{stem}.lean')
        response = connection.getresponse()
        require(response.status == 200)
        return response.read(MAX_SOURCE + 1)
    finally:
        connection.close()


def run_jailed(raw, judge):
    with tempfile.TemporaryDirectory() as directory:
        work = Path(directory)
        jail = work / 'jail'
        reader = jail / 'reader'
        reader.mkdir(parents=True)
        (jail / 'tools').mkdir()
        (jail / 'in').mkdir()
        for name in ('read-col0-v2.py', 'read-decision.py', 'outside-read.py'):
            shutil.copyfile(TOOLS / name, reader / name)
            (reader / name).chmod(0o444)
        # Reuse the original sandbox entrypoint. Only the worker and one proof
        # are staged here alongside its two pinned reader dependencies.
        (jail / 'tools/read-decision.py').symlink_to('../reader/read-col0-v2.py')
        proof = jail / 'in/proof.lean'
        proof.write_bytes(raw)
        proof.chmod(0o444)
        for folder in (reader, jail / 'tools', jail / 'in', jail):
            folder.chmod(0o755)
        with tempfile.TemporaryFile(dir=work) as capture:
            launch = ['/usr/bin/sudo', '-n', '/usr/bin/env', '-i', 'PATH=/usr/bin:/bin',
                      '/bin/sh', TOOLS / 'read-sandbox.sh', jail, judge]
            try:
                rc = subprocess.run(launch, env={'PATH': '/usr/bin:/bin'}, timeout=110,
                                    stdin=subprocess.DEVNULL, stdout=capture, stderr=subprocess.DEVNULL).returncode
            except (OSError, subprocess.TimeoutExpired):
                return UNKNOWN
            capture.seek(0)
            payload = capture.read(len(BIN_WIRE[0]) + 1)
        return collect_bin(rc, payload)


def collect_bin(rc, payload):
    if rc == 3 and payload == b'':
        raise InvalidCohort  # the pinned baseline did not hold this member for COL0
    if rc == 0 and payload in BIN_WIRE:
        return BIN_WIRE.index(payload)
    return UNKNOWN


def replay(rows, fetch, classify):
    seen = {}
    cells = [{} for _ in BIN_WIRE]
    for row in rows:
        digest, owner, _, _ = row
        if digest in seen:
            require(seen[digest] == owner)
            continue
        raw = fetch(row)
        require(len(raw) <= MAX_SOURCE and hashlib.sha256(raw).hexdigest() == digest)
        category = classify(raw)
        require(type(category) is int and 0 <= category < len(cells))
        cells[category][digest] = owner
        seen[digest] = owner
    return histogram(cells)


def fixture_export():
    proof = runpy.run_path(str(TOOLS / 'read-col0-v2-fixtures.py'))['proof']
    rows, blobs = [], {}
    for category in range(6):
        for suffix in range(5):
            raw = proof(category, suffix)
            digest = hashlib.sha256(raw).hexdigest()
            blobs[digest] = raw
            rows.append([digest, suffix + 1, '0' * 40, 'team'])
    return rows, lambda row: blobs[row[0]]


def main(args):
    if args == ['--team-fixtures']:
        rows, fetch = fixture_export()
    elif not args:
        manifest = os.environ.get('COL0_V2_RECEIPTS', '').encode()
        repo = os.environ.get('GITHUB_REPOSITORY', '')
        rows = frozen_members(manifest, FROZEN_MANIFEST_SHA256, repo,
                              os.environ.get('GITHUB_RUN_NUMBER'), os.environ.get('GITHUB_RUN_ATTEMPT'))
        def fetch(row):
            return hosted_bytes(repo, row)
    else:
        return SUPPRESSED
    judge = subprocess.check_output(['git', '-C', TOOLS.parent, 'rev-parse', 'HEAD:tools/check-lean.mjs'],
                                    env={'PATH': '/usr/bin:/bin'}, stderr=subprocess.DEVNULL, text=True).strip()
    require(re.fullmatch('[0-9a-f]{40}', judge))
    return replay(rows, fetch, lambda raw: run_jailed(raw, judge))


if __name__ == '__main__':
    try:
        output = main(sys.argv[1:])
    except Exception:
        output = SUPPRESSED
    sys.stdout.buffer.write(output)
