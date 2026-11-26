// node --test .github/scripts/install-elan.test.mjs
// THE INSTALLER PIN (red team ruling, 2026-11-25): install-elan.sh runs here with a stub curl and a
// recording tar. Wrong bytes give the FAULT line and a non-zero exit, and nothing is extracted; a download
// that keeps failing is tried five times, then a FAULT; the right bytes (a stand-in archive) do install.
// Only the test's copy is changed: the architecture (this test may run on another one) and the waits.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdtempSync, mkdirSync, rmSync, existsSync, chmodSync } from 'node:fs';
import { spawnSync, execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const script = readFileSync(new URL('./install-elan.sh', import.meta.url), 'utf8');
const workflow = readFileSync(new URL('../workflows/authoritative.yml', import.meta.url), 'utf8');

function setup() {
  const d = mkdtempSync(join(tmpdir(), 'pnp-elan-'));
  const swap = (s, a, b) => { assert.ok(s.includes(a), `install-elan.sh no longer has: ${a}`); return s.replace(a, b); };
  let s = swap(script, 'arch=$(uname -m)\n', 'arch=x86_64\n');
  s = swap(s, 'waits="10 20 30 60"\n', 'waits="0 0 0 0"\n');
  writeFileSync(join(d, 'install.sh'), s);
  // A stand-in archive: an elan-init that makes an elan which records what it was asked.
  mkdirSync(join(d, 'src'));
  writeFileSync(join(d, 'src', 'elan-init'), `#!/bin/sh\nmkdir -p "$ELAN_HOME/bin"\nprintf '#!/bin/sh\\necho "$*" >> "$ELAN_HOME/elan.log"\\n' > "$ELAN_HOME/bin/elan"\nchmod +x "$ELAN_HOME/bin/elan"\necho "init $*" > "$ELAN_HOME/init.log"\n`);
  chmodSync(join(d, 'src', 'elan-init'), 0o755);
  execFileSync('/usr/bin/tar', ['-czf', join(d, 'asset.tar.gz'), '-C', join(d, 'src'), 'elan-init']);
  // stub curl: counts its calls; the first FAIL_FIRST calls fail with 56, then it writes the asset to -o.
  mkdirSync(join(d, 'bin'));
  writeFileSync(join(d, 'bin', 'curl'), `#!/bin/sh\nn=$(( $(cat "${d}/curl.n" 2>/dev/null || echo 0) + 1 )); echo $n > "${d}/curl.n"\n` +
    `while [ $# -gt 0 ]; do [ "$1" = -o ] && out=$2; last=$1; shift; done\necho "$last" >> "${d}/curl.urls"\n` +
    `[ "$n" -le "$FAIL_FIRST" ] && { echo "curl: (56) Connection died" >&2; exit 56; }\ncp "${d}/asset.tar.gz" "$out"\n`);
  writeFileSync(join(d, 'bin', 'tar'), `#!/bin/sh\necho "$*" >> "${d}/tar.calls"\nexec /usr/bin/tar "$@"\n`);
  chmodSync(join(d, 'bin', 'curl'), 0o755); chmodSync(join(d, 'bin', 'tar'), 0o755);
  const good = createHash('sha256').update(readFileSync(join(d, 'asset.tar.gz'))).digest('hex');
  const run = (sha, failFirst = 0) => spawnSync('/bin/sh', [join(d, 'install.sh'), 'v4.4.0', sha, join(d, 'home'), 'leanprover/lean4:v4.0.0'],
    { encoding: 'utf8', env: { PATH: `${d}/bin:/usr/bin:/bin:/usr/sbin:/sbin`, FAIL_FIRST: String(failFirst) } });
  const read = (f) => existsSync(join(d, f)) ? readFileSync(join(d, f), 'utf8') : '';
  return { d, good, run, read, done: () => rmSync(d, { recursive: true, force: true }) };
}

test('a wrong sha256: the FAULT line, a non-zero exit, nothing extracted or run, no retry', () => {
  const t = setup();
  try {
    const r = t.run('0'.repeat(64));
    assert.notEqual(r.status, 0);
    assert.equal(r.stdout.trim().split('\n').pop(), "FAULT: the elan installer's sha256 is not the pinned one; nothing was extracted or run");
    assert.equal(t.read('tar.calls'), '', 'tar ran on bytes that do not match the pin');
    assert.equal(existsSync(join(t.d, 'home')), false, 'ELAN_HOME was made');
    assert.equal(t.read('curl.n').trim(), '1', 'a hash mismatch was downloaded again');
    assert.equal(t.read('curl.urls').trim(), 'https://github.com/leanprover/elan/releases/download/v4.4.0/elan-x86_64-unknown-linux-gnu.tar.gz');
  } finally { t.done(); }
});

test('a download that keeps failing: five tries, then the FAULT line, nothing extracted', () => {
  const t = setup();
  try {
    const r = t.run(t.good, 99);
    assert.notEqual(r.status, 0);
    assert.equal(r.stdout.trim().split('\n').pop(), 'FAULT: the pinned elan installer could not be downloaded (5 tries)');
    assert.equal(t.read('curl.n').trim(), '5');
    assert.equal(t.read('tar.calls'), '');
    assert.equal(existsSync(join(t.d, 'home')), false);
  } finally { t.done(); }
});

test('positive control: the pinned bytes after two failed downloads install elan, then the toolchain', () => {
  const t = setup();
  try {
    const r = t.run(t.good, 2);
    assert.equal(r.status, 0, r.stdout + r.stderr);
    assert.equal(t.read('curl.n').trim(), '3');
    assert.match(r.stdout, new RegExp(`elan v4\\.4\\.0: sha256 ${t.good} \\(the pinned one\\)`));
    assert.equal(t.read('home/init.log'), 'init -y --no-modify-path --default-toolchain none\n');
    assert.equal(t.read('home/elan.log'), 'toolchain install leanprover/lean4:v4.0.0\n');
  } finally { t.done(); }
});

test('malformed pins are refused before any download', () => {
  const t = setup();
  try {
    const r = t.run('xyz');
    assert.notEqual(r.status, 0);
    assert.equal(r.stdout.trim(), 'FAULT: the pinned elan sha256 is not 64 hex digits');
    assert.equal(t.read('curl.n'), '');
  } finally { t.done(); }
});

const advisory = readFileSync(new URL('../workflows/advisory.yml', import.meta.url), 'utf8');
test('both workflows: no unpinned installer, the same pins, no action, the script called with them', () => {
  const pin = (wf, k) => { const m = wf.match(new RegExp(`^\\s+${k}: (\\S+)$`, 'm')); assert.ok(m, `no ${k}`); return m[1]; };
  for (const [name, wf] of [['authoritative.yml', workflow], ['advisory.yml', advisory]]) {
    assert.doesNotMatch(wf, /elan-init\.sh|releases\/latest|elan\/master/, `${name}: an unpinned installer address`);
    assert.doesNotMatch(wf, /^\s+(?:- )?uses:/m, `${name}: uses an action`);
    assert.match(pin(wf, 'ELAN_VERSION'), /^v\d+\.\d+\.\d+$/); assert.match(pin(wf, 'ELAN_SHA256'), /^[0-9a-f]{64}$/);
  }
  assert.equal(pin(advisory, 'ELAN_VERSION'), pin(workflow, 'ELAN_VERSION'), 'the two workflows pin different elan versions');
  assert.equal(pin(advisory, 'ELAN_SHA256'), pin(workflow, 'ELAN_SHA256'), 'the two workflows pin different hashes');
  assert.match(workflow, /sh "\$W\/base\/\.github\/scripts\/install-elan\.sh" "\$ELAN_VERSION" "\$ELAN_SHA256" "\$ELAN_HOME"/);
  // advisory: the script from the BASE side of the merge, never the pull request's copy.
  assert.match(advisory, /git show 'HEAD\^1:\.github\/scripts\/install-elan\.sh' > "\$RUNNER_TEMP\/install-elan\.sh"\n\s+sh "\$RUNNER_TEMP\/install-elan\.sh" "\$ELAN_VERSION" "\$ELAN_SHA256"/);
  assert.doesNotMatch(advisory, /sh \.github\/scripts\/install-elan\.sh/);
});

const library = readFileSync(new URL('../workflows/library-build.yml', import.meta.url), 'utf8');
test('library-build.yml: hand start only, read-only, no action, no secret, the same elan pins, both modes through lake-locked.sh, an empty mode refuses a Defs path', () => {
  const pin = (wf, k) => { const m = wf.match(new RegExp(`^\\s+${k}: (\\S+)$`, 'm')); assert.ok(m, `no ${k}`); return m[1]; };
  assert.equal(pin(library, 'ELAN_VERSION'), pin(workflow, 'ELAN_VERSION'));
  assert.equal(pin(library, 'ELAN_SHA256'), pin(workflow, 'ELAN_SHA256'));
  assert.doesNotMatch(library, /^\s+(?:- )?uses:/m, 'uses an action');
  assert.doesNotMatch(library, /secrets\./, 'names a secret');
  assert.match(library, /^on:\n  workflow_dispatch:\n/m, 'started by hand only');
  assert.doesNotMatch(library, /^\s+(push|pull_request|pull_request_target|schedule|workflow_run):/m, 'another trigger');
  assert.match(library, /^permissions:\n  contents: read\n  pull-requests: read\n\n/m);
  // Both modes: the one locked compile step takes the empty mode's changed modules and the full mode's whole tree.
  assert.match(library, /if \[ "\$MODE" = full \]; then\n[\s\S]+?\n\s+set -- PEqualNP\n[\s\S]+?else\n\s+set --; while IFS= read -r m; do set -- "\$@" "\$m"; done < "\$W\/in\/modules\.txt"[\s\S]+?sh "\$W\/base\/\.github\/scripts\/lake-locked\.sh" build "\$@"/);
  assert.match(library, /sh "\$W\/base\/\.github\/scripts\/lake-locked\.sh" build "\$m"/, 'the sample compiles through lake-locked.sh');
  assert.match(library, /sh "\$W\/base\/\.github\/scripts\/install-elan\.sh" "\$ELAN_VERSION" "\$ELAN_SHA256" "\$ELAN_HOME"/);
  // An empty mode takes ADDED library files only: a Defs path, the root, an outside path or a workflow never match.
  const re = (k) => new RegExp(library.match(new RegExp(`^\\s+${k}: '(.+)'$`, 'm'))[1]);
  for (const p of ['lean/PEqualNP/Library/X.lean', 'lean/PEqualNP/Library/Sub/X.lean']) assert.ok(re('LIB_PATH').test(p), p);
  for (const p of ['lean/PEqualNP/Defs/X.lean', 'lean/PEqualNP/Defs.lean', 'lean/PEqualNP/Outside/L_x_1.lean', '.github/workflows/x.yml', 'lean/lakefile.toml', 'lean/PEqualNP/Library/a/b/X.lean']) assert.ok(!re('LIB_PATH').test(p), p);
  assert.ok(re('DEFS_PATH').test('lean/PEqualNP/Defs/X.lean') && !re('DEFS_PATH').test('lean/PEqualNP/Defs/a/X.lean') && !re('DEFS_PATH').test('lean/PEqualNP/Library/X.lean'));
  assert.match(library, /select\(\(\.status != "added"\) or \(\.previous_filename != null\) or \(\(\.filename \| test\(env\.LIB_PATH\)\) \| not\)\)/, 'the empty mode refuses all but an added library file');
  // The association rule, run as the workflow runs it: OWNER, MEMBER and COLLABORATOR pass; an outside author does not.
  const assoc = library.match(/(case "\$\(jq -r '\.author_association \/\/ ""' "\$W\/api\/pr\.json"\)" in [^\n]+ esac)/);
  assert.ok(assoc, 'the association rule is not where the test looks');
  for (const [v, ok] of [['OWNER', true], ['MEMBER', true], ['COLLABORATOR', true], ['CONTRIBUTOR', false], ['FIRST_TIME_CONTRIBUTOR', false], ['FIRST_TIMER', false], ['NONE', false], ['', false]]) {
    const dir = mkdtempSync(join(tmpdir(), 'assoc-')); const W = dir;
    try {
      mkdirSync(join(W, 'api')); writeFileSync(join(W, 'api', 'pr.json'), JSON.stringify(v ? { author_association: v } : {}));
      const r = spawnSync('bash', ['-c', `${assoc[1]}\necho PASSED`], { env: { ...process.env, W }, encoding: 'utf8' });
      assert.equal(r.stdout.includes('PASSED'), ok, `${v || '(none)'}: ${r.stdout}`);
    } finally { rmSync(dir, { recursive: true, force: true }); }
  }
});

// THE IMPORT CHECK (seat-redteam-1 R1, seat-redteam-2 A): the reader takes the leading blank and import lines; a later
// import line, or one after a block comment's end, makes the file refused. The awk program is run here as the workflow
// runs it, on files of each shape.
test('library-build.yml: a leading comment no longer hides an import from the check', () => {
  const m = library.match(/imports=\$\(awk '([\s\S]+?)' "\$W\/in\/files\/\$i\.lean"\)/);
  assert.ok(m, 'the import reader is not where the test looks');
  const dir = mkdtempSync(join(tmpdir(), 'imports-'));
  try {
    const run = (text) => { const f = join(dir, 'f.lean'); writeFileSync(f, text); return execFileSync('awk', [m[1].replace(/\n\s+/g, '\n'), f], { encoding: 'utf8' }).trim().split('\n').filter(Boolean); };
    assert.deepEqual(run('import Mathlib\nimport PEqualNP.Defs.Base\n\ndef x : Nat := 1\n'), ['Mathlib', 'PEqualNP.Defs.Base']);
    assert.deepEqual(run('\n\nimport Mathlib\ntheorem t : 1 = 1 := rfl\n'), ['Mathlib']);
    assert.ok(run('-- a comment first\nimport PEqualNP.Library.Helpers\n').includes('LATE'), 'a line comment before the imports');
    assert.ok(run('/- a block\n   comment -/\nimport PEqualNP.Library.Helpers\n').includes('LATE'), 'a block comment before the imports');
    assert.ok(run('/- x -/ import PEqualNP.Library.Helpers\n').includes('LATE'), 'an import after a block comment on one line');
    assert.ok(run('import Mathlib\ndef x : Nat := 1\n  import PEqualNP.Library.Helpers\n').includes('LATE'), 'an indented import after the header');
    assert.deepEqual(run('def x : Nat := 1\n'), []);
  } finally { rmSync(dir, { recursive: true, force: true }); }
  assert.match(library, /case "\$imports" in \*LATE\*\) echo "REFUSED: \$f has an import line after its first other line/);
});

// OUTSIDE-DEPENDENT FLEET MODULES (the baseline run of 26 Nov): left out of the tree build, which has the outside folder
// aside, and built after the sample with the folder present. The import walk is run here, as the workflow runs it.
test('library-build.yml: fleet modules that reach an outside proof are found by their imports and built in their own locked step', () => {
  const m = library.match(/python3 -I - "\$RUNNER_TEMP\/outside-dependent\.txt" <<'PY'\n([\s\S]+?)\n\s*PY\n/);
  assert.ok(m, 'the import walk is not where the test looks');
  const py = m[1].split('\n').map((l) => l.replace(/^ {10}/, '')).join('\n');
  const dir = mkdtempSync(join(tmpdir(), 'walk-'));
  try {
    const put = (rel, text) => { mkdirSync(join(dir, rel, '..'), { recursive: true }); writeFileSync(join(dir, rel), text); };
    put('PEqualNP/Defs.lean', 'import Mathlib\n');
    put('PEqualNP/Library/A.lean', 'import PEqualNP.Defs\n');
    put('PEqualNP/MetaComplexity/Direct.lean', 'import PEqualNP.Outside.L_meta_1\n');
    put('PEqualNP/MetaComplexity/Through.lean', 'import PEqualNP.MetaComplexity.Direct\n');
    put('PEqualNP/MetaComplexity/Clean.lean', 'import PEqualNP.Library.A\n-- import PEqualNP.Outside.L_meta_2\n');
    const out = join(dir, 'dep.txt');
    execFileSync('python3', ['-I', '-', out], { cwd: dir, input: py });
    assert.deepEqual(readFileSync(out, 'utf8').trim().split('\n'), ['PEqualNP.MetaComplexity.Direct', 'PEqualNP.MetaComplexity.Through']);
  } finally { rmSync(dir, { recursive: true, force: true }); }
  assert.match(library, /grep -qxF "\$m" "\$RUNNER_TEMP\/outside-dependent\.txt" \|\| set -- "\$@" "\$m"/, 'they are left out of the tree build');
  assert.match(library, /id: dep\n\s+if: env\.MODE == 'full' && steps\.run\.outputs\.code == '0'\n\s+timeout-minutes: 60\n/);
  assert.match(library, /sh "\$W\/base\/\.github\/scripts\/lake-locked\.sh" build "\$m" >> "\$RUNNER_TEMP\/dep\.out"/, 'built through lake-locked.sh, one module a build');
  assert.ok(library.indexOf('id: sample') < library.indexOf('id: dep'), 'after the sample');
  assert.match(library, /\[ -n "\$\{DN:-\}" \] && \[ "\$\{DPASS:-\}" = "\$DN" \] \|\| ok=no/);
});

// THE BASELINE (seat-redteam-2 B): memory first.
test('library-build.yml: full mode caps threads by memory, has swap, the memory watch and step limits', () => {
  assert.match(library, /bymem=\$\(\( \$\(awk '\/\^MemTotal:\/\{print \$2\}' \/proc\/meminfo\) \/ 4194304 \)\)/, 'threads by memory (GB / 4)');
  assert.match(library, /- name: Swap space for the build \(as authoritative\)/);
  assert.match(library, /sh "\$W\/base\/\.github\/scripts\/memory-watch\.sh" "\$RUNNER_TEMP\/sampler" "\$cg" "\$unit" "\$t0" "\$cap" "\$MARK"/);
  assert.match(library, /systemd-run --quiet --scope --collect --unit="\$unit" -p MemoryMax="\$\{cap\}K"/);
  assert.match(library, /id: sample\n\s+if: env\.MODE == 'full' && steps\.run\.outputs\.code == '0'\n\s+timeout-minutes: 100\n/, 'the sample step has its own limit');
  assert.doesNotMatch(library, /MeaningProbe/, 'no meaning test in this patch (it comes rebuilt, separately)');
});
