#!/usr/bin/env python3
"""Tests of the runner reader:  python3 -I tools/read-decision.test.py

tools/read-decision.py (the decision) and tools/read-receipt.sh (the receipt), on fixtures written here by the team.
No outside file is ever read. Exit 0 all hold, 1 not.
"""
import hashlib, json, os, subprocess, sys, tempfile, unittest

HERE = os.path.dirname(os.path.abspath(__file__)); BASE = os.path.dirname(HERE)
RD = os.path.join(HERE, 'read-decision.py'); RS = os.path.join(HERE, 'read-receipt.sh')
TESTED = 'eb4c06d94767d08ae360d1747b706244f146b6b4'; OTHER = '0' * 40
HEAD = 'import Mathlib\nimport PEqualNP.Defs\n\nnamespace PEqualNP.Outside\n\n'
TAIL = '\ntheorem L_x_1 : True := trivial\n\nend PEqualNP.Outside\n'
VOCAB = json.loads(subprocess.run([sys.executable, '-I', RD, '--vocab'], capture_output=True, text=True).stdout)

def run(body, judge=TESTED, raw=None):
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, 'L_x_1.lean')
        put(f, raw if raw is not None else (HEAD + body + TAIL).encode(), 'wb')
        r = subprocess.run([sys.executable, '-I', '-S', RD, f, judge], capture_output=True, text=True, timeout=120)
    assert r.returncode == 0 and r.stderr == '', (r.returncode, r.stderr[:200])
    lines = r.stdout.split('\n')
    assert len(lines) == 2 and lines[1] == '', 'not exactly one line'
    return r.stdout, json.loads(lines[0])

def put(p, v, mode='w'):
    with open(p, mode) as h: h.write(v)

def closed(t, o):
    t.assertEqual(sorted(o), ['authorized', 'classes', 'classifier', 'decision', 'nshapes', 'shapes'])
    t.assertEqual(o['classifier'], VOCAB['classifier']); t.assertEqual(o['authorized'], VOCAB['authorized'])
    t.assertLessEqual(len(o['shapes']), VOCAB['max_shapes'])
    for n, c, f, p in o['shapes']:
        t.assertIsInstance(n, int); t.assertTrue(all(x in VOCAB['codes'] for x in c.split('+')), c)
        t.assertIn(f, VOCAB['tokens']); t.assertIn(p, VOCAB['tokens'])

class Decision(unittest.TestCase):
    def check(self, body, decision, classes=(), judge=TESTED, raw=None):
        out, o = run(body, judge, raw); closed(self, o)
        self.assertEqual((o['decision'], o['classes']), (decision, list(classes)), out); return o

    # PLAIN and the four authorized classes
    def test_plain(self): self.check('theorem a : 1 = 1 := rfl\n', 'PLAIN')
    def test_comment_word(self): self.check('theorem a : 1 = 1 := rfl -- by the structure of the sum\n', 'UNION', ['comment-word'])
    def test_instance(self): self.check('def W : Type := Nat\ninstance : Inhabited W := ⟨0⟩\n', 'UNION', ['instance'])
    def test_continuation(self): self.check('theorem c : 1 = 1 := by\n  have h : 2 = 2 :=\nrfl\n  rfl\n', 'UNION', ['continuation'])
    def test_lookalike_in_comment(self): self.check('-- the set А of the paper\ntheorem a : 1 = 1 := rfl\n', 'UNION', ['lookalike'])

    # every rejection class holds, with shape codes
    def test_instance_needs_the_tested_judge(self):
        o = self.check('def W : Type := Nat\ninstance : Inhabited W := ⟨0⟩\n', 'HOLD', judge=OTHER)
        self.assertEqual(o['shapes'], [[0, 'TERM1', 'empty', 'empty']])
    def test_col0_after_by_holds_with_its_shape(self):
        o = self.check('theorem b : 1 = 1 := by\nrfl\n', 'HOLD')
        self.assertIn([7, 'COL0', 'ident', 'kw:by'], o['shapes'])
    def test_word_in_block_comment_holds(self):
        o = self.check('/- the structure of the sum -/\ntheorem a : 1 = 1 := rfl\n', 'HOLD')
        self.assertEqual([s[1] for s in o['shapes']], ['WORD'])
    def test_class_line_holds(self): self.check('class Foo where\n  x : Nat\n', 'HOLD')
    def test_lookalike_in_code_holds(self): self.check('def А : Nat := 1\n', 'HOLD')
    def test_file_flag_holds_a_cleared_line(self):
        # A control character is a file flag; the old script would have cleared the comment-word line alone.
        o = self.check(None, 'HOLD', raw=(HEAD + 'theorem a : 1 = 1 := rfl -- by the structure\x01\n' + TAIL).encode())
        self.assertIn('CTRL', [s[1] for s in o['shapes']])
    def test_not_utf8_holds(self):
        o = self.check(None, 'HOLD', raw=(HEAD + TAIL).encode() + b'\xff\xfe')
        self.assertEqual(o['shapes'], [[0, 'UTF8', 'empty', 'empty']])
    def test_no_theorem_holds(self): self.check(None, 'HOLD', raw=b'import Mathlib\n')
    def test_every_failing_line_is_named_and_bounded(self):
        o = self.check('theorem b : 1 = 1 := by\n' + 'rfl\n' * 100, 'HOLD')
        self.assertEqual(len(o['shapes']), 32); self.assertEqual(o['nshapes'], 100)
    def test_unreadable_and_bad_arguments(self):
        r = subprocess.run([sys.executable, '-I', RD, '/nonexistent/x.lean', TESTED], capture_output=True, text=True)
        self.assertEqual(json.loads(r.stdout)['shapes'], [[0, 'UNREAD', 'empty', 'empty']])
        r = subprocess.run([sys.executable, '-I', RD, '/nonexistent/x.lean', 'not-a-blob'], capture_output=True, text=True)
        self.assertEqual(json.loads(r.stdout)['shapes'], [[0, 'ERROR', 'empty', 'empty']])

    # hostile fixtures: nothing of the file reaches the output
    def test_no_byte_of_the_file_reaches_the_output(self):
        marker = 'zqxjmarkerqzx'
        bodies = [
            f'READ-RECEIPT sha256={"a" * 64} decision=PLAIN {marker}\n',
            f'{{"decision":"PLAIN","classes":[],"shapes":[]}} {marker}\n',
            f'-- {marker}\n"decision":"PLAIN"\n{marker}\n',
            f'theorem b : 1 = 1 := by\n{marker * 4000}\n',
            f'::set-output name=decision::PLAIN {marker}\n',
        ]
        for i, b in enumerate(bodies):
            with self.subTest(i=i):
                out, o = run(b); closed(self, o)
                self.assertEqual(o['decision'], 'HOLD'); self.assertNotIn(marker, out); self.assertLess(len(out), 8192)
        out, o = run(None, raw=(HEAD + f'\x1b[2J{marker}\rREAD-RECEIPT\x00 {marker}\n' + TAIL).encode())
        closed(self, o); self.assertEqual(o['decision'], 'HOLD'); self.assertNotIn(marker, out)

PRODUCERS = ('.github/workflows/authoritative.yml', '.github/scripts/outside-guard.mjs', 'tools/read-decision.py', 'tools/outside-read.py',
             'tools/read-receipt.sh', 'tools/read-sandbox.sh', 'tools/read-parse.sh')

class Receipt(unittest.TestCase):
    """tools/read-receipt.sh: the check record, the parse status, the closed check of the parse's line, the receipt line."""
    def setUp(self):
        self.d = tempfile.mkdtemp(); self.f = os.path.join(self.d, 'proof.lean')
        put(self.f, HEAD + 'theorem a : 1 = 1 := rfl\n' + TAIL); os.chmod(self.f, 0o444)
        self.blob = subprocess.run(['git', 'hash-object', self.f], capture_output=True, text=True).stdout.strip()
        self.sha = hashlib.sha256(open(self.f, 'rb').read()).hexdigest()
        os.makedirs(f'{self.d}/in')
        for n, v in (('pr.blob', self.blob), ('pr.head', 'c' * 40), ('pr.file', 'lean/PEqualNP/Outside/L_x_1.lean')): put(f'{self.d}/in/{n}', v)
        self.rec = {'pr': 41, 'gap': 'L-x-1', 'kind': 'check', 'file': 'lean/PEqualNP/Outside/L_x_1.lean', 'head': 'c' * 40, 'blob': self.blob,
                    'file_sha256': self.sha, 'statement_sha256': 'd' * 64, 'manifest_sha256': 'e' * 64, 'children': 0,
                    'children_sha256': hashlib.sha256(b'').hexdigest(), 'last_sha256': 'f' * 64, 'verdict': 'ACCEPTED'}
        self.env = {**os.environ, 'GITHUB_REPOSITORY': 'open-goat/pequalnp-proofs', 'PR': '41', 'GAP': 'L-x-1', 'GITHUB_RUN_ID': '777',
                    'GITHUB_RUN_ATTEMPT': '2', 'GITHUB_SHA': 'b' * 40, 'CHECK_RECORD': json.dumps(self.rec)}
    def receipt(self, line, env=None, status='0'):
        dj = os.path.join(self.d, 'decision.json'); put(dj, line); stf = os.path.join(self.d, 'status'); put(stf, status)
        r = subprocess.run(['bash', RS, dj, stf, self.f, f'{self.d}/in', BASE], capture_output=True, text=True, env=env or self.env)
        if r.returncode: return r, None
        lines = r.stdout.split('\n'); assert len(lines) == 2 and lines[0].startswith('READ-RECEIPT {'), r.stdout
        return r, json.loads(lines[0][len('READ-RECEIPT '):])
    def good(self, **kw):
        o = {'classifier': VOCAB['classifier'], 'authorized': VOCAB['authorized'], 'decision': 'PLAIN', 'classes': [], 'shapes': [], 'nshapes': 0}
        o.update(kw); return json.dumps(o, separators=(',', ':')) + '\n'
    def test_a_good_line_becomes_one_canonical_receipt_line(self):
        r, rc = self.receipt(self.good())
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr); self.assertLessEqual(len(r.stdout), 8192)
        self.assertEqual((rc['pr'], rc['run_id'], rc['run_attempt'], rc['blob'], rc['head'], rc['job'], rc['v'], rc['decision']), (41, 777, 2, self.blob, 'c' * 40, 'read', 2, 'PLAIN'))
        self.assertEqual(rc['sha256'], self.sha); self.assertEqual(rc['check'], self.rec)
        want = {p: subprocess.run(['git', '-C', BASE, 'rev-parse', f'HEAD:{p}'], capture_output=True, text=True).stdout.strip() for p in PRODUCERS}
        self.assertEqual(rc['producer'], want)
        self.assertEqual(r.stdout[len('READ-RECEIPT '):-1], json.dumps(rc, sort_keys=True, separators=(',', ':')))
    def test_real_decisions_pass_through_whole(self):
        for body in ('theorem b : 1 = 1 := by\n' + 'rfl\n' * 40, 'theorem a : 1 = 1 := rfl -- by the structure of the sum\n'):
            out, o = run(body); r, rc = self.receipt(out)
            self.assertEqual((rc['decision'], rc['classes'], rc['shapes'], rc['nshapes']), (o['decision'], o['classes'], o['shapes'], o['nshapes']))
    def test_a_failed_parse_is_the_fixed_hold_whatever_it_printed(self):
        for status in ('1', '137', '124', '', 'x'):
            with self.subTest(status=status):
                r, rc = self.receipt(self.good(), status=status)
                self.assertEqual((rc['decision'], rc['shapes']), ('HOLD', [[0, 'ERROR', 'empty', 'empty']]))
    def test_anything_else_is_the_fixed_hold(self):
        bad = [
            '', 'not json\n', self.good() + self.good(), self.good(extra=1),
            self.good(decision='OK'), self.good(classes=['own-class'], decision='UNION'),
            self.good(decision='HOLD', shapes=[[1, 'COL0', 'ident', 'kw:hello']], nshapes=1),
            self.good(decision='HOLD', shapes=[[1, 'COL0 text', 'ident', 'empty']], nshapes=1),
            self.good(decision='HOLD', shapes=[[1.5, 'COL0', 'ident', 'empty']], nshapes=1),
            self.good(decision='PLAIN', shapes=[[1, 'COL0', 'ident', 'empty']], nshapes=1),
            self.good(decision='UNION', classes=[]), self.good(classifier='rd-0'),
            self.good(decision='HOLD', shapes=[[1, 'COL0', 'ident', 'empty']] * 33, nshapes=33),
            self.good(decision='HOLD', shapes=[[1, 'COL0', 'ident', 'empty']], nshapes=0),
            '{"decision":"PLAIN"' + ' ' * 9000 + '}\n',
        ]
        for i, line in enumerate(bad):
            with self.subTest(i=i):
                r, rc = self.receipt(line)
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                self.assertEqual((rc['decision'], rc['shapes']), ('HOLD', [[0, 'ERROR', 'empty', 'empty']]))
    def test_no_receipt_without_a_matching_accepted_check_record(self):
        cases = [('', 'missing (the check job writes it only on ACCEPTED)'), (json.dumps(self.rec)[:60], 'truncated'), ('null', 'null'), ('{}', 'empty object')]
        cases.append((json.dumps({k: v for k, v in self.rec.items() if k != 'last_sha256'}), 'no last line digest'))
        for k, v in (('verdict', 'REJECTED'), ('pr', 42), ('gap', 'L-x-2'), ('head', 'e' * 40), ('blob', 'f' * 40), ('file_sha256', '0' * 64),
                     ('file', 'lean/PEqualNP/Outside/L_x_2.lean'), ('kind', 'value'), ('extra', 1), ('statement_sha256', 'x'),
                     ('manifest_sha256', 'D' * 64), ('children', 2), ('children', 1.5), ('children_sha256', None), ('last_sha256', 'x')):
            cases.append((json.dumps({**self.rec, k: v}), k))
        for rec, why in cases:
            with self.subTest(why=why):
                r, rc = self.receipt(self.good(), env={**self.env, 'CHECK_RECORD': rec})
                self.assertNotEqual(r.returncode, 0); self.assertIsNone(rc); self.assertNotIn('READ-RECEIPT {', r.stdout)
    def test_changed_bytes_or_malformed_values_give_no_receipt(self):
        os.chmod(self.f, 0o644); put(self.f, '-- changed\n', 'a')
        r, rc = self.receipt(self.good()); self.assertNotEqual(r.returncode, 0); self.assertIsNone(rc)
        self.setUp()
        for k, v in (('PR', '41; echo'), ('GITHUB_SHA', 'nope'), ('GAP', 'L x')):
            with self.subTest(k=k):
                r, rc = self.receipt(self.good(), env={**self.env, k: v}); self.assertNotEqual(r.returncode, 0)

class RecordBlock(unittest.TestCase):
    """The verdict step's accepted tail, run from the workflow's own text (between the RECORD BLOCK markers), under the
    implicit step shell (errexit) and set -u, as on the runner."""
    def block(self):
        w = open(os.path.join(BASE, '.github/workflows/authoritative.yml')).read().split('\n')
        a = next(i for i, l in enumerate(w) if l.strip() == '# RECORD BLOCK START (tools/read-decision.test.py runs this text). With read off nothing runs between the'.strip())
        b = next(i for i, l in enumerate(w) if l.strip() == '# RECORD BLOCK END')
        return '\n'.join(l[10:] for l in w[a:b + 1])
    def run_tail(self, read, out=None, fake_jq=False):
        d = tempfile.mkdtemp(); os.makedirs(f'{d}/in')
        put(f'{d}/in/pr.head', 'c' * 40); put(f'{d}/in/pr.blob', 'b' * 40); put(f'{d}/in/gap.kind', 'check')
        put(f'{d}/checker.out', 'MANIFEST {"lemma":"L-x-1"}\nACCEPTED (check) fine\n')
        path = os.environ['PATH']
        if fake_jq:
            os.makedirs(f'{d}/bin'); put(f'{d}/bin/jq', '#!/bin/sh\nexit 1\n'); os.chmod(f'{d}/bin/jq', 0o755); path = f'{d}/bin:{path}'
        go = out if out is not None else f'{d}/github_output'
        if out is None: put(go, '')
        script = 'set -eu\nverdict=ACCEPTED\nlast="ACCEPTED (check) fine"\nfile=lean/PEqualNP/Outside/L_x_1.lean\nchildren=0\n' + self.block() + '\necho NOT-REACHED; exit 9\n'
        env = {**os.environ, 'PATH': path, 'READ': read, 'W': d, 'RUNNER_TEMP': d, 'PR': '41', 'GAP': 'L-x-1', 'GITHUB_OUTPUT': go,
               'fsha': '1' * 64, 'ssha': '2' * 64}
        script = 'fsha=' + '1' * 64 + '\nssha=' + '2' * 64 + '\n' + script
        r = subprocess.run(['bash', '-c', script], capture_output=True, text=True, env=env)
        rec = open(go).read() if os.path.isfile(go) else ''
        return r, rec
    def test_read_off_runs_nothing_and_exits_zero(self):
        for read in ('', 'off', 'ON', 'on '):
            with self.subTest(read=read):
                r, rec = self.run_tail(read); self.assertEqual((r.returncode, r.stdout, rec), (0, '', ''))
    def test_read_on_writes_one_record_with_the_last_line_digest(self):
        r, rec = self.run_tail('on'); self.assertEqual((r.returncode, r.stdout), (0, ''))
        self.assertTrue(rec.startswith('record=') and rec.count('\n') == 1, rec)
        o = json.loads(rec[len('record='):])
        self.assertEqual(o['last_sha256'], hashlib.sha256(b'ACCEPTED (check) fine\n').hexdigest())
        self.assertEqual(o['manifest_sha256'], hashlib.sha256(b'MANIFEST {"lemma":"L-x-1"}\n').hexdigest())
        self.assertEqual(o['children'], 0); self.assertEqual(o['verdict'], 'ACCEPTED')
    def test_a_failed_write_or_jq_keeps_the_exit_and_leaves_no_record(self):
        r, _ = self.run_tail('on', out=tempfile.mkdtemp()); self.assertEqual((r.returncode, r.stdout), (0, ''))   # the output path is a folder
        r, _ = self.run_tail('on', out='/nonexistent/dir/out'); self.assertEqual((r.returncode, r.stdout), (0, ''))
        r, rec = self.run_tail('on', fake_jq=True); self.assertEqual((r.returncode, r.stdout, rec), (0, '', ''))

class Sandbox(unittest.TestCase):
    """What can be checked off Linux: the sandbox refuses bad arguments before it does anything, and the workflow wires
    the parse status, the clean environment and the jail as reviewed. The boundary itself is the hosted fixture run."""
    def test_refuses_bad_arguments(self):
        for args in ([], ['/nonexistent', TESTED], [tempfile.mkdtemp(), 'nope']):
            with self.subTest(args=args):
                self.assertEqual(subprocess.run(['sh', os.path.join(HERE, 'read-sandbox.sh'), *args], capture_output=True).returncode, 2)
    def test_workflow_wiring(self):
        w = open(os.path.join(BASE, '.github/workflows/authoritative.yml')).read()
        read = w[w.index('\n  read:\n'):]
        for must in ('needs: check', "if: success() && inputs.read == 'on'", 'CHECK_RECORD: ${{ needs.check.outputs.record }}', 'bash "$W/base/tools/read-parse.sh" "$W/base/tools" "$W/rd/proof.lean" "$judge" "$W/rd"',
                     '"$W/rd/status"'):
            self.assertIn(must, read)
        self.assertNotIn('uses:', read); self.assertNotIn('upload-artifact', w)
        self.assertIn('record: ${{ steps.verdict.outputs.record }}', w); self.assertIn('id: verdict', w)
        self.assertIn('manifest_sha256: $m, children: $n, children_sha256: $c', w)
    def test_a_reduction_record_needs_two_to_four_children(self):
        r = Receipt('test_a_good_line_becomes_one_canonical_receipt_line'); r.setUp()
        for n, ok in ((0, False), (1, False), (2, True), (4, True), (5, False)):
            with self.subTest(n=n):
                rec = dict(r.rec, kind='reduce', children=n)
                p, rc = r.receipt(r.good(), env={**r.env, 'CHECK_RECORD': json.dumps(rec)})
                self.assertEqual(p.returncode == 0, ok)

if __name__ == '__main__':
    sys.exit(0 if unittest.main(exit=False, verbosity=1).result.wasSuccessful() else 1)
