"""Coverage wire and trust-boundary tests using only team-generated data."""
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parent
API = runpy.run_path(str(TOOLS / 'read-col0-v3.py'))
FIXTURES = runpy.run_path(str(TOOLS / 'read-col0-v3-fixtures.py'))
PIN = API['pins']()
SUPPRESSED = b'[3,5,-1,-1]\n'
RELEASED = b'[3,6,5,50]\n'


class Count(unittest.TestCase):
    def setUp(self):
        self.doc, self.sources = FIXTURES['rehearsal'](
            API['sha'], API['blob'], API['WORKER']['canonical'])

    def cells(self, total=50, owners=10, yes=5, no=5, yes_owners=5, no_owners=5):
        return [[(i, i % distinct) for i in range(size)] for size, distinct in (
            (total - yes - no, owners), (no, no_owners), (yes, yes_owners))]

    def test_each_release_floor(self):
        release = API['release']
        for dimension, boundary in (('total', 50), ('owners', 10), ('yes', 5), ('no', 5),
                                    ('yes_owners', 5), ('no_owners', 5)):
            with self.subTest(floor=dimension):
                self.assertEqual(release(self.cells(**{dimension: boundary - 1})), SUPPRESSED)
                self.assertEqual(release(self.cells(**{dimension: boundary})), RELEASED)
        for yes, no in ((0, 10), (1, 9), (10, 0), (9, 1), (5, 1)):
            self.assertEqual(release(self.cells(yes=yes, no=no)), SUPPRESSED)
        self.assertEqual(release(self.cells(), False), SUPPRESSED)

    def replay(self, evaluate=lambda *args: 0, *, pin=None, fetch=None, changes=None,
               private=True, tag_change=None):
        env, tag = FIXTURES['platform'](API, self.doc)
        env.update(changes or {})
        return API['reserved'](
            env, private, lambda ref: tag if tag_change is None else tag_change,
            lambda: PIN if pin is None else pin,
            fetch or (lambda row: self.sources[row['digest']]), evaluate,
        )

    def test_exact_status_bytes_and_late_failure(self):
        self.assertEqual(self.replay(changes={'COL0_V3_BINDING': ''})[0], b'[3,2,-1,-1]\n')
        for secret in (' ', '{}', '{"authorization":"invalid"}'):
            self.assertEqual(self.replay(changes={'COL0_V3_BINDING': secret})[0], b'[3,3,-1,-1]\n')
        self.assertEqual(self.replay(changes={'COL0_V3_MANIFEST_1': ''})[0], b'[3,3,-1,-1]\n')
        for path in ('tools/check-lean.mjs', 'tools/read-col0-v3-worker.py'):
            self.assertEqual(self.replay(pin={**PIN, path: '0' * 40},
                                        changes={'COL0_V3_BINDING': ''})[0], b'[3,1,-1,-1]\n')
        checked = []
        def late_failure(raw, judge, row):
            checked.append(row['proof'])
            if row['proof'] == 50:
                raise ValueError
            return 2 if row['proof'] < 6 else 1
        failure = self.replay(late_failure)[0]
        self.assertEqual(failure, b'[3,4,-1,-1]\n')
        self.assertEqual(checked, list(range(1, 51)))
        self.assertEqual(self.replay(fetch=lambda row: self.sources[row['digest']]
                                     if row['proof'] != 50 else None)[0], failure)
        self.assertEqual(self.replay(fetch=lambda row: self.sources[row['digest']]
                                     if row['proof'] != 50 else b'wrong bytes')[0], failure)
        self.assertEqual(self.replay(lambda *args: 99)[0], failure)
        self.assertEqual(self.replay()[0], SUPPRESSED)
        self.assertEqual(self.replay(lambda raw, judge, row: (2 if row['proof'] <= 5
                                                              else 1 if row['proof'] <= 10 else 0))[0], RELEASED)

    def test_reservation_and_order(self):
        self.assertEqual(self.replay(private=False, changes={'COL0_V3_BINDING': ''}), (b'', True))
        for changes in ({'GITHUB_RUN_NUMBER': '4'}, {'GITHUB_RUN_ATTEMPT': '2'},
                        {'GITHUB_RUN_NUMBER': '2', 'COL0_V3_RUN_NUMBER': '2'},
                        {'GITHUB_REF': 'refs/heads/col0-v3-count-team', 'GITHUB_REF_TYPE': 'branch'},
                        {'COL0_V3_ENABLED': 'false'}, {'COL0_V3_SELECTION': 'existing'}):
            def unexpected(_):
                self.fail('an unauthorized slot fetched content')
            self.assertEqual(self.replay(fetch=unexpected, changes=changes), (b'', False))
            self.assertEqual(self.replay(fetch=unexpected, changes=changes, private=False), (b'', False))
        for changes in ({'GITHUB_WORKFLOW_REF': 'wrong'},
                        {'COL0_V3_DESCRIPTOR_SHA256': '0' * 64},
                        {'COL0_V3_PROTECTED_TAG_TYPE': 'annotated'},
                        {'COL0_V3_PROTECTED_PEELED_COMMIT': 'b' * 40},
                        {'COL0_V3_PROTECTED_DESCRIPTOR_SHA256': '0' * 64}):
            self.assertEqual(self.replay(changes=changes)[0], b'[3,1,-1,-1]\n')
        self.assertEqual(self.replay(tag_change=('a' * 40, 'tag', 'b' * 40, 'a' * 40))[0],
                         b'[3,1,-1,-1]\n')

    def test_moving_main_and_same_named_branch_do_not_move_tag(self):
        with tempfile.TemporaryDirectory() as folder:
            def git(*args):
                return subprocess.check_output(['git', '-C', folder, *args], stderr=subprocess.DEVNULL,
                                               text=True).strip()
            git('init', '-q', '-b', 'main')
            git('-c', 'user.name=Team', '-c', 'user.email=team@example.test',
                'commit', '--allow-empty', '-qm', 'reviewed tag fixture')
            commit = git('rev-parse', 'HEAD')
            git('tag', 'col0-v3-count-team')
            git('-c', 'user.name=Team', '-c', 'user.email=team@example.test',
                'commit', '--allow-empty', '-qm', 'moving main fixture')
            newer = git('rev-parse', 'HEAD')
            git('branch', 'col0-v3-count-team')
            git('checkout', '-q', '--detach', commit)
            with patch.dict(API['tag_identity'].__globals__, {'git': git}):
                resolved = API['tag_identity']('refs/tags/col0-v3-count-team')
            self.assertNotEqual(newer, commit)
            self.assertEqual(resolved, (commit, 'commit', commit, commit))
            self.assertEqual(git('rev-parse', 'refs/heads/col0-v3-count-team'), newer)
            env, _ = FIXTURES['platform'](API, self.doc, commit)
            self.assertEqual(API['reserved'](env, False, lambda ref: resolved), (b'', True))
            env['GITHUB_SHA'] = newer
            self.assertEqual(API['reserved'](env, False, lambda ref: resolved), (b'[3,1,-1,-1]\n', False))

    def test_scheduler_missing_receipt_is_silent(self):
        command = [sys.executable, '-I', '-B', '-S', TOOLS / 'read-col0-v3.py', '--preflight']
        run = subprocess.run(command, env={}, capture_output=True)
        self.assertEqual((run.returncode, run.stdout, run.stderr), (0, b'', b''))
        workflow = (TOOLS.parent / API['WORKFLOW']).read_text()
        self.assertIn("needs.coverage_preflight.outputs.authorized == 'true'", workflow)

    def test_exact_duplicates_revisions_and_ambiguous_ownership(self):
        row = self.doc['members'][0]
        self.doc['members'].append(row.copy())
        self.assertEqual(len(API['members'](self.doc)), 50)
        for changed in ({'head': 'd' * 40}, {'owner': 99, 'proof': 999, 'stem': 'L_alias'},
                        {'verdict': 'REJECTED'}, {'inventory': '0' * 64}):
            self.doc['members'][-1] = {**row, **changed}
            self.assertEqual(self.replay()[0], b'[3,3,-1,-1]\n')
        self.doc['members'].pop()
        self.doc['members'].pop()
        self.assertEqual(self.replay()[0], b'[3,3,-1,-1]\n')

    def test_team_rehearsal_through_real_staged_worker(self):
        launch = subprocess.run
        outcomes = []

        def local(argv, **kwargs):
            self.assertEqual(argv[0], '/usr/bin/sudo')
            self.assertEqual(kwargs['env'], {'PATH': '/usr/bin:/bin'})
            jail, judge = Path(argv[-2]), argv[-1]
            context = json.loads((jail / 'in/context.json').read_bytes())
            self.assertEqual(set(context), {'run', 'attempt', 'stem', 'inventory'})
            proc = launch([sys.executable, '-I', '-B', '-S', jail / 'tools/read-decision.py',
                           jail / 'in/proof.lean', judge], capture_output=True, env=kwargs['env'])
            self.assertEqual(proc.stderr, b'')
            outcomes.append(proc.stdout)
            kwargs['stdout'].write(proc.stdout)
            return proc

        with patch.object(subprocess, 'run', local):
            self.assertEqual(API['main'](['--team-fixtures']), RELEASED)
            self.assertEqual(outcomes, [b'2\n'] * 5 + [b'1\n'] * 5 + [b'0\n'] * 40)
            self.doc['members'][-1]['inventory'] = '0' * 64
            self.assertEqual(self.replay(API['jailed'])[0], b'[3,4,-1,-1]\n')
        self.assertEqual(API['main']([]), b'')
        self.assertEqual(API['reserved']({}, True), (b'', False))

    def test_full_inventory_preserves_late_independent_hold(self):
        row = self.doc['members'][0]
        raw = self.sources[row['digest']]
        lines = raw.splitlines(keepends=True)
        raw = b''.join(lines[:2] + [b'n\xe2\x82\x90\n  -\n'] * 36 + [b'n\xe2\x82\x90\n', lines[-1], b'-- please visit\n'])
        baseline = runpy.run_path(str(TOOLS / 'read-decision.py'))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'team.lean'
            path.write_bytes(raw)
            ordinary = baseline['decide'](str(path), PIN['tools/check-lean.mjs'])
        self.assertGreater(len(ordinary[2]), 32)
        self.assertEqual(ordinary[2][-1][1], 'ADDR')
        context = dict(row, inventory=API['sha'](API['WORKER']['canonical'](ordinary)))
        launch = subprocess.run

        def local(argv, **kwargs):
            jail, judge = Path(argv[-2]), argv[-1]
            return launch([sys.executable, '-I', '-B', '-S', jail / 'tools/read-decision.py',
                           jail / 'in/proof.lean', judge], **kwargs)

        with patch.object(subprocess, 'run', local):
            self.assertEqual(API['jailed'](raw, PIN['tools/check-lean.mjs'], context), 0)


# V2's whole-surface blob guard also covers V3. Include it in this suite.
ProductionIdentity = runpy.run_path(str(TOOLS / 'read-col0-v2.test.py'))['ProductionIdentity']


if __name__ == '__main__':
    unittest.main()
