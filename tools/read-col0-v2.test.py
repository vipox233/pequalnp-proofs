"""Run on team data only. No network, git history, production receipts or Lean imports."""
import hashlib
import itertools
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parent
PROOF = runpy.run_path(str(TOOLS / 'read-col0-v2-fixtures.py'))['proof']
WORKER = TOOLS / 'read-col0-v2.py'
PUBLISHER = TOOLS / 'read-col0-v2-replay.py'
HIDDEN = b'[2,[-1,-1,-1,-1,-1,-1],-1]\n'
JUDGE = 'eb4c06d94767d08ae360d1747b706244f146b6b4'


def on_proof(reader, raw):
    with tempfile.TemporaryDirectory() as root:
        path = Path(root) / 'team.lean'
        path.write_bytes(raw)
        return reader(path, JUDGE)


class Diagnostic(unittest.TestCase):
    def test_private_reader_all_six_bins(self):
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / 'team.lean'
            for category in range(6):
                with self.subTest(category=category):
                    path.write_bytes(PROOF(category))
                    run = subprocess.run([sys.executable, '-I', '-B', '-S', WORKER, path, JUDGE],
                                         capture_output=True)
                    self.assertEqual((run.returncode, run.stdout, run.stderr),
                                     (0, f'[2,{category}]\n'.encode(), b''))
            path.write_bytes(b'theorem notHeld : True := True.intro\n')
            run = subprocess.run([sys.executable, '-I', '-B', '-S', WORKER, path, JUDGE], capture_output=True)
            self.assertEqual((run.returncode, run.stdout, run.stderr), (3, b'', b''))

    def test_main_holds_each_team_fixture_before_serialization(self):
        baseline = runpy.run_path(str(TOOLS / 'read-decision.py'))
        for category, expected in enumerate(([2], [2], [3], [2, 6], [2], [2, 5, 8, 11, 14])):
            with self.subTest(category=category):
                decision, _, rows = on_proof(baseline['decide'], PROOF(category))
                self.assertEqual(decision, 'HOLD')
                self.assertEqual([n for n, reasons, _, _ in rows if 'COL0' in reasons.split('+')], expected)

    def test_single_file_and_diverse_cohort_bytes(self):
        api = runpy.run_path(str(PUBLISHER))
        cells = [{} for _ in range(6)]
        for i in range(6):
            digest = hashlib.sha256(PROOF(i)).hexdigest()
            cells[i][digest] = 1
            self.assertEqual(api['histogram'](cells), HIDDEN)
            cells[i].clear()
        for i, cell in enumerate(cells):
            for n in range(5):
                cell[hashlib.sha256(PROOF(i, n)).hexdigest()] = n + 1
        self.assertEqual(api['histogram'](cells), b'[2,[5,5,5,5,5,5],-1]\n')


class Shapes(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rd = runpy.run_path(str(WORKER))

    def packet(self, text, line=2):
        return next(self.rd['shapes'](text.encode(), {line}))

    def test_clipped_fixed_arity_all_bits_and_depth(self):
        raw = 'lemma amber (n : Nat) : Nat := (((1 + 2 -\nn + 3 + 4\n  + 5 + 6)))\n'
        # ROUND, depth THREE_PLUS, all three slices clipped.
        self.assertEqual(self.packet(raw), bytes([2, 1, 0, 3, 1, 1, 1, 2, 6, 1, 6, 2, 6, 6, 2]))
        self.assertEqual(self.packet(raw.replace('\n', '\r\n')), self.packet(raw))
        self.assertEqual(self.packet(raw.replace('1 + 2', '1 /- ( /- -- -/ ) -/ + 2')), self.packet(raw))

    def test_slice_ends_at_nearest_construct_and_command(self):
        raw = 'def amber (n : Nat) : Nat := ((1 -\nn) + 1\n  + 2)\n'
        # The close is on the held line. The outer + and number are out of scope.
        self.assertEqual(self.packet(raw), bytes([2, 2, 0, 2, 1, 0, 0, 2, 6, 1, 12, 0, 0, 0, 0]))
        body = 'theorem t : 0 = 0 := by\n  exact\nrfl\n'
        self.assertEqual(self.packet(body + 'def x : Nat := 3\n', 3),
                         bytes([2, 0, 4, 0, 1, 0, 0, 5, 5, 5, 0, 0, 0, 0, 0]))
        self.assertEqual(self.packet(body + 'theorem red : True := True.intro\n', 3), self.packet(body, 3))
        self.assertEqual(self.packet('example : Nat := (\n3\n)\n')[7:9], bytes([0, 8]))

    def test_pinned_commands_groups_and_tokens(self):
        for cmd, code in (('theorem x', 0), ('lemma x', 1), ('def x', 2), ('example', 3), ('abbrev x', 4)):
            self.assertEqual(self.packet(f'{cmd} : Nat := (1 -\n2\n)\n')[1], code)
        for i, (left, right) in enumerate(zip('([{⟨', ')]}⟩')):
            p = self.packet(f'def x : Nat := {left}1 -\n2\n{right}\n')
            self.assertEqual((p[2], p[3], p[9], p[13]), (i, 1, 2, 12 + i))
            self.assertEqual(self.rd['file_bin']([p]), 0)
        words = 'def x : Char := ("--/-",\n\'q\')\n'
        self.assertEqual(self.packet(words)[7:11], bytes([3, 7, 4, 12]))

    def test_uncertain_syntax_has_one_fixed_unknown(self):
        base = PROOF(1).decode()
        for bad in ('`(term| 1)', 's!"{n}"', 'r"raw"', '0xff', '1.25', '⟨1]', '(1', '1)',
                    "foo% 1", 'do return 1', 'if True then 1 else 2', '«red»'):
            with self.subTest(bad=bad):
                raw = base.replace('Nat.succ', bad).encode()
                self.assertEqual(list(self.rd['shapes'](raw, {2})), [self.rd['UNKNOWN_SHAPE']])
        for text in ('syntax "tag" : term\n', ' /-- docs -/\n', '/-! module docs -/\n',
                     'open Widget\n', 'macro "red" : term => 1\n', '  def x : Nat := 1\n',
                     'theorem q : True := True.intro def sub : Nat := 0\n'):
            with self.subTest(text=text):
                self.assertEqual(list(self.rd['shapes']((text + base).encode(), {3})), [self.rd['UNKNOWN_SHAPE']])
        # A margin identifier after a complete ungrouped term has no proven owner.
        self.assertEqual(self.packet('def x (n : Nat) : Nat := Nat.succ\nn\n'), self.rd['UNKNOWN_SHAPE'])

    def test_tactic_at_margin_has_no_proven_owner(self):
        self.assertEqual(self.packet('theorem t : 0 = 0 := by\nrfl\n'), self.rd['UNKNOWN_SHAPE'])

    def test_uncertainty_in_a_later_command_only_masks_unproven_shapes(self):
        first = PROOF(1)
        second = PROOF(3, 9).replace(b'  )\n', b'  + `(term| 0))\n')
        self.assertEqual(on_proof(self.rd['observe'], first + second), 3)

    def test_collector_rejects_wrong_size_range_bits_and_padding(self):
        rd = self.rd
        p = self.packet('def x : Nat := (1 -\n2\n)\n')
        bad = [b'', p + b'X', list(p), bytearray(p), p[:-1]]
        for i, value in ((0, 1), (1, 5), (2, 5), (3, 4), (3, 0), (4, 2), (5, 1),
                         (7, 16), (8, 0), (9, 0), (11, 1), (14, 16)):
            bad.append(p[:i] + bytes([value]) + p[i+1:])
        for entry in bad:
            self.assertFalse(rd['valid'](entry))
            self.assertEqual(rd['file_bin']([entry]), 4)
        self.assertEqual(rd['file_bin']([p, rd['UNKNOWN_SHAPE']]), 3)
        self.assertEqual(rd['file_bin']([p] * 80), 0)

    def test_holds_beyond_the_receipt_prefix_and_independent_baseline(self):
        base = self.rd['BASELINE']
        raw = PROOF(0)
        before = on_proof(base['decide'], raw)
        self.assertEqual((before[0], [r[1] for r in before[2]]), ('HOLD', ['WORD', 'COL0']))
        self.assertEqual(on_proof(self.rd['observe'], raw), 0)
        self.assertEqual(on_proof(base['decide'], raw), before)
        prefix = b''.join(PROOF(2, i) for i in range(40))
        self.assertEqual(on_proof(self.rd['observe'], prefix), 2)
        self.assertEqual(on_proof(self.rd['observe'], prefix + raw), 3)


class Release(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.api = runpy.run_path(str(PUBLISHER))

    def cells(self, sizes, diversity):
        return [{(i, n): 1 + n % d for n in range(size)}
                for i, (size, d) in enumerate(zip(sizes, diversity))]

    def test_small_diversity_pool_and_complementary_suppression(self):
        hist = self.api['histogram']
        for sizes, owners, expected in (
            ([4, 4, 5, 5, 5, 5], [4]*2 + [5]*4, b'[2,[-1,-1,-1,5,5,5],13]\n'),
            ([5, 4, 5, 5, 5, 5], [2, 4, 5, 5, 5, 5], b'[2,[-1,-1,-1,5,5,5],14]\n'),
            ([1, 5, 5, 5, 5, 5], [1] + [5]*5, b'[2,[-1,-1,5,5,5,5],6]\n'),
            ([10, 0, 0, 0, 0, 0], [5]*6, HIDDEN),
            ([2]*6, [2]*6, HIDDEN),
            ([30]*6, [1]*6, HIDDEN),
        ):
            self.assertEqual(hist(self.cells(sizes, owners)), expected)
        cells = self.cells([4, 4, 5, 5, 5, 5], [5]*6)
        cells[1] = {f: owner + 4 for f, owner in cells[1].items()}
        self.assertEqual(hist(cells), b'[2,[-1,-1,5,5,5,5],8]\n')

    def test_public_schema_for_every_occupancy_mask(self):
        for sizes in itertools.product((0, 2, 5), repeat=6):
            cells = self.cells(sizes, [5]*6)
            output = self.api['histogram'](cells)
            version, counts, pool = json.loads(output)
            self.assertEqual((version, len(counts)), (2, 6))
            self.assertEqual(output, (json.dumps([2, counts, pool], separators=(',', ':')) + '\n').encode())
            if output == HIDDEN:
                continue
            for actual, observed in zip(sizes, counts):
                self.assertIn(observed, (-1, actual))
                self.assertTrue(observed == -1 or observed >= 5)
            masked = [cells[i] for i, n in enumerate(counts) if n == -1]
            if masked:
                self.assertEqual(pool, sum(map(len, masked)))
                self.assertGreaterEqual(sum(bool(x) for x in masked), 2)
                self.assertGreaterEqual(len(set.union(*(set(x.values()) for x in masked))), 5)
            else:
                self.assertEqual(pool, -1)

    def test_bounded_private_bin_channel(self):
        collect = self.api['collect_bin']
        for i in range(6):
            self.assertEqual(collect(0, f'[2,{i}]\n'.encode()), i)
        for bad in (b'[2,0]', b'[2,0]\n\n', b'[2,9]\n', b'[2,true]\n', b'[2,0,1]\n',
                    b'[2,0]\nquartzVioletLark', b'[[2,0]]\n', b'X' * 65537):
            self.assertEqual(collect(0, bad), 4)
        self.assertEqual(collect(137, b'[2,0]\n'), 4)
        with self.assertRaises(self.api['InvalidCohort']):
            collect(3, b'')

    def test_sealed_export_no_filtered_or_overlapping_release(self):
        rows, _ = self.api['fixture_export']()
        manifest = dict(v=2, repo='team/test', run_number=31, members=rows)
        encode = lambda obj: json.dumps(obj, separators=(',', ':')).encode()
        original = encode(manifest)
        pin = hashlib.sha256(original).hexdigest()
        check = self.api['frozen_members']
        self.assertEqual(check(original, pin, 'team/test', '31', '1'), rows)
        for raw, number, attempt in (
                (encode(dict(manifest, members=rows[:-1])), '31', '1'),
                (encode(dict(manifest, members=rows[1:])), '31', '1'),
                (encode(dict(manifest, members=rows[::-1])), '31', '1'),
                (original, '32', '1'), (original, '31', '2')):
            with self.assertRaises(ValueError):
                check(raw, pin, 'team/test', number, attempt)
        for bad in (dict(manifest, members=[rows[0], [rows[0][0], 99, *rows[0][2:]]]),
                    dict(manifest, members=[[rows[0][0], True, *rows[0][2:]]]),
                    dict(manifest, members=[[*rows[0][:3], '../escape']]), dict(manifest, filter='owner')):
            raw = encode(bad)
            with self.assertRaises(ValueError):
                check(raw, hashlib.sha256(raw).hexdigest(), 'team/test', '31', '1')

    def test_whole_replay_no_canaries_and_no_duplicate_votes(self):
        rows, fetch = self.api['fixture_export']()
        classifier = runpy.run_path(str(WORKER))
        visited = []
        def classify(raw):
            visited.append(raw)
            return on_proof(classifier['observe'], raw)
        replay = self.api['replay']
        result = replay(rows * 2, fetch, classify)
        self.assertEqual(len(visited), 30)
        for marker in ('quartzVioletLarkₐ', 'opal-cabinet-73951'):
            self.assertIn(marker.encode(), visited[0])
            self.assertNotIn(marker.encode(), result)
        self.assertEqual(result, b'[2,[5,5,5,5,5,5],-1]\n')
        with self.assertRaises(ValueError):
            replay(rows, lambda _: b'wrong bytes', classify)

    def test_public_entrypoint_only_emits_fixed_bytes(self):
        for args in ([], ['--filter', 'quartzVioletLark'], ['--cohort', 'opal-cabinet-73951']):
            run = subprocess.run([sys.executable, '-I', '-B', '-S', PUBLISHER, *args],
                                 env={**os.environ, 'COL0_V2_RECEIPTS': 'opal-cabinet-73951'},
                                 capture_output=True, check=True)
            self.assertEqual((run.stdout, run.stderr), (HIDDEN, b''))
        # Exercise private selection with an authenticated team export and the
        # staged worker entrypoint. Only the network and Linux launcher are replaced.
        rows, fetch = self.api['fixture_export']()
        doc = json.dumps(dict(v=2, repo='team/trial', run_number=41, members=rows))
        env = dict(COL0_V2_RECEIPTS=doc, GITHUB_RUN_NUMBER='41', GITHUB_RUN_ATTEMPT='1',
                   GITHUB_REPOSITORY='team/trial')
        def launch(argv, **kwargs):
            root = Path(argv[-2])
            self.assertEqual(kwargs['env'], {'PATH': '/usr/bin:/bin'})
            self.assertEqual({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()},
                             {'reader/read-decision.py', 'reader/outside-read.py', 'reader/read-col0-v2.py',
                              'tools/read-decision.py', 'in/proof.lean'})
            return subprocess.run([sys.executable, '-I', '-B', '-S', root / 'tools/read-decision.py',
                                   root / 'in/proof.lean', argv[-1]], **kwargs)
        original_run = subprocess.run
        def dispatch(argv, **kwargs):
            if argv[0] == '/usr/bin/sudo':
                return launch(argv, **kwargs)
            return original_run(argv, **kwargs)
        main = self.api['main']
        with patch.dict(os.environ, env), patch.dict(main.__globals__, {
                'FROZEN_MANIFEST_SHA256': hashlib.sha256(doc.encode()).hexdigest(),
                'hosted_bytes': lambda _, row: fetch(row)}), patch.object(subprocess, 'run', dispatch):
            self.assertEqual(main([]), b'[2,[5,5,5,5,5,5],-1]\n')

    def test_private_workflow_is_manual_and_pinned(self):
        workflow = (TOOLS.parent / '.github/workflows/read-diagnostic.yml').read_text()
        for value in ('workflow_dispatch:', 'default: existing', "inputs.diagnostic != 'col0-v2'",
                      "inputs.diagnostic == 'col0-v2' && github.ref", 'environment: col0-v2-private',
                      "github.sha == vars.COL0_V2_BASE && secrets.COL0_V2_RECEIPTS", 'permissions: {}'):
            self.assertIn(value, workflow)
        private = workflow.split('\n  private:\n')[1]
        self.assertNotIn('upload-artifact', workflow)
        self.assertNotIn('read-receipt.sh', private)
        self.assertNotIn('inputs.', private.split('steps:')[1])


class ProductionIdentity(unittest.TestCase):
    def test_production_blobs_match_origin_main(self):
        root = TOOLS.parent

        def git(*args):
            return subprocess.check_output(['git', '-C', root, *args])

        # Protect the entire production tooling surface, including transitive
        # files and the receipt publisher. Only the manual diagnostic may differ.
        tree = git('ls-tree', '-r', '-z', 'origin/main', '--', 'tools', '.github')
        self.assertTrue(tree, 'origin/main has no tooling tree')
        expected_blobs = {}
        for entry in tree.rstrip(b'\0').split(b'\0'):
            metadata, name = entry.split(b'\t', 1)
            path = os.fsdecode(name)
            if path == '.github/workflows/read-diagnostic.yml':
                continue
            _, kind, expected = metadata.split()
            file = root / path
            self.assertTrue(kind == b'blob' and file.is_file() and not file.is_symlink(), path)
            expected_blobs[path] = expected
        paths = b''.join(os.fsencode(path) + b'\n' for path in expected_blobs)
        actual = subprocess.check_output(
            ['git', '-C', root, 'hash-object', '--no-filters', '--stdin-paths'], input=paths,
        ).splitlines()
        for path, digest in zip(expected_blobs, actual, strict=True):
            self.assertEqual(digest, expected_blobs[path], path)
        # These tracked checker inputs are outside the sparse checkout. Use
        # their index blob IDs so this test never has to materialize them.
        checker = ('lean/CheckLemma.lean', 'lean/lean-toolchain',
                   'lean/lakefile.toml', 'lean/lake-manifest.json')
        for path in checker:
            self.assertEqual(git('rev-parse', f':{path}'), git('rev-parse', f'origin/main:{path}'), path)
        print(f'Production identity: {len(expected_blobs)} worktree blobs and '
              f'{len(checker)} sparse index blobs match origin/main', flush=True)


if __name__ == '__main__':
    unittest.main()
