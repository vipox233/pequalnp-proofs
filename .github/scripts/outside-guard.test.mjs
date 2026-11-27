// node --test .github/scripts/outside-guard.test.mjs
// The plain-file rule of outside-guard.mjs: one fixture per way a proof file could carry code
// that runs while it compiles (or hide it from a reader), and the honest shapes that must pass.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkImports, checkOwnNamespace } from './outside-guard.mjs';

const head = 'import Mathlib\nimport PEqualNP.Defs\n\n';
const run = (body) => checkImports(new TextEncoder().encode(head + body), ['PEqualNP.Defs']);
const refused = (name, body, word) => test(`refused: ${name}`, () => {
  assert.throws(() => run(body), (e) => e.message.includes(word), 'not refused, or for another reason');
});
// What passes passes the whole `imports` mode: the plain-file rule and the own-namespace rule.
const passes = (name, body) => test(`passes: ${name}`, () => {
  assert.deepEqual(run(body), ['Mathlib', 'PEqualNP.Defs']);
  checkOwnNamespace(head + body, 'PEqualNP.Outside.L_x_1');
});
const thm = 'theorem PEqualNP.Outside.L_x_1 : True := trivial\n';
const by = (tac) => `theorem PEqualNP.Outside.L_x_1 : True := by\n  ${tac}\n`;

refused('an initialize', `initialize pure ()\n${thm}`, 'initialize');
refused('an indented initialize', `${thm}  initialize pure ()\n`, 'initialize');
refused('run_cmd, indented', `${thm} run_cmd pure ()\n`, 'run_cmd');
refused('#eval', `${thm} #eval 1\n`, '#');
refused('a tactic that runs code', by('run_tac (do return ())'), 'run_tac');
refused('an elaborator, indented', `${thm} elab x : term => pure default\n`, 'elab');
refused('a macro, indented', `${thm} macro x : tactic => y\n`, 'macro');
refused('notation3', `${thm} notation3 x => y\n`, 'notation');
refused('an attribute command', `${thm} attribute [simp] Nat.add_comm\n`, 'attribute');
refused('a generating attribute', `@[to_additive] theorem foo : True := trivial\n${thm}`, '@[');
refused('an option that is not a limit', `set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an indented option that is not a limit', by('set_option debug.skipKernelTC true in\n  trivial'), 'set_option');
refused('a same-line option that is not a limit', `set_option maxHeartbeats 1 in set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an axiom', `${thm} axiom a : False\n`, 'axiom');
refused('sorry', by('sorry'), 'sorry');
refused('sorryAx', 'theorem PEqualNP.Outside.L_x_1 : False := sorryAx _\n', 'sorry');
refused('lcProof', 'theorem PEqualNP.Outside.L_x_1 : False := lcProof\n', 'lcProof');
refused('native_decide', by('native_decide'), 'native');
refused('decide +native', by('decide +native'), 'native');
refused('bv_decide', by('bv_decide'), 'bv_decide');
refused('a simproc', `${thm}  simproc foo (x) := y\n`, 'simproc');
refused('open Lean', `open Lean in\n${thm}`, 'Lean');
refused('ofReduceBool', by('exact ofReduceBool x true rfl'), 'ofReduce');
refused('_root_', by('exact _root_.id trivial'), '_root_');
refused('include_str', by('exact include_str x'), 'include_str');
refused('polyrith', by('polyrith'), 'polyrith');
refused('a string literal', `private def s : String := "x"\n${thm}`, '"');
refused('a character-literal trick', `${thm}  -- '"'\n`, '"');
refused('a quoted identifier', `private def «a» : Nat := 1\n${thm}`, '«');
refused('code hidden behind a comment trick', `-- a note /- here\n  initialize pure ()\n-- done -/\n${thm}`, 'initialize');
refused('a command after a comment on one line', `/- note -/ initialize pure ()\n${thm}`, 'initialize');
refused('a syntax quotation', by('exact \x60(tactic| trivial)'), '(tactic|');
refused('#check', `#check Nat\n${thm}`, '#check');
refused('#print axioms, indented', `${thm}  #print axioms Nat.add_comm\n`, '#print');
refused('a direction-changing character', `-- ‮\n${thm}`, 'invisible');
refused('no theorem at all', 'def x : Nat := 1\n', 'no theorem');
// Commands that take an explicit target name could place a declaration outside the file's own
// namespace; refused anywhere until tested in Lean (red team, read of the own-namespace rule).
refused('mk_iff_of_inductive_prop', `mk_iff_of_inductive_prop Foo Bar.baz\n${thm}`, 'mk_iff_of_inductive_prop');
refused('proof_wanted', `proof_wanted foo : True\n${thm}`, 'proof_wanted');
refused('an attribute that takes a target name', `@[to_additive Foo.bar] theorem t : True := trivial\n${thm}`, '@[');

passes('one theorem', thm);
passes('helpers, definitions, namespaces, a docstring', `namespace PEqualNP.Outside.L_x_1\nopen Finset\nvariable {n : ℕ}\n/-- A doc comment. -/\nprivate def f (x : ℕ) : ℕ := x\nprivate lemma l : f 1 = 1 := rfl\nend PEqualNP.Outside.L_x_1\n\n${thm}`);
passes('a block comment with indented prose', `/-\n  The idea of the proof,\n  in two lines.\n-/\n${thm}`);
passes('the simp attributes', `namespace PEqualNP.Outside.L_x_1\n@[simp] private theorem a : True := trivial\n@[local simp] private theorem b : True := trivial\nend PEqualNP.Outside.L_x_1\n${thm}`);
passes('the four limit options', `set_option maxHeartbeats 400000 in\nset_option maxRecDepth 2000 in\n${thm}`);
passes('an indented limit option inside a proof', by('set_option maxRecDepth 2000 in\n  trivial'));
passes('comment prose at column 0 and a heading (form is not judged)', `/-!\n# A heading\n\nProse that starts in column 0,\nover two lines.\n-/\n${thm}`);
passes('a small enumerated type and an instance', `namespace PEqualNP.Outside.L_x_1\nprivate inductive Stack | input | output\n  deriving DecidableEq\n\nprivate instance : Inhabited Stack := ⟨.input⟩\nend PEqualNP.Outside.L_x_1\n${thm}`);
passes('open scoped, and a cardinality written with a hash', `open scoped BigOperators\ntheorem PEqualNP.Outside.L_x_1 (s : Finset ℕ) : #s = #s := rfl\n`);
passes('a pair in backticks inside a doc comment', '/-- The coordinates \x60(a, b, c, d)\x60 of the block. -/\n' + thm);
passes('lemma names that contain add_', by('simp only [Nat.add_comm, add_zero]'));

// The closure rule: which listed modules the base step may build, and which are outside-written
// and built only in the locked step. The base tree is a map here; `read` answers null for a file
// that is not a plain file of the base tree.
import { importClosure, headerImports } from './outside-guard.mjs';
const tree = (files) => (m) => (m in files ? new TextEncoder().encode(files[m]) : null);
const proof = (imports, name = 'PEqualNP.Outside.L_x_2') => `${imports.map((m) => `import ${m}\n`).join('')}\ntheorem ${name} : True := trivial\n`;
const judged = 'PEqualNP.Outside.L_x_1';
const closure = (listed, files) => importClosure(listed, tree(files), judged);
const closureRefused = (name, listed, files, word) => test(`closure refused: ${name}`, () => {
  assert.throws(() => closure(listed, files), (e) => e.message.includes(word), 'not refused, or for another reason');
});

test('closure: base modules only, as before', () => {
  assert.deepEqual(closure(['PEqualNP.Gct.A'], { 'PEqualNP.Gct.A': 'import Mathlib\nimport PEqualNP.Gct.B\n', 'PEqualNP.Gct.B': '-- note\nimport PEqualNP.Defs\n', 'PEqualNP.Defs': 'import Mathlib\n' }),
    { outside: [], base: ['PEqualNP.Defs', 'PEqualNP.Gct.A', 'PEqualNP.Gct.B'] });
});
test('closure: a listed outside module is never handed to the base step; the base modules it imports are', () => {
  const r = closure(['PEqualNP.Outside.L_meta_473'], {
    'PEqualNP.Outside.L_meta_473': proof(['Mathlib', 'PEqualNP.Defs', 'PEqualNP.Outside.L_meta_9'], 'PEqualNP.Outside.L_meta_473'),
    'PEqualNP.Outside.L_meta_9': proof(['Mathlib', 'PEqualNP.Gct.L090'], 'PEqualNP.Outside.L_meta_9'),
    'PEqualNP.Defs': 'import Mathlib\n', 'PEqualNP.Gct.L090': 'import PEqualNP.Defs\n' });
  assert.deepEqual(r, { outside: ['PEqualNP.Outside.L_meta_473', 'PEqualNP.Outside.L_meta_9'], base: ['PEqualNP.Defs', 'PEqualNP.Gct.L090'] });
});
closureRefused('the judged file itself', [judged], {}, 'the file being judged');
closureRefused('an outside module that imports the judged file', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof([judged]) }, 'the file being judged');
closureRefused('a listed module missing from the base', ['PEqualNP.Outside.L_x_9'], {}, 'not a plain file of the base tree');
closureRefused('a listed base module missing from the base', ['PEqualNP.Gct.Nope'], {}, 'not a plain file of the base tree');
closureRefused('a base module that imports an outside module', ['PEqualNP.Gct.A'], { 'PEqualNP.Gct.A': 'import PEqualNP.Gct.B\n', 'PEqualNP.Gct.B': '/- x -/ import PEqualNP.Outside.L_x_2\n', 'PEqualNP.Outside.L_x_2': proof(['Mathlib']) }, 'imports the outside-written');
closureRefused('a base module behind an outside module that imports another outside module', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['PEqualNP.Gct.B']), 'PEqualNP.Gct.B': 'import PEqualNP.Outside.L_x_3\n', 'PEqualNP.Outside.L_x_3': proof([]) }, 'imports the outside-written');
closureRefused('an outside module that runs code when it compiles', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': `import Mathlib\ninitialize pure ()\n${thm}` }, 'initialize');
closureRefused('an outside module with an import below its header', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': `import Mathlib\n${thm}/- -/ import PEqualNP.Gct.B\n` }, 'the word "import"');
closureRefused('an outside module importing something not Mathlib and not the project', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['Lean.Elab']) }, 'not allowed');
closureRefused('a module under Outside that is not a proof file name', ['PEqualNP.Outside.Helper'], { 'PEqualNP.Outside.Helper': proof(['Mathlib']) }, 'not the name of an outside proof file');
test('closure: a cycle between outside modules ends', () => {
  assert.deepEqual(closure(['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['PEqualNP.Outside.L_x_3']), 'PEqualNP.Outside.L_x_3': proof(['PEqualNP.Outside.L_x_2']) }).outside, ['PEqualNP.Outside.L_x_2', 'PEqualNP.Outside.L_x_3']);
});

test('header: comments, module, modifiers, quoted names', () => {
  assert.deepEqual(headerImports('/- a /- nested -/ b -/\n-- c\nmodule\npublic import «PEqualNP».Outside.L_x_2\nmeta import all Mathlib.Tactic\nimport PEqualNP.Defs -- d\n\ntheorem t : True := trivial\n', 'm'),
    ['PEqualNP.Outside.L_x_2', 'Mathlib.Tactic', 'PEqualNP.Defs']);
});
test('header: an import line below the header is refused, never passed over', () => {
  assert.throws(() => headerImports('import Mathlib\ndef x := 1\nimport PEqualNP.Outside.L_x_2\n', 'm'), /below its header/);
});

// Reached base modules are under the PEqualNP root only, and outside modules are capped.
import { MAX_OUTSIDE } from './outside-guard.mjs';
closureRefused('a listed fixture module', ['CheckerSuite.Pass'], { 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under the PEqualNP root');
closureRefused('a base module that imports a fixture module', ['PEqualNP.Gct.A'], { 'PEqualNP.Gct.A': 'import CheckerSuite.Pass\n', 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under the PEqualNP root');
closureRefused('an outside module that imports a fixture module', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['CheckerSuite.Pass']), 'CheckerSuite.Pass': 'import Mathlib\n' }, 'not under the PEqualNP root');
const many = (n) => Object.fromEntries(Array.from({ length: n }, (_, k) => [`PEqualNP.Outside.L_x_${k + 10}`, proof(['Mathlib'], `PEqualNP.Outside.L_x_${k + 10}`)]));
test(`closure: ${MAX_OUTSIDE} outside modules pass`, () => {
  assert.equal(MAX_OUTSIDE, 16);
  assert.equal(closure(Object.keys(many(MAX_OUTSIDE)), many(MAX_OUTSIDE)).outside.length, MAX_OUTSIDE);
});
closureRefused(`${MAX_OUTSIDE + 1} outside modules listed`, Object.keys(many(MAX_OUTSIDE + 1)), many(MAX_OUTSIDE + 1), `more than ${MAX_OUTSIDE} outside modules`);
test(`closure refused: ${MAX_OUTSIDE + 1} outside modules, one listed and the rest reached through it`, () => {
  const files = many(MAX_OUTSIDE);
  files['PEqualNP.Outside.L_x_1000'] = proof(Object.keys(many(MAX_OUTSIDE)), 'PEqualNP.Outside.L_x_1000');
  assert.throws(() => closure(['PEqualNP.Outside.L_x_1000'], files), /more than 16 outside modules/);
});

// The own-namespace rule (checkOwnNamespace): every helper inside the file's own namespace block,
// PEqualNP.Outside.L_<x> or PEqualNP.Outside.L_<x>_aux (or below them); at the top level only the
// imports, `open` lines, the four limit options, those blocks and the one theorem, last.
const own = (file, body) => checkOwnNamespace(head + body, file);
const M = 'PEqualNP.Outside.L_meta_9';
const t9 = `theorem ${M} : True := by\n  trivial\n`;
const ownPasses = (name, body, mod = M) => test(`own namespace passes: ${name}`, () => { own(mod, body); });
const ownRefused = (name, body, word, mod = M) => test(`own namespace refused: ${name}`, () => {
  assert.throws(() => own(mod, body), (e) => e.message.includes(word), 'not refused, or for another reason');
});
ownPasses('only the theorem', t9);
ownPasses('helpers inside the own namespace', `namespace ${M}\n\ndef f (n : ℕ) : ℕ := n\nlemma l : f 1 = 1 := rfl\n\nend ${M}\n\nopen ${M} in\n${t9}`);
ownPasses('nested namespace and sections inside it', `namespace ${M}\nnamespace Helpers\nsection\nvariable {n : ℕ}\ntheorem a : n = n := rfl\nend\nnoncomputable section Reals\ndef g : ℕ := 0\nend Reals\nend Helpers\nend ${M}\n${t9}`);
ownPasses('the _aux form, a dotted block below it, and the block opened twice', `namespace ${M}_aux\ntheorem a : True := trivial\nend ${M}_aux\nnamespace ${M}_aux.Helpers\ntheorem b : True := trivial\nend ${M}_aux.Helpers\nnamespace ${M}.More\ntheorem c : True := trivial\nend ${M}.More\n${t9}`);
ownPasses('a where block after the theorem (its helpers carry no command word)', `theorem ${M} : 2 = 2 := by\n  exact aux 2\nwhere\n  aux (n : ℕ) : n = n := by\n    induction n with\n    | zero => rfl\n    | succ k ih => rfl\n  termination_by structural n\n`);
ownPasses('mutual inside the own namespace', `namespace ${M}\nmutual\ndef ev : ℕ → Bool\n  | 0 => true\n  | n + 1 => od n\ndef od : ℕ → Bool\n  | 0 => false\n  | n + 1 => ev n\nend\nend ${M}\n${t9}`);
ownPasses('comments, a doc comment, limit options and open lines at the top level', `/-! notes\ndef not_code : ℕ := 0\n-/\nopen Finset\n-- def nor_this : ℕ := 0\nset_option maxHeartbeats 400000 in\n/-- The step. -/\n${t9}`);
ownPasses('a statement over several lines, some at column 0', `theorem ${M} :\n∀ n : ℕ,\n  n = n := by\n  intro n\n  rfl\n`);
ownPasses('a comment after the proof', `namespace ${M}\ntheorem a : True := trivial\nend ${M}\n${t9}-- trailing note\n`);

ownRefused('a helper at the top level', `def f : ℕ := 1\n${t9}`, 'line 4: a declaration');
ownRefused('a private helper at the top level', `private lemma l : True := trivial\n${t9}`, 'line 4: a declaration');
ownRefused('a helper declared with the own name at the top level', `theorem ${M}.a : True := trivial\n${t9}`, 'line 4: a declaration');
ownRefused('the project namespace at the top level', `namespace PEqualNP.Library.Machines\ndef f : ℕ := 1\nend PEqualNP.Library.Machines\n${t9}`, '`namespace PEqualNP.Library.Machines` at the top level');
ownRefused('namespace PEqualNP.Outside with the short theorem name', `namespace PEqualNP.Outside\ntheorem L_meta_9 : True := trivial\nend PEqualNP.Outside\n`, '`namespace PEqualNP.Outside` at the top level');
ownRefused('a second top-level namespace after the own one closed', `namespace ${M}\ndef f : ℕ := 1\nend ${M}\nnamespace Other\ndef g : ℕ := 1\nend Other\n${t9}`, 'line 7: `namespace Other`');
ownRefused('an indented namespace', `namespace ${M}\n  namespace Inner\n  end Inner\nend ${M}\n${t9}`, 'line 5: `namespace`, `section`, `end`');
ownRefused('an indented end that would close the own block early', `namespace ${M}\ndef f : ℕ := 1\n  end ${M}\ndef PEqualNP.Library.g : ℕ := 1\nend ${M}\n${t9}`, 'line 6: `namespace`, `section`, `end`');
ownRefused('an end in the middle of a line', `namespace ${M}\ndef f : ℕ := 1 end ${M}\ndef g : ℕ := 1\n${t9}`, 'line 5: `namespace`, `section`, `end`');
ownRefused('the own block closed, then a helper', `namespace ${M}\ndef f : ℕ := 1\nend ${M}\ndef g : ℕ := 1\n${t9}`, 'line 7: a declaration');
ownRefused('an end that names a part of the own namespace', `namespace ${M}\nend L_meta_9\ndef g : ℕ := 1\n${t9}`, 'does not name what it closes');
ownRefused('an end with nothing open', `end ${M}\n${t9}`, 'nothing open');
ownRefused('a bare end closing a namespace', `namespace ${M}\nend\n${t9}`, 'does not name what it closes');
ownRefused('the namespace of ANOTHER step that shares a prefix', `namespace PEqualNP.Outside.L_meta_99\ndef f : ℕ := 1\nend PEqualNP.Outside.L_meta_99\n${t9}`, '`namespace PEqualNP.Outside.L_meta_99` at the top level');
ownRefused('the _aux namespace of ANOTHER step that shares a prefix', `namespace PEqualNP.Outside.L_meta_99_aux\nend PEqualNP.Outside.L_meta_99_aux\n${t9}`, 'at the top level');
ownRefused('a name that only starts like the own one', `namespace ${M}x\nend ${M}x\n${t9}`, 'at the top level');
ownRefused('a section at the top level', `section\ndef f : ℕ := 1\nend\n${t9}`, 'a section at the top level');
ownRefused('noncomputable section at the top level', `noncomputable section\ndef f : ℕ := 1\nend\n${t9}`, 'a section at the top level');
ownRefused('mutual at the top level', `mutual\ndef f : ℕ := 1\nend\n${t9}`, '`mutual` at the top level');
ownRefused('a helper after the theorem', `${t9}\ndef PEqualNP.Library.g : ℕ := 1\n`, 'after the theorem');
ownRefused('an indented helper after the theorem, as if in the proof', `${t9}  def g : ℕ := 1\n`, 'after the theorem');
ownRefused('a namespace after the theorem', `${t9}namespace ${M}\nend ${M}\n`, 'nothing but the proof may follow');
ownRefused('a second theorem after the theorem', `${t9}theorem x : True := trivial\n`, 'after the theorem');
ownRefused('a command hidden after a comment on a top-level line', `/- note -/ def f : ℕ := 1\n${t9}`, 'line 4: a declaration');
ownRefused('open ... in with a helper on the same line', `open Finset in def f : ℕ := 1\n${t9}`, 'must end with `in`');
ownRefused('a simp helper at the top level', `@[simp] theorem a : True := trivial\n${t9}`, 'line 4: a declaration');
ownRefused('variable at the top level', `variable {n : ℕ}\n${t9}`, 'line 4: a declaration');
ownRefused('no theorem with the full name', `namespace ${M}\ntheorem x : True := trivial\nend ${M}\n`, 'the theorem must stand at the top level');
ownRefused('a theorem of another step', `theorem PEqualNP.Outside.L_meta_99 : True := trivial\n`, 'line 4: a declaration');
ownRefused('a file name ending in _aux', `theorem PEqualNP.Outside.L_meta_9_aux : True := trivial\n`, 'may not end in _aux', 'PEqualNP.Outside.L_meta_9_aux');

// The add_ rule's sentence names the way round for an honest proof line.
refused('a proof line that begins with a lemma named add_...', `theorem PEqualNP.Outside.L_x_1 : True := by\n  exact\n    add_or_out\n`, 'may not BEGIN with a name that starts with add_');
// A file-wide limit option is refused with the one fix named; anything else set file-wide gets no such hint.
refused('a limit option set for the whole file', `set_option maxHeartbeats 400000\n${thm}`, 'write it as set_option <option> <value> in');
refused('a file-wide option that is not a limit', `set_option autoImplicit true\n${thm}`, 'no options but the four limits');
test('no limit hint for an option that is not a limit', () => {
  assert.throws(() => run(`set_option autoImplicit true\n${thm}`), (e) => !e.message.includes('write it as set_option'));
});
refused('an add_ command still refused', `add_decl_doc Nat.succ\n${thm}`, '"add_decl_doc" is not allowed');

// A refutation step: the desk's kind decides how the checker judges the file.
import { checkGap as checkGapKind } from './outside-guard.mjs';
const KF = 'lean/PEqualNP/Outside/L_meta_632.lean';
const krow = (kind, more = {}) => ({ gaps: [{ id: 'L-meta-632', file: KF, module: 'PEqualNP.Outside.L_meta_632', statement: 'True', imports: [], ...(kind === undefined ? {} : { kind }), ...more }] });
const pick632 = (x) => x.id === 'L-meta-632';
test('gap kind: a step without a kind is judged as a check', () => { assert.equal(checkGapKind(krow(undefined), pick632, KF).kind, 'check'); });
test('gap kind: a refutation step is judged as a refutation', () => { assert.equal(checkGapKind(krow('refute'), pick632, KF).kind, 'refute'); });
test('gap kind: an unknown kind is refused', () => { assert.throws(() => checkGapKind(krow('prove'), pick632, KF), /unknown kind/); });
test('gap kind: a run of kind refute on a refutation step passes', () => { assert.equal(checkGapKind(krow('refute'), pick632, KF, 'refute').kind, 'refute'); });
test('gap kind: a run of kind check on a refutation step is refused', () => { assert.throws(() => checkGapKind(krow('refute'), pick632, KF, 'check'), /the desk posts gap L-meta-632 as kind refute/); });
test('gap kind: a run of kind refute on a check step is refused', () => { assert.throws(() => checkGapKind(krow(undefined), pick632, KF, 'refute'), /as kind check/); });

// A reduction of a posted step S: lean/PEqualNP/Outside/R_<gap>_<n>.lean, kind reduce, and the desk's
// row of S carries reductions: true (dark: absent means refused).
import { checkFileKind, checkPr as checkPrR, FILE_RE as FILE_RE_R } from './outside-guard.mjs';
const RF = (n) => `lean/PEqualNP/Outside/R_meta_632_${n}.lean`;
test('reduce: a valid R_ file with kind reduce and reductions: true passes', () => {
  const g = checkGapKind(krow(undefined, { reductions: true }), pick632, RF(1), 'reduce');
  assert.equal(g.kind, 'reduce'); assert.equal(g.statement, 'True'); assert.equal(g.id, 'L-meta-632');
  assert.equal(checkGapKind(krow('check', { reductions: true }), pick632, RF(999), 'reduce').kind, 'reduce');
});
test('reduce: a step without reductions: true is refused, with the reason', () => {
  assert.throws(() => checkGapKind(krow(undefined), pick632, RF(1), 'reduce'), /not open to reductions: the desk's row carries no `reductions: true`/);
});
test('reduce: reductions set to anything but true is refused', () => {
  for (const r of ['true', 1, false, null, {}]) assert.throws(() => checkGapKind(krow(undefined, { reductions: r }), pick632, RF(1), 'reduce'), /not open to reductions/);
});
test('reduce: a refutation step is not reduced, even with reductions: true', () => {
  assert.throws(() => checkGapKind(krow('refute', { reductions: true }), pick632, RF(1), 'reduce'), /only a step posted to be proved is reduced/);
});
test('reduce: an R_ file with kind check is refused', () => {
  assert.throws(() => checkGapKind(krow(undefined, { reductions: true }), pick632, RF(1), 'check'), /judged only by a run of kind reduce/);
  assert.throws(() => checkFileKind(RF(1), 'check'), /judged only by a run of kind reduce/);
});
test('reduce: an R_ file with kind refute, or with no kind, is refused', () => {
  assert.throws(() => checkGapKind(krow('refute', { reductions: true }), pick632, RF(1), 'refute'), /judged only by a run of kind reduce/);
  assert.throws(() => checkGapKind(krow(undefined, { reductions: true }), pick632, RF(1)), /judged only by a run of kind reduce/);
});
test('reduce: an L_ file with kind reduce is refused', () => {
  assert.throws(() => checkGapKind(krow(undefined, { reductions: true }), pick632, KF, 'reduce'), /judges only a reduction file/);
  assert.throws(() => checkFileKind(KF, 'reduce'), /judges only a reduction file/);
});
test('reduce: n of 4 digits, 0, or a leading zero is refused', () => {
  for (const n of ['1000', '0', '00', '01', '007']) {
    assert.equal(FILE_RE_R.test(RF(n)), false, n);
    assert.throws(() => checkGapKind(krow(undefined, { reductions: true }), pick632, RF(n), 'reduce'), /the one file must be/, n);
  }
  for (const n of ['1', '10', '999']) assert.equal(FILE_RE_R.test(RF(n)), true, n);
});
test('reduce: an R_ file of ANOTHER step is refused', () => {
  assert.throws(() => checkGapKind(krow(undefined, { reductions: true }), pick632, 'lean/PEqualNP/Outside/R_meta_63_21.lean', 'reduce'), /is not a reduction file of gap L-meta-632/);
  assert.throws(() => checkGapKind(krow(undefined, { reductions: true }), pick632, 'lean/PEqualNP/Outside/R_meta_6321_1.lean', 'reduce'), /is not a reduction file of gap L-meta-632/);
});
test('reduce: an unknown run kind is refused', () => {
  assert.throws(() => checkGapKind(krow(undefined, { reductions: true }), pick632, KF, 'prove'), /must be check, refute or reduce/);
  assert.throws(() => checkGapKind(krow(undefined, { reductions: true }), pick632, KF, ''), /must be check, refute or reduce/);
});
test('reduce: the pull request may add an R_ file (the kind is decided at the gap step)', () => {
  const sha = 'a'.repeat(40), blob = 'b'.repeat(40);
  const pr = { state: 'open', base: { repo: { full_name: 'o/r' }, ref: 'main' }, head: { sha }, user: { login: 'someone' }, changed_files: 1 };
  const r = checkPrR(pr, [{ filename: RF(3), status: 'added', sha: blob }], { tree: [{ path: RF(3), type: 'blob', mode: '100644', sha: blob, size: 10 }] }, 'o/r', 'main');
  assert.equal(r.module, 'PEqualNP.Outside.R_meta_632_3');
  assert.throws(() => checkPrR(pr, [{ filename: RF('0'), status: 'added', sha: blob }], { tree: [] }, 'o/r', 'main'), /the one file must be/);
});
// The own-namespace rule for a reduction file: the theorem alone, under the R_ name.
const RM = 'PEqualNP.Outside.R_meta_632_1';
test('reduce: a reduction file with its one theorem passes the own-namespace rule', () => {
  checkOwnNamespace(`import Mathlib\nopen Nat\ntheorem ${RM} : (1 = 1) → (2 = 2) → True := by\n  intro _ _\n  trivial\n`, RM);
});
test('reduce: a reduction file that opens a namespace is refused', () => {
  assert.throws(() => checkOwnNamespace(`import Mathlib\nnamespace ${RM}\ndef f : ℕ := 1\nend ${RM}\ntheorem ${RM} : (1 = 1) → (2 = 2) → True := fun _ _ => trivial\n`, RM), /a reduction file holds its one theorem/);
});
test('reduce: a reduction file whose theorem has another name is refused', () => {
  assert.throws(() => checkOwnNamespace(`import Mathlib\ntheorem PEqualNP.Outside.L_meta_632 : True := trivial\n`, RM), /line 2: a declaration/);
});
test('reduce: an R_ module of 4 digits is not an outside module', () => {
  assert.throws(() => checkOwnNamespace(`theorem PEqualNP.Outside.R_meta_632_1000 : True := trivial\n`, 'PEqualNP.Outside.R_meta_632_1000'), /is not the module of an outside proof file/);
});
// The command line: the kind travels to the imports and closure commands too.
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, writeFileSync as wf } from 'node:fs';
import { tmpdir } from 'node:os';
import { join as pj } from 'node:path';
const GUARD = new URL('./outside-guard.mjs', import.meta.url).pathname;
const cli = (...args) => spawnSync(process.execPath, [GUARD, ...args], { encoding: 'utf8' });
test('reduce cli: gap with kind reduce writes gap.kind reduce; without reductions it is refused', () => {
  const d = mkdtempSync(pj(tmpdir(), 'guard-reduce-'));
  wf(pj(d, 'open.json'), JSON.stringify(krow(undefined, { reductions: true })));
  wf(pj(d, 'dark.json'), JSON.stringify(krow(undefined)));
  let r = cli('gap', pj(d, 'open.json'), 'L-meta-632', RF(2), d, 'reduce');
  assert.equal(r.status, 0, r.stdout + r.stderr);
  assert.equal(readFileSync(pj(d, 'gap.kind'), 'utf8'), 'reduce\n');
  r = cli('gap', pj(d, 'dark.json'), 'L-meta-632', RF(2), d, 'reduce');
  assert.equal(r.status, 1); assert.match(r.stdout, /^REFUSED: gap L-meta-632 is not open to reductions/);
  r = cli('gap', pj(d, 'open.json'), 'L-meta-632', RF(2), d, 'check');
  assert.equal(r.status, 1); assert.match(r.stdout, /judged only by a run of kind reduce/);
  r = cli('gap-of-file', pj(d, 'open.json'), RF(2), d);
  assert.equal(r.status, 1);
  wf(pj(d, 'imports.json'), '[]');
  wf(pj(d, 'r.lean'), `import Mathlib\ntheorem ${'PEqualNP.Outside.R_meta_632_2'} : (1 = 1) → (2 = 2) → True := fun _ _ => trivial\n`);
  r = cli('imports', pj(d, 'r.lean'), pj(d, 'imports.json'), RF(2), 'reduce');
  assert.equal(r.status, 0, r.stdout + r.stderr);
  r = cli('imports', pj(d, 'r.lean'), pj(d, 'imports.json'), RF(2), 'check');
  assert.equal(r.status, 1); assert.match(r.stdout, /judged only by a run of kind reduce/);
  r = cli('imports', pj(d, 'r.lean'), pj(d, 'imports.json'), RF(2));
  assert.equal(r.status, 1);
  r = cli('closure', d, pj(d, 'imports.json'), RF(2), d, 'reduce');
  assert.equal(r.status, 0, r.stdout + r.stderr);
  r = cli('closure', d, pj(d, 'imports.json'), KF, d, 'reduce');
  assert.equal(r.status, 1); assert.match(r.stdout, /judges only a reduction file/);
});

// A step that left the desk: the refusal says why, from the desk file (checked, or withdrawn with its reason).
import { checkGap as checkGapLeft } from './outside-guard.mjs';
const LF = 'lean/PEqualNP/Outside/L_meta_701.lean';
const leftDesk = { gaps: [{ id: 'L-meta-700', file: 'lean/PEqualNP/Outside/L_meta_700.lean', module: 'PEqualNP.Outside.L_meta_700', statement: 'True', imports: [] }],
  checked: [{ id: 'L-meta-701', file: LF }], withdrawn: { 'L-meta-702': 'restated as L-meta-703 (basis named in the title)' } };
test('a step already checked: the refusal says so', () => { assert.throws(() => checkGapLeft(leftDesk, (x) => x.id === 'L-meta-701', LF), /L-meta-701 is already CHECKED/); });
test('a withdrawn step: the refusal gives the desk reason', () => { assert.throws(() => checkGapLeft(leftDesk, (x) => x.id === 'L-meta-702', 'lean/PEqualNP/Outside/L_meta_702.lean'), /L-meta-702 was WITHDRAWN from the desk \(restated as L-meta-703/); });
test('a step the desk never had: the refusal says it is not on the desk', () => { assert.throws(() => checkGapLeft(leftDesk, (x) => x.id === 'L-meta-799', 'lean/PEqualNP/Outside/L_meta_799.lean'), /not on the desk/); });
test('a withdrawn reason with odd characters is cleaned and cut', () => { const d = { gaps: [], checked: [], withdrawn: { 'L-meta-704': '`$(x)` "q" ' + 'a'.repeat(300) } }; assert.throws(() => checkGapLeft(d, (x) => x.id === 'L-meta-704', 'lean/PEqualNP/Outside/L_meta_704.lean'), (e) => !/[`$"]/.test(e.message) && e.message.length < 400); });

// The checks of the file's text give EVERY problem at once, in file order, one per line (outside
// feedback: one author needed five pushes for five problems). The rules are unchanged.
import { checkProofFile, checkPlain as checkPlainAll, MAX_PROBLEMS, MAX_REFUSAL } from './outside-guard.mjs';
const FIVE = `${head}import Evil.Module\nset_option maxHeartbeats 400000\nprivate def f : ℕ := 1\ndef g : ℕ := sorry\n`;
const fiveSays = ['line 4: import Evil.Module is not allowed', 'line 5: "set_option" is not allowed', 'write it as set_option <option> <value> in',
  'line 6: a declaration or command outside the file\'s own namespace', 'line 7: "sorry" is not allowed', 'the file holds no theorem'];
test('all problems: one file with 5 problems is refused once, naming all 5 with their lines, in file order', () => {
  let msg;
  assert.throws(() => checkProofFile(new TextEncoder().encode(FIVE), ['PEqualNP.Defs'], 'PEqualNP.Outside.L_x_1'), (e) => { msg = e.message; return true; });
  const at = fiveSays.map((w) => msg.indexOf(w));
  assert.ok(at.every((i) => i >= 0), msg);
  assert.deepEqual([...at].sort((a, b) => a - b), at, 'not in file order');
  assert.ok(msg.split('\n').every((l) => !l.startsWith('REFUSED')));
});
test('all problems: the command line prints every problem on its own REFUSED line, the first line as before', () => {
  const d = mkdtempSync(pj(tmpdir(), 'guard-all-'));
  wf(pj(d, 'imports.json'), '["PEqualNP.Defs"]'); wf(pj(d, 'f.lean'), FIVE);
  const r = cli('imports', pj(d, 'f.lean'), pj(d, 'imports.json'), 'lean/PEqualNP/Outside/L_x_1.lean', 'check');
  assert.equal(r.status, 1);
  const lines = r.stdout.trimEnd().split('\n');
  assert.ok(lines.every((l) => l.startsWith('REFUSED: ')), r.stdout);
  assert.match(lines[0], /^REFUSED: line 4: import Evil\.Module is not allowed \(only Mathlib and the modules the gap lists\)$/);
  for (const w of fiveSays) assert.ok(r.stdout.includes(w), w);
  // A file with one problem still gives the one line it gave before.
  wf(pj(d, 'one.lean'), `${head}${thm}  #eval 1\n`);
  const one = cli('imports', pj(d, 'one.lean'), pj(d, 'imports.json'), 'lean/PEqualNP/Outside/L_x_1.lean', 'check');
  assert.equal(one.status, 1);
  assert.equal(one.stdout, 'REFUSED: line 5: "#eval" is not allowed in a proof file, in code or in a comment (no code that runs at build time, no new syntax, no string literals, no attributes but simp, no options but the four limits)\n');
});
test('all problems: the cap, 60 problems give 40 lines and "... and 20 more"', () => {
  assert.equal(MAX_PROBLEMS, 40);
  const body = Array.from({ length: 60 }, (_, k) => `import Evil.M${k}`).join('\n') + `\n${thm}`;
  assert.throws(() => run(body), (e) => {
    const l = e.message.split('\n');
    return l.length === 41 && l[0].startsWith('line 4: import Evil.M0 ') && l[39].startsWith('line 43: import Evil.M39 ') && l[40] === '... and 20 more' && e.message.length <= MAX_REFUSAL;
  });
});
test('all problems: the character cap comes first for long sentences (60 forbidden words: 29 lines, then the count)', () => {
  const body = Array.from({ length: 60 }, () => '-- sorry').join('\n') + `\n${thm}`;
  assert.throws(() => run(body), (e) => {
    const l = e.message.split('\n');
    return e.message.length <= MAX_REFUSAL && l.length < 41 && l.at(-1) === `... and ${60 - (l.length - 1)} more` && l[0].startsWith('line 4: "sorry"');
  });
});
test('all problems: at most 6000 characters, however long each line', () => {
  assert.equal(MAX_REFUSAL, 6000);
  const long = (k) => `namespace N${k}${'a'.repeat(900)}\nend N${k}${'a'.repeat(900)}`;
  const body = Array.from({ length: 30 }, (_, k) => long(k)).join('\n') + `\n${t9}`;
  assert.throws(() => own(M, body), (e) => e.message.length <= MAX_REFUSAL && /\.\.\. and \d+ more$/.test(e.message) && e.message.startsWith('line 4: `namespace N0'));
});
test('all problems: text that cannot be read stops first, alone', () => {
  const bad = new Uint8Array([...new TextEncoder().encode(FIVE), 0xff]);
  assert.throws(() => checkProofFile(bad, [], 'PEqualNP.Outside.L_x_1'), (e) => e.message === 'the file is not UTF-8 text');
  assert.throws(() => checkProofFile(new TextEncoder().encode(`${FIVE}\0`), [], 'PEqualNP.Outside.L_x_1'), (e) => e.message === 'the file holds a NUL byte');
});
test('all problems: control and invisible characters stop first and alone (red team C1)', () => {
  assert.throws(() => checkPlainAll(`-- \u202e\n  #eval 1\n`), (e) => e.message === 'the file holds invisible or direction-changing characters');
  assert.throws(() => checkProofFile(new TextEncoder().encode(`${head}import Evil.X\n-- \u0007\n`), ['PEqualNP.Defs'], 'PEqualNP.Outside.L_x_1'), (e) => e.message === 'the file holds control characters');
  const d = mkdtempSync(pj(tmpdir(), 'guard-ctl-'));
  wf(pj(d, 'imports.json'), '["PEqualNP.Defs"]'); wf(pj(d, 'c.lean'), `${head}import Evil.X\n-- \u0007\n`);
  assert.equal(cli('imports', pj(d, 'c.lean'), pj(d, 'imports.json'), 'lean/PEqualNP/Outside/L_x_1.lean', 'check').stdout, 'REFUSED: the file holds control characters\n');
});
test('all problems: a quoted import name is cut to 60 characters (red team C2)', () => {
  const name = `Evil.${'A'.repeat(195)}`;
  assert.throws(() => run(`import ${name}\n${thm}`), (e) => e.message === `line 4: import ${name.slice(0, 60)} is not allowed (only Mathlib and the modules the gap lists)`);
});
test('all problems: a quoted name outside letters, digits, dot, underscore and apostrophe is sanitised (red team C2)', () => {
  assert.throws(() => own(M, `namespace Δέλτα.x₁\nend Δέλτα.x₁\n${t9}`), (e) => e.message.startsWith('line 4: `namespace ?????.x?` at the top level') && !/[^\x20-\x7e\n]/.test(e.message));
  assert.throws(() => own(M, `namespace ${M}\nend Ωmega\n${t9}`), (e) => e.message.includes('`end ?mega` does not name what it closes'));
});
test('all problems: no line is longer than 400 characters', () => {
  const body = Array.from({ length: 30 }, (_, k) => `namespace N${k}${'a'.repeat(900)}\nend N${k}${'a'.repeat(900)}`).join('\n') + `\n${t9}`;
  assert.throws(() => own(M, body), (e) => e.message.split('\n').every((l) => l.length <= 400));
});
test('all problems: a listed outside module names every problem too', () => {
  assert.throws(() => closure(['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': `import Mathlib\ninitialize pure ()\n#eval 1\n${thm}` }),
    (e) => e.message.startsWith('the listed outside module PEqualNP.Outside.L_x_2: line 2: "initialize"') && e.message.includes('\nline 3: "#eval"'));
});
test('a matched word that is not one of the listed literals is still sanitised', () => {
  assert.throws(() => run(`${thm}  #zz_q 1\n`), (e) => e.message.startsWith('line 5: "?zz_q" is not allowed'));
  // (a single character before % is the remainder operator since sign 91; the sanitising is shown on a longer name)
  assert.throws(() => run(`${thm}  exact xy% y\n`), (e) => e.message.startsWith('line 5: "xy?" is not allowed'));
  assert.throws(() => run(`${thm}  exact \x60(foo| y)\n`), (e) => e.message.startsWith('line 5: "??foo?" is not allowed'));
  assert.throws(() => run(`${thm}  exact \x60(tactic| y)\n`), (e) => e.message.startsWith('line 5: "\x60(tactic|" is not allowed'));
});
test('the bv_decide refusal says what to use instead (a repeated honest mistake)', () => {
  assert.throws(() => checkPlainAll(`theorem PEqualNP.Outside.L_x : True := by\n  bv_decide\n`), (e) => /bv_decide runs a SAT solver as the file builds, so use tactics the kernel checks alone, e\.g\. decide \(small sizes\), simp, omega, rfl$/.test(e.message));
});
// More than one file: the refusal carries the fixed sentence the contributor can act on (red team, 2026-11-24: a repeated honest mistake).
test('more than one file: the refusal says to send each step as its own pull request', () => {
  const sha = 'a'.repeat(40), blob = 'b'.repeat(40);
  const two = [{ filename: RF(3), status: 'added', sha: blob }, { filename: RF(4), status: 'added', sha: blob }];
  const pr = n => ({ state: 'open', base: { repo: { full_name: 'o/r' }, ref: 'main' }, head: { sha }, user: { login: 'someone' }, changed_files: n });
  const SAY = /one file per pull request, so send each step as its own pull request/;
  assert.throws(() => checkPrR(pr(2), two, { tree: [] }, 'o/r', 'main'), SAY);
  assert.throws(() => checkPrR(pr(7), two, { tree: [] }, 'o/r', 'main'), /changes 7 files; one file per pull request, so/);
  // the count says one, the list says two: still the sentence
  assert.throws(() => checkPrR(pr(1), two, { tree: [] }, 'o/r', 'main'), SAY);
  // no file is not "more than one": the old text, no sentence
  assert.throws(() => checkPrR(pr(0), [], { tree: [] }, 'o/r', 'main'), e => /must add exactly one/.test(e.message) && !SAY.test(e.message));
});
// The % rule (red team sign 91, 2026-11-24): the remainder operator after a single character or a number is plain;
// a name of two or more characters straight before % (a library term macro such as eval%) is refused.
test('the remainder operator after one character or a number is plain; a longer name before % is refused', () => {
  const T = (body) => `theorem PEqualNP.Outside.L_x : True := by\n  ${body}\n  trivial\n`;
  for (const ok of ['have h : n%2 = n % 2 := rfl', 'have h : (k%m) = k % m := rfl', 'have h : 10%3 = 1 := rfl', 'have h : (a+b)%2 = (a+b)%2 := rfl'])
    checkPlainAll(T(ok));
  for (const bad of ['have h := eval% (1 + 1)', 'have h := type_of% x', 'have h : ab%2 = 0 := sorry', 'have h := x1%y', 'have h := decl_name%'])
    assert.throws(() => checkPlainAll(T(bad)), /is not allowed|sorry/, bad);
});

// A VALUE STEP: the desk's row carries a template and a bound, and the statement judged is the
// template with the file name's k put in. One fixture per way a wrong k could be judged, refused.
import { checkGap as checkGapValue, checkFileKind as checkFileKindV, checkPr as checkPrV, valueGap, rowOfFile, FILE_RE as FILE_RE_V, V_FILE_RE, VALUE_RE } from './outside-guard.mjs';
const VT = 'Size.AtMost f @@VALUE@@ ∧\n  ¬ Size.AtMost f (@@VALUE@@ - 1)';
const VF = (k, gap = 'meta_700') => `lean/PEqualNP/Outside/V_${gap}__k${k}.lean`;
const vrow = (more = {}) => ({ gaps: [{ id: 'L-meta-700', kind: 'value', template: VT, value_holes: 2, value_max: 12, imports: ['PEqualNP.Defs'], ...more },
  { id: 'L-meta-70', kind: 'value', template: VT, value_holes: 2, value_max: 99, imports: [] }, { id: 'L-meta-632', file: KF, module: 'PEqualNP.Outside.L_meta_632', statement: 'True', imports: [] }] });
const pick700 = (x) => x.id === 'L-meta-700';
test('value: the statement is the template with k put in, every occurrence, byte for byte; the kind is check', () => {
  const g = checkGapValue(vrow(), pick700, VF(6), 'check');
  assert.equal(g.statement, 'Size.AtMost f 6 ∧\n  ¬ Size.AtMost f (6 - 1)');
  assert.equal(g.kind, 'check'); assert.equal(g.value, 6); assert.deepEqual(g.imports, ['PEqualNP.Defs']);
  assert.equal(checkGapValue(vrow(), pick700, VF(0), 'check').statement, 'Size.AtMost f 0 ∧\n  ¬ Size.AtMost f (0 - 1)');
  assert.equal(checkGapValue(vrow(), pick700, VF(12)).value, 12, 'the bound itself is a value');
});
test('value E1: the numeral is plain ASCII digits, no leading zero, at most the bound', () => {
  for (const ok of ['0', '6', '12', '9999']) assert.ok(VALUE_RE.test(ok), ok);
  for (const bad of ['06', '00', '+6', '-6', '6_0', '0x6', '６', '٦', '6.0', '1e1', '', '10000', ' 6']) {
    assert.ok(!VALUE_RE.test(bad), bad);
    assert.throws(() => checkGapValue(vrow(), pick700, VF(bad), 'check'), /the one file must be|not a value file/, `a file named for "${bad}"`);
  }
  assert.throws(() => checkGapValue(vrow(), pick700, VF(13), 'check'), /the value 13 is above the bound of gap L-meta-700: no value above 12 is judged/);
  assert.throws(() => checkGapValue(vrow({ value_max: '12' }), pick700, VF(6), 'check'), /malformed value_max/);
  assert.throws(() => checkGapValue(vrow({ value_max: undefined }), pick700, VF(6), 'check'), /malformed value_max/);
});
test('value E2: the file name is rebuilt from the gap and k and compared byte for byte', () => {
  assert.throws(() => checkGapValue(vrow(), pick700, VF(6, 'meta_70'), 'check'), /is not the file of value 6 of gap L-meta-700 \(that is lean\/PEqualNP\/Outside\/V_meta_700__k6\.lean\)/);
  assert.throws(() => checkGapValue(vrow(), pick700, VF(6, 'meta_7000'), 'check'), /is not the file of value 6 of gap L-meta-700/);
  // A name that could be cut two ways if k were parsed out of it: the step 70 at "0__k6" is not a name at all.
  assert.throws(() => checkGapValue(vrow(), pick700, 'lean/PEqualNP/Outside/V_meta_70__k0__k6.lean', 'check'), /is not the file of value 6 of gap L-meta-700/);
  assert.throws(() => checkGapValue(vrow(), (x) => x.id === 'L-meta-70', 'lean/PEqualNP/Outside/V_meta_70__k0__k6.lean', 'check'), /is not the file of value 6 of gap L-meta-70 /);
  assert.throws(() => checkGapValue(vrow(), pick700, 'lean/PEqualNP/Outside/V_meta_700_k6.lean', 'check'), /the one file must be/, 'a single underscore is not the separator');
  assert.throws(() => checkGapValue(vrow(), pick700, 'lean/PEqualNP/Outside/L_meta_700.lean', 'check'), /is a value step, and .* is not a value file/);
  assert.throws(() => checkGapValue(vrow(), pick700, 'lean/PEqualNP/Outside/R_meta_700_1.lean', 'reduce'), /is a value step; it is judged only by a run of kind check/);
});
test('value E3: the token count is the count stored at posting, each a whole term, and nothing else with at-signs', () => {
  assert.throws(() => checkGapValue(vrow({ value_holes: 1 }), pick700, VF(6), 'check'), /holds @@VALUE@@ 2 time\(s\), and the step was posted with 1/);
  assert.throws(() => checkGapValue(vrow({ template: 'Size.AtMost f @@VALUE@@' }), pick700, VF(6), 'check'), /holds @@VALUE@@ 1 time\(s\), and the step was posted with 2/);
  assert.throws(() => checkGapValue(vrow({ template: 'Size.AtMost f VALUE', value_holes: 1 }), pick700, VF(6), 'check'), /holds @@VALUE@@ 0 time/, 'a bare word is never the token');
  assert.throws(() => checkGapValue(vrow({ value_holes: 0, template: 'True' }), pick700, VF(6), 'check'), /malformed value_holes/);
  assert.throws(() => checkGapValue(vrow({ template: 'Size.AtMost f x@@VALUE@@ ∧ g @@VALUE@@' }), pick700, VF(6), 'check'), /where it is not a whole term/);
  assert.throws(() => checkGapValue(vrow({ template: 'Size.AtMost f @@VALUE@@1 ∧ g @@VALUE@@' }), pick700, VF(6), 'check'), /where it is not a whole term/, 'a digit glued to the hole would make another number');
  assert.throws(() => checkGapValue(vrow({ template: 'Size.AtMost f @@VALUE@@ ∧ g @@VALUE@@ ∧ h @@ i' }), pick700, VF(6), 'check'), /a doubled at-sign that is not @@VALUE@@/);
  assert.throws(() => checkGapValue(vrow({ template: undefined }), pick700, VF(6), 'check'), /a value step with no template/);
  assert.throws(() => checkGapValue(vrow({ template: 'a @@VALUE@@ \0 @@VALUE@@' }), pick700, VF(6), 'check'), /a value step with no template/);
});
test('value: a value file is judged only for a value step, and only as a check', () => {
  assert.throws(() => checkGapValue(vrow(), pick632, 'lean/PEqualNP/Outside/V_meta_632__k6.lean', 'check'), /is a value file, and the desk does not post gap L-meta-632 as a value step/);
  assert.throws(() => checkGapValue(vrow(), pick700, VF(6), 'refute'), /judged only by a run of kind check/);
  assert.throws(() => checkGapValue(vrow(), pick700, VF(6), 'reduce'), /judged only by a run of kind check/);
  assert.throws(() => checkFileKindV(VF(6), 'refute'), /is a value file/);
  assert.equal(checkFileKindV(VF(6), 'check'), VF(6));
  assert.throws(() => valueGap(vrow().gaps[0], VF(6), 'refute'), /judged only by a run of kind check/);
  assert.throws(() => checkGapValue(vrow({ imports: ['Mathlib.Evil'] }), pick700, VF(6), 'check'), /lists a malformed import/);
});
test('value: land-by-push does not take a value file (FILE_RE is unchanged), the pull request step does', () => {
  assert.ok(!FILE_RE_V.test(VF(6)) && V_FILE_RE.test(VF(6)));
  const sha = 'a'.repeat(40), blob = 'b'.repeat(40);
  const pr = { state: 'open', base: { repo: { full_name: 'o/r' }, ref: 'main' }, head: { sha }, user: { login: 'someone' }, changed_files: 1 };
  const r = checkPrV(pr, [{ filename: VF(6), status: 'added', sha: blob }], { tree: [{ path: VF(6), type: 'blob', mode: '100644', sha: blob, size: 10 }] }, 'o/r', 'main');
  assert.equal(r.module, 'PEqualNP.Outside.V_meta_700__k6');
  assert.throws(() => checkPrV(pr, [{ filename: VF('06'), status: 'added', sha: blob }], { tree: [] }, 'o/r', 'main'), /the one file must be/);
});
test('value: a settled value step is in the checked list, so a later file for any k is told so; a withdrawn one too', () => {
  const settled = { gaps: [], checked: [{ id: 'L-meta-700', file: VF(6), file_sha256: 'c'.repeat(64) }], withdrawn: { 'L-meta-701': 'settled' } };
  assert.throws(() => checkGapValue(settled, pick700, VF(7), 'check'), /L-meta-700 is already CHECKED/);
  assert.throws(() => checkGapValue(settled, (x) => x.id === 'L-meta-701', VF(7, 'meta_701'), 'check'), /L-meta-701 was WITHDRAWN from the desk \(settled\)/);
});
test('value: the file of a value step finds its row without a gap id; the own-namespace rule takes the V_ name', () => {
  assert.equal(checkGapValue(vrow(), rowOfFile(VF(6)), VF(6)).id, 'L-meta-700');
  assert.equal(checkGapValue(vrow(), rowOfFile(VF(6, 'meta_70')), VF(6, 'meta_70')).id, 'L-meta-70');
  assert.throws(() => checkGapValue(vrow(), rowOfFile(VF(6, 'meta_7')), VF(6, 'meta_7')), /the step is not on the desk/);
  const VM = 'PEqualNP.Outside.V_meta_700__k6';
  checkOwnNamespace(`import Mathlib\nimport PEqualNP.Defs\nnamespace ${VM}\ntheorem up : True := trivial\nend ${VM}\ntheorem ${VM} : True := trivial\n`, VM);
  assert.throws(() => checkOwnNamespace(`import Mathlib\ntheorem PEqualNP.Outside.V_meta_700__k7 : True := trivial\n`, VM), /line 2: a declaration/, 'the theorem carries the file\'s own k');
  assert.throws(() => checkOwnNamespace('theorem X : True := trivial\n', 'PEqualNP.Outside.V_meta_700__k06'), /is not the module of an outside proof file/);
});
test('value cli: gap writes the instance to statement.txt and check to gap.kind; a wrong name writes nothing', () => {
  const d = mkdtempSync(pj(tmpdir(), 'guard-value-'));
  wf(pj(d, 'gaps.json'), JSON.stringify(vrow()));
  let r = cli('gap', pj(d, 'gaps.json'), 'L-meta-700', VF(6), d, 'check');
  assert.equal(r.status, 0, r.stdout + r.stderr);
  assert.equal(readFileSync(pj(d, 'statement.txt'), 'utf8'), 'Size.AtMost f 6 ∧\n  ¬ Size.AtMost f (6 - 1)');
  assert.equal(readFileSync(pj(d, 'gap.kind'), 'utf8'), 'check\n');
  assert.equal(readFileSync(pj(d, 'gap.id'), 'utf8'), 'L-meta-700\n');
  const e = mkdtempSync(pj(tmpdir(), 'guard-value-'));
  r = cli('gap', pj(d, 'gaps.json'), 'L-meta-700', VF(13), e, 'check');
  assert.equal(r.status, 1); assert.match(r.stdout, /^REFUSED: the value 13 is above the bound/);
  assert.throws(() => readFileSync(pj(e, 'statement.txt')));
  r = cli('gap-of-file', pj(d, 'gaps.json'), VF(4), e);
  assert.equal(r.status, 0, r.stdout + r.stderr);
  assert.equal(readFileSync(pj(e, 'statement.txt'), 'utf8'), 'Size.AtMost f 4 ∧\n  ¬ Size.AtMost f (4 - 1)');
  wf(pj(d, 'imports.json'), '["PEqualNP.Defs"]');
  wf(pj(d, 'v.lean'), 'import Mathlib\nimport PEqualNP.Defs\ntheorem PEqualNP.Outside.V_meta_700__k6 : True := trivial\n');
  r = cli('imports', pj(d, 'v.lean'), pj(d, 'imports.json'), VF(6), 'check');
  assert.equal(r.status, 0, r.stdout + r.stderr);
  r = cli('imports', pj(d, 'v.lean'), pj(d, 'imports.json'), VF(6), 'reduce');
  assert.equal(r.status, 1); assert.match(r.stdout, /is a value file/);
});

// THE STEP'S ROW BY ID (25 Nov): both workflows fetch the desk's row for the one gap from one account-bound address,
// never the whole list and never through pequalnp.com's DNS, and the advisory's id is the one its file belongs to.
import { GAP_RE as GAP_RE_ROW, rowOfFile as rowOfFileRow } from './outside-guard.mjs';
test('both workflows: the row by id from the one desk address, and the advisory id names the file\'s row', () => {
  const wfs = ['authoritative.yml', 'advisory.yml'].map((n) => [n, readFileSync(new URL(`../workflows/${n}`, import.meta.url), 'utf8')]);
  const urls = wfs.map(([n, wf]) => {
    assert.doesNotMatch(wf, /data\.pequalnp\.com|gaps\.json"? *"\$GAPS_URL|GAPS_URL/, `${n}: still fetches the whole list`);
    const m = wf.match(/^\s+ROW_URL: (\S+)$/m); assert.ok(m, `${n}: no ROW_URL`);
    assert.equal(wf.match(/curl [^\n]*\$ROW_URL/g)?.length, 1, `${n}: fetches the row other than once`);
    return m[1];
  });
  assert.equal(urls[0], urls[1], 'the two workflows read different desks');
  assert.equal(urls[0], 'https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=');
  assert.match(wfs[0][1], /curl [^\n]*--max-redirs 0[^\n]*"\$ROW_URL\$GAP"/);
  const line = wfs[1][1].match(/^\s+(gap="L-\$\(basename "\$FILE" \.lean \| cut -c3- \| tr _ -\)")$/m); assert.ok(line, 'advisory: no gap line');
  assert.match(wfs[1][1], /curl [^\n]*--max-redirs 0[^\n]*"\$ROW_URL\$gap"/);
  for (const id of ['L-meta-632', 'L-gct-101', 'L-x-0', 'L-clb-034']) {
    const file = `lean/PEqualNP/Outside/${id.replace(/-/g, '_')}.lean`;
    const r = spawnSync('sh', ['-c', `${line[1]}; printf %s "$gap"`], { env: { PATH: process.env.PATH, FILE: file }, encoding: 'utf8' });
    assert.equal(r.stdout, id); assert.ok(GAP_RE_ROW.test(r.stdout));
    assert.ok(rowOfFileRow(file)({ id, file }), `${file} is not the row of ${id}`);
  }
});

// THE GUARD MUST SHOW ITS WORK (2026-11-26, the operator's order, security first; redteam-1's spec, section 4).
// (a) main is decided by REAL path, so a symlinked call or a path with '#' or a space runs the checks; a run that
//     names the guard but is not main is a FAULT (exit 3), never a silent 0. (b) every mode ends on GUARD OK: <mode>.
import { cpSync, mkdirSync, symlinkSync } from 'node:fs';
import { ranAsScript } from './outside-guard.mjs';
{
  const okLine = (r, mode) => { assert.equal(r.status, 0, r.stdout + r.stderr); assert.equal(r.stdout.trimEnd().split('\n').at(-1), `GUARD OK: ${mode}`); };
  const fixtures = (d) => {
    wf(pj(d, 'row.json'), JSON.stringify(krow(undefined)));
    wf(pj(d, 'imports.json'), '[]');
    wf(pj(d, 'clean.lean'), 'import Mathlib\ntheorem PEqualNP.Outside.L_meta_632 : True := trivial\n');
    wf(pj(d, 'evil.lean'), 'import Mathlib\n#eval 1\ntheorem PEqualNP.Outside.L_meta_632 : True := trivial\n');
    const sha = 'a'.repeat(40), blob = 'b'.repeat(40);
    wf(pj(d, 'pr.json'), JSON.stringify({ state: 'open', base: { repo: { full_name: 'o/r' }, ref: 'main' }, head: { sha }, user: { login: 'someone' }, changed_files: 1 }));
    wf(pj(d, 'files.json'), JSON.stringify([{ filename: KF, status: 'added', sha: blob }]));
    wf(pj(d, 'tree.json'), JSON.stringify({ truncated: false, tree: [{ path: KF, type: 'blob', mode: '100644', sha: blob, size: 60 }] }));
    mkdirSync(pj(d, 'out'), { recursive: true });
  };
  const every = (call, d) => {
    okLine(call('pr', pj(d, 'pr.json'), pj(d, 'files.json'), pj(d, 'tree.json'), 'o/r', 'main', pj(d, 'out')), 'pr');
    okLine(call('gap', pj(d, 'row.json'), 'L-meta-632', KF, pj(d, 'out'), 'check'), 'gap');
    okLine(call('gap-of-file', pj(d, 'row.json'), KF, pj(d, 'out')), 'gap-of-file');
    okLine(call('imports', pj(d, 'clean.lean'), pj(d, 'imports.json'), KF, 'check'), 'imports');
    okLine(call('closure', d, pj(d, 'imports.json'), KF, pj(d, 'out'), 'check'), 'closure');
    const bad = call('imports', pj(d, 'evil.lean'), pj(d, 'imports.json'), KF, 'check');
    assert.equal(bad.status, 1); assert.match(bad.stdout, /^REFUSED: /); assert.doesNotMatch(bad.stdout, /GUARD OK/);
  };
  test('guard shows its work: every mode ends on GUARD OK: <mode>, and a refusal never does', () => {
    const d = mkdtempSync(pj(tmpdir(), 'guard-ok-')); fixtures(d); every(cli, d);
  });
  for (const [name, dirName] of [['a symlinked path', null], ['a path with a hash sign', 'a#b'], ['a path with a space', 'a b']]) {
    test(`guard shows its work: called through ${name}, the checks run (no silent 0)`, () => {
      const d = mkdtempSync(pj(tmpdir(), 'guard-path-')); fixtures(d);
      let g;
      if (dirName === null) { g = pj(d, 'linked-guard.mjs'); symlinkSync(GUARD, g); }
      else { mkdirSync(pj(d, dirName)); g = pj(d, dirName, 'outside-guard.mjs'); cpSync(GUARD, g); }
      every((...args) => spawnSync(process.execPath, [g, ...args], { encoding: 'utf8' }), d);
    });
  }
  test('guard shows its work: through a symlinked FOLDER as well (the Mac /tmp case)', () => {
    const d = mkdtempSync(pj(tmpdir(), 'guard-dirlink-')); fixtures(d);
    mkdirSync(pj(d, 'real')); cpSync(GUARD, pj(d, 'real', 'outside-guard.mjs')); symlinkSync(pj(d, 'real'), pj(d, 'link'));
    every((...args) => spawnSync(process.execPath, [pj(d, 'link', 'outside-guard.mjs'), ...args], { encoding: 'utf8' }), d);
  });
  test('guard shows its work: a run that names the guard but does not reach main is a FAULT, exit 3', () => {
    const d = mkdtempSync(pj(tmpdir(), 'guard-skip-')); mkdirSync(pj(d, 'w'));
    wf(pj(d, 'w', 'outside-guard.mjs'), `import ${JSON.stringify(GUARD)};\n`);   // another file of that name that only imports it
    const r = spawnSync(process.execPath, [pj(d, 'w', 'outside-guard.mjs'), 'imports', 'x', 'y', KF], { encoding: 'utf8' });
    assert.equal(r.status, 3); assert.match(r.stdout, /^FAULT: the guard was started but did not run its checks/); assert.doesNotMatch(r.stdout, /GUARD OK/);
  });
  test('guard shows its work: ranAsScript compares real paths and is false when imported', () => {
    const d = mkdtempSync(pj(tmpdir(), 'guard-ras-')); symlinkSync(GUARD, pj(d, 'l.mjs'));
    const url = new URL(`file://${GUARD}`).href;
    assert.equal(ranAsScript(url, pj(d, 'l.mjs')), true);
    assert.equal(ranAsScript(url, pj(d, 'missing.mjs')), false);
    assert.equal(ranAsScript(url, undefined), false);
  });
}

// THE NUMBER OF A REDUCTION (2026-11-26): k free on the base and in EARLIER open pull requests, else refused
// at the door with the smallest free k named. Later and stale open pull requests do not count.
import { checkCutNumber, STALE_HOURS, MAX_HELD } from './outside-guard.mjs';
import { createHash } from 'node:crypto';
{
  const F = (k) => `lean/PEqualNP/Outside/R_meta_4013_${k}.lean`;
  const now = Date.parse('2026-11-26T03:00:00Z');
  const ago = (h) => new Date(now - h * 3600e3).toISOString();
  const base = ['R_meta_4013_1.lean', 'R_meta_4013_2.lean', 'L_meta_4013.lean', 'R_meta_40130_3.lean'];
  const say = (re) => (e) => re.test(e.message) && !e.message.includes(':');
  test('cut number: a free k passes', () => assert.deepEqual(checkCutNumber(F(3), base, [], 500, now), { k: 3 }));
  test('cut number: a k on the base is refused and names the smallest free one', () =>
    assert.throws(() => checkCutNumber(F(2), base, [], 500, now), say(/number 2 of this step is already a file on main.*R_meta_4013_3\.lean.*PEqualNP\.Outside\.R_meta_4013_3/)));
  test('cut number: another step with a longer id does not count (R_meta_40130_3 is not R_meta_4013_3)', () =>
    assert.deepEqual(checkCutNumber(F(3), base, [], 500, now), { k: 3 }));
  test('cut number: an earlier open pull request holding k refuses, and its other numbers are skipped', () =>
    assert.throws(() => checkCutNumber(F(3), base, [{ number: 400, createdAt: ago(1), files: [F(3)] }, { number: 450, createdAt: ago(1), files: [F(4)] }], 500, now),
      say(/earlier open pull request.*R_meta_4013_5\.lean/)));
  test('cut number: a LATER open pull request holding k does not refuse this one (the earlier keeps it)', () =>
    assert.deepEqual(checkCutNumber(F(3), base, [{ number: 600, createdAt: ago(1), files: [F(3)] }], 500, now), { k: 3 }));
  test('cut number: the pull request itself does not count', () =>
    assert.deepEqual(checkCutNumber(F(3), base, [{ number: 500, createdAt: ago(1), files: [F(3)] }], 500, now), { k: 3 }));
  test(`cut number: an open pull request older than ${STALE_HOURS} hours stops counting`, () =>
    assert.deepEqual(checkCutNumber(F(3), base, [{ number: 400, createdAt: ago(STALE_HOURS + 1), files: [F(3)] }], 500, now), { k: 3 }));
  test('cut number: an entry with no time or a malformed number is ignored, not trusted', () =>
    assert.deepEqual(checkCutNumber(F(3), base, [{ number: 400, files: [F(3)] }, { number: '400', createdAt: ago(1), files: [F(3)] }, null], 500, now), { k: 3 }));
  test('cut number: a proof file (L_) is not looked at', () => assert.equal(checkCutNumber('lean/PEqualNP/Outside/L_meta_4013.lean', base, [], 500, now), null));
  test('cut number: every number in use says so', () => {
    const all = Array.from({ length: 999 }, (_, i) => `R_meta_4013_${i + 1}.lean`);
    assert.throws(() => checkCutNumber(F(7), all, [], 500, now), say(/every number from 1 to 999 is in use/));
  });
  test(`cut number: one account holds at most ${MAX_HELD} numbers of a step (10 open pull requests block 3)`, () => {
    const ten = Array.from({ length: 10 }, (_, i) => ({ number: 100 + i, createdAt: ago(1), author: 'hoarder', files: [F(i + 3)] }));   // claims 3..12
    assert.throws(() => checkCutNumber(F(5), base, ten, 500, now), say(/earlier open pull request.*R_meta_4013_6\.lean/));   // 3, 4, 5 count
    assert.deepEqual(checkCutNumber(F(6), base, ten, 500, now), { k: 6 });   // the fourth claim holds nothing
    assert.deepEqual(checkCutNumber(F(12), base, ten, 500, now), { k: 12 });
    const two = [...ten, { number: 120, createdAt: ago(1), author: 'other', files: [F(6)] }];
    assert.throws(() => checkCutNumber(F(6), base, two, 500, now), say(/earlier open pull request.*R_meta_4013_7\.lean/));   // another account's claim counts
  });
  test('cut number: unreadable lists refuse', () => assert.throws(() => checkCutNumber(F(3), null, [], 500, now), /could not be read/));
  test('cut number: the command line, on a real base folder', () => {
    const d = mkdtempSync(pj(tmpdir(), 'cutnum-')); const o = pj(d, 'lean', 'PEqualNP', 'Outside');
    spawnSync('mkdir', ['-p', o]); wf(pj(o, 'R_meta_4013_1.lean'), ''); wf(pj(d, 'open.json'), JSON.stringify([{ number: 10, createdAt: new Date().toISOString(), files: [F(2)] }]));
    const r1 = cli('number', F(1), d, pj(d, 'open.json'), '20');
    assert.equal(r1.status, 1); assert.match(r1.stdout, /^REFUSED: the reduction number 1 of this step is already a file on main.*R_meta_4013_3\.lean/);
    const r2 = cli('number', F(3), d, pj(d, 'open.json'), '20');
    assert.equal(r2.status, 0); assert.match(r2.stdout, /number 3 is free/); assert.equal(r2.stdout.trimEnd().split('\n').at(-1), 'GUARD OK: number');
    const r3 = cli('number', 'lean/PEqualNP/Outside/L_meta_4013.lean', d, pj(d, 'open.json'), '20');
    assert.equal(r3.status, 1); assert.match(r3.stdout, /^REFUSED: the number check is for a reduction file/); assert.doesNotMatch(r3.stdout, /GUARD OK/);
    assert.equal(cli('number', F(3), d, pj(d, 'open.json'), 'x').status, 1);
  });
  // THE OPEN CLAIMS FROM THE INTAKE (2026-11-26): the workflow's own lines for a reduction run, run here on a real
  // base folder. No list call: the claims are the input open_claims. Absent or malformed is a FAULT, never a pass.
  test('cut number: the open claims input, absent and malformed FAULT, a claimed k refused, a free k passes', () => {
    const wfl = readFileSync(new URL('../workflows/authoritative.yml', import.meta.url), 'utf8');
    assert.doesNotMatch(wfl, /graphql|pullRequests\(/, 'a list call is still made');
    const lines = wfl.split('\n'); const i = lines.findIndex((l) => l.includes('[ -n "$OPEN_CLAIMS" ]')); const j = lines.findIndex((l) => l.includes('cat "$W/api/claims.out"'));
    assert.ok(i > 0 && j > i, 'the open claims lines are not in the workflow'); const block = lines.slice(i, j + 1).join('\n');
    const W = mkdtempSync(pj(tmpdir(), 'claims-')); spawnSync('mkdir', ['-p', pj(W, 'base', '.github'), pj(W, 'api'), pj(W, 'base', 'lean', 'PEqualNP', 'Outside')]);
    spawnSync('ln', ['-s', new URL('.', import.meta.url).pathname, pj(W, 'base', '.github', 'scripts')]);
    wf(pj(W, 'base', 'lean', 'PEqualNP', 'Outside', 'R_meta_4013_1.lean'), '');
    const run = (claims, k = 3) => {
      spawnSync('rm', ['-f', pj(W, 'api', 'open.json')]); wf(pj(W, 'pr.file'), F(k));
      return spawnSync('bash', ['-euc', `mkdir -p "$W/in"; cp "$W/pr.file" "$W/in/pr.file"\n${block}`], { encoding: 'utf8', env: { PATH: process.env.PATH, W, OPEN_CLAIMS: claims } });
    };
    const last = (r) => r.stdout.trimEnd().split('\n').at(-1);
    const recent = new Date(Date.now() - 3600e3).toISOString();
    const h = (login) => createHash('sha256').update(login.toLowerCase()).digest('hex').slice(0, 12);   // the intake's author hash
    let r = run('');
    assert.equal(r.status, 1); assert.equal(last(r), 'FAULT: a reduction run needs the open claims from the intake (input open_claims) and none came; nothing was judged');
    // C1: a quote, a dollar sign, a backtick and a newline: the fixed FAULT line, and nothing of it runs
    r = run(`"'; touch "$W/pwned1"; $(touch "$W/pwned2") \`touch "$W/pwned3"\`\n[]`);
    assert.equal(r.status, 1); assert.equal(last(r), 'FAULT: the open claims from the intake are malformed; nothing was judged');
    for (const n of [1, 2, 3]) assert.throws(() => readFileSync(pj(W, `pwned${n}`)), `the input ran a command (${n})`);
    for (const bad of ['not json', '{}', JSON.stringify([{ number: 400, createdAt: recent, author: h('a'), files: ['lean/PEqualNP/Outside/R_meta_40130_3.lean'] }]),
      JSON.stringify([{ number: 400, createdAt: recent, author: 'someone', files: [F(3)] }]), JSON.stringify([{ number: 400, createdAt: recent, author: h('a').toUpperCase(), files: [F(3)] }]),
      JSON.stringify([{ number: 400, createdAt: recent, author: createHash('sha256').update('a').digest('hex'), files: [F(3)] }]),
      JSON.stringify([{ number: '400', createdAt: recent, author: h('a'), files: [F(3)] }]), JSON.stringify([{ number: 400, createdAt: recent, author: h('a'), files: [F(3)], extra: 1 }]),
      JSON.stringify([{ number: 400, createdAt: 'yesterday', author: h('a'), files: [F(3)] }]), JSON.stringify([{ number: 400, createdAt: recent, author: h('a'), files: [] }]), 'x'.repeat(40001)]) {
      r = run(bad);
      assert.equal(r.status, 1, bad.slice(0, 80)); assert.match(last(r), /^FAULT: the open claims from the intake (are malformed|are longer than 40000 characters); nothing was judged$/, bad.slice(0, 80));
      assert.throws(() => readFileSync(pj(W, 'api', 'open.json')), 'a refused list was written');
    }
    const claims = JSON.stringify([{ number: 400, createdAt: recent, author: h('a'), files: [F(3)] }, { number: 600, createdAt: recent, author: null, files: [F(4)] }]);
    r = run(claims, 3);
    assert.equal(r.status, 0, r.stdout + r.stderr); assert.equal(last(r), 'GUARD OK: claims');
    const g = cli('number', F(3), pj(W, 'base'), pj(W, 'api', 'open.json'), '500');
    assert.equal(g.status, 1); assert.match(g.stdout, /^REFUSED: the reduction number 3 of this step is the file of an earlier open pull request.*R_meta_4013_2\.lean/);
    r = run(claims, 5); assert.equal(r.status, 0, r.stdout);
    assert.equal(cli('number', F(5), pj(W, 'base'), pj(W, 'api', 'open.json'), '500').status, 0, 'a free k did not pass');
    r = run('[]', 3); assert.equal(r.status, 0, r.stdout); assert.equal(readFileSync(pj(W, 'api', 'open.json'), 'utf8'), '[]');
    // three numbers per account with 12-hex authors: one hash on 2..5 holds 2, 3, 4; another hash's claim on 5 counts
    const four = [2, 3, 4, 5].map((k, n) => ({ number: 100 + n, createdAt: recent, author: h('Hoarder'), files: [F(k)] }));
    r = run(JSON.stringify(four), 5); assert.equal(r.status, 0, r.stdout);
    assert.equal(cli('number', F(5), pj(W, 'base'), pj(W, 'api', 'open.json'), '500').status, 0, 'a fourth claim of one account held a number');
    assert.match(cli('number', F(4), pj(W, 'base'), pj(W, 'api', 'open.json'), '500').stdout, /^REFUSED: the reduction number 4 of this step is the file of an earlier open pull request/);
    r = run(JSON.stringify([...four, { number: 104, createdAt: recent, author: h('other'), files: [F(5)] }]), 5); assert.equal(r.status, 0, r.stdout);
    assert.match(cli('number', F(5), pj(W, 'base'), pj(W, 'api', 'open.json'), '500').stdout, /^REFUSED: the reduction number 5 of this step is the file of an earlier open pull request/);
    // the bound: 100 open pull requests of one step, the longest step id, fit the 40000 characters
    const stem = `R_${'a'.repeat(62)}`; const worst = Array.from({ length: 100 }, (_, n) => ({ number: 9000000 + n, createdAt: '2026-11-26T12:00:00.000Z', author: 'f'.repeat(12), files: [`lean/PEqualNP/Outside/${stem}_999.lean`] }));
    assert.ok(JSON.stringify(worst).length <= 40000, `100 worst case claims are ${JSON.stringify(worst).length} characters`);
  });
}
