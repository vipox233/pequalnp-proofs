#!/usr/bin/env node
// Guards for a pull request that adds one proof file. Used by both workflows, before anything
// is built. Plain node, no dependencies. Every value this script hands back to the shell has
// passed a strict pattern, so the shell never sees free text from a pull request.
//
//   node outside-guard.mjs pr <pr.json> <files.json> <tree.json> <repo> <default branch> <out dir>
//   node outside-guard.mjs gap <gaps.json> <gap id> <file path> <out dir> [check|refute|reduce]
//       (for a VALUE STEP the statement written is the desk's template with the file name's k put in)
//   node outside-guard.mjs gap-of-file <gaps.json> <file path> <out dir>
//   node outside-guard.mjs imports <lean file> <imports.json> <file path in the pull request> [kind]
//   node outside-guard.mjs closure <base dir> <imports.json> <judged file path> <out dir> [kind]
//   node outside-guard.mjs number <file path> <base dir> <open.json> <pr number>   (a reduction's k is free)
//   node outside-guard.mjs claims <file path> <claims json> <out open.json>   (the intake's open claims, whole or refused)
//       (each claim's author is sha256 of the lowercased login cut to 12 lowercase hex, or null: never the login itself)
//
// KINDS. A proof (check) or a refutation (refute) of a posted step S is the file of its gap row,
// lean/PEqualNP/Outside/L_<gap>.lean. A REDUCTION of S (kind reduce, ships dark) is
// lean/PEqualNP/Outside/R_<gap>_<n>.lean, n from 1 to 999 without leading zeros, one theorem
// T1 -> ... -> Tk -> S; it is judged only when the run asks for kind reduce AND the desk's row of S
// carries `reductions: true`. An R_ file is refused for every other kind, an L_ file for reduce.
// Without a kind argument (the advisory run) an R_ file is refused.
//
// A VALUE STEP is a desk row of kind `value`: it carries no statement, but a `template` (the fleet's
// own text) holding the token @@VALUE@@ `value_holes` times, and a bound `value_max`. A claim that the
// value is k is the one file lean/PEqualNP/Outside/V_<gap>__k<k>.lean, judged by a run of kind check
// against the template with k put in (valueGap below: the one rule value steps add). A V_ file is
// refused for every row that is not a value step, and an L_ or R_ file for a value step.
//
// <gaps.json> is the desk's list, whole or as the desk's row for one id (GET /desk/row?gap=<id>: the rows with that id,
// its checked entry and its withdrawn reason), which the workflows fetch; the guard decides the same on either.
//
// Exit 0: the guard holds. Exit 1: REFUSED, one line per reason, each line starting `REFUSED: `.
// The pull-request, gap and kind checks give one reason (the first). The checks of the file's text
// (the import, plain-file and own-namespace rules) give EVERY problem they find, in file order, so
// an author fixes all of them in one push; at most MAX_PROBLEMS lines, then `... and N more`, and
// at most MAX_REFUSAL characters in all. The first line is the sentence a one-reason refusal gave.
// Exit 3: bad usage.
import { lstatSync, readdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

// An outside file: L_<gap>.lean (a proof or refutation) or R_<gap>_<n>.lean (a reduction).
export const FILE_RE = /^lean\/PEqualNP\/Outside\/(L_[a-z0-9_]+|R_[a-z0-9_]+_[1-9][0-9]{0,2})\.lean$/;
export const L_FILE_RE = /^lean\/PEqualNP\/Outside\/L_[a-z0-9_]+\.lean$/;
export const R_FILE_RE = /^lean\/PEqualNP\/Outside\/R_[a-z0-9_]+_[1-9][0-9]{0,2}\.lean$/;
// A claim of value k for a value step: V_<gap>__k<k>.lean. Kept OUT of FILE_RE on purpose: land-by-push
// reads FILE_RE, and value files stay on the squash landing path until it is taught the name.
export const VALUE_RE = /^(0|[1-9][0-9]{0,3})$/;
export const V_FILE_RE = /^lean\/PEqualNP\/Outside\/V_[a-z0-9_]+__k(0|[1-9][0-9]{0,3})\.lean$/;
export const VALUE_TOKEN = '@@VALUE@@';
export const MAX_HOLES = 16;
const outsideFile = (f) => FILE_RE.test(f) || V_FILE_RE.test(f);
export const KINDS = ['check', 'refute', 'reduce'];
const FILE_SAY = 'the one file must be lean/PEqualNP/Outside/L_<gap>.lean (or R_<gap>_<n>.lean, n from 1 to 999, for a reduction; or V_<gap>__k<k>.lean for a value step)';
const ONE_FILE_SAY = "one file per pull request, so send each step as its own pull request";
// The file name must fit the run's kind: an R_ file only for reduce, an L_ file never for reduce.
export function checkFileKind(file, kind) {
  if (typeof file !== 'string' || !outsideFile(file)) refuse(FILE_SAY);
  if (kind !== undefined && !KINDS.includes(kind)) refuse(`the kind must be check, refute or reduce, not ${kind}`);
  if (V_FILE_RE.test(file) && kind !== undefined && kind !== 'check') refuse(`${file} is a value file (V_<gap>__k<k>); it is judged only by a run of kind check`);
  if (R_FILE_RE.test(file) && kind !== 'reduce') refuse(`${file} is a reduction file (R_<gap>_<n>); it is judged only by a run of kind reduce`);
  if (L_FILE_RE.test(file) && kind === 'reduce') refuse(`a run of kind reduce judges only a reduction file lean/PEqualNP/Outside/R_<gap>_<n>.lean, not ${file}`);
  return file;
}
export const GAP_RE = /^L-[a-z0-9]+(-[a-z0-9]+)*$/;
export const MODULE_RE = /^PEqualNP(\.[A-Za-z][A-Za-z0-9_]*)+$/;
export const MAX_BYTES = 512 * 1024;
const SHA_RE = /^[0-9a-f]{40}$/;
const LOGIN_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(\[bot\])?$/;

class Refused extends Error {}
const refuse = (why) => { throw new Refused(why); };
// The problems of a file's text, collected: each { at, why }, `at` its line (0 for the whole file,
// before every line; Infinity for what is missing, after every line). Refused once, all of them.
export const MAX_PROBLEMS = 40;
export const MAX_REFUSAL = 6000;
const MAX_LINE = 400;
// A piece of the file's own text quoted in a sentence: at most 60 characters, and only letters,
// digits, dot, underscore and apostrophe (anything else reads `?`), so what the author chose can
// neither steer the log nor fill it (red team, 2026-11-24).
export const tok = (x) => String(x).slice(0, 60).replace(/[^A-Za-z0-9._']/g, '?');
const refuseAll = (problems) => {
  if (problems.length === 0) return;
  const all = problems.map((p, k) => ({ ...p, k })).sort((a, b) => a.at - b.at || a.k - b.k)
    .map((p) => (p.why.length > MAX_LINE ? `${p.why.slice(0, MAX_LINE - 3)}...` : p.why));
  const out = [];
  let size = 0;
  for (const why of all) {
    // Room is kept for the last line, `... and N more`, and for a prefix naming a listed module.
    if (out.length > 0 && (out.length === MAX_PROBLEMS || size + 1 + why.length > MAX_REFUSAL - 200)) break;
    out.push(why); size += (out.length > 1 ? 1 : 0) + why.length;
  }
  if (out.length < all.length) out.push(`... and ${all.length - out.length} more`);
  throw new Refused(out.join('\n'));
};
const json = (path) => { try { return JSON.parse(readFileSync(path, 'utf8')); } catch { return refuse(`${path} is not JSON`); } };
const moduleOf = (file) => file.slice('lean/'.length, -'.lean'.length).split('/').join('.');

// The pull request must add exactly one file, the allowed kind, as a plain file, and nothing else.
// Read from the API's own answers: the pull request, its file list, the tree of its head commit.
export function checkPr(pr, files, tree, repo, defaultBranch) {
  if (pr?.state !== 'open') refuse('the pull request is not open');
  if (pr.base?.repo?.full_name !== repo) refuse('the pull request is not against this repository');
  if (pr.base?.ref !== defaultBranch) refuse(`the pull request is not against ${defaultBranch}`);
  const head = pr.head?.sha;
  if (!SHA_RE.test(head ?? '')) refuse('the pull request has no head commit');
  const author = pr.user?.login;
  if (!LOGIN_RE.test(author ?? '')) refuse('the pull request author is not a plain account name');
  // changed_files is the whole count, so a long file list cannot hide a second file on another page.
  // The fixed sentence for more than one file (red team, 2026-11-24, a repeated honest mistake): it says
  // what to do, not only what is wrong. No colon inside it: the intake keeps a reason up to its first colon.
  if (pr.changed_files > 1) refuse(`the pull request changes ${pr.changed_files} files; ${ONE_FILE_SAY}`);
  if (pr.changed_files !== 1) refuse(`the pull request changes ${pr.changed_files} files; it must add exactly one`);
  if (!Array.isArray(files) || files.length !== 1) refuse(Array.isArray(files) && files.length > 1 ? ONE_FILE_SAY : "the pull request must add exactly one file");
  const f = files[0];
  if (typeof f.filename !== 'string' || !outsideFile(f.filename)) refuse(FILE_SAY);
  if (f.status !== 'added') refuse(`the file must be added, not ${f.status}`);
  if (!SHA_RE.test(f.sha ?? '')) refuse('the file list names no content hash');
  // The tree says what kind of entry it is. 100644 is a plain file: a symbolic link is 120000,
  // an executable 100755, a submodule 160000, and each is refused.
  if (tree?.truncated) refuse('the tree of the head commit is too large to read whole');
  const entries = (tree?.tree ?? []).filter((e) => e.path === f.filename);
  if (entries.length !== 1) refuse('the file is not in the tree of the head commit');
  const e = entries[0];
  if (e.type !== 'blob' || e.mode !== '100644') refuse('the file must be a plain file (not a link, not executable)');
  if (e.sha !== f.sha) refuse('the file list and the tree disagree about the content');
  if (!Number.isInteger(e.size) || e.size < 1 || e.size > MAX_BYTES) refuse(`the file must be between 1 and ${MAX_BYTES} bytes`);
  return { file: f.filename, module: moduleOf(f.filename), head, blob: f.sha, author, size: e.size };
}

// THE NUMBER OF A REDUCTION (2026-11-26, the operator's yes on the checker seat's B2 answer). Nobody hands out k in
// R_<gap>_<k>.lean: the sender picks it, so two senders who read main at the same time take the same k, the second
// is checked, cannot merge (main has the path) and waited in silence. So, at the door, before the checker spends a
// minute, a reduction file is refused when its k is (1) already a file on the base, or (2) the file of an EARLIER
// open pull request (a smaller number, opened within STALE_HOURS), and the refusal names the smallest k free on
// both. The earlier pull request keeps its number, so two at once never block each other. An open pull request
// older than STALE_HOURS stops counting: a number is cheap and an abandoned one must not hold it for ever; the
// time is the API's createdAt (set by GitHub, not by the sender). Stricter only: nothing that passed before is
// let through by this, and a file that is not a reduction is not looked at.
// NO HOARDING (redteam-2's term D2): an account counts for at most MAX_HELD numbers of one step among the counted
// open pull requests (its earliest ones by number); the rest of its claims hold nothing, so one account opening ten
// pull requests on a step blocks three numbers, not ten. An entry with no author counts as one account of its own.
//   onBase: the file names in the base's lean/PEqualNP/Outside; open: the API's open pull requests as
//   [{ number, createdAt, author, files: [path] }] (the intake's, accepted whole by checkClaims, or refused before this);
//   pr: this pull request's number.
export const STALE_HOURS = 48;
export const MAX_HELD = 3;
const R_PARTS_RE = /^(?:lean\/PEqualNP\/Outside\/)?(R_[a-z0-9_]+)_([1-9][0-9]{0,2})\.lean$/;
export function checkCutNumber(file, onBase, open, pr, now = Date.now()) {
  const m = R_PARTS_RE.exec(file ?? '');
  if (!m || !R_FILE_RE.test(file)) return null;
  const [, stem, ks] = m; const k = Number(ks);
  if (!Number.isInteger(pr) || pr < 1) refuse('the pull request number is malformed');
  if (!Array.isArray(onBase) || !Array.isArray(open)) refuse('the list of reduction numbers in use could not be read');
  const onMain = new Set(); const inOpen = new Set(); let earlier = false;
  for (const name of onBase) { const q = R_PARTS_RE.exec(String(name)); if (q && q[1] === stem) onMain.add(Number(q[2])); }
  const claims = [];
  for (const o of open) {
    if (!o || !Number.isInteger(o.number) || o.number === pr || !Array.isArray(o.files)) continue;
    const t = Date.parse(String(o.createdAt ?? ''));
    if (!Number.isFinite(t) || now - t > STALE_HOURS * 3600e3) continue;
    for (const f of o.files) {
      const q = R_PARTS_RE.exec(String(f));
      if (q && q[1] === stem) claims.push({ number: o.number, author: typeof o.author === 'string' ? o.author : `#${o.number}`, n: Number(q[2]) });
    }
  }
  claims.sort((a, b) => a.number - b.number);
  const held = new Map();
  for (const c of claims) {
    const h = held.get(c.author) ?? 0;
    if (h >= MAX_HELD) continue;
    held.set(c.author, h + 1);
    inOpen.add(c.n);
    if (c.n === k && c.number < pr) earlier = true;
  }
  if (!onMain.has(k) && !earlier) return { k };
  let free = 0;
  for (let i = 1; i <= 999; i++) if (!onMain.has(i) && !inOpen.has(i) && i !== k) { free = i; break; }
  const where = onMain.has(k) ? 'is already a file on main' : 'is the file of an earlier open pull request';
  const next = free ? `send the same proof as ${stem}_${free}.lean with the theorem PEqualNP.Outside.${stem}_${free} (the smallest number free on main and in open pull requests), and it is judged` : 'every number from 1 to 999 is in use for this step';
  refuse(`the reduction number ${k} of this step ${where}, so this file could never be merged; ${next}. You did nothing wrong`);
}

// THE OPEN CLAIMS FROM THE INTAKE (2026-11-26): the open pull requests that can claim a k of this step reach the run
// as a dispatch input the intake writes (it holds the whole open list with each one's files, refreshed every minute,
// and it alone starts the run), already cut to this step and the stale window. Taken whole or not at all: a JSON list
// of at most MAX_CLAIMS entries, each exactly { number, createdAt, author, files }, number a pull request number (no
// two alike), createdAt an ISO time in UTC, author the intake's 12-hex hash of the sender or null (red team C2: a login
// is a stranger's text and the input is public on the run's page; the count of three per account needs only equality),
// files 1 to 3 reduction files of THIS step. Anything else refuses the whole list (the workflow then ends as a FAULT), so a list that was cut wrong is never half used.
export const MAX_CLAIMS = 150;
const AUTHOR_HASH_RE = /^[0-9a-f]{12}$/;
const ISO_RE = /^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(?:\.[0-9]{1,3})?Z$/;
export function checkClaims(v, file) {
  const m = R_PARTS_RE.exec(file ?? '');
  if (!m || !R_FILE_RE.test(file)) refuse('the open claims are for a reduction file R_<gap>_<n>.lean only');
  if (!Array.isArray(v)) refuse('the open claims are not a JSON list');
  if (v.length > MAX_CLAIMS) refuse(`the open claims hold more than ${MAX_CLAIMS} entries`);
  const seen = new Set();
  return v.map((o, i) => {
    const at = `open claim ${i + 1}`;
    if (!o || typeof o !== 'object' || Array.isArray(o) || Object.keys(o).sort().join() !== 'author,createdAt,files,number') refuse(`${at} is not exactly { number, createdAt, author, files }`);
    if (!Number.isInteger(o.number) || o.number < 1 || o.number > 9999999 || seen.has(o.number)) refuse(`${at} has a malformed or repeated number`);
    seen.add(o.number);
    if (typeof o.createdAt !== 'string' || !ISO_RE.test(o.createdAt) || !Number.isFinite(Date.parse(o.createdAt))) refuse(`${at} has a malformed time`);
    if (o.author !== null && (typeof o.author !== 'string' || !AUTHOR_HASH_RE.test(o.author))) refuse(`${at} has a malformed author`);
    if (!Array.isArray(o.files) || o.files.length < 1 || o.files.length > 3) refuse(`${at} must list 1 to 3 files`);
    for (const f of o.files) {
      const q = R_PARTS_RE.exec(typeof f === 'string' ? f : '');
      if (!q || !R_FILE_RE.test(f) || q[1] !== m[1]) refuse(`${at} lists a file that is not a reduction file of this step`);
    }
    return { number: o.number, createdAt: o.createdAt, author: o.author, files: [...o.files] };
  });
}

// The gap as the desk posts it. Its file must be the file of the pull request; for a reduction,
// the pull request's file is R_<the gap's L_ name without L_>_<n>.lean. `want` is the run's kind
// (undefined: none given, so the desk's kind stands and an R_ file is refused).
export function checkGap(gaps, pick, file, want) {
  const all = Array.isArray(gaps?.gaps) ? gaps.gaps : refuse('the gap list has no gaps');
  const found = all.filter(pick);
  if (found.length !== 1) {
    // Say WHY the step is not open, from the desk file itself, so an agent working from a saved list
    // learns to ask the desk again (hub-oncall and the red team, 2026-11-24: one handle had 20 of 24
    // runs refused only for this). The desk file carries no time for these, so none is given.
    // The reason text is the desk's own (the fleet's), already public in the same file.
    const done = Array.isArray(gaps?.checked) ? gaps.checked.find((c) => c && pick(c)) : undefined;
    if (done) refuse(`the step ${GAP_RE.test(String(done.id)) ? done.id : ''} is already CHECKED (it is in the desk file's checked list): ask the desk for a step that is still open`);
    const w = gaps?.withdrawn && typeof gaps.withdrawn === 'object' ? Object.keys(gaps.withdrawn).find((id) => pick({ id })) : undefined;
    if (w) {
      const why = String(gaps.withdrawn[w] ?? '').replace(/[^A-Za-z0-9 .,;:()'_+=<>-]/g, '').slice(0, 200);
      refuse(`the step ${GAP_RE.test(w) ? w : ''} was WITHDRAWN from the desk (${why || 'no reason given'}): ask the desk for a step that is still open`);
    }
    refuse('the step is not on the desk (not open, not in its checked or withdrawn lists): ask the desk for a step that is still open');
  }
  const g = found[0];
  if (typeof g.id !== 'string' || !GAP_RE.test(g.id)) refuse('the posted gap has a malformed id');
  checkFileKind(file, want);
  if (g.kind === 'value') return valueGap(g, file, want);
  if (V_FILE_RE.test(file)) refuse(`${file} is a value file, and the desk does not post gap ${g.id} as a value step`);
  if (typeof g.file !== 'string' || !L_FILE_RE.test(g.file)) refuse(`gap ${g.id} names no file lean/PEqualNP/Outside/L_<gap>.lean`);
  if (g.module !== moduleOf(g.file)) refuse(`gap ${g.id} names a module that is not its file`);
  const reduce = want === 'reduce';
  if (reduce) {
    const n = /_([1-9][0-9]{0,2})\.lean$/.exec(file)?.[1];
    if (!n || file !== `lean/PEqualNP/Outside/R_${g.file.slice('lean/PEqualNP/Outside/L_'.length, -'.lean'.length)}_${n}.lean`) refuse(`${file} is not a reduction file of gap ${g.id} (that would be ${g.file.replace('/L_', '/R_').replace(/\.lean$/, '_<n>.lean')})`);
  } else if (g.file !== file) refuse(`the file of gap ${g.id} is not the file of this pull request`);
  if (typeof g.statement !== 'string' || !g.statement.trim() || g.statement.includes('\0')) refuse(`gap ${g.id} has no statement`);
  const imports = g.imports ?? [];
  if (!Array.isArray(imports) || !imports.every((m) => typeof m === 'string' && MODULE_RE.test(m))) refuse(`gap ${g.id} lists a malformed import`);
  // A step the desk posts as a REFUTATION is judged with the checker's refute kind: the file's
  // theorem must be the negation of the recorded statement. Any other value is refused.
  const kind = g.kind === undefined || g.kind === 'check' ? 'check' : g.kind === 'refute' ? 'refute' : refuse(`gap ${g.id} has an unknown kind`);
  if (want !== undefined && !reduce && want !== kind) refuse(`the run's kind is ${want}, and the desk posts gap ${g.id} as kind ${kind}`);
  if (!reduce) return { id: g.id, statement: g.statement, imports, kind };
  // A REDUCTION (dark until the desk opens a step to it): the theorem is T1 -> ... -> Tk -> S, so
  // only a step posted to be proved can be reduced, and only one the desk marks open to reductions.
  if (g.reductions !== true) refuse(`gap ${g.id} is not open to reductions: the desk's row carries no \`reductions: true\`, so no reduction of it is judged`);
  if (kind !== 'check') refuse(`gap ${g.id} is posted as a ${kind} step; only a step posted to be proved is reduced`);
  return { id: g.id, statement: g.statement, imports, kind: 'reduce' };
}

// THE ONE RULE OF A VALUE STEP. The desk's row carries a template, never a statement; this writes the
// statement the checker judges. Nothing is read from the pull request but its file's NAME, and the
// name is not trusted for its shape: in this order,
//   1. the numeral: k is the name's last piece, ASCII digits only, `0` or no leading zero, at most
//      four digits, and at most the row's value_max; refused first, before anything else is read;
//   2. the name: the expected path is REBUILT from the gap id and k and must equal the pull
//      request's file byte for byte. The separator `__k` stands in no gap id (an id's parts are joined
//      by single underscores), so a name splits one way only, and k is never parsed out of a free name;
//   3. the token: the template holds @@VALUE@@ exactly `value_holes` times (the count stored when the
//      step was posted), each time as a whole term (after a space, a line break or `(`; before a
//      space, a line break, `)` or the end), and no other doubled at-sign. EVERY occurrence is replaced
//      by the same decimal numeral. The result holds no doubled at-sign.
// From there on nothing changes: the statement goes to the checker as for any step, kind check, and
// the workflow records the sha256 of exactly these bytes. The hub rebuilds the same bytes from its
// OWN stored template and records the run only when the hashes agree, so a desk file that served
// another template cannot settle anything.
export function valueGap(g, file, want) {
  if (want !== undefined && want !== 'check') refuse(`gap ${g.id} is a value step; it is judged only by a run of kind check, not ${want}`);
  const say = `the one file of a value step is lean/PEqualNP/Outside/V_<gap>__k<k>.lean, k the value claimed, written in plain digits with no leading zero`;
  if (!Number.isInteger(g.value_max) || g.value_max < 0 || g.value_max > 9999) refuse(`gap ${g.id} is a value step with a malformed value_max`);
  if (!V_FILE_RE.test(file)) refuse(`gap ${g.id} is a value step, and ${file} is not a value file; ${say}`);
  const k = /__k([^_/.]*)\.lean$/.exec(file)?.[1] ?? '';
  if (!VALUE_RE.test(k)) refuse(`the value in the file name is not a plain numeral; ${say}`);
  if (Number(k) > g.value_max) refuse(`the value ${k} is above the bound of gap ${g.id}: no value above ${g.value_max} is judged (a circuit of that size is on the record)`);
  const expected = `lean/PEqualNP/Outside/V_${g.id.slice(2).replace(/-/g, '_')}__k${k}.lean`;
  if (file !== expected) refuse(`${file} is not the file of value ${k} of gap ${g.id} (that is ${expected})`);
  const t = g.template;
  if (typeof t !== 'string' || !t.trim() || t.includes('\0')) refuse(`gap ${g.id} is a value step with no template`);
  if (!Number.isInteger(g.value_holes) || g.value_holes < 1 || g.value_holes > MAX_HOLES) refuse(`gap ${g.id} is a value step with a malformed value_holes`);
  const parts = t.split(VALUE_TOKEN);
  if (parts.length - 1 !== g.value_holes) refuse(`the template of gap ${g.id} holds ${VALUE_TOKEN} ${parts.length - 1} time(s), and the step was posted with ${g.value_holes}`);
  if (parts.join('').includes('@@')) refuse(`the template of gap ${g.id} holds a doubled at-sign that is not ${VALUE_TOKEN}`);
  for (let i = 0; i < parts.length - 1; i += 1) {
    const before = parts[i] === '' && i === 0 ? ' ' : parts[i].slice(-1), after = parts[i + 1] === '' && i === parts.length - 2 ? ' ' : parts[i + 1].slice(0, 1);
    if (!/^[ \n(]$/.test(before) || !/^[ \n)]$/.test(after)) refuse(`the template of gap ${g.id} holds ${VALUE_TOKEN} where it is not a whole term`);
  }
  const statement = parts.join(k);
  if (!statement.trim() || statement.includes('@@')) refuse(`gap ${g.id} has no statement at value ${k}`);
  const imports = g.imports ?? [];
  if (!Array.isArray(imports) || !imports.every((m) => typeof m === 'string' && MODULE_RE.test(m))) refuse(`gap ${g.id} lists a malformed import`);
  return { id: g.id, statement, imports, kind: 'check', value: Number(k) };
}
// The row a file belongs to, for the run that is given no gap id: the row that names the file, or the
// value step whose file of the name's k it is (rebuilt, as above; never parsed apart).
export const rowOfFile = (file) => (x) => x?.file === file || (x?.kind === 'value' && typeof x.id === 'string' && GAP_RE.test(x.id) && V_FILE_RE.test(String(file))
  && file === `lean/PEqualNP/Outside/V_${x.id.slice(2).replace(/-/g, '_')}__k${/__k([0-9]+)\.lean$/.exec(file)?.[1]}.lean`);

// The import rule. The file starts with its import lines, one module per line, and nothing else
// is among them. Each must be Mathlib, a module of Mathlib, or a module the gap lists. After the
// import lines the word `import` may not appear at all: Lean reads imports through comments, so
// `/- -/ import X` on a later line would still be an import. A plain rule, stricter than Lean.
export function checkImports(bytes, allowed) {
  const problems = [];
  const seen = importProblems(bytes, allowed, problems);
  refuseAll(problems);
  return seen;
}

// The text of the file's bytes. What cannot be read as text is refused at once, alone.
const textOf = (bytes) => {
  if (bytes.length > MAX_BYTES) refuse(`the file is larger than ${MAX_BYTES} bytes`);
  let text;
  try { text = new TextDecoder('utf-8', { fatal: true }).decode(bytes); } catch { return refuse('the file is not UTF-8 text'); }
  if (text.includes('\0')) refuse('the file holds a NUL byte');
  plainChars(text);
  return text;
};

// Control, invisible and direction-changing characters stop the check first and alone, as a NUL
// does: the workflow's quoting strips ASCII control characters only (red team, 2026-11-24).
const plainChars = (text) => {
  if (CONTROL.test(text.replace(/\r?\n/g, ''))) refuse('the file holds control characters');
  if (INVISIBLE.test(text)) refuse('the file holds invisible or direction-changing characters');
};

function importProblems(bytes, allowed, problems) {
  const text = textOf(bytes);
  const lines = text.split('\n').map((l) => l.replace(/\r$/, ''));
  const ok = typeof allowed === 'function' ? { has: allowed } : new Set(allowed);
  const seen = [];
  let i = 0;
  for (; i < lines.length; i += 1) {
    const l = lines[i];
    if (l.trim() === '') continue;
    const m = /^import ([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*)[ \t]*$/.exec(l);
    if (!m) break;
    const name = m[1];
    if (!(name === 'Mathlib' || name.startsWith('Mathlib.') || ok.has(name))) problems.push({ at: i + 1, why: `line ${i + 1}: import ${tok(name)} is not allowed (only Mathlib and the modules the gap lists)` });
    else seen.push(name);
  }
  for (; i < lines.length; i += 1) {
    if (/(^|[^A-Za-z0-9_])import([^A-Za-z0-9_]|$)/.test(lines[i])) problems.push({ at: i + 1, why: `line ${i + 1}: the word "import" after the import lines (imports are plain lines at the top, one module each)` });
  }
  plainProblems(text, problems);
  return seen;
}

// THE DANGEROUS-BY-NAME RULE: a first filter, NOT what makes an outside file safe to build. A
// Lean file runs code while it compiles; what contains that is the sandbox this job runs in (no
// secrets, no network, a time limit, a machine thrown away after) and the checker's own rules.
// This rule refuses, early and by name, what has no place in a proof file: code that runs at
// build time, new syntax, kernel bypasses, the meta-programming namespaces, string literals.
//   1. The RAW text is searched, comments included, and nothing is stripped: a stripper can be
//      led astray, so none is used. A refused word inside a comment is refused too: reword it.
//   2. It does NOT judge form. Comment prose at column 0, a `#` heading in a doc comment, a small
//      data type (`inductive ... deriving DecidableEq`) or an instance are built and judged by
//      the checker; whether such a file is merged is decided where it is read before any merge.
//      (Measured 2026-11-23: a rule that also refused form bounced nine honest proofs of
//      eighteen, each for a comment line or a small enumerated type.)
//   3. KNOWN LIMIT: the list cannot be complete. What it misses meets the sandbox.
// The only attributes are `@[simp]` and `@[local simp]`; the only options are four limits.
const B = String.raw`(?<![A-Za-z0-9_])`, A = String.raw`(?![A-Za-z0-9_])`;
const FORBIDDEN = new RegExp([
  String.raw`"|[«»]|simproc|builtin_|native|bv_decide|ofReduce|reduceNat|reduceBool`,
  '|' + B + String.raw`(Lean|System|IO|Elab|Meta|Lake|FS|Process|EIO)` + A,
  String.raw`|_root_|RealWorld|BaseIO|include_str|notation|[A-Za-z_][A-Za-z0-9_']*[A-Za-z0-9_']%|polyrith|initialize|run_cmd|run_tac|run_elab|run_meta|by_elab`,
  '|' + B + String.raw`elab|` + B + String.raw`macro|` + B + 'syntax' + A + '|' + B + 'attribute' + A,
  '|' + B + 'axiom' + A + '|' + B + 'opaque' + A + String.raw`|unsafe|` + B + 'partial' + A + String.raw`|sorry|` + B + 'admit' + A,
  String.raw`|#[a-z_][a-z_]{2,}|implemented_by|extern`,
  String.raw`|` + '`' + String.raw`\([a-z]+\||\$\(|%\[|@\[|register_|declare_|lcProof|lcUnreachable|` + B + 'infix|' + B + 'prefix' + A + '|' + B + 'postfix' + A,
  String.raw`|set_option|binder_predicate|unif_hint|^\s*add_\w+|unseal|compile_inductive|irreducible_def|proof_wanted|mk_iff_of_inductive_prop`,
].join(''), 'u');
// The four limit options, wherever they stand, are taken out before the list is asked; every
// other set_option, at column 0 or indented, is refused by it.
// The matched word is printed raw only when it is EXACTLY one of these literals of our own rules
// (string equality); any other match goes through tok() (red team, 2026-11-24).
const RAW_WORDS = new Set([
  '"', '«', '»', '$(', '%[', '@[', '`(tactic|', '`(term|', '`(command|', '`(conv|', '`(doElem|',
  '#eval', '#check', '#print', '#reduce', '#synth', '#exit', '#help', '#lint', '#guard', '#guard_msgs',
  '#find', '#simp', '#norm_num', '#conv', '#where', '#time', '#check_failure', '#adaptation_note',
  'simproc', 'builtin_', 'native', 'bv_decide', 'ofReduce', 'reduceNat', 'reduceBool',
  'Lean', 'System', 'IO', 'Elab', 'Meta', 'Lake', 'FS', 'Process', 'EIO',
  '_root_', 'RealWorld', 'BaseIO', 'include_str', 'notation', 'polyrith', 'initialize',
  'run_cmd', 'run_tac', 'run_elab', 'run_meta', 'by_elab', 'elab', 'macro', 'syntax', 'attribute',
  'axiom', 'opaque', 'unsafe', 'partial', 'sorry', 'admit', 'implemented_by', 'extern',
  'register_', 'declare_', 'lcProof', 'lcUnreachable', 'infix', 'prefix', 'postfix',
  'set_option', 'binder_predicate', 'unif_hint', 'unseal', 'compile_inductive', 'irreducible_def',
  'proof_wanted', 'mk_iff_of_inductive_prop',
]);
const sayWord = (w) => (RAW_WORDS.has(w) ? w : tok(w));
const LIMIT = /set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+ in(?![A-Za-z0-9_])/gu;
const INVISIBLE = /[​-‏‪-‮⁠-⁩﻿]/u;
const CONTROL = /[\u0000-\u0008\u000b-\u001f\u007f]/u;

// THE % RULE (red team sign 91, 2026-11-24): a name written straight before % is a library term macro
// (eval% evaluates code while the file elaborates; type_of%, decl_name% and their kind), so a NAME of two or
// more characters before % is refused, whatever follows. A single character or a number before % is the
// remainder operator (n%2, k%m, 10%3): no macro of the library is one character long, so that is plain.
export function checkPlain(text) {
  plainChars(text);
  const problems = [];
  plainProblems(text, problems);
  refuseAll(problems);
}

function plainProblems(text, problems) {
  let theorems = 0;
  text.split('\n').forEach((raw, k) => {
    const line = raw.replace(/\r$/, '');
    const m = FORBIDDEN.exec(line.replace(LIMIT, '').replace(/@\[(local )?simp\]/gu, ''));
    // A line that BEGINS with a name starting add_ reads like one of the library's add_ commands.
    // An honest proof line can begin with such a lemma name: the sentence says the way round.
    let hint = m && /^add_/.test(m[0].trim()) ? '; a line may not BEGIN with a name that starts with add_ (the library\'s commands do): if this is a lemma of yours used in a proof, put it after other text on the line or rename it' : '';
    // A limit option set for the whole file (no `in`) is refused, as before; the sentence names the
    // one fix, so an honest prover passes in one push (red team, 2026-11-23: the rule stays narrow).
    if (m && /^\s*set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+\s*$/u.test(line)) hint = '; a limit option holds only for one declaration: write it as set_option <option> <value> in, directly before the declaration that needs it';
    // bv_decide calls a SAT solver while the file builds; honest contributors reach for it on the
    // packed-column statements (a repeated honest mistake). The line says what to use instead.
    if (m && m[0].trim() === 'bv_decide') hint = '; bv_decide runs a SAT solver as the file builds, so use tactics the kernel checks alone, e.g. decide (small sizes), simp, omega, rfl';
    if (m) problems.push({ at: k + 1, why: `line ${k + 1}: "${sayWord(m[0].trim())}" is not allowed in a proof file, in code or in a comment (no code that runs at build time, no new syntax, no string literals, no attributes but simp, no options but the four limits)${hint}` });
    if (/^\s*(@\[(local )?simp\] )?((private|protected) )?theorem /u.test(line)) theorems += 1;
  });
  if (theorems === 0) problems.push({ at: Infinity, why: 'the file holds no theorem' });
}

// THE OWN-NAMESPACE RULE, for the file of a NEW pull request only (merged files are never edited,
// so the closure check below does not apply it to listed modules). Every helper of the file sits
// inside a namespace block named after the file, so two outside files, or an outside file and the
// project's own modules, can always be imported together (a file that copied project modules
// under the project's namespaces once could not be). For lean/PEqualNP/Outside/L_x.lean, M is
// PEqualNP.Outside.L_x, and at the top level (outside every block) the only code lines are:
//   import lines; `open ...` lines; the four limit options (`set_option <limit> <n> in`);
//   `namespace N` where N is M, M.<more>, M_aux or M_aux.<more>; the one theorem, written
//   `theorem M ...` with its full name, last: after it only its proof (no command word).
// Inside such a block anything the other rules allow. `namespace`, `section`, `end` and `mutual`
// stand alone at column 0 (an indented one is refused), so the depth is read line by line; each
// `end` names exactly what it closes. A line is read with its comments blanked: Lean ignores them.
// Private declarations at the top level are refused too: one simple rule, and a private helper
// moves into the block with two lines. KNOWN LIMITS: instances and simp lemmas inside the block
// still act in every importer (names are safe, behaviour is not); after the theorem the proof is
// searched for a list of command words, and a command word the list misses would meet the build.
const ID = String.raw`[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}_][\p{L}\p{N}_'!?]*)*`;
const W = (words) => new RegExp(String.raw`(?<![\p{L}\p{N}_.'!?])(?:${words})(?![\p{L}\p{N}_'!?])`, 'u');
const SCOPE_WORD = W('namespace|section|end|mutual');
const SCOPE_LINE = new RegExp(String.raw`^(?:(namespace) (${ID})|(noncomputable section|section)(?: (${ID}))?|(end)(?: (${ID}))?|(mutual))[ \t]*$`, 'u');
const AFTER_THEOREM = W('def|theorem|lemma|abbrev|instance|structure|class|inductive|coinductive|example|opaque|axiom|noncomputable|private|protected|partial|unsafe|variable|universe|attribute|export|deriving|alias|local|scoped|omit|include|mk_iff_of_inductive_prop');
const TOP_LIMIT = /^set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+ in[ \t]*$/u;

// The text with every comment blanked (same length, line breaks kept). No string literal can
// stand in a file that passed checkPlain, so a comment opener is always one.
export function blankComments(text) {
  let out = '', i = 0, depth = 0;
  const blank = (s) => s.replace(/[^\n]/g, ' ');
  while (i < text.length) {
    if (depth > 0) {
      if (text.startsWith('/-', i)) { depth += 1; out += '  '; i += 2; } else if (text.startsWith('-/', i)) { depth -= 1; out += '  '; i += 2; } else { out += blank(text[i]); i += 1; }
    } else if (text.startsWith('/-', i)) { depth = 1; out += '  '; i += 2; }
    else if (text.startsWith('--', i)) { const j = text.indexOf('\n', i); const e = j < 0 ? text.length : j; out += blank(text.slice(i, e)); i = e; }
    else { out += text[i]; i += 1; }
  }
  return out;
}

export function checkOwnNamespace(text, module) {
  const problems = [];
  namespaceProblems(text, module, problems);
  refuseAll(problems);
}

// Each problem is noted and the walk goes on, keeping the depth as the author meant it (a block
// opened where it may not be is still pushed, so its own `end` closes it and its body is not
// reported line by line), so the next problem is found too.
function namespaceProblems(text, module, problems) {
  const reduction = REDUCTION_MODULE_RE.test(module);
  if (!OUTSIDE_MODULE_RE.test(module) && !VALUE_MODULE_RE.test(module) && !reduction) { problems.push({ at: -1, why: `${module} is not the module of an outside proof file` }); return; }
  if (module.endsWith('_aux')) problems.push({ at: -1, why: 'the file name may not end in _aux (that suffix names the helper namespace of another file)' });
  const own = (n) => n === module || n.startsWith(`${module}.`) || n === `${module}_aux` || n.startsWith(`${module}_aux.`);
  const fix = `put every helper inside \`namespace ${module}\` ... \`end ${module}\`; only the imports and the theorem stay outside`;
  const stack = [];
  let theorem = false;
  blankComments(text).split('\n').forEach((raw, k) => {
    const code = raw.replace(/\r$/, '').replace(/[ \t]+$/, '');
    if (code.trim() === '') return;
    const at = `line ${k + 1}`;
    const note = (why) => problems.push({ at: k + 1, why });
    if (SCOPE_WORD.test(code)) {
      const m = SCOPE_LINE.exec(code);
      if (!m) { note(`${at}: \`namespace\`, \`section\`, \`end\` and \`mutual\` must stand alone at the start of a line (not indented, nothing else on it); ${fix}`); return; }
      if (theorem) { note(`${at}: nothing but the proof may follow the theorem ${module}; ${fix}`); return; }
      if (m[1]) {
        // The checker refuses a reduction file that declares anything but its theorem (reduce-extra).
        if (reduction) note(`${at}: \`namespace ${tok(m[2])}\`; a reduction file holds its one theorem \`theorem ${module} : T1 → ... → Tk → S\` and nothing else, so it opens no namespace`);
        else if (stack.length === 0 && !own(m[2])) note(`${at}: \`namespace ${tok(m[2])}\` at the top level; the only namespace allowed there is the file's own; ${fix}`);
        stack.push({ kind: 'namespace', name: m[2] });
      } else if (m[3]) {
        if (stack.length === 0) note(`${at}: a section at the top level; open it inside the file's own namespace; ${fix}`);
        stack.push({ kind: 'section', name: m[4] });
      } else if (m[7]) {
        if (stack.length === 0) note(`${at}: \`mutual\` at the top level; ${fix}`);
        stack.push({ kind: 'mutual' });
      } else {
        const top = stack.pop();
        if (!top) note(`${at}: \`end\` with nothing open to close; ${fix}`);
        else if (top.kind === 'mutual' ? m[6] !== undefined : m[6] !== top.name) note(`${at}: \`end${m[6] ? ` ${tok(m[6])}` : ''}\` does not name what it closes (${top.kind === 'mutual' ? '`end` alone closes `mutual`' : `write \`end${top.name ? ` ${tok(top.name)}` : ''}\``})`);
      }
      return;
    }
    if (theorem) {
      const w = AFTER_THEOREM.exec(code);
      if (w) note(`${at}: "${tok(w[0])}" after the theorem ${module}; nothing but its proof may follow it; ${fix}`);
      return;
    }
    if (stack.length > 0) return;
    if (/^import [^ \t]+$/u.test(code) || TOP_LIMIT.test(code)) return;
    if (/^open[ \t]/u.test(code)) {
      if (/[ \t]in[ \t]+\S/u.test(code)) note(`${at}: an \`open ... in\` line must end with \`in\`, with the theorem on the next line; ${fix}`);
      return;
    }
    if (new RegExp(String.raw`^theorem ${module.replace(/\./g, '\\.')}(?![\p{L}\p{N}_'!?.])`, 'u').test(code)) { theorem = true; return; }
    note(`${at}: a declaration or command outside the file's own namespace (at the top level only imports, \`open\` lines, the four limit options, \`namespace ${module}\` and \`theorem ${module}\` may stand); ${fix}`);
  });
  if (!theorem) problems.push({ at: Infinity, why: `the theorem must stand at the top level, last, written with its full name: \`theorem ${module} ...\`; ${fix}` });
}

// The whole file check of the `imports` command: the import, plain-file and own-namespace rules
// read the same text, and every problem of all three is refused at once, in file order.
export function checkProofFile(bytes, allowed, module) {
  const problems = [];
  const seen = importProblems(bytes, allowed, problems);
  namespaceProblems(new TextDecoder().decode(bytes), module, problems);
  refuseAll(problems);
  return seen;
}

// WHAT THE BASE STEP MAY BUILD. A gap may list modules that outsiders wrote (anything under
// PEqualNP.Outside, merged on the base branch). A Lean file runs code while it compiles, so such
// a module is never built by the base step: it is built in the locked step, by the checker's own
// build of the judged file, as the account that compiles the judged file. This walks the imports
// of every listed module, as plain text, and splits them:
//   outside: every outside-written module reached (through outside modules only);
//   base:    every other project module reached; the base step builds these.
// Refused: a listed module that is the judged file or is not a plain file of the base tree; an
// outside module whose text fails the rules a proof file must pass (checkImports, checkPlain:
// a second net, the sandbox is the first); a base module that imports an outside module (it
// could be built neither before the locked step, which would compile outside code, nor inside
// it, where nothing of the base may be written); a project module that is not under the
// PEqualNP root (the checker's fixtures are never a gap's import); more than MAX_OUTSIDE
// outside modules (each one is compiled on every run that lists it).
// CONSEQUENCE: a fleet module that imports an outside proof can never be a listed import. A
// file that builds on outside proofs imports the outside modules themselves, and the gap lists
// them; fleet helpers built on outside proofs stay off the lists.
export const OUTSIDE_MODULE_RE = /^PEqualNP\.Outside\.L_[a-z0-9_]+$/;
// The module of a reduction file. Never a listed import: a gap lists only L_ modules.
export const REDUCTION_MODULE_RE = /^PEqualNP\.Outside\.R_[a-z0-9_]+_[1-9][0-9]{0,2}$/;
// The module of a value file. Never a listed import either: a gap lists only L_ modules.
export const VALUE_MODULE_RE = /^PEqualNP\.Outside\.V_[a-z0-9_]+__k(0|[1-9][0-9]{0,3})$/;
export const MAX_OUTSIDE = 16;
const PROJECT_RE = /^(PEqualNP|CheckerSuite)(\.[A-Za-z][A-Za-z0-9_]*)*$/;
const BASE_ROOT_RE = /^PEqualNP(\.[A-Za-z][A-Za-z0-9_]*)*$/;
const isOutside = (m) => m === 'PEqualNP.Outside' || m.startsWith('PEqualNP.Outside.');

// The import lines of a base module, read the way Lean reads a header: comments, `module`,
// `prelude` and the modifiers `public`, `meta`, `private`, `all` are passed over. Base files are
// the project's own and are not hostile; the reader still fails closed: an `import` at the start
// of a line below the header it found is refused, never passed over.
export function headerImports(text, name) {
  const toks = [];
  let i = 0, line = 0;
  while (i < text.length) {
    const c = text[i];
    if (c === '\n') { line += 1; i += 1; } else if (/\s/.test(c)) { i += 1; }
    else if (text.startsWith('--', i)) { while (i < text.length && text[i] !== '\n') i += 1; }
    else if (text.startsWith('/-', i)) {
      let depth = 0;
      do {
        if (text.startsWith('/-', i)) { depth += 1; i += 2; } else if (text.startsWith('-/', i)) { depth -= 1; i += 2; }
        else { if (text[i] === '\n') line += 1; i += 1; }
      } while (depth > 0 && i < text.length);
    } else {
      let j = i; while (j < text.length && !/\s/.test(text[j]) && !text.startsWith('--', j) && !text.startsWith('/-', j)) j += 1;
      toks.push({ t: text.slice(i, j), line }); i = j;
    }
  }
  const out = [];
  let k = 0, end = 0;
  for (; k < toks.length; k += 1) {
    const t = toks[k].t;
    if (['module', 'prelude', 'public', 'meta', 'private'].includes(t)) continue;
    if (t !== 'import') break;
    k += 1;
    if (toks[k]?.t === 'all') k += 1;
    const id = (toks[k]?.t ?? '').replace(/[«»]/g, '');
    if (!/^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(id)) refuse(`cannot read the imports of ${name}`);
    out.push(id); end = toks[k].line;
  }
  const lines = text.split('\n');
  for (let n = end + 1; n < lines.length; n += 1) {
    if (/^\s*((public|meta|private)\s+)*import\s/.test(lines[n])) refuse(`cannot read the imports of ${name}: an import line below its header (line ${n + 1})`);
  }
  return out;
}

export function importClosure(listed, read, judged) {
  const outside = new Set(), base = new Set();
  const visit = (m, from) => {
    if (outside.has(m) || base.has(m)) return;
    if (!BASE_ROOT_RE.test(m)) refuse(`${from ? `${from} imports` : 'the gap lists'} ${tok(m)}, which is not under the PEqualNP root`);
    if (m === judged) refuse(`${from ? `${from} imports` : 'the gap lists'} ${tok(m)}, the file being judged`);
    const bytes = read(m);
    if (bytes === null) refuse(`${from ? `${from} imports` : 'the gap lists'} ${tok(m)}, which is not a plain file of the base tree`);
    if (isOutside(m)) {
      if (!OUTSIDE_MODULE_RE.test(m)) refuse(`${m} is not the name of an outside proof file`);
      outside.add(m);
      if (outside.size > MAX_OUTSIDE) refuse(`more than ${MAX_OUTSIDE} outside modules are listed or reached (${[...outside].slice(0, 3).join(', ')}, ...); list fewer`);
      // The same rules a proof file passes before it is built, on the text as it is on the base.
      let imports;
      try { imports = checkImports(bytes, (x) => PROJECT_RE.test(x)); } catch (e) { if (e instanceof Refused) refuse(`the listed outside module ${m}: ${e.message}`); throw e; }
      for (const x of imports) if (PROJECT_RE.test(x)) visit(x, m);
    } else {
      base.add(m);
      for (const x of headerImports(new TextDecoder().decode(bytes), m)) {
        if (!PROJECT_RE.test(x)) continue;
        if (isOutside(x)) refuse(`the base module ${m} imports the outside-written ${x}; it can be built neither before the locked step nor in it`);
        visit(x, m);
      }
    }
  };
  for (const m of listed) visit(m, null);
  return { outside: [...outside].sort(), base: [...base].sort() };
}

const put = (dir, name, value) => writeFileSync(join(dir, name), value);
const main = () => {
  const [cmd, ...a] = process.argv.slice(2);
  if (cmd === 'pr' && a.length === 6) {
    const r = checkPr(json(a[0]), json(a[1]), json(a[2]), a[3], a[4]);
    for (const [k, v] of Object.entries(r)) put(a[5], `pr.${k}`, `${v}\n`);
  } else if ((cmd === 'gap' && (a.length === 4 || a.length === 5)) || (cmd === 'gap-of-file' && a.length === 3)) {
    const byId = cmd === 'gap';
    const [gapsPath, file, out] = byId ? [a[0], a[2], a[3]] : a;
    if (byId && !GAP_RE.test(a[1])) refuse('the gap id is malformed');
    const g = checkGap(json(gapsPath), byId ? (x) => x?.id === a[1] : rowOfFile(file), file, byId ? a[4] : undefined);
    put(out, 'gap.id', `${g.id}\n`);
    put(out, 'statement.txt', g.statement);          // the posted text, byte for byte
    put(out, 'imports.json', JSON.stringify(g.imports));
    put(out, 'imports.txt', g.imports.map((m) => `${m}\n`).join(''));
    put(out, 'gap.kind', `${g.kind}\n`);
  } else if (cmd === 'number' && a.length === 4) {
    // node outside-guard.mjs number <file path> <base dir> <open.json> <pr number>
    const [file, baseDir, openPath, prs] = a;
    if (!/^[1-9][0-9]{0,8}$/.test(prs)) refuse('the pull request number is malformed');
    const dir = join(baseDir, 'lean', 'PEqualNP', 'Outside');
    let names = []; try { names = readdirSync(dir); } catch { names = []; }
    if (!R_FILE_RE.test(file)) refuse('the number check is for a reduction file R_<gap>_<n>.lean only');
    const r = checkCutNumber(file, names, json(openPath), Number(prs));
    process.stdout.write(`the reduction number ${r.k} is free on main and in earlier open pull requests\n`);
  } else if (cmd === 'claims' && a.length === 3) {
    // node outside-guard.mjs claims <file path> <claims json> <out open.json>
    const [file, inPath, outPath] = a;
    const raw = (() => { try { return readFileSync(inPath, 'utf8'); } catch { return refuse('the open claims could not be read'); } })();
    if (raw.length > 40000) refuse('the open claims are longer than 40000 characters');
    let v; try { v = JSON.parse(raw); } catch { refuse('the open claims are not JSON'); }
    const claims = checkClaims(v, file);
    writeFileSync(outPath, JSON.stringify(claims));
    process.stdout.write(`open claims of this step from the intake: ${claims.length}\n`);
  } else if (cmd === 'imports' && (a.length === 3 || a.length === 4)) {
    checkFileKind(a[2], a[3]);
    const bytes = readFileSync(a[0]);
    const seen = checkProofFile(bytes, json(a[1]), moduleOf(a[2]));
    process.stdout.write(`imports allowed: ${seen.join(' ') || '(none)'}\n`);
  } else if (cmd === 'closure' && (a.length === 4 || a.length === 5)) {
    const [baseDir, importsPath, judgedFile, out] = a;
    checkFileKind(judgedFile, a[4]);
    const listed = json(importsPath);
    if (!Array.isArray(listed) || !listed.every((m) => typeof m === 'string' && MODULE_RE.test(m))) refuse('the listed imports are malformed');
    // A module's file in the base tree: a plain file (not a link), at most 512 KiB, else null.
    const read = (m) => {
      const p = join(baseDir, 'lean', ...m.split('.')) + '.lean';
      let st; try { st = lstatSync(p); } catch { return null; }
      if (!st.isFile() || st.size > MAX_BYTES) return null;
      return readFileSync(p);
    };
    const r = importClosure(listed, read, moduleOf(judgedFile));
    put(out, 'base-imports.txt', r.base.map((m) => `${m}\n`).join(''));
    put(out, 'outside-imports.txt', r.outside.map((m) => `${m}\n`).join(''));
    put(out, 'outside-sources.txt', r.outside.map((m) => `base/lean/${m.split('.').join('/')}.lean\n`).join(''));
    process.stdout.write(`built before the locked step: ${r.base.join(' ') || '(none)'}\noutside-written, built only in the locked step: ${r.outside.join(' ') || '(none)'}\n`);
  } else {
    process.stderr.write('usage: outside-guard.mjs pr|gap|gap-of-file|imports|closure|number|claims ... (see the header)\n');
    process.exit(3);
  }
  // ONE FIXED LAST LINE ON SUCCESS (2026-11-26): the workflows require it after every call, so a silent exit 0 is
  // never read as a pass, whatever changes in how the guard is called.
  process.stdout.write(`GUARD OK: ${cmd}\n`);
};

// RUN AS A SCRIPT, BY REAL PATH (2026-11-26, the operator's order, security first). This used to compare its own URL
// with the called path as text, so a call through a symlinked path (a linked work folder, the Mac's /tmp) skipped
// main, printed nothing and exited 0: a door that passes by saying nothing. Now both sides are resolved to real paths,
// and a run that names this file but still is not main stops as a FAULT, never as a pass. Imported (the tests), it
// does nothing, as before. The workflows also require each call's verdict line or files, so a silent 0 cannot pass.
export const ranAsScript = (url, argv1) => {
  if (!argv1) return false;
  try { return realpathSync(fileURLToPath(url)) === realpathSync(argv1); } catch { return false; }
};
if (!ranAsScript(import.meta.url, process.argv[1]) && process.argv[1] && /(^|[\/\\])outside-guard\.mjs$/.test(process.argv[1])) {
  process.stdout.write('FAULT: the guard was started but did not run its checks (its own path and the called path differ); nothing passed\n');
  process.exit(3);
}
if (ranAsScript(import.meta.url, process.argv[1])) {
  try { main(); } catch (e) {
    if (!(e instanceof Refused)) throw e;
    process.stdout.write(e.message.split('\n').map((l) => `REFUSED: ${l}\n`).join(''));
    process.exit(1);
  }
}
