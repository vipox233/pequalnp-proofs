#!/usr/bin/env bash
# Run: bash tools/test_pnp_value.sh [gaps.json]
# Value steps in tools/pnp.sh: `next` writes nothing; `value <step> <k>` writes the theorem whose statement is, byte for
# byte, the one the public guard judges (valueGap in .github/scripts/outside-guard.mjs, run here); a bad k and an injected
# template are refused with nothing written; `tidy` (and check) removes comments outside literals; submit sends only the
# bytes check built. git, gh and lake are stubs on PATH: nothing is fetched from or pushed to a real host. Given a gaps.json,
# every value row in it is written at k = 0 and at k = value_max and matched against valueGap.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; guard="$here/../.github/scripts/outside-guard.mjs"; t="$(mktemp -d)"; trap 'kill $srv 2>/dev/null || true; wait $srv 2>/dev/null || true; rm -rf "$t"' EXIT
mkdir -p "$t/repo" "$t/bin" "$t/www"; git -C "$t/repo" init -q; mkdir -p "$t/repo/tools"; cp "$here/pnp.sh" "$t/repo/tools/"
printf '#!/bin/sh\necho tester\n' > "$t/bin/gh"; chmod +x "$t/bin/gh"
port=$((20000 + RANDOM % 20000)); (cd "$t/www" && exec python3 -m http.server "$port" --bind 127.0.0.1 >/dev/null 2>"$t/access") & srv=$!
for _ in $(seq 50); do curl -s "http://127.0.0.1:$port/" >/dev/null && break; sleep 0.1; done
R="$t/repo"; export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
mkdir -p "$t/up"; git -C "$t/up" init -q -b main; echo r > "$t/up/README"; mkdir -p "$t/up/lean/PEqualNP/Outside"; echo x > "$t/up/lean/PEqualNP/Outside/L_x_1.lean"
git -C "$t/up" add -A; git -C "$t/up" -c user.name=t -c user.email=t@t commit -qm base
! grep -q 'PNP_UPSTREAM' "$here/pnp.sh" || { echo "FAIL: the fetch source can be set from the environment"; exit 1; }
# git: the project's URL is answered from $t/up, any other fetch is refused, a push is only logged
cat > "$t/bin/git" <<STUB
#!/bin/bash
if [ "\$1" = push ]; then echo "\$*" >> "$t/pushed"; exit 0; fi
if [ "\$1" = fetch ]; then [ "\$*" = "fetch -q https://github.com/open-goat/pequalnp-proofs.git main" ] || { echo "stub: unexpected \$*" >&2; exit 9; }; exec "$(command -v git)" fetch -q "$t/up" main; fi
exec "$(command -v git)" "\$@"
STUB
# lake: copies what it was given to build; LAKE=fail refuses, LAKE=edit changes the file under the build
cat > "$t/bin/lake" <<'STUB'
#!/bin/bash
f="${2//.//}.lean"; cp "$f" "$BUILT"
case "${LAKE:-}" in fail) exit 1 ;; edit) echo '-- edited' >> "$f" ;; esac
STUB
chmod +x "$t/bin/git" "$t/bin/lake"; export BUILT="$t/built"
pnp() { (cd "$R" && PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:$port" bash tools/pnp.sh "$@") >"$t/out" 2>&1; }
T=$'PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (1 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) @@VALUE@@ ∧\n  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (1 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → @@VALUE@@ ≤ t'
# serve <row json>: the desk's answer for that row; rm the step's old state and files
serve() { printf '%s' "$1" > "$t/row.json"; python3 -c 'import json,sys; print(json.dumps({"gap":json.load(open(sys.argv[1])),"lease":{"id":"abc","expires_at":"2026-11-25T12:00:00Z","terms":{"kind":"value","level":"hard","points":100}}}))' "$t/row.json" > "$t/www/next"; rm -rf "$R/.pnp" "$R/lean"; }
row() { python3 -c 'import json,sys; g={"id":"L-meta-9507","kind":"value","title":"Table 1a","template":sys.argv[1],"value_holes":int(sys.argv[2]),"value_max":4,"size_in_words":"AND, OR and NOT gates","value_max_why":"a 4-gate circuit","file_form":"lean/PEqualNP/Outside/V_meta_9507__k<k>.lean","imports":["PEqualNP.Defs","PEqualNP.Library.LRAT.LinkN2"],"sketch":"s"}; print(json.dumps(g))' "$1" "${2:-2}"; }
# expect <row json file> <k> <file>: the skeleton's statement equals valueGap's, byte for byte, and the theorem names its module
expect() { node --input-type=module -e '
import { valueGap } from "'"$guard"'"; import { readFileSync } from "node:fs";
const [row, k, file] = process.argv.slice(1); const g = JSON.parse(readFileSync(row, "utf8"));
const rel = `lean/PEqualNP/Outside/V_${g.id.slice(2).replace(/-/g, "_")}__k${k}.lean`; const v = valueGap(g, rel, "check");
const mod = "PEqualNP.Outside." + rel.slice("lean/PEqualNP/Outside/".length, -5);
const want = "import Mathlib\n" + v.imports.map((m) => `import ${m}\n`).join("") + `\ntheorem ${mod} : (${v.statement}) := by\n  sorry\n`;
const got = readFileSync(file, "utf8"); if (got !== want) { console.error("FAIL: skeleton differs from the guard\n--- got\n" + got + "--- want\n" + want); process.exit(1); }' "$@"; }
V="$t/repo/lean/PEqualNP/Outside"

# 1. next on a value step writes nothing and prints the template, the bound, the size and the task
serve "$(row "$T")"; pnp next || { cat "$t/out"; echo "FAIL: next"; exit 1; }
grep -q 'GET /next?handle=tester&value=1 ' "$t/access" || { echo "FAIL: next does not say it can take a value step"; cat "$t/access"; exit 1; }
for w in 'VALUE UNIT Find the least value k' 'TEMPLATE' 'VALUE_MAX  4' 'SIZE       AND, OR and NOT gates' 'tools/pnp.sh value L-meta-9507 <k>'; do grep -qF "$w" "$t/out" || { cat "$t/out"; echo "FAIL: next lacks: $w"; exit 1; }; done
[ ! -e "$V" ] || { echo "FAIL: next wrote a file on a value step"; exit 1; }
pnp check L-meta-9507 && { echo "FAIL: check ran before a value was chosen"; exit 1; }; grep -q 'no value chosen yet' "$t/out" || { cat "$t/out"; exit 1; }

# 2. bad k refused, nothing written
for k in 5 03 -1 1e1 ' 3' 3x 99999 ''; do pnp value L-meta-9507 "$k" && { echo "FAIL: k accepted: '$k'"; exit 1; }; [ ! -e "$V" ] || { echo "FAIL: file written for k '$k'"; exit 1; }; done

# 3. k = 3: the skeleton is the guard's statement byte for byte, named V_meta_9507__k3, recorded for check and submit
pnp value L-meta-9507 3 || { cat "$t/out"; echo "FAIL: value 3"; exit 1; }
expect "$t/row.json" 3 "$V/V_meta_9507__k3.lean"
grep -q '^theorem PEqualNP.Outside.V_meta_9507__k3 : (' "$V/V_meta_9507__k3.lean" || { echo "FAIL: theorem name"; exit 1; }
(cd "$t/repo" && python3 -c 'import json,sys; g=json.load(open(".pnp/L-meta-9507.json"))["gap"]; sys.exit(0 if (g["file"], g["module"], g["value"]) == ("lean/PEqualNP/Outside/V_meta_9507__k3.lean", "PEqualNP.Outside.V_meta_9507__k3", 3) else 1)') || { echo "FAIL: not recorded for check and submit"; exit 1; }

# 4. an injected template is refused at next and never written (the desk guards it too)
for bad in "$(row "$T"$'\n#eval IO.println 1')" "$(row 'True) := trivial
run_cmd pure ()
example : (@@VALUE@@ = 0' 1)" "$(row "$T" 3)" "$(row "${T/@@VALUE@@ ≤/@@VALUE@@≤}")" "$(row "$T ∧ @@X@@ = 0")" "$(row "(by run_tac pure ()) = @@VALUE@@" 1)"; do
  serve "$bad"; pnp next && { echo "FAIL: accepted: $bad"; exit 1; }; grep -q REFUSED "$t/out" || { cat "$t/out"; echo "FAIL: no reason"; exit 1; }
  [ ! -e "$t/repo/.pnp/L-meta-9507.json" ] || ! pnp value L-meta-9507 1 || { echo "FAIL: value wrote an injected template"; exit 1; }; [ ! -e "$V" ] || { echo "FAIL: file written"; exit 1; }
done

# 5. comments are stripped outside literals (value and ordinary files alike: tidy is the step check runs)
serve "$(row "$T")"; pnp next; pnp value L-meta-9507 2
cat > "$V/V_meta_9507__k2.lean" <<'LEAN'
import Mathlib
/-! module doc /- nested -/ still doc -/
-- a line comment
theorem PEqualNP.Outside.V_meta_9507__k2 : (1 = 1) := by -- trailing
  have h : "a -- b /- c -/" = "a -- b /- c -/" := rfl /- why
  it holds -/
  have c : '-' = '-' := rfl
  have r : r#"x -- y"# = r#"x -- y"# := rfl
  rfl
LEAN
pnp tidy L-meta-9507 || { cat "$t/out"; echo "FAIL: tidy"; exit 1; }
grep -q 'removed the comments' "$t/out" || { echo "FAIL: no notice"; exit 1; }
cat > "$t/want" <<'LEAN'
import Mathlib

theorem PEqualNP.Outside.V_meta_9507__k2 : (1 = 1) := by
  have h : "a -- b /- c -/" = "a -- b /- c -/" := rfl

  have c : '-' = '-' := rfl
  have r : r#"x -- y"# = r#"x -- y"# := rfl
  rfl
LEAN
cmp -s "$t/want" "$V/V_meta_9507__k2.lean" || { echo "FAIL: tidy result"; diff "$t/want" "$V/V_meta_9507__k2.lean"; exit 1; }
pnp tidy L-meta-9507; [ ! -s "$t/out" ] || { echo "FAIL: notice on a file with no comments"; cat "$t/out"; exit 1; }

# 6. submit on a file already on main: this step's own file (value or ordinary) says it was proved first; a pull request
#    that would change a file of a DIFFERENT step keeps the never-change-main wording.
fresh() { R="$t/$1"; git clone -q "$t/up" "$R"; mkdir -p "$R/tools"; cp "$here/pnp.sh" "$R/tools/"; printf '.pnp/\ntools/\n' >> "$R/.git/info/exclude"; }
proof() { printf 'import Mathlib\n\ntheorem %s : (1 = 1) := rfl\n' "$2" > "$R/$1"; }
check() { pnp check "$1" || { echo "FAIL: check"; cat "$t/out"; exit 1; }; }
submit_says() { pnp submit "$1" && { echo "FAIL: submit went through"; cat "$t/out"; exit 1; }; grep -qF "$2" "$t/out" || { echo "FAIL: submit said:"; cat "$t/out"; exit 1; }; ! grep -qF "$3" "$t/out" || { echo "FAIL: wrong wording"; cat "$t/out"; exit 1; }; }
PROVED='This unit was just proved by someone else, and a recorded proof is final, so this one cannot be sent. You did nothing wrong. Ask the desk for another unit: tools/pnp.sh next'
NEVER='refused: never change a file that is already on main'
serve "$(row "$T")"; fresh r1; pnp next; pnp value L-meta-9507 3; proof lean/PEqualNP/Outside/V_meta_9507__k3.lean PEqualNP.Outside.V_meta_9507__k3; check L-meta-9507
cp "$R/lean/PEqualNP/Outside/V_meta_9507__k3.lean" "$t/up/lean/PEqualNP/Outside/"; git -C "$t/up" add -A; git -C "$t/up" commit -qm proved
submit_says L-meta-9507 "$PROVED" "$NEVER"
fresh r2; python3 -c 'import json; print(json.dumps({"gap":{"id":"L-x-2","title":"t","statement":"1 = 1","file":"lean/PEqualNP/Outside/L_x_2.lean","module":"PEqualNP.Outside.L_x_2","imports":[]},"lease":{"id":"abc","expires_at":"2026-11-25T12:00:00Z"}}))' > "$t/www/next"
pnp next; proof lean/PEqualNP/Outside/L_x_2.lean PEqualNP.Outside.L_x_2; check L-x-2
cp "$R/lean/PEqualNP/Outside/L_x_2.lean" "$t/up/lean/PEqualNP/Outside/"; git -C "$t/up" add -A; git -C "$t/up" commit -qm proved2
submit_says L-x-2 "$PROVED" "$NEVER"
serve "$(row "$T")"; fresh r3; pnp next; pnp value L-meta-9507 2; proof lean/PEqualNP/Outside/V_meta_9507__k2.lean PEqualNP.Outside.V_meta_9507__k2; check L-meta-9507
echo changed > "$R/lean/PEqualNP/Outside/L_x_1.lean"; git -C "$R" commit -qam "touch another step"
submit_says L-meta-9507 "$NEVER" "just proved"
[ ! -e "$t/pushed" ] || { echo "FAIL: a refused submit pushed"; exit 1; }

# 7. what is sent is what was checked: submit needs a check of these exact bytes, and the committed bytes are the built ones
NOT='is not the file that was checked'; F=lean/PEqualNP/Outside/V_meta_9507__k1.lean; M=PEqualNP.Outside.V_meta_9507__k1
serve "$(row "$T")"; fresh r4; pnp next; pnp value L-meta-9507 1; proof "$F" "$M"
submit_says L-meta-9507 "$NOT" "$NEVER"                                                # never checked
printf 'import Mathlib\n-- a note\ntheorem %s : (1 = 1) := rfl -- why\n' "$M" > "$R/$F"; check L-meta-9507
cmp -s "$t/built" "$R/$F" && ! grep -q -- '--' "$t/built" || { echo "FAIL: the build did not see the stripped bytes"; exit 1; }
cp "$R/$F" "$t/good"
echo '-- after' >> "$R/$F"; submit_says L-meta-9507 "$NOT" "$NEVER"                     # a comment added after check
sed 's/1 = 1/2 = 2/' "$t/good" > "$R/$F"; submit_says L-meta-9507 "$NOT" "$NEVER"     # the proof edited after check
cp "$t/good" "$R/$F"; LAKE=fail pnp check L-meta-9507 && { echo "FAIL: a failed build passed"; exit 1; }
submit_says L-meta-9507 "$NOT" "$NEVER"                                                # a failed check withdraws the earlier one
LAKE=edit pnp check L-meta-9507 && { echo "FAIL: a file edited under the build passed"; exit 1; }
grep -q 'changed while it was building' "$t/out" || { cat "$t/out"; echo "FAIL: no reason"; exit 1; }
cp "$t/good" "$R/$F"; submit_says L-meta-9507 "$NOT" "$NEVER"
check L-meta-9507; pnp value L-meta-9507 2; cp "$t/good" "$R/lean/PEqualNP/Outside/V_meta_9507__k2.lean"
submit_says L-meta-9507 "$NOT" "$NEVER"; rm "$R/lean/PEqualNP/Outside/V_meta_9507__k2.lean"; pnp value L-meta-9507 1   # another k, same bytes
printf 'import Mathlib\r\n\r\ntheorem %s : (1 = 1) := rfl\r\n' "$M" > "$R/$F"; git -C "$R" config core.autocrlf input; check L-meta-9507
submit_says L-meta-9507 "the committed $F is not the file that was checked" "$NEVER"   # git rewrote the bytes at commit
git -C "$R" config core.autocrlf false; [ ! -e "$t/pushed" ] || { echo "FAIL: a refused submit pushed"; exit 1; }
cp "$t/good" "$R/$F"; check L-meta-9507; pnp submit L-meta-9507 || true                # the release POST has no server here
grep -q 'push -q -u origin L-meta-9507' "$t/pushed" || { cat "$t/out"; echo "FAIL: a checked file was not sent"; exit 1; }
git -C "$R" cat-file blob "L-meta-9507:$F" | cmp -s - "$t/built" || { echo "FAIL: sent bytes are not the built bytes"; exit 1; }

# 8. a module planted in the folder the script runs from (or on PYTHONPATH) is never loaded, by any command
! grep -n 'python3 -' "$here/pnp.sh" | grep -v 'python3 -I ' || { echo "FAIL: a python3 that is not isolated"; exit 1; }
serve "$(row "$T")"; fresh r5; F=lean/PEqualNP/Outside/V_meta_9507__k1.lean
for m in json re os unicodedata hashlib; do printf 'open(%s, "a").write(%s)\nraise SystemExit(7)\n' "'$t/planted'" "'$m '" > "$R/$m.py"; echo "$m.py" >> "$R/.git/info/exclude"; done
# -B: this control loads the plant on purpose and must leave no __pycache__ behind, so any found below is pnp.sh's own
(cd "$R" && python3 -B -c 'import json') >/dev/null 2>&1 || true; [ -s "$t/planted" ] || { echo "FAIL: the plant does not work, so this proves nothing"; exit 1; }; rm "$t/planted"
export PYTHONPATH="$R"
pnp next || { cat "$t/out"; echo "FAIL: next beside planted modules"; exit 1; }
pnp value L-meta-9507 1 || { cat "$t/out"; echo "FAIL: value beside planted modules"; exit 1; }
printf 'import Mathlib\n-- note\ntheorem PEqualNP.Outside.V_meta_9507__k1 : (1 = 1) := rfl\n' > "$R/$F"
pnp tidy L-meta-9507 || { cat "$t/out"; echo "FAIL: tidy beside planted modules"; exit 1; }
check L-meta-9507; pnp beat L-meta-9507 || true
[ ! -e "$R/__pycache__" ] || { echo "FAIL: pnp.sh wrote a __pycache__ beside planted modules: $(ls "$R/__pycache__")"; exit 1; }
rm -f "$t/pushed"; pnp submit L-meta-9507 || true
[ -s "$t/pushed" ] || { cat "$t/out"; echo "FAIL: submit beside planted modules"; exit 1; }
unset PYTHONPATH
[ ! -e "$t/planted" ] || { echo "FAIL: loaded a planted module: $(cat "$t/planted")"; exit 1; }
R="$t/repo"

# 9. the size: 1 to 524288 bytes, the public guard's own limit; check refuses before lake is called, submit when the file grew
[ "$(node --input-type=module -e 'import { MAX_BYTES } from "'"$guard"'"; console.log(MAX_BYTES)')" = 524288 ] || { echo "FAIL: the public guard's limit is not 524288"; exit 1; }
serve "$(row "$T")"; fresh r6; pnp next; pnp value L-meta-9507 1; proof "$F" PEqualNP.Outside.V_meta_9507__k1; cp "$R/$F" "$t/small"
sized() { cp "$t/small" "$R/$F"; head -c "$(($1 - $(wc -c < "$t/small")))" /dev/zero | tr '\0' '\n' >> "$R/$F"; [ "$(wc -c < "$R/$F")" -eq "$1" ] || { echo "FAIL: test file size"; exit 1; }; }
size_says() { grep -qF "refused: $F is $1 bytes; a proof file must be 1 to 524288 bytes" "$t/out" || { cat "$t/out"; echo "FAIL: size line for $1"; exit 1; }; }
for n in 0 524289; do
  if [ "$n" = 0 ]; then : > "$R/$F"; else sized "$n"; fi
  rm -f "$t/built"; pnp check L-meta-9507 && { echo "FAIL: check took $n bytes"; exit 1; }
  size_says "$n"; [ ! -e "$t/built" ] || { echo "FAIL: lake was called on $n bytes"; exit 1; }
done
{ cat "$t/small"; printf -- '-- '; head -c 600000 /dev/zero | tr '\0' 'x'; echo; } > "$R/$F"; check L-meta-9507   # over the limit only by its comments
rm -f "$t/pushed"; sized 524288; check L-meta-9507; cp "$R/$F" "$t/max"
for n in 0 524289; do
  if [ "$n" = 0 ]; then : > "$R/$F"; else sized "$n"; fi
  pnp submit L-meta-9507 && { echo "FAIL: submit took $n bytes"; exit 1; }; size_says "$n"
done
[ ! -e "$t/pushed" ] || { echo "FAIL: a refused size was pushed"; exit 1; }
cp "$t/max" "$R/$F"; pnp submit L-meta-9507 || true; [ -s "$t/pushed" ] || { cat "$t/out"; echo "FAIL: exactly 524288 bytes was not sent"; exit 1; }
R="$t/repo"

# 10. live: every value row, at k = 0 and k = value_max, matches the guard
if [ -n "${1:-}" ]; then
  n=0; while IFS= read -r -d '' r; do
    serve "$r"; id="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["id"])' "$t/row.json")"; vm="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["value_max"])' "$t/row.json")"
    pnp next || { cat "$t/out"; echo "FAIL: live row refused: $id"; exit 1; }
    for k in 0 "$vm"; do pnp value "$id" "$k" || { cat "$t/out"; echo "FAIL: live value $id $k"; exit 1; }
      expect "$t/row.json" "$k" "$R/$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["gap"]["file"])' "$t/repo/.pnp/$id.json")"; done
    n=$((n+1)); done < <(python3 -c 'import json,sys; [sys.stdout.write(json.dumps(g)+"\0") for g in json.load(open(sys.argv[1]))["gaps"] if g.get("kind") == "value"]' "$1")
  echo "live: $n value rows, each written at 0 and value_max, all equal to the guard's statement"
fi
echo "pnp value: pass"
