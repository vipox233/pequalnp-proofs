#!/bin/bash
# THE RUNNER READER'S LINUX DIAGNOSTIC (27 Nov; redteam-2 round two, 14:33Z). Team-authored files only: every fixture
# and probe below is written by this script; no outside file, pull request or network answer is read.
#   bash tools/read-diagnostic.sh <base checkout>      (ubuntu-24.04 with passwordless sudo: a GitHub runner)
# It runs the read job's own scripts (tools/read-parse.sh, tools/read-sandbox.sh, tools/read-receipt.sh) and checks:
#   A. real reads: a plain file gives PLAIN, a comment-word file UNION, a column-0-after-by file HOLD with its shape,
#      a control-character file HOLD with CTRL, each as a READ-RECEIPT line;
#   B. the isolation, seen from inside by a probe run in the same sandbox: nobody, cwd /jail, an environment of PATH and
#      LANG only, a root of exactly bin jail lib lib64 proc sbin tmp usr, no /home /opt /etc /var /run, no network,
#      the jail and /usr read only, no capabilities, no new privileges, the limits;
#   C. failure: a probe that exits 3, one that runs past the time limit, one that asks for too much memory and one that
#      prints a forged PLAIN line and then fails: each gives a nonzero status and the fixed HOLD with ERROR;
#   D. the verdict step's accepted tail, taken from the workflow file at this base (its VERDICT line through the RECORD
#      BLOCK END marker) and run under the step shell's errexit and set -u on team-made inputs: read off, read on, and
#      read on with GITHUB_OUTPUT unwritable give the same VERDICT line and exit 0, and a record only in the plain
#      read-on case. (The tail is run outside a job; what a job adds, the runner's own GITHUB_OUTPUT file, is replaced
#      by a plain file, a folder and a missing path, the nearest honest stand-ins.)
# Prints one PASS or FAIL line per check, then "DIAGNOSTIC: PASS (<n> checks)" or "DIAGNOSTIC: FAIL (<k> of <n>)"; exit 0 or 1.
set -u
B=$(cd "$1" && pwd); T="$B/tools"; WD=$(mktemp -d); n=0; bad=0
judge=$(git -C "$B" rev-parse HEAD:tools/check-lean.mjs)
ok() { n=$((n + 1)); if [ "$1" = yes ]; then echo "PASS $2"; else echo "FAIL $2"; bad=$((bad + 1)); fi; }
is() { if eval "$1" > /dev/null 2>&1; then echo yes; else echo no; fi; }
HEAD_TXT='import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside
'
TAIL_TXT='
theorem L_diag_1 : True := trivial

end PEqualNP.Outside'
fixture() { printf '%s\n%s\n%s\n' "$HEAD_TXT" "$2" "$TAIL_TXT" > "$WD/$1.lean"; }
receipt() {   # receipt <name> <out dir>: the read job's last step for a team fixture, its line on stdout
  local f="$WD/$1.lean" o=$2 blob sha
  blob=$(git hash-object "$f"); sha=$(sha256sum "$f" | cut -d' ' -f1); mkdir -p "$o/in"
  printf '%s' "$blob" > "$o/in/pr.blob"; printf '%s' "$(printf c%.0s $(seq 40))" > "$o/in/pr.head"; printf '%s' "lean/PEqualNP/Outside/L_diag_1.lean" > "$o/in/pr.file"
  CHECK_RECORD=$(jq -cn --arg b "$blob" --arg s "$sha" --arg h "$(cat "$o/in/pr.head")" '{pr: 1, gap: "L-diag-1", kind: "check", file: "lean/PEqualNP/Outside/L_diag_1.lean", head: $h, blob: $b, file_sha256: $s,
    statement_sha256: ("d" * 64), manifest_sha256: ("e" * 64), children: 0, children_sha256: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", last_sha256: ("f" * 64), verdict: "ACCEPTED"}') \
  PR=1 GAP=L-diag-1 GITHUB_REPOSITORY=${GITHUB_REPOSITORY:-open-goat/pequalnp-proofs} GITHUB_RUN_ID=${GITHUB_RUN_ID:-1} GITHUB_RUN_ATTEMPT=${GITHUB_RUN_ATTEMPT:-1} \
  GITHUB_SHA=$(git -C "$B" rev-parse HEAD) bash "$T/read-receipt.sh" "$o/decision.json" "$o/status" "$f" "$o/in" "$B" | sed -n 's/^READ-RECEIPT //p'
}

# A. real reads
fixture plain 'theorem a : 1 = 1 := rfl'
fixture union 'theorem a : 1 = 1 := rfl -- by the structure of the sum'
fixture held 'theorem b : 1 = 1 := by
rfl'
printf '%s\ntheorem a : 1 = 1 := rfl -- by the structure\001\n%s\n' "$HEAD_TXT" "$TAIL_TXT" > "$WD/ctrl.lean"
for x in plain union held ctrl; do
  bash "$T/read-parse.sh" "$T" "$WD/$x.lean" "$judge" "$WD/out-$x" > /dev/null
  echo "$(receipt "$x" "$WD/out-$x")" > "$WD/rc-$x.json"
done
ok "$(is '[ "$(cat $WD/out-plain/status)" = 0 ] && jq -e ".decision == \"PLAIN\"" $WD/rc-plain.json')" "A1 a plain file reads PLAIN through the sandbox"
ok "$(is 'jq -e ".decision == \"UNION\" and .classes == [\"comment-word\"]" $WD/rc-union.json')" "A2 a comment-word file reads UNION"
ok "$(is 'jq -e ".decision == \"HOLD\" and (.shapes | index([[7, \"COL0\", \"ident\", \"kw:by\"]]) != null)" $WD/rc-held.json')" "A3 a column-0 line after by reads HOLD with its shape"
ok "$(is 'jq -e ".decision == \"HOLD\" and ([.shapes[][1]] | index(\"CTRL\") != null)" $WD/rc-ctrl.json')" "A4 a control character holds the whole file"
ok "$(is 'jq -e ".producer | length == 7" $WD/rc-plain.json')" "A5 the receipt names the seven producer objects"

# B. the isolation, from inside (a probe in place of the classifier, in the same sandbox)
probe() {   # probe <name> <python body>: a jail whose classifier is the probe, through read-parse.sh
  mkdir -p "$WD/p-$1"; printf '%s\n' "$2" > "$WD/p-$1/read-decision.py"; cp "$T/outside-read.py" "$WD/p-$1/"; cp "$T/read-sandbox.sh" "$WD/p-$1/"
  bash "$T/read-parse.sh" "$WD/p-$1" "$WD/plain.lean" "$judge" "$WD/q-$1" > /dev/null
}
probe look 'import json, os, socket, resource, sys
def can(f):
    try: f(); return True
    except BaseException: return False
try: st = dict(l.split(":", 1) for l in open("/proc/self/status").read().splitlines() if ":" in l)
except OSError: st = {}
def net():
    s = socket.socket(); s.settimeout(3); s.connect(("140.82.112.3", 443))
def w(p):
    with open(p, "w") as h: h.write("x")
print(json.dumps({"uid": os.getuid(), "gid": os.getgid(), "cwd": os.getcwd(), "env": sorted(os.environ), "root": sorted(os.listdir("/")),
  "hidden": [p for p in ("/home", "/opt", "/etc", "/var", "/run", "/root", "/mnt", "/srv", "/usr/local/bin/gh") if os.path.exists(p)],
  "net": can(net), "write_jail": can(lambda: w("/jail/x")), "write_usr": can(lambda: w("/usr/x")), "write_tmp": can(lambda: w("/tmp/x")),
  "capeff": st.get("CapEff", "").strip(), "nnp": st.get("NoNewPrivs", "").strip(),
  "as": resource.getrlimit(resource.RLIMIT_AS)[0], "cpu": resource.getrlimit(resource.RLIMIT_CPU)[0], "fsize": resource.getrlimit(resource.RLIMIT_FSIZE)[0],
  "nofile": resource.getrlimit(resource.RLIMIT_NOFILE)[0], "argv": sys.argv[1:2], "pid1": os.getppid() <= 3}))'
L="$WD/q-look/decision.json"
ok "$(is '[ "$(cat $WD/q-look/status)" = 0 ] && jq -e . '"$L")" "B0 the probe ran in the sandbox"
ok "$(is 'jq -e ".uid == 65534 and .gid == 65534" '"$L")" "B1 nobody"
ok "$(is 'jq -e ".cwd == \"/jail\"" '"$L")" "B2 the working directory is the jail"
ok "$(is 'jq -e ".env == [\"LANG\", \"PATH\"]" '"$L")" "B3 the environment is PATH and LANG only"
ok "$(is 'jq -e "(.root - [\"bin\",\"jail\",\"lib\",\"lib64\",\"proc\",\"sbin\",\"tmp\",\"usr\"]) == [] and .hidden == []" '"$L")" "B4 the root is restricted; host areas absent"
ok "$(is 'jq -e ".net == false" '"$L")" "B5 no network"
ok "$(is 'jq -e ".write_jail == false and .write_usr == false and .write_tmp == true" '"$L")" "B6 the jail and /usr are read only"
ok "$(is 'jq -e ".capeff == \"0000000000000000\" and .nnp == \"1\"" '"$L")" "B7 no capabilities, no new privileges"
ok "$(is 'jq -e ".as == 1073741824 and .cpu == 60 and .fsize == 65536 and .nofile == 64" '"$L")" "B8 the limits"
ok "$(is 'jq -e ".argv == [\"/jail/in/proof.lean\"]" '"$L")" "B9 the parser gets the jailed file"

# C. failure gives a nonzero status and the fixed ERROR hold, whatever was printed
probe exit 'import sys; sys.exit(3)'
probe slow 'import time; time.sleep(200)'
probe mem 'x = bytearray(2 * 1024 ** 3); print(len(x))'
probe forged 'import json, sys
print(json.dumps({"classifier": "rd-1", "authorized": ["comment-word", "continuation", "instance", "lookalike"], "decision": "PLAIN", "classes": [], "shapes": [], "nshapes": 0}, separators=(",", ":")))
sys.stdout.flush(); sys.exit(1)'
for x in exit slow mem forged; do
  echo "$(receipt plain "$WD/q-$x")" > "$WD/rc-$x.json"
  ok "$(is '[ "$(cat $WD/q-'"$x"'/status)" != 0 ] && jq -e ".decision == \"HOLD\" and .shapes == [[0, \"ERROR\", \"empty\", \"empty\"]]" '"$WD/rc-$x.json")" "C-$x a failing parse gives status $(cat "$WD/q-$x/status") and the ERROR hold"
done

# D. the verdict step's accepted tail, from the workflow's own text
WF="$B/.github/workflows/authoritative.yml"
awk '/echo "VERDICT: \$verdict \(checker exit \$CODE\)"/{on=1} on{print substr($0, 11)} /# RECORD BLOCK END/{if(on) exit}' "$WF" > "$WD/tail.sh"
tailrun() {   # tailrun <read> <GITHUB_OUTPUT path> <name>: prints the VERDICT line, the exit and the record count
  local d="$WD/tail-$3"; mkdir -p "$d/in"
  printf '%s' "$(printf c%.0s $(seq 40))" > "$d/in/pr.head"; printf '%s' "$(printf b%.0s $(seq 40))" > "$d/in/pr.blob"; printf check > "$d/in/gap.kind"
  printf 'MANIFEST {"lemma":"L-diag-1"}\nACCEPTED (check) fine\n' > "$d/checker.out"
  out=$(env READ="$1" W="$d" RUNNER_TEMP="$d" PR=1 GAP=L-diag-1 CODE=0 GITHUB_OUTPUT="$2" GITHUB_STEP_SUMMARY="$d/summary" \
        bash -c 'set -eu; verdict=ACCEPTED; last="ACCEPTED (check) fine"; file=lean/PEqualNP/Outside/L_diag_1.lean; children=0
                 fsha=$(printf 1%.0s $(seq 64)); ssha=$(printf 2%.0s $(seq 64)); . "$0"; echo NOT-REACHED; exit 9' "$WD/tail.sh" 2>/dev/null); rc=$?
  if [ -f "$2" ]; then recs=$(grep -c '^record={' "$2" || true); else recs=0; fi
  echo "$out|$rc|$recs"
}
: > "$WD/go-off"; : > "$WD/go-on"; mkdir -p "$WD/go-dir"
D_OFF=$(tailrun "" "$WD/go-off" off); D_ON=$(tailrun on "$WD/go-on" on); D_DIR=$(tailrun on "$WD/go-dir" dir); D_MISS=$(tailrun on "$WD/none/out" miss)
ok "$(is '[ -s $WD/tail.sh ] && grep -q "RECORD BLOCK END" $WD/tail.sh')" "D0 the accepted tail was taken from the workflow at this base"
ok "$(is '[ "$D_OFF" = "VERDICT: ACCEPTED (checker exit 0)|0|0" ]')" "D1 read off: the VERDICT line, exit 0, no record"
ok "$(is '[ "$D_ON" = "VERDICT: ACCEPTED (checker exit 0)|0|1" ]')" "D2 read on: the same VERDICT line, exit 0, one record"
ok "$(is '[ "$D_DIR" = "VERDICT: ACCEPTED (checker exit 0)|0|0" ] && [ "$D_MISS" = "VERDICT: ACCEPTED (checker exit 0)|0|0" ]')" "D3 read on, output unwritable: the same VERDICT line, exit 0, no record"

if [ "$bad" = 0 ]; then echo "DIAGNOSTIC: PASS ($n checks)"; exit 0; fi
echo "DIAGNOSTIC: FAIL ($bad of $n)"; exit 1
