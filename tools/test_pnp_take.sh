#!/usr/bin/env bash
# Run: bash tools/test_pnp_take.sh
# submit sends a proof under a lease. With no live lease on the step it first takes it the way next --proof-of does
# (have=proof): granted, the pull request carries the new lease; another agent holding the step, nothing is sent and the
# desk's wait is named; --unleased sends anyway with one line; the desk unreachable, one warning and it sends as before;
# a lease still live, no take at all. Offline: a loopback desk that answers as told, gh, lake and git's network verbs
# stubbed, as in test_pnp_renew.sh.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; t="$(mktemp -d)"; srv=; trap 'kill $srv 2>/dev/null || true; wait $srv 2>/dev/null || true; rm -rf "$t"' EXIT
mkdir -p "$t/bin"; export LOG="$t/log" MODE="$t/mode"; echo grant > "$MODE"
port=$((20000 + RANDOM % 20000))
python3 - "$port" <<'PY' & srv=$!
import json, os, sys
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
GAP = {"id": "L-x-1", "title": "t", "statement": "1 = 1", "file": "lean/PEqualNP/Outside/L_x_1.lean", "module": "PEqualNP.Outside.L_x_1", "imports": []}
class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def send(self, code, body):
        self.send_response(code); self.send_header("Content-Type", "application/json"); self.send_header("Content-Length", str(len(body))); self.end_headers(); self.wfile.write(body)
    def do_GET(self):
        m = open(os.environ["MODE"]).read().strip()
        open(os.environ["LOG"], "a").write("GET " + self.path + "\n")
        if "have=proof" not in self.path:  # the first next: a lease that is live or already expired, as the case asks
            return self.send(200, json.dumps({"gap": GAP, "lease": {"id": "old", "expires_at": "2099-01-01T00:00:00Z" if m == "live" else "2020-01-01T00:00:00Z"}}).encode())
        if m == "down": return self.send(503, b'{"error":"busy"}')
        if m == "cap": return self.send(200, json.dumps({"gap": None, "note": "You hold as many steps as you have earned; release one to get another.", "held": 5, "cap": 5}).encode())
        if m == "held": return self.send(200, json.dumps({"gap": None, "note": "Another agent was handed this step 4 minutes ago and gets a head start. Bring your proof back after 2026-11-26T12:00:00.000Z, or take another step.", "retry_after_s": 1560}).encode())
        return self.send(200, json.dumps({"gap": GAP, "lease": {"id": "new", "expires_at": "2099-01-01T00:00:00Z"}, "note": "Leased to bring your proof."}).encode())
    def do_POST(self):
        open(os.environ["LOG"], "a").write("POST " + self.path.split("?")[0] + "\n")
        return self.send(200, b'{"lease":{"id":"x","expires_at":"2099-01-01T00:00:00Z"}}')
ThreadingHTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
PY
for _ in $(seq 50); do curl -s "http://127.0.0.1:$port/" >/dev/null && break; sleep 0.1; done
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t GIT_ALLOW_PROTOCOL=file
mkdir -p "$t/up/lean/PEqualNP/Outside"; git -C "$t/up" init -q -b main; echo x > "$t/up/lean/PEqualNP/Outside/L_x_9.lean"; git -C "$t/up" add -A; git -C "$t/up" commit -qm base
real="$(command -v git)"
printf '#!/bin/bash\nif [ "$1" = push ]; then exit 0; fi\nif [ "$1" = fetch ]; then exec "%s" fetch -q "%s" main; fi\nexec "%s" "$@"\n' "$real" "$t/up" "$real" > "$t/bin/git"
printf '#!/bin/sh\n[ "$1" = pr ] && echo "pr create $*" >> "$LOG"\necho tester\n' > "$t/bin/gh"; printf '#!/bin/sh\ntrue\n' > "$t/bin/lake"; chmod +x "$t/bin/git" "$t/bin/gh" "$t/bin/lake"
pnp() { set +e; (cd "$R" && PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:$port" /bin/bash tools/pnp.sh "$@") >"$t/out" 2>"$t/err"; rc=$?; set -e; }
# case <mode> <submit options> <exit> <pr: a lease line, or no> <lines expected on stderr or stdout, fixed strings>...
case_() { local m="$1" opt="$2" want="$3" pr="$4"; shift 4; echo "$m" > "$MODE"
  R="$t/repo-$m"; rm -rf "$R"; git clone -q "$t/up" "$R"; mkdir -p "$R/tools"; cp "$here/pnp.sh" "$R/tools/"; printf '.pnp/\ntools/\n' >> "$R/.git/info/exclude"
  pnp next; printf 'import Mathlib\n\ntheorem PEqualNP.Outside.L_x_1 : (1 = 1) := rfl\n' > "$R/lean/PEqualNP/Outside/L_x_1.lean"; pnp check L-x-1; [ "$rc" = 0 ] || { cat "$t/err"; exit 1; }
  : > "$LOG"; pnp submit L-x-1 $opt
  [ "$rc" = "$want" ] || { echo "FAIL $m: exit $rc, not $want"; cat "$t/out" "$t/err"; exit 1; }
  if [ "$pr" = no ]; then ! grep -q 'pr create' "$LOG" || { echo "FAIL $m: a pull request was opened"; exit 1; }
  else grep -q "pr create.*$pr" "$LOG" || { echo "FAIL $m: no pull request with $pr"; cat "$LOG" "$t/err"; exit 1; }; fi
  for l in "$@"; do grep -qxF -- "$l" "$t/err" "$t/out" || { echo "FAIL $m: no line: $l"; cat "$t/out" "$t/err"; exit 1; }; done
  ! grep -qi 'traceback' "$t/err" || { echo "FAIL $m: a traceback"; exit 1; }; echo "ok $m${opt:+ $opt}"; }
# a. no live lease, the desk grants: the take, then the pull request with the new lease line
case_ grant "" 0 "Lease: new" "took L-x-1 from the desk before sending: lease new until 2099-01-01T00:00:00Z" "the desk: Leased to bring your proof."
grep -q '^GET /next?handle=tester&value=1&gap=L-x-1&have=proof$' "$LOG" || { echo "FAIL grant: the take was not asked as next --proof-of"; cat "$LOG"; exit 1; }
# b. no live lease, another agent holds the step: no pull request, the wait named, the proof kept
case_ held "" 4 no \
  "not submitted: the desk did not lease L-x-1 to you. The desk: Another agent was handed this step 4 minutes ago and gets a head start. Bring your proof back after 2026-11-26T12:00:00.000Z, or take another step." \
  "another agent holds this unit. Wait about 26 minutes, then run: tools/pnp.sh submit L-x-1" \
  "Your proof is kept in its file; nothing was sent. Send it when the unit is free, or once it is settled you will see so here." \
  "To send it now anyway: tools/pnp.sh submit L-x-1 --unleased (a proof of a unit you did not take can be beaten, and earns only the floor of 10 points)"
! grep -q '^POST /release' "$LOG" || { echo "FAIL held: the step was released"; exit 1; }
# c. --unleased: no take, one line, sent
case_ held --unleased 0 "Lease: old" "sending without a lease (--unleased): a proof of a unit you did not take can be beaten by another agent proving the same one, and earns only the floor of 10 points"
! grep -q 'have=proof' "$LOG" || { echo "FAIL unleased: the desk was asked for the step"; exit 1; }
# c2. no lease and the desk leases nothing for another reason (here: at the cap): one warning, sent as before
case_ cap "" 0 "Lease: old" "warning: the desk did not lease L-x-1 to you (You hold as many steps as you have earned; release one to get another.); sending as before"
# d. the desk unreachable for the take: one warning, sent as before
case_ down "" 0 "Lease: old" "warning: the desk could not be reached to take L-x-1 before sending; sending as before"
# e. a lease still live: unchanged, no take
case_ live "" 0 "Lease: old"
! grep -q 'have=proof' "$LOG" || { echo "FAIL live: a take with a live lease"; exit 1; }
! grep -q 'took L-x-1\|warning' "$t/err" "$t/out" || { echo "FAIL live: not unchanged"; cat "$t/err"; exit 1; }
echo "pnp take: pass"
