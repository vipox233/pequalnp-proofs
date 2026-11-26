#!/usr/bin/env bash
# Run: bash tools/test_pnp_next_unit.sh
# next --unit <id> asks the desk for that exact unit on the same next request (gap=<id>, the model as always): leased,
# the unit's file is written as by next; not leased, the desk's reason is printed, nothing is written, and it exits
# non-zero. A bad id is refused before any request, and --unit with --proof-of is refused. Offline: a loopback desk
# that answers as told; gh is a stub.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; t="$(mktemp -d)"; srv=; trap 'kill $srv 2>/dev/null || true; wait $srv 2>/dev/null || true; rm -rf "$t"' EXIT
mkdir -p "$t/bin"; export LOG="$t/log" MODE="$t/mode"; echo grant > "$MODE"; : > "$LOG"
port=$((20000 + RANDOM % 20000))
python3 - "$port" <<'PY' & srv=$!
import json, os, sys
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def send(self, body):
        self.send_response(200); self.send_header("Content-Type", "application/json"); self.send_header("Content-Length", str(len(body))); self.end_headers(); self.wfile.write(body)
    def do_GET(self):
        if self.path == "/": return self.send(b"{}")
        open(os.environ["LOG"], "a").write("GET " + self.path + "\n")
        m = open(os.environ["MODE"]).read().strip()
        if m == "empty60": return self.send(json.dumps({"gap": None, "retry_after_s": 60}).encode())
        if m == "emptynote": return self.send(json.dumps({"gap": None, "note": "Every unit is taken.", "retry_after_s": 60}).encode())
        if m == "emptybad": return self.send(json.dumps({"gap": None, "retry_after_s": 99999}).encode())
        if m == "emptystr": return self.send(json.dumps({"gap": None, "retry_after_s": "60; rm -rf"}).encode())
        if m == "no":
            return self.send(json.dumps({"gap": None, "note": "That unit is held by another agent until 12:30 UTC.\x1b[31m", "retry_after_s": 900}).encode())
        return self.send(json.dumps({"gap": {"id": "L-x-7", "title": "t", "statement": "1 = 1", "file": "lean/PEqualNP/Outside/L_x_7.lean", "module": "PEqualNP.Outside.L_x_7", "imports": []},
                                     "lease": {"id": "abc", "expires_at": "2099-01-01T00:00:00Z"}}).encode())
ThreadingHTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
PY
for _ in $(seq 50); do curl -s "http://127.0.0.1:$port/" >/dev/null && break; sleep 0.1; done
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t GIT_ALLOW_PROTOCOL=file
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0="url.$t/no-host.git.insteadOf" GIT_CONFIG_VALUE_0="https://github.com/open-goat/pequalnp-proofs.git"
printf '#!/bin/sh\necho tester\n' > "$t/bin/gh"; chmod +x "$t/bin/gh"
R="$t/repo"; git init -q "$R"; mkdir -p "$R/tools"; cp "$here/pnp.sh" "$R/tools/"
pnp() { set +e; (cd "$R" && PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:$port" PNP_MODEL=claude-opus-5.5 /bin/bash tools/pnp.sh "$@") >"$t/out" 2>"$t/err"; rc=$?; set -e; }
fail() { echo "FAIL $1"; cat "$t/out" "$t/err" "$LOG"; exit 1; }
# 1. leased: the query carries the model and gap=<id>; the unit's state and skeleton are written
pnp next --unit L-x-7; [ "$rc" = 0 ] || fail "leased: exit $rc"
grep -qx 'GET /next?handle=tester&value=1&model=claude-opus-5.5&gap=L-x-7' "$LOG" || fail "leased: the query"
[ -f "$R/.pnp/L-x-7.json" ] && [ -f "$R/lean/PEqualNP/Outside/L_x_7.lean" ] || fail "leased: nothing written"
echo "ok leased"
# 2. not leased: the desk's reason, cleaned, nothing written, a non-zero exit
rm -rf "$R/.pnp" "$R/lean"; echo no > "$MODE"; : > "$LOG"
pnp next --unit L-x-7; [ "$rc" = 4 ] || fail "not leased: exit $rc, not 4"
grep -qxF 'not leased: That unit is held by another agent until 12:30 UTC.[31m' "$t/out" || fail "not leased: the reason"
! grep -q $'\x1b' "$t/out" || fail "not leased: a control character printed"
[ ! -e "$R/.pnp/L-x-7.json" ] && [ ! -e "$R/lean" ] || fail "not leased: something was written"
echo "ok not leased"
# 3. a bad id is refused before any request; --unit with --proof-of is refused
: > "$LOG"
for bad in 'L-x-7&hard=1' '../x' 'L-X-7' ''; do pnp next --unit "$bad"; [ "$rc" = 1 ] && grep -qx -- '--unit needs a unit id, e.g. L-meta-1629' "$t/err" || fail "bad id [$bad]"; done
pnp next --unit L-x-7 --proof-of L-x-7; [ "$rc" = 1 ] && grep -qx 'give --unit or --proof-of, not both: --proof-of brings a proof you already have, --unit takes a unit to prove' "$t/err" || fail "both"
[ ! -s "$LOG" ] || fail "a request was sent for a refused call"
echo "ok refused before any request"
# 4. a plain empty next names the desk's wait in seconds (a whole number from 1 to 3600 only) and exits 0; anything else
#    in that field gives the old sentence; an exact-unit take with no lease is unchanged (case 2)
for mode in empty60 emptynote emptybad emptystr; do echo "$mode" > "$MODE"; rm -rf "$R/.pnp"; pnp next; [ "$rc" = 0 ] || fail "$mode: exit $rc"
  case "$mode" in
    empty60) [ "$(cat "$t/out")" = 'no unit right now; ask again in about 60 seconds' ] || fail "$mode: said" ;;
    emptynote) [ "$(cat "$t/out")" = $'Every unit is taken.\nno unit right now; ask again in about 60 seconds' ] || fail "$mode: said" ;;
    *) [ "$(cat "$t/out")" = 'no unit right now; ask again in a few minutes' ] || fail "$mode: said" ;;
  esac
  [ ! -e "$R/.pnp/L-x-7.json" ] || fail "$mode: something was written"
done
echo "ok a plain empty next names the wait"
echo "pnp next unit: pass"
