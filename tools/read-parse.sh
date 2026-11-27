#!/bin/bash
# THE PARSE, as the read job runs it (27 Nov; round two 14:33Z). One home for the workflow and the Linux diagnostic:
#   read-parse.sh <classifier tools dir> <proof.lean> <judge blob> <out dir>
# Builds a fresh jail in <out dir>/jail with a read-only copy of the two classifier files and the one file, runs
# tools/read-sandbox.sh (from the same tools dir) under sudo with an empty environment, and writes <out>/decision.json
# (the sandbox's standard output; its errors are dropped) and <out>/status. The status is taken by an explicit
# conditional, so a failing sandbox is recorded as its nonzero status and never stops this script before the write;
# tools/read-receipt.sh turns any status but 0 into the fixed HOLD with ERROR. This script itself always exits 0.
set -u
t=$1; f=$2; judge=$3; out=$4; J="$out/jail"
mkdir -p "$out"; : > "$out/decision.json"; echo none > "$out/status"
if { [ ! -e "$J" ] || chmod -R u+w "$J"; } && rm -rf "$J" && mkdir -p "$J/tools" "$J/in" \
   && cp "$t/read-decision.py" "$t/outside-read.py" "$J/tools/" && cp "$f" "$J/in/proof.lean" \
   && chmod 0444 "$J/tools/read-decision.py" "$J/tools/outside-read.py" "$J/in/proof.lean" && chmod 0555 "$J/tools" "$J/in" "$J"; then
  if sudo -n /usr/bin/env -i PATH=/usr/bin:/bin /bin/sh "$t/read-sandbox.sh" "$J" "$judge" > "$out/decision.json" 2>/dev/null; then rc=0; else rc=$?; fi
else rc=jail; fi
echo "$rc" > "$out/status"
echo "parse exit $rc"
exit 0
