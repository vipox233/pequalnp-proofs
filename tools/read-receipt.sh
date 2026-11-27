#!/bin/bash
# THE READ RECEIPT (27 Nov; reviews 14:20Z/14:21Z), the read job's last step. Our values only:
#   read-receipt.sh <decision.json> <parse status file> <proof.lean> <in dir> <base checkout>
# with GITHUB_REPOSITORY, PR, GAP, GITHUB_RUN_ID, GITHUB_RUN_ATTEMPT, GITHUB_SHA set by the runner and CHECK_RECORD
# from the check job's output. Prints ONE line, the receipt, canonical JSON of at most 8192 bytes:
#   READ-RECEIPT {"authorized":...,"check":{...},...,"producer":{...},...}
# 1. No receipt (exit 1) unless the run values, the identity this job read, the bytes (their blob again) and the check
#    record all agree: the record must be ACCEPTED for this pull request, gap, file, head and blob, and its file_sha256
#    (hashed by the check job before its outside step) must be the sha256 of the bytes read here.
# 2. The parse's line is taken only when its status is 0 and it is ONE line of at most 8192 bytes whose every field is
#    a word of read-decision.py --vocab (run here with no data); anything else becomes the fixed HOLD with ERROR.
# 3. producer: the git object of every file that made this receipt, at this base, for the intake's allowlist.
set -eu
d=$1; st=$2; f=$3; in=$4; base=$5
printf '%s %s %s %s %s %s' "$PR" "$GITHUB_RUN_ID" "$GITHUB_RUN_ATTEMPT" "$GITHUB_SHA" "$GITHUB_REPOSITORY" "$GAP" \
  | grep -Eqx '[1-9][0-9]{0,6} [1-9][0-9]{0,15} [1-9][0-9]{0,3} [0-9a-f]{40} [A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+ L-[a-z0-9]+(-[a-z0-9]+)*' \
  || { echo "READ-JOB: malformed run values; no receipt"; exit 1; }
blob=$(cat "$in/pr.blob"); head=$(cat "$in/pr.head"); path=$(cat "$in/pr.file")
printf '%s %s' "$blob" "$head" | grep -Eqx '[0-9a-f]{40} [0-9a-f]{40}' || { echo "READ-JOB: malformed identity; no receipt"; exit 1; }
printf '%s' "$path" | grep -Eqx 'lean/PEqualNP/Outside/[A-Za-z0-9_]{1,200}\.lean' || { echo "READ-JOB: malformed path; no receipt"; exit 1; }
[ "$(git hash-object "$f")" = "$blob" ] || { echo "READ-JOB: the bytes are not the named blob; no receipt"; exit 1; }
sha=$(sha256sum "$f" | cut -d' ' -f1)
[ "${#CHECK_RECORD}" -le 2000 ] && printf '%s' "$CHECK_RECORD" | jq -e --argjson pr "$PR" --arg gap "$GAP" --arg path "$path" --arg head "$head" --arg blob "$blob" --arg sha "$sha" '
    def h64: type == "string" and test("^[0-9a-f]{64}$");
    (keys == ["blob","children","children_sha256","file","file_sha256","gap","head","kind","last_sha256","manifest_sha256","pr","statement_sha256","verdict"])
    and .verdict == "ACCEPTED" and .pr == $pr and .gap == $gap and .file == $path and .head == $head and .blob == $blob and .file_sha256 == $sha
    and (.kind | IN("check","refute","reduce")) and (.statement_sha256 | h64) and (.manifest_sha256 | h64) and (.children_sha256 | h64) and (.last_sha256 | h64)
    and (.children | type == "number" and floor == .) and (if .kind == "reduce" then (.children >= 2 and .children <= 4) else .children == 0 end)' > /dev/null 2>&1 \
  || { echo "READ-JOB: the check record is missing, not ACCEPTED, or names other bytes; no receipt"; exit 1; }
vocab=$(mktemp); trap 'rm -f "$vocab"' EXIT
python3 -I -S "$base/tools/read-decision.py" --vocab > "$vocab"
ok=no
if [ "$(cat "$st" 2>/dev/null)" = 0 ] && [ -f "$d" ] && [ "$(wc -l < "$d")" -eq 1 ] && [ "$(wc -c < "$d")" -le 8192 ] && jq -e --slurpfile v "$vocab" '
     def tok: type == "string" and (. as $t | $v[0].tokens | index([$t]) != null);
     def code: type == "string" and length <= 64 and (split("+") | length >= 1 and all(. as $c | $v[0].codes | index([$c]) != null));
     (.shapes | if type == "array" then length else 0 end) as $n
     | (keys == ["authorized","classes","classifier","decision","nshapes","shapes"])
     and .classifier == $v[0].classifier and .authorized == $v[0].authorized
     and (.decision | IN("PLAIN","UNION","HOLD"))
     and (.classes | type == "array" and length <= 4 and all(. as $c | $v[0].authorized | index([$c]) != null))
     and (.shapes | type == "array" and length <= $v[0].max_shapes
          and all(type == "array" and length == 4 and (.[0] | type == "number" and . >= 0 and . <= $v[0].max_count and floor == .)
                  and (.[1] | code) and (.[2] | tok) and (.[3] | tok)))
     and (.nshapes | type == "number" and . >= $n and . <= $v[0].max_count and floor == .)
     and ((.decision == "PLAIN" and .classes == [] and .shapes == [])
          or (.decision == "UNION" and (.classes | length) >= 1 and .shapes == [])
          or (.decision == "HOLD" and .classes == [] and (.shapes | length) >= 1))' "$d" > /dev/null 2>&1; then ok=yes; fi
if [ "$ok" = yes ]; then dec=$(jq -c . "$d"); else
  dec=$(jq -cn --slurpfile v "$vocab" '{classifier: $v[0].classifier, authorized: $v[0].authorized, decision: "HOLD", classes: [], shapes: [[0, "ERROR", "empty", "empty"]], nshapes: 1}')
fi
producer='{}'
for p in .github/workflows/authoritative.yml .github/scripts/outside-guard.mjs tools/read-decision.py tools/outside-read.py tools/read-receipt.sh tools/read-sandbox.sh tools/read-parse.sh; do
  o=$(git -C "$base" rev-parse "HEAD:$p"); printf '%s' "$o" | grep -Eqx '[0-9a-f]{40}' || { echo "READ-JOB: a producer file is missing; no receipt"; exit 1; }
  producer=$(printf '%s' "$producer" | jq -c --arg p "$p" --arg o "$o" '. + {($p): $o}')
done
line=$(printf '%s' "$dec" | jq -cS --arg repo "$GITHUB_REPOSITORY" --argjson pr "$PR" --arg head "$head" --arg path "$path" --arg blob "$blob" \
  --arg sha "$sha" --argjson run "$GITHUB_RUN_ID" --argjson attempt "$GITHUB_RUN_ATTEMPT" --arg base "$GITHUB_SHA" \
  --argjson producer "$producer" --argjson check "$CHECK_RECORD" \
  '{v: 2, job: "read", repo: $repo, pr: $pr, head: $head, path: $path, blob: $blob, sha256: $sha, run_id: $run, run_attempt: $attempt,
    base: $base, producer: $producer, check: $check, classifier: .classifier, authorized: .authorized,
    decision: .decision, classes: .classes, shapes: .shapes, nshapes: .nshapes}')
[ "${#line}" -le 8192 ] || { echo "READ-JOB: the receipt is over its bound; no receipt"; exit 1; }
echo "READ-RECEIPT $line"
