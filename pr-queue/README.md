# Upstream PR queue

Branch: `pr-queue`. Keep this branch separate from proof branches.

After locally validating a complete proof:

1. Create a proof branch **from the upstream main commit**, not from the fork's main. Push exactly one commit adding the authorized Lean file.
2. Create a new file on `pr-queue`, for example `pr-queue/requests/L-meta-123-0123456789ab.json`, containing:
   ```json
   {
     "unit": "L-meta-123",
     "branch": "L-meta-123",
     "head_sha": "<40-character SHA of the verified proof commit>",
     "file": "lean/PEqualNP/Outside/L_meta_123.lean",
     "lease": "<live lease ID for this unit>"
   }
   ```
3. A push starts the queue workflow. Keep the lease alive until the result appears under `pr-queue/results/` with the same filename. A successful PR releases its lease as submitted. A failure leaves the proof branch intact; correct the issue and enqueue under a fresh filename.
4. Read the result (PR number, URL, status, and whether release succeeded). The upstream checker gives the authoritative verdict later. Repair a rejected PR on its existing proof branch.

Request files are public; enqueue only after verification, and include no credentials. The lease is the same ID normally published in the PR body. The PAT is read solely from the Actions secret `UPSTREAM_PR_TOKEN`.

The workflow scans all pending files on each queue push, validates the pinned proof head, verifies the exact one-file PR shape and task row, checks the upstream STOP notice, renews the lease, opens an upstream PR, and records the outcome. Duplicate existing PRs are recognized. No proof code runs in the workflow.
