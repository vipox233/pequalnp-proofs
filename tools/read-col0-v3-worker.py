"""Evaluate the main baseline and archived reviewed candidate inside the jail."""
import hashlib
import json
from pathlib import Path
import runpy
import sys


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode('ascii')


def verify(condition):
    if not condition:
        raise ValueError


def evaluate(path, judge, context, baseline, candidate):
    raw = path.read_bytes()
    verify(0 < len(raw) <= 524288)
    ordinary = baseline['decide'](str(path), judge)
    verify(ordinary[0] == 'HOLD' and ordinary[1] == [])
    rows = ordinary[2]
    verify(any(n > 0 and 'COL0' in code.split('+') for n, code, _, _ in rows))
    verify(hashlib.sha256(canonical(ordinary)).hexdigest() == context['inventory'])

    got, archived = candidate['assess'](raw)
    verify(candidate['result'](got, archived, judge) == ordinary)
    fallback, classes, _ = candidate['result'](got, [], judge)
    eligible = fallback != 'HOLD' and all(
        n > 0 and (code, first, prev) == ('COL0', 'ident', 'sym')
        for n, code, first, prev in rows
    )
    run, attempt, stem = (context[key] for key in ('run', 'attempt', 'stem'))
    trial = candidate['decision']([str(path), judge, '--rd-2', run, attempt, stem], 'rd-2')
    state = candidate['state'](*ordinary)
    verify(trial['binding'] == [run, attempt, hashlib.sha256(raw).hexdigest(),
                               hashlib.sha256(('PEqualNP.Outside.' + stem).encode()).hexdigest()])
    actual = {key: trial[key] for key in state}
    if actual == state:
        verify(trial['baseline'] == hashlib.sha256(canonical(state)).hexdigest())
        return 1 if eligible else 0
    expected = candidate['state']('UNION', sorted([*classes, candidate['STRUCTURAL']]), [])
    verify(eligible and actual == expected and trial['baseline'] == state)
    return 2


if __name__ == '__main__':
    try:
        root = Path(__file__).resolve().parent
        proof, judge = sys.argv[1:]
        baseline = runpy.run_path(str(root / '../baseline/read-decision.py'))
        candidate = runpy.run_path(str(root / 'read-decision.py'))
        context = json.loads((root / '../in/context.json').read_bytes())
        sys.stdout.write(f'{evaluate(Path(proof), judge, context, baseline, candidate)}\n')
    except Exception:
        sys.exit(2)
