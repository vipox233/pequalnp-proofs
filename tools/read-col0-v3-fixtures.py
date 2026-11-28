"""Team-only rehearsal members and pre-candidate receipt projections."""
import hashlib


def rehearsal(digest, git_blob, canonical):
    rows, source = [], {}
    for i in range(50):
        stem = f'L_trial_{i}'
        header = f'theorem PEqualNP.Outside.{stem} (nₐ : Nat) : 0 - nₐ = 0 - nₐ :=\n'
        body = '  Eq.refl (0 -\nnₐ\n  )\n'
        holds = [[3, 'COL0', 'ident', 'sym']]
        if 5 <= i < 10:
            header = 'theorem teamPrelude : True := True.intro\n' + header
            holds[0][0] += 1
        if i >= 10:
            header = '-- please visit\n' + header
            holds = [[1, 'ADDR', 'comment', 'empty'], [4, 'COL0', 'ident', 'sym']]
        raw = (header + body).encode()
        key = digest(raw)
        source[key] = raw
        rows.append(dict(proof=i + 1, stem=stem, head='c' * 40, digest=key, blob=git_blob(raw),
                         owner=i % 10 + 1, inventory=hashlib.sha256(canonical(('HOLD', [], holds))).hexdigest(),
                         run='41', attempt='1', verdict='ACCEPTED'))
    manifest = dict(version=3, cutoff='2026-11-28T00:00:00Z', total=50, members=rows, joint_safe=True)
    return manifest, source

def platform(api, manifest, commit='a' * 40):
    repo, ref = 'team/fixtures', 'refs/tags/col0-v3-count-team'
    env = dict(GITHUB_REPOSITORY=repo, GITHUB_REF=ref, GITHUB_SHA=commit,
               GITHUB_RUN_NUMBER='3', GITHUB_RUN_ATTEMPT='1', GITHUB_EVENT_NAME='workflow_dispatch',
               GITHUB_REF_TYPE='tag', GITHUB_WORKFLOW_REF=f"{repo}/{api['WORKFLOW']}@{ref}",
               GITHUB_WORKFLOW_SHA=commit, COL0_V3_ENABLED='true', COL0_V3_SELECTION='col0-v3-count',
               COL0_V3_TAG_REF=ref, COL0_V3_TAG_TYPE='lightweight', COL0_V3_REPOSITORY=repo,
               COL0_V3_RUN_NUMBER='3', COL0_V3_PEELED_COMMIT=commit,
               COL0_V3_PROTECTED_TAG_REF=ref, COL0_V3_PROTECTED_TAG_TYPE='lightweight',
               COL0_V3_PROTECTED_PEELED_COMMIT=commit)
    encode = api['WORKER']['canonical']
    raw = encode(manifest)
    descriptor = dict(binding=api['binding'](env), producers=api['pins'](), manifest_sha256=api['sha'](raw))
    value = encode(descriptor)
    env.update(COL0_V3_DESCRIPTOR=value.decode('ascii'), COL0_V3_DESCRIPTOR_SHA256=api['sha'](value),
               COL0_V3_PROTECTED_DESCRIPTOR_SHA256=api['sha'](value),
               COL0_V3_BINDING=encode(api['protected_binding'](descriptor)).decode('ascii'),
               COL0_V3_MANIFEST_1=raw.decode('ascii'))
    return env, (commit, 'commit', commit, commit)


def run_rehearsal(api, manifest, sources):
    env, tag = platform(api, manifest)
    def resolve(_):
        return tag
    output, authorized = api['reserved'](env, False, resolve)
    if not authorized:
        return output
    return api['reserved'](env, True, resolve,
                           fetch=lambda row: sources[row['digest']])[0]
