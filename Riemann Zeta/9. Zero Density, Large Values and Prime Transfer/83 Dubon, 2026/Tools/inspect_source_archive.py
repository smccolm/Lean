"""Compare the frozen source archive with extracted bytes; never execute/extract it."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import tarfile


def inspect(project: Path) -> int:
    observation = json.loads((project / 'Tools/author_code_observation.json').read_text(encoding='utf-8'))
    expected = {x['path']: x for x in observation['archiveMembers']}
    required = {'00README.json', 'Zero_Density_Concentration_for_Dirichlet_Polynomials.tex'}
    if set(expected) != required or observation['ancillaryPrograms'] or observation['executedAuthorCode']:
        raise ValueError('Archive/code-availability observation is inconsistent')
    seen = set()
    with tarfile.open(project / 'Sources/dubon-2609.17875v1.tar') as archive:
        for member in archive.getmembers():
            path = PurePosixPath(member.name)
            if path.is_absolute() or '..' in path.parts or member.issym() or member.islnk():
                raise ValueError(f'Unsafe archive member: {member.name}')
            if not member.isfile():
                if member.isdir():
                    continue
                raise ValueError(f'Unexpected archive member type: {member.name}')
            if member.name not in expected or member.name in seen:
                raise ValueError(f'Unexpected/duplicate archive member: {member.name}')
            data = archive.extractfile(member).read()
            entry = expected[member.name]
            if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
                raise ValueError(f'Archive member pin mismatch: {member.name}')
            extracted = project / 'Sources/Dubon-v1-source' / member.name
            if extracted.read_bytes() != data:
                raise ValueError(f'Extracted source differs: {member.name}')
            seen.add(member.name)
    if seen != required:
        raise ValueError('Incomplete source archive')
    actual = {p.relative_to(project / 'Sources/Dubon-v1-source').as_posix()
              for p in (project / 'Sources/Dubon-v1-source').rglob('*') if p.is_file()}
    if actual != required:
        raise ValueError('Unexpected extracted source file')
    return len(seen)


if __name__ == '__main__':
    count = inspect(Path(__file__).resolve().parents[1])
    print(f'ARCHIVE PASS: {count} exact members; no ancillary program executed; no Lean proof tested.')
