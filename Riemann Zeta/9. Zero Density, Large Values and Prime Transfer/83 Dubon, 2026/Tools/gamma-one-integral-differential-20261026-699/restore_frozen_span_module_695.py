from pathlib import Path
import hashlib, json, datetime

p = Path(__file__).parent
paper = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
name = 'SourceOriginalFrickeSpanDescent'
new = 'SourceFrickeLaurentSpanDescent'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
receipt = json.loads((p / 'source-cusp-fricke-rational-span-7-scratch-receipt.json').read_text(encoding='utf-8'))
entry = next(x for x in receipt['files'] if Path(x['path']).stem == name)
prod = paper / f'Extension/Dubon2026/{name}.lean'
original = prod.read_bytes().replace(b'import Dubon2026.', b'import ')
assert sha(original) == entry['sha256'], 'Do not restore without an exact historical hash match'
assert not (p / f'{new}.lean').exists()
snapshot = p / 'scratch-name-collision-695'
assert not snapshot.exists()
snapshot.mkdir()
saved = []
for f in p.glob(name + '.*'):
    target = snapshot / (f.name + ('.txt' if f.suffix == '.lean' else ''))
    target.write_bytes(f.read_bytes())
    saved.append(dict(path=str(target), sha256=sha(target.read_bytes())))
development = (p / f'{name}.lean').read_bytes()
assert b'theorem mem_frickeLaurentFieldK_of_represents_frickeSpan' in development
(p / f'{new}.lean').write_bytes(development)
(p / f'{name}.lean').write_bytes(original)
dependent = p / 'SourceRationalCuspWeightIntegrality.lean'
before = dependent.read_bytes()
assert b'import SourceOriginalFrickeSpanDescent\n' in before
dependent.write_bytes(before.replace(b'import SourceOriginalFrickeSpanDescent\n',
                                    b'import SourceFrickeLaurentSpanDescent\n'))
record = dict(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    issue='A new unaudited scratch module reused an existing frozen scratch basename. Production was not changed.',
    restoredSource=str(p / f'{name}.lean'), restoredSourceSha256=sha(original),
    expectedOleanSha256=entry['oleanSha256'], productionSourceSha256=sha(prod.read_bytes()),
    newDevelopmentSource=str(p / f'{new}.lean'), savedCollisionEvidence=saved,
    next='Recompile the exact restored source into a fresh restoration log, require the original olean hash, then recompile the distinct new module and its unaudited dependents. Verify all 8471 and prepared 8493 source/olean receipt hashes before further integration.',
    route694Correction='The new two-theorem Laurent/function fraction descent belongs to SourceFrickeLaurentSpanDescent. SourceOriginalFrickeSpanDescent retains its previously audited fixed-field cusp-image descent and original bytes.')
(p / 'scratch-name-collision-restoration-695.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps(dict(restoredSourceSha256=sha(original), newModule=new, snapshot=str(snapshot))))
