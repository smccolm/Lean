from pathlib import Path
from datetime import datetime, timezone
import urllib.request, json, hashlib

dest = Path(__file__).parent / 'weil-stacks-flt-followup-20261117-2290'
assert not dest.exists()
dest.mkdir()
rows = []

def fetch(url, path):
    req = urllib.request.Request(url, headers={'User-Agent': 'Dubon-public-proof-reuse-audit'})
    data = urllib.request.urlopen(req, timeout=25).read()
    target = dest / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    rows.append(dict(path=path, url=url, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
    return data

flt = json.loads(fetch('https://api.github.com/repos/anthropics/fermats-last-theorem/commits/main', 'FLT/commit.json'))['sha']
for path in ['README.md', 'PROOF-PATH.md', 'lean-toolchain', 'lakefile.lean', 'lake-manifest.json']:
    fetch(f'https://raw.githubusercontent.com/anthropics/fermats-last-theorem/{flt}/{path}',
          'FLT/' + path + ('.txt' if path.endswith('.lean') else ''))
stacks = '012108f61d7f92a6ffc35ec3f263b6da5d438125'
for path in ['README.md', 'LICENSE', 'lean-toolchain', 'lakefile.toml',
             'StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GeometricComponentsPurityReduction.lean',
             'StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/WeilIIFinalAssembly.lean']:
    fetch(f'https://raw.githubusercontent.com/AxiomMath/Stacks/{stacks}/{path}',
          'Stacks/' + path + ('.txt' if path.endswith('.lean') else ''))
weil = '27cdb2049be62ee2911429b47f54774078450e32'
for path in ['Weil/Definitions.lean',
             'Weil/Defs/AlgebraicGeometry/EtaleCohomology/Trace/RationalCohomologyFrobenius.lean',
             'Weil/AlgebraicGeometry/EtaleCohomology/Trace/RepresentationSheafTrivialConstant.lean']:
    fetch(f'https://raw.githubusercontent.com/AxiomMath/Weil/{weil}/{path}', 'Weil/' + path + '.txt')
review = dict(recordedUTC=datetime.now(timezone.utc).isoformat(), fltCommit=flt,
              previousFLTCommit='6e837e75355538c7f80bab5b956861e86c4eacc2',
              stacksCommit=stacks, weilCommit=weil, files=rows, buildClaimed=False,
              scope='Fresh FLT HEAD comparison; selected Weil and pinned Stacks purity dependencies, not full closure.',
              productionMutation=False, rootPinsChanged=False)
(dest / 'review.json').write_text(json.dumps(review, indent=2) + '\n', encoding='utf-8')
print(json.dumps(dict(fltCommit=flt, unchangedFLT=flt == review['previousFLTCommit'], files=len(rows))))
