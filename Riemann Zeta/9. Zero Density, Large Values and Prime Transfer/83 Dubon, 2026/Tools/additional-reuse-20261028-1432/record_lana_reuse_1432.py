from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
roots=[p/n for n in ['lana-reuse-1432b','lana-reuse-1432d','lana-reuse-1432e']]
files=[f for root in roots for f in sorted(root.rglob('*')) if f.is_file()]
records=[dict(path=str(f),sha256=sha(f),bytes=f.stat().st_size) for f in files]
repos=[]
for root in sorted(roots[0].iterdir()):
 if not root.is_dir():continue
 m=json.loads((root/'fetch-manifest.json').read_text(encoding='utf-8'))
 tree=json.loads((root/'tree.json').read_text(encoding='utf-8'));assert not tree.get('truncated',False)
 repos.append(dict(repository=m['repository'],revision=m['revision'],commitDate=m['commitDate'],treeEntries=len(tree['tree']),toolchain=(root/'lean-toolchain.txt').read_text().strip()))
selected=[f for root in roots[1:] for f in root.rglob('*.lean.txt')]
assert len(selected)==12
scan=[]
for f in selected:
 s=f.read_text(encoding='utf-8')
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
 scan.append(dict(path=str(f),matches=[dict(line=i,text=l) for i,l in enumerate(code.splitlines(),1) if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',l)]))
data=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17/18 -> literal higher symmetric-power continuation -> original all-weight arithmetic association -> actual finite Gamma1 Hecke-character realization -> exact coordinate degree/genus preservation or actual parabolic character transfer.',repositories=repos,files=records,selectedLeanFiles=12,selectedTokenScan=scan,inventoryBoundary='The four new LANA trees are complete and nontruncated. The older Anthropic inventory is truncated; two explicitly present source files were inspected without any absence inference from that inventory.',assessment='No newly inspected source discharges the original Gamma1 degree/genus equalities or finite-modulus homogeneous parabolic transfer. The elliptic good-reduction criterion and Tate uniformization remain candidates for an explicitly proved elliptic/cusp model bridge. The existing native original-Picard inertia, cyclotomic continuity and arithmetic-descent chain is shorter for the current consumers and is retained. The two Anthropic statements concern projective-line coefficients at Gamma0(N*p) over a field and complex Eichler-integral correction respectively, not the missing Gamma1 transfer over ZMod(p^(n+1)).',externalBuild=False,externalImport=False,transitiveAxiomAudit=False,rootPinsChanged=False,productionMutation=False,remaining='Actual geometric equalities, nonzero original Hecke-character realization, exceptional-prime handling, two-dimensional all-weight characteristic-zero association and higher continuation remain; 16/20, DUB-17--20 OPEN.')
f=p/'lana-reuse-review-1432.json';assert not f.exists();f.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(files),selected=12,review=str(f),sha256=sha(f),selectedCodeScanMatches=sum(len(x['matches']) for x in scan))))
