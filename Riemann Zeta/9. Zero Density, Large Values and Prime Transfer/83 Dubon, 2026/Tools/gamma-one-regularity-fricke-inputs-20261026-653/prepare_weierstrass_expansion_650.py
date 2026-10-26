from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'weierstrass-expansion-reuse-649/P2M/Sol/S_WLight_weierstrassP_qExpansion_package.lean.txt').read_text(encoding='utf-8')
def take(a,b):return s[s.index(a):s.index(b,s.index(a))]
header='''/-! DUB-17/18 -> higher symmetric-power continuation -> arithmetic
automorphy -> original all-weight association -> original finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> actual Fricke expansions.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
Native Lipschitz summation and Weierstrass absolute summability are reused.
No external proof module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

'''
tail='\nend\nend Dubon2026.SourceFricke\n'
data=[
('SourceLipschitzTwo','import Mathlib\n\n',take('theorem summable_one_div_add_int_sq','open Metric Set Filter Topology in')),
('SourceLipschitzTwoRealBoundary','import SourceLipschitzTwo\n\n',take('open Metric Set Filter Topology in','theorem summable_one_div_sub_int_sq')),
('SourceWeierstrassRowSeries','import SourceLipschitzTwoRealBoundary\n\n',take('theorem summable_one_div_sub_int_sq','end B2_lipschitz')),
('SourceWeierstrassLatticeRows','import SourceWeierstrassRowSeries\nimport SourceFrickeModularLatticeV2\n\n',take('abbrev wpSummand','end B2_rearrange')+take('theorem weierstrassP_periodPairOfTau_qExpansion','end B2_assembly')),
('SourceWeierstrassTorsionExpansion','import SourceWeierstrassLatticeRows\n\n',take('def zetaN','end B2_torsion')),
('SourceWeierstrassTorsionTail','import SourceWeierstrassTorsionExpansion\n\n',take('lemma norm_zetaN','def wpTorsion (')),
('SourceWeierstrassTorsionHolomorphy','import SourceWeierstrassTorsionTail\n\n',take('def wpTorsion (','end B3_holo'))]
docs={'wpSummand':'The literal Weierstrass summand indexed by the two integral lattice coordinates.','zetaN':'The standard complex root of unity for the positive level.','qN':'The actual complex Fourier parameter of width N.','wpTail':'The explicit paired-row Fourier summand at a torsion point.','wpTorsion':'The actual Weierstrass function at the indicated torsion-point representative.','wpTorsionSeries':'The explicit convergent Fourier expression for the actual torsion Weierstrass value.'}
for n,im,t in data:
 for d,doc in docs.items():
  import re
  t=re.sub(r'(?m)^((?:def|abbrev) '+re.escape(d)+r'\b)',lambda m:'/-- '+doc+' -/\n'+m[1],t)
 f=p/(n+'.lean');assert not f.exists();f.write_text(im+header+t+tail,encoding='utf-8')
route=p/'weierstrass-expansion-route-650.json';assert not route.exists()
route.write_text(json.dumps(dict(chain='DUB-17/18 -> higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 Hecke-character realization -> actual Picard/H1 and diamond comparison -> differential realization -> rational Fourier structure -> Fricke generator holomorphy and cyclotomic expansion.',selectedRoute='Reuse native EisensteinSeries.qExpansion_identity at weight two and PeriodPair.hasSum_weierstrassP. Keep the integer-complement boundary argument, because torsion points with first coordinate zero are required. Reuse the newly proved actual period-pair construction and omit duplicate scaling and invariant-normalization machinery. Derive the explicit paired Fourier tail, prove its uniform summable majorant, and obtain holomorphy of the same actual torsion Weierstrass functions.',assumptionsToDischarge='The exact torsion Fourier formula and holomorphy of the actual functions, with justified summation rearrangements. These feed the cyclotomic coefficient and Fricke rational-structure arguments.',remaining='Cusp boundedness, explicit coefficient model and conjugation, rational Fricke spanning, actual differential realization and converse, Picard/H1/diamond and arithmetic association remain; 16/20; DUB-17--20 OPEN.',source=str(p/'weierstrass-expansion-reuse-649/snapshots.json'),sourceSha256=hashlib.sha256((p/'weierstrass-expansion-reuse-649/snapshots.json').read_bytes()).hexdigest().upper(),modules=[x[0] for x in data],rootPinsChanged=False,proofLimitsChanged=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
print('Prepared seven scratch modules from the exact Fourier proof.')
