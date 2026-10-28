from pathlib import Path
import re,json
p=Path(r'E:\Lean\.tmp\dubon83')
s=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.lean.txt'
t=s.read_text(encoding='utf-8-sig')
ns='Dubon2026.SourceSmoothedFundamental'
head="""/-! DUB-17/18 -> actual Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> winding-period limit -> compact smooth modular
partition. The native group/coset equivalence preserves the exact chosen
coset representatives; no separate bijection or orbit-sum assumption is
introduced. The integral normalization remains a separate obligation. -/
"""
common='namespace '+ns+'\nnoncomputable section\nopen UpperHalfPlane hiding I coe_smul\nopen Filter Complex MulAction Set\nopen scoped MatrixGroups Topology ContDiff Pointwise\nlocal notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet\n\n'
def write(n,b,im):
 with (p/(n+'.lean')).open('x',encoding='utf-8',newline='\n') as f:f.write(im+'\n\n'+head+common+b+'\nend\nend '+ns+'\n')
b=t[t.index('theorem pOne_contDiff'):t.index('section Coset')]
b=b.replace('def boxH ', '/-- Upper-half-plane preimage of the compact cutoff rectangle. -/\ndef boxH ',1)
write('SourceModularSmoothCover',b,'import SourceModularSmoothGeometry')
b=t[t.index('theorem finsum_sum_coset'):t.index('end Coset')]
b=b.replace('  have hinj',"""  let e : (G ⧸ Γ) × Γ ≃ G :=
    (Subgroup.groupEquivQuotientProdSubgroup (s := Γ)).symm
  have he (p : (G ⧸ Γ) × Γ) : e p = p.1.out * p.2 := by rfl
  have hinj""",1)
b=b.replace('cosetEquiv Γ','e')
b=b.replace('  rfl\n','  simp only [he]\n')
# The first proof is intentionally retained as a definitional test of the native inverse.
write('SourceModularSmoothCosetSum','variable {G : Type*} [Group G] (Γ : Subgroup G)\n\n'+b,'import Mathlib')
b=t[t.index('section Support'):t.index('section Sums')]
b=b.replace('ModularCurve.smoothedFundamental','smoothedFundamental')
b=b.replace('private theorem _root_.ModularCurve.SmoothedFundamentalProof.contDiff','theorem contDiff')
b=re.sub(r'^p2m_export .*\n','',b,flags=re.M)
for n,doc in [('piece','Inverse modular translate of the cutoff rectangle, viewed in C.'),('carrier','Finite union of inverse translates indexed by the actual subgroup cosets.')]:
 b=b.replace('def '+n+' ', '/-- '+doc+' -/\ndef '+n+' ',1)
write('SourceModularSmoothedFundamentalSupport',b,'import SourceModularSmoothCover')
b=t[t.index('section Sums'):t.index('end ModularCurve.SmoothedFundamentalProof')]
b=b.replace('ModularCurve.smoothedFundamental','smoothedFundamental')
b=b.replace('def carrierH ', '/-- Upper-half-plane carrier of the actual smoothed fundamental family. -/\ndef carrierH ',1)
# The final source statement is assembled from every required component.
c=t[t.index('theorem solution'):t.index('\nend\np2m_reactivate',t.index('theorem solution'))]
c=c.replace('theorem solution','theorem smooth_partition')
c=c.replace('ModularCurve.SmoothedFundamental.smoothedFundamental_nonneg','smoothedFundamental_nonneg')
c=c.replace('ModularCurve.smoothedFundamental','smoothedFundamental')
write('SourceModularSmoothedFundamental',b+c,'import SourceModularSmoothedFundamentalSupport\nimport SourceModularSmoothCosetSum')
with (p/'modular-smooth-partition-route-876.json').open('x',encoding='utf-8') as f:json.dump(dict(previous='modular-smooth-partition-route-875.json',nativeReuse='Subgroup.groupEquivQuotientProdSubgroup inverse instead of custom cosetEquiv; exact Quotient.out formula is proved in Lean',scope='Local finite orbit sums, smoothness across the boundary, compact support and full subgroup orbit-partition contract. No supplied partition assumption.',remaining='Actual invariant integral limit with central-sign factor, winding-period comparison, Abel-Jacobi converse and full original all-weight arithmetic chain. 16/20; DUB-17--20 OPEN.'),f,indent=2)
