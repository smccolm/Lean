from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt').read_text(encoding='utf-8-sig')
b=s[s.index('theorem closedBall_subset'):s.index('theorem sm_eq_coe_iff')]
b=b.replace('Rset (Γ)','projectiveIntegralSubgroup Γ')
b=b.replace('sm ((δ : Γ) : SL(2, ℤ))','sm (representative Γ δ)').replace('sm ((p.2 : Γ) : SL(2, ℤ))','sm (representative Γ p.2)')
b=b.replace('((δ : Γ) : SL(2, ℤ))','(representative Γ δ : SL(2, ℤ))')
b=b.replace('(Subtype.val_injective.comp Subtype.val_injective).injOn','(Subtype.val_injective.comp (representative_injective Γ)).injOn')
head="""import SourceSmoothDivisorProduct

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
Proper discontinuity makes the actual projective dipole product locally finite.
Native analytic action and the proved local-product calculus give its local
integer exponent sum. Identifying that sum with the original order n remains
the exact orbit-counting step in the next module. Adapted from the pinned
Apache-2.0 scope-889 construction, using the actual projective subgroup. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set Metric
open SourceSmoothProjective SourceSmoothLocalModel
open scoped MatrixGroups Topology Real Classical
namespace Data
variable {Γ : Subgroup SL(2, ℤ)} (D : Data Γ)

"""
with (p/'SourceSmoothDivisorLocalProduct.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end Data\nend\nend Dubon2026.SourceSmoothDivisor\n')
