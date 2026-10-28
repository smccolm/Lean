from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt').read_text(encoding='utf-8-sig')
b=s[s.index('theorem dip_ne_zero'):s.index('end Data')]
b=b.replace('Rset (Γ)','projectiveIntegralSubgroup Γ')
b=b.replace('sm ((δ : Γ) : SL(2, ℤ))','sm (representative Γ δ)').replace('sm ((p.2 : Γ) : SL(2, ℤ))','sm (representative Γ p.2)')
b=b.replace('dsm ((δ : Γ) : SL(2, ℤ))','dsm (representative Γ δ)').replace('dsm ((p.2 : Γ) : SL(2, ℤ))','dsm (representative Γ p.2)')
b=b.replace('((δ : Γ) : SL(2, ℤ))','(representative Γ δ : SL(2, ℤ))').replace('hs (δ : Γ)','hs (representative Γ δ)').replace('(p.2 : Γ)','(representative Γ p.2)')
b=b.replace('def bad','/-- The countable exceptional set of actual translates of dipole zeros and poles. -/\ndef bad')
b=b.replace('first | exact h | simpa [Data.V] using h','exact h')
a=b.index('  rw [← finsum_eq_sum_of_support_subset')
end=b.index('\ntheorem ae_logDeriv',a)
b=b[:a]+"""  rw [← finsum_eq_sum_of_support_subset _ hsupp]
  have htwo := finsum_projection Γ D.hneg
    (fun q : projectiveIntegralSubgroup Γ =>
      D.Fk s (sm (representative Γ q) z) * conj (dsm (representative Γ q) z)) hfin
  simp only [sm_representative_projection, dsm_representative_projection] at htwo
  rw [htwo]
  ring

"""+b[end:]
head="""import SourceSmoothDivisorInvarianceCusps

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
The actual locally finite product has the asserted logarithmic derivative
outside a countable union of translated zeros and poles. The proved two-element
projective kernel supplies the exact one-half normalization of the sum over
the original integral subgroup. Adapted from the pinned Apache-2.0 scope-889
construction, using native projective fibers and the existing derivative rules. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open MeasureTheory Filter Complex Set Metric
open SourceSmoothProjective SourceSmoothedUnfolding SourceSmoothLocalModel
open scoped MatrixGroups Topology Real Classical ComplexConjugate
local notation "dbar" => SourceComplexReciprocity.DbarFundamental.D
namespace Data
variable {Γ : Subgroup SL(2, ℤ)} (D : Data Γ)

"""
with (p/'SourceSmoothDivisorLogDerivative.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end Data\nend\nend Dubon2026.SourceSmoothDivisor\n')
