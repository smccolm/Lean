import Dubon2026.SourceOriginalWeilFunctionChoice

/-! DUB-17/18 -> original Weil pairing descent -> independence of
principal function choices for fixed actual divisor representatives. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilDatum
noncomputable section
open SourceCurve
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable {n : ℕ} [NeZero n]

theorem pairing_eq_of_same_divisors (d d' : OriginalWeilDatum N L n)
    (h₁ : d'.D₁ = d.D₁) (h₂ : d'.D₂ = d.D₂) : d'.pairing = d.pairing := by
  have hnum : originalDivisorEval N L d'.f₁ d.D₂ = originalDivisorEval N L d.f₁ d.D₂ := by
    apply originalDivisorEval_eq_of_same_orders N L _ _ d'.f₁_ne_zero d.f₁_ne_zero
      (fun v => by rw [d'.ord_f₁, d.ord_f₁, h₁]) _ d.degree_second
    intro v hv
    rw [d.ord_f₁, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]
  have hden : originalDivisorEval N L d'.f₂ d.D₁ = originalDivisorEval N L d.f₂ d.D₁ := by
    apply originalDivisorEval_eq_of_same_orders N L _ _ d'.f₂_ne_zero d.f₂_ne_zero
      (fun v => by rw [d'.ord_f₂, d.ord_f₂, h₂]) _ d.degree_first
    intro v hv
    rw [d.ord_f₂, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]
  simp only [pairing, h₁, h₂, hnum, hden]

end
end Dubon2026.SourceFunctionField.OriginalWeilDatum
