import Dubon2026.SourceOriginalWeilReciprocity
import Dubon2026.SourceOriginalWeilDatum

/-! DUB-17/18 -> original Tate pairing -> divisorial Weil pairing.
The proved original reciprocity forces the literal ratio on n-torsion
representatives to have nth power one. No reciprocity hypothesis is retained. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped Classical BigOperators
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem originalDivisorEval_nsmul (f : modularFunctionFieldOver N L)
    (D : Divisor L (modularFunctionFieldOver N L)) (n : ℕ) :
    originalDivisorEval N L f (n • D) = originalDivisorEval N L f D ^ n := by
  unfold originalDivisorEval
  rw [Finsupp.prod_of_support_subset (n • D) Finsupp.support_smul _ (fun _ _ => zpow_zero _)]
  change (∏ v ∈ D.support, originalPlaceEval N L v f ^ ((n • D) v)) = _
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  simp_rw [mul_comm (n : ℤ), zpow_mul, zpow_natCast]
  exact Finset.prod_pow D.support n (fun v => originalPlaceEval N L v f ^ D v)

namespace OriginalWeilDatum
variable {N L} {n : ℕ} (d : OriginalWeilDatum N L n)

omit [IsAlgClosed L] in
theorem principalDivisor_first : originalPrincipalDivisor N L d.f₁ = n • d.D₁ := by
  ext v
  change v.ord d.f₁ = _
  rw [d.ord_f₁, Finsupp.smul_apply, nsmul_eq_mul]

omit [IsAlgClosed L] in
theorem principalDivisor_second : originalPrincipalDivisor N L d.f₂ = n • d.D₂ := by
  ext v
  change v.ord d.f₂ = _
  rw [d.ord_f₂, Finsupp.smul_apply, nsmul_eq_mul]

theorem pairing_pow_eq_one : d.pairing ^ n = 1 := by
  have hdisj (v : Place L (modularFunctionFieldOver N L)) (hv : v.ord d.f₁ ≠ 0) :
      v.ord d.f₂ = 0 := by
    rcases d.disjoint v with h | h
    · exact (hv (by rw [d.ord_f₁, h, mul_zero])).elim
    · rw [d.ord_f₂, h, mul_zero]
  have he := original_weil_reciprocity L N d.f₁ d.f₂ d.f₁_ne_zero d.f₂_ne_zero hdisj
  rw [d.principalDivisor_first, d.principalDivisor_second,
    originalDivisorEval_nsmul, originalDivisorEval_nsmul] at he
  have hn : originalDivisorEval N L d.f₂ d.D₁ ≠ 0 := by
    apply originalDivisorEval_ne_zero N L d.f₂ d.f₂_ne_zero
    intro v hv
    rw [d.ord_f₂, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]
  rw [pairing, div_pow, he, div_self (pow_ne_zero _ hn)]

end OriginalWeilDatum
end
end Dubon2026.SourceFunctionField
