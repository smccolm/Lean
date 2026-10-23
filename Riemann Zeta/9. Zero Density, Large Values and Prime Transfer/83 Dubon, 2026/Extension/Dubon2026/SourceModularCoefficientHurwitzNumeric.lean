import Dubon2026.SourceModularCoefficientJDegreeSums
import Dubon2026.SourceModularCoefficientHurwitzBound

/-! The actual all-level degree and full pole-order sum specialize the
Hurwitz bounds to psi(N). These are the exact numeric inputs for the
finite exceptional-fiber and wild differential-order counts in DUB-17/18.
The counts themselves, and hence the reverse genus inequality, remain open. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The actual differential contribution is bounded using psi(N) and the full pole count. -/
theorem coeff_hurwitz_differential_numeric (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v ∈ S, 0 ≤ v.ord (jCoeff N K))
    (P : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hP : ∀ v, v ∈ P ↔ v.ord (jCoeff N K) < 0) :
    (∑ v ∈ S, v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K))) +
      (SourceLevelProjective.dedekindPsi N : ℤ) - P.card ≤
        2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 +
          2 * (SourceLevelProjective.dedekindPsi N : ℤ) := by
  have h := coeff_hurwitz_differential_bound N K S hS P (fun v hv => (hP v).mp hv)
  have hp : (∑ v ∈ P, (-v.ord (jCoeff N K) - 1)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) - P.card := by
    rw [Finset.sum_sub_distrib, sum_coeff_j_pole_orders_finset N K hNK P hP]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [finrank_coeff_over_j_eq_psi N hNK, hp] at h
  simpa only [← add_sub_assoc] using h

/-- The finite ramification contribution is bounded using psi(N) and the full pole count. -/
theorem coeff_hurwitz_ramification_numeric (hNK : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (a : Place K (modularFunctionFieldCoeff N K) → K)
    (hS : ∀ v ∈ S, 0 < v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) (a v)))
    (P : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hP : ∀ v, v ∈ P ↔ v.ord (jCoeff N K) < 0) :
    (∑ v ∈ S, (v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) (a v)) - 1)) +
      (SourceLevelProjective.dedekindPsi N : ℤ) - P.card ≤
        2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 +
          2 * (SourceLevelProjective.dedekindPsi N : ℤ) := by
  have h := coeff_hurwitz_ramification_bound N K S a hS P (fun v hv => (hP v).mp hv)
  have hp : (∑ v ∈ P, (-v.ord (jCoeff N K) - 1)) =
      (SourceLevelProjective.dedekindPsi N : ℤ) - P.card := by
    rw [Finset.sum_sub_distrib, sum_coeff_j_pole_orders_finset N K hNK P hP]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [finrank_coeff_over_j_eq_psi N hNK, hp] at h
  simpa only [← add_sub_assoc] using h

end Dubon2026.SourceFunctionField
