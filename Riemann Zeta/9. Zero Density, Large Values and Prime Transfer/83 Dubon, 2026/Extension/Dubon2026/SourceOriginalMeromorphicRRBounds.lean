import Dubon2026.SourceOriginalRiemannRoch
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Existing original Riemann-Roch supplies a
nonzero denominator vanishing at every prescribed effective divisor, with
poles at one actual place. Its inequality also supplies enough independent
original functions for the analytic dimension comparison. No eventual
dimension formula or additional pole-divisor construction is needed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]

theorem original_riemannRoch_lower_bound
    (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) :
    Divisor.degree D + 1 - originalGenus N ℂ ≤ (ell D : ℤ) := by
  have h := original_functionFieldRiemannRoch N ℂ (D_jOver_ne_zero N ℂ) D
  omega

theorem original_degree_single (Q : Place ℂ (modularFunctionFieldOver N ℂ)) (n : ℤ) :
    Divisor.degree (Finsupp.single Q n) = n := by
  have hr := Module.finrank_of_bijective_algebraMap
    (original_place_residue_algebraMap_bijective N ℂ Q)
  rw [Divisor.degree_single, hr, Nat.cast_one, mul_one]

theorem exists_original_pole_clearing_function
    (Q : Place ℂ (modularFunctionFieldOver N ℂ))
    (E : Divisor ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ n : ℕ, ∃ h : modularFunctionFieldOver N ℂ, h ≠ 0 ∧
      h ∈ LSpace (Finsupp.single Q (n : ℤ) - E) := by
  let n := originalGenus N ℂ + (Divisor.degree E).toNat
  have hb := original_riemannRoch_lower_bound N (Finsupp.single Q (n : ℤ) - E)
  rw [map_sub, original_degree_single] at hb
  have hn : (n : ℤ) = originalGenus N ℂ + ((Divisor.degree E).toNat : ℤ) := by
    simp only [n, Nat.cast_add]
  have hell : (1 : ℤ) ≤ (ell (Finsupp.single Q (n : ℤ) - E) : ℤ) := by
    have : Divisor.degree E ≤ ((Divisor.degree E).toNat : ℤ) := by omega
    omega
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := LSpace (Finsupp.single Q (n : ℤ) - E)) (by
    intro hbot
    have hz : ell (Finsupp.single Q (n : ℤ) - E) = 0 := by
      rw [ell, hbot, finrank_bot]
    omega)
  exact ⟨n, h, hh0, hh⟩

theorem original_one_place_dimension_sum_gt
    (Q : Place ℂ (modularFunctionFieldOver N ℂ)) (n : ℕ) :
    n + 2 * originalGenus N ℂ + 1 <
      ell (Finsupp.single Q ((n + 2 * originalGenus N ℂ : ℕ) : ℤ)) +
      ell (Finsupp.single Q ((2 * originalGenus N ℂ : ℕ) : ℤ)) := by
  have h1 := original_riemannRoch_lower_bound N
    (Finsupp.single Q ((n + 2 * originalGenus N ℂ : ℕ) : ℤ))
  have h2 := original_riemannRoch_lower_bound N
    (Finsupp.single Q ((2 * originalGenus N ℂ : ℕ) : ℤ))
  rw [original_degree_single] at h1 h2
  push_cast at h1 h2 ⊢
  omega

end
end Dubon2026.SourceFunctionField
