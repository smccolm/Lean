import Dubon2026.SourceCurveFiniteCoordinateGenusMaximum
import Dubon2026.SourceCurveDivisorDegree
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! DUB-17/18 -> cover Abel converse -> actual meromorphic field comparison.
The native degree-dimension maximum supplies a natural dimension bound.
It gives a pole-clearing multiplier and enough independent algebraic
functions for the analytic dimension comparison. Canonical genus, full
Riemann-Roch and period-rank calculations are unnecessary for these bounds.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {F : Type*} [Field F] [Algebra ℂ F]
variable (t : F) [FiniteDimensional ℂ⟮t⟯ F]
include t

theorem exists_natural_degree_dimension_bound (ht : Transcendental ℂ t) :
    ∃ g : ℕ, ∀ D : Divisor ℂ F, Divisor.degree D + 1 - g ≤ (ell D : ℤ) := by
  obtain ⟨γ, D₀, hmax⟩ := finite_coordinate_degree_dimension_maximum t ht
  refine ⟨γ.toNat, fun D => ?_⟩
  have h := hmax.isMax D
  have hg : γ ≤ (γ.toNat : ℤ) := by omega
  omega

theorem finite_coordinate_degree_single (Q : Place ℂ F) (m : ℤ) :
    Divisor.degree (Finsupp.single Q m) = m := by
  have hr := Module.finrank_of_bijective_algebraMap
    (place_residue_bijective_of_finite_coordinate t Q)
  rw [Divisor.degree_single, hr, Nat.cast_one, mul_one]

theorem exists_pole_clearing_function_of_finite_coordinate
    (ht : Transcendental ℂ t) (Q : Place ℂ F) (E : Divisor ℂ F) :
    ∃ n : ℕ, ∃ a : F, a ≠ 0 ∧ a ∈ LSpace (Finsupp.single Q (n : ℤ) - E) := by
  obtain ⟨g, hg⟩ := exists_natural_degree_dimension_bound t ht
  let n := g + (Divisor.degree E).toNat
  have hb := hg (Finsupp.single Q (n : ℤ) - E)
  rw [map_sub, finite_coordinate_degree_single t] at hb
  have hn : (n : ℤ) = g + ((Divisor.degree E).toNat : ℤ) := by
    simp only [n, Nat.cast_add]
  have hell : (1 : ℤ) ≤ (ell (Finsupp.single Q (n : ℤ) - E) : ℤ) := by
    have : Divisor.degree E ≤ ((Divisor.degree E).toNat : ℤ) := by omega
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := LSpace (Finsupp.single Q (n : ℤ) - E)) (by
      intro hbot
      have hz : ell (Finsupp.single Q (n : ℤ) - E) = 0 := by
        rw [ell, hbot, finrank_bot]
      omega)
  exact ⟨n, a, ha0, ha⟩

theorem one_place_dimension_sum_gt_of_bound (Q : Place ℂ F) (g n : ℕ)
    (hg : ∀ D : Divisor ℂ F, Divisor.degree D + 1 - g ≤ (ell D : ℤ)) :
    n + 2 * g + 1 < ell (Finsupp.single Q ((n + 2 * g : ℕ) : ℤ)) +
      ell (Finsupp.single Q ((2 * g : ℕ) : ℤ)) := by
  have h1 := hg (Finsupp.single Q ((n + 2 * g : ℕ) : ℤ))
  have h2 := hg (Finsupp.single Q ((2 * g : ℕ) : ℤ))
  rw [finite_coordinate_degree_single t] at h1 h2
  push_cast at h1 h2 ⊢
  omega

end
end Dubon2026.SourceCurve
