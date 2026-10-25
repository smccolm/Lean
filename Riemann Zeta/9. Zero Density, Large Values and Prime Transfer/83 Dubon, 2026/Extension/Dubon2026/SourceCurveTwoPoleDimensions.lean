import Dubon2026.SourceCurveWeilRankOne
import Dubon2026.SourceCurveDivisorDegree
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! DUB-17/18 -> cover prescribed residues -> two-pole dimension growth.
Isolate the existing dimension calculation from the concrete cover field.
The actual cover supplies the full Riemann-Roch identity and degree-one
residue fields. This lemma performs the two-pole comparison, with no
numerical genus assumption or change of proof limits.
Adapted from the native original-curve proof, ultimately from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {F : Type*} [Field F] [Algebra ℂ F] [HasPrincipalDivisors ℂ F]

theorem two_pole_dimensions_of_riemann_roch (K₀ : Divisor ℂ F) (γ : ℤ)
    (hRR : ∀ D : Divisor ℂ F, (ell D : ℤ) - ell (K₀ - D) = Divisor.degree D + 1 - γ)
    (P Q : Place ℂ F) (hP : Module.finrank ℂ P.ResidueField = 1)
    (hQ : Module.finrank ℂ Q.ResidueField = 1) :
    let P1 : Divisor ℂ F := Finsupp.single P 1
    let Q1 : Divisor ℂ F := Finsupp.single Q 1
    (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + P1) + 1 ∧
      (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + Q1) + 1 := by
  classical
  set P1 : Divisor ℂ F := Finsupp.single P 1 with hP1
  set Q1 : Divisor ℂ F := Finsupp.single Q 1 with hQ1
  have hdegP : (Module.finrank ℂ P.ResidueField : ℤ) = 1 := by
    exact_mod_cast hP
  have hdegQ : (Module.finrank ℂ Q.ResidueField : ℤ) = 1 := by
    exact_mod_cast hQ
  have hdP1 : Divisor.degree P1 = 1 := by rw [hP1, Divisor.degree_single, hdegP, one_mul]
  have hdQ1 : Divisor.degree Q1 = 1 := by rw [hQ1, Divisor.degree_single, hdegQ, one_mul]

  have hℓP : ell (-P1) = 0 := ell_eq_zero_of_degree_neg (by rw [map_neg, hdP1]; norm_num)
  have hℓQ : ell (-Q1) = 0 := ell_eq_zero_of_degree_neg (by rw [map_neg, hdQ1]; norm_num)
  have hℓPQ : ell (-(P1 + Q1)) = 0 :=
    ell_eq_zero_of_degree_neg (by rw [map_neg, map_add, hdP1, hdQ1]; norm_num)

  have rPQ := hRR (K₀ + P1 + Q1)
  have rP := hRR (K₀ + P1)
  have rQ := hRR (K₀ + Q1)
  rw [show K₀ - (K₀ + P1 + Q1) = -(P1 + Q1) by abel, hℓPQ,
    map_add, map_add, hdP1, hdQ1] at rPQ
  rw [show K₀ - (K₀ + P1) = -P1 by abel, hℓP, map_add, hdP1] at rP
  rw [show K₀ - (K₀ + Q1) = -Q1 by abel, hℓQ, map_add, hdQ1] at rQ
  have hellP : (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + P1) + 1 := by push_cast at rPQ rP ⊢; linarith
  have hellQ : (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + Q1) + 1 := by push_cast at rPQ rQ ⊢; linarith

  exact ⟨hellP, hellQ⟩

end
end Dubon2026.SourceCurve
