import Dubon2026.SourceOriginalRiemannRoch
import Dubon2026.SourceCurveWeilRankOne

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
prescribed residues -> two-pole differential. The already proved original
Riemann--Roch and negative-degree vanishing compute the exact increase in
dimension when a second simple pole is allowed. This serves only the
original two-pole existence argument.
Adapted from S_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_two_pole_dimensions {ω₀ : Ω[F⁄ℂ]} (hω₀ : ω₀ ≠ 0)
    (P Q : Place ℂ F) :
    let K₀ := originalCanonicalDivisor N ℂ hω₀
    let P1 : Divisor ℂ F := Finsupp.single P 1
    let Q1 : Divisor ℂ F := Finsupp.single Q 1
    (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + P1) + 1 ∧
      (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + Q1) + 1 := by
  classical
  haveI : HasPrincipalDivisors ℂ F := hasPrincipalDivisors_original N ℂ
  set K₀ : Divisor ℂ F := originalCanonicalDivisor N ℂ hω₀ with hK₀
  set P1 : Divisor ℂ F := Finsupp.single P 1 with hP1
  set Q1 : Divisor ℂ F := Finsupp.single Q 1 with hQ1
  have hdegP : (Module.finrank ℂ P.ResidueField : ℤ) = 1 := by
    exact_mod_cast Module.finrank_of_bijective_algebraMap
      (original_place_residue_algebraMap_bijective N ℂ P)
  have hdegQ : (Module.finrank ℂ Q.ResidueField : ℤ) = 1 := by
    exact_mod_cast Module.finrank_of_bijective_algebraMap
      (original_place_residue_algebraMap_bijective N ℂ Q)
  have hdP1 : Divisor.degree P1 = 1 := by rw [hP1, Divisor.degree_single, hdegP, one_mul]
  have hdQ1 : Divisor.degree Q1 = 1 := by rw [hQ1, Divisor.degree_single, hdegQ, one_mul]

  have hℓP : ell (-P1) = 0 := ell_eq_zero_of_degree_neg (by rw [map_neg, hdP1]; norm_num)
  have hℓQ : ell (-Q1) = 0 := ell_eq_zero_of_degree_neg (by rw [map_neg, hdQ1]; norm_num)
  have hℓPQ : ell (-(P1 + Q1)) = 0 :=
    ell_eq_zero_of_degree_neg (by rw [map_neg, map_add, hdP1, hdQ1]; norm_num)

  have rPQ := original_functionFieldRiemannRoch N ℂ hω₀ (K₀ + P1 + Q1)
  have rP := original_functionFieldRiemannRoch N ℂ hω₀ (K₀ + P1)
  have rQ := original_functionFieldRiemannRoch N ℂ hω₀ (K₀ + Q1)
  rw [show originalCanonicalDivisor N ℂ hω₀ - (K₀ + P1 + Q1) = -(P1 + Q1) by rw [hK₀]; abel, hℓPQ,
    map_add, map_add, hdP1, hdQ1] at rPQ
  rw [show originalCanonicalDivisor N ℂ hω₀ - (K₀ + P1) = -P1 by rw [hK₀]; abel, hℓP, map_add, hdP1] at rP
  rw [show originalCanonicalDivisor N ℂ hω₀ - (K₀ + Q1) = -Q1 by rw [hK₀]; abel, hℓQ, map_add, hdQ1] at rQ
  have hellP : (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + P1) + 1 := by push_cast at rPQ rP ⊢; linarith
  have hellQ : (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + Q1) + 1 := by push_cast at rPQ rQ ⊢; linarith

  exact ⟨hellP, hellQ⟩

end
end Dubon2026.SourceFunctionField
