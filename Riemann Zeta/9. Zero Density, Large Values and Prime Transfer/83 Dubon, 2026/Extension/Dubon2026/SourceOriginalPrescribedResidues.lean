import Dubon2026.SourceOriginalTwoPoleResidues
import Dubon2026.SourceOriginalFiberOrderSupport
import Dubon2026.SourceOriginalAnalyticPlaces

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
third-kind differential with prescribed degree-zero residues. A finite
linear combination of the proved normalized two-pole differentials gives
the exact original divisor residues. Degree zero cancels the auxiliary
base-place contribution. This replaces support induction in the selected
external argument and retains the literal original residue-value contract.
Adapted from S_AlgebraicCurve_exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_differential_with_prescribed_residues
    (D : Divisor ℂ F) (hD : Divisor.degree D = 0) :
    ∃ η : Ω[F⁄ℂ], (∀ v : Place ℂ F, -1 ≤ v.ordDifferential η) ∧
      ∀ v : Place ℂ F, originalDifferentialResidue N v η = (D v : ℂ) := by
  classical
  let Q : Place ℂ F := originalAnalyticPlace N UpperHalfPlane.I
  have hpair : ∀ P : Place ℂ F, ∃ η : Ω[F⁄ℂ],
      (∀ v : Place ℂ F, -1 ≤ v.ordDifferential η) ∧
      ∀ v : Place ℂ F, originalDifferentialResidue N v η =
        (if v = P then 1 else 0) - (if v = Q then 1 else 0) := by
    intro P
    by_cases hPQ : P = Q
    · subst P
      exact ⟨0, original_simple_pole_zero_bound N, fun v => by rw [map_zero, sub_self]⟩
    exact exists_original_normalized_two_pole_differential N hPQ
  choose θ hθ hres using hpair
  let η : Ω[F⁄ℂ] := ∑ P ∈ D.support, (D P : ℂ) • θ P
  refine ⟨η, fun v => original_simple_pole_sum_bound N D.support _ v
    (fun P _ => original_simple_pole_smul_bound N v _ (hθ P v)), ?_⟩
  intro v
  have htotal : (∑ P ∈ D.support, (D P : ℂ)) = 0 := by
    exact_mod_cast (original_divisor_sum_support N D).trans hD
  have hfirst : (∑ P ∈ D.support, (D P : ℂ) * (if v = P then 1 else 0)) = (D v : ℂ) := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro P _ hPv
      simp only [if_neg hPv.symm, mul_zero]
    · intro hv
      have hz : D v = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hv
      simp only [hz, Int.cast_zero, zero_mul]
  change originalDifferentialResidue N v (∑ P ∈ D.support, (D P : ℂ) • θ P) = _
  simp only [map_sum, map_smul, smul_eq_mul, hres, mul_sub, Finset.sum_sub_distrib]
  rw [hfirst, ← Finset.sum_mul, htotal, zero_mul, sub_zero]

theorem exists_original_third_kind_differential
    (D : Divisor ℂ F) (hD : Divisor.degree D = 0) :
    ∃ η : Ω[F⁄ℂ], ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η ∧
      originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ) := by
  obtain ⟨η, hη, hres⟩ := exists_original_differential_with_prescribed_residues N D hD
  exact ⟨η, fun v => ⟨hη v, (originalDifferentialResidue_simplePole N v η (hη v)).symm.trans (hres v)⟩⟩

end
end Dubon2026.SourceFunctionField
