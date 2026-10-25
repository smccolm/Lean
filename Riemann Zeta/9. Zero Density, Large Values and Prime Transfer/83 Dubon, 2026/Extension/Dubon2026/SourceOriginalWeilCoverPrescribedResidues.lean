import Dubon2026.SourceOriginalWeilCoverTwoPoleResidues
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse. A finite
sum of the normalized two-pole differentials realizes every degree-zero
cover divisor as actual simple-pole residues; its degree cancels the base place.
Adapted from the existing original-field proof and its attributed FLT route,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

theorem cover_divisor_sum_support (D : Divisor ℂ EE) :
    (∑ v ∈ D.support, D v) = Divisor.degree D := by
  have hrank : ∀ v : Place ℂ EE, Module.finrank ℂ v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap
      (originalWeilKummerCover_residue_bijective N ℂ n r v)
  simp only [Divisor.degree_eq_sum_support, hrank, Nat.cast_one, mul_one]

theorem exists_cover_differential_with_prescribed_residues
    (D : Divisor ℂ EE) (hD : Divisor.degree D = 0) :
    ∃ η : Ω[EE⁄ℂ], (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η) ∧
      ∀ v : Place ℂ EE, coverDifferentialResidue N n r v η = (D v : ℂ) := by
  classical
  let Q : Place ℂ EE := Classical.choice (nonempty_cover_place N n r)
  have hpair : ∀ P : Place ℂ EE, ∃ η : Ω[EE⁄ℂ],
      (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η) ∧
      ∀ v : Place ℂ EE, coverDifferentialResidue N n r v η =
        (if v = P then 1 else 0) - (if v = Q then 1 else 0) := by
    intro P
    by_cases hPQ : P = Q
    · subst P
      exact ⟨0, cover_simple_pole_zero_bound N n r, fun v => by rw [map_zero, sub_self]⟩
    exact exists_cover_normalized_two_pole_differential N n r hPQ
  choose θ hθ hres using hpair
  let η : Ω[EE⁄ℂ] := ∑ P ∈ D.support, (D P : ℂ) • θ P
  refine ⟨η, fun v => cover_simple_pole_sum_bound N n r D.support _ v
    (fun P _ => cover_simple_pole_smul_bound N n r v _ (hθ P v)), ?_⟩
  intro v
  have htotal : (∑ P ∈ D.support, (D P : ℂ)) = 0 := by
    exact_mod_cast (cover_divisor_sum_support N n r D).trans hD
  have hfirst : (∑ P ∈ D.support, (D P : ℂ) * (if v = P then 1 else 0)) = (D v : ℂ) := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro P _ hPv
      simp only [if_neg hPv.symm, mul_zero]
    · intro hv
      have hz : D v = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hv
      simp only [hz, Int.cast_zero, zero_mul]
  change coverDifferentialResidue N n r v (∑ P ∈ D.support, (D P : ℂ) • θ P) = _
  simp only [map_sum, map_smul, smul_eq_mul, hres, mul_sub, Finset.sum_sub_distrib]
  rw [hfirst, ← Finset.sum_mul, htotal, zero_mul, sub_zero]

theorem exists_cover_third_kind_differential
    (D : Divisor ℂ EE) (hD : Divisor.degree D = 0) :
    ∃ η : Ω[EE⁄ℂ], ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η ∧
      v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ) := by
  obtain ⟨η, hη, hres⟩ := exists_cover_differential_with_prescribed_residues N n r D hD
  exact ⟨η, fun v => ⟨hη v, (coverDifferentialResidue_simplePole N n r v η (hη v)).symm.trans (hres v)⟩⟩


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
