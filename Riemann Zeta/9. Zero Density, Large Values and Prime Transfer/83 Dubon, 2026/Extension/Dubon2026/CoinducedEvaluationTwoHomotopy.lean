import Dubon2026.ContinuousCoinducedShapiroTwoHomotopy

/-! # The original H2 evaluation/Shapiro homotopy

The actual identity-coset coordinate need not be one. Three original cocycle
identities give its conjugation correction with a continuous original
one-cochain. This supplies the remaining inverse in DUB-17's low-degree
continuous induced-module comparison.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G)

/-- The original one-cochain correcting inner conjugation by the actual
identity-coset coordinate in the H2 comparison. -/
def coefficientConjugationTwoHomotopy (c : G × G → A) (r : G) : G → A :=
  fun g => c (r, r⁻¹ * g * r) - c (g, r)

/-- The original two-cocycle identity gives the precise conjugation boundary,
without any normalization assumption on the cocycle or the conjugating element. -/
theorem coefficientConjugationTwoHomotopy_differential
    (c : groupCohomology.cocycles₂ A) (r g h : G) :
    groupCohomology.d₁₂ A (coefficientConjugationTwoHomotopy A c r) (g, h) =
      A.ρ r (c (r⁻¹ * g * r, r⁻¹ * h * r)) - c (g, h) := by
  have h₁ := (groupCohomology.mem_cocycles₂_iff _).mp c.property g h r
  have h₂ := (groupCohomology.mem_cocycles₂_iff _).mp c.property g r (r⁻¹ * h * r)
  have h₃ := (groupCohomology.mem_cocycles₂_iff _).mp c.property r (r⁻¹ * g * r) (r⁻¹ * h * r)
  have hrh : r * (r⁻¹ * h * r) = h * r := by group
  have hrg : r * (r⁻¹ * g * r) = g * r := by group
  have hprod : (r⁻¹ * g * r) * (r⁻¹ * h * r) = r⁻¹ * (g * h) * r := by group
  rw [hrh] at h₂
  rw [hrg, hprod] at h₃
  have he := congrArg₂ (fun a b : A => a - b)
    (congrArg₂ (fun a b : A => a + b) h₁ h₃) h₂
  change A.ρ g (c (r, r⁻¹ * h * r) - c (h, r)) -
    (c (r, r⁻¹ * (g * h) * r) - c (g * h, r)) +
    (c (r, r⁻¹ * g * r) - c (g, r)) = _
  rw [map_sub]
  apply sub_eq_zero.mp
  calc
    _ = ((c (g * h, r) + c (g, h)) +
          (c (g * r, r⁻¹ * h * r) + c (r, r⁻¹ * g * r)) -
          (c (g * r, r⁻¹ * h * r) + c (g, r))) -
        ((A.ρ g (c (h, r)) + c (g, h * r)) +
          (A.ρ r (c (r⁻¹ * g * r, r⁻¹ * h * r)) + c (r, r⁻¹ * (g * h) * r)) -
          (A.ρ g (c (r, r⁻¹ * h * r)) + c (g, h * r))) := by abel
    _ = 0 := sub_eq_zero.mpr he

/-- The original conjugation correction preserves continuity of the actual
two-cocycle; its boundary therefore exists in continuous H2. -/
theorem coefficientConjugationTwoHomotopy_continuous
    [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace A] [IsTopologicalAddGroup A]
    (c : G × G → A) (hc : Continuous c) (r : G) :
    Continuous (coefficientConjugationTwoHomotopy A c r) :=
  (hc.comp (continuous_const.prodMk
    ((continuous_const.mul continuous_id).mul continuous_const))).sub
      (hc.comp (continuous_id.prodMk continuous_const))

/-- Evaluation of the original Shapiro lift differs from the original subgroup
two-cocycle by the boundary at the actual identity-coset coordinate. -/
theorem coinducedEvaluation_shapiroTwo_sub (S : Subgroup G)
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    (fun z : S × S => (coinducedShapiroTwo A S c (z.1, z.2)).val 1) - c.val =
      groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype)
        (coefficientConjugationTwoHomotopy (restrictedCoefficientRep A S.subtype) c
          (coinducedSubgroupCoordinate S 1)) := by
  funext z
  rcases z with ⟨g, h⟩
  let r := coinducedSubgroupCoordinate S 1
  have he := coefficientConjugationTwoHomotopy_differential
    (restrictedCoefficientRep A S.subtype) c r g h
  change (coinducedShapiroTwo A S c (g, h)).val 1 - c (g, h) = _
  rw [coinducedShapiroTwo_apply, one_mul, coinducedSubgroupCoordinate_subgroup]
  have hp : coinducedSubgroupCoordinate S ((g : G) * (h : G)) = (g * h) * r :=
    coinducedSubgroupCoordinate_subgroup S (g * h)
  rw [hp]
  have harg : (g * r)⁻¹ * ((g * h) * r) = r⁻¹ * h * r := by group
  rw [harg]
  simpa only [mul_assoc] using he.symm

end
end Dubon2026
