import Dubon2026.OriginalSubgroupCosetCoordinates
import Dubon2026.OriginalCoinducedFunctionCoefficients
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # Explicit original subgroup coboundaries for coinduced functions -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- The actual coset coordinates give an explicit original coboundary
witness for every first cocycle of the restricted coinduced coefficient module. -/
theorem originalCoinducedSubgroup_first_coboundary
    (c : groupCohomology.cocycles₁ (Rep.res S.subtype (originalCoinducedFunctionRep A))) :
    ∃ b : originalCoinducedFunctionRep A,
      groupCohomology.d₀₁ (Rep.res S.subtype (originalCoinducedFunctionRep A)) b = c := by
  refine ⟨originalCoinducedFunction A (fun g =>
    (c (subgroupCosetRemainder S g)).val (subgroupCosetRepresentative S g)), ?_⟩
  funext h
  apply Subtype.ext
  funext g
  change (c (subgroupCosetRemainder S (g * h))).val (subgroupCosetRepresentative S (g * h)) -
    (c (subgroupCosetRemainder S g)).val (subgroupCosetRepresentative S g) = (c h).val g
  rw [subgroupCosetRepresentative_mul, subgroupCosetRemainder_mul]
  have hc := congrArg (fun v : originalCoinducedFunctionRep A =>
    v.val (subgroupCosetRepresentative S g))
      ((groupCohomology.mem_cocycles₁_iff _).mp c.property (subgroupCosetRemainder S g) h)
  change (c (subgroupCosetRemainder S g * h)).val (subgroupCosetRepresentative S g) =
    (c h).val (subgroupCosetRepresentative S g * (subgroupCosetRemainder S g : G)) +
      (c (subgroupCosetRemainder S g)).val (subgroupCosetRepresentative S g) at hc
  rw [subgroupCosetRepresentative_mul_remainder] at hc
  exact sub_eq_iff_eq_add.mpr hc

/-- The same original coset coordinates provide an explicit second
coboundary by evaluating the actual cocycle on its subgroup remainder. -/
theorem originalCoinducedSubgroup_second_coboundary
    (c : groupCohomology.cocycles₂ (Rep.res S.subtype (originalCoinducedFunctionRep A))) :
    ∃ b : S → originalCoinducedFunctionRep A,
      groupCohomology.d₁₂ (Rep.res S.subtype (originalCoinducedFunctionRep A)) b = c := by
  refine ⟨fun h => originalCoinducedFunction A (fun g =>
    (c (subgroupCosetRemainder S g, h)).val (subgroupCosetRepresentative S g)), ?_⟩
  funext z
  rcases z with ⟨h, l⟩
  apply Subtype.ext
  funext g
  change (c (subgroupCosetRemainder S (g * h), l)).val (subgroupCosetRepresentative S (g * h)) -
      (c (subgroupCosetRemainder S g, h * l)).val (subgroupCosetRepresentative S g) +
        (c (subgroupCosetRemainder S g, h)).val (subgroupCosetRepresentative S g) = (c (h, l)).val g
  rw [subgroupCosetRepresentative_mul, subgroupCosetRemainder_mul]
  have hc := congrArg (fun v : originalCoinducedFunctionRep A =>
    v.val (subgroupCosetRepresentative S g))
      ((groupCohomology.mem_cocycles₂_iff _).mp c.property (subgroupCosetRemainder S g) h l)
  change (c (subgroupCosetRemainder S g * h, l)).val (subgroupCosetRepresentative S g) +
      (c (subgroupCosetRemainder S g, h)).val (subgroupCosetRepresentative S g) =
    (c (h, l)).val (subgroupCosetRepresentative S g * (subgroupCosetRemainder S g : G)) +
      (c (subgroupCosetRemainder S g, h * l)).val (subgroupCosetRepresentative S g) at hc
  rw [subgroupCosetRepresentative_mul_remainder] at hc
  calc
    _ = ((c (subgroupCosetRemainder S g * h, l)).val (subgroupCosetRepresentative S g) +
      (c (subgroupCosetRemainder S g, h)).val (subgroupCosetRepresentative S g)) -
      (c (subgroupCosetRemainder S g, h * l)).val (subgroupCosetRepresentative S g) := by abel
    _ = _ := sub_eq_iff_eq_add.mpr hc

/-- The first cohomology of the original coinduced functions vanishes
after restriction to every actual subgroup. -/
theorem originalCoinducedSubgroup_first_zero :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalCoinducedFunctionRep A)) 1) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    exact (groupCohomology.H1π_eq_zero_iff _).mpr
      (originalCoinducedSubgroup_first_coboundary A S c)

/-- The second cohomology also vanishes, with the explicit original
coboundary witnesses proved above. -/
theorem originalCoinducedSubgroup_second_zero :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalCoinducedFunctionRep A)) 2) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    exact (groupCohomology.H2π_eq_zero_iff _).mpr
      (originalCoinducedSubgroup_second_coboundary A S c)

end
end Dubon2026
