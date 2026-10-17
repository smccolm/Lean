import Dubon2026.OriginalPositiveCoinducedShifts

/-! # Actual positive inflation for an acyclic normal subgroup

For the finite class/Ext converse, subgroup induction must compare the
actual cohomology of a group with that of quotient-group invariants.
Reuse the existing H1 inflation-restriction sequence, positive coinduced
shifts and genuine connecting naturality. This supplies that comparison
without a spectral-sequence or integer-graded Tate construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (S : Subgroup G) [S.Normal]

/-- Vanishing of actual subgroup H1 makes the original first inflation an isomorphism. -/
theorem originalFirstInflation_isIso_of_subgroup_zero
    (h : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    IsIso (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
      (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 1) := by
  let X := groupCohomology.H1InfRes A S
  have hz : X.g = 0 := h.eq_zero_of_tgt _
  haveI : Epi X.f := (ModuleCat.epi_iff_surjective _).mpr (by
    intro x
    have hx : x ∈ X.f.hom.range := by
      rw [(groupCohomology.H1InfRes_exact A S).moduleCat_range_eq_ker]
      change X.g x = 0
      rw [hz]
      rfl
    exact hx)
  change IsIso X.f
  exact isIso_of_mono_of_epi X.f

/-- If all actual positive subgroup cohomology vanishes, original inflation from quotient invariants is an isomorphism in every positive degree. -/
theorem originalPositiveInflation_isIso_of_subgroup_zero
    (h : ∀ n : ℕ, Limits.IsZero (groupCohomology (Rep.res S.subtype A) (n + 1)))
    (n : ℕ) :
    IsIso (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
      (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) (n + 1)) := by
  induction n generalizing A with
  | zero => exact originalFirstInflation_isIso_of_subgroup_zero A S (h 0)
  | succ n ih =>
    let dQ := groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S (h 0))
      (n + 1) (n + 2) rfl
    let dG := groupCohomology.δ (originalCoinducedShortComplex_shortExact A)
      (n + 1) (n + 2) rfl
    let iQ := groupCohomology.map (A := (originalCoinducedQuotient A).quotientToInvariants S)
      (B := originalCoinducedQuotient A) (QuotientGroup.mk' S)
      (Rep.ofHom ((originalCoinducedQuotient A).ρ.quotientToInvariants_lift S)) (n + 1)
    let iG := groupCohomology.map (A := A.quotientToInvariants S) (B := A)
      (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) (n + 2)
    have hQ : IsIso dQ := originalCoinducedInvariantPositiveShift_isIso A S (h 0) n
    have hG : IsIso dG := originalCoinducedGlobalPositiveShift_isIso A n
    have hiQ : IsIso iQ := ih (originalCoinducedQuotient A)
      (originalCoinducedQuotient_subgroup_positive_zero A S h)
    have hn : dQ ≫ iG = iQ ≫ dG :=
      originalCohomologyGroupChange_delta_naturality (QuotientGroup.mk' S)
        (normalInvariantSequenceInflationMap (originalCoinducedShortComplex A) S)
        (originalCoinducedInvariantSequence_shortExact A S (h 0))
        (originalCoinducedShortComplex_shortExact A) (n + 1) (n + 2) rfl
    have hcomp : IsIso (dQ ≫ iG) := by rw [hn]; exact IsIso.comp_isIso' hiQ hG
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ dQ iG hQ hcomp

end
end Dubon2026
