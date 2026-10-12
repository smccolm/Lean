import Dubon2026.InvariantCoefficientExactness

/-! # The original normal-subgroup invariant coefficient sequence -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]
  (X : ShortComplex (Rep.{0} k G)) (S : Subgroup G) [S.Normal]

/-- Apply the actual normal-subgroup invariant representations and the
original coefficient maps to the original short complex. -/
def normalInvariantCoefficientSequence : ShortComplex (Rep k (G ⧸ S)) where
  X₁ := X.X₁.quotientToInvariants S
  X₂ := X.X₂.quotientToInvariants S
  X₃ := X.X₃.quotientToInvariants S
  f := (Rep.quotientToInvariantsFunctor k S).map X.f
  g := (Rep.quotientToInvariantsFunctor k S).map X.g
  zero := by
    apply Rep.hom_ext
    ext x
    exact congrArg (fun f : X.X₁ ⟶ X.X₃ => f.hom x.val) X.zero

/-- Actual restricted exactness and vanishing first cohomology of the
original kernel prove exactness of the genuine quotient-group invariant sequence. -/
theorem normalInvariantCoefficientSequence_shortExact
    (hX : (X.map (Rep.resFunctor S.subtype)).ShortExact)
    (hzero : Limits.IsZero (groupCohomology (Rep.res S.subtype X.X₁) 1)) :
    (normalInvariantCoefficientSequence X S).ShortExact := by
  have hi := invariantCoefficientSequence_shortExact_of_first_zero
    (X.map (Rep.resFunctor S.subtype)) hX hzero
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr
      ((ModuleCat.mono_iff_injective _).mp hi.mono_f)
    epi_g := (Rep.epi_iff_surjective _).mpr
      ((ModuleCat.epi_iff_surjective _).mp hi.epi_g) }
  apply ((normalInvariantCoefficientSequence X S).exact_map_iff_of_faithful
    (forget₂ (Rep.{0} k (G ⧸ S)) (ModuleCat.{0} k))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact hi.exact.moduleCat_range_eq_ker

end
end Dubon2026
