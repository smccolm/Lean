import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # Exact original invariant coefficients from vanishing first cohomology -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Vanishing first cohomology of the original kernel makes the actual
map on invariant coefficients surjective, through the original H0 sequence. -/
theorem invariantCoefficientMap_surjective_of_first_zero
    {k G : Type} [CommRing k] [Group G]
    (X : ShortComplex (Rep.{0} k G)) (hX : X.ShortExact)
    (hzero : Limits.IsZero (groupCohomology X.X₁ 1)) :
    Function.Surjective ((Rep.invariantsFunctor k G).map X.g) := by
  have hep : Epi ((groupCohomology.functor k G 0).map X.g) :=
    (groupCohomology.mapShortComplex₃_exact hX (i := 0) rfl).epi_f
      (hzero.eq_of_tgt _ _)
  intro x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).mp hep ((groupCohomology.H0Iso X.X₃).inv x)
  refine ⟨(groupCohomology.H0Iso X.X₂).hom y, ?_⟩
  have hn := congrArg (fun f : groupCohomology X.X₂ 0 ⟶ ModuleCat.of k X.X₃.ρ.invariants => f y)
    (groupCohomology.map_id_comp_H0Iso_hom X.g)
  change (groupCohomology.H0Iso X.X₃).hom
      (((groupCohomology.functor k G 0).map X.g) y) =
    ((Rep.invariantsFunctor k G).map X.g) ((groupCohomology.H0Iso X.X₂).hom y) at hn
  rw [hy] at hn
  exact hn.symm.trans ((groupCohomology.H0Iso X.X₃).toLinearEquiv.apply_symm_apply x)

/-- The original invariant coefficient sequence is short exact when the
original kernel has zero first cohomology. Its middle exactness is proved
by the original coefficient injection and actual invariant equations. -/
theorem invariantCoefficientSequence_shortExact_of_first_zero
    {k G : Type} [CommRing k] [Group G]
    (X : ShortComplex (Rep.{0} k G)) (hX : X.ShortExact)
    (hzero : Limits.IsZero (groupCohomology X.X₁ 1)) :
    (X.map (Rep.invariantsFunctor k G)).ShortExact := by
  have hf := (Rep.mono_iff_injective X.f).mp hX.mono_f
  refine {
    exact := ?_
    mono_f := (ModuleCat.mono_iff_injective _).mpr ?_
    epi_g := (ModuleCat.epi_iff_surjective _).mpr
      (invariantCoefficientMap_surjective_of_first_zero X hX hzero) }
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    ext x
    change (∃ y : X.X₁.ρ.invariants, ((Rep.invariantsFunctor k G).map X.f) y = x) ↔
      ((Rep.invariantsFunctor k G).map X.g) x = 0
    constructor
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact congrArg (fun f : X.X₁ ⟶ X.X₃ => f.hom y.val) X.zero
    · intro hx
      have hg : X.g.hom x.val = 0 := congrArg Subtype.val hx
      have hex := (hX.exact.map (forget₂ (Rep.{0} k G) (ModuleCat.{0} k))).moduleCat_range_eq_ker
      change X.f.hom.toLinearMap.range = X.g.hom.toLinearMap.ker at hex
      have hxrange : x.val ∈ X.f.hom.toLinearMap.range := by
        rw [hex]
        exact hg
      obtain ⟨y, hy⟩ := hxrange
      change X.f.hom y = x.val at hy
      have hiy : y ∈ X.X₁.ρ.invariants := by
        intro g
        apply hf
        rw [Rep.hom_comm_apply, hy]
        exact x.property g
      exact ⟨⟨y, hiy⟩, Subtype.ext hy⟩
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))

end
end Dubon2026
