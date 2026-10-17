import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # The genuine invariant connecting kernel

The degree-zero long exact sequence identifies zero connecting classes
with actual invariant lifts. This comparison is used to compute the
original augmentation kernel on DUB-17's finite duality route. Keeping
the sequence abstract here avoids repeatedly unfolding the concrete
regular representation during elaboration at the default limits.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G]
  {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

/-- A zero genuine invariant connecting class has a literal invariant lift in the original middle coefficient. -/
theorem originalInvariantConnecting_lift (z : X.X₃.ρ.invariants)
    (hz : (groupCohomology.δ hX 0 1 rfl).hom ((groupCohomology.H0Iso X.X₃).inv z) = 0) :
    ∃ x : X.X₂, x ∈ X.X₂.ρ.invariants ∧ X.g.hom x = z.val := by
  have he : LinearMap.range (groupCohomology.map (MonoidHom.id G) X.g 0).hom =
      LinearMap.ker (groupCohomology.δ hX 0 1 rfl).hom :=
    (groupCohomology.mapShortComplex₃_exact hX (rfl : 0 + 1 = 1)).moduleCat_range_eq_ker
  have hm : (groupCohomology.H0Iso X.X₃).inv z ∈
      LinearMap.range (groupCohomology.map (MonoidHom.id G) X.g 0).hom := by
    rw [he]
    exact hz
  obtain ⟨t, ht⟩ := hm
  let xi := (groupCohomology.H0Iso X.X₂).hom t
  have hn : (groupCohomology.H0Iso X.X₃).hom
      ((groupCohomology.functor k G 0).map X.g t) =
      ((Rep.invariantsFunctor k G).map X.g) xi :=
    congrArg (fun m : groupCohomology X.X₂ 0 ⟶ ModuleCat.of k X.X₃.ρ.invariants => m t)
      (groupCohomology.map_id_comp_H0Iso_hom X.g)
  have hi : (groupCohomology.H0Iso X.X₃).hom ((groupCohomology.H0Iso X.X₃).inv z) = z :=
    (groupCohomology.H0Iso X.X₃).toLinearEquiv.apply_symm_apply z
  have heq : ((Rep.invariantsFunctor k G).map X.g) xi = z :=
    hn.symm.trans ((congrArg (fun y => (groupCohomology.H0Iso X.X₃).hom y) ht).trans hi)
  exact ⟨xi.val, xi.property, congrArg Subtype.val heq⟩

/-- An actual invariant lift has zero genuine connecting class. -/
theorem originalInvariantConnecting_zero_of_lift (z : X.X₃.ρ.invariants)
    (x : X.X₂) (hx : x ∈ X.X₂.ρ.invariants) (hg : X.g.hom x = z.val) :
    (groupCohomology.δ hX 0 1 rfl).hom ((groupCohomology.H0Iso X.X₃).inv z) = 0 := by
  let xi : X.X₂.ρ.invariants := ⟨x, hx⟩
  let t := (groupCohomology.H0Iso X.X₂).inv xi
  have ht : (groupCohomology.H0Iso X.X₂).hom t = xi :=
    (groupCohomology.H0Iso X.X₂).toLinearEquiv.apply_symm_apply xi
  have hi : (groupCohomology.H0Iso X.X₃).hom ((groupCohomology.H0Iso X.X₃).inv z) = z :=
    (groupCohomology.H0Iso X.X₃).toLinearEquiv.apply_symm_apply z
  have hn : (groupCohomology.H0Iso X.X₃).hom
      ((groupCohomology.functor k G 0).map X.g t) =
      ((Rep.invariantsFunctor k G).map X.g) ((groupCohomology.H0Iso X.X₂).hom t) :=
    congrArg (fun m : groupCohomology X.X₂ 0 ⟶ ModuleCat.of k X.X₃.ρ.invariants => m t)
      (groupCohomology.map_id_comp_H0Iso_hom X.g)
  have ht' : (groupCohomology.map (MonoidHom.id G) X.g 0).hom t =
      (groupCohomology.H0Iso X.X₃).inv z := by
    apply (groupCohomology.H0Iso X.X₃).toLinearEquiv.injective
    have hg' : ((Rep.invariantsFunctor k G).map X.g) xi = z := Subtype.ext hg
    exact hn.trans ((congrArg (fun y => ((Rep.invariantsFunctor k G).map X.g) y) ht).trans
      (hg'.trans hi.symm))
  have he : LinearMap.range (groupCohomology.map (MonoidHom.id G) X.g 0).hom =
      LinearMap.ker (groupCohomology.δ hX 0 1 rfl).hom :=
    (groupCohomology.mapShortComplex₃_exact hX (rfl : 0 + 1 = 1)).moduleCat_range_eq_ker
  have hm : (groupCohomology.H0Iso X.X₃).inv z ∈
      LinearMap.ker (groupCohomology.δ hX 0 1 rfl).hom := by
    rw [← he]
    exact ⟨t, ht'⟩
  exact hm

/-- The genuine invariant connecting kernel is exactly the actual invariant image. -/
theorem originalInvariantConnecting_zero_iff (z : X.X₃.ρ.invariants) :
    (groupCohomology.δ hX 0 1 rfl).hom ((groupCohomology.H0Iso X.X₃).inv z) = 0 ↔
      ∃ x : X.X₂, x ∈ X.X₂.ρ.invariants ∧ X.g.hom x = z.val :=
  ⟨originalInvariantConnecting_lift hX z,
    fun ⟨x, hx, hg⟩ => originalInvariantConnecting_zero_of_lift hX z x hx hg⟩

end
end Dubon2026
