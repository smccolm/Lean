import Dubon2026.OriginalHomologyFirstFromCoinvariants

/-! # Original norm-zero classes and the actual homology boundary

For DUB-17's converse norm criterion, a norm witness in the fundamental
coefficient projects to a norm-zero augmentation coefficient. The
actual augmentation homology sequence must lift its coinvariant class
to first homology of the integral dual. The following statements use
the pinned H0 comparison and long exact sequence for precisely this step.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G]

/-- The actual H0 comparison carries an original coefficient map to its literal coinvariant map. -/
theorem originalHomologyH0_coinvariant_naturality
    {A B : Rep.{0} k G} (f : A ⟶ B) (x : groupHomology A 0) :
    (groupHomology.H0Iso B).hom ((groupHomology.functor k G 0).map f x) =
      Representation.Coinvariants.map A.ρ B.ρ f.hom ((groupHomology.H0Iso A).hom x) :=
  congrArg (fun j => j.hom x) (groupHomology.map_id_comp_H0Iso_hom f)

/-- Exactness of the original coefficient sequence gives literal coinvariant preimages. -/
theorem originalCoinvariant_exact_lift
    {X : ShortComplex (Rep.{0} k G)} (hX : X.ShortExact)
    (x : X.X₂.ρ.Coinvariants)
    (hx : Representation.Coinvariants.map X.X₂.ρ X.X₃.ρ X.g.hom x = 0) :
    ∃ y : X.X₁.ρ.Coinvariants,
      Representation.Coinvariants.map X.X₁.ρ X.X₂.ρ X.f.hom y = x := by
  let a := (groupHomology.H0Iso X.X₂).inv x
  have ha : (groupHomology.functor k G 0).map X.g a = 0 := by
    apply (ModuleCat.mono_iff_injective (groupHomology.H0Iso X.X₃).hom).mp inferInstance
    have he : (groupHomology.H0Iso X.X₂).hom a = x :=
      (groupHomology.H0Iso X.X₂).toLinearEquiv.apply_symm_apply x
    have hn := originalHomologyH0_coinvariant_naturality X.g a
    rw [he, hx] at hn
    exact hn.trans (groupHomology.H0Iso X.X₃).hom.hom.map_zero.symm
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (groupHomology.mapShortComplex₂_exact hX 0) a ha
  refine ⟨(groupHomology.H0Iso X.X₁).hom b, ?_⟩
  have hb' : (groupHomology.functor k G 0).map X.f b = a := hb
  have he : (groupHomology.H0Iso X.X₂).hom a = x :=
    (groupHomology.H0Iso X.X₂).toLinearEquiv.apply_symm_apply x
  exact (originalHomologyH0_coinvariant_naturality X.f b).symm.trans
    ((congrArg (fun v => (groupHomology.H0Iso X.X₂).hom v) hb').trans he)

/-- A literal norm-zero coefficient has an actual H1 boundary preimage when the middle coinvariant norm is injective. -/
theorem originalHomology_boundary_of_norm_zero [Fintype G]
    {X : ShortComplex (Rep.{0} k G)} (hX : X.ShortExact)
    (hmid : OriginalNormCoinvariantInjective X.X₂)
    (x : X.X₁) (hx : X.X₁.ρ.norm x = 0) :
    ∃ y : groupHomology X.X₃ 1,
      (groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl y) =
        Representation.Coinvariants.mk X.X₁.ρ x := by
  have hf : X.X₂.ρ.norm (X.f.hom x) = 0 := by
    rw [← originalCoefficientMorphism_norm, hx, map_zero]
  have hc := hmid (X.f.hom x) hf
  let a := (groupHomology.H0Iso X.X₁).inv (Representation.Coinvariants.mk X.X₁.ρ x)
  have ha : (groupHomology.functor k G 0).map X.f a = 0 := by
    apply (ModuleCat.mono_iff_injective (groupHomology.H0Iso X.X₂).hom).mp inferInstance
    have he : (groupHomology.H0Iso X.X₁).hom a = Representation.Coinvariants.mk X.X₁.ρ x :=
      (groupHomology.H0Iso X.X₁).toLinearEquiv.apply_symm_apply _
    have hn := originalHomologyH0_coinvariant_naturality X.f a
    rw [he, Representation.Coinvariants.map_mk, hc] at hn
    exact hn.trans (groupHomology.H0Iso X.X₂).hom.hom.map_zero.symm
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (groupHomology.mapShortComplex₁_exact hX (i := 1) (j := 0) rfl) a ha
  refine ⟨y, ?_⟩
  calc
    _ = (groupHomology.H0Iso X.X₁).hom a := congrArg _ hy
    _ = _ := (groupHomology.H0Iso X.X₁).toLinearEquiv.apply_symm_apply _

end
end Dubon2026
