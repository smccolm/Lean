import Dubon2026.OriginalContravariantHomSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-! # Exactness of the actual contravariant Hom sequence

The pinned integer Ext exact sequence supplies the one necessary lifting
step. The remaining maps are the original precomposition maps. Applying
this to the actual restricted relation presentation and the proved S-unit
integer Ext vanishing discharges the dual-exactness input to DUB-17's
continuous cup/connecting comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Abelian
attribute [local instance 1100] Rep.hV2
variable {G : Type} [Group G] (X : ShortComplex (Rep.{0} ℤ G)) (C : Rep.{0} ℤ G)

/-- Vanishing of the actual integer Ext obstruction makes literal
precomposition a short exact dual coefficient sequence. -/
theorem originalContravariantHom_shortExact_of_integerExt
    (hX : X.ShortExact)
    (hExt : ∀ x : Ext (ModuleCat.of ℤ X.X₃) (ModuleCat.of ℤ C) 1, x = 0) :
    (originalContravariantHomShortComplex X C).ShortExact := by
  let S := X.map (forget₂ (Rep ℤ G) (ModuleCat ℤ))
  have hS : S.ShortExact := hX.map_of_exact _
  let Y := ModuleCat.of ℤ C
  have hg := (Rep.epi_iff_surjective X.g).mp hX.epi_g
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (fun η θ h => by
      apply LinearMap.ext
      intro x
      obtain ⟨b, rfl⟩ := hg x
      exact LinearMap.congr_fun h b)
    epi_g := (Rep.epi_iff_surjective _).mpr (fun η => by
      change X.X₁ →ₗ[ℤ] C at η
      let t : S.X₁ ⟶ Y := ModuleCat.ofHom η
      have hz : hS.extClass.comp (Ext.mk₀ t) (show 1 + 0 = 1 from rfl) = 0 := hExt _
      obtain ⟨v, hv⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ t)
        (show 1 + 0 = 1 from rfl) hz
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective S.X₂ Y).surjective v
      rw [Ext.mk₀_comp_mk₀] at hv
      have he : S.f ≫ g = t := (Ext.mk₀_bijective S.X₁ Y).injective hv
      exact ⟨g.hom, congrArg (fun f : S.X₁ ⟶ Y => f.hom) he⟩) }
  apply ((originalContravariantHomShortComplex X C).exact_map_iff_of_faithful
    (forget₂ (Rep ℤ G) (ModuleCat ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro η hη
  change X.X₂ →ₗ[ℤ] C at η
  change η.comp X.f.hom.toLinearMap = 0 at hη
  let t : S.X₂ ⟶ Y := ModuleCat.ofHom η
  have hz : (Ext.mk₀ S.f).comp (Ext.mk₀ t) (zero_add 0) = 0 := by
    rw [Ext.mk₀_comp_mk₀]
    have he : S.f ≫ t = 0 := ModuleCat.hom_ext hη
    rw [he]
    simp
  obtain ⟨v, hv⟩ := Ext.contravariant_sequence_exact₂ hS Y (Ext.mk₀ t) hz
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective S.X₃ Y).surjective v
  rw [Ext.mk₀_comp_mk₀] at hv
  have he : S.g ≫ g = t := (Ext.mk₀_bijective S.X₂ Y).injective hv
  exact ⟨g.hom, congrArg (fun f : S.X₂ ⟶ Y => f.hom) he⟩

end
end Dubon2026
