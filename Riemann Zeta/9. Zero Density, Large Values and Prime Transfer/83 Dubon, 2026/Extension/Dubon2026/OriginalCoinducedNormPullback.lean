import Dubon2026.OriginalCoinducedExtensionDiagram
import Dubon2026.OriginalCoefficientNormComposition

/-! # Pull a literal norm back through the actual shift diagram

Projectivity lifts the linear norm preimage across the target quotient.
Subtracting its norm corrects the middle map into the target kernel.
The proved norm surjectivity for maps from the original coinduced
source then supplies a norm witness for the original left map. This
is the reverse step used twice in DUB-17's finite norm criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] [Fintype G] (M : Rep.{0} ℤ G)

/-- A literal norm on the right of the genuine shift diagram constructs a literal norm for its original left map. -/
theorem originalCoinducedDiagram_norm_pullback
    [Module.Projective ℤ (originalCoinducedQuotient M)]
    {Y : ShortComplex (Rep ℤ G)} (hY : Y.ShortExact)
    (d : originalCoinducedShortComplex M ⟶ Y)
    (η : originalCoinducedQuotient M →ₗ[ℤ] Y.X₃)
    (hη : originalCoefficientNormMorphism (originalCoinducedQuotient M) Y.X₃ η = d.τ₃) :
    ∃ ξ : M →ₗ[ℤ] Y.X₁, originalCoefficientNormMorphism M Y.X₁ ξ = d.τ₁ := by
  letI := hY.mono_f
  obtain ⟨η', hη'⟩ := Module.projective_lifting_property Y.g.hom.toLinearMap η
    ((Rep.epi_iff_surjective _).mp hY.epi_g)
  let t := originalCoefficientNormMorphism (originalCoinducedQuotient M) Y.X₂ η'
  have ht : t ≫ Y.g = d.τ₃ :=
    (originalCoefficientNorm_postcomp η' Y.g).trans
      ((congrArg (originalCoefficientNormMorphism (originalCoinducedQuotient M) Y.X₃) hη').trans hη)
  let b := d.τ₂ - (originalCoinducedShortComplex M).g ≫ t
  have hb : b ≫ Y.g = 0 := by
    dsimp only [b]
    rw [Preadditive.sub_comp, Category.assoc]
    erw [ht]
    rw [← d.comm₂₃, sub_self]
  obtain ⟨l, hl⟩ := hY.exact.lift' b hb
  have hu : originalCoinducedUnit M ≫ l = d.τ₁ := by
    apply (cancel_mono Y.f).mp
    rw [Category.assoc]
    erw [hl]
    change originalCoinducedUnit M ≫ (d.τ₂ - (originalCoinducedShortComplex M).g ≫ t) = _
    erw [Preadditive.comp_sub, ← Category.assoc]
    have hz : originalCoinducedUnit M ≫ (originalCoinducedShortComplex M).g = 0 :=
      (originalCoinducedShortComplex M).zero
    rw [hz, Limits.zero_comp, sub_zero]
    exact d.comm₁₂.symm
  obtain ⟨ξ, hξ⟩ := originalCoinducedSource_norm_witness M Y.X₁ l
  refine ⟨ξ.comp (originalCoinducedUnit M).hom.toLinearMap, ?_⟩
  exact (originalCoefficientNorm_precomp (originalCoinducedUnit M) ξ).symm.trans
    ((congrArg (fun f => originalCoinducedUnit M ≫ f) hξ).trans hu)

end
end Dubon2026
