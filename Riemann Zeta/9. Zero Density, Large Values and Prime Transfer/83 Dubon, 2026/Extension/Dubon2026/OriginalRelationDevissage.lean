/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The correction and final diagram chase adapt P2M/Sol/
S_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage.lean at
revision 6e837e75355538c7f80bab5b956861e86c4eacc2. Original relation
presentations, native connecting naturality, and the pinned quotient-kernel
isomorphism replace the external arbitrary-presentation and choice helpers.
-/
import Dubon2026.PrimeTorsionFunctionalExtension
import Dubon2026.OriginalPrimeCoefficientCohomology
import Dubon2026.OriginalCoefficientConnectingNaturality
import Dubon2026.CoinducedCohomologyTrace

/-! # Assemble the actual prime-coefficient relation extension

This is the finite dévissage step serving DUB-17's class/Ext duality.
The kernel decomposition, induced middle extension and realization of
quotient functionals are separate upstream obligations. Their actual
commuting presentations produce extension through the original free cover.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Kernel decomposition, middle extension and actual quotient-functional
surjectivity imply extension of the original zero-obstruction morphism. -/
theorem originalRelation_extension_of_devissage
    {G : Type} [Group G] (C : Rep.{0} ℤ G) (p : ℕ) [Fact p.Prime]
    {SB : ShortComplex (Rep.{0} ℤ G)} (hSB : SB.ShortExact)
    (hB₁ : ∀ b : SB.X₃, p • b = 0)
    {R_I P_I : Rep.{0} ℤ G} (f_I : R_I ⟶ P_I) (g_I : P_I ⟶ SB.X₂)
    (w_I : f_I ≫ g_I = 0) (hTI : (ShortComplex.mk f_I g_I w_I).ShortExact)
    (ιR : originalRelationModule SB.X₁ ⟶ R_I) (ιP : Rep.free ℤ G SB.X₁ ⟶ P_I)
    (sq₁ : originalRelationInclusion SB.X₁ ≫ ιP = ιR ≫ f_I)
    (sq₂ : originalRelationFreeCover SB.X₁ ≫ SB.f = ιP ≫ g_I)
    (ρR : R_I ⟶ originalRelationModule SB.X₃) (ρP : P_I ⟶ Rep.free ℤ G SB.X₃)
    (sq₃ : f_I ≫ ρP = ρR ≫ originalRelationInclusion SB.X₃)
    (sq₄ : g_I ≫ SB.g = ρP ≫ originalRelationFreeCover SB.X₃)
    (hker : ∀ χ : originalRelationModule SB.X₁ ⟶ C,
      originalRelationExtensionObstruction SB.X₁ C χ = 0 →
      ∃ (ψ : R_I ⟶ C) (a : Rep.free ℤ G SB.X₁ ⟶ C),
        χ = ιR ≫ ψ + originalRelationInclusion SB.X₁ ≫ a)
    (hmid : ∀ ψ : R_I ⟶ C,
      groupCohomology.δ hTI 1 2 rfl ≫ (groupCohomology.functor ℤ G 2).map ψ = 0 →
      ∃ a : P_I ⟶ C, f_I ≫ a = ψ)
    (hsurj : Function.Surjective (originalRelationExtensionObstruction SB.X₃ C))
    (χ : originalRelationModule SB.X₁ ⟶ C)
    (hz : originalRelationExtensionObstruction SB.X₁ C χ = 0) :
    ∃ a : Rep.free ℤ G SB.X₁ ⟶ C, originalRelationInclusion SB.X₁ ≫ a = χ := by
  let TB := originalRelationShortComplex SB.X₁
  let TQ := originalRelationShortComplex SB.X₃
  let TI := ShortComplex.mk f_I g_I w_I
  let i : TB ⟶ TI := {
    τ₁ := ιR, τ₂ := ιP, τ₃ := SB.f, comm₁₂ := sq₁.symm, comm₂₃ := sq₂.symm }
  let r : TI ⟶ TQ := {
    τ₁ := ρR, τ₂ := ρP, τ₃ := SB.g, comm₁₂ := sq₃.symm, comm₂₃ := sq₄.symm }
  have hi := originalCoefficient_delta_naturality i
    (originalRelationShortComplex_shortExact SB.X₁) hTI 1 2 rfl
  have hr := originalCoefficient_delta_naturality r hTI
    (originalRelationShortComplex_shortExact SB.X₃) 1 2 rfl
  change groupCohomology.δ (originalRelationShortComplex_shortExact SB.X₁) 1 2 rfl ≫
    (groupCohomology.functor ℤ G 2).map ιR =
      (groupCohomology.functor ℤ G 1).map SB.f ≫ groupCohomology.δ hTI 1 2 rfl at hi
  change groupCohomology.δ hTI 1 2 rfl ≫ (groupCohomology.functor ℤ G 2).map ρR =
    (groupCohomology.functor ℤ G 1).map SB.g ≫
      groupCohomology.δ (originalRelationShortComplex_shortExact SB.X₃) 1 2 rfl at hr
  have hδf := (groupCohomology.mapShortComplex₁
    (originalRelationShortComplex_shortExact SB.X₁) (i := 1) (j := 2) rfl).zero
  obtain ⟨ψ, a, hχ⟩ := hker χ hz
  change groupCohomology.δ (originalRelationShortComplex_shortExact SB.X₁) 1 2 rfl ≫
    (groupCohomology.functor ℤ G 2).map (originalRelationInclusion SB.X₁) = 0 at hδf
  change groupCohomology.δ (originalRelationShortComplex_shortExact SB.X₁) 1 2 rfl ≫
    (groupCohomology.functor ℤ G 2).map χ = 0 at hz
  let A : groupCohomology SB.X₂ 1 ⟶ groupCohomology C 2 :=
    groupCohomology.δ hTI 1 2 rfl ≫ (groupCohomology.functor ℤ G 2).map ψ
  have hA : (groupCohomology.functor ℤ G 1).map SB.f ≫ A = 0 := by
    have hii : ιR ≫ ψ = χ - originalRelationInclusion SB.X₁ ≫ a := by rw [hχ]; abel
    change (groupCohomology.functor ℤ G 1).map SB.f ≫
      (groupCohomology.δ hTI 1 2 rfl ≫ (groupCohomology.functor ℤ G 2).map ψ) = 0
    erw [← Category.assoc, ← hi, Category.assoc, ← Functor.map_comp]
    change groupCohomology.δ (originalRelationShortComplex_shortExact SB.X₁) 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map (ιR ≫ ψ) = 0
    erw [hii]
    erw [Functor.map_sub, Preadditive.comp_sub, hz, Functor.map_comp,
      ← Category.assoc, hδf, Limits.zero_comp, sub_zero]
  let q : groupCohomology SB.X₂ 1 ⟶ groupCohomology SB.X₃ 1 :=
    (groupCohomology.functor ℤ G 1).map SB.g
  have hk : q.hom.ker ≤ A.hom.ker := by
    have he := groupCohomology.mapShortComplex₂_exact hSB 1
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at he
    change ((groupCohomology.functor ℤ G 1).map SB.f).hom.range =
      ((groupCohomology.functor ℤ G 1).map SB.g).hom.ker at he
    intro x hx
    change x ∈ ((groupCohomology.functor ℤ G 1).map SB.g).hom.ker at hx
    rw [← he] at hx
    obtain ⟨y, rfl⟩ := hx
    exact congrArg (fun f => f.hom y) hA
  obtain ⟨θ, hθ⟩ := originalPrimeTorsion_functional_extension p
    (originalPrimeCoefficient_first_annihilated SB.X₃ p hB₁) q.hom A.hom hk
  let θM : groupCohomology SB.X₃ 1 ⟶ groupCohomology C 2 := ModuleCat.ofHom θ
  have hθM : q ≫ θM = A := ModuleCat.hom_ext hθ
  obtain ⟨ϑ, hϑ⟩ := hsurj θM
  change groupCohomology.δ (originalRelationShortComplex_shortExact SB.X₃) 1 2 rfl ≫
    (groupCohomology.functor ℤ G 2).map ϑ = θM at hϑ
  have hcorr : groupCohomology.δ hTI 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map (ρR ≫ ϑ) = q ≫ θM := by
    erw [Functor.map_comp, ← Category.assoc, hr]
    change ((groupCohomology.functor ℤ G 1).map SB.g ≫
      groupCohomology.δ (originalRelationShortComplex_shortExact SB.X₃) 1 2 rfl) ≫
        (groupCohomology.functor ℤ G 2).map ϑ = q ≫ θM
    erw [Category.assoc, hϑ]
    rfl
  let ψ' := ψ - ρR ≫ ϑ
  have hψ' : groupCohomology.δ hTI 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map ψ' = 0 := by
    change groupCohomology.δ hTI 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map (ψ - ρR ≫ ϑ) = 0
    erw [Functor.map_sub, Preadditive.comp_sub, hcorr]
    exact sub_eq_zero.mpr hθM.symm
  obtain ⟨aI, haI⟩ := hmid ψ' hψ'
  haveI : Mono (originalRelationInclusion SB.X₃) :=
    (originalRelationShortComplex_shortExact SB.X₃).mono_f
  haveI : Mono (originalRelationShortComplex SB.X₃).f :=
    (originalRelationShortComplex_shortExact SB.X₃).mono_f
  have h0 : (ιP ≫ ρP) ≫ TQ.g = 0 := by
    change (ιP ≫ ρP) ≫ originalRelationFreeCover SB.X₃ = 0
    rw [Category.assoc, ← sq₄, ← Category.assoc, ← sq₂, Category.assoc, SB.zero, Limits.comp_zero]
  let b := (originalRelationShortComplex_shortExact SB.X₃).exact.lift (ιP ≫ ρP) h0
  have hb : b ≫ originalRelationInclusion SB.X₃ = ιP ≫ ρP :=
    (originalRelationShortComplex_shortExact SB.X₃).exact.lift_f _ h0
  have hir : ιR ≫ ρR = originalRelationInclusion SB.X₁ ≫ b := by
    erw [← cancel_mono (originalRelationInclusion SB.X₃), Category.assoc, Category.assoc,
      ← sq₃, ← Category.assoc, ← sq₁, Category.assoc, hb]
  refine ⟨ιP ≫ aI + b ≫ ϑ + a, ?_⟩
  have hψ : ψ = f_I ≫ aI + ρR ≫ ϑ := by rw [haI]; dsimp [ψ']; abel
  rw [hχ, hψ, Preadditive.comp_add, Preadditive.comp_add, Preadditive.comp_add,
    ← Category.assoc, sq₁, Category.assoc, ← Category.assoc ιR ρR, hir]
  rfl

end
end Dubon2026
