/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Comparison calculations adapt P2M/Sol/
S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.lean
at revision 6e837e75355538c7f80bab5b956861e86c4eacc2. Pinned projectivity
and the actual short-complex API replace the external lifting hypotheses.
-/
import Dubon2026.OriginalRelationModuleSequence
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Actual presentation comparisons for the relation-kernel reduction

DUB-17's remaining nontrivial-action extension step transports a literal
norm witness through the original short exact presentations. Projectivity
constructs comparison maps; their difference factors through the original
free term. The required integral retraction uses the pinned splitting
theorem, avoiding a new elementwise construction of a linear section.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G]

/-- Projectivity of the actual middle term lifts a coefficient map to a
commuting map of the original presentations. -/
theorem originalPresentation_exists_comparison
    (X Y : ShortComplex (Rep.{0} ℤ G)) (hY : Y.ShortExact)
    [Projective X.X₂] (m : X.X₃ ⟶ Y.X₃) :
    ∃ (cR : X.X₁ ⟶ Y.X₁) (cP : X.X₂ ⟶ Y.X₂),
      X.f ≫ cP = cR ≫ Y.f ∧ X.g ≫ m = cP ≫ Y.g := by
  letI := hY.epi_g
  letI := hY.mono_f
  let cP := Projective.factorThru (X.g ≫ m) Y.g
  have hcP : cP ≫ Y.g = X.g ≫ m := Projective.factorThru_comp _ _
  have h0 : (X.f ≫ cP) ≫ Y.g = 0 := by
    rw [Category.assoc, hcP, ← Category.assoc, X.zero, Limits.zero_comp]
  exact ⟨hY.exact.lift (X.f ≫ cP) h0, cP,
    (hY.exact.lift_f _ _).symm, hcP.symm⟩

/-- Two actual presentation comparisons over the same coefficient map
differ on the relation module by a map through the original free term. -/
theorem originalPresentation_comparison_difference
    (X Y : ShortComplex (Rep.{0} ℤ G)) (hY : Y.ShortExact) (m : X.X₃ ⟶ Y.X₃)
    (cR dR : X.X₁ ⟶ Y.X₁) (cP dP : X.X₂ ⟶ Y.X₂)
    (hc₁ : X.f ≫ cP = cR ≫ Y.f) (hc₂ : X.g ≫ m = cP ≫ Y.g)
    (hd₁ : X.f ≫ dP = dR ≫ Y.f) (hd₂ : X.g ≫ m = dP ≫ Y.g) :
    ∃ t : X.X₂ ⟶ Y.X₁, cR - dR = X.f ≫ t := by
  letI := hY.mono_f
  have h0 : (cP - dP) ≫ Y.g = 0 := by
    rw [Preadditive.sub_comp, ← hc₂, ← hd₂, sub_self]
  refine ⟨hY.exact.lift (cP - dP) h0, ?_⟩
  rw [← cancel_mono Y.f, Category.assoc, hY.exact.lift_f,
    Preadditive.comp_sub, Preadditive.sub_comp, hc₁, hd₁]

/-- A genuine short exact coefficient sequence with integrally projective
quotient admits an actual integral retraction of its inclusion. -/
theorem originalPresentation_integral_retraction
    (X : ShortComplex (Rep.{0} ℤ G)) (hX : X.ShortExact)
    [Module.Projective ℤ X.X₃] :
    ∃ r : X.X₂ →ₗ[ℤ] X.X₁, ∀ x : X.X₁, r (X.f.hom x) = x := by
  letI := hX.mono_f
  letI := hX.epi_g
  let U := X.map (forget₂ (Rep ℤ G) (ModuleCat ℤ))
  have hU : U.ShortExact := hX.map _
  letI : Projective U.X₃ := inferInstanceAs (Projective (ModuleCat.of ℤ X.X₃))
  let s := hU.splittingOfProjective
  exact ⟨s.r.hom, fun x => congrArg (fun f : U.X₁ ⟶ U.X₁ => f.hom x) s.f_r⟩

end
end Dubon2026
