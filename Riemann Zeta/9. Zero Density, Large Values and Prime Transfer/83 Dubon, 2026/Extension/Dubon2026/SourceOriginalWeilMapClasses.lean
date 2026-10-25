import Dubon2026.SourceOriginalWeilNormDatum
import Dubon2026.SourceOriginalWeilPullbackDatum

/-! DUB-17/18 -> finite-map Weil adjunction. Identify the actual
Picard classes of the constructed pullback and norm representatives. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M] {n : ℕ} [NeZero n]
variable (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
variable (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L))

section Pullback
variable (E : Divisor.degZero (K := L) (F := modularFunctionFieldOver M L))
variable (f : modularFunctionFieldOver N L) (g : modularFunctionFieldOver M L)
variable (hf : f ≠ 0) (hg : g ≠ 0)
variable (hordf : ∀ v : Place L (modularFunctionFieldOver N L), v.ord f = n * D.val v)
variable (hordg : ∀ w : Place L (modularFunctionFieldOver M L), w.ord g = n * E.val w)
variable (havoid : ∀ w ∈ (Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D.val).support,
  E.val w = 0)

theorem originalWeilPullbackDatum_classLeft :
    (originalWeilPullbackDatum L N M φ D E f g hf hg hordf hordg havoid).classLeft.val =
      originalPicardPullback L N M φ (Pic0.mk D) := by
  rw [originalPicardPullback_mk]
  rfl

omit [IsAlgClosed L] [NeZero N] in
theorem originalWeilPullbackDatum_classRight :
    (originalWeilPullbackDatum L N M φ D E f g hf hg hordf hordg havoid).classRight.val =
      Pic0.mk E := rfl

end Pullback

section Norm
variable (e : OriginalWeilDatum M L n) (f : modularFunctionFieldOver N L) (hf : f ≠ 0)
variable (hord : ∀ v : Place L (modularFunctionFieldOver N L), v.ord f = n * D.val v)
variable (hD : e.D₁ = Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D.val)

theorem originalWeilNormDatum_classLeft :
    (originalWeilNormDatum L N M φ e D.val f hf hord hD).classLeft.val = Pic0.mk D := rfl

theorem originalWeilNormDatum_classRight :
    (originalWeilNormDatum L N M φ e D.val f hf hord hD).classRight.val =
      originalPicardNorm L N M φ e.classRight.val := by
  change Pic0.mk _ = originalPicardNorm L N M φ (Pic0.mk _)
  rw [originalPicardNorm_mk]
  rfl

end Norm
end
end Dubon2026.SourceFunctionField
