import Dubon2026.SourceOriginalWeilMapClasses

/-! DUB-17/18 -> finite-map Weil adjunction. Assemble the proved
pullback and norm class identities for fixed principal representatives. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M] {n : ℕ} [NeZero n]

theorem exists_original_weil_adjunction_witness
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L))
    (E : Divisor.degZero (K := L) (F := modularFunctionFieldOver M L))
    (f : modularFunctionFieldOver N L) (g : modularFunctionFieldOver M L)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hordf : ∀ v : Place L (modularFunctionFieldOver N L), v.ord f = n * D.val v)
    (hordg : ∀ w : Place L (modularFunctionFieldOver M L), w.ord g = n * E.val w)
    (havoid : ∀ w ∈ (Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D.val).support,
      E.val w = 0) :
    ∃ d : OriginalWeilDatum N L n, ∃ e : OriginalWeilDatum M L n,
      d.classLeft.val = Pic0.mk D ∧ e.classRight.val = Pic0.mk E ∧
      e.classLeft.val = originalPicardPullback L N M φ (Pic0.mk D) ∧
      d.classRight.val = originalPicardNorm L N M φ (Pic0.mk E) ∧ d.pairing = e.pairing := by
  let e : OriginalWeilDatum M L n := originalWeilPullbackDatum L N M φ D E f g hf hg hordf hordg havoid
  let d : OriginalWeilDatum N L n := originalWeilNormDatum L N M φ e D.val f hf hordf rfl
  have heR : e.classRight.val = Pic0.mk E :=
    originalWeilPullbackDatum_classRight L N M φ D E f g hf hg hordf hordg havoid
  refine ⟨d, e, originalWeilNormDatum_classLeft L N M φ D e f hf hordf rfl, heR,
    originalWeilPullbackDatum_classLeft L N M φ D E f g hf hg hordf hordg havoid, ?_,
    originalWeilNormDatum_pairing L N M φ e D.val f hf hordf rfl rfl⟩
  exact (originalWeilNormDatum_classRight L N M φ D e f hf hordf rfl).trans
    (congrArg (originalPicardNorm L N M φ) heR)

end
end Dubon2026.SourceFunctionField
