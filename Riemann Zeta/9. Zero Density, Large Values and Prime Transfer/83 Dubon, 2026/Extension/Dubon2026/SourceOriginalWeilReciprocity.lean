import Dubon2026.SourceOriginalCoordinateWeilReciprocity
import Dubon2026.SourceOriginalConstantWeilReciprocity

/-! DUB-17/18 -> original Weil pairing -> reciprocity on the actual
original modular function field. The constant case uses proved principal
degree zero. Every nonconstant second function gives the finite rational
coordinate used by the proved norm transfer. No reciprocity hypothesis,
finite-map premise or residue identification is supplied by the caller. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

private theorem transcendental_of_not_constant {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] {g : F} (h : g ∉ Set.range (algebraMap K F)) : Transcendental K g := by
  intro ha
  have hm := mem_algebraicClosure_iff.mpr ha
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure K F)] at hm
  exact h (IntermediateField.mem_bot.mp hm)

theorem original_weil_reciprocity (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (N : ℕ) [NeZero N] (f g : modularFunctionFieldOver N L) (hf : f ≠ 0) (hg : g ≠ 0)
    (hdisj : ∀ w : Place L (modularFunctionFieldOver N L), w.ord f ≠ 0 → w.ord g = 0) :
    originalDivisorEval N L f (originalPrincipalDivisor N L g) =
      originalDivisorEval N L g (originalPrincipalDivisor N L f) := by
  classical
  by_cases hc : g ∈ Set.range (algebraMap L (modularFunctionFieldOver N L))
  · obtain ⟨c, rfl⟩ := hc
    exact original_weil_reciprocity_constant L N f c (fun he => hg (by rw [he, map_zero]))
  · have ht := transcendental_of_not_constant hc
    let φ := rationalCoordinate g ht
    have hφ : φ RatFunc.X = g := rationalCoordinate_X g ht
    have hd : ∀ w : Place L (modularFunctionFieldOver N L),
        w.ord f ≠ 0 → w.ord (φ RatFunc.X) = 0 := by
      simpa only [hφ] using hdisj
    simpa only [hφ] using original_weil_reciprocity_coordinate L N φ f hf hd

end
end Dubon2026.SourceFunctionField
