import Dubon2026.OriginalIdeleInfiniteH2
import Dubon2026.OriginalFullIdeleBaseChangeH2

/-! # Infinite vanishing for the actual base-changed single-prime witness

Use the literal coefficient constructor and its actual infinite completion
map. This is the needed base-change edge for DUB-17's auxiliary generator
transfer; no general infinite-localization naturality hypothesis is assumed.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

/-- Base change retains identity at every infinite coordinate of the same
original single-finite-prime idele. -/
theorem originalIdeleSingleFinite_baseChange_infinite
    (L M : Type) [Field L] [NumberField L] [Field M] [NumberField M] [Algebra L M]
    (w : HeightOneSpectrum (𝓞 L)) (u : (w.adicCompletion L)ˣ) (v : InfinitePlace M) :
    numberFieldIdeleInfiniteComponent M v
      (originalIdeleBaseChangeMap L M (originalIdeleSingleFinite L w u)) = 1 := by
  apply Units.ext
  change originalInfiniteCompletionBaseChange L M v (1 : (v.comap (algebraMap L M)).Completion) = 1
  exact map_one _

variable (K E L M : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L]

/-- The actual base change of the original single-prime H2 lift has zero
original infinite localization at every target place. -/
theorem originalFullDecompositionIdeleH2Lift_baseChange_infinite
    (w : HeightOneSpectrum (𝓞 L)) (hw : OriginalFiniteDecompositionGroup K L w = ⊤)
    (v : InfinitePlace M) (x : groupCohomology (originalAdicUnitRep K L w) 2) :
    originalFullIdeleInfiniteH2 E M v
      (originalFullIdeleBaseChangeH2 K E L M (originalFullDecompositionIdeleH2Lift K L w hw x)) = 0 := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [originalFullIdeleInfiniteH2, originalFullIdeleBaseChangeH2,
      originalFullDecompositionIdeleH2Lift, ModuleCat.comp_apply,
      originalCohomologyReindex, CategoryTheory.asIso_hom,
      groupCohomology.functor, groupCohomology.H2π_comp_map_apply]
    rw [← map_zero (groupCohomology.H2π (originalInfiniteUnitRep E M v)).hom]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext gh
    exact congrArg Additive.ofMul (originalIdeleSingleFinite_baseChange_infinite L M w _ v)

end
end Dubon2026
