import Dubon2026.OriginalLocalCompletionSurjective

/-! # Continuity of both directions of the actual completion equivalence

The proved closed embedding and surjectivity retain both original
topologies. This is needed to transport original prime-stabilizer actions
to the arithmetic orbit field on DUB-17's prime-indexing route.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField ValuativeRel

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  (hgen : (algebraMap (rationalPrimeLocalField p hp) E).fieldRange ⊔ (algebraMap L E).fieldRange = ⊤)

/-- The literal original completion equivalence is continuous. -/
theorem originalLocalCompletionEquiv_continuous :
    Continuous (originalLocalCompletionEquiv L E p hp hgen) :=
  originalLocalCompletionMap_continuous L E p hp

/-- Its actual inverse is continuous for the same original topologies. -/
theorem originalLocalCompletionEquiv_symm_continuous :
    Continuous (originalLocalCompletionEquiv L E p hp hgen).symm := by
  apply (originalLocalCompletionMap_isClosedEmbedding L E p hp).isEmbedding.continuous_iff.mpr
  change Continuous (fun x : E => originalLocalCompletionEquiv L E p hp hgen
    ((originalLocalCompletionEquiv L E p hp hgen).symm x))
  simpa only [RingEquiv.apply_symm_apply] using (continuous_id : Continuous (fun x : E => x))

end
end Dubon2026
