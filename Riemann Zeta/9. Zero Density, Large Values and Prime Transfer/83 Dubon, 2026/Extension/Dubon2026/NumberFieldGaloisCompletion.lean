import Dubon2026.NumberFieldGaloisValuation
import Dubon2026.ValuationPreservingRingEquiv

/-! # Original Galois transport of the original completed local fields

The original automorphism is extended from the original valued field to
its completion at the transported prime. This is the local map required
to act on original finite ideles in DUB-17's supported exact sequence.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The original automorphism between the original fields with their transported valuations. -/
def numberFieldGaloisWithVal (σ : Gal(L/K)) (v : HeightOneSpectrum (𝓞 L)) :
    WithVal (v.valuation L) ≃+*
      WithVal ((numberFieldGaloisPlaceEquiv K L σ v).valuation L) :=
  WithVal.congr _ _ σ.toRingEquiv

/-- The exact original valuation identity makes the forward local map continuous. -/
theorem numberFieldGaloisWithVal_continuous (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) : Continuous (numberFieldGaloisWithVal K L σ v) := by
  apply (valuationPreservingRingEquiv_uniformContinuous _ ?_).continuous
  intro x
  exact numberFieldGaloisPlace_valuation K L σ v x.ofVal

/-- The same original valuation identity also makes the inverse local map continuous. -/
theorem numberFieldGaloisWithVal_symm_continuous (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) : Continuous (numberFieldGaloisWithVal K L σ v).symm := by
  apply (valuationPreservingRingEquiv_uniformContinuous _ ?_).continuous
  intro x
  have h := numberFieldGaloisPlace_valuation K L σ v (σ.symm x.ofVal)
  simpa only [AlgEquiv.apply_symm_apply] using h.symm

/-- The actual original Galois equivalence between the original completed local fields. -/
def numberFieldGaloisCompletion (σ : Gal(L/K)) (v : HeightOneSpectrum (𝓞 L)) :
    v.adicCompletion L ≃+* (numberFieldGaloisPlaceEquiv K L σ v).adicCompletion L :=
  Completion.mapRingEquiv (numberFieldGaloisWithVal K L σ v)
    (numberFieldGaloisWithVal_continuous K L σ v)
    (numberFieldGaloisWithVal_symm_continuous K L σ v)

/-- On the original global field, the completed map is exactly the original automorphism. -/
theorem numberFieldGaloisCompletion_algebraMap (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    numberFieldGaloisCompletion K L σ v (algebraMap L (v.adicCompletion L) x) =
      algebraMap L ((numberFieldGaloisPlaceEquiv K L σ v).adicCompletion L) (σ x) := by
  change Completion.mapRingHom (numberFieldGaloisWithVal K L σ v).toRingHom
    (numberFieldGaloisWithVal_continuous K L σ v)
    (↑(WithVal.toVal (v.valuation L) x) : v.adicCompletion L) = _
  rw [Completion.mapRingHom_coe]
  rfl

end
end Dubon2026
