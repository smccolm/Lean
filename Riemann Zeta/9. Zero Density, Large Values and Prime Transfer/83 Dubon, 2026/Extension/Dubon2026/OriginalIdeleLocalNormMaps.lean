import Dubon2026.OriginalIdeleNormFiniteLocal
import Dubon2026.OriginalIdeleNormInfiniteLocal
import Dubon2026.OriginalAdicNormIntegralPreimage

/-! # Actual local unit norm maps for original idele norm assembly

The local norm maps retain the actual completed base embeddings, with
lying-over supplied by the actual prime contraction. Their exact original
idele component formulas and integral-preimage implication provide the
local data for a globally restricted preimage in DUB-17's norm-index chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The actual finite-local field unit norm along the original completed embedding at the actual contracted prime. -/
def originalFiniteLocalNorm (w : HeightOneSpectrum (𝓞 L)) :
    (w.adicCompletion L)ˣ →* ((originalFinitePrimeBelow K L w).adicCompletion K)ˣ := by
  letI := originalFinitePrimeBelow_liesOver K L w
  letI : Algebra ((originalFinitePrimeBelow K L w).adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w).toAlgebra
  exact Units.map (Algebra.norm ((originalFinitePrimeBelow K L w).adicCompletion K) (S := w.adicCompletion L))

/-- The actual infinite-local field unit norm along the original completed embedding at the restricted infinite place. -/
def originalInfiniteLocalNorm (w : InfinitePlace L) :
    w.Completionˣ →* (w.comap (algebraMap K L)).Completionˣ := by
  letI : Algebra (w.comap (algebraMap K L)).Completion w.Completion :=
    (originalInfiniteCompletionBaseChange K L w).toAlgebra
  exact Units.map (Algebra.norm (w.comap (algebraMap K L)).Completion (S := w.Completion))

variable [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- An actual finite-local norm preimage of an original integer unit is integral and invertible in the original local integers. -/
theorem originalFiniteLocalNorm_preimage_integerUnit (w : HeightOneSpectrum (𝓞 L))
    (u : (w.adicCompletion L)ˣ)
    (hu : originalFiniteLocalNorm K L w u ∈ ((originalFinitePrimeBelow K L w).adicCompletionIntegers K).units) :
    u ∈ (w.adicCompletionIntegers L).units := by
  letI := originalFinitePrimeBelow_liesOver K L w
  exact originalAdicNorm_preimage_integerUnit K L (originalFinitePrimeBelow K L w) w u hu

variable [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual contracted finite component of the original idele norm is its actual finite-local norm. -/
theorem originalIdeleNorm_finiteLocal (w : HeightOneSpectrum (𝓞 L)) (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) (originalIdeleNorm K L a) =
      originalFiniteLocalNorm K L w (originalIdeleFiniteOrbitNormPreimage K L w a) := by
  letI := originalFinitePrimeBelow_liesOver K L w
  exact originalIdeleNorm_finiteComponent_eq_localNorm K L (originalFinitePrimeBelow K L w) w a

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual restricted infinite component of the original idele norm is its actual infinite-local norm. -/
theorem originalIdeleNorm_infiniteLocal (w : InfinitePlace L) (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a) =
      originalInfiniteLocalNorm K L w (originalIdeleInfiniteOrbitNormPreimage K L w a) :=
  originalIdeleNorm_infiniteComponent_eq_localNorm K L w a

end
end Dubon2026
