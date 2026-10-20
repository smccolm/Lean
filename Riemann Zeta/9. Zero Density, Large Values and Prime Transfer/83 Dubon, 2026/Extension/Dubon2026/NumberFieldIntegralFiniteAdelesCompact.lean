import Dubon2026.NumberFieldIntegralFiniteAdeles
import Dubon2026.OriginalAdicCompletionResidue

/-! # Compactness of the original integral finite adeles

For DUB-17's original adelic unitary levels, the actual integral finite
adeles form a compact open ring. Original completion residue finiteness
and properness are already proved; their compact integer rings and the
native restricted-product topology supply this compactness directly.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Filter
open scoped NumberField RestrictedProduct

variable (K : Type*) [Field K] [NumberField K]

/-- The actual product of completed integer rings maps into the original finite adeles. -/
def numberFieldIntegralFiniteAdeleMap :
    (∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) →+* FiniteAdeleRing (𝓞 K) K where
  toFun a := ⟨fun v => (a v).val, Filter.Eventually.of_forall fun v => (a v).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The original integral product map is continuous in the actual finite-adele topology. -/
theorem numberFieldIntegralFiniteAdeleMap_continuous :
    Continuous (numberFieldIntegralFiniteAdeleMap K) := by
  let f : (∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) →
      Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]_[⊤] :=
    fun a => ⟨fun v => (a v).val, Filter.Eventually.of_forall fun v => (a v).property⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_top.mpr
    (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v))
  exact (RestrictedProduct.continuous_inclusion (show cofinite ≤ ⊤ from le_top)).comp hf

/-- The original integral finite-adele ring is exactly the image of the actual integral product. -/
theorem numberFieldIntegralFiniteAdeleMap_range :
    Set.range (numberFieldIntegralFiniteAdeleMap K) =
      (numberFieldIntegralFiniteAdeles K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact fun v => (x v).property
  · intro ha
    refine ⟨fun v => ⟨a v, ha v⟩, ?_⟩
    apply FiniteAdeleRing.ext
    intro v
    rfl

/-- The original integral finite-adele ring is compact. -/
theorem numberFieldIntegralFiniteAdeles_isCompact :
    IsCompact (numberFieldIntegralFiniteAdeles K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  letI : ∀ v : HeightOneSpectrum (𝓞 K), CompactSpace (v.adicCompletionIntegers K) := fun v => by
    change CompactSpace (Valued.integer (v.adicCompletion K))
    exact Valued.integer.properSpace_iff_compactSpace_integer.mp
      (original_adicCompletion_properSpace K v)
  rw [← numberFieldIntegralFiniteAdeleMap_range]
  exact isCompact_range (numberFieldIntegralFiniteAdeleMap_continuous K)

end
end Dubon2026
