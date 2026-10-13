import Dubon2026.NumberFieldGaloisCompletion
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Galois transport preserves original completed valuations and units

These are the restricted-product membership obligations for the actual
finite-idele action, which is required by DUB-17's supported sequence.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace WithZeroTopology
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The original completed Galois map is continuous. -/
theorem numberFieldGaloisCompletion_continuous (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) : Continuous (numberFieldGaloisCompletion K L σ v) :=
  Completion.continuous_map

/-- Original valuation preservation extends to every element of the original completion. -/
theorem numberFieldGaloisCompletion_valuation (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) :
    Valued.v (numberFieldGaloisCompletion K L σ v x) =
      (Valued.v x : WithZero (Multiplicative ℤ)) := by
  induction x using Completion.induction_on
  · exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective
        ((numberFieldGaloisPlaceEquiv K L σ v).valuedAdicCompletion_surjective L)).comp
          (numberFieldGaloisCompletion_continuous K L σ v))
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective L))
  · rename_i x
    change Valued.v (numberFieldGaloisCompletion K L σ v
      (algebraMap L (v.adicCompletion L) x.ofVal)) = _
    rw [numberFieldGaloisCompletion_algebraMap]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Valued.valuedCompletion_apply]
    exact numberFieldGaloisPlace_valuation K L σ v x.ofVal

/-- The completed original Galois map preserves membership in the original integer subrings. -/
theorem numberFieldGaloisCompletion_mem_integers (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) :
    numberFieldGaloisCompletion K L σ v x ∈
      (numberFieldGaloisPlaceEquiv K L σ v).adicCompletionIntegers L ↔
        x ∈ v.adicCompletionIntegers L := by
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers,
    numberFieldGaloisCompletion_valuation]

end
end Dubon2026
