import Dubon2026.OriginalAdicFieldRestriction

/-! # Base change on the original completed fields

This is the original field embedding completed at actual primes lying
over one another. Its integral-membership equivalence supplies the local
restricted-product condition in DUB-17's native idele norm comparison.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace WithZeroTopology
open scoped NumberField WithZero

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The actual base-field embedding, extended to the original adic completions. -/
def originalAdicBaseChangeMap : v.adicCompletion K →+* w.adicCompletion L :=
  Completion.mapRingHom (WithVal.map (v.valuation K) (w.valuation L) (algebraMap K L))
    (original_adicFieldMap_uniformContinuous K L v w).continuous

/-- On the original field the completed map is the actual algebra map. -/
theorem originalAdicBaseChangeMap_algebraMap (x : K) :
    originalAdicBaseChangeMap K L v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  change Completion.mapRingHom _ _
    (↑(WithVal.toVal (v.valuation K) x) : v.adicCompletion K) = _
  rw [Completion.mapRingHom_coe]
  rfl

/-- The actual map of original completions is continuous. -/
theorem originalAdicBaseChangeMap_continuous :
    Continuous (originalAdicBaseChangeMap K L v w) := Completion.continuous_map

/-- The completed map retains the original ramification-index power formula. -/
theorem originalAdicBaseChangeMap_valuation (x : v.adicCompletion K) :
    Valued.v (originalAdicBaseChangeMap K L v w x) =
      (Valued.v x : ℤᵐ⁰) ^ v.asIdeal.ramificationIdx w.asIdeal := by
  induction x using Completion.induction_on
  · exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective L)).comp
        (originalAdicBaseChangeMap_continuous K L v w))
      ((Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)).pow _)
  · rename_i x
    change Valued.v (originalAdicBaseChangeMap K L v w
      (algebraMap K (v.adicCompletion K) x.ofVal)) = _
    rw [originalAdicBaseChangeMap_algebraMap]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Valued.valuedCompletion_apply]
    exact original_valuation_algebraMap_pow K L v w x.ofVal

/-- Integrality in the original completed valuation ring is preserved and reflected. -/
theorem originalAdicBaseChangeMap_mem_integers (x : v.adicCompletion K) :
    originalAdicBaseChangeMap K L v w x ∈ w.adicCompletionIntegers L ↔
      x ∈ v.adicCompletionIntegers K := by
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers,
    originalAdicBaseChangeMap_valuation]
  exact pow_le_one_iff_of_nonneg zero_le (by
    exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot)

end
end Dubon2026
