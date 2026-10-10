import Dubon2026.UnramifiedGaloisStageUnion
import Dubon2026.NumberFieldRamificationUnramified

/-! # The genuine base field is an original unramified Galois stage -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- An actual extension isomorphic to the original base field is unramified at every original finite prime. -/
theorem numberField_ramificationIdx_one_of_baseEquiv (e : K ≃ₐ[K] L)
    (w : HeightOneSpectrum (𝓞 L)) :
    (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  let eO : (𝓞 K) ≃ₐ[𝓞 K] (𝓞 L) := NumberField.RingOfIntegers.mapAlgEquiv e
  letI : Algebra.FormallyUnramified (𝓞 K) (𝓞 L) :=
    Algebra.FormallyUnramified.of_equiv eO
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) w.ne_bot

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- The genuine original base-field stage makes the actual unramified finite Galois family nonempty for every original exceptional integer. -/
theorem originalUnramifiedGaloisStage_nonempty (a : 𝓞 K) :
    Nonempty (OriginalUnramifiedGaloisStage (Ω := Ω) a) := by
  letI : NumberField (⊥ : IntermediateField K Ω) := NumberField.of_module_finite K _
  refine ⟨⟨⊥, ?_⟩⟩
  intro w _
  exact numberField_ramificationIdx_one_of_baseEquiv
    (IntermediateField.botEquiv K Ω).symm w

end
end Dubon2026
