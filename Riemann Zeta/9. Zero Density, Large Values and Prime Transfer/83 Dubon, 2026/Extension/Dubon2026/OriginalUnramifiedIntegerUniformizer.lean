import Dubon2026.UnramifiedIntegralValuations
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Dubon2026.OriginalFiniteRamification

/-! # An actual integer uniformizer at every absolutely unramified place

The original integral valuation comparison transfers an integer
uniformizer at the prime below to the original completion. Integers
are fixed by the actual stabilizer; this is the remaining local input
to outside-support vanishing in DUB-17's idele cohomology calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField WithZero
variable (L : Type) [Field L] [NumberField L]

/-- The original prime of the integers below a finite place. -/
def originalIntegerPrimeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum ℤ where
  asIdeal := w.asIdeal.under ℤ
  isPrime := inferInstance
  ne_bot := by
    haveI : Algebra.IsIntegral ℤ (𝓞 L) := Algebra.IsIntegral.of_finite ℤ (𝓞 L)
    exact Ideal.under_ne_bot ℤ w.ne_bot

/-- Outside absolute ramification there is an integer of actual original valuation minus one. -/
theorem original_unramified_exists_integer_uniformizer (w : HeightOneSpectrum (𝓞 L))
    [Algebra.IsUnramifiedAt ℤ w.asIdeal] :
    ∃ r : ℤ, w.intValuation (algebraMap ℤ (𝓞 L) r) = WithZero.exp (-1 : ℤ) := by
  let v := originalIntegerPrimeBelow L w
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : v.asIdeal.ramificationIdx w.asIdeal = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt w.ne_bot
  obtain ⟨r, hr⟩ := v.intValuation_exists_uniformizer
  exact ⟨r, (unramified_intValuation_algebraMap v w he r).trans hr⟩

/-- The same actual integer has uniformizer value in the original completion. -/
theorem original_unramified_exists_completion_integer_uniformizer
    (w : HeightOneSpectrum (𝓞 L)) [Algebra.IsUnramifiedAt ℤ w.asIdeal] :
    ∃ r : ℤ, Valued.v (r : w.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨r, hr⟩ := original_unramified_exists_integer_uniformizer L w
  refine ⟨r, ?_⟩
  have hv := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := L) w
    (algebraMap ℤ (𝓞 L) r)
  have hi := w.valuation_of_algebraMap (K := L) (algebraMap ℤ (𝓞 L) r)
  simpa using hv.trans (hi.trans hr)

end
end Dubon2026
