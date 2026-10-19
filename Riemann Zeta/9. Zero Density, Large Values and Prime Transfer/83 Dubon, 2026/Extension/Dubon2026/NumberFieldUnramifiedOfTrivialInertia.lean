import Dubon2026.NumberFieldInertiaRamification
import Dubon2026.NumberFieldRamificationUnramified
import Dubon2026.Reuse.Chebotarev.Frobenius

/-! Trivial inertia at one genuine prime in an original Galois number
field implies unramifiedness at every prime above the same base prime.
Native inertia cardinality, Galois equality of ramification indices and
the localized unramifiedness criterion supply the complete implication
needed by Dubon Theorem 2.6's original-support quotient comparison. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Trivial original inertia at one prime implies the full original
Chebotarev unramifiedness condition at its base prime. -/
theorem numberField_unramifiedIn_of_inertia_eq_bot
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (hI : w.asIdeal.inertia Gal(L/K) = ⊥) :
    Chebotarev.UnramifiedIn K L v.asIdeal := by
  have hram : v.asIdeal.ramificationIdx w.asIdeal = 1 := by
    rw [← numberField_card_inertia_eq_ramificationIdx v w, hI]
    simp only [Nat.card_eq_fintype_card, Fintype.card_unique]
  refine ⟨v.ne_bot, ?_⟩
  intro P hP hPv
  letI := hP
  letI := hPv
  let z : HeightOneSpectrum (𝓞 L) :=
    ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  apply (numberField_isUnramifiedAt_iff_ramificationIdx_one v z).mpr
  exact (Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal P w.asIdeal Gal(L/K)).trans hram

end
end Dubon2026
