import Dubon2026.ArithmeticExceptionalTraceLocalConditions
import Dubon2026.ArithmeticExceptionalTraceSelmerQuotient

/-! Prescribed original local classes modulo actual Selmer conditions.
The proved arithmetic quotient exactness constructs a single global class.
This is the local solvability input to DUB-17's deformation patching chain. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)
  (L : Submodule (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ))
  (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The kernel of the original quotient localization is precisely the
original primal Selmer condition at all exceptional primes. -/
theorem rationalArithmeticTracePrimeQuotientLocalization_ker
    (C : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val)) :
    LinearMap.ker (rationalArithmeticTraceQuotientLocalization a q ha σ hσ
      (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ C)) =
      rationalArithmeticTraceSelmer a q ha σ hσ C := by
  rw [rationalArithmeticTraceQuotientLocalization, LinearMap.ker_comp, Submodule.ker_mkQ]
  rfl

include hq2 hn

/-- The actual dual Selmer obstruction is the complete obstruction to one original
global class having the prescribed local values modulo the specified condition. -/
theorem rationalArithmeticTrace_exists_global_mod_condition_iff
    (y : RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :
    (∃ x : ContinuousTraceZeroAdjointH1 σ hσ,
      y - rationalArithmeticTraceH1Localization a q ha σ hσ x ∈ L) ↔
    rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ L y = 0 := by
  have he := rationalArithmeticTraceQuotientLocalization_range_eq_ker
    a q hqa ha σ hσ L hq2 hn
  constructor
  · rintro ⟨x, hx⟩
    have hxq : L.mkQ y = L.mkQ (rationalArithmeticTraceH1Localization a q ha σ hσ x) :=
      (Submodule.Quotient.eq L).mpr hx
    have hr : L.mkQ y ∈ LinearMap.range
        (rationalArithmeticTraceQuotientLocalization a q ha σ hσ L) := ⟨x, hxq.symm⟩
    rw [he] at hr
    exact hr
  · intro hy
    have hr : L.mkQ y ∈ LinearMap.ker
        (rationalArithmeticTraceSelmerQuotientObstruction a q hqa ha σ hσ L) := hy
    rw [← he] at hr
    obtain ⟨x, hx⟩ := hr
    exact ⟨x, (Submodule.Quotient.eq L).mp hx.symm⟩

omit L in
/-- One original global class simultaneously realizes every original prime-local
prescription modulo its specified subspace exactly when the genuine dual Selmer
obstruction vanishes. No global lift or local-to-global exactness is assumed. -/
theorem rationalArithmeticTrace_exists_global_mod_prime_conditions_iff
    (C : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val))
    (y : RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :
    (∃ x : ContinuousTraceZeroAdjointH1 σ hσ,
      ∀ p, y p - rationalArithmeticTraceH1Localization a q ha σ hσ x p ∈ C p) ↔
    rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ
      (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ C) y = 0 := by
  have he := rationalArithmeticTrace_exists_global_mod_condition_iff a q hqa ha σ hσ
    (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ C) hq2 hn y
  simpa only [rationalArithmeticTraceLocalConditionProduct_mem_iff, Pi.sub_apply] using he

end
end Dubon2026
