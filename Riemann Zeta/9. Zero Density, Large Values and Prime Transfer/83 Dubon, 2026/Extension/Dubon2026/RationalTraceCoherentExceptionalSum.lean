import Dubon2026.RationalTraceCoherentSourceCup
import Dubon2026.ArithmeticExceptionalLocalization

/-! Sum the original normalized local Cartier values in the actual
coherent exceptional-prime pairing. This is the annihilator input needed
to prove DUB-17's constructed canonical rational total vanishes. -/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)

/-- The original H1 classes of a cocycle at each actual exceptional prime. -/
def rationalTraceExceptionalSourceH1
    (d : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property) :
    RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ :=
  fun p => Quotient.mk _ (d p)

/-- Every original exceptional dual H1 family has actual continuous
cocycle representatives, without changing its prime index or quotient. -/
theorem rationalTraceExceptionalSourceH1_surjective :
    Function.Surjective (rationalTraceExceptionalSourceH1 a ha q σ hσ) := by
  intro x
  have h (p : rationalArithmeticExceptionalPrimes a ha) := Quotient.exists_rep (x p)
  choose d hd using h
  exact ⟨d, funext hd⟩

variable (hqa : (q : 𝓞 ℚ) ∣ a)
  (d : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property)
  (c : continuousTraceZeroAdjointCocycles σ)

/-- The sum of the actual coherently scaled local Cartier values is
minus the cyclic image of the original exceptional trace pairing. -/
theorem rationalTraceCoherentSourceScalarCup_sum :
    (∑ p : rationalArithmeticExceptionalPrimes a ha,
      rationalTraceSourceScalarCupInvariant a q σ p.val.val p.val.property hσ
        (rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property (d p)) c) =
      -rationalCyclicInvariant q
        (rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
          (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
          (rationalArithmeticTraceH1Localization a q ha σ hσ (Quotient.mk _ c))) := by
  rw [rationalArithmeticExceptionalTracePairing_apply, map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  exact rationalTraceSourceScalarCupInvariant_coherent a q hqa σ p.val.val p.val.property hσ (d p) c

/-- Orthogonality to every actual global source H1 class kills the
normalized local Cartier sum on every original continuous source cocycle. -/
theorem rationalTraceCoherentSourceScalarCup_sum_eq_zero
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    (∑ p : rationalArithmeticExceptionalPrimes a ha,
      rationalTraceSourceScalarCupInvariant a q σ p.val.val p.val.property hσ
        (rationalTraceCoherentCartierSourceCocycle a q hqa σ p.val.val p.val.property (d p)) c) = 0 := by
  rw [rationalTraceCoherentSourceScalarCup_sum, hann, map_zero, neg_zero]

end
end Dubon2026
