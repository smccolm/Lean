import Dubon2026.ArithmeticExceptionalTraceSelmerExactness

/-! The actual localization sequence modulo specified local conditions.
The original obstruction factors through the genuine local quotient,
and its kernel is exactly the original global image. This consumes the
proved arithmetic dual Selmer identity for DUB-17's patching input. -/
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

/-- The original dual Selmer obstruction annihilates the specified local condition. -/
theorem rationalArithmeticTraceSelmerObstruction_condition :
    L ≤ LinearMap.ker (rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ L) := by
  intro y hy
  apply LinearMap.ext
  intro d
  exact (rationalArithmeticTraceDualSelmer_mem_iff a q hqa ha σ hσ L d.val).mp d.property y hy

/-- Literal original global localization modulo the specified local condition. -/
def rationalArithmeticTraceQuotientLocalization :
    ContinuousTraceZeroAdjointH1 σ hσ →ₗ[ZMod q]
      (RationalArithmeticExceptionalTraceH1 a q ha σ hσ ⧸ L) :=
  L.mkQ.comp (rationalArithmeticTraceH1Localization a q ha σ hσ)

/-- The original dual Selmer obstruction on the genuine local quotient. -/
def rationalArithmeticTraceSelmerQuotientObstruction :
    (RationalArithmeticExceptionalTraceH1 a q ha σ hσ ⧸ L) →ₗ[ZMod q]
      Module.Dual (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ L) :=
  L.liftQ (rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ L)
    (rationalArithmeticTraceSelmerObstruction_condition a q hqa ha σ hσ L)

/-- The quotient obstruction retains the original pairing on each original local family. -/
theorem rationalArithmeticTraceSelmerQuotientObstruction_mk
    (y : RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :
    rationalArithmeticTraceSelmerQuotientObstruction a q hqa ha σ hσ L (L.mkQ y) =
      rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ L y := rfl

variable (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0)
include hq2 hn

/-- The original global localization image modulo the local conditions
is exactly the kernel of the actual dual Selmer obstruction. -/
theorem rationalArithmeticTraceQuotientLocalization_range_eq_ker :
    LinearMap.range (rationalArithmeticTraceQuotientLocalization a q ha σ hσ L) =
      LinearMap.ker (rationalArithmeticTraceSelmerQuotientObstruction a q hqa ha σ hσ L) := by
  rw [rationalArithmeticTraceSelmerQuotientObstruction, Submodule.ker_liftQ,
    rationalArithmeticTraceSelmerObstruction_ker a q hqa ha σ hσ L hq2 hn,
    Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq,
    rationalArithmeticTraceQuotientLocalization, LinearMap.range_comp]

end
end Dubon2026
