import Dubon2026.RationalPrimeGeometricTraceFirstOrder
import Dubon2026.ArithmeticExceptionalTraceSelmerPrescription
import Dubon2026.ArithmeticExceptionalTraceSelmerDimension

/-! A genuine geometric deformation condition in the original Selmer sequence.
The actual residual model constructs the local subspace; the original global
first-order representatives and all positive finite-flat adic levels are retained.
This is an instantiated input for DUB-17, not arithmetic model existence or patching. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ) (p : rationalArithmeticExceptionalPrimes a ha)
  (m : FiniteFreeHopfPointModel.{0,0,0,0,0}
    (rationalPrimeLocalIntegerRing p.val.val p.val.property)
    (rationalPrimeLocalField p.val.val p.val.property)
    (rationalPrimeLocalClosure p.val.val p.val.property)
    (Multiplicative (ι → ZMod q))
    (matrixUnderlyingGroupAction
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)))

/-- The actual exceptional product condition imposing geometric finite-flatness at
the specified original prime; other coordinates retain their full local spaces. -/
def rationalArithmeticGeometricTraceProductCondition :
    Submodule (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :=
  (rationalPrimeGeometricTraceCondition a q σ hσ p.val m).comap (LinearMap.proj p)

/-- The actual global trace-zero Selmer classes for this original geometric condition. -/
def rationalArithmeticGeometricTraceSelmer :
    Submodule (ZMod q) (ContinuousTraceZeroAdjointH1 σ hσ) :=
  (rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m).comap
    (rationalArithmeticTraceH1Localization a q ha σ hσ)

/-- This actual Selmer subspace consists exactly of the original global first-order
classes with constant determinant and a genuine finite-flat model at the specified prime. -/
theorem rationalArithmeticGeometricTraceSelmer_exists_lift_iff
    (x : ContinuousTraceZeroAdjointH1 σ hσ) :
    x ∈ rationalArithmeticGeometricTraceSelmer a q ha σ hσ p m ↔
    ∃ τ : MatrixFirstOrderLift σ, ∃ hτ : Continuous τ.val,
      (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (σ g).val)) ∧
      MatrixAdicFiniteFlatScheme (rationalPrimeLocalIntegerRing p.val.val p.val.property)
        (rationalPrimeLocalField p.val.val p.val.property)
        (rationalPrimeLocalClosure p.val.val p.val.property)
        (τ.val.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom) ∧
      continuousMatrixFirstOrderClass σ hσ τ hτ = continuousTraceZeroH1Inclusion σ hσ x := by
  exact rationalPrimeGeometricTraceCondition_global_exists_lift_iff a q σ hσ p.val m x

variable (hqa : (q : 𝓞 ℚ) ∣ a) (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0)
include hq2 hn

/-- The proved original arithmetic duality solves the actual prime-local prescription
modulo the constructed geometric finite-flat condition. The model is a residual
geometric input; global lift existence is concluded from the actual Selmer obstruction. -/
theorem rationalArithmeticTrace_exists_global_mod_geometric_iff
    (y : RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :
    (∃ x : ContinuousTraceZeroAdjointH1 σ hσ,
      y p - rationalArithmeticTraceH1Localization a q ha σ hσ x p ∈
        rationalPrimeGeometricTraceCondition a q σ hσ p.val m) ↔
    rationalArithmeticTraceSelmerObstruction a q hqa ha σ hσ
      (rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m) y = 0 := by
  exact rationalArithmeticTrace_exists_global_mod_condition_iff a q hqa ha σ hσ
    (rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m) hq2 hn y

end
end Dubon2026
