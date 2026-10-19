import Dubon2026.RationalPrimeGeometricTraceCondition
import Dubon2026.LocalGeometricTraceFirstOrder
import Dubon2026.ArithmeticExceptionalLocalization
import Dubon2026.ContinuousAdjointRestriction

/-! The genuine global first-order meaning of the original prime-local condition.
This connects DUB-17's specified local Selmer subspace to actual continuous
representations and finite-flat scheme models, retaining its residual model input. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ) (p : Nat.Primes)
  (m : FiniteFreeHopfPointModel.{0,0,0,0,0}
    (rationalPrimeLocalIntegerRing p.val p.property)
    (rationalPrimeLocalField p.val p.property) (rationalPrimeLocalClosure p.val p.property)
    (Multiplicative (ι → ZMod q))
    (matrixUnderlyingGroupAction
      (σ.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)))

/-- For any original global first-order representative of the trace-zero class,
the actual local condition is exactly a genuine finite-flat model of its same restriction. -/
theorem rationalPrimeGeometricTraceCondition_global_firstOrder_iff
    (x : ContinuousTraceZeroAdjointH1 σ hσ)
    (τ : MatrixFirstOrderLift σ) (hτ : Continuous τ.val)
    (hclass : continuousMatrixFirstOrderClass σ hσ τ hτ = continuousTraceZeroH1Inclusion σ hσ x) :
    continuousTraceZeroH1Restriction σ hσ
      (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
      (rationalPrimeArithmeticRestriction a p.val p.property).continuous x ∈
        rationalPrimeGeometricTraceCondition a q σ hσ p m ↔
      MatrixAdicFiniteFlatScheme (rationalPrimeLocalIntegerRing p.val p.property)
        (rationalPrimeLocalField p.val p.property) (rationalPrimeLocalClosure p.val p.property)
        (τ.val.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom) := by
  exact localGeometricTraceCondition_global_firstOrder_iff σ hσ
    (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
    (rationalPrimeArithmeticRestriction a p.val p.property).continuous m x τ hτ hclass

/-- A global trace-zero class lies in the genuine prime-local deformation condition
exactly when it has a continuous global first-order representative with constant
residual determinant and an actual finite-flat model at the same original prime. -/
theorem rationalPrimeGeometricTraceCondition_global_exists_lift_iff
    (x : ContinuousTraceZeroAdjointH1 σ hσ) :
    continuousTraceZeroH1Restriction σ hσ
      (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
      (rationalPrimeArithmeticRestriction a p.val p.property).continuous x ∈
        rationalPrimeGeometricTraceCondition a q σ hσ p m ↔
    ∃ τ : MatrixFirstOrderLift σ, ∃ hτ : Continuous τ.val,
      (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (σ g).val)) ∧
      MatrixAdicFiniteFlatScheme (rationalPrimeLocalIntegerRing p.val p.property)
        (rationalPrimeLocalField p.val p.property) (rationalPrimeLocalClosure p.val p.property)
        (τ.val.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom) ∧
      continuousMatrixFirstOrderClass σ hσ τ hτ = continuousTraceZeroH1Inclusion σ hσ x := by
  exact localGeometricTraceCondition_global_exists_lift_iff σ hσ
    (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
    (rationalPrimeArithmeticRestriction a p.val p.property).continuous m x

end
end Dubon2026
