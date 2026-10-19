import Dubon2026.LocalGeometricTraceCondition
import Dubon2026.ArithmeticExceptionalTraceDuality

/-! The original prime-local finite-flat deformation condition in trace-zero H1.
Reuse the proved closure under genuine model operations. This constructs a
specific local subspace for DUB-17's Selmer comparison from an actual residual
model; it does not assert that a modular form supplies that model. -/
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

/-- The genuine finite-flat local condition pulled back along the original
trace-zero inclusion; linear closure is supplied by the existing geometric theorem. -/
def rationalPrimeGeometricTraceCondition :
    Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p) :=
  localGeometricTraceCondition
    (σ.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
    (hσ.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous) m

/-- Membership is the original geometric condition on the exact included local class. -/
theorem rationalPrimeGeometricTraceCondition_mem_iff
    (x : rationalArithmeticPrimeTraceH1Module a q σ hσ p) :
    x ∈ rationalPrimeGeometricTraceCondition a q σ hσ p m ↔
      continuousTraceZeroH1Inclusion
        (σ.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous) x ∈
      localGeometricFiniteFlatCohomologyCondition
        (rationalPrimeLocalIntegerRing p.val p.property)
        (rationalPrimeLocalField p.val p.property) (rationalPrimeLocalClosure p.val p.property)
        (σ.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous) := Iff.rfl

/-- Every class in the actual local condition has a continuous genuine finite-flat
first-order representative with the original constant residual determinant. -/
theorem rationalPrimeGeometricTraceCondition_exists_lift
    (x : rationalArithmeticPrimeTraceH1Module a q σ hσ p)
    (hx : x ∈ rationalPrimeGeometricTraceCondition a q σ hσ p m) :
    let ρ := σ.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
    let hρ := hσ.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous
    ∃ τ : MatrixFirstOrderLift ρ, ∃ hτ : Continuous τ.val,
      (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ∧
      MatrixAdicFiniteFlatScheme (rationalPrimeLocalIntegerRing p.val p.property)
        (rationalPrimeLocalField p.val p.property) (rationalPrimeLocalClosure p.val p.property) τ.val ∧
      continuousMatrixFirstOrderClass ρ hρ τ hτ = continuousTraceZeroH1Inclusion ρ hρ x := by
  dsimp only
  exact localGeometricTraceCondition_exists_lift _ _ m x hx

end
end Dubon2026
