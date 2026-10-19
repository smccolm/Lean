import Dubon2026.RationalArithmeticFiniteInertiaTrivial
import Dubon2026.ContinuousUnramifiedDeformationClasses
import Dubon2026.ContinuousUnramifiedTraceDeformation
import Dubon2026.ArithmeticSymmetricDetectingFamily
import Dubon2026.RationalPrimeUnramifiedTraceClasses

/-! The very same good regular primes selected for DUB-17 have genuinely
unramified residual representations. Thus their local first-order deformation
criterion requires no supplied inertia-triviality hypothesis. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField
attribute [local instance] rationalArithmeticOriginalFiniteGalois

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q level : ℕ) [Fact q.Prime]
  (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
  (p : Nat.Primes)

/-- A selected original regular auxiliary prime has trivial actual local
inertia in the original residual representation, using its retained finite
unramified factor. -/
theorem rationalArithmetic_regular_auxiliary_inertia
    (hp : RationalArithmeticRegularAuxiliaryPrime a q level R p) :
    rationalPrimeNormInertia p.val p.property ≤
      (R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom).ker := by
  obtain ⟨_, _, F, ψ, hψ, hF⟩ := hp
  intro δ hδ
  exact rationalArithmetic_finite_representation_inertia_eq_one
    a p.val p.property R F ψ hψ hF.1 δ hδ

/-- At each selected prime the original local deformation subspace
characterizes actual continuous fixed-determinant lifts trivial on the
whole actual inertia group. Residual triviality is derived from selection. -/
theorem rationalArithmetic_regular_auxiliary_firstOrder_iff
    (hR : Continuous R) (hp : RationalArithmeticRegularAuxiliaryPrime a q level R p)
    (τ : MatrixFirstOrderLift
      (R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom))
    (hτ : Continuous τ.val) :
    let σ := R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
    let hσ := hR.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous
    continuousMatrixFirstOrderClass σ hσ τ hτ ∈
      continuousUnramifiedFixedDeterminantClasses σ hσ (rationalPrimeNormInertia p.val p.property) ↔
        (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (σ g).val)) ∧
          rationalPrimeNormInertia p.val p.property ≤ τ.val.ker := by
  exact continuousUnramifiedFixedDeterminantClasses_firstOrder_iff _ _ _
    (rationalArithmetic_regular_auxiliary_inertia a q level R p hp) τ hτ

/-- At the same selected prime, actual continuous fixed-determinant
unramified lifts modulo strict conjugacy are precisely the original
trace-zero inertia classes whose dimension was proved. The only dimension
condition is invertibility of the actual residual rank. -/
def rationalRegularPrimeUnramifiedDeformationClassesEquiv
    (hn : (Fintype.card ι : ZMod q) ≠ 0)
    (hR : Continuous R) (hp : RationalArithmeticRegularAuxiliaryPrime a q level R p) :
    let σ := R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
    let hσ := hR.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous
    Quotient (Setoid.ker (continuousUnramifiedFirstOrderClass σ hσ
      (rationalPrimeNormInertia p.val p.property)
      (rationalArithmetic_regular_auxiliary_inertia a q level R p hp))) ≃
        rationalPrimeUnramifiedTraceClasses p.val p.property q σ hσ := by
  dsimp only
  exact (continuousUnramifiedFirstOrderClassesEquiv _ _ _
    (rationalArithmetic_regular_auxiliary_inertia a q level R p hp)).trans
      (continuousUnramifiedTraceFixedDeterminantEquiv hn _ _ _).symm.toEquiv

end
end Dubon2026
