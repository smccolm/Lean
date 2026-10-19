import Dubon2026.AlgebraicLocalUnramifiedLifting
import Dubon2026.RationalRegularPrimeInertia

/-! The actual original prime-local unramified deformation condition lifts
across finite local coefficient surjections. Residue finiteness is derived
from the original local field; at the selected auxiliary primes, residual
inertia triviality is derived from the retained finite unramified factor.
This is the finite-coefficient lifting input for DUB-17's local ring geometry. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- Every actual unramified representation on the original rational-prime
local field lifts across a finite local coefficient surjection with its
compatible prescribed unramified determinant. -/
theorem rationalPrime_unramified_fixedDeterminant_lift
    (p : ℕ) (hp : p.Prime)
    {ι A B : Type} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    [TopologicalSpace B] [DiscreteTopology B]
    (i₀ : ι) (f : A →+* B) (hf : Function.Surjective f) [IsLocalHom f]
    (σ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →ₜ*
      GeneralLinearGroup ι B)
    (hσ : rationalPrimeNormInertia p hp ≤ σ.toMonoidHom.ker)
    (δ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →ₜ* Aˣ)
    (hδ : rationalPrimeNormInertia p hp ≤ δ.toMonoidHom.ker)
    (hcompat : ∀ g, Units.map f.toMonoidHom (δ g) = GeneralLinearGroup.det (σ g)) :
    ∃ τ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →ₜ*
        GeneralLinearGroup ι A,
      rationalPrimeNormInertia p hp ≤ τ.toMonoidHom.ker ∧
      (GeneralLinearGroup.map f).comp τ.toMonoidHom = σ.toMonoidHom ∧
      GeneralLinearGroup.det.comp τ.toMonoidHom = δ.toMonoidHom := by
  letI : Finite (IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalField p hp))) :=
    normLocal_residue_finite (rationalPrimeLocalField p hp)
  exact algebraicLocal_unramified_fixedDeterminant_lift
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) i₀ f hf σ hσ δ hδ hcompat

/-- At each same selected auxiliary prime, the actual residual
representation admits the genuine unramified fixed-determinant lift.
Neither residual inertia triviality, residue finiteness, a chosen
Frobenius nor a matrix lift is an additional hypothesis. -/
theorem rationalArithmetic_regular_auxiliary_fixedDeterminant_lift
    {ι A : Type} [Fintype ι] [DecidableEq ι] [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (a : 𝓞 ℚ) (q level : ℕ) [Fact q.Prime]
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
    (hR : Continuous R) (p : Nat.Primes)
    (hp : RationalArithmeticRegularAuxiliaryPrime a q level R p)
    (i₀ : ι) (f : A →+* ZMod q) (hf : Function.Surjective f) [IsLocalHom f]
    (δ : Gal(rationalPrimeLocalClosure p.val p.property /
      rationalPrimeLocalField p.val p.property) →ₜ* Aˣ)
    (hδ : rationalPrimeNormInertia p.val p.property ≤ δ.toMonoidHom.ker)
    (hcompat : ∀ g, Units.map f.toMonoidHom (δ g) =
      GeneralLinearGroup.det (R (rationalPrimeArithmeticRestriction a p.val p.property g))) :
    ∃ τ : Gal(rationalPrimeLocalClosure p.val p.property /
        rationalPrimeLocalField p.val p.property) →ₜ* GeneralLinearGroup ι A,
      rationalPrimeNormInertia p.val p.property ≤ τ.toMonoidHom.ker ∧
      (GeneralLinearGroup.map f).comp τ.toMonoidHom =
        R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom ∧
      GeneralLinearGroup.det.comp τ.toMonoidHom = δ.toMonoidHom := by
  let σ : Gal(rationalPrimeLocalClosure p.val p.property /
      rationalPrimeLocalField p.val p.property) →ₜ* GeneralLinearGroup ι (ZMod q) :=
    ⟨R.comp (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom,
      hR.comp (rationalPrimeArithmeticRestriction a p.val p.property).continuous⟩
  exact rationalPrime_unramified_fixedDeterminant_lift p.val p.property i₀ f hf σ
    (rationalArithmetic_regular_auxiliary_inertia a q level R p hp) δ hδ hcompat

end
end Dubon2026
