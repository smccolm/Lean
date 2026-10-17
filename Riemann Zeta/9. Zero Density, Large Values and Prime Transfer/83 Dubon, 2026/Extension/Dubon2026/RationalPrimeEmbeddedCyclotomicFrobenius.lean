import Dubon2026.RationalPrimeChangedCyclotomicClosureReciprocityAction
import Dubon2026.EmbeddedNormalGaloisRestriction

/-! # The actual embedded cyclotomic Frobenius root value

The existing inverse-unit root calculation is read through the literal
embedded restriction used by cyclic-subfield reciprocity. This supplies
the root-value comparison for DUB-17's conductor-two principal product.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction wittCyclotomicRootDVR
  rationalPrimeChangedIntegralRootDomain rationalPrimeChangedIntegralRootDVR

variable
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (hcoprimeA : a.Coprime (p ^ (n + 1)))
    (hcoprimeB : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)])
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha))]
    [ValuativeRel (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha]
      𝒪[rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha]]

include hcoprimeA hcoprimeB hab

/-- The literal embedded arithmetic Frobenius has the native inverse-unit
power on the original cyclotomic root, including at the prime two. -/
theorem rationalPrimeChangedCyclotomicClosure_embeddedFrobenius_root :
    let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
    let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
    let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
    embeddedNormalGaloisRestriction (F := E) j (localFieldArithmeticFrobenius E M)
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
      (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b := by
  exact rationalPrimeChangedCyclotomicClosure_baseChangeFrobenius_root
    p hp n a b u hu ha
    (by simpa only [rationalPrimePlace_natGenerator] using hcoprimeA)
    (by simpa only [rationalPrimePlace_natGenerator] using hcoprimeB)
    (by simpa only [rationalPrimePlace_natGenerator] using hab)

end
end Dubon2026
