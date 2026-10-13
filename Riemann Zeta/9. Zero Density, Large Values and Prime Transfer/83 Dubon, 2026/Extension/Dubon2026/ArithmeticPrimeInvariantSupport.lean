import Dubon2026.ArithmeticCyclotomicH2FiniteSupport
import Dubon2026.ArithmeticCoherentLocalInvariant

/-! # Finite support of the coherently normalized original prime invariants

Use the single global root and its exact local images. The primewise map is
the original H2 restriction followed by that coherent local coordinate, with
canonical discrete coefficient topologies. Its support is proved finite from
the actual arithmetic vanishing, preparing the DUB-17 global invariant sum.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The actual local root coefficient module uses its discrete topology. -/
local instance arithmeticPrimeInvariantRootTopology (p : ℕ) (hp : p.Prime) (q : ℕ) :
    TopologicalSpace (galoisRootOfUnityRepresentation
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q) := ⊥

local instance arithmeticPrimeInvariantRootDiscrete (p : ℕ) (hp : p.Prime) (q : ℕ) :
    DiscreteTopology (galoisRootOfUnityRepresentation
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q) := ⟨rfl⟩

/-- The actual local algebraic unit coefficient module uses its discrete topology. -/
local instance arithmeticPrimeInvariantUnitTopology (p : ℕ) (hp : p.Prime) :
    TopologicalSpace (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) := ⊥

local instance arithmeticPrimeInvariantUnitDiscrete (p : ℕ) (hp : p.Prime) :
    DiscreteTopology (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)) := ⟨rfl⟩

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The original prime-local arithmetic invariant in the coherent coordinate
determined by the image of the one original global primitive root. -/
def rationalArithmeticPrimeH2Invariant (p : ℕ) (hp : p.Prime) :
    ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous) →ₗ[ZMod q] ZMod q :=
  (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp).toLinearMap.comp
    (rationalPrimeCyclotomicH2Restriction a q hqa p hp)

/-- The coherently normalized original prime invariant is zero away from the
actual exceptional integer, by the proved original H2 restriction vanishing. -/
theorem rationalArithmeticPrimeH2Invariant_eq_zero (p : ℕ) (hp : p.Prime)
    (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticPrimeH2Invariant a q hqa p hp x = 0 := by
  exact (congrArg (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp)
    (rationalPrimeCyclotomicH2Restriction_eq_zero a q hqa p hp ha hpa x)).trans
      (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp).map_zero

/-- The actual coherent prime-invariant family has proved finite support,
so its sum is a genuine finite sum on original primes. -/
theorem rationalArithmeticPrimeH2Invariant_finite_support (ha : a ≠ 0)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    (Function.support (fun p : Nat.Primes => rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x)).Finite := by
  apply (rationalExceptionalPrimeSet_finite a ha).subset
  intro p hp
  by_contra hpa
  exact hp (rationalArithmeticPrimeH2Invariant_eq_zero a q hqa p.val p.property ha hpa x)

end
end Dubon2026
