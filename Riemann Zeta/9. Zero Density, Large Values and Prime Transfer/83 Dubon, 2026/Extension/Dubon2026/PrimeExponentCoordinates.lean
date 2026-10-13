import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Exact prime-exponent coordinates for the actual Kummer restriction kernel

The already proved original restriction kernel has order p^(s-1) and exponent
p. Its ZMod p vector space therefore has dimension s-1. These coordinates
provide exactly the cyclic order-p subgroups needed for the actual selected
primes in DUB-17's norm-index upper-bound chain. No prime-power classification
is required for this prime-degree step.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] AddCommGroup.toAddCommMonoid
variable (G : Type) [CommGroup G] (p : ℕ) [Fact p.Prime]

/-- An actual commutative prime-exponent group of order p^r has exact r
coordinates over the original residue field. -/
def primeExponentCoordinateEquiv (r : ℕ)
    (hPower : ∀ g : G, g ^ p = 1) (hCard : Nat.card G = p ^ r) :
    G ≃* (Fin r → Multiplicative (ZMod p)) := by
  have hp : p.Prime := Fact.out
  letI : Finite G := Nat.finite_of_card_ne_zero (by rw [hCard]; exact (pow_pos hp.pos r).ne')
  letI primeExponentModule : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule (n := p) (G := Additive G) (by
    intro g
    exact congrArg Additive.ofMul (hPower g.toMul))
  letI : Finite (Additive G) := inferInstanceAs (Finite G)
  letI primeExponentFinite : Module.Finite (ZMod p) (Additive G) := Module.Finite.of_finite
  letI primeExponentFree : Module.Free (ZMod p) (Additive G) :=
    Module.Free.of_divisionRing (ZMod p) (Additive G)
  have hDim : Module.finrank (ZMod p) (Additive G) = r := by
    have h : Nat.card (Additive G) = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (Additive G) :=
      @Module.natCard_eq_pow_finrank (ZMod p) (Additive G) inferInstance inferInstance
        primeExponentModule primeExponentFinite
    change Nat.card G = _ at h
    rw [hCard, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.one_lt) h.symm
  let e : Additive G ≃ₗ[ZMod p] (Fin r → ZMod p) :=
    (@Module.finBasisOfFinrankEq (ZMod p) (Additive G)
      (inferInstanceAs (Semiring (ZMod p))) (inferInstanceAs (AddCommMonoid (Additive G)))
      primeExponentModule primeExponentFree (inferInstanceAs (StrongRankCondition (ZMod p)))
      primeExponentFinite r hDim).equivFun
  exact {
    toFun := fun g i => Multiplicative.ofAdd (e.toEquiv (Additive.ofMul g) i)
    invFun := fun f => (e.symm.toEquiv (fun i => (f i).toAdd)).toMul
    left_inv := fun g => congrArg Additive.toMul (e.symm_apply_apply (Additive.ofMul g))
    right_inv := fun f => by
      funext i
      exact congrArg (fun z : Fin r → ZMod p => Multiplicative.ofAdd (z i))
        (e.apply_symm_apply (fun i => (f i).toAdd))
    map_mul' := fun g h => by
      funext i
      exact congrArg (fun z : Fin r → ZMod p => Multiplicative.ofAdd (z i))
        (e.map_add (Additive.ofMul g) (Additive.ofMul h)) }

/-- The prime-exponent coordinates are an actual multiplicative equivalence,
with no coordinate-existence input. -/
theorem primeExponent_exists_coordinates (r : ℕ)
    (hPower : ∀ g : G, g ^ p = 1) (hCard : Nat.card G = p ^ r) :
    Nonempty (G ≃* (Fin r → Multiplicative (ZMod p))) :=
  ⟨primeExponentCoordinateEquiv G p r hPower hCard⟩

end
end Dubon2026
