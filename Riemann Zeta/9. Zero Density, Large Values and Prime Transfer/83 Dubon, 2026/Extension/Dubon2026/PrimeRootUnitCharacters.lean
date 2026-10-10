import Dubon2026.ContinuousGaloisKummerClasses
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Instances.ZMod

/-! # Original prime-order characters as actual base-unit-valued exponent characters -/

namespace Dubon2026

noncomputable section

variable {K : Type*} [Field K]

/-- The original cyclic group of order p is identified with the genuine pth roots of unity in the original field. -/
def primeRootUnitEquiv (p : ℕ) (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Multiplicative (ZMod p) ≃* rootsOfUnity p K := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply mulEquivOfPrimeCardEq (p := p)
  · simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  · rw [Nat.card_eq_fintype_card, hζ.card_rootsOfUnity]

/-- The genuine original prime-order character target embeds in the original field units. -/
def primeRootUnitEmbedding (p : ℕ) (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Multiplicative (ZMod p) →* Kˣ :=
  (rootsOfUnity p K).subtype.comp (primeRootUnitEquiv p hp hζ).toMonoidHom

/-- The actual original root-of-unity target embedding is injective. -/
theorem primeRootUnitEmbedding_injective (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (primeRootUnitEmbedding p hp hζ) :=
  Subtype.val_injective.comp (primeRootUnitEquiv p hp hζ).injective

/-- Every actual image in the original unit group has pth power one. -/
theorem primeRootUnitEmbedding_pow (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (x : Multiplicative (ZMod p)) :
    primeRootUnitEmbedding p hp hζ x ^ p = 1 :=
  (primeRootUnitEquiv p hp hζ x).property

variable {Ω : Type*} [Field Ω] [Algebra K Ω]
  [TopologicalSpace Kˣ]

/-- The original continuous prime-order Galois character is sent to its genuine continuous base-unit-valued exponent character. -/
def primeRootContinuousCharacter (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) :
    ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) p := by
  let κ : Multiplicative (ZMod p) →ₜ* Kˣ := {
    toMonoidHom := primeRootUnitEmbedding p hp hζ
    continuous_toFun := continuous_of_discreteTopology }
  exact ⟨κ.comp χ, fun g => primeRootUnitEmbedding_pow p hp hζ (χ g)⟩

/-- The actual transformation retains the entire original continuous prime-order character. -/
theorem primeRootContinuousCharacter_injective (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (primeRootContinuousCharacter (Ω := Ω) p hp hζ) := by
  intro χ ψ h
  ext g
  apply primeRootUnitEmbedding_injective p hp hζ
  exact DFunLike.congr_fun (congrArg Subtype.val h) g

/-- Actual finite original unit-valued exponent characters imply finite original continuous prime-order characters through the genuine root embedding. -/
theorem prime_characters_finite_of_unit_exponent_characters (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    [Finite (ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) p)] :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) :=
  Finite.of_injective _ (primeRootContinuousCharacter_injective p hp hζ)

end
end Dubon2026
