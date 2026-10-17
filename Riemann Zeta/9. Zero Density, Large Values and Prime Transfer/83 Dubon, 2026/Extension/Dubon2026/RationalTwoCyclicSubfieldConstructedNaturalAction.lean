import Dubon2026.RationalTwoCyclicSubfieldNaturalAction

/-! # Constructed inverse-unit reciprocity on the two-primary cyclic subfield

The original auxiliary-field theorem supplies compatible local structures,
and the pinned modular inverse theorem supplies the exponent. No local
structure, inverse exponent, norm, Frobenius or reciprocity certificate is
an input to this natural-unit application. This is the local source entry
needed before DUB-17's rational principal-product and invariant-sum assembly.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable
    (n a : ℕ) (hn : 1 ≤ n)
    (u : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hu : u.val = a) (ha : ¬2 ∣ a)
    (L₀ : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL₀ : L₀.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha).toIntermediateField)
    [IsCyclic Gal(L₀/rationalPrimeLocalField 2 Nat.prime_two)]

include hn

/-- Compatible auxiliary local structures are derived before applying the
proved natural-unit action. The inverse exponent is a narrower arithmetic input. -/
private theorem twoPrimaryConstructedNaturalAction_of_inverse
    (b : ℕ) (hcoprimeA : a.Coprime (2 ^ (n + 1)))
    (hb : b.Coprime (2 ^ (n + 1))) (hab : a * b ≡ 1 [MOD 2 ^ (n + 1)]) :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
    let i₀ : L₀ →ₐ[K] F := IntermediateField.inclusion hL₀
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha
    ∃ σ : Gal(F/K), σ ζ = ζ ^ b ∧
        (localFieldFiniteCyclicReciprocity K Ω L₀
          (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul =
          embeddedNormalGaloisRestriction (F := K) i₀ σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let E := rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha
  let M := rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha
  obtain ⟨fdE, valE, topE, localE, extKE, valM, topM, localM, extKM, extEM, _⟩ :=
    rationalPrimeChangedCyclotomicClosure_exists_local_structure 2 Nat.prime_two n a u hu ha
  letI : FiniteDimensional K E := fdE
  letI : ValuativeRel E := valE
  letI : TopologicalSpace E := topE
  letI : IsNonarchimedeanLocalField E := localE
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) := extKE
  letI : ValuativeRel M := valM
  letI : TopologicalSpace M := topM
  letI : IsNonarchimedeanLocalField M := localM
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M) := extKM
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M) := extEM
  exact rationalTwoOriginalCyclotomicClosure_cyclicSubfield_exists_natural_action
      n a b hn u hu ha hcoprimeA hb hab L₀ hL₀


/-- The actual cyclic subfield receives the natural-unit reciprocity action
from a constructed cyclotomic automorphism with the correct inverse exponent.
The auxiliary local structures and modular inverse are both derived. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_constructed_natural_action :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
    let i₀ : L₀ →ₐ[K] F := IntermediateField.inclusion hL₀
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha
    ∃ b : ℕ, b.Coprime (2 ^ (n + 1)) ∧ a * b ≡ 1 [MOD 2 ^ (n + 1)] ∧
      ∃ σ : Gal(F/K), σ ζ = ζ ^ b ∧
        (localFieldFiniteCyclicReciprocity K Ω L₀
          (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul =
          embeddedNormalGaloisRestriction (F := K) i₀ σ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hab⟩ := primePowerNaturalUnit_exists_inverse 2 n a ha
  have hcoprimeA : a.Coprime (2 ^ (n + 1)) := Nat.prime_two.coprime_pow_of_not_dvd ha
  exact ⟨b, hb, hab, twoPrimaryConstructedNaturalAction_of_inverse
    n a hn u hu ha L₀ hL₀ b hcoprimeA hb hab⟩

end
end Dubon2026
