import Dubon2026.RationalTwoArithmeticSubfieldRestriction
import Dubon2026.RationalTwoCyclicSubfieldPrincipalCharacter

/-! # The conductor-two character at the original arithmetic completion

The actual global cyclic subfield and its retained cyclotomic containing
field supply the local containment and cyclicity. The reference unit is one.
The local principal character therefore applies directly to the original
arithmetic reciprocity map, without a supplied local field or comparison
certificate. This advances DUB-17's global principal-product comparison.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    [IsCyclic Gal(E/ℚ)]
    (n : ℕ) (hn : 1 ≤ n) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]
    (q : ℚˣ)

include hn

/-- The actual arithmetic completion consumes the local principal-character
theorem after deriving its literal containment and cyclicity. -/
private theorem twoPrimaryArithmetic_local_principal_character :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let h1 : (1 : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ).val = (1 : ℕ) :=
      by simp only [Units.val_one, Nat.cast_one]
    let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1 h1
      Nat.prime_two.not_dvd_one
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let M := rationalArithmeticFiniteLocalStage a E 2 Nat.prime_two
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    letI : IsCyclic Gal(M/K) := arithmeticCyclotomicLocalCyclic a E 2 Nat.prime_two
    let hM := rationalTwoArithmeticFiniteLocalStage_le_cyclotomicClosure
      a E F hEF n 1 1 h1 Nat.prime_two.not_dvd_one
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        ∃ σ : Gal(C/K),
          (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive
            2 Nat.prime_two n 1 1 h1 Nat.prime_two.not_dvd_one).autToPow K σ *
            arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS r = 1 ∧
          (localFieldFiniteCyclicReciprocity K Ω M
            (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two q))).toMul =
            embeddedNormalGaloisRestriction (F := K) (IntermediateField.inclusion hM) σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  let M := rationalArithmeticFiniteLocalStage a E 2 Nat.prime_two
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : IsCyclic Gal(M/K) := arithmeticCyclotomicLocalCyclic a E 2 Nat.prime_two
  have h1 : (1 : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ).val = (1 : ℕ) :=
    by simp only [Units.val_one, Nat.cast_one]
  have hM := rationalTwoArithmeticFiniteLocalStage_le_cyclotomicClosure
    a E F hEF n 1 1 h1 Nat.prime_two.not_dvd_one
  exact rationalTwoOriginalCyclotomicClosure_cyclicSubfield_principal_character
    n 1 hn 1 h1 Nat.prime_two.not_dvd_one M hM q

omit hn in
/-- The proved local value gives the original arithmetic value by its
literal restriction map. The public source theorem supplies the local equality. -/
private theorem twoPrimaryArithmetic_reciprocity_of_local
    (σ : Gal(rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
      (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one /
      rationalPrimeLocalField 2 Nat.prime_two))
    (hrec :
      let K := rationalPrimeLocalField 2 Nat.prime_two
      let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
      let M := rationalArithmeticFiniteLocalStage a E 2 Nat.prime_two
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
      letI : IsCyclic Gal(M/K) := arithmeticCyclotomicLocalCyclic a E 2 Nat.prime_two
      let hM := rationalTwoArithmeticFiniteLocalStage_le_cyclotomicClosure
        a E F hEF n 1 1 (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
      (localFieldFiniteCyclicReciprocity K Ω M
        (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two q))).toMul =
        embeddedNormalGaloisRestriction (F := K) (IntermediateField.inclusion hM) σ) :
    rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
      rationalTwoArithmeticSubfieldRestriction a E F hEF n σ := by
  exact congrArg (rationalArithmeticFiniteLocalRestriction a E 2 Nat.prime_two) hrec

/-- The original arithmetic reciprocity value on the global cyclic
subfield is the exact restriction of a local cyclotomic automorphism whose
character cancels the normalized residual's real and away-prime factors.
All local containment, cyclicity and reference-unit inputs are derived. -/
theorem rationalTwoArithmeticCyclicSubfield_exists_principal_character :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let h1 : (1 : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ).val = (1 : ℕ) :=
      by simp only [Units.val_one, Nat.cast_one]
    let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1 h1
      Nat.prime_two.not_dvd_one
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        ∃ σ : Gal(C/K),
          (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive
            2 Nat.prime_two n 1 1 h1 Nat.prime_two.not_dvd_one).autToPow K σ *
            arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS r = 1 ∧
          rationalArithmeticFiniteLocalReciprocityAut a E 2 Nat.prime_two q =
            rationalTwoArithmeticSubfieldRestriction a E F hEF n σ :=
  Exists.imp (fun _ => Exists.imp (fun _ hs =>
    And.intro hs.1 (And.intro hs.2.1
      (Exists.imp (fun σ hσ => And.intro hσ.1
        (twoPrimaryArithmetic_reciprocity_of_local a E F hEF n q σ hσ.2)) hs.2.2))))
    (twoPrimaryArithmetic_local_principal_character a E F hEF n hn q)

end
end Dubon2026
