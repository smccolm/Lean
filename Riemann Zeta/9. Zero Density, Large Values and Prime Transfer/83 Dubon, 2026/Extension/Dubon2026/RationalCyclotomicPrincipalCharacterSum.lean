import Dubon2026.RationalCyclotomicPrincipalProduct

/-! # The additive character of the rational cyclotomic principal product

The proved principal product is an equality in the actual cyclotomic Galois
group.  This module applies an arbitrary finite cyclic character to that
equality and converts the selected finite product to an additive sum.  The
finite part is the negative of the real-sign character and is therefore
killed by two.  This is the algebraic half of the pending odd-prime
arithmetic invariant-sum theorem.
-/
namespace Dubon2026
noncomputable section

open Polynomial IsCyclotomicExtension
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators NumberField ValuativeRel

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- The actual real-sign automorphism has order dividing two. -/
theorem rationalCyclotomicRealSignAut_mul_self
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] (q : ℚˣ) :
    rationalCyclotomicRealSignAut n F q *
        rationalCyclotomicRealSignAut n F q = 1 := by
  apply (IsCyclotomicExtension.zeta_spec n ℚ F).autToPow_injective ℚ
  rw [map_mul, rationalCyclotomicRealSignAut_autToPow n F q, map_one]
  by_cases hq : 0 < q.val <;>
    simp [rationalCyclotomicRealSignUnit, hq]

/-- Every finite cyclic character sends the actual real-sign automorphism to
an additive element killed by two. -/
theorem rationalCyclotomicRealSignCharacter_two_nsmul
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] (q : ℚˣ)
    {d : ℕ} [NeZero d] (χ : Gal(F/ℚ) →* Multiplicative (ZMod d)) :
    2 • (χ (rationalCyclotomicRealSignAut n F q)).toAdd = 0 := by
  have h := congrArg (fun g => (χ g).toAdd)
    (rationalCyclotomicRealSignAut_mul_self n F q)
  simpa only [map_mul, map_one, toAdd_mul, toAdd_one, two_nsmul] using h

/-- At the conductor prime, the rational prime itself has trivial reciprocity
on the actual arithmetic cyclotomic stage. -/
theorem rationalArithmeticFiniteLocalReciprocityAut_prime_eq_one
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ)
    [IsCyclotomicExtension {p ^ (m + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) :
    rationalArithmeticFiniteLocalReciprocityAut a F p hp
        (rationalPrimeRationalPrimeUnit p hp) = 1 := by
  let u : 𝒪[rationalPrimeLocalField p hp]ˣ := 1
  have hu : u.val = ((1 : ℕ) : 𝒪[rationalPrimeLocalField p hp]) := by simp [u]
  have hc : ¬p ∣ 1 := by
    intro h
    exact hp.ne_one (Nat.dvd_one.mp h)
  letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply hζ.autToPow_injective ℚ
  rw [rationalArithmeticFiniteLocalRestriction_ramified_autToPow
    a F p hp hp2 m hζ 1 u hu hc (rationalPrimeRationalPrimeUnit p hp)]
  have hprime :=
    rationalPrimeOriginalCyclotomicClosure_reciprocity_prime
      p hp hp2 m 1 u hu hc
  have hprime' : rationalPrimeOriginalCyclotomicReciprocityAut
      p hp hp2 m 1 u hu hc (rationalPrimeRationalPrimeUnit p hp) = 1 := by
    simpa only [rationalPrimeOriginalCyclotomicReciprocityAut,
      rationalPrimeRationalUnit_prime] using hprime
  rw [hprime']
  simp only [map_one]

/-- Removing the normalized conductor-prime power from a rational unit does
not change its reciprocity value on the actual arithmetic cyclotomic stage. -/
theorem rationalArithmeticFiniteLocalReciprocityAut_normalizedResidual
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ)
    [IsCyclotomicExtension {p ^ (m + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) (q : ℚˣ) :
    rationalArithmeticFiniteLocalReciprocityAut a F p hp
        (rationalPrimeNormalizedResidual p hp q) =
      rationalArithmeticFiniteLocalReciprocityAut a F p hp q := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let M := rationalArithmeticFiniteLocalStage a F p hp
  let z := localFieldUnitOrder K
    (Additive.ofMul (rationalPrimeRationalUnit p hp q))
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : IsCyclic Gal(M/K) := arithmeticCyclotomicLocalCyclic a F p hp
  have hprime :=
    rationalArithmeticFiniteLocalReciprocityAut_prime_eq_one
      a F p hp hp2 m hζ
  change rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity K Ω M
        (Additive.ofMul (rationalPrimeRationalUnit p hp
          (rationalPrimeNormalizedResidual p hp q)))).toMul = _
  rw [rationalPrimeRationalUnit_normalizedResidual]
  change rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity K Ω M
        (Additive.ofMul
          (rationalPrimeRationalUnit p hp q /
            rationalPrimePrimeUnit p hp ^ z))).toMul = _
  change rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity K Ω M
        (Additive.ofMul (rationalPrimeRationalUnit p hp q) -
          z • Additive.ofMul (rationalPrimePrimeUnit p hp))).toMul = _
  rw [map_sub, map_zsmul, toMul_sub, toMul_zsmul, _root_.map_div, map_zpow]
  have hprimeLocal : rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity K Ω M
        (Additive.ofMul (rationalPrimePrimeUnit p hp))).toMul = 1 := by
    simpa only [rationalArithmeticFiniteLocalReciprocityAut, K, Ω, M,
      rationalPrimeRationalUnit_prime] using hprime
  rw [hprimeLocal, one_zpow, div_one]
  rfl

/-- A rational prime different from the prime represented by a rational
height-one place has valuation one at that place. -/
theorem rationalHeightOneSpectrum_valuation_prime_eq_one_of_ne
    (v : HeightOneSpectrum ℤ) (p : ℕ) (hp : p.Prime)
    (hvp : Rat.HeightOneSpectrum.natGenerator v ≠ p) :
    v.valuation ℚ (p : ℚ) = 1 := by
  change v.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1
  rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hpv
  have hmap : (p : ℤ) ∈
      v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
    simpa using Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv ℤ) hpv
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ p :=
    (Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mpr hmap
  have heq : Rat.HeightOneSpectrum.natGenerator v = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left
      (Rat.HeightOneSpectrum.prime_natGenerator v).ne_one
  exact hvp heq

/-- Away from the conductor, removing the normalized conductor-prime power
does not change the local reciprocity automorphism. -/
theorem arithmeticCyclotomicAwayAut_normalizedResidual
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)]
    (p : ℕ) (hp : p.Prime) (m : ℕ)
    [IsCyclotomicExtension {p ^ (m + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    (v : HeightOneSpectrum ℤ)
    (hvp : Rat.HeightOneSpectrum.natGenerator v ≠ p) (q : ℚˣ) :
    arithmeticCyclotomicAwayAut a F v
        (rationalPrimeNormalizedResidual p hp q) =
      arithmeticCyclotomicAwayAut a F v q := by
  let l := Rat.HeightOneSpectrum.natGenerator v
  let hl : l.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  let K := rationalPrimeLocalField l hl
  let z := localFieldUnitOrder (rationalPrimeLocalField p hp)
    (Additive.ofMul (rationalPrimeRationalUnit p hp q))
  letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have haway : ¬l ∣ p ^ (m + 1) := by
    intro hdvd
    have hdivp : l ∣ p := hl.dvd_of_dvd_pow hdvd
    have heq : l = p :=
      ((Nat.dvd_prime hp).mp hdivp).resolve_left hl.ne_one
    exact hvp heq
  have hprimeVal : v.valuation ℚ (p : ℚ) = 1 :=
    rationalHeightOneSpectrum_valuation_prime_eq_one_of_ne v p hp hvp
  have hprimeOrder : localFieldUnitOrder K
      (Additive.ofMul (rationalPrimeRationalUnit l hl
        (rationalPrimeRationalPrimeUnit p hp))) = 0 := by
    change localFieldUnitOrder (rationalPrimeLocalField l hl)
      (Additive.ofMul (Units.map
        (algebraMap ℚ (rationalPrimeLocalField l hl)).toMonoidHom
        (rationalPrimeRationalPrimeUnit p hp))) = 0
    rw [rationalPrimeLocalField_rational_order]
    change -WithZero.log ((rationalPrimePlace l hl).valuation ℚ (p : ℚ)) = 0
    rw [show rationalPrimePlace l hl = v by
      exact rationalPrimePlace_of_natGenerator v, hprimeVal]
    simp
  have horder : localFieldUnitOrder K
      (Additive.ofMul (rationalPrimeRationalUnit l hl
        (rationalPrimeNormalizedResidual p hp q))) =
      localFieldUnitOrder K
        (Additive.ofMul (rationalPrimeRationalUnit l hl q)) := by
    have hunit : rationalPrimeRationalUnit l hl
        (rationalPrimeNormalizedResidual p hp q) =
        rationalPrimeRationalUnit l hl q /
          rationalPrimeRationalUnit l hl
            (rationalPrimeRationalPrimeUnit p hp) ^ z := by
      apply Units.ext
      simp [rationalPrimeNormalizedResidual, rationalPrimeRationalUnit,
        rationalPrimeRationalPrimeUnit, z]
    rw [hunit]
    change localFieldUnitOrder K
        (Additive.ofMul (rationalPrimeRationalUnit l hl q) -
          z • Additive.ofMul (rationalPrimeRationalUnit l hl
            (rationalPrimeRationalPrimeUnit p hp))) = _
    rw [map_sub, map_zsmul, hprimeOrder, smul_zero, sub_zero]
  apply hζ.autToPow_injective ℚ
  rw [arithmeticCyclotomicAwayAut_autToPow a F (p ^ (m + 1)) v haway hζ,
    arithmeticCyclotomicAwayAut_autToPow a F (p ^ (m + 1)) v haway hζ,
    horder]

/-- At an away prime where the rational input has valuation one, the actual
local reciprocity automorphism on the cyclotomic stage is trivial. -/
theorem arithmeticCyclotomicAwayAut_eq_one_of_valuation_eq_one
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} ℚ F]
    (v : HeightOneSpectrum ℤ)
    (hvn : ¬Rat.HeightOneSpectrum.natGenerator v ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (q : ℚˣ)
    (hq : v.valuation ℚ q.val = 1) :
    arithmeticCyclotomicAwayAut a F v q = 1 := by
  have horder : localFieldUnitOrder
      (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
        (Rat.HeightOneSpectrum.prime_natGenerator v))
      (Additive.ofMul
        (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v) q)) = 0 := by
    change localFieldUnitOrder
      (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
        (Rat.HeightOneSpectrum.prime_natGenerator v))
      (Additive.ofMul (Units.map
        (algebraMap ℚ (rationalPrimeLocalField
          (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom q)) = 0
    rw [rationalPrimeLocalField_rational_order]
    rw [rationalPrimePlace_of_natGenerator, hq]
    simp
  apply hζ.autToPow_injective ℚ
  rw [arithmeticCyclotomicAwayAut_autToPow a F n v hvn hζ, horder]
  simp

/-- The packaged away-prime automorphism is definitionally the same actual
local reciprocity value used by the finite carry invariant. -/
theorem arithmeticCyclotomicAwayAut_eq_finiteLocalReciprocity
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)] (v : HeightOneSpectrum ℤ) (q : ℚˣ) :
    let p := Rat.HeightOneSpectrum.natGenerator v
    let hp := Rat.HeightOneSpectrum.prime_natGenerator v
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let M := rationalArithmeticFiniteLocalStage a F p hp
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    letI : IsCyclic Gal(M/K) := arithmeticCyclotomicLocalCyclic a F p hp
    arithmeticCyclotomicAwayAut a F v q =
      rationalArithmeticFiniteLocalRestriction a F p hp
        (localFieldFiniteCyclicReciprocity K Ω M
          (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul := by
  dsimp only
  rfl

/-- Applying an arbitrary finite cyclic character to the actual rational
cyclotomic principal product turns its ramified and away-prime factors into
the negative real-sign character.  Consequently that finite character sum
is killed by two. -/
theorem rationalPrimeNormalizedResidual_exists_arithmetic_principal_character_sum
    (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    [IsCyclic Gal(F/ℚ)]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ)
    [IsCyclotomicExtension {p ^ (m + 1)} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) (q : ℚˣ)
    {d : ℕ} [NeZero d] (χ : Gal(F/ℚ) →* Multiplicative (ZMod d)) :
    let N := p ^ (m + 1)
    letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
    let r := rationalPrimeNormalizedResidual p hp q
    ∃ S : Finset (HeightOneSpectrum ℤ),
        (∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ N) ∧
        (∀ v ∉ S, v.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
                  (Rat.HeightOneSpectrum.prime_natGenerator v) r))) = r.val ∧
        let z :=
          (χ (rationalArithmeticFiniteLocalReciprocityAut a F p hp r)).toAdd +
            ∑ v ∈ S, (χ (arithmeticCyclotomicAwayAut a F v r)).toAdd
        z = -(χ (rationalCyclotomicRealSignAut N F r)).toAdd ∧ 2 • z = 0 := by
  dsimp only
  let N := p ^ (m + 1)
  letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
  let r := rationalPrimeNormalizedResidual p hp q
  obtain ⟨S, hS, houtside, hvalue, hproduct⟩ :=
    rationalPrimeNormalizedResidual_exists_arithmetic_principal_product
      a F p hp hp2 m hζ q
  refine ⟨S, hS, houtside, hvalue, ?_⟩
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup N F
  have hcharacter := congrArg (fun g => (χ g).toAdd) hproduct
  have hsum :
      (χ (rationalArithmeticFiniteLocalReciprocityAut a F p hp r)).toAdd +
          (χ (rationalCyclotomicRealSignAut N F r)).toAdd +
          ∑ v ∈ S, (χ (arithmeticCyclotomicAwayAut a F v r)).toAdd = 0 := by
    simpa only [arithmeticCyclotomicSignedAwayProduct,
      arithmeticCyclotomicAwayProduct, map_mul, map_one, map_prod,
      toAdd_mul, toAdd_one, toAdd_prod, add_assoc] using hcharacter
  have hfinite :
      (χ (rationalArithmeticFiniteLocalReciprocityAut a F p hp r)).toAdd +
          ∑ v ∈ S, (χ (arithmeticCyclotomicAwayAut a F v r)).toAdd =
        -(χ (rationalCyclotomicRealSignAut N F r)).toAdd := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc, add_left_comm, add_comm] using hsum
  constructor
  · exact hfinite
  · rw [hfinite, two_nsmul, ← neg_add, ← two_nsmul,
      rationalCyclotomicRealSignCharacter_two_nsmul N F r χ, neg_zero]

end
end Dubon2026
