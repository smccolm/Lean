import Dubon2026.RationalCyclotomicPrincipalCharacterSum
import Dubon2026.ArithmeticFiniteInvariantSumComparison
import Dubon2026.ArithmeticFiniteCarryInvariant
import Dubon2026.ArithmeticKummerCyclicCarry

/-! # The finite carry on the rational cyclotomic principal support

This module identifies every original finite-place invariant of the global
Kummer class with the character of the corresponding actual finite-stage
local reciprocity automorphism.  It also packages the elementary odd/two
torsion cancellation used after the principal-product support is assembled.
-/
namespace Dubon2026
noncomputable section

open Polynomial IsCyclotomicExtension
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators NumberField ValuativeRel

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageGalois arithmeticKummerStageTopology
  arithmeticKummerStageDiscrete
  arithmeticGlobalUnitContinuousSMul arithmeticFiniteLocalStageGalois
  arithmeticFiniteLocalStageRationalAlgebra arithmeticPrimeInvariantUnitTopology
  arithmeticPrimeInvariantUnitDiscrete

/-- In an additive commutative group, simultaneous odd torsion and
two-torsion force an element to vanish. -/
theorem eq_zero_of_two_nsmul_eq_zero_of_odd_nsmul_eq_zero
    {A : Type*} [AddCommGroup A] (q : ℕ) (hq : Odd q) (x : A)
    (h2 : 2 • x = 0) (hqx : q • x = 0) : x = 0 := by
  obtain ⟨k, rfl⟩ := hq
  simpa only [add_nsmul, mul_nsmul, h2, nsmul_zero, zero_add, one_nsmul] using hqx

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

section

variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- A finite character-carry presentation of the global Kummer image gives
the exact finite-carry class underlying every original local invariant. -/
theorem rationalArithmeticKummerUnitPrimeInvariant_eq_finiteCarryInvariant
    [IsCyclic Gal(F/ℚ)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F)]
    (p : ℕ) (hp : p.Prime)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : GaloisUnitContinuousH2 (K := ℚ) (Ω := F))
    (hy : galoisUnitFiniteStageH2Inflation F y =
      rationalArithmeticKummerH2Inclusion a q
        (rationalArithmeticCyclotomicH2RootEquiv a q hqa x))
    {n : ℕ} [NeZero n] (χ : Gal(F/ℚ) →* Multiplicative (ZMod n))
    (u : ℚˣ)
    (hcarry : Submodule.Quotient.mk
      (galoisUnitCharacterCarryCocycle χ u) = y) :
    rationalArithmeticKummerUnitPrimeInvariant a q hqa p hp x =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalArithmeticUnitH2Restriction a p hp
          (galoisUnitFiniteStageH2Inflation F
            (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)))) := by
  unfold rationalArithmeticKummerUnitPrimeInvariant
  rw [← hy, ← hcarry]

end

/-- For an odd coefficient prime, the actual finite-prime invariant sum of
the original arithmetic Kummer class vanishes.  The proof compares the
existing coherent support with the support of the normalized rational
principal product.  Its image in the rational circle is killed by two by
the real-sign character and by `q` because it comes from `ZMod q`; oddness
and injectivity of the cyclic invariant force the original scalar to be
zero. -/
theorem rationalArithmeticFiniteH2InvariantSum_eq_zero
    (ha : a ≠ 0) (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticFiniteH2InvariantSum a q hqa ha x = 0 := by
  classical
  obtain ⟨k, F, hk, hcycl, hcyc, y, hqy, hy, n, hn, χ, u, hcarry⟩ :=
    rationalArithmeticKummerUnitH2_exists_cyclic_carry a q hqa hq2 x
  let A₀ : Algebra ℚ F := F.toIntermediateField.algebra'
  have hcycl₀ : letI := A₀; IsCyclotomicExtension {q ^ (k + 1)} ℚ F := hcycl
  have hcyc₀ : letI := A₀; IsCyclic Gal(F/ℚ) := hcyc
  have hcyclAll : ∀ A : Algebra ℚ F,
      letI := A; IsCyclotomicExtension {q ^ (k + 1)} ℚ F := by
    intro A
    have hA : A = A₀ := Subsingleton.elim _ _
    cases hA
    exact hcycl₀
  have hcycAll : ∀ A : Algebra ℚ F, letI := A; IsCyclic Gal(F/ℚ) := by
    intro A
    have hA : A = A₀ := Subsingleton.elim _ _
    cases hA
    exact hcyc₀
  letI : IsCyclotomicExtension {q ^ (k + 1)} ℚ F := hcyclAll _
  letI : IsCyclic Gal(F/ℚ) := hcycAll _
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ F) := ⟨rfl⟩
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  let N := q ^ (k + 1)
  letI : NeZero N := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  let hζ := IsCyclotomicExtension.zeta_spec N ℚ F
  obtain ⟨S, hS, houtside, hvalue, hsum, htwo⟩ :=
    rationalPrimeNormalizedResidual_exists_arithmetic_principal_character_sum
      a F q (Fact.out : q.Prime) hq2 k hζ u χ.toMonoidHom
  have hlocal (p : ℕ) (hp : p.Prime) :
      rationalArithmeticKummerUnitPrimeInvariant a q hqa p hp x =
        rationalCyclicInvariant n
          (χ.toMonoidHom
            (rationalArithmeticFiniteLocalReciprocityAut a F p hp u)).toAdd := by
    rw [rationalArithmeticKummerUnitPrimeInvariant_eq_finiteCarryInvariant
      a q hqa F p hp x y hy χ.toMonoidHom u hcarry]
    rw [rationalArithmeticFiniteCarryInvariant]
    rfl
  let r := rationalPrimeNormalizedResidual q (Fact.out : q.Prime) u
  let U : Finset Nat.Primes :=
    insert ⟨q, Fact.out⟩ (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding)
  have hlocal_q :
      rationalArithmeticKummerUnitPrimeInvariant a q hqa q Fact.out x =
        rationalCyclicInvariant n
          (χ.toMonoidHom
            (rationalArithmeticFiniteLocalReciprocityAut a F q Fact.out r)).toAdd := by
    rw [hlocal]
    rw [rationalArithmeticFiniteLocalReciprocityAut_normalizedResidual
      a F q Fact.out hq2 k hζ u]
  have hlocal_away (v : HeightOneSpectrum ℤ)
      (hvq : Rat.HeightOneSpectrum.natGenerator v ≠ q) :
      rationalArithmeticKummerUnitPrimeInvariant a q hqa
          (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v) x =
        rationalCyclicInvariant n
          (χ.toMonoidHom (arithmeticCyclotomicAwayAut a F v r)).toAdd := by
    rw [hlocal]
    unfold rationalArithmeticFiniteLocalReciprocityAut
    rw [← arithmeticCyclotomicAwayAut_eq_finiteLocalReciprocity a F v u]
    rw [arithmeticCyclotomicAwayAut_normalizedResidual
      a F q Fact.out k hζ v hvq u]
  have hzero_outside (v : HeightOneSpectrum ℤ) (hvS : v ∉ S)
      (hvq : Rat.HeightOneSpectrum.natGenerator v ≠ q) :
      rationalArithmeticKummerUnitPrimeInvariant a q hqa
          (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v) x = 0 := by
    rw [hlocal_away v hvq]
    have hvN : ¬Rat.HeightOneSpectrum.natGenerator v ∣ N := by
      intro hdvd
      have hdvdq : Rat.HeightOneSpectrum.natGenerator v ∣ q :=
        (Rat.HeightOneSpectrum.prime_natGenerator v).dvd_of_dvd_pow hdvd
      exact hvq (((Nat.dvd_prime (Fact.out : q.Prime)).mp hdvdq).resolve_left
        (Rat.HeightOneSpectrum.prime_natGenerator v).ne_one)
    rw [arithmeticCyclotomicAwayAut_eq_one_of_valuation_eq_one
      a F N v hvN hζ r (houtside v hvS)]
    calc
      rationalCyclicInvariant n
          (χ.toMonoidHom (1 : Gal(F/ℚ))).toAdd =
          rationalCyclicInvariant n 0 := congrArg (rationalCyclicInvariant n) (by
            change χ.toMonoidHom 1 = 1
            exact χ.toMonoidHom.map_one)
      _ = 0 := map_zero (rationalCyclicInvariant n)
  have hzero_not_mem_U (p : Nat.Primes) (hpU : p ∉ U) :
      rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x = 0 := by
    have hpq : p.val ≠ q := by
      intro hpq
      apply hpU
      exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hpq))
    let v : HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm p
    have hvp : Rat.HeightOneSpectrum.primesEquiv v = p :=
      Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p
    have hgen : Rat.HeightOneSpectrum.natGenerator v = p.val :=
      congrArg Subtype.val hvp
    have hvS : v ∉ S := by
      intro hvS
      apply hpU
      simp only [U, Finset.mem_insert, Finset.mem_map]
      exact Or.inr ⟨v, hvS, hvp⟩
    have hvq : Rat.HeightOneSpectrum.natGenerator v ≠ q := by
      intro h
      exact hpq (hgen.symm.trans h)
    simpa only [hgen] using hzero_outside v hvS hvq
  let T := (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x).support
  have hTU : T ⊆ U := by
    intro p hpT
    by_contra hpU
    have hpne : rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x ≠ 0 := by
      simpa only [T, Finsupp.mem_support_iff] using hpT
    apply hpne
    apply rationalCyclicInvariant_injective q
    rw [rationalArithmeticPrimeH2Invariant_unit_invariant]
    rw [hzero_not_mem_U p hpU, map_zero]
  have hsupport :
      (∑ p ∈ T,
        rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x) =
      ∑ p ∈ U,
        rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x := by
    apply Finset.sum_subset hTU
    intro p hpU hpT
    have hpzero : rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x = 0 := by
      change (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x) p = 0
      apply Finsupp.notMem_support_iff.mp
      simpa only [T] using hpT
    rw [← rationalArithmeticPrimeH2Invariant_unit_invariant]
    rw [hpzero, map_zero]
  have hqnot : (⟨q, Fact.out⟩ : Nat.Primes) ∉
      S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding := by
    intro hmem
    obtain ⟨v, hvS, hvq⟩ := Finset.mem_map.mp hmem
    have hgen : Rat.HeightOneSpectrum.natGenerator v = q :=
      congrArg Subtype.val hvq
    apply hS v hvS
    change Rat.HeightOneSpectrum.natGenerator v ∣ N
    rw [hgen]
    exact dvd_pow_self q (by omega)
  have hUexpand :
      (∑ p ∈ U,
        rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x) =
      rationalArithmeticKummerUnitPrimeInvariant a q hqa q Fact.out x +
        ∑ v ∈ S, rationalArithmeticKummerUnitPrimeInvariant a q hqa
          (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v) x := by
    let f : Nat.Primes → AddCircle (1 : ℚ) := fun p =>
      rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x
    change (insert ⟨q, Fact.out⟩
        (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding)).sum f = _
    calc
      _ = f ⟨q, Fact.out⟩ +
          (S.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding).sum f :=
        Finset.sum_insert hqnot
      _ = _ := by
        rw [Finset.sum_map]
        rfl
  have hSneq (v : HeightOneSpectrum ℤ) (hvS : v ∈ S) :
      Rat.HeightOneSpectrum.natGenerator v ≠ q := by
    intro hvq
    apply hS v hvS
    change Rat.HeightOneSpectrum.natGenerator v ∣ N
    rw [hvq]
    exact dvd_pow_self q (by omega)
  let z : ZMod n :=
    (χ.toMonoidHom
      (rationalArithmeticFiniteLocalReciprocityAut a F q Fact.out r)).toAdd +
      ∑ v ∈ S, (χ.toMonoidHom (arithmeticCyclotomicAwayAut a F v r)).toAdd
  have hselected :
      rationalArithmeticKummerUnitPrimeInvariant a q hqa q Fact.out x +
          ∑ v ∈ S, rationalArithmeticKummerUnitPrimeInvariant a q hqa
            (Rat.HeightOneSpectrum.natGenerator v)
            (Rat.HeightOneSpectrum.prime_natGenerator v) x =
        rationalCyclicInvariant n z := by
    rw [hlocal_q]
    have haway :
        (∑ v ∈ S, rationalArithmeticKummerUnitPrimeInvariant a q hqa
          (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v) x) =
        ∑ v ∈ S, rationalCyclicInvariant n
          (χ.toMonoidHom (arithmeticCyclotomicAwayAut a F v r)).toAdd := by
      apply Finset.sum_congr rfl
      intro v hvS
      exact hlocal_away v (hSneq v hvS)
    rw [haway, ← map_sum, ← map_add]
  have htotal :
      rationalCyclicInvariant q
          (rationalArithmeticFiniteH2InvariantSum a q hqa ha x) =
        rationalCyclicInvariant n z := by
    rw [rationalArithmeticFiniteH2InvariantSum_unit_invariants]
    change (∑ p ∈ T,
      rationalArithmeticKummerUnitPrimeInvariant a q hqa p.val p.property x) = _
    rw [hsupport, hUexpand, hselected]
  have htwoz : 2 • z = 0 := by
    exact htwo
  have htwoCircle : 2 • rationalCyclicInvariant n z = 0 := by
    rw [← map_nsmul, htwoz, map_zero]
  have htwoTotal : 2 • rationalCyclicInvariant q
      (rationalArithmeticFiniteH2InvariantSum a q hqa ha x) = 0 := by
    rw [htotal]
    exact htwoCircle
  have hqScalar : q • rationalArithmeticFiniteH2InvariantSum a q hqa ha x = 0 := by
    simp [nsmul_eq_mul]
  have hqTotal : q • rationalCyclicInvariant q
      (rationalArithmeticFiniteH2InvariantSum a q hqa ha x) = 0 := by
    rw [← map_nsmul, hqScalar, map_zero]
  have hzero := eq_zero_of_two_nsmul_eq_zero_of_odd_nsmul_eq_zero
    q ((Fact.out : q.Prime).odd_of_ne_two hq2)
    (rationalCyclicInvariant q
      (rationalArithmeticFiniteH2InvariantSum a q hqa ha x)) htwoTotal hqTotal
  apply rationalCyclicInvariant_injective q
  simpa only [map_zero] using hzero

end
end Dubon2026
