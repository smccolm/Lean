import RiemannZeta.GuthMaynard.PolynomialPowers
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Arithmetic coefficient bounds

This module proves the classical subpolynomial bound for the divisor-counting
function, derives the ordered-factorization estimate used by powered Dirichlet
polynomials, and specializes the powered detector-coefficient theorem without
arithmetic proposition parameters.
-/

open Finset Filter
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

lemma exponent_succ_le_const_mul_two_rpow (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ a : ℕ,
      ((a + 1 : ℕ) : ℝ) ≤ K * (2 : ℝ) ^ (eps * (a : ℝ)) := by
  let c : ℝ := eps * Real.log 2
  have hc : 0 < c := mul_pos heps (Real.log_pos one_lt_two)
  refine ⟨c⁻¹ + 1, by
    have : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    linarith, ?_⟩
  intro a
  have hca : 0 ≤ c * (a : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg a)
  have hmul : c * (a : ℝ) ≤ Real.exp (c * (a : ℝ)) :=
    le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp _)
  have ha : (a : ℝ) ≤ c⁻¹ * Real.exp (c * (a : ℝ)) := by
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    simpa [mul_comm] using hmul
  have hone : (1 : ℝ) ≤ Real.exp (c * (a : ℝ)) := Real.one_le_exp hca
  have hsum : (a : ℝ) + 1 ≤ (c⁻¹ + 1) * Real.exp (c * (a : ℝ)) := by
    nlinarith
  calc
    ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by norm_num
    _ ≤ (c⁻¹ + 1) * Real.exp (c * (a : ℝ)) := hsum
    _ = (c⁻¹ + 1) * (2 : ℝ) ^ (eps * (a : ℝ)) := by
      congr 1
      rw [Real.rpow_def_of_pos zero_lt_two]
      congr 1
      dsimp [c]
      ring

lemma exponent_succ_le_large_prime_rpow (eps : ℝ) (p a : ℕ)
    (hlarge : (2 : ℝ) ≤ (p : ℝ) ^ eps) :
    ((a + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (eps * (a : ℝ)) := by
  have htwo : ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := by
    have h := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) a
    norm_num at h
    simpa [add_comm] using h
  calc
    ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := htwo
    _ ≤ ((p : ℝ) ^ eps) ^ a := by gcongr
    _ = (p : ℝ) ^ (eps * (a : ℝ)) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p) eps a]

theorem divisorCountBound_native : DivisorCountBoundProp := by
  intro eps heps
  obtain ⟨K, hK, hsmall⟩ := exponent_succ_le_const_mul_two_rpow eps heps
  have htendsto :
      Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ eps) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop heps).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ p : ℕ in Filter.atTop, (2 : ℝ) ≤ (p : ℝ) ^ eps :=
    htendsto.eventually (eventually_ge_atTop 2)
  obtain ⟨B, hB⟩ := (eventually_atTop.1 hevent)
  refine ⟨K ^ B, pow_pos (lt_of_lt_of_le zero_lt_one hK) B, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  let smallFactors := n.primeFactors.filter (fun p => p < B)
  have hsmall_card : smallFactors.card ≤ B := by
    have hsubset : smallFactors ⊆ Finset.range B := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsubset
  have hKpow : K ^ smallFactors.card ≤ K ^ B := by
    exact pow_le_pow_right₀ (by linarith) hsmall_card
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < B then K else 1) *
          (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    split_ifs with hpB
    · have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
      have hexp : 0 ≤ eps * (n.factorization p : ℝ) :=
        mul_nonneg heps.le (Nat.cast_nonneg _)
      have hs := hsmall (n.factorization p)
      have hs' : (n.factorization p : ℝ) + 1 ≤
          K * (2 : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
        simpa using hs
      exact hs'.trans <| mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by norm_num) hpTwo hexp) (by linarith)
    · simpa using exponent_succ_le_large_prime_rpow eps p (n.factorization p)
        (hB p (Nat.le_of_not_gt hpB))
  have hprimeProduct :
      (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)) ≤
        K ^ smallFactors.card * (n : ℝ) ^ eps := by
    calc
      (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)) ≤
          ∏ p ∈ n.primeFactors,
            ((if p < B then K else 1) *
              (p : ℝ) ^ (eps * (n.factorization p : ℝ))) := by
            exact Finset.prod_le_prod (fun _ _ => by positivity) hfactor
      _ = (∏ p ∈ n.primeFactors, (if p < B then K else 1)) *
          ∏ p ∈ n.primeFactors,
            (p : ℝ) ^ (eps * (n.factorization p : ℝ)) := by
            rw [Finset.prod_mul_distrib]
      _ = K ^ smallFactors.card * (n : ℝ) ^ eps := by
        congr 1
        · rw [Finset.prod_ite]
          simp [smallFactors]
        · have hreconstruct :
              (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
            simpa [Nat.prod_factorization_eq_prod_primeFactors] using
              Nat.prod_factorization_pow_eq_self hn0
          calc
            (∏ p ∈ n.primeFactors,
                (p : ℝ) ^ (eps * (n.factorization p : ℝ))) =
                ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ eps := by
                  apply Finset.prod_congr rfl
                  intro p hp
                  calc
                    (p : ℝ) ^ (eps * (n.factorization p : ℝ)) =
                        (p : ℝ) ^ ((n.factorization p : ℝ) * eps) := by
                          rw [mul_comm]
                    _ = ((p : ℝ) ^ (n.factorization p : ℝ)) ^ eps :=
                          Real.rpow_mul (Nat.cast_nonneg p) _ _
                    _ = ((p : ℝ) ^ n.factorization p) ^ eps := by
                          rw [Real.rpow_natCast]
            _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ eps := by
                  rw [Real.finset_prod_rpow]
                  intro p hp
                  positivity
            _ = (n : ℝ) ^ eps := by
                  have hreconstructReal :
                      (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
                    exact_mod_cast hreconstruct
                  rw [hreconstructReal]
  rw [Nat.card_divisors hn0]
  push_cast
  exact hprimeProduct.trans <| mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg (by positivity) _)

theorem factorizationCountBound_native : FactorizationCountBoundProp := by
  intro k eps heps
  let delta : ℝ := eps / (k + 1 : ℕ)
  have hkOnePos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos heps hkOnePos
  obtain ⟨C, hC, hDivisor⟩ := divisorCountBound_native delta hdelta
  refine ⟨C ^ k, pow_pos hC k, ?_⟩
  intro m hm
  let tuples :=
    (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter
      (fun p => (∏ x : Fin k, p x) = m)
  have htupleSubset : tuples ⊆ Fintype.piFinset (fun (_ : Fin k) => m.divisors) := by
    intro p hp
    have hpProduct := (Finset.mem_filter.mp hp).2
    rw [Fintype.mem_piFinset]
    intro i
    rw [Nat.mem_divisors]
    constructor
    · have hi : p i ∣ ∏ j : Fin k, p j :=
        dvd_prod_of_mem (fun j => p j) (Finset.mem_univ i)
      simpa [hpProduct] using hi
    · exact Nat.ne_of_gt hm
  have hcardNat : tuples.card ≤ m.divisors.card ^ k := by
    calc
      tuples.card ≤ (Fintype.piFinset (fun (_ : Fin k) => m.divisors)).card :=
        Finset.card_le_card htupleSubset
      _ = m.divisors.card ^ k := Fintype.card_piFinset_const m.divisors k
  have hcardReal : (tuples.card : ℝ) ≤ (m.divisors.card : ℝ) ^ k := by
    exact_mod_cast hcardNat
  have hdivisorReal : (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ delta :=
    hDivisor m hm
  have hpowBound : (m.divisors.card : ℝ) ^ k ≤
      (C * (m : ℝ) ^ delta) ^ k := by
    gcongr
  have hdeltaK : delta * (k : ℝ) ≤ eps := by
    have hkLe : (k : ℝ) ≤ (k + 1 : ℕ) := by norm_num
    have hratio : (k : ℝ) / (k + 1 : ℕ) ≤ 1 :=
      (div_le_one hkOnePos).mpr hkLe
    calc
      delta * (k : ℝ) = eps * ((k : ℝ) / (k + 1 : ℕ)) := by
        dsimp [delta]
        field_simp
      _ ≤ eps * 1 := mul_le_mul_of_nonneg_left hratio heps.le
      _ = eps := mul_one eps
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrpow : (m : ℝ) ^ (delta * (k : ℝ)) ≤ (m : ℝ) ^ eps :=
    Real.rpow_le_rpow_of_exponent_le hmOne hdeltaK
  change (tuples.card : ℝ) ≤ C ^ k * (m : ℝ) ^ eps
  calc
    (tuples.card : ℝ) ≤ (m.divisors.card : ℝ) ^ k := hcardReal
    _ ≤ (C * (m : ℝ) ^ delta) ^ k := hpowBound
    _ = C ^ k * (m : ℝ) ^ (delta * (k : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg m)]
    _ ≤ C ^ k * (m : ℝ) ^ eps :=
      mul_le_mul_of_nonneg_left hrpow (pow_nonneg hC.le k)

theorem powCoeffBound_native : PowCoeffBoundProp :=
  powCoeff_bound_of_divisor_and_factorization
    divisorCountBound_native factorizationCountBound_native

end RiemannZeta.GuthMaynard
