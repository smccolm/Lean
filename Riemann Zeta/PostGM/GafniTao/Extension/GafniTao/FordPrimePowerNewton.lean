import GafniTao.FordTriangularFiber
import Mathlib.Data.ZMod.Units

/-!
# Ford Lemma 2.4: prime-power Newton infrastructure

This file begins the prime-power part of the nonsingular fibre estimate used
in Ford's Lemma 3.2.  Newton's identities are proved over an arbitrary
commutative ring under the exact unit hypotheses needed to cancel the
integers `1,...,d`.  The specialization to `ZMod (p^s)` derives those unit
hypotheses from `p>d`.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem ford_elementary_eq_of_powerSums_eq_of_isUnit
    {d : ℕ} {R : Type*} [CommRing R]
    (c c' : Fin d → R)
    (hunit : ∀ r, 1 ≤ r → r ≤ d → IsUnit (r : R))
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    ∀ r, r ≤ d → fordElementary c r = fordElementary c' r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hrd
      by_cases hr0 : r = 0
      · subst r
        simp [fordElementary]
      · have hrpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        have hc := ford_newton_identity c r
        have hc' := ford_newton_identity c' r
        apply (hunit r hrpos hrd).mul_left_cancel
        rw [hc, hc']
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        have haanti := (Finset.mem_filter.mp ha).1
        have halt := (Finset.mem_filter.mp ha).2
        have hasum := mem_antidiagonal.mp haanti
        have ha1le : a.1 ≤ d := le_trans (Nat.le_of_lt halt) hrd
        have helem := ih a.1 halt ha1le
        have hpower : fordPowerSum c a.2 = fordPowerSum c' a.2 := by
          by_cases ha20 : a.2 = 0
          · rw [ha20]
            simp [fordPowerSum]
          · apply hpow a.2 (Nat.one_le_iff_ne_zero.mpr ha20)
            omega
        rw [helem, hpower]

theorem ford_natCast_isUnit_zmod_prime_pow
    {p s d r : ℕ} (hp : Nat.Prime p) (hs : 0 < s)
    (hr1 : 1 ≤ r) (hrd : r ≤ d) (hdp : d < p) :
    IsUnit (r : ZMod (p ^ s)) := by
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hs]
  exact Nat.not_dvd_of_pos_of_lt hr1 (hrd.trans_lt hdp)

theorem ford_elementary_eq_of_powerSums_eq_prime_pow
    {p s d : ℕ} (hp : Nat.Prime p) (hs : 0 < s) (hdp : d < p)
    (c c' : Fin d → ZMod (p ^ s))
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    ∀ r, r ≤ d → fordElementary c r = fordElementary c' r := by
  exact ford_elementary_eq_of_powerSums_eq_of_isUnit c c'
    (fun r hr1 hrd => ford_natCast_isUnit_zmod_prime_pow hp hs hr1 hrd hdp)
    hpow

theorem fordRootPolynomial_eq_of_powerSums_eq_prime_pow
    {p s d : ℕ} (hp : Nat.Prime p) (hs : 0 < s) (hdp : d < p)
    (c c' : Fin d → ZMod (p ^ s))
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    fordRootPolynomial c = fordRootPolynomial c' := by
  apply fordRootPolynomial_eq_of_elementary_eq
  exact ford_elementary_eq_of_powerSums_eq_prime_pow hp hs hdp c c' hpow

theorem fordRootPolynomial_eval
    {d : ℕ} {R : Type*} [CommRing R] (c : Fin d → R) (t : R) :
    (fordRootPolynomial c).eval t = ∏ i : Fin d, (t - c i) := by
  unfold fordRootPolynomial
  rw [eval_multiset_prod]
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C,
    Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Multiset.prod_coe,
    List.prod_ofFn]

def fordPrimeReduction {p s : ℕ} (a : ZMod (p ^ s)) : ZMod p :=
  ZMod.cast a

theorem fordPrimeReduction_map_powerSum
    {p s d r : ℕ} (hs : 0 < s) (c : Fin d → ZMod (p ^ s)) :
    fordPrimeReduction (fordPowerSum c r) =
      fordPowerSum (fun i => fordPrimeReduction (c i)) r := by
  let hdiv : p ∣ p ^ s := dvd_pow_self p hs.ne'
  change (ZMod.castHom hdiv (ZMod p)) (fordPowerSum c r) = _
  simp only [fordPowerSum, map_sum, ZMod.castHom_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact ZMod.cast_pow hdiv (c i) r

theorem ford_isUnit_of_primeReduction_ne_zero
    {p s : ℕ} (hp : Nat.Prime p) (hs : 0 < s)
    (a : ZMod (p ^ s)) (ha : fordPrimeReduction a ≠ 0) : IsUnit a := by
  letI : NeZero (p ^ s) := ⟨pow_ne_zero s hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val a,
    ZMod.isUnit_natCast_iff_not_dvd_pow hp hs]
  intro hpa
  apply ha
  unfold fordPrimeReduction
  rw [ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_zero_iff a.val p).mpr hpa

theorem ford_exists_reduction_perm_of_powerSums_eq_prime_pow
    {p s d : ℕ} (hp : Nat.Prime p) (hs : 0 < s) (hdp : d < p)
    (c c' : Fin d → ZMod (p ^ s))
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    ∃ σ : Equiv.Perm (Fin d),
      (fun i => fordPrimeReduction (c' i)) =
        (fun i => fordPrimeReduction (c i)) ∘ σ := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : LinearOrder (ZMod p) := LinearOrder.lift' ZMod.val (ZMod.val_injective p)
  let cRed : Fin d → ZMod p := fun i => fordPrimeReduction (c i)
  let cRed' : Fin d → ZMod p := fun i => fordPrimeReduction (c' i)
  have hpowRed : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum cRed r = fordPowerSum cRed' r := by
    intro r hr1 hrd
    rw [← fordPrimeReduction_map_powerSum hs c,
      ← fordPrimeReduction_map_powerSum hs c', hpow r hr1 hrd]
  have hmulti := ford_multiset_eq_of_powerSums_eq hp hdp cRed cRed' hpowRed
  exact ford_exists_perm_of_multiset_eq cRed cRed' hmulti

theorem ford_eq_comp_perm_of_powerSums_eq_prime_pow
    {p s d : ℕ} (hp : Nat.Prime p) (hs : 0 < s) (hdp : d < p)
    (c c' : Fin d → ZMod (p ^ s))
    (hdistinct : Function.Injective (fun i => fordPrimeReduction (c i)))
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    ∃ σ : Equiv.Perm (Fin d), c' = c ∘ σ := by
  obtain ⟨σ, hσ⟩ :=
    ford_exists_reduction_perm_of_powerSums_eq_prime_pow hp hs hdp c c' hpow
  refine ⟨σ, funext fun i => ?_⟩
  have hpoly := fordRootPolynomial_eq_of_powerSums_eq_prime_pow
    hp hs hdp c c' hpow
  have hzero : ∏ j : Fin d, (c' i - c j) = 0 := by
    rw [← fordRootPolynomial_eval c (c' i), hpoly,
      fordRootPolynomial_eval]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (c' i))
  let u : ZMod (p ^ s) :=
    ∏ j ∈ (Finset.univ : Finset (Fin d)).erase (σ i), (c' i - c j)
  have hu : IsUnit u := by
    unfold u
    rw [IsUnit.prod_iff]
    intro j hj
    apply ford_isUnit_of_primeReduction_ne_zero hp hs
    intro hzeroRed
    have hcastSub : fordPrimeReduction (c' i - c j) =
        fordPrimeReduction (c' i) - fordPrimeReduction (c j) := by
      let hdiv : p ∣ p ^ s := dvd_pow_self p hs.ne'
      exact ZMod.cast_sub hdiv (c' i) (c j)
    rw [hcastSub, sub_eq_zero] at hzeroRed
    have hσi := congrFun hσ i
    have heq : fordPrimeReduction (c (σ i)) = fordPrimeReduction (c j) := by
      simpa [Function.comp_apply] using hσi.symm.trans hzeroRed
    exact (Finset.mem_erase.mp hj).1 (hdistinct heq).symm
  have hproduct : u * (c' i - c (σ i)) = 0 := by
    rw [show u * (c' i - c (σ i)) = ∏ j : Fin d, (c' i - c j) by
      exact Finset.prod_erase_mul Finset.univ (fun j => c' i - c j)
        (Finset.mem_univ (σ i))]
    exact hzero
  apply sub_eq_zero.mp
  exact hu.mul_left_cancel (by simpa using hproduct)

def FordPrimePowerPowerSumFiber (p s d : ℕ)
    (c : Fin d → ZMod (p ^ s)) :=
  {c' : Fin d → ZMod (p ^ s) // ∀ r, 1 ≤ r → r ≤ d →
    fordPowerSum c' r = fordPowerSum c r}

theorem ford_primePowerPowerSumFiber_card_le_factorial
    {p s d : ℕ} (hp : Nat.Prime p) (hs : 0 < s) (hdp : d < p)
    (c : Fin d → ZMod (p ^ s))
    (hdistinct : Function.Injective (fun i => fordPrimeReduction (c i))) :
    Nat.card (FordPrimePowerPowerSumFiber p s d c) ≤ Nat.factorial d := by
  classical
  let orbit : Equiv.Perm (Fin d) → FordPrimePowerPowerSumFiber p s d c :=
    fun σ => ⟨c ∘ σ, fun r _ _ => ford_powerSum_comp_perm c σ r⟩
  have horbit : Function.Surjective orbit := by
    rintro ⟨c', hc'⟩
    obtain ⟨σ, hσ⟩ := ford_eq_comp_perm_of_powerSums_eq_prime_pow
      hp hs hdp c c' hdistinct (fun r hr1 hrd => (hc' r hr1 hrd).symm)
    exact ⟨σ, Subtype.ext hσ.symm⟩
  calc
    Nat.card (FordPrimePowerPowerSumFiber p s d c) ≤
        Nat.card (Equiv.Perm (Fin d)) :=
      Nat.card_le_card_of_surjective orbit horbit
    _ = Nat.factorial d := by rw [Nat.card_perm, Nat.card_fin]

#print axioms ford_elementary_eq_of_powerSums_eq_of_isUnit
#print axioms ford_natCast_isUnit_zmod_prime_pow
#print axioms ford_elementary_eq_of_powerSums_eq_prime_pow
#print axioms fordRootPolynomial_eq_of_powerSums_eq_prime_pow
#print axioms fordRootPolynomial_eval
#print axioms fordPrimeReduction_map_powerSum
#print axioms ford_isUnit_of_primeReduction_ne_zero
#print axioms ford_exists_reduction_perm_of_powerSums_eq_prime_pow
#print axioms ford_eq_comp_perm_of_powerSums_eq_prime_pow
#print axioms ford_primePowerPowerSumFiber_card_le_factorial

end

end GafniTao
