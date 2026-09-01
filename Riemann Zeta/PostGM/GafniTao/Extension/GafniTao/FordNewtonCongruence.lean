import GafniTao.FordPrimeSelection
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finite.Perm

/-!
# Ford Lemma 3.2: Newton congruences

This file formalizes the Newton-identity step used to bound the residue-class
fibres in Ford's equation (3.4).
-/

open Finset
open Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordPowerSum {d : ℕ} {R : Type*} [CommRing R]
    (c : Fin d → R) (r : ℕ) : R :=
  ∑ i : Fin d, c i ^ r

def fordElementary {d : ℕ} {R : Type*} [CommRing R]
    (c : Fin d → R) (r : ℕ) : R :=
  MvPolynomial.aeval c (MvPolynomial.esymm (Fin d) R r)

theorem ford_aeval_psum {d : ℕ} {R : Type*} [CommRing R]
    (c : Fin d → R) (r : ℕ) :
    MvPolynomial.aeval c (MvPolynomial.psum (Fin d) R r) =
      fordPowerSum c r := by
  simp [MvPolynomial.psum, fordPowerSum]

theorem ford_newton_identity
    {d : ℕ} {R : Type*} [CommRing R] (c : Fin d → R) (r : ℕ) :
    (r : R) * fordElementary c r = (-1 : R) ^ (r + 1) *
      ∑ a ∈ antidiagonal r with a.1 < r,
        (-1 : R) ^ a.1 * fordElementary c a.1 * fordPowerSum c a.2 := by
  have h := congrArg (MvPolynomial.aeval c)
    (MvPolynomial.mul_esymm_eq_sum (Fin d) R r)
  simpa [fordElementary, ford_aeval_psum, map_sum, map_mul, map_pow] using h

theorem ford_elementary_eq_of_powerSums_eq
    {p d : ℕ} (hp : Nat.Prime p) (hdp : d < p)
    (c c' : Fin d → ZMod p)
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    ∀ r, r ≤ d → fordElementary c r = fordElementary c' r := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hrd
      by_cases hr0 : r = 0
      · subst r
        simp [fordElementary]
      · have hrpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        have hrp : r < p := lt_of_le_of_lt hrd hdp
        have hrcast : (r : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt hrpos hrp
        have hc := ford_newton_identity c r
        have hc' := ford_newton_identity c' r
        apply (mul_left_cancel₀ hrcast)
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

theorem fordElementary_eq_multiset_esymm
    {d : ℕ} {R : Type*} [CommRing R] (c : Fin d → R) (r : ℕ) :
    fordElementary c r =
      ((Finset.univ : Finset (Fin d)).val.map c).esymm r := by
  exact MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin d) (R := R) r c

def fordRootPolynomial {d : ℕ} {R : Type*} [CommRing R]
    (c : Fin d → R) : R[X] :=
  (((Finset.univ : Finset (Fin d)).val.map c).map
    fun t => Polynomial.X - Polynomial.C t).prod

theorem fordRootPolynomial_eq_of_elementary_eq
    {d : ℕ} {R : Type*} [CommRing R] (c c' : Fin d → R)
    (helem : ∀ r, r ≤ d → fordElementary c r = fordElementary c' r) :
    fordRootPolynomial c = fordRootPolynomial c' := by
  unfold fordRootPolynomial
  rw [Multiset.prod_X_sub_X_eq_sum_esymm,
    Multiset.prod_X_sub_X_eq_sum_esymm]
  simp only [Multiset.card_map]
  apply Finset.sum_congr rfl
  intro r hr
  have hrd : r ≤ d := by simpa using (Finset.mem_range.mp hr)
  rw [← fordElementary_eq_multiset_esymm c r,
    ← fordElementary_eq_multiset_esymm c' r, helem r hrd]

/-- Ford's Newton-formula conclusion: equal first `d` power sums modulo a
prime `p>d` force equality of the multisets of residues. -/
theorem ford_multiset_eq_of_powerSums_eq
    {p d : ℕ} (hp : Nat.Prime p) (hdp : d < p)
    (c c' : Fin d → ZMod p)
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    (Finset.univ.val.map c) = Finset.univ.val.map c' := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have helem := ford_elementary_eq_of_powerSums_eq hp hdp c c' hpow
  have hpoly := fordRootPolynomial_eq_of_elementary_eq c c' helem
  have hroots := congrArg Polynomial.roots hpoly
  simpa only [fordRootPolynomial, Polynomial.roots_multiset_prod_X_sub_C] using hroots

theorem ford_exists_perm_of_multiset_eq
    {d : ℕ} {R : Type*} [LinearOrder R] (c c' : Fin d → R)
    (hmulti : (Finset.univ.val.map c) = Finset.univ.val.map c') :
    ∃ σ : Equiv.Perm (Fin d), c' = c ∘ σ := by
  have hperm : List.Perm (List.ofFn c) (List.ofFn c') := by
    exact Quotient.exact (show
      (↑(List.ofFn c) : Multiset R) = ↑(List.ofFn c') by
        simpa only [Fin.univ_val_map] using hmulti)
  have hsortedPerm : List.Perm
      (List.ofFn (c ∘ Tuple.sort c)) (List.ofFn (c' ∘ Tuple.sort c')) :=
    ((Tuple.sort c).ofFn_comp_perm c).trans
      (hperm.trans ((Tuple.sort c').ofFn_comp_perm c').symm)
  have hsortedList :
      List.ofFn (c ∘ Tuple.sort c) = List.ofFn (c' ∘ Tuple.sort c') :=
    hsortedPerm.eq_of_sortedLE
      (Tuple.monotone_sort c).sortedLE_ofFn
      (Tuple.monotone_sort c').sortedLE_ofFn
  have hsorted : c ∘ Tuple.sort c = c' ∘ Tuple.sort c' :=
    List.ofFn_injective hsortedList
  refine ⟨(Tuple.sort c').symm.trans (Tuple.sort c), ?_⟩
  funext i
  have hi := congrFun hsorted ((Tuple.sort c').symm i)
  simpa [Function.comp_apply] using hi.symm

theorem ford_powerSum_comp_perm
    {d : ℕ} {R : Type*} [CommRing R] (c : Fin d → R)
    (σ : Equiv.Perm (Fin d)) (r : ℕ) :
    fordPowerSum (c ∘ σ) r = fordPowerSum c r := by
  exact Equiv.sum_comp σ (fun i => c i ^ r)

def FordPowerSumFiber (p d : ℕ) (c : Fin d → ZMod p) :=
  {c' : Fin d → ZMod p // ∀ r, 1 ≤ r → r ≤ d →
    fordPowerSum c' r = fordPowerSum c r}

/-- The quantitative Newton conclusion used in Ford's equation (3.4): a
first-`d` power-sum fibre modulo a prime `p>d` has at most `d!` elements. -/
theorem ford_powerSumFiber_card_le_factorial
    {p d : ℕ} (hp : Nat.Prime p) (hdp : d < p) (c : Fin d → ZMod p) :
    Nat.card (FordPowerSumFiber p d c) ≤ Nat.factorial d := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : LinearOrder (ZMod p) := LinearOrder.lift' ZMod.val (ZMod.val_injective p)
  let orbit : Equiv.Perm (Fin d) → FordPowerSumFiber p d c := fun σ =>
    ⟨c ∘ σ, fun r _ _ => ford_powerSum_comp_perm c σ r⟩
  have horbit : Function.Surjective orbit := by
    rintro ⟨c', hc'⟩
    have hmulti := ford_multiset_eq_of_powerSums_eq hp hdp c c'
      (fun r hr1 hrd => (hc' r hr1 hrd).symm)
    obtain ⟨σ, hσ⟩ := ford_exists_perm_of_multiset_eq c c' hmulti
    refine ⟨σ, Subtype.ext ?_⟩
    exact hσ.symm
  calc
    Nat.card (FordPowerSumFiber p d c) ≤ Nat.card (Equiv.Perm (Fin d)) :=
      Nat.card_le_card_of_surjective orbit horbit
    _ = Nat.factorial d := by rw [Nat.card_perm, Nat.card_fin]

#print axioms ford_aeval_psum
#print axioms ford_newton_identity
#print axioms ford_elementary_eq_of_powerSums_eq
#print axioms fordRootPolynomial_eq_of_elementary_eq
#print axioms ford_multiset_eq_of_powerSums_eq
#print axioms ford_exists_perm_of_multiset_eq
#print axioms ford_powerSumFiber_card_le_factorial

end

end GafniTao
