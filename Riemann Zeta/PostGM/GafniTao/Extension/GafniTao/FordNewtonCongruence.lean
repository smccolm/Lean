import GafniTao.FordPrimeSelection
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.ZMod.Basic

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

#print axioms ford_aeval_psum
#print axioms ford_newton_identity
#print axioms ford_elementary_eq_of_powerSums_eq
#print axioms fordRootPolynomial_eq_of_elementary_eq
#print axioms ford_multiset_eq_of_powerSums_eq

end

end GafniTao
