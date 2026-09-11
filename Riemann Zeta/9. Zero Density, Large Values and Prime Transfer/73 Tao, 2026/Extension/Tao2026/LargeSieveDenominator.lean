import Tao2026.LargeSieveAggregation
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Fixed-cardinality denominator lower bounds

This file supplies the elementary-symmetric lower bound needed after the
global survivor estimate.  A uniform lower bound for every modulus weight is
amplified over all fixed-cardinality selections, and the binomial coefficient
is bounded below without any loss depending on the number of selections.
-/

open Finset
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The type of `k`-element subsets has the expected binomial cardinality. -/
theorem card_fixedCardModulusSelections
    (Q : Type*) [Fintype Q] [DecidableEq Q] (k : ℕ) :
    Fintype.card (FixedCardModulusSelections Q k) =
      Nat.choose (Fintype.card Q) k := by
  classical
  unfold FixedCardModulusSelections
  rw [Fintype.card_subtype]
  have heq : (Finset.univ.filter fun s : Finset Q => s.card = k) =
      Finset.powersetCard k (Finset.univ : Finset Q) := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [heq, Finset.card_powersetCard, Finset.card_univ]

/-- A pointwise lower bound for the weights gives the corresponding
binomial lower bound for their degree-`k` elementary symmetric sum. -/
theorem fixedCardSelection_weightSum_ge_choose
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (w : Q → ℝ) (c : ℝ) (k : ℕ)
    (hc : 0 ≤ c) (hw : ∀ q, c ≤ w q) :
    (Nat.choose (Fintype.card Q) k : ℝ) * c ^ k ≤
      ∑ s : FixedCardModulusSelections Q k, ∏ q ∈ s.1, w q := by
  classical
  calc
    (Nat.choose (Fintype.card Q) k : ℝ) * c ^ k =
        ∑ _s : FixedCardModulusSelections Q k, c ^ k := by
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, card_fixedCardModulusSelections]
    _ ≤ ∑ s : FixedCardModulusSelections Q k, ∏ q ∈ s.1, w q := by
      apply Finset.sum_le_sum
      intro s hs
      calc
        c ^ k = c ^ s.1.card := by rw [s.2]
        _ = ∏ _q ∈ s.1, c := (Finset.prod_const c).symm
        _ ≤ ∏ q ∈ s.1, w q :=
          Finset.prod_le_prod (fun _ _ => hc) (fun q _ => hw q)

/-- If `2k ≤ n`, then `choose n k` dominates `(n/(2k))^k`. -/
theorem choose_ge_half_card_div_pow
    (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ((n : ℝ) / (2 * k)) ^ k ≤ (Nat.choose n k : ℝ) := by
  have hsub : k ≤ n + 1 := by omega
  have hhalfNat : n ≤ 2 * (n + 1 - k) := by omega
  have hhalfReal : (n : ℝ) ≤ 2 * (n + 1 - k : ℕ) := by
    exact_mod_cast hhalfNat
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : (n : ℝ) / (2 * k) ≤ (n + 1 - k : ℕ) / k := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k) hkpos).2
    nlinarith
  have hpow : ((n : ℝ) / (2 * k)) ^ k ≤
      ((n + 1 - k : ℕ) / k : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hbase k
  have hfactNat : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
  have hfact : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast hfactNat
  have hnum : (0 : ℝ) ≤ (n + 1 - k : ℕ) ^ k := by positivity
  have hfrac : ((n + 1 - k : ℕ) : ℝ) ^ k / (k : ℝ) ^ k ≤
      ((n + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) := by
    exact div_le_div_of_nonneg_left hnum (by positivity) hfact
  calc
    ((n : ℝ) / (2 * k)) ^ k ≤
        ((n + 1 - k : ℕ) / k : ℝ) ^ k := hpow
    _ = ((n + 1 - k : ℕ) : ℝ) ^ k / (k : ℝ) ^ k := by
      rw [div_pow]
    _ ≤ ((n + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) := hfrac
    _ ≤ (Nat.choose n k : ℝ) := Nat.pow_le_choose k n

/-- Source-facing elementary-symmetric denominator bound: if every weight is
at least `c` and at least `2k` moduli are available, then the sum over all
`k`-element selections is at least `((#Q)c/(2k))^k`. -/
theorem fixedCardSelection_weightSum_ge_halfCard
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (w : Q → ℝ) (c : ℝ) (k : ℕ)
    (hc : 0 ≤ c) (hw : ∀ q, c ≤ w q)
    (hk : 1 ≤ k) (hcard : 2 * k ≤ Fintype.card Q) :
    (((Fintype.card Q : ℝ) * c) / (2 * k)) ^ k ≤
      ∑ s : FixedCardModulusSelections Q k, ∏ q ∈ s.1, w q := by
  have hchoose := choose_ge_half_card_div_pow
    (Fintype.card Q) k hk hcard
  have hcpow : 0 ≤ c ^ k := pow_nonneg hc k
  calc
    (((Fintype.card Q : ℝ) * c) / (2 * k)) ^ k =
        ((Fintype.card Q : ℝ) / (2 * k)) ^ k * c ^ k := by
      rw [← mul_pow]
      congr 2
      ring
    _ ≤ (Nat.choose (Fintype.card Q) k : ℝ) * c ^ k :=
      mul_le_mul_of_nonneg_right hchoose hcpow
    _ ≤ ∑ s : FixedCardModulusSelections Q k, ∏ q ∈ s.1, w q :=
      fixedCardSelection_weightSum_ge_choose w c k hc hw

end

end Tao2026
