import GafniTao.FordLemma51Exponential

/-!
# Ford Lemma 5.1: exact exponent normalization

This file separates the analytic moment estimate from the algebra which
produces Ford's displayed negative powers.  The normalization lemma keeps all
three positive scales explicit; in particular, the cancellation of the
auxiliary `M₂` is proved rather than performed informally.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The exponent identity behind the last line of Ford's Lemma 5.1.  It is
stated independently of the analytic definitions so that every cancellation
can be audited directly. -/
theorem fordLemma51_prefactor_normalization
    {a b c v n : ℝ} {r s : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hv : 0 ≤ v)
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) :
    n / (a * b) *
        (b ^ (2 * r * s - 2 * s) * a ^ (2 * r * s - 2 * r) * v) ^
          (1 / ((2 * r * s : ℕ) : ℝ)) =
      n * (c / b) ^ (1 / (r : ℝ)) *
        (c ^ (-(2 * s : ℝ)) * a ^ (-(2 * r : ℝ)) * v) ^
          (1 / ((2 * r * s : ℕ) : ℝ)) := by
  have hpNat : 0 < 2 * r * s := by positivity
  have hp : 0 < ((2 * r * s : ℕ) : ℝ) := by exact_mod_cast hpNat
  have hq : 0 < 1 / ((2 * r * s : ℕ) : ℝ) := by positivity
  have hbr : 2 * s ≤ 2 * r * s := by
    calc
      2 * s = (2 * s) * 1 := by omega
      _ ≤ (2 * s) * r := Nat.mul_le_mul_left (2 * s) hr
      _ = 2 * r * s := by ring
  have har : 2 * r ≤ 2 * r * s := by
    calc
      2 * r = (2 * r) * 1 := by omega
      _ ≤ (2 * r) * s := Nat.mul_le_mul_left (2 * r) hs
      _ = 2 * r * s := by ring
  by_cases hv0 : v = 0
  · subst v
    rw [mul_zero, Real.zero_rpow hq.ne', mul_zero]
    rw [mul_zero, Real.zero_rpow hq.ne', mul_zero]
  have hvpos : 0 < v := hv.lt_of_ne' hv0
  have hleft : 0 < n / (a * b) *
      (b ^ (2 * r * s - 2 * s) * a ^ (2 * r * s - 2 * r) * v) ^
        (1 / ((2 * r * s : ℕ) : ℝ)) := by positivity
  have hright : 0 < n * (c / b) ^ (1 / (r : ℝ)) *
      (c ^ (-(2 * s : ℝ)) * a ^ (-(2 * r : ℝ)) * v) ^
        (1 / ((2 * r * s : ℕ) : ℝ)) := by positivity
  apply Real.log_injOn_pos (Set.mem_Ioi.2 hleft) (Set.mem_Ioi.2 hright)
  rw [Real.log_mul (div_ne_zero hn.ne' (mul_ne_zero ha.ne' hb.ne'))
      (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))]
  rw [Real.log_div hn.ne' (mul_ne_zero ha.ne' hb.ne'), Real.log_mul ha.ne' hb.ne']
  rw [Real.log_rpow (by positivity)]
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hb.ne') (pow_ne_zero _ ha.ne')) hvpos.ne']
  rw [Real.log_mul (pow_ne_zero _ hb.ne') (pow_ne_zero _ ha.ne')]
  rw [Real.log_pow, Real.log_pow]
  rw [Real.log_mul
      (mul_ne_zero hn.ne' (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))
      (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))]
  rw [Real.log_mul hn.ne'
      (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))]
  rw [Real.log_rpow (by positivity), Real.log_div hc.ne' hb.ne']
  rw [Real.log_rpow (by positivity)]
  rw [Real.log_mul
      (mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hc _))
        (ne_of_gt (Real.rpow_pos_of_pos ha _))) hvpos.ne']
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hc _))
      (ne_of_gt (Real.rpow_pos_of_pos ha _))]
  rw [Real.log_rpow hc, Real.log_rpow ha]
  push_cast [Nat.cast_sub hbr, Nat.cast_sub har]
  field_simp
  ring

/-- The portion of the moment majorant not containing the two Hölder
prefactors. -/
def fordLemma51AnalyticCore
    (k h g r s M M₂ N : ℕ) (B : Finset ℕ) (t : ℝ) : ℝ :=
  (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
    (fordVinogradovMomentNat r k M : ℝ) *
    (fordLemma51WindowMoment k h g s B : ℝ) *
    ∏ j : FordLemma51DegreeWindow k h g,
      fordLemma51W s M₂ r M N t j.1

/-- Ford's displayed expression inside the final `1/(2rs)` power, still at
the natural cutoff used by the proof. -/
def fordLemma51DisplayedCore
    (k h g r s M M₂ N : ℕ) (B : Finset ℕ) (t : ℝ) : ℝ :=
  (5 * (r : ℝ)) ^ k * (M₂ : ℝ) ^ (-(2 * s : ℝ)) *
    (M : ℝ) ^ (-(2 * r : ℝ) + fordVinogradovKappa k) *
    (fordVinogradovMomentNat r k M : ℝ) *
    (fordLemma51WindowMoment k h g s B : ℝ) *
    ∏ j : FordLemma51DegreeWindow k h g,
      fordLemma51W s M₂ r M N t j.1

theorem fordLemma51W_nonneg
    {k s M₂ r M : ℕ} {N t : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hM : 0 < M)
    (hN : 0 < N) (ht : 0 < t) (j : Fin k) :
    0 ≤ fordLemma51W s M₂ r M N t j := by
  unfold fordLemma51W
  apply le_min
  · positivity
  · positivity

theorem fordLemma51AnalyticCore_nonneg
    {k h g r s M M₂ : ℕ} (hs : 0 < s)
    (hr : 0 < r) (hM : 0 < M) {N : ℕ} {t : ℝ}
    (hN : (0 : ℝ) < N) (ht : 0 < t) (B : Finset ℕ) :
    0 ≤ fordLemma51AnalyticCore k h g r s M M₂ N B t := by
  have hprod : 0 ≤ ∏ j : FordLemma51DegreeWindow k h g,
      fordLemma51W s M₂ r M N t j.1 := by
    exact Finset.prod_nonneg fun j _ =>
      fordLemma51W_nonneg hs hr hM hN ht j.1
  unfold fordLemma51AnalyticCore
  positivity

theorem fordLemma51MomentMajorant_eq_prefactors
    (k h g r s M M₂ N : ℕ) (B : Finset ℕ) (t : ℝ) :
    fordLemma51MomentMajorant k h g r s M M₂ N B t =
      (B.card : ℝ) ^ (2 * r * s - 2 * s) *
        (M : ℝ) ^ (2 * r * s - 2 * r) *
        fordLemma51AnalyticCore k h g r s M M₂ N B t := by
  unfold fordLemma51MomentMajorant fordLemma51AnalyticCore
  ring

theorem fordLemma51DisplayedCore_eq_separated
    {k h g r s M M₂ N : ℕ} (hM : 0 < M)
    (B : Finset ℕ) (t : ℝ) :
    fordLemma51DisplayedCore k h g r s M M₂ N B t =
      (M₂ : ℝ) ^ (-(2 * s : ℝ)) * (M : ℝ) ^ (-(2 * r : ℝ)) *
        fordLemma51AnalyticCore k h g r s M M₂ N B t := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  unfold fordLemma51DisplayedCore fordLemma51AnalyticCore
  rw [Real.rpow_add hMreal]
  rw [Real.rpow_natCast]
  ring

/-- The exact negative-exponent normalization of the analytic term in the
natural-cutoff version of Lemma 5.1. -/
theorem fordLemma51_centralTerm_eq_displayed
    {k h g r s M M₂ N : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hM : 0 < M) (hM₂ : 0 < M₂) {B : Finset ℕ}
    (hBne : B.Nonempty) {t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    (N : ℝ) / ((M : ℝ) * B.card) *
        (fordLemma51MomentMajorant k h g r s M M₂ N B t) ^
          (1 / ((2 * r * s : ℕ) : ℝ)) =
      (N : ℝ) * ((M₂ : ℝ) / B.card) ^ (1 / (r : ℝ)) *
        (fordLemma51DisplayedCore k h g r s M M₂ N B t) ^
          (1 / ((2 * r * s : ℕ) : ℝ)) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hM₂real : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hBcard : 0 < B.card := Finset.card_pos.mpr hBne
  have hBreal : (0 : ℝ) < B.card := by exact_mod_cast hBcard
  have hcore := fordLemma51AnalyticCore_nonneg
    (k := k) (h := h) (g := g) (M₂ := M₂) hs hr hM hNreal ht B
  rw [fordLemma51MomentMajorant_eq_prefactors]
  rw [fordLemma51DisplayedCore_eq_separated hM]
  exact fordLemma51_prefactor_normalization
    hMreal hBreal hM₂real hcore hNreal hr hs

/-- Ford's Lemma 5.1 at a natural cutoff, in the displayed source
normalization.  The Taylor term retains the stronger `k+1` denominator. -/
theorem ford_exponential_lemma_5_1_natural
    {k h g r s M M₂ N R : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hM : 0 < M) (hM₂ : 1 ≤ M₂)
    {B : Finset ℕ} (hBne : B.Nonempty)
    (hBpos : ∀ b ∈ B, 1 ≤ b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (hMN : M * M₂ ≤ N) (hR : R ≤ 2 * N)
    {u t : ℝ} (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      2 * (M : ℝ) * (M₂ : ℝ) +
        t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) /
          (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) +
        (N : ℝ) * ((M₂ : ℝ) / B.card) ^ (1 / (r : ℝ)) *
          (fordLemma51DisplayedCore k h g r s M M₂ N B t) ^
            (1 / ((2 * r * s : ℕ) : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le (Nat.mul_pos hM hM₂) hMN
  have hraw := ford_exponential_lemma_5_1_raw
    (k := k) (h := h) (g := g) hr hs hM hM₂ hBne hBpos hBtop
      hMN hR hu huOne ht
  have hcentral := fordLemma51_centralTerm_eq_displayed
    (k := k) (h := h) (g := g) (r := r) (s := s)
    (M := M) (M₂ := M₂)
    (N := N) (by omega) (by omega) hM hM₂ hBne hN ht
  rw [hcentral] at hraw
  calc
    ‖fordShiftedExponentialSum N R u t‖ ≤
        (N : ℝ) * ((M₂ : ℝ) / B.card) ^ (1 / (r : ℝ)) *
            (fordLemma51DisplayedCore k h g r s M M₂ N B t) ^
              (1 / ((2 * r * s : ℕ) : ℝ)) +
          t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) /
            (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) +
          2 * (M : ℝ) * (M₂ : ℝ) := hraw
    _ = _ := by ring

/-- The source denominator `k` follows from the sharper Taylor denominator
`k+1`. -/
theorem ford_exponential_lemma_5_1_natural_source_denominator
    {k h g r s M M₂ N R : ℕ} (hk : 2 ≤ k)
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hM : 0 < M) (hM₂ : 1 ≤ M₂)
    {B : Finset ℕ} (hBne : B.Nonempty)
    (hBpos : ∀ b ∈ B, 1 ≤ b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (hMN : M * M₂ ≤ N) (hR : R ≤ 2 * N)
    {u t : ℝ} (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      2 * (M : ℝ) * (M₂ : ℝ) +
        t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) /
          ((k : ℝ) * (N : ℝ) ^ k) +
        (N : ℝ) * ((M₂ : ℝ) / B.card) ^ (1 / (r : ℝ)) *
          (fordLemma51DisplayedCore k h g r s M M₂ N B t) ^
            (1 / ((2 * r * s : ℕ) : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le (Nat.mul_pos hM hM₂) hMN
  have hbase : 0 ≤ t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) := by positivity
  have hdenNew : 0 < (k : ℝ) * (N : ℝ) ^ k := by positivity
  have hden : (k : ℝ) * (N : ℝ) ^ k ≤
      ((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k := by
    gcongr
    omega
  have herror :
      t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) /
          (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) ≤
        t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) /
          ((k : ℝ) * (N : ℝ) ^ k) :=
    div_le_div_of_nonneg_left hbase hdenNew hden
  refine (ford_exponential_lemma_5_1_natural
    (k := k) (h := h) (g := g)
    hr hs hM hM₂ hBne hBpos hBtop hMN hR hu huOne ht).trans ?_
  gcongr

#print axioms fordLemma51_prefactor_normalization
#print axioms fordLemma51W_nonneg
#print axioms fordLemma51AnalyticCore_nonneg
#print axioms fordLemma51DisplayedCore_eq_separated
#print axioms fordLemma51_centralTerm_eq_displayed
#print axioms ford_exponential_lemma_5_1_natural
#print axioms ford_exponential_lemma_5_1_natural_source_denominator

end

end GafniTao
