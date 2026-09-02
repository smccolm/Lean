import GafniTao.FordLemma63PhaseVolume
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Ford Lemma 6.3: top-coordinate spacing and box overlap

This file formalizes the one-dimensional geometric argument following
equation (6.9).  The source top coefficient is separated from its alternating
sign so that its monotonicity and consecutive spacing remain explicit.
-/

open Finset Set MeasureTheory
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The positive amplitude of Ford's degree-`k` coefficient. -/
def fordLemma63TopAmplitude (k : ℕ) (t x : ℝ) : ℝ :=
  t / (2 * Real.pi * k * x ^ k)

/-- Ford's literal degree-`k` coefficient `gamma_k(n)`. -/
def fordLemma63TopGamma (k n : ℕ) (u t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * fordLemma63TopAmplitude k t ((n : ℝ) + u)

theorem fordLemma63TopGamma_eq_fordTaylorGamma
    {k n : ℕ} {u t : ℝ} (hk : 1 ≤ k) :
    fordLemma63TopGamma k n u t =
      fordTaylorGamma t ((n : ℝ) + u) (k - 1) := by
  unfold fordLemma63TopGamma fordLemma63TopAmplitude fordTaylorGamma
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hkpred]
  have hkcast : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
    exact_mod_cast hkpred
  rw [hkcast]
  ring

theorem hasDerivAt_fordLemma63TopAmplitude
    {k : ℕ} (hk : 1 ≤ k) {t x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fordLemma63TopAmplitude k t)
      (-t / (2 * Real.pi * x ^ (k + 1))) x := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold fordLemma63TopAmplitude
  have hkR : ((q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : HasDerivAt (fun y : ℝ => y ^ (q + 1))
      (((q + 1 : ℕ) : ℝ) * x ^ q) x := by
    simpa using (hasDerivAt_id x).pow (q + 1)
  have hi := hp.inv (pow_ne_zero (q + 1) hx)
  have hc := HasDerivAt.const_mul (t / (2 * Real.pi * (q + 1))) hi
  have hderivEq :
      t / (2 * Real.pi * ((q + 1 : ℕ) : ℝ)) *
          (-((q + 1 : ℕ) : ℝ) * x ^ q / (x ^ (q + 1)) ^ 2) =
        -t / (2 * Real.pi * x ^ ((q + 1) + 1)) := by
    simp only [pow_succ]
    field_simp [Real.pi_ne_zero, hkR, hx]
  convert hc using 1
  · funext y
    have hinv : (fun z : ℝ => z ^ (q + 1))⁻¹ y = (y ^ (q + 1))⁻¹ := rfl
    rw [hinv]
    simp only [Nat.cast_succ, Nat.succ_eq_add_one]
    by_cases hy : y = 0
    · simp [hy]
    · field_simp [Real.pi_ne_zero, hkR, hy]
  · convert hderivEq.symm using 1
    · simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem fordLemma63TopAmplitude_consecutive_gap
    {k n N : ℕ} {u t : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hnUpper : n ≤ 2 * N - 2) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (ht : 0 ≤ t) :
    fordLemma63TopAmplitude k t ((n : ℝ) + u) -
        fordLemma63TopAmplitude k t (((n + 1 : ℕ) : ℝ) + u) ≥
      t / (2 * Real.pi * (2 * N : ℝ) ^ (k + 1)) := by
  let a : ℝ := (n : ℝ) + u
  let b : ℝ := ((n + 1 : ℕ) : ℝ) + u
  have hapos : 0 < a := by
    dsimp [a]
    positivity
  have hab : a < b := by
    dsimp [a, b]
    push_cast
    linarith
  have hbN : b ≤ 2 * (N : ℝ) := by
    dsimp [b]
    have htwoN : 2 ≤ 2 * N := by omega
    have hnTwo : n + 2 ≤ 2 * N := by omega
    have hcast : ((n + 2 : ℕ) : ℝ) ≤ (2 * N : ℕ) := by exact_mod_cast hnTwo
    push_cast at hcast
    have hn1cast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by norm_num
    rw [hn1cast]
    linarith
  have hcont : ContinuousOn (fordLemma63TopAmplitude k t) (Set.Icc a b) := by
    intro x hx
    exact (hasDerivAt_fordLemma63TopAmplitude hk
      (ne_of_gt (hapos.trans_le hx.1))).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fordLemma63TopAmplitude k t)
        (-t / (2 * Real.pi * x ^ (k + 1))) x := by
    intro x hx
    exact hasDerivAt_fordLemma63TopAmplitude hk
      (ne_of_gt (hapos.trans (hx.1)))
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope
      (fordLemma63TopAmplitude k t)
      (fun x : ℝ => -t / (2 * Real.pi * x ^ (k + 1))) hab hcont hderiv
  have hba : b - a = 1 := by
    dsimp [a, b]
    push_cast
    ring
  have hcb : c ≤ (2 * N : ℝ) := (le_of_lt hc.2).trans hbN
  have hcpos : 0 < c := hapos.trans hc.1
  have hpow : c ^ (k + 1) ≤ (2 * N : ℝ) ^ (k + 1) :=
    pow_le_pow_left₀ hcpos.le hcb _
  have hdenPos : 0 < 2 * Real.pi := by positivity
  have hrecip :
      t / (2 * Real.pi * (2 * N : ℝ) ^ (k + 1)) ≤
        t / (2 * Real.pi * c ^ (k + 1)) := by
    gcongr
  rw [hba, div_one] at hslope
  calc
    t / (2 * Real.pi * (2 * N : ℝ) ^ (k + 1)) ≤
        t / (2 * Real.pi * c ^ (k + 1)) := hrecip
    _ = -(-t / (2 * Real.pi * c ^ (k + 1))) := by ring
    _ = -(fordLemma63TopAmplitude k t b -
        fordLemma63TopAmplitude k t a) := congrArg Neg.neg hslope
    _ = fordLemma63TopAmplitude k t a -
        fordLemma63TopAmplitude k t b := by ring

theorem abs_fordLemma63TopGamma_consecutive_gap
    {k n N : ℕ} {u t : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hnUpper : n ≤ 2 * N - 2) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (ht : 0 ≤ t) :
    |fordLemma63TopGamma k n u t -
        fordLemma63TopGamma k (n + 1) u t| ≥
      t / (2 * Real.pi * (2 * N : ℝ) ^ (k + 1)) := by
  have hgap := fordLemma63TopAmplitude_consecutive_gap
    hk hN hnUpper hu0 hu1 ht
  unfold fordLemma63TopGamma
  rw [← mul_sub]
  rw [abs_mul, abs_neg_one_pow, one_mul]
  have hnonneg : 0 ≤
      fordLemma63TopAmplitude k t ((n : ℝ) + u) -
        fordLemma63TopAmplitude k t (((n + 1 : ℕ) : ℝ) + u) := by
    exact le_trans (by positivity) hgap
  rw [abs_of_nonneg hnonneg]
  exact hgap

/-- Telescoping form of a uniform consecutive-spacing estimate. -/
theorem ford_consecutive_gap_telescope
    {f : ℕ → ℝ} {d : ℝ} {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ n, a ≤ n → n < b → d ≤ f n - f (n + 1)) :
    (((b - a : ℕ) : ℝ) * d) ≤ f a - f b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases habEq : a = b + 1
      · subst a
        simp
      · have hab' : a ≤ b := by omega
        have hfirst := ih hab' (fun n han hnb => hstep n han (hnb.trans (Nat.lt_succ_self b)))
        have hlast := hstep b hab' (Nat.lt_succ_self b)
        have hsub : (b + 1 - a : ℕ) = (b - a) + 1 := by omega
        rw [hsub]
        push_cast
        calc
          (((b - a : ℕ) : ℝ) + 1) * d =
              (((b - a : ℕ) : ℝ) * d) + d := by ring
          _ ≤ (f a - f b) + (f b - f (b + 1)) := add_le_add hfirst hlast
          _ = f a - f (b + 1) := by ring

/-- A finite subset of a real interval, whose ordered images have spacing
`d`, has cardinality at most interval-length divided by `d`, plus one. -/
theorem ford_finset_card_le_of_ordered_spacing
    {S : Finset ℕ} {f : ℕ → ℝ} {β r d : ℝ}
    (hd : 0 < d) (hr : 0 ≤ r) (hS : ∀ n ∈ S, |f n - β| ≤ r)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a ≤ b →
      (((b - a : ℕ) : ℝ) * d) ≤ f a - f b) :
    (S.card : ℝ) ≤ 2 * r / d + 1 := by
  by_cases hEmpty : S = ∅
  · subst S
    simp
    positivity
  · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    let a := S.min' hne
    let b := S.max' hne
    have haMem : a ∈ S := S.min'_mem hne
    have hbMem : b ∈ S := S.max'_mem hne
    have hab : a ≤ b := S.min'_le_max' hne
    have hsubset : S ⊆ Finset.Icc a b := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨S.min'_le n hn, S.le_max' n hn⟩
    have hcardNat : S.card ≤ b + 1 - a := by
      have hmono := Finset.card_le_card hsubset
      simpa [Nat.card_Icc] using hmono
    have hcardNat' : S.card ≤ (b - a) + 1 := by
      omega
    have hcardReal : (S.card : ℝ) ≤ ((b - a : ℕ) : ℝ) + 1 := by
      exact_mod_cast hcardNat'
    have haBound := hS a haMem
    have hbBound := hS b hbMem
    rw [abs_le] at haBound hbBound
    have hspan : f a - f b ≤ 2 * r := by linarith
    have hseparation := hgap a haMem b hbMem hab
    have hdiffMul : ((b - a : ℕ) : ℝ) * d ≤ 2 * r :=
      hseparation.trans hspan
    have hdiff : ((b - a : ℕ) : ℝ) ≤ 2 * r / d :=
      (le_div_iff₀ hd).2 hdiffMul
    linarith

/-- The exact half-width used in Ford's top-coordinate overlap count. -/
def fordLemma63TopRadius (k M : ℕ) : ℝ :=
  1 / (2 * Real.pi * k ^ 2 * M ^ k)

/-- The non-periodic top-coordinate fiber over Ford's source index interval. -/
def fordLemma63TopFiber
    (N k M : ℕ) (u t β : ℝ) : Finset ℕ :=
  (Finset.Ioc N (2 * N - 1)).filter fun n =>
    |fordLemma63TopAmplitude k t ((n : ℝ) + u) - β| ≤
      fordLemma63TopRadius k M

theorem fordLemma63TopFiber_mem
    {N k M n : ℕ} {u t β : ℝ} :
    n ∈ fordLemma63TopFiber N k M u t β ↔
      N < n ∧ n ≤ 2 * N - 1 ∧
      |fordLemma63TopAmplitude k t ((n : ℝ) + u) - β| ≤
        fordLemma63TopRadius k M := by
  simp [fordLemma63TopFiber, and_assoc]

/-- Ford's literal real overlap constant. -/
def fordLemma63W (N k M : ℕ) (t : ℝ) : ℝ :=
  2 ^ (k + 2) * (N : ℝ) ^ (k + 1) /
      ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) + 1

theorem fordLemma63TopFiber_card_le_W
    {N k M : ℕ} {u t β : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (ht : 0 < t) :
    ((fordLemma63TopFiber N k M u t β).card : ℝ) ≤
      fordLemma63W N k M t := by
  let d : ℝ := t / (2 * Real.pi * (2 * N : ℝ) ^ (k + 1))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hr : 0 ≤ fordLemma63TopRadius k M := by
    unfold fordLemma63TopRadius
    positivity
  have hgap : ∀ a ∈ fordLemma63TopFiber N k M u t β,
      ∀ b ∈ fordLemma63TopFiber N k M u t β, a ≤ b →
        (((b - a : ℕ) : ℝ) * d) ≤
          fordLemma63TopAmplitude k t ((a : ℝ) + u) -
            fordLemma63TopAmplitude k t ((b : ℝ) + u) := by
    intro a ha b hb hab
    have haRange := fordLemma63TopFiber_mem.mp ha
    have hbRange := fordLemma63TopFiber_mem.mp hb
    apply ford_consecutive_gap_telescope hab
    intro n han hnb
    have hnUpper : n ≤ 2 * N - 2 := by omega
    exact fordLemma63TopAmplitude_consecutive_gap
      hk hN hnUpper hu0 hu1 ht.le
  have hcard := ford_finset_card_le_of_ordered_spacing
    (S := fordLemma63TopFiber N k M u t β)
    (f := fun n => fordLemma63TopAmplitude k t ((n : ℝ) + u))
    (β := β) (r := fordLemma63TopRadius k M) (d := d) hd hr
    (fun n hn => (fordLemma63TopFiber_mem.mp hn).2.2)
    hgap
  calc
    ((fordLemma63TopFiber N k M u t β).card : ℝ) ≤
        2 * fordLemma63TopRadius k M / d + 1 := hcard
    _ = fordLemma63W N k M t := by
      unfold fordLemma63TopRadius fordLemma63W d
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have htR : (0 : ℝ) < t := ht
      field_simp [Real.pi_ne_zero, hkR.ne', hNR.ne', htR.ne']
      ring

theorem fordLemma63TopAmplitude_le
    {N k n : ℕ} {u t : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) (hn : N < n)
    (hu0 : 0 < u)
    (htN : t ≤ (N : ℝ) ^ k) :
    fordLemma63TopAmplitude k t ((n : ℝ) + u) ≤
      1 / (2 * Real.pi * k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnx : (N : ℝ) ≤ (n : ℝ) + u := by
    have hcast : (N : ℝ) < n := by exact_mod_cast hn
    linarith
  have hx : 0 < (n : ℝ) + u := hNR.trans_le hnx
  have hpow : (N : ℝ) ^ k ≤ ((n : ℝ) + u) ^ k :=
    pow_le_pow_left₀ hNR.le hnx _
  unfold fordLemma63TopAmplitude
  calc
    t / (2 * Real.pi * (k : ℝ) * ((n : ℝ) + u) ^ k) ≤
        (N : ℝ) ^ k /
          (2 * Real.pi * (k : ℝ) * ((n : ℝ) + u) ^ k) := by
      gcongr
    _ ≤ (N : ℝ) ^ k /
          (2 * Real.pi * (k : ℝ) * (N : ℝ) ^ k) := by
      have hcoeff : 0 < 2 * Real.pi * (k : ℝ) := by positivity
      gcongr
    _ = 1 / (2 * Real.pi * k) := by
      field_simp [Real.pi_ne_zero, hkR.ne', hNR.ne']

theorem abs_fordLemma63TopGamma_sub_lt_half
    {N k a b : ℕ} {u t : ℝ}
    (hk : 2 ≤ k) (hN : 1 ≤ N)
    (ha : a ∈ Finset.Ioc N (2 * N - 1))
    (hb : b ∈ Finset.Ioc N (2 * N - 1))
    (hu0 : 0 < u) (ht : 0 ≤ t) (htN : t ≤ (N : ℝ) ^ k) :
    |fordLemma63TopGamma k a u t - fordLemma63TopGamma k b u t| < 1 / 2 := by
  have hk1 : 1 ≤ k := hk.trans' (by omega)
  have hAa := fordLemma63TopAmplitude_le hk1 hN
    (Finset.mem_Ioc.mp ha).1 hu0 htN
  have hAb := fordLemma63TopAmplitude_le hk1 hN
    (Finset.mem_Ioc.mp hb).1 hu0 htN
  have hAanonneg : 0 ≤ fordLemma63TopAmplitude k t ((a : ℝ) + u) := by
    unfold fordLemma63TopAmplitude
    positivity
  have hAbnonneg : 0 ≤ fordLemma63TopAmplitude k t ((b : ℝ) + u) := by
    unfold fordLemma63TopAmplitude
    positivity
  have hgammaA : |fordLemma63TopGamma k a u t| =
      fordLemma63TopAmplitude k t ((a : ℝ) + u) := by
    unfold fordLemma63TopGamma
    rw [abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg hAanonneg]
  have hgammaB : |fordLemma63TopGamma k b u t| =
      fordLemma63TopAmplitude k t ((b : ℝ) + u) := by
    unfold fordLemma63TopGamma
    rw [abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg hAbnonneg]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsmall : 2 * (1 / (2 * Real.pi * (k : ℝ))) < 1 / 2 := by
    have hden : 4 < 2 * Real.pi * (k : ℝ) := by nlinarith
    rw [show 2 * (1 / (2 * Real.pi * (k : ℝ))) =
      2 / (2 * Real.pi * (k : ℝ)) by ring]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi * (k : ℝ))).2
    nlinarith
  calc
    |fordLemma63TopGamma k a u t - fordLemma63TopGamma k b u t| ≤
        |fordLemma63TopGamma k a u t| +
          |fordLemma63TopGamma k b u t| := abs_sub _ _
    _ = fordLemma63TopAmplitude k t ((a : ℝ) + u) +
        fordLemma63TopAmplitude k t ((b : ℝ) + u) := by rw [hgammaA, hgammaB]
    _ ≤ 2 * (1 / (2 * Real.pi * (k : ℝ))) := by linarith
    _ < 1 / 2 := hsmall

theorem fordLemma63_twice_topRadius_lt_half
    {k M : ℕ} (hk : 2 ≤ k) (hM : 1 ≤ M) :
    2 * fordLemma63TopRadius k M < (1 : ℝ) / 2 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpow : (1 : ℝ) ≤ (M : ℝ) ^ k := one_le_pow₀ hMR
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  unfold fordLemma63TopRadius
  have hden : 4 < Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ k := by
    have hkSq : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [sq_nonneg ((k : ℝ) - 2)]
    have hprod : (4 : ℝ) ≤ (k : ℝ) ^ 2 * (M : ℝ) ^ k := by
      nlinarith [mul_le_mul hkSq hMpow (by positivity : (0 : ℝ) ≤ 1)
        (sq_nonneg (k : ℝ))]
    calc
      (4 : ℝ) < Real.pi * 4 := by nlinarith
      _ ≤ Real.pi * ((k : ℝ) ^ 2 * (M : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hprod Real.pi_pos.le
      _ = Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ k := by ring
  rw [show 2 * (1 / (2 * Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ k)) =
    1 / (Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ k) by ring]
  apply (div_lt_iff₀ (by positivity :
    0 < Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ k)).2
  nlinarith

/-- If two top-coordinate boxes overlap modulo integer translation, Ford's
`< 1/2` drift and radius bounds force the integer translates to coincide. -/
theorem fordLemma63_integer_translate_unique
    {g₁ g₂ β r : ℝ} {z₁ z₂ : ℤ}
    (hg : |g₁ - g₂| < 1 / 2) (hr : 2 * r < 1 / 2)
    (h₁ : |g₁ - (β + z₁)| ≤ r) (h₂ : |g₂ - (β + z₂)| ≤ r) :
    z₁ = z₂ := by
  have hid : ((z₁ - z₂ : ℤ) : ℝ) =
      -(g₁ - (β + (z₁ : ℝ))) + (g₁ - g₂) +
        (g₂ - (β + (z₂ : ℝ))) := by
    push_cast
    ring
  have hzabs : |((z₁ - z₂ : ℤ) : ℝ)| < 1 := by
    rw [hid]
    calc
      |-(g₁ - (β + (z₁ : ℝ))) + (g₁ - g₂) +
          (g₂ - (β + (z₂ : ℝ)))| ≤
          |g₁ - (β + (z₁ : ℝ))| + |g₁ - g₂| +
            |g₂ - (β + (z₂ : ℝ))| := by
        calc
          |_ + _| ≤ |-(g₁ - (β + (z₁ : ℝ))) + (g₁ - g₂)| +
              |g₂ - (β + (z₂ : ℝ))| := abs_add_le _ _
          _ ≤ (|g₁ - (β + (z₁ : ℝ))| + |g₁ - g₂|) +
              |g₂ - (β + (z₂ : ℝ))| := by
            gcongr
            simpa only [abs_neg] using
              (abs_add_le (-(g₁ - (β + (z₁ : ℝ)))) (g₁ - g₂))
      _ < 1 := by linarith
  have hzInt : |z₁ - z₂| < (1 : ℤ) := by
    rw [← Int.cast_lt (R := ℝ), Int.cast_abs]
    simpa using hzabs
  have hzZero : z₁ - z₂ = 0 := Int.abs_lt_one_iff.mp hzInt
  exact sub_eq_zero.mp hzZero

/-- The actual top-coordinate fiber on the unit torus. -/
def fordLemma63PeriodicTopFiber
    (N k M : ℕ) (u t β : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc N (2 * N - 1)).filter fun n =>
    ∃ z : ℤ, |fordLemma63TopGamma k n u t - (β + z)| ≤
      fordLemma63TopRadius k M

theorem fordLemma63PeriodicTopFiber_mem
    {N k M n : ℕ} {u t β : ℝ} :
    n ∈ fordLemma63PeriodicTopFiber N k M u t β ↔
      N < n ∧ n ≤ 2 * N - 1 ∧
      ∃ z : ℤ, |fordLemma63TopGamma k n u t - (β + z)| ≤
        fordLemma63TopRadius k M := by
  simp [fordLemma63PeriodicTopFiber, and_assoc]

theorem fordLemma63PeriodicTopFiber_card_le_W
    {N k M : ℕ} {u t β : ℝ}
    (hk : 2 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k) :
    ((fordLemma63PeriodicTopFiber N k M u t β).card : ℝ) ≤
      fordLemma63W N k M t := by
  classical
  let S := fordLemma63PeriodicTopFiber N k M u t β
  by_cases hEmpty : S = ∅
  · subst S
    rw [hEmpty]
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold fordLemma63W
    positivity
  · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    let a := S.min' hne
    have haS : a ∈ S := S.min'_mem hne
    have haPeriodic : a ∈ fordLemma63PeriodicTopFiber N k M u t β := haS
    obtain ⟨z₀, hz₀⟩ := (fordLemma63PeriodicTopFiber_mem.mp haPeriodic).2.2
    let ε : ℝ := (-1 : ℝ) ^ k
    let βA : ℝ := ε * (β + (z₀ : ℝ))
    have hεabs : |ε| = 1 := by
      dsimp [ε]
      exact abs_neg_one_pow k
    have hεsq : ε * ε = 1 := by
      dsimp [ε]
      rw [← pow_add]
      simp
    have hr := fordLemma63_twice_topRadius_lt_half hk hM
    have hsubset : S ⊆ fordLemma63TopFiber N k M u t βA := by
      intro n hnS
      have hnPeriodic : n ∈ fordLemma63PeriodicTopFiber N k M u t β := hnS
      have hnData := fordLemma63PeriodicTopFiber_mem.mp hnPeriodic
      obtain ⟨z, hz⟩ := hnData.2.2
      have haRange : a ∈ Finset.Ioc N (2 * N - 1) := by
        exact Finset.mem_Ioc.mpr
          ⟨(fordLemma63PeriodicTopFiber_mem.mp haPeriodic).1,
            (fordLemma63PeriodicTopFiber_mem.mp haPeriodic).2.1⟩
      have hnRange : n ∈ Finset.Ioc N (2 * N - 1) := by
        exact Finset.mem_Ioc.mpr ⟨hnData.1, hnData.2.1⟩
      have hgamma := abs_fordLemma63TopGamma_sub_lt_half
        hk hN haRange hnRange hu0 ht.le htN
      have hzEq : z₀ = z := fordLemma63_integer_translate_unique
        hgamma hr hz₀ hz
      subst z
      apply fordLemma63TopFiber_mem.mpr
      refine ⟨hnData.1, hnData.2.1, ?_⟩
      have herrEq :
          fordLemma63TopAmplitude k t ((n : ℝ) + u) - βA =
            ε * (fordLemma63TopGamma k n u t - (β + (z₀ : ℝ))) := by
        unfold fordLemma63TopGamma
        dsimp [βA]
        change fordLemma63TopAmplitude k t ((n : ℝ) + u) -
            ε * (β + (z₀ : ℝ)) =
          ε * (ε * fordLemma63TopAmplitude k t ((n : ℝ) + u) -
            (β + (z₀ : ℝ)))
        rw [mul_sub, ← mul_assoc, hεsq, one_mul]
      rw [herrEq, abs_mul, hεabs, one_mul]
      exact hz
    have hcardNat := Finset.card_le_card hsubset
    have hcardReal : (S.card : ℝ) ≤
        ((fordLemma63TopFiber N k M u t βA).card : ℝ) := by
      exact_mod_cast hcardNat
    exact hcardReal.trans
      (fordLemma63TopFiber_card_le_W (by omega) hN hu0 hu1 ht)

#print axioms hasDerivAt_fordLemma63TopAmplitude
#print axioms fordLemma63TopAmplitude_consecutive_gap
#print axioms abs_fordLemma63TopGamma_consecutive_gap
#print axioms ford_finset_card_le_of_ordered_spacing
#print axioms fordLemma63TopFiber_card_le_W
#print axioms abs_fordLemma63TopGamma_sub_lt_half
#print axioms fordLemma63_integer_translate_unique
#print axioms fordLemma63PeriodicTopFiber_card_le_W

end

end GafniTao
