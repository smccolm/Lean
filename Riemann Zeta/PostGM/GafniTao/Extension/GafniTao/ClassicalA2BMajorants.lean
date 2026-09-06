import GafniTao.ClassicalA2BOuter
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Algebraic majorants for the finite `A²B` estimate

The exact B-process expression is reduced here to four homogeneous terms.
This is an inequality about the previously proved finite majorant, not a new
analytic assumption.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem one_div_sqrt_nat_le_telescoping (n : ℕ) :
    1 / Real.sqrt (n : ℝ) ≤
      2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    let a : ℝ := Real.sqrt (n : ℝ)
    let b : ℝ := Real.sqrt ((n - 1 : ℕ) : ℝ)
    have ha : 0 < a := by
      dsimp only [a]
      exact Real.sqrt_pos.2 (by exact_mod_cast hnPos)
    have hb : 0 ≤ b := Real.sqrt_nonneg _
    have hab : b ≤ a := by
      dsimp only [a, b]
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Nat.sub_le n 1)
    have haSq : a ^ 2 = (n : ℝ) := by
      dsimp only [a]
      exact Real.sq_sqrt (by positivity)
    have hbSq : b ^ 2 = ((n - 1 : ℕ) : ℝ) := by
      dsimp only [b]
      exact Real.sq_sqrt (by positivity)
    have hcastSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn)]
      norm_num
    have hone : (a - b) * (a + b) = 1 := by
      calc
        (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
        _ = 1 := by rw [haSq, hbSq, hcastSub]; ring
    have hfactor : a + b ≤ 2 * a := by linarith
    have hdiff : 0 ≤ a - b := sub_nonneg.mpr hab
    have hmul := mul_le_mul_of_nonneg_left hfactor hdiff
    rw [← mul_assoc, hone] at hmul
    rw [div_le_iff₀ ha]
    dsimp only [a, b]
    nlinarith

theorem sum_range_sqrt_telescoping (H : ℕ) :
    ∑ n ∈ Finset.range (H + 1),
        (Real.sqrt (n : ℝ) - Real.sqrt ((n - 1 : ℕ) : ℝ)) =
      Real.sqrt (H : ℝ) := by
  induction H with
  | zero => norm_num
  | succ H ih =>
      rw [show H + 1 + 1 = (H + 1) + 1 by omega,
        Finset.sum_range_succ]
      rw [ih]
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

theorem sum_Icc_one_div_sqrt_le_two_sqrt (H : ℕ) :
    ∑ n ∈ Finset.Icc 1 (H - 1), 1 / Real.sqrt (n : ℝ) ≤
      2 * Real.sqrt (H : ℝ) := by
  have hsubset : Finset.Icc 1 (H - 1) ⊆ Finset.range (H + 1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact Finset.mem_range.mpr (by omega)
  calc
    ∑ n ∈ Finset.Icc 1 (H - 1), 1 / Real.sqrt n ≤
        ∑ n ∈ Finset.range (H + 1), 1 / Real.sqrt (n : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _hn _ => by positivity)
    _ ≤ ∑ n ∈ Finset.range (H + 1),
        2 * (Real.sqrt (n : ℝ) -
          Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact one_div_sqrt_nat_le_telescoping n
    _ = 2 * Real.sqrt H := by
      rw [← Finset.mul_sum, sum_range_sqrt_telescoping]

theorem sqrt_div_sixteen {q : ℝ} (hq : 0 ≤ q) :
    Real.sqrt (q / 16) = Real.sqrt q / 4 := by
  have hleft : 0 ≤ Real.sqrt (q / 16) := Real.sqrt_nonneg _
  have hright : 0 ≤ Real.sqrt q / 4 := by positivity
  have hleftSq : Real.sqrt (q / 16) ^ 2 = q / 16 := by
    rw [Real.sq_sqrt]
    positivity
  have hrightSq : (Real.sqrt q / 4) ^ 2 = q / 16 := by
    rw [div_pow, Real.sq_sqrt hq]
    norm_num
  nlinarith

theorem logarithmicSecondCorrelationBound_le_homogeneous
    (t A : ℝ) (N r s : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s) :
    logarithmicSecondCorrelationBound t A N r s ≤
      240 *
        ((N : ℝ) * Real.sqrt (t * r * s / A ^ 4) +
          (N : ℝ) * (t * r * s / A ^ 4) +
          1 / Real.sqrt (t * r * s / A ^ 4) + 1) := by
  let q : ℝ := t * r * s / A ^ 4
  have hq : 0 < q := by dsimp only [q]; positivity
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsqrtqSq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hsqrt16 : Real.sqrt (q / 16) = Real.sqrt q / 4 :=
    sqrt_div_sixteen hq.le
  let M := N - s - 1
  have hMN : (M : ℝ) ≤ N := by
    exact_mod_cast (Nat.sub_le N (s + 1))
  have hfirst :
      (M : ℝ) * (32 * q) / (2 * Real.pi) + 2 ≤
        6 * (N : ℝ) * q + 2 := by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hden : 0 < 2 * Real.pi := by positivity
    rw [add_le_add_iff_right]
    have hMq : (M : ℝ) * q ≤ (N : ℝ) * q :=
      mul_le_mul_of_nonneg_right hMN hq.le
    have hcoef : 32 / (2 * Real.pi) ≤ (6 : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith
    calc
      (M : ℝ) * (32 * q) / (2 * Real.pi) =
          ((M : ℝ) * q) * (32 / (2 * Real.pi)) := by ring
      _ ≤ ((N : ℝ) * q) * 6 :=
        mul_le_mul hMq hcoef (by positivity) (by positivity)
      _ = 6 * (N : ℝ) * q := by ring
  have hsecond :
      2 * Real.pi / Real.sqrt (q / 16) +
          2 * (Real.sqrt (q / 16) / (q / 16) + 1) ≤
        40 / Real.sqrt q + 2 := by
    rw [hsqrt16]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hqNe : q ≠ 0 := hq.ne'
    have hsqrtNe : Real.sqrt q ≠ 0 := hsqrtq.ne'
    field_simp [hqNe, hsqrtNe]
    nlinarith
  have hfirstNonneg :
      0 ≤ (M : ℝ) * (32 * q) / (2 * Real.pi) + 2 := by positivity
  have hsecondNonneg :
      0 ≤ 2 * Real.pi / Real.sqrt (q / 16) +
          2 * (Real.sqrt (q / 16) / (q / 16) + 1) := by positivity
  have hproduct := mul_le_mul hfirst hsecond hsecondNonneg
    (by positivity : 0 ≤ 6 * (N : ℝ) * q + 2)
  have hsimple :
      (6 * (N : ℝ) * q + 2) * (40 / Real.sqrt q + 2) ≤
        240 * ((N : ℝ) * Real.sqrt q +
          (N : ℝ) * q + 1 / Real.sqrt q + 1) := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have honeSqrt : 0 ≤ 1 / Real.sqrt q := by positivity
    field_simp [hsqrtq.ne']
    nlinarith
  have hqSixteen :
      t * (r : ℝ) * (s : ℝ) / (16 * A ^ 4) = q / 16 := by
    dsimp only [q]
    field_simp [hA.ne']
  unfold logarithmicSecondCorrelationBound
  dsimp only
  rw [show 32 * t * (r : ℝ) * (s : ℝ) / A ^ 4 =
      32 * (t * (r : ℝ) * (s : ℝ) / A ^ 4) by ring]
  rw [hqSixteen]
  simpa only [q, M] using hproduct.trans hsimple

theorem logarithmicSecondCorrelationBound_le_simple
    (t A : ℝ) (N r s : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hsmall : t * (r : ℝ) * (s : ℝ) / A ^ 4 ≤ 1) :
    logarithmicSecondCorrelationBound t A N r s ≤
      480 * ((N : ℝ) * Real.sqrt (t * r * s / A ^ 4) +
        1 / Real.sqrt (t * r * s / A ^ 4)) := by
  let q : ℝ := t * r * s / A ^ 4
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqOne : q ≤ 1 := by simpa only [q] using hsmall
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsqrtOne : Real.sqrt q ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hqOne
  have hqSqrt : q ≤ Real.sqrt q := by
    have hsq := Real.sq_sqrt hq.le
    nlinarith
  have honeInv : 1 ≤ 1 / Real.sqrt q := by
    rw [le_div_iff₀ hsqrt]
    simpa using hsqrtOne
  have hraw := logarithmicSecondCorrelationBound_le_homogeneous
    t A N r s ht hA hr hs
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have htargetNonneg :
      0 ≤ (N : ℝ) * Real.sqrt q + 1 / Real.sqrt q := by positivity
  calc
    logarithmicSecondCorrelationBound t A N r s ≤
        240 * ((N : ℝ) * Real.sqrt q +
          (N : ℝ) * q + 1 / Real.sqrt q + 1) := by
      simpa only [q] using hraw
    _ ≤ 480 * ((N : ℝ) * Real.sqrt q + 1 / Real.sqrt q) := by
      have hNq := mul_le_mul_of_nonneg_left hqSqrt hN
      nlinarith
    _ = 480 * ((N : ℝ) * Real.sqrt (t * r * s / A ^ 4) +
        1 / Real.sqrt (t * r * s / A ^ 4)) := by rfl

theorem sum_logarithmicSecondCorrelationBound_le
    (t A : ℝ) (N r H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (hsmall : t * (r : ℝ) * (H : ℝ) / A ^ 4 ≤ 1) :
    ∑ s ∈ Finset.Icc 1 (H - 1),
        logarithmicSecondCorrelationBound t A N r s ≤
      480 * ((N : ℝ) * H *
          Real.sqrt (t * r * H / A ^ 4) +
        2 * Real.sqrt (H : ℝ) /
          Real.sqrt (t * r / A ^ 4)) := by
  let q₀ : ℝ := t * r / A ^ 4
  have hq₀ : 0 < q₀ := by dsimp only [q₀]; positivity
  have hsqrtq₀ : 0 < Real.sqrt q₀ := Real.sqrt_pos.2 hq₀
  have hqHEq : t * (r : ℝ) * (H : ℝ) / A ^ 4 = q₀ * H := by
    dsimp only [q₀]
    ring
  let S := Finset.Icc 1 (H - 1)
  have hcard : (S.card : ℝ) ≤ H := by
    have hsubset : S ⊆ Finset.range H := by
      intro s hs
      exact Finset.mem_range.mpr (by
        have := Finset.mem_Icc.mp hs
        omega)
    have hcardNat : S.card ≤ H := by
      simpa using Finset.card_le_card hsubset
    exact_mod_cast hcardNat
  have hpoint : ∀ s ∈ S,
      logarithmicSecondCorrelationBound t A N r s ≤
        480 * ((N : ℝ) * Real.sqrt (q₀ * H) +
          (1 / Real.sqrt q₀) * (1 / Real.sqrt (s : ℝ))) := by
    intro s hs
    have hsData := Finset.mem_Icc.mp hs
    have hsPos : 0 < s := by omega
    have hsH : s ≤ H := by omega
    have hqEq : t * (r : ℝ) * (s : ℝ) / A ^ 4 = q₀ * s := by
      dsimp only [q₀]
      ring
    have hsmallS : t * (r : ℝ) * (s : ℝ) / A ^ 4 ≤ 1 := by
      calc
        t * (r : ℝ) * (s : ℝ) / A ^ 4 ≤
            t * (r : ℝ) * (H : ℝ) / A ^ 4 := by gcongr
        _ ≤ 1 := hsmall
    have hbase := logarithmicSecondCorrelationBound_le_simple
      t A N r s ht hA hr hsPos hsmallS
    have hsqrtLe : Real.sqrt (q₀ * s) ≤ Real.sqrt (q₀ * H) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsH) hq₀.le
    have hsqrtMul : Real.sqrt (q₀ * s) =
        Real.sqrt q₀ * Real.sqrt (s : ℝ) := by
      rw [Real.sqrt_mul hq₀.le]
    have hsqrtSPos : 0 < Real.sqrt (s : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hsPos)
    have hinvEq : 1 / Real.sqrt (q₀ * s) =
        (1 / Real.sqrt q₀) * (1 / Real.sqrt (s : ℝ)) := by
      rw [hsqrtMul]
      field_simp [hsqrtq₀.ne', hsqrtSPos.ne']
    rw [hqEq] at hbase
    exact hbase.trans (by
      rw [hinvEq]
      gcongr)
  calc
    ∑ s ∈ Finset.Icc 1 (H - 1),
        logarithmicSecondCorrelationBound t A N r s ≤
      ∑ s ∈ S, 480 * ((N : ℝ) * Real.sqrt (q₀ * H) +
        (1 / Real.sqrt q₀) * (1 / Real.sqrt (s : ℝ))) := by
          simpa only [S] using Finset.sum_le_sum hpoint
    _ = 480 * ((S.card : ℝ) *
          ((N : ℝ) * Real.sqrt (q₀ * H)) +
        (1 / Real.sqrt q₀) *
          (∑ s ∈ S, 1 / Real.sqrt (s : ℝ))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      · simp
      · rw [← Finset.mul_sum]
    _ ≤ 480 * ((H : ℝ) *
          ((N : ℝ) * Real.sqrt (q₀ * H)) +
        (1 / Real.sqrt q₀) * (2 * Real.sqrt (H : ℝ))) := by
      have hsum : ∑ s ∈ S, 1 / Real.sqrt (s : ℝ) ≤
          2 * Real.sqrt (H : ℝ) := by
        simpa only [S] using sum_Icc_one_div_sqrt_le_two_sqrt H
      gcongr
    _ = 480 * ((N : ℝ) * H *
          Real.sqrt (t * r * H / A ^ 4) +
        2 * Real.sqrt (H : ℝ) / Real.sqrt (t * r / A ^ 4)) := by
      rw [hqHEq, show t * (r : ℝ) / A ^ 4 = q₀ by rfl]
      ring

theorem logarithmicDifferenceA2Majorant_le_simple
    (t A : ℝ) (r N H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hH : H ≤ N)
    (hsmall : t * (r : ℝ) * (H : ℝ) / A ^ 4 ≤ 1) :
    logarithmicDifferenceA2Majorant t A r N H ≤
      2 * (N : ℝ) * H *
        ((N : ℝ) + 960 *
          ((N : ℝ) * H * Real.sqrt (t * r * H / A ^ 4) +
            2 * Real.sqrt (H : ℝ) /
              Real.sqrt (t * r / A ^ 4))) := by
  have hsum := sum_logarithmicSecondCorrelationBound_le
    t A N r H ht hA hr hsmall
  have hNH : ((N + H : ℕ) : ℝ) ≤ 2 * N := by
    norm_num
    exact_mod_cast (by omega : N + H ≤ 2 * N)
  have hinnerNonneg :
      0 ≤ (H : ℝ) * N + (H : ℝ) *
        (2 * ∑ s ∈ Finset.Icc 1 (H - 1),
          logarithmicSecondCorrelationBound t A N r s) := by
    apply add_nonneg
    · positivity
    · apply mul_nonneg (Nat.cast_nonneg H)
      apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg fun s _ =>
        logarithmicSecondCorrelationBound_nonneg t A N r s ht hA hr
  unfold logarithmicDifferenceA2Majorant
  calc
    ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N + (H : ℝ) *
          (2 * ∑ s ∈ Finset.Icc 1 (H - 1),
            logarithmicSecondCorrelationBound t A N r s)) ≤
      (2 * (N : ℝ)) *
        ((H : ℝ) * N + (H : ℝ) *
          (2 * ∑ s ∈ Finset.Icc 1 (H - 1),
            logarithmicSecondCorrelationBound t A N r s)) :=
      mul_le_mul_of_nonneg_right hNH hinnerNonneg
    _ ≤ (2 * (N : ℝ)) *
        ((H : ℝ) * N + (H : ℝ) *
          (2 * (480 * ((N : ℝ) * H *
            Real.sqrt (t * r * H / A ^ 4) +
            2 * Real.sqrt (H : ℝ) /
              Real.sqrt (t * r / A ^ 4))))) := by
      gcongr
    _ = 2 * (N : ℝ) * H *
        ((N : ℝ) + 960 *
          ((N : ℝ) * H * Real.sqrt (t * r * H / A ^ 4) +
            2 * Real.sqrt (H : ℝ) /
              Real.sqrt (t * r / A ^ 4))) := by ring

/-- A three-term square-root majorant, before optimizing the two A-process
shift lengths.  Keeping these three terms separate is what permits the outer
sum over the first shift to retain its `r^(-1/4)` saving. -/
noncomputable def logarithmicDifferenceA2RawBound
    (t A : ℝ) (r N H : ℕ) : ℝ :=
  Real.sqrt (2 * (N : ℝ) ^ 2 * H) / H +
    Real.sqrt (1920 * (N : ℝ) ^ 2 * H ^ 2 *
      Real.sqrt (t * r * H / A ^ 4)) / H +
    Real.sqrt (3840 * (N : ℝ) * H * Real.sqrt (H : ℝ) /
      Real.sqrt (t * r / A ^ 4)) / H

private theorem sqrt_three_sum_le
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  have habc : 0 ≤ a + b + c := by positivity
  have hsqa := Real.sq_sqrt ha
  have hsqb := Real.sq_sqrt hb
  have hsqc := Real.sq_sqrt hc
  have hsa := Real.sqrt_nonneg a
  have hsb := Real.sqrt_nonneg b
  have hsc := Real.sqrt_nonneg c
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith

theorem logarithmicDifferenceA2Bound_le_raw
    (t A : ℝ) (r N H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hHpos : 0 < H)
    (hH : H ≤ N)
    (hsmall : t * (r : ℝ) * (H : ℝ) / A ^ 4 ≤ 1) :
    logarithmicDifferenceA2Bound t A r N H ≤
      logarithmicDifferenceA2RawBound t A r N H := by
  let a : ℝ := 2 * (N : ℝ) ^ 2 * H
  let b : ℝ := 1920 * (N : ℝ) ^ 2 * H ^ 2 *
    Real.sqrt (t * r * H / A ^ 4)
  let c : ℝ := 3840 * (N : ℝ) * H * Real.sqrt (H : ℝ) /
    Real.sqrt (t * r / A ^ 4)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hq : 0 < t * (r : ℝ) / A ^ 4 := by positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hmaj := logarithmicDifferenceA2Majorant_le_simple
    t A r N H ht hA hr hH hsmall
  have hrewrite :
      2 * (N : ℝ) * H *
          ((N : ℝ) + 960 *
            ((N : ℝ) * H * Real.sqrt (t * r * H / A ^ 4) +
              2 * Real.sqrt (H : ℝ) /
                Real.sqrt (t * r / A ^ 4))) = a + b + c := by
    dsimp only [a, b, c]
    ring
  rw [hrewrite] at hmaj
  unfold logarithmicDifferenceA2Bound logarithmicDifferenceA2RawBound
  change Real.sqrt (logarithmicDifferenceA2Majorant t A r N H) / H ≤
    Real.sqrt a / H + Real.sqrt b / H + Real.sqrt c / H
  calc
    Real.sqrt (logarithmicDifferenceA2Majorant t A r N H) / H ≤
        Real.sqrt (a + b + c) / H := by
      gcongr
    _ ≤ (Real.sqrt a + Real.sqrt b + Real.sqrt c) / H := by
      gcongr
      exact sqrt_three_sum_le ha hb hc
    _ = Real.sqrt a / H + Real.sqrt b / H + Real.sqrt c / H := by ring

theorem logarithmicA2BCorrelationBound_le_raw
    (t A : ℝ) (N H₁ H₂ r : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (hrHigh : r ≤ H₁ - 1)
    (hH₂pos : 0 < H₂) (hH₂ : H₂ ≤ N - (H₁ - 1))
    (hsmall : t * (r : ℝ) * (H₂ : ℝ) / A ^ 4 ≤ 1) :
    logarithmicA2BCorrelationBound t A N H₂ r ≤
      logarithmicDifferenceA2RawBound t A r (N - r) H₂ := by
  unfold logarithmicA2BCorrelationBound
  apply logarithmicDifferenceA2Bound_le_raw t A r (N - r) H₂
    ht hA hr hH₂pos
  · omega
  · exact hsmall

/-- The full outer A-process with every inner square-root contribution still
visible under the finite first-shift sum. -/
theorem logarithmic_weyl_A2B_process_raw
    (t A : ℝ) (N H₁ H₂ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂)
    (hH₂ : H₂ ≤ N - (H₁ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) / A ^ 4 ≤ 1) :
    (H₁ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerLogarithmicTerm t A n‖ ^ 2 ≤
      ((N + H₁ : ℕ) : ℝ) *
        ((H₁ : ℝ) * N + (H₁ : ℝ) *
          (2 * ∑ r ∈ Finset.Icc 1 (H₁ - 1),
            logarithmicDifferenceA2RawBound t A r (N - r) H₂)) := by
  have hbase := logarithmic_weyl_A2B_process
    t A N H₁ H₂ ht hA hNA hH₁ hH₂pos hH₂
  refine hbase.trans ?_
  have hpref : 0 ≤ ((N + H₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hH₁nonneg : 0 ≤ (H₁ : ℝ) := Nat.cast_nonneg _
  have hsum :
      ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicA2BCorrelationBound t A N H₂ r ≤
        ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicDifferenceA2RawBound t A r (N - r) H₂ := by
    apply Finset.sum_le_sum
    intro r hrMem
    have hrData := Finset.mem_Icc.mp hrMem
    have hrPos : 0 < r := by omega
    have hrHigh : r ≤ H₁ - 1 := hrData.2
    have hsmallR : t * (r : ℝ) * (H₂ : ℝ) / A ^ 4 ≤ 1 := by
      calc
        t * (r : ℝ) * (H₂ : ℝ) / A ^ 4 ≤
            t * (H₁ : ℝ) * (H₂ : ℝ) / A ^ 4 := by
          gcongr
          exact_mod_cast (hrHigh.trans (Nat.sub_le H₁ 1))
        _ ≤ 1 := hsmall
    exact logarithmicA2BCorrelationBound_le_raw
      t A N H₁ H₂ r ht hA hrPos hrHigh hH₂pos hH₂ hsmallR
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 by norm_num))
        hH₁nonneg)
      ((H₁ : ℝ) * N)) hpref

noncomputable def logarithmicDifferenceA2UniformBound
    (t A : ℝ) (N H₁ H₂ r : ℕ) : ℝ :=
  Real.sqrt (2 * (N : ℝ) ^ 2 * H₂) / H₂ +
    Real.sqrt (1920 * (N : ℝ) ^ 2 * H₂ ^ 2 *
      Real.sqrt (t * H₁ * H₂ / A ^ 4)) / H₂ +
    Real.sqrt (3840 * (N : ℝ) * H₂ * Real.sqrt (H₂ : ℝ) /
      Real.sqrt (t * r / A ^ 4)) / H₂

theorem logarithmicDifferenceA2RawBound_le_uniform
    (t A : ℝ) (N H₁ H₂ r : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH₂pos : 0 < H₂)
    (hr : 0 < r) (hrHigh : r ≤ H₁) :
    logarithmicDifferenceA2RawBound t A r (N - r) H₂ ≤
      logarithmicDifferenceA2UniformBound t A N H₁ H₂ r := by
  have hsub : ((N - r : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.sub_le N r
  have hrReal : (r : ℝ) ≤ H₁ := by exact_mod_cast hrHigh
  have hden : 0 < (H₂ : ℝ) := by exact_mod_cast hH₂pos
  unfold logarithmicDifferenceA2RawBound logarithmicDifferenceA2UniformBound
  apply add_le_add
  · apply add_le_add
    · apply div_le_div_of_nonneg_right _ hden.le
      apply Real.sqrt_le_sqrt
      gcongr
    · apply div_le_div_of_nonneg_right _ hden.le
      apply Real.sqrt_le_sqrt
      have hsqrt :
          Real.sqrt (t * (r : ℝ) * H₂ / A ^ 4) ≤
            Real.sqrt (t * (H₁ : ℝ) * H₂ / A ^ 4) := by
        apply Real.sqrt_le_sqrt
        gcongr
      have hsq : (((N - r : ℕ) : ℝ) ^ 2) ≤ (N : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((N - r : ℕ) : ℝ)), sq_nonneg (N : ℝ)]
      gcongr
  · apply div_le_div_of_nonneg_right _ hden.le
    apply Real.sqrt_le_sqrt
    have hdenq : 0 < Real.sqrt (t * (r : ℝ) / A ^ 4) := by
      exact Real.sqrt_pos.2 (by positivity)
    gcongr

noncomputable def logarithmicDifferenceA2SeparatedBound
    (t A : ℝ) (N H₁ H₂ r : ℕ) : ℝ :=
  2 * N / Real.sqrt (H₂ : ℝ) +
    44 * N * Real.sqrt (Real.sqrt (t * H₁ * H₂ / A ^ 4)) +
    62 * Real.sqrt (N : ℝ) *
      Real.sqrt (1 /
        (Real.sqrt (H₂ : ℝ) * Real.sqrt (t * r / A ^ 4)))

theorem logarithmicDifferenceA2UniformBound_le_separated
    (t A : ℝ) (N H₁ H₂ r : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH₂pos : 0 < H₂) (hr : 0 < r) :
    logarithmicDifferenceA2UniformBound t A N H₁ H₂ r ≤
      logarithmicDifferenceA2SeparatedBound t A N H₁ H₂ r := by
  have hH : (0 : ℝ) < H₂ := by exact_mod_cast hH₂pos
  have hsH : 0 < Real.sqrt (H₂ : ℝ) := Real.sqrt_pos.2 hH
  have hsHsq : Real.sqrt (H₂ : ℝ) ^ 2 = H₂ := Real.sq_sqrt hH.le
  have hq : 0 < t * (r : ℝ) / A ^ 4 := by positivity
  have hsq : 0 < Real.sqrt (t * (r : ℝ) / A ^ 4) := Real.sqrt_pos.2 hq
  have hfirst :
      Real.sqrt (2 * (N : ℝ) ^ 2 * H₂) / H₂ ≤
        2 * N / Real.sqrt (H₂ : ℝ) := by
    rw [div_le_iff₀ hH]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · field_simp [hsH.ne']
      nlinarith [sq_nonneg (N : ℝ)]
  have hsecond :
      Real.sqrt (1920 * (N : ℝ) ^ 2 * H₂ ^ 2 *
          Real.sqrt (t * H₁ * H₂ / A ^ 4)) / H₂ ≤
        44 * N * Real.sqrt (Real.sqrt (t * H₁ * H₂ / A ^ 4)) := by
    rw [div_le_iff₀ hH]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · let z : ℝ := Real.sqrt (t * H₁ * H₂ / A ^ 4)
      have hz : 0 ≤ z := by dsimp only [z]; positivity
      have hsz : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz
      change 1920 * (N : ℝ) ^ 2 * H₂ ^ 2 * z ≤
        (44 * N * Real.sqrt z * H₂) ^ 2
      calc
        1920 * (N : ℝ) ^ 2 * H₂ ^ 2 * z ≤
            1936 * (N : ℝ) ^ 2 * H₂ ^ 2 * z := by
          have hp : 0 ≤ (N : ℝ) ^ 2 * H₂ ^ 2 * z := by positivity
          nlinarith
        _ = 1936 * (N : ℝ) ^ 2 * H₂ ^ 2 * (Real.sqrt z) ^ 2 := by
          rw [hsz]
        _ = (44 * N * Real.sqrt z * H₂) ^ 2 := by ring
  have hthird :
      Real.sqrt (3840 * (N : ℝ) * H₂ * Real.sqrt (H₂ : ℝ) /
          Real.sqrt (t * r / A ^ 4)) / H₂ ≤
        62 * Real.sqrt (N : ℝ) *
          Real.sqrt (1 /
            (Real.sqrt (H₂ : ℝ) * Real.sqrt (t * r / A ^ 4))) := by
    rw [div_le_iff₀ hH]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · let q : ℝ := Real.sqrt (t * r / A ^ 4)
      let z : ℝ := Real.sqrt
        (1 / (Real.sqrt (H₂ : ℝ) * q))
      have hqz : 0 < q := by simpa only [q] using hsq
      have hsN := Real.sq_sqrt (Nat.cast_nonneg N)
      have hsz : z ^ 2 = 1 / (Real.sqrt (H₂ : ℝ) * q) := by
        dsimp only [z]
        exact Real.sq_sqrt (by positivity)
      have hrhs :
          (62 * Real.sqrt (N : ℝ) * z * H₂) ^ 2 =
            3844 * (N : ℝ) * H₂ *
              Real.sqrt (H₂ : ℝ) / q := by
        rw [mul_pow, mul_pow, mul_pow, hsN, hsz]
        field_simp [hsH.ne', hqz.ne']
        nlinarith [hsHsq]
      change 3840 * (N : ℝ) * H₂ * Real.sqrt (H₂ : ℝ) / q ≤
        (62 * Real.sqrt (N : ℝ) * z * H₂) ^ 2
      rw [hrhs]
      gcongr
      norm_num
  unfold logarithmicDifferenceA2UniformBound
    logarithmicDifferenceA2SeparatedBound
  linarith

/-- Cauchy--Schwarz plus the telescoping inverse-square-root estimate gives
the exact finite `r^(-1/4)` summability needed by the outer A-process. -/
theorem sum_Icc_sqrt_one_div_sqrt_le (H : ℕ) :
    ∑ r ∈ Finset.Icc 1 (H - 1),
        Real.sqrt (1 / Real.sqrt (r : ℝ)) ≤
      Real.sqrt (H : ℝ) *
        Real.sqrt (2 * Real.sqrt (H : ℝ)) := by
  let S := Finset.Icc 1 (H - 1)
  have hcard : (S.card : ℝ) ≤ H := by
    have hsubset : S ⊆ Finset.range H := by
      intro r hr
      exact Finset.mem_range.mpr (by
        have := Finset.mem_Icc.mp hr
        omega)
    have hcardNat : S.card ≤ H := by
      simpa using Finset.card_le_card hsubset
    exact_mod_cast hcardNat
  have hsum : ∑ r ∈ S, 1 / Real.sqrt (r : ℝ) ≤
      2 * Real.sqrt (H : ℝ) := by
    simpa only [S] using sum_Icc_one_div_sqrt_le_two_sqrt H
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun _r : ℕ => (1 : ℝ))
    (fun r : ℕ => Real.sqrt (1 / Real.sqrt (r : ℝ)))
  have hsquares :
      ∑ r ∈ S, (Real.sqrt (1 / Real.sqrt (r : ℝ))) ^ 2 =
        ∑ r ∈ S, 1 / Real.sqrt (r : ℝ) := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [Real.sq_sqrt]
    positivity
  have honeSquares : ∑ _r ∈ S, (1 : ℝ) ^ 2 = S.card := by simp
  have hraw :
      ∑ r ∈ S, Real.sqrt (1 / Real.sqrt (r : ℝ)) ≤
        Real.sqrt (S.card : ℝ) *
          Real.sqrt (∑ r ∈ S, 1 / Real.sqrt (r : ℝ)) := by
    simpa only [one_mul, honeSquares, hsquares] using hcauchy
  calc
    ∑ r ∈ Finset.Icc 1 (H - 1),
        Real.sqrt (1 / Real.sqrt (r : ℝ)) =
      ∑ r ∈ S, Real.sqrt (1 / Real.sqrt (r : ℝ)) := by rfl
    _ ≤ Real.sqrt (S.card : ℝ) *
        Real.sqrt (∑ r ∈ S, 1 / Real.sqrt (r : ℝ)) := hraw
    _ ≤ Real.sqrt (H : ℝ) *
        Real.sqrt (2 * Real.sqrt (H : ℝ)) := by
      gcongr

theorem separated_inverse_shift_factor
    (t A : ℝ) (H r : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH : 0 < H) (hr : 0 < r) :
    Real.sqrt (1 /
        (Real.sqrt (H : ℝ) * Real.sqrt (t * r / A ^ 4))) =
      Real.sqrt (1 /
        (Real.sqrt (H : ℝ) * Real.sqrt (t / A ^ 4))) *
        Real.sqrt (1 / Real.sqrt (r : ℝ)) := by
  have hbase : 0 < t / A ^ 4 := by positivity
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hsH : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hH)
  have hsbase : 0 < Real.sqrt (t / A ^ 4) := Real.sqrt_pos.2 hbase
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrReal
  have hsplit : Real.sqrt (t * (r : ℝ) / A ^ 4) =
      Real.sqrt (t / A ^ 4) * Real.sqrt (r : ℝ) := by
    rw [show t * (r : ℝ) / A ^ 4 = (t / A ^ 4) * r by ring,
      Real.sqrt_mul hbase.le]
  have hrecip :
      1 / (Real.sqrt (H : ℝ) * Real.sqrt (t * r / A ^ 4)) =
        (1 / (Real.sqrt (H : ℝ) * Real.sqrt (t / A ^ 4))) *
          (1 / Real.sqrt (r : ℝ)) := by
    rw [hsplit]
    field_simp [hsH.ne', hsbase.ne', hsr.ne']
  rw [hrecip, Real.sqrt_mul (by positivity :
    0 ≤ 1 / (Real.sqrt (H : ℝ) * Real.sqrt (t / A ^ 4)))]

theorem sum_logarithmicDifferenceA2SeparatedBound_le
    (t A : ℝ) (N H₁ H₂ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH₂pos : 0 < H₂) :
    ∑ r ∈ Finset.Icc 1 (H₁ - 1),
        logarithmicDifferenceA2SeparatedBound t A N H₁ H₂ r ≤
      (H₁ : ℝ) *
        (2 * N / Real.sqrt (H₂ : ℝ) +
          44 * N * Real.sqrt
            (Real.sqrt (t * H₁ * H₂ / A ^ 4))) +
      62 * Real.sqrt (N : ℝ) *
        Real.sqrt (1 /
          (Real.sqrt (H₂ : ℝ) * Real.sqrt (t / A ^ 4))) *
        (Real.sqrt (H₁ : ℝ) *
          Real.sqrt (2 * Real.sqrt (H₁ : ℝ))) := by
  let S := Finset.Icc 1 (H₁ - 1)
  let d : ℝ := 2 * N / Real.sqrt (H₂ : ℝ) +
    44 * N * Real.sqrt (Real.sqrt (t * H₁ * H₂ / A ^ 4))
  let e : ℝ := 62 * Real.sqrt (N : ℝ) *
    Real.sqrt (1 /
      (Real.sqrt (H₂ : ℝ) * Real.sqrt (t / A ^ 4)))
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hcard : (S.card : ℝ) ≤ H₁ := by
    have hsubset : S ⊆ Finset.range H₁ := by
      intro r hr
      exact Finset.mem_range.mpr (by
        have := Finset.mem_Icc.mp hr
        omega)
    have hcardNat : S.card ≤ H₁ := by
      simpa using Finset.card_le_card hsubset
    exact_mod_cast hcardNat
  have hquarter : ∑ r ∈ S,
      Real.sqrt (1 / Real.sqrt (r : ℝ)) ≤
        Real.sqrt (H₁ : ℝ) *
          Real.sqrt (2 * Real.sqrt (H₁ : ℝ)) := by
    simpa only [S] using sum_Icc_sqrt_one_div_sqrt_le H₁
  have hpoint : ∀ r ∈ S,
      logarithmicDifferenceA2SeparatedBound t A N H₁ H₂ r =
        d + e * Real.sqrt (1 / Real.sqrt (r : ℝ)) := by
    intro r hrMem
    have hrPos : 0 < r := by
      have := Finset.mem_Icc.mp hrMem
      omega
    unfold logarithmicDifferenceA2SeparatedBound
    rw [separated_inverse_shift_factor t A H₂ r ht hA hH₂pos hrPos]
    dsimp only [d, e]
    ring
  calc
    ∑ r ∈ Finset.Icc 1 (H₁ - 1),
        logarithmicDifferenceA2SeparatedBound t A N H₁ H₂ r =
      ∑ r ∈ S, (d + e * Real.sqrt (1 / Real.sqrt (r : ℝ))) := by
        apply Finset.sum_congr rfl
        intro r hrMem
        exact hpoint r hrMem
    _ = (S.card : ℝ) * d + e *
        (∑ r ∈ S, Real.sqrt (1 / Real.sqrt (r : ℝ))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · simp
      · rw [← Finset.mul_sum]
    _ ≤ (H₁ : ℝ) * d + e *
        (Real.sqrt (H₁ : ℝ) *
          Real.sqrt (2 * Real.sqrt (H₁ : ℝ))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcard hd)
        (mul_le_mul_of_nonneg_left hquarter he)
    _ = (H₁ : ℝ) *
        (2 * N / Real.sqrt (H₂ : ℝ) +
          44 * N * Real.sqrt
            (Real.sqrt (t * H₁ * H₂ / A ^ 4))) +
      62 * Real.sqrt (N : ℝ) *
        Real.sqrt (1 /
          (Real.sqrt (H₂ : ℝ) * Real.sqrt (t / A ^ 4))) *
        (Real.sqrt (H₁ : ℝ) *
          Real.sqrt (2 * Real.sqrt (H₁ : ℝ))) := by
      dsimp only [d, e]

noncomputable def logarithmicA2BInnerSumBound
    (t A : ℝ) (N H₁ H₂ : ℕ) : ℝ :=
  (H₁ : ℝ) *
      (2 * N / Real.sqrt (H₂ : ℝ) +
        44 * N * Real.sqrt
          (Real.sqrt (t * H₁ * H₂ / A ^ 4))) +
    62 * Real.sqrt (N : ℝ) *
      Real.sqrt (1 /
        (Real.sqrt (H₂ : ℝ) * Real.sqrt (t / A ^ 4))) *
      (Real.sqrt (H₁ : ℝ) *
        Real.sqrt (2 * Real.sqrt (H₁ : ℝ)))

theorem logarithmic_weyl_A2B_process_summed
    (t A : ℝ) (N H₁ H₂ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂)
    (hH₂ : H₂ ≤ N - (H₁ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) / A ^ 4 ≤ 1) :
    (H₁ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerLogarithmicTerm t A n‖ ^ 2 ≤
      ((N + H₁ : ℕ) : ℝ) *
        ((H₁ : ℝ) * N + (H₁ : ℝ) *
          (2 * logarithmicA2BInnerSumBound t A N H₁ H₂)) := by
  have hraw := logarithmic_weyl_A2B_process_raw
    t A N H₁ H₂ ht hA hNA hH₁ hH₂pos hH₂ hsmall
  refine hraw.trans ?_
  have hsumRawUniform :
      ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicDifferenceA2RawBound t A r (N - r) H₂ ≤
        ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicDifferenceA2UniformBound t A N H₁ H₂ r := by
    apply Finset.sum_le_sum
    intro r hrMem
    have hrData := Finset.mem_Icc.mp hrMem
    exact logarithmicDifferenceA2RawBound_le_uniform
      t A N H₁ H₂ r ht hA hH₂pos (by omega)
        (hrData.2.trans (Nat.sub_le H₁ 1))
  have hsumUniformSeparated :
      ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicDifferenceA2UniformBound t A N H₁ H₂ r ≤
        ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicDifferenceA2SeparatedBound t A N H₁ H₂ r := by
    apply Finset.sum_le_sum
    intro r hrMem
    have hrData := Finset.mem_Icc.mp hrMem
    exact logarithmicDifferenceA2UniformBound_le_separated
      t A N H₁ H₂ r ht hA hH₂pos (by omega)
  have hsumSeparated := sum_logarithmicDifferenceA2SeparatedBound_le
    t A N H₁ H₂ ht hA hH₂pos
  have hsum :
      ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicDifferenceA2RawBound t A r (N - r) H₂ ≤
        logarithmicA2BInnerSumBound t A N H₁ H₂ := by
    exact hsumRawUniform.trans (hsumUniformSeparated.trans (by
      simpa only [logarithmicA2BInnerSumBound] using hsumSeparated))
  have hpref : 0 ≤ ((N + H₁ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hH₁nonneg : 0 ≤ (H₁ : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 by norm_num))
        hH₁nonneg)
      ((H₁ : ℝ) * N)) hpref

theorem logarithmicA2BInnerSumBound_nonneg
    (t A : ℝ) (N H₁ H₂ : ℕ) :
    0 ≤ logarithmicA2BInnerSumBound t A N H₁ H₂ := by
  unfold logarithmicA2BInnerSumBound
  positivity

/-- Division by the first A-process length, with the `N+H₁` endpoint loss
replaced by `2N`.  This is the compact form used for scale optimization. -/
theorem norm_logarithmic_sum_sq_le_A2B_compact
    (t A : ℝ) (N H₁ H₂ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁pos : 0 < H₁) (hH₁ : H₁ ≤ N)
    (hH₂pos : 0 < H₂) (hH₂ : H₂ ≤ N - (H₁ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) / A ^ 4 ≤ 1) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
        integerLogarithmicTerm t A n‖ ^ 2 ≤
      (2 * (N : ℝ) / H₁) *
        ((N : ℝ) + 2 * logarithmicA2BInnerSumBound t A N H₁ H₂) := by
  have hsource := logarithmic_weyl_A2B_process_summed
    t A N H₁ H₂ ht hA hNA hH₁ hH₂pos hH₂ hsmall
  let S := logarithmicA2BInnerSumBound t A N H₁ H₂
  have hS : 0 ≤ S := logarithmicA2BInnerSumBound_nonneg t A N H₁ H₂
  have hfactor : 0 ≤ (N : ℝ) + 2 * S := by positivity
  have hNH : ((N + H₁ : ℕ) : ℝ) ≤ 2 * N := by
    norm_num
    exact_mod_cast (by omega : N + H₁ ≤ 2 * N)
  have hupper :
      ((N + H₁ : ℕ) : ℝ) *
          ((H₁ : ℝ) * N + (H₁ : ℝ) * (2 * S)) ≤
        (H₁ : ℝ) ^ 2 *
          ((2 * (N : ℝ) / H₁) * ((N : ℝ) + 2 * S)) := by
    have hH₁Real : (0 : ℝ) < H₁ := by exact_mod_cast hH₁pos
    calc
      ((N + H₁ : ℕ) : ℝ) *
          ((H₁ : ℝ) * N + (H₁ : ℝ) * (2 * S)) ≤
        (2 * (N : ℝ)) *
          ((H₁ : ℝ) * N + (H₁ : ℝ) * (2 * S)) := by
            gcongr
      _ = (H₁ : ℝ) ^ 2 *
          ((2 * (N : ℝ) / H₁) * ((N : ℝ) + 2 * S)) := by
        field_simp [hH₁Real.ne']
  have hsq := hsource.trans (by simpa only [S] using hupper)
  apply le_of_mul_le_mul_left
    (by simpa [mul_assoc] using hsq)
  exact sq_pos_of_pos (by exact_mod_cast hH₁pos : (0 : ℝ) < H₁)

#print axioms sqrt_div_sixteen
#print axioms sum_Icc_one_div_sqrt_le_two_sqrt
#print axioms logarithmicSecondCorrelationBound_le_homogeneous
#print axioms logarithmicSecondCorrelationBound_le_simple
#print axioms sum_logarithmicSecondCorrelationBound_le
#print axioms logarithmicDifferenceA2Majorant_le_simple
#print axioms logarithmicDifferenceA2Bound_le_raw
#print axioms logarithmic_weyl_A2B_process_raw
#print axioms logarithmicDifferenceA2RawBound_le_uniform
#print axioms logarithmicDifferenceA2UniformBound_le_separated
#print axioms sum_Icc_sqrt_one_div_sqrt_le
#print axioms separated_inverse_shift_factor
#print axioms sum_logarithmicDifferenceA2SeparatedBound_le
#print axioms logarithmic_weyl_A2B_process_summed
#print axioms norm_logarithmic_sum_sq_le_A2B_compact

end

end GafniTao
