import RiemannZeta.GuthMaynard.HughesYoungRightTail

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Arbitrarily high Hughes--Young opening lines

Hughes--Young truncate the opened approximate functional equation by
moving its Mellin line arbitrarily far to the right.  The recurrence for
Deligne's real Gamma factor makes this operation quantitative without any
use of an unstated Stirling estimate.  This file records the exact finite
recurrence first; all later tail estimates use this identity.
-/

/-- The finite product occurring after moving `Gammaℝ s` right by `2q`. -/
noncomputable def gammaRShiftProduct (s : ℂ) (q : ℕ) : ℂ :=
  ∏ r ∈ Finset.range q, (s + (2 * r : ℕ)) / (2 * (Real.pi : ℂ))

theorem gammaRShiftProduct_zero (s : ℂ) :
    gammaRShiftProduct s 0 = 1 := by
  simp [gammaRShiftProduct]

theorem gammaRShiftProduct_succ (s : ℂ) (q : ℕ) :
    gammaRShiftProduct s (q + 1) =
      gammaRShiftProduct s q *
        (s + (2 * q : ℕ)) / (2 * (Real.pi : ℂ)) := by
  simp [gammaRShiftProduct, Finset.prod_range_succ]
  ring

/-- Exact iteration of `Gammaℝ_add_two`.  The explicit nonvanishing
hypothesis is precisely what the recurrence requires at each finite step. -/
theorem GammaR_add_two_mul_nat
    (s : ℂ) (q : ℕ)
    (hs : ∀ r < q, s + (2 * r : ℕ) ≠ 0) :
    Complex.Gammaℝ (s + (2 * q : ℕ)) =
      Complex.Gammaℝ s * gammaRShiftProduct s q := by
  induction q with
  | zero => simp [gammaRShiftProduct]
  | succ q ih =>
      have hsPrev : ∀ r < q, s + (2 * r : ℕ) ≠ 0 := by
        intro r hr
        exact hs r (Nat.lt_succ_of_lt hr)
      have hsq : s + (2 * q : ℕ) ≠ 0 := hs q (Nat.lt_succ_self q)
      have harg :
          s + (2 * (q + 1) : ℕ) = (s + (2 * q : ℕ)) + 2 := by
        push_cast
        ring
      rw [harg, Complex.Gammaℝ_add_two hsq, ih hsPrev,
        gammaRShiftProduct_succ]
      ring

theorem afeCriticalPoint_add_nat_ne_zero
    (t u : ℝ) (r : ℕ) :
    afeCriticalPoint t + (u : ℂ) * I + (2 * r : ℕ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [afeCriticalPoint] at hre
  have hpos : 0 < (1 / 2 : ℝ) + (2 * r : ℕ) := by positivity
  linarith

/-- Exact paired Gamma quotient on the line `Re w = 2q`. -/
noncomputable def hughesYoungGammaRatioEven
    (q : ℕ) (t u : ℝ) : ℂ :=
  let w : ℂ := (2 * q : ℕ) + (u : ℂ) * I
  let s₁ := afeCriticalPoint t + w
  let s₂ := afeCriticalPoint (-t) + w
  Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2 /
    afeGammaNormalization t

theorem hughesYoungGammaRatioEven_eq
    (q : ℕ) (t u : ℝ) :
    hughesYoungGammaRatioEven q t u =
      hughesYoungGammaRatio t u *
        gammaRShiftProduct (afeCriticalPoint t + (u : ℂ) * I) q ^ 2 *
        gammaRShiftProduct (afeCriticalPoint (-t) + (u : ℂ) * I) q ^ 2 := by
  let s₁ : ℂ := afeCriticalPoint t + (u : ℂ) * I
  let s₂ : ℂ := afeCriticalPoint (-t) + (u : ℂ) * I
  have hrec₁ := GammaR_add_two_mul_nat s₁ q
    (fun r _ => afeCriticalPoint_add_nat_ne_zero t u r)
  have hrec₂ := GammaR_add_two_mul_nat s₂ q
    (fun r _ => afeCriticalPoint_add_nat_ne_zero (-t) u r)
  have harg₁ :
      afeCriticalPoint t + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I) =
        s₁ + (2 * q : ℕ) := by
    dsimp [s₁]
    ring
  have harg₂ :
      afeCriticalPoint (-t) + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I) =
        s₂ + (2 * q : ℕ) := by
    dsimp [s₂]
    ring
  unfold hughesYoungGammaRatioEven hughesYoungGammaRatio
  dsimp only
  rw [harg₁, harg₂, hrec₁, hrec₂]
  field_simp [afeGammaNormalization_ne_zero]
  ring

/-- A deliberately generous common majorant for every recurrence factor
on the line `Re w = 2q`. -/
noncomputable def hughesYoungHighLineBase
    (q : ℕ) (t u : ℝ) : ℝ :=
  3 + 2 * q + |t| + |u|

theorem norm_gammaRShiftFactor_le_base
    (q : ℕ) (t u : ℝ) {r : ℕ} (hr : r < q) :
    ‖(afeCriticalPoint t + (u : ℂ) * I + (2 * r : ℕ)) /
        (2 * (Real.pi : ℂ))‖ ≤
      hughesYoungHighLineBase q t u := by
  have hden : 1 ≤ ‖(2 : ℂ) * (Real.pi : ℂ)‖ := by
    rw [norm_mul, Complex.norm_ofNat, norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hnum :
      ‖afeCriticalPoint t + (u : ℂ) * I + (2 * r : ℕ)‖ ≤
        hughesYoungHighLineBase q t u := by
    calc
      ‖afeCriticalPoint t + (u : ℂ) * I + (2 * r : ℕ)‖ ≤
          |(afeCriticalPoint t + (u : ℂ) * I + (2 * r : ℕ)).re| +
            |(afeCriticalPoint t + (u : ℂ) * I + (2 * r : ℕ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |(1 / 2 : ℝ) + 2 * r| + |t + u| := by
        simp [afeCriticalPoint]
      _ ≤ (1 / 2 : ℝ) + 2 * r + (|t| + |u|) := by
        rw [abs_of_nonneg (by positivity)]
        gcongr
        exact abs_add_le t u
      _ ≤ hughesYoungHighLineBase q t u := by
        unfold hughesYoungHighLineBase
        have hrle : (r : ℝ) ≤ q := by exact_mod_cast (Nat.le_of_lt hr)
        nlinarith
  rw [norm_div]
  exact (div_le_self (norm_nonneg _) hden).trans hnum

theorem norm_gammaRShiftProduct_le_base_pow
    (q : ℕ) (t u : ℝ) :
    ‖gammaRShiftProduct (afeCriticalPoint t + (u : ℂ) * I) q‖ ≤
      hughesYoungHighLineBase q t u ^ q := by
  rw [gammaRShiftProduct, norm_prod]
  calc
    ∏ r ∈ Finset.range q,
        ‖(afeCriticalPoint t + (u : ℂ) * I + (2 * r : ℕ)) /
          (2 * (Real.pi : ℂ))‖ ≤
      ∏ _r ∈ Finset.range q, hughesYoungHighLineBase q t u := by
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun r hr =>
          norm_gammaRShiftFactor_le_base q t u (Finset.mem_range.mp hr)
    _ = hughesYoungHighLineBase q t u ^ q := by simp

theorem norm_hughesYoungGammaRatioEven_le
    (q : ℕ) (t u : ℝ) :
    ‖hughesYoungGammaRatioEven q t u‖ ≤
      Real.exp (16 * u ^ 2) *
        hughesYoungHighLineBase q t u ^ (4 * q) := by
  rw [hughesYoungGammaRatioEven_eq, norm_mul, norm_mul, norm_pow, norm_pow]
  have hplus := norm_gammaRShiftProduct_le_base_pow q t u
  have hminus := norm_gammaRShiftProduct_le_base_pow q (-t) u
  have hbaseNeg :
      hughesYoungHighLineBase q (-t) u = hughesYoungHighLineBase q t u := by
    simp [hughesYoungHighLineBase]
  rw [hbaseNeg] at hminus
  calc
    ‖hughesYoungGammaRatio t u‖ *
          ‖gammaRShiftProduct (afeCriticalPoint t + (u : ℂ) * I) q‖ ^ 2 *
          ‖gammaRShiftProduct (afeCriticalPoint (-t) + (u : ℂ) * I) q‖ ^ 2 ≤
        Real.exp (16 * u ^ 2) *
          (hughesYoungHighLineBase q t u ^ q) ^ 2 *
          (hughesYoungHighLineBase q t u ^ q) ^ 2 := by
      gcongr
      exact norm_hughesYoungGammaRatio_le t u
    _ = Real.exp (16 * u ^ 2) *
          hughesYoungHighLineBase q t u ^ (4 * q) := by
      ring

theorem norm_afeCriticalPoint_add_even_le_base
    (q : ℕ) (t u : ℝ) :
    ‖afeCriticalPoint t + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I)‖ ≤
      hughesYoungHighLineBase q t u := by
  calc
    ‖afeCriticalPoint t + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I)‖ ≤
        |(afeCriticalPoint t + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I)).re| +
          |(afeCriticalPoint t + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |(1 / 2 : ℝ) + 2 * q| + |t + u| := by
      simp [afeCriticalPoint]
    _ ≤ (1 / 2 : ℝ) + 2 * q + (|t| + |u|) := by
      rw [abs_of_nonneg (by positivity)]
      gcongr
      exact abs_add_le t u
    _ ≤ hughesYoungHighLineBase q t u := by
      unfold hughesYoungHighLineBase
      linarith

theorem norm_one_sub_afeCriticalPoint_add_even_le_base
    (q : ℕ) (t u : ℝ) :
    ‖1 - (afeCriticalPoint t + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I))‖ ≤
      hughesYoungHighLineBase q t u := by
  have hreal : |(1 / 2 : ℝ) - 2 * q| ≤ (1 / 2 : ℝ) + 2 * q := by
    rw [abs_le]
    have hq : 0 ≤ (q : ℝ) := by positivity
    constructor <;> nlinarith
  calc
    ‖1 - (afeCriticalPoint t + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I))‖ ≤
        |(1 - (afeCriticalPoint t +
          (((2 * q : ℕ) : ℂ) + (u : ℂ) * I))).re| +
        |(1 - (afeCriticalPoint t +
          (((2 * q : ℕ) : ℂ) + (u : ℂ) * I))).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |(1 / 2 : ℝ) - 2 * q| + |-(t + u)| := by
      simp [afeCriticalPoint]
      ring_nf
    _ ≤ ((1 / 2 : ℝ) + 2 * q) + (|t| + |u|) := by
      rw [abs_neg]
      exact add_le_add hreal (abs_add_le t u)
    _ ≤ hughesYoungHighLineBase q t u := by
      unfold hughesYoungHighLineBase
      linarith

/-- Exact norm of the pole-canceling central normalization. -/
theorem norm_afePoleNormalization_eq (t : ℝ) :
    ‖afePoleNormalization t‖ = ((1 / 4 : ℝ) + t ^ 2) ^ 4 := by
  let A : ℝ := (1 / 4 : ℝ) + t ^ 2
  have hcritical (v : ℝ) :
      ‖(1 / 2 : ℂ) + (v : ℂ) * I‖ *
          ‖1 - ((1 / 2 : ℂ) + (v : ℂ) * I)‖ =
        (1 / 4 : ℝ) + v ^ 2 := by
    have h₁ : ‖(1 / 2 : ℂ) + (v : ℂ) * I‖ =
        Real.sqrt ((1 / 4 : ℝ) + v ^ 2) := by
      rw [Complex.norm_def]
      congr 1
      simp [Complex.normSq, sq]
      ring
    have h₂ : ‖1 - ((1 / 2 : ℂ) + (v : ℂ) * I)‖ =
        Real.sqrt ((1 / 4 : ℝ) + v ^ 2) := by
      rw [Complex.norm_def]
      congr 1
      simp [Complex.normSq, sq]
      ring
    rw [h₁, h₂, ← sq]
    exact Real.sq_sqrt (by positivity)
  have hcrit :
      ‖afeCriticalPoint t * (1 - afeCriticalPoint t)‖ = A := by
    rw [norm_mul]
    simpa only [afeCriticalPoint, A] using hcritical t
  have hcritNeg :
      ‖afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ = A := by
    rw [norm_mul]
    have h := hcritical (-t)
    simpa only [afeCriticalPoint, A, neg_sq] using h
  unfold afePoleNormalization
  rw [show afeCriticalPoint t * (1 - afeCriticalPoint t) *
      afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)) =
    (afeCriticalPoint t * (1 - afeCriticalPoint t)) *
      (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) by ring,
    norm_pow, norm_mul, hcrit, hcritNeg]
  ring

theorem norm_afePoleNormalization_inv_le (t : ℝ) :
    ‖(afePoleNormalization t)⁻¹‖ ≤ 256 := by
  rw [norm_inv, norm_afePoleNormalization_eq]
  have hA : (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) + t ^ 2 :=
    le_add_of_nonneg_right (sq_nonneg t)
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / 4) hA 4
  calc
    (((1 / 4 : ℝ) + t ^ 2) ^ 4)⁻¹ ≤ (((1 / 4 : ℝ) ^ 4))⁻¹ := by
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow
    _ = 256 := by norm_num

/-- Pole-canceling polynomial quotient on `Re w = 2q`. -/
noncomputable def hughesYoungPolynomialRatioEven
    (q : ℕ) (t u : ℝ) : ℂ :=
  let w : ℂ := (2 * q : ℕ) + (u : ℂ) * I
  let s₁ := afeCriticalPoint t + w
  let s₂ := afeCriticalPoint (-t) + w
  (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2 /
    afePoleNormalization t

theorem norm_hughesYoungPolynomialRatioEven_le
    (q : ℕ) (t u : ℝ) :
    ‖hughesYoungPolynomialRatioEven q t u‖ ≤
      256 * hughesYoungHighLineBase q t u ^ 8 := by
  let B := hughesYoungHighLineBase q t u
  have hBneg : hughesYoungHighLineBase q (-t) u = B := by
    simp [hughesYoungHighLineBase, B]
  have hs₁ := norm_afeCriticalPoint_add_even_le_base q t u
  have h1s₁ := norm_one_sub_afeCriticalPoint_add_even_le_base q t u
  have hs₂ := norm_afeCriticalPoint_add_even_le_base q (-t) u
  have h1s₂ := norm_one_sub_afeCriticalPoint_add_even_le_base q (-t) u
  rw [hBneg] at hs₂ h1s₂
  have hB0 : 0 ≤ B := by unfold B hughesYoungHighLineBase; positivity
  unfold hughesYoungPolynomialRatioEven
  dsimp only
  simp only [div_eq_mul_inv, norm_mul, norm_pow]
  calc
    (‖afeCriticalPoint t + (((2 * q : ℕ) : ℂ) + (u : ℂ) * I)‖ *
          ‖1 - (afeCriticalPoint t +
            (((2 * q : ℕ) : ℂ) + (u : ℂ) * I))‖) ^ 2 *
        (‖afeCriticalPoint (-t) +
            (((2 * q : ℕ) : ℂ) + (u : ℂ) * I)‖ *
          ‖1 - (afeCriticalPoint (-t) +
            (((2 * q : ℕ) : ℂ) + (u : ℂ) * I))‖) ^ 2 *
        ‖(afePoleNormalization t)⁻¹‖ ≤
      (B * B) ^ 2 * (B * B) ^ 2 * 256 := by
        gcongr
        exact norm_afePoleNormalization_inv_le t
    _ = 256 * B ^ 8 := by ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- Exact factorization of the opening kernel on every even right line. -/
theorem hughesYoungRightContourWeight_even_eq
    {q : ℕ} (hq : 0 < q) (t u : ℝ) :
    hughesYoungRightContourWeight t (2 * q) u =
      (Complex.exp (100 *
        ((((2 * q : ℕ) : ℂ) + (u : ℂ) * I) ^ 2)) *
        hughesYoungAuxiliaryZero
          (((2 * q : ℕ) : ℂ) + (u : ℂ) * I)) *
        hughesYoungPolynomialRatioEven q t u *
        hughesYoungGammaRatioEven q t u /
        (((2 * q : ℕ) : ℂ) + (u : ℂ) * I) := by
  let w : ℂ := ((2 * q : ℕ) : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  have hw : w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
    omega
  have hfactor (E p₁ p₂ g₁ g₂ PN GN W : ℂ)
      (hPN : PN ≠ 0) (hGN : GN ≠ 0) (hW : W ≠ 0) :
      E * p₁ * p₂ * g₁ * g₂ / PN / W / GN =
        E * ((p₁ * p₂) / PN) * ((g₁ * g₂) / GN) / W := by
    field_simp [hPN, hGN, hW]
  unfold hughesYoungRightContourWeight hughesYoungPolynomialRatioEven
    hughesYoungGammaRatioEven
  dsimp only
  have hcast : (((2 * q : ℝ) : ℂ)) = (((2 * q : ℕ) : ℂ)) := by
    norm_cast
  rw [hcast]
  exact hfactor _ _ _ _ _ _ _ _
    (afePoleNormalization_ne_zero t) (afeGammaNormalization_ne_zero t) hw

theorem hughesYoungHighLineBase_le_on_height_support
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    (q : ℕ) (u : ℝ) :
    hughesYoungHighLineBase q t u ≤
      (7 + 2 * (q : ℝ)) * T * (1 + |u|) := by
  have hT0 : 0 ≤ T := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have habst : |t| ≤ 4 * T := by simpa [abs_of_nonneg ht0] using ht.2
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hu0 : 0 ≤ |u| := abs_nonneg u
  unfold hughesYoungHighLineBase
  have hC : 1 ≤ (7 + 2 * (q : ℝ)) * T := by
    nlinarith
  have hleft :
      (3 + 2 * (q : ℝ)) + |t| + |u| ≤
        (7 + 2 * (q : ℝ)) * T + |u| := by
    nlinarith
  calc
    (3 + 2 * (q : ℝ)) + |t| + |u| ≤
        (7 + 2 * (q : ℝ)) * T + |u| := hleft
    _ ≤ (7 + 2 * (q : ℝ)) * T +
        ((7 + 2 * (q : ℝ)) * T) * |u| := by
      simpa only [one_mul, add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_right hC hu0)
          ((7 + 2 * (q : ℝ)) * T)
    _ = (7 + 2 * (q : ℝ)) * T * (1 + |u|) := by ring

/-- Uniform Gaussian-polynomial estimate on an arbitrary even right line.
The line parameter is free and will be chosen after the final epsilon. -/
theorem norm_hughesYoungRightContourWeight_even_le_on_height_support
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {q : ℕ} (hq : 0 < q) (u : ℝ) :
    ‖hughesYoungRightContourWeight t (2 * q) u‖ ≤
      160000 * (2 * (q : ℝ) + 1) ^ 8 *
        Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
        ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) *
        (1 + |u|) ^ 8 := by
  let w : ℂ := ((2 * q : ℕ) : ℂ) + (u : ℂ) * I
  let B : ℝ := hughesYoungHighLineBase q t u
  let D : ℝ := (7 + 2 * (q : ℝ)) * T * (1 + |u|)
  have hB0 : 0 ≤ B := by unfold B hughesYoungHighLineBase; positivity
  have hD0 : 0 ≤ D := by unfold D; positivity
  have hBD : B ≤ D := by
    simpa only [B, D] using
      hughesYoungHighLineBase_le_on_height_support hT ht q u
  have hwNorm : 1 ≤ ‖w‖ := by
    have hre := Complex.abs_re_le_norm w
    have hqTwo : 1 ≤ (2 * q : ℕ) := by omega
    calc
      1 ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast hqTwo
      _ = |w.re| := by simp [w]
      _ ≤ ‖w‖ := hre
  have hexp :
      ‖Complex.exp (100 * w ^ 2)‖ =
        Real.exp (400 * (q : ℝ) ^ 2 - 100 * u ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [w, pow_two, Complex.mul_re]
    ring
  have hpoly : ‖hughesYoungPolynomialRatioEven q t u‖ ≤ 256 * B ^ 8 := by
    simpa only [B] using norm_hughesYoungPolynomialRatioEven_le q t u
  have hgamma : ‖hughesYoungGammaRatioEven q t u‖ ≤
      Real.exp (16 * u ^ 2) * B ^ (4 * q) := by
    simpa only [B] using norm_hughesYoungGammaRatioEven_le q t u
  have hwLe : ‖w‖ ≤ (2 * (q : ℝ) + 1) * (1 + |u|) := by
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ = 2 * (q : ℝ) + |u| := by simp [w]
      _ ≤ (2 * (q : ℝ) + 1) * (1 + |u|) := by
        have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
        nlinarith [abs_nonneg u]
  have hQ1 : 1 ≤ (2 * (q : ℝ) + 1) * (1 + |u|) := by
    have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith [abs_nonneg u]
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤
      625 * (2 * (q : ℝ) + 1) ^ 8 * (1 + |u|) ^ 8 := by
    unfold hughesYoungAuxiliaryZero
    rw [norm_pow]
    let Q : ℝ := (2 * (q : ℝ) + 1) * (1 + |u|)
    have hbase : ‖1 - 4 * w ^ 2‖ ≤ 5 * Q ^ 2 := by
      calc
        ‖1 - 4 * w ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖4 * w ^ 2‖ := norm_sub_le _ _
        _ = 1 + 4 * ‖w‖ ^ 2 := by simp [norm_pow]
        _ ≤ 1 + 4 * Q ^ 2 := by dsimp only [Q]; gcongr
        _ ≤ 5 * Q ^ 2 := by
          have : 1 ≤ Q := by simpa only [Q] using hQ1
          nlinarith [sq_nonneg Q]
    calc
      ‖1 - 4 * w ^ 2‖ ^ 4 ≤ (5 * Q ^ 2) ^ 4 := by gcongr
      _ = 625 * (2 * (q : ℝ) + 1) ^ 8 * (1 + |u|) ^ 8 := by
        dsimp only [Q]
        ring
  rw [hughesYoungRightContourWeight_even_eq hq]
  change ‖(Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w) *
      hughesYoungPolynomialRatioEven q t u *
      hughesYoungGammaRatioEven q t u / w‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, norm_mul]
  calc
    (‖Complex.exp (100 * w ^ 2)‖ * ‖hughesYoungAuxiliaryZero w‖) *
          ‖hughesYoungPolynomialRatioEven q t u‖ *
          ‖hughesYoungGammaRatioEven q t u‖ / ‖w‖ ≤
        (‖Complex.exp (100 * w ^ 2)‖ * ‖hughesYoungAuxiliaryZero w‖) *
          ‖hughesYoungPolynomialRatioEven q t u‖ *
          ‖hughesYoungGammaRatioEven q t u‖ := by
      exact div_le_self (by positivity) hwNorm
    _ ≤ (Real.exp (400 * (q : ℝ) ^ 2 - 100 * u ^ 2) *
          (625 * (2 * (q : ℝ) + 1) ^ 8 * (1 + |u|) ^ 8)) *
          (256 * B ^ 8) *
          (Real.exp (16 * u ^ 2) * B ^ (4 * q)) := by
      rw [hexp]
      gcongr
    _ = 160000 * (2 * (q : ℝ) + 1) ^ 8 *
          Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
          B ^ (4 * q + 8) * (1 + |u|) ^ 8 := by
      rw [show 400 * (q : ℝ) ^ 2 - 84 * u ^ 2 =
        (400 * (q : ℝ) ^ 2 - 100 * u ^ 2) + 16 * u ^ 2 by ring,
        Real.exp_add]
      ring
    _ ≤ 160000 * (2 * (q : ℝ) + 1) ^ 8 *
          Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
          D ^ (4 * q + 8) * (1 + |u|) ^ 8 := by
      gcongr
    _ = _ := by rfl

end RiemannZeta.GuthMaynard
