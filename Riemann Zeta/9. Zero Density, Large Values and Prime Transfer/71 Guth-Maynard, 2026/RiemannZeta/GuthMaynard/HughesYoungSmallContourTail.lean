import RiemannZeta.GuthMaynard.HughesYoungContourShift
import RiemannZeta.GuthMaynard.HughesYoungIntegratedConsumer
import RiemannZeta.GuthMaynard.HughesYoungDFIProfile

open Asymptotics Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The finite Hughes--Young small-contour correction

The native contour has real part `1 / log T` and height `T / 8`.  The
older horizontal estimate in `HughesYoungCentralBounds` assumes that the
Mellin ordinate dominates the physical height, so it cannot estimate this
literal contour.  This file starts the required joint estimate by keeping
the quotient of the two moving Gamma factors intact.
-/

private theorem smallContour_cosh_add_le_exp_abs_mul_cosh (x d : ℝ) :
    Real.cosh (x + d) ≤ Real.exp |d| * Real.cosh x := by
  have hplus : Real.exp d ≤ Real.exp |d| :=
    Real.exp_le_exp.mpr (le_abs_self d)
  have hminus : Real.exp (-d) ≤ Real.exp |d| :=
    Real.exp_le_exp.mpr (neg_le_abs d)
  rw [Real.cosh_eq, Real.cosh_eq]
  rw [Real.exp_add, show -(x + d) = -x + -d by ring, Real.exp_add]
  have hx : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have hnx : 0 ≤ Real.exp (-x) := (Real.exp_pos (-x)).le
  calc
    (Real.exp x * Real.exp d + Real.exp (-x) * Real.exp (-d)) / 2 ≤
        (Real.exp x * Real.exp |d| + Real.exp (-x) * Real.exp |d|) / 2 := by
          gcongr
    _ = Real.exp |d| * ((Real.exp x + Real.exp (-x)) / 2) := by ring

/-- Moving Gamma to the left of `Re z = 1/2` by at most `1/3` costs only
the exponential of the displacement times the logarithmic height.  The
strip stays in `Re z ≥ 1/6`, so no Gamma pole is crossed. -/
theorem exists_norm_Gamma_half_left_displacement_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (d : ℝ),
      z.re = 1 / 2 → 0 ≤ d → d ≤ 1 / 3 →
      ‖Complex.Gamma (z - (d : ℂ))‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp (C * d * Real.log (|z.im| + 2)) := by
  obtain ⟨C, hC, hdigamma⟩ :=
    Complex.exists_norm_digamma_le_log
      (a := (1 / 6 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro z d hzre hd0 hdUpper
  let f : ℝ → ℂ := fun x => Complex.Gamma (z - (x : ℂ))
  let f' : ℝ → ℂ := fun x =>
    -(Complex.Gamma (z - (x : ℂ)) * Complex.digamma (z - (x : ℂ)))
  let K : ℝ := C * Real.log (|z.im| + 2)
  have hlog : 0 ≤ Real.log (|z.im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hK : 0 ≤ K := mul_nonneg hC.le hlog
  have hzpos (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      0 < (z - (x : ℂ)).re := by
    simp only [sub_re, ofReal_re, hzre]
    linarith [hx.2]
  have hfderiv (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      HasDerivAt f (f' x) x := by
    have houter := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos (hzpos x hx)
    have hshift : HasDerivAt (fun w : ℂ => z - w) (-1) (x : ℂ) := by
      simpa using
        (hasDerivAt_const (x := (x : ℂ)) z).sub (hasDerivAt_id (x : ℂ))
    convert (houter.comp (x : ℂ) hshift).comp_ofReal using 1
    all_goals simp only [f']
    all_goals ring
  have hfcont : ContinuousOn f (Set.Icc 0 d) := by
    intro x hx
    exact (hfderiv x hx).continuousAt.continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico 0 d,
      HasDerivWithinAt f (f' x) (Set.Ici x) x := by
    intro x hx
    exact (hfderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico 0 d,
      ‖f' x‖ ≤ K * ‖f x‖ + 0 := by
    intro x hx
    have hxLower : (1 / 6 : ℝ) ≤ (z - (x : ℂ)).re := by
      simp only [sub_re, ofReal_re, hzre]
      linarith [hx.2.le]
    have hxUpper : (z - (x : ℂ)).re ≤ (1 / 2 : ℝ) := by
      simp only [sub_re, ofReal_re, hzre]
      linarith [hx.1]
    have him : (z - (x : ℂ)).im = z.im := by simp
    have hpsi := hdigamma (z - (x : ℂ)) hxLower hxUpper
    rw [him] at hpsi
    simp only [f', f, norm_neg, norm_mul, add_zero]
    calc
      ‖Complex.Gamma (z - (x : ℂ))‖ *
            ‖Complex.digamma (z - (x : ℂ))‖ ≤
          ‖Complex.Gamma (z - (x : ℂ))‖ *
            (C * Real.log (|z.im| + 2)) :=
        mul_le_mul_of_nonneg_left hpsi (norm_nonneg _)
      _ = K * ‖Complex.Gamma (z - (x : ℂ))‖ := by
        dsimp only [K]
        ring
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    hfcont hderivWithin (show ‖f 0‖ ≤ ‖f 0‖ by rfl) hbound d
    (show d ∈ Set.Icc 0 d from ⟨hd0, le_rfl⟩)
  rw [gronwallBound_ε0, sub_zero] at hgronwall
  change ‖Complex.Gamma (z - (d : ℂ))‖ ≤
    ‖Complex.Gamma z‖ *
      Real.exp (C * d * Real.log (|z.im| + 2))
  convert hgronwall using 1
  all_goals simp only [f, ofReal_zero, sub_zero, K]
  all_goals ring_nf

/-- Reciprocal Gamma has the matching right-displacement estimate.  This
is the lower-bound half of the moving Gamma quotient and is proved directly
for the entire reciprocal-Gamma function rather than by separating a
reflection-formula sine factor. -/
theorem exists_norm_inv_Gamma_half_right_displacement_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (d : ℝ),
      z.re = 1 / 2 → 0 ≤ d → d ≤ 1 / 3 →
      ‖(Complex.Gamma (z + (d : ℂ)))⁻¹‖ ≤
        ‖(Complex.Gamma z)⁻¹‖ *
          Real.exp (C * d * Real.log (|z.im| + 2)) := by
  obtain ⟨C, hC, hdigamma⟩ :=
    Complex.exists_norm_digamma_le_log
      (a := (1 / 2 : ℝ)) (b := (5 / 6 : ℝ)) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro z d hzre hd0 hdUpper
  let f : ℝ → ℂ := fun x => (Complex.Gamma (z + (x : ℂ)))⁻¹
  let f' : ℝ → ℂ := fun x =>
    -((Complex.Gamma (z + (x : ℂ)))⁻¹ *
      Complex.digamma (z + (x : ℂ)))
  let K : ℝ := C * Real.log (|z.im| + 2)
  have hlog : 0 ≤ Real.log (|z.im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hK : 0 ≤ K := mul_nonneg hC.le hlog
  have hzpos (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      0 < (z + (x : ℂ)).re := by
    simp only [add_re, ofReal_re, hzre]
    linarith [hx.1]
  have hGammaNe (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      Complex.Gamma (z + (x : ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [add_re, ofReal_re, neg_re, natCast_re, hzre] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hx.1]
  have hfderiv (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      HasDerivAt f (f' x) x := by
    have houter := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos (hzpos x hx)
    have hshift : HasDerivAt (fun w : ℂ => z + w) 1 (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).const_add z
    have hgamma := houter.comp (x : ℂ) hshift
    have hinv := hgamma.inv (hGammaNe x hx)
    convert hinv.comp_ofReal using 1
    all_goals simp only [f', Function.comp_apply]
    field_simp [hGammaNe x hx]
  have hfcont : ContinuousOn f (Set.Icc 0 d) := by
    intro x hx
    exact (hfderiv x hx).continuousAt.continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico 0 d,
      HasDerivWithinAt f (f' x) (Set.Ici x) x := by
    intro x hx
    exact (hfderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico 0 d,
      ‖f' x‖ ≤ K * ‖f x‖ + 0 := by
    intro x hx
    have hxLower : (1 / 2 : ℝ) ≤ (z + (x : ℂ)).re := by
      simp only [add_re, ofReal_re, hzre]
      linarith [hx.1]
    have hxUpper : (z + (x : ℂ)).re ≤ (5 / 6 : ℝ) := by
      simp only [add_re, ofReal_re, hzre]
      linarith [hx.2.le]
    have him : (z + (x : ℂ)).im = z.im := by simp
    have hpsi := hdigamma (z + (x : ℂ)) hxLower hxUpper
    rw [him] at hpsi
    simp only [f', f, norm_neg, norm_mul, add_zero]
    calc
      ‖(Complex.Gamma (z + (x : ℂ)))⁻¹‖ *
            ‖Complex.digamma (z + (x : ℂ))‖ ≤
          ‖(Complex.Gamma (z + (x : ℂ)))⁻¹‖ *
            (C * Real.log (|z.im| + 2)) :=
        mul_le_mul_of_nonneg_left hpsi (norm_nonneg _)
      _ = K * ‖(Complex.Gamma (z + (x : ℂ)))⁻¹‖ := by
        dsimp only [K]
        ring
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    hfcont hderivWithin (show ‖f 0‖ ≤ ‖f 0‖ by rfl) hbound d
    (show d ∈ Set.Icc 0 d from ⟨hd0, le_rfl⟩)
  rw [gronwallBound_ε0, sub_zero] at hgronwall
  change ‖(Complex.Gamma (z + (d : ℂ)))⁻¹‖ ≤
    ‖(Complex.Gamma z)⁻¹‖ *
      Real.exp (C * d * Real.log (|z.im| + 2))
  rw [show C * d * Real.log (|z.im| + 2) =
      (C * Real.log (|z.im| + 2)) * d by ring]
  simpa only [f, ofReal_zero, add_zero, K] using hgronwall

/-- The half-line Gamma quotient keeps the exponential cancellation between
the two physical heights.  This is the `c = 0` quotient underlying the
native small-contour estimate. -/
theorem norm_Gamma_half_t_sub_u_div_half_t_add_u_le (t u : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I) /
        Complex.Gamma ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ ≤
      Real.exp (Real.pi * |u|) := by
  let A : ℝ :=
    ‖Complex.Gamma ((1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I)‖
  let B : ℝ :=
    ‖Complex.Gamma ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖
  let X : ℝ := Real.cosh (Real.pi * (t - u))
  let Y : ℝ := Real.cosh (Real.pi * (t + u))
  let E : ℝ := Real.exp (2 * Real.pi * |u|)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hX : 0 < X := by dsimp only [X]; exact Real.cosh_pos _
  have hY : 0 < Y := by dsimp only [Y]; exact Real.cosh_pos _
  have hA2 : A ^ 2 = Real.pi / X := by
    simpa only [A, X] using Gamma_half_add_mul_I_norm_sq (t - u)
  have hB2 : B ^ 2 = Real.pi / Y := by
    simpa only [B, Y] using Gamma_half_add_mul_I_norm_sq (t + u)
  have hShift := smallContour_cosh_add_le_exp_abs_mul_cosh
    (Real.pi * (t - u)) (2 * Real.pi * u)
  have hArg : Real.pi * (t - u) + 2 * Real.pi * u =
      Real.pi * (t + u) := by ring
  have hAbs : |2 * Real.pi * u| = 2 * Real.pi * |u| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
  rw [hArg, hAbs] at hShift
  change Y ≤ E * X at hShift
  have hInv : X⁻¹ ≤ E * Y⁻¹ := by
    calc
      X⁻¹ = Y * (X * Y)⁻¹ := by field_simp
      _ ≤ (E * X) * (X * Y)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hShift
          (inv_nonneg.mpr (mul_nonneg hX.le hY.le))
      _ = E * Y⁻¹ := by field_simp
  have hExpSq : Real.exp (Real.pi * |u|) ^ 2 = E := by
    dsimp only [E]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hSquare : A ^ 2 ≤ Real.exp (Real.pi * |u|) ^ 2 * B ^ 2 := by
    rw [hA2, hB2, div_eq_mul_inv, div_eq_mul_inv, hExpSq]
    calc
      Real.pi * X⁻¹ ≤ Real.pi * (E * Y⁻¹) :=
        mul_le_mul_of_nonneg_left hInv Real.pi_pos.le
      _ = E * (Real.pi * Y⁻¹) := by ring
  rw [norm_div]
  exact (sq_le_sq₀ (div_nonneg hA hB.le) (Real.exp_pos _).le).mp (by
    rw [div_pow, div_le_iff₀ (pow_pos hB 2)]
    simpa only [A, B] using hSquare)

/-- Cancellation-preserving Gamma quotient on the literal small contour.
The Gaussian part of Hughes--Young's kernel will absorb the displayed
polynomial and logarithmic-displacement costs. -/
theorem exists_norm_Gamma_smallContour_movingQuotient_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u c : ℝ),
      0 ≤ c → c ≤ 1 / 3 →
      ‖Complex.Gamma
          (((1 / 2 : ℝ) - c : ℝ) + ((t - u : ℝ) : ℂ) * I + 1) /
          Complex.Gamma
            (((1 / 2 : ℝ) + c : ℝ) + ((t + u : ℝ) : ℂ) * I)‖ ≤
        (|t| + |u| + 2) * Real.exp (Real.pi * |u|) *
          Real.exp (C * c *
            (Real.log (|t - u| + 2) + Real.log (|t + u| + 2))) := by
  obtain ⟨Cminus, hCminus, hleft⟩ := exists_norm_Gamma_half_left_displacement_le
  obtain ⟨Cplus, hCplus, hright⟩ := exists_norm_inv_Gamma_half_right_displacement_le
  let C : ℝ := Cminus + Cplus
  have hC : 0 < C := add_pos hCminus hCplus
  refine ⟨C, hC, ?_⟩
  intro t u c hc0 hcUpper
  let zminus : ℂ := (1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I
  let zplus : ℂ := (1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I
  let Lminus : ℝ := Real.log (|t - u| + 2)
  let Lplus : ℝ := Real.log (|t + u| + 2)
  let R : ℝ := |t| + |u| + 2
  have hzminusRe : zminus.re = 1 / 2 := by simp [zminus]
  have hzplusRe : zplus.re = 1 / 2 := by simp [zplus]
  have hLminus : 0 ≤ Lminus := by
    dsimp only [Lminus]
    exact Real.log_nonneg (by linarith [abs_nonneg (t - u)])
  have hLplus : 0 ≤ Lplus := by
    dsimp only [Lplus]
    exact Real.log_nonneg (by linarith [abs_nonneg (t + u)])
  have hzminusC : zminus - (c : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [sub_re, ofReal_re, zero_re, hzminusRe] at hre
    linarith
  have hrec : Complex.Gamma (zminus - (c : ℂ) + 1) =
      (zminus - (c : ℂ)) * Complex.Gamma (zminus - (c : ℂ)) :=
    Complex.Gamma_add_one (zminus - (c : ℂ)) hzminusC
  have hzminusIm : zminus.im = t - u := by simp [zminus]
  have hzplusIm : zplus.im = t + u := by simp [zplus]
  have hleft' : ‖Complex.Gamma (zminus - (c : ℂ))‖ ≤
      ‖Complex.Gamma zminus‖ * Real.exp (Cminus * c * Lminus) := by
    have h := hleft zminus c hzminusRe hc0 hcUpper
    rw [hzminusIm] at h
    simpa only [Lminus] using h
  have hright' : ‖(Complex.Gamma (zplus + (c : ℂ)))⁻¹‖ ≤
      ‖(Complex.Gamma zplus)⁻¹‖ * Real.exp (Cplus * c * Lplus) := by
    have h := hright zplus c hzplusRe hc0 hcUpper
    rw [hzplusIm] at h
    simpa only [Lplus] using h
  have hzNorm : ‖zminus - (c : ℂ)‖ ≤ R := by
    calc
      ‖zminus - (c : ℂ)‖ ≤ |(zminus - (c : ℂ)).re| + |(zminus - (c : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |(1 / 2 : ℝ) - c| + |t - u| := by simp [zminus]
      _ ≤ (1 / 2 : ℝ) + (|t| + |u|) := by
        have hcHalf : |(1 / 2 : ℝ) - c| ≤ 1 / 2 := by
          rw [abs_le]
          constructor <;> linarith
        exact add_le_add hcHalf (by simpa using abs_sub_le t 0 u)
      _ ≤ R := by dsimp only [R]; linarith
  have hbase : ‖Complex.Gamma zminus‖ * ‖(Complex.Gamma zplus)⁻¹‖ ≤
      Real.exp (Real.pi * |u|) := by
    simpa only [zminus, zplus, norm_div, norm_inv] using
      norm_Gamma_half_t_sub_u_div_half_t_add_u_le t u
  have hExp :
      Real.exp (Cminus * c * Lminus) * Real.exp (Cplus * c * Lplus) ≤
        Real.exp (C * c * (Lminus + Lplus)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcross : 0 ≤ Cplus * c * Lminus + Cminus * c * Lplus :=
      add_nonneg (mul_nonneg (mul_nonneg hCplus.le hc0) hLminus)
        (mul_nonneg (mul_nonneg hCminus.le hc0) hLplus)
    dsimp only [C]
    nlinarith
  have hgoal : ‖Complex.Gamma (zminus - (c : ℂ) + 1) /
        Complex.Gamma (zplus + (c : ℂ))‖ ≤
      R * Real.exp (Real.pi * |u|) *
        Real.exp (C * c * (Lminus + Lplus)) := by
    rw [hrec, div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖zminus - (c : ℂ)‖ * ‖Complex.Gamma (zminus - (c : ℂ))‖ *
            ‖(Complex.Gamma (zplus + (c : ℂ)))⁻¹‖ ≤
          R * (‖Complex.Gamma zminus‖ * Real.exp (Cminus * c * Lminus)) *
            (‖(Complex.Gamma zplus)⁻¹‖ * Real.exp (Cplus * c * Lplus)) := by
        gcongr
      _ = R * (‖Complex.Gamma zminus‖ * ‖(Complex.Gamma zplus)⁻¹‖) *
            (Real.exp (Cminus * c * Lminus) * Real.exp (Cplus * c * Lplus)) := by ring
      _ ≤ R * Real.exp (Real.pi * |u|) *
            Real.exp (C * c * (Lminus + Lplus)) := by
        gcongr
  have hnum :
      (((1 / 2 : ℝ) - c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I + 1 =
        zminus - (c : ℂ) + 1 := by
    dsimp only [zminus]
    push_cast
    ring
  have hden :
      (((1 / 2 : ℝ) + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I =
        zplus + (c : ℂ) := by
    dsimp only [zplus]
    push_cast
    ring
  rw [hnum, hden]
  simpa only [Lminus, Lplus, R] using hgoal

set_option maxHeartbeats 1000000 in
/-- Every positive pair term on the literal Hughes--Young small contour is
Bochner integrable.  The proof uses the source small-line Gamma estimate and
keeps the two divisor coefficients independent of the Mellin ordinate. -/
theorem integrable_hughesYoungRightPairTerm_small
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Integrable (fun u : ℝ =>
      hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)) := by
  let c : ℝ := hughesYoungSmallContour T
  obtain ⟨hc, hc1, _hcinv⟩ := hughesYoungSmallContour_spec hT
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_height_power
  let Dm : ℝ :=
    ‖divisorDirichletTerm (afeCriticalPoint t + (c : ℂ)) m‖
  let Dn : ℝ :=
    ‖divisorDirichletTerm (afeCriticalPoint (-t) + (c : ℂ)) n‖
  let K : ℝ := c⁻¹ * T ^ (4 * C * c) * Dm * Dn
  have hT1 : 1 ≤ T := by
    exact (Real.one_le_exp (by norm_num)).trans hT
  have hfactor : Integrable (hughesYoungIntegratedOrdinateFactor C c) :=
    integrable_hughesYoungIntegratedOrdinateFactor hC hc hc1
  have hmajorant : Integrable (fun u : ℝ =>
      K * hughesYoungIntegratedOrdinateFactor C c u) := by
    exact hfactor.const_mul K
  have hcontinuous : Continuous (fun u : ℝ =>
      hughesYoungRightPairTerm t c u (m, n)) := by
    have hline : Continuous (fun u : ℝ => (c : ℂ) + (u : ℂ) * I) := by
      fun_prop
    have hcomp : Continuous (fun u : ℝ =>
        hughesYoungPairContourTerm t (m, n) ((c : ℂ) + (u : ℂ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro u
      exact (differentiableAt_hughesYoungPairContourTerm t (m, n)
        (by simpa using hc)).continuousAt.comp hline.continuousAt
    have heq : (fun u : ℝ =>
        hughesYoungPairContourTerm t (m, n) ((c : ℂ) + (u : ℂ) * I)) =
        fun u : ℝ => hughesYoungRightPairTerm t c u (m, n) := by
      funext u
      exact hughesYoungPairContourTerm_vertical t c u hm hn
    rw [← heq]
    exact hcomp
  refine hmajorant.mono' hcontinuous.aestronglyMeasurable ?_
  filter_upwards with u
  have hweight' := hweight T t u c hT1 ht hc hc1
  have hord :
      Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (6 * (|u| + 1))) *
          (25 + 8 * u ^ 2) ^ 8 ≤
        hughesYoungIntegratedOrdinateFactor C c u := by
    unfold hughesYoungIntegratedOrdinateFactor
    gcongr
    norm_num
  have hpairNorm :
      ‖hughesYoungRightPairTerm t c u (m, n)‖ =
        ‖hughesYoungRightContourWeight t c u‖ * Dm * Dn := by
    unfold hughesYoungRightPairTerm
    rw [norm_mul, norm_mul,
      norm_divisorDirichletTerm_afe_vertical,
      norm_divisorDirichletTerm_afe_vertical]
  rw [hpairNorm]
  calc
    ‖hughesYoungRightContourWeight t c u‖ * Dm * Dn ≤
        (c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8)) * Dm * Dn := by
      gcongr
    _ ≤ (c⁻¹ * T ^ (4 * C * c) *
          hughesYoungIntegratedOrdinateFactor C c u) * Dm * Dn := by
      gcongr
    _ = K * hughesYoungIntegratedOrdinateFactor C c u := by
      dsimp only [K]
      ring

end RiemannZeta.GuthMaynard
