import RiemannZeta.GuthMaynard.DFIEquation24
import RiemannZeta.GuthMaynard.DFIEquation28
import RiemannZeta.GuthMaynard.ArithmeticCoefficients
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DFI equation (29): effective dual-frequency truncation

This file proves the contour displacement and rapid frequency decay behind
the two inequalities in DFI equation (29).  The contour is moved one unit at
a time so that every horizontal side is controlled on a translated compact
Mellin strip.
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval
open Classical

namespace RiemannZeta.GuthMaynard

/-- Quantitative tail of a shifted real `p`-series.  This is the summation
lemma that turns the pointwise Mellin-contour decay in DFI (29) into an
effective dual-frequency truncation with an explicit power saving. -/
theorem tsum_nat_add_one_rpow_neg_le
    {L p : ℝ} (hL : 0 < L) (hp : 1 < p) :
    ∑' j : ℕ, (L + (j + 1 : ℕ)) ^ (-p) ≤ L ^ (1 - p) / (p - 1) := by
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact Real.rpow_nonneg (by positivity) _
  · intro N
    have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-p))
        (Set.Icc L (L + N)) := by
      exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
        (fun x hx ↦ hL.trans_le hx.1)
    have hsum :
        ∑ j ∈ Finset.range N, (L + (j + 1 : ℕ)) ^ (-p) ≤
          ∫ x in L..L + N, x ^ (-p) :=
      hanti.sum_le_integral
    have hzero_not_mem : (0 : ℝ) ∉ [[L, L + N]] := by
      rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg N))]
      exact fun hx ↦ hL.not_ge hx.1
    rw [integral_rpow
      (Or.inr ⟨by linarith, hzero_not_mem⟩)] at hsum
    calc
      ∑ j ∈ Finset.range N, (L + (j + 1 : ℕ)) ^ (-p) ≤
          (((L + N) ^ (-p + 1) - L ^ (-p + 1)) / (-p + 1)) := hsum
      _ = (L ^ (1 - p) - (L + N) ^ (1 - p)) / (p - 1) := by
        field_simp [show p - 1 ≠ 0 by linarith, show -p + 1 ≠ 0 by linarith]
        ring_nf
      _ ≤ L ^ (1 - p) / (p - 1) := by
        have hpow : 0 ≤ (L + N) ^ (1 - p) := Real.rpow_nonneg (by positivity) _
        have hden : 0 < p - 1 := by linarith
        apply (div_le_div_iff_of_pos_right hden).2
        linarith

private lemma dfiEquation29_zeroTendstoDiff
    (L₁ L₂ : ℂ) (f : ℝ → ℂ) (h : ∀ᶠ T in atTop, f T = 0)
    (h' : Tendsto f atTop (𝓝 (L₂ - L₁))) : L₁ = L₂ := by
  rw [← zero_add L₁, ← @eq_sub_iff_add_eq]
  exact tendsto_nhds_unique (EventuallyEq.tendsto h) h'

private lemma dfiEquation29_rectangle_tendsTo_vertical
    {σ σ' : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I))
      atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I))
      atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ - I * T) (σ' + I * T))
      atTop (𝓝 (VerticalIntegral f σ' - VerticalIntegral f σ)) := by
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im,
    one_mul, zero_add, zero_sub, add_im]
  apply Tendsto.sub
  · rewrite [← zero_add (VerticalIntegral _ _), ← zero_sub_zero]
    apply Tendsto.add <| Tendsto.sub (hbot.comp tendsto_neg_atTop_atBot) htop
    exact (intervalIntegral_tendsto_integral hright
      tendsto_neg_atTop_atBot tendsto_id).const_smul I
  · exact (intervalIntegral_tendsto_integral hleft
      tendsto_neg_atTop_atBot tendsto_id).const_smul I

private lemma dfiEquation29_verticalIntegral_eq
    {σ σ' : ℝ} {f : ℂ → ℂ}
    (hf : HolomorphicOn f ([[σ, σ']] ×ℂ univ))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I))
      atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I))
      atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    VerticalIntegral f σ = VerticalIntegral f σ' := by
  refine dfiEquation29_zeroTendstoDiff _ _ _ (univ_mem' fun _ ↦ ?_)
    (dfiEquation29_rectangle_tendsTo_vertical hbot htop hleft hright)
  exact integral_boundary_rect_eq_zero_of_differentiableOn f _ _
    (hf.mono fun z hrect ↦ ⟨by simpa using hrect.1, trivial⟩)

noncomputable def dfiEquation29Multiplier (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) : ℂ → ℂ :=
  match branch with
  | .minusTerm => dfiVoronoiMinusMultiplier q
  | .plusTerm => dfiVoronoiPlusMultiplier q

noncomputable def dfiEquation29Integrand (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ) ^ (-(1 - z)) * dfiEquation29Multiplier q branch z * mellin g z

noncomputable def dfiEquation29TransformAt (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) (σ : ℝ) : ℂ :=
  VerticalIntegral' (dfiEquation29Integrand q branch g n) σ

noncomputable def dfiEquation29InitialTransform (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  match branch with
  | .minusTerm => dfiVoronoiMinusTransform q (mellin g) n
  | .plusTerm => dfiVoronoiPlusTransform q (mellin g) n

theorem dfiEquation29TransformAt_initial (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29InitialTransform q branch g n := by
  cases branch <;>
    unfold dfiEquation29TransformAt dfiEquation29InitialTransform
      dfiVoronoiMinusTransform dfiVoronoiPlusTransform <;>
    apply congrArg (fun f : ℂ → ℂ => VerticalIntegral' f (-(1 / 2 : ℝ))) <;>
    funext z <;>
    unfold dfiEquation29Integrand dfiEquation29Multiplier <;>
    rw [show -(1 - z) = z - 1 by ring]

/-- Exact extraction of the modulus scale from the DFI archimedean factor. -/
theorem dfiPeriodicArchimedeanFactor_eq_modulus_cpow_mul_one
    (q : ℕ) [NeZero q] (s : ℂ) :
    dfiPeriodicArchimedeanFactor q s =
      (q : ℂ) ^ (s - 1) * dfiPeriodicArchimedeanFactor 1 s := by
  unfold dfiPeriodicArchimedeanFactor
  simp only [Nat.cast_one, one_cpow, one_mul]
  ring

/-- The full modulus dependence of either DFI dual multiplier is the single
power `q^(1-2z)`.  This identity is what makes the frequency scale in (29)
quantitative rather than hidden in an existential contour constant. -/
theorem dfiEquation29Multiplier_eq_modulus_cpow_mul_one
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) (z : ℂ) :
    dfiEquation29Multiplier q branch z =
      (q : ℂ) ^ (1 - 2 * z) * dfiEquation29Multiplier 1 branch z := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 =
      (q : ℂ) ^ (1 - 2 * z) := by
    calc
      (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 =
          (q : ℂ) ^ (1 : ℂ) * (q : ℂ) ^ (-z + -z) := by
            rw [pow_two, Complex.cpow_add _ _ hq0]
            simp
      _ = (q : ℂ) ^ ((1 : ℂ) + (-z + -z)) := by
            exact (Complex.cpow_add (1 : ℂ) (-z + -z) hq0).symm
      _ = (q : ℂ) ^ (1 - 2 * z) := by
            congr 1
            ring
  cases branch
  · simp only [dfiEquation29Multiplier, dfiVoronoiMinusMultiplier]
    rw [dfiPeriodicArchimedeanFactor_eq_modulus_cpow_mul_one]
    simp only [Nat.cast_one, one_mul]
    rw [show (1 - z - 1 : ℂ) = -z by ring]
    rw [show
      ((q : ℂ) ^ (-z) * dfiPeriodicArchimedeanFactor 1 (1 - z)) ^ 2 =
        ((q : ℂ) ^ (-z)) ^ 2 *
          dfiPeriodicArchimedeanFactor 1 (1 - z) ^ 2 by ring]
    rw [← hpow]
    ring
  · simp only [dfiEquation29Multiplier, dfiVoronoiPlusMultiplier]
    rw [dfiPeriodicArchimedeanFactor_eq_modulus_cpow_mul_one]
    simp only [Nat.cast_one]
    rw [show (1 - z - 1 : ℂ) = -z by ring]
    rw [show
      ((q : ℂ) ^ (-z) * dfiPeriodicArchimedeanFactor 1 (1 - z)) ^ 2 =
        ((q : ℂ) ^ (-z)) ^ 2 *
          dfiPeriodicArchimedeanFactor 1 (1 - z) ^ 2 by ring]
    rw [← hpow]
    ring

theorem differentiableAt_dfiEquation29Multiplier_of_re_lt_one
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiEquation29Multiplier q branch) z := by
  cases branch
  · exact differentiableAt_dfiVoronoiMinusMultiplier_of_re_lt_one q hz
  · exact differentiableAt_dfiVoronoiPlusMultiplier_of_re_lt_one q hz

theorem DFIVoronoiTestFunction.differentiableAt_dfiEquation29Integrand
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiEquation29Integrand q branch g n) z := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hExponent : DifferentiableAt ℂ (fun w : ℂ => -(1 - w)) z := by fun_prop
  have hPower : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ (-(1 - w))) z :=
    hExponent.const_cpow (Or.inl hn0)
  exact (hPower.mul
    (differentiableAt_dfiEquation29Multiplier_of_re_lt_one q branch hz)).mul
      (hg.differentiable_mellin z)

theorem dfiEquation29Multiplier_shifted_strip_bound
    (q k : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) - k ≤ σ → σ ≤ -(1 / 2 : ℝ) → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        C * (1 + |u|) ^ (2 * (k + 1)) := by
  obtain ⟨C, hC, hBoth⟩ :=
    exists_norm_dfiVoronoiMultipliers_shifted_strip_bound q k
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  cases branch
  · exact (hBoth σ hσLower (by linarith [hσUpper]) u).1
  · exact (hBoth σ hσLower (by linarith [hσUpper]) u).2

/-- Multiplier control on the right-shift strip `-1/2 ≤ Re z ≤ 1/2`. -/
theorem dfiEquation29Multiplier_half_strip_bound
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 1 / 2 → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  obtain ⟨C, hC, hBoth⟩ :=
    exists_norm_dfiVoronoiMultipliers_three_quarter_strip_bound q
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  cases branch
  · exact (hBoth σ hσLower (by linarith [hσUpper]) u).1
  · exact (hBoth σ hσLower (by linarith [hσUpper]) u).2

/-- Multiplier control on the full source strip
`-1/2 ≤ Re z ≤ 3/4`. -/
theorem dfiEquation29Multiplier_threeQuarter_strip_bound
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 4 → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  obtain ⟨C, hC, hBoth⟩ :=
    exists_norm_dfiVoronoiMultipliers_three_quarter_strip_bound q
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  cases branch
  · exact (hBoth σ hσLower hσUpper u).1
  · exact (hBoth σ hσLower hσUpper u).2

/-- On the retained-frequency line `Re z = 1/2`, the exact modulus factor
`q^(1-2z)` has norm one.  Hence the multiplier bound is uniform in `q`. -/
theorem exists_dfiEquation29Multiplier_half_line_uniform_bound
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_hq : NeZero q) (u : ℝ),
      ‖dfiEquation29Multiplier q branch
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  obtain ⟨C, hC, hOne⟩ :=
    dfiEquation29Multiplier_half_strip_bound 1 branch
  refine ⟨C, hC, ?_⟩
  intro q hq u
  letI : NeZero q := hq
  have hqPos : 0 < q := NeZero.pos q
  rw [dfiEquation29Multiplier_eq_modulus_cpow_mul_one, norm_mul,
    Complex.norm_natCast_cpow_of_pos hqPos]
  have hRe :
      (1 - 2 * ((1 / 2 : ℂ) + (u : ℂ) * I)).re = 0 := by simp
  rw [hRe, Real.rpow_zero, one_mul]
  simpa using hOne (1 / 2) (by norm_num) (by norm_num) u

/-- Uniform-in-the-modulus version of the shifted-strip multiplier bound.
The factor `q^(2+2k)` is the exact worst modulus power on the strip
`-1/2-k ≤ Re z ≤ -1/2`; unlike the earlier fixed-`q` estimate, its
constant is independent of `q`. -/
theorem exists_dfiEquation29Multiplier_explicit_modulus_bound
    (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_hq : NeZero q) (σ : ℝ),
      -(1 / 2 : ℝ) - k ≤ σ → σ ≤ -(1 / 2 : ℝ) → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (1 + |u|) ^ (2 * (k + 1)) := by
  obtain ⟨C, hC, hOne⟩ :=
    dfiEquation29Multiplier_shifted_strip_bound 1 k branch
  refine ⟨C, hC, ?_⟩
  intro q hq σ hσLower hσUpper u
  letI : NeZero q := hq
  have hqPos : 0 < q := NeZero.pos q
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqPos
  have hExponent : 1 - 2 * σ ≤ 2 + 2 * (k : ℝ) := by linarith
  have hqPower : (q : ℝ) ^ (1 - 2 * σ) ≤
      (q : ℝ) ^ (2 + 2 * (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hqOne hExponent
  rw [dfiEquation29Multiplier_eq_modulus_cpow_mul_one, norm_mul,
    Complex.norm_natCast_cpow_of_pos hqPos]
  have hRealPart :
      (1 - 2 * ((σ : ℂ) + (u : ℂ) * I)).re = 1 - 2 * σ := by simp
  rw [hRealPart]
  calc
    (q : ℝ) ^ (1 - 2 * σ) *
        ‖dfiEquation29Multiplier 1 branch ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      (q : ℝ) ^ (1 - 2 * σ) *
        (C * (1 + |u|) ^ (2 * (k + 1))) :=
      mul_le_mul_of_nonneg_left (hOne σ hσLower hσUpper u)
        (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    _ ≤ (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
        (C * (1 + |u|) ^ (2 * (k + 1))) := by
      gcongr
    _ = C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
        (1 + |u|) ^ (2 * (k + 1)) := by ring

/-- Normalize a positive-half-line test function by its physical scale.
The resulting support endpoints are dimensionless. -/
noncomputable def DFIVoronoiTestFunction.scaleNormalize
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) :
    DFIVoronoiTestFunction (fun x ↦ g (S * x)) where
  lower := hg.lower / S
  upper := hg.upper / S
  lower_pos := div_pos hg.lower_pos hS
  lower_le_upper := (div_le_div_iff_of_pos_right hS).2 hg.lower_le_upper
  smooth := hg.smooth.comp (by fun_prop)
  support_subset := by
    intro x hx
    have hs := hg.support_subset hx
    constructor
    · exact (div_le_iff₀ hS).2 (by simpa [mul_comm] using hs.1)
    · exact (le_div_iff₀ hS).2 (by simpa [mul_comm] using hs.2)

/-- Exact Mellin scaling used to expose the physical support scale in DFI
(29).  No asymptotic constant is hidden in this identity. -/
theorem mellin_eq_scale_cpow_mul_normalized
    (g : ℝ → ℂ) (S : ℝ) (hS : 0 < S) (z : ℂ) :
    mellin g z = (S : ℂ) ^ z * mellin (fun x ↦ g (S * x)) z := by
  have hscale := mellin_comp_mul_left g z hS
  rw [hscale]
  simp only [smul_eq_mul]
  have hSC : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  rw [← mul_assoc, ← Complex.cpow_add _ _ hSC]
  simp

/-- Elementary cancellation of a polynomial growth factor against four extra
powers of Mellin decay, in the integrable `1 / (1 + u²)` form. -/
theorem norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    {A B : ℝ} {p : ℕ} (hA : 0 ≤ A)
    {F G : ℂ} {u : ℝ}
    (hF : ‖F‖ ≤ A * (1 + |u|) ^ p)
    (hG : (1 + |u|) ^ (p + 4) * ‖G‖ ≤ B) :
    ‖F * G‖ ≤ A * B * (1 + u ^ 2)⁻¹ := by
  have hw : 0 < 1 + |u| := by positivity
  have hquad : 1 + u ^ 2 ≤ (1 + |u|) ^ 4 := by
    have huSq : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [abs_nonneg u, sq_nonneg (1 + |u|),
      mul_nonneg (sq_nonneg (1 + |u|)) (sq_nonneg (1 + |u|))]
  have hScale :
      (1 + u ^ 2) * (1 + |u|) ^ p ≤ (1 + |u|) ^ (p + 4) := by
    calc
      (1 + u ^ 2) * (1 + |u|) ^ p ≤
          (1 + |u|) ^ 4 * (1 + |u|) ^ p :=
        mul_le_mul_of_nonneg_right hquad (by positivity)
      _ = (1 + |u|) ^ (p + 4) := by rw [← pow_add]; ring_nf
  have hNormScaled : (1 + u ^ 2) * ‖F * G‖ ≤ A * B := by
    rw [norm_mul]
    calc
      (1 + u ^ 2) * (‖F‖ * ‖G‖) ≤
          (1 + u ^ 2) * (A * (1 + |u|) ^ p * ‖G‖) := by
        gcongr
      _ = A * (((1 + u ^ 2) * (1 + |u|) ^ p) * ‖G‖) := by ring
      _ ≤ A * ((1 + |u|) ^ (p + 4) * ‖G‖) := by gcongr
      _ ≤ A * B := mul_le_mul_of_nonneg_left hG hA
  rw [le_mul_inv_iff₀ (by positivity : 0 < 1 + u ^ 2)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hNormScaled

theorem DFIVoronoiTestFunction.integrable_dfiEquation29Integrand_vertical
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q k : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) {σ : ℝ}
    (hσLower : -(1 / 2 : ℝ) - k ≤ σ)
    (hσUpper : σ ≤ -(1 / 2 : ℝ)) :
    Integrable (fun u : ℝ => dfiEquation29Integrand q branch g n
      ((σ : ℂ) + (u : ℂ) * I)) := by
  let p : ℕ := 2 * (k + 1)
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_shifted_strip_bound q k branch
  obtain ⟨B, _, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_line_bound (p + 4) σ
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hMajor : Integrable (fun u : ℝ =>
      D * A * B * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using integrable_inv_one_add_sq.const_mul (D * A * B)
  have hCont : Continuous (fun u : ℝ => dfiEquation29Integrand q branch g n
      ((σ : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    let φ : ℝ → ℂ := fun v => (σ : ℂ) + (v : ℂ) * I
    have hφ : ContinuousAt φ u := by fun_prop
    have hout : ContinuousAt (dfiEquation29Integrand q branch g n) (φ u) :=
      (hg.differentiableAt_dfiEquation29Integrand q branch hn
        (by simp [φ]; linarith : (φ u).re < 1)).continuousAt
    exact hout.comp hφ
  apply hMajor.mono' hCont.aestronglyMeasurable
  filter_upwards with u
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le
    (hMultiplier σ hσLower hσUpper u)
    (hMellin u)
  rw [norm_mul] at hCore
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul, hPower]
  calc
    D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
      D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤
      D * (A * B * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore hD
    _ = D * A * B * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.exists_dfiEquation29Integrand_step_strip_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q r : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) - (r + 1) ≤ σ →
      σ ≤ -(1 / 2 : ℝ) - r → ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        C * (1 + u ^ 2)⁻¹ := by
  let k : ℕ := r + 1
  let p : ℕ := 2 * (k + 1)
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_shifted_strip_bound q k branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_shifted_strip_bound (p + 4) k
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro σ hσLower hσUpper u
  have hσGlobalLower : -(1 / 2 : ℝ) - k ≤ σ := by simpa [k] using hσLower
  have hσGlobalUpper : σ ≤ -(1 / 2 : ℝ) := by
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hσMellinUpper : σ ≤ (3 / 2 : ℝ) - k := by
    dsimp [k]
    norm_num at hσUpper ⊢
    linarith
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le
    (hMultiplier σ hσGlobalLower hσGlobalUpper u)
    (hMellin σ hσGlobalLower hσMellinUpper u)
  rw [norm_mul] at hCore
  have hPowerEq :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ =
        (n : ℝ) ^ (σ - 1) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ ≤ 1 := by
    rw [hPowerEq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnOne (by linarith)
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul]
  calc
    ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ *
        ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ *
        (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ 1 * (A * B * (1 + u ^ 2)⁻¹) :=
      mul_le_mul hPower hCore (by positivity) (by norm_num)
    _ = (A * B) * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.tendsto_dfiEquation29_horizontal_zero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q r : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in
        (-(1 / 2 : ℝ) - (r + 1))..(-(1 / 2 : ℝ) - r),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) ∧
    Tendsto (fun y : ℝ => ∫ x : ℝ in
        (-(1 / 2 : ℝ) - (r + 1))..(-(1 / 2 : ℝ) - r),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  obtain ⟨C, _, hDecay⟩ :=
    hg.exists_dfiEquation29Integrand_step_strip_decay q r branch hn
  let left : ℝ := -(1 / 2 : ℝ) - (r + 1)
  let right : ℝ := -(1 / 2 : ℝ) - r
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  let envelope : ℝ → ℝ := fun y => C * (1 + y ^ 2)⁻¹
  have hDen : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
  have hEnv : Tendsto envelope atTop (𝓝 0) := by
    dsimp [envelope]
    simpa [div_eq_mul_inv] using tendsto_const_nhds.div_atTop hDen
  have hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in left..right,
      f ((x : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards with y
      have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I))
        (C := envelope y) (fun x hx => by
          have hx' : x ∈ Set.uIcc left right := Set.uIoc_subset_uIcc hx
          have hleftRight : left ≤ right := by dsimp [left, right]; linarith
          rw [Set.uIcc_of_le hleftRight] at hx'
          have hxLower : -(1 / 2 : ℝ) - (r + 1) ≤ x := by
            simpa [left] using hx'.1
          have hxUpper : x ≤ -(1 / 2 : ℝ) - r := by
            simpa [right] using hx'.2
          simpa [f, envelope, left, right] using
            hDecay x hxLower hxUpper y)
      have hLength : |right - left| = 1 := by
        dsimp [left, right]
        norm_num
      simpa [hLength] using hInt
    · exact hEnv
  have hBottomTop : Tendsto (fun H : ℝ => ∫ x : ℝ in left..right,
      f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards with H
      have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x : ℝ => f ((x : ℂ) + ((-H : ℝ) : ℂ) * I))
        (C := envelope H) (fun x hx => by
          have hx' : x ∈ Set.uIcc left right := Set.uIoc_subset_uIcc hx
          have hleftRight : left ≤ right := by dsimp [left, right]; linarith
          rw [Set.uIcc_of_le hleftRight] at hx'
          have hxLower : -(1 / 2 : ℝ) - (r + 1) ≤ x := by
            simpa [left] using hx'.1
          have hxUpper : x ≤ -(1 / 2 : ℝ) - r := by
            simpa [right] using hx'.2
          have h := hDecay x hxLower hxUpper (-H)
          simpa [f, envelope] using h)
      have hLength : |right - left| = 1 := by
        dsimp [left, right]
        norm_num
      simpa [hLength] using hInt
    · exact hEnv
  constructor
  · simpa [left, right, f] using hTop
  · have hComp := hBottomTop.comp tendsto_neg_atBot_atTop
    have hfun :
        ((fun H : ℝ => ∫ x : ℝ in left..right,
          f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) ∘ Neg.neg) =
        (fun y : ℝ => ∫ x : ℝ in left..right,
          f ((x : ℂ) + (y : ℂ) * I)) := by
      funext y
      simp
    rw [hfun] at hComp
    simpa [left, right, f] using hComp

/-- One source-faithful unit displacement of the Mellin contour in DFI (29).
There are no residues: all factors are holomorphic throughout the closed strip,
and the horizontal sides vanish by the preceding uniform strip estimate. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_step
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q r : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n
        (-(1 / 2 : ℝ) - (r + 1)) =
      dfiEquation29TransformAt q branch g n
        (-(1 / 2 : ℝ) - r) := by
  let left : ℝ := -(1 / 2 : ℝ) - (r + 1)
  let right : ℝ := -(1 / 2 : ℝ) - r
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  have hleftRight : left ≤ right := by
    dsimp [left, right]
    linarith
  have hHol : HolomorphicOn f ([[left, right]] ×ℂ (Set.univ : Set ℝ)) := by
    intro z hz
    have hzRe : z.re ≤ right := by
      have hz' := hz.1
      rw [Set.uIcc_of_le hleftRight] at hz'
      exact hz'.2
    dsimp [right] at hzRe
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hzOne : z.re < 1 := by linarith
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn hzOne).differentiableWithinAt
  obtain ⟨hTop, hBot⟩ := hg.tendsto_dfiEquation29_horizontal_zero q r branch hn
  have hLeft : Integrable (fun u : ℝ => f ((left : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_vertical q (r + 1) branch hn
    · simp [left]
    · dsimp [left]
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
  have hRight : Integrable (fun u : ℝ => f ((right : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_vertical q (r + 1) branch hn
    · have hrSucc : (r : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast Nat.le_succ r
      dsimp [right]
      linarith
    · dsimp [right]
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
  have hVertical : VerticalIntegral f left = VerticalIntegral f right :=
    dfiEquation29_verticalIntegral_eq hHol
      (by simpa [left, right, f] using hBot)
      (by simpa [left, right, f] using hTop) hLeft hRight
  unfold dfiEquation29TransformAt VerticalIntegral'
  simpa [left, right, f] using congrArg
    (fun z : ℂ => (1 / (2 * Real.pi * I) : ℂ) * z) hVertical

/-- Iteration of the residue-free displacement.  This is the exact contour
identity used to obtain arbitrary power saving in the dual frequency. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_shift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q k : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29TransformAt q branch g n
        (-(1 / 2 : ℝ) - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
            dfiEquation29TransformAt q branch g n
              (-(1 / 2 : ℝ) - k) := ih
        _ = dfiEquation29TransformAt q branch g n
              (-(1 / 2 : ℝ) - (k + 1)) := by
          exact (hg.dfiEquation29TransformAt_step q k branch hn).symm
        _ = dfiEquation29TransformAt q branch g n
              (-(1 / 2 : ℝ) - (Nat.succ k)) := by simp

theorem DFIVoronoiTestFunction.integrable_dfiEquation29Integrand_right_vertical
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) {σ : ℝ}
    (hσLower : -(1 / 2 : ℝ) ≤ σ) (hσUpper : σ ≤ 3 / 4) :
    Integrable (fun u : ℝ => dfiEquation29Integrand q branch g n
      ((σ : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_threeQuarter_strip_bound q branch
  obtain ⟨B, _, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_line_bound 6 σ
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hMajor : Integrable (fun u : ℝ =>
      D * A * B * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using integrable_inv_one_add_sq.const_mul (D * A * B)
  have hCont : Continuous (fun u : ℝ => dfiEquation29Integrand q branch g n
      ((σ : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    let φ : ℝ → ℂ := fun v => (σ : ℂ) + (v : ℂ) * I
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn
      (by simp [φ]; linarith : (φ u).re < 1)).continuousAt.comp (by fun_prop)
  apply hMajor.mono' hCont.aestronglyMeasurable
  filter_upwards with u
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le (hMultiplier σ hσLower hσUpper u) (hMellin u)
  rw [norm_mul] at hCore
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul, hPower]
  calc
    D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
      D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ D * (A * B * (1 + u ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hCore hD
    _ = D * A * B * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.exists_dfiEquation29Integrand_right_strip_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 4 → ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + u ^ 2)⁻¹ := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_threeQuarter_strip_bound q branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_shifted_strip_bound 6 0
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro σ hσLower hσUpper u
  have hσMellinUpper : σ ≤ (3 / 2 : ℝ) := by linarith
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le (hMultiplier σ hσLower hσUpper u)
      (hMellin σ (by simpa using hσLower) (by simpa using hσMellinUpper) u)
  rw [norm_mul] at hCore
  have hPowerEq :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ =
        (n : ℝ) ^ (σ - 1) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ ≤ 1 := by
    rw [hPowerEq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnOne (by linarith)
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul]
  calc
    ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ *
        ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ *
        (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ 1 * (A * B * (1 + u ^ 2)⁻¹) :=
      mul_le_mul hPower hCore (by positivity) (by norm_num)
    _ = (A * B) * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.tendsto_dfiEquation29_half_horizontal_zero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) ∧
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  obtain ⟨C, _, hDecay⟩ :=
    hg.exists_dfiEquation29Integrand_right_strip_decay q branch hn
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  let envelope : ℝ → ℝ := fun y => C * (1 + y ^ 2)⁻¹
  have hDen : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
  have hEnv : Tendsto envelope atTop (𝓝 0) := by
    dsimp [envelope]
    simpa [div_eq_mul_inv] using tendsto_const_nhds.div_atTop hDen
  have boundIntegral : ∀ y : ℝ,
      ‖∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          f ((x : ℂ) + (y : ℂ) * I)‖ ≤ envelope y := by
    intro y
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I))
      (C := envelope y) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] at hx'
        simpa [f, envelope] using hDecay x hx'.1 hx'.2 y)
    norm_num at hInt ⊢
    simpa using hInt
  have hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(1 / 2 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall boundIntegral) hEnv
  have hBottomTop : Tendsto (fun H : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(1 / 2 : ℝ), f ((x : ℂ) + ((-H : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun H => ?_) hEnv
    simpa [envelope] using boundIntegral (-H)
  constructor
  · simpa [f] using hTop
  · have hComp := hBottomTop.comp tendsto_neg_atBot_atTop
    simpa [f, Function.comp_def] using hComp

/-- The horizontal sides of the source rectangle from `Re z = -1/2` to
`Re z = 3/4` vanish. -/
theorem DFIVoronoiTestFunction.tendsto_dfiEquation29_threeQuarter_horizontal_zero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(3 / 4 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atTop (ℕ 0) ∧
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(3 / 4 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atBot (ℕ 0) := by
  obtain ⟨C, _, hDecay⟩ :=
    hg.exists_dfiEquation29Integrand_right_strip_decay q branch hn
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  let envelope : ℝ → ℝ := fun y => (5 / 4 : ℝ) * C * (1 + y ^ 2)⁻¹
  have hDen : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
  have hEnv : Tendsto envelope atTop (ℕ 0) := by
    dsimp [envelope]
    simpa [div_eq_mul_inv, mul_assoc] using
      tendsto_const_nhds.div_atTop hDen
  have boundIntegral : ∀ y : ℝ,
      ‖∫ x : ℝ in (-(1 / 2 : ℝ))..(3 / 4 : ℝ),
          f ((x : ℂ) + (y : ℂ) * I)‖ ≤ envelope y := by
    intro y
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I))
      (C := C * (1 + y ^ 2)⁻¹) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 4)] at hx'
        simpa [f] using hDecay x hx'.1 hx'.2 y)
    norm_num at hInt ⊢
    simpa [envelope, mul_assoc] using hInt
  have hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(3 / 4 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (ℕ 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall boundIntegral) hEnv
  have hBottomTop : Tendsto (fun H : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(3 / 4 : ℝ),
        f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) atTop (ℕ 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun H => ?_) hEnv
    simpa [envelope] using boundIntegral (-H)
  constructor
  · simpa [f] using hTop
  · have hComp := hBottomTop.comp tendsto_neg_atBot_atTop
    simpa [f, Function.comp_def] using hComp

/-- Residue-free displacement from the initial Voronoi line to DFI's
retained-frequency line `Re z = 3/4`. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_threeQuarter
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29TransformAt q branch g n (3 / 4 : ℝ) := by
  let left : ℝ := -(1 / 2 : ℝ)
  let right : ℝ := 3 / 4
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  have hHol : HolomorphicOn f ([[left, right]] ×ℂ (Set.univ : Set ℝ)) := by
    intro z hz
    have hzRe : z.re ≤ right := by
      have hz' := hz.1
      rw [Set.uIcc_of_le (by norm_num : left ≤ right)] at hz'
      exact hz'.2
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn
      (by dsimp [right] at hzRe; linarith)).differentiableWithinAt
  obtain ⟨hTop, hBot⟩ :=
    hg.tendsto_dfiEquation29_threeQuarter_horizontal_zero q branch hn
  have hLeft : Integrable (fun u : ℝ => f ((left : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · simp [left]
    · norm_num [left]
  have hRight : Integrable (fun u : ℝ => f ((right : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · norm_num [right]
    · simp [right]
  have hVertical : VerticalIntegral f left = VerticalIntegral f right :=
    dfiEquation29_verticalIntegral_eq hHol
      (by simpa [left, right, f] using hBot)
      (by simpa [left, right, f] using hTop) hLeft hRight
  unfold dfiEquation29TransformAt VerticalIntegral'
  simpa [left, right, f] using congrArg
    (fun z : ℂ => (1 / (2 * Real.pi * I) : ℂ) * z) hVertical

/-- Residue-free rightward displacement from the source line `Re z=-1/2`
to the retained-frequency line `Re z=1/2`. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_half
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) := by
  let left : ℝ := -(1 / 2 : ℝ)
  let right : ℝ := 1 / 2
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  have hHol : HolomorphicOn f ([[left, right]] ×ℂ (Set.univ : Set ℝ)) := by
    intro z hz
    have hzRe : z.re ≤ right := by
      have hz' := hz.1
      rw [Set.uIcc_of_le (by norm_num : left ≤ right)] at hz'
      exact hz'.2
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn
      (by dsimp [right] at hzRe; linarith)).differentiableWithinAt
  obtain ⟨hTop, hBot⟩ := hg.tendsto_dfiEquation29_half_horizontal_zero q branch hn
  have hLeft : Integrable (fun u : ℝ => f ((left : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · simp [left]
    · norm_num [left]
  have hRight : Integrable (fun u : ℝ => f ((right : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · norm_num [right]
    · simp [right]
  have hVertical : VerticalIntegral f left = VerticalIntegral f right :=
    dfiEquation29_verticalIntegral_eq hHol
      (by simpa [left, right, f] using hBot)
      (by simpa [left, right, f] using hTop) hLeft hRight
  unfold dfiEquation29TransformAt VerticalIntegral'
  simpa [left, right, f] using congrArg
    (fun z : ℂ => (1 / (2 * Real.pi * I) : ℂ) * z) hVertical

theorem DFIVoronoiTestFunction.exists_mellin_scaled_half_line_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (S : ℝ) (hS : 0 < S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      (1 + |u|) ^ 6 * ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
        S ^ (1 / 2 : ℝ) * B := by
  let g₁ : ℝ → ℂ := fun x ↦ g (S * x)
  have hg₁ : DFIVoronoiTestFunction g₁ := by
    simpa [g₁] using hg.scaleNormalize S hS
  obtain ⟨B, hB, hMellin⟩ :=
    hg₁.exists_mellin_one_add_abs_pow_line_bound 6 (1 / 2)
  refine ⟨B, hB, ?_⟩
  intro u
  let R : ℝ := S ^ (1 / 2 : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg hS.le _
  rw [mellin_eq_scale_cpow_mul_normalized g S hS, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hS]
  have hRe : (((1 / 2 : ℂ) + (u : ℂ) * I).re) = (1 / 2 : ℝ) := by simp
  rw [hRe]
  change (1 + |u|) ^ 6 *
      (R * ‖mellin g₁ ((1 / 2 : ℂ) + (u : ℂ) * I)‖) ≤ R * B
  calc
    (1 + |u|) ^ 6 *
        (R * ‖mellin g₁ ((1 / 2 : ℂ) + (u : ℂ) * I)‖) =
      R * ((1 + |u|) ^ 6 *
        ‖mellin g₁ ((1 / 2 : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ R * B := by
      have hm : (1 + |u|) ^ 6 *
          ‖mellin g₁ ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ B := by
        simpa using hMellin u
      exact mul_le_mul_of_nonneg_left hm hR

theorem DFIVoronoiTestFunction.exists_dfiEquation29Integrand_scaled_half_line_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n → ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
        C * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (1 + u ^ 2)⁻¹ := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_half_line_uniform_bound branch
  obtain ⟨B, hB, hMellin⟩ := hg.exists_mellin_scaled_half_line_bound S hS
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro q hq n hn u
  letI : NeZero q := hq
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le (hMultiplier q hq u) (hMellin u)
  rw [norm_mul] at hCore
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + (u : ℂ) * I)))‖ =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    norm_num
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul, hPower]
  calc
    (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖dfiEquation29Multiplier q branch ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        (‖dfiEquation29Multiplier q branch ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        (A * (S ^ (1 / 2 : ℝ) * B) * (1 + u ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hCore
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (A * B) * S ^ (1 / 2 : ℝ) *
        (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.norm_dfiEquation29TransformAt_half_le_of_pointwise
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (D : ℝ)
    (hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ D * (1 + u ^ 2)⁻¹) :
    ‖dfiEquation29TransformAt q branch g n (1 / 2 : ℝ)‖ ≤
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D *
        (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
  have hTargetInt : Integrable (fun u : ℝ =>
      ‖dfiEquation29Integrand q branch g n
        ((1 / 2 : ℂ) + (u : ℂ) * I)‖) := by
    have hInt := hg.integrable_dfiEquation29Integrand_right_vertical
      (σ := (1 / 2 : ℝ)) q branch hn (by norm_num) (by norm_num)
    simpa using hInt.norm
  have hMajorInt : Integrable (fun u : ℝ => D * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul D
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖) ≤
        D * (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, D * (1 + u ^ 2)⁻¹ :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = D * (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
        rw [MeasureTheory.integral_const_mul]
  calc
    ‖dfiEquation29TransformAt q branch g n (1 / 2 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
            ((1 / 2 : ℂ) + (u : ℂ) * I)‖ :=
      by
        unfold dfiEquation29TransformAt
        simpa using norm_verticalIntegral'_le_integral_norm
          (dfiEquation29Integrand q branch g n) (1 / 2 : ℝ)
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (D * (∫ u : ℝ, (1 + u ^ 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D *
        (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by ring

/-- Universal right-contour constant for Equation (29).  It is selected
before the test function and its Mellin bound, so later arithmetic slices
cannot alter it. -/
theorem exists_dfiEquation29InitialTransform_retained_constant
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : ℝ → ℂ}, DFIVoronoiTestFunction g →
      ∀ {B : ℝ}, (∀ u : ℝ,
        (1 + |u|) ^ 6 *
          ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ B) →
      ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform q branch g n‖ ≤
          C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_half_line_uniform_bound branch
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro g hg B hMellin q hq n hn
  letI : NeZero q := hq
  let D : ℝ := A * B * (n : ℝ) ^ (-(1 / 2 : ℝ))
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ D * (1 + u ^ 2)⁻¹ := by
    intro u
    have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
      hA.le (hMultiplier q hq u) (hMellin u)
    rw [norm_mul] at hCore
    have hPower :
        ‖(n : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + (u : ℂ) * I)))‖ =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      norm_num
    unfold dfiEquation29Integrand
    rw [norm_mul, norm_mul, hPower]
    calc
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          ‖dfiEquation29Multiplier q branch ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
            ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (‖dfiEquation29Multiplier q branch ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
            ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (A * B * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = D * (1 + u ^ 2)⁻¹ := by
        dsimp [D]
        ring
  have hHalf := hg.norm_dfiEquation29TransformAt_half_le_of_pointwise
    q branch hn D hPoint
  have hShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) :=
        hg.dfiEquation29TransformAt_half q branch hn
  rw [hShift]
  calc
    ‖dfiEquation29TransformAt q branch g n (1 / 2 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D * J := by
      simpa [J] using hHalf
    _ = C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      dsimp [C, D]
      ring

/-- Right-contour estimate with an explicit Mellin-decay input.  The output
constant depends only on the fixed Voronoi branch and universal vertical
integral, while all source dependence remains visible in `B`. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_retained_of_mellin_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (branch : DFIVoronoiDualBranch) {B : ℝ}
    (hMellin : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q)
      (n : ℕ), 0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hUniversal⟩ :=
    exists_dfiEquation29InitialTransform_retained_constant branch
  exact ⟨C, hC, hUniversal hg hMellin⟩

/-- Scale-uniform retained-frequency estimate obtained on `Re z = 1/2`.
The modulus disappears exactly on this line; the physical scale and dual
frequency contribute `S^(1/2)` and `n^(-1/2)`, respectively. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_scaled_retained_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hPoint⟩ :=
    hg.exists_dfiEquation29Integrand_scaled_half_line_bound S hS branch
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  let D : ℝ := A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
  have hHalf := hg.norm_dfiEquation29TransformAt_half_le_of_pointwise
    q branch hn D (fun u => by simpa [D] using hPoint q hq n hn u)
  have hShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) :=
        hg.dfiEquation29TransformAt_half q branch hn
  rw [hShift]
  calc
    ‖dfiEquation29TransformAt q branch g n (1 / 2 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D * J := by
      simpa [J] using hHalf
    _ = C * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      dsimp [C, D]
      ring

/-- Arbitrary polynomial decay of either DFI dual transform.  The constant is
uniform in the positive dual frequency `n`; its dependence on the modulus,
branch, test function, and chosen decay order is explicit in the binders. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q k : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  let σ : ℝ := -(1 / 2 : ℝ) - k
  let p : ℕ := 2 * (k + 1)
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_shifted_strip_bound q k branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_line_bound (p + 4) σ
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * B * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u => inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hσLower : -(1 / 2 : ℝ) - k ≤ σ := by simp [σ]
  have hσUpper : σ ≤ -(1 / 2 : ℝ) := by
    dsimp [σ]
    exact sub_le_self _ (Nat.cast_nonneg k)
  have hTargetInt : Integrable (fun u : ℝ =>
      ‖dfiEquation29Integrand q branch g n
        ((σ : ℂ) + (u : ℂ) * I)‖) :=
    (hg.integrable_dfiEquation29Integrand_vertical q k branch hn
      hσLower hσUpper).norm
  have hMajorInt : Integrable (fun u : ℝ =>
      D * A * B * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using integrable_inv_one_add_sq.const_mul (D * A * B)
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        D * A * B * (1 + u ^ 2)⁻¹ := by
    intro u
    have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
      hA.le
      (hMultiplier σ hσLower hσUpper u)
      (hMellin u)
    rw [norm_mul] at hCore
    have hPower :
        ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      simp
    unfold dfiEquation29Integrand
    rw [norm_mul, norm_mul, hPower]
    calc
      D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
        D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ D * (A * B * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore hD
      _ = D * A * B * (1 + u ^ 2)⁻¹ := by ring
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤ D * A * B * J := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, D * A * B * (1 + u ^ 2)⁻¹ :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = D * A * B * J := by
        rw [MeasureTheory.integral_const_mul]
  have hInitialShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n σ := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n σ := by
        simpa [σ] using hg.dfiEquation29TransformAt_shift q k branch hn
  have hD_eq : D = (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
    dsimp [D, σ]
    congr 1
    ring
  rw [hInitialShift]
  calc
    ‖dfiEquation29TransformAt q branch g n σ‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
            ((σ : ℂ) + (u : ℂ) * I)‖ :=
      norm_verticalIntegral'_le_integral_norm _ _
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ * (D * A * B * J) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = C * (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
      rw [hD_eq]
      dsimp [C]
      ring

/-- Scale-explicit form of DFI (29).  After normalizing a test function at
physical scale `S`, the constant is uniform in the modulus and positive dual
frequency.  The displayed factor is
`q^(2+2k) S^(-1/2-k) n^(-3/2-k)`, so every further contour displacement gains
the source ratio `q²/(nS)`. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_scaled_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ),
      0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  let σ : ℝ := -(1 / 2 : ℝ) - k
  let p : ℕ := 2 * (k + 1)
  let g₁ : ℝ → ℂ := fun x ↦ g (S * x)
  have hg₁ : DFIVoronoiTestFunction g₁ := by
    simpa [g₁] using hg.scaleNormalize S hS
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_explicit_modulus_bound k branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg₁.exists_mellin_one_add_abs_pow_line_bound (p + 4) σ
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * B * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  let Qk : ℝ := (q : ℝ) ^ (2 + 2 * (k : ℝ))
  let Sk : ℝ := S ^ σ
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hQk : 0 ≤ Qk := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hSk : 0 ≤ Sk := Real.rpow_nonneg hS.le _
  have hσLower : -(1 / 2 : ℝ) - k ≤ σ := by simp [σ]
  have hσUpper : σ ≤ -(1 / 2 : ℝ) := by
    dsimp [σ]
    exact sub_le_self _ (Nat.cast_nonneg k)
  have hMellinScaled : ∀ u : ℝ,
      (1 + |u|) ^ (p + 4) *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ Sk * B := by
    intro u
    rw [mellin_eq_scale_cpow_mul_normalized g S hS, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hS]
    have hRe : (((σ : ℂ) + (u : ℂ) * I).re) = σ := by simp
    rw [hRe]
    change (1 + |u|) ^ (p + 4) *
        (Sk * ‖mellin g₁ ((σ : ℂ) + (u : ℂ) * I)‖) ≤ Sk * B
    calc
      (1 + |u|) ^ (p + 4) *
          (Sk * ‖mellin g₁ ((σ : ℂ) + (u : ℂ) * I)‖) =
        Sk * ((1 + |u|) ^ (p + 4) *
          ‖mellin g₁ ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ Sk * B := mul_le_mul_of_nonneg_left (hMellin u) hSk
  have hTargetInt : Integrable (fun u : ℝ ↦
      ‖dfiEquation29Integrand q branch g n
        ((σ : ℂ) + (u : ℂ) * I)‖) :=
    (hg.integrable_dfiEquation29Integrand_vertical q k branch hn
      hσLower hσUpper).norm
  have hMajorInt : Integrable (fun u : ℝ ↦
      D * (A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using
      integrable_inv_one_add_sq.const_mul (D * (A * Qk) * (Sk * B))
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        D * (A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹ := by
    intro u
    have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
      (mul_nonneg hA.le hQk)
      (by simpa [Qk, p, mul_assoc] using
        hMultiplier q hq σ hσLower hσUpper u)
      (hMellinScaled u)
    rw [norm_mul] at hCore
    have hPower :
        ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      simp
    unfold dfiEquation29Integrand
    rw [norm_mul, norm_mul, hPower]
    calc
      D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
        D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ D * ((A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore hD
      _ = D * (A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹ := by ring
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤
        D * (A * Qk) * (Sk * B) * J := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, D * (A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹ :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = D * (A * Qk) * (Sk * B) * J := by
        rw [MeasureTheory.integral_const_mul]
  have hInitialShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n σ := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n σ := by
        simpa [σ] using hg.dfiEquation29TransformAt_shift q k branch hn
  have hD_eq : D = (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
    dsimp [D, σ]
    congr 1
    ring
  have hSk_eq : Sk = S ^ (-(1 / 2 : ℝ) - k) := by rfl
  rw [hInitialShift]
  calc
    ‖dfiEquation29TransformAt q branch g n σ‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
            ((σ : ℂ) + (u : ℂ) * I)‖ :=
      norm_verticalIntegral'_le_integral_norm _ _
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (D * (A * Qk) * (Sk * B) * J) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
        S ^ (-(1 / 2 : ℝ) - k) *
          (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
      rw [hD_eq, hSk_eq]
      dsimp [C, Qk]
      ring

/-- The residue-independent Voronoi summand is the divisor weight times the
equation-(29) initial transform. -/
theorem dfiVoronoiDualTerm_eq_divisorWeight_mul_initial
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (n : ℕ) :
    dfiVoronoiDualTerm q branch g n =
      divisorWeight n * dfiEquation29InitialTransform q branch g n := by
  cases branch <;> rfl

/-- Retained-frequency version of DFI (29), after inserting the native
divisor estimate with exponent `1/4`. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_scaled_retained_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        C * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨A, hA, hTransform⟩ :=
    hg.exists_dfiEquation29InitialTransform_scaled_retained_bound S hS branch
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native (1 / 4 : ℝ) (by norm_num)
  refine ⟨D * A, mul_nonneg hD.le hA, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ (1 / 4 : ℝ) := by
    simpa [divisorWeight] using hDivisor n hn
  have hTransform' := hTransform q hq n hn
  calc
    ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
        (D * (n : ℝ) ^ (1 / 4 : ℝ)) *
          (A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul hWeight hTransform' (norm_nonneg _)
        (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = (D * A) * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      calc
        (D * (n : ℝ) ^ (1 / 4 : ℝ)) *
            (A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) =
          ((D * A) * S ^ (1 / 2 : ℝ)) *
            ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
        _ = ((D * A) * S ^ (1 / 2 : ℝ)) *
            (n : ℝ) ^ ((1 / 4 : ℝ) + (-(1 / 2 : ℝ))) := by
          rw [Real.rpow_add (Nat.cast_pos.mpr hn)]
        _ = (D * A) * S ^ (1 / 2 : ℝ) *
            (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
          congr 1
          ring_nf

/-- DFI (29) after inserting the native divisor-function estimate.  The
constant remains uniform in the modulus and positive dual frequency. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_scaled_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ),
      0 < n →
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
  obtain ⟨A, hA, hTransform⟩ :=
    hg.exists_dfiEquation29InitialTransform_scaled_decay S hS k branch
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native (1 / 2 : ℝ) (by norm_num)
  refine ⟨D * A, mul_nonneg hD.le hA, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [divisorWeight] using hDivisor n hn
  have hTransform' := hTransform q hq n hn
  calc
    ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
        (D * (n : ℝ) ^ (1 / 2 : ℝ)) *
          (A * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
            S ^ (-(1 / 2 : ℝ) - k) *
              (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) :=
      mul_le_mul hWeight hTransform' (norm_nonneg _)
        (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = (D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
      calc
        (D * (n : ℝ) ^ (1 / 2 : ℝ)) *
            (A * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
              S ^ (-(1 / 2 : ℝ) - k) *
                (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) =
            ((D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
              S ^ (-(1 / 2 : ℝ) - k)) *
                ((n : ℝ) ^ (1 / 2 : ℝ) *
                  (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) := by ring_nf
        _ = ((D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
              S ^ (-(1 / 2 : ℝ) - k)) *
                (n : ℝ) ^ ((1 / 2 : ℝ) + (-(3 / 2 : ℝ) - k)) := by
              rw [Real.rpow_add (Nat.cast_pos.mpr hn)]
        _ = (D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
              S ^ (-(1 / 2 : ℝ) - k) *
                (n : ℝ) ^ (-(1 : ℝ) - k) := by
              congr 1
              ring_nf

/-- Summed, quantitative form of DFI (29).  Frequencies strictly beyond `L`
have total norm bounded by the displayed power tail.  Choosing
`L` larger than the transition scale `q²/S` by a small power and then taking
`k` large gives the arbitrary power saving used in the source. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_tail_scaled_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
      ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    hg.exists_dfiVoronoiDualTerm_scaled_decay S hS k branch
  refine ⟨C, hC, ?_⟩
  intro q L hq hL
  letI : NeZero q := hq
  let B : ℝ := C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
    S ^ (-(1 / 2 : ℝ) - k)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hSeries := tsum_nat_add_one_rpow_neg_le
    (L := (L : ℝ)) (p := 1 + (k : ℝ))
    (Nat.cast_pos.mpr hL) (by
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      linarith)
  have hSeries' :
      ∑' j : ℕ, ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) ≤
        (L : ℝ) ^ (-(k : ℝ)) / (k : ℝ) := by
    convert hSeries using 1
    all_goals ring_nf
  have hPowerSummable : Summable (fun j : ℕ ↦
      ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ)))) := by
    have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(1 + (k : ℝ)))) :=
      Real.summable_nat_rpow.mpr (by
        have hk' : (0 : ℝ) < k := by exact_mod_cast hk
        linarith)
    have hshift := (summable_nat_add_iff (L + 1)).2 hbase
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hshift
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact norm_nonneg _
  · intro N
    calc
      ∑ j ∈ Finset.range N,
          ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖ ≤
          ∑ j ∈ Finset.range N,
            B * ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
        gcongr with j hj
        have hn : 0 < L + (j + 1) := by omega
        have hpnt := hPoint q hq (L + (j + 1)) hn
        have hexp : -(1 + (k : ℝ)) = -(1 : ℝ) - k := by ring_nf
        dsimp [B]
        rw [hexp]
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hpnt
      _ = B * ∑ j ∈ Finset.range N,
            ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ B * ∑' j : ℕ,
            ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
          gcongr
          exact hPowerSummable.sum_le_tsum
            (Finset.range N) (fun j _ ↦ Real.rpow_nonneg (by positivity) _)
      _ ≤ B * ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hSeries' hB
      _ = C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by rfl

/-- Effective transition-scale version of DFI (29).  If the retained dual
window extends past `(q²/S) R`, then the discarded tail gains the factor
`((q²/S) R)^(-k)`.  This is the precise quantified form in which the paper
takes `R` to be a small power of its global parameter and then chooses `k`
arbitrarily large. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_tail_of_transition
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q L : ℕ) (_hq : NeZero q) (R : ℝ), 0 < L → 0 < R →
        (q : ℝ) ^ 2 / S * R ≤ L →
        ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖ ≤
          C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
            S ^ (-(1 / 2 : ℝ) - k) *
              (((q : ℝ) ^ 2 / S * R) ^ (-(k : ℝ))) := by
  obtain ⟨C, hC, hTail⟩ :=
    hg.exists_dfiVoronoiDualTerm_tail_scaled_decay S hS k hk branch
  refine ⟨C, hC, ?_⟩
  intro q L hq R hL hR hcut
  letI : NeZero q := hq
  have hqPos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have htransition : 0 < (q : ℝ) ^ 2 / S * R := by positivity
  have hkNonpos : -(k : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg k)
  have hpow : (L : ℝ) ^ (-(k : ℝ)) ≤
      ((q : ℝ) ^ 2 / S * R) ^ (-(k : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos htransition hcut hkNonpos
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdiv : (L : ℝ) ^ (-(k : ℝ)) / (k : ℝ) ≤
      (L : ℝ) ^ (-(k : ℝ)) :=
    div_le_self (Real.rpow_nonneg (Nat.cast_nonneg L) _) hkOne
  have hfactor : 0 ≤ C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
      S ^ (-(1 / 2 : ℝ) - k) := by positivity
  exact (hTail q L hq hL).trans
    (mul_le_mul_of_nonneg_left (hdiv.trans hpow) hfactor)

/-- Equation (29), first-variable source entry: the literal localized
equation-(23) slice has physical scale `X/a`, and its two Voronoi transforms
therefore gain the exact ratio `r²/(m(X/a))` per contour displacement. -/
theorem exists_dfiEquation29_xSlice_scaled_decay
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (y : ℝ) (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ) (_hr : NeZero r) (m : ℕ), 0 < m →
      ‖dfiEquation29InitialTransform r branch
          (fun x ↦ dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x y) m‖ ≤
        C * (r : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (X / a) ^ (-(1 / 2 : ℝ) - k) *
            (m : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  have hScale : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  exact (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    |>.exists_dfiEquation29InitialTransform_scaled_decay
      (X / a) hScale k branch

/-- Equation (29), first-variable source tail.  This is the actual localized
equation-(23) test function, not an independently supplied smooth function. -/
theorem exists_dfiEquation29_xSlice_tail_scaled_decay
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (y : ℝ) (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r), 0 < L →
      ∑' j : ℕ, ‖dfiVoronoiDualTerm r branch
          (fun x ↦ dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x y) (L + (j + 1))‖ ≤
        C * (r : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (X / a) ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  have hScale : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  exact (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    |>.exists_dfiVoronoiDualTerm_tail_scaled_decay
      (X / a) hScale k hk branch

/-- Equation (29), second-variable source entry, with physical scale `Y/b`.
This is the symmetric consumer needed before the double-dual branch of (24)
is estimated. -/
theorem exists_dfiEquation29_ySlice_scaled_decay
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (hb : 0 < b) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (x : ℝ) (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ) (_hr : NeZero r) (n : ℕ), 0 < n →
      ‖dfiEquation29InitialTransform r branch
          (dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x) n‖ ≤
        C * (r : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (Y / b) ^ (-(1 / 2 : ℝ) - k) *
            (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  have hScale : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
  exact (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    |>.exists_dfiEquation29InitialTransform_scaled_decay
      (Y / b) hScale k branch

/-- Equation (29), second-variable source tail, symmetric to the preceding
first-variable theorem. -/
theorem exists_dfiEquation29_ySlice_tail_scaled_decay
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (hb : 0 < b) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (x : ℝ) (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r), 0 < L →
      ∑' j : ℕ, ‖dfiVoronoiDualTerm r branch
          (dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x) (L + (j + 1))‖ ≤
        C * (r : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (Y / b) ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  have hScale : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
  exact (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    |>.exists_dfiVoronoiDualTerm_tail_scaled_decay
      (Y / b) hScale k hk branch

/-- DFI equations (28)--(29), with the source quantifiers in their required
order: a single constant profile is selected before `a,b,q,h,x`, and the
literal equation-(23) second-variable slice receives an explicit Mellin-line
bound. -/
theorem exists_dfiEquation28_ySlice_mellin_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x u : ℝ),
        let C₆ := ∑ j ∈ Finset.range 7, C j
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * Y / b)
        (1 + |u|) ^ 6 *
            ‖mellin
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)
              ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ 6 *
            (64 *
              ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
              (D * A + D * (512 * A * (1 + D * B) ^ 6))) := by
  choose C hC hBound using fun j =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ 0 j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x u
  dsimp only
  let C₆ : ℝ := ∑ j ∈ Finset.range 7, C j
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := C₆ * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hC₆ : 0 < C₆ := by
    dsimp [C₆]
    exact Finset.sum_pos
      (fun j hj => hC j) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDeriv : ∀ j ≤ 6, ∀ y : ℝ,
      ‖iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y‖ ≤ A * B ^ j := by
    intro j hj y
    have hjMem : j ∈ Finset.range 7 := by
      simp only [Finset.mem_range]
      omega
    have hCle : C j ≤ C₆ := by
      dsimp [C₆]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hjMem
    have hEq : iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y =
        dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C j * qQ⁻¹ * B ^ (0 + j) := by
        simpa only [qQ, B] using
          hBound j a b q ha hb hq hqQ h x y
      _ ≤ C₆ * qQ⁻¹ * B ^ j := by
        simp only [zero_add]
        gcongr
      _ = A * B ^ j := rfl
  have hMellin :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
      |>.mellin_half_line_bound_of_physical_profile hA hB hDeriv u
  simpa only [A, B, C₆] using hMellin

/-- First-variable counterpart of `exists_dfiEquation28_ySlice_mellin_bound`.
The same source-level quantifier discipline is preserved. -/
theorem exists_dfiEquation28_xSlice_mellin_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y u : ℝ),
        let C₆ := ∑ i ∈ Finset.range 7, C i
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * X / a)
        (1 + |u|) ^ 6 *
            ‖mellin
              (fun x => dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)
              ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ 6 *
            (64 *
              ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
              (D * A + D * (512 * A * (1 + D * B) ^ 6))) := by
  choose C hC hBound using fun i =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y u
  dsimp only
  let C₆ : ℝ := ∑ i ∈ Finset.range 7, C i
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := C₆ * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hC₆ : 0 < C₆ := by
    dsimp [C₆]
    exact Finset.sum_pos (fun i hi => hC i) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDeriv : ∀ i ≤ 6, ∀ x : ℝ,
      ‖iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x‖ ≤ A * B ^ i := by
    intro i hi x
    have hiMem : i ∈ Finset.range 7 := by
      simp only [Finset.mem_range]
      omega
    have hCle : C i ≤ C₆ := by
      dsimp [C₆]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hiMem
    have hEq : iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x =
        dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C i * qQ⁻¹ * B ^ (i + 0) := by
        simpa only [qQ, B] using
          hBound i a b q ha hb hq hqQ h x y
      _ ≤ C₆ * qQ⁻¹ * B ^ i := by
        simp only [add_zero]
        gcongr
      _ = A * B ^ i := rfl
  have hMellin :=
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
      |>.mellin_half_line_bound_of_physical_profile hA hB hDeriv u
  simpa only [A, B, C₆] using hMellin

end RiemannZeta.GuthMaynard
