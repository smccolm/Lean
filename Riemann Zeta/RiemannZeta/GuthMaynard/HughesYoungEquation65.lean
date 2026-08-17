import RiemannZeta.GuthMaynard.HughesYoungPolynomialRatioJets
import RiemannZeta.GuthMaynard.HughesYoungCutoff

open Complex Filter MeasureTheory Set Topology
open Classical
open scoped ContDiff

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equation (65)

This file proves the physical-height derivative estimates needed for the
repeated integration by parts in Hughes--Young equation (65).  The proof uses
the exact factorization of the shifted contour weight, Cauchy estimates for
the pole-cancelling rational factor, and the paired-Gamma logarithmic jets.
-/

/-- The order-`n` Leibniz constant for the product of the rational factor and
the paired Gamma quotient. -/
noncomputable def hughesYoungRightContourDerivativeConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
      hughesYoungGammaRatioBellConstant (n - i)

theorem hughesYoungRightContourDerivativeConstant_pos (n : ℕ) :
    0 < hughesYoungRightContourDerivativeConstant n := by
  unfold hughesYoungRightContourDerivativeConstant
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (by positivity)))
      (hughesYoungGammaRatioBellConstant_nonneg _)
  · refine ⟨n, by simp, ?_⟩
    simp
    positivity

/-- Exact all-orders physical-height derivative formula for the complete
right-contour coefficient. -/
theorem iteratedDeriv_hughesYoungRightContourWeight_shift_eq
    (n : ℕ) {c : ℝ} (hc : 0 < c) (u t : ℝ) :
    iteratedDeriv n (fun x : ℝ =>
        hughesYoungRightContourWeight x c u) t =
      (Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) /
          ((c : ℂ) + (u : ℂ) * I)) *
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i (fun x : ℝ =>
              hughesYoungPolynomialRatioShift x c u) t *
            iteratedDeriv (n - i) (fun x : ℝ =>
              hughesYoungGammaRatioShift x c u) t) := by
  let A : ℂ :=
    Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) /
      ((c : ℂ) + (u : ℂ) * I)
  let P : ℝ → ℂ := fun x => hughesYoungPolynomialRatioShift x c u
  let G : ℝ → ℂ := fun x => hughesYoungGammaRatioShift x c u
  have hfun : (fun x : ℝ => hughesYoungRightContourWeight x c u) =
      fun x : ℝ => A * (P x * G x) := by
    funext x
    rw [hughesYoungRightContourWeight_shift_eq]
    dsimp [A, P, G]
    ring
  rw [hfun, iteratedDeriv_const_mul_field]
  change A * iteratedDeriv n (P * G) t = _
  rw [iteratedDeriv_mul
    ((contDiff_hughesYoungPolynomialRatioShift c u).contDiffAt.of_le
      (by exact_mod_cast le_top))
    ((contDiff_hughesYoungGammaRatioShift (by linarith) u).contDiffAt.of_le
      (by exact_mod_cast le_top))]

private theorem norm_hughesYoungRightContour_constant_le
    {c u : ℝ} (hc : 0 < c) :
    ‖Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) /
        ((c : ℂ) + (u : ℂ) * I)‖ ≤
      c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hw : c ≤ ‖w‖ := by
    have hre := Complex.abs_re_le_norm w
    simpa [w, abs_of_pos hc] using hre
  have hwpos : 0 < ‖w‖ := hc.trans_le hw
  have hgauss : ‖Complex.exp (100 * w ^ 2)‖ =
      Real.exp (100 * c ^ 2 - 100 * u ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [w, pow_two, Complex.mul_re]
    ring
  change ‖Complex.exp (100 * w ^ 2) / w‖ ≤ _
  rw [norm_div, hgauss]
  have hinv : 1 / ‖w‖ ≤ c⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hc hw
  calc
    Real.exp (100 * c ^ 2 - 100 * u ^ 2) / ‖w‖ =
        Real.exp (100 * c ^ 2 - 100 * u ^ 2) * (1 / ‖w‖) := by ring
    _ ≤ Real.exp (100 * c ^ 2 - 100 * u ^ 2) * c⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg _)
    _ = c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2) := by ring

/-- Uniform all-orders physical-height derivative bound for the complete
right-contour coefficient in the central Mellin range. -/
theorem exists_norm_iteratedDeriv_hughesYoungRightContourWeight_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (T t c u : ℝ),
      16 ≤ T → T / 4 ≤ t → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      ‖iteratedDeriv n (fun x : ℝ =>
          hughesYoungRightContourWeight x c u) t‖ ≤
        c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (|t| + |u| + 2)) *
          hughesYoungRightContourDerivativeConstant n *
          (((T / 16)⁻¹ * (1 + |u|)) ^ n) := by
  obtain ⟨C, hC, hgamma⟩ :=
    exists_norm_iteratedDeriv_hughesYoungGammaRatioShift_le
  refine ⟨C, hC, ?_⟩
  intro n T t c u hT ht hc hc1 hu
  let S : ℝ := (T / 16)⁻¹ * (1 + |u|)
  let E : ℝ := Real.exp
    (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA := norm_hughesYoungRightContour_constant_le (u := u) hc
  rw [iteratedDeriv_hughesYoungRightContourWeight_shift_eq n hc u t,
    norm_mul]
  calc
    ‖Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) /
          ((c : ℂ) + (u : ℂ) * I)‖ *
        ‖∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i (fun x : ℝ =>
              hughesYoungPolynomialRatioShift x c u) t *
            iteratedDeriv (n - i) (fun x : ℝ =>
              hughesYoungGammaRatioShift x c u) t‖ ≤
        (c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2)) *
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
              hughesYoungGammaRatioBellConstant (n - i)) *
                E * S ^ n) := by
      apply mul_le_mul hA
      · calc
          ‖∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℂ) *
                iteratedDeriv i (fun x : ℝ =>
                  hughesYoungPolynomialRatioShift x c u) t *
                iteratedDeriv (n - i) (fun x : ℝ =>
                  hughesYoungGammaRatioShift x c u) t‖ ≤
              ∑ i ∈ Finset.range (n + 1),
                ‖(n.choose i : ℂ) *
                  iteratedDeriv i (fun x : ℝ =>
                    hughesYoungPolynomialRatioShift x c u) t *
                  iteratedDeriv (n - i) (fun x : ℝ =>
                    hughesYoungGammaRatioShift x c u) t‖ :=
            norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (n + 1),
                (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
                  hughesYoungGammaRatioBellConstant (n - i)) *
                    E * S ^ n := by
            apply Finset.sum_le_sum
            intro i hi
            have hiN : i ≤ n :=
              Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            have hP :=
              norm_iteratedDeriv_hughesYoungPolynomialRatioShift_le_commonScale
                i hT ht hc.le hc1 hu
            have hG := hgamma (n - i) T t c u hT ht hc.le hc1 hu
            change ‖iteratedDeriv i (fun x : ℝ =>
                hughesYoungPolynomialRatioShift x c u) t‖ ≤
              (i.factorial * 6 ^ (8 : ℕ)) * S ^ i at hP
            change ‖iteratedDeriv (n - i) (fun x : ℝ =>
                hughesYoungGammaRatioShift x c u) t‖ ≤
              E * hughesYoungGammaRatioBellConstant (n - i) *
                S ^ (n - i) at hG
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            calc
              (n.choose i : ℝ) *
                    ‖iteratedDeriv i (fun x : ℝ =>
                      hughesYoungPolynomialRatioShift x c u) t‖ *
                    ‖iteratedDeriv (n - i) (fun x : ℝ =>
                      hughesYoungGammaRatioShift x c u) t‖ ≤
                  (n.choose i : ℝ) *
                    ((i.factorial * 6 ^ (8 : ℕ)) * S ^ i) *
                    (E * hughesYoungGammaRatioBellConstant (n - i) *
                      S ^ (n - i)) := by
                have hchoose : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
                have hleft := mul_le_mul_of_nonneg_left hP hchoose
                exact mul_le_mul hleft hG (norm_nonneg _)
                  (mul_nonneg hchoose
                    (mul_nonneg (by positivity) (pow_nonneg hS _)))
              _ = (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
                    hughesYoungGammaRatioBellConstant (n - i)) *
                      E * S ^ n := by
                have hpow : S ^ i * S ^ (n - i) = S ^ n := by
                  rw [← pow_add, Nat.add_sub_of_le hiN]
                calc
                  (n.choose i : ℝ) *
                        ((i.factorial * 6 ^ (8 : ℕ)) * S ^ i) *
                        (E * hughesYoungGammaRatioBellConstant (n - i) *
                          S ^ (n - i)) =
                      (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
                        hughesYoungGammaRatioBellConstant (n - i)) * E *
                          (S ^ i * S ^ (n - i)) := by ring
                  _ = _ := by rw [hpow]
      · positivity
      · positivity
    _ = c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (|t| + |u| + 2)) *
          hughesYoungRightContourDerivativeConstant n * S ^ n := by
      have hsum :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
              hughesYoungGammaRatioBellConstant (n - i)) * E * S ^ n) =
          (∑ i ∈ Finset.range (n + 1),
            n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
              hughesYoungGammaRatioBellConstant (n - i)) * E * S ^ n := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [hsum]
      dsimp only [hughesYoungRightContourDerivativeConstant, E]
      let D : ℝ := ∑ i ∈ Finset.range (n + 1),
        n.choose i * (i.factorial * 6 ^ (8 : ℕ)) *
          hughesYoungGammaRatioBellConstant (n - i)
      have hexp :
          Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
              Real.exp
                (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) =
            Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (|t| + |u| + 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      change c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
          (D * Real.exp
            (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) *
              S ^ n) =
        c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (|t| + |u| + 2)) * D * S ^ n
      calc
        c⁻¹ * Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
            (D * Real.exp
              (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) *
                S ^ n) =
            c⁻¹ *
              (Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
                Real.exp
                  (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2)) *
              D * S ^ n := by ring
        _ = _ := by rw [hexp]
    _ = _ := rfl

/-- The topological support of the physical height cutoff is the advertised
Hughes--Young interval. -/
theorem tsupport_hughesYoungHeightWeight_subset
    {T : ℝ} (hT : 0 < T) :
    tsupport (hughesYoungHeightWeight T) ⊆ Set.Icc (T / 4) (4 * T) := by
  apply closure_minimal
  · intro t ht
    exact hughesYoungHeightWeight_support hT ht
  · exact isClosed_Icc

/-- Differentiating the cleaned height input does not enlarge its physical
height support. -/
theorem support_iteratedDeriv_hughesYoungHeightFourierInput_subset
    {T : ℝ} (hT : 0 < T) (c u : ℝ) (n : ℕ) :
    Function.support
        (iteratedDeriv n (hughesYoungHeightFourierInput T c u)) ⊆
      Set.Icc (T / 4) (4 * T) := by
  have hiter : tsupport
      (iteratedDeriv n (hughesYoungHeightFourierInput T c u)) ⊆
      tsupport (hughesYoungHeightFourierInput T c u) :=
    tsupport_iteratedDeriv_complex_subset _ n
  have hmul : tsupport (hughesYoungHeightFourierInput T c u) ⊆
      tsupport (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ)) := by
    unfold hughesYoungHeightFourierInput
    exact tsupport_mul_subset_left
  have hcast : tsupport (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ)) ⊆
      tsupport (hughesYoungHeightWeight T) := by
    change tsupport (Complex.ofReal ∘ hughesYoungHeightWeight T) ⊆ _
    exact tsupport_comp_subset (by norm_num) _
  exact (subset_tsupport _).trans
    (hiter.trans (hmul.trans (hcast.trans
      (tsupport_hughesYoungHeightWeight_subset hT))))

/-- The all-orders Leibniz constant after adjoining the fixed height cutoff. -/
noncomputable def hughesYoungHeightInputDerivativeConstant
    (Cw : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * Cw i *
      hughesYoungRightContourDerivativeConstant (n - i)

theorem hughesYoungHeightInputDerivativeConstant_pos
    {Cw : ℕ → ℝ} (hCw : ∀ i, 0 < Cw i) (n : ℕ) :
    0 < hughesYoungHeightInputDerivativeConstant Cw n := by
  unfold hughesYoungHeightInputDerivativeConstant
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hCw i).le)
      (hughesYoungRightContourDerivativeConstant_pos _).le
  · refine ⟨n, by simp, ?_⟩
    simp
    exact mul_pos (hCw n)
      (hughesYoungRightContourDerivativeConstant_pos 0)

/-- Pointwise bound for every derivative of the exact cleaned height input.
All dependence on the derivative order is isolated in a fixed profile. -/
theorem exists_norm_iteratedDeriv_hughesYoungHeightFourierInput_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧ ∀ (n : ℕ) (T t c u : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      ‖iteratedDeriv n (hughesYoungHeightFourierInput T c u) t‖ ≤
        c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
          hughesYoungHeightInputDerivativeConstant Cw n *
          (((T / 16)⁻¹ * (1 + |u|)) ^ n) := by
  obtain ⟨Cγ, hCγ, hright⟩ :=
    exists_norm_iteratedDeriv_hughesYoungRightContourWeight_shift_le
  obtain ⟨Cw, hCw⟩ :=
    exists_uniform_hughesYoungHeightWeight_derivativeProfile
  refine ⟨Cγ, hCγ, Cw, fun i => (hCw i).1, ?_⟩
  intro n T t c u hT hc hc1 hu
  have hT0 : 0 < T := by linarith
  let S : ℝ := (T / 16)⁻¹ * (1 + |u|)
  let A : ℝ := c⁻¹ * Real.exp
    (100 * c ^ 2 - 84 * u ^ 2 +
      4 * Cγ * c * Real.log (4 * T + |u| + 2))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hscale : T⁻¹ ≤ S := by
    dsimp [S]
    rw [inv_div]
    have hTi : 0 ≤ T⁻¹ := by positivity
    have hfirst : T⁻¹ ≤ 16 / T := by
      rw [div_eq_mul_inv]
      nlinarith
    have hsecond : 16 / T ≤ 16 / T * (1 + |u|) := by
      have h16T : 0 ≤ 16 / T := by positivity
      nlinarith [abs_nonneg u]
    exact hfirst.trans hsecond
  by_cases htmem : t ∈ Set.Icc (T / 4) (4 * T)
  · have hcut (i : ℕ) :
        ‖iteratedDeriv i (fun x : ℝ =>
            (hughesYoungHeightWeight T x : ℂ)) t‖ ≤ Cw i * S ^ i := by
      have hcast := congrFun
        (iteratedDeriv_ofReal_comp (hughesYoungHeightWeight T)
          (contDiff_hughesYoungHeightWeight T) i) t
      rw [hcast, norm_real, Real.norm_eq_abs]
      have hw := (hCw i).2 T hT0 t
      rw [Real.norm_eq_abs] at hw
      exact hw.trans <| mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hscale i) (hCw i).1.le
    have hright' (j : ℕ) :
        ‖iteratedDeriv j (fun x : ℝ =>
            hughesYoungRightContourWeight x c u) t‖ ≤
          A * hughesYoungRightContourDerivativeConstant j * S ^ j := by
      have hraw := hright j T t c u hT htmem.1 hc hc1 hu
      change ‖iteratedDeriv j (fun x : ℝ =>
          hughesYoungRightContourWeight x c u) t‖ ≤
        c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (|t| + |u| + 2)) *
          hughesYoungRightContourDerivativeConstant j * S ^ j at hraw
      have ht0 : 0 ≤ t := by nlinarith [htmem.1]
      have habst : |t| ≤ 4 * T := by simpa [abs_of_nonneg ht0] using htmem.2
      have harg : |t| + |u| + 2 ≤ 4 * T + |u| + 2 := by linarith
      have harg0 : 0 < |t| + |u| + 2 := by positivity
      have hlog := Real.log_le_log harg0 harg
      have hcoef : 0 ≤ 4 * Cγ * c := by positivity
      have hexp : Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (|t| + |u| + 2)) ≤
          Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * Cγ * c * Real.log (4 * T + |u| + 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hlog hcoef]
      exact hraw.trans <| by
        dsimp [A]
        gcongr
        exact (hughesYoungRightContourDerivativeConstant_pos j).le
    have hcutSmooth : ContDiffAt ℝ n (fun x : ℝ =>
        (hughesYoungHeightWeight T x : ℂ)) t :=
      (Complex.ofRealCLM.contDiff.comp
        (contDiff_hughesYoungHeightWeight T)).contDiffAt.of_le
          (by exact_mod_cast le_top)
    have hrightSmooth : ContDiffAt ℝ n (fun x : ℝ =>
        hughesYoungRightContourWeight x c u) t :=
      (contDiff_hughesYoungRightContourWeight_height hc u).contDiffAt.of_le
        (by exact_mod_cast le_top)
    unfold hughesYoungHeightFourierInput
    change ‖iteratedDeriv n
      ((fun x : ℝ => (hughesYoungHeightWeight T x : ℂ)) *
        fun x : ℝ => hughesYoungRightContourWeight x c u) t‖ ≤ _
    rw [iteratedDeriv_mul hcutSmooth hrightSmooth]
    calc
      ‖∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i (fun x : ℝ =>
              (hughesYoungHeightWeight T x : ℂ)) t *
            iteratedDeriv (n - i) (fun x : ℝ =>
              hughesYoungRightContourWeight x c u) t‖ ≤
          ∑ i ∈ Finset.range (n + 1),
            ‖(n.choose i : ℂ) *
              iteratedDeriv i (fun x : ℝ =>
                (hughesYoungHeightWeight T x : ℂ)) t *
              iteratedDeriv (n - i) (fun x : ℝ =>
                hughesYoungRightContourWeight x c u) t‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i * Cw i *
            hughesYoungRightContourDerivativeConstant (n - i)) *
              A * S ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        calc
          (n.choose i : ℝ) *
                ‖iteratedDeriv i (fun x : ℝ =>
                  (hughesYoungHeightWeight T x : ℂ)) t‖ *
                ‖iteratedDeriv (n - i) (fun x : ℝ =>
                  hughesYoungRightContourWeight x c u) t‖ ≤
              (n.choose i : ℝ) * (Cw i * S ^ i) *
                (A * hughesYoungRightContourDerivativeConstant (n - i) *
                  S ^ (n - i)) := by
            have hchoose : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
            have hleft := mul_le_mul_of_nonneg_left (hcut i) hchoose
            exact mul_le_mul hleft (hright' (n - i)) (norm_nonneg _)
              (mul_nonneg hchoose
                (mul_nonneg (hCw i).1.le (pow_nonneg hS _)))
          _ = (n.choose i * Cw i *
                hughesYoungRightContourDerivativeConstant (n - i)) *
                  A * S ^ n := by
            have hpow : S ^ i * S ^ (n - i) = S ^ n := by
              rw [← pow_add, Nat.add_sub_of_le hiN]
            calc
              (n.choose i : ℝ) * (Cw i * S ^ i) *
                    (A * hughesYoungRightContourDerivativeConstant (n - i) *
                      S ^ (n - i)) =
                  (n.choose i * Cw i *
                    hughesYoungRightContourDerivativeConstant (n - i)) * A *
                      (S ^ i * S ^ (n - i)) := by ring
              _ = _ := by rw [hpow]
      _ = A * hughesYoungHeightInputDerivativeConstant Cw n * S ^ n := by
        unfold hughesYoungHeightInputDerivativeConstant
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring
      _ = _ := rfl
  · have hsupp :=
      support_iteratedDeriv_hughesYoungHeightFourierInput_subset hT0 c u n
    have hzero : iteratedDeriv n
        (hughesYoungHeightFourierInput T c u) t = 0 := by
      by_contra hne
      exact htmem (hsupp hne)
    rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hc.le) (Real.exp_nonneg _))
        (hughesYoungHeightInputDerivativeConstant_pos
          (fun i => (hCw i).1) n).le)
      (pow_nonneg hS _)

/-- The derivative mass appearing after `j` integrations by parts has the
correct support length and inverse-height scale. -/
theorem exists_integral_norm_iteratedDeriv_hughesYoungHeightFourierInput_le :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧ ∀ (j : ℕ) (T c u : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      (∫ t : ℝ,
        ‖iteratedDeriv j (hughesYoungHeightFourierInput T c u) t‖) ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hpoint⟩ :=
    exists_norm_iteratedDeriv_hughesYoungHeightFourierInput_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u hT hc hc1 hu
  have hT0 : 0 < T := by linarith
  let g : ℝ → ℂ :=
    iteratedDeriv j (hughesYoungHeightFourierInput T c u)
  let M : ℝ := c⁻¹ * Real.exp
    (100 * c ^ 2 - 84 * u ^ 2 +
      4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
    hughesYoungHeightInputDerivativeConstant Cw j *
    (((T / 16)⁻¹ * (1 + |u|)) ^ j)
  have hg : Integrable (fun t : ℝ => ‖g t‖) := by
    dsimp [g]
    exact (integrable_iteratedDeriv_hughesYoungHeightFourierInput
      hT0 hc u j).norm
  have hsupp : Function.support g ⊆ Set.Icc (T / 4) (4 * T) := by
    dsimp [g]
    exact support_iteratedDeriv_hughesYoungHeightFourierInput_subset
      hT0 c u j
  have hbound : ∀ t : ℝ, ‖g t‖ ≤ M := by
    intro t
    exact hpoint j T t c u hT hc hc1 hu
  have hraw := integral_norm_le_interval_length_mul g
    (show T / 4 ≤ 4 * T by linarith) hg hsupp hbound
  simpa only [g, M] using hraw.trans_eq (by ring)

/-- Hughes--Young equation (65), in the exact Fourier normalization used by
the project. -/
theorem hughesYoung_equation65 :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧ ∀ (j : ℕ) (T c u ξ : ℝ),
      16 ≤ T → 0 < c → c ≤ 1 → |u| ≤ T / 8 →
      |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
        (15 * T / 4) *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * Cγ * c * Real.log (4 * T + |u| + 2)) *
            hughesYoungHeightInputDerivativeConstant Cw j *
            (((T / 16)⁻¹ * (1 + |u|)) ^ j)) := by
  obtain ⟨Cγ, hCγ, Cw, hCw, hmass⟩ :=
    exists_integral_norm_iteratedDeriv_hughesYoungHeightFourierInput_le
  refine ⟨Cγ, hCγ, Cw, hCw, ?_⟩
  intro j T c u ξ hT hc hc1 hu
  have hT0 : 0 < T := by linarith
  exact (abs_pow_mul_norm_hughesYoungHeightTransform_le
    hT0 hc u ξ j).trans (hmass j T c u hT hc hc1 hu)

end RiemannZeta.GuthMaynard
