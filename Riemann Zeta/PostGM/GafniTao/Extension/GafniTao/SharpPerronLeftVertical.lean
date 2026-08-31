import GafniTao.SharpPerronHorizontalEdges

/-!
# The left vertical edge of the sharp Perron rectangle

On `Re s = -1` the completed-zeta functional equation reflects to the
absolutely convergent line `Re(1-s)=2`.  The proof below includes ordinate
zero; pole avoidance is established from real parts and does not appeal to a
large-height hypothesis.
-/

open Complex Set MeasureTheory

noncomputable section

namespace GafniTao

theorem Gammaℝ_ne_zero_on_neg_one_line (t : ℝ) :
    Gammaℝ ((-1 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hzero
  have hre := congrArg Complex.re hn
  norm_num at hre
  have hnreal : (2 * n : ℝ) = 1 := by
    exact_mod_cast hre.symm
  have hnnat : 2 * n = 1 := by exact_mod_cast hnreal
  omega

theorem sharpPerron_left_vertical_zeta_ne_zero (t : ℝ) :
    riemannZeta ((-1 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  let s : ℂ := (-1 : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have href : riemannZeta (1 - s) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [s]
  exact riemannZeta_ne_zero_of_reflected hs0 h1s0
    (Gammaℝ_ne_zero_on_neg_one_line t) href

theorem sharpPerron_left_vertical_digamma_poles_avoided (t : ℝ) :
    ∀ m : ℕ,
      (((-1 : ℂ) + (t : ℂ) * I) / 2) ≠ -m := by
  intro m h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hmreal : (2 * m : ℝ) = 1 := by
    linarith
  have hmnat : 2 * m = 1 := by exact_mod_cast hmreal
  omega

/-- Uniform logarithmic bound for `ζ'/ζ` on the complete left vertical
line, including the real point `s=-1`. -/
theorem exists_norm_riemannZeta_logDeriv_left_vertical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖deriv riemannZeta ((-1 : ℂ) + (t : ℂ) * I) /
        riemannZeta ((-1 : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.log (|t| + 2) := by
  obtain ⟨C₁, hC₁, hdig₁⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 1) (b := 1)
      (by norm_num)
  obtain ⟨C₂, hC₂, hdig₂⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 2) (b := 2)
      (by norm_num)
  let K : ℝ := ‖deriv riemannZeta (2 : ℂ) / riemannZeta (2 : ℂ)‖
  let C : ℝ :=
    (|Real.log Real.pi| + K + C₁ + C₂ + 2) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by unfold K; positivity
  have hC : 0 < C := by
    unfold C
    positivity
  refine ⟨C, hC, ?_⟩
  intro t
  let s : ℂ := (-1 : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hzeta : riemannZeta s ≠ 0 :=
    sharpPerron_left_vertical_zeta_ne_zero t
  have href : riemannZeta (1 - s) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [s]
  have hFE := sharpPerron_zeta_logDeriv_functional_eq
    hs1 hs0 hzeta href
  have hrefBound := dlog_riemannZeta_bdd_on_vertical_lines_generalized
    2 2 (-t) (by norm_num) le_rfl
  have hrefEq :
      ((2 : ℂ) + ((-t : ℝ) : ℂ) * I) = 1 - s := by
    apply Complex.ext
    · norm_num [s]
    · simp [s]
  have hrefBound' :
      ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ K := by
    have hrefBoundAbs :
        ‖deriv riemannZeta
            (((2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
          riemannZeta (((2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤ K := by
      simpa [K, neg_div, norm_neg] using hrefBound
    rw [← hrefEq]
    simpa using hrefBoundAbs
  have hshiftRe : (s + 2).re = 1 := by norm_num [s]
  have hrefRe : (1 - s).re = 2 := by norm_num [s]
  have hdigShift := hdig₁ (s + 2) (by rw [hshiftRe]) (by rw [hshiftRe])
  have hdigRef := hdig₂ (1 - s) (by rw [hrefRe]) (by rw [hrefRe])
  have himShift : |(s + 2).im| = |t| := by simp [s]
  have himRef : |(1 - s).im| = |t| := by simp [s, abs_neg]
  rw [himShift] at hdigShift
  rw [himRef] at hdigRef
  have hpoles := sharpPerron_left_vertical_digamma_poles_avoided t
  have hshift := sharpPerron_digamma_shift hpoles
  have hinv : ‖(s / 2)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hrele := Complex.abs_re_le_norm (s / 2)
    have hreEq : (s / 2).re = -1 / 2 := by simp [s]
    rw [hreEq] at hrele
    norm_num at hrele
    have hnormLower : (1 / 2 : ℝ) ≤ ‖s / 2‖ := by
      rw [norm_div]
      norm_num
      exact hrele
    calc
      ‖s / 2‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
        (inv_le_inv₀
          (norm_pos_iff.mpr (div_ne_zero hs0 (by norm_num)))
          (by norm_num)).2 hnormLower
      _ = 2 := by norm_num
  have hdigS : ‖digamma (s / 2)‖ ≤
      C₁ * Real.log (|t| + 2) + 2 := by
    rw [hshift]
    exact (norm_sub_le _ _).trans (add_le_add hdigShift hinv)
  have hlogLower : Real.log 2 ≤ Real.log (|t| + 2) := by
    apply Real.log_le_log (by norm_num)
    linarith [abs_nonneg t]
  have hlogPos : 0 < Real.log (|t| + 2) := hlog2.trans_le hlogLower
  have hnegNorm : ‖-deriv riemannZeta s / riemannZeta s‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ := by
    rw [neg_div, norm_neg]
  rw [← hnegNorm, hFE]
  have hhalfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  calc
    ‖(((-Real.log Real.pi : ℝ) : ℂ) +
        deriv riemannZeta (1 - s) / riemannZeta (1 - s)) +
          (1 / 2 : ℂ) *
            (digamma (s / 2) + digamma ((1 - s) / 2))‖ ≤
      |Real.log Real.pi| + K +
        (1 / 2 : ℝ) *
          ((C₁ * Real.log (|t| + 2) + 2) +
            C₂ * Real.log (|t| + 2)) := by
      calc
        _ ≤ ‖((-Real.log Real.pi : ℝ) : ℂ)‖ +
              ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ +
              ‖(1 / 2 : ℂ) *
                (digamma (s / 2) + digamma ((1 - s) / 2))‖ := by
            calc
              _ ≤ ‖(((-Real.log Real.pi : ℝ) : ℂ) +
                    deriv riemannZeta (1 - s) / riemannZeta (1 - s))‖ +
                  ‖(1 / 2 : ℂ) *
                    (digamma (s / 2) + digamma ((1 - s) / 2))‖ :=
                norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
        _ ≤ _ := by
          rw [norm_real, Real.norm_eq_abs, abs_neg, norm_mul, hhalfNorm]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hdigS hdigRef)
    _ ≤ C * Real.log (|t| + 2) := by
      let L : ℝ := Real.log (|t| + 2)
      let A : ℝ := |Real.log Real.pi| + K + 1
      have hA : 0 ≤ A := by
        dsimp [A]
        positivity
      have hL : 0 ≤ L := by exact hlogPos.le
      have hlog2le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at this ⊢
        exact this
      have hLscale : L ≤ L / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        nlinarith
      have hAscale : A ≤ A * (L / Real.log 2) := by
        have hone : 1 ≤ L / Real.log 2 := by
          rw [le_div_iff₀ hlog2]
          simpa [L] using hlogLower
        nlinarith
      have hCscale : (C₁ + C₂) * L ≤
          (C₁ + C₂) * (L / Real.log 2) := by
        exact mul_le_mul_of_nonneg_left hLscale (by positivity)
      have hQ : 0 ≤ L / Real.log 2 := div_nonneg hL hlog2.le
      calc
        |Real.log Real.pi| + K +
              (1 / 2 : ℝ) *
                ((C₁ * Real.log (|t| + 2) + 2) +
                  C₂ * Real.log (|t| + 2)) =
            A + ((C₁ + C₂) / 2) * L := by
              dsimp [A, L]
              ring
        _ ≤ A + (C₁ + C₂) * L := by
              gcongr
              nlinarith [hC₁.le, hC₂.le, hL]
        _ ≤ A * (L / Real.log 2) +
              (C₁ + C₂) * (L / Real.log 2) :=
            add_le_add hAscale hCscale
        _ ≤ (A + C₁ + C₂ + 1) * (L / Real.log 2) := by
              nlinarith
        _ = C * Real.log (|t| + 2) := by
              dsimp [A, L, C]
              field_simp [ne_of_gt hlog2]
              all_goals ring

end GafniTao
