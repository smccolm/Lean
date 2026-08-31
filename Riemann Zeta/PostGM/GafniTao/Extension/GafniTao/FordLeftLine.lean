import GafniTao.FordLogDerivative
import GafniTao.SharpPerronLeftVertical

/-!
# The left line in Ford's `K(s)` contour shift

Ford shifts the logarithmic-derivative integral to `Re w = -1/2`.  This
file proves the qualitative logarithmic bound on that complete line directly
from the completed-zeta functional equation, the Euler-product bound on the
reflected line `Re (1-w) = 3/2`, and the pinned digamma-series estimate.

The source's sharper numerical inequality with constants `4.62`, `1/2`, and
`9` is deliberately not claimed here.  It is a later explicit-constant
refinement of this analytic convergence theorem.
-/

open Complex

namespace GafniTao

noncomputable section

/-- The shifted line `Re s = -1/2` contains no zeta zero. -/
theorem ford_leftLine_zeta_ne_zero (t : ℝ) :
    riemannZeta ((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
  let s : ℂ := (-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
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
    norm_num [s]
  have hgamma : Gammaℝ s ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hzero
    have hre := congrArg Complex.re hn
    norm_num [s] at hre
    have hnreal : (4 : ℝ) * (n : ℝ) = 1 := by linarith
    have hnnat : 4 * n = 1 := by exact_mod_cast hnreal
    omega
  exact riemannZeta_ne_zero_of_reflected hs0 h1s0 hgamma href

private theorem ford_leftLine_digamma_poles_avoided (t : ℝ) :
    ∀ m : ℕ,
      ((((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2)) ≠ -m := by
  intro m h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hmreal : (4 * m : ℝ) = 1 := by linarith
  have hmnat : 4 * m = 1 := by exact_mod_cast hmreal
  omega

/-- Qualitative form of Ford's left-line logarithmic-derivative estimate.
It is strong enough to justify absolute convergence after multiplication by
an `O(|z|⁻²)` Laplace-transform remainder. -/
theorem exists_norm_riemannZeta_logDeriv_ford_leftLine_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖deriv riemannZeta ((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta ((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.log (|t| + 2) := by
  obtain ⟨Cψ, hCψ, hdig⟩ :=
    Complex.exists_norm_digamma_div_two_le_log
      (a := 3 / 2) (b := 3 / 2) (by norm_num)
  let C : ℝ :=
    (|Real.log Real.pi| + 4 + Cψ) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t
  let s : ℂ := (-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hzeta : riemannZeta s ≠ 0 := ford_leftLine_zeta_ne_zero t
  have href : riemannZeta (1 - s) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    norm_num [s]
  have hFE := sharpPerron_zeta_logDeriv_functional_eq
    hs1 hs0 hzeta href
  have hrefBound :
      ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ < 2 := by
    have h := ford_zeta_basic_logDerivative
      (sigma := 3 / 2) (t := -t) (by norm_num)
    have hrefEq :
        (((3 / 2 : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ)) = 1 - s := by
      apply Complex.ext <;> norm_num [s]
    rw [hrefEq] at h
    norm_num at h
    simpa [neg_div, norm_neg, mul_comm] using h
  have hshiftRe : (s + 2).re = 3 / 2 := by norm_num [s]
  have hrefRe : (1 - s).re = 3 / 2 := by norm_num [s]
  have hdigShift := hdig (s + 2)
    (by rw [hshiftRe]) (by rw [hshiftRe])
  have hdigRef := hdig (1 - s)
    (by rw [hrefRe]) (by rw [hrefRe])
  have himShift : |(s + 2).im| = |t| := by simp [s]
  have himRef : |(1 - s).im| = |t| := by simp [s, abs_neg]
  rw [himShift] at hdigShift
  rw [himRef] at hdigRef
  have hpoles := ford_leftLine_digamma_poles_avoided t
  have hshift := sharpPerron_digamma_shift hpoles
  have hinv : ‖(s / 2)⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    have hrele := Complex.abs_re_le_norm (s / 2)
    have hreEq : (s / 2).re = -1 / 4 := by norm_num [s]
    rw [hreEq] at hrele
    norm_num at hrele
    have hnormLower : (1 / 4 : ℝ) ≤ ‖s / 2‖ := by
      rw [norm_div]
      norm_num
      exact hrele
    calc
      ‖s / 2‖⁻¹ ≤ (1 / 4 : ℝ)⁻¹ :=
        (inv_le_inv₀
          (norm_pos_iff.mpr (div_ne_zero hs0 (by norm_num)))
          (by norm_num)).2 hnormLower
      _ = 4 := by norm_num
  have hdigS : ‖digamma (s / 2)‖ ≤
      Cψ * Real.log (|t| + 2) + 4 := by
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
      |Real.log Real.pi| + 2 +
        (1 / 2 : ℝ) *
          ((Cψ * Real.log (|t| + 2) + 4) +
            Cψ * Real.log (|t| + 2)) := by
      calc
        _ ≤ ‖((-Real.log Real.pi : ℝ) : ℂ)‖ +
              ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ +
              ‖(1 / 2 : ℂ) *
                (digamma (s / 2) + digamma ((1 - s) / 2))‖ := by
            calc
              _ ≤ ‖((-Real.log Real.pi : ℝ) : ℂ) +
                    deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ +
                  ‖(1 / 2 : ℂ) *
                    (digamma (s / 2) + digamma ((1 - s) / 2))‖ :=
                norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
        _ ≤ _ := by
          rw [norm_real, Real.norm_eq_abs, abs_neg, norm_mul, hhalfNorm]
          have hsum :
              ‖digamma (s / 2) + digamma ((1 - s) / 2)‖ ≤
                (Cψ * Real.log (|t| + 2) + 4) +
                  Cψ * Real.log (|t| + 2) :=
            (norm_add_le _ _).trans (add_le_add hdigS hdigRef)
          nlinarith [hrefBound.le]
    _ ≤ C * Real.log (|t| + 2) := by
      let L : ℝ := Real.log (|t| + 2)
      let A : ℝ := |Real.log Real.pi| + 4
      have hL : 0 ≤ L := hlogPos.le
      have hlog2le : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h ⊢
        exact h
      have hLscale : L ≤ L / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        nlinarith
      have hAscale : A ≤ A * (L / Real.log 2) := by
        have hone : 1 ≤ L / Real.log 2 := by
          rw [le_div_iff₀ hlog2]
          simpa [L] using hlogLower
        nlinarith [show 0 ≤ A by dsimp [A]; positivity]
      have hψscale : Cψ * L ≤ Cψ * (L / Real.log 2) :=
        mul_le_mul_of_nonneg_left hLscale hCψ.le
      calc
        |Real.log Real.pi| + 2 +
              (1 / 2 : ℝ) *
                ((Cψ * Real.log (|t| + 2) + 4) +
                  Cψ * Real.log (|t| + 2)) = A + Cψ * L := by
                    dsimp [A, L]
                    ring
        _ ≤ A * (L / Real.log 2) + Cψ * (L / Real.log 2) :=
          add_le_add hAscale hψscale
        _ = (A + Cψ) * (L / Real.log 2) := by ring
        _ = C * Real.log (|t| + 2) := by
          dsimp [A, L, C]
          field_simp [ne_of_gt hlog2]

/-- The point `-1/2+iu` on Ford's shifted contour. -/
noncomputable def fordLeftLinePoint (u : ℝ) : ℂ :=
  (-(1 / 2 : ℝ) : ℂ) + (u : ℂ) * I

@[simp] theorem fordLeftLinePoint_re (u : ℝ) :
    (fordLeftLinePoint u).re = -1 / 2 := by
  norm_num [fordLeftLinePoint]

@[simp] theorem fordLeftLinePoint_im (u : ℝ) :
    (fordLeftLinePoint u).im = u := by
  simp [fordLeftLinePoint]

/-- Exact denominator on the shifted line.  Keeping this equality literal is
important: Ford's numerical integral uses `9/4+(u-t)²`, obtained from the
lower bound `sigma > 1` only after this identity. -/
theorem norm_sq_sub_fordLeftLinePoint
    (sigma t u : ℝ) :
    ‖((sigma : ℂ) + (t : ℂ) * I) - fordLeftLinePoint u‖ ^ 2 =
      (sigma + 1 / 2) ^ 2 + (t - u) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [fordLeftLinePoint]
  ring

/-- Pointwise domination of Ford's left-edge integrand by its genuine
logarithmic-over-quadratic envelope.  This is the source-order bridge from
the qualitative left-line theorem to absolute convergence of the `K(s)`
contour; no unspecified bounded weight is introduced. -/
theorem norm_fordLeftLine_logDeriv_mul_le
    {F₀ : ℂ → ℂ} {sigma t D eta C : ℝ}
    (hsigma : 1 < sigma) (hetaUpper : eta ≤ 3 / 2)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (hlogDeriv : ∀ u : ℝ,
      ‖deriv riemannZeta (fordLeftLinePoint u) /
        riemannZeta (fordLeftLinePoint u)‖ ≤
          C * Real.log (|u| + 2))
    (hC : 0 ≤ C) (u : ℝ) :
    ‖(-deriv riemannZeta (fordLeftLinePoint u) /
          riemannZeta (fordLeftLinePoint u)) *
        F₀ (((sigma : ℂ) + (t : ℂ) * I) - fordLeftLinePoint u)‖ ≤
      C * D * Real.log (|u| + 2) /
        ((sigma + 1 / 2) ^ 2 + (t - u) ^ 2) := by
  let z : ℂ := ((sigma : ℂ) + (t : ℂ) * I) - fordLeftLinePoint u
  have hzre : z.re = sigma + 1 / 2 := by
    simp [z, fordLeftLinePoint]
  have hzreNonneg : 0 ≤ z.re := by rw [hzre]; linarith
  have hzNormLower : sigma + 1 / 2 ≤ ‖z‖ := by
    rw [← hzre]
    exact (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have hetaNorm : eta ≤ ‖z‖ := by
    exact hetaUpper.trans (by linarith [hzNormLower])
  have hF := hF₀ z hzreNonneg hetaNorm
  have hlog := hlogDeriv u
  have hlogNonneg : 0 ≤ Real.log (|u| + 2) := by
    exact Real.log_nonneg (by linarith [abs_nonneg u])
  have hdenPos : 0 < (sigma + 1 / 2) ^ 2 + (t - u) ^ 2 := by
    positivity
  have hzsq : ‖z‖ ^ 2 =
      (sigma + 1 / 2) ^ 2 + (t - u) ^ 2 := by
    simpa [z] using norm_sq_sub_fordLeftLinePoint sigma t u
  rw [norm_mul, neg_div, norm_neg]
  calc
    ‖deriv riemannZeta (fordLeftLinePoint u) /
        riemannZeta (fordLeftLinePoint u)‖ * ‖F₀ z‖ ≤
      (C * Real.log (|u| + 2)) * (D / ‖z‖ ^ 2) := by
        exact mul_le_mul hlog hF (norm_nonneg _) (mul_nonneg hC hlogNonneg)
    _ = C * D * Real.log (|u| + 2) /
        ((sigma + 1 / 2) ^ 2 + (t - u) ^ 2) := by
      rw [hzsq]
      field_simp [ne_of_gt hdenPos]

end

end GafniTao
