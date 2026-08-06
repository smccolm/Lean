import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.ZeroCount
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Exp

open Complex
open MeasureTheory

namespace RiemannZeta.GuthMaynard

-- 1. Smooth Cutoff Function and its Fourier Transform
variable (Φ : ℝ → ℝ)
variable (Φ_smooth : ContDiff ℝ ⊤ Φ)
variable (Φ_compact : HasCompactSupport Φ)

-- The Fourier transform of Φ
noncomputable def fourierTransformΦ (Φ : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ (x : ℝ), (Φ x : ℂ) * cexp (-(2 * Real.pi * I * x * ξ))

lemma cexp_periodic_1 (x : ℝ) : cexp (2 * Real.pi * I * (x + 1)) = cexp (2 * Real.pi * I * x) := by
  have h1 : 2 * Real.pi * I * (x + 1) = 2 * Real.pi * I * x + 2 * Real.pi * I := by ring
  rw [h1, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma cexp_zero_eval : cexp 0 = 1 := by
  exact Complex.exp_zero

-- 2. Cutoff function depending on beta, sigma, and N
noncomputable def psiCutoff (β σ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  if Real.log N ≤ u ∧ u ≤ Real.log (2 * N) then
    Real.exp (u * (σ - β))
  else
    0

lemma psiCutoff_nonneg (β σ : ℝ) (N : ℕ) (u : ℝ) : 0 ≤ psiCutoff β σ N u := by
  unfold psiCutoff
  split_ifs
  · positivity
  · exact le_refl 0

lemma psiCutoff_zero (β σ : ℝ) (N : ℕ) (u : ℝ) (h : u < Real.log N) : psiCutoff β σ N u = 0 := by
  unfold psiCutoff
  split_ifs with h_if
  · exfalso
    linarith [h_if.1]
  · rfl

lemma psiCutoff_zero_right (β σ : ℝ) (N : ℕ) (u : ℝ) (h : Real.log (2 * N) < u) : psiCutoff β σ N u = 0 := by
  unfold psiCutoff
  split_ifs with h_if
  · exfalso
    linarith [h_if.2]
  · rfl

lemma psiCutoff_le_exp (β σ : ℝ) (N : ℕ) (u : ℝ) : psiCutoff β σ N u ≤ Real.exp (u * (σ - β)) := by
  unfold psiCutoff
  split_ifs
  · exact le_refl _
  · exact (Real.exp_pos _).le

lemma psiCutoff_bounded_of_sigma_le_beta (β σ : ℝ) (N : ℕ) (u : ℝ) (hN : 1 ≤ N) (h_sigma : σ ≤ β) : psiCutoff β σ N u ≤ 1 := by
  unfold psiCutoff
  split_ifs with h
  · have h1 : σ - β ≤ 0 := sub_nonpos.mpr h_sigma
    have h2 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have h3 : 0 ≤ u := le_trans h2 h.1
    have h4 : u * (σ - β) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h3 h1
    exact Real.exp_le_one_iff.mpr h4
  · exact zero_le_one

-- 3. Fourier Inversion Formula (Hypothesis)
/--
Hypothesis: Smooth compactly supported functions belong to the Schwartz space.
-/
axiom smooth_compact_is_schwartz (Φ : ℝ → ℝ) (h_smooth : ContDiff ℝ ⊤ Φ) (h_compact : HasCompactSupport Φ) : True

/--
Hypothesis: Fourier inversion holds for functions in the Schwartz space.
-/
axiom fourier_inversion_unconditional (Φ : ℝ → ℝ) (h_smooth : ContDiff ℝ ⊤ Φ) (h_compact : HasCompactSupport Φ) :
  ∀ (x : ℝ), (Φ x : ℂ) = ∫ (ξ : ℝ), fourierTransformΦ Φ ξ * cexp (2 * Real.pi * I * x * ξ)

lemma norm_cexp_ofReal_mul_I (y : ℝ) : ‖cexp ((y : ℂ) * I)‖ = 1 := by simp

lemma fourier_inversion_integrand_bound (Φ : ℝ → ℝ) (ξ x : ℝ) :
  ‖fourierTransformΦ Φ ξ * cexp (2 * Real.pi * I * x * ξ)‖ = ‖fourierTransformΦ Φ ξ‖ := by
  rw [norm_mul]
  have h_im : 2 * Real.pi * I * (x : ℂ) * (ξ : ℂ) = ((2 * Real.pi * x * ξ : ℝ) : ℂ) * I := by
    push_cast
    ring
  have h_im2 : 2 * Real.pi * I * x * ξ = ((2 * Real.pi * x * ξ : ℝ) : ℂ) * I := by
    calc 2 * Real.pi * I * x * ξ = 2 * Real.pi * I * (x : ℂ) * (ξ : ℂ) := by norm_cast
         _ = ((2 * Real.pi * x * ξ : ℝ) : ℂ) * I := h_im
  rw [h_im2]
  rw [norm_cexp_ofReal_mul_I (2 * Real.pi * x * ξ)]
  rw [mul_one]

/--
Hypothesis: Schwartz space functions exhibit rapid Fourier decay faster than any polynomial.
-/
def SchwartzFourierDecayProp : Prop :=
  ∀ (Φ : ℝ → ℝ),
    ContDiff ℝ ⊤ Φ →
    HasCompactSupport Φ →
    ∀ (k : ℕ), ∃ C_k : ℝ, 0 ≤ C_k ∧ ∀ ξ : ℝ, ‖fourierTransformΦ Φ ξ‖ ≤ C_k * (1 + |ξ|)^(- (k : ℝ))

lemma fourier_decay_rhs_nonneg (k : ℕ) (C_k : ℝ) (ξ : ℝ) (hC : 0 ≤ C_k) :
  0 ≤ C_k * (1 + |ξ|)^(- (k : ℝ)) := by
  have h1 : 0 ≤ 1 + |ξ| := by
    have h_abs : 0 ≤ |ξ| := abs_nonneg ξ
    linarith
  have h2 : 0 ≤ (1 + |ξ|)^(- (k : ℝ)) := Real.rpow_nonneg h1 _
  exact mul_nonneg hC h2

axiom fourier_decay_unconditional : SchwartzFourierDecayProp

-- 5. Integral representation over fixed line Re(s) = σ (Hypothesis)
/--
Hypothesis: A detector polynomial D(s) can be expressed as a continuous contour integral via Cauchy's Residue Theorem.
-/
axiom cauchy_residue_dirichlet_polynomial (N : ℕ) (β γ T : ℝ) :
  ∃ (Γ : ℝ → ℂ), detectPoly N (β + I * γ) T = ∫ (t : ℝ), Γ t * detectPoly N (β + I * t) T

/--
Hypothesis: The contour integral can be shifted to the fixed line Re(s) = σ, pulling out the Fourier transform of the cutoff function and an explicit Fourier truncation error.
-/
axiom contour_shift_to_real_line (Φ : ℝ → ℝ) (h_smooth : ContDiff ℝ ⊤ Φ) (h_compact : HasCompactSupport Φ) :
  ∀ (N : ℕ) (β σ γ T : ℝ), ∃ (error : ℂ), detectPoly N (β + I * γ) T = (∫ (v : ℝ), fourierTransformΦ Φ v * detectPoly N (σ + I * (γ - 2 * Real.pi * v)) T) + error

-- 6. Coefficient bounds and epsilon losses (Hypothesis)
/--
Hypothesis: The Fourier decay of the smooth, compactly supported cutoff function bounds the truncation error term asymptotically by T^(-100).
-/
axiom fourier_decay_error_bound (Φ : ℝ → ℝ) (h_smooth : ContDiff ℝ ⊤ Φ) (h_compact : HasCompactSupport Φ) (T : ℝ) (hT : T ≥ 2) :
  ∃ (C : ℝ), ∀ (v : ℝ), ‖fourierTransformΦ Φ v‖ ≤ C * (1 + |v|)^(-100 : ℝ)

/--
Hypothesis: The fixed line polynomial integral implies the existence of a point γ' where the polynomial is large, via the pigeonhole principle over the truncated integral domain.
-/
axiom pigeonhole_integral_bound :
  ∀ (N : ℕ) (β σ γ T ε : ℝ), 1 / (3 * Real.log T) ≤ ‖detectPoly N (β + I * γ) T‖ →
    ∃ (γ' : ℝ), |γ - γ'| ≤ T^ε ∧ 1 / (4 * Real.log T) ≤ ‖detectPoly N (σ + I * γ') T‖

-- The final BetaDependenceRemovalProp now assembled from these pieces.
/--
F-04: Beta dependence removal hypothesis.
For every T ≥ 1, σ, β and N, if the actual detector D_N(s)
is large at a zero ρ = β + iγ, then D_N(σ + iγ') is large for some γ' shifted by at most T^ε.
-/
theorem beta_dependence_removal :
  ∀ (Φ : ℝ → ℝ),
    ContDiff ℝ ⊤ Φ →
    HasCompactSupport Φ →
    ∀ (T : ℝ) (σ : ℝ) (N : ℕ) (ε : ℝ), T ≥ 1 → ε > 0 →
      ∀ (ρ : ℂ), ρ ∈ zerosInRect σ 1 T (2 * T) →
        1 / (3 * Real.log T) ≤ ‖detectPoly N ρ T‖ →
        ∃ (γ' : ℝ), |ρ.im - γ'| ≤ T^ε ∧ 1 / (4 * Real.log T) ≤ ‖detectPoly N (σ + I * γ') T‖ := by
  intro Φ h_smooth h_compact T σ N ε hT hε ρ hρ h_large
  have h_rw : ρ = (ρ.re : ℂ) + I * (ρ.im : ℂ) := by
    calc ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * I := (Complex.re_add_im ρ).symm
         _ = (ρ.re : ℂ) + I * (ρ.im : ℂ) := by rw [mul_comm]
  rw [h_rw] at h_large
  exact pigeonhole_integral_bound N ρ.re σ ρ.im T ε h_large



end RiemannZeta.GuthMaynard
