import TaoTrudgianYang2025.DirichletPrefixBounded
import TaoTrudgianYang2025.ZetaFourthPolynomialMean
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini and Gaussian averaging of the actual polynomial mean square

A finite coefficient-norm majorant proves product integrability first.
The sharper translated time mean square is then integrated in the
contour variable, with the exact Gaussian mass.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval

namespace TaoTrudgianYang2025

theorem integrable_gaussian_dirichletPrefix_prod
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Real.exp (-b*z.2^2)*‖dirichletPrefix N a (z.2-z.1)‖^2)
      ((volume.restrict (uIoc A B)).prod volume) := by
  let C : ℝ := ∑ n ∈ Finset.Ioc 0 N, ‖a n‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hc : Integrable (fun _ : ℝ => C^2) (volume.restrict (uIoc A B)) := by
    change Integrable (fun _ : ℝ => C^2)
      (volume.restrict (Ioc (min A B) (max A B)))
    exact integrable_const _
  have hg := integrable_exp_neg_mul_sq hb
  have hcont : Continuous (fun z : ℝ × ℝ =>
      Real.exp (-b*z.2^2)*‖dirichletPrefix N a (z.2-z.1)‖^2) :=
    (by fun_prop : Continuous (fun z : ℝ × ℝ => Real.exp (-b*z.2^2))).mul
      (((continuous_dirichletPrefix N a).comp (by fun_prop)).norm.pow 2)
  apply (hc.mul_prod hg).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ Real.exp (-b*z.2^2)*C^2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletPrefix_le N a (z.2-z.1)) 2)
        (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem intervalIntegrable_gaussianPrefixMean
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      ∫ u : ℝ, Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^2) volume A B := by
  rw [intervalIntegrable_iff]
  exact (integrable_gaussian_dirichletPrefix_prod hb N a A B).integral_prod_left

theorem integral_gaussianPrefixMean_swap
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (A B : ℝ) :
    (∫ t : ℝ in A..B, ∫ u : ℝ,
      Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^2) =
        ∫ u : ℝ, Real.exp (-b*u^2)*
          (∫ t : ℝ in A..B, ‖dirichletPrefix N a (u-t)‖^2) := by
  rw [intervalIntegral_integral_swap
    (integrable_gaussian_dirichletPrefix_prod hb N a A B)]
  simp_rw [intervalIntegral.integral_const_mul]

theorem exists_integral_gaussian_fourthPolynomial_le {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 ≤ c → ∀ M : ℕ, ∀ H : ℝ, 0 ≤ H →
      (∫ t : ℝ in H..2*H, ∫ u : ℝ,
        Real.exp (-98*u^2)*‖dirichletPrefix (2^M) (zetaFourthCoeff c) (u-t)‖^2) ≤
          D*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε := by
  obtain ⟨C,hC,hmean⟩ := exists_integral_sq_fourthPolynomial_le hε
  let G : ℝ := Real.sqrt (Real.pi/98)
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨C*G,mul_pos hC hG,?_⟩
  intro c hc M H hH
  rw [integral_gaussianPrefixMean_swap (by norm_num : (0:ℝ)<98)]
  let Q : ℝ := C*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^ε
  have hnonneg : ∀ u : ℝ, 0 ≤ Real.exp (-98*u^2)*
      (∫ t : ℝ in H..2*H, ‖dirichletPrefix (2^M) (zetaFourthCoeff c) (u-t)‖^2) := by
    intro u
    apply mul_nonneg (Real.exp_pos _).le
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  calc
    _ ≤ ∫ u : ℝ, Real.exp (-98*u^2)*Q :=
      integral_mono_of_nonneg (Eventually.of_forall hnonneg)
        ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<98)).mul_const Q)
        (Eventually.of_forall (fun u =>
          mul_le_mul_of_nonneg_left (hmean c hc M H hH u) (Real.exp_pos _).le))
    _ = _ := by
      rw [integral_mul_const,integral_gaussian]
      dsimp [Q,G]
      ring

end TaoTrudgianYang2025
