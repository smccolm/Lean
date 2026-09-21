import TaoTrudgianYang2025.ZetaFourthKernelBasic

/-!
# Individual divisor terms on the fourth-moment contour

These are the actual ordinary-divisor terms from the zeta-square identity.
Their complex shift is holomorphic throughout Re(w)>0, and their vertical
norm retains the exact divisor coefficient and real power of the index.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaFourthTerm (t : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  divisorDirichletTerm (afeCriticalPoint (-t)+w) n * zetaFourthKernel t w

theorem zetaFourthTerm_zero (t : ℝ) (w : ℂ) : zetaFourthTerm t 0 w = 0 := by
  simp [zetaFourthTerm,divisorDirichletTerm]

theorem differentiableAt_zetaFourthKernel (t : ℝ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (zetaFourthKernel t) w := by
  have hs : DifferentiableAt ℂ (fun z : ℂ => afeCriticalPoint (-t)+z) w := by fun_prop
  have hpos : 0 < (afeCriticalPoint (-t)+w).re := by
    simp [afeCriticalPoint]
    linarith
  have hgamma := (differentiableAt_GammaR_of_re_pos hpos).comp w hs
  have haux := differentiable_hughesYoungAuxiliaryZero.differentiableAt (x := w)
  have hw0 : w ≠ 0 := by
    intro he
    subst w
    norm_num at hw
  unfold zetaFourthKernel zetaSquarePoleShift
  fun_prop (disch := assumption)

theorem differentiableAt_zetaFourthTerm (t : ℝ) (n : ℕ)
    {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (zetaFourthTerm t n) w := by
  by_cases hn : n = 0
  · subst n
    simpa only [show zetaFourthTerm t 0 = fun _ => (0:ℂ) by
      funext z; exact zetaFourthTerm_zero t z] using
        (differentiableAt_const (0:ℂ) : DifferentiableAt ℂ (fun _ : ℂ => (0:ℂ)) w)
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  have hd : DifferentiableAt ℂ
      (fun z : ℂ => divisorDirichletTerm (afeCriticalPoint (-t)+z) n) w := by
    simp only [divisorDirichletTerm_eq_divisorWeight_mul_cpow]
    fun_prop (disch := first | assumption | exact Or.inl hnC)
  exact hd.mul (differentiableAt_zetaFourthKernel t hw)

theorem norm_fourth_divisorTerm_vertical (t c u : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖ =
      (n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c)) := by
  by_cases hn : n = 0
  · subst n
    simp [divisorDirichletTerm]
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [divisorDirichletTerm_eq_divisorWeight_mul_cpow, norm_mul]
  simp only [divisorWeight,Complex.norm_natCast]
  rw [show (n:ℂ) = ((n:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  congr 2
  norm_num [afeCriticalPoint]

theorem norm_zetaFourthTerm_vertical (t c u : ℝ) (n : ℕ) :
    ‖zetaFourthTerm t n ((c:ℂ)+(u:ℂ)*I)‖ =
      ((n.divisors.card:ℝ)*(n:ℝ)^(-(1/2+c))) *
        ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ := by
  rw [zetaFourthTerm,norm_mul,norm_fourth_divisorTerm_vertical]

theorem norm_fourth_divisorTerm_le_card {c : ℝ} (hc : 0 ≤ c) (t u : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) n‖ ≤
      (n.divisors.card:ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [divisorDirichletTerm]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rw [norm_fourth_divisorTerm_vertical]
  exact mul_le_of_le_one_right (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))

theorem zetaFourthTerm_one (t u : ℝ) (n : ℕ) :
    zetaFourthTerm t n (1+(u:ℂ)*I) =
      zetaSquareDivisorTerm (-t) n u / zetaSquareGammaNormalization t := by
  rw [zetaFourthTerm,zetaFourthKernel_one,zetaSquareDivisorTerm]
  ring

theorem zetaFourthTerm_boundaryRect_zero
    (t : ℝ) (n : ℕ) {a b H : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(-H:ℂ)*I)) -
      (∫ x : ℝ in a..b, zetaFourthTerm t n ((x:ℂ)+(H:ℂ)*I)) +
      I • (∫ y : ℝ in -H..H, zetaFourthTerm t n ((b:ℂ)+(y:ℂ)*I)) -
      I • (∫ y : ℝ in -H..H, zetaFourthTerm t n ((a:ℂ)+(y:ℂ)*I)) = 0 := by
  have hd : DifferentiableOn ℂ (zetaFourthTerm t n) ([[a,b]] ×ℂ [[-H,H]]) := by
    intro w hw
    apply (differentiableAt_zetaFourthTerm t n ?_).differentiableWithinAt
    rw [mem_reProdIm,uIcc_of_le hab] at hw
    exact ha.trans_le hw.1.1
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (zetaFourthTerm t n) ((a:ℂ)-(H:ℂ)*I) ((b:ℂ)+(H:ℂ)*I)
    (by simpa using hd)
  simpa using hrect

end TaoTrudgianYang2025
