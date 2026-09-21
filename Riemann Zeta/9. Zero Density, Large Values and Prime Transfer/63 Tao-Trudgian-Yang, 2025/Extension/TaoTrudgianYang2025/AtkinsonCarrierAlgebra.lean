import TaoTrudgianYang2025.AtkinsonPowerIntegral

/-!
# Exact exponential carriers of the two retained Neumann terms

The signs and quarter powers are linked to the actual Bessel argument.
No trigonometric term or complex source amplitude is discarded.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

def atkinsonBesselScale (α : ℝ) (n : ℕ) : ℝ :=
  (4 * Real.pi) ^ (-2 * α) * (n : ℝ) ^ (-α)

def neumannLeadingPlus : ℂ := -(1 + I) / 2
def neumannLeadingMinus : ℂ := -(1 - I) / 2
def neumannCorrectionPlus : ℂ := (1 - I) / 2
def neumannCorrectionMinus : ℂ := (1 + I) / 2

theorem neumannTwoTerm_complex_exp (z : ℝ) :
    (neumannTwoTerm z : ℂ) = (Real.sqrt Real.pi / Real.pi : ℂ) *
      ((neumannLeadingPlus * Complex.exp ((z : ℂ) * I) +
        neumannLeadingMinus * Complex.exp ((-z : ℂ) * I)) *
          ((z ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) -
       (neumannCorrectionPlus * Complex.exp ((z : ℂ) * I) +
        neumannCorrectionMinus * Complex.exp ((-z : ℂ) * I)) / 8 *
          ((z ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  apply Complex.ext <;>
    norm_num [neumannTwoTerm, neumannLeadingPlus, neumannLeadingMinus,
      neumannCorrectionPlus, neumannCorrectionMinus, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.exp_re, Complex.exp_im,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos] <;> ring_nf <;> simp only [true_or, or_true]

theorem atkinson_bessel_argument_rpow {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) (α : ℝ) :
    (4 * Real.pi * Real.sqrt (x * n)) ^ (-2 * α) =
      atkinsonBesselScale α n * x ^ (-α) := by
  have hn0 : (0 : ℝ) < n := by positivity
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ x * n)]
  rw [show (1 / 2 : ℝ) * (-2 * α) = -α by ring, Real.mul_rpow hx.le hn0.le]
  unfold atkinsonBesselScale
  ring

theorem atkinsonPowerIntegrand_bessel {T G L x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 0 < n) (α s : ℝ) :
    zetaAtkinsonDivisorTest T G L x *
      (((4 * Real.pi * Real.sqrt (x * n)) ^ (-2 * α) : ℝ) : ℂ) *
        Complex.exp (((s * (4 * Real.pi * Real.sqrt (x * n)) : ℝ) : ℂ) * I) =
      (atkinsonBesselScale α n : ℂ) *
        atkinsonPowerIntegrand T G L α (s * Real.sqrt n) x := by
  rw [atkinson_bessel_argument_rpow hx hn α]
  have hp : s * (4 * Real.pi * Real.sqrt (x * n)) =
      4 * Real.pi * (s * Real.sqrt n) * Real.sqrt x := by
    rw [Real.sqrt_mul hx.le]
    ring
  rw [hp]
  unfold atkinsonPowerIntegrand
  push_cast
  ring

theorem zetaAtkinsonTwoTermIntegrand_eq_carriers {T G L x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 0 < n) :
    zetaAtkinsonTwoTermIntegrand T G L n x =
      (Real.sqrt Real.pi / Real.pi : ℂ) *
        ((atkinsonBesselScale (1 / 4) n : ℂ) *
          (neumannLeadingPlus * atkinsonPowerIntegrand T G L (1 / 4) (Real.sqrt n) x +
           neumannLeadingMinus * atkinsonPowerIntegrand T G L (1 / 4) (-Real.sqrt n) x) -
         (atkinsonBesselScale (3 / 4) n : ℂ) / 8 *
          (neumannCorrectionPlus * atkinsonPowerIntegrand T G L (3 / 4) (Real.sqrt n) x +
           neumannCorrectionMinus * atkinsonPowerIntegrand T G L (3 / 4) (-Real.sqrt n) x)) := by
  have hp := atkinsonPowerIntegrand_bessel (T := T) (G := G) (L := L) hx hn (1 / 4) 1
  have hm := atkinsonPowerIntegrand_bessel (T := T) (G := G) (L := L) hx hn (1 / 4) (-1)
  have hcp := atkinsonPowerIntegrand_bessel (T := T) (G := G) (L := L) hx hn (3 / 4) 1
  have hcm := atkinsonPowerIntegrand_bessel (T := T) (G := G) (L := L) hx hn (3 / 4) (-1)
  norm_num only [one_mul, neg_one_mul, Complex.ofReal_neg,
    show (-2 : ℝ) * (1 / 4) = -(1 / 2) by norm_num,
    show (-2 : ℝ) * (3 / 4) = -(3 / 2) by norm_num] at hp hm hcp hcm
  rw [zetaAtkinsonTwoTermIntegrand, neumannTwoTerm_complex_exp]
  linear_combination (Real.sqrt Real.pi / Real.pi : ℂ) *
    (neumannLeadingPlus * hp + neumannLeadingMinus * hm -
      neumannCorrectionPlus / 8 * hcp - neumannCorrectionMinus / 8 * hcm)

end TaoTrudgianYang2025
