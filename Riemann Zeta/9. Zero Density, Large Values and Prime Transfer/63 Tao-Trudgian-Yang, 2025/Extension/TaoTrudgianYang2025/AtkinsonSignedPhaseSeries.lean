import TaoTrudgianYang2025.AtkinsonMainNormalization
import TaoTrudgianYang2025.AtkinsonStationarySeries

/-!
# Exact signed exponential sums for the evaluated divisor source

Both source phases, ordinary divisor coefficients and residual profiles
are retained. The common factor is computed from the original Bessel
normalization, not selected by a bound.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def atkinsonFourthRootCoefficient (T : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^(-(1/4:ℝ))*atkinsonCommonSaddleFactor T (Real.sqrt n)

def atkinsonPositiveMainWeight (T G L : ℝ) (n : ℕ) : ℂ :=
  (atkinsonFourthRootCoefficient T n : ℂ) * atkinsonSaddleGaussian T G n *
    atkinsonSaddleResidual T G L (Real.sqrt n)

def atkinsonNegativeMainWeight (T G L : ℝ) (n : ℕ) : ℂ :=
  (atkinsonFourthRootCoefficient T n : ℂ) * atkinsonSaddleGaussian T G n *
    atkinsonSaddleResidual T G L (-Real.sqrt n)

def atkinsonPositivePhaseTerm (T : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-1:ℂ)^n * Complex.exp ((atkinsonSourcePhase T n : ℂ)*I)

def atkinsonNegativePhaseTerm (T : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-1:ℂ)^n * Complex.exp ((-atkinsonSourcePhase T n : ℂ)*I)

def atkinsonPositiveMainSum (T G L : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, atkinsonPositiveMainWeight T G L n * atkinsonPositivePhaseTerm T n

def atkinsonNegativeMainSum (T G L : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, atkinsonNegativeMainWeight T G L n * atkinsonNegativePhaseTerm T n

def atkinsonCommonMainPhase (T : ℝ) : ℂ :=
  (1+I)*zetaSquareReflectedGammaPhase T*Complex.exp ((atkinsonCentralPhase T : ℂ)*I)

theorem atkinsonFourthRootCoefficient_eq {T : ℝ} (hT : 0 < T) (n : ℕ) :
    atkinsonFourthRootCoefficient T n =
      (1/Real.sqrt 2)*(n:ℝ)^(-(1/4:ℝ))*
        ((n:ℝ)+2*T/Real.pi)^(-(1/4:ℝ)) := by
  rw [atkinsonFourthRootCoefficient,atkinsonCommonSaddleFactor_eq_rpow hT,
    Real.sq_sqrt (Nat.cast_nonneg n),show 4*(T/(2*Real.pi)) = 2*T/Real.pi by ring]
  ring

theorem atkinsonBesselScale_quarter_normalization (n : ℕ) :
    2*Real.sqrt Real.pi*atkinsonBesselScale (1/4) n = (n:ℝ)^(-(1/4:ℝ)) := by
  have hp : Real.sqrt (4*Real.pi) = 2*Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  unfold atkinsonBesselScale
  norm_num only [show (-2:ℝ)*(1/4) = -(1/2) by norm_num]
  rw [Real.rpow_neg (by positivity),← Real.sqrt_eq_rpow,hp]
  field_simp

theorem atkinsonStationaryLeadingTerm_eq_signed {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (n : ℕ) :
    atkinsonStationaryLeadingTerm T G L n = atkinsonCommonMainPhase T *
      (atkinsonPositiveMainWeight T G L n*atkinsonPositivePhaseTerm T n -
        atkinsonNegativeMainWeight T G L n*atkinsonNegativePhaseTerm T n) := by
  have he : (2:ℂ)*(Real.sqrt Real.pi : ℂ)*(atkinsonBesselScale (1/4) n : ℂ) =
      (((n:ℝ)^(-(1/4:ℝ)) : ℝ) : ℂ) := by
    exact_mod_cast atkinsonBesselScale_quarter_normalization n
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold atkinsonStationaryLeadingTerm atkinsonStationaryLeadingIntegral
  rw [atkinsonStationaryMain_sqrt_normalized hT,atkinsonStationaryMain_neg_sqrt_normalized hT hG]
  unfold atkinsonCommonMainPhase atkinsonPositiveMainWeight atkinsonNegativeMainWeight
    atkinsonPositivePhaseTerm atkinsonNegativePhaseTerm atkinsonFourthRootCoefficient
    neumannLeadingPlus neumannLeadingMinus
  push_cast
  rw [← he]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem atkinsonStationaryLeadingFiniteSum_eq_signed {T G : ℝ} (hT : 0 < T)
    (hG : G ≠ 0) (L : ℝ) (N : ℕ) :
    atkinsonStationaryLeadingFiniteSum T G L N =
      atkinsonCommonMainPhase T *
        (atkinsonPositiveMainSum T G L N-atkinsonNegativeMainSum T G L N) := by
  unfold atkinsonStationaryLeadingFiniteSum atkinsonPositiveMainSum atkinsonNegativeMainSum
  simp_rw [atkinsonStationaryLeadingTerm_eq_signed hT hG L]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]

theorem atkinsonStationaryLeadingSum_eq_signed {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) :
    atkinsonStationaryLeadingSum T G L =
      atkinsonCommonMainPhase T *
        (atkinsonPositiveMainSum T G L (atkinsonSourceCutoff T G L)-
          atkinsonNegativeMainSum T G L (atkinsonSourceCutoff T G L)) := by
  rw [atkinsonStationaryLeadingSum_eq_finite hT hG hL hwidth,
    atkinsonStationaryLeadingFiniteSum_eq_signed hT hG.ne']

theorem norm_atkinsonCommonMainPhase_le (T : ℝ) :
    ‖atkinsonCommonMainPhase T‖ ≤ 2 := by
  unfold atkinsonCommonMainPhase
  rw [norm_mul,norm_mul,norm_zetaSquareReflectedGammaPhase,Complex.norm_exp_ofReal_mul_I,
    mul_one,mul_one]
  apply (norm_add_le _ _).trans
  norm_num

theorem norm_atkinsonStationaryLeadingSum_le_signed {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) :
    ‖atkinsonStationaryLeadingSum T G L‖ ≤ 2*
      (‖atkinsonPositiveMainSum T G L (atkinsonSourceCutoff T G L)‖+
        ‖atkinsonNegativeMainSum T G L (atkinsonSourceCutoff T G L)‖) := by
  rw [atkinsonStationaryLeadingSum_eq_signed hT hG hL hwidth,norm_mul]
  exact mul_le_mul (norm_atkinsonCommonMainPhase_le T) (norm_sub_le _ _)
    (norm_nonneg _) (by norm_num)

end TaoTrudgianYang2025

