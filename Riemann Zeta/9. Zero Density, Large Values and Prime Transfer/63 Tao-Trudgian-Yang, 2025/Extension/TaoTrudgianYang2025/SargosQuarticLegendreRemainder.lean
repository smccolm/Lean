import TaoTrudgianYang2025.SargosQuarticInverse
import TaoTrudgianYang2025.SargosQuarticLegendreAlgebra

/-! The literal quartic specialization of the Legendre expansion, with its actual residual. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosQuarticLegendreRemainder (N α γ y : ℝ) : ℝ :=
  sargosQuarticLegendre N α γ y+y^2/(4*α)-γ*y^4/(16*α^4)+γ^2*y^6/(16*α^7)

def sargosQuarticLegendreRemainderDerivative (N α γ y : ℝ) : ℝ :=
  -sargosQuarticInverseSlope N α γ y+y/(2*α)-γ*y^3/(4*α^4)+3*γ^2*y^5/(8*α^7)

theorem sargosQuarticLegendre_expansion (N α γ y : ℝ) :
    sargosQuarticLegendre N α γ y =
      -y^2/(4*α)+γ*y^4/(16*α^4)-γ^2*y^6/(16*α^7)+
        sargosQuarticLegendreRemainder N α γ y := by
  unfold sargosQuarticLegendreRemainder
  ring

theorem sargosQuarticLegendreRemainder_hasDerivAt {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    HasDerivAt (sargosQuarticLegendreRemainder N α γ)
      (sargosQuarticLegendreRemainderDerivative N α γ y) y := by
  have hi := sargosQuarticLegendre_hasDerivAt hN hα hγ hy
  have h2 := ((hasDerivAt_id y).pow 2).div_const (4*α)
  have h4 := (((hasDerivAt_id y).pow 4).const_mul γ).div_const (16*α^4)
  have h6 := (((hasDerivAt_id y).pow 6).const_mul (γ^2)).div_const (16*α^7)
  convert ((hi.add h2).sub h4).add h6 using 1
  dsimp only [sargosQuarticLegendreRemainderDerivative,id_eq]
  ring

theorem sargosQuarticLegendreRemainder_eq {N α γ y : ℝ}
    (hα : α ≠ 0) (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticLegendreRemainder N α γ y =
      α*(sargosQuarticInverseSlope N α γ y)^2*
        (2*γ*(sargosQuarticInverseSlope N α γ y)^2/α)^3*
        sargosQuarticRemainderPolynomial (2*γ*(sargosQuarticInverseSlope N α γ y)^2/α) := by
  simpa only [sargosQuarticSlope_inverse hy] using
    sargosQuartic_legendre_algebra hα γ (sargosQuarticInverseSlope N α γ y)

theorem sargosQuarticLegendreRemainderDerivative_eq {N α γ y : ℝ}
    (hα : α ≠ 0) (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticLegendreRemainderDerivative N α γ y =
      sargosQuarticInverseSlope N α γ y*
        (2*γ*(sargosQuarticInverseSlope N α γ y)^2/α)^3*
        sargosQuarticRemainderDerivativePolynomial
          (2*γ*(sargosQuarticInverseSlope N α γ y)^2/α) := by
  simpa only [sargosQuarticSlope_inverse hy] using
    sargosQuartic_legendre_derivative_algebra hα γ (sargosQuarticInverseSlope N α γ y)

theorem sargosQuarticLegendreRemainder_contDiffAt {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    ContDiffAt ℝ ∞ (sargosQuarticLegendreRemainder N α γ) y := by
  unfold sargosQuarticLegendreRemainder
  exact (((sargosQuarticLegendre_contDiffAt hN hα hγ hy).add
    ((contDiffAt_id.pow 2).div_const (4*α))).sub
    ((contDiffAt_const.mul (contDiffAt_id.pow 4)).div_const (16*α^4))).add
    ((contDiffAt_const.mul (contDiffAt_id.pow 6)).div_const (16*α^7))

end TaoTrudgianYang2025
