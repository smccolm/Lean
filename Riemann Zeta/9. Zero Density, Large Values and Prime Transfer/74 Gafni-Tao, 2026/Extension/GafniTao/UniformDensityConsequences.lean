import GafniTao.NearOneExponent
import GafniTao.NativeTheorems

/-!
# Uniform ordinary-density consequences

This module proves the exponent calculation behind Gafni--Tao Theorem 1.1.
The upper-half supremum is not bounded by taking a limit at `sigma = 1`:
the proved Pintz logarithmic estimate supplies a positive gap from that edge.
-/

namespace GafniTao

noncomputable section

/-- The literal uniform ordinary zero-density hypothesis in Theorem 1.1. -/
def UniformOrdinaryDensityExponent (Azero : ℝ) : Prop :=
  ∀ sigma : ℝ, 1 / 2 ≤ sigma → sigma < 1 →
    zeroDensityExponent sigma ≤ (Azero : EReal)

/-- Replace `A(sigma)` by a uniform coefficient in the ordinary moment
candidate. -/
theorem ordinaryMomentExponent_le_of_uniform
    {theta sigma Azero : ℝ}
    (htheta : theta < 1) (hsigmaHalf : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma < 1)
    (hUniform : UniformOrdinaryDensityExponent Azero) :
    ordinaryMomentExponent theta sigma ≤
      (((1 - theta) * (1 - sigma) * Azero + 2 * sigma - 1 : ℝ) : EReal) := by
  unfold ordinaryMomentExponent
  have hcoef : 0 ≤ (1 - theta) * (1 - sigma) := by
    positivity
  calc
    (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
          zeroDensityExponent sigma + ((2 * sigma - 1 : ℝ) : EReal) ≤
        (((1 - theta) * (1 - sigma) : ℝ) : EReal) *
          (Azero : EReal) + ((2 * sigma - 1 : ℝ) : EReal) := by
      gcongr
      exact hUniform sigma hsigmaHalf hsigmaUpper
    _ = (((1 - theta) * (1 - sigma) * Azero +
          2 * sigma - 1 : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

/-- A Pintz right-edge gap and a uniform ordinary density exponent give an
explicit strict subunit bound for the fixed-epsilon upper-half supremum. -/
theorem upperHalfOrdinaryFixedEpsilonExponent_le_uniform
    {C B Tzero theta eps Azero : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hC : 0 < C) (htheta : theta < 1)
    (hthreshold : 0 < 1 / (1 - theta) - eps)
    (hUniform : UniformOrdinaryDensityExponent Azero)
    (hslope : (1 - theta) * Azero < 2) :
    upperHalfOrdinaryFixedEpsilonExponent theta eps ≤
      ((1 - (((1 / (1 - theta) - eps) / C) ^ 2) *
        (2 - (1 - theta) * Azero) : ℝ) : EReal) := by
  unfold upperHalfOrdinaryFixedEpsilonExponent
  apply sSup_le
  rintro x ⟨sigma, hsigma, rfl⟩
  have hGap := one_sub_sigma_lower_of_upperHalf_admissible
    hDensity hC hthreshold hsigma
  have hsigmaBound : sigma ≤
      1 - ((1 / (1 - theta) - eps) / C) ^ 2 := by
    linarith
  have hCandidate := ordinaryMomentExponent_le_of_uniform
    htheta hsigma.1.le hsigma.2.1 hUniform
  apply hCandidate.trans
  exact_mod_cast (show
    (1 - theta) * (1 - sigma) * Azero + 2 * sigma - 1 ≤
      1 - ((1 / (1 - theta) - eps) / C) ^ 2 *
        (2 - (1 - theta) * Azero) by
    have hslopeNonneg : 0 ≤ 2 - (1 - theta) * Azero := by linarith
    nlinarith)

/-- Exponent form of the almost-all assertion in Theorem 1.1.  The proof
retains the source `inf_{epsilon>0}` and inserts one explicit positive
epsilon only after the exact Gafni--Tao theorem has been established. -/
theorem exceptionalExponent_lt_one_of_uniform_density
    {C B Tzero theta Azero : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hC : 0 < C) (hAzero : 0 < Azero)
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (hUniform : UniformOrdinaryDensityExponent Azero)
    (hthetaThreshold : 1 - 2 / Azero < theta) :
    exceptionalExponent theta < (1 : EReal) := by
  let eps : ℝ := 1 / (2 * (1 - theta))
  have hthetaGap : 0 < 1 - theta := by linarith
  have heps : 0 < eps := by
    dsimp only [eps]
    positivity
  have hthreshold : 0 < 1 / (1 - theta) - eps := by
    dsimp only [eps]
    field_simp
    linarith
  have hslope : (1 - theta) * Azero < 2 := by
    have hdiv : 1 - theta < 2 / Azero := by linarith
    rwa [lt_div_iff₀ hAzero] at hdiv
  have hFixed := upperHalfOrdinaryFixedEpsilonExponent_le_uniform
    hDensity hC hthetaUpper hthreshold hUniform hslope
  have hInf : upperHalfOrdinaryExceptionalUpperExponent theta ≤
      upperHalfOrdinaryFixedEpsilonExponent theta eps := by
    apply sInf_le
    exact ⟨eps, heps, rfl⟩
  have hRight : upperHalfOrdinaryExceptionalUpperExponent theta <
      (1 : EReal) := hInf.trans_lt (hFixed.trans_lt (by
    exact_mod_cast (show
      1 - ((1 / (1 - theta) - eps) / C) ^ 2 *
          (2 - (1 - theta) * Azero) < (1 : ℝ) by
      have hratio : 0 < (1 / (1 - theta) - eps) / C :=
        div_pos hthreshold hC
      nlinarith [sq_pos_of_pos hratio])))
  have hBase : ((1 - theta : ℝ) : EReal) < (1 : EReal) := by
    exact_mod_cast (show 1 - theta < (1 : ℝ) by linarith)
  exact (gafniTaoTheorem12_max_native hthetaLower hthetaUpper).trans_lt
    (max_lt hBase hRight)

end

end GafniTao
