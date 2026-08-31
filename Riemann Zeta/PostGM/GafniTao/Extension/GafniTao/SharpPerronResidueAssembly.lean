import GafniTao.SharpPerronZeroLocation

/-!
# Assembly of the sharp Perron residue coefficients

This file combines the separately audited origin, pole, and nontrivial-zero
principal parts into the coefficient function consumed by the finite-pole
rectangle theorem.
-/

open Complex Filter Set Topology Asymptotics
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

/-- Exact coefficient of `(s-p)⁻¹` in the surrogate Perron integrand. -/
noncomputable def sharpZetaPerronResidueCoefficient (y : ℝ) (p : ℂ) : ℂ :=
  if p = 0 then -logDeriv sharpZetaSurrogate 0 - 1
  else if p = 1 then (y : ℂ)
  else -(zeroMultiplicity p : ℂ) * sharpPerronMonomial y p

theorem differentiableAt_sharpSurrogateLogPerron
    {y : ℝ} (hy : 0 < y) {s : ℂ} (hs0 : s ≠ 0)
    (hsSur : sharpZetaSurrogate s ≠ 0) :
    DifferentiableAt ℂ (sharpSurrogateLogPerron y) s := by
  unfold sharpSurrogateLogPerron
  exact (differentiableAt_sharpPerronMonomial hy hs0).neg.mul
    (differentiableAt_logDeriv_sharpZetaSurrogate hsSur)

theorem differentiableAt_sharpPerronPoleCorrection
    {y : ℝ} (hy : 0 < y) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (sharpPerronPoleCorrection y) s := by
  unfold sharpPerronPoleCorrection
  exact (differentiableAt_sharpPerronMonomial hy hs0).div
    (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))
    (sub_ne_zero.mpr hs1)

/-- Complete local principal part at the origin. -/
theorem sharpZetaPerronIntegrand_near_origin
    {y : ℝ} (hy : 0 < y) :
    (sharpZetaPerronIntegrand y - fun s =>
        sharpZetaPerronResidueCoefficient y 0 / (s - 0))
      =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
  have hsum := (sharpSurrogateLogPerron_near_origin hy).add
    (sharpPerronPoleCorrection_near_origin hy)
  refine hsum.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [sharpZetaPerronIntegrand, Pi.sub_apply,
      sharpZetaPerronResidueCoefficient, if_pos, sub_zero]
    field_simp [hs]
    ring
  · filter_upwards with s
    simp

/-- Complete local principal part at the zeta pole. -/
theorem sharpZetaPerronIntegrand_near_one
    {y : ℝ} (hy : 0 < y) :
    (sharpZetaPerronIntegrand y - fun s =>
        sharpZetaPerronResidueCoefficient y 1 / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hsurDiff : DifferentiableAt ℂ (sharpSurrogateLogPerron y) 1 :=
    differentiableAt_sharpSurrogateLogPerron hy (by norm_num) (by simp)
  have hsurO : sharpSurrogateLogPerron y =O[𝓝[≠] (1 : ℂ)]
      (1 : ℂ → ℂ) :=
    (hsurDiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hsum := hsurO.add (sharpPerronPoleCorrection_near_one hy)
  refine hsum.congr' ?_ ?_
  · filter_upwards with s
    simp only [sharpZetaPerronIntegrand, Pi.sub_apply,
      sharpZetaPerronResidueCoefficient, if_neg one_ne_zero, if_pos]
    ring
  · filter_upwards with s
    simp

/-- Complete local principal part at a nontrivial zero. -/
theorem sharpZetaPerronIntegrand_near_nontrivial_zero
    {y : ℝ} (hy : 0 < y) {rho : ℂ}
    (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1)
    (hrho : riemannZeta rho = 0) :
    (sharpZetaPerronIntegrand y - fun s =>
        sharpZetaPerronResidueCoefficient y rho / (s - rho))
      =O[𝓝[≠] rho] (1 : ℂ → ℂ) := by
  have hcorrDiff := differentiableAt_sharpPerronPoleCorrection hy hrho0 hrho1
  have hcorrO : sharpPerronPoleCorrection y =O[𝓝[≠] rho]
      (1 : ℂ → ℂ) :=
    (hcorrDiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hsum := (sharpSurrogateLogPerron_near_zero hy hrho).add hcorrO
  refine hsum.congr' ?_ ?_
  · filter_upwards with s
    simp only [sharpZetaPerronIntegrand, Pi.sub_apply,
      sharpZetaPerronResidueCoefficient, if_neg hrho0, if_neg hrho1,
      zeroMultiplicity]
    ring
  · filter_upwards with s
    simp

end GafniTao
