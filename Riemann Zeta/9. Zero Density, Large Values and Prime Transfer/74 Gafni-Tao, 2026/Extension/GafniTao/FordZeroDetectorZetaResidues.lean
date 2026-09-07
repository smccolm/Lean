import GafniTao.FordZeroDetectorCenter
import GafniTao.SharpPerronResidues

/-!
# Zeta residues in Ford's zero detector

The entire surrogate `(s-1)ζ(s)` permits a single holomorphic logarithmic
derivative calculation.  Subtracting `1/(s-1)` restores the meromorphic zeta
logarithmic derivative, so the pole at one has coefficient `-1` while every
nontrivial zero has its analytic multiplicity.  This file proves all three
local principal parts needed by the finite detector rectangle.
-/

open Complex Filter Set Topology Asymptotics
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

set_option maxHeartbeats 800000

/-- Surrogate presentation of the zeta logarithmic derivative, including
the negative principal coefficient at the pole `s=1`. -/
noncomputable def fordDetectorZetaLogDeriv (s : ℂ) : ℂ :=
  logDeriv sharpZetaSurrogate s - 1 / (s - 1)

/-- Away from the pole and zeros, the surrogate presentation is literally
`ζ'/ζ`. -/
theorem fordDetectorZetaLogDeriv_eq
    {s : ℂ} (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    fordDetectorZetaLogDeriv s = logDeriv riemannZeta s := by
  rw [fordDetectorZetaLogDeriv,
    logDeriv_sharpZetaSurrogate_eq hs1 hzeta]
  ring

/-- Ford's translated zeta detector integrand. -/
noncomputable def fordZetaDetectorIntegrand
    (eta : ℝ) (z₀ : ℂ) (s : ℂ) : ℂ :=
  fordCotKernel eta (s - z₀) * fordDetectorZetaLogDeriv s

/-- At a nontrivial zeta zero, the detector coefficient is the exact
analytic multiplicity times the translated cotangent weight. -/
theorem fordZetaDetectorIntegrand_near_zero
    {eta : ℝ} {z₀ rho : ℂ}
    (hrho : riemannZeta rho = 0)
    (hweight : DifferentiableAt ℂ
      (fun s : ℂ => fordCotKernel eta (s - z₀)) rho) :
    (fordZetaDetectorIntegrand eta z₀ - fun s =>
        ((analyticVanishingOrder riemannZeta rho : ℂ) *
          fordCotKernel eta (rho - z₀)) / (s - rho))
      =O[𝓝[≠] rho] (1 : ℂ → ℂ) := by
  have hrho1 : rho ≠ 1 := by
    intro h
    subst rho
    exact riemannZeta_one_ne_zero hrho
  let m : ℤ := analyticVanishingOrder riemannZeta rho
  have hord : meromorphicOrderAt sharpZetaSurrogate rho =
      (m : WithTop ℤ) := by
    simpa [m] using
      meromorphicOrderAt_sharpZetaSurrogate_eq_multiplicity hrho1
  have hsur := weightedLogDeriv_sub_principal_isBigO_one
    (sharpZetaSurrogate_analytic rho (by simp)).meromorphicAt hord hweight
  have hden : DifferentiableAt ℂ (fun s : ℂ => s - 1) rho :=
    differentiableAt_id.sub_const (1 : ℂ)
  have hcorrDiff : DifferentiableAt ℂ
      (fun s : ℂ =>
        -(fordCotKernel eta (s - z₀) / (s - 1))) rho := by
    exact (hweight.div hden (sub_ne_zero.mpr hrho1)).neg
  have hcorr : (fun s : ℂ =>
      -(fordCotKernel eta (s - z₀) / (s - 1)))
      =O[𝓝[≠] rho] (1 : ℂ → ℂ) :=
    (hcorrDiff.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).isBigO_one ℂ
  have hsum := hsur.add hcorr
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards with s
  simp only [fordZetaDetectorIntegrand, fordDetectorZetaLogDeriv,
    Pi.sub_apply]
  dsimp [m]
  push_cast
  ring

/-- At the zeta pole, the detector coefficient is minus the translated
cotangent weight. -/
theorem fordZetaDetectorIntegrand_near_one
    {eta : ℝ} {z₀ : ℂ}
    (hweight : DifferentiableAt ℂ
      (fun s : ℂ => fordCotKernel eta (s - z₀)) 1) :
    (fordZetaDetectorIntegrand eta z₀ - fun s =>
        (-fordCotKernel eta (1 - z₀)) / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hsurNonzero : sharpZetaSurrogate 1 ≠ 0 := by norm_num
  have hfirstDiff : DifferentiableAt ℂ
      (fun s : ℂ => fordCotKernel eta (s - z₀) *
        logDeriv sharpZetaSurrogate s) 1 :=
    hweight.mul (differentiableAt_logDeriv_sharpZetaSurrogate hsurNonzero)
  have hfirst : (fun s : ℂ => fordCotKernel eta (s - z₀) *
      logDeriv sharpZetaSurrogate s)
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) :=
    (hfirstDiff.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).isBigO_one ℂ
  have hprincipal :
      ((fun s : ℂ => 1 / (s - 1)) - fun s => 1 / (s - 1))
        =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
    simpa using (isBigO_zero (1 : ℂ → ℂ) (𝓝[≠] (1 : ℂ)))
  have hsecond := mul_sub_principal_isBigO_one
    (L := fun s : ℂ => 1 / (s - 1))
    (g := fun s : ℂ => -fordCotKernel eta (s - z₀))
    (p := (1 : ℂ)) (n := 1) hprincipal hweight.neg
  have hsum := hfirst.add hsecond
  refine hsum.congr' ?_ ?_
  · filter_upwards with s
    simp only [fordZetaDetectorIntegrand, fordDetectorZetaLogDeriv,
      Pi.sub_apply]
    ring
  · filter_upwards with s
    simp

/-- At the detector center, the coefficient is the regular value of the
actual zeta logarithmic derivative. -/
theorem fordZetaDetectorIntegrand_near_center
    {eta : ℝ} (heta : 0 < eta) {z₀ : ℂ}
    (hz₀1 : z₀ ≠ 1) (hz₀ : riemannZeta z₀ ≠ 0) :
    (fordZetaDetectorIntegrand eta z₀ - fun s =>
        fordDetectorZetaLogDeriv z₀ / (s - z₀))
      =O[𝓝[≠] z₀] (1 : ℂ → ℂ) := by
  have hsur : sharpZetaSurrogate z₀ ≠ 0 := by
    intro h
    exact hz₀ ((sharpZetaSurrogate_eq_zero_iff hz₀1).mp h)
  have hL : DifferentiableAt ℂ fordDetectorZetaLogDeriv z₀ := by
    unfold fordDetectorZetaLogDeriv
    exact (differentiableAt_logDeriv_sharpZetaSurrogate hsur).sub
      ((differentiableAt_const (c := (1 : ℂ))).div
        (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ))))
        (sub_ne_zero.mpr hz₀1))
  simpa only [fordZetaDetectorIntegrand] using
    fordCotKernel_translate_mul_sub_principal_isBigO_one heta hL

end

end GafniTao
