import GafniTao.FordZeroDetectorKernel
import GafniTao.SharpPerronResidueProduct

/-!
# Local residues in Ford's zero detector

The detector has two different local contributions.  At a zero or pole of
the function, the cotangent weight evaluates the logarithmic-derivative
residue.  At the centre of the rectangle, the cotangent kernel itself has
residue one and evaluates the regular logarithmic derivative.  This file
proves both calculations without a global contour hypothesis.
-/

open Complex Filter Set Topology Asymptotics

namespace GafniTao

noncomputable section

/-- A bounded error added to a simple principal part does not change the
residue. -/
theorem residue_eq_of_sub_principal_isBigO_one
    {F : ℂ → ℂ} {p c : ℂ}
    (hF : (F - fun z => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    residue F p = c := by
  apply residue_eq_of_tendsto
  have hp : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr
      (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)
  have hpSmall : (fun z : ℂ => z - p) =o[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (isLittleO_one_iff ℂ).2 hp
  have hrem :
      Tendsto (fun z : ℂ => (z - p) *
        ((F - fun w : ℂ => c / (w - p)) z)) (𝓝[≠] p) (𝓝 0) := by
    simpa using hpSmall.mul_isBigO hF
  have hprincipal :
      (fun z : ℂ => (z - p) * (c / (z - p))) =ᶠ[𝓝[≠] p]
        fun _ : ℂ => c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    field_simp [sub_ne_zero.mpr hz]
  have hprincipalLim :
      Tendsto (fun z : ℂ => (z - p) * (c / (z - p)))
        (𝓝[≠] p) (𝓝 c) := tendsto_const_nhds.congr' hprincipal.symm
  have hadd := hprincipalLim.add hrem
  simpa only [add_zero] using hadd.congr' (by
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring)

/-- The residue of an analytically weighted logarithmic derivative is the
meromorphic order times the value of the weight. -/
theorem residue_weightedLogDeriv_eq
    {f g : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ))
    (hg : DifferentiableAt ℂ g p) :
    residue (fun s => g s * logDeriv f s) p = (n : ℂ) * g p := by
  exact residue_eq_of_sub_principal_isBigO_one
    (weightedLogDeriv_sub_principal_isBigO_one hf hord hg)

/-- At the central cotangent pole, a continuous factor is evaluated at the
centre. -/
theorem residue_fordCotKernel_mul_eq
    {eta : ℝ} (heta : 0 < eta) {L : ℂ → ℂ}
    (hL : ContinuousAt L 0) :
    residue (fun z => fordCotKernel eta z * L z) 0 = L 0 := by
  apply residue_eq_of_tendsto
  have hk := tendsto_mul_fordCotKernel_zero heta
  have hprod := hk.mul (hL.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [sub_zero, one_mul, mul_assoc] using hprod

/-- The central contribution in Ford's detector is the ordinary logarithmic
derivative at the centre whenever that logarithmic derivative is regular. -/
theorem residue_fordCotKernel_mul_logDeriv_eq
    {eta : ℝ} (heta : 0 < eta) {f : ℂ → ℂ}
    (hlog : ContinuousAt (logDeriv f) 0) :
    residue (fun z => fordCotKernel eta z * logDeriv f z) 0 =
      logDeriv f 0 :=
  residue_fordCotKernel_mul_eq heta hlog

end

end GafniTao
