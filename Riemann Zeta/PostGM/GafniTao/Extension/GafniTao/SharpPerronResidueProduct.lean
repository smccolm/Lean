import GafniTao.SharpPerronZetaSurrogate
import RiemannZeta.External.PNT.RectangleArgumentPrinciple

/-!
# Multiplying a logarithmic-derivative principal part

The sharp Perron integrand multiplies `-F'/F` by an analytic weight.  This
file records the local calculation showing that the residue is the analytic
weight evaluated at the zero times the exact analytic multiplicity.
-/

open Complex Filter Set Topology Asymptotics

noncomputable section

namespace GafniTao

/-- Multiplication by a function differentiable at the pole evaluates that
factor at the pole in the principal coefficient. -/
theorem mul_sub_principal_isBigO_one
    {L g : ℂ → ℂ} {p n : ℂ}
    (hL : (L - fun s => n / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hg : DifferentiableAt ℂ g p) :
    ((fun s => g s * L s) - fun s => (n * g p) / (s - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hgO : g =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
  have hfirst :
      (fun s => g s * ((L - fun w => n / (w - p)) s))
        =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have hmul := hgO.mul hL
    refine hmul.congr' ?_ ?_
    · filter_upwards with s
      rfl
    · filter_upwards with s
      simp
  have hslope : Tendsto (slope g p) (𝓝[≠] p) (𝓝 (deriv g p)) :=
    hasDerivAt_iff_tendsto_slope.mp hg.hasDerivAt
  have hslopeO : slope g p =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    hslope.isBigO_one ℂ
  have hsecond :
      (fun s => n * ((g s - g p) / (s - p)))
        =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have hnO : (fun _ : ℂ => n) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
      isBigO_const_const n (c' := (1 : ℂ)) one_ne_zero (𝓝[≠] p)
    have hmul := hnO.mul hslopeO
    refine hmul.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [slope_def_field]
    · filter_upwards with s
      simp
  have hsum := hfirst.add hsecond
  refine hsum.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Pi.sub_apply]
    field_simp [sub_ne_zero.mpr hs]
    ring
  · filter_upwards with s
    simp

/-- Principal part of an analytically weighted logarithmic derivative at a
point of finite meromorphic order. -/
theorem weightedLogDeriv_sub_principal_isBigO_one
    {f g : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ))
    (hg : DifferentiableAt ℂ g p) :
    ((fun s => g s * logDeriv f s) -
        fun s => ((n : ℂ) * g p) / (s - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
  mul_sub_principal_isBigO_one
    (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord) hg

end GafniTao
