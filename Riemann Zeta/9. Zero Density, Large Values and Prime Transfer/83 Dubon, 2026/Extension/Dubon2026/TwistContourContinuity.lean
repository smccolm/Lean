import Dubon2026.CompactParameterIntegral
import Dubon2026.RectangleZeroCount

/-! # Phase continuity of an actual zero-free contour integral -/

namespace Dubon2026

open Filter Set Complex MeasureTheory
open scoped Topology

theorem continuousAt_twisted_path_logDeriv_integral (a : ℕ → ℂ) (N : ℕ)
    (z : PrimeTorus N) (γ : ℝ → ℂ) (hγ : Continuous γ) (b t : ℝ)
    (hn : ∀ y ∈ uIcc b t, dirichletSum (twistedCoefficients a N z) N (γ y) ≠ 0) :
    ContinuousAt (fun w : PrimeTorus N => ∫ y in b..t,
      logDeriv (dirichletSum (twistedCoefficients a N w) N) (γ y)) z := by
  apply continuousAt_intervalIntegral_of_compact_joint
    (f := fun w y => logDeriv (dirichletSum (twistedCoefficients a N w) N) (γ y)) z b t
  · intro y hy
    have hg : ContinuousAt (fun wy : PrimeTorus N × ℝ => (wy.1, γ wy.2)) (z, y) :=
      continuousAt_fst.prodMk (hγ.continuousAt.comp continuousAt_snd)
    exact ContinuousAt.comp (f := fun wy : PrimeTorus N × ℝ => (wy.1, γ wy.2))
      (x := (z, y)) (continuousAt_twisted_logDeriv a N z (γ y) (hn y hy)) hg
  · have he := eventually_ne_zero_twist_compact a N z
      (isCompact_uIcc.image hγ) (by rintro s ⟨y, hy, rfl⟩; exact hn y hy)
    filter_upwards [he] with w hw
    have hf : Continuous (dirichletSum (twistedCoefficients a N w) N) :=
      continuous_iff_continuousAt.mpr (fun s =>
        (analyticAt_dirichletSum (twistedCoefficients a N w) N s).continuousAt)
    have hd : Continuous (deriv (dirichletSum (twistedCoefficients a N w) N)) :=
      continuous_iff_continuousAt.mpr (fun s =>
        (analyticAt_dirichletSum (twistedCoefficients a N w) N s).deriv.continuousAt)
    exact ((hd.comp hγ).continuousOn.div (hf.comp hγ).continuousOn
      (fun y hy => hw (γ y) (mem_image_of_mem γ hy))).intervalIntegrable

theorem isCompact_rectangleBorder (s t : ℂ) : IsCompact (RectangleBorder s t) := by
  unfold RectangleBorder
  exact (((isCompact_uIcc.reProdIm isCompact_singleton).union
    (isCompact_singleton.reProdIm isCompact_uIcc)).union
      (isCompact_uIcc.reProdIm isCompact_singleton)).union
        (isCompact_singleton.reProdIm isCompact_uIcc)

theorem continuousAt_twisted_rectangle_logDeriv (a : ℕ → ℂ) (N : ℕ)
    (z : PrimeTorus N) (s t : ℂ)
    (hn : ∀ w ∈ RectangleBorder s t, dirichletSum (twistedCoefficients a N z) N w ≠ 0) :
    ContinuousAt (fun w : PrimeTorus N =>
      RectangleIntegral' (logDeriv (dirichletSum (twistedCoefficients a N w) N)) s t) z := by
  have h₁ := continuousAt_twisted_path_logDeriv_integral a N z
    (fun x : ℝ => (x : ℂ) + s.im * I) (by fun_prop) s.re t.re
    (fun y hy => hn _ (mapsTo_rectangleBorder_left_im s t hy))
  have h₂ := continuousAt_twisted_path_logDeriv_integral a N z
    (fun x : ℝ => (x : ℂ) + t.im * I) (by fun_prop) s.re t.re
    (fun y hy => hn _ (mapsTo_rectangleBorder_right_im s t hy))
  have h₃ := continuousAt_twisted_path_logDeriv_integral a N z
    (fun y : ℝ => (t.re : ℂ) + y * I) (by fun_prop) s.im t.im
    (fun y hy => hn _ (mapsTo_rectangleBorder_right_re s t hy))
  have h₄ := continuousAt_twisted_path_logDeriv_integral a N z
    (fun y : ℝ => (s.re : ℂ) + y * I) (by fun_prop) s.im t.im
    (fun y hy => hn _ (mapsTo_rectangleBorder_left_re s t hy))
  exact (((h₁.sub h₂).add (h₃.const_smul I)).sub (h₄.const_smul I)).const_smul _

theorem eventually_eq_twistZeroCount_of_boundary_ne_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (z : PrimeTorus N) {l u H : ℝ}
    (hlu : l ≤ u) (hH : 0 ≤ H)
    (hn : ∀ s ∈ RectangleBorder (⟨l, -H⟩ : ℂ) (⟨u, H⟩ : ℂ),
      dirichletSum (twistedCoefficients a N z) N s ≠ 0) :
    ∀ᶠ w in 𝓝 z, twistZeroCount a N hN ha l u H w = twistZeroCount a N hN ha l u H z := by
  have hc := continuousAt_twisted_rectangle_logDeriv a N z
    (⟨l, -H⟩ : ℂ) (⟨u, H⟩ : ℂ) hn
  have he := eventually_ne_zero_twist_compact a N z
    (isCompact_rectangleBorder (⟨l, -H⟩ : ℂ) (⟨u, H⟩ : ℂ)) hn
  have hb := Metric.tendsto_nhds.mp hc 1 zero_lt_one
  filter_upwards [he, hb] with w hw hdist
  have haz : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
  have haw : twistedCoefficients a N w 1 ≠ 0 := by rwa [twistedCoefficients_one]
  rw [rectangleIntegral_logDeriv_eq_verticalZeroCount hN haw hlu hH hw,
    rectangleIntegral_logDeriv_eq_verticalZeroCount hN haz hlu hH hn,
    dist_eq_norm] at hdist
  have hr := (abs_re_le_norm
    ((twistZeroCount a N hN ha l u H w : ℂ) -
      (twistZeroCount a N hN ha l u H z : ℂ))).trans_lt hdist
  simp only [Complex.sub_re, Complex.natCast_re] at hr
  have hi : |(twistZeroCount a N hN ha l u H w : ℤ) -
      (twistZeroCount a N hN ha l u H z : ℤ)| < 1 := by exact_mod_cast hr
  obtain ⟨h₁, h₂⟩ := abs_lt.mp hi
  omega

end Dubon2026
