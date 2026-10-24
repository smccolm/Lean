import Dubon2026.SourceEllipticPeriodUniformization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! Local inverse coordinates for the actual period map. A holomorphic
affine curve-valued map with nonzero y-coordinate lifts holomorphically
through the Weierstrass functions. The native analytic inverse theorem
inverts x, while the curve equation and continuity determine the y-sign.
SourceEllipticPeriodQuotientGerm supplies these coordinate hypotheses
for the DUB-17/18 quotient-product identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set WeierstrassCurve WeierstrassCurve.Affine
open scoped Topology PeriodPair

theorem local_lift_of_affine_coordinates (M : PeriodPair) [(periodCurve M).IsElliptic]
    (f : ℂ → (periodCurve M).toAffine.Point) (z₀ : ℂ)
    {U : Set ℂ} (hU : U ∈ 𝓝 z₀) (X Y : ℂ → ℂ)
    (hXd : DifferentiableOn ℂ X U) (hYd : DifferentiableOn ℂ Y U)
    (hcoord : ∀ z ∈ U, Y z ≠ 0 ∧ ∃ h, f z = Point.some (X z) (Y z) h) :
    ∃ V ∈ 𝓝 z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G V ∧
      ∀ z ∈ V, periodHom M (G z) = f z := by
  obtain ⟨U', hU'U, hU'open, hz₀U'⟩ := mem_nhds_iff.mp hU
  obtain ⟨hYz₀, hnsz₀, hcoord₀⟩ := hcoord z₀ (hU'U hz₀U')
  obtain ⟨w₀, hw₀⟩ := (periodHom_surjective M) (.some (X z₀) (Y z₀) hnsz₀)
  have hw₀Λ : w₀ ∉ M.lattice := by
    intro hmem
    have h0 : (periodHom M) w₀ = 0 := by
      rw [← AddMonoidHom.mem_ker, (ker_periodHom M)]; exact hmem
    exact Point.some_ne_zero _ (hw₀ ▸ h0)
  have hPw₀ : ℘[M] w₀ = X z₀ ∧ ℘'[M] w₀ / 2 = Y z₀ := by
    have h : periodPoint M w₀ = .some (X z₀) (Y z₀) hnsz₀ := hw₀
    rwa [periodPoint_of_notMem M hw₀Λ, Point.some.injEq] at h
  have hder : deriv ℘[M] w₀ ≠ 0 := by
    simp only [PeriodPair.deriv_weierstrassP]
    exact fun h0 => hYz₀ (by rw [← hPw₀.2, h0, zero_div])
  have hPa : AnalyticAt ℂ ℘[M] w₀ := M.analyticOnNhd_weierstrassP w₀ hw₀Λ
  set ψ := hPa.hasStrictDerivAt.localInverse ℘[M] (deriv ℘[M] w₀) w₀ hder with hψdef
  have hψa : AnalyticAt ℂ ψ (X z₀) := hPw₀.1 ▸ hPa.analyticAt_localInverse hder
  have hψw₀ : ψ (X z₀) = w₀ :=
    hPw₀.1 ▸ HasStrictFDerivAt.localInverse_apply_image _
  set G := ψ ∘ X with hGdef
  have hXcont : ContinuousAt X z₀ := (hXd.differentiableAt hU).continuousAt
  have hGcont : ContinuousAt G z₀ := hψa.continuousAt.comp hXcont
  have hGz₀ : G z₀ = w₀ := hψw₀
  have hevΛ : ∀ᶠ z in 𝓝 z₀, G z ∉ M.lattice :=
    hGcont.eventually (M.isClosed_lattice.isOpen_compl.mem_nhds (hGz₀ ▸ hw₀Λ))
  have hevR : ∀ᶠ z in 𝓝 z₀, ℘[M] (G z) = X z := by
    have h := hPw₀.1 ▸ hPa.hasStrictDerivAt.eventually_right_inverse hder
    exact hXcont.eventually h
  have hevψd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ ψ (X z) :=
    hXcont.eventually
      ((AnalyticAt.eventually_analyticAt hψa).mono fun _ hy => hy.differentiableAt)
  have hevXd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ X z :=
    eventually_of_mem (hU'open.mem_nhds hz₀U') fun z hz =>
      (hXd.mono hU'U).differentiableAt (hU'open.mem_nhds hz)
  have hevU : ∀ᶠ z in 𝓝 z₀, z ∈ U :=
    eventually_of_mem (hU'open.mem_nhds hz₀U') hU'U
  have hevSgn : ∀ᶠ z in 𝓝 z₀, ℘'[M] (G z) / 2 + Y z ≠ 0 := by
    have hP'cont : ContinuousAt ℘'[M] (G z₀) := by
      rw [hGz₀]; exact (M.analyticOnNhd_derivWeierstrassP w₀ hw₀Λ).continuousAt
    have hcont : ContinuousAt (fun z => ℘'[M] (G z) / 2 + Y z) z₀ :=
      ((hP'cont.comp hGcont).div_const 2).add (hYd.differentiableAt hU).continuousAt
    refine hcont.eventually (isOpen_ne.mem_nhds ?_)
    show ℘'[M] (G z₀) / 2 + Y z₀ ≠ 0
    rw [hGz₀, hPw₀.2, ← two_mul]; exact mul_ne_zero two_ne_zero hYz₀
  obtain ⟨V, hVmem, hVopen, hVz₀⟩ := eventually_nhds_iff.mp
    (((((hevΛ.and hevR).and hevψd).and hevXd).and hevU).and hevSgn)
  refine ⟨V, hVopen.mem_nhds hVz₀, G, ?_, fun z hz => ?_⟩
  ·
    exact fun z hz =>
      ((hVmem z hz).1.1.1.2.comp z (hVmem z hz).1.1.2).differentiableWithinAt
  ·
    obtain ⟨⟨⟨⟨⟨hGzΛ, hPGz⟩, -⟩, -⟩, hzU⟩, hsgn⟩ := hVmem z hz
    obtain ⟨hYz, hnsz, hcoordz⟩ := hcoord z hzU
    have hPGy : ℘'[M] (G z) / 2 = Y z := by
      have h1 : (℘'[M] (G z) / 2) ^ 2 = Y z ^ 2 := by
        have hG := (WeierstrassCurve.Affine.equation_iff _ _).mp
          (hPGz ▸ periodCurve_equation M hGzΛ)
        have hY := (WeierstrassCurve.Affine.equation_iff _ _).mp hnsz.1
        simp only [periodCurve,
          zero_mul, add_zero] at hG hY
        exact hG.trans hY.symm
      have hfac : (℘'[M] (G z) / 2 - Y z) * (℘'[M] (G z) / 2 + Y z) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hsgn
    change periodPoint M (G z) = f z
    rw [periodPoint_of_notMem M hGzΛ, hcoordz, Point.some.injEq]
    exact ⟨hPGz, hPGy⟩

end Dubon2026.SourceEllipticPeriod
