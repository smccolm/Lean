import Dubon2026.SourceOriginalHolomorphicDifferentials

/-! DUB-17/18 -> regular-differential cusp forms -> decay at every cusp.
A nonzero modular denominator has isolated zeros after any full modular
translate. Continuity extends an eventual estimate across those zeros.
This avoids introducing a separate Fourier leading-term nonvanishing theory.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology Manifold MatrixGroups

theorem eventually_ne_zero_modular_translate (N : ℕ) {k : ℤ}
    (h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (γ : SL(2, ℤ)) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, h (γ • w) ≠ 0 := by
  have hhol : MDiff (fun w : ℍ => h (γ • w)) := by
    have hdet : 0 < (γ : GL (Fin 2) ℝ).det.val := by
      change 0 < (γ : GL (Fin 2) ℝ).val.det
      have he : (γ : GL (Fin 2) ℝ).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
      rw [he]
      exact zero_lt_one
    simpa only [ModularGroup.sl_moeb] using h.holo'.comp (mdifferentiable_smul hdet)
  by_contra hcon
  have hfreq : ∃ᶠ w in 𝓝[≠] τ, h (γ • w) = 0 := by
    simpa only [Filter.not_eventually, not_not] using hcon
  have he := eq_zero_of_frequently hhol hfreq
  apply hh
  apply DFunLike.ext
  intro w
  have hw := congrFun he (γ⁻¹ • w)
  simpa only [smul_inv_smul, Pi.zero_apply, ModularForm.zero_apply] using hw

theorem eventually_le_of_punctured_nonzero {f g : ℍ → ℝ} {h : ℍ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hh : ∀ τ : ℍ, ∀ᶠ w in 𝓝[≠] τ, h w ≠ 0)
    (hb : ∀ᶠ τ : ℍ in atImInfty, h τ ≠ 0 → f τ ≤ g τ) :
    ∀ᶠ τ : ℍ in atImInfty, f τ ≤ g τ := by
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hb
  apply (atImInfty_mem _).mpr
  refine ⟨A + 1, ?_⟩
  intro τ hτ
  have hAτ : A < τ.im := by linarith
  have hev : ∀ᶠ w in 𝓝[≠] τ, A ≤ w.im :=
    ((continuous_im.continuousAt.eventually_const_lt hAτ).mono fun _ hw => hw.le).filter_mono
      nhdsWithin_le_nhds
  have hft : Tendsto f (𝓝[≠] τ) (𝓝 (f τ)) :=
    (hf.tendsto τ).mono_left nhdsWithin_le_nhds
  have hgt : Tendsto g (𝓝[≠] τ) (𝓝 (g τ)) :=
    (hg.tendsto τ).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hft hgt
  filter_upwards [hh τ, hev] with w hw hAw
  exact hA w hAw hw

end
end Dubon2026.SourceFunctionField
