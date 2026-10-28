import Dubon2026.SourceMeromorphicPrimitiveSpecification

/-! DUB17/18 -> actual Gamma1 Picard/H1 -> Abel-Jacobi principal-divisor converse ->
actual meromorphic function -> multiplier covariance. Adapt only the necessary
integer-residue integration consumer and multiplier argument, reusing the
proved global primitive, native analytic action and punctured-domain connectivity.
Actual analytic differential input and nonzero cusp limits remain. -/
namespace Dubon2026.SourceMeromorphicPrimitiveMultiplier
noncomputable section
open scoped MatrixGroups Topology ModularForm
open UpperHalfPlane Filter Set Metric

/-- The actual modular action in the complex coordinate. -/
def μ (g : SL(2, ℤ)) (z : ℂ) : ℂ := ((g • ofComplex z : ℍ) : ℂ)

theorem μ_coe (g : SL(2, ℤ)) (τ : ℍ) : μ g τ = ((g • τ : ℍ) : ℂ) := by
  simp [μ, ofComplex_apply]

theorem μ_im_pos (g : SL(2, ℤ)) (z : ℂ) : 0 < (μ g z).im := (g • ofComplex z).im_pos

theorem μ_of_im_pos (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    μ g z = ((g • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := by
  rw [μ, ofComplex_apply_of_im_pos hz]

theorem hasDerivAt_μ (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (μ γ) (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ)) = μ γ := by
    funext z
    rw [μ, MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem continuousAt_μ (γ : SL(2, ℤ)) (τ : ℍ) : ContinuousAt (μ γ) ↑τ :=
  (hasDerivAt_μ γ τ).continuousAt

theorem slash_two_apply (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(2 : ℤ)] γ) τ =
      f (γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) :=
  ModularForm.SL_slash_apply f γ τ


theorem eventually_μ_ne (γ : SL(2, ℤ)) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), μ γ z ≠ μ γ τ := by
  have h1 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  filter_upwards [h1, self_mem_nhdsWithin] with z hz hzτ
  rw [μ_of_im_pos γ hz, μ_coe]
  intro h
  have h' : γ • (⟨z, hz⟩ : ℍ) = γ • τ := UpperHalfPlane.ext h
  have h'' := MulAction.injective γ h'
  exact hzτ (congrArg UpperHalfPlane.coe h'')

theorem tendsto_μ_nhdsNE (γ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (μ γ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
  rw [← μ_coe]
  refine tendsto_nhdsWithin_iff.mpr ⟨(continuousAt_μ γ τ).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  exact eventually_μ_ne γ τ

theorem μ_inv_μ (γ : SL(2, ℤ)) (τ : ℍ) : μ γ⁻¹ (μ γ τ) = τ := by
  rw [μ_coe, μ_coe, inv_smul_smul]


end
end Dubon2026.SourceMeromorphicPrimitiveMultiplier
