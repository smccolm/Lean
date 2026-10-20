import Dubon2026.SourceEichlerCuspPolynomial
import Mathlib.NumberTheory.ModularForms.NormTrace

/-! The cohomologically corrected original Eichler integral is a modular form.
DUB-17/18 -> modular Galois association -> original analytic H1 injectivity.
The actual coboundary gives invariance; at every rational cusp the translated
primitive is its decaying Fourier series plus a periodic polynomial. The
polynomial correction is constant. This discharges the all-cusps boundedness hypothesis of
pinned nonpositive-weight vanishing.
-/

namespace Dubon2026
noncomputable section
open Complex ConjAct Matrix.SpecialLinearGroup MvPolynomial OnePoint
open UpperHalfPlane hiding I
open scoped Real Nat MatrixGroups ModularForm Manifold Pointwise

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {n : ℕ}
    (f : CuspForm (Γ.map (mapGL ℝ)) k) (hk : k = n + 2) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods)
    (L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ n))
    (hL : ∀ γ : Γ,
      sourcePeriodCocycle f hk ∞ γ = (sourcePeriodDualRep Γ n).ρ γ L - L)

/-- The actual scalar Eichler integral with its original coboundary correction is slash invariant. -/
def sourceCorrectedEichlerSlashInvariant : SlashInvariantForm (Γ.map (mapGL ℝ)) (-(n : ℤ)) where
  toFun τ := sourceEichlerIntegral h (n + 1) f τ -
    (-2 * π * I) ^ (n + 1) / (n ! : ℂ) * (sourcePeriodCorrectionPolynomial n L).eval (τ : ℂ)
  slash_action_eq' := by
    rintro γ ⟨σ, hσ, rfl⟩
    rw [← sourceSL_coe_eq_mapGL, ← ModularForm.SL_slash]
    exact sourceEichlerIntegral_corrected_slash f hk hh hΓ L hL ⟨σ, hσ⟩

/-- Every rational-cusp translate of the corrected original primitive is bounded. -/
theorem sourceCorrectedEichler_bounded_slash (σ : SL(2, ℤ)) :
    IsBoundedAtImInfty
      (⇑(sourceCorrectedEichlerSlashInvariant f hk hh hΓ L hL) ∣[-(n : ℤ)] σ) := by
  let Δ := toConjAct (mapGL ℝ σ)⁻¹ • Γ.map (mapGL ℝ)
  have : Δ.IsArithmetic := by
    have he : Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (mapGL ℚ σ) = mapGL ℝ σ := by
      rw [Subsingleton.elim (Rat.castHom ℝ) (algebraMap ℚ ℝ), map_mapGL]
    simpa only [map_inv, he] using
      Subgroup.IsArithmetic.conj (Γ.map (mapGL ℝ)) (mapGL ℚ σ)⁻¹
  let f' := _root_.CuspForm.translate f (mapGL ℝ σ)
  have hf' : ⇑f' = ⇑f ∣[k] σ := by
    change (⇑f ∣[k] (mapGL ℝ σ)) = _
    rw [ModularForm.SL_slash, sourceSL_coe_eq_mapGL]
  let E := sourceCorrectedEichlerSlashInvariant f hk hh hΓ L hL
  let E' := SlashInvariantForm.translate E (mapGL ℝ σ)
  have hE' : ⇑E' = ⇑E ∣[-(n : ℤ)] σ := by
    change (⇑E ∣[-(n : ℤ)] (mapGL ℝ σ)) = _
    rw [ModularForm.SL_slash, sourceSL_coe_eq_mapGL]
  obtain ⟨p, hp⟩ := sourceEichlerIntegral_corrected_slash_exists_polynomial hk f f'
    hh hΓ Δ.strictWidthInfty_pos Δ.strictWidthInfty_mem_strictPeriods σ hf' L
  have hp' (τ : UpperHalfPlane) :
      E' τ = sourceEichlerIntegral Δ.strictWidthInfty (n + 1) f' τ + p.eval (τ : ℂ) := by
    rw [hE']
    exact hp τ
  rw [← hE']
  exact sourceEichlerIntegral_polynomial_bounded Δ.strictWidthInfty_pos n f' E' p
    (SlashInvariantFormClass.periodic_comp_ofComplex f' Δ.strictWidthInfty_mem_strictPeriods)
    (ModularFormClass.holo f') (ModularFormClass.bdd_at_infty f') hp'
    (fun τ => SlashInvariantForm.vAdd_apply_of_mem_strictPeriods E' τ
      Δ.strictWidthInfty_mem_strictPeriods)

/-- The original corrected primitive is holomorphic and bounded at all cusps,
so is an actual modular form of weight minus the binary-form degree. -/
def sourceCorrectedEichlerModularForm : ModularForm (Γ.map (mapGL ℝ)) (-(n : ℤ)) where
  toSlashInvariantForm := sourceCorrectedEichlerSlashInvariant f hk hh hΓ L hL
  holo' := by
    have hE := mdifferentiable_sourceEichlerIntegral hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) (n + 1)
    have hp : MDiff (fun τ : UpperHalfPlane =>
        (sourcePeriodCorrectionPolynomial n L).eval (τ : ℂ)) :=
      fun τ => (sourcePeriodCorrectionPolynomial n L).differentiableAt.mdifferentiableAt.comp τ
        (mdifferentiable_coe τ)
    exact hE.sub (mdifferentiable_const.mul hp)
  bdd_at_cusps' := by
    intro c hc
    have hc' := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
    obtain ⟨σ, hσ⟩ := isCusp_SL2Z_iff'.mp hc'
    exact (isBoundedAt_iff_exists_SL2Z hc').mpr
      ⟨σ, hσ.symm, sourceCorrectedEichler_bounded_slash f hk hh hΓ L hL σ⟩

end
end Dubon2026
