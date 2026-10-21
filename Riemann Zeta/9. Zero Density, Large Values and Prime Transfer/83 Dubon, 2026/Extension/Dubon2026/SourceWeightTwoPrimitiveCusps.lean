import Dubon2026.SourceWeightTwoAnalyticPrimitive

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> period-pair injectivity -> actual finite limits of original primitives.
The exact existing Eichler transformation expresses each original cusp
translate as a decaying translated Eichler series plus its literal cusp
integral. No boundedness or cusp-limit hypothesis is supplied.
-/
namespace Dubon2026
noncomputable section
open Complex UpperHalfPlane Filter ConjAct Matrix.SpecialLinearGroup OnePoint
open scoped Topology Real ModularForm MatrixGroups Pointwise

/-- The actual normalized first Eichler primitive tends to zero at the original cusp. -/
theorem sourceWeightTwoPrimitive_tendsto
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 2) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Tendsto (sourceWeightTwoPrimitive h f) atImInfty (𝓝 0) := by
  have he := isZeroAtImInfty_sourceEichlerIntegral hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) 0
  simpa only [sourceWeightTwoPrimitive, Nat.zero_add, mul_zero] using
    he.const_mul (2 * π * Complex.I)⁻¹

/-- Every original integral cusp has a finite limit for the constructed primitive,
derived from the translated original cusp form and its exact period integral. -/
theorem sourceWeightTwoPrimitive_exists_cusp_limit
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 2) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (σ : SL(2, ℤ)) :
    ∃ L : ℂ, Tendsto (fun τ : ℍ => sourceWeightTwoPrimitive h f (σ • τ))
      atImInfty (𝓝 L) := by
  let Δ := toConjAct (mapGL ℝ σ)⁻¹ • Γ
  letI : Δ.IsArithmetic := by
    have he : Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (mapGL ℚ σ) = mapGL ℝ σ := by
      rw [Subsingleton.elim (Rat.castHom ℝ) (algebraMap ℚ ℝ), map_mapGL]
    simpa only [map_inv, he] using Subgroup.IsArithmetic.conj Γ (mapGL ℚ σ)⁻¹
  let f' : CuspForm Δ 2 := _root_.CuspForm.translate f (mapGL ℝ σ)
  have hf' : ⇑f' = ⇑f ∣[(2 : ℤ)] σ := by
    change (⇑f ∣[(2 : ℤ)] (mapGL ℝ σ)) = _
    rw [ModularForm.SL_slash, sourceSL_coe_eq_mapGL]
  let L := sourceCuspIntegral f' (mapGL ℚ σ⁻¹ • (∞ : OnePoint ℚ)) ∞
  have he (τ : ℍ) := sourceWeightTwoPrimitive_transform f f' hh hΓ
    Δ.strictWidthInfty_pos Δ.strictWidthInfty_mem_strictPeriods σ hf' τ
  have hl := (sourceWeightTwoPrimitive_tendsto f'
    Δ.strictWidthInfty_pos Δ.strictWidthInfty_mem_strictPeriods).add_const L
  refine ⟨L, ?_⟩
  simpa only [zero_add] using hl.congr (fun τ => (he τ).symm)

end
end Dubon2026
