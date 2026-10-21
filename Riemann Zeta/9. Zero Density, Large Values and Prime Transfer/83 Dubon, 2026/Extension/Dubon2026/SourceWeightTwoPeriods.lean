import Dubon2026.SourcePeriodCocycle
import Dubon2026.SourceWeightTwoAnalyticPrimitive

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> period-pair injectivity. Evaluate the existing genuine polynomial period
map at the constant binary form in degree zero. Its cocycle law then gives
the actual weight-two additive periods, and the previously proved Eichler
transformation law identifies them with the constructed primitive shifts.
-/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup MvPolynomial SourceModularSymbols OnePoint UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- The constant binary form used to evaluate original weight-two periods. -/
def sourceWeightTwoConstant : homogeneousSubmodule (Fin 2) ℂ 0 :=
  ⟨1, isHomogeneous_one (Fin 2) ℂ⟩

/-- Substitution fixes the original constant binary form. -/
theorem sourceWeightTwoConstant_fixed (γ : SL(2, ℤ)) :
    sourceModularBinaryFormRep ℂ 0 (MulOpposite.op (γ : Matrix (Fin 2) (Fin 2) ℤ))
      sourceWeightTwoConstant = sourceWeightTwoConstant := by
  apply Subtype.ext
  change matrixPolynomialAction _ (1 : MvPolynomial (Fin 2) ℂ) = 1
  exact map_one _

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- Actual weight-two cusp periods, obtained from the already constructed linear period map. -/
def sourceWeightTwoPeriodValue :
    CuspForm (Γ.map (mapGL ℝ)) 2 →ₗ[ℂ] (Γ → ℂ) where
  toFun f γ := periodMap ℂ Γ (w := 0) (by norm_num) f
    (symbol (R := ℂ) (w := 0) Γ (mapGL ℚ γ.val • ∞) ∞ sourceWeightTwoConstant)
  map_add' f g := by
    funext γ
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c f := by
    funext γ
    simp only [_root_.map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]

/-- The new scalar period is exactly the convergent original cusp integral. -/
theorem sourceWeightTwoPeriodValue_apply
    (f : CuspForm (Γ.map (mapGL ℝ)) 2) (γ : Γ) :
    sourceWeightTwoPeriodValue Γ f γ =
      sourceCuspIntegral f ∞ (mapGL ℚ γ.val • ∞) := by
  change periodMap ℂ Γ (w := 0) (by norm_num) f
    (symbol (R := ℂ) (w := 0) Γ (mapGL ℚ γ.val • ∞) ∞ sourceWeightTwoConstant) = _
  rw [periodMap_symbol]
  congr 1
  funext z
  simp [periodIntegrand, sourceWeightTwoConstant]

/-- Evaluating the existing degree-zero cocycle recovers exactly the scalar period. -/
theorem sourceWeightTwoPeriodValue_cocycle
    (f : CuspForm (Γ.map (mapGL ℝ)) 2) (γ : Γ) :
    sourceWeightTwoPeriodValue Γ f γ =
      sourcePeriodCocycle f (w := 0) (by norm_num) ∞ γ sourceWeightTwoConstant := rfl

/-- The genuine cocycle is additive because its degree-zero coefficient is fixed. -/
theorem sourceWeightTwoPeriodValue_mul
    (f : CuspForm (Γ.map (mapGL ℝ)) 2) (γ δ : Γ) :
    sourceWeightTwoPeriodValue Γ f (γ * δ) =
      sourceWeightTwoPeriodValue Γ f γ + sourceWeightTwoPeriodValue Γ f δ := by
  let c := sourcePeriodCocycle f (w := 0) (by norm_num) ∞
  have hc : c (γ * δ) = c γ + (sourcePeriodDualRep Γ 0).ρ γ (c δ) := by
    simpa only [add_comm] using
      (groupCohomology.mem_cocycles₁_iff _).mp c.property γ δ
  have h := congrArg (fun L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ 0) =>
    L sourceWeightTwoConstant) hc
  change c (γ * δ) sourceWeightTwoConstant = c γ sourceWeightTwoConstant +
    ((sourcePeriodDualRep Γ 0).ρ γ (c δ)) sourceWeightTwoConstant at h
  rw [sourcePeriodDualRep_apply, sourceWeightTwoConstant_fixed] at h
  exact h

/-- The actual periods as a linear map to the native additive-character space. -/
def sourceWeightTwoPeriodHom :
    CuspForm (Γ.map (mapGL ℝ)) 2 →ₗ[ℂ] (Additive Γ →+ ℂ) where
  toFun f :=
    { toFun := fun γ => sourceWeightTwoPeriodValue Γ f γ.toMul
      map_zero' := by
        change sourceWeightTwoPeriodValue Γ f 1 = 0
        simp [sourceWeightTwoPeriodValue_apply]
      map_add' γ δ := sourceWeightTwoPeriodValue_mul Γ f γ.toMul δ.toMul }
  map_add' f g := by
    ext γ
    exact congrFun ((sourceWeightTwoPeriodValue Γ).map_add f g) γ
  map_smul' c f := by
    ext γ
    exact congrFun ((sourceWeightTwoPeriodValue Γ).map_smul c f) γ

/-- Original subgroup invariance turns the normalized Eichler transform into
the original scalar period, with its orientation preserved. -/
theorem sourceWeightTwoPrimitive_period
    (f : CuspForm (Γ.map (mapGL ℝ)) 2) (γ : Γ) (z : ℍ) :
    sourceWeightTwoPrimitive (Γ.map (mapGL ℝ)).strictWidthInfty f (γ.val • z) =
      sourceWeightTwoPrimitive (Γ.map (mapGL ℝ)).strictWidthInfty f z +
        sourceWeightTwoPeriodValue Γ f γ := by
  have hf : ⇑f = ⇑f ∣[(2 : ℤ)] γ.val := by
    rw [ModularForm.SL_slash, sourceSL_coe_eq_mapGL]
    exact (SlashInvariantFormClass.slash_action_eq f _
      (Subgroup.mem_map_of_mem _ γ.property)).symm
  rw [sourceWeightTwoPrimitive_transform f f
    (Γ.map (mapGL ℝ)).strictWidthInfty_pos
    (Γ.map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods
    (Γ.map (mapGL ℝ)).strictWidthInfty_pos
    (Γ.map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods γ.val hf,
    sourceWeightTwoPeriodValue_apply]
  congr 1
  have hd : 0 < ((mapGL ℚ γ.val : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact one_pos
  have he := sourceCuspIntegral_slash (⇑f) hd (mapGL ℚ γ.val⁻¹ • ∞) ∞
  rw [sourceRat_slash_mapGL, ← sourceSL_coe_eq_mapGL, ← ModularForm.SL_slash,
    ← hf, map_inv, smul_inv_smul] at he
  simpa only [map_inv] using he

end
end Dubon2026
