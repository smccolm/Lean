import Dubon2026.SourceWeightTwoPeriodPair

/-! DUB-17/18 -> residual Galois association -> actual parabolic Hecke
realization. The existing cocycle's explicit cusp coboundary vanishes after
evaluation in degree zero. Thus the injective original period pair takes
values in the precise parabolic subspace already used by the residual
weight-two alternative.
-/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup OnePoint SourceCuspBoundary
open scoped MatrixGroups

/-- A fixed original cusp kills the actual scalar period: the original
cocycle's explicit parabolic coboundary has trivial constant coefficient. -/
theorem sourceWeightTwoPeriodValue_eq_zero_of_fix
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm (Γ.map (mapGL ℝ)) 2)
    (γ : Γ) (β : OnePoint ℚ) (hγ : mapGL ℚ γ.val • β = β) :
    sourceWeightTwoPeriodValue Γ f γ = 0 := by
  obtain ⟨b, hb⟩ := sourcePeriodCocycle_parabolic f (w := 0) (by norm_num) ∞ β
  have h := congrArg (fun L : Module.Dual ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ 0) =>
    L sourceWeightTwoConstant) (hb γ hγ)
  change sourcePeriodCocycle f (w := 0) (by norm_num) ∞ γ sourceWeightTwoConstant =
    ((sourcePeriodDualRep Γ 0).ρ γ b) sourceWeightTwoConstant -
      b sourceWeightTwoConstant at h
  rw [sourcePeriodDualRep_apply, sourceWeightTwoConstant_fixed, sub_self] at h
  exact h

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
/-- The actual level translation fixes its original rational cusp. -/
theorem sourceWeightTwo_cusp_translation_fix (δ : SL(2, ℤ)) :
    mapGL ℚ (uOf N δ).val • (mapGL ℚ δ • (∞ : OnePoint ℚ)) = mapGL ℚ δ • ∞ := by
  have hT : mapGL ℚ (ModularGroup.T ^ (N : ℤ)) • (∞ : OnePoint ℚ) = ∞ := by
    apply smul_infty_eq_self_iff.mpr
    change (((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) 1 0 : ℤ) : ℚ) = 0
    rw [ModularGroup.coe_T_zpow]
    norm_num
  rw [coe_uOf, map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_smul, hT]

/-- Every actual weight-two period character lies in the existing parabolic subspace. -/
theorem sourceWeightTwoPeriodHom_parabolic
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) :
    sourceWeightTwoPeriodHom (Gamma0 N) f ∈ parabolicHoms N := by
  apply mem_parabolicHoms_of_B_eq_zero
  intro δ
  exact sourceWeightTwoPeriodValue_eq_zero_of_fix (Gamma0 N) f (uOf N δ)
    (mapGL ℚ δ • ∞) (sourceWeightTwo_cusp_translation_fix N δ)

/-- Integral reflection preserves the literal trace defining parabolicity. -/
theorem sourceJConjugateSL_trace (γ : SL(2, ℤ)) :
    (sourceJConjugateSL γ).val.trace = γ.val.trace := by
  simp [Matrix.trace_fin_two, sourceJConjugateSL]

omit [NeZero N] in
/-- The actual reflection preserves the exact existing parabolic character space. -/
theorem sourceWeightTwoPeriodReflection_parabolic
    (φ : Additive (Gamma0 N) →+ ℂ) (hφ : φ ∈ parabolicHoms N) :
    sourceWeightTwoPeriodReflection N φ ∈ parabolicHoms N := by
  intro γ hγ
  apply hφ (sourceJConjugateGamma0 N γ)
  change (sourceJConjugateSL γ.val).val.trace ^ 2 = 4
  rw [sourceJConjugateSL_trace]
  exact hγ

/-- The injective pair of actual cusp-form periods takes values in the
same parabolic space as the original complex Hecke lift. -/
def sourceWeightTwoParabolicPeriodPair :
    (CuspForm ((Gamma0 N).map (mapGL ℝ)) 2 ×
      CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) →ₗ[ℂ] parabolicHoms N :=
  (sourceWeightTwoPeriodPair N).codRestrict (parabolicHoms N) (fun fg =>
    (parabolicHoms N).sub_mem
      ((parabolicHoms N).add_mem
        ((parabolicHoms N).add_mem
          (sourceWeightTwoPeriodHom_parabolic N fg.1)
          (sourceWeightTwoPeriodReflection_parabolic N _
            (sourceWeightTwoPeriodHom_parabolic N fg.1)))
        (sourceWeightTwoPeriodHom_parabolic N fg.2))
      (sourceWeightTwoPeriodReflection_parabolic N _
        (sourceWeightTwoPeriodHom_parabolic N fg.2)))

/-- The actual period pair remains injective in the required parabolic target. -/
theorem sourceWeightTwoParabolicPeriodPair_injective :
    Function.Injective (sourceWeightTwoParabolicPeriodPair N) := by
  intro x y h
  exact sourceWeightTwoPeriodPair_injective N (congrArg Subtype.val h)

end
end Dubon2026
