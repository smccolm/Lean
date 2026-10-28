import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate
attribute [-instance] CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate
    {N : ℕ} [NeZero N] (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ) = 0) :
    ∃ (V : ℂ → ℂ) (b : ℍ) (m : ℍ → ℤ) (F : ℍ → ℂ → ℂ),
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ s ∈ S, Continuous (F s) ∧ HasCompactSupport (F s) ∧ tsupport (F s) ⊆ {z : ℂ | 0 < z.im} ∧
        ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
          Integrable (fun z : ℂ => E' z * F s z) ∧
            ∫ z : ℂ, E' z * F s z = Real.pi * (E s - E b)) ∧
      (∀ s ∈ S, (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℤ) * m s =
        2 * n s) ∧
      ∀ᵐ z : ℂ, 0 < z.im →
        (fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z =
          ∑ s ∈ S, (m s : ℂ) / 2 * ∑ᶠ γ : CongruenceSubgroup.Gamma0 N,
            F s (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
              conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate.solution
