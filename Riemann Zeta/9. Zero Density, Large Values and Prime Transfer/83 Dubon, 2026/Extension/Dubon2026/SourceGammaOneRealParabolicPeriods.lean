import Dubon2026.SourceGammaOneRealPeriodMap
import Dubon2026.SourceParabolicClassification

/-! DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Hecke characters -> Picard/H1 and Abel-Jacobi -> real period surjectivity.
The literal real character has zero value on every squared-trace-four
element. The existing signed-translation classification, actual primitive
shift and finite translated cusp limits discharge this condition. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem sourceGamma1_period_eq_zero_of_trace
    (N : ℕ) [NeZero N] (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    (γ : Gamma1 N) (hγ : γ.val.val.trace ^ 2 = 4) :
    sourceWeightTwoPeriodValue (Gamma1 N) f γ = 0 := by
  let H := (Gamma1 N).map (mapGL ℝ)
  let F := sourceWeightTwoPrimitive H.strictWidthInfty f
  obtain ⟨ε, δ, n, hε, he⟩ := SourceParabolic.classification γ.val hγ
  have ha (w : ℍ) : γ.val • (δ • w) = δ • ((n : ℝ) +ᵥ w) := by
    rw [he]
    rcases hε with rfl | rfl
    · rw [one_mul, mul_smul, mul_smul, inv_smul_smul, modular_T_zpow_smul]
    · rw [neg_one_mul, ModularGroup.SL_neg_smul,
        mul_smul, mul_smul, inv_smul_smul, modular_T_zpow_smul]
  have ht : Tendsto (fun w : ℍ => (n : ℝ) +ᵥ w) atImInfty atImInfty := by
    simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
    exact tendsto_comap.congr fun w => (vadd_im (n : ℝ) w).symm
  obtain ⟨L, hL⟩ := sourceWeightTwoPrimitive_exists_cusp_limit f
    H.strictWidthInfty_pos H.strictWidthInfty_mem_strictPeriods δ
  have hleft : Tendsto (fun w : ℍ => F (γ.val • (δ • w))) atImInfty (𝓝 L) := by
    simpa only [ha, Function.comp_def, F] using hL.comp ht
  have hright : Tendsto (fun w : ℍ => F (γ.val • (δ • w))) atImInfty
      (𝓝 (L + sourceWeightTwoPeriodValue (Gamma1 N) f γ)) := by
    have hp (w : ℍ) : F (δ • w) + sourceWeightTwoPeriodValue (Gamma1 N) f γ =
        F (γ.val • (δ • w)) :=
      (sourceWeightTwoPrimitive_period (Gamma1 N) f γ (δ • w)).symm
    exact (hL.add_const _).congr hp
  have heq := tendsto_nhds_unique hleft hright
  exact (add_left_cancel (heq.symm.trans (add_zero L).symm))

/-- The actual real characters vanishing on all parabolic elements. -/
def sourceGamma1RealParabolicHoms (N : ℕ) :
    Submodule ℝ (Additive (Gamma1 N) →+ ℝ) where
  carrier := {φ | ∀ γ : Gamma1 N, γ.val.val.trace ^ 2 = 4 →
    φ (Additive.ofMul γ) = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    simp only [AddMonoidHom.add_apply, hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    simp only [AddMonoidHom.smul_apply, hφ γ hγ, smul_zero]

theorem sourceGamma1RealPeriodHom_parabolic (N : ℕ) [NeZero N]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) :
    sourceGamma1RealPeriodHom N f ∈ sourceGamma1RealParabolicHoms N := by
  intro γ hγ
  rw [sourceGamma1RealPeriodHom_apply, sourceGamma1_period_eq_zero_of_trace N f γ hγ,
    Complex.zero_re]

/-- The proved real periods with their exact parabolic target. -/
def sourceGamma1RealParabolicPeriodHom (N : ℕ) [NeZero N] :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 →ₗ[ℝ] sourceGamma1RealParabolicHoms N :=
  (sourceGamma1RealPeriodHom N).codRestrict _ (sourceGamma1RealPeriodHom_parabolic N)

theorem sourceGamma1RealParabolicPeriodHom_injective (N : ℕ) [NeZero N] :
    Function.Injective (sourceGamma1RealParabolicPeriodHom N) := by
  intro f g h
  exact sourceGamma1RealPeriodHom_injective N (congrArg Subtype.val h)

theorem sourceGamma1RealParabolicHoms_finite (N : ℕ) [NeZero N] :
    Module.Finite ℝ (sourceGamma1RealParabolicHoms N) := by
  letI := sourceGamma1RealCharacter_finite N
  infer_instance

end
end Dubon2026
