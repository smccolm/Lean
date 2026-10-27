import Dubon2026.SourceFrickeCuspInputs
import Dubon2026.SourceGammaOneCuspAuxiliaryForm

/-! DUB-17/18 -> original Gamma1 global charts -> orbit separation.
The actual normalized torsion Weierstrass functions already have proved
transformation, holomorphy and cusp bounds. Package their fixed row (0,t)
as native weight-two Gamma1 forms. This normalization is one twelfth of W
in the selected Apache-2.0 source at anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.
The explicit coefficient formula is not needed for orbit separation. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceFricke
open scoped MatrixGroups ModularForm Manifold

theorem wpNormZ_slash_eq {N : ℕ} [NeZero N]
    (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    (wpNormZ N a) ∣[(2 : ℤ)] γ = wpNormZ N (vecMulSL N a γ) := by
  funext τ
  rw [ModularForm.SL_slash_apply, wpNormZ_slash]
  change (denomZ γ τ ^ 2 * wpNormZ N (vecMulSL N a γ) τ) *
    denomZ γ τ ^ (-(2 : ℤ)) = _
  rw [zpow_neg, zpow_ofNat, mul_comm (denomZ γ τ ^ 2), mul_inv_cancel_right₀ (pow_ne_zero _ (denomZ_ne_zero γ τ))]

private theorem division_index_ne_zero {N : ℕ} {t : ZMod N} (ht : t ≠ 0) :
    (![0, t] : Fin 2 → ZMod N) ≠ 0 := by
  intro he
  exact ht (congrFun he 1)

private theorem division_index_fixed {N : ℕ} (t : ZMod N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) :
    vecMulSL N ![0, t] γ = ![0, t] := by
  obtain ⟨h00, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem N γ).mp hγ
  funext i
  fin_cases i <;> simp [vecMulSL_apply, h11, h10]

/-- The actual normalized Weierstrass value at the nonzero row (0,t). -/
def divisionForm (N : ℕ) [NeZero N] (t : ZMod N) (ht : t ≠ 0) :
    ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := wpNormZ N ![0, t]
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have he := wpNormZ_slash_eq ![0, t] γ
    rw [division_index_fixed t γ hγ] at he
    rwa [ModularForm.SL_slash] at he
  holo' := mdifferentiable_wpNormZ _ (division_index_ne_zero ht)
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [wpNormZ_slash_eq]
    exact isBoundedAtImInfty_wpNormZ _ (vecMulSL_ne_zero (division_index_ne_zero ht) γ)

theorem divisionForm_apply (N : ℕ) [NeZero N] (t : ZMod N) (ht : t ≠ 0) (τ : ℍ) :
    divisionForm N t ht τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (periodPairOfTau τ) ((t.val : ℂ) / N) := by
  change wpNormZ N ![0, t] τ = _
  simp [wpNormZ, frickeTorsionPt]


theorem divisionForm_slash_gamma0 (N : ℕ) [NeZero N] (t : ZMod N) (ht : t ≠ 0)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (divisionForm N t ht : ℍ → ℂ) ∣[(2 : ℤ)] γ =
      wpNormZ N ![0, t * ((γ 1 1 : ℤ) : ZMod N)] := by
  change (wpNormZ N ![0, t]) ∣[(2 : ℤ)] γ = _
  rw [wpNormZ_slash_eq]
  congr 1
  funext i
  have h10 := CongruenceSubgroup.Gamma0_mem.mp hγ
  fin_cases i <;> simp [vecMulSL_apply, h10]

end
end Dubon2026.SourceFunctionField.GammaOne
