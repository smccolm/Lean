import Dubon2026.SourceIntegralEisensteinHolomorphic
import Mathlib.NumberTheory.ModularForms.Basic

/-! DUB-17/18 -> original Gamma1 coordinate-degree preservation -> integral
Eisenstein separating functions. The actual weight-four congruence sum is
bounded at every rational cusp, hence is a genuine modular form. Reuse the
native Mathlib lattice majorant, vertical-strip reduction and cusp criterion.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean. -/
namespace Dubon2026.SourceFunctionField.GammaOne.IntegralEisenstein
noncomputable section
open scoped MatrixGroups CongruenceSubgroup ModularForm Topology Manifold Matrix
open UpperHalfPlane hiding I
open EisensteinSeries Filter Complex

private theorem norm_series_le (N : ℕ) (a : Fin 2 → ZMod N) (z : ℍ) :
    ‖series N a z‖ ≤ ∑' (x : Fin 2 → ℤ), ‖eisSummand 4 x z‖ := by
  unfold series
  exact (norm_tsum_le_tsum_norm ((summable_norm_eisSummand (by norm_num : 3 ≤ (4 : ℤ)) z).subtype _)).trans
    (Summable.tsum_subtype_le (fun x : Fin 2 → ℤ => ‖eisSummand 4 x z‖) _
      (fun _ => norm_nonneg _) (summable_norm_eisSummand (by norm_num) z))

theorem slashInvariant_bounded {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N)
    (A : SL(2, ℤ)) : IsBoundedAtImInfty (series N a ∣[(4 : ℤ)] A) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨∑' x : Fin 2 → ℤ, r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-4 : ℤ) * ‖x‖ ^ (-4 : ℤ), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N)
  rw [series_slash]
  change ‖slashInvariant N (a ᵥ* A) z‖ ≤ _
  rw [← SlashInvariantForm.T_zpow_width_invariant N 4 n (slashInvariant N (a ᵥ* A)) z]
  refine (norm_series_le N (a ᵥ* A) _).trans ?_
  apply (summable_norm_eisSummand (by norm_num : 3 ≤ (4 : ℤ)) _).tsum_le_tsum _
  · exact_mod_cast (summable_one_div_norm_rpow (show (2 : ℝ) < 4 by norm_num)).mul_left
      (r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-4 : ℤ))
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast summand_bound_of_mem_verticalStrip (by norm_num : (0 : ℝ) ≤ 4)
      x two_pos (verticalStrip_anti_right N hz hn)

/-- The actual weight-four congruence Eisenstein series as a modular form. -/
def modularForm (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) : ModularForm Γ(N) 4 where
  toFun := slashInvariant N a
  slash_action_eq' := (slashInvariant N a).slash_action_eq'
  holo' := slashInvariant_mdifferentiable N a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ => slashInvariant_bounded a γ

theorem modularForm_coe (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) :
    (modularForm N a : ℍ → ℂ) = series N a := rfl

end
end Dubon2026.SourceFunctionField.GammaOne.IntegralEisenstein
