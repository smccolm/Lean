from pathlib import Path
import json
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.lean.txt').read_text(encoding='utf-8-sig')
b=s[s.index('theorem main'):s.index('end ModularCurve.WindingLog')]
b=b.replace('theorem main','theorem exists_parabolic_log').replace('ModularCurve.Period.IsParabolicHom Γ m','(∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → m (Additive.ofMul γ) = 0)')
b=b[:b.index('  have hF := isEquivariantPrimitive')]+"""  intro γ hγ
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
  obtain ⟨c, hc⟩ := hlim δ
  have hleft : Tendsto (fun w : ℍ => Lext L₀ (γ.val • (δ • w))) atImInfty (𝓝 c) := by
    simpa only [ha, Function.comp_def] using hc.comp ht
  have hright : Tendsto (fun w : ℍ => Lext L₀ (γ.val • (δ • w))) atImInfty
      (𝓝 (c + 2 * π * Complex.I * (mHom L₀ hL₀ hinv (Additive.ofMul γ) : ℂ))) :=
    (hc.add_const _).congr fun w => (Lext_smul L₀ hL₀ hinv γ (δ • w)).symm
  have heq := tendsto_nhds_unique hleft hright
  have hz : (2 * π * Complex.I : ℂ) *
      (mHom L₀ hL₀ hinv (Additive.ofMul γ) : ℂ) = 0 :=
    add_left_cancel (heq.symm.trans (add_zero c).symm)
  exact_mod_cast (mul_eq_zero.1 hz).resolve_left two_pi_I_ne_zero

"""
head="""import SourceModularWindingCuspLimit
import Dubon2026.SourceParabolicClassification

/-! The literal integral logarithmic character vanishes on every element
of squared trace four. The existing signed-translation classification and
the proved finite translated cusp limits discharge parabolicity directly.
DUB-17/18 -> original all-weight association -> Gamma1 Picard/H1 ->
Abel-Jacobi converse -> analytic reciprocity -> winding-period comparison.
The function is arbitrary C1, invariant and nonzero with nonzero cusp limits;
construction of the actual comparison quotient remains a separate obligation.
The logarithm proof is adapted from the Apache-2.0 source pinned in
winding-log-reuse-route-887.json, with no external Period wrapper. -/
namespace Dubon2026.SourceWindingLog
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set Topology
open scoped MatrixGroups Topology Real

"""
with (p/'SourceModularParabolicWindingLog.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end\nend Dubon2026.SourceWindingLog\n')
