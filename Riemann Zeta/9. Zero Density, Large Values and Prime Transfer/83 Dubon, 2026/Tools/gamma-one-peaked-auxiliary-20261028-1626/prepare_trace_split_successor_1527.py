from pathlib import Path
s=Path(__file__).parent;a=s/'SourceIntegralTraceTransversalSplit1525a.lean';b=s/'SourceIntegralTraceTransversalSplit1525b.lean';assert not b.exists()
t=a.read_text(encoding='utf-8').replace('  rw [← zpow_natCast, ModularGroup.coe_T_zpow, ModularGroup.coe_S] at this', '  simp only at this\n  rw [← zpow_natCast, ModularGroup.coe_T_zpow, ModularGroup.coe_S] at this')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
f=s/'SourceIntegralTraceDecomposition1526a.lean';assert not f.with_suffix('.log').exists()
f.write_text(f.read_text(encoding='utf-8').replace('import SourceIntegralTraceTransversalSplit1525a','import SourceIntegralTraceTransversalSplit1525b'),encoding='utf-8')
t=(s/'anthropic-peaked-integrality-depth-1498/S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.lean.txt').read_text(encoding='utf-8')
body=t[t.index('theorem T_mem_of_S_mul_T_zpow_mem'):t.index('\ntheorem coeff_qExpansion_one_eq_of_T_mem')]
f=s/'SourceIntegralTraceDegenerateCusp1527a.lean';assert not f.exists()
f.write_text('''import SourceIntegralTraceSlashPeriods1523b
import Dubon2026.SourceQExpansionPeriodWidth

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. In the coincident-cusp
case, even weight makes the S-slash equal the original form. The native
width-change theorem then gives coefficient integrality immediately,
without the upstream odd-weight auxiliary argument. The even-ratio
reduction proves that this restricted branch covers the original field
generators. The group conjugation calculation is adapted from the pinned
Anthropic trace proof, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane

'''+body+'''
theorem slash_coeff_mem_of_coincident_cusps
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k : ℤ} (hk : Even k)
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n, (qExpansion (h : ℝ) (⇑G : ℍ → ℂ)).coeff n ∈ R)
    (hdeg : ∃ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∈ Γ ∨
      -(ModularGroup.S * ModularGroup.T ^ j) ∈ Γ) (n : ℕ) :
    (qExpansion 1 ((⇑G : ℍ → ℂ) ∣[k]
      ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R := by
  obtain ⟨j, hj⟩ := hdeg
  have hT1 := T_mem_of_S_mul_T_zpow_mem Γ hS hj
  have hGj := slash_eq_of_mem_or_neg_mem G hk _ hj
  rw [← ModularForm.SL_slash] at hGj
  have hGS := congrArg (fun F : ℍ → ℂ => F ∣[k] (ModularGroup.T ^ j)⁻¹) hGj
  rw [← SlashAction.slash_mul, mul_inv_cancel_right, ModularForm.SL_slash,
    ModularForm.SL_slash] at hGS
  rw [SlashInvariantForm.slash_action_eqn G _
    (Subgroup.mem_map_of_mem _ (Γ.inv_mem (Γ.zpow_mem hT1 j)))] at hGS
  rw [hGS]
  have hper : Function.Periodic ((⇑G : ℍ → ℂ) ∘ ofComplex) (1 : ℝ) := by
    simpa using periodic_of_pm_mem G hk 1 (Or.inl (by simpa using hT1))
  have hc := SourceFricke.qExpansion_coeff_width (⇑G) hh.ne' hper
    (ModularFormClass.holo G) (ModularFormClass.bdd_at_infty G) (h * n)
  rw [if_pos (dvd_mul_right h n), Nat.mul_div_cancel_left n hh] at hc
  rw [← hc]
  exact hG _

end
end Dubon2026.SourceFunctionField.IntegralTrace
''',encoding='utf-8')
