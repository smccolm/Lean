from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-peaked-core-1533/S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff.lean.txt').read_text(encoding='utf-8')
helper=t[t.index('theorem coe_mul_T_zpow_mul_S_inv'):t.index('\nend GCusp')]
helper=helper.replace('theorem coe_mul_T_zpow_mul_S_inv','private theorem coe_mul_T_zpow_mul_S_inv')
body=t[t.index('theorem solution'):].replace('theorem solution','theorem gammaOne_peaked_cusp_classes').replace('GCusp.coe_mul_T_zpow_mul_S_inv','coe_mul_T_zpow_mul_S_inv')
f=s/'SourceGammaOnePeakedCuspClasses1534a.lean';assert not f.exists()
f.write_text('''import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> even-weight peaked auxiliary existence. Match the
actual two exceptional signed cusp classes with the first-column residue
conditions used by the Bernoulli-order peak, retaining every level.
Reuse native Gamma1 membership and determinant one. No curve model,
degree equality or source cusp-classification premise is introduced.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary
open scoped MatrixGroups
open Matrix

'''+helper+'\n'+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary\n',encoding='utf-8')
