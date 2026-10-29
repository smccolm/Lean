from pathlib import Path
s=Path(__file__).parent
a=s/'SourceIntegralTraceCoefficientExtraction1514b.lean';b=s/'SourceIntegralTraceCoefficientExtraction1514c.lean'
assert not b.exists()
b.write_text(a.read_text(encoding='utf-8').replace('(δ : ℝ) (hδ : 0 ≤ δ)','(δ : ℝ)'),encoding='utf-8')
a.rename(a.with_suffix('.lean.txt'))
t=(s/'anthropic-trace-dependencies-1510/S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S.lean.txt').read_text(encoding='utf-8')
body=t[t.index('theorem solution'):]
body=body.replace('theorem solution','theorem exists_signed_cusp_transversal')
start=body.index('  have hneg_inv');end=body.index("  have hmemΓ'",start)
body=body[:start]+"  let Γ' : Subgroup SL(2, ℤ) := plusMinus Γ\n"+body[end:]
body=body.replace(':= fun g => Iff.rfl', ':= fun g => mem_plusMinus_iff Γ g')
body=body.replace("  have hΓle : Γ ≤ Γ' := fun g hg => Or.inl hg", "  have hΓle : Γ ≤ Γ' := le_plusMinus Γ")
body=body.replace('by rw [zpow_natCast]; exact hT', "by rw [zpow_natCast]; exact (hmemΓ' _).mpr hT")
body=body.replace('∀ i : ℕ, i < h₀ → π (T ^ i) ≠ π S','∀ i : ℕ, π (T ^ i) ≠ π S').replace('    intro i hi h\n', '    intro i h\n')
body=body.replace('(hTS j hj)', '(hTS j)').replace('(hTS i hi)', '(hTS i)')
body=body.replace('(hπ x g).mp hxc⟩', "(hmemΓ' _).mp ((hπ x g).mp hxc)⟩")
body=body.replace('      exact (hπ _ g).mp (hπout _)', "      exact (hmemΓ' _).mp ((hπ _ g).mp (hπout _))")
body=body.replace('((hπ y x).mpr hxy)', "((hπ y x).mpr ((hmemΓ' _).mpr hxy))")
f=s/'SourceIntegralTraceCuspTransversal1516a.lean';assert not f.exists()
f.write_text('''import Dubon2026.SourceGammaOnePlusMinus
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Construct a genuine signed
coset transversal containing exactly the translation representatives and
S, with every remaining term outside those two cusp classes. Reuse the
native plusMinus subgroup and finite quotient; no new curve or field is
introduced. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups
open GammaOne

'''+body+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
