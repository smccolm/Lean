from pathlib import Path
s=Path(__file__).parent
a=s/'SourceIntegralTraceCoefficientExtraction1514a.lean';b=s/'SourceIntegralTraceCoefficientExtraction1514b.lean'
assert not b.exists()
b.write_text(a.read_text(encoding='utf-8').replace('Nat.cast_nonneg (R := ℝ) r','(Nat.cast_nonneg r : (0 : ℝ) ≤ r)'),encoding='utf-8')
a.rename(a.with_suffix('.lean.txt'))
t=(s/'anthropic-trace-dependencies-1510/S_ModularForm_exists_levelOne_coe_eq_sum_slash.lean.txt').read_text(encoding='utf-8')
body=t[t.index('theorem slash_neg'):t.index('\nend TraceToLevelOne')]
body=body.replace('theorem slash_neg','theorem slash_neg_even').replace('slash_neg hk','slash_neg_even hk')
body=body.replace('theorem slash_pm_mul','private theorem slash_pm_mul').replace('theorem mdifferentiable_sum','private theorem mdifferentiable_sum').replace('theorem isBoundedAtImInfty_sum','private theorem isBoundedAtImInfty_sum')
body=body.replace('PM Γ γ','γ ∈ plusMinus Γ').replace('  rcases hγ with hγ | hγ','  rcases (mem_plusMinus_iff Γ γ).mp hγ with hγ | hγ')
main=t[t.index('theorem solution'):]
main=main[:main.index('\n#print') if '\n#print' in main else len(main)]
main=main.replace('theorem solution','theorem exists_levelOne_trace').replace('(Γ : Subgroup SL(2, ℤ)) {k : ℤ}', '(Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℤ}')
start=main.index('  haveI : Γ.FiniteIndex := by');end=main.index('  have rep :',start)
main=main[:start]+main[end:]
main=main.replace('  have rep : ∀ g : SL(2, ℤ), ∃ x ∈ s, PM Γ (g * x⁻¹) := hcover', '''  have rep : ∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ plusMinus Γ := by
    intro g
    obtain ⟨x, hx, hg⟩ := hcover g
    exact ⟨x, hx, (mem_plusMinus_iff Γ _).mpr hg⟩''')
main=main.replace('PM Γ (g * x⁻¹)', 'g * x⁻¹ ∈ plusMinus Γ')
main=main.replace('hsep _ (hρs g) _ hx (by', 'hsep _ (hρs g) _ hx ((mem_plusMinus_iff Γ _).mp (by')
main=main.replace('have := (hρ g).inv.mul hgx','have := (plusMinus Γ).mul_mem ((plusMinus Γ).inv_mem (hρ g)) hgx')
main=main.replace('inv_mul_cancel_left] at this)', 'inv_mul_cancel_left] at this))')
main=main.replace('have := (hρ (x * a)).inv','have := (plusMinus Γ).inv_mem (hρ (x * a))').replace('have := (hρ (x * a⁻¹)).inv','have := (plusMinus Γ).inv_mem (hρ (x * a⁻¹))')
f=s/'SourceIntegralTraceModularForm1515a.lean';assert not f.exists()
f.write_text('''import Dubon2026.SourceGammaOnePlusMinus
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Construct the actual
level-one modular form from the prescribed signed coset transversal.
Native plusMinus and its membership theorem replace the upstream
duplicate signed subgroup. Native trace uses arbitrary quotient
representatives; the prescribed representatives here expose the
distinguished cusp term required by coefficient extraction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_exists_levelOne_coe_eq_sum_slash. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane GammaOne
variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

'''+body+'\n'+main+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
