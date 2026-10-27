from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'fricke-cusp-descent-inputs-reuse-678/P2M/Sol/S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean.txt').read_text(encoding='utf-8')
t=s[s.index('theorem exists_div_E₄'):s.index('include hk hF in')]
t=t.replace('include hF in\n\n','').replace('theorem exists_div_E₄ (h :','theorem exists_div_E4 {a m : ℕ} {F : ℍ → ℂ} (hF : MDiff F) (h :').replace('theorem exists_div_E₆ (h :','theorem exists_div_E6 {b m : ℕ} {F : ℍ → ℂ} (hF : MDiff F) (h :')
t=t.replace('mdifferentiable_disc','JMultiplicity.mdiff_Δ').replace('mdifferentiable_E₄','JMultiplicity.mdiff_E₄').replace('mdifferentiable_E₆','JMultiplicity.mdiff_E₆').replace('exists_E₄_ne_zero','exists_E4_ne_zero').replace('exists_E₆_ne_zero','exists_E6_ne_zero').replace('WLight.exists_mdifferentiable_div_of_monicRel','exists_mdifferentiable_quotient_of_monic')
t=t.replace('''    · have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun _ : ℍ => (0 : ℂ))
      simp [c, hi] at h__af ⊢
      exact h__af''','''    · simpa only [c, hi, if_false] using
        (mdifferentiable_const : MDiff (fun _ : ℍ => (0 : ℂ)))''')
head='''import SourceCuspWeightFactors
import SourceHolomorphicMonicQuotient

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> exact cusp-image characterization. Power divisibility by E4 or E6
produces literal holomorphic division by the corresponding original factor.
The already proved local monic quotient theorem discharges the external
analytic dependency. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff. -/
namespace Dubon2026.SourceFunctionField.CuspWeightCriterion
noncomputable section
open UpperHalfPlane ModularForm
open scoped Manifold ModularForm
local notation "Δ" => ModularForm.discriminant

'''
f=p/'SourceCuspWeightHolomorphicDivision.lean';assert not f.exists();f.write_text(head+t+'end\nend Dubon2026.SourceFunctionField.CuspWeightCriterion\n',encoding='utf-8')
print('Prepared two actual monic-division consumers')