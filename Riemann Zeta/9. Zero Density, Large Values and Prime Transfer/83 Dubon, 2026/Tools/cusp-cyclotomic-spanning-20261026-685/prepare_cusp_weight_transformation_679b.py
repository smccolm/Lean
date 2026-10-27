from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'fricke-cusp-descent-inputs-reuse-678/P2M/Sol/S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean.txt').read_text(encoding='utf-8')
a=s[s.index('theorem Efun_smul'):s.index('theorem tendsto_E {')]
a=a.replace('theorem Efun_smul (A', 'theorem eisensteinFactor_smul (a b : ℕ) (A').replace('theorem disc_pow_smul (A','theorem discriminant_pow_smul (m : ℕ) (A').replace('Efun','eisensteinFactor').replace('E₄_smul','JMultiplicity.E₄_smul').replace('E₆_smul','JMultiplicity.E₆_smul').replace('disc_smul','JMultiplicity.Δ_smul')
b=s[s.index('theorem slash_mul_Efun'):s.index('theorem forward')].rsplit('include hk in',1)[0]
b=b.replace('theorem slash_mul_Efun {f : ℍ → ℂ}', 'theorem slash_mul_eisensteinFactor {k : ℤ} {a b m : ℕ}\n    (hk : k + 4 * a + 6 * b = 12 * m) {F f : ℍ → ℂ}').replace('Efun','eisensteinFactor').replace('disc_pow_smul','discriminant_pow_smul')
head='''import SourceCuspWeightFactors

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> exact cusp-image characterization. Reuse the existing original E4, E6
and discriminant transformation laws to prove the weight-balanced slash
identity. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff. -/
namespace Dubon2026.SourceFunctionField.CuspWeightCriterion
noncomputable section
open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm
local notation "Δ" => ModularForm.discriminant

'''
f=p/'SourceCuspWeightTransformation.lean';assert not f.exists();f.write_text(head+a+b+'end\nend Dubon2026.SourceFunctionField.CuspWeightCriterion\n',encoding='utf-8')
print('Prepared transformations using the original proved E4, E6 and discriminant laws')