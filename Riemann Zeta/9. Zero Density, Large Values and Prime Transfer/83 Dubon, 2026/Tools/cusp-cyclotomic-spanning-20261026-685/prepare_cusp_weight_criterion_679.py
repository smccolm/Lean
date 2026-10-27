from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'fricke-cusp-descent-inputs-reuse-678/P2M/Sol/S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean.txt').read_text(encoding='utf-8')
fwd=s[s.index('theorem forward'):s.index('end Forward')]
bwd=s[s.index('theorem backward'):s.index('end Backward')]
main=s[s.index('theorem main'):s.index('end WeightLoweringCriterion')]
params='''{Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {a b m : ℕ}
    (hk : k + 4 * a + 6 * b = 12 * m) {F : ℍ → ℂ}'''
fwd=fwd.replace('theorem forward (f', 'theorem forward '+params+'\n    (f')
bwd=bwd.replace('theorem backward\n', 'theorem backward '+params+' (hF : MDiff F)\n')
t=fwd+bwd+main
replacements={'Efun_apply':'eisensteinFactor','Efun':'eisensteinFactor','E₄_ne_zero_or_E₆_ne_zero':'E4_ne_zero_or_E6_ne_zero','exists_div_E₄':'exists_div_E4','exists_div_E₆':'exists_div_E6','mdifferentiable_disc':'JMultiplicity.mdiff_Δ','mdifferentiable_E₄':'JMultiplicity.mdiff_E₄','mdifferentiable_E₆':'JMultiplicity.mdiff_E₆','disc_ne_zero':'discriminant_ne_zero'}
for x,y in replacements.items():t=t.replace(x,y)
old='''    have := eq_zero_of_mul_eq_zero hdiff (mdifferentiable_eisensteinFactor a b) hzero hτ₀
    funext τ
    exact sub_eq_zero.1 (by simpa using congrFun this τ)'''
new='''    have hz := ((UpperHalfPlane.mul_eq_zero_iff hdiff
      (mdifferentiable_eisensteinFactor a b)).mp (funext hzero)).resolve_right
        (fun he => hτ₀ (congrFun he τ₀))
    exact sub_eq_zero.mp hz'''
assert old in t;t=t.replace(old,new)
head='''import SourceCuspWeightHolomorphicDivision
import SourceCuspWeightTransformation

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> exact cusp-image characterization. The actual cusp-form image is
characterized by the E4/E6 power divisibilities, vanishing at every cusp,
and original subgroup invariance with the exact weight balance. Local
monic division, coprime gluing and native analytic cancellation construct
the actual cusp form. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff. -/
namespace Dubon2026.SourceFunctionField.CuspWeightCriterion
noncomputable section
open UpperHalfPlane ModularForm Filter
open scoped Topology Manifold MatrixGroups ModularForm
local notation "Δ" => ModularForm.discriminant

'''
f=p/'SourceCuspWeightCriterion.lean';assert not f.exists();f.write_text(head+t+'end\nend Dubon2026.SourceFunctionField.CuspWeightCriterion\n',encoding='utf-8')
print('Prepared exact cusp-image criterion with local monic division and native cancellation')