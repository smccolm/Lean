from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-siegel-dependencies-1553/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.lean.txt').read_text(encoding='utf-8')
body=t[t.index('def zeta (N : ℕ)'):t.index('def Pc (N : ℕ)')]
body=body.replace('def zeta ', '/-- The actual cyclotomic phase in the source Siegel coefficients. -/\ndef zeta ',1)
body+=t[t.index('theorem N_mul_inv_one_sub '):t.index('theorem isIntegral_exp_of_pow ')]
body+=t[t.index('theorem isIntegral_N_mul_inv_one_sub '):t.index('theorem q_eq (N : ℕ)')]
body+=t[t.index('theorem zeta_ne_one '):t.index('theorem isIntegral_N_mul_inv_coef_zero ')]
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion'
f=s/'SourceSiegelLeadingUnit1589a.lean';assert not f.exists()
f.write_text('''import SourceSiegelIntegralCoefficients1585a

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> source leading Fourier unit.
The actual cyclotomic phase and its inverse are integral. A finite
geometric-sum identity expresses N/(1-zeta) as an integral polynomial in
zeta, discharging the level-cleared inverse obligation for the nonzero
leading coefficient. No integrality-of-an-inverse premise is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun. -/
namespace '''+ns+'''
noncomputable section
open Complex
open scoped Real

'''+body+'\nend\nend '+ns+'\n',encoding='utf-8')
