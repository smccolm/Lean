from pathlib import Path
s=Path(__file__).parent
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel'
intro='namespace '+ns+'\nnoncomputable section\nopen Complex\nopen scoped Real MatrixGroups\n\n'
ending='\nend\nend '+ns+'\n'
header='''/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> Gamma1-invariant Siegel
product. Prove the literal level shifts of the actual Siegel factors,
reduce integer indices to residue representatives, and show that the
source 12*N exponents kill all derived root-of-unity multipliers. Then
the already constructed exponent translation invariance gives the actual
Gamma1 invariance. No arbitrary multiplier or product invariance premise
is introduced. Common analytic product facts are reused.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_siegelFun_add_level and
S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.
The upstream unused-section-variable suppression is not adopted. -/
'''
def write(n,c):
 f=s/n;assert not f.exists();f.write_text(c,encoding='utf-8')
t=(s/'anthropic-siegel-dependencies-1553/S_ModularCurve_SiegelUnit_siegelFun_add_level.lean.txt').read_text(encoding='utf-8').replace('ModularCurve.siegelFun','siegelFun')
body='theorem qq_ne_zero (τ : ℂ) : qq τ ≠ 0 := Complex.exp_ne_zero _\n\n'
body+=t[t.index('theorem qa_add_level '):t.index('\nend SiegelPerE96')]
write('SourceSiegelLevelShiftFactors1572a.lean','import SourceSiegelProductCore1565a\n\n'+header+intro+body+ending)
body=t[t.index('theorem solution '):t.rindex('\nend')]
body=body.replace('theorem solution ', 'theorem siegelFun_add_level ').replace('SiegelPerE96.','')
write('SourceSiegelLevelShifts1573a.lean','import SourceSiegelLevelShiftFactors1572a\n\n'+header+intro+body+ending)
t=(s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.lean.txt').read_text(encoding='utf-8')
body=t[t.index('variable (N : ℕ)'):t.index('\nend SiegelTransport')]
body=body.replace('ModularCurve.SiegelUnit.siegelFun_add_level','siegelFun_add_level')
body=body.replace('noncomputable def dS ', '/-- The actual multiplier for a shift of the second Siegel index by the level. -/\nnoncomputable def dS ',1).replace('noncomputable def dR ', '/-- The actual multiplier for a shift of the first Siegel index by the level. -/\nnoncomputable def dR ',1)
write('SourceSiegelResidueReduction1574a.lean','import SourceSiegelLevelShifts1573a\nimport Mathlib.NumberTheory.ModularForms.CongruenceSubgroups\n\n'+header+intro+body+ending)
body=t[t.index('theorem solution '):]
body=body.replace('theorem solution ', 'theorem prod_siegelFun_pow_specialLinearGroup_smul ').replace('ModularCurve.siegelFun_specialLinearGroup_smul','law_all')
write('SourceSiegelProductTransformation1575a.lean','import SourceSiegelResidueReduction1574a\nimport SourceSiegelSL2Transformation1571a\n\n'+header+intro+body+ending)
