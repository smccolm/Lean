from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-siegel-dependencies-1553/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.lean.txt').read_text(encoding='utf-8')
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion'
head='''/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> integral Siegel expansion.
These identities connect the literal Siegel factors to the source q
parameter and residue-selected polynomial products. Native q-parameter
norm control is reused; no unrelated parameter or limiting theory is
introduced. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun. -/
'''
intro='namespace '+ns+'\nnoncomputable section\nopen Complex Filter Topology\nopen scoped Real\n\n'
ending='\nend\nend '+ns+'\n'
body=t[t.index('def qN (N : ℕ)'):t.index('theorem norm_qN_lt_one ')]
body=body.replace('def qN ', '/-- The actual source level-N exponential parameter. -/\ndef qN ',1)
body+='''theorem norm_qN_lt_one (N : ℕ) (hN : 0 < N) (τ : UpperHalfPlane) : ‖qN N τ‖ < 1 := by
  rw [qN_eq_qParam]
  exact Dubon2026.SourceFunctionField.Realized.norm_qParam_lt_one_of_pos
    (by exact_mod_cast hN) τ

'''
body+=t[t.index('theorem q_eq (N : ℕ)'):t.index('theorem E_pow ')]
def write(n,c):
 f=s/n;assert not f.exists();f.write_text(c,encoding='utf-8')
write('SourceSiegelQParameter1586a.lean','import SourceSiegelFunction\nimport Dubon2026.SourceRealizedPowerSeries\nimport Mathlib.Tactic\n\n'+head+intro+body+ending)
body=t[t.index('theorem multipliable_one_sub_mul_pow '):t.index('theorem neg_natCast_eq ')]
write('SourceSiegelResidueProductIndices1587a.lean','import SourceSiegelQParameter1586a\nimport Mathlib.Analysis.SpecialFunctions.Log.Summable\nimport Mathlib.Data.ZMod.Basic\n\n'+head+intro+body+ending)
body=t[t.index('theorem neg_natCast_eq '):t.index('theorem siegelFun_div_eq_streams ')]
body+=t[t.index('theorem tprod_Pc_eval (N : ℕ)'):t.index('\nend ArchSkel')]
write('SourceSiegelResidueProductStreams1588a.lean','import SourceSiegelResidueProductIndices1587a\n\n'+head+intro+body+ending)
