from pathlib import Path
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
u=lambda n:chr(n)
G=u(0x393);Z=u(0x2124);C=u(0x2102);R=u(0x211d);N=u(0x2115);mem=u(0x2208)
s=(r/'SourceOriginalHolomorphicDifferentials.lean').read_text(encoding='utf-8')
s=s[s.index('theorem exists_original_holomorphic_differential'):]
s=s.replace('(N : '+N+') [NeZero N]', '{'+G+' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) '+Z+')} ['+G+'.FiniteIndex] (hT : ModularGroup.T '+mem+' '+G+')')
s=s.replace('(CongruenceSubgroup.Gamma0 N)', '('+G+' : Subgroup (GL (Fin 2) '+R+'))').replace('CongruenceSubgroup.Gamma0 N',G)
s=s.replace('modularFunctionFieldOver N '+C,'functionFieldOver '+G+' '+C).replace('jOver N '+C,'jCoordinateOver '+G+' '+C)
s=s.replace('exists_original_holomorphic_differential N','exists_holomorphic_differential hT').replace('exists_original_holomorphic_differential','exists_holomorphic_differential')
s=s.replace('original_regular_differential_holomorphic_realization','regular_differential_holomorphic_realization')
s=s.replace('original_regular_analytic_differential_bounded N','regular_analytic_differential_bounded hT').replace('original_field_modular_ratio N','functionFieldOver_modular_ratio hT')
s=s.replace('realize_eventuallyEq_of_ratio g h','realize_eventuallyEq_of_ratio hT g h')
s=s.replace('end Dubon2026.SourceFunctionField','end Dubon2026.SourceFunctionField.GammaOne')
header='import SourceGammaOneAnalyticDifferentialRegularity\nimport Dubon2026.SourceOriginalHolomorphicDifferentials\n\n/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> finite holomorphy.\nThe actual regular differential has a native holomorphic weight-two realization.\nThe exact quotient identity and Gamma covariance are derived, using existing\nremovable-singularity and derivative transformation theorems. Cusp vanishing\nand the complete differential/cusp converse remain separate obligations. -/\nnamespace Dubon2026.SourceFunctionField.GammaOne\nnoncomputable section\nopen UpperHalfPlane SourceCurve KaehlerDifferential Filter\nopen scoped Topology Manifold MatrixGroups ModularForm\n\n'
f=p/'SourceGammaOneHolomorphicDifferentials.lean';assert not (r/f.name).exists()
with f.open('x',encoding='utf-8',newline='\n') as o:o.write(header+s)
print(f.name)
