from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneKummerPowerLifting1344a.lean'
t=p.read_text(encoding='utf-8').replace('  classical\n  by_contra','  classical\n  haveI := valuation_residue_isAlgClosed A\n  by_contra').replace('  letI : NeZero q', '  letI : Algebra Qbar E := ((algebraMap FF E).comp (algebraMap Qbar FF)).toAlgebra\n  letI : IsScalarTower Qbar FF E := IsScalarTower.of_algebraMap_eq fun _ => rfl\n  letI : NeZero q').replace('gammaOne_kummer_degree_and_unramified M hf hdvd E','@gammaOne_kummer_degree_and_unramified M inferInstance q inferInstance (f : FF) hf hdvd E\n    inferInstance inferInstance inferInstance inferInstance inferInstance').replace('gammaOne_kummer_genus_sub_one M hf hdvd E','@gammaOne_kummer_genus_sub_one M inferInstance q inferInstance (f : FF) hf hdvd E\n    inferInstance inferInstance inferInstance inferInstance inferInstance')
(s/'SourceGammaOneKummerPowerLifting1344b.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
