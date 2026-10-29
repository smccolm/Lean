from pathlib import Path
p=Path(__file__).parent
s=(p/'fetch_lana_candidates_1432d.py').read_text(encoding='utf-8')
s=s.replace("'lana-reuse-1432d'","'lana-reuse-1432e'")
a=s.index('chosen={');b=s.index('\ntasks=[]',a)
s=s[:a]+"chosen={'lana-agents/tate-curves-theta':['TateCurvesTheta/TateCurve/DefectVanishing.lean','TateCurvesTheta/TateCurve/TatePointMem.lean','TateCurvesTheta/TateCurve/TatePointOnCurve.lean']}"+s[b:]
t=p/'fetch_lana_identity_1432e.py';assert not t.exists();t.write_text(s,encoding='utf-8')
