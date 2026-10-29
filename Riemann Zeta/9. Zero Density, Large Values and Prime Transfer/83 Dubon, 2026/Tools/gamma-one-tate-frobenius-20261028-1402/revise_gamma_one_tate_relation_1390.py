from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTateFrobeniusRelation1380j.lean';s=f.read_text(encoding='utf-8')
s='import SourceTateTorsionQuadratic1390a\n'+s
a=s.index('  apply LinearMap.ext');b=s.index('\nend\n',a)
s=s[:a]+'''  apply TateModule.tateMap_diamond_quadratic
  intro n x hx
  exact hrel (ell ^ n) (by simpa only [Nat.cast_pow] using pow_ne_zero n hell)
    x (Pic0.mem_torsion_iff.mpr hx)
'''+s[b:]
t=p/'SourceGammaOneTateFrobeniusRelation1380k.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceTateTorsionQuadratic1390a','SourceGammaOneTateFrobeniusRelation1380k')")
t=p/'build_gamma_one_tate_relation_1390.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
