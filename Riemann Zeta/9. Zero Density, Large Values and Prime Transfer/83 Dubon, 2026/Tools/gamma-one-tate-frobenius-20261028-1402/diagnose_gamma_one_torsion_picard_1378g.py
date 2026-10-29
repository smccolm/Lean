from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckeTorsionPicard1378f.lean';s=f.read_text(encoding='utf-8')
for old,label in [('  obtain ⟨g,','obtain norm'),('  refine ⟨g,','introduce data'),('  obtain ⟨D,','represent quotient'),('  exact hecke_','apply descent')]:s=s.replace(old,'  run_tac Lean.logInfo "'+label+'"\n'+old)
t=p/'SourceGammaOneHeckeTorsionPicard1378g.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceGammaOneHeckeTorsionPicard1378g')
t=p/'diagnose_gamma_one_torsion_picard_1378g.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
