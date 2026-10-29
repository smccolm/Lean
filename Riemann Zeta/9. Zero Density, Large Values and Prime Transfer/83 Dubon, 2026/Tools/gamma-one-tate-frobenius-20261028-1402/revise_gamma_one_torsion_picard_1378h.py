from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckeTorsionPicard1378g.lean';s=f.read_text(encoding='utf-8')
s='\n'.join(x for x in s.split('\n') if 'run_tac Lean.logInfo' not in x)
s=s.replace('  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x','  revert hx\n  refine Quotient.inductionOn x ?_\n  intro D hx')
t=p/'SourceGammaOneHeckeTorsionPicard1378h.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'diagnose_gamma_one_torsion_picard_1378g.ps1').read_text(encoding='utf-8').replace('1378g','1378h')
t=p/'build_gamma_one_torsion_picard_1378h.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
