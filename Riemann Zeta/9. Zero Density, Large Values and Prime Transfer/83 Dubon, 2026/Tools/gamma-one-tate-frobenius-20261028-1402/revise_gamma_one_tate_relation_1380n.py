from pathlib import Path
p=Path(__file__).parent
s=(p/'SourceGammaOneTateFrobeniusRelation1380m.lean').read_text(encoding='utf-8')
s='\n'.join(x for x in s.split('\n') if 'run_tac Lean.logInfo' not in x)
t=p/'SourceGammaOneTateFrobeniusRelation1380n.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
for v in ['k','l','m']:
    f=p/f'SourceGammaOneTateFrobeniusRelation1380{v}.lean';t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'diagnose_gamma_one_tate_relation_1380m.ps1').read_text(encoding='utf-8').replace('1380m','1380n')
t=p/'build_gamma_one_tate_relation_1380n.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
