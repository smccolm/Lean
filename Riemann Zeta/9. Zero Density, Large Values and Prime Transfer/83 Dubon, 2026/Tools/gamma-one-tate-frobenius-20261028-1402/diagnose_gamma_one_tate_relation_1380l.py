from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTateFrobeniusRelation1380k.lean';s=f.read_text(encoding='utf-8')
lines=[]
for line in s.splitlines():
    if line.startswith(('  obtain','  refine','  intro','  apply','  exact')):lines.append('  run_tac Lean.logInfo "'+line.strip()[:70]+'"')
    lines.append(line)
t=p/'SourceGammaOneTateFrobeniusRelation1380l.lean';assert not t.exists();t.write_text('\n'.join(lines)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceGammaOneTateFrobeniusRelation1380l')
t=p/'diagnose_gamma_one_tate_relation_1380l.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
