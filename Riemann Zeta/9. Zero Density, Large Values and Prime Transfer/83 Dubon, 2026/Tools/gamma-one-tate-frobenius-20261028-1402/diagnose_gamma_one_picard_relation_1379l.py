from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOnePicardFrobeniusRelation1379k.lean';s=f.read_text(encoding='utf-8')
lines=[]
for line in s.splitlines():
    if line.startswith(('  obtain','  refine','  intro','  have','  apply','  let ','  exact')):
        lines.append('  run_tac Lean.logInfo "'+line.strip().replace('"','')[:75]+'"')
    lines.append(line)
t=p/'SourceGammaOnePicardFrobeniusRelation1379l.lean';assert not t.exists();t.write_text('\n'.join(lines)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceGammaOnePicardFrobeniusRelation1379l')
t=p/'diagnose_gamma_one_picard_relation_1379l.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
