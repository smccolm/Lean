from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedGaloisFrobenius1406b.lean';s=f.read_text(encoding='utf-8')
lines=[]
for line in s.splitlines():
    if line.startswith(('  have','  obtain','  refine','  exact')):lines.append('  run_tac Lean.logInfo "'+line.strip()[:72]+'"')
    lines.append(line)
t=p/'SourceGammaOneTwistedGaloisFrobenius1406c.lean';assert not t.exists();t.write_text('\n'.join(lines)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_galois_frobenius_1406b.ps1').read_text(encoding='utf-8').replace('1406b','1406c')
t=p/'diagnose_gamma_one_galois_frobenius_1406c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
