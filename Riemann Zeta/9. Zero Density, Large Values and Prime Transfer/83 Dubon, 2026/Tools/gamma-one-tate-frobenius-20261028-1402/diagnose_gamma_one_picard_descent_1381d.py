from pathlib import Path
p=Path(__file__).parent
s=(p/'SourceGammaOneHeckePicardDescent1381c.lean').read_text(encoding='utf-8')
for old,label in [('  have hT :','entered proof'),('  let E :=','construct E'),('  have hdiamond :','diamond'),('  have hzero :','degree zero'),('    apply Subtype.ext','subtype'),('    change R.divMap','change divisor'),('    rw [← decomposition','inverse residue'),('    exact hdiv','exact divisor'),('  have hclass :=','quotient'),('  rw [map_add','map addition'),('  change R.pic0Map','change quotient'),('  exact hclass.trans','finish')]:
    indent=old[:len(old)-len(old.lstrip())]
    s=s.replace(old,indent+'run_tac Lean.logInfo "'+label+'"\n'+old)
t=p/'SourceGammaOneHeckePicardDescent1381d.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
s=(p/'build_gamma_one_picard_descent_1381c.ps1').read_text(encoding='utf-8').replace('1381c','1381d')
t=p/'build_gamma_one_picard_descent_1381d.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
