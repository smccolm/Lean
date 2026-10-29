from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneKummerPowerLifting1344c.lean'
t=p.read_text(encoding='utf-8').replace('  let E :=','  letI : Algebra Qbar FF := (functionFieldOver Δ Qbar).toSubalgebra.algebra\n  let E :=')
(s/'SourceGammaOneKummerPowerLifting1344d.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
