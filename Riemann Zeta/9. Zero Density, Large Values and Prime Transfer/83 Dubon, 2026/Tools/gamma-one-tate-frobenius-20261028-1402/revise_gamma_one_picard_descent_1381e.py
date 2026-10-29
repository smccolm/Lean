from pathlib import Path
p=Path(__file__).parent
s=(p/'SourceGammaOneHeckePicardDescent1381c.lean').read_text(encoding='utf-8')
a=s.index('  have hclass :=');b=s.index('  change R.pic0Map',a)
s=s[:a]+'''  let q : Divisor.degZero (K := kk) (F := Fb) →+ Pic0 kk Fb := Pic0.mk
  let Y := decompositionResidueDegZero A Γ hT d (R.degZeroMap E)
  let Z := decompositionResidueDegZero A Γ hT d⁻¹ (R.degZeroMap D)
  have hmap : q (Y + p • Z) = q Y + p • q Z :=
    (q.map_add Y (p • Z)).trans (congrArg (fun z => q Y + z) (q.map_nsmul Z p))
  have hclass := (congrArg q hzero).trans hmap
'''+s[b:]
t=p/'SourceGammaOneHeckePicardDescent1381e.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
for v in ['b','c','d']:
    f=p/f'SourceGammaOneHeckePicardDescent1381{v}.lean'
    if f.exists():
        target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'build_gamma_one_picard_descent_1381c.ps1').read_text(encoding='utf-8').replace('1381c','1381e')
t=p/'build_gamma_one_picard_descent_1381e.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
