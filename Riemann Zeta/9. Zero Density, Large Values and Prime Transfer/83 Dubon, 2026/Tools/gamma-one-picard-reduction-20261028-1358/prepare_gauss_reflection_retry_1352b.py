from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneHeckeGaussReflection1352a.lean'
t=p.read_text(encoding='utf-8').replace("    rw [(heckeBeta L M d).commutes, map_mul, map_inv₀] at he'", "    have hcomm : heckeBeta L M d (algebraMap L FF c⁻¹) = algebraMap L GG c⁻¹ :=\n      (heckeBeta L M d).commutes c⁻¹\n    rw [hcomm, map_mul, map_inv₀] at he'")
(s/'SourceGammaOneHeckeGaussReflection1352b.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
