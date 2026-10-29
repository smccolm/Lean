from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneHeckeGaussReflection1352b.lean'
t=p.read_text(encoding='utf-8').replace("    rw [hcomm, map_mul, map_inv₀] at he'", "    have hmul : heckeBeta L M d (f * (c • f)⁻¹) =\n        heckeBeta L M d f * heckeBeta L M d (c • f)⁻¹ := map_mul (heckeBeta L M d) _ _\n    have hinv : heckeBeta L M d (c • f)⁻¹ = (heckeBeta L M d (c • f))⁻¹ :=\n      map_inv₀ (heckeBeta L M d) _\n    rw [hcomm, hmul, hinv] at he'")
(s/'SourceGammaOneHeckeGaussReflection1352c.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
p=s/'SourceGammaOneHeckeGaussNorm1354a.lean'
p.write_text(p.read_text(encoding='utf-8').replace('SourceGammaOneHeckeGaussReflection1352b','SourceGammaOneHeckeGaussReflection1352c'),encoding='utf-8')
t=(s/'build_gamma_one_kummer_consumers_1347.ps1').read_text(encoding='utf-8-sig')
a=t.index('foreach($n in @(');b=t.index(')){',a)+3
t=t[:a]+"foreach($n in @('SourceGammaOneHeckeGaussReflection1352c','SourceGammaOneHeckeGaussNorm1354a')){"+t[b:]
(s/'build_gamma_one_gauss_norm_1354.ps1').write_text(t,encoding='utf-8-sig')
