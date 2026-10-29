from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneHeckeGaussReflection1352a.lean.txt'
t=p.read_text(encoding='utf-8')
pos=t.index('  obtain ⟨c, hc, hcres⟩')
t=t[:pos]+'  let φ : FF →ₐ[L] GG := heckeBeta L M d\n'+t[pos:].replace('heckeBeta L M d','φ')
(s/'SourceGammaOneHeckeGaussReflection1352d.lean').write_text(t,encoding='utf-8')
p=s/'SourceGammaOneHeckeGaussReflection1352c.lean';p.rename(p.with_suffix('.lean.txt'))
p=s/'SourceGammaOneHeckeGaussNorm1354a.lean'
p.write_text(p.read_text(encoding='utf-8').replace('SourceGammaOneHeckeGaussReflection1352c','SourceGammaOneHeckeGaussReflection1352d'),encoding='utf-8')
t=(s/'build_gamma_one_gauss_norm_1354.ps1').read_text(encoding='utf-8-sig').replace('SourceGammaOneHeckeGaussReflection1352c','SourceGammaOneHeckeGaussReflection1352d')
(s/'build_gamma_one_gauss_norm_1354b.ps1').write_text(t,encoding='utf-8-sig')
