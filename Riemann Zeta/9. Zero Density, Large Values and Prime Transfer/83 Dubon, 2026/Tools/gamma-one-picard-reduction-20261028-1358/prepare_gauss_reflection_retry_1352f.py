from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneHeckeGaussReflection1352e.lean';p.rename(p.with_suffix('.lean.txt'))
p=s/'SourceGammaOneHeckeGaussNorm1354a.lean'
p.write_text(p.read_text(encoding='utf-8').replace('SourceGammaOneHeckeGaussReflection1352e','SourceGammaOneHeckeGaussReflection1352f'),encoding='utf-8')
t=(s/'build_gamma_one_gauss_norm_1354c.ps1').read_text(encoding='utf-8-sig').replace("'SourceGammaOneHeckeGaussReflection1352e'","'SourceReductionMapReflection1355a','SourceGammaOneHeckeGaussReflection1352f'")
(s/'build_gamma_one_gauss_norm_1354d.ps1').write_text(t,encoding='utf-8-sig')
