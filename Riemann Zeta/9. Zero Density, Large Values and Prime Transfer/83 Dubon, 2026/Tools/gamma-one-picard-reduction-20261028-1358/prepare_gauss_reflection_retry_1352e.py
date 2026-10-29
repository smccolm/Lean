from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneHeckeGaussReflection1352d.lean'
t=p.read_text(encoding='utf-8').replace("    have he' := congrArg (φ) he\n    rw [(φ).commutes, map_mul, map_inv₀] at he'", "    have he' : algebraMap L GG c⁻¹ = φ f * (φ (c • f))⁻¹ := by\n      simpa only [map_mul, map_inv₀, φ.commutes] using congrArg φ he")
assert t!=p.read_text(encoding='utf-8')
(s/'SourceGammaOneHeckeGaussReflection1352e.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
p=s/'SourceGammaOneHeckeGaussNorm1354a.lean'
p.write_text(p.read_text(encoding='utf-8').replace('SourceGammaOneHeckeGaussReflection1352d','SourceGammaOneHeckeGaussReflection1352e'),encoding='utf-8')
t=(s/'build_gamma_one_gauss_norm_1354b.ps1').read_text(encoding='utf-8-sig').replace('SourceGammaOneHeckeGaussReflection1352d','SourceGammaOneHeckeGaussReflection1352e')
(s/'build_gamma_one_gauss_norm_1354c.ps1').write_text(t,encoding='utf-8-sig')
