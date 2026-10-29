from pathlib import Path
s=Path(__file__).parent
f=s/'SourceSiegelResidueProductStreams1588a.lean';t=f.read_text(encoding='utf-8')
t=t.replace('theorem tprod_Pc_eval (N : ℕ) (hN : 0 < N) (r : ℕ)', 'theorem tprod_Pc_eval (N : ℕ) (r : ℕ)')
t=t.replace("  haveI : NeZero N := ⟨hN.ne'⟩\n",'')
t=t.replace('simp [norm_mul, norm_pow]','simp [norm_pow]')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
n=s/'SourceSiegelResidueProductStreams1588b.lean';assert not n.exists();n.write_text(t,encoding='utf-8')
for name in ['SourceSiegelNormalizedProduct1590','SourceSiegelCoefficientSeries1591','SourceSiegelIntegralExpansion1592']:
 f=s/(name+'a.lean');t=f.read_text(encoding='utf-8')
 for a,b in [('SourceSiegelResidueProductStreams1588a','SourceSiegelResidueProductStreams1588b'),('SourceSiegelNormalizedProduct1590a','SourceSiegelNormalizedProduct1590b'),('SourceSiegelCoefficientSeries1591a','SourceSiegelCoefficientSeries1591b')]:t=t.replace(a,b)
 t=t.replace('theorem polynomial_product_eq_streams (N : ℕ) (hN : 0 < N) (r : ℕ)','theorem polynomial_product_eq_streams (N : ℕ) (r : ℕ)')
 t=t.replace('tprod_Pc_eval N hN r hr','tprod_Pc_eval N r hr').replace('polynomial_product_eq_streams N hN r hr','polynomial_product_eq_streams N r hr')
 assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
 n=s/(name+'b.lean');assert not n.exists();n.write_text(t,encoding='utf-8')
