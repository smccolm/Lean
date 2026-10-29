from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneResidueSeparability.lean'
d=p/'gamma-one-residue-separability-1279a'
assert not d.exists();d.mkdir()
(d/(f.name+'.txt')).write_bytes(f.read_bytes())
s=f.read_text(encoding='utf-8')
s=s.replace('  let J := IntermediateField.adjoin kk', '  letI : Algebra kk Fb := (residueImage A Γ).toSubalgebra.algebra\n  let J := IntermediateField.adjoin kk')
s=s.replace('  haveI : FiniteDimensional J Fb', '  letI : Algebra kk J := J.toSubalgebra.algebra\n  haveI : FiniteDimensional J Fb')
f.write_text(s,encoding='utf-8')
t=(p/'compile_gamma_one_residue_separability_1279a.ps1').read_text(encoding='utf-8').replace('1279a','1279b')
out=p/'compile_gamma_one_residue_separability_1279b.ps1';assert not out.exists()
out.write_text(t,encoding='utf-8')
