from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedNormInertia1424a.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8').replace('variable (Q p n w : ℕ)','private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois\nvariable (Q p n w : ℕ)').replace('theorem binaryArithmeticTateGaloisRep_normInertia_of_degree_genus_eq','include hqp in\ntheorem binaryArithmeticTateGaloisRep_normInertia_of_degree_genus_eq')
t=p/'SourceGammaOneTwistedNormInertia1424b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_norm_inertia_1424.ps1').read_text(encoding='utf-8').replace('1424a','1424b')
t=p/'build_gamma_one_norm_inertia_1424b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
