from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedGalois1401d.lean';s=f.read_text(encoding='utf-8')
s=s.replace('''    rw [binaryArithmeticTateGaloisRep_apply, hχ]
    rfl))''','''    have he := congrArg (fun a : ZMod N => a •
      homogeneousMatrixAction w (Matrix.diagonal ![a, 1])
        (φ (arithmeticTateGaloisRep M p σ⁻¹ x))) hχ
    exact (binaryArithmeticTateGaloisRep_apply Q p n w σ φ x).trans he))''')
t=p/'SourceGammaOneTwistedGalois1401e.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_twisted_galois_1401d.ps1').read_text(encoding='utf-8').replace('1401d','1401e')
t=p/'build_gamma_one_twisted_galois_1401e.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceCyclotomicHomogeneousHecke1403a')
t=p/'build_gamma_one_cyclotomic_hecke_1403a.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
