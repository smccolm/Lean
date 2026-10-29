from pathlib import Path
p=Path(__file__).parent
f=p/'SourceCyclotomicHomogeneousAction1399a.lean';s=f.read_text(encoding='utf-8')
s=s.replace('''  rfl

end''','''  have hm : (gl2UnitDiagonalPair u (1 : Rˣ)).val = Matrix.diagonal ![(u : R), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  exact congrArg (fun a : Matrix (Fin 2) (Fin 2) R => (u : R) • homogeneousMatrixAction w a) hm

end''')
t=p/'SourceCyclotomicHomogeneousAction1399b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=p/'SourceGammaOneTwistedGalois1401a.lean';s=f.read_text(encoding='utf-8').replace('1399a','1399b')
t=p/'SourceGammaOneTwistedGalois1401b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceCyclotomicHomogeneousAction1399b','SourceAbsoluteCyclotomicCharacter1400a','SourceGammaOneTwistedGalois1401b')")
t=p/'build_gamma_one_twisted_galois_1401b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
