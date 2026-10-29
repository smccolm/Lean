from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedFiniteFactor1421a.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8').replace('private local instance : Algebra ℤ_[p]', '''private local instance (F : FiniteGaloisIntermediateField ℚ Qbar)
    (α : Algebra ℚ F) : @IsGalois ℚ _ F _ α := by
  have he : F.algebra' = α := Subsingleton.elim _ _
  exact Eq.mp (congrArg (fun β : Algebra ℚ F => @IsGalois ℚ _ F _ β) he) F.isGalois
private local instance : Algebra ℤ_[p]''')
t=p/'SourceGammaOneTwistedFiniteFactor1421b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_twisted_factor_1421.ps1').read_text(encoding='utf-8').replace('1421a','1421b')
t=p/'build_gamma_one_twisted_factor_1421b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
