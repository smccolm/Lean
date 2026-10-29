from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedContinuity1420d.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
s=s.replace('''theorem binaryArithmeticTateGaloisRep_continuous :
    @Continuous _ _ _ ⊥ (binaryArithmeticTateGaloisRep Q p n w).toFun := by''','''theorem binaryArithmeticTateGaloisRep_eventually_one :
    ∀ᶠ σ in 𝓝 (1 : G), binaryArithmeticTateGaloisRep Q p n w σ = 1 := by''')
s=s.replace('  apply continuous_discrete_of_eventually_one (binaryArithmeticTateGaloisRep Q p n w)\n','')
end=s.index('\nend\nend Dubon2026.SourceFunctionField.GammaOne')
s=s[:end]+'''
theorem binaryArithmeticTateGaloisRep_continuous :
    @Continuous _ _ _ ⊥ (binaryArithmeticTateGaloisRep Q p n w).toFun :=
  continuous_discrete_of_eventually_one (binaryArithmeticTateGaloisRep Q p n w)
    (binaryArithmeticTateGaloisRep_eventually_one Q p n w)
'''+s[end:]
t=p/'SourceGammaOneTwistedContinuity1420e.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_twisted_continuity_1420d.ps1').read_text(encoding='utf-8').replace('1420d','1420e')
t=p/'build_gamma_one_twisted_continuity_1420e.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
