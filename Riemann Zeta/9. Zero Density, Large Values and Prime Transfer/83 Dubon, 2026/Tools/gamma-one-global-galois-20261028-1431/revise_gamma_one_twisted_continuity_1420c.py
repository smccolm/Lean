from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedContinuity1420b.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
start=s.index('private local instance : Algebra');end=s.index('theorem binaryArithmeticTateGaloisRep_continuous',start)
s=s[:start]+s[end:]
s=s.replace('''    @Continuous G (Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)) _ ⊥
      (binaryArithmeticTateGaloisRep Q p n w) := by''','''    @Continuous _ _ _ ⊥ (binaryArithmeticTateGaloisRep Q p n w).toFun := by''')
s=s.replace('  apply continuous_discrete_of_eventually_one\n','  apply continuous_discrete_of_eventually_one (binaryArithmeticTateGaloisRep Q p n w)\n')
t=p/'SourceGammaOneTwistedContinuity1420c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_twisted_continuity_1420b.ps1').read_text(encoding='utf-8').replace('1420b','1420c')
t=p/'build_gamma_one_twisted_continuity_1420c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
