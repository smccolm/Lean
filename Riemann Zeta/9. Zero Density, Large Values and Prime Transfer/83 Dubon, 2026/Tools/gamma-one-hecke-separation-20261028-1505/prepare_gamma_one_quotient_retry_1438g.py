from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientGalois1438f.lean';c=f.read_text(encoding='utf-8')
c=c.replace('private local instance : HasQuotient', '''private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance

private local instance : HasQuotient''')
c=c.replace('  @Submodule.hasQuotient (ZMod N) (T →ₗ[ℤ_[p]] V) inferInstance inferInstance inferInstance','''by
  have h := @Submodule.hasQuotient (ZMod N) (T →ₗ[ℤ_[p]] V)
    inferInstance inferInstance inferInstance
  exact h''')
t=s/'SourceGammaOneDiamondQuotientGalois1438g.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
print('Cached the already existing carrier structures and staged quotient-instance elaboration.')
