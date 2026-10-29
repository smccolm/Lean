from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientGalois1438d.lean';c=f.read_text(encoding='utf-8')
c=c.replace('@Continuous _ _ _ ⊥ (ρ.quotient K hK).toFun','@Continuous G (Module.End R (W ⧸ K)) _ ⊥ (ρ.quotient K hK)')
c=c.replace('apply continuous_of_tendsto_nhds_one','apply continuous_of_tendsto_nhds_one (ρ.quotient K hK)')
c=c.replace('/-- The actual Galois action', '''private local instance : HasQuotient (T →ₗ[ℤ_[p]] V)
    (Submodule (ZMod N) (T →ₗ[ℤ_[p]] V)) :=
  Submodule.hasQuotient (R := ZMod N) (M := T →ₗ[ℤ_[p]] V)

/-- The actual Galois action''')
c=c.replace('(binaryArithmeticTateGaloisRep Q p n w).quotient','Representation.quotient (k := ZMod N) (V := T →ₗ[ℤ_[p]] V)\n    (binaryArithmeticTateGaloisRep Q p n w)')
c=c.replace('continuous_quotient_discrete (binaryArithmeticTateGaloisRep','continuous_quotient_discrete (R := ZMod N) (W := T →ₗ[ℤ_[p]] V)\n    (binaryArithmeticTateGaloisRep')
t=s/'SourceGammaOneDiamondQuotientGalois1438e.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
print('Explicit quotient instance and representation API; prior elaboration failures archived.')
