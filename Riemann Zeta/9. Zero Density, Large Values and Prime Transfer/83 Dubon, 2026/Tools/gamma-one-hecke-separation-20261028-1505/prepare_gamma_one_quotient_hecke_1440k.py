from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientHecke1440j.lean';c=f.read_text(encoding='utf-8')
c=c.replace('''  have h4 := exists_hecke_quotient (R := ZMod N) (W := T →ₗ[ℤ_[p]] V) (G := Qbar ≃ₐ[ℚ] Qbar)
    (binaryTateDiamondRelations Q p n w)
    (binaryDiamondQuotientGaloisRep Q p n w) (binaryTatePrimeOperators Q p n w ell)
    d.val ((ell.val : ZMod N) ^ (w + 1))''','''  let K := binaryTateDiamondRelations Q p n w
  let ρ := binaryDiamondQuotientGaloisRep Q p n w
  let H := binaryTatePrimeOperators Q p n w ell
  have h4 := exists_hecke_quotient K ρ H d.val ((ell.val : ZMod N) ^ (w + 1))''')
t=s/'SourceGammaOneDiamondQuotientHecke1440k.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=s/'SourceGammaOneDiamondQuotientAssembly1448a.lean';c=f.read_text(encoding='utf-8').replace('SourceGammaOneDiamondQuotientHecke1440j','SourceGammaOneDiamondQuotientHecke1440k')
t=s/'SourceGammaOneDiamondQuotientAssembly1448b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_quotient_consumers_1440d.ps1').read_text(encoding='utf-8')
runner=runner.replace('SourceGammaOneDiamondQuotientPolynomial1439d','SourceGammaOneDiamondQuotientHecke1440k').replace('SourceGammaOneDiamondQuotientHecke1440d','SourceGammaOneDiamondQuotientAssembly1448b')
t=s/'build_gamma_one_quotient_assembly_1448b.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Cache the actual quotient and Hecke objects before the existence argument.')
