from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientPolynomial1439e.lean';c=f.read_text(encoding='utf-8')
c=c.replace('  exact quotient_polynomial (R := ZMod N) (W := T →ₗ[ℤ_[p]] V)','  have h4 := quotient_polynomial (R := ZMod N) (W := T →ₗ[ℤ_[p]] V)')
c=c.replace('    d.val ((ell.val : ZMod N) ^ (w + 1)) hq\n    (binaryTateDiamondRelations_mk_diamond Q p n w g)','    d.val ((ell.val : ZMod N) ^ (w + 1))\n  have h5 := h4 hq\n  have h6 := h5 (binaryTateDiamondRelations_mk_diamond Q p n w g)\n  exact h6')
t=s/'SourceGammaOneDiamondQuotientPolynomial1439f.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=s/'SourceGammaOneDiamondQuotientHecke1440e.lean';c=f.read_text(encoding='utf-8').replace('SourceGammaOneDiamondQuotientPolynomial1439e','SourceGammaOneDiamondQuotientPolynomial1439f')
for nm in ['hecke_stable_of_quotient_polynomial','exists_hecke_quotient']:
 c=c.replace('  exact '+nm+' (binaryTateDiamondRelations','  have h4 := '+nm+' (R := ZMod N) (W := T →ₗ[ℤ_[p]] V)\n    (binaryTateDiamondRelations')
c=c.replace('    d.val ((ell.val : ZMod N) ^ (w + 1)) h3','    d.val ((ell.val : ZMod N) ^ (w + 1))\n  have h5 := h4 h3\n  exact h5')
t=s/'SourceGammaOneDiamondQuotientHecke1440f.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_quotient_consumers_1440d.ps1').read_text(encoding='utf-8').replace('1439d','1439f').replace('1440d','1440f')
t=s/'build_gamma_one_quotient_consumers_1440f.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Separated actual polynomial and Hecke applications into bounded elaboration steps.')
