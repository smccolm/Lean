from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedGaloisFrobenius1406b.lean';s=f.read_text(encoding='utf-8')
needle='open SourceCurve CongruenceSubgroup IntermediateField\n'
helper='''
private theorem transfer_quadratic {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (F G H : Module.End R W) (a : R) (x : W) (he : F = G)
    (hq : G (H x) = G (G x) + a • x) : F (H x) = F (F x) + a • x := by
  cases he
  exact hq

'''
s=s.replace(needle,needle+helper)
a=s.index('  have heq :=');b=s.index('\nend\n',a)
s=s[:a]+'''  exact transfer_quadratic (binaryArithmeticTateGaloisRep Q p n w d.val)
    (binaryTateArithmeticFrobeniusOperator Q p n w ell d.val)
    (binaryTatePrimeOperators Q p n w ell) ((ell.val : ZMod N) ^ (w + 1)) φ he (hq φ hφ)
'''+s[b:]
t=p/'SourceGammaOneTwistedGaloisFrobenius1406d.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
for v in ['b','c']:
    f=p/f'SourceGammaOneTwistedGaloisFrobenius1406{v}.lean';t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_galois_frobenius_1406b.ps1').read_text(encoding='utf-8').replace('1406b','1406d')
t=p/'build_gamma_one_galois_frobenius_1406d.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
