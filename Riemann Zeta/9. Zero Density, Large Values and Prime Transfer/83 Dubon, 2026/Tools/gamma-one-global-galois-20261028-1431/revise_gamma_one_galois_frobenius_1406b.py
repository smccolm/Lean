from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedGaloisFrobenius1406a.lean';s=f.read_text(encoding='utf-8')
s=s.replace('''  rw [he]
  exact hq φ hφ''','''  have heq := congrArg (fun op : Module.End (ZMod N) (T →ₗ[ℤ_[p]] V) =>
    op (binaryTatePrimeOperators Q p n w ell φ) = op (op φ) + (ell.val : ZMod N) ^ (w + 1) • φ) he
  exact heq.mpr (hq φ hφ)''')
t=p/'SourceGammaOneTwistedGaloisFrobenius1406b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
for name,script in [('SourceGammaOneTwistedGaloisFrobenius1406b','build_gamma_one_galois_frobenius_1406b.ps1'),('SourceTwistedCoefficientDualTrivial1407a','build_gamma_one_twisted_trivial_1407.ps1')]:
    s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f',name)
    t=p/script;assert not t.exists();t.write_text(s,encoding='utf-8')
