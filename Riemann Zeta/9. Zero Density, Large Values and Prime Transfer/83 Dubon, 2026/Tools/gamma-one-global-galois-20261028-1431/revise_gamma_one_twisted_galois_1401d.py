from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedGalois1401c.lean';s=f.read_text(encoding='utf-8')
a=s.index('theorem binaryArithmeticTateGaloisRep_frobenius_operator')
helper='''theorem binaryArithmeticTateGaloisRep_apply
    (σ : Qbar ≃ₐ[ℚ] Qbar) (φ : T →ₗ[ℤ_[p]] V) (x : T) :
    binaryArithmeticTateGaloisRep Q p n w σ φ x =
      (sourceAbsoluteCyclotomicCharacter N σ : ZMod N) •
        homogeneousMatrixAction w
          (Matrix.diagonal ![(sourceAbsoluteCyclotomicCharacter N σ : ZMod N), 1])
          (φ (arithmeticTateGaloisRep M p σ⁻¹ x)) := by
  have h := sourceCyclotomicHomogeneousAction_apply (ZMod N) w
    (sourceAbsoluteCyclotomicCharacter N σ)
  exact LinearMap.congr_fun h (φ (arithmeticTateGaloisRep M p σ⁻¹ x))

'''
s=s[:a]+helper+s[a:]
a=s.index('  apply LinearMap.ext',s.index('theorem binaryArithmeticTateGaloisRep_frobenius_operator'));b=s.index('\nend\n',a)
s=s[:a]+'''  exact LinearMap.ext (fun (φ : T →ₗ[ℤ_[p]] V) => LinearMap.ext (fun (x : T) => by
    rw [binaryArithmeticTateGaloisRep_apply, hχ]
    rfl))
'''+s[b:]
t=p/'SourceGammaOneTwistedGalois1401d.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceGammaOneTwistedGalois1401d')
t=p/'build_gamma_one_twisted_galois_1401d.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
