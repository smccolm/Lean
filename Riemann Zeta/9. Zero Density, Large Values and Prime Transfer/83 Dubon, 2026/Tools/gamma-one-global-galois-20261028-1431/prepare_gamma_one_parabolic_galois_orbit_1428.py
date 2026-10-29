from pathlib import Path
p=Path(__file__).parent
s=(p/'SourceGammaOneParabolicGaloisFrobenius.lean').read_text(encoding='utf-8')
s=s.replace('import SourceGammaOneParabolicTateLift','import SourceGammaOneTwistedGaloisDiamond1427a\nimport SourceGammaOneParabolicTateLift')
s=s.replace('exists_parabolic_binaryTate_galois_frobenius_of_degree_genus_eq','exists_parabolic_binaryTate_galois_orbit_frobenius_of_degree_genus_eq')
s=s.replace('Frobenius polynomial on the actual Tate preimage of an original parabolic','Frobenius polynomial throughout the Galois orbit of the Tate preimage of an original parabolic')
s=s.replace('invariance supply the input to the genuine Galois polynomial.', 'invariance and its proved Galois stability supply the input to the genuine Galois polynomial.')
old='''      binaryArithmeticTateGaloisRep Q p n w d.val (binaryTatePrimeOperators Q p n w ell φ) =
        binaryArithmeticTateGaloisRep Q p n w d.val
          (binaryArithmeticTateGaloisRep Q p n w d.val φ) + (ell.val : ZMod N) ^ (w + 1) • φ := by'''
new='''      ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
        binaryArithmeticTateGaloisRep Q p n w d.val
            (binaryTatePrimeOperators Q p n w ell (binaryArithmeticTateGaloisRep Q p n w σ φ)) =
          binaryArithmeticTateGaloisRep Q p n w d.val
            (binaryArithmeticTateGaloisRep Q p n w d.val
              (binaryArithmeticTateGaloisRep Q p n w σ φ)) +
            (ell.val : ZMod N) ^ (w + 1) • (binaryArithmeticTateGaloisRep Q p n w σ φ) := by'''
assert old in s;s=s.replace(old,new)
s=s.replace('exact ⟨φ, hφ, hq φ (hfixed g)⟩','''refine ⟨φ, hφ, fun σ => ?_⟩
  exact hq (binaryArithmeticTateGaloisRep Q p n w σ φ)
    (binaryArithmeticTateGaloisRep_diamond_fixed Q p n w σ g φ (hfixed g))''')
t=p/'SourceGammaOneParabolicGaloisOrbit1428a.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
s=(p/'build_gamma_one_arithmetic_descent_1425c.ps1').read_text(encoding='utf-8').replace('SourceGammaOneTwistedArithmeticDescent1425c','SourceGammaOneParabolicGaloisOrbit1428a')
t=p/'build_gamma_one_parabolic_galois_orbit_1428.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
