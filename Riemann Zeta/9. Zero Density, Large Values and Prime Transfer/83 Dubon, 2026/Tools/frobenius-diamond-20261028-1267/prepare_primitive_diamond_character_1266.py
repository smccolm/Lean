from pathlib import Path
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
s=(r/'SourcePrimitiveGammaOneHeckeCharacter.lean').read_text(encoding='utf-8')
for a,b in [
 ('import Dubon2026.SourceGammaOneOperatorDescent','import SourceGammaOneHeckeDiamondDescent'),
 ('sourcePrimitiveGammaOneHeckeCharacter','sourcePrimitiveGammaOneHeckeDiamondCharacter'),
 ('sourceGammaOneOriginalHeckeWord','sourceGammaOneOriginalHeckeDiamondWord'),
 ('sourceGammaOnePrimeOperators','sourceGammaOneHeckeDiamondOperators'),
 ('sourceGammaOneHeckeAlgebra','sourceGammaOneHeckeDiamondAlgebra'),
 ('sourceGammaOneToModulus','sourceGammaOneDiamondToModulus'),
 ('FreeAlgebra.ι ℤ ell','FreeAlgebra.ι ℤ (Sum.inl ell)')]:s=s.replace(a,b)
a=s.index('/-!');b=s.index('-/',a)+2
s=s[:a]+'''/-! DUB-17/18 -> original all-weight association -> actual finite Gamma1
arithmetic character -> original diamond value one. Compose the original
finite Fourier-valued character with the proved native prime-and-diamond
operator descent. The resulting character retains every original prime
Fourier value and sends every original homogeneous normalizer diamond to
one, at every prime-power precision with p > 3. This is a character on
full H1; parabolic and arithmetic two-dimensional realization remain open. -/'''+s[b:]
s=s.replace('good-prime Hecke operator ring','good-prime Hecke and original diamond operator ring')
s=s.replace('matching restricted prime words','matching restricted prime words with every diamond acting as one')
tail='''
/-- Every actual original homogeneous normalizer diamond has value one
in the same primitive form's finite character, at every retained precision. -/
theorem sourcePrimitiveGammaOneHeckeDiamondCharacter_diamond
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (p n : ℕ) [NeZero p] (hp : p.Prime) (hlarge : 3 < p) [CharP 𝓀[E] p]
    (g : CongruenceSubgroup.Gamma0 (Q * (p ^ (n + 1)) ^ 2)) :
    sourcePrimitiveGammaOneHeckeDiamondCharacter f hk τ p n hp hlarge
      ((FreeAlgebra.lift ℤ
        (sourceGammaOneHeckeDiamondOperators Q (p ^ (n + 1)) (k - 2).toNat)).rangeRestrict
          (FreeAlgebra.ι ℤ (Sum.inr g))) = 1 := by
  have h := RingHom.congr_fun
    (sourcePrimitiveGammaOneHeckeDiamondCharacter_comp f hk τ p n hp hlarge)
      (FreeAlgebra.ι ℤ (Sum.inr g))
  change sourcePrimitiveGammaOneHeckeDiamondCharacter f hk τ p n hp hlarge _ =
    sourcePrimitiveH1AdicQuotientCharacter f hk τ n
      (sourceGammaOneOriginalHeckeDiamondWord Q (p ^ (n + 1)) (k - 2).toNat
        (FreeAlgebra.ι ℤ (Sum.inr g))) at h
  simpa only [sourceGammaOneOriginalHeckeDiamondWord, FreeAlgebra.lift_ι_apply,
    Sum.elim_inr, map_one] using h

end
end Dubon2026
'''
assert s.endswith('end\nend Dubon2026\n')
s=s[:-len('end\nend Dubon2026\n')]+tail
out=p/'SourcePrimitiveGammaOneHeckeDiamondCharacter.lean';assert not out.exists()
out.write_text(s,encoding='utf-8')
q=(p/'compile_hecke_diamond_words_1264a.ps1').read_text(encoding='utf-8')
out=p/'compile_primitive_diamond_character_1266a.ps1';assert not out.exists()
out.write_text(q.replace('SourceGammaOneHeckeDiamondWords','SourcePrimitiveGammaOneHeckeDiamondCharacter').replace('1264a','1266a'),encoding='utf-8')
