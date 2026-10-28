from pathlib import Path
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
s=(r/'SourceGammaOneOperatorDescent.lean').read_text(encoding='utf-8')
for a,b in [
 ('import Dubon2026.SourceGammaOneHeckeWords','import SourceGammaOneHeckeDiamondWords'),
 ('sourceGammaOneHeckeWord','sourceGammaOneHeckeDiamondWord'),
 ('sourceGammaOneOriginalHeckeWord','sourceGammaOneOriginalHeckeDiamondWord'),
 ('sourceGammaOnePrimeOperators','sourceGammaOneHeckeDiamondOperators'),
 ('sourceGammaOneHeckeAlgebra','sourceGammaOneHeckeDiamondAlgebra'),
 ('sourceGammaOneToModulus','sourceGammaOneDiamondToModulus'),
 ('FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N))',
  'FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N) ⊕ CongruenceSubgroup.Gamma0 (Q * N ^ 2))')]:
 s=s.replace(a,b)
a=s.index('/-!');b=s.index('-/',a)+2
s=s[:a]+'''/-! DUB-17/18 -> original all-weight association -> finite Gamma1
arithmetic characters -> original diamond-one character. Reuse the native
surjective-transfer operator descent on the actual algebra enlarged by
original normalizer diamonds. Its proved whole-word transfer identifies
every such diamond with one in the original finite operator algebra.
This is full H1 descent; parabolic lifting remains a separate obligation. -/'''+s[b:]
s=s.replace('Gamma1 Hecke operators','Gamma1 Hecke and diamond operators')
s=s.replace('same good-prime words','same good-prime and normalizer words')
s=s.replace('genuine Gamma1 good-prime operators','genuine Gamma1 prime and diamond operators')
s=s.replace('Only primes away from level and\nmodulus are used;',
 'The prime generators are away from level and\nmodulus and all original normalizer diamonds are included;')
s=s.replace('integral word action','integral word action with diamonds acting as one')
out=p/'SourceGammaOneHeckeDiamondDescent.lean'
assert not out.exists();out.write_text(s,encoding='utf-8')
q=(p/'compile_hecke_diamond_words_1264a.ps1').read_text(encoding='utf-8')
out=p/'compile_hecke_diamond_descent_1265a.ps1';assert not out.exists()
out.write_text(q.replace('SourceGammaOneHeckeDiamondWords','SourceGammaOneHeckeDiamondDescent').replace('1264a','1265a'),encoding='utf-8')
