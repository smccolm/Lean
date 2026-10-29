from pathlib import Path
s=Path(__file__).parent
c=(s/'SourceGammaOneDiamondQuotientLocal1449c.lean.txt').read_text(encoding='utf-8')
c=c.replace('import Dubon2026.RationalPrimeFiniteTameGenerator','import SourceRationalLocalFrobenius1450a')
a=c.index('  obtain ⟨φ, hφ⟩');b=c.index('  have hs := gammaOne_diamond_relations_hecke',a)
c=c[:a]+'''  obtain ⟨d, hd⟩ := sourceRationalLocalValuation_exists_frobenius ell.val ell.property.1 e
'''+c[b:]
c=c.replace('exact h2 d hres hp','exact h2 d hd hp')
t=s/'SourceGammaOneDiamondQuotientLocal1449d.lean';assert not t.exists()
t.write_text(c,encoding='utf-8')
print('Consume the separately compiled exact local Frobenius existence theorem.')
