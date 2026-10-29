from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientHeckeFamily1454a.lean';c=f.read_text(encoding='utf-8')
c=c.replace('import Dubon2026.SourceArithmeticLocalEmbeddingExtension','import SourceRationalLocalClosureEmbedding1456a')
c=c.replace('The native extension of the prescribed\n+arithmetic local embedding supplies','Native algebraic-closure lifting supplies') if False else c
c=c.replace('The native extension of the prescribed\narithmetic local embedding supplies','Native algebraic-closure lifting supplies')
c=c.replace('open scoped NumberField\n','')
a=c.index('private local instance : AddCommGroup\n');b=c.index('theorem exists_gammaOne',a)
c=c[:a]+c[b:]
a=c.index('theorem exists_gammaOne');b=c.index(' :\n    ∃ Hq',a)
params=c[a:b].replace('theorem exists_gammaOne_diamond_quotient_hecke_family_of_degree_genus_eq','theorem gammaOne_diamond_relations_hecke_family_of_degree_genus_eq')
proof=''' :
    ∀ ell : sourceBinaryHeckePrime (Q * N),
      binaryTateDiamondRelations Q p n w ≤
        (binaryTateDiamondRelations Q p n w).comap (binaryTatePrimeOperators Q p n w ell) := by
  intro ell
  let e := Classical.choice (sourceRationalLocalClosure_nonempty_embedding ell.val ell.property.1)
  have hs := gammaOne_diamond_relations_hecke_at_local_of_degree_genus_eq Q p n w ell e
  have h1 := hs (hdeg ell e)
  exact h1 (hgen ell e)

'''
c=c[:a]+params+proof+c[a:]
a=c.index('  have hstable (ell');b=c.index('\nend\n',a)
c=c[:a]+'''  have hs := gammaOne_diamond_relations_hecke_family_of_degree_genus_eq Q p n w
  have h1 := hs hdeg
  have hstable := h1 hgen
  let K := binaryTateDiamondRelations Q p n w
  exact ⟨fun ell => K.mapQ K (binaryTatePrimeOperators Q p n w ell) (hstable ell), fun _ => rfl⟩
'''+c[b:]
t=s/'SourceGammaOneDiamondQuotientHeckeFamily1454b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
print('Separate original-prime stability from quotient-family construction; reuse plain algebraic-closure lifting.')
