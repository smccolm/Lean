from pathlib import Path
s=Path(__file__).parent
def write(n,c):
 t=s/n;assert not t.exists();t.write_text(c,encoding='utf-8')
for name,old,new in [('SourceGammaOneArithmeticDiamond','1434a','1434b'),('SourceGammaOneGeometricDiamond','1435a','1435b'),('SourceGammaOneGaloisDiamondPolynomial','1436a','1436b')]:
 f=s/(name+old+'.lean');c=f.read_text(encoding='utf-8')
 c=c.replace('import Dubon2026.SourceGammaOneArithmeticFrobenius','import SourceGammaOneArithmeticFrobenius')
 c=c.replace('import Dubon2026.SourceGammaOneTateFrobeniusRelation','import SourceGammaOneTateFrobeniusRelation')
 c=c.replace('SourceGammaOneArithmeticDiamond1434a','SourceGammaOneArithmeticDiamond1434b')
 c=c.replace('SourceGammaOneGeometricDiamond1435a','SourceGammaOneGeometricDiamond1435b')
 write(name+new+'.lean',c)
 t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=s/'SourceGammaOneTateDiamondRelations1437a.lean';c=f.read_text(encoding='utf-8')
a=c.index('variable (Q p n w');c=c[:a]+'''private theorem relations_stable {R W I : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] (D : I → Module.End R W)
    (F : Module.End R W) (hc : ∀ i, Commute F (D i)) :
    Submodule.span R (Set.range fun z : I × W => D z.1 z.2 - z.2) ≤
      (Submodule.span R (Set.range fun z : I × W => D z.1 z.2 - z.2)).comap F := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, x⟩, rfl⟩
  change F (D i x - x) ∈ _
  rw [map_sub, LinearMap.congr_fun (hc i).eq x]
  exact Submodule.subset_span (Set.mem_range_self (i, F x))

'''+c[a:]
c=c.replace('b.map_add _ _','b.map_add (φ (arithmeticDiamondTate M p g x)) (ψ (arithmeticDiamondTate M p g x))')
c=c.replace('b.map_smul c _','b.map_smul c (φ (arithmeticDiamondTate M p g x))')
a=c.index(' := by\n  apply Submodule.span_le.mpr',c.index('theorem binaryTateDiamondRelations_galois'))
b=c.index('\ntheorem binaryTateDiamondRelations_mk_diamond',a)
c=c[:a]+''' := by
  exact relations_stable (binaryTateDiamondOperator Q p n w)
    (binaryArithmeticTateGaloisRep Q p n w σ)
    (fun g => LinearMap.ext (fun φ => binaryArithmeticTateGaloisRep_diamond Q p n w σ g φ))
'''+c[b:]
write('SourceGammaOneTateDiamondRelations1437b.lean',c)
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
old=(s/'build_gamma_one_diamond_polynomial_1433.ps1').read_text(encoding='utf-8')
a=old.index('$names=@(');b=old.index('\nforeach',a)
new=['SourceGammaOneArithmeticDiamond1434b','SourceGammaOneGeometricDiamond1435b','SourceGammaOneGaloisDiamondPolynomial1436b','SourceGammaOneTateDiamondRelations1437b']
old=old[:a]+"$names=@("+','.join(repr(x) for x in new)+')'+old[b:]
write('build_gamma_one_diamond_retry_1437.ps1',old)
print('Preserved prior attempts; qualified shared scratch imports and staged the span proof.')
