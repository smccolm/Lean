from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneTateDiamondRelations1437b.lean'
c=f.read_text(encoding='utf-8').replace('change F (D i x - x) ∈ _','change F (D i x - x) ∈ Submodule.span R (Set.range fun z : I × W => D z.1 z.2 - z.2)')
a=c.index('theorem binaryTateDiamondRelations_galois')
c=c[:a]+'''theorem binaryTateDiamondOperator_galois_commute (σ : Qbar ≃ₐ[ℚ] Qbar) (g : Gamma0 M) :
    Commute (binaryArithmeticTateGaloisRep Q p n w σ) (binaryTateDiamondOperator Q p n w g) := by
  apply LinearMap.ext
  intro φ
  exact binaryArithmeticTateGaloisRep_diamond Q p n w σ g φ

'''+c[a:]
c=c.replace('    (fun g => LinearMap.ext (fun φ => binaryArithmeticTateGaloisRep_diamond Q p n w σ g φ))','    (binaryTateDiamondOperator_galois_commute Q p n w σ)')
t=s/'SourceGammaOneTateDiamondRelations1437c.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=s/'SourceGammaOneDiamondQuotientGalois1438a.lean'
c=f.read_text(encoding='utf-8').replace('SourceGammaOneTateDiamondRelations1437b','SourceGammaOneTateDiamondRelations1437c')
t=s/'SourceGammaOneDiamondQuotientGalois1438b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
print('Staged actual operator commutation separately and specified the span carrier.')
