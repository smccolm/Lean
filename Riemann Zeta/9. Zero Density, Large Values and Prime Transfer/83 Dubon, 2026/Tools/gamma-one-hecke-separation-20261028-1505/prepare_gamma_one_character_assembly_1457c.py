from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientCharacterAssembly1457b.lean';c=f.read_text(encoding='utf-8')
marker='private theorem assemble_character'
definition='''/-- The explicit conclusion consisting of an actual quotient operator family,
its quotient square, and a character on its literal word-image algebra.
This definition is a statement; the source consumer below proves it from
the separate original geometric and parabolic-transfer hypotheses. -/
def sourceQuotientOperatorCharacterData {I R W Z C : Type} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z] [Ring C]
    (q : W →ₗ[R] Z) (H : I → Module.End R W) (ψ : FreeAlgebra ℤ I →+* C) : Prop :=
  ∃ Hq : I → Module.End R Z, (∀ i, (Hq i).comp q = q.comp (H i)) ∧
    ∃ χ : (FreeAlgebra.lift ℤ Hq).range →+* C,
      χ.comp (FreeAlgebra.lift ℤ Hq).rangeRestrict.toRingHom = ψ

'''
c=c.replace(marker,definition+marker)
start=c.index('theorem exists_gammaOne_diamond_quotient_original_character')
a=c.index('    ∃ Hq :',start);b=c.index(' := by',a)
c=c[:a]+'''    sourceQuotientOperatorCharacterData
      (binaryTateDiamondRelations Q p n w).mkQ (binaryTatePrimeOperators Q p n w)
      ((sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
        (sourceGammaOneOriginalHeckeWord Q N w).toRingHom)'''+c[b:]
t=s/'SourceGammaOneDiamondQuotientCharacterAssembly1457c.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
f=s/'prepare_gamma_one_quotient_character_canonical_1460.py';c=f.read_text(encoding='utf-8')
assert "'SourceGammaOneDiamondQuotientCharacterAssembly':'1457b'" in c
f.write_text(c.replace("'SourceGammaOneDiamondQuotientCharacterAssembly':'1457b'","'SourceGammaOneDiamondQuotientCharacterAssembly':'1457c'"),encoding='utf-8')
print('Name the exact existential conclusion without adding a hypothesis; retain the source construction proof.')
