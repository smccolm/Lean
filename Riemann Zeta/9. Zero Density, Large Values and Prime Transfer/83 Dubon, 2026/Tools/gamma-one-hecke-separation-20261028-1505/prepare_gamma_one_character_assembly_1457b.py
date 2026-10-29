from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientCharacterAssembly1457a.lean';c=f.read_text(encoding='utf-8')
marker='variable (Q p n : ℕ)'
helper='''private theorem assemble_character {I R W Z C : Type} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z] [Ring C]
    (q : W →ₗ[R] Z) (H : I → Module.End R W) (ψ : FreeAlgebra ℤ I →+* C)
    (hf : ∃ Hq : I → Module.End R Z, ∀ i, (Hq i).comp q = q.comp (H i))
    (hc : ∀ Hq : I → Module.End R Z, (∀ i, (Hq i).comp q = q.comp (H i)) →
      ∃ χ : (FreeAlgebra.lift ℤ Hq).range →+* C,
        χ.comp (FreeAlgebra.lift ℤ Hq).rangeRestrict.toRingHom = ψ) :
    ∃ Hq : I → Module.End R Z, (∀ i, (Hq i).comp q = q.comp (H i)) ∧
      ∃ χ : (FreeAlgebra.lift ℤ Hq).range →+* C,
        χ.comp (FreeAlgebra.lift ℤ Hq).rangeRestrict.toRingHom = ψ := by
  obtain ⟨Hq, hH⟩ := hf
  exact ⟨Hq, hH, hc Hq hH⟩

'''
assert c.count(marker)==1;c=c.replace(marker,helper+marker)
a=c.index('  have hs := exists_gammaOne_diamond_quotient_hecke_family');b=c.index('\nend\n',a)
c=c[:a]+'''  let q := (binaryTateDiamondRelations Q p n w).mkQ
  let H := binaryTatePrimeOperators Q p n w
  let ψ := (sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
    (sourceGammaOneOriginalHeckeWord Q N w).toRingHom
  have hs := exists_gammaOne_diamond_quotient_hecke_family_of_degree_genus_eq Q p n w
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := assemble_character q H ψ h2
  apply h3
  intro Hq hH
  have hc := binaryDiamondQuotient_original_character_of_transfer_away Q p n f hk hlarge τ hcop
  have h4 := hc Hq hH
  exact h4 hlift
'''+c[b:]
t=s/'SourceGammaOneDiamondQuotientCharacterAssembly1457b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
# The canonical preparation has not been run; update its selected successful candidate before use.
f=s/'prepare_gamma_one_quotient_character_canonical_1460.py';t=f.read_text(encoding='utf-8')
assert "'SourceGammaOneDiamondQuotientCharacterAssembly':'1457a'" in t
f.write_text(t.replace("'SourceGammaOneDiamondQuotientCharacterAssembly':'1457a'","'SourceGammaOneDiamondQuotientCharacterAssembly':'1457b'"),encoding='utf-8')
print('Use a narrow existential assembly with actual map parameters, retaining all geometric inputs and character values.')
