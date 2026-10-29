from pathlib import Path
s=Path(__file__).parent
family=(s/'SourceGammaOneDiamondQuotientHeckeFamily1454b.lean').read_text(encoding='utf-8')
header=family[:family.index('theorem gammaOne_diamond_relations_hecke_family')]
header=header[header.index('namespace '):]
header=header.replace('variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]','variable (Q p n : ℕ) [NeZero Q] [Fact p.Prime] {k : ℤ}\nlocal notation "w" => Int.toNat (k - 2)')
header=header.replace('open SourceCurve CongruenceSubgroup IntermediateField','open SourceCurve CongruenceSubgroup IntermediateField\nopen scoped ValuativeRel')
a=family.index('    (hdeg :');b=family.index(' :\n    ∀ ell',a)
geom=family[a:b]
c='''import SourceGammaOneDiamondQuotientHeckeFamily1454b
import SourceGammaOneDiamondQuotientCharacter1452c

/-! DUB-17/18 -> original all-weight association -> finite original
Hecke-character realization. Assemble the actual good-prime quotient
operators from the two separate original geometric families, then descend
the primitive form's original adic Hecke character using the original
parabolic-transfer input. No operator family, eigensystem, character or
nonzero vector is supplied. The three narrower geometric/transfer inputs,
the comparison prime range and fixed exceptional integer remain explicit. -/
'''+header+'''theorem exists_gammaOne_diamond_quotient_original_character_of_degree_genus_transfer
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hlarge : 3 < p)
    {E : Type} [Field E] [CharZero E] [ValuativeRel E] [CharP 𝓀[E] p]
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (hcop : IsCoprime (p : ℤ) (sourcePrimitiveParabolicExceptionalInteger f hk))
'''+geom+'''
    (hlift : sourceGammaOneIntegralParabolicTransfer Q N w) :
    ∃ Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N)
        ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w),
      (∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
        (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell)) ∧
      ∃ χ : (FreeAlgebra.lift ℤ Hq).range →+*
          𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1),
        χ.comp (FreeAlgebra.lift ℤ Hq).rangeRestrict.toRingHom =
          (sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
            (sourceGammaOneOriginalHeckeWord Q N w).toRingHom := by
  have hs := exists_gammaOne_diamond_quotient_hecke_family_of_degree_genus_eq Q p n w
  have h1 := hs hdeg
  obtain ⟨Hq, hH⟩ := h1 hgen
  have hc := binaryDiamondQuotient_original_character_of_transfer_away Q p n f hk hlarge τ hcop
  have h2 := hc Hq hH
  exact ⟨Hq, hH, h2 hlift⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
'''
t=s/'SourceGammaOneDiamondQuotientCharacterAssembly1457a.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
print('Assembled original quotient operators and full-word adic character from exact geometric and parabolic inputs.')
