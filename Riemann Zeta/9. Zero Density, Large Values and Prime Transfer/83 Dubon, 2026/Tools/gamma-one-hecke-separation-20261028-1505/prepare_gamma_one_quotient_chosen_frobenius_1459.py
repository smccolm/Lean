from pathlib import Path
s=Path(__file__).parent
c=(s/'SourceGammaOneDiamondQuotientAssembly.lean').read_text(encoding='utf-8')
c=c.replace('import SourceGammaOneDiamondQuotientTransfer\n','')
a=c.index('/-!');b=c.index('namespace ',a)
c=c[:a]+'''/-! DUB-17/18 -> original all-weight association -> finite original
Hecke-character realization. Any original quotient Hecke operator with
the proved quotient square equals the geometrically constructed one by
surjectivity of the quotient map. Therefore the entire chosen family,
including the family carrying the original adic character, retains the
exact Frobenius polynomial. Degree and genus preservation remain explicit. -/
'''+c[b:]
c=c.replace('theorem exists_gammaOne_diamond_quotient_original_transfer_frobenius\n    (hlarge : 3 < p)', 'theorem gammaOne_diamond_quotient_hecke_frobenius_of_intertwining')
a=c.index('    (hp :');b=c.index('\nend\n',a)
c=c[:a]+'''    (hp : (p : kk) ≠ 0)
    (Hq : Module.End (ZMod N) ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w))
    (hH : Hq.comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell)) :
    binaryDiamondQuotientGaloisRep Q p n w d.val * Hq =
      binaryDiamondQuotientGaloisRep Q p n w d.val *
        binaryDiamondQuotientGaloisRep Q p n w d.val +
        (ell.val : ZMod N) ^ (w + 1) • 1 := by
  have hs := exists_gammaOne_diamond_quotient_hecke_frobenius_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  obtain ⟨H₀, hcomp, hpoly⟩ := h2 d hd hp
  have he : Hq = H₀ := by
    apply Submodule.linearMap_qext
    exact hH.trans hcomp.symm
  exact (congrArg (fun H => binaryDiamondQuotientGaloisRep Q p n w d.val * H) he).trans hpoly
'''+c[b:]
t=s/'SourceGammaOneDiamondQuotientChosenFrobenius1459a.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
print('Reuse native quotient-map extensionality to retain Frobenius for the chosen original Hecke family.')
