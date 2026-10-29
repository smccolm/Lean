from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckeGauss.lean';d=p/'gamma-one-hecke-gauss-1281a'
assert not d.exists();d.mkdir();(d/(f.name+'.txt')).write_bytes(f.read_bytes())
s=f.read_text(encoding='utf-8')
start=s.index('/-- The original first Hecke')
end=s.index('theorem heckeAlphaGauss_resHom',start)
s=s[:start]+'''theorem heckeAlpha_mem_gaussRing (f : coefficientGaussRing Γ A) :
    heckeAlpha L M d f.val ∈ coefficientGaussRing Δ A := by
  change IsInt A (heckeAlpha L M d f.val : LaurentSeries L)
  rw [heckeAlpha_coe]
  exact f.property

/-- The original first Hecke field map restricted to integral functions. -/
def heckeAlphaGauss : coefficientGaussRing Γ A →+* coefficientGaussRing Δ A :=
  (((heckeAlpha L M d).toRingHom).comp (coefficientGaussRing Γ A).subtype).codRestrict
    (coefficientGaussRing Δ A).toSubring (heckeAlpha_mem_gaussRing A M d)

'''+s[end:]
s=s.replace('  rw [resHom_eq A Δ hy h, resHom_eq A Γ hy h]', '''  have h' : ((heckeAlphaGauss A M d f : functionFieldOver Δ L) : LaurentSeries L) *
      ι A (wit A Γ f).2 = ι A (wit A Γ f).1 := by
    change (heckeAlpha L M d f.val : LaurentSeries L) * ι A (wit A Γ f).2 = _
    rw [heckeAlpha_coe]
    exact h
  rw [resHom_eq A Δ hy h', resHom_eq A Γ hy h]''')
s=s.replace('omit M in','omit M [Algebra ℚ L] in')
start=s.index('/-- The original q-substitution Hecke')
end=s.index('theorem heckeBetaGauss_resHom',start)
s=s[:start]+'''theorem heckeBeta_mem_gaussRing (f : coefficientGaussRing Γ A) :
    heckeBeta L M d f.val ∈ coefficientGaussRing Δ A := by
  change IsInt A (heckeBeta L M d f.val : LaurentSeries L)
  rw [heckeBeta_coe]
  exact isInt_qExpand A d f.property

/-- The original q-substitution Hecke field map restricted to integral functions. -/
def heckeBetaGauss : coefficientGaussRing Γ A →+* coefficientGaussRing Δ A :=
  (((heckeBeta L M d).toRingHom).comp (coefficientGaussRing Γ A).subtype).codRestrict
    (coefficientGaussRing Δ A).toSubring (heckeBeta_mem_gaussRing A M d)

'''+s[end:]
f.write_text(s,encoding='utf-8')
out=p/'compile_gamma_one_residue_hecke_1281b.ps1';assert not out.exists()
out.write_text((p/'compile_gamma_one_residue_hecke_1281a.ps1').read_text(encoding='utf-8').replace('1281a','1281b'),encoding='utf-8')
