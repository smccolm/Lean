from pathlib import Path
p=Path(__file__).parent
src=p/'SourceGammaOneResidueFrobenius.lean'
old=src.read_text(encoding='utf-8')
archive=p/'gamma-one-residue-frobenius-1286b'
archive.mkdir(exist_ok=False)
(archive/(src.name+'.txt')).write_text(old,encoding='utf-8')
start=old.index('omit Γ in\ntheorem residueHeckeBeta_eq_alpha_geometricFrobenius')
replacement='''omit Γ in
theorem residueHeckeAlpha_coe (M d₀ : ℕ) (f : residueImage A (Gamma1 M)) :
    (residueHeckeAlpha A M d₀ f : LaurentSeries kk) = f.val := rfl

omit Γ in
theorem residueHeckeBeta_coe (M d₀ : ℕ) [NeZero d₀]
    (f : residueImage A (Gamma1 M)) :
    (residueHeckeBeta A M d₀ f : LaurentSeries kk) = qExpand kk d₀ f.val := rfl

omit Γ in
theorem residueHeckeBeta_eq_alpha_geometricFrobenius (M : ℕ)
    (f : residueImage A (Gamma1 M)) :
    residueHeckeBeta A M p f = residueHeckeAlpha A M p
      (geometricFrobenius A (Gamma1 M) p d hd f) := by
  apply Subtype.ext
  rw [residueHeckeBeta_coe, residueHeckeAlpha_coe, geometricFrobenius_coe]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
'''
src.write_text(old[:start]+replacement,encoding='utf-8')
run=(p/'compile_gamma_one_residue_frobenius_1286b.ps1').read_text(encoding='utf-8')
target=p/'compile_gamma_one_residue_frobenius_1286c.ps1'
assert not target.exists()
target.write_text(run.replace('1286b','1286c'),encoding='utf-8')
