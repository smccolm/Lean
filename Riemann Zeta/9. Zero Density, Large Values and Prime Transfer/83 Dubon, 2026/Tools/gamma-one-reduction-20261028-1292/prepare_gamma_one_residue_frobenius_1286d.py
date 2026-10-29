from pathlib import Path
p=Path(__file__).parent
src=p/'SourceGammaOneResidueFrobenius.lean'
old=src.read_text(encoding='utf-8')
archive=p/'gamma-one-residue-frobenius-1286c'
archive.mkdir(exist_ok=False)
(archive/(src.name+'.txt')).write_text(old,encoding='utf-8')
a='(residueHeckeAlpha A M d₀ f : LaurentSeries kk) = f.val := rfl'
b='''(residueHeckeAlpha A M d₀ f : LaurentSeries kk) = f.val :=
  IntermediateField.coe_inclusion (residueImage_heckeAlpha_le A M d₀) f'''
assert old.count(a)==1
src.write_text(old.replace(a,b),encoding='utf-8')
run=(p/'compile_gamma_one_residue_frobenius_1286c.ps1').read_text(encoding='utf-8')
target=p/'compile_gamma_one_residue_frobenius_1286d.ps1'
assert not target.exists()
target.write_text(run.replace('1286c','1286d'),encoding='utf-8')
