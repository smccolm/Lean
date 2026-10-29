from pathlib import Path
p=Path(__file__).parent;f=p/'SourceGammaOneResidueFrobenius.lean'
d=p/'gamma-one-residue-frobenius-1286a';assert not d.exists();d.mkdir()
(d/(f.name+'.txt')).write_bytes(f.read_bytes())
s=f.read_text(encoding='utf-8').replace('[CharP kk p]', '[CharP (IsLocalRing.ResidueField A) p]')
s=s.replace('(hd : ∀ a : kk, d • a = a ^ p)', '(hd : ∀ a : IsLocalRing.ResidueField A, d • a = a ^ p)')
f.write_text(s,encoding='utf-8')
out=p/'compile_gamma_one_residue_frobenius_1286b.ps1';assert not out.exists()
out.write_text((p/'compile_gamma_one_residue_frobenius_1286a.ps1').read_text(encoding='utf-8').replace('1286a','1286b'),encoding='utf-8')
