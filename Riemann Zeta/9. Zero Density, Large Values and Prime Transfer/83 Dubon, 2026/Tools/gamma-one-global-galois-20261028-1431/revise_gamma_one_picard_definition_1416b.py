from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOnePicardFieldDefinition1416a.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
t=p/'SourceGammaOnePicardFieldDefinition1416b.lean';assert not t.exists()
t.write_text(f.read_text(encoding='utf-8').replace('(gamma1ArithmeticPicardRep Qbar N)','(arithmeticPicardRep (Gamma1 N) (by simp [Gamma1_mem, ModularGroup.T]))'),encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_picard_definition_1416.ps1').read_text(encoding='utf-8').replace('1416a','1416b')
t=p/'build_gamma_one_picard_definition_1416b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
