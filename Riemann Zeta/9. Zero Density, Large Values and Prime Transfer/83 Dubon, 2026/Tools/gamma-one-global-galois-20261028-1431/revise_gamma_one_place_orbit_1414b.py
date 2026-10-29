from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneFinitePlaceOrbit1414a.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
t=p/'SourceGammaOneFinitePlaceOrbit1414b.lean';assert not t.exists()
t.write_text(f.read_text(encoding='utf-8').replace(':= gammaOne_translation_mem N',':= by simp [Γ, Gamma1_mem, ModularGroup.T]'),encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_place_orbit_1414.ps1').read_text(encoding='utf-8').replace('1414a','1414b')
t=p/'build_gamma_one_place_orbit_1414b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
f=p/'SourceGammaOnePlaceFieldDefinition1415a.lean';assert not f.with_suffix('.log').exists()
f.write_text(f.read_text(encoding='utf-8').replace('SourceGammaOneFinitePlaceOrbit1414a','SourceGammaOneFinitePlaceOrbit1414b'),encoding='utf-8')
