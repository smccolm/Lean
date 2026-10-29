from pathlib import Path
p=Path(__file__).parent
s=(p/'build_gamma_one_function_definition_1413.ps1').read_text(encoding='utf-8').replace('SourceGammaOneFunctionFieldDefinition1413a','SourceGammaOneFinitePlaceOrbit1414a')
t=p/'build_gamma_one_place_orbit_1414.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
