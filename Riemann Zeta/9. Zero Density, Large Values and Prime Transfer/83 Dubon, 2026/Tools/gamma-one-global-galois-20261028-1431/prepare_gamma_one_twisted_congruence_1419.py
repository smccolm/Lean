from pathlib import Path
p=Path(__file__).parent
s=(p/'build_gamma_one_function_definition_1413.ps1').read_text(encoding='utf-8').replace('SourceGammaOneFunctionFieldDefinition1413a','SourceGammaOneTwistedCongruence1419a')
t=p/'build_gamma_one_twisted_congruence_1419.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
