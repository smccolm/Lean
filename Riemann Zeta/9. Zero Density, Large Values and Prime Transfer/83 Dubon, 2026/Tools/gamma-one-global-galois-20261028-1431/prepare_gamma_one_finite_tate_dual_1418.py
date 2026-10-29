from pathlib import Path
p=Path(__file__).parent
s=(p/'build_gamma_one_function_definition_1413.ps1').read_text(encoding='utf-8').replace('SourceGammaOneFunctionFieldDefinition1413a','SourceGammaOneFiniteTateDual1418a')
t=p/'build_gamma_one_finite_tate_dual_1418.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
