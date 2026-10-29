from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTateFrobeniusRelation1380k.lean';s=f.read_text(encoding='utf-8')
a=s.index('  obtain ⟨g, hlabel, hrel⟩ :=');b=s.index('  refine ⟨g, hlabel',a)
s=s[:a]+'''  have hsource := exists_gammaOne_picard_frobenius_relation_of_degree_genus_eq A M p
  run_tac Lean.logInfo "instantiated source"
  have h1 := hsource hcop
  run_tac Lean.logInfo "coprimality"
  have h2 := h1 hdeg
  run_tac Lean.logInfo "degree"
  have h3 := h2 hgen
  run_tac Lean.logInfo "genus"
  have h4 := h3 d hd
  run_tac Lean.logInfo "decomposition"
  obtain ⟨g, hlabel, hrel⟩ := h4
  run_tac Lean.logInfo "unpacked"
'''+s[b:]
t=p/'SourceGammaOneTateFrobeniusRelation1380m.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
s=(p/'diagnose_gamma_one_tate_relation_1380l.ps1').read_text(encoding='utf-8').replace('1380l','1380m')
t=p/'diagnose_gamma_one_tate_relation_1380m.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
