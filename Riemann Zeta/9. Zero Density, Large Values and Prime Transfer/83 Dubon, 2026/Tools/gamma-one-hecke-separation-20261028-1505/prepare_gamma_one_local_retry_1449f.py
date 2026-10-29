from pathlib import Path
import json
s=Path(__file__).parent
c=(s/'SourceGammaOneDiamondQuotientLocal1449d.lean.txt').read_text(encoding='utf-8')
old='variable (ell : sourceBinaryHeckePrime (Q * N))'
assert c.count(old)==1
c=c.replace(old,'variable (ell : sourceBinaryHeckePrime (Q * p ^ (n + 1)))')
t=s/'SourceGammaOneDiamondQuotientLocal1449f.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
f=s/'GammaOneLocalDiagnostic1449e.lean';a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
record=dict(cause='The diagnostic proof print exposes synthetic recovery terms in the type of the section variable ell: p and n were hidden inside the local N notation in a variable command. This also contaminated later theorem applications. The separately stated exact local Frobenius theorem compiled without diagnostics; no imported proved theorem was found faulty.',repair='Expand p^(n+1) explicitly in the section-variable type so Lean records both parameters. Keep original theorem, proof limits, zero-diagnostic rejection and all rejected versions/evidence. A fresh compile and full dependency audit remain mandatory.',affected='Unpromoted SourceGammaOneDiamondQuotientLocal1449a/b/c/d only; audited twelve-module diamond/transfer scope has passed exhaustive checks.',productionMutation=False)
t=s/'gamma-one-local-elaboration-diagnosis-1449f.json';assert not t.exists();t.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('Expanded the hidden section-variable parameters identified by the proof-term diagnostic.')
