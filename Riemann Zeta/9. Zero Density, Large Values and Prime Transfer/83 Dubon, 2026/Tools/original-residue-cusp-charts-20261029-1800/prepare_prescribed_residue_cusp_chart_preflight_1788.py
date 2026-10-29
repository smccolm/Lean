from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
p=Path(__file__).parent
versions={'SourcePrescribedPrimitiveRootReduction':'1785a','SourceOriginalResiduePrescribedCuspChart':'1786a'}
ns='Dubon2026.SourceFunctionField.IntegralSlash.'
mods=[n+v for n,v in versions.items()]
ths=[ns+'exists_algebraicIntegerReduction_primitiveRoot',ns+'exists_originalResiduePrescribedCuspFieldHom']
edges=ths+['Dubon2026.sourceIntegralReduction_exists_extension','minpoly.equivAdjoin',
 'AdjoinRoot.lift','Polynomial.cyclotomic_eq_minpoly','Complex.isPrimitiveRoot_exp',
 'Dubon2026.SourceFunctionField.valuation_residue_isAlgClosed',
 ns+'exists_originalResidueSlashFieldHom',ns+'normalizedSlashValue_jqModC']
old=json.loads((p/'original-residue-slash-embedding-preflight-config-1783.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,
 roots=[ths[1]],proofEdges=edges,localModules=mods+old['localModules'],
 separatelyAxiomChecked=[],compileEvidence={m:m for m in mods})
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
arr=lambda a:'#['+', '.join('`'+n for n in a)+']'
write('prescribed-residue-cusp-chart-versions-1788.json',json.dumps(versions,indent=2)+'\n')
write('prescribed-residue-cusp-chart-preflight-config-1788.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
s=(p/'SourceOriginalResidueSlashEmbeddingPreflight1783.lean').read_text()
s=imports+'\n'.join('#print axioms '+n for n in ths)+'\n\n'+s[s.index('private def'):]
s=s[:s.index('\n#lint in')]+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
for name in ['modules','theorems','constructions']:
 s=re.sub(r'let '+name+r' : Array Name := #\[[^\n]*\]','let '+name+' : Array Name := '+arr(cfg[name]),s)
s=s.replace('ORIGINAL RESIDUE SLASH EMBEDDING PREFLIGHT','PRESCRIBED RESIDUE CUSP CHART PREFLIGHT')
write('SourcePrescribedResidueCuspChartPreflight1788.lean',s)
s=(p/'SourceOriginalResidueSlashEmbeddingValuePreflight1783.lean').read_text()
s=imports+s[s.index('private def'):]
for name in ['roots','localModules']:
 s=re.sub(r'let '+name+r' : Array Name := #\[[^\n]*\]','let '+name+' : Array Name := '+arr(cfg[name]),s)
s=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(edges),s)
a=s.index('  logInfo m!');b=s.index('\n\n#eval',a)
s=s[:a]+'  logInfo m!"SOURCE PRESCRIBED RESIDUE CUSP CHART PREFLIGHT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the value closure of the actual prescribed residue cusp chart. Native integral-reduction extension, cyclotomic evaluation, residue algebraic closedness and the actual original function-field embedding discharge the coefficient reduction and field-chart existence inputs. Stabilizer equivariance, residue fiber bounds and reverse genus remain open; DUB17--20 OPEN."'+s[b:]
write('SourcePrescribedResidueCuspChartValuePreflight1788.lean',s)
s=(p/'audit_original_residue_slash_embedding_preflight_1783.ps1').read_text()
s=s.replace('SourceOriginalResidueSlashEmbeddingPreflight1783','SourcePrescribedResidueCuspChartPreflight1788').replace('SourceOriginalResidueSlashEmbeddingValuePreflight1783','SourcePrescribedResidueCuspChartValuePreflight1788').replace('original residue slash embedding','prescribed residue cusp chart')
write('audit_prescribed_residue_cusp_chart_preflight_1788.ps1',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
refs=['anthropic-prescribed-root-reduction-1784/manifest.json','original-residue-slash-embedding-route-1783.json']
write('prescribed-residue-cusp-chart-route-1788.json',json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17/18 -> literal higher continuation -> automorphy -> original all-weight association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus inequality -> cusp residue fiber bounds -> actual prescribed-root cusp field chart.',reuseReviewed=[dict(path=str(p/n),sha256=sha(p/n)) for n in refs],shorterRoute='The native sourceIntegralReduction_exists_extension theorem replaces the external second lying-over, quotient-domain and algebraic-closure construction. Native cyclotomic/minimal-polynomial evaluation prescribes the root. Native algebraic closedness of the actual valuation residue field and the already constructed original cusp embedding give the actual prescribed chart and its j(q^N) image.',remaining='Diamond-stabilizer equivariance, full-base slot identification, residue fiber bounds and reverse genus remain open. Acceptance remains 16/20; DUB17--20 OPEN. Frozen paper, proof standards and full completion criteria unchanged.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False),indent=2)+'\n')
print(json.dumps(dict(modules=2,queries=2,valueEdges=len(edges))))
