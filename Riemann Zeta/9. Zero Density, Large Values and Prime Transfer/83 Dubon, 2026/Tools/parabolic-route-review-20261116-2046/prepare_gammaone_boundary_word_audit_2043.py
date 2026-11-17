from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceGammaOneBoundaryWordKernel2040c','SourceGammaOneBoundaryWordCharacter2041b','SourceGammaOneGeometricBoundaryCharacter2042a']
mapping={v:re.sub(r'\d+[a-z]$','',v) for v in versions}
modules=list(mapping.values());queries=[];theorems=[];constructions=[];files=[]
def output(name,text):
 f=p/name;assert not f.exists(),f
 if name.endswith('.py'):ast.parse(text)
 f.write_text(text,encoding='utf-8')
for v,m in mapping.items():
 f=p/(v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert not (src/(m+'.lean')).exists()
 t=f.read_text(encoding='utf-8');ns=re.search(r'(?m)^namespace (\S+)',t)[1]+'.'
 qs=re.findall(r'(?m)^(?:scoped |noncomputable )?(theorem|lemma|def|abbrev|instance)\s+(\S+)',t)
 queries += [ns+n for k,n in qs]
 theorems += [ns+n for k,n in qs if k in ['theorem','lemma']]
 constructions += [ns+n for k,n in qs if k not in ['theorem','lemma']]
 c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+mapping.get(x[1],x[1]),t)
 assert re.sub(r'(?m)^import .*\n','',c)==re.sub(r'(?m)^import .*\n','',t)
 output(m+'.lean',c)
 files.append(dict(version=v,module=m,sourcePath=str(f),originalSha256=sha(f),canonicalSha256=sha(p/(m+'.lean')),mathematicalBodyIdentical=True))
assert (len(modules),len(queries),len(theorems),len(constructions))==(3,3,3,0)
assert len(queries)==len(set(queries))
roots=['Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_diamond_quotient_original_character_of_boundary_word']
edges=queries+[
 'Dubon2026.sourceGammaOneConstantH1Transfer_surjective',
 'Dubon2026.sourcePrimePower_six_isUnit',
 'Dubon2026.SourceFunctionField.GammaOne.binaryTateH1Equiv',
 'Dubon2026.SourceFunctionField.GammaOne.binaryDiamondQuotientOriginalTransfer_word',
 'Dubon2026.sourceGammaOneHeckeWord_transfer',
 'Dubon2026.sourceGammaOneOriginalHeckeWord_change',
 'Dubon2026.sourcePrimitiveH1AdicQuotientCharacter_zero_of_operator',
 'Dubon2026.sourceFiniteOperatorCharacterDescend',
 'Dubon2026.sourceFiniteOperatorCharacterDescend_comp',
 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_diamond_quotient_hecke_family',
 'Dubon2026.SourceFunctionField.IntegralDiamond.gammaOne_residue_genus_eq_away_level']
assert len(edges)==len(set(edges))==14

cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-2043' for m in modules},separatelyAxiomChecked=[])
output('source-gammaone-boundary-word-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('gammaone-boundary-word-versions-2043.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$','  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedWildDifferentAudit1','SourceGammaOneBoundaryWordAudit1'),('SourceMarkedWildDifferentDependencyAudit1','SourceGammaOneBoundaryWordDependencyAudit1'),('SourceMarkedWildDifferentScratchOwnership1984','SourceGammaOneBoundaryWordScratchOwnership2043')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedWildDifferent','GammaOneBoundaryWord').replace('SOURCE MARKED WILD DIFFERENT','SOURCE GAMMAONE BOUNDARY WORD')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,ns)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE GAMMAONE BOUNDARY WORD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual quotient-character deduction. Native full-H1 surjectivity, actual Tate/parabolic comparison, word intertwining, full-H1 congruence, unit cancellation and original proved good-reduction geometry are consumed. The boundary-annihilating word and its unit value remain unconstructed; association and higher continuation remain open; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
prior=json.loads((p/'gammaone-boundary-word-route-2040.json').read_text(encoding='utf-8'))
paths=[Path(x['path']) for x in prior['reuseChecked']]+[p/'SourceGammaOneGeometricHeckeFamily.lean']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=prior['chain'],shorterRoute=prior['assessment'],
 assumptionsToDischarge=['A zero actual quotient word, multiplied by a concrete boundary-annihilating Hecke word, kills every original integral H1 class after reduction; derive this using actual full-H1 transfer and Tate/parabolic comparison.','Native full-H1 congruence and a unit value of the boundary word imply exact character descent to the actual quotient algebra.','Existing proved original geometry constructs the full quotient Hecke family.'],
 remaining='The concrete boundary-annihilating word and unit original character value remain unconstructed. This conditional alternative neither proves global parabolic surjectivity nor closes the original all-weight association, automorphy or higher continuation. The entire original source contract remains in force; DUB17--20 OPEN.',
 boundary='Three focused modules compile. Exhaustive scratch audit, production promotion and assembled verification pending.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-gammaone-boundary-word-audit-route-2043.json',json.dumps(route,indent=2)+'\n')
replacements={'MarkedWildDifferent':'GammaOneBoundaryWord','marked_wild_different':'gammaone_boundary_word','marked-wild-different':'gammaone-boundary-word','SOURCE MARKED WILD DIFFERENT':'SOURCE GAMMAONE BOUNDARY WORD','1984':'2043','20261029':'20261116','2026-10-29 America/Vancouver':'2026-11-16 America/Whitehorse'}
def tr(t):
 for a,b in replacements.items():t=t.replace(a,b)
 return t
t=tr((p/'build_marked_wild_different_canonical_1984.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
output('build_gammaone_boundary_word_canonical_2043.ps1',t)
output('audit_gammaone_boundary_word_2043.ps1',tr((p/'audit_marked_wild_different_1984.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_marked_wild_different_1984.py').read_text(encoding='utf-8'))
t=t.replace('(8, 10, 23)','(3, 3, 14)').replace('== 8','== 3').replace('linterScopes=8','linterScopes=3').replace('all 23 required','all 14 required').replace('requiredProofValueEdges=23','requiredProofValueEdges=14').replace('modules=8, queries=10','modules=3, queries=3').replace('proofEdges=23','proofEdges=14')
output('record_gammaone_boundary_word_2043.py',t)
print(json.dumps(dict(modules=3,queries=3,theorems=3,constructions=0,proofEdges=14)))
