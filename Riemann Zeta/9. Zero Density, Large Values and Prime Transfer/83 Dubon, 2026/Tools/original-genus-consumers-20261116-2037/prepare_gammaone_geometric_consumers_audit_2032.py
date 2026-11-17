from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceGammaOneLocalGoodReduction2028b','SourceGammaOneGeometricHeckeFamily2029a','SourceGammaOneGeometricArithmeticDescent2030a','SourceGammaOneGeometricCharacter2031a']
mapping={v:re.sub(r'\d+[a-z]$','',v) for v in versions}
importMapping={**mapping,'SourceOriginalGammaOneGenusPreservation2026b':'SourceOriginalGammaOneGenusPreservation'}
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
 c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+importMapping.get(x[1],x[1]),t)
 assert re.sub(r'(?m)^import .*\n','',c)==re.sub(r'(?m)^import .*\n','',t)
 output(m+'.lean',c)
 files.append(dict(version=v,module=m,sourcePath=str(f),originalSha256=sha(f),canonicalSha256=sha(p/(m+'.lean')),mathematicalBodyIdentical=True))
assert (len(modules),len(queries),len(theorems),len(constructions))==(4,5,5,0)
assert len(queries)==len(set(queries))
gn='Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
roots=[gn+'binaryArithmeticTateGaloisRep_arithmetic_descent',gn+'exists_gammaOne_diamond_quotient_original_character_of_transfer']
edges=queries+[
 'Dubon2026.SourceFunctionField.IntegralDiamond.gammaOne_residue_genus_eq_away_level',
 'Dubon2026.SourceFunctionField.IntegralDiamond.gammaOne_degree_and_residueField_away_level',
 'Dubon2026.SourceFunctionField.GaussReduction.residue_charP_of_prime_mem_nonunits',
 'Dubon2026.sourceRationalLocalValuation_prime',
 gn+'gammaOne_diamond_relations_hecke_family_of_degree_genus_eq',
 gn+'binaryArithmeticTateGaloisRep_arithmetic_descent_of_degree_genus_eq',
 gn+'binaryDiamondQuotient_original_character_of_transfer_away',
 gn+'binaryArithmeticTateGaloisRep_normInertia_of_degree_genus_eq']
assert len(edges)==len(set(edges))==13

cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-2032' for m in modules},separatelyAxiomChecked=[])
output('source-gammaone-geometric-consumers-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('gammaone-geometric-consumers-versions-2032.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$','  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedWildDifferentAudit1','SourceGammaOneGeometricConsumersAudit1'),('SourceMarkedWildDifferentDependencyAudit1','SourceGammaOneGeometricConsumersDependencyAudit1'),('SourceMarkedWildDifferentScratchOwnership1984','SourceGammaOneGeometricConsumersScratchOwnership2032')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedWildDifferent','GammaOneGeometricConsumers').replace('SOURCE MARKED WILD DIFFERENT','SOURCE GAMMAONE GEOMETRIC CONSUMERS')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,ns)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE GAMMAONE GEOMETRIC CONSUMERS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of original arithmetic descent and the original quotient Hecke character conditional only on parabolic transfer. The prescribed local valuations consume proved all-level original degree and genus preservation, discharging both geometric families. Parabolic transfer and later association and higher continuation remain open; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
reuse=['SourceGammaOneDiamondQuotientHeckeFamily','SourceGammaOneTwistedArithmeticDescent','SourceGammaOneDiamondQuotientCharacterAssembly','SourceGammaOneDiamondQuotientCharacter','SourceOriginalTateInertia','SourceRationalLocalValuation']
paths=[src/(n+'.lean') for n in reuse]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> homogeneous Gamma1 realization -> actual original Hecke operators and arithmetic descent.',shorterRoute='Apply the proved original all-level geometry directly to the existing Frobenius and norm-inertia consumers at their prescribed rational local valuation. Reuse the native arithmetic descent and quotient-character assembly. No new representation, valuation or operator construction is needed.',assumptionsToDischarge=['Derive original degree and genus at every prescribed local valuation from its proved residue characteristic.','Discharge both geometric families in the original diamond quotient Hecke operator construction.','Discharge both geometric families in the original arithmetic descent of the finite homogeneous-valued Tate action.','Reduce the original quotient-character assembly to its sole remaining parabolic transfer hypothesis, preserving its prime range and exceptional integer.'],remaining='Parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, automorphy and literal higher continuation remain required. Acceptance16/20; DUB17--20 OPEN.',boundary='Four focused modules compile. Exhaustive scratch audit, promotion and assembled verification pending.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-gammaone-geometric-consumers-audit-route-2032.json',json.dumps(route,indent=2)+'\n')
replacements={'MarkedWildDifferent':'GammaOneGeometricConsumers','marked_wild_different':'gammaone_geometric_consumers','marked-wild-different':'gammaone-geometric-consumers','SOURCE MARKED WILD DIFFERENT':'SOURCE GAMMAONE GEOMETRIC CONSUMERS','1984':'2032','20261029':'20261116','2026-10-29 America/Vancouver':'2026-11-16 America/Whitehorse'}
def tr(t):
 for a,b in replacements.items():t=t.replace(a,b)
 return t
t=tr((p/'build_marked_wild_different_canonical_1984.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
output('build_gammaone_geometric_consumers_canonical_2032.ps1',t)
output('audit_gammaone_geometric_consumers_2032.ps1',tr((p/'audit_marked_wild_different_1984.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_marked_wild_different_1984.py').read_text(encoding='utf-8'))
t=t.replace('(8, 10, 23)','(4, 5, 13)').replace('== 8','== 4').replace('linterScopes=8','linterScopes=4').replace('all 23 required','all 13 required').replace('requiredProofValueEdges=23','requiredProofValueEdges=13').replace('modules=8, queries=10','modules=4, queries=5').replace('proofEdges=23','proofEdges=13')
output('record_gammaone_geometric_consumers_2032.py',t)
print(json.dumps(dict(modules=4,queries=5,theorems=5,constructions=0,proofEdges=13)))
