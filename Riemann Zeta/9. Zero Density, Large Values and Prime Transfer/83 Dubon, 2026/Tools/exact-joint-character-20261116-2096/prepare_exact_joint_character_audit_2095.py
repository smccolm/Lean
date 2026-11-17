from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceGammaOneBoundaryWordKernel2040c','SourcePrimitiveH1SquareCongruence2080a',
 'SourceOperatorRangeCharacter2086a','SourceGammaOneBoundaryQuotient2089c',
 'SourceGammaOneExactJointRing2090a','SourceGammaOneExactJointSquare2091a',
 'SourceGammaOneExactJointFinite2094c','SourceGammaOneExactJointCharacter2092a',
 'SourceGammaOneGeometricExactJointCharacter2093c']
mapping={v:re.sub(r'\d+[a-z]$','',v) for v in versions}
modules=list(mapping.values());queries=[];theorems=[];constructions=[];files=[];newmods=[]
def output(name,t):
 f=p/name;assert not f.exists(),f
 if name.endswith('.py'):ast.parse(t)
 f.write_text(t,encoding='utf-8')
for v,m in mapping.items():
 f=p/(v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,v
 assert not (src/(m+'.lean')).exists()
 t=f.read_text(encoding='utf-8');ns=re.search(r'(?m)^namespace (\S+)',t)[1]+'.'
 qs=re.findall(r'(?m)^(?:scoped |noncomputable )?(theorem|lemma|def|abbrev|instance)\s+(\S+)',t)
 queries += [ns+n for k,n in qs]
 theorems += [ns+n for k,n in qs if k in ['theorem','lemma']]
 constructions += [ns+n for k,n in qs if k not in ['theorem','lemma']]
 c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+mapping.get(x[1],x[1]),t)
 canonical=p/(m+'.lean')
 if canonical.exists():
  assert m=='SourceGammaOneBoundaryWordKernel' and canonical.read_text(encoding='utf-8')==c
 else:output(m+'.lean',c);newmods.append(m)
 assert re.sub(r'(?m)^import .*\n','',c)==re.sub(r'(?m)^import .*\n','',t)
 files.append(dict(version=v,module=m,sourcePath=str(f),originalSha256=sha(f),canonicalSha256=sha(canonical),mathematicalBodyIdentical=True))
assert (len(modules),len(queries),len(theorems),len(constructions))==(9,18,12,6)
assert len(queries)==len(set(queries)) and len(newmods)==8
ns='Dubon2026.SourceFunctionField.GammaOne.'
roots=[ns+'CoefficientReduction.exists_gammaOne_exact_joint_original_character']
separate=['Dubon2026.sourceOperatorRangeCharacterData',ns+'binaryBoundaryQuotient']
edges=[q for q in queries if q not in separate]+[
 'IsIntegral.of_pow','Dubon2026.sourcePrimitiveH1Hecke_operator_congruence_integral',
 'Dubon2026.sourceFiniteOperatorCharacterDescend','Dubon2026.sourceGammaOneConstantH1Transfer_surjective',
 'Dubon2026.sourceGammaOneConstantH1_finite','Dubon2026.sourceHeckeWord_intertwine_addHom',
 ns+'binaryParabolicH1_hecke_mem',ns+'binaryTateH1Equiv',
 ns+'binaryDiamondQuotientOriginalTransfer_word',ns+'binaryDiamondQuotient_finite',
 ns+'CoefficientReduction.exists_gammaOne_diamond_quotient_hecke_family']
assert len(edges)==len(set(edges))==27
compileEvidence={m:m+('-2043' if m=='SourceGammaOneBoundaryWordKernel' else '-2095') for m in modules}
cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence=compileEvidence,separatelyAxiomChecked=separate)
output('source-gammaone-exact-joint-character-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('gammaone-exact-joint-character-versions-2095.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$', '  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedWildDifferentAudit1','SourceGammaOneExactJointCharacterAudit1'),('SourceMarkedWildDifferentDependencyAudit1','SourceGammaOneExactJointCharacterDependencyAudit1'),('SourceMarkedWildDifferentScratchOwnership1984','SourceGammaOneExactJointCharacterScratchOwnership2095')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedWildDifferent','GammaOneExactJointCharacter').replace('SOURCE MARKED WILD DIFFERENT','SOURCE GAMMAONE EXACT JOINT CHARACTER')
 if 'Dependency' in old:
  for n,x in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,x)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE GAMMAONE EXACT JOINT CHARACTER DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual finite geometric/boundary-quotient character. Native parabolic stability, full H1 finiteness and transfer, Tate comparison, squared original congruence, power-integrality descent and original geometry are consumed. No separator, parabolic lift or discreteness is assumed. Arithmetic realization of the joint algebra, exceptional primes, association and higher continuation remain OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,x in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,x)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
paths=[src/n for n in ['SourceGammaOneParabolicOperatorAlgebra.lean','SourceGammaOneBinaryParabolicH1.lean','SourceGammaOneHeckeFinite.lean','SourceGammaOneBinaryTateH1.lean','SourceGammaOneDiamondQuotientGalois.lean','SourceGammaOneDiamondQuotientWords.lean','SourcePrimitiveH1HeckeCongruence.lean','SourcePrimitiveH1AdicOperatorKernel.lean','SourceFiniteOperatorCharacterDescent.lean','SourceGammaOneGeometricHeckeFamily.lean']]
paths += [Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib\RingTheory\IntegralClosure\IsIntegral\Basic.lean'),p/'expanded-reuse-20261116-2071/expanded-reuse-assessment-2079.md.txt',p/'expanded-reuse-20261116-2071/publication-manifest-2079.json']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> arithmetic realization of the exact joint geometric/boundary operator character.',
 shorterRoute='Existing parabolic stability and full-H1 finiteness construct the literal H1/parabolic quotient directly. Keep this boundary alongside the actual Tate diamond quotient. Their joint zero word has square zero on original H1; twice the source precision and native integrality of powers give the original character at every target precision. This removes the unit separator, global parabolic lifting and new cusp-row infrastructure from this route. The earlier 26-module promotion is deferred; only the consumed nine-module chain is prepared.',
 assumptionsToDischarge=['Construct the literal finite boundary quotient and its original Hecke operators using already proved stability and cohomology finiteness.','Derive square-zero original H1 from simultaneous zero on the two actual quotient operator spaces.','Descend original congruence integrality from the square at twice the precision, without a discrete valuation hypothesis.','Construct a finite actual joint operator image character with the entire original pullback using the proved original geometric operators; no lifting or unit separator premise.'],
 remaining='Arithmetic Galois realization of the joint algebra, primes two and three, two-dimensional characteristic-zero realization, all-weight association, local/image/regularity inputs, automorphy and literal higher symmetric-power continuation remain required. This does not assert a character on the geometric factor alone. Acceptance remains 16/20; DUB-17--20 OPEN and the full source contract is unchanged.',
 boundary='Focused compilations passed; exhaustive scratch audits, production promotion and assembled verification pending.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-gammaone-exact-joint-character-audit-route-2095.json',json.dumps(route,indent=2)+'\n')
subs={'GammaOneDiamondBoundary':'GammaOneExactJointCharacter','gammaone_diamond_boundary':'gammaone_exact_joint_character','gammaone-diamond-boundary':'gammaone-exact-joint-character','SOURCE GAMMAONE DIAMOND BOUNDARY':'SOURCE GAMMAONE EXACT JOINT CHARACTER','2075':'2095'}
pat=re.compile('|'.join(re.escape(x) for x in sorted(subs,key=len,reverse=True)))
tr=lambda t:pat.sub(lambda m:subs[m[0]],t)
t=tr((p/'build_gammaone_diamond_boundary_canonical_2075.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in newmods)+')',t)
output('build_gammaone_exact_joint_character_canonical_2095.ps1',t)
output('audit_gammaone_exact_joint_character_2095.ps1',tr((p/'audit_gammaone_diamond_boundary_2075.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_gammaone_diamond_boundary_2075.py').read_text(encoding='utf-8'))
t=t.replace('(4, 10, 19)','(9, 18, 27)').replace('== 4','== 9').replace('linterScopes=4','linterScopes=9').replace('all 19 required','all 27 required').replace('requiredProofValueEdges=19','requiredProofValueEdges=27').replace('modules=4, queries=10','modules=9, queries=18').replace('proofEdges=19','proofEdges=27')
output('record_gammaone_exact_joint_character_2095.py',t)
print(json.dumps(dict(modules=9,queries=18,theorems=12,constructions=6,proofEdges=27,oldCompileEvidenceReused=1,newCanonicalCompilations=8)))
