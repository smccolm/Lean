from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceMarkedDihedralFiberBound1985a','SourceMarkedSignFiberSymmetries1986a','SourceMarkedOriginalWildFiberThree1987a','SourceMarkedOrderTwelveFiberBound1989c','SourceMarkedSignActionHom1990a','SourceMarkedCharTwoSignAction1991b','SourceMarkedOriginalWildFiberTwo1992b','SourceMarkedNormalOrderDescent1993a','SourceMarkedOriginalOrderBoundTwo1994a','SourceMarkedOriginalOrderBoundThree1995a','SourceMarkedOriginalPositiveDegree1996b','SourceMarkedFiberOrderRigidity1997b','SourceMarkedOriginalExactOrderTwo1998a','SourceMarkedOriginalExactOrderThree1999a','SourceMarkedOriginalWildContributionTwo2000a','SourceMarkedOriginalWildContributionThree2001a']
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
assert (len(modules),len(queries),len(theorems),len(constructions))==(16,23,20,3)
assert len(queries)==len(set(queries))
mc='Dubon2026.SourceFunctionField.MarkedChart.'
roots=[mc+'original_char_two_differential_contribution',mc+'original_char_three_differential_contribution']
edges=queries+[
 mc+'original_fourteen_le_different_of_j_order_twelve',mc+'original_seven_le_different_of_j_order_six',
 mc+'exists_original_residue_marked_fiber_of_char_two',mc+'exists_original_residue_marked_fiber_of_char_three',
 mc+'exists_original_normal_field_j_order_dvd_twelve',mc+'exists_original_normal_field_j_order_dvd_six',
 mc+'original_coordinate_finrank_eq_index',
 'Dubon2026.SourceFunctionField.MarkedTorsion.actual_point_signClasses_card',
 'Dubon2026.SourceCurve.sum_positive_orders_eq_finrank_separating',
 'Dubon2026.SourceCurve.Place.restrictAlongFinite_surjective',
 'Dubon2026.SourceOrderTwelve.marks',
 'Dubon2026.SourceDihedralThree.card_six_mem','Dubon2026.SourceDihedralThree.odd_iff','Dubon2026.SourceDihedralThree.small_iff',
 'Dubon2026.SourceEllipticCharTwo.charTwoSignQuotient_card',
 'Dubon2026.SourceEllipticCharTwo.charTwoSignQuotient_square_or_cube',
 'Dubon2026.SourceEllipticCharTwo.cubicPoint_quadratic',
 'Dubon2026.SourceEllipticExceptional.charThreeTranslation_conjugation']
assert len(edges)==len(set(edges))==41
cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-2002' for m in modules},separatelyAxiomChecked=[])
output('source-marked-wild-contribution-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('marked-wild-contribution-versions-2002.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$','  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedWildDifferentAudit1','SourceMarkedWildContributionAudit1'),('SourceMarkedWildDifferentDependencyAudit1','SourceMarkedWildContributionDependencyAudit1'),('SourceMarkedWildDifferentScratchOwnership1984','SourceMarkedWildContributionScratchOwnership2002')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedWildDifferent','MarkedWildContribution').replace('SOURCE MARKED WILD DIFFERENT','SOURCE MARKED WILD CONTRIBUTION')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,ns)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE MARKED WILD CONTRIBUTION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual original Gamma1 characteristic-two and characteristic-three weighted different contributions for N greater than three. Native orbit counts bound the marked fibers; normal-field divisibility and actual degree force local orders twelve and six. The audited local different bounds yield the full weighted contribution with no chart, order or differential hypothesis. Small levels and reverse genus remain open; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
reuse=['SourceOrderTwelveTransitiveMarks','SourceDihedralThreeOrbits','SourceDihedralThreeCycles','SourceEllipticCharTwoMarkedElements','SourceEllipticCharTwoCubicPoint','SourceEllipticCharThreeConjugation','SourceCurveFiniteEmbeddingRestriction','SourceCurveSeparatingCoordinateDegree','SourceCurveFiniteCoordinateResidues','SourceModularCoefficientWildGenusCriterion']
paths=[src/(n+'.lean') for n in reuse]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> homogeneous Gamma1 realization -> original genus preservation -> reverse genus -> characteristic-two/three weighted different contribution.',shorterRoute='Reuse the existing dihedral and order-twelve finite orbit theorems on actual marked point sign classes. For N greater than three the actual quartic and cubic point identities exclude fixed classes, so the complicated cyclic-subgroup weighted census reduces to orbit sizes six and twelve. Native normal-field order divisibility descends. The original degree sum forces every positive local order to attain the upper bound. The previously audited local different estimates then yield the full weighted contribution.',assumptionsToDischarge=['Actual residue charts have no finite-field, torsion-count or inertia-lift premises.','Native free actions on primitive sign classes give cardinal factors six and twelve.','Every original positive j order divides six or twelve by restriction from the constructed normal field.','The finite positive j fiber has total multiplicity equal to the signed Gamma1 index.','Cardinal and degree equality force orders six or twelve at all positive places.','The full weighted original-field different contribution follows with no local-order, normal-field or differential certificate.'],remaining='Small levels N at most three and reverse genus remain required. Continue original association and higher continuation afterwards. Acceptance16/20; DUB17--20 OPEN.',boundary='Sixteen focused modules compile. Exhaustive scratch audit, promotion and assembled verification pending. Both weighted endpoints assume precisely N greater than three and residue characteristic away from the level. No all-level genus claim is made.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-marked-wild-contribution-audit-route-2002.json',json.dumps(route,indent=2)+'\n')
replacements={'MarkedWildDifferent':'MarkedWildContribution','marked_wild_different':'marked_wild_contribution','marked-wild-different':'marked-wild-contribution','SOURCE MARKED WILD DIFFERENT':'SOURCE MARKED WILD CONTRIBUTION','1984':'2002','20261029':'20261116','2026-10-29 America/Vancouver':'2026-11-16 America/Whitehorse'}
def tr(t):
 for a,b in replacements.items():t=t.replace(a,b)
 return t
t=tr((p/'build_marked_wild_different_canonical_1984.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
output('build_marked_wild_contribution_canonical_2002.ps1',t)
output('audit_marked_wild_contribution_2002.ps1',tr((p/'audit_marked_wild_different_1984.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_marked_wild_different_1984.py').read_text(encoding='utf-8'))
t=t.replace('(8, 10, 23)','(16, 23, 41)').replace('== 8','== 16').replace('linterScopes=8','linterScopes=16').replace('all 23 required','all 41 required').replace('requiredProofValueEdges=23','requiredProofValueEdges=41').replace('modules=8, queries=10','modules=16, queries=23').replace('proofEdges=23','proofEdges=41')
output('record_marked_wild_contribution_2002.py',t)
print(json.dumps(dict(modules=16,queries=23,theorems=20,constructions=3,proofEdges=41)))
