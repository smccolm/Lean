from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceCurveSeparatingCoordinateGeometry2008a', 'SourceCurveSeparatingCoordinateCanonical2009a', 'SourceCurveSeparatingCoordinateGlobalResidues2010a', 'SourceCurveSeparatingCoordinateResidueDuality2011b', 'SourceCurveSeparatingCoordinateCanonicalDegree2012a', 'SourceCurveSeparatingCoordinateHurwitz2013c', 'SourceCurveSeparatingHurwitzBound2015a', 'SourceCurveSeparatingPoleSums2016b', 'SourceCurveSeparatingHurwitzCuspBound2017b', 'SourceOriginalResidueHurwitz2018a', 'SourceOriginalWildGenusLower2019e', 'SourceCurveSeparatingFiberSums2020b', 'SourceOriginalTameGenusCriterion2021a', 'SourceOriginalTameGenusLower2022a', 'SourceOriginalLargeLevelGenusLower2023a', 'SourceGammaOneSmallLevelIndex2024b', 'SourceGammaOneSmallLevelGenus2025a', 'SourceOriginalGammaOneGenusPreservation2026b']
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
assert (len(modules),len(queries),len(theorems),len(constructions))==(18,35,34,1)
assert len(queries)==len(set(queries))
sc='Dubon2026.SourceCurve.'
mc='Dubon2026.SourceFunctionField.MarkedChart.'
gn='Dubon2026.SourceFunctionField.GammaOne.'
roots=['Dubon2026.SourceFunctionField.IntegralDiamond.gammaOne_residue_genus_eq_away_level']
separate=[sc+'separating_hurwitz_ramification_bound']
edges=[q for q in queries if q not in separate]+[
 sc+'tateResidue_global_trace',sc+'sum_tateResidue_adjoin_generator_eq_zero',
 sc+'finite_differential_support_of_separating_coordinate',
 sc+'separating_coordinate_degree_dimension_maximum',sc+'indexOfSpecialty_eq_of_genusReached',
 sc+'degree_poleDivisor_eq_finrank_separating',
 'Dubon2026.SourceFunctionField.IntegralSlash.originalResidue_j_pole_card_le_complex',
 mc+'original_char_two_differential_contribution',mc+'original_char_three_differential_contribution',
 mc+'original_two_mul_card_j_1728_fiber_le_of_five_le',
 mc+'original_three_mul_card_j_zero_fiber_le_of_five_le',
 gn+'gamma1_arithmetic_genus_cusp_bound',
 'Dubon2026.SourceFunctionField.MarkedTorsion.natCard_residue_signClasses',
 'Dubon2026.SourceFunctionField.IntegralDiamond.gammaOne_residue_genus_le_away_level',
 'Dubon2026.SourceFunctionField.IntegralDiamond.gammaOne_degree_and_residueField_away_level']
assert len(edges)==len(set(edges))==49
cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-2027' for m in modules},separatelyAxiomChecked=separate)
output('source-original-genus-preservation-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('original-genus-preservation-versions-2027.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$','  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedWildDifferentAudit1','SourceOriginalGenusPreservationAudit1'),('SourceMarkedWildDifferentDependencyAudit1','SourceOriginalGenusPreservationDependencyAudit1'),('SourceMarkedWildDifferentScratchOwnership1984','SourceOriginalGenusPreservationScratchOwnership2027')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedWildDifferent','OriginalGenusPreservation').replace('SOURCE MARKED WILD DIFFERENT','SOURCE ORIGINAL GENUS PRESERVATION')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,ns)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE ORIGINAL GENUS PRESERVATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of literal original Gamma1 genus preservation for every nonzero level and every residue prime away from it. Native separating-coordinate local, residue, duality and Hurwitz proofs consume the actual wild and tame contributions; finite small-level index bounds remove the remaining level restriction. Original realization and higher continuation remain open; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
reuse=['SourceCurveSeparatingLocalFinite','SourceCurveFiniteCoordinateGeometry','SourceCurveFiniteCoordinateCanonical','SourceCurveFiniteCoordinateGlobalResidues','SourceCurveGlobalTateTrace','SourceCurveSeparatingGenusMaximum','SourceCurveFiniteCoordinateResidueDuality','SourceCurveFiniteCoordinateCanonicalDegree','SourceModularCoefficientLocalDifferentials','SourceModularCoefficientHurwitzDivisor','SourceModularCoefficientHurwitzBound','SourceModularCoefficientJDegreeSums','SourceModularCoefficientTameGenusCriterion','SourceOriginalResidueCuspCount','SourceGammaOneResidueGenusUpper','SourceMarkedTorsionSignedIndex']
paths=[src/(n+'.lean') for n in reuse]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> homogeneous Gamma1 realization -> original genus preservation.',shorterRoute='Native trace, rational residues, separating-coordinate degree and genus maximum already apply in every characteristic. Supplying local differential generation from the two separating charts suffices to reuse canonical duality and Hurwitz. Native original cusp bounds and wild/tame fiber contributions then give reverse genus for N greater than three. Native sign-class index comparison and four explicit residue pairs prove small-level genus vanishing, preserving every nonzero level and every prime away from it.',assumptionsToDischarge=['Explicit separation of the original j coordinate discharges local generation, finite differential support, global residue vanishing, canonical duality and degree.','The original Hurwitz bounds derive coordinate degree and residue cusp count, rather than retaining them as premises.','The actual wild contributions and tame fiber bounds give reverse genus for every residue prime when N greater than three.','The small levels one, two and three have arithmetic H1 genus zero by a finite signed-index argument and the native Manin bound.','Native degree preservation identifies the literal residue image; native specialization upper genus proves exact all-level original genus equality.'],remaining='The original genus-equality premise is discharged by the endpoint, subject to exhaustive audit and assembled verification. Apply it to the original Hecke-character and arithmetic descent consumers. Parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, all-weight association, automorphy and literal higher continuation remain required. Acceptance16/20; DUB17--20 OPEN.',boundary='Eighteen focused modules are to be audited. The unused finite-set ramification variant is separately axiom checked; it is not claimed as a VALUE dependency of the original genus endpoint. Its cusp form is consumed by the actual tame argument. No incidental generalization is pursued.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-original-genus-preservation-audit-route-2027.json',json.dumps(route,indent=2)+'\n')
replacements={'MarkedWildDifferent':'OriginalGenusPreservation','marked_wild_different':'original_genus_preservation','marked-wild-different':'original-genus-preservation','SOURCE MARKED WILD DIFFERENT':'SOURCE ORIGINAL GENUS PRESERVATION','1984':'2027','20261029':'20261116','2026-10-29 America/Vancouver':'2026-11-16 America/Whitehorse'}
def tr(t):
 for a,b in replacements.items():t=t.replace(a,b)
 return t
t=tr((p/'build_marked_wild_different_canonical_1984.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
output('build_original_genus_preservation_canonical_2027.ps1',t)
output('audit_original_genus_preservation_2027.ps1',tr((p/'audit_marked_wild_different_1984.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_marked_wild_different_1984.py').read_text(encoding='utf-8'))
t=t.replace('(8, 10, 23)','(18, 35, 49)').replace('== 8','== 18').replace('linterScopes=8','linterScopes=18').replace('all 23 required','all 49 required').replace('requiredProofValueEdges=23','requiredProofValueEdges=49').replace('modules=8, queries=10','modules=18, queries=35').replace('proofEdges=23','proofEdges=49')
output('record_original_genus_preservation_2027.py',t)
print(json.dumps(dict(modules=18,queries=35,theorems=34,constructions=1,proofEdges=49)))
