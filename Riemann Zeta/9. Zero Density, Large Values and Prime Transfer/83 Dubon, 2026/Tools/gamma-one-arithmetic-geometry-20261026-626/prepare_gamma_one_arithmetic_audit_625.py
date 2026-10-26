from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceGammaOneFieldCoefficients', 'SourceGammaOneHeckeFieldNaturality', 'SourceGammaOneArithmeticField', 'SourceGammaOneArithmeticPlaces', 'SourceGammaOneArithmeticDivisors', 'SourceGammaOneArithmeticPicard', 'SourceGammaOneHeckeArithmeticPlaces', 'SourceGammaOneHeckeArithmeticDivisors', 'SourceGammaOneHeckeArithmetic']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^(?:@\[[^\n]*\]\s*)?theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.GammaOne.heckePicard_arithmetic', 'Dubon2026.SourceFunctionField.GammaOne.gamma1ArithmeticPicardRep_torsion', 'Dubon2026.SourceFunctionField.GammaOne.gamma1ArithmeticPicardRep', 'Dubon2026.SourceFunctionField.GammaOne.arithmeticRingAut_j', 'Dubon2026.SourceFunctionField.GammaOne.fieldCoefficientMap_coe']
extra=['Dubon2026.SourceFunctionField.coeffMap_coeffMap', 'Dubon2026.SourceFunctionField.coeffMap_congr', 'Dubon2026.SourceFunctionField.coeffMap_qExpand', 'Dubon2026.SourceFunctionField.GammaOne.finiteDimensional_jCoordinateOver', 'Dubon2026.SourceFunctionField.GammaOne.heckeAlpha_finite', 'Dubon2026.SourceFunctionField.GammaOne.heckeBeta_finite', 'Dubon2026.SourceCurve.place_residue_bijective_of_finite_coordinate', 'Dubon2026.SourceCurve.Place.eq_ord_of_addHom_of_nonneg_iff', 'Dubon2026.SourceCurve.Place.ord_restrictAlong', 'Dubon2026.SourceCurve.Divisor.finitePullbackAlong_apply', 'Dubon2026.SourceCurve.Divisor.geometricPushforwardAlong_single', 'QuotientAddGroup.map', 'Finsupp.domCongr']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-arithmetic-9-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE ARITHMETIC')
output('SourceGammaOneArithmeticAudit9.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
localClosure=[];todo=mods.copy()
while todo:
 m=todo.pop()
 if m in localClosure:continue
 f=p/(m+'.lean')
 if not f.exists():continue
 localClosure.append(m)
 for line in re.findall(r'^import (.+)$',f.read_text(encoding='utf-8-sig'),re.M):
  for imp in line.split():
   if not imp.startswith(('Mathlib.','Dubon2026.','Lean.')) and (p/(imp+'.lean')).exists():todo.append(imp)
prior=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
dep=prior[prior.index('private def runPlanarPairingDependencyAudit'):]
for key,ns in [('roots',roots),('localModules',localClosure),('required',required)]:
 dep=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),dep)
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE GAMMA ONE ARITHMETIC DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Gamma1 Picard arithmetic representation construction, its Hecke-equivariance and torsion consumers, original-j invariance or literal coefficient projection. Only declaration values are traversed. Actual finite coordinates, coefficient transport, normalized orders, place restriction and ramification, divisor naturality and quotient action laws discharge every advertised arithmetic-compatibility input. Geometric/H1 and diamond comparison, Frobenius/inertia, finite-character Galois realization, original all-weight association and higher continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneArithmeticDependencyAudit9.lean',imports+dep)
route=p/'gamma1-arithmetic-hecke-picard-route-625.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
