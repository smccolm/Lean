from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceGammaOneFunctionField', 'SourceGammaOneJCoordinate', 'SourceGammaOneRatioClosure', 'SourceGammaOneNormRelation', 'SourceGammaOneComplexRelation', 'SourceGammaOneComplexRatio', 'SourceGammaOneRationalRelation', 'SourceGammaOneFunctionFieldFinite', 'SourceGammaOneFunctionFieldBaseChange', 'SourceGammaOneCurveFinite']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.GammaOne.gamma1_finite_coordinate', 'Dubon2026.SourceFunctionField.GammaOne.gamma1_hecke_finite_coordinate', 'Dubon2026.SourceFunctionField.GammaOne.gamma1_hecke_baseChange_le', 'Dubon2026.SourceFunctionField.GammaOne.transcendental_jCoordinate']
extra=['Dubon2026.SourceFunctionField.ModularNormPolynomial.Sform_eq_zero', 'Dubon2026.SourceFunctionField.ModularNormPolynomial.qExpansion_Sform', 'Dubon2026.SourceFunctionField.exists_levelOne_j_polynomial', 'Dubon2026.SourceFunctionField.linearIndependent_coeffMap_algebraMap', 'Dubon2026.SourceFunctionField.DegreeTransport.finite_and_finrank_le', 'Dubon2026.SourceFunctionField.transcendental_jqModC', 'IntermediateField.exists_lt_finrank_of_infinite_dimensional', 'Field.exists_primitive_element', 'Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-function-field-10b-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE FUNCTION FIELD')
output('SourceGammaOneFunctionFieldAudit10b.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE GAMMA ONE FUNCTION FIELD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual Gamma1/Hecke function-field finite coordinates, the literal scalar-extended inclusion, or the original rational-coordinate transcendence theorem. Only declaration values are traversed. Original j, native modular norms, level-one polynomials, existing Laurent independence, native primitive-element theory and existing scalar-extension finiteness discharge every advertised field-generation, transcendence and finite-degree input. Arithmetic geometric and diamond comparison, finite-character Galois realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneFunctionFieldDependencyAudit10b.lean',imports+dep)
route=p/'gamma1-function-field-finite-route-620b.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
