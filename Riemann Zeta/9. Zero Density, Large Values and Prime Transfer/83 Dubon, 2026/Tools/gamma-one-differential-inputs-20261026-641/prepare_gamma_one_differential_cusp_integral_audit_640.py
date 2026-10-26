from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceInverseJLevelOneIntegral', 'SourceIntegralHomogeneousRelation', 'SourceModularInverseJIntegral', 'SourceGammaOneCuspAuxiliaryForm', 'SourceGammaOneCuspAuxiliaryExpansion', 'SourceGammaOneDifferentialCuspIntegral']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^(?:@\[[^\n]*\]\s*)?theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.GammaOne.isIntegral_cusp_differential_cusp_expression']
extra=['Dubon2026.SourceFunctionField.exists_levelOne_j_polynomial', 'Dubon2026.SourceFunctionField.ModularNormPolynomial.Aform', 'Dubon2026.SourceFunctionField.ModularNormPolynomial.Sform_eq_zero', 'Dubon2026.SourceFunctionField.ModularNormPolynomial.qExpansion_Sform', 'CuspFormClass.exp_decay_atImInfty', 'ModularForm.exp_isBigO_discriminant', 'Dubon2026.SourceFunctionField.ModularQDerivative.exists_qEuler_jqModC_formula', 'Dubon2026.SourceFunctionField.ModularQDerivative.laurent_discriminant_relation', 'Dubon2026.SourceFunctionField.GammaOne.hper']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-differential-cusp-integral-6-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE DIFFERENTIAL CUSP INTEGRAL')
output('SourceGammaOneDifferentialCuspIntegralAudit6.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE GAMMA ONE DIFFERENTIAL CUSP INTEGRAL DEPENDENCY AUDIT PASS: all {required.size} required dependencies occur in the actual cusp integral consumer. Only declaration values are traversed. Existing level-one polynomials and modular norms, native cusp decay and discriminant growth construct the exact inverse-j integral bound. Regularity, differential realization, actual Picard/H1 and diamond comparison, original all-weight association and higher continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'

output('SourceGammaOneDifferentialCuspIntegralDependencyAudit6.lean',imports+dep)
route=p/'gamma1-differential-cusp-integral-route-640.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
