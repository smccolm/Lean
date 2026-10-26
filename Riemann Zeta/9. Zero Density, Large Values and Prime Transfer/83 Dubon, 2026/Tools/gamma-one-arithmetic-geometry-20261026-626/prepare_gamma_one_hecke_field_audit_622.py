from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceGammaOneModularStretch', 'SourceGammaOneModularStretchCoefficients', 'SourceGammaOneHeckeFieldInclusion', 'SourceGammaOneHeckeDegeneracy', 'SourceGammaOneHeckeFieldFinite']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^(?:@\[[^\n]*\]\s*)?theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.GammaOne.heckeAlpha_finite', 'Dubon2026.SourceFunctionField.GammaOne.heckeBeta_finite', 'Dubon2026.SourceFunctionField.GammaOne.heckeAlpha_coe', 'Dubon2026.SourceFunctionField.GammaOne.heckeBeta_coe']
extra=['ModularForm.translate', 'Dubon2026.levelRaiseFun_apply', 'Dubon2026.hasSum_pow_dvd_reindex', 'ModularFormClass.qExpansion_coeff_unique', 'Dubon2026.SourceFunctionField.coeffMap_qExpand', 'Dubon2026.SourceCurve.finite_over_transcendental_of_finite_coordinate', 'Dubon2026.SourceCurve.finite_hom_of_finite_image_coordinate', 'Dubon2026.SourceFunctionField.GammaOne.gamma1_finite_coordinate', 'Dubon2026.SourceFunctionField.GammaOne.gamma1_hecke_finite_coordinate', 'Dubon2026.SourceFunctionField.GammaOne.gamma1_hecke_baseChange_le']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-hecke-field-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE HECKE FIELD')
output('SourceGammaOneHeckeFieldAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE GAMMA ONE HECKE FIELD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in finiteness or literal projection of the actual Gamma1 Hecke maps. Only declaration values are traversed. Native modular translation, existing sparse sums, actual integral ratios, Laurent coefficient compatibility and proved coordinate exchange discharge the field-preservation and finite-map inputs. Arithmetic geometric and diamond comparison, finite-character Galois realization, original all-weight characteristic-zero association and higher continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneHeckeFieldDependencyAudit5.lean',imports+dep)
route=p/'gamma1-finite-hecke-field-route-622.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
