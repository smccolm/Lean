from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceGammaOneResidues', 'SourceGammaOneHeckePicard']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^(?:@\[[^\n]*\]\s*)?theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.GammaOne.heckeDivisor_mem_degZero', 'Dubon2026.SourceFunctionField.GammaOne.isPrincipal_heckeDivisor', 'Dubon2026.SourceFunctionField.GammaOne.heckePicard_mk', 'Dubon2026.SourceFunctionField.GammaOne.heckeDivisor', 'Dubon2026.SourceFunctionField.GammaOne.heckePicard']
extra=['Dubon2026.SourceFunctionField.GammaOne.gamma1_finite_coordinate', 'Dubon2026.SourceFunctionField.GammaOne.gamma1_hecke_finite_coordinate', 'Dubon2026.SourceFunctionField.GammaOne.heckeAlpha_finite', 'Dubon2026.SourceFunctionField.GammaOne.heckeBeta_finite', 'Dubon2026.SourceCurve.place_residue_bijective_of_finite_coordinate', 'Dubon2026.SourceCurve.Divisor.geometricCorrespondence', 'Dubon2026.SourceCurve.Divisor.geometricCorrespondence_mem_degZero', 'Dubon2026.SourceCurve.Divisor.isPrincipal_geometricCorrespondence', 'Dubon2026.SourceCurve.Pic0.geometricCorrespondence', 'Dubon2026.SourceCurve.Pic0.geometricCorrespondence_mk']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-hecke-picard-2b-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE HECKE PICARD')
output('SourceGammaOneHeckePicardAudit2b.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE GAMMA ONE HECKE PICARD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Gamma1 divisor/Picard operator construction values, degree-zero and principal-divisor preservation, or representative evaluation. Construction roots are checked explicitly because definitional wrapper names in consumer types do not count as proof-value edges. Only declaration values are traversed. Actual finite coordinates and finite Hecke maps, closed residue fields and existing norm/degree identities discharge all advertised geometric-construction inputs. Geometric/H1 and diamond comparison, arithmetic action compatibility, finite-character Galois realization, original all-weight characteristic-zero association and higher continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneHeckePicardDependencyAudit2b.lean',imports+dep)
route=p/'gamma1-actual-picard-hecke-route-624b.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
