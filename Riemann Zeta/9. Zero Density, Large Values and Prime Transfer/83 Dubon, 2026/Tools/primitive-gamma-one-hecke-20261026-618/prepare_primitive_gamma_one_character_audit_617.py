from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceGammaOneHeckeWords', 'SourceGammaOneOperatorDescent', 'SourceGammaOneHeckeFinite', 'SourcePrimitiveGammaOneHeckeCharacter', 'SourcePrimitiveGammaOneH1Realization']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourcePrimitive_exists_gammaOneH1HeckeCharacters']
extra=['Dubon2026.sourceGammaOneConstantH1Transfer_hecke','Dubon2026.sourceGammaOneConstantH1Transfer_surjective','Dubon2026.sourceHeckeWord_intertwine_addHom','Dubon2026.sourceBinaryH1ModulusOperatorMap_zero_of_coefficients','Dubon2026.sourceFiniteOperatorCharacterDescend_comp','Dubon2026.sourcePrimitiveFiniteH1HeckeCharacter_comp','Dubon2026.sourcePrimitiveH1AdicQuotientCharacter_hecke','Dubon2026.sourcePrimitive_exists_finiteH1OperatorCharacters','Dubon2026.sourceH1Finite','Dubon2026.sourcePrimePower_six_isUnit','SpecialLinearGroup.SL2Z_generators']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-primitive-gamma-one-character-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE PRIMITIVE GAMMA ONE CHARACTER')
output('SourcePrimitiveGammaOneCharacterAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE PRIMITIVE GAMMA ONE CHARACTER DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the original primitive-form consumer producing actual finite Gamma1 H1 Hecke characters at every positive power of every prime greater than three. Only declaration values are traversed. The genuine surjective transfer and its proved Hecke compatibility feed the existing additive word intertwiner. The exact original integral reduction kernel proves operator-relation descent, and native ring-map descent gives a canonical map into the original finite tensor-operator algebra. Original Fourier-valued adic characters then give the entire matching word character and exact prime values. Native congruence-group finite generation and existing finite H1 prove the actual Gamma1 operator ring finite. The generator set explicitly omits primes dividing the level or modulus; no surjectivity onto the entire original Hecke algebra is claimed. Arithmetic geometric and diamond comparison, finite Galois realization, all-weight characteristic-zero association and higher continuation remain required; no characteristic-zero point is inferred from finite characters. DUB-17--20 OPEN; 16/20."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourcePrimitiveGammaOneCharacterDependencyAudit5.lean',imports+dep)
route=p/'gamma1-original-finite-character-route-617.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
