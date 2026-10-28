from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceIntegralCharacter'+s for s in ['Crossed','Potential','Shapiro','FreeProduct','InitialLift','CuspConjugacy','CuspSum','Correction','ModularFacts','ModularBridge']]+['SourceIntegralParabolicCharacterLift','SourceGammaOneIntegralParabolicLift']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 code=re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S);stack=[]
 for raw in code.splitlines():
  line=re.sub(r'--.*','',raw).strip()
  if line.startswith('namespace '):stack.append(('namespace',line.split()[1]));continue
  if re.match(r'^(noncomputable )?section\b',line):stack.append(('section',''));continue
  if re.match(r'^end(?:\s|$)',line):assert stack,(m,line);stack.pop();continue
  line=re.sub(r'^@\[[^]]*\]\s*','',line)
  d=re.match(r'^(?:noncomputable\s+)?(theorem|def|abbrev)\s+([^\s(:]+)',line)
  if d:
   name='.'.join([x[1] for x in stack if x[0]=='namespace']+[d[2]])
   (ths if d[1]=='theorem' else defs).append(name)
 assert not stack,m
queries=ths+defs;ns='Dubon2026.SourceIntegralCharacterLift.'
required=[ns+n for n in ['IsCrossed.map_one','IsCrossed.conj_apply','IsCrossed.map','IsCrossed.ext_of','isCrossed_cob','cob_apply_of_smul_eq','exists_potential','trHom','evalBase','evalBase_conj','shapiro','isCrossed_shapiro','evalBase_shapiro','genHom','totalHom','totalHom_right','liftCrossed','isCrossed_liftCrossed','liftCrossed_of','exists_char_comp_eq_of_forall_conj_of','char_zpow','char_conj_zpow_eq_zero','sum_char_cuspGen_eq_zero','exists_sub_smul_apply_conj_zpow_eq_zero','isOfFinOrder_of_rho','isOfFinOrder_of_rho_eq_conj_of','exists_rho_eq_conj_tP_zpow','trace_sq_of_rho_eq_conj_tP_zpow','exists_int_lift']]
required+=['Dubon2026.sourceGamma1_integral_parabolic_character_lift','Dubon2026.cosetTransition_mul','Dubon2026.SourceParabolic.classification','MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot']
required+=['Dubon2026.SourceModularFreeProduct.'+n for n in ['mulEquiv','mulEquiv_of_zero','mulEquiv_of_one','lift_injective','range_lift_eq','ker_toPerm_eq_center','mem_center_iff_eq']]
cc=json.loads((p/'source-cusp-correction-1-audit-config.json').read_text(encoding='utf-8'))
required+=cc['proofEdges']
closure=mods+cc['modules']+json.loads((p/'source-modular-free-product-1-audit-config.json').read_text(encoding='utf-8'))['modules']
roots=['Dubon2026.sourceGamma1_integral_parabolic_character_lift']
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=[q for q in queries if q not in required],separateReason='All public declarations are individually axiom checked; every required substantive dependency must occur in the VALUE closure of the actual Gamma1 integral parabolic lift. Scalar helpers are not falsely labelled used by that consumer.')
output('source-integral-parabolic-character-lift-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceCuspCorrectionAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE CUSP CORRECTION','SOURCE INTEGRAL PARABOLIC CHARACTER LIFT').replace('Cusp Correction','Integral Parabolic Character Lift')
output('SourceIntegralParabolicCharacterLiftAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceCuspCorrectionDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE INTEGRAL PARABOLIC CHARACTER LIFT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual Gamma1 integral lift. Native coset-transition multiplication, native transfer, the actual modular free-product equivalence, actual cusp-character correction and original trace-four classification are consumed. Unitary logarithms, analytic reciprocity and full arithmetic association remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceIntegralParabolicCharacterLiftDependencyAudit1.lean',imports+b)
t=(p/'SourceCuspCorrectionScratchOwnership817.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def inspectOwnership'):];b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceIntegralParabolicCharacterLiftScratchOwnership830.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
routes=[p/n for n in ['gamma-one-integral-character-lift-route-818.json','gamma-one-integral-character-correction-route-823.json','gamma-one-integral-character-modular-route-826.json']]
rd=json.loads(routes[-1].read_text(encoding='utf-8'));rd['reuseChecked']+=[dict(path=str(f),sha256=sha(f)) for f in routes]
output('source-integral-parabolic-character-lift-audit-route-830.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_source_cusp_correction_817.py').read_text(encoding='utf-8-sig')
for a,b in [('source-cusp-correction-1','source-integral-parabolic-character-lift-1'),('SourceCuspCorrection','SourceIntegralParabolicCharacterLift'),('SOURCE CUSP CORRECTION','SOURCE INTEGRAL PARABOLIC CHARACTER LIFT'),('source-cusp-correction-audit-route-817.json','source-integral-parabolic-character-lift-audit-route-830.json'),('(6, 73, 18)',str((len(mods),len(queries),len(required)))),('all 18 required',f'all {len(required)} required'),('requiredProofValueEdges=18',f'requiredProofValueEdges={len(required)}'),('modules=6, queries=73',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=18',f'proofEdges={len(required)}'),('== 6','== 12'),('linterScopes=6','linterScopes=12')]:
 assert a in s,a
 s=s.replace(a,b)
ast.parse(s);output('record_source_integral_parabolic_character_lift_830.py',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),edges=len(required))))
