from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).parent
mods=['SourceWeightTwoPeriodUntwist','SourceMeromorphicNormalUntwist','SourceMeromorphicPeriodUntwist','SourceMeromorphicTranslatedGerms','SourceMeromorphicCuspUntwist','SourceCuspDerivativeDecay','SourceMeromorphicUntwistDecay','SourceMeromorphicUntwistDerivative','SourceGammaOneInvariantUntwist']
ev=dict(zip(mods,[mods[0]+'849b',mods[1]+'850b',mods[2]+'851d',mods[3]+'852c',mods[4]+'853c',mods[5],mods[6]+'855b',mods[7],mods[8]]))
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');log=p/(ev[m]+'.log');ex=p/(ev[m]+'.exit')
 assert ex.read_text().strip()=='0' and log.stat().st_size==0,m
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
queries=ths+defs
old=json.loads((p/'source-gamma-one-meromorphic-multiplier-periods-1-audit-config.json').read_text(encoding='utf-8'))
unused=['Dubon2026.SourcePeriodUntwist.'+n for n in ['norm_R','fderiv_R_apply','normalized_eq_of_tendsto']]
required=old['proofEdges']+[q for q in queries if q not in unused]
required+=['meromorphicNFOn_toMeromorphicNFOn','meromorphicOrderAt_toMeromorphicNFOn','UpperHalfPlane.analyticAt_smul','UpperHalfPlane.meromorphicOrderAt_comp_smul','Homeomorph.map_punctured_nhds_eq','Complex.norm_deriv_le_of_forall_mem_sphere_norm_le','Dubon2026.sourceWeightTwoPrimitive_hasDerivAt','Dubon2026.sourceWeightTwoPrimitive_exists_cusp_limit','Dubon2026.sourceWeightTwoPrimitive_period']
required=list(dict.fromkeys(required))
roots=['Dubon2026.sourceGamma1_meromorphic_invariant_untwist'];closure=mods
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=unused,separateReason='All public declarations are axiom checked. The norm, pointwise derivative evaluation and normalized-value limit helpers are separately checked; the assembled original-divisor consumer must actually use every remaining new declaration and all 101 earlier multiplier dependencies.')
output('source-gamma-one-invariant-untwist-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneMeromorphicMultiplierPeriodsAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE MEROMORPHIC MULTIPLIER PERIODS','SOURCE GAMMA ONE INVARIANT UNTWIST').replace('Gamma One Meromorphic Multiplier Periods','Gamma One Invariant Untwist')
output('SourceGammaOneInvariantUntwistAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneMeromorphicMultiplierPeriodsDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE INVARIANT UNTWIST DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the original Gamma1 divisor and invariant-untwist consumer. Actual integral lifting and multiplier realization, native normalization, the original cusp-form primitive, native action and Cauchy estimates are consumed. Analytic reciprocity, meromorphic construction from periods and full arithmetic association remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneInvariantUntwistDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneMeromorphicMultiplierPeriodsScratchOwnership846.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def inspectOwnership'):];b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneInvariantUntwistScratchOwnership858.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
routes=[p/('gamma-one-'+n+'-route-'+str(i)+'.json') for i,n in [(849,'period-untwist'),(850,'normal-untwist'),(851,'meromorphic-untwist'),(852,'translated-germs'),(853,'cusp-untwist'),(854,'cusp-derivative'),(855,'untwist-decay'),(856,'untwist-derivative'),(857,'invariant-untwist')]]
rd=json.loads(routes[-1].read_text(encoding='utf-8'));rd['reuseChecked']+=[dict(path=str(f),sha256=sha(f)) for f in routes]
output('source-gamma-one-invariant-untwist-audit-route-858.json',json.dumps(rd,indent=2)+'\n')
t=(p/'record_source_gamma_one_meromorphic_multiplier_periods_846.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-meromorphic-multiplier-periods-1','source-gamma-one-invariant-untwist-1'),('SourceGammaOneMeromorphicMultiplierPeriods','SourceGammaOneInvariantUntwist'),('SOURCE GAMMA ONE MEROMORPHIC MULTIPLIER PERIODS','SOURCE GAMMA ONE INVARIANT UNTWIST'),('source-gamma-one-meromorphic-multiplier-periods-audit-route-846.json','source-gamma-one-invariant-untwist-audit-route-858.json'),('(5, 10, 101)',str((len(mods),len(queries),len(required)))),('all 101 required',f'all {len(required)} required'),('requiredProofValueEdges=101',f'requiredProofValueEdges={len(required)}'),('modules=5, queries=10',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=101',f'proofEdges={len(required)}'),('== 5','== 9'),('linterScopes=5','linterScopes=9')]:
 assert a in t,a
 t=t.replace(a,b)
a=" assert f.with_suffix('.exit').read_text().strip() == '0' and f.with_suffix('.log').stat().st_size == 0, m"
b=" ev = p / cfg['compileEvidence'][m]\n assert ev.with_suffix('.exit').read_text().strip() == '0' and ev.with_suffix('.log').stat().st_size == 0, m"
assert a in t;t=t.replace(a,b)
a=" files.append(dict(path=str(f), sha256=sha(f), oleanSha256=sha(f.with_suffix('.olean'))))"
b=" files.append(dict(path=str(f), sha256=sha(f), oleanSha256=sha(f.with_suffix('.olean')), compileLog=str(ev.with_suffix('.log')), compileExit=str(ev.with_suffix('.exit'))))"
assert a in t;t=t.replace(a,b)
ast.parse(t);output('record_source_gamma_one_invariant_untwist_858.py',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))
