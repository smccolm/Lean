from pathlib import Path
import json,re,ast,hashlib
p=Path(__file__).parent
mods=['SourceGammaOneDivisorReciprocityData']
ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['exists_analytic_support_representatives','sum_on_analytic_representatives_eq_degree','weighted_analytic_order_eq_half_coefficient','exists_degree_zero_reciprocity_data']]
required=ths+[ns+n for n in ['analyticPlace_eq_iff_gamma1_orbit','two_mul_ramification_eq_stabilizer_card','degree_mapDomain_analyticPlace','place_residue_bijective']]+['Finset.exists_subset_injOn_image_eq_of_surjOn','Finsupp.mapDomain_of_not_mem_image_support']
roots=[ths[-1]];queries=ths;defs=[]
ev={mods[0]:mods[0]+'859b'}
f=p/(mods[0]+'.lean')
assert (p/(ev[mods[0]]+'.exit')).read_text().strip()=='0' and (p/(ev[mods[0]]+'.log')).stat().st_size==0
assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=mods,separatelyAxiomChecked=[],separateReason='Every new theorem must occur in the VALUE closure of the actual original analytic-divisor reciprocity-data consumer.')
output('source-gamma-one-divisor-reciprocity-data-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneInvariantUntwistAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE INVARIANT UNTWIST','SOURCE GAMMA ONE DIVISOR RECIPROCITY DATA').replace('Gamma One Invariant Untwist','Gamma One Divisor Reciprocity Data')
output('SourceGammaOneDivisorReciprocityDataAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneInvariantUntwistDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE DIVISOR RECIPROCITY DATA DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual original analytic-divisor consumer. Native finite selection, original place-orbit separation, closed residues, degree and exact signed ramification are consumed. Analytic reciprocity and the full all-weight goal remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneDivisorReciprocityDataDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneInvariantUntwistScratchOwnership858.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def inspectOwnership'):];b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneDivisorReciprocityDataScratchOwnership860.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=p/'gamma-one-divisor-reciprocity-data-route-859.json';rd=json.loads(route.read_text(encoding='utf-8'));rd['reuseChecked'].append(dict(path=str(route),sha256=sha(route)))
output('source-gamma-one-divisor-reciprocity-data-audit-route-860.json',json.dumps(rd,indent=2)+'\n')
t=(p/'record_source_gamma_one_invariant_untwist_858.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-invariant-untwist-1','source-gamma-one-divisor-reciprocity-data-1'),('SourceGammaOneInvariantUntwist','SourceGammaOneDivisorReciprocityData'),('SOURCE GAMMA ONE INVARIANT UNTWIST','SOURCE GAMMA ONE DIVISOR RECIPROCITY DATA'),('source-gamma-one-invariant-untwist-audit-route-858.json','source-gamma-one-divisor-reciprocity-data-audit-route-860.json'),('(9, 43, 150)','(1, 4, 10)'),('all 150 required','all 10 required'),('requiredProofValueEdges=150','requiredProofValueEdges=10'),('modules=9, queries=43','modules=1, queries=4'),('proofEdges=150','proofEdges=10'),('== 9','== 1'),('linterScopes=9','linterScopes=1')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);output('record_source_gamma_one_divisor_reciprocity_data_860.py',t)
print('Prepared four-query exhaustive, sixteen-linter and ten-edge VALUE audits for actual divisor data.')
