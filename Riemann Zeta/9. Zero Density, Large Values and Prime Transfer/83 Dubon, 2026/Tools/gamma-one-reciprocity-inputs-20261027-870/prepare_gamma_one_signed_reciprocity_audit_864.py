from pathlib import Path
import json,re,ast,hashlib
p=Path(__file__).parent
mods=['SourceWeightTwoSignedForms','SourceWeightTwoSignedReciprocity']
ns='Dubon2026.SourceFunctionField.GammaOne.SignedForms.'
ths=[ns+n for n in ['weightTwo_slash_neg','extend_apply','extend_injective','along_extend','period_extend_representative','dualPeriod_comp_extend','integralLattice_comp_extend','multiplier_extend','orbit_iff']]
defs=[ns+'extend'];queries=ths+defs
separate=[ns+'extend_apply',ns+'extend_injective']
required=[n for n in queries if n not in separate]+['Dubon2026.sourceUpperHalfPlane_primitive_difference','Dubon2026.sourceWeightTwoPrimitive_hasDerivAt','Dubon2026.sourceWeightTwoDualPeriod_mem','Dubon2026.SourceFunctionField.GammaOne.CentralSign.representative_spec','Submodule.span_induction']
roots=[ns+n for n in ['integralLattice_comp_extend','multiplier_extend','orbit_iff']]
ev=dict(zip(mods,[mods[0]+'861c',mods[1]+'862c']))
for m in mods:
 f=p/(m+'.lean')
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=mods,separatelyAxiomChecked=separate,separateReason='Definitional evaluation and injectivity are separately axiom checked; lattice restriction, multiplier transport and orbit comparison consume every other new declaration.')
output('source-gamma-one-signed-reciprocity-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneDivisorReciprocityDataAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE DIVISOR RECIPROCITY DATA','SOURCE GAMMA ONE SIGNED RECIPROCITY').replace('Gamma One Divisor Reciprocity Data','Gamma One Signed Reciprocity')
output('SourceGammaOneSignedReciprocityAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneDivisorReciprocityDataDependencyAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE SIGNED RECIPROCITY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the signed-to-original lattice, multiplier and orbit consumers. Original periods and central-sign representatives are consumed. Analytic reciprocity and full all-weight goal remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneSignedReciprocityDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneDivisorReciprocityDataScratchOwnership860.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneSignedReciprocityScratchOwnership864.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'gamma-one-signed-forms-route-861.json',p/'gamma-one-signed-reciprocity-route-862.json']
rd=dict(chain=['DUB-17/18','all-weight arithmetic association','original Gamma1 coefficient Hecke realization','Picard/H1','Abel-Jacobi converse','analytic reciprocity','faithful central-sign transport'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],assumptionsToDischarge=['same actual weight-two cusp function extends to signed subgroup','normalized endpoint and group periods agree','signed integer lattice restricts into original integer lattice','actual multiplier and orbits transport across central sign'],remaining='Analytic winding/period limit, Petersson reciprocity, original principal-divisor converse and full arithmetic chain remain. No gate closed; 16/20; DUB-17--20 OPEN.')
output('source-gamma-one-signed-reciprocity-audit-route-864.json',json.dumps(rd,indent=2)+'\n')
t=(p/'record_source_gamma_one_divisor_reciprocity_data_860.py').read_text(encoding='utf-8-sig')
repls=[('source-gamma-one-divisor-reciprocity-data-1','source-gamma-one-signed-reciprocity-1'),('SourceGammaOneDivisorReciprocityData','SourceGammaOneSignedReciprocity'),('SOURCE GAMMA ONE DIVISOR RECIPROCITY DATA','SOURCE GAMMA ONE SIGNED RECIPROCITY'),('source-gamma-one-divisor-reciprocity-data-audit-route-860.json','source-gamma-one-signed-reciprocity-audit-route-864.json'),('(1, 4, 10)',f'(2, 10, {len(required)})'),('all 10 required',f'all {len(required)} required'),('requiredProofValueEdges=10',f'requiredProofValueEdges={len(required)}'),('modules=1, queries=4','modules=2, queries=10'),('proofEdges=10',f'proofEdges={len(required)}'),('== 1','== 2'),('linterScopes=1','linterScopes=2')]
for a,b in repls:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);output('record_source_gamma_one_signed_reciprocity_864.py',t)
print(json.dumps(dict(modules=len(mods),queries=len(queries),required=len(required))))
