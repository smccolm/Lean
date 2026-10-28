from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83');inv=json.loads((p/'cusp-correction-declaration-inventory-817.json').read_text(encoding='utf-8'))
mods=inv['modules'];ths=inv['theorems'];defs=inv['constructions'];queries=ths+defs
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
ns='Dubon2026.SourceCuspCorrection.'
required=[ns+n for n in ['lTransl','lTranslMulAut','chainSect','edgeChain','edgeChain_mul','edgeChainHom','edgeChainHom_conj','edgeChainHom_genAt_raw','enum_injOn_range','exists_enum_eq_of_cusp_eq','sum_ite_enum_eq','edgeChainHom_genAt_apply','edgeChar_genAt','single_sub_single_mem_span_of_smul','single_sub_single_mem_span_cuspDiffAt','exists_addChar_of_mem_span','closure_sA_τ','engine']]
roots=[ns+'engine']
assert (len(mods),len(ths),len(defs),len(required))==(6,51,22,18)
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=roots,separatelyAxiomChecked=[q for q in queries if q not in required],scratchImportClosure=mods,separateReason='All 73 public declarations are individually axiom checked. The 18 substantive dependencies must occur in the VALUE closure of the single actual prescribed-cusp-character consumer engine, rather than merely in independently queried helpers.')
output('source-cusp-correction-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE CUSP CORRECTION').replace('Gamma One Exact Ramification','Cusp Correction')
output('SourceCuspCorrectionAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE CUSP CORRECTION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the single actual prescribed-cusp-character consumer engine. Actual finite edge chains, parabolic coset cycles, generator values and integer span realization are consumed. Integral character lifting, unitary logarithms, analytic reciprocity and full arithmetic association remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceCuspCorrectionDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=p/'gamma-one-integral-lift-cusp-correction-route-811.json';old=json.loads(route.read_text(encoding='utf-8'))
rd=dict(chain=old['chain'],assumptionsToDischarge='Construct an actual additive character with arbitrary prescribed values of zero total sum on the primitive parabolic generators of any finite-index subgroup of C2*C3. The finite edge-chain cocycle, actual coset cycles, exact generator evaluations and span realization are proved. No character-realization premise remains in this correction theorem.',remaining='Promote and run assembled verification. Initial integral character lifting, zero-sum cusp values for an arbitrary lift, composition into original Gamma1 parabolic lifting, unitary logarithms, analytic reciprocity and all-weight arithmetic association remain. 16/20; DUB-17--20 OPEN.',reuseChecked=old['reuseChecked']+[dict(path=str(route),sha256=sha(route))],shorterRoute=old['shorterRoute'])
output('source-cusp-correction-audit-route-817.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_closed_chain_periods_804.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-closed-chain-periods-1','source-cusp-correction-1'),('SourceGammaOneClosedChainPeriods','SourceCuspCorrection'),('SOURCE GAMMA ONE CLOSED CHAIN PERIODS','SOURCE CUSP CORRECTION'),('gamma-one-closed-chain-audit-route-804.json','source-cusp-correction-audit-route-817.json'),('(5, 20, 24)','(6, 73, 18)'),('all 24 required','all 18 required'),('requiredProofValueEdges=24','requiredProofValueEdges=18'),('modules=5, queries=20','modules=6, queries=73'),('proofEdges=24','proofEdges=18'),('== 5','== 6'),('linterScopes=5','linterScopes=6'),('separatelyAxiomChecked=[]','separatelyAxiomChecked=cfg["separatelyAxiomChecked"]')]:
 assert a in s,a
 s=s.replace(a,b)
ast.parse(s);output('record_source_cusp_correction_817.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceCuspCorrectionScratchOwnership817.lean',s)
print(json.dumps(dict(modules=6,queries=73,edges=18,roots=roots)))
