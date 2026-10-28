from pathlib import Path
import json,re,ast,hashlib
p=Path(__file__).parent
mods=['SourceComplexWedgeStokes','SourceComplexWedgeLocalLog','SourceComplexWedgeDisc','SourceComplexWedgeIntegral','SourceGammaOneUntwistWedgeIntegral']
ths=[];defs=[]
for m in mods:
 t=(p/(m+'.lean')).read_text(encoding='utf-8')
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 for kind,n in re.findall(r'^(?:noncomputable )?(theorem|def) (\S+)',t,re.M):
  (ths if kind=='theorem' else defs).append(ns+n)
queries=ths+defs
required=queries+['Dubon2026.SourceComplexReciprocity.DbarFundamental.integral_inv_sub_mul_dbar','Dubon2026.SourcePeriodUntwist.Φ_local','Dubon2026.SourcePeriodUntwist.normalized_local_form','Dubon2026.SourcePeriodUntwist.Ek_hasDerivAt','Dubon2026.sourceWeightTwoPrimitive_hasDerivAt','SmoothPartitionOfUnity.exists_isSubordinate','ContDiffAt.isSymmSndFDerivAt','integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable']
roots=['Dubon2026.sourceGamma1_untwist_wedge_integral']
ev={m:m+'874a' for m in mods}
for m in mods:
 f=p/(m+'.lean')
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
priorCfg=json.loads((p/'source-gamma-one-log-derivative-residues-1b-audit-config.json').read_text(encoding='utf-8'))
closure=mods+priorCfg['modules']+['SourceWeightTwoPeriodUntwist','SourceMeromorphicNormalUntwist','SourceMeromorphicPeriodUntwist']
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=[],separateReason='Every new declaration is required in the VALUE closure of the actual original-divisor untwist wedge consumer. Unconsumed helpers were deferred before audit.')
output('source-gamma-one-untwist-wedge-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneLogDerivativeResiduesAudit1b.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE LOG DERIVATIVE RESIDUES','SOURCE GAMMA ONE UNTWIST WEDGE').replace('Gamma One Log Derivative Residues','Gamma One Untwist Wedge')
output('SourceGammaOneUntwistWedgeAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneLogDerivativeResiduesDependencyAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE UNTWIST WEDGE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual original-divisor untwist consumer. Native smooth partition and derivative symmetry, the proved singular kernel, actual meromorphic normal form and the original cusp-form primitive are consumed. Modular winding/period limit and full all-weight goal remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneUntwistWedgeDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneLogDerivativeResiduesScratchOwnership869.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneUntwistWedgeScratchOwnership874.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
paths=['complex-wedge-stokes-route-871.json','complex-wedge-integral-route-872.json','gamma-one-untwist-wedge-route-873.json','wedge-minimal-route-review-872c.json','wedge-minimal-route-review-874a.json','source-gamma-one-invariant-untwist-1-scratch-receipt.json','source-gamma-one-log-derivative-residues-1b-scratch-receipt.json']
rows=[dict(path=str(p/n),sha256=sha(p/n)) for n in paths]
for n in paths[:2]:
 for row in json.loads((p/n).read_text(encoding='utf-8')).get('reuseChecked',[]):rows.append(row)
for n in paths[-2:]:
 c=json.loads((p/n).read_text(encoding='utf-8'))
 for row in c['files']:
  f=Path(row['path']);assert sha(f)==row['sha256']
route=dict(chain=['DUB-17/18','all-weight arithmetic association','original Gamma1 coefficient Hecke realization','Picard/H1','Abel-Jacobi converse','analytic reciprocity','winding-period limit','actual untwist wedge identity'],reuseChecked=rows,assumptionsToDischarge=['Compact-support wedge integration by parts from native derivative symmetry','C1 local integer-order models imply integrability and exact wedge/residue identity via proved singular kernel and native smooth partition','Actual original divisor and its meromorphic untwist derive every local model; existing actual cusp-form primitive supplies derivative'],remaining='F and exact original-divisor orders remain inputs. Invariance and cusp control are proved separately by the invariant-untwist consumer. Actual smooth comparison model and modular winding/period/Petersson limit remain, followed by original principal-divisor converse and entire all-weight arithmetic chain. No DUB gate closed; 16/20; DUB-17--20 OPEN.')
output('source-gamma-one-untwist-wedge-audit-route-874.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_log_derivative_residues_869b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-log-derivative-residues-1b','source-gamma-one-untwist-wedge-1'),('SourceGammaOneLogDerivativeResiduesAudit1b','SourceGammaOneUntwistWedgeAudit1'),('SourceGammaOneLogDerivativeResidues','SourceGammaOneUntwistWedge'),('SOURCE GAMMA ONE LOG DERIVATIVE RESIDUES','SOURCE GAMMA ONE UNTWIST WEDGE'),('source-gamma-one-log-derivative-residues-audit-route-869.json','source-gamma-one-untwist-wedge-audit-route-874.json'),('(9, 51, 61)',str((len(mods),len(queries),len(required)))),('all 61 required',f'all {len(required)} required'),('requiredProofValueEdges=61',f'requiredProofValueEdges={len(required)}'),('modules=9, queries=51',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=61',f'proofEdges={len(required)}'),('== 9',f'== {len(mods)}'),('linterScopes=9',f'linterScopes={len(mods)}')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);output('record_source_gamma_one_untwist_wedge_874.py',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))
