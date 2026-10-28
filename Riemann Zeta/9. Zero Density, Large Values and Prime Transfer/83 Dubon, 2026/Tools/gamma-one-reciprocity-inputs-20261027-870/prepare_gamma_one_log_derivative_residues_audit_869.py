from pathlib import Path
import json,re,ast,hashlib
p=Path(__file__).parent
mods=['SourceComplexHolomorphicStokes','SourceComplexDbarCutoff','SourceComplexDbarKernelIntegrability','SourceComplexDbarRadialNormalization','SourceComplexCauchyPompeiu','SourceComplexResidueLocalModels','SourceComplexResidueIntegral','SourceComplexLogDerivativeResidues','SourceGammaOneLogDerivativeResidues']
ths=[];defs=[]
for m in mods:
 t=(p/(m+'.lean')).read_text(encoding='utf-8')
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 for kind,n in re.findall(r'^(?:noncomputable )?(theorem|def) (\S+)',t,re.M):
  (ths if kind=='theorem' else defs).append(ns+n)
queries=ths+defs
required=queries+['Dubon2026.SourcePeriodUntwist.differentiableOn_Ek','Dubon2026.SourcePeriodUntwist.Ek_hasDerivAt','Dubon2026.sourceWeightTwoPrimitive_hasDerivAt','integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable','MeasureTheory.integral_fun_norm_addHaar','MeasureTheory.integrableOn_ball_of_norm_le_rpow','MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto','logDeriv_mul','logDeriv_fun_zpow','meromorphicOrderAt_eq_int_iff']
roots=['Dubon2026.sourceGamma1_logDerivative_residue_integral']
ev={m:m for m in mods}
ev['SourceComplexHolomorphicStokes']='SourceComplexHolomorphicStokes863b'
ev['SourceComplexLogDerivativeResidues']='SourceComplexLogDerivativeResidues867c'
ev['SourceGammaOneLogDerivativeResidues']='SourceGammaOneLogDerivativeResidues868c'
for m in mods:
 f=p/(m+'.lean')
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=mods+['SourceWeightTwoPeriodUntwist'],separatelyAxiomChecked=[],separateReason='Every new declaration is required in the VALUE closure of the actual original-divisor logarithmic-residue consumer.')
output('source-gamma-one-log-derivative-residues-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneDivisorReciprocityDataAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE DIVISOR RECIPROCITY DATA','SOURCE GAMMA ONE LOG DERIVATIVE RESIDUES').replace('Gamma One Divisor Reciprocity Data','Gamma One Log Derivative Residues')
output('SourceGammaOneLogDerivativeResiduesAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneDivisorReciprocityDataDependencyAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',cfg['scratchImportClosure']),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE LOG DERIVATIVE RESIDUES DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual original-divisor consumer. Native integration by parts, singular integrability, radial normalization, meromorphic local orders and the original cusp-form primitive are consumed. Modular reciprocity and full all-weight goal remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneLogDerivativeResiduesDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneDivisorReciprocityDataScratchOwnership860.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneLogDerivativeResiduesScratchOwnership869.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
paths=['complex-holomorphic-stokes-route-863.json','complex-cauchy-pompeiu-route-865.json','complex-residue-integral-route-866.json','complex-log-derivative-residues-route-867.json','gamma-one-log-derivative-residues-route-868.json']
rows=[];discharged=[]
for n in paths:
 f=p/n;rd=json.loads(f.read_text(encoding='utf-8'))
 rows.append(dict(path=str(f),sha256=sha(f)))
 rows.extend(rd['reuseChecked']);discharged.extend(rd['assumptionsToDischarge'])
prior=p/'source-gamma-one-invariant-untwist-1-scratch-receipt.json'
cert=json.loads(prior.read_text(encoding='utf-8'))
orig=next(x for x in cert['files'] if Path(x['path']).stem=='SourceWeightTwoPeriodUntwist')
assert sha(Path(orig['path']))==orig['sha256']
rows.append(dict(path=str(prior),sha256=sha(prior)))
local=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026\SourceComplexResidueSubtractedCoefficient.lean')
rows.append(dict(path=str(local),sha256=sha(local),review='Read exact existing finite-part helper. It fills the residue-subtracted function at one specified pole, whereas the present local-to-global formula regularizes all varying centers and proves finite exceptional support. It does not remove the remaining finite-support argument or integration step; no duplicate single-pole extension theorem was added.'))
route=dict(chain=['DUB-17/18','all-weight arithmetic association','original Gamma1 coefficient Hecke realization','Picard/H1','Abel-Jacobi converse','analytic reciprocity','actual original-divisor compact-support logarithmic residue integral'],reuseChecked=rows,assumptionsToDischarge=discharged,remaining='Actual F and its exact original-divisor orders remain explicit inputs. Modular winding/period/Petersson comparison, original principal-divisor converse and entire original all-weight arithmetic chain remain. No gate closed; 16/20; DUB-17--20 OPEN.')
output('source-gamma-one-log-derivative-residues-audit-route-869.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_divisor_reciprocity_data_860.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-divisor-reciprocity-data-1','source-gamma-one-log-derivative-residues-1'),('SourceGammaOneDivisorReciprocityData','SourceGammaOneLogDerivativeResidues'),('SOURCE GAMMA ONE DIVISOR RECIPROCITY DATA','SOURCE GAMMA ONE LOG DERIVATIVE RESIDUES'),('source-gamma-one-divisor-reciprocity-data-audit-route-860.json','source-gamma-one-log-derivative-residues-audit-route-869.json'),('(1, 4, 10)',str((len(mods),len(queries),len(required)))),('all 10 required',f'all {len(required)} required'),('requiredProofValueEdges=10',f'requiredProofValueEdges={len(required)}'),('modules=1, queries=4',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=10',f'proofEdges={len(required)}'),('== 1',f'== {len(mods)}'),('linterScopes=1',f'linterScopes={len(mods)}')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);output('record_source_gamma_one_log_derivative_residues_869.py',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))
