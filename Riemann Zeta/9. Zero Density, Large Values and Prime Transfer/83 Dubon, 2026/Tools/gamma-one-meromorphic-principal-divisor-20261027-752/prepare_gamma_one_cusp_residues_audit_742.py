from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
r=Path(r"E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026")
mods=['SourceGammaOneCuspResidues'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['cuspPlace_mem_iff','cuspRealize_sub_constant_eventuallyEq','cuspPlace_order_eq_zero_of_tendsto','cuspRealize_tendsto_residue','regular_cusp_analytic_representative']]
required=ths+[ns+n for n in ['cuspPlace_order','cuspRamification_pos','meromorphicAt_cuspRealize','place_residue_bijective']]+['Dubon2026.SourceCurve.Place.rationalEval_eq_zero_iff_ord_pos']
assert len(required)==10
f=p/(mods[0]+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=ths,separatelyAxiomChecked=[],scratchImportClosure=mods,separateReason='The actual cusp-place limit and residue comparison is proved; exhaustion of j-pole places remains separate.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-cusp-residues-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports='import SourceGammaOneCuspResidues\nimport Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE CUSP RESIDUES').replace('Gamma One Exact Ramification','Gamma One Cusp Residues')
output('SourceGammaOneCuspResiduesAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+b+'#lint in SourceGammaOneCuspResidues\n')
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',ths),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE CUSP RESIDUES DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual cusp-place residue limits and normalized zero-order control. Only declaration values are traversed. Exhaustion of j-pole places, global periods, arithmetic association and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneCuspResiduesDependencyAudit1.lean',imports+b)
rd=json.loads((p/'gamma-one-cusp-residues-route-742.json').read_text());rd['chain']=rd['dependency'];rd['assumptionsToDischarge']=rd['intendedDischarge'];rd['reuseAssessment']=rd['reuseChecked']
files=[r/n for n in ['SourceGammaOneAnalyticResidues.lean','SourceGammaOneCuspPlaces.lean','SourceGammaOneCuspRealizationAlgebra.lean']]
files.append(Path(r"E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib\Analysis\Meromorphic\Order.lean"))
rd['reuseChecked']=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in files]
output('gamma-one-cusp-residues-audit-route-742.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_exact_ramification_731.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-exact-ramification-1','source-gamma-one-cusp-residues-1'),('SourceGammaOneExactRamificationAudit1','SourceGammaOneCuspResiduesAudit1'),('SourceGammaOneExactRamificationDependencyAudit1','SourceGammaOneCuspResiduesDependencyAudit1'),('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE CUSP RESIDUES'),('gamma-one-exact-ramification-audit-route-731.json','gamma-one-cusp-residues-audit-route-742.json'),('(1, 3, 10)','(1, 5, 10)'),('modules=1, queries=3','modules=1, queries=5')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_cusp_residues_742.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8').replace('SourceGammaOneExactRamification','SourceGammaOneCuspResidues')
output('SourceGammaOneCuspResiduesScratchOwnership742.lean',s)
print(json.dumps(dict(modules=1,queries=5,edges=10)))
