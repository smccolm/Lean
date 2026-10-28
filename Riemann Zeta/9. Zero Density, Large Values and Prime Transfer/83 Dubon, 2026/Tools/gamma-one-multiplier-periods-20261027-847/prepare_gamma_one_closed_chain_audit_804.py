from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceWeightTwoEndpointPeriods','SourceWeightTwoIntegralPeriods','SourceWeightTwoClosedChainPeriods','SourceWeightTwoSegmentPeriods','SourceGammaOneClosedChainIntegral']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 code=re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S)
 for kind,n in re.findall(r'^(theorem|def|abbrev) ([\w.]+)',code,re.M):
  (ths if kind=='theorem' else defs).append('Dubon2026.'+n)
queries=ths+defs
required=queries+['Dubon2026.sourceWeightTwoPrimitive_period','Dubon2026.sourceWeightTwoPrimitive_hasDerivAt','Dubon2026.sourceWeightTwoPeriodValue_apply','Dubon2026.SourceFunctionField.OriginalPrimitiveGlue.eventually_sub_eq_of_hasDerivAt']
assert (len(mods),len(ths),len(defs),len(required))==(5,15,5,24)
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=mods,separateReason='Actual original Gamma1 closed integer-chain segment integrals lie in the original modular-period integer lattice. Integral character lifting and analytic reciprocity remain.')
output('source-gamma-one-closed-chain-periods-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE CLOSED CHAIN PERIODS').replace('Gamma One Exact Ramification','Gamma One Closed Chain Periods')
output('SourceGammaOneClosedChainPeriodsAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE CLOSED CHAIN PERIODS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual original Gamma1 closed-chain segment integrals, integer modular periods, native primitive derivatives and transformation. Only declaration values are traversed. Integral character lifting, analytic reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneClosedChainPeriodsDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((p/'gamma-one-closed-chain-route-797.json').read_text(encoding='utf-8'))
rd=dict(chain=old['chain'],assumptionsToDischarge='For every nonzero level, an actual finite integer chain with zero orbit boundary has its literal straight-segment integrals of original Gamma1 weight-two cusp forms represented by an element of the integer span of the original scalar modular periods. Derive primitive linearity, exact subgroup shifts, orbit-quotient descent and the segment FTC normalization; no period-lattice inclusion or analytic normalization is assumed. The zero-boundary condition remains the source condition, not an assumed conclusion.',remaining='Promote and run assembled verification. Integral parabolic-character lifting, analytic reciprocity and meromorphic construction from Abel-Jacobi periods, Picard/Hecke/diamond/H1, all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=old['reuseChecked']+[dict(path=str(p/'gamma-one-closed-chain-route-797.json'),sha256=sha(p/'gamma-one-closed-chain-route-797.json'))],shorterRoute='The pinned external proof expands orbit representatives. Evaluate the pushed finite-chain boundary directly in the quotient by the actual period lattice using existing Finsupp.mapDomain, avoiding extra representatives and summation infrastructure. Reuse local primitive uniqueness and original period transformation. Prove the literal straight-segment normalization by interval FTC.')
output('gamma-one-closed-chain-audit-route-804.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_real_period_surjectivity_793.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-real-period-surjectivity-1','source-gamma-one-closed-chain-periods-1'),('SourceGammaOneRealPeriodSurjectivity','SourceGammaOneClosedChainPeriods'),('SOURCE GAMMA ONE REAL PERIOD SURJECTIVITY','SOURCE GAMMA ONE CLOSED CHAIN PERIODS'),('gamma-one-real-period-surjectivity-audit-route-793.json','gamma-one-closed-chain-audit-route-804.json'),('(3, 19, 32)','(5, 20, 24)'),('all 32 required','all 24 required'),('requiredProofValueEdges=32','requiredProofValueEdges=24'),('modules=3, queries=19','modules=5, queries=20'),('proofEdges=32','proofEdges=24'),('== 3','== 5'),('linterScopes=3','linterScopes=5')]:
 assert a in s,a
 s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_closed_chain_periods_804.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneClosedChainPeriodsScratchOwnership804.lean',s)
print(json.dumps(dict(modules=5,queries=20,edges=24)))
