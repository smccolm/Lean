from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceModularEllipticFixedPoint','SourceMeromorphicMultiplierParabolic','SourceMeromorphicMultiplierGerm','SourceGammaOneMeromorphicMultiplierElliptic','SourceGammaOneMeromorphicMultiplierPeriods']
s=(p/'prepare_integral_parabolic_character_lift_audit_830.py').read_text(encoding='utf-8')
exec(s[s.index('ths=[];defs=[]'):s.index("queries=ths+defs;ns=")])
queries=ths+defs
old=json.loads((p/'source-gamma-one-unitary-character-periods-1c-audit-config.json').read_text(encoding='utf-8'))
required=old['proofEdges']+[n for n in ths if not n.endswith('.multiplier_one')]
required+=['UpperHalfPlane.fixedPt','UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt','Dubon2026.SourceParabolic.classification']
required+=['Dubon2026.SourceFunctionField.SubgroupStabilizer.'+n for n in ['moeb','moeb_sub','continuousAt_moeb','continuous_denom','chi']]
required+=['Dubon2026.SourceFunctionField.GammaOne.two_mul_ramification_eq_stabilizer_card','meromorphicOrderAt_eq_int_iff']
required=list(dict.fromkeys(required))
roots=['Dubon2026.sourceGamma1_meromorphic_multiplier_eq_exp_real_period'];closure=mods+old['scratchImportClosure']
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=[q for q in queries if q not in required],separateReason='All public declarations are axiom checked. The unused multiplier_one normalization helper is separately checked; required substantive dependencies must occur in the VALUE closure of the actual original-divisor meromorphic-multiplier consumer.')
output('source-gamma-one-meromorphic-multiplier-periods-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneUnitaryCharacterPeriodsAudit1c.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE UNITARY CHARACTER PERIODS','SOURCE GAMMA ONE MEROMORPHIC MULTIPLIER PERIODS').replace('Gamma One Unitary Character Periods','Gamma One Meromorphic Multiplier Periods')
output('SourceGammaOneMeromorphicMultiplierPeriodsAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneUnitaryCharacterPeriodsDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE MEROMORPHIC MULTIPLIER PERIODS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the original Gamma1 divisor and meromorphic-multiplier consumer. Native elliptic fixed points, the existing Mobius germs, signed stabilizer ramification, actual integral lifting, unitary logarithms and original real-period surjectivity are consumed. Analytic reciprocity, meromorphic construction from periods and full arithmetic association remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneMeromorphicMultiplierPeriodsDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneUnitaryCharacterPeriodsScratchOwnership840.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def inspectOwnership'):];b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneMeromorphicMultiplierPeriodsScratchOwnership846.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
f=p/'gamma-one-meromorphic-multiplier-route-841.json';rd=json.loads(f.read_text(encoding='utf-8'));rd['reuseChecked']+=[dict(path=str(f),sha256=sha(f))]
rd['assumptionsToDischarge']='A unitary multiplier of an actual meromorphic function, with prescribed original Gamma1 divisor orders and nonzero limits at every translated cusp, is realized by actual weight-two cusp-form real periods. Multiplicativity is derived from a nonzero cusp limit; elliptic triviality consumes actual finite germ orders and the exact signed stabilizer formula; parabolic triviality consumes signed translation classification and cusp limits. No character law, triviality, logarithm or cusp-form-realization premise remains.'
rd['remaining']='Construct the actual meromorphic function from the original Abel-Jacobi condition; prove analytic reciprocity; finish original Picard/H1/Hecke/diamond/full-parabolic/transpose comparison and original all-weight arithmetic association. 16/20; DUB-17--20 OPEN.'
output('source-gamma-one-meromorphic-multiplier-periods-audit-route-846.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_source_gamma_one_unitary_character_periods_840c.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-unitary-character-periods-1c','source-gamma-one-meromorphic-multiplier-periods-1'),('SourceGammaOneUnitaryCharacterPeriods','SourceGammaOneMeromorphicMultiplierPeriods'),('PeriodsAudit1c.log','PeriodsAudit1.log'),('SOURCE GAMMA ONE UNITARY CHARACTER PERIODS','SOURCE GAMMA ONE MEROMORPHIC MULTIPLIER PERIODS'),('source-gamma-one-unitary-character-periods-audit-route-840.json','source-gamma-one-meromorphic-multiplier-periods-audit-route-846.json'),('(9, 30, 83)',str((len(mods),len(queries),len(required)))),('all 83 required',f'all {len(required)} required'),('requiredProofValueEdges=83',f'requiredProofValueEdges={len(required)}'),('modules=9, queries=30',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=83',f'proofEdges={len(required)}'),('== 9','== 5'),('linterScopes=9','linterScopes=5')]:
 assert a in s,a
 s=s.replace(a,b)
ast.parse(s);output('record_source_gamma_one_meromorphic_multiplier_periods_846.py',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),edges=len(required))))
