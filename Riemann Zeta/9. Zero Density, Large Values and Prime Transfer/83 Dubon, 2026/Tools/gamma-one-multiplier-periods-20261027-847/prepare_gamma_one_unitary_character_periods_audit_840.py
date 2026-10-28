from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceUnitaryCharacter'+s for s in ['FiniteOrder','Recurrence','TraceBound','AbelianQuotient','BasisExt','Torsion']]+['SourceUnitaryCircleCharacter','SourceUnitaryCharacterLogarithm','SourceGammaOneUnitaryCharacterPeriods']
s=(p/'prepare_integral_parabolic_character_lift_audit_830.py').read_text(encoding='utf-8')
exec(s[s.index('ths=[];defs=[]'):s.index("queries=ths+defs;ns=")])
queries=ths+defs;ns='Dubon2026.SourceUnitaryCharacterLift.'
old=json.loads((p/'source-integral-parabolic-character-lift-1-audit-config.json').read_text(encoding='utf-8'))
required=[n for n in old['proofEdges'] if n!='Dubon2026.sourceGamma1_integral_parabolic_character_lift']
required += [ns+n for n in ['mul_self_eq_trace_smul_sub_one','pow_twelve_eq_one','cheb','pow_succ_eq_cheb','abs_cheb_succ_ge','cheb_ne_zero','trace_sq_le_four_of_isOfFinOrder','piM_surjective','piA_surjective','piM_eq_one','piA_eq_zero','desc','descA','fg_SL2Z','fgQ','hom_ext_of_basis','torsion_exponent_eq_zero','unitChar','exists_real_logarithm']]
required += ['Matrix.aeval_self_charpoly','Matrix.charpoly_fin_two','AddCommGroup.equiv_free_prod_directSum_zmod','Circle.exp_surjective','Dubon2026.sourceGamma1_exists_cuspForm_of_real_parabolic_character','Dubon2026.sourceGamma1RealParabolicPeriodHom_surjective','Dubon2026.sourceGamma1_unitary_character_eq_exp_real_period']
roots=['Dubon2026.sourceGamma1_unitary_character_eq_exp_real_period'];closure=mods+old['scratchImportClosure']
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=[q for q in queries if q not in required],separateReason='Every public declaration is individually axiom checked. Required dependencies must occur in the VALUE closure of the actual Gamma1 unitary-character period representation; the earlier Gamma1 integer-lift wrapper is separately audited while its general theorem is consumed directly.')
output('source-gamma-one-unitary-character-periods-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceIntegralParabolicCharacterLiftAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE INTEGRAL PARABOLIC CHARACTER LIFT','SOURCE GAMMA ONE UNITARY CHARACTER PERIODS').replace('Integral Parabolic Character Lift','Gamma One Unitary Character Periods')
output('SourceGammaOneUnitaryCharacterPeriodsAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceIntegralParabolicCharacterLiftDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE UNITARY CHARACTER PERIODS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual Gamma1 unitary-character period representation. Native Cayley-Hamilton, finite abelian decomposition, actual integral parabolic lifting, torsion elimination, circle logarithms and actual Gamma1 real-period surjectivity are consumed. Triviality of the actual meromorphic multiplier, analytic reciprocity and full arithmetic association remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneUnitaryCharacterPeriodsDependencyAudit1.lean',imports+b)
t=(p/'SourceIntegralParabolicCharacterLiftScratchOwnership830.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def inspectOwnership'):];b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneUnitaryCharacterPeriodsScratchOwnership840.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
f=p/'gamma-one-unitary-logarithm-route-831.json';rd=json.loads(f.read_text(encoding='utf-8'));rd['reuseChecked']+=[dict(path=str(f),sha256=sha(f))]
rd['assumptionsToDischarge']='Every actual Gamma1 unitary character trivial on squared trace at most four is the exponential of the real periods of an actual weight-two cusp form, at every nonzero level. The real logarithm and torsion-free quotient are derived using the proved integral parabolic lift, native finite abelian decomposition and the actual real-period surjectivity. No logarithm, torsion-free quotient, basis or cusp-form realization hypothesis remains.'
rd['remaining']='Derive multiplicativity and elliptic/parabolic triviality for the actual meromorphic multiplier with the original Gamma1 central-stabilizer normalization; analytic reciprocity, Abel-Jacobi and original all-weight arithmetic association remain. 16/20; DUB-17--20 OPEN.'
output('source-gamma-one-unitary-character-periods-audit-route-840.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_source_integral_parabolic_character_lift_830.py').read_text(encoding='utf-8-sig')
for a,b in [('source-integral-parabolic-character-lift-1','source-gamma-one-unitary-character-periods-1'),('SourceIntegralParabolicCharacterLift','SourceGammaOneUnitaryCharacterPeriods'),('SOURCE INTEGRAL PARABOLIC CHARACTER LIFT','SOURCE GAMMA ONE UNITARY CHARACTER PERIODS'),('source-integral-parabolic-character-lift-audit-route-830.json','source-gamma-one-unitary-character-periods-audit-route-840.json'),('(12, 77, 58)',str((len(mods),len(queries),len(required)))),('all 58 required',f'all {len(required)} required'),('requiredProofValueEdges=58',f'requiredProofValueEdges={len(required)}'),('modules=12, queries=77',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=58',f'proofEdges={len(required)}'),('== 12','== 9'),('linterScopes=12','linterScopes=9')]:
 assert a in s,a
 s=s.replace(a,b)
ast.parse(s);output('record_source_gamma_one_unitary_character_periods_840.py',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),edges=len(required))))
