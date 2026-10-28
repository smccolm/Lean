from pathlib import Path
import re
p=Path(r"E:\Lean\.tmp\dubon83")
f=p/'gamma-one-period-core-reuse-796/S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.lean.txt'
lines=f.read_text(encoding='utf-8').splitlines()
for mod,a,b,imports in [('SourceIntegralCharacterFreeProduct',290,348,['SourceIntegralCharacterShapiro']),('SourceIntegralCharacterInitialLift',350,412,['SourceIntegralCharacterFreeProduct'])]:
 body='\n'.join(lines[a-1:b])+'\n'
 body=body.replace('{? : Type*} {M : ? ? Type*}', '{? : Type} {M : ? ? Type}')
 docs={'genHom':'The factor homomorphism with its actual coboundary component.','totalHom':'The free-product homomorphism assembled from the factor coboundaries.','liftCrossed':'The actual crossed cocycle obtained from the free-product semidirect lift.'}
 for name,doc in docs.items():
  body=re.sub(r'(?m)^(def '+name+r'\b)',lambda m:'/-- '+doc+' -/\n'+m[1],body)
 header=''.join('import '+i+'\n' for i in imports)+'\n/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary\nmultiplier logarithms -> integral parabolic-character lifting. The actual\nfree-product universal property lifts a subgroup character that vanishes\non all conjugates of the finite factors. Adapted from the Apache-2.0\npinned primary integral-lift proof in scope 796, revision\n6e837e75355538c7f80bab5b956861e86c4eacc2. Native cosetTransition\nmultiplication is used through the scalar Shapiro construction. Parabolic\nvanishing is a separate correction obligation, not assumed proved here. -/\nnamespace Dubon2026.SourceIntegralCharacterLift\nnoncomputable section\n'
 with (p/(mod+'.lean')).open('x',encoding='utf-8',newline='\n') as out:out.write(header+body+'\nend\nend Dubon2026.SourceIntegralCharacterLift\n')
print('Prepared actual factor-cocycle lift and initial character realization.')
