from pathlib import Path
import ast
s=Path(__file__).parent
c=(s/'prepare_reduced_diamond_action_canonical_1700.py').read_text(encoding='utf-8')
for a,b in [('reduced-diamond-action','reduced-diamond-kernel'),('reduced_diamond_action','reduced_diamond_kernel'),('ReducedDiamondAction','ReducedDiamondKernel'),('REDUCED DIAMOND ACTION','REDUCED DIAMOND KERNEL'),('1694','1705'),('1700','1709')]:c=c.replace(a,b)
c=c.replace("adjacent=json.loads((s/'even-weight-integral-diamond-versions-1669.json').read_text(encoding='utf-8'))","adjacent=json.loads((s/'reduced-diamond-action-versions-1700.json').read_text(encoding='utf-8'))")
c=c.replace("'even-weight-integral-diamond-versions-1669.json']:","'even-weight-integral-diamond-versions-1669.json','reduced-diamond-action-versions-1700.json']:")
start=c.index("report='Dubon Original Reduced Diamond Action Assessment")
end=c.index("routeobj=dict",start)
c=c[:start]+'''report='Dubon Reduced Diamond Kernel and Fixed Field Assessment 2026-10-29.md'
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> finite homogeneous Gamma1 Hecke-character realization -> original degree/genus preservation -> signed-index lower bound -> actual reduced action, exact kernel and fixed-field degree.'
discharged=['Native degeneracy maps and the original integral j ratio put every divisor j expansion in the Gamma0 field, hence put the actual full modular base field in the original Gamma1 field.',
'Actual even integral Gamma0 ratios are fixed by the constructed diamond pullback. Adjoin extensionality proves fixation of the whole Gamma0 field and therefore of the actual full modular base field.',
'The actual integral Eisenstein separator transforms by the upper-left matrix entry. Its nonzero E4 denominator and first-coefficient separation identify every signed class at levels above two, in every coefficient characteristic. At levels one and two all Gamma0 matrices already lie in signed Gamma1.',
'The exact action kernel is signed Gamma1 inside Gamma0. Its finite index proves finiteness of the actual automorphism image; native Artin fixed-field theory gives its exact degree, equal to that signed relative index. No kernel, finiteness, fixation or degree premise remains in these consumers.']
remaining='The total signed-index lower bound still needs the full-base degree comparison and finite coordinate-degree transfer. Original degree/genus preservation, integral parabolic transfer, removal of the 3<p and fixed exceptional-prime restrictions, the required two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain open. Acceptance stays 16/20; DUB-17--20 OPEN, with every original criterion preserved.'
route='Reuse was checked in native SourceGammaOneHeckeFieldInclusion, SourceGammaOneIntegralJRatio, SourceGammaOneEisensteinSeparation and Mathlib fixed-field theory. The pinned Apache-2.0 source is anthropics/fermats-last-theorem at 6e837e75355538c7f80bab5b956861e86c4eacc2. Specializing its general GammaH argument to Gamma1 avoids coset-averaged forms and uses the already proved integral separators directly. Adjoin extensionality avoids a second construction of the fixed intermediate field.'
write(report,'# Reduced diamond kernel and fixed-field degree — 29 October 2026\\n\\n'+chain+'\\n\\n'+'\\n\\n'.join(discharged)+'\\n\\n'+route+'\\n\\nSix versioned modules pass all 17 public axiom queries, exhaustive private/generated theorem checks and sixteen linters each. All 31 required dependencies occur in declaration-value closures of the actual base inclusion/fixation, exact kernel and Artin degree consumers. The first value audit caught three incorrectly qualified Eisenstein declaration names; the corrected fresh audit verifies their actual GammaOne namespace. Mathematical statements and proofs were unchanged. Both audits are retained.\\n\\n'+remaining+'\\n\\nThis scope is scratch-audited; production promotion and assembled verification are pending. Frozen source, root pins, proof limits and the owner-only synchronization BAT remain unchanged.\\n')
refs=['anthropic-reduced-field-action-1662/manifest.json','source-reduced-diamond-action-1-scratch-receipt.json',report]
''' + c[end:]
c=c.replace('assert (nm,nq,ne)==(20,77,98)','assert (nm,nq,ne)==(6,17,31)')
ast.parse(c)
f=s/'prepare_reduced_diamond_kernel_canonical_1709.py';assert not f.exists();f.write_text(c,encoding='utf-8')
print('Prepared canonical kernel audit factory; 6 modules, 17 queries, 31 value dependencies.')
