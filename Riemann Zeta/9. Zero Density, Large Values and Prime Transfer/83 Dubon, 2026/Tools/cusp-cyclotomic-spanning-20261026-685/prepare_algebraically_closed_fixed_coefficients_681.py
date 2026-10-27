from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'fricke-cusp-descent-inputs-reuse-678/P2M/Sol/S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range.lean.txt').read_text(encoding='utf-8')
imports=s[:s.index('import P2M.Util')]
start=s.index('open MvPolynomial Polynomial in')
end=s.index('theorem exists_intermediateField_isAlgebraic_notMem_of_isAlgebraic')
body=s[start:end]
head=imports+'''
/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> fixed-field descent of the proved twist-stable cusp image. An element of
a purely transcendental field that is algebraic over the original constants
belongs to those constants. This is the needed separation input for the
full complex automorphism fixed field, not an assumed Galois descent result.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range. -/
namespace Dubon2026.SourceFunctionField.ConstantFixedField
noncomputable section
open IntermediateField

'''
f=p/'SourcePureTranscendentalConstantIntersection.lean';assert not f.exists();f.write_text(head+body+'end\nend Dubon2026.SourceFunctionField.ConstantFixedField\n',encoding='utf-8')
print('Prepared the required constant-intersection proof using native fraction and polynomial results')