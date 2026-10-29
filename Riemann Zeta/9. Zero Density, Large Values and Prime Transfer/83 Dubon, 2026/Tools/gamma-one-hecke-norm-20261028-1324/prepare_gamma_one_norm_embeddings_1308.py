from pathlib import Path
import re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
s=(r/'SourceOriginalHeckeNormEmbeddings.lean').read_text(encoding='utf-8')
s=s.replace('import Dubon2026.SourceOriginalHeckePrimeDegree', 'import SourceGammaOneHeckePrimeDegree')
s=s.replace('namespace Dubon2026.SourceFunctionField.HeckeNorm','namespace Dubon2026.SourceFunctionField.GammaOne.HeckeNorm')
s=s.replace('end Dubon2026.SourceFunctionField.HeckeNorm','end Dubon2026.SourceFunctionField.GammaOne.HeckeNorm')
s=re.sub(r'\bN\b','M',s)
s=s.replace('modularFunctionFieldOver M L','laurentBaseChange L (x1FunctionField M)')
s=s.replace('modularFunctionFieldOver (M * p) L','laurentBaseChange L (x1x0FunctionFieldC ℚ M (p * M))')
s=s.replace('originalHeckeAlpha','heckeAlpha').replace('originalHeckeBeta','heckeBeta')
s=s.replace('jOver M L','jCoordinateOver (CongruenceSubgroup.Gamma1 M) L')
s=s.replace('abbrev alphaAlgebra','def alphaAlgebra').replace('abbrev targetAlgebra','def targetAlgebra')
s=s.replace('attribute [local instance] alphaAlgebra', '''attribute [local instance] alphaAlgebra

/-- The module induced by the actual alpha algebra. -/
def alphaModule : Module FF GG := Algebra.toModule

attribute [local instance] alphaModule''')
old='(hback : ∀ x, w (heckeBeta L M p x) = heckeAlpha L M p x)'
new='(hjback : w (heckeBeta L M p (jCoordinateOver (CongruenceSubgroup.Gamma1 M) L)) =\n      heckeAlpha L M p (jCoordinateOver (CongruenceSubgroup.Gamma1 M) L))'
assert s.count(old)==1
s=s.replace(old,new).replace('embedding_succ_apply, hback,','embedding_succ_apply, hjback,')
a=s.index('/-!');b=s.index('-/',a)+2
s=s[:a]+'''/-! DUB-17/18 -> original Gamma1 Frobenius norm -> complete embeddings.
Adapt the native actual-field norm embeddings to the original Gamma1
correspondence. Only the proved forward equation and reverse j-coordinate
equation are used. No involution or reverse equation on arbitrary lower
elements is presumed. The native source credits anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/'''+s[b:]
out=p/'SourceGammaOneHeckeNormEmbeddings.lean'
assert not out.exists();out.write_text(s,encoding='utf-8')
s=(p/'compile_gamma_one_adjacent_j_coefficients_1307a.ps1').read_text(encoding='utf-8')
s=s.replace('SourceGammaOneAdjacentJCoefficients','SourceGammaOneHeckeNormEmbeddings').replace('1307a','1308a')
out=p/'compile_gamma_one_norm_embeddings_1308a.ps1'
assert not out.exists();out.write_text(s,encoding='utf-8')
print('Prepared actual Gamma1 norm embeddings; no audit or completion claim.')
