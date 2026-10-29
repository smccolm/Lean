from pathlib import Path
import re
s=Path(__file__).parent
src=s/'anthropic-even-integrality-depth-1503/S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem.lean.txt'
t=src.read_text(encoding='utf-8');t=t[t.index('noncomputable def cInt'):t.index('end A2LevelOneCrit')]
a=t.index('theorem constantCoeff_eisenstein4');b=t.index('theorem constantCoeff_cInt',a)
t=t[:a]+t[b:]
t=t.replace('ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne','Dubon2026.SourceFunctionField.exists_levelOne_j_polynomial')
t=t.replace('ModularCurve.','Dubon2026.SourceFunctionField.')
t=t.replace('noncomputable def ','private def ')
t=re.sub(r'^theorem (?!main\b)','private theorem ',t,flags=re.M)
t=t.replace('theorem main (','theorem levelOne_coeff_mem_of_initial_coeff_mem (')
head='''import Dubon2026.SourceLevelOneJPolynomial

/-! DUB-17/18 -> original all-weight association -> Gamma1 degree
preservation -> even-weight slash integrality -> peaked auxiliary trace
argument. Its exact level-one coefficient step follows from the existing
native j-polynomial representation and the integral E4/Delta expansions.
Only the first N+1 coefficients of a weight-12N form are needed to derive
membership of every coefficient in the specified subring.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem.lean.
The original native polynomial theorem replaces the external dependency. -/
namespace Dubon2026.SourceFunctionField.LevelOneCoefficientRing
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

'''
out=s/'SourceLevelOneCoefficientRing1504a.lean';assert not out.exists()
out.write_text(head+t+'\nend\nend Dubon2026.SourceFunctionField.LevelOneCoefficientRing\n',encoding='utf-8')
print(out)
