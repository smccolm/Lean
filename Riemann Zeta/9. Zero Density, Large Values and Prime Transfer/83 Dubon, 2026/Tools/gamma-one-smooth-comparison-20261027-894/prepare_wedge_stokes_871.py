from pathlib import Path
import json,hashlib
p=Path(__file__).parent
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.lean.txt'
t=src.read_text(encoding='utf-8-sig')
b=t[t.index("theorem integrable_mul_of_tsupport_subset'"):t.index('def D (')]
head="""import SourceComplexHolomorphicStokes

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> winding-period limit -> smooth comparison function
-> local logarithmic wedge identity -> compact-support wedge integration
by parts. The comparison function is only C1; requiring it to be meromorphic
would add a new obligation closely related to the desired divisor converse.
Native symmetry of the second derivative and integration by parts discharge
the smooth test-function identity; no Stokes conclusion is assumed. -/
namespace Dubon2026.SourceComplexReciprocity.Wedge
noncomputable section
open MeasureTheory Filter Complex Metric Set
open scoped Topology Real

"""
with (p/'SourceComplexWedgeStokes.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end\nend Dubon2026.SourceComplexReciprocity.Wedge\n')
r={'gate':'DUB-17/18','chain':['all-weight arithmetic association','original Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','winding-period limit','smooth comparison local models','local logarithmic wedge identity','compact-support wedge integration by parts'],'reuseChecked':[{'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest().upper(),'review':'Primary declarations, initial wedge proof, local logarithm/product/derivative lemmas and global assembly read. Disc calculation and local order isolation remain to inspect before adapting them. Existing holomorphic compact-support continuity/integrability reused, removing duplicated helpers. Native second-derivative symmetry and integration by parts used directly.'}],'assumptionsToDischarge':['C1 coefficient and compact C2 test function imply zero integral of exact derivative wedge'],'remaining':'Local logarithmic wedge identity, actual smooth comparison model, modular winding/period/Petersson comparison, original principal-divisor converse and full all-weight arithmetic chain remain. Generic meromorphic residue theorem cannot replace the smooth comparison-function step without an additional meromorphic realization assumption.'}
with (p/'complex-wedge-stokes-route-871.json').open('x',encoding='utf-8') as f:json.dump(r,f,indent=2)
