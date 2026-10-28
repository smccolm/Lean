from pathlib import Path
import hashlib,json
s=Path(__file__).parent
up=s/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.lean.txt'
t=up.read_text(encoding='utf-8-sig')
b=t[t.index('theorem continuous_mul_of_tsupport_subset'):t.index('end HolomorphicStokes')]
start=b.index('  refine continuous_iff_continuousAt.')
stop=b.index('\ntheorem integrable_mul_of_tsupport_subset')
b=b[:start]+"""  apply continuous_of_tsupport
  intro z hz
  exact (hf.continuousAt (hV.mem_nhds (hgV (tsupport_mul_subset_right _ _ hz)))).mul
    hg.continuousAt
"""+b[stop:]
b=b.replace('theorem main ', 'theorem integral_mul_dbar_eq_zero ')
head="""import Mathlib

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> logarithmic-derivative residue identity ->
holomorphic compact-support integration by parts. Adapted from the pinned
Anthropic FLT primary proof, with native support continuity replacing its
case split. No boundary identity or Stokes conclusion is assumed. -/
namespace Dubon2026.SourceComplexReciprocity
noncomputable section
open MeasureTheory Filter Complex Metric Set
open scoped Topology

"""
with (s/'SourceComplexHolomorphicStokes.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end\nend Dubon2026.SourceComplexReciprocity\n')
r={'gate':'DUB-17/18','chain':['all-weight arithmetic association','original Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','logarithmic-derivative residue identity','holomorphic compact-support integration by parts'],'reuseChecked':[{'path':str(up),'sha256':hashlib.sha256(up.read_bytes()).hexdigest().upper(),'review':'Full primary proof read. Native continuous_of_tsupport shortens its local-to-global support argument; native integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable supplies both real-coordinate integration-by-parts identities.'}],'assumptionsToDischarge':['holomorphic compact-support dbar integral vanishes, derived from holomorphicity and actual compact support'],'remaining':'Simple-pole kernel integral and finite residue decomposition, actual smoothed winding/period limit, Petersson reciprocity, principal-divisor converse and full arithmetic chain remain. This foundational lemma alone closes no DUB gate.'}
with (s/'complex-holomorphic-stokes-route-863.json').open('x',encoding='utf-8') as f:json.dump(r,f,indent=2)
