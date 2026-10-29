from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.lean.txt').read_text(encoding='utf-8')
body=t[t.index('def wt '):t.index('\nend Ws47.BSpan')]
body=body.replace('def wt ', '/-- The integer-normalized second Bernoulli weight determining the Siegel-product cusp order. -/\ndef wt ',1)
body=body.replace('noncomputable def cosZ ', '/-- The real cosine of the standard additive phase on the actual residue ring. -/\nnoncomputable def cosZ ',1)
f=s/'SourcePeakedBernoulliFourier1539a.lean';assert not f.exists()
f.write_text('''import Mathlib.NumberTheory.ZetaValues
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary form -> finite
Bernoulli-order separation. Reuse Mathlib's proved Bernoulli Fourier
series to express the literal integer-normalized weight. This is the
specific finite-dimensional spanning prerequisite of the source peak;
no auxiliary form or cusp-order separation is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.
The upstream raised heartbeat option is not adopted. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli
open Finset Real
open scoped Real

'''+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli\n',encoding='utf-8')
