from pathlib import Path
import shutil,json
s=Path(__file__).parent
d=s/'untwist-decay-failed-855a';d.mkdir()
for ext in ['lean','log','exit']:shutil.copyfile(s/('SourceMeromorphicUntwistDecay.'+ext),d/('SourceMeromorphicUntwistDecay.'+('lean.txt' if ext=='lean' else ext)))
p=s/'SourceMeromorphicUntwistDecay.lean';t=p.read_text(encoding='utf-8')
a='simp [Complex.norm_real, Real.pi_pos.le, abs_of_pos Real.pi_pos]'
assert a in t;p.write_text(t.replace(a,'simp [Complex.norm_real, abs_of_pos Real.pi_pos]'),encoding='utf-8')
primary=s/'gamma-one-reciprocity-reuse-848/S_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp_periodOf.lean.txt'
t=primary.read_text(encoding='utf-8')
a=t.index('private theorem countable_bad')
b=t.index('\ninclude hF hχ hcusp in',a)
body=t[a:b].replace('private theorem','theorem').replace('include hF hcusp in','include hF hfinite in').replace('countable_bad F hF hcusp','countable_bad F hF hfinite').replace('reg (FC F)','reg F')
a='    obtain ⟨m, hm⟩ := ModularCurve.exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty F hF hcusp τ\n    obtain ⟨-, -, -, -, -, hgood⟩ := reg_normal_form (FC F) (hF τ) hm'
b='    obtain ⟨m, hm⟩ := hfinite τ\n    have hmer : MeromorphicOn (F ∘ ofComplex) upperHalfPlaneSet := fun z hz => hF ⟨z, hz⟩\n    have hgood := normalized_eventually_regular isOpen_upperHalfPlaneSet hmer τ.im_pos hm'
assert a in body;body=body.replace(a,b)
header=r"""import SourceMeromorphicUntwistDecay
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> the almost-everywhere logarithmic derivative
identity of the actual invariant untwist. Native normalized local forms
give a countable exceptional set. Prescribed original divisor orders
supply the finite-order input in the assembled Gamma1 consumer.
Adapted from the pinned Apache-2.0 scope-848 untwisting source. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open UpperHalfPlane Filter MeasureTheory Matrix.SpecialLinearGroup Set
open scoped MatrixGroups Topology

/-- Points where the original meromorphic germ is analytic and nonzero. -/
def Good (F : ℍ → ℂ) (z : ℂ) : Prop :=
  ((F ∘ ofComplex) =ᶠ[𝓝 z] reg F) ∧ AnalyticAt ℂ (reg F) z ∧ reg F z ≠ 0

variable (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
  (hfinite : ∀ τ : ℍ, ∃ n : ℤ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) = (n : WithTop ℤ))

include hF hfinite in
"""
a=body.index('include hF hfinite in')
body=body[:a]+r"""variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
  (k : CuspForm (Γ.map (mapGL ℝ)) 2)

"""+body[a:]
with (s/'SourceMeromorphicUntwistDerivative.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(header+body+'\nend\nend Dubon2026.SourcePeriodUntwist\n')
route=json.loads((s/'gamma-one-untwist-decay-route-855.json').read_text(encoding='utf-8'))
route['shorterRoute']='Native normalized local forms replace the custom regularization proof in the countable-exception argument. Differentiate the actual normalized function times the actual real-period exponential. The assembled original-divisor consumer will discharge finite local order using its literal ramification-weighted divisor equality.'
with (s/'gamma-one-untwist-derivative-route-856.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
print('Prepared exact almost-everywhere derivative identity; preserved and fixed one unused simp diagnostic.')
