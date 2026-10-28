from pathlib import Path
import json,hashlib
s=Path(__file__).parent
p=s/'gamma-one-reciprocity-reuse-848/S_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp_periodOf.lean.txt'
t=p.read_text(encoding='utf-8')
a=t.index('private theorem eventually_imInf_iff')
b=t.index('\nsection Automorphic',a)
body=t[a:b].replace('private theorem','theorem')
header="""import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> derivative decay of the invariant untwist.
Existing modular derivative bounds require global holomorphy. Here the
translated normalized function is holomorphic only above some height;
native Cauchy estimates on unit disks give the needed precise variant.
Adapted from the Apache-2.0 scope-848 untwisting primary at commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open Filter Complex Metric Set
open scoped Topology

"""
with (s/'SourceCuspDerivativeDecay.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(header+body+'\nend\nend Dubon2026.SourcePeriodUntwist\n')
route=json.loads((s/'gamma-one-cusp-untwist-route-853.json').read_text(encoding='utf-8'))
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026\SourceModularDerivativeCuspBounds.lean')
route['reuseChecked'].append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest().upper()))
route['shorterRoute']='Existing norm_deriv_le and isZeroAtImInfty_D require MDiff on the whole upper half-plane. Normalized meromorphic translates have poles below the cusp threshold, so those hypotheses do not apply. Adapt the exact eventual-holomorphy Cauchy estimate, using native Complex.norm_deriv_le_of_forall_mem_sphere_norm_le. Defer general derivative families and arbitrary domains.'
with (s/'gamma-one-cusp-derivative-route-854.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
print('Prepared eventual cusp-holomorphy derivative decay.')
