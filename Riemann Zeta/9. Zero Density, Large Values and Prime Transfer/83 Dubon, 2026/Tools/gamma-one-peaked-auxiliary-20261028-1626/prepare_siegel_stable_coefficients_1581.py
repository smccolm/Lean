from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-siegel-dependencies-1553/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.lean.txt').read_text(encoding='utf-8')
body=t[t.index('def fac '):t.index('theorem map_fac ')]
body=body.replace('R[X]','ℂ[X]').replace('PowerSeries R','PowerSeries ℂ').replace('Polynomial.expand R','Polynomial.expand ℂ')
body=body.replace('def fac ', '/-- The actual expanded polynomial factor as a formal series. -/\ndef fac ',1)
body=body.replace('def pp ', '/-- The actual finite truncation of the source product. -/\ndef pp ',1)
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion'
f=s/'SourceSiegelStableCoefficients1581a.lean';assert not f.exists()
f.write_text('''import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> integral Siegel expansion.
Use stabilized coefficients of actual finite polynomial products. The
coefficient of degree m cannot change when factors of order > m are
appended. This is the necessary coefficient calculation for the native
local-uniform/Taylor route, not a general formal infinite-product theory.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun, with the
existing SourceDiscriminantProductExpansion analytic proof route. -/
namespace '''+ns+'''
noncomputable section
open Polynomial Filter Topology

'''+body+'''
/-- The stabilized coefficient of the actual finite product. -/
def stableCoeff (P : ℕ → ℂ[X]) (m : ℕ) : ℂ := (pp P m).coeff m

theorem stableCoeff_eq {P : ℕ → ℂ[X]} (hP : ∀ n, (P n).coeff 0 = 1)
    {m N : ℕ} (h : m ≤ N) : stableCoeff P m = (pp P N).coeff m :=
  (coeff_pp_stable hP h).symm

theorem stableCoeff_zero (P : ℕ → ℂ[X]) : stableCoeff P 0 = 1 := by
  rw [stableCoeff, pp_zero, Polynomial.coeff_one_zero]

theorem eval_pp (P : ℕ → ℂ[X]) (N : ℕ) (x : ℂ) :
    (pp P N).eval x = ∏ n ∈ Finset.range N, (P n).eval (x ^ (n + 1)) := by
  simp [pp, Polynomial.eval_prod, Polynomial.expand_eval]

end
end '''+ns+'\n',encoding='utf-8')
