import TaoTrudgianYang2025.SargosQuarticMorseInverse
import TaoTrudgianYang2025.BetaMorseJets

/-! Exact derivatives of the polynomial inside the quartic quadratic coordinate. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosQuarticMorseCurvature (ε r u : ℝ) : ℝ :=
  2*sargosQuarticMorseCoefficient ε r u

theorem sargosQuarticMorseCurvature_contDiff (ε r : ℝ) :
    ContDiff ℝ ∞ (sargosQuarticMorseCurvature ε r) := by
  unfold sargosQuarticMorseCurvature sargosQuarticMorseCoefficient
  fun_prop

theorem sargosQuarticMorseCurvature_hasDerivAt (ε r u : ℝ) :
    HasDerivAt (sargosQuarticMorseCurvature ε r) (4*ε*(u+r)) u := by
  convert (sargosQuarticMorseCoefficient_hasDerivAt ε r u).const_mul 2 using 1
  ring

theorem sargosQuarticMorseCurvature_deriv (ε r : ℝ) :
    deriv (sargosQuarticMorseCurvature ε r) = fun u => 4*ε*(u+r) := by
  funext u
  exact (sargosQuarticMorseCurvature_hasDerivAt ε r u).deriv

theorem sargosQuarticMorseCurvature_deriv_two (ε r : ℝ) :
    deriv (fun u : ℝ => 4*ε*(u+r)) = fun _ => 4*ε := by
  funext u
  simpa only [mul_one] using (((hasDerivAt_id u).add_const r).const_mul (4*ε)).deriv

theorem sargosQuarticMorseCurvature_high_deriv (ε r u : ℝ) (n : ℕ) :
    iteratedDeriv (n+3) (sargosQuarticMorseCurvature ε r) u = 0 := by
  rw [show n+3 = (n+1)+1+1 by omega,iteratedDeriv_succ',
    sargosQuarticMorseCurvature_deriv,iteratedDeriv_succ',
    sargosQuarticMorseCurvature_deriv_two,iteratedDeriv_const]
  simp

end TaoTrudgianYang2025

