import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair
import Theorems.Thm_ModularCurve_periodMap_mem_parabolicHoms
import Theorems.Thm_ModularCurve_existsPeriodMapLinear
import P2M.Util
namespace P2MW.S_ModularCurve_range_periodHomPair_le_parabolicHoms

set_option autoImplicit false
open CongruenceSubgroup ModularCurve ModularCurve.Period
open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N] :
    LinearMap.range (ModularCurve.periodHomPair N)
      ≤ ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ := by
  obtain ⟨pml, hpml, hdef⟩ := periodHomPair_def N (existsPeriodMapLinear N)
  rintro _ ⟨fg, rfl⟩
  rw [hdef, LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.id_apply]
  have h1 : pml fg.1 ∈ parabolicHoms ℂ (Gamma0 N) ℂ := by rw [hpml]; exact periodMap_mem_parabolicHoms ℂ fg.1
  have h2 : pml fg.2 ∈ parabolicHoms ℂ (Gamma0 N) ℂ := by rw [hpml]; exact periodMap_mem_parabolicHoms ℂ fg.2
  exact add_mem (add_mem h1 (charInvolution_mem_parabolicHoms N ℂ ℂ h1))
    (sub_mem h2 (charInvolution_mem_parabolicHoms N ℂ ℂ h2))
