import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair
import Theorems.Thm_ModularCurve_periodHomPair_injective
import Theorems.Thm_ModularCurve_range_periodHomPair_le_parabolicHoms
import Theorems.Thm_ModularCurve_Period_moduleFinite_addMonoidHom_gamma0_complex
import P2M.Util
namespace P2MW.S_ModularCurve_two_mul_finrank_cuspForm_le_finrank_parabolicHoms

set_option autoImplicit false
open CongruenceSubgroup ModularCurve ModularCurve.Period
open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N] :
    2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)
      ≤ Module.finrank ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ) := by
  haveI := ModularCurve.Period.moduleFinite_addMonoidHom_gamma0_complex N
  haveI : Module.Finite ℂ (CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) :=
    Module.Finite.of_injective (periodHomPair N) (periodHomPair_injective N)
  haveI : Module.Finite ℂ (CuspForm (Gamma0 N) 2) :=
    Module.Finite.of_injective (LinearMap.inl ℂ (CuspForm (Gamma0 N) 2) (CuspForm (Gamma0 N) 2)) LinearMap.inl_injective
  have hle := ModularCurve.range_periodHomPair_le_parabolicHoms N
  have hφ : Function.Injective ((periodHomPair N).codRestrict (parabolicHoms ℂ (Gamma0 N) ℂ)
      (fun x => hle ⟨x, rfl⟩)) := by
    intro x y h
    exact periodHomPair_injective N (congrArg Subtype.val h)
  calc 2 * Module.finrank ℂ (CuspForm (Gamma0 N) 2)
      = Module.finrank ℂ (CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) := by
        rw [Module.finrank_prod, two_mul]
    _ ≤ Module.finrank ℂ ↥(parabolicHoms ℂ (Gamma0 N) ℂ) := LinearMap.finrank_le_finrank_of_injective hφ
