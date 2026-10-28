import Definitions.Def_ModularCurve_PeriodMapBundled
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Theorems.Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt
import P2M.Util
namespace P2MW.S_ModularCurve_periodMap_eq_periodHom

set_option autoImplicit false

open scoped MatrixGroups

theorem solution {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    {Fprim : UpperHalfPlane → ℂ} (hFprim : ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    ModularCurve.periodMap N f = hFprim.periodHom := by
  obtain ⟨F₁, hF₁⟩ := ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨F₀, h₀, h⟩ := ModularCurve.periodMap_def N f (F := F₁) hF₁
  rw [h]
  exact h₀.2.2.1.periodHom_eq_of_hasDerivAt hFprim h₀.1 hFf

#print axioms solution
