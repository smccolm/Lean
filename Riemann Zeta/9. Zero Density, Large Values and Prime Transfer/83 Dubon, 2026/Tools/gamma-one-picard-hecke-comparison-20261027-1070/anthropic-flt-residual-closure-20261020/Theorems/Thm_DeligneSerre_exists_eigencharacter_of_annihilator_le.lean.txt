import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_DeligneSerre_exists_eigencharacter_of_annihilator_le

theorem DeligneSerre.exists_eigencharacter_of_annihilator_le
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T ℂ V] [Module.Finite ℤ T]
    (𝔪 : Ideal T) [h𝔪 : 𝔪.IsMaximal] (hsupp : Module.annihilator T V ≤ 𝔪) :
    ∃ (χ : T →+* integralClosure ℤ ℂ) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      𝔪'.IsMaximal ∧ 𝔪'.comap χ = 𝔪 ∧
      ∃ x : V, x ≠ 0 ∧ ∀ t : T, t • x = ((χ t : integralClosure ℤ ℂ) : ℂ) • x := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_exists_eigencharacter_of_annihilator_le.solution
