import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top

theorem ValuationSubring.exists_valuation_mul_eq_one_of_forall_sup_eq_top
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (Q : ValuationSubring F) (S : Finset (ValuationSubring F'))
    (hS : ∀ P ∈ S, P.comap (algebraMap F F') = Q)
    {σ : Type*} [Fintype σ] (cls : σ → ValuationSubring F') (hcls : ∀ s, cls s ∈ S)
    (ω : σ → F') (hω : ∀ s, ω s ∈ cls s)
    (hind : ∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) → P.valuation (∑ s, algebraMap F F' (a s) * ω s) = 1)
    (hcard : Module.finrank F F' ≤ Fintype.card σ)
    (P₀ : ValuationSubring F') (hP₀ : P₀ ∈ S) (hindep : ∀ P ∈ S, P ≠ P₀ → P₀ ⊔ P = ⊤)
    (g : F') (hg : g ≠ 0) :
    ∃ h : F, P₀.valuation (algebraMap F F' h * g) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top.solution
