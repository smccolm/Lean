import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card

theorem ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (O : ValuationSubring F) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F')
    (hinj : Function.Injective O') (hO' : ∀ i, (O' i).comap (algebraMap F F') = O)
    (hcard : Module.finrank F F' ≤ Fintype.card ι) (i : ι) (g : F') (hg : g ≠ 0) :
    ∃ h : F, (O' i).valuation (algebraMap F F' h * g) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card.solution
