import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card

theorem ValuationSubring.exists_sub_mem_nonunits_of_finrank_le_card
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (O : ValuationSubring F) {ι : Type*} [Fintype ι] (O' : ι → ValuationSubring F')
    (hinj : Function.Injective O') (hO' : ∀ i, (O' i).comap (algebraMap F F') = O)
    (hcard : Module.finrank F F' ≤ Fintype.card ι) (i : ι) (x : F') (hx : x ∈ O' i) :
    ∃ y ∈ O, x - algebraMap F F' y ∈ (O' i).nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card.solution
