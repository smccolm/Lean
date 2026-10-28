import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_LaurentSeries_exists_algHom_comp_map_eq_single

open HahnSeries
theorem LaurentSeries.exists_algHom_comp_map_eq_single {K F : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (φ : F →ₐ[K] LaurentSeries K) (f : F) (hf : 0 < (φ f).order) :
    ∃ φ' : F →ₐ[K] LaurentSeries K,
      (∀ x : F, (φ' x).order = (φ x).order) ∧ φ' f = single (φ f).order 1 := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_exists_algHom_comp_map_eq_single.solution
