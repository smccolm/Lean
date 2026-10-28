import Mathlib
import Definitions.Def_HahnSeries_RamificationBound
import P2M.Util
import P2M.Sol.S_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq

theorem HahnSeries.hasRamBound_one_of_forall_ringEquiv_apply_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {x : HahnSeries ℚ K}
    (hx : ∀ σ : HahnSeries ℚ K ≃+* HahnSeries ℚ K,
      (∀ z : HahnSeries ℚ K, (σ z).orderTop = z.orderTop) →
      (∀ z : HahnSeries ℚ K, HahnSeries.HasRamBound 1 z → σ z = z) → σ x = x) :
    HahnSeries.HasRamBound 1 x := by p2m_exact_reverting @_root_.P2MW.S_HahnSeries_hasRamBound_one_of_forall_ringEquiv_apply_eq.solution
