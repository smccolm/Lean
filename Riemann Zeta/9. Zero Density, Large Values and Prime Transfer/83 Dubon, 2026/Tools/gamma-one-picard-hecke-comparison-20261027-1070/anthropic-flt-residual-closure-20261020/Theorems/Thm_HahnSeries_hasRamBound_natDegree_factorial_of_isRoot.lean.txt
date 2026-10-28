import Mathlib
import Definitions.Def_HahnSeries_RamificationBound
import P2M.Util
import P2M.Sol.S_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot

theorem HahnSeries.hasRamBound_natDegree_factorial_of_isRoot
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {p : Polynomial (HahnSeries ℚ K)} (hp : p ≠ 0)
    (hcoeff : ∀ i : ℕ, HahnSeries.HasRamBound 1 (p.coeff i))
    {y : HahnSeries ℚ K} (hy : p.IsRoot y) :
    HahnSeries.HasRamBound p.natDegree.factorial y := by p2m_exact_reverting @_root_.P2MW.S_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot.solution
