import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker

theorem PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (α : ℂˣ)
    (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
    (hψ : ∀ z : ℂ, L'.toPoint hL' ((α : ℂ) * z) = ψ (L.toPoint hL z)) :
    ∃ β : ℂˣ, ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = Nat.card ψ.ker := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.solution
