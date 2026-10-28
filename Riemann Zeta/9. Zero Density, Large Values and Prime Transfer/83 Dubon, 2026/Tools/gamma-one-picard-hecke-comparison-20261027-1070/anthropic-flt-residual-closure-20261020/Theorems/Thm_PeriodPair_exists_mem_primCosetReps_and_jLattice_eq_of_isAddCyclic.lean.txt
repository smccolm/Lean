import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic

open UpperHalfPlane
theorem PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
    {N : ℕ} [NeZero N] (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    ∃ (a b d : ℕ) (τ σ : ℍ), (a, b, d) ∈ ModularCurve.primCosetReps N ∧
      (σ : ℂ) = ((a : ℂ) * τ + b) / d ∧
      L.jLattice = (PeriodPair.ofTau τ).jLattice ∧ L'.jLattice = (PeriodPair.ofTau σ).jLattice := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.solution
