import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import P2M.Util
import P2M.Sol.S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul

theorem DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.solution
