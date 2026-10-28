import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_Module_End_exists_common_eigenvector_of_commute

theorem Module.End.exists_common_eigenvector_of_commute
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_common_eigenvector_of_commute.solution
