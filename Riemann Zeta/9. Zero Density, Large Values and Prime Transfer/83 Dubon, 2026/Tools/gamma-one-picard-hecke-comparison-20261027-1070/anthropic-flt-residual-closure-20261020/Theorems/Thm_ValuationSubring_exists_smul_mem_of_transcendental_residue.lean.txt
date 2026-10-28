import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_smul_mem_of_transcendental_residue

theorem ValuationSubring.exists_smul_mem_of_transcendental_residue
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (O : ValuationSubring F) (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (ρ : O →+* Fbar) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ a : A, ρ ⟨algebraMap L F a, (hO a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a))
    (f : F) (hf : f ∈ O)
    (htr : Transcendental (IsLocalRing.ResidueField A) (ρ ⟨f, hf⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (h : F) (hh : h ≠ 0) :
    ∃ c : L, ∃ hc : c • h ∈ O, ρ ⟨c • h, hc⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_smul_mem_of_transcendental_residue.solution
