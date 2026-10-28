import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_valuationSubring_lift_with_transcendental

set_option autoImplicit false

universe u

theorem WittVector.exists_valuationSubring_lift_with_transcendental
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] [PerfectRing K p] :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
      (A : ValuationSubring L) (φ : WittVector p K →+* L) (hφ : ∀ x, φ x ∈ A)
      (ι : K →+* IsLocalRing.ResidueField A),
      (∀ a : K, IsLocalRing.residue A ⟨φ (WittVector.teichmuller p a), hφ _⟩ = ι a) ∧
      ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
        ∀ P : Polynomial (WittVector p K), P ≠ 0 → P.eval₂ φ t ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_valuationSubring_lift_with_transcendental.solution
