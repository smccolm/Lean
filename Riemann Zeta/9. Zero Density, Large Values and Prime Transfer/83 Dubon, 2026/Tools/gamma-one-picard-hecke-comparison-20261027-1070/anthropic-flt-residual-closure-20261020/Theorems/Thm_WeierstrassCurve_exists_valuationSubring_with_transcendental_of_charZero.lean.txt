import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero

set_option autoImplicit false

open Polynomial WeierstrassCurve

universe u
theorem WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero
    (k : Type u) [Field k] [CharZero k] :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
      (A : ValuationSubring L) (φ : k →+* L) (hφ : ∀ x, φ x ∈ A)
      (ι : k →+* IsLocalRing.ResidueField A),
      (∀ a : k, IsLocalRing.residue A ⟨φ a, hφ a⟩ = ι a) ∧
      ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
        ∀ P : Polynomial k, P ≠ 0 → P.eval₂ φ t ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero.solution
