import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_transcendental_j_perturb

set_option autoImplicit false

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.transcendental_j_perturb
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {L : Type*} [Field L] [CharZero L]
    (φ : R →+* L) (t : L) (ht : ∀ P : Polynomial R, P ≠ 0 → P.eval₂ φ t ≠ 0)
    (W : WeierstrassCurve R) :
    ∃ hΔ : (⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ : WeierstrassCurve L).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _
        (⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ : WeierstrassCurve L)
        ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_transcendental_j_perturb.solution
