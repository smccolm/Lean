import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq

open UpperHalfPlane
open scoped MatrixGroups

theorem UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq
    (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (τ : ℍ) (n : ℤ)
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.solution
