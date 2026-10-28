import Mathlib

open Polynomial

namespace RamanujanPetersson

/--
Lean-generated witness form of the local characteristic-polynomial consequence in
Theorem 3.1 from the source note.

This does not construct Deligne's Galois representation. Instead, it formalizes the
safe algebraic consequence used later in the paper: once a rank-two witness matrix
has characteristic polynomial `X^2 - aₚ X + χ(p) p^(k-1)`, its trace and determinant
are exactly `aₚ` and `χ(p) p^(k-1)`.
-/
theorem theorem31_localCharpoly_witnessForm
    {ρFp : Matrix (Fin 2) (Fin 2) ℂ} {aₚ χp : ℂ} {p k N ℓ : ℕ}
    (hp : Nat.Prime p) (hpnmidN : ¬ p ∣ N) (hpneℓ : p ≠ ℓ)
    (hchar : ρFp.charpoly = X ^ 2 - C aₚ * X + C (χp * (p : ℂ) ^ (k - 1))) :
    ρFp.trace = aₚ ∧ ρFp.det = χp * (p : ℂ) ^ (k - 1) := by
  let _ := hp
  let _ := hpnmidN
  let _ := hpneℓ
  let b : ℂ := χp * (p : ℂ) ^ (k - 1)
  have hchar' : ρFp.charpoly = X ^ 2 - C aₚ * X + C b := by
    simpa [b] using hchar
  have hM := Matrix.charpoly_fin_two ρFp
  have hEq : X ^ 2 - C ρFp.trace * X + C ρFp.det = X ^ 2 - C aₚ * X + C b := by
    exact hM.symm.trans hchar'
  have hcoeff1 := congrArg (fun q => q.coeff 1) hEq
  have hcoeff0 := congrArg (fun q => q.coeff 0) hEq
  simp at hcoeff1 hcoeff0
  simpa [b] using And.intro hcoeff1 hcoeff0

end RamanujanPetersson
