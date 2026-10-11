import Dubon2026.CommutativeHopfPointsCoefficientChange
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Finite geometric points of the actual finite free Hopf coordinate algebra -/

namespace Dubon2026
noncomputable section

variable {R A K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Module.Free R A] [Module.Finite R A] [Field K] [Algebra R K]

/-- A finite free original coordinate algebra has finitely many actual points in any field algebra. -/
theorem finiteFreeHopfPoints_finite : Finite (WithConv (A →ₐ[R] K)) :=
  Finite.of_injective WithConv.ofConv WithConv.ofConv_injective

/-- The number of genuine points is bounded by the rank of the same finite free coordinate algebra. -/
theorem finiteFreeHopfPoints_card_le :
    Nat.card (WithConv (A →ₐ[R] K)) ≤ Module.finrank R A := by
  rw [Nat.card_congr (WithConv.equiv (A →ₐ[R] K))]
  exact card_algHom_le_finrank R A K

/-- Cocommutativity of the same coordinate Hopf algebra makes the actual convolution point group commutative. -/
abbrev finiteFreeHopfPointsCommGroup [Coalgebra.IsCocomm R A] :
    CommGroup (WithConv (A →ₐ[R] K)) :=
  { commutativeHopfPointsGroup with mul_comm := mul_comm }

end
end Dubon2026
