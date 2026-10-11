import Dubon2026.HopfPointsVanishingIdeal
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Antipode and counit stability of the genuine subgroup vanishing ideal -/

namespace Dubon2026
noncomputable section

variable {R A K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing K] [Algebra R K]

/-- The original Hopf point group used by the subgroup vanishing argument. -/
local instance hopfSubgroupPointGroup : Group (WithConv (A →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- The actual subgroup vanishing ideal is stable under the original coordinate antipode because the same subgroup is closed under point inversion. -/
theorem hopfSubgroupVanishingIdeal_antipode
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (a : A) (ha : a ∈ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) :
    HopfAlgebra.antipode R a ∈ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) := by
  apply (hopfPointsVanishingIdeal_mem_iff _ _).mpr
  intro p
  have h := (hopfPointsVanishingIdeal_mem_iff _ _).mp ha ⟨p.val⁻¹, X.inv_mem p.property⟩
  exact h

/-- Every coordinate vanishing on the genuine subgroup has zero counit when the base ring embeds in the point-value ring. The identity point supplies this conclusion. -/
theorem hopfSubgroupVanishingIdeal_counit
    (hinj : Function.Injective (algebraMap R K))
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (a : A) (ha : a ∈ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) :
    Coalgebra.counit (R := R) a = 0 := by
  have h := (hopfPointsVanishingIdeal_mem_iff _ _).mp ha ⟨1, X.one_mem⟩
  apply hinj
  exact h.trans (map_zero (algebraMap R K)).symm

end
end Dubon2026
