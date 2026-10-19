import Dubon2026.LocalIntegralPrimeBelow

/-! Literal original field-action squares preserve the contracted prime and
its Frobenius action. These discharge the finite-prime action hypotheses of
the tame auxiliary deformation condition on the route to Dubon Theorem 2.6. -/

namespace Dubon2026

open scoped NumberField

attribute [local instance] algebraicLocalIntegerAction

variable {K L F : Type} [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L] [Field F] [NumberField F]
  (e : F →+* L) (σ : Gal(F/ℚ)) (δ : Gal(L/K))
  (he : ∀ x : F, e (σ x) = δ (e x))

include he

theorem algebraicLocalGlobalIntegerMap_smul (x : 𝓞 F) :
    algebraicLocalGlobalIntegerMap e (σ • x) = δ • algebraicLocalGlobalIntegerMap e x := by
  apply Subtype.ext
  exact he x.val

theorem algebraicLocalGlobalPrime_stable (x : 𝓞 F) (hx : x ∈ algebraicLocalGlobalPrime e) :
    σ • x ∈ algebraicLocalGlobalPrime e := by
  change IsLocalRing.residue (algebraicLocalIntegerRing L)
    (algebraicLocalGlobalIntegerMap e x) = 0 at hx
  change IsLocalRing.residue (algebraicLocalIntegerRing L)
    (algebraicLocalGlobalIntegerMap e (σ • x)) = 0
  rw [algebraicLocalGlobalIntegerMap_smul e σ δ he,
    IsLocalRing.ResidueField.residue_smul, hx, smul_zero]

theorem algebraicLocalGlobalPrime_frobenius (p : ℕ)
    (hδ : ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing L), δ • x = x ^ p)
    (x : 𝓞 F) : σ • x - x ^ p ∈ algebraicLocalGlobalPrime e := by
  change IsLocalRing.residue (algebraicLocalIntegerRing L)
    (algebraicLocalGlobalIntegerMap e (σ • x - x ^ p)) = 0
  rw [map_sub, map_sub, map_pow, map_pow,
    algebraicLocalGlobalIntegerMap_smul e σ δ he, IsLocalRing.ResidueField.residue_smul,
    hδ, sub_self]

end Dubon2026
