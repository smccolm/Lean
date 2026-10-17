import Dubon2026.OriginalCharacterFirstDuality

/-! # Rational-circle duality for original first homology

Pinned Mathlib proves injectivity and separation for rational-circle
characters. Combining these with the literal low-degree chain pairing
discharges both nondegeneracy assumptions without finite-cardinality
or abstract perfect-pairing certificates. DUB-17 still requires the
integral connecting-map and fundamental-class comparisons.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

local instance : Module.Injective ℤ (AddCircle (1 : ℚ)) :=
  (Module.Baer.of_divisible (AddCircle (1 : ℚ))).injective

variable {G : Type} [Group G] (M : Rep.{0} ℤ G)

/-- The actual rational-circle duality between first cohomology and characters of first homology. -/
def originalRationalCharacterFirstDuality :
    groupCohomology (originalLinearCharacterRep (AddCircle (1 : ℚ)) M) 1 ≃ₗ[ℤ]
      (groupHomology M 1 →ₗ[ℤ] AddCircle (1 : ℚ)) :=
  originalCharacterFirstDuality (AddCircle (1 : ℚ)) M

/-- Rational-circle cohomology characters separate the original first homology classes. -/
theorem originalRationalCharacterFirstDuality_right_nondegenerate
    (x : groupHomology M 1)
    (hx : ∀ c, originalRationalCharacterFirstDuality M c x = 0) : x = 0 := by
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  let f : groupHomology M 1 →ₗ[ℤ] AddCircle (1 : ℚ) :=
    { toFun := χ
      map_add' := χ.map_add
      map_smul' := fun r y =>
        (congrArg χ (int_smul_eq_zsmul (groupHomology M 1).isModule r y)).trans
          (map_zsmul χ r y) }
  obtain ⟨c, hc⟩ := (originalRationalCharacterFirstDuality M).surjective f
  have he := hx c
  rw [hc] at he
  exact he

/-- Evaluation on original first homology separates the original character-valued first cohomology classes. -/
theorem originalRationalCharacterFirstDuality_left_nondegenerate
    (c : groupCohomology (originalLinearCharacterRep (AddCircle (1 : ℚ)) M) 1)
    (hc : ∀ x, originalRationalCharacterFirstDuality M c x = 0) : c = 0 := by
  apply (originalRationalCharacterFirstDuality M).injective
  rw [map_zero]
  exact LinearMap.ext hc

/-- Rational-circle duality uses the literal original chain sum on cocycle and cycle representatives. -/
theorem originalRationalCharacterFirstDuality_representatives
    (c : groupCohomology.cocycles₁ (originalLinearCharacterRep (AddCircle (1 : ℚ)) M))
    (z : groupHomology.cycles₁ M) :
    originalRationalCharacterFirstDuality M
      (groupCohomology.H1π (originalLinearCharacterRep (AddCircle (1 : ℚ)) M) c)
      (groupHomology.H1π M z) =
        originalCharacterChainEvaluation (AddCircle (1 : ℚ)) M c.val z.val :=
  originalCharacterFirstDuality_representatives (AddCircle (1 : ℚ)) M c z

end
end Dubon2026
