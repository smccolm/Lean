import Dubon2026.OriginalRationalCharacterSequence
import Dubon2026.FiniteFirstCohomologySylowDetection
import Dubon2026.FiniteSecondCohomologySylowDetection

/-! # Vanishing of the actual rational Hom coefficient in degrees one and two

DUB-17's integral duality needs the connecting map for the literal
integer/rational/character sequence to be an isomorphism. Scaling by
the reciprocal group order and the already proved group-order
annihilation discharge its two rational cohomology assumptions.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (M : Rep.{0} ℤ G)

/-- Actual rational scaling of the original rational-valued character coefficient. -/
def originalRationalHomScalar (r : ℚ) :
    originalLinearCharacterRep ℚ M ⟶ originalLinearCharacterRep ℚ M :=
  Rep.ofHom ⟨r • (LinearMap.id : (M →ₗ[ℤ] ℚ) →ₗ[ℤ] (M →ₗ[ℤ] ℚ)), fun _ => by
    ext φ x
    rfl⟩

/-- Reciprocal integer scaling is a literal division map on the original rational Hom coefficient. -/
theorem originalRationalHomScalar_division (n : ℕ) (hn : n ≠ 0) :
    n • originalRationalHomScalar M (n : ℚ)⁻¹ = 𝟙 (originalLinearCharacterRep ℚ M) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro φ
  change M →ₗ[ℤ] ℚ at φ
  apply LinearMap.ext
  intro x
  rw [Rep.nsmul_hom]
  change n • ((n : ℚ)⁻¹ * φ x) = φ x
  rw [nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn), one_mul]

private theorem originalRationalHomCohomology_zero_of_annihilation
    (i n : ℕ) (hn : n ≠ 0)
    (h : ∀ x : groupCohomology (originalLinearCharacterRep ℚ M) i, n • x = 0) :
    Limits.IsZero (groupCohomology (originalLinearCharacterRep ℚ M) i) := by
  have hm : n • (groupCohomology.functor ℤ G i).map
      (originalRationalHomScalar M (n : ℚ)⁻¹) =
        𝟙 (groupCohomology (originalLinearCharacterRep ℚ M) i) := by
    rw [← Functor.map_nsmul, originalRationalHomScalar_division M n hn,
      CategoryTheory.Functor.map_id]
    rfl
  have hz (x : groupCohomology (originalLinearCharacterRep ℚ M) i) : x = 0 := by
    have he := congrArg (fun f : groupCohomology (originalLinearCharacterRep ℚ M) i ⟶
        groupCohomology (originalLinearCharacterRep ℚ M) i => f x) hm
    exact he.symm.trans (h _)
  letI : Subsingleton (groupCohomology (originalLinearCharacterRep ℚ M) i) :=
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Original first and second cohomology of the rational-valued Hom coefficient vanish for a finite group. -/
theorem originalRationalHom_first_second_zero [Fintype G] :
    Limits.IsZero (groupCohomology (originalLinearCharacterRep ℚ M) 1) ∧
      Limits.IsZero (groupCohomology (originalLinearCharacterRep ℚ M) 2) :=
  ⟨originalRationalHomCohomology_zero_of_annihilation M 1 (Fintype.card G)
      (Fintype.card_ne_zero) (finiteFirstCohomology_card_nsmul_eq_zero _),
    originalRationalHomCohomology_zero_of_annihilation M 2 (Fintype.card G)
      (Fintype.card_ne_zero) (finiteSecondCohomology_card_nsmul_eq_zero _)⟩

end
end Dubon2026
