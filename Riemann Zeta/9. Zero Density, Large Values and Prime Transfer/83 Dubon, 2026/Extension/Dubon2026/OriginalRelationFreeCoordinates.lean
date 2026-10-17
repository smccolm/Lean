import Dubon2026.OriginalPrimeCoefficientCoordinates

/-! # Coordinates in the actual integral relation cover

These additive maps split the coordinate calculation used to extend a
literal norm witness. They retain the original free representation and
cover. The trivial coefficient action is explicit; discharging it on the
required subgroup is part of DUB-17's later arithmetic reduction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (B : Rep.{0} ℤ G) {ι : Type}

/-- Sum the integer coefficients in the original group ring. -/
def originalRelationCoefficientTotal : (G →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

/-- The original free cover's coordinates induced by representatives of the coefficient. -/
def originalRelationFreeCoordinates (v : B → (ι →₀ ℤ)) :
    (B →₀ G →₀ ℤ) →+ (ι →₀ ℤ) :=
  (Finsupp.liftAddHom fun b => zmultiplesHom (ι →₀ ℤ) (v b)).comp
    (Finsupp.mapRange.addMonoidHom originalRelationCoefficientTotal)

/-- The literal section placing each coordinate at the identity group element. -/
def originalRelationCoordinateSection (a : ι → B) : (ι →₀ ℤ) →+ (B →₀ G →₀ ℤ) :=
  (Finsupp.mapRange.addMonoidHom (Finsupp.singleAddHom (1 : G))).comp
    (Finsupp.mapDomain.addMonoidHom a)

/-- The actual free-cover coordinates of an elementary group-ring generator. -/
theorem originalRelationFreeCoordinates_single (v : B → (ι →₀ ℤ))
    (b : B) (h : G) (n : ℤ) :
    originalRelationFreeCoordinates B v (Finsupp.single b (Finsupp.single h n)) = n • v b := by
  simp [originalRelationFreeCoordinates, originalRelationCoefficientTotal]

/-- The original coordinate section on a basis generator. -/
theorem originalRelationCoordinateSection_single (a : ι → B) (i : ι) (n : ℤ) :
    originalRelationCoordinateSection B a (Finsupp.single i n) =
      Finsupp.single (a i) (Finsupp.single 1 n) := by
  simp [originalRelationCoordinateSection, Finsupp.mapDomain_single]

/-- On a coefficient with trivial action, the original free cover evaluates the integer generator. -/
theorem originalRelationFreeCover_single_of_trivial
    (htriv : ∀ (g : G) (b : B), B.ρ g b = b) (b : B) (h : G) (n : ℤ) :
    (originalRelationFreeCover B).hom (Finsupp.single b (Finsupp.single h n)) = n • b := by
  simp only [originalRelationFreeCover, Rep.freeLift, Rep.hom_ofHom,
    Representation.freeLift_single_single, htriv]
  exact int_smul_eq_zsmul B.hV2 n b

/-- Evaluation of actual free coordinates is exactly the original cover. -/
theorem originalRelationFreeCover_eq_coordinate_evaluation (a : ι → B)
    (v : B → (ι →₀ ℤ))
    (hv : ∀ b : B, originalPrimeCoordinateEvaluation B a (v b) = b)
    (htriv : ∀ (g : G) (b : B), B.ρ g b = b) (x : B →₀ G →₀ ℤ) :
    (originalRelationFreeCover B).hom x =
      originalPrimeCoordinateEvaluation B a (originalRelationFreeCoordinates B v x) := by
  suffices he : (originalRelationFreeCover B).hom.toAddMonoidHom =
      (originalPrimeCoordinateEvaluation B a).comp (originalRelationFreeCoordinates B v)
      from DFunLike.congr_fun he x
  refine Finsupp.addHom_ext fun b m => ?_
  suffices he : (originalRelationFreeCover B).hom.toAddMonoidHom.comp (Finsupp.singleAddHom b) =
      ((originalPrimeCoordinateEvaluation B a).comp
        (originalRelationFreeCoordinates B v)).comp (Finsupp.singleAddHom b)
      from DFunLike.congr_fun he m
  refine Finsupp.addHom_ext fun h n => ?_
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply,
    LinearMap.toAddMonoidHom_coe,
    originalRelationFreeCoordinates_single, map_zsmul, hv]
  exact originalRelationFreeCover_single_of_trivial B htriv b h n

/-- The original cover of the literal section is the coordinate evaluation. -/
theorem originalRelationFreeCover_coordinate_section (a : ι → B)
    (htriv : ∀ (g : G) (b : B), B.ρ g b = b) (y : ι →₀ ℤ) :
    (originalRelationFreeCover B).hom (originalRelationCoordinateSection B a y) =
      originalPrimeCoordinateEvaluation B a y := by
  suffices he : (originalRelationFreeCover B).hom.toAddMonoidHom.comp
      (originalRelationCoordinateSection B a) = originalPrimeCoordinateEvaluation B a
      from DFunLike.congr_fun he y
  refine Finsupp.addHom_ext fun i n => ?_
  simp [originalRelationCoordinateSection_single,
    originalRelationFreeCover_single_of_trivial B htriv, originalPrimeCoordinateEvaluation]

/-- Group translation leaves the actual free coordinates unchanged. -/
theorem originalRelationFreeCoordinates_action (v : B → (ι →₀ ℤ))
    (g : G) (x : B →₀ G →₀ ℤ) :
    originalRelationFreeCoordinates B v ((Rep.free ℤ G B).ρ g x) =
      originalRelationFreeCoordinates B v x := by
  suffices he : (originalRelationFreeCoordinates B v).comp
      ((Rep.free ℤ G B).ρ g).toAddMonoidHom = originalRelationFreeCoordinates B v
      from DFunLike.congr_fun he x
  refine Finsupp.addHom_ext fun b m => ?_
  suffices he : ((originalRelationFreeCoordinates B v).comp
        ((Rep.free ℤ G B).ρ g).toAddMonoidHom).comp (Finsupp.singleAddHom b) =
      (originalRelationFreeCoordinates B v).comp (Finsupp.singleAddHom b)
      from DFunLike.congr_fun he m
  refine Finsupp.addHom_ext fun h n => ?_
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply,
    LinearMap.toAddMonoidHom_coe, Representation.free_single_single,
    originalRelationFreeCoordinates_single]

end
end Dubon2026
