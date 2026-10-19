import Dubon2026.PolarizedFramedMatrixFiber

/-! Genuine continuous polarized lifts are equivalent to the original
continuous framed matrix lifts satisfying the explicit source equations.
This is the comparison needed to restrict native framed universality to
the polarized coefficient quotient in DUB-17's CM deformation problem. -/

namespace Dubon2026
open Matrix
noncomputable section

universe u
variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
  (H : ProfiniteGrp.{u}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : H →* Oˣ)

/-- Original continuous framed matrices satisfying the literal source polarized equations. -/
abbrev PolarizedMatrixFramedFiber :=
  {τ : OriginalContinuousFramedFiber eA H (polarizedBlockRepresentation.comp σ) //
    PolarizedMatrixEquations τ.val.toMonoidHom
      ((polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ)
      ((Units.map (algebraMap O A).toMonoidHom).comp ν)}

variable [Nonempty ι] [CompactSpace A] [T2Space A]

/-- The original matrix equations construct a genuine continuous polarized lift,
including its original residual map and fixed similitude. -/
@[irreducible] def polarizedFramedFiberOfMatrices (τ : PolarizedMatrixFramedFiber eA H σ ν) :
    OriginalContinuousPolarizedFiber eA H σ ν := by
  let ρ : H →* PolarizedGaloisGroup ι A :=
    @polarizedRepresentationOfEquations H A ι _ _ _ _ _ _ τ.val.val.toMonoidHom
      ((polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ)
      ((Units.map (algebraMap O A).toMonoidHom).comp ν) τ.property
  have hb (g : H) : polarizedBlockRepresentation (ρ g) = τ.val.val g :=
    polarizedRepresentationOfEquations_block _ _ _ _ g
  have hcont : Continuous ρ := by
    apply (continuous_polarized_iff_block ρ).mpr
    exact τ.val.val.continuous.congr (fun g => (hb g).symm)
  refine ⟨⟨ρ, hcont⟩, ?_, ?_⟩
  · apply MonoidHom.ext
    intro g
    apply polarizedBlockRepresentation_injective
    change polarizedBlockRepresentation
      (polarizedCoefficientMap (localCoefficientReduction eA).toRingHom (ρ g)) = _
    rw [← polarizedBlockRepresentation_map, hb]
    exact DFunLike.congr_fun τ.val.property g
  · apply MonoidHom.ext
    intro g
    exact polarizedRepresentationOfEquations_similitude τ.val.val.toMonoidHom
      ((polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ)
      ((Units.map (algebraMap O A).toMonoidHom).comp ν) τ.property g

/-- The reconstructed continuous polarized lift retains every original matrix. -/
theorem polarizedFramedFiberOfMatrices_block (τ : PolarizedMatrixFramedFiber eA H σ ν) (g : H) :
    polarizedBlockRepresentation ((polarizedFramedFiberOfMatrices eA H σ ν τ).val g) = τ.val.val g := by
  unfold polarizedFramedFiberOfMatrices
  exact polarizedRepresentationOfEquations_block τ.val.val.toMonoidHom
    ((polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ)
    ((Units.map (algebraMap O A).toMonoidHom).comp ν) τ.property g

/-- The actual continuous source deformation fiber is equivalent to the same original
framed matrix fiber with the proved explicit polarized equations. -/
def polarizedFramedFiberEquiv :
    OriginalContinuousPolarizedFiber eA H σ ν ≃ PolarizedMatrixFramedFiber eA H σ ν where
  toFun ρ := ⟨polarizedFramedMatrixFiber eA H σ ν ρ, polarizedFramedMatrixFiber_equations eA H σ ν ρ⟩
  invFun := polarizedFramedFiberOfMatrices eA H σ ν
  left_inv ρ := by
    apply Subtype.ext
    apply DFunLike.ext
    intro g
    apply polarizedBlockRepresentation_injective
    exact polarizedFramedFiberOfMatrices_block eA H σ ν _ g
  right_inv τ := by
    apply Subtype.ext
    apply Subtype.ext
    apply DFunLike.ext
    intro g
    exact polarizedFramedFiberOfMatrices_block eA H σ ν τ g

end
end Dubon2026
