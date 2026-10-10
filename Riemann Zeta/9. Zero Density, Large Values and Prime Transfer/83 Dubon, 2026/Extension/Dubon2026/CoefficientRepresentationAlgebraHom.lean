import Dubon2026.CoefficientRepresentationMatrixAlgebra

/-! # The whole original group homomorphism into its actual coefficient matrix algebra -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]

/-- The original whole representation takes values in the literal coefficient algebra it generates. -/
def coefficientRepresentationAlgebraHom (S : Subalgebra O R)
    (ρ : G →* GeneralLinearGroup ι R) : G →* coefficientRepresentationMatrixAlgebra S ρ where
  toFun g := ⟨(ρ g).val, Algebra.subset_adjoin ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (congrArg Units.val (ρ.map_one))
  map_mul' g h := Subtype.ext (congrArg Units.val (ρ.map_mul g h))

/-- The whole original representation is retained exactly under the actual matrix-algebra inclusion. -/
theorem coefficientRepresentationAlgebraHom_inclusion (S : Subalgebra O R)
    (ρ : G →* GeneralLinearGroup ι R) :
    (coefficientRepresentationMatrixAlgebra S ρ).val.toRingHom.toMonoidHom.comp
        (coefficientRepresentationAlgebraHom S ρ) =
      (Units.coeHom (Matrix ι ι R)).comp ρ := by
  apply MonoidHom.ext
  intro g
  rfl

/-- Each original group element retains its entire original matrix in the generated coefficient algebra. -/
theorem coefficientRepresentationAlgebraHom_val (S : Subalgebra O R)
    (ρ : G →* GeneralLinearGroup ι R) (g : G) :
    (coefficientRepresentationAlgebraHom S ρ g).val = (ρ g).val := rfl

end
end Dubon2026
