import Dubon2026.MatrixAdjointScalarDescent
import Dubon2026.LocalCoefficientReduction

/-! # Actual scalar extension through the original true-residue equivalence -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L]

/-- Extending the actual maximal-ideal reduction through the specified true-residue equivalence gives the original residual representation over the same extension field, entry by entry. -/
theorem trueResidueScalarExtension_eq
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ) :
    letI : Algebra (IsLocalRing.ResidueField R) L :=
      ((algebraMap (IsLocalRing.ResidueField O) L).comp eR.toRingHom).toAlgebra
    matrixCoefficientExtension (L := L)
      ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ) =
        matrixCoefficientExtension (L := L) σ := by
  letI : Algebra (IsLocalRing.ResidueField R) L :=
    ((algebraMap (IsLocalRing.ResidueField O) L).comp eR.toRingHom).toAlgebra
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  have he := congrArg
    (fun U : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => U.val i j)
    (DFunLike.congr_fun hσ g)
  exact congrArg (algebraMap (IsLocalRing.ResidueField O) L) he

end
end Dubon2026
