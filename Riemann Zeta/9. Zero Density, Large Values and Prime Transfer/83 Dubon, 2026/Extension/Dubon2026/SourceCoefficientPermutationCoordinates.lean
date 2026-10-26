import Dubon2026.SourcePermutationCoefficientQuotient
import Dubon2026.PermutationCoordinateRepresentation
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! DUB-17/18 -> original all-weight adic association -> finite-level
geometric realization -> the original finite coefficient permutation module.
Reuse the existing permuted-basis coordinate isomorphism. Its action is the
literal original representation on its actual vectors. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]

/-- The original representation acting on its actual coefficient vectors. -/
abbrev sourceCoefficientVectorAction (A : Rep R G) : MulAction G A where
  smul g x := A.ρ g x
  one_smul x := by change A.ρ 1 x = x; simp
  mul_smul g h x := by
    change A.ρ (g * h) x = A.ρ g (A.ρ h x)
    simp [Module.End.mul_apply]

attribute [local instance] sourceCoefficientVectorAction

/-- The original finite permutation coefficients are the existing inverse-action coordinates. -/
def sourceCoefficientPermutationCoordinateIso (A : Rep R G) [Fintype A] :
    sourceCoefficientPermutationRep A ≅ permutationCoordinateRep R G A :=
  permutationBasisCoordinateIso R G A (sourceCoefficientPermutationRep A)
    Finsupp.basisSingleOne (fun g x => by
      change Finsupp.lmapDomain R R (A.ρ g) (Finsupp.basisSingleOne x) =
        Finsupp.basisSingleOne (A.ρ g x)
      simp [Finsupp.coe_basisSingleOne])

end
end Dubon2026
