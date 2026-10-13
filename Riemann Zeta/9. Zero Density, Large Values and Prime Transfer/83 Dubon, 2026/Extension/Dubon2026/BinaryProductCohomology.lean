import Dubon2026.FiniteProductCohomology
import Mathlib.LinearAlgebra.Pi

/-! # Original cohomology of the literal binary product representation

The existing finite-product cohomology theorem applies through the
two-coordinate equivalence to the literal product representation. This
combines DUB-17's actual unrestricted and outside-support idele factors.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G] (A B : Rep R G)

/-- The literal binary product representation is the original two-coordinate product. -/
def originalBinaryProductPiIso :
    Rep.of (A.ρ.prod B.ρ) ≅ originalPiRep ![A, B] := by
  apply Rep.mkIso
  refine Representation.Equiv.mk (LinearEquiv.piFinTwo R (fun i => (![A, B] i : Type))).symm ?_
  intro g
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;> rfl

/-- Original cohomology of the actual binary product is the product of original cohomologies. -/
def originalBinaryProductCohomologyIso (n : ℕ) :
    groupCohomology (Rep.of (A.ρ.prod B.ρ)) n ≅
      ModuleCat.of R (groupCohomology A n × groupCohomology B n) :=
  (groupCohomology.functor R G n).mapIso (originalBinaryProductPiIso A B) ≪≫
    originalFinitePiCohomologyIso ![A, B] n ≪≫
    (LinearEquiv.piFinTwo R (fun i => (groupCohomology (![A, B] i) n : Type))).toModuleIso

/-- The actual binary-product cohomology has the product of the original factor orders. -/
theorem originalBinaryProduct_cohomology_card (n : ℕ) :
    Nat.card (groupCohomology (Rep.of (A.ρ.prod B.ρ)) n) =
      Nat.card (groupCohomology A n) * Nat.card (groupCohomology B n) :=
  (Nat.card_congr (originalBinaryProductCohomologyIso A B n).toLinearEquiv.toEquiv).trans (Nat.card_prod _ _)

/-- Finite original factor cohomologies imply finite actual binary-product cohomology. -/
theorem originalBinaryProduct_cohomology_finite (n : ℕ)
    [Finite (groupCohomology A n)] [Finite (groupCohomology B n)] :
    Finite (groupCohomology (Rep.of (A.ρ.prod B.ρ)) n) :=
  Finite.of_equiv (groupCohomology A n × groupCohomology B n)
    (originalBinaryProductCohomologyIso A B n).symm.toLinearEquiv.toEquiv

end
end Dubon2026
