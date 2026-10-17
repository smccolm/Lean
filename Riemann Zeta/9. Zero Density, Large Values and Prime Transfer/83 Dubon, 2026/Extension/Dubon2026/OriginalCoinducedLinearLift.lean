import Dubon2026.OriginalCoefficientNormCohomology
import Dubon2026.OriginalCoinducedNormKernel

/-! # Lift an original linear map through existing coinduced trace

The mod-p comparison extends a linear section of the actual coinvariant
projection to a genuine coefficient morphism. Existing trivial-subgroup
coinduction and the original coset trace supply equivariance, avoiding
a new induced tensor model on DUB-17's integral projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (D A : Rep.{0} ℤ G)

/-- The original linear map extended to an equivariant map by the existing actual coinduced trace. -/
def originalCoinducedLinearLift (T : D →ₗ[ℤ] A) : originalCoinducedFunctionRep D ⟶ A :=
  letI : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  (Rep.coindFunctor ℤ (⊥ : Subgroup G).subtype).map
    (originalTrivialSubgroupCoefficientMap D A T) ≫ coinducedCosetTrace A (⊥ : Subgroup G)

/-- The existing coinduced trace lift is the literal finite sum of translates of the original linear values. -/
theorem originalCoinducedLinearLift_apply (T : D →ₗ[ℤ] A)
    (x : originalCoinducedFunctionRep D) :
    (originalCoinducedLinearLift D A T).hom x = ∑ g : G, A.ρ g (T (x.val g⁻¹)) := by
  letI : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  change (∑ q : G ⧸ (⊥ : Subgroup G), coinducedCosetValues A (⊥ : Subgroup G)
    (((Rep.coindFunctor ℤ (⊥ : Subgroup G).subtype).map
      (originalTrivialSubgroupCoefficientMap D A T)).hom x) q) = _
  refine Fintype.sum_equiv (QuotientGroup.quotientBot.toEquiv) _ _ ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H g => rfl

/-- On an original identity-supported function, the actual trace lift equals the supplied original linear map. -/
theorem originalCoinducedLinearLift_point (T : D →ₗ[ℤ] A) (d : D) :
    (originalCoinducedLinearLift D A T).hom (originalCoinducedPoint D d) = T d := by
  classical
  rw [originalCoinducedLinearLift_apply]
  change (∑ g : G, A.ρ g (T (if g⁻¹ = 1 then d else 0))) = T d
  rw [Finset.sum_eq_single 1]
  · simp
  · intro g _ hg
    simp [hg]
  · simp

end
end Dubon2026
