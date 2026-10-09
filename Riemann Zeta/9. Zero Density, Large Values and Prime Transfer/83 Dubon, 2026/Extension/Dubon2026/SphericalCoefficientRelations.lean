import Dubon2026.GramFamilyIsometry
import Dubon2026.UnitaryDoubleCosetCoefficient

/-! # Genuine spherical coefficient identities preserve the original cyclic linear relations -/

namespace Dubon2026

noncomputable section

variable {G V W : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (v : V) (w : W) (ℓ : W →ₗ[ℂ] ℂ)
    (hcoeff : ∀ g, ℓ (σ g w) = inner ℂ v (ρ g v))

include hρ hcoeff in
/-- Equality of the actual spherical coefficients identifies every original finite orbit pairing with the genuine translated linear functional. -/
theorem sphericalCoefficient_linearCombination (g : G) (a : G →₀ ℂ) :
    inner ℂ (ρ g v) (Finsupp.linearCombination ℂ (fun h => ρ h v) a) =
      ℓ (σ g⁻¹ (Finsupp.linearCombination ℂ (fun h => σ h w) a)) := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, inner_smul_right,
    map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [representation_inner_inverse ρ hρ g, ← Module.End.mul_apply, ← map_mul,
    ← hcoeff, map_mul, Module.End.mul_apply]

include hρ hcoeff in
/-- Every genuine finite relation among the source induced orbit vectors is an actual relation in the original unitary orbit, by nondegeneracy of its original inner product. -/
theorem sphericalCoefficient_linearCombination_ker_le :
    (Finsupp.linearCombination ℂ (fun g => σ g w)).ker ≤
      (Finsupp.linearCombination ℂ (fun g => ρ g v)).ker := by
  intro a ha
  change Finsupp.linearCombination ℂ (fun g => ρ g v) a = 0
  change Finsupp.linearCombination ℂ (fun g => σ g w) a = 0 at ha
  have hz (g : G) : inner ℂ (ρ g v) (Finsupp.linearCombination ℂ (fun h => ρ h v) a) = 0 := by
    rw [sphericalCoefficient_linearCombination ρ σ hρ v w ℓ hcoeff g a, ha, map_zero, map_zero]
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  conv_lhs => lhs; rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, sum_inner, inner_smul_left, hz, mul_zero, Finset.sum_const_zero]

/-- The actual source cyclic orbit maps to the original unitary orbit through the genuine quotient by its proved linear relations. No norm or unitarity on the source space is assumed. -/
def sphericalCoefficientRangeMap :
    (Finsupp.linearCombination ℂ (fun g => σ g w)).range →ₗ[ℂ] V :=
  ((Finsupp.linearCombination ℂ (fun g => σ g w)).ker.liftQ
    (Finsupp.linearCombination ℂ (fun g => ρ g v))
    (sphericalCoefficient_linearCombination_ker_le ρ σ hρ v w ℓ hcoeff)).comp
      (Finsupp.linearCombination ℂ (fun g => σ g w)).quotKerEquivRange.symm.toLinearMap

/-- The genuine cyclic quotient map sends each original finite source orbit combination to exactly the corresponding original unitary combination. -/
theorem sphericalCoefficientRangeMap_linearCombination (a : G →₀ ℂ)
    (ha : Finsupp.linearCombination ℂ (fun g => σ g w) a ∈
      (Finsupp.linearCombination ℂ (fun g => σ g w)).range) :
    sphericalCoefficientRangeMap ρ σ hρ v w ℓ hcoeff
      ⟨Finsupp.linearCombination ℂ (fun g => σ g w) a, ha⟩ =
      Finsupp.linearCombination ℂ (fun g => ρ g v) a := by
  simp only [sphericalCoefficientRangeMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- The image of the genuine cyclic quotient map is precisely the original unitary cyclic orbit span. -/
theorem sphericalCoefficientRangeMap_range :
    (sphericalCoefficientRangeMap ρ σ hρ v w ℓ hcoeff).range =
      (Finsupp.linearCombination ℂ (fun g => ρ g v)).range := by
  ext x
  constructor
  · rintro ⟨⟨y, a, rfl⟩, rfl⟩
    exact ⟨a, (sphericalCoefficientRangeMap_linearCombination ρ σ hρ v w ℓ hcoeff a _).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨_, ⟨a, rfl⟩⟩, sphericalCoefficientRangeMap_linearCombination ρ σ hρ v w ℓ hcoeff a _⟩

end
end Dubon2026
