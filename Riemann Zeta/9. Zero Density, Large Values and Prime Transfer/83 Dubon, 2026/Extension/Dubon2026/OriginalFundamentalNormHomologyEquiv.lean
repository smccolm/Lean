import Dubon2026.OriginalFundamentalHomologyNormUniqueness
import Dubon2026.OriginalFundamentalHomologyWitnessLinear
import Dubon2026.OriginalFundamentalHomologySurjectivity

/-! # The actual original coefficient norm quotient and first homology

The chosen literal norm lifts define a linear map with exactly the
original norm range as kernel. Every actual homology class has a lift,
so the map induces an equivalence. Its trivial-source specialization
supplies the abelian norm index needed for DUB-17's norm-field route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (M C : Rep.{0} ℤ G)
  [Module.Projective ℤ M] (φ : groupCohomology.cocycles₂ C)
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
  (h : ∀ S : Subgroup G,
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))

/-- The actual homology class of the original coefficient morphism, independent of the literal middle norm lift. -/
def originalFundamentalHomologyLinear :
    (M ⟶ C) →ₗ[ℤ] groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1 where
  toFun χ := (originalFundamentalHomology_witness_exists M C φ p hG h χ).choose
  map_add' χ ψ := by
    apply originalFundamentalHomologyWitness_unique M C φ p hG h (χ + ψ)
    · exact (originalFundamentalHomology_witness_exists M C φ p hG h (χ + ψ)).choose_spec.1
    · exact originalFundamentalHomologyWitness_add M C φ
        (originalFundamentalHomology_witness_exists M C φ p hG h χ).choose_spec.1
        (originalFundamentalHomology_witness_exists M C φ p hG h ψ).choose_spec.1
  map_smul' n χ := by
    apply originalFundamentalHomologyWitness_unique M C φ p hG h (n • χ)
    · exact (originalFundamentalHomology_witness_exists M C φ p hG h (n • χ)).choose_spec.1
    · exact (congrArg (OriginalFundamentalHomologyWitness M C φ (n • χ))
        (int_smul_eq_zsmul (groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1).isModule n _)).mpr
        (originalFundamentalHomologyWitness_smul M C φ
          (originalFundamentalHomology_witness_exists M C φ p hG h χ).choose_spec.1 n)

/-- The constructed linear homology map retains the actual middle norm lift and augmentation boundary. -/
theorem originalFundamentalHomologyLinear_witness (χ : M ⟶ C) :
    OriginalFundamentalHomologyWitness M C φ χ
      (originalFundamentalHomologyLinear M C φ p hG h χ) :=
  (originalFundamentalHomology_witness_exists M C φ p hG h χ).choose_spec.1

/-- The kernel is precisely the range of literal original coefficient norms. -/
theorem originalFundamentalHomologyLinear_ker :
    (originalFundamentalHomologyLinear M C φ p hG h).ker =
      (originalCoefficientNormLinearMap M C).range := by
  ext χ
  change originalFundamentalHomologyLinear M C φ p hG h χ = 0 ↔ _
  exact (originalFundamentalHomology_witness_exists M C φ p hG h χ).choose_spec.2.symm.trans
    (Submodule.Quotient.mk_eq_zero _)

/-- Every actual first homology class is the image of an original coefficient morphism. -/
theorem originalFundamentalHomologyLinear_surjective :
    Function.Surjective (originalFundamentalHomologyLinear M C φ p hG h) := by
  intro y
  obtain ⟨χ, hy⟩ := originalFundamentalHomology_witness_surjective M C φ y
  exact ⟨χ, originalFundamentalHomologyWitness_unique M C φ p hG h χ
    (originalFundamentalHomologyLinear_witness M C φ p hG h χ) hy⟩

/-- The existing original morphism norm quotient is linearly equivalent to actual first homology of the integral dual. -/
def originalFundamentalNormHomologyEquiv :
    OriginalCoefficientNormQuotient M C ≃ₗ[ℤ]
      groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1 :=
  (Submodule.quotEquivOfEq _ _ (originalFundamentalHomologyLinear_ker M C φ p hG h).symm).trans
    ((originalFundamentalHomologyLinear M C φ p hG h).quotKerEquivOfSurjective
      (originalFundamentalHomologyLinear_surjective M C φ p hG h))

end
end Dubon2026
