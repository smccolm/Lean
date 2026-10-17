import Dubon2026.OriginalFiniteFundamentalHomologyWitness
import Dubon2026.OriginalFundamentalHomologyWitnessLinear
import Dubon2026.OriginalFundamentalHomologySurjectivity

/-! # Original finite-group norm quotient and actual homology

Reuse the original linear witness, quotient and homology-surjectivity
construction with the newly proved finite-group norm inputs. This removes
the p-group premise from the comparison needed by DUB-17's relation
obstruction surjectivity. The actual H2-map surjectivity is still separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (M C : Rep.{0} ℤ G)
  [Module.Projective ℤ M] (φ : groupCohomology.cocycles₂ C)
  (h : ∀ S : Subgroup G,
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))

/-- The actual homology class of the original coefficient morphism, independent of the literal middle norm lift. -/
def originalFiniteFundamentalHomologyLinear :
    (M ⟶ C) →ₗ[ℤ] groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1 where
  toFun χ := (originalFiniteFundamentalHomology_witness_exists M C φ h χ).choose
  map_add' χ ψ := by
    apply originalFiniteFundamentalHomologyWitness_unique M C φ h (χ + ψ)
    · exact (originalFiniteFundamentalHomology_witness_exists M C φ h (χ + ψ)).choose_spec.1
    · exact originalFundamentalHomologyWitness_add M C φ
        (originalFiniteFundamentalHomology_witness_exists M C φ h χ).choose_spec.1
        (originalFiniteFundamentalHomology_witness_exists M C φ h ψ).choose_spec.1
  map_smul' n χ := by
    apply originalFiniteFundamentalHomologyWitness_unique M C φ h (n • χ)
    · exact (originalFiniteFundamentalHomology_witness_exists M C φ h (n • χ)).choose_spec.1
    · exact (congrArg (OriginalFundamentalHomologyWitness M C φ (n • χ))
        (int_smul_eq_zsmul (groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1).isModule n _)).mpr
        (originalFundamentalHomologyWitness_smul M C φ
          (originalFiniteFundamentalHomology_witness_exists M C φ h χ).choose_spec.1 n)

/-- The constructed linear homology map retains the actual middle norm lift and augmentation boundary. -/
theorem originalFiniteFundamentalHomologyLinear_witness (χ : M ⟶ C) :
    OriginalFundamentalHomologyWitness M C φ χ
      (originalFiniteFundamentalHomologyLinear M C φ h χ) :=
  (originalFiniteFundamentalHomology_witness_exists M C φ h χ).choose_spec.1

/-- The kernel is precisely the range of literal original coefficient norms. -/
theorem originalFiniteFundamentalHomologyLinear_ker :
    (originalFiniteFundamentalHomologyLinear M C φ h).ker =
      (originalCoefficientNormLinearMap M C).range := by
  ext χ
  change originalFiniteFundamentalHomologyLinear M C φ h χ = 0 ↔ _
  exact (originalFiniteFundamentalHomology_witness_exists M C φ h χ).choose_spec.2.symm.trans
    (Submodule.Quotient.mk_eq_zero _)

/-- Every actual first homology class is the image of an original coefficient morphism. -/
theorem originalFiniteFundamentalHomologyLinear_surjective :
    Function.Surjective (originalFiniteFundamentalHomologyLinear M C φ h) := by
  intro y
  obtain ⟨χ, hy⟩ := originalFundamentalHomology_witness_surjective M C φ y
  exact ⟨χ, originalFiniteFundamentalHomologyWitness_unique M C φ h χ
    (originalFiniteFundamentalHomologyLinear_witness M C φ h χ) hy⟩

/-- The existing original morphism norm quotient is linearly equivalent to actual first homology of the integral dual. -/
def originalFiniteFundamentalNormHomologyEquiv :
    OriginalCoefficientNormQuotient M C ≃ₗ[ℤ]
      groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1 :=
  (Submodule.quotEquivOfEq _ _ (originalFiniteFundamentalHomologyLinear_ker M C φ h).symm).trans
    ((originalFiniteFundamentalHomologyLinear M C φ h).quotKerEquivOfSurjective
      (originalFiniteFundamentalHomologyLinear_surjective M C φ h))

end
end Dubon2026
