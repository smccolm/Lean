import Dubon2026.ContinuousCocycleRestrictionFiniteness
import Dubon2026.ContinuousFiniteCoefficientSplitting
import Dubon2026.ContinuousTrivialCocycleCoordinates
import Dubon2026.ContinuousCohomologyCoefficientCongr
import Dubon2026.RationalArithmeticGaloisGroup

/-! Finiteness of actual arithmetic H1 with finite prime-field coefficients.
This supplies the twisted global H1 finiteness needed for DUB-17's numerical
dual Selmer comparison, using the proved arithmetic character finiteness.
The action kernel, its finite index and its trivial restricted action are derived. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] continuousTrivialCoordinateSMul

variable (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (hqa : (q : 𝓞 ℚ) ∣ a)
  (A : Rep (ZMod q) (rationalArithmeticGaloisGroup a))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))

include ha hqa hA

/-- Actual continuous arithmetic cocycles in a finite prime-field module are finite. -/
theorem rationalArithmeticFiniteCoefficientCocycles_finite :
    Finite (continuousRepresentationCocyclesOne A) := by
  let U : OpenSubgroup (rationalArithmeticGaloisGroup a) :=
    ⟨A.ρ.asGroupHom.ker, continuousFiniteCoefficient_kernel_isOpen A hA⟩
  haveI : Finite (rationalArithmeticGaloisGroup a ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen
  haveI : Finite (U →ₜ* Multiplicative (ZMod q)) :=
    rationalArithmeticGaloisGroup_openSubgroup_prime_characters_finite
      a ha q Fact.out hqa U
  haveI : Module.Finite (ZMod q) A := Module.Finite.of_finite
  haveI : Finite (continuousRepresentationCocyclesOne
      (Rep.of (1 : Representation (ZMod q) U A))) :=
    continuousTrivialCocycles_finite q
  have he : A.ρ.comp U.toSubgroup.subtype = (1 : Representation (ZMod q) U A) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro x
    exact congrArg (fun u : Units (A →ₗ[ZMod q] A) => u.val x) g.property
  haveI : Finite (continuousRepresentationCocyclesOne
      (restrictedCoefficientRep A U.toSubgroup.subtype)) :=
    Finite.of_equiv _ (continuousCocycleOneCoefficientCongr he).symm.toEquiv
  exact continuousCocyclesOne_finite_of_restriction A U.toSubgroup

/-- The original arithmetic H1 quotient is finite, with no finiteness premise on its classes. -/
theorem rationalArithmeticFiniteCoefficientH1_finite :
    Finite (ContinuousRepresentationH1 A hA) := by
  haveI := rationalArithmeticFiniteCoefficientCocycles_finite a ha q hqa A hA
  exact Finite.of_surjective (continuousRepresentationCoboundariesOne A hA).mkQ
    (Submodule.mkQ_surjective _)

end
end Dubon2026
