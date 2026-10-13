import Dubon2026.ContinuousFiniteCyclicH2
import Dubon2026.CyclicGeneratorNormSum
import Mathlib.LinearAlgebra.Isomorphisms

/-! # The original finite cyclic norm quotient and cocycle-period map

This is the finite-stage input for killing unramified finite-coefficient H2
by enlarging the cyclic stage. Together with the existing period-inflation
formula, that vanishing will serve support control for the original local
invariants in DUB-17's global reciprocity and Selmer duality route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
  [TopologicalSpace R] [TopologicalSpace G] [DiscreteTopology G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The actual norm range inside the original generator-fixed coefficients. -/
def finiteCyclicInvariantNormRange :
    Submodule R (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :=
  (LinearMap.range A.norm.hom.toLinearMap).comap
    (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap).subtype

/-- The existing original cyclic H2 class map has exactly the norm kernel. -/
theorem continuousFiniteCyclicH2Pi_ker :
    LinearMap.ker (continuousFiniteCyclicH2Pi A hA g hg) = finiteCyclicInvariantNormRange A g := by
  ext x
  exact continuousFiniteCyclicH2Pi_eq_zero_iff A hA g hg x

/-- The original invariant coefficients modulo actual norms identify with
the same continuous H2 by the already proved finite cyclic computation. -/
def continuousFiniteCyclicNormQuotientEquiv :
    (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap ⧸
      finiteCyclicInvariantNormRange A g) ≃ₗ[R] ContinuousRepresentationH2 A hA :=
  (Submodule.quotEquivOfEq _ _ (continuousFiniteCyclicH2Pi_ker A hA g hg).symm).trans
    ((continuousFiniteCyclicH2Pi A hA g hg).quotKerEquivOfSurjective
      (continuousFiniteCyclicH2Pi_surjective A hA g hg))

/-- The literal original two-cocycle period is an actual invariant coefficient. -/
def finiteCyclicTwoCocycleInvariantPeriod :
    continuousRepresentationCocyclesTwo A →ₗ[R]
      LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap :=
  ((representationCyclicTwoCochainPeriodSum A g (orderOf g)).comp
    ((groupCohomology.cocycles₂ A).subtype.comp (continuousRepresentationCocyclesTwo A).subtype)).codRestrict _
      (fun c => sub_eq_zero.mpr (representationCyclicTwoCocyclePeriodSum_fixed A g
        (orderOf g) (pow_orderOf_eq_one g) c.val))

/-- The actual cocycle period descends through original continuous
coboundaries into the original norm quotient. Bijectivity is separate. -/
def finiteCyclicH2PeriodNormMap :
    ContinuousRepresentationH2 A hA →ₗ[R]
      (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap ⧸
        finiteCyclicInvariantNormRange A g) :=
  (continuousRepresentationCoboundariesTwo A hA).liftQ
    ((finiteCyclicInvariantNormRange A g).mkQ.comp
      (finiteCyclicTwoCocycleInvariantPeriod A g)) (by
        rintro _ ⟨b, rfl⟩
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        change representationCyclicTwoCochainPeriodSum A g (orderOf g)
          (groupCohomology.d₁₂ A b) ∈ LinearMap.range A.norm.hom.toLinearMap
        rw [representationCyclicPeriodSum_coboundary_eq_norm A g hg]
        exact ⟨b g, rfl⟩)

/-- This H2 map retains exactly the original period of every representative. -/
theorem finiteCyclicH2PeriodNormMap_mk (c : continuousRepresentationCocyclesTwo A) :
    finiteCyclicH2PeriodNormMap A hA g hg (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (finiteCyclicTwoCocycleInvariantPeriod A g c) := by
  rfl

end
end Dubon2026
