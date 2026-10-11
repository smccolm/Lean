import Dubon2026.CyclicGeneratorNormSum
import Dubon2026.GaloisGeneratorInvariantBaseEquiv

/-! # Original cyclic Galois cocycle period sums descend to actual base units -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The original generator period of the actual continuous two-cocycle,
descended to the genuine original base-field unit by proved invariant descent. -/
def galoisUnitCyclicPeriodBase :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L) →ₗ[ℤ] Additive Kˣ := by
  let A := Rep.ofAlgebraAutOnUnits K L
  let S : continuousRepresentationCocyclesTwo A →ₗ[ℤ] A :=
    (representationCyclicTwoCochainPeriodSum A g (orderOf g)).comp
      ((groupCohomology.cocycles₂ A).subtype.comp (continuousRepresentationCocyclesTwo A).subtype)
  have hS : ∀ c, S c ∈ LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
    intro c
    change A.ρ g (S c) - S c = 0
    exact sub_eq_zero.mpr (representationCyclicTwoCocyclePeriodSum_fixed A g
      (orderOf g) (pow_orderOf_eq_one g) c.val)
  exact (galoisGeneratorInvariantBaseEquiv g hg).symm.toLinearMap.comp (S.codRestrict _ hS)

/-- The actual descended base unit has exactly the original cocycle period
as its original extension-field coefficient. -/
theorem galoisUnitCyclicPeriodBase_coefficient
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    galoisUnitsBaseCoefficient (L := L) (galoisUnitCyclicPeriodBase g hg c).toMul =
      representationCyclicTwoCochainPeriodSum (Rep.ofAlgebraAutOnUnits K L)
        g (orderOf g) c.val := by
  exact galoisGeneratorInvariantBaseEquiv_symm_coefficient g hg _

/-- The original continuous coboundary period is precisely the actual
field norm of the original cochain value at the generator. -/
theorem galoisUnitCyclicPeriodBase_coboundary
    (b : C(Gal(L/K), Rep.ofAlgebraAutOnUnits K L)) :
    galoisUnitCyclicPeriodBase g hg
        (continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits K L)
          (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) b) =
      Additive.ofMul (Units.map (Algebra.norm K (S := L))
        (Additive.toMul (Rep.toAdditive (b g)))) := by
  apply Additive.toMul.injective
  apply galoisUnitsBaseCoefficient_injective (L := L)
  rw [galoisUnitCyclicPeriodBase_coefficient]
  change representationCyclicTwoCochainPeriodSum (Rep.ofAlgebraAutOnUnits K L)
    g (orderOf g) (groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K L) b) = _
  rw [representationCyclicPeriodSum_coboundary_eq_norm
    (Rep.ofAlgebraAutOnUnits K L) g hg]
  exact galoisUnitsNorm_baseCoefficient (Additive.toMul (Rep.toAdditive (b g)))

end
end Dubon2026
