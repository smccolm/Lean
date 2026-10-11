import Dubon2026.GaloisUnitCyclicPeriodBase
import Dubon2026.ContinuousCyclicGaloisNormQuotient

/-! # The original cyclic period sum induces a genuine continuous H2 norm-quotient map -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The actual cocycle period map descends through the original continuous
coboundaries into the actual base-unit quotient by original field norms.
Bijectivity and comparison with the periodic-resolution map are separate. -/
def cyclicGaloisH2PeriodNormMap :
    GaloisUnitContinuousH2 (K := K) (Ω := L) →ₗ[ℤ]
      (Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L))) :=
  (continuousRepresentationCoboundariesTwo (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L))).liftQ
      ((LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L))).mkQ.comp
        (galoisUnitCyclicPeriodBase g hg)) (by
          rintro _ ⟨b, rfl⟩
          change (Submodule.Quotient.mk (galoisUnitCyclicPeriodBase g hg
            (continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits K L)
              (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) b)) :
            Additive Kˣ ⧸ LinearMap.range
              (galoisUnitFieldNormLinear (K := K) (L := L))) = 0
          rw [galoisUnitCyclicPeriodBase_coboundary]
          apply (Submodule.Quotient.mk_eq_zero _).mpr
          exact ⟨Rep.toAdditive (b g), rfl⟩)

/-- The genuine continuous H2 map keeps the exact original cocycle period. -/
theorem cyclicGaloisH2PeriodNormMap_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    cyclicGaloisH2PeriodNormMap g hg (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (galoisUnitCyclicPeriodBase g hg c) := by
  rfl

end
end Dubon2026
