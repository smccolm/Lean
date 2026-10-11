import Dubon2026.CyclicGaloisH2PeriodSurjective
import Dubon2026.LocalFieldArithmeticH2Normalization

/-! # The literal arithmetic-Frobenius cocycle period computes original unramified H2 -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

/-- The exact original cocycle-period map is an equivalence, using actual
arithmetic Frobenius and actual normalized order. The existing cyclic
cohomology computation supplies cardinality only, without identifying maps. -/
def localFieldPeriodH2Equiv :
    GaloisUnitContinuousH2 (K := K) (Ω := L) ≃ₗ[ℤ] ZMod (Module.finrank K L) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  haveI : Finite (Additive Kˣ ⧸
      LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := L))) :=
    Finite.of_equiv (ZMod (Module.finrank K L))
      (unramifiedLocalNormQuotientEquiv (K := K) (L := L)).symm.toEquiv
  exact (LinearEquiv.ofBijective
    (cyclicGaloisH2PeriodNormMap (localFieldArithmeticFrobenius K L)
      (localFieldArithmeticFrobenius_generates K L))
    (cyclicGaloisH2PeriodNormMap_bijective (localFieldArithmeticFrobenius K L)
      (localFieldArithmeticFrobenius_generates K L))).trans
        (unramifiedLocalNormQuotientEquiv (K := K) (L := L))

/-- Its value on the genuine original continuous cocycle is precisely
the original normalized order of its actual arithmetic-Frobenius period. -/
theorem localFieldPeriodH2Equiv_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    localFieldPeriodH2Equiv K L (Submodule.Quotient.mk c) =
      (localFieldUnitOrder K (galoisUnitCyclicPeriodBase
        (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) c) :
          ZMod (Module.finrank K L)) := by
  rfl

end
end Dubon2026
