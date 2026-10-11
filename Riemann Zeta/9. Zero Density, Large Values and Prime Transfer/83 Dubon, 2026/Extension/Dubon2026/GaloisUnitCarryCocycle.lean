import Dubon2026.RepresentationCarryPeriod
import Dubon2026.GaloisUnitCyclicPeriodBase

/-! # Explicit original cyclic Galois cocycles realizing original base-unit periods -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The actual generator-index character of the original finite cyclic Galois group. -/
def galoisUnitGeneratorIndex : Gal(L/K) →* Multiplicative (ZMod (Nat.card Gal(L/K))) :=
  (zmodMulEquivOfGenerator hg rfl).symm.toMonoidHom

omit [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)] in
/-- The actual generator has index one with the selected arithmetic convention. -/
theorem galoisUnitGeneratorIndex_generator :
    galoisUnitGeneratorIndex g hg g = Multiplicative.ofAdd 1 :=
  zmodMulEquivOfGenerator_symm_apply_generator hg rfl

/-- An original base unit gives a genuine continuous cocycle of the original
Galois unit representation by the literal generator-index carry formula. -/
def galoisUnitCarryCocycle (u : Kˣ) :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L) := by
  haveI : NeZero (Nat.card Gal(L/K)) := ⟨Nat.card_pos.ne'⟩
  exact ⟨representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L)
    (galoisUnitGeneratorIndex g hg) (galoisUnitsBaseCoefficient u)
    (galoisUnitsBaseCoefficient_fixed u), continuous_of_discreteTopology⟩

/-- The original carry cocycle has exactly its original base-unit period
for every nontrivial original cyclic Galois extension. -/
theorem galoisUnitCarryCocycle_period (u : Kˣ) (hn : 1 < Nat.card Gal(L/K)) :
    galoisUnitCyclicPeriodBase g hg (galoisUnitCarryCocycle g hg u) = Additive.ofMul u := by
  haveI : NeZero (Nat.card Gal(L/K)) := ⟨Nat.card_pos.ne'⟩
  apply Additive.toMul.injective
  apply galoisUnitsBaseCoefficient_injective (L := L)
  rw [galoisUnitCyclicPeriodBase_coefficient]
  rw [orderOf_eq_card_of_forall_mem_zpowers hg]
  exact representationCarryCocycle_period (Rep.ofAlgebraAutOnUnits K L)
    (galoisUnitGeneratorIndex g hg) (galoisUnitsBaseCoefficient u)
    (galoisUnitsBaseCoefficient_fixed u) g (galoisUnitGeneratorIndex_generator g hg) hn

end
end Dubon2026
