import Dubon2026.RepresentationCarryCharacterPeriod
import Dubon2026.GaloisUnitCarryCocycle

/-! # Original field-unit carry cocycles for arbitrary finite cyclic characters -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ)

/-- The literal addition carry of an actual cyclic character gives a
continuous original Galois-unit cocycle with the actual base-unit coefficient. -/
def galoisUnitCharacterCarryCocycle :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L) :=
  ⟨representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L) χ
    (galoisUnitsBaseCoefficient u) (galoisUnitsBaseCoefficient_fixed u),
    continuous_of_discreteTopology⟩

variable [IsCyclic Gal(L/K)] (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)
attribute [local instance] IsCyclic.commGroup

/-- The descended original period is exactly the actual sum of carries
times the original base unit; the character need not send the generator to one. -/
theorem galoisUnitCharacterCarryCocycle_period :
    galoisUnitCyclicPeriodBase g hg (galoisUnitCharacterCarryCocycle χ u) =
      (∑ i ∈ Finset.range (orderOf g),
        zmodAdditionCarry (i • (χ g).toAdd) (χ g).toAdd) • Additive.ofMul u := by
  apply Additive.toMul.injective
  apply galoisUnitsBaseCoefficient_injective (L := L)
  rw [galoisUnitCyclicPeriodBase_coefficient]
  change representationCyclicTwoCochainPeriodSum (Rep.ofAlgebraAutOnUnits K L) g
    (orderOf g) (representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L) χ
      (galoisUnitsBaseCoefficient u) (galoisUnitsBaseCoefficient_fixed u)) = _
  rw [representationCarryCocycle_period_character]
  exact (map_nsmul (Units.map (algebraMap K L).toMonoidHom).toAdditive
    _ (Additive.ofMul u)).symm

/-- The actual period, multiplied by the character modulus, equals the
group period times the character value times the genuine original base unit. -/
theorem galoisUnitCharacterCarryCocycle_period_mul :
    n • galoisUnitCyclicPeriodBase g hg (galoisUnitCharacterCarryCocycle χ u) =
      (orderOf g * (χ g).toAdd.val) • Additive.ofMul u := by
  rw [galoisUnitCharacterCarryCocycle_period, smul_smul]
  have hz : orderOf g • (χ g).toAdd = 0 := by
    have h := congrArg (fun x => (χ x).toAdd) (pow_orderOf_eq_one g)
    simpa only [map_pow, toAdd_pow, map_one, toAdd_one] using h
  rw [zmodAdditionCarry_sum_period _ _ hz]

end
end Dubon2026
