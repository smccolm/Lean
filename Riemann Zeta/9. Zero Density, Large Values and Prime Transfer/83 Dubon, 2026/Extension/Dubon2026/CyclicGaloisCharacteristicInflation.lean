import Dubon2026.FiniteCyclicCharacteristicInflation
import Dubon2026.FiniteGaloisUnitTowerInflation

/-! # Original cyclic Galois towers kill characteristic-q coefficient H2

The finite-group period theorem is applied to the actual restriction of field
automorphisms. Original tower degrees give the required period enlargement.
Unramified local towers will provide the cyclicity and degree input, for
support control in DUB-17's global reciprocity and Selmer duality route.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] IsCyclic.commGroup

variable (K F E : Type) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
  [FiniteDimensional K E] [IsGalois K F] [IsGalois K E] [IsCyclic Gal(E/K)]
  (q : ℕ) [Fact q.Prime]
  (A : Rep (ZMod q) Gal(F/K)) [Finite A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(F/K) × A => A.ρ z.1 z.2))

/-- In a genuine finite cyclic Galois tower whose relative degree is the
coefficient characteristic, inflation along original field restriction
kills every original finite-coefficient continuous H2 class. -/
theorem cyclicGaloisCharacteristicH2Inflation_eq_zero
    (hdegree : Module.finrank F E = q) (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (AlgEquiv.restrictNormalHom F : Gal(E/K) →* Gal(F/K))
      continuous_of_discreteTopology x = 0 := by
  haveI : FiniteDimensional K F := FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom K F E).toLinearMap (algebraMap F E).injective
  obtain ⟨h, hh⟩ := IsCyclic.exists_generator (α := Gal(E/K))
  let φ : Gal(E/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  let g := φ h
  have hn : g ^ Module.finrank K F = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one' (x := g)
  have ho : orderOf h = Module.finrank K F * q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hh, IsGalois.card_aut_eq_finrank,
      ← Module.finrank_mul_finrank K F E, hdegree]
  exact finiteCyclicCharacteristicH2Inflation_eq_zero q A hA φ g h hh rfl
    (Module.finrank K F) hn (Module.finrank_pos) ho x

end
end Dubon2026
