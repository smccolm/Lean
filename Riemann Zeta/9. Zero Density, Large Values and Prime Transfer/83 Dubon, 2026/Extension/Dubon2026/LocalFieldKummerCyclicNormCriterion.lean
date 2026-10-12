import Dubon2026.ContinuousFiniteCharacterCarryInflation

/-! # The actual local Kummer cup has the original cyclic norm kernel

This closes the bridge from the original cohomology cup to the proved finite
cyclic norm quotient. General finite-module local perfectness remains separate.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(E/K)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := K) (Ω := Ω) (Nat.card Gal(E/K)))]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := K) (Ω := Ω) (Nat.card Gal(E/K)))]
  (g : Gal(E/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

attribute [local instance] IsCyclic.commGroup

/-- For a nontrivial actual cyclic local extension, cup with its actual generator
character vanishes exactly on norms of actual extension-field units. -/
theorem localFieldKummer_generatorCup_zero_iff_norm
    (hn : 1 < Nat.card Gal(E/K)) (a : Kˣ) :
    letI : NeZero (Nat.card Gal(E/K)) := ⟨Nat.card_pos.ne'⟩
    continuousGaloisRootCharacterH1Cup (Nat.card Gal(E/K))
      (finiteGaloisCharacterInflation E (galoisUnitGeneratorIndex g hg))
      (galoisKummerH1Class (Nat.card Gal(E/K)) a) = 0 ↔
        ∃ u : Eˣ, Units.map (Algebra.norm K (S := E)) u = a := by
  letI : NeZero (Nat.card Gal(E/K)) := ⟨Nat.card_pos.ne'⟩
  rw [continuousKummerH1Cup_inflated_eq_zero_iff]
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  let e := localFieldFiniteCyclicNormPeriodEquiv K Ω E g hg
  have he : e (localFieldFiniteCharacterCarryClass K Ω E (galoisUnitGeneratorIndex g hg) a) =
      Submodule.Quotient.mk (Additive.ofMul a) := by
    change cyclicGaloisH2PeriodNormMap g hg
      (Submodule.Quotient.mk (galoisUnitCarryCocycle g hg a)) = _
    rw [cyclicGaloisH2PeriodNormMap_mk, galoisUnitCarryCocycle_period g hg a hn]
  have hz : localFieldFiniteCharacterCarryClass K Ω E (galoisUnitGeneratorIndex g hg) a = 0 ↔
      (Submodule.Quotient.mk (Additive.ofMul a) :
        Additive Kˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := K) (L := E))) = 0 := by
    constructor
    · intro h
      rw [← he, h, e.map_zero]
    · intro h
      apply e.injective
      rw [he, h, e.map_zero]
  rw [hz, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.toMul, congrArg Additive.toMul hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩

/-- Every nontrivial actual finite cyclic local character detects an actual
Kummer class. Surjectivity of the proved original norm-residue map supplies
the base unit, so nondegeneracy in this cyclic case is not an assumption. -/
theorem localFieldKummer_generatorCup_exists_nonzero
    (hn : 1 < Nat.card Gal(E/K)) :
    letI : NeZero (Nat.card Gal(E/K)) := ⟨Nat.card_pos.ne'⟩
    ∃ a : Kˣ, continuousGaloisRootCharacterH1Cup (Nat.card Gal(E/K))
      (finiteGaloisCharacterInflation E (galoisUnitGeneratorIndex g hg))
      (galoisKummerH1Class (Nat.card Gal(E/K)) a) ≠ 0 := by
  letI : NeZero (Nat.card Gal(E/K)) := ⟨Nat.card_pos.ne'⟩
  haveI : Nontrivial Gal(E/K) := by
    by_contra h
    haveI : Subsingleton Gal(E/K) := not_nontrivial_iff_subsingleton.mp h
    have hc : Nat.card Gal(E/K) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    omega
  obtain ⟨σ, hσ⟩ := exists_ne (1 : Gal(E/K))
  obtain ⟨u, hu⟩ := localFieldFiniteCyclicNormResidue_surjective K Ω E g hg (Additive.ofMul σ)
  refine ⟨u.toMul, ?_⟩
  intro hz
  have hnorm := (localFieldKummer_generatorCup_zero_iff_norm K Ω E g hg hn u.toMul).mp hz
  have hu0 := (localFieldFiniteCyclicNormResidue_eq_zero_iff K Ω E g hg u).mpr hnorm
  exact hσ (hu.symm.trans hu0)

end
end Dubon2026
