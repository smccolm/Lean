import Dubon2026.ScalarNormalLatticeQuotient
import Dubon2026.SmallUnitGradedQuotient

/-! # The original Galois-equivariant unit difference map on a normal lattice -/

namespace Dubon2026
noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (U : Subgroup Lˣ)
  (hstable : ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
    Units.map (σ : L →+* L).toMonoidHom u ∈ U)

/-- Restrict the original field automorphism on units to the actual stable subgroup. -/
def galoisUnitSubgroupMap (σ : Gal(L/K)) : U →* U where
  toFun u := ⟨Units.map (σ : L →+* L).toMonoidHom u, hstable σ u u.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext
    (map_mul (Units.map (σ : L →+* L).toMonoidHom) (u : Lˣ) (v : Lˣ))

/-- The actual original Galois action restricted to its stable unit subgroup. -/
@[reducible]
def galoisUnitSubgroupMulDistribMulAction : MulDistribMulAction Gal(L/K) U where
  smul σ u := galoisUnitSubgroupMap K L U hstable σ u
  one_smul _ := Subtype.ext (Units.ext rfl)
  mul_smul _ _ _ := Subtype.ext (Units.ext rfl)
  smul_one σ := map_one (galoisUnitSubgroupMap K L U hstable σ)
  smul_mul σ u v := map_mul (galoisUnitSubgroupMap K L U hstable σ) u v

variable (R : Type) [CommRing R] [IsDomain R]
  [Algebra R K] [IsFractionRing R K] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1)) (r s : R)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
    scalarLatticeImage (Submodule.span R (Set.range b)) r)
  (hmul : ∀ x ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    ∀ y ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    x * y ∈ scalarLatticeImage
      (scalarLatticeImage (Submodule.span R (Set.range b)) r) s)

/-- The original difference-from-one homomorphism into the actual scalar
normal-lattice quotient, using the proved equality of its literal kernels. -/
def normalLatticeUnitGradedMap :
    Additive U →+ repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s :=
  (Submodule.quotEquivOfEq _ _
    (lattice_scalar_range_eq_comap
      (scalarLatticeImage (Submodule.span R (Set.range b)) r) s).symm).toAddEquiv.toAddMonoidHom.comp
    (smallUnitGradedMap (scalarLatticeImage (Submodule.span R (Set.range b)) r)
      (scalarLatticeImage (scalarLatticeImage (Submodule.span R (Set.range b)) r) s)
      U hU hmul)

omit [IsDomain R] [IsFractionRing R K] [FiniteDimensional K L] [IsGalois K L] in
/-- The genuine scalar quotient map evaluates to the literal original unit
minus one, with no change of representatives or coefficient action. -/
theorem normalLatticeUnitGradedMap_apply (u : Additive U) :
    normalLatticeUnitGradedMap K L U R b hb r s hU hmul u =
      (repScalarRange (scalarNormalLatticeRep R K L b hb r) s).mkQ
        (smallUnitDifference
          (scalarLatticeImage (Submodule.span R (Set.range b)) r) U hU u) := rfl

omit [IsDomain R] [IsFractionRing R K] [FiniteDimensional K L] [IsGalois K L] in
/-- The original unit difference map commutes with the actual Galois action
on its same scalar normal lattice and quotient. -/
theorem normalLatticeUnitGradedMap_equivariant (σ : Gal(L/K)) (u : Additive U) :
    normalLatticeUnitGradedMap K L U R b hb r s hU hmul
        ((galoisUnitSubgroupMap K L U hstable σ).toAdditive u) =
      (repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s).ρ σ
        (normalLatticeUnitGradedMap K L U R b hb r s hU hmul u) := by
  rw [normalLatticeUnitGradedMap_apply, normalLatticeUnitGradedMap_apply]
  change (repScalarRange (scalarNormalLatticeRep R K L b hb r) s).mkQ _ =
    (repScalarRange (scalarNormalLatticeRep R K L b hb r) s).mkQ _
  congr 1
  apply Subtype.ext
  change σ (((Additive.toMul u : U) : Lˣ) : L) - 1 =
    σ (((((Additive.toMul u : U) : Lˣ) : L) - 1))
  rw [map_sub, map_one]

omit [IsDomain R] [IsFractionRing R K] [FiniteDimensional K L] [IsGalois K L] in
/-- Actual original one-plus-lattice units give every class in the same
Galois scalar quotient; no quotient surjectivity is assumed. -/
theorem normalLatticeUnitGradedMap_surjective
    (hunit : ∀ a ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
      (1 : L) + a ≠ 0) :
    Function.Surjective (normalLatticeUnitGradedMap K L U R b hb r s hU hmul) := by
  exact (Submodule.quotEquivOfEq _ _
    (lattice_scalar_range_eq_comap
      (scalarLatticeImage (Submodule.span R (Set.range b)) r) s).symm).surjective.comp
    (smallUnitGradedMap_surjective
      (scalarLatticeImage (Submodule.span R (Set.range b)) r)
      (scalarLatticeImage (scalarLatticeImage (Submodule.span R (Set.range b)) r) s)
      U hU hmul hunit)

omit [IsDomain R] [IsFractionRing R K] [FiniteDimensional K L] [IsGalois K L] in
/-- The actual equivariant difference map has exactly the original next
scalar lattice as its unit kernel. -/
theorem normalLatticeUnitGradedMap_eq_zero_iff (u : Additive U) :
    normalLatticeUnitGradedMap K L U R b hb r s hU hmul u = 0 ↔
      (((Additive.toMul u : U) : Lˣ) : L) - 1 ∈
        scalarLatticeImage (scalarLatticeImage (Submodule.span R (Set.range b)) r) s := by
  rw [normalLatticeUnitGradedMap_apply]
  change (Submodule.Quotient.mk
    (smallUnitDifference (scalarLatticeImage (Submodule.span R (Set.range b)) r) U hU u) :
    scalarLatticeImage (Submodule.span R (Set.range b)) r ⧸
      repScalarRange (scalarNormalLatticeRep R K L b hb r) s) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change _ ∈ LinearMap.range (s • (LinearMap.id :
    scalarLatticeImage (Submodule.span R (Set.range b)) r →ₗ[R]
      scalarLatticeImage (Submodule.span R (Set.range b)) r)) ↔ _
  rw [lattice_scalar_range_eq_comap]
  rfl

end
end Dubon2026
