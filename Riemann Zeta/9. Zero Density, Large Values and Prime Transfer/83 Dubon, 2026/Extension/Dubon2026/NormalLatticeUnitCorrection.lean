import Dubon2026.NormalLatticeUnitGradedMap
import Dubon2026.UnitGradedCorrection

/-! # Original normal-lattice unit corrections modulo the next scalar level -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
  (b : Module.Basis Gal(L/K) K L) (hb : ∀ σ, b σ = σ (b 1))
  (r s : R) (hr : r ≠ 0) (hs : s ≠ 0) (U : Subgroup Lˣ)
  (hstable : ∀ (σ : Gal(L/K)) (u : Lˣ), u ∈ U →
    Units.map (σ : L →+* L).toMonoidHom u ∈ U)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈
    scalarLatticeImage (Submodule.span R (Set.range b)) r)
  (hmul : ∀ x ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    ∀ y ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    x * y ∈ scalarLatticeImage
      (scalarLatticeImage (Submodule.span R (Set.range b)) r) s)
  (hunit : ∀ a ∈ scalarLatticeImage (Submodule.span R (Set.range b)) r,
    (1 : L) + a ≠ 0)

include hb hr hs hU hmul hunit in
omit [IsGalois K L] in
/-- The actual original normal-basis quotient supplies an original unit
coboundary correction, reducing the original multiplicative cocycle to the
next literal scalar lattice. Quotient cohomology vanishing is derived. -/
theorem normalLatticeUnit_cocycle_correction (c : Gal(L/K) → U)
    (hc : ∀ σ τ, c (σ * τ) = galoisUnitSubgroupMap K L U hstable σ (c τ) * c σ) :
    ∃ u : U, ∀ σ : Gal(L/K),
      ((((c σ / (galoisUnitSubgroupMap K L U hstable σ u / u)) : U) : Lˣ) : L) - 1 ∈
        scalarLatticeImage (scalarLatticeImage (Submodule.span R (Set.range b)) r) s := by
  letI := galoisUnitSubgroupMulDistribMulAction K L U hstable
  let Q := repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s
  let f := normalLatticeUnitGradedMap K L U R b hb r s hU hmul
  have hf : ∀ (σ : Gal(L/K)) (u : U),
      f (Additive.ofMul (σ • u)) = Q.ρ σ (f (Additive.ofMul u)) := by
    intro σ u
    exact normalLatticeUnitGradedMap_equivariant K L U hstable R b hb r s hU hmul σ
      (Additive.ofMul u)
  obtain ⟨u, hu⟩ := unitGraded_cocycle_correction Q f hf
    (normalLatticeUnitGradedMap_surjective K L U R b hb r s hU hmul hunit)
    (scalarNormalLatticeQuotient_groupCohomology_isZero R K L b hb r s hr hs 0) c hc
  refine ⟨u, fun σ => ?_⟩
  exact (normalLatticeUnitGradedMap_eq_zero_iff K L U R b hb r s hU hmul _).mp (hu σ)

include hb hr hs hU hmul hunit in
omit [IsGalois K L] in
/-- The actual invariant norm preimages in the original normal-basis quotient
give a unit norm correction with error in the next literal scalar lattice. -/
theorem normalLatticeUnit_norm_correction (u : U)
    (hu : ∀ σ : Gal(L/K), galoisUnitSubgroupMap K L U hstable σ u = u) :
    ∃ v : U,
      ((((u / ∏ σ : Gal(L/K), galoisUnitSubgroupMap K L U hstable σ v) : U) : Lˣ) : L) - 1 ∈
        scalarLatticeImage (scalarLatticeImage (Submodule.span R (Set.range b)) r) s := by
  letI := galoisUnitSubgroupMulDistribMulAction K L U hstable
  let Q := repScalarQuotient (scalarNormalLatticeRep R K L b hb r) s
  let f := normalLatticeUnitGradedMap K L U R b hb r s hU hmul
  have hf : ∀ (σ : Gal(L/K)) (v : U),
      f (Additive.ofMul (σ • v)) = Q.ρ σ (f (Additive.ofMul v)) := by
    intro σ v
    exact normalLatticeUnitGradedMap_equivariant K L U hstable R b hb r s hU hmul σ
      (Additive.ofMul v)
  obtain ⟨v, hv⟩ := unitGraded_norm_correction Q f hf
    (normalLatticeUnitGradedMap_surjective K L U R b hb r s hU hmul hunit)
    (scalarNormalLatticeQuotient_invariant_mem_norm R K L b hb r s hr hs) u hu
  exact ⟨v, (normalLatticeUnitGradedMap_eq_zero_iff K L U R b hb r s hU hmul _).mp hv⟩

end
end Dubon2026
