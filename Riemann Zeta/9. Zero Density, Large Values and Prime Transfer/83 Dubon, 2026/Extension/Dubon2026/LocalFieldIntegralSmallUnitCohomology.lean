import Dubon2026.LocalFieldIntegerUnitAction
import Dubon2026.InjectiveUnitCohomologyTransfer
import Dubon2026.LocalFieldIntegralSmallUnits
import Dubon2026.LocalFieldSmallUnitCohomology

/-! # Exact original norm and coboundary preimages in actual integer units -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- The actual compact open normal-lattice field-unit subgroup has a genuine
open preimage in the original integer units. Its original Galois action, finite
quotient, exact invariant norm preimages and exact coboundaries all descend
through the proved coefficient-preserving integer-unit equivalence. -/
theorem localField_exists_integral_small_unit_norm_and_coboundary
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    ∃ V : Subgroup 𝒪[L]ˣ,
      IsOpen (V : Set 𝒪[L]ˣ) ∧ Finite (𝒪[L]ˣ ⧸ V) ∧
      (∀ (σ : Gal(L/K)) (v : 𝒪[L]ˣ), v ∈ V → σ • v ∈ V) ∧
      (∀ u : 𝒪[L]ˣ, u ∈ V → (∀ σ : Gal(L/K), σ • u = u) →
        ∃ v : 𝒪[L]ˣ, v ∈ V ∧ finiteActionUnitNorm Gal(L/K) 𝒪[L]ˣ v = u) ∧
      ∀ c : Gal(L/K) → 𝒪[L]ˣ,
        (∀ σ τ, c (σ * τ) = (σ • c τ) * c σ) → (∀ σ, c σ ∈ V) →
          ∃ v : 𝒪[L]ˣ, v ∈ V ∧ ∀ σ : Gal(L/K), (σ • v) / v = c σ := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  letI := localFieldIntegerUnitMulDistribMulAction K L
  obtain ⟨b, n, U, _, hupper, _, _, hopen, hfinite, hU, hstable, hnorm, hcob⟩ :=
    localField_exists_small_unit_norm_and_coboundary K L π hπ
  let j := Units.map (algebraMap 𝒪[L] L).toMonoidHom
  let V := U.comap j
  have hinj : Function.Injective j := localFieldIntegerUnit_inclusion_injective L
  have heq : ∀ (σ : Gal(L/K)) (v : 𝒪[L]ˣ), j (σ • v) = σ • j v :=
    localFieldIntegerUnit_inclusion_equivariant K L
  have hmem : ∀ v : 𝒪[L]ˣ, v ∈ V ↔ j v ∈ U := fun _ => Iff.rfl
  have honto : ∀ u : Lˣ, u ∈ U → ∃ v : 𝒪[L]ˣ, v ∈ V ∧ j v = u := by
    intro u hu
    let e := localFieldSmallUnitIntegerEquiv K L
      (Submodule.span 𝒪[K] (Set.range b)) (π ^ (n + 1)) hupper U hU
    obtain ⟨v, hv⟩ := e.surjective ⟨u, hu⟩
    refine ⟨v, v.property, ?_⟩
    exact congrArg (fun z : U => (z : Lˣ)) hv
  have hjcont : Continuous j := Continuous.units_map _ continuous_subtype_val
  refine ⟨V, hopen.preimage hjcont, hfinite, ?_, ?_, ?_⟩
  · intro σ v hv
    apply (hmem _).mpr
    rw [heq]
    exact hstable σ (j v) ((hmem v).mp hv)
  · exact injective_unit_norm_preimages j hinj heq V U hmem honto hnorm
  · exact injective_unit_cocycle_preimages j hinj heq V U hmem honto hcob

end
end Dubon2026
