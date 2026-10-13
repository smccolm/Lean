import Dubon2026.UnramifiedLocalFieldZeroOrderNorm
import Dubon2026.LocalFieldUnitValuationSequence
import Dubon2026.GaloisUnitInvariantBaseDescent

/-! # Actual invariant norm preimages in unramified local integer units

Original fixed-field descent takes an invariant integer unit to an
actual base-field unit. The valuation-extension identity proves it is
an integer unit. The already proved unramified complete-local unit norm
and original norm naturality provide its integer-unit norm preimage.
This is the vanishing input for the outside-support local factors in
DUB-17's supported-idele cohomology calculation.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped ValuativeRel
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- Every invariant original integer unit of an unramified local Galois extension is an actual original representation norm. -/
theorem unramified_integer_unit_norm_preimages :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x := by
  letI : FiniteDimensional K L := localField_field_module_finite
  letI := localFieldIntegerUnitMulDistribMulAction K L
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  haveI : Module.Free 𝒪[K] 𝒪[L] := Module.free_of_finite_type_torsion_free'
  haveI : Finite (𝒪[K] ⧸ IsLocalRing.maximalIdeal 𝒪[K]) := inferInstanceAs (Finite 𝓀[K])
  let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
  let B := Rep.ofAlgebraAutOnUnits K L
  let f : A ⟶ B := (localFieldUnitValuationShortComplex K L).f
  change ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x
  intro x hx
  have hfixed : f.hom x ∈ B.ρ.invariants := by
    intro σ
    rw [← Rep.hom_comm_apply f, hx σ]
  obtain ⟨u, hu⟩ := galoisUnitInvariant_exists_base (f.hom x) hfixed
  have huval : algebraMap K L u.val = algebraMap 𝒪[L] L x.toMul.val :=
    congrArg (fun z : B => ((Additive.toMul (Rep.toAdditive z) : Lˣ) : L)) hu
  have hvL : ValuativeRel.valuation L (algebraMap K L u.val) = 1 := by
    rw [huval]
    exact (Valuation.integer.integers (ValuativeRel.valuation L)).valuation_unit x.toMul
  have hvK := (Valuation.HasExtension.val_map_eq_one_iff
    (ValuativeRel.valuation K) (ValuativeRel.valuation L) u.val).mp hvL
  obtain ⟨a, ha⟩ := (localFieldUnitOrder_eq_zero_iff_integer_unit K u).mp
    ((localFieldUnitOrder_eq_zero_iff K u).mpr hvK)
  obtain ⟨b, hb⟩ := unramifiedLocal_exists_fraction_field_unit_norm
    (R := 𝒪[K]) (S := 𝒪[L]) (K := K) (L := L) a
  refine ⟨Additive.ofMul b, ?_⟩
  have hinj : Function.Injective f.hom := by
    intro x y h
    apply Additive.toMul.injective
    exact localFieldIntegerUnit_inclusion_injective L (congrArg Additive.toMul h)
  apply hinj
  calc
    f.hom (A.norm.hom (Additive.ofMul b)) = B.norm.hom (f.hom (Additive.ofMul b)) :=
      (congrArg (fun t : A ⟶ B => t.hom (Additive.ofMul b)) (Rep.norm_comm f)).symm
    _ = galoisUnitsBaseCoefficient (L := L)
        (Units.map (Algebra.norm K (S := L)) (Units.map (algebraMap 𝒪[L] L).toMonoidHom b)) :=
      galoisUnitsNorm_baseCoefficient _
    _ = galoisUnitsBaseCoefficient (L := L) u := by rw [hb, ha]
    _ = f.hom x := hu

end
end Dubon2026
