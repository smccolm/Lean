import Dubon2026.OriginalClassH2SubgroupGenerators
import Dubon2026.OriginalFiniteCyclicInvariant

/-! # Original finite class invariants from a full-order class

Actual finite-Galois H2 size bounds and literal restriction/corestriction
derive all subgroup generators. The existing rational cyclic invariant then
supplies normalized injections and exact images, compatible with restriction.
The full-order original class remains an explicit upstream arithmetic input;
this does not yet construct the unconditional DUB-17 class-formation invariant.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory groupCohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A full-order genuine class generates the actual full class H2, using its proved size bound. -/
theorem originalIdeleClass_full_order_generates
    (u : groupCohomology (originalIdeleClassRep K L) 2)
    (hu : addOrderOf u = Module.finrank K L) :
    ∀ x : groupCohomology (originalIdeleClassRep K L) 2,
      x ∈ AddSubgroup.zmultiples u := by
  classical
  obtain ⟨hf, hd⟩ := originalIdeleClass_finiteGalois_second_card_dvd K L
  haveI := hf
  letI : Fintype (groupCohomology (originalIdeleClassRep K L) 2) := Fintype.ofFinite _
  have hlo : Module.finrank K L ≤ Nat.card (groupCohomology (originalIdeleClassRep K L) 2) := by
    rw [← hu, Nat.card_eq_fintype_card]
    exact addOrderOf_le_card_univ
  have hcard := le_antisymm (Nat.le_of_dvd (Module.finrank_pos (R := K) (M := L)) hd) hlo
  have hz : AddSubgroup.zmultiples u = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, hu, hcard])
  intro x
  rw [hz]
  trivial

/-- From one full-order genuine class, construct normalized global and subgroup invariants with exact images and the original restriction-index formula. -/
theorem originalIdeleClass_exists_invariants_of_full_order
    (u : groupCohomology (originalIdeleClassRep K L) 2)
    (hu : addOrderOf u = Module.finrank K L) :
    ∃ invG : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Module.finrank K L • t = 0) ∧
      invG u = ↑((1 : ℚ) / Module.finrank K L) ∧
      ∀ S : Subgroup Gal(L/K),
        ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ),
          Function.Injective invS ∧
          (∀ t : AddCircle (1 : ℚ), t ∈ invS.range ↔ Nat.card S • t = 0) ∧
          ∀ x : groupCohomology (originalIdeleClassRep K L) 2,
            invS ((map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom x) =
              S.index • invG x := by
  have hgen := originalIdeleClass_full_order_generates K L u hu
  obtain ⟨invG, hiG, hrG, hnG⟩ := originalFiniteCyclic_exists_invariant
    u (Module.finrank K L) (Module.finrank_pos (R := K) (M := L)) hu hgen
  have hnG' := hnG 1
  simp only [one_zsmul, Int.cast_one] at hnG'
  refine ⟨invG, hiG, hrG, hnG', fun S => ?_⟩
  let r := (map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom.toAddMonoidHom
  obtain ⟨hcard, hspan⟩ := originalIdeleClass_full_order_restricts_to_generators K L u hu
  have hgS : ∀ x : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2,
      x ∈ AddSubgroup.zmultiples (r u) := by
    intro x
    have hx : x ∈ Submodule.span ℤ {r u} := by
      change x ∈ Submodule.span ℤ
        {(map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom u}
      rw [hspan S]
      trivial
    obtain ⟨j, hj⟩ := Submodule.mem_span_singleton.mp hx
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨j, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℤ j (r u), Int.cast_id]
    exact hj
  have hoS : addOrderOf (r u) = Nat.card S :=
    (addOrderOf_eq_card_of_forall_mem_zmultiples hgS).trans (hcard S)
  obtain ⟨invS, hiS, hrS, hnS⟩ := originalFiniteCyclic_exists_invariant
    (r u) (Nat.card S) Nat.card_pos hoS hgS
  refine ⟨invS, hiS, hrS, fun x => ?_⟩
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen x)
  change invS (r (j • u)) = _
  rw [map_zsmul, hnS, hnG, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  have hd : Module.finrank K L = Nat.card S * S.index :=
    (IsGalois.card_aut_eq_finrank K L).symm.trans S.card_mul_index.symm
  have hs0 : (Nat.card S : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hi0 : (S.index : ℚ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    intro hz
    rw [hz, mul_zero] at hd
    exact (Module.finrank_pos (R := K) (M := L)).ne' hd
  rw [hd]
  push_cast
  field_simp

end
end Dubon2026
