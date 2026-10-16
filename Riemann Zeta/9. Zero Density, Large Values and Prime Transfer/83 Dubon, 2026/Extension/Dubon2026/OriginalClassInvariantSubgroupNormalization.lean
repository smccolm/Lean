import Dubon2026.OriginalFiniteCyclicNormalizedHom

/-! # Normalize actual subgroup invariants by the prescribed global invariant

The existing original restriction and subgroup-generator theorem supplies
the subgroup maps. Agreement on the full-order original generator identifies
its chosen global invariant with the prescribed one. This discharges the
subgroup normalization input, preserving the actual full-idele total in the
next arithmetic application on DUB-17's finite class-invariant chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Actual subgroup invariants normalize against any prescribed original class invariant with the positive reciprocal-degree value on the same full-order generator. -/
theorem originalIdeleClass_subgroup_invariants_of_normalized
    (u : groupCohomology (originalIdeleClassRep K L) 2)
    (hu : addOrderOf u = Module.finrank K L)
    (f : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ))
    (hf : f u = ↑((1 : ℚ) / Module.finrank K L))
    (S : Subgroup Gal(L/K)) :
    ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invS ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invS.range ↔ Nat.card S • t = 0) ∧
      ∀ x : groupCohomology (originalIdeleClassRep K L) 2,
        invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom x) =
          S.index • f x := by
  obtain ⟨g, _, _, hg, hS⟩ := originalIdeleClass_exists_invariants_of_full_order K L u hu
  have he : g = f := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp
      (originalIdeleClass_full_order_generates K L u hu x)
    rw [map_zsmul, map_zsmul, hg, hf]
  obtain ⟨invS, hi, hr, hs⟩ := hS S
  refine ⟨invS, hi, hr, fun x => ?_⟩
  exact (hs x).trans (congrArg (fun a => S.index • a) (congrArg (fun h => h x) he))

end
end Dubon2026
