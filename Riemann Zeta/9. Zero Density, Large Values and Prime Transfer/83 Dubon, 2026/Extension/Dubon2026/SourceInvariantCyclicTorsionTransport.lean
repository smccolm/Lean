import Dubon2026.SourceCyclicTorsionTransport

/-! DUB-17/18 -> reverse genus -> exceptional j-fiber counts ->
fixed cyclic subgroups of the prescribed elliptic automorphisms.
Reuse the existing injective cyclic-subgroup transport. Intertwining the
actual torsion action transports the fixed-subgroup condition as well;
full target torsion discharges the range condition. -/
namespace Dubon2026.SourceQuadraticCyclicCount
open SourceEllipticCyclicCount
noncomputable section

theorem stable_cyclic_subgroup_card_transport
    (n : ℕ) {M A : Type*} [AddCommGroup M] [AddCommGroup A]
    (ι : M →+ A) (hι : Function.Injective ι)
    (hr : ∀ a : A, n • a = 0 → a ∈ ι.range)
    (τ : M →+ M) (σ : A →+ A) (hcomm : ι.comp τ = σ.comp ι) :
    Nat.card {H : AddSubgroup M // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H} =
      Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H} := by
  have hm (H : AddSubgroup M) (hH : IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H) :
      IsAddCyclic (H.map ι) ∧ Nat.card (H.map ι) = n ∧ (H.map ι).map σ = H.map ι := by
    obtain ⟨hc, hn, _hrange⟩ := isAddCyclic_map_and_card_of_injective n ι hι ⟨hH.1, hH.2.1⟩
    refine ⟨hc, hn, ?_⟩
    rw [AddSubgroup.map_map, ← hcomm, ← AddSubgroup.map_map, hH.2.2]
  refine Nat.card_eq_of_bijective (fun H => ⟨H.val.map ι, hm H.val H.property⟩) ⟨?_, ?_⟩
  · intro H H' he
    exact Subtype.ext (AddSubgroup.map_injective hι (congrArg Subtype.val he))
  · intro H
    have hle : H.val ≤ ι.range := le_of_card_eq_of_nsmul_mem n H.property.2.1 hr
    obtain ⟨C, hC⟩ := (cyclicAddSubgroupMapEquiv n ι hι).surjective
      ⟨H.val, H.property.1, H.property.2.1, hle⟩
    have he : C.val.map ι = H.val := congrArg Subtype.val hC
    have hstable : C.val.map τ = C.val := by
      apply AddSubgroup.map_injective hι
      rw [AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map, he, H.property.2.2]
    exact ⟨⟨C.val, C.property.1, C.property.2, hstable⟩, Subtype.ext he⟩

end
end Dubon2026.SourceQuadraticCyclicCount
