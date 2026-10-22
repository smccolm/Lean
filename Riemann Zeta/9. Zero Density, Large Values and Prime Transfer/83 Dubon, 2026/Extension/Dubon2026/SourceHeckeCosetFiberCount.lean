import Dubon2026.SourceHeckeFiberStabilizer

/-! DUB-17/18 -> original Picard-period Hecke comparison -> divisor
fiber multiplicities. Use the actual subgroup quotient as transversal;
this avoids another explicit prime-representative classification.
-/
namespace Dubon2026.HeckeFiber
noncomputable section
open MulAction
variable {G X : Type*} [Group G] [MulAction G X]

theorem card_stabilizer_eq_coset_filter_mul (H : Subgroup G) [Fintype (G ⧸ H)]
    (y x : X) (g₀ : G) (hg₀ : g₀ • y = x)
    [DecidablePred fun q : G ⧸ H => q.out⁻¹ • y ∈ orbit H x] :
    Nat.card (stabilizer G x) =
      (Finset.univ.filter fun q : G ⧸ H => q.out⁻¹ • y ∈ orbit H x).card *
        Nat.card (stabilizer H x) := by
  classical
  apply card_stabilizer_eq_card_filter_mul H (fun q : G ⧸ H => q.out⁻¹)
    Finset.univ ?_ ?_ y x g₀ hg₀
  · intro g
    refine ⟨QuotientGroup.mk (g⁻¹), Finset.mem_univ _, ?_⟩
    have he : (QuotientGroup.mk (g⁻¹) : G ⧸ H) =
        QuotientGroup.mk ((QuotientGroup.mk (g⁻¹) : G ⧸ H).out) :=
      (Quotient.out_eq _).symm
    simpa only [inv_inv] using QuotientGroup.eq.mp he
  · intro i _ j _ hij
    have he : (QuotientGroup.mk i.out : G ⧸ H) = QuotientGroup.mk j.out :=
      QuotientGroup.eq.mpr (by simpa only [inv_inv] using hij)
    simpa only [Quotient.out_eq] using he

end
end Dubon2026.HeckeFiber
