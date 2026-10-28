import Dubon2026.SourceGammaOneHeckeGenericFiber
import Dubon2026.SourceGammaOneJFiberDegree
import Dubon2026.SourceAnalyticJSurjectivity

/-! DUB17/18 -> actual Gamma1 Picard/Hecke comparison -> exact geometric fibers.
The actual generic fiber fixes the field degree over j as the intersection
subgroup index. Reuse native j-surjectivity, order bounds and fixed fiber degree.
This removes a new modular-form separation/degree development for the Hecke curve. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups StabilizerCharacter SubgroupStabilizer GammaOne IntermediateField

private theorem exists_card_stabilizer_two :
    ∃ τ : ℍ, Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = 2 := by
  obtain ⟨τ, hj⟩ := JMultiplicity.jf_surjective 1
  have h4 : ModularForm.E₄ τ ≠ 0 := by
    intro hz
    have h := hj
    change ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ = 1 at h
    rw [hz, zero_pow (by decide : 3 ≠ 0), zero_div] at h
    exact zero_ne_one h
  have h6 : ModularForm.E₆ τ ≠ 0 := by
    intro hz
    have h := (JMultiplicity.jf_eq_of_E₆_eq_zero hz).symm.trans hj
    norm_num at h
  exact ⟨τ, (JMultiplicity.case_generic h4 h6).2⟩

theorem sum_relative_indices_eq_index (M d : ℕ) [NeZero M] [NeZero d] (τ : ℍ)
    [Fintype (OrbitQuot M d τ)] :
    (∑ q : OrbitQuot M d τ,
      ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).relIndex (MulAction.stabilizer SL(2, ℤ) (rep M d τ q)) : ℤ)) =
        ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).index : ℤ) := by
  have h := OrbitCounting.finsum_relIndex_stabilizer_eq_index (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) τ
  rw [finsum_eq_sum_of_fintype] at h
  exact_mod_cast h

theorem exists_fiber_order_sum_eq_index (M d : ℕ) [NeZero M] [NeZero d]
    (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) :
    ∃ τ : ℍ, (∑ᶠ P : Fiber M d τ, P.1.ord (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ -
      algebraMap ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (JMultiplicity.jf τ))) =
        ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).index : ℤ) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_card_stabilizer_two
  haveI := finite_orbitQuot M d τ
  letI : Fintype (OrbitQuot M d τ) := Fintype.ofFinite _
  refine ⟨τ, ?_⟩
  rw [← sum_orders_of_generic M d hT τ hτ, ← sum_relative_indices_eq_index M d τ]
  apply Finset.sum_congr rfl
  intro q _
  have hs := two_le_card_stabilizer_plusMinus (Gamma1 M ⊓ Gamma0 (d * M)) (rep M d τ q)
  have hb := OrbitCounting.relIndex_stabilizer_mul_card_stabilizer
    (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) (rep M d τ q)
  rw [card_stabilizer_rep, hτ] at hb
  have hle : (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).relIndex
      (MulAction.stabilizer SL(2, ℤ) (rep M d τ q)) ≤ 1 := by nlinarith
  have hle' : ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).relIndex
      (MulAction.stabilizer SL(2, ℤ) (rep M d τ q)) : ℤ) ≤ 1 := by exact_mod_cast hle
  have hp := analytic_j_order_le_relative_index hT (rep M d τ q)
  rw [j_rep] at hp
  omega

theorem finrank_over_j_eq_index (M d : ℕ) [NeZero M] [NeZero d]
    (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) :
    Module.finrank ℂ⟮jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ⟯
      (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) =
        (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).index := by
  obtain ⟨τ, hτ⟩ := exists_fiber_order_sum_eq_index M d hT
  have h := sum_j_fiber_orders_eq_finrank hT (JMultiplicity.jf τ)
  exact_mod_cast h.symm.trans hτ

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
