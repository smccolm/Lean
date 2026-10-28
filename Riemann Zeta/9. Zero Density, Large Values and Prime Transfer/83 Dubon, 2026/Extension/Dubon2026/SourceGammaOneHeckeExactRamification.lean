import Dubon2026.SourceGammaOneHeckeAllFibers

/-! DUB17/18 -> actual Gamma1 Picard/Hecke comparison -> exact fiber multiplicities.
The proved all-fiber bijection and fixed field degree force equality in every
native ramification bound. This gives the precise stabilizer normalization on
the actual intersection curve at all points, including elliptic points. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups IntermediateField GammaOne

theorem sum_analytic_fiber_orders_eq_index (M d : ℕ) [NeZero M] [NeZero d]
    (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ) [Fintype (OrbitQuot M d τ)] :
    (∑ q : OrbitQuot M d τ, (analyticPlace hT (HeckeFiberOrbits.rep M d τ q)).ord
      (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ -
        algebraMap ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (JMultiplicity.jf τ))) =
      ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).index : ℤ) := by
  rw [sum_orders M d hT τ, sum_j_fiber_orders_eq_finrank hT, finrank_over_j_eq_index M d hT]

theorem two_mul_ramification_eq_stabilizer_card (M d : ℕ) [NeZero M] [NeZero d]
    (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ) :
    2 * analyticRamification hT τ = Nat.card (MulAction.stabilizer (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) τ) := by
  classical
  haveI := finite_orbitQuot M d τ
  letI : Fintype (OrbitQuot M d τ) := Fintype.ofFinite _
  have hle : ∀ q ∈ (Finset.univ : Finset (OrbitQuot M d τ)),
      (analyticPlace hT (HeckeFiberOrbits.rep M d τ q)).ord
        (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ -
          algebraMap ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (JMultiplicity.jf τ)) ≤
        ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).relIndex (MulAction.stabilizer SL(2, ℤ) (HeckeFiberOrbits.rep M d τ q)) : ℤ) := by
    intro q _
    have h := (analytic_j_order_le_relative_index hT (HeckeFiberOrbits.rep M d τ q)).2.1
    rwa [j_rep] at h
  have hsum := (sum_analytic_fiber_orders_eq_index M d hT τ).trans
    (sum_relative_indices_eq_index M d τ).symm
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  let q₀ : OrbitQuot M d τ := Quotient.mk _ ⟨τ, MulAction.mem_orbit_self τ⟩
  obtain ⟨γ, hγ, hγτ⟩ := OrbitCounting.exists_smul_out_eq
    (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) τ ⟨τ, MulAction.mem_orbit_self τ⟩
  have hsm : γ • HeckeFiberOrbits.rep M d τ q₀ = τ := hγτ
  have hplace : analyticPlace hT (HeckeFiberOrbits.rep M d τ q₀) = analyticPlace hT τ := by
    rw [← analyticPlace_smul_plusMinus hT hγ (HeckeFiberOrbits.rep M d τ q₀), hsm]
  have hrel : (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).relIndex
      (MulAction.stabilizer SL(2, ℤ) (HeckeFiberOrbits.rep M d τ q₀)) =
      (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).relIndex (MulAction.stabilizer SL(2, ℤ) τ) := by
    rw [← OrbitCounting.relIndex_stabilizer_smul_of_mem
      (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) hγ (HeckeFiberOrbits.rep M d τ q₀), hsm]
  apply (analytic_j_order_le_relative_index hT τ).2.2
  have h := heq q₀ (Finset.mem_univ _)
  rwa [hplace, hrel] at h

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
