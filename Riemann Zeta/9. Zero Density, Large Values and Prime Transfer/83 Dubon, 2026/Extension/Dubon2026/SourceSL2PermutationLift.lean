import Dubon2026.SourceSL2CocycleExt
import Dubon2026.SourcePermutationPotential

/-! DUB-17/18 -> residual Galois association -> integral weight-two lifting.
The native modular-group cocycle is lifted through a surjection of additive
coefficient groups. Stabilizer vanishing on finite-order elements supplies
the two generator potentials; the existing modular relations and cocycle
extension theorem replace the external free-product construction.
-/

namespace Dubon2026
noncomputable section
open scoped MatrixGroups
open Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup groupCohomology

variable (M : ℕ) {A B : Type} [AddCommGroup A] [AddCommGroup B]

private theorem additivePermutation_S_sq (f : (SL(2, ℤ) ⧸ Gamma0 M) → A) :
    sourceAdditivePermutationRep SL(2, ℤ) _ A S
      (sourceAdditivePermutationRep SL(2, ℤ) _ A S f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, SourceSL2Cocycle.S_mul_S]
  funext q
  change f ((-1 : SL(2, ℤ))⁻¹ • q) = f q
  rw [show (-1 : SL(2, ℤ))⁻¹ = -1 from by ext i j; simp,
    sourceGamma0Coset_neg_one]

private theorem additivePermutation_U_cube (f : (SL(2, ℤ) ⧸ Gamma0 M) → A) :
    sourceAdditivePermutationRep SL(2, ℤ) _ A (S * T)
      (sourceAdditivePermutationRep SL(2, ℤ) _ A (S * T)
        (sourceAdditivePermutationRep SL(2, ℤ) _ A (S * T) f)) = f := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    show (S * T) * (S * T) * (S * T) = (S * T) ^ 3 by rw [pow_succ, pow_two],
    show (S * T) ^ 3 = (-1 : SL(2, ℤ)) from SourceSL2Cocycle.U_pow_three]
  funext q
  change f ((-1 : SL(2, ℤ))⁻¹ • q) = f q
  rw [show (-1 : SL(2, ℤ))⁻¹ = -1 from by ext i j; simp,
    sourceGamma0Coset_neg_one]

/-- A native cocycle on the original cosets which vanishes at fixed points of
finite-order matrices lifts through any surjective additive coefficient map. -/
theorem sourceSL2PermutationCocycle_lift (π : A →+ B) (hπ : Function.Surjective π)
    (c : cocycles₁ (Rep.of
      (sourceAdditivePermutationRep SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma0 M) B)))
    (hc : ∀ g : SL(2, ℤ), IsOfFinOrder g → ∀ q : SL(2, ℤ) ⧸ Gamma0 M,
      g • q = q → c g q = 0) :
    ∃ z : cocycles₁ (Rep.of
      (sourceAdditivePermutationRep SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma0 M) A)),
      ∀ g q, π (z g q) = c g q := by
  classical
  have hSfin : IsOfFinOrder (S : SL(2, ℤ)) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨4, by omega, ?_⟩
    rw [show S ^ 4 = (S * S) * (S * S) by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc], SourceSL2Cocycle.S_mul_S]
    simp
  have hUfin : IsOfFinOrder (S * T : SL(2, ℤ)) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨6, by omega, ?_⟩
    rw [show (S * T) ^ 6 = ((S * T) ^ 3) ^ 2 by group,
      show (S * T) ^ 3 = (-1 : SL(2, ℤ)) from SourceSL2Cocycle.U_pow_three]
    simp
  obtain ⟨fS, hfS⟩ := sourcePermutationCocycle_exists_potential c (Subgroup.zpowers S)
    (fun g hg q hq => hc g (hSfin.of_mem_zpowers hg) q hq)
  obtain ⟨fU, hfU⟩ := sourcePermutationCocycle_exists_potential c (Subgroup.zpowers (S * T))
    (fun g hg q hq => hc g (hUfin.of_mem_zpowers hg) q hq)
  choose aS haS using fun q => hπ (fS q)
  choose aU haU using fun q => hπ (fU q)
  let ρ := sourceAdditivePermutationRep SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma0 M) A
  let vS := aS - ρ S aS
  let vU := aU - ρ (S * T) aU
  have hS : vS + ρ S vS = 0 := by
    dsimp only [vS]
    rw [map_sub, additivePermutation_S_sq]
    abel
  have hU : vU + ρ (S * T) vU + ρ (S * T) (ρ (S * T) vU) = 0 := by
    dsimp only [vU]
    simp only [map_sub]
    rw [additivePermutation_U_cube]
    abel
  obtain ⟨z, hzS, hzU⟩ := sourceSL2Cocycle_exists ρ vS vU hS hU
  have hzmap : (fun g q => π (z g q)) ∈ cocycles₁
      (Rep.of (sourceAdditivePermutationRep SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma0 M) B)) := by
    apply (mem_cocycles₁_iff _).mpr
    intro g h
    funext q
    have hz := congrFun ((mem_cocycles₁_iff z).mp z.property g h) q
    change z (g * h) q = z h (g⁻¹ • q) + z g q at hz
    change π (z (g * h) q) = π (z h (g⁻¹ • q)) + π (z g q)
    rw [hz, map_add]
  let d : cocycles₁ (Rep.of
      (sourceAdditivePermutationRep SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma0 M) B)) :=
    ⟨fun g q => π (z g q), hzmap⟩
  have hd : d = c := by
    apply sourceSL2Cocycle_ext
    · funext q
      change π (z S q) = c S q
      rw [hzS]
      change π (aS q - aS (S⁻¹ • q)) = c S q
      rw [map_sub, haS, haS]
      exact (hfS S (Subgroup.mem_zpowers S) q).symm
    · funext q
      change π (z (S * T) q) = c (S * T) q
      rw [hzU]
      change π (aU q - aU ((S * T)⁻¹ • q)) = c (S * T) q
      rw [map_sub, haU, haU]
      exact (hfU (S * T) (Subgroup.mem_zpowers (S * T)) q).symm
  exact ⟨z, fun g q => congrFun (congrArg (fun w => w g) hd) q⟩

end
end Dubon2026
