import Dubon2026.SourceAffinePointCalculus
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! Evaluation detects every nonzero original full-function H1 class.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> nonzero evaluation on the actual upper-congruence subgroup ->
the original trivial-coefficient class at raised level.
The explicit primitive is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). Native cocycles and original
integral translations retain the exact source coefficient action.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] (hpQ : p ∣ Q)

/-- An original function-valued cocycle whose evaluation vanishes on the
actual stabilizer of zero is a native coboundary, with an explicit primitive. -/
theorem sourceAffineCocycleEvaluation_coboundary
    (z : cocycles₁ (sourceAffineFunctionRep p Q F hpQ))
    (h0 : ∀ h : Gamma0 Q, (p : ℤ) ∣ h.val 0 1 → z h 0 = 0) :
    (z : Gamma0 Q → sourceAffineFunctionRep p Q F hpQ) ∈
      coboundaries₁ (sourceAffineFunctionRep p Q F hpQ) := by
  let zf : Gamma0 Q → ZMod p → F := fun g => z g
  have hz (g h : Gamma0 Q) :
      zf (g * h) = zf g + sourceAffineFunctionAction p Q F g (zf h) := by
    have he := (mem_cocycles₁_iff z).mp z.property g h
    exact he.trans (add_comm _ _)
  have hz1 : zf 1 = 0 := cocycles₁_map_one z
  have hzi (g : Gamma0 Q) :
      zf g⁻¹ = -(sourceAffineFunctionAction p Q F g⁻¹ (zf g)) := by
    have he := hz g⁻¹ g
    rw [inv_mul_cancel, hz1] at he
    exact eq_neg_of_add_eq_zero_left he.symm
  let f : ZMod p → F := fun u => zf (heckeUpperTranslation Q (u.val : ℤ)) u
  have hkey (g : Gamma0 Q) : zf g (sourceAffinePoint p Q g) = f (sourceAffinePoint p Q g) := by
    let n : ℤ := ((sourceAffinePoint p Q g).val : ℤ)
    have hn : (n : ZMod p) = sourceAffinePoint p Q g := by
      simp only [n, Int.cast_natCast, ZMod.natCast_zmod_val]
    let h := (heckeUpperTranslation Q n)⁻¹ * g
    have hg : g = heckeUpperTranslation Q n * h := by
      simp only [h, mul_inv_cancel_left]
    have hb : sourceAffineB p Q h = 0 := by
      rw [show h = (heckeUpperTranslation Q n)⁻¹ * g from rfl,
        sourceAffine_b_mul, sourceAffine_a_inv, sourceAffine_b_inv]
      have hd : sourceAffineD p Q (heckeUpperTranslation Q n) = 1 := by
        simp [sourceAffineD, heckeUpperTranslation]
      have ht : sourceAffineB p Q (heckeUpperTranslation Q n) = (n : ZMod p) := rfl
      rw [hd, ht, hn, sourceAffinePoint, one_mul]
      linear_combination (-sourceAffineB p Q g) * sourceAffine_ad p Q hpQ g
    have hzh : zf h 0 = 0 := h0 h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb)
    have he : zf g = zf (heckeUpperTranslation Q n) +
        sourceAffineFunctionAction p Q F (heckeUpperTranslation Q n) (zf h) := by
      conv_lhs => rw [hg]
      exact hz _ _
    have ht : sourceAffineFunctionAction p Q F (heckeUpperTranslation Q n)
        (zf h) (sourceAffinePoint p Q g) = zf h 0 := by
      simp [sourceAffineFunctionAction, sourceAffineD, sourceAffineB, heckeUpperTranslation, hn]
    rw [he, Pi.add_apply, ht, hzh, add_zero]
  refine ⟨-f, funext fun g => funext fun u => ?_⟩
  let delta := heckeUpperTranslation Q (u.val : ℤ)
  have hpoint : sourceAffinePoint p Q delta = u := by
    rw [sourceAffinePoint_translation]
    simp
  have hfu : f u = zf delta u := rfl
  have hA : sourceAffineFunctionAction p Q F g f u =
      f (sourceAffinePoint p Q (g⁻¹ * delta)) := by
    rw [sourceAffinePoint_move p Q hpQ, hpoint]
    rfl
  have hB : f (sourceAffinePoint p Q (g⁻¹ * delta)) =
      zf (g⁻¹ * delta) (sourceAffinePoint p Q (g⁻¹ * delta)) := (hkey _).symm
  have hC : zf (g⁻¹ * delta) (sourceAffinePoint p Q (g⁻¹ * delta)) =
      -(zf g u) + zf delta u := by
    rw [hz, Pi.add_apply, hzi, Pi.neg_apply]
    simp only [sourceAffineFunctionAction, LinearMap.coe_mk, AddHom.coe_mk]
    rw [sourceAffinePoint_move p Q hpQ, hpoint, sourceAffinePoint_inverse p Q hpQ]
  change (sourceAffineFunctionAction p Q F g (-f)) u - (-f) u = zf g u
  rw [map_neg, Pi.neg_apply, hA, hB, hC, Pi.neg_apply, hfu]
  ring

/-- Every nonzero original native H1 class has a nonzero evaluated cocycle
on the actual upper-congruence subgroup. -/
theorem sourceAffineCocycleEvaluation_nonzero
    (z : cocycles₁ (sourceAffineFunctionRep p Q F hpQ))
    (hz : H1π (sourceAffineFunctionRep p Q F hpQ) z ≠ 0) :
    ∃ h : Gamma0 Q, (p : ℤ) ∣ h.val 0 1 ∧ z h 0 ≠ 0 := by
  by_contra h
  push Not at h
  exact hz ((H1π_eq_zero_iff z).mpr (sourceAffineCocycleEvaluation_coboundary F p Q hpQ z h))

end
end Dubon2026
