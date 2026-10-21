import Dubon2026.SourceSL2CocycleExists
import Dubon2026.PermutationCoordinateRepresentation
import Dubon2026.HeckeUpperCosets

/-! The actual nonzero cusp functional for the required Eisenstein eigensystem.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of its Eisenstein exception -> a nonzero functional
on original trivial-coefficient H1, evaluated on the actual translation.
Adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_isEigensystemH1_one_natCast_add_one.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). The existing actual permutation
representation and the proved native SL2(Z) cocycle are reused.
-/

namespace Dubon2026
noncomputable section
open scoped MatrixGroups
open Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup groupCohomology

variable (Q : ℕ)

/-- The actual central minus-one matrix fixes every original congruence coset. -/
theorem sourceGamma0Coset_neg_one (q : SL(2, ℤ) ⧸ Gamma0 Q) :
    (-1 : SL(2, ℤ)) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    change (QuotientGroup.mk (-1 * g) : SL(2, ℤ) ⧸ Gamma0 Q) = QuotientGroup.mk g
    rw [QuotientGroup.eq, neg_one_mul, show (-g)⁻¹ * g = -1 by
      rw [show (-g)⁻¹ = -g⁻¹ from by
        ext i j
        simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two],
        neg_mul, inv_mul_cancel]]
    rw [Gamma0_mem]
    simp

/-- At every actual level at least two there is a genuine additive homomorphism
which takes the original unit translation to one. -/
theorem sourceGamma0_exists_translation_hom (F : Type) [CommRing F] (hQ : 2 ≤ Q) :
    ∃ φ : Additive (Gamma0 Q) →+ F,
      φ (Additive.ofMul (heckeUpperTranslation Q 1)) = 1 := by
  classical
  let ρ : Representation F SL(2, ℤ) ((SL(2, ℤ) ⧸ Gamma0 Q) → F) :=
    (permutationCoordinateRep F SL(2, ℤ) (SL(2, ℤ) ⧸ Gamma0 Q)).ρ
  let ind : (SL(2, ℤ) ⧸ Gamma0 Q) → F :=
    fun q => if q = (QuotientGroup.mk S : SL(2, ℤ) ⧸ Gamma0 Q) then 1 else 0
  let y := ind - ρ (S * T) ind
  have hx : (0 : (SL(2, ℤ) ⧸ Gamma0 Q) → F) + ρ S 0 = 0 := by simp
  have hR3 : ρ (S * T) (ρ (S * T) (ρ (S * T) ind)) = ind := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      show (S * T) * (S * T) * (S * T) = (S * T) ^ 3 by rw [pow_succ, pow_two]]
    rw [show (S * T) ^ 3 = (-1 : SL(2, ℤ)) from SourceSL2Cocycle.U_pow_three]
    funext q
    change ind ((-1 : SL(2, ℤ))⁻¹ • q) = ind q
    rw [show (-1 : SL(2, ℤ))⁻¹ = -1 from by
      ext i j
      simp,
      sourceGamma0Coset_neg_one]
  have hy : y + ρ (S * T) y + ρ (S * T) (ρ (S * T) y) = 0 := by
    dsimp only [y]
    simp only [map_sub]
    rw [hR3]
    abel
  obtain ⟨z, hzS, hzST⟩ := sourceSL2Cocycle_exists ρ 0 y hx hy
  let zf : SL(2, ℤ) → (SL(2, ℤ) ⧸ Gamma0 Q) → F := fun g => z g
  have hz (g h : SL(2, ℤ)) : zf (g * h) = zf g + ρ g (zf h) :=
    ((mem_cocycles₁_iff z).mp z.property g h).trans (add_comm _ _)
  let e : SL(2, ℤ) ⧸ Gamma0 Q := QuotientGroup.mk 1
  have hinv (h : Gamma0 Q) : (h.val)⁻¹ • e = e := by
    change (QuotientGroup.mk (h.val⁻¹ * 1) : SL(2, ℤ) ⧸ Gamma0 Q) = QuotientGroup.mk 1
    rw [QuotientGroup.eq]
    simpa only [mul_one, inv_inv] using h.property
  refine ⟨AddMonoidHom.mk' (fun a => zf (Additive.toMul a).val e) ?_, ?_⟩
  · intro a b
    change zf (Additive.toMul a * Additive.toMul b).val e = _
    rw [Subgroup.coe_mul, hz, Pi.add_apply]
    change zf (Additive.toMul a).val e +
      zf (Additive.toMul b).val ((Additive.toMul a).val⁻¹ • e) = _
    rw [hinv]
  · change zf T e = 1
    have hzSinv : zf S⁻¹ = 0 := by
      have he := hz S⁻¹ S
      rw [inv_mul_cancel, show zf S = 0 from hzS, map_zero, add_zero] at he
      exact he.symm.trans (cocycles₁_map_one z)
    rw [show T = S⁻¹ * (S * T) from (inv_mul_cancel_left S T).symm,
      hz, hzSinv, zero_add, show zf (S * T) = y from hzST]
    change y ((S⁻¹)⁻¹ • e) = 1
    rw [inv_inv]
    have h1 : S • e = (QuotientGroup.mk S : SL(2, ℤ) ⧸ Gamma0 Q) := by
      change (QuotientGroup.mk (S * 1) : SL(2, ℤ) ⧸ Gamma0 Q) = _
      rw [mul_one]
    have h2 : (S * T)⁻¹ • (QuotientGroup.mk S : SL(2, ℤ) ⧸ Gamma0 Q) =
        QuotientGroup.mk T⁻¹ := by
      change (QuotientGroup.mk ((S * T)⁻¹ * S) : SL(2, ℤ) ⧸ Gamma0 Q) = _
      rw [mul_inv_rev, inv_mul_cancel_right]
    change ind (S • e) - ind ((S * T)⁻¹ • (S • e)) = 1
    rw [h1, h2]
    dsimp only [ind]
    rw [if_pos rfl, if_neg, sub_zero]
    intro hTS
    rw [QuotientGroup.eq, inv_inv, Gamma0_mem] at hTS
    have h10 : ((T * S : SL(2, ℤ)) 1 0 : ℤ) = 1 := by
      simp [ModularGroup.coe_S]
    rw [h10, Int.cast_one] at hTS
    haveI : Fact (1 < Q) := ⟨hQ⟩
    exact one_ne_zero hTS

end
end Dubon2026
