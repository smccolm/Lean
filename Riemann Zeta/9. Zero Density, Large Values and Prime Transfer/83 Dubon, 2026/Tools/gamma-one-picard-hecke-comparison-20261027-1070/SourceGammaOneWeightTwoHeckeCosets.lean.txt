import Dubon2026.SourceGammaOneHeckeSubgroup
import Dubon2026.SourceWeightTwoHeckeCosetTrace

/-! DUB17/18 -> original all-weight arithmetic association -> actual
Gamma1 Picard/H1 Hecke comparison -> the literal weight-two coset trace.
Use the already proved integral Gamma1 conjugation and slash laws.
The translate descends to the actual upper-subgroup quotient. No
Gamma0 form or transferred Picard operator is substituted. -/
namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm
variable (M d : ℕ) [NeZero d]

theorem sourceGammaOneWeightTwoDiagonal_invariant
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) (g : sourceGammaOneHeckeUpper M d) :
    (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 d 0) ∣[(2 : ℤ)] mapGL ℝ g.val.val =
      ⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 d 0 := by
  have hf : (⇑f ∣[(2 : ℤ)] mapGL ℝ (sourceGammaOneHeckeConjugation M d g).val) =
      (⇑f : ℍ → ℂ) :=
    f.slash_action_eq' _ (Subgroup.mem_map.mpr
      ⟨_, (sourceGammaOneHeckeConjugation M d g).property, rfl⟩)
  rw [← SlashAction.slash_mul, sourceGammaOneHeckeConjugation_matrix,
    SlashAction.slash_mul, hf]

/-- The actual weight-two inverse-dilation slash term on a Gamma1 upper-subgroup coset. -/
def sourceGammaOneWeightTwoHeckeCoset
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) :
    (Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) → (ℍ → ℂ) :=
  Quotient.lift
    (fun g => (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 d 0) ∣[(2 : ℤ)] mapGL ℝ g.val⁻¹)
    (by
      intro g h he
      have hs : g⁻¹ * h ∈ sourceGammaOneHeckeUpper M d := QuotientGroup.leftRel_apply.mp he
      have hi := sourceGammaOneWeightTwoDiagonal_invariant M d f
        ⟨(g⁻¹ * h)⁻¹, (sourceGammaOneHeckeUpper M d).inv_mem hs⟩
      have hm : h.val⁻¹ = ((g⁻¹ * h)⁻¹ : Gamma1 M).val * g.val⁻¹ := by
        simp only [Subgroup.coe_inv, Subgroup.coe_mul]
        group
      change _ = (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 d 0) ∣[(2 : ℤ)] mapGL ℝ h.val⁻¹
      rw [hm, map_mul, SlashAction.slash_mul, hi])

theorem sourceGammaOneWeightTwoHeckeCoset_mk
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) (g : Gamma1 M) :
    sourceGammaOneWeightTwoHeckeCoset M d f (QuotientGroup.mk g) =
      (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 d 0) ∣[(2 : ℤ)] mapGL ℝ g.val⁻¹ := rfl

theorem sourceGammaOneWeightTwoHeckeCoset_out
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2)
    (q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) :
    sourceGammaOneWeightTwoHeckeCoset M d f q =
      (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 d 0) ∣[(2 : ℤ)] mapGL ℝ q.out.val⁻¹ := by
  simpa only [Quotient.out_eq] using sourceGammaOneWeightTwoHeckeCoset_mk M d f q.out

theorem sourceGammaOneWeightTwoHeckeCoset_slash
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) (g : Gamma1 M)
    (q : Gamma1 M ⧸ sourceGammaOneHeckeUpper M d) :
    sourceGammaOneWeightTwoHeckeCoset M d f q ∣[(2 : ℤ)] mapGL ℝ g.val =
      sourceGammaOneWeightTwoHeckeCoset M d f (g⁻¹ • q) := by
  induction q using Quotient.inductionOn with
  | h h =>
    change sourceGammaOneWeightTwoHeckeCoset M d f (QuotientGroup.mk h) ∣[(2 : ℤ)] mapGL ℝ g.val =
      sourceGammaOneWeightTwoHeckeCoset M d f (QuotientGroup.mk (g⁻¹ * h))
    simp only [sourceGammaOneWeightTwoHeckeCoset_mk, Subgroup.coe_mul,
      Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, map_mul, SlashAction.slash_mul]

end
end Dubon2026
