import Dubon2026.SourceHeckeSymbolCosets

/-! DUB-17/18 -> original Picard-period Hecke comparison -> the derivative
of the genuine cusp-primitive coset sum. Reuse the actual upper-subgroup
conjugation and the existing classical Hecke transversal. The weight-two
slash sum over genuine quotient cosets is the already proved analytic
good-prime Hecke operator; no new representative classification is needed.
-/
namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm
variable {N p : ℕ} [NeZero p]

theorem sourceWeightTwoHeckeDiagonal_invariant (hp : Nat.Prime p)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) (γ : heckeUpperSubgroup N p) :
    (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 p 0) ∣[(2 : ℤ)] mapGL ℝ γ.val.val =
      ⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 p 0 :=
  cusp_slash_factor f γ.val.val
    ⟨(sourceHeckeConjugation hp γ).val, (sourceHeckeConjugation hp γ).property,
      sourceHeckeConjugation_matrix hp γ⟩

/-- The genuine weight-two slash translate, independent of the quotient representative. -/
def sourceWeightTwoHeckeCoset (hp : Nat.Prime p)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) :
    (Gamma0 N ⧸ heckeUpperSubgroup N p) → (ℍ → ℂ) :=
  Quotient.lift
    (fun γ => (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 p 0) ∣[(2 : ℤ)] mapGL ℝ γ.val⁻¹)
    (by
      intro γ δ h
      have hs : γ⁻¹ * δ ∈ heckeUpperSubgroup N p := QuotientGroup.leftRel_apply.mp h
      have hi := sourceWeightTwoHeckeDiagonal_invariant hp f
        ⟨(γ⁻¹ * δ)⁻¹, (heckeUpperSubgroup N p).inv_mem hs⟩
      have he : δ.val⁻¹ = ((γ⁻¹ * δ)⁻¹ : Gamma0 N).val * γ.val⁻¹ := by
        simp only [Subgroup.coe_inv, Subgroup.coe_mul]
        group
      change _ = (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 p 0) ∣[(2 : ℤ)] mapGL ℝ δ.val⁻¹
      rw [he, map_mul, SlashAction.slash_mul, hi])

theorem sourceWeightTwoHeckeCoset_mk (hp : Nat.Prime p)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) (γ : Gamma0 N) :
    sourceWeightTwoHeckeCoset hp f (QuotientGroup.mk γ) =
      (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 p 0) ∣[(2 : ℤ)] mapGL ℝ γ.val⁻¹ := rfl

theorem sourceWeightTwoHeckeCoset_out (hp : Nat.Prime p)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2)
    (q : Gamma0 N ⧸ heckeUpperSubgroup N p) :
    sourceWeightTwoHeckeCoset hp f q =
      (⇑f ∣[(2 : ℤ)] heckeTriangularMatrix 1 p 0) ∣[(2 : ℤ)] mapGL ℝ q.out.val⁻¹ := by
  simpa only [Quotient.out_eq] using sourceWeightTwoHeckeCoset_mk hp f q.out

private local instance : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N p) :=
  sourceHeckeUpperFintype N p

theorem sourceWeightTwoHeckeCoset_sum [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) :
    (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N p, sourceWeightTwoHeckeCoset hp f q) =
      ⇑(cuspHeckePrime hp f) := by
  rw [← (heckeUpperCosetEquiv hp hpN).sum_comp]
  change (∑ x : Option (ZMod p), sourceWeightTwoHeckeCoset hp f
    (QuotientGroup.mk (heckeUpperRepresentative p N hpN x)⁻¹)) = _
  simp only [sourceWeightTwoHeckeCoset_mk, Subgroup.coe_inv, inv_inv]
  exact heckeUpperTrace_eq hp hpN f

end
end Dubon2026
