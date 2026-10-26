import Dubon2026.PrincipalCongruenceQuotient

/-! DUB-17/18 -> all-weight adic association -> Gamma1 cover Hecke
compatibility -> representatives for the exact good-prime cosets. Reuse
the proved full SL2 reduction and its existing Chinese-remainder equivalence
to lift inside the original principal subgroup. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The already constructed Chinese-remainder isomorphism sends literal
integral reduction to the two literal component reductions. -/
theorem sourceSL2ChineseRemainder_reduction (M N : ℕ) (h : Nat.Coprime M N)
    (g : SL(2, ℤ)) :
    sl2ChineseRemainder h (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (M * N))) g) =
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g,
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g) := by
  apply Prod.ext <;> ext i j <;>
    simp [sl2ChineseRemainder, sl2RingEquiv, sl2ProductEquiv]

/-- At coprime moduli the actual principal subgroup still reduces onto
the full determinant-one matrix group. No matrix lift is assumed. -/
theorem sourcePrincipalReduction_surjective (M N : ℕ) [NeZero M] [NeZero N]
    (h : Nat.Coprime M N) :
    Function.Surjective
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))).comp (Gamma M).subtype) := by
  intro B
  let C := (sl2ChineseRemainder h).symm (1, B)
  obtain ⟨g, hg⟩ := SL2Reduction.SL2_reduction_surjective (M * N) C
  have he : sl2ChineseRemainder h
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (M * N))) g) = (1, B) := by
    rw [hg]
    exact (sl2ChineseRemainder h).apply_symm_apply (1, B)
  rw [sourceSL2ChineseRemainder_reduction] at he
  have hm : g ∈ Gamma M := congrArg Prod.fst he
  exact ⟨⟨g, hm⟩, congrArg Prod.snd he⟩

end
end Dubon2026
