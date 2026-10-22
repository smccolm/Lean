import Dubon2026.SourceCurvePlaceRestriction
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> exact constant-field place extension. A residue digit followed by a uniformizer
factor decomposes finite local combinations. The original consumer supplies
the proved finite residue field; no IsCurveOver or order-preservation premise
is introduced. This is the local calculation needed to show extension has
ramification index one and is unique.
Adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F)

theorem exists_digit [IsAlgClosed K] [Module.Finite K P.ResidueField] {π : P.toValuationSubring}
    (hπ : Irreducible π) (o : P.toValuationSubring) :
    ∃ a : K, ∃ o' : P.toValuationSubring,
      o = algebraMap K P.toValuationSubring a + π * o' ∧ (o = 0 → o' = 0) := by
  rcases eq_or_ne o 0 with rfl | ho
  · exact ⟨0, 0, by simp, fun _ => rfl⟩
  haveI : Algebra.IsIntegral K P.ResidueField := Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue P.toValuationSubring o)
  have hmem : o - algebraMap K P.toValuationSubring a ∈
      IsLocalRing.maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
      IsScalarTower.algebraMap_apply K P.toValuationSubring P.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨a, b, by rw [mul_comm, hb]; ring, fun h => absurd h ho⟩

end
end Dubon2026.SourceCurve.ConstantField
