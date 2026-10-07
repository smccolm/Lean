import Dubon2026.ProjectiveEisensteinCosets

/-! # The exact two primitive rows above each projective parabolic coset -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The opposite primitive row, preserving the actual level divisibility. -/
def gamma0NegRow {Q : ℕ} (v : gamma0PrimitiveRows Q) : gamma0PrimitiveRows Q :=
  ⟨-v.val, by simpa using v.property.1, dvd_neg.mpr v.property.2⟩

/-- No actual primitive row is equal to its opposite. -/
theorem gamma0NegRow_ne_self {Q : ℕ} (v : gamma0PrimitiveRows Q) : gamma0NegRow v ≠ v := by
  intro h
  apply gamma0PrimitiveRow_ne_zero v
  funext i
  have hi := congrFun (congrArg Subtype.val h) i
  change -v.val i = v.val i at hi
  change v.val i = 0
  omega

/-- An actual determinant-one Γ₀ completion of the given row. -/
def gamma0RowCompletion {Q : ℕ} (v : gamma0PrimitiveRows Q) : Gamma0 Q :=
  (gamma0BottomRow_surjective Q v).choose

/-- The chosen completion has exactly the given bottom row. -/
theorem gamma0RowCompletion_row {Q : ℕ} (v : gamma0PrimitiveRows Q) :
    gamma0BottomRow (gamma0RowCompletion v) = v :=
  (gamma0BottomRow_surjective Q v).choose_spec

/-- The actual projective parabolic coset determined by a primitive row. -/
def gamma0RowParabolicCoset {Q : ℕ} (v : gamma0PrimitiveRows Q) :
    (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q :=
  gamma0InverseParabolicCoset (gamma0RowCompletion v)

/-- Precisely two rows, the opposite signs, determine each actual projective coset. -/
theorem gamma0RowParabolicCoset_eq_iff {Q : ℕ} (v w : gamma0PrimitiveRows Q) :
    gamma0RowParabolicCoset v = gamma0RowParabolicCoset w ↔ v = w ∨ v = gamma0NegRow w := by
  rw [gamma0RowParabolicCoset, gamma0RowParabolicCoset, gamma0InverseParabolicCoset_eq_iff]
  have hv := congrArg Subtype.val (gamma0RowCompletion_row v)
  have hw := congrArg Subtype.val (gamma0RowCompletion_row w)
  change (gamma0RowCompletion v).val.val 1 = v.val at hv
  change (gamma0RowCompletion w).val.val 1 = w.val at hw
  rw [hv, hw]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl) <;> simp [gamma0NegRow]

/-- The primitive-row map uses the same coset as any actual matrix with that row. -/
theorem gamma0RowParabolicCoset_bottomRow {Q : ℕ} (A : Gamma0 Q) :
    gamma0RowParabolicCoset (gamma0BottomRow A) = gamma0InverseParabolicCoset A := by
  apply (gamma0InverseParabolicCoset_eq_iff _ _).mpr
  exact Or.inl (congrArg Subtype.val (gamma0RowCompletion_row (gamma0BottomRow A)))

/-- All projective parabolic cosets occur among the literal primitive rows. -/
theorem gamma0RowParabolicCoset_surjective (Q : ℕ) :
    Function.Surjective (@gamma0RowParabolicCoset Q) := by
  intro q
  obtain ⟨A, hA⟩ := gamma0Projectivize_surjective Q q.out⁻¹
  refine ⟨gamma0BottomRow A, ?_⟩
  rw [gamma0RowParabolicCoset_bottomRow, gamma0InverseParabolicCoset, hA, inv_inv]
  exact q.out_eq

/-- A genuine primitive row above the actual projective coset. -/
def gamma0ParabolicRow {Q : ℕ}
    (q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q) : gamma0PrimitiveRows Q :=
  Function.surjInv (gamma0RowParabolicCoset_surjective Q) q

/-- The selected row lies above its own coset. -/
theorem gamma0ParabolicRow_coset {Q : ℕ}
    (q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q) :
    gamma0RowParabolicCoset (gamma0ParabolicRow q) = q :=
  Function.rightInverse_surjInv (gamma0RowParabolicCoset_surjective Q) q

/-- Negating a primitive row preserves its actual projective coset. -/
theorem gamma0RowParabolicCoset_neg {Q : ℕ} (v : gamma0PrimitiveRows Q) :
    gamma0RowParabolicCoset (gamma0NegRow v) = gamma0RowParabolicCoset v :=
  (gamma0RowParabolicCoset_eq_iff _ _).mpr (Or.inr rfl)

/-- The two signed primitive rows in a parabolic fiber. -/
def gamma0RowFiberPoint {Q : ℕ}
    (q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q) :
    Bool → {v : gamma0PrimitiveRows Q // gamma0RowParabolicCoset v = q}
  | false => ⟨gamma0NegRow (gamma0ParabolicRow q),
    (gamma0RowParabolicCoset_neg _).trans (gamma0ParabolicRow_coset q)⟩
  | true => ⟨gamma0ParabolicRow q, gamma0ParabolicRow_coset q⟩

/-- The exact two-element fiber, without treating the central signs as distinct projective cosets. -/
def gamma0RowFiberEquiv {Q : ℕ}
    (q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q) :
    Bool ≃ {v : gamma0PrimitiveRows Q // gamma0RowParabolicCoset v = q} :=
  Equiv.ofBijective (gamma0RowFiberPoint q) ⟨by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (gamma0NegRow_ne_self _ (congrArg Subtype.val h))
    · exact False.elim (gamma0NegRow_ne_self _ (congrArg Subtype.val h.symm))
    · rfl, by
    intro v
    have h : gamma0RowParabolicCoset v.val = gamma0RowParabolicCoset (gamma0ParabolicRow q) :=
      v.property.trans (gamma0ParabolicRow_coset q).symm
    rcases (gamma0RowParabolicCoset_eq_iff _ _).mp h with he | he
    · exact ⟨true, Subtype.ext he.symm⟩
    · exact ⟨false, Subtype.ext he.symm⟩⟩

/-- Opposite primitive rows have identical genuine height kernels. -/
theorem eisensteinRowHeight_neg_row {Q : ℕ} (v : gamma0PrimitiveRows Q) (z : ℍ) :
    eisensteinRowHeight (gamma0NegRow v).val z = eisensteinRowHeight v.val z := by
  simp only [eisensteinRowHeight, gamma0NegRow, Pi.neg_apply, Int.cast_neg]
  rw [neg_mul, ← neg_add, norm_neg]

end
end Dubon2026
