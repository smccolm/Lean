import GafniTao.ClassicalBinaryPhysicalDetector

/-!
# Exact branch alternative for a selected classical family

The mixed zero-energy extraction fixes one binary scale label per coordinate.
This file exposes the surviving branch together with its physical range and
the actual unit-coefficient large-value family.  In the Type-I branch the
upper cutoff is derived from a member of the selected ordinate family; an
empty family is handled separately and cannot smuggle in a support premise.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Source-faithful data attached to one nonempty selected ordinate family. -/
theorem classicalBinarySelectedFamily_alternative
    {A X kI kII : Nat} {sigma q0 eta C : Real}
    (hX : 0 < X) (hq0 : 0 < q0) (hkI : 0 < kI)
    (hkII : kII = Nat.clog 2 X)
    (hC : 0 < C) (heta : 0 <= eta) (hsigma : 0 <= sigma)
    (hCoeff : forall n : Nat, 0 < n ->
      ‖sharpMollifiedCoeff X X n‖ <= C * (n : Real) ^ eta)
    (q : Fin (kI * 2 + kII * 2)) (W : Finset Real)
    (hW : W.Nonempty)
    (hLarge : ∀ t ∈ W, Sum.elim
      (ClassicalTypeIShellScaleLarge A X kI sigma q0)
      (ClassicalTypeIIShellScaleLarge X X kII sigma)
      (binaryScaleLabel q) t) :
    let N := classicalBinarySelectedN X X kI kII q
    let a := classicalBinarySelectedCoeff A X X kI kII sigma eta C q
    let V := classicalBinarySelectedThreshold X X kI kII
      sigma q0 eta C q
    0 < N /\
      (∀ n, n ∈ dyadicInterval N -> ‖a n‖ <= 1) /\
      (∀ t ∈ W, V <= ‖sourceDirichletPoly N a t‖) /\
      ((exists r : Fin (kI * 2),
          binaryScaleLabel q = Sum.inl r /\ X <= N /\ N < A) \/
        (exists r : Fin (kII * 2),
          binaryScaleLabel q = Sum.inr r /\ X <= N /\ N < X ^ 2)) := by
  dsimp only
  have hUnit := norm_classicalBinarySelectedCoeff_le_one
    A X X kI kII sigma eta C q hX hX hsigma heta hC hCoeff
  have hLargeNormalized : ∀ t ∈ W,
      classicalBinarySelectedThreshold X X kI kII sigma q0 eta C q <=
        ‖sourceDirichletPoly (classicalBinarySelectedN X X kI kII q)
          (classicalBinarySelectedCoeff A X X kI kII sigma eta C q) t‖ := by
    intro t ht
    exact classicalBinarySelectedCoeff_large A X X kI kII
      sigma q0 eta C t q hX hX hC (hLarge t ht)
  refine ⟨classicalBinarySelectedN_pos hX hX q, hUnit,
    hLargeNormalized, ?_⟩
  cases hq : binaryScaleLabel q with
  | inl r =>
      left
      obtain ⟨t, ht⟩ := hW
      refine ⟨r, rfl, le_classicalBinarySelectedN_of_typeI q r hq, ?_⟩
      exact classicalBinarySelectedN_lt_cutoff_of_typeI_large
        hq0 hkI q r hq (hLarge t ht)
  | inr r =>
      right
      refine ⟨r, rfl, ?_⟩
      have hRange := classicalBinarySelectedN_typeII_equal_cutoff_range
        hX (by rw [hkII]) q r hq
      exact hRange

/-- Any selected scale alternative either lies in the exact physical power
window `N^2 <= X^4 <= N^4`, or is an explicitly labelled Type-I block beyond
the Type-II range. -/
theorem classicalBinarySelected_powerWindow_or_longTypeI
    {A X kI kII : Nat} (q : Fin (kI * 2 + kII * 2))
    (hAlt :
      (exists r : Fin (kI * 2),
        binaryScaleLabel q = Sum.inl r /\
        X <= classicalBinarySelectedN X X kI kII q /\
        classicalBinarySelectedN X X kI kII q < A) \/
      (exists r : Fin (kII * 2),
        binaryScaleLabel q = Sum.inr r /\
        X <= classicalBinarySelectedN X X kI kII q /\
        classicalBinarySelectedN X X kI kII q < X ^ 2)) :
    (((classicalBinarySelectedN X X kI kII q : Real) ^ 2 <=
          (X : Real) ^ 4 /\
        (X : Real) ^ 4 <=
          (classicalBinarySelectedN X X kI kII q : Real) ^ 4) \/
      exists r : Fin (kI * 2),
        binaryScaleLabel q = Sum.inl r /\
        X ^ 2 < classicalBinarySelectedN X X kI kII q /\
        classicalBinarySelectedN X X kI kII q < A) := by
  let N := classicalBinarySelectedN X X kI kII q
  have powerWindow (hXN : X <= N) (hNX : N <= X ^ 2) :
      (N : Real) ^ 2 <= (X : Real) ^ 4 /\
        (X : Real) ^ 4 <= (N : Real) ^ 4 := by
    have hXNReal : (X : Real) <= (N : Real) := by exact_mod_cast hXN
    have hNXReal : (N : Real) <= (X : Real) ^ 2 := by
      exact_mod_cast hNX
    constructor
    · calc
        (N : Real) ^ 2 <= ((X : Real) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg N) hNXReal 2
        _ = (X : Real) ^ 4 := by ring
    · exact pow_le_pow_left₀ (Nat.cast_nonneg X) hXNReal 4
  rcases hAlt with ⟨r, hq, hXN, hNA⟩ | ⟨r, hq, hXN, hNX⟩
  · by_cases hNX2 : N <= X ^ 2
    · left
      exact powerWindow hXN hNX2
    · right
      exact ⟨r, hq, lt_of_not_ge hNX2, hNA⟩
  · left
    exact powerWindow hXN hNX.le

#print axioms classicalBinarySelectedFamily_alternative
#print axioms classicalBinarySelected_powerWindow_or_longTypeI

end

end GafniTao
