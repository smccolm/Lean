import GafniTao.ClassicalBinaryNormalization

/-!
# A branch-independent normalized classical detector family

The signed binary detector returns either a coefficient-one Type-I block or
a sharp-mollifier Type-II block.  This file packages the two alternatives
without erasing the `Sum` label that records the actual branch.  In both
cases the resulting coefficients have norm at most one and the exact
normalized large-value threshold remains visible.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Physical length selected by a binary Type-I/Type-II scale label. -/
def classicalBinarySelectedN
    (Y X kI kII : Nat) (q : Fin (kI * 2 + kII * 2)) : Nat :=
  Sum.elim (classicalTypeIShellScaleN Y)
    (classicalTypeIIShellScaleN X) (binaryScaleLabel q)

/-- The source-sign attached to a selected binary scale. -/
def classicalBinarySelectedSign
    {kI kII : Nat} (q : Fin (kI * 2 + kII * 2)) : Fin 2 :=
  Sum.elim (fun r => (classicalTypeIShellScalePair r).2)
    (fun r => (classicalTypeIIShellScalePair r).2) (binaryScaleLabel q)

/-- Unit-normalized coefficients at a selected binary scale. -/
noncomputable def classicalBinarySelectedCoeff
    (A Y X kI kII : Nat) (sigma eta C : Real)
    (q : Fin (kI * 2 + kII * 2)) : Nat -> Complex :=
  Sum.elim
    (fun r => signedNormalizedClassicalTypeICoeff A
      (classicalTypeIShellScaleN Y r) sigma
      (classicalTypeIShellScalePair r).2)
    (fun r => signedNormalizedClassicalTypeIICoeff Y X
      (classicalTypeIIShellScaleN X r) sigma eta C
      (classicalTypeIIShellScalePair r).2)
    (binaryScaleLabel q)

/-- Exact normalized threshold of the selected branch. -/
noncomputable def classicalBinarySelectedThreshold
    (Y X kI kII : Nat) (sigma q0 eta C : Real)
    (q : Fin (kI * 2 + kII * 2)) : Real :=
  Sum.elim
    (fun r => (classicalTypeIShellScaleN Y r : Real) ^ sigma *
      (((3 / 4) * (q0 / 2)) / (kI : Real)))
    (fun r => ((3 / 4) * (3 / 4) / (kII : Real)) /
      (C * (2 * classicalTypeIIShellScaleN X r : Real) ^ eta *
        (classicalTypeIIShellScaleN X r : Real) ^ (-sigma)))
    (binaryScaleLabel q)

theorem classicalBinarySelectedN_pos
    {Y X kI kII : Nat} (hY : 0 < Y) (hX : 0 < X)
    (q : Fin (kI * 2 + kII * 2)) :
    0 < classicalBinarySelectedN Y X kI kII q := by
  unfold classicalBinarySelectedN
  cases hq : binaryScaleLabel q with
  | inl r =>
      simp only [Sum.elim_inl, classicalTypeIShellScaleN]
      exact Nat.mul_pos (pow_pos (by omega) _) hY
  | inr r =>
      simp only [Sum.elim_inr, classicalTypeIIShellScaleN]
      exact Nat.mul_pos (pow_pos (by omega) _) hX

/-- The normalized threshold is strictly positive in either detector branch. -/
theorem classicalBinarySelectedThreshold_pos
    {Y X kI kII : Nat} {sigma q0 eta C : Real}
    (hY : 0 < Y) (hX : 0 < X) (hkI : 0 < kI) (hkII : 0 < kII)
    (hq0 : 0 < q0) (hC : 0 < C)
    (q : Fin (kI * 2 + kII * 2)) :
    0 < classicalBinarySelectedThreshold
      Y X kI kII sigma q0 eta C q := by
  unfold classicalBinarySelectedThreshold
  cases hq : binaryScaleLabel q with
  | inl r =>
      simp only [Sum.elim_inl]
      have hN : 0 < classicalTypeIShellScaleN Y r :=
        Nat.mul_pos (pow_pos (by omega) _) hY
      have hkIReal : (0 : Real) < kI := by exact_mod_cast hkI
      positivity
  | inr r =>
      simp only [Sum.elim_inr]
      have hN : 0 < classicalTypeIIShellScaleN X r :=
        Nat.mul_pos (pow_pos (by omega) _) hX
      have hkIIReal : (0 : Real) < kII := by exact_mod_cast hkII
      positivity

/-- Both detector branches become genuine unit-coefficient families. -/
theorem norm_classicalBinarySelectedCoeff_le_one
    (A Y X kI kII : Nat) (sigma eta C : Real)
    (q : Fin (kI * 2 + kII * 2))
    (hY : 0 < Y) (hX : 0 < X) (hsigma : 0 <= sigma)
    (heta : 0 <= eta) (hC : 0 < C)
    (hCoeff : forall n : Nat, 0 < n ->
      ‖sharpMollifiedCoeff Y X n‖ <= C * (n : Real) ^ eta) :
    forall n, n ∈ dyadicInterval
        (classicalBinarySelectedN Y X kI kII q) ->
      ‖classicalBinarySelectedCoeff A Y X kI kII sigma eta C q n‖ <= 1 := by
  intro n hn
  unfold classicalBinarySelectedN at hn
  unfold classicalBinarySelectedCoeff
  cases hq : binaryScaleLabel q with
  | inl r =>
      simp only [hq, Sum.elim_inl] at hn ⊢
      exact norm_signedNormalizedClassicalTypeICoeff_le_one A
        (classicalTypeIShellScaleN Y r) sigma
        (classicalTypeIShellScalePair r).2
        (Nat.mul_pos (pow_pos (by omega) _) hY) hsigma n hn
  | inr r =>
      simp only [hq, Sum.elim_inr] at hn ⊢
      exact norm_signedNormalizedClassicalTypeIICoeff_le_one Y X
        (classicalTypeIIShellScaleN X r) sigma eta C
        (classicalTypeIIShellScalePair r).2
        (Nat.mul_pos (pow_pos (by omega) _) hX) hsigma heta hC
        hCoeff n hn

/-- The literal binary large-value predicate implies the exact normalized
large-value inequality at the branch-independent selected family. -/
theorem classicalBinarySelectedCoeff_large
    (A Y X kI kII : Nat) (sigma q0 eta C t : Real)
    (q : Fin (kI * 2 + kII * 2))
    (hY : 0 < Y) (hX : 0 < X) (hC : 0 < C)
    (hLarge : Sum.elim
      (ClassicalTypeIShellScaleLarge A Y kI sigma q0)
      (ClassicalTypeIIShellScaleLarge Y X kII sigma)
      (binaryScaleLabel q) t) :
    classicalBinarySelectedThreshold Y X kI kII sigma q0 eta C q <=
      ‖sourceDirichletPoly
        (classicalBinarySelectedN Y X kI kII q)
        (classicalBinarySelectedCoeff A Y X kI kII sigma eta C q) t‖ := by
  unfold classicalBinarySelectedThreshold classicalBinarySelectedN
    classicalBinarySelectedCoeff
  cases hq : binaryScaleLabel q with
  | inl r =>
      simp only [hq, Sum.elim_inl] at hLarge ⊢
      exact signedNormalizedClassicalTypeICoeff_large A
        (classicalTypeIShellScaleN Y r) sigma t
        (((3 / 4) * (q0 / 2)) / (kI : Real))
        (classicalTypeIShellScalePair r).2
        (Nat.mul_pos (pow_pos (by omega) _) hY) hLarge
  | inr r =>
      simp only [hq, Sum.elim_inr] at hLarge ⊢
      exact signedNormalizedClassicalTypeIICoeff_large Y X
        (classicalTypeIIShellScaleN X r) sigma eta C t
        (((3 / 4) * (3 / 4)) / (kII : Real))
        (classicalTypeIIShellScalePair r).2
        (Nat.mul_pos (pow_pos (by omega) _) hX) hC hLarge

#print axioms classicalBinarySelectedN_pos
#print axioms classicalBinarySelectedThreshold_pos
#print axioms norm_classicalBinarySelectedCoeff_le_one
#print axioms classicalBinarySelectedCoeff_large

end

end GafniTao
