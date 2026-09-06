import GafniTao.EnergyDetectorTranslation
import RiemannZeta.GuthMaynard.LargeValuesEnergy

/-!
# The finite Heath--Brown energy relation

This module assembles the three exact finite estimates that underlie the
Heath--Brown zero-energy argument: the large-value-to-third-moment bound,
finite Holder interpolation, and the second- and fourth-moment estimates.
No asymptotic exponent has yet been taken in this file.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The three-term second-moment expression in Heath--Brown's relation. -/
noncomputable def heathBrownSecondMomentShape
    (T : Real) (M : Nat) (W : Finset Real) : Real :=
  (W.card : Real) ^ 2 * M +
    (W.card : Real) * M ^ 2 +
    (W.card : Real) ^ (5 / 4 : Real) * T ^ (1 / 2 : Real) * M

/-- The three-term fourth-moment expression in Heath--Brown's relation. -/
noncomputable def heathBrownFourthMomentShape
    (T : Real) (M : Nat) (W : Finset Real) : Real :=
  (W.card : Real) ^ 4 * M +
    (ApproxAddEnergy 1 W : Real) * M ^ 2 +
    (ApproxAddEnergy 1 W : Real) ^ (3 / 4 : Real) *
      (W.card : Real) * T ^ (1 / 2 : Real) * M

theorem heathBrownSecondMomentShape_nonneg
    (T : Real) (M : Nat) (W : Finset Real) (hT : 0 <= T) :
    0 <= heathBrownSecondMomentShape T M W := by
  unfold heathBrownSecondMomentShape
  have hCard : 0 <= (W.card : Real) := Nat.cast_nonneg W.card
  have hM : 0 <= (M : Real) := Nat.cast_nonneg M
  have hTSqrt : 0 <= T ^ (1 / 2 : Real) := Real.rpow_nonneg hT _
  have hCardRpow : 0 <= (W.card : Real) ^ (5 / 4 : Real) :=
    Real.rpow_nonneg hCard _
  exact add_nonneg
    (add_nonneg (mul_nonneg (pow_nonneg hCard 2) hM)
      (mul_nonneg hCard (pow_nonneg hM 2)))
    (mul_nonneg (mul_nonneg hCardRpow hTSqrt) hM)

theorem heathBrownFourthMomentShape_nonneg
    (T : Real) (M : Nat) (W : Finset Real) (hT : 0 <= T) :
    0 <= heathBrownFourthMomentShape T M W := by
  unfold heathBrownFourthMomentShape
  have hCard : 0 <= (W.card : Real) := Nat.cast_nonneg W.card
  have hM : 0 <= (M : Real) := Nat.cast_nonneg M
  have hEnergy : 0 <= (ApproxAddEnergy 1 W : Real) :=
    Nat.cast_nonneg (ApproxAddEnergy 1 W)
  have hEnergyRpow :
      0 <= (ApproxAddEnergy 1 W : Real) ^ (3 / 4 : Real) :=
    Real.rpow_nonneg hEnergy _
  have hTSqrt : 0 <= T ^ (1 / 2 : Real) := Real.rpow_nonneg hT _
  exact add_nonneg
    (add_nonneg (mul_nonneg (pow_nonneg hCard 4) hM)
      (mul_nonneg hEnergy (pow_nonneg hM 2)))
    (mul_nonneg (mul_nonneg (mul_nonneg hEnergyRpow hCard) hTSqrt) hM)

/-- The exact finite inequality behind the Heath--Brown exponent relation.

The two square-root factors are left visible.  Thus taking logarithmic
exponents gives one half of each of the second- and fourth-moment maxima,
exactly as in the source relation, without silently absorbing either moment.
-/
theorem heathBrownFiniteEnergyRelation_native :
    forall epsilon : Real, 0 < epsilon ->
      exists C0 C2 C4 T0 : Real,
        0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 <= T0 ∧
        forall (M : Nat) (T V : Real) (W : Finset Real) (b : Nat -> Complex),
          0 < M -> T0 <= T -> (M : Real) <= T -> 0 <= V ->
          IsSeparated 1 W -> InBaseInterval T W ->
          (∀ n ∈ dyadicInterval M, ‖b n‖ <= 1) ->
          (∀ t ∈ W, V <= ‖sourceDirichletPoly M b t‖) ->
          (ApproxAddEnergy 1 W : Real) * V ^ 2 <=
            C0 * T ^ (epsilon / 2) *
              Real.sqrt (C2 * T ^ (epsilon / 2) *
                heathBrownSecondMomentShape T M W) *
              Real.sqrt (C4 * T ^ (epsilon / 2) *
                heathBrownFourthMomentShape T M W) := by
  intro epsilon hepsilon
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C0, T0a, hC0, hT0a, hThird⟩ :=
    gmApproxAddEnergy_largeValues_native (epsilon / 2) hepsilonHalf
  obtain ⟨C2, T0b, hC2, hT0b, hSecond⟩ :=
    gmDiscreteRatioSecondMoment_native (epsilon / 2) hepsilonHalf
  obtain ⟨C4, T0c, hC4, hT0c, hFourth⟩ :=
    gmDiscreteFourthMoment_native (epsilon / 2) hepsilonHalf
  let T0 : Real := max T0a (max T0b T0c)
  refine ⟨C0, C2, C4, T0, hC0, hC2, hC4, ?_, ?_⟩
  · exact hT0a.trans (le_max_left T0a (max T0b T0c))
  intro M T V W b hM hT hMT hV hSep hBase hb hLarge
  have hTa : T0a <= T :=
    (le_max_left T0a (max T0b T0c)).trans hT
  have hTb : T0b <= T :=
    (le_max_left T0b T0c).trans
      ((le_max_right T0a (max T0b T0c)).trans hT)
  have hTc : T0c <= T :=
    (le_max_right T0b T0c).trans
      ((le_max_right T0a (max T0b T0c)).trans hT)
  have hThirdBound := hThird M T V W b hM hTa hMT hV hSep hb hLarge
  have hSecondBound := hSecond M T W hM hTb hSep hBase
  have hFourthBound := hFourth M T W hM hTc hMT hSep hBase
  have hTOne : 1 <= T := hT0a.trans hTa
  have hOuter : 0 <= C0 * T ^ (epsilon / 2) :=
    mul_nonneg hC0.le (Real.rpow_nonneg (zero_le_one.trans hTOne) _)
  have hSecondSqrt :
      Real.sqrt (gmDiscreteRatioMoment 2 M W) <=
        Real.sqrt (C2 * T ^ (epsilon / 2) *
          heathBrownSecondMomentShape T M W) := by
    simpa only [heathBrownSecondMomentShape] using
      (Real.sqrt_le_sqrt hSecondBound)
  have hFourthSqrt :
      Real.sqrt (gmDiscreteRatioMoment 4 M W) <=
        Real.sqrt (C4 * T ^ (epsilon / 2) *
          heathBrownFourthMomentShape T M W) := by
    simpa only [heathBrownFourthMomentShape] using
      (Real.sqrt_le_sqrt hFourthBound)
  calc
    (ApproxAddEnergy 1 W : Real) * V ^ 2 <=
        C0 * T ^ (epsilon / 2) * gmDiscreteRatioMoment 3 M W :=
      hThirdBound
    _ <= C0 * T ^ (epsilon / 2) *
        (Real.sqrt (gmDiscreteRatioMoment 2 M W) *
          Real.sqrt (gmDiscreteRatioMoment 4 M W)) := by
      exact mul_le_mul_of_nonneg_left
        (gmDiscreteThirdMoment_le_sqrt M W) hOuter
    _ <= C0 * T ^ (epsilon / 2) *
        (Real.sqrt (C2 * T ^ (epsilon / 2) *
            heathBrownSecondMomentShape T M W) *
          Real.sqrt (C4 * T ^ (epsilon / 2) *
            heathBrownFourthMomentShape T M W)) := by
      apply mul_le_mul_of_nonneg_left _ hOuter
      exact mul_le_mul hSecondSqrt hFourthSqrt
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = C0 * T ^ (epsilon / 2) *
          Real.sqrt (C2 * T ^ (epsilon / 2) *
            heathBrownSecondMomentShape T M W) *
          Real.sqrt (C4 * T ^ (epsilon / 2) *
            heathBrownFourthMomentShape T M W) := by ring

/-- Symmetric-height form of the finite Heath--Brown relation.  It performs
the exact ordinate translation, coefficient phase twist, interval inclusion,
cardinality preservation, and energy-translation rewrite. -/
theorem heathBrownFiniteSymmetricEnergyRelation_native :
    forall epsilon : Real, 0 < epsilon ->
      exists C0 C2 C4 T0 : Real,
        0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 <= T0 ∧
        forall (M : Nat) (B R V : Real) (W : Finset Real)
            (b : Nat -> Complex),
          0 < M -> T0 <= B -> (M : Real) <= B -> 0 <= V ->
          2 * R <= B -> IsSeparated 1 W ->
          (forall t, t ∈ W -> -R <= t ∧ t <= R) ->
          (∀ n ∈ dyadicInterval M, ‖b n‖ <= 1) ->
          (∀ t ∈ W, V <= ‖sourceDirichletPoly M b t‖) ->
          (ApproxAddEnergy 1 W : Real) * V ^ 2 <=
            C0 * B ^ (epsilon / 2) *
              Real.sqrt (C2 * B ^ (epsilon / 2) *
                heathBrownSecondMomentShape B M W) *
              Real.sqrt (C4 * B ^ (epsilon / 2) *
                heathBrownFourthMomentShape B M W) := by
  intro epsilon hepsilon
  obtain ⟨C0, C2, C4, T0, hC0, hC2, hC4, hT0, hFinite⟩ :=
    heathBrownFiniteEnergyRelation_native epsilon hepsilon
  refine ⟨C0, C2, C4, T0, hC0, hC2, hC4, hT0, ?_⟩
  intro M B R V W b hM hB hMB hV hRB hSep hSymm hb hLarge
  let WT := gmTranslate R W
  let bT := phaseShiftCoeffs R b
  have hSepT : IsSeparated 1 WT :=
    isSeparated_gmTranslate 1 R W hSep
  have hBaseT : InBaseInterval B WT := by
    have hBaseSmall := inBaseInterval_gmTranslate_of_symmetric R W hSymm
    intro t ht
    obtain ⟨ht0, htUpper⟩ := hBaseSmall t ht
    exact ⟨ht0, htUpper.trans hRB⟩
  have hbT : ∀ n ∈ dyadicInterval M, ‖bT n‖ <= 1 :=
    norm_phaseShiftCoeffs_le_one_on M b R hb
  have hLargeT : ∀ t ∈ WT, V <= ‖sourceDirichletPoly M bT t‖ :=
    sourceDirichletPoly_large_on_gmTranslate M b R V W hLarge
  have h := hFinite M B V WT bT hM hB hMB hV hSepT hBaseT hbT hLargeT
  simpa only [WT, bT, approxAddEnergy_translate, card_gmTranslate,
    heathBrownSecondMomentShape, heathBrownFourthMomentShape] using h

#print axioms heathBrownFiniteEnergyRelation_native
#print axioms heathBrownFiniteSymmetricEnergyRelation_native

end

end GafniTao
