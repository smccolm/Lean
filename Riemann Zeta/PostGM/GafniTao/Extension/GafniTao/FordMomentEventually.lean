import GafniTao.FordLemma35Index

/-!
# Eventual Vinogradov moment bounds

The audited PNT gives Ford's prime packets only eventually.  This file proves
the precise finite-prefix repair needed to iterate Lemma 3.4: an eventual
moment estimate with a fixed exponent extends to all positive integral
endpoints after enlarging only its coefficient.
-/

namespace GafniTao

noncomputable section

open Filter

/-- The literal finite count has the trivial `Q^(2s)` upper bound. -/
theorem fordVinogradovMomentNat_le_trivial (s k Q : ℕ) :
    fordVinogradovMomentNat s k Q ≤ Q ^ (2 * s) := by
  unfold fordVinogradovMomentNat fordVinogradovShiftedCountNat
    fordRepresentationCount
  calc
    (((Finset.univ : Finset (FordVinogradovTuple s Q)) ×ˢ
        (Finset.univ : Finset (FordVinogradovTuple s Q))).filter
          fun xy => fordVinogradovPowerVector s k Q xy.1 -
            fordVinogradovPowerVector s k Q xy.2 = 0).card ≤
        ((Finset.univ : Finset (FordVinogradovTuple s Q)) ×ˢ
          (Finset.univ : Finset (FordVinogradovTuple s Q))).card :=
      Finset.card_filter_le _ _
    _ = (Q ^ s) * (Q ^ s) := by
      rw [Finset.card_product, card_fordVinogradovTuple_univ]
    _ = Q ^ (2 * s) := by
      rw [← pow_add]
      congr 1
      omega

/-- An eventual version of Ford's moment hypothesis, with exactly the same
exponent and no epsilon loss. -/
def FordVinogradovMomentBoundEventually
    (s k : ℕ) (C delta : ℝ) : Prop :=
  ∀ᶠ Q : ℕ in atTop,
    (fordVinogradovMomentNat s k Q : ℝ) ≤
      C * (Q : ℝ) ^ fordLambda34 s k delta

theorem FordVinogradovMomentBound.toEventually
    {s k : ℕ} {C delta : ℝ}
    (h : FordVinogradovMomentBound s k C delta) :
    FordVinogradovMomentBoundEventually s k C delta := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with Q hQ
  exact h Q hQ

theorem FordVinogradovMomentBoundEventually.lambda_nonneg
    {s k : ℕ} {C delta : ℝ}
    (hmoment : FordVinogradovMomentBoundEventually s k C delta) :
    0 ≤ fordLambda34 s k delta := by
  let lambda := fordLambda34 s k delta
  by_contra hneg
  have hlambda : lambda < 0 := lt_of_not_ge hneg
  have htReal : Tendsto (fun x : ℝ => C * x ^ lambda)
      atTop (nhds 0) := by
    have ht := (tendsto_rpow_neg_atTop (y := -lambda) (by linarith)).const_mul C
    simpa [show - -lambda = lambda by ring] using ht
  have htNat : Tendsto (fun n : ℕ => C * (n : ℝ) ^ lambda)
      atTop (nhds 0) :=
    htReal.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ lambda < 1 :=
    htNat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hbound, hnsmall, hn⟩ :=
    (hmoment.and (hsmall.and (eventually_ge_atTop (1 : ℕ)))).exists
  have hone : (1 : ℝ) ≤ fordVinogradovMomentNat s k n := by
    have hdiag := fordVinogradovMoment_one_le s k (Q := (n : ℝ))
      (by exact_mod_cast hn)
    simpa [fordVinogradovMoment] using hdiag
  exact (not_lt_of_ge (hone.trans (by simpa [lambda] using hbound))) hnsmall

/-- Any eventual fixed-exponent estimate becomes Ford's all-positive-endpoint
hypothesis after absorbing the finitely many omitted endpoints into one
coefficient.  The exponent is unchanged. -/
theorem FordVinogradovMomentBoundEventually.exists_global_coefficient
    {s k : ℕ} {C delta : ℝ}
    (hmoment : FordVinogradovMomentBoundEventually s k C delta) :
    ∃ C' : ℝ, C ≤ C' ∧ FordVinogradovMomentBound s k C' delta := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmoment
  let R : ℕ := max N 1
  let C' : ℝ := max C ((R : ℝ) ^ (2 * s))
  have hR1 : 1 ≤ R := Nat.le_max_right _ _
  have hCnonneg : 0 ≤ C' := by
    exact (by positivity : (0 : ℝ) ≤ (R : ℝ) ^ (2 * s)).trans
      (le_max_right _ _)
  have hlambda := hmoment.lambda_nonneg
  refine ⟨C', le_max_left _ _, ?_⟩
  intro Q hQ
  by_cases hNQ : N ≤ Q
  · have hsource := hN Q hNQ
    exact hsource.trans (mul_le_mul_of_nonneg_right
      (le_max_left C ((R : ℝ) ^ (2 * s))) (Real.rpow_nonneg (by positivity) _))
  · have hQR : Q ≤ R := by
      have hQN : Q < N := Nat.lt_of_not_ge hNQ
      exact hQN.le.trans (Nat.le_max_left _ _)
    have htrivialNat := fordVinogradovMomentNat_le_trivial s k Q
    have htrivial : (fordVinogradovMomentNat s k Q : ℝ) ≤
        (Q : ℝ) ^ (2 * s) := by exact_mod_cast htrivialNat
    have hpower : (Q : ℝ) ^ (2 * s) ≤ (R : ℝ) ^ (2 * s) := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hQR) _
    have htoC : (fordVinogradovMomentNat s k Q : ℝ) ≤ C' :=
      htrivial.trans (hpower.trans (le_max_right _ _))
    have hQrpow : 1 ≤ (Q : ℝ) ^ fordLambda34 s k delta := by
      exact Real.one_le_rpow (by exact_mod_cast hQ) hlambda
    exact htoC.trans (by
      calc
        C' = C' * 1 := by ring
        _ ≤ C' * (Q : ℝ) ^ fordLambda34 s k delta := by gcongr)

#print axioms fordVinogradovMomentNat_le_trivial
#print axioms FordVinogradovMomentBound.toEventually
#print axioms FordVinogradovMomentBoundEventually.lambda_nonneg
#print axioms FordVinogradovMomentBoundEventually.exists_global_coefficient

end

end GafniTao
