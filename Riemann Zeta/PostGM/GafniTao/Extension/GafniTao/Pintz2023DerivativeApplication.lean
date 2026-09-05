import GafniTao.Pintz2023LogPhase

/-!
# Pintz (2023), Corollary 1: applying the k-th derivative theorem

The source phase on `(N,R]` is translated to `[1,R-N]`.  Its k-th
derivative has constant sign; the parity split changes the phase by a minus
sign when necessary, which preserves the norm of the exponential sum.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The positive magnitude of the k-th derivative of Pintz's phase. -/
noncomputable def pintz2023DerivativeMagnitude
    (k N : ℕ) (t x : ℝ) : ℝ :=
  t / (2 * Real.pi) * (k - 1).factorial *
    ((N : ℝ) + x) ^ (-(k : ℕ) : ℤ)

/-- The lower derivative scale obtained at the right endpoint `2N`. -/
noncomputable def pintz2023DerivativeLambda
    (k N : ℕ) (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * (k - 1).factorial *
    (2 * (N : ℝ)) ^ (-(k : ℕ) : ℤ)

/-- A negative integral power reverses positive base inequalities. -/
theorem zpow_neg_nat_antitone
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    b ^ (-(k : ℕ) : ℤ) ≤ a ^ (-(k : ℕ) : ℤ) := by
  have hb : 0 < b := ha.trans_le hab
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
  exact (inv_le_inv₀ (pow_pos hb k) (pow_pos ha k)).2
    (pow_le_pow_left₀ ha.le hab k)

/-- Exact factorization behind the uniform ratio `2^k` between the two
endpoint derivative scales. -/
theorem zpow_neg_nat_two_mul
    {N k : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (-(k : ℕ) : ℤ) =
      (2 : ℝ) ^ k * (2 * (N : ℝ)) ^ (-(k : ℕ) : ℤ) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show 2 * (N : ℝ) = (2 : ℝ) * (N : ℝ) by ring,
    mul_zpow]
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
  field_simp

/-- On every translated subinterval of `(N,2N]`, the derivative magnitude
lies between the endpoint scale and `2^k` times that scale. -/
theorem pintz2023DerivativeMagnitude_bounds
    {k N L : ℕ} {t x : ℝ}
    (hN : 0 < N) (ht : 0 ≤ t) (hLN : L ≤ N)
    (hx : x ∈ Set.Icc (0 : ℝ) L) :
    pintz2023DerivativeLambda k N t ≤
        pintz2023DerivativeMagnitude k N t x ∧
      pintz2023DerivativeMagnitude k N t x ≤
        (2 : ℝ) ^ k * pintz2023DerivativeLambda k N t := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hLReal : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hbaseLower : (N : ℝ) ≤ (N : ℝ) + x := by linarith [hx.1]
  have hbaseUpper : (N : ℝ) + x ≤ 2 * (N : ℝ) := by
    linarith [hx.2]
  have hbasePos : 0 < (N : ℝ) + x := hNReal.trans_le hbaseLower
  have hlower := zpow_neg_nat_antitone hbasePos hbaseUpper k
  have hupper := zpow_neg_nat_antitone hNReal hbaseLower k
  have hfactor : 0 ≤ t / (2 * Real.pi) * (k - 1).factorial := by positivity
  constructor
  · unfold pintz2023DerivativeLambda pintz2023DerivativeMagnitude
    exact mul_le_mul_of_nonneg_left hlower hfactor
  · unfold pintz2023DerivativeLambda pintz2023DerivativeMagnitude
    calc
      t / (2 * Real.pi) * (k - 1).factorial *
          ((N : ℝ) + x) ^ (-(k : ℕ) : ℤ) ≤
          (t / (2 * Real.pi) * (k - 1).factorial) *
            (N : ℝ) ^ (-(k : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hupper hfactor
      _ = (2 : ℝ) ^ k *
          (t / (2 * Real.pi) * (k - 1).factorial *
            (2 * (N : ℝ)) ^ (-(k : ℕ) : ℤ)) := by
        rw [zpow_neg_nat_two_mul hN]
        ring

/-- For even derivative order the source phase itself has positive k-th
derivative. -/
theorem iteratedDeriv_pintz2023LogPhase_of_even
    {k N : ℕ} {t x : ℝ} (hk : 1 ≤ k) (hkEven : Even k)
    (hNx : 0 < (N : ℝ) + x) :
    iteratedDeriv k (fun y : ℝ => pintz2023LogPhase t (N + y)) x =
      pintz2023DerivativeMagnitude k N t x := by
  rw [iteratedDeriv_pintz2023LogPhase hk hNx]
  rcases hkEven with ⟨j, hj⟩
  have hjPos : 0 < j := by omega
  have hodd : Odd (k - 1) := ⟨j - 1, by omega⟩
  rw [hodd.neg_one_pow]
  unfold pintz2023DerivativeMagnitude
  ring

/-- For odd derivative order the negative source phase has positive k-th
derivative. -/
theorem iteratedDeriv_neg_pintz2023LogPhase_of_odd
    {k N : ℕ} {t x : ℝ} (hk : 1 ≤ k) (hkOdd : Odd k)
    (hNx : 0 < (N : ℝ) + x) :
    iteratedDeriv k
        (fun y : ℝ => -pintz2023LogPhase t (N + y)) x =
      pintz2023DerivativeMagnitude k N t x := by
  rw [iteratedDeriv_fun_neg]
  rw [iteratedDeriv_pintz2023LogPhase hk hNx]
  rcases hkOdd with ⟨j, hj⟩
  have heven : Even (k - 1) := ⟨j, by omega⟩
  rw [heven.neg_one_pow]
  unfold pintz2023DerivativeMagnitude
  ring

/-- The literal unweighted oscillatory block in Pintz Corollary 1. -/
noncomputable def pintz2023ExponentialBlock
    (N R : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N R, (n : ℂ) ^ (-(t : ℂ) * I)

/-- Translation from the source half-open interval to Heath-Brown's
positive initial interval. -/
theorem heathBrownExponentialSum_shifted_eq_pintz2023Block
    {N R : ℕ} (hNR : N ≤ R) (t : ℝ) :
    heathBrownExponentialSum (R - N)
        (fun x : ℝ => pintz2023LogPhase t (N + x)) =
      pintz2023ExponentialBlock N R t := by
  classical
  unfold heathBrownExponentialSum pintz2023ExponentialBlock
  symm
  refine Finset.sum_nbij (fun n => n - N) ?_ ?_ ?_ ?_
  · intro n hn
    change n ∈ Finset.Ioc N R at hn
    change n - N ∈ Finset.Icc 1 (R - N)
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    change a ∈ Finset.Ioc N R at ha
    change b ∈ Finset.Ioc N R at hb
    rw [Finset.mem_Ioc] at ha hb
    change a - N = b - N at hab
    omega
  · intro b hb
    change b ∈ Finset.Icc 1 (R - N) at hb
    rw [Finset.mem_Icc] at hb
    refine ⟨N + b, ?_, ?_⟩
    rw [Finset.mem_coe, Finset.mem_Ioc]
    omega
    change N + b - N = b
    omega
  · intro n hn
    change n ∈ Finset.Ioc N R at hn
    rw [Finset.mem_Ioc] at hn
    have hnPos : 0 < n := by omega
    have hshift : (N : ℝ) + (n - N : ℕ) = (n : ℝ) := by
      norm_cast
      omega
    change (n : ℂ) ^ (-(t : ℂ) * I) =
      heathBrownPhase (pintz2023LogPhase t
        ((N : ℝ) + (n - N : ℕ)))
    rw [hshift, heathBrownPhase_pintz2023LogPhase hnPos]

/-- The same translation after the parity-forced sign change. -/
theorem norm_heathBrownExponentialSum_neg_shifted_eq_pintz2023Block
    {N R : ℕ} (hNR : N ≤ R) (t : ℝ) :
    ‖heathBrownExponentialSum (R - N)
        (fun x : ℝ => -pintz2023LogPhase t (N + x))‖ =
      ‖pintz2023ExponentialBlock N R t‖ := by
  rw [norm_heathBrownExponentialSum_neg,
    heathBrownExponentialSum_shifted_eq_pintz2023Block hNR]

/-- Direct source-interval application of the now-native Heath-Brown
k-th derivative theorem.  The displayed majorant is still in
Heath-Brown's three-term form; Pintz's three powers are extracted in the
next file. -/
theorem norm_pintz2023ExponentialBlock_le_heathBrown
    (k : ℕ) (epsilon : ℝ) (hk : 3 ≤ k) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (t : ℝ),
      0 < N → N < R → R ≤ 2 * N → 0 < t →
      ‖pintz2023ExponentialBlock N R t‖ ≤
        C * ((R - N : ℕ) : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k (R - N)
            (pintz2023DerivativeLambda k N t) := by
  obtain ⟨C, hC, hmain⟩ := heathBrownKthDerivativeTheorem_native
    k ((2 : ℝ) ^ k) epsilon hk (by positivity) hepsilon
  refine ⟨C, hC, ?_⟩
  intro N R t hN hNR hR ht
  have hLPos : 1 ≤ R - N := by omega
  have hLN : R - N ≤ N := by omega
  have hlambda : 0 < pintz2023DerivativeLambda k N t := by
    unfold pintz2023DerivativeLambda
    have hbase : 0 < 2 * (N : ℝ) := by positivity
    positivity
  have hreg := pintz2023LogPhase_contDiffOn k t (L := R - N) hN
  have hregOpen : ContDiffOn ℝ k
      (fun x : ℝ => pintz2023LogPhase t (N + x))
      (Set.Ioo 0 ((R - N : ℕ) : ℝ)) :=
    hreg.mono (by
      intro x hx
      exact ⟨hx.1.le, hx.2.le⟩)
  rcases Nat.even_or_odd k with hkEven | hkOdd
  · have hbound := hmain (R - N) (pintz2023DerivativeLambda k N t)
        (fun x : ℝ => pintz2023LogPhase t (N + x)) hLPos hlambda
        hreg.continuousOn hregOpen (by
          intro x hx
          rw [iteratedDeriv_pintz2023LogPhase_of_even (by omega) hkEven
            (by
              have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
              linarith [hx.1])]
          exact pintz2023DerivativeMagnitude_bounds hN ht.le hLN
            ⟨hx.1.le, hx.2.le⟩)
    rw [heathBrownExponentialSum_shifted_eq_pintz2023Block hNR.le] at hbound
    simpa [Nat.cast_sub hNR.le] using hbound
  · have hregNeg : ContDiffOn ℝ k
        (fun x : ℝ => -pintz2023LogPhase t (N + x))
        (Set.Icc 0 ((R - N : ℕ) : ℝ)) := hreg.neg
    have hregNegOpen : ContDiffOn ℝ k
        (fun x : ℝ => -pintz2023LogPhase t (N + x))
        (Set.Ioo 0 ((R - N : ℕ) : ℝ)) :=
      hregNeg.mono (by
        intro x hx
        exact ⟨hx.1.le, hx.2.le⟩)
    have hbound := hmain (R - N) (pintz2023DerivativeLambda k N t)
        (fun x : ℝ => -pintz2023LogPhase t (N + x)) hLPos hlambda
        hregNeg.continuousOn hregNegOpen (by
          intro x hx
          rw [iteratedDeriv_neg_pintz2023LogPhase_of_odd (by omega) hkOdd
            (by
              have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
              linarith [hx.1])]
          exact pintz2023DerivativeMagnitude_bounds hN ht.le hLN
            ⟨hx.1.le, hx.2.le⟩)
    rw [norm_heathBrownExponentialSum_neg_shifted_eq_pintz2023Block
      hNR.le] at hbound
    simpa [Nat.cast_sub hNR.le] using hbound

#print axioms iteratedDeriv_pintz2023LogPhase_of_even
#print axioms iteratedDeriv_neg_pintz2023LogPhase_of_odd
#print axioms heathBrownExponentialSum_shifted_eq_pintz2023Block
#print axioms norm_heathBrownExponentialSum_neg_shifted_eq_pintz2023Block
#print axioms norm_pintz2023ExponentialBlock_le_heathBrown

end

end GafniTao
