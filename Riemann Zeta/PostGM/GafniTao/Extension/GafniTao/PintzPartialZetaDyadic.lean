import GafniTao.PintzPartialZeta
import GafniTao.FordDyadicDecomposition

/-!
# A source-corrected partial-zeta bound for the Pintz Gram matrix

The partial Dirichlet sum in Pintz's displayed definition of `M₁` cannot be
bounded uniformly in the cutoff by the zeta bound alone.  The correction used
here keeps Ford's estimate on dyadic shells whose left endpoint is below the
frequency and uses the frozen foundation's Kusmin--Landau/Abel estimate once
the left endpoint is beyond the frequency.  Thus the long-cutoff contribution
retains the indispensable inverse-frequency factor.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- At shift zero, Ford's phase is the frozen foundation's logarithmic phase. -/
theorem fordShiftedLogPhase_zero_eq_unitary
    (n : ℕ) (t : ℝ) :
    fordShiftedLogPhase n 0 t =
      unitaryPhase (logarithmicPhase t n) := by
  unfold fordShiftedLogPhase unitaryPhase logarithmicPhase
  simp only [add_zero, ofReal_neg, ofReal_mul]
  congr 1
  ring

/-- The zero-shift weighted Ford term is the ordinary Dirichlet monomial. -/
theorem fordShiftedWeightedTerm_zero_eq_cpow
    {sigma t : ℝ} {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) ^ (-sigma)) • fordShiftedLogPhase n 0 t =
      (n : ℂ) ^ (-fordComplexHeight sigma t) := by
  rw [fordShiftedLogPhase_zero_eq_unitary,
    Complex.real_smul, unitaryPhase_logarithmicPhase_eq_cpow t n hn]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  change (n : ℂ) ^ ((-sigma : ℝ) : ℂ) *
      (n : ℂ) ^ (-(t : ℂ) * I) = _
  rw [← Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
  congr 2
  unfold fordComplexHeight
  push_cast
  ring

/-- A zero-shift Ford block is exactly the corresponding ordinary partial-zeta
block. -/
theorem fordShiftedWeightedBlock_zero_eq_partialZeta
    (sigma : ℝ) {N R : ℕ} (t : ℝ) (hN : 0 < N) :
    fordShiftedWeightedBlock sigma N R 0 t =
      ∑ n ∈ Finset.Ioc N R,
        (n : ℂ) ^ (-fordComplexHeight sigma t) := by
  unfold fordShiftedWeightedBlock
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro n hn
  exact fordShiftedWeightedTerm_zero_eq_cpow
    (hN.trans (Finset.mem_Ioc.mp hn).1)

/-- A shifted Ford block is the difference of its two finite Hurwitz heads. -/
theorem fordShiftedWeightedBlock_eq_finite_sub
    {sigma u t : ℝ} {N R : ℕ} (hu : 0 < u) (hNR : N ≤ R) :
    fordShiftedWeightedBlock sigma N R u t =
      fordFiniteHurwitzSum sigma R u t -
        fordFiniteHurwitzSum sigma N u t := by
  rw [fordShiftedWeightedBlock_eq_cpow sigma N R hu]
  unfold fordFiniteHurwitzSum
  have hUnion : Finset.Icc 1 R =
      Finset.Icc 1 N ∪ Finset.Ioc N R := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hDisjoint : Disjoint (Finset.Icc 1 N) (Finset.Ioc N R) := by
    exact Finset.disjoint_left.mpr fun n hn hnr => by
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_Ioc] at hnr
      omega
  rw [hUnion, Finset.sum_union hDisjoint]
  ring

/-- The same head-difference identity at shift zero. -/
theorem fordShiftedWeightedBlock_zero_eq_finite_sub
    (sigma : ℝ) {N R : ℕ} (t : ℝ) (hN : 0 < N) (hNR : N ≤ R) :
    fordShiftedWeightedBlock sigma N R 0 t =
      fordFiniteHurwitzSum sigma R 0 t -
        fordFiniteHurwitzSum sigma N 0 t := by
  rw [fordShiftedWeightedBlock_zero_eq_partialZeta sigma t hN,
    fordFiniteHurwitzSum_zero_eq_partialSum_general,
    fordFiniteHurwitzSum_zero_eq_partialSum_general]
  have hUnion : Finset.Icc 1 R =
      Finset.Icc 1 N ∪ Finset.Ioc N R := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hDisjoint : Disjoint (Finset.Icc 1 N) (Finset.Ioc N R) := by
    exact Finset.disjoint_left.mpr fun n hn hnr => by
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_Ioc] at hnr
      omega
  rw [hUnion, Finset.sum_union hDisjoint]
  ring

/-- Ford's shifted Theorem 2 estimate extends continuously to shift zero on
one dyadic shell. -/
theorem norm_fordShiftedWeightedBlock_zero_le_of_fordTheorem2
    (hFord : FordTheorem2)
    {sigma t : ℝ} {N R : ℕ}
    (hsigma : 0 ≤ sigma) (hN : 0 < N) (hNt : (N : ℝ) ≤ t)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      (N + 1 : ℝ) ^ (-sigma) * fordTheorem2Majorant N t := by
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have huLim : Tendsto u atTop (𝓝 0) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hRLim : Tendsto
      (fun k => fordFiniteHurwitzSum sigma R (u k) t)
        atTop (𝓝 (fordFiniteHurwitzSum sigma R 0 t)) :=
    (continuousAt_fordFiniteHurwitzSum_zero
      (sigma := sigma) (t := t) R).tendsto.comp huLim
  have hNLim : Tendsto
      (fun k => fordFiniteHurwitzSum sigma N (u k) t)
        atTop (𝓝 (fordFiniteHurwitzSum sigma N 0 t)) :=
    (continuousAt_fordFiniteHurwitzSum_zero
      (sigma := sigma) (t := t) N).tendsto.comp huLim
  have hsumLim : Tendsto
      (fun k => fordShiftedWeightedBlock sigma N R (u k) t)
        atTop (𝓝 (fordShiftedWeightedBlock sigma N R 0 t)) := by
    have hdiff := hRLim.sub hNLim
    rw [fordShiftedWeightedBlock_zero_eq_finite_sub sigma t hN hNR.le]
    exact hdiff.congr' (Filter.Eventually.of_forall fun k =>
      (fordShiftedWeightedBlock_eq_finite_sub
        (sigma := sigma) (t := t)
        (by
          show 0 < 1 / ((k : ℝ) + 1)
          positivity) hNR.le).symm)
  apply le_of_tendsto hsumLim.norm
  filter_upwards [] with k
  have huPos : 0 < u k := by dsimp [u]; positivity
  have huOne : u k ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by positivity)]
    norm_num
  have hraw := norm_fordShiftedWeightedBlock_le_of_fordTheorem2 hFord
    hsigma hN hNt huPos huOne hNR hR
  simp only [Nat.cast_add, Nat.cast_one] at hraw
  exact hraw.trans (by
    have hbase : (N : ℝ) + 1 ≤ (N : ℝ) + 1 + u k := by
      exact le_add_of_nonneg_right huPos.le
    have hpow := Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < (N + 1 : ℝ)) hbase (by linarith : -sigma ≤ 0)
    exact mul_le_mul_of_nonneg_right hpow (by
      unfold fordTheorem2Majorant
      positivity))

/-- Zero-shift extension for a general proved Ford exponential-sum estimate. -/
theorem norm_fordShiftedWeightedBlock_zero_le_general
    {C D sigma t : ℝ} {N R : ℕ}
    (hFord : FordExponentialSumEstimate C D)
    (hC : 0 ≤ C) (hsigma : 0 ≤ sigma) (hN : 0 < N)
    (hNt : (N : ℝ) ≤ t) (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      (N + 1 : ℝ) ^ (-sigma) * fordGeneralMajorant C D N t := by
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have huLim : Tendsto u atTop (𝓝 0) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hRLim : Tendsto
      (fun k => fordFiniteHurwitzSum sigma R (u k) t)
        atTop (𝓝 (fordFiniteHurwitzSum sigma R 0 t)) :=
    (continuousAt_fordFiniteHurwitzSum_zero
      (sigma := sigma) (t := t) R).tendsto.comp huLim
  have hNLim : Tendsto
      (fun k => fordFiniteHurwitzSum sigma N (u k) t)
        atTop (𝓝 (fordFiniteHurwitzSum sigma N 0 t)) :=
    (continuousAt_fordFiniteHurwitzSum_zero
      (sigma := sigma) (t := t) N).tendsto.comp huLim
  have hsumLim : Tendsto
      (fun k => fordShiftedWeightedBlock sigma N R (u k) t)
        atTop (𝓝 (fordShiftedWeightedBlock sigma N R 0 t)) := by
    have hdiff := hRLim.sub hNLim
    rw [fordShiftedWeightedBlock_zero_eq_finite_sub sigma t hN hNR.le]
    exact hdiff.congr' (Filter.Eventually.of_forall fun k =>
      (fordShiftedWeightedBlock_eq_finite_sub
        (sigma := sigma) (t := t)
        (by
          show 0 < 1 / ((k : ℝ) + 1)
          positivity) hNR.le).symm)
  apply le_of_tendsto hsumLim.norm
  filter_upwards [] with k
  have huPos : 0 < u k := by dsimp [u]; positivity
  have huOne : u k ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by positivity)]
    norm_num
  have hraw := norm_fordShiftedWeightedBlock_le_general hFord
    hsigma hN hNt huPos huOne hNR hR
  simp only [Nat.cast_add, Nat.cast_one] at hraw
  exact hraw.trans (by
    have hbase : (N : ℝ) + 1 ≤ (N : ℝ) + 1 + u k :=
      le_add_of_nonneg_right huPos.le
    have hpow := Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < (N + 1 : ℝ)) hbase (by linarith : -sigma ≤ 0)
    exact mul_le_mul_of_nonneg_right hpow (by
      unfold fordGeneralMajorant
      exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)))

/-- The frozen terminal Kusmin--Landau theorem, rewritten as a Ford block at
shift zero. -/
theorem norm_fordShiftedWeightedBlock_zero_le_terminal
    {sigma t : ℝ} {N R : ℕ}
    (hsigma : 0 ≤ sigma) (hN : 0 < N) (hNR : N < R)
    (hR : R ≤ 2 * N) (htOne : 1 ≤ t) (htN : t ≤ (N : ℝ)) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      (N + 1 : ℝ) ^ (-sigma) * (6 * Real.pi * (N : ℝ) / t) := by
  have hLPos : 0 < R - N := Nat.sub_pos_of_lt hNR
  have hL : R - N ≤ N := by omega
  have hterminal := norm_terminalWeightedBlock_le sigma t N (R - N)
    hsigma hN hLPos hL htOne htN
  have hblock : fordShiftedWeightedBlock sigma N R 0 t =
      ∑ n ∈ Finset.range (R - N),
        ((N + 1 + n : ℝ) ^ (-sigma) : ℝ) •
          unitaryPhase (logarithmicPhase t (N + 1 + n)) := by
    unfold fordShiftedWeightedBlock
    rw [Finset.Ioc_eq_Ico, Finset.sum_Ico_eq_sum_range]
    have hlen : R + 1 - (N + 1) = R - N := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [fordShiftedLogPhase_zero_eq_unitary]
    simp only [add_zero]
    push_cast
    rfl
  rw [hblock]
  exact hterminal

/-- A single nonnegative majorant covering both sides of the transition
`2^j ≶ t`. -/
noncomputable def pintzDyadicPartialZetaMajorant
    (sigma : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  fordGeneralDyadicRawMajorant fordQualitativeCoefficient 3000000
      sigma j 0 t +
    ((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) *
      (6 * Real.pi * ((2 ^ j : ℕ) : ℝ) / t)

theorem pintzDyadicPartialZetaMajorant_nonneg
    {sigma t : ℝ} {j : ℕ} (ht : 0 < t) :
    0 ≤ pintzDyadicPartialZetaMajorant sigma j t := by
  unfold pintzDyadicPartialZetaMajorant
  have hraw : 0 ≤ fordGeneralDyadicRawMajorant
      fordQualitativeCoefficient 3000000 sigma j 0 t := by
    unfold fordGeneralDyadicRawMajorant fordGeneralMajorant
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg fordQualitativeCoefficient_nonneg
        (Real.rpow_nonneg (by positivity) _))
  exact add_nonneg
    hraw
    (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (div_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) ht.le))

/-- Every terminally truncated dyadic shell is controlled by the corrected
two-regime majorant. -/
theorem norm_fordShiftedWeightedBlock_zero_dyadic_le
    {sigma t : ℝ} {j M : ℕ}
    (hsigma : 0 ≤ sigma) (htOne : 1 ≤ t) :
    ‖fordShiftedWeightedBlock sigma (2 ^ j)
        (min M (2 ^ (j + 1))) 0 t‖ ≤
      pintzDyadicPartialZetaMajorant sigma j t := by
  by_cases hNonempty : 2 ^ j < min M (2 ^ (j + 1))
  · have hUpper : min M (2 ^ (j + 1)) ≤ 2 * 2 ^ j := by
      calc
        min M (2 ^ (j + 1)) ≤ 2 ^ (j + 1) := min_le_right _ _
        _ = 2 * 2 ^ j := by rw [pow_succ]; omega
    by_cases hNt : ((2 ^ j : ℕ) : ℝ) ≤ t
    · have hford := norm_fordShiftedWeightedBlock_zero_le_general
        ford_exponential_sum_qualitative fordQualitativeCoefficient_nonneg
        hsigma (pow_pos (by omega) _) hNt hNonempty hUpper
      have hterminalNonneg :
          0 ≤ (((2 ^ j : ℕ) : ℝ) + 1) ^ (-sigma) *
            (6 * Real.pi * ((2 ^ j : ℕ) : ℝ) / t) := by positivity
      exact hford.trans (by
        unfold pintzDyadicPartialZetaMajorant fordGeneralDyadicRawMajorant
        simp only [Nat.cast_add, Nat.cast_one, add_zero]
        exact le_add_of_nonneg_right hterminalNonneg)
    · have htN : t ≤ ((2 ^ j : ℕ) : ℝ) := le_of_not_ge hNt
      have hterminal := norm_fordShiftedWeightedBlock_zero_le_terminal
        hsigma (pow_pos (by omega) _) hNonempty hUpper htOne htN
      have hrawNonneg : 0 ≤ fordGeneralDyadicRawMajorant
          fordQualitativeCoefficient 3000000 sigma j 0 t := by
        unfold fordGeneralDyadicRawMajorant fordGeneralMajorant
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (mul_nonneg fordQualitativeCoefficient_nonneg
            (Real.rpow_nonneg (by positivity) _))
      exact hterminal.trans (by
        unfold pintzDyadicPartialZetaMajorant
        simp only [Nat.cast_add, Nat.cast_one]
        exact le_add_of_nonneg_left hrawNonneg)
  · have hEmpty : Finset.Ioc (2 ^ j) (min M (2 ^ (j + 1))) = ∅ :=
      Finset.Ioc_eq_empty hNonempty
    rw [fordShiftedWeightedBlock, hEmpty, Finset.sum_empty, norm_zero]
    exact pintzDyadicPartialZetaMajorant_nonneg (lt_of_lt_of_le zero_lt_one htOne)

/-- The corrected full finite-sum majorant.  The leading `1` is the exact
`n=1` term and every remaining summand is a literal dyadic shell. -/
noncomputable def pintzCorrectedPartialZetaMajorant
    (sigma : ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.range (Nat.clog 2 M),
    pintzDyadicPartialZetaMajorant sigma j t

theorem pintzCorrectedPartialZetaMajorant_nonneg
    {sigma t : ℝ} {M : ℕ} (ht : 0 < t) :
    0 ≤ pintzCorrectedPartialZetaMajorant sigma M t := by
  unfold pintzCorrectedPartialZetaMajorant
  exact add_nonneg (by norm_num) (Finset.sum_nonneg fun j hj =>
    pintzDyadicPartialZetaMajorant_nonneg ht)

/-- Exact decomposition of an ordinary partial-zeta sum into the zero-shift
Ford shells. -/
theorem partialZeta_eq_one_add_fordDyadic
    {sigma t : ℝ} {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)) =
      1 + fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t := by
  have hCover : M ≤ 2 ^ Nat.clog 2 M :=
    Nat.le_pow_clog (by omega) M
  have hdecomp := ford_sum_Icc_eq_first_add_dyadic
    sigma (u := 0) (t := t) hM hCover
  have hleft :
      (∑ n ∈ Finset.Icc 1 M,
          ((n : ℝ) + 0) ^ (-sigma) • fordShiftedLogPhase n 0 t) =
        ∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight sigma t) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnPos : 0 < n := (show 0 < 1 by norm_num).trans_le
      (Finset.mem_Icc.mp hn).1
    simpa only [add_zero] using fordShiftedWeightedTerm_zero_eq_cpow
      hnPos
  have hfirst :
      ((1 : ℝ) + 0) ^ (-sigma) • fordShiftedLogPhase 1 0 t = 1 := by
    norm_num [fordShiftedLogPhase]
  rw [hleft, hfirst] at hdecomp
  exact hdecomp

/-- Source-corrected arbitrary-cutoff estimate.  Unlike Pintz's printed
`M₁`, it is valid for every finite cutoff; shells beyond the height are paid
for by explicit inverse-frequency Kusmin--Landau terms. -/
theorem norm_partialZeta_le_correctedMajorant_pos
    {sigma t : ℝ} {M : ℕ}
    (hsigma : 0 ≤ sigma)
    (htOne : 1 ≤ t) (hM : 1 ≤ M) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      pintzCorrectedPartialZetaMajorant sigma M t := by
  rw [partialZeta_eq_one_add_fordDyadic hM]
  calc
    ‖(1 : ℂ) + fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t‖ ≤
        1 + ‖fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t‖ := by
      simpa using norm_add_le (1 : ℂ)
        (fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t)
    _ ≤ 1 + ∑ j ∈ Finset.range (Nat.clog 2 M),
        ‖fordShiftedWeightedBlock sigma (2 ^ j)
          (min M (2 ^ (j + 1))) 0 t‖ := by
      unfold fordDyadicWeightedShellSum
      gcongr
      exact norm_sum_le _ _
    _ ≤ 1 + ∑ j ∈ Finset.range (Nat.clog 2 M),
        pintzDyadicPartialZetaMajorant sigma j t := by
      gcongr with j hj
      exact norm_fordShiftedWeightedBlock_zero_dyadic_le
        hsigma htOne
    _ = pintzCorrectedPartialZetaMajorant sigma M t := rfl

/-- Signed-height form of the corrected arbitrary-cutoff estimate. -/
theorem norm_partialZeta_le_correctedMajorant
    {sigma t : ℝ} {M : ℕ}
    (hsigma : 0 ≤ sigma)
    (htOne : 1 ≤ |t|) (hM : 1 ≤ M) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      pintzCorrectedPartialZetaMajorant sigma M |t| := by
  rw [norm_partialZeta_height_abs]
  exact norm_partialZeta_le_correctedMajorant_pos
    hsigma htOne hM

/-- The standard exponential form of a qualitative Ford shell remains valid
at shift zero. -/
theorem fordGeneralDyadicRawMajorant_zero_le_source
    {C D sigma t : ℝ} {j : ℕ}
    (hC : 0 ≤ C) (hsigma : 0 ≤ sigma) (ht : 1 < t) (hD : 0 < D) :
    fordGeneralDyadicRawMajorant C D sigma j 0 t ≤
      C * Real.exp (fordDyadicExponent D sigma t j) := by
  have hBase : 0 < (((2 ^ j : ℕ) : ℝ)) := by positivity
  have hWeight : ((((2 ^ j + 1 : ℕ) : ℝ) + 0) ^ (-sigma)) ≤
      (((2 ^ j : ℕ) : ℝ) ^ (-sigma)) := by
    apply Real.rpow_le_rpow_of_nonpos hBase
    · norm_num
    · linarith
  have hMajorantNonneg : 0 ≤ fordGeneralMajorant C D (2 ^ j) t := by
    unfold fordGeneralMajorant
    exact mul_nonneg hC (Real.rpow_nonneg hBase.le _)
  calc
    fordGeneralDyadicRawMajorant C D sigma j 0 t ≤
        (((2 ^ j : ℕ) : ℝ) ^ (-sigma)) *
          fordGeneralMajorant C D (2 ^ j) t :=
      mul_le_mul_of_nonneg_right hWeight hMajorantNonneg
    _ = C * ((((2 ^ j : ℕ) : ℝ) ^ (-sigma)) *
        (((2 ^ j : ℕ) : ℝ) ^
          (1 - 1 / (D * fordLambda (2 ^ j) t ^ 2)))) := by
      unfold fordGeneralMajorant
      ring
    _ = C * Real.exp (fordDyadicExponent D sigma t j) := by
      rw [fordTheorem2_dyadic_power_eq_exp ht hD.ne']

/-- Elementary power comparison used to keep the terminal shell cost at the
correct `M^(1-sigma)/t` scale. -/
theorem dyadic_terminal_weight_le_endpoint
    {sigma : ℝ} {j M : ℕ}
    (hsigma : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hjM : 2 ^ j ≤ M) :
    ((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) * ((2 ^ j : ℕ) : ℝ) ≤
      (M : ℝ) ^ (1 - sigma) := by
  have hA : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hM : (0 : ℝ) < (M : ℝ) := hA.trans_le (by exact_mod_cast hjM)
  have hWeight : ((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) ≤
      ((2 ^ j : ℕ) : ℝ) ^ (-sigma) := by
    apply Real.rpow_le_rpow_of_nonpos hA
    · exact_mod_cast (show 2 ^ j ≤ 2 ^ j + 1 by omega)
    · linarith
  have hPowA : ((2 ^ j : ℕ) : ℝ) ^ (-sigma) * ((2 ^ j : ℕ) : ℝ) =
      ((2 ^ j : ℕ) : ℝ) ^ (1 - sigma) := by
    calc
      ((2 ^ j : ℕ) : ℝ) ^ (-sigma) * ((2 ^ j : ℕ) : ℝ) =
          ((2 ^ j : ℕ) : ℝ) ^ (-sigma) *
            ((2 ^ j : ℕ) : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ((2 ^ j : ℕ) : ℝ) ^ (-sigma + 1) :=
        (Real.rpow_add hA (-sigma) 1).symm
      _ = ((2 ^ j : ℕ) : ℝ) ^ (1 - sigma) := by ring_nf
  calc
    ((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) * ((2 ^ j : ℕ) : ℝ) ≤
        ((2 ^ j : ℕ) : ℝ) ^ (-sigma) * ((2 ^ j : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hWeight (Nat.cast_nonneg _)
    _ = ((2 ^ j : ℕ) : ℝ) ^ (1 - sigma) := hPowA
    _ ≤ (M : ℝ) ^ (1 - sigma) := by
      exact Real.rpow_le_rpow hA.le (by exact_mod_cast hjM) (by linarith)

/-- A closed upper envelope for the corrected majorant.  Its two analytic
pieces are respectively Ford's cubic estimate and the genuinely oscillatory
long-cutoff tail. -/
noncomputable def pintzCorrectedPartialZetaEnvelope
    (sigma : ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  1 + fordQualitativeCoefficient *
      (t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
          Real.log t ^ (2 / 3 : ℝ))) +
    (Nat.clog 2 M : ℝ) *
      (6 * Real.pi * (M : ℝ) ^ (1 - sigma) / t)

theorem pintzCorrectedPartialZetaMajorant_le_envelope
    {sigma t : ℝ} {M : ℕ}
    (hsigma : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 1 < t) :
    pintzCorrectedPartialZetaMajorant sigma M t ≤
      pintzCorrectedPartialZetaEnvelope sigma M t := by
  let r := Nat.clog 2 M
  have hFordSum :
      (∑ j ∈ Finset.range r,
        fordGeneralDyadicRawMajorant fordQualitativeCoefficient 3000000
          sigma j 0 t) ≤
        fordQualitativeCoefficient *
          (t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
              Real.log t ^ (2 / 3 : ℝ))) := by
    calc
      _ ≤ ∑ j ∈ Finset.range r,
          fordQualitativeCoefficient *
            Real.exp (fordDyadicExponent 3000000 sigma t j) := by
        gcongr with j hj
        exact fordGeneralDyadicRawMajorant_zero_le_source
          fordQualitativeCoefficient_nonneg hsigma ht (by norm_num)
      _ = fordQualitativeCoefficient *
          ∑ j ∈ Finset.range r,
            Real.exp (fordDyadicExponent 3000000 sigma t j) := by
        rw [Finset.mul_sum]
      _ ≤ fordQualitativeCoefficient *
          (t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
              Real.log t ^ (2 / 3 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (fordCubicExpSum_le_source hsigmaUpper (by norm_num) ht r)
          fordQualitativeCoefficient_nonneg
  have hTerminal (j : ℕ) (hj : j ∈ Finset.range r) :
      ((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) *
          (6 * Real.pi * ((2 ^ j : ℕ) : ℝ) / t) ≤
        6 * Real.pi * (M : ℝ) ^ (1 - sigma) / t := by
    have hjlt : j < Nat.clog 2 M := by simpa [r] using Finset.mem_range.mp hj
    have hjM : 2 ^ j < M := Nat.pow_lt_of_lt_clog hjlt
    have hweight := dyadic_terminal_weight_le_endpoint hsigma hsigmaUpper hjM.le
    have hfactor : 0 ≤ 6 * Real.pi / t := by positivity
    calc
      ((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) *
          (6 * Real.pi * ((2 ^ j : ℕ) : ℝ) / t) =
        (6 * Real.pi / t) *
          (((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) * ((2 ^ j : ℕ) : ℝ)) := by ring
      _ ≤ (6 * Real.pi / t) * (M : ℝ) ^ (1 - sigma) :=
        mul_le_mul_of_nonneg_left hweight hfactor
      _ = 6 * Real.pi * (M : ℝ) ^ (1 - sigma) / t := by ring
  unfold pintzCorrectedPartialZetaMajorant
  change 1 + (∑ j ∈ Finset.range r,
      (fordGeneralDyadicRawMajorant fordQualitativeCoefficient 3000000
          sigma j 0 t +
        ((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) *
          (6 * Real.pi * ((2 ^ j : ℕ) : ℝ) / t))) ≤ _
  rw [Finset.sum_add_distrib]
  calc
    1 + ((∑ j ∈ Finset.range r,
        fordGeneralDyadicRawMajorant fordQualitativeCoefficient 3000000
          sigma j 0 t) +
      ∑ j ∈ Finset.range r,
        ((2 ^ j + 1 : ℕ) : ℝ) ^ (-sigma) *
          (6 * Real.pi * ((2 ^ j : ℕ) : ℝ) / t)) ≤
      1 + (fordQualitativeCoefficient *
          (t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
              Real.log t ^ (2 / 3 : ℝ))) +
        ∑ j ∈ Finset.range r,
          (6 * Real.pi * (M : ℝ) ^ (1 - sigma) / t)) := by
        gcongr with j hj
        exact hTerminal j hj
    _ = pintzCorrectedPartialZetaEnvelope sigma M t := by
      unfold pintzCorrectedPartialZetaEnvelope
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [r]
      ring

/-- Final unconditional, signed-height, arbitrary-cutoff partial-zeta bound. -/
theorem norm_partialZeta_le_correctedEnvelope
    {sigma t : ℝ} {M : ℕ}
    (hsigma : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 1 < |t|) (hM : 1 ≤ M) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      pintzCorrectedPartialZetaEnvelope sigma M |t| :=
  (norm_partialZeta_le_correctedMajorant hsigma ht.le hM).trans
    (pintzCorrectedPartialZetaMajorant_le_envelope
      hsigma hsigmaUpper ht)

#print axioms fordShiftedWeightedTerm_zero_eq_cpow
#print axioms fordShiftedWeightedBlock_eq_finite_sub
#print axioms norm_fordShiftedWeightedBlock_zero_le_of_fordTheorem2
#print axioms norm_fordShiftedWeightedBlock_zero_le_general
#print axioms norm_fordShiftedWeightedBlock_zero_le_terminal
#print axioms norm_fordShiftedWeightedBlock_zero_dyadic_le
#print axioms partialZeta_eq_one_add_fordDyadic
#print axioms norm_partialZeta_le_correctedMajorant
#print axioms fordGeneralDyadicRawMajorant_zero_le_source
#print axioms dyadic_terminal_weight_le_endpoint
#print axioms norm_partialZeta_le_correctedEnvelope

end

end GafniTao
