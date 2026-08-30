import RiemannZeta.GuthMaynard.HughesYoungInfiniteTransfer
import RiemannZeta.GuthMaynard.HughesYoungFiniteMoment

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Exact finite-square entry to the Hughes--Young arithmetic moment
-/

theorem continuous_uncurry_hughesYoungRightPairTerm_height_ordinate
    {c : ℝ} (hc : 0 < c) {p : ℕ × ℕ} (hp₁ : 0 < p.1) (hp₂ : 0 < p.2) :
    Continuous (Function.uncurry fun t u : ℝ =>
      hughesYoungRightPairTerm t c u p) := by
  let s₁ : ℝ × ℝ → ℂ := fun z =>
    afeCriticalPoint z.1 + ((c : ℂ) + (z.2 : ℂ) * I)
  let s₂ : ℝ × ℝ → ℂ := fun z =>
    afeCriticalPoint (-z.1) + ((c : ℂ) + (z.2 : ℂ) * I)
  have hs₁ : Continuous s₁ := by
    dsimp [s₁, afeCriticalPoint]
    fun_prop
  have hs₂ : Continuous s₂ := by
    dsimp [s₂, afeCriticalPoint]
    fun_prop
  have hd₁ : Continuous (fun z : ℝ × ℝ =>
      divisorDirichletTerm (s₁ z) p.1) := by
    simp only [divisorDirichletTerm,
      LSeries.term_of_ne_zero (Nat.ne_of_gt hp₁)]
    exact continuous_const.div₀
      (continuous_const.cpow hs₁ (fun _ => by
        rw [Complex.mem_slitPlane_iff]
        left
        simpa using (show (0 : ℝ) < p.1 by exact_mod_cast hp₁)))
      (fun _ => Complex.cpow_ne_zero_iff.mpr
        (Or.inl (by exact_mod_cast (Nat.ne_of_gt hp₁))))
  have hd₂ : Continuous (fun z : ℝ × ℝ =>
      divisorDirichletTerm (s₂ z) p.2) := by
    simp only [divisorDirichletTerm,
      LSeries.term_of_ne_zero (Nat.ne_of_gt hp₂)]
    exact continuous_const.div₀
      (continuous_const.cpow hs₂ (fun _ => by
        rw [Complex.mem_slitPlane_iff]
        left
        simpa using (show (0 : ℝ) < p.2 by exact_mod_cast hp₂)))
      (fun _ => Complex.cpow_ne_zero_iff.mpr
        (Or.inl (by exact_mod_cast (Nat.ne_of_gt hp₂))))
  unfold Function.uncurry hughesYoungRightPairTerm
  simpa only [s₁, s₂, mul_assoc] using
    ((continuous_uncurry_hughesYoungRightContourWeight hc).mul hd₁).mul hd₂

theorem continuous_integral_hughesYoungRightPairTerm_height
    {c : ℝ} (hc : 0 < c) (H : ℝ) {p : ℕ × ℕ}
    (hp₁ : 0 < p.1) (hp₂ : 0 < p.2) :
    Continuous (fun t : ℝ =>
      ∫ u in -H..H, hughesYoungRightPairTerm t c u p) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_uncurry_hughesYoungRightPairTerm_height_ordinate hc hp₁ hp₂)
    (-H) H

theorem continuous_hughesYoungFiniteArithmeticTerm_height
    {c : ℝ} (hc : 0 < c) (T H : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) {p : ℕ × ℕ}
    (hp₁ : 0 < p.1) (hp₂ : 0 < p.2) :
    Continuous (fun t : ℝ =>
      hughesYoungFiniteArithmeticTerm T t c H h k p) := by
  have hhpow : Continuous (fun t : ℝ =>
      (h : ℂ) ^ (-afeCriticalPoint t)) :=
    continuous_const_cpow_of_ne_zero (h : ℂ)
      (by exact_mod_cast (Nat.ne_of_gt hh)) (by
        unfold afeCriticalPoint
        fun_prop)
  have hkpow : Continuous (fun t : ℝ =>
      (k : ℂ) ^ (-afeCriticalPoint (-t))) :=
    continuous_const_cpow_of_ne_zero (k : ℂ)
      (by exact_mod_cast (Nat.ne_of_gt hk)) (by
        unfold afeCriticalPoint
        fun_prop)
  unfold hughesYoungFiniteArithmeticTerm
  exact (((continuous_const.mul hhpow).mul continuous_const).mul hkpow).mul
    (continuous_const.mul
      (continuous_integral_hughesYoungRightPairTerm_height
        hc H hp₁ hp₂))

set_option maxHeartbeats 1000000 in
theorem integrable_weight_mul_hughesYoungFiniteArithmeticTerm
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (H : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {p : ℕ × ℕ}
    (hp₁ : 0 < p.1) (hp₂ : 0 < p.2) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFiniteArithmeticTerm T t c H h k p) := by
  have hcontinuous : Continuous (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t c H h k p) :=
    (Complex.ofRealCLM.continuous.comp
      (contDiff_hughesYoungHeightWeight T).continuous).mul
        (continuous_hughesYoungFiniteArithmeticTerm_height
          hc T H hh hk hp₁ hp₂)
  have hcutoffCompact : HasCompactSupport (hughesYoungCutoff : ℝ → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      hughesYoungCutoff.support
  have hweightCompact : HasCompactSupport (hughesYoungHeightWeight T) := by
    simpa only [hughesYoungHeightWeight] using
      hcutoffCompact.comp_smul (inv_ne_zero hT.ne')
  have hweightCompactC : HasCompactSupport
      (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ)) :=
    hweightCompact.mono (by
      intro t ht
      simpa only [Function.mem_support, ne_eq, ofReal_eq_zero] using ht)
  exact hcontinuous.integrable_of_hasCompactSupport hweightCompactC.mul_right

/-- The `hughesYoungFiniteSmallTwistedSquare` definition used by the source-facing construction in `HughesYoungFiniteSquareBridge`. -/
noncomputable def hughesYoungFiniteSmallTwistedSquare
    (T t H : ℝ) (M : ℕ) : ℂ :=
  shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
    shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
    ((1 / (Real.pi : ℂ)) *
      hughesYoungIntegratedSmallPairSquare T t H M)

theorem hughesYoungFiniteSmallTwistedSquare_eq_four_index_sum
    (T t H : ℝ) (M : ℕ) :
    hughesYoungFiniteSmallTwistedSquare T t H M =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
            hughesYoungFiniteArithmeticTerm T t
              (hughesYoungSmallContour T) H h k (m, n) := by
  classical
  rw [hughesYoungFiniteSmallTwistedSquare,
    shortMobiusPolynomial_sq_eq, shortMobiusPolynomial_sq_eq]
  unfold hughesYoungIntegratedSmallPairSquare
  rw [mul_assoc, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.Icc_prod_def, Finset.sum_product]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  unfold hughesYoungFiniteArithmeticTerm
  ring

theorem integral_hughesYoungFiniteSmallTwistedSquare_eq_finiteRect
    {T : ℝ} (hTexp : Real.exp 1 ≤ T) (H : ℝ) (M : ℕ) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteSmallTwistedSquare T t H M) =
      hughesYoungFiniteRectIntegratedMoment T
        (hughesYoungSmallContour T) H M M := by
  classical
  have hT : 0 < T := (Real.exp_pos 1).trans_le hTexp
  let K : Finset ℕ := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let S : Finset ℕ := Finset.Icc 1 M
  have hc : 0 < hughesYoungSmallContour T := by
    exact (hughesYoungSmallContour_spec hTexp).1
  have hterm : ∀ h ∈ K, ∀ k ∈ K, ∀ m ∈ S, ∀ n ∈ S,
      Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t (hughesYoungSmallContour T) H
          h k (m, n)) := by
    intro h hh k hk m hm n hn
    exact integrable_weight_mul_hughesYoungFiniteArithmeticTerm
      hT hc H
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)
  have hnInt : ∀ h ∈ K, ∀ k ∈ K, ∀ m ∈ S,
      Integrable (fun t : ℝ => ∑ n ∈ S,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteArithmeticTerm T t
            (hughesYoungSmallContour T) H h k (m, n)) := by
    intro h hh k hk m hm
    exact integrable_finsetSum S (fun n hn => hterm h hh k hk m hm n hn)
  have hmInt : ∀ h ∈ K, ∀ k ∈ K,
      Integrable (fun t : ℝ => ∑ m ∈ S, ∑ n ∈ S,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteArithmeticTerm T t
            (hughesYoungSmallContour T) H h k (m, n)) := by
    intro h hh k hk
    exact integrable_finsetSum S (fun m hm => hnInt h hh k hk m hm)
  have hkInt : ∀ h ∈ K,
      Integrable (fun t : ℝ => ∑ k ∈ K, ∑ m ∈ S, ∑ n ∈ S,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteArithmeticTerm T t
            (hughesYoungSmallContour T) H h k (m, n)) := by
    intro h hh
    exact integrable_finsetSum K (fun k hk => hmInt h hh k hk)
  rw [integral_congr_ae (Eventually.of_forall fun t => by
    rw [hughesYoungFiniteSmallTwistedSquare_eq_four_index_sum])]
  simp_rw [Finset.mul_sum]
  unfold hughesYoungFiniteRectIntegratedMoment
  change (∫ t : ℝ, ∑ h ∈ K, ∑ k ∈ K, ∑ m ∈ S, ∑ n ∈ S,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t
          (hughesYoungSmallContour T) H h k (m, n)) = _
  rw [MeasureTheory.integral_finsetSum K hkInt]
  apply Finset.sum_congr rfl
  intro h hh
  rw [MeasureTheory.integral_finsetSum K (fun k hk => hmInt h hh k hk)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [MeasureTheory.integral_finsetSum S (fun m hm => hnInt h hh k hk m hm)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MeasureTheory.integral_finsetSum S (fun n hn => hterm h hh k hk m hm n hn)]

theorem tendsto_hughesYoungFiniteSmallTwistedSquare
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hTexp : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {M : ℕ} (hM : 0 < M) :
    Tendsto (fun H : ℝ => hughesYoungFiniteSmallTwistedSquare T t H M)
      atTop (𝓝 (
        (twistedZetaMomentIntegrand T t : ℂ) -
          (1 / (Real.pi : ℂ)) *
            shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
            shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
            hughesYoungWholeHighPairSquareTail q t M)) := by
  have hsmall := tendsto_hughesYoungIntegratedSmallPairSquare
    hq η hη0 hη hTexp ht hM
  have hmul := hsmall.const_mul
    ((1 / (Real.pi : ℂ)) *
      shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
      shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2)
  convert hmul using 1
  · funext H
    unfold hughesYoungFiniteSmallTwistedSquare
    ring
  · rw [ofReal_twistedZetaMomentIntegrand_eq_conjugate_product]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]

end RiemannZeta.GuthMaynard
