import TaoTrudgianYang2025.BourgainSmoothedMoments
import TaoTrudgianYang2025.MixedDoubleZeta

/-!
# Positive-kernel entry from actual dyadic critical coefficients

A zero-extended finite block is dominated on the full ordered-pair set by
the genuine smoothed critical polynomial. The positive-kernel theorem is
not applied to an arbitrary restricted pair kernel.
-/

open Complex Finset MeasureTheory Set
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The real nonnegative coefficient underlying the smoothed polynomial. -/
def bourgainSmoothCriticalCoeff (L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)^(-1/2 : ℝ) * zetaIntervalCutoff 1 2 ((n : ℝ)/L)

theorem bourgainSmoothCriticalCoeff_nonneg (L : ℝ) (n : ℕ) :
    0 ≤ bourgainSmoothCriticalCoeff L n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (zetaIntervalCutoff_nonneg _ _ _)

theorem bourgainSmoothCriticalCoeff_coe (L : ℝ) (n : ℕ) :
    (bourgainSmoothCriticalCoeff L n : ℂ) =
      bourgainCriticalWeight bourgainDyadicProfile L n := by
  simp only [bourgainSmoothCriticalCoeff, ofReal_mul, bourgainCriticalWeight,
    bourgainRealPowerWeight, bourgainDyadicProfile]

/-- Positive-index finite support, needed by the native phase-product bridge. -/
theorem bourgainSmoothedCriticalPolynomial_eq_sum_positive {L : ℝ}
    (hL : 0 < L) (t : ℝ) :
    bourgainSmoothedCriticalPolynomial L t =
      ∑ n ∈ Finset.Icc 1 (Nat.ceil (5*L/2)),
        (bourgainSmoothCriticalCoeff L n : ℂ) * dirichletPhase n t := by
  unfold bourgainSmoothedCriticalPolynomial
  simp_rw [bourgainSmoothCriticalCoeff_coe]
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    rw [bourgainDyadicProfile_weight_eq_zero hL (Or.inl (by simpa only [Nat.cast_zero] using (half_pos hL).le)), zero_mul]
  · have hnlarge : Nat.ceil (5*L/2) < n := by
      have hnot : ¬ (1 ≤ n ∧ n ≤ Nat.ceil (5*L/2)) := by
        simpa only [Finset.mem_Icc] using hn
      omega
    have hcut : 5*L/2 ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnlarge.le)
    rw [bourgainDyadicProfile_weight_eq_zero hL (Or.inr hcut), zero_mul]

/-- A finite block on the literal physical interval [L,2L] enters the
smooth self-moment with exactly the squared coefficient bound. -/
theorem bourgain_critical_block_moment_le_smoothed
    (I : Finset ℕ) (W : Finset ℝ) (a : ℕ → ℂ) {L B : ℝ}
    (hL : 0 < L) (hB : 0 ≤ B)
    (hI : ∀ n ∈ I, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*L)
    (ha : ∀ n ∈ I, ‖a n‖ ≤ B*(n : ℝ)^(-1/2 : ℝ)) :
    (∑ t ∈ W, ∑ v ∈ W, ‖∑ n ∈ I, a n * dirichletPhase n (t-v)‖^2) ≤
      B^2 * ∑ t ∈ W, ∑ v ∈ W, ‖bourgainSmoothedCriticalPolynomial L (t-v)‖^2 := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (Nat.ceil (5*L/2))
  let a₀ : ℕ → ℂ := fun n => if n ∈ I then a n else 0
  let b : ℕ → ℝ := fun n => B*bourgainSmoothCriticalCoeff L n
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hIS : I ⊆ S := by
    intro n hn
    have hl : (0 : ℝ) < n := hL.trans_le (hI n hn).1
    have hln : 1 ≤ n := by exact_mod_cast hl
    have hu : (n : ℝ) ≤ Nat.ceil (5*L/2) := by
      apply le_trans _ (Nat.le_ceil _)
      linarith [(hI n hn).2]
    exact Finset.mem_Icc.mpr ⟨hln, by exact_mod_cast hu⟩
  have hb : ∀ n ∈ S, 0 ≤ b n :=
    fun n _ => mul_nonneg hB (bourgainSmoothCriticalCoeff_nonneg L n)
  have hab : ∀ n ∈ S, ‖a₀ n‖ ≤ b n := by
    intro n hn
    dsimp [a₀,b]
    split_ifs with hni
    · have heq : bourgainSmoothCriticalCoeff L n = (n : ℝ)^(-1/2 : ℝ) := by
        apply Complex.ofReal_injective
        rw [bourgainSmoothCriticalCoeff_coe]
        exact bourgainDyadicProfile_weight_eq hL (hI n hni).1 (hI n hni).2
      rw [heq]
      exact ha n hni
    · rw [norm_zero]
      exact hb n hn
  have hleft (t v : ℝ) : heathBrownDifferencePolynomial S a₀ t v =
      ∑ n ∈ I, a n * dirichletPhase n (t-v) := by
    rw [heathBrownDifferencePolynomial_eq_dirichletPhase S a₀ hpos t v]
    calc
      _ = ∑ n ∈ S with n ∈ I, a n * dirichletPhase n (t-v) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [a₀]
        split_ifs <;> simp only [zero_mul]
      _ = _ := by
        congr 1
        ext n
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun hn => ⟨hIS hn,hn⟩⟩
  have hright (t v : ℝ) :
      heathBrownDifferencePolynomial S (fun n => (b n : ℂ)) t v =
        (B : ℂ)*bourgainSmoothedCriticalPolynomial L (t-v) := by
    rw [heathBrownDifferencePolynomial_eq_dirichletPhase S _ hpos t v,
      bourgainSmoothedCriticalPolynomial_eq_sum_positive hL (t-v), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [b, ofReal_mul, mul_assoc]
  have h := heathBrownDifferenceMoment_le_of_norm_le S W a₀ b hb hab
  simp only [heathBrownDifferenceMoment,hleft,hright,norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB, mul_pow,
    ← Finset.mul_sum] at h
  exact h

/-- Source-facing finite critical-block estimate with the actual retained
zeta moment. Its hypotheses are pointwise coefficient and support data,
not an assumed Mellin or moment estimate. -/
theorem bourgain_critical_block_retained_zeta_moment {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L →
      ∀ (I : Finset ℕ) (W : Finset ℝ) (a : ℕ → ℂ) (B T H : ℝ),
      0 ≤ B → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
      (∀ n ∈ I, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*L) →
      (∀ n ∈ I, ‖a n‖ ≤ B*(n : ℝ)^(-1/2 : ℝ)) →
      (∑ t ∈ W, ∑ v ∈ W, ‖∑ n ∈ I, a n * dirichletPhase n (t-v)‖^2) ≤
        C*B^2*(L*(W.card : ℝ) + H*bourgainZetaDifferenceMoment W (H+1) +
          (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)) := by
  obtain ⟨C,hC,hbound⟩ := bourgainSmoothedCriticalPolynomial_separated_moment hq
  refine ⟨C,hC,?_⟩
  intro L hL I W a B T H hB hT hH hsep hbase hI ha
  calc
    _ ≤ _ := bourgain_critical_block_moment_le_smoothed I W a hL hB hI ha
    _ ≤ B^2*(C*(L*(W.card : ℝ) + H*bourgainZetaDifferenceMoment W (H+1) +
        (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q))) :=
      mul_le_mul_of_nonneg_left (hbound L hL W T H hT hH hsep hbase) (sq_nonneg B)
    _ = _ := by ring

end TaoTrudgianYang2025
