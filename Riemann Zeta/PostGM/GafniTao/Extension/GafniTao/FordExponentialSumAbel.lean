import GafniTao.FordExponentialSum
import GafniTao.FordLaplaceInversion
import Mathlib.NumberTheory.AbelSummation

/-!
# Abel transfer for Ford's shifted exponential sum

Ford's Lemma 7.3 applies Theorem 2 to a genuinely weighted block.  This
file keeps the source endpoint convention `N < n ≤ R` and proves the
partial-summation step with no factor-two loss.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordShiftedWeightedBlock
    (sigma : ℝ) (N R : ℕ) (u t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N R,
    ((n : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase n u t

/-- A weighted phase is the literal shifted Dirichlet monomial occurring in
Ford's Hurwitz-zeta calculation. -/
theorem fordShiftedWeightedTerm_eq_cpow
    {sigma u t : ℝ} {n : ℕ} (hu : 0 < u) :
    (((n : ℝ) + u) ^ (-sigma)) • fordShiftedLogPhase n u t =
      (((n : ℝ) + u : ℝ) : ℂ) ^
        (-((sigma : ℂ) + (t : ℂ) * I)) := by
  have hx : 0 < (n : ℝ) + u := by positivity
  rw [← ford_exp_neg_mul_log_eq_cpow_neg hx
      ((sigma : ℂ) + (t : ℂ) * I)]
  unfold fordShiftedLogPhase
  rw [Complex.real_smul, Complex.ofReal_cpow hx.le]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.ofReal_log hx.le, ← Complex.exp_add]
  congr 1
  have hlog :
      Complex.log ((n : ℂ) + (u : ℂ)) =
        (Real.log ((n : ℝ) + u) : ℂ) := by
    have hbase :
        (n : ℂ) + (u : ℂ) = (((n : ℝ) + u : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hbase]
    exact (Complex.ofReal_log hx.le).symm
  push_cast
  rw [hlog]
  ring

theorem fordShiftedWeightedBlock_eq_cpow
    (sigma : ℝ) (N R : ℕ) {u t : ℝ} (hu : 0 < u) :
    fordShiftedWeightedBlock sigma N R u t =
      ∑ n ∈ Finset.Ioc N R,
        (((n : ℝ) + u : ℝ) : ℂ) ^
          (-((sigma : ℂ) + (t : ℂ) * I)) := by
  unfold fordShiftedWeightedBlock
  apply Finset.sum_congr rfl
  intro n _hn
  exact fordShiftedWeightedTerm_eq_cpow hu

/-- Reindex a Ford prefix without changing either endpoint. -/
theorem fordShiftedExponentialSum_eq_sum_range
    (N j : ℕ) (u t : ℝ) :
    fordShiftedExponentialSum N (N + j) u t =
      ∑ i ∈ Finset.range j, fordShiftedLogPhase (N + 1 + i) u t := by
  unfold fordShiftedExponentialSum
  have hIoc : Finset.Ioc N (N + j) =
      Finset.Ico (N + 1) (N + j + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : N + j + 1 - (N + 1) = j := by omega
  rw [hLength]

/-- Abel summation on the literal source interval. -/
theorem ford_norm_weighted_Ioc_le_of_antitone
    (f : ℕ → ℝ) (g : ℕ → ℂ) (N R : ℕ) (B : ℝ)
    (hNR : N < R)
    (hf : ∀ n ∈ Finset.Ioc N R, 0 ≤ f n)
    (hanti : ∀ n, N < n → n < R → f (n + 1) ≤ f n)
    (hpartial : ∀ j, j ≤ R - N →
      ‖∑ i ∈ Finset.range j, g (N + 1 + i)‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N R, f n • g n‖ ≤ f (N + 1) * B := by
  have hLen : 0 < R - N := Nat.sub_pos_of_lt hNR
  let F : ℕ → ℝ := fun i => f (N + 1 + i)
  let G : ℕ → ℂ := fun i => g (N + 1 + i)
  have hF : ∀ i, i < R - N → 0 ≤ F i := by
    intro i hi
    exact hf _ (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
  have hAntiF : ∀ i, i + 1 < R - N → F (i + 1) ≤ F i := by
    intro i hi
    simpa only [F, Nat.add_assoc] using
      hanti (N + 1 + i) (by omega) (by omega)
  have hBound := RiemannZeta.GuthMaynard.norm_weighted_sum_le_of_antitone
    F G (R - N) B hLen hF hAntiF (by
      intro j hj
      simpa only [G] using hpartial j hj)
  have hIoc : Finset.Ioc N R = Finset.Ico (N + 1) (R + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : R + 1 - (N + 1) = R - N := by omega
  rw [hLength]
  simpa only [F, G] using hBound

/-- The exact no-loss partial-summation step in Ford Lemma 7.3. -/
theorem norm_fordShiftedWeightedBlock_le
    {sigma B u t : ℝ} {N R : ℕ}
    (hsigma : 0 ≤ sigma) (hu : 0 < u) (hNR : N < R)
    (hpartial : ∀ Q, N < Q → Q ≤ R →
      ‖fordShiftedExponentialSum N Q u t‖ ≤ B) :
    ‖fordShiftedWeightedBlock sigma N R u t‖ ≤
      (((N + 1 : ℕ) : ℝ) + u) ^ (-sigma) * B := by
  unfold fordShiftedWeightedBlock
  apply ford_norm_weighted_Ioc_le_of_antitone
      (fun n => ((n : ℝ) + u) ^ (-sigma))
      (fun n => fordShiftedLogPhase n u t) N R B hNR
  · intro n hn
    exact Real.rpow_nonneg (by positivity) _
  · intro n hnN hnR
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · norm_num
    · linarith
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp
      have hB : 0 ≤ B := by
        have h := hpartial R hNR le_rfl
        exact (norm_nonneg _).trans h
      exact hB
    · rw [← fordShiftedExponentialSum_eq_sum_range]
      exact hpartial (N + j) (by omega) (by omega)

def fordTheorem2Majorant (N : ℕ) (t : ℝ) : ℝ :=
  9.463 * (N : ℝ) ^
    (1 - 1 / (133.66 * fordLambda N t ^ 2))

/-- Ford Theorem 2 supplies every prefix needed by the exact Abel transfer. -/
theorem norm_fordShiftedWeightedBlock_le_of_fordTheorem2
    (hFord : FordTheorem2)
    {sigma u t : ℝ} {N R : ℕ}
    (hsigma : 0 ≤ sigma) (hN : 0 < N) (hNt : (N : ℝ) ≤ t)
    (hu : 0 < u) (huOne : u ≤ 1) (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R u t‖ ≤
      (((N + 1 : ℕ) : ℝ) + u) ^ (-sigma) *
        fordTheorem2Majorant N t := by
  apply norm_fordShiftedWeightedBlock_le hsigma hu hNR
  intro Q hNQ hQR
  exact hFord hN hNt hu huOne hNQ (hQR.trans hR)

#print axioms fordShiftedExponentialSum_eq_sum_range
#print axioms fordShiftedWeightedTerm_eq_cpow
#print axioms norm_fordShiftedWeightedBlock_le
#print axioms norm_fordShiftedWeightedBlock_le_of_fordTheorem2

end

end GafniTao
