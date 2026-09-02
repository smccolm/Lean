import GafniTao.FordModerateCoreRoot
import GafniTao.FordLemma51Quantitative

/-!
# Ford's Lemma 5.1 in the moderate-degree range

This applies the literal exponential-sum lemma to the Lemma 6.5 moment input
and absorbs the two source boundary terms without changing the phase or the
summation interval.
-/

namespace GafniTao

noncomputable section

theorem ford_exponential_lemma_5_1_moderate
    {k N R : ℕ} {u t C : ℝ}
    (hk : 40 ≤ k) (hN : 1024 ≤ N)
    (hR : R ≤ 2 * N) (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hC : 0 ≤ C)
    (hmoment : FordVinogradovMomentBound
      (fordModerateMomentDegree k) k C (fordModerateMomentDelta k))
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      3 * (N : ℝ) ^ (3 / 10 : ℝ) +
        2 * (N : ℝ) *
          (fordModerateCoreCoefficient k C) ^
            (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) *
          (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by
  let r := fordModerateMomentDegree k
  let M₁ : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)
  let M₂ : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  let Q : ℕ := ⌊M₂⌋₊
  let B : Finset ℕ := Finset.Icc 1 Q
  have hrTwo : 2 ≤ r := by
    dsimp [r, fordModerateMomentDegree]
    nlinarith
  obtain ⟨_hM₁two, hM₂two, _hMhalf, hMone, hQone,
      hM₁top, hM₂top, hprodTop⟩ :=
    ford_basic_scale_data (x := (N : ℝ)) (by exact_mod_cast hN)
  have hQone' : 1 ≤ Q := by dsimp [Q, M₂]; exact hQone
  have hBne : B.Nonempty := by simp [B, hQone']
  have hBpos : ∀ b ∈ B, 1 ≤ b := by
    intro b hb
    exact (Finset.mem_Icc.mp hb).1
  have hBtop : ∀ b ∈ B, (b : ℝ) ≤ M₂ := by
    intro b hb
    have hbQ := (Finset.mem_Icc.mp hb).2
    have hbQr : (b : ℝ) ≤ Q := by exact_mod_cast hbQ
    exact hbQr.trans (by
      dsimp [Q]
      exact Nat.floor_le (by positivity))
  have hsource := ford_exponential_lemma_5_1
    (k := k) (h := 1) (g := k) (r := r) (s := r)
    (N := N) (R := R) (M₁ := M₁) (M₂ := M₂) (B := B)
    (u := u) (t := t) (by omega) hrTwo hrTwo (by omega) (by omega)
    (by omega) (by linarith) hM₁top (by linarith) hM₂top hBne
    hBpos hBtop hR hu huOne ht
  have htTop := (ford_lambda_band_t_bounds (by omega : 1 < N) ht hlower hupper).2
  have htaylor := ford_taylor_boundary_term_le (by omega : 1 ≤ k)
    (by omega : 1 ≤ N) htTop
  have hprefactor : (M₂ / (B.card : ℝ)) ^ (1 / (r : ℝ)) ≤ 2 := by
    simpa [M₂, B, Q] using ford_complete_window_prefactor_le_two hM₂two
      (by omega : 1 ≤ r)
  have hroot := fordLemma51SourceCore_moderate_root_le hk hN ht hC hmoment
    hlower hupper
  have hcore0 : 0 ≤ fordLemma51SourceCore k 1 k r r M₁ M₂ N B t := by
    apply fordLemma51SourceCore_nonneg
    · simpa [M₁] using Real.one_le_rpow
        (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num : (0 : ℝ) ≤ 1 / 5)
    · positivity
    · omega
    · omega
    · positivity
    · exact ht
  have hroot0 : 0 ≤ (fordLemma51SourceCore k 1 k r r M₁ M₂ N B t) ^
      (1 / ((2 * r ^ 2 : ℕ) : ℝ)) := Real.rpow_nonneg hcore0 _
  have hprefactorApplied := mul_le_mul_of_nonneg_right hprefactor hroot0
  have hcentralApplied := mul_le_mul_of_nonneg_left hprefactorApplied
    (by positivity : (0 : ℝ) ≤ N)
  have hcentral :
      (N : ℝ) * (M₂ / (B.card : ℝ)) ^ (1 / (r : ℝ)) *
          (fordLemma51SourceCore k 1 k r r M₁ M₂ N B t) ^
            (1 / ((2 * r ^ 2 : ℕ) : ℝ)) ≤
        2 * (N : ℝ) *
          (fordModerateCoreCoefficient k C) ^
            (1 / ((2 * r ^ 2 : ℕ) : ℝ)) *
          (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by
    calc
      _ ≤ (N : ℝ) * 2 *
          (fordLemma51SourceCore k 1 k r r M₁ M₂ N B t) ^
            (1 / ((2 * r ^ 2 : ℕ) : ℝ)) := by
        simpa [mul_assoc] using hcentralApplied
      _ ≤ (N : ℝ) * 2 *
          ((fordModerateCoreCoefficient k C) ^
              (1 / ((2 * r ^ 2 : ℕ) : ℝ)) *
            (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2)))) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [r, M₁, M₂, B, Q] using hroot)
          (by positivity)
      _ = _ := by ring
  have hboundary : 2 * M₁ * M₂ = 2 * (N : ℝ) ^ (3 / 10 : ℝ) := by
    calc
      2 * M₁ * M₂ = 2 * (M₁ * M₂) := by ring
      _ = 2 * (N : ℝ) ^ (3 / 10 : ℝ) := by
        rw [show M₁ * M₂ = (N : ℝ) ^ (3 / 10 : ℝ) by
          simpa [M₁, M₂] using ford_scale_product_eq (by omega : 1 ≤ N)]
  rw [hboundary] at hsource
  apply hsource.trans
  have htaylor' :
      t * (M₁ * M₂) ^ (k + 1) / ((k : ℝ) * (N : ℝ) ^ k) ≤
        (N : ℝ) ^ (3 / 10 : ℝ) := by
    simpa [M₁, M₂] using htaylor
  calc
    _ ≤ 2 * (N : ℝ) ^ (3 / 10 : ℝ) +
        (N : ℝ) ^ (3 / 10 : ℝ) +
        2 * (N : ℝ) *
          (fordModerateCoreCoefficient k C) ^
            (1 / ((2 * r ^ 2 : ℕ) : ℝ)) *
          (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by
      exact add_le_add (add_le_add le_rfl htaylor')
        (by simpa [pow_two, mul_assoc] using hcentral)
    _ = _ := by dsimp [r]; ring

theorem ford_shifted_exponential_sum_moderate_degree
    {k N R : ℕ} {u t : ℝ}
    (hk : 40 ≤ k) (hN : 1024 ≤ N)
    (hR : R ≤ 2 * N) (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    ∃ D : ℝ, 0 ≤ D ∧
      ‖fordShiftedExponentialSum N R u t‖ ≤
        D * (N : ℝ) ^
          (1 - 1 / ((665600 : ℝ) * (k : ℝ) ^ 2)) := by
  obtain ⟨C, hmoment⟩ := ford_moderate_moment_bound (by omega : 4 ≤ k)
  have hC : 0 ≤ C := zero_le_one.trans hmoment.one_le_coefficient
  let q : ℝ := 1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)
  let A : ℝ := (fordModerateCoreCoefficient k C) ^ q
  let D : ℝ := 3 + 2 * A
  refine ⟨D, by
    dsimp [D, A]
    exact add_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (fordModerateCoreCoefficient_nonneg k C) _)), ?_⟩
  have hsource := ford_exponential_lemma_5_1_moderate hk hN hR hu huOne ht
    hC hmoment hlower hupper
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hkPos : (0 : ℝ) < k := by positivity
  have hexponentLow : (3 / 10 : ℝ) ≤
      1 - 1 / ((665600 : ℝ) * (k : ℝ) ^ 2) := by
    have hkR : (40 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : (2 : ℝ) ≤ 665600 * (k : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((k : ℝ) - 40)]
    have hinv : 1 / (665600 * (k : ℝ) ^ 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hden
    linarith
  have hboundary := Real.rpow_le_rpow_of_exponent_le hNreal hexponentLow
  have hcombine :
      (N : ℝ) * (N : ℝ) ^
          (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) =
        (N : ℝ) ^ (1 - 1 / ((665600 : ℝ) * (k : ℝ) ^ 2)) := by
    calc
      (N : ℝ) * (N : ℝ) ^
          (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) =
        (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^
          (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) +
          -(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by
            rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      _ = _ := by congr 1
  apply hsource.trans
  dsimp [D, A, q]
  let P : ℝ := (N : ℝ) ^
    (1 - 1 / ((665600 : ℝ) * (k : ℝ) ^ 2))
  let A' : ℝ := (fordModerateCoreCoefficient k C) ^
    (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ))
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hA0 : 0 ≤ A' := by
    dsimp [A']
    exact Real.rpow_nonneg (fordModerateCoreCoefficient_nonneg k C) _
  have hcentralEq :
      2 * (N : ℝ) * A' *
          (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) =
        2 * A' * P := by
    dsimp [P]
    rw [← hcombine]
    ring
  rw [show (fordModerateCoreCoefficient k C) ^
      (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) = A' by rfl,
    hcentralEq]
  change 3 * (N : ℝ) ^ (3 / 10 : ℝ) + 2 * A' * P ≤
    (3 + 2 * A') * P
  nlinarith

#print axioms ford_exponential_lemma_5_1_moderate
#print axioms ford_shifted_exponential_sum_moderate_degree

end

end GafniTao
