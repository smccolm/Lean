import GafniTao.FordCoreRootBound

/-!
# Quantitative specialization of Ford's exponential-sum lemma

The results here control the two boundary terms and the complete-window
prefactor in the literal statement of Ford's Lemma 5.1.
-/

namespace GafniTao

noncomputable section

theorem ford_complete_window_card
    (x : ℝ) :
    (Finset.Icc 1 ⌊x⌋₊).card = ⌊x⌋₊ := by
  simp [Nat.card_Icc]

theorem ford_complete_window_ratio_le_two
    {x : ℝ} (hx : 2 ≤ x) :
    x / ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) ≤ 2 := by
  have hhalf := ford_natFloor_ge_half hx
  have hcard := ford_complete_window_card x
  have hfloorPos : (0 : ℝ) < ⌊x⌋₊ := by
    exact_mod_cast Nat.floor_pos.mpr (by linarith)
  rw [hcard]
  rw [div_le_iff₀ hfloorPos]
  linarith

theorem ford_complete_window_prefactor_le_two
    {x : ℝ} {r : ℕ} (hx : 2 ≤ x) (hr : 1 ≤ r) :
    (x / ((Finset.Icc 1 ⌊x⌋₊).card : ℝ)) ^ (1 / (r : ℝ)) ≤ 2 := by
  have hratio0 : 0 ≤ x / ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) := by positivity
  have hratio := ford_complete_window_ratio_le_two hx
  have hq0 : 0 ≤ (1 / (r : ℝ)) := by positivity
  have hqOne : (1 / (r : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < r)]
    exact_mod_cast hr
  calc
    (x / ((Finset.Icc 1 ⌊x⌋₊).card : ℝ)) ^ (1 / (r : ℝ)) ≤
        (2 : ℝ) ^ (1 / (r : ℝ)) := Real.rpow_le_rpow hratio0 hratio hq0
    _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hqOne
    _ = 2 := by norm_num

theorem ford_scale_product_eq {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) =
      (N : ℝ) ^ (3 / 10 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  rw [← Real.rpow_add hNpos]
  congr 1
  norm_num

theorem ford_taylor_boundary_term_le
    {k N : ℕ} {t : ℝ} (hk : 1 ≤ k) (hN : 1 ≤ N)
    (htop : t ≤ (N : ℝ) ^ ((7 / 10 : ℝ) * k)) :
    t * (((N : ℝ) ^ (1 / 5 : ℝ)) *
          ((N : ℝ) ^ (1 / 10 : ℝ))) ^ (k + 1) /
        ((k : ℝ) * (N : ℝ) ^ k) ≤
      (N : ℝ) ^ (3 / 10 : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod := ford_scale_product_eq hN
  rw [hprod]
  have hpowEq :
      (((N : ℝ) ^ (3 / 10 : ℝ)) ^ (k + 1)) =
        (N : ℝ) ^ ((3 / 10 : ℝ) * (k + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  rw [hpowEq]
  have hnum :
      t * (N : ℝ) ^ ((3 / 10 : ℝ) * (k + 1)) ≤
        (N : ℝ) ^ ((7 / 10 : ℝ) * k) *
          (N : ℝ) ^ ((3 / 10 : ℝ) * (k + 1)) := by
    gcongr
  have hcombine :
      (N : ℝ) ^ ((7 / 10 : ℝ) * k) *
          (N : ℝ) ^ ((3 / 10 : ℝ) * (k + 1)) =
        (N : ℝ) ^ ((k : ℝ) + 3 / 10) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hdenPos : 0 < (k : ℝ) * (N : ℝ) ^ k := by positivity
  rw [div_le_iff₀ hdenPos]
  calc
    t * (N : ℝ) ^ ((3 / 10 : ℝ) * (k + 1)) ≤
        (N : ℝ) ^ ((7 / 10 : ℝ) * k) *
          (N : ℝ) ^ ((3 / 10 : ℝ) * (k + 1)) := hnum
    _ = (N : ℝ) ^ ((k : ℝ) + 3 / 10) := hcombine
    _ = (N : ℝ) ^ (3 / 10 : ℝ) * (N : ℝ) ^ k := by
      rw [show (k : ℝ) + 3 / 10 = 3 / 10 + k by ring,
        Real.rpow_add hNpos, Real.rpow_natCast]
    _ ≤ (N : ℝ) ^ (3 / 10 : ℝ) *
          ((k : ℝ) * (N : ℝ) ^ k) := by
      have hpow0 : 0 ≤ (N : ℝ) ^ k := pow_nonneg (by positivity) _
      calc
        (N : ℝ) ^ (3 / 10 : ℝ) * (N : ℝ) ^ k =
            (N : ℝ) ^ (3 / 10 : ℝ) * (1 * (N : ℝ) ^ k) := by ring
        _ ≤ (N : ℝ) ^ (3 / 10 : ℝ) *
            ((k : ℝ) * (N : ℝ) ^ k) := by
          gcongr

/-- Ford's literal Lemma 5.1 after the complete-window moment estimate. -/
theorem ford_exponential_lemma_5_1_quantitative
    {k N R : ℕ} {u t : ℝ}
    (hk : 1000 ≤ k) (hN : 1024 ≤ N)
    (hR : R ≤ 2 * N) (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      3 * (N : ℝ) ^ (3 / 10 : ℝ) +
        2 * (N : ℝ) *
          (fordScaledCoreCoefficient k) ^
            (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
          (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by
  let r : ℕ := fordDoubleSquareDegree k
  let M₁ : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)
  let M₂ : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  let Q : ℕ := ⌊M₂⌋₊
  let B : Finset ℕ := Finset.Icc 1 Q
  have hk1000 : 1000 ≤ k := hk
  have hk1 : 1 ≤ k := by omega
  have hrTwo : 2 ≤ r := by
    dsimp [r, fordDoubleSquareDegree]
    nlinarith [Nat.zero_le (k ^ 2)]
  obtain ⟨hM₁two, hM₂two, _hMhalf, hMone, hQone,
      hM₁top, hM₂top, hprodTop⟩ :=
    ford_basic_scale_data (x := (N : ℝ)) (by exact_mod_cast hN)
  have hQone' : 1 ≤ Q := by simpa [Q, M₂] using hQone
  have hBne : B.Nonempty := by
    simp [B, hQone']
  have hBpos : ∀ b ∈ B, 1 ≤ b := by
    intro b hb
    exact (Finset.mem_Icc.mp hb).1
  have hBtop : ∀ b ∈ B, (b : ℝ) ≤ M₂ := by
    intro b hb
    have hbQ := (Finset.mem_Icc.mp hb).2
    have hbQr : (b : ℝ) ≤ Q := by exact_mod_cast hbQ
    exact hbQr.trans (by simpa [Q] using (Nat.floor_le (by positivity : 0 ≤ M₂)))
  have hsource := ford_exponential_lemma_5_1
    (k := k) (h := 1) (g := k) (r := r) (s := r)
    (N := N) (R := R) (M₁ := M₁) (M₂ := M₂) (B := B)
    (u := u) (t := t) (by omega) hrTwo hrTwo (by omega) (by omega)
    (by omega) (by linarith) hM₁top (by linarith) hM₂top hBne
    hBpos hBtop hR hu huOne ht
  have htTop := (ford_lambda_band_t_bounds (by omega : 1 < N) ht hlower hupper).2
  have htaylor := ford_taylor_boundary_term_le hk1 (by omega : 1 ≤ N) htTop
  have hprefactor : (M₂ / (B.card : ℝ)) ^ (1 / (r : ℝ)) ≤ 2 := by
    simpa [M₂, B, Q] using ford_complete_window_prefactor_le_two hM₂two
      (by omega : 1 ≤ r)
  have hroot := fordLemma51SourceCore_root_le hk hN ht hlower hupper
  have hcentral0 : 0 ≤ (N : ℝ) *
      (M₂ / (B.card : ℝ)) ^ (1 / (r : ℝ)) := by positivity
  have hroot0 : 0 ≤
      (fordLemma51SourceCore k 1 k r r M₁ M₂ N B t) ^
        (1 / (((2 * r * r : ℕ) : ℝ))) := by
    exact Real.rpow_nonneg
      (fordLemma51SourceCore_nonneg (by linarith : 1 ≤ M₁)
        (by linarith : 0 ≤ M₂) (by omega : 0 < r) (by omega : 0 < r)
        (by positivity : (0 : ℝ) < N) ht B) _
  have hprefactorApplied := mul_le_mul_of_nonneg_right hprefactor hroot0
  have hcentralApplied := mul_le_mul_of_nonneg_left hprefactorApplied
    (by positivity : (0 : ℝ) ≤ N)
  have hrEq : 2 * r * r = 8 * k ^ 4 := by
    dsimp [r, fordDoubleSquareDegree]
    ring
  have hroot' :
      (fordLemma51SourceCore k 1 k r r M₁ M₂ N B t) ^
          (1 / (((2 * r * r : ℕ) : ℝ))) ≤
        (fordScaledCoreCoefficient k) ^
            (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
          (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by
    simpa [r, M₁, M₂, B, Q, hrEq] using hroot
  have hcentral :
      (N : ℝ) * (M₂ / (B.card : ℝ)) ^ (1 / (r : ℝ)) *
          (fordLemma51SourceCore k 1 k r r M₁ M₂ N B t) ^
            (1 / (((2 * r * r : ℕ) : ℝ))) ≤
        2 * (N : ℝ) *
          (fordScaledCoreCoefficient k) ^
            (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
          (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by
    calc
      _ ≤ (N : ℝ) * 2 *
          (fordLemma51SourceCore k 1 k r r M₁ M₂ N B t) ^
            (1 / (((2 * r * r : ℕ) : ℝ))) := by
        simpa [mul_assoc] using hcentralApplied
      _ ≤ (N : ℝ) * 2 *
          ((fordScaledCoreCoefficient k) ^
              (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
            (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)))) := by
        gcongr
      _ = _ := by ring
  have hboundary : 2 * M₁ * M₂ = 2 * (N : ℝ) ^ (3 / 10 : ℝ) := by
    have hprod : M₁ * M₂ = (N : ℝ) ^ (3 / 10 : ℝ) := by
      simpa [M₁, M₂] using ford_scale_product_eq (by omega : 1 ≤ N)
    calc
      2 * M₁ * M₂ = 2 * (M₁ * M₂) := by ring
      _ = 2 * (N : ℝ) ^ (3 / 10 : ℝ) := by rw [hprod]
  rw [hboundary] at hsource
  apply hsource.trans
  calc
    2 * (N : ℝ) ^ (3 / 10 : ℝ) +
          t * (M₁ * M₂) ^ (k + 1) / ((k : ℝ) * (N : ℝ) ^ k) +
          (N : ℝ) * (M₂ / (B.card : ℝ)) ^ (1 / (r : ℝ)) *
            (fordLemma51SourceCore k 1 k r r M₁ M₂ N B t) ^
              (1 / (((2 * r * r : ℕ) : ℝ))) ≤
        2 * (N : ℝ) ^ (3 / 10 : ℝ) +
          (N : ℝ) ^ (3 / 10 : ℝ) +
          2 * (N : ℝ) *
            (fordScaledCoreCoefficient k) ^
              (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
            (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by
      have htaylor' :
          t * (M₁ * M₂) ^ (k + 1) / ((k : ℝ) * (N : ℝ) ^ k) ≤
            (N : ℝ) ^ (3 / 10 : ℝ) := by
        simpa [M₁, M₂] using htaylor
      gcongr
    _ = 3 * (N : ℝ) ^ (3 / 10 : ℝ) +
          2 * (N : ℝ) *
            (fordScaledCoreCoefficient k) ^
              (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
            (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by ring

#print axioms ford_complete_window_ratio_le_two
#print axioms ford_taylor_boundary_term_le
#print axioms ford_exponential_lemma_5_1_quantitative

end

end GafniTao
