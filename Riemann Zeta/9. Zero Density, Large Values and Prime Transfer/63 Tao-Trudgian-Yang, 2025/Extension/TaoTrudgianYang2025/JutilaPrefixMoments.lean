import TaoTrudgianYang2025.JutilaPolynomialMoments

/-!
# Powered moments of the complete reflected prefix

The actual reflected polynomial includes its n = 1 term. Its translation
parameter stays inside unit-bounded coefficients, so the resulting
bound has a constant independent of that parameter.
-/

open Complex Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Finite Hölder with an explicitly retained initial term. -/
theorem jutila_norm_one_add_sum_pow_le {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) {p : ℕ} (hp : 0 < p) :
    ‖1 + ∑ i ∈ s, a i‖ ^ p ≤
      ((s.card : ℝ) + 1) ^ (p-1) * (1 + ∑ i ∈ s, ‖a i‖ ^ p) := by
  classical
  let S : Finset (Option ι) := Finset.cons none (s.map Function.Embedding.some) (by simp)
  let f : Option ι → ℝ := fun i => i.elim 1 (fun j => ‖a j‖)
  have hf (i : Option ι) : 0 ≤ f i := by cases i <;> simp [f]
  have h := pow_sum_le_card_mul_sum_pow (s := S) (f := f) (fun i _ => hf i) (p-1)
  have hp' : p-1+1 = p := by omega
  rw [hp'] at h
  simp only [S, f, Finset.sum_cons, Finset.sum_map, Function.Embedding.some_apply,
    Option.elim_none, Option.elim_some, Finset.card_cons, Finset.card_map,
    Nat.cast_add, Nat.cast_one, one_pow] at h
  apply le_trans _ h
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖∑ i ∈ s, a i‖ := norm_add_le _ _
    _ ≤ 1 + ∑ i ∈ s, ‖a i‖ := by simpa using add_le_add_left (norm_sum_le s a) 1

/-- Pointwise 2k-th power of the exact reflected prefix, with its literal
first term and an explicit logarithmic Hölder loss. -/
theorem jutila_reflected_prefix_power_le_blocks (t u : ℝ) {M k : ℕ}
    (hM : 0 < M) (hk : 0 < k) :
    ‖gmReflectionDirichletPoly t M u‖ ^ (2*k) ≤
      ((Nat.clog 2 M : ℝ) + 1) ^ (2*k-1) *
        (1 + ∑ r ∈ Finset.range (Nat.clog 2 M),
          ‖dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) t‖ ^ (2*k)) := by
  rw [gmReflectionDirichletPoly_eq_one_add_wide t u hM,
    wideDirichletPoly_eq_sum_blocks]
  simpa only [Nat.mul_one, Finset.card_range] using
    jutila_norm_one_add_sum_pow_le (Finset.range (Nat.clog 2 M))
      (fun r => dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) t)
      (by omega : 0 < 2*k)

/-- Ordered-pair summation retains R² from the literal n = 1 term. -/
theorem jutila_reflected_prefix_moment_le_blocks (W : Finset ℝ) (u : ℝ)
    {M k : ℕ} (hM : 0 < M) (hk : 0 < k) :
    (∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) M u‖ ^ (2*k)) ≤
      ((Nat.clog 2 M : ℝ) + 1) ^ (2*k-1) *
        ((W.card : ℝ) ^ 2 + ∑ r ∈ Finset.range (Nat.clog 2 M),
          ∑ t ∈ W, ∑ v ∈ W,
            ‖dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖ ^ (2*k)) := by
  have h := Finset.sum_le_sum (s := W) fun t _ =>
    Finset.sum_le_sum (s := W) fun v _ =>
      jutila_reflected_prefix_power_le_blocks (t-v) u hM hk
  apply h.trans_eq
  simp_rw [← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [pow_two]
  congr 1
  calc
    _ = ∑ t ∈ W, ∑ r ∈ Finset.range (Nat.clog 2 M), ∑ v ∈ W,
        ‖dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖ ^ (2*k) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- The complete reflected-prefix 2k-th moment, uniform in the prefix
length and in its real translation. The powered endpoint is U = (2M)^k;
the displayed logarithmic factor is not hidden in the constant. -/
theorem jutila_reflected_prefix_moment_uniform (k : ℕ) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ) (u : ℝ),
        0 < M → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
        (∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) M u‖ ^ (2*k)) ≤
          C * ((Nat.clog 2 M : ℝ) + 1) ^ (2*k) * (2 ^ k * M ^ k : ℕ) *
            (((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
            ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * M ^ k : ℕ) +
              (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)) := by
  obtain ⟨A, T₀, hA, hT₀, hmoment⟩ := jutila_source_power_moment_uniform k hk hε hη
  refine ⟨A+1, T₀, by positivity, hT₀, ?_⟩
  intro M T W u hM hT hsep hbase
  let U : ℕ := 2 ^ k * M ^ k
  let B : ℝ := (W.card : ℝ) ^ 2 + (W.card : ℝ) * U +
    (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)
  let F : ℝ := (U : ℝ) * ((U : ℝ) ^ η) ^ 2 * T ^ ε * B
  let L : ℝ := Nat.clog 2 M
  have hT1 : 1 ≤ T := hT₀.trans hT
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hUpos
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hRF : (W.card : ℝ) ^ 2 ≤ F := by
    have hη1 : 1 ≤ (U : ℝ) ^ η := Real.one_le_rpow hU1 hη.le
    have hε1 : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
    calc
      _ ≤ B := by
        dsimp [B]
        exact (le_add_of_nonneg_right (by positivity)).trans
          (le_add_of_nonneg_right (by positivity))
      _ ≤ F := by
        dsimp [F]
        calc
          B = 1 * 1 ^ 2 * 1 * B := by ring
          _ ≤ _ := by gcongr
  have hblock (r : ℕ) (hr : r ∈ Finset.range (Nat.clog 2 M)) :
      (∑ t ∈ W, ∑ v ∈ W,
        ‖dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖ ^ (2*k)) ≤
        A * F := by
    have hNM : 2 ^ r ≤ M := (Nat.pow_lt_of_lt_clog (Finset.mem_range.mp hr)).le
    have hQU : 2 ^ k * (2 ^ r) ^ k ≤ U := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNM k)
    have hQUr : ((2 ^ k * (2 ^ r) ^ k : ℕ) : ℝ) ≤ U := by exact_mod_cast hQU
    have hm := hmoment (2 ^ r) T W (heathBrownReflectedPrefixCoeff M u)
      (by positivity) hT hsep hbase (fun n _ => norm_heathBrownReflectedPrefixCoeff_le_one M u n)
    have heq :
        (∑ t ∈ W, ∑ v ∈ W,
          ‖dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖ ^ (2*k)) =
        ∑ t ∈ W, ∑ v ∈ W,
          ‖sourceDirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖ ^ (2*k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro v hv
      rw [← dirichletPoly_neg_eq_sourceDirichletPoly, neg_sub]
    rw [heq]
    apply hm.trans
    dsimp [F, B]
    have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    calc
      _ ≤ A * (U : ℝ) * ((U : ℝ) ^ η) ^ 2 * T ^ ε *
          ((W.card : ℝ) ^ 2 + (W.card : ℝ) * U +
            (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ)) := by gcongr
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hblock
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hbound := jutila_reflected_prefix_moment_le_blocks W u hM hk
  have hcore : (W.card : ℝ) ^ 2 +
      (∑ r ∈ Finset.range (Nat.clog 2 M), ∑ t ∈ W, ∑ v ∈ W,
        ‖dirichletPoly (2 ^ r) (heathBrownReflectedPrefixCoeff M u) (t-v)‖ ^ (2*k)) ≤
        (A+1) * (L+1) * F := by
    calc
      _ ≤ F + L * (A * F) := add_le_add hRF hsum
      _ ≤ _ := by nlinarith [mul_nonneg hA.le hF, mul_nonneg hL hF]
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hcore (by positivity))
  have hp : 2*k-1+1 = 2*k := by omega
  have hid : (L+1) ^ (2*k-1) * ((A+1) * (L+1) * F) =
      (A+1) * (L+1) ^ (2*k) * F := by
    calc
      _ = (A+1) * ((L+1) ^ (2*k-1) * (L+1)) * F := by ring
      _ = _ := by rw [← pow_succ, hp]
  change _ ≤ (L+1) ^ (2*k-1) * ((A+1) * (L+1) * F) at hfinal
  rw [hid] at hfinal
  convert hfinal using 1
  dsimp [L, F, B, U]
  ring

end TaoTrudgianYang2025
