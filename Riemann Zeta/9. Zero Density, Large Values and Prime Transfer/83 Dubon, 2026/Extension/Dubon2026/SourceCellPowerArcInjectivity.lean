import Dubon2026.SourceCellPowerArcs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Separation.Regular

/-! DUB-17/18 -> original Abel-Jacobi -> actual branch and pole cells.
The source power pullback retains the exact radial preimage, multiplicity,
arc laps and separated inverse branches needed for geometric pairing.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing radial periodicity and periodic argument evaluation are reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.PowPullback
noncomputable section
open scoped Real

theorem injOn_loop_of_radialRegion (S : RadialRegion) :
    Set.InjOn S.loop (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  have hab2 : S.q + (S.r a : ℂ) * Complex.exp ((a : ℂ) * Complex.I)
      = S.q + (S.r b : ℂ) * Complex.exp ((b : ℂ) * Complex.I) := hab
  have hab' : (S.r a : ℂ) * Complex.exp ((a : ℂ) * Complex.I)
      = (S.r b : ℂ) * Complex.exp ((b : ℂ) * Complex.I) := add_left_cancel hab2
  have hr : S.r a = S.r b := by
    have h1 : ‖(S.r a : ℂ) * Complex.exp ((a : ℂ) * Complex.I)‖
        = ‖(S.r b : ℂ) * Complex.exp ((b : ℂ) * Complex.I)‖ := by rw [hab']
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_of_nonneg (S.hpos a).le, Complex.norm_of_nonneg (S.hpos b).le] at h1
    exact h1
  have hr0 : (S.r b : ℂ) ≠ 0 := by exact_mod_cast (S.hpos b).ne'
  have hexp : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) := by
    rw [hr] at hab'
    exact mul_right_injective₀ hr0 hab'
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  have hn' : (a : ℂ) = b + n * (2 * Real.pi) := by
    have := mul_left_injective₀ Complex.I_ne_zero
      (by rw [hn]; ring : (a : ℂ) * Complex.I = (b + n * (2 * Real.pi)) * Complex.I)
    exact this
  have hreal : a = b + n * (2 * Real.pi) := by exact_mod_cast hn'
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith [ha.2, hb.1]
    have h2 : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by linarith [ha.1, hb.2]
    have h3 : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have h4 : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
    have h3' : n < 1 := by exact_mod_cast h3
    have h4' : -1 < n := by exact_mod_cast h4
    omega
  rw [hreal, hn0]
  simp

theorem injOn_loop (R : RadialRegion) (e : ℕ) (he : e ≠ 0) :
    Set.InjOn (efold R e he).loop (Set.Ico 0 (2 * Real.pi)) :=
  injOn_loop_of_radialRegion (efold R e he)

theorem arcLength_lt (R : RadialRegion) (hN : 2 ≤ R.N) (k : Fin R.N) :
    R.φs k.succ - R.φs k.castSucc < 2 * Real.pi := by
  have h0 : 0 ≤ R.φs k.castSucc := by
    rw [← R.hφ0]
    exact R.hmono.monotone (Fin.zero_le _)
  have h2π : R.φs k.succ ≤ 2 * Real.pi := by
    rw [← R.hφN]
    exact R.hmono.monotone (Fin.le_last _)
  rcases Nat.lt_or_ge (k.val + 1) R.N with hlt | hge
  ·
    have hlt' : R.φs k.succ < 2 * Real.pi := by
      rw [← R.hφN]
      apply R.hmono
      rw [Fin.lt_def]
      exact hlt
    linarith
  ·
    have hpos : 0 < R.φs k.castSucc := by
      rw [← R.hφ0]
      apply R.hmono
      rw [Fin.lt_def]
      show 0 < k.val
      omega
    linarith

theorem loop_eq_exists_int (S : RadialRegion) {a b : ℝ} (hab : S.loop a = S.loop b) :
    ∃ n : ℤ, a = b + n * (2 * Real.pi) := by
  have hab2 : S.q + (S.r a : ℂ) * Complex.exp ((a : ℂ) * Complex.I)
      = S.q + (S.r b : ℂ) * Complex.exp ((b : ℂ) * Complex.I) := hab
  have hab' : (S.r a : ℂ) * Complex.exp ((a : ℂ) * Complex.I)
      = (S.r b : ℂ) * Complex.exp ((b : ℂ) * Complex.I) := add_left_cancel hab2
  have hr : S.r a = S.r b := by
    have h1 : ‖(S.r a : ℂ) * Complex.exp ((a : ℂ) * Complex.I)‖
        = ‖(S.r b : ℂ) * Complex.exp ((b : ℂ) * Complex.I)‖ := by rw [hab']
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_of_nonneg (S.hpos a).le, Complex.norm_of_nonneg (S.hpos b).le] at h1
    exact h1
  have hr0 : (S.r b : ℂ) ≠ 0 := by exact_mod_cast (S.hpos b).ne'
  have hexp : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) := by
    rw [hr] at hab'
    exact mul_right_injective₀ hr0 hab'
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  have hn' : (a : ℂ) = b + n * (2 * Real.pi) := by
    have := mul_left_injective₀ Complex.I_ne_zero
      (by rw [hn]; ring : (a : ℂ) * Complex.I = (b + n * (2 * Real.pi)) * Complex.I)
    exact this
  have hreal : a = b + n * (2 * Real.pi) := by exact_mod_cast hn'
  exact ⟨n, hreal⟩

theorem lap_of_turns {a b : ℝ} (hba : b - a < 2 * Real.pi) (M : ℤ) (j j' : ℕ) {s₁ s₂ : ℝ}
    (h1 : 2 * Real.pi * j + a ≤ s₁) (h2 : s₁ ≤ 2 * Real.pi * j + b)
    (h3 : 2 * Real.pi * j' + a ≤ s₂) (h4 : s₂ ≤ 2 * Real.pi * j' + b)
    (hM : s₁ = s₂ + M * (2 * Real.pi)) : (j : ℤ) - j' = M := by
  have hA : (M : ℝ) * (2 * Real.pi) < ((j : ℝ) - j' + 1) * (2 * Real.pi) := by linarith
  have hB : ((j : ℝ) - j' - 1) * (2 * Real.pi) < (M : ℝ) * (2 * Real.pi) := by linarith
  have hA' : (M : ℝ) < (j : ℝ) - j' + 1 := lt_of_mul_lt_mul_right hA Real.two_pi_pos.le
  have hB' : (j : ℝ) - j' - 1 < (M : ℝ) := lt_of_mul_lt_mul_right hB Real.two_pi_pos.le
  have hA'' : M < (j : ℤ) - j' + 1 := by exact_mod_cast hA'
  have hB'' : (j : ℤ) - j' - 1 < M := by exact_mod_cast hB'
  omega

theorem bounds_of_mem_arcIcc (R : RadialRegion) (e : ℕ) (he : e ≠ 0) (j : Fin e)
    (k : Fin R.N) {ψ : ℝ} (hψ : ψ ∈ (efold R e he).arcIcc (lapIdx R e he j k)) :
    2 * Real.pi * ((j : ℕ) : ℝ) + R.φs k.castSucc ≤ (e : ℝ) * ψ ∧
      (e : ℝ) * ψ ≤ 2 * Real.pi * ((j : ℕ) : ℝ) + R.φs k.succ := by
  have heR := natCast_pos_of_ne_zero he
  have h0 := hψ
  unfold RadialRegion.arcIcc at h0
  rw [φs_lapIdx_castSucc, φs_lapIdx_succ] at h0
  obtain ⟨h1, h2⟩ := h0
  exact ⟨le_of_div_le heR h1, div_le_of_le heR h2⟩

theorem injOn_pow_arcSet (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) (j : Fin e)
    (k : Fin R.N) :
    Set.InjOn (fun u : ℂ => R.q + u ^ e) ((efold R e he).arcSet (lapIdx R e he j k)) := by
  have heR := natCast_pos_of_ne_zero he
  have hba := arcLength_lt R hN k
  unfold RadialRegion.arcSet
  rintro _ ⟨ψ₁, hψ₁, rfl⟩ _ ⟨ψ₂, hψ₂, rfl⟩ h
  have h' : R.q + (efold R e he).loop ψ₁ ^ e = R.q + (efold R e he).loop ψ₂ ^ e := h
  rw [loop_pow, loop_pow] at h'
  obtain ⟨n, hn⟩ := loop_eq_exists_int R h'
  obtain ⟨h1, h2⟩ := bounds_of_mem_arcIcc R e he j k hψ₁
  obtain ⟨h3, h4⟩ := bounds_of_mem_arcIcc R e he j k hψ₂
  have hkey := lap_of_turns hba n j.val j.val h1 h2 h3 h4 hn
  have hn0 : n = 0 := by omega
  subst hn0
  simp only [Int.cast_zero, zero_mul, add_zero] at hn
  have hψ : ψ₁ = ψ₂ := mul_left_cancel₀ heR.ne' hn
  rw [hψ]

theorem arcSet_lap_disjoint (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0)
    (k : Fin R.N) {j j' : Fin e} (hjj' : j ≠ j') :
    Disjoint ((efold R e he).arcSet (lapIdx R e he j k))
      ((efold R e he).arcSet (lapIdx R e he j' k)) := by
  have hba := arcLength_lt R hN k
  rw [Set.disjoint_left]
  unfold RadialRegion.arcSet
  rintro _ ⟨ψ₁, hψ₁, rfl⟩ ⟨ψ₂, hψ₂, hψ⟩
  obtain ⟨n, hn⟩ := loop_eq_exists_int (efold R e he) hψ
  obtain ⟨h1, h2⟩ := bounds_of_mem_arcIcc R e he j k hψ₁
  obtain ⟨h3, h4⟩ := bounds_of_mem_arcIcc R e he j' k hψ₂
  have hM : (e : ℝ) * ψ₂ = (e : ℝ) * ψ₁ + ((n * (e : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hn]
    push_cast
    ring
  have hkey := lap_of_turns hba (n * (e : ℤ)) j'.val j.val h3 h4 h1 h2 hM
  have hj : (j.val : ℤ) < e := by exact_mod_cast j.isLt
  have hj' : (j'.val : ℤ) < e := by exact_mod_cast j'.isLt
  have hj0 : (0 : ℤ) ≤ j.val := by positivity
  have hj'0 : (0 : ℤ) ≤ j'.val := by positivity
  have hjne : (j.val : ℤ) ≠ j'.val := by
    intro hc
    apply hjj'
    apply Fin.ext
    exact_mod_cast hc
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · have h5 : n * (e : ℤ) ≤ (-1) * (e : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    linarith
  · subst hzero
    rw [zero_mul] at hkey
    exact hjne (by omega)
  · have h5 : (1 : ℤ) * (e : ℤ) ≤ n * (e : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    linarith


end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback
