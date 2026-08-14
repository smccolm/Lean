import RiemannZeta.GuthMaynard.DFIEquation24DoubleDual
import RiemannZeta.GuthMaynard.DFIEquation29
import RiemannZeta.GuthMaynard.DFIEquation30
import RiemannZeta.GuthMaynard.KloostermanComposite

/-!
# DFI equations (24)--(30): quantitative error assembly

This module estimates the eight non-main branches isolated by the exact
equation-(24) decomposition.  It keeps the complete Weil--Estermann factor
and the Mellin--Voronoi weights visible so that the source truncations from
equation (29) can be inserted without an assumed error certificate.
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

/-- Explicit norm of the logarithmic main operator on a positive compact
interval, in the form used for the mixed terms of DFI (24). -/
noncomputable def dfiVoronoiMainIntervalNorm
    (q : ℕ) (A B : ℝ) : ℝ :=
  (q : ℝ)⁻¹ * (B - A) *
    (|Real.log A| + |Real.log B| +
      2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|)

/-- Quantitative operator norm for the logarithmic main term in the divisor
Voronoi formula.  The estimate is deliberately stated on the actual support
interval: it is the device used below to integrate the source-uniform
equation-(29) bounds through the untransformed variable of each mixed branch
in DFI (24). -/
theorem norm_dfiVoronoiMainTerm_le_Icc_of_norm_le
    {A B K : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (q : ℕ) (hq : 0 < q) {g : ℝ → ℂ}
    (hSupport : Function.support g ⊆ Set.Icc A B)
    (hBound : ∀ x ∈ Set.Icc A B, ‖g x‖ ≤ K) :
    ‖dfiVoronoiMainTerm q g‖ ≤
      (q : ℝ)⁻¹ * (B - A) *
        (|Real.log A| + |Real.log B| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) * K := by
  let W : ℝ := |Real.log A| + |Real.log B| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hPoint (x : ℝ) (hx : x ∈ Set.Icc A B) :
      ‖((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)) * g x‖ ≤ W * K := by
    have hxpos : 0 < x := hA.trans_le hx.1
    have hlogLower : Real.log A ≤ Real.log x :=
      Real.log_le_log hA hx.1
    have hlogUpper : Real.log x ≤ Real.log B :=
      Real.log_le_log hxpos hx.2
    have hlogAbs : |Real.log x| ≤ |Real.log A| + |Real.log B| := by
      rw [abs_le]
      constructor
      · have hnegA : -|Real.log A| ≤ Real.log A := neg_abs_le _
        linarith [abs_nonneg (Real.log B)]
      · have hBabs : Real.log B ≤ |Real.log B| := le_abs_self _
        linarith [abs_nonneg (Real.log A)]
    have hWeight :
        ‖(dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
            2 * Complex.log (q : ℂ)‖ ≤ W := by
      have hlogq : ‖Complex.log (q : ℂ)‖ = |Real.log q| := by
        calc
          ‖Complex.log (q : ℂ)‖ = ‖(Real.log q : ℂ)‖ := by
            exact congrArg norm Complex.natCast_log |>.symm
          _ = |Real.log q| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      rw [dfiSafeLog_eq_log hx.1]
      calc
        ‖(Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
            2 * Complex.log (q : ℂ)‖ ≤
            ‖(Real.log x : ℂ) +
              2 * Real.eulerMascheroniConstant‖ +
              ‖2 * Complex.log (q : ℂ)‖ := by
          exact norm_sub_le _ _
        _ ≤ ‖(Real.log x : ℂ)‖ +
              ‖(2 * Real.eulerMascheroniConstant : ℂ)‖ +
              ‖2 * Complex.log (q : ℂ)‖ := by
          gcongr
          exact norm_add_le _ _
        _ = |Real.log x| + 2 * |Real.eulerMascheroniConstant| +
            2 * |Real.log q| := by
          simp only [norm_mul, norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs]
          rw [hlogq]
        _ ≤ W := by
          dsimp [W]
          linarith
    rw [norm_mul]
    exact mul_le_mul hWeight (hBound x hx) (norm_nonneg _) hW
  rw [dfiVoronoiMainTerm_eq_Icc hA q hSupport, norm_mul]
  have hIntegral := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume)
    (f := fun x : ℝ =>
      ((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (q : ℂ)) * g x)
    (s := Set.Icc A B) isCompact_Icc.measure_lt_top hPoint
  rw [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hAB)] at hIntegral
  calc
    ‖((q : ℂ)⁻¹)‖ *
        ‖∫ x in Set.Icc A B,
          ((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
            2 * Complex.log (q : ℂ)) * g x‖ ≤
        (q : ℝ)⁻¹ * ((W * K) * (B - A)) := by
      rw [norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hIntegral (by positivity)
    _ = (q : ℝ)⁻¹ * (B - A) * W * K := by ring

/-- Weighted form of `norm_dfiVoronoiMainTerm_le_Icc_of_norm_le`.  A
parameter-uniform Mellin decay estimate passes through the logarithmic main
operator with exactly the same vertical weight. -/
theorem mul_norm_dfiVoronoiMainTerm_le_Icc_of_mul_norm_le
    {A B K R : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hR : 0 < R)
    (q : ℕ) (hq : 0 < q) {g : ℝ → ℂ}
    (hSupport : Function.support g ⊆ Set.Icc A B)
    (hBound : ∀ x ∈ Set.Icc A B, R * ‖g x‖ ≤ K) :
    R * ‖dfiVoronoiMainTerm q g‖ ≤
      (q : ℝ)⁻¹ * (B - A) *
        (|Real.log A| + |Real.log B| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) * K := by
  have hPoint : ∀ x ∈ Set.Icc A B, ‖g x‖ ≤ K / R := by
    intro x hx
    exact (le_div_iff₀ hR).2 (by simpa [mul_comm] using hBound x hx)
  have hMain := norm_dfiVoronoiMainTerm_le_Icc_of_norm_le
    hA hAB q hq hSupport hPoint
  have hRnonneg : 0 ≤ R := hR.le
  calc
    R * ‖dfiVoronoiMainTerm q g‖ ≤
        R * ((q : ℝ)⁻¹ * (B - A) *
          (|Real.log A| + |Real.log B| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) *
          (K / R)) := mul_le_mul_of_nonneg_left hMain hRnonneg
    _ = (q : ℝ)⁻¹ * (B - A) *
        (|Real.log A| + |Real.log B| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) * K := by
      field_simp [hR.ne']

/-- Quantitative mixed-branch Fubini estimate.  Mellin transformation in
the first variable is commuted through the logarithmic main operator in the
second variable, and a uniform vertical-line estimate for the literal
source slices is preserved. -/
theorem mul_norm_mellin_dfiVoronoiMainTerm_family_le
    {E : ℝ → ℝ → ℂ} {A B C D K R : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (hq : 0 < q) (z : ℂ) (hR : 0 < R)
    (hBound : ∀ y ∈ Set.Icc C D,
      R * ‖mellin (fun x ↦ E x y) z‖ ≤ K) :
    R * ‖mellin
        (fun x ↦ dfiVoronoiMainTerm q (E x)) z‖ ≤
      (q : ℝ)⁻¹ * (D - C) *
        (|Real.log C| + |Real.log D| +
          2 * |Real.eulerMascheroniConstant| + 2 * |Real.log q|) * K := by
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hmem := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hmem.2, hmem.1⟩
  have hMellinSupport : Function.support
      (fun y ↦ mellin (fun x ↦ E x y) z) ⊆ Set.Icc C D := by
    intro y hy
    by_contra hyOutside
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      exact hyOutside (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support,
            Function.uncurry_apply_pair] using hne)).2
    change mellin (fun x ↦ E x y) z ≠ 0 at hy
    rw [hzero] at hy
    exact hy (by simp [mellin])
  rw [show (fun x ↦ dfiVoronoiMainTerm q (E x)) =
      fun x ↦ dfiVoronoiMainTerm q (fun y ↦ Eswap y x) by rfl]
  rw [mellin_dfiVoronoiMainTerm_comm_of_rectangular_support
    hEswap hC hA hSupportSwap q z]
  exact mul_norm_dfiVoronoiMainTerm_le_Icc_of_mul_norm_le
    hC hCD hR q hq hMellinSupport hBound

/-- Applying the logarithmic main operator in the second variable preserves
the DFI test-function class in the first variable. -/
noncomputable def dfiVoronoiMainTermSecondFamilyTestFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) :
    DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm q (E x)) := by
  let Eswap : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hEswap : ContDiff ℝ ∞ (Function.uncurry Eswap) := by
    simpa only [Eswap, Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSupportSwap : Function.support (Function.uncurry Eswap) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hm := hSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry E) by
        simpa only [Eswap, Function.mem_support,
          Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  simpa only [Eswap] using dfiVoronoiMainTermFamilyTestFunction
    hEswap hC hA hAB hSupportSwap q

/-- The elementary partial-sum estimate needed for DFI's retained dual
frequencies. -/
theorem sum_Icc_natCast_rpow_neg_quarter_le (L : ℕ) :
    ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (4 / 3 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  cases L with
  | zero => simp
  | succ K =>
      let f : ℝ → ℝ := fun x ↦ x ^ (-(1 / 4 : ℝ))
      have hanti : AntitoneOn f (Set.Icc 1 (1 + K)) := by
        exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
          (fun x hx ↦ lt_of_lt_of_le zero_lt_one hx.1)
      have htail :
          ∑ j ∈ Finset.range K, f (1 + (j + 1 : ℕ)) ≤
            ∫ x in (1 : ℝ)..1 + K, f x := hanti.sum_le_integral
      have hzero : (0 : ℝ) ∉ [[(1 : ℝ), 1 + K]] := by
        rw [Set.uIcc_of_le
          (le_add_of_nonneg_right (Nat.cast_nonneg K) : (1 : ℝ) ≤ 1 + K)]
        intro hx
        linarith [hx.1]
      rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)] at htail
      have hfinset : Finset.Icc 1 (K + 1) =
          insert 1 ((Finset.range K).image
            (fun j ↦ (1 + (j + 1) : ℕ))) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro hn
          by_cases h1 : n = 1
          · exact Or.inl h1
          · right
            refine ⟨n - 2, by omega, by omega⟩
        · intro hn
          rcases hn with h1 | ⟨j, hj, rfl⟩
          · omega
          · omega
      have honeNot : 1 ∉ (Finset.range K).image
          (fun j ↦ (1 + (j + 1) : ℕ)) := by
        intro hmem
        rw [Finset.mem_image] at hmem
        rcases hmem with ⟨j, _, hj⟩
        omega
      have hinj : Function.Injective (fun j : ℕ ↦ (1 + (j + 1) : ℕ)) := by
        intro x y hxy
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hxy
      rw [hfinset, Finset.sum_insert honeNot, Finset.sum_image] 
      · dsimp [f] at htail ⊢
        norm_num at htail ⊢
        calc
          _ ≤ 1 + (((1 + (K : ℝ)) ^ (3 / 4 : ℝ) - 1) /
                (3 / 4 : ℝ)) := by linarith
          _ ≤ (4 / 3 : ℝ) * (1 + (K : ℝ)) ^ (3 / 4 : ℝ) := by
            ring_nf
            norm_num
          _ = (4 / 3 : ℝ) * ((K : ℝ) + 1) ^ (3 / 4 : ℝ) := by
            congr 2
            ring
      · intro x _ y _ hxy
        exact hinj hxy

/-- Source-strength partial sum for DFI (29).  The exponent `ε - 1/4`
integrates to `L^(3/4+ε)` with the exact elementary constant. -/
theorem sum_Icc_natCast_rpow_sub_quarter_le
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε : ε < 1 / 4) (L : ℕ) :
    ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (ε - 1 / 4) ≤
      (3 / 4 + ε)⁻¹ * (L : ℝ) ^ (3 / 4 + ε) := by
  cases L with
  | zero =>
      have hαpos : 0 < 3 / 4 + ε := by linarith
      simp [Real.zero_rpow hαpos.ne']
  | succ K =>
      let p : ℝ := ε - 1 / 4
      let α : ℝ := 3 / 4 + ε
      have hp : p ≤ 0 := by dsimp [p]; linarith
      have hαpos : 0 < α := by dsimp [α]; linarith
      have hαle : α ≤ 1 := by dsimp [α]; linarith
      have hpα : p + 1 = α := by dsimp [p, α]; ring
      let f : ℝ → ℝ := fun x ↦ x ^ p
      have hanti : AntitoneOn f (Set.Icc 1 (1 + K)) := by
        exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hp).mono
          (fun x hx ↦ lt_of_lt_of_le zero_lt_one hx.1)
      have htail :
          ∑ j ∈ Finset.range K, f (1 + (j + 1 : ℕ)) ≤
            ∫ x in (1 : ℝ)..1 + K, f x := hanti.sum_le_integral
      have hzero : (0 : ℝ) ∉ [[(1 : ℝ), 1 + K]] := by
        rw [Set.uIcc_of_le
          (le_add_of_nonneg_right (Nat.cast_nonneg K) : (1 : ℝ) ≤ 1 + K)]
        intro hx
        linarith [hx.1]
      have hpGt : -1 < p := by dsimp [p]; linarith
      rw [integral_rpow (Or.inl hpGt)] at htail
      have hfinset : Finset.Icc 1 (K + 1) =
          insert 1 ((Finset.range K).image
            (fun j ↦ (1 + (j + 1) : ℕ))) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro hn
          by_cases h1 : n = 1
          · exact Or.inl h1
          · right
            refine ⟨n - 2, by omega, by omega⟩
        · intro hn
          rcases hn with h1 | ⟨j, hj, rfl⟩
          · omega
          · omega
      have honeNot : 1 ∉ (Finset.range K).image
          (fun j ↦ (1 + (j + 1) : ℕ)) := by
        intro hmem
        rw [Finset.mem_image] at hmem
        rcases hmem with ⟨j, _, hj⟩
        omega
      have hinj : Function.Injective (fun j : ℕ ↦ (1 + (j + 1) : ℕ)) := by
        intro x y hxy
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hxy
      rw [hfinset, Finset.sum_insert honeNot, Finset.sum_image]
      · dsimp [f] at htail ⊢
        norm_num at htail ⊢
        rw [hpα] at htail
        calc
          _ ≤ 1 + (((1 + (K : ℝ)) ^ α - 1) / α) := by
            nlinarith
          _ ≤ α⁻¹ * (1 + (K : ℝ)) ^ α := by
            rw [div_eq_mul_inv]
            field_simp [hαpos.ne']
            nlinarith
          _ = (3 / 4 + ε)⁻¹ * ((K : ℝ) + 1) ^ (3 / 4 + ε) := by
            dsimp [α]
            congr 2
            ring
      · intro x _ y _ hxy
        exact hinj hxy

/-- A complete Kloosterman coefficient may be pulled uniformly through one
absolutely convergent dual Voronoi series. -/
theorem norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    (q r : ℕ) [NeZero q] [NeZero r] (A : ZMod q)
    (frequency : ℕ → ZMod q) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖∑' n : ℕ, kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ ≤
      (Real.sqrt (Nat.gcd A.val q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ, ‖dfiVoronoiDualTerm r branch g n‖ := by
  let B : ℝ := Real.sqrt (Nat.gcd A.val q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDual := summable_norm_dfiVoronoiDualTerm r branch g
  have hScaled : Summable (fun n : ℕ =>
      B * ‖dfiVoronoiDualTerm r branch g n‖) := hDual.mul_left B
  have hPoint (n : ℕ) :
      ‖kloostermanSumZMod q A (frequency n) *
          dfiVoronoiDualTerm r branch g n‖ ≤
        B * ‖dfiVoronoiDualTerm r branch g n‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_kloostermanSumZMod_le_first_gcd q A (frequency n))
      (norm_nonneg _)
  have hSeries : Summable (fun n : ℕ =>
      kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n) := by
    apply Summable.of_norm_bounded hScaled
    exact hPoint
  calc
    ‖∑' n : ℕ, kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ ≤
      ∑' n : ℕ, ‖kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ :=
      norm_tsum_le_tsum_norm hSeries.norm
    _ ≤ ∑' n : ℕ, B * ‖dfiVoronoiDualTerm r branch g n‖ :=
      hSeries.norm.tsum_le_tsum hPoint hScaled
    _ = B * ∑' n : ℕ, ‖dfiVoronoiDualTerm r branch g n‖ := by
      rw [tsum_mul_left]

/-- A complete Kloosterman coefficient may be pulled uniformly through an
absolutely convergent source-ordered double-frequency series. -/
theorem norm_dfiEquation24DualDualKloosterman_le
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xSign ySign : DFIVoronoiFrequencySign)
    (amplitude : ℕ → ℕ → ℂ)
    (hRight : ∀ m, Summable (fun n ↦ ‖amplitude m n‖))
    (hOuter : Summable (fun m ↦ ∑' n, ‖amplitude m n‖)) :
    ‖dfiEquation24DualDualKloosterman
        q a b h xSign ySign amplitude‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' m : ℕ, ∑' n : ℕ, ‖amplitude m n‖ := by
  let B : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
    Real.sqrt q * (q.divisors.card : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hPoint (m n : ℕ) :
      ‖kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n‖ ≤ B * ‖amplitude m n‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_kloostermanSumZMod_le_first_gcd q (-h : ZMod q) _)
      (norm_nonneg _)
  have hInner (m : ℕ) : Summable (fun n : ℕ ↦
      kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n) := by
    apply Summable.of_norm_bounded ((hRight m).mul_left B)
    exact hPoint m
  have hInnerNorm (m : ℕ) :
      ‖∑' n : ℕ,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
              dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
          amplitude m n‖ ≤
        B * ∑' n : ℕ, ‖amplitude m n‖ := by
    calc
      _ ≤ ∑' n : ℕ,
          ‖kloostermanSumZMod q (-h : ZMod q)
              (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
                dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
            amplitude m n‖ := norm_tsum_le_tsum_norm (hInner m).norm
      _ ≤ ∑' n : ℕ, B * ‖amplitude m n‖ :=
        (hInner m).norm.tsum_le_tsum (hPoint m) ((hRight m).mul_left B)
      _ = B * ∑' n : ℕ, ‖amplitude m n‖ := by
        rw [tsum_mul_left]
  have hSeries : Summable (fun m : ℕ ↦ ∑' n : ℕ,
      kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n) := by
    apply Summable.of_norm_bounded (hOuter.mul_left B)
    exact hInnerNorm
  unfold dfiEquation24DualDualKloosterman
  calc
    _ ≤ ∑' m : ℕ, ‖∑' n : ℕ,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
              dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
          amplitude m n‖ := norm_tsum_le_tsum_norm hSeries.norm
    _ ≤ ∑' m : ℕ, B * ∑' n : ℕ, ‖amplitude m n‖ :=
      hSeries.norm.tsum_le_tsum hInnerNorm (hOuter.mul_left B)
    _ = B * ∑' m : ℕ, ∑' n : ℕ, ‖amplitude m n‖ := by
      rw [tsum_mul_left]

/-- The single transformed `x` branch has exactly the Weil factor times the
absolute dual Voronoi mass. -/
theorem norm_dfiEquation24XDualContribution_le
    (q a : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖dfiEquation24XDualContribution q a h branch g‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ,
          ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator
            branch g n‖ := by
  rw [dfiEquation24XDualContribution_eq]
  exact norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    q (dfiReducedModulus a q).denominator (-h : ZMod q)
    (fun n => dfiSignedFrequency branch.xSign
      (dfiLiftedInverseFrequency a q n)) branch g

/-- The symmetric single transformed `y` branch, including the reversed
source character, has the same Weil majorant. -/
theorem norm_dfiEquation24YDualContribution_le
    (q b : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖dfiEquation24YDualContribution q b h branch g‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ,
          ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator
            branch g n‖ := by
  rw [dfiEquation24YDualContribution_eq]
  exact norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    q (dfiReducedModulus b q).denominator (-h : ZMod q)
    (fun n => dfiSignedFrequency branch.ySign
      (dfiLiftedInverseFrequency b q n)) branch g

/-- The literal double-dual branch of equation (24) is bounded by the full
Weil factor times the absolutely convergent Mellin-amplitude mass. -/
theorem norm_dfiEquation24ActualDualDualContribution_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    ‖dfiEquation24ActualDualDualContribution
        q a b h xBranch yBranch E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            (dfiReducedModulus a q).denominator xBranch
            (dfiReducedModulus b q).denominator yBranch E m n‖ := by
  rw [dfiEquation24ActualDualDualContribution_eq_kloosterman
    hE hA hAB hC hCD hSupport q a b h xBranch yBranch]
  exact norm_dfiEquation24DualDualKloosterman_le
    q a b h xBranch.xSign yBranch.ySign
      (dfiEquation24DoubleDualMellinAmplitude
        (dfiReducedModulus a q).denominator xBranch
        (dfiReducedModulus b q).denominator yBranch E)
    (fun m ↦
      summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
        (E := E) (dfiReducedModulus a q).denominator xBranch
        (dfiReducedModulus b q).denominator yBranch m)
    (summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
      (E := E) (dfiReducedModulus a q).denominator xBranch
      (dfiReducedModulus b q).denominator yBranch)

/-- The literal eight non-main terms in DFI equation (24) are bounded by
the two one-sided transformed families and the four double-transformed
families.  This is the source-facing bridge from the exact branch expansion
to the analytic estimates in equations (29) and (30). -/
theorem norm_dfiEquation24ReducedError_le_single_add_double
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ) :
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (∑ branch : DFIVoronoiDualBranch,
        ‖dfiEquation24XDualContribution q a h branch
          (fun x ↦ dfiVoronoiMainTerm
            (dfiReducedModulus b q).denominator (E x))‖) +
      (∑ branch : DFIVoronoiDualBranch,
        ‖dfiEquation24YDualContribution q b h branch
          (fun y ↦ dfiVoronoiMainTerm
            (dfiReducedModulus a q).denominator (fun x ↦ E x y))‖) +
      ∑ yBranch : DFIVoronoiDualBranch,
        ∑ xBranch : DFIVoronoiDualBranch,
          ‖dfiEquation24ActualDualDualContribution
            q a b h xBranch yBranch E‖ := by
  calc
    ‖dfiEquation24ReducedError q a b h E‖ ≤
        ∑ yBranch : DFIVoronoiBranch, ∑ xBranch : DFIVoronoiBranch,
          if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
            ‖dfiEquation24ReducedBranchContribution
              q a b h xBranch yBranch E‖ :=
      norm_dfiEquation24ReducedError_le q a b h E
    _ = _ := by
      have hBranches : (Finset.univ : Finset DFIVoronoiBranch) =
          {DFIVoronoiBranch.mainTerm, DFIVoronoiBranch.minusTerm,
            DFIVoronoiBranch.plusTerm} := by
        ext branch
        fin_cases branch <;> simp
      have hDualBranches : (Finset.univ : Finset DFIVoronoiDualBranch) =
          {DFIVoronoiDualBranch.minusTerm,
            DFIVoronoiDualBranch.plusTerm} := by
        ext branch
        fin_cases branch <;> simp
      rw [hBranches, hDualBranches]
      simp only [Finset.sum_insert, Finset.sum_singleton,
        Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
        or_false, not_false_eq_true, true_and, false_and, ite_true,
        ite_false]
      have hxMinus := dfiEquation24ReducedBranchContribution_dual_main
        q a b h DFIVoronoiDualBranch.minusTerm E
      have hxPlus := dfiEquation24ReducedBranchContribution_dual_main
        q a b h DFIVoronoiDualBranch.plusTerm E
      have hyMinus := dfiEquation24ReducedBranchContribution_main_dual
        q a b h DFIVoronoiDualBranch.minusTerm E hE hA hC hCD hSupport
      have hyPlus := dfiEquation24ReducedBranchContribution_main_dual
        q a b h DFIVoronoiDualBranch.plusTerm E hE hA hC hCD hSupport
      have hmm := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.minusTerm
          DFIVoronoiDualBranch.minusTerm E
      have hpm := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.plusTerm
          DFIVoronoiDualBranch.minusTerm E
      have hmp := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.minusTerm
          DFIVoronoiDualBranch.plusTerm E
      have hpp := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.plusTerm
          DFIVoronoiDualBranch.plusTerm E
      simp only [DFIVoronoiDualBranch.toBranch] at hxMinus hxPlus hyMinus hyPlus hmm hpm hmp hpp
      rw [hxMinus, hxPlus, hyMinus, hyPlus, hmm, hpm, hmp, hpp]
      ring

/-- Absolute mass of the two `x`-dual/`y`-main terms in DFI (24). -/
noncomputable def dfiEquation24XSingleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ branch : DFIVoronoiDualBranch,
    ∑' n : ℕ,
      ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator branch
        (fun x ↦ dfiVoronoiMainTerm
          (dfiReducedModulus b q).denominator (E x)) n‖

/-- Absolute mass of the two `x`-main/`y`-dual terms in DFI (24). -/
noncomputable def dfiEquation24YSingleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ branch : DFIVoronoiDualBranch,
    ∑' n : ℕ,
      ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator branch
        (fun y ↦ dfiVoronoiMainTerm
          (dfiReducedModulus a q).denominator (fun x ↦ E x y)) n‖

/-- Absolute two-variable Mellin mass of the four double-dual terms in
DFI (24). -/
noncomputable def dfiEquation24DoubleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ yBranch : DFIVoronoiDualBranch,
    ∑ xBranch : DFIVoronoiDualBranch,
      ∑' m : ℕ, ∑' n : ℕ,
        ‖dfiEquation24DoubleDualMellinAmplitude
          (dfiReducedModulus a q).denominator xBranch
          (dfiReducedModulus b q).denominator yBranch E m n‖

/-- The complete equation-(24) error is the Weil--Estermann factor times
the sum of the two single-dual masses and the four double-dual masses. -/
theorem norm_dfiEquation24ReducedError_le_weil_mul_masses
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ) :
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (dfiEquation24XSingleDualMass q a b E +
          dfiEquation24YSingleDualMass q a b E +
          dfiEquation24DoubleDualMass q a b E) := by
  let K : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
    Real.sqrt q * (q.divisors.card : ℝ)
  have hSingle := norm_dfiEquation24ReducedError_le_single_add_double
    hE hA hC hCD hSupport q a b h
  calc
    ‖dfiEquation24ReducedError q a b h E‖ ≤
        (∑ branch : DFIVoronoiDualBranch,
          ‖dfiEquation24XDualContribution q a h branch
            (fun x ↦ dfiVoronoiMainTerm
              (dfiReducedModulus b q).denominator (E x))‖) +
        (∑ branch : DFIVoronoiDualBranch,
          ‖dfiEquation24YDualContribution q b h branch
            (fun y ↦ dfiVoronoiMainTerm
              (dfiReducedModulus a q).denominator (fun x ↦ E x y))‖) +
        ∑ yBranch : DFIVoronoiDualBranch,
          ∑ xBranch : DFIVoronoiDualBranch,
            ‖dfiEquation24ActualDualDualContribution
              q a b h xBranch yBranch E‖ := hSingle
    _ ≤
        (∑ branch : DFIVoronoiDualBranch,
          K * ∑' n : ℕ,
            ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator branch
              (fun x ↦ dfiVoronoiMainTerm
                (dfiReducedModulus b q).denominator (E x)) n‖) +
        (∑ branch : DFIVoronoiDualBranch,
          K * ∑' n : ℕ,
            ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator branch
              (fun y ↦ dfiVoronoiMainTerm
                (dfiReducedModulus a q).denominator (fun x ↦ E x y)) n‖) +
        ∑ yBranch : DFIVoronoiDualBranch,
          ∑ xBranch : DFIVoronoiDualBranch,
            K * ∑' m : ℕ, ∑' n : ℕ,
              ‖dfiEquation24DoubleDualMellinAmplitude
                (dfiReducedModulus a q).denominator xBranch
                (dfiReducedModulus b q).denominator yBranch E m n‖ := by
      apply add_le_add
      · apply add_le_add
        · apply Finset.sum_le_sum
          intro branch _hbranch
          simpa only [K] using
            norm_dfiEquation24XDualContribution_le q a h branch
              (fun x ↦ dfiVoronoiMainTerm
                (dfiReducedModulus b q).denominator (E x))
        · apply Finset.sum_le_sum
          intro branch _hbranch
          simpa only [K] using
            norm_dfiEquation24YDualContribution_le q b h branch
              (fun y ↦ dfiVoronoiMainTerm
                (dfiReducedModulus a q).denominator (fun x ↦ E x y))
      · apply Finset.sum_le_sum
        intro yBranch _hyBranch
        apply Finset.sum_le_sum
        intro xBranch _hxBranch
        simpa only [K] using
          norm_dfiEquation24ActualDualDualContribution_le
            hE hA hAB hC hCD hSupport q a b h xBranch yBranch
    _ = _ := by
      unfold dfiEquation24XSingleDualMass
        dfiEquation24YSingleDualMass dfiEquation24DoubleDualMass
      dsimp only [K]
      simp_rw [← Finset.mul_sum]
      ring

/-- Source specialization of the complete equation-(24) error bound.  All
smoothness, support, and positive-scale hypotheses are discharged from the
literal equation-(2)/(21)/(23) weight. -/
theorem norm_dfiEquation24_source_error_le_weil_mul_masses
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) :
    let E := dfiEquation23Weight w
      (dfiLocalizedWeight f φ h) a b h q
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (dfiEquation24XSingleDualMass q a b E +
          dfiEquation24YSingleDualMass q a b E +
          dfiEquation24DoubleDualMass q a b E) := by
  dsimp only
  have hE : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w
        (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w
        (dfiLocalizedWeight f φ h) a b h q)) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact norm_dfiEquation24ReducedError_le_weil_mul_masses
    hE
    (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
    ((div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X]))
    (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
    ((div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y]))
    hSupport q a b h

/-- A slice obtained after differentiating the second source variable is
still an admissible Voronoi test function in the first variable.  The
support proof uses the full rectangular support, so no projection or
pointwise-support shortcut is hidden in this construction. -/
noncomputable def dfiMixedDerivativeFirstSliceTestFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (j : ℕ) (y : ℝ) :
    DFIVoronoiTestFunction (fun x ↦ iteratedDeriv j (E x) y) where
  lower := A
  upper := B
  lower_pos := hA
  lower_le_upper := hAB
  smooth := contDiff_iteratedDeriv_slice_right hE j y
  support_subset := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y'
      by_contra hne
      exact hnot (hSupport (show
        (x, y') ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change iteratedDeriv j (E x) y ≠ 0 at hx
    rw [hzero] at hx
    exact hx (by simp)

@[simp] theorem iteratedDeriv_mixedDerivativeFirstSlice
    {E : ℝ → ℝ → ℂ}
    (i j : ℕ) (x y : ℝ) :
    iteratedDeriv i (fun x' ↦ iteratedDeriv j (E x') y) x =
      dfiMixedDeriv i j E x y := by
  rfl

/-- Differentiation in the retained second variable commutes with the
compactly supported Mellin transform in the first variable.  This is the
source-order identity that makes DFI's mixed derivative estimate (28)
apply literally. -/
theorem iteratedDeriv_mellin_transpose
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (j : ℕ) (y : ℝ) (z : ℂ) :
    iteratedDeriv j (fun y' ↦ mellin (fun x ↦ E x y') z) y =
      mellin (fun x ↦ iteratedDeriv j (E x) y) z := by
  let F : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    exact hE.comp (contDiff_snd.prodMk contDiff_fst)
  have hFSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hne : E p.2 p.1 ≠ 0 := by
      simpa [F, Function.mem_support, Function.uncurry_apply_pair] using hp
    have hs : (p.2, p.1) ∈ Function.support (Function.uncurry E) := by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne
    exact ⟨(hSupport hs).2, (hSupport hs).1⟩
  have h := iteratedDeriv_mellin_slice hF hA hFSupport j y z
  simpa only [F, dfiMixedDeriv, Function.uncurry_apply_pair] using h

/-- The explicit one-dimensional Mellin majorant obtained by integrating
by parts `p` times in logarithmic coordinates. -/
noncomputable def dfiMellinProfileMajorant
    (lower upper σ : ℝ) (p : ℕ) (A B : ℝ) : ℝ :=
  let D := max 1 (max upper lower⁻¹)
  (1 + 2 * Real.pi) ^ p *
    ((2 : ℝ) ^ p * ((-Real.log lower) - (-Real.log upper)) *
      (D ^ |σ| * A + D ^ |σ| *
        (A * (|σ| + (p : ℝ) + D * B) ^ p)))

theorem DFIVoronoiTestFunction.mellin_le_profileMajorant
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (σ : ℝ) (p : ℕ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDeriv : ∀ j ≤ p, ∀ x : ℝ,
      ‖iteratedDeriv j g x‖ ≤ A * B ^ j) (u : ℝ) :
    (1 + |u|) ^ p *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      dfiMellinProfileMajorant hg.lower hg.upper σ p A B := by
  exact hg.mellin_line_bound_of_physical_profile_order
    σ p hA hB hDeriv u

theorem dfiMellinProfileMajorant_mul_amplitude
    (lower upper σ : ℝ) (p j : ℕ) (A B : ℝ) :
    dfiMellinProfileMajorant lower upper σ p (A * B ^ j) B =
      dfiMellinProfileMajorant lower upper σ p A B * B ^ j := by
  simp only [dfiMellinProfileMajorant]
  ring

theorem dfiMellinProfileMajorant_scale_amplitude
    (lower upper σ : ℝ) (p : ℕ) (A B r : ℝ) :
    dfiMellinProfileMajorant lower upper σ p (A * r) B =
      dfiMellinProfileMajorant lower upper σ p A B * r := by
  simp only [dfiMellinProfileMajorant]
  ring

/-- Quantitative two-variable Mellin decay obtained by applying the
one-dimensional physical-profile estimate twice after the exact compact
support interchange.  Both frequency weights and every mixed derivative
used in DFI (28) are explicit. -/
theorem dfiBiMellin_line_bound_of_mixed_profile
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (σ τ : ℝ) (p : ℕ) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j))
    (u v : ℝ) :
    (1 + |u|) ^ p * (1 + |v|) ^ p *
        ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
          ((τ : ℂ) + (v : ℂ) * I)‖ ≤
      dfiMellinProfileMajorant C D τ p
        (dfiMellinProfileMajorant A B σ p M R) R := by
  let X : ℝ := dfiMellinProfileMajorant A B σ p M R
  let wu : ℝ := (1 + |u|) ^ p
  have hwu : 0 < wu := by dsimp [wu]; positivity
  have hInner (j : ℕ) (hj : j ≤ p) (y : ℝ) :
      wu * ‖mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ X * R ^ j := by
    have hProfile : ∀ i ≤ p, ∀ x : ℝ,
        ‖iteratedDeriv i (fun x' ↦ iteratedDeriv j (E x') y) x‖ ≤
          (M * R ^ j) * R ^ i := by
      intro i hi x
      rw [iteratedDeriv_mixedDerivativeFirstSlice]
      calc
        ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j) :=
          hDeriv i hi j hj x y
        _ = (M * R ^ j) * R ^ i := by rw [pow_add]; ring
    have hBound :=
      (dfiMixedDerivativeFirstSliceTestFunction hE hA hAB hSupport j y)
        |>.mellin_le_profileMajorant σ p
          (mul_nonneg hM (pow_nonneg hR j)) hR hProfile u
    simpa only [X, wu,
      dfiMellinProfileMajorant_mul_amplitude] using hBound
  have hX : 0 ≤ X := by
    have h0 := hInner 0 (Nat.zero_le p) 0
    have hleft : 0 ≤ wu *
        ‖mellin (fun x ↦ iteratedDeriv 0 (E x) 0)
          ((σ : ℂ) + (u : ℂ) * I)‖ := by positivity
    exact hleft.trans (by simpa using h0)
  let G : ℝ → ℂ := fun y ↦
    mellin (fun x ↦ E x y) ((σ : ℂ) + (u : ℂ) * I)
  have hGDeriv : ∀ j ≤ p, ∀ y : ℝ,
      ‖iteratedDeriv j G y‖ ≤ (X * wu⁻¹) * R ^ j := by
    intro j hj y
    rw [show iteratedDeriv j G y =
        mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I) by
      exact iteratedDeriv_mellin_transpose hE hA hSupport j y _]
    calc
      ‖mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ (X * R ^ j) / wu := by
        apply (le_div_iff₀ hwu).2
        simpa [mul_comm] using hInner j hj y
      _ = (X * wu⁻¹) * R ^ j := by
        rw [div_eq_mul_inv]
        ring
  have hOuter :=
    (dfiMellinTransposeTestFunction hE hA hC hCD hSupport
      ((σ : ℂ) + (u : ℂ) * I))
      |>.mellin_le_profileMajorant τ p
        (mul_nonneg hX (inv_nonneg.mpr hwu.le)) hR hGDeriv v
  change (1 + |v|) ^ p *
      ‖mellin G ((τ : ℂ) + (v : ℂ) * I)‖ ≤
        dfiMellinProfileMajorant C D τ p (X * wu⁻¹) R at hOuter
  have hComm := mellin_mellin_comm_of_rectangular_support
    hE hA hC hSupport
      ((σ : ℂ) + (u : ℂ) * I)
      ((τ : ℂ) + (v : ℂ) * I)
  rw [show dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
      ((τ : ℂ) + (v : ℂ) * I) =
        mellin G ((τ : ℂ) + (v : ℂ) * I) by
    exact hComm]
  have hScaled := mul_le_mul_of_nonneg_left hOuter hwu.le
  rw [dfiMellinProfileMajorant_scale_amplitude] at hScaled
  have hCancel : wu *
      (dfiMellinProfileMajorant C D τ p X R * wu⁻¹) =
        dfiMellinProfileMajorant C D τ p X R := by
    field_simp [ne_of_gt hwu]
  rw [hCancel] at hScaled
  simpa only [wu, X, mul_assoc] using hScaled

/-- Source-uniform two-variable Mellin estimate for the literal
equation-(23) weight.  The constants are selected before the arithmetic
parameters and every mixed derivative is supplied by DFI equation (28). -/
theorem exists_dfiEquation28_biMellin_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ τ : ℝ) (p : ℕ) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u v : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1),
          ∑ j ∈ Finset.range (p + 1), K i j
        let qQ := (q : ℝ) * Q
        let M := Csum * qQ⁻¹
        let R := ((a : ℝ) * (b : ℝ)) / qQ
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (1 + |u|) ^ p * (1 + |v|) ^ p *
            ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
              ((τ : ℂ) + (v : ℂ) * I)‖ ≤
          dfiMellinProfileMajorant (Y / b) (2 * Y / b) τ p
            (dfiMellinProfileMajorant (X / a) (2 * X / a)
              σ p M R) R := by
  choose K hK hBound using fun i j ↦
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i j
  refine ⟨K, hK, ?_⟩
  intro a b q ha hb hq hqQ h u v
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ : ℝ := (q : ℝ) * Q
  let M : ℝ := Csum * qQ⁻¹
  let R : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    have hinner : ∀ i ∈ Finset.range (p + 1),
        0 < ∑ j ∈ Finset.range (p + 1), K i j := by
      intro i _hi
      exact Finset.sum_pos (fun j _hj ↦ hK i j) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j) := by
    intro i hi j hj x y
    have hiMem : i ∈ Finset.range (p + 1) := by simp [hi]
    have hjMem : j ∈ Finset.range (p + 1) := by simp [hj]
    have hKle : K i j ≤ Csum := by
      dsimp [Csum]
      exact (Finset.single_le_sum (fun t _ ↦ (hK i t).le) hjMem).trans
        (Finset.single_le_sum
          (fun t _ ↦ Finset.sum_nonneg (fun s _ ↦ (hK t s).le)) hiMem)
    calc
      ‖dfiMixedDeriv i j E x y‖ ≤
          K i j * qQ⁻¹ * R ^ (i + j) := by
        simpa only [E, qQ, R] using
          hBound i j a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * R ^ (i + j) := by gcongr
      _ = M * R ^ (i + j) := rfl
  simpa only [E, M, R, Csum, qQ] using
    dfiBiMellin_line_bound_of_mixed_profile hE hXA hXAB hYC hYCD
      hSupport σ τ p hM hR hDeriv u v

/-- Two quadratically growing vertical multipliers consume four of six
powers of Mellin decay in each frequency, leaving an integrable Cauchy
kernel in both variables. -/
theorem two_frequency_quadratic_decay
    {a b c Cx Cy M u v : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hCx : 0 ≤ Cx) (hCy : 0 ≤ Cy) (hM : 0 ≤ M)
    (hA : a ≤ Cx * (1 + |u|) ^ 2)
    (hB : b ≤ Cy * (1 + |v|) ^ 2)
    (hC : (1 + |u|) ^ 6 * (1 + |v|) ^ 6 * c ≤ M) :
    a * b * c ≤
      Cx * Cy * M * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
  let wu : ℝ := 1 + |u|
  let wv : ℝ := 1 + |v|
  have hwu : 0 < wu := by dsimp [wu]; positivity
  have hwv : 0 < wv := by dsimp [wv]; positivity
  have hc' : c ≤ M / (wu ^ 6 * wv ^ 6) := by
    apply (le_div_iff₀ (mul_pos (pow_pos hwu 6) (pow_pos hwv 6))).2
    simpa only [wu, wv, mul_comm, mul_left_comm, mul_assoc] using hC
  have huDen : 0 < 1 + u ^ 2 := by positivity
  have hvDen : 0 < 1 + v ^ 2 := by positivity
  have huPow : 1 + u ^ 2 ≤ wu ^ 4 := by
    dsimp [wu]
    nlinarith [abs_nonneg u, sq_abs u]
  have hvPow : 1 + v ^ 2 ≤ wv ^ 4 := by
    dsimp [wv]
    nlinarith [abs_nonneg v, sq_abs v]
  have huInv : (wu ^ 4)⁻¹ ≤ (1 + u ^ 2)⁻¹ :=
    inv_anti₀ huDen huPow
  have hvInv : (wv ^ 4)⁻¹ ≤ (1 + v ^ 2)⁻¹ :=
    inv_anti₀ hvDen hvPow
  calc
    a * b * c ≤
        (Cx * wu ^ 2) * (Cy * wv ^ 2) *
          (M / (wu ^ 6 * wv ^ 6)) := by gcongr
    _ = Cx * Cy * M * (wu ^ 4)⁻¹ * (wv ^ 4)⁻¹ := by
      field_simp [ne_of_gt hwu, ne_of_gt hwv]
    _ ≤ Cx * Cy * M * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
      gcongr

/-- The fixed two-dimensional Cauchy mass left after the two DFI
archimedean multipliers are absorbed. -/
noncomputable def dfiCauchyPlaneMass : ℝ :=
  ∫ p : ℝ × ℝ, (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹

theorem integrable_dfiCauchyPlaneKernel :
    Integrable (fun p : ℝ × ℝ ↦
      (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) := by
  exact integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq

theorem dfiCauchyPlaneMass_nonneg : 0 ≤ dfiCauchyPlaneMass := by
  exact integral_nonneg fun _ ↦ mul_nonneg (inv_nonneg.mpr (by positivity))
    (inv_nonneg.mpr (by positivity))

/-- The common archimedean integral of a literal double-dual branch is
bounded by the equation-(28) bivariate Mellin majorant. -/
theorem integral_norm_dfiDualBranchMultipliers_mul_biMellin_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) (M : ℝ) (hM : 0 ≤ M)
    (hBi : ∀ u v : ℝ,
      (1 + |u|) ^ 6 * (1 + |v|) ^ 6 *
        ‖dfiBiMellin E (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ M) :
    (∫ p : ℝ × ℝ,
      ‖dfiDualBranchMultiplier qx xBranch
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
        dfiDualBranchMultiplier qy yBranch
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖) ≤
      (32 * qx * dfiArchimedeanScale qx ^ 2) *
        (32 * qy * dfiArchimedeanScale qy ^ 2) * M *
          dfiCauchyPlaneMass := by
  let Cx : ℝ := 32 * qx * dfiArchimedeanScale qx ^ 2
  let Cy : ℝ := 32 * qy * dfiArchimedeanScale qy ^ 2
  have hCx : 0 ≤ Cx := by dsimp [Cx]; positivity
  have hCy : 0 ≤ Cy := by dsimp [Cy]; positivity
  have hMajor : Integrable (fun p : ℝ × ℝ ↦
      Cx * Cy * M * ((1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹)) := by
    exact integrable_dfiCauchyPlaneKernel.const_mul (Cx * Cy * M)
  have hInt : Integrable (fun p : ℝ × ℝ ↦
      ‖dfiDualBranchMultiplier qx xBranch
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
        dfiDualBranchMultiplier qy yBranch
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖) := by
    exact (integrable_dfiDualBranchMultipliers_mul_biMellin
      hE hA hAB hC hCD hSupport qx qy xBranch yBranch).norm
  calc
    _ ≤ ∫ p : ℝ × ℝ,
        Cx * Cy * M * ((1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) := by
      apply integral_mono hInt hMajor
      intro p
      simpa only [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), Cx, Cy, mul_assoc] using
        two_frequency_quadratic_decay
          (norm_nonneg (dfiDualBranchMultiplier qy yBranch
            (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)))
          (norm_nonneg (dfiBiMellin E
            (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
            (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)))
          hCx hCy hM
          (norm_dfiDualBranchMultiplier_le qx xBranch p.1)
          (norm_dfiDualBranchMultiplier_le qy yBranch p.2)
          (hBi p.1 p.2)
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]
      rfl

theorem summable_norm_divisorWeight_LSeriesTerm_threeHalf :
    Summable (fun n : ℕ ↦
      ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖) := by
  have h := periodicDivisorCoeff_LSeriesSummable
    1 (fun _ : ZMod 1 ↦ (1 : ℂ)) (s := (3 / 2 : ℂ)) (by norm_num)
  have hEq : periodicDivisorCoeff 1 (fun _ : ZMod 1 ↦ (1 : ℂ)) =
      divisorWeight := by
    funext n
    simp [periodicDivisorCoeff, divisorWeight]
  rw [hEq] at h
  exact summable_norm_iff.mpr h

/-- The absolute Dirichlet mass of the ordinary divisor coefficients on
the DFI line `Re s = 3/2`. -/
noncomputable def dfiDivisorThreeHalfMass : ℝ :=
  ∑' n : ℕ, ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖

theorem dfiDivisorThreeHalfMass_nonneg : 0 ≤ dfiDivisorThreeHalfMass :=
  tsum_nonneg fun _ ↦ norm_nonneg _

/-- Exact coefficient/archimedean factorization for the
residue-independent double-dual amplitude integrand. -/
theorem integral_norm_dfiEquation24DoubleDualAmplitudeIntegrand_eq
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (m n : ℕ) :
    (∫ p : ℝ × ℝ,
      ‖dfiEquation24DoubleDualAmplitudeIntegrand
        qx xBranch qy yBranch E m n p‖) =
      ‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
        ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ *
        ∫ p : ℝ × ℝ,
          ‖dfiDualBranchMultiplier qx xBranch
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
            dfiDualBranchMultiplier qy yBranch
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖ := by
  have hx : periodicDivisorCoeff qx (fun _ ↦ 1) = divisorWeight := by
    funext k
    simp [periodicDivisorCoeff, divisorWeight]
  have hy : periodicDivisorCoeff qy (fun _ ↦ 1) = divisorWeight := by
    funext k
    simp [periodicDivisorCoeff, divisorWeight]
  have h := integral_norm_dfiEquation24DoubleMellinTerm
    (E := E) qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch m n
  rw [hx, hy] at h
  simpa only [dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand] using h

/-- The complete absolute `(m,n)` mass of one double-dual branch factors
through the fixed divisor mass and its common archimedean integral. -/
theorem tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch) :
    (∑' m : ℕ, ∑' n : ℕ,
      ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖) ≤
      ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
        dfiDivisorThreeHalfMass ^ 2 *
        ∫ p : ℝ × ℝ,
          ‖dfiDualBranchMultiplier qx xBranch
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
            dfiDualBranchMultiplier qy yBranch
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖ := by
  let K : ℝ := ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖
  let J : ℝ := ∫ p : ℝ × ℝ,
    ‖dfiDualBranchMultiplier qx xBranch
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
      dfiDualBranchMultiplier qy yBranch
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
      dfiBiMellin E
        (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
        (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖
  have hAmpOuter :=
    summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
      (E := E) qx xBranch qy yBranch
  have hCoeff := summable_norm_divisorWeight_LSeriesTerm_threeHalf
  have hCoeffScaled (m : ℕ) : Summable (fun n : ℕ ↦
      K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
        ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ * J)) := by
    exact ((hCoeff.mul_left
      ‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖).mul_right J).mul_left K
  have hInner (m : ℕ) :
      (∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤
        K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
          dfiDivisorThreeHalfMass * J) := by
    have hAmp := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    calc
      _ ≤ ∑' n : ℕ,
          K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
            ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ * J) :=
        hAmp.tsum_le_tsum (fun n ↦ by
          calc
            ‖dfiEquation24DoubleDualMellinAmplitude
                qx xBranch qy yBranch E m n‖ ≤
                K * ∫ p : ℝ × ℝ,
                  ‖dfiEquation24DoubleDualAmplitudeIntegrand
                    qx xBranch qy yBranch E m n p‖ := by
              exact norm_dfiEquation24DoubleDualMellinAmplitude_le
                qx xBranch qy yBranch E m n
            _ = K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
                ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ * J) := by
              rw [integral_norm_dfiEquation24DoubleDualAmplitudeIntegrand_eq])
          (hCoeffScaled m)
      _ = K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
          dfiDivisorThreeHalfMass * J) := by
        rw [show (fun n : ℕ ↦
            K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
              ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ * J)) =
            fun n : ℕ ↦
              (K * ‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ * J) *
                ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ by
          funext n; ring,
          tsum_mul_left]
        dsimp [dfiDivisorThreeHalfMass]
        ring
  have hOuterMajor : Summable (fun m : ℕ ↦
      K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
        dfiDivisorThreeHalfMass * J)) := by
    convert ((hCoeff.mul_right (dfiDivisorThreeHalfMass * J)).mul_left K) using 1
    funext m
    ring
  calc
    _ ≤ ∑' m : ℕ,
        K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
          dfiDivisorThreeHalfMass * J) :=
      hAmpOuter.tsum_le_tsum hInner hOuterMajor
    _ = K * dfiDivisorThreeHalfMass ^ 2 * J := by
      rw [show (fun m : ℕ ↦
          K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
            dfiDivisorThreeHalfMass * J)) =
          fun m : ℕ ↦
            K * (‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
              (dfiDivisorThreeHalfMass * J)) by
        funext m; ring,
        tsum_mul_left, tsum_mul_right]
      dsimp [K, J, dfiDivisorThreeHalfMass]
      ring
    _ = _ := rfl

/-- One complete double-dual Voronoi branch is bounded by the fixed divisor
mass, the two archimedean scales, and the bivariate Mellin majorant.  This is
the absolute-convergence step needed before the four signs are recombined in
DFI equation (24). -/
theorem tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le_of_biMellin
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (xBranch yBranch : DFIVoronoiDualBranch) (M : ℝ) (hM : 0 ≤ M)
    (hBi : ∀ u v : ℝ,
      (1 + |u|) ^ 6 * (1 + |v|) ^ 6 *
        ‖dfiBiMellin E (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ M) :
    (∑' m : ℕ, ∑' n : ℕ,
      ‖dfiEquation24DoubleDualMellinAmplitude
        qx xBranch qy yBranch E m n‖) ≤
      ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
        dfiDivisorThreeHalfMass ^ 2 *
        ((32 * qx * dfiArchimedeanScale qx ^ 2) *
          (32 * qy * dfiArchimedeanScale qy ^ 2) * M *
          dfiCauchyPlaneMass) := by
  refine (tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le
    qx xBranch qy yBranch).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact integral_norm_dfiDualBranchMultipliers_mul_biMellin_le
      hE hA hAB hC hCD hSupport qx qy xBranch yBranch M hM hBi
  · positivity

/-- The dual Voronoi series has no zero-frequency term; DFI's transformed
sums begin at frequency one. -/
@[simp] theorem dfiVoronoiDualTerm_zero
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    dfiVoronoiDualTerm q branch g 0 = 0 := by
  cases branch <;>
    simp [dfiVoronoiDualTerm, divisorWeight]

/-- Exact equation-(29) retained window. -/
noncomputable def dfiVoronoiDualMassUpTo
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖

/-- Exact equation-(29) tail beyond the retained window. -/
noncomputable def dfiVoronoiDualMassAfter
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) : ℝ :=
  ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖

/-- Exact integer cutoff for the transition in DFI (29).  Here `S` is the
physical support scale and `R` is the harmless source power. -/
noncomputable def dfiEquation29RetainedCutoff
    (q : ℕ) (S R : ℝ) : ℕ :=
  ⌈(q : ℝ) ^ 2 / S * R⌉₊

theorem dfiEquation29RetainedCutoff_pos
    (q : ℕ) [NeZero q] {S R : ℝ} (hS : 0 < S) (hR : 0 < R) :
    0 < dfiEquation29RetainedCutoff q S R := by
  have hTransition : 0 < (q : ℝ) ^ 2 / S * R := by
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity
  unfold dfiEquation29RetainedCutoff
  exact Nat.ceil_pos.mpr hTransition

theorem dfiEquation29_transition_le_retainedCutoff
    (q : ℕ) {S R : ℝ} :
    (q : ℝ) ^ 2 / S * R ≤ dfiEquation29RetainedCutoff q S R := by
  unfold dfiEquation29RetainedCutoff
  exact Nat.le_ceil _

/-- The exact integer window differs from DFI's real transition scale by
less than one.  This is the rounding estimate needed when the retained
frequency count is converted back to the source powers of `Q`. -/
theorem dfiEquation29RetainedCutoff_lt_transition_add_one
    (q : ℕ) {S R : ℝ} (hTransition : 0 ≤ (q : ℝ) ^ 2 / S * R) :
    (dfiEquation29RetainedCutoff q S R : ℝ) <
      (q : ℝ) ^ 2 / S * R + 1 := by
  unfold dfiEquation29RetainedCutoff
  exact Nat.ceil_lt_add_one hTransition

/-- Weak form of the preceding estimate, convenient under monotone real
powers. -/
theorem dfiEquation29RetainedCutoff_le_transition_add_one
    (q : ℕ) {S R : ℝ} (hTransition : 0 ≤ (q : ℝ) ^ 2 / S * R) :
    (dfiEquation29RetainedCutoff q S R : ℝ) ≤
      (q : ℝ) ^ 2 / S * R + 1 :=
  (dfiEquation29RetainedCutoff_lt_transition_add_one q hTransition).le

/-- Monotone-power form of the exact rounding estimate. -/
theorem dfiEquation29RetainedCutoff_rpow_le
    (q : ℕ) {S R α : ℝ} (hTransition : 0 ≤ (q : ℝ) ^ 2 / S * R)
    (hα : 0 ≤ α) :
    (dfiEquation29RetainedCutoff q S R : ℝ) ^ α ≤
      ((q : ℝ) ^ 2 / S * R + 1) ^ α := by
  exact Real.rpow_le_rpow
    (Nat.cast_nonneg (dfiEquation29RetainedCutoff q S R))
    (dfiEquation29RetainedCutoff_le_transition_add_one q hTransition) hα

/-- Passing to the reduced additive-character modulus does not enlarge the
equation-(29) transition. -/
theorem dfiEquation29_reduced_transition_le_original
    (a q : ℕ) [NeZero q] {S R : ℝ} (hS : 0 < S) (hR : 0 ≤ R) :
    ((dfiReducedModulus a q).denominator : ℝ) ^ 2 / S * R ≤
      (q : ℝ) ^ 2 / S * R := by
  have hden : ((dfiReducedModulus a q).denominator : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le a q
  have hdenNonneg : (0 : ℝ) ≤ (dfiReducedModulus a q).denominator := by
    positivity
  have hqNonneg : (0 : ℝ) ≤ q := by positivity
  have hsquare : ((dfiReducedModulus a q).denominator : ℝ) ^ 2 ≤
      (q : ℝ) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hsquare hS.le) hR

/-- Under the delta-method support `q ≤ 2Q`, the reduced transition is at
most the literal source scale `4 Q²/S`, before inserting the harmless
`Q^ε` enlargement. -/
theorem dfiEquation29_reduced_transition_le_four_mul
    (a q : ℕ) [NeZero q] {S R Q : ℝ} (hS : 0 < S) (hR : 0 ≤ R)
    (hQ : 0 ≤ Q) (hqQ : (q : ℝ) ≤ 2 * Q) :
    ((dfiReducedModulus a q).denominator : ℝ) ^ 2 / S * R ≤
      4 * Q ^ 2 / S * R := by
  refine (dfiEquation29_reduced_transition_le_original a q hS hR).trans ?_
  have hqNonneg : (0 : ℝ) ≤ q := by positivity
  have hsquare : (q : ℝ) ^ 2 ≤ 4 * Q ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hsquare hS.le) hR

/-- Summed retained-frequency bound from the right-shifted equation-(29)
contour. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassUpTo_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q),
      dfiVoronoiDualMassUpTo q branch g L ≤
        C * S ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨A, hA, hPoint⟩ :=
    hg.exists_dfiVoronoiDualTerm_scaled_retained_bound S hS branch
  refine ⟨(4 / 3 : ℝ) * A, by positivity, ?_⟩
  intro q L hq
  letI : NeZero q := hq
  have hScale : 0 ≤ A * S ^ (1 / 2 : ℝ) :=
    mul_nonneg hA (Real.rpow_nonneg hS.le _)
  unfold dfiVoronoiDualMassUpTo
  calc
    ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖ ≤
        ∑ n ∈ Finset.Icc 1 L,
          A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIcc : n ∈ Finset.Icc 1 L := by simpa using hn
      exact hPoint q hq n (by
        have := (Finset.mem_Icc.mp hnIcc).1
        omega)
    _ = (A * S ^ (1 / 2 : ℝ)) *
        ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (A * S ^ (1 / 2 : ℝ)) *
        ((4 / 3 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_natCast_rpow_neg_quarter_le L) hScale
    _ = ((4 / 3 : ℝ) * A) * S ^ (1 / 2 : ℝ) *
        (L : ℝ) ^ (3 / 4 : ℝ) := by ring

/-- Source-strength retained mass from the `Re z = 3/4` contour. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassUpTo_threeQuarter_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q),
      dfiVoronoiDualMassUpTo q branch g L ≤
        C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
          (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨A, hA, hPoint⟩ :=
    hg.exists_dfiVoronoiDualTerm_scaled_threeQuarter_bound
      S hS ε hε₀ branch
  let cε : ℝ := (3 / 4 + ε)⁻¹
  have hcε : 0 ≤ cε := by
    dsimp [cε]
    positivity
  refine ⟨cε * A, mul_nonneg hcε hA, ?_⟩
  intro q L hq
  letI : NeZero q := hq
  have hScale : 0 ≤ A * (q : ℝ) ^ (-(1 / 2 : ℝ)) *
      S ^ (3 / 4 : ℝ) := by positivity
  unfold dfiVoronoiDualMassUpTo
  calc
    ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖ ≤
        ∑ n ∈ Finset.Icc 1 L,
          A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
            (n : ℝ) ^ (ε - 1 / 4) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hPoint q hq n (by
        have hnIcc := (Finset.mem_Icc.mp hn).1
        omega)
    _ = (A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ)) *
        ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (ε - 1 / 4) := by
      rw [Finset.mul_sum]
    _ ≤ (A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ)) *
        (cε * (L : ℝ) ^ (3 / 4 + ε)) :=
      mul_le_mul_of_nonneg_left
        (by simpa [cε] using
          sum_Icc_natCast_rpow_sub_quarter_le hε₀.le hε L)
        hScale
    _ = (cε * A) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
        (L : ℝ) ^ (3 / 4 + ε) := by ring

/-- Universal passage from a source-normalized three-quarter-line transform
bound to its retained divisor-weighted mass. -/
theorem exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (_hq : NeZero q) (branch : DFIVoronoiDualBranch)
        (g : ℝ → ℂ) (K B : ℝ),
        (∀ n : ℕ, 0 < n →
          ‖dfiEquation29InitialTransform q branch g n‖ ≤
            K * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
              (n : ℝ) ^ (-(1 / 4 : ℝ))) →
        ∀ L : ℕ,
          dfiVoronoiDualMassUpTo q branch g L ≤
            C * K * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
              (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε₀
  let cε : ℝ := (3 / 4 + ε)⁻¹
  have hcε : 0 ≤ cε := by dsimp [cε]; positivity
  refine ⟨cε * D, mul_nonneg hcε hD.le, ?_⟩
  intro q hq branch g K B hTransform L
  letI : NeZero q := hq
  let R : ℝ := K * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B
  have hR : 0 ≤ R := by
    have hOne := hTransform 1 (by omega)
    have hnonneg : 0 ≤ ‖dfiEquation29InitialTransform q branch g 1‖ := norm_nonneg _
    dsimp [R]
    norm_num at hOne
    exact hnonneg.trans hOne
  have hPoint (n : ℕ) (hn : 0 < n) :
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        D * R * (n : ℝ) ^ (ε - 1 / 4) := by
    rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
    have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
      simpa [divisorWeight] using hDivisor n hn
    have hTransform' := hTransform n hn
    calc
      ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
          (D * (n : ℝ) ^ ε) *
            (R * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
        exact mul_le_mul hWeight (by simpa [R, mul_assoc] using hTransform')
          (norm_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      _ = D * R * (n : ℝ) ^ (ε - 1 / 4) := by
        calc
          (D * (n : ℝ) ^ ε) * (R * (n : ℝ) ^ (-(1 / 4 : ℝ))) =
              (D * R) * ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
          _ = (D * R) * (n : ℝ) ^ (ε + (-(1 / 4 : ℝ))) := by
            rw [Real.rpow_add (Nat.cast_pos.mpr hn)]
          _ = D * R * (n : ℝ) ^ (ε - 1 / 4) := by ring
  unfold dfiVoronoiDualMassUpTo
  calc
    ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖ ≤
        ∑ n ∈ Finset.Icc 1 L, D * R * (n : ℝ) ^ (ε - 1 / 4) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hPoint n (by
        have hnIcc := (Finset.mem_Icc.mp hn).1
        omega)
    _ = (D * R) * ∑ n ∈ Finset.Icc 1 L,
        (n : ℝ) ^ (ε - 1 / 4) := by rw [Finset.mul_sum]
    _ ≤ (D * R) * (cε * (L : ℝ) ^ (3 / 4 + ε)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [cε] using
          sum_Icc_natCast_rpow_sub_quarter_le hε₀.le hε L)
        (mul_nonneg hD.le hR)
    _ = (cε * D) * K * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
        (L : ℝ) ^ (3 / 4 + ε) := by
      dsimp [R]
      ring

/-- Absolute convergence decomposes the complete transformed mass exactly
into DFI's retained frequencies `1 ≤ n ≤ L` and the tail `n > L`. -/
theorem dfiVoronoiDualMassUpTo_add_after
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) :
    dfiVoronoiDualMassUpTo q branch g L +
        dfiVoronoiDualMassAfter q branch g L =
      ∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖ := by
  let F : ℕ → ℝ := fun n ↦ ‖dfiVoronoiDualTerm q branch g n‖
  have hF : Summable F := summable_norm_dfiVoronoiDualTerm q branch g
  have hSplit := hF.sum_add_tsum_nat_add (L + 1)
  have hFinite : ∑ n ∈ Finset.range (L + 1), F n =
      dfiVoronoiDualMassUpTo q branch g L := by
    unfold dfiVoronoiDualMassUpTo
    rw [show Finset.range (L + 1) = insert 0 (Finset.Icc 1 L) by
      ext n
      simp
      omega]
    simp [F]
  have hTail : (∑' j : ℕ, F (j + (L + 1))) =
      dfiVoronoiDualMassAfter q branch g L := by
    unfold dfiVoronoiDualMassAfter
    apply tsum_congr
    intro j
    rw [show j + (L + 1) = L + (j + 1) by omega]
  rw [hFinite, hTail] at hSplit
  simpa only [F] using hSplit

/-- Quantitative equation-(29) tail for an arbitrary admissible test
function, expressed using the exact tail object above. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassAfter_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
      dfiVoronoiDualMassAfter q branch g L ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  simpa only [dfiVoronoiDualMassAfter] using
    hg.exists_dfiVoronoiDualTerm_tail_scaled_decay S hS k hk branch

/-- Equation-(29) tail evaluated at its exact retained cutoff. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassAfter_cutoff_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q),
      dfiVoronoiDualMassAfter q branch g
          (dfiEquation29RetainedCutoff q S R) ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            (((q : ℝ) ^ 2 / S * R) ^ (-(k : ℝ))) := by
  obtain ⟨C, hC, hTail⟩ :=
    hg.exists_dfiVoronoiDualTerm_tail_of_transition S hS k hk branch
  refine ⟨C, hC, ?_⟩
  intro q hq
  letI : NeZero q := hq
  have hL : 0 < dfiEquation29RetainedCutoff q S R :=
    dfiEquation29RetainedCutoff_pos q hS (lt_of_lt_of_le zero_lt_one hR)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  simpa only [dfiVoronoiDualMassAfter] using
    hTail q (dfiEquation29RetainedCutoff q S R) hq R hL hRpos
      (dfiEquation29_transition_le_retainedCutoff q)

/-- Full one-variable Voronoi mass split at an arbitrary positive retained
window.  The first term is the right-contour estimate and the second is the
arbitrary-order left-contour tail. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMass_split_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
      (∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖) ≤
        A * S ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) +
        B * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A, hA, hRetained⟩ := hg.exists_dfiVoronoiDualMassUpTo_le S hS branch
  obtain ⟨B, hB, hTail⟩ := hg.exists_dfiVoronoiDualMassAfter_le S hS k hk branch
  refine ⟨A, B, hA, hB, ?_⟩
  intro q L hq hL
  letI : NeZero q := hq
  rw [← dfiVoronoiDualMassUpTo_add_after q branch g L]
  exact add_le_add (hRetained q L hq) (hTail q L hq hL)

/-- Complete divisor-weighted Voronoi mass from the two literal Mellin
contours used in DFI (29).  The right contour controls the retained window;
the arbitrarily deep left contour controls its complement. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMass_le_of_mellin_bounds
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch)
    {B₃ Bk : ℝ}
    (h₃ : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B₃)
    (hkLine : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin g (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
        (∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖) ≤
          A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B₃ *
              (L : ℝ) ^ (3 / 4 + ε) +
            D * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * Bk *
              ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A₀, hA₀, hRetainedFromTransform⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨A₁, hA₁, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_threeQuarter_constant branch
  obtain ⟨D, hD, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  refine ⟨A₀ * A₁, D, mul_nonneg hA₀ hA₁, hD, ?_⟩
  intro q L hq hL
  letI : NeZero q := hq
  have hB₃ : 0 ≤ B₃ := by
    have h := h₃ 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans h
  have hBk : 0 ≤ Bk := by
    have h := hkLine 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans h
  have hInitial := hTransform hg h₃ q hq
  have hRetained := hRetainedFromTransform q hq branch g A₁ B₃
    hInitial L
  have hAfter := hTail hg hBk hkLine q L hq hL
  rw [← dfiVoronoiDualMassUpTo_add_after q branch g L]
  exact add_le_add (by simpa [mul_assoc] using hRetained) hAfter

/-- Retained first-variable frequencies for the literal equation-(23)
source weight, with physical scale `X/a`. -/
theorem exists_dfiEquation29_xSlice_retained_mass
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (y : ℝ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r),
      dfiVoronoiDualMassUpTo r branch
          (fun x ↦ dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x y) L ≤
        C * (X / a) ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hScale : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  exact (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    |>.exists_dfiVoronoiDualMassUpTo_le (X / a) hScale branch

/-- Retained second-variable frequencies for the literal equation-(23)
source weight, with physical scale `Y/b`. -/
theorem exists_dfiEquation29_ySlice_retained_mass
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (hb : 0 < b) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (x : ℝ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r),
      dfiVoronoiDualMassUpTo r branch
          (dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x) L ≤
        C * (Y / b) ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hScale : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
  exact (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    |>.exists_dfiVoronoiDualMassUpTo_le (Y / b) hScale branch

/-- Source-uniform retained first-variable mass on the three-quarter
contour, including the divisor-function loss `ε`. -/
theorem exists_dfiEquation29_xSlice_retained_mass_threeQuarter
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (hUQ : U = Q ^ 2) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (r : ℕ) (_hr : NeZero r) (L : ℕ),
        let C₆ := ∑ i ∈ Finset.range 7, C i
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * X / a)
        dfiVoronoiDualMassUpTo r branch
            (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x y) L ≤
          K * (r : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((1 + 2 * Real.pi) ^ 6 *
              (64 * ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
                (D * A + D * (1024 * A * (1 + D * B) ^ 6)))) *
            (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨M, hM, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨K, hK, C, hC, hTransform⟩ :=
    exists_dfiEquation29_xSlice_threeQuarter_transform_bound
      hf hbox hφ hscale w hUQ branch
  refine ⟨M * K, mul_nonneg hM hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y r hr L
  dsimp only
  have hApply := hMass r hr branch
    (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
      a b h q x y) K
    ((1 + 2 * Real.pi) ^ 6 *
      (64 * ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
        (max 1 (2 * X / a) *
            ((∑ i ∈ Finset.range 7, C i) * ((q : ℝ) * Q)⁻¹) +
          max 1 (2 * X / a) *
            (1024 * ((∑ i ∈ Finset.range 7, C i) * ((q : ℝ) * Q)⁻¹) *
              (1 + max 1 (2 * X / a) *
                (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q))) ^ 6))))
    (hTransform a b q ha hb hq hqQ h y r hr) L
  simpa [mul_assoc] using hApply

/-- Source-uniform retained second-variable mass, symmetric to the preceding
first-variable theorem. -/
theorem exists_dfiEquation29_ySlice_retained_mass_threeQuarter
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (hUQ : U = Q ^ 2) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (r : ℕ) (_hr : NeZero r) (L : ℕ),
        let C₆ := ∑ j ∈ Finset.range 7, C j
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * Y / b)
        dfiVoronoiDualMassUpTo r branch
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x) L ≤
          K * (r : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((1 + 2 * Real.pi) ^ 6 *
              (64 * ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
                (D * A + D * (1024 * A * (1 + D * B) ^ 6)))) *
            (L : ℝ) ^ (3 / 4 + ε) := by
  obtain ⟨M, hM, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨K, hK, C, hC, hTransform⟩ :=
    exists_dfiEquation29_ySlice_threeQuarter_transform_bound
      hf hbox hφ hscale w hUQ branch
  refine ⟨M * K, mul_nonneg hM hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x r hr L
  dsimp only
  have hApply := hMass r hr branch
    (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x) K
    ((1 + 2 * Real.pi) ^ 6 *
      (64 * ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
        (max 1 (2 * Y / b) *
            ((∑ j ∈ Finset.range 7, C j) * ((q : ℝ) * Q)⁻¹) +
          max 1 (2 * Y / b) *
            (1024 * ((∑ j ∈ Finset.range 7, C j) * ((q : ℝ) * Q)⁻¹) *
              (1 + max 1 (2 * Y / b) *
                (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q))) ^ 6))))
    (hTransform a b q ha hb hq hqQ h x r hr) L
  simpa [mul_assoc] using hApply

/-- The literal source majorant produced by equation (28) after a logarithmic
Voronoi main operator is applied in the other variable.  `S/c` is the Mellin
variable's physical scale and `R/d` is the interval integrated by the main
operator. -/
noncomputable def dfiEquation28MixedMajorant
    (C : ℕ → ℝ) (p : ℕ) (σ Q S R : ℝ)
    (a b q qMain c d : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1), C i
  let qQ := (q : ℝ) * Q
  let A := Csum * qQ⁻¹
  let B := ((a : ℝ) * (b : ℝ)) / qQ
  let D := max 1 (max (2 * S / c) (S / c)⁻¹)
  dfiVoronoiMainIntervalNorm qMain (R / d) (2 * R / d) *
    ((1 + 2 * Real.pi) ^ p *
      ((2 : ℝ) ^ p *
        ((-Real.log (S / c)) - (-Real.log (2 * S / c))) *
        (D ^ |σ| * A +
          D ^ |σ| * (A * (|σ| + (p : ℝ) + D * B) ^ p))))

/-- Source-uniform all-orders Mellin estimate for the `x`-dual/`y`-main
mixed branch of DFI (24).  This is not a separately assumed mixed estimate:
it is obtained by commuting the actual Mellin transform with the actual
logarithmic main term and inserting equation (28) for every source slice. -/
theorem exists_dfiEquation28_xMellin_yMain_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1), C i
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * X / a) (X / a)⁻¹)
        let M := (1 + 2 * Real.pi) ^ p *
          ((2 : ℝ) ^ p *
            ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
            (D ^ |σ| * A +
              D ^ |σ| * (A * (|σ| + (p : ℝ) + D * B) ^ p)))
        (1 + |u|) ^ p *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiVoronoiMainIntervalNorm qy (Y / b) (2 * Y / b) * M := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_xSlice_mellin_line_bound_order
      hf hbox hφ hscale w hUQ σ p
  refine ⟨C, hC, ?_⟩
  intro a b q qy ha hb hq hqy hqQ h u
  dsimp only
  let E : ℝ → ℝ → ℂ :=
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hXA hYC hYCD hSupport qy hqy
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun y _hy ↦ hRaw a b q ha hb hq hqQ h y u)
  simpa only [E, dfiVoronoiMainIntervalNorm] using hMixed

/-- Symmetric source-uniform all-orders Mellin estimate for the
`x`-main/`y`-dual mixed branch of DFI (24). -/
theorem exists_dfiEquation28_yMellin_xMain_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        let Csum := ∑ j ∈ Finset.range (p + 1), C j
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * Y / b) (Y / b)⁻¹)
        let M := (1 + 2 * Real.pi) ^ p *
          ((2 : ℝ) ^ p *
            ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
            (D ^ |σ| * A +
              D ^ |σ| * (A * (|σ| + (p : ℝ) + D * B) ^ p)))
        (1 + |u|) ^ p *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x y))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiVoronoiMainIntervalNorm qx (X / a) (2 * X / a) * M := by
  obtain ⟨C, hC, hRaw⟩ :=
    exists_dfiEquation28_ySlice_mellin_line_bound_order
      hf hbox hφ hscale w hUQ σ p
  refine ⟨C, hC, ?_⟩
  intro a b q qx ha hb hq hqx hqQ h u
  dsimp only
  let E : ℝ → ℝ → ℂ := fun y x ↦
    dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x y
  have hSource : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    simpa only [E, Function.uncurry_apply_pair] using hSource.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  have hSourceSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
        Set.Icc (X / a) (2 * X / a) ×ˢ
          Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (Y / b) (2 * Y / b) ×ˢ
        Set.Icc (X / a) (2 * X / a) := by
    intro p hp
    have hm := hSourceSupport (show
      (p.2, p.1) ∈ Function.support (Function.uncurry
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q)) by
      simpa only [E, Function.mem_support,
        Function.uncurry_apply_pair] using hp)
    exact ⟨hm.2, hm.1⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hYA : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hXC : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXCD : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hR : 0 < (1 + |u|) ^ p := by positivity
  have hMixed := mul_norm_mellin_dfiVoronoiMainTerm_family_le
    hE hYA hXC hXCD hSupport qx hqx
      ((σ : ℂ) + (u : ℂ) * I) hR
      (fun x _hx ↦ hRaw a b q ha hb hq hqQ h x u)
  simpa only [E, dfiVoronoiMainIntervalNorm] using hMixed

/-- Concise source form of the mixed `x`-Mellin/`y`-main estimate. -/
theorem exists_dfiEquation28_xMellin_yMain_source_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q qy : ℕ), 0 < a → 0 < b → 0 < q → 0 < qy →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun x ↦ dfiVoronoiMainTerm qy
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28MixedMajorant C p σ Q X Y a b q qy a b := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_dfiEquation28_xMellin_yMain_line_bound_order
      hf hbox hφ hscale w hUQ σ p
  exact ⟨C, hC, by
    intro a b q qy ha hb hq hqy hqQ h u
    simpa only [dfiEquation28MixedMajorant] using
      hBound a b q qy ha hb hq hqy hqQ h u⟩

/-- Concise source form of the symmetric mixed `y`-Mellin/`x`-main
estimate. -/
theorem exists_dfiEquation28_yMellin_xMain_source_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q qx : ℕ), 0 < a → 0 < b → 0 < q → 0 < qx →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (u : ℝ),
        (1 + |u|) ^ p *
          ‖mellin (fun y ↦ dfiVoronoiMainTerm qx
              (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x y))
            ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          dfiEquation28MixedMajorant C p σ Q Y X a b q qx b a := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_dfiEquation28_yMellin_xMain_line_bound_order
      hf hbox hφ hscale w hUQ σ p
  exact ⟨C, hC, by
    intro a b q qx ha hb hq hqx hqQ h u
    simpa only [dfiEquation28MixedMajorant] using
      hBound a b q qx ha hb hq hqx hqQ h u⟩

/-- The actual `x`-dual/`y`-main equation-(24) test function, with all
smoothness and support obligations discharged from equations (2), (21), and
(23). -/
noncomputable def dfiEquation23XMainFamilyTestFunction
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) :
    DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm (dfiReducedModulus b q).denominator
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x)) := by
  have hE : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact dfiVoronoiMainTermSecondFamilyTestFunction hE
    (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
    ((div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X]))
    (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
    hSupport (dfiReducedModulus b q).denominator

/-- The actual `x`-main/`y`-dual equation-(24) test function. -/
noncomputable def dfiEquation23YMainFamilyTestFunction
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) :
    DFIVoronoiTestFunction
      (fun y ↦ dfiVoronoiMainTerm (dfiReducedModulus a q).denominator
        (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y)) := by
  have hE : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle (φ := φ) w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact dfiVoronoiMainTermFamilyTestFunction hE
    (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
    (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
    ((div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y]))
    hSupport (dfiReducedModulus a q).denominator

/-- Source-uniform bound for either of the two `x`-dual/`y`-main branches
in equation (24), obtained from the retained and tail contours of equation
(29).  No transformed-sum estimate is assumed. -/
theorem exists_dfiEquation24_xSingleDualBranch_mass_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∃ C₃ Ck : ℕ → ℝ, (∀ i, 0 < C₃ i) ∧ (∀ i, 0 < Ck i) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (L : ℕ), 0 < L →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (∑' n : ℕ, ‖dfiVoronoiDualTerm qx branch
            (fun x ↦ dfiVoronoiMainTerm qy (E x)) n‖) ≤
          A * (qx : ℝ) ^ (-(1 / 2 : ℝ)) *
              dfiEquation28MixedMajorant C₃ 6 (3 / 4) Q X Y
                a b q qy a b * (L : ℝ) ^ (3 / 4 + ε) +
            D * (qx : ℝ) ^ (2 + 2 * (k : ℝ)) *
              dfiEquation28MixedMajorant Ck (2 * (k + 1) + 4)
                (-(1 / 2 : ℝ) - k) Q X Y a b q qy a b *
              ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A₀, hA₀, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨A₁, hA₁, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_threeQuarter_constant branch
  obtain ⟨D, hD, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨C₃, hC₃, hRight⟩ :=
    exists_dfiEquation28_xMellin_yMain_source_bound
      hf hbox hφ hscale w hUQ (3 / 4) 6
  obtain ⟨Ck, hCk, hLeft⟩ :=
    exists_dfiEquation28_xMellin_yMain_source_bound
      hf hbox hφ hscale w hUQ (-(1 / 2 : ℝ) - k)
        (2 * (k + 1) + 4)
  refine ⟨A₀ * A₁, D, mul_nonneg hA₀ hA₁, hD,
    C₃, Ck, hC₃, hCk, ?_⟩
  intro a b q hq0 ha hb hqQ h L hL
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hg : DFIVoronoiTestFunction
      (fun x ↦ dfiVoronoiMainTerm qy (E x)) := by
    simpa only [qx, qy, E] using dfiEquation23XMainFamilyTestFunction
      w hf hbox hφ a b ha hb h q hq
  have hRightLine := hRight a b q qy ha hb hq hqy hqQ h
  have hLeftLine := hLeft a b q qy ha hb hq hqy hqQ h
  let B₃ := dfiEquation28MixedMajorant C₃ 6 (3 / 4) Q X Y
    a b q qy a b
  let Bk := dfiEquation28MixedMajorant Ck (2 * (k + 1) + 4)
    (-(1 / 2 : ℝ) - k) Q X Y a b q qy a b
  have hRightLine' : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin (fun x ↦ dfiVoronoiMainTerm qy (E x))
          (((3 / 4 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ B₃ := by
    simpa only [E, B₃] using hRightLine
  have hLeftLine' : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin (fun x ↦ dfiVoronoiMainTerm qy (E x))
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk := by
    simpa only [E, Bk] using hLeftLine
  have hRightComplex : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin (fun x ↦ dfiVoronoiMainTerm qy (E x))
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B₃ := by
    intro u
    have hCast : (((3 / 4 : ℝ) : ℂ)) = (3 / 4 : ℂ) := by norm_num
    simpa only [hCast] using hRightLine' u
  have hB₃ : 0 ≤ B₃ := by
    have hu := hRightLine' 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hBk : 0 ≤ Bk := by
    have hu := hLeftLine' 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hInitial := hTransform hg hRightComplex qx inferInstance
  have hRetained := hMass qx inferInstance branch
    (fun x ↦ dfiVoronoiMainTerm qy (E x)) A₁ B₃ hInitial L
  have hAfter := hTail hg hBk hLeftLine' qx L inferInstance hL
  dsimp only [qx, qy, E]
  rw [← dfiVoronoiDualMassUpTo_add_after qx branch
    (fun x ↦ dfiVoronoiMainTerm qy (E x)) L]
  exact add_le_add (by simpa [B₃, mul_assoc] using hRetained)
    (by simpa [Bk, mul_assoc] using hAfter)

/-- Source-uniform bound for either symmetric `x`-main/`y`-dual branch in
equation (24). -/
theorem exists_dfiEquation24_ySingleDualBranch_mass_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (ε : ℝ) (hε₀ : 0 < ε) (hε : ε < 1 / 4)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∃ C₃ Ck : ℕ → ℝ, (∀ i, 0 < C₃ i) ∧ (∀ i, 0 < Ck i) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (L : ℕ), 0 < L →
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q
        (∑' n : ℕ, ‖dfiVoronoiDualTerm qy branch
            (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) n‖) ≤
          A * (qy : ℝ) ^ (-(1 / 2 : ℝ)) *
              dfiEquation28MixedMajorant C₃ 6 (3 / 4) Q Y X
                a b q qx b a * (L : ℝ) ^ (3 / 4 + ε) +
            D * (qy : ℝ) ^ (2 + 2 * (k : ℝ)) *
              dfiEquation28MixedMajorant Ck (2 * (k + 1) + 4)
                (-(1 / 2 : ℝ) - k) Q Y X a b q qx b a *
              ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A₀, hA₀, hMass⟩ :=
    exists_dfiVoronoiDualMassUpTo_le_of_initial_threeQuarter ε hε₀ hε
  obtain ⟨A₁, hA₁, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_threeQuarter_constant branch
  obtain ⟨D, hD, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨C₃, hC₃, hRight⟩ :=
    exists_dfiEquation28_yMellin_xMain_source_bound
      hf hbox hφ hscale w hUQ (3 / 4) 6
  obtain ⟨Ck, hCk, hLeft⟩ :=
    exists_dfiEquation28_yMellin_xMain_source_bound
      hf hbox hφ hscale w hUQ (-(1 / 2 : ℝ) - k)
        (2 * (k + 1) + 4)
  refine ⟨A₀ * A₁, D, mul_nonneg hA₀ hA₁, hD,
    C₃, Ck, hC₃, hCk, ?_⟩
  intro a b q hq0 ha hb hqQ h L hL
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  have hqx : 0 < qx := NeZero.pos qx
  have hqy : 0 < qy := NeZero.pos qy
  have hg : DFIVoronoiTestFunction
      (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) := by
    simpa only [qx, qy, E] using dfiEquation23YMainFamilyTestFunction
      w hf hbox hφ a b ha hb h q hq
  have hRightLine := hRight a b q qx ha hb hq hqx hqQ h
  have hLeftLine := hLeft a b q qx ha hb hq hqx hqQ h
  let B₃ := dfiEquation28MixedMajorant C₃ 6 (3 / 4) Q Y X
    a b q qx b a
  let Bk := dfiEquation28MixedMajorant Ck (2 * (k + 1) + 4)
    (-(1 / 2 : ℝ) - k) Q Y X a b q qx b a
  have hRightLine' : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
          (((3 / 4 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ B₃ := by
    simpa only [E, B₃] using hRightLine
  have hLeftLine' : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
          (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ Bk := by
    simpa only [E, Bk] using hLeftLine
  have hRightComplex : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y))
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B₃ := by
    intro u
    have hCast : (((3 / 4 : ℝ) : ℂ)) = (3 / 4 : ℂ) := by norm_num
    simpa only [hCast] using hRightLine' u
  have hB₃ : 0 ≤ B₃ := by
    have hu := hRightLine' 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hBk : 0 ≤ Bk := by
    have hu := hLeftLine' 0
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans hu
  have hInitial := hTransform hg hRightComplex qy inferInstance
  have hRetained := hMass qy inferInstance branch
    (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) A₁ B₃ hInitial L
  have hAfter := hTail hg hBk hLeftLine' qy L inferInstance hL
  dsimp only [qx, qy, E]
  rw [← dfiVoronoiDualMassUpTo_add_after qy branch
    (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) L]
  exact add_le_add (by simpa [B₃, mul_assoc] using hRetained)
    (by simpa [Bk, mul_assoc] using hAfter)

/-- The literal nested majorant produced by equation (28) for the
two-variable Mellin transform on `Re s = Re t = -1/2`. -/
noncomputable def dfiEquation28BiMajorant
    (K : ℕ → ℕ → ℝ) (p : ℕ) (Q X Y : ℝ)
    (a b q : ℕ) : ℝ :=
  let Csum := ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (p + 1), K i j
  let qQ := (q : ℝ) * Q
  let M := Csum * qQ⁻¹
  let R := ((a : ℝ) * (b : ℝ)) / qQ
  dfiMellinProfileMajorant (Y / b) (2 * Y / b) (-(1 / 2)) p
    (dfiMellinProfileMajorant (X / a) (2 * X / a) (-(1 / 2)) p M R) R

/-- Each of the four source double-dual branches is bounded uniformly by
the actual equation-(28) bivariate Mellin majorant.  All smoothness, support,
and positivity hypotheses are discharged from equations (2), (21), and (23). -/
theorem exists_dfiEquation24_doubleDualBranch_mass_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ h : ℤ,
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
        (∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖) ≤
          ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
            dfiDivisorThreeHalfMass ^ 2 *
            ((32 * qx * dfiArchimedeanScale qx ^ 2) *
              (32 * qy * dfiArchimedeanScale qy ^ 2) *
              dfiEquation28BiMajorant K 6 Q X Y a b q *
              dfiCauchyPlaneMass) := by
  obtain ⟨K, hK, hBound⟩ :=
    exists_dfiEquation28_biMellin_line_bound_order
      hf hbox hφ hscale w hUQ (-(1 / 2)) (-(1 / 2)) 6
  refine ⟨K, hK, ?_⟩
  intro a b q hq0 ha hb hqQ h
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let M := dfiEquation28BiMajorant K 6 Q X Y a b q
  have hLine := hBound a b q ha hb hq hqQ h
  have hBi : ∀ u v : ℝ,
      (1 + |u|) ^ 6 * (1 + |v|) ^ 6 *
        ‖dfiBiMellin E (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ M := by
    intro u v
    simpa [E, M, dfiEquation28BiMajorant] using hLine u v
  have hM : 0 ≤ M := by
    have hZero := hBi 0 0
    exact (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (norm_nonneg _)).trans hZero
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  simpa only [qx, qy, E, M] using
    tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le_of_biMellin
      hE hXA hXAB hYC hYCD hSupport qx qy xBranch yBranch M hM hBi

/-- The four double-dual signs in DFI equation (24), recombined with one
source-uniform equation-(28) constant field. -/
theorem exists_dfiEquation24_doubleDualMass_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) :
    ∃ K : ℕ → ℕ → ℝ, (∀ i j, 0 < K i j) ∧
      ∀ (a b q : ℕ) (_hq0 : NeZero q), 0 < a → 0 < b →
        (q : ℝ) ≤ 2 * Q → ∀ h : ℤ,
        let qx := (dfiReducedModulus a q).denominator
        let qy := (dfiReducedModulus b q).denominator
        dfiEquation24DoubleDualMass q a b
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) ≤
          4 * (‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
            dfiDivisorThreeHalfMass ^ 2 *
            ((32 * qx * dfiArchimedeanScale qx ^ 2) *
              (32 * qy * dfiArchimedeanScale qy ^ 2) *
              dfiEquation28BiMajorant K 6 Q X Y a b q *
              dfiCauchyPlaneMass)) := by
  obtain ⟨K, hK, hBound⟩ :=
    exists_dfiEquation28_biMellin_line_bound_order
      hf hbox hφ hscale w hUQ (-(1 / 2)) (-(1 / 2)) 6
  refine ⟨K, hK, ?_⟩
  intro a b q hq0 ha hb hqQ h
  letI : NeZero q := hq0
  have hq : 0 < q := NeZero.pos q
  let qx := (dfiReducedModulus a q).denominator
  let qy := (dfiReducedModulus b q).denominator
  let E := dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q
  let M := dfiEquation28BiMajorant K 6 Q X Y a b q
  let Bnd := ‖(((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2)‖ *
    dfiDivisorThreeHalfMass ^ 2 *
      ((32 * qx * dfiArchimedeanScale qx ^ 2) *
        (32 * qy * dfiArchimedeanScale qy ^ 2) * M * dfiCauchyPlaneMass)
  have hLine := hBound a b q ha hb hq hqQ h
  have hBi : ∀ u v : ℝ,
      (1 + |u|) ^ 6 * (1 + |v|) ^ 6 *
        ‖dfiBiMellin E (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ M := by
    intro u v
    simpa [E, M, dfiEquation28BiMajorant] using hLine u v
  have hM : 0 ≤ M := by
    have hZero := hBi 0 0
    exact (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (norm_nonneg _)).trans hZero
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ Set.Icc (Y / b) (2 * Y / b) := by
    exact dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hXA : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) haR
  have hXAB : X / (a : ℝ) ≤ 2 * X / a :=
    (div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X])
  have hYC : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR
  have hYCD : Y / (b : ℝ) ≤ 2 * Y / b :=
    (div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y])
  have hEach (xBranch yBranch : DFIVoronoiDualBranch) :
      (∑' m : ℕ, ∑' n : ℕ,
        ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖) ≤ Bnd := by
    simpa only [Bnd] using
      tsum_tsum_norm_dfiEquation24DoubleDualMellinAmplitude_le_of_biMellin
        hE hXA hXAB hYC hYCD hSupport qx qy xBranch yBranch M hM hBi
  dsimp only [dfiEquation24DoubleDualMass]
  change (∑ yBranch : DFIVoronoiDualBranch,
      ∑ xBranch : DFIVoronoiDualBranch,
        ∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            qx xBranch qy yBranch E m n‖) ≤ 4 * Bnd
  calc
    _ ≤ ∑ _yBranch : DFIVoronoiDualBranch,
        ∑ _xBranch : DFIVoronoiDualBranch, Bnd := by
      apply Finset.sum_le_sum
      intro yBranch _hy
      apply Finset.sum_le_sum
      intro xBranch _hx
      exact hEach xBranch yBranch
    _ = 4 * Bnd := by
      have hcard : Fintype.card DFIVoronoiDualBranch = 2 := by decide
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        Nat.cast_ofNat]
      ring

end RiemannZeta.GuthMaynard
