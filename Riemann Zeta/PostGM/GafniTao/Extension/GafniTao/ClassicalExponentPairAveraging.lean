import RiemannZeta.GuthMaynard.VanDerCorput

/-!
# Row-averaged finite Weyl differencing

The second application of van der Corput's `A` process must retain the
average over shift distances.  Replacing every off-diagonal correlation by
their total sum loses one full power of the shift length and cannot recover
the classical `A²B(0,1)` exponent pair.  This file records the exact finite
row-sum form of the same Cauchy--Schwarz argument.
-/

open Complex Finset
open scoped BigOperators InnerProductSpace

namespace GafniTao

noncomputable section

/-- Symmetric natural-number distance, kept local to the isolated extension. -/
def finiteShiftDistance (h k : ℕ) : ℕ := (h - k) + (k - h)

/-- Finite Weyl differencing with an off-diagonal bound averaged in each
row.  The hypothesis exposes the literal real inner products produced by
Cauchy--Schwarz; applications may dominate them by norms of complex
correlation sums. -/
theorem finite_weyl_differencing_row
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (r : Finset κ) (b : ι → κ → ℂ) (S : ℂ) (A B : ℝ)
    (hshift : ∀ h ∈ r, ∑ n ∈ s, b n h = S)
    (hdiag : ∀ h ∈ r, ∑ n ∈ s, ‖b n h‖ ^ 2 ≤ A)
    (hrow : ∀ h ∈ r,
      ∑ k ∈ r.filter (fun k => k ≠ h),
          |∑ n ∈ s, ⟪b n h, b n k⟫_ℝ| ≤ B) :
    (r.card : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
      (s.card : ℝ) * ((r.card : ℝ) * A + (r.card : ℝ) * B) := by
  let u : ι → ℂ := fun n => ∑ h ∈ r, b n h
  have hsum : ∑ n ∈ s, u n = r.card • S := by
    calc
      ∑ n ∈ s, u n = ∑ h ∈ r, ∑ n ∈ s, b n h := by
        simp only [u]
        rw [sum_comm]
      _ = ∑ _h ∈ r, S := by
        apply Finset.sum_congr rfl
        intro h hh
        exact hshift h hh
      _ = r.card • S := by simp
  have hcs :=
    RiemannZeta.GuthMaynard.norm_sum_sq_le_card_mul_sum_norm_sq s u
  have hexpand :
      ∑ n ∈ s, ‖u n‖ ^ 2 =
        ∑ h ∈ r, ∑ k ∈ r, ∑ n ∈ s, ⟪b n h, b n k⟫_ℝ := by
    simp only [u, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
    rw [sum_comm]
    apply Finset.sum_congr rfl
    intro h _hh
    rw [sum_comm]
    apply Finset.sum_congr rfl
    intro k _hk
    apply Finset.sum_congr rfl
    intro n _hn
    exact real_inner_comm _ _
  have hrowBound : ∀ h ∈ r,
      ∑ k ∈ r, ∑ n ∈ s, ⟪b n h, b n k⟫_ℝ ≤ A + B := by
    intro h hh
    rw [← Finset.sum_filter_add_sum_filter_not r (fun k => k = h)]
    have hdiagPart :
        ∑ k ∈ r.filter (fun k => k = h),
            ∑ n ∈ s, ⟪b n h, b n k⟫_ℝ ≤ A := by
      have hfilter : r.filter (fun k => k = h) = {h} := by
        ext k
        simp only [mem_filter, mem_singleton]
        constructor
        · intro hk
          exact hk.2
        · intro hk
          subst k
          exact ⟨hh, rfl⟩
      rw [hfilter]
      simp only [sum_singleton]
      calc
        ∑ n ∈ s, ⟪b n h, b n h⟫_ℝ =
            ∑ n ∈ s, ‖b n h‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro n _hn
          exact real_inner_self_eq_norm_sq (b n h)
        _ ≤ A := hdiag h hh
    have hoffPart :
        ∑ k ∈ r.filter (fun k => ¬k = h),
            ∑ n ∈ s, ⟪b n h, b n k⟫_ℝ ≤ B := by
      calc
        ∑ k ∈ r.filter (fun k => ¬k = h),
              ∑ n ∈ s, ⟪b n h, b n k⟫_ℝ ≤
            ∑ k ∈ r.filter (fun k => k ≠ h),
              |∑ n ∈ s, ⟪b n h, b n k⟫_ℝ| := by
          apply Finset.sum_le_sum
          intro k hk
          exact le_abs_self _
        _ ≤ B := hrow h hh
    linarith
  have hcorrelation :
      ∑ h ∈ r, ∑ k ∈ r, ∑ n ∈ s, ⟪b n h, b n k⟫_ℝ ≤
        (r.card : ℝ) * A + (r.card : ℝ) * B := by
    calc
      ∑ h ∈ r, ∑ k ∈ r, ∑ n ∈ s, ⟪b n h, b n k⟫_ℝ ≤
          ∑ _h ∈ r, (A + B) :=
        Finset.sum_le_sum fun h hh => hrowBound h hh
      _ = (r.card : ℝ) * A + (r.card : ℝ) * B := by
        simp
  rw [hsum, RCLike.norm_nsmul ℂ, nsmul_eq_mul, hexpand] at hcs
  calc
    (r.card : ℝ) ^ 2 * ‖S‖ ^ 2 =
        ((r.card : ℝ) * ‖S‖) ^ 2 := by ring
    _ ≤ (s.card : ℝ) *
        (∑ h ∈ r, ∑ k ∈ r, ∑ n ∈ s, ⟪b n h, b n k⟫_ℝ) := hcs
    _ ≤ (s.card : ℝ) *
        ((r.card : ℝ) * A + (r.card : ℝ) * B) := by
      exact mul_le_mul_of_nonneg_left hcorrelation
        (Nat.cast_nonneg s.card)

/-- Interval form of the row-averaged inequality for zero-padded complex
translates.  This is the reusable outer `A`-process interface. -/
theorem interval_weyl_differencing_row_complex
    (a : ℤ → ℂ) (N H : ℕ) (B : ℝ)
    (ha : ∀ n ∈ Finset.Ico (0 : ℤ) N, ‖a n‖ ≤ 1)
    (hrow : ∀ h ∈ Finset.range H,
      ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
          ‖∑ n ∈ Finset.Ico (-(H : ℤ)) N,
            star (RiemannZeta.GuthMaynard.paddedShift a N n h) *
              RiemannZeta.GuthMaynard.paddedShift a N n k‖ ≤ B) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : ℤ) N, a n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) * ((H : ℝ) * N + (H : ℝ) * B) := by
  let b : ℤ → ℕ → ℂ := fun n h =>
    RiemannZeta.GuthMaynard.paddedShift a N n h
  have hdiag : ∀ h ∈ Finset.range H,
      ∑ n ∈ Finset.Ico (-(H : ℤ)) N, ‖b n h‖ ^ 2 ≤ (N : ℝ) := by
    intro h hh
    dsimp only [b]
    rw [RiemannZeta.GuthMaynard.sum_norm_sq_paddedShift_eq
      a N H h (Finset.mem_range.mp hh)]
    calc
      ∑ m ∈ Finset.Ico (0 : ℤ) N, ‖a m‖ ^ 2 ≤
          ∑ _m ∈ Finset.Ico (0 : ℤ) N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        nlinarith [norm_nonneg (a m), ha m hm]
      _ = (N : ℝ) := by simp [Int.card_Ico]
  have hrowReal : ∀ h ∈ Finset.range H,
      ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
          |∑ n ∈ Finset.Ico (-(H : ℤ)) N, ⟪b n h, b n k⟫_ℝ| ≤ B := by
    intro h hh
    calc
      ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
            |∑ n ∈ Finset.Ico (-(H : ℤ)) N, ⟪b n h, b n k⟫_ℝ| ≤
          ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
            ‖∑ n ∈ Finset.Ico (-(H : ℤ)) N,
              star (b n h) * b n k‖ := by
        apply Finset.sum_le_sum
        intro k hk
        let z := ∑ n ∈ Finset.Ico (-(H : ℤ)) N,
          star (b n h) * b n k
        have hre :
            (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
              ⟪b n h, b n k⟫_ℝ) = z.re := by
          dsimp only [z]
          simp only [Complex.re_sum]
          apply Finset.sum_congr rfl
          intro n _hn
          simp
          ring
        rw [hre]
        exact abs_re_le_norm z
      _ ≤ B := by simpa only [b] using hrow h hh
  have hraw := finite_weyl_differencing_row
    (Finset.Ico (-(H : ℤ)) (N : ℤ)) (Finset.range H) b
    (∑ n ∈ Finset.Ico (0 : ℤ) N, a n) (N : ℝ) B
    (fun h hh => RiemannZeta.GuthMaynard.sum_paddedShift_eq
      a N H h (Finset.mem_range.mp hh)) hdiag hrowReal
  have hcard : ((Finset.Ico (-(H : ℤ)) (N : ℤ)).card : ℝ) = N + H := by
    norm_num [Int.card_Ico]
    norm_cast
  simpa only [Finset.card_range, Nat.cast_add, hcard] using hraw

/-- For a fixed shift, every positive distance below `H` occurs at most
twice.  This is the exact combinatorial multiplicity behind the averaged
`A` process. -/
theorem sum_shiftDistance_le_two_mul_sum
    (C : ℕ → ℝ) (hC : ∀ d, 0 ≤ C d) {H h : ℕ} (hh : h < H) :
    ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
        C (finiteShiftDistance h k) ≤
      2 * ∑ d ∈ Finset.Icc 1 (H - 1), C d := by
  let L := (Finset.range H).filter (fun k => k < h)
  let R := (Finset.range H).filter (fun k => h < k)
  have hsplit :
      (Finset.range H).filter (fun k => k ≠ h) = L ∪ R := by
    ext k
    simp only [L, R, mem_filter, mem_range, mem_union]
    omega
  have hdisjoint : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro k hkL hkR
    simp only [L, mem_filter] at hkL
    simp only [R, mem_filter] at hkR
    omega
  rw [hsplit, Finset.sum_union hdisjoint]
  have hleftImage : L.image (fun k => h - k) ⊆ Finset.Icc 1 (H - 1) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨k, hkL, rfl⟩ := hd
    simp only [L, mem_filter, mem_range] at hkL
    apply Finset.mem_Icc.mpr
    omega
  have hrightImage : R.image (fun k => k - h) ⊆ Finset.Icc 1 (H - 1) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨k, hkR, rfl⟩ := hd
    simp only [R, mem_filter, mem_range] at hkR
    apply Finset.mem_Icc.mpr
    omega
  have hleftInjective : Set.InjOn (fun k : ℕ => h - k) L := by
    intro a ha b hb hab
    simp only [L, mem_coe, mem_filter] at ha hb
    change h - a = h - b at hab
    omega
  have hrightInjective : Set.InjOn (fun k : ℕ => k - h) R := by
    intro a ha b hb hab
    simp only [R, mem_coe, mem_filter] at ha hb
    change a - h = b - h at hab
    omega
  have hleftRewrite :
      ∑ k ∈ L, C (finiteShiftDistance h k) =
        ∑ d ∈ L.image (fun k => h - k), C d := by
    rw [Finset.sum_image hleftInjective]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [L, mem_filter] at hk
    unfold finiteShiftDistance
    rw [Nat.sub_eq_zero_of_le hk.2.le]
    simp
  have hrightRewrite :
      ∑ k ∈ R, C (finiteShiftDistance h k) =
        ∑ d ∈ R.image (fun k => k - h), C d := by
    rw [Finset.sum_image hrightInjective]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [R, mem_filter] at hk
    unfold finiteShiftDistance
    rw [Nat.sub_eq_zero_of_le hk.2.le]
    simp
  rw [hleftRewrite, hrightRewrite]
  have hleftLe : ∑ d ∈ L.image (fun k => h - k), C d ≤
      ∑ d ∈ Finset.Icc 1 (H - 1), C d :=
    Finset.sum_le_sum_of_subset_of_nonneg hleftImage
      (fun d _hd _ => hC d)
  have hrightLe : ∑ d ∈ R.image (fun k => k - h), C d ≤
      ∑ d ∈ Finset.Icc 1 (H - 1), C d :=
    Finset.sum_le_sum_of_subset_of_nonneg hrightImage
      (fun d _hd _ => hC d)
  linarith

#print axioms finite_weyl_differencing_row
#print axioms interval_weyl_differencing_row_complex
#print axioms sum_shiftDistance_le_two_mul_sum

end

end GafniTao
