import GafniTao.SharpPerronPsiAssembly
import GafniTao.LocalZeroCount

/-!
# The unit zero shell between the requested and selected heights

The good ordinate lies in `[T,T+1]`.  This module bounds exactly the zeros
introduced by moving the truncation from `T` to that ordinate, using four
literal half-open unit bins and analytic multiplicity.
-/

open Complex Set Finset
open scoped BigOperators

noncomputable section

namespace GafniTao

noncomputable def sharpPerronZeroShell (T R : ℝ) : Finset ℂ :=
  (zeroSet 0 R).filter (fun rho => T < |rho.im|)

theorem zeroSet_mono_height {T R : ℝ} (hTR : T ≤ R) :
    zeroSet 0 T ⊆ zeroSet 0 R := by
  intro rho hrho
  have hd := mem_zeroSet_zero_data hrho
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-R) R
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff]
  refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-R) R rho).2
    ⟨hd.1, hd.2.1, ?_, ?_⟩, hd.2.2.2.2⟩
  · linarith [hd.2.2.1]
  · linarith [hd.2.2.2.1]

theorem zeroSet_filter_abs_le_height
    {T R : ℝ} (_hT : 0 ≤ T) (hTR : T ≤ R) :
    (zeroSet 0 R).filter (fun rho => |rho.im| ≤ T) = zeroSet 0 T := by
  ext rho
  simp only [Finset.mem_filter]
  constructor
  · intro h
    have hd := mem_zeroSet_zero_data h.1
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-T) T
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff]
    refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-T) T rho).2
      ⟨hd.1, hd.2.1, ?_, ?_⟩, hd.2.2.2.2⟩
    · exact (abs_le.mp h.2).1
    · exact (abs_le.mp h.2).2
  · intro h
    refine ⟨zeroSet_mono_height hTR h, ?_⟩
    have hd := mem_zeroSet_zero_data h
    exact (abs_le).2 ⟨hd.2.2.1, hd.2.2.2.1⟩

theorem sum_zeroSet_eq_sum_shell_add
    {T R : ℝ} (hT : 0 ≤ T) (hTR : T ≤ R) (f : ℂ → ℂ) :
    (∑ rho ∈ zeroSet 0 R, f rho) =
      (∑ rho ∈ sharpPerronZeroShell T R, f rho) +
        ∑ rho ∈ zeroSet 0 T, f rho := by
  have hpart := Finset.sum_filter_add_sum_filter_not
    (zeroSet 0 R) (fun rho => T < |rho.im|) f
  have hcomp : (zeroSet 0 R).filter (fun rho => ¬T < |rho.im|) =
      zeroSet 0 T := by
    simpa only [not_lt] using zeroSet_filter_abs_le_height hT hTR
  calc
    (∑ rho ∈ zeroSet 0 R, f rho) =
        (∑ rho ∈ (zeroSet 0 R).filter (fun rho => T < |rho.im|), f rho) +
          ∑ rho ∈ (zeroSet 0 R).filter (fun rho => ¬T < |rho.im|), f rho :=
      hpart.symm
    _ = (∑ rho ∈ sharpPerronZeroShell T R, f rho) +
          ∑ rho ∈ zeroSet 0 T, f rho := by
      rw [sharpPerronZeroShell, hcomp]

private theorem sum_union_le_add (s t : Finset ℂ) (f : ℂ → ℕ) :
    (∑ z ∈ s ∪ t, f z) ≤ (∑ z ∈ s, f z) + ∑ z ∈ t, f z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      by_cases hs : a ∈ s
      · simp [ha, hs]
        omega
      · simp [ha, hs]
        omega

private theorem exp_two_le_eight : Real.exp 2 ≤ 8 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

private theorem ordinate_in_two_floor_bins
    {a t : ℝ} (ht : t ∈ Set.Icc a (a + 1)) :
    (((⌊a⌋ : ℤ) : ℝ) ≤ t ∧ t < ((⌊a⌋ : ℤ) : ℝ) + 1) ∨
      ((((⌊a⌋ : ℤ) : ℝ) + 1 ≤ t) ∧
        t < (((⌊a⌋ : ℤ) : ℝ) + 1) + 1) := by
  have hfloor : ((⌊a⌋ : ℤ) : ℝ) ≤ a := Int.floor_le a
  have haUpper : a < ((⌊a⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one a
  by_cases h : t < ((⌊a⌋ : ℤ) : ℝ) + 1
  · exact Or.inl ⟨hfloor.trans ht.1, h⟩
  · exact Or.inr ⟨le_of_not_gt h, by linarith [ht.2, haUpper]⟩

private noncomputable def sharpPerronShellBins (T : ℝ) : Finset ℂ :=
  let H := T + 2
  let zp : ℤ := ⌊T⌋
  let zn : ℤ := ⌊-T - 1⌋
  zeroLocalUnitBin 0 H zp ∪ zeroLocalUnitBin 0 H (zp + 1) ∪
    zeroLocalUnitBin 0 H zn ∪ zeroLocalUnitBin 0 H (zn + 1)

private theorem sharpPerronZeroShell_subset_bins
    {T R : ℝ} (_hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1)) :
    sharpPerronZeroShell T R ⊆ sharpPerronShellBins T := by
  intro rho hrho
  have hshell := Finset.mem_filter.mp hrho
  have hd := mem_zeroSet_zero_data hshell.1
  have hH : R ≤ T + 2 := by linarith [hR.2]
  have hrhoH := zeroSet_mono_height hH hshell.1
  have habsUpper : |rho.im| ≤ R := (abs_le).2 ⟨hd.2.2.1, hd.2.2.2.1⟩
  simp only [sharpPerronShellBins, Finset.mem_union, zeroLocalUnitBin,
    Finset.mem_filter]
  by_cases him : 0 ≤ rho.im
  · have ht : rho.im ∈ Set.Icc T (T + 1) := by
      rw [abs_of_nonneg him] at hshell habsUpper
      exact ⟨hshell.2.le, habsUpper.trans hR.2⟩
    rcases ordinate_in_two_floor_bins ht with hz | hz
    · exact Or.inl (Or.inl (Or.inl ⟨hrhoH, hz.1, hz.2⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hrhoH, by simpa using hz.1,
        by simpa using hz.2⟩))
  · have himNeg : rho.im < 0 := lt_of_not_ge him
    have ht : rho.im ∈ Set.Icc (-T - 1) ((-T - 1) + 1) := by
      rw [abs_of_neg himNeg] at hshell habsUpper
      constructor <;> linarith [hshell.2, habsUpper, hR.2]
    rcases ordinate_in_two_floor_bins ht with hz | hz
    · exact Or.inl (Or.inr ⟨hrhoH, hz.1, hz.2⟩)
    · exact Or.inr ⟨hrhoH, by simpa using hz.1, by simpa using hz.2⟩

/-- The selected-height shell contains only `O(log(T+2))` zeros, with
analytic multiplicity and an explicit factor four. -/
theorem sharpPerronZeroShell_multiplicity_le
    {T R : ℝ} (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1)) :
    ((∑ rho ∈ sharpPerronZeroShell T R,
        zeroMultiplicity rho : ℕ) : ℝ) ≤
      4 * globalLocalZeroLogConstant * Real.log (T + 2) := by
  let H : ℝ := T + 2
  let zp : ℤ := ⌊T⌋
  let zn : ℤ := ⌊-T - 1⌋
  let A := zeroLocalUnitBin 0 H zp
  let B := zeroLocalUnitBin 0 H (zp + 1)
  let C := zeroLocalUnitBin 0 H zn
  let D := zeroLocalUnitBin 0 H (zn + 1)
  have hH : max (Real.exp 2) 8 ≤ H := by
    rw [max_le_iff]
    exact ⟨exp_two_le_eight.trans (by linarith), by linarith⟩
  have hA := zeroLocalUnitBin_multiplicity_le_global_log 0 H zp (by norm_num) hH
  have hB := zeroLocalUnitBin_multiplicity_le_global_log 0 H (zp + 1) (by norm_num) hH
  have hC := zeroLocalUnitBin_multiplicity_le_global_log 0 H zn (by norm_num) hH
  have hD := zeroLocalUnitBin_multiplicity_le_global_log 0 H (zn + 1) (by norm_num) hH
  have hsubset : sharpPerronZeroShell T R ⊆ A ∪ B ∪ C ∪ D := by
    simpa [A, B, C, D, H, zp, zn, sharpPerronShellBins] using
      sharpPerronZeroShell_subset_bins hT hR
  have hNat :
      ∑ rho ∈ sharpPerronZeroShell T R, zeroMultiplicity rho ≤
        (∑ rho ∈ A, zeroMultiplicity rho) +
        (∑ rho ∈ B, zeroMultiplicity rho) +
        (∑ rho ∈ C, zeroMultiplicity rho) +
        (∑ rho ∈ D, zeroMultiplicity rho) := by
    calc
      _ ≤ ∑ rho ∈ A ∪ B ∪ C ∪ D, zeroMultiplicity rho :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
      _ ≤ ((∑ rho ∈ A, zeroMultiplicity rho) +
            (∑ rho ∈ B, zeroMultiplicity rho) +
            (∑ rho ∈ C, zeroMultiplicity rho)) +
            ∑ rho ∈ D, zeroMultiplicity rho := by
        refine (sum_union_le_add (A ∪ B ∪ C) D zeroMultiplicity).trans ?_
        gcongr
        refine (sum_union_le_add (A ∪ B) C zeroMultiplicity).trans ?_
        gcongr
        exact sum_union_le_add A B zeroMultiplicity
      _ = _ := by ring
  have hReal :
      ((∑ rho ∈ sharpPerronZeroShell T R,
          zeroMultiplicity rho : ℕ) : ℝ) ≤
        ((∑ rho ∈ A, zeroMultiplicity rho : ℕ) : ℝ) +
        ((∑ rho ∈ B, zeroMultiplicity rho : ℕ) : ℝ) +
        ((∑ rho ∈ C, zeroMultiplicity rho : ℕ) : ℝ) +
        ((∑ rho ∈ D, zeroMultiplicity rho : ℕ) : ℝ) := by
    exact_mod_cast hNat
  calc
    _ ≤ ((∑ rho ∈ A, zeroMultiplicity rho : ℕ) : ℝ) +
        ((∑ rho ∈ B, zeroMultiplicity rho : ℕ) : ℝ) +
        ((∑ rho ∈ C, zeroMultiplicity rho : ℕ) : ℝ) +
        ((∑ rho ∈ D, zeroMultiplicity rho : ℕ) : ℝ) := hReal
    _ ≤ globalLocalZeroLogConstant * Real.log H +
        globalLocalZeroLogConstant * Real.log H +
        globalLocalZeroLogConstant * Real.log H +
        globalLocalZeroLogConstant * Real.log H := by gcongr
    _ = 4 * globalLocalZeroLogConstant * Real.log (T + 2) := by
      dsimp [H]
      ring

/-- The literal contribution of the zeros introduced by replacing the
requested cutoff `T` by a selected cutoff `R`. -/
noncomputable def sharpPerronShellZeroSum (T R y : ℝ) : ℂ :=
  ∑ rho ∈ sharpPerronZeroShell T R,
    (zeroMultiplicity rho : ℂ) * ((y : ℂ) ^ rho / rho)

private theorem norm_shell_zero_term_le
    {T R y : ℝ} (hT : 0 < T) (hy : 1 ≤ y) {rho : ℂ}
    (hrho : rho ∈ sharpPerronZeroShell T R) :
    ‖(zeroMultiplicity rho : ℂ) * ((y : ℂ) ^ rho / rho)‖ ≤
      (zeroMultiplicity rho : ℝ) * (y / T) := by
  have hshell := Finset.mem_filter.mp hrho
  have hd := mem_zeroSet_zero_data hshell.1
  have hyPos : 0 < y := zero_lt_one.trans_le hy
  have hnormRho : T ≤ ‖rho‖ := by
    calc
      T ≤ |rho.im| := hshell.2.le
      _ ≤ ‖rho‖ := Complex.abs_im_le_norm rho
  have hpow : y ^ rho.re ≤ y := by
    calc
      y ^ rho.re ≤ y ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy hd.2.1
      _ = y := Real.rpow_one y
  rw [norm_mul, RCLike.norm_natCast, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
  gcongr

/-- The selected-height zero shell costs `O(y log(T+2)/T)`, with the
literal multiplicity-weighted zero terms and an explicit constant. -/
theorem norm_sharpPerronShellZeroSum_le
    {T R y : ℝ} (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1))
    (hy : 1 ≤ y) :
    ‖sharpPerronShellZeroSum T R y‖ ≤
      4 * globalLocalZeroLogConstant * Real.log (T + 2) * (y / T) := by
  unfold sharpPerronShellZeroSum
  calc
    ‖∑ rho ∈ sharpPerronZeroShell T R,
        (zeroMultiplicity rho : ℂ) * ((y : ℂ) ^ rho / rho)‖
        ≤ ∑ rho ∈ sharpPerronZeroShell T R,
            ‖(zeroMultiplicity rho : ℂ) * ((y : ℂ) ^ rho / rho)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ sharpPerronZeroShell T R,
          (zeroMultiplicity rho : ℝ) * (y / T) := by
      apply Finset.sum_le_sum
      intro rho hrho
      exact norm_shell_zero_term_le (by linarith) hy hrho
    _ = ((∑ rho ∈ sharpPerronZeroShell T R,
          zeroMultiplicity rho : ℕ) : ℝ) * (y / T) := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ (4 * globalLocalZeroLogConstant * Real.log (T + 2)) *
          (y / T) := by
      gcongr
      exact sharpPerronZeroShell_multiplicity_le hT hR
    _ = 4 * globalLocalZeroLogConstant * Real.log (T + 2) * (y / T) := by
      ring

/-- Exact algebraic transfer of the sharp explicit-formula error from the
selected cutoff back to the requested cutoff. -/
theorem sharpPsiTruncationError_eq_selected_sub_shell
    {T R : ℝ} (hT : 0 ≤ T) (hTR : T ≤ R) (y : ℝ) :
    sharpPsiTruncationError T y =
      sharpPsiTruncationError R y - sharpPerronShellZeroSum T R y := by
  unfold sharpPsiTruncationError truncatedPsiZeroSum sharpPerronShellZeroSum
  rw [sum_zeroSet_eq_sum_shell_add hT hTR]
  ring

/-- The selected-height contour estimate, transferred back to the literal
requested cutoff.  This still uses the half-integral Perron evaluation point;
the endpoint-uniform arithmetic transfer is handled in the next module. -/
theorem exists_norm_sharpPsiTruncationError_halfPoint_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T x : ℝ}, 8 ≤ T →
      2 ≤ sharpPerronHalfPoint x → T ≤ sharpPerronHalfPoint x →
      ‖sharpPsiTruncationError T (sharpPerronHalfPoint x)‖ ≤
        C * sharpPerronHalfPoint x *
          Real.log (sharpPerronHalfPoint x) ^ 2 / T := by
  obtain ⟨C, hC, hselected⟩ :=
    exists_good_height_norm_sharpPsiTruncationError_le
  let D : ℝ := C + 16 * globalLocalZeroLogConstant
  refine ⟨D, by
    dsimp [D]
    exact add_pos hC (mul_pos (by norm_num) globalLocalZeroLogConstant_pos), ?_⟩
  intro T x hT hy hTy
  let y := sharpPerronHalfPoint x
  obtain ⟨R, hR, hRbound⟩ := hselected hT hy hTy
  change ‖sharpPsiTruncationError R y‖ ≤
    C * y * Real.log y ^ 2 / T at hRbound
  change ‖sharpPsiTruncationError T y‖ ≤
    D * y * Real.log y ^ 2 / T
  have hyPos : 0 < y := by dsimp [y]; linarith
  have hTpos : 0 < T := by linarith
  have hlogTy : Real.log (T + 2) ≤ 2 * Real.log y := by
    have hT2pos : 0 < T + 2 := by linarith
    have hT2y2 : T + 2 ≤ y ^ 2 := by
      nlinarith [sq_nonneg (y - 1)]
    calc
      Real.log (T + 2) ≤ Real.log (y ^ 2) :=
        Real.log_le_log hT2pos hT2y2
      _ = 2 * Real.log y := by
        rw [show y ^ 2 = y ^ (2 : ℝ) by
          exact (Real.rpow_natCast y 2).symm, Real.log_rpow hyPos]
  have hlogHalf : (1 / 2 : ℝ) ≤ Real.log y := by
    have hlogTwo : Real.log 2 ≤ Real.log y :=
      Real.log_le_log (by norm_num) hy
    linarith [Real.log_two_gt_d9]
  have hlogAbsorb : Real.log y ≤ 2 * Real.log y ^ 2 := by
    nlinarith [sq_nonneg (Real.log y)]
  have hshell := norm_sharpPerronShellZeroSum_le (y := y) hT hR (by
    change 2 ≤ y at hy
    exact (by norm_num : (1 : ℝ) ≤ 2).trans hy)
  have hshell' : ‖sharpPerronShellZeroSum T R y‖ ≤
      16 * globalLocalZeroLogConstant * y * Real.log y ^ 2 / T := by
    calc
      _ ≤ 4 * globalLocalZeroLogConstant * Real.log (T + 2) *
          (y / T) := hshell
      _ ≤ 4 * globalLocalZeroLogConstant * (2 * Real.log y) *
          (y / T) := by
        have hcoeff : 0 ≤ 4 * globalLocalZeroLogConstant :=
          mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogTy hcoeff)
          (div_nonneg hyPos.le hTpos.le)
      _ ≤ 16 * globalLocalZeroLogConstant * y * Real.log y ^ 2 / T := by
        have hlocal := globalLocalZeroLogConstant_pos.le
        have hy0 := hyPos.le
        have hT0 := hTpos.le
        calc
          4 * globalLocalZeroLogConstant * (2 * Real.log y) * (y / T) =
              (8 * globalLocalZeroLogConstant * y / T) * Real.log y := by ring
          _ ≤ (8 * globalLocalZeroLogConstant * y / T) *
                (2 * Real.log y ^ 2) := by
            gcongr
          _ = 16 * globalLocalZeroLogConstant * y * Real.log y ^ 2 / T := by
            ring
  rw [sharpPsiTruncationError_eq_selected_sub_shell (by linarith [hT]) hR.1]
  calc
    ‖sharpPsiTruncationError R y - sharpPerronShellZeroSum T R y‖ ≤
        ‖sharpPsiTruncationError R y‖ +
          ‖sharpPerronShellZeroSum T R y‖ := norm_sub_le _ _
    _ ≤ C * y * Real.log y ^ 2 / T +
          16 * globalLocalZeroLogConstant * y * Real.log y ^ 2 / T :=
      add_le_add hRbound hshell'
    _ = D * y * Real.log y ^ 2 / T := by
      dsimp [D]
      ring

end GafniTao
