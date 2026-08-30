import RiemannZeta.GuthMaynard.FiniteDensityTransfer

open Complex Finset Filter Topology
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Finite classical Type-I/Type-II dichotomy

This module formalizes the finite detector split in ANTEDB Lemma 11.5.
The Type-I branch is a long ordinary-zeta tail.  The Type-II branch is the
genuinely short tail obtained by multiplying a short zeta sum by a short
Möbius polynomial.  Medium reflection, the terminal estimate, and endpoint
exponent assembly remain downstream of the certificate constructed here.
-/

/-- The sharp finite partial-zeta sum through `A`. -/
noncomputable def classicalZetaPartialSum (A : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 A, (n : ℂ) ^ (-s)

/-- The ordinary-zeta tail strictly above `Y` and through `A`. -/
noncomputable def classicalZetaLongTail (Y A : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc Y A, (n : ℂ) ^ (-s)

/-- Finite support of the ordinary Type-I tail. -/
noncomputable def classicalZetaLongTailSupport (Y A : ℕ) : Finset ℕ :=
  Ioc Y A

theorem classicalZetaLongTail_eq_finiteDirichletSeries
    (Y A : ℕ) (s : ℂ) :
    classicalZetaLongTail Y A s =
      finiteDirichletSeries (classicalZetaLongTailSupport Y A)
        (fun _n => 1) s := by
  simp only [classicalZetaLongTail, classicalZetaLongTailSupport,
    finiteDirichletSeries, one_mul]

theorem classicalZetaLongTailSupport_pos (Y A n : ℕ)
    (hn : n ∈ classicalZetaLongTailSupport Y A) : 0 < n := by
  rw [classicalZetaLongTailSupport, Finset.mem_Ioc] at hn
  omega

/-- The ordinary Type-I coefficient mass is at most its upper cutoff. -/
theorem classicalZetaLongTail_mass_le (Y A : ℕ) :
    finiteDirichletMass (classicalZetaLongTailSupport Y A) (fun _n => 1) ≤ A := by
  unfold finiteDirichletMass classicalZetaLongTailSupport
  simp only [norm_one, sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (show (Ioc Y A).card ≤ A by simp)

/-- Fixed-line coefficients of the ordinary Type-I tail, extended by zero
beyond the sharp upper cutoff. -/
noncomputable def classicalZetaLongLineCoeff
    (A : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  if n ≤ A then (n : ℂ) ^ (-(σ : ℂ)) else 0

theorem classicalZetaLongLineCoeff_term
    (A n : ℕ) (σ t : ℝ) (hn : 0 < n) (hnA : n ≤ A) :
    classicalZetaLongLineCoeff A σ n * (n : ℂ) ^ (-(t : ℂ) * I) =
      (n : ℂ) ^ (-((σ : ℂ) + I * (t : ℂ))) := by
  rw [classicalZetaLongLineCoeff, if_pos hnA,
    ← Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
  congr 2
  ring

/-- The fixed-line Type-I tail is one wide polynomial starting at `Y`. -/
theorem classicalZetaLongTail_eq_wideDirichletPoly
    (Y A : ℕ) (σ t : ℝ) (hY : 1 ≤ Y) :
    classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ)) =
      wideDirichletPoly Y (Nat.clog 2 A)
        (classicalZetaLongLineCoeff A σ) t := by
  have hCover : A ≤ 2 ^ Nat.clog 2 A :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mp le_rfl
  have hUpper : A ≤ 2 ^ Nat.clog 2 A * Y := by
    calc
      A ≤ 2 ^ Nat.clog 2 A := hCover
      _ ≤ 2 ^ Nat.clog 2 A * Y :=
        Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hSubset : Finset.Ioc Y A ⊆
      Finset.Ioc Y (2 ^ Nat.clog 2 A * Y) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans hUpper⟩
  rw [classicalZetaLongTail, wideDirichletPoly]
  have hExtend :
      (∑ n ∈ Finset.Ioc Y A,
          classicalZetaLongLineCoeff A σ n * (n : ℂ) ^ (-(t : ℂ) * I)) =
        ∑ n ∈ Finset.Ioc Y (2 ^ Nat.clog 2 A * Y),
          classicalZetaLongLineCoeff A σ n * (n : ℂ) ^ (-(t : ℂ) * I) := by
    apply Finset.sum_subset hSubset
    intro n hnBig hnSmall
    have hnA : A < n := by
      by_contra h
      exact hnSmall (Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hnBig).1, Nat.le_of_not_gt h⟩)
    rw [classicalZetaLongLineCoeff, if_neg (by omega), zero_mul]
  rw [← hExtend]
  apply Finset.sum_congr rfl
  intro n hn
  exact (classicalZetaLongLineCoeff_term A n σ t
    (lt_of_le_of_lt (Nat.zero_le Y) (Finset.mem_Ioc.mp hn).1)
    (Finset.mem_Ioc.mp hn).2).symm

/-- A fixed-line Type-I tail has a dyadic block carrying its average share. -/
theorem exists_classicalZetaLong_large_dyadic_block
    (Y A : ℕ) (σ t V : ℝ) (hY : 1 ≤ Y) (hA : 1 < A)
    (hLarge : V ≤
      ‖classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ))‖) :
    ∃ r ∈ Finset.range (Nat.clog 2 A),
      V / Nat.clog 2 A ≤
        ‖dirichletPoly (2 ^ r * Y)
          (classicalZetaLongLineCoeff A σ) t‖ := by
  have hk : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
  apply exists_large_dyadic_block Y (Nat.clog 2 A)
    (classicalZetaLongLineCoeff A σ) t V hk
  rw [← classicalZetaLongTail_eq_wideDirichletPoly Y A σ t hY]
  exact hLarge

/-- Splitting a finite zeta sum at `Y` is an exact identity. -/
theorem classicalZetaPartialSum_eq_short_add_long
    (Y A : ℕ) (s : ℂ) (hYA : Y ≤ A) :
    classicalZetaPartialSum A s =
      classicalZetaPartialSum Y s + classicalZetaLongTail Y A s := by
  have hUnion : Finset.Icc 1 A = Finset.Icc 1 Y ∪ Finset.Ioc Y A := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [classicalZetaPartialSum, classicalZetaPartialSum,
    classicalZetaLongTail, hUnion, sum_union]
  rw [disjoint_left]
  intro n hnShort hnLong
  exact (not_lt_of_ge (Finset.mem_Icc.mp hnShort).2)
    (Finset.mem_Ioc.mp hnLong).1

/-- Exact finite Type-I/Type-II alternative.

If the full zeta sum is small, then either the short zeta sum is large and
the complementary ordinary-zeta tail is large, or the short sum is small.
In the latter case exact Möbius cancellation makes the short convolution
tail close to `-1`.  The theorem deliberately exposes the error `e`, split
threshold `q`, and mollifier bound `B`; the native power-scale specialization
is proved separately. -/
theorem classical_typeI_or_typeII_of_full_sum_small
    (A Y X : ℕ) (s : ℂ) (e q B : ℝ)
    (hY : 1 ≤ Y) (hX : 1 ≤ X)
    (hYA : Y ≤ A) (hXY : X ≤ Y)
    (hq : 0 ≤ q)
    (hFull : ‖classicalZetaPartialSum A s‖ ≤ e)
    (hMollifier : ‖zetaMollifier X s‖ ≤ B) :
    q - e ≤ ‖classicalZetaLongTail Y A s‖ ∨
      1 - q * B ≤ ‖sharpMollifiedTail Y X s‖ := by
  by_cases hShort : q ≤ ‖classicalZetaPartialSum Y s‖
  · left
    have hSplit := classicalZetaPartialSum_eq_short_add_long Y A s hYA
    have hTriangle :
        ‖classicalZetaPartialSum Y s‖ ≤
          ‖classicalZetaPartialSum A s‖ + ‖classicalZetaLongTail Y A s‖ := by
      calc
        ‖classicalZetaPartialSum Y s‖ =
            ‖classicalZetaPartialSum A s - classicalZetaLongTail Y A s‖ := by
          rw [hSplit]
          ring_nf
        _ ≤ ‖classicalZetaPartialSum A s‖ + ‖classicalZetaLongTail Y A s‖ :=
          norm_sub_le _ _
    linarith
  · right
    have hShort' : ‖classicalZetaPartialSum Y s‖ ≤ q :=
      (lt_of_not_ge hShort).le
    have hProductBound :
        ‖classicalZetaPartialSum Y s * zetaMollifier X s‖ ≤ q * B := by
      rw [norm_mul]
      exact mul_le_mul hShort' hMollifier (norm_nonneg _) hq
    have hProductIdentity :
        classicalZetaPartialSum Y s * zetaMollifier X s =
          1 + sharpMollifiedTail Y X s := by
      simpa only [classicalZetaPartialSum, sharpMollifiedTail_apply] using
        zetaPartialSum_mul_zetaMollifier_eq_one_add_tail Y X s hY hX hXY
    have hTriangle :
        (1 : ℝ) ≤
          ‖classicalZetaPartialSum Y s * zetaMollifier X s‖ +
            ‖sharpMollifiedTail Y X s‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖classicalZetaPartialSum Y s * zetaMollifier X s -
              sharpMollifiedTail Y X s‖ := by
          rw [hProductIdentity]
          ring_nf
        _ ≤ ‖classicalZetaPartialSum Y s * zetaMollifier X s‖ +
              ‖sharpMollifiedTail Y X s‖ := norm_sub_le _ _
    linarith

theorem classical_typeI_of_short_sum_large
    (A Y : ℕ) (s : ℂ) (e q : ℝ) (hYA : Y ≤ A)
    (hFull : ‖classicalZetaPartialSum A s‖ ≤ e)
    (hShort : q ≤ ‖classicalZetaPartialSum Y s‖) :
    q - e ≤ ‖classicalZetaLongTail Y A s‖ := by
  have hSplit := classicalZetaPartialSum_eq_short_add_long Y A s hYA
  have hTriangle :
      ‖classicalZetaPartialSum Y s‖ ≤
        ‖classicalZetaPartialSum A s‖ + ‖classicalZetaLongTail Y A s‖ := by
    calc
      ‖classicalZetaPartialSum Y s‖ =
          ‖classicalZetaPartialSum A s - classicalZetaLongTail Y A s‖ := by
        rw [hSplit]
        ring_nf
      _ ≤ ‖classicalZetaPartialSum A s‖ + ‖classicalZetaLongTail Y A s‖ :=
        norm_sub_le _ _
  linarith

theorem classical_typeII_of_short_sum_small
    (Y X : ℕ) (s : ℂ) (q B : ℝ)
    (hY : 1 ≤ Y) (hX : 1 ≤ X) (hXY : X ≤ Y)
    (hq : 0 ≤ q)
    (hShort : ‖classicalZetaPartialSum Y s‖ ≤ q)
    (hMollifier : ‖zetaMollifier X s‖ ≤ B) :
    1 - q * B ≤ ‖sharpMollifiedTail Y X s‖ := by
  have hProductBound :
      ‖classicalZetaPartialSum Y s * zetaMollifier X s‖ ≤ q * B := by
    rw [norm_mul]
    exact mul_le_mul hShort hMollifier (norm_nonneg _) hq
  have hProductIdentity :
      classicalZetaPartialSum Y s * zetaMollifier X s =
        1 + sharpMollifiedTail Y X s := by
    simpa only [classicalZetaPartialSum, sharpMollifiedTail_apply] using
      zetaPartialSum_mul_zetaMollifier_eq_one_add_tail Y X s hY hX hXY
  have hTriangle :
      (1 : ℝ) ≤
        ‖classicalZetaPartialSum Y s * zetaMollifier X s‖ +
          ‖sharpMollifiedTail Y X s‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖classicalZetaPartialSum Y s * zetaMollifier X s -
            sharpMollifiedTail Y X s‖ := by
        rw [hProductIdentity]
        ring_nf
      _ ≤ ‖classicalZetaPartialSum Y s * zetaMollifier X s‖ +
            ‖sharpMollifiedTail Y X s‖ := norm_sub_le _ _
  linarith

/-- Convenient constant-threshold consequence used by the native scale
specialization. -/
theorem classical_typeI_or_typeII_quantitative
    (A Y X : ℕ) (s : ℂ) (q B : ℝ)
    (hY : 1 ≤ Y) (hX : 1 ≤ X)
    (hYA : Y ≤ A) (hXY : X ≤ Y)
    (hq : 0 ≤ q)
    (hFull : ‖classicalZetaPartialSum A s‖ ≤ q / 2)
    (hMollifier : ‖zetaMollifier X s‖ ≤ B)
    (hQB : q * B ≤ 1 / 4) :
    q / 2 ≤ ‖classicalZetaLongTail Y A s‖ ∨
      3 / 4 ≤ ‖sharpMollifiedTail Y X s‖ := by
  rcases classical_typeI_or_typeII_of_full_sum_small A Y X s
      (q / 2) q B hY hX hYA hXY hq hFull hMollifier with hI | hII
  · left
    convert hI using 1
    ring
  · right
    linarith

/-- On the closed right half-plane the crude length bound suffices for the
short Möbius polynomial. -/
theorem norm_zetaMollifier_le_length
    (X : ℕ) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖zetaMollifier X s‖ ≤ (X : ℝ) := by
  refine (norm_zetaMollifier_le_sum_rpow X s).trans ?_
  calc
    (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-s.re)) ≤
        ∑ _n ∈ Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (Finset.mem_Icc.mp hn).1) (by linarith)
    _ = (X : ℝ) := by simp

/-- Zero-specialized finite dichotomy with every scale error left as an
explicit numerical inequality.  The subsequent eventual-scale lemma
discharges `hError` and `hShortProduct` for power cutoffs. -/
theorem zeta_zero_classical_typeI_or_typeII
    {σ T : ℝ} {ρ : ℂ} (Y X : ℕ) (q : ℝ)
    (hT : 3 / 4 ≤ T)
    (hρmem : ρ ∈ zerosInRect σ 1 T (2 * T))
    (hσ : 0 < σ) (hq : 0 ≤ q)
    (hY : 1 ≤ Y) (hX : 1 ≤ X)
    (hYA : Y ≤ ⌊sharpZetaCutoff T⌋₊) (hXY : X ≤ Y)
    (hError : 149 * sharpZetaCutoff T ^ (-ρ.re) ≤ q / 2)
    (hShortProduct : q * (X : ℝ) ≤ 1 / 4) :
    q / 2 ≤
        ‖classicalZetaLongTail Y ⌊sharpZetaCutoff T⌋₊ ρ‖ ∨
      3 / 4 ≤ ‖sharpMollifiedTail Y X ρ‖ := by
  have hFull :
      ‖classicalZetaPartialSum ⌊sharpZetaCutoff T⌋₊ ρ‖ ≤ q / 2 := by
    have hSharp :
        ‖classicalZetaPartialSum ⌊sharpZetaCutoff T⌋₊ ρ‖ ≤
          149 * sharpZetaCutoff T ^ (-ρ.re) := by
      simpa only [classicalZetaPartialSum] using
        norm_zeta_zero_sharp_cutoff_sum_le hT hρmem hσ
    exact hSharp.trans hError
  have hRect := hρmem
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle] at hRect
  exact classical_typeI_or_typeII_quantitative
    ⌊sharpZetaCutoff T⌋₊ Y X ρ q (X : ℝ) hY hX hYA hXY hq
    hFull (norm_zetaMollifier_le_length X ρ (hσ.le.trans hRect.1.1))
    hShortProduct

/-- The decidable branch classifier used before multiplicity-weighted
pigeonholing.  This name is deliberately distinct from the Section 13.1
Guth--Maynard predicate `IsTypeIZero`. -/
def ChoosesClassicalTypeI (Y : ℕ) (q : ℝ) (ρ : ℂ) : Prop :=
  q ≤ ‖classicalZetaPartialSum Y ρ‖

noncomputable instance (Y : ℕ) (q : ℝ) (ρ : ℂ) :
    Decidable (ChoosesClassicalTypeI Y q ρ) :=
  inferInstanceAs (Decidable (q ≤ ‖classicalZetaPartialSum Y ρ‖))

/-- Splitting a finite set by a decidable predicate preserves its full
natural-valued weight exactly. -/
theorem sum_filter_add_sum_filter_not_eq_sum
    {α : Type*} [DecidableEq α] (S : Finset α) (weight : α → ℕ)
    (P : α → Prop) [DecidablePred P] :
    (∑ x ∈ S.filter P, weight x) +
        (∑ x ∈ S.filter (fun y => ¬ P y), weight x) =
      ∑ x ∈ S, weight x := by
  simpa only using Finset.sum_filter_add_sum_filter_not S P weight

/-- One side of a finite binary partition carries at least half the total
natural-valued weight. -/
theorem exists_multiplicity_dominant_binary_branch
    {α : Type*} [DecidableEq α] (S : Finset α) (weight : α → ℕ)
    (P : α → Prop) [DecidablePred P] :
    (∑ x ∈ S, weight x ≤ 2 * ∑ x ∈ S.filter P, weight x) ∨
      (∑ x ∈ S, weight x ≤
        2 * ∑ x ∈ S.filter (fun y => ¬ P y), weight x) := by
  let leftWeight := ∑ x ∈ S.filter P, weight x
  let rightWeight := ∑ x ∈ S.filter (fun y => ¬ P y), weight x
  have hSplit : leftWeight + rightWeight = ∑ x ∈ S, weight x := by
    simpa only [leftWeight, rightWeight] using
      sum_filter_add_sum_filter_not_eq_sum S weight P
  rcases le_total rightWeight leftWeight with h | h
  · left
    omega
  · right
    omega

/-- Polynomial coefficient mass and a power-sized lower threshold are
compatible with the rational localizer after increasing its degree. -/
theorem rpow_mass_mul_localizer_lt_three_fourths_mul_rpow
    (B D δ T : ℝ) (k : ℕ) (hT : 8 ≤ T)
    (hExponent : 2 * (B + D + 1) ≤ δ * (k : ℝ)) :
    T ^ B * (T ^ (δ / 2) / T ^ δ) ^ k <
      (3 / 4) * T ^ (-D) := by
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hRatio : (T ^ (δ / 2) / T ^ δ) ^ k =
      T ^ ((-(δ / 2)) * (k : ℝ)) := by
    rw [← Real.rpow_sub hTpos]
    have hsub : δ / 2 - δ = -(δ / 2) := by ring
    rw [hsub, ← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
  have hPower :
      T ^ B * (T ^ (δ / 2) / T ^ δ) ^ k ≤ T ^ (-D - 1) := by
    rw [hRatio, ← Real.rpow_add hTpos]
    apply Real.rpow_le_rpow_of_exponent_le hTone
    nlinarith
  have hInv : T ^ (-1 : ℝ) ≤ 1 / 8 := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hT
  have hDpow : 0 < T ^ (-D) := Real.rpow_pos_of_pos hTpos _
  calc
    T ^ B * (T ^ (δ / 2) / T ^ δ) ^ k ≤ T ^ (-D - 1) := hPower
    _ = T ^ (-D) * T ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      congr 1
    _ ≤ T ^ (-D) * (1 / 8) := mul_le_mul_of_nonneg_left hInv hDpow.le
    _ < T ^ (-D) * (3 / 4) := by nlinarith
    _ = (3 / 4) * T ^ (-D) := by ring

/-- Generic exact-beta removal for a finite Dirichlet polynomial whose
coefficient mass and large-value threshold have explicit power bounds.
This is the common localization engine for both classical detector branches. -/
theorem finiteDirichlet_beta_removal_power_threshold :
    ∀ δ : ℝ, 0 < δ → ∀ B D : ℝ,
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ (σ T : ℝ) (ρ : ℂ) (S : Finset ℕ) (coeff : ℕ → ℂ) (V : ℝ),
          1 / 2 ≤ σ → σ ≤ 1 → T₀ ≤ T →
          σ ≤ ρ.re → ρ.re ≤ 1 →
          (∀ n ∈ S, 0 < n) →
          finiteDirichletMass S coeff ≤ T ^ B →
          T ^ (-D) ≤ V →
          V ≤ ‖finiteDirichletSeries S coeff ρ‖ →
          ∃ t : ℝ, |t - ρ.im| ≤ T ^ δ ∧
            (3 / 4) * V ≤
              ‖finiteDirichletSeries S coeff
                ((σ : ℂ) + I * (t : ℂ))‖ := by
  intro δ hδ B D
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (B + D + 1) / δ)
  have hExponent : 2 * (B + D + 1) < δ * (k : ℝ) := by
    rw [div_lt_iff₀ hδ] at hk
    simpa only [mul_comm] using hk
  have hPowTendsto : Tendsto (fun T : ℝ => T ^ (δ / 2)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hEventually : ∀ᶠ T : ℝ in atTop, 4 * (k : ℝ) < T ^ (δ / 2) :=
    hPowTendsto.eventually (eventually_gt_atTop (4 * (k : ℝ)))
  rw [eventually_atTop] at hEventually
  obtain ⟨Tfactor, hTfactor⟩ := hEventually
  let T₀ := max 8 Tfactor
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro σ T ρ S coeff V hσLower hσUpper hT hσρ hρUpper hS hMass hV hLarge
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTFactor : Tfactor ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hHpos : 0 < T ^ (δ / 2) := Real.rpow_pos_of_pos hTpos _
  have hRpos : 0 < T ^ δ := Real.rpow_pos_of_pos hTpos _
  let displacement : ℝ := ρ.re - σ
  let z : ℂ := (σ : ℂ) + I * (ρ.im : ℂ)
  have hDisplacement : 0 ≤ displacement := by
    dsimp [displacement]
    linarith
  have hDisplacementOne : displacement ≤ 1 := by
    dsimp [displacement]
    linarith
  have hz : 0 ≤ z.re := by
    dsimp [z]
    simp
    linarith
  have hza : z + (displacement : ℂ) = ρ := by
    apply Complex.ext
    · simp [z, displacement]
    · simp [z, displacement]
  have hFactor : 3 / 4 <
      ‖(((T ^ (δ / 2) : ℝ) : ℂ) /
        (((T ^ (δ / 2) : ℝ) : ℂ) + (displacement : ℂ))) ^ k‖ :=
    localizer_factor_gt_three_fourths k (T ^ (δ / 2)) displacement
      hHpos hDisplacement hDisplacementOne (hTfactor T hTFactor)
  have hExterior :
      finiteDirichletMass S coeff * (T ^ (δ / 2) / T ^ δ) ^ k <
        (3 / 4) * V := by
    have hDecay := rpow_mass_mul_localizer_lt_three_fourths_mul_rpow
      B D δ T k hTEight hExponent.le
    have hRatioNonneg : 0 ≤ (T ^ (δ / 2) / T ^ δ) ^ k := by positivity
    calc
      finiteDirichletMass S coeff * (T ^ (δ / 2) / T ^ δ) ^ k ≤
          T ^ B * (T ^ (δ / 2) / T ^ δ) ^ k :=
        mul_le_mul_of_nonneg_right hMass hRatioNonneg
      _ < (3 / 4) * T ^ (-D) := hDecay
      _ ≤ (3 / 4) * V := mul_le_mul_of_nonneg_left hV (by norm_num)
  have hVpos : 0 < V := (Real.rpow_pos_of_pos hTpos (-D)).trans_le hV
  obtain ⟨y, hy, hyLarge⟩ := exists_nearby_large_value_finiteDirichlet
    S coeff k z (T ^ (δ / 2)) (T ^ δ) V displacement
    hS hHpos hRpos hVpos hz hDisplacement
    (by simpa only [hza] using hLarge) hFactor hExterior
  refine ⟨ρ.im + y, ?_, ?_⟩
  · have hSub : ρ.im + y - ρ.im = y := by ring
    rw [hSub]
    exact hy
  · have hPoint : z + (y : ℂ) * I =
        (σ : ℂ) + I * ((ρ.im + y : ℝ) : ℂ) := by
      dsimp [z]
      rw [ofReal_add]
      ring
    rw [← hPoint]
    exact hyLarge

/-- Once every object has a shifted dyadic witness in its assigned branch,
one branch and one scale preserve the full multiplicity up to the explicit
factor two for branch selection and the existing extraction losses. -/
theorem finite_common_scale_binary_branch_extraction
    {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) (ordinate : α → ℝ)
    (P : α → Prop) [DecidablePred P]
    (kI kII L : ℕ) (H : ℝ)
    (largeI : ℕ → ℝ → Prop) (largeII : ℕ → ℝ → Prop)
    (inInterval : ℝ → Prop)
    (hTotalPos : 0 < ∑ x ∈ S, weight x)
    (hEachI : ∀ x ∈ S, P x → ∃ t : ℝ,
      |ordinate x - t| ≤ H ∧ inInterval t ∧
        ∃ r ∈ Finset.range kI, largeI r t)
    (hEachII : ∀ x ∈ S, ¬ P x → ∃ t : ℝ,
      |ordinate x - t| ≤ H ∧ inInterval t ∧
        ∃ r ∈ Finset.range kII, largeII r t)
    (hLocal : ∀ z : ℤ,
      ∑ x ∈ S.filter
        (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
        weight x ≤ L) :
    (∃ r ∈ Finset.range kI, ∃ W : Finset ℝ,
      IsSeparated 1 W ∧
      (∀ t ∈ W, largeI r t) ∧
      (∀ t ∈ W, inInterval t) ∧
      ∑ x ∈ S, weight x ≤
        4 * kI * ((2 * ⌈H⌉₊ + 1) * L) * W.card) ∨
    (∃ r ∈ Finset.range kII, ∃ W : Finset ℝ,
      IsSeparated 1 W ∧
      (∀ t ∈ W, largeII r t) ∧
      (∀ t ∈ W, inInterval t) ∧
      ∑ x ∈ S, weight x ≤
        4 * kII * ((2 * ⌈H⌉₊ + 1) * L) * W.card) := by
  rcases exists_multiplicity_dominant_binary_branch S weight P with hDom | hDom
  · left
    let SI := S.filter P
    have hBranchPos : 0 < ∑ x ∈ SI, weight x := by
      dsimp only [SI]
      omega
    have hSINonempty : SI.Nonempty := by
      by_contra hEmpty
      have hEq : SI = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
      rw [hEq] at hBranchPos
      simp at hBranchPos
    have hEach : ∀ x ∈ SI, ∃ t : ℝ,
        |ordinate x - t| ≤ H ∧ inInterval t ∧
          ∃ r ∈ Finset.range kI, largeI r t := by
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      exact hEachI x hxData.1 hxData.2
    have hLocalI : ∀ z : ℤ,
        ∑ x ∈ SI.filter
          (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
          weight x ≤ L := by
      intro z
      apply (Finset.sum_le_sum_of_subset ?_).trans (hLocal z)
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      have hxSI := Finset.mem_filter.mp hxData.1
      exact Finset.mem_filter.mpr ⟨hxSI.1, hxData.2⟩
    obtain ⟨r, hr, W, hSep, hLarge, hInterval, hBranchBound⟩ :=
      finite_shifted_dyadic_witness_extraction SI weight ordinate kI L H
        largeI inInterval hSINonempty hEach hLocalI
    refine ⟨r, hr, W, hSep, hLarge, hInterval, ?_⟩
    calc
      ∑ x ∈ S, weight x ≤ 2 * ∑ x ∈ SI, weight x := by
        simpa only [SI] using hDom
      _ ≤ 2 * (2 * kI * ((2 * ⌈H⌉₊ + 1) * L) * W.card) :=
        Nat.mul_le_mul_left 2 hBranchBound
      _ = 4 * kI * ((2 * ⌈H⌉₊ + 1) * L) * W.card := by ring
  · right
    let SII := S.filter (fun x => ¬ P x)
    have hBranchPos : 0 < ∑ x ∈ SII, weight x := by
      dsimp only [SII]
      omega
    have hSIINonempty : SII.Nonempty := by
      by_contra hEmpty
      have hEq : SII = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
      rw [hEq] at hBranchPos
      simp at hBranchPos
    have hEach : ∀ x ∈ SII, ∃ t : ℝ,
        |ordinate x - t| ≤ H ∧ inInterval t ∧
          ∃ r ∈ Finset.range kII, largeII r t := by
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      exact hEachII x hxData.1 hxData.2
    have hLocalII : ∀ z : ℤ,
        ∑ x ∈ SII.filter
          (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
          weight x ≤ L := by
      intro z
      apply (Finset.sum_le_sum_of_subset ?_).trans (hLocal z)
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      have hxSII := Finset.mem_filter.mp hxData.1
      exact Finset.mem_filter.mpr ⟨hxSII.1, hxData.2⟩
    obtain ⟨r, hr, W, hSep, hLarge, hInterval, hBranchBound⟩ :=
      finite_shifted_dyadic_witness_extraction SII weight ordinate kII L H
        largeII inInterval hSIINonempty hEach hLocalII
    refine ⟨r, hr, W, hSep, hLarge, hInterval, ?_⟩
    calc
      ∑ x ∈ S, weight x ≤ 2 * ∑ x ∈ SII, weight x := by
        simpa only [SII] using hDom
      _ ≤ 2 * (2 * kII * ((2 * ⌈H⌉₊ + 1) * L) * W.card) :=
        Nat.mul_le_mul_left 2 hBranchBound
      _ = 4 * kII * ((2 * ⌈H⌉₊ + 1) * L) * W.card := by ring

/-- Actual zeta-zero branch and scale extraction once the elementary cutoff
and power-mass inequalities have been supplied.  The following native scale
lemma discharges those inequalities for `X = floor(T^(δ₂/2))` and
`Y = floor(T^δ₁)`. -/
theorem extract_classical_dichotomy_of_scale_bounds :
    ∀ (σ δ B₁ D₁ B₂ D₂ : ℝ),
      1 / 2 < σ → σ ≤ 1 → 0 < δ →
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ (T : ℝ) (Y X : ℕ), T₀ ≤ T →
          1 ≤ X → 1 < Y → X ≤ Y → Y ≤ ⌊sharpZetaCutoff T⌋₊ →
          (∀ ρ ∈ zerosInRect σ 1 T (2 * T),
            149 * sharpZetaCutoff T ^ (-ρ.re) ≤ T ^ (-D₁) / 2) →
          T ^ (-D₁) * (X : ℝ) ≤ 1 / 4 →
          finiteDirichletMass (classicalZetaLongTailSupport Y
              ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤ T ^ B₁ →
          T ^ (-D₁ - 1) ≤ T ^ (-D₁) / 2 →
          finiteDirichletMass (sharpMollifiedTailSupport Y X)
              (sharpMollifiedCoeff Y X) ≤ T ^ B₂ →
          T ^ (-D₂) ≤ 3 / 4 →
          zeroCountRect σ 1 T (2 * T) = 0 ∨
          (∃ r ∈ Finset.range (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊),
            ∃ W : Finset ℝ,
              IsSeparated 1 W ∧
              (∀ t ∈ W,
                ((3 / 4) * (T ^ (-D₁) / 2)) /
                    Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ ≤
                  ‖dirichletPoly (2 ^ r * Y)
                    (classicalZetaLongLineCoeff ⌊sharpZetaCutoff T⌋₊ σ) t‖) ∧
              (∀ t ∈ W,
                (3 / 4) * (T ^ (-D₁) / 2) ≤
                  ‖classicalZetaLongTail Y ⌊sharpZetaCutoff T⌋₊
                    ((σ : ℂ) + I * (t : ℂ))‖) ∧
              (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
              zeroCountRect σ 1 T (2 * T) ≤
                4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
                  ((2 * ⌈T ^ δ⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card) ∨
          (∃ r ∈ Finset.range (Nat.clog 2 Y),
            ∃ W : Finset ℝ,
              IsSeparated 1 W ∧
              (∀ t ∈ W,
                ((3 / 4) * (3 / 4)) / Nat.clog 2 Y ≤
                  ‖dirichletPoly (2 ^ r * X)
                    (sharpMollifiedLineCoeff Y X σ) t‖) ∧
              (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
              zeroCountRect σ 1 T (2 * T) ≤
                4 * Nat.clog 2 Y *
                  ((2 * ⌈T ^ δ⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card) := by
  intro σ δ B₁ D₁ B₂ D₂ hσ hσUpper hδ
  obtain ⟨T₁, hT₁, hBetaI⟩ :=
    finiteDirichlet_beta_removal_power_threshold δ hδ B₁ (D₁ + 1)
  obtain ⟨T₂, hT₂, hBetaII⟩ :=
    finiteDirichlet_beta_removal_power_threshold δ hδ B₂ D₂
  let T₀ := max T₁ T₂
  refine ⟨T₀, hT₁.trans (le_max_left _ _), ?_⟩
  intro T Y X hT hX hYStrict hXY hYA hError hShortProduct hMassI hThresholdI
    hMassII hThresholdII
  let A := ⌊sharpZetaCutoff T⌋₊
  let S := zerosInRect σ 1 T (2 * T)
  let q := T ^ (-D₁)
  let kI := Nat.clog 2 A
  let kII := Nat.clog 2 Y
  by_cases hCountZero : zeroCountRect σ 1 T (2 * T) = 0
  · exact Or.inl hCountZero
  · right
    have hT₁' : T₁ ≤ T := (le_max_left _ _).trans hT
    have hT₂' : T₂ ≤ T := (le_max_right _ _).trans hT
    have hTEight : 8 ≤ T := hT₁.trans hT₁'
    have hTpos : 0 < T := by linarith
    have hqPos : 0 < q := by
      exact Real.rpow_pos_of_pos hTpos _
    have hA : 1 < A := by
      have hCutNonneg : 0 ≤ sharpZetaCutoff T :=
        (four_mul_lt_sharpZetaCutoff T).le.trans'
          (mul_nonneg (by norm_num) hTpos.le)
      have hTwo : (2 : ℝ) ≤ sharpZetaCutoff T := by
        linarith [four_mul_lt_sharpZetaCutoff T]
      have hTwoNat : 2 ≤ A := (Nat.le_floor_iff hCutNonneg).mpr hTwo
      omega
    have hY : 1 ≤ Y := hX.trans hXY
    have hTotalPos : 0 < ∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ := by
      simpa only [S, zeroCountRect] using Nat.pos_of_ne_zero hCountZero
    have hEachI : ∀ ρ ∈ S, ChoosesClassicalTypeI Y q ρ →
        ∃ t : ℝ, |ρ.im - t| ≤ T ^ δ ∧
          (T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
          ∃ r ∈ Finset.range kI,
            ((3 / 4) * (q / 2)) / kI ≤
                ‖dirichletPoly (2 ^ r * Y)
                  (classicalZetaLongLineCoeff A σ) t‖ ∧
            (3 / 4) * (q / 2) ≤
              ‖classicalZetaLongTail Y A
                ((σ : ℂ) + I * (t : ℂ))‖ := by
      intro ρ hρ hChoice
      have hSharp : ‖classicalZetaPartialSum A ρ‖ ≤ q / 2 := by
        have hBase := norm_zeta_zero_sharp_cutoff_sum_le
          (by linarith) hρ (by linarith : 0 < σ)
        have hBase' : ‖classicalZetaPartialSum A ρ‖ ≤
            149 * sharpZetaCutoff T ^ (-ρ.re) := by
          simpa only [A, classicalZetaPartialSum] using hBase
        have hError' : 149 * sharpZetaCutoff T ^ (-ρ.re) ≤ q / 2 := by
          simpa only [q, S] using hError ρ hρ
        exact hBase'.trans hError'
      have hLong : q / 2 ≤ ‖classicalZetaLongTail Y A ρ‖ := by
        have hRaw := classical_typeI_of_short_sum_large A Y ρ (q / 2) q
          (by simpa only [A] using hYA) hSharp hChoice
        convert hRaw using 1
        ring
      have hRect := hρ
      dsimp only [S] at hRect
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
        mem_ZeroRectangle] at hRect
      obtain ⟨t, htShift, htLarge⟩ := hBetaI σ T ρ
        (classicalZetaLongTailSupport Y A) (fun _n => 1) (q / 2)
        hσ.le hσUpper hT₁' hRect.1.1 hRect.1.2.1
        (classicalZetaLongTailSupport_pos Y A)
        (by simpa only [A] using hMassI)
        (by simpa only [q, neg_add] using hThresholdI)
        (by simpa only [classicalZetaLongTail_eq_finiteDirichletSeries] using hLong)
      have htInterval : T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ := by
        rw [abs_le] at htShift
        constructor <;> linarith [hRect.1.2.2.1, hRect.1.2.2.2]
      have htLarge' : (3 / 4) * (q / 2) ≤
          ‖classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ))‖ := by
        simpa only [classicalZetaLongTail_eq_finiteDirichletSeries] using htLarge
      obtain ⟨r, hr, hrLarge⟩ := exists_classicalZetaLong_large_dyadic_block
        Y A σ t ((3 / 4) * (q / 2)) hY hA htLarge'
      exact ⟨t, by simpa [abs_sub_comm] using htShift, htInterval,
        r, by simpa only [kI] using hr,
        by simpa only [kI] using hrLarge, htLarge'⟩
    have hEachII : ∀ ρ ∈ S, ¬ ChoosesClassicalTypeI Y q ρ →
        ∃ t : ℝ, |ρ.im - t| ≤ T ^ δ ∧
          (T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
          ∃ r ∈ Finset.range kII,
            ((3 / 4) * (3 / 4)) / kII ≤
              ‖dirichletPoly (2 ^ r * X)
                (sharpMollifiedLineCoeff Y X σ) t‖ := by
      intro ρ hρ hChoice
      have hRect := hρ
      dsimp only [S] at hRect
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
        mem_ZeroRectangle] at hRect
      have hShort : ‖classicalZetaPartialSum Y ρ‖ ≤ q :=
        (lt_of_not_ge hChoice).le
      have hTailRaw := classical_typeII_of_short_sum_small Y X ρ q (X : ℝ)
        hY hX hXY hqPos.le hShort
        (norm_zetaMollifier_le_length X ρ (by linarith [hRect.1.1]))
      have hTail : 3 / 4 ≤ ‖sharpMollifiedTail Y X ρ‖ := by
        linarith [hTailRaw, hShortProduct]
      obtain ⟨t, htShift, htLarge⟩ := hBetaII σ T ρ
        (sharpMollifiedTailSupport Y X) (sharpMollifiedCoeff Y X) (3 / 4)
        hσ.le hσUpper hT₂' hRect.1.1 hRect.1.2.1
        (sharpMollifiedTailSupport_pos Y X) hMassII hThresholdII
        (by simpa only [sharpMollifiedTail] using hTail)
      have htInterval : T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ := by
        rw [abs_le] at htShift
        constructor <;> linarith [hRect.1.2.2.1, hRect.1.2.2.2]
      have htLarge' : (3 / 4) * (3 / 4) ≤
          ‖sharpMollifiedTail Y X ((σ : ℂ) + I * (t : ℂ))‖ := by
        simpa only [sharpMollifiedTail] using htLarge
      obtain ⟨r, hr, hrLarge⟩ := exists_sharpMollified_large_dyadic_block
        Y X σ t ((3 / 4) * (3 / 4)) hYStrict htLarge'
      exact ⟨t, by simpa [abs_sub_comm] using htShift, htInterval,
        r, by simpa only [kII] using hr, by simpa only [kII] using hrLarge⟩
    have hLocal : ∀ z : ℤ,
        ∑ ρ ∈ S.filter
          (fun y => (z : ℝ) ≤ y.im ∧ y.im < (z : ℝ) + 1),
          analyticVanishingOrder riemannZeta ρ ≤ classicalLocalMultiplicityCap T := by
      intro z
      simpa only [S, zeroUnitBin] using
        zeroUnitBin_multiplicity_le_cap σ T z hσ.le hTEight
    have hExtract := finite_common_scale_binary_branch_extraction S
      (analyticVanishingOrder riemannZeta) Complex.im
      (ChoosesClassicalTypeI Y q) kI kII
      (classicalLocalMultiplicityCap T) (T ^ δ)
      (fun r t =>
        (((3 / 4) * (q / 2)) / kI ≤
          ‖dirichletPoly (2 ^ r * Y) (classicalZetaLongLineCoeff A σ) t‖) ∧
        (3 / 4) * (q / 2) ≤
          ‖classicalZetaLongTail Y A
            ((σ : ℂ) + I * (t : ℂ))‖)
      (fun r t => ((3 / 4) * (3 / 4)) / kII ≤
        ‖dirichletPoly (2 ^ r * X) (sharpMollifiedLineCoeff Y X σ) t‖)
      (fun t => T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ)
      hTotalPos hEachI hEachII hLocal
    rcases hExtract with
      ⟨r, hr, W, hSep, hBoth, hRange, hCount⟩ |
      ⟨r, hr, W, hSep, hLarge, hRange, hCount⟩
    · left
      refine ⟨r, by simpa only [kI, A] using hr, W, hSep, ?_, ?_, hRange, ?_⟩
      · intro t ht
        simpa only [q, kI, A] using (hBoth t ht).1
      · intro t ht
        simpa only [q, A] using (hBoth t ht).2
      · simpa only [S, zeroCountRect, kI, A] using hCount
    · right
      refine ⟨r, by simpa only [kII] using hr, W, hSep, ?_, hRange, ?_⟩
      · intro t ht
        simpa only [kII] using hLarge t ht
      · simpa only [S, zeroCountRect, kII] using hCount

/-- The two power cutoffs used in the classical dichotomy eventually have
all required order, positivity, and ambient-length properties. -/
theorem eventually_classical_dichotomy_cutoffs
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hδOrder : δ₂ / 2 ≤ δ₁) (hδ₁One : δ₁ ≤ 1) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T ≥ T₀,
      let X := ⌊T ^ (δ₂ / 2)⌋₊
      let Y := ⌊T ^ δ₁⌋₊
      1 ≤ X ∧ 1 < Y ∧ X ≤ Y ∧ Y ≤ ⌊sharpZetaCutoff T⌋₊ ∧
        (X : ℝ) ≤ T ∧ (Y : ℝ) ≤ T := by
  have hTendsto : Tendsto (fun T : ℝ => T ^ δ₁) atTop atTop :=
    tendsto_rpow_atTop hδ₁
  have hEventually : ∀ᶠ T : ℝ in atTop, (2 : ℝ) ≤ T ^ δ₁ :=
    hTendsto.eventually (eventually_ge_atTop 2)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tscale, hTscale⟩ := hEventually
  let T₀ := max 8 Tscale
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT
  dsimp only
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTscale' : Tscale ≤ T := (le_max_right _ _).trans hT
  have hTone : 1 ≤ T := by linarith
  have hTnonneg : 0 ≤ T := by linarith
  have hXpowOne : 1 ≤ T ^ (δ₂ / 2) :=
    Real.one_le_rpow hTone (by positivity)
  have hYpowTwo : (2 : ℝ) ≤ T ^ δ₁ := hTscale T hTscale'
  have hYpowOne : 1 ≤ T ^ δ₁ := hYpowTwo.trans' one_le_two
  have hX : 1 ≤ ⌊T ^ (δ₂ / 2)⌋₊ :=
    (Nat.one_le_floor_iff _).mpr hXpowOne
  have hY : 1 < ⌊T ^ δ₁⌋₊ := by
    have hTwo : 2 ≤ ⌊T ^ δ₁⌋₊ :=
      (Nat.le_floor_iff (Real.rpow_nonneg hTnonneg _)).mpr hYpowTwo
    omega
  have hPowXY : T ^ (δ₂ / 2) ≤ T ^ δ₁ :=
    Real.rpow_le_rpow_of_exponent_le hTone hδOrder
  have hXY : ⌊T ^ (δ₂ / 2)⌋₊ ≤ ⌊T ^ δ₁⌋₊ :=
    Nat.floor_mono hPowXY
  have hYpowT : T ^ δ₁ ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hTone hδ₁One
  have hCutNonneg : 0 ≤ sharpZetaCutoff T :=
    (four_mul_lt_sharpZetaCutoff T).le.trans'
      (mul_nonneg (by norm_num) hTnonneg)
  have hYpowCut : T ^ δ₁ ≤ sharpZetaCutoff T := by
    calc
      T ^ δ₁ ≤ T := hYpowT
      _ ≤ 4 * T := by nlinarith
      _ ≤ sharpZetaCutoff T := (four_mul_lt_sharpZetaCutoff T).le
  have hYA : ⌊T ^ δ₁⌋₊ ≤ ⌊sharpZetaCutoff T⌋₊ :=
    Nat.floor_mono hYpowCut
  have hXcastFloor : (⌊T ^ (δ₂ / 2)⌋₊ : ℝ) ≤ T ^ (δ₂ / 2) :=
    Nat.floor_le (Real.rpow_nonneg hTnonneg _)
  have hYcastFloor : (⌊T ^ δ₁⌋₊ : ℝ) ≤ T ^ δ₁ :=
    Nat.floor_le (Real.rpow_nonneg hTnonneg _)
  have hXpowT : T ^ (δ₂ / 2) ≤ T := by
    have hHalfOne : δ₂ / 2 ≤ 1 := hδOrder.trans hδ₁One
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hTone hHalfOne
  exact ⟨hX, hY, hXY, hYA, hXcastFloor.trans hXpowT,
    hYcastFloor.trans hYpowT⟩

/-- Structural mass and localization-threshold bounds for admissible
classical cutoffs. -/
theorem classical_dichotomy_mass_and_threshold_bounds
    (T δ₂ : ℝ) (Y X : ℕ) (hT : 8 ≤ T)
    (hYT : (Y : ℝ) ≤ T) (hXT : (X : ℝ) ≤ T) :
    finiteDirichletMass (classicalZetaLongTailSupport Y
        ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤ T ^ (2 : ℝ) ∧
      T ^ (-δ₂ - 1) ≤ T ^ (-δ₂) / 2 ∧
      finiteDirichletMass (sharpMollifiedTailSupport Y X)
          (sharpMollifiedCoeff Y X) ≤ T ^ (4 : ℝ) ∧
      T ^ (-1 : ℝ) ≤ 3 / 4 := by
  have hTpos : 0 < T := by linarith
  have hTnonneg : 0 ≤ T := hTpos.le
  have hCutNonneg : 0 ≤ sharpZetaCutoff T :=
    (four_mul_lt_sharpZetaCutoff T).le.trans'
      (mul_nonneg (by norm_num) hTnonneg)
  have hAcast : (⌊sharpZetaCutoff T⌋₊ : ℝ) ≤ 6 * T :=
    (Nat.floor_le hCutNonneg).trans (sharpZetaCutoff_le_six_mul (by linarith))
  have hSixT : 6 * T ≤ T ^ 2 := by nlinarith
  have hMassI :
      finiteDirichletMass (classicalZetaLongTailSupport Y
          ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤ T ^ (2 : ℝ) := by
    calc
      finiteDirichletMass (classicalZetaLongTailSupport Y
            ⌊sharpZetaCutoff T⌋₊) (fun _n => 1) ≤
          (⌊sharpZetaCutoff T⌋₊ : ℝ) :=
        classicalZetaLongTail_mass_le Y ⌊sharpZetaCutoff T⌋₊
      _ ≤ T ^ 2 := hAcast.trans hSixT
      _ = T ^ (2 : ℝ) := by norm_num
  have hInv : T ^ (-1 : ℝ) ≤ 1 / 8 := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hT
  have hDeltaPow : 0 < T ^ (-δ₂) := Real.rpow_pos_of_pos hTpos _
  have hThresholdI : T ^ (-δ₂ - 1) ≤ T ^ (-δ₂) / 2 := by
    calc
      T ^ (-δ₂ - 1) = T ^ (-δ₂) * T ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hTpos]
        congr 1
      _ ≤ T ^ (-δ₂) * (1 / 8) :=
        mul_le_mul_of_nonneg_left hInv hDeltaPow.le
      _ ≤ T ^ (-δ₂) / 2 := by nlinarith
  have hYX : ((Y * X : ℕ) : ℝ) ≤ T ^ 2 := by
    push_cast
    calc
      (Y : ℝ) * (X : ℝ) ≤ T * T :=
        mul_le_mul hYT hXT (Nat.cast_nonneg X) hTnonneg
      _ = T ^ 2 := by ring
  have hMassII :
      finiteDirichletMass (sharpMollifiedTailSupport Y X)
          (sharpMollifiedCoeff Y X) ≤ T ^ (4 : ℝ) := by
    calc
      finiteDirichletMass (sharpMollifiedTailSupport Y X)
            (sharpMollifiedCoeff Y X) ≤ ((Y * X : ℕ) : ℝ) ^ 2 :=
        by simpa only [Nat.cast_mul] using sharpMollifiedTail_mass_le_sq Y X
      _ ≤ (T ^ 2) ^ 2 := by
        exact pow_le_pow_left₀ (Nat.cast_nonneg (Y * X)) hYX 2
      _ = T ^ (4 : ℝ) := by
        rw [show (T ^ 2) ^ 2 = T ^ 4 by ring]
        norm_num
  exact ⟨hMassI, hThresholdI, hMassII, hInv.trans (by norm_num)⟩

theorem eventually_classical_short_product_le_quarter
    (δ₂ : ℝ) (hδ₂ : 0 < δ₂) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T ≥ T₀,
      T ^ (-δ₂) * (⌊T ^ (δ₂ / 2)⌋₊ : ℝ) ≤ 1 / 4 := by
  have hTendsto : Tendsto (fun T : ℝ => T ^ (-(δ₂ / 2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by positivity)
  have hEventually : ∀ᶠ T : ℝ in atTop, T ^ (-(δ₂ / 2)) < 1 / 4 :=
    (tendsto_order.1 hTendsto).2 (1 / 4) (by norm_num)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tscale, hTscale⟩ := hEventually
  let T₀ := max 1 Tscale
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT
  have hTone : 1 ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hTscale' : Tscale ≤ T := (le_max_right _ _).trans hT
  have hFloor : (⌊T ^ (δ₂ / 2)⌋₊ : ℝ) ≤ T ^ (δ₂ / 2) :=
    Nat.floor_le (Real.rpow_nonneg (by linarith) _)
  have hNegPow : 0 ≤ T ^ (-δ₂) := Real.rpow_nonneg (by linarith) _
  calc
    T ^ (-δ₂) * (⌊T ^ (δ₂ / 2)⌋₊ : ℝ) ≤
        T ^ (-δ₂) * T ^ (δ₂ / 2) :=
      mul_le_mul_of_nonneg_left hFloor hNegPow
    _ = T ^ (-(δ₂ / 2)) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring
    _ ≤ 1 / 4 := (hTscale T hTscale').le

/-- Uniform sharp-cutoff error bound with no mollifier loss. -/
theorem sharp_full_error_le_power_majorant
    {σ T : ℝ} {ρ : ℂ} (hσ : 0 ≤ σ) (hT : 1 ≤ T)
    (hρ : ρ ∈ zerosInRect σ 1 T (2 * T)) :
    149 * sharpZetaCutoff T ^ (-ρ.re) ≤ 149 * (4 * T) ^ (-σ) := by
  have hRect := hρ
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle] at hRect
  have hCutOne : 1 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hPower : sharpZetaCutoff T ^ (-ρ.re) ≤ (4 * T) ^ (-σ) := by
    calc
      sharpZetaCutoff T ^ (-ρ.re) ≤ sharpZetaCutoff T ^ (-σ) :=
        Real.rpow_le_rpow_of_exponent_le hCutOne (by linarith [hRect.1.1])
      _ ≤ (4 * T) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (four_mul_lt_sharpZetaCutoff T).le (by linarith)
  exact mul_le_mul_of_nonneg_left hPower (by norm_num)

theorem eventually_sharp_full_error_le_split_threshold
    (σ δ₂ : ℝ) (hσ : 0 ≤ σ) (hGap : δ₂ < σ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T ≥ T₀,
      ∀ ρ ∈ zerosInRect σ 1 T (2 * T),
        149 * sharpZetaCutoff T ^ (-ρ.re) ≤ T ^ (-δ₂) / 2 := by
  let d := σ - δ₂
  have hd : 0 < d := by dsimp only [d]; linarith
  have hCore : Tendsto (fun T : ℝ => T ^ (-d)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hd
  have hScaled : Tendsto
      (fun T : ℝ => (149 * (4 : ℝ) ^ (-σ)) * T ^ (-d))
      atTop (𝓝 0) := by
    simpa using hCore.const_mul (149 * (4 : ℝ) ^ (-σ))
  have hEventually : ∀ᶠ T : ℝ in atTop,
      (149 * (4 : ℝ) ^ (-σ)) * T ^ (-d) < 1 / 2 :=
    (tendsto_order.1 hScaled).2 (1 / 2) (by norm_num)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tscale, hTscale⟩ := hEventually
  let T₀ := max 1 Tscale
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT ρ hρ
  have hTone : 1 ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hTscale' : Tscale ≤ T := (le_max_right _ _).trans hT
  have hMajorant := sharp_full_error_le_power_majorant hσ hTone hρ
  have hIdentity :
      149 * (4 * T) ^ (-σ) * T ^ δ₂ =
        (149 * (4 : ℝ) ^ (-σ)) * T ^ (-d) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by linarith : 0 ≤ T)]
    calc
      149 * (4 ^ (-σ) * T ^ (-σ)) * T ^ δ₂ =
          (149 * 4 ^ (-σ)) * (T ^ (-σ) * T ^ δ₂) := by ring
      _ = (149 * 4 ^ (-σ)) * T ^ (-d) := by
        rw [← Real.rpow_add hTpos]
        congr 2
        dsimp only [d]
        ring
  have hProduct : 149 * (4 * T) ^ (-σ) * T ^ δ₂ ≤ 1 / 2 := by
    rw [hIdentity]
    exact (hTscale T hTscale').le
  have hRpowPos : 0 < T ^ δ₂ := Real.rpow_pos_of_pos hTpos _
  have hTarget : 149 * (4 * T) ^ (-σ) ≤ T ^ (-δ₂) / 2 := by
    have hNeg : T ^ (-δ₂) = (T ^ δ₂)⁻¹ := by
      rw [Real.rpow_neg (by linarith : 0 ≤ T)]
    rw [hNeg, show (T ^ δ₂)⁻¹ / 2 = (1 / 2) / T ^ δ₂ by
      field_simp]
    rw [le_div_iff₀ hRpowPos]
    exact hProduct
  exact hMajorant.trans hTarget

/-- Downstream-facing certificate produced by the finite classical detector.
It records the actual power cutoffs, exact fixed line, common dyadic scale,
separated ordinates, and analytic-multiplicity loss for each branch. -/
def ClassicalTypeITypeIIDichotomyConclusion
    (σ δ δ₁ δ₂ T : ℝ) : Prop :=
  let X := ⌊T ^ (δ₂ / 2)⌋₊
  let Y := ⌊T ^ δ₁⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  zeroCountRect σ 1 T (2 * T) = 0 ∨
    (∃ r ∈ Finset.range (Nat.clog 2 A), ∃ W : Finset ℝ,
      IsSeparated 1 W ∧
      (∀ t ∈ W,
        ((3 / 4) * (T ^ (-δ₂) / 2)) / Nat.clog 2 A ≤
          ‖dirichletPoly (2 ^ r * Y)
            (classicalZetaLongLineCoeff A σ) t‖) ∧
      (∀ t ∈ W,
        (3 / 4) * (T ^ (-δ₂) / 2) ≤
          ‖classicalZetaLongTail Y A
            ((σ : ℂ) + I * (t : ℂ))‖) ∧
      (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
      zeroCountRect σ 1 T (2 * T) ≤
        4 * Nat.clog 2 A *
          ((2 * ⌈T ^ δ⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card) ∨
    (∃ r ∈ Finset.range (Nat.clog 2 Y), ∃ W : Finset ℝ,
      IsSeparated 1 W ∧
      (∀ t ∈ W,
        ((3 / 4) * (3 / 4)) / Nat.clog 2 Y ≤
          ‖dirichletPoly (2 ^ r * X)
            (sharpMollifiedLineCoeff Y X σ) t‖) ∧
      (∀ t ∈ W, T - T ^ δ ≤ t ∧ t ≤ 2 * T + T ^ δ) ∧
      zeroCountRect σ 1 T (2 * T) ≤
        4 * Nat.clog 2 Y *
          ((2 * ⌈T ^ δ⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card)

/-- Complete finite Type-I/Type-II detector dichotomy with the source power
cutoffs.  This closes the detector node itself; the Type-I medium and terminal
scale estimates and the endpoint density reduction remain downstream. -/
theorem classical_typeI_typeII_dichotomy_native :
    ∀ (σ δ δ₁ δ₂ : ℝ),
      1 / 2 < σ → σ ≤ 1 → 0 < δ →
      0 < δ₁ → 0 < δ₂ → δ₂ / 2 ≤ δ₁ → δ₁ ≤ 1 → δ₂ < σ →
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T ≥ T₀,
        ClassicalTypeITypeIIDichotomyConclusion σ δ δ₁ δ₂ T := by
  intro σ δ δ₁ δ₂ hσ hσUpper hδ hδ₁ hδ₂ hδOrder hδ₁One hδ₂σ
  obtain ⟨Tbranch, hTbranch, hBranch⟩ :=
    extract_classical_dichotomy_of_scale_bounds σ δ 2 δ₂ 4 1
      hσ hσUpper hδ
  obtain ⟨Tcut, hTcut, hCut⟩ :=
    eventually_classical_dichotomy_cutoffs δ₁ δ₂ hδ₁ hδ₂ hδOrder hδ₁One
  obtain ⟨Tproduct, hTproduct, hProduct⟩ :=
    eventually_classical_short_product_le_quarter δ₂ hδ₂
  have hσNonneg : 0 ≤ σ := by linarith
  obtain ⟨Terror, hTerror, hError⟩ :=
    eventually_sharp_full_error_le_split_threshold σ δ₂ hσNonneg hδ₂σ
  let T₀ := max Tbranch (max Tcut (max Tproduct Terror))
  refine ⟨T₀, hTbranch.trans (le_max_left _ _), ?_⟩
  intro T hT
  have hTbranch' : Tbranch ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tcut (max Tproduct Terror) ≤ T :=
    (le_max_right _ _).trans hT
  have hTcut' : Tcut ≤ T := (le_max_left _ _).trans hRest
  have hRest' : max Tproduct Terror ≤ T := (le_max_right _ _).trans hRest
  have hTproduct' : Tproduct ≤ T := (le_max_left _ _).trans hRest'
  have hTerror' : Terror ≤ T := (le_max_right _ _).trans hRest'
  have hCutData := hCut T hTcut'
  dsimp only at hCutData
  rcases hCutData with ⟨hX, hY, hXY, hYA, hXT, hYT⟩
  have hTEight : 8 ≤ T := hTbranch.trans hTbranch'
  obtain ⟨hMassI, hThresholdI, hMassII, hThresholdII⟩ :=
    classical_dichotomy_mass_and_threshold_bounds T δ₂
      ⌊T ^ δ₁⌋₊ ⌊T ^ (δ₂ / 2)⌋₊ hTEight hYT hXT
  have hResult := hBranch T ⌊T ^ δ₁⌋₊ ⌊T ^ (δ₂ / 2)⌋₊ hTbranch'
    hX hY hXY hYA (hError T hTerror') (hProduct T hTproduct')
    hMassI hThresholdI hMassII hThresholdII
  simpa only [ClassicalTypeITypeIIDichotomyConclusion] using hResult

end RiemannZeta.GuthMaynard
