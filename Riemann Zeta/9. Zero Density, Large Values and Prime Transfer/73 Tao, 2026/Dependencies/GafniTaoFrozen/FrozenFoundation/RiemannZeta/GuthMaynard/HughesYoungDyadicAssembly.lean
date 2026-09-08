import RiemannZeta.GuthMaynard.HughesYoungBoxConsumer

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Exact finite dyadic assembly for the Hughes--Young source sum

The DFI theorem is applied only after multiplying the physical source weight
by smooth dyadic cutoffs.  This file proves that the resulting finite family
really reconstructs the original finite off-diagonal sum.  The telescoping
partition has one boundary piece, `hughesYoungDyadicStep`; on positive integer
arguments that piece is supported only at the physical endpoint `1`.
-/

/-- The finite telescoping partition, with its lower boundary piece restored,
is exactly one throughout the represented positive range. -/
theorem hughesYoungDyadicStep_add_sum_cutoff_eq_one
    {K : ℕ} {x : ℝ}
    (hxUpper : x ≤ hughesYoungDyadicRatio ^ (K + 1)) :
    hughesYoungDyadicStep x +
        (∑ j ∈ Finset.range (K + 1),
          hughesYoungDyadicCutoffAt (hughesYoungDyadicScale j) x) = 1 := by
  rw [sum_hughesYoungDyadicCutoff_eq]
  have hpow : 0 < hughesYoungDyadicRatio ^ (K + 1) :=
    pow_pos hughesYoungDyadicRatio_pos _
  have hquot : x / hughesYoungDyadicRatio ^ (K + 1) ≤ 1 :=
    (div_le_one hpow).mpr hxUpper
  rw [hughesYoungDyadicStep_eq_one hquot]
  ring

/-- On a positive natural argument, the lower boundary cutoff can be nonzero
only at the isolated value `1`. -/
theorem hughesYoungDyadicStep_nat_eq_zero_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    hughesYoungDyadicStep (n : ℝ) = 0 := by
  apply hughesYoungDyadicStep_eq_zero
  have hsqrt : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hsqrt.le.trans (by exact_mod_cast hn)

/-- Every finite physical scale is covered by a finite initial segment of
the geometric Hughes--Young partition. -/
theorem exists_hughesYoungDyadicCoverIndex (x : ℝ) :
    ∃ K : ℕ, x ≤ hughesYoungDyadicRatio ^ (K + 1) := by
  have hpow : Tendsto (fun K : ℕ => hughesYoungDyadicRatio ^ K)
      atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_hughesYoungDyadicRatio
  have hevent : ∀ᶠ K : ℕ in atTop,
      x ≤ hughesYoungDyadicRatio ^ K :=
    hpow.eventually (eventually_ge_atTop x)
  obtain ⟨K, hK⟩ := hevent.exists
  exact ⟨K, hK.trans (by
    apply pow_le_pow_right₀ one_lt_hughesYoungDyadicRatio.le
    omega)⟩

/-- One dyadic depth covers both physical coordinates uniformly for every
positive mollifier pair below `ell` and every arithmetic index below `M`.
This is the finite cover used when summing the exact per-box DFI theorem. -/
theorem exists_uniform_hughesYoungDyadicCoverIndex (ell M : ℕ) :
    ∃ K : ℕ, ∀ {h k m n : ℕ}, h ≤ ell → k ≤ ell → m ≤ M → n ≤ M →
      (((hughesYoungReducedLeft h k) * m : ℕ) : ℝ) ≤
          hughesYoungDyadicRatio ^ (K + 1) ∧
        (((hughesYoungReducedRight h k) * n : ℕ) : ℝ) ≤
          hughesYoungDyadicRatio ^ (K + 1) := by
  obtain ⟨K, hK⟩ :=
    exists_hughesYoungDyadicCoverIndex (((ell * M : ℕ) : ℝ))
  refine ⟨K, ?_⟩
  intro h k m n hh hk hm hn
  have hleft : hughesYoungReducedLeft h k ≤ h := by
    exact Nat.div_le_self h (hughesYoungCommonDivisor h k)
  have hright : hughesYoungReducedRight h k ≤ k := by
    exact Nat.div_le_self k (hughesYoungCommonDivisor h k)
  constructor
  · have hnat : hughesYoungReducedLeft h k * m ≤ ell * M :=
      Nat.mul_le_mul (hleft.trans hh) hm
    have hreal : (((hughesYoungReducedLeft h k) * m : ℕ) : ℝ) ≤
        ((ell * M : ℕ) : ℝ) := by exact_mod_cast hnat
    exact hreal.trans hK
  · have hnat : hughesYoungReducedRight h k * n ≤ ell * M :=
      Nat.mul_le_mul (hright.trans hk) hn
    have hreal : (((hughesYoungReducedRight h k) * n : ℕ) : ℝ) ≤
        ((ell * M : ℕ) : ℝ) := by exact_mod_cast hnat
    exact hreal.trans hK

/-- A source sum localized by arbitrary real cutoffs in the two physical
variables. -/
noncomputable def finiteQuadraticDivisorOffDiagonalPiece
    (h k M N : ℕ) (F : ℝ → ℝ → ℂ) (A B : ℝ → ℝ) : ℂ :=
  finiteQuadraticDivisorOffDiagonal h k M N
    (fun x y => (A (x : ℝ) : ℂ) * (B (y : ℝ) : ℂ) * F x y)

/-- The piece with two dyadic cutoffs is exactly the localized source box
used by the near/far DFI consumer. -/
theorem finiteQuadraticDivisorOffDiagonalPiece_cutoff_eq_localizedBox
    (T c H : ℝ) (h k M N : ℕ) (i j : ℕ) :
    finiteQuadraticDivisorOffDiagonalPiece h k M N
        (hughesYoungIntegratedSourceWeight T c H h k)
        (hughesYoungDyadicCutoffAt
          (hughesYoungCommonDivisor h k * hughesYoungDyadicScale i))
        (hughesYoungDyadicCutoffAt
          (hughesYoungCommonDivisor h k * hughesYoungDyadicScale j)) =
      hughesYoungLocalizedOffDiagonalBox T c H
        (hughesYoungDyadicScale i) (hughesYoungDyadicScale j) h k M N := by
  unfold finiteQuadraticDivisorOffDiagonalPiece
    hughesYoungLocalizedOffDiagonalBox
    hughesYoungPreReducedIntegratedBoxWeight
  rfl

theorem finiteQuadraticDivisorOffDiagonalPiece_add_left
    (h k M N : ℕ) (F : ℝ → ℝ → ℂ) (A B C : ℝ → ℝ) :
    finiteQuadraticDivisorOffDiagonalPiece h k M N F (A + B) C =
      finiteQuadraticDivisorOffDiagonalPiece h k M N F A C +
      finiteQuadraticDivisorOffDiagonalPiece h k M N F B C := by
  unfold finiteQuadraticDivisorOffDiagonalPiece
    finiteQuadraticDivisorOffDiagonal
  simp only [Pi.add_apply, Complex.ofReal_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : quadraticDivisorShift h k m n = 0
  · simp [hs]
  · simp only [hs, if_false]
    ring

theorem finiteQuadraticDivisorOffDiagonalPiece_add_right
    (h k M N : ℕ) (F : ℝ → ℝ → ℂ) (A B C : ℝ → ℝ) :
    finiteQuadraticDivisorOffDiagonalPiece h k M N F A (B + C) =
      finiteQuadraticDivisorOffDiagonalPiece h k M N F A B +
      finiteQuadraticDivisorOffDiagonalPiece h k M N F A C := by
  unfold finiteQuadraticDivisorOffDiagonalPiece
    finiteQuadraticDivisorOffDiagonal
  simp only [Pi.add_apply, Complex.ofReal_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : quadraticDivisorShift h k m n = 0
  · simp [hs]
  · simp only [hs, if_false]
    ring

theorem finiteQuadraticDivisorOffDiagonalPiece_sum_left
    (h k M N : ℕ) (F : ℝ → ℝ → ℂ) (A : ℕ → ℝ → ℝ)
    (B : ℝ → ℝ) (I : Finset ℕ) :
    finiteQuadraticDivisorOffDiagonalPiece h k M N F
        (∑ i ∈ I, A i) B =
      ∑ i ∈ I, finiteQuadraticDivisorOffDiagonalPiece h k M N F (A i) B := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [finiteQuadraticDivisorOffDiagonalPiece,
      finiteQuadraticDivisorOffDiagonal]
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        finiteQuadraticDivisorOffDiagonalPiece_add_left, ih]

theorem finiteQuadraticDivisorOffDiagonalPiece_sum_right
    (h k M N : ℕ) (F : ℝ → ℝ → ℂ) (A : ℝ → ℝ)
    (B : ℕ → ℝ → ℝ) (J : Finset ℕ) :
    finiteQuadraticDivisorOffDiagonalPiece h k M N F A
        (∑ j ∈ J, B j) =
      ∑ j ∈ J, finiteQuadraticDivisorOffDiagonalPiece h k M N F A (B j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [finiteQuadraticDivisorOffDiagonalPiece,
      finiteQuadraticDivisorOffDiagonal]
  | @insert j J hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        finiteQuadraticDivisorOffDiagonalPiece_add_right, ih]

/-- Exact bilinear expansion of a finite off-diagonal sum through two finite
partitions of unity.  This lemma is deliberately stated for arbitrary
partitions so the source bookkeeping is independent of the analytic choice
of dyadic cutoffs. -/
theorem finiteQuadraticDivisorOffDiagonal_eq_partition
    (h k M N : ℕ) (F : ℝ → ℝ → ℂ)
    (A₀ B₀ : ℝ → ℝ) (A : ℕ → ℝ → ℝ) (B : ℕ → ℝ → ℝ)
    (I J : Finset ℕ)
    (hA : ∀ m ∈ Finset.Icc 1 M,
      A₀ ((h * m : ℕ) : ℝ) + ∑ i ∈ I, A i ((h * m : ℕ) : ℝ) = 1)
    (hB : ∀ n ∈ Finset.Icc 1 N,
      B₀ ((k * n : ℕ) : ℝ) + ∑ j ∈ J, B j ((k * n : ℕ) : ℝ) = 1) :
    finiteQuadraticDivisorOffDiagonal h k M N
        (fun x y => F (x : ℝ) (y : ℝ)) =
      finiteQuadraticDivisorOffDiagonalPiece h k M N F
        (A₀ + ∑ i ∈ I, A i) (B₀ + ∑ j ∈ J, B j) := by
  unfold finiteQuadraticDivisorOffDiagonal
    finiteQuadraticDivisorOffDiagonalPiece
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hshift : quadraticDivisorShift h k m n = 0
  · simp [hshift]
  · simp only [hshift, if_false, Pi.add_apply]
    have hAC : A₀ ((h * m : ℕ) : ℝ) +
        (∑ i ∈ I, A i) ((h * m : ℕ) : ℝ) = 1 := by
      simpa only [Finset.sum_apply] using hA m hm
    have hBC : B₀ ((k * n : ℕ) : ℝ) +
        (∑ j ∈ J, B j) ((k * n : ℕ) : ℝ) = 1 := by
      simpa only [Finset.sum_apply] using hB n hn
    rw [hAC, hBC]
    simp

/-- The isolated lower cutoff in the gcd-reduced physical coordinate. -/
noncomputable def hughesYoungGCDBoundaryCutoff (h k : ℕ) (x : ℝ) : ℝ :=
  hughesYoungDyadicStep (x / hughesYoungCommonDivisor h k)

theorem hughesYoungGCDBoundaryCutoff_left_nat
    {h k m : ℕ} (hh : 0 < h) (hm : 0 < m) :
    hughesYoungGCDBoundaryCutoff h k (((h * m : ℕ) : ℝ)) =
      if hughesYoungReducedLeft h k * m = 1 then 1 else 0 := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hscale : (((h * m : ℕ) : ℝ) / hughesYoungCommonDivisor h k) =
      (((hughesYoungReducedLeft h k * m : ℕ) : ℝ)) := by
    have hfactor := hughesYoungCommonDivisor_mul_reducedLeft h k
    have hfactorR : (h : ℝ) =
        (hughesYoungCommonDivisor h k : ℝ) *
          (hughesYoungReducedLeft h k : ℝ) := by
      exact_mod_cast hfactor.symm
    push_cast
    rw [hfactorR]
    field_simp [hd.ne']
  unfold hughesYoungGCDBoundaryCutoff
  rw [hscale]
  by_cases hone : hughesYoungReducedLeft h k * m = 1
  · rw [if_pos hone, hone]
    exact hughesYoungDyadicStep_eq_one (by norm_num)
  · rw [if_neg hone]
    apply hughesYoungDyadicStep_nat_eq_zero_of_two_le
    have hleft := hughesYoungReducedLeft_pos (k := k) hh
    have hprod : 0 < hughesYoungReducedLeft h k * m := Nat.mul_pos hleft hm
    omega

theorem hughesYoungGCDBoundaryCutoff_right_nat
    {h k n : ℕ} (hh : 0 < h) (hk : 0 < k) (hn : 0 < n) :
    hughesYoungGCDBoundaryCutoff h k (((k * n : ℕ) : ℝ)) =
      if hughesYoungReducedRight h k * n = 1 then 1 else 0 := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hscale : (((k * n : ℕ) : ℝ) / hughesYoungCommonDivisor h k) =
      (((hughesYoungReducedRight h k * n : ℕ) : ℝ)) := by
    have hfactor := hughesYoungCommonDivisor_mul_reducedRight h k
    have hfactorR : (k : ℝ) =
        (hughesYoungCommonDivisor h k : ℝ) *
          (hughesYoungReducedRight h k : ℝ) := by
      exact_mod_cast hfactor.symm
    push_cast
    rw [hfactorR]
    field_simp [hd.ne']
  unfold hughesYoungGCDBoundaryCutoff
  rw [hscale]
  by_cases hone : hughesYoungReducedRight h k * n = 1
  · rw [if_pos hone, hone]
    exact hughesYoungDyadicStep_eq_one (by norm_num)
  · rw [if_neg hone]
    apply hughesYoungDyadicStep_nat_eq_zero_of_two_le
    have hright := hughesYoungReducedRight_pos hh hk
    have hprod : 0 < hughesYoungReducedRight h k * n := Nat.mul_pos hright hn
    omega

/-- The double endpoint piece contains only the reduced point `(1,1)`, which
is diagonal.  Consequently it contributes nothing to the off-diagonal sum. -/
theorem finiteQuadraticDivisorOffDiagonalPiece_boundary_boundary_eq_zero
    {h k M N : ℕ} (hh : 0 < h) (hk : 0 < k) (F : ℝ → ℝ → ℂ) :
    finiteQuadraticDivisorOffDiagonalPiece h k M N F
        (hughesYoungGCDBoundaryCutoff h k)
        (hughesYoungGCDBoundaryCutoff h k) = 0 := by
  classical
  unfold finiteQuadraticDivisorOffDiagonalPiece
    finiteQuadraticDivisorOffDiagonal
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  change (if quadraticDivisorShift h k m n = 0 then 0 else
    divisorWeight m * divisorWeight n *
      ((hughesYoungGCDBoundaryCutoff h k (((h * m : ℕ) : ℝ)) : ℂ) *
        (hughesYoungGCDBoundaryCutoff h k (((k * n : ℕ) : ℝ)) : ℂ) *
        F (((h * m : ℕ) : ℝ)) (((k * n : ℕ) : ℝ)))) = 0
  rw [hughesYoungGCDBoundaryCutoff_left_nat hh hm0,
    hughesYoungGCDBoundaryCutoff_right_nat hh hk hn0]
  by_cases hleft : hughesYoungReducedLeft h k * m = 1
  · by_cases hright : hughesYoungReducedRight h k * n = 1
    · have hreduced : quadraticDivisorShift
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) m n = 0 := by
        unfold quadraticDivisorShift
        have heq : hughesYoungReducedLeft h k * m =
            hughesYoungReducedRight h k * n := hleft.trans hright.symm
        exact sub_eq_zero.mpr (by exact_mod_cast heq)
      have horiginal : quadraticDivisorShift h k m n = 0 :=
        (quadraticDivisorShift_eq_zero_iff_reduced hh).2 hreduced
      simp [horiginal]
    · simp [hleft, hright]
  · simp [hleft]

theorem hughesYoungGCDCutoff_partition
    {h k K : ℕ} (hh : 0 < h) {x : ℝ}
    (hxUpper : x / hughesYoungCommonDivisor h k ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    hughesYoungGCDBoundaryCutoff h k x +
        (∑ i ∈ Finset.range (K + 1),
          hughesYoungDyadicCutoffAt
            (hughesYoungCommonDivisor h k * hughesYoungDyadicScale i) x) = 1 := by
  have hd : 0 < hughesYoungCommonDivisor h k := by
    exact_mod_cast Nat.gcd_pos_of_pos_left k hh
  have hcut (i : ℕ) :
      hughesYoungDyadicCutoffAt
          (hughesYoungCommonDivisor h k * hughesYoungDyadicScale i) x =
        hughesYoungDyadicCutoffAt (hughesYoungDyadicScale i)
          (x / hughesYoungCommonDivisor h k) := by
    unfold hughesYoungDyadicCutoffAt
    congr 1
    field_simp [hd.ne']
  simp_rw [hcut]
  exact hughesYoungDyadicStep_add_sum_cutoff_eq_one hxUpper

/-- Exact reconstruction of the original finite Hughes--Young off-diagonal
box by the boundary pieces and all smooth dyadic boxes. -/
theorem hughesYoungFiniteOffDiagonalBox_eq_boundary_add_dyadic
    (T c H : ℝ) {h k M N K₁ K₂ : ℕ}
    (hh : 0 < h) (hk : 0 < k)
    (hM : (((hughesYoungReducedLeft h k) * M : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K₁ + 1))
    (hN : (((hughesYoungReducedRight h k) * N : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K₂ + 1)) :
    hughesYoungFiniteOffDiagonalBox T c H h k M N =
      finiteQuadraticDivisorOffDiagonalPiece h k M N
        (hughesYoungIntegratedSourceWeight T c H h k)
        (hughesYoungGCDBoundaryCutoff h k)
        (hughesYoungGCDBoundaryCutoff h k) +
      (∑ j ∈ Finset.range (K₂ + 1),
        finiteQuadraticDivisorOffDiagonalPiece h k M N
          (hughesYoungIntegratedSourceWeight T c H h k)
          (hughesYoungGCDBoundaryCutoff h k)
          (hughesYoungDyadicCutoffAt
            (hughesYoungCommonDivisor h k * hughesYoungDyadicScale j))) +
      (∑ i ∈ Finset.range (K₁ + 1),
        finiteQuadraticDivisorOffDiagonalPiece h k M N
          (hughesYoungIntegratedSourceWeight T c H h k)
          (hughesYoungDyadicCutoffAt
            (hughesYoungCommonDivisor h k * hughesYoungDyadicScale i))
          (hughesYoungGCDBoundaryCutoff h k)) +
      (∑ i ∈ Finset.range (K₁ + 1),
        ∑ j ∈ Finset.range (K₂ + 1),
          hughesYoungLocalizedOffDiagonalBox T c H
            (hughesYoungDyadicScale i) (hughesYoungDyadicScale j)
            h k M N) := by
  have hsource : hughesYoungFiniteOffDiagonalBox T c H h k M N =
      finiteQuadraticDivisorOffDiagonal h k M N
        (fun x y => hughesYoungIntegratedSourceWeight T c H h k x y) := by
    unfold hughesYoungFiniteOffDiagonalBox
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hshift : quadraticDivisorShift h k m n = 0
    · simp [hshift]
    · simp only [hshift, if_false]
      rw [integral_hughesYoungFiniteArithmeticTerm_eq_source T c H hh hk]
  rw [hsource, finiteQuadraticDivisorOffDiagonal_eq_partition h k M N
    (hughesYoungIntegratedSourceWeight T c H h k)
    (hughesYoungGCDBoundaryCutoff h k) (hughesYoungGCDBoundaryCutoff h k)
    (fun i => hughesYoungDyadicCutoffAt
      (hughesYoungCommonDivisor h k * hughesYoungDyadicScale i))
    (fun j => hughesYoungDyadicCutoffAt
      (hughesYoungCommonDivisor h k * hughesYoungDyadicScale j))
    (Finset.range (K₁ + 1)) (Finset.range (K₂ + 1))]
  · rw [finiteQuadraticDivisorOffDiagonalPiece_add_left,
      finiteQuadraticDivisorOffDiagonalPiece_add_right,
      finiteQuadraticDivisorOffDiagonalPiece_add_right,
      finiteQuadraticDivisorOffDiagonalPiece_sum_right,
      finiteQuadraticDivisorOffDiagonalPiece_sum_left]
    rw [finiteQuadraticDivisorOffDiagonalPiece_sum_left]
    simp_rw [finiteQuadraticDivisorOffDiagonalPiece_sum_right]
    have hboxes :
        (∑ i ∈ Finset.range (K₁ + 1),
          ∑ j ∈ Finset.range (K₂ + 1),
            finiteQuadraticDivisorOffDiagonalPiece h k M N
              (hughesYoungIntegratedSourceWeight T c H h k)
              (hughesYoungDyadicCutoffAt
                (hughesYoungCommonDivisor h k * hughesYoungDyadicScale i))
              (hughesYoungDyadicCutoffAt
                (hughesYoungCommonDivisor h k * hughesYoungDyadicScale j))) =
        ∑ i ∈ Finset.range (K₁ + 1),
          ∑ j ∈ Finset.range (K₂ + 1),
            hughesYoungLocalizedOffDiagonalBox T c H
              (hughesYoungDyadicScale i) (hughesYoungDyadicScale j)
              h k M N := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact finiteQuadraticDivisorOffDiagonalPiece_cutoff_eq_localizedBox
        T c H h k M N i j
    rw [hboxes]
    ring
  · intro m hm
    apply hughesYoungGCDCutoff_partition hh
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hhScale : hughesYoungReducedLeft h k * m ≤
        hughesYoungReducedLeft h k * M :=
      Nat.mul_le_mul_left (hughesYoungReducedLeft h k) hmM
    have hhScaleR : (((hughesYoungReducedLeft h k) * m : ℕ) : ℝ) ≤
        (((hughesYoungReducedLeft h k) * M : ℕ) : ℝ) := by
      exact_mod_cast hhScale
    have hdiv : ((h * m : ℕ) : ℝ) / hughesYoungCommonDivisor h k =
        (((hughesYoungReducedLeft h k) * m : ℕ) : ℝ) := by
      have hmul : hughesYoungCommonDivisor h k *
          (hughesYoungReducedLeft h k * m) = h * m := by
        rw [← Nat.mul_assoc, hughesYoungCommonDivisor_mul_reducedLeft]
      have hmulR : (hughesYoungCommonDivisor h k : ℝ) *
          (((hughesYoungReducedLeft h k) * m : ℕ) : ℝ) =
          ((h * m : ℕ) : ℝ) := by exact_mod_cast hmul
      rw [← hmulR]
      field_simp [show (hughesYoungCommonDivisor h k : ℝ) ≠ 0 by
        exact_mod_cast (hughesYoungCommonDivisor_pos hh).ne']
    rw [hdiv]
    exact hhScaleR.trans hM
  · intro n hn
    apply hughesYoungGCDCutoff_partition hh
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hkScale : hughesYoungReducedRight h k * n ≤
        hughesYoungReducedRight h k * N :=
      Nat.mul_le_mul_left (hughesYoungReducedRight h k) hnN
    have hkScaleR : (((hughesYoungReducedRight h k) * n : ℕ) : ℝ) ≤
        (((hughesYoungReducedRight h k) * N : ℕ) : ℝ) := by
      exact_mod_cast hkScale
    have hdiv : ((k * n : ℕ) : ℝ) / hughesYoungCommonDivisor h k =
        (((hughesYoungReducedRight h k) * n : ℕ) : ℝ) := by
      have hmul : hughesYoungCommonDivisor h k *
          (hughesYoungReducedRight h k * n) = k * n := by
        rw [← Nat.mul_assoc, hughesYoungCommonDivisor_mul_reducedRight]
      have hmulR : (hughesYoungCommonDivisor h k : ℝ) *
          (((hughesYoungReducedRight h k) * n : ℕ) : ℝ) =
          ((k * n : ℕ) : ℝ) := by exact_mod_cast hmul
      rw [← hmulR]
      field_simp [show (hughesYoungCommonDivisor h k : ℝ) ≠ 0 by
        exact_mod_cast (hughesYoungCommonDivisor_pos hh).ne']
    rw [hdiv]
    exact hkScaleR.trans hN

end RiemannZeta.GuthMaynard
