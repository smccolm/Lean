import RiemannZeta.GuthMaynard.HughesYoungCentralTail
import RiemannZeta.GuthMaynard.HughesYoungCompleteCentralContinuation
import RiemannZeta.GuthMaynard.HughesYoungPositiveScaleCentralSeries

open Complex MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Cancellation-preserving reassembly of the Hughes--Young central family

The DFI theorem is applied only on `hughesYoungActiveLargeDFIBoxes`, but the
source central term is evaluated after restoring the complementary active
boxes.  This file keeps that restoration as an exact identity, before any
norm is taken.
-/

/-- Exact decomposition of a finite signed integer interval, with its zero
term deleted, into positive and negative natural-number ranges.  This is the
index-level form of the two signed branches preceding Hughes--Young (83). -/
theorem sum_int_Icc_ite_zero_eq_positive_add_negative
    {A : Type*} [AddCommMonoid A] (F : ℤ → A) (L U : ℕ) :
    (∑ r ∈ Finset.Icc (-(L : ℤ)) (U : ℤ),
        if r = 0 then 0 else F r) =
      (∑ n ∈ Finset.Icc 1 U, F (n : ℤ)) +
        ∑ n ∈ Finset.Icc 1 L, F (-(n : ℤ)) := by
  classical
  let s := Finset.Icc (-(L : ℤ)) (U : ℤ)
  let snz := s.filter fun r => r ≠ 0
  let spos := snz.filter fun r => 0 < r
  let sneg := snz.filter fun r => r < 0
  have hnz : (∑ r ∈ s, if r = 0 then 0 else F r) = ∑ r ∈ snz, F r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases hr : r = 0 <;> simp [hr]
  have hsplit : snz = spos ∪ sneg := by
    ext r
    constructor
    · intro hr
      have hr0 : r ≠ 0 := (Finset.mem_filter.mp hr).2
      by_cases hp : 0 < r
      · exact Finset.mem_union.mpr <|
          Or.inl <| Finset.mem_filter.mpr ⟨hr, hp⟩
      · have hn : r < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr0
        exact Finset.mem_union.mpr <|
          Or.inr <| Finset.mem_filter.mpr ⟨hr, hn⟩
    · intro hr
      rcases Finset.mem_union.mp hr with hp | hn
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hn).1
  have hdisjoint : Disjoint spos sneg := by
    rw [Finset.disjoint_left]
    intro r hp hn
    simp only [spos, sneg, Finset.mem_filter] at hp hn
    omega
  have hpos : (∑ r ∈ spos, F r) =
      ∑ n ∈ Finset.Icc 1 U, F (n : ℤ) := by
    refine Finset.sum_bij' (fun r _ => r.toNat) (fun n _ => (n : ℤ))
      ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [spos, snz, s, Finset.mem_filter, Finset.mem_Icc] at hr
      have hcast : (r.toNat : ℤ) = r := by
        rw [Int.ofNat_toNat, max_eq_left (le_of_lt hr.2)]
      simp only [Finset.mem_Icc]
      constructor
      · omega
      · have hbound : (r.toNat : ℤ) ≤ (U : ℤ) := by
          rw [hcast]
          exact hr.1.1.2
        exact_mod_cast hbound
    · intro n hn
      simp only [spos, snz, s, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    · intro r hr
      simp only [spos, Finset.mem_filter] at hr
      change (r.toNat : ℤ) = r
      rw [Int.ofNat_toNat, max_eq_left (le_of_lt hr.2)]
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp
    · intro r hr
      simp only [spos, Finset.mem_filter] at hr
      change F r = F (r.toNat : ℤ)
      congr 1
      rw [Int.ofNat_toNat, max_eq_left (le_of_lt hr.2)]
  have hneg : (∑ r ∈ sneg, F r) =
      ∑ n ∈ Finset.Icc 1 L, F (-(n : ℤ)) := by
    refine Finset.sum_bij' (fun r _ => r.natAbs) (fun n _ => -(n : ℤ))
      ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [sneg, snz, s, Finset.mem_filter, Finset.mem_Icc] at hr
      have hcast : -(r.natAbs : ℤ) = r := by
        rw [Int.natCast_natAbs, abs_of_neg hr.2, neg_neg]
      simp only [Finset.mem_Icc]
      constructor
      · have : r.natAbs ≠ 0 := by
          intro hz
          apply hr.1.2
          exact Int.natAbs_eq_zero.mp hz
        omega
      · exact_mod_cast (show (r.natAbs : ℤ) ≤ (L : ℤ) by omega)
    · intro n hn
      simp only [sneg, snz, s, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    · intro r hr
      simp only [sneg, Finset.mem_filter] at hr
      change -(r.natAbs : ℤ) = r
      rw [Int.natCast_natAbs, abs_of_neg hr.2, neg_neg]
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp
    · intro r hr
      simp only [sneg, Finset.mem_filter] at hr
      change F r = F (-(r.natAbs : ℤ))
      congr 1
      rw [Int.natCast_natAbs, abs_of_neg hr.2, neg_neg]
  rw [hnz, hsplit, Finset.sum_union hdisjoint, hpos, hneg]

/-- One finite complete central box is exactly the sum of its positive and
negative natural-shift branches.  No triangle inequality or absolute value
has been used. -/
theorem hughesYoungFiniteCompleteSignedCentralBox_eq_positive_add_negative
    (T c u X Y : ℝ) (h k a b M N : ℕ) :
    hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k a b M N =
      (∑ r ∈ Finset.Icc 1 (a * M),
        dfiSignedCentralSeries a b (r : ℤ)
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (r : ℤ))) +
      ∑ r ∈ Finset.Icc 1 (b * N),
        dfiSignedCentralSeries a b (-(r : ℤ))
          (hughesYoungReducedCleanedShiftWeight T c u X Y h k (-(r : ℤ))) := by
  unfold hughesYoungFiniteCompleteSignedCentralBox
    hughesYoungShiftInterval
  exact sum_int_Icc_ite_zero_eq_positive_add_negative
    (fun r => dfiSignedCentralSeries a b r
      (hughesYoungReducedCleanedShiftWeight T c u X Y h k r))
    (b * N) (a * M)

/-- The complete nonzero-shift DFI central family over every active dyadic
box.  The compact Mellin integral and all three finite source sums remain in
their original order. -/
noncomputable def hughesYoungActiveIntegratedCompleteCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complete signed-central family on the active boxes where the
optimized DFI theorem is not invoked.  This is the exact complementary term
which must be subtracted after evaluating the full source family. -/
noncomputable def hughesYoungActiveNonLargeDFIIntegratedCompleteCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveNonLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact restoration of the complementary active boxes.  This is the
finite Hughes--Young cancellation step immediately preceding the global
equation-(84) evaluation. -/
theorem hughesYoungActiveIntegratedCompleteCentral_eq_large_add_nonLarge
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveIntegratedCompleteCentral T R K =
      hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K +
        hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K := by
  classical
  unfold hughesYoungActiveIntegratedCompleteCentral
    hughesYoungActiveLargeDFIIntegratedCompleteCentral
    hughesYoungActiveNonLargeDFIIntegratedCompleteCentral
    hughesYoungActiveLargeDFIBoxes
    hughesYoungActiveNonLargeDFIBoxes
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (Finset.sum_filter_add_sum_filter_not
    (s := hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
    (p := fun ij =>
      0 < ij.1 ∧ 0 < ij.2 ∧
      (hughesYoungReducedLeft h k : ℝ) ≤
        2 * hughesYoungFullDyadicScale ij.1 ∧
      (hughesYoungReducedRight h k : ℝ) ≤
        2 * hughesYoungFullDyadicScale ij.2 ∧
      64 ≤ hughesYoungDFIOptimalU P
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) ∧
      hughesYoungFullDyadicScale ij.1 ≤
        4 * hughesYoungFullDyadicScale ij.2 ∧
      hughesYoungFullDyadicScale ij.2 ≤
        4 * hughesYoungFullDyadicScale ij.1)
    (f := fun ij =>
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2))).symm

/-- Solved form used by the DFI consumer: the large-box central term is the
full cancellation-preserving source family minus its explicit active
complement. -/
theorem hughesYoungActiveLargeDFIIntegratedCompleteCentral_eq_full_sub_nonLarge
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K =
      hughesYoungActiveIntegratedCompleteCentral T R K -
        hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K := by
  rw [hughesYoungActiveIntegratedCompleteCentral_eq_large_add_nonLarge]
  ring

/-! ## Source-faithful regular-box reassembly

The preceding all-active identity is useful algebraically, but the DFI
theorem is never applied to either isolated index-zero boundary.  The next
objects therefore perform the restoration on the exact regular family.
This prevents a boundary central integral from being silently identified
with the Hughes--Young equation-(84) source.
-/

/-- Active ordinary dyadic boxes, excluding both isolated lower endpoints. -/
noncomputable def hughesYoungCentralRegularBoxes
    (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungActiveDyadicBoxes a b R K).filter fun ij =>
    0 < ij.1 ∧ 0 < ij.2

/-- Regular active boxes on which the optimized large-DFI predicate fails. -/
noncomputable def hughesYoungCentralRegularNonLargeBoxes
    (P : ℝ) (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungCentralRegularBoxes a b R K).filter fun ij =>
    ¬ ((a : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.1 ∧
      (b : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.2 ∧
      64 ≤ hughesYoungDFIOptimalU P
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) ∧
      hughesYoungFullDyadicScale ij.1 ≤
        4 * hughesYoungFullDyadicScale ij.2 ∧
      hughesYoungFullDyadicScale ij.2 ≤
        4 * hughesYoungFullDyadicScale ij.1)

/-- The complete central family over precisely the regular active boxes. -/
noncomputable def hughesYoungActiveRegularIntegratedCompleteCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungCentralRegularBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The exact regular complement of the large-DFI central family. -/
noncomputable def hughesYoungActiveRegularNonLargeIntegratedCompleteCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungCentralRegularNonLargeBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact regular restoration.  The first summand is definitionally the
large-DFI family; the second contains every and only remaining regular
active box. -/
theorem hughesYoungActiveRegularIntegratedCompleteCentral_eq_large_add_nonLarge
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveRegularIntegratedCompleteCentral T R K =
      hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K +
        hughesYoungActiveRegularNonLargeIntegratedCompleteCentral T P R K := by
  classical
  unfold hughesYoungActiveRegularIntegratedCompleteCentral
    hughesYoungActiveLargeDFIIntegratedCompleteCentral
    hughesYoungActiveRegularNonLargeIntegratedCompleteCentral
    hughesYoungActiveLargeDFIBoxes
    hughesYoungCentralRegularNonLargeBoxes
    hughesYoungCentralRegularBoxes
  simp only [Finset.filter_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  let p : ℕ × ℕ → Prop := fun ij =>
    (hughesYoungReducedLeft h k : ℝ) ≤
        2 * hughesYoungFullDyadicScale ij.1 ∧
      (hughesYoungReducedRight h k : ℝ) ≤
        2 * hughesYoungFullDyadicScale ij.2 ∧
      64 ≤ hughesYoungDFIOptimalU P
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) ∧
      hughesYoungFullDyadicScale ij.1 ≤
        4 * hughesYoungFullDyadicScale ij.2 ∧
      hughesYoungFullDyadicScale ij.2 ≤
        4 * hughesYoungFullDyadicScale ij.1
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).filter
        fun ij => 0 < ij.1 ∧ 0 < ij.2)
    (p := p)
    (f := fun ij =>
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2))
  simpa only [p, Finset.filter_filter, and_assoc] using hsplit.symm

/-- Solved regular form used in the eventual equation-(84) consumer. -/
theorem hughesYoungActiveLargeDFIIntegratedCompleteCentral_eq_regular_sub_nonLarge
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K =
      hughesYoungActiveRegularIntegratedCompleteCentral T R K -
        hughesYoungActiveRegularNonLargeIntegratedCompleteCentral T P R K := by
  rw [hughesYoungActiveRegularIntegratedCompleteCentral_eq_large_add_nonLarge]
  ring

/-! ## Restoration of the complete finite dyadic rectangle -/

/-- The actual finite-depth reduced Mellin weight obtained by summing the
complete Hughes--Young dyadic rectangle.  This is a source object, not an
asymptotic proxy. -/
noncomputable def hughesYoungFiniteReassembledReducedMellinWeight
    (T t c u : ℝ) (h k K : ℕ) (x y : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (K + 2), ∑ j ∈ Finset.range (K + 2),
    hughesYoungFullDyadicReducedMellinWeight T t c u h k i j x y

/-- Exact finite endpoint formula for the reassembled Mellin weight.  It
retains both the upper terminal cutoff and the lower endpoint subtraction. -/
theorem hughesYoungFiniteReassembledReducedMellinWeight_eq_endpoint
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (K : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hughesYoungFiniteReassembledReducedMellinWeight T t c u h k K x y =
      hughesYoungReducedMellinScaleConstant T t c u h k *
        ((hughesYoungDyadicStep
            (x / hughesYoungDyadicRatio ^ (K + 1)) -
          hughesYoungDyadicStep
            (x * hughesYoungDyadicRatio) : ℝ) : ℂ) *
        ((hughesYoungDyadicStep
            (y / hughesYoungDyadicRatio ^ (K + 1)) -
          hughesYoungDyadicStep
            (y * hughesYoungDyadicRatio) : ℝ) : ℂ) *
        (x : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (y : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) := by
  exact sum_range_hughesYoungFullDyadicReducedMellinWeight_eq
    T t c u hh hk K hx hy

/-- The locally finite nonnegative-index dyadic family after its upper
endpoint has been sent to infinity.  The genuine lower cutoff remains. -/
noncomputable def hughesYoungLowerCompleteReducedMellinWeight
    (T t c u : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  if 0 < x ∧ 0 < y then
    hughesYoungReducedMellinScaleConstant T t c u h k *
      ((1 - hughesYoungDyadicStep
        (x * hughesYoungDyadicRatio) : ℝ) : ℂ) *
      ((1 - hughesYoungDyadicStep
        (y * hughesYoungDyadicRatio) : ℝ) : ℂ) *
      (x : ℂ) ^ (-(afeCriticalPoint t +
        ((c : ℂ) + (u : ℂ) * I))) *
      (y : ℂ) ^ (-(afeCriticalPoint (-t) +
        ((c : ℂ) + (u : ℂ) * I)))
  else 0

/-- The exact lower-end correction between the pure positive-quadrant
Mellin monomial and the complete nonnegative-index dyadic family. -/
noncomputable def hughesYoungLowerBoundaryReducedMellinCorrection
    (T t c u : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  hughesYoungPureReducedMellinWeight T t c u h k x y -
    hughesYoungLowerCompleteReducedMellinWeight T t c u h k x y

/-- The exact terminal correction between the infinite nonnegative-index
family and its finite depth-`K` rectangle. -/
noncomputable def hughesYoungTerminalReducedMellinCorrection
    (T t c u : ℝ) (h k K : ℕ) (x y : ℝ) : ℂ :=
  hughesYoungLowerCompleteReducedMellinWeight T t c u h k x y -
    hughesYoungFiniteReassembledReducedMellinWeight T t c u h k K x y

/-- Exact two-endpoint decomposition of the finite Hughes--Young source.
This algebraic identity is deliberately global; the preceding endpoint
formula identifies both correction terms with the actual smooth cutoffs. -/
theorem hughesYoungFiniteReassembledReducedMellinWeight_eq_pure_sub_corrections
    (T t c u : ℝ) (h k K : ℕ) :
    hughesYoungFiniteReassembledReducedMellinWeight T t c u h k K =
      fun x y => hughesYoungPureReducedMellinWeight T t c u h k x y -
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k x y -
        hughesYoungTerminalReducedMellinCorrection
          T t c u h k K x y := by
  funext x y
  unfold hughesYoungLowerBoundaryReducedMellinCorrection
    hughesYoungTerminalReducedMellinCorrection
  ring

/-- Every dyadic scale occurring before depth `K + 2` is bounded by the
last ordinary scale in that rectangle. -/
theorem hughesYoungFullDyadicScale_le_terminal
    {i K : ℕ} (hi : i < K + 2) :
    hughesYoungFullDyadicScale i ≤
      hughesYoungFullDyadicScale (K + 1) := by
  cases i with
  | zero =>
      rw [hughesYoungFullDyadicScale]
      have hright : 1 ≤ hughesYoungFullDyadicScale (K + 1) :=
        one_le_hughesYoungFullDyadicScale_succ K
      exact ((div_le_one hughesYoungDyadicRatio_pos).2
        one_lt_hughesYoungDyadicRatio.le).trans hright
  | succ i =>
      simp only [hughesYoungFullDyadicScale]
      unfold hughesYoungDyadicScale
      apply pow_le_pow_right₀ one_lt_hughesYoungDyadicRatio.le
      omega

/-- Corresponding monotonicity of the natural finite-box cutoff. -/
theorem hughesYoungFullDyadicBound_le_terminal
    {i K : ℕ} (hi : i < K + 2) :
    hughesYoungFullDyadicBound i ≤
      hughesYoungFullDyadicBound (K + 1) := by
  unfold hughesYoungFullDyadicBound
  exact Nat.ceil_mono (by
    gcongr
    exact hughesYoungFullDyadicScale_le_terminal hi)

/-- A localized complete central box may be enlarged to any common divisor
rectangle covering its two natural cutoffs.  Every newly introduced shift
is zero by the literal DFI support from equation (2). -/
theorem hughesYoungFiniteCompleteSignedCentralBox_eq_enlarged
    (T c u X Y : ℝ) (h k a b M N B : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hb : 0 < b)
    (hMX : 2 * X ≤ M) (hNY : 2 * Y ≤ N)
    (hMB : M ≤ B) (hNB : N ≤ B) :
    hughesYoungFiniteCompleteSignedCentralBox T c u X Y h k a b M N =
      ∑ r ∈ hughesYoungShiftInterval a b B B,
        if r = 0 then 0 else
          dfiSignedCentralSeries a b r
            (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) := by
  unfold hughesYoungFiniteCompleteSignedCentralBox
  apply Finset.sum_subset
  · intro r hr
    simp only [hughesYoungShiftInterval, Finset.mem_Icc] at hr ⊢
    have hleft : b * N ≤ b * B := Nat.mul_le_mul_left b hNB
    have hright : a * M ≤ a * B := Nat.mul_le_mul_left a hMB
    constructor
    · have hcast : ((b * N : ℕ) : ℤ) ≤ ((b * B : ℕ) : ℤ) := by
        exact_mod_cast hleft
      exact (neg_le_neg hcast).trans hr.1
    · exact hr.2.trans (by exact_mod_cast hright)
  · intro r _hrBig hrSmall
    simp only [hughesYoungShiftInterval, Finset.mem_Icc] at hrSmall
    by_cases hr0 : r = 0
    · simp [hr0]
    simp only [hr0, if_false]
    apply dfiSignedCentralSeries_reducedCleaned_eq_zero_of_outside_support_of_pos
      hX hY h k a b hr0
    constructor
    · intro hrPos
      have hrInt : ((a * M : ℕ) : ℤ) < r := by
        by_contra hnlt
        apply hrSmall
        constructor
        · have hz : -((b * N : ℕ) : ℤ) ≤ 0 := by omega
          exact hz.trans hrPos
        · omega
      have hrAM : (a * M : ℕ) < r.toNat := by
        have hcast : (r.toNat : ℤ) = r := by
          rw [Int.ofNat_toNat, max_eq_left hrPos]
        have hrInt' : ((a * M : ℕ) : ℤ) < (r.toNat : ℤ) := by
          simpa only [hcast] using hrInt
        exact_mod_cast hrInt'
      have hMle : M ≤ a * M := by
        have hraw := Nat.mul_le_mul_right M ha
        omega
      have hnat : M < r.natAbs := by
        have habs : r.natAbs = r.toNat := by
          have hleft : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg hrPos
          have hright : (r.toNat : ℤ) = r := by
            rw [Int.ofNat_toNat, max_eq_left hrPos]
          exact_mod_cast hleft.trans hright.symm
        rw [habs]
        exact hMle.trans_lt hrAM
      exact hMX.trans_lt (by exact_mod_cast hnat)
    · intro hrNeg
      have hrInt : ((b * N : ℕ) : ℤ) < -r := by
        by_contra hnlt
        apply hrSmall
        constructor
        · omega
        · have hrUpper : r ≤ ((a * M : ℕ) : ℤ) := by omega
          exact hrUpper
      have hrBN : (b * N : ℕ) < (-r).toNat := by
        have hnegNonneg : 0 ≤ -r := by omega
        have hcast : ((-r).toNat : ℤ) = -r := by
          rw [Int.ofNat_toNat, max_eq_left hnegNonneg]
        have hrInt' : ((b * N : ℕ) : ℤ) < ((-r).toNat : ℤ) := by
          simpa only [hcast] using hrInt
        exact_mod_cast hrInt'
      have hNle : N ≤ b * N := by
        have hraw := Nat.mul_le_mul_right N hb
        omega
      have hraw : N < (-r).natAbs := by
        have hneg0 : 0 ≤ -r := by omega
        have habs : (-r).natAbs = (-r).toNat := by
          have hleft : ((-r).natAbs : ℤ) = -r :=
            Int.natAbs_of_nonneg hneg0
          have hright : ((-r).toNat : ℤ) = -r := by
            rw [Int.ofNat_toNat, max_eq_left hneg0]
          exact_mod_cast hleft.trans hright.symm
        rw [habs]
        exact hNle.trans_lt hrBN
      have hnat : N < r.natAbs := by
        simpa only [Int.natAbs_neg] using hraw
      exact hNY.trans_lt (by exact_mod_cast hnat)

/-- Every dyadic box retained by the finite source depth, before the
physical product cutoff is imposed.  Index zero is deliberately included:
it is the lower-end correction in the exact telescoping partition. -/
noncomputable def hughesYoungCompleteDyadicRectangle
    (K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (K + 2)).product (Finset.range (K + 2))

/-- The boxes in the complete finite rectangle omitted by the physical
product cutoff. -/
noncomputable def hughesYoungInactiveDyadicBoxes
    (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungCompleteDyadicRectangle K).filter fun ij =>
    ¬ (hughesYoungFullDyadicScale ij.1 *
      hughesYoungFullDyadicScale ij.2 ≤ ((a * b * R : ℕ) : ℝ))

/-- Complete cancellation-preserving central family on the finite
rectangular dyadic partition. -/
noncomputable def hughesYoungRectangularIntegratedCompleteCentral
    (T : ℝ) (K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact central family on the inactive complement of the source
rectangle. -/
noncomputable def hughesYoungInactiveIntegratedCompleteCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact active/inactive partition of the complete finite source
rectangle, before any norm or tail estimate is introduced. -/
theorem hughesYoungRectangularIntegratedCompleteCentral_eq_active_add_inactive
    (T : ℝ) (R K : ℕ) :
    hughesYoungRectangularIntegratedCompleteCentral T K =
      hughesYoungActiveIntegratedCompleteCentral T R K +
        hughesYoungInactiveIntegratedCompleteCentral T R K := by
  classical
  unfold hughesYoungRectangularIntegratedCompleteCentral
    hughesYoungActiveIntegratedCompleteCentral
    hughesYoungInactiveIntegratedCompleteCentral
    hughesYoungActiveDyadicBoxes
    hughesYoungInactiveDyadicBoxes
    hughesYoungCompleteDyadicRectangle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (Finset.sum_filter_add_sum_filter_not
    (s := (Finset.range (K + 2)).product (Finset.range (K + 2)))
    (p := fun ij => hughesYoungFullDyadicScale ij.1 *
      hughesYoungFullDyadicScale ij.2 ≤
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ))
    (f := fun ij =>
      hughesYoungIntegratedFiniteCompleteSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2))).symm

/-- Source-order solved form: the large DFI central contribution is the
complete finite dyadic source minus the inactive and active-nonlarge
corrections. -/
theorem hughesYoungActiveLargeDFIIntegratedCompleteCentral_eq_rectangular_sub_corrections
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveLargeDFIIntegratedCompleteCentral T P R K =
      hughesYoungRectangularIntegratedCompleteCentral T K -
        hughesYoungInactiveIntegratedCompleteCentral T R K -
        hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K := by
  rw [hughesYoungRectangularIntegratedCompleteCentral_eq_active_add_inactive,
    hughesYoungActiveIntegratedCompleteCentral_eq_large_add_nonLarge]
  ring

end RiemannZeta.GuthMaynard
