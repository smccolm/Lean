import Tao2026.SpecializedFourierPartition
import Tao2026.FourierApproximation

/-!
# Natural cores of real order-convex intervals

This module starts the endpoint reduction from Tao's arbitrary measurable
order-convex interval to the natural half-open interval consumed by the
specialized Fourier theorem.  The discrete prime sum is preserved exactly.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Tao2026

noncomputable section

/-- Changing a measurable integration set costs the uniform norm bound times
the real measure of the symmetric difference. -/
theorem norm_setIntegral_sub_setIntegral_le_symmDiff
    {f : ℝ → ℂ} {s t : Set ℝ} {C : ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : IntegrableOn f s) (hft : IntegrableOn f t)
    (hsfinite : volume s ≠ ∞) (htfinite : volume t ≠ ∞)
    (hC : ∀ x ∈ symmDiff s t, ‖f x‖ ≤ C) :
    ‖(∫ x in s, f x) - ∫ x in t, f x‖ ≤
      C * volume.real (symmDiff s t) := by
  have hsDiffFinite : volume (s \ t) < ∞ :=
    (lt_top_iff_ne_top).2 (measure_ne_top_of_subset diff_subset hsfinite)
  have htDiffFinite : volume (t \ s) < ∞ :=
    (lt_top_iff_ne_top).2 (measure_ne_top_of_subset diff_subset htfinite)
  have hsBound : ‖∫ x in s \ t, f x‖ ≤ C * volume.real (s \ t) := by
    apply norm_setIntegral_le_of_norm_le_const hsDiffFinite
    intro x hx
    exact hC x (Set.mem_symmDiff.mpr (Or.inl hx))
  have htBound : ‖∫ x in t \ s, f x‖ ≤ C * volume.real (t \ s) := by
    apply norm_setIntegral_le_of_norm_le_const htDiffFinite
    intro x hx
    exact hC x (Set.mem_symmDiff.mpr (Or.inr hx))
  have hsDecomp := integral_inter_add_diff ht hfs
  have htDecomp := integral_inter_add_diff hs hft
  have hdecomp :
      (∫ x in s, f x) - ∫ x in t, f x =
        (∫ x in s \ t, f x) - ∫ x in t \ s, f x := by
    rw [← hsDecomp, ← htDecomp]
    rw [inter_comm]
    ring
  rw [hdecomp]
  calc
    ‖(∫ x in s \ t, f x) - ∫ x in t \ s, f x‖ ≤
        ‖∫ x in s \ t, f x‖ + ‖∫ x in t \ s, f x‖ := norm_sub_le _ _
    _ ≤ C * volume.real (s \ t) + C * volume.real (t \ s) :=
      add_le_add hsBound htBound
    _ = C * volume.real (symmDiff s t) := by
      rw [measureReal_symmDiff_eq hs ht hsfinite htfinite]
      ring

/-- Natural points of a real set inside one natural dyadic block. -/
noncomputable def naturalPointsInDyadicInterval
    (P : ℕ) (I : Set ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc P (2 * P)).filter fun n => (n : ℝ) ∈ I

/-- Left endpoint of the natural core, when it is nonempty. -/
noncomputable def naturalAnalyticCoreStart
    (P : ℕ) (I : Set ℝ)
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) : ℕ :=
  (naturalPointsInDyadicInterval P I).min' hne

/-- Right endpoint used by the analytic core.  Capping at `2P` keeps the
real half-open interval inside Tao's ambient dyadic block; the only possibly
discarded natural point is the composite endpoint `2P`. -/
noncomputable def naturalAnalyticCoreStop
    (P : ℕ) (I : Set ℝ)
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) : ℕ :=
  min ((naturalPointsInDyadicInterval P I).max' hne + 1) (2 * P)

theorem mem_naturalPointsInDyadicInterval
    {P n : ℕ} {I : Set ℝ} :
    n ∈ naturalPointsInDyadicInterval P I ↔
      P ≤ n ∧ n ≤ 2 * P ∧ (n : ℝ) ∈ I := by
  simp [naturalPointsInDyadicInterval, and_assoc]

/-- The natural points of an order-convex real set form exactly one natural
half-open interval, from their minimum through one past their maximum. -/
theorem naturalPointsInDyadicInterval_eq_Ico
    {P : ℕ} {I : Set ℝ} (hconn : OrdConnected I)
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    naturalPointsInDyadicInterval P I =
      Finset.Ico
        ((naturalPointsInDyadicInterval P I).min' hne)
        ((naturalPointsInDyadicInterval P I).max' hne + 1) := by
  let s := naturalPointsInDyadicInterval P I
  have hminMem : s.min' hne ∈ s := Finset.min'_mem s hne
  have hmaxMem : s.max' hne ∈ s := Finset.max'_mem s hne
  have hminData := mem_naturalPointsInDyadicInterval.mp hminMem
  have hmaxData := mem_naturalPointsInDyadicInterval.mp hmaxMem
  apply Finset.ext
  intro n
  rw [Finset.mem_Ico, Nat.lt_succ_iff]
  constructor
  · intro hn
    exact ⟨Finset.min'_le s n hn, Finset.le_max' s n hn⟩
  · rintro ⟨hmin, hmax⟩
    apply mem_naturalPointsInDyadicInterval.mpr
    refine ⟨hminData.1.trans hmin, hmax.trans hmaxData.2.1, ?_⟩
    apply hconn.out hminData.2.2 hmaxData.2.2
    constructor
    · exact_mod_cast hmin
    · exact_mod_cast hmax

/-- Membership of a natural number in an order-convex real interval is
equivalent to membership in the half-open natural core determined by the
minimum and maximum natural points. -/
theorem natCast_mem_iff_mem_natural_core
    {P n : ℕ} {I : Set ℝ} (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    (n : ℝ) ∈ I ↔
      n ∈ Finset.Ico
        ((naturalPointsInDyadicInterval P I).min' hne)
        ((naturalPointsInDyadicInterval P I).max' hne + 1) := by
  have hcore := naturalPointsInDyadicInterval_eq_Ico hconn hne
  constructor
  · intro hn
    have hnBounds := hI hn
    rw [← hcore]
    apply mem_naturalPointsInDyadicInterval.mpr
    exact ⟨by exact_mod_cast hnBounds.1, by exact_mod_cast hnBounds.2, hn⟩
  · intro hn
    rw [← hcore] at hn
    exact (mem_naturalPointsInDyadicInterval.mp hn).2.2

/-- Replacing an order-convex real interval by its natural half-open core
does not change the finite set of sampled primes. -/
theorem primesInScaleSet_eq_natural_core
    {P : ℕ} {I : Set ℝ} (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    primesInScaleSet (P : ℝ) I =
      primesInScaleSet (P : ℝ)
        (Set.Ico
          ((naturalPointsInDyadicInterval P I).min' hne : ℝ)
          (((naturalPointsInDyadicInterval P I).max' hne + 1 : ℕ) : ℝ)) := by
  classical
  unfold primesInScaleSet
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpRange, hpPrime, hpI⟩
    refine ⟨hpRange, hpPrime, ?_⟩
    have hpCore :=
      (natCast_mem_iff_mem_natural_core hconn hI hne).mp hpI
    have hpCore' := Finset.mem_Ico.mp hpCore
    rw [Set.mem_Ico]
    constructor
    · exact_mod_cast hpCore'.1
    · exact_mod_cast hpCore'.2
  · rintro ⟨hpRange, hpPrime, hpCore⟩
    refine ⟨hpRange, hpPrime, ?_⟩
    apply (natCast_mem_iff_mem_natural_core hconn hI hne).mpr
    rw [Finset.mem_Ico]
    constructor
    · exact_mod_cast hpCore.1
    · exact_mod_cast hpCore.2

/-- Exact discrete endpoint reduction for Tao's prime sum. -/
theorem primeEquidistributionSum_eq_natural_core
    {P : ℕ} {I : Set ℝ} (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty)
    (W : ℝ × ℝ → ℂ) (N M : ℝ) (j : ℕ) :
    primeEquidistributionSum (P : ℝ) I W N M j =
      primeEquidistributionSum (P : ℝ)
        (Set.Ico
          ((naturalPointsInDyadicInterval P I).min' hne : ℝ)
          (((naturalPointsInDyadicInterval P I).max' hne + 1 : ℕ) : ℝ))
        W N M j := by
  unfold primeEquidistributionSum
  rw [primesInScaleSet_eq_natural_core hconn hI hne]

/-- The capped analytic core still preserves every sampled prime: its only
possible difference from the full natural core is the endpoint `2P`, which
is composite for `P ≥ 2`. -/
theorem primesInScaleSet_eq_analytic_core
    {P : ℕ} {I : Set ℝ} (hP : 2 ≤ P) (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    primesInScaleSet (P : ℝ) I =
      primesInScaleSet (P : ℝ)
        (Set.Ico
          (naturalAnalyticCoreStart P I hne : ℝ)
          (naturalAnalyticCoreStop P I hne : ℝ)) := by
  classical
  let s := naturalPointsInDyadicInterval P I
  let a := s.min' hne
  let m := s.max' hne
  let b := min (m + 1) (2 * P)
  have hcore := naturalPointsInDyadicInterval_eq_Ico hconn hne
  change primesInScaleSet (P : ℝ) I =
    primesInScaleSet (P : ℝ) (Set.Ico (a : ℝ) (b : ℝ))
  unfold primesInScaleSet
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpRange, hpPrime, hpI⟩
    refine ⟨hpRange, hpPrime, ?_⟩
    have hpBounds := hI hpI
    have hpS : p ∈ s := mem_naturalPointsInDyadicInterval.mpr
      ⟨by exact_mod_cast hpBounds.1, by exact_mod_cast hpBounds.2, hpI⟩
    have hpCore : p ∈ Finset.Ico a (m + 1) := by
      rw [← hcore]
      exact hpS
    have hpCoreBounds := Finset.mem_Ico.mp hpCore
    have hpNeTop : p ≠ 2 * P := by
      intro hpEq
      subst p
      rcases Nat.prime_mul_iff.mp hpPrime with hpPrime | hpPrime
      · omega
      · omega
    have hpTop : p < 2 * P :=
      lt_of_le_of_ne (by exact_mod_cast hpBounds.2) hpNeTop
    rw [Set.mem_Ico]
    exact ⟨by exact_mod_cast hpCoreBounds.1,
      by exact_mod_cast (lt_min hpCoreBounds.2 hpTop)⟩
  · rintro ⟨hpRange, hpPrime, hpCore⟩
    refine ⟨hpRange, hpPrime, ?_⟩
    have hpCoreBounds : a ≤ p ∧ p < b := by
      rw [Set.mem_Ico] at hpCore
      exact ⟨by exact_mod_cast hpCore.1, by exact_mod_cast hpCore.2⟩
    have hpFull : p ∈ Finset.Ico a (m + 1) := by
      apply Finset.mem_Ico.mpr
      exact ⟨hpCoreBounds.1, hpCoreBounds.2.trans_le (min_le_left _ _)⟩
    rw [← hcore] at hpFull
    exact (mem_naturalPointsInDyadicInterval.mp hpFull).2.2

/-- Exact prime-sum reduction to the capped analytic core. -/
theorem primeEquidistributionSum_eq_analytic_core
    {P : ℕ} {I : Set ℝ} (hP : 2 ≤ P) (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty)
    (W : ℝ × ℝ → ℂ) (N M : ℝ) (j : ℕ) :
    primeEquidistributionSum (P : ℝ) I W N M j =
      primeEquidistributionSum (P : ℝ)
        (Set.Ico
          (naturalAnalyticCoreStart P I hne : ℝ)
          (naturalAnalyticCoreStop P I hne : ℝ)) W N M j := by
  unfold primeEquidistributionSum
  rw [primesInScaleSet_eq_analytic_core hP hconn hI hne]

/-- The capped analytic core has valid dyadic endpoints; it is either
nonempty as a half-open interval or degenerates only at the top endpoint. -/
theorem naturalAnalyticCore_bounds
    {P : ℕ} {I : Set ℝ}
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    P ≤ naturalAnalyticCoreStart P I hne ∧
      naturalAnalyticCoreStart P I hne ≤ naturalAnalyticCoreStop P I hne ∧
      naturalAnalyticCoreStop P I hne ≤ 2 * P := by
  let s := naturalPointsInDyadicInterval P I
  let a := s.min' hne
  let m := s.max' hne
  have haMem : a ∈ s := Finset.min'_mem s hne
  have hmMem : m ∈ s := Finset.max'_mem s hne
  have haData := mem_naturalPointsInDyadicInterval.mp haMem
  have hmData := mem_naturalPointsInDyadicInterval.mp hmMem
  change P ≤ a ∧ a ≤ min (m + 1) (2 * P) ∧
    min (m + 1) (2 * P) ≤ 2 * P
  exact ⟨haData.1,
    le_min (Finset.min'_le s m hmMem |>.trans (Nat.le_add_right m 1))
      haData.2.1,
    min_le_right _ _⟩

theorem naturalAnalyticCore_start_lt_stop_or_top
    {P : ℕ} {I : Set ℝ}
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    naturalAnalyticCoreStart P I hne < naturalAnalyticCoreStop P I hne ∨
      (naturalAnalyticCoreStart P I hne = 2 * P ∧
        (naturalPointsInDyadicInterval P I).max' hne = 2 * P) := by
  let s := naturalPointsInDyadicInterval P I
  let a := s.min' hne
  let m := s.max' hne
  have haMem : a ∈ s := Finset.min'_mem s hne
  have hmMem : m ∈ s := Finset.max'_mem s hne
  have haData := mem_naturalPointsInDyadicInterval.mp haMem
  have hmData := mem_naturalPointsInDyadicInterval.mp hmMem
  have ham : a ≤ m := Finset.min'_le s m hmMem
  change a < min (m + 1) (2 * P) ∨ (a = 2 * P ∧ m = 2 * P)
  by_cases hmTop : m + 1 ≤ 2 * P
  · rw [min_eq_left hmTop]
    exact Or.inl (by omega)
  · rw [min_eq_right (by omega : 2 * P ≤ m + 1)]
    omega

/-- An order-convex interval with a nonempty natural core lies within one
unit of its extreme natural points, while the closed span of those extreme
points lies in the original interval.  This is the geometric endpoint-error
ledger for the later integral comparison. -/
theorem natural_core_endpoint_geometry
    {P : ℕ} {I : Set ℝ} (hP : 1 ≤ P) (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    I ⊆ Set.Ioo
        (((naturalPointsInDyadicInterval P I).min' hne : ℝ) - 1)
        (((naturalPointsInDyadicInterval P I).max' hne : ℝ) + 1) ∧
      Set.Icc
          ((naturalPointsInDyadicInterval P I).min' hne : ℝ)
          ((naturalPointsInDyadicInterval P I).max' hne : ℝ) ⊆ I := by
  let s := naturalPointsInDyadicInterval P I
  let a := s.min' hne
  let m := s.max' hne
  have haMem : a ∈ s := Finset.min'_mem s hne
  have hmMem : m ∈ s := Finset.max'_mem s hne
  have haData := mem_naturalPointsInDyadicInterval.mp haMem
  have hmData := mem_naturalPointsInDyadicInterval.mp hmMem
  have haOne : 1 ≤ a := hP.trans haData.1
  constructor
  · intro x hx
    constructor
    · by_contra hnot
      have hxLeft : x ≤ (a : ℝ) - 1 := le_of_not_gt hnot
      have hcastPred : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
        rw [Nat.cast_sub haOne]
        norm_num
      have hpredP : P ≤ a - 1 := by
        have hxP := (hI hx).1
        have : (P : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by
          rw [hcastPred]
          exact hxP.trans hxLeft
        exact_mod_cast this
      have hpredI : ((a - 1 : ℕ) : ℝ) ∈ I := by
        apply hconn.out hx haData.2.2
        constructor
        · simpa only [hcastPred] using hxLeft
        · exact_mod_cast Nat.sub_le a 1
      have hpredMem : a - 1 ∈ s :=
        mem_naturalPointsInDyadicInterval.mpr
          ⟨hpredP, (Nat.sub_le a 1).trans haData.2.1, hpredI⟩
      have := Finset.min'_le s (a - 1) hpredMem
      omega
    · by_contra hnot
      have hxRight : (m : ℝ) + 1 ≤ x := le_of_not_gt hnot
      have hsuccTop : m + 1 ≤ 2 * P := by
        have hxTop := (hI hx).2
        have : ((m + 1 : ℕ) : ℝ) ≤ (2 * P : ℕ) := by
          norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul,
            Nat.cast_ofNat]
          exact hxRight.trans hxTop
        exact_mod_cast this
      have hsuccI : ((m + 1 : ℕ) : ℝ) ∈ I := by
        apply hconn.out hmData.2.2 hx
        constructor
        · exact_mod_cast Nat.le_add_right m 1
        · simpa only [Nat.cast_add, Nat.cast_one] using hxRight
      have hsuccMem : m + 1 ∈ s :=
        mem_naturalPointsInDyadicInterval.mpr
          ⟨hmData.1.trans (Nat.le_add_right m 1), hsuccTop, hsuccI⟩
      have := Finset.le_max' s (m + 1) hsuccMem
      omega
  · intro x hx
    exact hconn.out haData.2.2 hmData.2.2 hx

/-- The natural core changes an order-convex interval only on two endpoint
pieces of total Lebesgue measure at most two. -/
theorem volumeReal_symmDiff_natural_core_le_two
    {P : ℕ} {I : Set ℝ} (hP : 1 ≤ P) (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    volume.real
        (symmDiff I (Set.Ico
          ((naturalPointsInDyadicInterval P I).min' hne : ℝ)
          (((naturalPointsInDyadicInterval P I).max' hne + 1 : ℕ) : ℝ))) ≤
      2 := by
  let s := naturalPointsInDyadicInterval P I
  let a := s.min' hne
  let m := s.max' hne
  have hgeom := natural_core_endpoint_geometry hP hconn hI hne
  change I ⊆ Set.Ioo ((a : ℝ) - 1) ((m : ℝ) + 1) ∧
      Set.Icc (a : ℝ) (m : ℝ) ⊆ I at hgeom
  change volume.real (symmDiff I (Set.Ico (a : ℝ) ((m + 1 : ℕ) : ℝ))) ≤ 2
  have hsubset : symmDiff I (Set.Ico (a : ℝ) ((m + 1 : ℕ) : ℝ)) ⊆
      Set.Ioo ((a : ℝ) - 1) (a : ℝ) ∪
        Set.Ioo (m : ℝ) ((m : ℝ) + 1) := by
    intro x hx
    rw [Set.mem_symmDiff] at hx
    rcases hx with hx | hx
    · have hout := hgeom.1 hx.1
      by_cases hxa : x < (a : ℝ)
      · exact Or.inl ⟨hout.1, hxa⟩
      · exfalso
        apply hx.2
        rw [Set.mem_Ico]
        constructor
        · exact le_of_not_gt hxa
        · simpa only [Nat.cast_add, Nat.cast_one] using hout.2
    · rw [Set.mem_Ico] at hx
      by_cases hxm : (m : ℝ) < x
      · exact Or.inr ⟨hxm, by simpa only [Nat.cast_add, Nat.cast_one] using hx.1.2⟩
      · exfalso
        apply hx.2
        apply hgeom.2
        exact ⟨hx.1.1, le_of_not_gt hxm⟩
  calc
    volume.real (symmDiff I (Set.Ico (a : ℝ) ((m + 1 : ℕ) : ℝ))) ≤
        volume.real (Set.Ioo ((a : ℝ) - 1) (a : ℝ) ∪
          Set.Ioo (m : ℝ) ((m : ℝ) + 1)) :=
      measureReal_mono hsubset (measure_union_ne_top
        (by simp [Real.volume_Ioo]) (by simp [Real.volume_Ioo]))
    _ ≤ volume.real (Set.Ioo ((a : ℝ) - 1) (a : ℝ)) +
        volume.real (Set.Ioo (m : ℝ) ((m : ℝ) + 1)) :=
      measureReal_union_le _ _
    _ = 2 := by
      simp [Measure.real, Real.volume_Ioo]
      norm_num

/-- The capped analytic core differs from the original interval on at most
two units of Lebesgue measure. -/
theorem volumeReal_symmDiff_analytic_core_le_two
    {P : ℕ} {I : Set ℝ} (hP : 1 ≤ P) (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty) :
    volume.real
        (symmDiff I (Set.Ico
          (naturalAnalyticCoreStart P I hne : ℝ)
          (naturalAnalyticCoreStop P I hne : ℝ))) ≤ 2 := by
  let s := naturalPointsInDyadicInterval P I
  let a := s.min' hne
  let m := s.max' hne
  let b := min (m + 1) (2 * P)
  have hmMem : m ∈ s := Finset.max'_mem s hne
  have hmData := mem_naturalPointsInDyadicInterval.mp hmMem
  have hmb : m ≤ b := le_min (Nat.le_add_right m 1) hmData.2.1
  have hmbReal : (m : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmb
  have hbTop : b ≤ m + 1 := min_le_left (m + 1) (2 * P)
  have hbTopReal : (b : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hbTop
  have hgeom := natural_core_endpoint_geometry hP hconn hI hne
  change I ⊆ Set.Ioo ((s.min' hne : ℝ) - 1) ((m : ℝ) + 1) ∧
      Set.Icc (s.min' hne : ℝ) (m : ℝ) ⊆ I at hgeom
  change volume.real (symmDiff I (Set.Ico (a : ℝ) (b : ℝ))) ≤ 2
  have hsubset : symmDiff I (Set.Ico (a : ℝ) (b : ℝ)) ⊆
      Set.Ioo ((a : ℝ) - 1) (a : ℝ) ∪
        Set.Icc (m : ℝ) ((m : ℝ) + 1) := by
    intro x hx
    rw [Set.mem_symmDiff] at hx
    rcases hx with hx | hx
    · have hout := hgeom.1 hx.1
      by_cases hxa : x < (a : ℝ)
      · exact Or.inl ⟨hout.1, hxa⟩
      · have hbx : (b : ℝ) ≤ x := by
          by_contra hnot
          exact hx.2 (Set.mem_Ico.mpr ⟨le_of_not_gt hxa, lt_of_not_ge hnot⟩)
        exact Or.inr ⟨hmbReal.trans hbx, hout.2.le⟩
    · rw [Set.mem_Ico] at hx
      by_cases hxm : (m : ℝ) < x
      · exact Or.inr ⟨hxm.le, (hx.1.2.trans_le hbTopReal).le⟩
      · exfalso
        apply hx.2
        apply hgeom.2
        exact ⟨hx.1.1, le_of_not_gt hxm⟩
  calc
    volume.real (symmDiff I (Set.Ico (a : ℝ) (b : ℝ))) ≤
        volume.real (Set.Ioo ((a : ℝ) - 1) (a : ℝ) ∪
          Set.Icc (m : ℝ) ((m : ℝ) + 1)) :=
      measureReal_mono hsubset (measure_union_ne_top
        (by simp [Real.volume_Ioo]) (by simp [Real.volume_Icc]))
    _ ≤ volume.real (Set.Ioo ((a : ℝ) - 1) (a : ℝ)) +
        volume.real (Set.Icc (m : ℝ) ((m : ℝ) + 1)) :=
      measureReal_union_le _ _
    _ = 2 := by
      simp [Measure.real, Real.volume_Ioo, Real.volume_Icc]
      norm_num

/-- An order-convex dyadic interval with no natural point is contained in one
open unit cell, hence has Lebesgue measure at most one. -/
theorem volumeReal_le_one_of_natural_core_empty
    {P : ℕ} {I : Set ℝ} (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hempty : naturalPointsInDyadicInterval P I = ∅) :
    volume.real I ≤ 1 := by
  rcases I.eq_empty_or_nonempty with hIempty | hInonempty
  · subst I
    simp
  obtain ⟨x, hx⟩ := hInonempty
  let n := ⌊x⌋₊
  have hxnonneg : 0 ≤ x := (Nat.cast_nonneg P).trans (hI hx).1
  have hnle : (n : ℝ) ≤ x := Nat.floor_le hxnonneg
  have hxlt : x < (n : ℝ) + 1 := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have hsubset : I ⊆ Set.Ioo (n : ℝ) ((n : ℝ) + 1) := by
    intro y hy
    constructor
    · by_contra hnot
      have hyn : y ≤ (n : ℝ) := le_of_not_gt hnot
      have hnI : (n : ℝ) ∈ I := by
        apply hconn.out hy hx
        exact ⟨hyn, hnle⟩
      have hnBounds := hI hnI
      have hnMem : n ∈ naturalPointsInDyadicInterval P I :=
        mem_naturalPointsInDyadicInterval.mpr
          ⟨by exact_mod_cast hnBounds.1, by exact_mod_cast hnBounds.2, hnI⟩
      rw [hempty] at hnMem
      simp at hnMem
    · by_contra hnot
      have hny : (n : ℝ) + 1 ≤ y := le_of_not_gt hnot
      have hsuccI : ((n + 1 : ℕ) : ℝ) ∈ I := by
        apply hconn.out hx hy
        constructor
        · simpa only [Nat.cast_add, Nat.cast_one] using hxlt.le
        · simpa only [Nat.cast_add, Nat.cast_one] using hny
      have hsuccBounds := hI hsuccI
      have hsuccMem : n + 1 ∈ naturalPointsInDyadicInterval P I :=
        mem_naturalPointsInDyadicInterval.mpr
          ⟨by exact_mod_cast hsuccBounds.1,
            by exact_mod_cast hsuccBounds.2, hsuccI⟩
      rw [hempty] at hsuccMem
      simp at hsuccMem
  calc
    volume.real I ≤ volume.real (Set.Ioo (n : ℝ) ((n : ℝ) + 1)) :=
      measureReal_mono hsubset (by simp [Real.volume_Ioo])
    _ = 1 := by simp [Measure.real, Real.volume_Ioo]

/-- If the natural core is empty, Tao's sampled-prime set is empty as well. -/
theorem primesInScaleSet_eq_empty_of_natural_core_empty
    {P : ℕ} {I : Set ℝ}
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hempty : naturalPointsInDyadicInterval P I = ∅) :
    primesInScaleSet (P : ℝ) I = ∅ := by
  classical
  unfold primesInScaleSet
  apply Finset.filter_eq_empty_iff.mpr
  intro p _hpRange hpData
  have hpBounds := hI hpData.2
  have hpCore : p ∈ naturalPointsInDyadicInterval P I :=
    mem_naturalPointsInDyadicInterval.mpr
      ⟨by exact_mod_cast hpBounds.1, by exact_mod_cast hpBounds.2, hpData.2⟩
  rw [hempty] at hpCore
  simp at hpCore

/-- Empty natural core forces the discrete prime sum itself to vanish. -/
theorem primeEquidistributionSum_eq_zero_of_natural_core_empty
    {P : ℕ} {I : Set ℝ}
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hempty : naturalPointsInDyadicInterval P I = ∅)
    (W : ℝ × ℝ → ℂ) (N M : ℝ) (j : ℕ) :
    primeEquidistributionSum (P : ℝ) I W N M j = 0 := by
  unfold primeEquidistributionSum
  rw [primesInScaleSet_eq_empty_of_natural_core_empty hI hempty]
  simp

/-- A finite Fourier polynomial has only the elementary `ℓ¹/log P` endpoint
error on an order-convex interval with empty natural core. -/
theorem norm_specializedFiniteFourierPolynomial_discrepancy_le_of_core_empty
    {P : ℕ} {I : Set ℝ} (hP : 2 ≤ P)
    (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hempty : naturalPointsInDyadicInterval P I = ∅)
    (R : ℕ) (c : ℤ × ℤ → ℂ) (N : ℝ) :
    ‖primeEquidistributionSum (P : ℝ) I
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
        primeEquidistributionIntegral I
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
      (∑ q ∈ fourierFrequencyBox R, ‖c q‖) / Real.log P := by
  let A : ℝ := ∑ q ∈ fourierFrequencyBox R, ‖c q‖
  have hPReal : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hIfinite : volume I < ∞ := by
    apply lt_of_le_of_lt (measure_mono hI)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hpoint : ∀ t ∈ I,
      ‖finiteFourierPolynomial (fourierFrequencyBox R) c
          (N / t, N / t ^ 2) / Real.log t‖ ≤ A / Real.log P := by
    intro t ht
    have htBounds := hI ht
    have htpos : 0 < t := hPpos.trans_le htBounds.1
    have htone : (1 : ℝ) < t :=
      (by norm_num : (1 : ℝ) < 2).trans_le (hPReal.trans htBounds.1)
    have hlogt : 0 < Real.log t := Real.log_pos htone
    have hlogmono : Real.log (P : ℝ) ≤ Real.log t :=
      Real.strictMonoOn_log.monotoneOn hPpos htpos htBounds.1
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hlogt]
    exact (div_le_div_of_nonneg_right
      (norm_finiteFourierPolynomial_le_sum_norm
        (fourierFrequencyBox R) c (N / t, N / t ^ 2)) hlogt.le).trans
      (div_le_div_of_nonneg_left (by positivity : 0 ≤ A) hlogP hlogmono)
  have hint : ‖∫ t in I,
      finiteFourierPolynomial (fourierFrequencyBox R) c
        (N / t, N / t ^ 2) / Real.log t‖ ≤
      (A / Real.log P) * volume.real I :=
    norm_setIntegral_le_of_norm_le_const hIfinite hpoint
  have hvolume := volumeReal_le_one_of_natural_core_empty hconn hI hempty
  have hsum := primeEquidistributionSum_eq_zero_of_natural_core_empty
    hI hempty (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2
  unfold primeEquidistributionIntegral
  rw [hsum, zero_sub, norm_neg]
  refine hint.trans ?_
  exact mul_le_of_le_one_right (by positivity) hvolume

/-- Replacing a nonempty order-convex interval by its capped analytic core
changes the specialized finite-Fourier integral by at most the two endpoint
cells. -/
theorem norm_specializedFiniteFourierPolynomial_integral_sub_analyticCore_le
    {P : ℕ} {I : Set ℝ} (hP : 2 ≤ P) (hImeas : MeasurableSet I)
    (hconn : OrdConnected I)
    (hI : I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)))
    (hne : (naturalPointsInDyadicInterval P I).Nonempty)
    (R : ℕ) (c : ℤ × ℤ → ℂ) (N : ℝ) :
    ‖primeEquidistributionIntegral I
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
        primeEquidistributionIntegral
          (Set.Ico
            (naturalAnalyticCoreStart P I hne : ℝ)
            (naturalAnalyticCoreStop P I hne : ℝ))
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
      2 * (∑ q ∈ fourierFrequencyBox R, ‖c q‖) / Real.log P := by
  let A : ℝ := ∑ q ∈ fourierFrequencyBox R, ‖c q‖
  let J : Set ℝ := Set.Ico
    (naturalAnalyticCoreStart P I hne : ℝ)
    (naturalAnalyticCoreStop P I hne : ℝ)
  have hPReal : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hbounds := naturalAnalyticCore_bounds hne
  have hstartReal : (P : ℝ) ≤
      (naturalAnalyticCoreStart P I hne : ℝ) := by
    exact_mod_cast hbounds.1
  have hstopReal : (naturalAnalyticCoreStop P I hne : ℝ) ≤
      2 * (P : ℝ) := by
    exact_mod_cast hbounds.2.2
  have hJ : J ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) := by
    intro t ht
    change t ∈ Set.Ico
      (naturalAnalyticCoreStart P I hne : ℝ)
      (naturalAnalyticCoreStop P I hne : ℝ) at ht
    constructor
    · exact hstartReal.trans ht.1
    · exact ht.2.le.trans hstopReal
  have hImeasJ : MeasurableSet J := measurableSet_Ico
  have hIfinite : volume I ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono hI)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hJfinite : volume J ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono hJ)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hcont : Continuous
      (finiteFourierPolynomial (fourierFrequencyBox R) c) :=
    continuous_finiteFourierPolynomial _ _
  have hintI := integrableOn_primeEquidistributionIntegrand
    hPReal hI hcont N N 2
  have hintJ := integrableOn_primeEquidistributionIntegrand
    hPReal hJ hcont N N 2
  have hpoint : ∀ t ∈ symmDiff I J,
      ‖finiteFourierPolynomial (fourierFrequencyBox R) c
          (N / t, N / t ^ 2) / Real.log t‖ ≤ A / Real.log P := by
    intro t ht
    have htIJ : t ∈ I ∨ t ∈ J := by
      rw [Set.mem_symmDiff] at ht
      exact ht.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    have htBounds : t ∈ Set.Icc (P : ℝ) (2 * (P : ℝ)) :=
      htIJ.elim (fun ht => hI ht) (fun ht => hJ ht)
    have htpos : 0 < t := hPpos.trans_le htBounds.1
    have htone : (1 : ℝ) < t :=
      (by norm_num : (1 : ℝ) < 2).trans_le (hPReal.trans htBounds.1)
    have hlogt : 0 < Real.log t := Real.log_pos htone
    have hlogmono : Real.log (P : ℝ) ≤ Real.log t :=
      Real.strictMonoOn_log.monotoneOn hPpos htpos htBounds.1
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hlogt]
    exact (div_le_div_of_nonneg_right
      (norm_finiteFourierPolynomial_le_sum_norm
        (fourierFrequencyBox R) c (N / t, N / t ^ 2)) hlogt.le).trans
      (div_le_div_of_nonneg_left (by positivity : 0 ≤ A) hlogP hlogmono)
  have hchange := norm_setIntegral_sub_setIntegral_le_symmDiff
    hImeas hImeasJ hintI hintJ hIfinite hJfinite hpoint
  have hvolume := volumeReal_symmDiff_analytic_core_le_two
    (show 1 ≤ P by omega) hconn hI hne
  unfold primeEquidistributionIntegral
  change ‖(∫ t in I, finiteFourierPolynomial (fourierFrequencyBox R) c
      (N / t, N / t ^ 2) / Real.log t) -
    ∫ t in J, finiteFourierPolynomial (fourierFrequencyBox R) c
      (N / t, N / t ^ 2) / Real.log t‖ ≤ _
  refine hchange.trans ?_
  calc
    A / Real.log P * volume.real (symmDiff I J) ≤ A / Real.log P * 2 :=
      mul_le_mul_of_nonneg_left hvolume (by positivity)
    _ = 2 * (∑ q ∈ fourierFrequencyBox R, ‖c q‖) / Real.log P := by
      simp only [A]
      ring

/-- The finite-Fourier specialized estimate on natural half-open intervals
extends to every measurable order-convex real interval in the dyadic block. -/
theorem eventually_specializedFiniteFourierPolynomial_interval_le_logSaving
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    (hVinogradov : VinogradovExponentialSumEstimate)
    (R : ℕ) (c : ℤ × ℤ → ℂ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (I : Set ℝ) (N : ℝ),
      MeasurableSet I → OrdConnected I →
      I ⊆ Set.Icc (P : ℝ) (2 * (P : ℝ)) →
      VinogradovParameterBound ε K P N →
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S := by
  let A : ℝ := ∑ q ∈ fourierFrequencyBox R, ‖c q‖
  have hcore := eventually_specializedFiniteFourierPolynomial_Ico_le_logSaving
    hPNT hVinogradov R c hK hε haexp (S + 1)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have habsorb : ∀ᶠ P : ℕ in atTop,
      (4 * A) * (Real.log P) ^ S ≤ P :=
    eventually_const_mul_log_pow_le_natCast (by positivity) S
  have hlogTop : Tendsto (fun P : ℕ => Real.log P) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogTwo : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log P :=
    hlogTop.eventually (eventually_ge_atTop 2)
  filter_upwards [hcore, habsorb, hlogTwo, eventually_ge_atTop (3 : ℕ)] with
      P hcoreP habsorbP hlogPtwo hPthree
  intro I N hImeas hconn hI hN
  have hP : 2 ≤ P := by omega
  have hPnonneg : (0 : ℝ) ≤ P := by positivity
  have hlogP : 0 < Real.log (P : ℝ) := lt_of_lt_of_le (by norm_num) hlogPtwo
  have hlogPow : 0 < (Real.log (P : ℝ)) ^ S := pow_pos hlogP S
  have hcombine :
      (P : ℝ) / (Real.log P) ^ (S + 1) + 2 * A / Real.log P ≤
        (P : ℝ) / (Real.log P) ^ S := by
    apply (le_div_iff₀ hlogPow).2
    have heq :
        ((P : ℝ) / (Real.log P) ^ (S + 1) + 2 * A / Real.log P) *
            (Real.log P) ^ S =
          ((P : ℝ) + 2 * A * (Real.log P) ^ S) / Real.log P := by
      rw [pow_succ]
      field_simp
    rw [heq]
    apply (div_le_iff₀ hlogP).2
    have htwoA : 2 * A * (Real.log P) ^ S ≤ (P : ℝ) := by
      nlinarith [mul_nonneg hA (pow_nonneg hlogP.le S)]
    nlinarith
  by_cases hempty : naturalPointsInDyadicInterval P I = ∅
  · have hemptyBound :=
      norm_specializedFiniteFourierPolynomial_discrepancy_le_of_core_empty
        hP hconn hI hempty R c N
    refine hemptyBound.trans ?_
    calc
      (∑ q ∈ fourierFrequencyBox R, ‖c q‖) / Real.log P ≤
          (P : ℝ) / (Real.log P) ^ (S + 1) + 2 * A / Real.log P := by
        change A / Real.log P ≤ _
        have hsource : 0 ≤ (P : ℝ) / (Real.log P) ^ (S + 1) := by positivity
        calc
          A / Real.log P ≤ 2 * A / Real.log P :=
            (div_le_div_iff_of_pos_right hlogP).2 (by nlinarith)
          _ ≤ (P : ℝ) / (Real.log P) ^ (S + 1) +
              2 * A / Real.log P := le_add_of_nonneg_left hsource
      _ ≤ (P : ℝ) / (Real.log P) ^ S := hcombine
  · have hne : (naturalPointsInDyadicInterval P I).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let a := naturalAnalyticCoreStart P I hne
    let b := naturalAnalyticCoreStop P I hne
    let J : Set ℝ := Set.Ico (a : ℝ) (b : ℝ)
    have hbounds := naturalAnalyticCore_bounds hne
    have hsum := primeEquidistributionSum_eq_analytic_core
      hP hconn hI hne (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2
    change primeEquidistributionSum (P : ℝ) I
        (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 =
      primeEquidistributionSum (P : ℝ) J
        (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 at hsum
    have hendpoint :=
      norm_specializedFiniteFourierPolynomial_integral_sub_analyticCore_le
        hP hImeas hconn hI hne R c N
    change ‖primeEquidistributionIntegral I
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
        primeEquidistributionIntegral J
          (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
      2 * A / Real.log P at hendpoint
    have hcoreBound :
        ‖primeEquidistributionSum (P : ℝ) J
              (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
            primeEquidistributionIntegral J
              (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ ≤
          (P : ℝ) / (Real.log P) ^ (S + 1) := by
      rcases naturalAnalyticCore_start_lt_stop_or_top hne with hab | htop
      · exact hcoreP a b N hbounds.1 hab hbounds.2.2 hN
      · have habEq : a = b := by
          dsimp [a, b]
          omega
        have hJempty : J = ∅ := by simp [J, habEq]
        rw [hJempty]
        simp [primeEquidistributionSum, primesInScaleSet,
          primeEquidistributionIntegral]
        positivity
    calc
      ‖primeEquidistributionSum (P : ℝ) I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
          primeEquidistributionIntegral I
            (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ =
          ‖(primeEquidistributionSum (P : ℝ) J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2) +
            (primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral I
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2)‖ := by
            rw [hsum]
            congr 1
            ring
      _ ≤ ‖primeEquidistributionSum (P : ℝ) J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ +
            ‖primeEquidistributionIntegral J
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2 -
              primeEquidistributionIntegral I
                (finiteFourierPolynomial (fourierFrequencyBox R) c) N N 2‖ :=
          norm_add_le _ _
      _ ≤ (P : ℝ) / (Real.log P) ^ (S + 1) +
            2 * A / Real.log P :=
          add_le_add hcoreBound (by simpa only [norm_sub_rev] using hendpoint)
      _ ≤ (P : ℝ) / (Real.log P) ^ S := hcombine

end

end Tao2026
