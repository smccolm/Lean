import TaoTrudgianYang2025.EnergyPowering
import TaoTrudgianYang2025.EnergySeparation
import GuthMaynard.ClassicalPowering

/-!
# Actual powered large-value patterns

The native polynomial-power API uses half-open dyadic intervals. We account
for the removed endpoint, normalize using the uniform divisor bound, and
embed every selected powered block back into the source's closed support.
These are finite constructions, not yet the limiting EPZAE-34 theorem.
-/

open Complex Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Removing the single left endpoint costs at most one in the large-value
threshold. No phase, coefficient, or ordinate is changed. -/
theorem LargeValuePattern.halfOpen_large (P : LargeValuePattern)
    {t : ℝ} (ht : t ∈ P.ordinates) :
    P.V - 1 ≤ ‖∑ n ∈ Ioc P.scale (2 * P.scale),
      P.coeff n * (n : ℂ) ^ (-(0 + I * t))‖ := by
  have hmem : P.scale ∈ P.indices := by
    rw [P.indices_eq_dyadicInterval]
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hterm : ‖P.coeff P.scale * dirichletPhase P.scale t‖ ≤ 1 := by
    rw [norm_mul, P.norm_dirichletPhase hmem, mul_one]
    exact P.coeff_one_bounded _ hmem
  have h := P.large t ht
  rw [P.indices_eq_dyadicInterval, Finset.Icc_eq_cons_Ioc (by omega),
    Finset.sum_cons] at h
  have htriangle := norm_add_le (P.coeff P.scale * dirichletPhase P.scale t)
    (∑ n ∈ Ioc P.scale (2 * P.scale), P.coeff n * dirichletPhase n t)
  simp only [dirichletPhase, zero_add] at h hterm htriangle ⊢
  change P.V - 1 ≤ ‖∑ n ∈ Ioc P.scale (2 * P.scale),
    P.coeff n * Complex.cpow (n : ℂ) (-(I * (t : ℂ)))‖
  linarith

/-- Zero padding at the left endpoint changes a half-open polynomial into
the exact closed-support convention without changing its value. -/
theorem closedSupportPolynomial_eq_halfOpen
    (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ Icc M (2 * M), (if n = M then 0 else a n) * dirichletPhase n t) =
      dirichletPoly M a t := by
  classical
  rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]
  simp only [ite_true, zero_mul, zero_add]
  unfold dirichletPoly dyadicInterval
  apply Finset.sum_congr rfl
  intro n hn
  have hnNe : n ≠ M := ne_of_gt (Finset.mem_Ioc.mp hn).1
  rw [if_neg hnNe, dirichletPhase]
  congr 2
  ring

/-- A normalized half-open polynomial on a subset of the original
ordinates gives an actual closed-support large-value pattern. -/
def LargeValuePattern.ofHalfOpenBlock (P : LargeValuePattern)
    (M : ℕ) (a : ℕ → ℂ) (V : ℝ) (W : Finset ℝ)
    (hM : 1 < M) (hV : 0 < V)
    (ha : ∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1)
    (hW : W ⊆ P.ordinates)
    (hlarge : ∀ t ∈ W, V ≤ ‖dirichletPoly M a t‖) : LargeValuePattern where
  N := M
  scale := M
  T := P.T
  V := V
  coeff := fun n => if n = M then 0 else a n
  indices := Icc M (2 * M)
  intervalLeft := P.intervalLeft
  intervalRight := P.intervalRight
  ordinates := W
  N_eq_scale := rfl
  one_lt_N := by exact_mod_cast hM
  T_pos := P.T_pos
  V_pos := hV
  mem_indices_iff := by intro n; simp only [Finset.mem_Icc]; norm_cast
  coeff_one_bounded := by
    intro n hn
    split_ifs with h
    · simp
    · exact ha n (Finset.mem_Ioc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega,
        (Finset.mem_Icc.mp hn).2⟩)
  interval_length := P.interval_length
  ordinates_in_interval := fun t ht => P.ordinates_in_interval t (hW ht)
  ordinates_oneSeparated := fun t ht u hu htu =>
    P.ordinates_oneSeparated t (hW ht) u (hW hu) htu
  large := by
    intro t ht
    rw [closedSupportPolynomial_eq_halfOpen]
    exact hlarge t ht

/-- Finset specialization of energy pigeonholing. The equivalence of the
filtered index type and the color fiber preserves every ordered quadruple. -/
theorem exists_energy_preserving_finset_color
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (W : Finset ℝ) (color : ℝ → κ) :
    ∃ c : κ, (finsetAdditiveEnergy W : ℝ) ≤
      9 * (Fintype.card κ : ℝ) ^ 4 *
        (finsetAdditiveEnergy (W.filter fun t => color t = c) : ℝ) := by
  classical
  obtain ⟨c, hc⟩ := exists_energy_preserving_color
    (fun t : W => (t : ℝ)) (fun t : W => color t)
  let e : EnergyColorFiber (fun t : W => color t) c ≃
      ↥(W.filter fun t => color t = c) :=
    { toFun := fun t => ⟨t.1.1, Finset.mem_filter.mpr ⟨t.1.2, t.2⟩⟩
      invFun := fun t => ⟨⟨t.1, (Finset.mem_filter.mp t.2).1⟩,
        (Finset.mem_filter.mp t.2).2⟩
      left_inv := by intro t; rfl
      right_inv := by intro t; rfl }
  have he := approximateAdditiveEnergyOf_equiv 1
    (fun t : EnergyColorFiber (fun t : W => color t) c => (t.1 : ℝ))
    (fun t : ↥(W.filter fun t => color t = c) => (t : ℝ)) e (fun _ => rfl)
  exact ⟨c, by simpa only [he, finsetAdditiveEnergy] using hc⟩

/-- Fixed-power coefficient normalization is uniform in the input pattern.
Every color class is an actual powered pattern, including empty classes.
The separate cardinality and energy selections can therefore use this same
finite family without identifying their output witnesses. -/
theorem exists_normalized_powered_pattern_partition
    (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : LargeValuePattern, 1 < P.V →
      ∃ color : ℝ → Fin k, ∃ Q : Fin k → LargeValuePattern,
        ∀ r : Fin k,
          (Q r).scale = 2 ^ r.val * P.scale ^ k ∧
          (Q r).T = P.T ∧
          (Q r).V = (P.V - 1) ^ k /
            (C * ((2 ^ k * P.scale ^ k : ℕ) : ℝ) ^ η) / k ∧
          (Q r).ordinates = P.ordinates.filter (fun t => color t = r) := by
  classical
  obtain ⟨C, hC, hcoeff⟩ := finitePowCoeff_bound_uniform k η hη
  refine ⟨C, hC, ?_⟩
  intro P hV
  have hscale : 1 < P.scale := by
    exact_mod_cast (show (1 : ℝ) < P.scale by simpa [P.N_eq_scale] using P.one_lt_N)
  have hscalePos : 0 < P.scale := by omega
  let a := normalizedFinitePoweredCoeffs P.scale k P.coeff 0 C η
  let V := (P.V - 1) ^ k / (C * ((2 ^ k * P.scale ^ k : ℕ) : ℝ) ^ η) / k
  have hdenom : 0 < C * ((2 ^ k * P.scale ^ k : ℕ) : ℝ) ^ η := by
    apply mul_pos hC
    apply Real.rpow_pos_of_pos
    exact_mod_cast mul_pos (pow_pos (by omega : 0 < 2) k) (pow_pos hscalePos k)
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hVpos : 0 < V := div_pos (div_pos (pow_pos (sub_pos.mpr hV) k) hdenom) hkReal
  have hEach (t : ℝ) (ht : t ∈ P.ordinates) :
      ∃ r : Fin k, V ≤ ‖dirichletPoly (2 ^ r.val * P.scale ^ k) a t‖ := by
    have hwide := normalized_finite_powered_wide_lower P.scale k P.coeff
      0 C η t (P.V - 1) hscalePos hk (sub_pos.mpr hV).le hdenom
      (P.halfOpen_large ht)
    simp only [Real.rpow_zero, one_mul] at hwide
    obtain ⟨r, hr, hrl⟩ := exists_large_dyadic_block (P.scale ^ k) k a t
      ((P.V - 1) ^ k / (C * ((2 ^ k * P.scale ^ k : ℕ) : ℝ) ^ η)) hk hwide
    exact ⟨⟨r, Finset.mem_range.mp hr⟩, hrl⟩
  let color : ℝ → Fin k := fun t =>
    if ht : t ∈ P.ordinates then Classical.choose (hEach t ht) else ⟨0, hk⟩
  have hColorLarge (t : ℝ) (ht : t ∈ P.ordinates) :
      V ≤ ‖dirichletPoly (2 ^ (color t).val * P.scale ^ k) a t‖ := by
    simp only [color, dif_pos ht]
    exact Classical.choose_spec (hEach t ht)
  have hM (r : Fin k) : 1 < 2 ^ r.val * P.scale ^ k := by
    have hp : 1 < P.scale ^ k := one_lt_pow₀ hscale hk.ne'
    exact hp.trans_le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _))
  have ha (r : Fin k) : ∀ n ∈ Ioc (2 ^ r.val * P.scale ^ k)
      (2 * (2 ^ r.val * P.scale ^ k)), ‖a n‖ ≤ 1 := by
    intro n hn
    have hleft : P.scale ^ k ≤ 2 ^ r.val * P.scale ^ k :=
      Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)
    have hright : 2 * (2 ^ r.val * P.scale ^ k) ≤ 2 ^ k * P.scale ^ k := by
      calc
        2 * (2 ^ r.val * P.scale ^ k) = 2 ^ (r.val + 1) * P.scale ^ k := by
          rw [pow_succ]; ring
        _ ≤ 2 ^ k * P.scale ^ k := Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by omega) (by omega))
    have hnWide : n ∈ Ioc (P.scale ^ k) (2 ^ k * P.scale ^ k) :=
      Finset.mem_Ioc.mpr ⟨hleft.trans_lt (Finset.mem_Ioc.mp hn).1,
        (Finset.mem_Ioc.mp hn).2.trans hright⟩
    apply norm_normalizedFinitePoweredCoeffs_le_one P.scale k n P.coeff
      0 C η hscalePos le_rfl hC hη hnWide
    apply hcoeff P.scale P.coeff
    · intro m hm
      apply P.coeff_one_bounded m
      rw [P.indices_eq_dyadicInterval]
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hm).1.le, (Finset.mem_Ioc.mp hm).2⟩
    · exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hnWide).1
  refine ⟨color, fun r => P.ofHalfOpenBlock (2 ^ r.val * P.scale ^ k) a V
    (P.ordinates.filter fun t => color t = r) (hM r) hVpos (ha r)
    (Finset.filter_subset _ _) (fun t ht => ?_), ?_⟩
  · have h := hColorLarge t (Finset.mem_filter.mp ht).1
    simpa only [(Finset.mem_filter.mp ht).2] using h
  · intro r
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Restricting a finite set of ordinates cannot increase its energy. -/
theorem finsetAdditiveEnergy_mono {U W : Finset ℝ} (h : U ⊆ W) :
    finsetAdditiveEnergy U ≤ finsetAdditiveEnergy W := by
  classical
  let f : U → W := fun t => ⟨t.1, h t.2⟩
  unfold finsetAdditiveEnergy approximateAdditiveEnergyOf
  apply Finset.card_le_card_of_injOn (fun q => f ∘ q)
  · intro q hq
    simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.comp_apply] using hq
  · intro q _ p _ hqp
    funext i
    have heq : (q i).val = (p i).val :=
      congrArg (fun t : W => (t : ℝ)) (congrFun hqp i)
    exact Subtype.ext heq

/-- Exact finite geometry of one of the normalized powered blocks. -/
structure NormalizedPoweredSubpattern (P : LargeValuePattern) (k : ℕ) (C η : ℝ) where
  pattern : LargeValuePattern
  block : Fin k
  scale_eq : pattern.scale = 2 ^ block.val * P.scale ^ k
  time_eq : pattern.T = P.T
  value_eq : pattern.V = (P.V - 1) ^ k /
    (C * ((2 ^ k * P.scale ^ k : ℕ) : ℝ) ^ η) / k
  ordinates_subset : pattern.ordinates ⊆ P.ordinates

theorem NormalizedPoweredSubpattern.card_le
    {P : LargeValuePattern} {k : ℕ} {C η : ℝ}
    (Q : NormalizedPoweredSubpattern P k C η) :
    Q.pattern.ordinates.card ≤ P.ordinates.card :=
  Finset.card_le_card Q.ordinates_subset

theorem NormalizedPoweredSubpattern.energy_le
    {P : LargeValuePattern} {k : ℕ} {C η : ℝ}
    (Q : NormalizedPoweredSubpattern P k C η) :
    finsetAdditiveEnergy Q.pattern.ordinates ≤ finsetAdditiveEnergy P.ordinates :=
  finsetAdditiveEnergy_mono Q.ordinates_subset

/-- Powered scales are linked exactly to the original physical scale. -/
theorem NormalizedPoweredSubpattern.real_scale_eq
    {P : LargeValuePattern} {k : ℕ} {C η : ℝ}
    (Q : NormalizedPoweredSubpattern P k C η) :
    Q.pattern.N = (2 : ℝ) ^ Q.block.val * P.N ^ k := by
  rw [Q.pattern.N_eq_scale, Q.scale_eq, P.N_eq_scale]
  push_cast
  rfl

theorem NormalizedPoweredSubpattern.scale_bounds
    {P : LargeValuePattern} {k : ℕ} {C η : ℝ}
    (Q : NormalizedPoweredSubpattern P k C η) :
    P.N ^ k ≤ Q.pattern.N ∧ Q.pattern.N ≤ (2 : ℝ) ^ k * P.N ^ k := by
  rw [Q.real_scale_eq]
  have hN : 0 ≤ P.N ^ k := pow_nonneg (zero_le_one.trans P.one_lt_N.le) _
  constructor
  · simpa using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hN
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) Q.block.isLt.le) hN

/-- Exact logarithmic scale formula; the block index contributes only a
bounded additive term when the power is fixed. -/
theorem NormalizedPoweredSubpattern.log_scale_eq
    {P : LargeValuePattern} {k : ℕ} {C η : ℝ}
    (Q : NormalizedPoweredSubpattern P k C η) :
    Real.log Q.pattern.N = k * Real.log P.N + Q.block.val * Real.log 2 := by
  rw [Q.real_scale_eq, Real.log_mul (by positivity)
    (pow_ne_zero _ (zero_lt_one.trans P.one_lt_N).ne'), Real.log_pow, Real.log_pow]
  ring

/-- Both repaired witnesses exist at the finite-pattern level, with fixed
losses `k` and `9 k⁴`. Each is selected from the actual powered polynomials;
neither is an assumed large-value or energy witness. -/
theorem exists_normalized_powered_subpatterns
    (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : LargeValuePattern, 1 < P.V →
      ∃ Qcard Qenergy : NormalizedPoweredSubpattern P k C η,
        (P.ordinates.card : ℝ) ≤ k * (Qcard.pattern.ordinates.card : ℝ) ∧
        (finsetAdditiveEnergy P.ordinates : ℝ) ≤ 9 * (k : ℝ) ^ 4 *
          (finsetAdditiveEnergy Qenergy.pattern.ordinates : ℝ) := by
  classical
  obtain ⟨C, hC, hpartition⟩ := exists_normalized_powered_pattern_partition k hk η hη
  refine ⟨C, hC, ?_⟩
  intro P hV
  obtain ⟨color, Q, hQ⟩ := hpartition P hV
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hsum : (P.ordinates.card : ℝ) =
      ∑ r : Fin k, ((P.ordinates.filter fun t => color t = r).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun t (_ht : t ∈ P.ordinates) => Finset.mem_univ (color t))
  let f : Fin k → ℝ := fun r => (P.ordinates.filter fun t => color t = r).card
  obtain ⟨r, _hr, hmax⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hcard : (P.ordinates.card : ℝ) ≤ k * ((Q r).ordinates.card : ℝ) := by
    rw [hsum, (hQ r).2.2.2]
    calc
      ∑ i : Fin k, f i ≤ ∑ _i : Fin k, f r :=
        Finset.sum_le_sum fun i hi => hmax i hi
      _ = k * f r := by simp
  obtain ⟨s, hs⟩ := exists_energy_preserving_finset_color P.ordinates color
  let subpattern (i : Fin k) : NormalizedPoweredSubpattern P k C η :=
    { pattern := Q i
      block := i
      scale_eq := (hQ i).1
      time_eq := (hQ i).2.1
      value_eq := (hQ i).2.2.1
      ordinates_subset := by rw [(hQ i).2.2.2]; exact Finset.filter_subset _ _ }
  refine ⟨subpattern r, subpattern s, hcard, ?_⟩
  change (finsetAdditiveEnergy P.ordinates : ℝ) ≤ 9 * (k : ℝ) ^ 4 *
    (finsetAdditiveEnergy (Q s).ordinates : ℝ)
  simpa only [(hQ s).2.2.2, Fintype.card_fin] using hs

end TaoTrudgianYang2025
