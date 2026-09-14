import Tao2026.BadIntervalTypicalCounting

/-!
# Moving dyadic prime scales for the typical branch

The source places the distinguished prime and the following 1000 prime
factors in ordered dyadic bands between two cutoffs of the form
`z^(1+o(1))`.  This module gives that finite grid an exact definition.  It
also proves the uniform selector fact needed by Proposition 6.6: any sequence
of coordinate scales selected from the moving grid is a
`TaoPrimeTupleSourceScaleFamily`.
-/

namespace Tao2026

open Filter Topology
open scoped Classical

noncomputable section

set_option maxRecDepth 4000

/-- Lower endpoint of the moving prime-scale grid selected by `q`. -/
def taoPrimeTupleSlowLowerCutoff (q : ℕ → ℕ) (x : ℕ) : ℕ :=
  taoZPowerFloor (taoSlowLowerExponent (q x)) x

/-- Upper endpoint of the moving prime-scale grid selected by `q`. -/
def taoPrimeTupleSlowUpperCutoff (q : ℕ → ℕ) (x : ℕ) : ℕ :=
  taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x

/-- Powers of two whose half-open dyadic bands can meet the moving source
prime range. -/
def taoPrimeTupleSlowDyadicExponents (q : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (taoPrimeTupleSlowUpperCutoff q x) + 1)).filter
    fun r => taoPrimeTupleSlowLowerCutoff q x < 2 ^ (r + 1)

theorem mem_taoPrimeTupleSlowDyadicExponents
    {q : ℕ → ℕ} {x r : ℕ} :
    r ∈ taoPrimeTupleSlowDyadicExponents q x ↔
      r ≤ Nat.log 2 (taoPrimeTupleSlowUpperCutoff q x) ∧
      taoPrimeTupleSlowLowerCutoff q x < 2 ^ (r + 1) := by
  simp [taoPrimeTupleSlowDyadicExponents]

/-- The finite Cartesian family of all 1001 coordinate-scale choices. -/
def taoPrimeTupleSlowScaleExponentTuples
    (q : ℕ → ℕ) (x : ℕ) : Finset (Fin 1001 → ℕ) :=
  Fintype.piFinset fun _ => taoPrimeTupleSlowDyadicExponents q x

theorem mem_taoPrimeTupleSlowScaleExponentTuples
    {q : ℕ → ℕ} {x : ℕ} {R : Fin 1001 → ℕ} :
    R ∈ taoPrimeTupleSlowScaleExponentTuples q x ↔
      ∀ j, R j ∈ taoPrimeTupleSlowDyadicExponents q x := by
  simp [taoPrimeTupleSlowScaleExponentTuples]

/-- The source-relevant subfamily in which the coordinate scales are
nonincreasing. -/
def taoPrimeTupleSlowOrderedScaleExponentTuples
    (q : ℕ → ℕ) (x : ℕ) : Finset (Fin 1001 → ℕ) :=
  (taoPrimeTupleSlowScaleExponentTuples q x).filter Antitone

theorem mem_taoPrimeTupleSlowOrderedScaleExponentTuples
    {q : ℕ → ℕ} {x : ℕ} {R : Fin 1001 → ℕ} :
    R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x ↔
      (∀ j, R j ∈ taoPrimeTupleSlowDyadicExponents q x) ∧ Antitone R := by
  simp [taoPrimeTupleSlowOrderedScaleExponentTuples,
    mem_taoPrimeTupleSlowScaleExponentTuples]

/-- Every row's lower exponent is at least `4/5`; this fixed positive margin
makes the moving lower cutoff tend to infinity without imposing any rate on
the row selector. -/
theorem four_fifths_le_taoSlowLowerExponent (n : ℕ) :
    (4 / 5 : ℝ) ≤ taoSlowLowerExponent n := by
  have hd : (10 : ℝ) ≤ taoSlowCutoffDenominator n := by
    exact_mod_cast ten_le_taoSlowCutoffDenominator n
  have hdPos : (0 : ℝ) < taoSlowCutoffDenominator n := by positivity
  rw [taoSlowLowerExponent]
  have hquot : 2 / (taoSlowCutoffDenominator n : ℝ) ≤ 1 / 5 := by
    rw [div_le_iff₀ hdPos]
    nlinarith
  linarith

/-- The moving lower cutoff tends to infinity for every row selector. -/
theorem tendsto_taoPrimeTupleSlowLowerCutoff_atTop (q : ℕ → ℕ) :
    Tendsto (taoPrimeTupleSlowLowerCutoff q) atTop atTop := by
  have hle : ∀ᶠ x : ℕ in atTop,
      taoZPowerFloor (4 / 5 : ℝ) x ≤ taoPrimeTupleSlowLowerCutoff q x := by
    filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with x hz
    unfold taoPrimeTupleSlowLowerCutoff taoZPowerFloor
    exact Nat.floor_mono
      (Real.rpow_le_rpow_of_exponent_le hz
        (four_fifths_le_taoSlowLowerExponent (q x)))
  exact tendsto_atTop_mono' atTop hle
    (tendsto_taoZPowerFloor_atTop (by norm_num : (0 : ℝ) < 4 / 5))

/-- A positive integer between the moving cutoffs lies in the dyadic band
indexed by its base-two logarithm. -/
theorem natLog_mem_taoPrimeTupleSlowDyadicExponents_of_bounds
    {q : ℕ → ℕ} {x p : ℕ}
    (hlower : taoPrimeTupleSlowLowerCutoff q x ≤ p)
    (hupper : p ≤ taoPrimeTupleSlowUpperCutoff q x) :
    Nat.log 2 p ∈ taoPrimeTupleSlowDyadicExponents q x := by
  apply mem_taoPrimeTupleSlowDyadicExponents.mpr
  constructor
  · exact Nat.log_mono_right hupper
  · exact hlower.trans_lt
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p)

/-- Every retained dyadic scale lies between half the lower cutoff and the
upper cutoff, in the exact natural-number form used below. -/
theorem taoPrimeTupleSlowDyadicScale_bounds
    {q : ℕ → ℕ} {x r : ℕ}
    (hr : r ∈ taoPrimeTupleSlowDyadicExponents q x)
    (hupper : taoPrimeTupleSlowUpperCutoff q x ≠ 0) :
    taoPrimeTupleSlowLowerCutoff q x < 2 * 2 ^ r ∧
      2 ^ r ≤ taoPrimeTupleSlowUpperCutoff q x := by
  have hrData := mem_taoPrimeTupleSlowDyadicExponents.mp hr
  constructor
  · simpa only [pow_succ, mul_comm] using hrData.2
  · exact (Nat.pow_le_pow_right (by norm_num) hrData.1).trans
      (Nat.pow_log_le_self 2 hupper)

/-- The moving lower cutoff never exceeds the moving upper cutoff. -/
theorem taoPrimeTupleSlowLowerCutoff_le_upperCutoff
    (q : ℕ → ℕ) (x : ℕ) :
    taoPrimeTupleSlowLowerCutoff q x ≤
      taoPrimeTupleSlowUpperCutoff q x := by
  have hz : (1 : ℝ) ≤ taoZ x := by
    rw [taoZ]
    exact Real.one_le_exp (by positivity)
  have hexponents :
      taoSlowLowerExponent (q x) ≤ taoSlowUpperExponent (q x) := by
    rw [taoSlowLowerExponent, taoSlowUpperExponent]
    have hd : (0 : ℝ) < taoSlowCutoffDenominator (q x) := by
      exact_mod_cast taoSlowCutoffDenominator_pos (q x)
    have hdiv : 0 ≤ 2 / (taoSlowCutoffDenominator (q x) : ℝ) :=
      div_nonneg (by norm_num) hd.le
    linarith
  exact (taoZPowerFloor_le_taoOneTermExponentCutoff
      (taoSlowLowerExponent (q x)) x).trans
    (taoOneTermExponentCutoff_mono_of_one_le hz hexponents)

/-- The moving one-dimensional dyadic grid is nonempty. -/
theorem taoPrimeTupleSlowDyadicExponents_nonempty
    (q : ℕ → ℕ) (x : ℕ) :
    (taoPrimeTupleSlowDyadicExponents q x).Nonempty := by
  refine ⟨Nat.log 2 (taoPrimeTupleSlowUpperCutoff q x), ?_⟩
  apply mem_taoPrimeTupleSlowDyadicExponents.mpr
  exact ⟨le_rfl,
    (taoPrimeTupleSlowLowerCutoff_le_upperCutoff q x).trans_lt
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
        (taoPrimeTupleSlowUpperCutoff q x))⟩

/-- Consequently the Cartesian scale-tuple family is nonempty. -/
theorem taoPrimeTupleSlowScaleExponentTuples_nonempty
    (q : ℕ → ℕ) (x : ℕ) :
    (taoPrimeTupleSlowScaleExponentTuples q x).Nonempty := by
  obtain ⟨r, hr⟩ := taoPrimeTupleSlowDyadicExponents_nonempty q x
  exact ⟨fun _ => r,
    mem_taoPrimeTupleSlowScaleExponentTuples.mpr fun _ => hr⟩

/-- The ordered scale-tuple subfamily is also nonempty. -/
theorem taoPrimeTupleSlowOrderedScaleExponentTuples_nonempty
    (q : ℕ → ℕ) (x : ℕ) :
    (taoPrimeTupleSlowOrderedScaleExponentTuples q x).Nonempty := by
  obtain ⟨r, hr⟩ := taoPrimeTupleSlowDyadicExponents_nonempty q x
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hmem : (fun _ : Fin 1001 => r) ∈
      taoPrimeTupleSlowOrderedScaleExponentTuples q x :=
    mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mpr
      ⟨fun _ => hr, antitone_const⟩
  rw [hempty] at hmem
  simp at hmem

/-- All retained dyadic prime bands are eventually nonempty, uniformly over
the moving finite grid. -/
theorem eventually_forall_taoPrimeTupleSlowDyadicPrimeBand_nonempty
    (q : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ r ∈ taoPrimeTupleSlowDyadicExponents q x,
      (taoDyadicPrimeBand (2 ^ r)).Nonempty := by
  have hband := eventually_taoDyadicPrimeBand_nonempty
  rw [eventually_atTop] at hband
  obtain ⟨Z₀, hZ₀⟩ := hband
  filter_upwards
    [(tendsto_taoPrimeTupleSlowLowerCutoff_atTop q).eventually
      (eventually_ge_atTop (2 * Z₀))] with x hlower
  intro r hr
  have hscale : Z₀ ≤ 2 ^ r := by
    have hmeet := (mem_taoPrimeTupleSlowDyadicExponents.mp hr).2
    have hmeet' : taoPrimeTupleSlowLowerCutoff q x < 2 * 2 ^ r := by
      simpa only [pow_succ, mul_comm] using hmeet
    omega
  exact hZ₀ (2 ^ r) hscale

/-- Any coordinate selector from the moving grid tends to infinity. -/
theorem tendsto_taoPrimeTupleSlowDyadicScale_atTop
    {q r : ℕ → ℕ}
    (hr : ∀ᶠ x : ℕ in atTop,
      r x ∈ taoPrimeTupleSlowDyadicExponents q x) :
    Tendsto (fun x => 2 ^ r x) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  have hevent : ∀ᶠ x : ℕ in atTop,
      2 * b ≤ taoPrimeTupleSlowLowerCutoff q x ∧
        r x ∈ taoPrimeTupleSlowDyadicExponents q x :=
    ((tendsto_taoPrimeTupleSlowLowerCutoff_atTop q).eventually
      (eventually_ge_atTop (2 * b))).and hr
  rw [eventually_atTop] at hevent
  obtain ⟨a, ha⟩ := hevent
  refine ⟨a, fun x hx => ?_⟩
  have hdata := ha x hx
  have hmeet := (mem_taoPrimeTupleSlowDyadicExponents.mp hdata.2).2
  have hmeet' : taoPrimeTupleSlowLowerCutoff q x < 2 * 2 ^ r x := by
    simpa only [pow_succ, mul_comm] using hmeet
  omega

/-- Every coordinate selector from a grid whose row tends to infinity has
logarithmic scale ratio tending to one. -/
theorem tendsto_log_taoPrimeTupleSlowDyadicScale_div_log_taoZ
    {q r : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hr : ∀ᶠ x : ℕ in atTop,
      r x ∈ taoPrimeTupleSlowDyadicExponents q x) :
    Tendsto (fun x =>
      Real.log (((2 ^ r x : ℕ) : ℝ)) / Real.log (taoZ x))
        atTop (𝓝 1) := by
  have hlower := tendsto_log_taoSlowDiagonalCutoff_div_log_taoZ hq
  have hupper := tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ hq
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have htwo : Tendsto (fun x : ℕ =>
      Real.log (taoPrimeTupleSlowLowerCutoff q x) / Real.log (taoZ x) -
        Real.log 2 / Real.log (taoZ x)) atTop (𝓝 1) := by
    have hzero : Tendsto (fun x : ℕ =>
        Real.log 2 / Real.log (taoZ x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlogZ
    simpa only [taoPrimeTupleSlowLowerCutoff, sub_zero] using
      hlower.sub hzero
  apply htwo.squeeze' hupper
  · filter_upwards [hr,
      (tendsto_taoPrimeTupleSlowLowerCutoff_atTop q).eventually
        (eventually_ge_atTop 1),
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
        x hrx hlowerPos hz
    have hmeet := (mem_taoPrimeTupleSlowDyadicExponents.mp hrx).2
    have hscalePos : (0 : ℝ) < ((2 ^ r x : ℕ) : ℝ) := by positivity
    have hlowerRealPos : (0 : ℝ) < taoPrimeTupleSlowLowerCutoff q x := by
      exact_mod_cast (show 0 < taoPrimeTupleSlowLowerCutoff q x by omega)
    have hmeetReal : (taoPrimeTupleSlowLowerCutoff q x : ℝ) ≤
        2 * ((2 ^ r x : ℕ) : ℝ) := by
      have hmeetNat : taoPrimeTupleSlowLowerCutoff q x ≤ 2 * 2 ^ r x := by
        have hmeet' : taoPrimeTupleSlowLowerCutoff q x < 2 * 2 ^ r x := by
          simpa only [pow_succ, mul_comm] using hmeet
        omega
      exact_mod_cast hmeetNat
    have hlogs : Real.log (taoPrimeTupleSlowLowerCutoff q x) ≤
        Real.log (2 * ((2 ^ r x : ℕ) : ℝ)) :=
      Real.strictMonoOn_log.monotoneOn hlowerRealPos
        (mul_pos (by norm_num) hscalePos) hmeetReal
    rw [Real.log_mul (by norm_num) hscalePos.ne'] at hlogs
    have hlogZPos : 0 < Real.log (taoZ x) := Real.log_pos hz
    rw [sub_le_iff_le_add]
    calc
      Real.log (taoPrimeTupleSlowLowerCutoff q x) / Real.log (taoZ x) ≤
          (Real.log 2 + Real.log (((2 ^ r x : ℕ) : ℝ))) /
            Real.log (taoZ x) :=
        (div_le_div_iff_of_pos_right hlogZPos).2 hlogs
      _ = Real.log (((2 ^ r x : ℕ) : ℝ)) / Real.log (taoZ x) +
          Real.log 2 / Real.log (taoZ x) := by ring
  · filter_upwards [hr,
      (tendsto_taoPrimeTupleSlowLowerCutoff_atTop q).eventually
        (eventually_ge_atTop 1),
      tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
        x hrx hlowerPos hz
    have hupperPos : taoPrimeTupleSlowUpperCutoff q x ≠ 0 := by
      unfold taoPrimeTupleSlowUpperCutoff taoOneTermExponentCutoff
      exact (Nat.ceil_pos.mpr
        (Real.rpow_pos_of_pos (taoZ_pos x) _)).ne'
    have hbounds := taoPrimeTupleSlowDyadicScale_bounds hrx hupperPos
    have hscaleRealPos : (0 : ℝ) < ((2 ^ r x : ℕ) : ℝ) := by positivity
    have hupperRealPos : (0 : ℝ) < taoPrimeTupleSlowUpperCutoff q x := by
      exact_mod_cast Nat.pos_of_ne_zero hupperPos
    have hscaleUpperReal : (((2 ^ r x : ℕ) : ℝ)) ≤
        taoPrimeTupleSlowUpperCutoff q x := by exact_mod_cast hbounds.2
    have hlogs : Real.log (((2 ^ r x : ℕ) : ℝ)) ≤
        Real.log (taoPrimeTupleSlowUpperCutoff q x) :=
      Real.strictMonoOn_log.monotoneOn hscaleRealPos hupperRealPos
        hscaleUpperReal
    exact (div_le_div_iff_of_pos_right (Real.log_pos hz)).2 hlogs

/-- Coordinatewise selection from the moving grid automatically satisfies
the exact source-scale contract used throughout Proposition 6.6. -/
theorem taoPrimeTupleSourceScaleFamily_of_slowScaleExponentTupleSelector
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {R : ℕ → Fin 1001 → ℕ}
    (hR : ∀ᶠ x : ℕ in atTop,
      R x ∈ taoPrimeTupleSlowScaleExponentTuples q x) :
    TaoPrimeTupleSourceScaleFamily (fun x j => 2 ^ R x j) := by
  constructor
  · intro j
    apply tendsto_taoPrimeTupleSlowDyadicScale_atTop
    filter_upwards [hR] with x hx
    exact (mem_taoPrimeTupleSlowScaleExponentTuples.mp hx) j
  · intro j
    apply tendsto_log_taoPrimeTupleSlowDyadicScale_div_log_taoZ hq
    filter_upwards [hR] with x hx
    exact (mem_taoPrimeTupleSlowScaleExponentTuples.mp hx) j

/-- A harmless total repair of a finite scale family: empty dyadic bands are
replaced by the fixed nonempty band `[2,4)`.  On every eventually admissible
moving selector this repair is eventually the identity. -/
def taoPrimeTupleRepairScale (P : Fin 1001 → ℕ) : Fin 1001 → ℕ :=
  fun j => if (taoDyadicPrimeBand (P j)).Nonempty then P j else 2

theorem taoDyadicPrimeBand_two_nonempty :
    (taoDyadicPrimeBand 2).Nonempty := by
  exact ⟨2, mem_taoDyadicPrimeBand.mpr
    ⟨Nat.prime_two, le_rfl, by norm_num⟩⟩

theorem taoPrimeTupleRepairScale_band_nonempty
    (P : Fin 1001 → ℕ) (j : Fin 1001) :
    (taoDyadicPrimeBand (taoPrimeTupleRepairScale P j)).Nonempty := by
  unfold taoPrimeTupleRepairScale
  split_ifs with h
  · exact h
  · exact taoDyadicPrimeBand_two_nonempty

theorem eventually_taoPrimeTupleRepairScale_slowSelector_eq
    {q : ℕ → ℕ} {R : ℕ → Fin 1001 → ℕ}
    (hR : ∀ᶠ x : ℕ in atTop,
      R x ∈ taoPrimeTupleSlowScaleExponentTuples q x) :
    ∀ᶠ x : ℕ in atTop,
      taoPrimeTupleRepairScale (fun j => 2 ^ R x j) =
        (fun j => 2 ^ R x j) := by
  filter_upwards [hR,
    eventually_forall_taoPrimeTupleSlowDyadicPrimeBand_nonempty q] with
      x hx hbands
  funext j
  have hj := (mem_taoPrimeTupleSlowScaleExponentTuples.mp hx) j
  simp [taoPrimeTupleRepairScale, hbands (R x j) hj]

/-- The total repaired selector retains the source-scale asymptotics. -/
theorem taoPrimeTupleSourceScaleFamily_repaired_slowScaleExponentTupleSelector
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {R : ℕ → Fin 1001 → ℕ}
    (hR : ∀ᶠ x : ℕ in atTop,
      R x ∈ taoPrimeTupleSlowScaleExponentTuples q x) :
    TaoPrimeTupleSourceScaleFamily
      (fun x => taoPrimeTupleRepairScale (fun j => 2 ^ R x j)) := by
  have hsource :=
    taoPrimeTupleSourceScaleFamily_of_slowScaleExponentTupleSelector hq hR
  have heq := eventually_taoPrimeTupleRepairScale_slowSelector_eq hR
  constructor
  · intro j
    apply (hsource.tendsto_scale j).congr'
    filter_upwards [heq] with x hx
    exact congrFun hx j |>.symm
  · intro j
    apply (hsource.log_ratio j).congr'
    filter_upwards [heq] with x hx
    rw [congrFun hx j]

/-- Proposition 6.6 and both finite summations, specialized to any one
selector from the moving grid, with the named constant independent of that
selector.  The repair disappears from the eventual conclusion. -/
theorem eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_slowSelector_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {R : ℕ → Fin 1001 → ℕ}
    (hR : ∀ᶠ x : ℕ in atTop,
      R x ∈ taoPrimeTupleSlowScaleExponentTuples q x) :
    ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleTypicalDyadicRemainderTriples
          (fun j => 2 ^ R x j) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        2 * (psiNat
            (taoPrimeTupleRemainderBudget x (fun j => 2 ^ R x j))
            (taoPrimeTupleRemainderSmoothnessCutoff
              (fun j => 2 ^ R x j)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
                (8 * iteratedLog x) ^ (50 : ℕ) /
              Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (2 ^ R x j)).card : ℝ)) := by
  let P : ℕ → Fin 1001 → ℕ := fun x =>
    taoPrimeTupleRepairScale (fun j => 2 ^ R x j)
  have hscale : TaoPrimeTupleSourceScaleFamily P := by
    simpa only [P] using
      taoPrimeTupleSourceScaleFamily_repaired_slowScaleExponentTupleSelector
        hq hR
  have hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty := by
    intro x j
    exact taoPrimeTupleRepairScale_band_nonempty _ _
  have hcount :=
    eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP (taoPrimeTupleSlowLowerCutoff q)
  filter_upwards [hcount,
    eventually_taoPrimeTupleRepairScale_slowSelector_eq hR] with
      x hx heq
  simpa only [P, heq] using hx

/-- Existential compatibility wrapper for one moving-grid selector. -/
theorem exists_eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_slowSelector_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {R : ℕ → Fin 1001 → ℕ}
    (hR : ∀ᶠ x : ℕ in atTop,
      R x ∈ taoPrimeTupleSlowScaleExponentTuples q x) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleTypicalDyadicRemainderTriples
          (fun j => 2 ^ R x j) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        2 * (psiNat
            (taoPrimeTupleRemainderBudget x (fun j => 2 ^ R x j))
            (taoPrimeTupleRemainderSmoothnessCutoff
              (fun j => 2 ^ R x j)) : ℝ) *
          ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
              Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (2 ^ R x j)).card : ℝ)) := by
  exact ⟨taoPrimeTupleTypicalUniformSourceConstant hC hburgess,
    taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess,
    eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_slowSelector_uniformConstant_of_explicitBurgess
      hC hburgess hq hR⟩

/-- The evaluated Proposition 6.6 counting bound for one member of the moving
finite scale grid. -/
def TaoPrimeTupleSlowScaleCountBound
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q : ℕ → ℕ) (x : ℕ) (R : Fin 1001 → ℕ) : Prop :=
  ((taoPrimeTupleTypicalDyadicRemainderTriples
      (fun j => 2 ^ R j) x
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
    2 * (psiNat
        (taoPrimeTupleRemainderBudget x (fun j => 2 ^ R j))
        (taoPrimeTupleRemainderSmoothnessCutoff
          (fun j => 2 ^ R j)) : ℝ) *
      ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ)) *
        ∏ j, ((taoDyadicPrimeBand (2 ^ R j)).card : ℝ))

/-- Proposition 6.6 now holds simultaneously for every member of the moving
finite scale grid.  The selector argument is legitimate precisely because the
bound above was chosen before the selector. -/
theorem eventually_forall_taoPrimeTupleSlowScaleCountBound_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop, ∀ R ∈ taoPrimeTupleSlowScaleExponentTuples q x,
      TaoPrimeTupleSlowScaleCountBound hC hburgess q x R := by
  let S : ℕ → (Fin 1001 → ℕ) → Prop := fun x R =>
    R ∈ taoPrimeTupleSlowScaleExponentTuples q x
  let Q : ℕ → (Fin 1001 → ℕ) → Prop := fun x R =>
    TaoPrimeTupleSlowScaleCountBound hC hburgess q x R
  have hne : ∀ᶠ x : ℕ in atTop, ∃ R, S x R :=
    Filter.Eventually.of_forall fun x => by
      simpa only [S] using taoPrimeTupleSlowScaleExponentTuples_nonempty q x
  have hselector : ∀ f : ℕ → (Fin 1001 → ℕ),
      (∀ᶠ x : ℕ in atTop, S x (f x)) →
        ∀ᶠ x : ℕ in atTop, Q x (f x) := by
    intro f hf
    have hcount :=
      eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_slowSelector_uniformConstant_of_explicitBurgess
        hC hburgess hq (by simpa only [S] using hf)
    simpa only [Q, TaoPrimeTupleSlowScaleCountBound] using hcount
  have hu := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hu] with x hx R hR
  exact hx R hR

/-- Ordered scale tuples inherit the same simultaneous bound. -/
theorem eventually_forall_taoPrimeTupleSlowOrderedScaleCountBound_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ∀ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        TaoPrimeTupleSlowScaleCountBound hC hburgess q x R := by
  filter_upwards
    [eventually_forall_taoPrimeTupleSlowScaleCountBound_of_explicitBurgess
      hC hburgess hq] with x hx R hR
  exact hx R
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr
      (mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hR).1)

/-- The prime tuple canonically attached to an anatomy packet. -/
def taoPrimeTupleOfTypicalAnatomy
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) : TaoPrimeTuple :=
  Fin.cases p₀ a.factors

@[simp] theorem taoPrimeTupleOfTypicalAnatomy_zero
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    taoPrimeTupleOfTypicalAnatomy a 0 = p₀ := by
  simp [taoPrimeTupleOfTypicalAnatomy]

@[simp] theorem taoPrimeTupleOfTypicalAnatomy_succ
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) (i : Fin 1000) :
    taoPrimeTupleOfTypicalAnatomy a i.succ = a.factors i := by
  simp [taoPrimeTupleOfTypicalAnatomy]

/-- The canonical anatomy tuple is nonincreasing. -/
theorem antitone_taoPrimeTupleOfTypicalAnatomy
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    Antitone (taoPrimeTupleOfTypicalAnatomy a) := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp
    · simpa using a.factor_le_p₀ j
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp at hij
    · simpa using a.factors_nonincreasing
        (Fin.succ_le_succ_iff.mp hij)

/-- The dyadic logarithms of a canonical anatomy tuple belong to the ordered
moving scale family. -/
theorem typicalAnatomy_natLog_mem_slowOrderedScaleExponentTuples
    {q : ℕ → ℕ} {x : ℕ} {p₀ m : ℕ}
    (a : TypicalPrimeAnatomy
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoPrimeTupleSlowUpperCutoff q x) p₀ m) :
    (fun j => Nat.log 2 (taoPrimeTupleOfTypicalAnatomy a j)) ∈
      taoPrimeTupleSlowOrderedScaleExponentTuples q x := by
  apply mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mpr
  constructor
  · intro j
    apply natLog_mem_taoPrimeTupleSlowDyadicExponents_of_bounds
    · refine Fin.cases ?_ (fun i => ?_) j
      · exact a.lower_le_p₀
      · simpa using a.lower_le_factor i
    · refine Fin.cases ?_ (fun i => ?_) j
      · exact a.p₀_le_upper
      · simpa using a.factor_le_upper i
  · intro i j hij
    exact Nat.log_mono_right
      (antitone_taoPrimeTupleOfTypicalAnatomy a hij)

end

end Tao2026
