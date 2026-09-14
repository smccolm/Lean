import Tao2026.BadIntervalTypicalGlobal
import Tao2026.BadIntervalLargePrimeBlockSum

/-!
# Assembly of the typical prime-tuple count

This module compares the original dyadic prime alphabets in Proposition 6.6
with the enlarged alphabets used by the bounded-multiplicity map.  The
comparison is uniform over the moving finite scale grid, so the simultaneous
per-scale estimate can be summed before applying the global fiber bound.
-/

namespace Tao2026

open Filter Topology Asymptotics
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

private theorem eventually_card_taoDyadicPrimeBand_le_eight_mul_scaled
    {c : ℕ} (hc : 1 ≤ c) :
    ∀ᶠ R : ℕ in atTop,
      ((taoDyadicPrimeBand R).card : ℝ) ≤
        8 * ((taoDyadicPrimeBand (c * R)).card : ℝ) := by
  have hupperEvent := eventually_card_taoDyadicPrimeBand_le_two_mul_div_log
  have hlowerEvent := eventually_nat_div_two_log_le_card_taoDyadicPrimeBand
  rw [eventually_atTop] at hupperEvent hlowerEvent ⊢
  obtain ⟨N₁, hN₁⟩ := hupperEvent
  obtain ⟨N₂, hN₂⟩ := hlowerEvent
  refine ⟨max (max N₁ N₂) (max c 2), ?_⟩
  intro R hR
  have hRN₁ : N₁ ≤ R := le_trans (le_max_left N₁ N₂)
    (le_trans (le_max_left (max N₁ N₂) (max c 2)) hR)
  have hRN₂ : N₂ ≤ R := le_trans (le_max_right N₁ N₂)
    (le_trans (le_max_left (max N₁ N₂) (max c 2)) hR)
  have hcR : c ≤ R := le_trans (le_max_left c 2)
    (le_trans (le_max_right (max N₁ N₂) (max c 2)) hR)
  have hRtwo : 2 ≤ R := le_trans (le_max_right c 2)
    (le_trans (le_max_right (max N₁ N₂) (max c 2)) hR)
  have hcRN₂ : N₂ ≤ c * R := hRN₂.trans (Nat.le_mul_of_pos_left R (by omega))
  have hupper := hN₁ R hRN₁
  have hlower := hN₂ (c * R) hcRN₂
  have hRpos : (0 : ℝ) < R := by positivity
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hc)
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hRtwo)
  have hlogcR : 0 < Real.log (c * R : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < c * R by nlinarith)
  have hlogc_le : Real.log (c : ℝ) ≤ Real.log (R : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hcpos hRpos (by exact_mod_cast hcR)
  have hlog_scaled : Real.log (c * R : ℕ) ≤ 2 * Real.log (R : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hcpos.ne' hRpos.ne']
    linarith
  have hratio :
      2 * ((R : ℝ) / Real.log R) ≤
        8 * ((c * R : ℕ) / (2 * Real.log (c * R : ℕ))) := by
    rw [← mul_div_assoc, ← mul_div_assoc]
    rw [div_le_div_iff₀ hlogR (mul_pos (by norm_num) hlogcR)]
    have hscaled := mul_le_mul_of_nonneg_left hlog_scaled
      (show 0 ≤ 4 * (R : ℝ) by positivity)
    have hcOne : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have hcMul := mul_le_mul_of_nonneg_right hcOne
      (mul_nonneg (by positivity : (0 : ℝ) ≤ R) hlogR.le)
    push_cast at hscaled ⊢
    calc
      (2 * (R : ℝ)) * (2 * Real.log ((c : ℝ) * R)) =
          (4 * (R : ℝ)) * Real.log ((c : ℝ) * R) := by ring
      _ ≤ (4 * (R : ℝ)) * (2 * Real.log (R : ℝ)) := hscaled
      _ ≤ (8 * (c : ℝ) * R) * Real.log (R : ℝ) := by
        nlinarith
      _ = 8 * ((c : ℝ) * R) * Real.log (R : ℝ) := by ring
  calc
    ((taoDyadicPrimeBand R).card : ℝ) ≤
        2 * ((R : ℝ) / Real.log R) := hupper
    _ ≤ 8 * ((c * R : ℕ) / (2 * Real.log (c * R : ℕ))) := hratio
    _ ≤ 8 * ((taoDyadicPrimeBand (c * R)).card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlower (by norm_num)

/-- Eventually an original dyadic prime alphabet is at most eight times its
tail-coordinate enlarged alphabet. -/
theorem eventually_card_taoDyadicPrimeBand_le_eight_mul_doubleBand :
    ∀ᶠ R : ℕ in atTop,
      ((taoDyadicPrimeBand R).card : ℝ) ≤
        8 * ((taoDyadicPrimeBand (2 * R)).card : ℝ) :=
  eventually_card_taoDyadicPrimeBand_le_eight_mul_scaled (by norm_num)

/-- The same uniform comparison for the distinguished squared coordinate. -/
theorem eventually_card_taoDyadicPrimeBand_le_eight_mul_quadrupleBand :
    ∀ᶠ R : ℕ in atTop,
      ((taoDyadicPrimeBand R).card : ℝ) ≤
        8 * ((taoDyadicPrimeBand (4 * R)).card : ℝ) :=
  eventually_card_taoDyadicPrimeBand_le_eight_mul_scaled (by norm_num)

/-- All 1001 alphabet comparisons hold simultaneously on the moving grid. -/
theorem eventually_forall_taoPrimeTuple_originalBand_card_le_eight_mul_enlargedBand
    (q : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ∀ R ∈ taoPrimeTupleSlowScaleExponentTuples q x, ∀ j,
        ((taoDyadicPrimeBand (taoPrimeTupleDyadicScales R j)).card : ℝ) ≤
          8 * ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ) := by
  have hdouble :=
    eventually_card_taoDyadicPrimeBand_le_eight_mul_doubleBand
  have hquadruple :=
    eventually_card_taoDyadicPrimeBand_le_eight_mul_quadrupleBand
  rw [eventually_atTop] at hdouble hquadruple
  obtain ⟨N₂, hN₂⟩ := hdouble
  obtain ⟨N₄, hN₄⟩ := hquadruple
  filter_upwards
    [(tendsto_taoPrimeTupleSlowLowerCutoff_atTop q).eventually
      (eventually_ge_atTop (2 * max N₂ N₄))] with x hx
  intro R hR j
  have hjGrid := (mem_taoPrimeTupleSlowScaleExponentTuples.mp hR) j
  have hmeet := (mem_taoPrimeTupleSlowDyadicExponents.mp hjGrid).2
  have hscale : max N₂ N₄ ≤ taoPrimeTupleDyadicScales R j := by
    unfold taoPrimeTupleDyadicScales
    rw [pow_succ] at hmeet
    omega
  by_cases hj : j = 0
  · subst j
    simpa [taoPrimeTupleEnlargedScale, taoPrimeTupleDyadicScales] using
      hN₄ (2 ^ R 0) ((le_max_right N₂ N₄).trans hscale)
  · simpa [taoPrimeTupleEnlargedScale, taoPrimeTupleDyadicScales, hj] using
      hN₂ (2 ^ R j) ((le_max_left N₂ N₄).trans hscale)

/-- Consequently the entire original Cartesian alphabet is at most
`8 ^ 1001` times the enlarged Cartesian alphabet. -/
theorem eventually_forall_taoPrimeTuple_originalBandProduct_le_enlargedBandProduct
    (q : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ∀ R ∈ taoPrimeTupleSlowScaleExponentTuples q x,
        (∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleDyadicScales R j)).card : ℝ)) ≤
          8 ^ (1001 : ℕ) *
            ∏ j, ((taoDyadicPrimeBand
              (taoPrimeTupleEnlargedScale
                (taoPrimeTupleDyadicScales R) j)).card : ℝ) := by
  filter_upwards
    [eventually_forall_taoPrimeTuple_originalBand_card_le_eight_mul_enlargedBand q]
      with x hx R hR
  calc
    (∏ j, ((taoDyadicPrimeBand
        (taoPrimeTupleDyadicScales R j)).card : ℝ)) ≤
        ∏ j, (8 * ((taoDyadicPrimeBand
          (taoPrimeTupleEnlargedScale
            (taoPrimeTupleDyadicScales R) j)).card : ℝ)) := by
      exact Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => hx R hR j
    _ = (∏ _j : Fin 1001, (8 : ℝ)) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ) := by
      rw [Finset.prod_mul_distrib]
    _ = 8 ^ (1001 : ℕ) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ) := by
      congr 1
      rw [Finset.prod_const]
      simp only [Finset.card_univ, Fintype.card_fin]

/-- The dimensionless loss left after replacing all original prime alphabets
by their enlarged counterparts. -/
def taoPrimeTupleTypicalAssemblyFactor
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) (x : ℕ) : ℝ :=
  2 * (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
    ((8 * iteratedLog x) ^ (50 : ℕ) /
      Real.log (taoZ x) ^ (2 : ℕ))) *
    8 ^ (1001 : ℕ)

theorem taoPrimeTupleTypicalAssemblyFactor_nonneg
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) (x : ℕ) :
    0 ≤ taoPrimeTupleTypicalAssemblyFactor hC hburgess x := by
  unfold taoPrimeTupleTypicalAssemblyFactor
  have hB := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
  positivity

/-- The logarithmic loss supplied by Proposition 6.6 vanishes.  The exact
identity `log x = 2 log(z)^2 / log₂ x` reduces this to the standard fact that
a fixed power of `log t` is little-o of `t`. -/
theorem tendsto_taoPrimeTupleTypical_logarithmicFactor_zero :
    Tendsto (fun x : ℕ =>
      (8 * iteratedLog x) ^ (50 : ℕ) /
        Real.log (taoZ x) ^ (2 : ℕ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun x : ℕ =>
      iteratedLog x ^ (49 : ℕ) / Real.log x) atTop (𝓝 0) := by
    simpa only [iteratedLog] using
      (Real.isLittleO_pow_log_id_atTop (n := 49)).tendsto_div_nhds_zero.comp hlog
  have hscaled : Tendsto (fun x : ℕ =>
      (2 * 8 ^ (50 : ℕ) : ℝ) *
        (iteratedLog x ^ (49 : ℕ) / Real.log x)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hbase
  apply hscaled.congr'
  filter_upwards
    [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
     tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with x hlogX hiterX
  have hidentity :=
    log_nat_eq_two_mul_log_taoZ_sq_div_iteratedLog hlogX hiterX
  have hidentity' := (eq_div_iff hiterX.ne').mp hidentity
  have hdenominator :
      Real.log (taoZ x) ^ (2 : ℕ) =
        Real.log x * iteratedLog x / 2 := by
    nlinarith [hidentity']
  rw [hdenominator]
  field_simp [hlogX.ne', hiterX.ne']

theorem tendsto_taoPrimeTupleTypicalAssemblyFactor_zero
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    Tendsto (taoPrimeTupleTypicalAssemblyFactor hC hburgess)
      atTop (𝓝 0) := by
  have hcoefficient : Tendsto (fun x : ℕ =>
      taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
        ((8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ))) atTop (𝓝 0) := by
    simpa using
      tendsto_taoPrimeTupleTypical_logarithmicFactor_zero.const_mul
        (taoPrimeTupleTypicalUniformSourceConstant hC hburgess)
  have hleft : Tendsto (fun x : ℕ =>
      2 * (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
        ((8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ)))) atTop (𝓝 0) := by
    simpa using hcoefficient.const_mul (2 : ℝ)
  have hfull : Tendsto (fun x : ℕ =>
      2 * (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
        ((8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ))) *
        (8 ^ (1001 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa using hleft.mul_const (8 ^ (1001 : ℕ) : ℝ)
  change Tendsto (fun x : ℕ =>
      2 * (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
        ((8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ))) *
        (8 ^ (1001 : ℕ) : ℝ)) atTop (𝓝 0)
  exact hfull

/-- At one scale, the Proposition 6.6 count is bounded by the assembly
factor times the exact enlarged source cardinality. -/
theorem taoPrimeTupleSlowScaleCountBound_le_assemblyFactor_mul_enlarged
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} {x : ℕ} {R : Fin 1001 → ℕ}
    (hcount : TaoPrimeTupleSlowScaleCountBound hC hburgess q x R)
    (hprod :
      (∏ j, ((taoDyadicPrimeBand
          (taoPrimeTupleDyadicScales R j)).card : ℝ)) ≤
        8 ^ (1001 : ℕ) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ)) :
    ((taoPrimeTupleTypicalDyadicRemainderTriples
        (taoPrimeTupleDyadicScales R) x
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
      taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
        ((taoPrimeTupleEnlargedRemainderPairs
          (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
  let A : ℝ := 2 *
    (psiNat
      (taoPrimeTupleRemainderBudget x (taoPrimeTupleDyadicScales R))
      (taoPrimeTupleRemainderSmoothnessCutoff
        (taoPrimeTupleDyadicScales R)) : ℝ) *
    (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
      (8 * iteratedLog x) ^ (50 : ℕ) /
        Real.log (taoZ x) ^ (2 : ℕ))
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    have hB := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
    positivity
  calc
    ((taoPrimeTupleTypicalDyadicRemainderTriples
        (taoPrimeTupleDyadicScales R) x
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        2 *
          (psiNat
            (taoPrimeTupleRemainderBudget x (taoPrimeTupleDyadicScales R))
            (taoPrimeTupleRemainderSmoothnessCutoff
              (taoPrimeTupleDyadicScales R)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
              (8 * iteratedLog x) ^ (50 : ℕ) /
                Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand
              (taoPrimeTupleDyadicScales R j)).card : ℝ)) := by
      simpa only [TaoPrimeTupleSlowScaleCountBound,
        taoPrimeTupleDyadicScales] using hcount
    _ = A * (∏ j, ((taoDyadicPrimeBand
          (taoPrimeTupleDyadicScales R j)).card : ℝ)) := by
      dsimp [A]
      ac_rfl
    _ ≤ A * (8 ^ (1001 : ℕ) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod hAnonneg
    _ = taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
        ((taoPrimeTupleEnlargedRemainderPairs
          (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      rw [card_taoPrimeTupleEnlargedRemainderPairs, Nat.cast_mul,
        Nat.cast_prod]
      unfold taoPrimeTupleTypicalAssemblyFactor A
      rw [mul_div_assoc]
      ac_rfl

/-- The fixed-scale comparison above holds simultaneously on the entire
ordered moving grid. -/
theorem eventually_forall_taoPrimeTupleSlowOrderedScaleCount_le_assembly
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ∀ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        ((taoPrimeTupleTypicalDyadicRemainderTriples
            (taoPrimeTupleDyadicScales R) x
            (taoPrimeTupleSlowLowerCutoff q x)
            (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
          taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
            ((taoPrimeTupleEnlargedRemainderPairs
              (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
  filter_upwards
    [eventually_forall_taoPrimeTupleSlowOrderedScaleCountBound_of_explicitBurgess
      hC hburgess hq,
     eventually_forall_taoPrimeTuple_originalBandProduct_le_enlargedBandProduct q]
      with x hcount hprod R hR
  apply taoPrimeTupleSlowScaleCountBound_le_assemblyFactor_mul_enlarged
    hC hburgess (hcount R hR)
  exact hprod R
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr
      (mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hR).1)

/-- The complete typical family, summed over ordered prime-scale tuples as
well as dyadic interval lengths and smooth remainders. -/
def taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples
    (q : ℕ → ℕ) (x : ℕ) :
    Finset (Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple) :=
  (taoPrimeTupleSlowOrderedScaleExponentTuples q x).sigma fun R =>
    taoPrimeTupleTypicalDyadicRemainderTriples
      (taoPrimeTupleDyadicScales R) x
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoLargePrimeSourceUpperCutoff x)

theorem mem_taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples
    {q : ℕ → ℕ} {x : ℕ}
    {a : Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple} :
    a ∈ taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x ↔
      a.1 ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x ∧
        a.2 ∈ taoPrimeTupleTypicalDyadicRemainderTriples
          (taoPrimeTupleDyadicScales a.1) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x) := by
  simp [taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples]

theorem card_taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples
    (q : ℕ → ℕ) (x : ℕ) :
    (taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x).card =
      ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        (taoPrimeTupleTypicalDyadicRemainderTriples
          (taoPrimeTupleDyadicScales R) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x)).card := by
  rw [taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples,
    Finset.card_sigma]

/-- Summing the simultaneous fixed-scale estimates gives a single comparison
between the complete typical and enlarged global families. -/
theorem eventually_card_taoPrimeTupleGlobalTypical_le_assemblyFactor_mul_enlarged
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x).card : ℝ) ≤
        taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
          ((taoPrimeTupleGlobalEnlargedRemainderPairs q x).card : ℝ) := by
  filter_upwards
    [eventually_forall_taoPrimeTupleSlowOrderedScaleCount_le_assembly
      hC hburgess hq] with x hx
  rw [card_taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples,
    Nat.cast_sum, card_taoPrimeTupleGlobalEnlargedRemainderPairs,
    Nat.cast_sum]
  calc
    (∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        ((taoPrimeTupleTypicalDyadicRemainderTriples
          (taoPrimeTupleDyadicScales R) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ)) ≤
        ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
          taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
            ((taoPrimeTupleEnlargedRemainderPairs
              (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      exact Finset.sum_le_sum fun R hR => hx R hR
    _ = taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
        ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
          ((taoPrimeTupleEnlargedRemainderPairs
            (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      rw [Finset.mul_sum]

/-- The complete typical family is therefore controlled by one dilated
one-term count, the absolute global fiber multiplicity, and the assembly
factor. -/
theorem eventually_card_taoPrimeTupleGlobalTypical_le_assemblyFactor_mul_badOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x).card : ℝ) ≤
        taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := by
  filter_upwards
    [eventually_card_taoPrimeTupleGlobalTypical_le_assemblyFactor_mul_enlarged
      hC hburgess hq,
     (tendsto_taoPrimeTupleSlowLowerCutoff_atTop q).eventually
      (eventually_ge_atTop 2)] with x htyp hlower
  calc
    ((taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x).card : ℝ) ≤
        taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
          ((taoPrimeTupleGlobalEnlargedRemainderPairs q x).card : ℝ) := htyp
    _ ≤ taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _
        (taoPrimeTupleTypicalAssemblyFactor_nonneg hC hburgess x)
      exact_mod_cast
        card_taoPrimeTupleGlobalEnlargedRemainderPairs_le_badOneTermCount_mul
          hlower

/-- Conditional on the explicit Burgess input, the assembled typical count
is little-o of the one-term count at the fixed enlarged endpoint. -/
theorem card_taoPrimeTupleGlobalTypical_isLittleO_dilatedBadOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    (fun x : ℕ =>
      ((taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x).card : ℝ))
      =o[atTop]
    (fun x : ℕ =>
      (badOneTermCount (2 * taoPrimeTupleEnlargementFactor * x) : ℝ)) := by
  apply IsLittleO.of_bound
  intro ε hε
  let M : ℝ := (1000 : ℝ) ^ (1000 : ℕ)
  have hMpos : 0 < M := by
    exact pow_pos (by norm_num) 1000
  have hsmall := (tendsto_taoPrimeTupleTypicalAssemblyFactor_zero
    hC hburgess).eventually (Iio_mem_nhds (div_pos hε hMpos))
  filter_upwards
    [eventually_card_taoPrimeTupleGlobalTypical_le_assemblyFactor_mul_badOneTermCount
      hC hburgess hq, hsmall] with x hbound hfactor
  have hfactorM :
      taoPrimeTupleTypicalAssemblyFactor hC hburgess x * M ≤ ε :=
    (le_div_iff₀ hMpos).mp hfactor.le
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤
      (taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x).card),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x))]
  calc
    ((taoPrimeTupleGlobalTypicalDyadicRemainderQuadruples q x).card : ℝ) ≤
        taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := hbound
    _ = (taoPrimeTupleTypicalAssemblyFactor hC hburgess x * M) *
          (badOneTermCount
            (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) := by
      rw [Nat.cast_mul]
      rw [Nat.cast_pow]
      change taoPrimeTupleTypicalAssemblyFactor hC hburgess x *
        ((badOneTermCount
          (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) * M) = _
      ac_rfl
    _ ≤ ε *
          (badOneTermCount
            (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) :=
      mul_le_mul_of_nonneg_right hfactorM (by positivity)

end

end Tao2026
