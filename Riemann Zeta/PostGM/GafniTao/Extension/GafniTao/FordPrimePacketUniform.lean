import GafniTao.FordPrimePacketEventually
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A uniform quantitative prime-packet threshold

The PNT error threshold used here is chosen once, at the fixed relative
width `1/100`; it does not depend on Ford's degree `k`.  Above that one fixed
threshold, the elementary lower bound for the Chebyshev mass and
`log x = o(sqrt x)` give at least `k^3` primes as soon as
`M >= (200 k^3)^2`.  This removes the opaque `k`-dependent threshold that
would otherwise prevent uniform use of Ford's moment theorem when
`k` varies with the logarithmic scale.
-/

open Filter Finset
open scoped Topology

namespace GafniTao

noncomputable section

def fordUniformPrimeWidth : ℝ := 1 / 100

theorem fordUniformPrimeWidth_pos : 0 < fordUniformPrimeWidth := by
  norm_num [fordUniformPrimeWidth]

/-- A single natural threshold for the fixed-width Chebyshev mass estimate. -/
theorem exists_fordUniformPrimeMassThreshold :
    ∃ N₀ : ℕ, ∀ M : ℕ, N₀ ≤ M →
      3 * fordUniformPrimeWidth * (M : ℝ) / 4 ≤
        Chebyshev.theta ((1 + fordUniformPrimeWidth) * (M : ℝ)) -
          Chebyshev.theta M := by
  have h := (eventually_chebyshev_relative_interval_lower
    fordUniformPrimeWidth_pos).filter_mono tendsto_natCast_atTop_atTop
  exact eventually_atTop.1 h

def fordUniformPrimeMassThreshold : ℕ :=
  Classical.choose exists_fordUniformPrimeMassThreshold

theorem fordUniformPrimeMassThreshold_spec
    {M : ℕ} (hM : fordUniformPrimeMassThreshold ≤ M) :
    3 * fordUniformPrimeWidth * (M : ℝ) / 4 ≤
      Chebyshev.theta ((1 + fordUniformPrimeWidth) * (M : ℝ)) -
        Chebyshev.theta M :=
  (Classical.choose_spec exists_fordUniformPrimeMassThreshold) M hM

/-- The second fixed threshold makes the logarithmic cost of one prime at
the right endpoint at most `sqrt M`. -/
theorem exists_fordUniformPrimeLogThreshold :
    ∃ N₁ : ℕ, ∀ M : ℕ, N₁ ≤ M →
      Real.log ((1 + fordUniformPrimeWidth) * (M : ℝ)) ≤ Real.sqrt M := by
  have hlog :
      (fun x : ℝ => Real.log ((1 + fordUniformPrimeWidth) * x)) =o[atTop]
        (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    have hone : 0 < 1 + fordUniformPrimeWidth := by
      linarith [fordUniformPrimeWidth_pos]
    have heq :
        (fun x : ℝ => Real.log (1 + fordUniformPrimeWidth) + Real.log x) =ᶠ[atTop]
          (fun x : ℝ => Real.log ((1 + fordUniformPrimeWidth) * x)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.log_mul (ne_of_gt hone) (ne_of_gt hx)]
    exact (((Asymptotics.isLittleO_const_id_atTop
      (Real.log (1 + fordUniformPrimeWidth))).comp_tendsto
        (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num))).add
      (isLittleO_log_rpow_atTop (by norm_num))).congr'
        heq (EventuallyEq.rfl)
  rw [Asymptotics.isLittleO_iff] at hlog
  have hbound := hlog (show (0 : ℝ) < 1 by norm_num)
  have hnat := tendsto_natCast_atTop_atTop.eventually hbound
  have hsqrt : ∀ M : ℕ,
      ((M : ℝ) ^ (1 / 2 : ℝ)) = Real.sqrt M := by
    intro M
    symm
    exact Real.sqrt_eq_rpow (M : ℝ)
  apply eventually_atTop.1
  filter_upwards [hnat, eventually_ge_atTop (1 : ℕ)] with M hM hMone
  have hnonneg : 0 ≤ Real.log ((1 + fordUniformPrimeWidth) * (M : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ M := by exact_mod_cast hMone
    nlinarith [fordUniformPrimeWidth_pos]
  have habs :
      |Real.log ((1 + fordUniformPrimeWidth) * (M : ℝ))| ≤
        |(M : ℝ) ^ (1 / 2 : ℝ)| := by
    simpa only [Real.norm_eq_abs, one_mul] using hM
  rw [abs_of_nonneg hnonneg,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at habs
  exact habs.trans_eq (hsqrt M)

def fordUniformPrimeLogThreshold : ℕ :=
  Classical.choose exists_fordUniformPrimeLogThreshold

theorem fordUniformPrimeLogThreshold_spec
    {M : ℕ} (hM : fordUniformPrimeLogThreshold ≤ M) :
    Real.log ((1 + fordUniformPrimeWidth) * (M : ℝ)) ≤ Real.sqrt M :=
  (Classical.choose_spec exists_fordUniformPrimeLogThreshold) M hM

/-- A fixed analytic base, independent of `k`. -/
def fordUniformPrimeThreshold : ℕ :=
  max 2 (max fordUniformPrimeMassThreshold fordUniformPrimeLogThreshold)

theorem fordUniformPrimeThreshold_two : 2 ≤ fordUniformPrimeThreshold :=
  le_max_left _ _

/-- The explicit polynomial scale beyond the one fixed analytic threshold. -/
def fordPrimePacketScaleThreshold (k : ℕ) : ℕ :=
  max fordUniformPrimeThreshold ((200 * k ^ 3) ^ 2)

theorem fordPrimeInterval_fixedWidth_card_ge
    {k M : ℕ} (hM : fordPrimePacketScaleThreshold k ≤ M) :
    k ^ 3 ≤
      (fordPrimeInterval M
        (fordRelativePrimeBound fordUniformPrimeWidth M)).card := by
  let B := fordRelativePrimeBound fordUniformPrimeWidth M
  have hthreshold : fordUniformPrimeThreshold ≤ M :=
    (le_max_left _ _).trans hM
  have hMtwo : 2 ≤ M := fordUniformPrimeThreshold_two.trans hthreshold
  have hmassToInner : fordUniformPrimeMassThreshold ≤
      max fordUniformPrimeMassThreshold fordUniformPrimeLogThreshold :=
    le_max_left _ _
  have hlogToInner : fordUniformPrimeLogThreshold ≤
      max fordUniformPrimeMassThreshold fordUniformPrimeLogThreshold :=
    le_max_right _ _
  have hinnerToThreshold :
      max fordUniformPrimeMassThreshold fordUniformPrimeLogThreshold ≤
        fordUniformPrimeThreshold := le_max_right _ _
  have hmassThreshold : fordUniformPrimeMassThreshold ≤ M :=
    hmassToInner.trans (hinnerToThreshold.trans hthreshold)
  have hlogThreshold : fordUniformPrimeLogThreshold ≤ M :=
    hlogToInner.trans (hinnerToThreshold.trans hthreshold)
  have hmass := fordUniformPrimeMassThreshold_spec hmassThreshold
  have hlog := fordUniformPrimeLogThreshold_spec hlogThreshold
  have hMB : M ≤ B := ford_le_relativePrimeBound
    fordUniformPrimeWidth_pos.le M
  have hBpos : 0 < B := lt_of_lt_of_le (by omega) hMB
  have hMposR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hypos : 0 < (1 + fordUniformPrimeWidth) * (M : ℝ) := by
    exact mul_pos (by linarith [fordUniformPrimeWidth_pos]) hMposR
  have hB_le_y : (B : ℝ) ≤ (1 + fordUniformPrimeWidth) * (M : ℝ) := by
    dsimp [B, fordRelativePrimeBound]
    exact Nat.floor_le hypos.le
  have hlogB : Real.log B ≤ Real.sqrt M :=
    (Real.log_le_log (by exact_mod_cast hBpos) hB_le_y).trans hlog
  have hthetaFloor :
      Chebyshev.theta ((1 + fordUniformPrimeWidth) * (M : ℝ)) =
        Chebyshev.theta B := by
    simpa [B, fordRelativePrimeBound] using
      Chebyshev.theta_eq_theta_coe_floor
        ((1 + fordUniformPrimeWidth) * (M : ℝ))
  have hsumEq := sum_fordPrimeInterval_log_eq_theta_sub hMB
  have hsumUpper := sum_fordPrimeInterval_log_le (M := M) (B := B)
  have hmassSum : 3 * fordUniformPrimeWidth * (M : ℝ) / 4 ≤
      ∑ p ∈ fordPrimeInterval M B, Real.log p := by
    rw [hsumEq, ← hthetaFloor]
    exact hmass
  have hcardSqrt :
      ∑ p ∈ fordPrimeInterval M B, Real.log p ≤
        ((fordPrimeInterval M B).card : ℝ) * Real.sqrt M := by
    exact hsumUpper.trans (mul_le_mul_of_nonneg_left hlogB (by positivity))
  by_contra hkcard
  have hcardNat : (fordPrimeInterval M B).card < k ^ 3 :=
    Nat.lt_of_not_ge hkcard
  have hcardReal : ((fordPrimeInterval M B).card : ℝ) ≤ (k ^ 3 : ℕ) := by
    exact_mod_cast hcardNat.le
  have hpoly : (200 * k ^ 3) ^ 2 ≤ M :=
    (le_max_right _ _).trans hM
  have hsqrtLower : (200 : ℝ) * k ^ 3 ≤ Real.sqrt M := by
    have hpolyR : (((200 * k ^ 3) ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hpoly
    norm_num [Nat.cast_pow, Nat.cast_mul] at hpolyR
    have hsqrtSq : (Real.sqrt (M : ℝ)) ^ 2 = (M : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hleft : (0 : ℝ) ≤ (200 : ℝ) * k ^ 3 := by positivity
    nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hupper :
      ((fordPrimeInterval M B).card : ℝ) * Real.sqrt M ≤
        (k ^ 3 : ℕ) * Real.sqrt M := by
    gcongr
  have hsqrtSq : (Real.sqrt (M : ℝ)) ^ 2 = (M : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hk3 : (0 : ℝ) ≤ (k ^ 3 : ℕ) := by positivity
  have hstrict :
      (k ^ 3 : ℕ) * Real.sqrt M <
        3 * fordUniformPrimeWidth * (M : ℝ) / 4 := by
    have hsqrtPos : 0 < Real.sqrt M := Real.sqrt_pos.2 (by positivity)
    have hkcast : ((k ^ 3 : ℕ) : ℝ) = (k : ℝ) ^ 3 := by norm_num
    have hcoef : ((k ^ 3 : ℕ) : ℝ) < (3 / 400 : ℝ) * Real.sqrt M := by
      rw [hkcast]
      nlinarith
    calc
      ((k ^ 3 : ℕ) : ℝ) * Real.sqrt M <
          ((3 / 400 : ℝ) * Real.sqrt M) * Real.sqrt M :=
        mul_lt_mul_of_pos_right hcoef hsqrtPos
      _ = (3 / 400 : ℝ) *
          (Real.sqrt M * Real.sqrt M) := by ring
      _ = (3 / 400 : ℝ) * (M : ℝ) := by
        rw [show Real.sqrt (M : ℝ) * Real.sqrt M = (M : ℝ) by nlinarith]
      _ = 3 * fordUniformPrimeWidth * (M : ℝ) / 4 := by
        rw [fordUniformPrimeWidth]
        ring
  exact (not_lt_of_ge (hmassSum.trans (hcardSqrt.trans hupper))) hstrict

/-- The first `k^3` primes above `M` lie in the fixed relative interval once
the explicit polynomial scale and one global analytic threshold are met. -/
theorem fordPrimeSet_le_fixedWidth
    {k M p : ℕ} (hM : fordPrimePacketScaleThreshold k ≤ M)
    (hp : p ∈ fordPrimeSet k M) :
    p ≤ fordRelativePrimeBound fordUniformPrimeWidth M :=
  fordPrimeSet_le_of_interval_card
    (fordPrimeInterval_fixedWidth_card_ge hM) hp

#print axioms fordUniformPrimeMassThreshold_spec
#print axioms fordUniformPrimeLogThreshold_spec
#print axioms fordPrimeInterval_fixedWidth_card_ge
#print axioms fordPrimeSet_le_fixedWidth

end

end GafniTao
