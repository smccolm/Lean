import GafniTao.SourceConventions
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Source-faithful exponent language

Gafni--Tao use two different asymptotic conventions.  Exceptional-set
exponents use one fixed power with an eventual constant and no epsilon loss.
Zero-density exponents allow every positive epsilon.  This module keeps those
notions separate.
-/

open Asymptotics Filter Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- A fixed-power eventual estimate.  The function has already absorbed all
parameters on which the constant is permitted to depend. -/
def FixedPowerBound (f : ℝ → ℝ) (xi : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ X in atTop, |f X| ≤ C * X ^ xi

/-- The set of real fixed-power exponents, embedded in the extended reals. -/
def fixedPowerExponentSet (f : ℝ → ℝ) : Set EReal :=
  {a | ∃ xi : ℝ, FixedPowerBound f xi ∧ a = (xi : EReal)}

/-- The least fixed-power exponent.  If every real exponent works, its value
is `-∞`, matching the paper's eventually-empty convention. -/
noncomputable def leastFixedPowerExponent (f : ℝ → ℝ) : EReal :=
  sInf (fixedPowerExponentSet f)

/-- The epsilon-power convention for a real exponent. -/
def EpsilonExponentBound (f : ℝ → ℝ) (a : ℝ) : Prop :=
  EpsilonPowerBound f (fun T => T ^ a)

/-- The least real exponent satisfying the epsilon-power convention. -/
noncomputable def leastEpsilonExponent (f : ℝ → ℝ) : EReal :=
  sInf {a | ∃ r : ℝ, EpsilonExponentBound f r ∧ a = (r : EReal)}

theorem leastFixedPowerExponent_le {f : ℝ → ℝ} {xi : ℝ}
    (hxi : FixedPowerBound f xi) :
    leastFixedPowerExponent f ≤ (xi : EReal) := by
  apply sInf_le
  exact ⟨xi, hxi, rfl⟩

theorem leastEpsilonExponent_le {f : ℝ → ℝ} {a : ℝ}
    (ha : EpsilonExponentBound f a) :
    leastEpsilonExponent f ≤ (a : EReal) := by
  apply sInf_le
  exact ⟨a, ha, rfl⟩

/-- Raising the central exponent preserves an epsilon-power estimate.  The
extra `epsilon` in the source convention is left untouched; only the named
central exponent is enlarged. -/
theorem EpsilonExponentBound.mono_exponent {f : ℝ → ℝ} {a b : ℝ}
    (h : EpsilonExponentBound f a) (hab : a ≤ b) :
    EpsilonExponentBound f b := by
  unfold EpsilonExponentBound at h ⊢
  apply EpsilonPowerBound_mono _ _ _ h
  intro T hT
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) a),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) b)]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) hab

/-- Strict comparison of real powers at infinity. -/
theorem rpow_isLittleO_rpow {a b : ℝ} (hab : a < b) :
    (fun X : ℝ => X ^ a) =o[atTop] (fun X : ℝ => X ^ b) := by
  rw [isLittleO_iff_tendsto']
  · have hpow := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
    apply hpow.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [← Real.rpow_sub hX]
    congr 1
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX hzero
    exact False.elim ((Real.rpow_pos_of_pos hX _).ne' hzero)

/-- An epsilon-exponent estimate is little-oh of every strictly larger real
power.  This is the strict-margin form used to turn Lemma 2.2 into an empty
large-value event. -/
theorem EpsilonExponentBound.isLittleO_rpow {f : ℝ → ℝ} {a b : ℝ}
    (h : EpsilonExponentBound f a) (hab : a < b) :
    (fun X => |f X|) =o[atTop] (fun X : ℝ => X ^ b) := by
  let eps := (b - a) / 2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  have H := h eps heps
  have hEq :
      (fun X : ℝ => X ^ eps * |X ^ a|) =ᶠ[atTop]
        (fun X : ℝ => X ^ (a + eps)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [abs_of_nonneg (Real.rpow_nonneg hX.le _), ← Real.rpow_add hX]
    congr 1
    ring
  have H' : (fun X => |f X|) =O[atTop] (fun X : ℝ => X ^ (a + eps)) :=
    H.trans_eventuallyEq hEq
  exact H'.trans_isLittleO
    (rpow_isLittleO_rpow (by
      dsimp [eps]
      linarith))

/-- Every real exponent strictly above the extended infimum is an admissible
epsilon exponent.  As for fixed powers, this deliberately makes no assertion
that the infimum is attained. -/
theorem epsilonExponentBound_of_leastEpsilonExponent_lt
    {f : ℝ → ℝ} {a : ℝ}
    (ha : leastEpsilonExponent f < (a : EReal)) :
    EpsilonExponentBound f a := by
  obtain ⟨x, hxSet, hxLt⟩ := sInf_lt_iff.mp ha
  rcases hxSet with ⟨b, hb, rfl⟩
  exact hb.mono_exponent (by exact_mod_cast hxLt.le)

theorem leastEpsilonExponent_lt_of_bound {f : ℝ → ℝ} {a b : ℝ}
    (h : EpsilonExponentBound f a) (hab : a < b) :
    leastEpsilonExponent f < (b : EReal) := by
  exact (leastEpsilonExponent_le h).trans_lt (by exact_mod_cast hab)

/-- Pointwise equality preserves the epsilon-power predicate. -/
theorem EpsilonExponentBound.congr {f g : ℝ → ℝ} {a : ℝ}
    (h : EpsilonExponentBound f a) (hfg : ∀ T, f T = g T) :
    EpsilonExponentBound g a := by
  unfold EpsilonExponentBound at h ⊢
  intro ε hε
  simpa only [← hfg] using h ε hε

/-- A finite sum of quantities with one common epsilon exponent has the same
epsilon exponent. -/
theorem EpsilonExponentBound.finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) {a : ℝ}
    (h : ∀ i ∈ s, EpsilonExponentBound (f i) a) :
    EpsilonExponentBound (fun X => ∑ i ∈ s, f i X) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold EpsilonExponentBound RiemannZeta.GuthMaynard.EpsilonPowerBound
      intro eps heps
      apply IsBigO.of_bound 0
      filter_upwards [] with X
      simp
  | @insert i s hi ih =>
      have hiBound := h i (Finset.mem_insert_self i s)
      have hsBound := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert hi] using hiBound.add hsBound

theorem fixedPowerBound_of_eventually_zero {f : ℝ → ℝ}
    (hf : ∀ᶠ X in atTop, f X = 0) (xi : ℝ) :
    FixedPowerBound f xi := by
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards [hf, eventually_ge_atTop (1 : ℝ)] with X hX hXone
  rw [hX, abs_zero]
  positivity

theorem FixedPowerBound.mono_exponent {f : ℝ → ℝ} {xi eta : ℝ}
    (h : FixedPowerBound f xi) (hxi : xi ≤ eta) :
    FixedPowerBound f eta := by
  rcases h with ⟨C, hC, hEventually⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hEventually, eventually_ge_atTop (1 : ℝ)] with X hX hXone
  calc
    |f X| ≤ C * X ^ xi := hX
    _ ≤ C * X ^ eta := by
      gcongr

/-- Fixed-power estimates are stable under addition. -/
theorem FixedPowerBound.add {f g : ℝ → ℝ} {xi : ℝ}
    (hf : FixedPowerBound f xi) (hg : FixedPowerBound g xi) :
    FixedPowerBound (fun X => f X + g X) xi := by
  rcases hf with ⟨C, hC, hf⟩
  rcases hg with ⟨D, hD, hg⟩
  refine ⟨C + D, add_pos hC hD, ?_⟩
  filter_upwards [hf, hg] with X hfX hgX
  calc
    |f X + g X| ≤ |f X| + |g X| := abs_add_le _ _
    _ ≤ C * X ^ xi + D * X ^ xi := add_le_add hfX hgX
    _ = (C + D) * X ^ xi := by ring

/-- A finite family of fixed-power estimates with one exponent has that same
fixed exponent. -/
theorem FixedPowerBound.finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) {xi : ℝ}
    (h : ∀ i ∈ s, FixedPowerBound (f i) xi) :
    FixedPowerBound (fun X => ∑ i ∈ s, f i X) xi := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
      simp only [Finset.sum_empty, abs_zero]
      positivity
  | @insert i s hi ih =>
      have hiBound := h i (Finset.mem_insert_self i s)
      have hsBound := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert hi] using hiBound.add hsBound

/-- Eventual domination transfers a fixed-power bound. -/
theorem FixedPowerBound.mono_eventually {f g : ℝ → ℝ} {xi : ℝ}
    (hg : FixedPowerBound g xi)
    (hfg : ∀ᶠ X in atTop, |f X| ≤ |g X|) :
    FixedPowerBound f xi := by
  rcases hg with ⟨C, hC, hg⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfg, hg] with X hfgX hgX
  exact hfgX.trans hgX

/-- An eventually zero quantity has exponent `-∞`, not zero. -/
theorem leastFixedPowerExponent_eq_bot_of_eventually_zero {f : ℝ → ℝ}
    (hf : ∀ᶠ X in atTop, f X = 0) :
    leastFixedPowerExponent f = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  have hle : leastFixedPowerExponent f ≤ ((y - 1 : ℝ) : EReal) :=
    leastFixedPowerExponent_le (fixedPowerBound_of_eventually_zero hf (y - 1))
  exact hle.trans_lt (by exact_mod_cast sub_one_lt y)

/-- Every real exponent strictly above the extended infimum is an admissible
fixed-power exponent.  This is the usable direction of the infimum interface;
no attainment at the boundary is asserted. -/
theorem fixedPowerBound_of_leastFixedPowerExponent_lt {f : ℝ → ℝ} {xi : ℝ}
    (hxi : leastFixedPowerExponent f < (xi : EReal)) :
    FixedPowerBound f xi := by
  obtain ⟨a, haSet, haLt⟩ := sInf_lt_iff.mp hxi
  rcases haSet with ⟨eta, heta, rfl⟩
  apply heta.mono_exponent
  exact_mod_cast haLt.le

theorem leastFixedPowerExponent_lt_of_bound {f : ℝ → ℝ} {xi eta : ℝ}
    (h : FixedPowerBound f xi) (hxi : xi < eta) :
    leastFixedPowerExponent f < (eta : EReal) := by
  exact (leastFixedPowerExponent_le h).trans_lt (by exact_mod_cast hxi)

/-- An epsilon-power estimate supplies a genuine fixed-power estimate at
every strictly larger exponent.  This is the exact conversion needed at the
end of Gafni--Tao's `o(1)` ledger: the spare exponent is spent once, and no
epsilon loss is inserted into the definition of `mu_delta`. -/
theorem fixedPowerBound_of_epsilonExponentBound_lt
    {f : ℝ → ℝ} {a xi : ℝ}
    (h : EpsilonExponentBound f a) (haxi : a < xi) :
    FixedPowerBound f xi := by
  let eps : ℝ := xi - a
  have heps : 0 < eps := sub_pos.mpr haxi
  have hO := h eps heps
  obtain ⟨C, hC⟩ := hO.bound
  let C' : ℝ := max C 1
  refine ⟨C', by
    dsimp [C']
    exact lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with X hCX hX
  have hpow : X ^ eps * |X ^ a| = X ^ xi := by
    rw [abs_of_nonneg (Real.rpow_nonneg hX.le _), ← Real.rpow_add hX]
    congr 1
    dsimp [eps]
    ring
  have hnonneg : 0 ≤ X ^ xi := Real.rpow_nonneg hX.le _
  have hnormLeft : ‖|f X|‖ = |f X| := by simp
  have hnormRight : ‖X ^ eps * |X ^ a|‖ = X ^ xi := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hpow]
  rw [hnormLeft, hnormRight] at hCX
  exact hCX.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) hnonneg)

theorem leastFixedPowerExponent_le_of_epsilonExponentBound_lt
    {f : ℝ → ℝ} {a xi : ℝ}
    (h : EpsilonExponentBound f a) (haxi : a < xi) :
    leastFixedPowerExponent f ≤ (xi : EReal) :=
  leastFixedPowerExponent_le
    (fixedPowerBound_of_epsilonExponentBound_lt h haxi)

/-- Pointwise equality preserves the fixed-power predicate. -/
theorem FixedPowerBound.congr {f g : ℝ → ℝ} {xi : ℝ}
    (h : FixedPowerBound f xi) (hfg : ∀ X, f X = g X) :
    FixedPowerBound g xi := by
  rcases h with ⟨C, hC, hEventually⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hEventually] with X hX
  simpa only [← hfg X] using hX

end GafniTao
