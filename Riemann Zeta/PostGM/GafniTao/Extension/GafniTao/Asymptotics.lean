import GafniTao.SourceConventions
import Mathlib.Data.EReal.Basic

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

/-- Pointwise equality preserves the fixed-power predicate. -/
theorem FixedPowerBound.congr {f g : ℝ → ℝ} {xi : ℝ}
    (h : FixedPowerBound f xi) (hfg : ∀ X, f X = g X) :
    FixedPowerBound g xi := by
  rcases h with ⟨C, hC, hEventually⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hEventually] with X hX
  simpa only [← hfg X] using hX

end GafniTao
