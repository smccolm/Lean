import GafniTao.HeathBrownGlobalSourceAlternative
import RiemannZeta.GuthMaynard.NativeZeroDensity

/-!
# The bounded-shell branch

If one coordinate of the logarithmic shell cover remains below the fixed
detector threshold, the other two freely summed coordinates are controlled
by an ordinary zero-density estimate.  This file performs the ceiling,
dilation, square, logarithm, and epsilon bookkeeping explicitly.
-/

open Asymptotics Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Epsilon-exponent bounds are stable under a fixed positive dilation of
the argument. -/
theorem EpsilonExponentBound.const_mul_arg
    {f : Real → Real} {a c : Real} (h : EpsilonExponentBound f a)
    (hc : 0 < c) :
    EpsilonExponentBound (fun T => f (c * T)) a := by
  unfold EpsilonExponentBound EpsilonPowerBound at h ⊢
  intro eps heps
  have H := (h eps heps).comp_tendsto (tendsto_id.const_mul_atTop hc)
  apply H.trans
  apply IsBigO.of_bound (c ^ eps * |c ^ a|)
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  have hc0 : 0 ≤ c := hc.le
  have hT0 : 0 ≤ T := hT.le
  change ‖(c * T) ^ eps * |(c * T) ^ a|‖ ≤
    c ^ eps * |c ^ a| * ‖T ^ eps * |T ^ a|‖
  rw [Real.mul_rpow hc0 hT0, Real.mul_rpow hc0 hT0, abs_mul]
  have hceps : 0 ≤ c ^ eps := Real.rpow_nonneg hc0 _
  have hTeps : 0 ≤ T ^ eps := Real.rpow_nonneg hT0 _
  simp only [Real.norm_eq_abs, abs_mul, abs_abs,
    abs_of_nonneg hceps, abs_of_nonneg hTeps]
  ring_nf
  exact le_rfl

/-- Replace the literal common cover height `2 * ceil T` by the fixed
dilation `4T`. -/
theorem zeroDensityEnvelope_at_two_ceil
    {sigma a : Real} (hDensity : ZeroDensityEnvelope sigma a) :
    EpsilonExponentBound
      (fun T => (zeroCount sigma (2 * (Nat.ceil T : Real)) : Real))
      (a * (1 - sigma)) := by
  have hFour : EpsilonExponentBound
      (fun T => (zeroCount sigma (4 * T) : Real))
      (a * (1 - sigma)) := by
    exact (show EpsilonExponentBound
      (fun T => (zeroCount sigma T : Real)) (a * (1 - sigma)) from
        hDensity).const_mul_arg (by norm_num)
  unfold EpsilonExponentBound at hFour ⊢
  intro eps heps
  have hDom :
      (fun T : Real =>
        |(zeroCount sigma (2 * (Nat.ceil T : Real)) : Real)|) =O[atTop]
      (fun T : Real => |(zeroCount sigma (4 * T) : Real)|) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : Real)] with T hT
    have hCeil : (Nat.ceil T : Real) ≤ 2 * T := by
      have hRaw := Nat.ceil_lt_add_one (show 0 ≤ T by linarith)
      linarith
    have hCount := zeroCount_mono_height_sigma
      (sigma := sigma) (T := 2 * (Nat.ceil T : Real))
      (R := 4 * T) (by linarith)
    rw [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast hCount
  exact hDom.trans (hFour eps heps)

/-- Literal majorant produced when one selected shell is below the source
threshold. -/
noncomputable def heathBrownBoundedShellMajorant
    (sigma R0 T : Real) : Real :=
  (zeroCount sigma R0 : Real) *
    (zeroCount sigma (2 * (Nat.ceil T : Real)) : Real) ^ 2 *
    (3 * globalLocalZeroLogConstant *
      Real.log (2 * (Nat.ceil T : Real)))

/-- A bounded selected shell costs twice the ordinary zero-density exponent;
all fixed, logarithmic, and ceiling losses are absorbed in the requested
epsilon. -/
theorem heathBrownBoundedShellMajorant_envelope
    {sigma a R0 : Real} (hDensity : ZeroDensityEnvelope sigma a) :
    EpsilonExponentBound
      (heathBrownBoundedShellMajorant sigma R0)
      (2 * (a * (1 - sigma))) := by
  have hCeil := zeroDensityEnvelope_at_two_ceil hDensity
  unfold EpsilonExponentBound at hCeil ⊢
  intro eps heps
  have hepsHalf : 0 < eps / 2 := by positivity
  have hepsQuarter : 0 < eps / 4 := by positivity
  have hLog :
      (fun T : Real => |Real.log (2 * (Nat.ceil T : Real))|) =O[atTop]
        (fun T : Real => T ^ (eps / 2)) := by
    have hBase :
        (fun X : Real => |Real.log X|) =O[atTop]
          (fun X : Real => X ^ (eps / 4)) := by
      simpa only [Real.norm_eq_abs] using
        (isLittleO_log_rpow_atTop hepsQuarter).isBigO.norm_left
    have hComposed := hBase.comp_tendsto
      (show Tendsto (fun T : Real => 2 * (Nat.ceil T : Real)) atTop atTop by
        apply tendsto_atTop_mono'
        · filter_upwards [eventually_ge_atTop (0 : Real)] with T hT
          exact mul_le_mul_of_nonneg_left (Nat.le_ceil T) (by norm_num)
        · exact tendsto_id.const_mul_atTop (by norm_num))
    apply hComposed.trans
    apply IsBigO.of_bound (4 ^ (eps / 4))
    filter_upwards [eventually_ge_atTop (1 : Real)] with T hT
    have hCeil : (Nat.ceil T : Real) ≤ 2 * T := by
      have hRaw := Nat.ceil_lt_add_one (show 0 ≤ T by linarith)
      linarith
    have hArg0 : 0 ≤ 2 * (Nat.ceil T : Real) := by positivity
    have hT0 : 0 ≤ T := by linarith
    have hArg : 2 * (Nat.ceil T : Real) ≤ 4 * T := by linarith
    change ‖(2 * (Nat.ceil T : Real)) ^ (eps / 4)‖ ≤
      4 ^ (eps / 4) * ‖T ^ (eps / 2)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hArg0 _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT0 _)]
    calc
      (2 * (Nat.ceil T : Real)) ^ (eps / 4) ≤
          (4 * T) ^ (eps / 4) :=
        Real.rpow_le_rpow hArg0 hArg hepsQuarter.le
      _ = 4 ^ (eps / 4) * T ^ (eps / 4) := by
        rw [Real.mul_rpow (by norm_num) hT0]
      _ ≤ 4 ^ (eps / 4) * T ^ (eps / 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        · positivity
  have hCountSq := (hCeil (eps / 4) hepsQuarter).pow 2
  have hProduct := hLog.mul hCountSq
  have hProductTarget :
      (fun T : Real =>
        |Real.log (2 * (Nat.ceil T : Real))| *
          |(zeroCount sigma (2 * (Nat.ceil T : Real)) : Real)| ^ 2) =O[atTop]
      (fun T : Real =>
        T ^ eps * |T ^ (2 * (a * (1 - sigma)))|) := by
    apply hProduct.trans
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
    have hpHalf : 0 ≤ T ^ (eps / 2) := Real.rpow_nonneg hT.le _
    have hpQuarter : 0 ≤ T ^ (eps / 4) := Real.rpow_nonneg hT.le _
    have hpD : 0 ≤ T ^ (a * (1 - sigma)) := Real.rpow_nonneg hT.le _
    have hpEps : 0 ≤ T ^ eps := Real.rpow_nonneg hT.le _
    have hpTwoD : 0 ≤ T ^ (2 * (a * (1 - sigma))) :=
      Real.rpow_nonneg hT.le _
    simp only [Real.norm_eq_abs, one_mul, abs_mul, abs_pow,
      abs_of_nonneg hpHalf, abs_of_nonneg hpQuarter, abs_of_nonneg hpD,
      abs_of_nonneg hpEps, abs_of_nonneg hpTwoD]
    change T ^ (eps / 2) *
        (T ^ (eps / 4) * T ^ (a * (1 - sigma))) ^ 2 ≤
      T ^ eps * T ^ (2 * (a * (1 - sigma)))
    rw [← Real.rpow_add hT, ← Real.rpow_mul_natCast hT.le,
      ← Real.rpow_add hT, ← Real.rpow_add hT]
    ring_nf
    exact le_rfl
  apply (hProductTarget.const_mul_left
    ((zeroCount sigma R0 : Real) *
      (3 * globalLocalZeroLogConstant))).congr'
  · filter_upwards [eventually_ge_atTop (1 : Real)] with T hT
    have hLogNonneg : 0 ≤ Real.log (2 * (Nat.ceil T : Real)) := by
      apply Real.log_nonneg
      have hCeil : (1 : Real) ≤ (Nat.ceil T : Real) :=
        hT.trans (Nat.le_ceil T)
      linarith
    have hCountNonneg :
        0 ≤ (zeroCount sigma (2 * (Nat.ceil T : Real)) : Real) := by
      positivity
    have hMajorantNonneg :
        0 ≤ heathBrownBoundedShellMajorant sigma R0 T := by
      unfold heathBrownBoundedShellMajorant
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (mul_nonneg
          (mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le)
          hLogNonneg)
    rw [abs_of_nonneg hMajorantNonneg]
    unfold heathBrownBoundedShellMajorant
    rw [abs_of_nonneg hLogNonneg, abs_of_nonneg hCountNonneg]
    ring
  · exact Filter.Eventually.of_forall fun _ => rfl

#print axioms EpsilonExponentBound.const_mul_arg
#print axioms zeroDensityEnvelope_at_two_ceil
#print axioms heathBrownBoundedShellMajorant_envelope

end

end GafniTao
