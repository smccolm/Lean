import GafniTao.Pintz2023PoweredScaleSharp

/-!
# Pintz (2023), equation (4.24): shell exponent arithmetic

This module records the exact perturbed exponent before the auxiliary
epsilon is sent to zero.  The maximum retains the separate square (`k`) and
higher-power (`ell`) branches.
-/

namespace GafniTao

noncomputable section

/-- Exponent of the powered block after the coefficient energy and the
diagonal Gram term have been combined. -/
noncomputable def pintz2023ShellBlockExponent
    (eta epsilon : ℝ) (k : ℕ) : ℝ :=
  2 * eta + 2 * (epsilon / (100 * (k : ℝ)))

/-- Upper logarithmic scale of the squared block, before the bounded dyadic
factor is absorbed. -/
noncomputable def pintz2023SquareBlockScale
    (eta epsilon delta : ℝ) (k ell : ℕ) : ℝ :=
  2 * (epsilon / (10 * (ell : ℝ)) +
    pintz2023CriticalScaleExponent k eta epsilon + delta)

/-- Literal exponent delivered by the two branches of equation (4.24), with
all auxiliary perturbations still present. -/
noncomputable def pintz2023ShellCoreExponent
    (eta epsilon delta : ℝ) (k ell : ℕ) : ℝ :=
  max
    (pintz2023ShellBlockExponent eta epsilon k *
      pintz2023SquareBlockScale eta epsilon delta k ell)
    (pintz2023ShellBlockExponent eta epsilon k *
      pintz2023EllPowerWindowUpper eta epsilon ell)

theorem pintz2023ShellBlockExponent_pos
    {eta epsilon : ℝ} {k : ℕ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (hk : 0 < k) :
    0 < pintz2023ShellBlockExponent eta epsilon k := by
  unfold pintz2023ShellBlockExponent
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- The negative local-frequency term in equation (4.19) can be discarded
when forming an upper exponent. -/
theorem pintz2023_equation419_exponent_le_blockExponent
    {eta epsilon lambda : ℝ} {k : ℕ}
    (hlambda : 0 < lambda) :
    2 * eta - 2 / lambda + 2 * (epsilon / (100 * (k : ℝ))) ≤
      pintz2023ShellBlockExponent eta epsilon k := by
  unfold pintz2023ShellBlockExponent
  have : 0 ≤ 2 / lambda := by positivity
  linarith

/-- A powered block in either source scale contributes at most the shell
core exponent, plus the explicit dyadic reserve. -/
theorem pintz2023_powered_block_rpow_le_shellCore
    {eta epsilon delta reserve T : ℝ} {k ell N : ℕ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (hk : 0 < k)
    (hT : 1 ≤ T) (hN : 0 < N)
    (hScale :
      ((N : ℝ) < T ^
          (pintz2023SquareBlockScale eta epsilon delta k ell + reserve)) ∨
      ((N : ℝ) < T ^
          (pintz2023EllPowerWindowUpper eta epsilon ell + reserve))) :
    (N : ℝ) ^ pintz2023ShellBlockExponent eta epsilon k ≤
      T ^ (pintz2023ShellCoreExponent eta epsilon delta k ell +
        pintz2023ShellBlockExponent eta epsilon k * reserve) := by
  have hQ := pintz2023ShellBlockExponent_pos heta hepsilon hk
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hNNonneg : (0 : ℝ) ≤ N := by positivity
  rcases hScale with hSquare | hEll
  · have hPow := Real.rpow_le_rpow hNNonneg hSquare.le hQ.le
    have hRewrite :
        (T ^ (pintz2023SquareBlockScale eta epsilon delta k ell + reserve)) ^
            pintz2023ShellBlockExponent eta epsilon k =
          T ^ (pintz2023ShellBlockExponent eta epsilon k *
            pintz2023SquareBlockScale eta epsilon delta k ell +
            pintz2023ShellBlockExponent eta epsilon k * reserve) := by
      rw [← Real.rpow_mul hTPos.le]
      congr 1
      ring
    rw [hRewrite] at hPow
    apply hPow.trans
    apply Real.rpow_le_rpow_of_exponent_le hT
    unfold pintz2023ShellCoreExponent
    linarith [le_max_left
      (pintz2023ShellBlockExponent eta epsilon k *
        pintz2023SquareBlockScale eta epsilon delta k ell)
      (pintz2023ShellBlockExponent eta epsilon k *
        pintz2023EllPowerWindowUpper eta epsilon ell)]
  · have hPow := Real.rpow_le_rpow hNNonneg hEll.le hQ.le
    have hRewrite :
        (T ^ (pintz2023EllPowerWindowUpper eta epsilon ell + reserve)) ^
            pintz2023ShellBlockExponent eta epsilon k =
          T ^ (pintz2023ShellBlockExponent eta epsilon k *
            pintz2023EllPowerWindowUpper eta epsilon ell +
            pintz2023ShellBlockExponent eta epsilon k * reserve) := by
      rw [← Real.rpow_mul hTPos.le]
      congr 1
      ring
    rw [hRewrite] at hPow
    apply hPow.trans
    apply Real.rpow_le_rpow_of_exponent_le hT
    unfold pintz2023ShellCoreExponent
    linarith [le_max_right
      (pintz2023ShellBlockExponent eta epsilon k *
        pintz2023SquareBlockScale eta epsilon delta k ell)
      (pintz2023ShellBlockExponent eta epsilon k *
        pintz2023EllPowerWindowUpper eta epsilon ell)]

#print axioms pintz2023_equation419_exponent_le_blockExponent
#print axioms pintz2023_powered_block_rpow_le_shellCore

end

end GafniTao
