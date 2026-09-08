import GafniTao.FordCotangentCorrection

/-!
# The central pole in Ford's translated zero detector

Ford centers the cotangent detector at a physical point `z₀`.  The residue
theorem therefore needs the principal part of `fordCotKernel eta (z-z₀)` at
`z₀`, rather than only the unshifted residue at zero.  This file proves that
translation from the removable-cotangent estimate and then evaluates an
arbitrary analytic multiplier at the center.
-/

open Complex Filter Set Topology Asymptotics

namespace GafniTao

noncomputable section

/-- The translated Ford kernel has the literal principal part
`1 / (z-z₀)` at its detector center. -/
theorem fordCotKernel_translate_sub_principal_isBigO_one
    {eta : ℝ} (heta : 0 < eta) (z₀ : ℂ) :
    ((fun z : ℂ => fordCotKernel eta (z - z₀)) -
        fun z => 1 / (z - z₀))
      =O[𝓝[≠] z₀] (1 : ℂ → ℂ) := by
  have hshift : ContinuousAt (fun z : ℂ => z - z₀) z₀ := by fun_prop
  have hcont : ContinuousAt
      (fun z : ℂ => fordCotKernel eta (z - z₀) - 1 / (z - z₀)) z₀ :=
    (continuousAt_fordCotKernel_sub_inv_zero heta).comp_of_eq hshift
      (by simp)
  have ht : Tendsto
      (fun z : ℂ => fordCotKernel eta (z - z₀) - 1 / (z - z₀))
      (𝓝[≠] z₀)
      (𝓝 (fordCotKernel eta (z₀ - z₀) - 1 / (z₀ - z₀))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hO :
      (fun z : ℂ => fordCotKernel eta (z - z₀) - 1 / (z - z₀))
        =O[𝓝[≠] z₀] (1 : ℂ → ℂ) := ht.isBigO_one ℂ
  simpa only [Pi.sub_apply] using hO

/-- Multiplying the translated detector kernel by an analytic factor
evaluates that factor at the detector center. -/
theorem fordCotKernel_translate_mul_sub_principal_isBigO_one
    {eta : ℝ} (heta : 0 < eta) {z₀ : ℂ} {L : ℂ → ℂ}
    (hL : DifferentiableAt ℂ L z₀) :
    ((fun z => fordCotKernel eta (z - z₀) * L z) -
        fun z => L z₀ / (z - z₀))
      =O[𝓝[≠] z₀] (1 : ℂ → ℂ) := by
  have hkernel := fordCotKernel_translate_sub_principal_isBigO_one heta z₀
  have hmul := mul_sub_principal_isBigO_one
    (L := fun z : ℂ => fordCotKernel eta (z - z₀))
    (g := L) (p := z₀) (n := 1) hkernel hL
  simpa only [one_mul, mul_one, mul_comm, div_eq_mul_inv] using hmul

/-- Residue form of the translated central-pole calculation. -/
theorem residue_fordCotKernel_translate_mul_eq
    {eta : ℝ} (heta : 0 < eta) {z₀ : ℂ} {L : ℂ → ℂ}
    (hL : DifferentiableAt ℂ L z₀) :
    residue (fun z => fordCotKernel eta (z - z₀) * L z) z₀ = L z₀ := by
  exact residue_eq_of_sub_principal_isBigO_one
    (fordCotKernel_translate_mul_sub_principal_isBigO_one heta hL)

end

end GafniTao
