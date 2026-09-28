import TaoTrudgianYang2025.SquareProductCount
noncomputable section
open Set Expdb Filter
open scoped Topology ContDiff BigOperators NNReal FourierTransform
namespace TaoTrudgianYang2025.CubicJointCount

/-- The exponent-pair refined spacing estimate gives the exact two-piece
analytic beta bound; every physical condition comes from the model sequence. -/
theorem isExponentSumBound_refined_bourgain
    {α : ℝ≥0} (hlo : 2/5<(α:ℝ)) (hhi : (α:ℝ)<3/7) :
    IsExponentSumBound α (max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164)) := by
  intro P T F a b _hP hT hTunbounded hPT hF hab
  let β := max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164)
  apply (isPowerBounded_iff_forall_pos (exponentialSum F T P a b) T β hT hTunbounded).mpr
  intro ε hε
  let η := min ((1:ℝ)/100) ε
  have hη : 0<η := lt_min (by norm_num) hε
  have hηε : η≤ε := min_le_right _ _
  have hηsmall : (13/84:ℝ)+η<1 := by
    have hh : η≤(1:ℝ)/100 := min_le_left _ _
    linarith only [hh]
  obtain ⟨hphase,σ,hσ,herror⟩ := hF
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,_hQ,C₀,hC₀,hsource⟩ :=
    exists_model_refined_global_bound hσ exponentPair_bourgain hη hηsmall
  have happrox := (IsModelPhaseFunctionWith.mk hphase herror).eventually_isApproximate Q hδ
  have hparameters := eventually_refined_bourgain_parameters hlo hhi hσ hκ₀ hT hTunbounded hPT
  have hcost := eventually_refined_bourgain_cost hlo hhi hσ hη hT hTunbounded hPT
  let C := max 1 (3*C₀)
  have hC : 1≤C := le_max_left _ _
  have hC₀C : 3*C₀≤C := le_max_right _ _
  have hCpow : C≤C^12 := by
    calc
      C=C*1 := (mul_one C).symm
      _≤C*C^11 := mul_le_mul_of_nonneg_left (one_le_pow₀ hC) (zero_le_one.trans hC)
      _=C^12 := by ring
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [happrox,hparameters,hcost] with i hFi hpi hci
  obtain ⟨hPi,hwi,hwhalf,hUsmall,hcurve,hPU,hLsmall,hliftSmall,hlift,hκ⟩ := hpi
  have hTi : 0<T i := zero_lt_one.trans_le (hT i)
  have hs := hsource (F i) (T i) (P i) (a i) (b i) ((T i)^(-(3+23*(α:ℝ))/194))
    hFi hTi hPi (hab i).1 (hab i).2 hwi hwhalf
    hUsmall hcurve hPU hLsmall hliftSmall hlift hκ
  have hmajor := mul_le_mul_of_nonneg_left hci hC₀.le
  have hbound : ‖exponentialSumAt (F i) (T i) (P i) (a i) (b i)‖^12≤
      (3*C₀)*(T i)^(12*β+5*η) := by
    apply hs.trans
    simpa only [mul_assoc,mul_left_comm C₀ 3] using hmajor
  have hexp : 12*β+5*η≤(β+ε)*12 := by linarith only [hηε,hε]
  have hp : ‖exponentialSumAt (F i) (T i) (P i) (a i) (b i)‖^12≤
      (C*(T i)^(β+ε))^12 := by
    calc
      _≤(3*C₀)*(T i)^(12*β+5*η) := hbound
      _≤C^12*(T i)^((β+ε)*12) :=
        mul_le_mul (hC₀C.trans hCpow) (Real.rpow_le_rpow_of_exponent_le (hT i) hexp)
          (Real.rpow_nonneg hTi.le _) (by positivity)
      _=_ := by rw [mul_pow,←Real.rpow_mul_natCast hTi.le]; norm_num
  have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
    (by positivity : 0≤C*(T i)^(β+ε)) (by norm_num : (12:ℕ)≠0)).mp hp
  simpa only [exponentialSum_apply,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTi.le _)] using hh

/-- Public beta consumer of the complete refined original-source proof. -/
theorem exponentSumGrowthExponent_le_refined_bourgain
    {α : ℝ≥0} (hlo : 2/5<(α:ℝ)) (hhi : (α:ℝ)<3/7) :
    exponentSumGrowthExponent α ≤ max (1/12+2*(α:ℝ)/3) (241/1164+425*(α:ℝ)/1164) :=
  exponentSumGrowthExponent_le_iff.mpr (isExponentSumBound_refined_bourgain hlo hhi)

end TaoTrudgianYang2025.CubicJointCount
