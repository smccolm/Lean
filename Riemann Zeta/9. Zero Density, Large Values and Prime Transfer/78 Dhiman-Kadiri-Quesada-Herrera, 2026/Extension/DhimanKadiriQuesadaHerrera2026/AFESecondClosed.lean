import DhimanKadiriQuesadaHerrera2026.AFESecondLimits

/-! # Closed-strip and reflected bounds for the actual AFE

Continuity of the assembled zeta remainder includes σ=0 and σ=1 without assigning
convergent values to the separate endpoint improper integrals. Conjugation and the
functional equation transport the proved bound to both height signs and exchanged
cutoffs. Source-constant simplification is a separate obligation.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Filter
open scoped Topology

/-- The literal sharp Dirichlet polynomial is continuous in its complex exponent. -/
theorem continuous_sharpZetaSum (x : ℝ) : Continuous (fun s : ℂ => sharpZetaSum s x) := by
  unfold sharpZetaSum zetaTerm
  apply continuous_finsetSum
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  exact continuous_id.neg.const_cpow (Or.inl (by exact_mod_cast hn0))

/-- The literal chi product is continuous at every nonreal point. -/
theorem continuousAt_chi {s : ℂ} (hs : s.im ≠ 0) : ContinuousAt chi s := by
  have hΓ : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n hn
    have hi := congrArg Complex.im hn
    simp only [Complex.sub_im, Complex.one_im, Complex.neg_im, Complex.natCast_im] at hi
    exact hs (by linarith)
  unfold chi
  exact (((continuousAt_id.const_cpow (Or.inl (by norm_num))).mul
    ((continuousAt_id.sub_const 1).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))).mul
    ((Complex.continuousAt_Gamma (1 - s) hΓ).comp (continuousAt_const.sub continuousAt_id))).mul
    (by fun_prop)

/-- The actual AFE remainder is continuous at every nonreal exponent. -/
theorem continuousAt_afeRemainder {s : ℂ} (hs : s.im ≠ 0) (x y : ℝ) :
    ContinuousAt (fun z : ℂ => afeRemainder z x y) s := by
  have hs1 : s ≠ 1 := by intro he; apply hs; rw [he]; rfl
  unfold afeRemainder
  exact ((differentiableAt_riemannZeta hs1).continuousAt.sub
    (continuous_sharpZetaSum x).continuousAt).sub ((continuousAt_chi hs).mul
      ((continuous_sharpZetaSum y).continuousAt.comp (continuousAt_const.sub continuousAt_id)))

/-- The left Poisson error after substituting the exact power-weight derivatives. -/
noncomputable def afeSecondLeftExplicit (σ c a : ℝ) : ℝ :=
  let y : ℝ := c / a
  let M : ℕ := ⌊y⌋₊
  a ^ (-σ) / (2 * Real.pi) * (Real.log 2 + 1 / y) +
    ((σ + 2 * Real.pi * c) * a ^ (-σ - 1)) / (4 * Real.pi ^ 2) * ((Real.pi / 2 + Real.log 2) / y) +
    ((σ + 1) * (σ + 2 * Real.pi * c) * a ^ (-σ - 2)) / (4 * Real.pi ^ 3) *
      (minusSquareBound M y + plusSquareBound y) +
    (((σ + 2 * Real.pi * c) * a ^ (-σ - 1)) * (c / a ^ 2) / (4 * Real.pi ^ 3)) *
      (minusCubeBound M y + plusCubeBound y)

/-- The explicit left error is exactly the previously proved Poisson error for nonnegative σ. -/
theorem afeSecondLeftError_eq {σ c a : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c) (ha : 0 < a) :
    afeSecondLeftError σ c a = afeSecondLeftExplicit σ c a := by
  dsimp only [afeSecondLeftError, afeSecondLeftExplicit]
  rw [secondH_afe hσ hc ha, secondH1_afe hσ hc ha]
  rfl

/-- The substituted left error is continuous in σ, including both closed-strip endpoints. -/
theorem continuous_afeSecondLeftExplicit {c a : ℝ} (ha : 0 < a) :
    Continuous (fun σ : ℝ => afeSecondLeftExplicit σ c a) := by
  have hp : Continuous (fun σ : ℝ => a ^ (-σ)) :=
    (Real.continuous_const_rpow ha.ne').comp continuous_neg
  have hp1 : Continuous (fun σ : ℝ => a ^ (-σ - 1)) :=
    (Real.continuous_const_rpow ha.ne').comp (continuous_neg.sub continuous_const)
  have hp2 : Continuous (fun σ : ℝ => a ^ (-σ - 2)) :=
    (Real.continuous_const_rpow ha.ne').comp (continuous_neg.sub continuous_const)
  unfold afeSecondLeftExplicit
  exact (((hp.div_const _).mul_const _).add
    ((((continuous_id.add continuous_const).mul hp1).div_const _).mul_const _)).add
    (((((continuous_id.add continuous_const).mul (continuous_id.add continuous_const)).mul hp2).div_const _).mul_const _) |>.add
    (((((continuous_id.add continuous_const).mul hp1).mul_const _).div_const _).mul_const _)

/-- The complete explicit direct AFE error before the source's numerical simplification. -/
noncomputable def afeSecondError (σ t x y t₀ : ℝ) : ℝ :=
  afeSecondLeftExplicit σ (t / (2 * Real.pi)) x + (x / t) * x ^ (-σ) +
    ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
      (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) * (y ^ σ * Real.log y + 1) +
    x ^ (-σ) * (Real.log y / Real.pi +
      (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
        3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2))

/-- The explicit direct error is continuous across the whole real σ-axis at nonzero height. -/
theorem continuous_afeSecondError {t x y : ℝ} (ht : t ≠ 0) (hx : 0 < x) (hy : 0 < y) (t₀ : ℝ) :
    Continuous (fun σ : ℝ => afeSecondError σ t x y t₀) := by
  have hc : Continuous (fun σ : ℝ => chi ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro σ
    exact (continuousAt_chi (by simpa using ht)).comp (by fun_prop)
  have hp : Continuous (fun σ : ℝ => x ^ (-σ)) :=
    (Real.continuous_const_rpow hx.ne').comp continuous_neg
  have hy' := Real.continuous_const_rpow hy.ne'
  exact ((((continuous_afeSecondLeftExplicit hx).add (hp.const_mul _)).add
    ((hc.norm.mul_const _).mul ((hy'.mul_const _).add continuous_const))).add (hp.mul_const _))


/-- The actual two-polynomial estimate extends to both σ endpoints by continuity of the assembled remainder. -/
theorem afe_closed_strip_bound {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = t)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤ afeSecondError σ t x y t₀ := by
  have htpos := ht₀.trans_le ht
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hc : Continuous (fun v : ℝ => ‖afeRemainder ((v : ℂ) + (t : ℂ) * Complex.I) x y‖) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact ((continuousAt_afeRemainder (by simpa using htpos.ne') x y).comp (by fun_prop)).norm
  have hb : ∀ v ∈ Set.Ioo (0 : ℝ) 1,
      ‖afeRemainder ((v : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤ afeSecondError v t x y t₀ := by
    intro v hv
    have hh := afe_strict_strip_bound hv hx hy hxhalf hyhalf hscale ht₀ ht
    rw [afeSecondLeftError_eq hv.1.le (div_nonneg htpos.le (by positivity)) hxpos] at hh
    exact hh
  apply le_on_closure hb hc.continuousOn (continuous_afeSecondError htpos.ne' hxpos hypos t₀).continuousOn
  simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hσ

/-- The closed-strip estimate at either height sign uses the positive magnitude throughout the error. -/
theorem afe_closed_strip_abs_bound {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤ afeSecondError σ |t| x y t₀ := by
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0] at hscale ht ⊢
    exact afe_closed_strip_bound hσ hx hy hxhalf hyhalf hscale ht₀ ht
  · have htneg : t < 0 := lt_of_not_ge ht0
    rw [abs_of_neg htneg] at hscale ht ⊢
    have he : (σ : ℂ) + (t : ℂ) * Complex.I = (σ : ℂ) - ((-t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, norm_afeRemainder_neg_height (neg_ne_zero.mpr htneg.ne)]
    exact afe_closed_strip_bound hσ hx hy hxhalf hyhalf hscale ht₀ ht

/-- Reflection applies the actual direct estimate at the dual exponent and exchanged cutoffs. -/
theorem afe_closed_strip_reflected_bound {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * afeSecondError (1 - σ) |t| y x t₀ := by
  have htne : t ≠ 0 := abs_pos.mp (ht₀.trans_le ht)
  have hs : 1 - σ ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hσ.1, hσ.2]
  have ht' : t₀ ≤ |-t| := by simpa only [abs_neg] using ht
  have hscale' : 2 * Real.pi * y * x = |-t| := by rw [abs_neg, ← hscale]; ring
  have hb := afe_closed_strip_abs_bound hs hy hx hyhalf hxhalf hscale' ht₀ ht'
  rw [abs_neg] at hb
  have he : 1 - ((σ : ℂ) + (t : ℂ) * Complex.I) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [norm_afeRemainder_reflection (by simpa using htne), he]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-- The actual remainder satisfies both explicit branches simultaneously, including both σ endpoints and height signs. -/
theorem afe_closed_strip_min_bound {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      min (afeSecondError σ |t| x y t₀)
        (‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * afeSecondError (1 - σ) |t| y x t₀) :=
  le_min (afe_closed_strip_abs_bound hσ hx hy hxhalf hyhalf hscale ht₀ ht)
    (afe_closed_strip_reflected_bound hσ hx hy hxhalf hyhalf hscale ht₀ ht)

end DhimanKadiriQuesadaHerrera2026
