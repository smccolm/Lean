import RiemannZeta.GuthMaynard.HughesYoungMainTerms

open Complex Filter Set
open scoped Topology

noncomputable section

theorem test_affine_residue {a b p : ℂ} (ha : a ≠ 0)
    (hp : a * p + b = 1) :
    residue (fun z : ℂ => riemannZeta (a * z + b)) p = a⁻¹ := by
  apply residue_eq_of_tendsto
  have hcontinuous : Tendsto (fun z : ℂ => a * z + b)
      (nhdsWithin p {p}ᶜ) (nhds 1) := by
    have h : Tendsto (fun z : ℂ => a * z + b) (nhds p) (nhds (a * p + b)) :=
      (tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds
    rw [hp] at h
    exact h.mono_left inf_le_left
  have havoid : ∀ᶠ z : ℂ in nhdsWithin p {p}ᶜ, a * z + b ∈ ({1} : Set ℂ)ᶜ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    change a * z + b ≠ 1
    intro hz1
    have hzp : z = p := by
      apply (mul_left_cancel₀ ha)
      calc
        a * z = (a * z + b) - b := by ring
        _ = 1 - b := by rw [hz1]
        _ = (a * p + b) - b := by rw [hp]
        _ = a * p := by ring
    exact hz hzp
  have hmap : Tendsto (fun z : ℂ => a * z + b)
      (nhdsWithin p {p}ᶜ) (nhdsWithin 1 {1}ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcontinuous, havoid⟩
  have hzeta := riemannZeta_residue_one.comp hmap
  have hscaled : Tendsto
      (fun z : ℂ => a⁻¹ * ((a * z + b - 1) * riemannZeta (a * z + b)))
      (nhdsWithin p {p}ᶜ) (nhds (a⁻¹ * 1)) := by
    simpa only [Function.comp_apply] using tendsto_const_nhds.mul hzeta
  have hfun : (fun z : ℂ =>
      a⁻¹ * ((a * z + b - 1) * riemannZeta (a * z + b))) =
      (fun z : ℂ => (z - p) * riemannZeta (a * z + b)) := by
    funext z
    have haz : a * z + b - 1 = a * (z - p) := by rw [← hp]; ring
    rw [haz]
    field_simp [ha]
  rw [hfun] at hscaled
  simpa only [mul_one] using hscaled

open RiemannZeta.GuthMaynard

example (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta s0 : ℂ)
    (hden :
      ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
        (1 - (p : ℂ) ^ (-2 - alpha - beta - gamma - delta - 2 * s0)) ≠ 0) :
    ContinuousAt (fun s : ℂ =>
      hughesYoungBPrimeFactor e p alpha beta gamma delta s) s0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpow1 : ContinuousAt (fun s : ℂ => (p : ℂ) ^ (-s)) s0 :=
    (continuousAt_const_cpow hpC).comp (by fun_prop)
  have hpow2 : ContinuousAt (fun s : ℂ => (p : ℂ) ^ (-2 * s)) s0 :=
    (continuousAt_const_cpow hpC).comp (by fun_prop)
  have hpowDen : ContinuousAt
      (fun s : ℂ => (p : ℂ) ^ (-2 - alpha - beta - gamma - delta - 2 * s)) s0 :=
    (continuousAt_const_cpow hpC).comp (by fun_prop)
  unfold hughesYoungBPrimeFactor hughesYoungB0 hughesYoungB1 hughesYoungB2
  apply ContinuousAt.div
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · exact hden

theorem test_nat_div_cpow {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (z : ℂ) :
    ((h : ℂ) / (k : ℂ)) ^ z = (h : ℂ) ^ z / (k : ℂ) ^ z := by
  have hkR : (0 : ℝ) ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hcast : (h : ℂ) / (k : ℂ) =
      (h : ℂ) * (((k : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [div_eq_mul_inv, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hcast]
  have hmul := Complex.mul_cpow_ofReal_nonneg
    (a := (h : ℝ)) (b := (k : ℝ)⁻¹) (by positivity) hkR z
  have hmul' :
      ((h : ℂ) * (((k : ℝ)⁻¹ : ℝ) : ℂ)) ^ z =
        (h : ℂ) ^ z * ((((k : ℝ)⁻¹ : ℝ) : ℂ)) ^ z := by
    simpa only [Complex.ofReal_natCast] using hmul
  rw [hmul']
  have hinv : ((((k : ℝ)⁻¹ : ℝ) : ℂ)) ^ z = ((k : ℂ) ^ z)⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow_eq_ite]
    simp only [natCast_arg, if_neg (Ne.symm Real.pi_ne_zero)]
  rw [hinv, div_eq_mul_inv]

example {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (alpha gamma : ℂ) :
    ((h : ℂ) / (k : ℂ)) ^ ((alpha - gamma) / 2) =
      (h * k : ℂ) ^ ((alpha + gamma) / 2) *
        (h : ℂ) ^ (-gamma) * (k : ℂ) ^ (-alpha) := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [test_nat_div_cpow hh hk]
  rw [Complex.natCast_mul_natCast_cpow]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  calc
    (h : ℂ) ^ ((alpha - gamma) / 2) *
        (k : ℂ) ^ (-((alpha - gamma) / 2)) =
      ((h : ℂ) ^ ((alpha + gamma) / 2) * (h : ℂ) ^ (-gamma)) *
        ((k : ℂ) ^ ((alpha + gamma) / 2) * (k : ℂ) ^ (-alpha)) := by
          rw [← Complex.cpow_add _ _ hhC, ← Complex.cpow_add _ _ hkC]
          congr 1 <;> ring
    _ = (h : ℂ) ^ ((alpha + gamma) / 2) *
        (k : ℂ) ^ ((alpha + gamma) / 2) *
        ((h : ℂ) ^ (-gamma) * (k : ℂ) ^ (-alpha)) := by ring
    _ = _ := by ring
