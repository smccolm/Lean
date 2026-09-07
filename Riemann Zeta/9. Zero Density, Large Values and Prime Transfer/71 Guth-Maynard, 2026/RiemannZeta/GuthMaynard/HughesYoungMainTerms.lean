import RiemannZeta.GuthMaynard.HughesYoungZFactors
import RiemannZeta.External.PNT.ResidueCalcOnRectangles

open Complex Finset Filter Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equations (12), (15), (138), (164), and (173)

This file connects the finite Euler factors proved in
`HughesYoungZFactors` to the zeta quotient used in the source main terms.
The definitions below are the literal equations (12) and (15).
-/

/-- Hughes--Young equation (12). -/
noncomputable def hughesYoungA
    (alpha beta gamma delta s : ℂ) : ℂ :=
  (riemannZeta (1 + s + alpha + gamma) *
      riemannZeta (1 + s + alpha + delta) *
      riemannZeta (1 + s + beta + gamma) *
      riemannZeta (1 + s + beta + delta)) /
    riemannZeta (2 + 2 * s + alpha + beta + gamma + delta)

/-- Hughes--Young equation (15), using the finite rational continuation of
the Euler product from equations (140)--(156). -/
noncomputable def hughesYoungZ
    (h k : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  hughesYoungA alpha beta gamma delta s *
    hughesYoungBPair h k alpha beta gamma delta s

/-- Simultaneous interchange symmetry of equation (12). -/
theorem hughesYoungA_swap
    (alpha beta gamma delta s : ℂ) :
    hughesYoungA alpha beta gamma delta s =
      hughesYoungA beta alpha delta gamma s := by
  unfold hughesYoungA
  ring_nf

/-- Simultaneous interchange symmetry of equation (141). -/
theorem hughesYoungBPair_swap
    (h k : ℕ) (alpha beta gamma delta s : ℂ) :
    hughesYoungBPair h k alpha beta gamma delta s =
      hughesYoungBPair h k beta alpha delta gamma s := by
  unfold hughesYoungBPair
  rw [hughesYoungB_swap h alpha beta gamma delta s,
    hughesYoungB_swap k gamma delta alpha beta s]

/-- Simultaneous interchange symmetry of equation (15). -/
theorem hughesYoungZ_swap
    (h k : ℕ) (alpha beta gamma delta s : ℂ) :
    hughesYoungZ h k alpha beta gamma delta s =
      hughesYoungZ h k beta alpha delta gamma s := by
  unfold hughesYoungZ
  rw [hughesYoungA_swap, hughesYoungBPair_swap]

/-- Limit form of the zeta residue under a nonzero affine
reparameterization. -/
theorem tendsto_riemannZeta_affine_residue
    {a b p : ℂ} (ha : a ≠ 0) (hp : a * p + b = 1) :
    Tendsto (fun z : ℂ => (z - p) * riemannZeta (a * z + b))
      (nhdsWithin p {p}ᶜ) (nhds a⁻¹) := by
  have hcontinuous : Tendsto (fun z : ℂ => a * z + b)
      (nhdsWithin p {p}ᶜ) (nhds 1) := by
    have h : Tendsto (fun z : ℂ => a * z + b) (nhds p)
        (nhds (a * p + b)) :=
      (tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds
    rw [hp] at h
    exact h.mono_left inf_le_left
  have havoid : ∀ᶠ z : ℂ in nhdsWithin p {p}ᶜ,
      a * z + b ∈ ({1} : Set ℂ)ᶜ := by
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

/-- A nonzero affine reparameterization of the zeta pole at `1` has residue
equal to the reciprocal slope. -/
theorem residue_riemannZeta_affine
    {a b p : ℂ} (ha : a ≠ 0) (hp : a * p + b = 1) :
    residue (fun z : ℂ => riemannZeta (a * z + b)) p = a⁻¹ :=
  residue_eq_of_tendsto (tendsto_riemannZeta_affine_residue ha hp)

/-- Multiplication by a continuous regular factor evaluates that factor at
the affine zeta pole. -/
theorem residue_riemannZeta_affine_mul
    {a b p : ℂ} {f : ℂ → ℂ} (ha : a ≠ 0) (hp : a * p + b = 1)
    (hf : ContinuousAt f p) :
    residue (fun z : ℂ => riemannZeta (a * z + b) * f z) p =
      a⁻¹ * f p := by
  apply residue_eq_of_tendsto
  have hpole := tendsto_riemannZeta_affine_residue ha hp
  have hmul := hpole.mul hf.continuousWithinAt
  simpa only [mul_assoc] using hmul

/-- Complex powers distribute over a quotient of positive natural numbers.
The positivity is what removes the branch-cut ambiguity. -/
theorem natCast_div_natCast_cpow
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (z : ℂ) :
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

/-- The positive-base power identity converting the source `(h/k)` factor
to the two prime-power normalizations in equation (167). -/
theorem hughesYoungEquation164_power_identity
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (alpha gamma : ℂ) :
    ((h : ℂ) / (k : ℂ)) ^ ((alpha - gamma) / 2) =
      (h * k : ℂ) ^ ((alpha + gamma) / 2) *
        (h : ℂ) ^ (-gamma) * (k : ℂ) ^ (-alpha) := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [natCast_div_natCast_cpow hh hk]
  rw [Complex.natCast_mul_natCast_cpow]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  have hhExp : (alpha + gamma) / 2 + -gamma =
      (alpha - gamma) / 2 := by ring
  have hkExp : (alpha + gamma) / 2 + -alpha =
      -((alpha - gamma) / 2) := by ring
  calc
    (h : ℂ) ^ ((alpha - gamma) / 2) *
        (k : ℂ) ^ (-((alpha - gamma) / 2)) =
      ((h : ℂ) ^ ((alpha + gamma) / 2) * (h : ℂ) ^ (-gamma)) *
        ((k : ℂ) ^ ((alpha + gamma) / 2) * (k : ℂ) ^ (-alpha)) := by
          rw [← Complex.cpow_add _ _ hhC, ← Complex.cpow_add _ _ hkC,
            hhExp, hkExp]
    _ = (h : ℂ) ^ ((alpha + gamma) / 2) *
        (k : ℂ) ^ ((alpha + gamma) / 2) *
        ((h : ℂ) ^ (-gamma) * (k : ℂ) ^ (-alpha)) := by ring
    _ = _ := by ring

/-- The pointwise identity underlying Hughes--Young equation (138). -/
theorem hughesYoungEquation138_integrand
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {alpha beta gamma delta : ℂ}
    (hhc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha - delta) ≠ 0)
    (hhr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0)
    (hkc : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-gamma - beta) ≠ 0)
    (hkr : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta) ≠ 0) :
    hughesYoungA (-gamma) beta (-alpha) delta 0 *
        ((h : ℂ) ^ alpha * (k : ℂ) ^ gamma *
          (hughesYoungC h alpha beta gamma delta 0 *
            hughesYoungC k gamma delta alpha beta 0)) =
      hughesYoungZ h k (-gamma) beta (-alpha) delta 0 := by
  rw [hughesYoungEquation157 hh hk hhc hhr hkc hkr]
  rfl

/-- The three regular zeta factors and denominator occurring in equation
(166), separated from the single affine zeta pole. -/
noncomputable def hughesYoungEquation166RegularFactor
    (alpha beta gamma delta : ℂ) : ℂ :=
  (riemannZeta (1 - gamma + delta) *
      riemannZeta (1 - alpha + beta) *
      riemannZeta (1 - alpha + beta - gamma + delta)) /
    riemannZeta (2 - alpha + beta - gamma + delta)

/-- The regular factor in equation (165), before evaluation at the affine
zeta pole. -/
noncomputable def hughesYoungEquation165RegularFunction
    (h k : ℕ) (alpha beta gamma delta z : ℂ) : ℂ :=
  ((riemannZeta (1 + 2 * z + alpha + delta) *
      riemannZeta (1 + 2 * z + beta + gamma) *
      riemannZeta (1 + 2 * z + beta + delta)) /
    riemannZeta (2 + 2 * (2 * z) + alpha + beta + gamma + delta)) *
    hughesYoungBPair h k alpha beta gamma delta (2 * z)

/-- Continuity of the regular factor in equation (165). -/
theorem continuousAt_hughesYoungEquation165RegularFunction
    (h k : ℕ) (alpha beta gamma delta : ℂ)
    (h1 : 1 - gamma + delta ≠ 1)
    (h2 : 1 - alpha + beta ≠ 1)
    (h3 : 1 - alpha + beta - gamma + delta ≠ 1)
    (h4 : 2 - alpha + beta - gamma + delta ≠ 1)
    (hz4 : riemannZeta (2 - alpha + beta - gamma + delta) ≠ 0)
    (hhden : ∀ p ∈ hughesYoungPrimeFactors h,
      ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
        (1 - (p : ℂ) ^
          (-2 - alpha - beta - gamma - delta - 2 * (-alpha - gamma))) ≠ 0)
    (hkden : ∀ p ∈ hughesYoungPrimeFactors k,
      ((p : ℂ) ^ (-alpha) - (p : ℂ) ^ (-beta)) *
        (1 - (p : ℂ) ^
          (-2 - gamma - delta - alpha - beta - 2 * (-alpha - gamma))) ≠ 0) :
    ContinuousAt
      (hughesYoungEquation165RegularFunction h k alpha beta gamma delta)
      ((-alpha - gamma) / 2) := by
  let s0 : ℂ := (-alpha - gamma) / 2
  have harg1 : 1 + 2 * s0 + alpha + delta ≠ 1 := by
    have he : 1 + 2 * s0 + alpha + delta = 1 - gamma + delta := by
      simp only [s0]
      ring
    rw [he]
    exact h1
  have harg2 : 1 + 2 * s0 + beta + gamma ≠ 1 := by
    have he : 1 + 2 * s0 + beta + gamma = 1 - alpha + beta := by
      simp only [s0]
      ring
    rw [he]
    exact h2
  have harg3 : 1 + 2 * s0 + beta + delta ≠ 1 := by
    have he : 1 + 2 * s0 + beta + delta =
        1 - alpha + beta - gamma + delta := by
      simp only [s0]
      ring
    rw [he]
    exact h3
  have harg4 : 2 + 2 * (2 * s0) + alpha + beta + gamma + delta ≠ 1 := by
    have he : 2 + 2 * (2 * s0) + alpha + beta + gamma + delta =
        2 - alpha + beta - gamma + delta := by
      simp only [s0]
      ring
    rw [he]
    exact h4
  have hz1 : ContinuousAt
      (fun z : ℂ => riemannZeta (1 + 2 * z + alpha + delta)) s0 := by
    exact ContinuousAt.comp' (differentiableAt_riemannZeta harg1).continuousAt
      (by fun_prop)
  have hz2 : ContinuousAt
      (fun z : ℂ => riemannZeta (1 + 2 * z + beta + gamma)) s0 := by
    exact ContinuousAt.comp' (differentiableAt_riemannZeta harg2).continuousAt
      (by fun_prop)
  have hz3 : ContinuousAt
      (fun z : ℂ => riemannZeta (1 + 2 * z + beta + delta)) s0 := by
    exact ContinuousAt.comp' (differentiableAt_riemannZeta harg3).continuousAt
      (by fun_prop)
  have hzDen : ContinuousAt
      (fun z : ℂ =>
        riemannZeta (2 + 2 * (2 * z) + alpha + beta + gamma + delta)) s0 := by
    exact ContinuousAt.comp' (differentiableAt_riemannZeta harg4).continuousAt
      (by fun_prop)
  have hzDen0 :
      riemannZeta (2 + 2 * (2 * s0) + alpha + beta + gamma + delta) ≠ 0 := by
    have he : 2 + 2 * (2 * s0) + alpha + beta + gamma + delta =
        2 - alpha + beta - gamma + delta := by
      simp only [s0]
      ring
    rw [he]
    exact hz4
  have hB0 := continuousAt_hughesYoungBPair h k alpha beta gamma delta
    (-alpha - gamma) hhden hkden
  have hB : ContinuousAt
      (fun z : ℂ => hughesYoungBPair h k alpha beta gamma delta (2 * z)) s0 := by
    have hs : 2 * s0 = -alpha - gamma := by
      simp only [s0]
      ring
    rw [← hs] at hB0
    exact ContinuousAt.comp' hB0 (by fun_prop)
  unfold hughesYoungEquation165RegularFunction
  exact (((hz1.mul hz2).mul hz3).div hzDen hzDen0).mul hB

/-- Exact residue calculation (165)--(166). -/
theorem hughesYoungEquations165_166
    (h k : ℕ) (alpha beta gamma delta : ℂ)
    (h1 : 1 - gamma + delta ≠ 1)
    (h2 : 1 - alpha + beta ≠ 1)
    (h3 : 1 - alpha + beta - gamma + delta ≠ 1)
    (h4 : 2 - alpha + beta - gamma + delta ≠ 1)
    (hz4 : riemannZeta (2 - alpha + beta - gamma + delta) ≠ 0)
    (hhden : ∀ p ∈ hughesYoungPrimeFactors h,
      ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
        (1 - (p : ℂ) ^
          (-2 - alpha - beta - gamma - delta - 2 * (-alpha - gamma))) ≠ 0)
    (hkden : ∀ p ∈ hughesYoungPrimeFactors k,
      ((p : ℂ) ^ (-alpha) - (p : ℂ) ^ (-beta)) *
        (1 - (p : ℂ) ^
          (-2 - gamma - delta - alpha - beta - 2 * (-alpha - gamma))) ≠ 0) :
    residue (fun z : ℂ =>
      hughesYoungZ h k alpha beta gamma delta (2 * z))
        ((-alpha - gamma) / 2) =
      (1 / 2 : ℂ) *
        hughesYoungEquation166RegularFactor alpha beta gamma delta *
        hughesYoungBPair h k alpha beta gamma delta (-alpha - gamma) := by
  let s0 : ℂ := (-alpha - gamma) / 2
  let F : ℂ → ℂ :=
    hughesYoungEquation165RegularFunction h k alpha beta gamma delta
  have hF : ContinuousAt F s0 :=
    continuousAt_hughesYoungEquation165RegularFunction h k
      alpha beta gamma delta h1 h2 h3 h4 hz4 hhden hkden
  have hp : (2 : ℂ) * s0 + (1 + alpha + gamma) = 1 := by
    simp only [s0]
    ring
  have hres := residue_riemannZeta_affine_mul
    (a := (2 : ℂ)) (b := 1 + alpha + gamma) (p := s0)
    (by norm_num) hp hF
  have hdecomp :
      (fun z : ℂ => hughesYoungZ h k alpha beta gamma delta (2 * z)) =
        (fun z : ℂ => riemannZeta (2 * z + (1 + alpha + gamma)) * F z) := by
    funext z
    unfold hughesYoungZ hughesYoungA F
      hughesYoungEquation165RegularFunction
    ring_nf
  rw [hdecomp, hres]
  have hFvalue : F s0 =
      hughesYoungEquation166RegularFactor alpha beta gamma delta *
        hughesYoungBPair h k alpha beta gamma delta (-alpha - gamma) := by
    unfold F hughesYoungEquation165RegularFunction
      hughesYoungEquation166RegularFactor
    have hs : 2 * s0 = -alpha - gamma := by
      simp only [s0]
      ring
    rw [hs]
    congr 2 <;> ring_nf
  rw [hFvalue]
  ring

/-- Hughes--Young equation (164), combining the affine residue calculation
with the finite Euler identity (167). -/
theorem hughesYoungEquation164
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {alpha beta gamma delta : ℂ}
    (h1 : 1 - gamma + delta ≠ 1)
    (h2 : 1 - alpha + beta ≠ 1)
    (h3 : 1 - alpha + beta - gamma + delta ≠ 1)
    (h4 : 2 - alpha + beta - gamma + delta ≠ 1)
    (hz4 : riemannZeta (2 - alpha + beta - gamma + delta) ≠ 0)
    (hhden : ∀ p ∈ hughesYoungPrimeFactors h,
      ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
        (1 - (p : ℂ) ^
          (-2 - alpha - beta - gamma - delta - 2 * (-alpha - gamma))) ≠ 0)
    (hkden : ∀ p ∈ hughesYoungPrimeFactors k,
      ((p : ℂ) ^ (-alpha) - (p : ℂ) ^ (-beta)) *
        (1 - (p : ℂ) ^
          (-2 - gamma - delta - alpha - beta - 2 * (-alpha - gamma))) ≠ 0)
    (hhc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (gamma - delta) ≠ 0)
    (hhr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0)
    (hkc : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (alpha - beta) ≠ 0)
    (hkr : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta) ≠ 0) :
    (1 / 2 : ℂ) *
        hughesYoungEquation166RegularFactor alpha beta gamma delta *
        (((h : ℂ) / (k : ℂ)) ^ ((alpha - gamma) / 2)) *
        (hughesYoungC h alpha beta gamma delta ((-alpha - gamma) / 2) *
          hughesYoungC k gamma delta alpha beta ((-alpha - gamma) / 2)) =
      residue (fun z : ℂ =>
          hughesYoungZ h k alpha beta gamma delta (2 * z))
          ((-alpha - gamma) / 2) *
        (h * k : ℂ) ^ ((alpha + gamma) / 2) := by
  have hres := hughesYoungEquations165_166 h k alpha beta gamma delta
    h1 h2 h3 h4 hz4 hhden hkden
  have hpair := hughesYoungEquation167_pair hh hk hhc hhr hkc hkr
  have hpow := hughesYoungEquation164_power_identity hh hk alpha gamma
  rw [hres]
  calc
    (1 / 2 : ℂ) *
        hughesYoungEquation166RegularFactor alpha beta gamma delta *
        (((h : ℂ) / (k : ℂ)) ^ ((alpha - gamma) / 2)) *
        (hughesYoungC h alpha beta gamma delta ((-alpha - gamma) / 2) *
          hughesYoungC k gamma delta alpha beta ((-alpha - gamma) / 2)) =
      (1 / 2 : ℂ) *
        hughesYoungEquation166RegularFactor alpha beta gamma delta *
        ((h * k : ℂ) ^ ((alpha + gamma) / 2) *
          ((h : ℂ) ^ (-gamma) * (k : ℂ) ^ (-alpha) *
            (hughesYoungC h alpha beta gamma delta ((-alpha - gamma) / 2) *
              hughesYoungC k gamma delta alpha beta ((-alpha - gamma) / 2)))) := by
        rw [hpow]
        ring
    _ = (1 / 2 : ℂ) *
        hughesYoungEquation166RegularFactor alpha beta gamma delta *
        ((h * k : ℂ) ^ ((alpha + gamma) / 2) *
          hughesYoungBPair h k alpha beta gamma delta (-alpha - gamma)) := by
        rw [hpair]
    _ = ((1 / 2 : ℂ) *
          hughesYoungEquation166RegularFactor alpha beta gamma delta *
          hughesYoungBPair h k alpha beta gamma delta (-alpha - gamma)) *
        (h * k : ℂ) ^ ((alpha + gamma) / 2) := by ring

/-- Hughes--Young equation (174).  The pole is the fourth zeta factor of
the displayed `Z`; simultaneous shift symmetry moves it to the first factor
so that equations (165)--(166) apply verbatim. -/
theorem hughesYoungEquation174
    (h k : ℕ) (alpha beta gamma delta : ℂ)
    (h1 : 1 - gamma + delta ≠ 1)
    (h2 : 1 - alpha + beta ≠ 1)
    (h3 : 1 - alpha + beta - gamma + delta ≠ 1)
    (h4 : 2 - alpha + beta - gamma + delta ≠ 1)
    (hz4 : riemannZeta (2 - alpha + beta - gamma + delta) ≠ 0)
    (hhden : ∀ p ∈ hughesYoungPrimeFactors h,
      ((p : ℂ) ^ beta - (p : ℂ) ^ alpha) *
        (1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta)) ≠ 0)
    (hkden : ∀ p ∈ hughesYoungPrimeFactors k,
      ((p : ℂ) ^ delta - (p : ℂ) ^ gamma) *
        (1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta)) ≠ 0) :
    residue (fun z : ℂ =>
      hughesYoungZ h k (-gamma) (-delta) (-alpha) (-beta) (2 * z))
        ((beta + delta) / 2) =
      (1 / 2 : ℂ) *
        hughesYoungEquation166RegularFactor alpha beta gamma delta *
        hughesYoungBPair h k (-gamma) (-delta) (-alpha) (-beta)
          (beta + delta) := by
  have h3q : 1 - -delta + -gamma - -beta + -alpha ≠ 1 := by
    have he : 1 - -delta + -gamma - -beta + -alpha =
        1 - alpha + beta - gamma + delta := by ring
    rw [he]
    exact h3
  have h4q : 2 - -delta + -gamma - -beta + -alpha ≠ 1 := by
    have he : 2 - -delta + -gamma - -beta + -alpha =
        2 - alpha + beta - gamma + delta := by ring
    rw [he]
    exact h4
  have hz4q :
      riemannZeta (2 - -delta + -gamma - -beta + -alpha) ≠ 0 := by
    have he : 2 - -delta + -gamma - -beta + -alpha =
        2 - alpha + beta - gamma + delta := by ring
    rw [he]
    exact hz4
  have hhdenQ : ∀ p ∈ hughesYoungPrimeFactors h,
      ((p : ℂ) ^ (- -beta) - (p : ℂ) ^ (- -alpha)) *
        (1 - (p : ℂ) ^
          (-2 - -delta - -gamma - -beta - -alpha -
            2 * (- -delta - -beta))) ≠ 0 := by
    intro p hp
    convert hhden p hp using 1
    all_goals ring_nf
  have hkdenQ : ∀ p ∈ hughesYoungPrimeFactors k,
      ((p : ℂ) ^ (- -delta) - (p : ℂ) ^ (- -gamma)) *
        (1 - (p : ℂ) ^
          (-2 - -beta - -alpha - -delta - -gamma -
            2 * (- -delta - -beta))) ≠ 0 := by
    intro p hp
    convert hkden p hp using 1
    all_goals ring_nf
  have hres := hughesYoungEquations165_166 h k
    (-delta) (-gamma) (-beta) (-alpha)
    (by
      convert h2 using 1
      all_goals ring_nf)
    (by
      convert h1 using 1
      all_goals ring_nf)
    h3q h4q hz4q hhdenQ hkdenQ
  have hpole : (- -delta - -beta) / 2 = (beta + delta) / 2 := by ring
  have harg : - -delta - -beta = beta + delta := by ring
  rw [hpole, harg] at hres
  have hfun :
      (fun z : ℂ =>
          hughesYoungZ h k (-delta) (-gamma) (-beta) (-alpha) (2 * z)) =
        (fun z : ℂ =>
          hughesYoungZ h k (-gamma) (-delta) (-alpha) (-beta) (2 * z)) := by
    funext z
    exact hughesYoungZ_swap h k (-delta) (-gamma) (-beta) (-alpha) (2 * z)
  rw [← hfun]
  rw [← hughesYoungBPair_swap h k (-delta) (-gamma) (-beta) (-alpha)
    (beta + delta)]
  have hregular :
      hughesYoungEquation166RegularFactor (-delta) (-gamma) (-beta) (-alpha) =
        hughesYoungEquation166RegularFactor alpha beta gamma delta := by
    unfold hughesYoungEquation166RegularFactor
    ring_nf
  rw [← hregular]
  exact hres

/-- Hughes--Young equation (173), combining the second polar residue with
the finite Euler identity (175). -/
theorem hughesYoungEquation173
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {alpha beta gamma delta : ℂ}
    (h1 : 1 - gamma + delta ≠ 1)
    (h2 : 1 - alpha + beta ≠ 1)
    (h3 : 1 - alpha + beta - gamma + delta ≠ 1)
    (h4 : 2 - alpha + beta - gamma + delta ≠ 1)
    (hz4 : riemannZeta (2 - alpha + beta - gamma + delta) ≠ 0)
    (hhden : ∀ p ∈ hughesYoungPrimeFactors h,
      ((p : ℂ) ^ beta - (p : ℂ) ^ alpha) *
        (1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta)) ≠ 0)
    (hkden : ∀ p ∈ hughesYoungPrimeFactors k,
      ((p : ℂ) ^ delta - (p : ℂ) ^ gamma) *
        (1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta)) ≠ 0)
    (hhx : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha + beta) ≠ 0)
    (hhc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (alpha - beta) ≠ 0)
    (hhr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0)
    (hkx : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-gamma + delta) ≠ 0)
    (hkc : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (gamma - delta) ≠ 0)
    (hkr : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta) ≠ 0) :
    (1 / 2 : ℂ) *
        hughesYoungEquation166RegularFactor alpha beta gamma delta *
        (h : ℂ) ^ alpha * (k : ℂ) ^ gamma *
        (hughesYoungC h alpha beta gamma delta ((-beta - delta) / 2) *
          hughesYoungC k gamma delta alpha beta ((-beta - delta) / 2)) =
      residue (fun z : ℂ =>
        hughesYoungZ h k (-gamma) (-delta) (-alpha) (-beta) (2 * z))
          ((beta + delta) / 2) := by
  rw [hughesYoungEquation174 h k alpha beta gamma delta
    h1 h2 h3 h4 hz4 hhden hkden]
  rw [← hughesYoungEquation175 hh hk hhx hhc hhr hkx hkc hkr]
  ring

/-- Algebraic evaluation of the regular part of equation (165) at the pole
`s = (-alpha-gamma)/2`. -/
theorem hughesYoungA_two_mul_regular_value
    (alpha beta gamma delta : ℂ) :
    let s0 := (-alpha - gamma) / 2
    (riemannZeta (1 + 2 * s0 + alpha + delta) *
        riemannZeta (1 + 2 * s0 + beta + gamma) *
        riemannZeta (1 + 2 * s0 + beta + delta)) /
      riemannZeta (2 + 2 * (2 * s0) + alpha + beta + gamma + delta) =
      hughesYoungEquation166RegularFactor alpha beta gamma delta := by
  dsimp only
  unfold hughesYoungEquation166RegularFactor
  congr 1 <;> ring_nf

end RiemannZeta.GuthMaynard
