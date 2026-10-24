import Dubon2026.SourceEllipticWeierstrassNonconstant

/-! Differentiate the actual Weierstrass differential equation and use
analytic continuation across the isolated derivative zeros. The resulting
second and third derivatives control the principal-part cancellation in
the addition formula, needed for uniformization and the DUB-17/18 odd-prime
product identity. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set
open scoped PeriodPair Topology
variable (L : PeriodPair)

theorem two_mul_deriv_derivWeierstrassP_mul {z : ℂ} (hz : z ∉ L.lattice) :
    2 * ℘'[L] z * deriv ℘'[L] z = (12 * ℘[L] z ^ 2 - L.g₂) * ℘'[L] z := by
  have hP : DifferentiableAt ℂ ℘[L] z := (L.analyticOnNhd_weierstrassP z hz).differentiableAt
  have hP' : DifferentiableAt ℂ ℘'[L] z := (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt

  have hEq : (fun u => ℘'[L] u ^ 2) =ᶠ[𝓝 z]
      fun u => 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with u hu
    exact L.derivWeierstrassP_sq u hu
  have hD := hEq.deriv_eq

  have hdP : HasDerivAt ℘[L] (℘'[L] z) z := L.deriv_weierstrassP ▸ hP.hasDerivAt
  have hL : HasDerivAt (fun u => ℘'[L] u ^ 2) (2 * ℘'[L] z * deriv ℘'[L] z) z :=
    (hP'.hasDerivAt.pow 2).congr_deriv (by ring)
  have hR' : HasDerivAt (fun u => 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃)
      (4 * (3 * ℘[L] z ^ 2 * ℘'[L] z) - L.g₂ * ℘'[L] z - 0) z :=
    (((hdP.pow 3).const_mul 4).sub (hdP.const_mul L.g₂)).sub (hasDerivAt_const z _)
  have hR : HasDerivAt (fun u => 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃)
      ((12 * ℘[L] z ^ 2 - L.g₂) * ℘'[L] z) z := hR'.congr_deriv (by ring)
  rw [hL.deriv, hR.deriv] at hD
  exact hD


theorem deriv_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by

  have hAnL : AnalyticOnNhd ℂ (deriv ℘'[L]) (L.lattice : Set ℂ)ᶜ :=
    fun u hu => (L.analyticOnNhd_derivWeierstrassP u hu).deriv
  have hAnR : AnalyticOnNhd ℂ (fun u => 6 * ℘[L] u ^ 2 - L.g₂ / 2) (L.lattice : Set ℂ)ᶜ :=
    fun u hu => (analyticAt_const.mul ((L.analyticOnNhd_weierstrassP u hu).pow 2)).sub
      analyticAt_const

  obtain ⟨c, hc, hP'c⟩ := (exists_derivWeierstrassP_ne_zero L)
  have hAgree : deriv ℘'[L] =ᶠ[𝓝 c] fun u => 6 * ℘[L] u ^ 2 - L.g₂ / 2 := by
    have hP'cont : ContinuousAt ℘'[L] c :=
      (L.analyticOnNhd_derivWeierstrassP c hc).continuousAt
    have hne_nhd : ∀ᶠ u in 𝓝 c, ℘'[L] u ≠ 0 := hP'cont.eventually_ne hP'c
    filter_upwards [hne_nhd, L.isClosed_lattice.isOpen_compl.mem_nhds hc] with u hu_ne hu_mem
    have hmul := (two_mul_deriv_derivWeierstrassP_mul L) hu_mem
    refine mul_left_cancel₀ (a := 2 * ℘'[L] u) (mul_ne_zero two_ne_zero hu_ne) ?_
    calc 2 * ℘'[L] u * deriv ℘'[L] u = (12 * ℘[L] u ^ 2 - L.g₂) * ℘'[L] u := hmul
      _ = 2 * ℘'[L] u * (6 * ℘[L] u ^ 2 - L.g₂ / 2) := by ring

  exact hAnL.eqOn_of_preconnected_of_eventuallyEq hAnR (isPreconnected_compl_lattice L)
    hc hAgree hz


theorem deriv2_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (deriv ℘'[L]) z = 12 * ℘[L] z * ℘'[L] z := by
  have hP : DifferentiableAt ℂ ℘[L] z := (L.analyticOnNhd_weierstrassP z hz).differentiableAt

  have hEq : deriv ℘'[L] =ᶠ[𝓝 z] fun u => 6 * ℘[L] u ^ 2 - L.g₂ / 2 := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with u hu
    exact (deriv_derivWeierstrassP L) hu
  rw [hEq.deriv_eq]
  have hdP : HasDerivAt ℘[L] (℘'[L] z) z := L.deriv_weierstrassP ▸ hP.hasDerivAt
  have h1' : HasDerivAt (fun u => 6 * ℘[L] u ^ 2 - L.g₂ / 2)
      (6 * (2 * ℘[L] z ^ 1 * ℘'[L] z) - 0) z :=
    ((hdP.pow 2).const_mul 6).sub (hasDerivAt_const z _)
  exact h1'.congr_deriv (by ring) |>.deriv


end Dubon2026.SourceEllipticPeriod
