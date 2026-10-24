import Dubon2026.SourceEllipticWeierstrassSurjectivity
import Dubon2026.SourcePeriodLatticeInvariants

/-! Nonconstancy and finite local order for the actual Weierstrass function.
Reuse the existing connected lattice complement and the newly proved
surjectivity. These supply analytic continuation and generic points in the
addition law, required for the actual uniformization and odd-prime product
on the DUB-17/18 cyclic-root dependency chain.
Adapted from the frozen Apache-2.0 FLT period uniformization proof. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set
open scoped PeriodPair Topology

theorem isPreconnected_compl_lattice (L : PeriodPair) :
    IsPreconnected (L.lattice : Set ℂ)ᶜ := by
  simpa only [Set.union_self] using
    SourceFunctionField.LatticeInvariants.isPreconnected_compl_union L L

theorem weierstrassP_not_eventually_const (L : PeriodPair) {c : ℂ}
    (hc : c ∉ L.lattice) (e : ℂ) : ¬ ℘[L] =ᶠ[𝓝 c] fun _ => e := by
  intro hconst
  have hEq : Set.EqOn ℘[L] (fun _ => e) (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_weierstrassP.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (isPreconnected_compl_lattice L) hc hconst
  obtain ⟨z, hz, he⟩ := weierstrassP_surjective L (e + 1)
  have h := he.symm.trans (hEq hz)
  exact one_ne_zero (add_left_cancel (h.trans (add_zero e).symm))

theorem analyticOrderAt_weierstrassP_sub_self_ne_top (L : PeriodPair) {c : ℂ}
    (hc : c ∉ L.lattice) :
    analyticOrderAt (fun z => ℘[L] z - ℘[L] c) c ≠ ⊤ := by
  rw [Ne, analyticOrderAt_eq_top]
  exact fun h => weierstrassP_not_eventually_const L hc (℘[L] c)
    (h.mono fun z hz => sub_eq_zero.mp hz)

theorem analyticOrderAt_derivWeierstrassP (L : PeriodPair) {c : ℂ}
    (hc : c ∉ L.lattice) :
    analyticOrderAt ℘'[L] c + 1 = analyticOrderAt (fun z => ℘[L] z - ℘[L] c) c := by
  have hP : AnalyticAt ℂ ℘[L] c := L.analyticOnNhd_weierstrassP c hc
  simpa [L.deriv_weierstrassP] using hP.analyticOrderAt_deriv_add_one

theorem exists_derivWeierstrassP_ne_zero (L : PeriodPair) :
    ∃ c, c ∉ L.lattice ∧ ℘'[L] c ≠ 0 := by
  by_contra! h
  have h0 : ℘'[L] =ᶠ[𝓝 (L.ω₁ / 2)] fun _ => 0 :=
    eventually_of_mem (L.isClosed_lattice.isOpen_compl.mem_nhds L.ω₁_div_two_notMem_lattice)
      fun u hu => h u hu
  have hord : analyticOrderAt ℘'[L] (L.ω₁ / 2) = ⊤ := analyticOrderAt_eq_top.mpr h0
  have hfin := analyticOrderAt_weierstrassP_sub_self_ne_top L L.ω₁_div_two_notMem_lattice
  rw [← analyticOrderAt_derivWeierstrassP L L.ω₁_div_two_notMem_lattice, hord, top_add] at hfin
  exact hfin rfl

end Dubon2026.SourceEllipticPeriod
