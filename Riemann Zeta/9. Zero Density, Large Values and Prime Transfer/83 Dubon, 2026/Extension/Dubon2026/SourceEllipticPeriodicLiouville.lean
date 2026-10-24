import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Tactic

/-! The two elementary analytic inputs for the actual period uniformization:
entire functions periodic under the actual lattice are constant, and the
native Weierstrass function tends to infinity at each lattice point. Native
lattice compactness avoids rebuilding a fundamental-domain argument.
These serve the odd-prime product identity and the DUB-17/18 cyclic-root census. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set
open scoped PeriodPair Topology

theorem periodic_entire_constant (L : PeriodPair) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hp : ∀ l ∈ L.lattice, ∀ z, f (z + l) = f z) (z w : ℂ) : f z = f w :=
  hf.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice f hf.continuous
      (fun z l hl => hp l hl z)).isBounded z w

theorem compl_lattice_mem_nhdsNE (L : PeriodPair) (l : ℂ) :
    (L.lattice : Set ℂ)ᶜ ∈ 𝓝[≠] l := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (L.compl_lattice_diff_singleton_mem_nhds l),
    self_mem_nhdsWithin] with z hz hzne hzL
  exact hz ⟨hzL, hzne⟩

theorem tendsto_weierstrassP_cobounded (L : PeriodPair) {l : ℂ} (hl : l ∈ L.lattice) :
    Tendsto ℘[L] (𝓝[≠] l) (Bornology.cobounded ℂ) := by
  refine tendsto_cobounded_of_meromorphicOrderAt_neg ?_
  simp only [L.order_weierstrassP l hl]
  decide

end Dubon2026.SourceEllipticPeriod
