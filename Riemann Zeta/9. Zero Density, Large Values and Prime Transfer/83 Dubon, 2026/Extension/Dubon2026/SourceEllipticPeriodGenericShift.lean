import Dubon2026.SourceEllipticWeierstrassNonconstant

/-! A simultaneous generic shift removes the exceptional cases in the
actual period-point addition law. Only the eight exceptional sets consumed
by that proof are excluded; no derivative-zero census is needed. This
serves uniformization and the DUB-17/18 odd-prime quotient-product identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Set
open scoped PeriodPair

theorem countable_lattice (L : PeriodPair) : (L.lattice : Set ℂ).Countable := by
  refine (Set.countable_range fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂).mono ?_
  intro z hz
  obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hz
  exact ⟨(m, n), h⟩

theorem countable_analytic_level (L : PeriodPair) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    (hfnc : ∃ z ∉ L.lattice, f z ≠ 0) :
    {z | z ∉ L.lattice ∧ f z = 0}.Countable := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected
    (isPreconnected_compl_lattice L) with heq | hne
  · obtain ⟨z, hz, hfz⟩ := hfnc
    exact absurd (heq hz) hfz
  · have hD : IsDiscrete ({z | f z = 0} ∩ (L.lattice : Set ℂ)ᶜ) := by
      refine isDiscrete_of_codiscreteWithin ?_
      simp only [compl_setOf] at hne ⊢
      exact hne
    haveI := hD.to_subtype
    have hcount : Countable ({z | f z = 0} ∩ (L.lattice : Set ℂ)ᶜ : Set ℂ) :=
      countable_of_Lindelof_of_discrete
    refine (Set.countable_coe_iff.mp hcount).mono fun z hz => ?_
    exact Set.mem_inter hz.2 hz.1

theorem countable_weierstrassP_eq (L : PeriodPair) (c : ℂ) :
    {z | z ∉ L.lattice ∧ ℘[L] z = c}.Countable := by
  obtain ⟨z, hz, he⟩ := weierstrassP_surjective L (c + 1)
  have h := countable_analytic_level L (f := fun z => ℘[L] z - c)
    (L.analyticOnNhd_weierstrassP.sub analyticOnNhd_const) ⟨z, hz, by simp [he]⟩
  refine h.mono fun z hz => ?_
  exact ⟨hz.1, sub_eq_zero.mpr hz.2⟩

theorem exists_generic_period_shift (L : PeriodPair) (z w : ℂ) :
    ∃ u : ℂ, u ∉ L.lattice ∧ 2 * u ∉ L.lattice ∧ w + u ∉ L.lattice ∧
      z + w + u ∉ L.lattice ∧ 2 * (w + u) ∉ L.lattice ∧
      ℘[L] w ≠ ℘[L] u ∧ ℘[L] (z + w) ≠ ℘[L] u ∧ ℘[L] z ≠ ℘[L] (w + u) := by
  have hLc := countable_lattice L
  let S : Set ℂ := (L.lattice : Set ℂ) ∪ {u | 2 * u ∈ L.lattice} ∪
    {u | w + u ∈ L.lattice} ∪ {u | z + w + u ∈ L.lattice} ∪
    {u | 2 * (w + u) ∈ L.lattice} ∪ {u | u ∉ L.lattice ∧ ℘[L] u = ℘[L] w} ∪
    {u | u ∉ L.lattice ∧ ℘[L] u = ℘[L] (z + w)} ∪
    {u | w + u ∉ L.lattice ∧ ℘[L] (w + u) = ℘[L] z}
  have hSc : S.Countable := by
    have hinj : ∀ c : ℂ, Function.Injective (fun u : ℂ => c + u) :=
      fun c => add_right_injective c
    have hinj2 : Function.Injective (fun u : ℂ => 2 * u) := mul_right_injective₀ two_ne_zero
    exact ((((((hLc.union (hLc.preimage hinj2)).union (hLc.preimage (hinj w))).union
      (hLc.preimage (hinj (z + w)))).union (hLc.preimage (hinj2.comp (hinj w)))).union
      (countable_weierstrassP_eq L (℘[L] w))).union
      (countable_weierstrassP_eq L (℘[L] (z + w)))).union
      ((countable_weierstrassP_eq L (℘[L] z)).preimage (hinj w))
  have hSne : Sᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    exact fun hSu => not_countable_complex (hSu ▸ hSc)
  obtain ⟨u, hu⟩ := hSne
  simp only [S, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
    not_and] at hu
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hu
  exact ⟨u, h1, h2, h3, h4, h5, Ne.symm (h6 h1), Ne.symm (h7 h1), Ne.symm (h8 h3)⟩

end Dubon2026.SourceEllipticPeriod
