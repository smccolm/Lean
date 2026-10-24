import Dubon2026.SourceEllipticPeriodicLiouville

/-! The native Weierstrass function attains every complex x-coordinate away
from its actual lattice. A missing value gives an entire periodic reciprocal;
the double poles make its values zero at the lattice, contradicting Liouville.
This is the surjectivity input for the actual uniformization map, needed for
the odd-prime quotient product and DUB-17/18 cyclic-root interpretation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set Bornology
open scoped PeriodPair Topology

theorem weierstrassP_surjective (L : PeriodPair) (x₀ : ℂ) : ∃ z, z ∉ L.lattice ∧ ℘[L] z = x₀ := by
  by_contra! hno
  classical

  let G : ℂ → ℂ := fun z => if z ∈ L.lattice then 0 else (℘[L] z - x₀)⁻¹
  have hGcompl : ∀ z ∉ L.lattice, G z = (℘[L] z - x₀)⁻¹ := fun z hz => if_neg hz
  have hGmem : ∀ z ∈ L.lattice, G z = 0 := fun z hz => if_pos hz

  have hGper : ∀ l ∈ L.lattice, ∀ z, G (z + l) = G z := by
    intro l hl z
    by_cases hz : z ∈ L.lattice
    · rw [hGmem z hz, hGmem (z + l) (add_mem hz hl)]
    · have hzl : z + l ∉ L.lattice := fun h => hz (by simpa using sub_mem h hl)
      rw [hGcompl z hz, hGcompl (z + l) hzl, L.weierstrassP_add_coe z ⟨l, hl⟩]

  have hne : ∀ z ∉ L.lattice, ℘[L] z - x₀ ≠ 0 := fun z hz => sub_ne_zero.mpr (hno z hz)
  have hGdiff_compl : DifferentiableOn ℂ G (L.lattice : Set ℂ)ᶜ := by
    refine DifferentiableOn.congr ?_ (fun z hz => hGcompl z hz)
    exact fun z hz => ((L.analyticOnNhd_weierstrassP z hz).sub
      analyticAt_const).differentiableAt.inv (hne z hz) |>.differentiableWithinAt

  have hGdiff : Differentiable ℂ G := by
    intro z
    by_cases hz : z ∈ L.lattice
    ·
      set s := ((L.lattice : Set ℂ) \ {z})ᶜ with hs_def
      have hs_nhds : s ∈ 𝓝 z := L.compl_lattice_diff_singleton_mem_nhds z

      have hs_diff : s \ {z} = (L.lattice : Set ℂ)ᶜ := by
        ext w; simp only [hs_def, mem_diff, mem_compl_iff, mem_singleton_iff]
        constructor
        · rintro ⟨hw, hwne⟩ hwL; exact hw ⟨hwL, hwne⟩
        · exact fun hwL => ⟨fun ⟨h, _⟩ => hwL h, fun h => hwL (h ▸ hz)⟩

      have hGcont : ContinuousAt G z := by
        rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hGmem z hz]

        refine Tendsto.congr'
          (eventually_of_mem (compl_lattice_mem_nhdsNE L z)
            (fun w hw => (hGcompl w hw).symm)) ?_

        have h℘ := tendsto_weierstrassP_cobounded L hz
        have h℘' : Tendsto (fun w => ℘[L] w - x₀) (𝓝[≠] z) (cobounded ℂ) := by
          rw [← tendsto_norm_atTop_iff_cobounded] at h℘ ⊢
          exact tendsto_atTop_mono (fun w => norm_sub_norm_le (℘[L] w) x₀)
            (tendsto_atTop_add_const_right _ (-‖x₀‖) h℘)
        exact tendsto_inv₀_cobounded.comp h℘'
      exact ((differentiableOn_compl_singleton_and_continuousAt_iff hs_nhds).mp
        ⟨hs_diff ▸ hGdiff_compl, hGcont⟩).differentiableAt hs_nhds
    · exact (hGdiff_compl z hz).differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)

  have hGconst := periodic_entire_constant L hGdiff hGper

  have h0 : G 0 = 0 := hGmem 0 (zero_mem _)
  have hω : G (L.ω₁ / 2) = (℘[L] (L.ω₁ / 2) - x₀)⁻¹ :=
    hGcompl _ L.ω₁_div_two_notMem_lattice
  refine absurd (hGconst (L.ω₁ / 2) 0) ?_
  rw [h0, hω]
  exact inv_ne_zero (hne _ L.ω₁_div_two_notMem_lattice)


end Dubon2026.SourceEllipticPeriod
