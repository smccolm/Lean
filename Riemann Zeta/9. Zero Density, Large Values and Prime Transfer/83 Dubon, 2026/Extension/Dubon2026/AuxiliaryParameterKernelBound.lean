import Dubon2026.AuxiliaryFiniteParameterQuotient
import Dubon2026.AuxiliaryGroupAlgebraPowerSeries
import Dubon2026.ContinuousPowerSeriesHomExt
import Mathlib.Topology.Algebra.Ring.Ideal

/-! The actual auxiliary group-algebra parameter kernel lies in every
maximal-ideal power below its selected congruence level. A constructed
reverse map to that finite quotient and polynomial density give the
bound directly. This discharges the coefficient-ideal convergence input
for DUB-17, before genuine Hecke-module freeness is supplied. -/

namespace Dubon2026
noncomputable section
open IsLocalRing
open scoped MvPowerSeries.WithPiTopology

/-- The original generator values and continuity force the parameter
kernel into the prescribed maximal-adic power. The reverse finite
quotient map is constructed from the selected congruences. -/
theorem auxiliaryGroupAlgebra_parameter_kernel_le
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {η ι : Type} [Fintype η] [Fintype ι] [DecidableEq ι]
    (Q : Finset Nat.Primes) (q level n : ℕ) [Fact q.Prime] [CharP (ResidueField O) q]
    (e : η ≃ Q × ι) (hn : n ≤ level)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level])
    (g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q)
    (hg : ∀ p d, ∃ j : ℕ, g p ^ j = d) :
    let D := ∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q
    letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
    ∀ f : MvPowerSeries η O →ₐ[O] MonoidAlgebra O D,
      (∀ j, f (MvPowerSeries.X j) = MonoidAlgebra.of O D
        (Pi.mulSingle (e j).1 (Pi.mulSingle (e j).2 (g (e j).1))) - 1) →
      Continuous f → RingHom.ker f.toRingHom ≤ maximalIdeal (MvPowerSeries η O) ^ n := by
  classical
  let D := ∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q
  letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
  dsimp only
  intro f hf hfc
  letI := finitePowerSeries_compactSpace (O := O) (η := η)
  letI := finiteVariablePowerSeries_isNoetherian (R := O) η
  letI := finitePowerSeries_isAdicTopology (O := O) (η := η)
  letI : ContinuousSMul O (MvPowerSeries η O ⧸ maximalIdeal (MvPowerSeries η O) ^ n) := ⟨by
    have hc : Continuous (algebraMap O
        (MvPowerSeries η O ⧸ maximalIdeal (MvPowerSeries η O) ^ n)) :=
      continuous_quot_mk.comp MvPowerSeries.WithPiTopology.continuous_C
    simpa only [Algebra.smul_def] using (hc.comp continuous_fst).mul continuous_snd⟩
  let back := auxiliaryFiniteParameterGroupAlgebra O Q q level n e hn hmod g hg
  have hback : Continuous back := IsModuleTopology.continuous_of_linearMap back.toLinearMap
  let mk := Ideal.Quotient.mkₐ O (maximalIdeal (MvPowerSeries η O) ^ n)
  have he : back.comp f = mk := by
    apply continuousPowerSeriesAlgHom_ext
    · exact hback.comp hfc
    · exact continuous_quot_mk
    · intro j
      change back (f (MvPowerSeries.X j)) = mk (MvPowerSeries.X j)
      rw [hf]
      change back.toRingHom ((MonoidAlgebra.of O D
        (Pi.mulSingle (e j).1 (Pi.mulSingle (e j).2 (g (e j).1)))) - 1) =
          mk (MvPowerSeries.X j)
      rw [map_sub back.toRingHom
        (MonoidAlgebra.of O D (Pi.mulSingle (e j).1
          (Pi.mulSingle (e j).2 (g (e j).1)))) 1, map_one back.toRingHom]
      have hgen := auxiliaryFiniteParameterGroupAlgebra_generator O Q q level n e hn hmod g hg
        (e j).1 (e j).2
      have hgen' : back.toRingHom (MonoidAlgebra.of O D
          (Pi.mulSingle (e j).1 (Pi.mulSingle (e j).2 (g (e j).1)))) =
          Ideal.Quotient.mk (maximalIdeal (MvPowerSeries η O) ^ n)
            (1 + MvPowerSeries.X j) := by
        simpa only [Prod.mk.eta, e.symm_apply_apply] using hgen
      rw [hgen']
      change mk (1 + MvPowerSeries.X j) - 1 = mk (MvPowerSeries.X j)
      rw [map_add, map_one, add_sub_cancel_left]
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change mk x = 0
  rw [← he]
  change back (f x) = 0
  change f x = 0 at hx
  rw [hx, map_zero]

end
end Dubon2026
