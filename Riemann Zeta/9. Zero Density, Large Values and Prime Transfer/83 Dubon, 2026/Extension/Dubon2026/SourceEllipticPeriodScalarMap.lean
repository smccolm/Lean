import Dubon2026.SourceEllipticPeriodHolomorphicLift
import Dubon2026.SourceEllipticPeriodAffineLift

/-! A surjective homomorphism between actual period curves, once its local
holomorphic lifts are supplied, is induced by a nonzero complex scalar.
The scalar maps the actual source lattice into the target lattice. The
local-lift hypothesis is discharged by SourceEllipticPeriodQuotientGerm
for the actual odd quotient; it is not a uniformization or product-identity assumption.
This is the immediate analytic input to DUB-17/18 cyclic quotient roots. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set
open scoped Topology

theorem scalar_map_of_local_lifts (L M : PeriodPair)
    [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
    (ψ : (periodCurve L).toAffine.Point →+ (periodCurve M).toAffine.Point)
    (hψ : Function.Surjective ψ)
    (hloc : ∀ z₀ : ℂ, ∃ U ∈ 𝓝 z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, periodHom M (G z) = ψ (periodHom L z)) :
    ∃ α : ℂˣ, (∀ l ∈ L.lattice, (α : ℂ) * l ∈ M.lattice) ∧
      ∀ z, periodHom M ((α : ℂ) * z) = ψ (periodHom L z) := by
  obtain ⟨F, hFd, hF0, hFint⟩ := exists_holomorphic_lift L M ψ hloc
  have hper : ∀ l ∈ L.lattice, ∀ z, F (z + l) - F z ∈ M.lattice := by
    intro l hl z
    apply (periodPoint_eq_zero_iff M _).mp
    change periodHom M (F (z + l) - F z) = 0
    rw [map_sub, hFint, hFint, map_add,
      show periodHom L l = 0 from periodPoint_of_mem L hl, add_zero, sub_self]
  obtain ⟨α, hαL, hαF⟩ := affine_of_period_differences L M hFd hper
  have hlinear : ∀ z, F z = α * z := by
    intro z
    simpa only [hF0, zero_add] using hαF z
  have hint : ∀ z, periodHom M (α * z) = ψ (periodHom L z) := by
    intro z
    rw [← hlinear z]
    exact hFint z
  have hα : α ≠ 0 := by
    intro hzero
    obtain ⟨P, hP⟩ := hψ (periodHom M (M.ω₁ / 2))
    obtain ⟨z, hz⟩ := periodHom_surjective L P
    have h := hint z
    rw [hzero, zero_mul, map_zero, hz, hP] at h
    exact M.ω₁_div_two_notMem_lattice ((periodPoint_eq_zero_iff M _).mp h.symm)
  exact ⟨Units.mk0 α hα, hαL, hint⟩

end Dubon2026.SourceEllipticPeriod
