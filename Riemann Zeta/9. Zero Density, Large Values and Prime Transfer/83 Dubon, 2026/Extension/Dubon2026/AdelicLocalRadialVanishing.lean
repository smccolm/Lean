import Dubon2026.AdelicLocalRadialRecurrence
import Dubon2026.RadialRecurrenceUniqueness
import Dubon2026.AdelicLocalCartanCoefficient
import Dubon2026.AdelicLocalCyclicClosure
import Dubon2026.ClosedSpanOrthogonality

/-! # Genuine local orbit orthogonality from the original primitive radial recurrence -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Orthogonality to the original primitive generator forces all its actual radial spherical coefficients to vanish. -/
theorem adelicCyclicLocal_radial_orthogonal_zero {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (horth : inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) = 0) (n : ℕ) :
    @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      x (adelicCyclicHilbertGenerator F.toCuspForm) n = 0 := by
  have he := adelicCyclicLocal_primitive_radial_recurrence F hpN x hx
  apply radial_recurrence_zero p _ _ ?_ he.1 he.2 n
  simpa only [finitePlaceRadialCoefficient, pow_zero, map_one, Module.End.one_apply] using horth

/-- Actual Cartan factorization transfers the proved primitive radial vanishing to every original local orbit vector. -/
theorem adelicCyclicLocal_orbit_orthogonal_zero {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (horth : inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) = 0)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    inner ℂ x (adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g (adelicCyclicHilbertGenerator F.toCuspForm)) = 0 := by
  obtain ⟨n, he⟩ := adelicCyclicLocal_matrixCoefficient_cartan F.toCuspForm hpN x
    (adelicCyclicHilbertGenerator F.toCuspForm) hx
    (adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm _) g
  exact he.trans (adelicCyclicLocal_radial_orthogonal_zero F hpN x hx horth n)

/-- Inside the actual original local cyclic Hilbert space, a local fixed vector orthogonal to the primitive generator is zero. -/
theorem adelicLocalCyclic_fixed_orthogonal_eq_zero {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hcyclic : x ∈ adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (hfixed : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (horth : inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) = 0) : x = 0 :=
  @closedSpan_orthogonal_eq_zero (AdelicCyclicHilbert F.toCuspForm)
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    inferInstance inferInstance _ x hcyclic
    (adelicCyclicLocal_orbit_orthogonal_zero F hpN x hfixed horth)

end
end Dubon2026
