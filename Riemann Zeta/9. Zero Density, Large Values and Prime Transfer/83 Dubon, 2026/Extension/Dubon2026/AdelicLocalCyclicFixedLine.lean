import Dubon2026.AdelicLocalRadialVanishing
import Dubon2026.OrthogonalGeneratorLine

/-! # The actual good-prime fixed space inside the original local cyclic Hilbert space is exactly the original generator line -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- For the original primitive cusp form, actual local cyclic membership and good-prime integral invariance characterize exactly its original generator line. -/
theorem adelicLocalCyclic_fixed_eq_generator_line {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊓
      adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) =
        Submodule.span ℂ {adelicCyclicHilbertGenerator F.toCuspForm} :=
  @submodule_inf_eq_generator_line (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance
    _ _ (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicLocalCyclicClosedSpan_generator_mem F.toCuspForm _)
    (adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm _)
    (adelicLocalCyclic_fixed_orthogonal_eq_zero F hpN)

/-- Every actual good-prime fixed vector in the genuine original local cyclic Hilbert space is an exact scalar multiple of the original primitive cusp generator. -/
theorem adelicLocalCyclic_fixed_generator_scalar {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hcyclic : x ∈ adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (hfixed : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    ∃ c : ℂ, x = c • adelicCyclicHilbertGenerator F.toCuspForm := by
  have hx : x ∈ Submodule.span ℂ ({adelicCyclicHilbertGenerator F.toCuspForm} :
      Set (AdelicCyclicHilbert F.toCuspForm)) := by
    rw [← adelicLocalCyclic_fixed_eq_generator_line F hpN]
    exact ⟨hcyclic, hfixed⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨c, hc.symm⟩

end
end Dubon2026
