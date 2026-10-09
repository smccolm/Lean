import Dubon2026.AdelicLocalRepresentation
import Dubon2026.RationalPrimePlace
import Dubon2026.PrimitiveCuspForms

/-! # Actual unramified local vectors at every ordinary prime away from the original level -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original nonzero primitive cusp generator is a genuine spherical vector at every actual rational prime not dividing its original level. -/
theorem adelicPrimitive_good_prime_spherical {N p : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (hp : p.Prime) (hpN : p.Coprime N) :
    adelicCyclicHilbertGenerator f.toCuspForm ≠ 0 ∧
      ∀ g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletionIntegers ℚ),
        adelicCyclicLocalRepresentation f.toCuspForm (rationalPrimePlace p hp)
          (GeneralLinearGroup.map ((rationalPrimePlace p hp).adicCompletionIntegers ℚ).subtype g)
          (adelicCyclicHilbertGenerator f.toCuspForm) = adelicCyclicHilbertGenerator f.toCuspForm := by
  refine ⟨adelicCyclicHilbertGenerator_ne_zero f.toCuspForm (primitiveCuspForm_ne_zero f), ?_⟩
  apply adelicCyclicLocal_generator_integral_fixed
  rw [rationalPrimePlace_nat_mem_iff]
  exact hp.coprime_iff_not_dvd.mp hpN

end
end Dubon2026
