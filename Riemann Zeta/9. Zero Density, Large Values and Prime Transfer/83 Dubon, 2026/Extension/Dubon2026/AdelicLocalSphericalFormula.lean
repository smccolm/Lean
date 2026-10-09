import Dubon2026.SphericalRadialFormula
import Dubon2026.AdelicLocalRadialRecurrence
import Dubon2026.AdelicLocalCartanCoefficient

/-! # Closed spherical matrix coefficients for the actual primitive local representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The original primitive local radial coefficient is the exact spherical polynomial of its actual normalized Fourier eigenvalue. -/
theorem adelicCyclicLocal_primitive_radial_formula {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) (n : ℕ) :
    @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      x (adelicCyclicHilbertGenerator F.toCuspForm) n =
    inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) *
      sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) n := by
  obtain ⟨hb, hc⟩ := adelicCyclicLocal_primitive_radial_recurrence F hpN x hx
  have hr : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast (Fact.out : p.Prime).pos)).ne'
  have hs : (Real.sqrt p : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have he := radial_recurrence_chebyshev_formula p (Real.sqrt p)
    (normalizedCuspCoefficients F.toCuspForm p) hr hs _ hb hc n
  simpa only [finitePlaceRadialCoefficient, pow_zero, map_one, Module.End.one_apply] using he

/-- Every genuine local spherical matrix coefficient has the actual normalized Fourier spherical formula at its true Cartan radius. -/
theorem adelicCyclicLocal_primitive_spherical_formula {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    ∃ n : ℕ, inner ℂ x (adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g (adelicCyclicHilbertGenerator F.toCuspForm)) =
      inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) *
        sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) n := by
  obtain ⟨n, hn⟩ := adelicCyclicLocal_matrixCoefficient_cartan F.toCuspForm hpN x
    (adelicCyclicHilbertGenerator F.toCuspForm) hx
    (adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm _) g
  exact ⟨n, hn.trans (adelicCyclicLocal_primitive_radial_formula F hpN x hx n)⟩

end
end Dubon2026
