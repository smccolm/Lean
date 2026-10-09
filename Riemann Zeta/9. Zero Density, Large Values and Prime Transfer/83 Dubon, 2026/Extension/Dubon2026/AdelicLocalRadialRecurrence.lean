import Dubon2026.FinitePlaceRadialEigenRecurrence
import Dubon2026.HeckeRadialNormalization
import Dubon2026.AdelicLocalFixedSpace
import Dubon2026.AdelicLocalCentralCharacter

/-! # Exact original primitive Fourier eigenvalue in the genuine local spherical radial recurrence -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The actual original primitive cusp generator satisfies the intrinsic unnormalized local Hecke equation with its exact original Fourier coefficient and square-root factor. -/
theorem adelicLocalHeckeTrace_primitive_generator {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    @finitePlaceHeckeTrace (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance N p
      inferInstance inferInstance inferInstance hpN
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicCyclicHilbertGenerator F.toCuspForm) =
    ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) •
      adelicCyclicHilbertGenerator F.toCuspForm := by
  have he := adelicLocalNormalizedHecke_primitive_generator F (Fact.out : p.Prime) hpN
  rw [adelicLocalNormalizedHecke_intrinsic, LinearMap.smul_apply] at he
  exact @hecke_trace_eigen_of_normalized (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance (p : ℝ) (by exact_mod_cast (Fact.out : p.Prime).pos) _ _ _ he

/-- The genuine original local spherical coefficient of every fixed vector against the primitive cusp generator satisfies the exact radial boundary equation and recurrence with the original normalized Fourier eigenvalue. -/
theorem adelicCyclicLocal_primitive_radial_recurrence {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    let φ := @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      x (adelicCyclicHilbertGenerator F.toCuspForm)
    let μ := (Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p
    μ * φ 0 = ((p : ℂ) + 1) * φ 1 ∧
      ∀ n, μ * φ (n + 1) = φ n + (p : ℂ) * φ (n + 2) := by
  exact @finitePlaceHecke_radial_eigen_recurrence (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance N p inferInstance inferInstance inferInstance hpN
    (adelicCyclicLocalRepresentation F.toCuspForm _)
    (adelicCyclicLocalRepresentation_inner F.toCuspForm _)
    (adelicCyclicLocal_scalar_action F.toCuspForm _) x (adelicCyclicHilbertGenerator F.toCuspForm)
    hx (adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm _) _
    (adelicLocalHeckeTrace_primitive_generator F hpN)

end
end Dubon2026
