import Dubon2026.AdelicLocalFixedSpace
import Dubon2026.AdelicLocalHeckeSymmetric
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The actual self-adjoint normalized Hecke operator on the original local fixed Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original fixed Hilbert space gives its bounded operators the actual Hilbert adjoint. -/
instance adelicLocalFixedSpaceOperatorStar (v : HeightOneSpectrum ℤ) :
    Star (adelicLocalFixedSpace f v →L[ℂ] adelicLocalFixedSpace f v) :=
  ⟨fun T => @ContinuousLinearMap.adjoint ℂ (adelicLocalFixedSpace f v) (adelicLocalFixedSpace f v)
    inferInstance inferInstance inferInstance (adelicLocalFixedSpaceInnerProduct f v)
    (adelicLocalFixedSpaceInnerProduct f v) (adelicLocalFixedSpace_complete f v)
    (adelicLocalFixedSpace_complete f v) T⟩

/-- Restriction of the genuine normalized local Hecke operator to its actual invariant fixed space. -/
def adelicLocalSphericalHecke (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) :
    adelicLocalFixedSpace f (rationalPrimePlace p (Fact.out : p.Prime)) →L[ℂ]
      adelicLocalFixedSpace f (rationalPrimePlace p (Fact.out : p.Prime)) :=
  (adelicLocalBoundedNormalizedHecke f p hpN).restrict (by
    intro x hx
    rw [adelicLocalBoundedNormalizedHecke_apply]
    exact adelicLocalNormalizedHecke_local_fixed f hpN x hx)

/-- The original restricted operator retains exactly the genuine normalized local Hecke action. -/
theorem adelicLocalSphericalHecke_apply (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (x : adelicLocalFixedSpace f (rationalPrimePlace p (Fact.out : p.Prime))) :
    (adelicLocalSphericalHecke f p hpN x).val =
      adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN x.val :=
  adelicLocalBoundedNormalizedHecke_apply f p hpN x.val

/-- The genuine normalized local spherical Hecke operator is self-adjoint on the original complete local integral fixed space. -/
theorem adelicLocalSphericalHecke_selfAdjoint (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) :
    IsSelfAdjoint (adelicLocalSphericalHecke f p hpN) := by
  apply (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric ℂ
    (adelicLocalFixedSpace f (rationalPrimePlace p (Fact.out : p.Prime)))
    inferInstance inferInstance inferInstance inferInstance _).mpr
  intro x y
  change inner ℂ (adelicLocalSphericalHecke f p hpN x).val y.val =
    inner ℂ x.val (adelicLocalSphericalHecke f p hpN y).val
  rw [adelicLocalSphericalHecke_apply, adelicLocalSphericalHecke_apply]
  exact adelicLocalNormalizedHecke_symmetric f hpN x.val y.val x.property y.property

/-- The actual cusp generator considered inside its genuine local fixed Hilbert space. -/
def adelicLocalFixedGenerator (v : HeightOneSpectrum ℤ) : adelicLocalFixedSpace f v :=
  ⟨adelicCyclicHilbertGenerator f, adelicCyclicHilbertGenerator_mem_localFixed f v⟩

/-- The original fixed-space generator is nonzero whenever its actual cusp form is nonzero. -/
theorem adelicLocalFixedGenerator_ne_zero (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    adelicLocalFixedGenerator f v ≠ 0 := by
  intro h
  exact adelicCyclicHilbertGenerator_ne_zero f hf (congrArg Subtype.val h)

/-- The original nonzero primitive generator remains an exact Fourier-eigenvalue eigenvector of the genuine self-adjoint local spherical operator. -/
theorem adelicLocalSphericalHecke_primitive_generator (F : PrimitiveCuspForm N k)
    (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) :
    adelicLocalSphericalHecke F.toCuspForm p hpN
        (adelicLocalFixedGenerator F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
      normalizedCuspCoefficients F.toCuspForm p •
        adelicLocalFixedGenerator F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) := by
  apply Subtype.ext
  rw [adelicLocalSphericalHecke_apply]
  exact adelicLocalNormalizedHecke_primitive_generator F (Fact.out : p.Prime) hpN

end
end Dubon2026
