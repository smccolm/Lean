import Dubon2026.AdelicDirichletLocalRestriction
import Dubon2026.FinitePlaceHeckeCosetDeterminant
import Dubon2026.AdelicLocalSelfTwistHecke
import Dubon2026.CuspSelfTwists

/-! # Actual global Dirichlet self-twists force original Fourier coefficient self-twists -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {N D : ℕ} [NeZero N] [NeZero D] {k : ℤ}
    (F : PrimitiveCuspForm N k) (χ : DirichletCharacter ℂ D)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (adelicDirichletDeterminant χ)))

/-- The original global twisted intertwiner restricts to the actual local character twist, with its determinant character identified. -/
def adelicDirichletSelfTwistLocal (v : HeightOneSpectrum ℤ) :
    Representation.IntertwiningMap (adelicCyclicLocalRepresentation F.toCuspForm v)
      (scalarTwistRepresentation (adelicCyclicLocalRepresentation F.toCuspForm v)
        (finitePlaceDirichletDeterminant χ v)) where
  toLinearMap := T.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    have h := scalarTwist_intertwining_apply (adelicCyclicHilbertRepresentation F.toCuspForm)
      (adelicCyclicHilbertRepresentation F.toCuspForm) (adelicDirichletDeterminant χ) T
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) x
    rw [adelicDirichletDeterminant_local] at h
    exact h

/-- An actual injective global quadratic Dirichlet self-twist forces the original normalized Fourier relation at every prime away from both levels. -/
theorem adelicDirichletSelfTwist_normalized (hχ : χ.IsQuadratic) (hT : Function.Injective T) :
    IsCoefficientSelfTwist N χ (normalizedCuspCoefficients F.toCuspForm) := by
  intro p hp hpND
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpN, hpD⟩ := Nat.coprime_mul_iff_right.mp hpND
  have hD : (D : ℤ) ∉ (rationalPrimePlace p hp).asIdeal := by
    rw [rationalPrimePlace_nat_mem_iff]
    exact hp.coprime_iff_not_dvd.mp hpD
  have hn : adelicDirichletSelfTwistLocal F χ T (rationalPrimePlace p hp)
      (adelicCyclicHilbertGenerator F.toCuspForm) ≠ 0 := by
    intro hz
    apply adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F)
    apply hT
    exact hz.trans (map_zero T).symm
  exact adelicLocalSelfTwist_fourier_relation F hpN (finitePlaceDirichletDeterminant χ _)
    (adelicDirichletSelfTwistLocal F χ T _)
    (finitePlaceDirichletDeterminant_level χ N _ hD) (χ (p : ZMod D))
    (finitePlaceDirichletDeterminant_hecke_quadratic χ hχ N p hp hpN hpD) hn

/-- The actual global self-twist therefore gives the classical original Fourier coefficient condition, with normalization discharged. -/
theorem adelicDirichletSelfTwist_classical (hχ : χ.IsQuadratic) (hT : Function.Injective T) :
    IsCoefficientSelfTwist N χ (cuspCoefficients F.toCuspForm) :=
  (cusp_selfTwist_normalization_iff F.toCuspForm χ).mp
    (adelicDirichletSelfTwist_normalized F χ T hχ hT)

end
end Dubon2026
