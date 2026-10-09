import Dubon2026.AdelicLocalFullFixedHecke
import Dubon2026.FinitePlaceHeckeCharacterTwist

/-! # Original Fourier consequences of a genuine local character self-twist

The hypotheses describe the actual local group character on the integral group
and on the original Hecke cosets. Deriving them from a Dirichlet idèle character
is a separate bridge; no Fourier self-twist relation is assumed here.
-/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

private theorem scalar_of_twisted_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A T : Module.End ℂ V) (z c : ℂ) (x : V)
    (hx : A x = c • x) (hTx : A (T x) = c • T x)
    (hcov : T (A x) = z • A (T x)) (hne : T x ≠ 0) : z * c = c := by
  rw [hx, map_smul, hTx, smul_smul] at hcov
  exact (smul_left_injective ℂ hne) hcov.symm

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (χ : GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) →* ℂ)
    (T : Representation.IntertwiningMap
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (scalarTwistRepresentation
        (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) χ))

omit [NeZero p] in
/-- A genuine local twisted intertwiner sends the actual original generator into the entire genuine global local-fixed space. -/
theorem adelicLocalSelfTwist_generator_fixed
    (hχK : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), χ g.val = 1) :
    T (adelicCyclicHilbertGenerator F.toCuspForm) ∈
      adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) :=
  scalarTwist_intertwining_fixed _ χ T _ hχK _
    (adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm _)

/-- Nonvanishing of the actual twisted image and the proved full fixed-space Hecke action force the original normalized Fourier coefficient relation. -/
theorem adelicLocalSelfTwist_fourier_relation
    (hχK : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), χ g.val = 1)
    (z : ℂ) (hχ : ∀ i : Option (ZMod p), χ
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) = z)
    (hT : T (adelicCyclicHilbertGenerator F.toCuspForm) ≠ 0) :
    z * normalizedCuspCoefficients F.toCuspForm p = normalizedCuspCoefficients F.toCuspForm p := by
  have hcov : T (adelicLocalNormalizedHecke F.toCuspForm p (Fact.out : p.Prime) hpN
      (adelicCyclicHilbertGenerator F.toCuspForm)) =
    z • adelicLocalNormalizedHecke F.toCuspForm p (Fact.out : p.Prime) hpN
      (T (adelicCyclicHilbertGenerator F.toCuspForm)) := by
    rw [adelicLocalNormalizedHecke_intrinsic]
    simp only [LinearMap.smul_apply, map_smul]
    rw [finitePlaceHeckeTrace_character_intertwines N p hpN _ χ z hχ T]
    exact smul_comm _ z _
  exact @scalar_of_twisted_eigenvector (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance (adelicLocalNormalizedHecke F.toCuspForm p (Fact.out : p.Prime) hpN)
    T.toLinearMap z (normalizedCuspCoefficients F.toCuspForm p) (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicLocalNormalizedHecke_primitive_generator F (Fact.out : p.Prime) hpN)
    (adelicLocalNormalizedHecke_full_fixed F hpN _ (adelicLocalSelfTwist_generator_fixed F χ T hχK))
    hcov hT

end
end Dubon2026
