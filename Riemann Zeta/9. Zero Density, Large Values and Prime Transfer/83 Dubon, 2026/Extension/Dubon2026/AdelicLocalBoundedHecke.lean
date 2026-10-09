import Dubon2026.AdelicIntrinsicLocalHecke

/-! # The genuine local Hecke sum as a bounded operator on the original full Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual local group action as the original bounded full-adelic Hilbert operator. -/
def adelicCyclicLocalOperator (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g))

/-- The genuine bounded local operator has exactly the original restricted representation action. -/
theorem adelicCyclicLocalOperator_apply (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : AdelicCyclicHilbert f) :
    adelicCyclicLocalOperator f v g x = adelicCyclicLocalRepresentation f v g x := rfl

/-- Each original local bounded operator is an actual isometry. -/
theorem adelicCyclicLocalOperator_norm (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : AdelicCyclicHilbert f) :
    ‖adelicCyclicLocalOperator f v g x‖ = ‖x‖ := adelicCyclicHilbertOperator_norm f _ x

/-- The original intrinsic local coset trace is a finite sum of its genuine bounded unitary operators. -/
def adelicLocalBoundedHeckeTrace (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  ∑ i : Option (ZMod p), adelicCyclicLocalOperator f (rationalPrimePlace p (Fact.out : p.Prime))
    (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
        (finiteAdelicHeckeDiagonal p)⁻¹))

/-- The genuine bounded trace agrees exactly with the intrinsic local Hecke action on every original vector. -/
theorem adelicLocalBoundedHeckeTrace_apply (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert f) :
    adelicLocalBoundedHeckeTrace f p hpN x =
      finitePlaceHeckeTrace N p hpN (adelicCyclicLocalRepresentation f (rationalPrimePlace p (Fact.out : p.Prime))) x := by
  simp only [adelicLocalBoundedHeckeTrace, finitePlaceHeckeTrace, ContinuousLinearMap.sum_apply,
    LinearMap.sum_apply, adelicCyclicLocalOperator_apply]

/-- The original local trace has its literal p+1-summand unitary bound. -/
theorem adelicLocalBoundedHeckeTrace_norm_le (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert f) :
    ‖adelicLocalBoundedHeckeTrace f p hpN x‖ ≤ (p + 1 : ℝ) * ‖x‖ := by
  simp only [adelicLocalBoundedHeckeTrace, ContinuousLinearMap.sum_apply]
  calc
    _ ≤ ∑ i : Option (ZMod p), ‖adelicCyclicLocalOperator f (rationalPrimePlace p (Fact.out : p.Prime))
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) x‖ := norm_sum_le _ _
    _ = _ := by simp [adelicCyclicLocalOperator_norm, Fintype.card_option, ZMod.card]

/-- The actual normalized local Hecke operator retains its bounded Hilbert action. -/
def adelicLocalBoundedNormalizedHecke (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) • adelicLocalBoundedHeckeTrace f p hpN

/-- The genuine bounded normalized action is precisely the previously constructed original local Hecke action. -/
theorem adelicLocalBoundedNormalizedHecke_apply (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert f) :
    adelicLocalBoundedNormalizedHecke f p hpN x = adelicLocalNormalizedHecke f p (Fact.out : p.Prime) hpN x := by
  rw [adelicLocalNormalizedHecke_intrinsic]
  simp only [adelicLocalBoundedNormalizedHecke, ContinuousLinearMap.smul_apply, LinearMap.smul_apply,
    adelicLocalBoundedHeckeTrace_apply]

end
end Dubon2026
