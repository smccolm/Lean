import Dubon2026.RationalTraceCoherentScalarCupComparison
import Dubon2026.RationalTraceFiniteLocalSourceCup

/-! Apply the proved coherent normalization factor to the actual local
Cartier source cocycle. Its original local cup then equals the coherent
exceptional trace pairing on the unchanged source arithmetic class.
This is the termwise input for DUB-17's annihilator-to-total implication. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

private def scalarCocycle {R G : Type} [CommRing R] [Group G]
    [TopologicalSpace R] [TopologicalSpace G]
    (A : Rep.{0} R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
    (s : R) (d : continuousRepresentationCocyclesOne A) :
    continuousRepresentationCocyclesOne A := s • d

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (p : ℕ) (hp : p.Prime)

/-- Scale the actual trace-dual cocycle by the derived coordinate factor;
the original local Cartier/root construction is otherwise unchanged. -/
def rationalTraceCoherentCartierSourceCocycle
    (d : rationalTraceOriginalCartierSourceCocycles a q σ p hp) :
    rationalTraceOriginalCartierSourceCocycles a q σ p hp :=
  @scalarCocycle (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)
    _ _ _ _
    (matrixTraceZeroCharacterRep (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
    (inferInstanceAs (TopologicalSpace (matrixTraceZeroSubmodule ι (ZMod q))))
    (inferInstanceAs (IsTopologicalAddGroup (matrixTraceZeroSubmodule ι (ZMod q))))
    (inferInstanceAs (ContinuousSMul (ZMod q) (matrixTraceZeroSubmodule ι (ZMod q))))
    (rationalArithmeticLocalNormalizationScalar a q hqa p hp) d

/-- The coherently normalized original cocycle retains the exact scalar
multiple of every original matrix value. -/
theorem rationalTraceCoherentCartierSourceCocycle_apply
    (d : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :
    (rationalTraceCoherentCartierSourceCocycle a q hqa σ p hp d).val g =
      rationalArithmeticLocalNormalizationScalar a q hqa p hp • d.val g := rfl

/-- The original normalized Cartier cup on the scaled local cocycle is
minus the coherent scalar pairing on the unchanged original H1 classes. -/
theorem rationalTraceSourceScalarCupInvariant_coherent
    (hσ : Continuous σ)
    (d : rationalTraceOriginalCartierSourceCocycles a q σ p hp)
    (c : continuousTraceZeroAdjointCocycles σ) :
    rationalTraceSourceScalarCupInvariant a q σ p hp hσ
      (rationalTraceCoherentCartierSourceCocycle a q hqa σ p hp d) c =
      -rationalCyclicInvariant q
        (rationalArithmeticPrimeTraceH1ScalarCup a q hqa p hp
          (σ.comp (rationalPrimeArithmeticRestriction a p hp))
          (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
          (Quotient.mk _ d)
          (continuousTraceZeroH1Restriction σ hσ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
            (rationalPrimeArithmeticRestriction a p hp).continuous (Quotient.mk _ c))) := by
  exact congrArg (fun t : ZMod q => -rationalCyclicInvariant q t)
    (rationalPrimeTraceH1ScalarCup_normalization_smul a q hqa p hp
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous)
      (Quotient.mk _ d)
      (continuousTraceZeroH1Restriction σ hσ (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous (Quotient.mk _ c)))

end
end Dubon2026
