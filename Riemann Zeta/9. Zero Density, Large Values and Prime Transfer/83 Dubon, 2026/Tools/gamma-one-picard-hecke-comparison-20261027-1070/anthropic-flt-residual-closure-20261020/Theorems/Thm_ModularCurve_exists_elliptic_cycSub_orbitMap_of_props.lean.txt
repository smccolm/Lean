import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_CycSubRootBridgeN
import Definitions.Def_ModularCurve_SpecialisationBridge
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar

open scoped Classical

open ModularCurve ModularCurve.TatePoint AlgebraicCurve
theorem ModularCurve.exists_elliptic_cycSub_orbitMap_of_props (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (hequivN : ∀ data : ModularPolynomialData N,
      ∀ (m : HahnSeries.monodromy Qbar) (r r' : RootsAt data (nearCurve j₀).j),
        r'.1 = (m : H ≃ₐ[Qbar] H) r.1 →
        B3.b3Act j₀ m (dictN N data j₀ hW1 hW2 hW3 r).1 = (dictN N data j₀ hW1 hW2 hW3 r').1)
    :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props.solution
