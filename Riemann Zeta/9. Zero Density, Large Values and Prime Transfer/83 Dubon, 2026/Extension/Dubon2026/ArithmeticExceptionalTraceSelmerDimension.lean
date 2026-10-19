import Dubon2026.ArithmeticExceptionalTraceLocalConditions
import Dubon2026.ArithmeticTraceGlobalH1Finite
import Dubon2026.SelmerAnnihilatorDimension

/-! Numerical comparison for the actual original arithmetic Selmer spaces.
The exact arithmetic localization and derived global finiteness discharge
the duality and finite-dimensionality inputs. This is the numerical input to
DUB-17's deformation patching chain, retaining the everywhere-zero dual kernel. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)
  (L : Submodule (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ))
  (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0)

include hq2 hn

/-- The original Selmer dimensions satisfy the exact balanced identity.
The kernel is the original global dual classes with zero localization at every
exceptional prime; it is retained and is not assumed to vanish. -/
theorem rationalArithmeticTraceSelmer_finrank_balance :
    Module.finrank (ZMod q) (L.comap (rationalArithmeticTraceH1Localization a q ha σ hσ)) +
      Module.finrank (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) +
      Module.finrank (ZMod q) (LinearMap.ker
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)) =
    Module.finrank (ZMod q) (ContinuousTraceZeroAdjointH1 σ hσ) +
      Module.finrank (ZMod q) L +
      Module.finrank (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ L) := by
  haveI := rationalArithmeticTraceH1_finite a q hqa ha σ hσ
  haveI := rationalArithmeticTraceDualH1_finite a q hqa ha σ hσ
  haveI := rationalArithmeticExceptionalTraceH1_finite a q ha σ hσ
  haveI : Module.Finite (ZMod q) (ContinuousTraceZeroAdjointH1 σ hσ) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod q) (RationalArithmeticTraceDualH1 a q hqa σ hσ) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) := Module.Finite.of_finite
  let P := rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
  haveI : P.IsPerfPair := rationalArithmeticExceptionalTracePairing_isPerfPair a q hqa ha σ hσ hn
  have he := selmer_finrank_of_range_eq_annihilator
    (rationalArithmeticTraceH1Localization a q ha σ hσ)
    (P.comp (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ))
    (rationalArithmeticTraceDualLocalization_range_eq_annihilator a ha q σ hn hσ hqa hq2) L
  have hk : LinearMap.ker P = ⊥ := LinearMap.ker_eq_bot.mpr
    (LinearMap.IsPerfPair.bijective_left P).injective
  rw [LinearMap.ker_comp_of_ker_eq_bot _ hk] at he
  exact he

/-- Changing the specified local subspace changes the actual primal-minus-dual
Selmer dimension by exactly the change in local dimension. This cancels the
same original global and everywhere-zero terms, without an Euler-characteristic premise. -/
theorem rationalArithmeticTraceSelmer_finrank_comparison
    (M : Submodule (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ)) :
    Module.finrank (ZMod q) (L.comap (rationalArithmeticTraceH1Localization a q ha σ hσ)) +
      Module.finrank (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ M) +
      Module.finrank (ZMod q) M =
    Module.finrank (ZMod q) (M.comap (rationalArithmeticTraceH1Localization a q ha σ hσ)) +
      Module.finrank (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ L) +
      Module.finrank (ZMod q) L := by
  have hL := rationalArithmeticTraceSelmer_finrank_balance a q hqa ha σ hσ L hq2 hn
  have hM := rationalArithmeticTraceSelmer_finrank_balance a q hqa ha σ hσ M hq2 hn
  omega

end
end Dubon2026
