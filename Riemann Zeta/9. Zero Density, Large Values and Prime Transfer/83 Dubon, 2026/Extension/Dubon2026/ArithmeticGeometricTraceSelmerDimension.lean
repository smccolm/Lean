import Dubon2026.ArithmeticGeometricTraceSelmer

/-! The numerical local contribution of the actual geometric condition.
The full exceptional product quotient has precisely the codimension of the
genuine finite-flat trace subspace at the specified prime. The remaining local
dimension is displayed explicitly on DUB-17's deformation patching route. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ) (p : rationalArithmeticExceptionalPrimes a ha)
  (m : FiniteFreeHopfPointModel.{0,0,0,0,0}
    (rationalPrimeLocalIntegerRing p.val.val p.val.property)
    (rationalPrimeLocalField p.val.val p.val.property)
    (rationalPrimeLocalClosure p.val.val p.val.property)
    (Multiplicative (ι → ZMod q))
    (matrixUnderlyingGroupAction
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)))

/-- Imposing the actual geometric condition in the original product costs exactly
its prime-local codimension. Other exceptional coordinates introduce no extra term. -/
theorem rationalArithmeticGeometricTraceProductCondition_codimension :
    Module.finrank (ZMod q) (rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m) +
      Module.finrank (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) =
    Module.finrank (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) +
      Module.finrank (ZMod q) (rationalPrimeGeometricTraceCondition a q σ hσ p.val m) := by
  haveI := rationalArithmeticExceptionalTraceH1_finite a q ha σ hσ
  haveI : Module.Finite (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :=
    Module.Finite.of_finite
  haveI : Finite (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) :=
    rationalPrimeTraceZeroAdjointH1_finite p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
  haveI : Module.Finite (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) :=
    Module.Finite.of_finite
  let S := rationalPrimeGeometricTraceCondition a q σ hσ p.val m
  let f : RationalArithmeticExceptionalTraceH1 a q ha σ hσ →ₗ[ZMod q]
      (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val ⧸ S) :=
    S.mkQ.comp (LinearMap.proj p)
  have hf : Function.Surjective f := (Submodule.mkQ_surjective S).comp
    (LinearMap.proj_surjective p)
  have hk : LinearMap.ker f = rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m := by
    change LinearMap.ker (S.mkQ.comp (LinearMap.proj p :
      RationalArithmeticExceptionalTraceH1 a q ha σ hσ →ₗ[ZMod q]
        rationalArithmeticPrimeTraceH1Module a q σ hσ p.val)) = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    rfl
  have hd := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hk] at hd
  have hs := S.finrank_quotient_add_finrank
  change Module.finrank (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val ⧸ S) +
      Module.finrank (ZMod q) (rationalPrimeGeometricTraceCondition a q σ hσ p.val m) =
    Module.finrank (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) at hs
  omega

variable (hqa : (q : 𝓞 ℚ) ∣ a) (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0)
include hq2 hn

/-- The actual geometric Selmer dimension has exactly the genuine prime-local
finite-flat contribution and the original dual Selmer correction. No numerical
finite-flat dimension, residual model existence or dual-kernel vanishing is assumed. -/
theorem rationalArithmeticGeometricTraceSelmer_finrank_balance :
    Module.finrank (ZMod q) (rationalArithmeticGeometricTraceSelmer a q ha σ hσ p m) +
      Module.finrank (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) +
      Module.finrank (ZMod q) (LinearMap.ker
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)) =
    Module.finrank (ZMod q) (ContinuousTraceZeroAdjointH1 σ hσ) +
      Module.finrank (ZMod q) (rationalPrimeGeometricTraceCondition a q σ hσ p.val m) +
      Module.finrank (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ
        (rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m)) := by
  have hb := rationalArithmeticTraceSelmer_finrank_balance a q hqa ha σ hσ
    (rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m) hq2 hn
  have hc := rationalArithmeticGeometricTraceProductCondition_codimension a q ha σ hσ p m
  change Module.finrank (ZMod q) (rationalArithmeticGeometricTraceSelmer a q ha σ hσ p m) +
      Module.finrank (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) +
      Module.finrank (ZMod q) (LinearMap.ker
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)) =
    Module.finrank (ZMod q) (ContinuousTraceZeroAdjointH1 σ hσ) +
      Module.finrank (ZMod q) (rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m) +
      Module.finrank (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ
        (rationalArithmeticGeometricTraceProductCondition a q ha σ hσ p m)) at hb
  omega

end
end Dubon2026
