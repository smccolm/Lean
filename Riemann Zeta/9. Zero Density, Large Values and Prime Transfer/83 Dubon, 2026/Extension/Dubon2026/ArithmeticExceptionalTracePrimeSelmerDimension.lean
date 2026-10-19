import Dubon2026.ArithmeticExceptionalTraceSelmerDimension

/-! Primewise numerical comparison for the original Selmer conditions.
The genuine exceptional product dimension is computed from its original
prime-local H1 spaces and specified subspaces. This supplies the local terms
in DUB-17's deformation comparison; arithmetic deformation choices remain to be realized. -/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)
  (C : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val))

private def conditionProductEquiv :
    rationalArithmeticTraceLocalConditionProduct a q ha σ hσ C ≃ₗ[ZMod q] (p : _) → C p where
  toFun x p := ⟨x.val p,
    (rationalArithmeticTraceLocalConditionProduct_mem_iff a q ha σ hσ C x.val).mp x.property p⟩
  invFun x := ⟨fun p => (x p).val,
    (rationalArithmeticTraceLocalConditionProduct_mem_iff a q ha σ hσ C _).mpr
      (fun p => (x p).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The specified original product condition has the sum of its actual local dimensions. -/
theorem rationalArithmeticTraceLocalConditionProduct_finrank :
    Module.finrank (ZMod q) (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ C) =
      ∑ p, Module.finrank (ZMod q) (C p) := by
  haveI (p : rationalArithmeticExceptionalPrimes a ha) :
      Finite (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) :=
    rationalPrimeTraceZeroAdjointH1_finite p.val.val p.val.property q
      (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
  haveI (p : rationalArithmeticExceptionalPrimes a ha) : Module.Finite (ZMod q) (C p) :=
    Module.Finite.of_finite
  exact (conditionProductEquiv a q ha σ hσ C).finrank_eq.trans (Module.finrank_pi_fintype _)

variable (hqa : (q : 𝓞 ℚ) ∣ a) (hq2 : q ≠ 2) (hn : (Fintype.card ι : ZMod q) ≠ 0)
include hq2 hn

/-- The actual primal-minus-dual Selmer dimension changes by exactly the sum
of the primewise local dimension changes, for the same original representation. -/
theorem rationalArithmeticTracePrimeSelmer_finrank_comparison
    (D : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val)) :
    Module.finrank (ZMod q) (rationalArithmeticTraceSelmer a q ha σ hσ C) +
      Module.finrank (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ
        (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ D)) +
      ∑ p, Module.finrank (ZMod q) (D p) =
    Module.finrank (ZMod q) (rationalArithmeticTraceSelmer a q ha σ hσ D) +
      Module.finrank (ZMod q) (rationalArithmeticTraceDualSelmer a q hqa ha σ hσ
        (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ C)) +
      ∑ p, Module.finrank (ZMod q) (C p) := by
  have he := rationalArithmeticTraceSelmer_finrank_comparison a q hqa ha σ hσ
    (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ C) hq2 hn
    (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ D)
  rw [rationalArithmeticTraceLocalConditionProduct_finrank,
    rationalArithmeticTraceLocalConditionProduct_finrank] at he
  exact he

end
end Dubon2026
