import Dubon2026.ArithmeticExceptionalTraceSelmerExactness

/-! Primewise conditions on the original exceptional trace H1 product.
The original scalar cup at each prime is retained. The actual global
dual Selmer condition is proved equivalent to these separate local
orthogonality tests, for DUB-17's local-condition patching input. -/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (ha : a ≠ 0)
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)
  (L : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q σ hσ p.val))

/-- The specified local conditions in the actual exceptional H1 product. -/
def rationalArithmeticTraceLocalConditionProduct :
    Submodule (ZMod q) (RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :=
  Submodule.pi Set.univ L

/-- Product membership is exactly the prescribed condition at every original prime. -/
theorem rationalArithmeticTraceLocalConditionProduct_mem_iff
    (x : RationalArithmeticExceptionalTraceH1 a q ha σ hσ) :
    x ∈ rationalArithmeticTraceLocalConditionProduct a q ha σ hσ L ↔ ∀ p, x p ∈ L p := by
  simp only [rationalArithmeticTraceLocalConditionProduct, Submodule.mem_pi, Set.mem_univ, forall_const]

/-- The actual primal Selmer classes satisfy the prescribed original primewise conditions. -/
def rationalArithmeticTraceSelmer : Submodule (ZMod q) (ContinuousTraceZeroAdjointH1 σ hσ) :=
  (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ L).comap
    (rationalArithmeticTraceH1Localization a q ha σ hσ)

/-- The primal Selmer definition consumes the literal original restriction at each prime. -/
theorem rationalArithmeticTraceSelmer_mem_iff
    (x : ContinuousTraceZeroAdjointH1 σ hσ) :
    x ∈ rationalArithmeticTraceSelmer a q ha σ hσ L ↔
      ∀ p, rationalArithmeticTraceH1Localization a q ha σ hσ x p ∈ L p := by
  exact rationalArithmeticTraceLocalConditionProduct_mem_iff a q ha σ hσ L _

private theorem condition_single_mem
    (p : rationalArithmeticExceptionalPrimes a ha)
    (y : rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) (hy : y ∈ L p) :
    Pi.single p y ∈ rationalArithmeticTraceLocalConditionProduct a q ha σ hσ L := by
  classical
  apply (rationalArithmeticTraceLocalConditionProduct_mem_iff a q ha σ hσ L _).mpr
  intro r
  by_cases hr : r = p
  · subst r
    simpa only [Pi.single_eq_same] using hy
  · simpa only [Pi.single_eq_of_ne hr] using (L r).zero_mem

variable (hqa : (q : 𝓞 ℚ) ∣ a)

private theorem actual_pairing_single
    (x : RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ)
    (p : rationalArithmeticExceptionalPrimes a ha)
    (y : rationalArithmeticPrimeTraceH1Module a q σ hσ p.val) :
    rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ x (Pi.single p y) =
      rationalArithmeticPrimeTraceH1ScalarCup a q hqa p.val.val p.val.property
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
        (x p) y := by
  let B (r : ↥(rationalArithmeticExceptionalPrimes a ha)) :
      rationalArithmeticPrimeTraceDualH1Module a q σ hσ r.val →ₗ[ZMod q]
        rationalArithmeticPrimeTraceH1Module a q σ hσ r.val →ₗ[ZMod q] ZMod q :=
    rationalArithmeticPrimeTraceH1ScalarCup a q hqa r.val.val r.val.property
      (σ.comp (rationalPrimeArithmeticRestriction a r.val.val r.val.property).toMonoidHom)
      (hσ.comp (rationalPrimeArithmeticRestriction a r.val.val r.val.property).continuous)
  change (∑ r, (B r).compl₁₂ (LinearMap.proj r) (LinearMap.proj r)) x (Pi.single p y) = B p (x p) y
  simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single p]
  · rw [Pi.single_eq_same]
  · intro r _ hr
    rw [Pi.single_eq_of_ne hr]
    exact map_zero _
  · simp

private theorem product_orthogonality_iff
    (x : RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ) :
    (∀ y ∈ rationalArithmeticTraceLocalConditionProduct a q ha σ hσ L,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ x y = 0) ↔
    ∀ (p : rationalArithmeticExceptionalPrimes a ha)
      (y : rationalArithmeticPrimeTraceH1Module a q σ hσ p.val), y ∈ L p →
      rationalArithmeticPrimeTraceH1ScalarCup a q hqa p.val.val p.val.property
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
        (x p) y = 0 := by
  constructor
  · intro h p y hy
    have hs := h (Pi.single p y) (condition_single_mem a q ha σ hσ L p y hy)
    exact (actual_pairing_single a q ha σ hσ hqa x p y).symm.trans hs
  · intro h y hy
    rw [rationalArithmeticExceptionalTracePairing_apply]
    apply Finset.sum_eq_zero
    intro p _
    exact h p (y p) ((rationalArithmeticTraceLocalConditionProduct_mem_iff a q ha σ hσ L y).mp hy p)

/-- The actual dual Selmer condition is exactly original scalar-cup
orthogonality to each specified primewise local condition. -/
theorem rationalArithmeticTraceDualSelmer_primewise_iff
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ) :
    x ∈ rationalArithmeticTraceDualSelmer a q hqa ha σ hσ
      (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ L) ↔
    ∀ (p : rationalArithmeticExceptionalPrimes a ha)
      (y : rationalArithmeticPrimeTraceH1Module a q σ hσ p.val), y ∈ L p →
      rationalArithmeticPrimeTraceH1ScalarCup a q hqa p.val.val p.val.property
        (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom)
        (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous)
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ x p) y = 0 := by
  exact (rationalArithmeticTraceDualSelmer_mem_iff a q hqa ha σ hσ
    (rationalArithmeticTraceLocalConditionProduct a q ha σ hσ L) x).trans
      (product_orthogonality_iff a q ha σ hσ L hqa
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ x))

end
end Dubon2026
