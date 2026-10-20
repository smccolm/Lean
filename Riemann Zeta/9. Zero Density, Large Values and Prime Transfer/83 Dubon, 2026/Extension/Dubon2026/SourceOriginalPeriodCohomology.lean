import Dubon2026.SourcePeriodCocycle
import Dubon2026.PrimitiveCuspForms

/-! Original Gamma0 cusp forms in actual analytic parabolic cohomology.
DUB-17/18 -> higher symmetric-power continuation -> modular Galois association
-> comparison with the original analytic form. The actual period cocycle gives
a complex-linear H1 map and its original primitive-form consumer. Its injectivity
is proved in SourcePeriodCohomologyInjective. Betti/etale comparison and modular
Galois action remain open.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup SourceModularSymbols OnePoint
open scoped MatrixGroups

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {w : ℕ}

/-- The original analytic period cocycle depends complex-linearly on the cusp form. -/
def sourcePeriodCocycleLinear (hk : k = w + 2) (α : OnePoint ℚ) :
    CuspForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ]
      groupCohomology.cocycles₁ (sourcePeriodDualRep Γ w) where
  toFun f := sourcePeriodCocycle f hk α
  map_add' f g := by
    apply groupCohomology.cocycles₁_ext
    intro γ
    apply LinearMap.ext
    intro P
    change (periodMap ℂ Γ hk (f + g))
        (symbol (R := ℂ) (w := w) Γ (mapGL ℚ γ.val • α) α P) =
      (periodMap ℂ Γ hk f) (symbol (R := ℂ) (w := w) Γ (mapGL ℚ γ.val • α) α P) +
        (periodMap ℂ Γ hk g) (symbol (R := ℂ) (w := w) Γ (mapGL ℚ γ.val • α) α P)
    rw [map_add, LinearMap.add_apply]
  map_smul' c f := by
    apply groupCohomology.cocycles₁_ext
    intro γ
    apply LinearMap.ext
    intro P
    change (periodMap ℂ Γ hk (c • f))
        (symbol (R := ℂ) (w := w) Γ (mapGL ℚ γ.val • α) α P) =
      c • (periodMap ℂ Γ hk f) (symbol (R := ℂ) (w := w) Γ (mapGL ℚ γ.val • α) α P)
    rw [_root_.map_smul, LinearMap.smul_apply]

/-- The actual period map to analytic group cohomology is complex-linear. -/
def sourcePeriodCohomologyLinear (hk : k = w + 2) (α : OnePoint ℚ) :
    CuspForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ] groupCohomology.H1 (sourcePeriodDualRep Γ w) :=
  (groupCohomology.H1π _).hom.comp (sourcePeriodCocycleLinear hk α)

/-- The linear H1 map is the class of the original period cocycle. -/
theorem sourcePeriodCohomologyLinear_apply (hk : k = w + 2) (α : OnePoint ℚ)
    (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    sourcePeriodCohomologyLinear hk α f = sourcePeriodH1 f hk α := rfl

/-- Changing the rational base cusp preserves the entire original linear cohomology map. -/
theorem sourcePeriodCohomologyLinear_base_independent (hk : k = w + 2) (α β : OnePoint ℚ) :
    (sourcePeriodCohomologyLinear (Γ := Γ) hk β) = sourcePeriodCohomologyLinear hk α := by
  ext f
  exact sourcePeriodH1_base_independent f hk α β

variable (Q : ℕ) [NeZero Q] (k : ℤ)

/-- The original Gamma0 period class at every source weight, with its literal weight-minus-two coefficients. -/
def sourceOriginalPeriodCohomology (hk : 2 ≤ k) :
    CuspForm ((Gamma0 Q).map (mapGL ℝ)) k →ₗ[ℂ]
      groupCohomology.H1 (sourcePeriodDualRep (Gamma0 Q) (k - 2).toNat) :=
  sourcePeriodCohomologyLinear (Γ := Gamma0 Q) (k := k) (w := (k - 2).toNat) (by omega) ∞

/-- An actual source primitive form supplies its analytic H1 class through the original cusp integrals; the same cocycle is principal on every rational cusp stabilizer. -/
theorem sourcePrimitive_periodCohomology_realization
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    ∃ c : groupCohomology.cocycles₁ (sourcePeriodDualRep (Gamma0 Q) (k - 2).toNat),
      groupCohomology.H1π _ c = sourceOriginalPeriodCohomology Q k hk f.toCuspForm ∧
      (∀ (γ : Gamma0 Q) (P : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (k - 2).toNat),
        c γ P = sourceCuspIntegral (periodIntegrand f.toCuspForm P) ∞ (mapGL ℚ γ.val • ∞)) ∧
      ∀ β : OnePoint ℚ, ∃ b : sourcePeriodDualRep (Gamma0 Q) (k - 2).toNat,
        ∀ γ : Gamma0 Q, mapGL ℚ γ.val • β = β →
          c γ = (sourcePeriodDualRep (Gamma0 Q) (k - 2).toNat).ρ γ b - b := by
  have hw : k = ((k - 2).toNat : ℤ) + 2 := by omega
  exact ⟨sourcePeriodCocycle f.toCuspForm hw ∞, rfl,
    sourcePeriodCocycle_apply f.toCuspForm hw ∞,
    sourcePeriodCocycle_parabolic f.toCuspForm hw ∞⟩

end
end Dubon2026
