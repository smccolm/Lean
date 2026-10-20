import Dubon2026.SourcePeriodMap
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! The actual cusp periods define the parabolic analytic cohomology class.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> modular Galois association -> the analytic/etale comparison
for the original modular form. Reuse the constructed convergent period map,
its exact binary coefficient action and native low-degree group cohomology.
This supplies the analytic class. SourcePeriodCohomologyInjective proves its
injectivity; geometric comparison, Frobenius traces and Galois action remain open.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup MvPolynomial MulOpposite SourceModularSymbols
open scoped MatrixGroups

variable (Γ : Subgroup SL(2, ℤ)) (w : ℕ)

/-- The dual of the original binary coefficient representation, restricted to the actual level. -/
abbrev sourcePeriodDualRep : Rep ℂ Γ :=
  Rep.of ((sourceModularBinaryFormSLRep ℂ w).dual.comp Γ.subtype)

variable {Γ w}

/-- The original dual coefficient action is precomposition by the right matrix substitution. -/
theorem sourcePeriodDualRep_apply (γ : Γ)
    (L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ w))
    (P : homogeneousSubmodule (Fin 2) ℂ w) :
    (sourcePeriodDualRep Γ w).ρ γ L P =
      L (sourceModularBinaryFormRep ℂ w (op (γ.val : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
  change L (sourceModularBinaryFormSLRep ℂ w γ.val⁻¹ P) = _
  rw [sourceModularBinaryFormSLRep_apply, inv_inv]

variable [Γ.FiniteIndex] {k : ℤ}

/-- The linear functional of actual periods from the second cusp to the first cusp. -/
def sourcePeriodBetween (f : CuspForm (Γ.map (mapGL ℝ)) k) (hk : k = w + 2)
    (α β : OnePoint ℚ) : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ w) :=
  (periodMap ℂ Γ hk f).comp (symbol Γ α β)

/-- This functional evaluates to the already constructed convergent cusp integral. -/
theorem sourcePeriodBetween_apply (f : CuspForm (Γ.map (mapGL ℝ)) k) (hk : k = w + 2)
    (α β : OnePoint ℚ) (P : homogeneousSubmodule (Fin 2) ℂ w) :
    sourcePeriodBetween f hk α β P = sourceCuspIntegral (periodIntegrand f P) β α :=
  periodMap_symbol hk f α β P

/-- Adjacent actual periods add, with their original orientation. -/
theorem sourcePeriodBetween_add (f : CuspForm (Γ.map (mapGL ℝ)) k) (hk : k = w + 2)
    (α β δ : OnePoint ℚ) :
    sourcePeriodBetween f hk α β + sourcePeriodBetween f hk β δ =
      sourcePeriodBetween f hk α δ := by
  simp only [sourcePeriodBetween, ← LinearMap.comp_add, symbol_add_symbol]

/-- Moving both cusps acts through the original dual binary representation. -/
theorem sourcePeriodBetween_equivariant (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (hk : k = w + 2) (γ : Γ) (α β : OnePoint ℚ) :
    sourcePeriodBetween f hk (mapGL ℚ γ.val • α) (mapGL ℚ γ.val • β) =
      (sourcePeriodDualRep Γ w).ρ γ (sourcePeriodBetween f hk α β) := by
  ext P
  rw [sourcePeriodDualRep_apply]
  simp only [sourcePeriodBetween, LinearMap.comp_apply, symbol_mapGL_smul Γ γ.property]

/-- The cocycle of the original cusp form, based at an arbitrary rational cusp. -/
def sourcePeriodCocycle (f : CuspForm (Γ.map (mapGL ℝ)) k) (hk : k = w + 2)
    (α : OnePoint ℚ) : groupCohomology.cocycles₁ (sourcePeriodDualRep Γ w) :=
  ⟨fun γ => sourcePeriodBetween f hk (mapGL ℚ γ.val • α) α, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro γ δ
    change sourcePeriodBetween f hk (mapGL ℚ (γ.val * δ.val) • α) α = _
    rw [map_mul, mul_smul, ← sourcePeriodBetween_equivariant]
    exact (sourcePeriodBetween_add f hk _ _ _).symm⟩

/-- The actual cocycle value is the period from the base cusp to its image. -/
theorem sourcePeriodCocycle_apply (f : CuspForm (Γ.map (mapGL ℝ)) k) (hk : k = w + 2)
    (α : OnePoint ℚ) (γ : Γ) (P : homogeneousSubmodule (Fin 2) ℂ w) :
    sourcePeriodCocycle f hk α γ P =
      sourceCuspIntegral (periodIntegrand f P) α (mapGL ℚ γ.val • α) :=
  sourcePeriodBetween_apply f hk _ _ P

/-- Changing the base cusp changes the actual cocycle by the explicit period coboundary. -/
theorem sourcePeriodCocycle_change_base (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (hk : k = w + 2) (α β : OnePoint ℚ) (γ : Γ) :
    sourcePeriodCocycle f hk β γ - sourcePeriodCocycle f hk α γ =
      (sourcePeriodDualRep Γ w).ρ γ (sourcePeriodBetween f hk β α) -
        sourcePeriodBetween f hk β α := by
  change sourcePeriodBetween f hk (mapGL ℚ γ.val • β) β -
    sourcePeriodBetween f hk (mapGL ℚ γ.val • α) α = _
  rw [← sourcePeriodBetween_equivariant]
  have h₁ := sourcePeriodBetween_add f hk (mapGL ℚ γ.val • β) β α
  have h₂ := sourcePeriodBetween_add f hk (mapGL ℚ γ.val • β) (mapGL ℚ γ.val • α) α
  exact sub_eq_sub_iff_add_eq_add.mpr (h₁.trans h₂.symm)

/-- On every rational cusp stabilizer the original cocycle is the displayed coboundary. -/
theorem sourcePeriodCocycle_parabolic (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (hk : k = w + 2) (α β : OnePoint ℚ) :
    ∃ b : sourcePeriodDualRep Γ w,
      ∀ γ : Γ, mapGL ℚ γ.val • β = β →
        sourcePeriodCocycle f hk α γ = (sourcePeriodDualRep Γ w).ρ γ b - b := by
  refine ⟨sourcePeriodBetween f hk α β, ?_⟩
  intro γ hγ
  have h := sourcePeriodCocycle_change_base f hk β α γ
  have hz : sourcePeriodCocycle f hk β γ = 0 := by
    change (periodMap ℂ Γ hk f).comp (symbol Γ (mapGL ℚ γ.val • β) β) = 0
    rw [hγ, symbol_self, LinearMap.comp_zero]
  simpa only [hz, sub_zero] using h

/-- The analytic group-cohomology class of the original cusp form and its actual periods. -/
def sourcePeriodH1 (f : CuspForm (Γ.map (mapGL ℝ)) k) (hk : k = w + 2)
    (α : OnePoint ℚ) : groupCohomology.H1 (sourcePeriodDualRep Γ w) :=
  groupCohomology.H1π _ (sourcePeriodCocycle f hk α)

/-- The original analytic cohomology class does not depend on the chosen rational base cusp. -/
theorem sourcePeriodH1_base_independent (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (hk : k = w + 2) (α β : OnePoint ℚ) :
    sourcePeriodH1 f hk β = sourcePeriodH1 f hk α := by
  apply (groupCohomology.H1π_eq_iff _ _).mpr
  refine ⟨sourcePeriodBetween f hk β α, ?_⟩
  funext γ
  exact (sourcePeriodCocycle_change_base f hk α β γ).symm

end
end Dubon2026
