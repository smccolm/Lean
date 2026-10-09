import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Antidiagonal

/-! # Genuine splitting of variables in multivariate formal power series -/

namespace Dubon2026

noncomputable section
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

/-- Split the actual exponent family into its two original variable sets. -/
def splitPowerSeriesVariables (f : MvPowerSeries (σ ⊕ τ) R) :
    MvPowerSeries σ (MvPowerSeries τ R) :=
  fun d e => f (d.sumElim e)

/-- Splitting variables retains every literal original coefficient. -/
theorem splitPowerSeriesVariables_coeff (f : MvPowerSeries (σ ⊕ τ) R)
    (d : σ →₀ ℕ) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.coeff d (splitPowerSeriesVariables f)) =
      MvPowerSeries.coeff (d.sumElim e) f := rfl

/-- Actual antidiagonal convolution is preserved under splitting the original variables. -/
theorem splitPowerSeriesVariables_mul (f g : MvPowerSeries (σ ⊕ τ) R) :
    splitPowerSeriesVariables (f * g) =
      splitPowerSeriesVariables f * splitPowerSeriesVariables g := by
  classical
  apply MvPowerSeries.ext
  intro d
  apply MvPowerSeries.ext
  intro e
  rw [splitPowerSeriesVariables_coeff]
  simp only [MvPowerSeries.coeff_mul, map_sum, splitPowerSeriesVariables_coeff]
  rw [← Finsupp.image_sumElim_product_antidiagonal, Finset.sum_image]
  · rw [Finset.sum_product]
  · intro a _ b _ hab
    rcases a with ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩⟩
    rcases b with ⟨⟨b₁, b₂⟩, ⟨b₃, b₄⟩⟩
    have h₁ := congrArg (fun p => p.1) hab
    have h₂ := congrArg (fun p => p.2) hab
    have ha₁ := congrArg
      (fun q : (σ ⊕ τ) →₀ ℕ => q.comapDomain Sum.inl Sum.inl_injective.injOn) h₁
    have ha₃ := congrArg
      (fun q : (σ ⊕ τ) →₀ ℕ => q.comapDomain Sum.inr Sum.inr_injective.injOn) h₁
    have ha₂ := congrArg
      (fun q : (σ ⊕ τ) →₀ ℕ => q.comapDomain Sum.inl Sum.inl_injective.injOn) h₂
    have ha₄ := congrArg
      (fun q : (σ ⊕ τ) →₀ ℕ => q.comapDomain Sum.inr Sum.inr_injective.injOn) h₂
    simp only [Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim] at ha₁ ha₂ ha₃ ha₄
    exact Prod.ext (Prod.ext ha₁ ha₂) (Prod.ext ha₃ ha₄)

/-- The actual formal series ring on a disjoint union is the corresponding iterated formal series ring. -/
def splitPowerSeriesVariablesEquiv :
    MvPowerSeries (σ ⊕ τ) R ≃+* MvPowerSeries σ (MvPowerSeries τ R) where
  toFun := splitPowerSeriesVariables
  invFun f d := f (d.comapDomain Sum.inl Sum.inl_injective.injOn)
    (d.comapDomain Sum.inr Sum.inr_injective.injOn)
  left_inv f := by
    apply MvPowerSeries.ext
    intro d
    change f ((d.comapDomain Sum.inl Sum.inl_injective.injOn).sumElim
      (d.comapDomain Sum.inr Sum.inr_injective.injOn)) = f d
    rw [Finsupp.comapDomain_sumElim_comapDomain]
  right_inv f := by
    apply MvPowerSeries.ext
    intro d
    apply MvPowerSeries.ext
    intro e
    change f ((d.sumElim e).comapDomain Sum.inl Sum.inl_injective.injOn)
      ((d.sumElim e).comapDomain Sum.inr Sum.inr_injective.injOn) = f d e
    rw [Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
  map_mul' := splitPowerSeriesVariables_mul
  map_add' _ _ := rfl

end
end Dubon2026
