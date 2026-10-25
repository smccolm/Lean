import Dubon2026.SourceCellPolygonWordChains
import Dubon2026.SourceRadialFundamentalCycleSystem

/-! DUB-17/18 -> original Abel-Jacobi -> jump-to-period formula.
Reindex an actual closed integer edge chain by the constructed fundamental
cycles and its vector of integrals. A scalar lift preserves the universe of
the universal circulation theorem without restricting its family quantifier.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
universe u
noncomputable section
variable {X : Type*} [TopologicalSpace X] {κ : Type*} {𝒟 : RadialCellDissection X}

/-- The vector of actual edge-integral sums along an integer fundamental cycle. -/
noncomputable def zv (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (I : 𝒟.ιE → κ → ℂ) (l : 𝒟.ιE) : κ → ℂ :=
  ∑ e, (Z l e : ℂ) • I e

theorem integer_decomposition_of_lift (D : RadialCellDissection X)
    {T : Finset D.ιE} {Z : D.ιE → D.ιE → ℤ}
    (hZ : ∀ f : D.ιE → ULift.{u} ℤ,
      (∀ w, (∑ e with (D.ends e).2 = w, f e) = ∑ e with (D.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j) :
    ∀ f : D.ιE → ℤ,
      (∀ w, (∑ e with (D.ends e).2 = w, f e) = ∑ e with (D.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j := by
  intro f hf e
  have he := hZ (fun e => (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).symm (f e)) (by
    intro w
    rw [← map_sum, ← map_sum, hf w]) e
  have hh := congrArg (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ) he
  simpa only [map_sum, map_zsmul, AddEquiv.apply_symm_apply] using hh

theorem sum_chain_smul {𝒯 : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : ∀ p : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, p e) = ∑ e with (𝒟.ends e).1 = w, p e) →
      ∀ e, p e = ∑ j ∈ 𝒯ᶜ, Z j e • p j)
    (p : 𝒟.ιE → ℤ)
    (hp : ∀ w, (∑ e with (𝒟.ends e).2 = w, p e) = ∑ e with (𝒟.ends e).1 = w, p e)
    (I : 𝒟.ιE → κ → ℂ) :
    ∑ f, (p f : ℂ) • I f = ∑ l ∈ 𝒯ᶜ, (p l : ℂ) • zv Z I l := by
  classical
  have hdec : ∀ f, p f = ∑ l ∈ 𝒯ᶜ, Z l f • p l := hZ p hp
  calc ∑ f, (p f : ℂ) • I f = ∑ f, ∑ l ∈ 𝒯ᶜ, ((Z l f * p l : ℤ) : ℂ) • I f := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        rw [hdec f]
        push_cast
        simp
    _ = ∑ l ∈ 𝒯ᶜ, ∑ f, ((Z l f * p l : ℤ) : ℂ) • I f := Finset.sum_comm
    _ = ∑ l ∈ 𝒯ᶜ, (p l : ℂ) • zv Z I l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [zv, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun f _ => ?_
        push_cast
        rw [mul_comm]

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
