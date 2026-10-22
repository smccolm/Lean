import Dubon2026.SourceOriginalSlotRange
import Dubon2026.SourceLaurentExpansionOrders

/-! DUB-17/18 -> original torsion cardinality -> normalized cusp charts.
Invert the actual injective Laurent power-substitution homomorphism on
its proved range. This transports an existing embedding, preserving field
operations and deriving its exact order normalization.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section

/-- An embedding into the actual expansion range, with that expansion inverted. -/
def descendExpansion {F : Type*} [Field F] [Algebra ℂ F]
    (e : ℕ) [NeZero e] (ι : F →ₐ[ℂ] LaurentSeries ℂ)
    (hrange : ∀ f, ι f ∈ (qExpandAlgHom ℂ e).fieldRange) : F →ₐ[ℂ] LaurentSeries ℂ :=
  (AlgEquiv.ofInjectiveField (qExpandAlgHom ℂ e)).symm.toAlgHom.comp
    (ι.codRestrict (qExpandAlgHom ℂ e).range hrange)

theorem qExpand_descendExpansion {F : Type*} [Field F] [Algebra ℂ F]
    (e : ℕ) [NeZero e] (ι : F →ₐ[ℂ] LaurentSeries ℂ)
    (hrange : ∀ f, ι f ∈ (qExpandAlgHom ℂ e).fieldRange) (f : F) :
    qExpand ℂ e (descendExpansion e ι hrange f) = ι f := by
  let E := AlgEquiv.ofInjectiveField (qExpandAlgHom ℂ e)
  have h := congrArg (fun x : (qExpandAlgHom ℂ e).range => (x : LaurentSeries ℂ))
    (E.apply_symm_apply ⟨ι f, hrange f⟩)
  exact h

theorem descendExpansion_order {F : Type*} [Field F] [Algebra ℂ F]
    (e : ℕ) [NeZero e] (ι : F →ₐ[ℂ] LaurentSeries ℂ)
    (hrange : ∀ f, ι f ∈ (qExpandAlgHom ℂ e).fieldRange) (f : F) :
    (e : ℤ) * (descendExpansion e ι hrange f).order = (ι f).order := by
  rw [← laurent_order_qExpand, qExpand_descendExpansion]

theorem descendExpansion_apply_of_eq {F : Type*} [Field F] [Algebra ℂ F]
    (e : ℕ) [NeZero e] (ι : F →ₐ[ℂ] LaurentSeries ℂ)
    (hrange : ∀ f, ι f ∈ (qExpandAlgHom ℂ e).fieldRange) (f : F) (A : LaurentSeries ℂ)
    (h : ι f = qExpand ℂ e A) : descendExpansion e ι hrange f = A := by
  apply (qExpand ℂ e).injective
  rw [qExpand_descendExpansion, h]

end
end Dubon2026.SourceFunctionField
