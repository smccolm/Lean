import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.Submodule.Equiv

/-! DUB-17/18 -> primitive determinant -> transfer the actual Weil pairing
through the existing specialization on its invariant projector image.
The pairing target is kept unchanged; no scalar-valued replacement is used. -/
namespace Dubon2026
noncomputable section
variable {E V W Z : Type*} [Field E]
variable [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]
variable [AddCommGroup Z] [Module E Z]

theorem image_specialization_section_intertwine
    (π : V →ₗ[E] W) (Q : Module.End E V) (e : Q.range ≃ₗ[E] W)
    (he : ∀ x, e x = π x.val) (G : Module.End E V) (M : Module.End E W)
    (hc : Commute G Q) (hπ : ∀ x, π (G x) = M (π x)) (x : W) :
    G (e.symm x).val = (e.symm (M x)).val := by
  have hz : G (e.symm x).val ∈ Q.range := by
    obtain ⟨v, hv⟩ := (e.symm x).property
    exact ⟨G v, (congrArg (fun T : Module.End E V => T v) hc.eq).symm.trans
      (congrArg G hv)⟩
  have hx : π (e.symm x).val = x := (he (e.symm x)).symm.trans (e.apply_symm_apply x)
  have hh : e ⟨G (e.symm x).val, hz⟩ = M x :=
    (he _).trans ((hπ _).trans (congrArg M hx))
  exact congrArg (fun z : Q.range => z.val)
    (e.injective (hh.trans (e.apply_symm_apply (M x)).symm))

/-- The original pairing expressed through the prescribed image specialization. -/
def imageSpecializationPairing (B : V →ₗ[E] V →ₗ[E] Z)
    (Q : Module.End E V) (e : Q.range ≃ₗ[E] W) : W →ₗ[E] W →ₗ[E] Z :=
  (B.compl₁₂ Q.range.subtype Q.range.subtype).compl₁₂
    e.symm.toLinearMap e.symm.toLinearMap

theorem imageSpecializationPairing_injective (B : V →ₗ[E] V →ₗ[E] Z)
    (Q : Module.End E V) (e : Q.range ≃ₗ[E] W)
    (hB : Function.Injective (B.compl₁₂ Q.range.subtype Q.range.subtype)) :
    Function.Injective (imageSpecializationPairing B Q e) := by
  intro x y h
  apply e.symm.injective
  apply hB
  ext z
  have hz := congrArg (fun L : W →ₗ[E] Z => L (e z)) h
  change B (e.symm x).val z.val = B (e.symm y).val z.val
  change B (e.symm x).val (e.symm (e z)).val =
    B (e.symm y).val (e.symm (e z)).val at hz
  simpa only [e.symm_apply_apply] using hz

theorem imageSpecializationPairing_self (B : V →ₗ[E] V →ₗ[E] Z)
    (Q : Module.End E V) (e : Q.range ≃ₗ[E] W) (hB : ∀ x, B x x = 0) (x : W) :
    imageSpecializationPairing B Q e x x = 0 := hB (e.symm x).val

theorem imageSpecializationPairing_multiplier (B : V →ₗ[E] V →ₗ[E] Z)
    (π : V →ₗ[E] W) (Q : Module.End E V) (e : Q.range ≃ₗ[E] W)
    (he : ∀ x, e x = π x.val) (G : Module.End E V) (M : Module.End E W)
    (hc : Commute G Q) (hπ : ∀ x, π (G x) = M (π x)) (c : E)
    (hB : ∀ x y, B (G x) (G y) = c • B x y) (x y : W) :
    imageSpecializationPairing B Q e (M x) (M y) =
      c • imageSpecializationPairing B Q e x y := by
  change B (e.symm (M x)).val (e.symm (M y)).val =
    c • B (e.symm x).val (e.symm y).val
  rw [← image_specialization_section_intertwine π Q e he G M hc hπ x,
    ← image_specialization_section_intertwine π Q e he G M hc hπ y]
  exact hB _ _

end
end Dubon2026
