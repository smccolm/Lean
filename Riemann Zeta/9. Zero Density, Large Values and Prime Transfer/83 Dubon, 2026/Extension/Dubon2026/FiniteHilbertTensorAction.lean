import Dubon2026.FiniteHilbertTensor
import Mathlib.RepresentationTheory.Basic

/-! # Genuine finite tensor maps and the external product of the original factor actions -/

namespace Dubon2026

noncomputable section
open scoped TensorProduct

/-- The actual tensor of a finite family of original linear endomorphisms. -/
def finiteHilbertTensorMap : {n : ℕ} → (V : Fin n → ComplexInnerCarrier) →
    (∀ i, V i →ₗ[ℂ] V i) → (finiteHilbertTensor n V →ₗ[ℂ] finiteHilbertTensor n V)
  | 0, _, _ => LinearMap.id
  | n + 1, V, A => TensorProduct.map (A 0)
      (finiteHilbertTensorMap (fun i : Fin n => V i.succ) (fun i => A i.succ))

/-- The genuine finite tensor map acts on pure tensors by precisely the original factor maps. -/
theorem finiteHilbertTensorMap_pure {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    (A : ∀ i, V i →ₗ[ℂ] V i) (x : ∀ i, V i) :
    finiteHilbertTensorMap V A (finiteHilbertPureTensor V x) =
      finiteHilbertPureTensor V (fun i => A i (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.map (A 0) (finiteHilbertTensorMap (fun i : Fin n => V i.succ) (fun i => A i.succ))
      (x 0 ⊗ₜ[ℂ] finiteHilbertPureTensor (fun i : Fin n => V i.succ) (fun i => x i.succ)) = _
    rw [TensorProduct.map_tmul, ih]
    rfl

/-- The tensor of genuine identity factor maps is the actual finite tensor identity. -/
theorem finiteHilbertTensorMap_id {n : ℕ} (V : Fin n → ComplexInnerCarrier) :
    finiteHilbertTensorMap V (fun _ => LinearMap.id : ∀ i, V i →ₗ[ℂ] V i) = LinearMap.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.map LinearMap.id
      (finiteHilbertTensorMap (fun i : Fin n => V i.succ) (fun _ => LinearMap.id)) = LinearMap.id
    rw [ih, TensorProduct.map_id]

/-- The actual finite tensor construction preserves composition of all original factor maps. -/
theorem finiteHilbertTensorMap_comp {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    (A B : ∀ i, V i →ₗ[ℂ] V i) :
    finiteHilbertTensorMap V (fun i => (A i).comp (B i)) =
      (finiteHilbertTensorMap V A).comp (finiteHilbertTensorMap V B) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.map ((A 0).comp (B 0))
      (finiteHilbertTensorMap (fun i : Fin n => V i.succ) (fun i => (A i.succ).comp (B i.succ))) =
      (TensorProduct.map (A 0) (finiteHilbertTensorMap (fun i : Fin n => V i.succ) (fun i => A i.succ))).comp
        (TensorProduct.map (B 0) (finiteHilbertTensorMap (fun i : Fin n => V i.succ) (fun i => B i.succ)))
    rw [ih, TensorProduct.map_comp]

/-- The genuine external tensor representation of a finite family of original group representations. -/
def finiteHilbertTensorRepresentation {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    {G : Fin n → Type} [∀ i, Group (G i)] (ρ : ∀ i, Representation ℂ (G i) (V i)) :
    Representation ℂ (∀ i, G i) (finiteHilbertTensor n V) where
  toFun g := finiteHilbertTensorMap V (fun i => ρ i (g i))
  map_one' := by
    change finiteHilbertTensorMap V (fun i => ρ i 1) = LinearMap.id
    simp only [map_one]
    exact finiteHilbertTensorMap_id V
  map_mul' a b := by
    change finiteHilbertTensorMap V (fun i => ρ i (a i * b i)) =
      (finiteHilbertTensorMap V (fun i => ρ i (a i))).comp
        (finiteHilbertTensorMap V (fun i => ρ i (b i)))
    simp only [map_mul]
    exact finiteHilbertTensorMap_comp V _ _

/-- The actual finite external tensor action has the original coordinatewise pure-orbit multiplication law. -/
theorem finiteHilbertTensorRepresentation_orbit_action {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    {G : Fin n → Type} [∀ i, Group (G i)] (ρ : ∀ i, Representation ℂ (G i) (V i))
    (y : ∀ i, V i) (a b : ∀ i, G i) :
    finiteHilbertTensorRepresentation V ρ b (finiteHilbertPureTensor V (fun i => ρ i (a i) (y i))) =
      finiteHilbertPureTensor V (fun i => ρ i ((b * a) i) (y i)) := by
  change finiteHilbertTensorMap V (fun i => ρ i (b i))
    (finiteHilbertPureTensor V (fun i => ρ i (a i) (y i))) = _
  rw [finiteHilbertTensorMap_pure]
  congr 1
  funext i
  exact (Module.End.mul_apply (ρ i (b i)) (ρ i (a i)) (y i)).symm.trans
    (congrArg (fun T : Module.End ℂ (V i) => T (y i)) (map_mul (ρ i) (b i) (a i)).symm)

end
end Dubon2026
