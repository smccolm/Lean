import Dubon2026.FiniteFreeHopfPointModelProduct
import Dubon2026.FiniteFreeHopfPointModelEquiv
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin

/-! # Actual finite nonempty products of the original modeled Galois module -/

namespace Dubon2026
noncomputable section

variable {G V : Type*} [Group G] [CommGroup V]

/-- The original group acts componentwise on the actual indexed product of its original module. -/
def galoisModulePiAction (J : Type*) (ρ : G →* MulAut V) : G →* MulAut (J → V) where
  toFun g := MulEquiv.piCongrRight (fun _ : J => ρ g)
  map_one' := by
    apply MulEquiv.ext
    intro v
    funext j
    exact congrArg (fun e : MulAut V => e (v j)) ρ.map_one
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    funext j
    exact congrArg (fun e : MulAut V => e (v j)) (ρ.map_mul g h)

/-- The indexed action evaluates at the same original coordinate and original group element. -/
theorem galoisModulePiAction_apply (J : Type*) (ρ : G →* MulAut V)
    (g : G) (v : J → V) (j : J) :
    galoisModulePiAction J ρ g v j = ρ g (v j) := by
  rfl

universe u
variable {R F K W : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K] [CommGroup W]
  {τ : (K ≃ₐ[F] K) →* MulAut W}

/-- Construct every positive finite power model from the original model and actual tensor-coordinate binary products. -/
def finiteFreeHopfPointModelPositivePower
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K W τ) (n : ℕ) :
    FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Fin (n + 1) → W)
      (galoisModulePiAction (Fin (n + 1)) τ) := by
  induction n with
  | zero =>
    let e : W ≃* (Fin 1 → W) := {
      toFun := fun w _ => w
      invFun := fun v => v 0
      left_inv := fun _ => rfl
      right_inv := fun v => funext (fun i => congrArg v (Subsingleton.elim 0 i))
      map_mul' := fun _ _ => rfl }
    exact finiteFreeHopfPointModelEquiv m e (fun _ _ => rfl)
  | succ n ih =>
    let e : W × (Fin (n + 1) → W) ≃* (Fin (n + 1 + 1) → W) := {
      toFun := fun z => Fin.cases z.1 z.2
      invFun := fun v => (v 0, fun j => v j.succ)
      left_inv := by intro z; rfl
      right_inv := by
        intro v
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      map_mul' := by
        intro z w
        funext j
        exact Fin.cases rfl (fun _ => rfl) j }
    apply finiteFreeHopfPointModelEquiv (finiteFreeHopfPointModelProduct m ih) e
    intro g z
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

/-- Every positive finite power of the original module has the derived actual model. -/
theorem finiteFreeHopfPointModel_positivePower_exists
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K W τ) (n : ℕ) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Fin (n + 1) → W)
      (galoisModulePiAction (Fin (n + 1)) τ)) := by
  exact ⟨finiteFreeHopfPointModelPositivePower m n⟩

/-- An actual finite nonempty index equivalence transports the genuine positive-power model to the original indexed product, retaining its coordinatewise Galois action. -/
def finiteFreeHopfPointModelFinitePi (J : Type u) [Fintype J] [Nonempty J]
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K W τ) :
    FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (J → W) (galoisModulePiAction J τ) := by
  have hcard : Fintype.card J = (Fintype.card J - 1) + 1 :=
    (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)).symm
  let e := (Fintype.equivFin J).trans (finCongr hcard)
  let E : (Fin ((Fintype.card J - 1) + 1) → W) ≃* (J → W) := {
    toFun := fun v j => v (e j)
    invFun := fun w i => w (e.symm i)
    left_inv := fun v => funext (fun i => congrArg v (e.apply_symm_apply i))
    right_inv := fun w => funext (fun j => congrArg w (e.symm_apply_apply j))
    map_mul' := fun _ _ => rfl }
  exact finiteFreeHopfPointModelEquiv
    (finiteFreeHopfPointModelPositivePower m (Fintype.card J - 1)) E (fun _ _ => rfl)

/-- The actual finite indexed product of a modeled module has a model built from genuine coordinate products. -/
theorem finiteFreeHopfPointModel_finitePi_exists (J : Type u) [Fintype J] [Nonempty J]
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K W τ) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (J → W) (galoisModulePiAction J τ)) := by
  exact ⟨finiteFreeHopfPointModelFinitePi J m⟩

end
end Dubon2026
