import Mathlib.NumberTheory.ModularForms.QExpansion
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
namespace P2MW.S_UpperHalfPlane_eq_of_forall_qCoeff_eq

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

namespace W2WsF

theorem hasSum_qCoeff {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qExpansion one_pos hper hhol hbdd τ

end W2WsF

theorem solution {f g : UpperHalfPlane → ℂ} (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hfhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hfbdd : UpperHalfPlane.IsBoundedAtImInfty f) (hgper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) (hghol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g) (hgbdd : UpperHalfPlane.IsBoundedAtImInfty g) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  funext τ
  have hf := W2WsF.hasSum_qCoeff hfper hfhol hfbdd τ
  have hg := W2WsF.hasSum_qCoeff hgper hghol hgbdd τ
  simp only [h] at hf
  exact hf.unique hg

end
