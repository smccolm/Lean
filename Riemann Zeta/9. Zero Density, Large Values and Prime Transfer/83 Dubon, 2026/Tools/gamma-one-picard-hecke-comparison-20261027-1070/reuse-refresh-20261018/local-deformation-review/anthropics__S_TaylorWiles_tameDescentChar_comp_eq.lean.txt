import Mathlib
import Definitions.Def_Deformations_TameDescent
import P2M.Util
namespace P2MW.S_TaylorWiles_tameDescentChar_comp_eq

set_option autoImplicit false

universe u v w

open Function

theorem solution {G : Type u} {Δ : Type v} {A : Type w} [Group G] [Group Δ] [CommRing A]
    (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) (g : G) :
    TaylorWiles.tameDescentChar π hπ χ hχ (π g) = χ g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g) =
      QuotientGroup.mk g := by
    apply (QuotientGroup.quotientKerEquivOfSurjective π hπ).injective
    rw [MulEquiv.apply_symm_apply]
    exact (QuotientGroup.kerLift_mk (φ := π) g).symm
  show (QuotientGroup.lift π.ker χ hχ)
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g)) = χ g
  rw [h]
  rfl
