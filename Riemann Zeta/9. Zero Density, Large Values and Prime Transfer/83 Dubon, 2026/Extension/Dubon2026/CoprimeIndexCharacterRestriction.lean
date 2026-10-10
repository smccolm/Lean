import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Constructions

/-! # Actual character restriction across an original subgroup of coprime index -/

namespace Dubon2026

noncomputable section

/-- An original homomorphism between groups of coprime actual cardinalities is trivial. -/
theorem monoidHom_eq_one_of_natCard_coprime
    {G T : Type*} [Group G] [Group T]
    (hcard : (Nat.card G).Coprime (Nat.card T)) (f : G →* T) : f = 1 := by
  ext g
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hcard
    ((orderOf_map_dvd f g).trans (orderOf_dvd_natCard g))
    (orderOf_dvd_natCard (f g))

/-- Original commutative-valued characters are determined by their restriction to an actual normal subgroup whose quotient cardinality is coprime to the target cardinality. -/
theorem coprime_quotient_character_restriction_injective
    {G T : Type*} [Group G] [CommGroup T] (H : Subgroup G) [H.Normal]
    (hcard : (Nat.card (G ⧸ H)).Coprime (Nat.card T)) :
    Function.Injective (fun f : G →* T => f.comp H.subtype) := by
  intro f g hfg
  let χ : G →* T := f / g
  have hker : H ≤ χ.ker := by
    intro x hx
    change f x / g x = 1
    apply div_eq_one.mpr
    exact DFunLike.congr_fun hfg (⟨x, hx⟩ : H)
  let ψ := QuotientGroup.lift H χ hker
  have hψ : ψ = 1 := monoidHom_eq_one_of_natCard_coprime hcard ψ
  ext x
  apply div_eq_one.mp
  exact DFunLike.congr_fun hψ (QuotientGroup.mk' H x)

/-- Finiteness of actual continuous characters on the original subgroup descends through restriction across the actual coprime quotient. -/
theorem coprime_quotient_continuous_characters_finite
    {G T : Type*} [Group G] [CommGroup T] [TopologicalSpace G] [TopologicalSpace T]
    (H : Subgroup G) [H.Normal]
    (hcard : (Nat.card (G ⧸ H)).Coprime (Nat.card T))
    [Finite (H →ₜ* T)] : Finite (G →ₜ* T) := by
  let inclusion : H →ₜ* G := {
    toMonoidHom := H.subtype
    continuous_toFun := continuous_subtype_val }
  apply Finite.of_injective (fun f : G →ₜ* T => f.comp inclusion)
  intro f g hfg
  have hrest : f.toMonoidHom.comp H.subtype = g.toMonoidHom.comp H.subtype := by
    ext x
    exact DFunLike.congr_fun hfg x
  have h := coprime_quotient_character_restriction_injective H hcard hrest
  ext x
  exact DFunLike.congr_fun h x

end
end Dubon2026
