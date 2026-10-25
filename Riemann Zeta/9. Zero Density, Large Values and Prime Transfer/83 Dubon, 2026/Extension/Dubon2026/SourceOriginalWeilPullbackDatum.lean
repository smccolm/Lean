import Dubon2026.SourceOriginalPicardFiniteMaps
import Dubon2026.SourceOriginalWeilPairingDescent
import Dubon2026.SourceCurveCorrespondencePlaces

/-! DUB-17/18 -> Weil norm adjunction -> compatible representatives.
Map the first principal function along the actual field embedding and
pull back its divisor; retain a second representative disjoint from it. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M] {n : ℕ}

/-- The literal pullback representatives used for finite-map adjunction. -/
def originalWeilPullbackDatum
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L))
    (E : Divisor.degZero (K := L) (F := modularFunctionFieldOver M L))
    (f : modularFunctionFieldOver N L) (g : modularFunctionFieldOver M L)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hordf : ∀ v : Place L (modularFunctionFieldOver N L), v.ord f = n * D.val v)
    (hordg : ∀ w : Place L (modularFunctionFieldOver M L), w.ord g = n * E.val w)
    (havoid : ∀ w ∈ (Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D.val).support,
      E.val w = 0) : OriginalWeilDatum M L n where
  D₁ := Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D.val
  D₂ := E.val
  f₁ := φ f
  f₂ := g
  f₁_ne_zero := (map_ne_zero φ).mpr hf
  f₂_ne_zero := hg
  ord_f₁ w := by
    rw [Place.ord_restrictAlong, hordf, Divisor.finitePullbackAlong_apply, mul_assoc]
  ord_f₂ := hordg
  disjoint w := by
    by_cases hw : Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D.val w = 0
    · exact Or.inl hw
    · exact Or.inr (havoid w (Finsupp.mem_support_iff.mpr hw))

end
end Dubon2026.SourceFunctionField
