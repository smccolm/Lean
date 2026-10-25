import Dubon2026.SourceOriginalWeilNormAdjunction
import Dubon2026.SourceCurvePullbackPushforwardDisjoint

/-! DUB-17/18 -> correspondence adjointness. A top-level Weil datum
whose first divisor is pulled back supplies an actual base datum by
norming the second function and pushing its divisor forward. The norm
orders and disjointness are proved, so no norm-datum existence is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped Classical BigOperators
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M] {n : ℕ}

/-- Actual norm pushforward of compatible Weil representatives. -/
def originalWeilNormDatum
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (e : OriginalWeilDatum M L n)
    (D : Divisor L (modularFunctionFieldOver N L)) (f : modularFunctionFieldOver N L)
    (hf : f ≠ 0) (hord : ∀ v : Place L (modularFunctionFieldOver N L), v.ord f = n * D v)
    (hD : e.D₁ = Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D) :
    OriginalWeilDatum N L n := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    original_field_hom_finite L N M φ
  haveI : Algebra.IsSeparable (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    Algebra.IsSeparable.of_integral _ _
  refine {
    D₁ := D
    D₂ := Divisor.geometricPushforwardAlong φ (original_field_hom_finite L N M φ) e.D₂
    f₁ := f
    f₂ := Algebra.norm (modularFunctionFieldOver N L) e.f₂
    f₁_ne_zero := hf
    f₂_ne_zero := Algebra.norm_ne_zero_iff.mpr e.f₂_ne_zero
    ord_f₁ := hord
    ord_f₂ := ?_
    disjoint := Divisor.disjoint_pushforward_of_pullback φ
      (original_field_hom_finite L N M φ) D e.D₂ (fun w => by rw [← hD]; exact e.disjoint w) }
  · intro v
    rw [v.ord_norm_eq_sum_fiber (original_place_residue_algebraMap_bijective N L v)
      (original_place_residue_algebraMap_bijective M L) e.f₂_ne_zero]
    change _ = (n : ℤ) * Divisor.geometricPushforward (modularFunctionFieldOver N L) e.D₂ v
    rw [Divisor.geometricPushforward_apply]
    haveI : Finite {w : Place L (modularFunctionFieldOver M L) //
        w.restrict (modularFunctionFieldOver N L) = v} := Place.finite_placeFiber v
    letI := Fintype.ofFinite {w : Place L (modularFunctionFieldOver M L) //
      w.restrict (modularFunctionFieldOver N L) = v}
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => e.ord_f₂ w.val

theorem originalWeilNormDatum_pairing
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (e : OriginalWeilDatum M L n)
    (D : Divisor L (modularFunctionFieldOver N L)) (f : modularFunctionFieldOver N L)
    (hf : f ≠ 0) (hord : ∀ v : Place L (modularFunctionFieldOver N L), v.ord f = n * D v)
    (hD : e.D₁ = Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D)
    (he : e.f₁ = φ f) : (originalWeilNormDatum L N M φ e D f hf hord hD).pairing = e.pairing :=
  originalWeilDatum_norm_adjunction L N M φ _ e hD rfl he rfl

end
end Dubon2026.SourceFunctionField
