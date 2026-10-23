import Dubon2026.SourceEllipticOddSummingSet
import Dubon2026.SourceEllipticVeluBaseChange

/-! Native base change of the actual odd kernel and quotient identity.
Mathlib's affine-point homomorphism supplies the map and injectivity; its
coordinate formula transports the finite half-orbit even at the zero point.
The existing coefficient specialization transports the exact discriminant.
This discharges field descent for odd quotient ellipticity on the DUB-17 /
DUB-18 chain through cyclic products, inertia census and good reduction. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- The native affine-point homomorphism for a specified field embedding. -/
def pointMapHom (f : F →+* K) (W : WeierstrassCurve F) :
    W.toAffine.Point →+ (W.map f).toAffine.Point :=
  letI : Algebra F K := f.toAlgebra
  WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId F K)

theorem pointMapHom_injective (f : F →+* K) (W : WeierstrassCurve F) :
    Function.Injective (pointMapHom f W) := by
  letI : Algebra F K := f.toAlgebra
  exact WeierstrassCurve.Affine.Point.map_injective (W' := W) (Algebra.ofId F K)

theorem coordsOrZero_pointMapHom (f : F →+* K) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) :
    coordsOrZero (pointMapHom f W P) = Prod.map f f (coordsOrZero P) := by
  rcases P with _ | ⟨x, y, h⟩
  · change (0, 0) = (f 0, f 0)
    rw [map_zero]
  · rfl

omit [DecidableEq F] [DecidableEq K] in
theorem map_veluU (f : F →+* K) (W : WeierstrassCurve F) (x y : F) :
    f (veluU W x y) = veluU (W.map f) (f x) (f y) := by
  simp only [veluU, veluGy, map_pow, map_neg, map_add, map_mul, map_ofNat,
    map_a₁, map_a₃]

omit [DecidableEq F] [DecidableEq K] in
theorem map_prod_veluU (f : F →+* K) (W : WeierstrassCurve F) (S : Finset (F × F)) :
    (∏ P ∈ S.map ⟨Prod.map f f, f.injective.prodMap f.injective⟩,
      veluU (W.map f) P.1 P.2) = f (∏ P ∈ S, veluU W P.1 P.2) := by
  rw [Finset.prod_map, map_prod]
  exact Finset.prod_congr rfl fun P _ => (map_veluU f W P.1 P.2).symm

theorem map_oddOrderSummingSet (f : F →+* K) (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) :
    oddOrderSummingSet (W.map f) (pointMapHom f W Q) n =
      (oddOrderSummingSet W Q n).map ⟨Prod.map f f, f.injective.prodMap f.injective⟩ := by
  unfold oddOrderSummingSet
  rw [Finset.map_eq_image, Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  rw [← map_nsmul, coordsOrZero_pointMapHom]
  rfl

omit [DecidableEq F] in
theorem identity_map_iff (f : F →+* K) (W : WeierstrassCurve F)
    (S : Finset (F × F)) (n : ℕ) :
    (veluQuotient (W.map f) (S.map ⟨Prod.map f f, f.injective.prodMap f.injective⟩)).Δ *
        (∏ P ∈ S.map ⟨Prod.map f f, f.injective.prodMap f.injective⟩,
          veluU (W.map f) P.1 P.2) ^ 4 = (W.map f).Δ ^ (2 * n + 1) ↔
      (veluQuotient W S).Δ * (∏ P ∈ S, veluU W P.1 P.2) ^ 4 = W.Δ ^ (2 * n + 1) := by
  have hquot : veluQuotient (W.map f)
      (S.map ⟨Prod.map f f, f.injective.prodMap f.injective⟩) = (veluQuotient W S).map f := by
    rw [Finset.map_eq_image]
    exact (veluQuotient_map f W S (f.injective.prodMap f.injective).injOn).symm
  rw [hquot, map_Δ, map_prod_veluU, map_Δ, ← map_pow, ← map_pow, ← map_mul]
  exact f.injective.eq_iff

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
