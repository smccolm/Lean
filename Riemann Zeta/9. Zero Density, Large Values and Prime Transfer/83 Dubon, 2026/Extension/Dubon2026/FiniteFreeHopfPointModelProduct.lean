import Dubon2026.FiniteFreeHopfPointModel
import Dubon2026.FiniteFreeHopfPointProducts

/-! # Actual tensor-coordinate models of products of original Galois modules -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R F K V W : Type*} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommGroup V] [CommGroup W]

/-- The specified original Galois actions act on the actual product group componentwise. -/
def galoisModuleProductAction
    (ρ : (K ≃ₐ[F] K) →* MulAut V) (τ : (K ≃ₐ[F] K) →* MulAut W) :
    (K ≃ₐ[F] K) →* MulAut (V × W) where
  toFun g := MulEquiv.prodCongr (ρ g) (τ g)
  map_one' := by
    apply MulEquiv.ext
    intro x
    change (ρ 1 x.1, τ 1 x.2) = x
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    change (ρ (g * h) x.1, τ (g * h) x.2) = (ρ g (ρ h x.1), τ g (τ h x.2))
    rw [map_mul, map_mul]
    rfl

/-- The tensor product of the original finite free coordinate algebras constructs a genuine model for the product of the given original Galois modules. Finite freeness, cocommutativity, point reconstruction, and exact original Galois compatibility are supplied by the actual tensor constructions. -/
def finiteFreeHopfPointModelProduct
    {ρ : (K ≃ₐ[F] K) →* MulAut V} {τ : (K ≃ₐ[F] K) →* MulAut W}
    (m : FiniteFreeHopfPointModel R F K V ρ) (n : FiniteFreeHopfPointModel R F K W τ) :
    FiniteFreeHopfPointModel R F K (V × W) (galoisModuleProductAction ρ τ) := by
  letI := m.commRing
  letI := m.hopf
  letI := m.cocomm
  letI := m.finite
  letI := m.free
  letI := n.commRing
  letI := n.hopf
  letI := n.cocomm
  letI := n.finite
  letI := n.free
  refine { Coordinates := m.Coordinates ⊗[R] n.Coordinates
           pointEquiv := hopfTensorPointsProductEquiv.trans
             (MulEquiv.prodCongr m.pointEquiv n.pointEquiv)
           galois := ?_ }
  intro g p
  change (m.pointEquiv (hopfTensorPointsProductEquiv (hopfPointsGaloisAction g p)).1,
      n.pointEquiv (hopfTensorPointsProductEquiv (hopfPointsGaloisAction g p)).2) =
    (ρ g (m.pointEquiv (hopfTensorPointsProductEquiv p).1),
      τ g (n.pointEquiv (hopfTensorPointsProductEquiv p).2))
  rw [hopfTensorPointsProductEquiv_galois]
  exact Prod.ext (m.galois g (hopfTensorPointsProductEquiv p).1)
    (n.galois g (hopfTensorPointsProductEquiv p).2)

/-- The constructed product model retains the original point groups and evaluates them through the genuine restrictions to the two original coordinate factors. -/
theorem finiteFreeHopfPointModel_product_points
    {ρ : (K ≃ₐ[F] K) →* MulAut V} {τ : (K ≃ₐ[F] K) →* MulAut W}
    (m : FiniteFreeHopfPointModel R F K V ρ) (n : FiniteFreeHopfPointModel R F K W τ) :
    letI := m.commRing
    letI := m.hopf
    letI := n.commRing
    letI := n.hopf
    ∀ p : WithConv ((m.Coordinates ⊗[R] n.Coordinates) →ₐ[R] K),
      (finiteFreeHopfPointModelProduct m n).pointEquiv p =
        (m.pointEquiv (hopfTensorPointsProductEquiv p).1,
         n.pointEquiv (hopfTensorPointsProductEquiv p).2) := by
  intro p
  rfl

end
end Dubon2026
