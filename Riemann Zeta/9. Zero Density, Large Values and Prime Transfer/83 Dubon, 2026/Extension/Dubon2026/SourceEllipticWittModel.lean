import Dubon2026.SourceWittValuationLift
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! Lift the five actual Weierstrass coefficients by Teichmuller representatives.
Their exact reduction and the original unit discriminant give a good integral
model; no model-existence or good-reduction certificate is assumed. -/

namespace Dubon2026.SourceWittLift
open WeierstrassCurve IsLocalRing
noncomputable section
variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]

/-- The literal five-coefficient Teichmuller lift through a Witt-ring homomorphism. -/
def teichmullerCurve {A : Type*} [CommRing A] (f : WittVector p K →+* A)
    (W : WeierstrassCurve K) : WeierstrassCurve A :=
  ⟨f (WittVector.teichmuller p W.a₁), f (WittVector.teichmuller p W.a₂),
    f (WittVector.teichmuller p W.a₃), f (WittVector.teichmuller p W.a₄),
    f (WittVector.teichmuller p W.a₆)⟩

omit [CharP K p] in
/-- The lifted curve reduces exactly to base change of the original curve. -/
theorem teichmullerCurve_map {A : Type*} [CommRing A] [IsLocalRing A]
    (f : WittVector p K →+* A) (ι : K →+* ResidueField A)
    (h : ∀ a : K, residue A (f (WittVector.teichmuller p a)) = ι a)
    (W : WeierstrassCurve K) :
    (teichmullerCurve f W).map (residue A) = W.map ι := by
  ext <;> exact h _

/-- Every elliptic curve over a perfect positive-characteristic field has this good valuation model. -/
theorem exists_good_integral_model [PerfectRing K p] (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (A : ValuationSubring (AlgebraicClosure (FractionRing (WittVector p K))))
      (V : WeierstrassCurve A) (ι : K →+* ResidueField A),
      V.IsElliptic ∧ V.map (residue A) = W.map ι := by
  obtain ⟨A, f, ι, h⟩ := exists_valuation_lift p K
  have he := teichmullerCurve_map f ι h W
  refine ⟨A, teichmullerCurve f W, ι, ⟨?_⟩, he⟩
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [← map_Δ, he]
  exact (W.map ι).isUnit_Δ.ne_zero

end
end Dubon2026.SourceWittLift
