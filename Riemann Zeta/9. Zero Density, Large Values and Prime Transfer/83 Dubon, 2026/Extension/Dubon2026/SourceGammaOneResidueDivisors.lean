import Dubon2026.SourceGammaOneResidueFrobeniusPlaces
import Dubon2026.SourceGammaOneResidueGeometry

/-! DUB-17/18 -> original Gamma1 Hecke/Frobenius comparison on torsion ->
exact residue divisor orders. Reuse the actual decomposition place permutation
and proved geometric Frobenius ramification. The inverse permutation and
the factor p are retained exactly; no Frobenius relation is postulated. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

/-- The original residue decomposition action on actual finite divisors. -/
def decompositionResidueDivisorEquiv (d : A.decompositionSubgroup ℚ) :
    Divisor kk Fb ≃+ Divisor kk Fb := Finsupp.domCongr (decompositionResiduePlaceEquiv A Γ d)

theorem decompositionResidueDivisorEquiv_apply (d : A.decompositionSubgroup ℚ)
    (D : Divisor kk Fb) (P : Place kk Fb) :
    decompositionResidueDivisorEquiv A Γ d D (decompositionResiduePlace A Γ d P) = D P := by
  change Finsupp.equivMapDomain (decompositionResiduePlaceEquiv A Γ d) D
    (decompositionResiduePlaceEquiv A Γ d P) = D P
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

theorem decompositionResidueDivisorEquiv_order (d : A.decompositionSubgroup ℚ)
    (D : Divisor kk Fb) (f : Fb) (hD : ∀ P, D P = P.ord f) (P : Place kk Fb) :
    decompositionResidueDivisorEquiv A Γ d D P = P.ord (decompositionResidueAut A Γ d f) := by
  obtain ⟨Q, rfl⟩ := (decompositionResiduePlaceEquiv A Γ d).surjective P
  change decompositionResidueDivisorEquiv A Γ d D (decompositionResiduePlace A Γ d Q) =
    (decompositionResiduePlace A Γ d Q).ord (decompositionResidueAut A Γ d f)
  rw [decompositionResidueDivisorEquiv_apply, decompositionResiduePlace_ord_action, hD]

theorem decompositionResidueDivisorEquiv_degree [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (d : A.decompositionSubgroup ℚ) (D : Divisor kk Fb) :
    Divisor.degree (decompositionResidueDivisorEquiv A Γ d D) = Divisor.degree D := by
  have hr (P : Place kk Fb) : Module.finrank kk P.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (residueImage_place_residue_bijective A Γ hT P)
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero]
  | single_add P n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    change Divisor.degree (Finsupp.equivMapDomain (decompositionResiduePlaceEquiv A Γ d)
      (Finsupp.single P n)) + _ = _
    rw [Finsupp.equivMapDomain_single, Divisor.degree_single, Divisor.degree_single, hr, hr]

theorem geometricFrobenius_inverse_divisor_order (p : ℕ) [Fact p.Prime] [CharP kk p]
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ p)
    (D : Divisor kk Fb) (f : Fb) (hD : ∀ P, D P = P.ord f) (P : Place kk Fb) :
    (p • (decompositionResidueDivisorEquiv A Γ d).symm D) P =
      P.ord (geometricFrobenius A Γ p d hd f) := by
  rw [Finsupp.smul_apply, nsmul_eq_mul, geometricFrobenius_place_order,
    geometricFrobeniusPlace_eq_decomposition]
  change (p : ℤ) * D (decompositionResiduePlace A Γ d P) = _
  rw [hD]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
