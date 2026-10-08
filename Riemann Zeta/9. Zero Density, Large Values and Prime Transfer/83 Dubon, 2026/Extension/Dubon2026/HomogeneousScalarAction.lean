import Dubon2026.HomogeneousRaisingBasis

/-! # Full scalar central action on the entire original homogeneous representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- Every original algebraic raising vector has the exact same genuine central scalar as its original generator. -/
theorem homogeneousEnvelopingAction_center_jet (n r : ℕ)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    homogeneousEnvelopingAction n z.val (homogeneousRaisingJet n r) =
      vermaPolynomialCentralValue (n : ℂ) z • homogeneousRaisingJet n r := by
  have he := primitiveVermaMap_enveloping (homogeneousSl2Action n) (homogeneousCompactGenerator n)
    (n : ℂ) (homogeneousCompactGenerator_ne_zero n) (homogeneousCompactGenerator_H n)
    (homogeneousCompactGenerator_F n) z.val (Polynomial.X ^ r)
  rw [vermaPolynomialCentralValue_X_pow, map_smul, homogeneousRaisingJet_verma] at he
  exact he.symm

/-- Every genuine central enveloping element acts by its original Verma scalar on the entire actual finite-dimensional homogeneous representation. -/
theorem homogeneousEnvelopingAction_center_scalar (n : ℕ)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    homogeneousEnvelopingAction n z.val = vermaPolynomialCentralValue (n : ℂ) z • LinearMap.id := by
  apply (homogeneousRaisingBasis n).ext
  intro r
  simp only [homogeneousRaisingBasis_apply, LinearMap.smul_apply, LinearMap.id_apply,
    homogeneousEnvelopingAction_center_jet]

/-- The full actual central character applies to every original homogeneous polynomial vector. -/
theorem homogeneousEnvelopingAction_center_apply (n : ℕ)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2))
    (p : homogeneousSubmodule (Fin 2) ℂ n) :
    homogeneousEnvelopingAction n z.val p = vermaPolynomialCentralValue (n : ℂ) z • p := by
  rw [homogeneousEnvelopingAction_center_scalar, LinearMap.smul_apply, LinearMap.id_apply]

end
end Dubon2026
