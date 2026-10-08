import Dubon2026.HomogeneousCompactGenerator
import Dubon2026.PrimitiveVermaIntertwiner
import Dubon2026.VermaCentralPolynomial

/-! # Full central scalars on the original finite-dimensional algebraic generator -/

namespace Dubon2026

noncomputable section

/-- The genuine full enveloping algebra acts by the original homogeneous matrix infinitesimals. -/
def homogeneousEnvelopingAction (n : ℕ) :
    UniversalEnvelopingAlgebra ℂ ComplexSl2 →ₐ[ℂ]
      Module.End ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n) :=
  UniversalEnvelopingAlgebra.lift ℂ (homogeneousSl2Action n)

/-- Every genuine central element acts on the actual nonzero algebraic generator by its original Verma scalar at n. -/
theorem homogeneousEnvelopingAction_center_generator (n : ℕ)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    homogeneousEnvelopingAction n z.val (homogeneousCompactGenerator n) =
      vermaPolynomialCentralValue (n : ℂ) z • homogeneousCompactGenerator n := by
  have he := primitiveVermaMap_enveloping (homogeneousSl2Action n) (homogeneousCompactGenerator n)
    (n : ℂ) (homogeneousCompactGenerator_ne_zero n) (homogeneousCompactGenerator_H n)
    (homogeneousCompactGenerator_F n) z.val 1
  rw [vermaPolynomialCentralValue_generator, map_smul] at he
  simpa only [primitiveVermaMap, polynomialCyclicMap_one] using he.symm

end
end Dubon2026
