import Dubon2026.HopfCoinvariantBaseChangeEquivalence
import Dubon2026.AlgebraBaseChangePoints

/-! # Exact original invariant-point restriction under scalar extension -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R K A B : Type*} [CommRing R] [CommRing K] [Algebra R K] [Module.Flat R K]
  [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]

/-- The actual extension of an original point, restricted to genuine geometric invariants and pulled back along their original base-change equivalence, is the extension of its restriction to the original integral invariants. -/
theorem hopfCoinvariantPointBaseChange_restriction (q : A →ₐc[R] B) (p : A →ₐ[R] K) :
    ((AlgHom.liftEquiv R K A K p).comp
      (hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := K) q)).val).comp
        (hopfCoinvariantBaseChangeAlgEquiv (S := K) q).toAlgHom =
      AlgHom.liftEquiv R K (hopfSubgroupCoinvariants q) K
        (p.comp (hopfSubgroupCoinvariants q).val) := by
  apply Algebra.TensorProduct.ext'
  intro k a
  change (AlgHom.liftEquiv R K A K p) ((hopfCoinvariantBaseChangeAlgEquiv q (k ⊗ₜ[R] a)).val) = _
  rw [hopfCoinvariantBaseChangeAlgEquiv_coordinate]
  rfl

/-- Equality on the actual integral invariant coordinates is equivalent to equality on the genuine geometric invariant coordinates after extending the same original points. -/
theorem hopfCoinvariantPointBaseChange_restriction_iff (q : A →ₐc[R] B)
    (p r : A →ₐ[R] K) :
    p.comp (hopfSubgroupCoinvariants q).val = r.comp (hopfSubgroupCoinvariants q).val ↔
      (AlgHom.liftEquiv R K A K p).comp
        (hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := K) q)).val =
      (AlgHom.liftEquiv R K A K r).comp
        (hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := K) q)).val := by
  constructor
  · intro h
    apply AlgHom.ext
    intro a
    obtain ⟨z, rfl⟩ := (hopfCoinvariantBaseChangeAlgEquiv (S := K) q).surjective a
    calc
      _ = (AlgHom.liftEquiv R K (hopfSubgroupCoinvariants q) K
          (p.comp (hopfSubgroupCoinvariants q).val)) z :=
        AlgHom.congr_fun (hopfCoinvariantPointBaseChange_restriction q p) z
      _ = (AlgHom.liftEquiv R K (hopfSubgroupCoinvariants q) K
          (r.comp (hopfSubgroupCoinvariants q).val)) z := by rw [h]
      _ = _ := (AlgHom.congr_fun (hopfCoinvariantPointBaseChange_restriction q r) z).symm
  · intro h
    apply (AlgHom.liftEquiv R K (hopfSubgroupCoinvariants q) K).injective
    rw [← hopfCoinvariantPointBaseChange_restriction q p,
      ← hopfCoinvariantPointBaseChange_restriction q r, h]

end
end Dubon2026
