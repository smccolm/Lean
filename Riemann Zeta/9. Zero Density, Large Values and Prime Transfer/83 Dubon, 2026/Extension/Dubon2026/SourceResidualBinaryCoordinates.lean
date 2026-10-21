import Dubon2026.SourceResidualTensorCoordinates
import Dubon2026.SourceBinaryCocycleCoordinates

/-! Residue-field coordinate projections preserve actual binary coboundaries.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> injective tensor coefficient change -> detecting each prime-field coordinate.
The existing additive polynomial action comparison supplies equivariance.
-/

namespace Dubon2026
noncomputable section
open MvPolynomial CongruenceSubgroup

variable {R S : Type} [CommRing R] [CommRing S]

/-- An arbitrary additive coefficient projection sends each original native binary coboundary
to a coboundary for the same original integer group action. -/
theorem sourceBinaryAdditiveCocycles_coboundary (φ : R →+ S) (Q w : ℕ)
    (z : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w))
    (hz : (z : Gamma0 Q → sourceBinaryCoefficientRep R Q w) ∈
      groupCohomology.coboundaries₁ (sourceBinaryCoefficientRep R Q w)) :
    (sourceBinaryAdditiveCocycles φ Q w z :
      Gamma0 Q → sourceBinaryCoefficientRep S Q w) ∈
      groupCohomology.coboundaries₁ (sourceBinaryCoefficientRep S Q w) := by
  obtain ⟨v, hv⟩ := hz
  refine ⟨sourceHomogeneousAdditiveMap w φ v, ?_⟩
  funext g
  change homogeneousMatrixAction w (g.val.val.map (Int.castRingHom S))
      (sourceHomogeneousAdditiveMap w φ v) -
    sourceHomogeneousAdditiveMap w φ v = sourceHomogeneousAdditiveMap w φ (z g)
  rw [← sourceHomogeneousAdditiveMap_matrix w φ g.val.val, ← map_sub]
  exact congrArg (sourceHomogeneousAdditiveMap w φ) (congrFun hv g)

variable {ell : ℕ} {F ι : Type} [Field F] [Algebra (ZMod ell) F]

open Classical in
private theorem coordinate_integer_sum (b : Module.Basis ι (ZMod ell) F)
    (s : Finset ι) (a : ι → ℤ) (j : ι) :
    sourceResidualCoordinate b j (∑ i ∈ s, b i * (a i : F)) =
      if j ∈ s then (a j : ZMod ell) else 0 := by
  simp only [map_sum, sourceResidualCoordinate_basis_intCast]
  rw [Finset.sum_ite_eq' s j]

private def coefficientEval (R : Type) [CommRing R] (Q w : ℕ)
    (g : Gamma0 Q) (m : Fin 2 →₀ ℕ) :
    groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w) →ₗ[R] R where
  toFun c := coeff m (c g).val
  map_add' c d := coeff_add m (c g).val (d g).val
  map_smul' a c := coeff_smul m a (c g).val

/-- Each coordinate of a finite residue-field combination of integral cocycles is
the actual prime reduction of its corresponding integral cocycle. -/
theorem sourceResidualBinaryCoordinate_sum (b : Module.Basis ι (ZMod ell) F)
    (Q w : ℕ) (s : Finset ι)
    (z : ι → groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℤ Q w))
    (j : ι) (hj : j ∈ s) :
    sourceBinaryAdditiveCocycles (sourceResidualCoordinate b j) Q w
      (∑ i ∈ s, b i • sourceBinaryCocyclesChange (Int.castRingHom F) Q w (z i)) =
      sourceBinaryCocyclesChange (Int.castRingHom (ZMod ell)) Q w (z j) := by
  classical
  apply groupCohomology.cocycles₁_ext
  intro g
  apply Subtype.ext
  apply MvPolynomial.ext
  intro m
  rw [sourceBinaryAdditiveCocycles_coeff, sourceBinaryCocyclesChange_apply]
  change sourceResidualCoordinate b j (coefficientEval F Q w g m
      (∑ i ∈ s, b i • sourceBinaryCocyclesChange (Int.castRingHom F) Q w (z i))) = _
  rw [map_sum]
  simp only [map_smul]
  change sourceResidualCoordinate b j (∑ i ∈ s,
      b i * coeff m (sourceBinaryCocyclesChange (Int.castRingHom F) Q w (z i) g).val) = _
  simp only [sourceBinaryCocyclesChange_apply, coeff_map, eq_intCast]
  rw [coordinate_integer_sum, if_pos hj]

end
end Dubon2026
