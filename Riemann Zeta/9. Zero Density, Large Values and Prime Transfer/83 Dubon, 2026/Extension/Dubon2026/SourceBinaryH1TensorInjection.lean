import Dubon2026.SourceBinaryH1ReductionKernel
import Dubon2026.SourceResidualBinaryCoordinates
import Dubon2026.SourceBinaryH1TensorChange

/-! Injective tensor coefficient change for the original native binary H1.
DUB-17/18 -> residual modular Galois association -> nonzero residual H1
eigensystem -> preservation of a nonzero tensor eigenclass in actual residual H1.

Adapted to the original native cohomology from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL.lean
(Apache-2.0; retained LICENSE and NOTICE). All supplied maps, kernel and
coordinate assumptions in that auxiliary argument are discharged here.
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

/-- Tensoring actual integral binary H1 with any field of prime characteristic
injects into the full original binary H1 over that field by literal coefficient change.
No coefficient kernel, tensor injection or preservation of nonvanishing is assumed. -/
theorem sourceBinaryH1TensorChange_injective (Q w ell : ℕ) (hell : ell.Prime)
    (F : Type) [Field F] [CharP F ell] :
    Function.Injective (sourceBinaryH1TensorChange F Q w) := by
  classical
  letI : Fact ell.Prime := ⟨hell⟩
  letI : NeZero ell := ⟨hell.ne_zero⟩
  letI : Algebra (ZMod ell) F := ZMod.algebra F ell
  let b := Module.Basis.ofVectorSpace (ZMod ell) F
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨f, rfl⟩ := sourceResidualTensor_exists_finsupp b y
  have hsurj : Function.Surjective
      (groupCohomology.H1π (sourceBinaryCoefficientRep ℤ Q w)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  choose z hz using fun j => hsurj (f j)
  have hsum : sourceBinaryH1TensorChange F Q w (f.sum fun j x => b j ⊗ₜ[ℤ] x) =
      groupCohomology.H1π _
        (∑ j ∈ f.support, b j • sourceBinaryCocyclesChange (Int.castRingHom F) Q w (z j)) := by
    rw [Finsupp.sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hz j, sourceBinaryH1TensorChange_cocycle]
  rw [hsum, groupCohomology.H1π_eq_zero_iff] at hy
  have hdiv (j) (hj : j ∈ f.support) :
      ∃ u : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w), f j = (ell : ℤ) • u := by
    have hcob := sourceBinaryAdditiveCocycles_coboundary
      (sourceResidualCoordinate b j) Q w _ hy
    rw [sourceResidualBinaryCoordinate_sum b Q w f.support z j hj] at hcob
    have hred := (groupCohomology.H1π_eq_zero_iff _).mpr hcob
    rw [← sourceBinaryH1Change_cocycle, hz j] at hred
    exact (sourceBinaryH1Change_zmod_eq_zero_iff Q w ell hell (f j)).mp hred
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  obtain ⟨u, hu⟩ := hdiv j hj
  rw [hu]
  have hbalance := (TensorProduct.CompatibleSMul.int (R := ℤ) (M := F)
    (P := groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w))).smul_tmul
      (ell : ℤ) (b j) u
  rw [← hbalance]
  have he : (ell : ℤ) • b j = 0 := by
    rw [zsmul_eq_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]
  rw [he, TensorProduct.zero_tmul]

end
end Dubon2026
