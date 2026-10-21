import Dubon2026.SourceCurvePlaceTransport
import Dubon2026.SourceCurveResiduePullback
import Dubon2026.SourceCurveResidueRestrictionConstants

/-! DUB-17/18 -> actual regular differential dimension -> global residue
identity -> Galois trace comparison. The proved local pullback law specializes
to constant-preserving field equivalences. Actual normalized order makes the
factor equal to one; restricted residue rationality is derived from the top
place. This is the local invariance needed to permute places in residue sums.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F E : Type*} [Field K] [Field F] [Field E] [CharZero K]
variable [Algebra K F] [Algebra K E] (w : Place K E) (e : F ≃ₐ[K] E)
variable [w.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K w.ResidueField]

theorem localResidueScalar_equiv_uniformizer
    (hres : Function.Surjective (algebraMap K w.ResidueField)) (g : F) :
    w.localResidueScalar (e g *
      w.coordinateDerivation (e (w.comapEquiv e).uniformizer)) =
        (w.comapEquiv e).localResidueScalar g := by
  letI : Algebra F E := e.toRingHom.toAlgebra
  letI : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  letI : Algebra.IsIntegral F E := Algebra.isIntegral_of_surjective e.surjective
  have hv : w.restrict F = w.comapEquiv e := Place.ext rfl
  have hbase := w.residue_algebraMap_surjective_restrict (F := F) hres
  have h := w.localResidueScalar_restrict_pullback hbase hres g
  rw [hv] at h
  change w.localResidueScalar (e g *
    w.coordinateDerivation (e (w.comapEquiv e).uniformizer)) =
      (w.ord (e (w.comapEquiv e).uniformizer) : K) *
        (w.comapEquiv e).localResidueScalar g at h
  have hord := w.ord_comapEquiv e (w.comapEquiv e).uniformizer
  rw [(w.comapEquiv e).ord_uniformizer] at hord
  rwa [← hord, Int.cast_one, one_mul] at h

omit [CharZero K] [Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄K]]
    [Algebra.IsSeparable K w.ResidueField] in
theorem coordinateDerivation_equiv [Nontrivial Ω[F⁄K]]
    [(w.comapEquiv e).DCoordGenerates] (x : F) :
    w.coordinateDerivation (e x) =
      e ((w.comapEquiv e).coordinateDerivation x) *
        w.coordinateDerivation (e (w.comapEquiv e).uniformizer) := by
  letI : Algebra F E := e.toRingHom.toAlgebra
  letI : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  letI : Algebra.IsIntegral F E := Algebra.isIntegral_of_surjective e.surjective
  have hv : w.restrict F = w.comapEquiv e := Place.ext rfl
  haveI : (w.restrict F).DCoordGenerates := hv ▸ inferInstance
  have h := w.differentialCoeff_map_restrict (D K F x)
  rw [KaehlerDifferential.map_D, hv] at h
  exact h

theorem localResidueScalar_equiv_differential [Nontrivial Ω[F⁄K]]
    [(w.comapEquiv e).DCoordGenerates]
    (hres : Function.Surjective (algebraMap K w.ResidueField)) (g x : F) :
    w.localResidueScalar (e g * w.coordinateDerivation (e x)) =
      (w.comapEquiv e).localResidueScalar
        (g * (w.comapEquiv e).coordinateDerivation x) := by
  rw [w.coordinateDerivation_equiv e, ← mul_assoc, ← map_mul]
  exact w.localResidueScalar_equiv_uniformizer e hres _

end
end Dubon2026.SourceCurve.Place
