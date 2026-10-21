import Dubon2026.SourceCurveResidueEquiv
import Dubon2026.SourceCurveResidueFunctional

/-! DUB-17/18 -> actual regular differential dimension -> global residue
identity -> finite-extension comparison. The actual trace-residue sum is
invariant under constant-preserving field automorphisms. Local canonical
normalization identifies the residue-field trace with the scalar residue;
the proved place bijection then reindexes the whole sum. No vanishing of
global residues is used in this invariance statement.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.trace_canonicalResidue_eq_scalar (v : Place K F)
    (d : v.CanonicalLocalResidueDataK)
    (hres : Function.Bijective (algebraMap K v.ResidueField)) (g : F) :
    Algebra.trace K v.ResidueField (d.res g) = v.localResidueScalar g := by
  rw [v.canonicalLocalResidueData_res_unique hres d]
  change Algebra.trace K v.ResidueField
    (algebraMap K v.ResidueField (v.localResidueScalar g)) = _
  let e := AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hres
  have hd : Module.finrank K v.ResidueField = 1 := by
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [Algebra.trace_algebraMap, hd, one_smul]

variable [CharZero K] [Nontrivial Ω[F⁄K]]
variable [∀ v : Place K F, v.DCoordGenerates]
variable [∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [∀ v : Place K F, Algebra.IsSeparable K v.ResidueField]

theorem kaehlerResidueTermKFam_equiv
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (e : F ≃ₐ[K] F) (g x : F) (v : Place K F) :
    kaehlerResidueTermKFam Rfam (D K F (e x)) (diagonalHom K F (e g)) v =
      kaehlerResidueTermKFam Rfam (D K F x) (diagonalHom K F g) (v.comapEquiv e) := by
  simp only [kaehlerResidueTermKFam_apply]
  rw [v.trace_canonicalResidue_eq_scalar (Rfam v) (hres v),
    (v.comapEquiv e).trace_canonicalResidue_eq_scalar _ (hres _)]
  exact v.localResidueScalar_equiv_differential e (hres v).surjective g x

theorem residueSum_equiv
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (e : F ≃ₐ[K] F) (g x : F) :
    (∑ᶠ v : Place K F,
      kaehlerResidueTermKFam Rfam (D K F (e x)) (diagonalHom K F (e g)) v) =
      ∑ᶠ v : Place K F,
        kaehlerResidueTermKFam Rfam (D K F x) (diagonalHom K F g) v := by
  simp_rw [kaehlerResidueTermKFam_equiv Rfam hres e g x]
  exact finsum_comp_equiv (Place.placeEquiv e)

end
end Dubon2026.SourceCurve
