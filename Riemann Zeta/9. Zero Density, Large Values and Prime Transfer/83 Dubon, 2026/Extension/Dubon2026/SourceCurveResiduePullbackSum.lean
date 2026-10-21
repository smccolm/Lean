import Dubon2026.SourceCurveResidueFiberSum

/-! DUB-17/18 -> original global residue identity -> descent from the normal
closure. The global residue sum of a pulled-back differential is the original
sum multiplied by the actual field-extension degree. The local pullback law,
actual fiber correspondence and native Dedekind degree sum discharge the
entire comparison; only finite support and local geometric inputs are used.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]
variable [CharZero K] [Nontrivial Ω[F⁄K]] [Nontrivial Ω[E⁄K]]
variable [∀ v : Place K F, v.DCoordGenerates]
variable [∀ w : Place K E, w.DCoordGenerates]
variable [∀ w : Place K E, Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄K]]
variable [∀ w : Place K E, Algebra.IsSeparable K w.ResidueField]

theorem residueSum_pullback
    (RF : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (RE : ∀ w : Place K E, w.CanonicalLocalResidueDataK)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (ω : Ω[F⁄K]) (f : F)
    (hs : (Function.support (kaehlerResidueTermKFam RE (KaehlerDifferential.map K K F E ω)
      (diagonalHom K E (algebraMap F E f)))).Finite) :
    (∑ᶠ w : Place K E, kaehlerResidueTermKFam RE (KaehlerDifferential.map K K F E ω)
      (diagonalHom K E (algebraMap F E f)) w) =
      (Module.finrank F E : K) *
        ∑ᶠ v : Place K F, kaehlerResidueTermKFam RF ω (diagonalHom K F f) v := by
  classical
  rw [finsum_eq_fiber_finsum (fun w : Place K E => w.restrict F) _ hs, mul_finsum]
  apply finsum_congr
  intro v
  have he : (∑ᶠ w : {w : Place K E // w.restrict F = v},
      (w.1.ord (algebraMap F E v.uniformizer) : K)) = (Module.finrank F E : K) := by
    letI := Fintype.ofFinite {w : Place K E // w.restrict F = v}
    have h := v.sum_fiber_ramification (hF v) hE
    rw [finsum_eq_sum_of_fintype] at h ⊢
    exact_mod_cast h
  calc
    _ = ∑ᶠ w : {w : Place K E // w.restrict F = v},
        (w.1.ord (algebraMap F E v.uniformizer) : K) *
          kaehlerResidueTermKFam RF ω (diagonalHom K F f) v := by
      apply finsum_congr
      intro w
      rw [kaehlerResidueTermKFam_pullback RF RE hF hE, w.2]
    _ = _ := by rw [← finsum_mul, he]

theorem residueSum_pullback_differential
    (RF : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (RE : ∀ w : Place K E, w.CanonicalLocalResidueDataK)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (x f : F)
    (hs : (Function.support (kaehlerResidueTermKFam RE (D K E (algebraMap F E x))
      (diagonalHom K E (algebraMap F E f)))).Finite) :
    (∑ᶠ w : Place K E, kaehlerResidueTermKFam RE (D K E (algebraMap F E x))
      (diagonalHom K E (algebraMap F E f)) w) =
      (Module.finrank F E : K) *
        ∑ᶠ v : Place K F, kaehlerResidueTermKFam RF (D K F x) (diagonalHom K F f) v := by
  have h := residueSum_pullback RF RE hF hE (D K F x) f
    (by rw [KaehlerDifferential.map_D]; exact hs)
  rwa [KaehlerDifferential.map_D] at h

end
end Dubon2026.SourceCurve
