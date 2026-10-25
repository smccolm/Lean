import Dubon2026.SourceOriginalWeilAdjunctionWitness

/-! DUB-17/18 -> Hecke-adjoint original Weil pairing. Move the top
divisor away from the finite pullback of a base representative. The
literal mapped first function and normed second function then produce
compatible representatives of all four required actual torsion classes. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped Classical
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M] (n : ℕ) [NeZero n]

theorem exists_original_weil_adjunction_representatives
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n)
    (y : Pic0.torsion (K := L) (F := modularFunctionFieldOver M L) n) :
    ∃ d : OriginalWeilDatum N L n, ∃ e : OriginalWeilDatum M L n,
      d.classLeft.val = x.val ∧ e.classRight.val = y.val ∧
      e.classLeft.val = originalPicardPullback L N M φ x.val ∧
      d.classRight.val = originalPicardNorm L N M φ y.val ∧ d.pairing = e.pairing := by
  obtain ⟨D, hDx⟩ := Pic0.mk_surjective x.val
  have ht : Pic0.mk D ∈ Pic0.torsion n := hDx.symm ▸ x.property
  obtain ⟨f, hf, hordf⟩ := (Pic0.mk_mem_torsion_iff D n).mp ht
  have ho (v : Place L (modularFunctionFieldOver N L)) : v.ord f = n * D.val v := by
    simpa only [Finsupp.smul_apply, nsmul_eq_mul] using (hordf v).symm
  let P := Divisor.finitePullbackAlong φ (original_field_hom_finite L N M φ) D.val
  obtain ⟨E, hEy, havoid⟩ := originalPic0_representative_avoiding M L y.val P.support
  have htE : Pic0.mk E ∈ Pic0.torsion n := hEy.symm ▸ y.property
  obtain ⟨g, hg, hordg⟩ := (Pic0.mk_mem_torsion_iff E n).mp htE
  have hog (w : Place L (modularFunctionFieldOver M L)) : w.ord g = n * E.val w := by
    simpa only [Finsupp.smul_apply, nsmul_eq_mul] using (hordg w).symm
  obtain ⟨d, e, hdL, heR, heL, hdR, he⟩ :=
    exists_original_weil_adjunction_witness L N M φ D E f g hf hg ho hog havoid
  exact ⟨d, e, hdL.trans hDx, heR.trans hEy,
    heL.trans (congrArg (originalPicardPullback L N M φ) hDx),
    hdR.trans (congrArg (originalPicardNorm L N M φ) hEy), he⟩

end
end Dubon2026.SourceFunctionField
