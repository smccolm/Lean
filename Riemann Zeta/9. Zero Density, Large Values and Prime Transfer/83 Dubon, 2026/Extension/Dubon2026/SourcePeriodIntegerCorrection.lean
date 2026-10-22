import Dubon2026.SourcePeriodReciprocityKernel

/-! DUB-17/18 -> original torsion cardinality -> Abel converse -> period correction.
Raw reciprocity and an integral unimodular intersection matrix suffice to
correct a third-kind period vector by a regular-period vector to integer
multiples of the prescribed scalar. The application uses the scalar 2 pi i.
No alternating-matrix normal form or change of geometric loops is needed.
-/
namespace Dubon2026.SourceFunctionField.PeriodCorrection
noncomputable section
open Matrix

theorem exists_integer_period_correction {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (hA : Function.Injective A.mulVecLin) (hQ : IsUnit Q.det)
    (hRR : (A.transpose * Q.map (Int.castRingHom ℂ)) * A = 0)
    (y : Fin n ⊕ Fin n → ℂ) (t : ℂ) (z : Fin n ⊕ Fin n → ℤ)
    (hrec : (A.transpose * Q.map (Int.castRingHom ℂ)).mulVec y =
      t • A.transpose.mulVec (fun k => (z k : ℂ))) :
    ∃ (c : Fin n → ℂ) (m : Fin n ⊕ Fin n → ℤ),
      ∀ k, y k - A.mulVec c k = t * (m k : ℂ) := by
  obtain ⟨m, hm⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det Q).mpr hQ) z
  have hmC : (Q.map (Int.castRingHom ℂ)).mulVec (fun k => (m k : ℂ)) =
      fun k => (z k : ℂ) := by
    ext k
    have h := (Int.castRingHom ℂ).map_mulVec Q m k
    rw [hm] at h
    exact h.symm
  have hQC : IsUnit (Q.map (Int.castRingHom ℂ)).det := by
    change IsUnit (Q.map fun k => (k : ℂ)).det
    rw [← Int.cast_det]
    exact hQ.map (Int.castRingHom ℂ)
  have hk : (A.transpose * Q.map (Int.castRingHom ℂ)).mulVec
      (y - t • (fun k => (m k : ℂ))) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hrec,
      ← Matrix.mulVec_mulVec, hmC, sub_self]
  obtain ⟨c, hc⟩ := exists_period_correction_of_reciprocity_kernel A
    (Q.map (Int.castRingHom ℂ)) hA hQC hRR _ hk
  refine ⟨c, m, fun k => ?_⟩
  have h := congrFun hc k
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel] using
    congrArg (fun w => y k - w) h

end
end Dubon2026.SourceFunctionField.PeriodCorrection
