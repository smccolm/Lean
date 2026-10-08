import Dubon2026.AdelicProjectiveL2Embedding
import Dubon2026.RealProjectivePetersson

/-! # The exact finite-level factor in the original adelic generator's Petersson norm -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- On the genuine finite level the actual original adelic generator is exactly the original real projective cusp lift. -/
theorem adelicCyclicProjectiveGenerator_level (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (q : PSL(2, ℝ))
    (a : RationalFiniteProjectiveGL2) (ha : a ∈ finiteProjectiveGL2Level N) :
    adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) (q, a) = realProjectiveCuspLift f q := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨u, hu, rfl⟩ := ha
  rw [adelicCyclicProjectiveFunction_mk, realProjectiveCuspLift_mk]
  have he := canonicalAdelicGL2CuspLift_level_invariant N f
    (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, 1)) ⟨u, hu⟩
  rw [← map_mul] at he
  simp only [Prod.mk_mul_mk, mul_one, one_mul] at he
  change canonicalAdelicGL2CuspLift N k f (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, u)) = _
  rw [he]
  have hr := canonicalAdelicGL2CuspLift_real_restriction N f (toGLPos r)
  rw [realPositiveUnitaryLift_toGLPos] at hr
  exact hr

/-- The genuine adelic quotient L2 norm of the original generator has exactly the positive finite-level Haar factor times its original classical Petersson norm. -/
theorem adelicCyclicGenerator_l2_inner (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    inner ℂ (adelicProjectiveCyclicToL2 N f (adelicCyclicGenerator N f))
      (adelicProjectiveCyclicToL2 N f (adelicCyclicGenerator N f)) =
      cuspPetersson f f * (finiteProjectiveGL2Measure (finiteProjectiveGL2Level N)).toReal := by
  rw [adelicProjectiveCyclicToL2_inner]
  change (∫ p in adelicProjectiveGamma0Domain N,
    conj (adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) p) *
      adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) p ∂adelicProjectiveMeasure) = _
  calc
    _ = ∫ p in adelicProjectiveGamma0Domain N,
        (conj (realProjectiveCuspLift f p.1) * realProjectiveCuspLift f p.1) * (1 : ℂ)
          ∂adelicProjectiveMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (adelicProjectiveGamma0Domain_isOpen N).measurableSet] with p hp
      have ha : p.2 ∈ finiteProjectiveGL2Level N := hp.2
      change conj (adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) (p.1, p.2)) *
        adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) (p.1, p.2) = _
      rw [adelicCyclicProjectiveGenerator_level N f p.1 p.2 ha, mul_one]
    _ = _ := by
      rw [adelicProjectiveGamma0Domain, adelicProjectiveMeasure,
        setIntegral_prod_mul (fun q => conj (realProjectiveCuspLift f q) * realProjectiveCuspLift f q)
          (fun _ : RationalFiniteProjectiveGL2 => (1 : ℂ)),
        ← cuspPetersson_eq_projectiveGroup_integral]
      simp [Measure.real]

end
end Dubon2026
