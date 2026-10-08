import Dubon2026.AdelicHilbertCentralLevel

/-! # The original compact weight in the genuine completed adelic representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The actual positive-real/finite original cusp function retains its exact original compact character. -/
theorem positiveAdelicGL2CuspLift_compact_right (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : GL(2, ℝ)⁺) (x : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (a : realCompactSubgroup) :
    positiveAdelicGL2CuspLift N k f (g * toGLPos a.val) x =
      (realCompactWeight k a : ℂ) * positiveAdelicGL2CuspLift N k f g x := by
  unfold positiveAdelicGL2CuspLift realPositiveUnitaryLift
  rw [← mul_assoc, map_mul, realPositiveNormalize_toGLPos]
  exact congrFun (realWeightLift_rightRegular k f a) _

/-- The original compact real subgroup is embedded in canonical full adelic GL2 with finite coordinate one. -/
def adelicRealCompactEmbedding : realCompactSubgroup →* RationalAdelicGL2 :=
  positiveAdelicGL2Embedding.comp
    ((toGLPos.comp realCompactSubgroup.subtype).prod (1 : realCompactSubgroup →*
      GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))

/-- The actual original algebraic adelic generator is an eigenvector of its genuine compact subgroup with exactly the original compact weight. -/
theorem adelicCyclicGenerator_compact_weight (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : realCompactSubgroup) :
    (adelicLiftCyclicRepresentation N k f).toRepresentation (adelicRealCompactEmbedding a)
      (adelicCyclicGenerator N f) = (realCompactWeight k a : ℂ) • adelicCyclicGenerator N f := by
  apply adelicCyclicProjectiveFunction_injective N f
  funext p
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
  obtain ⟨x, hx⟩ := ProjGenLinGroup.mk_surjective p.2
  have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk x) := Prod.ext hr.symm hx.symm
  rw [hp, adelicCyclicProjectiveFunction_mk, adelicCyclicProjectiveFunction_mk]
  change canonicalAdelicGL2CuspLift N k f (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, x) *
    rationalAdelicGL2RealFiniteEquiv.symm (toGL a.val, 1)) =
    (realCompactWeight k a : ℂ) * canonicalAdelicGL2CuspLift N k f
      (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, x))
  rw [← map_mul]
  simp only [Prod.mk_mul_mk, mul_one]
  rw [canonicalAdelicGL2CuspLift_coordinates, canonicalAdelicGL2CuspLift_coordinates]
  change fullAdelicGL2CuspLift N k f (toGLPos r * toGLPos a.val).val x =
    (realCompactWeight k a : ℂ) * fullAdelicGL2CuspLift N k f (toGLPos r).val x
  rw [fullAdelicGL2CuspLift_positive, fullAdelicGL2CuspLift_positive]
  exact positiveAdelicGL2CuspLift_compact_right N k f (toGLPos r) x a

/-- The completed genuine original adelic generator retains exactly the original compact weight character. -/
theorem adelicCyclicHilbertGenerator_compact_weight {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a : realCompactSubgroup) :
    adelicCyclicHilbertRepresentation f (adelicRealCompactEmbedding a) (adelicCyclicHilbertGenerator f) =
      (realCompactWeight k a : ℂ) • adelicCyclicHilbertGenerator f := by
  rw [adelicCyclicHilbertGenerator, adelicCyclicHilbertEmbedding_intertwines,
    adelicCyclicGenerator_compact_weight, map_smul]

end
end Dubon2026
