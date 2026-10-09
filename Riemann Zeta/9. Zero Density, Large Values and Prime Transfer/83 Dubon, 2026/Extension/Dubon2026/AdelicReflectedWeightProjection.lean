import Dubon2026.AdelicRotationProjectionReal
import Dubon2026.RealRotationReflection
import Dubon2026.IntegerIrrationalCharacter

/-! # The actual negative real component has zero positive lowest-weight projection -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

private theorem representation_relation_eigen {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (a b c : G) (h : a * b = b * c)
    (v : V) (μ : ℂ) (hv : ρ c v = μ • v) : ρ a (ρ b v) = μ • ρ b v := by
  rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply, hv, map_smul]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The reflected original raising vector has precisely the negative of its actual rotation weight. -/
theorem adelicReflectedRaisingJet_rotation (hf : f ≠ 0) (n : ℕ) (t : ℝ) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve t))
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection))
        (adelicRaisingJet f n).val) =
    Complex.exp (((-t : ℝ) : ℂ) * (Complex.I * ((k : ℂ) + 2 * n))) •
      adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection))
        (adelicRaisingJet f n).val := by
  exact @representation_relation_eigen RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f) _ _ _
    (adelicRealReflection_rotation t) (adelicRaisingJet f n).val _
    (adelicRaisingJet_rotation f hf n (-t))

/-- Every reflected original raising vector is orthogonal to the positive original lowest rotation-character space. -/
theorem adelicReflectedRaisingJet_orthogonal (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) :
    adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection))
      (adelicRaisingJet f n).val ∈ (@Submodule.orthogonal ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
      (adelicRotationWeightSpace f)) := by
  intro u hu
  have hmu := (mem_adelicRotationWeightSpace f u).mp hu (Real.pi * Real.sqrt 2)
  have hnorm : ‖integerIrrationalCharacter k‖ = 1 := by
    simpa only [irrationalRotationCharacter, integerIrrationalCharacter, Nat.cast_zero,
      mul_zero, add_zero] using irrationalRotationCharacter_norm k 0
  have hne : integerIrrationalCharacter k ≠ integerIrrationalCharacter (-(k + 2 * (n : ℤ))) :=
    integerIrrationalCharacter_injective.ne (by omega)
  have hnu := adelicReflectedRaisingJet_rotation f hf n (Real.pi * Real.sqrt 2)
  rw [irrationalRotationCharacter_negative] at hnu
  exact @unitary_distinct_eigen_inner_zero (AdelicCyclicHilbert f) inferInstance inferInstance
    (adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))))
    (adelicCyclicHilbertRepresentation_inner f _) u _ _ _ hnorm hne hmu hnu

/-- The genuine positive lowest-weight projector annihilates every reflected original raising vector. -/
theorem adelicRotationWeightProjection_reflectedRaising (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) :
    adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection))
        (adelicRaisingJet f n).val) = 0 := by
  have h := (@Submodule.orthogonalProjection_eq_zero_iff ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicRotationWeightSpace f) inferInstance _).mpr
    (adelicReflectedRaisingJet_orthogonal f hf hk n)
  exact congrArg Subtype.val h

/-- The original projector annihilates the reflected entire genuine real cyclic component. -/
theorem adelicRotationWeightProjection_reflectedReal (hf : f ≠ 0) (hk : 0 < k)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRealCyclicClosedSpan f) :
    adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection)) v) = 0 := by
  rw [← adelicRaisingClosedSpan_eq_realCyclicClosedSpan f hf] at hv
  let T := (adelicRotationWeightProjection f).comp
    (adelicCyclicHilbertOperator f (adelicRealGL2Embedding (rationalGL2ToReal rationalGL2Reflection)))
  have hs : Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val)) ≤
      LinearMap.ker T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact adelicRotationWeightProjection_reflectedRaising f hf hk n
  exact closure_minimal hs T.isClosed_ker hv

end
end Dubon2026
