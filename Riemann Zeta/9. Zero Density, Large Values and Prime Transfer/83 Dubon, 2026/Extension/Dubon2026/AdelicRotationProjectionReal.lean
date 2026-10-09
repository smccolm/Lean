import Dubon2026.AdelicRotationWeightSpace
import Dubon2026.UnitaryDistinctEigenOrthogonal
import Dubon2026.IrrationalRotationCharacter
import Dubon2026.AdelicRealCyclicClosure

/-! # The original lowest-weight projector on the genuine real cyclic component -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every strictly raised original vector is orthogonal to the full original lowest rotation-character space. -/
theorem adelicRaisingJet_orthogonal_rotationWeight (hf : f ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    (adelicRaisingJet f n).val ∈ (@Submodule.orthogonal ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
      (adelicRotationWeightSpace f)) := by
  intro u hu
  have hu' := (mem_adelicRotationWeightSpace f u).mp hu (Real.pi * Real.sqrt 2)
  have hmu : adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))) u =
        irrationalRotationCharacter k 0 • u := by
    simpa only [irrationalRotationCharacter, Nat.cast_zero, mul_zero, add_zero] using hu'
  exact @unitary_distinct_eigen_inner_zero (AdelicCyclicHilbert f) inferInstance inferInstance
    (adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))))
    (adelicCyclicHilbertRepresentation_inner f _)
    u (adelicRaisingJet f n).val (irrationalRotationCharacter k 0) (irrationalRotationCharacter k n)
    (irrationalRotationCharacter_norm k 0) ((irrationalRotationCharacter_injective k).ne hn.symm)
    hmu (adelicRaisingJet_rotation f hf n (Real.pi * Real.sqrt 2))

/-- The actual lowest-weight projector annihilates every strictly raised original derivative. -/
theorem adelicRotationWeightProjection_raising (hf : f ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    adelicRotationWeightProjection f (adelicRaisingJet f n).val = 0 := by
  have h := (@Submodule.orthogonalProjection_eq_zero_iff ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicRotationWeightSpace f) inferInstance _).mpr
    (adelicRaisingJet_orthogonal_rotationWeight f hf n hn)
  exact congrArg Subtype.val h

/-- On the full original raising closure, the genuine lowest-weight projector takes values in the literal original generator line. -/
theorem adelicRotationWeightProjection_raisingClosure (hf : f ≠ 0) (v : AdelicCyclicHilbert f)
    (hv : v ∈ adelicRaisingClosedSpan f) :
    adelicRotationWeightProjection f v ∈ Submodule.span ℂ {adelicCyclicHilbertGenerator f} := by
  let L : Submodule ℂ (AdelicCyclicHilbert f) := Submodule.span ℂ {adelicCyclicHilbertGenerator f}
  have hs : ∀ w ∈ Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val)),
      adelicRotationWeightProjection f w ∈ L := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨n, rfl⟩ := hw
        by_cases hn : n = 0
        · subst n
          change adelicRotationWeightProjection f (adelicCyclicHilbertGenerator f) ∈ L
          rw [adelicRotationWeightProjection_generator f hf]
          exact Submodule.subset_span (Set.mem_singleton _)
        · rw [adelicRotationWeightProjection_raising f hf n hn]
          exact L.zero_mem
    | zero => simpa only [map_zero] using L.zero_mem
    | add w z hw hz ihw ihz => simpa only [map_add] using L.add_mem ihw ihz
    | smul c w hw ih => simpa only [map_smul] using L.smul_mem c ih
  exact closure_minimal hs (L.closed_of_finiteDimensional.preimage
    (adelicRotationWeightProjection f).continuous) hv

/-- Every original real-group translate projects to an actual scalar multiple of the original generator. -/
theorem adelicRotationWeightProjection_realOrbit (hf : f ≠ 0) (g : SL(2, ℝ)) :
    ∃ c : ℂ, adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (adelicCyclicHilbertGenerator f)) =
        c • adelicCyclicHilbertGenerator f := by
  have hv : adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g)
      (adelicCyclicHilbertGenerator f) ∈ adelicRaisingClosedSpan f := by
    rw [adelicRaisingClosedSpan_eq_realCyclicClosedSpan f hf]
    exact adelicRealCyclicClosedSpan_orbit_mem f g
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (adelicRotationWeightProjection_raisingClosure f hf _ hv)
  exact ⟨c, hc.symm⟩

/-- The exact original finite-place translate is retained when the actual real orbit is projected to its original lowest weight. -/
theorem adelicRotationWeightProjection_finite_realOrbit (hf : f ≠ 0)
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (g : SL(2, ℝ)) :
    ∃ c : ℂ, adelicRotationWeightProjection f
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (adelicCyclicHilbertGenerator f))) =
      c • adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicCyclicHilbertGenerator f) := by
  obtain ⟨c, hc⟩ := adelicRotationWeightProjection_realOrbit f hf g
  exact ⟨c, by rw [adelicRotationWeightProjection_finite, hc, map_smul]⟩

end
end Dubon2026
