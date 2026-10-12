import Dubon2026.LocalFieldFiniteStageCyclicH2

/-! # The fundamental class of each original finite Galois local extension -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original relative fundamental class is the unique genuine H2
class with invariant the reciprocal of its actual field degree. -/
def localFieldFiniteStageFundamentalClass (E : FiniteGaloisIntermediateField K Ω) :
    GaloisUnitH2FiniteStage K Ω E :=
  (localFieldFiniteStageH2CyclicEquiv K Ω E).symm 1

/-- The fundamental class has the arithmetic, positive reciprocal-degree
normalization, also for ramified and noncyclic Galois extensions. -/
theorem localFieldFiniteStageFundamentalClass_invariant
    (E : FiniteGaloisIntermediateField K Ω) :
    localFieldFiniteStageInvariant K Ω E (localFieldFiniteStageFundamentalClass K Ω E) =
      ↑((1 : ℚ) / Module.finrank K E) := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  rw [← localFieldFiniteStageH2CyclicEquiv_invariant]
  simp only [localFieldFiniteStageFundamentalClass, LinearEquiv.apply_symm_apply]
  simpa only [Int.cast_one] using rationalCyclicInvariant_intCast (Module.finrank K E) 1

/-- The reciprocal-degree normalization uniquely characterizes the
class inside the original finite Galois cohomology group. -/
theorem localFieldFiniteStageFundamentalClass_unique
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    localFieldFiniteStageInvariant K Ω E x = ↑((1 : ℚ) / Module.finrank K E) ↔
      x = localFieldFiniteStageFundamentalClass K Ω E := by
  rw [← localFieldFiniteStageFundamentalClass_invariant K Ω E]
  exact (localFieldFiniteStageInvariant_injective K Ω E).eq_iff

/-- The order of the actual fundamental class is exactly the original
field degree, without a cyclicity assumption on the Galois group. -/
theorem localFieldFiniteStageFundamentalClass_addOrderOf
    (E : FiniteGaloisIntermediateField K Ω) :
    addOrderOf (localFieldFiniteStageFundamentalClass K Ω E) = Module.finrank K E := by
  rw [← addOrderOf_injective (localFieldFiniteStageInvariant K Ω E).toAddMonoidHom
    (localFieldFiniteStageInvariant_injective K Ω E)]
  change addOrderOf (localFieldFiniteStageInvariant K Ω E
    (localFieldFiniteStageFundamentalClass K Ω E)) = _
  rw [localFieldFiniteStageFundamentalClass_invariant]
  letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  exact AddCircle.addOrderOf_period_div Module.finrank_pos

/-- Every original finite-stage class is an integer multiple of the
genuine normalized fundamental class. -/
theorem localFieldFiniteStageFundamentalClass_generates
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    ∃ j : ℤ, j • localFieldFiniteStageFundamentalClass K Ω E = x := by
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (localFieldFiniteStageH2CyclicEquiv K Ω E x)
  refine ⟨j, (localFieldFiniteStageH2CyclicEquiv K Ω E).injective ?_⟩
  rw [(localFieldFiniteStageH2CyclicEquiv K Ω E).map_smul]
  simp only [localFieldFiniteStageFundamentalClass, LinearEquiv.apply_symm_apply,
    zsmul_eq_mul, mul_one]
  exact hj

end
end Dubon2026
