import Dubon2026.SpectralFiniteStageCyclicH2

/-! # The fundamental class of each original finite Galois local extension -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original relative fundamental class is the unique genuine H2
class with invariant the reciprocal of its actual field degree. -/
def spectralFiniteStageFundamentalClass (E : FiniteGaloisIntermediateField K Ω) :
    GaloisUnitH2FiniteStage K Ω E :=
  (spectralFiniteStageH2CyclicEquiv K Ω E).symm 1

/-- The fundamental class has the arithmetic, positive reciprocal-degree
normalization, also for ramified and noncyclic Galois extensions. -/
theorem spectralFiniteStageFundamentalClass_invariant
    (E : FiniteGaloisIntermediateField K Ω) :
    spectralFiniteStageFullInvariant K Ω E (spectralFiniteStageFundamentalClass K Ω E) =
      ↑((1 : ℚ) / Module.finrank K E) := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  rw [← spectralFiniteStageH2CyclicEquiv_invariant]
  simp only [spectralFiniteStageFundamentalClass, LinearEquiv.apply_symm_apply]
  simpa only [Int.cast_one] using rationalCyclicInvariant_intCast (Module.finrank K E) 1

/-- The reciprocal-degree normalization uniquely characterizes the
class inside the original finite Galois cohomology group. -/
theorem spectralFiniteStageFundamentalClass_unique
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    spectralFiniteStageFullInvariant K Ω E x = ↑((1 : ℚ) / Module.finrank K E) ↔
      x = spectralFiniteStageFundamentalClass K Ω E := by
  rw [← spectralFiniteStageFundamentalClass_invariant K Ω E]
  exact (spectralFiniteStageFullInvariant_injective K Ω E).eq_iff

/-- The order of the actual fundamental class is exactly the original
field degree, without a cyclicity assumption on the Galois group. -/
theorem spectralFiniteStageFundamentalClass_addOrderOf
    (E : FiniteGaloisIntermediateField K Ω) :
    addOrderOf (spectralFiniteStageFundamentalClass K Ω E) = Module.finrank K E := by
  rw [← addOrderOf_injective (spectralFiniteStageFullInvariant K Ω E).toAddMonoidHom
    (spectralFiniteStageFullInvariant_injective K Ω E)]
  change addOrderOf (spectralFiniteStageFullInvariant K Ω E
    (spectralFiniteStageFundamentalClass K Ω E)) = _
  rw [spectralFiniteStageFundamentalClass_invariant]
  letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  exact AddCircle.addOrderOf_period_div Module.finrank_pos

/-- Every original finite-stage class is an integer multiple of the
genuine normalized fundamental class. -/
theorem spectralFiniteStageFundamentalClass_generates
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    ∃ j : ℤ, j • spectralFiniteStageFundamentalClass K Ω E = x := by
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (spectralFiniteStageH2CyclicEquiv K Ω E x)
  refine ⟨j, (spectralFiniteStageH2CyclicEquiv K Ω E).injective ?_⟩
  rw [(spectralFiniteStageH2CyclicEquiv K Ω E).map_smul]
  simp only [spectralFiniteStageFundamentalClass, LinearEquiv.apply_symm_apply,
    zsmul_eq_mul, mul_one]
  exact hj

end
end Dubon2026
