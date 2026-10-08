import Dubon2026.AdelicLowestWeightIrreducible
import Dubon2026.EigenlineCharacter

/-! # The genuine infinitesimal character of the original cyclic lowest-weight module -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

private theorem centralAction_commutes {K A W : Type*} [Field K] [Ring A] [Algebra K A]
    [AddCommGroup W] [Module K W] (T : A →ₐ[K] Module.End K W)
    (z : Subalgebra.center K A) (a : A) : Commute (T a) (T z.val) := by
  exact (show Commute a z.val from (Subalgebra.mem_center_iff.mp z.property a)).map T

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every compact Cartan eigenspace in the original raising span is exactly its original raising line. -/
theorem adelicRaisingSpan_weight_line (hf : f ≠ 0) (n : ℕ)
    (v : adelicRealSmoothSubmodule f) (hv : v ∈ adelicRaisingSpan f)
    (hH : ⁅compactSl2H, v⁆ = ((k : ℂ) + 2 * n) • v) :
    ∃ a : ℂ, v = a • adelicRaisingJet f n := by
  apply distinctWeight_eigenvector_eq_smul (adelicComplexSl2Action f compactSl2H)
    (adelicRaisingJet f) (fun n => (k : ℂ) + 2 * n) _ (adelicRaisingJet_weight f hf) n v hv hH
  intro m n he
  have hn : (m : ℂ) = n := by linear_combination he / 2
  exact_mod_cast hn

/-- Every genuine central enveloping action commutes with each original matrix infinitesimal. -/
theorem adelicEnvelopingAction_center_commutes_matrix
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) (x : ComplexSl2) :
    Commute (adelicComplexSl2Action f x) (adelicEnvelopingAction f z.val) := by
  have he := centralAction_commutes (adelicEnvelopingAction f) z (UniversalEnvelopingAlgebra.ι ℂ x)
  exact (adelicEnvelopingAction_generator f x) ▸ he

/-- The central translate of the original generator has the same original lowest compact weight. -/
theorem adelicEnvelopingAction_center_generator_weight (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    ⁅compactSl2H, adelicEnvelopingAction f z.val (adelicSmoothGenerator f)⁆ =
      ((k : ℂ) + 2 * (0 : ℕ)) • adelicEnvelopingAction f z.val (adelicSmoothGenerator f) :=
  commutingEnd_eigenvector (adelicComplexSl2Action f compactSl2H)
    (adelicEnvelopingAction f z.val) (adelicSmoothGenerator f) _
    (adelicEnvelopingAction_center_commutes_matrix f z compactSl2H)
    (adelicRaisingJet_weight f hf 0)

/-- Each element of the genuine enveloping-algebra center preserves the original cusp-generator line. -/
theorem adelicEnvelopingAction_center_generator (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    ∃ a : ℂ, adelicEnvelopingAction f z.val (adelicSmoothGenerator f) = a • adelicSmoothGenerator f :=
  adelicRaisingSpan_weight_line f hf 0 _
    (adelicRaisingSpan_enveloping f hf z.val _ (adelicSmoothGenerator_mem_raisingSpan f))
    (adelicEnvelopingAction_center_generator_weight f hf z)

/-- The actual center acts through a genuine complex algebra character defined by its original generator action. -/
def adelicInfinitesimalCharacter (hf : f ≠ 0) :
    Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2) →ₐ[ℂ] ℂ :=
  eigenlineCharacter ((adelicEnvelopingAction f).comp
    (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)).val)
    (adelicSmoothGenerator f)
    (fun h => adelicCyclicHilbertGenerator_ne_zero f hf (congrArg Subtype.val h))
    (adelicEnvelopingAction_center_generator f hf)

/-- The genuine character retains the exact action of every central element on the original generator. -/
theorem adelicInfinitesimalCharacter_generator (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    adelicEnvelopingAction f z.val (adelicSmoothGenerator f) =
      adelicInfinitesimalCharacter f hf z • adelicSmoothGenerator f :=
  eigenlineCharacter_spec ((adelicEnvelopingAction f).comp
    (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)).val)
    (adelicSmoothGenerator f)
    (fun h => adelicCyclicHilbertGenerator_ne_zero f hf (congrArg Subtype.val h))
    (adelicEnvelopingAction_center_generator f hf) z

/-- Every central element acts by the original infinitesimal character on the entire original cyclic raising span. -/
theorem adelicInfinitesimalCharacter_span (hf : f ≠ 0)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2))
    (v : adelicRealSmoothSubmodule f) (hv : v ∈ adelicRaisingSpan f) :
    adelicEnvelopingAction f z.val v = adelicInfinitesimalCharacter f hf z • v := by
  apply commutingEnd_cyclicSpan (adelicEnvelopingAction f) (adelicEnvelopingAction f z.val)
    (adelicSmoothGenerator f) (adelicInfinitesimalCharacter f hf z)
    (fun a => (centralAction_commutes (adelicEnvelopingAction f) z a).symm)
    (adelicInfinitesimalCharacter_generator f hf z) v
  exact (adelicRaisingSpan_eq_enveloping f hf) ▸ hv

/-- The actual infinitesimal character takes the normalized central Casimir to its exact original Hilbert eigenvalue. -/
theorem adelicInfinitesimalCharacter_casimir (hf : f ≠ 0) :
    adelicInfinitesimalCharacter f hf
      ⟨complexSl2EnvelopingCasimir, complexSl2EnvelopingCasimir_mem_center⟩ =
      ((k : ℂ) / 2) * (1 - (k : ℂ) / 2) := by
  apply smul_left_injective ℂ (show adelicSmoothGenerator f ≠ 0 from
    fun h => adelicCyclicHilbertGenerator_ne_zero f hf (congrArg Subtype.val h))
  exact (adelicInfinitesimalCharacter_generator f hf
    ⟨complexSl2EnvelopingCasimir, complexSl2EnvelopingCasimir_mem_center⟩).symm.trans
      (adelicEnvelopingAction_casimir_generator f)

end
end Dubon2026
