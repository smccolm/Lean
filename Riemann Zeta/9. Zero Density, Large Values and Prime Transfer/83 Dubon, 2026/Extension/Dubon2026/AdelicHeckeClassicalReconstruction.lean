import Dubon2026.AdelicCyclicHeckeTrace
import Dubon2026.HeckeAllIndices

/-! # The original finite-adelic Hecke trace is the full adelic lift of the genuine classical Hecke cusp form -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every actual original cyclic vector identified with a canonical classical cusp lift is fixed by the genuine original finite level subgroup. -/
theorem adelicCyclic_canonical_level
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hF : v.val = canonicalAdelicGL2CuspLift N k F) :
    adelicCyclicHilbertEmbedding f v ∈ adelicLevelFixedSpace f := by
  apply (mem_adelicLevelFixedSpace f _).mpr
  intro a
  rw [adelicCyclicHilbertEmbedding_intertwines]
  apply congrArg (adelicCyclicHilbertEmbedding f)
  apply Subtype.ext
  funext g
  change v.val (g * rationalAdelicFiniteGL2Embedding a.val) = v.val g
  rw [hF]
  exact canonicalAdelicGL2CuspLift_level_invariant N F g a

/-- On every actual original cyclic classical cusp lift, the genuine finite-adelic Hecke trace equals everywhere the full canonical lift of sqrt(p)^(2-k) times the actual classical Hecke cusp form. -/
theorem adelicAlgebraicHeckeTrace_classical_full (p : ℕ) [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N) (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hF : v.val = canonicalAdelicGL2CuspLift N k F) :
    (adelicAlgebraicHeckeTrace f p hpN v).val = canonicalAdelicGL2CuspLift N k
      ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) • cuspHecke p F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) := by
  have hl : adelicCyclicHilbertEmbedding f (adelicAlgebraicHeckeTrace f p hpN v) ∈ adelicLevelFixedSpace f := by
    rw [adelicHeckeTrace_embedding]
    exact adelicHilbertHeckeTrace_level f p hpN _ (adelicCyclic_canonical_level f v F hF)
  apply adelicCyclic_classical_reconstruction f _ hl
  funext g
  have ht : (adelicAlgebraicHeckeTrace f p hpN v).val (adelicRealSL2Embedding g) =
      (Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) * realWeightLift k (classicalHeckeFunction N k p F) g := by
    rw [adelicAlgebraicHeckeTrace_coe, hF]
    exact canonicalAdelic_HeckeTrace_real F (Fact.out : p.Prime) hpN g
  have hc : (cuspHecke p F : ℍ → ℂ) = classicalHeckeFunction N k p F := funext (cuspHecke_apply p F)
  change realWeightLiftLinear k
    ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) • (cuspHecke p F : ℍ → ℂ)) g = _
  rw [map_smul, hc]
  exact ht.symm

end
end Dubon2026
