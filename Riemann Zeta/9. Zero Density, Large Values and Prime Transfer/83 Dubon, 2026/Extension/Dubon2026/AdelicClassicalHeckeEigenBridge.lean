import Dubon2026.AdelicPrimitiveHeckeEigen

/-! # Actual Hilbert Hecke eigenvectors descend to their genuine classical Hecke equations -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- Faithfulness of the original completion, the exact full Hecke lift and the nonzero determinant factor transfer an actual Hilbert Hecke equation to the genuine reconstructed classical cusp form. -/
theorem adelicCyclic_classical_Hecke_eigen {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hF : v.val = canonicalAdelicGL2CuspLift N k F)
    (a : ℂ) (ha : adelicHilbertHeckeTrace f p hpN (adelicCyclicHilbertEmbedding f v) =
      ((Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) * a) • adelicCyclicHilbertEmbedding f v) :
    cuspHeckeLinear N k p F = a • F := by
  let c : ℂ := (Real.sqrt (p : ℝ) : ℂ) ^ (2 - k)
  have hv : adelicAlgebraicHeckeTrace f p hpN v = (c * a) • v := by
    apply adelicCyclicHilbertEmbedding_injective f
    rw [adelicHeckeTrace_embedding, map_smul]
    exact ha
  have ht := adelicAlgebraicHeckeTrace_classical_full f p hpN v F hF
  have he : canonicalAdelicGL2CuspLift N k (c • cuspHecke p F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) =
      canonicalAdelicGL2CuspLift N k ((c * a) • F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) := by
    calc
      _ = (adelicAlgebraicHeckeTrace f p hpN v).val := ht.symm
      _ = (c * a) • v.val := congrArg Subtype.val hv
      _ = _ := by rw [hF]; exact (canonicalAdelicGL2CuspLift_smul N k (c * a) F).symm
  have hcusp := canonicalAdelicGL2CuspLift_injective N k he
  have hc : c ≠ 0 := zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero p))).ne')
  apply smul_right_injective _ hc
  change c • cuspHecke p F = c • (a • F)
  rw [smul_smul]
  exact hcusp

end
end Dubon2026
