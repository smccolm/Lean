import Dubon2026.AdelicSublevelFixedSpace
import Dubon2026.AdelicCyclicLevelDescent

/-! # Genuine classical slash invariance at actual finite adelic sublevels -/

namespace Dubon2026

noncomputable section
open NumberField Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine real restriction is invariant under every rational real matrix whose finite component belongs to the original level group. -/
theorem adelicCyclic_real_rational_sublevel
    (L : Subgroup (finiteAdeleGL2Gamma0 N))
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : adelicCyclicHilbertEmbedding f v ∈ adelicSublevelFixedSpace f L)
    (γ : GeneralLinearGroup (Fin 2) ℚ) (a : L) (ha : a.val.val = rationalGL2ToFinite γ)
    (g : GeneralLinearGroup (Fin 2) ℝ) :
    v.val (adelicRealGL2Embedding (rationalGL2ToReal γ * g)) =
      v.val (adelicRealGL2Embedding g) := by
  calc
    _ = v.val (adelicRealGL2Embedding (rationalGL2ToReal γ * g) *
        rationalAdelicFiniteGL2Embedding (rationalGL2ToFinite γ)) :=
      by
          rw [← ha]
          exact (adelicCyclic_sublevel_pointwise f L v hv a _).symm
    _ = v.val (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ *
        adelicRealGL2Embedding g) := by
      rw [rationalAdelicGL2_diagonal_split, map_mul, mul_assoc, mul_assoc,
        (adelicRealGL2_finite_commute g (rationalGL2ToFinite γ)).eq]
    _ = _ := adelicLiftCyclic_rational_invariant N f v.property γ _

/-- Actual finite-level invariance forces the reconstructed original classical function to satisfy every original Gamma0 slash equation. -/
theorem adelicCyclic_sublevel_classical_slash_invariant
    (L : Subgroup (finiteAdeleGL2Gamma0 N))
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : adelicCyclicHilbertEmbedding f v ∈ adelicSublevelFixedSpace f L)
    (F : ℍ → ℂ) (hF : realWeightLiftLinear k F = adelicCyclicRealRestriction f v)
    (γ : Gamma0 N) (hγ : integralGamma0FiniteGL2Hom N γ ∈ L) : F ∣[k] mapGL ℝ γ.val = F := by
  apply realWeightLift_injective k
  funext g
  have hr : rationalGL2ToReal (GeneralLinearGroup.map (Int.castRingHom ℚ) (toGL γ.val)) =
      toGL (integralToRealSL γ.val) := by
    apply Units.ext
    funext i j
    exact map_intCast (algebraMap ℚ ℝ) (γ.val i j)
  have hs : mapGL ℝ (integralToRealSL γ.val) = mapGL ℝ γ.val := by
    apply Units.ext
    rfl
  rw [← hs, ← realWeightLift_mul]
  change realWeightLiftLinear k F (integralToRealSL γ.val * g) = realWeightLiftLinear k F g
  rw [hF]
  change v.val (adelicRealSL2Embedding (integralToRealSL γ.val * g)) = v.val (adelicRealSL2Embedding g)
  have hi := adelicCyclic_real_rational_sublevel f L v hv
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (toGL γ.val))
    ⟨integralGamma0FiniteGL2Hom N γ, hγ⟩ (integralGamma0FiniteGL2Hom_val N γ) (toGL g)
  rw [hr, ← map_mul, adelicRealGL2Embedding_toGL, adelicRealGL2Embedding_toGL] at hi
  exact hi

end
end Dubon2026
