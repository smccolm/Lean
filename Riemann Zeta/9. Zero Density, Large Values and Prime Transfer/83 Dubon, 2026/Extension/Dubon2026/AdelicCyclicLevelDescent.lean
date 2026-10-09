import Dubon2026.AdelicFiniteClassicalRestriction

/-! # Original finite-level Hilbert invariance descends to actual classical invariance -/

namespace Dubon2026

noncomputable section
open NumberField Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The original rational diagonal matrix factors into its literal real and finite embeddings. -/
theorem rationalAdelicGL2_diagonal_split (γ : GeneralLinearGroup (Fin 2) ℚ) :
    GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ =
      adelicRealGL2Embedding (rationalGL2ToReal γ) *
        rationalAdelicFiniteGL2Embedding (rationalGL2ToFinite γ) := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  rw [rationalAdelicGL2RealFiniteEquiv_rational, map_mul,
    adelicRealGL2Embedding_coordinates, rationalAdelicFiniteGL2Embedding_coordinates]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Faithfulness of the original completion turns its fixed-level equation into literal right invariance of its actual adelic function. -/
theorem adelicCyclic_level_pointwise
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : adelicCyclicHilbertEmbedding f v ∈ adelicLevelFixedSpace f)
    (a : finiteAdeleGL2Gamma0 N) (g : RationalAdelicGL2) :
    v.val (g * rationalAdelicFiniteGL2Embedding a.val) = v.val g := by
  have h := (mem_adelicLevelFixedSpace f _).mp hv a
  rw [adelicCyclicHilbertEmbedding_intertwines] at h
  have he := adelicCyclicHilbertEmbedding_injective f h
  exact congrFun (congrArg Subtype.val he) g

/-- The genuine real restriction is invariant under every rational real matrix whose finite component belongs to the original level group. -/
theorem adelicCyclic_real_rational_level
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : adelicCyclicHilbertEmbedding f v ∈ adelicLevelFixedSpace f)
    (γ : GeneralLinearGroup (Fin 2) ℚ) (hγ : rationalGL2ToFinite γ ∈ finiteAdeleGL2Gamma0 N)
    (g : GeneralLinearGroup (Fin 2) ℝ) :
    v.val (adelicRealGL2Embedding (rationalGL2ToReal γ * g)) =
      v.val (adelicRealGL2Embedding g) := by
  calc
    _ = v.val (adelicRealGL2Embedding (rationalGL2ToReal γ * g) *
        rationalAdelicFiniteGL2Embedding (rationalGL2ToFinite γ)) :=
      (adelicCyclic_level_pointwise f v hv ⟨_, hγ⟩ _).symm
    _ = v.val (GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) γ *
        adelicRealGL2Embedding g) := by
      rw [rationalAdelicGL2_diagonal_split, map_mul, mul_assoc, mul_assoc,
        (adelicRealGL2_finite_commute g (rationalGL2ToFinite γ)).eq]
    _ = _ := adelicLiftCyclic_rational_invariant N f v.property γ _

/-- The finite component of an original integral Gamma0 matrix is in the actual GL2 level group. -/
theorem integralGamma0_rationalGL2_finite_level (γ : Gamma0 N) :
    rationalGL2ToFinite (GeneralLinearGroup.map (Int.castRingHom ℚ) (toGL γ.val)) ∈
      finiteAdeleGL2Gamma0 N := by
  have he : rationalGL2ToFinite (GeneralLinearGroup.map (Int.castRingHom ℚ) (toGL γ.val)) =
      toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) γ.val) := by
    apply Units.ext
    funext i j
    exact map_intCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (γ.val i j)
  rw [he]
  exact finiteAdeleGamma0_toGL_mem N _ ((integralSL2_mem_finiteAdeleGamma0 N γ.val).mpr γ.property)

/-- Actual finite-level invariance forces the reconstructed original classical function to satisfy every original Gamma0 slash equation. -/
theorem adelicCyclic_classical_slash_invariant
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : adelicCyclicHilbertEmbedding f v ∈ adelicLevelFixedSpace f)
    (F : ℍ → ℂ) (hF : realWeightLiftLinear k F = adelicCyclicRealRestriction f v)
    (γ : Gamma0 N) : F ∣[k] mapGL ℝ γ.val = F := by
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
  have hi := adelicCyclic_real_rational_level f v hv
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (toGL γ.val))
    (integralGamma0_rationalGL2_finite_level γ) (toGL g)
  rw [hr, ← map_mul, adelicRealGL2Embedding_toGL, adelicRealGL2Embedding_toGL] at hi
  exact hi

end
end Dubon2026
