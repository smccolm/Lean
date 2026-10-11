import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.Topology.Instances.ZMod

/-! # The genuine finite cyclotomic character is continuous in the Krull topology -/

namespace Dubon2026
noncomputable section
open Filter Topology

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {n : ℕ} [NeZero n] {μ : K}

/-- The actual finite cyclotomic character is independent of the chosen primitive
root and acts by its claimed exponent on every original primitive root. -/
theorem primitiveRootCyclotomicCharacter_apply_root (hμ : IsPrimitiveRoot μ n)
    (g : K ≃ₐ[F] K) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    g ζ = ζ ^ (hμ.autToPow F g : ZMod n).val := by
  have hc : hμ.autToPow F g = hζ.autToPow F g := by
    rw [hμ.autToPow_eq_modularCyclotomicCharacter n F g,
      hζ.autToPow_eq_modularCyclotomicCharacter n F g]
  rw [hc]
  exact (hζ.autToPow_spec F g).symm

/-- The kernel is exactly the stabilizer of the actual primitive root. Hence it
is open in the original Krull topology for an algebraic field extension. -/
theorem primitiveRootCyclotomicCharacter_isOpen_ker [Algebra.IsIntegral F K]
    (hμ : IsPrimitiveRoot μ n) :
    IsOpen ((hμ.autToPow F).ker : Set (K ≃ₐ[F] K)) := by
  have hker : ((hμ.autToPow F).ker : Set (K ≃ₐ[F] K)) =
      (MulAction.stabilizer (K ≃ₐ[F] K) μ : Set (K ≃ₐ[F] K)) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      have he : hμ.autToPow F g = hμ.autToPow F 1 := hg.trans (map_one _).symm
      change g μ = μ
      rw [← hμ.autToPow_spec F g, he, hμ.autToPow_spec F 1]
      rfl
    · intro hg
      have he : hμ.autToPow F g = hμ.autToPow F 1 := by
        apply Units.ext
        apply ZMod.val_injective
        apply hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
        rw [hμ.autToPow_spec F g, hμ.autToPow_spec F 1]
        exact hg
      exact he.trans (map_one _)
  rw [hker]
  exact stabilizer_isOpen_of_isIntegral (K := F) μ

/-- Openness of the true root stabilizer proves continuity of the entire genuine
cyclotomic character. No continuous-character hypothesis is supplied. -/
theorem primitiveRootCyclotomicCharacter_continuous [Algebra.IsIntegral F K]
    (hμ : IsPrimitiveRoot μ n) : Continuous (hμ.autToPow F) := by
  apply continuous_of_tendsto_nhds_one
  apply tendsto_const_nhds.congr'
  filter_upwards [(primitiveRootCyclotomicCharacter_isOpen_ker (F := F) hμ).mem_nhds
    (Subgroup.one_mem _)] with g hg
  exact (MonoidHom.mem_ker.mp hg).symm

end
end Dubon2026
