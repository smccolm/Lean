import Dubon2026.SourceValuationResidualAction
import Dubon2026.AlgebraicLocalInertia

/-! DUB-17/18 -> prescribed residual association -> exact norm-local
comparison. Pull back the actual local integer valuation through the
original global embedding. Norm invariance and literal residue congruences
transport the same automorphism's Frobenius and inertia conditions. -/
namespace Dubon2026
noncomputable section
attribute [local instance] algebraicLocalIntegerAction
variable {K L F : Type} [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L] [Field F] [Algebra ℚ F]
variable (e : F →+* L) (g : Gal(L/K)) (σ : Gal(F/ℚ))
  (he : ∀ x : F, e (σ x) = g (e x))
local notation "A" => ValuationSubring.comap (algebraicLocalIntegerRing L) e

include he

theorem norm_restriction_mem_decomposition : σ ∈ (A).decompositionSubgroup ℚ := by
  apply valuation_decomposition_of_mem_iff
  intro x
  change ‖e (σ x)‖₊ ≤ 1 ↔ ‖e x‖₊ ≤ 1
  have hn : ‖g (e x)‖₊ = ‖e x‖₊ :=
    NNReal.coe_injective (completeNonarchimedeanGalois_norm_map g (e x))
  rw [he, hn]

theorem norm_restriction_frobenius (q : ℕ)
    (hg : ∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing L), g • z = z ^ q) :
    ∃ hd : σ ∈ (A).decompositionSubgroup ℚ,
      ∀ z : IsLocalRing.ResidueField A,
        (⟨σ, hd⟩ : (A).decompositionSubgroup ℚ) • z = z ^ q := by
  refine ⟨norm_restriction_mem_decomposition e g σ he, ?_⟩
  apply (valuation_residue_power_iff A σ _ q).mpr
  intro x
  let y : algebraicLocalIntegerRing L := ⟨e x, x.property⟩
  have hy : g (y : L) - (y : L) ^ q ∈ (algebraicLocalIntegerRing L).nonunits := by
    change ((g • y - y ^ q : algebraicLocalIntegerRing L) : L) ∈ _
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, map_pow, sub_eq_zero, IsLocalRing.ResidueField.residue_smul]
    exact hg (IsLocalRing.residue _ y)
  apply (valuation_comap_nonunits_iff (algebraicLocalIntegerRing L) e _).mpr
  rw [map_sub, map_pow, he]
  exact hy

theorem norm_restriction_inertia (hg : g ∈ algebraicLocalInertia K L) :
    σ ∈ ((A).inertiaSubgroup ℚ).map ((A).decompositionSubgroup ℚ).subtype := by
  have h := norm_restriction_frobenius e g σ he 1 (by
    intro z
    simpa only [pow_one] using (algebraicLocalInertia_mem_iff K L g).mp hg z)
  rcases h with ⟨hd, hr⟩
  apply Subgroup.mem_map.mpr
  refine ⟨⟨σ, hd⟩, ?_, rfl⟩
  change MulSemiringAction.toRingAut ((A).decompositionSubgroup ℚ)
    (IsLocalRing.ResidueField A) ⟨σ, hd⟩ = 1
  apply RingEquiv.ext
  intro z
  simpa only [pow_one] using hr z

end
end Dubon2026
