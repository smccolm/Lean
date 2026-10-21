import Dubon2026.SourceModularRationalCusps
import Dubon2026.SourceManinOrbitCount

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual Galois association -> original parabolic Hecke
realization -> reverse period dimension inequality -> actual cusp potentials
and finite Manin relations. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index.lean
and Definitions/Def_ModularCurve_CuspSpace.lean. The target is the existing
original complex parabolic character space; no new cohomology model or
dimension assumption is introduced.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Matrix Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup OnePoint
open scoped MatrixGroups

variable (N : ℕ)

/-- The rational-matrix image of the original integral level subgroup. -/
def Gamma0Q : Subgroup (GL (Fin 2) ℚ) := (Gamma0 N).map (mapGL ℚ)

lemma mem_Gamma0Q {g : GL (Fin 2) ℚ} :
    g ∈ Gamma0Q N ↔ ∃ γ ∈ Gamma0 N, mapGL ℚ γ = g := Iff.rfl

/-- Original rational cusps modulo the actual level subgroup. -/
abbrev CuspSpace : Type := MulAction.orbitRel.Quotient (Gamma0Q N) (OnePoint ℚ)

namespace CuspSpace

/-- The level orbit of an original rational cusp. -/
def mk (x : OnePoint ℚ) : CuspSpace N := ⟦x⟧

lemma mk_surjective : Function.Surjective (mk N) := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩

variable {N}

lemma mk_eq_mk_iff {x y : OnePoint ℚ} :
    mk N x = mk N y ↔ ∃ γ ∈ Gamma0 N, mapGL ℚ γ • y = x := by
  rw [mk, mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, γ, hγ, rfl⟩, hg⟩
    exact ⟨γ, hγ, hg⟩
  · rintro ⟨γ, hγ, hg⟩
    exact ⟨⟨mapGL ℚ γ, γ, hγ, rfl⟩, hg⟩

lemma mk_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (x : OnePoint ℚ) :
    mk N (mapGL ℚ γ • x) = mk N x :=
  mk_eq_mk_iff.mpr ⟨γ, hγ, rfl⟩

variable (N)

lemma mk_smul_infty_eq_of_mem {a b : SL(2, ℤ)} (hab : a⁻¹ * b ∈ Gamma0 N) :
    mk N (mapGL ℚ a⁻¹ • ∞) = mk N (mapGL ℚ b⁻¹ • ∞) := by
  have key : mapGL ℚ b⁻¹ • (∞ : OnePoint ℚ)
      = mapGL ℚ (a⁻¹ * b)⁻¹ • (mapGL ℚ a⁻¹ • (∞ : OnePoint ℚ)) := by
    have h1 : (a⁻¹ * b)⁻¹ * a⁻¹ = b⁻¹ := by group
    rw [← mul_smul, ← map_mul, h1]
  rw [key]
  exact (mk_smul (inv_mem hab) _).symm

/-- The inverse-coset action at infinity maps actual integral cosets onto cusp orbits. -/
def fromCoset : SL(2, ℤ) ⧸ Gamma0 N → CuspSpace N :=
  Quotient.lift (fun g => mk N (mapGL ℚ g⁻¹ • ∞))
    (fun _ _ hab => mk_smul_infty_eq_of_mem N (QuotientGroup.leftRel_apply.mp hab))

@[simp] lemma fromCoset_mk (g : SL(2, ℤ)) :
    fromCoset N ((g : SL(2, ℤ) ⧸ Gamma0 N)) = mk N (mapGL ℚ g⁻¹ • ∞) := rfl

lemma fromCoset_surjective : Function.Surjective (fromCoset N) := by
  rintro ⟨x⟩
  obtain ⟨g, hg⟩ := OnePoint.exists_mem_SL2 ℤ x
  exact ⟨(g⁻¹ : SL(2, ℤ)), by rw [fromCoset_mk, inv_inv, hg]; rfl⟩

instance instFinite [NeZero N] : Finite (CuspSpace N) :=
  Finite.of_surjective _ (fromCoset_surjective N)

instance instNonempty : Nonempty (CuspSpace N) := ⟨mk N ∞⟩


end CuspSpace

end
end Dubon2026.SourceManin
