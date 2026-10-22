import Dubon2026.SourceOriginalTateGalois
import Dubon2026.SourceTateProjections
import Dubon2026.SourceOriginalTateRank

/-! DUB-17/18 -> actual modular Galois realization -> original Tate continuity.
The exact projection kernel identifies finite torsion stabilizers with p-adic
congruence conditions on the original Tate action. The already proved finite
fields of definition make each such condition open in the arithmetic Galois group.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IsLocalRing
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "T" => TateModule p (originalJZero N)

theorem originalTate_congruence_iff (n : ℕ) (σ : Qbar ≃ₐ[ℚ] Qbar) (x : T) :
    originalTateGaloisRep N p σ x - x ∈
        (maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] T) ↔
      originalArithmeticPicard N σ ((x : ℕ → originalJZero N) n) =
        (x : ℕ → originalJZero N) n := by
  rw [← TateModule.proj_eq_zero_iff, map_sub, sub_eq_zero]
  rfl

theorem originalTateGalois_congruence_isOpen (n : ℕ) (x : T) :
    IsOpen {σ : Qbar ≃ₐ[ℚ] Qbar | originalTateGaloisRep N p σ x - x ∈
      (maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] T)} := by
  have he : {σ : Qbar ≃ₐ[ℚ] Qbar | originalTateGaloisRep N p σ x - x ∈
      (maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] T)} =
      (MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) ((x : ℕ → originalJZero N) n) :
        Set (Qbar ≃ₐ[ℚ] Qbar)) := by
    ext σ
    exact originalTate_congruence_iff N p n σ x
  rw [he]
  exact originalJZero_isOpen_stabilizer N ((x : ℕ → originalJZero N) n)

theorem originalTateGalois_uniform_congruence_isOpen (n : ℕ) :
    IsOpen {σ : Qbar ≃ₐ[ℚ] Qbar | ∀ x : T, originalTateGaloisRep N p σ x - x ∈
      (maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] T)} := by
  obtain ⟨hfree, hfinite, _⟩ := OriginalChart.original_tate_free_finite_rank N p
  letI : Module.Free ℤ_[p] T := hfree
  letI : Module.Finite ℤ_[p] T := hfinite
  let b := Module.finBasis ℤ_[p] T
  let U := (maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] T)
  have he : {σ : Qbar ≃ₐ[ℚ] Qbar | ∀ x : T, originalTateGaloisRep N p σ x - x ∈ U} =
      ⋂ i, {σ : Qbar ≃ₐ[ℚ] Qbar | originalTateGaloisRep N p σ (b i) - b i ∈ U} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · exact fun h i => h (b i)
    · intro h x
      let f : T →ₗ[ℤ_[p]] T := originalTateGaloisRep N p σ - LinearMap.id
      have hu : U.comap f = ⊤ := (Submodule.eq_top_iff_forall_basis_mem b).mpr h
      have hx : x ∈ U.comap f := by rw [hu]; exact Submodule.mem_top
      exact hx
  change IsOpen {σ : Qbar ≃ₐ[ℚ] Qbar | ∀ x : T, originalTateGaloisRep N p σ x - x ∈ U}
  rw [he]
  exact isOpen_iInter_of_finite (fun i => originalTateGalois_congruence_isOpen N p n (b i))

end
end Dubon2026.SourceFunctionField
