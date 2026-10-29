import Dubon2026.SourceGammaOneTwistedCongruence
import Mathlib.Topology.Algebra.Group.Basic

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
finite homogeneous-coefficient Galois realization. The genuine action on
the original finite Tate dual is continuous with its discrete topology.
The continuous actual cyclotomic character and the proved uniform Tate
congruences give an identity neighborhood; the native group theorem
propagates continuity to every Galois element. No continuity or finite
quotient representation is supplied as an input. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup IsLocalRing Filter
open scoped Topology
private theorem continuous_discrete_of_eventually_one {G A : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Monoid A] (ρ : G →* A)
    (h : ∀ᶠ σ in 𝓝 (1 : G), ρ σ = 1) : @Continuous G A _ ⊥ ρ := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  apply continuous_of_tendsto_nhds_one
  apply tendsto_const_nhds.congr'
  exact h.mono (fun _ he => he.symm)

private theorem one_congruence {R W G : Type*} [CommRing R] [AddCommGroup W]
    [Module R W] [Monoid G] (ρ : G →* Module.End R W) (U : Submodule R W) :
    ∀ x : W, ρ 1 x - x ∈ U := by
  intro x
  rw [map_one]
  change x - x ∈ U
  rw [sub_self]
  exact U.zero_mem

private theorem eventually_one_of_open_controls {G A B R W : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Monoid A]
    [Monoid B] [TopologicalSpace B] [DiscreteTopology B]
    [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : G →* A) (χ : G →ₜ* B) (τ : G →* Module.End R W) (U : Submodule R W)
    (ho : IsOpen {σ : G | ∀ x : W, τ σ x - x ∈ U})
    (hk : ∀ σ : G, χ σ = 1 → (∀ x : W, τ σ⁻¹ x - x ∈ U) → ρ σ = 1) :
    ∀ᶠ σ in 𝓝 (1 : G), ρ σ = 1 := by
  have hi := ho.preimage (continuous_inv : Continuous (fun σ : G => σ⁻¹))
  have hχ : IsOpen {σ : G | χ σ = 1} :=
    χ.continuous.isOpen_preimage {a | a = 1} (isOpen_discrete _)
  have hm : (1 : G) ∈ (fun σ : G => σ⁻¹) ⁻¹' {σ : G | ∀ x : W, τ σ x - x ∈ U} := by
    simpa only [Set.mem_preimage, inv_one, Set.mem_setOf_eq] using one_congruence τ U
  filter_upwards [hi.mem_nhds hm, hχ.mem_nhds χ.map_one] with σ hσ hc
  exact hk σ hc hσ

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Qbar" => AlgebraicClosure ℚ
local notation "G" => Qbar ≃ₐ[ℚ] Qbar
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "J" => Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar)
local notation "T" => TateModule p J

theorem binaryArithmeticTateGaloisRep_eventually_one :
    ∀ᶠ σ in 𝓝 (1 : G), binaryArithmeticTateGaloisRep Q p n w σ = 1 := by
  exact eventually_one_of_open_controls (binaryArithmeticTateGaloisRep Q p n w)
    (sourceAbsoluteCyclotomicCharacter N) (arithmeticTateGaloisRep M p)
    ((maximalIdeal ℤ_[p] ^ (n + 1)) • (⊤ : Submodule ℤ_[p] T))
    (arithmeticTateGalois_uniform_congruence_isOpen M p (n + 1))
    (binaryArithmeticTateGaloisRep_eq_one_of_congruence Q p n w)

theorem binaryArithmeticTateGaloisRep_continuous :
    @Continuous _ _ _ ⊥ (binaryArithmeticTateGaloisRep Q p n w).toFun :=
  continuous_discrete_of_eventually_one (binaryArithmeticTateGaloisRep Q p n w)
    (binaryArithmeticTateGaloisRep_eventually_one Q p n w)

end
end Dubon2026.SourceFunctionField.GammaOne
