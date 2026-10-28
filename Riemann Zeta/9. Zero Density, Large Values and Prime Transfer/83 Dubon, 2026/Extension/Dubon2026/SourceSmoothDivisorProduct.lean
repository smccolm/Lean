import Dubon2026.SourceSmoothDivisorOrbitData
import Dubon2026.SourceSmoothLocalModelProducts
import Dubon2026.SourceSmoothModularLogDerivative

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
The actual product uses the projective image of the original integral subgroup,
with representatives from the proved projection/fiber equivalence. Its raw
invariance follows by group translation. The data record contains only finite
divisor data and the separately constructed compact dipoles, not the desired
global comparison-function properties. Adapted from the pinned Apache-2.0
scope-889 construction, replacing its positive-matrix representative system. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set
open SourceSmoothProjective SourceSmoothedUnfolding SourceSmoothLocalModel
open scoped MatrixGroups Topology Real
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet
local notation "dbar" => SourceComplexReciprocity.DbarFundamental.D

/-- Actual compact dipoles and finite divisor data; no orbit-product conclusion is assumed. -/
structure Data (Γ : Subgroup SL(2, ℤ)) where
  /-- The integral subgroup contains the central negative identity. -/
  hneg : (-1 : SL(2, ℤ)) ∈ Γ
  /-- Finite representatives of the prescribed nonzero orders. -/
  S : Finset ℍ
  /-- The actual invariant integer-order function. -/
  n : ℍ → ℤ
  /-- The auxiliary base point outside all chosen orbits. -/
  b : ℍ
  /-- Integer multiplicities normalized by stabilizer order. -/
  mS : ℍ → ℤ
  /-- Actual compact smooth dipoles at the chosen points. -/
  dip : ℍ → ℂ → ℂ
  /-- Their antiholomorphic logarithmic derivative coefficients. -/
  Fk : ℍ → ℂ → ℂ
  /-- Their compact supports in the upper half-plane. -/
  Kk : ℍ → Set ℂ
  /-- Invariance of the prescribed integer orders. -/
  hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ
  /-- The finite chosen orbits cover all nonzero orders. -/
  hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ
  /-- The chosen representatives have distinct subgroup orbits. -/
  hinj : ∀ s ∈ S, ∀ t ∈ S, (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t
  /-- Exact stabilizer-normalized integer multiplicity. -/
  hmS : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) * mS s = 2 * n s
  /-- Degree-zero cancellation of the base-point multiplicity. -/
  hsum : ∑ s ∈ S, mS s = 0
  /-- The base point lies outside all chosen full modular orbits. -/
  hb : ∀ s ∈ S, ∀ γ : SL(2, ℤ), γ • s ≠ b
  /-- Each dipole support is compact. -/
  hKc : ∀ s ∈ S, IsCompact (Kk s)
  /-- Every dipole support lies in the upper half-plane. -/
  hKU : ∀ s ∈ S, Kk s ⊆ 𝕌
  /-- The dipole equals one off its compact support. -/
  hd1 : ∀ s ∈ S, ∀ z ∉ Kk s, dip s z = 1
  /-- Each dipole has exactly its zero and pole local integer orders. -/
  hloc : ∀ s ∈ S, ∀ τ : ℂ, 0 < τ.im → ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
    dip s =ᶠ[𝓝 τ] fun z =>
      (z - τ) ^ ((if τ = (s : ℂ) then (1 : ℤ) else 0) - (if τ = (b : ℂ) then (1 : ℤ) else 0)) * Ψ z
  /-- The coefficient support lies in the same compact set. -/
  hFt : ∀ s ∈ S, tsupport (Fk s) ⊆ Kk s
  /-- The actual dipole logarithmic derivative equals its coefficient away from the pole. -/
  hFeq : ∀ s ∈ S, ∀ z : ℂ, 0 < z.im → z ≠ b → dbar (dip s) z / dip s z = Fk s z

namespace Data

open scoped Classical

variable {Γ : Subgroup SL(2, ℤ)} (D : Data Γ)

/-- The actual signed local exponent of a dipole. -/
def ex (s : ℍ) (τ : ℂ) : ℤ :=
  (if τ = (s : ℂ) then (1 : ℤ) else 0) - (if τ = (D.b : ℂ) then (1 : ℤ) else 0)

/-- The dipole translated by an actual projective group representative. -/
def fac (s : ℍ) (δ : projectiveIntegralSubgroup Γ) (z : ℂ) : ℂ := D.dip s (sm (representative Γ δ) z) ^ D.mS s

/-- The locally finite projective orbit product of compact dipoles. -/
def Vraw (z : ℂ) : ℂ := ∏ s ∈ D.S, ∏ᶠ δ : projectiveIntegralSubgroup Γ, D.fac s δ z

/-- Fill the removable finite limits of the actual orbit product. -/
def V : ℂ → ℂ := regularize D.Vraw

theorem s_ne_b {s : ℍ} (hs : s ∈ D.S) : (s : ℂ) ≠ D.b := by
  intro h
  exact D.hb s hs 1 (by rw [one_smul]; exact UpperHalfPlane.ext h)

theorem dip_s {s : ℍ} (hs : s ∈ D.S) : D.dip s s = 0 := by
  obtain ⟨Ψ, -, -, h⟩ := D.hloc s hs s s.im_pos
  have := h.self_of_nhds
  simp only [sub_self, if_neg (D.s_ne_b hs)] at this
  simpa using this

theorem dip_b {s : ℍ} (hs : s ∈ D.S) : D.dip s D.b = 0 := by
  obtain ⟨Ψ, -, -, h⟩ := D.hloc s hs D.b D.b.im_pos
  have := h.self_of_nhds
  simp only [sub_self, if_neg (D.s_ne_b hs).symm] at this
  simpa using this

theorem sK {s : ℍ} (hs : s ∈ D.S) : (s : ℂ) ∈ D.Kk s := by
  by_contra h
  have := D.hd1 s hs _ h
  rw [D.dip_s hs] at this
  exact zero_ne_one this

theorem bK {s : ℍ} (hs : s ∈ D.S) : (D.b : ℂ) ∈ D.Kk s := by
  by_contra h
  have := D.hd1 s hs _ h
  rw [D.dip_b hs] at this
  exact zero_ne_one this

theorem heights {s : ℍ} (hs : s ∈ D.S) :
    ∃ ε B : ℝ, 0 < ε ∧ ∀ w ∈ D.Kk s, ε ≤ w.im ∧ w.im ≤ B := by
  have hK := D.hKc s hs
  have hne : (D.Kk s).Nonempty := ⟨_, D.sK hs⟩
  obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨w₁, hw₁, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_im.continuousOn
  exact ⟨w₀.im, w₁.im, D.hKU s hs hw₀, fun w hw => ⟨hmin hw, hmax hw⟩⟩

theorem fac_sm (s : ℍ) (q : projectiveIntegralSubgroup Γ) (γ : Γ) (z : ℂ) :
    D.fac s q (sm γ z) = D.fac s (q * projection Γ γ) z := by
  simp only [fac, sm, ofComplex_apply, representative_smul]
  change D.dip s (((q • ((projection Γ γ) • ofComplex z) : ℍ) : ℂ)) ^ D.mS s =
    D.dip s ((((q * projection Γ γ) • ofComplex z : ℍ) : ℂ)) ^ D.mS s
  rw [mul_smul]

theorem Vraw_sm (γ : Γ) (z : ℂ) : D.Vraw (sm γ z) = D.Vraw z := by
  simp only [Vraw]
  refine Finset.prod_congr rfl fun s _ => ?_
  exact finprod_eq_of_bijective _ (Equiv.mulRight (projection Γ γ)).bijective
    fun q => D.fac_sm s q γ z

end Data
end
end Dubon2026.SourceSmoothDivisor
