import Dubon2026.SourceJointChartOrderSpaces
import Dubon2026.SourceJointChartMonicTorsion

/-! DUB-17/18 -> Picard torsion injectivity -> original-field Kummer
power lifting -> genus inequality -> two-chart dimension comparison.
These helpers identify the actual residue chart windows with products of
pole spaces. Adapted from Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Existing valuation-ring closure
replaces separate order-addition and scalar-order lemmas. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open Polynomial
universe u v w

section Concrete

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
  (R : ∀ i, RegularProlongation A F (Fb i))

local notation "𝕜" => IsLocalRing.ResidueField A

/-- The actual simultaneous residue vector of a common integral element. -/
def rv (g : F) (hg : ∀ i, g ∈ (R i).integers) : ∀ i, Fb i := fun i => (R i).residue ⟨g, hg i⟩

@[scoped simp] theorem rv_apply (g : F) (hg : ∀ i, g ∈ (R i).integers) (i : ι) :
    rv R g hg i = (R i).residue ⟨g, hg i⟩ := rfl

/-- Residue span of the original coordinate chart. -/
def ST (g : F) : Submodule 𝕜 (∀ i, Fb i) :=
  Submodule.span 𝕜 {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
    (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) ∧
    ∀ i, (R i).residue ⟨u, hu i⟩ = h i}

variable {R}

theorem ne_zero_of_residue_ne_zero {g : F} {hg : ∀ i, g ∈ (R i).integers} {i : ι}
    (h : (R i).residue ⟨g, hg i⟩ ≠ 0) : g ≠ 0 := by
  rintro rfl
  apply h
  have h0 : (⟨(0 : F), hg i⟩ : (R i).integers) = 0 := Subtype.ext (by simp)
  rw [h0, map_zero]

theorem inv_mem_integers {g : F} {hg : ∀ i, g ∈ (R i).integers}
    (h : ∀ i, (R i).residue ⟨g, hg i⟩ ≠ 0) (i : ι) : g⁻¹ ∈ (R i).integers := by
  obtain ⟨b, hb⟩ := ((R i).isUnit_of_residue_ne_zero (h i)).exists_right_inv
  have hb' : g * (b : F) = 1 := by simpa using congrArg Subtype.val hb
  rw [inv_eq_of_mul_eq_one_right hb']
  exact b.2

theorem residue_inv {g : F} {hg : ∀ i, g ∈ (R i).integers}
    (h : ∀ i, (R i).residue ⟨g, hg i⟩ ≠ 0) (i : ι) :
    (R i).residue ⟨g⁻¹, inv_mem_integers h i⟩ = ((R i).residue ⟨g, hg i⟩)⁻¹ := by
  have hg0 : g ≠ 0 := ne_zero_of_residue_ne_zero (h i)
  have hmul : (⟨g, hg i⟩ : (R i).integers) * ⟨g⁻¹, inv_mem_integers h i⟩ = 1 :=
    Subtype.ext (by simp [hg0])
  have := congrArg (R i).residue hmul
  rw [map_mul, map_one] at this
  exact (inv_eq_of_mul_eq_one_right this).symm

theorem transcendental_inv {K E : Type*} [Field K] [Field E] [Algebra K E] {x : E}
    (hx : Transcendental K x) : Transcendental K x⁻¹ :=
  fun h => hx (by simpa using h.inv)

theorem ne_zero_of_transcendental {K E : Type*} [Field K] [Field E] [Algebra K E] {x : E}
    (hx : Transcendental K x) : x ≠ 0 := by
  rintro rfl
  exact hx isAlgebraic_zero

theorem ST_map_le (g : F) (hg : ∀ i, g ∈ (R i).integers) (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0)
    (hug : ∀ i, (R i).residue ⟨g, hg i⟩ = u i) :
    (ST R g).map (mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ≤ ST R g := by
  rw [ST, Submodule.map_span_le]
  rintro h ⟨u', hu', hV', hres'⟩
  refine Submodule.subset_span ⟨g * u', fun i => mul_mem (hg i) (hu' i),
    fun V hL hgV => mul_mem hgV (hV' V hL hgV), fun i => ?_⟩
  rw [LinearEquiv.coe_coe, mulEquiv_apply, Pi.mul_apply, ← hug i, ← hres' i, ← map_mul]
  rfl

theorem setM_eq (f : F) (hf : ∀ i, f ∈ (R i).integers) (hf' : ∀ i, f⁻¹ ∈ (R i).integers)
    (hf0 : f ≠ 0) (M : ℕ) :
    {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          u * (f ^ M)⁻¹ ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} =
    (fun h => rv R f hf ^ M * h) '' {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  ext h
  constructor
  · rintro ⟨u, hu, hV, hres⟩
    have hm : ∀ i, u * (f ^ M)⁻¹ ∈ (R i).integers := fun i => by
      rw [← inv_pow]; exact mul_mem (hu i) (pow_mem (hf' i) M)
    refine ⟨fun i => (R i).residue ⟨u * (f ^ M)⁻¹, hm i⟩, ⟨u * (f ^ M)⁻¹, hm, hV, fun i => rfl⟩,
      ?_⟩
    ext i
    show (rv R f hf ^ M * fun i => (R i).residue ⟨u * (f ^ M)⁻¹, hm i⟩) i = h i
    rw [Pi.mul_apply, Pi.pow_apply, rv_apply, ← hres i, ← map_pow, ← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    rw [mul_left_comm, mul_inv_cancel₀ (pow_ne_zero M hf0), mul_one]
  · rintro ⟨h', ⟨u', hu', hV', hres'⟩, rfl⟩
    refine ⟨u' * f ^ M, fun i => mul_mem (hu' i) (pow_mem (hf i) M), fun V hL hfV => ?_,
      fun i => ?_⟩
    · rw [mul_inv_cancel_right₀ (pow_ne_zero M hf0)]
      exact hV' V hL hfV
    · show _ = (rv R f hf ^ M * h') i
      rw [Pi.mul_apply, Pi.pow_apply, rv_apply, ← hres' i, ← map_pow, ← map_mul]
      congr 1
      apply Subtype.ext
      push_cast
      ring

theorem span_setM_eq (f : F) (hf : ∀ i, f ∈ (R i).integers) (hf' : ∀ i, f⁻¹ ∈ (R i).integers)
    (hf0 : f ≠ 0) (hu : ∀ i, rv R f hf i ≠ 0) (M : ℕ) :
    Submodule.span 𝕜 {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          u * (f ^ M)⁻¹ ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} =
    (ST R f⁻¹).map ((mulEquiv (k := 𝕜) (rv R f hf) hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M) := by
  rw [ST, Submodule.map_span, setM_eq f hf hf' hf0 M]
  congr 1
  refine Set.image_congr fun h _ => ?_
  exact (mulEquiv_pow_apply (k := 𝕜) (rv R f hf) hu M h).symm

theorem tor_of_pointwise {k : Type*} [Field k] [∀ i, Algebra k (Fb i)] (u : ∀ i, Fb i)
    (hu : ∀ i, u i ≠ 0) (P B : Submodule k (∀ i, Fb i))
    (h : ∀ y : ∀ i, Fb i, ∃ c : k[X], c.Monic ∧ (fun i => aeval (u i) c * y i) ∈ P) :
    ∀ y ∈ B, ∃ c : k[X], c.Monic ∧
      aeval (mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) c y ∈ P := fun y _ => by
  obtain ⟨c, hc, hy⟩ := h y
  exact ⟨c, hc, by rwa [aeval_mulEquiv_apply]⟩

end Concrete

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
