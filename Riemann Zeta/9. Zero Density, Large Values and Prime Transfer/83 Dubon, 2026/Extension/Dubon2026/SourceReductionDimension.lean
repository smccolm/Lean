import Dubon2026.SourceReductionPolynomialCover
import Dubon2026.SourceReductionSubspaceBasis
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> arithmetic automorphy and residual association -> original
weight-two Frobenius/inertia -> actual good reduction -> genus comparison ->
preservation of dimensions under coefficient reduction. These lemmas serve
that finite-space dimension theorem; no genus or good-reduction claim is made.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native polynomial monomial independence
replaces the external custom coefficient linear-combination equivalence. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

variable (R : RegularProlongation A F Fbar)

theorem finrank_span_residue_eq_finrank' (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (ResidueField A)
        (Submodule.span (ResidueField A)
          {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) =
      Module.finrank L V := by
  classical
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)

  let yb := Module.finBasis
    (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar
  choose y hy using fun i => R.residue_surjective (yb i)
  have hyind : LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
      (fun i => R.residue (y i)) := by
    have : (fun i => R.residue (y i)) = yb := funext hy
    rw [this]
    exact yb.linearIndependent

  have hrank : Module.rank (ResidueField A)
      (Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) ≤ Module.finrank L V := by
    apply rank_le
    intro s hs
    have hmem := fun i : s => mem_of_mem_span R V (i : Submodule.span (ResidueField A) _).2
    choose f hfV hfres using hmem
    have hind : LinearIndependent (ResidueField A) (fun i : s => R.residue (f i)) := by
      have : (fun i : s => R.residue (f i)) =
          (Submodule.span (ResidueField A)
            {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}).subtype ∘
            (fun i : s => (i : Submodule.span (ResidueField A) _)) := by
        funext i
        simp [hfres]
      rw [this]
      exact hs.map' _ (Submodule.ker_subtype _)
    have h := card_le_finrank R V f hfV hind
    simpa using h
  haveI hfinS : Module.Finite (ResidueField A)
      (Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0)
  apply le_antisymm (Module.finrank_le_of_rank_le hrank)

  obtain ⟨U, hU, _, T, hT⟩ := exists_unit_mul_mem_span R x hx y hyind hdeg V
  have hUne : (U : F) ≠ 0 := by
    intro h
    apply hU
    rw [show U = 0 from Subtype.ext h, map_zero]
  let μ : F →ₗ[L] F := LinearMap.mulLeft L (U : F)
  have hμinj : Function.Injective μ := mul_right_injective₀ hUne
  have hWfin : Module.finrank L (V.map μ) = Module.finrank L V :=
    (Submodule.equivMapOfInjective μ hμinj V).finrank_eq.symm
  let ET : T → R.integers := fun p => frame R x y p.1
  have hET : LinearIndependent (ResidueField A) (fun p : T => R.residue (ET p)) :=
    (linearIndependent_residue_frame R x hx y hyind).comp _ Subtype.val_injective
  have hWle : V.map μ ≤ Submodule.span L (Set.range fun p : T => (ET p : F)) := by
    have hrange : (Set.range fun p : T => (ET p : F)) =
        Set.range fun p : T => (x : F) ^ p.1.1 * (y p.1.2 : F) := by
      congr 1
    rw [hrange]
    rintro _ ⟨v, hv, rfl⟩
    exact hT v hv
  obtain ⟨g, hgW, hgind⟩ := exists_residue_linearIndependent R ET hET (V.map μ) hWle hWfin

  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hU
  have hg'V : ∀ a, ((↑u⁻¹ * g a : R.integers) : F) ∈ V := by
    intro a
    obtain ⟨v, hv, hgv⟩ := hgW a
    have h1 : ((↑u⁻¹ * g a : R.integers) : F) = v := by
      have huinv : ((↑u⁻¹ : R.integers) : F) * (U : F) = 1 := by
        rw [← hu, ← Subring.coe_mul, Units.inv_mul]
        rfl
      rw [Subring.coe_mul, ← hgv]
      change ((↑u⁻¹ : R.integers) : F) * ((U : F) * v) = v
      rw [← mul_assoc, huinv, one_mul]
    rw [h1]
    exact hv
  have hg'ind : LinearIndependent (ResidueField A) (fun a => R.residue (↑u⁻¹ * g a)) := by
    have hru : R.residue ↑u⁻¹ ≠ 0 := R.residue_ne_zero_of_isUnit (Units.isUnit _)
    rw [Fintype.linearIndependent_iff] at hgind ⊢
    intro κ hκ
    apply hgind κ
    have : ∑ a, κ a • R.residue (↑u⁻¹ * g a) = R.residue ↑u⁻¹ * ∑ a, κ a • R.residue (g a) := by
      simp only [map_mul, Finset.mul_sum, mul_smul_comm]
    rw [this] at hκ
    exact (mul_eq_zero.mp hκ).resolve_left hru
  have hmemS : ∀ a, R.residue (↑u⁻¹ * g a) ∈ Submodule.span (ResidueField A)
      {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h} :=
    fun a => Submodule.subset_span ⟨_, hg'V a, rfl⟩
  have hind2 : LinearIndependent (ResidueField A)
      (fun a => (⟨R.residue (↑u⁻¹ * g a), hmemS a⟩ : Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h})) :=
    LinearIndependent.of_comp (Submodule.span (ResidueField A) _).subtype hg'ind
  have h := hind2.fintype_card_le_finrank
  simpa using h


end
end Dubon2026.SourceCurve.RegularProlongation
