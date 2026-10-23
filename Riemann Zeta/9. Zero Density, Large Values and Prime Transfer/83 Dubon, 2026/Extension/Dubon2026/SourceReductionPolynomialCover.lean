import Dubon2026.SourceReductionFrame
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

section covering

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

include hx in

theorem exists_normalize_aeval (q : Polynomial L) (hq : q ≠ 0) :
    ∃ U : R.integers, R.residue U ≠ 0 ∧ ∃ c : L, c ≠ 0 ∧
      (U : F) = algebraMap L F c⁻¹ * Polynomial.aeval (x : F) q := by
  classical
  set t := Finset.range (q.natDegree + 1) with ht
  have hi₀ : q.natDegree ∈ t := Finset.self_mem_range_succ _
  have hg : q.coeff q.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j₁, hj₁t, hj₁, hcA, -⟩ := exists_normalizer (A := A) t (fun j => q.coeff j) hi₀ hg
  let a : ℕ → A := fun j => if hj : j ∈ t then ⟨(q.coeff j₁)⁻¹ * q.coeff j, hcA j hj⟩ else 0
  refine ⟨∑ j ∈ t, constHom R (a j) * x ^ j, ?_, q.coeff j₁, hj₁, ?_⟩
  · intro h0
    have hE := linearIndependent_residue_pow R x hx
    have h1 := residue_coeff_eq_zero R (fun j : ℕ => x ^ j) hE t a h0 j₁ hj₁t
    have ha1 : a j₁ = 1 := by
      apply Subtype.ext
      simp [a, dif_pos hj₁t, inv_mul_cancel₀ hj₁]
    rw [ha1, map_one] at h1
    exact one_ne_zero h1
  · rw [coe_sum_constHom_mul, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ∈ t := hj
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [a, dif_pos hj', map_mul]
    push_cast
    ring

include hx hy in

theorem exists_unit_mul_mem_span
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (V : Submodule L F) [FiniteDimensional L V] :
    ∃ U : R.integers, R.residue U ≠ 0 ∧
      (U : F) ∈ IntermediateField.adjoin L ({(x : F)} : Set F) ∧
      ∃ T : Finset (ℕ × Fin n),
      ∀ v ∈ V, (U : F) * v ∈
        Submodule.span L (Set.range fun p : T => (x : F) ^ p.1.1 * (y p.1.2 : F)) := by
  classical
  let bV := Module.finBasis L V

  choose r hr using
    fun a : Fin (Module.finrank L V) => exists_repr_adjoinField R x hx y hy hcard ((bV a : V) : F)

  have hfrac : ∀ a i, ∃ PQ : Polynomial L × Polynomial L, Polynomial.aeval (x : F) PQ.2 ≠ 0 ∧
      (r a i : F) = Polynomial.aeval (x : F) PQ.1 / Polynomial.aeval (x : F) PQ.2 := by
    intro a i
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L (r a i : F)).mp (r a i).2
    by_cases hQ : Polynomial.aeval (x : F) Q = 0
    · refine ⟨(0, 1), by simp, ?_⟩
      rw [hPQ, hQ, div_zero]
      simp
    · exact ⟨(P, Q), hQ, hPQ⟩
  choose PQ hQne hPQ using hfrac

  set q : Polynomial L := ∏ p : Fin (Module.finrank L V) × Fin n, (PQ p.1 p.2).2 with hqdef
  have haevalq : Polynomial.aeval (x : F) q =
      ∏ p : Fin (Module.finrank L V) × Fin n, Polynomial.aeval (x : F) (PQ p.1 p.2).2 := by
    rw [hqdef, map_prod]
  have hqx : Polynomial.aeval (x : F) q ≠ 0 := by
    rw [haevalq]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => hQne p.1 p.2
  have hq0 : q ≠ 0 := by
    rintro h
    rw [h, map_zero] at hqx
    exact hqx rfl
  obtain ⟨U, hU, c, hc, hUq⟩ := exists_normalize_aeval R x hx q hq0

  obtain ⟨H, hH⟩ : ∃ H : Fin (Module.finrank L V) → Fin n → Polynomial L,
      ∀ a i, (U : F) * ((r a i : F) * (y i : F)) =
        Polynomial.aeval (x : F) (H a i) * (y i : F) := by
    refine ⟨fun a i => Polynomial.C c⁻¹ *
      ((∏ p ∈ Finset.univ.erase (a, i), (PQ p.1 p.2).2) * (PQ a i).1), fun a i => ?_⟩
    rw [hUq, hPQ a i, ← mul_assoc]
    congr 1
    simp only [map_mul, Polynomial.aeval_C, map_prod]
    rw [haevalq, ← Finset.mul_prod_erase Finset.univ
      (fun p : Fin (Module.finrank L V) × Fin n => Polynomial.aeval (x : F) (PQ p.1 p.2).2)
      (Finset.mem_univ (a, i))]
    have hQ := hQne a i
    field_simp
  have hN : ∃ N : ℕ, ∀ a i, (H a i).natDegree < N := by
    let g : Fin (Module.finrank L V) × Fin n → ℕ := fun p => (H p.1 p.2).natDegree
    refine ⟨Finset.univ.sup g + 1, fun a i => Nat.lt_succ_of_le ?_⟩
    exact Finset.le_sup (f := g) (Finset.mem_univ (a, i))
  obtain ⟨N, hlt⟩ := hN
  have hULx : (U : F) ∈ IntermediateField.adjoin L ({(x : F)} : Set F) := by
    rw [hUq]
    refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    rw [Polynomial.aeval_eq_sum_range]
    refine sum_mem fun j _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (pow_mem (IntermediateField.mem_adjoin_simple_self L (x : F)) _)
  refine ⟨U, hU, hULx, Finset.range N ×ˢ Finset.univ, ?_⟩
  let S : Submodule L F := Submodule.span L
    (Set.range fun p : ↥(Finset.range N ×ˢ (Finset.univ : Finset (Fin n))) =>
      (x : F) ^ p.1.1 * (y p.1.2 : F))
  change ∀ v ∈ V, (U : F) * v ∈ S
  have hgen : ∀ j < N, ∀ i, (x : F) ^ j * (y i : F) ∈ S := by
    intro j hj i
    apply Submodule.subset_span
    exact ⟨⟨(j, i), Finset.mk_mem_product (Finset.mem_range.mpr hj) (Finset.mem_univ i)⟩, rfl⟩
  have hbasis : ∀ a, (U : F) * ((bV a : V) : F) ∈ S := by
    intro a
    rw [hr a, Finset.mul_sum]
    refine S.sum_mem fun i _ => ?_
    rw [hH a i, Polynomial.aeval_eq_sum_range' (hlt a i), Finset.sum_mul]
    refine S.sum_mem fun j hj => ?_
    rw [smul_mul_assoc]
    exact S.smul_mem _ (hgen j (Finset.mem_range.mp hj) i)
  intro v hv
  have hvsum : v = ∑ a, bV.repr ⟨v, hv⟩ a • ((bV a : V) : F) := by
    have h := congrArg (fun w : V => (w : F)) (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  rw [hvsum, Finset.mul_sum]
  refine S.sum_mem fun a _ => ?_
  rw [mul_smul_comm]
  exact S.smul_mem _ (hbasis a)

end covering


end
end Dubon2026.SourceCurve.RegularProlongation
