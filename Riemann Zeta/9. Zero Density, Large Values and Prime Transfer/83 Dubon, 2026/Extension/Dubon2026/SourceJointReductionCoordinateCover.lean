import Dubon2026.SourceJointReductionPolynomialCover

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
joint chart integrality. This strengthening records that the common unit
denominator belongs to the rational coordinate field, as required by the
finite integral-coordinate argument. It reuses the already checked joint
basis and normalization proofs. The earlier audited existential remains
frozen; only its necessary coordinate-membership refinement is added.


simultaneous residue dimension. The actual joint residue span preserves
finite-space dimension when the coordinate degrees sum to the original
degree. Existing constant normalizers, adapted bases, coordinate powers
and native fraction-ring independence are reused. Finite residue coordinate
degrees are explicit upstream inputs, supplied by the actual modular fields.
Adapted from frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing

variable {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

variable (R : ∀ i, RegularProlongation A F (Fb i))
  [DecidableEq ι]
  (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  {d : ι → ℕ} (yb : ∀ i, Fin (d i) → Fb i)
  (hyb : ∀ i, LinearIndependent
    (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
    (yb i))
  (z : (Σ i, Fin (d i)) → F) (hzmem : ∀ τ l, z τ ∈ (R l).integers)
  (hzi : ∀ τ : Σ i, Fin (d i), (R τ.1).residue ⟨z τ, hzmem τ τ.1⟩ = yb τ.1 τ.2)
  (hzl : ∀ (τ : Σ i, Fin (d i)) l, l ≠ τ.1 → (R l).residue ⟨z τ, hzmem τ l⟩ = 0)
  [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
  (heq : ∑ i, d i = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include htr hyb hzi hzl heq in

theorem exists_joint_unit_mul_mem_span_in_coordinate (V : Submodule L F) [FiniteDimensional L V] :
    ∃ U : F, ∃ hU : ∀ i, U ∈ (R i).integers,
      (∀ i, (R i).residue ⟨U, hU i⟩ ≠ 0) ∧
      U ∈ IntermediateField.adjoin L ({f} : Set F) ∧
      ∃ T : Finset (ℕ × (Σ i, Fin (d i))),
        ∀ v ∈ V, U * v ∈
          Submodule.span L (Set.range fun p : T => f ^ p.1.1 * z p.1.2) := by
  classical
  let bV := Module.finBasis L V
  choose r hr using fun a => exists_repr_adjoinField_z R f hf htr yb hyb z hzmem hzi hzl heq
    ((bV a : V) : F)
  have hfrac : ∀ a τ, ∃ PQ : Polynomial L × Polynomial L, Polynomial.aeval f PQ.2 ≠ 0 ∧
      (r a τ : F) = Polynomial.aeval f PQ.1 / Polynomial.aeval f PQ.2 := by
    intro a τ
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L (r a τ : F)).mp (r a τ).2
    by_cases hQ : Polynomial.aeval f Q = 0
    · exact ⟨(0, 1), by simp, by rw [hPQ, hQ, div_zero]; simp⟩
    · exact ⟨(P, Q), hQ, hPQ⟩
  choose PQ hQne hPQ using hfrac
  set q : Polynomial L := ∏ p : Fin (Module.finrank L V) × (Σ i, Fin (d i)), (PQ p.1 p.2).2
  have haevalq : Polynomial.aeval f q =
      ∏ p : Fin (Module.finrank L V) × (Σ i, Fin (d i)), Polynomial.aeval f (PQ p.1 p.2).2 := by
    simp only [q, map_prod]
  have hqx : Polynomial.aeval f q ≠ 0 := by
    rw [haevalq]; exact Finset.prod_ne_zero_iff.mpr fun p _ => hQne p.1 p.2
  have hq0 : q ≠ 0 := fun h => hqx (h ▸ map_zero _)
  obtain ⟨U, hUmem, hUres, c, hc, hUq⟩ := exists_joint_normalize_aeval R f hf htr q hq0
  obtain ⟨H, hH⟩ : ∃ H : Fin (Module.finrank L V) → (Σ i, Fin (d i)) → Polynomial L,
      ∀ a τ, U * ((r a τ : F) * z τ) = Polynomial.aeval f (H a τ) * z τ := by
    refine ⟨fun a τ => Polynomial.C c⁻¹ *
      ((∏ p ∈ Finset.univ.erase (a, τ), (PQ p.1 p.2).2) * (PQ a τ).1), fun a τ => ?_⟩
    rw [hUq, hPQ a τ, ← mul_assoc]; congr 1
    simp only [map_mul, Polynomial.aeval_C, map_prod]
    rw [haevalq, ← Finset.mul_prod_erase Finset.univ
      (fun p => Polynomial.aeval f (PQ p.1 p.2).2) (Finset.mem_univ (a, τ))]
    have hQ := hQne a τ; field_simp
  obtain ⟨N, hlt⟩ : ∃ N, ∀ a τ, (H a τ).natDegree < N := by
    refine ⟨(Finset.univ.sup fun p : _ × _ => (H p.1 p.2).natDegree) + 1, fun a τ => ?_⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun p : _ × _ => (H p.1 p.2).natDegree)
      (Finset.mem_univ (a, τ)))
  have hUcoordinate : U ∈ IntermediateField.adjoin L ({f} : Set F) := by
    rw [hUq, Polynomial.aeval_eq_sum_range]
    refine mul_mem ((IntermediateField.adjoin L ({f} : Set F)).algebraMap_mem _)
      (sum_mem fun j _ => ?_)
    rw [Algebra.smul_def]
    exact mul_mem ((IntermediateField.adjoin L ({f} : Set F)).algebraMap_mem _)
      (pow_mem (IntermediateField.mem_adjoin_simple_self L f) _)
  refine ⟨U, hUmem, hUres, hUcoordinate, Finset.range N ×ˢ Finset.univ, ?_⟩
  let S := Submodule.span L (Set.range fun p : ↥(Finset.range N ×ˢ (Finset.univ :
    Finset (Σ i, Fin (d i)))) => f ^ p.1.1 * z p.1.2)
  have hgen : ∀ j < N, ∀ τ, f ^ j * z τ ∈ S := fun j hj τ =>
    Submodule.subset_span ⟨⟨(j, τ), Finset.mk_mem_product (Finset.mem_range.mpr hj)
      (Finset.mem_univ τ)⟩, rfl⟩
  have hbasis : ∀ a, U * ((bV a : V) : F) ∈ S := by
    intro a; rw [hr a, Finset.mul_sum]
    refine S.sum_mem fun τ _ => ?_
    rw [hH a τ, Polynomial.aeval_eq_sum_range' (hlt a τ), Finset.sum_mul]
    refine S.sum_mem fun j hj => ?_
    rw [smul_mul_assoc]
    exact S.smul_mem _ (hgen j (Finset.mem_range.mp hj) τ)
  intro v hv
  have hvsum : v = ∑ a, bV.repr ⟨v, hv⟩ a • ((bV a : V) : F) := by
    have h := congrArg (fun w : V => (w : F)) (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h; exact h.symm
  rw [hvsum, Finset.mul_sum]
  exact S.sum_mem fun a _ => by rw [mul_smul_comm]; exact S.smul_mem _ (hbasis a)


end
end Dubon2026.SourceCurve.RegularProlongation.Joint
