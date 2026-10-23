import Dubon2026.SourceReductionAdaptedBasis
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

section core

variable (R : RegularProlongation A F Fbar) {ι : Type*} [Fintype ι] (E : ι → R.integers)
  (hE : LinearIndependent (ResidueField A) (fun i => R.residue (E i)))

include hE in

theorem exists_residue_linearIndependent (W : Submodule L F)
    (hW : W ≤ Submodule.span L (Set.range fun i => (E i : F))) {d : ℕ}
    (hd : Module.finrank L W = d) :
    ∃ f : Fin d → R.integers, (∀ a, (f a : F) ∈ W) ∧
      LinearIndependent (ResidueField A) (fun a => R.residue (f a)) := by
  classical
  have hli := linearIndependent_coe R E hE

  let ℓ : ι → Submodule.span L (Set.range fun i => (E i : F)) →ₗ[L] L :=
    fun i => (Finsupp.lapply i).comp hli.repr
  have hexp : ∀ s : Submodule.span L (Set.range fun i => (E i : F)),
      (s : F) = ∑ i, ℓ i s • (E i : F) := by
    intro s
    have h := hli.linearCombination_repr s
    rw [Finsupp.linearCombination_apply] at h
    rw [Finsupp.sum_fintype _ _ (fun i => zero_smul L (E i : F))] at h
    exact h.symm

  let W₀ : Submodule L (Submodule.span L (Set.range fun i => (E i : F))) :=
    W.comap (Submodule.span L (Set.range fun i => (E i : F))).subtype
  have hW₀ : Module.finrank L W₀ = d := by
    rw [← hd]
    exact (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hinj : ∀ v ∈ W₀, (∀ i, ℓ i v = 0) → v = 0 := by
    intro v _ hv
    apply Subtype.ext
    rw [hexp v]
    simp [hv]
  obtain ⟨b, c, hcinj, hbW, hbA, hδ⟩ := exists_adapted A ℓ d W₀ hinj hW₀

  have hcoe : ∀ a, ((b a : _) : F) =
      ((∑ i, constHom R ⟨ℓ i (b a), hbA a i⟩ * E i : R.integers) : F) := by
    intro a
    rw [coe_sum_constHom_mul, hexp (b a)]
  have hbO : ∀ a, ((b a : _) : F) ∈ R.integers := fun a => by
    rw [hcoe a]
    exact Subtype.mem _
  refine ⟨fun a => ⟨(b a : F), hbO a⟩, fun a => hbW a, ?_⟩

  rw [Fintype.linearIndependent_iff]
  intro κ hκ a₀
  have hsurjres : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective
  choose α hα using fun a => hsurjres (κ a)
  let sβ : Submodule.span L (Set.range fun i => (E i : F)) := ∑ a, (α a : L) • b a
  have hGeq : ∑ i, ℓ i sβ • (E i : F) =
      ((∑ a, constHom R (α a) * ⟨(b a : F), hbO a⟩ : R.integers) : F) := by
    rw [← hexp sβ, coe_sum_constHom_mul]
    simp [sβ]
  have hGmem : ∑ i, ℓ i sβ • (E i : F) ∈ R.integers := by
    rw [hGeq]
    exact Subtype.mem _
  have hG0 : R.residue ⟨_, hGmem⟩ = 0 := by
    have : (⟨_, hGmem⟩ : R.integers) = ∑ a, constHom R (α a) * ⟨(b a : F), hbO a⟩ :=
      Subtype.ext (hGeq)
    rw [this, residue_sum_constHom_mul]
    simp_rw [hα]
    exact hκ
  have hlt := valuation_lt_one_of_sum_smul_mem R E hE Finset.univ (fun i => ℓ i sβ) hGmem hG0
    (c a₀) (Finset.mem_univ _)
  have hcoord : ℓ (c a₀) sβ = α a₀ := by
    simp only [sβ, map_sum, map_smul, smul_eq_mul, hδ, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ a₀, if_pos (Finset.mem_univ a₀)]
  simp only [hcoord] at hlt
  rw [← hα a₀]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr
    ((ValuationSubring.valuation_lt_one_iff A _).mpr hlt)

end core

section assembly

variable (R : RegularProlongation A F Fbar)

theorem card_le_finrank (V : Submodule L F) [FiniteDimensional L V] {ι : Type*} [Fintype ι]
    (f : ι → R.integers) (hfV : ∀ i, (f i : F) ∈ V)
    (hind : LinearIndependent (ResidueField A) (fun i => R.residue (f i))) :
    Fintype.card ι ≤ Module.finrank L V := by
  have hli := linearIndependent_coe R f hind
  have hli' : LinearIndependent L (fun i => (⟨(f i : F), hfV i⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hli
  exact hli'.fintype_card_le_finrank

theorem mem_of_mem_span (V : Submodule L F) {h : Fbar}
    (hh : h ∈ Submodule.span (ResidueField A)
      {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) :
    ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h := by
  induction hh using Submodule.span_induction with
  | mem h hh => exact hh
  | zero => exact ⟨0, by simp, map_zero _⟩
  | add h₁ h₂ _ _ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁, rfl⟩ := ih₁
    obtain ⟨f₂, hf₂, rfl⟩ := ih₂
    exact ⟨f₁ + f₂, by simpa using V.add_mem hf₁ hf₂, map_add _ _ _⟩
  | smul κ h _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    obtain ⟨α, hα⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal A) κ
    refine ⟨constHom R α * f, ?_, ?_⟩
    · have : ((constHom R α * f : R.integers) : F) = (α : L) • (f : F) := by
        simp [Algebra.smul_def]
      rw [this]
      exact V.smul_mem _ hf
    · rw [map_mul, residue_constHom, ← hα, Algebra.smul_def]
      rfl


end assembly

end
end Dubon2026.SourceCurve.RegularProlongation
