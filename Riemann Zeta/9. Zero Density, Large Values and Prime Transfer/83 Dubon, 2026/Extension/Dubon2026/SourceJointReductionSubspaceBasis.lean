import Dubon2026.SourceJointReductionIndependent
import Dubon2026.SourceReductionAdaptedBasis

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
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
  {J : Type*} [Fintype J] (E : J → F) (hEmem : ∀ j i, E j ∈ (R i).integers)
  (hE : LinearIndependent (ResidueField A) (jointRes R E hEmem))

include hE in

omit [Fintype ι] in
theorem exists_jointResidue_linearIndependent (W : Submodule L F)
    (hW : W ≤ Submodule.span L (Set.range E)) {m : ℕ} (hm : Module.finrank L W = m) :
    ∃ w : Fin m → F, ∃ hwmem : ∀ a i, w a ∈ (R i).integers,
      (∀ a, w a ∈ W) ∧
      LinearIndependent (ResidueField A) (fun a => jointRes R w hwmem a) := by
  classical
  have hli := linearIndependent_coe_joint R E hEmem hE
  let ℓ : J → Submodule.span L (Set.range E) →ₗ[L] L :=
    fun j => (Finsupp.lapply j).comp hli.repr
  have hexp : ∀ s : Submodule.span L (Set.range E), (s : F) = ∑ j, ℓ j s • E j := by
    intro s
    have h := hli.linearCombination_repr s
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun j => zero_smul L (E j))] at h
    exact h.symm
  let W₀ : Submodule L (Submodule.span L (Set.range E)) :=
    W.comap (Submodule.span L (Set.range E)).subtype
  have hW₀ : Module.finrank L W₀ = m := by
    rw [← hm]; exact (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hinj : ∀ v ∈ W₀, (∀ j, ℓ j v = 0) → v = 0 := by
    intro v _ hv; apply Subtype.ext
    rw [hexp v]; exact Finset.sum_eq_zero fun j _ => by rw [hv j, zero_smul]
  obtain ⟨b, c, hcinj, hbW, hbA, hδ⟩ := exists_adapted A ℓ m W₀ hinj hW₀

  let aA : Fin m → J → A := fun a j => ⟨ℓ j (b a), hbA a j⟩
  have haA : ∀ a j, ((aA a j : A) : L) = ℓ j (b a) := fun a j => rfl
  have hwexp : ∀ a, ((b a : Submodule.span L (Set.range E)) : F) =
      ∑ j, ((aA a j : A) : L) • E j := fun a => by
    exact hexp (b a)
  refine ⟨fun a => (b a : F), fun a i => ?_, fun a => (hbW a), ?_⟩
  · show ((b a : Submodule.span L (Set.range E)) : F) ∈ (R i).integers
    rw [hwexp a]; exact sum_smul_mem R E hEmem Finset.univ (aA a) i
  ·
    rw [Fintype.linearIndependent_iff]
    intro κ hκ a'

    have hκ' : ∀ i, ∑ a, κ a • (R i).residue ⟨(b a : F), by
        rw [hwexp a]; exact sum_smul_mem R E hEmem Finset.univ (aA a) i⟩ = 0 := by
      intro i; have := congrFun hκ i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, jointRes] at this; exact this
    have hswap : ∀ j, ∑ a, κ a • IsLocalRing.residue A (aA a j) = 0 := by
      intro j
      have hsum2 : ∑ j', (∑ a, κ a • IsLocalRing.residue A (aA a j')) • jointRes R E hEmem j' = 0 := by
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
        rw [← hκ' i]
        simp_rw [Finset.sum_smul, smul_eq_mul, mul_smul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        have hres := residue_sum_smul R E hEmem Finset.univ (aA a) i
        have heq : (⟨(b a : F), by rw [hwexp a]; exact sum_smul_mem R E hEmem Finset.univ (aA a) i⟩ :
            (R i).integers) =
            ⟨∑ j, ((aA a j : A) : L) • E j, sum_smul_mem R E hEmem Finset.univ (aA a) i⟩ :=
          Subtype.ext (hwexp a)
        simp only [jointRes] at hres
        rw [heq, hres]
        simp only [jointRes]
      exact linearIndependent_iff'.mp hE Finset.univ
        (fun j' => ∑ a, κ a • IsLocalRing.residue A (aA a j')) hsum2 j (Finset.mem_univ j)

    have heval := hswap (c a')
    have haδ : ∀ a, (aA a (c a') : L) = if a' = a then 1 else 0 := fun a => by
      rw [haA]; exact hδ a' a
    simp_rw [show ∀ a, IsLocalRing.residue A (aA a (c a')) =
        if a' = a then 1 else 0 from fun a => by
      have := haδ a
      by_cases h : a' = a
      · rw [if_pos h] at this ⊢
        have : aA a (c a') = 1 := Subtype.ext this
        rw [this, map_one]
      · rw [if_neg h] at this ⊢
        have : aA a (c a') = 0 := Subtype.ext this
        rw [this, map_zero]] at heval
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at heval
    simpa [smul_eq_mul, mul_one] using heval


end
end Dubon2026.SourceCurve.RegularProlongation.Joint
