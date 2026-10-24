import Dubon2026.SourceJointChartPolynomialRank

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap -> chart
basis rank. The existing monic-multiple theorem places a full residue
coordinate-field basis in the chart without losing polynomial independence.
Degree equality therefore forces the lifted polynomial basis to have the
full original coordinate-field rank. No valuation-extension classification
or second Gauss-basis theorem is needed. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

variable {L F : Type*} [Field L] (A : ValuationSubring L) [Field F] [Algebra L F]
  {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
  (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
  (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
  [∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
    ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
  (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
    Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include hR htr heq in
theorem coordinate_finrank_le_chart_rank {n : ℕ}
    (hcard : ∀ (d' : ℕ) (zb' : Fin d' → ∀ i, Fb i), (∀ τ, zb' τ ∈ ST R f) →
      (∀ q q' : Fin d' → (ResidueField A)[X],
        ∑ τ, aeval (rv R f hf) (q τ) * zb' τ =
          ∑ τ, aeval (rv R f hf) (q' τ) * zb' τ → q = q') → d' ≤ n) :
    Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F ≤ n := by
  classical
  let d : ι → ℕ := fun i => Module.finrank (IntermediateField.adjoin (ResidueField A)
    ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
  let b : ∀ i, Fin (d i) → Fb i := fun i => Module.finBasis _ (Fb i)
  have hb : ∀ i, LinearIndependent (IntermediateField.adjoin (ResidueField A)
      ({rv R f hf i} : Set (Fb i))) (b i) := by
    intro i
    change LinearIndependent (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (b i)
    exact (Module.finBasis _ (Fb i)).linearIndependent
  let J := Σ i, Fin (d i)
  choose c hc hcmem using fun τ : J =>
    Joint.exists_monic_residue_chart_multiple A Fb R hR f hf
      (Module.finrank_pos) (Pi.single τ.1 (b τ.1 τ.2))
  let g : J → ∀ i, Fb i := fun τ =>
    aeval (rv R f hf) (c τ) * Pi.single τ.1 (b τ.1 τ.2)
  have hg : ∀ τ, g τ ∈ ST R f := fun τ => by
    simpa only [g, aeval_pi_apply] using hcmem τ
  have huniq := polynomial_unique_single_multiples Fb (rv R f hf) htr d b hb c
    (fun τ => (hc τ).ne_zero)
  let e := (Fintype.equivFin J).symm
  have hsum : ∀ q : Fin (Fintype.card J) → (ResidueField A)[X],
      ∑ j, aeval (rv R f hf) (q j) * g (e j) =
        ∑ τ, aeval (rv R f hf) (q (e.symm τ)) * g τ := by
    intro q
    simpa only [Equiv.symm_apply_apply] using
      e.sum_comp (fun τ => aeval (rv R f hf) (q (e.symm τ)) * g τ)
  have hn := hcard (Fintype.card J) (fun j => g (e j)) (fun j => hg (e j)) (by
    intro q q' he
    rw [hsum, hsum] at he
    have he' := huniq (fun τ => q (e.symm τ)) (fun τ => q' (e.symm τ)) he
    funext j
    simpa only [Equiv.symm_apply_apply] using congrFun he' (e j))
  have hdim : Fintype.card J = Module.finrank
      (IntermediateField.adjoin L ({f} : Set F)) F := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using heq
  rwa [hdim] at hn

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
