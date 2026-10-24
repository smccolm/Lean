import Dubon2026.SourceJointChartWindowGeneration
import Dubon2026.SourceJointChartOrderInclusion
import Dubon2026.SourceJointChartDimensionInequality
import Dubon2026.SourceCurveTranscendentalDegree

/-! DUB-17/18 -> Picard torsion injectivity -> original-field Kummer
power lifting -> genus inequality -> eventual joint chart dimension bound.
The proved monic multiples and residue integrality supply the chart quotient
inputs. Finite pole spaces and separating-coordinate generation are explicit
upstream inputs here, discharged for the actual modular fields by the consumer.
Adapted from Apache-2.0 FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
using native/local finite integral-closure generation instead of the general
external Riemann--Roch generation theorem. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open Polynomial

section Assembly

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F]
  [Algebra L F] {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]

local notation "𝕜" => IsLocalRing.ResidueField A

theorem eventual_residue_chart_dimension (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental 𝕜 ((R i).residue ⟨f, hf i⟩))
    [∀ i, FiniteDimensional (IntermediateField.adjoin 𝕜
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
    [∀ i (D : Divisor 𝕜 (Fb i)), FiniteDimensional 𝕜 ↥(LSpace D)]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin 𝕜
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (Db : ∀ i, Divisor 𝕜 (Fb i))
    (hDb : ∀ i, ∀ w : Place 𝕜 (Fb i), Db i w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩)))
    (Db' : ∀ i, Divisor 𝕜 (Fb i))
    (hDb' : ∀ i (w : Place 𝕜 (Fb i)), Db' i w =
      max 0 (-w.ord (((R i).residue ⟨f, hf i⟩)⁻¹)))
    (hgeni : ∀ i, ∃ Mi : ℕ, ∀ h : Fb i,
      (∀ w : Place 𝕜 (Fb i), 0 ≤ w.ord ((R i).residue ⟨f, hf i⟩) → 0 ≤ w.ord h) →
        h ∈ Submodule.span 𝕜 {g : Fb i | ∃ j : ℕ,
          ∃ y ∈ LSpace (Mi • Db i), g = ((R i).residue ⟨f, hf i⟩) ^ j * y})
    (hgeni' : ∀ i, ∃ Mi : ℕ, ∀ h : Fb i,
      (∀ w : Place 𝕜 (Fb i), 0 ≤ w.ord (((R i).residue ⟨f, hf i⟩)⁻¹) → 0 ≤ w.ord h) →
        h ∈ Submodule.span 𝕜 {g : Fb i | ∃ j : ℕ,
          ∃ y ∈ LSpace (Mi • Db' i), g = (((R i).residue ⟨f, hf i⟩)⁻¹) ^ j * y})
    (u : ∀ i, Fb i) (hu_def : ∀ i, (R i).residue ⟨f, hf i⟩ = u i) (hu : ∀ i, u i ≠ 0) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      FiniteDimensional 𝕜 ↥(ST R f ⊓ (ST R f⁻¹).map
        ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M)) ∧
      Module.finrank 𝕜 ↥(ST R f ⊓ (ST R f⁻¹).map
        ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M)) + Fintype.card ι ≤
        (∑ i, Module.finrank 𝕜 ↥(LSpace (M • Db i))) + Module.finrank 𝕜 ↥(ST R f ⊓ ST R f⁻¹) := by
  classical
  haveI := hfd
  have htru : ∀ i, Transcendental 𝕜 (u i) := fun i => hu_def i ▸ htr i
  have hDb_u : ∀ i (w : Place 𝕜 (Fb i)), Db i w = max 0 (-w.ord (u i)) := fun i w => by
    rw [← hu_def i]; exact hDb i w

  have hwin : ∀ M : ℕ, Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M) =
      Submodule.pi Set.univ fun i => LSpace (M • Db i) := window_eq u hu Db hDb_u
  have hfin : ∀ M : ℕ, FiniteDimensional 𝕜 ↥(Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M)) := fun M => by
    rw [hwin M]; exact finite_pi _
  have hrank : ∀ M : ℕ, Module.finrank 𝕜 ↥(Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M)) =
      ∑ i, Module.finrank 𝕜 ↥(LSpace (M • Db i)) :=
    fun M => by rw [hwin M, finrank_pi]

  have hPa := residue_chart_le_order_chart A Fb R hR f hf htr heq
  have hPB : ST R f ≤ Bsub (k := 𝕜) u := fun h hh i w hw =>
    hPa hh i w (by change 0 ≤ w.ord ((R i).residue ⟨f, hf i⟩); rw [hu_def i]; exact hw)
  have hPb := Joint.exists_monic_residue_chart_multiple A Fb R hR f hf
    (Module.finrank_pos (R := IntermediateField.adjoin L ({f} : Set F)) (M := F))
  have htor : ∀ y ∈ Bsub (k := 𝕜) u, ∃ c : 𝕜[X], c.Monic ∧
      aeval (mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) c y ∈ ST R f := by
    refine tor_of_pointwise u hu (ST R f) (Bsub u) fun y => ?_
    obtain ⟨c, hc, hy⟩ := hPb y
    refine ⟨c, hc, ?_⟩
    have : (fun i => aeval (u i) c * y i) = fun i => aeval ((R i).residue ⟨f, hf i⟩) c * y i :=
      funext fun i => by rw [hu_def i]
    rw [this]; exact hy

  have hu0 : ∀ i, (R i).residue ⟨f, hf i⟩ ≠ 0 := fun i => by rw [hu_def i]; exact hu i
  have hf' : ∀ i, f⁻¹ ∈ (R i).integers := inv_mem_integers hu0
  have hres_inv : ∀ i, (R i).residue ⟨f⁻¹, hf' i⟩ = u⁻¹ i := fun i => by
    rw [Pi.inv_apply, ← hu_def i]; exact residue_inv hu0 i
  have htr' : ∀ i, Transcendental 𝕜 ((R i).residue ⟨f⁻¹, hf' i⟩) := fun i => by
    rw [hres_inv i]; exact transcendental_inv (htru i)
  have hfd' : FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [adjoin_singleton_inv_eq]; exact hfd
  have heq' : ∑ i, Module.finrank (IntermediateField.adjoin 𝕜
      ({(R i).residue ⟨f⁻¹, hf' i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [adjoin_singleton_inv_eq, ← heq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hres_inv i, Pi.inv_apply, adjoin_singleton_inv_eq, ← hu_def i]
  letI : FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := hfd'
  letI (i : ι) : FiniteDimensional (IntermediateField.adjoin 𝕜
      ({(R i).residue ⟨f⁻¹, hf' i⟩} : Set (Fb i))) (Fb i) := by
    rw [hres_inv i, Pi.inv_apply, adjoin_singleton_inv_eq, ← hu_def i]
    infer_instance
  have hPa' := residue_chart_le_order_chart A Fb R hR f⁻¹ hf' htr' heq'
  have hPb' := Joint.exists_monic_residue_chart_multiple A Fb R hR f⁻¹ hf'
    (Module.finrank_pos (R := IntermediateField.adjoin L ({f⁻¹} : Set F)) (M := F))
  have hP'B' : ST R f⁻¹ ≤ Bsub' (k := 𝕜) u := fun h hh i w hw => by
    have := hPa' hh i w
    change 0 ≤ w.ord ((R i).residue ⟨f⁻¹, hf' i⟩) → 0 ≤ w.ord (h i) at this
    rw [hres_inv i, Pi.inv_apply, Place.ord_inv, neg_nonneg] at this
    exact this hw
  have htor' : ∀ y ∈ Bsub' (k := 𝕜) u, ∃ c : 𝕜[X], c.Monic ∧
      aeval ((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) c y ∈ ST R f⁻¹ := by
    rw [mulEquiv_symm_eq]
    refine tor_of_pointwise u⁻¹ (inv_ne_zero_pi hu) (ST R f⁻¹) (Bsub' u) fun y => ?_
    obtain ⟨c, hc, hy⟩ := hPb' y
    refine ⟨c, hc, ?_⟩
    have : (fun i => aeval (u⁻¹ i) c * y i) =
        fun i => aeval ((R i).residue ⟨f⁻¹, hf' i⟩) c * y i :=
      funext fun i => by rw [hres_inv i]
    rw [this]; exact hy

  have hP : (ST R f).map (mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ≤ ST R f :=
    ST_map_le f hf u hu hu_def
  have hB := Bsub_map_le (k := 𝕜) u hu
  have hP' : (ST R f⁻¹).map ((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ≤
      ST R f⁻¹ := by
    rw [mulEquiv_symm_eq]; exact ST_map_le f⁻¹ hf' u⁻¹ (inv_ne_zero_pi hu) hres_inv
  have hB' : (Bsub' (k := 𝕜) u).map
      ((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ≤ Bsub' u := by
    rw [mulEquiv_symm_eq, ← Bsub_inv]; exact Bsub_map_le u⁻¹ _

  have hgen : ∃ M₁ : ℕ, Bsub (k := 𝕜) u ≤ ⨆ j : ℕ, (Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M₁)).map
        ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ j) := by
    have hn : ∀ i, ∃ Mi : ℕ, ∀ h : Fb i, (∀ w : Place 𝕜 (Fb i), 0 ≤ w.ord (u i) → 0 ≤ w.ord h) →
        h ∈ Submodule.span 𝕜
          {g : Fb i | ∃ j : ℕ, ∃ y ∈ LSpace (Mi • Db i), g = u i ^ j * y} :=
      fun i => by simpa only [hu_def i] using hgeni i
    choose Mi hMi using hn
    exact ⟨Finset.univ.sup Mi, Bsub_le_iSup u hu Db hDb_u _ fun i =>
      ⟨Mi i, Finset.le_sup (Finset.mem_univ i), hMi i⟩⟩
  have hgen' : ∃ M₁ : ℕ, Bsub' (k := 𝕜) u ≤ ⨆ j : ℕ, (Bsub' u ⊓ (Bsub u).map
      (((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ M₁)).map
        (((mulEquiv (k := 𝕜) u hu).symm : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ j) := by
    have hD' : ∀ i (w : Place 𝕜 (Fb i)), Db' i w = max 0 (-w.ord (u⁻¹ i)) := by
      intro i w
      rw [Pi.inv_apply, ← hu_def i]
      exact hDb' i w
    have hn : ∀ i, ∃ Mi : ℕ, ∀ h : Fb i,
        (∀ w : Place 𝕜 (Fb i), 0 ≤ w.ord (u⁻¹ i) → 0 ≤ w.ord h) →
        h ∈ Submodule.span 𝕜
          {g : Fb i | ∃ j : ℕ, ∃ y ∈ LSpace (Mi • Db' i), g = u⁻¹ i ^ j * y} :=
      fun i => by simpa only [hu_def i, Pi.inv_apply] using hgeni' i
    choose Mi hMi using hn
    rw [mulEquiv_symm_eq, ← Bsub_inv u, ← Bsub'_inv u]
    exact ⟨Finset.univ.sup Mi, Bsub_le_iSup u⁻¹ (inv_ne_zero_pi hu) Db' hD' _ fun i =>
      ⟨Mi i, Finset.le_sup (Finset.mem_univ i), hMi i⟩⟩

  obtain ⟨M₀, hM₀⟩ := JointChartLinearAlgebra.eventual_chart_intersection_dimension
    (mulEquiv (k := 𝕜) u hu) (ST R f) (Bsub u) (ST R f⁻¹) (Bsub' u) hPB hP'B' hP hB hP' hB'
    hfin hgen hgen' htor htor'
  haveI : FiniteDimensional 𝕜 ↥(Bsub (k := 𝕜) u ⊓ Bsub' u) := by
    haveI := hfin 0
    refine Submodule.finiteDimensional_of_le (S₂ := Bsub (k := 𝕜) u ⊓ (Bsub' u).map
      ((mulEquiv (k := 𝕜) u hu : (∀ i, Fb i) →ₗ[𝕜] (∀ i, Fb i)) ^ 0)) fun x hx =>
      Submodule.mem_inf.mpr ⟨hx.1, Submodule.mem_map.mpr ⟨x, hx.2, ?_⟩⟩
    rw [pow_zero, Module.End.one_apply]
  have hcard := card_le_finrank_inf (k := 𝕜) u
  refine ⟨M₀, fun M hM => ⟨?_, ?_⟩⟩
  · haveI := hfin M
    exact Submodule.finiteDimensional_of_le (inf_le_inf hPB (Submodule.map_mono hP'B'))
  · have h1 := hM₀ M hM
    rw [hrank M] at h1
    omega

end Assembly

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
