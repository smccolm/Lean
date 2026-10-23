import Dubon2026.SourceResidueAllLevelDegree
import Dubon2026.SourceResidueConjugateEmbedding
import Dubon2026.SourceResidueEmbeddedConjugate

/-! DUB-17/18 -> actual modular good reduction -> reverse genus inequality
-> cusp count. The proved all-level generation and expanded minimal
polynomial give actual coefficient-linear Laurent embeddings for every
primitive triangular conjugate. Their restricted valuations will produce
the cusp places; no generation or polynomial-root premise is supplied. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
open scoped IntermediateField

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- Every actual primitive conjugate gives a coefficient-linear modular field embedding. -/
theorem coeff_slot_embedding (hNK : (N : K) ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    ∃ ι : modularFunctionFieldCoeff N K →ₐ[K] LaurentSeries K,
      ι (jCoeff N K) = TS K N 1 ∧
        ι ⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩ = slotValue ζ s.1 s.2 := by
  have hr : (residueExpandedJMinpoly K N N).eval (slotValue ζ s.1 s.2) = 0 := by
    have h := residue_expanded_minpoly_slot_root_of_identity 1 N ζ
      (residueExpandedJMinpoly_eq_slotProduct N hNK ζ hζ) s hs
    simpa only [one_mul, qExpand_one_apply] using h
  obtain ⟨σ, hj, hjN, hbase⟩ := residue_full_embedding_of_expanded_minpoly_root N N
    (residue_full_generation_and_degree N hNK).1 _ hr
  let ι : modularFunctionFieldCoeff N K →ₐ[K] LaurentSeries K :=
    { toRingHom := σ
      commutes' := fun c => by
        have hc := hbase (algebraMap K K⟮jqModC K⟯ c)
          ((modularFunctionFieldCoeff N K).algebraMap_mem c)
        apply hc.trans
        change qExpand K N (algebraMap K (LaurentSeries K) c) = _
        rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, qExpand_single, mul_zero] }
  exact ⟨ι, hj, hjN⟩

end Dubon2026.SourceFunctionField
