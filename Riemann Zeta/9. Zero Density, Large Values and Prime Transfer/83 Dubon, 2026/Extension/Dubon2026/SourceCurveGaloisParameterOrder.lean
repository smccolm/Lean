import Dubon2026.SourceCurveDecompositionOrderGap

/-! An order-one base parameter has upper order equal to the actual
decomposition group cardinality. This is the other geometric input to
the DUB-17/18 wild different estimate, derived from the existing place
cardinality and normalized restriction-order theorems. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F M : Type*} [Field K] [IsAlgClosed K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
variable [FiniteDimensional F M] [IsGalois F M] (v : Place K M)

theorem galois_parameter_order_eq_decomposition_card
    (htop : Function.Bijective (algebraMap K v.ResidueField))
    {x : F} (hx : (v.restrict F).ord x = 1) :
    v.ord (algebraMap F M x) =
      (Nat.card (v.toValuationSubring.decompositionSubgroup F) : ℤ) := by
  have hbase : Function.Bijective (algebraMap K (v.restrict F).ResidueField) :=
    ⟨(algebraMap K (v.restrict F).ResidueField).injective,
      v.residue_algebraMap_surjective_restrict htop.surjective⟩
  have hc := decomposition_card_eq_uniformizer_order v hbase htop
  have he := congrArg (fun n : ℕ => (n : ℤ)) hc
  dsimp only at he
  rw [Int.toNat_of_nonneg (v.ord_restricted_uniformizer_pos (F := F)).le] at he
  rw [v.ord_algebraMap_restrict x, hx, one_mul]
  exact he.symm

end
end Dubon2026.SourceCurve.Place
