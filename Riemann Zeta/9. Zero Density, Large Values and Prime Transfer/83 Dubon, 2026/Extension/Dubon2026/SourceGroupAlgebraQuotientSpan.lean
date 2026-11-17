import Dubon2026.SourceActualTraceAlgebra

/-! DUB-17/18 -> actual rank-two realization -> matrix continuity.
The actual group-algebra quotient is spanned by its original group image.
This necessary bridge will express each fixed matrix coordinate as a
finite linear combination of translates of the original continuous trace.
It is proved for the constructed quotient, not assumed for an ambient algebra. -/
namespace Dubon2026
noncomputable section

/-- The actual quotient of the original group algebra is spanned by its
original group image, with no finite-dimensionality assumption. -/
theorem sourceGroupAlgebraQuotient_span
    {G R : Type} [Group G] [CommRing R]
    (I : Ideal (MonoidAlgebra R G)) [I.IsTwoSided] :
    Submodule.span R (Set.range (fun g : G =>
      Ideal.Quotient.mk I (MonoidAlgebra.of R G g))) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction x using MonoidAlgebra.induction_on with
  | hM g => exact Submodule.subset_span ⟨g, rfl⟩
  | hadd x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | hsmul r x hx =>
    change r • Ideal.Quotient.mk I x ∈ _
    exact Submodule.smul_mem _ r hx

end
end Dubon2026
