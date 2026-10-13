import Dubon2026.SUnitFullLogEquivariance

/-! # The actual S-unit logarithmic sequence

The original full logarithm surjects onto its actual complete lattice.
Its kernel is finite and equals the actual S-unit torsion subgroup.
The map and lattice retain the original Galois action. This discharges
the finite-kernel equivariant-sequence input for DUB-17's comparison
of the S-unit and logarithmic-lattice Herbrand quotients.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))

/-- The kernel of the actual full original logarithm is finite. -/
theorem sUnitFullLog_finite_kernel : Finite (sUnitFullLog L S).ker := by
  letI := sUnitReducedLog_finite_kernel L S
  let f : (sUnitFullLog L S).ker → (sUnitReducedLog L S).ker := fun x =>
    ⟨x.val, by
      change sUnitReducedLog L S x.val = 0
      rw [← sUnitLogHyperplaneEquiv_fullLog, x.property, map_zero]⟩
  exact Finite.of_injective f (fun _ _ h =>
    Subtype.ext (congrArg (fun y : (sUnitReducedLog L S).ker => y.val) h))

/-- The original full logarithmic kernel is exactly the actual S-unit torsion subgroup. -/
theorem sUnitFullLog_ker_eq_torsion :
    (sUnitFullLog L S).ker =
      AddCommGroup.torsion (Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) := by
  letI := sUnitFullLog_finite_kernel L S
  ext x
  constructor
  · intro hx
    exact ((sUnitFullLog L S).ker.subtype.isOfFinAddOrder
      (isOfFinAddOrder_of_finite (⟨x, hx⟩ : (sUnitFullLog L S).ker)))
  · intro hx
    obtain ⟨n, hn, he⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
    have hf := congrArg (sUnitFullLog L S) he
    rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul ℝ] at hf
    exact (smul_eq_zero.mp hf).resolve_left (by exact_mod_cast hn.ne')

/-- The original full logarithm with codomain equal to its actual complete lattice. -/
def sUnitLogToLattice : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L) →+
    sUnitFullLogLattice L S :=
  (sUnitFullLog L S).codRestrict _ (fun x => by
    rw [sUnitFullLogLattice_eq_range]
    exact LinearMap.mem_range_self _ x)

/-- Every element of the actual original logarithmic lattice comes from an original S-unit. -/
theorem sUnitLogToLattice_surjective : Function.Surjective (sUnitLogToLattice L S) := by
  intro z
  have hz : z.val ∈ (sUnitFullLog L S).toIntLinearMap.range := by
    simpa only [sUnitFullLogLattice_eq_range] using z.property
  obtain ⟨x, hx⟩ := hz
  exact ⟨x, Subtype.ext hx⟩

/-- Restricting the codomain to the actual lattice retains precisely the actual torsion kernel. -/
theorem sUnitLogToLattice_ker :
    (sUnitLogToLattice L S).ker =
      AddCommGroup.torsion (Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) := by
  rw [← sUnitFullLog_ker_eq_torsion L S]
  ext x
  exact Subtype.ext_iff

variable (K : Type) [Field K] [Algebra K L]
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual Galois action on the complete original logarithmic lattice. -/
@[reducible]
def sUnitFullLogLatticeAction : DistribMulAction Gal(L/K) (sUnitFullLogLattice L S) := by
  letI := sUnitLogHyperplaneAction K L S hS
  exact {
    smul := fun σ z => ⟨σ • z.val, sUnitFullLogLattice_galois_mem K L S hS σ z.val z.property⟩
    one_smul := fun z => Subtype.ext (one_smul Gal(L/K) z.val)
    mul_smul := fun σ τ z => Subtype.ext (mul_smul σ τ z.val)
    smul_zero := fun σ => Subtype.ext (smul_zero σ)
    smul_add := fun σ z z' => Subtype.ext (smul_add σ z.val z'.val) }

/-- The actual surjective torsion-kernel logarithmic map is Galois-equivariant. -/
theorem sUnitLogToLattice_galois (σ : Gal(L/K))
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    letI := sUnitAdditiveGaloisAction K L S hS
    letI := sUnitFullLogLatticeAction L S K hS
    sUnitLogToLattice L S (σ • x) = σ • sUnitLogToLattice L S x := by
  apply Subtype.ext
  exact sUnitFullLog_galois K L S hS σ x

end
end Dubon2026
