import Dubon2026.SourceCurveFiniteCoordinateGlobalResidues
import Dubon2026.SourceCurveFiniteCoordinateGenusMaximum
import Dubon2026.SourceCurveResidueProbe

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer-cover genus ->
canonical degree. The actual finite residue sum gives the canonical
complement formula for the adelic index. Existing residue probes and
Weil rank one prove injectivity and surjectivity; global vanishing is
the preceding trace-transfer theorem, not an added hypothesis. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential
variable {K F : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]

theorem finite_coordinate_index_eq_canonical_complement
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) :
    letI := hasCanonicalDivisor_finite_coordinate t ht hDt
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      indexOfSpecialty D = ell (canonicalDivisorOf hω - D) := by
  letI := hasCanonicalDivisor_finite_coordinate t ht hDt
  letI := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  letI : ∀ v : Place K F, v.DCoordGenerates := finite_coordinate_place_dCoordGenerates t
  letI := nonempty_place_of_separating_coordinate t ht
  intro ω hω D
  let Rfam := fun v : Place K F =>
    v.canonicalLocalResidueData (place_residue_bijective_of_finite_coordinate t v).2
  let φ := weilOfKaehlerK Rfam hω
  have hmem : φ ∈ omegaSpace (canonicalDivisorOf hω) := by
    rw [omegaSpace, Submodule.mem_dualAnnihilator]
    intro α hα
    obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
    change weilOfKaehlerK Rfam hω (β + γ) = 0
    rw [map_add, weilOfKaehlerK_vanish_adeleBdd_canonical Rfam hω
      (Submodule.mem_comap.mp hβ), zero_add]
    obtain ⟨f, hf⟩ := Submodule.mem_comap.mp hγ
    change diagonalHom K F f = (γ : Place K F → F) at hf
    rw [weilOfKaehlerK_apply, ← hf]
    exact finite_coordinate_global_residue_sum_zero t ht hDt Rfam ω f
  have hne : φ ≠ 0 := weilOfKaehlerK_ne_zero_of_rational_residues Rfam
    (place_residue_bijective_of_finite_coordinate t) hω
  have hmax : ∀ D' : Divisor K F, φ ∈ omegaSpace D' → D' ≤ canonicalDivisorOf hω := by
    intro D' hD'
    exact weilOfKaehlerK_adeleBound_le_canonical Rfam
      (place_residue_bijective_of_finite_coordinate t) hω
      (fun _ hα => omegaSpace_vanishBdd hD' hα)
  have hbij : Function.Bijective (residuePairing K F (canonicalDivisorOf hω) D hmem) :=
    ⟨residuePairing_injective _ D hmem hne,
      residuePairing_surjective_of_rankOne_max
        (finite_coordinate_weil_differentials_rank_one t ht) hmem hne hmax D⟩
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact (LinearEquiv.ofBijective _ hbij).finrank_eq.symm

end
end Dubon2026.SourceCurve
