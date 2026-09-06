import GafniTao.ZeroEnergy

/-!
# Literal replicated form of the four-zero energy

The source treats zeros with analytic multiplicity. `ZeroEnergy` already
constructs the canonical sigma type whose fiber above a resonant distinct
quadruple has the product analytic multiplicity. Here we expose that finite
type and its four coordinate maps for the forthcoming energy-preserving
detector and coloring argument.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The tolerance-one count on the canonical product-multiplicity
replication type. -/
def zeroOccurrenceAdditiveEnergyCount (sigma T : ℝ) : ℕ :=
  Fintype.card (ResonantZeroOccurrenceQuadruple sigma T)

/-- A coordinate of a replicated resonant zero quadruple. The replication
index affects cardinality only and deliberately does not change the zero. -/
def ResonantZeroOccurrenceQuadruple.coord
    {sigma T : ℝ} (i : Fin 4)
    (q : ResonantZeroOccurrenceQuadruple sigma T) : ℂ :=
  match i with
  | ⟨0, _⟩ => q.1.1.1.1
  | ⟨1, _⟩ => q.1.1.1.2
  | ⟨2, _⟩ => q.1.1.2.1
  | ⟨3, _⟩ => q.1.1.2.2

theorem ResonantZeroOccurrenceQuadruple.coord_mem_zeroSet
    {sigma T : ℝ} (i : Fin 4)
    (q : ResonantZeroOccurrenceQuadruple sigma T) :
    q.coord i ∈ zeroSet sigma T := by
  have hq := (mem_resonantZeroQuadruples.mp q.1.2)
  fin_cases i <;> simp only [coord] <;> tauto

theorem ResonantZeroOccurrenceQuadruple.resonant
    {sigma T : ℝ} (q : ResonantZeroOccurrenceQuadruple sigma T) :
    |(q.coord 0).im + (q.coord 1).im -
        (q.coord 2).im - (q.coord 3).im| ≤ 1 := by
  have hq := (mem_resonantZeroQuadruples.mp q.1.2).2.2.2.2
  simpa only [coord] using hq

/-- Expanding the four sigma types recovers exactly the product analytic
multiplicity in `zeroAdditiveEnergyCount`. -/
theorem zeroOccurrenceAdditiveEnergyCount_eq
    (sigma T : ℝ) :
    zeroOccurrenceAdditiveEnergyCount sigma T =
      zeroAdditiveEnergyCount sigma T := by
  exact zeroAdditiveEnergyOccurrenceCount_eq sigma T

#print axioms zeroOccurrenceAdditiveEnergyCount_eq
#print axioms ResonantZeroOccurrenceQuadruple.coord_mem_zeroSet
#print axioms ResonantZeroOccurrenceQuadruple.resonant

end

end GafniTao
