import WightmanToAlgebra.PolynomialNet
import ChallengeSpec

/-! Main statements.

`JointExistence` is taken as a hypothesis so this library only builds the
upstream statement files (Mathlib-only import closure). The upstream proof is
`YangMills.jointExistence` in `Solution.lean`; importing it discharges the
hypothesis at the cost of building the full construction. -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- Wightman W0–W3 give a net satisfying isotony, Einstein causality and
Poincaré covariance in the Fewster–Rejzner sense. Timeslice is not claimed:
it does not follow from W0–W3 for polynomial field algebras in general. -/
theorem wightman_to_haagKastler (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (polynomialNet T hT).Isotony ∧
    (polynomialNet T hT).EinsteinCausality ∧
    (polynomialNet T hT).Covariant (polynomialCovariance T hT) := by
  sorry

/-- The Yang–Mills hierarchies of the upstream result carry Haag–Kastler nets. -/
theorem yangMills_haagKastler (hYM : JointExistence) :
    ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g,
      ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, ∃ N : Net, ∃ α : N.Covariance,
          N.Isotony ∧ N.EinsteinCausality ∧ N.Covariant α := by
  intro g hg
  obtain ⟨C, -, hC⟩ := hYM g hg
  refine ⟨C, fun p hp => ?_⟩
  obtain ⟨q, hq, T, hT⟩ := hC p hp
  have hax := hT.reconstruction.axioms
  exact ⟨q, hq, T, polynomialNet T.theory hax, polynomialCovariance T.theory hax,
    wightman_to_haagKastler T.theory hax⟩

end WightmanToAlgebra
