import WightmanToAlgebra.PolynomialNet
import WightmanToAlgebra.Locality
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

theorem polyVal_mul' (T : WightmanTheory H Labels) (hT : T.Axioms) {O : Region}
    (X Y : (polynomialNet T hT).Alg O) :
    polyVal T hT (X * Y) = polyVal T hT X * polyVal T hT Y := by
  unfold polyVal
  exact Subalgebra.coe_mul _ _ _

-- Proofs go through `polyVal_incl`: `Subtype.ext rfl` makes the kernel unfold the
-- `choose`-based star and time out.
theorem polynomialNet_isotony (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (polynomialNet T hT).Isotony where
  injective {_ O₂} h a b hab := by
    apply polyVal_injective T hT
    rw [← polyVal_incl T hT h a, ← polyVal_incl T hT h b, hab]
  refl O := by
    refine StarAlgHom.ext fun a => ?_
    apply polyVal_injective T hT O
    rw [polyVal_incl]
    rfl
  trans {_ _ O₃} h₁₂ h₂₃ := by
    refine StarAlgHom.ext fun a => ?_
    apply polyVal_injective T hT O₃
    rw [StarAlgHom.comp_apply, polyVal_incl, polyVal_incl, polyVal_incl]

theorem polynomialNet_einsteinCausality (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (polynomialNet T hT).EinsteinCausality := by
  intro O₁ O₂ O h₁ h₂ hd a b
  apply polyVal_injective T hT O
  rw [polyVal_mul', polyVal_mul', polyVal_incl, polyVal_incl]
  exact (polynomialAlgebra_commute T.fields hT.w3.locality hd
    (polyVal_mem T hT a) (polyVal_mem T hT b)).eq

/-- Wightman W0–W3 give a net satisfying isotony, Einstein causality and
Poincaré covariance in the Fewster–Rejzner sense. Timeslice is not claimed:
it does not follow from W0–W3 for polynomial field algebras in general. -/
theorem wightman_to_haagKastler (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (polynomialNet T hT).Isotony ∧
    (polynomialNet T hT).EinsteinCausality ∧
    (polynomialNet T hT).Covariant (polynomialCovariance T hT) :=
  ⟨polynomialNet_isotony T hT, polynomialNet_einsteinCausality T hT,
    polynomialCovariance_covariant T hT⟩

/-- The Yang–Mills hierarchies of the upstream result carry Haag–Kastler nets:
the polynomial field net of the hierarchy's own Wightman theory. -/
theorem yangMills_haagKastler (hYM : JointExistence) :
    ∀ g : GaugeGroup, g.IsSimple → ∃ C : WilsonFamily g, WilsonRegularity C ∧
      ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ T : Hierarchy C, T.Properties (p ∘ q) ∧
          ∃ hax : T.theory.Axioms,
            (polynomialNet T.theory hax).Isotony ∧
            (polynomialNet T.theory hax).EinsteinCausality ∧
            (polynomialNet T.theory hax).Covariant (polynomialCovariance T.theory hax) := by
  intro g hg
  obtain ⟨C, hreg, hC⟩ := hYM g hg
  refine ⟨C, hreg, fun p hp => ?_⟩
  obtain ⟨q, hq, T, hT⟩ := hC p hp
  exact ⟨q, hq, T, hT, hT.reconstruction.axioms,
    wightman_to_haagKastler T.theory hT.reconstruction.axioms⟩

end WightmanToAlgebra
