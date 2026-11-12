import WightmanToAlgebra.Vacuum

/-! Stretch 1 for the polynomial net: the Wightman vacuum is a Poincaré-invariant
vacuum state (FR Def. 25), and every GNS representation of it is unitarily equivalent
to the Wightman fields acting on `A(M) Ω ⊆ D`. -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills MeasureTheory
open scoped ComplexOrder

variable {H : HilbertSpace} {Labels : FieldLabels}

/-- The Wightman vacuum as a state on the polynomial net: `ω(X) = ⟨Ω, X Ω⟩`. -/
def wightmanVacuum (T : WightmanTheory H Labels) (hT : T.Axioms) : (polynomialNet T hT).State :=
  sorry

theorem wightmanVacuum_apply (T : WightmanTheory H Labels) (hT : T.Axioms) (O : Region)
    (X : (polynomialNet T hT).Alg O) :
    (wightmanVacuum T hT).ω O X = inner ℂ T.fields.vacuum.1 (polyVal T hT X T.fields.vacuum).1 := by
  sorry

/-- The Wightman representation: `K` = closure of `A(M) Ω` in `H`, domain `A(M) Ω ⊆ D`,
fields acting by restriction. -/
def wightmanGNS (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (polynomialNet T hT).GNSRepresentation (wightmanVacuum T hT) :=
  sorry

/-- The domain of the Wightman GNS representation sits inside the Wightman domain
and the local algebras act there by the Wightman field polynomials themselves. -/
theorem wightmanGNS_spec (T : WightmanTheory H Labels) (hT : T.Axioms) :
    ∃ ι : (wightmanGNS T hT).domain →ₗ[ℂ] T.fields.domain,
      (∀ u v, inner ℂ (ι u).1 (ι v).1 = inner ℂ u.1 v.1) ∧
      ι (wightmanGNS T hT).vector = T.fields.vacuum ∧
      ∀ (O : Region) (X : (polynomialNet T hT).Alg O) u,
        ι ((wightmanGNS T hT).π O X u) = polyVal T hT X (ι u) := by
  sorry

/-- Stretch 1: the Wightman vacuum is a Poincaré-invariant vacuum state on the net. -/
theorem wightmanVacuum_isVacuum (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (wightmanVacuum T hT).IsVacuum (polynomialCovariance T hT) := by
  sorry

/-- Stretch 1: every GNS representation of the Wightman vacuum is unitarily
equivalent to the Wightman fields acting on `A(M) Ω`. -/
theorem gns_recovers_wightman (T : WightmanTheory H Labels) (hT : T.Axioms)
    (R : (polynomialNet T hT).GNSRepresentation (wightmanVacuum T hT)) :
    R.Equivalent (wightmanGNS T hT) :=
  R.equivalent _

end WightmanToAlgebra
