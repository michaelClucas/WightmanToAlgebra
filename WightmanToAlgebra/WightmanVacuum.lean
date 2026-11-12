import WightmanToAlgebra.WightmanVacuumAux

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
def wightmanVacuum (T : WightmanTheory H Labels) (hT : T.Axioms) : (polynomialNet T hT).State where
  ω O :=
    { toFun := fun X => inner ℂ T.fields.vacuum.1 (polyVal T hT X T.fields.vacuum).1
      map_add' := fun X Y => by
        rw [polyVal_add', LinearMap.add_apply, Submodule.coe_add, inner_add_right]
      map_smul' := fun c X => by
        rw [polyVal_smul', LinearMap.smul_apply, Submodule.coe_smul, inner_smul_right]
        rfl }
  normalized O := by
    show inner ℂ T.fields.vacuum.1 (polyVal T hT 1 T.fields.vacuum).1 = 1
    rw [polyVal_one', Module.End.one_apply, inner_self_eq_norm_sq_to_K,
      hT.w1.domain.normalizedVacuum]
    simp
  positive O a := by
    show 0 ≤ inner ℂ T.fields.vacuum.1 (polyVal T hT (star a * a) T.fields.vacuum).1
    rw [polyVal_mul'', Module.End.mul_apply,
      ← isFormalAdjoint_polyVal_star T hT a T.fields.vacuum (polyVal T hT a T.fields.vacuum),
      inner_self_eq_norm_sq_to_K]
    exact pow_nonneg (Complex.zero_le_real.mpr (norm_nonneg (polyVal T hT a T.fields.vacuum).1)) 2
  compatible h a := by
    show inner ℂ T.fields.vacuum.1 (polyVal T hT ((polynomialNet T hT).incl h a)
      T.fields.vacuum).1 = inner ℂ T.fields.vacuum.1 (polyVal T hT a T.fields.vacuum).1
    rw [polyVal_incl]

theorem wightmanVacuum_apply (T : WightmanTheory H Labels) (hT : T.Axioms) (O : Region)
    (X : (polynomialNet T hT).Alg O) :
    (wightmanVacuum T hT).ω O X = inner ℂ T.fields.vacuum.1 (polyVal T hT X T.fields.vacuum).1 := by
  rfl

/-- The Wightman representation: `K` = closure of `A(M) Ω` in `H`, domain `A(M) Ω ⊆ D`,
fields acting by restriction. -/
def wightmanGNS (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (polynomialNet T hT).GNSRepresentation (wightmanVacuum T hT) where
  K := gnsSpace T hT
  domain := gnsDomain T hT
  dense := gnsDomain_dense T hT
  vector := gnsVector T hT
  π := gnsπ T hT
  compatible h a := by
    refine LinearMap.ext fun w => gnsDomain_ext T hT ?_
    rw [gnsπ_apply, gnsπ_apply, gnsAct_coe, gnsAct_coe, polyVal_incl]
  star O a u v := by
    rw [gnsπ_apply, gnsπ_apply, gnsInner, gnsInner, gnsIncl_gnsAct, gnsIncl_gnsAct]
    exact isFormalAdjoint_polyVal_star T hT a _ _
  cyclic u := by
    obtain ⟨O, X, hX⟩ := (mem_cyclicH T hT).mp u.2
    refine ⟨O, X, gnsDomain_ext T hT ?_⟩
    rw [gnsπ_apply, gnsAct_coe, gnsIncl_vector]
    exact hX
  expectation O a := by
    rw [wightmanVacuum_apply, gnsπ_apply, gnsInner, gnsIncl_gnsAct, gnsIncl_vector]

/-- The domain of the Wightman GNS representation sits inside the Wightman domain
and the local algebras act there by the Wightman field polynomials themselves. -/
theorem wightmanGNS_spec (T : WightmanTheory H Labels) (hT : T.Axioms) :
    ∃ ι : (wightmanGNS T hT).domain →ₗ[ℂ] T.fields.domain,
      (∀ u v, inner ℂ (ι u).1 (ι v).1 = inner ℂ u.1 v.1) ∧
      ι (wightmanGNS T hT).vector = T.fields.vacuum ∧
      ∀ (O : Region) (X : (polynomialNet T hT).Alg O) u,
        ι ((wightmanGNS T hT).π O X u) = polyVal T hT X (ι u) := by
  refine ⟨{ toFun := gnsIncl T hT, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun _ _ => rfl, rfl, fun _ _ _ => rfl⟩

/-- The translations restricted to `K` fix `Ω` and implement `α` on translations. -/
def wightmanTranslationImplementation (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (wightmanGNS T hT).TranslationImplementation (polynomialCovariance T hT) where
  U := gnsTranslationAction T hT
  fixes x := Subtype.ext (translations_vacuum T hT x)
  implements x O a := by
    apply Subtype.ext
    show T.translations.operator x (polyVal T hT a (gnsIncl T hT (gnsVector T hT))).1 =
      (polyVal T hT ((polynomialCovariance T hT).act (translationCoords x) O a)
        (gnsIncl T hT (gnsVector T hT))).1
    rw [gnsIncl_vector, polynomialCovariance_act, translations_polyVal_vacuum]

theorem wightmanVacuum_invariant (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (wightmanVacuum T hT).Invariant (polynomialCovariance T hT) := by
  intro g O a
  rw [wightmanVacuum_apply, wightmanVacuum_apply, polynomialCovariance_act,
    polyVal_polynomialAct, domainConj_vacuum]
  have h := domainEquiv_inner T hT g T.fields.vacuum (polyVal T hT a T.fields.vacuum)
  rw [domainEquiv_vacuum] at h
  exact h

/-- Stretch 1: the Wightman vacuum is a Poincaré-invariant vacuum state on the net. -/
theorem wightmanVacuum_isVacuum (T : WightmanTheory H Labels) (hT : T.Axioms) :
    (wightmanVacuum T hT).IsVacuum (polynomialCovariance T hT) := by
  refine ⟨wightmanVacuum_invariant T hT, ?_⟩
  refine ⟨wightmanGNS T hT, wightmanTranslationImplementation T hT, ?_, ?_⟩
  · rintro ⟨v, hv⟩
    refine ⟨T.energyMomentum.diagonal v, inferInstance,
      fun x => hT.w0.spectralRepresentation v x, ?_⟩
    have hm : MeasurableSet (forwardConeᶜ) := isClosed_forwardCone.measurableSet.compl
    have h := T.energyMomentum.diagonalIdentity hm v
    rw [hT.w0.positiveEnergy, zero_apply, inner_zero_right,
      Complex.ofReal_eq_zero] at h
    exact (measureReal_eq_zero_iff).mp h
  · rintro ⟨v, hv⟩ hψ
    obtain ⟨c, hc⟩ := hT.w0.uniqueVacuum v fun x => congrArg Subtype.val (hψ x)
    exact ⟨c, Subtype.ext hc.symm⟩

/-- Stretch 1: every GNS representation of the Wightman vacuum is unitarily
equivalent to the Wightman fields acting on `A(M) Ω`. -/
theorem gns_recovers_wightman (T : WightmanTheory H Labels) (hT : T.Axioms)
    (R : (polynomialNet T hT).GNSRepresentation (wightmanVacuum T hT)) :
    R.Equivalent (wightmanGNS T hT) :=
  R.equivalent _

end WightmanToAlgebra
