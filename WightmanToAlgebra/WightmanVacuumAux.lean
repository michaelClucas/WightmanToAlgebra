import WightmanToAlgebra.Vacuum

/-! Helpers for `WightmanVacuum.lean`: a fixed region,
`polyVal` algebra lemmas, the cyclic subspace `A(M) Ω ⊆ H`, its closure `K`, and
the translations restricted to `K`. -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills MeasureTheory

/-! ## Regions -/

theorem isClosed_forwardCone : IsClosed forwardCone :=
  isClosed_le (continuous_norm.comp continuous_spatial) continuous_time

/-- A fixed region, so that `0 ∈ A(M) Ω` and `Ω ∈ A(M) Ω`. -/
def unitDiamond : Region := doubleCone 1 one_pos

/-! ## `polyVal` lemmas -/

variable {H : HilbertSpace} {Labels : FieldLabels}
variable (T : WightmanTheory H Labels) (hT : T.Axioms)

theorem polyVal_zero' {O : Region} : polyVal T hT (0 : (polynomialNet T hT).Alg O) = 0 := by
  unfold polyVal
  exact ZeroMemClass.coe_zero _

theorem polyVal_one' {O : Region} : polyVal T hT (1 : (polynomialNet T hT).Alg O) = 1 := by
  unfold polyVal
  exact OneMemClass.coe_one _

theorem polyVal_add' {O : Region} (X Y : (polynomialNet T hT).Alg O) :
    polyVal T hT (X + Y) = polyVal T hT X + polyVal T hT Y := by
  unfold polyVal
  exact Subalgebra.coe_add _ _ _

theorem polyVal_smul' {O : Region} (c : ℂ) (X : (polynomialNet T hT).Alg O) :
    polyVal T hT (c • X) = c • polyVal T hT X := by
  unfold polyVal
  exact Subalgebra.coe_smul _ _ _

theorem polyVal_mul'' {O : Region} (X Y : (polynomialNet T hT).Alg O) :
    polyVal T hT (X * Y) = polyVal T hT X * polyVal T hT Y := by
  unfold polyVal
  exact Subalgebra.coe_mul _ _ _

theorem polyVal_algebraMap' {O : Region} (c : ℂ) :
    polyVal T hT (algebraMap ℂ ((polynomialNet T hT).Alg O) c) =
      algebraMap ℂ (Module.End ℂ T.fields.domain) c := by
  unfold polyVal
  exact Subalgebra.coe_algebraMap _ _

theorem polynomialCovariance_act (g : PoincareCoordinates) (O : Region)
    (X : (polynomialNet T hT).Alg O) :
    (polynomialCovariance T hT).act g O X = polynomialAct T hT g O X := rfl

/-! ## Vacuum invariance on the domain -/

theorem domainEquiv_vacuum (g : PoincareCoordinates) :
    domainEquiv T hT g T.fields.vacuum = T.fields.vacuum :=
  Subtype.ext (hT.w2.vacuumInvariant _)

theorem domainEquiv_symm_vacuum (g : PoincareCoordinates) :
    (domainEquiv T hT g).symm T.fields.vacuum = T.fields.vacuum := by
  conv_lhs => rw [← domainEquiv_vacuum T hT g]
  exact (domainEquiv T hT g).symm_apply_apply _

theorem domainConj_vacuum (g : PoincareCoordinates) (X : Module.End ℂ T.fields.domain) :
    domainConj T hT g X T.fields.vacuum = domainEquiv T hT g (X T.fields.vacuum) := by
  rw [domainConj_apply, domainEquiv_symm_vacuum]

theorem pureTranslation_eq (x : Spacetime) :
    T.poincare.pureTranslation x = T.poincare.coordinates.symm (translationCoords x) := by
  apply T.poincare.coordinates.injective
  rw [Homeomorph.apply_symm_apply]
  exact poincareCoordinates_ext (T.poincare.translationCoordinates x).1
    (T.poincare.translationCoordinates x).2

theorem translations_eq_onStates (x : Spacetime) (v : H.carrier) :
    T.translations.operator x v = T.poincare.onStates (symOf T (translationCoords x)) v := by
  rw [← T.translationCompatibility, pureTranslation_eq]

/-- `U(x) X Ω = (α_x X) Ω`. -/
theorem translations_polyVal_vacuum (x : Spacetime) {O : Region}
    (X : (polynomialNet T hT).Alg O) :
    T.translations.operator x (polyVal T hT X T.fields.vacuum).1 =
      (polyVal T hT (polynomialAct T hT (translationCoords x) O X) T.fields.vacuum).1 := by
  rw [polyVal_polynomialAct, domainConj_vacuum, domainEquiv_apply, translations_eq_onStates]

include hT in
theorem translations_vacuum (x : Spacetime) :
    T.translations.operator x T.fields.vacuum.1 = T.fields.vacuum.1 := by
  rw [translations_eq_onStates]
  exact hT.w2.vacuumInvariant _

/-! ## The cyclic subspace `A(M) Ω` and its closure -/

/-- `A(M) Ω` as a subspace of `H`. -/
def cyclicH : Submodule ℂ H.carrier where
  carrier := {v | ∃ (O : Region) (X : (polynomialNet T hT).Alg O),
    v = (polyVal T hT X T.fields.vacuum).1}
  zero_mem' := ⟨unitDiamond, 0, by rw [polyVal_zero']; rfl⟩
  add_mem' := by
    rintro _ _ ⟨O₁, X₁, rfl⟩ ⟨O₂, X₂, rfl⟩
    obtain ⟨O, h₁, h₂⟩ := Region.exists_common O₁ O₂
    refine ⟨O, (polynomialNet T hT).incl h₁ X₁ + (polynomialNet T hT).incl h₂ X₂, ?_⟩
    rw [polyVal_add', polyVal_incl, polyVal_incl]
    rfl
  smul_mem' := by
    rintro c _ ⟨O, X, rfl⟩
    refine ⟨O, c • X, ?_⟩
    rw [polyVal_smul']
    rfl

theorem mem_cyclicH {v : H.carrier} :
    v ∈ cyclicH T hT ↔ ∃ (O : Region) (X : (polynomialNet T hT).Alg O),
      v = (polyVal T hT X T.fields.vacuum).1 := Iff.rfl

theorem polyVal_vacuum_mem_cyclicH {O : Region} (X : (polynomialNet T hT).Alg O) :
    (polyVal T hT X T.fields.vacuum).1 ∈ cyclicH T hT := ⟨O, X, rfl⟩

theorem vacuum_mem_cyclicH : T.fields.vacuum.1 ∈ cyclicH T hT :=
  ⟨unitDiamond, 1, by rw [polyVal_one']; rfl⟩

theorem cyclicH_le : cyclicH T hT ≤ T.fields.domain := by
  rintro _ ⟨O, X, rfl⟩
  exact (polyVal T hT X T.fields.vacuum).2

/-- `A(M) Ω` is invariant under every `X ∈ P(O)`. -/
theorem polyVal_mem_cyclicH {O : Region} (X : (polynomialNet T hT).Alg O) {v : H.carrier}
    (hv : v ∈ cyclicH T hT) :
    (polyVal T hT X ⟨v, cyclicH_le T hT hv⟩).1 ∈ cyclicH T hT := by
  obtain ⟨O', Y, rfl⟩ := hv
  obtain ⟨O'', h₁, h₂⟩ := Region.exists_common O O'
  refine ⟨O'', (polynomialNet T hT).incl h₁ X * (polynomialNet T hT).incl h₂ Y, ?_⟩
  rw [polyVal_mul'', polyVal_incl, polyVal_incl]
  rfl

/-- The GNS Hilbert space: closure of `A(M) Ω`. -/
abbrev cyclicClosure : Submodule ℂ H.carrier := (cyclicH T hT).topologicalClosure

abbrev gnsSpace : HilbertSpace where
  carrier := cyclicClosure T hT

/-- The GNS domain inside `K`. -/
def gnsDomain : Submodule ℂ (gnsSpace T hT).carrier :=
  (cyclicH T hT).comap (cyclicClosure T hT).subtype

theorem gnsDomain_dense : Dense (gnsDomain T hT : Set (gnsSpace T hT).carrier) := by
  show Dense (((cyclicH T hT).comap (cyclicClosure T hT).subtype : Set (cyclicClosure T hT)))
  rw [Subtype.dense_iff]
  intro v hv
  have hsub : (cyclicH T hT : Set H.carrier) ⊆
      (Subtype.val '' (((cyclicH T hT).comap (cyclicClosure T hT).subtype :
        Set (cyclicClosure T hT)))) := fun w hw =>
    ⟨⟨w, (cyclicH T hT).le_topologicalClosure hw⟩, hw, rfl⟩
  have hv' : v ∈ closure (cyclicH T hT : Set H.carrier) := by
    rw [← Submodule.topologicalClosure_coe]; exact hv
  exact closure_mono hsub hv'

/-! ## The GNS representation on `K` -/

/-- The vacuum as an element of the GNS domain. -/
def gnsVector : gnsDomain T hT :=
  ⟨⟨T.fields.vacuum.1, (cyclicH T hT).le_topologicalClosure (vacuum_mem_cyclicH T hT)⟩,
    vacuum_mem_cyclicH T hT⟩

/-- An element of the GNS domain, as an element of the Wightman domain. -/
def gnsIncl (w : gnsDomain T hT) : T.fields.domain :=
  ⟨w.1.1, cyclicH_le T hT w.2⟩

/-- `X ∈ P(O)` acting on `A(M) Ω`. -/
def gnsAct {O : Region} (X : (polynomialNet T hT).Alg O) : Module.End ℂ (gnsDomain T hT) where
  toFun w := ⟨⟨(polyVal T hT X (gnsIncl T hT w)).1,
      (cyclicH T hT).le_topologicalClosure (polyVal_mem_cyclicH T hT X w.2)⟩,
    polyVal_mem_cyclicH T hT X w.2⟩
  map_add' a b := by
    ext
    show (polyVal T hT X (gnsIncl T hT a + gnsIncl T hT b)).1 = _
    rw [map_add]
    rfl
  map_smul' c a := by
    ext
    show (polyVal T hT X (c • gnsIncl T hT a)).1 = _
    rw [map_smul]
    rfl

theorem gnsAct_coe {O : Region} (X : (polynomialNet T hT).Alg O) (w : gnsDomain T hT) :
    (gnsAct T hT X w).1.1 =
      (polyVal T hT X (gnsIncl T hT w)).1 := rfl

theorem gnsIncl_gnsAct {O : Region} (X : (polynomialNet T hT).Alg O) (w : gnsDomain T hT) :
    gnsIncl T hT (gnsAct T hT X w) = polyVal T hT X (gnsIncl T hT w) := rfl

theorem gnsIncl_vector : gnsIncl T hT (gnsVector T hT) = T.fields.vacuum := rfl

theorem gnsDomain_ext {a b : gnsDomain T hT}
    (h : a.1.1 = b.1.1) :
    a = b :=
  Subtype.ext (Subtype.ext h)

/-- The representation `π_O`. -/
def gnsπ (O : Region) :
    (polynomialNet T hT).Alg O →ₐ[ℂ] Module.End ℂ (gnsDomain T hT) where
  toFun := gnsAct T hT
  map_one' := by
    refine LinearMap.ext fun w => gnsDomain_ext T hT ?_
    rw [gnsAct_coe, polyVal_one']
    rfl
  map_mul' X Y := by
    refine LinearMap.ext fun w => gnsDomain_ext T hT ?_
    rw [gnsAct_coe, polyVal_mul'', Module.End.mul_apply, Module.End.mul_apply, gnsAct_coe,
      gnsIncl_gnsAct]
  map_zero' := by
    refine LinearMap.ext fun w => gnsDomain_ext T hT ?_
    rw [gnsAct_coe, polyVal_zero']
    rfl
  map_add' X Y := by
    refine LinearMap.ext fun w => gnsDomain_ext T hT ?_
    rw [gnsAct_coe, polyVal_add']
    rfl
  commutes' c := by
    refine LinearMap.ext fun w => gnsDomain_ext T hT ?_
    rw [gnsAct_coe, polyVal_algebraMap']
    rfl

theorem gnsπ_apply {O : Region} (X : (polynomialNet T hT).Alg O) (w : gnsDomain T hT) :
    gnsπ T hT O X w = gnsAct T hT X w := rfl

theorem gnsInner (a b : gnsDomain T hT) :
    inner ℂ a.1 b.1 =
      inner ℂ (gnsIncl T hT a).1 (gnsIncl T hT b).1 := rfl

/-! ## Translations restricted to `K` -/

theorem translations_mapsTo_cyclicH (x : Spacetime) {v : H.carrier} (hv : v ∈ cyclicH T hT) :
    T.translations.operator x v ∈ cyclicH T hT := by
  obtain ⟨O, X, rfl⟩ := hv
  rw [translations_polyVal_vacuum]
  exact polyVal_vacuum_mem_cyclicH T hT _

theorem translations_mapsTo_closure (x : Spacetime) {v : H.carrier}
    (hv : v ∈ cyclicClosure T hT) :
    T.translations.operator x v ∈ cyclicClosure T hT := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv ⊢
  have h := image_closure_subset_closure_image (T.translations.operator x).continuous
    (Set.mem_image_of_mem _ hv)
  refine closure_mono ?_ h
  rintro _ ⟨w, hw, rfl⟩
  exact translations_mapsTo_cyclicH T hT x hw

/-- `U(x)` restricted to `K`. -/
def gnsTranslation (x : Spacetime) : (gnsSpace T hT).Operator :=
  ((T.translations.operator x).comp (cyclicClosure T hT).subtypeL).codRestrict
    (cyclicClosure T hT) fun v => translations_mapsTo_closure T hT x v.2

theorem gnsTranslation_coe (x : Spacetime) (v : (gnsSpace T hT).carrier) :
    ((gnsTranslation T hT x v : cyclicClosure T hT) : H.carrier) =
      T.translations.operator x (v : cyclicClosure T hT) := rfl

def gnsTranslationAction : TranslationAction (gnsSpace T hT) where
  operator := gnsTranslation T hT
  identity := by
    ext v
    rw [gnsTranslation_coe, T.translations.identity]
    rfl
  add x y := by
    ext v
    rw [ContinuousLinearMap.comp_apply, gnsTranslation_coe, gnsTranslation_coe,
      gnsTranslation_coe, ← T.translations.add]
    rfl
  unitary x v := by
    show ‖(gnsTranslation T hT x v : H.carrier)‖ = ‖(v : H.carrier)‖
    rw [gnsTranslation_coe]
    exact T.translations.unitary x _
  stronglyContinuous v := by
    show Continuous fun x => gnsTranslation T hT x v
    exact (T.translations.stronglyContinuous (v : cyclicClosure T hT)).subtype_mk _

end WightmanToAlgebra
