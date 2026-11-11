import PublicTheory

/-! Causal structure of Minkowski space and the index set of an AQFT net.

Spacetime, the forward cone and `spacelike` are reused from the upstream
`PublicTheory` so that the AQFT statement and the Wightman statement refer to
literally the same geometry (time is the last coordinate). -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills Set Filter

/-- `CausalLE x y`: `y` lies in the closed causal future of `x`. -/
def CausalLE (x y : Spacetime) : Prop := y - x ∈ forwardCone

/-- Every point of `A` is spacelike to every point of `B`. -/
def CausallyDisjoint (A B : Set Spacetime) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x - y ∈ spacelike

/-- Order-convexity for the causal order. In Minkowski space this is
equivalent to containing every causal curve that starts and ends in `A`. -/
def CausallyConvex (A : Set Spacetime) : Prop :=
  ∀ x ∈ A, ∀ z ∈ A, ∀ y, CausalLE x y → CausalLE y z → y ∈ A

/-- A future-directed causal curve that is inextendible in both directions. -/
structure InextendibleCausalCurve where
  path : ℝ → Spacetime
  continuous : Continuous path
  causal : ∀ s t, s ≤ t → CausalLE (path s) (path t)
  toFuture : Tendsto (fun t ↦ time (path t)) atTop atTop
  toPast : Tendsto (fun t ↦ time (path t)) atBot atBot

/-- Domain of dependence: points every inextendible causal curve through which
meets `A`. -/
def dependenceDomain (A : Set Spacetime) : Set Spacetime :=
  {x | ∀ γ : InextendibleCausalCurve, x ∈ range γ.path → (range γ.path ∩ A).Nonempty}

/-- Index set of the net: nonempty open bounded causally convex regions. -/
structure Region where
  carrier : Set Spacetime
  isOpen : IsOpen carrier
  bounded : Bornology.IsBounded carrier
  nonempty : carrier.Nonempty
  causallyConvex : CausallyConvex carrier

/-! ## Poincaré action on regions -/

/-- Affine action `x ↦ Λ x + a` of `(Λ, a)`. -/
def poincareAct (g : PoincareCoordinates) (x : Spacetime) : Spacetime :=
  g.1.val.val x + g.2

theorem properLorentz_mul_mem (Λ M : ProperLorentz) :
    LinearMap.det (Λ.val * M.val).val.toLinearMap = 1 ∧
    (∀ x, minkowskiSquare ((Λ.val * M.val).val x) = minkowskiSquare x) ∧
    (∀ x, (Λ.val * M.val).val x ∈ forwardCone ↔ x ∈ forwardCone) := by
  obtain ⟨Λ, hΛd, hΛm, hΛc⟩ := Λ
  obtain ⟨M, hMd, hMm, hMc⟩ := M
  refine ⟨?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · change LinearMap.det ((Λ.val : Spacetime →ₗ[ℝ] Spacetime) ∘ₗ (M.val : _)) = 1
    rw [LinearMap.det_comp, hΛd, hMd, one_mul]
  · simp only [Units.val_mul, mul_apply_eq_comp, hΛm, hMm]
  · simp only [Units.val_mul, mul_apply_eq_comp, hΛc, hMc]

theorem properLorentz_one_mem :
    LinearMap.det (1 : (Spacetime →L[ℝ] Spacetime)ˣ).val.toLinearMap = 1 ∧
    (∀ x, minkowskiSquare ((1 : (Spacetime →L[ℝ] Spacetime)ˣ).val x) = minkowskiSquare x) ∧
    (∀ x, (1 : (Spacetime →L[ℝ] Spacetime)ˣ).val x ∈ forwardCone ↔ x ∈ forwardCone) := by
  refine ⟨?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [Units.val_one, ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id,
      LinearMap.det_id]
  · rfl
  · exact Iff.rfl

def poincareOne : PoincareCoordinates := (⟨1, properLorentz_one_mem⟩, 0)

/-- Group law in coordinates, matching `PoincareAction.productCoordinates`. -/
def poincareMul (g h : PoincareCoordinates) : PoincareCoordinates :=
  (⟨g.1.val * h.1.val, properLorentz_mul_mem g.1 h.1⟩, g.1.val.val h.2 + g.2)

/-- `Λ (Λ⁻¹ v) = v`. -/
theorem lorentz_apply_inv_apply (Λ : ProperLorentz) (v : Spacetime) :
    Λ.val.val (Λ.val⁻¹.val v) = v := by
  rw [← mul_apply_eq_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_apply_eq_self]

/-- `Λ⁻¹ (Λ v) = v`. -/
theorem lorentz_inv_apply_apply (Λ : ProperLorentz) (v : Spacetime) :
    Λ.val⁻¹.val (Λ.val.val v) = v := by
  rw [← mul_apply_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_apply_eq_self]

/-- The image under `poincareAct g` is the preimage under its inverse affine map. -/
theorem poincareAct_image_eq_preimage (g : PoincareCoordinates) (A : Set Spacetime) :
    poincareAct g '' A = (fun y ↦ g.1.val⁻¹.val (y - g.2)) ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [poincareAct, lorentz_inv_apply_apply] using hx
  · intro hy
    refine ⟨_, hy, ?_⟩
    simp [poincareAct, lorentz_apply_inv_apply]

theorem poincareAct_isOpen (g : PoincareCoordinates) {A : Set Spacetime}
    (hA : IsOpen A) : IsOpen (poincareAct g '' A) := by
  rw [poincareAct_image_eq_preimage]
  exact hA.preimage (g.1.val⁻¹.val.continuous.comp (continuous_id.sub continuous_const))

theorem poincareAct_bounded (g : PoincareCoordinates) {A : Set Spacetime}
    (hA : Bornology.IsBounded A) : Bornology.IsBounded (poincareAct g '' A) := by
  have hL : LipschitzWith ‖g.1.val.val‖₊ (poincareAct g) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simp only [poincareAct, dist_add_right]
    exact g.1.val.val.lipschitz.dist_le_mul x y
  exact hL.isBounded_image hA

theorem poincareAct_causallyConvex (g : PoincareCoordinates) {A : Set Spacetime}
    (hA : CausallyConvex A) : CausallyConvex (poincareAct g '' A) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩ y hxy hyz
  have hy : poincareAct g (g.1.val⁻¹.val (y - g.2)) = y := by
    simp [poincareAct, lorentz_apply_inv_apply]
  refine ⟨g.1.val⁻¹.val (y - g.2), hA x hx z hz _ ?_ ?_, hy⟩
  · unfold CausalLE at hxy ⊢
    rw [← g.1.prop.2.2, map_sub, lorentz_apply_inv_apply]
    convert hxy using 1
    simp only [poincareAct]
    abel
  · unfold CausalLE at hyz ⊢
    rw [← g.1.prop.2.2, map_sub, lorentz_apply_inv_apply]
    convert hyz using 1
    simp only [poincareAct]
    abel

namespace Region

def map (g : PoincareCoordinates) (O : Region) : Region where
  carrier := poincareAct g '' O.carrier
  isOpen := poincareAct_isOpen g O.isOpen
  bounded := poincareAct_bounded g O.bounded
  nonempty := O.nonempty.image _
  causallyConvex := poincareAct_causallyConvex g O.causallyConvex

theorem map_mono (g : PoincareCoordinates) {O₁ O₂ : Region}
    (h : O₁.carrier ⊆ O₂.carrier) : (O₁.map g).carrier ⊆ (O₂.map g).carrier :=
  image_mono h

theorem map_one (O : Region) : (O.map poincareOne).carrier = O.carrier := by
  have : poincareAct poincareOne = id := by
    funext x
    simp [poincareAct, poincareOne]
  simp only [map, this, Set.image_id]

theorem map_mul (g h : PoincareCoordinates) (O : Region) :
    ((O.map h).map g).carrier = (O.map (poincareMul g h)).carrier := by
  have : poincareAct (poincareMul g h) = poincareAct g ∘ poincareAct h := by
    funext x
    simp only [poincareAct, poincareMul, Function.comp_apply, Units.val_mul,
      mul_apply_eq_comp, map_add]
    abel
  simp only [map, this, Set.image_comp]

end Region

end WightmanToAlgebra
