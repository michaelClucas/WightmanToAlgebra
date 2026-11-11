import WightmanToAlgebra.Regions

/-! Group-theoretic helpers for the upstream `PoincareAction`.

Upstream `Symmetry` only carries `One` and `Mul`. Inverses are produced through
the coordinate homeomorphism: `coordinates.symm (Λ⁻¹, -Λ⁻¹ a)` is a two-sided
inverse of `coordinates.symm (Λ, a)`. We also record how `onTests` moves
topological supports (by the affine map `poincareAct`). -/

set_option autoImplicit false
noncomputable section

namespace WightmanToAlgebra

open YangMills

/-- The inverse of a proper orthochronous Lorentz transformation is again one. -/
theorem properLorentz_inv_mem (Λ : ProperLorentz) :
    LinearMap.det (Λ.val⁻¹).val.toLinearMap = 1 ∧
    (∀ x, minkowskiSquare ((Λ.val⁻¹).val x) = minkowskiSquare x) ∧
    (∀ x, (Λ.val⁻¹).val x ∈ forwardCone ↔ x ∈ forwardCone) := by
  obtain ⟨u, hdet, hsq, hcone⟩ := Λ
  have key : ∀ x, u.val ((u⁻¹).val x) = x := fun x => by
    rw [← mul_apply_eq_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_apply_eq_self]
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · have h : u.val.toLinearMap * (u⁻¹).val.toLinearMap = 1 := by
      ext x
      simp [key]
    have := congrArg LinearMap.det h
    rw [map_mul, map_one, hdet, one_mul] at this
    exact this
  · have := hsq ((u⁻¹).val x)
    rw [key] at this
    exact this.symm
  · have := hcone ((u⁻¹).val x)
    rw [key] at this
    exact this.symm

/-- Inverse in Poincaré coordinates: `(Λ, a)⁻¹ = (Λ⁻¹, -Λ⁻¹ a)`. -/
def poincareInv (g : PoincareCoordinates) : PoincareCoordinates :=
  (⟨g.1.val⁻¹, properLorentz_inv_mem g.1⟩, -((g.1.val⁻¹).val g.2))

theorem poincareCoordinates_ext {p q : PoincareCoordinates} (h₁ : p.1.val = q.1.val)
    (h₂ : p.2 = q.2) : p = q :=
  Prod.ext (Subtype.ext h₁) h₂

/-- `poincareAct g` as a homeomorphism of spacetime, with inverse `x ↦ Λ⁻¹ (x - a)`. -/
def poincareHomeomorph (g : PoincareCoordinates) : Spacetime ≃ₜ Spacetime where
  toFun := poincareAct g
  invFun x := (g.1.val⁻¹).val (x - g.2)
  left_inv x := by simp [poincareAct, lorentz_inv_apply_apply]
  right_inv x := by simp [poincareAct, lorentz_apply_inv_apply]
  continuous_toFun := g.1.val.val.continuous.add continuous_const
  continuous_invFun := (g.1.val⁻¹).val.continuous.comp (continuous_id.sub continuous_const)

@[simp] theorem poincareHomeomorph_apply (g : PoincareCoordinates) (x : Spacetime) :
    poincareHomeomorph g x = poincareAct g x := rfl

theorem poincareHomeomorph_symm_apply (g : PoincareCoordinates) (x : Spacetime) :
    (poincareHomeomorph g).symm x = (g.1.val⁻¹).val (x - g.2) := rfl

namespace PoincareActionAux

variable {H : HilbertSpace} {Labels : FieldLabels} (P : PoincareAction H Labels)

theorem coordinates_mul_fst (s t : P.Symmetry) :
    (P.coordinates (s * t)).1.val = (P.coordinates s).1.val * (P.coordinates t).1.val :=
  (P.productCoordinates s t).1

theorem coordinates_mul_snd (s t : P.Symmetry) :
    (P.coordinates (s * t)).2 =
      (P.coordinates s).1.val.val (P.coordinates t).2 + (P.coordinates s).2 :=
  (P.productCoordinates s t).2

theorem symm_poincareOne : P.coordinates.symm poincareOne = 1 := by
  apply P.coordinates.injective
  rw [Homeomorph.apply_symm_apply]
  exact poincareCoordinates_ext P.identityCoordinates.1.symm P.identityCoordinates.2.symm

theorem symm_poincareMul (g h : PoincareCoordinates) :
    P.coordinates.symm (poincareMul g h) = P.coordinates.symm g * P.coordinates.symm h := by
  apply P.coordinates.injective
  rw [Homeomorph.apply_symm_apply]
  refine poincareCoordinates_ext ?_ ?_
  · rw [coordinates_mul_fst, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    rfl
  · rw [coordinates_mul_snd, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    rfl

theorem symm_mul_symm_inv (g : PoincareCoordinates) :
    P.coordinates.symm g * P.coordinates.symm (poincareInv g) = 1 := by
  apply P.coordinates.injective
  refine poincareCoordinates_ext ?_ ?_
  · rw [coordinates_mul_fst, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
      P.identityCoordinates.1]
    exact mul_inv_cancel _
  · rw [coordinates_mul_snd, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
      P.identityCoordinates.2]
    simp [poincareInv, lorentz_apply_inv_apply]

theorem symm_inv_mul_symm (g : PoincareCoordinates) :
    P.coordinates.symm (poincareInv g) * P.coordinates.symm g = 1 := by
  apply P.coordinates.injective
  refine poincareCoordinates_ext ?_ ?_
  · rw [coordinates_mul_fst, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
      P.identityCoordinates.1]
    exact inv_mul_cancel _
  · rw [coordinates_mul_snd, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
      P.identityCoordinates.2]
    simp [poincareInv]

theorem onStates_apply_apply {s t : P.Symmetry} (h : s * t = 1) (x : H.carrier) :
    P.onStates s (P.onStates t x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← P.composition, h, P.identity]
  rfl

theorem onStates_inner (s : P.Symmetry) (x y : H.carrier) :
    inner ℂ (P.onStates s x) (P.onStates s y) = inner ℂ x y :=
  (LinearMap.norm_map_iff_inner_map_map (P.onStates s)).mp (P.unitary s) x y

theorem onTests_one (f : TestFunction) : P.onTests 1 f = f := by
  ext x
  rw [P.pullback]
  congr 1
  have h1 : (P.coordinates 1).1.val = 1 := P.identityCoordinates.1
  rw [h1, P.identityCoordinates.2, inv_one, sub_zero]
  rfl

theorem onTests_mul (s t : P.Symmetry) (f : TestFunction) :
    P.onTests s (P.onTests t f) = P.onTests (s * t) f := by
  ext x
  rw [P.pullback, P.pullback, P.pullback]
  congr 1
  rw [coordinates_mul_fst, coordinates_mul_snd, mul_inv_rev, Units.val_mul,
    mul_apply_eq_comp]
  congr 1
  rw [show ∀ a b c : Spacetime, a - (b + c) = (a - c) - b from fun a b c => by abel]
  simp only [map_sub, lorentz_inv_apply_apply]

theorem onTests_apply_apply {s t : P.Symmetry} (h : s * t = 1) (f : TestFunction) :
    P.onTests s (P.onTests t f) = f := by
  rw [onTests_mul, h, onTests_one]

/-- `onTests s` moves topological supports by the affine map of `coordinates s`. -/
theorem tsupport_onTests (s : P.Symmetry) (f : TestFunction) :
    tsupport (P.onTests s f : Spacetime → ℂ) =
      poincareAct (P.coordinates s) '' tsupport (f : Spacetime → ℂ) := by
  have hfun : (P.onTests s f : Spacetime → ℂ) =
      (f : Spacetime → ℂ) ∘ (poincareHomeomorph (P.coordinates s)).symm := by
    funext x
    rw [P.pullback]
    rfl
  rw [hfun, tsupport_comp_eq_preimage, Homeomorph.preimage_symm]
  rfl

end PoincareActionAux

end WightmanToAlgebra
