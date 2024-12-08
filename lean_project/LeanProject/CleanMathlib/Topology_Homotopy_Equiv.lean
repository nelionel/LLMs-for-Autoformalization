import Mathlib.Topology.Homotopy.Basic
universe u v w x
variable {X : Type u} {Y : Type v} {Z : Type w} {Z' : Type x}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']
namespace ContinuousMap
@[ext]
structure HomotopyEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : C(X, Y)
  invFun : C(Y, X)
  left_inv : (invFun.comp toFun).Homotopic (ContinuousMap.id X)
  right_inv : (toFun.comp invFun).Homotopic (ContinuousMap.id Y)
scoped infixl:25 " ≃ₕ " => ContinuousMap.HomotopyEquiv
namespace HomotopyEquiv
@[coe] def toFun' (e : X ≃ₕ Y) : X → Y := e.toFun
instance : CoeFun (X ≃ₕ Y) fun _ => X → Y := ⟨toFun'⟩
@[simp]
theorem toFun_eq_coe (h : HomotopyEquiv X Y) : (h.toFun : X → Y) = h :=
  rfl
@[continuity]
theorem continuous (h : HomotopyEquiv X Y) : Continuous h :=
  h.toFun.continuous
end HomotopyEquiv
end ContinuousMap
open ContinuousMap
namespace Homeomorph
def toHomotopyEquiv (h : X ≃ₜ Y) : X ≃ₕ Y where
  toFun := h
  invFun := h.symm
  left_inv := by rw [symm_comp_toContinuousMap]
  right_inv := by rw [toContinuousMap_comp_symm]
@[simp]
theorem coe_toHomotopyEquiv (h : X ≃ₜ Y) : (h.toHomotopyEquiv : X → Y) = h :=
  rfl
end Homeomorph
namespace ContinuousMap
namespace HomotopyEquiv
def symm (h : X ≃ₕ Y) : Y ≃ₕ X where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv
@[simp]
theorem coe_invFun (h : HomotopyEquiv X Y) : (⇑h.invFun : Y → X) = ⇑h.symm :=
  rfl
def Simps.apply (h : X ≃ₕ Y) : X → Y :=
  h
def Simps.symm_apply (h : X ≃ₕ Y) : Y → X :=
  h.symm
initialize_simps_projections HomotopyEquiv (toFun_toFun → apply, invFun_toFun → symm_apply,
  -toFun, -invFun)
@[simps!]
def refl (X : Type u) [TopologicalSpace X] : X ≃ₕ X :=
  (Homeomorph.refl X).toHomotopyEquiv
instance : Inhabited (HomotopyEquiv Unit Unit) :=
  ⟨refl Unit⟩
@[simps!]
def trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z where
  toFun := h₂.toFun.comp h₁.toFun
  invFun := h₁.invFun.comp h₂.invFun
  left_inv := by
    refine Homotopic.trans ?_ h₁.left_inv
    exact ((Homotopic.refl _).hcomp h₂.left_inv).hcomp (Homotopic.refl _)
  right_inv := by
    refine Homotopic.trans ?_ h₂.right_inv
    exact ((Homotopic.refl _).hcomp h₁.right_inv).hcomp (Homotopic.refl _)
theorem symm_trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := rfl
def prodCongr (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z') : (X × Z) ≃ₕ (Y × Z') where
  toFun := h₁.toFun.prodMap h₂.toFun
  invFun := h₁.invFun.prodMap h₂.invFun
  left_inv := h₁.left_inv.prodMap h₂.left_inv
  right_inv := h₁.right_inv.prodMap h₂.right_inv
def piCongrRight {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (h : ∀ i, X i ≃ₕ Y i) :
    (∀ i, X i) ≃ₕ (∀ i, Y i) where
  toFun := .piMap fun i ↦ (h i).toFun
  invFun := .piMap fun i ↦ (h i).invFun
  left_inv := .piMap fun i ↦ (h i).left_inv
  right_inv := .piMap fun i ↦ (h i).right_inv
end HomotopyEquiv
end ContinuousMap
open ContinuousMap
namespace Homeomorph
@[simp]
theorem refl_toHomotopyEquiv (X : Type u) [TopologicalSpace X] :
    (Homeomorph.refl X).toHomotopyEquiv = HomotopyEquiv.refl X :=
  rfl
@[simp]
theorem symm_toHomotopyEquiv (h : X ≃ₜ Y) : h.symm.toHomotopyEquiv = h.toHomotopyEquiv.symm :=
  rfl
@[simp]
theorem trans_toHomotopyEquiv (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z) :
    (h₀.trans h₁).toHomotopyEquiv = h₀.toHomotopyEquiv.trans h₁.toHomotopyEquiv :=
  rfl
end Homeomorph