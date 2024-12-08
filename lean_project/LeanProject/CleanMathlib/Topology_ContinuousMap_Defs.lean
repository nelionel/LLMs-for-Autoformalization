import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Lift
import Mathlib.Topology.Defs.Basic
open Function
open scoped Topology
structure ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  protected toFun : X → Y
  protected continuous_toFun : Continuous toFun := by continuity
notation "C(" X ", " Y ")" => ContinuousMap X Y
section
class ContinuousMapClass (F : Type*) (X Y : outParam Type*)
    [TopologicalSpace X] [TopologicalSpace Y] [FunLike F X Y] : Prop where
  map_continuous (f : F) : Continuous f
end
export ContinuousMapClass (map_continuous)
attribute [continuity, fun_prop] map_continuous
section ContinuousMapClass
variable {F X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [FunLike F X Y]
variable [ContinuousMapClass F X Y]
@[coe] def toContinuousMap (f : F) : C(X, Y) := ⟨f, map_continuous f⟩
instance : CoeTC F C(X, Y) := ⟨toContinuousMap⟩
end ContinuousMapClass
namespace ContinuousMap
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
instance instFunLike : FunLike C(X, Y) X Y where
  coe := ContinuousMap.toFun
  coe_injective' f g h := by cases f; cases g; congr
instance instContinuousMapClass : ContinuousMapClass C(X, Y) X Y where
  map_continuous := ContinuousMap.continuous_toFun
@[simp]
theorem toFun_eq_coe {f : C(X, Y)} : f.toFun = (f : X → Y) :=
  rfl
instance : CanLift (X → Y) C(X, Y) DFunLike.coe Continuous := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩
def Simps.apply (f : C(X, Y)) : X → Y := f
initialize_simps_projections ContinuousMap (toFun → apply)
@[simp] 
protected theorem coe_coe {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F) :
    ⇑(f : C(X, Y)) = f :=
  rfl
protected theorem coe_apply {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y] (f : F) (x : X) :
    (f : C(X, Y)) x = f x :=
  rfl
@[ext]
theorem ext {f g : C(X, Y)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h
protected def copy (f : C(X, Y)) (f' : X → Y) (h : f' = f) : C(X, Y) where
  toFun := f'
  continuous_toFun := h.symm ▸ f.continuous_toFun
@[simp]
theorem coe_copy (f : C(X, Y)) (f' : X → Y) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
theorem copy_eq (f : C(X, Y)) (f' : X → Y) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
protected theorem continuous (f : C(X, Y)) : Continuous f :=
  f.continuous_toFun
@[deprecated map_continuous (since := "2024-09-29")]
theorem continuous_set_coe (s : Set C(X, Y)) (f : s) : Continuous (f : X → Y) :=
  map_continuous _
protected theorem congr_fun {f g : C(X, Y)} (H : f = g) (x : X) : f x = g x :=
  H ▸ rfl
protected theorem congr_arg (f : C(X, Y)) {x y : X} (h : x = y) : f x = f y :=
  h ▸ rfl
theorem coe_injective : Function.Injective (DFunLike.coe : C(X, Y) → (X → Y)) :=
  DFunLike.coe_injective
@[simp]
theorem coe_mk (f : X → Y) (h : Continuous f) : ⇑(⟨f, h⟩ : C(X, Y)) = f :=
  rfl
end ContinuousMap