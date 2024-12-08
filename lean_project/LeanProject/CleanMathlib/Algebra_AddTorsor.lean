import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
class AddTorsor (G : outParam Type*) (P : Type*) [AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  vsub_vadd' : ∀ p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
attribute [instance 100] AddTorsor.nonempty
instance addGroupIsAddTorsor (G : Type*) [AddGroup G] : AddTorsor G G where
  vsub := Sub.sub
  vsub_vadd' := sub_add_cancel
  vadd_vsub' := add_sub_cancel_right
@[simp]
theorem vsub_eq_sub {G : Type*} [AddGroup G] (g₁ g₂ : G) : g₁ -ᵥ g₂ = g₁ - g₂ :=
  rfl
section General
variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]
@[simp]
theorem vsub_vadd (p₁ p₂ : P) : (p₁ -ᵥ p₂) +ᵥ p₂ = p₁ :=
  AddTorsor.vsub_vadd' p₁ p₂
@[simp]
theorem vadd_vsub (g : G) (p : P) : (g +ᵥ p) -ᵥ p = g :=
  AddTorsor.vadd_vsub' g p
theorem vadd_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ +ᵥ p = g₂ +ᵥ p) : g₁ = g₂ := by
  rw [← vadd_vsub g₁ p, h, vadd_vsub]
@[simp]
theorem vadd_right_cancel_iff {g₁ g₂ : G} (p : P) : g₁ +ᵥ p = g₂ +ᵥ p ↔ g₁ = g₂ :=
  ⟨vadd_right_cancel p, fun h => h ▸ rfl⟩
theorem vadd_right_injective (p : P) : Function.Injective ((· +ᵥ p) : G → P) := fun _ _ =>
  vadd_right_cancel p
theorem vadd_vsub_assoc (g : G) (p₁ p₂ : P) : (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂) := by
  apply vadd_right_cancel p₂
  rw [vsub_vadd, add_vadd, vsub_vadd]
@[simp]
theorem vsub_self (p : P) : p -ᵥ p = (0 : G) := by
  rw [← zero_add (p -ᵥ p), ← vadd_vsub_assoc, vadd_vsub]
theorem eq_of_vsub_eq_zero {p₁ p₂ : P} (h : p₁ -ᵥ p₂ = (0 : G)) : p₁ = p₂ := by
  rw [← vsub_vadd p₁ p₂, h, zero_vadd]
@[simp]
theorem vsub_eq_zero_iff_eq {p₁ p₂ : P} : p₁ -ᵥ p₂ = (0 : G) ↔ p₁ = p₂ :=
  Iff.intro eq_of_vsub_eq_zero fun h => h ▸ vsub_self _
theorem vsub_ne_zero {p q : P} : p -ᵥ q ≠ (0 : G) ↔ p ≠ q :=
  not_congr vsub_eq_zero_iff_eq
@[simp]
theorem vsub_add_vsub_cancel (p₁ p₂ p₃ : P) : p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃ := by
  apply vadd_right_cancel p₃
  rw [add_vadd, vsub_vadd, vsub_vadd, vsub_vadd]
@[simp]
theorem neg_vsub_eq_vsub_rev (p₁ p₂ : P) : -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁ := by
  refine neg_eq_of_add_eq_zero_right (vadd_right_cancel p₁ ?_)
  rw [vsub_add_vsub_cancel, vsub_self]
theorem vadd_vsub_eq_sub_vsub (g : G) (p q : P) : (g +ᵥ p) -ᵥ q = g - (q -ᵥ p) := by
  rw [vadd_vsub_assoc, sub_eq_add_neg, neg_vsub_eq_vsub_rev]
theorem vsub_vadd_eq_vsub_sub (p₁ p₂ : P) (g : G) : p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g := by
  rw [← add_right_inj (p₂ -ᵥ p₁ : G), vsub_add_vsub_cancel, ← neg_vsub_eq_vsub_rev, vadd_vsub, ←
    add_sub_assoc, ← neg_vsub_eq_vsub_rev, neg_add_cancel, zero_sub]
@[simp]
theorem vsub_sub_vsub_cancel_right (p₁ p₂ p₃ : P) : p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂ := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd]
theorem eq_vadd_iff_vsub_eq (p₁ : P) (g : G) (p₂ : P) : p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g :=
  ⟨fun h => h.symm ▸ vadd_vsub _ _, fun h => h ▸ (vsub_vadd _ _).symm⟩
theorem vadd_eq_vadd_iff_neg_add_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ -v₁ + v₂ = p₁ -ᵥ p₂ := by
  rw [eq_vadd_iff_vsub_eq, vadd_vsub_assoc, ← add_right_inj (-v₁), neg_add_cancel_left, eq_comm]
namespace Set
open Pointwise
theorem singleton_vsub_self (p : P) : ({p} : Set P) -ᵥ {p} = {(0 : G)} := by
  rw [Set.singleton_vsub_singleton, vsub_self]
end Set
@[simp]
theorem vadd_vsub_vadd_cancel_right (v₁ v₂ : G) (p : P) : (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ - v₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, vsub_self, add_zero]
theorem vsub_left_cancel {p₁ p₂ p : P} (h : p₁ -ᵥ p = p₂ -ᵥ p) : p₁ = p₂ := by
  rwa [← sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h
@[simp]
theorem vsub_left_cancel_iff {p₁ p₂ p : P} : p₁ -ᵥ p = p₂ -ᵥ p ↔ p₁ = p₂ :=
  ⟨vsub_left_cancel, fun h => h ▸ rfl⟩
theorem vsub_left_injective (p : P) : Function.Injective ((· -ᵥ p) : P → G) := fun _ _ =>
  vsub_left_cancel
theorem vsub_right_cancel {p₁ p₂ p : P} (h : p -ᵥ p₁ = p -ᵥ p₂) : p₁ = p₂ := by
  refine vadd_left_cancel (p -ᵥ p₂) ?_
  rw [vsub_vadd, ← h, vsub_vadd]
@[simp]
theorem vsub_right_cancel_iff {p₁ p₂ p : P} : p -ᵥ p₁ = p -ᵥ p₂ ↔ p₁ = p₂ :=
  ⟨vsub_right_cancel, fun h => h ▸ rfl⟩
theorem vsub_right_injective (p : P) : Function.Injective ((p -ᵥ ·) : P → G) := fun _ _ =>
  vsub_right_cancel
end General
section comm
variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]
@[simp]
theorem vsub_sub_vsub_cancel_left (p₁ p₂ p₃ : P) : p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁ -ᵥ p₂ := by
  rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm, vsub_add_vsub_cancel]
@[simp]
theorem vadd_vsub_vadd_cancel_left (v : G) (p₁ p₂ : P) : (v +ᵥ p₁) -ᵥ (v +ᵥ p₂) = p₁ -ᵥ p₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_cancel_left]
theorem vsub_vadd_comm (p₁ p₂ p₃ : P) : (p₁ -ᵥ p₂ : G) +ᵥ p₃ = (p₃ -ᵥ p₂) +ᵥ p₁ := by
  rw [← @vsub_eq_zero_iff_eq G, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub]
  simp
theorem vadd_eq_vadd_iff_sub_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂ := by
  rw [vadd_eq_vadd_iff_neg_add_eq_vsub, neg_add_eq_sub]
theorem vsub_sub_vsub_comm (p₁ p₂ p₃ p₄ : P) : p₁ -ᵥ p₂ - (p₃ -ᵥ p₄) = p₁ -ᵥ p₃ - (p₂ -ᵥ p₄) := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub]
end comm
namespace Prod
variable {G G' P P' : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']
instance instAddTorsor : AddTorsor (G × G') (P × P') where
  vadd v p := (v.1 +ᵥ p.1, v.2 +ᵥ p.2)
  zero_vadd _ := Prod.ext (zero_vadd _ _) (zero_vadd _ _)
  add_vadd _ _ _ := Prod.ext (add_vadd _ _ _) (add_vadd _ _ _)
  vsub p₁ p₂ := (p₁.1 -ᵥ p₂.1, p₁.2 -ᵥ p₂.2)
  vsub_vadd' _ _ := Prod.ext (vsub_vadd _ _) (vsub_vadd _ _)
  vadd_vsub' _ _ := Prod.ext (vadd_vsub _ _) (vadd_vsub _ _)
@[simp]
theorem fst_vadd (v : G × G') (p : P × P') : (v +ᵥ p).1 = v.1 +ᵥ p.1 :=
  rfl
@[simp]
theorem snd_vadd (v : G × G') (p : P × P') : (v +ᵥ p).2 = v.2 +ᵥ p.2 :=
  rfl
@[simp]
theorem mk_vadd_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') +ᵥ (p, p') = (v +ᵥ p, v' +ᵥ p') :=
  rfl
@[simp]
theorem fst_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').1 = p₁.1 -ᵥ p₂.1 :=
  rfl
@[simp]
theorem snd_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').2 = p₁.2 -ᵥ p₂.2 :=
  rfl
@[simp]
theorem mk_vsub_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') -ᵥ (p₂, p₂') : G × G') = (p₁ -ᵥ p₂, p₁' -ᵥ p₂') :=
  rfl
end Prod
namespace Pi
universe u v w
variable {I : Type u} {fg : I → Type v} [∀ i, AddGroup (fg i)] {fp : I → Type w}
open AddAction AddTorsor
instance instAddTorsor [∀ i, AddTorsor (fg i) (fp i)] : AddTorsor (∀ i, fg i) (∀ i, fp i) where
  vadd g p i := g i +ᵥ p i
  zero_vadd p := funext fun i => zero_vadd (fg i) (p i)
  add_vadd g₁ g₂ p := funext fun i => add_vadd (g₁ i) (g₂ i) (p i)
  vsub p₁ p₂ i := p₁ i -ᵥ p₂ i
  vsub_vadd' p₁ p₂ := funext fun i => vsub_vadd (p₁ i) (p₂ i)
  vadd_vsub' g p := funext fun i => vadd_vsub (g i) (p i)
end Pi
namespace Equiv
variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]
def vaddConst (p : P) : G ≃ P where
  toFun v := v +ᵥ p
  invFun p' := p' -ᵥ p
  left_inv _ := vadd_vsub _ _
  right_inv _ := vsub_vadd _ _
@[simp]
theorem coe_vaddConst (p : P) : ⇑(vaddConst p) = fun v => v +ᵥ p :=
  rfl
@[simp]
theorem coe_vaddConst_symm (p : P) : ⇑(vaddConst p).symm = fun p' => p' -ᵥ p :=
  rfl
def constVSub (p : P) : P ≃ G where
  toFun := (p -ᵥ ·)
  invFun := (-· +ᵥ p)
  left_inv p' := by simp
  right_inv v := by simp [vsub_vadd_eq_vsub_sub]
@[simp] lemma coe_constVSub (p : P) : ⇑(constVSub p) = (p -ᵥ ·) := rfl
@[simp]
theorem coe_constVSub_symm (p : P) : ⇑(constVSub p).symm = fun (v : G) => -v +ᵥ p :=
  rfl
variable (P)
def constVAdd (v : G) : Equiv.Perm P where
  toFun := (v +ᵥ ·)
  invFun := (-v +ᵥ ·)
  left_inv p := by simp [vadd_vadd]
  right_inv p := by simp [vadd_vadd]
@[simp] lemma coe_constVAdd (v : G) : ⇑(constVAdd P v) = (v +ᵥ ·) := rfl
variable (G)
@[simp]
theorem constVAdd_zero : constVAdd P (0 : G) = 1 :=
  ext <| zero_vadd G
variable {G}
@[simp]
theorem constVAdd_add (v₁ v₂ : G) : constVAdd P (v₁ + v₂) = constVAdd P v₁ * constVAdd P v₂ :=
  ext <| add_vadd v₁ v₂
def constVAddHom : Multiplicative G →* Equiv.Perm P where
  toFun v := constVAdd P (v.toAdd)
  map_one' := constVAdd_zero G P
  map_mul' := constVAdd_add P
variable {P}
open Function
def pointReflection (x : P) : Perm P :=
  (constVSub x).trans (vaddConst x)
theorem pointReflection_apply (x y : P) : pointReflection x y = (x -ᵥ y) +ᵥ x :=
  rfl
@[simp]
theorem pointReflection_vsub_left (x y : P) : pointReflection x y -ᵥ x = x -ᵥ y :=
  vadd_vsub ..
@[simp]
theorem left_vsub_pointReflection (x y : P) : x -ᵥ pointReflection x y = y -ᵥ x :=
  neg_injective <| by simp
@[simp]
theorem pointReflection_vsub_right (x y : P) : pointReflection x y -ᵥ y = 2 • (x -ᵥ y) := by
  simp [pointReflection, two_nsmul, vadd_vsub_assoc]
@[simp]
theorem right_vsub_pointReflection (x y : P) : y -ᵥ pointReflection x y = 2 • (y -ᵥ x) :=
  neg_injective <| by simp [← neg_nsmul]
@[simp]
theorem pointReflection_symm (x : P) : (pointReflection x).symm = pointReflection x :=
  ext <| by simp [pointReflection]
@[simp]
theorem pointReflection_self (x : P) : pointReflection x x = x :=
  vsub_vadd _ _
theorem pointReflection_involutive (x : P) : Involutive (pointReflection x : P → P) := fun y =>
  (Equiv.apply_eq_iff_eq_symm_apply _).2 <| by rw [pointReflection_symm]
theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P} (h : Injective (2 • · : G → G)) :
    pointReflection x y = y ↔ y = x := by
  rw [pointReflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
    neg_eq_iff_add_eq_zero, ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]
@[deprecated (since := "2024-11-18")] alias pointReflection_fixed_iff_of_injective_bit0 :=
pointReflection_fixed_iff_of_injective_two_nsmul
theorem injective_pointReflection_left_of_injective_two_nsmul {G P : Type*} [AddCommGroup G]
    [AddTorsor G P] (h : Injective (2 • · : G → G)) (y : P) :
    Injective fun x : P => pointReflection x y :=
  fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero,
    ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq] at hy
@[deprecated (since := "2024-11-18")] alias injective_pointReflection_left_of_injective_bit0 :=
injective_pointReflection_left_of_injective_two_nsmul
end Equiv
theorem AddTorsor.subsingleton_iff (G P : Type*) [AddGroup G] [AddTorsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.vaddConst default).subsingleton_congr