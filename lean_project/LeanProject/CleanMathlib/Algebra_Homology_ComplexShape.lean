import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Relation
noncomputable section
@[ext]
structure ComplexShape (ι : Type*) where
  Rel : ι → ι → Prop
  next_eq : ∀ {i j j'}, Rel i j → Rel i j' → j = j'
  prev_eq : ∀ {i i' j}, Rel i j → Rel i' j → i = i'
namespace ComplexShape
variable {ι : Type*}
@[simps]
def refl (ι : Type*) : ComplexShape ι where
  Rel i j := i = j
  next_eq w w' := w.symm.trans w'
  prev_eq w w' := w.trans w'.symm
@[simps]
def symm (c : ComplexShape ι) : ComplexShape ι where
  Rel i j := c.Rel j i
  next_eq w w' := c.prev_eq w w'
  prev_eq w w' := c.next_eq w w'
@[simp]
theorem symm_symm (c : ComplexShape ι) : c.symm.symm = c := rfl
theorem symm_bijective :
    Function.Bijective (ComplexShape.symm : ComplexShape ι → ComplexShape ι) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
@[simp]
def trans (c₁ c₂ : ComplexShape ι) : ComplexShape ι where
  Rel := Relation.Comp c₁.Rel c₂.Rel
  next_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₁.next_eq w₁ w₁'] at w₂
    exact c₂.next_eq w₂ w₂'
  prev_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₂.prev_eq w₂ w₂'] at w₁
    exact c₁.prev_eq w₁ w₁'
instance subsingleton_next (c : ComplexShape ι) (i : ι) : Subsingleton { j // c.Rel i j } := by
  constructor
  rintro ⟨j, rij⟩ ⟨k, rik⟩
  congr
  exact c.next_eq rij rik
instance subsingleton_prev (c : ComplexShape ι) (j : ι) : Subsingleton { i // c.Rel i j } := by
  constructor
  rintro ⟨i, rik⟩ ⟨j, rjk⟩
  congr
  exact c.prev_eq rik rjk
open Classical in
def next (c : ComplexShape ι) (i : ι) : ι :=
  if h : ∃ j, c.Rel i j then h.choose else i
open Classical in
def prev (c : ComplexShape ι) (j : ι) : ι :=
  if h : ∃ i, c.Rel i j then h.choose else j
theorem next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Rel i j) : c.next i = j := by
  apply c.next_eq _ h
  rw [next]
  rw [dif_pos]
  exact Exists.choose_spec ⟨j, h⟩
theorem prev_eq' (c : ComplexShape ι) {i j : ι} (h : c.Rel i j) : c.prev j = i := by
  apply c.prev_eq _ h
  rw [prev, dif_pos]
  exact Exists.choose_spec (⟨i, h⟩ : ∃ k, c.Rel k j)
lemma next_eq_self' (c : ComplexShape ι) (j : ι) (hj : ∀ k, ¬ c.Rel j k) :
    c.next j = j :=
  dif_neg (by simpa using hj)
lemma prev_eq_self' (c : ComplexShape ι) (j : ι) (hj : ∀ i, ¬ c.Rel i j) :
    c.prev j = j :=
  dif_neg (by simpa using hj)
lemma next_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬ c.Rel j (c.next j)) :
    c.next j = j :=
  c.next_eq_self' j (fun k hk' => hj (by simpa only [c.next_eq' hk'] using hk'))
lemma prev_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬ c.Rel (c.prev j) j) :
    c.prev j = j :=
  c.prev_eq_self' j (fun k hk' => hj (by simpa only [c.prev_eq' hk'] using hk'))
@[simps]
def up' {α : Type*} [AddRightCancelSemigroup α] (a : α) : ComplexShape α where
  Rel i j := i + a = j
  next_eq hi hj := hi.symm.trans hj
  prev_eq hi hj := add_right_cancel (hi.trans hj.symm)
@[simps]
def down' {α : Type*} [AddRightCancelSemigroup α] (a : α) : ComplexShape α where
  Rel i j := j + a = i
  next_eq hi hj := add_right_cancel (hi.trans hj.symm)
  prev_eq hi hj := hi.symm.trans hj
theorem down'_mk {α : Type*} [AddRightCancelSemigroup α] (a : α) (i j : α) (h : j + a = i) :
    (down' a).Rel i j := h
@[simps!]
def up (α : Type*) [AddRightCancelSemigroup α] [One α] : ComplexShape α :=
  up' 1
@[simps!]
def down (α : Type*) [AddRightCancelSemigroup α] [One α] : ComplexShape α :=
  down' 1
theorem down_mk {α : Type*} [AddRightCancelSemigroup α] [One α] (i j : α) (h : j + 1 = i) :
    (down α).Rel i j :=
  down'_mk (1 : α) i j h
end ComplexShape
end
namespace ComplexShape
variable (α : Type*) [AddRightCancelSemigroup α] [DecidableEq α]
instance (a : α) : DecidableRel (ComplexShape.up' a).Rel :=
  fun _ _ => by dsimp; infer_instance
instance (a : α) : DecidableRel (ComplexShape.down' a).Rel :=
  fun _ _ => by dsimp; infer_instance
variable [One α]
instance : DecidableRel (ComplexShape.up α).Rel := by
  dsimp [ComplexShape.up]; infer_instance
instance : DecidableRel (ComplexShape.down α).Rel := by
  dsimp [ComplexShape.down]; infer_instance
end ComplexShape