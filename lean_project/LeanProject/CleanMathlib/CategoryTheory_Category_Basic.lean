import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Tactic.PPWithUniv
import Mathlib.Tactic.Common
import Mathlib.Tactic.StacksAttribute
library_note "CategoryTheory universes"
universe v u
namespace CategoryTheory
@[pp_with_univ]
class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
initialize_simps_projections CategoryStruct (-toQuiver_Hom)
scoped notation "𝟙" => CategoryStruct.id  
scoped infixr:80 " ≫ " => CategoryStruct.comp 
syntax (name := sorryIfSorry) "sorry_if_sorry" : tactic
open Lean Meta Elab.Tactic in
@[tactic sorryIfSorry, inherit_doc sorryIfSorry] def evalSorryIfSorry : Tactic := fun _ => do
  let goalType ← getMainTarget
  if goalType.hasSorry then
    closeMainGoal `sorry_if_sorry (← mkSorry goalType true)
  else
    throwError "The goal does not contain `sorry`"
macro (name := aesop_cat) "aesop_cat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry |
  aesop $c* (config := { introsTransparency? := some .default, terminal := true })
            (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))
macro (name := aesop_cat?) "aesop_cat?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry |
  aesop? $c* (config := { introsTransparency? := some .default, terminal := true })
             (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))
macro (name := aesop_cat_nonterminal) "aesop_cat_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c* (config := { introsTransparency? := some .default, warnOnNonterminal := false })
              (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))
attribute [aesop safe (rule_sets := [CategoryTheory])] Subsingleton.elim
@[pp_with_univ]
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat
attribute [simp] Category.id_comp Category.comp_id Category.assoc
attribute [trans] CategoryStruct.comp
example {C} [Category C] {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp
example {C} [Category C] {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp
abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) := Category.{u} C
abbrev SmallCategory (C : Type u) : Type (u + 1) := Category.{u} C
section
variable {C : Type u} [Category.{v} C] {X Y Z : C}
initialize_simps_projections Category (-Hom)
theorem eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h := by rw [w]
theorem whisker_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h := by rw [w]
scoped infixr:80 " =≫ " => eq_whisker
scoped infixr:80 " ≫= " => whisker_eq
theorem eq_of_comp_left_eq {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    f = g := by
  convert w (𝟙 Y) <;> simp
theorem eq_of_comp_right_eq {f g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) :
    f = g := by
  convert w (𝟙 Y) <;> simp
theorem eq_of_comp_left_eq' (f g : X ⟶ Y)
    (w : (fun {Z} (h : Y ⟶ Z) => f ≫ h) = fun {Z} (h : Y ⟶ Z) => g ≫ h) : f = g :=
  eq_of_comp_left_eq @fun Z h => by convert congr_fun (congr_fun w Z) h
theorem eq_of_comp_right_eq' (f g : Y ⟶ Z)
    (w : (fun {X} (h : X ⟶ Y) => h ≫ f) = fun {X} (h : X ⟶ Y) => h ≫ g) : f = g :=
  eq_of_comp_right_eq @fun X h => by convert congr_fun (congr_fun w X) h
theorem id_of_comp_left_id (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  simp
theorem id_of_comp_right_id (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  simp
theorem comp_ite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' := by aesop
theorem ite_comp {P : Prop} [Decidable P] {X Y Z : C} (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (if P then f else f') ≫ g = if P then f ≫ g else f' ≫ g := by aesop
theorem comp_dite {P : Prop} [Decidable P]
    {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
    (f ≫ if h : P then g h else g' h) = if h : P then f ≫ g h else f ≫ g' h := by aesop
theorem dite_comp {P : Prop} [Decidable P]
    {X Y Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) :
    (if h : P then f h else f' h) ≫ g = if h : P then f h ≫ g else f' h ≫ g := by aesop
class Epi (f : X ⟶ Y) : Prop where
  left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h
class Mono (f : X ⟶ Y) : Prop where
  right_cancellation : ∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h
instance (X : C) : Epi (𝟙 X) :=
  ⟨fun g h w => by aesop⟩
instance (X : C) : Mono (𝟙 X) :=
  ⟨fun g h w => by aesop⟩
theorem cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} : f ≫ g = f ≫ h ↔ g = h :=
  ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩
theorem cancel_epi_assoc_iff (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} {W : C} {k l : Z ⟶ W} :
    (f ≫ g) ≫ k = (f ≫ h) ≫ l ↔ g ≫ k = h ≫ l :=
  ⟨fun p => (cancel_epi f).1 <| by simpa using p, fun p => by simp only [Category.assoc, p]⟩
theorem cancel_mono (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X} : g ≫ f = h ≫ f ↔ g = h :=
  ⟨fun p => Mono.right_cancellation g h p, congr_arg (fun k => k ≫ f)⟩
theorem cancel_mono_assoc_iff (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X} {W : C} {k l : W ⟶ Z} :
    k ≫ (g ≫ f) = l ≫ (h ≫ f) ↔ k ≫ g = l ≫ h :=
  ⟨fun p => (cancel_mono f).1 <| by simpa using p, fun p => by simp only [← Category.assoc, p]⟩
theorem cancel_epi_id (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y} : f ≫ h = f ↔ h = 𝟙 Y := by
  convert cancel_epi f
  simp
theorem cancel_mono_id (f : X ⟶ Y) [Mono f] {g : X ⟶ X} : g ≫ f = f ↔ g = 𝟙 X := by
  convert cancel_mono f
  simp
instance epi_comp {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g] : Epi (f ≫ g) :=
  ⟨fun _ _ w => (cancel_epi g).1 <| (cancel_epi_assoc_iff f).1 w⟩
instance mono_comp {X Y Z : C} (f : X ⟶ Y) [Mono f] (g : Y ⟶ Z) [Mono g] : Mono (f ≫ g) :=
  ⟨fun _ _ w => (cancel_mono f).1 <| (cancel_mono_assoc_iff g).1 w⟩
theorem mono_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono (f ≫ g)] : Mono f :=
  ⟨fun _ _ w => (cancel_mono (f ≫ g)).1 <| by simp only [← Category.assoc, w]⟩
theorem mono_of_mono_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Mono h]
    (w : f ≫ g = h) : Mono f := by
  subst h; exact mono_of_mono f g
theorem epi_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g :=
  ⟨fun _ _ w => (cancel_epi (f ≫ g)).1 <| by simp only [Category.assoc, w]⟩
theorem epi_of_epi_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h]
    (w : f ≫ g = h) : Epi g := by
  subst h; exact epi_of_epi f g
section
variable [Quiver.IsThin C] (f : X ⟶ Y)
instance : Mono f where
  right_cancellation _ _ _ := Subsingleton.elim _ _
instance : Epi f where
  left_cancellation _ _ _ := Subsingleton.elim _ _
end
end
section
variable (C : Type u)
variable [Category.{v} C]
universe u'
instance uliftCategory : Category.{v} (ULift.{u'} C) where
  Hom X Y := X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp f g := f ≫ g
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := by infer_instance
end
end CategoryTheory
library_note "dsimp, simp"