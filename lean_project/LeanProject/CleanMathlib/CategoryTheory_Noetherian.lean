import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Simple
namespace CategoryTheory
open CategoryTheory.Limits
variable {C : Type*} [Category C]
class NoetherianObject (X : C) : Prop where
  subobject_gt_wellFounded' : WellFounded ((· > ·) : Subobject X → Subobject X → Prop)
lemma NoetherianObject.subobject_gt_wellFounded (X : C) [NoetherianObject X] :
    WellFounded ((· > ·) : Subobject X → Subobject X → Prop) :=
  NoetherianObject.subobject_gt_wellFounded'
class ArtinianObject (X : C) : Prop where
  subobject_lt_wellFounded' : WellFounded ((· < ·) : Subobject X → Subobject X → Prop)
lemma ArtinianObject.subobject_lt_wellFounded (X : C) [ArtinianObject X] :
    WellFounded ((· < ·) : Subobject X → Subobject X → Prop) :=
  ArtinianObject.subobject_lt_wellFounded'
variable (C)
class Noetherian extends EssentiallySmall C : Prop where
  noetherianObject : ∀ X : C, NoetherianObject X
attribute [instance] Noetherian.noetherianObject
class Artinian extends EssentiallySmall C : Prop where
  artinianObject : ∀ X : C, ArtinianObject X
attribute [instance] Artinian.artinianObject
variable {C}
open Subobject
variable [HasZeroMorphisms C] [HasZeroObject C]
theorem exists_simple_subobject {X : C} [ArtinianObject X] (h : ¬IsZero X) :
    ∃ Y : Subobject X, Simple (Y : C) := by
  haveI : Nontrivial (Subobject X) := nontrivial_of_not_isZero h
  haveI := isAtomic_of_orderBot_wellFounded_lt (ArtinianObject.subobject_lt_wellFounded X)
  obtain ⟨Y, s⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Subobject X)).resolve_left top_ne_bot
  exact ⟨Y, (subobject_simple_iff_isAtom _).mpr s.1⟩
noncomputable def simpleSubobject {X : C} [ArtinianObject X] (h : ¬IsZero X) : C :=
  (exists_simple_subobject h).choose
noncomputable def simpleSubobjectArrow {X : C} [ArtinianObject X] (h : ¬IsZero X) :
    simpleSubobject h ⟶ X :=
  (exists_simple_subobject h).choose.arrow
instance mono_simpleSubobjectArrow {X : C} [ArtinianObject X] (h : ¬IsZero X) :
    Mono (simpleSubobjectArrow h) := by
  dsimp only [simpleSubobjectArrow]
  infer_instance
instance {X : C} [ArtinianObject X] (h : ¬IsZero X) : Simple (simpleSubobject h) :=
  (exists_simple_subobject h).choose_spec
end CategoryTheory