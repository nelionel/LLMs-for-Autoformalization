import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Defs
import Mathlib.Control.Basic
import Mathlib.Data.Set.Notation
universe u
open Function Set.Notation
namespace Set
variable {α β : Type u} {s : Set α} {f : α → Set β}
protected def monad : Monad.{u} Set where
  pure a := {a}
  bind s f := ⋃ i ∈ s, f i
  seq s t := Set.seq s (t ())
  map := Set.image
section with_instance
attribute [local instance] Set.monad
@[simp]
theorem bind_def : s >>= f = ⋃ i ∈ s, f i :=
  rfl
@[simp]
theorem fmap_eq_image (f : α → β) : f <$> s = f '' s :=
  rfl
@[simp]
theorem seq_eq_set_seq (s : Set (α → β)) (t : Set α) : s <*> t = s.seq t :=
  rfl
@[simp]
theorem pure_def (a : α) : (pure a : Set α) = {a} :=
  rfl
theorem image2_def {α β γ : Type u} (f : α → β → γ) (s : Set α) (t : Set β) :
    image2 f s t = f <$> s <*> t := by
  ext
  simp
instance : LawfulMonad Set := LawfulMonad.mk'
  (id_map := image_id)
  (pure_bind := biUnion_singleton)
  (bind_assoc := fun _ _ _ => by simp only [bind_def, biUnion_iUnion])
  (bind_pure_comp := fun _ _ => (image_eq_iUnion _ _).symm)
  (bind_map := fun _ _ => seq_def.symm)
instance : CommApplicative (Set : Type u → Type u) :=
  ⟨fun s t => prod_image_seq_comm s t⟩
instance : Alternative Set :=
  { Set.monad with
    orElse := fun s t => s ∪ (t ())
    failure := ∅ }
variable {β : Set α} {γ : Set β}
theorem mem_coe_of_mem {a : α} (ha : a ∈ β) (ha' : ⟨a, ha⟩ ∈ γ) : a ∈ (γ : Set α) :=
  ⟨_, ⟨⟨_, rfl⟩, _, ⟨ha', rfl⟩, rfl⟩⟩
theorem coe_subset : (γ : Set α) ⊆ β := by
  intro _ ⟨_, ⟨⟨⟨_, ha⟩, rfl⟩, _, ⟨_, rfl⟩, _⟩⟩; convert ha
theorem mem_of_mem_coe {a : α} (ha : a ∈ (γ : Set α)) : ⟨a, coe_subset ha⟩ ∈ γ := by
  rcases ha with ⟨_, ⟨_, rfl⟩, _, ⟨ha, rfl⟩, _⟩; convert ha
theorem eq_univ_of_coe_eq (hγ : (γ : Set α) = β) : γ = univ :=
  eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_coe <| hγ.symm ▸ ha
theorem image_coe_eq_restrict_image {δ : Type*} {f : α → δ} : f '' γ = β.restrict f '' γ :=
  ext fun _ =>
    ⟨fun ⟨_, h, ha⟩ => ⟨_, mem_of_mem_coe h, ha⟩, fun ⟨_, h, ha⟩ => ⟨_, mem_coe_of_mem _ h, ha⟩⟩
end with_instance
theorem coe_eq_image_val (t : Set s) :
    @Lean.Internal.coeM Set s α _ Set.monad t = (t : Set α) := by
  change ⋃ (x ∈ t), {x.1} = _
  ext
  simp
variable {β : Set α} {γ : Set β} {a : α}
theorem mem_image_val_of_mem (ha : a ∈ β) (ha' : ⟨a, ha⟩ ∈ γ) : a ∈ (γ : Set α) :=
  ⟨_, ha', rfl⟩
theorem image_val_subset : (γ : Set α) ⊆ β := by
  rintro _ ⟨⟨_, ha⟩, _, rfl⟩; exact ha
theorem mem_of_mem_image_val (ha : a ∈ (γ : Set α)) : ⟨a, image_val_subset ha⟩ ∈ γ := by
  rcases ha with ⟨_, ha, rfl⟩; exact ha
theorem eq_univ_of_image_val_eq (hγ : (γ : Set α) = β) : γ = univ :=
  eq_univ_of_forall fun ⟨_, ha⟩ => mem_of_mem_image_val <| hγ.symm ▸ ha
theorem image_image_val_eq_restrict_image {δ : Type*} {f : α → δ} : f '' γ = β.restrict f '' γ := by
  ext; simp
end Set
def SetM (α : Type u) := Set α
instance : Monad SetM := Set.monad
protected def SetM.run {α : Type*} (s : SetM α) : Set α := s