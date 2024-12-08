import Mathlib.Order.SetNotation
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FunProp
universe u v
open Set
@[to_additive existing TopologicalSpace]
class TopologicalSpace (X : Type u) where
  protected IsOpen : Set X → Prop
  protected isOpen_univ : IsOpen univ
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
variable {X : Type u} {Y : Type v}
section Defs
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}
def IsOpen : Set X → Prop := TopologicalSpace.IsOpen
@[simp] theorem isOpen_univ : IsOpen (univ : Set X) := TopologicalSpace.isOpen_univ
theorem IsOpen.inter (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  TopologicalSpace.isOpen_inter s t hs ht
theorem isOpen_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpace.isOpen_sUnion s h
class IsClosed (s : Set X) : Prop where
  isOpen_compl : IsOpen sᶜ
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s
def IsLocallyClosed (s : Set X) : Prop := ∃ (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
def frontier (s : Set X) : Set X :=
  closure s \ interior s
def coborder (s : Set X) : Set X :=
  (closure s \ s)ᶜ
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
def DenseRange {α : Type*} (f : α → X) := Dense (range f)
@[fun_prop]
structure Continuous (f : X → Y) : Prop where
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)
def IsClosedMap (f : X → Y) : Prop := ∀ U : Set X, IsClosed U → IsClosed (f '' U)
@[mk_iff]
structure IsOpenQuotientMap (f : X → Y) : Prop where
  surjective : Function.Surjective f
  continuous : Continuous f
  isOpenMap : IsOpenMap f
end Defs
scoped[Topology] notation (name := IsOpen_of) "IsOpen[" t "]" => @IsOpen _ t
scoped[Topology] notation (name := IsClosed_of) "IsClosed[" t "]" => @IsClosed _ t
scoped[Topology] notation (name := closure_of) "closure[" t "]" => @closure _ t
scoped[Topology] notation (name := Continuous_of) "Continuous[" t₁ ", " t₂ "]" =>
  @Continuous _ _ t₁ t₂
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)