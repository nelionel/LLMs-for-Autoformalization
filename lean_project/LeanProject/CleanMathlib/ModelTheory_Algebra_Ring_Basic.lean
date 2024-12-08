import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Algebra.Ring.Equiv
variable {α : Type*}
namespace FirstOrder
open FirstOrder
inductive ringFunc : ℕ → Type
  | add : ringFunc 2
  | mul : ringFunc 2
  | neg : ringFunc 1
  | zero : ringFunc 0
  | one : ringFunc 0
  deriving DecidableEq
def Language.ring : Language :=
  { Functions := ringFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic
namespace Ring
open ringFunc Language
example (n : ℕ) : DecidableEq (Language.ring.Functions n) := inferInstance
example (n : ℕ) : DecidableEq (Language.ring.Relations n) := inferInstance
abbrev addFunc : Language.ring.Functions 2 := add
abbrev mulFunc : Language.ring.Functions 2 := mul
abbrev negFunc : Language.ring.Functions 1 := neg
abbrev zeroFunc : Language.ring.Functions 0 := zero
abbrev oneFunc : Language.ring.Functions 0 := one
instance (α : Type*) : Zero (Language.ring.Term α) :=
{ zero := Constants.term zeroFunc }
theorem zero_def (α : Type*) : (0 : Language.ring.Term α) = Constants.term zeroFunc := rfl
instance (α : Type*) : One (Language.ring.Term α) :=
{ one := Constants.term oneFunc }
theorem one_def (α : Type*) : (1 : Language.ring.Term α) = Constants.term oneFunc := rfl
instance (α : Type*) : Add (Language.ring.Term α) :=
{ add := addFunc.apply₂ }
theorem add_def (α : Type*) (t₁ t₂ : Language.ring.Term α) :
    t₁ + t₂ = addFunc.apply₂ t₁ t₂ := rfl
instance (α : Type*) : Mul (Language.ring.Term α) :=
{ mul := mulFunc.apply₂ }
theorem mul_def (α : Type*) (t₁ t₂ : Language.ring.Term α) :
    t₁ * t₂ = mulFunc.apply₂ t₁ t₂ := rfl
instance (α : Type*) : Neg (Language.ring.Term α) :=
{ neg := negFunc.apply₁ }
theorem neg_def (α : Type*) (t : Language.ring.Term α) :
    -t = negFunc.apply₁ t := rfl
instance : Fintype Language.ring.Symbols :=
  ⟨⟨Multiset.ofList
      [Sum.inl ⟨2, .add⟩,
       Sum.inl ⟨2, .mul⟩,
       Sum.inl ⟨1, .neg⟩,
       Sum.inl ⟨0, .zero⟩,
       Sum.inl ⟨0, .one⟩], by
    dsimp [Language.Symbols]; decide⟩, by
    intro x
    dsimp [Language.Symbols]
    rcases x with ⟨_, f⟩ | ⟨_, f⟩
    · cases f <;> decide
    · cases f ⟩
@[simp]
theorem card_ring : card Language.ring = 5 := by
  have : Fintype.card Language.ring.Symbols = 5 := rfl
  simp [Language.card, this]
open Language Structure
class CompatibleRing (R : Type*) [Add R] [Mul R] [Neg R] [One R] [Zero R]
    extends Language.ring.Structure R where
  funMap_add : ∀ x, funMap addFunc x = x 0 + x 1
  funMap_mul : ∀ x, funMap mulFunc x = x 0 * x 1
  funMap_neg : ∀ x, funMap negFunc x = -x 0
  funMap_zero : ∀ x, funMap (zeroFunc : Language.ring.Constants) x = 0
  funMap_one : ∀ x, funMap (oneFunc : Language.ring.Constants) x = 1
open CompatibleRing
attribute [simp] funMap_add funMap_mul funMap_neg funMap_zero funMap_one
section
variable {R : Type*} [Add R] [Mul R] [Neg R] [One R] [Zero R] [CompatibleRing R]
@[simp]
theorem realize_add (x y : ring.Term α) (v : α → R) :
    Term.realize v (x + y) = Term.realize v x + Term.realize v y := by
  simp [add_def, funMap_add]
@[simp]
theorem realize_mul (x y : ring.Term α) (v : α → R) :
    Term.realize v (x * y) = Term.realize v x * Term.realize v y := by
  simp [mul_def, funMap_mul]
@[simp]
theorem realize_neg (x : ring.Term α) (v : α → R) :
    Term.realize v (-x) = -Term.realize v x := by
  simp [neg_def, funMap_neg]
@[simp]
theorem realize_zero (v : α → R) : Term.realize v (0 : ring.Term α) = 0 := by
  simp [zero_def, funMap_zero, constantMap]
@[simp]
theorem realize_one (v : α → R) : Term.realize v (1 : ring.Term α) = 1 := by
  simp [one_def, funMap_one, constantMap]
end
def compatibleRingOfRing (R : Type*) [Add R] [Mul R] [Neg R] [One R] [Zero R] :
    CompatibleRing R :=
  { funMap := fun {n} f =>
      match n, f with
      | _, .add => fun x => x 0 + x 1
      | _, .mul => fun x => x 0 * x 1
      | _, .neg => fun x => -x 0
      | _, .zero => fun _ => 0
      | _, .one => fun _ => 1
    funMap_add := fun _ => rfl,
    funMap_mul := fun _ => rfl,
    funMap_neg := fun _ => rfl,
    funMap_zero := fun _ => rfl,
    funMap_one := fun _ => rfl }
def languageEquivEquivRingEquiv {R S : Type*}
    [NonAssocRing R] [NonAssocRing S]
    [CompatibleRing R] [CompatibleRing S] :
    (Language.ring.Equiv R S) ≃ (R ≃+* S) :=
  { toFun := fun f =>
    { f with
      map_add' := by
        intro x y
        simpa using f.map_fun addFunc ![x, y]
      map_mul' := by
        intro x y
        simpa using f.map_fun mulFunc ![x, y] }
    invFun := fun f =>
    { f with
      map_fun' := fun {n} f => by
        cases f <;> simp
      map_rel' := fun {n} f => by cases f },
    left_inv := fun f => by ext; rfl
    right_inv := fun f => by ext; rfl }
variable (R : Type*) [Language.ring.Structure R]
abbrev addOfRingStructure : Add R :=
  { add := fun x y => funMap addFunc ![x, y] }
abbrev mulOfRingStructure : Mul R :=
  { mul := fun x y => funMap mulFunc ![x, y] }
abbrev negOfRingStructure : Neg R :=
  { neg := fun x => funMap negFunc ![x] }
abbrev zeroOfRingStructure : Zero R :=
  { zero := funMap zeroFunc ![] }
abbrev oneOfRingStructure : One R :=
  { one := funMap oneFunc ![] }
attribute [local instance] addOfRingStructure mulOfRingStructure negOfRingStructure
  zeroOfRingStructure oneOfRingStructure
abbrev compatibleRingOfRingStructure : CompatibleRing R :=
  { funMap_add := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_mul := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_neg := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_zero := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      rfl
    funMap_one := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      rfl  }
end Ring
end FirstOrder