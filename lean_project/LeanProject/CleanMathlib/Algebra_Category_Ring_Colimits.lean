import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
universe u v
open CategoryTheory Limits
namespace RingCat.Colimits
variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})
inductive Prequotient
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient
  | mul : Prequotient → Prequotient → Prequotient
instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩
open Prequotient
inductive Relation : Prequotient F → Prequotient F → Prop 
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | one : ∀ j, Relation (Prequotient.of j 1) one
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : ∀ (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
  | neg_add_cancel : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : ∀ x, Relation (mul zero x) zero
  | mul_zero : ∀ x, Relation (mul x zero) zero
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩
attribute [instance] colimitSetoid
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
instance ColimitType.instZero : Zero (ColimitType F) where zero := Quotient.mk _ zero
instance ColimitType.instAdd : Add (ColimitType F) where
  add := Quotient.map₂ add <| fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)
instance ColimitType.instNeg : Neg (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  neg_add_cancel := Quotient.ind <| fun _ => Quotient.sound <| Relation.neg_add_cancel _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
instance InhabitedColimitType : Inhabited <| ColimitType F where
  default := 0
instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }
instance : Ring (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
    one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.one_mul _
    mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_one _
    add_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.add_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
    mul_zero := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_zero _
    zero_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.zero_mul _
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }
@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl
@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl
@[simp]
theorem quot_neg (x : Prequotient F) :
    (by exact Quot.mk Setoid.r (neg x) : ColimitType F) = -(by exact Quot.mk Setoid.r x) :=
  rfl
@[simp]
theorem quot_add (x y) :
    (by exact Quot.mk Setoid.r (add x y) : ColimitType F) =
      (by exact Quot.mk _ x) + (by exact Quot.mk _ y) :=
  rfl
@[simp]
theorem quot_mul (x y) :
    (by exact Quot.mk Setoid.r (mul x y) : ColimitType F) =
      (by exact Quot.mk _ x) * (by exact Quot.mk _ y) :=
  rfl
def colimit : RingCat :=
  RingCat.of (ColimitType F)
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := coconeFun F j
  map_one' := by apply Quot.sound; apply Relation.one
  map_mul' := by intros; apply Quot.sound; apply Relation.mul
  map_zero' := by apply Quot.sound; apply Relation.zero
  map_add' := by intros; apply Quot.sound; apply Relation.add
@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map
@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f, comp_apply]
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
  | mul x y => descFunLift s x * descFunLift s y
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (s.ι.naturality f) x
    | zero j => simp
    | one j => simp
    | neg j x => simp
    | add j x y => simp
    | mul j x y => simp
    | neg_1 x x' r ih => dsimp; rw [ih]
    | add_1 x x' y r ih => dsimp; rw [ih]
    | add_2 x y y' r ih => dsimp; rw [ih]
    | mul_1 x x' y r ih => dsimp; rw [ih]
    | mul_2 x y y' r ih => dsimp; rw [ih]
    | zero_add x => dsimp; rw [zero_add]
    | add_zero x => dsimp; rw [add_zero]
    | one_mul x => dsimp; rw [one_mul]
    | mul_one x => dsimp; rw [mul_one]
    | neg_add_cancel x => dsimp; rw [neg_add_cancel]
    | add_comm x y => dsimp; rw [add_comm]
    | add_assoc x y z => dsimp; rw [add_assoc]
    | mul_assoc x y z => dsimp; rw [mul_assoc]
    | left_distrib x y z => dsimp; rw [mul_add]
    | right_distrib x y z => dsimp; rw [add_mul]
    | zero_mul x => dsimp; rw [zero_mul]
    | mul_zero x => dsimp; rw [mul_zero]
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt where
  toFun := descFun F s
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by
    refine Quot.induction_on₂ x y fun a b => ?_
    dsimp [descFun]
    rw [← quot_add]
    rfl
  map_mul' x y := by exact Quot.induction_on₂ x y fun a b => rfl
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := RingHom.ext fun x => by
    change (colimitCocone F).pt →+* s.pt at m
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j → s.pt)) (w j)) x
    | add x y ih_x ih_y => simp [ih_x, ih_y]
    | mul x y ih_x ih_y => simp [ih_x, ih_y]
instance hasColimits_ringCat : HasColimits RingCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }
end RingCat.Colimits
namespace CommRingCat.Colimits
variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})
inductive Prequotient 
  | of : ∀ (j : J) (_ : F.obj j), Prequotient 
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient
  | mul : Prequotient → Prequotient → Prequotient
instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩
open Prequotient
inductive Relation : Prequotient F → Prequotient F → Prop 
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | one : ∀ j, Relation (Prequotient.of j 1) one
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : ∀ (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
  | neg_add_cancel : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | mul_comm : ∀ x y, Relation (mul x y) (mul y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : ∀ x, Relation (mul zero x) zero
  | mul_zero : ∀ x, Relation (mul x zero) zero
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩
attribute [instance] colimitSetoid
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
instance ColimitType.instZero : Zero (ColimitType F) where zero := Quotient.mk _ zero
instance ColimitType.instAdd : Add (ColimitType F) where
  add := Quotient.map₂ add <| fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)
instance ColimitType.instNeg : Neg (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  neg_add_cancel := Quotient.ind <| fun _ => Quotient.sound <| Relation.neg_add_cancel _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
instance InhabitedColimitType : Inhabited <| ColimitType F where
  default := 0
instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }
instance : CommRing (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
    one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.one_mul _
    mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_one _
    add_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.add_comm _ _
    mul_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.mul_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
    mul_zero := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_zero _
    zero_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.zero_mul _
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }
@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl
@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl
@[simp]
theorem quot_neg (x : Prequotient F) :
    (by exact Quot.mk Setoid.r (neg x) : ColimitType F) = -(by exact Quot.mk Setoid.r x) :=
  rfl
@[simp]
theorem quot_add (x y) :
    (by exact Quot.mk Setoid.r (add x y) : ColimitType F) =
      (by exact Quot.mk _ x) + (by exact Quot.mk _ y) :=
  rfl
@[simp]
theorem quot_mul (x y) :
    (by exact Quot.mk Setoid.r (mul x y) : ColimitType F) =
      (by exact Quot.mk _ x) * (by exact Quot.mk _ y) :=
  rfl
def colimit : CommRingCat :=
  CommRingCat.of (ColimitType F)
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := coconeFun F j
  map_one' := by apply Quot.sound; apply Relation.one
  map_mul' := by intros; apply Quot.sound; apply Relation.mul
  map_zero' := by apply Quot.sound; apply Relation.zero
  map_add' := by intros; apply Quot.sound; apply Relation.add
@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map
@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f, comp_apply]
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
  | mul x y => descFunLift s x * descFunLift s y
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (s.ι.naturality f) x
    | zero j => simp
    | one j => simp
    | neg j x => simp
    | add j x y => simp
    | mul j x y => simp
    | neg_1 x x' r ih => dsimp; rw [ih]
    | add_1 x x' y r ih => dsimp; rw [ih]
    | add_2 x y y' r ih => dsimp; rw [ih]
    | mul_1 x x' y r ih => dsimp; rw [ih]
    | mul_2 x y y' r ih => dsimp; rw [ih]
    | zero_add x => dsimp; rw [zero_add]
    | add_zero x => dsimp; rw [add_zero]
    | one_mul x => dsimp; rw [one_mul]
    | mul_one x => dsimp; rw [mul_one]
    | neg_add_cancel x => dsimp; rw [neg_add_cancel]
    | add_comm x y => dsimp; rw [add_comm]
    | mul_comm x y => dsimp; rw [mul_comm]
    | add_assoc x y z => dsimp; rw [add_assoc]
    | mul_assoc x y z => dsimp; rw [mul_assoc]
    | left_distrib x y z => dsimp; rw [mul_add]
    | right_distrib x y z => dsimp; rw [add_mul]
    | zero_mul x => dsimp; rw [zero_mul]
    | mul_zero x => dsimp; rw [mul_zero]
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt where
  toFun := descFun F s
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by
    refine Quot.induction_on₂ x y fun a b => ?_
    dsimp [descFun]
    rw [← quot_add]
    rfl
  map_mul' x y := by exact Quot.induction_on₂ x y fun a b => rfl
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := RingHom.ext fun x => by
    change (colimitCocone F).pt →+* s.pt at m
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j → s.pt)) (w j)) x
    | add x y ih_x ih_y => simp [ih_x, ih_y]
    | mul x y ih_x ih_y => simp [ih_x, ih_y]
instance hasColimits_commRingCat : HasColimits CommRingCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }
end CommRingCat.Colimits