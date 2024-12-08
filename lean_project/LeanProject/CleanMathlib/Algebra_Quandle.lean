import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Aut
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring
open MulOpposite
universe u v
class Shelf (α : Type u) where
  act : α → α → α
  self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z)
class UnitalShelf (α : Type u) extends Shelf α, One α where
  one_act : ∀ a : α, act 1 a = a
  act_one : ∀ a : α, act a 1 = a
@[ext]
structure ShelfHom (S₁ : Type*) (S₂ : Type*) [Shelf S₁] [Shelf S₂] where
  toFun : S₁ → S₂
  map_act' : ∀ {x y : S₁}, toFun (Shelf.act x y) = Shelf.act (toFun x) (toFun y)
class Rack (α : Type u) extends Shelf α where
  invAct : α → α → α
  left_inv : ∀ x, Function.LeftInverse (invAct x) (act x)
  right_inv : ∀ x, Function.RightInverse (invAct x) (act x)
scoped[Quandles] infixr:65 " ◃ " => Shelf.act
scoped[Quandles] infixr:65 " ◃⁻¹ " => Rack.invAct
scoped[Quandles] infixr:25 " →◃ " => ShelfHom
open Quandles
namespace UnitalShelf
open Shelf
variable {S : Type*} [UnitalShelf S]
lemma act_act_self_eq (x y : S) : (x ◃ y) ◃ x = x ◃ y := by
  have h : (x ◃ y) ◃ x = (x ◃ y) ◃ (x ◃ 1) := by rw [act_one]
  rw [h, ← Shelf.self_distrib, act_one]
lemma act_idem (x : S) : (x ◃ x) = x := by rw [← act_one x, ← Shelf.self_distrib, act_one]
lemma act_self_act_eq (x y : S) : x ◃ (x ◃ y) = x ◃ y := by
  have h : x ◃ (x ◃ y) = (x ◃ 1) ◃ (x ◃ y) := by rw [act_one]
  rw [h, ← Shelf.self_distrib, one_act]
lemma assoc (x y z : S) : (x ◃ y) ◃ z = x ◃ y ◃ z := by
  rw [self_distrib, self_distrib, act_act_self_eq, act_self_act_eq]
end UnitalShelf
namespace Rack
variable {R : Type*} [Rack R]
export Shelf (self_distrib)
def act' (x : R) : R ≃ R where
  toFun := Shelf.act x
  invFun := invAct x
  left_inv := left_inv x
  right_inv := right_inv x
@[simp]
theorem act'_apply (x y : R) : act' x y = x ◃ y :=
  rfl
@[simp]
theorem act'_symm_apply (x y : R) : (act' x).symm y = x ◃⁻¹ y :=
  rfl
@[simp]
theorem invAct_apply (x y : R) : (act' x)⁻¹ y = x ◃⁻¹ y :=
  rfl
@[simp]
theorem invAct_act_eq (x y : R) : x ◃⁻¹ x ◃ y = y :=
  left_inv x y
@[simp]
theorem act_invAct_eq (x y : R) : x ◃ x ◃⁻¹ y = y :=
  right_inv x y
theorem left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' := by
  constructor
  · apply (act' x).injective
  rintro rfl
  rfl
theorem left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' := by
  constructor
  · apply (act' x).symm.injective
  rintro rfl
  rfl
theorem self_distrib_inv {x y z : R} : x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ x ◃⁻¹ z := by
  rw [← left_cancel (x ◃⁻¹ y), right_inv, ← left_cancel x, right_inv, self_distrib]
  repeat' rw [right_inv]
theorem ad_conj {R : Type*} [Rack R] (x y : R) : act' (x ◃ y) = act' x * act' y * (act' x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]; ext z
  apply self_distrib.symm
instance oppositeRack : Rack Rᵐᵒᵖ where
  act x y := op (invAct (unop x) (unop y))
  self_distrib := by
    intro x y z
    induction x
    induction y
    induction z
    simp only [op_inj, unop_op, op_unop]
    rw [self_distrib_inv]
  invAct x y := op (Shelf.act (unop x) (unop y))
  left_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp
  right_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp
@[simp]
theorem op_act_op_eq {x y : R} : op x ◃ op y = op (x ◃⁻¹ y) :=
  rfl
@[simp]
theorem op_invAct_op_eq {x y : R} : op x ◃⁻¹ op y = op (x ◃ y) :=
  rfl
@[simp]
theorem self_act_act_eq {x y : R} : (x ◃ x) ◃ y = x ◃ y := by rw [← right_inv x y, ← self_distrib]
@[simp]
theorem self_invAct_invAct_eq {x y : R} : (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y := by
  have h := @self_act_act_eq _ _ (op x) (op y)
  simpa using h
@[simp]
theorem self_act_invAct_eq {x y : R} : (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y := by
  rw [← left_cancel (x ◃ x)]
  rw [right_inv]
  rw [self_act_act_eq]
  rw [right_inv]
@[simp]
theorem self_invAct_act_eq {x y : R} : (x ◃⁻¹ x) ◃ y = x ◃ y := by
  have h := @self_act_invAct_eq _ _ (op x) (op y)
  simpa using h
theorem self_act_eq_iff_eq {x y : R} : x ◃ x = y ◃ y ↔ x = y := by
  constructor; swap
  · rintro rfl; rfl
  intro h
  trans (x ◃ x) ◃⁻¹ x ◃ x
  · rw [← left_cancel (x ◃ x), right_inv, self_act_act_eq]
  · rw [h, ← left_cancel (y ◃ y), right_inv, self_act_act_eq]
theorem self_invAct_eq_iff_eq {x y : R} : x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y := by
  have h := @self_act_eq_iff_eq _ _ (op x) (op y)
  simpa using h
def selfApplyEquiv (R : Type*) [Rack R] : R ≃ R where
  toFun x := x ◃ x
  invFun x := x ◃⁻¹ x
  left_inv x := by simp
  right_inv x := by simp
def IsInvolutory (R : Type*) [Rack R] : Prop :=
  ∀ x : R, Function.Involutive (Shelf.act x)
theorem involutory_invAct_eq_act {R : Type*} [Rack R] (h : IsInvolutory R) (x y : R) :
    x ◃⁻¹ y = x ◃ y := by
  rw [← left_cancel x, right_inv, h x]
def IsAbelian (R : Type*) [Rack R] : Prop :=
  ∀ x y z w : R, (x ◃ y) ◃ z ◃ w = (x ◃ z) ◃ y ◃ w
theorem assoc_iff_id {R : Type*} [Rack R] {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z := by
  rw [self_distrib]
  rw [left_cancel]
end Rack
namespace ShelfHom
variable {S₁ : Type*} {S₂ : Type*} {S₃ : Type*} [Shelf S₁] [Shelf S₂] [Shelf S₃]
instance : FunLike (S₁ →◃ S₂) S₁ S₂ where
  coe := toFun
  coe_injective' | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
@[simp] theorem toFun_eq_coe (f : S₁ →◃ S₂) : f.toFun = f := rfl
@[simp]
theorem map_act (f : S₁ →◃ S₂) {x y : S₁} : f (x ◃ y) = f x ◃ f y :=
  map_act' f
def id (S : Type*) [Shelf S] : S →◃ S where
  toFun := fun x => x
  map_act' := by simp
instance inhabited (S : Type*) [Shelf S] : Inhabited (S →◃ S) :=
  ⟨id S⟩
def comp (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) : S₁ →◃ S₃ where
  toFun := g.toFun ∘ f.toFun
  map_act' := by simp
@[simp]
theorem comp_apply (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) (x : S₁) : (g.comp f) x = g (f x) :=
  rfl
end ShelfHom
class Quandle (α : Type*) extends Rack α where
  fix : ∀ {x : α}, act x x = x
namespace Quandle
open Rack
variable {Q : Type*} [Quandle Q]
attribute [simp] fix
@[simp]
theorem fix_inv {x : Q} : x ◃⁻¹ x = x := by
  rw [← left_cancel x]
  simp
instance oppositeQuandle : Quandle Qᵐᵒᵖ where
  fix := by
    intro x
    induction x
    simp
abbrev Conj (G : Type*) := G
instance Conj.quandle (G : Type*) [Group G] : Quandle (Conj G) where
  act x := @MulAut.conj G _ x
  self_distrib := by
    intro x y z
    dsimp only [MulAut.conj_apply]
    simp [mul_assoc]
  invAct x := (@MulAut.conj G _ x).symm
  left_inv x y := by
    simp [act', mul_assoc]
  right_inv x y := by
    simp [act', mul_assoc]
  fix := by simp
@[simp]
theorem conj_act_eq_conj {G : Type*} [Group G] (x y : Conj G) :
    x ◃ y = ((x : G) * (y : G) * (x : G)⁻¹ : G) :=
  rfl
theorem conj_swap {G : Type*} [Group G] (x y : Conj G) : x ◃ y = y ↔ y ◃ x = x := by
  dsimp [Conj] at *; constructor
  repeat' intro h; conv_rhs => rw [eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq h)]; simp
def Conj.map {G : Type*} {H : Type*} [Group G] [Group H] (f : G →* H) : Conj G →◃ Conj H where
  toFun := f
  map_act' := by simp
def Dihedral (n : ℕ) :=
  ZMod n
def dihedralAct (n : ℕ) (a : ZMod n) : ZMod n → ZMod n := fun b => 2 * a - b
theorem dihedralAct.inv (n : ℕ) (a : ZMod n) : Function.Involutive (dihedralAct n a) := by
  intro b
  dsimp only [dihedralAct]
  simp
instance (n : ℕ) : Quandle (Dihedral n) where
  act := dihedralAct n
  self_distrib := by
    intro x y z
    simp only [dihedralAct]
    ring_nf
  invAct := dihedralAct n
  left_inv x := (dihedralAct.inv n x).leftInverse
  right_inv x := (dihedralAct.inv n x).rightInverse
  fix := by
    intro x
    simp only [dihedralAct]
    ring_nf
end Quandle
namespace Rack
def toConj (R : Type*) [Rack R] : R →◃ Quandle.Conj (R ≃ R) where
  toFun := act'
  map_act' := by
    intro x y
    exact ad_conj x y
section EnvelGroup
inductive PreEnvelGroup (R : Type u) : Type u
  | unit : PreEnvelGroup R
  | incl (x : R) : PreEnvelGroup R
  | mul (a b : PreEnvelGroup R) : PreEnvelGroup R
  | inv (a : PreEnvelGroup R) : PreEnvelGroup R
instance PreEnvelGroup.inhabited (R : Type u) : Inhabited (PreEnvelGroup R) :=
  ⟨PreEnvelGroup.unit⟩
open PreEnvelGroup
inductive PreEnvelGroupRel' (R : Type u) [Rack R] : PreEnvelGroup R → PreEnvelGroup R → Type u
  | refl {a : PreEnvelGroup R} : PreEnvelGroupRel' R a a
  | symm {a b : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b) : PreEnvelGroupRel' R b a
  | trans {a b c : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b)
    (hbc : PreEnvelGroupRel' R b c) : PreEnvelGroupRel' R a c
  | congr_mul {a b a' b' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a')
    (hb : PreEnvelGroupRel' R b b') : PreEnvelGroupRel' R (mul a b) (mul a' b')
  | congr_inv {a a' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a') :
    PreEnvelGroupRel' R (inv a) (inv a')
  | assoc (a b c : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (mul a b) c) (mul a (mul b c))
  | one_mul (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul unit a) a
  | mul_one (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul a unit) a
  | inv_mul_cancel (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (inv a) a) unit
  | act_incl (x y : R) :
    PreEnvelGroupRel' R (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))
instance PreEnvelGroupRel'.inhabited (R : Type u) [Rack R] :
    Inhabited (PreEnvelGroupRel' R unit unit) :=
  ⟨PreEnvelGroupRel'.refl⟩
inductive PreEnvelGroupRel (R : Type u) [Rack R] : PreEnvelGroup R → PreEnvelGroup R → Prop
  | rel {a b : PreEnvelGroup R} (r : PreEnvelGroupRel' R a b) : PreEnvelGroupRel R a b
theorem PreEnvelGroupRel'.rel {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel' R a b → PreEnvelGroupRel R a b := PreEnvelGroupRel.rel
@[refl]
theorem PreEnvelGroupRel.refl {R : Type u} [Rack R] {a : PreEnvelGroup R} :
    PreEnvelGroupRel R a a :=
  PreEnvelGroupRel.rel PreEnvelGroupRel'.refl
@[symm]
theorem PreEnvelGroupRel.symm {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel R a b → PreEnvelGroupRel R b a
  | ⟨r⟩ => r.symm.rel
@[trans]
theorem PreEnvelGroupRel.trans {R : Type u} [Rack R] {a b c : PreEnvelGroup R} :
    PreEnvelGroupRel R a b → PreEnvelGroupRel R b c → PreEnvelGroupRel R a c
  | ⟨rab⟩, ⟨rbc⟩ => (rab.trans rbc).rel
instance PreEnvelGroup.setoid (R : Type*) [Rack R] : Setoid (PreEnvelGroup R) where
  r := PreEnvelGroupRel R
  iseqv := by
    constructor
    · apply PreEnvelGroupRel.refl
    · apply PreEnvelGroupRel.symm
    · apply PreEnvelGroupRel.trans
def EnvelGroup (R : Type*) [Rack R] :=
  Quotient (PreEnvelGroup.setoid R)
instance (R : Type*) [Rack R] : DivInvMonoid (EnvelGroup R) where
  mul a b :=
    Quotient.liftOn₂ a b (fun a b => ⟦PreEnvelGroup.mul a b⟧) fun _ _ _ _ ⟨ha⟩ ⟨hb⟩ =>
      Quotient.sound (PreEnvelGroupRel'.congr_mul ha hb).rel
  one := ⟦unit⟧
  inv a :=
    Quotient.liftOn a (fun a => ⟦PreEnvelGroup.inv a⟧) fun _ _ ⟨ha⟩ =>
      Quotient.sound (PreEnvelGroupRel'.congr_inv ha).rel
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun a b c => Quotient.sound (PreEnvelGroupRel'.assoc a b c).rel
  one_mul a := Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.one_mul a).rel
  mul_one a := Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.mul_one a).rel
instance (R : Type*) [Rack R] : Group (EnvelGroup R) :=
  { inv_mul_cancel := fun a =>
      Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.inv_mul_cancel a).rel }
instance EnvelGroup.inhabited (R : Type*) [Rack R] : Inhabited (EnvelGroup R) :=
  ⟨1⟩
def toEnvelGroup (R : Type*) [Rack R] : R →◃ Quandle.Conj (EnvelGroup R) where
  toFun x := ⟦incl x⟧
  map_act' := @fun x y => Quotient.sound (PreEnvelGroupRel'.act_incl x y).symm.rel
def toEnvelGroup.mapAux {R : Type*} [Rack R] {G : Type*} [Group G] (f : R →◃ Quandle.Conj G) :
    PreEnvelGroup R → G
  | .unit => 1
  | .incl x => f x
  | .mul a b => toEnvelGroup.mapAux f a * toEnvelGroup.mapAux f b
  | .inv a => (toEnvelGroup.mapAux f a)⁻¹
namespace toEnvelGroup.mapAux
open PreEnvelGroupRel'
theorem well_def {R : Type*} [Rack R] {G : Type*} [Group G] (f : R →◃ Quandle.Conj G) :
    ∀ {a b : PreEnvelGroup R},
      PreEnvelGroupRel' R a b → toEnvelGroup.mapAux f a = toEnvelGroup.mapAux f b
  | _, _, PreEnvelGroupRel'.refl => rfl
  | _, _, PreEnvelGroupRel'.symm h => (well_def f h).symm
  | _, _, PreEnvelGroupRel'.trans hac hcb => Eq.trans (well_def f hac) (well_def f hcb)
  | _, _, PreEnvelGroupRel'.congr_mul ha hb => by
    simp [toEnvelGroup.mapAux, well_def f ha, well_def f hb]
  | _, _, congr_inv ha => by simp [toEnvelGroup.mapAux, well_def f ha]
  | _, _, assoc a b c => by apply mul_assoc
  | _, _, PreEnvelGroupRel'.one_mul a => by simp [toEnvelGroup.mapAux]
  | _, _, PreEnvelGroupRel'.mul_one a => by simp [toEnvelGroup.mapAux]
  | _, _, PreEnvelGroupRel'.inv_mul_cancel a => by simp [toEnvelGroup.mapAux]
  | _, _, act_incl x y => by simp [toEnvelGroup.mapAux]
end toEnvelGroup.mapAux
def toEnvelGroup.map {R : Type*} [Rack R] {G : Type*} [Group G] :
    (R →◃ Quandle.Conj G) ≃ (EnvelGroup R →* G) where
  toFun f :=
    { toFun := fun x =>
        Quotient.liftOn x (toEnvelGroup.mapAux f) fun _ _ ⟨hab⟩ =>
          toEnvelGroup.mapAux.well_def f hab
      map_one' := by
        change Quotient.liftOn ⟦Rack.PreEnvelGroup.unit⟧ (toEnvelGroup.mapAux f) _ = 1
        simp only [Quotient.lift_mk, mapAux]
      map_mul' := fun x y =>
        Quotient.inductionOn₂ x y fun x y => by
          simp only [toEnvelGroup.mapAux]
          change Quotient.liftOn ⟦mul x y⟧ (toEnvelGroup.mapAux f) _ = _
          simp [toEnvelGroup.mapAux] }
  invFun F := (Quandle.Conj.map F).comp (toEnvelGroup R)
  left_inv f := by ext; rfl
  right_inv F :=
    MonoidHom.ext fun x =>
      Quotient.inductionOn x fun x => by
        induction x with
        | unit => exact F.map_one.symm
        | incl => rfl
        | mul x y ih_x ih_y =>
          have hm : ⟦x.mul y⟧ = @Mul.mul (EnvelGroup R) _ ⟦x⟧ ⟦y⟧ := rfl
          simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.lift_mk]
          suffices ∀ x y, F (Mul.mul x y) = F (x) * F (y) by
            simp_all only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.lift_mk, hm]
            rw [← ih_x, ← ih_y, mapAux]
          exact F.map_mul
        | inv x ih_x =>
          have hm : ⟦x.inv⟧ = @Inv.inv (EnvelGroup R) _ ⟦x⟧ := rfl
          rw [hm, F.map_inv, MonoidHom.map_inv, ih_x]
theorem toEnvelGroup.univ (R : Type*) [Rack R] (G : Type*) [Group G] (f : R →◃ Quandle.Conj G) :
    (Quandle.Conj.map (toEnvelGroup.map f)).comp (toEnvelGroup R) = f :=
  toEnvelGroup.map.symm_apply_apply f
theorem toEnvelGroup.univ_uniq (R : Type*) [Rack R] (G : Type*) [Group G]
    (f : R →◃ Quandle.Conj G) (g : EnvelGroup R →* G)
    (h : f = (Quandle.Conj.map g).comp (toEnvelGroup R)) : g = toEnvelGroup.map f :=
  h.symm ▸ (toEnvelGroup.map.apply_symm_apply g).symm
def envelAction {R : Type*} [Rack R] : EnvelGroup R →* R ≃ R :=
  toEnvelGroup.map (toConj R)
@[simp]
theorem envelAction_prop {R : Type*} [Rack R] (x y : R) :
    envelAction (toEnvelGroup R x) y = x ◃ y :=
  rfl
end EnvelGroup
end Rack