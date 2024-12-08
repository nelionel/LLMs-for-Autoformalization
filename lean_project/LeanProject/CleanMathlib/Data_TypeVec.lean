import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Common
universe u v w
@[pp_with_univ]
def TypeVec (n : ℕ) :=
  Fin2 n → Type*
instance {n} : Inhabited (TypeVec.{u} n) :=
  ⟨fun _ => PUnit⟩
namespace TypeVec
variable {n : ℕ}
def Arrow (α β : TypeVec n) :=
  ∀ i : Fin2 n, α i → β i
@[inherit_doc] scoped[MvFunctor] infixl:40 " ⟹ " => TypeVec.Arrow
open MvFunctor
@[ext]
theorem Arrow.ext {α β : TypeVec n} (f g : α ⟹ β) :
    (∀ i, f i = g i) → f = g := by
  intro h; funext i; apply h
instance Arrow.inhabited (α β : TypeVec n) [∀ i, Inhabited (β i)] : Inhabited (α ⟹ β) :=
  ⟨fun _ _ => default⟩
def id {α : TypeVec n} : α ⟹ α := fun _ x => x
def comp {α β γ : TypeVec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ := fun i x => g i (f i x)
@[inherit_doc] scoped[MvFunctor] infixr:80 " ⊚ " => TypeVec.comp 
@[simp]
theorem id_comp {α β : TypeVec n} (f : α ⟹ β) : id ⊚ f = f :=
  rfl
@[simp]
theorem comp_id {α β : TypeVec n} (f : α ⟹ β) : f ⊚ id = f :=
  rfl
theorem comp_assoc {α β γ δ : TypeVec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f :=
  rfl
def append1 (α : TypeVec n) (β : Type*) : TypeVec (n + 1)
  | Fin2.fs i => α i
  | Fin2.fz => β
@[inherit_doc] infixl:67 " ::: " => append1
def drop (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.fs
def last (α : TypeVec.{u} (n + 1)) : Type _ :=
  α Fin2.fz
instance last.inhabited (α : TypeVec (n + 1)) [Inhabited (α Fin2.fz)] : Inhabited (last α) :=
  ⟨show α Fin2.fz from default⟩
theorem drop_append1 {α : TypeVec n} {β : Type*} {i : Fin2 n} : drop (append1 α β) i = α i :=
  rfl
theorem drop_append1' {α : TypeVec n} {β : Type*} : drop (append1 α β) = α :=
  funext fun _ => drop_append1
theorem last_append1 {α : TypeVec n} {β : Type*} : last (append1 α β) = β :=
  rfl
@[simp]
theorem append1_drop_last (α : TypeVec (n + 1)) : append1 (drop α) (last α) = α :=
  funext fun i => by cases i <;> rfl
@[elab_as_elim]
def append1Cases {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ := by
  rw [← @append1_drop_last _ γ]; apply H
@[simp]
theorem append1_cases_append1 {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (α β) :
    @append1Cases _ C H (append1 α β) = H α β :=
  rfl
def splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
  | Fin2.fs i => f i
  | Fin2.fz => g
def appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    append1 α β ⟹ append1 α' β' :=
  splitFun f g
@[inherit_doc] infixl:0 " ::: " => appendFun
def dropFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : drop α ⟹ drop β := fun i => f i.fs
def lastFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : last α → last β :=
  f Fin2.fz
def nilFun {α : TypeVec 0} {β : TypeVec 0} : α ⟹ β := fun i => by apply Fin2.elim0 i
theorem eq_of_drop_last_eq {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
    (h₁ : lastFun f = lastFun g) : f = g := by
  refine funext (fun x => ?_)
  cases x
  · apply h₁
  · apply congr_fun h₀
@[simp]
theorem dropFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    dropFun (splitFun f g) = f :=
  rfl
def Arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | _ => Eq.mp (congr_fun h _)
def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | _ => Eq.mpr (congr_fun h _)
def toAppend1DropLast {α : TypeVec (n + 1)} : α ⟹ (drop α ::: last α) :=
  Arrow.mpr (append1_drop_last _)
def fromAppend1DropLast {α : TypeVec (n + 1)} : (drop α ::: last α) ⟹ α :=
  Arrow.mp (append1_drop_last _)
@[simp]
theorem lastFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    lastFun (splitFun f g) = g :=
  rfl
@[simp]
theorem dropFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    dropFun (f ::: g) = f :=
  rfl
@[simp]
theorem lastFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    lastFun (f ::: g) = g :=
  rfl
theorem split_dropFun_lastFun {α α' : TypeVec (n + 1)} (f : α ⟹ α') :
    splitFun (dropFun f) (lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl
theorem splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
    (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g' := by
  rw [← dropFun_splitFun f g, H, ← lastFun_splitFun f g, H]; simp
theorem appendFun_inj {α α' : TypeVec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β → β'} :
    (f ::: g : (α ::: β) ⟹ _) = (f' ::: g' : (α ::: β) ⟹ _)
    → f = f' ∧ g = g' :=
  splitFun_inj
theorem splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁)
    (f₁ : drop α₁ ⟹ drop α₂) (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
    splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀ :=
  eq_of_drop_last_eq rfl rfl
theorem appendFun_comp_splitFun {α γ : TypeVec n} {β δ : Type*} {ε : TypeVec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last ε → β) (g₁ : β → δ) :
    appendFun f₁ g₁ ⊚ splitFun f₀ g₀ = splitFun (α' := γ.append1 δ) (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (splitFun_comp _ _ _ _).symm
theorem appendFun_comp  {α₀ α₁ α₂ : TypeVec n}
    {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl
theorem appendFun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ ⊚ f₀ ::: g₁ ∘ g₀) :=
  eq_of_drop_last_eq rfl rfl
theorem nilFun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0) : nilFun ⊚ f₀ = f₀ :=
  funext fun x => by apply Fin2.elim0 x 
theorem appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type u} (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl
@[simp]
theorem dropFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀ :=
  rfl
@[simp]
theorem lastFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀ :=
  rfl
theorem appendFun_aux {α α' : TypeVec n} {β β' : Type*} (f : (α ::: β) ⟹ (α' ::: β')) :
    (dropFun f ::: lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl
theorem appendFun_id_id {α : TypeVec n} {β : Type*} :
    (@TypeVec.id n α ::: @_root_.id β) = TypeVec.id :=
  eq_of_drop_last_eq rfl rfl
instance subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨fun a b => funext fun a => by apply Fin2.elim0 a⟩ 
protected def casesNil {β : TypeVec 0 → Sort*} (f : β Fin2.elim0) : ∀ v, β v :=
  fun v => cast (by congr; funext i; cases i) f
protected def casesCons (n : ℕ) {β : TypeVec (n + 1) → Sort*}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) :
    ∀ v, β v :=
  fun v : TypeVec (n + 1) => cast (by simp) (f v.last v.drop)
protected theorem casesNil_append1 {β : TypeVec 0 → Sort*} (f : β Fin2.elim0) :
    TypeVec.casesNil f Fin2.elim0 = f :=
  rfl
protected theorem casesCons_append1 (n : ℕ) {β : TypeVec (n + 1) → Sort*}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) (v : TypeVec n) (α) :
    TypeVec.casesCons n f (v ::: α) = f α v :=
  rfl
def typevecCasesNil₃ {β : ∀ v v' : TypeVec 0, v ⟹ v' → Sort*}
    (f : β Fin2.elim0 Fin2.elim0 nilFun) :
    ∀ v v' fs, β v v' fs := fun v v' fs => by
  refine cast ?_ f
  have eq₁ : v = Fin2.elim0 := by funext i; contradiction
  have eq₂ : v' = Fin2.elim0 := by funext i; contradiction
  have eq₃ : fs = nilFun := by funext i; contradiction
  cases eq₁; cases eq₂; cases eq₃; rfl
def typevecCasesCons₃ (n : ℕ) {β : ∀ v v' : TypeVec (n + 1), v ⟹ v' → Sort*}
    (F : ∀ (t t') (f : t → t') (v v' : TypeVec n) (fs : v ⟹ v'),
    β (v ::: t) (v' ::: t') (fs ::: f)) :
    ∀ v v' fs, β v v' fs := by
  intro v v'
  rw [← append1_drop_last v, ← append1_drop_last v']
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F
def typevecCasesNil₂ {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort*} (f : β nilFun) : ∀ f, β f := by
  intro g
  suffices g = nilFun by rwa [this]
  ext ⟨⟩
def typevecCasesCons₂ (n : ℕ) (t t' : Type*) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) : ∀ fs, β fs := by
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F
theorem typevecCasesNil₂_appendFun {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort*} (f : β nilFun) :
    typevecCasesNil₂ f nilFun = f :=
  rfl
theorem typevecCasesCons₂_appendFun (n : ℕ) (t t' : Type*) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f))
    (f fs) :
    typevecCasesCons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl
def PredLast (α : TypeVec n) {β : Type*} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop
  | Fin2.fs _ => fun _ => True
  | Fin2.fz => p
def RelLast (α : TypeVec n) {β γ : Type u} (r : β → γ → Prop) :
    ∀ ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
  | Fin2.fs _ => Eq
  | Fin2.fz => r
section Liftp'
open Nat
def «repeat» : ∀ (n : ℕ), Sort _ → TypeVec n
  | 0, _ => Fin2.elim0
  | Nat.succ i, t => append1 («repeat» i t) t
def prod : ∀ {n}, TypeVec.{u} n → TypeVec.{u} n → TypeVec n
  | 0,     _, _ => Fin2.elim0
  | n + 1, α, β => (@prod n (drop α) (drop β)) ::: (last α × last β)
@[inherit_doc] scoped[MvFunctor] infixl:45 " ⊗ " => TypeVec.prod
protected def const {β} (x : β) : ∀ {n} (α : TypeVec n), α ⟹ «repeat» _ β
  | succ _, α, Fin2.fs _ => TypeVec.const x (drop α) _
  | succ _, _, Fin2.fz   => fun _ => x
open Function (uncurry)
def repeatEq : ∀ {n} (α : TypeVec n), (α ⊗ α) ⟹ «repeat» _ Prop
  | 0, _ => nilFun
  | succ _, α => repeatEq (drop α) ::: uncurry Eq
theorem const_append1 {β γ} (x : γ) {n} (α : TypeVec n) :
    TypeVec.const x (α ::: β) = appendFun (TypeVec.const x α) fun _ => x := by
  ext i : 1; cases i <;> rfl
theorem eq_nilFun {α β : TypeVec 0} (f : α ⟹ β) : f = nilFun := by
  ext x; cases x
theorem id_eq_nilFun {α : TypeVec 0} : @id _ α = nilFun := by
  ext x; cases x
theorem const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nilFun := by
  ext i : 1; cases i
@[typevec]
theorem repeat_eq_append1 {β} {n} (α : TypeVec n) :
    repeatEq (α ::: β) = splitFun (α := (α ⊗ α) ::: _ )
    (α' := («repeat» n Prop) ::: _) (repeatEq α) (uncurry Eq) := by
  induction n <;> rfl
@[typevec]
theorem repeat_eq_nil (α : TypeVec 0) : repeatEq α = nilFun := by ext i; cases i
def PredLast' (α : TypeVec n) {β : Type*} (p : β → Prop) :
    (α ::: β) ⟹ «repeat» (n + 1) Prop :=
  splitFun (TypeVec.const True α) p
def RelLast' (α : TypeVec n) {β : Type*} (p : β → β → Prop) :
    (α ::: β) ⊗ (α ::: β) ⟹ «repeat» (n + 1) Prop :=
  splitFun (repeatEq α) (uncurry p)
def Curry (F : TypeVec.{u} (n + 1) → Type*) (α : Type u) (β : TypeVec.{u} n) : Type _ :=
  F (β ::: α)
instance Curry.inhabited (F : TypeVec.{u} (n + 1) → Type*) (α : Type u) (β : TypeVec.{u} n)
    [I : Inhabited (F <| (β ::: α))] : Inhabited (Curry F α β) :=
  I
def dropRepeat (α : Type*) : ∀ {n}, drop («repeat» (succ n) α) ⟹ «repeat» n α
  | succ _, Fin2.fs i => dropRepeat α i
  | succ _, Fin2.fz   => fun (a : α) => a
def ofRepeat {α : Sort _} : ∀ {n i}, «repeat» n α i → α
  | _, Fin2.fz   => fun (a : α) => a
  | _, Fin2.fs i => @ofRepeat _ _ i
theorem const_iff_true {α : TypeVec n} {i x p} : ofRepeat (TypeVec.const p α i x) ↔ p := by
  induction i with
  | fz      => rfl
  | fs _ ih => erw [TypeVec.const, @ih (drop α) x]
section
variable {α β : TypeVec.{u} n}
variable (p : α ⟹ «repeat» n Prop)
def prod.fst : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ α
  | succ _, α, β, Fin2.fs i => @prod.fst _ (drop α) (drop β) i
  | succ _, _, _, Fin2.fz => Prod.fst
def prod.snd : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ β
  | succ _, α, β, Fin2.fs i => @prod.snd _ (drop α) (drop β) i
  | succ _, _, _, Fin2.fz => Prod.snd
def prod.diag : ∀ {n} {α : TypeVec.{u} n}, α ⟹ α ⊗ α
  | succ _, α, Fin2.fs _, x => @prod.diag _ (drop α) _ x
  | succ _, _, Fin2.fz, x => (x, x)
def prod.mk : ∀ {n} {α β : TypeVec.{u} n} (i : Fin2 n), α i → β i → (α ⊗ β) i
  | succ _, α, β, Fin2.fs i => mk (α := fun i => α i.fs) (β := fun i => β i.fs) i
  | succ _, _, _, Fin2.fz   => Prod.mk
end
@[simp]
theorem prod_fst_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.fst i (prod.mk i a b) = a := by
  induction i with
  | fz => simp_all only [prod.fst, prod.mk]
  | fs _ i_ih => apply i_ih
@[simp]
theorem prod_snd_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.snd i (prod.mk i a b) = b := by
  induction i with
  | fz => simp_all [prod.snd, prod.mk]
  | fs _ i_ih => apply i_ih
protected def prod.map : ∀ {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β → α' ⟹ β' → α ⊗ α' ⟹ β ⊗ β'
  | succ _, α, α', β, β', x, y, Fin2.fs _, a =>
    @prod.map _ (drop α) (drop α') (drop β) (drop β') (dropFun x) (dropFun y) _ a
  | succ _, _, _, _, _, x, y, Fin2.fz, a => (x _ a.1, y _ a.2)
@[inherit_doc] scoped[MvFunctor] infixl:45 " ⊗' " => TypeVec.prod.map
theorem fst_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.fst ⊚ (f ⊗' g) = f ⊚ TypeVec.prod.fst := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
theorem snd_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.snd ⊚ (f ⊗' g) = g ⊚ TypeVec.prod.snd := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
theorem fst_diag {α : TypeVec n} : TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
theorem snd_diag {α : TypeVec n} : TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
theorem repeatEq_iff_eq {α : TypeVec n} {i x y} :
    ofRepeat (repeatEq α i (prod.mk _ x y)) ↔ x = y := by
  induction i with
  | fz => rfl
  | fs _ i_ih => erw [repeatEq, i_ih]
def Subtype_ : ∀ {n} {α : TypeVec.{u} n}, (α ⟹ «repeat» n Prop) → TypeVec n
  | _, _, p, Fin2.fz => Subtype fun x => p Fin2.fz x
  | _, _, p, Fin2.fs i => Subtype_ (dropFun p) i
def subtypeVal : ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop), Subtype_ p ⟹ α
  | succ n, _, _, Fin2.fs i => @subtypeVal n _ _ i
  | succ _, _, _, Fin2.fz => Subtype.val
def toSubtype :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop),
      (fun i : Fin2 n => { x // ofRepeat <| p i x }) ⟹ Subtype_ p
  | succ _, _, p, Fin2.fs i, x => toSubtype (dropFun p) i x
  | succ _, _, _, Fin2.fz, x => x
def ofSubtype {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop) :
    Subtype_ p ⟹ fun i : Fin2 n => { x // ofRepeat <| p i x }
  | Fin2.fs i, x => ofSubtype _ i x
  | Fin2.fz,   x => x
def toSubtype' {n} {α : TypeVec.{u} n} (p : α ⊗ α ⟹ «repeat» n Prop) :
    (fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (prod.mk _ x.1 x.2) }) ⟹ Subtype_ p
  | Fin2.fs i, x => toSubtype' (dropFun p) i x
  | Fin2.fz, x => ⟨x.val, cast (by congr) x.property⟩
def ofSubtype' {n} {α : TypeVec.{u} n} (p : α ⊗ α ⟹ «repeat» n Prop) :
    Subtype_ p ⟹ fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (prod.mk _ x.1 x.2) }
  | Fin2.fs i, x => ofSubtype' _ i x
  | Fin2.fz, x => ⟨x.val, cast (by congr) x.property⟩
def diagSub {n} {α : TypeVec.{u} n} : α ⟹ Subtype_ (repeatEq α)
  | Fin2.fs _, x => @diagSub _ (drop α) _ x
  | Fin2.fz, x => ⟨(x, x), rfl⟩
theorem subtypeVal_nil {α : TypeVec.{u} 0} (ps : α ⟹ «repeat» 0 Prop) :
    TypeVec.subtypeVal ps = nilFun :=
  funext <| by rintro ⟨⟩
theorem diag_sub_val {n} {α : TypeVec.{u} n} : subtypeVal (repeatEq α) ⊚ diagSub = prod.diag := by
  ext i x
  induction i with
  | fz => simp only [comp, subtypeVal, repeatEq.eq_2, diagSub, prod.diag]
  | fs _ i_ih => apply @i_ih (drop α)
theorem prod_id : ∀ {n} {α β : TypeVec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) := by
  intros
  ext i a
  induction i with
  | fz => cases a; rfl
  | fs _ i_ih => apply i_ih
theorem append_prod_appendFun {n} {α α' β β' : TypeVec.{u} n} {φ φ' ψ ψ' : Type u}
    {f₀ : α ⟹ α'} {g₀ : β ⟹ β'} {f₁ : φ → φ'} {g₁ : ψ → ψ'} :
    ((f₀ ⊗' g₀) ::: (_root_.Prod.map f₁ g₁)) = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) := by
  ext i a
  cases i
  · cases a
    rfl
  · rfl
end Liftp'
@[simp]
theorem dropFun_diag {α} : dropFun (@prod.diag (n + 1) α) = prod.diag := by
  ext i : 2
  induction i <;> simp [dropFun, *] <;> rfl
@[simp]
theorem dropFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (subtypeVal p) = subtypeVal _ :=
  rfl
@[simp]
theorem lastFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (subtypeVal p) = Subtype.val :=
  rfl
@[simp]
theorem dropFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (toSubtype p) = toSubtype _ := by
  ext i
  induction i <;> simp [dropFun, *] <;> rfl
@[simp]
theorem lastFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (toSubtype p) = _root_.id := by
  ext i : 2
  induction i; simp [dropFun, *]; rfl
@[simp]
theorem dropFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (ofSubtype p) = ofSubtype _ := by
  ext i : 2
  induction i <;> simp [dropFun, *] <;> rfl
@[simp]
theorem lastFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (ofSubtype p) = _root_.id := rfl
@[simp]
theorem dropFun_RelLast' {α : TypeVec n} {β} (R : β → β → Prop) :
    dropFun (RelLast' α R) = repeatEq α :=
  rfl
attribute [simp] drop_append1'
open MvFunctor
@[simp]
theorem dropFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    dropFun (f ⊗' f') = (dropFun f ⊗' dropFun f') := by
  ext i : 2
  induction i <;> simp [dropFun, *] <;> rfl
@[simp]
theorem lastFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    lastFun (f ⊗' f') = Prod.map (lastFun f) (lastFun f') := by
  ext i : 1
  induction i; simp [lastFun, *]; rfl
@[simp]
theorem dropFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    dropFun (@fromAppend1DropLast _ α) = id :=
  rfl
@[simp]
theorem lastFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    lastFun (@fromAppend1DropLast _ α) = _root_.id :=
  rfl
@[simp]
theorem dropFun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id :=
  rfl
@[simp]
theorem prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α ⊗' @TypeVec.id _ β) = id := by
  ext i x : 2
  induction i <;> simp only [TypeVec.prod.map, *, dropFun_id]
  cases x
  · rfl
  · rfl
@[simp]
theorem subtypeVal_diagSub {α : TypeVec n} : subtypeVal (repeatEq α) ⊚ diagSub = prod.diag := by
  ext i x
  induction i with
  | fz => simp [comp, diagSub, subtypeVal, prod.diag]
  | fs _ i_ih =>
    simp only [comp, subtypeVal, diagSub, prod.diag] at *
    apply i_ih
@[simp]
theorem toSubtype_of_subtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) :
    toSubtype p ⊚ ofSubtype p = id := by
  ext i x
  induction i <;> dsimp only [id, toSubtype, comp, ofSubtype] at *
  simp [*]
@[simp]
theorem subtypeVal_toSubtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) :
    subtypeVal p ⊚ toSubtype p = fun _ => Subtype.val := by
  ext i x
  induction i <;> dsimp only [toSubtype, comp, subtypeVal] at *
  simp [*]
@[simp]
theorem toSubtype_of_subtype_assoc
    {α β : TypeVec n} (p : α ⟹ «repeat» n Prop) (f : β ⟹ Subtype_ p) :
    @toSubtype n _ p ⊚ ofSubtype _ ⊚ f = f := by
  rw [← comp_assoc, toSubtype_of_subtype]; simp
@[simp]
theorem toSubtype'_of_subtype' {α : TypeVec n} (r : α ⊗ α ⟹ «repeat» n Prop) :
    toSubtype' r ⊚ ofSubtype' r = id := by
  ext i x
  induction i
  <;> dsimp only [id, toSubtype', comp, ofSubtype'] at *
  <;> simp [Subtype.eta, *]
theorem subtypeVal_toSubtype' {α : TypeVec n} (r : α ⊗ α ⟹ «repeat» n Prop) :
    subtypeVal r ⊚ toSubtype' r = fun i x => prod.mk i x.1.fst x.1.snd := by
  ext i x
  induction i <;> dsimp only [id, toSubtype', comp, subtypeVal, prod.mk] at *
  simp [*]
end TypeVec