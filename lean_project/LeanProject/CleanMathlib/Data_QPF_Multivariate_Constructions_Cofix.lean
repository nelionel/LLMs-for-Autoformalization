import Mathlib.Control.Functor.Multivariate
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Multivariate.M
import Mathlib.Data.QPF.Multivariate.Basic
universe u
open MvFunctor
namespace MvQPF
open TypeVec MvPFunctor
open MvFunctor (LiftP LiftR)
variable {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [q : MvQPF F]
def corecF {α : TypeVec n} {β : Type u} (g : β → F (α.append1 β)) : β → q.P.M α :=
  M.corec _ fun x => repr (g x)
theorem corecF_eq {α : TypeVec n} {β : Type u} (g : β → F (α.append1 β)) (x : β) :
    M.dest q.P (corecF g x) = appendFun id (corecF g) <$$> repr (g x) := by
  rw [corecF, M.dest_corec]
def IsPrecongr {α : TypeVec n} (r : q.P.M α → q.P.M α → Prop) : Prop :=
  ∀ ⦃x y⦄,
    r x y →
      abs (appendFun id (Quot.mk r) <$$> M.dest q.P x) =
        abs (appendFun id (Quot.mk r) <$$> M.dest q.P y)
def Mcongr {α : TypeVec n} (x y : q.P.M α) : Prop :=
  ∃ r, IsPrecongr r ∧ r x y
def Cofix (F : TypeVec (n + 1) → Type u) [MvQPF F] (α : TypeVec n) :=
  Quot (@Mcongr _ F _ α)
instance {α : TypeVec n} [Inhabited q.P.A] [∀ i : Fin2 n, Inhabited (α i)] :
    Inhabited (Cofix F α) :=
  ⟨Quot.mk _ default⟩
def mRepr {α : TypeVec n} : q.P.M α → q.P.M α :=
  corecF (abs ∘ M.dest q.P)
def Cofix.map {α β : TypeVec n} (g : α ⟹ β) : Cofix F α → Cofix F β :=
  Quot.lift (fun x : q.P.M α => Quot.mk Mcongr (g <$$> x))
    (by
      rintro aa₁ aa₂ ⟨r, pr, ra₁a₂⟩; apply Quot.sound
      let r' b₁ b₂ := ∃ a₁ a₂ : q.P.M α, r a₁ a₂ ∧ b₁ = g <$$> a₁ ∧ b₂ = g <$$> a₂
      use r'; constructor
      · show IsPrecongr r'
        rintro b₁ b₂ ⟨a₁, a₂, ra₁a₂, b₁eq, b₂eq⟩
        let u : Quot r → Quot r' :=
          Quot.lift (fun x : q.P.M α => Quot.mk r' (g <$$> x))
            (by
              intro a₁ a₂ ra₁a₂
              apply Quot.sound
              exact ⟨a₁, a₂, ra₁a₂, rfl, rfl⟩)
        have hu : (Quot.mk r' ∘ fun x : q.P.M α => g <$$> x) = u ∘ Quot.mk r := by
          ext x
          rfl
        rw [b₁eq, b₂eq, M.dest_map, M.dest_map, ← q.P.comp_map, ← q.P.comp_map]
        rw [← appendFun_comp, id_comp, hu, ← comp_id g, appendFun_comp]
        rw [q.P.comp_map, q.P.comp_map, abs_map, pr ra₁a₂, ← abs_map]
      show r' (g <$$> aa₁) (g <$$> aa₂); exact ⟨aa₁, aa₂, ra₁a₂, rfl, rfl⟩)
instance Cofix.mvfunctor : MvFunctor (Cofix F) where map := @Cofix.map _ _ _
def Cofix.corec {α : TypeVec n} {β : Type u} (g : β → F (α.append1 β)) : β → Cofix F α := fun x =>
  Quot.mk _ (corecF g x)
def Cofix.dest {α : TypeVec n} : Cofix F α → F (α.append1 (Cofix F α)) :=
  Quot.lift (fun x => appendFun id (Quot.mk Mcongr) <$$> abs (M.dest q.P x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      dsimp
      have : ∀ x y, r x y → Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [appendFun_comp_id, comp_map, ← abs_map, pr rxy, abs_map, ← comp_map,
          ← appendFun_comp_id])
def Cofix.abs {α} : q.P.M α → Cofix F α :=
  Quot.mk _
def Cofix.repr {α} : Cofix F α → q.P.M α :=
  M.corec _ <| q.repr ∘ Cofix.dest
def Cofix.corec'₁ {α : TypeVec n} {β : Type u} (g : ∀ {X}, (β → X) → F (α.append1 X)) (x : β) :
    Cofix F α :=
  Cofix.corec (fun _ => g id) x
def Cofix.corec' {α : TypeVec n} {β : Type u} (g : β → F (α.append1 (Cofix F α ⊕ β))) (x : β) :
    Cofix F α :=
  let f : (α ::: Cofix F α) ⟹ (α ::: (Cofix F α ⊕ β)) := id ::: Sum.inl
  Cofix.corec (Sum.elim (MvFunctor.map f ∘ Cofix.dest) g) (Sum.inr x : Cofix F α ⊕ β)
def Cofix.corec₁ {α : TypeVec n} {β : Type u}
    (g : ∀ {X}, (Cofix F α → X) → (β → X) → β → F (α ::: X)) (x : β) : Cofix F α :=
  Cofix.corec' (fun x => g Sum.inl Sum.inr x) x
theorem Cofix.dest_corec {α : TypeVec n} {β : Type u} (g : β → F (α.append1 β)) (x : β) :
    Cofix.dest (Cofix.corec g x) = appendFun id (Cofix.corec g) <$$> g x := by
  conv =>
    lhs
    rw [Cofix.dest, Cofix.corec]
  dsimp
  rw [corecF_eq, abs_map, abs_repr, ← comp_map, ← appendFun_comp]; rfl
def Cofix.mk {α : TypeVec n} : F (α.append1 <| Cofix F α) → Cofix F α :=
  Cofix.corec fun x => (appendFun id fun i : Cofix F α => Cofix.dest.{u} i) <$$> x
private theorem Cofix.bisim_aux {α : TypeVec n} (r : Cofix F α → Cofix F α → Prop) (h' : ∀ x, r x x)
    (h : ∀ x y, r x y →
      appendFun id (Quot.mk r) <$$> Cofix.dest x = appendFun id (Quot.mk r) <$$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  intro x
  rcases x; clear x; rename M (P F) α => x
  intro y
  rcases y; clear y; rename M (P F) α => y
  intro rxy
  apply Quot.sound
  let r' := fun x y => r (Quot.mk _ x) (Quot.mk _ y)
  have hr' : r' = fun x y => r (Quot.mk _ x) (Quot.mk _ y) := rfl
  have : IsPrecongr r' := by
    intro a b r'ab
    have h₀ :
      appendFun id (Quot.mk r ∘ Quot.mk Mcongr) <$$> MvQPF.abs (M.dest q.P a) =
        appendFun id (Quot.mk r ∘ Quot.mk Mcongr) <$$> MvQPF.abs (M.dest q.P b) := by
      rw [appendFun_comp_id, comp_map, comp_map]; exact h _ _ r'ab
    have h₁ : ∀ u v : q.P.M α, Mcongr u v → Quot.mk r' u = Quot.mk r' v := by
      intro u v cuv
      apply Quot.sound
      dsimp [r', hr']
      rw [Quot.sound cuv]
      apply h'
    let f : Quot r → Quot r' :=
      Quot.lift (Quot.lift (Quot.mk r') h₁)
        (by
          intro c
          apply Quot.inductionOn
            (motive := fun c =>
              ∀b, r c b → Quot.lift (Quot.mk r') h₁ c = Quot.lift (Quot.mk r') h₁ b) c
          clear c
          intro c d
          apply Quot.inductionOn
            (motive := fun d => r (Quot.mk Mcongr c) d →
              Quot.lift (Quot.mk r') h₁ (Quot.mk Mcongr c) = Quot.lift (Quot.mk r') h₁ d) d
          clear d
          intro d rcd; apply Quot.sound; apply rcd)
    have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
    rw [← this, appendFun_comp_id, q.P.comp_map, q.P.comp_map, abs_map, abs_map, abs_map, abs_map,
      h₀]
  exact ⟨r', this, rxy⟩
theorem Cofix.bisim_rel {α : TypeVec n} (r : Cofix F α → Cofix F α → Prop)
    (h : ∀ x y, r x y →
      appendFun id (Quot.mk r) <$$> Cofix.dest x = appendFun id (Quot.mk r) <$$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    cases r'xy with
    | inl h =>
      rw [h]
    | inr r'xy =>
      have : ∀ x y, r x y → r' x y := fun x y h => Or.inr h
      rw [← Quot.factor_mk_eq _ _ this]
      dsimp [r']
      rw [appendFun_comp_id]
      rw [@comp_map _ _ q _ _ _ (appendFun id (Quot.mk r)),
        @comp_map _ _ q _ _ _ (appendFun id (Quot.mk r))]
      rw [h _ _ r'xy]
  right; exact rxy
theorem Cofix.bisim {α : TypeVec n} (r : Cofix F α → Cofix F α → Prop)
    (h : ∀ x y, r x y → LiftR (RelLast α r (i := _)) (Cofix.dest x) (Cofix.dest y)) :
    ∀ x y, r x y → x = y := by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftR_iff (fun a b => RelLast α r a b) (dest x) (dest y)).mp (h x y rxy)
    with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq, dyeq, ← abs_map, ← abs_map, MvPFunctor.map_eq, MvPFunctor.map_eq]
  rw [← split_dropFun_lastFun f₀, ← split_dropFun_lastFun f₁]
  rw [appendFun_comp_splitFun, appendFun_comp_splitFun]
  rw [id_comp, id_comp]
  congr 2 with (i j); cases' i with _ i
  · apply Quot.sound
    apply h' _ j
  · change f₀ _ j = f₁ _ j
    apply h' _ j
open MvFunctor
theorem Cofix.bisim₂ {α : TypeVec n} (r : Cofix F α → Cofix F α → Prop)
    (h : ∀ x y, r x y → LiftR' (RelLast' α r) (Cofix.dest x) (Cofix.dest y)) :
    ∀ x y, r x y → x = y :=
  Cofix.bisim r <| by intros; rw [← LiftR_RelLast_iff]; apply h; assumption
theorem Cofix.bisim' {α : TypeVec n} {β : Type*} (Q : β → Prop) (u v : β → Cofix F α)
    (h : ∀ x, Q x → ∃ a f' f₀ f₁,
      Cofix.dest (u x) = q.abs ⟨a, q.P.appendContents f' f₀⟩ ∧
        Cofix.dest (v x) = q.abs ⟨a, q.P.appendContents f' f₁⟩ ∧
          ∀ i, ∃ x', Q x' ∧ f₀ i = u x' ∧ f₁ i = v x') :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : Cofix F α => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f', f₀, f₁, ux'eq, vx'eq, h'⟩
      rw [liftR_iff]
      refine
        ⟨a, q.P.appendContents f' f₀, q.P.appendContents f' f₁, xeq.symm ▸ ux'eq,
          yeq.symm ▸ vx'eq, ?_⟩
      intro i; cases i
      · apply h'
      · intro j
        apply Eq.refl)
    _ _ ⟨x, Qx, rfl, rfl⟩
theorem Cofix.mk_dest {α : TypeVec n} (x : Cofix F α) : Cofix.mk (Cofix.dest x) = x := by
  apply Cofix.bisim_rel (fun x y : Cofix F α => x = Cofix.mk (Cofix.dest y)) _ _ _ rfl
  dsimp
  intro x y h
  rw [h]
  conv =>
    lhs
    congr
    rfl
    rw [Cofix.mk]
    rw [Cofix.dest_corec]
  rw [← comp_map, ← appendFun_comp, id_comp]
  rw [← comp_map, ← appendFun_comp, id_comp, ← Cofix.mk]
  congr
  apply congrArg
  funext x
  apply Quot.sound
  rfl
theorem Cofix.dest_mk {α : TypeVec n} (x : F (α.append1 <| Cofix F α)) :
    Cofix.dest (Cofix.mk x) = x := by
  have : Cofix.mk ∘ Cofix.dest = @_root_.id (Cofix F α) := funext Cofix.mk_dest
  rw [Cofix.mk, Cofix.dest_corec, ← comp_map, ← Cofix.mk, ← appendFun_comp, this, id_comp,
    appendFun_id_id, MvFunctor.id_map]
theorem Cofix.ext {α : TypeVec n} (x y : Cofix F α) (h : x.dest = y.dest) : x = y := by
  rw [← Cofix.mk_dest x, h, Cofix.mk_dest]
theorem Cofix.ext_mk {α : TypeVec n} (x y : F (α ::: Cofix F α)) (h : Cofix.mk x = Cofix.mk y) :
    x = y := by rw [← Cofix.dest_mk x, h, Cofix.dest_mk]
section LiftRMap
theorem liftR_map {α β : TypeVec n} {F' : TypeVec n → Type u} [MvFunctor F'] [LawfulMvFunctor F']
    (R : β ⊗ β ⟹ «repeat» n Prop) (x : F' α) (f g : α ⟹ β) (h : α ⟹ Subtype_ R)
    (hh : subtypeVal _ ⊚ h = (f ⊗' g) ⊚ prod.diag) : LiftR' R (f <$$> x) (g <$$> x) := by
  rw [LiftR_def]
  exists h <$$> x
  rw [MvFunctor.map_map, comp_assoc, hh, ← comp_assoc, fst_prod_mk, comp_assoc, fst_diag]
  rw [MvFunctor.map_map, comp_assoc, hh, ← comp_assoc, snd_prod_mk, comp_assoc, snd_diag]
  dsimp [LiftR']; constructor <;> rfl
open Function
theorem liftR_map_last [lawful : LawfulMvFunctor F]
    {α : TypeVec n} {ι ι'} (R : ι' → ι' → Prop)
    (x : F (α ::: ι)) (f g : ι → ι') (hh : ∀ x : ι, R (f x) (g x)) :
    LiftR' (RelLast' _ R) ((id ::: f) <$$> x) ((id ::: g) <$$> x) :=
  let h : ι → { x : ι' × ι' // uncurry R x } := fun x => ⟨(f x, g x), hh x⟩
  let b : (α ::: ι) ⟹ _ := @diagSub n α ::: h
  let c :
    (Subtype_ α.repeatEq ::: { x // uncurry R x }) ⟹
      ((fun i : Fin2 n => { x // ofRepeat (α.RelLast' R i.fs x) }) ::: Subtype (uncurry R)) :=
    ofSubtype _ ::: id
  have hh :
    subtypeVal _ ⊚ toSubtype _ ⊚ fromAppend1DropLast ⊚ c ⊚ b =
      ((id ::: f) ⊗' (id ::: g)) ⊚ prod.diag := by
    dsimp [b]
    apply eq_of_drop_last_eq
    · dsimp
      simp only [prod_map_id, dropFun_prod, dropFun_appendFun, dropFun_diag, TypeVec.id_comp,
        dropFun_toSubtype]
      erw [toSubtype_of_subtype_assoc, TypeVec.id_comp]
      clear liftR_map_last q lawful F x R f g hh h b c
      ext (i x) : 2
      induction i with
      | fz => rfl
      | fs _ ih =>
        apply ih
    simp only [lastFun_from_append1_drop_last, lastFun_toSubtype, lastFun_appendFun,
      lastFun_subtypeVal, Function.id_comp, lastFun_comp, lastFun_prod]
    ext1
    rfl
  liftR_map _ _ _ _ (toSubtype _ ⊚ fromAppend1DropLast ⊚ c ⊚ b) hh
theorem liftR_map_last' [LawfulMvFunctor F] {α : TypeVec n} {ι} (R : ι → ι → Prop) (x : F (α ::: ι))
    (f : ι → ι) (hh : ∀ x : ι, R (f x) x) : LiftR' (RelLast' _ R) ((id ::: f) <$$> x) x := by
  have := liftR_map_last R x f id hh
  rwa [appendFun_id_id, MvFunctor.id_map] at this
end LiftRMap
variable {F : TypeVec (n + 1) → Type u} [q : MvQPF F]
theorem Cofix.abs_repr {α} (x : Cofix F α) : Quot.mk _ (Cofix.repr x) = x := by
  let R := fun x y : Cofix F α => abs (repr y) = x
  refine Cofix.bisim₂ R ?_ _ _ rfl
  clear x
  rintro x y h
  subst h
  dsimp [Cofix.dest, Cofix.abs]
  induction y using Quot.ind
  simp only [Cofix.repr, M.dest_corec, abs_map, MvQPF.abs_repr, Function.comp]
  conv => congr; rfl; rw [Cofix.dest]
  rw [MvFunctor.map_map, MvFunctor.map_map, ← appendFun_comp_id, ← appendFun_comp_id]
  apply liftR_map_last
  intros
  rfl
end MvQPF
namespace Mathlib.Tactic.MvBisim
open Lean Expr Elab Term Tactic Meta Qq
syntax "mv_bisim" (ppSpace colGt term) (" with" (ppSpace colGt binderIdent)+)? : tactic
elab_rules : tactic
  | `(tactic| mv_bisim $e $[ with $ids:binderIdent*]?) => do
    let ids : TSyntaxArray `Lean.binderIdent := ids.getD #[]
    let idsn (n : ℕ) : Name :=
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => n.getId
        | `(binderIdent| _) => `_
        | _ => unreachable!
      | none => `_
    let idss (n : ℕ) : TacticM (TSyntax `rcasesPat) := do
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => `(rcasesPat| $n)
        | `(binderIdent| _%$b) => `(rcasesPat| _%$b)
        | _ => unreachable!
      | none => `(rcasesPat| _)
    withMainContext do
      let e ← Tactic.elabTerm e none
      let f ← liftMetaTacticAux fun g => do
        let (#[fv], g) ← g.generalize #[{ expr := e }] | unreachable!
        return (mkFVar fv, [g])
      withMainContext do
        let some (t, l, r) ← matchEq? (← getMainTarget) | throwError "goal is not an equality"
        let ex ←
          withLocalDecl (idsn 1) .default t fun v₀ =>
            withLocalDecl (idsn 2) .default t fun v₁ => do
              let x₀ ← mkEq v₀ l
              let x₁ ← mkEq v₁ r
              let xx ← mkAppM ``And #[x₀, x₁]
              let ex₁ ← mkLambdaFVars #[f] xx
              let ex₂ ← mkAppM ``Exists #[ex₁]
              mkLambdaFVars #[v₀, v₁] ex₂
        let R ← liftMetaTacticAux fun g => do
          let g₁ ← g.define (idsn 0) (← mkArrow t (← mkArrow t (mkSort .zero))) ex
          let (Rv, g₂) ← g₁.intro1P
          return (mkFVar Rv, [g₂])
        withMainContext do
          ids[0]?.forM fun s => addLocalVarInfoForBinderIdent R s
          let sR ← exprToSyntax R
          evalTactic <| ← `(tactic|
            refine MvQPF.Cofix.bisim₂ $sR ?_ _ _ ⟨_, rfl, rfl⟩;
            rintro $(← idss 1) $(← idss 2) ⟨$(← idss 3), $(← idss 4), $(← idss 5)⟩)
          liftMetaTactic fun g => return [← g.clear f.fvarId!]
    for n in [6 : ids.size] do
      let name := ids[n]!
      logWarningAt name m!"unused name: {name}"
end Mathlib.Tactic.MvBisim
namespace MvQPF
open TypeVec MvPFunctor
open MvFunctor (LiftP LiftR)
variable {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [q : MvQPF F]
theorem corec_roll {α : TypeVec n} {X Y} {x₀ : X} (f : X → Y) (g : Y → F (α ::: X)) :
    Cofix.corec (g ∘ f) x₀ = Cofix.corec (MvFunctor.map (id ::: f) ∘ g) (f x₀) := by
  mv_bisim x₀ with R a b x Ha Hb
  rw [Ha, Hb, Cofix.dest_corec, Cofix.dest_corec, Function.comp_apply, Function.comp_apply]
  rw [MvFunctor.map_map, ← appendFun_comp_id]
  refine liftR_map_last _ _ _ _ ?_
  intro a; refine ⟨a, rfl, rfl⟩
theorem Cofix.dest_corec' {α : TypeVec.{u} n} {β : Type u}
    (g : β → F (α.append1 (Cofix F α ⊕ β))) (x : β) :
    Cofix.dest (Cofix.corec' g x) =
      appendFun id (Sum.elim _root_.id (Cofix.corec' g)) <$$> g x := by
  rw [Cofix.corec', Cofix.dest_corec]; dsimp
  congr!; ext (i | i) <;> erw [corec_roll] <;> dsimp [Cofix.corec']
  · mv_bisim i with R a b x Ha Hb
    rw [Ha, Hb, Cofix.dest_corec]
    dsimp [Function.comp_def]
    repeat rw [MvFunctor.map_map, ← appendFun_comp_id]
    apply liftR_map_last'
    dsimp [Function.comp_def]
    intros
    exact ⟨_, rfl, rfl⟩
  · congr with y
    erw [appendFun_id_id]
    simp [MvFunctor.id_map, Sum.elim]
theorem Cofix.dest_corec₁ {α : TypeVec n} {β : Type u}
    (g : ∀ {X}, (Cofix F α → X) → (β → X) → β → F (α.append1 X)) (x : β)
    (h : ∀ (X Y) (f : Cofix F α → X) (f' : β → X) (k : X → Y),
      g (k ∘ f) (k ∘ f') x = (id ::: k) <$$> g f f' x) :
    Cofix.dest (Cofix.corec₁ (@g) x) = g id (Cofix.corec₁ @g) x := by
  rw [Cofix.corec₁, Cofix.dest_corec', ← h]; rfl
instance mvqpfCofix : MvQPF (Cofix F) where
  P         := q.P.mp
  abs       := Quot.mk Mcongr
  repr      := Cofix.repr
  abs_repr  := Cofix.abs_repr
  abs_map   := by intros; rfl
end MvQPF