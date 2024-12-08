import Mathlib.Computability.Halting
import Mathlib.Computability.TuringMachine
import Mathlib.Data.Num.Lemmas
import Mathlib.Tactic.DeriveFintype
open Mathlib (Vector)
open Function (update)
open Relation
namespace Turing
namespace ToPartrec
inductive Code
  | zero'
  | succ
  | tail
  | cons : Code → Code → Code
  | comp : Code → Code → Code
  | case : Code → Code → Code
  | fix : Code → Code
  deriving DecidableEq, Inhabited
def Code.eval : Code → List ℕ →. List ℕ
  | Code.zero' => fun v => pure (0 :: v)
  | Code.succ => fun v => pure [v.headI.succ]
  | Code.tail => fun v => pure v.tail
  | Code.cons f fs => fun v => do
    let n ← Code.eval f v
    let ns ← Code.eval fs v
    pure (n.headI :: ns)
  | Code.comp f g => fun v => g.eval v >>= f.eval
  | Code.case f g => fun v => v.headI.rec (f.eval v.tail) fun y _ => g.eval (y::v.tail)
  | Code.fix f =>
    PFun.fix fun v => (f.eval v).map fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail
namespace Code
@[simp]
theorem zero'_eval : zero'.eval = fun v => pure (0 :: v) := by simp [eval]
@[simp]
theorem succ_eval : succ.eval = fun v => pure [v.headI.succ] := by simp [eval]
@[simp]
theorem tail_eval : tail.eval = fun v => pure v.tail := by simp [eval]
@[simp]
theorem cons_eval (f fs) : (cons f fs).eval = fun v => do {
    let n ← Code.eval f v
    let ns ← Code.eval fs v
    pure (n.headI :: ns) } := by simp [eval]
@[simp]
theorem comp_eval (f g) : (comp f g).eval = fun v => g.eval v >>= f.eval := by simp [eval]
@[simp]
theorem case_eval (f g) :
    (case f g).eval = fun v => v.headI.rec (f.eval v.tail) fun y _ => g.eval (y::v.tail) := by
  simp [eval]
@[simp]
theorem fix_eval (f) : (fix f).eval =
    PFun.fix fun v => (f.eval v).map fun v =>
      if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail := by
  simp [eval]
def nil : Code :=
  tail.comp succ
@[simp]
theorem nil_eval (v) : nil.eval v = pure [] := by simp [nil]
def id : Code :=
  tail.comp zero'
@[simp]
theorem id_eval (v) : id.eval v = pure v := by simp [id]
def head : Code :=
  cons id nil
@[simp]
theorem head_eval (v) : head.eval v = pure [v.headI] := by simp [head]
def zero : Code :=
  cons zero' nil
@[simp]
theorem zero_eval (v) : zero.eval v = pure [0] := by simp [zero]
def pred : Code :=
  case zero head
@[simp]
theorem pred_eval (v) : pred.eval v = pure [v.headI.pred] := by
  simp [pred]; cases v.headI <;> simp
def rfind (f : Code) : Code :=
  comp pred <| comp (fix <| cons f <| cons succ tail) zero'
def prec (f g : Code) : Code :=
  let G :=
    cons tail <|
      cons succ <|
        cons (comp pred tail) <|
          cons (comp g <| cons id <| comp tail tail) <| comp tail <| comp tail tail
  let F := case id <| comp (comp (comp tail tail) (fix G)) zero'
  cons (comp F (cons head <| cons (comp f tail) tail)) nil
attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some
theorem exists_code.comp {m n} {f : Mathlib.Vector ℕ n →. ℕ} {g : Fin n → Mathlib.Vector ℕ m →. ℕ}
    (hf : ∃ c : Code, ∀ v : Mathlib.Vector ℕ n, c.eval v.1 = pure <$> f v)
    (hg : ∀ i, ∃ c : Code, ∀ v : Mathlib.Vector ℕ m, c.eval v.1 = pure <$> g i v) :
    ∃ c : Code, ∀ v : Mathlib.Vector ℕ m,
      c.eval v.1 = pure <$> ((Mathlib.Vector.mOfFn fun i => g i v) >>= f) := by
  rsuffices ⟨cg, hg⟩ :
    ∃ c : Code, ∀ v : Mathlib.Vector ℕ m,
      c.eval v.1 = Subtype.val <$> Mathlib.Vector.mOfFn fun i => g i v
  · obtain ⟨cf, hf⟩ := hf
    exact
      ⟨cf.comp cg, fun v => by
        simp [hg, hf, map_bind, seq_bind_eq, Function.comp_def]
        rfl⟩
  clear hf f; induction' n with n IH
  · exact ⟨nil, fun v => by simp [Vector.mOfFn, Bind.bind]; rfl⟩
  · obtain ⟨cg, hg₁⟩ := hg 0
    obtain ⟨cl, hl⟩ := IH fun i => hg i.succ
    exact
      ⟨cons cg cl, fun v => by
        simp [Vector.mOfFn, hg₁, map_bind, seq_bind_eq, bind_assoc, (· ∘ ·), hl]
        rfl⟩
theorem exists_code {n} {f : Mathlib.Vector ℕ n →. ℕ} (hf : Nat.Partrec' f) :
    ∃ c : Code, ∀ v : Mathlib.Vector ℕ n, c.eval v.1 = pure <$> f v := by
  induction hf with
  | prim hf =>
    induction hf with
    | zero => exact ⟨zero', fun ⟨[], _⟩ => rfl⟩
    | succ => exact ⟨succ, fun ⟨[v], _⟩ => rfl⟩
    | get i =>
      refine Fin.succRec (fun n => ?_) (fun n i IH => ?_) i
      · exact ⟨head, fun ⟨List.cons a as, _⟩ => by simp [Bind.bind]; rfl⟩
      · obtain ⟨c, h⟩ := IH
        exact ⟨c.comp tail, fun v => by simpa [← Vector.get_tail, Bind.bind] using h v.tail⟩
    | comp g hf hg IHf IHg =>
      simpa [Part.bind_eq_bind] using exists_code.comp IHf IHg
    | @prec n f g _ _ IHf IHg =>
      obtain ⟨cf, hf⟩ := IHf
      obtain ⟨cg, hg⟩ := IHg
      simp only [Part.map_eq_map, Part.map_some, PFun.coe_val] at hf hg
      refine ⟨prec cf cg, fun v => ?_⟩
      rw [← v.cons_head_tail]
      specialize hf v.tail
      replace hg := fun a b => hg (a ::ᵥ b ::ᵥ v.tail)
      simp only [Vector.cons_val, Vector.tail_val] at hf hg
      simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, Vector.tail_cons,
        Vector.head_cons, PFun.coe_val, Vector.tail_val]
      simp only [← Part.pure_eq_some] at hf hg ⊢
      induction' v.head with n _ <;>
        simp [prec, hf, Part.bind_assoc, ← Part.bind_some_eq_map, Part.bind_some,
          show ∀ x, pure x = [x] from fun _ => rfl, Bind.bind, Functor.map]
      suffices ∀ a b, a + b = n →
        (n.succ :: 0 ::
          g (n ::ᵥ Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) n ::ᵥ v.tail) ::
              v.val.tail : List ℕ) ∈
          PFun.fix
            (fun v : List ℕ => Part.bind (cg.eval (v.headI :: v.tail.tail))
              (fun x => Part.some (if v.tail.headI = 0
                then Sum.inl
                  (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail : List ℕ)
                else Sum.inr
                  (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail))))
            (a :: b :: Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) a :: v.val.tail) by
        erw [Part.eq_some_iff.2 (this 0 n (zero_add n))]
        simp only [List.headI, Part.bind_some, List.tail_cons]
      intro a b e
      induction' b with b IH generalizing a
      · refine PFun.mem_fix_iff.2 (Or.inl <| Part.eq_some_iff.1 ?_)
        simp only [hg, ← e, Part.bind_some, List.tail_cons, pure]
        rfl
      · refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH (a + 1) (by rwa [add_right_comm])⟩)
        simp only [hg, eval, Part.bind_some, Nat.rec_add_one, List.tail_nil, List.tail_cons, pure]
        exact Part.mem_some_iff.2 rfl
  | comp g _ _ IHf IHg => exact exists_code.comp IHf IHg
  | @rfind n f _ IHf =>
    obtain ⟨cf, hf⟩ := IHf; refine ⟨rfind cf, fun v => ?_⟩
    replace hf := fun a => hf (a ::ᵥ v)
    simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val,
      show ∀ x, pure x = [x] from fun _ => rfl] at hf ⊢
    refine Part.ext fun x => ?_
    simp only [rfind, Part.bind_eq_bind, Part.pure_eq_some, Part.map_eq_map, Part.bind_some,
      exists_prop, cons_eval, comp_eval, fix_eval, tail_eval, succ_eval, zero'_eval,
      List.headI_nil, List.headI_cons, pred_eval, Part.map_some, false_eq_decide_iff,
      Part.mem_bind_iff, List.length, Part.mem_map_iff, Nat.mem_rfind, List.tail_nil,
      List.tail_cons, true_eq_decide_iff, Part.mem_some_iff, Part.map_bind]
    constructor
    · rintro ⟨v', h1, rfl⟩
      suffices ∀ v₁ : List ℕ, v' ∈ PFun.fix
        (fun v => (cf.eval v).bind fun y => Part.some <|
          if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
            else Sum.inr (v.headI.succ :: v.tail)) v₁ →
        ∀ n, (v₁ = n :: v.val) → (∀ m < n, ¬f (m ::ᵥ v) = 0) →
          ∃ a : ℕ,
            (f (a ::ᵥ v) = 0 ∧ ∀ {m : ℕ}, m < a → ¬f (m ::ᵥ v) = 0) ∧ [a] = [v'.headI.pred]
        by exact this _ h1 0 rfl (by rintro _ ⟨⟩)
      clear h1
      intro v₀ h1
      refine PFun.fixInduction h1 fun v₁ h2 IH => ?_
      clear h1
      rintro n rfl hm
      have := PFun.mem_fix_iff.1 h2
      simp only [hf, Part.bind_some] at this
      split_ifs at this with h
      · simp only [List.headI_nil, List.headI_cons, exists_false, or_false, Part.mem_some_iff,
          List.tail_cons, false_and, Sum.inl.injEq, reduceCtorEq] at this
        subst this
        exact ⟨_, ⟨h, @(hm)⟩, rfl⟩
      · refine IH (n.succ::v.val) (by simp_all) _ rfl fun m h' => ?_
        obtain h | rfl := Nat.lt_succ_iff_lt_or_eq.1 h'
        exacts [hm _ h, h]
    · rintro ⟨n, ⟨hn, hm⟩, rfl⟩
      refine ⟨n.succ::v.1, ?_, rfl⟩
      have : (n.succ::v.1 : List ℕ) ∈
        PFun.fix (fun v =>
          (cf.eval v).bind fun y =>
            Part.some <|
              if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
                else Sum.inr (v.headI.succ :: v.tail))
            (n::v.val) :=
        PFun.mem_fix_iff.2 (Or.inl (by simp [hf, hn]))
      generalize (n.succ :: v.1 : List ℕ) = w at this ⊢
      clear hn
      induction n with
      | zero => exact this
      | succ n IH =>
        refine IH (fun {m} h' => hm (Nat.lt_succ_of_lt h'))
          (PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, this⟩))
        simp only [hf, hm n.lt_succ_self, Part.bind_some, List.headI, eq_self_iff_true, if_false,
          Part.mem_some_iff, and_self_iff, List.tail_cons]
end Code
inductive Cont
  | halt
  | cons₁ : Code → List ℕ → Cont → Cont
  | cons₂ : List ℕ → Cont → Cont
  | comp : Code → Cont → Cont
  | fix : Code → Cont → Cont
  deriving Inhabited
def Cont.eval : Cont → List ℕ →. List ℕ
  | Cont.halt => pure
  | Cont.cons₁ fs as k => fun v => do
    let ns ← Code.eval fs as
    Cont.eval k (v.headI :: ns)
  | Cont.cons₂ ns k => fun v => Cont.eval k (ns.headI :: v)
  | Cont.comp f k => fun v => Code.eval f v >>= Cont.eval k
  | Cont.fix f k => fun v => if v.headI = 0 then k.eval v.tail else f.fix.eval v.tail >>= k.eval
inductive Cfg
  | halt : List ℕ → Cfg
  | ret : Cont → List ℕ → Cfg
  deriving Inhabited
def stepNormal : Code → Cont → List ℕ → Cfg
  | Code.zero' => fun k v => Cfg.ret k (0::v)
  | Code.succ => fun k v => Cfg.ret k [v.headI.succ]
  | Code.tail => fun k v => Cfg.ret k v.tail
  | Code.cons f fs => fun k v => stepNormal f (Cont.cons₁ fs v k) v
  | Code.comp f g => fun k v => stepNormal g (Cont.comp f k) v
  | Code.case f g => fun k v =>
    v.headI.rec (stepNormal f k v.tail) fun y _ => stepNormal g k (y::v.tail)
  | Code.fix f => fun k v => stepNormal f (Cont.fix f k) v
def stepRet : Cont → List ℕ → Cfg
  | Cont.halt, v => Cfg.halt v
  | Cont.cons₁ fs as k, v => stepNormal fs (Cont.cons₂ v k) as
  | Cont.cons₂ ns k, v => stepRet k (ns.headI :: v)
  | Cont.comp f k, v => stepNormal f k v
  | Cont.fix f k, v => if v.headI = 0 then stepRet k v.tail else stepNormal f (Cont.fix f k) v.tail
def step : Cfg → Option Cfg
  | Cfg.halt _ => none
  | Cfg.ret k v => some (stepRet k v)
def Cont.then : Cont → Cont → Cont
  | Cont.halt => fun k' => k'
  | Cont.cons₁ fs as k => fun k' => Cont.cons₁ fs as (k.then k')
  | Cont.cons₂ ns k => fun k' => Cont.cons₂ ns (k.then k')
  | Cont.comp f k => fun k' => Cont.comp f (k.then k')
  | Cont.fix f k => fun k' => Cont.fix f (k.then k')
theorem Cont.then_eval {k k' : Cont} {v} : (k.then k').eval v = k.eval v >>= k'.eval := by
  induction k generalizing v with
  | halt => simp only [Cont.eval, Cont.then, pure_bind]
  | cons₁ => simp only [Cont.eval, bind_assoc, *]
  | cons₂ => simp only [Cont.eval, *]
  | comp _ _ k_ih => simp only [Cont.eval, bind_assoc, ← k_ih]
  | fix _ _ k_ih =>
    simp only [Cont.eval, *]
    split_ifs <;> [rfl; simp only [← k_ih, bind_assoc]]
def Cfg.then : Cfg → Cont → Cfg
  | Cfg.halt v => fun k' => stepRet k' v
  | Cfg.ret k v => fun k' => Cfg.ret (k.then k') v
theorem stepNormal_then (c) (k k' : Cont) (v) :
    stepNormal c (k.then k') v = (stepNormal c k v).then k' := by
  induction c generalizing k v with simp only [Cont.then, stepNormal, *]
  | cons c c' ih _ => rw [← ih, Cont.then]
  | comp c c' _ ih' => rw [← ih', Cont.then]
  | case => cases v.headI <;> simp only [Nat.rec_zero]
  | fix c ih => rw [← ih, Cont.then]
  | _ => simp only [Cfg.then]
theorem stepRet_then {k k' : Cont} {v} : stepRet (k.then k') v = (stepRet k v).then k' := by
  induction k generalizing v with simp only [Cont.then, stepRet, *]
  | cons₁ =>
    rw [← stepNormal_then]
    rfl
  | comp =>
    rw [← stepNormal_then]
  | fix _ _ k_ih =>
    split_ifs
    · rw [← k_ih]
    · rw [← stepNormal_then]
      rfl
  | _ => simp only [Cfg.then]
def Code.Ok (c : Code) :=
  ∀ k v, Turing.eval step (stepNormal c k v) =
    Code.eval c v >>= fun v => Turing.eval step (Cfg.ret k v)
theorem Code.Ok.zero {c} (h : Code.Ok c) {v} :
    Turing.eval step (stepNormal c Cont.halt v) = Cfg.halt <$> Code.eval c v := by
  rw [h, ← bind_pure_comp]; congr; funext v
  exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.single rfl, rfl⟩)
theorem stepNormal.is_ret (c k v) : ∃ k' v', stepNormal c k v = Cfg.ret k' v' := by
  induction c generalizing k v with
  | cons _f fs IHf _IHfs => apply IHf
  | comp f _g _IHf IHg => apply IHg
  | case f g IHf IHg =>
    rw [stepNormal]
    simp only []
    cases v.headI <;> [apply IHf; apply IHg]
  | fix f IHf => apply IHf
  | _ => exact ⟨_, _, rfl⟩
theorem cont_eval_fix {f k v} (fok : Code.Ok f) :
    Turing.eval step (stepNormal f (Cont.fix f k) v) =
      f.fix.eval v >>= fun v => Turing.eval step (Cfg.ret k v) := by
  refine Part.ext fun x => ?_
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · suffices ∀ c, x ∈ eval step c → ∀ v c', c = Cfg.then c' (Cont.fix f k) →
      Reaches step (stepNormal f Cont.halt v) c' →
        ∃ v₁ ∈ f.eval v, ∃ v₂ ∈ if List.headI v₁ = 0 then pure v₁.tail else f.fix.eval v₁.tail,
          x ∈ eval step (Cfg.ret k v₂) by
      intro h
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (stepNormal_then _ Cont.halt _ _) ReflTransGen.refl
      refine ⟨v₂, PFun.mem_fix_iff.2 ?_, h₃⟩
      simp only [Part.eq_some_iff.2 hv₁, Part.map_some]
      split_ifs at hv₂ ⊢
      · rw [Part.mem_some_iff.1 hv₂]
        exact Or.inl (Part.mem_some _)
      · exact Or.inr ⟨_, Part.mem_some _, hv₂⟩
    refine fun c he => evalInduction he fun y h IH => ?_
    rintro v (⟨v'⟩ | ⟨k', v'⟩) rfl hr <;> rw [Cfg.then] at h IH <;> simp only [] at h IH
    · have := mem_eval.2 ⟨hr, rfl⟩
      rw [fok, Part.bind_eq_bind, Part.mem_bind_iff] at this
      obtain ⟨v'', h₁, h₂⟩ := this
      rw [reaches_eval] at h₂
      swap
      · exact ReflTransGen.single rfl
      cases Part.mem_unique h₂ (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
      refine ⟨v', h₁, ?_⟩
      rw [stepRet] at h
      revert h
      by_cases he : v'.headI = 0 <;> simp only [exists_prop, if_pos, if_false, he] <;> intro h
      · refine ⟨_, Part.mem_some _, ?_⟩
        rw [reaches_eval]
        · exact h
        exact ReflTransGen.single rfl
      · obtain ⟨k₀, v₀, e₀⟩ := stepNormal.is_ret f Cont.halt v'.tail
        have e₁ := stepNormal_then f Cont.halt (Cont.fix f k) v'.tail
        rw [e₀, Cont.then, Cfg.then] at e₁
        simp only [] at e₁
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (stepRet (k₀.then (Cont.fix f k)) v₀) (by rw [stepRet, if_neg he, e₁]; rfl)
            v'.tail _ stepRet_then (by apply ReflTransGen.single; rw [e₀]; rfl)
        refine ⟨_, PFun.mem_fix_iff.2 ?_, h₃⟩
        simp only [Part.eq_some_iff.2 hv₁, Part.map_some, Part.mem_some_iff]
        split_ifs at hv₂ ⊢ <;> [exact Or.inl (congr_arg Sum.inl (Part.mem_some_iff.1 hv₂));
          exact Or.inr ⟨_, rfl, hv₂⟩]
    · exact IH _ rfl _ _ stepRet_then (ReflTransGen.tail hr rfl)
  · rintro ⟨v', he, hr⟩
    rw [reaches_eval] at hr
    swap
    · exact ReflTransGen.single rfl
    refine PFun.fixInduction he fun v (he : v' ∈ f.fix.eval v) IH => ?_
    rw [fok, Part.bind_eq_bind, Part.mem_bind_iff]
    obtain he | ⟨v'', he₁', _⟩ := PFun.mem_fix_iff.1 he
    · obtain ⟨v', he₁, he₂⟩ := (Part.mem_map_iff _).1 he
      split_ifs at he₂ with h; cases he₂
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rwa [stepRet, if_pos h]
    · obtain ⟨v₁, he₁, he₂⟩ := (Part.mem_map_iff _).1 he₁'
      split_ifs at he₂ with h; cases he₂
      clear he₁'
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rw [stepRet, if_neg h]
      exact IH v₁.tail ((Part.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩)
theorem code_is_ok (c) : Code.Ok c := by
  induction c with (intro k v; rw [stepNormal])
  | cons f fs IHf IHfs =>
    rw [Code.eval, IHf]
    simp only [bind_assoc, Cont.eval, pure_bind]; congr; funext v
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet, IHfs]; congr; funext v'
    refine Eq.trans (b := eval step (stepRet (Cont.cons₂ v k) v')) ?_ (Eq.symm ?_) <;>
      exact reaches_eval (ReflTransGen.single rfl)
  | comp f g IHf IHg =>
    rw [Code.eval, IHg]
    simp only [bind_assoc, Cont.eval, pure_bind]; congr; funext v
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet, IHf]
  | case f g IHf IHg =>
    simp only [Code.eval]
    cases v.headI <;> simp only [Nat.rec_zero, Part.bind_eq_bind] <;> [apply IHf; apply IHg]
  | fix f IHf => rw [cont_eval_fix IHf]
  | _ => simp only [Code.eval, pure_bind]
theorem stepNormal_eval (c v) : eval step (stepNormal c Cont.halt v) = Cfg.halt <$> c.eval v :=
  (code_is_ok c).zero
theorem stepRet_eval {k v} : eval step (stepRet k v) = Cfg.halt <$> k.eval v := by
  induction k generalizing v with
  | halt =>
    simp only [mem_eval, Cont.eval, map_pure]
    exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
  | cons₁ fs as k IH =>
    rw [Cont.eval, stepRet, code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet, IH, bind_pure_comp]
  | cons₂ ns k IH => rw [Cont.eval, stepRet]; exact IH
  | comp f k IH =>
    rw [Cont.eval, stepRet, code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [IH, bind_pure_comp]
  | fix f k IH =>
    rw [Cont.eval, stepRet]; simp only [bind_pure_comp]
    split_ifs; · exact IH
    simp only [← bind_pure_comp, bind_assoc, cont_eval_fix (code_is_ok _)]
    congr; funext; rw [bind_pure_comp, ← IH]
    exact reaches_eval (ReflTransGen.single rfl)
end ToPartrec
namespace PartrecToTM2
section
open ToPartrec
inductive Γ'
  | consₗ
  | cons
  | bit0
  | bit1
  deriving DecidableEq, Inhabited, Fintype
inductive K'
  | main
  | rev
  | aux
  | stack
  deriving DecidableEq, Inhabited
open K'
inductive Cont'
  | halt
  | cons₁ : Code → Cont' → Cont'
  | cons₂ : Cont' → Cont'
  | comp : Code → Cont' → Cont'
  | fix : Code → Cont' → Cont'
  deriving DecidableEq, Inhabited
inductive Λ'
  | move (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
  | clear (p : Γ' → Bool) (k : K') (q : Λ')
  | copy (q : Λ')
  | push (k : K') (s : Option Γ' → Option Γ') (q : Λ')
  | read (f : Option Γ' → Λ')
  | succ (q : Λ')
  | pred (q₁ q₂ : Λ')
  | ret (k : Cont')
compile_inductive% Code
compile_inductive% Cont'
compile_inductive% K'
compile_inductive% Λ'
instance Λ'.instInhabited : Inhabited Λ' :=
  ⟨Λ'.ret Cont'.halt⟩
instance Λ'.instDecidableEq : DecidableEq Λ' := fun a b => by
  induction a generalizing b <;> cases b <;> first
    | apply Decidable.isFalse; rintro ⟨⟨⟩⟩; done
    | exact decidable_of_iff' _ (by simp [funext_iff]; rfl)
def Stmt' :=
  TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited
def Cfg' :=
  TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited
open TM2.Stmt
@[simp]
def natEnd : Γ' → Bool
  | Γ'.consₗ => true
  | Γ'.cons => true
  | _ => false
attribute [nolint simpNF] natEnd.eq_3
@[simp]
def pop' (k : K') : Stmt' → Stmt' :=
  pop k fun _ v => v
@[simp]
def peek' (k : K') : Stmt' → Stmt' :=
  peek k fun _ v => v
@[simp]
def push' (k : K') : Stmt' → Stmt' :=
  push k fun x => x.iget
def unrev :=
  Λ'.move (fun _ => false) rev main
def moveExcl (p k₁ k₂ q) :=
  Λ'.move p k₁ k₂ <| Λ'.push k₁ id q
def move₂ (p k₁ k₂ q) :=
  moveExcl p k₁ rev <| Λ'.move (fun _ => false) rev k₂ q
def head (k : K') (q : Λ') : Λ' :=
  Λ'.move natEnd k rev <|
    (Λ'.push rev fun _ => some Γ'.cons) <|
      Λ'.read fun s =>
        (if s = some Γ'.consₗ then id else Λ'.clear (fun x => x = Γ'.consₗ) k) <| unrev q
@[simp]
def trNormal : Code → Cont' → Λ'
  | Code.zero', k => (Λ'.push main fun _ => some Γ'.cons) <| Λ'.ret k
  | Code.succ, k => head main <| Λ'.succ <| Λ'.ret k
  | Code.tail, k => Λ'.clear natEnd main <| Λ'.ret k
  | Code.cons f fs, k =>
    (Λ'.push stack fun _ => some Γ'.consₗ) <|
      Λ'.move (fun _ => false) main rev <| Λ'.copy <| trNormal f (Cont'.cons₁ fs k)
  | Code.comp f g, k => trNormal g (Cont'.comp f k)
  | Code.case f g, k => Λ'.pred (trNormal f k) (trNormal g k)
  | Code.fix f, k => trNormal f (Cont'.fix f k)
def tr : Λ' → Stmt'
  | Λ'.move p k₁ k₂ q =>
    pop' k₁ <|
      branch (fun s => s.elim true p) (goto fun _ => q)
        (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)
  | Λ'.push k f q =>
    branch (fun s => (f s).isSome) ((push k fun s => (f s).iget) <| goto fun _ => q)
      (goto fun _ => q)
  | Λ'.read q => goto q
  | Λ'.clear p k q =>
    pop' k <| branch (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)
  | Λ'.copy q =>
    pop' rev <|
      branch Option.isSome (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)
  | Λ'.succ q =>
    pop' main <|
      branch (fun s => s = some Γ'.bit1) ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q) <|
        branch (fun s => s = some Γ'.cons)
          ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
          ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
  | Λ'.pred q₁ q₂ =>
    pop' main <|
      branch (fun s => s = some Γ'.bit0)
          ((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂) <|
        branch (fun s => natEnd s.iget) (goto fun _ => q₁)
          (peek' main <|
            branch (fun s => natEnd s.iget) (goto fun _ => unrev q₂)
              ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))
  | Λ'.ret (Cont'.cons₁ fs k) =>
    goto fun _ =>
      move₂ (fun _ => false) main aux <|
        move₂ (fun s => s = Γ'.consₗ) stack main <|
          move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)
  | Λ'.ret (Cont'.cons₂ k) => goto fun _ => head stack <| Λ'.ret k
  | Λ'.ret (Cont'.comp f k) => goto fun _ => trNormal f k
  | Λ'.ret (Cont'.fix f k) =>
    pop' main <|
      goto fun s =>
        cond (natEnd s.iget) (Λ'.ret k) <| Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)
  | Λ'.ret Cont'.halt => (load fun _ => none) <| halt
@[simp]
theorem tr_move (p k₁ k₂ q) : tr (Λ'.move p k₁ k₂ q) =
    pop' k₁ (branch (fun s => s.elim true p) (goto fun _ => q)
      (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)) := rfl
@[simp]
theorem tr_push (k f q) : tr (Λ'.push k f q) = branch (fun s => (f s).isSome)
    ((push k fun s => (f s).iget) <| goto fun _ => q) (goto fun _ => q) := rfl
@[simp]
theorem tr_read (q) : tr (Λ'.read q) = goto q := rfl
@[simp]
theorem tr_clear (p k q) : tr (Λ'.clear p k q) = pop' k (branch
    (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)) := rfl
@[simp]
theorem tr_copy (q) : tr (Λ'.copy q) = pop' rev (branch Option.isSome
    (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)) := rfl
@[simp]
theorem tr_succ (q) : tr (Λ'.succ q) = pop' main (branch (fun s => s = some Γ'.bit1)
    ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q) <|
      branch (fun s => s = some Γ'.cons)
        ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
        ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)) := rfl
@[simp]
theorem tr_pred (q₁ q₂) : tr (Λ'.pred q₁ q₂) = pop' main (branch (fun s => s = some Γ'.bit0)
    ((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂) <|
    branch (fun s => natEnd s.iget) (goto fun _ => q₁)
      (peek' main <|
        branch (fun s => natEnd s.iget) (goto fun _ => unrev q₂)
          ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))) := rfl
@[simp]
theorem tr_ret_cons₁ (fs k) : tr (Λ'.ret (Cont'.cons₁ fs k)) = goto fun _ =>
    move₂ (fun _ => false) main aux <|
      move₂ (fun s => s = Γ'.consₗ) stack main <|
        move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k) := rfl
@[simp]
theorem tr_ret_cons₂ (k) : tr (Λ'.ret (Cont'.cons₂ k)) =
    goto fun _ => head stack <| Λ'.ret k := rfl
@[simp]
theorem tr_ret_comp (f k) : tr (Λ'.ret (Cont'.comp f k)) = goto fun _ => trNormal f k := rfl
@[simp]
theorem tr_ret_fix (f k) : tr (Λ'.ret (Cont'.fix f k)) = pop' main (goto fun s =>
    cond (natEnd s.iget) (Λ'.ret k) <| Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) := rfl
@[simp]
theorem tr_ret_halt : tr (Λ'.ret Cont'.halt) = (load fun _ => none) halt := rfl
def trCont : Cont → Cont'
  | Cont.halt => Cont'.halt
  | Cont.cons₁ c _ k => Cont'.cons₁ c (trCont k)
  | Cont.cons₂ _ k => Cont'.cons₂ (trCont k)
  | Cont.comp c k => Cont'.comp c (trCont k)
  | Cont.fix c k => Cont'.fix c (trCont k)
def trPosNum : PosNum → List Γ'
  | PosNum.one => [Γ'.bit1]
  | PosNum.bit0 n => Γ'.bit0 :: trPosNum n
  | PosNum.bit1 n => Γ'.bit1 :: trPosNum n
def trNum : Num → List Γ'
  | Num.zero => []
  | Num.pos n => trPosNum n
def trNat (n : ℕ) : List Γ' :=
  trNum n
@[simp]
theorem trNat_zero : trNat 0 = [] := by rw [trNat, Nat.cast_zero]; rfl
theorem trNat_default : trNat default = [] :=
  trNat_zero
@[simp]
def trList : List ℕ → List Γ'
  | [] => []
  | n::ns => trNat n ++ Γ'.cons :: trList ns
@[simp]
def trLList : List (List ℕ) → List Γ'
  | [] => []
  | l::ls => trList l ++ Γ'.consₗ :: trLList ls
@[simp]
def contStack : Cont → List (List ℕ)
  | Cont.halt => []
  | Cont.cons₁ _ ns k => ns :: contStack k
  | Cont.cons₂ ns k => ns :: contStack k
  | Cont.comp _ k => contStack k
  | Cont.fix _ k => contStack k
def trContStack (k : Cont) :=
  trLList (contStack k)
def K'.elim (a b c d : List Γ') : K' → List Γ'
  | K'.main => a
  | K'.rev => b
  | K'.aux => c
  | K'.stack => d
theorem K'.elim_main (a b c d) : K'.elim a b c d K'.main = a := rfl
theorem K'.elim_rev (a b c d) : K'.elim a b c d K'.rev = b := rfl
theorem K'.elim_aux (a b c d) : K'.elim a b c d K'.aux = c := rfl
theorem K'.elim_stack (a b c d) : K'.elim a b c d K'.stack = d := rfl
attribute [simp] K'.elim
@[simp]
theorem K'.elim_update_main {a b c d a'} : update (K'.elim a b c d) main a' = K'.elim a' b c d := by
  funext x; cases x <;> rfl
@[simp]
theorem K'.elim_update_rev {a b c d b'} : update (K'.elim a b c d) rev b' = K'.elim a b' c d := by
  funext x; cases x <;> rfl
@[simp]
theorem K'.elim_update_aux {a b c d c'} : update (K'.elim a b c d) aux c' = K'.elim a b c' d := by
  funext x; cases x <;> rfl
@[simp]
theorem K'.elim_update_stack {a b c d d'} :
    update (K'.elim a b c d) stack d' = K'.elim a b c d' := by funext x; cases x <;> rfl
def halt (v : List ℕ) : Cfg' :=
  ⟨none, none, K'.elim (trList v) [] [] []⟩
def TrCfg : Cfg → Cfg' → Prop
  | Cfg.ret k v, c' =>
    ∃ s, c' = ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩
  | Cfg.halt v, c' => c' = halt v
def splitAtPred {α} (p : α → Bool) : List α → List α × Option α × List α
  | [] => ([], none, [])
  | a :: as =>
    cond (p a) ([], some a, as) <|
      let ⟨l₁, o, l₂⟩ := splitAtPred p as
      ⟨a::l₁, o, l₂⟩
theorem splitAtPred_eq {α} (p : α → Bool) :
    ∀ L l₁ o l₂,
      (∀ x ∈ l₁, p x = false) →
        Option.elim' (L = l₁ ∧ l₂ = []) (fun a => p a = true ∧ L = l₁ ++ a::l₂) o →
          splitAtPred p L = (l₁, o, l₂)
  | [], _, none, _, _, ⟨rfl, rfl⟩ => rfl
  | [], l₁, some o, l₂, _, ⟨_, h₃⟩ => by simp at h₃
  | a :: L, l₁, o, l₂, h₁, h₂ => by
    rw [splitAtPred]
    have IH := splitAtPred_eq p L
    cases' o with o
    · cases' l₁ with a' l₁ <;> rcases h₂ with ⟨⟨⟩, rfl⟩
      rw [h₁ a (List.Mem.head _), cond, IH L none [] _ ⟨rfl, rfl⟩]
      exact fun x h => h₁ x (List.Mem.tail _ h)
    · cases' l₁ with a' l₁ <;> rcases h₂ with ⟨h₂, ⟨⟩⟩
      · rw [h₂, cond]
      rw [h₁ a (List.Mem.head _), cond, IH l₁ (some o) l₂ _ ⟨h₂, _⟩] <;> try rfl
      exact fun x h => h₁ x (List.Mem.tail _ h)
theorem splitAtPred_false {α} (L : List α) : splitAtPred (fun _ => false) L = (L, none, []) :=
  splitAtPred_eq _ _ _ _ _ (fun _ _ => rfl) ⟨rfl, rfl⟩
theorem move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ k₂)
    (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.move p k₁ k₂ q), s, S⟩
      ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverseAux (S k₂))⟩ := by
  induction' L₁ with a L₁ IH generalizing S s
  · rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    swap
    · rw [Function.update_noteq h₁.symm, List.reverseAux_nil]
    refine TransGen.head' rfl ?_
    simp only [TM2.step, Option.mem_def, TM2.stepAux, Option.elim, ne_eq]
    revert e; cases' S k₁ with a Sk <;> intro e
    · cases e
      rfl
    simp only [splitAtPred, Option.elim, List.head?, List.tail_cons, Option.iget_some] at e ⊢
    revert e; cases p a <;> intro e <;>
      simp only [cond_false, cond_true, Prod.mk.injEq, true_and, false_and, reduceCtorEq] at e ⊢
    simp only [e]
    rfl
  · refine TransGen.head rfl ?_
    simp only [TM2.step, Option.mem_def, TM2.stepAux, Option.elim, ne_eq, List.reverseAux_cons]
    cases' e₁ : S k₁ with a' Sk <;> rw [e₁, splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, ne_eq, cond_false]
    convert @IH _ (update (update S k₁ Sk) k₂ (a :: S k₂)) _ using 2 <;>
      simp [Function.update_noteq, h₁, h₁.symm, e₃, List.reverseAux]
    simp [Function.update_comm h₁.symm]
theorem unrev_ok {q s} {S : K' → List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (unrev q), s, S⟩
      ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (S main))⟩ :=
  move_ok (by decide) <| splitAtPred_false _
theorem move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂)
    (h₂ : S rev = []) (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (move₂ p k₁ k₂ q), s, S⟩
      ⟨some q, none, update (update S k₁ (o.elim id List.cons L₂)) k₂ (L₁ ++ S k₂)⟩ := by
  refine (move_ok h₁.1 e).trans (TransGen.head rfl ?_)
  simp only [TM2.step, Option.mem_def, TM2.stepAux, id_eq, ne_eq, Option.elim]
  cases o <;> simp only [Option.elim, id]
  · simp only [TM2.stepAux, Option.isSome, cond_false]
    convert move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [Function.update_comm h₁.1, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_noteq h₁.2.2.symm, Function.update_noteq h₁.2.1,
      Function.update_noteq h₁.1.symm, List.reverseAux_eq, h₂, Function.update_same,
      List.append_nil, List.reverse_reverse]
  · simp only [TM2.stepAux, Option.isSome, cond_true]
    convert move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [h₂, Function.update_comm h₁.1, List.reverseAux_eq, Function.update_same,
      List.append_nil, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_noteq h₁.1.symm, Function.update_noteq h₁.2.2.symm,
      Function.update_noteq h₁.2.1, Function.update_same, List.reverse_reverse]
theorem clear_ok {p k q s L₁ o L₂} {S : K' → List Γ'} (e : splitAtPred p (S k) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.clear p k q), s, S⟩ ⟨some q, o, update S k L₂⟩ := by
  induction' L₁ with a L₁ IH generalizing S s
  · refine TransGen.head' rfl ?_
    simp only [TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    revert e; cases' S k with a Sk <;> intro e
    · cases e
      rfl
    simp only [splitAtPred, Option.elim, List.head?, List.tail_cons] at e ⊢
    revert e; cases p a <;> intro e <;>
      simp only [cond_false, cond_true, Prod.mk.injEq, true_and, false_and, reduceCtorEq] at e ⊢
    rcases e with ⟨e₁, e₂⟩
    rw [e₁, e₂]
  · refine TransGen.head rfl ?_
    simp only [TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    cases' e₁ : S k with a' Sk <;> rw [e₁, splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, cond_false]
    convert @IH _ (update S k Sk) _ using 2 <;> simp [e₃]
theorem copy_ok (q s a b c d) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.copy q), s, K'.elim a b c d⟩
      ⟨some q, none, K'.elim (List.reverseAux b a) [] c (List.reverseAux b d)⟩ := by
  induction' b with x b IH generalizing a d s
  · refine TransGen.single ?_
    simp
  refine TransGen.head rfl ?_
  simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_rev, List.head?_cons, Option.isSome_some,
    List.tail_cons, elim_update_rev, ne_eq, Function.update_noteq, elim_main, elim_update_main,
    elim_stack, elim_update_stack, cond_true, List.reverseAux_cons]
  exact IH _ _ _
theorem trPosNum_natEnd : ∀ (n), ∀ x ∈ trPosNum n, natEnd x = false
  | PosNum.one, _, List.Mem.head _ => rfl
  | PosNum.bit0 _, _, List.Mem.head _ => rfl
  | PosNum.bit0 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h
  | PosNum.bit1 _, _, List.Mem.head _ => rfl
  | PosNum.bit1 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h
theorem trNum_natEnd : ∀ (n), ∀ x ∈ trNum n, natEnd x = false
  | Num.pos n, x, h => trPosNum_natEnd n x h
theorem trNat_natEnd (n) : ∀ x ∈ trNat n, natEnd x = false :=
  trNum_natEnd _
theorem trList_ne_consₗ : ∀ (l), ∀ x ∈ trList l, x ≠ Γ'.consₗ
  | a :: l, x, h => by
    simp only [trList, List.mem_append, List.mem_cons] at h
    obtain h | rfl | h := h
    · rintro rfl
      cases trNat_natEnd _ _ h
    · rintro ⟨⟩
    · exact trList_ne_consₗ l _ h
theorem head_main_ok {q s L} {c d : List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (head main q), s, K'.elim (trList L) [] c d⟩
      ⟨some q, none, K'.elim (trList [L.headI]) [] c d⟩ := by
  let o : Option Γ' := List.casesOn L none fun _ _ => some Γ'.cons
  refine
    (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat L.headI) o (trList L.tail) (trNat_natEnd _) ?_)).trans
      (TransGen.head rfl (TransGen.head rfl ?_))
  · cases L <;> simp [o]
  simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_update_main, elim_rev, elim_update_rev,
    Function.update_same, trList]
  rw [if_neg (show o ≠ some Γ'.consₗ by cases L <;> simp [o])]
  refine (clear_ok (splitAtPred_eq _ _ _ none [] ?_ ⟨rfl, rfl⟩)).trans ?_
  · exact fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)
  convert unrev_ok using 2; simp [List.reverseAux_eq]
theorem head_stack_ok {q s L₁ L₂ L₃} :
    Reaches₁ (TM2.step tr)
      ⟨some (head stack q), s, K'.elim (trList L₁) [] [] (trList L₂ ++ Γ'.consₗ :: L₃)⟩
      ⟨some q, none, K'.elim (trList (L₂.headI :: L₁)) [] [] L₃⟩ := by
  cases' L₂ with a L₂
  · refine
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ [] (some Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
        (TransGen.head rfl (TransGen.head rfl ?_))
    simp only [TM2.step, Option.mem_def, TM2.stepAux, ite_true, id_eq, trList, List.nil_append,
      elim_update_stack, elim_rev, List.reverseAux_nil, elim_update_rev, Function.update_same,
      List.headI_nil, trNat_default]
    convert unrev_ok using 2
    simp
  · refine
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat a) (some Γ'.cons) (trList L₂ ++ Γ'.consₗ :: L₃)
            (trNat_natEnd _) ⟨rfl, by simp⟩))
        (TransGen.head rfl (TransGen.head rfl ?_))
    simp only [TM2.step, Option.mem_def, TM2.stepAux, ite_false, trList, List.append_assoc,
      List.cons_append, elim_update_stack, elim_rev, elim_update_rev, Function.update_same,
      List.headI_cons]
    refine
      TransGen.trans
        (clear_ok
          (splitAtPred_eq _ _ (trList L₂) (some Γ'.consₗ) L₃
            (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, by simp⟩))
        ?_
    convert unrev_ok using 2
    simp [List.reverseAux_eq]
theorem succ_ok {q s n} {c d : List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.succ q), s, K'.elim (trList [n]) [] c d⟩
      ⟨some q, none, K'.elim (trList [n.succ]) [] c d⟩ := by
  simp only [TM2.step, trList, trNat.eq_1, Nat.cast_succ, Num.add_one]
  cases' (n : Num) with a
  · refine TransGen.head rfl ?_
    simp only [Option.mem_def, TM2.stepAux, elim_main, decide_false, elim_update_main, ne_eq,
      Function.update_noteq, elim_rev, elim_update_rev, decide_true, Function.update_same,
      cond_true, cond_false]
    convert unrev_ok using 1
    simp only [elim_update_rev, elim_rev, elim_main, List.reverseAux_nil, elim_update_main]
    rfl
  simp only [trNum, Num.succ, Num.succ']
  suffices ∀ l₁, ∃ l₁' l₂' s',
      List.reverseAux l₁ (trPosNum a.succ) = List.reverseAux l₁' l₂' ∧
        Reaches₁ (TM2.step tr) ⟨some q.succ, s, K'.elim (trPosNum a ++ [Γ'.cons]) l₁ c d⟩
          ⟨some (unrev q), s', K'.elim (l₂' ++ [Γ'.cons]) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp? [List.reverseAux] at e says simp only [List.reverseAux, List.reverseAux_eq] at e
    refine h.trans ?_
    convert unrev_ok using 2
    simp [e, List.reverseAux_eq]
  induction' a with m IH m _ generalizing s <;> intro l₁
  · refine ⟨Γ'.bit0 :: l₁, [Γ'.bit1], some Γ'.cons, rfl, TransGen.head rfl (TransGen.single ?_)⟩
    simp [trPosNum]
  · obtain ⟨l₁', l₂', s', e, h⟩ := IH (Γ'.bit0 :: l₁)
    refine ⟨l₁', l₂', s', e, TransGen.head ?_ h⟩
    simp [PosNum.succ, trPosNum]
    rfl
  · refine ⟨l₁, _, some Γ'.bit0, rfl, TransGen.single ?_⟩
    simp only [TM2.step, TM2.stepAux, elim_main, elim_update_main, ne_eq, Function.update_noteq,
      elim_rev, elim_update_rev, Function.update_same, Option.mem_def, Option.some.injEq]
    rfl
theorem pred_ok (q₁ q₂ s v) (c d : List Γ') : ∃ s',
    Reaches₁ (TM2.step tr) ⟨some (Λ'.pred q₁ q₂), s, K'.elim (trList v) [] c d⟩
      (v.headI.rec ⟨some q₁, s', K'.elim (trList v.tail) [] c d⟩ fun n _ =>
        ⟨some q₂, s', K'.elim (trList (n::v.tail)) [] c d⟩) := by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine ⟨none, TransGen.single ?_⟩
    simp
  · refine ⟨some Γ'.cons, TransGen.single ?_⟩
    simp
  refine ⟨none, ?_⟩
  simp only [TM2.step, trList, trNat.eq_1, trNum, Nat.cast_succ, Num.add_one, Num.succ,
    List.tail_cons, List.headI_cons]
  cases' (n : Num) with a
  · simp only [trPosNum, List.singleton_append, List.nil_append]
    refine TransGen.head rfl ?_
    simp only [Option.mem_def, TM2.stepAux, elim_main, List.head?_cons, Option.some.injEq,
      decide_false, List.tail_cons, elim_update_main, ne_eq, Function.update_noteq, elim_rev,
      elim_update_rev, natEnd, Function.update_same,  cond_true, cond_false]
    convert unrev_ok using 2
    simp
  simp only [Num.succ']
  suffices ∀ l₁, ∃ l₁' l₂' s',
    List.reverseAux l₁ (trPosNum a) = List.reverseAux l₁' l₂' ∧
      Reaches₁ (TM2.step tr)
        ⟨some (q₁.pred q₂), s, K'.elim (trPosNum a.succ ++ Γ'.cons :: trList v) l₁ c d⟩
        ⟨some (unrev q₂), s', K'.elim (l₂' ++ Γ'.cons :: trList v) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp only [List.reverseAux] at e
    refine h.trans ?_
    convert unrev_ok using 2
    simp [e, List.reverseAux_eq]
  induction' a with m IH m IH generalizing s <;> intro l₁
  · refine ⟨Γ'.bit1::l₁, [], some Γ'.cons, rfl, TransGen.head rfl (TransGen.single ?_)⟩
    simp [trPosNum, show PosNum.one.succ = PosNum.one.bit0 from rfl]
  · obtain ⟨l₁', l₂', s', e, h⟩ := IH (some Γ'.bit0) (Γ'.bit1 :: l₁)
    refine ⟨l₁', l₂', s', e, TransGen.head ?_ h⟩
    simp
    rfl
  · obtain ⟨a, l, e, h⟩ : ∃ a l, (trPosNum m = a::l) ∧ natEnd a = false := by
      cases m <;> refine ⟨_, _, rfl, rfl⟩
    refine ⟨Γ'.bit0 :: l₁, _, some a, rfl, TransGen.single ?_⟩
    simp [trPosNum, PosNum.succ, e, h, show some Γ'.bit1 ≠ some Γ'.bit0 by decide,
      Option.iget, -natEnd]
    rfl
theorem trNormal_respects (c k v s) :
    ∃ b₂,
      TrCfg (stepNormal c k v) b₂ ∧
        Reaches₁ (TM2.step tr)
          ⟨some (trNormal c (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩ b₂ := by
  induction c generalizing k v s with
  | zero' => refine ⟨_, ⟨s, rfl⟩, TransGen.single ?_⟩; simp
  | succ => refine ⟨_, ⟨none, rfl⟩, head_main_ok.trans succ_ok⟩
  | tail =>
    let o : Option Γ' := List.casesOn v none fun _ _ => some Γ'.cons
    refine ⟨_, ⟨o, rfl⟩, ?_⟩; convert clear_ok _ using 2
    · simp; rfl
    swap
    refine splitAtPred_eq _ _ (trNat v.headI) _ _ (trNat_natEnd _) ?_
    cases v <;> simp [o]
  | cons f fs IHf _ =>
    obtain ⟨c, h₁, h₂⟩ := IHf (Cont.cons₁ fs v k) v none
    refine ⟨c, h₁, TransGen.head rfl <| (move_ok (by decide) (splitAtPred_false _)).trans ?_⟩
    simp only [TM2.step, Option.mem_def, elim_stack, elim_update_stack, elim_update_main, ne_eq,
      Function.update_noteq, elim_main, elim_rev, elim_update_rev]
    refine (copy_ok _ none [] (trList v).reverse _ _).trans ?_
    convert h₂ using 2
    simp [List.reverseAux_eq, trContStack]
  | comp f _ _ IHg => exact IHg (Cont.comp f k) v s
  | case f g IHf IHg =>
    rw [stepNormal]
    simp only
    obtain ⟨s', h⟩ := pred_ok _ _ s v _ _
    revert h; cases' v.headI with n <;> intro h
    · obtain ⟨c, h₁, h₂⟩ := IHf k _ s'
      exact ⟨_, h₁, h.trans h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := IHg k _ s'
      exact ⟨_, h₁, h.trans h₂⟩
  | fix f IH => apply IH
theorem tr_ret_respects (k v s) : ∃ b₂,
    TrCfg (stepRet k v) b₂ ∧
      Reaches₁ (TM2.step tr)
        ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩ b₂ := by
  induction k generalizing v s with
  | halt => exact ⟨_, rfl, TransGen.single rfl⟩
  | cons₁ fs as k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects fs (Cont.cons₂ v k) as none
    refine ⟨s', h₁, TransGen.head rfl ?_⟩; simp
    refine (move₂_ok (by decide) ?_ (splitAtPred_false _)).trans ?_; · rfl
    simp only [TM2.step, Option.mem_def, Option.elim, id_eq, elim_update_main, elim_main, elim_aux,
      List.append_nil, elim_update_aux]
    refine (move₂_ok (L₁ := ?_) (o := ?_) (L₂ := ?_) (by decide) rfl ?_).trans ?_
    pick_goal 4
    · exact splitAtPred_eq _ _ _ (some Γ'.consₗ) _
        (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, rfl⟩
    refine (move₂_ok (by decide) ?_ (splitAtPred_false _)).trans ?_; · rfl
    simp only [TM2.step, Option.mem_def, Option.elim, elim_update_stack, elim_main,
      List.append_nil, elim_update_main,  id_eq, elim_update_aux, ne_eq, Function.update_noteq,
      elim_aux, elim_stack]
    exact h₂
  | cons₂ ns k IH =>
    obtain ⟨c, h₁, h₂⟩ := IH (ns.headI :: v) none
    exact ⟨c, h₁, TransGen.head rfl <| head_stack_ok.trans h₂⟩
  | comp f k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects f k v s
    exact ⟨_, h₁, TransGen.head rfl h₂⟩
  | fix f k IH =>
    rw [stepRet]
    have :
      if v.headI = 0 then natEnd (trList v).head?.iget = true ∧ (trList v).tail = trList v.tail
      else
        natEnd (trList v).head?.iget = false ∧
          (trList v).tail = (trNat v.headI).tail ++ Γ'.cons :: trList v.tail := by
      cases' v with n
      · exact ⟨rfl, rfl⟩
      cases' n with n
      · simp
      rw [trList, List.headI, trNat, Nat.cast_succ, Num.add_one, Num.succ, List.tail]
      cases (n : Num).succ' <;> exact ⟨rfl, rfl⟩
    by_cases h : v.headI = 0 <;> simp only [h, ite_true, ite_false] at this ⊢
    · obtain ⟨c, h₁, h₂⟩ := IH v.tail (trList v).head?
      refine ⟨c, h₁, TransGen.head rfl ?_⟩
      simp only [Option.mem_def, TM2.stepAux, trContStack, contStack, elim_main, this, cond_true,
        elim_update_main]
      exact h₂
    · obtain ⟨s', h₁, h₂⟩ := trNormal_respects f (Cont.fix f k) v.tail (some Γ'.cons)
      refine ⟨_, h₁, TransGen.head rfl <| TransGen.trans ?_ h₂⟩
      simp only [Option.mem_def, TM2.stepAux, elim_main, this.1, cond_false, elim_update_main,
        trCont]
      convert clear_ok (splitAtPred_eq _ _ (trNat v.headI).tail (some Γ'.cons) _ _ _) using 2
      · simp
        convert rfl
      · exact fun x h => trNat_natEnd _ _ (List.tail_subset _ h)
      · exact ⟨rfl, this.2⟩
theorem tr_respects : Respects step (TM2.step tr) TrCfg
  | Cfg.ret _ _, _, ⟨_, rfl⟩ => tr_ret_respects _ _ _
  | Cfg.halt _, _, rfl => rfl
def init (c : Code) (v : List ℕ) : Cfg' :=
  ⟨some (trNormal c Cont'.halt), none, K'.elim (trList v) [] [] []⟩
theorem tr_init (c v) :
    ∃ b, TrCfg (stepNormal c Cont.halt v) b ∧ Reaches₁ (TM2.step tr) (init c v) b :=
  trNormal_respects _ _ _ _
theorem tr_eval (c v) : eval (TM2.step tr) (init c v) = halt <$> Code.eval c v := by
  obtain ⟨i, h₁, h₂⟩ := tr_init c v
  refine Part.ext fun x => ?_
  rw [reaches_eval h₂.to_reflTransGen]; simp only [Part.map_eq_map, Part.mem_map_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, hc₁, hc₂⟩ := tr_eval_rev tr_respects h₁ h
    simp [stepNormal_eval] at hc₂
    obtain ⟨v', hv, rfl⟩ := hc₂
    exact ⟨_, hv, hc₁.symm⟩
  · rintro ⟨v', hv, rfl⟩
    have := Turing.tr_eval (b₁ := Cfg.halt v') tr_respects h₁
    simp only [stepNormal_eval, Part.map_eq_map, Part.mem_map_iff, Cfg.halt.injEq,
      exists_eq_right] at this
    obtain ⟨_, ⟨⟩, h⟩ := this hv
    exact h
def trStmts₁ : Λ' → Finset Λ'
  | Q@(Λ'.move _ _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.push _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.read q) => insert Q <| Finset.univ.biUnion fun s => trStmts₁ (q s)
  | Q@(Λ'.clear _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.copy q) => insert Q <| trStmts₁ q
  | Q@(Λ'.succ q) => insert Q <| insert (unrev q) <| trStmts₁ q
  | Q@(Λ'.pred q₁ q₂) => insert Q <| trStmts₁ q₁ ∪ insert (unrev q₂) (trStmts₁ q₂)
  | Q@(Λ'.ret _) => {Q}
theorem trStmts₁_trans {q q'} : q' ∈ trStmts₁ q → trStmts₁ q' ⊆ trStmts₁ q := by
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
  all_goals
    simp +contextual only [trStmts₁, Finset.mem_insert, Finset.mem_union,
      or_imp, Finset.mem_singleton, Finset.Subset.refl, imp_true_iff, true_and]
    repeat exact fun h => Finset.Subset.trans (q_ih h) (Finset.subset_insert _ _)
  · simp
    intro s h x h'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert]
    exact Or.inr ⟨_, q_ih s h h'⟩
  · constructor
    · rintro rfl
      apply Finset.subset_insert
    · intro h x h'
      simp only [Finset.mem_insert]
      exact Or.inr (Or.inr <| q_ih h h')
  · refine ⟨fun h x h' => ?_, fun _ x h' => ?_, fun h x h' => ?_⟩ <;> simp
    · exact Or.inr (Or.inr <| Or.inl <| q₁_ih h h')
    · cases' Finset.mem_insert.1 h' with h' h' <;> simp [h', unrev]
    · exact Or.inr (Or.inr <| Or.inr <| q₂_ih h h')
theorem trStmts₁_self (q) : q ∈ trStmts₁ q := by
  induction q <;> · first |apply Finset.mem_singleton_self|apply Finset.mem_insert_self
def codeSupp' : Code → Cont' → Finset Λ'
  | c@Code.zero', k => trStmts₁ (trNormal c k)
  | c@Code.succ, k => trStmts₁ (trNormal c k)
  | c@Code.tail, k => trStmts₁ (trNormal c k)
  | c@(Code.cons f fs), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' f (Cont'.cons₁ fs k) ∪
        (trStmts₁
            (move₂ (fun _ => false) main aux <|
              move₂ (fun s => s = Γ'.consₗ) stack main <|
                move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
          (codeSupp' fs (Cont'.cons₂ k) ∪ trStmts₁ (head stack <| Λ'.ret k))))
  | c@(Code.comp f g), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' g (Cont'.comp f k) ∪ (trStmts₁ (trNormal f k) ∪ codeSupp' f k))
  | c@(Code.case f g), k => trStmts₁ (trNormal c k) ∪ (codeSupp' f k ∪ codeSupp' g k)
  | c@(Code.fix f), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' f (Cont'.fix f k) ∪
        (trStmts₁ (Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) ∪ {Λ'.ret k}))
@[simp]
theorem codeSupp'_self (c k) : trStmts₁ (trNormal c k) ⊆ codeSupp' c k := by
  cases c <;> first | rfl | exact Finset.union_subset_left (fun _ a ↦ a)
def contSupp : Cont' → Finset Λ'
  | Cont'.cons₁ fs k =>
    trStmts₁
        (move₂ (fun _ => false) main aux <|
          move₂ (fun s => s = Γ'.consₗ) stack main <|
            move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
      (codeSupp' fs (Cont'.cons₂ k) ∪ (trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k))
  | Cont'.cons₂ k => trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k
  | Cont'.comp f k => codeSupp' f k ∪ contSupp k
  | Cont'.fix f k => codeSupp' (Code.fix f) k ∪ contSupp k
  | Cont'.halt => ∅
def codeSupp (c : Code) (k : Cont') : Finset Λ' :=
  codeSupp' c k ∪ contSupp k
@[simp]
theorem codeSupp_self (c k) : trStmts₁ (trNormal c k) ⊆ codeSupp c k :=
  Finset.Subset.trans (codeSupp'_self _ _) (Finset.union_subset_left fun _ a ↦ a)
@[simp]
theorem codeSupp_zero (k) : codeSupp Code.zero' k = trStmts₁ (trNormal Code.zero' k) ∪ contSupp k :=
  rfl
@[simp]
theorem codeSupp_succ (k) : codeSupp Code.succ k = trStmts₁ (trNormal Code.succ k) ∪ contSupp k :=
  rfl
@[simp]
theorem codeSupp_tail (k) : codeSupp Code.tail k = trStmts₁ (trNormal Code.tail k) ∪ contSupp k :=
  rfl
@[simp]
theorem codeSupp_cons (f fs k) :
    codeSupp (Code.cons f fs) k =
      trStmts₁ (trNormal (Code.cons f fs) k) ∪ codeSupp f (Cont'.cons₁ fs k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]
@[simp]
theorem codeSupp_comp (f g k) :
    codeSupp (Code.comp f g) k =
      trStmts₁ (trNormal (Code.comp f g) k) ∪ codeSupp g (Cont'.comp f k) := by
  simp only [codeSupp, codeSupp', trNormal, Finset.union_assoc, contSupp]
  rw [← Finset.union_assoc _ _ (contSupp k),
    Finset.union_eq_right.2 (codeSupp'_self _ _)]
@[simp]
theorem codeSupp_case (f g k) :
    codeSupp (Code.case f g) k =
      trStmts₁ (trNormal (Code.case f g) k) ∪ (codeSupp f k ∪ codeSupp g k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm]
@[simp]
theorem codeSupp_fix (f k) :
    codeSupp (Code.fix f) k = trStmts₁ (trNormal (Code.fix f) k) ∪ codeSupp f (Cont'.fix f k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm,
    Finset.union_left_idem]
@[simp]
theorem contSupp_cons₁ (fs k) :
    contSupp (Cont'.cons₁ fs k) =
      trStmts₁
          (move₂ (fun _ => false) main aux <|
            move₂ (fun s => s = Γ'.consₗ) stack main <|
              move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
        codeSupp fs (Cont'.cons₂ k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]
@[simp]
theorem contSupp_cons₂ (k) :
    contSupp (Cont'.cons₂ k) = trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k :=
  rfl
@[simp]
theorem contSupp_comp (f k) : contSupp (Cont'.comp f k) = codeSupp f k :=
  rfl
theorem contSupp_fix (f k) : contSupp (Cont'.fix f k) = codeSupp f (Cont'.fix f k) := by
  simp +contextual [codeSupp, codeSupp', contSupp, Finset.union_assoc,
    Finset.subset_iff]
@[simp]
theorem contSupp_halt : contSupp Cont'.halt = ∅ :=
  rfl
def Λ'.Supports (S : Finset Λ') : Λ' → Prop
  | Λ'.move _ _ _ q => Λ'.Supports S q
  | Λ'.push _ _ q => Λ'.Supports S q
  | Λ'.read q => ∀ s, Λ'.Supports S (q s)
  | Λ'.clear _ _ q => Λ'.Supports S q
  | Λ'.copy q => Λ'.Supports S q
  | Λ'.succ q => Λ'.Supports S q
  | Λ'.pred q₁ q₂ => Λ'.Supports S q₁ ∧ Λ'.Supports S q₂
  | Λ'.ret k => contSupp k ⊆ S
def Supports (K S : Finset Λ') :=
  ∀ q ∈ K, TM2.SupportsStmt S (tr q)
theorem supports_insert {K S q} :
    Supports (insert q K) S ↔ TM2.SupportsStmt S (tr q) ∧ Supports K S := by simp [Supports]
theorem supports_singleton {S q} : Supports {q} S ↔ TM2.SupportsStmt S (tr q) := by simp [Supports]
theorem supports_union {K₁ K₂ S} : Supports (K₁ ∪ K₂) S ↔ Supports K₁ S ∧ Supports K₂ S := by
  simp [Supports, or_imp, forall_and]
theorem supports_biUnion {K : Option Γ' → Finset Λ'} {S} :
    Supports (Finset.univ.biUnion K) S ↔ ∀ a, Supports (K a) S := by
  simpa [Supports] using forall_swap
theorem head_supports {S k q} (H : (q : Λ').Supports S) : (head k q).Supports S := fun _ => by
  dsimp only; split_ifs <;> exact H
theorem ret_supports {S k} (H₁ : contSupp k ⊆ S) : TM2.SupportsStmt S (tr (Λ'.ret k)) := by
  have W := fun {q} => trStmts₁_self q
  cases k with
  | halt => trivial
  | cons₁ => rw [contSupp_cons₁, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | cons₂ => rw [contSupp_cons₂, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | comp => rw [contSupp_comp] at H₁; exact fun _ => H₁ (codeSupp_self _ _ W)
  | fix =>
    rw [contSupp_fix] at H₁
    have L := @Finset.mem_union_left; have R := @Finset.mem_union_right
    intro s; dsimp only; cases natEnd s.iget
    · refine H₁ (R _ <| L _ <| R _ <| R _ <| L _ W)
    · exact H₁ (R _ <| L _ <| R _ <| R _ <| R _ <| Finset.mem_singleton_self _)
theorem trStmts₁_supports {S q} (H₁ : (q : Λ').Supports S) (HS₁ : trStmts₁ q ⊆ S) :
    Supports (trStmts₁ q) S := by
  have W := fun {q} => trStmts₁_self q
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
    simp [trStmts₁, -Finset.singleton_subset_iff] at HS₁ ⊢
  any_goals
    cases' Finset.insert_subset_iff.1 HS₁ with h₁ h₂
    first | have h₃ := h₂ W | try simp [Finset.subset_iff] at h₂
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₁⟩, q_ih H₁ h₂⟩ 
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₁⟩, q_ih H₁ h₂⟩ 
  · exact supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₃⟩, q_ih H₁ h₂⟩ 
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₃⟩, q_ih H₁ h₂⟩ 
  · refine supports_insert.2 ⟨fun _ => h₂ _ W, ?_⟩ 
    exact supports_biUnion.2 fun _ => q_ih _ (H₁ _) fun _ h => h₂ _ h
  · refine supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₂.1, fun _ => h₂.1⟩, ?_⟩ 
    exact supports_insert.2 ⟨⟨fun _ => h₂.2 _ W, fun _ => h₂.1⟩, q_ih H₁ h₂.2⟩
  · refine 
      supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₂.2 _ (Or.inl W),
                          fun _ => h₂.1, fun _ => h₂.1⟩, ?_⟩
    refine supports_insert.2 ⟨⟨fun _ => h₂.2 _ (Or.inr W), fun _ => h₂.1⟩, ?_⟩
    refine supports_union.2 ⟨?_, ?_⟩
    · exact q₁_ih H₁.1 fun _ h => h₂.2 _ (Or.inl h)
    · exact q₂_ih H₁.2 fun _ h => h₂.2 _ (Or.inr h)
  · exact supports_singleton.2 (ret_supports H₁)  
theorem trStmts₁_supports' {S q K} (H₁ : (q : Λ').Supports S) (H₂ : trStmts₁ q ∪ K ⊆ S)
    (H₃ : K ⊆ S → Supports K S) : Supports (trStmts₁ q ∪ K) S := by
  simp only [Finset.union_subset_iff] at H₂
  exact supports_union.2 ⟨trStmts₁_supports H₁ H₂.1, H₃ H₂.2⟩
theorem trNormal_supports {S c k} (Hk : codeSupp c k ⊆ S) : (trNormal c k).Supports S := by
  induction c generalizing k with simp [Λ'.Supports, head]
  | zero' => exact Finset.union_subset_right Hk
  | succ => intro; split_ifs <;> exact Finset.union_subset_right Hk
  | tail => exact Finset.union_subset_right Hk
  | cons f fs IHf _ =>
    apply IHf
    rw [codeSupp_cons] at Hk
    exact Finset.union_subset_right Hk
  | comp f g _ IHg => apply IHg; rw [codeSupp_comp] at Hk; exact Finset.union_subset_right Hk
  | case f g IHf IHg =>
    simp only [codeSupp_case, Finset.union_subset_iff] at Hk
    exact ⟨IHf Hk.2.1, IHg Hk.2.2⟩
  | fix f IHf => apply IHf; rw [codeSupp_fix] at Hk; exact Finset.union_subset_right Hk
theorem codeSupp'_supports {S c k} (H : codeSupp c k ⊆ S) : Supports (codeSupp' c k) S := by
  induction c generalizing k with
  | cons f fs IHf IHfs =>
    have H' := H; simp only [codeSupp_cons, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHf H'.2, ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun h => ?_
    · simp only [codeSupp, Finset.union_subset_iff, contSupp] at h H ⊢
      exact ⟨h.2.2.1, h.2.2.2, H.2⟩
    refine supports_union.2 ⟨IHfs ?_, ?_⟩
    · rw [codeSupp, contSupp_cons₁] at H'
      exact Finset.union_subset_right (Finset.union_subset_right H'.2)
    exact
      trStmts₁_supports (head_supports <| Finset.union_subset_right H)
        (Finset.union_subset_right h)
  | comp f g IHf IHg =>
    have H' := H; rw [codeSupp_comp] at H'; have H' := Finset.union_subset_right H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHg H', ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun _ => ?_
    · simp only [codeSupp', codeSupp, Finset.union_subset_iff, contSupp] at h H ⊢
      exact ⟨h.2.2, H.2⟩
    exact IHf (Finset.union_subset_right H')
  | case f g IHf IHg =>
    have H' := H; simp only [codeSupp_case, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun _ => ?_
    exact supports_union.2 ⟨IHf H'.2.1, IHg H'.2.2⟩
  | fix f IHf =>
    have H' := H; simp only [codeSupp_fix, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHf H'.2, ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun _ => ?_
    · simp only [codeSupp', codeSupp, Finset.union_subset_iff, contSupp, trStmts₁,
        Finset.insert_subset_iff] at h H ⊢
      exact ⟨h.1, ⟨H.1.1, h⟩, H.2⟩
    exact supports_singleton.2 (ret_supports <| Finset.union_subset_right H)
  | _ => exact trStmts₁_supports (trNormal_supports H) (Finset.Subset.trans (codeSupp_self _ _) H)
theorem contSupp_supports {S k} (H : contSupp k ⊆ S) : Supports (contSupp k) S := by
  induction k with
  | halt => simp [contSupp_halt, Supports]
  | cons₁ f k IH =>
    have H₁ := H; rw [contSupp_cons₁] at H₁; have H₂ := Finset.union_subset_right H₁
    refine trStmts₁_supports' (trNormal_supports H₂) H₁ fun h => ?_
    refine supports_union.2 ⟨codeSupp'_supports H₂, ?_⟩
    simp only [codeSupp, contSupp_cons₂, Finset.union_subset_iff] at H₂
    exact trStmts₁_supports' (head_supports H₂.2.2) (Finset.union_subset_right h) IH
  | cons₂ k IH =>
    have H' := H; rw [contSupp_cons₂] at H'
    exact trStmts₁_supports' (head_supports <| Finset.union_subset_right H') H' IH
  | comp f k IH =>
    have H' := H; rw [contSupp_comp] at H'; have H₂ := Finset.union_subset_right H'
    exact supports_union.2 ⟨codeSupp'_supports H', IH H₂⟩
  | fix f k IH =>
    rw [contSupp] at H
    exact supports_union.2 ⟨codeSupp'_supports H, IH (Finset.union_subset_right H)⟩
theorem codeSupp_supports {S c k} (H : codeSupp c k ⊆ S) : Supports (codeSupp c k) S :=
  supports_union.2 ⟨codeSupp'_supports H, contSupp_supports (Finset.union_subset_right H)⟩
theorem tr_supports (c k) : @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (codeSupp c k) :=
  ⟨codeSupp_self _ _ (trStmts₁_self _), fun _ => codeSupp_supports (Finset.Subset.refl _) _⟩
end
end PartrecToTM2
end Turing
set_option linter.style.longFile 2100