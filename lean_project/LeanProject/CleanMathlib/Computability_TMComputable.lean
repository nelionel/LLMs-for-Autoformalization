import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine
open Computability
namespace Turing
structure FinTM2 where
  {K : Type} [kDecidableEq : DecidableEq K]
  [kFin : Fintype K]
  (k₀ k₁ : K)
  (Γ : K → Type)
  (Λ : Type)
  (main : Λ)
  [ΛFin : Fintype Λ]
  (σ : Type)
  (initialState : σ)
  [σFin : Fintype σ]
  [Γk₀Fin : Fintype (Γ k₀)]
  (m : Λ → Turing.TM2.Stmt Γ Λ σ)
attribute [nolint docBlame] FinTM2.kDecidableEq
namespace FinTM2
section
variable (tm : FinTM2)
instance decidableEqK : DecidableEq tm.K :=
  tm.kDecidableEq
instance inhabitedσ : Inhabited tm.σ :=
  ⟨tm.initialState⟩
def Stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ
instance inhabitedStmt : Inhabited (Stmt tm) :=
  inferInstanceAs (Inhabited (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ))
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ
instance inhabitedCfg : Inhabited (Cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  Turing.TM2.step tm.m
end
end FinTM2
def initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tm.Cfg where
  l := Option.some tm.main
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact s)
      fun _ => []
def haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : tm.Cfg where
  l := Option.none
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁) (fun h => by rw [h]; exact s)
      fun _ => []
structure EvalsTo {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) where
  steps : ℕ
  evals_in_steps : (flip bind f)^[steps] a = b
structure EvalsToInTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) extends
  EvalsTo f a b where
  steps_le_m : steps ≤ m
def EvalsTo.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsTo f a a :=
  ⟨0, rfl⟩
@[trans]
def EvalsTo.trans {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
    (h₁ : EvalsTo f a b) (h₂ : EvalsTo f b c) : EvalsTo f a c :=
  ⟨h₂.steps + h₁.steps, by rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩
def EvalsToInTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsToInTime f a a 0 :=
  ⟨EvalsTo.refl f a, le_refl 0⟩
@[trans]
def EvalsToInTime.trans {σ : Type*} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToInTime f a b m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩
def TM2Outputs (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')
def TM2OutputsInTime (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
    (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m
def TM2OutputsInTime.toTM2Outputs {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} (h : TM2OutputsInTime tm l l' m) :
    TM2Outputs tm l l' :=
  h.toEvalsTo
structure TM2ComputableAux (Γ₀ Γ₁ : Type) where
  tm : FinTM2
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁
structure TM2Computable {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) extends
  TM2ComputableAux ea.Γ eb.Γ where
  outputsFun :
    ∀ a,
      TM2Outputs tm (List.map inputAlphabet.invFun (ea.encode a))
        (Option.some ((List.map outputAlphabet.invFun) (eb.encode (f a))))
structure TM2ComputableInTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
  (f : α → β) extends TM2ComputableAux ea.Γ eb.Γ where
  time : ℕ → ℕ
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea.encode a))
        (Option.some ((List.map outputAlphabet.invFun) (eb.encode (f a))))
        (time (ea.encode a).length)
structure TM2ComputableInPolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
  (f : α → β) extends TM2ComputableAux ea.Γ eb.Γ where
  time : Polynomial ℕ
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea.encode a))
        (Option.some ((List.map outputAlphabet.invFun) (eb.encode (f a))))
        (time.eval (ea.encode a).length)
def TM2ComputableInTime.toTM2Computable {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    {f : α → β} (h : TM2ComputableInTime ea eb f) : TM2Computable ea eb f :=
  ⟨h.toTM2ComputableAux, fun a => TM2OutputsInTime.toTM2Outputs (h.outputsFun a)⟩
def TM2ComputableInPolyTime.toTM2ComputableInTime {α β : Type} {ea : FinEncoding α}
    {eb : FinEncoding β} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    TM2ComputableInTime ea eb f :=
  ⟨h.toTM2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩
open Turing.TM2.Stmt
def idComputer {α : Type} (ea : FinEncoding α) : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := ea.Γ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  Γk₀Fin := ea.ΓFin
  m _ := halt
instance inhabitedFinTM2 : Inhabited FinTM2 :=
  ⟨idComputer Computability.inhabitedFinEncoding.default⟩
noncomputable section
def idComputableInPolyTime {α : Type} (ea : FinEncoding α) :
    @TM2ComputableInPolyTime α α ea ea id where
  tm := idComputer ea
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 1
  outputsFun _ :=
    { steps := 1
      evals_in_steps := rfl
      steps_le_m := by simp only [Polynomial.eval_one, le_refl] }
instance inhabitedTM2ComputableInPolyTime :
    Inhabited (TM2ComputableInPolyTime (default : FinEncoding Bool) default id) :=
  ⟨idComputableInPolyTime Computability.inhabitedFinEncoding.default⟩
instance inhabitedTM2OutputsInTime :
    Inhabited
      (TM2OutputsInTime (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false])) (Polynomial.eval 1 1)) :=
  ⟨(idComputableInPolyTime finEncodingBoolBool).outputsFun false⟩
instance inhabitedTM2Outputs :
    Inhabited
      (TM2Outputs (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
        (some (List.map (Equiv.cast rfl).invFun [false]))) :=
  ⟨TM2OutputsInTime.toTM2Outputs Turing.inhabitedTM2OutputsInTime.default⟩
instance inhabitedEvalsToInTime :
    Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
  ⟨EvalsToInTime.refl _ _⟩
instance inhabitedTM2EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
  ⟨EvalsTo.refl _ _⟩
def idComputableInTime {α : Type} (ea : FinEncoding α) : @TM2ComputableInTime α α ea ea id :=
  TM2ComputableInPolyTime.toTM2ComputableInTime <| idComputableInPolyTime ea
instance inhabitedTM2ComputableInTime :
    Inhabited (TM2ComputableInTime finEncodingBoolBool finEncodingBoolBool id) :=
  ⟨idComputableInTime Computability.inhabitedFinEncoding.default⟩
def idComputable {α : Type} (ea : FinEncoding α) : @TM2Computable α α ea ea id :=
  TM2ComputableInTime.toTM2Computable <| idComputableInTime ea
instance inhabitedTM2Computable :
    Inhabited (TM2Computable finEncodingBoolBool finEncodingBoolBool id) :=
  ⟨idComputable Computability.inhabitedFinEncoding.default⟩
instance inhabitedTM2ComputableAux : Inhabited (TM2ComputableAux Bool Bool) :=
  ⟨(default : TM2Computable finEncodingBoolBool finEncodingBoolBool id).toTM2ComputableAux⟩
end
end Turing