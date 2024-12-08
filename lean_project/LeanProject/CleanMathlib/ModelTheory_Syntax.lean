import Mathlib.Data.Set.Prod
import Mathlib.Logic.Equiv.Fin
import Mathlib.ModelTheory.LanguageMap
import Mathlib.Algebra.Order.Ring.Nat
universe u v w u' v'
namespace FirstOrder
namespace Language
variable (L : Language.{u, v}) {L' : Language}
variable {M : Type w} {α : Type u'} {β : Type v'} {γ : Type*}
open FirstOrder
open Structure Fin
inductive Term (α : Type u') : Type max u u'
  | var : α → Term α
  | func : ∀ {l : ℕ} (_f : L.Functions l) (_ts : Fin l → Term α), Term α
export Term (var func)
variable {L}
namespace Term
instance instDecidableEq [DecidableEq α] [∀ n, DecidableEq (L.Functions n)] : DecidableEq (L.Term α)
  | .var a, .var b => decidable_of_iff (a = b) <| by simp
  | @Term.func _ _ m f xs, @Term.func _ _ n g ys =>
      if h : m = n then
        letI : DecidableEq (L.Term α) := instDecidableEq
        decidable_of_iff (f = h ▸ g ∧ ∀ i : Fin m, xs i = ys (Fin.cast h i)) <| by
          subst h
          simp [funext_iff]
      else
        .isFalse <| by simp [h]
  | .var _, .func _ _ | .func _ _, .var _ => .isFalse <| by simp
open Finset
@[simp]
def varFinset [DecidableEq α] : L.Term α → Finset α
  | var i => {i}
  | func _f ts => univ.biUnion fun i => (ts i).varFinset
@[simp]
def varFinsetLeft [DecidableEq α] : L.Term (α ⊕ β) → Finset α
  | var (Sum.inl i) => {i}
  | var (Sum.inr _i) => ∅
  | func _f ts => univ.biUnion fun i => (ts i).varFinsetLeft
@[simp]
def relabel (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun {i} => (ts i).relabel g
theorem relabel_id (t : L.Term α) : t.relabel id = t := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]
@[simp]
theorem relabel_id_eq_id : (Term.relabel id : L.Term α → L.Term α) = id :=
  funext relabel_id
@[simp]
theorem relabel_relabel (f : α → β) (g : β → γ) (t : L.Term α) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]
@[simp]
theorem relabel_comp_relabel (f : α → β) (g : β → γ) :
    (Term.relabel g ∘ Term.relabel f : L.Term α → L.Term γ) = Term.relabel (g ∘ f) :=
  funext (relabel_relabel f g)
@[simps]
def relabelEquiv (g : α ≃ β) : L.Term α ≃ L.Term β :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩
def restrictVar [DecidableEq α] : ∀ (t : L.Term α) (_f : t.varFinset → β), L.Term β
  | var a, f => var (f ⟨a, mem_singleton_self a⟩)
  | func F ts, f =>
    func F fun i => (ts i).restrictVar (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => varFinset (ts i)) (mem_univ i)))
def restrictVarLeft [DecidableEq α] {γ : Type*} :
    ∀ (t : L.Term (α ⊕ γ)) (_f : t.varFinsetLeft → β), L.Term (β ⊕ γ)
  | var (Sum.inl a), f => var (Sum.inl (f ⟨a, mem_singleton_self a⟩))
  | var (Sum.inr a), _f => var (Sum.inr a)
  | func F ts, f =>
    func F fun i =>
      (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_biUnion_of_mem
        (fun i => varFinsetLeft (ts i)) (mem_univ i)))
end Term
def Constants.term (c : L.Constants) : L.Term α :=
  func c default
def Functions.apply₁ (f : L.Functions 1) (t : L.Term α) : L.Term α :=
  func f ![t]
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) : L.Term α :=
  func f ![t₁, t₂]
namespace Term
@[simp]
def constantsToVars : L[[γ]].Term α → L.Term (γ ⊕ α)
  | var a => var (Sum.inr a)
  | @func _ _ 0 f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => var (Sum.inl c)
  | @func _ _ (_n + 1) f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => isEmptyElim c
@[simp]
def varsToConstants : L.Term (γ ⊕ α) → L[[γ]].Term α
  | var (Sum.inr a) => var a
  | var (Sum.inl c) => Constants.term (Sum.inr c)
  | func f ts => func (Sum.inl f) fun i => (ts i).varsToConstants
@[simps]
def constantsVarsEquiv : L[[γ]].Term α ≃ L.Term (γ ⊕ α) :=
  ⟨constantsToVars, varsToConstants, by
    intro t
    induction t with
    | var => rfl
    | @func n f _ ih =>
      cases n
      · cases f
        · simp [constantsToVars, varsToConstants, ih]
        · simp [constantsToVars, varsToConstants, Constants.term, eq_iff_true_of_subsingleton]
      · cases' f with f f
        · simp [constantsToVars, varsToConstants, ih]
        · exact isEmptyElim f, by
    intro t
    induction' t with x n f _ ih
    · cases x <;> rfl
    · cases n <;> · simp [varsToConstants, constantsToVars, ih]⟩
def constantsVarsEquivLeft : L[[γ]].Term (α ⊕ β) ≃ L.Term ((γ ⊕ α) ⊕ β) :=
  constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm
@[simp]
theorem constantsVarsEquivLeft_apply (t : L[[γ]].Term (α ⊕ β)) :
    constantsVarsEquivLeft t = (constantsToVars t).relabel (Equiv.sumAssoc _ _ _).symm :=
  rfl
@[simp]
theorem constantsVarsEquivLeft_symm_apply (t : L.Term ((γ ⊕ α) ⊕ β)) :
    constantsVarsEquivLeft.symm t = varsToConstants (t.relabel (Equiv.sumAssoc _ _ _)) :=
  rfl
instance inhabitedOfVar [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩
instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α) :=
  ⟨(default : L.Constants).term⟩
def liftAt {n : ℕ} (n' m : ℕ) : L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin (n + n'))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n')
@[simp]
def subst : L.Term α → (α → L.Term β) → L.Term β
  | var a, tf => tf a
  | func f ts, tf => func f fun i => (ts i).subst tf
end Term
scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr
namespace LHom
open Term
@[simp]
def onTerm (φ : L →ᴸ L') : L.Term α → L'.Term α
  | var i => var i
  | func f ts => func (φ.onFunction f) fun i => onTerm φ (ts i)
@[simp]
theorem id_onTerm : ((LHom.id L).onTerm : L.Term α → L.Term α) = id := by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl
@[simp]
theorem comp_onTerm {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α → L''.Term α) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction t with
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl
end LHom
@[simps]
def Lequiv.onTerm (φ : L ≃ᴸ L') : L.Term α ≃ L'.Term α where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onTerm, φ.left_inv, LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onTerm, φ.right_inv, LHom.id_onTerm]
variable (L) (α)
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : BoundedFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : BoundedFormula n
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n
abbrev Formula :=
  L.BoundedFormula α 0
abbrev Sentence :=
  L.Formula Empty
abbrev Theory :=
  Set L.Sentence
variable {L} {α} {n : ℕ}
def Relations.boundedFormula {l : ℕ} (R : L.Relations n) (ts : Fin n → L.Term (α ⊕ (Fin l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t]
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    L.BoundedFormula α n :=
  r.boundedFormula ![t₁, t₂]
def Term.bdEqual (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂
def Relations.formula (R : L.Relations n) (ts : Fin n → L.Term α) : L.Formula α :=
  R.boundedFormula fun i => (ts i).relabel Sum.inl
def Relations.formula₁ (r : L.Relations 1) (t : L.Term α) : L.Formula α :=
  r.formula ![t]
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : L.Formula α :=
  r.formula ![t₁, t₂]
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)
namespace BoundedFormula
instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩
instance : Bot (L.BoundedFormula α n) :=
  ⟨falsum⟩
@[match_pattern]
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥
@[match_pattern]
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.not.all.not
instance : Top (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩
instance : Min (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.not).not⟩
instance : Max (L.BoundedFormula α n) :=
  ⟨fun f g => f.not.imp g⟩
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ ⊓ ψ.imp φ
open Finset
@[simp]
def freeVarFinset [DecidableEq α] : ∀ {n}, L.BoundedFormula α n → Finset α
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all f => f.freeVarFinset
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
  | _m, _n, _h, falsum => falsum
  | _m, _n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _m, _n, h, rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLE h)) ∘ ts)
  | _m, _n, h, imp f₁ f₂ => (f₁.castLE h).imp (f₂.castLE h)
  | _m, _n, h, all f => (f.castLE (add_le_add_right h 1)).all
@[simp]
theorem castLE_rfl {n} (h : n ≤ n) (φ : L.BoundedFormula α n) : φ.castLE h = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp [Fin.castLE_of_eq]
  | rel => simp [Fin.castLE_of_eq]
  | imp _ _ ih1 ih2 => simp [Fin.castLE_of_eq, ih1, ih2]
  | all _ ih3 => simp [Fin.castLE_of_eq, ih3]
@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.BoundedFormula α k) :
    (φ.castLE km).castLE mn = φ.castLE (km.trans mn) := by
  revert m n
  induction φ with
  | falsum => intros; rfl
  | equal => simp
  | rel =>
    intros
    simp only [castLE, eq_self_iff_true, heq_iff_eq]
    rw [← Function.comp_assoc, Term.relabel_comp_relabel]
    simp
  | imp _ _ ih1 ih2 => simp [ih1, ih2]
  | all _ ih3 => intros; simp only [castLE, ih3]
@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedFormula.castLE mn ∘ BoundedFormula.castLE km :
        L.BoundedFormula α k → L.BoundedFormula α n) =
      BoundedFormula.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)
def restrictFreeVar [DecidableEq α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (_f : φ.freeVarFinset → β), L.BoundedFormula β n
  | _n, falsum, _f => falsum
  | _n, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (f ∘ Set.inclusion subset_union_left))
      (t₂.restrictVarLeft (f ∘ Set.inclusion subset_union_right))
  | _n, rel R ts, f =>
    rel R fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion
      (subset_biUnion_of_mem (fun i => Term.varFinsetLeft (ts i)) (mem_univ i)))
  | _n, imp φ₁ φ₂, f =>
    (φ₁.restrictFreeVar (f ∘ Set.inclusion subset_union_left)).imp
      (φ₂.restrictFreeVar (f ∘ Set.inclusion subset_union_right))
  | _n, all φ, f => (φ.restrictFreeVar f).all
def alls : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.all.alls
def exs : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | _n + 1, φ => φ.ex.exs
def mapTermRel {g : ℕ → ℕ} (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin (g n))))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)) :
    ∀ {n}, L.BoundedFormula α n → L'.BoundedFormula β (g n)
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => equal (ft _ t₁) (ft _ t₂)
  | _n, rel R ts => rel (fr _ R) fun i => ft _ (ts i)
  | _n, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | n, all φ => (h n (φ.mapTermRel ft fr h)).all
def liftAt : ∀ {n : ℕ} (n' _m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') :=
  fun {_} n' m φ =>
  φ.mapTermRel (fun _ t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])
@[simp]
theorem mapTermRel_mapTermRel {L'' : Language}
    (ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (ft' : ∀ n, L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ (Fin n)))
    (fr' : ∀ n, L'.Relations n → L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]
@[simp]
theorem mapTermRel_id_id_id {n} (φ : L.BoundedFormula α n) :
    (φ.mapTermRel (fun _ => id) (fun _ => id) fun _ => id) = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel]
  | rel => simp [mapTermRel]
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih3 => simp [mapTermRel, ih3]
@[simps]
def mapTermRelEquiv (ft : ∀ n, L.Term (α ⊕ (Fin n)) ≃ L'.Term (β ⊕ (Fin n)))
    (fr : ∀ n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩
def relabelAux (g : α → β ⊕ (Fin n)) (k : ℕ) : α ⊕ (Fin k) → β ⊕ (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id
@[simp]
theorem sum_elim_comp_relabelAux {m : ℕ} {g : α → β ⊕ (Fin n)} {v : β → M}
    {xs : Fin (n + m) → M} : Sum.elim v xs ∘ relabelAux g m =
    Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
  ext x
  cases' x with x x
  · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    cases' g x with l r <;> simp
  · simp [BoundedFormula.relabelAux]
@[simp]
theorem relabelAux_sum_inl (k : ℕ) :
    relabelAux (Sum.inl : α → α ⊕ (Fin n)) k = Sum.map id (natAdd n) := by
  ext x
  cases x <;> · simp [relabelAux]
def relabel (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))
def relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k :=
  mapTermRelEquiv (fun _n => Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
    fun _n => _root_.Equiv.refl _
@[simp]
theorem relabel_falsum (g : α → β ⊕ (Fin n)) {k} :
    (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl
@[simp]
theorem relabel_bot (g : α → β ⊕ (Fin n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl
@[simp]
theorem relabel_imp (g : α → β ⊕ (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl
@[simp]
theorem relabel_not (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α k) :
    φ.not.relabel g = (φ.relabel g).not := by simp [BoundedFormula.not]
@[simp]
theorem relabel_all (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all := by
  rw [relabel, mapTermRel, relabel]
  simp
@[simp]
theorem relabel_ex (g : α → β ⊕ (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabel g = (φ.relabel g).ex := by simp [BoundedFormula.ex]
@[simp]
theorem relabel_sum_inl (φ : L.BoundedFormula α n) :
    (φ.relabel Sum.inl : L.BoundedFormula α (0 + n)) = φ.castLE (ge_of_eq (zero_add n)) := by
  simp only [relabel, relabelAux_sum_inl]
  induction φ with
  | falsum => rfl
  | equal => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]
  | rel => simp [Fin.natAdd_zero, castLE_of_eq, mapTermRel]; rfl
  | imp _ _ ih1 ih2 => simp_all [mapTermRel]
  | all _ ih3 => simp_all [mapTermRel]
def subst {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id
def constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (γ ⊕ α) n :=
  mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _
@[simp]
def toFormula : ∀ {n : ℕ}, L.BoundedFormula α n → L.Formula (α ⊕ (Fin n))
  | _n, falsum => falsum
  | _n, equal t₁ t₂ => t₁.equal t₂
  | _n, rel R ts => R.formula ts
  | _n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | _n, all φ =>
    (φ.toFormula.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all
noncomputable def iSup (s : Finset β) (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (s.toList.map f).foldr (· ⊔ ·) ⊥
noncomputable def iInf (s : Finset β) (f : β → L.BoundedFormula α n) : L.BoundedFormula α n :=
  (s.toList.map f).foldr (· ⊓ ·) ⊤
end BoundedFormula
namespace LHom
open BoundedFormula
@[simp]
def onBoundedFormula (g : L →ᴸ L') : ∀ {k : ℕ}, L.BoundedFormula α k → L'.BoundedFormula α k
  | _k, falsum => falsum
  | _k, equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | _k, rel R ts => (g.onRelation R).boundedFormula (g.onTerm ∘ ts)
  | _k, imp f₁ f₂ => (onBoundedFormula g f₁).imp (onBoundedFormula g f₂)
  | _k, all f => (onBoundedFormula g f).all
@[simp]
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α n → L.BoundedFormula α n) = id := by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => rw [onBoundedFormula, LHom.id_onTerm]; rfl
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ ih3 => rw [onBoundedFormula, ih3, id, id]
@[simp]
theorem comp_onBoundedFormula {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α n → L''.BoundedFormula α n) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula := by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp only [onBoundedFormula, comp_onTerm, Function.comp_apply]
  | rel => simp only [onBoundedFormula, comp_onRelation, comp_onTerm, Function.comp_apply]; rfl
  | imp _ _ ih1 ih2 =>
    simp only [onBoundedFormula, Function.comp_apply, ih1, ih2, eq_self_iff_true, and_self_iff]
  | all _ ih3 => simp only [ih3, onBoundedFormula, Function.comp_apply]
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula
def onTheory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T
@[simp]
theorem mem_onTheory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ ∈ g.onTheory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _
end LHom
namespace LEquiv
@[simps]
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula α n where
  toFun := φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.left_inv,
      LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.right_inv,
      LHom.id_onBoundedFormula]
theorem onBoundedFormula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α n ≃ L.BoundedFormula α n) =
      φ.symm.onBoundedFormula :=
  rfl
def onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α :=
  φ.onBoundedFormula
@[simp]
theorem onFormula_apply (φ : L ≃ᴸ L') :
    (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLHom.onFormula :=
  rfl
@[simp]
theorem onFormula_symm (φ : L ≃ᴸ L') :
    (φ.onFormula.symm : L'.Formula α ≃ L.Formula α) = φ.symm.onFormula :=
  rfl
@[simps!] 
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula
end LEquiv
scoped[FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual
scoped[FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp
scoped[FirstOrder] prefix:110 "∀'" => FirstOrder.Language.BoundedFormula.all
scoped[FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not
scoped[FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff
scoped[FirstOrder] prefix:110 "∃'" => FirstOrder.Language.BoundedFormula.ex
namespace Formula
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0
def graph (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  Term.equal (var 0) (func f fun i => var i.succ)
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not
protected abbrev imp : L.Formula α → L.Formula α → L.Formula α :=
  BoundedFormula.imp
noncomputable def iAlls [Finite γ] (f : α → β ⊕ γ)
    (φ : L.Formula α) : L.Formula β :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  (BoundedFormula.relabel (fun a => Sum.map id e (f a)) φ).alls
noncomputable def iExs [Finite γ] (f : α → β ⊕ γ)
    (φ : L.Formula α) : L.Formula β :=
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  (BoundedFormula.relabel (fun a => Sum.map id e (f a)) φ).exs
protected nonrec abbrev iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.iff ψ
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm
theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  rfl
theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  rfl
end Formula
namespace Relations
variable (r : L.Relations 2)
protected def reflexive : L.Sentence :=
  ∀'r.boundedFormula₂ (&0) &0
protected def irreflexive : L.Sentence :=
  ∀'∼(r.boundedFormula₂ (&0) &0)
protected def symmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)
protected def antisymmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)
protected def transitive : L.Sentence :=
  ∀'∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)
protected def total : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)
end Relations
section Cardinality
variable (L)
protected def Sentence.cardGe (n : ℕ) : L.Sentence :=
  ((((List.finRange n ×ˢ List.finRange n).filter fun ij : _ × _ => ij.1 ≠ ij.2).map
          fun ij : _ × _ => ∼((&ij.1).bdEqual &ij.2)).foldr
      (· ⊓ ·) ⊤).exs
def infiniteTheory : L.Theory :=
  Set.range (Sentence.cardGe L)
def nonemptyTheory : L.Theory :=
  {Sentence.cardGe L 1}
def distinctConstantsTheory (s : Set α) : L[[α]].Theory :=
  (fun ab : α × α => ((L.con ab.1).term.equal (L.con ab.2).term).not) ''
  (s ×ˢ s ∩ (Set.diagonal α)ᶜ)
variable {L}
open Set
theorem distinctConstantsTheory_mono {s t : Set α} (h : s ⊆ t) :
    L.distinctConstantsTheory s ⊆ L.distinctConstantsTheory t := by
  unfold distinctConstantsTheory; gcongr
theorem monotone_distinctConstantsTheory :
    Monotone (L.distinctConstantsTheory : Set α → L[[α]].Theory) := fun _s _t st =>
  L.distinctConstantsTheory_mono st
theorem directed_distinctConstantsTheory :
    Directed (· ⊆ ·) (L.distinctConstantsTheory : Set α → L[[α]].Theory) :=
  Monotone.directed_le monotone_distinctConstantsTheory
theorem distinctConstantsTheory_eq_iUnion (s : Set α) :
    L.distinctConstantsTheory s =
      ⋃ t : Finset s,
        L.distinctConstantsTheory (t.map (Function.Embedding.subtype fun x => x ∈ s)) := by
  classical
    simp only [distinctConstantsTheory]
    rw [← image_iUnion, ← iUnion_inter]
    refine congr(_ '' ($(?_) ∩ _))
    ext ⟨i, j⟩
    simp only [prod_mk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_iUnion,
      mem_image, Finset.mem_coe, Subtype.exists, Subtype.coe_mk, exists_and_right, exists_eq_right]
    refine ⟨fun h => ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, ?_⟩, ⟨h.2, ?_⟩⟩, ?_⟩
    · simp
    · simp
    · rintro ⟨t, ⟨is, _⟩, ⟨js, _⟩⟩
      exact ⟨is, js⟩
end Cardinality
end Language
end FirstOrder