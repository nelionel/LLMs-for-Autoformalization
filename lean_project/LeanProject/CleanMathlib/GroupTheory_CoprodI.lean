import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Pointwise.SMul
open Set
variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)]
inductive Monoid.CoprodI.Rel : FreeMonoid (Σi, M i) → FreeMonoid (Σi, M i) → Prop
  | of_one (i : ι) : Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, 1⟩) 1
  | of_mul {i : ι} (x y : M i) :
    Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, x⟩ * FreeMonoid.of ⟨i, y⟩) (FreeMonoid.of ⟨i, x * y⟩)
def Monoid.CoprodI : Type _ := (conGen (Monoid.CoprodI.Rel M)).Quotient
instance : Monoid (Monoid.CoprodI M) := by
  delta Monoid.CoprodI; infer_instance
instance : Inhabited (Monoid.CoprodI M) :=
  ⟨1⟩
namespace Monoid.CoprodI
@[ext]
structure Word where
  toList : List (Σi, M i)
  ne_one : ∀ l ∈ toList, Sigma.snd l ≠ 1
  chain_ne : toList.Chain' fun l l' => Sigma.fst l ≠ Sigma.fst l'
variable {M}
def of {i : ι} : M i →* CoprodI M where
  toFun x := Con.mk' _ (FreeMonoid.of <| Sigma.mk i x)
  map_one' := (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_one i))
  map_mul' x y := Eq.symm <| (Con.eq _).mpr (ConGen.Rel.of _ _ (CoprodI.Rel.of_mul x y))
theorem of_apply {i} (m : M i) : of m = Con.mk' _ (FreeMonoid.of <| Sigma.mk i m) :=
  rfl
variable {N : Type*} [Monoid N]
@[ext 1100]
theorem ext_hom (f g : CoprodI M →* N) (h : ∀ i, f.comp (of : M i →* _) = g.comp of) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    FreeMonoid.hom_eq fun ⟨i, x⟩ => by
      erw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← of_apply, ← MonoidHom.comp_apply, ←
        MonoidHom.comp_apply, h]; rfl
@[simps symm_apply]
def lift : (∀ i, M i →* N) ≃ (CoprodI M →* N) where
  toFun fi :=
    Con.lift _ (FreeMonoid.lift fun p : Σi, M i => fi p.fst p.snd) <|
      Con.conGen_le <| by
        simp_rw [Con.ker_rel]
        rintro _ _ (i | ⟨x, y⟩)
        · change FreeMonoid.lift _ (FreeMonoid.of _) = FreeMonoid.lift _ 1
          simp only [MonoidHom.map_one, FreeMonoid.lift_eval_of]
        · change
            FreeMonoid.lift _ (FreeMonoid.of _ * FreeMonoid.of _) =
              FreeMonoid.lift _ (FreeMonoid.of _)
          simp only [MonoidHom.map_mul, FreeMonoid.lift_eval_of]
  invFun f _ := f.comp of
  left_inv := by
    intro fi
    ext i x
    erw [MonoidHom.comp_apply, of_apply, Con.lift_mk', FreeMonoid.lift_eval_of]
  right_inv := by
    intro f
    ext i x
    rfl
@[simp]
theorem lift_comp_of {N} [Monoid N] (fi : ∀ i, M i →* N) i : (lift fi).comp of = fi i :=
  congr_fun (lift.symm_apply_apply fi) i
@[simp]
theorem lift_of {N} [Monoid N] (fi : ∀ i, M i →* N) {i} (m : M i) : lift fi (of m) = fi i m :=
  DFunLike.congr_fun (lift_comp_of ..) m
@[simp]
theorem lift_comp_of' {N} [Monoid N] (f : CoprodI M →* N) :
    lift (fun i ↦ f.comp (of (i := i))) = f :=
  lift.apply_symm_apply f
@[simp]
theorem lift_of' : lift (fun i ↦ (of : M i →* CoprodI M)) = .id (CoprodI M) :=
  lift_comp_of' (.id _)
theorem of_leftInverse [DecidableEq ι] (i : ι) :
    Function.LeftInverse (lift <| Pi.mulSingle i (MonoidHom.id (M i))) of := fun x => by
  simp only [lift_of, Pi.mulSingle_eq_same, MonoidHom.id_apply]
theorem of_injective (i : ι) : Function.Injective (of : M i →* _) := by
  classical exact (of_leftInverse i).injective
theorem mrange_eq_iSup {N} [Monoid N] (f : ∀ i, M i →* N) :
    MonoidHom.mrange (lift f) = ⨆ i, MonoidHom.mrange (f i) := by
  rw [lift, Equiv.coe_fn_mk, Con.lift_range, FreeMonoid.mrange_lift,
    range_sigma_eq_iUnion_range, Submonoid.closure_iUnion]
  simp only [MonoidHom.mclosure_range]
theorem lift_mrange_le {N} [Monoid N] (f : ∀ i, M i →* N) {s : Submonoid N} :
    MonoidHom.mrange (lift f) ≤ s ↔ ∀ i, MonoidHom.mrange (f i) ≤ s := by
  simp [mrange_eq_iSup]
@[simp]
theorem iSup_mrange_of : ⨆ i, MonoidHom.mrange (of : M i →* CoprodI M) = ⊤ := by
  simp [← mrange_eq_iSup]
@[simp]
theorem mclosure_iUnion_range_of :
    Submonoid.closure (⋃ i, Set.range (of : M i →* CoprodI M)) = ⊤ := by
  simp [Submonoid.closure_iUnion]
@[elab_as_elim]
theorem induction_left {C : CoprodI M → Prop} (m : CoprodI M) (one : C 1)
    (mul : ∀ {i} (m : M i) x, C x → C (of m * x)) : C m := by
  induction m using Submonoid.induction_of_closure_eq_top_left mclosure_iUnion_range_of with
  | one => exact one
  | mul x hx y ihy =>
    obtain ⟨i, m, rfl⟩ : ∃ (i : ι) (m : M i), of m = x := by simpa using hx
    exact mul m y ihy
@[elab_as_elim]
theorem induction_on {C : CoprodI M → Prop} (m : CoprodI M) (h_one : C 1)
    (h_of : ∀ (i) (m : M i), C (of m)) (h_mul : ∀ x y, C x → C y → C (x * y)) : C m := by
  induction m using CoprodI.induction_left with
  | one => exact h_one
  | mul m x hx => exact h_mul _ _ (h_of _ _) hx
section Group
variable (G : ι → Type*) [∀ i, Group (G i)]
instance : Inv (CoprodI G) where
  inv :=
    MulOpposite.unop ∘ lift fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom
theorem inv_def (x : CoprodI G) :
    x⁻¹ =
      MulOpposite.unop
        (lift (fun i => (of : G i →* _).op.comp (MulEquiv.inv' (G i)).toMonoidHom) x) :=
  rfl
instance : Group (CoprodI G) :=
  { inv_mul_cancel := by
      intro m
      rw [inv_def]
      induction m using CoprodI.induction_on with
      | h_one => rw [MonoidHom.map_one, MulOpposite.unop_one, one_mul]
      | h_of m ih =>
        change of _⁻¹ * of _ = 1
        rw [← of.map_mul, inv_mul_cancel, of.map_one]
      | h_mul x y ihx ihy =>
        rw [MonoidHom.map_mul, MulOpposite.unop_mul, mul_assoc, ← mul_assoc _ x y, ihx, one_mul,
          ihy] }
theorem lift_range_le {N} [Group N] (f : ∀ i, G i →* N) {s : Subgroup N}
    (h : ∀ i, (f i).range ≤ s) : (lift f).range ≤ s := by
  rintro _ ⟨x, rfl⟩
  induction' x using CoprodI.induction_on with i x x y hx hy
  · exact s.one_mem
  · simp only [lift_of, SetLike.mem_coe]
    exact h i (Set.mem_range_self x)
  · simp only [map_mul, SetLike.mem_coe]
    exact s.mul_mem hx hy
theorem range_eq_iSup {N} [Group N] (f : ∀ i, G i →* N) : (lift f).range = ⨆ i, (f i).range := by
  apply le_antisymm (lift_range_le _ f fun i => le_iSup (fun i => MonoidHom.range (f i)) i)
  apply iSup_le _
  rintro i _ ⟨x, rfl⟩
  exact ⟨of x, by simp only [lift_of]⟩
end Group
namespace Word
@[simps]
def empty : Word M where
  toList := []
  ne_one := by simp
  chain_ne := List.chain'_nil
instance : Inhabited (Word M) :=
  ⟨empty⟩
def prod (w : Word M) : CoprodI M :=
  List.prod (w.toList.map fun l => of l.snd)
@[simp]
theorem prod_empty : prod (empty : Word M) = 1 :=
  rfl
def fstIdx (w : Word M) : Option ι :=
  w.toList.head?.map Sigma.fst
theorem fstIdx_ne_iff {w : Word M} {i} :
    fstIdx w ≠ some i ↔ ∀ l ∈ w.toList.head?, i ≠ Sigma.fst l :=
  not_iff_not.mp <| by simp [fstIdx]
variable (M)
@[ext]
structure Pair (i : ι) where
  head : M i
  tail : Word M
  fstIdx_ne : fstIdx tail ≠ some i
instance (i : ι) : Inhabited (Pair M i) :=
  ⟨⟨1, empty, by tauto⟩⟩
variable {M}
@[simps]
def cons {i} (m : M i) (w : Word M) (hmw : w.fstIdx ≠ some i) (h1 : m ≠ 1) : Word M :=
  { toList := ⟨i, m⟩ :: w.toList,
    ne_one := by
      simp only [List.mem_cons]
      rintro l (rfl | hl)
      · exact h1
      · exact w.ne_one l hl
    chain_ne := w.chain_ne.cons' (fstIdx_ne_iff.mp hmw) }
@[simp]
theorem fstIdx_cons {i} (m : M i) (w : Word M) (hmw : w.fstIdx ≠ some i) (h1 : m ≠ 1) :
    fstIdx (cons m w hmw h1) = some i := by simp [cons, fstIdx]
@[simp]
theorem prod_cons (i) (m : M i) (w : Word M) (h1 : m ≠ 1) (h2 : w.fstIdx ≠ some i) :
    prod (cons m w h2 h1) = of m * prod w := by
  simp [cons, prod, List.map_cons, List.prod_cons]
section
variable [∀ i, DecidableEq (M i)]
def rcons {i} (p : Pair M i) : Word M :=
  if h : p.head = 1 then p.tail
  else cons p.head p.tail p.fstIdx_ne h
@[simp]
theorem prod_rcons {i} (p : Pair M i) : prod (rcons p) = of p.head * prod p.tail :=
  if hm : p.head = 1 then by rw [rcons, dif_pos hm, hm, MonoidHom.map_one, one_mul]
  else by rw [rcons, dif_neg hm, cons, prod, List.map_cons, List.prod_cons, prod]
theorem rcons_inj {i} : Function.Injective (rcons : Pair M i → Word M) := by
  rintro ⟨m, w, h⟩ ⟨m', w', h'⟩ he
  by_cases hm : m = 1 <;> by_cases hm' : m' = 1
  · simp only [rcons, dif_pos hm, dif_pos hm'] at he
    aesop
  · exfalso
    simp only [rcons, dif_pos hm, dif_neg hm'] at he
    rw [he] at h
    exact h rfl
  · exfalso
    simp only [rcons, dif_pos hm', dif_neg hm] at he
    rw [← he] at h'
    exact h' rfl
  · have : m = m' ∧ w.toList = w'.toList := by
      simpa [cons, rcons, dif_neg hm, dif_neg hm', eq_self_iff_true, Subtype.mk_eq_mk,
        heq_iff_eq, ← Subtype.ext_iff_val] using he
    rcases this with ⟨rfl, h⟩
    congr
    exact Word.ext h
theorem mem_rcons_iff {i j : ι} (p : Pair M i) (m : M j) :
    ⟨_, m⟩ ∈ (rcons p).toList ↔ ⟨_, m⟩ ∈ p.tail.toList ∨
      m ≠ 1 ∧ (∃ h : i = j, m = h ▸ p.head) := by
  simp only [rcons, cons, ne_eq]
  by_cases hij : i = j
  · subst i
    by_cases hm : m = p.head
    · subst m
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  · split_ifs <;> simp_all [Ne.symm hij]
end
@[elab_as_elim]
def consRecOn {motive : Word M → Sort*} (w : Word M) (h_empty : motive empty)
    (h_cons : ∀ (i) (m : M i) (w) h1 h2, motive w → motive (cons m w h1 h2)) :
    motive w := by
  rcases w with ⟨w, h1, h2⟩
  induction w with
  | nil => exact h_empty
  | cons m w ih =>
    refine h_cons m.1 m.2 ⟨w, fun _ hl => h1 _ (List.mem_cons_of_mem _ hl), h2.tail⟩ ?_ ?_ (ih _ _)
    · rw [List.chain'_cons'] at h2
      simp only [fstIdx, ne_eq, Option.map_eq_some',
        Sigma.exists, exists_and_right, exists_eq_right, not_exists]
      intro m' hm'
      exact h2.1 _ hm' rfl
    · exact h1 _ (List.mem_cons_self _ _)
@[simp]
theorem consRecOn_empty {motive : Word M → Sort*} (h_empty : motive empty)
    (h_cons : ∀ (i) (m : M i) (w) h1 h2, motive w → motive (cons m w h1 h2)) :
    consRecOn empty h_empty h_cons = h_empty := rfl
@[simp]
theorem consRecOn_cons {motive : Word M → Sort*} (i) (m : M i) (w : Word M) h1 h2
    (h_empty : motive empty)
    (h_cons : ∀ (i) (m : M i) (w) h1 h2, motive w → motive (cons m w h1 h2)) :
    consRecOn (cons m w h1 h2) h_empty h_cons = h_cons i m w h1 h2
      (consRecOn w h_empty h_cons) := rfl
variable [DecidableEq ι] [∀ i, DecidableEq (M i)]
private def equivPairAux (i) (w : Word M) : { p : Pair M i // rcons p = w } :=
  consRecOn w ⟨⟨1, .empty, by simp [fstIdx, empty]⟩, by simp [rcons]⟩ <|
    fun j m w h1 h2 _ =>
      if ij : i = j then
        { val :=
          { head := ij ▸ m
            tail := w
            fstIdx_ne := ij ▸ h1 }
          property := by subst ij; simp [rcons, h2] }
      else ⟨⟨1, cons m w h1 h2, by simp [cons, fstIdx, Ne.symm ij]⟩,  by simp [rcons]⟩
def equivPair (i) : Word M ≃ Pair M i where
  toFun w := (equivPairAux i w).val
  invFun := rcons
  left_inv w := (equivPairAux i w).property
  right_inv _ := rcons_inj (equivPairAux i _).property
theorem equivPair_symm (i) (p : Pair M i) : (equivPair i).symm p = rcons p :=
  rfl
theorem equivPair_eq_of_fstIdx_ne {i} {w : Word M} (h : fstIdx w ≠ some i) :
    equivPair i w = ⟨1, w, h⟩ :=
  (equivPair i).apply_eq_iff_eq_symm_apply.mpr <| Eq.symm (dif_pos rfl)
theorem mem_equivPair_tail_iff {i j : ι} {w : Word M} (m : M i) :
    (⟨i, m⟩ ∈ (equivPair j w).tail.toList) ↔ ⟨i, m⟩ ∈ w.toList.tail
      ∨ i ≠ j ∧ ∃ h : w.toList ≠ [], w.toList.head h = ⟨i, m⟩ := by
  simp only [equivPair, equivPairAux, ne_eq, Equiv.coe_fn_mk]
  induction w using consRecOn with
  | h_empty => simp
  | h_cons k g tail h1 h2 ih =>
    simp only [consRecOn_cons]
    split_ifs with h
    · subst k
      by_cases hij : j = i <;> simp_all
    · by_cases hik : i = k
      · subst i; simp_all [@eq_comm _ m g, @eq_comm _ k j, or_comm]
      · simp [hik, Ne.symm hik]
theorem mem_of_mem_equivPair_tail {i j : ι} {w : Word M} (m : M i) :
    (⟨i, m⟩ ∈ (equivPair j w).tail.toList) → ⟨i, m⟩ ∈ w.toList := by
  rw [mem_equivPair_tail_iff]
  rintro (h | h)
  · exact List.mem_of_mem_tail h
  · revert h; cases w.toList <;> simp (config := {contextual := true})
theorem equivPair_head {i : ι} {w : Word M} :
    (equivPair i w).head =
      if h : ∃ (h : w.toList ≠ []), (w.toList.head h).1 = i
      then h.snd ▸ (w.toList.head h.1).2
      else 1 := by
  simp only [equivPair, equivPairAux]
  induction w using consRecOn with
  | h_empty => simp
  | h_cons head =>
    by_cases hi : i = head
    · subst hi; simp
    · simp [hi, Ne.symm hi]
instance summandAction (i) : MulAction (M i) (Word M) where
  smul m w := rcons { equivPair i w with head := m * (equivPair i w).head }
  one_smul w := by
    apply (equivPair i).symm_apply_eq.mpr
    simp [equivPair]
  mul_smul m m' w := by
    dsimp [instHSMul]
    simp [mul_assoc, ← equivPair_symm, Equiv.apply_symm_apply]
instance : MulAction (CoprodI M) (Word M) :=
  MulAction.ofEndHom (lift fun _ => MulAction.toEndHom)
theorem smul_def {i} (m : M i) (w : Word M) :
    m • w = rcons { equivPair i w with head := m * (equivPair i w).head } :=
  rfl
theorem of_smul_def (i) (w : Word M) (m : M i) :
    of m • w = rcons { equivPair i w with head := m * (equivPair i w).head } :=
  rfl
theorem equivPair_smul_same {i} (m : M i) (w : Word M) :
    equivPair i (of m • w) = ⟨m * (equivPair i w).head, (equivPair i w).tail,
      (equivPair i w).fstIdx_ne⟩ := by
  rw [of_smul_def, ← equivPair_symm]
  simp
@[simp]
theorem equivPair_tail {i} (p : Pair M i) :
    equivPair i p.tail = ⟨1, p.tail, p.fstIdx_ne⟩ :=
  equivPair_eq_of_fstIdx_ne _
theorem smul_eq_of_smul {i} (m : M i) (w : Word M) :
    m • w = of m • w := rfl
theorem mem_smul_iff {i j : ι} {m₁ : M i} {m₂ : M j} {w : Word M} :
    ⟨_, m₁⟩ ∈ (of m₂ • w).toList ↔
      (¬i = j ∧ ⟨i, m₁⟩ ∈ w.toList)
      ∨ (m₁ ≠ 1 ∧ ∃ (hij : i = j),(⟨i, m₁⟩ ∈ w.toList.tail) ∨
        (∃ m', ⟨j, m'⟩ ∈ w.toList.head? ∧ m₁ = hij ▸ (m₂ * m')) ∨
        (w.fstIdx ≠ some j ∧ m₁ = hij ▸ m₂)) := by
  rw [of_smul_def, mem_rcons_iff, mem_equivPair_tail_iff, equivPair_head, or_assoc]
  by_cases hij : i = j
  · subst i
    simp only [not_true, ne_eq, false_and, exists_prop, true_and, false_or]
    by_cases hw : ⟨j, m₁⟩ ∈ w.toList.tail
    · simp [hw, show m₁ ≠ 1 from w.ne_one _ (List.mem_of_mem_tail hw)]
    · simp only [hw, false_or, Option.mem_def, ne_eq, and_congr_right_iff]
      intro hm1
      split_ifs with h
      · rcases h with ⟨hnil, rfl⟩
        simp only [List.head?_eq_head hnil, Option.some.injEq, ne_eq]
        constructor
        · rintro rfl
          exact Or.inl ⟨_, rfl, rfl⟩
        · rintro (⟨_, h, rfl⟩ | hm')
          · simp only [Sigma.ext_iff, heq_eq_eq, true_and] at h
            subst h
            rfl
          · simp only [fstIdx, Option.map_eq_some', Sigma.exists,
              exists_and_right, exists_eq_right, not_exists, ne_eq] at hm'
            exact (hm'.1 (w.toList.head hnil).2 (by rw [List.head?_eq_head])).elim
      · revert h
        rw [fstIdx]
        cases w.toList
        · simp
        · simp (config := {contextual := true}) [Sigma.ext_iff]
  · rcases w with ⟨_ | _, _, _⟩ <;>
    simp [or_comm, hij, Ne.symm hij]; rw [eq_comm]
theorem mem_smul_iff_of_ne {i j : ι} (hij : i ≠ j) {m₁ : M i} {m₂ : M j} {w : Word M} :
    ⟨_, m₁⟩ ∈ (of m₂ • w).toList ↔ ⟨i, m₁⟩ ∈ w.toList := by
  simp [mem_smul_iff, *]
theorem cons_eq_smul {i} {m : M i} {ls h1 h2} :
    cons m ls h1 h2 = of m • ls := by
  rw [of_smul_def, equivPair_eq_of_fstIdx_ne _]
  · simp [cons, rcons, h2]
  · exact h1
theorem rcons_eq_smul {i} (p : Pair M i) :
    rcons p = of p.head • p.tail := by
  simp [of_smul_def]
@[simp]
theorem equivPair_head_smul_equivPair_tail {i : ι} (w : Word M) :
    of (equivPair i w).head • (equivPair i w).tail = w := by
  rw [← rcons_eq_smul, ← equivPair_symm, Equiv.symm_apply_apply]
theorem equivPair_tail_eq_inv_smul {G : ι → Type*} [∀ i, Group (G i)]
    [∀i, DecidableEq (G i)] {i} (w : Word G) :
    (equivPair i w).tail = (of (equivPair i w).head)⁻¹ • w :=
  Eq.symm <| inv_smul_eq_iff.2 (equivPair_head_smul_equivPair_tail w).symm
theorem smul_induction {C : Word M → Prop} (h_empty : C empty)
    (h_smul : ∀ (i) (m : M i) (w), C w → C (of m • w)) (w : Word M) : C w := by
  induction w using consRecOn with
  | h_empty => exact h_empty
  | h_cons _ _ _ _ _ ih =>
    rw [cons_eq_smul]
    exact h_smul _ _ _ ih
@[simp]
theorem prod_smul (m) : ∀ w : Word M, prod (m • w) = m * prod w := by
  induction m using CoprodI.induction_on with
  | h_one =>
    intro
    rw [one_smul, one_mul]
  | h_of _ =>
    intros
    rw [of_smul_def, prod_rcons, of.map_mul, mul_assoc, ← prod_rcons, ← equivPair_symm,
      Equiv.symm_apply_apply]
  | h_mul x y hx hy =>
    intro w
    rw [mul_smul, hx, hy, mul_assoc]
def equiv : CoprodI M ≃ Word M where
  toFun m := m • empty
  invFun w := prod w
  left_inv m := by dsimp only; rw [prod_smul, prod_empty, mul_one]
  right_inv := by
    apply smul_induction
    · dsimp only
      rw [prod_empty, one_smul]
    · dsimp only
      intro i m w ih
      rw [prod_smul, mul_smul, ih]
instance : DecidableEq (Word M) :=
  Function.Injective.decidableEq fun _ _ => Word.ext
instance : DecidableEq (CoprodI M) :=
  Equiv.decidableEq Word.equiv
end Word
variable (M)
inductive NeWord : ι → ι → Type _
  | singleton : ∀ {i : ι} (x : M i), x ≠ 1 → NeWord i i
  | append : ∀ {i j k l} (_w₁ : NeWord i j) (_hne : j ≠ k) (_w₂ : NeWord k l), NeWord i l
variable {M}
namespace NeWord
open Word
@[simp]
def toList : ∀ {i j} (_w : NeWord M i j), List (Σi, M i)
  | i, _, singleton x _ => [⟨i, x⟩]
  | _, _, append w₁ _ w₂ => w₁.toList ++ w₂.toList
theorem toList_ne_nil {i j} (w : NeWord M i j) : w.toList ≠ List.nil := by
  induction w
  · rintro ⟨rfl⟩
  · apply List.append_ne_nil_of_left_ne_nil
    assumption
@[simp]
def head : ∀ {i j} (_w : NeWord M i j), M i
  | _, _, singleton x _ => x
  | _, _, append w₁ _ _ => w₁.head
@[simp]
def last : ∀ {i j} (_w : NeWord M i j), M j
  | _, _, singleton x _hne1 => x
  | _, _, append _w₁ _hne w₂ => w₂.last
@[simp]
theorem toList_head? {i j} (w : NeWord M i j) : w.toList.head? = Option.some ⟨i, w.head⟩ := by
  rw [← Option.mem_def]
  induction w
  · rw [Option.mem_def]
    rfl
  · exact List.mem_head?_append_of_mem_head? (by assumption)
@[simp]
theorem toList_getLast? {i j} (w : NeWord M i j) : w.toList.getLast? = Option.some ⟨j, w.last⟩ := by
  rw [← Option.mem_def]
  induction w
  · rw [Option.mem_def]
    rfl
  · exact List.mem_getLast?_append_of_mem_getLast? (by assumption)
def toWord {i j} (w : NeWord M i j) : Word M where
  toList := w.toList
  ne_one := by
    induction w
    · simpa only [toList, List.mem_singleton, ne_eq, forall_eq]
    · intro l h
      simp only [toList, List.mem_append] at h
      cases h <;> aesop
  chain_ne := by
    induction w
    · exact List.chain'_singleton _
    · refine List.Chain'.append (by assumption) (by assumption) ?_
      intro x hx y hy
      rw [toList_getLast?, Option.mem_some_iff] at hx
      rw [toList_head?, Option.mem_some_iff] at hy
      subst hx
      subst hy
      assumption
theorem of_word (w : Word M) (h : w ≠ empty) : ∃ (i j : _) (w' : NeWord M i j), w'.toWord = w := by
  suffices ∃ (i j : _) (w' : NeWord M i j), w'.toWord.toList = w.toList by
    rcases this with ⟨i, j, w, h⟩
    refine ⟨i, j, w, ?_⟩
    ext
    rw [h]
  cases' w with l hnot1 hchain
  induction' l with x l hi
  · contradiction
  · rw [List.forall_mem_cons] at hnot1
    cases' l with y l
    · refine ⟨x.1, x.1, singleton x.2 hnot1.1, ?_⟩
      simp [toWord]
    · rw [List.chain'_cons] at hchain
      specialize hi hnot1.2 hchain.2 (by rintro ⟨rfl⟩)
      obtain ⟨i, j, w', hw' : w'.toList = y::l⟩ := hi
      obtain rfl : y = ⟨i, w'.head⟩ := by simpa [hw'] using w'.toList_head?
      refine ⟨x.1, j, append (singleton x.2 hnot1.1) hchain.1 w', ?_⟩
      simpa [toWord] using hw'
def prod {i j} (w : NeWord M i j) :=
  w.toWord.prod
@[simp]
theorem singleton_head {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).head = x :=
  rfl
@[simp]
theorem singleton_last {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).last = x :=
  rfl
@[simp]
theorem prod_singleton {i} (x : M i) (hne_one : x ≠ 1) : (singleton x hne_one).prod = of x := by
  simp [toWord, prod, Word.prod]
@[simp]
theorem append_head {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).head = w₁.head :=
  rfl
@[simp]
theorem append_last {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).last = w₂.last :=
  rfl
@[simp]
theorem append_prod {i j k l} {w₁ : NeWord M i j} {hne : j ≠ k} {w₂ : NeWord M k l} :
    (append w₁ hne w₂).prod = w₁.prod * w₂.prod := by simp [toWord, prod, Word.prod]
def replaceHead : ∀ {i j : ι} (x : M i) (_hnotone : x ≠ 1) (_w : NeWord M i j), NeWord M i j
  | _, _, x, h, singleton _ _ => singleton x h
  | _, _, x, h, append w₁ hne w₂ => append (replaceHead x h w₁) hne w₂
@[simp]
theorem replaceHead_head {i j : ι} (x : M i) (hnotone : x ≠ 1) (w : NeWord M i j) :
    (replaceHead x hnotone w).head = x := by
  induction w
  · rfl
  · simp [*]
def mulHead {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) : NeWord M i j :=
  replaceHead (x * w.head) hnotone w
@[simp]
theorem mulHead_head {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
    (mulHead w x hnotone).head = x * w.head := by
  induction w
  · rfl
  · simp [*]
@[simp]
theorem mulHead_prod {i j : ι} (w : NeWord M i j) (x : M i) (hnotone : x * w.head ≠ 1) :
    (mulHead w x hnotone).prod = of x * w.prod := by
  unfold mulHead
  induction w with
  | singleton => simp [mulHead, replaceHead]
  | append _ _ _ w_ih_w₁ w_ih_w₂ =>
    specialize w_ih_w₁ _ hnotone
    clear w_ih_w₂
    simp? [replaceHead, ← mul_assoc] at * says
      simp only [replaceHead, head, append_prod, ← mul_assoc] at *
    congr 1
section Group
variable {G : ι → Type*} [∀ i, Group (G i)]
def inv : ∀ {i j} (_w : NeWord G i j), NeWord G j i
  | _, _, singleton x h => singleton x⁻¹ (mt inv_eq_one.mp h)
  | _, _, append w₁ h w₂ => append w₂.inv h.symm w₁.inv
@[simp]
theorem inv_prod {i j} (w : NeWord G i j) : w.inv.prod = w.prod⁻¹ := by
  induction w <;> simp [inv, *]
@[simp]
theorem inv_head {i j} (w : NeWord G i j) : w.inv.head = w.last⁻¹ := by
  induction w <;> simp [inv, *]
@[simp]
theorem inv_last {i j} (w : NeWord G i j) : w.inv.last = w.head⁻¹ := by
  induction w <;> simp [inv, *]
end Group
end NeWord
section PingPongLemma
open Pointwise
open Cardinal
variable {G : Type*} [Group G]
variable {H : ι → Type*} [∀ i, Group (H i)]
variable (f : ∀ i, H i →* G)
variable (hcard : 3 ≤ #ι ∨ ∃ i, 3 ≤ #(H i))
variable {α : Type*} [MulAction G α]
variable (X : ι → Set α)
variable (hXnonempty : ∀ i, (X i).Nonempty)
variable (hXdisj : Pairwise (Disjoint on X))
variable (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i)
include hpp
theorem lift_word_ping_pong {i j k} (w : NeWord H i j) (hk : j ≠ k) :
    lift f w.prod • X k ⊆ X i := by
  induction' w with i x hne_one i j k l w₁ hne w₂ hIw₁ hIw₂ generalizing k
  · simpa using hpp hk _ hne_one
  · calc
      lift f (NeWord.append w₁ hne w₂).prod • X k = lift f w₁.prod • lift f w₂.prod • X k := by
        simp [MulAction.mul_smul]
      _ ⊆ lift f w₁.prod • X _ := set_smul_subset_set_smul_iff.mpr (hIw₂ hk)
      _ ⊆ X i := hIw₁ hne
include hXnonempty hXdisj
theorem lift_word_prod_nontrivial_of_other_i {i j k} (w : NeWord H i j) (hhead : k ≠ i)
    (hlast : k ≠ j) : lift f w.prod ≠ 1 := by
  intro heq1
  have : X k ⊆ X i := by simpa [heq1] using lift_word_ping_pong f X hpp w hlast.symm
  obtain ⟨x, hx⟩ := hXnonempty k
  exact (hXdisj hhead).le_bot ⟨hx, this hx⟩
variable [Nontrivial ι]
theorem lift_word_prod_nontrivial_of_head_eq_last {i} (w : NeWord H i i) :
    lift f w.prod ≠ 1 := by
  obtain ⟨k, hk⟩ := exists_ne i
  exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w hk hk
theorem lift_word_prod_nontrivial_of_head_card {i j} (w : NeWord H i j)
    (hcard : 3 ≤ #(H i)) (hheadtail : i ≠ j) : lift f w.prod ≠ 1 := by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head ≠ 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : NeWord H i i :=
    NeWord.append (NeWord.mulHead w h hnot1) hheadtail.symm
      (NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
  have hw' : lift f w'.prod ≠ 1 :=
    lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w'
  intro heq1
  apply hw'
  simp [w', heq1]
include hcard in
theorem lift_word_prod_nontrivial_of_not_empty {i j} (w : NeWord H i j) :
    lift f w.prod ≠ 1 := by
  classical
    cases' hcard with hcard hcard
    · obtain ⟨i, h1, h2⟩ := Cardinal.three_le hcard i j
      exact lift_word_prod_nontrivial_of_other_i f X hXnonempty hXdisj hpp w h1 h2
    · cases' hcard with k hcard
      by_cases hh : i = k <;> by_cases hl : j = k
      · subst hh
        subst hl
        exact lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w
      · subst hh
        change j ≠ i at hl
        exact lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w hcard hl.symm
      · subst hl
        change i ≠ j at hh
        have : lift f w.inv.prod ≠ 1 :=
          lift_word_prod_nontrivial_of_head_card f X hXnonempty hXdisj hpp w.inv hcard hh.symm
        intro heq
        apply this
        simpa using heq
      · change i ≠ k at hh
        change j ≠ k at hl
        obtain ⟨h, hn1, -⟩ := Cardinal.three_le hcard 1 1
        let w' : NeWord H k k :=
          NeWord.append (NeWord.append (NeWord.singleton h hn1) hh.symm w) hl
            (NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
        have hw' : lift f w'.prod ≠ 1 :=
          lift_word_prod_nontrivial_of_head_eq_last f X hXnonempty hXdisj hpp w'
        intro heq1
        apply hw'
        simp [w', heq1]
include hcard in
theorem empty_of_word_prod_eq_one {w : Word H} (h : lift f w.prod = 1) :
    w = Word.empty := by
  by_contra hnotempty
  obtain ⟨i, j, w, rfl⟩ := NeWord.of_word w hnotempty
  exact lift_word_prod_nontrivial_of_not_empty f hcard X hXnonempty hXdisj hpp w h
include hcard in
theorem lift_injective_of_ping_pong : Function.Injective (lift f) := by
  classical
    apply (injective_iff_map_eq_one (lift f)).mpr
    rw [(CoprodI.Word.equiv).forall_congr_left]
    intro w Heq
    dsimp [Word.equiv] at *
    rw [empty_of_word_prod_eq_one f hcard X hXnonempty hXdisj hpp Heq, Word.prod_empty]
end PingPongLemma
def FreeGroupBasis.coprodI {ι : Type*} {X : ι → Type*} {G : ι → Type*} [∀ i, Group (G i)]
    (B : ∀ i, FreeGroupBasis (X i) (G i)) :
    FreeGroupBasis (Σ i, X i) (CoprodI G) :=
  ⟨MulEquiv.symm <| MonoidHom.toMulEquiv
    (FreeGroup.lift fun x : Σ i, X i => CoprodI.of (B x.1 x.2))
    (CoprodI.lift fun i : ι => (B i).lift fun x : X i =>
              FreeGroup.of (⟨i, x⟩ : Σ i, X i))
    (by ext; simp)
    (by ext1 i; apply (B i).ext_hom; simp)⟩
instance {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)] [∀ i, IsFreeGroup (G i)] :
    IsFreeGroup (CoprodI G) :=
  (FreeGroupBasis.coprodI (fun i ↦ IsFreeGroup.basis (G i))).isFreeGroup
@[simps!]
def _root_.freeGroupEquivCoprodI {ι : Type u_1} :
    FreeGroup ι ≃* CoprodI fun _ : ι => FreeGroup Unit := by
  refine MonoidHom.toMulEquiv ?_ ?_ ?_ ?_
  · exact FreeGroup.lift fun i => @CoprodI.of ι _ _ i (FreeGroup.of Unit.unit)
  · exact CoprodI.lift fun i => FreeGroup.lift fun _ => FreeGroup.of i
  · ext; simp
  · ext i a; cases a; simp
section PingPongLemma
open Pointwise Cardinal
variable [Nontrivial ι]
variable {G : Type u_1} [Group G] (a : ι → G)
variable {α : Type*} [MulAction G α]
variable (X Y : ι → Set α)
variable (hXnonempty : ∀ i, (X i).Nonempty)
variable (hXdisj : Pairwise (Disjoint on X))
variable (hYdisj : Pairwise (Disjoint on Y))
variable (hXYdisj : ∀ i j, Disjoint (X i) (Y j))
variable (hX : ∀ i, a i • (Y i)ᶜ ⊆ X i)
variable (hY : ∀ i, a⁻¹ i • (X i)ᶜ ⊆ Y i)
include hXnonempty hXdisj hYdisj hXYdisj hX hY in
theorem _root_.FreeGroup.injective_lift_of_ping_pong : Function.Injective (FreeGroup.lift a) := by
  have : FreeGroup.lift a =
      (CoprodI.lift fun i => FreeGroup.lift fun _ => a i).comp
        (@freeGroupEquivCoprodI ι).toMonoidHom := by
    ext i
    simp
  rw [this, MonoidHom.coe_comp]
  clear this
  refine Function.Injective.comp ?_ (MulEquiv.injective freeGroupEquivCoprodI)
  show Function.Injective (lift fun i : ι => FreeGroup.lift fun _ => a i)
  let H : ι → Type _ := fun _i => FreeGroup Unit
  let f : ∀ i, H i →* G := fun i => FreeGroup.lift fun _ => a i
  let X' : ι → Set α := fun i => X i ∪ Y i
  apply lift_injective_of_ping_pong f _ X'
  · show ∀ i, (X' i).Nonempty
    exact fun i => Set.Nonempty.inl (hXnonempty i)
  · show Pairwise (Disjoint on X')
    intro i j hij
    simp only [X']
    apply Disjoint.union_left <;> apply Disjoint.union_right
    · exact hXdisj hij
    · exact hXYdisj i j
    · exact (hXYdisj j i).symm
    · exact hYdisj hij
  · show Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X' j ⊆ X' i
    rintro i j hij
    refine FreeGroup.freeGroupUnitEquivInt.forall_congr_left.mpr ?_
    intro n hne1
    change FreeGroup.lift (fun _ => a i) (FreeGroup.of () ^ n) • X' j ⊆ X' i
    simp only [map_zpow, FreeGroup.lift.of]
    change a i ^ n • X' j ⊆ X' i
    have hnne0 : n ≠ 0 := by
      rintro rfl
      apply hne1
      simp [H, FreeGroup.freeGroupUnitEquivInt]
    clear hne1
    simp only [X']
    cases' (lt_or_gt_of_ne hnne0).symm with hlt hgt
    · have h1n : 1 ≤ n := hlt
      calc
        a i ^ n • X' j ⊆ a i ^ n • (Y i)ᶜ :=
          smul_set_mono ((hXYdisj j i).union_left <| hYdisj hij.symm).subset_compl_right
        _ ⊆ X i := by
          clear hnne0 hlt
          refine Int.le_induction (P := fun n => a i ^ n • (Y i)ᶜ ⊆ X i) ?_ ?_ n h1n
          · dsimp
            rw [zpow_one]
            exact hX i
          · dsimp
            intro n _hle hi
            calc
              a i ^ (n + 1) • (Y i)ᶜ = (a i ^ n * a i) • (Y i)ᶜ := by rw [zpow_add, zpow_one]
              _ = a i ^ n • a i • (Y i)ᶜ := MulAction.mul_smul _ _ _
              _ ⊆ a i ^ n • X i := smul_set_mono <| hX i
              _ ⊆ a i ^ n • (Y i)ᶜ := smul_set_mono (hXYdisj i i).subset_compl_right
              _ ⊆ X i := hi
        _ ⊆ X' i := Set.subset_union_left
    · have h1n : n ≤ -1 := by
        apply Int.le_of_lt_add_one
        simpa using hgt
      calc
        a i ^ n • X' j ⊆ a i ^ n • (X i)ᶜ :=
          smul_set_mono ((hXdisj hij.symm).union_left (hXYdisj i j).symm).subset_compl_right
        _ ⊆ Y i := by
          refine Int.le_induction_down (P := fun n => a i ^ n • (X i)ᶜ ⊆ Y i) ?_ ?_ _ h1n
          · dsimp
            rw [zpow_neg, zpow_one]
            exact hY i
          · dsimp
            intro n _ hi
            calc
              a i ^ (n - 1) • (X i)ᶜ = (a i ^ n * (a i)⁻¹) • (X i)ᶜ := by rw [zpow_sub, zpow_one]
              _ = a i ^ n • (a i)⁻¹ • (X i)ᶜ := MulAction.mul_smul _ _ _
              _ ⊆ a i ^ n • Y i := smul_set_mono <| hY i
              _ ⊆ a i ^ n • (X i)ᶜ := smul_set_mono (hXYdisj i i).symm.subset_compl_right
              _ ⊆ Y i := hi
        _ ⊆ X' i := Set.subset_union_right
  show _ ∨ ∃ i, 3 ≤ #(H i)
  inhabit ι
  right
  use Inhabited.default
  simp only [H]
  rw [FreeGroup.freeGroupUnitEquivInt.cardinal_eq, Cardinal.mk_denumerable]
  apply le_of_lt
  exact nat_lt_aleph0 3
end PingPongLemma
end Monoid.CoprodI