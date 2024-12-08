import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Logic.Relation
import Mathlib.Logic.Small.Defs
import Mathlib.Order.GameAdd
namespace SetTheory
open Function Relation
universe u
inductive PGame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → PGame) → (β → PGame) → PGame
compile_inductive% PGame
namespace PGame
def LeftMoves : PGame → Type u
  | mk l _ _ _ => l
def RightMoves : PGame → Type u
  | mk _ r _ _ => r
def moveLeft : ∀ g : PGame, LeftMoves g → PGame
  | mk _l _ L _ => L
def moveRight : ∀ g : PGame, RightMoves g → PGame
  | mk _ _r _ R => R
@[simp]
theorem leftMoves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).LeftMoves = xl :=
  rfl
@[simp]
theorem moveLeft_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).moveLeft = xL :=
  rfl
@[simp]
theorem rightMoves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).RightMoves = xr :=
  rfl
@[simp]
theorem moveRight_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : PGame).moveRight = xR :=
  rfl
def ofLists (L R : List PGame.{u}) : PGame.{u} :=
  mk (ULift (Fin L.length)) (ULift (Fin R.length)) (fun i => L[i.down.1]) fun j ↦ R[j.down.1]
theorem leftMoves_ofLists (L R : List PGame) : (ofLists L R).LeftMoves = ULift (Fin L.length) :=
  rfl
theorem rightMoves_ofLists (L R : List PGame) : (ofLists L R).RightMoves = ULift (Fin R.length) :=
  rfl
abbrev toOfListsLeftMoves {L R : List PGame} : Fin L.length ≃ (ofLists L R).LeftMoves :=
  Equiv.ulift.symm
abbrev toOfListsRightMoves {L R : List PGame} : Fin R.length ≃ (ofLists L R).RightMoves :=
  Equiv.ulift.symm
@[simp]
theorem ofLists_moveLeft' {L R : List PGame} (i : (ofLists L R).LeftMoves) :
    (ofLists L R).moveLeft i = L[i.down.val] :=
  rfl
theorem ofLists_moveLeft {L R : List PGame} (i : Fin L.length) :
    (ofLists L R).moveLeft (ULift.up i) = L[i] :=
  rfl
@[simp]
theorem ofLists_moveRight' {L R : List PGame} (i : (ofLists L R).RightMoves) :
    (ofLists L R).moveRight i = R[i.down.val] :=
  rfl
theorem ofLists_moveRight {L R : List PGame} (i : Fin R.length) :
    (ofLists L R).moveRight (ULift.up i) = R[i] :=
  rfl
@[elab_as_elim]
def moveRecOn {C : PGame → Sort*} (x : PGame)
    (IH : ∀ y : PGame, (∀ i, C (y.moveLeft i)) → (∀ j, C (y.moveRight j)) → C y) : C x :=
  x.recOn fun yl yr yL yR => IH (mk yl yr yL yR)
@[mk_iff]
inductive IsOption : PGame → PGame → Prop
  | moveLeft {x : PGame} (i : x.LeftMoves) : IsOption (x.moveLeft i) x
  | moveRight {x : PGame} (i : x.RightMoves) : IsOption (x.moveRight i) x
theorem IsOption.mk_left {xl xr : Type u} (xL : xl → PGame) (xR : xr → PGame) (i : xl) :
    (xL i).IsOption (mk xl xr xL xR) :=
  @IsOption.moveLeft (mk _ _ _ _) i
theorem IsOption.mk_right {xl xr : Type u} (xL : xl → PGame) (xR : xr → PGame) (i : xr) :
    (xR i).IsOption (mk xl xr xL xR) :=
  @IsOption.moveRight (mk _ _ _ _) i
theorem wf_isOption : WellFounded IsOption :=
  ⟨fun x =>
    moveRecOn x fun x IHl IHr =>
      Acc.intro x fun y h => by
        induction h with
        | moveLeft i => exact IHl i
        | moveRight j => exact IHr j⟩
def Subsequent : PGame → PGame → Prop :=
  TransGen IsOption
instance : IsTrans _ Subsequent :=
  inferInstanceAs <| IsTrans _ (TransGen _)
@[trans]
theorem Subsequent.trans {x y z} : Subsequent x y → Subsequent y z → Subsequent x z :=
  TransGen.trans
theorem wf_subsequent : WellFounded Subsequent :=
  wf_isOption.transGen
instance : WellFoundedRelation PGame :=
  ⟨_, wf_subsequent⟩
@[simp]
theorem Subsequent.moveLeft {x : PGame} (i : x.LeftMoves) : Subsequent (x.moveLeft i) x :=
  TransGen.single (IsOption.moveLeft i)
@[simp]
theorem Subsequent.moveRight {x : PGame} (j : x.RightMoves) : Subsequent (x.moveRight j) x :=
  TransGen.single (IsOption.moveRight j)
@[simp]
theorem Subsequent.mk_left {xl xr} (xL : xl → PGame) (xR : xr → PGame) (i : xl) :
    Subsequent (xL i) (mk xl xr xL xR) :=
  @Subsequent.moveLeft (mk _ _ _ _) i
@[simp]
theorem Subsequent.mk_right {xl xr} (xL : xl → PGame) (xR : xr → PGame) (j : xr) :
    Subsequent (xR j) (mk xl xr xL xR) :=
  @Subsequent.moveRight (mk _ _ _ _) j
macro "pgame_wf_tac" : tactic =>
  `(tactic| solve_by_elim (config := { maxDepth := 8 })
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subsequent.moveLeft, Subsequent.moveRight, Subsequent.mk_left, Subsequent.mk_right,
    Subsequent.trans] )
variable {xl xr : Type u}
@[simp]
theorem Subsequent.mk_right' (xL : xl → PGame) (xR : xr → PGame) (j : RightMoves (mk xl xr xL xR)) :
    Subsequent (xR j) (mk xl xr xL xR) := by
  pgame_wf_tac
@[simp] theorem Subsequent.moveRight_mk_left {xR : xr → PGame} {i : xl} (xL : xl → PGame) (j) :
    Subsequent ((xL i).moveRight j) (mk xl xr xL xR) := by
  pgame_wf_tac
@[simp] theorem Subsequent.moveRight_mk_right {xL : xl → PGame} {i : xr} (xR : xr → PGame) (j) :
    Subsequent ((xR i).moveRight j) (mk xl xr xL xR) := by
  pgame_wf_tac
@[simp] theorem Subsequent.moveLeft_mk_left {xR : xr → PGame} {i : xl} (xL : xl → PGame) (j) :
    Subsequent ((xL i).moveLeft j) (mk xl xr xL xR) := by
  pgame_wf_tac
@[simp] theorem Subsequent.moveLeft_mk_right {xL : xl → PGame} {i : xr} (xR : xr → PGame) (j) :
    Subsequent ((xR i).moveLeft j) (mk xl xr xL xR) := by
  pgame_wf_tac
instance : Zero PGame :=
  ⟨⟨PEmpty, PEmpty, PEmpty.elim, PEmpty.elim⟩⟩
@[simp]
theorem zero_leftMoves : LeftMoves 0 = PEmpty :=
  rfl
@[simp]
theorem zero_rightMoves : RightMoves 0 = PEmpty :=
  rfl
instance isEmpty_zero_leftMoves : IsEmpty (LeftMoves 0) :=
  instIsEmptyPEmpty
instance isEmpty_zero_rightMoves : IsEmpty (RightMoves 0) :=
  instIsEmptyPEmpty
instance : Inhabited PGame :=
  ⟨0⟩
instance instOnePGame : One PGame :=
  ⟨⟨PUnit, PEmpty, fun _ => 0, PEmpty.elim⟩⟩
@[simp]
theorem one_leftMoves : LeftMoves 1 = PUnit :=
  rfl
@[simp]
theorem one_moveLeft (x) : moveLeft 1 x = 0 :=
  rfl
@[simp]
theorem one_rightMoves : RightMoves 1 = PEmpty :=
  rfl
instance uniqueOneLeftMoves : Unique (LeftMoves 1) :=
  PUnit.unique
instance isEmpty_one_rightMoves : IsEmpty (RightMoves 1) :=
  instIsEmptyPEmpty
def Identical : PGame.{u} → PGame.{u} → Prop
  | mk _ _ xL xR, mk _ _ yL yR =>
    Relator.BiTotal (fun i j ↦ Identical (xL i) (yL j)) ∧
      Relator.BiTotal (fun i j ↦ Identical (xR i) (yR j))
@[inherit_doc] scoped infix:50 " ≡ " => PGame.Identical
theorem identical_iff : ∀ {x y : PGame}, x ≡ y ↔
    Relator.BiTotal (x.moveLeft · ≡ y.moveLeft ·) ∧ Relator.BiTotal (x.moveRight · ≡ y.moveRight ·)
  | mk _ _ _ _, mk _ _ _ _ => Iff.rfl
@[refl, simp] protected theorem Identical.refl (x) : x ≡ x :=
  PGame.recOn x fun _ _ _ _ IHL IHR ↦ ⟨Relator.BiTotal.refl IHL, Relator.BiTotal.refl IHR⟩
protected theorem Identical.rfl {x} : x ≡ x := Identical.refl x
@[symm] protected theorem Identical.symm : ∀ {x y}, x ≡ y → y ≡ x
  | mk _ _ _ _, mk _ _ _ _, ⟨hL, hR⟩ => ⟨hL.symm fun _ _ h ↦ h.symm, hR.symm fun _ _ h ↦ h.symm⟩
theorem identical_comm {x y} : x ≡ y ↔ y ≡ x :=
  ⟨.symm, .symm⟩
@[trans] protected theorem Identical.trans : ∀ {x y z}, x ≡ y → y ≡ z → x ≡ z
  | mk _ _ _ _, mk _ _ _ _, mk _ _ _ _, ⟨hL₁, hR₁⟩, ⟨hL₂, hR₂⟩ =>
    ⟨hL₁.trans (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) hL₂, hR₁.trans (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) hR₂⟩
def memₗ (x y : PGame.{u}) : Prop := ∃ b, x ≡ y.moveLeft b
def memᵣ (x y : PGame.{u}) : Prop := ∃ b, x ≡ y.moveRight b
@[inherit_doc] scoped infix:50 " ∈ₗ " => PGame.memₗ
@[inherit_doc] scoped infix:50 " ∈ᵣ " => PGame.memᵣ
@[inherit_doc PGame.memₗ] binder_predicate x " ∈ₗ " y:term => `($x ∈ₗ $y)
@[inherit_doc PGame.memᵣ] binder_predicate x " ∈ᵣ " y:term => `($x ∈ᵣ $y)
theorem memₗ_def {x y : PGame} : x ∈ₗ y ↔ ∃ b, x ≡ y.moveLeft b := .rfl
theorem memᵣ_def {x y : PGame} : x ∈ᵣ y ↔ ∃ b, x ≡ y.moveRight b := .rfl
theorem moveLeft_memₗ (x : PGame) (b) : x.moveLeft b ∈ₗ x := ⟨_, .rfl⟩
theorem moveRight_memᵣ (x : PGame) (b) : x.moveRight b ∈ᵣ x := ⟨_, .rfl⟩
theorem identical_of_isEmpty (x y : PGame)
    [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves]
    [IsEmpty y.LeftMoves] [IsEmpty y.RightMoves] : x ≡ y :=
  identical_iff.2 (by simp [biTotal_empty])
def identicalSetoid : Setoid PGame :=
  ⟨Identical, Identical.refl, Identical.symm, Identical.trans⟩
instance : IsRefl PGame (· ≡ ·) := ⟨Identical.refl⟩
instance : IsSymm PGame (· ≡ ·) := ⟨fun _ _ ↦ Identical.symm⟩
instance : IsTrans PGame (· ≡ ·) := ⟨fun _ _ _ ↦ Identical.trans⟩
instance : IsEquiv PGame (· ≡ ·) := { }
lemma Identical.moveLeft : ∀ {x y}, x ≡ y →
    ∀ i, ∃ j, x.moveLeft i ≡ y.moveLeft j
  | mk _ _ _ _, mk _ _ _ _, ⟨hl, _⟩, i => hl.1 i
lemma Identical.moveRight : ∀ {x y}, x ≡ y →
    ∀ i, ∃ j, x.moveRight i ≡ y.moveRight j
  | mk _ _ _ _, mk _ _ _ _, ⟨_, hr⟩, i => hr.1 i
theorem identical_iff' : ∀ {x y : PGame}, x ≡ y ↔
    ((∀ i, x.moveLeft i ∈ₗ y) ∧ (∀ j, y.moveLeft j ∈ₗ x)) ∧
      ((∀ i, x.moveRight i ∈ᵣ y) ∧ (∀ j, y.moveRight j ∈ᵣ x))
  | mk xl xr xL xR, mk yl yr yL yR => by
    convert identical_iff <;>
    dsimp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal] <;>
    congr! <;>
    exact exists_congr <| fun _ ↦ identical_comm
theorem memₗ.congr_right : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, w ∈ₗ x ↔ w ∈ₗ y)
  | mk _ _ _ _, mk _ _ _ _, ⟨⟨h₁, h₂⟩, _⟩, _w =>
    ⟨fun ⟨i, hi⟩ ↦ (h₁ i).imp (fun _ ↦ hi.trans),
      fun ⟨j, hj⟩ ↦ (h₂ j).imp (fun _ hi ↦ hj.trans hi.symm)⟩
theorem memᵣ.congr_right : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, w ∈ᵣ x ↔ w ∈ᵣ y)
  | mk _ _ _ _, mk _ _ _ _, ⟨_, ⟨h₁, h₂⟩⟩, _w =>
    ⟨fun ⟨i, hi⟩ ↦ (h₁ i).imp (fun _ ↦ hi.trans),
      fun ⟨j, hj⟩ ↦ (h₂ j).imp (fun _ hi ↦ hj.trans hi.symm)⟩
theorem memₗ.congr_left : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, x ∈ₗ w ↔ y ∈ₗ w)
  | _, _, h, mk _ _ _ _ => ⟨fun ⟨i, hi⟩ ↦ ⟨i, h.symm.trans hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, h.trans hi⟩⟩
theorem memᵣ.congr_left : ∀ {x y : PGame},
    x ≡ y → (∀ {w : PGame}, x ∈ᵣ w ↔ y ∈ᵣ w)
  | _, _, h, mk _ _ _ _ => ⟨fun ⟨i, hi⟩ ↦ ⟨i, h.symm.trans hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, h.trans hi⟩⟩
lemma Identical.ext : ∀ {x y}, (∀ z, z ∈ₗ x ↔ z ∈ₗ y) → (∀ z, z ∈ᵣ x ↔ z ∈ᵣ y) → x ≡ y
  | mk _ _ _ _, mk _ _ _ _, hl, hr => identical_iff'.mpr
    ⟨⟨fun i ↦ (hl _).mp ⟨i, refl _⟩, fun j ↦ (hl _).mpr ⟨j, refl _⟩⟩,
      ⟨fun i ↦ (hr _).mp ⟨i, refl _⟩, fun j ↦ (hr _).mpr ⟨j, refl _⟩⟩⟩
lemma Identical.ext_iff {x y} : x ≡ y ↔ (∀ z, z ∈ₗ x ↔ z ∈ₗ y) ∧ (∀ z, z ∈ᵣ x ↔ z ∈ᵣ y) :=
  ⟨fun h ↦ ⟨@memₗ.congr_right _ _ h, @memᵣ.congr_right _ _ h⟩, fun h ↦ h.elim Identical.ext⟩
lemma Identical.congr_right {x y z} (h : x ≡ y) : z ≡ x ↔ z ≡ y :=
  ⟨fun hz ↦ hz.trans h, fun hz ↦ hz.trans h.symm⟩
lemma Identical.congr_left {x y z} (h : x ≡ y) : x ≡ z ↔ y ≡ z :=
  ⟨fun hz ↦ h.symm.trans hz, fun hz ↦ h.trans hz⟩
lemma Identical.of_fn {x y : PGame}
    (l : x.LeftMoves → y.LeftMoves) (il : y.LeftMoves → x.LeftMoves)
    (r : x.RightMoves → y.RightMoves) (ir : y.RightMoves → x.RightMoves)
    (hl : ∀ i, x.moveLeft i ≡ y.moveLeft (l i))
    (hil : ∀ i, x.moveLeft (il i) ≡ y.moveLeft i)
    (hr : ∀ i, x.moveRight i ≡ y.moveRight (r i))
    (hir : ∀ i, x.moveRight (ir i) ≡ y.moveRight i) : x ≡ y :=
  identical_iff.mpr
    ⟨⟨fun i ↦ ⟨l i, hl i⟩, fun i ↦ ⟨il i, hil i⟩⟩, ⟨fun i ↦ ⟨r i, hr i⟩, fun i ↦ ⟨ir i, hir i⟩⟩⟩
lemma Identical.of_equiv {x y : PGame}
    (l : x.LeftMoves ≃ y.LeftMoves) (r : x.RightMoves ≃ y.RightMoves)
    (hl : ∀ i, x.moveLeft i ≡ y.moveLeft (l i)) (hr : ∀ i, x.moveRight i ≡ y.moveRight (r i)) :
    x ≡ y :=
  .of_fn l l.symm r r.symm hl (by simpa using hl <| l.symm ·) hr (by simpa using hr <| r.symm ·)
instance le : LE PGame :=
  ⟨Sym2.GameAdd.fix wf_isOption fun x y le =>
      (∀ i, ¬le y (x.moveLeft i) (Sym2.GameAdd.snd_fst <| IsOption.moveLeft i)) ∧
        ∀ j, ¬le (y.moveRight j) x (Sym2.GameAdd.fst_snd <| IsOption.moveRight j)⟩
def LF (x y : PGame) : Prop :=
  ¬y ≤ x
@[inherit_doc]
scoped infixl:50 " ⧏ " => PGame.LF
@[simp]
protected theorem not_le {x y : PGame} : ¬x ≤ y ↔ y ⧏ x :=
  Iff.rfl
@[simp]
theorem not_lf {x y : PGame} : ¬x ⧏ y ↔ y ≤ x :=
  Classical.not_not
theorem _root_.LE.le.not_gf {x y : PGame} : x ≤ y → ¬y ⧏ x :=
  not_lf.2
theorem LF.not_ge {x y : PGame} : x ⧏ y → ¬y ≤ x :=
  id
theorem le_iff_forall_lf {x y : PGame} :
    x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ ∀ j, x ⧏ y.moveRight j := by
  unfold LE.le le
  simp only
  rw [Sym2.GameAdd.fix_eq]
  rfl
@[simp]
theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ≤ mk yl yr yL yR ↔ (∀ i, xL i ⧏ mk yl yr yL yR) ∧ ∀ j, mk xl xr xL xR ⧏ yR j :=
  le_iff_forall_lf
theorem le_of_forall_lf {x y : PGame} (h₁ : ∀ i, x.moveLeft i ⧏ y) (h₂ : ∀ j, x ⧏ y.moveRight j) :
    x ≤ y :=
  le_iff_forall_lf.2 ⟨h₁, h₂⟩
theorem lf_iff_exists_le {x y : PGame} :
    x ⧏ y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [LF, le_iff_forall_lf, not_and_or]
  simp
@[simp]
theorem mk_lf_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ⧏ mk yl yr yL yR ↔ (∃ i, mk xl xr xL xR ≤ yL i) ∨ ∃ j, xR j ≤ mk yl yr yL yR :=
  lf_iff_exists_le
theorem le_or_gf (x y : PGame) : x ≤ y ∨ y ⧏ x := by
  rw [← PGame.not_le]
  apply em
theorem moveLeft_lf_of_le {x y : PGame} (h : x ≤ y) (i) : x.moveLeft i ⧏ y :=
  (le_iff_forall_lf.1 h).1 i
alias _root_.LE.le.moveLeft_lf := moveLeft_lf_of_le
theorem lf_moveRight_of_le {x y : PGame} (h : x ≤ y) (j) : x ⧏ y.moveRight j :=
  (le_iff_forall_lf.1 h).2 j
alias _root_.LE.le.lf_moveRight := lf_moveRight_of_le
theorem lf_of_moveRight_le {x y : PGame} {j} (h : x.moveRight j ≤ y) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inr ⟨j, h⟩
theorem lf_of_le_moveLeft {x y : PGame} {i} (h : x ≤ y.moveLeft i) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inl ⟨i, h⟩
theorem lf_of_le_mk {xl xr xL xR y} : mk xl xr xL xR ≤ y → ∀ i, xL i ⧏ y :=
  moveLeft_lf_of_le
theorem lf_of_mk_le {x yl yr yL yR} : x ≤ mk yl yr yL yR → ∀ j, x ⧏ yR j :=
  lf_moveRight_of_le
theorem mk_lf_of_le {xl xr y j} (xL) {xR : xr → PGame} : xR j ≤ y → mk xl xr xL xR ⧏ y :=
  @lf_of_moveRight_le (mk _ _ _ _) y j
theorem lf_mk_of_le {x yl yr} {yL : yl → PGame} (yR) {i} : x ≤ yL i → x ⧏ mk yl yr yL yR :=
  @lf_of_le_moveLeft x (mk _ _ _ _) i
private theorem le_trans_aux {x y z : PGame}
    (h₁ : ∀ {i}, y ≤ z → z ≤ x.moveLeft i → y ≤ x.moveLeft i)
    (h₂ : ∀ {j}, z.moveRight j ≤ x → x ≤ y → z.moveRight j ≤ y) (hxy : x ≤ y) (hyz : y ≤ z) :
    x ≤ z :=
  le_of_forall_lf (fun i => PGame.not_le.1 fun h => (h₁ hyz h).not_gf <| hxy.moveLeft_lf i)
    fun j => PGame.not_le.1 fun h => (h₂ h hxy).not_gf <| hyz.lf_moveRight j
instance : Preorder PGame :=
  { PGame.le with
    le_refl := fun x => by
      induction x with | mk _ _ _ _ IHl IHr => _
      exact
        le_of_forall_lf (fun i => lf_of_le_moveLeft (IHl i)) fun i => lf_of_moveRight_le (IHr i)
    le_trans := by
      suffices
        ∀ {x y z : PGame},
          (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y) from
        fun x y z => this.1
      intro x y z
      induction' x with xl xr xL xR IHxl IHxr generalizing y z
      induction' y with yl yr yL yR IHyl IHyr generalizing z
      induction' z with zl zr zL zR IHzl IHzr
      exact
        ⟨le_trans_aux (fun {i} => (IHxl i).2.1) fun {j} => (IHzr j).2.2,
          le_trans_aux (fun {i} => (IHyl i).2.2) fun {j} => (IHxr j).1,
          le_trans_aux (fun {i} => (IHzl i).1) fun {j} => (IHyr j).2.1⟩
    lt := fun x y => x ≤ y ∧ x ⧏ y }
lemma Identical.le : ∀ {x y}, x ≡ y → x ≤ y
  | mk _ _ _ _, mk _ _ _ _, ⟨hL, hR⟩ => le_of_forall_lf
    (fun i ↦ let ⟨_, hj⟩ := hL.1 i; lf_of_le_moveLeft hj.le)
    (fun i ↦ let ⟨_, hj⟩ := hR.2 i; lf_of_moveRight_le hj.le)
lemma Identical.ge {x y} (h : x ≡ y) : y ≤ x := h.symm.le
theorem lt_iff_le_and_lf {x y : PGame} : x < y ↔ x ≤ y ∧ x ⧏ y :=
  Iff.rfl
theorem lt_of_le_of_lf {x y : PGame} (h₁ : x ≤ y) (h₂ : x ⧏ y) : x < y :=
  ⟨h₁, h₂⟩
theorem lf_of_lt {x y : PGame} (h : x < y) : x ⧏ y :=
  h.2
alias _root_.LT.lt.lf := lf_of_lt
theorem lf_irrefl (x : PGame) : ¬x ⧏ x :=
  le_rfl.not_gf
instance : IsIrrefl _ (· ⧏ ·) :=
  ⟨lf_irrefl⟩
@[trans]
theorem lf_of_le_of_lf {x y z : PGame} (h₁ : x ≤ y) (h₂ : y ⧏ z) : x ⧏ z := by
  rw [← PGame.not_le] at h₂ ⊢
  exact fun h₃ => h₂ (h₃.trans h₁)
instance : Trans (· ≤ ·) (· ⧏ ·) (· ⧏ ·) := ⟨lf_of_le_of_lf⟩
@[trans]
theorem lf_of_lf_of_le {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y ≤ z) : x ⧏ z := by
  rw [← PGame.not_le] at h₁ ⊢
  exact fun h₃ => h₁ (h₂.trans h₃)
instance : Trans (· ⧏ ·) (· ≤ ·) (· ⧏ ·) := ⟨lf_of_lf_of_le⟩
alias _root_.LE.le.trans_lf := lf_of_le_of_lf
alias LF.trans_le := lf_of_lf_of_le
@[trans]
theorem lf_of_lt_of_lf {x y z : PGame} (h₁ : x < y) (h₂ : y ⧏ z) : x ⧏ z :=
  h₁.le.trans_lf h₂
@[trans]
theorem lf_of_lf_of_lt {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y < z) : x ⧏ z :=
  h₁.trans_le h₂.le
alias _root_.LT.lt.trans_lf := lf_of_lt_of_lf
alias LF.trans_lt := lf_of_lf_of_lt
theorem moveLeft_lf {x : PGame} : ∀ i, x.moveLeft i ⧏ x :=
  le_rfl.moveLeft_lf
theorem lf_moveRight {x : PGame} : ∀ j, x ⧏ x.moveRight j :=
  le_rfl.lf_moveRight
theorem lf_mk {xl xr} (xL : xl → PGame) (xR : xr → PGame) (i) : xL i ⧏ mk xl xr xL xR :=
  @moveLeft_lf (mk _ _ _ _) i
theorem mk_lf {xl xr} (xL : xl → PGame) (xR : xr → PGame) (j) : mk xl xr xL xR ⧏ xR j :=
  @lf_moveRight (mk _ _ _ _) j
theorem le_of_forall_lt {x y : PGame} (h₁ : ∀ i, x.moveLeft i < y) (h₂ : ∀ j, x < y.moveRight j) :
    x ≤ y :=
  le_of_forall_lf (fun i => (h₁ i).lf) fun i => (h₂ i).lf
theorem le_def {x y : PGame} :
    x ≤ y ↔
      (∀ i, (∃ i', x.moveLeft i ≤ y.moveLeft i') ∨ ∃ j, (x.moveLeft i).moveRight j ≤ y) ∧
        ∀ j, (∃ i, x ≤ (y.moveRight j).moveLeft i) ∨ ∃ j', x.moveRight j' ≤ y.moveRight j := by
  rw [le_iff_forall_lf]
  conv =>
    lhs
    simp only [lf_iff_exists_le]
theorem lf_def {x y : PGame} :
    x ⧏ y ↔
      (∃ i, (∀ i', x.moveLeft i' ⧏ y.moveLeft i) ∧ ∀ j, x ⧏ (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i ⧏ y) ∧ ∀ j', x.moveRight j ⧏ y.moveRight j' := by
  rw [lf_iff_exists_le]
  conv =>
    lhs
    simp only [le_iff_forall_lf]
theorem zero_le_lf {x : PGame} : 0 ≤ x ↔ ∀ j, 0 ⧏ x.moveRight j := by
  rw [le_iff_forall_lf]
  simp
theorem le_zero_lf {x : PGame} : x ≤ 0 ↔ ∀ i, x.moveLeft i ⧏ 0 := by
  rw [le_iff_forall_lf]
  simp
theorem zero_lf_le {x : PGame} : 0 ⧏ x ↔ ∃ i, 0 ≤ x.moveLeft i := by
  rw [lf_iff_exists_le]
  simp
theorem lf_zero_le {x : PGame} : x ⧏ 0 ↔ ∃ j, x.moveRight j ≤ 0 := by
  rw [lf_iff_exists_le]
  simp
theorem zero_le {x : PGame} : 0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.moveRight j).moveLeft i := by
  rw [le_def]
  simp
theorem le_zero {x : PGame} : x ≤ 0 ↔ ∀ i, ∃ j, (x.moveLeft i).moveRight j ≤ 0 := by
  rw [le_def]
  simp
theorem zero_lf {x : PGame} : 0 ⧏ x ↔ ∃ i, ∀ j, 0 ⧏ (x.moveLeft i).moveRight j := by
  rw [lf_def]
  simp
theorem lf_zero {x : PGame} : x ⧏ 0 ↔ ∃ j, ∀ i, (x.moveRight j).moveLeft i ⧏ 0 := by
  rw [lf_def]
  simp
@[simp]
theorem zero_le_of_isEmpty_rightMoves (x : PGame) [IsEmpty x.RightMoves] : 0 ≤ x :=
  zero_le.2 isEmptyElim
@[simp]
theorem le_zero_of_isEmpty_leftMoves (x : PGame) [IsEmpty x.LeftMoves] : x ≤ 0 :=
  le_zero.2 isEmptyElim
noncomputable def rightResponse {x : PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).RightMoves :=
  Classical.choose <| (le_zero.1 h) i
theorem rightResponse_spec {x : PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).moveRight (rightResponse h i) ≤ 0 :=
  Classical.choose_spec <| (le_zero.1 h) i
noncomputable def leftResponse {x : PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    (x.moveRight j).LeftMoves :=
  Classical.choose <| (zero_le.1 h) j
theorem leftResponse_spec {x : PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    0 ≤ (x.moveRight j).moveLeft (leftResponse h j) :=
  Classical.choose_spec <| (zero_le.1 h) j
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → PGame.{u}) :
    BddAbove (Set.range f) := by
  let x : PGame.{u} := ⟨Σ i, (f <| (equivShrink.{u} ι).symm i).LeftMoves, PEmpty,
    fun x ↦ moveLeft _ x.2, PEmpty.elim⟩
  refine ⟨x, Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @moveLeft_lf x ⟨equivShrink ι i, j⟩
lemma bddAbove_of_small (s : Set PGame.{u}) [Small.{u} s] : BddAbove s := by
  simpa using bddAbove_range_of_small (Subtype.val : s → PGame.{u})
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → PGame.{u}) :
    BddBelow (Set.range f) := by
  let x : PGame.{u} := ⟨PEmpty, Σ i, (f <| (equivShrink.{u} ι).symm i).RightMoves, PEmpty.elim,
    fun x ↦ moveRight _ x.2⟩
  refine ⟨x, Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @lf_moveRight x ⟨equivShrink ι i, j⟩
lemma bddBelow_of_small (s : Set PGame.{u}) [Small.{u} s] : BddBelow s := by
  simpa using bddBelow_range_of_small (Subtype.val : s → PGame.{u})
def Equiv (x y : PGame) : Prop :=
  x ≤ y ∧ y ≤ x
instance : IsEquiv _ PGame.Equiv where
  refl _ := ⟨le_rfl, le_rfl⟩
  trans := fun _ _ _ ⟨xy, yx⟩ ⟨yz, zy⟩ => ⟨xy.trans yz, zy.trans yx⟩
  symm _ _ := And.symm
instance setoid : Setoid PGame :=
  ⟨Equiv, refl, symm, Trans.trans⟩
theorem equiv_def {x y : PGame} : x ≈ y ↔ x ≤ y ∧ y ≤ x := Iff.rfl
theorem Equiv.le {x y : PGame} (h : x ≈ y) : x ≤ y :=
  h.1
theorem Equiv.ge {x y : PGame} (h : x ≈ y) : y ≤ x :=
  h.2
@[refl, simp]
theorem equiv_rfl {x : PGame} : x ≈ x :=
  refl x
theorem equiv_refl (x : PGame) : x ≈ x :=
  refl x
@[symm]
protected theorem Equiv.symm {x y : PGame} : (x ≈ y) → (y ≈ x) :=
  symm
@[trans]
protected theorem Equiv.trans {x y z : PGame} : (x ≈ y) → (y ≈ z) → (x ≈ z) :=
  _root_.trans
protected theorem equiv_comm {x y : PGame} : (x ≈ y) ↔ (y ≈ x) :=
  comm
theorem equiv_of_eq {x y : PGame} (h : x = y) : x ≈ y := by subst h; rfl
lemma Identical.equiv {x y} (h : x ≡ y) : x ≈ y := ⟨h.le, h.ge⟩
@[trans]
theorem le_of_le_of_equiv {x y z : PGame} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z :=
  h₁.trans h₂.1
instance : Trans
    ((· ≤ ·) : PGame → PGame → Prop)
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop) where
  trans := le_of_le_of_equiv
@[trans]
theorem le_of_equiv_of_le {x y z : PGame} (h₁ : x ≈ y) : y ≤ z → x ≤ z :=
  h₁.1.trans
instance : Trans
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop)
    ((· ≤ ·) : PGame → PGame → Prop) where
  trans := le_of_equiv_of_le
theorem LF.not_equiv {x y : PGame} (h : x ⧏ y) : ¬(x ≈ y) := fun h' => h.not_ge h'.2
theorem LF.not_equiv' {x y : PGame} (h : x ⧏ y) : ¬(y ≈ x) := fun h' => h.not_ge h'.1
theorem LF.not_gt {x y : PGame} (h : x ⧏ y) : ¬y < x := fun h' => h.not_ge h'.le
theorem le_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ ≤ y₁) : x₂ ≤ y₂ :=
  hx.2.trans (h.trans hy.1)
theorem le_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂ :=
  ⟨le_congr_imp hx hy, le_congr_imp (Equiv.symm hx) (Equiv.symm hy)⟩
theorem le_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ≤ y ↔ x₂ ≤ y :=
  le_congr hx equiv_rfl
theorem le_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ≤ y₁ ↔ x ≤ y₂ :=
  le_congr equiv_rfl hy
theorem lf_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ ↔ x₂ ⧏ y₂ :=
  PGame.not_le.symm.trans <| (not_congr (le_congr hy hx)).trans PGame.not_le
theorem lf_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ → x₂ ⧏ y₂ :=
  (lf_congr hx hy).1
theorem lf_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ⧏ y ↔ x₂ ⧏ y :=
  lf_congr hx equiv_rfl
theorem lf_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ⧏ y₁ ↔ x ⧏ y₂ :=
  lf_congr equiv_rfl hy
@[trans]
theorem lf_of_lf_of_equiv {x y z : PGame} (h₁ : x ⧏ y) (h₂ : y ≈ z) : x ⧏ z :=
  lf_congr_imp equiv_rfl h₂ h₁
instance : Trans (· ⧏ ·) (· ≈ ·) (· ⧏ ·) := ⟨lf_of_lf_of_equiv⟩
@[trans]
theorem lf_of_equiv_of_lf {x y z : PGame} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
  lf_congr_imp (Equiv.symm h₁) equiv_rfl
instance : Trans (· ≈ ·) (· ⧏ ·) (· ⧏ ·) := ⟨lf_of_equiv_of_lf⟩
@[trans]
theorem lt_of_lt_of_equiv {x y z : PGame} (h₁ : x < y) (h₂ : y ≈ z) : x < z :=
  h₁.trans_le h₂.1
instance : Trans
    ((· < ·) : PGame → PGame → Prop)
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop) where
  trans := lt_of_lt_of_equiv
@[trans]
theorem lt_of_equiv_of_lt {x y z : PGame} (h₁ : x ≈ y) : y < z → x < z :=
  h₁.1.trans_lt
instance : Trans
    ((· ≈ ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop)
    ((· < ·) : PGame → PGame → Prop) where
  trans := lt_of_equiv_of_lt
theorem lt_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ < y₁) : x₂ < y₂ :=
  hx.2.trans_lt (h.trans_le hy.1)
theorem lt_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
  ⟨lt_congr_imp hx hy, lt_congr_imp (Equiv.symm hx) (Equiv.symm hy)⟩
theorem lt_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ < y ↔ x₂ < y :=
  lt_congr hx equiv_rfl
theorem lt_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x < y₁ ↔ x < y₂ :=
  lt_congr equiv_rfl hy
theorem lt_or_equiv_of_le {x y : PGame} (h : x ≤ y) : x < y ∨ (x ≈ y) :=
  and_or_left.mp ⟨h, (em <| y ≤ x).symm.imp_left PGame.not_le.1⟩
theorem lf_or_equiv_or_gf (x y : PGame) : x ⧏ y ∨ (x ≈ y) ∨ y ⧏ x := by
  by_cases h : x ⧏ y
  · exact Or.inl h
  · right
    cases' lt_or_equiv_of_le (PGame.not_lf.1 h) with h' h'
    · exact Or.inr h'.lf
    · exact Or.inl (Equiv.symm h')
theorem equiv_congr_left {y₁ y₂ : PGame} : (y₁ ≈ y₂) ↔ ∀ x₁, (x₁ ≈ y₁) ↔ (x₁ ≈ y₂) :=
  ⟨fun h _ => ⟨fun h' => Equiv.trans h' h, fun h' => Equiv.trans h' (Equiv.symm h)⟩,
   fun h => (h y₁).1 <| equiv_rfl⟩
theorem equiv_congr_right {x₁ x₂ : PGame} : (x₁ ≈ x₂) ↔ ∀ y₁, (x₁ ≈ y₁) ↔ (x₂ ≈ y₁) :=
  ⟨fun h _ => ⟨fun h' => Equiv.trans (Equiv.symm h) h', fun h' => Equiv.trans h h'⟩,
   fun h => (h x₂).2 <| equiv_rfl⟩
theorem Equiv.of_exists {x y : PGame}
    (hl₁ : ∀ i, ∃ j, x.moveLeft i ≈ y.moveLeft j) (hr₁ : ∀ i, ∃ j, x.moveRight i ≈ y.moveRight j)
    (hl₂ : ∀ j, ∃ i, x.moveLeft i ≈ y.moveLeft j) (hr₂ : ∀ j, ∃ i, x.moveRight i ≈ y.moveRight j) :
    x ≈ y := by
  constructor <;> refine le_def.2 ⟨?_, ?_⟩ <;> intro i
  · obtain ⟨j, hj⟩ := hl₁ i
    exact Or.inl ⟨j, Equiv.le hj⟩
  · obtain ⟨j, hj⟩ := hr₂ i
    exact Or.inr ⟨j, Equiv.le hj⟩
  · obtain ⟨j, hj⟩ := hl₂ i
    exact Or.inl ⟨j, Equiv.ge hj⟩
  · obtain ⟨j, hj⟩ := hr₁ i
    exact Or.inr ⟨j, Equiv.ge hj⟩
theorem Equiv.of_equiv {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, x.moveLeft i ≈ y.moveLeft (L i))
    (hr : ∀ j, x.moveRight j ≈ y.moveRight (R j)) : x ≈ y := by
  apply Equiv.of_exists <;> intro i
  exacts [⟨_, hl i⟩, ⟨_, hr i⟩,
    ⟨_, by simpa using hl (L.symm i)⟩, ⟨_, by simpa using hr (R.symm i)⟩]
@[deprecated (since := "2024-09-26")] alias equiv_of_mk_equiv := Equiv.of_equiv
def Fuzzy (x y : PGame) : Prop :=
  x ⧏ y ∧ y ⧏ x
@[inherit_doc]
scoped infixl:50 " ‖ " => PGame.Fuzzy
@[symm]
theorem Fuzzy.swap {x y : PGame} : x ‖ y → y ‖ x :=
  And.symm
instance : IsSymm _ (· ‖ ·) :=
  ⟨fun _ _ => Fuzzy.swap⟩
theorem Fuzzy.swap_iff {x y : PGame} : x ‖ y ↔ y ‖ x :=
  ⟨Fuzzy.swap, Fuzzy.swap⟩
theorem fuzzy_irrefl (x : PGame) : ¬x ‖ x := fun h => lf_irrefl x h.1
instance : IsIrrefl _ (· ‖ ·) :=
  ⟨fuzzy_irrefl⟩
theorem lf_iff_lt_or_fuzzy {x y : PGame} : x ⧏ y ↔ x < y ∨ x ‖ y := by
  simp only [lt_iff_le_and_lf, Fuzzy, ← PGame.not_le]
  tauto
theorem lf_of_fuzzy {x y : PGame} (h : x ‖ y) : x ⧏ y :=
  lf_iff_lt_or_fuzzy.2 (Or.inr h)
alias Fuzzy.lf := lf_of_fuzzy
theorem lt_or_fuzzy_of_lf {x y : PGame} : x ⧏ y → x < y ∨ x ‖ y :=
  lf_iff_lt_or_fuzzy.1
theorem Fuzzy.not_equiv {x y : PGame} (h : x ‖ y) : ¬(x ≈ y) := fun h' => h'.1.not_gf h.2
theorem Fuzzy.not_equiv' {x y : PGame} (h : x ‖ y) : ¬(y ≈ x) := fun h' => h'.2.not_gf h.2
theorem not_fuzzy_of_le {x y : PGame} (h : x ≤ y) : ¬x ‖ y := fun h' => h'.2.not_ge h
theorem not_fuzzy_of_ge {x y : PGame} (h : y ≤ x) : ¬x ‖ y := fun h' => h'.1.not_ge h
theorem Equiv.not_fuzzy {x y : PGame} (h : x ≈ y) : ¬x ‖ y :=
  not_fuzzy_of_le h.1
theorem Equiv.not_fuzzy' {x y : PGame} (h : x ≈ y) : ¬y ‖ x :=
  not_fuzzy_of_le h.2
theorem fuzzy_congr {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ ↔ x₂ ‖ y₂ :=
  show _ ∧ _ ↔ _ ∧ _ by rw [lf_congr hx hy, lf_congr hy hx]
theorem fuzzy_congr_imp {x₁ y₁ x₂ y₂ : PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ‖ y₁ → x₂ ‖ y₂ :=
  (fuzzy_congr hx hy).1
theorem fuzzy_congr_left {x₁ x₂ y : PGame} (hx : x₁ ≈ x₂) : x₁ ‖ y ↔ x₂ ‖ y :=
  fuzzy_congr hx equiv_rfl
theorem fuzzy_congr_right {x y₁ y₂ : PGame} (hy : y₁ ≈ y₂) : x ‖ y₁ ↔ x ‖ y₂ :=
  fuzzy_congr equiv_rfl hy
@[trans]
theorem fuzzy_of_fuzzy_of_equiv {x y z : PGame} (h₁ : x ‖ y) (h₂ : y ≈ z) : x ‖ z :=
  (fuzzy_congr_right h₂).1 h₁
@[trans]
theorem fuzzy_of_equiv_of_fuzzy {x y z : PGame} (h₁ : x ≈ y) (h₂ : y ‖ z) : x ‖ z :=
  (fuzzy_congr_left h₁).2 h₂
theorem lt_or_equiv_or_gt_or_fuzzy (x y : PGame) : x < y ∨ (x ≈ y) ∨ y < x ∨ x ‖ y := by
  cases' le_or_gf x y with h₁ h₁ <;> cases' le_or_gf y x with h₂ h₂
  · right
    left
    exact ⟨h₁, h₂⟩
  · left
    exact ⟨h₁, h₂⟩
  · right
    right
    left
    exact ⟨h₂, h₁⟩
  · right
    right
    right
    exact ⟨h₂, h₁⟩
theorem lt_or_equiv_or_gf (x y : PGame) : x < y ∨ (x ≈ y) ∨ y ⧏ x := by
  rw [lf_iff_lt_or_fuzzy, Fuzzy.swap_iff]
  exact lt_or_equiv_or_gt_or_fuzzy x y
inductive Relabelling : PGame.{u} → PGame.{u} → Type (u + 1)
  |
  mk :
    ∀ {x y : PGame} (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves),
      (∀ i, Relabelling (x.moveLeft i) (y.moveLeft (L i))) →
        (∀ j, Relabelling (x.moveRight j) (y.moveRight (R j))) → Relabelling x y
@[inherit_doc]
scoped infixl:50 " ≡r " => PGame.Relabelling
namespace Relabelling
variable {x y : PGame.{u}}
def mk' (L : y.LeftMoves ≃ x.LeftMoves) (R : y.RightMoves ≃ x.RightMoves)
    (hL : ∀ i, x.moveLeft (L i) ≡r y.moveLeft i) (hR : ∀ j, x.moveRight (R j) ≡r y.moveRight j) :
    x ≡r y :=
  ⟨L.symm, R.symm, fun i => by simpa using hL (L.symm i), fun j => by simpa using hR (R.symm j)⟩
def leftMovesEquiv : x ≡r y → x.LeftMoves ≃ y.LeftMoves
  | ⟨L,_, _,_⟩ => L
@[simp]
theorem mk_leftMovesEquiv {x y L R hL hR} : (@Relabelling.mk x y L R hL hR).leftMovesEquiv = L :=
  rfl
@[simp]
theorem mk'_leftMovesEquiv {x y L R hL hR} :
    (@Relabelling.mk' x y L R hL hR).leftMovesEquiv = L.symm :=
  rfl
def rightMovesEquiv : x ≡r y → x.RightMoves ≃ y.RightMoves
  | ⟨_, R, _, _⟩ => R
@[simp]
theorem mk_rightMovesEquiv {x y L R hL hR} : (@Relabelling.mk x y L R hL hR).rightMovesEquiv = R :=
  rfl
@[simp]
theorem mk'_rightMovesEquiv {x y L R hL hR} :
    (@Relabelling.mk' x y L R hL hR).rightMovesEquiv = R.symm :=
  rfl
def moveLeft : ∀ (r : x ≡r y) (i : x.LeftMoves), x.moveLeft i ≡r y.moveLeft (r.leftMovesEquiv i)
  | ⟨_, _, hL, _⟩ => hL
def moveLeftSymm :
    ∀ (r : x ≡r y) (i : y.LeftMoves), x.moveLeft (r.leftMovesEquiv.symm i) ≡r y.moveLeft i
  | ⟨L, R, hL, hR⟩, i => by simpa using hL (L.symm i)
def moveRight :
    ∀ (r : x ≡r y) (i : x.RightMoves), x.moveRight i ≡r y.moveRight (r.rightMovesEquiv i)
  | ⟨_, _, _, hR⟩ => hR
def moveRightSymm :
    ∀ (r : x ≡r y) (i : y.RightMoves), x.moveRight (r.rightMovesEquiv.symm i) ≡r y.moveRight i
  | ⟨L, R, hL, hR⟩, i => by simpa using hR (R.symm i)
@[refl]
def refl (x : PGame) : x ≡r x :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ => refl _, fun _ => refl _⟩
termination_by x
instance (x : PGame) : Inhabited (x ≡r x) :=
  ⟨refl _⟩
@[symm]
def symm : ∀ {x y : PGame}, x ≡r y → y ≡r x
  | _, _, ⟨L, R, hL, hR⟩ => mk' L R (fun i => (hL i).symm) fun j => (hR j).symm
theorem le {x y : PGame} (r : x ≡r y) : x ≤ y :=
  le_def.2
    ⟨fun i => Or.inl ⟨_, (r.moveLeft i).le⟩, fun j =>
      Or.inr ⟨_, (r.moveRightSymm j).le⟩⟩
termination_by x
theorem ge {x y : PGame} (r : x ≡r y) : y ≤ x :=
  r.symm.le
theorem equiv (r : x ≡r y) : x ≈ y :=
  ⟨r.le, r.ge⟩
@[trans]
def trans : ∀ {x y z : PGame}, x ≡r y → y ≡r z → x ≡r z
  | _, _, _, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ =>
    ⟨L₁.trans L₂, R₁.trans R₂, fun i => (hL₁ i).trans (hL₂ _), fun j => (hR₁ j).trans (hR₂ _)⟩
def isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡r 0 :=
  ⟨Equiv.equivPEmpty _, Equiv.equivOfIsEmpty _ _, isEmptyElim, isEmptyElim⟩
end Relabelling
theorem Equiv.isEmpty (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≈ 0 :=
  (Relabelling.isEmpty x).equiv
instance {x y : PGame} : Coe (x ≡r y) (x ≈ y) :=
  ⟨Relabelling.equiv⟩
def relabel {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves) : PGame :=
  ⟨xl', xr', x.moveLeft ∘ el, x.moveRight ∘ er⟩
@[simp]
theorem relabel_moveLeft' {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (i : xl') : moveLeft (relabel el er) i = x.moveLeft (el i) :=
  rfl
theorem relabel_moveLeft {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (i : x.LeftMoves) : moveLeft (relabel el er) (el.symm i) = x.moveLeft i := by simp
@[simp]
theorem relabel_moveRight' {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (j : xr') : moveRight (relabel el er) j = x.moveRight (er j) :=
  rfl
theorem relabel_moveRight {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves)
    (j : x.RightMoves) : moveRight (relabel el er) (er.symm j) = x.moveRight j := by simp
def relabelRelabelling {x : PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves) (er : xr' ≃ x.RightMoves) :
    x ≡r relabel el er :=
  Relabelling.mk' el er (fun i => by simp; rfl) (fun j => by simp; rfl)
def neg : PGame → PGame
  | ⟨l, r, L, R⟩ => ⟨r, l, fun i => neg (R i), fun i => neg (L i)⟩
instance : Neg PGame :=
  ⟨neg⟩
@[simp]
theorem neg_def {xl xr xL xR} : -mk xl xr xL xR = mk xr xl (fun j => -xR j) fun i => -xL i :=
  rfl
instance : InvolutiveNeg PGame :=
  { inferInstanceAs (Neg PGame) with
    neg_neg := fun x => by
      induction' x with xl xr xL xR ihL ihR
      simp_rw [neg_def, ihL, ihR] }
instance : NegZeroClass PGame :=
  { inferInstanceAs (Zero PGame), inferInstanceAs (Neg PGame) with
    neg_zero := by
      dsimp [Zero.zero, Neg.neg, neg]
      congr <;> funext i <;> cases i }
@[simp]
theorem neg_ofLists (L R : List PGame) :
    -ofLists L R = ofLists (R.map fun x => -x) (L.map fun x => -x) := by
  simp only [ofLists, neg_def, List.getElem_map, mk.injEq, List.length_map, true_and]
  constructor
  all_goals
    apply hfunext
    · simp
    · rintro ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩ h
      have :
        ∀ {m n} (_ : m = n) {b : ULift (Fin m)} {c : ULift (Fin n)} (_ : HEq b c),
          (b.down : ℕ) = ↑c.down := by
        rintro m n rfl b c
        simp only [heq_eq_eq]
        rintro rfl
        rfl
      simp only [heq_eq_eq]
      congr 5
      exact this (List.length_map _ _).symm h
theorem isOption_neg {x y : PGame} : IsOption x (-y) ↔ IsOption (-x) y := by
  rw [isOption_iff, isOption_iff, or_comm]
  cases y
  apply or_congr <;>
    · apply exists_congr
      intro
      rw [neg_eq_iff_eq_neg]
      rfl
@[simp]
theorem isOption_neg_neg {x y : PGame} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]
theorem leftMoves_neg : ∀ x : PGame, (-x).LeftMoves = x.RightMoves
  | ⟨_, _, _, _⟩ => rfl
theorem rightMoves_neg : ∀ x : PGame, (-x).RightMoves = x.LeftMoves
  | ⟨_, _, _, _⟩ => rfl
def toLeftMovesNeg {x : PGame} : x.RightMoves ≃ (-x).LeftMoves :=
  Equiv.cast (leftMoves_neg x).symm
def toRightMovesNeg {x : PGame} : x.LeftMoves ≃ (-x).RightMoves :=
  Equiv.cast (rightMoves_neg x).symm
theorem moveLeft_neg {x : PGame} (i) : (-x).moveLeft (toLeftMovesNeg i) = -x.moveRight i := by
  cases x
  rfl
@[simp]
theorem moveLeft_neg' {x : PGame} (i) : (-x).moveLeft i = -x.moveRight (toLeftMovesNeg.symm i) := by
  cases x
  rfl
theorem moveRight_neg {x : PGame} (i) : (-x).moveRight (toRightMovesNeg i) = -x.moveLeft i := by
  cases x
  rfl
@[simp]
theorem moveRight_neg' {x : PGame} (i) :
    (-x).moveRight i = -x.moveLeft (toRightMovesNeg.symm i) := by
  cases x
  rfl
theorem moveLeft_neg_symm {x : PGame} (i) :
    x.moveLeft (toRightMovesNeg.symm i) = -(-x).moveRight i := by simp
theorem moveLeft_neg_symm' {x : PGame} (i) :
    x.moveLeft i = -(-x).moveRight (toRightMovesNeg i) := by simp
theorem moveRight_neg_symm {x : PGame} (i) :
    x.moveRight (toLeftMovesNeg.symm i) = -(-x).moveLeft i := by simp
theorem moveRight_neg_symm' {x : PGame} (i) :
    x.moveRight i = -(-x).moveLeft (toLeftMovesNeg i) := by simp
def Relabelling.negCongr : ∀ {x y : PGame}, x ≡r y → -x ≡r -y
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨L, R, hL, hR⟩ =>
    ⟨R, L, fun j => (hR j).negCongr, fun i => (hL i).negCongr⟩
private theorem neg_le_lf_neg_iff : ∀ {x y : PGame.{u}}, (-y ≤ -x ↔ x ≤ y) ∧ (-y ⧏ -x ↔ x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR => by
    simp_rw [neg_def, mk_le_mk, mk_lf_mk, ← neg_def]
    constructor
    · rw [and_comm]
      apply and_congr <;> exact forall_congr' fun _ => neg_le_lf_neg_iff.2
    · rw [or_comm]
      apply or_congr <;> exact exists_congr fun _ => neg_le_lf_neg_iff.1
termination_by x y => (x, y)
@[simp]
theorem neg_le_neg_iff {x y : PGame} : -y ≤ -x ↔ x ≤ y :=
  neg_le_lf_neg_iff.1
@[simp]
theorem neg_lf_neg_iff {x y : PGame} : -y ⧏ -x ↔ x ⧏ y :=
  neg_le_lf_neg_iff.2
@[simp]
theorem neg_lt_neg_iff {x y : PGame} : -y < -x ↔ x < y := by
  rw [lt_iff_le_and_lf, lt_iff_le_and_lf, neg_le_neg_iff, neg_lf_neg_iff]
@[simp]
theorem neg_equiv_neg_iff {x y : PGame} : (-x ≈ -y) ↔ (x ≈ y) := by
  show Equiv (-x) (-y) ↔ Equiv x y
  rw [Equiv, Equiv, neg_le_neg_iff, neg_le_neg_iff, and_comm]
@[simp]
theorem neg_fuzzy_neg_iff {x y : PGame} : -x ‖ -y ↔ x ‖ y := by
  rw [Fuzzy, Fuzzy, neg_lf_neg_iff, neg_lf_neg_iff, and_comm]
theorem neg_le_iff {x y : PGame} : -y ≤ x ↔ -x ≤ y := by rw [← neg_neg x, neg_le_neg_iff, neg_neg]
theorem neg_lf_iff {x y : PGame} : -y ⧏ x ↔ -x ⧏ y := by rw [← neg_neg x, neg_lf_neg_iff, neg_neg]
theorem neg_lt_iff {x y : PGame} : -y < x ↔ -x < y := by rw [← neg_neg x, neg_lt_neg_iff, neg_neg]
theorem neg_equiv_iff {x y : PGame} : (-x ≈ y) ↔ (x ≈ -y) := by
  rw [← neg_neg y, neg_equiv_neg_iff, neg_neg]
theorem neg_fuzzy_iff {x y : PGame} : -x ‖ y ↔ x ‖ -y := by
  rw [← neg_neg y, neg_fuzzy_neg_iff, neg_neg]
theorem le_neg_iff {x y : PGame} : y ≤ -x ↔ x ≤ -y := by rw [← neg_neg x, neg_le_neg_iff, neg_neg]
theorem lf_neg_iff {x y : PGame} : y ⧏ -x ↔ x ⧏ -y := by rw [← neg_neg x, neg_lf_neg_iff, neg_neg]
theorem lt_neg_iff {x y : PGame} : y < -x ↔ x < -y := by rw [← neg_neg x, neg_lt_neg_iff, neg_neg]
@[simp]
theorem neg_le_zero_iff {x : PGame} : -x ≤ 0 ↔ 0 ≤ x := by rw [neg_le_iff, neg_zero]
@[simp]
theorem zero_le_neg_iff {x : PGame} : 0 ≤ -x ↔ x ≤ 0 := by rw [le_neg_iff, neg_zero]
@[simp]
theorem neg_lf_zero_iff {x : PGame} : -x ⧏ 0 ↔ 0 ⧏ x := by rw [neg_lf_iff, neg_zero]
@[simp]
theorem zero_lf_neg_iff {x : PGame} : 0 ⧏ -x ↔ x ⧏ 0 := by rw [lf_neg_iff, neg_zero]
@[simp]
theorem neg_lt_zero_iff {x : PGame} : -x < 0 ↔ 0 < x := by rw [neg_lt_iff, neg_zero]
@[simp]
theorem zero_lt_neg_iff {x : PGame} : 0 < -x ↔ x < 0 := by rw [lt_neg_iff, neg_zero]
@[simp]
theorem neg_equiv_zero_iff {x : PGame} : (-x ≈ 0) ↔ (x ≈ 0) := by rw [neg_equiv_iff, neg_zero]
@[simp]
theorem neg_fuzzy_zero_iff {x : PGame} : -x ‖ 0 ↔ x ‖ 0 := by rw [neg_fuzzy_iff, neg_zero]
@[simp]
theorem zero_equiv_neg_iff {x : PGame} : (0 ≈ -x) ↔ (0 ≈ x) := by rw [← neg_equiv_iff, neg_zero]
@[simp]
theorem zero_fuzzy_neg_iff {x : PGame} : 0 ‖ -x ↔ 0 ‖ x := by rw [← neg_fuzzy_iff, neg_zero]
instance : Add PGame.{u} :=
  ⟨fun x y => by
    induction x generalizing y with | mk xl xr _ _ IHxl IHxr => _
    induction y with | mk yl yr yL yR IHyl IHyr => _
    have y := mk yl yr yL yR
    refine ⟨xl ⊕ yl, xr ⊕ yr, Sum.rec ?_ ?_, Sum.rec ?_ ?_⟩
    · exact fun i => IHxl i y
    · exact IHyl
    · exact fun i => IHxr i y
    · exact IHyr⟩
instance : NatCast PGame :=
  ⟨Nat.unaryCast⟩
@[simp]
protected theorem nat_succ (n : ℕ) : ((n + 1 : ℕ) : PGame) = n + 1 :=
  rfl
instance isEmpty_leftMoves_add (x y : PGame.{u}) [IsEmpty x.LeftMoves] [IsEmpty y.LeftMoves] :
    IsEmpty (x + y).LeftMoves := by
  cases x
  cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'
instance isEmpty_rightMoves_add (x y : PGame.{u}) [IsEmpty x.RightMoves] [IsEmpty y.RightMoves] :
    IsEmpty (x + y).RightMoves := by
  cases x
  cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'
def addZeroRelabelling : ∀ x : PGame.{u}, x + 0 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.sumEmpty xl PEmpty, Equiv.sumEmpty xr PEmpty, ?_, ?_⟩ <;> rintro (⟨i⟩ | ⟨⟨⟩⟩) <;>
      apply addZeroRelabelling
termination_by x => x
theorem add_zero_equiv (x : PGame.{u}) : x + 0 ≈ x :=
  (addZeroRelabelling x).equiv
def zeroAddRelabelling : ∀ x : PGame.{u}, 0 + x ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.emptySum PEmpty xl, Equiv.emptySum PEmpty xr, ?_, ?_⟩ <;> rintro (⟨⟨⟩⟩ | ⟨i⟩) <;>
      apply zeroAddRelabelling
theorem zero_add_equiv (x : PGame.{u}) : 0 + x ≈ x :=
  (zeroAddRelabelling x).equiv
theorem leftMoves_add : ∀ x y : PGame.{u}, (x + y).LeftMoves = (x.LeftMoves ⊕ y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
theorem rightMoves_add : ∀ x y : PGame.{u}, (x + y).RightMoves = (x.RightMoves ⊕ y.RightMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
def toLeftMovesAdd {x y : PGame} : x.LeftMoves ⊕ y.LeftMoves ≃ (x + y).LeftMoves :=
  Equiv.cast (leftMoves_add x y).symm
def toRightMovesAdd {x y : PGame} : x.RightMoves ⊕ y.RightMoves ≃ (x + y).RightMoves :=
  Equiv.cast (rightMoves_add x y).symm
@[simp]
theorem mk_add_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inl i) =
      (mk xl xr xL xR).moveLeft i + mk yl yr yL yR :=
  rfl
@[simp]
theorem add_moveLeft_inl {x : PGame} (y : PGame) (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inl i)) = x.moveLeft i + y := by
  cases x
  cases y
  rfl
@[simp]
theorem mk_add_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inl i) =
      (mk xl xr xL xR).moveRight i + mk yl yr yL yR :=
  rfl
@[simp]
theorem add_moveRight_inl {x : PGame} (y : PGame) (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inl i)) = x.moveRight i + y := by
  cases x
  cases y
  rfl
@[simp]
theorem mk_add_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inr i) =
      mk xl xr xL xR + (mk yl yr yL yR).moveLeft i :=
  rfl
@[simp]
theorem add_moveLeft_inr (x : PGame) {y : PGame} (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inr i)) = x + y.moveLeft i := by
  cases x
  cases y
  rfl
@[simp]
theorem mk_add_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inr i) =
      mk xl xr xL xR + (mk yl yr yL yR).moveRight i :=
  rfl
@[simp]
theorem add_moveRight_inr (x : PGame) {y : PGame} (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inr i)) = x + y.moveRight i := by
  cases x
  cases y
  rfl
theorem leftMoves_add_cases {x y : PGame} (k) {P : (x + y).LeftMoves → Prop}
    (hl : ∀ i, P <| toLeftMovesAdd (Sum.inl i)) (hr : ∀ i, P <| toLeftMovesAdd (Sum.inr i)) :
    P k := by
  rw [← toLeftMovesAdd.apply_symm_apply k]
  cases' toLeftMovesAdd.symm k with i i
  · exact hl i
  · exact hr i
theorem rightMoves_add_cases {x y : PGame} (k) {P : (x + y).RightMoves → Prop}
    (hl : ∀ j, P <| toRightMovesAdd (Sum.inl j)) (hr : ∀ j, P <| toRightMovesAdd (Sum.inr j)) :
    P k := by
  rw [← toRightMovesAdd.apply_symm_apply k]
  cases' toRightMovesAdd.symm k with i i
  · exact hl i
  · exact hr i
instance isEmpty_nat_rightMoves : ∀ n : ℕ, IsEmpty (RightMoves n)
  | 0 => inferInstanceAs (IsEmpty PEmpty)
  | n + 1 => by
    haveI := isEmpty_nat_rightMoves n
    rw [PGame.nat_succ, rightMoves_add]
    infer_instance
def Relabelling.addCongr : ∀ {w x y z : PGame.{u}}, w ≡r x → y ≡r z → w + y ≡r x + z
  | ⟨wl, wr, wL, wR⟩, ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩, ⟨L₁, R₁, hL₁, hR₁⟩,
    ⟨L₂, R₂, hL₂, hR₂⟩ => by
    let Hwx : ⟨wl, wr, wL, wR⟩ ≡r ⟨xl, xr, xL, xR⟩ := ⟨L₁, R₁, hL₁, hR₁⟩
    let Hyz : ⟨yl, yr, yL, yR⟩ ≡r ⟨zl, zr, zL, zR⟩ := ⟨L₂, R₂, hL₂, hR₂⟩
    refine ⟨Equiv.sumCongr L₁ L₂, Equiv.sumCongr R₁ R₂, ?_, ?_⟩ <;> rintro (i | j)
    · exact (hL₁ i).addCongr Hyz
    · exact Hwx.addCongr (hL₂ j)
    · exact (hR₁ i).addCongr Hyz
    · exact Hwx.addCongr (hR₂ j)
termination_by _ x _ z => (x, z)
instance : Sub PGame :=
  ⟨fun x y => x + -y⟩
@[simp]
theorem sub_zero_eq_add_zero (x : PGame) : x - 0 = x + 0 :=
  show x + -0 = x + 0 by rw [neg_zero]
@[deprecated (since := "2024-09-26")] alias sub_zero := sub_zero_eq_add_zero
def Relabelling.subCongr {w x y z : PGame} (h₁ : w ≡r x) (h₂ : y ≡r z) : w - y ≡r x - z :=
  h₁.addCongr h₂.negCongr
def negAddRelabelling : ∀ x y : PGame, -(x + y) ≡r -x + -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine ⟨Equiv.refl _, Equiv.refl _, ?_, ?_⟩
    all_goals
      exact fun j =>
        Sum.casesOn j (fun j => negAddRelabelling _ _) fun j =>
          negAddRelabelling ⟨xl, xr, xL, xR⟩ _
termination_by x y => (x, y)
theorem neg_add_le {x y : PGame} : -(x + y) ≤ -x + -y :=
  (negAddRelabelling x y).le
def addCommRelabelling : ∀ x y : PGame.{u}, x + y ≡r y + x
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, ?_, ?_⟩ <;> rintro (_ | _) <;>
      · dsimp
        apply addCommRelabelling
termination_by x y => (x, y)
theorem add_comm_le {x y : PGame} : x + y ≤ y + x :=
  (addCommRelabelling x y).le
theorem add_comm_equiv {x y : PGame} : x + y ≈ y + x :=
  (addCommRelabelling x y).equiv
def addAssocRelabelling : ∀ x y z : PGame.{u}, x + y + z ≡r x + (y + z)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩ => by
    refine ⟨Equiv.sumAssoc _ _ _, Equiv.sumAssoc _ _ _, ?_, ?_⟩
    · rintro (⟨i | i⟩ | i)
      · apply addAssocRelabelling
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ (yL i)
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ (zL i)
    · rintro (⟨i | i⟩ | i)
      · apply addAssocRelabelling
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ (yR i)
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ (zR i)
termination_by x y z => (x, y, z)
theorem add_assoc_equiv {x y z : PGame} : x + y + z ≈ x + (y + z) :=
  (addAssocRelabelling x y z).equiv
theorem neg_add_cancel_le_zero : ∀ x : PGame, -x + x ≤ 0
  | ⟨xl, xr, xL, xR⟩ =>
    le_zero.2 fun i => by
      cases' i with i i
      · 
        refine ⟨@toRightMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), ?_⟩
        convert @neg_add_cancel_le_zero (xR i)
        apply add_moveRight_inr
      · 
        dsimp
        refine ⟨@toRightMovesAdd ⟨_, _, _, _⟩ _ (Sum.inl i), ?_⟩
        convert @neg_add_cancel_le_zero (xL i)
        apply add_moveRight_inl
theorem zero_le_neg_add_cancel (x : PGame) : 0 ≤ -x + x := by
  rw [← neg_le_neg_iff, neg_zero]
  exact neg_add_le.trans (neg_add_cancel_le_zero _)
theorem neg_add_cancel_equiv (x : PGame) : -x + x ≈ 0 :=
  ⟨neg_add_cancel_le_zero x, zero_le_neg_add_cancel x⟩
theorem add_neg_cancel_le_zero (x : PGame) : x + -x ≤ 0 :=
  add_comm_le.trans (neg_add_cancel_le_zero x)
theorem zero_le_add_neg_cancel (x : PGame) : 0 ≤ x + -x :=
  (zero_le_neg_add_cancel x).trans add_comm_le
theorem add_neg_cancel_equiv (x : PGame) : x + -x ≈ 0 :=
  ⟨add_neg_cancel_le_zero x, zero_le_add_neg_cancel x⟩
theorem sub_self_equiv : ∀ (x : PGame), x - x ≈ 0 :=
  add_neg_cancel_equiv
private theorem add_le_add_right' : ∀ {x y z : PGame}, x ≤ y → x + z ≤ y + z
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => fun h => by
    refine le_def.2 ⟨fun i => ?_, fun i => ?_⟩ <;> cases' i with i i
    · rw [le_def] at h
      cases' h with h_left h_right
      rcases h_left i with (⟨i', ih⟩ | ⟨j, jh⟩)
      · exact Or.inl ⟨toLeftMovesAdd (Sum.inl i'), add_le_add_right' ih⟩
      · refine Or.inr ⟨toRightMovesAdd (Sum.inl j), ?_⟩
        convert add_le_add_right' jh
        apply add_moveRight_inl
    · exact Or.inl ⟨@toLeftMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
    · rw [le_def] at h
      rcases h.right i with (⟨i, ih⟩ | ⟨j', jh⟩)
      · refine Or.inl ⟨toLeftMovesAdd (Sum.inl i), ?_⟩
        convert add_le_add_right' ih
        apply add_moveLeft_inl
      · exact Or.inr ⟨toRightMovesAdd (Sum.inl j'), add_le_add_right' jh⟩
    · exact
        Or.inr ⟨@toRightMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
termination_by x y z => (x, y, z)
instance addRightMono : AddRightMono PGame :=
  ⟨fun _ _ _ => add_le_add_right'⟩
instance addLeftMono : AddLeftMono PGame :=
  ⟨fun x _ _ h => (add_comm_le.trans (add_le_add_right h x)).trans add_comm_le⟩
theorem add_lf_add_right {y z : PGame} (h : y ⧏ z) (x) : y + x ⧏ z + x :=
  suffices z + x ≤ y + x → z ≤ y by
    rw [← PGame.not_le] at h ⊢
    exact mt this h
  fun w =>
  calc
    z ≤ z + 0 := (addZeroRelabelling _).symm.le
    _ ≤ z + (x + -x) := add_le_add_left (zero_le_add_neg_cancel x) _
    _ ≤ z + x + -x := (addAssocRelabelling _ _ _).symm.le
    _ ≤ y + x + -x := add_le_add_right w _
    _ ≤ y + (x + -x) := (addAssocRelabelling _ _ _).le
    _ ≤ y + 0 := add_le_add_left (add_neg_cancel_le_zero x) _
    _ ≤ y := (addZeroRelabelling _).le
theorem add_lf_add_left {y z : PGame} (h : y ⧏ z) (x) : x + y ⧏ x + z := by
  rw [lf_congr add_comm_equiv add_comm_equiv]
  apply add_lf_add_right h
instance addRightStrictMono : AddRightStrictMono PGame :=
  ⟨fun x _ _ h => ⟨add_le_add_right h.1 x, add_lf_add_right h.2 x⟩⟩
instance addLeftStrictMono : AddLeftStrictMono PGame :=
  ⟨fun x _ _ h => ⟨add_le_add_left h.1 x, add_lf_add_left h.2 x⟩⟩
theorem add_lf_add_of_lf_of_le {w x y z : PGame} (hwx : w ⧏ x) (hyz : y ≤ z) : w + y ⧏ x + z :=
  lf_of_lf_of_le (add_lf_add_right hwx y) (add_le_add_left hyz x)
theorem add_lf_add_of_le_of_lf {w x y z : PGame} (hwx : w ≤ x) (hyz : y ⧏ z) : w + y ⧏ x + z :=
  lf_of_le_of_lf (add_le_add_right hwx y) (add_lf_add_left hyz x)
theorem add_congr {w x y z : PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
  ⟨(add_le_add_left h₂.1 w).trans (add_le_add_right h₁.1 z),
    (add_le_add_left h₂.2 x).trans (add_le_add_right h₁.2 y)⟩
theorem add_congr_left {x y z : PGame} (h : x ≈ y) : x + z ≈ y + z :=
  add_congr h equiv_rfl
theorem add_congr_right {x y z : PGame} : (y ≈ z) → (x + y ≈ x + z) :=
  add_congr equiv_rfl
theorem sub_congr {w x y z : PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
  add_congr h₁ (neg_equiv_neg_iff.2 h₂)
theorem sub_congr_left {x y z : PGame} (h : x ≈ y) : x - z ≈ y - z :=
  sub_congr h equiv_rfl
theorem sub_congr_right {x y z : PGame} : (y ≈ z) → (x - y ≈ x - z) :=
  sub_congr equiv_rfl
theorem le_iff_sub_nonneg {x y : PGame} : x ≤ y ↔ 0 ≤ y - x :=
  ⟨fun h => (zero_le_add_neg_cancel x).trans (add_le_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ≤ y - x + x := add_le_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩
theorem lf_iff_sub_zero_lf {x y : PGame} : x ⧏ y ↔ 0 ⧏ y - x :=
  ⟨fun h => (zero_le_add_neg_cancel x).trans_lf (add_lf_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ⧏ y - x + x := add_lf_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩
theorem lt_iff_sub_pos {x y : PGame} : x < y ↔ 0 < y - x :=
  ⟨fun h => lt_of_le_of_lt (zero_le_add_neg_cancel x) (add_lt_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ < y - x + x := add_lt_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩
def insertLeft (x x' : PGame.{u}) : PGame :=
  match x with
  | mk xl xr xL xR => mk (xl ⊕ PUnit) xr (Sum.elim xL fun _ => x') xR
lemma le_insertLeft (x x' : PGame) : x ≤ insertLeft x x' := by
  rw [le_def]
  constructor
  · intro i
    left
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [insertLeft, leftMoves_mk, moveLeft_mk, Sum.exists, Sum.elim_inl]
    left
    use i
  · intro j
    right
    rcases x with ⟨xl, xr, xL, xR⟩
    simp only [rightMoves_mk, moveRight_mk, insertLeft]
    use j
lemma insertLeft_equiv_of_lf {x x' : PGame} (h : x' ⧏ x) : insertLeft x x' ≈ x := by
  rw [equiv_def]
  constructor
  · rw [le_def]
    constructor
    · intro i
      rcases x with ⟨xl, xr, xL, xR⟩
      simp only [insertLeft, leftMoves_mk, moveLeft_mk] at i ⊢
      rcases i with i | _
      · simp only [Sum.elim_inl]
        left
        use i
      · simp only [Sum.elim_inr]
        rw [lf_iff_exists_le] at h
        simp only [leftMoves_mk, moveLeft_mk] at h
        exact h
    · intro j
      right
      rcases x with ⟨xl, xr, xL, xR⟩
      simp only [insertLeft, rightMoves_mk, moveRight_mk]
      use j
  · apply le_insertLeft
def insertRight (x x' : PGame.{u}) : PGame :=
  match x with
  | mk xl xr xL xR => mk xl (xr ⊕ PUnit) xL (Sum.elim xR fun _ => x')
theorem neg_insertRight_neg (x x' : PGame.{u}) : (-x).insertRight (-x') = -x.insertLeft x' := by
  cases x
  cases x'
  dsimp [insertRight, insertLeft]
  congr! with (i | j)
theorem neg_insertLeft_neg (x x' : PGame.{u}) : (-x).insertLeft (-x') = -x.insertRight x' := by
  rw [← neg_eq_iff_eq_neg, ← neg_insertRight_neg, neg_neg, neg_neg]
lemma insertRight_le (x x' : PGame) : insertRight x x' ≤ x := by
  rw [← neg_le_neg_iff, ← neg_insertLeft_neg]
  exact le_insertLeft _ _
lemma insertRight_equiv_of_lf {x x' : PGame} (h : x ⧏ x') : insertRight x x' ≈ x := by
  rw [← neg_equiv_neg_iff, ← neg_insertLeft_neg]
  exact insertLeft_equiv_of_lf (neg_lf_neg_iff.mpr h)
theorem insertRight_insertLeft {x x' x'' : PGame} :
    insertRight (insertLeft x x') x'' = insertLeft (insertRight x x'') x' := by
  cases x; cases x'; cases x''
  dsimp [insertLeft, insertRight]
def star : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => 0, fun _ => 0⟩
@[simp]
theorem star_leftMoves : star.LeftMoves = PUnit :=
  rfl
@[simp]
theorem star_rightMoves : star.RightMoves = PUnit :=
  rfl
@[simp]
theorem star_moveLeft (x) : star.moveLeft x = 0 :=
  rfl
@[simp]
theorem star_moveRight (x) : star.moveRight x = 0 :=
  rfl
instance uniqueStarLeftMoves : Unique star.LeftMoves :=
  PUnit.unique
instance uniqueStarRightMoves : Unique star.RightMoves :=
  PUnit.unique
theorem zero_lf_star : 0 ⧏ star := by
  rw [zero_lf]
  use default
  rintro ⟨⟩
theorem star_lf_zero : star ⧏ 0 := by
  rw [lf_zero]
  use default
  rintro ⟨⟩
theorem star_fuzzy_zero : star ‖ 0 :=
  ⟨star_lf_zero, zero_lf_star⟩
@[simp]
theorem neg_star : -star = star := by simp [star]
@[simp]
protected theorem zero_lt_one : (0 : PGame) < 1 :=
  lt_of_le_of_lf (zero_le_of_isEmpty_rightMoves 1) (zero_lf_le.2 ⟨default, le_rfl⟩)
instance : ZeroLEOneClass PGame :=
  ⟨PGame.zero_lt_one.le⟩
@[simp]
theorem zero_lf_one : (0 : PGame) ⧏ 1 :=
  PGame.zero_lt_one.lf
end PGame
end SetTheory
set_option linter.style.longFile 2100