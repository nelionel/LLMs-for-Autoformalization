import Mathlib.Data.Fintype.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Game.Birthday
set_option synthInstance.checkSynthOrder false
universe u
namespace SetTheory
open scoped PGame
namespace PGame
inductive Short : PGame.{u} → Type (u + 1)
  | mk :
    ∀ {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} (_ : ∀ i : α, Short (L i))
      (_ : ∀ j : β, Short (R j)) [Fintype α] [Fintype β], Short ⟨α, β, L, R⟩
instance subsingleton_short (x : PGame) : Subsingleton (Short x) := by
  induction x with
  | mk xl xr xL xR =>
    constructor
    intro a b
    cases a; cases b
    congr!
attribute [-instance] subsingleton_short in
theorem subsingleton_short_example : ∀ x : PGame, Subsingleton (Short x)
  | mk xl xr xL xR =>
    ⟨fun a b => by
      cases a; cases b
      congr!
      · funext x
        apply @Subsingleton.elim _ (subsingleton_short_example (xL x))
      · funext x
        apply @Subsingleton.elim _ (subsingleton_short_example (xR x))⟩
termination_by x => x
decreasing_by all_goals {
  subst_vars
  simp only [mk.injEq, heq_eq_eq, true_and] at *
  casesm* _ ∧ _
  subst_vars
  pgame_wf_tac
}
def Short.mk' {x : PGame} [Fintype x.LeftMoves] [Fintype x.RightMoves]
    (sL : ∀ i : x.LeftMoves, Short (x.moveLeft i))
    (sR : ∀ j : x.RightMoves, Short (x.moveRight j)) : Short x := by
  convert Short.mk sL sR
  cases x
  dsimp
attribute [class] Short
def fintypeLeft {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} [S : Short ⟨α, β, L, R⟩] :
    Fintype α := by cases' S with _ _ _ _ _ _ F _; exact F
attribute [local instance] fintypeLeft
instance fintypeLeftMoves (x : PGame) [S : Short x] : Fintype x.LeftMoves := by
  cases S; assumption
def fintypeRight {α β : Type u} {L : α → PGame.{u}} {R : β → PGame.{u}} [S : Short ⟨α, β, L, R⟩] :
    Fintype β := by cases' S with _ _ _ _ _ _ _ F; exact F
attribute [local instance] fintypeRight
instance fintypeRightMoves (x : PGame) [S : Short x] : Fintype x.RightMoves := by
  cases S; assumption
instance moveLeftShort (x : PGame) [S : Short x] (i : x.LeftMoves) : Short (x.moveLeft i) := by
  cases' S with _ _ _ _ L _ _ _; apply L
def moveLeftShort' {xl xr} (xL xR) [S : Short (mk xl xr xL xR)] (i : xl) : Short (xL i) := by
  cases' S with _ _ _ _ L _ _ _; apply L
attribute [local instance] moveLeftShort'
instance moveRightShort (x : PGame) [S : Short x] (j : x.RightMoves) : Short (x.moveRight j) := by
  cases' S with _ _ _ _ _ R _ _; apply R
def moveRightShort' {xl xr} (xL xR) [S : Short (mk xl xr xL xR)] (j : xr) : Short (xR j) := by
  cases' S with _ _ _ _ _ R _ _; apply R
attribute [local instance] moveRightShort'
theorem short_birthday (x : PGame.{u}) : [Short x] → x.birthday < Ordinal.omega0 := by
  induction x with
  | mk xl xr xL xR ihl ihr =>
    intro hs
    rcases hs with ⟨sL, sR⟩
    rw [birthday, max_lt_iff]
    constructor
    all_goals
      rw [← Cardinal.ord_aleph0]
      refine
        Cardinal.lsub_lt_ord_of_isRegular.{u, u} Cardinal.isRegular_aleph0
          (Cardinal.lt_aleph0_of_finite _) fun i => ?_
      rw [Cardinal.ord_aleph0]
    · apply ihl
    · apply ihr
def Short.ofIsEmpty {l r xL xR} [IsEmpty l] [IsEmpty r] : Short (PGame.mk l r xL xR) := by
  have : Fintype l := Fintype.ofIsEmpty
  have : Fintype r := Fintype.ofIsEmpty
  exact Short.mk isEmptyElim isEmptyElim
instance short0 : Short 0 :=
  Short.ofIsEmpty
instance short1 : Short 1 :=
  Short.mk (fun i => by cases i; infer_instance) fun j => by cases j
class inductive ListShort : List PGame.{u} → Type (u + 1)
  | nil : ListShort []
  | cons' {hd : PGame.{u}} {tl : List PGame.{u}} : Short hd → ListShort tl → ListShort (hd::tl)
attribute [instance] ListShort.nil
instance ListShort.cons
    (hd : PGame.{u}) [short_hd : Short hd] (tl : List PGame.{u}) [short_tl : ListShort tl] :
    ListShort (hd::tl) :=
  cons' short_hd short_tl
instance listShortGet :
    ∀ (L : List PGame.{u}) [ListShort L] (i : Nat) (h : i < List.length L), Short L[i]
  | _::_, ListShort.cons' S _, 0, _ => S
  | _::tl, ListShort.cons' _ S, n + 1, h =>
    @listShortGet tl S n ((add_lt_add_iff_right 1).mp h)
instance shortOfLists : ∀ (L R : List PGame) [ListShort L] [ListShort R], Short (PGame.ofLists L R)
  | L, R, _, _ => by
    exact Short.mk (fun i ↦ inferInstance) fun j ↦ listShortGet R (↑j.down) (ofLists.proof_2 R j)
def shortOfRelabelling : ∀ {x y : PGame.{u}}, Relabelling x y → Short x → Short y
  | x, y, ⟨L, R, rL, rR⟩, S => by
    haveI := Fintype.ofEquiv _ L
    haveI := Fintype.ofEquiv _ R
    exact
      Short.mk'
        (fun i => by rw [← L.right_inv i]; apply shortOfRelabelling (rL (L.symm i)) inferInstance)
        fun j => by simpa using shortOfRelabelling (rR (R.symm j)) inferInstance
instance shortNeg : ∀ (x : PGame.{u}) [Short x], Short (-x)
  | mk xl xr xL xR, _ => by
    exact Short.mk (fun i => shortNeg _) fun i => shortNeg _
instance shortAdd : ∀ (x y : PGame.{u}) [Short x] [Short y], Short (x + y)
  | mk xl xr xL xR, mk yl yr yL yR, _, _ => by
    apply Short.mk
    all_goals
      rintro ⟨i⟩
      · apply shortAdd
      · change Short (mk xl xr xL xR + _); apply shortAdd
termination_by x y => (x, y)
instance shortNat : ∀ n : ℕ, Short n
  | 0 => PGame.short0
  | n + 1 => @PGame.shortAdd _ _ (shortNat n) PGame.short1
instance shortOfNat (n : ℕ) [Nat.AtLeastTwo n] : Short (no_index (OfNat.ofNat n)) := shortNat n
instance shortBit0 (x : PGame.{u}) [Short x] : Short (x + x) := by infer_instance
instance shortBit1 (x : PGame.{u}) [Short x] : Short ((x + x) + 1) := shortAdd _ _
def leLFDecidable : ∀ (x y : PGame.{u}) [Short x] [Short y], Decidable (x ≤ y) × Decidable (x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR, shortx, shorty => by
    constructor
    · refine @decidable_of_iff' _ _ mk_le_mk (id ?_)
      have : Decidable (∀ (i : xl), xL i ⧏ mk yl yr yL yR) := by
        apply @Fintype.decidableForallFintype xl _ ?_ _
        intro i
        apply (leLFDecidable _ _).2
      have : Decidable (∀ (j : yr), mk xl xr xL xR ⧏ yR j) := by
        apply @Fintype.decidableForallFintype yr _ ?_ _
        intro i
        apply (leLFDecidable _ _).2
      exact inferInstanceAs (Decidable (_ ∧ _))
    · refine @decidable_of_iff' _ _ mk_lf_mk (id ?_)
      have : Decidable (∃ i, mk xl xr xL xR ≤ yL i) := by
        apply @Fintype.decidableExistsFintype yl _ ?_ _
        intro i
        apply (leLFDecidable _ _).1
      have : Decidable (∃ j, xR j ≤ mk yl yr yL yR) := by
        apply @Fintype.decidableExistsFintype xr _ ?_ _
        intro i
        apply (leLFDecidable _ _).1
      exact inferInstanceAs (Decidable (_ ∨ _))
termination_by x y => (x, y)
instance leDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ≤ y) :=
  (leLFDecidable x y).1
instance lfDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ⧏ y) :=
  (leLFDecidable x y).2
instance ltDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x < y) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance equivDecidable (x y : PGame.{u}) [Short x] [Short y] : Decidable (x ≈ y) :=
  inferInstanceAs (Decidable (_ ∧ _))
example : Short 0 := by infer_instance
example : Short 1 := by infer_instance
example : Short 2 := by infer_instance
example : Short (-2) := by infer_instance
example : Short (ofLists [0] [1]) := by infer_instance
example : Short (ofLists [-2, -1] [1]) := by infer_instance
example : Short (0 + 0) := by infer_instance
example : Decidable ((1 : PGame) ≤ 1) := by infer_instance
end PGame
end SetTheory