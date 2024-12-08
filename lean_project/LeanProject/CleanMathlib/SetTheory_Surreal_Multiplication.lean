import Mathlib.Logic.Hydra
import Mathlib.SetTheory.Surreal.Basic
universe u
open SetTheory Game PGame WellFounded
namespace Surreal.Multiplication
def P1 (x₁ x₂ x₃ y₁ y₂ y₃ : PGame) :=
  ⟦x₁ * y₁⟧ + ⟦x₂ * y₂⟧ - ⟦x₁ * y₂⟧ < ⟦x₃ * y₁⟧ + ⟦x₂ * y₃⟧ - (⟦x₃ * y₃⟧ : Game)
def P2 (x₁ x₂ y : PGame) := x₁ ≈ x₂ → ⟦x₁ * y⟧ = (⟦x₂ * y⟧ : Game)
def P3 (x₁ x₂ y₁ y₂ : PGame) := ⟦x₁ * y₂⟧ + ⟦x₂ * y₁⟧ < ⟦x₁ * y₁⟧ + (⟦x₂ * y₂⟧ : Game)
def P4 (x₁ x₂ y : PGame) :=
  x₁ < x₂ → (∀ i, P3 x₁ x₂ (y.moveLeft i) y) ∧ ∀ j, P3 x₁ x₂ ((-y).moveLeft j) (-y)
def P24 (x₁ x₂ y : PGame) : Prop := P2 x₁ x₂ y ∧ P4 x₁ x₂ y
variable {x x₁ x₂ x₃ x' y y₁ y₂ y₃ y' : PGame.{u}}
lemma P3_comm : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ := by
  rw [P3, P3, add_comm]
  congr! 2 <;> rw [quot_mul_comm]
lemma P3.trans (h₁ : P3 x₁ x₂ y₁ y₂) (h₂ : P3 x₂ x₃ y₁ y₂) : P3 x₁ x₃ y₁ y₂ := by
  rw [P3] at h₁ h₂
  rw [P3, ← add_lt_add_iff_left (⟦x₂ * y₁⟧ + ⟦x₂ * y₂⟧)]
  convert add_lt_add h₁ h₂ using 1 <;> abel
lemma P3_neg : P3 x₁ x₂ y₁ y₂ ↔ P3 (-x₂) (-x₁) y₁ y₂ := by
  simp_rw [P3, quot_neg_mul]
  rw [← _root_.neg_lt_neg_iff]
  abel_nf
lemma P2_neg_left : P2 x₁ x₂ y ↔ P2 (-x₂) (-x₁) y := by
  rw [P2, P2]
  constructor
  · rw [quot_neg_mul, quot_neg_mul, eq_comm, neg_inj, neg_equiv_neg_iff, PGame.equiv_comm]
    exact (· ·)
  · rw [PGame.equiv_comm, neg_equiv_neg_iff, quot_neg_mul, quot_neg_mul, neg_inj, eq_comm]
    exact (· ·)
lemma P2_neg_right : P2 x₁ x₂ y ↔ P2 x₁ x₂ (-y) := by
  rw [P2, P2, quot_mul_neg, quot_mul_neg, neg_inj]
lemma P4_neg_left : P4 x₁ x₂ y ↔ P4 (-x₂) (-x₁) y := by
  simp_rw [P4, PGame.neg_lt_neg_iff, moveLeft_neg', ← P3_neg]
lemma P4_neg_right : P4 x₁ x₂ y ↔ P4 x₁ x₂ (-y) := by
  rw [P4, P4, neg_neg, and_comm]
lemma P24_neg_left : P24 x₁ x₂ y ↔ P24 (-x₂) (-x₁) y := by rw [P24, P24, P2_neg_left, P4_neg_left]
lemma P24_neg_right : P24 x₁ x₂ y ↔ P24 x₁ x₂ (-y) := by rw [P24, P24, P2_neg_right, P4_neg_right]
lemma mulOption_lt_iff_P1 {i j k l} :
    (⟦mulOption x y i k⟧ : Game) < -⟦mulOption x (-y) j l⟧ ↔
    P1 (x.moveLeft i) x (x.moveLeft j) y (y.moveLeft k) (-(-y).moveLeft l) := by
  dsimp only [P1, mulOption, quot_sub, quot_add]
  simp_rw [neg_sub', neg_add, quot_mul_neg, neg_neg]
lemma mulOption_lt_mul_iff_P3 {i j} :
    ⟦mulOption x y i j⟧ < (⟦x * y⟧ : Game) ↔ P3 (x.moveLeft i) x (y.moveLeft j) y := by
  dsimp only [mulOption, quot_sub, quot_add]
  exact sub_lt_iff_lt_add'
lemma P1_of_eq (he : x₁ ≈ x₃) (h₁ : P2 x₁ x₃ y₁) (h₃ : P2 x₁ x₃ y₃) (h3 : P3 x₁ x₂ y₂ y₃) :
    P1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [P1, ← h₁ he, ← h₃ he, sub_lt_sub_iff]
  convert add_lt_add_left h3 ⟦x₁ * y₁⟧ using 1 <;> abel
lemma P1_of_lt (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) : P1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [P1, sub_lt_sub_iff, ← add_lt_add_iff_left ⟦x₃ * y₂⟧]
  convert add_lt_add h₁ h₂ using 1 <;> abel
inductive Args : Type (u+1)
  | P1 (x y : PGame.{u}) : Args
  | P24 (x₁ x₂ y : PGame.{u}) : Args
def Args.toMultiset : Args → Multiset PGame
  | (Args.P1 x y) => {x, y}
  | (Args.P24 x₁ x₂ y) => {x₁, x₂, y}
def Args.Numeric (a : Args) := ∀ x ∈ a.toMultiset, SetTheory.PGame.Numeric x
lemma Args.numeric_P1 {x y} : (Args.P1 x y).Numeric ↔ x.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]
lemma Args.numeric_P24 {x₁ x₂ y} :
    (Args.P24 x₁ x₂ y).Numeric ↔ x₁.Numeric ∧ x₂.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]
open Relation
def ArgsRel := InvImage (TransGen <| CutExpand IsOption) Args.toMultiset
theorem argsRel_wf : WellFounded ArgsRel := InvImage.wf _ wf_isOption.cutExpand.transGen
def P124 : Args → Prop
  | (Args.P1 x y) => Numeric (x * y)
  | (Args.P24 x₁ x₂ y) => P24 x₁ x₂ y
lemma ArgsRel.numeric_closed {a' a} : ArgsRel a' a → a.Numeric → a'.Numeric :=
  TransGen.closed' <| @cutExpand_closed _ IsOption ⟨wf_isOption.isIrrefl.1⟩ _ Numeric.isOption
def IH1 (x y : PGame) : Prop :=
  ∀ ⦃x₁ x₂ y'⦄, IsOption x₁ x → IsOption x₂ x → (y' = y ∨ IsOption y' y) → P24 x₁ x₂ y'
lemma ih1_neg_left : IH1 x y → IH1 (-x) y :=
  fun h x₁ x₂ y' h₁ h₂ hy ↦ by
    rw [isOption_neg] at h₁ h₂
    exact P24_neg_left.2 (h h₂ h₁ hy)
lemma ih1_neg_right : IH1 x y → IH1 x (-y) :=
  fun h x₁ x₂ y' ↦ by
    rw [← neg_eq_iff_eq_neg, isOption_neg, P24_neg_right]
    apply h
lemma numeric_option_mul (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (h : IsOption x' x) :
    (x' * y).Numeric :=
  ih (Args.P1 x' y) (TransGen.single <| cutExpand_pair_left h)
lemma numeric_mul_option (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (h : IsOption y' y) :
    (x * y').Numeric :=
  ih (Args.P1 x y') (TransGen.single <| cutExpand_pair_right h)
lemma numeric_option_mul_option (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (hx : IsOption x' x)
    (hy : IsOption y' y) : (x' * y').Numeric :=
  ih (Args.P1 x' y') ((TransGen.single <| cutExpand_pair_right hy).tail <| cutExpand_pair_left hx)
lemma ih1 (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 x y := by
  rintro x₁ x₂ y' h₁ h₂ (rfl|hy) <;> apply ih (Args.P24 _ _ _)
  on_goal 2 => refine TransGen.tail ?_ (cutExpand_pair_right hy)
  all_goals exact TransGen.single (cutExpand_double_left h₁ h₂)
lemma ih1_swap (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 y x := ih1 <| by
  simp_rw [ArgsRel, InvImage, Args.toMultiset, Multiset.pair_comm] at ih ⊢
  exact ih
lemma P3_of_ih (hy : Numeric y) (ihyx : IH1 y x) (i k l) :
    P3 (x.moveLeft i) x (y.moveLeft k) (-(-y).moveLeft l) :=
  P3_comm.2 <| ((ihyx (IsOption.moveLeft k) (isOption_neg.1 <| .moveLeft l) <| Or.inl rfl).2
    (by rw [← moveRight_neg_symm]; apply hy.left_lt_right)).1 i
lemma P24_of_ih (ihxy : IH1 x y) (i j) : P24 (x.moveLeft i) (x.moveLeft j) y :=
  ihxy (IsOption.moveLeft i) (IsOption.moveLeft j) (Or.inl rfl)
section
lemma mulOption_lt_of_lt (hy : y.Numeric) (ihxy : IH1 x y) (ihyx : IH1 y x) (i j k l)
    (h : x.moveLeft i < x.moveLeft j) :
    (⟦mulOption x y i k⟧ : Game) < -⟦mulOption x (-y) j l⟧ :=
  mulOption_lt_iff_P1.2 <| P1_of_lt (P3_of_ih hy ihyx j k l) <| ((P24_of_ih ihxy i j).2 h).1 k
lemma mulOption_lt (hx : x.Numeric) (hy : y.Numeric) (ihxy : IH1 x y) (ihyx : IH1 y x) (i j k l) :
    (⟦mulOption x y i k⟧ : Game) < -⟦mulOption x (-y) j l⟧ := by
  obtain (h|h|h) := lt_or_equiv_or_gt (hx.moveLeft i) (hx.moveLeft j)
  · exact mulOption_lt_of_lt hy ihxy ihyx i j k l h
  · have ml := @IsOption.moveLeft
    exact mulOption_lt_iff_P1.2 (P1_of_eq h (P24_of_ih ihxy i j).1
      (ihxy (ml i) (ml j) <| Or.inr <| isOption_neg.1 <| ml l).1 <| P3_of_ih hy ihyx i k l)
  · rw [mulOption_neg_neg, lt_neg]
    exact mulOption_lt_of_lt hy.neg (ih1_neg_right ihxy) (ih1_neg_left ihyx) j i l _ h
end
theorem P1_of_ih (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (hx : x.Numeric) (hy : y.Numeric) :
    (x * y).Numeric := by
  have ihxy := ih1 ih
  have ihyx := ih1_swap ih
  have ihxyn := ih1_neg_left (ih1_neg_right ihxy)
  have ihyxn := ih1_neg_left (ih1_neg_right ihyx)
  refine numeric_def.mpr ⟨?_, ?_, ?_⟩
  · simp_rw [lt_iff_game_lt]
    intro i
    rw [rightMoves_mul_iff]
    constructor <;> (intro j l; revert i; rw [leftMoves_mul_iff (_ > ·)]; constructor <;> intro i k)
    · apply mulOption_lt hx hy ihxy ihyx
    · simp_rw [← mulOption_symm (-y), mulOption_neg_neg x]
      apply mulOption_lt hy.neg hx.neg ihyxn ihxyn
    · simp only [← mulOption_symm y]
      apply mulOption_lt hy hx ihyx ihxy
    · rw [mulOption_neg_neg y]
      apply mulOption_lt hx.neg hy.neg ihxyn ihyxn
  all_goals
    cases x; cases y
    rintro (⟨i,j⟩|⟨i,j⟩) <;>
    refine ((numeric_option_mul ih ?_).add <| numeric_mul_option ih ?_).sub
      (numeric_option_mul_option ih ?_ ?_) <;>
    solve_by_elim [IsOption.mk_left, IsOption.mk_right]
def IH24 (x₁ x₂ y : PGame) : Prop :=
  ∀ ⦃z⦄, (IsOption z x₁ → P24 z x₂ y) ∧ (IsOption z x₂ → P24 x₁ z y) ∧ (IsOption z y → P24 x₁ x₂ z)
def IH4 (x₁ x₂ y : PGame) : Prop :=
  ∀ ⦃z w⦄, IsOption w y → (IsOption z x₁ → P2 z x₂ w) ∧ (IsOption z x₂ → P2 x₁ z w)
lemma ih₁₂ (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₁ x₂ y := by
  rw [IH24]
  refine fun z ↦ ⟨?_, ?_, ?_⟩ <;>
    refine fun h ↦ ih' (Args.P24 _ _ _) (TransGen.single ?_)
  · exact (cutExpand_add_right {y}).2 (cutExpand_pair_left h)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_left h)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_right h)
lemma ih₂₁ (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₂ x₁ y := ih₁₂ <| by
  simp_rw [ArgsRel, InvImage, Args.toMultiset, Multiset.pair_comm] at ih' ⊢
  suffices {x₁, y, x₂} = {x₂, y, x₁} by rwa [← this]
  dsimp only [Multiset.insert_eq_cons, ← Multiset.singleton_add] at ih' ⊢
  abel
lemma ih4 (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH4 x₁ x₂ y := by
  refine fun z w h ↦ ⟨?_, ?_⟩
  all_goals
    intro h'
    apply (ih' (Args.P24 _ _ _) <| (TransGen.single _).tail <|
      (cutExpand_add_left {x₁}).2 <| cutExpand_pair_right h).1
    try exact (cutExpand_add_right {w}).2 <| cutExpand_pair_left h'
    try exact (cutExpand_add_right {w}).2 <| cutExpand_pair_right h'
lemma numeric_of_ih (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) :
    (x₁ * y).Numeric ∧ (x₂ * y).Numeric := by
  constructor <;> refine ih' (Args.P1 _ _) (TransGen.single ?_)
  · exact (cutExpand_add_right {y}).2 <| (cutExpand_add_left {x₁}).2 cutExpand_zero
  · exact (cutExpand_add_right {x₂, y}).2 cutExpand_zero
lemma ih24_neg : IH24 x₁ x₂ y → IH24 (-x₂) (-x₁) y ∧ IH24 x₁ x₂ (-y) := by
  simp_rw [IH24, ← P24_neg_right, isOption_neg]
  refine fun h ↦ ⟨fun z ↦ ⟨?_, ?_, ?_⟩,
    fun z ↦ ⟨(@h z).1, (@h z).2.1, P24_neg_right.2 ∘ (@h <| -z).2.2⟩⟩
  all_goals
    rw [P24_neg_left]
    simp only [neg_neg]
    first | exact (@h <| -z).2.1 | exact (@h <| -z).1 | exact (@h z).2.2
lemma ih4_neg : IH4 x₁ x₂ y → IH4 (-x₂) (-x₁) y ∧ IH4 x₁ x₂ (-y) := by
  simp_rw [IH4, isOption_neg]
  refine fun h ↦ ⟨fun z w h' ↦ ?_, fun z w h' ↦ ?_⟩
  · convert (h h').symm using 2 <;> rw [P2_neg_left, neg_neg]
  · convert h h' using 2 <;> rw [P2_neg_right]
lemma mulOption_lt_mul_of_equiv (hn : x₁.Numeric) (h : IH24 x₁ x₂ y) (he : x₁ ≈ x₂) (i j) :
    ⟦mulOption x₁ y i j⟧ < (⟦x₂ * y⟧ : Game) := by
  convert sub_lt_iff_lt_add'.2 ((((@h _).1 <| IsOption.moveLeft i).2 _).1 j) using 1
  · rw [← ((@h _).2.2 <| IsOption.moveLeft j).1 he]
    rfl
  · rw [← lt_congr_right he]
    apply hn.moveLeft_lt
theorem mul_right_le_of_equiv (h₁ : x₁.Numeric) (h₂ : x₂.Numeric)
    (h₁₂ : IH24 x₁ x₂ y) (h₂₁ : IH24 x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y := by
  have he' := neg_equiv_neg_iff.2 he
  apply PGame.le_of_forall_lt <;> simp_rw [lt_iff_game_lt]
  · rw [leftMoves_mul_iff (_ > ·)]
    refine ⟨mulOption_lt_mul_of_equiv h₁ h₁₂ he, ?_⟩
    rw [← quot_neg_mul_neg]
    exact mulOption_lt_mul_of_equiv h₁.neg (ih24_neg <| (ih24_neg h₂₁).1).2 he'
  · rw [rightMoves_mul_iff]
    constructor <;> intros <;> rw [lt_neg]
    · rw [← quot_mul_neg]
      apply mulOption_lt_mul_of_equiv h₂ (ih24_neg h₂₁).2 (symm he)
    · rw [← quot_neg_mul]
      apply mulOption_lt_mul_of_equiv h₂.neg (ih24_neg h₁₂).1 (symm he')
def MulOptionsLTMul (x y : PGame) : Prop := ∀ ⦃i j⦄, ⟦mulOption x y i j⟧ < (⟦x * y⟧ : Game)
lemma mulOptionsLTMul_of_numeric (hn : (x * y).Numeric) :
    (MulOptionsLTMul x y ∧ MulOptionsLTMul (-x) (-y)) ∧
    (MulOptionsLTMul x (-y) ∧ MulOptionsLTMul (-x) y) := by
  constructor
  · have h := hn.moveLeft_lt
    simp_rw [lt_iff_game_lt] at h
    convert (leftMoves_mul_iff <| GT.gt _).1 h
    rw [← quot_neg_mul_neg]
    rfl
  · have h := hn.lt_moveRight
    simp_rw [lt_iff_game_lt, rightMoves_mul_iff] at h
    refine h.imp ?_ ?_ <;> refine forall₂_imp fun a b ↦ ?_
    all_goals
      rw [lt_neg]
      first | rw [quot_mul_neg] | rw [quot_neg_mul]
      exact id
def IH3 (x₁ x' x₂ y₁ y₂ : PGame) : Prop :=
    P2 x₁ x' y₁ ∧ P2 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)
lemma ih3_of_ih (h24 : IH24 x₁ x₂ y) (h4 : IH4 x₁ x₂ y) (hl : MulOptionsLTMul x₂ y) (i j) :
    IH3 x₁ (x₂.moveLeft i) x₂ (y.moveLeft j) y :=
  have ml := @IsOption.moveLeft
  have h24 := (@h24 _).2.1 (ml i)
  ⟨(h4 <| ml j).2 (ml i), h24.1, mulOption_lt_mul_iff_P3.1 (@hl i j), fun l ↦ (h24.2 l).1 _⟩
lemma P3_of_le_left {y₁ y₂} (i) (h : IH3 x₁ (x₂.moveLeft i) x₂ y₁ y₂) (hl : x₁ ≤ x₂.moveLeft i) :
    P3 x₁ x₂ y₁ y₂ := by
  obtain (hl|he) := lt_or_equiv_of_le hl
  · exact (h.2.2.2 hl).trans h.2.2.1
  · rw [P3, h.1 he, h.2.1 he]
    exact h.2.2.1
theorem P3_of_lt {y₁ y₂} (h : ∀ i, IH3 x₁ (x₂.moveLeft i) x₂ y₁ y₂)
    (hs : ∀ i, IH3 (-x₂) ((-x₁).moveLeft i) (-x₁) y₁ y₂) (hl : x₁ < x₂) :
    P3 x₁ x₂ y₁ y₂ := by
  obtain (⟨i,hi⟩|⟨i,hi⟩) := lf_iff_exists_le.1 (lf_of_lt hl)
  · exact P3_of_le_left i (h i) hi
  · exact P3_neg.2 <| P3_of_le_left _ (hs _) <| by
      rw [moveLeft_neg]
      exact neg_le_neg (le_iff_game_le.1 hi)
theorem main (a : Args) : a.Numeric → P124 a := by
  apply argsRel_wf.induction a
  intros a ih ha
  replace ih : ∀ a', ArgsRel a' a → P124 a' := fun a' hr ↦ ih a' hr (hr.numeric_closed ha)
  cases a with
  | P1 x y =>
    rw [Args.numeric_P1] at ha
    exact P1_of_ih ih ha.1 ha.2
  | P24 x₁ x₂ y =>
    have h₁₂ := ih₁₂ ih
    have h₂₁ := ih₂₁ ih
    have h4 := ih4 ih
    obtain ⟨h₁₂x, h₁₂y⟩ := ih24_neg h₁₂
    obtain ⟨h4x, h4y⟩ := ih4_neg h4
    refine ⟨fun he ↦ Quotient.sound ?_, fun hl ↦ ?_⟩
    · 
      rw [Args.numeric_P24] at ha
      exact ⟨mul_right_le_of_equiv ha.1 ha.2.1 h₁₂ h₂₁ he,
        mul_right_le_of_equiv ha.2.1 ha.1 h₂₁ h₁₂ (symm he)⟩
    · 
      obtain ⟨hn₁, hn₂⟩ := numeric_of_ih ih
      obtain ⟨⟨h₁, -⟩, h₂, -⟩ := mulOptionsLTMul_of_numeric hn₂
      obtain ⟨⟨-, h₃⟩, -, h₄⟩ := mulOptionsLTMul_of_numeric hn₁
      constructor <;> intro <;> refine P3_of_lt ?_ ?_ hl <;> intro <;> apply ih3_of_ih
      any_goals assumption
      exacts [(ih24_neg h₁₂y).1, (ih4_neg h4y).1]
end Surreal.Multiplication
namespace SetTheory.PGame
open Surreal.Multiplication
variable {x x₁ x₂ y y₁ y₂ : PGame.{u}}
theorem Numeric.mul (hx : x.Numeric) (hy : y.Numeric) : Numeric (x * y) :=
  main _ <| Args.numeric_P1.mpr ⟨hx, hy⟩
theorem P24 (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy : y.Numeric) : P24 x₁ x₂ y :=
  main _ <| Args.numeric_P24.mpr ⟨hx₁, hx₂, hy⟩
theorem Equiv.mul_congr_left (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy : y.Numeric)
    (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
  equiv_iff_game_eq.2 <| (P24 hx₁ hx₂ hy).1 he
theorem Equiv.mul_congr_right (hx : x.Numeric) (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric)
    (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ :=
  .trans (mul_comm_equiv _ _) <| .trans (mul_congr_left hy₁ hy₂ hx he) (mul_comm_equiv _ _)
theorem Equiv.mul_congr (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric)
    (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric) (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
  .trans (mul_congr_left hx₁ hx₂ hy₁ hx) (mul_congr_right hx₂ hy₁ hy₂ hy)
open Prod.GameAdd
theorem P3_of_lt_of_lt (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric)
    (hx : x₁ < x₂) (hy : y₁ < y₂) : P3 x₁ x₂ y₁ y₂ := by
  revert x₁ x₂
  rw [← Prod.forall']
  refine (wf_isOption.prod_gameAdd wf_isOption).fix ?_
  rintro ⟨x₁, x₂⟩ ih hx₁ hx₂ hx
  refine P3_of_lt ?_ ?_ hx <;> intro i
  · have hi := hx₂.moveLeft i
    exact ⟨(P24 hx₁ hi hy₁).1, (P24 hx₁ hi hy₂).1,
      P3_comm.2 <| ((P24 hy₁ hy₂ hx₂).2 hy).1 _,
      ih _ (snd <| IsOption.moveLeft i) hx₁ hi⟩
  · have hi := hx₁.neg.moveLeft i
    exact ⟨(P24 hx₂.neg hi hy₁).1, (P24 hx₂.neg hi hy₂).1,
      P3_comm.2 <| ((P24 hy₁ hy₂ hx₁).2 hy).2 _, by
        rw [moveLeft_neg', ← P3_neg, neg_lt_neg_iff]
        exact ih _ (fst <| IsOption.moveRight _) (hx₁.moveRight _) hx₂⟩
theorem Numeric.mul_pos (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hp₁ : 0 < x₁) (hp₂ : 0 < x₂) :
    0 < x₁ * x₂ := by
  rw [lt_iff_game_lt]
  have := P3_of_lt_of_lt numeric_zero hx₁ numeric_zero hx₂ hp₁ hp₂
  simp_rw [P3, quot_zero_mul, quot_mul_zero, add_lt_add_iff_left] at this
  exact this
end SetTheory.PGame
namespace Surreal
open SetTheory.PGame.Equiv
noncomputable instance : LinearOrderedCommRing Surreal where
  __ := Surreal.orderedAddCommGroup
  mul := Surreal.lift₂ (fun x y ox oy ↦ ⟦⟨x * y, ox.mul oy⟩⟧)
    (fun ox₁ oy₁ ox₂ oy₂ hx hy ↦ Quotient.sound <| mul_congr ox₁ ox₂ oy₁ oy₂ hx hy)
  mul_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (mul_assoc_equiv _ _ _)
  one := mk 1 numeric_one
  one_mul := by rintro ⟨_⟩; exact Quotient.sound (one_mul_equiv _)
  mul_one := by rintro ⟨_⟩; exact Quotient.sound (mul_one_equiv _)
  left_distrib := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (left_distrib_equiv _ _ _)
  right_distrib := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (right_distrib_equiv _ _ _)
  mul_comm := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound (mul_comm_equiv _ _)
  le := lift₂ (fun x y _ _ ↦ x ≤ y) (fun _ _ _ _ hx hy ↦ propext <| le_congr hx hy)
  lt := lift₂ (fun x y _ _ ↦ x < y) (fun _ _ _ _ hx hy ↦ propext <| lt_congr hx hy)
  le_refl := by rintro ⟨_⟩; apply @le_rfl PGame
  le_trans := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; apply @le_trans PGame
  lt_iff_le_not_le := by rintro ⟨_⟩ ⟨_⟩; exact lt_iff_le_not_le
  le_antisymm := by rintro ⟨_⟩ ⟨_⟩ h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩
  add_le_add_left := by rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩; exact add_le_add_left hx _
  zero_le_one := PGame.zero_lt_one.le
  zero_mul := by rintro ⟨_⟩; exact Quotient.sound (zero_mul_equiv _)
  mul_zero := by rintro ⟨_⟩; exact Quotient.sound (mul_zero_equiv _)
  exists_pair_ne := ⟨0, 1, ne_of_lt PGame.zero_lt_one⟩
  le_total := by rintro ⟨x⟩ ⟨y⟩; exact (le_or_gf x.1 y.1).imp id (fun h ↦ h.le y.2 x.2)
  mul_pos := by rintro ⟨x⟩ ⟨y⟩; exact x.2.mul_pos y.2
  decidableLE := Classical.decRel _
end Surreal