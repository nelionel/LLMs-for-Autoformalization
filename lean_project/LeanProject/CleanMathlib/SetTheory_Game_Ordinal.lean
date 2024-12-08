import Mathlib.SetTheory.Game.Basic
import Mathlib.SetTheory.Ordinal.NaturalOps
universe u
open SetTheory PGame
open scoped NaturalOps PGame
namespace Ordinal
noncomputable def toPGame (o : Ordinal.{u}) : PGame.{u} :=
  ⟨o.toType, PEmpty, fun x => ((enumIsoToType o).symm x).val.toPGame, PEmpty.elim⟩
termination_by o
decreasing_by exact ((enumIsoToType o).symm x).prop
@[deprecated "No deprecation message was provided." (since := "2024-09-22")]
theorem toPGame_def (o : Ordinal) : o.toPGame =
    ⟨o.toType, PEmpty, fun x => ((enumIsoToType o).symm x).val.toPGame, PEmpty.elim⟩ := by
  rw [toPGame]
@[simp]
theorem toPGame_leftMoves (o : Ordinal) : o.toPGame.LeftMoves = o.toType := by
  rw [toPGame, LeftMoves]
@[simp]
theorem toPGame_rightMoves (o : Ordinal) : o.toPGame.RightMoves = PEmpty := by
  rw [toPGame, RightMoves]
instance isEmpty_zero_toPGame_leftMoves : IsEmpty (toPGame 0).LeftMoves := by
  rw [toPGame_leftMoves]; infer_instance
instance isEmpty_toPGame_rightMoves (o : Ordinal) : IsEmpty o.toPGame.RightMoves := by
  rw [toPGame_rightMoves]; infer_instance
noncomputable def toLeftMovesToPGame {o : Ordinal} : Set.Iio o ≃ o.toPGame.LeftMoves :=
  (enumIsoToType o).toEquiv.trans (Equiv.cast (toPGame_leftMoves o).symm)
@[simp]
theorem toLeftMovesToPGame_symm_lt {o : Ordinal} (i : o.toPGame.LeftMoves) :
    ↑(toLeftMovesToPGame.symm i) < o :=
  (toLeftMovesToPGame.symm i).prop
@[nolint unusedHavesSuffices]
theorem toPGame_moveLeft_hEq {o : Ordinal} :
    HEq o.toPGame.moveLeft fun x : o.toType => ((enumIsoToType o).symm x).val.toPGame := by
  rw [toPGame]
  rfl
@[simp]
theorem toPGame_moveLeft' {o : Ordinal} (i) :
    o.toPGame.moveLeft i = (toLeftMovesToPGame.symm i).val.toPGame :=
  (congr_heq toPGame_moveLeft_hEq.symm (cast_heq _ i)).symm
theorem toPGame_moveLeft {o : Ordinal} (i) :
    o.toPGame.moveLeft (toLeftMovesToPGame i) = i.val.toPGame := by simp
noncomputable def zeroToPGameRelabelling : toPGame 0 ≡r 0 :=
  Relabelling.isEmpty _
theorem toPGame_zero : toPGame 0 ≈ 0 :=
  zeroToPGameRelabelling.equiv
noncomputable instance uniqueOneToPGameLeftMoves : Unique (toPGame 1).LeftMoves :=
  (Equiv.cast <| toPGame_leftMoves 1).unique
@[simp]
theorem one_toPGame_leftMoves_default_eq :
    (default : (toPGame 1).LeftMoves) = @toLeftMovesToPGame 1 ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ :=
  rfl
@[simp]
theorem to_leftMoves_one_toPGame_symm (i) :
    (@toLeftMovesToPGame 1).symm i = ⟨0, Set.mem_Iio.mpr zero_lt_one⟩ := by
  simp [eq_iff_true_of_subsingleton]
theorem one_toPGame_moveLeft (x) : (toPGame 1).moveLeft x = toPGame 0 := by simp
noncomputable def oneToPGameRelabelling : toPGame 1 ≡r 1 :=
  ⟨Equiv.equivOfUnique _ _, Equiv.equivOfIsEmpty _ _, fun i => by
    simpa using zeroToPGameRelabelling, isEmptyElim⟩
theorem toPGame_one : toPGame 1 ≈ 1 :=
  oneToPGameRelabelling.equiv
theorem toPGame_lf {a b : Ordinal} (h : a < b) : a.toPGame ⧏ b.toPGame := by
  convert moveLeft_lf (toLeftMovesToPGame ⟨a, h⟩); rw [toPGame_moveLeft]
theorem toPGame_le {a b : Ordinal} (h : a ≤ b) : a.toPGame ≤ b.toPGame := by
  refine le_iff_forall_lf.2 ⟨fun i => ?_, isEmptyElim⟩
  rw [toPGame_moveLeft']
  exact toPGame_lf ((toLeftMovesToPGame_symm_lt i).trans_le h)
theorem toPGame_lt {a b : Ordinal} (h : a < b) : a.toPGame < b.toPGame :=
  ⟨toPGame_le h.le, toPGame_lf h⟩
theorem toPGame_nonneg (a : Ordinal) : 0 ≤ a.toPGame :=
  zeroToPGameRelabelling.ge.trans <| toPGame_le <| Ordinal.zero_le a
@[simp]
theorem toPGame_lf_iff {a b : Ordinal} : a.toPGame ⧏ b.toPGame ↔ a < b :=
  ⟨by contrapose; rw [not_lt, not_lf]; exact toPGame_le, toPGame_lf⟩
@[simp]
theorem toPGame_le_iff {a b : Ordinal} : a.toPGame ≤ b.toPGame ↔ a ≤ b :=
  ⟨by contrapose; rw [not_le, PGame.not_le]; exact toPGame_lf, toPGame_le⟩
@[simp]
theorem toPGame_lt_iff {a b : Ordinal} : a.toPGame < b.toPGame ↔ a < b :=
  ⟨by contrapose; rw [not_lt]; exact fun h => not_lt_of_le (toPGame_le h), toPGame_lt⟩
@[simp]
theorem toPGame_equiv_iff {a b : Ordinal} : (a.toPGame ≈ b.toPGame) ↔ a = b := by
  change _ ≤_ ∧ _ ≤ _ ↔ _
  rw [le_antisymm_iff, toPGame_le_iff, toPGame_le_iff]
theorem toPGame_injective : Function.Injective Ordinal.toPGame := fun _ _ h =>
  toPGame_equiv_iff.1 <| equiv_of_eq h
@[simp]
theorem toPGame_eq_iff {a b : Ordinal} : a.toPGame = b.toPGame ↔ a = b :=
  toPGame_injective.eq_iff
@[simps]
noncomputable def toPGameEmbedding : Ordinal.{u} ↪o PGame.{u} where
  toFun := Ordinal.toPGame
  inj' := toPGame_injective
  map_rel_iff' := @toPGame_le_iff
noncomputable abbrev toGame (o : Ordinal) : Game := ⟦o.toPGame⟧
@[simps]
noncomputable def toGameEmbedding : Ordinal.{u} ↪o Game.{u} where
  toFun := Ordinal.toGame
  inj' a b := by simpa [AntisymmRel] using le_antisymm
  map_rel_iff' := toPGame_le_iff
@[simp]
theorem toGame_zero : toGame 0 = 0 :=
  game_eq toPGame_zero
@[simp]
theorem toGame_one : toGame 1 = 1 :=
  game_eq toPGame_one
theorem toGame_injective : Function.Injective toGame :=
  toGameEmbedding.injective
@[simp]
theorem toGame_lf_iff {a b : Ordinal} : Game.LF (toGame a) (toGame b) ↔ a < b :=
  toPGame_lf_iff
@[simp]
theorem toGame_le_iff {a b : Ordinal} : toGame a ≤ toGame b ↔ a ≤ b :=
  toPGame_le_iff
@[simp]
theorem toGame_lt_iff {a b : Ordinal} : toGame a < toGame b ↔ a < b :=
  toPGame_lt_iff
theorem toGame_eq_iff {a b : Ordinal} : toGame a = toGame b ↔ a = b :=
  toGameEmbedding.inj
theorem toPGame_nadd (a b : Ordinal) : (a ♯ b).toPGame ≈ a.toPGame + b.toPGame := by
  refine ⟨le_of_forall_lf (fun i => ?_) isEmptyElim, le_of_forall_lf (fun i => ?_) isEmptyElim⟩
  · rw [toPGame_moveLeft']
    rcases lt_nadd_iff.1 (toLeftMovesToPGame_symm_lt i) with (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩) <;>
    rw [← toPGame_le_iff, le_congr_right (toPGame_nadd _ _)] at hc' <;>
    apply lf_of_le_of_lf hc'
    · apply add_lf_add_right
      rwa [toPGame_lf_iff]
    · apply add_lf_add_left
      rwa [toPGame_lf_iff]
  · apply leftMoves_add_cases i <;>
    intro i <;>
    let wf := toLeftMovesToPGame_symm_lt i <;>
    (try rw [add_moveLeft_inl]) <;>
    (try rw [add_moveLeft_inr]) <;>
    rw [toPGame_moveLeft', ← lf_congr_left (toPGame_nadd _ _), toPGame_lf_iff]
    · exact nadd_lt_nadd_right wf _
    · exact nadd_lt_nadd_left wf _
termination_by (a, b)
theorem toGame_nadd (a b : Ordinal) : (a ♯ b).toGame = a.toGame + b.toGame :=
  game_eq (toPGame_nadd a b)
theorem toPGame_nmul (a b : Ordinal) : (a ⨳ b).toPGame ≈ a.toPGame * b.toPGame := by
  refine ⟨le_of_forall_lf (fun i => ?_) isEmptyElim, le_of_forall_lf (fun i => ?_) isEmptyElim⟩
  · rw [toPGame_moveLeft']
    rcases lt_nmul_iff.1 (toLeftMovesToPGame_symm_lt i) with ⟨c, hc, d, hd, h⟩
    rw [← toPGame_le_iff, le_iff_game_le, ← toGame, ← toGame, toGame_nadd _ _, toGame_nadd _ _,
      ← le_sub_iff_add_le] at h
    refine lf_of_le_of_lf h <| (lf_congr_left ?_).1 <| moveLeft_lf <| toLeftMovesMul <| Sum.inl
      ⟨toLeftMovesToPGame ⟨c, hc⟩, toLeftMovesToPGame ⟨d, hd⟩⟩
    simp only [mul_moveLeft_inl, toPGame_moveLeft', Equiv.symm_apply_apply, equiv_iff_game_eq,
      quot_sub, quot_add]
    repeat rw [← game_eq (toPGame_nmul _ _)]
    rfl
  · apply leftMoves_mul_cases i _ isEmptyElim
    intro i j
    rw [mul_moveLeft_inl, toPGame_moveLeft', toPGame_moveLeft', lf_iff_game_lf,
      quot_sub, quot_add, ← Game.not_le, le_sub_iff_add_le]
    repeat rw [← game_eq (toPGame_nmul _ _)]
    repeat rw [← toGame_nadd]
    apply toPGame_lf (nmul_nadd_lt _ _) <;>
    exact toLeftMovesToPGame_symm_lt _
termination_by (a, b)
theorem toGame_nmul (a b : Ordinal) : (a ⨳ b).toGame = ⟦a.toPGame * b.toPGame⟧ :=
  game_eq (toPGame_nmul a b)
@[simp, norm_cast]
theorem toGame_natCast : ∀ n : ℕ, toGame n = n
  | 0 => Quot.sound (zeroToPGameRelabelling).equiv
  | n + 1 => by
    have : toGame 1 = 1 := Quot.sound oneToPGameRelabelling.equiv
    rw [Nat.cast_add, ← nadd_nat, toGame_nadd, toGame_natCast, Nat.cast_one, this]
    rfl
theorem toPGame_natCast (n : ℕ) : toPGame n ≈ n := by
  rw [PGame.equiv_iff_game_eq, ← toGame, toGame_natCast, quot_natCast]
end Ordinal