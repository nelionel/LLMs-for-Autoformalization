import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Translations
assert_not_exists Finset
namespace GenContFract
open GenContFract (of)
variable {K : Type*} [LinearOrderedField K] [FloorRing K] {v : K}
namespace IntFractPair
theorem stream_zero (v : K) : IntFractPair.stream v 0 = some (IntFractPair.of v) :=
  rfl
variable {n : ℕ}
theorem stream_eq_none_of_fr_eq_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    IntFractPair.stream v (n + 1) = none := by
  obtain ⟨_, fr⟩ := ifp_n
  change fr = 0 at nth_fr_eq_zero
  simp [IntFractPair.stream, stream_nth_eq, nth_fr_eq_zero]
theorem succ_nth_stream_eq_none_iff :
    IntFractPair.stream v (n + 1) = none ↔
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 := by
  rw [IntFractPair.stream]
  cases IntFractPair.stream v n <;> simp [imp_false]
theorem succ_nth_stream_eq_some_iff {ifp_succ_n : IntFractPair K} :
    IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      ∃ ifp_n : IntFractPair K,
        IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n := by
  simp [IntFractPair.stream, ite_eq_iff, Option.bind_eq_some]
theorem stream_succ_of_some {p : IntFractPair K} (h : IntFractPair.stream v n = some p)
    (h' : p.fr ≠ 0) : IntFractPair.stream v (n + 1) = some (IntFractPair.of p.fr⁻¹) :=
  succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩
theorem stream_succ_of_int (a : ℤ) (n : ℕ) : IntFractPair.stream (a : K) (n + 1) = none := by
  induction n with
  | zero =>
    refine IntFractPair.stream_eq_none_of_fr_eq_zero (IntFractPair.stream_zero (a : K)) ?_
    simp only [IntFractPair.of, Int.fract_intCast]
  | succ n ih => exact IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)
theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : IntFractPair K, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ := by
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [IntFractPair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero
theorem stream_succ (h : Int.fract v ≠ 0) (n : ℕ) :
    IntFractPair.stream v (n + 1) = IntFractPair.stream (Int.fract v)⁻¹ n := by
  induction n with
  | zero =>
    have H : (IntFractPair.of v).fr = Int.fract v := rfl
    rw [stream_zero, stream_succ_of_some (stream_zero v) (ne_of_eq_of_ne H h), H]
  | succ n ih =>
    rcases eq_or_ne (IntFractPair.stream (Int.fract v)⁻¹ n) none with hnone | hsome
    · rw [hnone] at ih
      rw [succ_nth_stream_eq_none_iff.mpr (Or.inl hnone),
        succ_nth_stream_eq_none_iff.mpr (Or.inl ih)]
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hsome
      rw [hp] at ih
      rcases eq_or_ne p.fr 0 with hz | hnz
      · rw [stream_eq_none_of_fr_eq_zero hp hz, stream_eq_none_of_fr_eq_zero ih hz]
      · rw [stream_succ_of_some hp hnz, stream_succ_of_some ih hnz]
end IntFractPair
section Head
@[simp]
theorem IntFractPair.seq1_fst_eq_of : (IntFractPair.seq1 v).fst = IntFractPair.of v :=
  rfl
theorem of_h_eq_intFractPair_seq1_fst_b : (of v).h = (IntFractPair.seq1 v).fst.b := by
  cases aux_seq_eq : IntFractPair.seq1 v
  simp [of, aux_seq_eq]
@[simp]
theorem of_h_eq_floor : (of v).h = ⌊v⌋ := by
  simp [of_h_eq_intFractPair_seq1_fst_b, IntFractPair.of]
end Head
section sequence
variable {n : ℕ}
theorem IntFractPair.get?_seq1_eq_succ_get?_stream :
    (IntFractPair.seq1 v).snd.get? n = (IntFractPair.stream v) (n + 1) :=
  rfl
section Termination
theorem of_terminatedAt_iff_intFractPair_seq1_terminatedAt :
    (of v).TerminatedAt n ↔ (IntFractPair.seq1 v).snd.TerminatedAt n :=
  Option.map_eq_none
theorem of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none :
    (of v).TerminatedAt n ↔ IntFractPair.stream v (n + 1) = none := by
  rw [of_terminatedAt_iff_intFractPair_seq1_terminatedAt, Stream'.Seq.TerminatedAt,
    IntFractPair.get?_seq1_eq_succ_get?_stream]
end Termination
section Values
theorem IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some {gp_n : Pair K}
    (s_nth_eq : (of v).s.get? n = some gp_n) :
    ∃ ifp : IntFractPair K, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b := by
  obtain ⟨ifp, stream_succ_nth_eq, gp_n_eq⟩ :
    ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ Pair.mk 1 (ifp.b : K) = gp_n := by
    unfold of IntFractPair.seq1 at s_nth_eq
    simpa [Stream'.Seq.get?_tail, Stream'.Seq.map_get?] using s_nth_eq
  cases gp_n_eq
  simp_all only [Option.some.injEq, exists_eq_left']
theorem get?_of_eq_some_of_succ_get?_intFractPair_stream {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (of v).s.get? n = some ⟨1, ifp_succ_n.b⟩ := by
  unfold of IntFractPair.seq1
  simp [Stream'.Seq.map_tail, Stream'.Seq.get?_tail, Stream'.Seq.map_get?, stream_succ_nth_eq]
theorem get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
    (of v).s.get? n = some ⟨1, (IntFractPair.of ifp_n.fr⁻¹).b⟩ :=
  have : IntFractPair.stream v (n + 1) = some (IntFractPair.of ifp_n.fr⁻¹) := by
    cases ifp_n
    simp only [IntFractPair.stream, Nat.add_eq, add_zero, stream_nth_eq, Option.some_bind,
      ite_eq_right_iff]
    intro; contradiction
  get?_of_eq_some_of_succ_get?_intFractPair_stream this
open Int IntFractPair
theorem of_s_head_aux (v : K) : (of v).s.get? 0 = (IntFractPair.stream v 1).bind (some ∘ fun p =>
    { a := 1
      b := p.b }) := by
  rw [of, IntFractPair.seq1]
  simp only [of, Stream'.Seq.map_tail, Stream'.Seq.map, Stream'.Seq.tail, Stream'.Seq.head,
    Stream'.Seq.get?, Stream'.map]
  rw [← Stream'.get_succ, Stream'.get, Option.map.eq_def]
  split <;> simp_all only [Option.some_bind, Option.none_bind, Function.comp_apply]
theorem of_s_head (h : fract v ≠ 0) : (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩ := by
  change (of v).s.get? 0 = _
  rw [of_s_head_aux, stream_succ_of_some (stream_zero v) h, Option.bind]
  rfl
variable (K)
theorem of_s_of_int (a : ℤ) : (of (a : K)).s = Stream'.Seq.nil :=
  haveI h : ∀ n, (of (a : K)).s.get? n = none := by
    intro n
    induction n with
    | zero => rw [of_s_head_aux, stream_succ_of_int, Option.bind]
    | succ n ih => exact (of (a : K)).s.prop ih
  Stream'.Seq.ext fun n => (h n).trans (Stream'.Seq.get?_nil n).symm
variable {K} (v)
theorem of_s_succ (n : ℕ) : (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [fract_intCast, inv_zero, of_s_of_int, ← cast_zero, of_s_of_int,
      Stream'.Seq.get?_nil, Stream'.Seq.get?_nil]
  rcases eq_or_ne ((of (fract v)⁻¹).s.get? n) none with h₁ | h₁
  · rwa [h₁, ← terminatedAt_iff_s_none,
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, stream_succ h, ←
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, terminatedAt_iff_s_none]
  · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp h₁
    obtain ⟨p', hp'₁, _⟩ := exists_succ_get?_stream_of_gcf_of_get?_eq_some hp
    have Hp := get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁
    rw [← stream_succ h] at hp'₁
    rw [Hp, get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁]
theorem of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s :=
  Stream'.Seq.ext fun n => Stream'.Seq.get?_tail (of v).s n ▸ of_s_succ v n
variable (K) (n)
theorem convs'_of_int (a : ℤ) : (of (a : K)).convs' n = a := by
  induction n with
  | zero => simp only [zeroth_conv'_eq_h, of_h_eq_floor, floor_intCast]
  | succ =>
    rw [convs', of_h_eq_floor, floor_intCast, add_right_eq_self]
    exact convs'Aux_succ_none ((of_s_of_int K a).symm ▸ Stream'.Seq.get?_nil 0) _
variable {K}
theorem convs'_succ :
    (of v).convs' (n + 1) = ⌊v⌋ + 1 / (of (fract v)⁻¹).convs' n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [convs'_of_int, fract_intCast, inv_zero, ← cast_zero, convs'_of_int, cast_zero,
      div_zero, add_zero, floor_intCast]
  · rw [convs', of_h_eq_floor, add_right_inj, convs'Aux_succ_some (of_s_head h)]
    exact congr_arg (1 / ·) (by rw [convs', of_h_eq_floor, add_right_inj, of_s_tail])
end Values
end sequence
end GenContFract