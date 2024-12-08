import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
variable {K : Type*} {n : ℕ}
namespace GenContFract
variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}
section Squash
section WithDivisionRing
variable [DivisionRing K]
def squashSeq (s : Stream'.Seq <| Pair K) (n : ℕ) : Stream'.Seq (Pair K) :=
  match Prod.mk (s.get? n) (s.get? (n + 1)) with
  | ⟨some gp_n, some gp_succ_n⟩ =>
    Stream'.Seq.nats.zipWith
      (fun n' gp => if n' = n then ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ else gp) s
  | _ => s
theorem squashSeq_eq_self_of_terminated (terminatedAt_succ_n : s.TerminatedAt (n + 1)) :
    squashSeq s n = s := by
  change s.get? (n + 1) = none at terminatedAt_succ_n
  cases s_nth_eq : s.get? n <;> simp only [*, squashSeq]
theorem squashSeq_nth_of_not_terminated {gp_n gp_succ_n : Pair K} (s_nth_eq : s.get? n = some gp_n)
    (s_succ_nth_eq : s.get? (n + 1) = some gp_succ_n) :
    (squashSeq s n).get? n = some ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ := by
  simp [*, squashSeq]
theorem squashSeq_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (squashSeq s n).get? m = s.get? m := by
  cases s_succ_nth_eq : s.get? (n + 1) with
  | none => rw [squashSeq_eq_self_of_terminated s_succ_nth_eq]
  | some =>
    obtain ⟨gp_n, s_nth_eq⟩ : ∃ gp_n, s.get? n = some gp_n :=
      s.ge_stable n.le_succ s_succ_nth_eq
    obtain ⟨gp_m, s_mth_eq⟩ : ∃ gp_m, s.get? m = some gp_m :=
      s.ge_stable (le_of_lt m_lt_n) s_nth_eq
    simp [*, squashSeq, m_lt_n.ne]
theorem squashSeq_succ_n_tail_eq_squashSeq_tail_n :
    (squashSeq s (n + 1)).tail = squashSeq s.tail n := by
  cases s_succ_succ_nth_eq : s.get? (n + 2) with
  | none =>
    cases s_succ_nth_eq : s.get? (n + 1) <;>
      simp only [squashSeq, Stream'.Seq.get?_tail, s_succ_nth_eq, s_succ_succ_nth_eq]
  | some gp_succ_succ_n =>
    obtain ⟨gp_succ_n, s_succ_nth_eq⟩ : ∃ gp_succ_n, s.get? (n + 1) = some gp_succ_n :=
      s.ge_stable (n + 1).le_succ s_succ_succ_nth_eq
    ext1 m
    rcases Decidable.em (m = n) with m_eq_n | m_ne_n
    · simp [*, squashSeq]
    · cases s_succ_mth_eq : s.get? (m + 1)
      · simp only [*, squashSeq, Stream'.Seq.get?_tail, Stream'.Seq.get?_zipWith,
          Option.map₂_none_right]
      · simp [*, squashSeq]
theorem succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq :
    convs'Aux s (n + 2) = convs'Aux (squashSeq s n) (n + 1) := by
  cases s_succ_nth_eq : s.get? <| n + 1 with
  | none =>
    rw [squashSeq_eq_self_of_terminated s_succ_nth_eq,
      convs'Aux_stable_step_of_terminated s_succ_nth_eq]
  | some gp_succ_n =>
    induction n generalizing s gp_succ_n with
    | zero =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable zero_le_one s_succ_nth_eq
      have : (squashSeq s 0).head = some ⟨gp_head.a, gp_head.b + gp_succ_n.a / gp_succ_n.b⟩ :=
        squashSeq_nth_of_not_terminated s_head_eq s_succ_nth_eq
      simp_all [convs'Aux, Stream'.Seq.head, Stream'.Seq.get?_tail]
    | succ m IH =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable (m + 2).zero_le s_succ_nth_eq
      suffices
        gp_head.a / (gp_head.b + convs'Aux s.tail (m + 2)) =
          convs'Aux (squashSeq s (m + 1)) (m + 2)
        by simpa only [convs'Aux, s_head_eq]
      have : (squashSeq s (m + 1)).head = some gp_head :=
        (squashSeq_nth_of_lt m.succ_pos).trans s_head_eq
      simp_all [convs'Aux, squashSeq_succ_n_tail_eq_squashSeq_tail_n]
def squashGCF (g : GenContFract K) : ℕ → GenContFract K
  | 0 =>
    match g.s.get? 0 with
    | none => g
    | some gp => ⟨g.h + gp.a / gp.b, g.s⟩
  | n + 1 => ⟨g.h, squashSeq g.s n⟩
theorem squashGCF_eq_self_of_terminated (terminatedAt_n : TerminatedAt g n) :
    squashGCF g n = g := by
  cases n with
  | zero =>
    change g.s.get? 0 = none at terminatedAt_n
    simp only [convs', squashGCF, convs'Aux, terminatedAt_n]
  | succ =>
    cases g
    simp only [squashGCF, mk.injEq, true_and]
    exact squashSeq_eq_self_of_terminated terminatedAt_n
theorem squashGCF_nth_of_lt {m : ℕ} (m_lt_n : m < n) :
    (squashGCF g (n + 1)).s.get? m = g.s.get? m := by
  simp only [squashGCF, squashSeq_nth_of_lt m_lt_n, Nat.add_eq, add_zero]
theorem succ_nth_conv'_eq_squashGCF_nth_conv' :
    g.convs' (n + 1) = (squashGCF g n).convs' n := by
  cases n with
  | zero =>
    cases g_s_head_eq : g.s.get? 0 <;>
      simp [g_s_head_eq, squashGCF, convs', convs'Aux, Stream'.Seq.head]
  | succ =>
    simp only [succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq, convs',
      squashGCF]
theorem contsAux_eq_contsAux_squashGCF_of_le {m : ℕ} :
    m ≤ n → contsAux g m = (squashGCF g n).contsAux m :=
  Nat.strong_induction_on m
    (by
      clear m
      intro m IH m_le_n
      rcases m with - | m'
      · rfl
      · rcases n with - | n'
        · exact (m'.not_succ_le_zero m_le_n).elim
        · rcases m' with - | m''
          · rfl
          · 
            have m'_lt_n : m'' + 1 < n' + 1 := m_le_n
            have succ_m''th_contsAux_eq := IH (m'' + 1) (lt_add_one (m'' + 1)) m'_lt_n.le
            have : m'' < m'' + 2 := lt_add_of_pos_right m'' zero_lt_two
            have m''th_contsAux_eq := IH m'' this (le_trans this.le m_le_n)
            have : (squashGCF g (n' + 1)).s.get? m'' = g.s.get? m'' :=
              squashGCF_nth_of_lt (Nat.succ_lt_succ_iff.mp m'_lt_n)
            simp [contsAux, succ_m''th_contsAux_eq, m''th_contsAux_eq, this])
end WithDivisionRing
theorem succ_nth_conv_eq_squashGCF_nth_conv [Field K]
    (nth_partDen_ne_zero : ∀ {b : K}, g.partDens.get? n = some b → b ≠ 0) :
    g.convs (n + 1) = (squashGCF g n).convs n := by
  rcases Decidable.em (g.TerminatedAt n) with terminatedAt_n | not_terminatedAt_n
  · have : squashGCF g n = g := squashGCF_eq_self_of_terminated terminatedAt_n
    simp only [this, convs_stable_of_terminated n.le_succ terminatedAt_n]
  · obtain ⟨⟨a, b⟩, s_nth_eq⟩ : ∃ gp_n, g.s.get? n = some gp_n :=
      Option.ne_none_iff_exists'.mp not_terminatedAt_n
    have b_ne_zero : b ≠ 0 := nth_partDen_ne_zero (partDen_eq_s_b s_nth_eq)
    cases n with
    | zero =>
      suffices (b * g.h + a) / b = g.h + a / b by
        simpa [squashGCF, s_nth_eq, conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux s_nth_eq zeroth_contAux_eq_one_zero first_contAux_eq_h_one]
      calc
        (b * g.h + a) / b = b * g.h / b + a / b := by ring
        _ = g.h + a / b := by rw [mul_div_cancel_left₀ _ b_ne_zero]
    | succ n' =>
      obtain ⟨⟨pa, pb⟩, s_n'th_eq⟩ : ∃ gp_n', g.s.get? n' = some gp_n' :=
        g.s.ge_stable n'.le_succ s_nth_eq
      let g' := squashGCF g (n' + 1)
      set pred_conts := g.contsAux (n' + 1) with succ_n'th_contsAux_eq
      set ppred_conts := g.contsAux n' with n'th_contsAux_eq
      let pA := pred_conts.a
      let pB := pred_conts.b
      let ppA := ppred_conts.a
      let ppB := ppred_conts.b
      set pred_conts' := g'.contsAux (n' + 1) with succ_n'th_contsAux_eq'
      set ppred_conts' := g'.contsAux n' with n'th_contsAux_eq'
      let pA' := pred_conts'.a
      let pB' := pred_conts'.b
      let ppA' := ppred_conts'.a
      let ppB' := ppred_conts'.b
      have : g'.convs (n' + 1) =
          ((pb + a / b) * pA' + pa * ppA') / ((pb + a / b) * pB' + pa * ppB') := by
        have : g'.s.get? n' = some ⟨pa, pb + a / b⟩ :=
          squashSeq_nth_of_not_terminated s_n'th_eq s_nth_eq
        rw [conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux this n'th_contsAux_eq'.symm succ_n'th_contsAux_eq'.symm]
      rw [this]
      have : g.convs (n' + 2) =
          (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) := by
        have : g.contsAux (n' + 2) = ⟨pb * pA + pa * ppA, pb * pB + pa * ppB⟩ :=
          contsAux_recurrence s_n'th_eq n'th_contsAux_eq.symm succ_n'th_contsAux_eq.symm
        rw [conv_eq_conts_a_div_conts_b,
          conts_recurrenceAux s_nth_eq succ_n'th_contsAux_eq.symm this]
      rw [this]
      suffices
        ((pb + a / b) * pA + pa * ppA) / ((pb + a / b) * pB + pa * ppB) =
          (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB) by
        obtain ⟨eq1, eq2, eq3, eq4⟩ : pA' = pA ∧ pB' = pB ∧ ppA' = ppA ∧ ppB' = ppB := by
          simp [*, pA', pB', ppA', ppB',
            (contsAux_eq_contsAux_squashGCF_of_le <| le_refl <| n' + 1).symm,
            (contsAux_eq_contsAux_squashGCF_of_le n'.le_succ).symm]
        symm
        simpa only [eq1, eq2, eq3, eq4, mul_div_cancel_right₀ _ b_ne_zero]
      field_simp
      congr 1 <;> ring
end Squash
theorem convs_eq_convs' [LinearOrderedField K]
    (s_pos : ∀ {gp : Pair K} {m : ℕ}, m < n → g.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b) :
    g.convs n = g.convs' n := by
  induction n generalizing g with
  | zero => simp
  | succ n IH =>
    let g' := squashGCF g n
    suffices g.convs (n + 1) = g'.convs' n by
      rwa [succ_nth_conv'_eq_squashGCF_nth_conv']
    rcases Decidable.em (TerminatedAt g n) with terminatedAt_n | not_terminatedAt_n
    · have g'_eq_g : g' = g := squashGCF_eq_self_of_terminated terminatedAt_n
      rw [convs_stable_of_terminated n.le_succ terminatedAt_n, g'_eq_g, IH _]
      intro _ _ m_lt_n s_mth_eq
      exact s_pos (Nat.lt.step m_lt_n) s_mth_eq
    · suffices g.convs (n + 1) = g'.convs n by
        rwa [← IH]
        intro gp' m m_lt_n s_mth_eq'
        rcases m_lt_n with n | succ_m_lt_n
        · 
          obtain ⟨gp_succ_m, s_succ_mth_eq⟩ : ∃ gp_succ_m, g.s.get? (m + 1) = some gp_succ_m :=
            Option.ne_none_iff_exists'.mp not_terminatedAt_n
          obtain ⟨gp_m, mth_s_eq⟩ : ∃ gp_m, g.s.get? m = some gp_m :=
            g.s.ge_stable m.le_succ s_succ_mth_eq
          suffices 0 < gp_m.a ∧ 0 < gp_m.b + gp_succ_m.a / gp_succ_m.b by
            have ot : g'.s.get? m = some ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩ :=
              squashSeq_nth_of_not_terminated mth_s_eq s_succ_mth_eq
            have : gp' = ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩ := by
              simp_all only [Option.some.injEq]
            rwa [this]
          have m_lt_n : m < m.succ := Nat.lt_succ_self m
          refine ⟨(s_pos (Nat.lt.step m_lt_n) mth_s_eq).left, ?_⟩
          refine add_pos (s_pos (Nat.lt.step m_lt_n) mth_s_eq).right ?_
          have : 0 < gp_succ_m.a ∧ 0 < gp_succ_m.b := s_pos (lt_add_one <| m + 1) s_succ_mth_eq
          exact div_pos this.left this.right
        · 
          refine s_pos (Nat.lt.step <| Nat.lt.step succ_m_lt_n) ?_
          exact Eq.trans (squashGCF_nth_of_lt succ_m_lt_n).symm s_mth_eq'
      have : ∀ ⦃b⦄, g.partDens.get? n = some b → b ≠ 0 := by
        intro b nth_partDen_eq
        obtain ⟨gp, s_nth_eq, ⟨refl⟩⟩ : ∃ gp, g.s.get? n = some gp ∧ gp.b = b :=
          exists_s_b_of_partDen nth_partDen_eq
        exact (ne_of_lt (s_pos (lt_add_one n) s_nth_eq).right).symm
      exact succ_nth_conv_eq_squashGCF_nth_conv @this
end GenContFract
open GenContFract
namespace ContFract
nonrec theorem convs_eq_convs' [LinearOrderedField K] {c : ContFract K} :
    (↑c : GenContFract K).convs = (↑c : GenContFract K).convs' := by
  ext n
  apply convs_eq_convs'
  intro gp m _ s_nth_eq
  exact ⟨zero_lt_one.trans_le ((c : SimpContFract K).property m gp.a
    (partNum_eq_s_a s_nth_eq)).symm.le, c.property m gp.b <| partDen_eq_s_b s_nth_eq⟩
end ContFract