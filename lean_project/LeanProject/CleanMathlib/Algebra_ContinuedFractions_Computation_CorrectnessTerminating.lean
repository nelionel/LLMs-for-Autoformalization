import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
namespace GenContFract
open GenContFract (of)
variable {K : Type*} [LinearOrderedField K] {v : K} {n : ℕ}
protected def compExactValue (pconts conts : Pair K) (fr : K) : K :=
  if fr = 0 then
    conts.a / conts.b
  else 
    let exactConts := nextConts 1 fr⁻¹ pconts conts
    exactConts.a / exactConts.b
variable [FloorRing K]
protected theorem compExactValue_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
    (fract_a_ne_zero : Int.fract a ≠ 0) :
    ((⌊a⌋ : K) * b + c) / Int.fract a + b = (b * a + c) / Int.fract a := by
  field_simp [fract_a_ne_zero]
  rw [Int.fract]
  ring
open GenContFract
  (compExactValue compExactValue_correctness_of_stream_eq_some_aux_comp)
theorem compExactValue_correctness_of_stream_eq_some :
    ∀ {ifp_n : IntFractPair K}, IntFractPair.stream v n = some ifp_n →
      v = compExactValue ((of v).contsAux n) ((of v).contsAux <| n + 1) ifp_n.fr := by
  let g := of v
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    obtain rfl : IntFractPair.of v = ifp_zero := by
      have : IntFractPair.stream v 0 = some (IntFractPair.of v) := rfl
      simpa only [this, Option.some.injEq] using stream_zero_eq
    cases eq_or_ne (Int.fract v) 0 with
    | inl fract_eq_zero =>
      suffices v = ⌊v⌋ by
        field_simp [nextConts, nextNum, nextDen, compExactValue]
        have : (IntFractPair.of v).fr = Int.fract v := rfl
        rwa [this, if_pos fract_eq_zero]
      calc
        v = Int.fract v + ⌊v⌋ := by rw [Int.fract_add_floor]
        _ = ⌊v⌋ := by simp [fract_eq_zero]
    | inr fract_ne_zero =>
      field_simp [contsAux, nextConts, nextNum, nextDen, of_h_eq_floor, compExactValue]
      have : (IntFractPair.of v).fr = Int.fract v := rfl
      rw [this, if_neg fract_ne_zero, Int.floor_add_fract]
  | succ n IH =>
    intro ifp_succ_n succ_nth_stream_eq
    obtain ⟨ifp_n, nth_stream_eq, nth_fract_ne_zero, -⟩ :
      ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
        ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
      IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
    let conts := g.contsAux (n + 2)
    set pconts := g.contsAux (n + 1) with pconts_eq
    set ppconts := g.contsAux n with ppconts_eq
    cases eq_or_ne ifp_succ_n.fr 0 with
    | inl ifp_succ_n_fr_eq_zero =>
      suffices v = conts.a / conts.b by simpa [compExactValue, ifp_succ_n_fr_eq_zero]
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_inv_eq_floor⟩ :
          ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
        IntFractPair.exists_succ_nth_stream_of_fr_zero succ_nth_stream_eq ifp_succ_n_fr_eq_zero
      have : ifp_n' = ifp_n := by injection Eq.trans nth_stream_eq'.symm nth_stream_eq
      cases this
      have s_nth_eq : g.s.get? n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero
      rw [← ifp_n_fract_inv_eq_floor] at s_nth_eq
      suffices v = compExactValue ppconts pconts ifp_n.fr by
        simpa [conts, contsAux, s_nth_eq, compExactValue, nth_fract_ne_zero] using this
      exact IH nth_stream_eq
    | inr ifp_succ_n_fr_ne_zero =>
      suffices
        compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts ifp_succ_n.fr by
        have : v = compExactValue ppconts pconts ifp_n.fr := IH nth_stream_eq
        conv_lhs => rw [this]
        assumption
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_ne_zero, ⟨refl⟩⟩ :
        ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
        IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
      have : ifp_n' = ifp_n := by injection Eq.trans nth_stream_eq'.symm nth_stream_eq
      cases this
      have s_nth_eq : g.s.get? n = some ⟨1, (⌊ifp_n.fr⁻¹⌋ : K)⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq ifp_n_fract_ne_zero
      let ppA := ppconts.a
      let ppB := ppconts.b
      let pA := pconts.a
      let pB := pconts.b
      have : compExactValue ppconts pconts ifp_n.fr =
          (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) := by
        field_simp [ifp_n_fract_ne_zero, compExactValue, nextConts, nextNum, nextDen, ppA, ppB]
        ac_rfl
      rw [this]
      have tmp_calc :=
        compExactValue_correctness_of_stream_eq_some_aux_comp pA ppA ifp_succ_n_fr_ne_zero
      have tmp_calc' :=
        compExactValue_correctness_of_stream_eq_some_aux_comp pB ppB ifp_succ_n_fr_ne_zero
      let f := Int.fract (1 / ifp_n.fr)
      have f_ne_zero : f ≠ 0 := by simpa [f] using ifp_succ_n_fr_ne_zero
      rw [inv_eq_one_div] at tmp_calc tmp_calc'
      have hA : (↑⌊1 / ifp_n.fr⌋ * pA + ppA) + pA * f = pA * (1 / ifp_n.fr) + ppA := by
        have := congrFun (congrArg HMul.hMul tmp_calc) f
        rwa [right_distrib, div_mul_cancel₀ (h := f_ne_zero),
          div_mul_cancel₀ (h := f_ne_zero)] at this
      have hB : (↑⌊1 / ifp_n.fr⌋ * pB + ppB) + pB * f = pB * (1 / ifp_n.fr) + ppB := by
        have := congrFun (congrArg HMul.hMul tmp_calc') f
        rwa [right_distrib, div_mul_cancel₀ (h := f_ne_zero),
          div_mul_cancel₀ (h := f_ne_zero)] at this
      dsimp only [conts, pconts, ppconts]
      field_simp [compExactValue, contsAux_recurrence s_nth_eq ppconts_eq pconts_eq,
        nextConts, nextNum, nextDen]
      have hfr : (IntFractPair.of (1 / ifp_n.fr)).fr = f := rfl
      rw [one_div, if_neg _, ← one_div, hfr]
      · field_simp [hA, hB]
        ac_rfl
      · rwa [inv_eq_one_div, hfr]
open GenContFract (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none)
theorem of_correctness_of_nth_stream_eq_none (nth_stream_eq_none : IntFractPair.stream v n = none) :
    v = (of v).convs (n - 1) := by
  induction n with
  | zero => contradiction
  | succ n IH =>
    let g := of v
    change v = g.convs n
    obtain ⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩ :
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
      IntFractPair.succ_nth_stream_eq_none_iff.1 nth_stream_eq_none
    · cases n with
      | zero => contradiction
      | succ n' =>
        have : g.TerminatedAt n' :=
          of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2
            nth_stream_eq_none
        have : g.convs (n' + 1) = g.convs n' :=
          convs_stable_of_terminated n'.le_succ this
        rw [this]
        exact IH nth_stream_eq_none
    · simpa [nth_stream_fr_eq_zero, compExactValue] using
        compExactValue_correctness_of_stream_eq_some nth_stream_eq
theorem of_correctness_of_terminatedAt (terminatedAt_n : (of v).TerminatedAt n) :
    v = (of v).convs n :=
  have : IntFractPair.stream v (n + 1) = none :=
    of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminatedAt_n
  of_correctness_of_nth_stream_eq_none this
theorem of_correctness_of_terminates (terminates : (of v).Terminates) :
    ∃ n : ℕ, v = (of v).convs n :=
  Exists.elim terminates fun n terminatedAt_n =>
    Exists.intro n (of_correctness_of_terminatedAt terminatedAt_n)
open Filter
theorem of_correctness_atTop_of_terminates (terminates : (of v).Terminates) :
    ∀ᶠ n in atTop, v = (of v).convs n := by
  rw [eventually_atTop]
  obtain ⟨n, terminatedAt_n⟩ : ∃ n, (of v).TerminatedAt n := terminates
  use n
  intro m m_geq_n
  rw [convs_stable_of_terminated m_geq_n terminatedAt_n]
  exact of_correctness_of_terminatedAt terminatedAt_n
end GenContFract