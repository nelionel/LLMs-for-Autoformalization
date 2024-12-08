import Mathlib.Algebra.Polynomial.Degree.Lemmas
open Polynomial
namespace Mathlib.Tactic.ComputeDegree
section recursion_lemmas
variable {R : Type*}
section semiring
variable [Semiring R]
theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
theorem natDegree_natCast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_natCast _).le
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le
@[deprecated (since := "2024-04-17")]
alias natDegree_nat_cast_le := natDegree_natCast_le
theorem coeff_add_of_eq {n : ℕ} {a b : R} {f g : R[X]}
    (h_add_left : f.coeff n = a) (h_add_right : g.coeff n = b) :
    (f + g).coeff n = a + b := by subst ‹_› ‹_›; apply coeff_add
theorem coeff_mul_add_of_le_natDegree_of_eq_ite {d df dg : ℕ} {a b : R} {f g : R[X]}
    (h_mul_left : natDegree f ≤ df) (h_mul_right : natDegree g ≤ dg)
    (h_mul_left : f.coeff df = a) (h_mul_right : g.coeff dg = b) (ddf : df + dg ≤ d) :
    (f * g).coeff d = if d = df + dg then a * b else 0 := by
  split_ifs with h
  · subst h_mul_left h_mul_right h
    exact coeff_mul_of_natDegree_le ‹_› ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le ‹_› ‹_›
    · exact ne_comm.mp h
theorem coeff_pow_of_natDegree_le_of_eq_ite' {m n o : ℕ} {a : R} {p : R[X]}
    (h_pow : natDegree p ≤ n) (h_exp : m * n ≤ o) (h_pow_bas : coeff p n = a) :
    coeff (p ^ m) o = if o = m * n then a ^ m else 0 := by
  split_ifs with h
  · subst h h_pow_bas
    exact coeff_pow_of_natDegree_le ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ‹_› ?_)
    · exact natDegree_pow_le_of_le m ‹_›
    · exact Iff.mp ne_comm h
theorem natDegree_smul_le_of_le {n : ℕ} {a : R} {f : R[X]} (hf : natDegree f ≤ n) :
    natDegree (a • f) ≤ n :=
  (natDegree_smul_le a f).trans hf
theorem degree_smul_le_of_le {n : ℕ} {a : R} {f : R[X]} (hf : degree f ≤ n) :
    degree (a • f) ≤ n :=
  (degree_smul_le a f).trans hf
theorem coeff_smul {n : ℕ} {a : R} {f : R[X]} : (a • f).coeff n = a * f.coeff n := rfl
section congr_lemmas
theorem natDegree_eq_of_le_of_coeff_ne_zero' {deg m o : ℕ} {c : R} {p : R[X]}
    (h_natDeg_le : natDegree p ≤ m) (coeff_eq : coeff p o = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    natDegree p = deg := by
  subst coeff_eq deg_eq_deg coeff_eq_deg
  exact natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›
theorem degree_eq_of_le_of_coeff_ne_zero' {deg m o : WithBot ℕ} {c : R} {p : R[X]}
    (h_deg_le : degree p ≤ m) (coeff_eq : coeff p (WithBot.unbot' 0 deg) = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    degree p = deg := by
  subst coeff_eq coeff_eq_deg deg_eq_deg
  rcases eq_or_ne m ⊥ with rfl|hh
  · exact bot_unique h_deg_le
  · obtain ⟨m, rfl⟩ := WithBot.ne_bot_iff_exists.mp hh
    exact degree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›
variable {m n : ℕ} {f : R[X]} {r : R}
theorem coeff_congr_lhs (h : coeff f m = r) (natDeg_eq_coeff : m = n) : coeff f n = r :=
  natDeg_eq_coeff ▸ h
theorem coeff_congr (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r = s) :
    coeff f n = s :=
  natDeg_eq_coeff ▸ rs ▸ h
end congr_lemmas
end semiring
section ring
variable [Ring R]
theorem natDegree_intCast_le (n : ℤ) : natDegree (n : R[X]) ≤ 0 := (natDegree_intCast _).le
@[deprecated (since := "2024-04-17")]
alias natDegree_int_cast_le := natDegree_intCast_le
theorem coeff_sub_of_eq {n : ℕ} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg : g.coeff n = b) :
    (f - g).coeff n = a - b := by subst hf hg; apply coeff_sub
theorem coeff_intCast_ite {n : ℕ} {a : ℤ} : (Int.cast a : R[X]).coeff n = ite (n = 0) a 0 := by
  simp only [← C_eq_intCast, coeff_C, Int.cast_ite, Int.cast_zero]
@[deprecated (since := "2024-04-17")]
alias coeff_int_cast_ite := coeff_intCast_ite
end ring
end recursion_lemmas
section Tactic
open Lean Elab Tactic Meta Expr
def twoHeadsArgs (e : Expr) : Name × Name × (Name ⊕ Name) × List Bool := Id.run do
  let (eq_or_le, lhs, rhs) ← match e.getAppFnArgs with
    | (na@``Eq, #[_, lhs, rhs])       => pure (na, lhs, rhs)
    | (na@``LE.le, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | _ => return (.anonymous, .anonymous, .inl .anonymous, [])
  let (ndeg_or_deg_or_coeff, pol, and?) ← match lhs.getAppFnArgs with
    | (na@``Polynomial.natDegree, #[_, _, pol])     => (na, pol, [rhs.isMVar])
    | (na@``Polynomial.degree,    #[_, _, pol])     => (na, pol, [rhs.isMVar])
    | (na@``Polynomial.coeff,     #[_, _, pol, c])  => (na, pol, [rhs.isMVar, c.isMVar])
    | _ => return (.anonymous, eq_or_le, .inl .anonymous, [])
  let head := match pol.numeral? with
    | some 0 => .inl `zero
    | some 1 => .inl `one
    | some _ => .inl `many
    | none => match pol.getAppFnArgs with
      | (``DFunLike.coe, #[_, _, _, _, polFun, _]) =>
        let na := polFun.getAppFn.constName
        if na ∈ [``Polynomial.monomial, ``Polynomial.C] then
          .inr na
        else
          .inl .anonymous
      | (na, _) => .inr na
  (ndeg_or_deg_or_coeff, eq_or_le, head, and?)
def getCongrLemma (twoH : Name × Name × List Bool) (debug : Bool := false) : Name :=
  let nam := match twoH with
    | (_,           ``LE.le, [rhs]) => if rhs then ``id else ``le_trans
    | (``natDegree, ``Eq, [rhs])    => if rhs then ``id else ``natDegree_eq_of_le_of_coeff_ne_zero'
    | (``degree,    ``Eq, [rhs])    => if rhs then ``id else ``degree_eq_of_le_of_coeff_ne_zero'
    | (``coeff,     ``Eq, [rhs, c]) =>
      match rhs, c with
      | false, false => ``coeff_congr
      | false, true  => ``Eq.trans
      | true, false  => ``coeff_congr_lhs
      | true, true   => ``id
    | _ => ``id
  if debug then
    let last := nam.lastComponentAsString
    let natr := if last == "trans" then nam.toString else last
    dbg_trace f!"congr lemma: '{natr}'"
    nam
  else
    nam
def dispatchLemma
    (twoH : Name × Name × (Name ⊕ Name) × List Bool) (debug : Bool := false) : Name :=
  match twoH with
    | (.anonymous, _, _) => ``id 
    | (_, .anonymous, _) => ``id 
    | (na1, na2, head, bools) =>
      let msg := f!"\ndispatchLemma:\n  {head}"
      if false ∈ bools then getCongrLemma (na1, na2, bools) debug
      else
      let π (natDegLE : Name) (degLE : Name) (coeff : Name) : Name := Id.run do
        let lem := match na1, na2 with
          | ``natDegree, ``LE.le => natDegLE
          | ``degree, ``LE.le => degLE
          | ``coeff, ``Eq => coeff
          | _, ``LE.le => ``le_rfl
          | _, _ => ``rfl
        if debug then
          dbg_trace f!"{lem.lastComponentAsString}\n{msg}"
        lem
      match head with
        | .inl `zero => π ``natDegree_zero_le ``degree_zero_le ``coeff_zero
        | .inl `one  => π ``natDegree_one_le ``degree_one_le ``coeff_one
        | .inl `many => π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inl .anonymous => π ``le_rfl ``le_rfl ``rfl
        | .inr ``HAdd.hAdd =>
          π ``natDegree_add_le_of_le ``degree_add_le_of_le ``coeff_add_of_eq
        | .inr ``HSub.hSub =>
          π ``natDegree_sub_le_of_le ``degree_sub_le_of_le ``coeff_sub_of_eq
        | .inr ``HMul.hMul =>
          π ``natDegree_mul_le_of_le ``degree_mul_le_of_le ``coeff_mul_add_of_le_natDegree_of_eq_ite
        | .inr ``HPow.hPow =>
          π ``natDegree_pow_le_of_le ``degree_pow_le_of_le ``coeff_pow_of_natDegree_le_of_eq_ite'
        | .inr ``Neg.neg =>
          π ``natDegree_neg_le_of_le ``degree_neg_le_of_le ``coeff_neg
        | .inr ``Polynomial.X =>
          π ``natDegree_X_le ``degree_X_le ``coeff_X
        | .inr ``Nat.cast =>
          π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inr ``NatCast.natCast =>
          π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inr ``Int.cast =>
          π ``natDegree_intCast_le ``degree_intCast_le ``coeff_intCast_ite
        | .inr ``IntCast.intCast =>
          π ``natDegree_intCast_le ``degree_intCast_le ``coeff_intCast_ite
        | .inr ``Polynomial.monomial =>
          π ``natDegree_monomial_le ``degree_monomial_le ``coeff_monomial
        | .inr ``Polynomial.C =>
          π ``natDegree_C_le ``degree_C_le ``coeff_C
        | .inr ``HSMul.hSMul =>
          π ``natDegree_smul_le_of_le ``degree_smul_le_of_le ``coeff_smul
        | _ => π ``le_rfl ``le_rfl ``rfl
def try_rfl (mvs : List MVarId) : MetaM (List MVarId) := do
  let (yesMV, noMV) := ← mvs.partitionM fun mv =>
                          return hasExprMVar (← instantiateMVars (← mv.getDecl).type)
  let tried_rfl := ← noMV.mapM fun g => g.applyConst ``rfl <|> return [g]
  let assignable := ← yesMV.mapM fun g => do
    let tgt := ← instantiateMVars (← g.getDecl).type
    match tgt.eq? with
      | some (_, lhs, rhs) =>
        if (isMVar rhs && (! hasExprMVar lhs)) ||
           (isMVar lhs && (! hasExprMVar rhs)) then
           g.applyConst ``rfl
        else pure [g]
      | none =>
        return [g]
  return (assignable.flatten ++ tried_rfl.flatten)
def splitApply (mvs static : List MVarId) : MetaM ((List MVarId) × (List MVarId)) := do
  let (can_progress, curr_static) := ← mvs.partitionM fun mv => do
    return dispatchLemma (twoHeadsArgs (← mv.getType'')) != ``id
  let progress := ← can_progress.mapM fun mv => do
    let lem := dispatchLemma <| twoHeadsArgs (← mv.getType'')
    mv.applyConst <| lem
  return (progress.flatten, static ++ curr_static)
def miscomputedDegree? (deg : Expr) : List Expr → List MessageData
  | tgt::tgts =>
    let rest := miscomputedDegree? deg tgts
    if tgt.ne?.isSome then
      m!"* the coefficient of degree {deg} may be zero" :: rest
    else if let some ((Expr.const ``Nat []), lhs, _) := tgt.le? then
      m!"* there is at least one term of naïve degree {lhs}" :: rest
    else if let some (_, lhs, _) := tgt.eq? then
      m!"* there may be a term of naïve degree {lhs}" :: rest
    else rest
  | [] => []
syntax (name := computeDegree) "compute_degree" "!"? : tactic
initialize registerTraceClass `Tactic.compute_degree
@[inherit_doc computeDegree]
macro "compute_degree!" : tactic => `(tactic| compute_degree !)
elab_rules : tactic | `(tactic| compute_degree $[!%$bang]?) => focus <| withMainContext do
  let goal ← getMainGoal
  let gt ← goal.getType''
  let deg? := match gt.eq? with
    | some (_, _, rhs) => some rhs
    | _ => none
  let twoH := twoHeadsArgs gt
  match twoH with
    | (_, .anonymous, _) => throwError m!"'compute_degree' inapplicable. \
        The goal{indentD gt}\nis expected to be '≤' or '='."
    | (.anonymous, _, _) => throwError m!"'compute_degree' inapplicable. \
        The LHS must be an application of 'natDegree', 'degree', or 'coeff'."
    | _ =>
      let lem := dispatchLemma twoH
      trace[Tactic.compute_degree]
        f!"'compute_degree' first applies lemma '{lem.lastComponentAsString}'"
      let mut (gls, static) := (← goal.applyConst lem, [])
      while gls != [] do (gls, static) ← splitApply gls static
      let rfled ← try_rfl static
      setGoals rfled
      evalTactic
        (← `(tactic| try any_goals conv_lhs =>
                       (simp +decide only [Nat.cast_withBot]; norm_num)))
      if bang.isSome then
        let mut false_goals : Array MVarId := #[]
        let mut new_goals : Array MVarId := #[]
        for g in ← getGoals do
          let gs' ← run g do evalTactic (←
            `(tactic| try (any_goals norm_num <;> norm_cast <;> try assumption)))
          new_goals := new_goals ++ gs'.toArray
          if ← gs'.anyM fun g' => g'.withContext do return (← g'.getType'').isConstOf ``False then
            false_goals := false_goals.push g
        setGoals new_goals.toList
        if let some deg := deg? then
          let errors := miscomputedDegree? deg (← false_goals.mapM (MVarId.getType'' ·)).toList
          unless errors.isEmpty do
            throwError Lean.MessageData.joinSep
              (m!"The given degree is '{deg}'.  However,\n" :: errors) "\n"
macro (name := monicityMacro) "monicity" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree))
@[inherit_doc monicityMacro]
macro "monicity!" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree!))
end Tactic
end Mathlib.Tactic.ComputeDegree