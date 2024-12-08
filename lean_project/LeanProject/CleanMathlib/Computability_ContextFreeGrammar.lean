import Mathlib.Computability.Language
open Function
universe uT uN in
@[ext]
structure ContextFreeRule (T : Type uT) (N : Type uN) where
  input : N
  output : List (Symbol T N)
structure ContextFreeGrammar.{uN,uT} (T : Type uT) where
  NT : Type uN
  initial : NT
  rules : Finset (ContextFreeRule T NT)
universe uT uN
variable {T : Type uT}
namespace ContextFreeRule
variable {N : Type uN} {r : ContextFreeRule T N} {u v : List (Symbol T N)}
inductive Rewrites (r : ContextFreeRule T N) : List (Symbol T N) → List (Symbol T N) → Prop
  | head (s : List (Symbol T N)) :
      r.Rewrites (Symbol.nonterminal r.input :: s) (r.output ++ s)
  | cons (x : Symbol T N) {s₁ s₂ : List (Symbol T N)} (hrs : Rewrites r s₁ s₂) :
      r.Rewrites (x :: s₁) (x :: s₂)
lemma Rewrites.exists_parts (hr : r.Rewrites u v) :
    ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
  induction hr with
  | head s =>
    use [], s
    simp
  | cons x _ ih =>
    rcases ih with ⟨p', q', rfl, rfl⟩
    use x :: p', q'
    simp
lemma Rewrites.input_output : r.Rewrites [.nonterminal r.input] r.output := by
  simpa using head []
lemma rewrites_of_exists_parts (r : ContextFreeRule T N) (p q : List (Symbol T N)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
  induction p with
  | nil         => exact Rewrites.head q
  | cons d l ih => exact Rewrites.cons d ih
theorem rewrites_iff :
    r.Rewrites u v ↔ ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q :=
  ⟨Rewrites.exists_parts, by rintro ⟨p, q, rfl, rfl⟩; apply rewrites_of_exists_parts⟩
lemma Rewrites.append_left (hvw : r.Rewrites u v) (p : List (Symbol T N)) :
    r.Rewrites (p ++ u) (p ++ v) := by
  rw [rewrites_iff] at *
  rcases hvw with ⟨x, y, hxy⟩
  use p ++ x, y
  simp_all
lemma Rewrites.append_right (hvw : r.Rewrites u v) (p : List (Symbol T N)) :
    r.Rewrites (u ++ p) (v ++ p) := by
  rw [rewrites_iff] at *
  rcases hvw with ⟨x, y, hxy⟩
  use x, y ++ p
  simp_all
end ContextFreeRule
namespace ContextFreeGrammar
def Produces (g : ContextFreeGrammar.{uN} T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.Rewrites u v
abbrev Derives (g : ContextFreeGrammar.{uN} T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces
def Generates (g : ContextFreeGrammar.{uN} T) (s : List (Symbol T g.NT)) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] s
def language (g : ContextFreeGrammar.{uN} T) : Language T :=
  { w | g.Generates (List.map Symbol.terminal w) }
@[simp]
lemma mem_language_iff (g : ContextFreeGrammar.{uN} T) (w : List T) :
    w ∈ g.language ↔ g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w) := by
  rfl
variable {g : ContextFreeGrammar.{uN} T}
@[refl]
lemma Derives.refl (w : List (Symbol T g.NT)) : g.Derives w w :=
  Relation.ReflTransGen.refl
lemma Produces.single {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) : g.Derives v w :=
  Relation.ReflTransGen.single hvw
@[trans]
lemma Derives.trans {u v w : List (Symbol T g.NT)} (huv : g.Derives u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  Relation.ReflTransGen.trans huv hvw
lemma Derives.trans_produces {u v w : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hvw : g.Produces v w) :
    g.Derives u w :=
  huv.trans hvw.single
lemma Produces.trans_derives {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  huv.single.trans hvw
lemma Derives.eq_or_head {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.Derives v w :=
  Relation.ReflTransGen.cases_head huw
lemma Derives.eq_or_tail {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Derives u v ∧ g.Produces v w :=
  (Relation.ReflTransGen.cases_tail huw).casesOn (Or.inl ∘ Eq.symm) Or.inr
lemma Produces.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (p ++ v) (p ++ w) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_left p⟩
lemma Produces.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (v ++ p) (w ++ p) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_right p⟩
lemma Derives.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (p ++ v) (p ++ w) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_left p
lemma Derives.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (v ++ p) (w ++ p) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_right p
end ContextFreeGrammar
def Language.IsContextFree (L : Language T) : Prop :=
  ∃ g : ContextFreeGrammar.{0} T, g.language = L
proof_wanted Language.isContextFree_iff {L : Language T} :
    L.IsContextFree ↔ ∃ g : ContextFreeGrammar.{uN} T, g.language = L
section closure_reversal
namespace ContextFreeRule
variable {N : Type uN} {r : ContextFreeRule T N} {u v : List (Symbol T N)}
def reverse (r : ContextFreeRule T N) : ContextFreeRule T N := ⟨r.input, r.output.reverse⟩
@[simp] lemma reverse_reverse (r : ContextFreeRule T N) : r.reverse.reverse = r := by simp [reverse]
@[simp] lemma reverse_comp_reverse :
    reverse ∘ reverse = (id : ContextFreeRule T N → ContextFreeRule T N) := by ext : 1; simp
lemma reverse_involutive : Involutive (reverse : ContextFreeRule T N → ContextFreeRule T N) :=
  reverse_reverse
lemma reverse_bijective : Bijective (reverse : ContextFreeRule T N → ContextFreeRule T N) :=
  reverse_involutive.bijective
lemma reverse_injective : Injective (reverse : ContextFreeRule T N → ContextFreeRule T N) :=
  reverse_involutive.injective
lemma reverse_surjective : Surjective (reverse : ContextFreeRule T N → ContextFreeRule T N) :=
  reverse_involutive.surjective
protected lemma Rewrites.reverse : ∀ {u v}, r.Rewrites u v → r.reverse.Rewrites u.reverse v.reverse
  | _, _, head s => by simpa using .append_left .input_output _
  | _, _, @cons _ _ _ x u v h => by simpa using h.reverse.append_right _
lemma rewrites_reverse : r.reverse.Rewrites u.reverse v.reverse ↔ r.Rewrites u v :=
  ⟨fun h ↦ by simpa using h.reverse, .reverse⟩
@[simp] lemma rewrites_reverse_comm : r.reverse.Rewrites u v ↔ r.Rewrites u.reverse v.reverse := by
  rw [← rewrites_reverse, reverse_reverse]
end ContextFreeRule
namespace ContextFreeGrammar
variable {g : ContextFreeGrammar T} {u v : List (Symbol T g.NT)} {w : List T}
@[simps] def reverse (g : ContextFreeGrammar T) : ContextFreeGrammar T :=
  ⟨g.NT, g.initial, g.rules.map (⟨ContextFreeRule.reverse, ContextFreeRule.reverse_injective⟩)⟩
@[simp] lemma reverse_reverse (g : ContextFreeGrammar T) : g.reverse.reverse = g := by
  simp [reverse, Finset.map_map]
lemma reverse_involutive : Involutive (reverse : ContextFreeGrammar T → ContextFreeGrammar T) :=
  reverse_reverse
lemma reverse_bijective : Bijective (reverse : ContextFreeGrammar T → ContextFreeGrammar T) :=
  reverse_involutive.bijective
lemma reverse_injective : Injective (reverse : ContextFreeGrammar T → ContextFreeGrammar T) :=
  reverse_involutive.injective
lemma reverse_surjective : Surjective (reverse : ContextFreeGrammar T → ContextFreeGrammar T) :=
  reverse_involutive.surjective
lemma produces_reverse : g.reverse.Produces u.reverse v.reverse ↔ g.Produces u v :=
  (Equiv.ofBijective _ ContextFreeRule.reverse_bijective).exists_congr
    (by simp [ContextFreeRule.reverse_involutive.eq_iff])
alias ⟨_, Produces.reverse⟩ := produces_reverse
@[simp] lemma produces_reverse_comm : g.reverse.Produces u v ↔ g.Produces u.reverse v.reverse :=
  (Equiv.ofBijective _ ContextFreeRule.reverse_bijective).exists_congr
    (by simp [ContextFreeRule.reverse_involutive.eq_iff])
protected lemma Derives.reverse (hg : g.Derives u v) : g.reverse.Derives u.reverse v.reverse := by
  induction hg with
  | refl => rfl
  | tail _ orig ih => exact ih.trans_produces orig.reverse
lemma derives_reverse : g.reverse.Derives u.reverse v.reverse ↔ g.Derives u v :=
  ⟨fun h ↦ by convert h.reverse <;> simp, .reverse⟩
@[simp] lemma derives_reverse_comm : g.reverse.Derives u v ↔ g.Derives u.reverse v.reverse := by
  rw [iff_comm, ← derives_reverse, List.reverse_reverse, List.reverse_reverse]
lemma generates_reverse : g.reverse.Generates u.reverse ↔ g.Generates u := by simp [Generates]
alias ⟨_, Generates.reverse⟩ := generates_reverse
@[simp] lemma generates_reverse_comm : g.reverse.Generates u ↔ g.Generates u.reverse := by
  simp [Generates]
@[simp] lemma language_reverse : g.reverse.language = g.language.reverse := by ext; simp
end ContextFreeGrammar
theorem Language.IsContextFree.reverse (L : Language T) :
    L.IsContextFree → L.reverse.IsContextFree := by rintro ⟨g, rfl⟩; exact ⟨g.reverse, by simp⟩
end closure_reversal