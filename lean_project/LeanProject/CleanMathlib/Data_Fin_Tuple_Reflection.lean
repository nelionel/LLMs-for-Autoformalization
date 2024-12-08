import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
namespace FinVec
variable {m : ℕ} {α β : Type*}
def seq : ∀ {m}, (Fin m → α → β) → (Fin m → α) → Fin m → β
  | 0, _, _ => ![]
  | _ + 1, f, v => Matrix.vecCons (f 0 (v 0)) (seq (Matrix.vecTail f) (Matrix.vecTail v))
@[simp]
theorem seq_eq : ∀ {m} (f : Fin m → α → β) (v : Fin m → α), seq f v = fun i => f i (v i)
  | 0, _, _ => Subsingleton.elim _ _
  | n + 1, f, v =>
    funext fun i => by
      simp_rw [seq, seq_eq]
      refine i.cases ?_ fun i => ?_
      · rfl
      · rw [Matrix.cons_val_succ]
        rfl
example {f₁ f₂ : α → β} (a₁ a₂ : α) : seq ![f₁, f₂] ![a₁, a₂] = ![f₁ a₁, f₂ a₂] := rfl
def map (f : α → β) {m} : (Fin m → α) → Fin m → β :=
  seq fun _ => f
@[simp]
theorem map_eq (f : α → β) {m} (v : Fin m → α) : map f v = f ∘ v :=
  seq_eq _ _
example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm
def etaExpand {m} (v : Fin m → α) : Fin m → α :=
  map id v
@[simp]
theorem etaExpand_eq {m} (v : Fin m → α) : etaExpand v = v :=
  map_eq id v
example (a : Fin 2 → α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm
def Forall : ∀ {m} (_ : (Fin m → α) → Prop), Prop
  | 0, P => P ![]
  | _ + 1, P => ∀ x : α, Forall fun v => P (Matrix.vecCons x v)
@[simp]
theorem forall_iff : ∀ {m} (P : (Fin m → α) → Prop), Forall P ↔ ∀ x, P x
  | 0, P => by
    simp only [Forall, Fin.forall_fin_zero_pi]
    rfl
  | .succ n, P => by simp only [Forall, forall_iff, Fin.forall_fin_succ_pi, Matrix.vecCons]
example (P : (Fin 2 → α) → Prop) : (∀ f, P f) ↔ ∀ a₀ a₁, P ![a₀, a₁] :=
  (forall_iff _).symm
def Exists : ∀ {m} (_ : (Fin m → α) → Prop), Prop
  | 0, P => P ![]
  | _ + 1, P => ∃ x : α, Exists fun v => P (Matrix.vecCons x v)
theorem exists_iff : ∀ {m} (P : (Fin m → α) → Prop), Exists P ↔ ∃ x, P x
  | 0, P => by
    simp only [Exists, Fin.exists_fin_zero_pi, Matrix.vecEmpty]
    rfl
  | .succ n, P => by simp only [Exists, exists_iff, Fin.exists_fin_succ_pi, Matrix.vecCons]
example (P : (Fin 2 → α) → Prop) : (∃ f, P f) ↔ ∃ a₀ a₁, P ![a₀, a₁] :=
  (exists_iff _).symm
def sum [Add α] [Zero α] : ∀ {m} (_ : Fin m → α), α
  | 0, _ => 0
  | 1, v => v 0
  | _ + 2, v => sum (fun i => v (Fin.castSucc i)) + v (Fin.last _)
@[simp]
theorem sum_eq [AddCommMonoid α] : ∀ {m} (a : Fin m → α), sum a = ∑ i, a i
  | 0, _ => rfl
  | 1, a => (Fintype.sum_unique a).symm
  | n + 2, a => by rw [Fin.sum_univ_castSucc, sum, sum_eq]
example [AddCommMonoid α] (a : Fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm
end FinVec