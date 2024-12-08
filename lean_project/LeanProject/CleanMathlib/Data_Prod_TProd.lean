import Mathlib.Data.List.Nodup
open List Function
universe u v
variable {ι : Type u} {α : ι → Type v} {i j : ι} {l : List ι}
namespace List
variable (α)
abbrev TProd (l : List ι) : Type v :=
  l.foldr (fun i β => α i × β) PUnit
variable {α}
namespace TProd
open List
protected def mk : ∀ (l : List ι) (_f : ∀ i, α i), TProd α l
  | [] => fun _ => PUnit.unit
  | i :: is => fun f => (f i, TProd.mk is f)
instance [∀ i, Inhabited (α i)] : Inhabited (TProd α l) :=
  ⟨TProd.mk l default⟩
@[simp]
theorem fst_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (TProd.mk (i :: l) f).1 = f i :=
  rfl
@[simp]
theorem snd_mk (i : ι) (l : List ι) (f : ∀ i, α i) :
    (TProd.mk.{u,v} (i :: l) f).2 = TProd.mk.{u,v} l f :=
  rfl
variable [DecidableEq ι]
protected def elim : ∀ {l : List ι} (_ : TProd α l) {i : ι} (_ : i ∈ l), α i
  | i :: is, v, j, hj =>
    if hji : j = i then by
      subst hji
      exact v.1
    else TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji)
@[simp]
theorem elim_self (v : TProd α (i :: l)) : v.elim (l.mem_cons_self i) = v.1 := by simp [TProd.elim]
@[simp]
theorem elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : TProd α (i :: l)) :
    v.elim hj = TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji) := by simp [TProd.elim, hji]
@[simp]
theorem elim_of_mem (hl : (i :: l).Nodup) (hj : j ∈ l) (v : TProd α (i :: l)) :
    v.elim (mem_cons_of_mem _ hj) = TProd.elim v.2 hj := by
  apply elim_of_ne
  rintro rfl
  exact hl.not_mem hj
theorem elim_mk : ∀ (l : List ι) (f : ∀ i, α i) {i : ι} (hi : i ∈ l), (TProd.mk l f).elim hi = f i
  | i :: is, f, j, hj => by
    by_cases hji : j = i
    · subst hji
      simp
    · rw [TProd.elim_of_ne _ hji, snd_mk, elim_mk is]
@[ext]
theorem ext :
    ∀ {l : List ι} (_ : l.Nodup) {v w : TProd α l}
      (_ : ∀ (i) (hi : i ∈ l), v.elim hi = w.elim hi), v = w
  | [], _, v, w, _ => PUnit.ext v w
  | i :: is, hl, v, w, hvw => by
    apply Prod.ext
    · rw [← elim_self v, hvw, elim_self]
    refine ext (nodup_cons.mp hl).2 fun j hj => ?_
    rw [← elim_of_mem hl, hvw, elim_of_mem hl]
@[simp]
protected def elim' (h : ∀ i, i ∈ l) (v : TProd α l) (i : ι) : α i :=
  v.elim (h i)
theorem mk_elim (hnd : l.Nodup) (h : ∀ i, i ∈ l) (v : TProd α l) : TProd.mk l (v.elim' h) = v :=
  TProd.ext hnd fun i hi => by simp [elim_mk]
def piEquivTProd (hnd : l.Nodup) (h : ∀ i, i ∈ l) : (∀ i, α i) ≃ TProd α l :=
  ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩
end TProd
end List
namespace Set
open List
@[simp]
protected def tprod : ∀ (l : List ι) (_t : ∀ i, Set (α i)), Set (TProd α l)
  | [], _ => univ
  | i :: is, t => t i ×ˢ Set.tprod is t
theorem mk_preimage_tprod :
    ∀ (l : List ι) (t : ∀ i, Set (α i)), TProd.mk l ⁻¹' Set.tprod l t = { i | i ∈ l }.pi t
  | [], t => by simp [Set.tprod]
  | i :: l, t => by
    ext f
    have h : TProd.mk l f ∈ Set.tprod l t ↔ ∀ i : ι, i ∈ l → f i ∈ t i := by
      change f ∈ TProd.mk l ⁻¹' Set.tprod l t ↔ f ∈ { x | x ∈ l }.pi t
      rw [mk_preimage_tprod l t]
    rw [Set.tprod, TProd.mk, mem_preimage, mem_pi, prod_mk_mem_set_prod_eq]
    simp_rw [mem_setOf_eq, mem_cons]
    rw [forall_eq_or_imp, and_congr_right_iff]
    exact fun _ => h
theorem elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : ∀ i, i ∈ l)
    (t : ∀ i, Set (α i)) : TProd.elim' h ⁻¹' pi univ t = Set.tprod l t := by
  have h2 : { i | i ∈ l } = univ := by
    ext i
    simp [h]
  rw [← h2, ← mk_preimage_tprod, preimage_preimage]
  simp only [TProd.mk_elim hnd h]
  dsimp
end Set