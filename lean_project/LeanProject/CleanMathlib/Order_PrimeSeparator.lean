import Mathlib.Order.PrimeIdeal
import Mathlib.Order.Zorn
universe u
variable {α : Type*}
open Order Ideal Set
variable [DistribLattice α] [BoundedOrder α]
variable {F : PFilter α} {I : Ideal α}
namespace DistribLattice
lemma mem_ideal_sup_principal (a b : α) (J : Ideal α) : b ∈ J ⊔ principal a ↔ ∃ j ∈ J, b ≤ j ⊔ a :=
  ⟨fun ⟨j, ⟨jJ, _, ha', bja'⟩⟩ => ⟨j, jJ, le_trans bja' (sup_le_sup_left ha' j)⟩,
    fun ⟨j, hj, hbja⟩ => ⟨j, hj, a, le_refl a, hbja⟩⟩
theorem prime_ideal_of_disjoint_filter_ideal (hFI : Disjoint (F : Set α) (I : Set α)) :
    ∃ J : Ideal α, (IsPrime J) ∧ I ≤ J ∧ Disjoint (F : Set α) J := by
  set S : Set (Set α) := { J : Set α | IsIdeal J ∧ I ≤ J ∧ Disjoint (F : Set α) J }
  have IinS : ↑I ∈ S := by
    refine ⟨Order.Ideal.isIdeal I, by trivial⟩
  have chainub : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intros c hcS hcC hcNe
    use sUnion c
    refine ⟨?_, fun s hs ↦ le_sSup hs⟩
    simp only [le_eq_subset, mem_setOf_eq, disjoint_sUnion_right, S]
    let ⟨J, hJ⟩ := hcNe
    refine ⟨Order.isIdeal_sUnion_of_isChain (fun _ hJ ↦ (hcS hJ).1) hcC hcNe,
            ⟨le_trans (hcS hJ).2.1 (le_sSup hJ), fun J hJ ↦ (hcS hJ).2.2⟩⟩
  obtain ⟨Jset, _, hmax⟩ := zorn_subset_nonempty S chainub I IinS
  obtain ⟨Jidl, IJ, JF⟩ := hmax.prop
  set J := IsIdeal.toIdeal Jidl
  use J
  have IJ' : I ≤ J := IJ
  clear chainub IinS
  refine ⟨?_, ⟨IJ, JF⟩⟩
  have Jpr : IsProper J := isProper_of_not_mem (Set.disjoint_left.1 JF F.top_mem)
  rw [isPrime_iff_mem_or_mem]
  intros a₁ a₂
  contrapose!
  intro ⟨ha₁, ha₂⟩
  let J₁ := J ⊔ principal a₁
  let J₂ := J ⊔ principal a₂
  have a₁J₁ : a₁ ∈ J₁ := mem_of_subset_of_mem (le_sup_right : _ ≤ J ⊔ _) mem_principal_self
  have a₂J₂ : a₂ ∈ J₂ := mem_of_subset_of_mem (le_sup_right : _ ≤ J ⊔ _) mem_principal_self
  have J₁J : ↑J₁ ≠ Jset := ne_of_mem_of_not_mem' a₁J₁ ha₁
  have J₂J : ↑J₂ ≠ Jset := ne_of_mem_of_not_mem' a₂J₂ ha₂
  have J₁S : ↑J₁ ∉ S := fun h => J₁J (hmax.eq_of_le h (le_sup_left : J ≤ J₁)).symm
  have J₂S : ↑J₂ ∉ S := fun h => J₂J (hmax.eq_of_le h (le_sup_left : J ≤ J₂)).symm
  have J₁F : ¬ (Disjoint (F : Set α) J₁) := by
    intro hdis
    apply J₁S
    simp only [le_eq_subset, mem_setOf_eq, SetLike.coe_subset_coe, S]
    exact ⟨J₁.isIdeal, le_trans IJ' le_sup_left, hdis⟩
  have J₂F : ¬ (Disjoint (F : Set α) J₂) := by
    intro hdis
    apply J₂S
    simp only [le_eq_subset, mem_setOf_eq, SetLike.coe_subset_coe, S]
    exact ⟨J₂.isIdeal, le_trans IJ' le_sup_left, hdis⟩
  let ⟨c₁, ⟨c₁F, c₁J₁⟩⟩ := Set.not_disjoint_iff.1 J₁F
  let ⟨c₂, ⟨c₂F, c₂J₂⟩⟩ := Set.not_disjoint_iff.1 J₂F
  let ⟨b₁, ⟨b₁J, cba₁⟩⟩ := (mem_ideal_sup_principal a₁ c₁ J).1 c₁J₁
  let ⟨b₂, ⟨b₂J, cba₂⟩⟩ := (mem_ideal_sup_principal a₂ c₂ J).1 c₂J₂
  let b := b₁ ⊔ b₂
  have bJ : b ∈ J := sup_mem b₁J b₂J
  have ineq : c₁ ⊓ c₂ ≤ b ⊔ (a₁ ⊓ a₂) :=
  calc
    c₁ ⊓ c₂ ≤ (b₁ ⊔ a₁) ⊓ (b₂ ⊔ a₂) := inf_le_inf cba₁ cba₂
    _       ≤ (b  ⊔ a₁) ⊓ (b  ⊔ a₂) := by
      apply inf_le_inf <;> apply sup_le_sup_right; exact le_sup_left; exact le_sup_right
    _       = b ⊔ (a₁ ⊓ a₂) := (sup_inf_left b a₁ a₂).symm
  have ba₁a₂F : b ⊔ (a₁ ⊓ a₂) ∈ F := PFilter.mem_of_le ineq (PFilter.inf_mem c₁F c₂F)
  contrapose! JF with ha₁a₂
  rw [Set.not_disjoint_iff]
  use b ⊔ (a₁ ⊓ a₂)
  exact ⟨ba₁a₂F, sup_mem bJ ha₁a₂⟩
end DistribLattice