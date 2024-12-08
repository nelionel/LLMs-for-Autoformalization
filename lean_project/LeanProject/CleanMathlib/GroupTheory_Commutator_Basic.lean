import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
assert_not_exists Cardinal
assert_not_exists Multiset
variable {G G' F : Type*} [Group G] [Group G'] [FunLike F G G'] [MonoidHomClass F G G']
variable (f : F) {g₁ g₂ g₃ g : G}
theorem commutatorElement_eq_one_iff_mul_comm : ⁅g₁, g₂⁆ = 1 ↔ g₁ * g₂ = g₂ * g₁ := by
  rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
theorem commutatorElement_eq_one_iff_commute : ⁅g₁, g₂⁆ = 1 ↔ Commute g₁ g₂ :=
  commutatorElement_eq_one_iff_mul_comm
theorem Commute.commutator_eq (h : Commute g₁ g₂) : ⁅g₁, g₂⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.mpr h
variable (g₁ g₂ g₃ g)
@[simp]
theorem commutatorElement_one_right : ⁅g, (1 : G)⁆ = 1 :=
  (Commute.one_right g).commutator_eq
@[simp]
theorem commutatorElement_one_left : ⁅(1 : G), g⁆ = 1 :=
  (Commute.one_left g).commutator_eq
@[simp]
theorem commutatorElement_self : ⁅g, g⁆ = 1 :=
  (Commute.refl g).commutator_eq
@[simp]
theorem commutatorElement_inv : ⁅g₁, g₂⁆⁻¹ = ⁅g₂, g₁⁆ := by
  simp_rw [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
theorem map_commutatorElement : (f ⁅g₁, g₂⁆ : G') = ⁅f g₁, f g₂⁆ := by
  simp_rw [commutatorElement_def, map_mul f, map_inv f]
theorem conjugate_commutatorElement : g₃ * ⁅g₁, g₂⁆ * g₃⁻¹ = ⁅g₃ * g₁ * g₃⁻¹, g₃ * g₂ * g₃⁻¹⁆ :=
  map_commutatorElement (MulAut.conj g₃).toMonoidHom g₁ g₂
namespace Subgroup
instance commutator : Bracket (Subgroup G) (Subgroup G) :=
  ⟨fun H₁ H₂ => closure { g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g }⟩
theorem commutator_def (H₁ H₂ : Subgroup G) :
    ⁅H₁, H₂⁆ = closure { g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g } :=
  rfl
variable {g₁ g₂ g₃} {H₁ H₂ H₃ K₁ K₂ : Subgroup G}
theorem commutator_mem_commutator (h₁ : g₁ ∈ H₁) (h₂ : g₂ ∈ H₂) : ⁅g₁, g₂⁆ ∈ ⁅H₁, H₂⁆ :=
  subset_closure ⟨g₁, h₁, g₂, h₂, rfl⟩
theorem commutator_le : ⁅H₁, H₂⁆ ≤ H₃ ↔ ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, ⁅g₁, g₂⁆ ∈ H₃ :=
  H₃.closure_le.trans
    ⟨fun h a b c d => h ⟨a, b, c, d, rfl⟩, fun h _g ⟨a, b, c, d, h_eq⟩ => h_eq ▸ h a b c d⟩
theorem commutator_mono (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) : ⁅H₁, H₂⁆ ≤ ⁅K₁, K₂⁆ :=
  commutator_le.mpr fun _g₁ hg₁ _g₂ hg₂ => commutator_mem_commutator (h₁ hg₁) (h₂ hg₂)
theorem commutator_eq_bot_iff_le_centralizer : ⁅H₁, H₂⁆ = ⊥ ↔ H₁ ≤ centralizer H₂ := by
  rw [eq_bot_iff, commutator_le]
  refine forall_congr' fun p =>
    forall_congr' fun _hp => forall_congr' fun q => forall_congr' fun hq => ?_
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm, eq_comm]
theorem commutator_commutator_eq_bot_of_rotate (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥) :
    ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥ := by
  simp_rw [commutator_eq_bot_iff_le_centralizer, commutator_le,
    mem_centralizer_iff_commutator_eq_one, ← commutatorElement_def] at h1 h2 ⊢
  intro x hx y hy z hz
  trans x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹
  · group
  · rw [h1 _ (H₂.inv_mem hy) _ hz _ (H₁.inv_mem hx), h2 _ (H₃.inv_mem hz) _ (H₁.inv_mem hx) _ hy]
    group
variable (H₁ H₂)
theorem commutator_comm_le : ⁅H₁, H₂⁆ ≤ ⁅H₂, H₁⁆ :=
  commutator_le.mpr fun g₁ h₁ g₂ h₂ =>
    commutatorElement_inv g₂ g₁ ▸ ⁅H₂, H₁⁆.inv_mem_iff.mpr (commutator_mem_commutator h₂ h₁)
theorem commutator_comm : ⁅H₁, H₂⁆ = ⁅H₂, H₁⁆ :=
  le_antisymm (commutator_comm_le H₁ H₂) (commutator_comm_le H₂ H₁)
section Normal
instance commutator_normal [h₁ : H₁.Normal] [h₂ : H₂.Normal] : Normal ⁅H₁, H₂⁆ := by
  let base : Set G := { x | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = x }
  change (closure base).Normal
  suffices h_base : base = Group.conjugatesOfSet base by
    rw [h_base]
    exact Subgroup.normalClosure_normal
  refine Set.Subset.antisymm Group.subset_conjugatesOfSet fun a h => ?_
  simp_rw [Group.mem_conjugatesOfSet_iff, isConj_iff] at h
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩
  exact ⟨_, h₁.conj_mem c hc d, _, h₂.conj_mem e he d, (conjugate_commutatorElement c e d).symm⟩
theorem commutator_def' [H₁.Normal] [H₂.Normal] :
    ⁅H₁, H₂⁆ = normalClosure { g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g } :=
  le_antisymm closure_le_normalClosure (normalClosure_le_normal subset_closure)
theorem commutator_le_right [h : H₂.Normal] : ⁅H₁, H₂⁆ ≤ H₂ :=
  commutator_le.mpr fun g₁ _h₁ g₂ h₂ => H₂.mul_mem (h.conj_mem g₂ h₂ g₁) (H₂.inv_mem h₂)
theorem commutator_le_left [H₁.Normal] : ⁅H₁, H₂⁆ ≤ H₁ :=
  commutator_comm H₂ H₁ ▸ commutator_le_right H₂ H₁
@[simp]
theorem commutator_bot_left : ⁅(⊥ : Subgroup G), H₁⁆ = ⊥ :=
  le_bot_iff.mp (commutator_le_left ⊥ H₁)
@[simp]
theorem commutator_bot_right : ⁅H₁, ⊥⁆ = (⊥ : Subgroup G) :=
  le_bot_iff.mp (commutator_le_right H₁ ⊥)
theorem commutator_le_inf [Normal H₁] [Normal H₂] : ⁅H₁, H₂⁆ ≤ H₁ ⊓ H₂ :=
  le_inf (commutator_le_left H₁ H₂) (commutator_le_right H₁ H₂)
end Normal
theorem map_commutator (f : G →* G') : map f ⁅H₁, H₂⁆ = ⁅map f H₁, map f H₂⁆ := by
  simp_rw [le_antisymm_iff, map_le_iff_le_comap, commutator_le, mem_comap, map_commutatorElement]
  constructor
  · intro p hp q hq
    exact commutator_mem_commutator (mem_map_of_mem _ hp) (mem_map_of_mem _ hq)
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [← map_commutatorElement]
    exact mem_map_of_mem _ (commutator_mem_commutator hp hq)
variable {H₁ H₂}
theorem commutator_le_map_commutator {f : G →* G'} {K₁ K₂ : Subgroup G'} (h₁ : K₁ ≤ H₁.map f)
    (h₂ : K₂ ≤ H₂.map f) : ⁅K₁, K₂⁆ ≤ ⁅H₁, H₂⁆.map f :=
  (commutator_mono h₁ h₂).trans (ge_of_eq (map_commutator H₁ H₂ f))
variable (H₁ H₂)
instance commutator_characteristic [h₁ : Characteristic H₁] [h₂ : Characteristic H₂] :
    Characteristic ⁅H₁, H₂⁆ :=
  characteristic_iff_le_map.mpr fun ϕ =>
    commutator_le_map_commutator (characteristic_iff_le_map.mp h₁ ϕ)
      (characteristic_iff_le_map.mp h₂ ϕ)
theorem commutator_prod_prod (K₁ K₂ : Subgroup G') :
    ⁅H₁.prod K₁, H₂.prod K₂⁆ = ⁅H₁, H₂⁆.prod ⁅K₁, K₂⁆ := by
  apply le_antisymm
  · rw [commutator_le]
    rintro ⟨p₁, p₂⟩ ⟨hp₁, hp₂⟩ ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩
    exact ⟨commutator_mem_commutator hp₁ hq₁, commutator_mem_commutator hp₂ hq₂⟩
  · rw [prod_le_iff]
    constructor <;>
      · rw [map_commutator]
        apply commutator_mono <;>
          simp [le_prod_iff, map_map, MonoidHom.fst_comp_inl, MonoidHom.snd_comp_inl,
            MonoidHom.fst_comp_inr, MonoidHom.snd_comp_inr]
theorem commutator_pi_pi_le {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]
    (H K : ∀ i, Subgroup (Gs i)) :
    ⁅Subgroup.pi Set.univ H, Subgroup.pi Set.univ K⁆ ≤ Subgroup.pi Set.univ fun i => ⁅H i, K i⁆ :=
  commutator_le.mpr fun _p hp _q hq i hi => commutator_mem_commutator (hp i hi) (hq i hi)
end Subgroup
variable (G)
def commutatorSet : Set G :=
  { g | ∃ g₁ g₂ : G, ⁅g₁, g₂⁆ = g }
theorem commutatorSet_def : commutatorSet G = { g | ∃ g₁ g₂ : G, ⁅g₁, g₂⁆ = g } :=
  rfl
theorem one_mem_commutatorSet : (1 : G) ∈ commutatorSet G :=
  ⟨1, 1, commutatorElement_self 1⟩
instance : Nonempty (commutatorSet G) :=
  ⟨⟨1, one_mem_commutatorSet G⟩⟩
variable {G g}
theorem mem_commutatorSet_iff : g ∈ commutatorSet G ↔ ∃ g₁ g₂ : G, ⁅g₁, g₂⁆ = g :=
  Iff.rfl
theorem commutator_mem_commutatorSet : ⁅g₁, g₂⁆ ∈ commutatorSet G :=
  ⟨g₁, g₂, rfl⟩