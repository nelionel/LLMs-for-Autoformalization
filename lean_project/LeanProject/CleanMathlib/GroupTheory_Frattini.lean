import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.Radical
def frattini (G : Type*) [Group G] : Subgroup G :=
  Order.radical (Subgroup G)
variable {G H : Type*} [Group G] [Group H] {φ : G →* H}
lemma frattini_le_coatom {K : Subgroup G} (h : IsCoatom K) : frattini G ≤ K :=
  Order.radical_le_coatom h
open Subgroup
lemma frattini_le_comap_frattini_of_surjective (hφ : Function.Surjective φ) :
    frattini G ≤ (frattini H).comap φ := by
  simp_rw [frattini, Order.radical, comap_iInf, le_iInf_iff]
  intro M hM
  apply biInf_le
  exact isCoatom_comap_of_surjective hφ hM
instance frattini_characteristic : (frattini G).Characteristic := by
  rw [characteristic_iff_comap_eq]
  intro φ
  apply φ.comapSubgroup.map_radical
theorem frattini_nongenerating [IsCoatomic (Subgroup G)] {K : Subgroup G}
    (h : K ⊔ frattini G = ⊤) : K = ⊤ :=
  Order.radical_nongenerating h
theorem frattini_nilpotent [Finite G] : Group.IsNilpotent (frattini G) := by
  have q := (isNilpotent_of_finite_tfae (G := frattini G)).out 0 3
  rw [q]; clear q
  intro p p_prime P
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  have normalizer_P := frattini_nongenerating frattini_argument
  have P_normal_in_G : (map (frattini G).subtype ↑P).Normal := normalizer_eq_top.mp normalizer_P
  exact P_normal_in_G.of_map_subtype