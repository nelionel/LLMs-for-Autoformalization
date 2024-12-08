import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
noncomputable section
attribute [local instance] Classical.propDecidable
open ENNReal
structure ENorm (𝕜 : Type*) (V : Type*) [NormedField 𝕜] [AddCommGroup V] [Module 𝕜 V] where
  toFun : V → ℝ≥0∞
  eq_zero' : ∀ x, toFun x = 0 → x = 0
  map_add_le' : ∀ x y : V, toFun (x + y) ≤ toFun x + toFun y
  map_smul_le' : ∀ (c : 𝕜) (x : V), toFun (c • x) ≤ ‖c‖₊ * toFun x
namespace ENorm
variable {𝕜 : Type*} {V : Type*} [NormedField 𝕜] [AddCommGroup V] [Module 𝕜 V] (e : ENorm 𝕜 V)
attribute [coe] ENorm.toFun
instance : CoeFun (ENorm 𝕜 V) fun _ => V → ℝ≥0∞ :=
  ⟨ENorm.toFun⟩
theorem coeFn_injective : Function.Injective ((↑) : ENorm 𝕜 V → V → ℝ≥0∞) := fun e₁ e₂ h => by
  cases e₁
  cases e₂
  congr
@[ext]
theorem ext {e₁ e₂ : ENorm 𝕜 V} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
  coeFn_injective <| funext h
@[simp, norm_cast]
theorem coe_inj {e₁ e₂ : ENorm 𝕜 V} : (e₁ : V → ℝ≥0∞) = e₂ ↔ e₁ = e₂ :=
  coeFn_injective.eq_iff
@[simp]
theorem map_smul (c : 𝕜) (x : V) : e (c • x) = ‖c‖₊ * e x := by
  apply le_antisymm (e.map_smul_le' c x)
  by_cases hc : c = 0
  · simp [hc]
  calc
    (‖c‖₊ : ℝ≥0∞) * e x = ‖c‖₊ * e (c⁻¹ • c • x) := by rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖₊ * (‖c⁻¹‖₊ * e (c • x)) := mul_le_mul_left' (e.map_smul_le' _ _) _
    _ = e (c • x) := by
      rw [← mul_assoc, nnnorm_inv, ENNReal.coe_inv, ENNReal.mul_inv_cancel _ ENNReal.coe_ne_top,
        one_mul]
        <;> simp [hc]
@[simp]
theorem map_zero : e 0 = 0 := by
  rw [← zero_smul 𝕜 (0 : V), e.map_smul]
  norm_num
@[simp]
theorem eq_zero_iff {x : V} : e x = 0 ↔ x = 0 :=
  ⟨e.eq_zero' x, fun h => h.symm ▸ e.map_zero⟩
@[simp]
theorem map_neg (x : V) : e (-x) = e x :=
  calc
    e (-x) = ‖(-1 : 𝕜)‖₊ * e x := by rw [← map_smul, neg_one_smul]
    _ = e x := by simp
theorem map_sub_rev (x y : V) : e (x - y) = e (y - x) := by rw [← neg_sub, e.map_neg]
theorem map_add_le (x y : V) : e (x + y) ≤ e x + e y :=
  e.map_add_le' x y
theorem map_sub_le (x y : V) : e (x - y) ≤ e x + e y :=
  calc
    e (x - y) = e (x + -y) := by rw [sub_eq_add_neg]
    _ ≤ e x + e (-y) := e.map_add_le x (-y)
    _ = e x + e y := by rw [e.map_neg]
instance partialOrder : PartialOrder (ENorm 𝕜 V) where
  le e₁ e₂ := ∀ x, e₁ x ≤ e₂ x
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁₂ h₂₃ x := le_trans (h₁₂ x) (h₂₃ x)
  le_antisymm _ _ h₁₂ h₂₁ := ext fun x => le_antisymm (h₁₂ x) (h₂₁ x)
noncomputable instance : Top (ENorm 𝕜 V) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else ⊤
      eq_zero' := fun x => by simp only; split_ifs <;> simp [*]
      map_add_le' := fun x y => by
        simp only
        split_ifs with hxy hx hy hy hx hy hy <;> try simp [*]
        simp [hx, hy] at hxy
      map_smul_le' := fun c x => by
        simp only
        split_ifs with hcx hx hx <;> simp only [smul_eq_zero, not_or] at hcx
        · simp only [mul_zero, le_refl]
        · have : c = 0 := by tauto
          simp [this]
        · tauto
        · simpa [mul_top'] using hcx.1 }⟩
noncomputable instance : Inhabited (ENorm 𝕜 V) :=
  ⟨⊤⟩
theorem top_map {x : V} (hx : x ≠ 0) : (⊤ : ENorm 𝕜 V) x = ⊤ :=
  if_neg hx
noncomputable instance : OrderTop (ENorm 𝕜 V) where
  top := ⊤
  le_top e x := if h : x = 0 then by simp [h] else by simp [top_map h]
noncomputable instance : SemilatticeSup (ENorm 𝕜 V) :=
  { ENorm.partialOrder with
    le := (· ≤ ·)
    lt := (· < ·)
    sup := fun e₁ e₂ =>
      { toFun := fun x => max (e₁ x) (e₂ x)
        eq_zero' := fun _ h => e₁.eq_zero_iff.1 (ENNReal.max_eq_zero_iff.1 h).1
        map_add_le' := fun _ _ =>
          max_le (le_trans (e₁.map_add_le _ _) <| add_le_add (le_max_left _ _) (le_max_left _ _))
            (le_trans (e₂.map_add_le _ _) <| add_le_add (le_max_right _ _) (le_max_right _ _))
        map_smul_le' := fun c x => le_of_eq <| by simp only [map_smul, mul_max] }
    le_sup_left := fun _ _ _ => le_max_left _ _
    le_sup_right := fun _ _ _ => le_max_right _ _
    sup_le := fun _ _ _ h₁ h₂ x => max_le (h₁ x) (h₂ x) }
@[simp, norm_cast]
theorem coe_max (e₁ e₂ : ENorm 𝕜 V) : ⇑(e₁ ⊔ e₂) = fun x => max (e₁ x) (e₂ x) :=
  rfl
@[norm_cast]
theorem max_map (e₁ e₂ : ENorm 𝕜 V) (x : V) : (e₁ ⊔ e₂) x = max (e₁ x) (e₂ x) :=
  rfl
abbrev emetricSpace : EMetricSpace V where
  edist x y := e (x - y)
  edist_self x := by simp
  eq_of_edist_eq_zero {x y} := by simp [sub_eq_zero]
  edist_comm := e.map_sub_rev
  edist_triangle x y z :=
    calc
      e (x - z) = e (x - y + (y - z)) := by rw [sub_add_sub_cancel]
      _ ≤ e (x - y) + e (y - z) := e.map_add_le (x - y) (y - z)
def finiteSubspace : Subspace 𝕜 V where
  carrier := { x | e x < ⊤ }
  zero_mem' := by simp
  add_mem' {x y} hx hy := lt_of_le_of_lt (e.map_add_le x y) (ENNReal.add_lt_top.2 ⟨hx, hy⟩)
  smul_mem' c x (hx : _ < _) :=
    calc
      e (c • x) = ‖c‖₊ * e x := e.map_smul c x
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hx
instance metricSpace : MetricSpace e.finiteSubspace := by
  letI := e.emetricSpace
  refine EMetricSpace.toMetricSpace fun x y => ?_
  change e (x - y) ≠ ⊤
  exact ne_top_of_le_ne_top (ENNReal.add_lt_top.2 ⟨x.2, y.2⟩).ne (e.map_sub_le x y)
theorem finite_dist_eq (x y : e.finiteSubspace) : dist x y = (e (x - y)).toReal :=
  rfl
theorem finite_edist_eq (x y : e.finiteSubspace) : edist x y = e (x - y) :=
  rfl
instance normedAddCommGroup : NormedAddCommGroup e.finiteSubspace :=
  { e.metricSpace with
    norm := fun x => (e x).toReal
    dist_eq := fun _ _ => rfl }
theorem finite_norm_eq (x : e.finiteSubspace) : ‖x‖ = (e x).toReal :=
  rfl
instance normedSpace : NormedSpace 𝕜 e.finiteSubspace where
  norm_smul_le c x := le_of_eq <| by simp [finite_norm_eq, ENNReal.toReal_mul]
end ENorm