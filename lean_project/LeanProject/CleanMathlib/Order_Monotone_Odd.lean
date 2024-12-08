import Mathlib.Order.Monotone.Union
import Mathlib.Algebra.Order.Group.Instances
open Set
variable {G H : Type*} [LinearOrderedAddCommGroup G] [OrderedAddCommGroup H]
theorem strictMono_of_odd_strictMonoOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictMonoOn f (Ici 0)) : StrictMono f := by
  refine StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 ?_) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)
theorem strictAnti_of_odd_strictAntiOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictAntiOn f (Ici 0)) : StrictAnti f :=
  @strictMono_of_odd_strictMonoOn_nonneg G Hᵒᵈ _ _ _ h₁ h₂
theorem monotone_of_odd_of_monotoneOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : MonotoneOn f (Ici 0)) : Monotone f := by
  refine MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 ?_) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)
theorem antitone_of_odd_of_monotoneOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : AntitoneOn f (Ici 0)) : Antitone f :=
  @monotone_of_odd_of_monotoneOn_nonneg G Hᵒᵈ _ _ _ h₁ h₂