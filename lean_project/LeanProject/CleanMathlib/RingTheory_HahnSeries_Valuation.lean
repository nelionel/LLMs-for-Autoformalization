import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Valuation.Basic
noncomputable section
variable {Γ R : Type*}
namespace HahnSeries
section Valuation
variable (Γ R) [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]
def addVal : AddValuation (HahnSeries Γ R) (WithTop Γ) :=
  AddValuation.of orderTop orderTop_zero (orderTop_one) (fun _ _ => min_orderTop_le_orderTop_add)
  fun x y => by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    rw [← order_eq_orderTop_of_ne hx, ← order_eq_orderTop_of_ne hy,
      ← order_eq_orderTop_of_ne (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
      order_mul hx hy]
variable {Γ} {R}
theorem addVal_apply {x : HahnSeries Γ R} :
    addVal Γ R x = x.orderTop :=
  AddValuation.of_apply _
@[simp]
theorem addVal_apply_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : addVal Γ R x = x.order :=
  addVal_apply.trans (order_eq_orderTop_of_ne hx).symm
theorem addVal_le_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) :
    addVal Γ R x ≤ g :=
  orderTop_le_of_coeff_ne_zero h
end Valuation
end HahnSeries