import Mathlib.Algebra.MonoidAlgebra.Defs
variable {k G : Type*} [Semiring k]
namespace AddMonoidAlgebra
section
variable [AddCancelCommMonoid G]
noncomputable def divOf (x : k[G]) (g : G) : k[G] :=
  @Finsupp.comapDomain.addMonoidHom _ _ _ _ (g + ·) (add_right_injective g) x
local infixl:70 " /ᵒᶠ " => divOf
@[simp]
theorem divOf_apply (g : G) (x : k[G]) (g' : G) : (x /ᵒᶠ g) g' = x (g + g') :=
  rfl
@[simp]
theorem support_divOf (g : G) (x : k[G]) :
    (x /ᵒᶠ g).support =
      x.support.preimage (g + ·) (Function.Injective.injOn (add_right_injective g)) :=
  rfl
@[simp]
theorem zero_divOf (g : G) : (0 : k[G]) /ᵒᶠ g = 0 :=
  map_zero (Finsupp.comapDomain.addMonoidHom _)
@[simp]
theorem divOf_zero (x : k[G]) : x /ᵒᶠ 0 = x := by
  refine Finsupp.ext fun _ => ?_  
  simp only [AddMonoidAlgebra.divOf_apply, zero_add]
theorem add_divOf (x y : k[G]) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g :=
  map_add (Finsupp.comapDomain.addMonoidHom _) _ _
theorem divOf_add (x : k[G]) (a b : G) : x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b := by
  refine Finsupp.ext fun _ => ?_  
  simp only [AddMonoidAlgebra.divOf_apply, add_assoc]
@[simps]
noncomputable def divOfHom : Multiplicative G →* AddMonoid.End k[G] where
  toFun g :=
    { toFun := fun x => divOf x g.toAdd
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y g.toAdd }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun _x =>
      (congr_arg _ (add_comm g₁.toAdd g₂.toAdd)).trans
        (divOf_add _ _ _)
theorem of'_mul_divOf (a : G) (x : k[G]) : of' k G a * x /ᵒᶠ a = x := by
  refine Finsupp.ext fun _ => ?_  
  rw [AddMonoidAlgebra.divOf_apply, of'_apply, single_mul_apply_aux, one_mul]
  intro c
  exact add_right_inj _
theorem mul_of'_divOf (x : k[G]) (a : G) : x * of' k G a /ᵒᶠ a = x := by
  refine Finsupp.ext fun _ => ?_  
  rw [AddMonoidAlgebra.divOf_apply, of'_apply, mul_single_apply_aux, mul_one]
  intro c
  rw [add_comm]
  exact add_right_inj _
theorem of'_divOf (a : G) : of' k G a /ᵒᶠ a = 1 := by
  simpa only [one_mul] using mul_of'_divOf (1 : k[G]) a
noncomputable def modOf (x : k[G]) (g : G) : k[G] :=
  letI := Classical.decPred fun g₁ => ∃ g₂, g₁ = g + g₂
  x.filter fun g₁ => ¬∃ g₂, g₁ = g + g₂
local infixl:70 " %ᵒᶠ " => modOf
@[simp]
theorem modOf_apply_of_not_exists_add (x : k[G]) (g : G) (g' : G)
    (h : ¬∃ d, g' = g + d) : (x %ᵒᶠ g) g' = x g' := by
  classical exact Finsupp.filter_apply_pos _ _ h
@[simp]
theorem modOf_apply_of_exists_add (x : k[G]) (g : G) (g' : G)
    (h : ∃ d, g' = g + d) : (x %ᵒᶠ g) g' = 0 := by
  classical exact Finsupp.filter_apply_neg _ _ <| by rwa [Classical.not_not]
@[simp]
theorem modOf_apply_add_self (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g) (d + g) = 0 :=
  modOf_apply_of_exists_add _ _ _ ⟨_, add_comm _ _⟩
theorem modOf_apply_self_add (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g) (g + d) = 0 :=
  modOf_apply_of_exists_add _ _ _ ⟨_, rfl⟩
theorem of'_mul_modOf (g : G) (x : k[G]) : of' k G g * x %ᵒᶠ g = 0 := by
  refine Finsupp.ext fun g' => ?_  
  rw [Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [modOf_apply_self_add]
  · rw [modOf_apply_of_not_exists_add _ _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h]
theorem mul_of'_modOf (x : k[G]) (g : G) : x * of' k G g %ᵒᶠ g = 0 := by
  refine Finsupp.ext fun g' => ?_  
  rw [Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [modOf_apply_self_add]
  · rw [modOf_apply_of_not_exists_add _ _ _ h, of'_apply, mul_single_apply_of_not_exists_add]
    simpa only [add_comm] using h
theorem of'_modOf (g : G) : of' k G g %ᵒᶠ g = 0 := by
  simpa only [one_mul] using mul_of'_modOf (1 : k[G]) g
theorem divOf_add_modOf (x : k[G]) (g : G) :
    of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x := by
  refine Finsupp.ext fun g' => ?_  
  rw [Finsupp.add_apply] 
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  swap
  · rw [modOf_apply_of_not_exists_add x _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h,
      zero_add]
  · rw [modOf_apply_self_add, add_zero]
    rw [of'_apply, single_mul_apply_aux _ _ _, one_mul, divOf_apply]
    intro a
    exact add_right_inj _
theorem modOf_add_divOf (x : k[G]) (g : G) : x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x := by
  rw [add_comm, divOf_add_modOf]
theorem of'_dvd_iff_modOf_eq_zero {x : k[G]} {g : G} :
    of' k G g ∣ x ↔ x %ᵒᶠ g = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [of'_mul_modOf]
  · intro h
    rw [← divOf_add_modOf x g, h, add_zero]
    exact dvd_mul_right _ _
end
end AddMonoidAlgebra