import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.ConcreteCategory.Basic
open CategoryTheory
attribute [elementwise (attr := simp)] Iso.hom_inv_id Iso.inv_hom_id
set_option linter.existingAttributeWarning false in
attribute [elementwise (attr := simp)] IsIso.hom_inv_id IsIso.inv_hom_id