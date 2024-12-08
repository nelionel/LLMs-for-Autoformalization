import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Hom.CompleteLattice
variable {α : Type*}
open OrderDual
namespace UpperSet
section SemilatticeSup
variable [SemilatticeSup α]
def iciSupHom : SupHom α (UpperSet α) :=
  ⟨Ici, Ici_sup⟩
@[simp]
theorem coe_iciSupHom : (iciSupHom : α → UpperSet α) = Ici :=
  rfl
@[simp]
theorem iciSupHom_apply (a : α) : iciSupHom a = Ici a :=
  rfl
end SemilatticeSup
variable [CompleteLattice α]
def icisSupHom : sSupHom α (UpperSet α) :=
  ⟨Ici, fun s => (Ici_sSup s).trans sSup_image.symm⟩
@[simp]
theorem coe_icisSupHom : (icisSupHom : α → UpperSet α) = Ici :=
  rfl
@[simp]
theorem icisSupHom_apply (a : α) : icisSupHom a = Ici a :=
  rfl
end UpperSet
namespace LowerSet
section SemilatticeInf
variable [SemilatticeInf α]
def iicInfHom : InfHom α (LowerSet α) :=
  ⟨Iic, Iic_inf⟩
@[simp]
theorem coe_iicInfHom : (iicInfHom : α → LowerSet α) = Iic :=
  rfl
@[simp]
theorem iicInfHom_apply (a : α) : iicInfHom a = Iic a :=
  rfl
end SemilatticeInf
variable [CompleteLattice α]
def iicsInfHom : sInfHom α (LowerSet α) :=
  ⟨Iic, fun s => (Iic_sInf s).trans sInf_image.symm⟩
@[simp]
theorem coe_iicsInfHom : (iicsInfHom : α → LowerSet α) = Iic :=
  rfl
@[simp]
theorem iicsInfHom_apply (a : α) : iicsInfHom a = Iic a :=
  rfl
end LowerSet