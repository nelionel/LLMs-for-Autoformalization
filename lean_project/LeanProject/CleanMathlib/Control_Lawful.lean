import Mathlib.Tactic.Basic
universe u v
namespace StateT
section
variable {σ : Type u}
variable {m : Type u → Type v}
variable {α : Type u}
protected def mk (f : σ → m (α × σ)) : StateT σ m α := f
@[simp]
theorem run_mk (f : σ → m (α × σ)) (st : σ) : StateT.run (StateT.mk f) st = f st :=
  rfl
end
end StateT
namespace ExceptT
variable {α ε : Type u} {m : Type u → Type v} (x : ExceptT ε m α)
attribute [simp] run_bind
@[simp]
theorem run_monadLift {n} [Monad m] [MonadLiftT n m] (x : n α) :
    (monadLift x : ExceptT ε m α).run = Except.ok <$> (monadLift x : m α) :=
  rfl
@[simp]
theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : ExceptT ε m α).run = monadMap (@f) x.run :=
  rfl
end ExceptT
namespace ReaderT
section
variable {m : Type u → Type v}
variable {α σ : Type u}
protected def mk (f : σ → m α) : ReaderT σ m α := f
@[simp]
theorem run_mk (f : σ → m α) (r : σ) : ReaderT.run (ReaderT.mk f) r = f r :=
  rfl
end
end ReaderT
namespace OptionT
variable {α β : Type u} {m : Type u → Type v} (x : OptionT m α)
@[ext] theorem ext {x x' : OptionT m α} (h : x.run = x'.run) : x = x' :=
  h
@[simp]
theorem run_mk (x : m (Option α)) : OptionT.run (OptionT.mk x) = x :=
  rfl
section Monad
variable [Monad m]
@[simp]
theorem run_pure (a) : (pure a : OptionT m α).run = pure (some a) :=
  rfl
@[simp]
theorem run_bind (f : α → OptionT m β) :
    (x >>= f).run = x.run >>= fun
                              | some a => OptionT.run (f a)
                              | none   => pure none :=
  rfl
@[simp]
theorem run_map (f : α → β) [LawfulMonad m] : (f <$> x).run = Option.map f <$> x.run := by
  rw [← bind_pure_comp _ x.run]
  change x.run >>= (fun
                     | some a => OptionT.run (pure (f a))
                     | none   => pure none) = _
  apply bind_congr
  intro a; cases a <;> simp [Option.map, Option.bind]
@[simp]
theorem run_monadLift {n} [MonadLiftT n m] (x : n α) :
    (monadLift x : OptionT m α).run = (monadLift x : m α) >>= fun a => pure (some a) :=
  rfl
end Monad
@[simp]
theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : OptionT m α).run = monadMap (@f) x.run :=
  rfl
end OptionT
instance (m : Type u → Type v) [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m) :=
  LawfulMonad.mk'
    (id_map := by
      intros; apply OptionT.ext; simp only [OptionT.run_map]
      rw [map_congr, id_map]
      intro a; cases a <;> rfl)
    (bind_assoc := by
      intros; apply OptionT.ext; simp only [OptionT.run_bind, bind_assoc]
      rw [bind_congr]
      intro a; cases a <;> simp)
    (pure_bind := by intros; apply OptionT.ext; simp)