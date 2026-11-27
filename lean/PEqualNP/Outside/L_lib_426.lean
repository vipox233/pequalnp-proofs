import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_426 : (∀ (m n q : ℕ) (M : Fin m → Fin n → Bool),
  (∃ (A : Fin q → Finset (Fin m)) (B : Fin q → Finset (Fin n)),
    ∀ x y, M x y = true ↔ ∃ i, x ∈ A i ∧ y ∈ B i) ↔
  ∃ color : {p : Fin m × Fin n // M p.1 p.2 = true} → Fin q,
    ∀ e f, color e = color f → M e.val.1 f.val.2 = true) := by
  classical
  intro m n q M
  let Cell := {p : Fin m × Fin n // M p.1 p.2 = true}
  constructor
  · rintro ⟨A, B, cover⟩
    have covered (e : Cell) : ∃ i, e.val.1 ∈ A i ∧ e.val.2 ∈ B i :=
      (cover _ _).mp e.property
    let color (e : Cell) : Fin q := Classical.choose (covered e)
    have mem_rect (e : Cell) : e.val.1 ∈ A (color e) ∧ e.val.2 ∈ B (color e) :=
      Classical.choose_spec (covered e)
    refine ⟨color, ?_⟩
    intro e f same
    apply (cover _ _).mpr
    exact ⟨color e, (mem_rect e).1, same.symm ▸ (mem_rect f).2⟩
  · rintro ⟨color, cross⟩
    let A (i : Fin q) := Finset.univ.filter
      (fun x : Fin m => ∃ e : Cell, color e = i ∧ e.val.1 = x)
    let B (i : Fin q) := Finset.univ.filter
      (fun y : Fin n => ∃ f : Cell, color f = i ∧ f.val.2 = y)
    refine ⟨A, B, ?_⟩
    intro x y
    constructor
    · intro h
      let e : Cell := ⟨(x, y), h⟩
      exact ⟨color e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, rfl, rfl⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, rfl, rfl⟩⟩
    · rintro ⟨i, hx, hy⟩
      obtain ⟨e, he, rfl⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨f, hf, rfl⟩ := (Finset.mem_filter.mp hy).2
      exact cross e f (he.trans hf.symm)
