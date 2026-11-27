import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_496_aux

theorem slack_one (p a : Bool) (h : p = true → a = true) :
    p.toNat + (!a).toNat + (!p && a).toNat = 1 := by
  revert h
  cases p <;> cases a <;> simp

theorem sel_one (j : Fin 3) :
    (decide ((0 : Fin 3) = j)).toNat + (decide ((1 : Fin 3) = j)).toNat +
      (decide ((2 : Fin 3) = j)).toNat = 1 := by
  revert j
  decide

theorem pick (a b c : Bool) (h : a.toNat + b.toNat + c.toNat = 1) :
    a = true ∨ b = true ∨ c = true := by
  revert a b c
  decide

theorem forced (a s : Bool) (h : true.toNat + (!a).toNat + s.toNat = 1) : a = true := by
  revert a s
  decide

end PEqualNP.Outside.L_lib_496_aux

theorem PEqualNP.Outside.L_lib_496 : (∀ (n m : ℕ) (L : Fin m → Fin 3 → Fin n × Bool),
  let ev := fun (x : Fin n → Bool) (i : Fin m) (k : Fin 3) => x (L i k).1 == (L i k).2
  let one := fun (a b c : Bool) => a.toNat + b.toNat + c.toNat = 1
  (∃ x : Fin n → Bool, ∀ i, ∃ k, ev x i k = true) ↔
    ∃ (x : Fin n → Bool) (p s : Fin m → Fin 3 → Bool), ∀ i,
      one (p i 0) (p i 1) (p i 2) ∧
      ∀ k, one (p i k) (!(ev x i k)) (s i k)) := by
  intro n m L ev one
  constructor
  · rintro ⟨x, hx⟩
    choose kk hk using hx
    refine ⟨x, fun i k => decide (k = kk i), fun i k => !(decide (k = kk i)) && ev x i k,
      fun i => ⟨?_, fun k => ?_⟩⟩
    · exact PEqualNP.Outside.L_lib_496_aux.sel_one (kk i)
    · refine PEqualNP.Outside.L_lib_496_aux.slack_one _ _ (fun h => ?_)
      have hkk : k = kk i := of_decide_eq_true h
      rw [hkk]
      exact hk i
  · rintro ⟨x, p, s, h⟩
    refine ⟨x, fun i => ?_⟩
    obtain ⟨h1, h2⟩ := h i
    rcases PEqualNP.Outside.L_lib_496_aux.pick _ _ _ h1 with h0 | h0 | h0
    · have h3 := h2 0
      rw [h0] at h3
      exact ⟨0, PEqualNP.Outside.L_lib_496_aux.forced _ _ h3⟩
    · have h3 := h2 1
      rw [h0] at h3
      exact ⟨1, PEqualNP.Outside.L_lib_496_aux.forced _ _ h3⟩
    · have h3 := h2 2
      rw [h0] at h3
      exact ⟨2, PEqualNP.Outside.L_lib_496_aux.forced _ _ h3⟩
