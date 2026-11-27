import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25625

def mx (x : ℤ → Bool) (z : ℤ) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def ev (x : ℤ → Bool) (z : ℤ) : Bool := xor (mx x z) (!(mx x (z+1)) && mx x (z+2))

def EA (F : Set (ℤ → Bool)) (e : ℤ) : Prop :=
  (∀ x ∈ F, ∀ z ≤ e, x z = false) ∧ ∃ x ∈ F, x (e+1) = true

theorem ev_eq (x : ℤ → Bool) (z : ℤ) : ev x z =
    xor (xor (xor (x (z-1)) (x z)) (x (z+1)))
      (!(xor (xor (x z) (x (z+1))) (x (z+2))) && xor (xor (x (z+1)) (x (z+2))) (x (z+3))) := by
  unfold ev mx
  rw [show z+1-1 = z by ring, show z+1+1 = z+2 by ring, show z+2-1 = z+1 by ring,
    show z+2+1 = z+3 by ring]

theorem ev_zero (x : ℤ → Bool) (e : ℤ) (h : ∀ z ≤ e, x z = false) (z : ℤ) (hz : z ≤ e-3) :
    ev x z = false := by
  rw [ev_eq, h (z-1) (by omega), h z (by omega), h (z+1) (by omega), h (z+2) (by omega),
    h (z+3) (by omega)]
  rfl

theorem ev_one (x : ℤ → Bool) (e : ℤ) (h : ∀ z ≤ e, x z = false) (h1 : x (e+1) = true) :
    ev x (e-2) = true := by
  rw [ev_eq, show e-2+3 = e+1 by ring, h1, h (e-2-1) (by omega), h (e-2) (by omega),
    h (e-2+1) (by omega), h (e-2+2) (by omega)]
  rfl

theorem img_step (F : Set (ℤ → Bool)) (e : ℤ) (h : EA F e) : EA (ev '' F) (e-3) := by
  obtain ⟨h0, x, hx, h1⟩ := h
  refine ⟨?_, ev x, ⟨x, hx, rfl⟩, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩ z hz
    exact ev_zero y e (h0 y hy) z hz
  · rw [show e-3+1 = e-2 by ring]
    exact ev_one x e (h0 x hx) h1

theorem scan_step (F : Set (ℤ → Bool)) (e c : ℤ) (h : EA F e) :
    EA {y | ∃ x ∈ F, ∀ site ≤ c, y site = ev x site} (min (e-3) c) := by
  obtain ⟨h0, x, hx, h1⟩ := h
  refine ⟨?_, ?_⟩
  · rintro y ⟨u, hu, hy⟩ z hz
    have hz' := le_min_iff.mp hz
    rw [hy z hz'.2]
    exact ev_zero u e (h0 u hu) z hz'.1
  · by_cases hc : e-2 ≤ c
    · rw [min_eq_left (by omega)]
      refine ⟨ev x, ⟨x, hx, fun _ _ => rfl⟩, ?_⟩
      rw [show e-3+1 = e-2 by ring]
      exact ev_one x e (h0 x hx) h1
    · rw [min_eq_right (by omega)]
      refine ⟨fun s => if s ≤ c then ev x s else true, ⟨x, hx, fun s hs => if_pos hs⟩, ?_⟩
      simp

theorem orb (S : Set (ℤ → Bool)) (E : ℤ) (h : EA S E) (k : ℕ) :
    EA ((List.range k).foldl (fun (family : Set (ℤ → Bool)) _ => ev '' family) S)
      (E - 3*(k : ℤ)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := img_step _ _ ih
    rw [show E - 3*(((k+1 : ℕ)) : ℤ) = E - 3*(k : ℤ) - 3 by push_cast; ring]
    exact this

def gE (E : ℤ) (cut : ℕ → ℤ) (k : ℕ) : ℤ :=
  (List.range k).foldl (fun cur idx => min (cur-3) (cut (idx+1))) E

theorem gE_succ (E : ℤ) (cut : ℕ → ℤ) (k : ℕ) :
    gE E cut (k+1) = min (gE E cut k - 3) (cut (k+1)) := by
  unfold gE
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sc (S : Set (ℤ → Bool)) (E : ℤ) (cut : ℕ → ℤ) (h : EA S E) (k : ℕ) :
    EA ((List.range k).foldl (fun (old : Set (ℤ → Bool)) tick =>
      {y | ∃ x ∈ old, ∀ site ≤ cut (tick+1), y site = ev x site}) S) (gE E cut k) := by
  induction k with
  | zero => simpa [gE] using h
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, gE_succ]
    exact scan_step _ _ _ ih

theorem fin_eq (E : ℤ) (cut : ℕ → ℤ) (n : ℕ) (k : ℕ) (hk : k ≤ n) :
    (List.range k).foldl (fun current idx =>
      min current (cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ))) (E - 3*(n : ℤ)) =
      gE E cut k - 3*((n-k : ℕ) : ℤ) := by
  induction k with
  | zero => simp [gE]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
      gE_succ]
    omega

end PEqualNP.Outside.L_meta_25625

open PEqualNP.Outside.L_meta_25625 in
theorem PEqualNP.Outside.L_meta_25625 :
    let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
    let evolve := fun (x : ℤ → Bool) (z : ℤ) =>
      xor (mix x z) (!(mix x (z+1)) && mix x (z+2))
    let edgeAt := fun (family : Set (ℤ → Bool)) (edge : ℤ) =>
      (∀ x ∈ family, ∀ z ≤ edge, x z = false) ∧
      ∃ x ∈ family, x (edge+1) = true
    ∀ (S : Set (ℤ → Bool)) (E : ℤ) (cut : ℕ → ℤ) (n : ℕ), edgeAt S E →
      let orbit := (List.range n).foldl (fun (family : Set (ℤ → Bool)) _ => evolve '' family) S
      let scan := (List.range n).foldl (fun (old : Set (ℤ → Bool)) tick =>
        {y | ∃ x ∈ old, ∀ site ≤ cut (tick+1), y site = evolve x site}) S
      let trueEdge := E - 3*(n : ℤ)
      let finalEdge := (List.range n).foldl (fun current idx =>
        min current (cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ))) trueEdge
      edgeAt orbit trueEdge ∧ edgeAt scan finalEdge
 := by
  intro mix evolve edgeAt S E cut n h
  have h' : EA S E := h
  have key := fin_eq E cut n n le_rfl
  rw [Nat.sub_self, Nat.cast_zero, mul_zero, sub_zero] at key
  have A := orb S E h' n
  have B := sc S E cut h' n
  rw [← key] at B
  exact ⟨A, B⟩
