import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_977

open Finset

def eps (c : ZMod 2) : ℤ := if c = 0 then 1 else -1

theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

@[simp] theorem eps_zero : eps 0 = 1 := rfl
@[simp] theorem eps_one : eps 1 = -1 := rfl

theorem eps_add (a b : ZMod 2) : eps (a + b) = eps a * eps b := by
  rcases z2 a with h | h <;> rcases z2 b with h' | h' <;> subst h <;> subst h' <;> rfl

theorem eps_sq (a : ZMod 2) : eps a * eps a = 1 := by
  rcases z2 a with h | h <;> subst h <;> rfl

theorem vadd_self {n : ℕ} (u : Fin n → ZMod 2) : u + u = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]; rcases z2 (u i) with h | h <;> rw [h] <;> decide

theorem sum_eps_dot {n : ℕ} (c : Fin n → ZMod 2) :
    ∑ u : Fin n → ZMod 2, eps (u ⬝ᵥ c) = if c = 0 then 2 ^ n else 0 := by
  split_ifs with hc
  · subst hc
    simp [eps, Finset.card_univ, ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h; push Not at h; exact hc (funext h)
    have hci : c i = 1 := by
      rcases z2 (c i) with h | h
      · exact absurd h hi
      · exact h
    have key := Fintype.sum_equiv (Equiv.addRight (Pi.single i 1))
      (fun u => eps ((u + Pi.single i 1) ⬝ᵥ c)) (fun u => eps (u ⬝ᵥ c)) (fun _ => rfl)
    simp only [add_dotProduct, single_dotProduct, hci, eps_add, eps_one, mul_neg,
      mul_one, Finset.sum_neg_distrib] at key
    linarith

def one1 (d : ℕ) : Fin d → ZMod 2 := fun _ => 1

theorem one1_ne (d : ℕ) (hd : 0 < d) : one1 d ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hd⟩
  simp [one1] at this

theorem par_single (d : ℕ) (i : Fin d) : one1 d ⬝ᵥ Pi.single i 1 = 1 := by
  simp [one1, dotProduct_single]

theorem span {d : ℕ} (hd : 0 < d) (P : (Fin d → ZMod 2) → Prop) (e : ZMod 2)
    (y : Fin d → ZMod 2) (hy : one1 d ⬝ᵥ y ≠ e) (hP : ∀ x, one1 d ⬝ᵥ x = e → P x)
    (hPy : P y) :
    ∀ a : Fin d → ZMod 2, a ≠ 0 → ∃ x z, P x ∧ P z ∧ a ⬝ᵥ x ≠ a ⬝ᵥ z := by
  intro a ha
  by_cases h1 : a = one1 d
  · subst h1
    rcases z2 e with he | he
    · refine ⟨0, y, hP 0 (by rw [dotProduct_zero, he]), hPy, ?_⟩
      rw [dotProduct_zero]; rw [he] at hy; exact fun h => hy h.symm
    · refine ⟨Pi.single ⟨0, hd⟩ 1, y, hP _ (by rw [par_single, he]), hPy, ?_⟩
      rw [par_single]; rw [he] at hy; exact fun h => hy h.symm
  · obtain ⟨i, hi⟩ : ∃ i, a i = 1 := by
      by_contra hc
      apply ha; funext i
      rcases z2 (a i) with h | h
      · exact h
      · exact absurd ⟨i, h⟩ hc
    obtain ⟨j, hj⟩ : ∃ j, a j = 0 := by
      by_contra hc
      apply h1; funext j
      rcases z2 (a j) with h | h
      · exact absurd ⟨j, h⟩ hc
      · exact h
    rcases z2 e with he | he
    · refine ⟨0, Pi.single i 1 + Pi.single j 1, hP 0 (by rw [dotProduct_zero, he]), hP _ ?_, ?_⟩
      · rw [dotProduct_add, par_single, par_single, he]; decide
      · rw [dotProduct_zero, dotProduct_add, dotProduct_single, dotProduct_single, hi, hj]
        decide
    · refine ⟨Pi.single i 1, Pi.single j 1, hP _ (by rw [par_single, he]),
        hP _ (by rw [par_single, he]), ?_⟩
      rw [dotProduct_single, dotProduct_single, hi, hj]; decide

theorem invert {d : ℕ} (D : (Fin d → ZMod 2) → ℤ)
    (h : ∀ a, a ≠ one1 d → ∑ x, D x * eps (a ⬝ᵥ x) = 0) :
    ∀ y, D y = D 0 * eps (one1 d ⬝ᵥ y) := by
  have key : ∀ y, ∑ a : Fin d → ZMod 2, (∑ x, D x * eps (a ⬝ᵥ x)) * eps (a ⬝ᵥ y)
      = 2 ^ d * D y := by
    intro y
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have hx : ∀ x, ∑ a : Fin d → ZMod 2, D x * eps (a ⬝ᵥ x) * eps (a ⬝ᵥ y)
        = D x * (if x + y = 0 then 2 ^ d else 0) := by
      intro x
      rw [← sum_eps_dot (x + y), Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_assoc, ← eps_add, dotProduct_add]
    rw [Finset.sum_congr rfl fun x _ => hx x]
    rw [Finset.sum_eq_single y]
    · rw [if_pos (vadd_self y)]; ring
    · intro x _ hxy
      have hne : x + y ≠ 0 := by
        intro h'; apply hxy
        calc x = x + y + y := by rw [add_assoc, vadd_self, add_zero]
          _ = y := by rw [h', zero_add]
      rw [if_neg hne, mul_zero]
    · intro hy; exact absurd (Finset.mem_univ y) hy
  have red : ∀ y, ∑ a : Fin d → ZMod 2, (∑ x, D x * eps (a ⬝ᵥ x)) * eps (a ⬝ᵥ y)
      = (∑ x, D x * eps (one1 d ⬝ᵥ x)) * eps (one1 d ⬝ᵥ y) := by
    intro y
    rw [Finset.sum_eq_single (one1 d)]
    · intro a _ ha; rw [h a ha, zero_mul]
    · intro hy; exact absurd (Finset.mem_univ _) hy
  intro y
  have h0 := key 0
  have hy := key y
  rw [red] at h0 hy
  simp only [dotProduct_zero, eps_zero, mul_one] at h0
  have hpos : (2 : ℤ) ^ d ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  rw [← hy, h0]
  ring

theorem core {d : ℕ} (hd : 0 < d) (A B : (Fin d → ZMod 2) → ℕ) (e : ZMod 2) (k : ℕ)
    (hk : 0 < k)
    (hDA : ∀ x, one1 d ⬝ᵥ x = e → A x = B x + k)
    (hDB : ∀ x, one1 d ⬝ᵥ x ≠ e → B x = A x + k)
    (hA : ¬ ∀ a : Fin d → ZMod 2, a ≠ 0 → ∃ x y, 0 < A x ∧ 0 < A y ∧ a ⬝ᵥ x ≠ a ⬝ᵥ y)
    (hB : ∀ a : Fin d → ZMod 2, a ≠ 0 → ∃ x y, 0 < B x ∧ 0 < B y ∧ a ⬝ᵥ x ≠ a ⬝ᵥ y) :
    ∃ (H : (Fin d → ZMod 2) → ℕ), (∃ x, 0 < H x) ∧ (∀ x, one1 d ⬝ᵥ x ≠ e → H x = 0) ∧
      ∀ x, A x = H x + (if one1 d ⬝ᵥ x = e then k else 0) ∧
        B x = H x + (if one1 d ⬝ᵥ x = e then 0 else k) := by
  have hA0 : ∀ y, one1 d ⬝ᵥ y ≠ e → A y = 0 := by
    intro y hy
    by_contra hne
    exact hA (span hd (fun x => 0 < A x) e y hy (fun x hx => by rw [hDA x hx]; omega)
      (Nat.pos_of_ne_zero hne))
  refine ⟨fun x => if one1 d ⬝ᵥ x = e then B x else 0, ?_, ?_, ?_⟩
  · by_contra hn
    have hz : ∀ x, one1 d ⬝ᵥ x = e → B x = 0 := by
      intro x hx
      by_contra hne
      exact hn ⟨x, by dsimp only; rw [if_pos hx]; omega⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := hB (one1 d) (one1_ne d hd)
    have px : one1 d ⬝ᵥ x ≠ e := fun h => by rw [hz x h] at hx; exact lt_irrefl _ hx
    have py : one1 d ⬝ᵥ y ≠ e := fun h => by rw [hz y h] at hy; exact lt_irrefl _ hy
    apply hxy
    rcases z2 e with he | he <;> subst he <;>
      rcases z2 (one1 d ⬝ᵥ x) with h1 | h1 <;> rcases z2 (one1 d ⬝ᵥ y) with h2 | h2 <;>
      simp_all
  · intro x hx
    dsimp only
    rw [if_neg hx]
  · intro x
    dsimp only
    by_cases hx : one1 d ⬝ᵥ x = e
    · rw [if_pos hx, if_pos hx, if_pos hx]
      exact ⟨hDA x hx, by omega⟩
    · rw [if_neg hx, if_neg hx, if_neg hx]
      have h1 := hA0 x hx
      have h2 := hDB x hx
      omega

theorem back {d : ℕ} (hd : 0 < d) (A B : (Fin d → ZMod 2) → ℕ) (e : ZMod 2) (k : ℕ)
    (H : (Fin d → ZMod 2) → ℕ) (hk : 0 < k) (hH : ∃ x, 0 < H x)
    (hHs : ∀ x, one1 d ⬝ᵥ x ≠ e → H x = 0)
    (hAB : ∀ x, A x = H x + (if one1 d ⬝ᵥ x = e then k else 0) ∧
        B x = H x + (if one1 d ⬝ᵥ x = e then 0 else k)) :
    (∀ a, a ≠ one1 d → ∑ x, (A x : ℤ) * eps (a ⬝ᵥ x) = ∑ x, (B x : ℤ) * eps (a ⬝ᵥ x)) ∧
    (¬ ∀ a : Fin d → ZMod 2, a ≠ 0 → ∃ x y, 0 < A x ∧ 0 < A y ∧ a ⬝ᵥ x ≠ a ⬝ᵥ y) ∧
    (∀ a : Fin d → ZMod 2, a ≠ 0 → ∃ x y, 0 < B x ∧ 0 < B y ∧ a ⬝ᵥ x ≠ a ⬝ᵥ y) := by
  have hee : ∀ e : ZMod 2, e + 1 ≠ e := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    have hd' : ∀ x, (A x : ℤ) * eps (a ⬝ᵥ x) - B x * eps (a ⬝ᵥ x)
        = (k : ℤ) * eps e * eps (x ⬝ᵥ (one1 d + a)) := by
      intro x
      rw [dotProduct_add, eps_add, dotProduct_comm x (one1 d), dotProduct_comm x a]
      obtain ⟨h1, h2⟩ := hAB x
      rw [h1, h2]
      have hs := eps_sq e
      by_cases hx : one1 d ⬝ᵥ x = e
      · rw [if_pos hx, if_pos hx, hx]; push_cast
        linear_combination (-(k : ℤ) * eps (a ⬝ᵥ x)) * hs
      · rw [if_neg hx, if_neg hx]
        have hx' : one1 d ⬝ᵥ x = e + 1 := by
          rcases z2 e with he | he <;> subst he <;>
            rcases z2 (one1 d ⬝ᵥ x) with h | h <;> simp_all <;> decide
        rw [hx', eps_add, eps_one]; push_cast
        linear_combination ((k : ℤ) * eps (a ⬝ᵥ x)) * hs
    have hne : one1 d + a ≠ 0 := by
      intro h; apply ha
      calc a = one1 d + a + one1 d := by rw [add_comm (one1 d) a, add_assoc, vadd_self, add_zero]
        _ = one1 d := by rw [h, zero_add]
    rw [Finset.sum_congr rfl fun x _ => hd' x, ← Finset.mul_sum, sum_eps_dot, if_neg hne,
      mul_zero]
  · intro hfa
    obtain ⟨x, y, hx, hy, hxy⟩ := hfa (one1 d) (one1_ne d hd)
    have key : ∀ z, 0 < A z → one1 d ⬝ᵥ z = e := by
      intro z hz
      by_contra hne
      rw [(hAB z).1, if_neg hne, hHs z hne] at hz
      exact lt_irrefl _ hz
    exact hxy ((key x hx).trans (key y hy).symm)
  · obtain ⟨x0, hx0⟩ := hH
    have px0 : one1 d ⬝ᵥ x0 = e := by
      by_contra hne
      rw [hHs x0 hne] at hx0
      exact lt_irrefl _ hx0
    refine span hd (fun x => 0 < B x) (e + 1) x0 ?_ ?_ ?_
    · rw [px0]; exact fun h => hee e h.symm
    · intro x hx
      have hne : one1 d ⬝ᵥ x ≠ e := by rw [hx]; exact hee e
      show 0 < B x
      rw [(hAB x).2, if_neg hne]
      omega
    · show 0 < B x0
      rw [(hAB x0).2, if_pos px0]
      omega

end PEqualNP.Outside.L_lib_977

open PEqualNP.Outside.L_lib_977 in
theorem PEqualNP.Outside.L_lib_977 : ∀ (d : ℕ) (_ : 0 < d),
  let V := Fin d → ZMod 2
  let ones : V := fun _ => 1
  let parity := fun x : V => dotProduct ones x
  let W := fun (H : V → ℕ) (a : V) =>
    ∑ x : V, (H x : ℤ) * (if dotProduct a x = 0 then (1 : ℤ) else -1)
  let full := fun (H : V → ℕ) => ∀ a : V, a ≠ 0 →
    ∃ x y : V, 0 < H x ∧ 0 < H y ∧ dotProduct a x ≠ dotProduct a y
  ∀ A B : V → ℕ,
    ((∀ a, a ≠ ones → W A a = W B a) ∧ (¬ full A) ∧ full B) ↔
    ∃ (e : ZMod 2) (k : ℕ) (H : V → ℕ),
      0 < k ∧ (∃ x, 0 < H x) ∧ (∀ x, parity x ≠ e → H x = 0) ∧
      ∀ x, A x = H x + (if parity x = e then k else 0) ∧
        B x = H x + (if parity x = e then 0 else k) := by
  intro d hd V ones parity W full A B
  constructor
  · rintro ⟨hW, hA, hB⟩
    have hD : ∀ a, a ≠ one1 d → ∑ x, ((A x : ℤ) - B x) * eps (a ⬝ᵥ x) = 0 := by
      intro a ha
      have h := hW a ha
      simp only [sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr h
    have inv := invert _ hD
    rcases lt_trichotomy ((A 0 : ℤ) - B 0) 0 with hc | hc | hc
    · obtain ⟨H, h1, h2, h3⟩ := core hd A B 1 ((B 0 : ℤ) - A 0).toNat (by omega)
        (fun x hx => by
          have := inv x
          rw [hx, eps_one] at this
          simp only [mul_neg, mul_one] at this
          omega)
        (fun x hx => by
          have := inv x
          rcases z2 (one1 d ⬝ᵥ x) with h | h
          · rw [h, eps_zero, mul_one] at this
            omega
          · exact absurd h hx)
        hA hB
      exact ⟨1, _, H, by omega, h1, h2, h3⟩
    · have hAB : A = B := by
        funext x
        have := inv x
        rw [hc, zero_mul] at this
        omega
      rw [hAB] at hA
      exact absurd hB hA
    · obtain ⟨H, h1, h2, h3⟩ := core hd A B 0 ((A 0 : ℤ) - B 0).toNat (by omega)
        (fun x hx => by
          have := inv x
          rw [hx, eps_zero, mul_one] at this
          omega)
        (fun x hx => by
          have := inv x
          rcases z2 (one1 d ⬝ᵥ x) with h | h
          · exact absurd h hx
          · rw [h, eps_one] at this
            simp only [mul_neg, mul_one] at this
            omega)
        hA hB
      exact ⟨0, _, H, by omega, h1, h2, h3⟩
  · rintro ⟨e, k, H, hk, h1, h2, h3⟩
    exact back hd A B e k H hk h1 h2 h3
