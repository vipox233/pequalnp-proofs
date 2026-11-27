import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25716_aux

def rot (k : ℕ) (s : ℕ) (w : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 := w (i - (s : ZMod k))

def mix (k : ℕ) (d : ℕ) (w : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 :=
  w (i - (d : ZMod k)) + w i + w (i + (d : ZMod k))

def out (k : ℕ) (d u v : ℕ) (name c x : ZMod k → ZMod 2) (j : ZMod k) : ZMod 2 :=
  let y := mix k d (rot k u x + name)
  y j + (1 + y (j + 1)) * y (j + 2) + rot k v x j + c j

theorem out_add (k : ℕ) (d u v : ℕ) (name c x z : ZMod k → ZMod 2) (j : ZMod k) :
    out k d u v name c (x + z) j = out k d u v name c x j +
      (mix k d (rot k u z) j + rot k v z j + mix k d (rot k u z) (j + 2)
        + mix k d (rot k u x + name) (j + 1) * mix k d (rot k u z) (j + 2)
        + mix k d (rot k u z) (j + 1) * mix k d (rot k u x + name) (j + 2)
        + mix k d (rot k u z) (j + 1) * mix k d (rot k u z) (j + 2)) := by
  have hy : ∀ m, mix k d (rot k u (x + z) + name) m
      = mix k d (rot k u x + name) m + mix k d (rot k u z) m := by
    intro m; simp only [mix, rot, Pi.add_apply]; ring
  have hr : rot k v (x + z) j = rot k v x j + rot k v z j := by simp [rot]
  simp only [out]
  rw [hy, hy, hy, hr]
  ring

theorem ylin (k : ℕ) (d u : ℕ) (name x : ZMod k → ZMod 2) (m : ZMod k) :
    mix k d (rot k u x + name) m = mix k d (rot k u x) m + mix k d (rot k u 0 + name) m := by
  simp only [mix, rot, Pi.add_apply, Pi.zero_apply]; ring

theorem shift (k : ℕ) (d u : ℕ) (w0 : ZMod k → ZMod 2) (j t : ZMod k) :
    mix k d (rot k u (fun i => w0 (i + (u : ZMod k) - j))) (j + t)
      = w0 (t - d) + w0 t + w0 (t + d) := by
  simp only [mix, rot]
  rw [show j + t - (d : ZMod k) - u + u - j = t - d by ring,
    show j + t - (u : ZMod k) + u - j = t by ring,
    show j + t + (d : ZMod k) - u + u - j = t + d by ring]

theorem nz (k : ℕ) [NeZero k] (n : ℕ) (hn : 0 < n) (h : n < k) : ((n : ℕ) : ZMod k) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd hn h0
  omega

theorem base (k : ℕ) [NeZero k] (hk : 4 ≤ k ∨ k = 2) (d : ℕ) (hd : d = 1 ∨ d = 2) :
    (∃ w : ZMod k → ZMod 2, w (1 - d) + w 1 + w (1 + d) = 1 ∧ w (2 - d) + w 2 + w (2 + d) = 0) ∧
    (∃ w : ZMod k → ZMod 2, w (1 - d) + w 1 + w (1 + d) = 0 ∧ w (2 - d) + w 2 + w (2 + d) = 1) := by
  rcases hk with hk | rfl
  · have h1 : (1 : ZMod k) ≠ 0 := by
      have := nz k 1 (by norm_num) (by omega); simpa using this
    have h2 : (2 : ZMod k) ≠ 0 := by
      have := nz k 2 (by norm_num) (by omega); simpa using this
    have h3 : (3 : ZMod k) ≠ 0 := by
      have := nz k 3 (by norm_num) (by omega); simpa using this
    rcases hd with rfl | rfl
    · refine ⟨⟨fun i => if i - 0 = 0 then 1 else 0, ?_⟩, ⟨fun i => if i - 3 = 0 then 1 else 0, ?_⟩⟩
      · norm_num [h1, h2, h3]
      · norm_num [h1, h2, h3]
    · refine ⟨⟨fun i => if i - 1 = 0 then 1 else 0, ?_⟩, ⟨fun i => if i - 2 = 0 then 1 else 0, ?_⟩⟩
      · norm_num [h1, h2, h3]
      · norm_num [h1, h2, h3]
  · rcases hd with rfl | rfl
    · exact ⟨⟨fun i => if i = 1 then 1 else 0, by decide⟩, ⟨fun i => if i = 0 then 1 else 0, by decide⟩⟩
    · exact ⟨⟨fun i => if i = 1 then 1 else 0, by decide⟩, ⟨fun i => if i = 0 then 1 else 0, by decide⟩⟩

theorem hconst (k : ℕ) (hk : k = 1 ∨ k = 3) (d : ℕ) (hd : d = 1 ∨ d = 2) :
    ∀ (w : ZMod k → ZMod 2) (m m' : ZMod k), mix k d w m = mix k d w m' := by
  rcases hk with rfl | rfl
  · intro w m m'
    have : m = m' := by revert m m'; decide
    rw [this]
  · have e : ∀ (w : ZMod 3 → ZMod 2) (m : ZMod 3),
        mix 3 d w m = w 0 + w 1 + w 2 := by
      rcases hd with rfl | rfl
      · unfold mix; decide
      · unfold mix; decide
    intro w m m'
    rw [e, e]

theorem dec1 : ∀ A A1 A2 R N1 N2 : ZMod 2,
    A + R + A2 + N1 * A2 + A1 * N2 + A1 * A2 = 0 →
    A + R + A2 + (1 + N1) * A2 + A1 * N2 + A1 * A2 = 0 →
    A + R + A2 + N1 * A2 + A1 * (1 + N2) + A1 * A2 = 0 → A = R ∧ A1 = 0 ∧ A2 = 0 := by
  decide

theorem dec2 : ∀ A R Y : ZMod 2, A + R + A + Y * A + A * Y + A * A = 0 → A = R := by decide

theorem dec3 : ∀ A Y Y' : ZMod 2, A + A + 0 + Y * 0 + 0 * Y' + 0 * 0 = 0 := by decide

theorem dec4 : ∀ A Y : ZMod 2, A + A + A + Y * A + A * Y + A * A = 0 := by decide

theorem key (k : ℕ) [NeZero k] (d u v : ℕ) (hd : d = 1 ∨ d = 2)
    (name c z : ZMod k → ZMod 2) (j : ZMod k) :
    (∀ x : ZMod k → ZMod 2, out k d u v name c (x + z) j = out k d u v name c x j) ↔
    (mix k d (rot k u z) j = rot k v z j ∧ ((k = 1 ∨ k = 3) ∨
      (mix k d (rot k u z) (j + 1) = 0 ∧ mix k d (rot k u z) (j + 2) = 0))) := by
  have hD : ∀ x, out k d u v name c (x + z) j = out k d u v name c x j ↔
      (mix k d (rot k u z) j + rot k v z j + mix k d (rot k u z) (j + 2)
        + mix k d (rot k u x + name) (j + 1) * mix k d (rot k u z) (j + 2)
        + mix k d (rot k u z) (j + 1) * mix k d (rot k u x + name) (j + 2)
        + mix k d (rot k u z) (j + 1) * mix k d (rot k u z) (j + 2)) = 0 := by
    intro x
    rw [out_add]
    constructor <;> intro h <;> linear_combination h
  simp only [hD]
  constructor
  · intro H
    by_cases hk : k = 1 ∨ k = 3
    · have hc := hconst k hk d hd
      have h0 := H 0
      rw [hc (rot k u z) (j + 1) j, hc (rot k u z) (j + 2) j,
        hc (rot k u 0 + name) (j + 2) (j + 1)] at h0
      exact ⟨dec2 _ _ _ h0, Or.inl hk⟩
    · have hk' : 4 ≤ k ∨ k = 2 := by
        have := NeZero.ne k
        omega
      obtain ⟨⟨w1, a1, b1⟩, ⟨w2, a2, b2⟩⟩ := base k hk' d hd
      have e1 := H (fun i => w1 (i + (u : ZMod k) - j))
      have e2 := H (fun i => w2 (i + (u : ZMod k) - j))
      have e0 := H 0
      rw [ylin k d u name _ (j + 1), ylin k d u name _ (j + 2), shift, shift] at e1 e2
      rw [a1, b1] at e1
      rw [a2, b2] at e2
      have hn : rot k u 0 + name = rot k u 0 + name := rfl
      simp only [zero_add] at e1 e2
      have := dec1 _ _ _ _ _ _ e0 e1 e2
      exact ⟨this.1, Or.inr this.2⟩
  · rintro ⟨hA, hk | ⟨h1, h2⟩⟩ x
    · have hc := hconst k hk d hd
      rw [hc (rot k u z) (j + 1) j, hc (rot k u z) (j + 2) j,
        hc (rot k u x + name) (j + 2) (j + 1), ← hA]
      exact dec4 _ _
    · rw [h1, h2, ← hA]
      exact dec3 _ _ _

end PEqualNP.Outside.L_meta_25716_aux

theorem PEqualNP.Outside.L_meta_25716 : ∀ (k : ℕ) [NeZero k],
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let rot := fun (s : ℕ) (w : V) (i : I) => w (i-(s : I))
  let mix := fun (d : ℕ) (w : V) (i : I) => w (i-(d : I))+w i+w (i+(d : I))
  let out := fun (d u v : ℕ) (name c x : V) (j : I) =>
    let y := mix d (rot u x + name)
    y j + (1+y (j+1))*y (j+2) + rot v x j + c j
  let test := fun (d u v : ℕ) (z : V) (j : I) =>
    let a := mix d (rot u z)
    a j = rot v z j ∧ ((k = 1 ∨ k = 3) ∨ (a (j+1) = 0 ∧ a (j+2) = 0))
  ∀ (row col cr cc z : V) (S T : Finset I),
    (∀ x : V,
      (∀ j ∈ S, out 1 1 0 row cr (x+z) j = out 1 1 0 row cr x j) ∧
      (∀ i ∈ T, out 2 3 4 col cc (x+z) i = out 2 3 4 col cc x i)) ↔
    (∀ j ∈ S, test 1 1 0 z j) ∧ (∀ i ∈ T, test 2 3 4 z i) := by
  intro k _ I B V rot mix out test row col cr cc z S T
  constructor
  · intro H
    exact ⟨fun j hj => (PEqualNP.Outside.L_meta_25716_aux.key k 1 1 0 (Or.inl rfl) row cr z j).1
        (fun x => (H x).1 j hj),
      fun i hi => (PEqualNP.Outside.L_meta_25716_aux.key k 2 3 4 (Or.inr rfl) col cc z i).1
        (fun x => (H x).2 i hi)⟩
  · rintro ⟨h1, h2⟩ x
    exact ⟨fun j hj => (PEqualNP.Outside.L_meta_25716_aux.key k 1 1 0 (Or.inl rfl) row cr z j).2
        (h1 j hj) x,
      fun i hi => (PEqualNP.Outside.L_meta_25716_aux.key k 2 3 4 (Or.inr rfl) col cc z i).2
        (h2 i hi) x⟩
