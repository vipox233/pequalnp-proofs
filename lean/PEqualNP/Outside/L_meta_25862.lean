import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25862_aux

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma vec_add_self {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 := by
  funext i
  exact zmod2_add_self (x i)

private lemma vec_add_cancel {k : ℕ} (x y : Fin k → ZMod 2) : x + y + y = x := by
  rw [add_assoc, vec_add_self, add_zero]

end PEqualNP.Outside.L_meta_25862_aux

open PEqualNP.Outside.L_meta_25862_aux

theorem PEqualNP.Outside.L_meta_25862 :
    ∀ (k d s : ℕ) (hk : 0 < k),
      let F := ZMod 2
      let W := Fin k → F
      let ix := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
      let rot := fun (n : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - n % k))
      let mix := fun (x : W) (i : Fin k) =>
        x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))
      let layer := fun (x : W) (i : Fin k) =>
        mix x i + (1 + mix x (ix (i.val + 1))) * mix x (ix (i.val + 2))
      let polar := fun (x y : W) (i : Fin k) =>
        mix x (ix (i.val + 1)) * mix y (ix (i.val + 2)) + mix x (ix (i.val + 2)) * mix y (ix (i.val + 1))
      ∀ (start : ℕ) (feed : ℕ → ℕ) (c : ℕ → W) (shift : Fin s → W),
        let state := fun (sched : ℕ → W) (name key : W) (t : ℕ) =>
          Nat.rec (motive := fun _ => W) (rot start key + name) (fun j x => layer x + rot (feed j) key + sched j) t
        ∀ (n : ℕ) (c' : ℕ → W) (keyOffset : W),
          (∀ j < n, c' j = c j + rot (feed j) keyOffset) →
          let h := c' n - c n + rot (feed n) keyOffset
          ∀ (name : W) (keys : Finset W) (path : ℕ → Fin s → W),
            let fitsPath := fun (sc : ℕ → W) (nm w : W) (pseq : ℕ → Fin s → W) =>
              ∀ j ≤ n + 2, ∀ p,
                state sc nm (w + shift p) j - state sc nm w j = pseq j p
            let newPath := fun (j : ℕ) (p : Fin s) => if j = n + 2 then
              path j p + polar h (path (n + 1) p) else path j p
            ((keys.image (fun w => w + keyOffset)).filter (fun w =>
              fitsPath c' (name + rot start keyOffset) w newPath)) =
              (keys.filter (fun w => fitsPath c name w path)).image (fun w => w + keyOffset) := by
  intro k d s hk
  dsimp only
  let F := ZMod 2
  let W := Fin k → F
  let ix : ℕ → Fin k := fun n => ⟨n % k, Nat.mod_lt _ hk⟩
  let rot : ℕ → W → W := fun n x i => x (ix (i.val + k - n % k))
  let mix : W → W := fun x i => x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))
  let layer : W → W := fun x i => mix x i + (1 + mix x (ix (i.val + 1))) * mix x (ix (i.val + 2))
  let polar : W → W → W := fun x y i =>
    mix x (ix (i.val + 1)) * mix y (ix (i.val + 2)) + mix x (ix (i.val + 2)) * mix y (ix (i.val + 1))
  have hrot_add : ∀ (m : ℕ) (x y : W), rot m (x + y) = rot m x + rot m y := by
    intro m x y; funext i; rfl
  have hmix_add : ∀ (x y : W), mix (x + y) = mix x + mix y := by
    intro x y; funext i
    change (x i + y i) + (x (ix (i.val + d)) + y (ix (i.val + d))) +
        (x (ix (i.val + k - d % k)) + y (ix (i.val + k - d % k))) =
      (x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))) +
        (y i + y (ix (i.val + d)) + y (ix (i.val + k - d % k)))
    ring
  have hmix_add_at : ∀ (x y : W) (j : Fin k), mix (x + y) j = mix x j + mix y j :=
    fun x y j => congrFun (hmix_add x y) j
  have hpolar_id : ∀ (x y h : W),
      layer (x + y + h) - layer (x + h) = (layer (x + y) - layer x) + polar h y := by
    intro x y h
    funext i
    change (mix (x + y + h) i + (1 + mix (x + y + h) (ix (i.val + 1))) * mix (x + y + h) (ix (i.val + 2))) -
        (mix (x + h) i + (1 + mix (x + h) (ix (i.val + 1))) * mix (x + h) (ix (i.val + 2))) =
      ((mix (x + y) i + (1 + mix (x + y) (ix (i.val + 1))) * mix (x + y) (ix (i.val + 2))) -
        (mix x i + (1 + mix x (ix (i.val + 1))) * mix x (ix (i.val + 2)))) +
      (mix h (ix (i.val + 1)) * mix y (ix (i.val + 2)) + mix h (ix (i.val + 2)) * mix y (ix (i.val + 1)))
    simp only [hmix_add_at]
    ring
  intro start feed c shift
  let state : (ℕ → W) → W → W → ℕ → W := fun sched name key t =>
    Nat.rec (motive := fun _ => W) (rot start key + name)
      (fun j x => layer x + rot (feed j) key + sched j) t
  intro n c' keyOffset hc'
  let h : W := c' n - c n + rot (feed n) keyOffset
  intro name keys path
  have hstate_le : ∀ (u : W) (j : ℕ), j ≤ n →
      state c' (name + rot start keyOffset) (u + keyOffset) j = state c name u j := by
    intro u j
    induction j with
    | zero =>
      intro _
      change rot start (u + keyOffset) + (name + rot start keyOffset) = rot start u + name
      rw [hrot_add]
      calc
        rot start u + rot start keyOffset + (name + rot start keyOffset)
          = rot start u + name + (rot start keyOffset + rot start keyOffset) := by abel
        _ = rot start u + name := by rw [vec_add_self, add_zero]
    | succ j ih =>
      intro hj
      have hjlt : j < n := Nat.lt_of_succ_le hj
      have hprev := ih (Nat.le_of_lt hjlt)
      change layer (state c' (name + rot start keyOffset) (u + keyOffset) j) +
          rot (feed j) (u + keyOffset) + c' j =
        layer (state c name u j) + rot (feed j) u + c j
      rw [hprev, hrot_add, hc' j hjlt]
      calc
        layer (state c name u j) + (rot (feed j) u + rot (feed j) keyOffset) +
            (c j + rot (feed j) keyOffset)
          = layer (state c name u j) + rot (feed j) u + c j +
            (rot (feed j) keyOffset + rot (feed j) keyOffset) := by abel
        _ = layer (state c name u j) + rot (feed j) u + c j := by rw [vec_add_self, add_zero]
  have hstate_n1 : ∀ (u : W),
      state c' (name + rot start keyOffset) (u + keyOffset) (n + 1) =
        state c name u (n + 1) + h := by
    intro u
    change layer (state c' (name + rot start keyOffset) (u + keyOffset) n) +
        rot (feed n) (u + keyOffset) + c' n =
      layer (state c name u n) + rot (feed n) u + c n + h
    rw [hstate_le u n le_rfl, hrot_add]
    dsimp only [h]
    abel
  have hdiff_le : ∀ (w : W) (p : Fin s) (j : ℕ), j ≤ n + 1 →
      state c' (name + rot start keyOffset) (w + keyOffset + shift p) j -
        state c' (name + rot start keyOffset) (w + keyOffset) j =
      state c name (w + shift p) j - state c name w j := by
    intro w p j hj
    have hcomm : w + keyOffset + shift p = w + shift p + keyOffset := by abel
    rw [hcomm]
    by_cases hle : j ≤ n
    · rw [hstate_le (w + shift p) j hle, hstate_le w j hle]
    · have heq : j = n + 1 := by omega
      subst heq
      rw [hstate_n1 (w + shift p), hstate_n1 w]
      abel
  have hdiff_n2 : ∀ (w : W) (p : Fin s),
      state c' (name + rot start keyOffset) (w + keyOffset + shift p) (n + 2) -
        state c' (name + rot start keyOffset) (w + keyOffset) (n + 2) =
      (state c name (w + shift p) (n + 2) - state c name w (n + 2)) +
        polar h (state c name (w + shift p) (n + 1) - state c name w (n + 1)) := by
    intro w p
    have hcomm : w + keyOffset + shift p = w + shift p + keyOffset := by abel
    rw [hcomm]
    change (layer (state c' (name + rot start keyOffset) (w + shift p + keyOffset) (n + 1)) +
        rot (feed (n + 1)) (w + shift p + keyOffset) + c' (n + 1)) -
      (layer (state c' (name + rot start keyOffset) (w + keyOffset) (n + 1)) +
        rot (feed (n + 1)) (w + keyOffset) + c' (n + 1)) =
      ((layer (state c name (w + shift p) (n + 1)) +
          rot (feed (n + 1)) (w + shift p) + c (n + 1)) -
        (layer (state c name w (n + 1)) +
          rot (feed (n + 1)) w + c (n + 1))) +
        polar h (state c name (w + shift p) (n + 1) - state c name w (n + 1))
    rw [hstate_n1 (w + shift p), hstate_n1 w]
    simp only [hrot_add]
    set X := state c name w (n + 1)
    set D := state c name (w + shift p) (n + 1) - X
    have hXD : state c name (w + shift p) (n + 1) = X + D := by
      dsimp only [D]; abel
    rw [hXD]
    have hp := hpolar_id X D h
    have h1 :
        (layer (X + D + h) + (rot (feed (n + 1)) w + rot (feed (n + 1)) (shift p) +
          rot (feed (n + 1)) keyOffset) + c' (n + 1)) -
        (layer (X + h) + (rot (feed (n + 1)) w + rot (feed (n + 1)) keyOffset) + c' (n + 1)) =
        (layer (X + D + h) - layer (X + h)) + rot (feed (n + 1)) (shift p) := by
      abel
    have h2 :
        (layer (X + D) + (rot (feed (n + 1)) w + rot (feed (n + 1)) (shift p)) + c (n + 1)) -
        (layer X + rot (feed (n + 1)) w + c (n + 1)) =
        (layer (X + D) - layer X) + rot (feed (n + 1)) (shift p) := by
      abel
    rw [h1, h2, hp]
    abel
  have hfits_iff : ∀ (w : W),
      (∀ j ≤ n + 2, ∀ p,
        state c' (name + rot start keyOffset) (w + keyOffset + shift p) j -
          state c' (name + rot start keyOffset) (w + keyOffset) j =
        if j = n + 2 then path j p + polar h (path (n + 1) p) else path j p) ↔
      (∀ j ≤ n + 2, ∀ p,
        state c name (w + shift p) j - state c name w j = path j p) := by
    intro w
    constructor
    · intro h' j hj p
      by_cases hjeq : j = n + 2
      · subst hjeq
        have hn1 := h' (n + 1) (by omega) p
        have hne1 : n + 1 ≠ n + 2 := by omega
        simp only [hne1, ↓reduceIte] at hn1
        rw [hdiff_le w p (n + 1) le_rfl] at hn1
        have hn2 := h' (n + 2) le_rfl p
        simp only [↓reduceIte] at hn2
        rw [hdiff_n2 w p, hn1] at hn2
        exact add_right_cancel hn2
      · have hhj := h' j hj p
        simp only [hjeq, ↓reduceIte] at hhj
        rw [hdiff_le w p j (by omega)] at hhj
        exact hhj
    · intro h0 j hj p
      by_cases hjeq : j = n + 2
      · subst hjeq
        simp only [↓reduceIte]
        rw [hdiff_n2 w p, h0 (n + 2) le_rfl p, h0 (n + 1) (by omega) p]
      · simp only [hjeq, ↓reduceIte]
        rw [hdiff_le w p j (by omega), h0 j hj p]
  ext v
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hfits⟩
    exact ⟨w, ⟨hw, (hfits_iff w).mp hfits⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hfits⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, (hfits_iff w).mpr hfits⟩
