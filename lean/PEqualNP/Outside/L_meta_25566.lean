import PEqualNP.Defs

-- L-meta-25566: with the all-ones direction the mixed difference is linear in v: it equals the
-- mixed word at places i+1 and i+2 added together. That map commutes with rotation, so it sends U
-- into U, and it kills only constant words (the mix kills only the zero word when k is not a
-- multiple of three), so on U it is one to one, hence onto U.

namespace PEqualNP.Outside.L_meta_25566_aux

-- copied from improve/gen/pfind/ready/prep_L_meta_25538.lean (ix, ix_eq, ix_val, mx, mx_add, kernel)
def ix (k : ℕ) (hk : 0 < k) (a : ℕ) : Fin k := ⟨a % k, Nat.mod_lt _ hk⟩

theorem ix_eq {k : ℕ} (hk : 0 < k) {a b : ℕ} (t1 t2 : ℕ) (h : a + k * t1 = b + k * t2) :
    ix k hk a = ix k hk b := by
  apply Fin.ext
  show a % k = b % k
  have h2 := congrArg (· % k) h
  simp only [Nat.add_mul_mod_self_left] at h2
  exact h2

theorem ix_val {k : ℕ} (hk : 0 < k) (p : Fin k) : ix k hk p.val = p := by
  apply Fin.ext; show p.val % k = p.val; exact Nat.mod_eq_of_lt p.isLt

def mx (k : ℕ) (hk : 0 < k) (d : ℕ) (w : Fin k → Bool) (p : Fin k) : Bool :=
  xor (xor (w p) (w (ix k hk (p.val + d)))) (w (ix k hk (p.val + k - d % k)))

theorem mx_add {k : ℕ} (hk : 0 < k) (d : ℕ) (a b : Fin k → Bool) (p : Fin k) :
    mx k hk d (fun j => xor (a j) (b j)) p = xor (mx k hk d a p) (mx k hk d b p) := by
  unfold mx
  dsimp only
  generalize a p = x1; generalize b p = y1
  generalize a (ix k hk (p.val + d)) = x2; generalize b (ix k hk (p.val + d)) = y2
  generalize a (ix k hk (p.val + k - d % k)) = x3; generalize b (ix k hk (p.val + k - d % k)) = y3
  cases x1 <;> cases y1 <;> cases x2 <;> cases y2 <;> cases x3 <;> cases y3 <;> rfl

theorem kernel {k : ℕ} (hk : 0 < k) (hk3 : k % 3 ≠ 0) (d : ℕ) (w : Fin k → Bool)
    (h : ∀ p, mx k hk d w p = false) : ∀ p, w p = false := by
  have hdk := Nat.mod_lt d hk
  have hdd := Nat.mod_add_div d k
  let W : ℕ → Bool := fun x => w (ix k hk x)
  have hW : ∀ x, xor (xor (W x) (W (x + d))) (W (x + k - d % k)) = false := by
    intro x
    have hx := h (ix k hk x)
    unfold mx at hx
    have hm := Nat.mod_add_div x k
    have e1 : ix k hk ((ix k hk x).val + d) = ix k hk (x + d) :=
      ix_eq hk (x / k) 0 (by show x % k + d + k * (x / k) = x + d + k * 0; omega)
    have e2 : ix k hk ((ix k hk x).val + k - d % k) = ix k hk (x + k - d % k) :=
      ix_eq hk (x / k) 0 (by show x % k + k - d % k + k * (x / k) = x + k - d % k + k * 0; omega)
    rw [e1, e2] at hx
    exact hx
  have hper : ∀ x t, W (x + k * t) = W x := fun x t =>
    congrArg w (ix_eq hk 0 t (by omega))
  have hback : ∀ x, W (x + k - d % k + d) = W x := by
    intro x
    show w _ = w _
    congr 1
    have hm : k * (1 + d / k) = k + k * (d / k) := by rw [Nat.mul_add, Nat.mul_one]
    exact ix_eq hk 0 (1 + d / k) (by rw [hm]; omega)
  have R : ∀ y, xor (xor (W y) (W (y + d))) (W (y + d + d)) = false := by
    intro y
    have hy := hW (y + d)
    rw [show y + d + k - d % k = y + k - d % k + d by omega, hback] at hy
    revert hy
    generalize W y = a; generalize W (y + d) = b; generalize W (y + d + d) = c
    cases a <;> cases b <;> cases c <;> decide
  have R3 : ∀ y, W (y + 3 * d) = W y := by
    intro y
    have h1 := R y
    have h2 := R (y + d)
    rw [show y + d + d + d = y + 3 * d by omega] at h2
    revert h1 h2
    generalize W y = a; generalize W (y + d) = b; generalize W (y + d + d) = c
    generalize W (y + 3 * d) = e
    cases a <;> cases b <;> cases c <;> cases e <;> decide
  have R3t : ∀ t y, W (y + 3 * d * t) = W y := by
    intro t
    induction t with
    | zero => intro y; simp
    | succ t ih =>
      intro y
      rw [show y + 3 * d * (t + 1) = (y + 3 * d * t) + 3 * d by ring, R3, ih]
  obtain ⟨a, m, ham⟩ : ∃ a m : ℕ, 3 * a = k * m + 1 := by
    have : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h1 | h1
    · exact ⟨(2 * k + 1) / 3, 2, by omega⟩
    · exact ⟨(k + 1) / 3, 1, by omega⟩
  have shift : ∀ y, W (y + d) = W y := by
    intro y
    have e : y + 3 * d * a = y + d + k * (d * m) := by
      have : 3 * d * a = d * (3 * a) := by ring
      rw [this, ham]; ring
    rw [← hper (y + d) (d * m), ← e, R3t]
  intro p
  have hp := hW p.val
  have e3 : W (p.val + k - d % k) = W p.val := by
    rw [← shift (p.val + k - d % k), hback]
  rw [shift, e3] at hp
  have : W p.val = w p := congrArg w (ix_val hk p)
  rw [this] at hp
  revert hp; cases w p <;> decide


theorem mx_not {k : ℕ} (hk : 0 < k) (d : ℕ) (w : Fin k → Bool) (p : Fin k) :
    mx k hk d (fun j => !(w j)) p = !(mx k hk d w p) := by
  unfold mx
  dsimp only
  generalize w p = x1; generalize w (ix k hk (p.val + d)) = x2
  generalize w (ix k hk (p.val + k - d % k)) = x3
  cases x1 <;> cases x2 <;> cases x3 <;> rfl

theorem rotN_mem {k : ℕ} (hk : 0 < k) (U : Finset (Fin k → Bool))
    (hrot : ∀ v ∈ U, (fun p : Fin k => v (ix k hk (p.val + 1))) ∈ U) :
    ∀ s, ∀ u ∈ U, (fun p : Fin k => u (ix k hk (p.val + s))) ∈ U := by
  intro s
  induction s with
  | zero =>
    intro u hu
    have : (fun p : Fin k => u (ix k hk (p.val + 0))) = u := by
      funext p; rw [Nat.add_zero, ix_val]
    rw [this]; exact hu
  | succ s ih =>
    intro u hu
    have h := hrot _ (ih u hu)
    have : (fun p : Fin k => (fun q : Fin k => u (ix k hk (q.val + s))) (ix k hk (p.val + 1))) =
        (fun p : Fin k => u (ix k hk (p.val + (s + 1)))) := by
      funext p
      show u _ = u _
      congr 1
      have := Nat.mod_add_div (p.val + 1) k
      exact ix_eq hk ((p.val + 1) / k) 0
        (by show (p.val + 1) % k + s + k * ((p.val + 1) / k) = p.val + (s + 1) + k * 0; omega)
    rw [← this]; exact h

-- the linear map v to (place i, mix v (i+1) xor mix v (i+2))
def L (k : ℕ) (hk : 0 < k) (d : ℕ) (v : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (mx k hk d v (ix k hk (i.val + 1))) (mx k hk d v (ix k hk (i.val + 2)))

theorem L_mem {k : ℕ} (hk : 0 < k) (d : ℕ) (U : Finset (Fin k → Bool))
    (hadd : ∀ a ∈ U, ∀ b ∈ U, (fun j => xor (a j) (b j)) ∈ U)
    (hrot : ∀ v ∈ U, (fun p : Fin k => v (ix k hk (p.val + 1))) ∈ U) :
    ∀ v ∈ U, L k hk d v ∈ U := by
  have hdk := Nat.mod_lt d hk
  intro v hv
  have hm : mx k hk d v = fun p => xor (xor (v p) ((fun q : Fin k => v (ix k hk (q.val + d))) p))
      ((fun q : Fin k => v (ix k hk (q.val + (k - d % k)))) p) := by
    funext p
    unfold mx
    dsimp only
    rw [show p.val + k - d % k = p.val + (k - d % k) by omega]
  have hmU : mx k hk d v ∈ U := by
    rw [hm]
    exact hadd _ (hadd _ hv _ (rotN_mem hk U hrot d v hv)) _ (rotN_mem hk U hrot _ v hv)
  exact hadd _ (rotN_mem hk U hrot 1 _ hmU) _ (rotN_mem hk U hrot 2 _ hmU)

theorem L_add {k : ℕ} (hk : 0 < k) (d : ℕ) (a b : Fin k → Bool) :
    L k hk d (fun j => xor (a j) (b j)) = fun j => xor (L k hk d a j) (L k hk d b j) := by
  funext i
  unfold L
  rw [mx_add, mx_add]
  generalize mx k hk d a (ix k hk (i.val + 1)) = a1
  generalize mx k hk d b (ix k hk (i.val + 1)) = b1
  generalize mx k hk d a (ix k hk (i.val + 2)) = a2
  generalize mx k hk d b (ix k hk (i.val + 2)) = b2
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> rfl

theorem L_zero {k : ℕ} (hk : 0 < k) (hk3 : k % 3 ≠ 0) (d : ℕ) (v : Fin k → Bool)
    (hz : ∀ i, L k hk d v i = false) (hnot : v ≠ fun _ => true) : ∀ p, v p = false := by
  have hstep : ∀ n : ℕ, mx k hk d v (ix k hk (n + 1)) = mx k hk d v (ix k hk n) := by
    intro n
    have h := hz (ix k hk (n + k - 1))
    unfold L at h
    have e1 : ix k hk ((ix k hk (n + k - 1)).val + 1) = ix k hk n := by
      have := Nat.mod_add_div (n + k - 1) k
      exact ix_eq hk ((n + k - 1) / k) 1
        (by show (n + k - 1) % k + 1 + k * ((n + k - 1) / k) = n + k * 1; omega)
    have e2 : ix k hk ((ix k hk (n + k - 1)).val + 2) = ix k hk (n + 1) := by
      have := Nat.mod_add_div (n + k - 1) k
      exact ix_eq hk ((n + k - 1) / k) 1
        (by show (n + k - 1) % k + 2 + k * ((n + k - 1) / k) = n + 1 + k * 1; omega)
    rw [e1, e2] at h
    revert h
    generalize mx k hk d v (ix k hk n) = a1
    generalize mx k hk d v (ix k hk (n + 1)) = a2
    cases a1 <;> cases a2 <;> decide
  have hall : ∀ n : ℕ, mx k hk d v (ix k hk n) = mx k hk d v (ix k hk 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
  obtain ⟨e, he⟩ : ∃ e, mx k hk d v (ix k hk 0) = e := ⟨_, rfl⟩
  rw [he] at hall
  have hw : ∀ p, mx k hk d (fun j => xor (v j) e) p = false := by
    intro p
    have h1 : mx k hk d v p = e := by rw [← ix_val hk p]; exact hall p.val
    unfold mx at h1 ⊢
    dsimp only at h1 ⊢
    revert h1
    generalize v p = x1; generalize v (ix k hk (p.val + d)) = x2
    generalize v (ix k hk (p.val + k - d % k)) = x3
    cases x1 <;> cases x2 <;> cases x3 <;> cases e <;> decide
  have hc := kernel hk hk3 d _ hw
  cases e with
  | false =>
    intro p; have := hc p; revert this; cases v p <;> decide
  | true =>
    exfalso; apply hnot
    funext p; have := hc p; revert this; cases v p <;> decide

end PEqualNP.Outside.L_meta_25566_aux

open PEqualNP.Outside.L_meta_25566_aux in
theorem PEqualNP.Outside.L_meta_25566 :
    ∀ (k : Nat) (hk : 0 < k), k % 3 ≠ 0 →
      let index := fun (a : Nat) => (⟨a % k, Nat.mod_lt _ hk⟩ : Fin k)
      let add := fun (x y : Fin k → Bool) (j : Fin k) => xor (x j) (y j)
      ∀ (U : Finset (Fin k → Bool)),
        (∀ a ∈ U, ∀ b ∈ U, add a b ∈ U) →
        (∀ a ∈ U, (fun slot : Fin k => a (index (slot.val + 1))) ∈ U) →
        (fun _ : Fin k => true) ∉ U →
      ∀ (d : Nat), (d = 1 ∨ d = 2) →
      let mix := fun (word : Fin k → Bool) (p : Fin k) =>
        xor (xor (word p) (word (index (p.val + d))))
          (word (index (p.val + k - d % k)))
      let output := fun (w : Fin k → Bool) (i : Fin k) =>
        let y := mix w
        xor (y i) (!(y (index (i.val + 1))) && y (index (i.val + 2)))
      ∀ (x target : Fin k → Bool),
        let mixed := fun (v : Fin k → Bool) (i : Fin k) =>
          xor (xor (output x i) (output (fun basePos => !(x basePos)) i))
            (xor (output (add x v) i) (output (fun shiftedPos => !((add x v) shiftedPos)) i))
        (U.filter (fun direction => mixed direction = target)).card = if target ∈ U then 1 else 0 := by
  intro k hk hk3 index add U hadd hrot hone d _ mix output x target mixed
  have hmix : ∀ w p, mix w p = mx k hk d w p := fun _ _ => rfl
  -- the mixed difference is the linear map L
  have key : ∀ v, mixed v = L k hk d v := by
    intro v
    funext i
    show xor (xor (xor (mix x i) (!(mix x (index (i.val + 1))) && mix x (index (i.val + 2))))
        (xor (mix (fun p => !(x p)) i) (!(mix (fun p => !(x p)) (index (i.val + 1))) &&
          mix (fun p => !(x p)) (index (i.val + 2)))))
      (xor (xor (mix (add x v) i) (!(mix (add x v) (index (i.val + 1))) && mix (add x v) (index (i.val + 2))))
        (xor (mix (fun p => !(add x v p)) i) (!(mix (fun p => !(add x v p)) (index (i.val + 1))) &&
          mix (fun p => !(add x v p)) (index (i.val + 2))))) = _
    simp only [hmix]
    show xor (xor (xor (mx k hk d x i) (!(mx k hk d x (ix k hk (i.val + 1))) && mx k hk d x (ix k hk (i.val + 2))))
        (xor (mx k hk d (fun p => !(x p)) i) (!(mx k hk d (fun p => !(x p)) (ix k hk (i.val + 1))) &&
          mx k hk d (fun p => !(x p)) (ix k hk (i.val + 2)))))
      (xor (xor (mx k hk d (fun j => xor (x j) (v j)) i) (!(mx k hk d (fun j => xor (x j) (v j)) (ix k hk (i.val + 1))) && mx k hk d (fun j => xor (x j) (v j)) (ix k hk (i.val + 2))))
        (xor (mx k hk d (fun p => !((fun j => xor (x j) (v j)) p)) i) (!(mx k hk d (fun p => !((fun j => xor (x j) (v j)) p)) (ix k hk (i.val + 1))) &&
          mx k hk d (fun p => !((fun j => xor (x j) (v j)) p)) (ix k hk (i.val + 2))))) =
      xor (mx k hk d v (ix k hk (i.val + 1))) (mx k hk d v (ix k hk (i.val + 2)))
    simp only [mx_not, mx_add]
    generalize mx k hk d x i = x0; generalize mx k hk d v i = v0
    generalize mx k hk d x (ix k hk (i.val + 1)) = x1
    generalize mx k hk d v (ix k hk (i.val + 1)) = v1
    generalize mx k hk d x (ix k hk (i.val + 2)) = x2
    generalize mx k hk d v (ix k hk (i.val + 2)) = v2
    revert x0 v0 x1 v1 x2 v2
    decide
  rw [Finset.filter_congr (fun v _ => by rw [key v])]
  have hLU := L_mem hk d U hadd hrot
  have hinj : Set.InjOn (L k hk d) U := by
    intro a ha b hb hab
    have hz : ∀ i, L k hk d (fun j => xor (a j) (b j)) i = false := by
      intro i; rw [L_add]; dsimp only; rw [hab]; cases L k hk d b i <;> rfl
    have hne : (fun j => xor (a j) (b j)) ≠ fun _ => true := by
      intro h; apply hone; rw [← h]; exact hadd a ha b hb
    have h0 := L_zero hk hk3 d _ hz hne
    funext j
    have := h0 j; revert this; cases a j <;> cases b j <;> decide
  by_cases ht : target ∈ U
  · rw [if_pos ht]
    have himg : U.image (L k hk d) = U := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨v, hv, rfl⟩ := hy
        exact hLU v hv
      · rw [Finset.card_image_of_injOn hinj]
    have hy : target ∈ U.image (L k hk d) := by rw [himg]; exact ht
    rw [Finset.mem_image] at hy
    obtain ⟨v0, hv0, hv0t⟩ := hy
    rw [Finset.card_eq_one]
    refine ⟨v0, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hvt⟩
      exact hinj hv hv0 (hvt.trans hv0t.symm)
    · rintro rfl
      exact ⟨hv0, hv0t⟩
  · rw [if_neg ht, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    intro v hv hvt
    exact ht (hvt ▸ hLU v hv)
