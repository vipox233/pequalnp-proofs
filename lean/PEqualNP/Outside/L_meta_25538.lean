import PEqualNP.Defs

-- L-meta-25538: the linear part cancels in the mixed difference, which equals A(u)B(v) xor A(v)B(u)
-- with A, B the mixed word at places i+1 and i+2. The mix kills only the zero word (k not a multiple
-- of three), so on a rotation-closed space with a nonconstant word the pair (A, B) takes all four
-- values on equal fibers; six of the sixteen value pairs give one.

namespace PEqualNP.Outside.L_meta_25538_aux

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

theorem mx_rot {k : ℕ} (hk : 0 < k) (d : ℕ) (u : Fin k → Bool) (s : ℕ) (p : Fin k) :
    mx k hk d (fun q => u (ix k hk (q.val + s))) p = mx k hk d u (ix k hk (p.val + s)) := by
  have hdk := Nat.mod_lt d hk
  unfold mx
  dsimp only
  have h1 := Nat.mod_add_div (p.val + d) k
  have h2 := Nat.mod_add_div (p.val + s) k
  have h3 := Nat.mod_add_div (p.val + k - d % k) k
  have e2 : ix k hk ((ix k hk (p.val + d)).val + s) = ix k hk ((ix k hk (p.val + s)).val + d) :=
    ix_eq hk ((p.val + d) / k) ((p.val + s) / k)
      (by show (p.val + d) % k + s + k * ((p.val + d) / k) = (p.val + s) % k + d + k * ((p.val + s) / k)
          omega)
  have e3 : ix k hk ((ix k hk (p.val + k - d % k)).val + s) =
      ix k hk ((ix k hk (p.val + s)).val + k - d % k) :=
    ix_eq hk ((p.val + k - d % k) / k) ((p.val + s) / k)
      (by show (p.val + k - d % k) % k + s + k * ((p.val + k - d % k) / k) =
            (p.val + s) % k + k - d % k + k * ((p.val + s) / k)
          omega)
  rw [e2, e3]

theorem reach {k : ℕ} (hk : 0 < k) (c : ℕ) (p : Fin k) : ∃ s, ix k hk (c + s) = p := by
  refine ⟨p.val + k - c % k, ?_⟩
  have hc := Nat.mod_add_div c k
  have hck := Nat.mod_lt c hk
  have hm : k * (c / k + 1) = k * (c / k) + k := by rw [Nat.mul_add, Nat.mul_one]
  exact (ix_eq hk 0 (c / k + 1) (by rw [hm]; omega)).trans (ix_val hk p)

theorem surj {k : ℕ} (hk : 0 < k) (hk3 : k % 3 ≠ 0) (d : ℕ) (U : Finset (Fin k → Bool))
    (hadd : ∀ a ∈ U, ∀ b ∈ U, (fun j => xor (a j) (b j)) ∈ U)
    (hrot : ∀ v ∈ U, (fun p : Fin k => v (ix k hk (p.val + 1))) ∈ U)
    (hnc : ∃ v ∈ U, ∃ p q, v p ≠ v q) (c : ℕ) :
    ∀ j : Bool × Bool, ∃ z ∈ U, (mx k hk d z (ix k hk c), mx k hk d z (ix k hk (c + 1))) = j := by
  have hrN : ∀ s, ∀ u ∈ U, (fun p : Fin k => u (ix k hk (p.val + s))) ∈ U := by
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
  -- every value at any place is a value at place c of a rotated word
  have atc : ∀ c' : ℕ, ∀ u ∈ U, ∀ p : Fin k, ∃ v ∈ U,
      mx k hk d u p = mx k hk d v (ix k hk c') ∧
      mx k hk d u (ix k hk (p.val + 1)) = mx k hk d v (ix k hk (c' + 1)) := by
    intro c' u hu p
    obtain ⟨s, hs⟩ := reach hk c' p
    refine ⟨_, hrN s u hu, ?_, ?_⟩
    · rw [mx_rot]
      congr 1
      rw [← hs]
      have := Nat.mod_add_div c' k
      exact ix_eq hk 0 (c' / k) (by show c' + s + k * 0 = c' % k + s + k * (c' / k); omega)
    · rw [mx_rot]
      congr 1
      have h1 := Nat.mod_add_div (c' + 1) k
      have h2 := Nat.mod_add_div (c' + s) k
      rw [← hs]
      exact ix_eq hk ((c' + s) / k) ((c' + 1) / k)
        (by show (c' + s) % k + 1 + k * ((c' + s) / k) = (c' + 1) % k + s + k * ((c' + 1) / k)
            omega)
  obtain ⟨v0, hv0, p0, q0, hpq⟩ := hnc
  -- a place where some word has mix value true
  have someA : ∀ c' : ℕ, ∃ z ∈ U, mx k hk d z (ix k hk c') = true := by
    intro c'
    by_contra hne
    push_neg at hne
    have hz : ∀ u ∈ U, ∀ p, mx k hk d u p = false := by
      intro u hu p
      obtain ⟨v, hv, h1, _⟩ := atc c' u hu p
      rw [h1]; simpa using hne v hv
    have := kernel hk hk3 d v0 (hz v0 hv0)
    exact hpq (by rw [this p0, this q0])
  have someAB : ∃ z ∈ U, mx k hk d z (ix k hk c) ≠ mx k hk d z (ix k hk (c + 1)) := by
    by_contra hne
    push_neg at hne
    have hstep : ∀ p : Fin k, mx k hk d v0 p = mx k hk d v0 (ix k hk (p.val + 1)) := by
      intro p
      obtain ⟨v, hv, h1, h2⟩ := atc c v0 hv0 p
      rw [h1, h2]; exact hne v hv
    have hall : ∀ n : ℕ, mx k hk d v0 (ix k hk n) = mx k hk d v0 (ix k hk 0) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [← ih, hstep (ix k hk n)]
        congr 1
        have := Nat.mod_add_div n k
        exact ix_eq hk 0 (n / k)
          (by show n + 1 + k * 0 = n % k + 1 + k * (n / k); omega)
    obtain ⟨e, he⟩ : ∃ e, mx k hk d v0 (ix k hk 0) = e := ⟨_, rfl⟩
    rw [he] at hall
    have hz : ∀ p, mx k hk d (fun j => xor (v0 j) e) p = false := by
      intro p
      have h1 : mx k hk d v0 p = e := by rw [← ix_val hk p]; exact hall p.val
      unfold mx at h1 ⊢
      dsimp only at h1 ⊢
      revert h1
      generalize v0 p = x1; generalize v0 (ix k hk (p.val + d)) = x2
      generalize v0 (ix k hk (p.val + k - d % k)) = x3
      cases x1 <;> cases x2 <;> cases x3 <;> cases e <;> decide
    have := kernel hk hk3 d _ hz
    have a1 := this p0
    have a2 := this q0
    apply hpq
    revert a1 a2
    cases v0 p0 <;> cases v0 q0 <;> cases e <;> decide
  obtain ⟨u1, hu1, h1⟩ := someA c
  obtain ⟨u2, hu2, h2⟩ := someA (c + 1)
  obtain ⟨u3, hu3, h3⟩ := someAB
  have lin : ∀ a b p, mx k hk d (fun j => xor (a j) (b j)) p = xor (mx k hk d a p) (mx k hk d b p) :=
    fun a b p => mx_add hk d a b p
  intro j
  obtain ⟨ja, jb⟩ := j
  have z0 := hadd u1 hu1 u1 hu1
  have z12 := hadd u1 hu1 u2 hu2
  have z13 := hadd u1 hu1 u3 hu3
  have z23 := hadd u2 hu2 u3 hu3
  revert h3
  generalize ea1 : mx k hk d u1 (ix k hk c) = a1 at h1
  generalize eb1 : mx k hk d u1 (ix k hk (c + 1)) = b1
  generalize ea2 : mx k hk d u2 (ix k hk c) = a2
  generalize eb2 : mx k hk d u2 (ix k hk (c + 1)) = b2 at h2
  generalize ea3 : mx k hk d u3 (ix k hk c) = a3
  generalize eb3 : mx k hk d u3 (ix k hk (c + 1)) = b3
  intro h3
  subst h1 h2
  cases ja <;> cases jb <;> cases b1 <;> cases a2 <;> cases a3 <;> cases b3 <;>
    simp at h3 <;>
    first
    | (refine ⟨_, z0, ?_⟩; rw [lin, lin, ea1, eb1]; rfl)
    | (refine ⟨_, hu1, ?_⟩; simp [ea1, eb1]; done)
    | (refine ⟨_, hu2, ?_⟩; simp [ea2, eb2]; done)
    | (refine ⟨_, hu3, ?_⟩; simp [ea3, eb3]; done)
    | (refine ⟨_, z12, ?_⟩; simp [lin, ea1, eb1, ea2, eb2]; done)
    | (refine ⟨_, z13, ?_⟩; simp [lin, ea1, eb1, ea3, eb3]; done)
    | (refine ⟨_, z23, ?_⟩; simp [lin, ea2, eb2, ea3, eb3]; done)

theorem expand {α : Type} (S : Finset α) (A B : α → Bool) (f : Bool × Bool → ℕ) :
    ∑ x ∈ S, f (A x, B x) = ∑ j : Bool × Bool, (S.filter (fun x => (A x, B x) = j)).card * f j := by
  rw [← Finset.sum_fiberwise S (fun x => (A x, B x)) (fun x => f (A x, B x))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_congr rfl (g := fun _ => f j) (by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2])]
  rw [Finset.sum_const, smul_eq_mul]

theorem fibeq {α : Type} [DecidableEq α] (S : Finset α) (A B : α → Bool) (op : α → α → α)
    (hop : ∀ a ∈ S, ∀ b ∈ S, op a b ∈ S) (hinv : ∀ a b, op (op a b) b = a)
    (hA : ∀ a b, A (op a b) = xor (A a) (A b)) (hB : ∀ a b, B (op a b) = xor (B a) (B b))
    (hsurj : ∀ j : Bool × Bool, ∃ z ∈ S, (A z, B z) = j) :
    ∀ j, 4 * (S.filter (fun x => (A x, B x) = j)).card = S.card := by
  have same : ∀ j, (S.filter (fun x => (A x, B x) = j)).card =
      (S.filter (fun x => (A x, B x) = (false, false))).card := by
    intro j
    obtain ⟨z, hz, hzj⟩ := hsurj j
    symm
    apply Finset.card_nbij' (fun x => op x z) (fun x => op x z)
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hop x hx.1 z hz, ?_⟩
      rw [hA, hB, ← hzj]
      have := hx.2
      simp only [Prod.mk.injEq] at this ⊢
      rw [this.1, this.2]; simp
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hop x hx.1 z hz, ?_⟩
      rw [hA, hB]
      have := hx.2
      rw [← hzj] at this
      simp only [Prod.mk.injEq] at this ⊢
      rw [this.1, this.2]; simp
    · intro x _; exact hinv x z
    · intro x _; exact hinv x z
  have tot := expand S A B (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Fintype.sum_prod_type, Fintype.sum_bool] at tot
  intro j
  rw [same j]
  rw [same (true, true), same (true, false), same (false, true)] at tot
  simp only [Finset.card_eq_sum_ones] at tot ⊢
  omega

theorem count4 {α : Type} (S : Finset α) (A B : α → Bool)
    (hfib : ∀ j, 4 * (S.filter (fun x => (A x, B x) = j)).card = S.card) (f : Bool × Bool → ℕ) :
    4 * ∑ x ∈ S, f (A x, B x) = S.card * ∑ j : Bool × Bool, f j := by
  rw [expand, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Nat.mul_assoc, hfib]

end PEqualNP.Outside.L_meta_25538_aux

open PEqualNP.Outside.L_meta_25538_aux in
theorem PEqualNP.Outside.L_meta_25538 :
    ∀ (k : Nat) (hk : 0 < k), k % 3 ≠ 0 →
      let index := fun (a : Nat) => (⟨a % k, Nat.mod_lt _ hk⟩ : Fin k)
      let add := fun (x y : Fin k → Bool) (j : Fin k) => xor (x j) (y j)
      let stable := fun (S : Finset (Fin k → Bool)) =>
        (∀ a ∈ S, ∀ b ∈ S, add a b ∈ S) ∧
        (∀ v ∈ S, (fun p : Fin k => v (index (p.val + 1))) ∈ S) ∧
        ∃ v ∈ S, ∃ p q, v p ≠ v q
      ∀ (U V : Finset (Fin k → Bool)), stable U → stable V →
      ∀ (d : Nat), (d = 1 ∨ d = 2) →
      let mix := fun (word : Fin k → Bool) (pos : Fin k) =>
        xor (xor (word pos) (word (index (pos.val + d))))
          (word (index (pos.val + k - d % k)))
      let output := fun (base : Fin k → Bool) (i : Fin k) =>
        let y := mix base
        xor (y i) (!(y (index (i.val + 1))) && y (index (i.val + 2)))
      ∀ (x : Fin k → Bool) (i : Fin k),
        8 * ((U.product V).filter (fun pair =>
          xor (xor (output x i) (output (add x pair.1) i))
            (xor (output (add x pair.2) i) (output (add (add x pair.1) pair.2) i)))).card =
          3 * U.card * V.card := by
  intro k hk hk3 index add stable U V hU hV d _ mix output x i
  obtain ⟨hUa, hUr, hUn⟩ := hU
  obtain ⟨hVa, hVr, hVn⟩ := hV
  have hmix : ∀ w p, mix w p = mx k hk d w p := fun _ _ => rfl
  let A : (Fin k → Bool) → Bool := fun u => mx k hk d u (ix k hk (i.val + 1))
  let B : (Fin k → Bool) → Bool := fun u => mx k hk d u (ix k hk (i.val + 1 + 1))
  have key : ∀ u v : Fin k → Bool,
      xor (xor (output x i) (output (add x u) i))
        (xor (output (add x v) i) (output (add (add x u) v) i)) =
      xor (A u && B v) (A v && B u) := by
    intro u v
    show xor (xor (xor (mix x i) (!(mix x (index (i.val + 1))) && mix x (index (i.val + 2))))
        (xor (mix (add x u) i) (!(mix (add x u) (index (i.val + 1))) && mix (add x u) (index (i.val + 2)))))
      (xor (xor (mix (add x v) i) (!(mix (add x v) (index (i.val + 1))) && mix (add x v) (index (i.val + 2))))
        (xor (mix (add (add x u) v) i)
          (!(mix (add (add x u) v) (index (i.val + 1))) && mix (add (add x u) v) (index (i.val + 2))))) = _
    simp only [hmix]
    show xor (xor (xor (mx k hk d x i) (!(mx k hk d x (ix k hk (i.val + 1))) && mx k hk d x (ix k hk (i.val + 1 + 1))))
        (xor (mx k hk d (fun j => xor (x j) (u j)) i) (!(mx k hk d (fun j => xor (x j) (u j)) (ix k hk (i.val + 1))) && mx k hk d (fun j => xor (x j) (u j)) (ix k hk (i.val + 1 + 1)))))
      (xor (xor (mx k hk d (fun j => xor (x j) (v j)) i) (!(mx k hk d (fun j => xor (x j) (v j)) (ix k hk (i.val + 1))) && mx k hk d (fun j => xor (x j) (v j)) (ix k hk (i.val + 1 + 1))))
        (xor (mx k hk d (fun j => xor ((fun j => xor (x j) (u j)) j) (v j)) i)
          (!(mx k hk d (fun j => xor ((fun j => xor (x j) (u j)) j) (v j)) (ix k hk (i.val + 1))) && mx k hk d (fun j => xor ((fun j => xor (x j) (u j)) j) (v j)) (ix k hk (i.val + 1 + 1))))) =
      xor (mx k hk d u (ix k hk (i.val + 1)) && mx k hk d v (ix k hk (i.val + 1 + 1)))
        (mx k hk d v (ix k hk (i.val + 1)) && mx k hk d u (ix k hk (i.val + 1 + 1)))
    simp only [mx_add]
    generalize mx k hk d x i = x0; generalize mx k hk d u i = u0; generalize mx k hk d v i = v0
    generalize mx k hk d x (ix k hk (i.val + 1)) = x1
    generalize mx k hk d u (ix k hk (i.val + 1)) = u1
    generalize mx k hk d v (ix k hk (i.val + 1)) = v1
    generalize mx k hk d x (ix k hk (i.val + 1 + 1)) = x2
    generalize mx k hk d u (ix k hk (i.val + 1 + 1)) = u2
    generalize mx k hk d v (ix k hk (i.val + 1 + 1)) = v2
    revert x0 u0 v0 x1 u1 v1 x2 u2 v2
    decide
  let F : Bool × Bool → Bool × Bool → ℕ := fun j1 j2 =>
    if xor (j1.1 && j2.2) (j2.1 && j1.2) = true then 1 else 0
  have hAop : ∀ a b, A (fun j => xor (a j) (b j)) = xor (A a) (A b) := fun a b => mx_add hk d a b _
  have hBop : ∀ a b, B (fun j => xor (a j) (b j)) = xor (B a) (B b) := fun a b => mx_add hk d a b _
  have hinv : ∀ a b : Fin k → Bool, (fun j => xor ((fun j => xor (a j) (b j)) j) (b j)) = a := by
    intro a b; funext j; simp
  have fibU := fibeq U A B (fun a b j => xor (a j) (b j)) hUa hinv hAop hBop
    (surj hk hk3 d U hUa hUr hUn (i.val + 1))
  have fibV := fibeq V A B (fun a b j => xor (a j) (b j)) hVa hinv hAop hBop
    (surj hk hk3 d V hVa hVr hVn (i.val + 1))
  have hcard : ((U.product V).filter (fun pair =>
          xor (xor (output x i) (output (add x pair.1) i))
            (xor (output (add x pair.2) i) (output (add (add x pair.1) pair.2) i)))).card =
      ∑ u ∈ U, ∑ v ∈ V, F (A u, B u) (A v, B v) := by
    rw [Finset.card_filter, show U.product V = U ×ˢ V from rfl, Finset.sum_product]
    apply Finset.sum_congr rfl; intro u _
    apply Finset.sum_congr rfl; intro v _
    simp only [key, F]
  have inner : ∀ u, 4 * ∑ v ∈ V, F (A u, B u) (A v, B v) = V.card * ∑ j, F (A u, B u) j :=
    fun u => count4 V A B fibV (F (A u, B u))
  have outer := count4 U A B fibU (fun j1 => ∑ j, F j1 j)
  have six : ∑ j1 : Bool × Bool, ∑ j : Bool × Bool, F j1 j = 6 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, F]; decide
  rw [hcard]
  have h16 : 16 * ∑ u ∈ U, ∑ v ∈ V, F (A u, B u) (A v, B v) = 6 * (U.card * V.card) := by
    rw [show 16 = 4 * 4 from rfl, Nat.mul_assoc, Finset.mul_sum]
    simp only [inner]
    rw [← Finset.mul_sum, Nat.mul_left_comm, outer, six]
    ring
  rw [Nat.mul_assoc]
  generalize ∑ u ∈ U, ∑ v ∈ V, F (A u, B u) (A v, B v) = N at h16 ⊢
  generalize U.card * V.card = M at h16 ⊢
  omega
