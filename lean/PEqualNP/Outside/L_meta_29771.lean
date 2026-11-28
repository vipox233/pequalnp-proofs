import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29771

noncomputable section

open Classical

abbrev F := ZMod 2
abbrev W (k : ℕ) := Fin k → F
abbrev D (k : ℕ) := W k →ₗ[F] F

lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (a : F) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma zmod2_mul_self (a : F) : a * a = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_two : (2 : F) = 0 := by decide

def ix {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def rot {k : ℕ} (hk : 0 < k) (s : ℕ) (x : W k) (i : Fin k) : F :=
  x (ix hk (i.val + k - s % k))

def mix {k : ℕ} (hk : 0 < k) (g : ℕ) (x : W k) (i : Fin k) : F :=
  x i + x (ix hk (i.val + g)) + x (ix hk (i.val + k - g % k))

def step {k : ℕ} (hk : 0 < k) (x : W k) (i : Fin k) : F :=
  x i + (1 + x (ix hk (i.val + 1))) * x (ix hk (i.val + 2))

def gap (b : Bool) : ℕ := if b then 2 else 1

def spin (b : Bool) : ℕ := if b then 3 else 1

def out {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → W k) (x : W k) (b : Bool) : W k :=
  let z := mix hk (gap b) (rot hk (spin b) x + name b)
  let y := step hk z + rot hk (if b then 4 else 0) x + c₁ b
  step hk (mix hk (gap b) y) + rot hk (if b then 7 else 2) x + c₂ b

def bag {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) : Finset (Fin k) :=
  (Finset.range (if b then 11 else 7)).image (fun r =>
    ix hk (i.val + k - (if b then 5 else 1) % k + r))

def run {k d : ℕ} (ask : Fin d → ℕ → D k) (x : W k) : ℕ :=
  (List.finRange d).foldl (fun h j =>
    2 * h + (if ask j h x = 0 then 0 else 1)) 0

lemma ix_val {k : ℕ} (hk : 0 < k) (i : Fin k) : ix hk i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

lemma ix_add_left {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  apply Fin.ext
  dsimp [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_add_k {k : ℕ} (hk : 0 < k) (a : ℕ) : ix hk (a + k) = ix hk a := by
  apply Fin.ext
  dsimp [ix]
  exact Nat.add_mod_right a k

lemma ix_sub_eq_add {k : ℕ} (hk : 0 < k) (a b : ℕ) (hb : b ≤ k) :
    ix hk (a + k - b) = ix hk (a + (k - b)) := by
  apply Fin.ext
  dsimp [ix]
  congr 1
  omega

lemma ix_add_sub_mod {k : ℕ} (hk : 0 < k) (a b : ℕ) (hb : b ≤ k) :
    ix hk ((ix hk a).val + k - b) = ix hk (a + (k - b)) := by
  rw [ix_sub_eq_add hk _ b hb, ix_add_left]

lemma ix_add_sub_cancel {k : ℕ} (hk : 0 < k) (a b : ℕ) (hb : b ≤ k) :
    ix hk (a + (k - b) + b) = ix hk a := by
  have : a + (k - b) + b = a + k := by omega
  rw [this, ix_add_k]

lemma ix_shift_sub_cancel {k : ℕ} (hk : 0 < k) (a b : ℕ) (hb : b < k) :
    ix hk ((ix hk (a + b)).val + k - b) = ix hk a := by
  rw [ix_add_sub_mod hk (a + b) b (le_of_lt hb)]
  have : a + b + (k - b) = a + k := by omega
  rw [this, ix_add_k]

lemma ix_ne_of_add {k : ℕ} (hk : 0 < k) (a d : ℕ) (hd0 : 0 < d) (hdk : d < k) :
    ix hk (a + d) ≠ ix hk a := by
  intro h
  have hm : (a + d) % k = a % k := congrArg Fin.val h
  have h1 : (a % k + d) % k = a % k := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hm]
  have ha : a % k < k := Nat.mod_lt a hk
  by_cases hlt : a % k + d < k
  · rw [Nat.mod_eq_of_lt hlt] at h1; omega
  · have hlt2 : a % k + d - k < k := by omega
    have h2 : (a % k + d) % k = a % k + d - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
    rw [h2] at h1; omega

lemma ix_eq_iff_of_lt {k : ℕ} (hk : 0 < k) (a r1 r2 : ℕ) (h1 : r1 < k) (h2 : r2 < k) :
    ix hk (a + r1) = ix hk (a + r2) ↔ r1 = r2 := by
  constructor
  · intro heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub : a + r2 = (a + r1) + (r2 - r1) := by omega
      rw [hsub] at heq
      exact ix_ne_of_add hk (a + r1) (r2 - r1) (by omega) (by omega) heq.symm
    · have hsub : a + r1 = (a + r2) + (r1 - r2) := by omega
      rw [hsub] at heq
      exact ix_ne_of_add hk (a + r2) (r1 - r2) (by omega) (by omega) heq
  · intro h; subst h; rfl

lemma rot_add {k : ℕ} (hk : 0 < k) (s : ℕ) (x y : W k) :
    rot hk s (x + y) = rot hk s x + rot hk s y := by
  funext i; rfl

lemma mix_add {k : ℕ} (hk : 0 < k) (g : ℕ) (x y : W k) :
    mix hk g (x + y) = mix hk g x + mix hk g y := by
  funext i; simp only [mix, Pi.add_apply]; ring

lemma rot_zero {k : ℕ} (hk : 0 < k) (s : ℕ) : rot hk s (0 : W k) = 0 := by
  funext i; rfl

lemma mix_zero {k : ℕ} (hk : 0 < k) (g : ℕ) : mix hk g (0 : W k) = 0 := by
  funext i; simp [mix]

def diff {α : Type*} [AddCommGroup α] (f : α → F) (u x : α) : F :=
  f (x + u) - f x

def fourth {α : Type*} [AddCommGroup α] (f : α → F) (v : Fin 4 → α) : α → F :=
  (List.ofFn v).foldl diff f

def cubic {α : Type*} [AddCommGroup α] (f : α → F) : Prop :=
  ∀ v x, fourth f v x = 0

lemma diff_eq_add {α : Type*} [AddCommGroup α] (f : α → F) (u x : α) :
    diff f u x = f (x + u) + f x :=
  zmod2_sub_eq_add _ _

lemma diff_add {α : Type*} [AddCommGroup α] (f g : α → F) (u : α) :
    diff (fun x => f x + g x) u = fun x => diff f u x + diff g u x := by
  funext x
  simp only [diff_eq_add]; ring

lemma diff_const {α : Type*} [AddCommGroup α] (c : F) (u : α) :
    diff (fun _ => c) u = fun _ => 0 := by
  funext x
  simp only [diff_eq_add, zmod2_add_self]

lemma diff_mul {α : Type*} [AddCommGroup α] (f g : α → F) (u : α) :
    diff (fun x => f x * g x) u =
      fun x => diff f u x * g x + f x * diff g u x + diff f u x * diff g u x := by
  funext x
  simp only [diff_eq_add]
  have h1 : (f (x + u) + f x) * g x + f x * (g (x + u) + g x) + (f (x + u) + f x) * (g (x + u) + g x) =
      f (x + u) * g (x + u) + f x * g x + (f (x + u) * g x + f (x + u) * g x) +
      (f x * g (x + u) + f x * g (x + u)) + (f x * g x + f x * g x) := by ring
  rw [h1, zmod2_add_self, zmod2_add_self, zmod2_add_self, add_zero, add_zero, add_zero]

lemma fourth_eq_iter {α : Type*} [AddCommGroup α] (f : α → F) (v : Fin 4 → α) (x : α) :
    fourth f v x = diff (diff (diff (diff f (v 0)) (v 1)) (v 2)) (v 3) x := by
  simp [fourth, List.ofFn_succ]

lemma fourth_add {α : Type*} [AddCommGroup α] (f g : α → F) (v : Fin 4 → α) (x : α) :
    fourth (fun y => f y + g y) v x = fourth f v x + fourth g v x := by
  rw [fourth_eq_iter, fourth_eq_iter, fourth_eq_iter]
  simp only [diff_add]

lemma fourth_comp_affine {α β : Type*} [AddCommGroup α] [AddCommGroup β]
    (f : β → F) (L : α → β) (L0 : α → β) (hL : ∀ x u, L (x + u) = L x + L0 u)
    (v : Fin 4 → α) (x : α) :
    fourth (fun y => f (L y)) v x = fourth f (fun r => L0 (v r)) (L x) := by
  have hstep : ∀ (g : β → F) (u : α), diff (fun y => g (L y)) u = fun y => diff g (L0 u) (L y) := by
    intro g u; funext y; simp only [diff, hL]
  rw [fourth_eq_iter, fourth_eq_iter]
  simp only [hstep]

def cubePt {α : Type*} [AddCommGroup α] (x : α) (v : Fin 4 → α) (b : Fin 4 → Bool) : α :=
  x + (if b 0 then v 0 else 0) + (if b 1 then v 1 else 0) +
    (if b 2 then v 2 else 0) + (if b 3 then v 3 else 0)

lemma fourth_eq_sum16 {α : Type*} [AddCommGroup α] (f : α → F) (v : Fin 4 → α) (x : α) :
    fourth f v x = ∑ b : Fin 4 → Bool, f (cubePt x v b) := by
  rw [fourth_eq_iter]
  simp only [diff_eq_add]
  have heq : (∑ b : Fin 4 → Bool, f (cubePt x v b)) =
      ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
        f (x + (if b0 then v 0 else 0) + (if b1 then v 1 else 0) +
          (if b2 then v 2 else 0) + (if b3 then v 3 else 0)) := by
    let e : (Fin 4 → Bool) ≃ Bool × Bool × Bool × Bool :=
      { toFun := fun b => (b 0, b 1, b 2, b 3)
        invFun := fun p r =>
          match r.val with
          | 0 => p.1
          | 1 => p.2.1
          | 2 => p.2.2.1
          | _ => p.2.2.2
        left_inv := fun b => by funext r; fin_cases r <;> rfl
        right_inv := fun ⟨_, _, _, _⟩ => rfl }
    rw [Fintype.sum_equiv e (fun b => f (cubePt x v b)) (fun p =>
      f (x + (if p.1 then v 0 else 0) + (if p.2.1 then v 1 else 0) +
        (if p.2.2.1 then v 2 else 0) + (if p.2.2.2 then v 3 else 0))) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro b0 _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro b1 _
    rw [Fintype.sum_prod_type]
  rw [heq]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, add_zero]
  have h1 : ∀ a b c d : α, a + b + c + d = a + c + b + d := fun a b c d => by abel
  have h2 : ∀ a b c : α, a + b + c = a + c + b := fun a b c => by abel
  have h3 : ∀ a b : α, a + b = b + a := fun a b => by abel
  have hc0 : x + v 3 + v 2 + v 1 + v 0 = x + v 0 + v 1 + v 2 + v 3 := by abel
  have hc1 : x + v 3 + v 2 + v 1 = x + v 1 + v 2 + v 3 := by abel
  have hc2 : x + v 3 + v 2 + v 0 = x + v 0 + v 2 + v 3 := by abel
  have hc3 : x + v 3 + v 2 = x + v 2 + v 3 := by abel
  have hc4 : x + v 3 + v 1 + v 0 = x + v 0 + v 1 + v 3 := by abel
  have hc5 : x + v 3 + v 1 = x + v 1 + v 3 := by abel
  have hc6 : x + v 3 + v 0 = x + v 0 + v 3 := by abel
  have hc7 : x + v 2 + v 1 + v 0 = x + v 0 + v 1 + v 2 := by abel
  have hc8 : x + v 2 + v 1 = x + v 1 + v 2 := by abel
  have hc9 : x + v 2 + v 0 = x + v 0 + v 2 := by abel
  have hc10 : x + v 1 + v 0 = x + v 0 + v 1 := by abel
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10]
  ring

lemma fourth_congr_cube {α : Type*} [AddCommGroup α] {f g : α → F} {v : Fin 4 → α} {x : α}
    (h : ∀ b : Fin 4 → Bool, f (cubePt x v b) = g (cubePt x v b)) :
    fourth f v x = fourth g v x := by
  rw [fourth_eq_sum16, fourth_eq_sum16]
  exact Finset.sum_congr rfl (fun b _ => h b)

def HasDeg {α : Type*} [AddCommGroup α] : ℕ → (α → F) → Prop
  | 0, f => ∀ u x, diff f u x = 0
  | n + 1, f => ∀ u, HasDeg n (diff f u)

lemma hasDeg_three_iff_cubic {α : Type*} [AddCommGroup α] (f : α → F) :
    HasDeg 3 f ↔ cubic f := by
  constructor
  · intro h v x
    rw [fourth_eq_iter]
    exact h (v 0) (v 1) (v 2) (v 3) x
  · intro h u0 u1 u2 u3 x
    let v : Fin 4 → α := fun r =>
      match r.val with | 0 => u0 | 1 => u1 | 2 => u2 | _ => u3
    have hv := h v x
    rw [fourth_eq_iter] at hv
    exact hv

lemma hasDeg_four_const {α : Type*} [AddCommGroup α] {f : α → F} (hf : HasDeg 4 f)
    (v : Fin 4 → α) (x y : α) : fourth f v x = fourth f v y := by
  have h0 : HasDeg 0 (fourth f v) := by
    have h4 := hf (v 0) (v 1) (v 2) (v 3)
    have heq : fourth f v = diff (diff (diff (diff f (v 0)) (v 1)) (v 2)) (v 3) := by
      funext z; exact fourth_eq_iter f v z
    rw [heq]; exact h4
  have hd := h0 (x - y) y
  rw [diff_eq_add, add_sub_cancel] at hd
  have : fourth f v x = fourth f v x + (fourth f v y + fourth f v y) := by
    rw [zmod2_add_self, add_zero]
  rw [this, ← add_assoc, hd, zero_add]

lemma hasDeg_const {α : Type*} [AddCommGroup α] (c : F) : HasDeg 0 (fun _ : α => c) := by
  intro u x; simp [diff_eq_add, zmod2_add_self]

lemma hasDeg_zero_eq {α : Type*} [AddCommGroup α] {f : α → F} (hf : HasDeg 0 f) (x y : α) :
    f x = f y := by
  have hd := hf (x - y) y
  rw [diff_eq_add, add_sub_cancel] at hd
  have : f x = f x + (f y + f y) := by rw [zmod2_add_self, add_zero]
  rw [this, ← add_assoc, hd, zero_add]

lemma hasDeg_succ {α : Type*} [AddCommGroup α] {n : ℕ} {f : α → F} (hf : HasDeg n f) :
    HasDeg (n + 1) f := by
  induction n generalizing f with
  | zero =>
    intro u v x
    have h1 : diff f u = fun _ => 0 := by funext y; exact hf u y
    rw [h1]; exact hasDeg_const 0 v x
  | succ n ih =>
    intro u; exact ih (hf u)

lemma hasDeg_mono {α : Type*} [AddCommGroup α] {a b : ℕ} {f : α → F}
    (hab : a ≤ b) (hf : HasDeg a f) : HasDeg b f := by
  induction hab with
  | refl => exact hf
  | step _ ih => exact hasDeg_succ ih

lemma hasDeg_add {α : Type*} [AddCommGroup α] {n : ℕ} {f g : α → F}
    (hf : HasDeg n f) (hg : HasDeg n g) : HasDeg n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero =>
    intro u x; rw [diff_add]; dsimp only; rw [hf u x, hg u x, add_zero]
  | succ n ih =>
    intro u; rw [diff_add]; exact ih (hf u) (hg u)

lemma hasDeg_mul_const_left {α : Type*} [AddCommGroup α] {n : ℕ} {f g : α → F}
    (hf : HasDeg 0 f) (hg : HasDeg n g) : HasDeg n (fun x => f x * g x) := by
  induction n generalizing g with
  | zero =>
    intro u x
    rw [diff_mul]; dsimp only; rw [hf u x, hg u x]; ring
  | succ n ih =>
    intro u
    have hrew : diff (fun x => f x * g x) u = fun x => f x * diff g u x := by
      funext x; rw [diff_mul]; dsimp only; rw [hf u x]; ring
    rw [hrew]
    exact ih (hg u)

lemma hasDeg_mul {α : Type*} [AddCommGroup α] :
    ∀ (s : ℕ) (m n : ℕ), m + n = s → ∀ {f g : α → F},
      HasDeg m f → HasDeg n g → HasDeg s (fun x => f x * g x) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro m n hmn f g hf hg
    cases m with
    | zero =>
      subst hmn; simp only [zero_add]
      exact hasDeg_mul_const_left hf hg
    | succ m =>
      cases n with
      | zero =>
        subst hmn; simp only [add_zero]
        have hcomm : (fun x => f x * g x) = (fun x => g x * f x) := by funext x; ring
        rw [hcomm]
        exact hasDeg_mul_const_left hg hf
      | succ n =>
        have hs : s = (m + n + 1) + 1 := by omega
        rw [hs]
        intro u
        rw [diff_mul]
        apply hasDeg_add
        · apply hasDeg_add
          · exact ih (m + n + 1) (by omega) m (n + 1) (by omega) (hf u) hg
          · exact ih (m + n + 1) (by omega) (m + 1) n (by omega) hf (hg u)
        · have h3 := ih (m + n) (by omega) m n rfl (hf u) (hg u)
          exact hasDeg_mono (by omega) h3

lemma hasDeg_one_of_affine {α : Type*} [AddCommGroup α] {f : α → F} (l : α → F)
    (h : ∀ x u, f (x + u) = f x + l u) : HasDeg 1 f := by
  intro u v x
  have h1 : diff f u = fun _ => l u := by
    funext y; rw [diff_eq_add, h y u]; ring_nf; rw [zmod2_two]; ring
  rw [h1]; exact hasDeg_const (l u) v x

lemma hasDeg_one_add {α : Type*} [AddCommGroup α] {f : α → F} (hf : HasDeg 1 f) :
    HasDeg 1 (fun x => 1 + f x) :=
  hasDeg_add (hasDeg_mono (by omega) (hasDeg_const 1)) hf

lemma hasDeg_rot {k : ℕ} (hk : 0 < k) (s : ℕ) (i : Fin k) :
    HasDeg 1 (fun x : W k => rot hk s x i) := by
  apply hasDeg_one_of_affine (fun u => rot hk s u i)
  intro x u; simp [rot]

lemma hasDeg_z {k : ℕ} (hk : 0 < k) (g s : ℕ) (name : W k) (i : Fin k) :
    HasDeg 1 (fun x : W k => mix hk g (rot hk s x + name) i) := by
  apply hasDeg_one_of_affine (fun u => mix hk g (rot hk s u) i)
  intro x u
  simp only [rot_add, mix_add, Pi.add_apply]; ring

lemma hasDeg_step_z {k : ℕ} (hk : 0 < k) {z : W k → W k}
    (hz : ∀ t, HasDeg 1 (fun x => z x t)) (i : Fin k) :
    HasDeg 2 (fun x => step hk (z x) i) := by
  unfold step
  apply hasDeg_add
  · exact hasDeg_mono (by omega) (hz i)
  · exact hasDeg_mul 2 1 1 rfl (hasDeg_one_add (hz _)) (hz _)

lemma hasDeg_step_z_const {k : ℕ} (hk : 0 < k) {z : W k → W k}
    (hz : ∀ t, HasDeg 1 (fun x => z x t)) (i : Fin k)
    (hc : HasDeg 0 (fun x => z x (ix hk (i.val + 1))) ∨
          HasDeg 0 (fun x => z x (ix hk (i.val + 2)))) :
    HasDeg 1 (fun x => step hk (z x) i) := by
  unfold step
  apply hasDeg_add (hz i)
  rcases hc with h1 | h2
  · exact hasDeg_mul 1 0 1 rfl (hasDeg_add (hasDeg_const 1) h1) (hz _)
  · exact hasDeg_mul 1 1 0 rfl (hasDeg_one_add (hz _)) h2

lemma hasDeg_step_z_split {k : ℕ} (hk : 0 < k) (z : W k → W k) (i : Fin k) :
    (fun x => step hk (z x) i) =
      fun x => z x (ix hk (i.val + 1)) * z x (ix hk (i.val + 2)) +
        (z x i + z x (ix hk (i.val + 2))) := by
  funext x; simp only [step]; ring

lemma hasDeg_deg2_mul {α : Type*} [AddCommGroup α] {p1 p2 a1 a2 : α → F}
    (hp1 : HasDeg 2 p1) (hp2 : HasDeg 2 p2) (ha1 : HasDeg 1 a1) (ha2 : HasDeg 1 a2)
    (hprod : HasDeg 3 (fun x => p1 x * p2 x)) :
    HasDeg 3 (fun x => (1 + (p1 x + a1 x)) * (p2 x + a2 x)) := by
  have heq : (fun x => (1 + (p1 x + a1 x)) * (p2 x + a2 x)) =
      fun x => (p1 x * p2 x + p1 x * a2 x) + (a1 x * p2 x + ((1 + a1 x) * a2 x + p2 x)) := by
    funext x; ring
  rw [heq]
  apply hasDeg_add
  · apply hasDeg_add hprod
    exact hasDeg_mul 3 2 1 rfl hp1 ha2
  · apply hasDeg_add
    · exact hasDeg_mul 3 1 2 rfl ha1 hp2
    · apply hasDeg_add
      · exact hasDeg_mono (by omega) (hasDeg_mul 2 1 1 rfl (hasDeg_one_add ha1) ha2)
      · exact hasDeg_mono (by omega) hp2

def outMod {k : ℕ} (hk : 0 < k) (b : Bool) (ov : Fin k → Option F)
    (name c₁ c₂ : Bool → W k) (x : W k) (i : Fin k) : F :=
  let z0 := mix hk (gap b) (rot hk (spin b) x + name b)
  let z : W k := fun t => match ov t with | some α => α | none => z0 t
  let y := step hk z + rot hk (if b then 4 else 0) x + c₁ b
  step hk (mix hk (gap b) y) i + rot hk (if b then 7 else 2) x i + c₂ b i

lemma outMod_eq_out {k : ℕ} (hk : 0 < k) (b : Bool) (ov : Fin k → Option F)
    (name c₁ c₂ : Bool → W k) (x : W k) (i : Fin k)
    (hov : ∀ t α, ov t = some α → mix hk (gap b) (rot hk (spin b) x + name b) t = α) :
    outMod hk b ov name c₁ c₂ x i = out hk name c₁ c₂ x b i := by
  unfold outMod out
  dsimp only
  have hz : (fun t => match ov t with
      | some α => α
      | none => mix hk (gap b) (rot hk (spin b) x + name b) t) =
      mix hk (gap b) (rot hk (spin b) x + name b) := by
    funext t
    cases h : ov t with
    | none => rfl
    | some α => exact (hov t α h).symm
  rw [hz]; rfl

lemma outMod_row_cubic {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k) (α : F)
    (name c₁ c₂ : Bool → W k) :
    cubic (fun x => outMod hk false (fun t => if t = ix hk (i.val + 2) then some α else none)
      name c₁ c₂ x i) := by
  rw [← hasDeg_three_iff_cubic]
  let z : W k → W k := fun x t =>
    if t = ix hk (i.val + 2) then α else mix hk 1 (rot hk 1 x + name false) t
  have hz1 : ∀ t, HasDeg 1 (fun x => z x t) := by
    intro t; dsimp [z]
    by_cases ht : t = ix hk (i.val + 2)
    · simp only [ht, ↓reduceIte]; exact hasDeg_mono (by omega) (hasDeg_const α)
    · simp only [ht, ↓reduceIte]; exact hasDeg_z hk 1 1 (name false) t
  have hz2_const : HasDeg 0 (fun x => z x (ix hk (i.val + 2))) := by
    dsimp [z]; simp only [↓reduceIte]; exact hasDeg_const α
  let y : W k → W k := fun x => step hk (z x) + rot hk 0 x + c₁ false
  have h1k : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hix_i1_m1 : ix hk ((ix hk (i.val + 1)).val + k - 1 % k) = i := by
    rw [h1k, ix_shift_sub_cancel hk i.val 1 (by omega), ix_val]
  have hix_i1_p1 : ix hk ((ix hk (i.val + 1)).val + 1) = ix hk (i.val + 2) := by
    rw [ix_add_left]
  have hix_i2_m1 : ix hk ((ix hk (i.val + 2)).val + k - 1 % k) = ix hk (i.val + 1) := by
    rw [h1k, ix_add_sub_mod hk (i.val + 2) 1 (by omega)]
    have : i.val + 2 + (k - 1) = (i.val + 1) + k := by omega
    rw [this, ix_add_k]
  have hix_i2_p1 : ix hk ((ix hk (i.val + 2)).val + 1) = ix hk (i.val + 3) := by
    rw [ix_add_left]
  have hix_i2_p2 : ix hk ((ix hk (i.val + 2)).val + 2) = ix hk (i.val + 4) := by
    rw [ix_add_left]
  have hix_i3_p1 : ix hk ((ix hk (i.val + 3)).val + 1) = ix hk (i.val + 4) := by
    rw [ix_add_left]
  have hix_i3_p2 : ix hk ((ix hk (i.val + 3)).val + 2) = ix hk (i.val + 5) := by
    rw [ix_add_left]
  have hy_i : HasDeg 1 (fun x => y x i) := by
    dsimp [y]
    apply hasDeg_add (hasDeg_add _ (hasDeg_rot hk 0 i)) (hasDeg_mono (by omega) (hasDeg_const _))
    exact hasDeg_step_z_const hk hz1 i (Or.inr hz2_const)
  have hy_i1 : HasDeg 1 (fun x => y x (ix hk (i.val + 1))) := by
    dsimp [y]
    apply hasDeg_add (hasDeg_add _ (hasDeg_rot hk 0 _)) (hasDeg_mono (by omega) (hasDeg_const _))
    refine hasDeg_step_z_const hk hz1 (ix hk (i.val + 1)) (Or.inl ?_)
    rw [hix_i1_p1]; exact hz2_const
  let p34 : W k → F := fun x => z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 4))
  let p45 : W k → F := fun x => z x (ix hk (i.val + 4)) * z x (ix hk (i.val + 5))
  have hp34 : HasDeg 2 p34 := hasDeg_mul 2 1 1 rfl (hz1 _) (hz1 _)
  have hp45 : HasDeg 2 p45 := hasDeg_mul 2 1 1 rfl (hz1 _) (hz1 _)
  let a2 : W k → F := fun x =>
    z x (ix hk (i.val + 2)) + z x (ix hk (i.val + 4)) + rot hk 0 x (ix hk (i.val + 2)) + c₁ false (ix hk (i.val + 2))
  let a3 : W k → F := fun x =>
    z x (ix hk (i.val + 3)) + z x (ix hk (i.val + 5)) + rot hk 0 x (ix hk (i.val + 3)) + c₁ false (ix hk (i.val + 3))
  have ha2 : HasDeg 1 a2 :=
    hasDeg_add (hasDeg_add (hasDeg_add (hz1 _) (hz1 _)) (hasDeg_rot hk 0 _)) (hasDeg_mono (by omega) (hasDeg_const _))
  have ha3 : HasDeg 1 a3 :=
    hasDeg_add (hasDeg_add (hasDeg_add (hz1 _) (hz1 _)) (hasDeg_rot hk 0 _)) (hasDeg_mono (by omega) (hasDeg_const _))
  have hy_i2 : ∀ x, y x (ix hk (i.val + 2)) = p34 x + a2 x := by
    intro x; dsimp [y, step, p34, a2]; rw [hix_i2_p1, hix_i2_p2]; ring
  have hy_i3 : ∀ x, y x (ix hk (i.val + 3)) = p45 x + a3 x := by
    intro x; dsimp [y, step, p45, a3]; rw [hix_i3_p1, hix_i3_p2]; ring
  have hm1 : ∀ x, mix hk 1 (y x) (ix hk (i.val + 1)) =
      p34 x + (y x (ix hk (i.val + 1)) + a2 x + y x i) := by
    intro x; dsimp [mix]; rw [hix_i1_p1, hix_i1_m1, hy_i2]; ring
  have hm2 : ∀ x, mix hk 1 (y x) (ix hk (i.val + 2)) =
      (p34 x + p45 x) + (a2 x + a3 x + y x (ix hk (i.val + 1))) := by
    intro x; dsimp [mix]; rw [hix_i2_p1, hix_i2_m1, hy_i2, hy_i3]; ring
  have hprod : HasDeg 3 (fun x => p34 x * (p34 x + p45 x)) := by
    have heq : (fun x => p34 x * (p34 x + p45 x)) =
        fun x => z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 4)) +
          (z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 4))) * z x (ix hk (i.val + 5)) := by
      funext x; dsimp [p34, p45]
      calc (z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 4))) *
            (z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 4)) + z x (ix hk (i.val + 4)) * z x (ix hk (i.val + 5)))
          = (z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 3))) * (z x (ix hk (i.val + 4)) * z x (ix hk (i.val + 4))) +
            z x (ix hk (i.val + 3)) * (z x (ix hk (i.val + 4)) * z x (ix hk (i.val + 4))) * z x (ix hk (i.val + 5)) := by ring
        _ = _ := by rw [zmod2_mul_self, zmod2_mul_self]
    rw [heq]
    apply hasDeg_add (hasDeg_mono (by omega) hp34)
    exact hasDeg_mul 3 2 1 rfl hp34 (hz1 _)
  have hmain : HasDeg 3 (fun x => (1 + mix hk 1 (y x) (ix hk (i.val + 1))) * mix hk 1 (y x) (ix hk (i.val + 2))) := by
    have hrew : (fun x => (1 + mix hk 1 (y x) (ix hk (i.val + 1))) * mix hk 1 (y x) (ix hk (i.val + 2))) =
        fun x => (1 + (p34 x + (y x (ix hk (i.val + 1)) + a2 x + y x i))) *
          ((p34 x + p45 x) + (a2 x + a3 x + y x (ix hk (i.val + 1)))) := by
      funext x; rw [hm1, hm2]
    rw [hrew]
    exact hasDeg_deg2_mul hp34 (hasDeg_add hp34 hp45)
      (hasDeg_add (hasDeg_add hy_i1 ha2) hy_i)
      (hasDeg_add (hasDeg_add ha2 ha3) hy_i1) hprod
  have hmi : HasDeg 2 (fun x => mix hk 1 (y x) i) := by
    have hy2 : ∀ t, HasDeg 2 (fun x => y x t) := fun t =>
      hasDeg_add (hasDeg_add (hasDeg_step_z hk hz1 t) (hasDeg_mono (by omega) (hasDeg_rot hk 0 t)))
        (hasDeg_mono (by omega) (hasDeg_const _))
    dsimp [mix]
    exact hasDeg_add (hasDeg_add (hy2 _) (hy2 _)) (hy2 _)
  have hgoal : (fun x => outMod hk false (fun t => if t = ix hk (i.val + 2) then some α else none)
      name c₁ c₂ x i) =
      fun x => (mix hk 1 (y x) i + (1 + mix hk 1 (y x) (ix hk (i.val + 1))) * mix hk 1 (y x) (ix hk (i.val + 2))) +
        rot hk 2 x i + c₂ false i := by
    funext x
    simp only [outMod, gap, spin, Bool.false_eq_true, ↓reduceIte, step]
    have hz_eq : (fun t => match (if t = ix hk (i.val + 2) then some α else none) with
        | some v => v
        | none => mix hk 1 (rot hk 1 x + name false) t) = z x := by
      funext t; dsimp [z]; split_ifs <;> rfl
    rw [hz_eq]
  rw [hgoal]
  apply hasDeg_add
  · apply hasDeg_add
    · exact hasDeg_add (hasDeg_mono (by omega) hmi) hmain
    · exact hasDeg_mono (by omega) (hasDeg_rot hk 2 i)
  · exact hasDeg_mono (by omega) (hasDeg_const _)

lemma outMod_col_cubic {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k) (α₁ α₅ : F)
    (name c₁ c₂ : Bool → W k) :
    cubic (fun x => outMod hk true
      (fun t => if t = ix hk (i.val + 1) then some α₁ else if t = ix hk (i.val + 5) then some α₅ else none)
      name c₁ c₂ x i) := by
  rw [← hasDeg_three_iff_cubic]
  let z : W k → W k := fun x t =>
    if t = ix hk (i.val + 1) then α₁
    else if t = ix hk (i.val + 5) then α₅
    else mix hk 2 (rot hk 3 x + name true) t
  have hne15 : ix hk (i.val + 5) ≠ ix hk (i.val + 1) := by
    have : i.val + 5 = (i.val + 1) + 4 := by omega
    rw [this]
    exact ix_ne_of_add hk (i.val + 1) 4 (by omega) (by omega)
  have hz1 : ∀ t, HasDeg 1 (fun x => z x t) := by
    intro t; dsimp [z]
    by_cases h1 : t = ix hk (i.val + 1)
    · simp only [h1, ↓reduceIte]; exact hasDeg_mono (by omega) (hasDeg_const α₁)
    · simp only [h1, ↓reduceIte]
      by_cases h5 : t = ix hk (i.val + 5)
      · simp only [h5, ↓reduceIte]; exact hasDeg_mono (by omega) (hasDeg_const α₅)
      · simp only [h5, ↓reduceIte]; exact hasDeg_z hk 2 3 (name true) t
  have hz1_c : HasDeg 0 (fun x => z x (ix hk (i.val + 1))) := by
    dsimp [z]; simp only [↓reduceIte]; exact hasDeg_const α₁
  have hz5_c : HasDeg 0 (fun x => z x (ix hk (i.val + 5))) := by
    dsimp [z]; simp only [hne15, ↓reduceIte]; exact hasDeg_const α₅
  let y : W k → W k := fun x => step hk (z x) + rot hk 4 x + c₁ true
  have h2k : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
  have hix_i1_p2 : ix hk ((ix hk (i.val + 1)).val + 2) = ix hk (i.val + 3) := by
    rw [ix_add_left]
  have hix_i1_m2 : ix hk ((ix hk (i.val + 1)).val + k - 2 % k) = ix hk (i.val + (k - 1)) := by
    rw [h2k, ix_add_sub_mod hk (i.val + 1) 2 (by omega)]
    have : i.val + 1 + (k - 2) = i.val + (k - 1) := by omega
    rw [this]
  have hix_i2_p2 : ix hk ((ix hk (i.val + 2)).val + 2) = ix hk (i.val + 4) := by
    rw [ix_add_left]
  have hix_i2_m2 : ix hk ((ix hk (i.val + 2)).val + k - 2 % k) = i := by
    rw [h2k, ix_shift_sub_cancel hk i.val 2 (by omega), ix_val]
  have hix_im1_p2 : ix hk ((ix hk (i.val + (k - 1))).val + 2) = ix hk (i.val + 1) := by
    rw [ix_add_left]
    have : i.val + (k - 1) + 2 = (i.val + 1) + k := by omega
    rw [this, ix_add_k]
  have hix_i3_p2 : ix hk ((ix hk (i.val + 3)).val + 2) = ix hk (i.val + 5) := by
    rw [ix_add_left]
  have hix_i4_p1 : ix hk ((ix hk (i.val + 4)).val + 1) = ix hk (i.val + 5) := by
    rw [ix_add_left]
  have hix_i1_p1 : ix hk ((ix hk (i.val + 1)).val + 1) = ix hk (i.val + 2) := by
    rw [ix_add_left]
  have hix_i2_p1 : ix hk ((ix hk (i.val + 2)).val + 1) = ix hk (i.val + 3) := by
    rw [ix_add_left]
  have hy_im1 : HasDeg 1 (fun x => y x (ix hk (i.val + (k - 1)))) := by
    dsimp [y]
    apply hasDeg_add (hasDeg_add _ (hasDeg_rot hk 4 _)) (hasDeg_mono (by omega) (hasDeg_const _))
    refine hasDeg_step_z_const hk hz1 _ (Or.inr ?_)
    rw [hix_im1_p2]; exact hz1_c
  have hy_i : HasDeg 1 (fun x => y x i) := by
    dsimp [y]
    apply hasDeg_add (hasDeg_add _ (hasDeg_rot hk 4 _)) (hasDeg_mono (by omega) (hasDeg_const _))
    exact hasDeg_step_z_const hk hz1 i (Or.inl hz1_c)
  have hy_i3 : HasDeg 1 (fun x => y x (ix hk (i.val + 3))) := by
    dsimp [y]
    apply hasDeg_add (hasDeg_add _ (hasDeg_rot hk 4 _)) (hasDeg_mono (by omega) (hasDeg_const _))
    refine hasDeg_step_z_const hk hz1 _ (Or.inr ?_)
    rw [hix_i3_p2]; exact hz5_c
  have hy_i4 : HasDeg 1 (fun x => y x (ix hk (i.val + 4))) := by
    dsimp [y]
    apply hasDeg_add (hasDeg_add _ (hasDeg_rot hk 4 _)) (hasDeg_mono (by omega) (hasDeg_const _))
    refine hasDeg_step_z_const hk hz1 _ (Or.inl ?_)
    rw [hix_i4_p1]; exact hz5_c
  let p23 : W k → F := fun x => z x (ix hk (i.val + 2)) * z x (ix hk (i.val + 3))
  let p34 : W k → F := fun x => z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 4))
  have hp23 : HasDeg 2 p23 := hasDeg_mul 2 1 1 rfl (hz1 _) (hz1 _)
  have hp34 : HasDeg 2 p34 := hasDeg_mul 2 1 1 rfl (hz1 _) (hz1 _)
  let a1 : W k → F := fun x =>
    z x (ix hk (i.val + 1)) + z x (ix hk (i.val + 3)) + rot hk 4 x (ix hk (i.val + 1)) + c₁ true (ix hk (i.val + 1))
  let a2 : W k → F := fun x =>
    z x (ix hk (i.val + 2)) + z x (ix hk (i.val + 4)) + rot hk 4 x (ix hk (i.val + 2)) + c₁ true (ix hk (i.val + 2))
  have ha1 : HasDeg 1 a1 :=
    hasDeg_add (hasDeg_add (hasDeg_add (hz1 _) (hz1 _)) (hasDeg_rot hk 4 _)) (hasDeg_mono (by omega) (hasDeg_const _))
  have ha2 : HasDeg 1 a2 :=
    hasDeg_add (hasDeg_add (hasDeg_add (hz1 _) (hz1 _)) (hasDeg_rot hk 4 _)) (hasDeg_mono (by omega) (hasDeg_const _))
  have hy_i1 : ∀ x, y x (ix hk (i.val + 1)) = p23 x + a1 x := by
    intro x; dsimp [y, step, p23, a1]; rw [hix_i1_p1, hix_i1_p2]; ring
  have hy_i2 : ∀ x, y x (ix hk (i.val + 2)) = p34 x + a2 x := by
    intro x; dsimp [y, step, p34, a2]; rw [hix_i2_p1, hix_i2_p2]; ring
  have hm1 : ∀ x, mix hk 2 (y x) (ix hk (i.val + 1)) =
      p23 x + (a1 x + y x (ix hk (i.val + 3)) + y x (ix hk (i.val + (k - 1)))) := by
    intro x; dsimp [mix]; rw [hix_i1_p2, hix_i1_m2, hy_i1]; ring
  have hm2 : ∀ x, mix hk 2 (y x) (ix hk (i.val + 2)) =
      p34 x + (a2 x + y x (ix hk (i.val + 4)) + y x i) := by
    intro x; dsimp [mix]; rw [hix_i2_p2, hix_i2_m2, hy_i2]; ring
  have hprod : HasDeg 3 (fun x => p23 x * p34 x) := by
    have heq : (fun x => p23 x * p34 x) =
        fun x => (z x (ix hk (i.val + 2)) * z x (ix hk (i.val + 3))) * z x (ix hk (i.val + 4)) := by
      funext x; dsimp [p23, p34]
      calc (z x (ix hk (i.val + 2)) * z x (ix hk (i.val + 3))) *
            (z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 4)))
          = z x (ix hk (i.val + 2)) * (z x (ix hk (i.val + 3)) * z x (ix hk (i.val + 3))) * z x (ix hk (i.val + 4)) := by ring
        _ = _ := by rw [zmod2_mul_self]
    rw [heq]
    exact hasDeg_mul 3 2 1 rfl hp23 (hz1 _)
  have hmain : HasDeg 3 (fun x => (1 + mix hk 2 (y x) (ix hk (i.val + 1))) * mix hk 2 (y x) (ix hk (i.val + 2))) := by
    have hrew : (fun x => (1 + mix hk 2 (y x) (ix hk (i.val + 1))) * mix hk 2 (y x) (ix hk (i.val + 2))) =
        fun x => (1 + (p23 x + (a1 x + y x (ix hk (i.val + 3)) + y x (ix hk (i.val + (k - 1)))))) *
          (p34 x + (a2 x + y x (ix hk (i.val + 4)) + y x i)) := by
      funext x; rw [hm1, hm2]
    rw [hrew]
    exact hasDeg_deg2_mul hp23 hp34
      (hasDeg_add (hasDeg_add ha1 hy_i3) hy_im1)
      (hasDeg_add (hasDeg_add ha2 hy_i4) hy_i) hprod
  have hmi : HasDeg 2 (fun x => mix hk 2 (y x) i) := by
    have hy2 : ∀ t, HasDeg 2 (fun x => y x t) := fun t =>
      hasDeg_add (hasDeg_add (hasDeg_step_z hk hz1 t) (hasDeg_mono (by omega) (hasDeg_rot hk 4 t)))
        (hasDeg_mono (by omega) (hasDeg_const _))
    dsimp [mix]
    exact hasDeg_add (hasDeg_add (hy2 _) (hy2 _)) (hy2 _)
  have hgoal : (fun x => outMod hk true
      (fun t => if t = ix hk (i.val + 1) then some α₁ else if t = ix hk (i.val + 5) then some α₅ else none)
      name c₁ c₂ x i) =
      fun x => (mix hk 2 (y x) i + (1 + mix hk 2 (y x) (ix hk (i.val + 1))) * mix hk 2 (y x) (ix hk (i.val + 2))) +
        rot hk 7 x i + c₂ true i := by
    funext x
    simp only [outMod, gap, spin, ↓reduceIte, step]
    have hz_eq : (fun t => match (if t = ix hk (i.val + 1) then some α₁ else if t = ix hk (i.val + 5) then some α₅ else none) with
        | some v => v
        | none => mix hk 2 (rot hk 3 x + name true) t) = z x := by
      funext t; dsimp [z]; split_ifs <;> rfl
    rw [hz_eq]
  rw [hgoal]
  apply hasDeg_add
  · apply hasDeg_add
    · exact hasDeg_add (hasDeg_mono (by omega) hmi) hmain
    · exact hasDeg_mono (by omega) (hasDeg_rot hk 7 i)
  · exact hasDeg_mono (by omega) (hasDeg_const _)

def bitAt (d j h : ℕ) : F :=
  if (h / 2 ^ (d - 1 - j)) % 2 = 1 then 1 else 0

lemma foldl_range_bit (f : ℕ → F) : ∀ (n : ℕ) (j : ℕ), j < n →
    let h := (List.range n).foldl (fun acc r => 2 * acc + (if f r = 0 then 0 else 1)) 0
    bitAt n j h = f j := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    dsimp only
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set h0 := (List.range n).foldl (fun acc r => 2 * acc + (if f r = 0 then 0 else 1)) 0
    set b : ℕ := if f n = 0 then 0 else 1
    have hb : b < 2 := by dsimp [b]; split_ifs <;> omega
    by_cases hjn : j = n
    · subst hjn
      have hval : (2 * h0 + b) / 2 ^ (j - j) % 2 = b := by
        rw [Nat.sub_self, pow_zero, Nat.div_one]; omega
      dsimp only [bitAt]
      rw [Nat.add_sub_cancel]
      simp only [hval]
      dsimp [b]
      rcases zmod2_cases (f j) with h | h <;> simp [h]
    · have hjlt : j < n := by omega
      have hval : (2 * h0 + b) / 2 ^ (n - j) % 2 = h0 / 2 ^ (n - 1 - j) % 2 := by
        have hsub : n - j = (n - 1 - j) + 1 := by omega
        have hdiv2 : (2 * h0 + b) / 2 = h0 := by omega
        rw [hsub, pow_succ', ← Nat.div_div_eq_div_mul, hdiv2]
      dsimp only [bitAt]
      rw [Nat.add_sub_cancel]
      simp only [hval]
      exact ih j hjlt

lemma bitAt_run_nonadaptive {k d : ℕ} (q : Fin d → D k) (x : W k) (j : Fin d) :
    bitAt d j.val (run (fun r _ => q r) x) = q j x := by
  let f : ℕ → F := fun r => if hr : r < d then q ⟨r, hr⟩ x else 0
  have hrun : run (fun r _ => q r) x =
      (List.range d).foldl (fun acc r => 2 * acc + (if f r = 0 then 0 else 1)) 0 := by
    unfold run
    have hmap : (List.finRange d).map Fin.val = List.range d := by
      apply List.ext_getElem (by simp)
      intro i hi1 hi2; simp
    rw [← hmap, List.foldl_map]
    congr 1; funext acc r
    simp only [f, r.isLt, ↓reduceDIte]
  rw [hrun, foldl_range_bit f d j.val j.isLt]
  simp only [f, j.isLt, ↓reduceDIte]

def linTap {k : ℕ} (hk : 0 < k) (g s : ℕ) (t : Fin k) : D k where
  toFun := fun x => mix hk g (rot hk s x) t
  map_add' := fun x y => by rw [rot_add, mix_add, Pi.add_apply]
  map_smul' := fun c x => by
    rcases zmod2_cases c with rfl | rfl
    · simp [rot_zero, mix_zero]
    · simp

theorem upper_bound {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k)
    (mark : Fin k → Bool × Bool) (d : ℕ) (name c₁ c₂ : Bool → W k)
    (hd : ((Finset.univ : Finset (Fin k)).filter (fun i => (mark i).1 = true)).card +
      2 * ((Finset.univ : Finset (Fin k)).filter (fun i => (mark i).2 = true)).card ≤ d) :
    ∃ (ask : Fin d → ℕ → D k) (readout : ℕ → Bool → Fin k → W k → F),
      (∀ h b i, cubic (readout h b i)) ∧
      ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
        out hk name c₁ c₂ x b i = readout (run ask x) b i x := by
  let Srow := (Finset.univ : Finset (Fin k)).filter (fun i => (mark i).1 = true)
  let Scol := (Finset.univ : Finset (Fin k)).filter (fun i => (mark i).2 = true)
  let r := Srow.card
  let c := Scol.card
  have hrc : r + 2 * c ≤ d := hd
  let eRow : {i : Fin k // i ∈ Srow} ≃ Fin r :=
    (Fintype.equivFinOfCardEq (by simp [r]))
  let eCol : {i : Fin k // i ∈ Scol} ≃ Fin c :=
    (Fintype.equivFinOfCardEq (by simp [c]))
  let q : Fin d → D k := fun j =>
    if h1 : j.val < r then
      let i := (eRow.symm ⟨j.val, h1⟩).1
      linTap hk 1 1 (ix hk (i.val + 2))
    else if h2 : j.val < r + 2 * c then
      let idx := (j.val - r) / 2
      have hidx : idx < c := by omega
      let i := (eCol.symm ⟨idx, hidx⟩).1
      if (j.val - r) % 2 = 0 then linTap hk 2 3 (ix hk (i.val + 1))
      else linTap hk 2 3 (ix hk (i.val + 5))
    else 0
  let ask : Fin d → ℕ → D k := fun j _ => q j
  let readout : ℕ → Bool → Fin k → W k → F := fun h b i =>
    match b with
    | false =>
      if hi : i ∈ Srow then
        let j := (eRow ⟨i, hi⟩).val
        let α := bitAt d j h + mix hk 1 (name false) (ix hk (i.val + 2))
        fun x => outMod hk false (fun t => if t = ix hk (i.val + 2) then some α else none) name c₁ c₂ x i
      else fun _ => 0
    | true =>
      if hi : i ∈ Scol then
        let j1 := r + 2 * (eCol ⟨i, hi⟩).val
        let j5 := r + 2 * (eCol ⟨i, hi⟩).val + 1
        let α1 := bitAt d j1 h + mix hk 2 (name true) (ix hk (i.val + 1))
        let α5 := bitAt d j5 h + mix hk 2 (name true) (ix hk (i.val + 5))
        fun x => outMod hk true
          (fun t => if t = ix hk (i.val + 1) then some α1 else if t = ix hk (i.val + 5) then some α5 else none)
          name c₁ c₂ x i
      else fun _ => 0
  refine ⟨ask, readout, ?_, ?_⟩
  · intro h b i
    cases b
    · dsimp only [readout]
      by_cases hi : i ∈ Srow
      · simp only [hi, ↓reduceDIte]
        exact outMod_row_cubic hk h7 i _ name c₁ c₂
      · simp only [hi, ↓reduceDIte]
        rw [← hasDeg_three_iff_cubic]
        exact hasDeg_mono (by omega) (hasDeg_const 0)
    · dsimp only [readout]
      by_cases hi : i ∈ Scol
      · simp only [hi, ↓reduceDIte]
        exact outMod_col_cubic hk h7 i _ _ name c₁ c₂
      · simp only [hi, ↓reduceDIte]
        rw [← hasDeg_three_iff_cubic]
        exact hasDeg_mono (by omega) (hasDeg_const 0)
  · intro x b i hon
    cases b
    · have hi : i ∈ Srow := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon⟩
      dsimp only [readout]
      simp only [hi, ↓reduceDIte]
      symm
      apply outMod_eq_out
      intro t α hα
      by_cases ht : t = ix hk (i.val + 2)
      · simp only [ht, ↓reduceIte, Option.some.injEq] at hα
        subst hα; subst ht
        let jFin : Fin d := ⟨(eRow ⟨i, hi⟩).val, by have := (eRow ⟨i, hi⟩).isLt; omega⟩
        have hbit := bitAt_run_nonadaptive q x jFin
        have hqj : q jFin x = mix hk 1 (rot hk 1 x) (ix hk (i.val + 2)) := by
          dsimp [q, jFin]
          have hlt : (eRow ⟨i, hi⟩).val < r := (eRow ⟨i, hi⟩).isLt
          simp only [hlt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply, linTap, LinearMap.coe_mk, AddHom.coe_mk]
        dsimp [jFin] at hbit
        rw [hbit, hqj, ← Pi.add_apply, ← mix_add]; rfl
      · simp only [ht, ↓reduceIte, reduceCtorEq] at hα
    · have hi : i ∈ Scol := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon⟩
      dsimp only [readout]
      simp only [hi, ↓reduceDIte]
      symm
      apply outMod_eq_out
      intro t α hα
      by_cases ht1 : t = ix hk (i.val + 1)
      · simp only [ht1, ↓reduceIte, Option.some.injEq] at hα
        subst hα; subst ht1
        let j1Fin : Fin d := ⟨r + 2 * (eCol ⟨i, hi⟩).val, by have := (eCol ⟨i, hi⟩).isLt; omega⟩
        have hbit := bitAt_run_nonadaptive q x j1Fin
        have hqj : q j1Fin x = mix hk 2 (rot hk 3 x) (ix hk (i.val + 1)) := by
          dsimp [q, j1Fin]
          have hn1 : ¬ (r + 2 * (eCol ⟨i, hi⟩).val < r) := by omega
          have h2 : r + 2 * (eCol ⟨i, hi⟩).val < r + 2 * c := by have := (eCol ⟨i, hi⟩).isLt; omega
          have hev : (r + 2 * (eCol ⟨i, hi⟩).val - r) % 2 = 0 := by omega
          have hdiv : (⟨(r + 2 * (eCol ⟨i, hi⟩).val - r) / 2, by omega⟩ : Fin c) = eCol ⟨i, hi⟩ :=
            Fin.ext (by dsimp; omega)
          simp only [hn1, h2, ↓reduceDIte, hev, ↓reduceIte, hdiv, Equiv.symm_apply_apply,
            linTap, LinearMap.coe_mk, AddHom.coe_mk]
        dsimp [j1Fin] at hbit
        rw [hbit, hqj, ← Pi.add_apply, ← mix_add]; rfl
      · simp only [ht1, ↓reduceIte] at hα
        by_cases ht5 : t = ix hk (i.val + 5)
        · simp only [ht5, ↓reduceIte, Option.some.injEq] at hα
          subst hα; subst ht5
          let j5Fin : Fin d := ⟨r + 2 * (eCol ⟨i, hi⟩).val + 1, by have := (eCol ⟨i, hi⟩).isLt; omega⟩
          have hbit := bitAt_run_nonadaptive q x j5Fin
          have hqj : q j5Fin x = mix hk 2 (rot hk 3 x) (ix hk (i.val + 5)) := by
            dsimp [q, j5Fin]
            have hn1 : ¬ (r + 2 * (eCol ⟨i, hi⟩).val + 1 < r) := by omega
            have h2 : r + 2 * (eCol ⟨i, hi⟩).val + 1 < r + 2 * c := by have := (eCol ⟨i, hi⟩).isLt; omega
            have hodd : ¬ ((r + 2 * (eCol ⟨i, hi⟩).val + 1 - r) % 2 = 0) := by omega
            have hdiv : (⟨(r + 2 * (eCol ⟨i, hi⟩).val + 1 - r) / 2, by omega⟩ : Fin c) = eCol ⟨i, hi⟩ :=
              Fin.ext (by dsimp; omega)
            simp only [hn1, h2, ↓reduceDIte, hodd, ↓reduceIte, hdiv, Equiv.symm_apply_apply,
              linTap, LinearMap.coe_mk, AddHom.coe_mk]
          dsimp [j5Fin] at hbit
          rw [hbit, hqj, ← Pi.add_apply, ← mix_add]; rfl
        · simp only [ht5, ↓reduceIte, reduceCtorEq] at hα

def P_row (z : Fin 5 → F) : F :=
  z 0 * z 1 * z 2 * z 3 + z 0 * z 1 * z 3 * z 4 + z 1 * z 2 * z 3 * z 4

def P_col (z : Fin 7 → F) : F :=
  z 0 * z 1 * z 3 * z 4 + z 0 * z 1 * z 5 * z 6 + z 2 * z 3 * z 5 * z 6 + z 1 * z 2 * z 4 * z 5

lemma hasDeg_coord {n : ℕ} (t : Fin n) : HasDeg 1 (fun z : Fin n → F => z t) := by
  apply hasDeg_one_of_affine (fun u => u t)
  intro x u; rfl

lemma hasDeg_four_P_row : HasDeg 4 P_row := by
  unfold P_row
  have hterm : ∀ a b c d : Fin 5, HasDeg 4 (fun z : Fin 5 → F => z a * z b * z c * z d) := fun a b c d =>
    hasDeg_mul 4 3 1 rfl (hasDeg_mul 3 2 1 rfl (hasDeg_mul 2 1 1 rfl (hasDeg_coord a) (hasDeg_coord b)) (hasDeg_coord c)) (hasDeg_coord d)
  exact hasDeg_add (hasDeg_add (hterm 0 1 2 3) (hterm 0 1 3 4)) (hterm 1 2 3 4)

lemma hasDeg_four_P_col : HasDeg 4 P_col := by
  unfold P_col
  have hterm : ∀ a b c d : Fin 7, HasDeg 4 (fun z : Fin 7 → F => z a * z b * z c * z d) := fun a b c d =>
    hasDeg_mul 4 3 1 rfl (hasDeg_mul 3 2 1 rfl (hasDeg_mul 2 1 1 rfl (hasDeg_coord a) (hasDeg_coord b)) (hasDeg_coord c)) (hasDeg_coord d)
  exact hasDeg_add (hasDeg_add (hasDeg_add (hterm 0 1 3 4) (hterm 0 1 5 6)) (hterm 2 3 5 6)) (hterm 1 2 4 5)

def tapRow {k : ℕ} (hk : 0 < k) (i : Fin k) : W k →ₗ[F] (Fin 5 → F) where
  toFun := fun x t => mix hk 1 (rot hk 1 x) (ix hk (i.val + 1 + t.val))
  map_add' := fun x y => by funext t; rw [rot_add, mix_add, Pi.add_apply, Pi.add_apply]
  map_smul' := fun c x => by
    funext t
    rcases zmod2_cases c with rfl | rfl
    · simp [rot_zero, mix_zero]
    · simp

def tapCol {k : ℕ} (hk : 0 < k) (i : Fin k) : W k →ₗ[F] (Fin 7 → F) where
  toFun := fun x t => mix hk 2 (rot hk 3 x) (ix hk (i.val + t.val))
  map_add' := fun x y => by funext t; rw [rot_add, mix_add, Pi.add_apply, Pi.add_apply]
  map_smul' := fun c x => by
    funext t
    rcases zmod2_cases c with rfl | rfl
    · simp [rot_zero, mix_zero]
    · simp

lemma fourth_out_row {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k)
    (name c₁ c₂ : Bool → W k) (v : Fin 4 → W k) :
    fourth (fun x => out hk name c₁ c₂ x false i) v 0 =
      fourth P_row (fun r => tapRow hk i (v r)) 0 := by
  let z : W k → W k := fun x => mix hk 1 (rot hk 1 x + name false)
  have hz1 : ∀ t, HasDeg 1 (fun x => z x t) := fun t => hasDeg_z hk 1 1 (name false) t
  let y : W k → W k := fun x => step hk (z x) + rot hk 0 x + c₁ false
  have h1k : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hix_i1_m1 : ix hk ((ix hk (i.val + 1)).val + k - 1 % k) = i := by
    rw [h1k, ix_shift_sub_cancel hk i.val 1 (by omega), ix_val]
  have hix_i1_p1 : ix hk ((ix hk (i.val + 1)).val + 1) = ix hk (i.val + 2) := by
    rw [ix_add_left]
  have hix_i1_p2 : ix hk ((ix hk (i.val + 1)).val + 2) = ix hk (i.val + 3) := by
    rw [ix_add_left]
  have hix_i2_m1 : ix hk ((ix hk (i.val + 2)).val + k - 1 % k) = ix hk (i.val + 1) := by
    rw [h1k, ix_add_sub_mod hk (i.val + 2) 1 (by omega)]
    have : i.val + 2 + (k - 1) = (i.val + 1) + k := by omega
    rw [this, ix_add_k]
  have hix_i2_p1 : ix hk ((ix hk (i.val + 2)).val + 1) = ix hk (i.val + 3) := by
    rw [ix_add_left]
  have hix_i2_p2 : ix hk ((ix hk (i.val + 2)).val + 2) = ix hk (i.val + 4) := by
    rw [ix_add_left]
  have hix_i3_p1 : ix hk ((ix hk (i.val + 3)).val + 1) = ix hk (i.val + 4) := by
    rw [ix_add_left]
  have hix_i3_p2 : ix hk ((ix hk (i.val + 3)).val + 2) = ix hk (i.val + 5) := by
    rw [ix_add_left]
  let Z : W k → Fin 5 → F := fun x t => z x (ix hk (i.val + 1 + t.val))
  have hZ : ∀ x u, Z (x + u) = Z x + tapRow hk i u := by
    intro x u; funext t
    dsimp [Z, z, tapRow]
    rw [rot_add]
    have h1 : rot hk 1 x + rot hk 1 u + name false = (rot hk 1 x + name false) + rot hk 1 u := by abel
    rw [h1, mix_add, Pi.add_apply]
  have hdeg3 : HasDeg 3 (fun x => out hk name c₁ c₂ x false i + P_row (Z x)) := by
    let p12 : W k → F := fun x => Z x 0 * Z x 1
    let p23 : W k → F := fun x => Z x 1 * Z x 2
    let p34 : W k → F := fun x => Z x 2 * Z x 3
    let p45 : W k → F := fun x => Z x 3 * Z x 4
    let m1_p : W k → F := fun x => p12 x + p23 x + p34 x
    let m2_p : W k → F := fun x => p23 x + p34 x + p45 x
    let linY : Fin k → W k → F := fun t x =>
      z x t + z x (ix hk (t.val + 2)) + rot hk 0 x t + c₁ false t
    have hlinY : ∀ t, HasDeg 1 (linY t) := fun t =>
      hasDeg_add (hasDeg_add (hasDeg_add (hz1 t) (hz1 _)) (hasDeg_rot hk 0 t)) (hasDeg_mono (by omega) (hasDeg_const _))
    have hy_eq : ∀ (t : Fin k) (x : W k), y x t = z x (ix hk (t.val + 1)) * z x (ix hk (t.val + 2)) + linY t x := by
      intro t x; dsimp [y, step, linY]; ring
    let a1 : W k → F := fun x => linY (ix hk (i.val + 1)) x + linY (ix hk (i.val + 2)) x + linY i x
    let a2 : W k → F := fun x => linY (ix hk (i.val + 2)) x + linY (ix hk (i.val + 3)) x + linY (ix hk (i.val + 1)) x
    have ha1 : HasDeg 1 a1 := hasDeg_add (hasDeg_add (hlinY _) (hlinY _)) (hlinY _)
    have ha2 : HasDeg 1 a2 := hasDeg_add (hasDeg_add (hlinY _) (hlinY _)) (hlinY _)
    have hm1 : ∀ x, mix hk 1 (y x) (ix hk (i.val + 1)) = m1_p x + a1 x := by
      intro x; dsimp [mix, m1_p, p12, p23, p34, a1, Z]
      rw [hix_i1_p1, hix_i1_m1, hy_eq, hy_eq, hy_eq, hix_i1_p1, hix_i1_p2, hix_i2_p1, hix_i2_p2]
      ring
    have hm2 : ∀ x, mix hk 1 (y x) (ix hk (i.val + 2)) = m2_p x + a2 x := by
      intro x; dsimp [mix, m2_p, p23, p34, p45, a2, Z]
      rw [hix_i2_p1, hix_i2_m1, hy_eq, hy_eq, hy_eq, hix_i2_p1, hix_i2_p2, hix_i3_p1, hix_i3_p2, hix_i1_p1, hix_i1_p2]
      ring
    have hZ1 : ∀ r : Fin 5, HasDeg 1 (fun x => Z x r) := fun r => hz1 _
    have hp12 : HasDeg 2 p12 := hasDeg_mul 2 1 1 rfl (hZ1 0) (hZ1 1)
    have hp23 : HasDeg 2 p23 := hasDeg_mul 2 1 1 rfl (hZ1 1) (hZ1 2)
    have hp34 : HasDeg 2 p34 := hasDeg_mul 2 1 1 rfl (hZ1 2) (hZ1 3)
    have hp45 : HasDeg 2 p45 := hasDeg_mul 2 1 1 rfl (hZ1 3) (hZ1 4)
    have hm1p : HasDeg 2 m1_p := hasDeg_add (hasDeg_add hp12 hp23) hp34
    have hm2p : HasDeg 2 m2_p := hasDeg_add (hasDeg_add hp23 hp34) hp45
    have hrem_prod : HasDeg 3 (fun x => m1_p x * m2_p x + P_row (Z x)) := by
      have heq : (fun x => m1_p x * m2_p x + P_row (Z x)) =
          fun x => (Z x 0 * Z x 1 * Z x 2 + Z x 1 * Z x 2) +
            (Z x 2 * Z x 3 + Z x 2 * Z x 3 * Z x 4) := by
        funext x
        dsimp [m1_p, m2_p, p12, p23, p34, p45, P_row]
        set a := Z x 0; set b := Z x 1; set c := Z x 2; set d := Z x 3; set e := Z x 4
        have ha : a * a = a := zmod2_mul_self a
        have hb : b * b = b := zmod2_mul_self b
        have hc : c * c = c := zmod2_mul_self c
        have hd : d * d = d := zmod2_mul_self d
        have he : e * e = e := zmod2_mul_self e
        have hstep1 : (a * b + b * c + c * d) * (b * c + c * d + d * e) +
            (a * b * c * d + a * b * d * e + b * c * d * e) =
            a * (b * b) * c + (b * b) * (c * c) + (c * c) * (d * d) +
            c * (d * d) * e +
            (a * b * c * d + a * b * c * d) + (a * b * d * e + a * b * d * e) +
            (b * c * d * e + b * c * d * e) +
            (b * (c * c) * d + b * (c * c) * d) := by ring
        rw [hstep1, hb, hc, hd, zmod2_add_self, zmod2_add_self, zmod2_add_self, zmod2_add_self]
        ring
      rw [heq]
      apply hasDeg_add
      · apply hasDeg_add (hasDeg_mul 3 2 1 rfl hp12 (hZ1 2)) (hasDeg_mono (by omega) hp23)
      · apply hasDeg_add (hasDeg_mono (by omega) hp34) (hasDeg_mul 3 2 1 rfl hp34 (hZ1 4))
    have hmi : HasDeg 2 (fun x => mix hk 1 (y x) i) := by
      have hy2 : ∀ t, HasDeg 2 (fun x => y x t) := fun t =>
        hasDeg_add (hasDeg_add (hasDeg_step_z hk hz1 t) (hasDeg_mono (by omega) (hasDeg_rot hk 0 t)))
          (hasDeg_mono (by omega) (hasDeg_const _))
      dsimp [mix]; exact hasDeg_add (hasDeg_add (hy2 _) (hy2 _)) (hy2 _)
    have hfull : (fun x => out hk name c₁ c₂ x false i + P_row (Z x)) =
        fun x => ((m1_p x * m2_p x + P_row (Z x)) + m1_p x * a2 x) +
          (a1 x * m2_p x + ((1 + a1 x) * a2 x + m2_p x)) +
          (mix hk 1 (y x) i + rot hk 2 x i + c₂ false i) := by
      funext x
      have ho : out hk name c₁ c₂ x false i =
          mix hk 1 (y x) i + (1 + mix hk 1 (y x) (ix hk (i.val + 1))) * mix hk 1 (y x) (ix hk (i.val + 2)) +
          rot hk 2 x i + c₂ false i := by
        simp only [out, gap, spin, Bool.false_eq_true, ↓reduceIte, step, y, z, Pi.add_apply]
      rw [ho, hm1, hm2]; ring
    rw [hfull]
    apply hasDeg_add
    · apply hasDeg_add
      · exact hasDeg_add hrem_prod (hasDeg_mul 3 2 1 rfl hm1p ha2)
      · exact hasDeg_add (hasDeg_mul 3 1 2 rfl ha1 hm2p)
          (hasDeg_add (hasDeg_mono (by omega) (hasDeg_mul 2 1 1 rfl (hasDeg_one_add ha1) ha2))
            (hasDeg_mono (by omega) hm2p))
    · exact hasDeg_add (hasDeg_add (hasDeg_mono (by omega) hmi) (hasDeg_mono (by omega) (hasDeg_rot hk 2 i)))
        (hasDeg_mono (by omega) (hasDeg_const _))
  have hzero : fourth (fun x => out hk name c₁ c₂ x false i + P_row (Z x)) v 0 = 0 :=
    (hasDeg_three_iff_cubic _).mp hdeg3 v 0
  rw [fourth_add, fourth_comp_affine P_row Z (tapRow hk i) hZ,
      hasDeg_four_const hasDeg_four_P_row _ (Z 0) 0] at hzero
  have : fourth (fun x => out hk name c₁ c₂ x false i) v 0 =
      (fourth (fun x => out hk name c₁ c₂ x false i) v 0 + fourth P_row (fun r => tapRow hk i (v r)) 0) +
      fourth P_row (fun r => tapRow hk i (v r)) 0 := by
    rw [add_assoc, zmod2_add_self, add_zero]
  rw [this, hzero, zero_add]

lemma fourth_out_col {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k)
    (name c₁ c₂ : Bool → W k) (v : Fin 4 → W k) :
    fourth (fun x => out hk name c₁ c₂ x true i) v 0 =
      fourth P_col (fun r => tapCol hk i (v r)) 0 := by
  let z : W k → W k := fun x => mix hk 2 (rot hk 3 x + name true)
  have hz1 : ∀ t, HasDeg 1 (fun x => z x t) := fun t => hasDeg_z hk 2 3 (name true) t
  let y : W k → W k := fun x => step hk (z x) + rot hk 4 x + c₁ true
  have h2k : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
  have hix_i1_p2 : ix hk ((ix hk (i.val + 1)).val + 2) = ix hk (i.val + 3) := by rw [ix_add_left]
  have hix_i1_m2 : ix hk ((ix hk (i.val + 1)).val + k - 2 % k) = ix hk (i.val + (k - 1)) := by
    rw [h2k, ix_add_sub_mod hk (i.val + 1) 2 (by omega)]
    have : i.val + 1 + (k - 2) = i.val + (k - 1) := by omega
    rw [this]
  have hix_i2_p2 : ix hk ((ix hk (i.val + 2)).val + 2) = ix hk (i.val + 4) := by rw [ix_add_left]
  have hix_i2_m2 : ix hk ((ix hk (i.val + 2)).val + k - 2 % k) = i := by
    rw [h2k, ix_shift_sub_cancel hk i.val 2 (by omega), ix_val]
  have hix_im1_p1 : ix hk ((ix hk (i.val + (k - 1))).val + 1) = ix hk (i.val + 0) := by
    rw [ix_add_left, add_zero]
    have : i.val + (k - 1) + 1 = i.val + k := by omega
    rw [this, ix_add_k]
  have hix_im1_p2 : ix hk ((ix hk (i.val + (k - 1))).val + 2) = ix hk (i.val + 1) := by
    rw [ix_add_left]
    have : i.val + (k - 1) + 2 = (i.val + 1) + k := by omega
    rw [this, ix_add_k]
  have hix_i1_p1 : ix hk ((ix hk (i.val + 1)).val + 1) = ix hk (i.val + 2) := by rw [ix_add_left]
  have hix_i2_p1 : ix hk ((ix hk (i.val + 2)).val + 1) = ix hk (i.val + 3) := by rw [ix_add_left]
  have hix_i3_p1 : ix hk ((ix hk (i.val + 3)).val + 1) = ix hk (i.val + 4) := by rw [ix_add_left]
  have hix_i3_p2 : ix hk ((ix hk (i.val + 3)).val + 2) = ix hk (i.val + 5) := by rw [ix_add_left]
  have hix_i4_p1 : ix hk ((ix hk (i.val + 4)).val + 1) = ix hk (i.val + 5) := by rw [ix_add_left]
  have hix_i4_p2 : ix hk ((ix hk (i.val + 4)).val + 2) = ix hk (i.val + 6) := by rw [ix_add_left]
  let Z : W k → Fin 7 → F := fun x t => z x (ix hk (i.val + t.val))
  have hZ : ∀ x u, Z (x + u) = Z x + tapCol hk i u := by
    intro x u; funext t
    dsimp [Z, z, tapCol]
    rw [rot_add]
    have h1 : rot hk 3 x + rot hk 3 u + name true = (rot hk 3 x + name true) + rot hk 3 u := by abel
    rw [h1, mix_add, Pi.add_apply]
  have hdeg3 : HasDeg 3 (fun x => out hk name c₁ c₂ x true i + P_col (Z x)) := by
    let p01 : W k → F := fun x => Z x 0 * Z x 1
    let p12 : W k → F := fun x => Z x 1 * Z x 2
    let p23 : W k → F := fun x => Z x 2 * Z x 3
    let p34 : W k → F := fun x => Z x 3 * Z x 4
    let p45 : W k → F := fun x => Z x 4 * Z x 5
    let p56 : W k → F := fun x => Z x 5 * Z x 6
    let m1_p : W k → F := fun x => p01 x + p23 x + p45 x
    let m2_p : W k → F := fun x => p12 x + p34 x + p56 x
    let linY : Fin k → W k → F := fun t x =>
      z x t + z x (ix hk (t.val + 2)) + rot hk 4 x t + c₁ true t
    have hlinY : ∀ t, HasDeg 1 (linY t) := fun t =>
      hasDeg_add (hasDeg_add (hasDeg_add (hz1 t) (hz1 _)) (hasDeg_rot hk 4 t)) (hasDeg_mono (by omega) (hasDeg_const _))
    have hy_eq : ∀ (t : Fin k) (x : W k), y x t = z x (ix hk (t.val + 1)) * z x (ix hk (t.val + 2)) + linY t x := by
      intro t x; dsimp [y, step, linY]; ring
    let a1 : W k → F := fun x => linY (ix hk (i.val + 1)) x + linY (ix hk (i.val + 3)) x + linY (ix hk (i.val + (k - 1))) x
    let a2 : W k → F := fun x => linY (ix hk (i.val + 2)) x + linY (ix hk (i.val + 4)) x + linY i x
    have ha1 : HasDeg 1 a1 := hasDeg_add (hasDeg_add (hlinY _) (hlinY _)) (hlinY _)
    have ha2 : HasDeg 1 a2 := hasDeg_add (hasDeg_add (hlinY _) (hlinY _)) (hlinY _)
    have hm1 : ∀ x, mix hk 2 (y x) (ix hk (i.val + 1)) = m1_p x + a1 x := by
      intro x; dsimp [mix, m1_p, p01, p23, p45, a1, Z]
      rw [hix_i1_p2, hix_i1_m2, hy_eq, hy_eq, hy_eq, hix_i1_p1, hix_i1_p2, hix_i3_p1, hix_i3_p2,
        hix_im1_p1, hix_im1_p2, Nat.add_zero]
      ring
    have hm2 : ∀ x, mix hk 2 (y x) (ix hk (i.val + 2)) = m2_p x + a2 x := by
      intro x; dsimp [mix, m2_p, p12, p34, p56, a2, Z]
      rw [hix_i2_p2, hix_i2_m2, hy_eq, hy_eq, hy_eq, hix_i2_p1, hix_i2_p2, hix_i4_p1, hix_i4_p2]
      ring
    have hZ1 : ∀ r : Fin 7, HasDeg 1 (fun x => Z x r) := fun r => hz1 _
    have hp01 : HasDeg 2 p01 := hasDeg_mul 2 1 1 rfl (hZ1 0) (hZ1 1)
    have hp12 : HasDeg 2 p12 := hasDeg_mul 2 1 1 rfl (hZ1 1) (hZ1 2)
    have hp23 : HasDeg 2 p23 := hasDeg_mul 2 1 1 rfl (hZ1 2) (hZ1 3)
    have hp34 : HasDeg 2 p34 := hasDeg_mul 2 1 1 rfl (hZ1 3) (hZ1 4)
    have hp45 : HasDeg 2 p45 := hasDeg_mul 2 1 1 rfl (hZ1 4) (hZ1 5)
    have hp56 : HasDeg 2 p56 := hasDeg_mul 2 1 1 rfl (hZ1 5) (hZ1 6)
    have hm1p : HasDeg 2 m1_p := hasDeg_add (hasDeg_add hp01 hp23) hp45
    have hm2p : HasDeg 2 m2_p := hasDeg_add (hasDeg_add hp12 hp34) hp56
    have hrem_prod : HasDeg 3 (fun x => m1_p x * m2_p x + P_col (Z x)) := by
      have heq : (fun x => m1_p x * m2_p x + P_col (Z x)) =
          fun x => (Z x 0 * Z x 1 * Z x 2 + Z x 1 * Z x 2 * Z x 3) +
            (Z x 2 * Z x 3 * Z x 4 + Z x 3 * Z x 4 * Z x 5 + Z x 4 * Z x 5 * Z x 6) := by
        funext x
        dsimp [m1_p, m2_p, p01, p12, p23, p34, p45, p56, P_col]
        set a := Z x 0; set b := Z x 1; set c := Z x 2; set d := Z x 3
        set e := Z x 4; set f := Z x 5; set g := Z x 6
        have hstep1 : (a * b + c * d + e * f) * (b * c + d * e + f * g) +
            (a * b * d * e + a * b * f * g + c * d * f * g + b * c * e * f) =
            a * (b * b) * c + b * (c * c) * d + c * (d * d) * e + d * (e * e) * f + e * (f * f) * g +
            (a * b * d * e + a * b * d * e) + (a * b * f * g + a * b * f * g) +
            (c * d * f * g + c * d * f * g) + (b * c * e * f + b * c * e * f) := by ring
        rw [hstep1, zmod2_mul_self b, zmod2_mul_self c, zmod2_mul_self d, zmod2_mul_self e, zmod2_mul_self f,
            zmod2_add_self, zmod2_add_self, zmod2_add_self, zmod2_add_self]
        ring
      rw [heq]
      have h3 : ∀ u v w : Fin 7, HasDeg 3 (fun x => Z x u * Z x v * Z x w) := fun u v w =>
        hasDeg_mul 3 2 1 rfl (hasDeg_mul 2 1 1 rfl (hZ1 u) (hZ1 v)) (hZ1 w)
      exact hasDeg_add (hasDeg_add (h3 0 1 2) (h3 1 2 3))
        (hasDeg_add (hasDeg_add (h3 2 3 4) (h3 3 4 5)) (h3 4 5 6))
    have hmi : HasDeg 2 (fun x => mix hk 2 (y x) i) := by
      have hy2 : ∀ t, HasDeg 2 (fun x => y x t) := fun t =>
        hasDeg_add (hasDeg_add (hasDeg_step_z hk hz1 t) (hasDeg_mono (by omega) (hasDeg_rot hk 4 t)))
          (hasDeg_mono (by omega) (hasDeg_const _))
      dsimp [mix]; exact hasDeg_add (hasDeg_add (hy2 _) (hy2 _)) (hy2 _)
    have hfull : (fun x => out hk name c₁ c₂ x true i + P_col (Z x)) =
        fun x => ((m1_p x * m2_p x + P_col (Z x)) + m1_p x * a2 x) +
          (a1 x * m2_p x + ((1 + a1 x) * a2 x + m2_p x)) +
          (mix hk 2 (y x) i + rot hk 7 x i + c₂ true i) := by
      funext x
      have ho : out hk name c₁ c₂ x true i =
          mix hk 2 (y x) i + (1 + mix hk 2 (y x) (ix hk (i.val + 1))) * mix hk 2 (y x) (ix hk (i.val + 2)) +
          rot hk 7 x i + c₂ true i := by
        simp only [out, gap, spin, ↓reduceIte, step, y, z, Pi.add_apply]
      rw [ho, hm1, hm2]; ring
    rw [hfull]
    apply hasDeg_add
    · apply hasDeg_add
      · exact hasDeg_add hrem_prod (hasDeg_mul 3 2 1 rfl hm1p ha2)
      · exact hasDeg_add (hasDeg_mul 3 1 2 rfl ha1 hm2p)
          (hasDeg_add (hasDeg_mono (by omega) (hasDeg_mul 2 1 1 rfl (hasDeg_one_add ha1) ha2))
            (hasDeg_mono (by omega) hm2p))
    · exact hasDeg_add (hasDeg_add (hasDeg_mono (by omega) hmi) (hasDeg_mono (by omega) (hasDeg_rot hk 7 i)))
        (hasDeg_mono (by omega) (hasDeg_const _))
  have hzero : fourth (fun x => out hk name c₁ c₂ x true i + P_col (Z x)) v 0 = 0 :=
    (hasDeg_three_iff_cubic _).mp hdeg3 v 0
  rw [fourth_add, fourth_comp_affine P_col Z (tapCol hk i) hZ,
      hasDeg_four_const hasDeg_four_P_col _ (Z 0) 0] at hzero
  have : fourth (fun x => out hk name c₁ c₂ x true i) v 0 =
      (fourth (fun x => out hk name c₁ c₂ x true i) v 0 + fourth P_col (fun r => tapCol hk i (v r)) 0) +
      fourth P_col (fun r => tapCol hk i (v r)) 0 := by
    rw [add_assoc, zmod2_add_self, add_zero]
  rw [this, hzero, zero_add]

def rotBy {k : ℕ} (hk : 0 < k) (i : Fin k) : W k →ₗ[F] W k where
  toFun := fun u j => u (ix hk (j.val + k - i.val))
  map_add' := fun u v => by funext j; rfl
  map_smul' := fun c u => by funext j; rfl

lemma rotBy_ix {k : ℕ} (hk : 0 < k) (i : Fin k) (u : W k) (r : ℕ) :
    rotBy hk i u (ix hk (i.val + r)) = u (ix hk r) := by
  dsimp [rotBy]
  congr 1
  rw [ix_add_sub_mod hk (i.val + r) i.val (le_of_lt i.isLt)]
  have : i.val + r + (k - i.val) = r + k := by omega
  rw [this, ix_add_k]

lemma rotBy_mix_rot {k : ℕ} (hk : 0 < k) (i : Fin k) (g s : ℕ) (u : W k) (r : ℕ) :
    mix hk g (rot hk s (rotBy hk i u)) (ix hk (i.val + r)) =
      mix hk g (rot hk s u) (ix hk r) := by
  have hrot : ∀ m : ℕ, rot hk s (rotBy hk i u) (ix hk (i.val + m)) = rot hk s u (ix hk m) := by
    intro m
    dsimp [rot]
    have h1 : ix hk ((ix hk (i.val + m)).val + k - s % k) = ix hk (i.val + (m + (k - s % k))) := by
      rw [ix_add_sub_mod hk (i.val + m) (s % k) (le_of_lt (Nat.mod_lt s hk))]
      congr 1; omega
    have h2 : ix hk ((ix hk m).val + k - s % k) = ix hk (m + (k - s % k)) := by
      rw [ix_add_sub_mod hk m (s % k) (le_of_lt (Nat.mod_lt s hk))]
    rw [h1, h2, rotBy_ix]
  dsimp [mix]
  have hp : ix hk ((ix hk (i.val + r)).val + g) = ix hk (i.val + (r + g)) := by
    rw [ix_add_left]; congr 1; omega
  have hp0 : ix hk ((ix hk r).val + g) = ix hk (r + g) := by
    rw [ix_add_left]
  have hm : ix hk ((ix hk (i.val + r)).val + k - g % k) = ix hk (i.val + (r + (k - g % k))) := by
    rw [ix_add_sub_mod hk (i.val + r) (g % k) (le_of_lt (Nat.mod_lt g hk))]
    congr 1; omega
  have hm0 : ix hk ((ix hk r).val + k - g % k) = ix hk (r + (k - g % k)) := by
    rw [ix_add_sub_mod hk r (g % k) (le_of_lt (Nat.mod_lt g hk))]
  rw [hp, hp0, hm, hm0, hrot r, hrot (r + g), hrot (r + (k - g % k))]

lemma rotBy_mem_bag {k : ℕ} (hk : 0 < k) (b : Bool) (i j : Fin k) :
    ix hk (j.val + k - i.val) ∈ bag hk b ⟨0, hk⟩ ↔ j ∈ bag hk b i := by
  simp only [bag, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨r, hr, heq⟩
    refine ⟨r, hr, ?_⟩
    have h1 : ix hk (0 + k - (if b then 5 else 1) % k + r + i.val) =
        ix hk (j.val + k - i.val + i.val) := by
      rw [← ix_add_left, heq, ix_add_left]
    have h2 : j.val + k - i.val + i.val = j.val + k := by have := i.isLt; omega
    rw [h2, ix_add_k, ix_val] at h1
    rw [← h1]
    have h3 : i.val + k - (if b then 5 else 1) % k + r =
        0 + k - (if b then 5 else 1) % k + r + i.val := by
      have := Nat.mod_lt (if b then 5 else 1) hk; omega
    rw [h3]
  · rintro ⟨r, hr, heq⟩
    refine ⟨r, hr, ?_⟩
    rw [← heq]
    rw [ix_add_sub_mod hk _ i.val (le_of_lt i.isLt)]
    have hlt : (if b then 5 else 1) % k < k := Nat.mod_lt _ hk
    have h3 : i.val + k - (if b then 5 else 1) % k + r + (k - i.val) =
        (0 + k - (if b then 5 else 1) % k + r) + k := by omega
    rw [h3, ix_add_k]

lemma tapRow_eq_zero_of_bag {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k) (x : W k)
    (hx : ∀ j ∈ bag hk false i, x j = 0) : tapRow hk i x = 0 := by
  funext t
  change mix hk 1 (rot hk 1 x) (ix hk (i.val + 1 + t.val)) = 0
  dsimp only [mix, rot]
  have h1k : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hmem : ∀ r < 7, ix hk (i.val + k - 1 + r) ∈ bag hk false i := by
    intro r hr
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by simp [h1k]⟩
  have hidx1 : ix hk ((ix hk (i.val + 1 + t.val)).val + k - 1 % k) = ix hk (i.val + k - 1 + (t.val + 1)) := by
    rw [h1k, ix_add_sub_mod hk (i.val + 1 + t.val) 1 (by omega)]
    congr 1; omega
  have hidx2 : ix hk ((ix hk ((ix hk (i.val + 1 + t.val)).val + 1)).val + k - 1 % k) =
      ix hk (i.val + k - 1 + (t.val + 2)) := by
    rw [ix_add_left, h1k, ix_add_sub_mod hk (i.val + 1 + t.val + 1) 1 (by omega)]
    congr 1; omega
  have hidx3 : ix hk ((ix hk ((ix hk (i.val + 1 + t.val)).val + k - 1 % k)).val + k - 1 % k) =
      ix hk (i.val + k - 1 + t.val) := by
    rw [h1k, ix_add_sub_mod hk (i.val + 1 + t.val) 1 (by omega), ix_add_sub_mod hk _ 1 (by omega)]
    have : i.val + 1 + t.val + (k - 1) + (k - 1) = (i.val + k - 1 + t.val) + k := by omega
    rw [this, ix_add_k]
  rw [hidx3, hidx1, hidx2, hx _ (hmem (t.val + 1) (by omega)), hx _ (hmem (t.val + 2) (by omega)),
      hx _ (hmem t.val (by omega))]
  simp

lemma tapCol_eq_zero_of_bag {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k) (x : W k)
    (hx : ∀ j ∈ bag hk true i, x j = 0) : tapCol hk i x = 0 := by
  funext t
  change mix hk 2 (rot hk 3 x) (ix hk (i.val + t.val)) = 0
  dsimp only [mix, rot]
  have h2k : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
  have h3k : 3 % k = 3 := Nat.mod_eq_of_lt (by omega)
  have h5k : 5 % k = 5 := Nat.mod_eq_of_lt (by omega)
  have hmem : ∀ r < 11, ix hk (i.val + k - 5 + r) ∈ bag hk true i := by
    intro r hr
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, by simp [h5k]⟩
  have hidx1 : ix hk ((ix hk (i.val + t.val)).val + k - 3 % k) = ix hk (i.val + k - 5 + (t.val + 2)) := by
    rw [h3k, ix_add_sub_mod hk (i.val + t.val) 3 (by omega)]
    congr 1; omega
  have hidx2 : ix hk ((ix hk ((ix hk (i.val + t.val)).val + 2)).val + k - 3 % k) =
      ix hk (i.val + k - 5 + (t.val + 4)) := by
    rw [ix_add_left, h3k, ix_add_sub_mod hk (i.val + t.val + 2) 3 (by omega)]
    congr 1; omega
  have hidx3 : ix hk ((ix hk ((ix hk (i.val + t.val)).val + k - 2 % k)).val + k - 3 % k) =
      ix hk (i.val + k - 5 + t.val) := by
    rw [h2k, h3k, ix_add_sub_mod hk (i.val + t.val) 2 (by omega), ix_add_sub_mod hk _ 3 (by omega)]
    have : i.val + t.val + (k - 2) + (k - 3) = (i.val + k - 5 + t.val) + k := by omega
    rw [this, ix_add_k]
  rw [hidx1, hidx2, hidx3, hx _ (hmem (t.val + 2) (by omega)), hx _ (hmem (t.val + 4) (by omega)),
      hx _ (hmem t.val (by omega))]
  simp

def liftRow0 {k : ℕ} : (Fin 5 → F) →ₗ[F] W k where
  toFun := fun t j =>
    if j.val = 1 then t 0
    else if j.val = 2 then t 0 + t 1
    else if j.val = 3 then t 1 + t 2
    else if j.val = 4 then t 0 + t 2 + t 3
    else if j.val = 5 then t 0 + t 1 + t 3 + t 4
    else 0
  map_add' := fun t1 t2 => by funext j; dsimp; split_ifs <;> ring
  map_smul' := fun c t => by
    funext j; dsimp
    rcases zmod2_cases c with rfl | rfl <;> split_ifs <;> simp

def liftRow {k : ℕ} (hk : 0 < k) (i : Fin k) : (Fin 5 → F) →ₗ[F] W k :=
  (rotBy hk i).comp liftRow0

lemma liftRow_support {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k) (t : Fin 5 → F) (j : Fin k)
    (hj : j ∉ bag hk false i) : liftRow hk i t j = 0 := by
  have hnot0 : ix hk (j.val + k - i.val) ∉ bag hk false ⟨0, hk⟩ := by
    rwa [rotBy_mem_bag]
  dsimp [liftRow, rotBy, liftRow0]
  set q := ix hk (j.val + k - i.val)
  have h1k : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hq : ∀ m, 1 ≤ m → m ≤ 5 → q.val ≠ m := by
    intro m hm1 hm5 heq
    apply hnot0
    refine Finset.mem_image.mpr ⟨m + 1, by simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_range]; omega, ?_⟩
    apply Fin.ext
    dsimp [ix]
    rw [h1k, heq]
    have : 0 + k - 1 + (m + 1) = m + k := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp only [hq 1 (by omega) (by omega), hq 2 (by omega) (by omega),
    hq 3 (by omega) (by omega), hq 4 (by omega) (by omega), hq 5 (by omega) (by omega), ↓reduceIte]

lemma tapRow_liftRow {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k) (t : Fin 5 → F) :
    tapRow hk i (liftRow hk i t) = t := by
  funext s
  have hrot : tapRow hk i (liftRow hk i t) s = mix hk 1 (rot hk 1 (liftRow0 t)) (ix hk (1 + s.val)) := by
    dsimp [tapRow, liftRow]
    have : i.val + 1 + s.val = i.val + (1 + s.val) := by omega
    rw [this, rotBy_mix_rot]
  rw [hrot]
  dsimp [mix, rot]
  have h1k : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  fin_cases s <;>
    (dsimp [liftRow0];
     try rw [h1k];
     simp only [ix, Nat.mod_eq_of_lt (show 0 < k by omega), Nat.mod_eq_of_lt (show 1 < k by omega),
       Nat.mod_eq_of_lt (show 2 < k by omega), Nat.mod_eq_of_lt (show 3 < k by omega),
       Nat.mod_eq_of_lt (show 4 < k by omega), Nat.mod_eq_of_lt (show 5 < k by omega),
       Nat.mod_eq_of_lt (show 6 < k by omega)])
  · have ha : (1 + k - 1) % k = 0 := by rw [show 1 + k - 1 = 0 + k by omega, Nat.add_mod_right]; simp
    have hb : (2 + k - 1) % k = 1 := by rw [show 2 + k - 1 = 1 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hc : ((1 + k - 1) % k + k - 1) % k = k - 1 := by rw [ha, zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [hc, ha, hb]
    have hk1 : k - 1 ≠ 1 ∧ k - 1 ≠ 2 ∧ k - 1 ≠ 3 ∧ k - 1 ≠ 4 ∧ k - 1 ≠ 5 := by omega
    simp [hk1]
  · have ha : (2 + k - 1) % k = 1 := by rw [show 2 + k - 1 = 1 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hb : (3 + k - 1) % k = 2 := by rw [show 3 + k - 1 = 2 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hc : ((2 + k - 1) % k + k - 1) % k = 0 := by rw [ha, show 1 + k - 1 = 0 + k by omega, Nat.add_mod_right]; simp
    rw [hc, ha, hb]; simp; rw [← add_assoc, zmod2_add_self, zero_add]
  · have ha : (3 + k - 1) % k = 2 := by rw [show 3 + k - 1 = 2 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hb : (4 + k - 1) % k = 3 := by rw [show 4 + k - 1 = 3 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hc : ((3 + k - 1) % k + k - 1) % k = 1 := by rw [ha, show 2 + k - 1 = 1 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    rw [hc, ha, hb]; simp
    have : t 0 + t 1 + (t 1 + t 2) + t 0 = t 2 + (t 0 + t 0) + (t 1 + t 1) := by ring
    rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
  · have ha : (4 + k - 1) % k = 3 := by rw [show 4 + k - 1 = 3 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hb : (5 + k - 1) % k = 4 := by rw [show 5 + k - 1 = 4 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hc : ((4 + k - 1) % k + k - 1) % k = 2 := by rw [ha, show 3 + k - 1 = 2 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    rw [hc, ha, hb]; simp
    have : t 1 + t 2 + (t 0 + t 2 + t 3) + (t 0 + t 1) = t 3 + (t 0 + t 0) + (t 1 + t 1) + (t 2 + t 2) := by ring
    rw [this, zmod2_add_self, zmod2_add_self, zmod2_add_self, add_zero, add_zero, add_zero]
  · have ha : (5 + k - 1) % k = 4 := by rw [show 5 + k - 1 = 4 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hb : (6 + k - 1) % k = 5 := by rw [show 6 + k - 1 = 5 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    have hc : ((5 + k - 1) % k + k - 1) % k = 3 := by rw [ha, show 4 + k - 1 = 3 + k by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    rw [hc, ha, hb]; simp
    have : t 0 + t 2 + t 3 + (t 0 + t 1 + t 3 + t 4) + (t 1 + t 2) =
        t 4 + (t 0 + t 0) + (t 1 + t 1) + (t 2 + t 2) + (t 3 + t 3) := by ring
    rw [this, zmod2_add_self, zmod2_add_self, zmod2_add_self, zmod2_add_self, add_zero, add_zero, add_zero, add_zero]

def liftCol0Fun (k : ℕ) (t : Fin 7 → F) (j : Fin k) : F :=
  if k = 7 then
    if j.val = 0 then t 1 + t 2 + t 3 + t 4 + t 5
    else if j.val = 1 then t 2 + t 3 + t 4 + t 5 + t 6
    else if j.val = 2 then t 0 + t 3 + t 4 + t 5 + t 6
    else if j.val = 3 then t 0 + t 1 + t 4 + t 5 + t 6
    else if j.val = 4 then t 0 + t 1 + t 2 + t 5 + t 6
    else if j.val = 5 then t 0 + t 1 + t 2 + t 3 + t 6
    else if j.val = 6 then t 0 + t 1 + t 2 + t 3 + t 4
    else 0
  else if k = 8 then
    if j.val = 0 then t 1 + t 3 + t 5
    else if j.val = 1 then t 2 + t 4 + t 6
    else if j.val = 2 then t 1 + t 5
    else if j.val = 3 then t 0 + t 4 + t 6
    else if j.val = 4 then t 3 + t 5
    else if j.val = 5 then t 0 + t 2 + t 6
    else if j.val = 7 then t 0 + t 2 + t 4
    else 0
  else if k = 9 then
    if j.val = 0 then t 1 + t 4 + t 6
    else if j.val = 1 then t 0 + t 2 + t 3 + t 5
    else if j.val = 2 then t 1 + t 3 + t 4 + t 6
    else if j.val = 3 then t 0 + t 2 + t 3 + t 4 + t 5
    else if j.val = 4 then t 3 + t 5
    else if j.val = 5 then t 4 + t 6
    else if j.val = 6 then t 0 + t 3 + t 5
    else 0
  else if k = 10 then
    if j.val = 0 then t 1
    else if j.val = 1 then t 0 + t 2 + t 4 + t 6
    else if j.val = 2 then t 1 + t 3
    else if j.val = 3 then t 0 + t 2 + t 6
    else if j.val = 4 then t 3 + t 5
    else if j.val = 5 then t 4 + t 6
    else if j.val = 7 then t 0 + t 4 + t 6
    else 0
  else
    if j.val = k - 1 then t 0
    else if j.val = 0 then t 1
    else if j.val = 1 then t 0 + t 2
    else if j.val = 2 then t 1 + t 3
    else if j.val = 3 then t 2 + t 4
    else if j.val = 4 then t 3 + t 5
    else if j.val = 5 then t 0 + t 4 + t 6
    else 0

lemma liftCol0Fun_add (k : ℕ) (t1 t2 : Fin 7 → F) :
    liftCol0Fun k (t1 + t2) = liftCol0Fun k t1 + liftCol0Fun k t2 := by
  funext j; dsimp only [liftCol0Fun, Pi.add_apply]
  by_cases h7 : k = 7
  · simp only [h7, ↓reduceIte]; split_ifs <;> ring
  · simp only [h7, ↓reduceIte]
    by_cases h8 : k = 8
    · simp only [h8, ↓reduceIte]; split_ifs <;> ring
    · simp only [h8, ↓reduceIte]
      by_cases h9 : k = 9
      · simp only [h9, ↓reduceIte]; split_ifs <;> ring
      · simp only [h9, ↓reduceIte]
        by_cases h10 : k = 10
        · simp only [h10, ↓reduceIte]; split_ifs <;> ring
        · simp only [h10, ↓reduceIte]; split_ifs <;> ring

def liftCol0 {k : ℕ} : (Fin 7 → F) →ₗ[F] W k where
  toFun := liftCol0Fun k
  map_add' := liftCol0Fun_add k
  map_smul' := fun c t => by
    rcases zmod2_cases c with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      have h0 : liftCol0Fun k (0 + 0) = liftCol0Fun k 0 + liftCol0Fun k 0 := liftCol0Fun_add k 0 0
      rw [add_zero] at h0
      funext j
      have hj := congrFun h0 j
      rw [Pi.add_apply, zmod2_add_self] at hj
      exact hj
    · simp [one_smul]

def liftCol {k : ℕ} (hk : 0 < k) (i : Fin k) : (Fin 7 → F) →ₗ[F] W k :=
  (rotBy hk i).comp liftCol0

lemma bag_true_eq_univ_of_le_ten {k : ℕ} (hk : 0 < k) (h10 : k ≤ 10) (i : Fin k) :
    bag hk true i = Finset.univ := by
  ext j
  simp only [bag, Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true, ↓reduceIte]
  let a := (i.val + k - 5 % k) % k
  let r := (j.val + k - a) % k
  have hr : r < 11 := by have := Nat.mod_lt (j.val + k - a) hk; omega
  refine ⟨r, hr, ?_⟩
  apply Fin.ext
  dsimp [ix]
  have ha : a < k := Nat.mod_lt _ hk
  have hrk : r < k := Nat.mod_lt _ hk
  have h1 : (i.val + k - 5 % k + r) % k = (a + r) % k :=
    calc (i.val + k - 5 % k + r) % k
        = ((i.val + k - 5 % k) % k + r % k) % k := Nat.add_mod _ _ _
      _ = (a + r % k) % k := rfl
      _ = (a % k + r % k) % k := by rw [Nat.mod_eq_of_lt ha]
      _ = (a + r) % k := (Nat.add_mod a r k).symm
  rw [h1]
  have h2 : (a + r) % k = (a + (j.val + k - a)) % k :=
    calc (a + r) % k
        = (a % k + r % k) % k := Nat.add_mod a r k
      _ = (a % k + r) % k := by rw [Nat.mod_eq_of_lt hrk]
      _ = (a % k + (j.val + k - a) % k) % k := rfl
      _ = (a + (j.val + k - a)) % k := (Nat.add_mod a _ k).symm
  rw [h2, show a + (j.val + k - a) = j.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

lemma liftCol_support {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k) (t : Fin 7 → F) (j : Fin k)
    (hj : j ∉ bag hk true i) : liftCol hk i t j = 0 := by
  by_cases h11 : 11 ≤ k
  · have hnot0 : ix hk (j.val + k - i.val) ∉ bag hk true ⟨0, hk⟩ := by
      rwa [rotBy_mem_bag]
    dsimp [liftCol, rotBy, liftCol0, liftCol0Fun]
    have hne7 : k ≠ 7 := by omega
    have hne8 : k ≠ 8 := by omega
    have hne9 : k ≠ 9 := by omega
    have hne10 : k ≠ 10 := by omega
    simp only [hne7, hne8, hne9, hne10, ↓reduceIte]
    set q := ix hk (j.val + k - i.val)
    have h5k : 5 % k = 5 := Nat.mod_eq_of_lt (by omega)
    have hq_km1 : q.val ≠ k - 1 := by
      intro heq; apply hnot0
      refine Finset.mem_image.mpr ⟨4, by simp only [↓reduceIte, Finset.mem_range]; omega, ?_⟩
      apply Fin.ext; dsimp [ix]; rw [h5k, heq]
      have : 0 + k - 5 + 4 = k - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have hq_le5 : ∀ m, m ≤ 5 → q.val ≠ m := by
      intro m hm heq; apply hnot0
      refine Finset.mem_image.mpr ⟨m + 5, by simp only [↓reduceIte, Finset.mem_range]; omega, ?_⟩
      apply Fin.ext; dsimp [ix]; rw [h5k, heq]
      have : 0 + k - 5 + (m + 5) = m + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [hq_km1, hq_le5 0 (by omega), hq_le5 1 (by omega), hq_le5 2 (by omega),
      hq_le5 3 (by omega), hq_le5 4 (by omega), hq_le5 5 (by omega), ↓reduceIte]
  · exfalso
    have hu := bag_true_eq_univ_of_le_ten hk (by omega) i
    rw [hu] at hj
    exact hj (Finset.mem_univ j)

lemma zmod2_ring_cancel (a b : F) : a + b + a = b := by
  have : a + b + a = b + (a + a) := by ring
  rw [this, zmod2_add_self, add_zero]

lemma tapCol_liftCol_small (k : ℕ) (hk : 0 < k) (hcases : k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10)
    (t : Fin 7 → F) (s : Fin 7) :
    mix hk 2 (rot hk 3 (liftCol0 t)) (ix hk s.val) = t s := by
  have h3 : (3 : F) = 1 := by decide
  have h4 : (4 : F) = 0 := by decide
  rcases hcases with rfl | rfl | rfl | rfl <;>
    fin_cases s <;>
    (dsimp [mix, rot, ix, liftCol0, liftCol0Fun];
     norm_num;
     try ring_nf;
     try simp only [zmod2_two, h3, h4, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add])

lemma tapCol_liftCol {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (i : Fin k) (t : Fin 7 → F) :
    tapCol hk i (liftCol hk i t) = t := by
  funext s
  have hrot : tapCol hk i (liftCol hk i t) s = mix hk 2 (rot hk 3 (liftCol0 t)) (ix hk s.val) := by
    dsimp [tapCol, liftCol]
    exact rotBy_mix_rot hk i 2 3 (liftCol0 t) s.val
  rw [hrot]
  by_cases h11 : 11 ≤ k
  · dsimp [mix, rot]
    have h2k : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    have h3k : 3 % k = 3 := Nat.mod_eq_of_lt (by omega)
    have h5k : 5 % k = 5 := Nat.mod_eq_of_lt (by omega)
    have hidx1 : (ix hk ((ix hk s.val).val + k - 3 % k)).val = (s.val + k - 3) % k := by
      rw [h3k, ix_add_sub_mod hk s.val 3 (by omega)]; dsimp [ix]; congr 1; omega
    have hidx2 : (ix hk ((ix hk ((ix hk s.val).val + 2)).val + k - 3 % k)).val = (s.val + k - 1) % k := by
      rw [ix_add_left, h3k, ix_add_sub_mod hk (s.val + 2) 3 (by omega)]; dsimp [ix]; congr 1; omega
    have hidx3 : (ix hk ((ix hk ((ix hk s.val).val + k - 2 % k)).val + k - 3 % k)).val = (s.val + k - 5) % k := by
      rw [h2k, h3k, ix_add_sub_mod hk s.val 2 (by omega), ix_add_sub_mod hk _ 3 (by omega)]
      have : s.val + (k - 2) + (k - 3) = (s.val + k - 5) + k := by omega
      rw [this, ix_add_k]; rfl
    have heval : ∀ (j : Fin k), liftCol0 t j =
        if j.val = k - 1 then t 0
        else if j.val = 0 then t 1
        else if j.val = 1 then t 0 + t 2
        else if j.val = 2 then t 1 + t 3
        else if j.val = 3 then t 2 + t 4
        else if j.val = 4 then t 3 + t 5
        else if j.val = 5 then t 0 + t 4 + t 6
        else 0 := by
      intro j; dsimp [liftCol0, liftCol0Fun]
      have hne7 : k ≠ 7 := by omega
      have hne8 : k ≠ 8 := by omega
      have hne9 : k ≠ 9 := by omega
      have hne10 : k ≠ 10 := by omega
      simp only [hne7, hne8, hne9, hne10, ↓reduceIte]
    rw [heval, heval, heval, hidx1, hidx2, hidx3]
    have hm_sub : ∀ d : ℕ, 1 ≤ d → d ≤ 5 → (k - d) % k = k - d := fun d _ _ => Nat.mod_eq_of_lt (by omega)
    have hm_add : ∀ d : ℕ, d ≤ 5 → (k + d) % k = d := fun d _ => by
      rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    fin_cases s
    · simp only [Fin.val_zero, zero_add, hm_sub 3 (by omega) (by omega), hm_sub 1 (by omega) (by omega),
        hm_sub 5 (by omega) (by omega)]
      have h3 : k - 3 ≠ k - 1 ∧ k - 3 ≠ 0 ∧ k - 3 ≠ 1 ∧ k - 3 ≠ 2 ∧ k - 3 ≠ 3 ∧ k - 3 ≠ 4 ∧ k - 3 ≠ 5 := by omega
      have h5 : k - 5 ≠ k - 1 ∧ k - 5 ≠ 0 ∧ k - 5 ≠ 1 ∧ k - 5 ≠ 2 ∧ k - 5 ≠ 3 ∧ k - 5 ≠ 4 ∧ k - 5 ≠ 5 := by omega
      simp [h3, h5]
    · have ha : (1 + k - 3) % k = k - 2 := by rw [show 1 + k - 3 = k - 2 by omega]; exact hm_sub 2 (by omega) (by omega)
      have hb : (1 + k - 1) % k = 0 := by rw [show 1 + k - 1 = k + 0 by omega]; exact hm_add 0 (by omega)
      have hc : (1 + k - 5) % k = k - 4 := by rw [show 1 + k - 5 = k - 4 by omega]; exact hm_sub 4 (by omega) (by omega)
      simp only [Fin.val_one, ha, hb, hc]
      have h2 : k - 2 ≠ k - 1 ∧ k - 2 ≠ 0 ∧ k - 2 ≠ 1 ∧ k - 2 ≠ 2 ∧ k - 2 ≠ 3 ∧ k - 2 ≠ 4 ∧ k - 2 ≠ 5 := by omega
      have h4 : k - 4 ≠ k - 1 ∧ k - 4 ≠ 0 ∧ k - 4 ≠ 1 ∧ k - 4 ≠ 2 ∧ k - 4 ≠ 3 ∧ k - 4 ≠ 4 ∧ k - 4 ≠ 5 := by omega
      have h0 : 0 ≠ k - 1 := by omega
      simp [h2, h4, h0]
    · have ha : (2 + k - 3) % k = k - 1 := by rw [show 2 + k - 3 = k - 1 by omega]; exact hm_sub 1 (by omega) (by omega)
      have hb : (2 + k - 1) % k = 1 := by rw [show 2 + k - 1 = k + 1 by omega]; exact hm_add 1 (by omega)
      have hc : (2 + k - 5) % k = k - 3 := by rw [show 2 + k - 5 = k - 3 by omega]; exact hm_sub 3 (by omega) (by omega)
      simp only [Fin.val_two, ha, hb, hc]
      have h3 : k - 3 ≠ k - 1 ∧ k - 3 ≠ 0 ∧ k - 3 ≠ 1 ∧ k - 3 ≠ 2 ∧ k - 3 ≠ 3 ∧ k - 3 ≠ 4 ∧ k - 3 ≠ 5 := by omega
      have h1 : 1 ≠ k - 1 := by omega
      simp [h3, h1]; rw [← add_assoc, zmod2_add_self, zero_add]
    · have ha : (3 + k - 3) % k = 0 := by rw [show 3 + k - 3 = k + 0 by omega]; exact hm_add 0 (by omega)
      have hb : (3 + k - 1) % k = 2 := by rw [show 3 + k - 1 = k + 2 by omega]; exact hm_add 2 (by omega)
      have hc : (3 + k - 5) % k = k - 2 := by rw [show 3 + k - 5 = k - 2 by omega]; exact hm_sub 2 (by omega) (by omega)
      dsimp only [Fin.isValue]
      rw [ha, hb, hc]
      have h2 : k - 2 ≠ k - 1 ∧ k - 2 ≠ 0 ∧ k - 2 ≠ 1 ∧ k - 2 ≠ 2 ∧ k - 2 ≠ 3 ∧ k - 2 ≠ 4 ∧ k - 2 ≠ 5 := by omega
      have h02 : 0 ≠ k - 1 ∧ 2 ≠ k - 1 := by omega
      simp [h2, h02]; rw [← add_assoc, zmod2_add_self, zero_add]
    · have ha : (4 + k - 3) % k = 1 := by rw [show 4 + k - 3 = k + 1 by omega]; exact hm_add 1 (by omega)
      have hb : (4 + k - 1) % k = 3 := by rw [show 4 + k - 1 = k + 3 by omega]; exact hm_add 3 (by omega)
      have hc : (4 + k - 5) % k = k - 1 := by rw [show 4 + k - 5 = k - 1 by omega]; exact hm_sub 1 (by omega) (by omega)
      dsimp only [Fin.isValue]
      rw [ha, hb, hc]
      have h13 : 1 ≠ k - 1 ∧ 3 ≠ k - 1 := by omega
      simp [h13]
      have : t 0 + t 2 + (t 2 + t 4) + t 0 = t 4 + (t 0 + t 0) + (t 2 + t 2) := by ring
      rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
    · have ha : (5 + k - 3) % k = 2 := by rw [show 5 + k - 3 = k + 2 by omega]; exact hm_add 2 (by omega)
      have hb : (5 + k - 1) % k = 4 := by rw [show 5 + k - 1 = k + 4 by omega]; exact hm_add 4 (by omega)
      have hc : (5 + k - 5) % k = 0 := by rw [show 5 + k - 5 = k + 0 by omega]; exact hm_add 0 (by omega)
      dsimp only [Fin.isValue]
      rw [ha, hb, hc]
      have h024 : 0 ≠ k - 1 ∧ 2 ≠ k - 1 ∧ 4 ≠ k - 1 := by omega
      simp [h024]
      have : t 1 + t 3 + (t 3 + t 5) + t 1 = t 5 + (t 1 + t 1) + (t 3 + t 3) := by ring
      rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
    · have ha : (6 + k - 3) % k = 3 := by rw [show 6 + k - 3 = k + 3 by omega]; exact hm_add 3 (by omega)
      have hb : (6 + k - 1) % k = 5 := by rw [show 6 + k - 1 = k + 5 by omega]; exact hm_add 5 (by omega)
      have hc : (6 + k - 5) % k = 1 := by rw [show 6 + k - 5 = k + 1 by omega]; exact hm_add 1 (by omega)
      dsimp only [Fin.isValue]
      rw [ha, hb, hc]
      have h135 : 1 ≠ k - 1 ∧ 3 ≠ k - 1 ∧ 5 ≠ k - 1 := by omega
      simp [h135]
      have : t 2 + t 4 + (t 0 + t 4 + t 6) + (t 0 + t 2) = t 6 + (t 0 + t 0) + (t 2 + t 2) + (t 4 + t 4) := by ring
      rw [this, zmod2_add_self, zmod2_add_self, zmod2_add_self, add_zero, add_zero, add_zero]
  · exact tapCol_liftCol_small k hk (by omega) t s

lemma fourth_P_row_nonzero :
    ∃ v : Fin 4 → (Fin 5 → F), fourth P_row v 0 ≠ 0 := by
  let v : Fin 4 → (Fin 5 → F) := fun r j => if j.val = r.val then 1 else 0
  refine ⟨v, ?_⟩
  rw [fourth_eq_sum16]
  have h1 : ∀ b : Fin 4 → Bool, P_row (cubePt 0 v b) =
      if b 0 = true ∧ b 1 = true ∧ b 2 = true ∧ b 3 = true then 1 else 0 := by
    intro b
    have hite : ∀ (c : Bool) (u : Fin 5 → F) (j : Fin 5),
        (if c then u else 0) j = if c then u j else 0 := fun c u j => by cases c <;> rfl
    have hc : ∀ j : Fin 5, cubePt 0 v b j =
        if hj : j.val < 4 then (if b ⟨j.val, hj⟩ then 1 else 0) else 0 := by
      intro j
      simp only [cubePt, Pi.add_apply, Pi.zero_apply, hite, v]
      fin_cases j <;> simp
    dsimp [P_row]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 5).val = 3 from rfl,
      show (4 : Fin 5).val = 4 from rfl, show 0 < 4 by omega, show 1 < 4 by omega,
      show 2 < 4 by omega, show 3 < 4 by omega, show ¬ (4 < 4) by omega, ↓reduceDIte,
      mul_zero, add_zero]
    change (if b 0 = true then (1 : F) else 0) * (if b 1 = true then 1 else 0) *
      (if b 2 = true then 1 else 0) * (if b 3 = true then 1 else 0) = _
    cases b 0 <;> cases b 1 <;> cases b 2 <;> cases b 3 <;> simp
  simp_rw [h1]
  rw [Finset.sum_eq_single (fun _ => true)]
  · simp
  · intro b _ hb
    have hnot : ¬ (b 0 = true ∧ b 1 = true ∧ b 2 = true ∧ b 3 = true) := by
      intro ⟨h0, h1, h2, h3⟩
      apply hb; funext r; fin_cases r <;> assumption
    simp [hnot]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma fourth_P_col_hyperplane (w : Fin 7 → F) (hw : w ≠ 0) :
    ∃ v : Fin 4 → (Fin 7 → F),
      (∀ r, ∑ j : Fin 7, w j * v r j = 0) ∧ fourth P_col v 0 ≠ 0 := by
  have hex : ∃ p : Fin 7, w p = 1 := by
    by_contra h
    push Not at h
    apply hw; funext p
    rcases zmod2_cases (w p) with h0 | h1
    · exact h0
    · exact absurd h1 (h p)
  obtain ⟨p, hp⟩ := hex
  let mkWitness (s : Fin 4 → Fin 7) : Fin 4 → (Fin 7 → F) :=
    fun r j => (if j = s r then 1 else 0) + (if j = p then w (s r) else 0)
  have hker : ∀ s : Fin 4 → Fin 7, ∀ r, ∑ j : Fin 7, w j * mkWitness s r j = 0 := by
    intro s r
    dsimp [mkWitness]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have h1 : ∑ j : Fin 7, w j * (if j = s r then 1 else 0) = w (s r) := by
      rw [Finset.sum_eq_single (s r)]
      · simp
      · intro j _ hj; simp [hj]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    have h2 : ∑ j : Fin 7, w j * (if j = p then w (s r) else 0) = w (s r) := by
      rw [Finset.sum_eq_single p]
      · simp [hp]
      · intro j _ hj; simp [hj]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [h1, h2, zmod2_add_self]
  have hcube_eval : ∀ (s : Fin 4 → Fin 7) (hs_inj : Function.Injective s)
      (hs_np : ∀ r, s r ≠ p) (b : Fin 4 → Bool) (j : Fin 7),
      cubePt 0 (mkWitness s) b j =
        (if j = p then
          (if b 0 then w (s 0) else 0) + (if b 1 then w (s 1) else 0) +
          (if b 2 then w (s 2) else 0) + (if b 3 then w (s 3) else 0)
        else if j = s 0 then (if b 0 then 1 else 0)
        else if j = s 1 then (if b 1 then 1 else 0)
        else if j = s 2 then (if b 2 then 1 else 0)
        else if j = s 3 then (if b 3 then 1 else 0)
        else 0) := by
    intro s hs_inj hs_np b j
    have hite : ∀ (c : Bool) (u : Fin 7 → F) (j : Fin 7),
        (if c then u else 0) j = if c then u j else 0 := fun c u j => by cases c <;> rfl
    simp only [cubePt, Pi.add_apply, Pi.zero_apply, hite, mkWitness, zero_add]
    have hne : ∀ r1 r2 : Fin 4, r1 ≠ r2 → s r1 ≠ s r2 := fun r1 r2 h h' => h (hs_inj h')
    by_cases hjp : j = p
    · subst hjp
      simp only [Ne.symm (hs_np 0), Ne.symm (hs_np 1), Ne.symm (hs_np 2), Ne.symm (hs_np 3),
        ↓reduceIte, zero_add]
    · simp only [hjp, ↓reduceIte, add_zero]
      by_cases h0 : j = s 0
      · subst h0
        simp only [↓reduceIte, hne 0 1 (by decide), hne 0 2 (by decide), hne 0 3 (by decide),
          ite_self, add_zero]
      · simp only [h0, ↓reduceIte, ite_self, zero_add]
        by_cases h1 : j = s 1
        · subst h1
          simp only [↓reduceIte, hne 1 2 (by decide), hne 1 3 (by decide), ite_self, add_zero]
        · simp only [h1, ↓reduceIte, ite_self, zero_add]
          by_cases h2 : j = s 2
          · subst h2
            simp only [↓reduceIte, hne 2 3 (by decide), ite_self, add_zero]
          · simp only [h2, ↓reduceIte, ite_self, zero_add]
            by_cases h3 : j = s 3
            · subst h3
              simp only [↓reduceIte]
            · simp only [h3, ↓reduceIte, ite_self]
  have hfinish : ∀ (s : Fin 4 → Fin 7),
      (∀ b : Fin 4 → Bool, P_col (cubePt 0 (mkWitness s) b) =
        if b 0 = true ∧ b 1 = true ∧ b 2 = true ∧ b 3 = true then 1 else 0) →
      ∃ v : Fin 4 → (Fin 7 → F),
        (∀ r, ∑ j : Fin 7, w j * v r j = 0) ∧ fourth P_col v 0 ≠ 0 := by
    intro s hval
    refine ⟨mkWitness s, hker s, ?_⟩
    rw [fourth_eq_sum16]
    simp_rw [hval]
    rw [Finset.sum_eq_single (fun _ => true)]
    · simp
    · intro b _ hb
      have hnot : ¬ (b 0 = true ∧ b 1 = true ∧ b 2 = true ∧ b 3 = true) := by
        intro ⟨h0, h1, h2, h3⟩; apply hb; funext r; fin_cases r <;> assumption
      simp [hnot]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  fin_cases p
  · let s : Fin 4 → Fin 7 := fun r => match r.val with | 0 => 2 | 1 => 3 | 2 => 5 | _ => 6
    refine hfinish s (fun b => ?_)
    have hc := hcube_eval s (by intro a c h; fin_cases a <;> fin_cases c <;> simp [s] at h ⊢)
      (by intro r; fin_cases r <;> decide) b
    dsimp [P_col]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6]
    dsimp [s]
    simp only [show (1 : Fin 7) ≠ 0 by decide, show (1 : Fin 7) ≠ 2 by decide, show (1 : Fin 7) ≠ 3 by decide,
      show (1 : Fin 7) ≠ 5 by decide, show (1 : Fin 7) ≠ 6 by decide,
      show (2 : Fin 7) ≠ 0 by decide, show (3 : Fin 7) ≠ 0 by decide, show (3 : Fin 7) ≠ 2 by decide,
      show (5 : Fin 7) ≠ 0 by decide, show (5 : Fin 7) ≠ 2 by decide, show (5 : Fin 7) ≠ 3 by decide,
      show (6 : Fin 7) ≠ 0 by decide, show (6 : Fin 7) ≠ 2 by decide, show (6 : Fin 7) ≠ 3 by decide,
      show (6 : Fin 7) ≠ 5 by decide, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add]
    cases b 0 <;> cases b 1 <;> cases b 2 <;> cases b 3 <;> simp
  · let s : Fin 4 → Fin 7 := fun r => match r.val with | 0 => 2 | 1 => 3 | 2 => 5 | _ => 6
    refine hfinish s (fun b => ?_)
    have hc := hcube_eval s (by intro a c h; fin_cases a <;> fin_cases c <;> simp [s] at h ⊢)
      (by intro r; fin_cases r <;> decide) b
    dsimp [P_col]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6]
    dsimp [s]
    simp only [show (0 : Fin 7) ≠ 1 by decide, show (0 : Fin 7) ≠ 2 by decide, show (0 : Fin 7) ≠ 3 by decide,
      show (0 : Fin 7) ≠ 5 by decide, show (0 : Fin 7) ≠ 6 by decide,
      show (4 : Fin 7) ≠ 1 by decide, show (4 : Fin 7) ≠ 2 by decide, show (4 : Fin 7) ≠ 3 by decide,
      show (4 : Fin 7) ≠ 5 by decide, show (4 : Fin 7) ≠ 6 by decide,
      show (2 : Fin 7) ≠ 1 by decide, show (3 : Fin 7) ≠ 1 by decide, show (3 : Fin 7) ≠ 2 by decide,
      show (5 : Fin 7) ≠ 1 by decide, show (5 : Fin 7) ≠ 2 by decide, show (5 : Fin 7) ≠ 3 by decide,
      show (6 : Fin 7) ≠ 1 by decide, show (6 : Fin 7) ≠ 2 by decide, show (6 : Fin 7) ≠ 3 by decide,
      show (6 : Fin 7) ≠ 5 by decide, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add]
    cases b 0 <;> cases b 1 <;> cases b 2 <;> cases b 3 <;> simp
  · let s : Fin 4 → Fin 7 := fun r => match r.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 4
    refine hfinish s (fun b => ?_)
    have hc := hcube_eval s (by intro a c h; fin_cases a <;> fin_cases c <;> simp [s] at h ⊢)
      (by intro r; fin_cases r <;> decide) b
    dsimp [P_col]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6]
    dsimp [s]
    simp only [show (5 : Fin 7) ≠ 2 by decide, show (5 : Fin 7) ≠ 0 by decide, show (5 : Fin 7) ≠ 1 by decide,
      show (5 : Fin 7) ≠ 3 by decide, show (5 : Fin 7) ≠ 4 by decide,
      show (0 : Fin 7) ≠ 2 by decide, show (1 : Fin 7) ≠ 2 by decide, show (1 : Fin 7) ≠ 0 by decide,
      show (3 : Fin 7) ≠ 2 by decide, show (3 : Fin 7) ≠ 0 by decide, show (3 : Fin 7) ≠ 1 by decide,
      show (4 : Fin 7) ≠ 2 by decide, show (4 : Fin 7) ≠ 0 by decide, show (4 : Fin 7) ≠ 1 by decide,
      show (4 : Fin 7) ≠ 3 by decide, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add]
    cases b 0 <;> cases b 1 <;> cases b 2 <;> cases b 3 <;> simp
  · let s : Fin 4 → Fin 7 := fun r => match r.val with | 0 => 0 | 1 => 1 | 2 => 5 | _ => 6
    refine hfinish s (fun b => ?_)
    have hc := hcube_eval s (by intro a c h; fin_cases a <;> fin_cases c <;> simp [s] at h ⊢)
      (by intro r; fin_cases r <;> decide) b
    dsimp [P_col]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6]
    dsimp [s]
    simp only [show (2 : Fin 7) ≠ 3 by decide, show (2 : Fin 7) ≠ 0 by decide, show (2 : Fin 7) ≠ 1 by decide,
      show (2 : Fin 7) ≠ 5 by decide, show (2 : Fin 7) ≠ 6 by decide,
      show (4 : Fin 7) ≠ 3 by decide, show (4 : Fin 7) ≠ 0 by decide, show (4 : Fin 7) ≠ 1 by decide,
      show (4 : Fin 7) ≠ 5 by decide, show (4 : Fin 7) ≠ 6 by decide,
      show (0 : Fin 7) ≠ 3 by decide, show (1 : Fin 7) ≠ 3 by decide, show (1 : Fin 7) ≠ 0 by decide,
      show (5 : Fin 7) ≠ 3 by decide, show (5 : Fin 7) ≠ 0 by decide, show (5 : Fin 7) ≠ 1 by decide,
      show (6 : Fin 7) ≠ 3 by decide, show (6 : Fin 7) ≠ 0 by decide, show (6 : Fin 7) ≠ 1 by decide,
      show (6 : Fin 7) ≠ 5 by decide, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add]
    cases b 0 <;> cases b 1 <;> cases b 2 <;> cases b 3 <;> simp
  · let s : Fin 4 → Fin 7 := fun r => match r.val with | 0 => 0 | 1 => 1 | 2 => 5 | _ => 6
    refine hfinish s (fun b => ?_)
    have hc := hcube_eval s (by intro a c h; fin_cases a <;> fin_cases c <;> simp [s] at h ⊢)
      (by intro r; fin_cases r <;> decide) b
    dsimp [P_col]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6]
    dsimp [s]
    simp only [show (2 : Fin 7) ≠ 4 by decide, show (2 : Fin 7) ≠ 0 by decide, show (2 : Fin 7) ≠ 1 by decide,
      show (2 : Fin 7) ≠ 5 by decide, show (2 : Fin 7) ≠ 6 by decide,
      show (3 : Fin 7) ≠ 4 by decide, show (3 : Fin 7) ≠ 0 by decide, show (3 : Fin 7) ≠ 1 by decide,
      show (3 : Fin 7) ≠ 5 by decide, show (3 : Fin 7) ≠ 6 by decide,
      show (0 : Fin 7) ≠ 4 by decide, show (1 : Fin 7) ≠ 4 by decide, show (1 : Fin 7) ≠ 0 by decide,
      show (5 : Fin 7) ≠ 4 by decide, show (5 : Fin 7) ≠ 0 by decide, show (5 : Fin 7) ≠ 1 by decide,
      show (6 : Fin 7) ≠ 4 by decide, show (6 : Fin 7) ≠ 0 by decide, show (6 : Fin 7) ≠ 1 by decide,
      show (6 : Fin 7) ≠ 5 by decide, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add]
    cases b 0 <;> cases b 1 <;> cases b 2 <;> cases b 3 <;> simp
  · let s : Fin 4 → Fin 7 := fun r => match r.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 4
    refine hfinish s (fun b => ?_)
    have hc := hcube_eval s (by intro a c h; fin_cases a <;> fin_cases c <;> simp [s] at h ⊢)
      (by intro r; fin_cases r <;> decide) b
    dsimp [P_col]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6]
    dsimp [s]
    simp only [show (2 : Fin 7) ≠ 5 by decide, show (2 : Fin 7) ≠ 0 by decide, show (2 : Fin 7) ≠ 1 by decide,
      show (2 : Fin 7) ≠ 3 by decide, show (2 : Fin 7) ≠ 4 by decide,
      show (6 : Fin 7) ≠ 5 by decide, show (6 : Fin 7) ≠ 0 by decide, show (6 : Fin 7) ≠ 1 by decide,
      show (6 : Fin 7) ≠ 3 by decide, show (6 : Fin 7) ≠ 4 by decide,
      show (0 : Fin 7) ≠ 5 by decide, show (1 : Fin 7) ≠ 5 by decide, show (1 : Fin 7) ≠ 0 by decide,
      show (3 : Fin 7) ≠ 5 by decide, show (3 : Fin 7) ≠ 0 by decide, show (3 : Fin 7) ≠ 1 by decide,
      show (4 : Fin 7) ≠ 5 by decide, show (4 : Fin 7) ≠ 0 by decide, show (4 : Fin 7) ≠ 1 by decide,
      show (4 : Fin 7) ≠ 3 by decide, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add]
    cases b 0 <;> cases b 1 <;> cases b 2 <;> cases b 3 <;> simp
  · let s : Fin 4 → Fin 7 := fun r => match r.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 4
    refine hfinish s (fun b => ?_)
    have hc := hcube_eval s (by intro a c h; fin_cases a <;> fin_cases c <;> simp [s] at h ⊢)
      (by intro r; fin_cases r <;> decide) b
    dsimp [P_col]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6]
    dsimp [s]
    simp only [show (5 : Fin 7) ≠ 6 by decide, show (5 : Fin 7) ≠ 0 by decide, show (5 : Fin 7) ≠ 1 by decide,
      show (5 : Fin 7) ≠ 3 by decide, show (5 : Fin 7) ≠ 4 by decide,
      show (0 : Fin 7) ≠ 6 by decide, show (1 : Fin 7) ≠ 6 by decide, show (1 : Fin 7) ≠ 0 by decide,
      show (3 : Fin 7) ≠ 6 by decide, show (3 : Fin 7) ≠ 0 by decide, show (3 : Fin 7) ≠ 1 by decide,
      show (4 : Fin 7) ≠ 6 by decide, show (4 : Fin 7) ≠ 0 by decide, show (4 : Fin 7) ≠ 1 by decide,
      show (4 : Fin 7) ≠ 3 by decide, ↓reduceIte, mul_zero, zero_mul, add_zero, zero_add]
    cases b 0 <;> cases b 1 <;> cases b 2 <;> cases b 3 <;> simp

lemma card_two_mul_of_proper {n : ℕ} (U : Submodule F (Fin n → F)) (hU : ∃ b, b ∉ U) :
    2 * Fintype.card U ≤ 2 ^ n := by
  obtain ⟨b, hb⟩ := hU
  let S0 : Finset (Fin n → F) := Finset.univ.filter (fun x => x ∈ U)
  let S1 : Finset (Fin n → F) := S0.image (fun x => x + b)
  have hcard0 : S0.card = Fintype.card U := by
    rw [Fintype.card_subtype]
  have hcard1 : S1.card = S0.card :=
    Finset.card_image_of_injective S0 (fun x y h => add_right_cancel h)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    obtain ⟨y, hy0, rfl⟩ := Finset.mem_image.mp hx1
    have hyU : y ∈ U := (Finset.mem_filter.mp hy0).2
    have hxyU : y + b ∈ U := (Finset.mem_filter.mp hx0).2
    have hbU : b ∈ U := by
      have : b = (y + b) - y := by abel
      rw [this]; exact U.sub_mem hxyU hyU
    exact hb hbU
  have hle : (S0 ∪ S1).card ≤ (Finset.univ : Finset (Fin n → F)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hdisj, hcard1, hcard0, Finset.card_univ,
      Fintype.card_fun, ZMod.card 2, Fintype.card_fin] at hle
  omega

lemma card_le_row (U : Submodule F (Fin 5 → F))
    (h : ∀ v : Fin 4 → (Fin 5 → F), (∀ r, v r ∈ U) → fourth P_row v 0 = 0) :
    2 * Fintype.card U ≤ 2 ^ 5 := by
  apply card_two_mul_of_proper U
  by_contra hall
  push Not at hall
  obtain ⟨v, hv⟩ := fourth_P_row_nonzero
  exact hv (h v (fun r => hall (v r)))

lemma card_le_col (U : Submodule F (Fin 7 → F))
    (h : ∀ v : Fin 4 → (Fin 7 → F), (∀ r, v r ∈ U) → fourth P_col v 0 = 0) :
    4 * Fintype.card U ≤ 2 ^ 7 := by
  have hproper : ∃ b, b ∉ U := by
    by_contra hall
    push Not at hall
    obtain ⟨v, _, hv⟩ := fourth_P_col_hyperplane (fun j => if j = 0 then 1 else 0)
      (fun h0 => by have := congrFun h0 0; simp at this)
    exact hv (h v (fun r => hall (v r)))
  obtain ⟨b, hb⟩ := hproper
  let U1 : Submodule F (Fin 7 → F) :=
    { carrier := {x | x ∈ U ∨ x + b ∈ U}, add_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (U.add_mem hx hy)
        · refine Or.inr ?_
          have : x + y + b = x + (y + b) := by abel
          rw [this]; exact U.add_mem hx hy
        · refine Or.inr ?_
          have : x + y + b = (x + b) + y := by abel
          rw [this]; exact U.add_mem hx hy
        · refine Or.inl ?_
          have hbb : b + b = 0 := by funext j; exact zmod2_add_self (b j)
          have : x + y = (x + b) + (y + b) := by
            calc x + y = x + y + (b + b) := by rw [hbb, add_zero]
              _ = (x + b) + (y + b) := by abel
          rw [this]; exact U.add_mem hx hy
      zero_mem' := Or.inl U.zero_mem
      smul_mem' := fun c x hx => by
        rcases zmod2_cases c with rfl | rfl
        · simp
        · simpa using hx }
  have hcard_U1 : Fintype.card U1 = 2 * Fintype.card U := by
    let S0 : Finset (Fin 7 → F) := Finset.univ.filter (fun x => x ∈ U)
    let S1 : Finset (Fin 7 → F) := S0.image (fun x => x + b)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro x hx0 hx1
      obtain ⟨y, hy0, rfl⟩ := Finset.mem_image.mp hx1
      have : b = (y + b) - y := by abel
      exact hb (this ▸ U.sub_mem (Finset.mem_filter.mp hx0).2 (Finset.mem_filter.mp hy0).2)
    have heq : Finset.univ.filter (fun x => x ∈ U1) = S0 ∪ S1 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image, S0, S1, U1,
        Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
      constructor
      · rintro (hx | hxb)
        · exact Or.inl hx
        · refine Or.inr ⟨x + b, hxb, ?_⟩
          have hbb : b + b = 0 := by funext j; exact zmod2_add_self (b j)
          rw [add_assoc, hbb, add_zero]
      · rintro (hx | ⟨y, hy, rfl⟩)
        · exact Or.inl hx
        · refine Or.inr ?_
          have hbb : b + b = 0 := by funext j; exact zmod2_add_self (b j)
          rw [add_assoc, hbb, add_zero]; exact hy
    rw [Fintype.card_subtype, heq, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective S0 (fun x y hxy => add_right_cancel hxy),
        Fintype.card_subtype]
    dsimp only [S0]
    omega
  by_cases hU1_prop : ∃ c, c ∉ U1
  · have hle := card_two_mul_of_proper U1 hU1_prop
    rw [hcard_U1] at hle
    omega
  · exfalso
    push Not at hU1_prop
    let ell : (Fin 7 → F) → F := fun x => if x ∈ U then 0 else 1
    have hell_add : ∀ x y, ell (x + y) = ell x + ell y := by
      intro x y
      by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
      · simp only [ell, hx, hy, U.add_mem hx hy, ↓reduceIte, add_zero]
      · have hnot : x + y ∉ U := fun hxy => hy (by
          have : y = (x + y) - x := by abel
          rw [this]; exact U.sub_mem hxy hx)
        simp only [ell, hx, hy, hnot, ↓reduceIte, zero_add]
      · have hnot : x + y ∉ U := fun hxy => hx (by
          have : x = (x + y) - y := by abel
          rw [this]; exact U.sub_mem hxy hy)
        simp only [ell, hx, hy, hnot, ↓reduceIte, add_zero]
      · have hxb : x + b ∈ U := (hU1_prop x).resolve_left hx
        have hyb : y + b ∈ U := (hU1_prop y).resolve_left hy
        have hxy : x + y ∈ U := by
          have hbb : b + b = 0 := by funext j; exact zmod2_add_self (b j)
          have : x + y = (x + b) + (y + b) := by
            calc x + y = x + y + (b + b) := by rw [hbb, add_zero]
              _ = (x + b) + (y + b) := by abel
          rw [this]; exact U.add_mem hxb hyb
        simp only [ell, hx, hy, hxy, ↓reduceIte, zmod2_add_self]
    let e : Fin 7 → (Fin 7 → F) := fun j r => if r = j then 1 else 0
    let w : Fin 7 → F := fun j => ell (e j)
    have hell_dot : ∀ x : Fin 7 → F, ell x = ∑ j : Fin 7, w j * x j := by
      intro x
      have hx_sum : x = ∑ j : Fin 7, (if x j = 1 then e j else 0) := by
        funext r
        rw [Finset.sum_apply, Finset.sum_eq_single r]
        · rcases zmod2_cases (x r) with h | h <;> simp [h, e]
        · intro j _ hj; split_ifs <;> simp [e, Ne.symm hj]
        · intro hm; exact absurd (Finset.mem_univ r) hm
      have hell_sum : ∀ (S : Finset (Fin 7)) (g : Fin 7 → (Fin 7 → F)),
          ell (∑ j ∈ S, g j) = ∑ j ∈ S, ell (g j) := by
        intro S g
        induction S using Finset.induction_on with
        | empty => simp [ell, U.zero_mem]
        | insert a S ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, hell_add, ih]
      conv_lhs => rw [hx_sum]
      rw [hell_sum]
      apply Finset.sum_congr rfl; intro j _
      rcases zmod2_cases (x j) with h0 | h1
      · simp [h0, ell, U.zero_mem]
      · simp [h1, w]
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hb1 : ell b = 1 := by simp [ell, hb]
      rw [hell_dot, hw0] at hb1
      simp at hb1
    obtain ⟨v, hv_ker, hv_nz⟩ := fourth_P_col_hyperplane w hw_ne
    have hv_mem : ∀ r, v r ∈ U := by
      intro r
      have h0 : ell (v r) = 0 := by rw [hell_dot, hv_ker r]
      dsimp [ell] at h0
      by_contra hnot
      simp only [hnot, ↓reduceIte] at h0
      exact one_ne_zero h0
    exact hv_nz (h v hv_mem)

lemma run_eq_zero_of_ker {k d : ℕ} (ask : Fin d → ℕ → D k) (x : W k)
    (hx : ∀ j : Fin d, ask j 0 x = 0) : run ask x = 0 := by
  unfold run
  have haux : ∀ (l : List (Fin d)), (∀ j ∈ l, ask j 0 x = 0) →
      l.foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0 = 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a rest ih =>
      intro hall
      simp only [List.foldl_cons, hall a (List.mem_cons_self), ↓reduceIte, mul_zero, add_zero]
      exact ih (fun j hj => hall j (List.mem_cons_of_mem a hj))
  exact haux (List.finRange d) (fun j _ => hx j)

lemma card_le_pow_mul_ker {α : Type*} [Fintype α] [AddCommGroup α] [Module F α]
    {d : ℕ} (L : α →ₗ[F] (Fin d → F)) :
    Fintype.card α ≤ 2 ^ d * Fintype.card (LinearMap.ker L) := by
  have hfib : (Finset.univ : Finset α).card =
      ∑ y : Fin d → F, (Finset.univ.filter (fun x : α => L x = y)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := L) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have hle : ∀ y : Fin d → F,
      (Finset.univ.filter (fun x : α => L x = y)).card ≤ Fintype.card (LinearMap.ker L) := by
    intro y
    by_cases hne : (Finset.univ.filter (fun x : α => L x = y)).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      have hx0L : L x0 = y := (Finset.mem_filter.mp hx0).2
      have hbij : (Finset.univ.filter (fun x : α => L x = y)).card =
          (Finset.univ.filter (fun x : α => x ∈ LinearMap.ker L)).card := by
        have hmap : Finset.univ.filter (fun x : α => L x = y) =
            (Finset.univ.filter (fun x : α => x ∈ LinearMap.ker L)).image (fun z => z + x0) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, LinearMap.mem_ker]
          constructor
          · intro hLx
            refine ⟨x - x0, ?_, sub_add_cancel x x0⟩
            rw [map_sub, hLx, hx0L, sub_self]
          · rintro ⟨z, hz, rfl⟩
            rw [map_add, hz, hx0L, zero_add]
        rw [hmap, Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
      rw [hbij, Fintype.card_subtype]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  calc Fintype.card α = (Finset.univ : Finset α).card := rfl
    _ = ∑ y : Fin d → F, (Finset.univ.filter (fun x : α => L x = y)).card := hfib
    _ ≤ ∑ _y : Fin d → F, Fintype.card (LinearMap.ker L) := Finset.sum_le_sum (fun y _ => hle y)
    _ = 2 ^ d * Fintype.card (LinearMap.ker L) := by
        simp [Fintype.card_fun, ZMod.card 2, Fintype.card_fin]

theorem lower_bound {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k)
    (mark : Fin k → Bool × Bool) (d : ℕ) (name c₁ c₂ : Bool → W k)
    (hdisj : ∀ (b c : Bool) (i j : Fin k),
      (if b then (mark i).2 else (mark i).1) = true →
      (if c then (mark j).2 else (mark j).1) = true →
      (b, i) ≠ (c, j) → Disjoint (bag hk b i) (bag hk c j))
    (hfits : ∃ (ask : Fin d → ℕ → D k) (readout : ℕ → Bool → Fin k → W k → F),
      (∀ h b i, cubic (readout h b i)) ∧
      ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
        out hk name c₁ c₂ x b i = readout (run ask x) b i x) :
    ((Finset.univ : Finset (Fin k)).filter (fun i => (mark i).1 = true)).card +
      2 * ((Finset.univ : Finset (Fin k)).filter (fun i => (mark i).2 = true)).card ≤ d := by
  obtain ⟨ask, readout, hcub, hagree⟩ := hfits
  let Srow := (Finset.univ : Finset (Fin k)).filter (fun i => (mark i).1 = true)
  let Scol := (Finset.univ : Finset (Fin k)).filter (fun i => (mark i).2 = true)
  let T := ({i : Fin k // i ∈ Srow} → Fin 5 → F) × ({i : Fin k // i ∈ Scol} → Fin 7 → F)
  let A : W k →ₗ[F] (Fin d → F) :=
    { toFun := fun x j => ask j 0 x
      map_add' := fun x y => by funext j; exact (ask j 0).map_add x y
      map_smul' := fun c x => by funext j; exact (ask j 0).map_smul c x }
  let Phi : W k →ₗ[F] T :=
    { toFun := fun x => (fun i => tapRow hk i.1 x, fun i => tapCol hk i.1 x)
      map_add' := fun x y => by
        ext i s
        · exact congrFun ((tapRow hk i.1).map_add x y) s
        · exact congrFun ((tapCol hk i.1).map_add x y) s
      map_smul' := fun c x => by
        ext i s
        · exact congrFun ((tapRow hk i.1).map_smul c x) s
        · exact congrFun ((tapCol hk i.1).map_smul c x) s }
  let Psi : T →ₗ[F] W k :=
    { toFun := fun t =>
        (∑ i : {i : Fin k // i ∈ Srow}, liftRow hk i.1 (t.1 i)) +
        (∑ i : {i : Fin k // i ∈ Scol}, liftCol hk i.1 (t.2 i))
      map_add' := fun t1 t2 => by
        change (∑ i : {i : Fin k // i ∈ Srow}, liftRow hk i.1 (t1.1 i + t2.1 i)) +
          (∑ i : {i : Fin k // i ∈ Scol}, liftCol hk i.1 (t1.2 i + t2.2 i)) =
          ((∑ i : {i : Fin k // i ∈ Srow}, liftRow hk i.1 (t1.1 i)) +
           (∑ i : {i : Fin k // i ∈ Scol}, liftCol hk i.1 (t1.2 i))) +
          ((∑ i : {i : Fin k // i ∈ Srow}, liftRow hk i.1 (t2.1 i)) +
           (∑ i : {i : Fin k // i ∈ Scol}, liftCol hk i.1 (t2.2 i)))
        simp only [map_add, Finset.sum_add_distrib]
        abel
      map_smul' := fun c t => by
        change (∑ i : {i : Fin k // i ∈ Srow}, liftRow hk i.1 (c • t.1 i)) +
          (∑ i : {i : Fin k // i ∈ Scol}, liftCol hk i.1 (c • t.2 i)) =
          c • ((∑ i : {i : Fin k // i ∈ Srow}, liftRow hk i.1 (t.1 i)) +
               (∑ i : {i : Fin k // i ∈ Scol}, liftCol hk i.1 (t.2 i)))
        simp only [map_smul, Finset.smul_sum, smul_add] }
  have hPhiPsi : ∀ t : T, Phi (Psi t) = t := by
    intro ⟨tr, tc⟩
    apply Prod.ext
    · funext i
      change tapRow hk i.1 ((∑ j : {j : Fin k // j ∈ Srow}, liftRow hk j.1 (tr j)) +
        (∑ j : {j : Fin k // j ∈ Scol}, liftCol hk j.1 (tc j))) = tr i
      rw [map_add, map_sum, map_sum]
      have hcol0 : ∑ j : {j : Fin k // j ∈ Scol}, tapRow hk i.1 (liftCol hk j.1 (tc j)) = 0 := by
        apply Finset.sum_eq_zero; intro j _
        apply tapRow_eq_zero_of_bag hk h7 i.1
        intro q hq
        apply liftCol_support hk h7 j.1
        have hd := hdisj false true i.1 j.1 (Finset.mem_filter.mp i.2).2 (Finset.mem_filter.mp j.2).2
          (by intro h; cases h)
        exact Finset.disjoint_left.mp hd hq
      rw [hcol0, add_zero, Finset.sum_eq_single i]
      · exact tapRow_liftRow hk h7 i.1 (tr i)
      · intro i' _ hne
        apply tapRow_eq_zero_of_bag hk h7 i.1
        intro q hq
        apply liftRow_support hk h7 i'.1
        have hne' : (false, i.1) ≠ (false, i'.1) := fun h => hne (Subtype.ext (Prod.mk.inj h).2).symm
        have hd := hdisj false false i.1 i'.1 (Finset.mem_filter.mp i.2).2 (Finset.mem_filter.mp i'.2).2 hne'
        exact Finset.disjoint_left.mp hd hq
      · intro hm; exact absurd (Finset.mem_univ i) hm
    · funext i
      change tapCol hk i.1 ((∑ j : {j : Fin k // j ∈ Srow}, liftRow hk j.1 (tr j)) +
        (∑ j : {j : Fin k // j ∈ Scol}, liftCol hk j.1 (tc j))) = tc i
      rw [map_add, map_sum, map_sum]
      have hrow0 : ∑ j : {j : Fin k // j ∈ Srow}, tapCol hk i.1 (liftRow hk j.1 (tr j)) = 0 := by
        apply Finset.sum_eq_zero; intro j _
        apply tapCol_eq_zero_of_bag hk h7 i.1
        intro q hq
        apply liftRow_support hk h7 j.1
        have hd := hdisj true false i.1 j.1 (Finset.mem_filter.mp i.2).2 (Finset.mem_filter.mp j.2).2
          (by intro h; cases h)
        exact Finset.disjoint_left.mp hd hq
      rw [hrow0, zero_add, Finset.sum_eq_single i]
      · exact tapCol_liftCol hk h7 i.1 (tc i)
      · intro i' _ hne
        apply tapCol_eq_zero_of_bag hk h7 i.1
        intro q hq
        apply liftCol_support hk h7 i'.1
        have hne' : (true, i.1) ≠ (true, i'.1) := fun h => hne (Subtype.ext (Prod.mk.inj h).2).symm
        have hd := hdisj true true i.1 i'.1 (Finset.mem_filter.mp i.2).2 (Finset.mem_filter.mp i'.2).2 hne'
        exact Finset.disjoint_left.mp hd hq
      · intro hm; exact absurd (Finset.mem_univ i) hm
  let K' : Submodule F T := LinearMap.ker (A.comp Psi)
  have hker_vanish : ∀ (b : Bool) (i : Fin k), (if b then (mark i).2 else (mark i).1) = true →
      ∀ v : Fin 4 → W k, (∀ r, A (v r) = 0) → fourth (fun x => out hk name c₁ c₂ x b i) v 0 = 0 := by
    intro b i hon v hv
    have hcube : ∀ s : Fin 4 → Bool, out hk name c₁ c₂ (cubePt 0 v s) b i = readout 0 b i (cubePt 0 v s) := by
      intro s
      have hAs : A (cubePt 0 v s) = 0 := by
        dsimp [cubePt]
        simp only [map_add, map_zero, zero_add]
        have h0 : A (if s 0 then v 0 else 0) = 0 := by split_ifs <;> simp [hv]
        have h1 : A (if s 1 then v 1 else 0) = 0 := by split_ifs <;> simp [hv]
        have h2 : A (if s 2 then v 2 else 0) = 0 := by split_ifs <;> simp [hv]
        have h3 : A (if s 3 then v 3 else 0) = 0 := by split_ifs <;> simp [hv]
        rw [h0, h1, h2, h3]; simp
      have hrun0 : run ask (cubePt 0 v s) = 0 :=
        run_eq_zero_of_ker ask (cubePt 0 v s) (fun j => congrFun hAs j)
      rw [hagree (cubePt 0 v s) b i hon, hrun0]
    rw [fourth_congr_cube hcube]
    exact hcub 0 b i v 0
  let projRow (i : {i : Fin k // i ∈ Srow}) : T →ₗ[F] (Fin 5 → F) :=
    { toFun := fun t => t.1 i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let projCol (i : {i : Fin k // i ∈ Scol}) : T →ₗ[F] (Fin 7 → F) :=
    { toFun := fun t => t.2 i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Urow (i : {i : Fin k // i ∈ Srow}) : Submodule F (Fin 5 → F) := K'.map (projRow i)
  let Ucol (i : {i : Fin k // i ∈ Scol}) : Submodule F (Fin 7 → F) := K'.map (projCol i)
  have hUrow : ∀ i, 2 * Fintype.card (Urow i) ≤ 2 ^ 5 := by
    intro i
    apply card_le_row (Urow i)
    intro v hv
    have hlift : ∀ r, ∃ t : T, t ∈ K' ∧ t.1 i = v r := fun r => hv r
    let t : Fin 4 → T := fun r => Classical.choose (hlift r)
    have htK : ∀ r, A (Psi (t r)) = 0 := fun r => (Classical.choose_spec (hlift r)).1
    have htv : ∀ r, tapRow hk i.1 (Psi (t r)) = v r := fun r => by
      have h1 := congrFun (congrArg Prod.fst (hPhiPsi (t r))) i
      dsimp [Phi] at h1
      rw [h1]
      exact (Classical.choose_spec (hlift r)).2
    have h4 := hker_vanish false i.1 (Finset.mem_filter.mp i.2).2 (fun r => Psi (t r)) htK
    rw [fourth_out_row hk h7 i.1 name c₁ c₂] at h4
    simpa only [htv] using h4
  have hUcol : ∀ i, 4 * Fintype.card (Ucol i) ≤ 2 ^ 7 := by
    intro i
    apply card_le_col (Ucol i)
    intro v hv
    have hlift : ∀ r, ∃ t : T, t ∈ K' ∧ t.2 i = v r := fun r => hv r
    let t : Fin 4 → T := fun r => Classical.choose (hlift r)
    have htK : ∀ r, A (Psi (t r)) = 0 := fun r => (Classical.choose_spec (hlift r)).1
    have htv : ∀ r, tapCol hk i.1 (Psi (t r)) = v r := fun r => by
      have h1 := congrFun (congrArg Prod.snd (hPhiPsi (t r))) i
      dsimp [Phi] at h1
      rw [h1]
      exact (Classical.choose_spec (hlift r)).2
    have h4 := hker_vanish true i.1 (Finset.mem_filter.mp i.2).2 (fun r => Psi (t r)) htK
    rw [fourth_out_col hk h7 i.1 name c₁ c₂] at h4
    simpa only [htv] using h4
  have hK'_le : Fintype.card K' ≤
      (∏ i : {i : Fin k // i ∈ Srow}, Fintype.card (Urow i)) *
      (∏ i : {i : Fin k // i ∈ Scol}, Fintype.card (Ucol i)) := by
    let emb : K' → (∀ i, Urow i) × (∀ i, Ucol i) :=
      fun x => (fun i => ⟨x.1.1 i, ⟨x.1, x.2, rfl⟩⟩, fun i => ⟨x.1.2 i, ⟨x.1, x.2, rfl⟩⟩)
    have hinj : Function.Injective emb := by
      intro x1 x2 h
      apply Subtype.ext
      apply Prod.ext
      · funext i; exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) i)
      · funext i; exact congrArg Subtype.val (congrFun (congrArg Prod.snd h) i)
    have hle := Fintype.card_le_of_injective emb hinj
    simpa only [Fintype.card_prod, Fintype.card_pi] using hle
  have hT_le : Fintype.card T ≤ 2 ^ d * Fintype.card K' :=
    card_le_pow_mul_ker (A.comp Psi)
  have hT_card : Fintype.card T =
      (∏ _i : {i : Fin k // i ∈ Srow}, 2 ^ 5) * (∏ _i : {i : Fin k // i ∈ Scol}, 2 ^ 7) := by
    dsimp [T]
    simp [Fintype.card_prod, Fintype.card_fun, ZMod.card 2, Fintype.card_fin]
  have hprod_row : (∏ i : {i : Fin k // i ∈ Srow}, 2 * Fintype.card (Urow i)) ≤
      ∏ _i : {i : Fin k // i ∈ Srow}, 2 ^ 5 :=
    Finset.prod_le_prod' (fun i _ => hUrow i)
  have hprod_col : (∏ i : {i : Fin k // i ∈ Scol}, 4 * Fintype.card (Ucol i)) ≤
      ∏ _i : {i : Fin k // i ∈ Scol}, 2 ^ 7 :=
    Finset.prod_le_prod' (fun i _ => hUcol i)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_subtype] at hprod_row
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_subtype] at hprod_col
  have hfour : (4 : ℕ) ^ Scol.card = 2 ^ (2 * Scol.card) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hfilt_row : (Finset.univ.filter (fun i : Fin k => i ∈ Srow)).card = Srow.card := by
    congr 1; ext i; simp
  have hfilt_col : (Finset.univ.filter (fun i : Fin k => i ∈ Scol)).card = Scol.card := by
    congr 1; ext i; simp
  rw [hfilt_row] at hprod_row
  rw [hfilt_col, hfour] at hprod_col
  let P := (∏ i : {i : Fin k // i ∈ Srow}, Fintype.card (Urow i)) *
           (∏ i : {i : Fin k // i ∈ Scol}, Fintype.card (Ucol i))
  have hP_pos : 0 < P := by
    dsimp [P]
    apply Nat.mul_pos
    · exact Finset.prod_pos (fun i _ => Fintype.card_pos_iff.mpr ⟨⟨0, (Urow i).zero_mem⟩⟩)
    · exact Finset.prod_pos (fun i _ => Fintype.card_pos_iff.mpr ⟨⟨0, (Ucol i).zero_mem⟩⟩)
  have hpow_le : 2 ^ (Srow.card + 2 * Scol.card) * P ≤ 2 ^ d * P := by
    calc 2 ^ (Srow.card + 2 * Scol.card) * P
        = (2 ^ Srow.card * ∏ i : {i : Fin k // i ∈ Srow}, Fintype.card (Urow i)) *
          (2 ^ (2 * Scol.card) * ∏ i : {i : Fin k // i ∈ Scol}, Fintype.card (Ucol i)) := by
            rw [pow_add]; dsimp [P]; ring
      _ ≤ (∏ _i : {i : Fin k // i ∈ Srow}, 2 ^ 5) * (∏ _i : {i : Fin k // i ∈ Scol}, 2 ^ 7) :=
            Nat.mul_le_mul hprod_row hprod_col
      _ = Fintype.card T := hT_card.symm
      _ ≤ 2 ^ d * Fintype.card K' := hT_le
      _ ≤ 2 ^ d * P := Nat.mul_le_mul_left _ hK'_le
  have h2le : 2 ^ (Srow.card + 2 * Scol.card) ≤ 2 ^ d :=
    Nat.le_of_mul_le_mul_right hpow_le hP_pos
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h2le

end

end PEqualNP.Outside.L_meta_29771

theorem PEqualNP.Outside.L_meta_29771 :
(let fits := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → ZMod 2) =>
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let gap := fun b : Bool => if b then 2 else (1 : ℕ)
  let spin := fun b : Bool => if b then 3 else (1 : ℕ)
  let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
  let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
  let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
  let out := fun (x : W) (b : Bool) =>
    let z := mix (gap b) (rot (spin b) x + name b)
    let y := step z + rot (if b then 4 else 0) x + c₁ b
    step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
  let run := fun (ask : Fin d → ℕ → D) (x : W) =>
    (List.finRange d).foldl (fun h j =>
      2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
  ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → W → F),
    (∀ h b i, cubic (readout h b i)) ∧
    ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
      out x b i = readout (run ask x) b i x
∀ (k : ℕ) (hk : 0 < k), 7 ≤ k →
  ∀ (mark : Fin k → Bool × Bool) (d : ℕ) (name c₁ c₂ : Bool → Fin k → ZMod 2),
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let on := fun (b : Bool) (i : Fin k) => if b then (mark i).2 else (mark i).1
  let bag := fun (b : Bool) (i : Fin k) =>
    (Finset.range (if b then 11 else 7)).image (fun r =>
      ix (i.val + k - (if b then 5 else 1) % k + r))
  (∀ (b c : Bool) (i j : Fin k), on b i = true → on c j = true →
    (b,i) ≠ (c,j) → Disjoint (bag b i) (bag c j)) →
  (fits k hk mark d name c₁ c₂ ↔
    ((Finset.univ : Finset (Fin k)).filter (fun i => (mark i).1 = true)).card +
      2 * ((Finset.univ : Finset (Fin k)).filter (fun i => (mark i).2 = true)).card ≤ d)) := by
  intro fits k hk h7 mark d name c₁ c₂ ix on bag hdisj
  constructor
  · exact PEqualNP.Outside.L_meta_29771.lower_bound hk h7 mark d name c₁ c₂ hdisj
  · exact PEqualNP.Outside.L_meta_29771.upper_bound hk h7 mark d name c₁ c₂
