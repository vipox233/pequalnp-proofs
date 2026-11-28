import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_415

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_mul_self (a : ZMod 2) : a * a = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> simp_all

private lemma zmod2_eq_or_eq_of_ne {a b e : ZMod 2} (hne : a ≠ b) : e = a ∨ e = b := by
  rcases zmod2_cases a with rfl | rfl <;>
    rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases e with rfl | rfl <;>
    simp_all

private lemma zmod2_sum_univ (h : ZMod 2 → ZMod 2) : ∑ a : ZMod 2, h a = h 0 + h 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide)]

private lemma sum2_const (c : ZMod 2) : ∑ _a : ZMod 2, ∑ _b : ZMod 2, c = 0 := by
  simp only [zmod2_sum_univ]
  rcases zmod2_cases c with rfl | rfl <;> decide

private lemma sum2_quad (p q α : ZMod 2) :
    ∑ a : ZMod 2, ∑ b : ZMod 2, (p * a + q * b + α * (a * b)) = α := by
  simp only [zmod2_sum_univ]
  rcases zmod2_cases p with rfl | rfl <;>
    rcases zmod2_cases q with rfl | rfl <;>
    rcases zmod2_cases α with rfl | rfl <;> decide

private lemma sum4_left (F : ZMod 2 → ZMod 2 → ZMod 2) :
    ∑ a : ZMod 2, ∑ b : ZMod 2, ∑ _c : ZMod 2, ∑ _d : ZMod 2, F a b = 0 := by
  simp only [sum2_const, Finset.sum_const_zero]

private lemma sum4_right (G : ZMod 2 → ZMod 2 → ZMod 2) :
    ∑ _a : ZMod 2, ∑ _b : ZMod 2, ∑ c : ZMod 2, ∑ d : ZMod 2, G c d = 0 := by
  exact sum2_const _

private lemma sum4_prod (F G : ZMod 2 → ZMod 2 → ZMod 2) :
    ∑ a : ZMod 2, ∑ b : ZMod 2, ∑ c : ZMod 2, ∑ d : ZMod 2, F a b * G c d =
      (∑ a : ZMod 2, ∑ b : ZMod 2, F a b) * (∑ c : ZMod 2, ∑ d : ZMod 2, G c d) := by
  calc ∑ a : ZMod 2, ∑ b : ZMod 2, ∑ c : ZMod 2, ∑ d : ZMod 2, F a b * G c d
      = ∑ a : ZMod 2, ∑ b : ZMod 2, F a b * (∑ c : ZMod 2, ∑ d : ZMod 2, G c d) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
    _ = (∑ a : ZMod 2, ∑ b : ZMod 2, F a b) * (∑ c : ZMod 2, ∑ d : ZMod 2, G c d) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]

private lemma sum4_quartic
    (p0 q0 α0 r0 s0 α0' p1 q1 β0 r1 s1 β0' p2 q2 γ0 r2 s2 γ0' u v : ZMod 2) :
    ∑ a : ZMod 2, ∑ b : ZMod 2, ∑ c : ZMod 2, ∑ d : ZMod 2,
      (((p2 * a + q2 * b + γ0 * (a * b)) + (r2 * c + s2 * d + γ0' * (c * d))) +
        ((p0 * a + q0 * b + α0 * (a * b)) + (r0 * c + s0 * d + α0' * (c * d)) + u) *
        ((p1 * a + q1 * b + β0 * (a * b)) + (r1 * c + s1 * d + β0' * (c * d)) + v)) =
      α0 * β0' + α0' * β0 := by
  let A : ZMod 2 → ZMod 2 → ZMod 2 := fun a b => p0 * a + q0 * b + α0 * (a * b)
  let A' : ZMod 2 → ZMod 2 → ZMod 2 := fun c d => r0 * c + s0 * d + α0' * (c * d)
  let B : ZMod 2 → ZMod 2 → ZMod 2 := fun a b => p1 * a + q1 * b + β0 * (a * b)
  let B' : ZMod 2 → ZMod 2 → ZMod 2 := fun c d => r1 * c + s1 * d + β0' * (c * d)
  let C : ZMod 2 → ZMod 2 → ZMod 2 := fun a b => p2 * a + q2 * b + γ0 * (a * b)
  let C' : ZMod 2 → ZMod 2 → ZMod 2 := fun c d => r2 * c + s2 * d + γ0' * (c * d)
  let P : ZMod 2 → ZMod 2 → ZMod 2 := fun a b => C a b + A a b * B a b + u * B a b + v * A a b + u * v
  let Q : ZMod 2 → ZMod 2 → ZMod 2 := fun c d => C' c d + A' c d * B' c d + u * B' c d + v * A' c d
  have hpt : ∀ a b c d : ZMod 2,
      ((C a b + C' c d) + (A a b + A' c d + u) * (B a b + B' c d + v)) =
      P a b + Q c d + A a b * B' c d + B a b * A' c d := by
    intro a b c d; dsimp only [P, Q]; ring
  change ∑ a : ZMod 2, ∑ b : ZMod 2, ∑ c : ZMod 2, ∑ d : ZMod 2,
      ((C a b + C' c d) + (A a b + A' c d + u) * (B a b + B' c d + v)) = α0 * β0' + α0' * β0
  simp_rw [hpt, Finset.sum_add_distrib]
  rw [sum4_left P, sum4_right Q, sum4_prod A B', sum4_prod B A', zero_add, zero_add]
  have hA : ∑ a : ZMod 2, ∑ b : ZMod 2, A a b = α0 := sum2_quad p0 q0 α0
  have hA' : ∑ c : ZMod 2, ∑ d : ZMod 2, A' c d = α0' := sum2_quad r0 s0 α0'
  have hB : ∑ a : ZMod 2, ∑ b : ZMod 2, B a b = β0 := sum2_quad p1 q1 β0
  have hB' : ∑ c : ZMod 2, ∑ d : ZMod 2, B' c d = β0' := sum2_quad r1 s1 β0'
  rw [hA, hA', hB, hB', mul_comm β0 α0']

private def eb (r : ℕ) (i : Fin r) (t : Fin 3) : Fin r → Fin 3 → ZMod 2 :=
  fun j s => if j = i ∧ s = t then 1 else 0

private def lift (r : ℕ) (b x y : Fin r → ZMod 2) : Fin r → Fin 3 → ZMod 2 :=
  fun i t => if t = 0 then x i else if t = 1 then y i else b i + x i * y i

private def mask (r : ℕ) (b : Fin r → ZMod 2) : Fin r → Fin 3 → ZMod 2 :=
  fun i t => if t = 2 then b i else 0

private lemma target_lift (r : ℕ) (b x y : Fin r → ZMod 2) :
    (fun i : Fin r => lift r b x y i 2 + lift r b x y i 0 * lift r b x y i 1) = b := by
  funext i
  simp only [lift, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    show (1 : Fin 3) ≠ 0 by decide, ite_true, ite_false]
  rw [add_assoc, zmod2_add_self, add_zero]

private lemma lift_eq_add_mask (r : ℕ) (b x y : Fin r → ZMod 2) :
    lift r b x y = lift r 0 x y + mask r b := by
  funext i t
  fin_cases t <;> simp [lift, mask, add_comm]

private lemma lift_zero_zero (r : ℕ) : lift r 0 0 0 = 0 := by
  funext i t
  fin_cases t <;> simp [lift]

private lemma vec_eq_sum_eb (r : ℕ) (w : Fin r → Fin 3 → ZMod 2) :
    w = ∑ i : Fin r, ∑ t : Fin 3, w i t • eb r i t := by
  funext j s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eb]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single s]
    · simp
    · intro t _ hts; simp [hts.symm]
    · intro h; exact (h (Finset.mem_univ s)).elim
  · intro i _ hij
    apply Finset.sum_eq_zero
    intro t _
    simp [hij.symm]
  · intro h; exact (h (Finset.mem_univ j)).elim

private lemma mask_eq_sum_eb (r : ℕ) (b : Fin r → ZMod 2) :
    mask r b = ∑ i : Fin r, b i • eb r i 2 := by
  funext j s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eb, mask]
  rw [Finset.sum_eq_single j]
  · by_cases hs : s = 2 <;> simp [hs]
  · intro i _ hij; simp [hij.symm]
  · intro h; exact (h (Finset.mem_univ j)).elim

private lemma linear_nonconst (r : ℕ)
    (φ : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0) :
    ∃ x y : Fin r → ZMod 2, φ (lift r 0 x y) ≠ 0 := by
  have hex : ∃ i : Fin r, ∃ t : Fin 3, φ (eb r i t) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hφ
    apply LinearMap.ext
    intro w
    rw [vec_eq_sum_eb r w, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro t _
    rw [map_smul, hall i t, smul_zero]
  rcases hex with ⟨i, t, hit⟩
  let d : Fin r → ZMod 2 := fun j => if j = i then 1 else 0
  have h0 : lift r 0 d 0 = eb r i 0 := by
    funext j s
    fin_cases s <;> by_cases hji : j = i <;> simp [lift, eb, d, hji]
  have h1 : lift r 0 0 d = eb r i 1 := by
    funext j s
    fin_cases s <;> by_cases hji : j = i <;> simp [lift, eb, d, hji]
  have h2 : lift r 0 d d = eb r i 0 + eb r i 1 + eb r i 2 := by
    funext j s
    fin_cases s <;> by_cases hji : j = i <;> simp [lift, eb, d, hji]
  fin_cases t
  · exact ⟨d, 0, by rw [h0]; exact hit⟩
  · exact ⟨0, d, by rw [h1]; exact hit⟩
  · by_contra hno
    push Not at hno
    have hv0 : φ (eb r i 0) = 0 := by rw [← h0]; exact hno d 0
    have hv1 : φ (eb r i 1) = 0 := by rw [← h1]; exact hno 0 d
    have hv2 : φ (eb r i 0 + eb r i 1 + eb r i 2) = 0 := by rw [← h2]; exact hno d d
    rw [map_add, map_add, hv0, hv1, zero_add, zero_add] at hv2
    exact hit hv2

private lemma lift_two_coords {r : ℕ} {i j : Fin r} (hij : i ≠ j) (a b c d : ZMod 2) :
    lift r 0 (fun l => if l = i then a else if l = j then c else 0)
             (fun l => if l = i then b else if l = j then d else 0) =
      a • eb r i 0 + b • eb r i 1 + (a * b) • eb r i 2 +
      c • eb r j 0 + d • eb r j 1 + (c * d) • eb r j 2 := by
  funext l s
  by_cases hli : l = i
  · subst hli
    fin_cases s <;> simp [lift, eb, hij]
  · by_cases hlj : l = j
    · subst hlj
      fin_cases s <;> simp [lift, eb, hli]
    · fin_cases s <;> simp [lift, eb, hli, hlj]

private lemma rank_le_one_cases {r : ℕ} (α β : Fin r → ZMod 2)
    (h : ∀ i j : Fin r, α i * β j + α j * β i = 0) :
    (∀ i, α i = 0) ∨ (∀ i, β i = 0) ∨ (∀ i, α i = β i) := by
  by_cases hα : ∀ i, α i = 0
  · exact Or.inl hα
  · by_cases hβ : ∀ i, β i = 0
    · exact Or.inr (Or.inl hβ)
    · right; right
      push Not at hα hβ
      rcases hα with ⟨i, hi⟩
      rcases hβ with ⟨j, hj⟩
      have hai : α i = 1 := by rcases zmod2_cases (α i) with h0 | h1; exact (hi h0).elim; exact h1
      have hbj : β j = 1 := by rcases zmod2_cases (β j) with h0 | h1; exact (hj h0).elim; exact h1
      have hij := h i j
      rw [hai, hbj, one_mul] at hij
      have hbi : β i = 1 := by
        rcases zmod2_cases (β i) with h0 | h1
        · rw [h0, mul_zero, add_zero] at hij; exact absurd hij (by decide)
        · exact h1
      intro l
      have hil := h i l
      rw [hai, hbi, one_mul, mul_one] at hil
      exact (zmod2_eq_of_add_eq_zero hil).symm

private lemma extra_block_surj (r : ℕ)
    (g : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (hg : g ≠ 0) :
    ∃ p q : ZMod 2, ∀ (b : Fin r → ZMod 2) (e : ZMod 2), ∃ w : Fin r → Fin 3 → ZMod 2,
      (fun i : Fin r => w i 2 + w i 0 * w i 1) = b ∧
      (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
  let F := ZMod 2
  let X := Fin r → Fin 3 → F
  let target := fun (w : X) (i : Fin r) => w i 2 + w i 0 * w i 1
  let L : Fin 3 → (X →ₗ[F] F) := fun k => (LinearMap.proj k).comp g
  let f : Fin 3 → (Fin r → F) → (Fin r → F) → F := fun k x y => L k (lift r 0 x y)
  let sh : Fin 3 → (Fin r → F) → F := fun k b => L k (mask r b)
  let H : F → F → (Fin r → F) → (Fin r → F) → F :=
    fun u v x y => f 2 x y + (f 0 x y + u) * (f 1 x y + v)
  have hgw : ∀ (k : Fin 3) (b x y : Fin r → F), g (lift r b x y) k = f k x y + sh k b := by
    intro k b x y
    change L k (lift r b x y) = L k (lift r 0 x y) + L k (mask r b)
    rw [lift_eq_add_mask, map_add]
  have heval_H : ∀ (p q : F) (b x y : Fin r → F),
      (g (lift r b x y)) 2 + ((g (lift r b x y)) 0 + p) * ((g (lift r b x y)) 1 + q) =
        sh 2 b + H (p + sh 0 b) (q + sh 1 b) x y := by
    intro p q b x y
    rw [hgw 2 b x y, hgw 0 b x y, hgw 1 b x y]
    dsimp only [H]
    ring
  have hfrom_nonconst : ∀ (p q : F),
      (∀ b : Fin r → F, ∃ x y : Fin r → F,
        H (p + sh 0 b) (q + sh 1 b) x y ≠ H (p + sh 0 b) (q + sh 1 b) 0 0) →
      ∀ (b : Fin r → F) (e : F), ∃ w : X,
        target w = b ∧ (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
    intro p q hnc b e
    rcases hnc b with ⟨x, y, hxy⟩
    have hne : sh 2 b + H (p + sh 0 b) (q + sh 1 b) x y ≠
        sh 2 b + H (p + sh 0 b) (q + sh 1 b) 0 0 := fun heq => hxy (add_left_cancel heq)
    rcases zmod2_eq_or_eq_of_ne hne (e := e) with he | he
    · refine ⟨lift r b x y, target_lift r b x y, ?_⟩
      rw [heval_H, he]
    · refine ⟨lift r b 0 0, target_lift r b 0 0, ?_⟩
      rw [heval_H, he]
  have hf00 : ∀ k : Fin 3, f k 0 0 = 0 := by
    intro k
    dsimp only [f]
    rw [lift_zero_zero, map_zero]
  have hH00 : ∀ u v : F, H u v 0 0 = u * v := by
    intro u v
    simp only [H, hf00, zero_add]
  let α : Fin r → F := fun i => L 0 (eb r i 2)
  let β : Fin r → F := fun i => L 1 (eb r i 2)
  have hsh0 : ∀ b : Fin r → F, sh 0 b = ∑ i : Fin r, b i * α i := by
    intro b
    dsimp only [sh, α]
    rw [mask_eq_sum_eb, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
  have hsh1 : ∀ b : Fin r → F, sh 1 b = ∑ i : Fin r, b i * β i := by
    intro b
    dsimp only [sh, β]
    rw [mask_eq_sum_eb, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
  by_cases hminor : ∃ i j : Fin r, α i * β j + α j * β i ≠ 0
  · rcases hminor with ⟨i, j, hmin⟩
    have hij : i ≠ j := by
      intro heq; subst heq; exact hmin (zmod2_add_self _)
    refine ⟨0, 0, hfrom_nonconst 0 0 fun b => ?_⟩
    set u := 0 + sh 0 b
    set v := 0 + sh 1 b
    by_contra hall
    push Not at hall
    let x2 : F → F → (Fin r → F) := fun a c l => if l = i then a else if l = j then c else 0
    let y2 : F → F → (Fin r → F) := fun b' d l => if l = i then b' else if l = j then d else 0
    have hfk : ∀ (k : Fin 3) (a b' c d : F),
        f k (x2 a c) (y2 b' d) =
          (L k (eb r i 0) * a + L k (eb r i 1) * b' + L k (eb r i 2) * (a * b')) +
          (L k (eb r j 0) * c + L k (eb r j 1) * d + L k (eb r j 2) * (c * d)) := by
      intro k a b' c d
      dsimp only [f, x2, y2]
      rw [lift_two_coords hij a b' c d]
      simp only [map_add, map_smul, smul_eq_mul]
      ring
    have hsum_zero : ∑ a : F, ∑ b' : F, ∑ c : F, ∑ d : F, H u v (x2 a c) (y2 b' d) = 0 := by
      simp_rw [hall]
      exact sum4_left (fun _ _ => H u v 0 0)
    have hsum_val : ∑ a : F, ∑ b' : F, ∑ c : F, ∑ d : F, H u v (x2 a c) (y2 b' d) =
        α i * β j + α j * β i := by
      simp only [H, hfk]
      exact sum4_quartic
        (L 0 (eb r i 0)) (L 0 (eb r i 1)) (L 0 (eb r i 2))
        (L 0 (eb r j 0)) (L 0 (eb r j 1)) (L 0 (eb r j 2))
        (L 1 (eb r i 0)) (L 1 (eb r i 1)) (L 1 (eb r i 2))
        (L 1 (eb r j 0)) (L 1 (eb r j 1)) (L 1 (eb r j 2))
        (L 2 (eb r i 0)) (L 2 (eb r i 1)) (L 2 (eb r i 2))
        (L 2 (eb r j 0)) (L 2 (eb r j 1)) (L 2 (eb r j 2)) u v
    exact hmin (hsum_val.symm.trans hsum_zero)
  · push Not at hminor
    have hL_not_all : ¬ (L 0 = 0 ∧ L 1 = 0 ∧ L 2 = 0) := by
      rintro ⟨h0, h1, h2⟩
      apply hg
      apply LinearMap.ext
      intro w
      funext k
      fin_cases k
      · exact LinearMap.congr_fun h0 w
      · exact LinearMap.congr_fun h1 w
      · exact LinearMap.congr_fun h2 w
    by_cases hL0 : L 0 = 0
    · have hα0 : ∀ i, α i = 0 := fun i => by dsimp only [α]; rw [hL0]; rfl
      have hsh0_zero : ∀ b, sh 0 b = 0 := fun b => by simp [hsh0, hα0]
      have hex_p : ∃ p : F, L 2 + p • L 1 ≠ 0 := by
        by_contra hall
        push Not at hall
        have hp0 : L 2 = 0 := by simpa using hall 0
        have hp1 : L 1 = 0 := by
          have h1 := hall 1
          rw [hp0, zero_add, one_smul] at h1
          exact h1
        exact hL_not_all ⟨hL0, hp1, hp0⟩
      rcases hex_p with ⟨p, hp⟩
      refine ⟨p, 0, hfrom_nonconst p 0 fun b => ?_⟩
      rcases linear_nonconst r (L 2 + p • L 1) hp with ⟨x, y, hxy⟩
      refine ⟨x, y, ?_⟩
      have hH_eq : H (p + sh 0 b) (0 + sh 1 b) x y =
          (L 2 + p • L 1) (lift r 0 x y) + p * sh 1 b := by
        dsimp only [H, f]
        rw [hsh0_zero b, hL0]
        simp only [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [hH_eq, hH00, hsh0_zero b]
      intro heq
      have h0 : (L 2 + p • L 1) (lift r 0 x y) = 0 := by
        have h1 : (L 2 + p • L 1) (lift r 0 x y) + p * sh 1 b = 0 + p * sh 1 b := by
          simpa [add_zero, zero_add] using heq
        exact add_right_cancel h1
      exact hxy h0
    · by_cases hL1 : L 1 = 0
      · have hβ0 : ∀ i, β i = 0 := fun i => by dsimp only [β]; rw [hL1]; rfl
        have hsh1_zero : ∀ b, sh 1 b = 0 := fun b => by simp [hsh1, hβ0]
        have hex_q : ∃ q : F, L 2 + q • L 0 ≠ 0 := by
          by_contra hall
          push Not at hall
          have hq0 : L 2 = 0 := by simpa using hall 0
          have hq1 : L 0 = 0 := by
            have h1 := hall 1
            rw [hq0, zero_add, one_smul] at h1
            exact h1
          exact hL0 hq1
        rcases hex_q with ⟨q, hq⟩
        refine ⟨0, q, hfrom_nonconst 0 q fun b => ?_⟩
        rcases linear_nonconst r (L 2 + q • L 0) hq with ⟨x, y, hxy⟩
        refine ⟨x, y, ?_⟩
        have hH_eq : H (0 + sh 0 b) (q + sh 1 b) x y =
            (L 2 + q • L 0) (lift r 0 x y) + sh 0 b * q := by
          dsimp only [H, f]
          rw [hsh1_zero b, hL1]
          simp only [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
          ring
        rw [hH_eq, hH00, hsh1_zero b]
        intro heq
        have h0 : (L 2 + q • L 0) (lift r 0 x y) = 0 := by
          have h1 : (L 2 + q • L 0) (lift r 0 x y) + sh 0 b * q = 0 + sh 0 b * q := by
            simpa [add_zero, zero_add] using heq
          exact add_right_cancel h1
        exact hxy h0
      · by_cases hL01 : L 0 = L 1
        · have hαβ : ∀ i, α i = β i := fun i => by dsimp only [α, β]; rw [hL01]
          have hsh01 : ∀ b, sh 0 b = sh 1 b := fun b => by simp [hsh0, hsh1, hαβ]
          have hex_p : ∃ p : F, L 2 + (1 + p) • L 0 ≠ 0 := by
            by_contra hall
            push Not at hall
            have h0 := hall 1
            have h1 := hall 0
            have h11 : (1 : F) + 1 = 0 := by decide
            rw [h11, zero_smul, add_zero] at h0
            rw [add_zero, one_smul, h0, zero_add] at h1
            exact hL0 h1
          rcases hex_p with ⟨p, hp⟩
          refine ⟨p, 0, hfrom_nonconst p 0 fun b => ?_⟩
          rcases linear_nonconst r (L 2 + (1 + p) • L 0) hp with ⟨x, y, hxy⟩
          refine ⟨x, y, ?_⟩
          have hH_eq : H (p + sh 0 b) (0 + sh 1 b) x y =
              (L 2 + (1 + p) • L 0) (lift r 0 x y) + (p + sh 0 b) * (0 + sh 1 b) := by
            dsimp only [H, f]
            rw [← hL01, ← hsh01 b]
            have hsq : L 0 (lift r 0 x y) * L 0 (lift r 0 x y) = L 0 (lift r 0 x y) := zmod2_mul_self _
            have hss : sh 0 b + sh 0 b = 0 := zmod2_add_self _
            simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            calc L 2 (lift r 0 x y) + (L 0 (lift r 0 x y) + (p + sh 0 b)) * (L 0 (lift r 0 x y) + (0 + sh 0 b))
                = L 2 (lift r 0 x y) + L 0 (lift r 0 x y) * L 0 (lift r 0 x y) +
                    (p + (sh 0 b + sh 0 b)) * L 0 (lift r 0 x y) + (p + sh 0 b) * (0 + sh 0 b) := by ring
              _ = L 2 (lift r 0 x y) + L 0 (lift r 0 x y) +
                    p * L 0 (lift r 0 x y) + (p + sh 0 b) * (0 + sh 0 b) := by rw [hsq, hss, add_zero]
              _ = L 2 (lift r 0 x y) + (1 + p) * L 0 (lift r 0 x y) + (p + sh 0 b) * (0 + sh 0 b) := by ring
          rw [hH_eq, hH00]
          intro heq
          have h0 : (L 2 + (1 + p) • L 0) (lift r 0 x y) = 0 := by
            have h1 : (L 2 + (1 + p) • L 0) (lift r 0 x y) + (p + sh 0 b) * (0 + sh 1 b) =
                0 + (p + sh 0 b) * (0 + sh 1 b) := by
              simpa [zero_add] using heq
            exact add_right_cancel h1
          exact hxy h0
        · have huniq_bad : ∀ u1 v1 u2 v2 : F,
              (∀ x y : Fin r → F, H u1 v1 x y = H u1 v1 0 0) →
              (∀ x y : Fin r → F, H u2 v2 x y = H u2 v2 0 0) →
              u1 = u2 ∧ v1 = v2 := by
            intro u1 v1 u2 v2 h1 h2
            have hlin0 : ∀ x y : Fin r → F,
                ((u1 + u2) • L 1 + (v1 + v2) • L 0) (lift r 0 x y) = 0 := by
              intro x y
              have he1 := h1 x y
              have he2 := h2 x y
              rw [hH00] at he1 he2
              have hsum := congrArg₂ (· + ·) he1 he2
              dsimp only [H, f] at hsum
              have hcalc : (L 2 (lift r 0 x y) + (L 0 (lift r 0 x y) + u1) * (L 1 (lift r 0 x y) + v1)) +
                  (L 2 (lift r 0 x y) + (L 0 (lift r 0 x y) + u2) * (L 1 (lift r 0 x y) + v2)) =
                  ((u1 + u2) * L 1 (lift r 0 x y) + (v1 + v2) * L 0 (lift r 0 x y)) + (u1 * v1 + u2 * v2) := by
                have h22 : L 2 (lift r 0 x y) + L 2 (lift r 0 x y) = 0 := zmod2_add_self _
                have h01 : L 0 (lift r 0 x y) * L 1 (lift r 0 x y) + L 0 (lift r 0 x y) * L 1 (lift r 0 x y) = 0 :=
                  zmod2_add_self _
                calc (L 2 (lift r 0 x y) + (L 0 (lift r 0 x y) + u1) * (L 1 (lift r 0 x y) + v1)) +
                      (L 2 (lift r 0 x y) + (L 0 (lift r 0 x y) + u2) * (L 1 (lift r 0 x y) + v2))
                    = (L 2 (lift r 0 x y) + L 2 (lift r 0 x y)) +
                        (L 0 (lift r 0 x y) * L 1 (lift r 0 x y) + L 0 (lift r 0 x y) * L 1 (lift r 0 x y)) +
                        ((u1 + u2) * L 1 (lift r 0 x y) + (v1 + v2) * L 0 (lift r 0 x y)) + (u1 * v1 + u2 * v2) := by ring
                  _ = ((u1 + u2) * L 1 (lift r 0 x y) + (v1 + v2) * L 0 (lift r 0 x y)) + (u1 * v1 + u2 * v2) := by
                        rw [h22, h01, zero_add, zero_add]
              rw [hcalc] at hsum
              have hres : ((u1 + u2) * L 1 (lift r 0 x y) + (v1 + v2) * L 0 (lift r 0 x y)) + (u1 * v1 + u2 * v2) =
                  0 + (u1 * v1 + u2 * v2) := by
                simpa [zero_add] using hsum
              simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using add_right_cancel hres
            have hmap0 : (u1 + u2) • L 1 + (v1 + v2) • L 0 = 0 := by
              by_contra hne
              rcases linear_nonconst r _ hne with ⟨x, y, hxy⟩
              exact hxy (hlin0 x y)
            rcases zmod2_cases (u1 + u2) with hu | hu <;> rcases zmod2_cases (v1 + v2) with hv | hv
            · exact ⟨zmod2_eq_of_add_eq_zero hu, zmod2_eq_of_add_eq_zero hv⟩
            · rw [hu, hv, zero_smul, zero_add, one_smul] at hmap0
              exact (hL0 hmap0).elim
            · rw [hu, hv, zero_smul, add_zero, one_smul] at hmap0
              exact (hL1 hmap0).elim
            · rw [hu, hv, one_smul, one_smul] at hmap0
              have heq : L 0 = L 1 := by
                apply LinearMap.ext
                intro w
                exact (zmod2_eq_of_add_eq_zero (LinearMap.congr_fun hmap0 w)).symm
              exact (hL01 heq).elim
          by_cases hbad : ∃ u0 v0 : F, ∀ x y : Fin r → F, H u0 v0 x y = H u0 v0 0 0
          · rcases hbad with ⟨u0, v0, hbad0⟩
            have hgood_of_ne : ∀ (p q : F),
                (∀ b : Fin r → F, p + sh 0 b ≠ u0 ∨ q + sh 1 b ≠ v0) →
                ∃ p' q' : F, ∀ (b : Fin r → F) (e : F), ∃ w : X,
                  target w = b ∧ (g w) 2 + ((g w) 0 + p') * ((g w) 1 + q') = e := by
              intro p q hne
              refine ⟨p, q, hfrom_nonconst p q fun b => ?_⟩
              by_contra hall
              push Not at hall
              have ⟨hu, hv⟩ := huniq_bad (p + sh 0 b) (q + sh 1 b) u0 v0 hall hbad0
              rcases hne b with h1 | h2
              · exact h1 hu
              · exact h2 hv
            rcases rank_le_one_cases α β hminor with hα0 | hβ0 | hαβ
            · apply hgood_of_ne (u0 + 1) v0
              intro b; left
              have h0 : sh 0 b = 0 := by simp [hsh0, hα0]
              rw [h0, add_zero]
              rcases zmod2_cases u0 with rfl | rfl <;> decide
            · apply hgood_of_ne u0 (v0 + 1)
              intro b; right
              have h1 : sh 1 b = 0 := by simp [hsh1, hβ0]
              rw [h1, add_zero]
              rcases zmod2_cases v0 with rfl | rfl <;> decide
            · apply hgood_of_ne (u0 + 1) v0
              intro b
              have h01 : sh 0 b = sh 1 b := by simp [hsh0, hsh1, hαβ]
              by_contra hboth
              push Not at hboth
              rcases hboth with ⟨h1, h2⟩
              have hsum := congrArg₂ (· + ·) h1 h2
              rw [h01] at hsum
              have hss : sh 1 b + sh 1 b = 0 := zmod2_add_self _
              have hcalc : u0 + 1 + sh 1 b + (v0 + sh 1 b) = u0 + v0 + 1 := by
                calc u0 + 1 + sh 1 b + (v0 + sh 1 b)
                    = u0 + v0 + 1 + (sh 1 b + sh 1 b) := by ring
                  _ = u0 + v0 + 1 := by rw [hss, add_zero]
              rw [hcalc] at hsum
              have h10 : (1 : F) = 0 := by
                have h3 : (u0 + v0) + 1 = (u0 + v0) + 0 := by
                  rw [add_zero]; exact hsum
                exact add_left_cancel h3
              exact absurd h10 (by decide)
          · push Not at hbad
            exact ⟨0, 0, hfrom_nonconst 0 0 fun b => hbad (0 + sh 0 b) (0 + sh 1 b)⟩

private lemma single_block_flip (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    ∃ a : Fin 3 → ZMod 2, (a 2 + v 2) + (a 0 + v 0) * (a 1 + v 1) ≠ a 2 + a 0 * a 1 := by
  by_contra hall
  push Not at hall
  have h0 : v 2 + v 0 * v 1 = 0 := by
    have := hall (fun _ => 0)
    simpa using this
  have h1 : v 2 + (1 + v 0) * v 1 = 0 := by
    have := hall (fun t => if t = 0 then 1 else 0)
    simpa [show (2 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 0 by decide] using this
  have h2 : v 2 + v 0 * (1 + v 1) = 0 := by
    have := hall (fun t => if t = 1 then 1 else 0)
    simpa [show (2 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 1 by decide] using this
  have hv1 : v 1 = 0 := by
    have hsum := congrArg₂ (· + ·) h0 h1
    have hcalc : (v 2 + v 0 * v 1) + (v 2 + (1 + v 0) * v 1) = v 1 := by
      have h22 := zmod2_add_self (v 2)
      have h01 := zmod2_add_self (v 0 * v 1)
      calc (v 2 + v 0 * v 1) + (v 2 + (1 + v 0) * v 1)
          = (v 2 + v 2) + (v 0 * v 1 + v 0 * v 1) + v 1 := by ring
        _ = v 1 := by rw [h22, h01, zero_add, zero_add]
    rw [hcalc, add_zero] at hsum
    exact hsum
  have hv0 : v 0 = 0 := by
    have hsum := congrArg₂ (· + ·) h0 h2
    have hcalc : (v 2 + v 0 * v 1) + (v 2 + v 0 * (1 + v 1)) = v 0 := by
      have h22 := zmod2_add_self (v 2)
      have h01 := zmod2_add_self (v 0 * v 1)
      calc (v 2 + v 0 * v 1) + (v 2 + v 0 * (1 + v 1))
          = (v 2 + v 2) + (v 0 * v 1 + v 0 * v 1) + v 0 := by ring
        _ = v 0 := by rw [h22, h01, zero_add, zero_add]
    rw [hcalc, add_zero] at hsum
    exact hsum
  have hv2 : v 2 = 0 := by rw [hv0, hv1, mul_zero, add_zero] at h0; exact h0
  apply hv
  funext t
  fin_cases t
  · exact hv0
  · exact hv1
  · exact hv2

private lemma finrank_le_of_inj_poly {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Module.Finite K W] (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Module.finrank K V ≤ Module.finrank K W :=
  LinearMap.finrank_le_finrank_of_injective hf

end PEqualNP.Outside.L_pcx_415

open PEqualNP.Outside.L_pcx_415 in
theorem PEqualNP.Outside.L_pcx_415 :
    ∀ (r k L : ℕ) (_ : k ≤ r) (_ : 2^k ≤ L) (_ : L < 2^(k+1)),
      let F := ZMod 2
      let X := Fin r → Fin 3 → F
      let target := fun (w : X) (i : Fin r) => w i 2 + w i 0 * w i 1
      ∀ (S : Submodule F X) (_ : Module.finrank F S = 3*k),
        (∀ a : X, Nat.card (Set.image (fun u : S => target (a+u.val)) Set.univ) ≤ L) ↔
        ∃ I : Finset (Fin r), I.card = k ∧
          ∀ u : X, u ∈ S ↔ ∀ i : Fin r, i ∉ I → u i = 0 := by
  classical
  intro r k L hkr hL_lo hL_hi F X target S hSdim
  constructor
  · intro hL
    let P : Finset (Fin r) → Prop := fun I => ∀ u : X, u ∈ S → (∀ i ∈ I, u i = 0) → u = 0
    have hP_univ : P Finset.univ := fun u _ h => funext fun i => h i (Finset.mem_univ i)
    have hex_m : ∃ m : ℕ, ∃ I : Finset (Fin r), I.card = m ∧ P I :=
      ⟨r, Finset.univ, by simp, hP_univ⟩
    let m := Nat.find hex_m
    rcases Nat.find_spec hex_m with ⟨I, hI_card, hPI⟩
    have hmin_I : ∀ I' : Finset (Fin r), P I' → m ≤ I'.card :=
      fun I' hP' => Nat.find_min' hex_m ⟨I', rfl, hP'⟩
    let projI : S →ₗ[F] (I → Fin 3 → F) :=
      { toFun := fun u i => u.1 i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hprojI_inj : Function.Injective projI := by
      intro u1 u2 heq
      apply Subtype.ext
      have hdiff : u1.1 - u2.1 ∈ S := S.sub_mem u1.2 u2.2
      have h0 : u1.1 - u2.1 = 0 := hPI (u1.1 - u2.1) hdiff fun i hi => by
        have := congr_fun heq ⟨i, hi⟩
        exact sub_eq_zero.mpr this
      exact sub_eq_zero.mp h0
    have hcard_S : Fintype.card S = 2 ^ (3 * k) := by
      have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
      rw [ZMod.card, hSdim] at h1
      exact h1
    have hcard_cod : Fintype.card (I → Fin 3 → F) = 2 ^ (3 * m) := by
      simp only [F, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_coe, hI_card]
      rw [← pow_mul]
    have hle_card : Fintype.card S ≤ Fintype.card (I → Fin 3 → F) :=
      Fintype.card_le_of_injective projI hprojI_inj
    have hk_le_m : k ≤ m := by
      rw [hcard_S, hcard_cod] at hle_card
      have h3 : 3 * k ≤ 3 * m := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle_card
      omega
    have hm_le_k : m ≤ k := by
      have hsep : ∀ i : I, ∃ v : S, v.1 i.1 ≠ 0 ∧ ∀ j : I, j ≠ i → v.1 j.1 = 0 := by
        intro i
        have hnotP : ¬ P (I.erase i.1) := by
          intro hPe
          have hle := hmin_I (I.erase i.1) hPe
          have hlt : (I.erase i.1).card < m := by
            rw [Finset.card_erase_of_mem i.2, hI_card]
            have hpos : 0 < I.card := Finset.card_pos.mpr ⟨i.1, i.2⟩
            omega
          omega
        dsimp only [P] at hnotP
        push Not at hnotP
        rcases hnotP with ⟨u, huS, hzero, hne⟩
        refine ⟨⟨u, huS⟩, ?_, ?_⟩
        · intro hui
          apply hne
          apply hPI u huS
          intro j hj
          by_cases hji : j = i.1
          · exact hji ▸ hui
          · exact hzero j (Finset.mem_erase.mpr ⟨hji, hj⟩)
        · intro j hji
          exact hzero j.1 (Finset.mem_erase.mpr ⟨fun h => hji (Subtype.ext h), j.2⟩)
      let v : I → S := fun i => Classical.choose (hsep i)
      have hv_ne : ∀ i : I, (v i).1 i.1 ≠ 0 := fun i => (Classical.choose_spec (hsep i)).1
      have hv_zero : ∀ i j : I, j ≠ i → (v i).1 j.1 = 0 := fun i => (Classical.choose_spec (hsep i)).2
      have ha_ex : ∀ i : I, ∃ a0 : Fin 3 → F,
          (a0 2 + (v i).1 i.1 2) + (a0 0 + (v i).1 i.1 0) * (a0 1 + (v i).1 i.1 1) ≠
            a0 2 + a0 0 * a0 1 :=
        fun i => single_block_flip ((v i).1 i.1) (hv_ne i)
      let a0 : I → Fin 3 → F := fun i => Classical.choose (ha_ex i)
      have ha0_spec : ∀ i : I,
          (a0 i 2 + (v i).1 i.1 2) + (a0 i 0 + (v i).1 i.1 0) * (a0 i 1 + (v i).1 i.1 1) ≠
            a0 i 2 + a0 i 0 * a0 i 1 :=
        fun i => Classical.choose_spec (ha_ex i)
      let a : X := fun j => if hj : j ∈ I then a0 ⟨j, hj⟩ else 0
      let uOf : (I → F) → S := fun c => ∑ i : I, c i • v i
      have huOf_coord : ∀ (c : I → F) (i : I), (uOf c).1 i.1 = c i • (v i).1 i.1 := by
        intro c i
        have hcoe : (uOf c).1 = ∑ j : I, c j • (v j).1 := by
          simp only [uOf, Submodule.coe_sum, Submodule.coe_smul]
        rw [hcoe]
        change (∑ j : I, c j • (v j).1) i.1 = c i • (v i).1 i.1
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single i]
        · rfl
        · intro j _ hji
          change (c j • (v j).1) i.1 = 0
          rw [Pi.smul_apply, hv_zero j i hji.symm, smul_zero]
        · intro h; exact (h (Finset.mem_univ i)).elim
      let img := Set.image (fun u : S => target (a + u.val)) Set.univ
      let φ : (I → F) → img := fun c => ⟨target (a + (uOf c).1), ⟨uOf c, Set.mem_univ _, rfl⟩⟩
      have hφ_inj : Function.Injective φ := by
        intro c1 c2 heq
        funext i
        have hi := congr_fun (congrArg Subtype.val heq) i.1
        change (a i.1 2 + (uOf c1).1 i.1 2) + (a i.1 0 + (uOf c1).1 i.1 0) * (a i.1 1 + (uOf c1).1 i.1 1) =
          (a i.1 2 + (uOf c2).1 i.1 2) + (a i.1 0 + (uOf c2).1 i.1 0) * (a i.1 1 + (uOf c2).1 i.1 1) at hi
        have hai : a i.1 = a0 i := dif_pos i.2
        rw [hai, huOf_coord c1 i, huOf_coord c2 i] at hi
        rcases zmod2_cases (c1 i) with h1 | h1 <;> rcases zmod2_cases (c2 i) with h2 | h2
        · rw [h1, h2]
        · rw [h1, h2, zero_smul, one_smul] at hi
          simp only [Pi.zero_apply, add_zero] at hi
          exact (ha0_spec i hi.symm).elim
        · rw [h1, h2, zero_smul, one_smul] at hi
          simp only [Pi.zero_apply, add_zero] at hi
          exact (ha0_spec i hi).elim
        · rw [h1, h2]
      have hcard_le : Nat.card (I → F) ≤ Nat.card img :=
        Nat.card_le_card_of_injective φ hφ_inj
      have hdom_card : Nat.card (I → F) = 2 ^ m := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_coe, hI_card]
      have hpow_lt : 2 ^ m < 2 ^ (k + 1) := by
        have h1 : Nat.card img ≤ L := hL a
        omega
      have hm_lt : m < k + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow_lt
      omega
    have hm_eq : m = k := le_antisymm hm_le_k hk_le_m
    have hI_k : I.card = k := hI_card.trans hm_eq
    have hprojI_bij : Function.Bijective projI :=
      (Fintype.bijective_iff_injective_and_card projI).mpr ⟨hprojI_inj, by rw [hcard_S, hcard_cod, hm_eq]⟩
    let eI : S ≃ₗ[F] (I → Fin 3 → F) := LinearEquiv.ofBijective projI hprojI_bij
    let inv : (I → Fin 3 → F) →ₗ[F] S := eI.symm.toLinearMap
    have hinv_proj : ∀ w : I → Fin 3 → F, projI (inv w) = w := fun w => eI.apply_symm_apply w
    have hproj_inv : ∀ u : S, inv (projI u) = u := fun u => eI.symm_apply_apply u
    let eqv : I ≃ Fin k := Fintype.equivFinOfCardEq (by simp [hI_k])
    let reidx : (Fin k → Fin 3 → F) →ₗ[F] (I → Fin 3 → F) :=
      { toFun := fun w i => w (eqv i)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hall_zero : ∀ j : Fin r, j ∉ I → ∀ u : S, u.1 j = 0 := by
      intro j hj
      let gj : (Fin k → Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
        { toFun := fun w => (inv (reidx w)).1 j
          map_add' := fun w1 w2 => by simp only [map_add, Submodule.coe_add]; rfl
          map_smul' := fun c w => by simp only [map_smul, SetLike.val_smul, RingHom.id_apply]; rfl }
      have hgj_zero : gj = 0 := by
        by_contra hgj_ne
        rcases extra_block_surj k gj hgj_ne with ⟨p, q, hpq⟩
        let a : X := fun l t => if l = j then (if t = 0 then p else if t = 1 then q else 0) else 0
        let img := Set.image (fun u : S => target (a + u.val)) Set.univ
        let wit : ((Fin k → F) × F) → Fin k → Fin 3 → F := fun pe => Classical.choose (hpq pe.1 pe.2)
        have hwit_t : ∀ pe : (Fin k → F) × F, (fun idx : Fin k => wit pe idx 2 + wit pe idx 0 * wit pe idx 1) = pe.1 :=
          fun pe => (Classical.choose_spec (hpq pe.1 pe.2)).1
        have hwit_e : ∀ pe : (Fin k → F) × F,
            (gj (wit pe)) 2 + ((gj (wit pe)) 0 + p) * ((gj (wit pe)) 1 + q) = pe.2 :=
          fun pe => (Classical.choose_spec (hpq pe.1 pe.2)).2
        let ψ : ((Fin k → F) × F) → img := fun pe =>
          ⟨target (a + (inv (reidx (wit pe))).1), ⟨inv (reidx (wit pe)), Set.mem_univ _, rfl⟩⟩
        have hψ_inj : Function.Injective ψ := by
          intro pe1 pe2 heq
          have hout : target (a + (inv (reidx (wit pe1))).1) = target (a + (inv (reidx (wit pe2))).1) :=
            congrArg Subtype.val heq
          have heval_i : ∀ (pe : (Fin k → F) × F) (idx : Fin k),
              target (a + (inv (reidx (wit pe))).1) (eqv.symm idx).1 = pe.1 idx := by
            intro pe idx
            have hne_j : (eqv.symm idx).1 ≠ j := fun h => hj (h ▸ (eqv.symm idx).2)
            have ha0 : a (eqv.symm idx).1 = 0 := by funext t; simp [a, hne_j]
            have hu_eq : (inv (reidx (wit pe))).1 (eqv.symm idx).1 = wit pe idx := by
              have h1 := congr_fun (hinv_proj (reidx (wit pe))) (eqv.symm idx)
              simpa [projI, reidx] using h1
            change (a (eqv.symm idx).1 2 + (inv (reidx (wit pe))).1 (eqv.symm idx).1 2) +
                (a (eqv.symm idx).1 0 + (inv (reidx (wit pe))).1 (eqv.symm idx).1 0) *
                (a (eqv.symm idx).1 1 + (inv (reidx (wit pe))).1 (eqv.symm idx).1 1) = pe.1 idx
            simp only [ha0, Pi.zero_apply, zero_add, hu_eq]
            exact congr_fun (hwit_t pe) idx
          have heval_j : ∀ pe : (Fin k → F) × F,
              target (a + (inv (reidx (wit pe))).1) j = pe.2 := by
            intro pe
            change (a j 2 + (gj (wit pe)) 2) + (a j 0 + (gj (wit pe)) 0) * (a j 1 + (gj (wit pe)) 1) = pe.2
            have ha0 : a j 0 = p := by simp [a]
            have ha1 : a j 1 = q := by simp [a]
            have ha2 : a j 2 = 0 := by simp [a]
            rw [ha0, ha1, ha2, zero_add, add_comm p, add_comm q]
            exact hwit_e pe
          apply Prod.ext
          · funext idx
            rw [← heval_i pe1 idx, ← heval_i pe2 idx, hout]
          · rw [← heval_j pe1, ← heval_j pe2, hout]
        have hcard_le : Nat.card ((Fin k → F) × F) ≤ Nat.card img :=
          Nat.card_le_card_of_injective ψ hψ_inj
        have hdom_card : Nat.card ((Fin k → F) × F) = 2 ^ (k + 1) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin, pow_succ]
        have h1 : Nat.card img ≤ L := hL a
        omega
      intro u
      let w : Fin k → Fin 3 → F := fun idx => u.1 (eqv.symm idx).1
      have hreidx : reidx w = projI u := by
        funext i
        simp [reidx, w, projI]
      have hu_eq : inv (reidx w) = u := by rw [hreidx, hproj_inv]
      have h0 := LinearMap.congr_fun hgj_zero w
      change (inv (reidx w)).1 j = 0 at h0
      rwa [hu_eq] at h0
    refine ⟨I, hI_k, fun u => ⟨fun hu j hj => hall_zero j hj ⟨u, hu⟩, fun hzero => ?_⟩⟩
    let u' : S := inv (fun i : I => u i.1)
    have heq : u = u'.1 := by
      funext j
      by_cases hj : j ∈ I
      · have h1 := congr_fun (hinv_proj (fun i : I => u i.1)) ⟨j, hj⟩
        exact h1.symm
      · rw [hzero j hj, hall_zero j hj u']
    rw [heq]
    exact u'.2
  · rintro ⟨I, hI_card, hS_iff⟩ a
    let img := Set.image (fun u : S => target (a + u.val)) Set.univ
    let restr : img → (I → F) := fun y i => y.1 i.1
    have hrestr_inj : Function.Injective restr := by
      intro y1 y2 heq
      apply Subtype.ext
      rcases y1.2 with ⟨u1, _, hu1⟩
      rcases y2.2 with ⟨u2, _, hu2⟩
      funext i
      by_cases hi : i ∈ I
      · exact congr_fun heq ⟨i, hi⟩
      · have hz1 : u1.1 i = 0 := (hS_iff u1.1).mp u1.2 i hi
        have hz2 : u2.1 i = 0 := (hS_iff u2.1).mp u2.2 i hi
        rw [← hu1, ← hu2]
        change (a i 2 + u1.1 i 2) + (a i 0 + u1.1 i 0) * (a i 1 + u1.1 i 1) =
          (a i 2 + u2.1 i 2) + (a i 0 + u2.1 i 0) * (a i 1 + u2.1 i 1)
        rw [hz1, hz2]
    have hcard_le : Nat.card img ≤ Nat.card (I → F) :=
      Nat.card_le_card_of_injective restr hrestr_inj
    have hcod_card : Nat.card (I → F) = 2 ^ k := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_coe, hI_card]
    change Nat.card img ≤ L
    omega
