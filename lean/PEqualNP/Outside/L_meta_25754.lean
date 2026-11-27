import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25750

namespace PEqualNP.Outside.L_meta_25754

abbrev B := ZMod 2

def signZ (t : B) : ℤ := if t = 0 then 1 else -1

lemma signZ_zero : signZ 0 = 1 := rfl

lemma signZ_one : signZ 1 = -1 := by decide

lemma signZ_add (a b : B) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma z2_eq_zero_or_one (x : B) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

lemma z2_add_self (x : B) : x + x = 0 := by
  fin_cases x <;> decide

lemma z2_add_eq_zero_iff (a b : B) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [z2_add_self, add_zero]
      _ = (a + b) + b := by ring
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact z2_add_self a

lemma dot_add_left {α : Type*} [Fintype α] (u v w : α → B) :
    dotProduct (u + v) w = dotProduct u w + dotProduct v w := by
  simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {α : Type*} [Fintype α] (u v w : α → B) :
    dotProduct u (v + w) = dotProduct u v + dotProduct u w := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_zero_left {α : Type*} [Fintype α] (w : α → B) :
    dotProduct (0 : α → B) w = 0 := by
  simp [dotProduct]

lemma card_V (k : ℕ) [NeZero k] : (Fintype.card (ZMod k → B) : ℤ) = (2 : ℤ) ^ k := by
  rw [Fintype.card_fun, ZMod.card, ZMod.card]
  norm_cast

lemma dot_rot {k : ℕ} [NeZero k] (s : ℕ) (a w : ZMod k → B) :
    dotProduct a (fun i => w (i - (s : ZMod k))) =
      dotProduct (fun i => a (i + (s : ZMod k))) w := by
  simp only [dotProduct]
  refine (Equiv.sum_comp (Equiv.addRight (s : ZMod k))
    (fun i => a i * w (i - (s : ZMod k)))).symm.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma sum_signZ_dot {k : ℕ} [NeZero k] (v : ZMod k → B) :
    (∑ y : ZMod k → B, signZ (dotProduct v y)) =
      if v = 0 then (2 : ℤ) ^ k else 0 := by
  have h := PEqualNP.Outside.L_meta_25750_aux.sum_signZ_dotProduct v
  rw [card_V k] at h
  exact h

lemma kernel_eq_walsh {k : ℕ} [NeZero k] (d : ℕ) (a b : ZMod k → B) :
    (∑ u ∈ Finset.univ.filter (fun v : ZMod k → B =>
        (fun i => v (i - (d : ZMod k)) + v i + v (i + (d : ZMod k))) = a),
      Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j =>
        let i := (j : ZMod k)
        (fun (l h : B) => signZ ((u i + b i + b (i - 2)) * l + b (i - 1) * l * h) : Matrix B B ℤ))))) =
    ∑ x : ZMod k → B, signZ (dotProduct a x +
      dotProduct b (fun j =>
        let y := fun i => x (i - (d : ZMod k)) + x i + x (i + (d : ZMod k))
        y j + (1 + y (j + 1)) * y (j + 2))) := by
  have h := ((PEqualNP.Outside.L_meta_25750 k d a b).1).symm
  dsimp only at h
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro u _
  congr 2
  have hfm : ∀ (f : ZMod k → Matrix B B ℤ) (l : List ℕ),
      (do let a ← l; pure (a : ZMod k)).map f = l.map (fun j : ℕ => f (j : ZMod k)) := by
    intro f l
    induction l with
    | nil => rfl
    | cons a tl ih =>
      simp only [List.bind_eq_flatMap, List.flatMap_cons, List.pure_def, List.singleton_append,
        List.map_cons] at ih ⊢
      rw [ih]
  exact hfm (fun i => (fun l h => signZ ((u i + b i + b (i - 2)) * l + b (i - 1) * l * h) : Matrix B B ℤ))
    (List.range k)

lemma sum_kernel_mul_sign {k : ℕ} [NeZero k] (d : ℕ) (p X : ZMod k → B) :
    let mix := fun (x : ZMod k → B) (i : ZMod k) => x (i - (d : ZMod k)) + x i + x (i + (d : ZMod k))
    let nl := fun (y : ZMod k → B) (j : ZMod k) => y j + (1 + y (j + 1)) * y (j + 2)
    let ker := fun (a b : ZMod k → B) =>
      ∑ u ∈ Finset.univ.filter (fun v : ZMod k → B => mix v = a),
        Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j =>
          let i := (j : ZMod k)
          (fun (l h : B) => signZ ((u i + b i + b (i - 2)) * l + b (i - 1) * l * h) : Matrix B B ℤ))))
    (∑ a : ZMod k → B, ker a p * signZ (dotProduct a X)) =
      (2 : ℤ) ^ k * signZ (dotProduct p (nl (mix X))) := by
  intro mix nl ker
  have hker : ∀ a : ZMod k → B,
      ker a p * signZ (dotProduct a X) =
        ∑ x : ZMod k → B, signZ (dotProduct p (nl (mix x))) * signZ (dotProduct (x + X) a) := by
    intro a
    dsimp only [ker]
    rw [kernel_eq_walsh d a p, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [← signZ_add, ← signZ_add]
    congr 1
    rw [dot_add_left, dotProduct_comm x a, dotProduct_comm X a]
    ring
  simp_rw [hker]
  rw [Finset.sum_comm]
  have hinner : ∀ x : ZMod k → B,
      (∑ a : ZMod k → B, signZ (dotProduct p (nl (mix x))) * signZ (dotProduct (x + X) a)) =
        if x = X then (2 : ℤ) ^ k * signZ (dotProduct p (nl (mix X))) else 0 := by
    intro x
    rw [← Finset.mul_sum, sum_signZ_dot (x + X)]
    have hiff : x + X = 0 ↔ x = X := by
      constructor
      · intro h; funext i; exact (z2_add_eq_zero_iff (x i) (X i)).mp (congrFun h i)
      · intro h; subst h; funext i; exact z2_add_self (x i)
    by_cases hx : x = X
    · rw [if_pos (hiff.mpr hx), if_pos hx, hx, mul_comm]
    · rw [if_neg (fun h => hx (hiff.mp h)), if_neg hx, mul_zero]
  simp_rw [hinner]
  rw [Finset.sum_ite_eq' Finset.univ X]
  simp

lemma H_formula_gen (k : ℕ) [NeZero k] (row col : ZMod k → B) (C1 C2 : ℕ → (ZMod k → B)) :
    let I := ZMod k
    let V := I → B
    let N := (2 : ℤ) ^ k
    let rot := fun (s : ℕ) (word : V) (i : I) => word (i - (s : I))
    let back := fun (s : ℕ) (b : V) (i : I) => b (i + (s : I))
    let mix := fun (d : ℕ) (x : V) (i : I) => x (i - (d : I)) + x i + x (i + (d : I))
    let nl := fun (y : V) (j : I) => y j + (1 + y (j + 1)) * y (j + 2)
    let kernel := fun (d : ℕ) (a b : V) =>
      ∑ u ∈ Finset.univ.filter (fun v : V => mix d v = a),
        Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j =>
          let i := (j : I)
          (fun (l h : B) => signZ ((u i + b i + b (i - 2)) * l + b (i - 1) * l * h) : Matrix B B ℤ))))
    let initial := fun (a b q : V) =>
      if q + back 1 a + back 3 b = 0 then N * signZ (dotProduct a row + dotProduct b col) else 0
    ∀ (n : ℕ) (a b q : V),
      let orbit := fun (key : V) =>
        (List.range n).foldl (fun (st : V × V) tick =>
          (nl (mix 1 st.1) + rot (2 * tick) key + C1 tick,
           nl (mix 2 st.2) + rot (3 * (tick + 1) + 1) key + C2 tick))
          (rot 1 key + row, rot 3 key + col)
      let H := (List.range n).foldl (fun (old : V → V → V → ℤ) roundIndex p s t =>
        signZ (dotProduct p (C1 roundIndex) + dotProduct s (C2 roundIndex)) *
          ∑ a' : V, ∑ b' : V, kernel 1 a' p * kernel 2 b' s *
            old a' b' (t + back (2 * roundIndex) p + back (3 * (roundIndex + 1) + 1) s)) initial
      H a b q = N ^ (2 * n) *
        ∑ w : V, signZ (dotProduct a (orbit w).1 + dotProduct b (orbit w).2 + dotProduct q w) := by
  intro I V N rot back mix nl kernel initial n
  induction n with
  | zero =>
    intro a b q
    dsimp only
    simp only [List.range_zero, List.foldl_nil, Nat.mul_zero, pow_zero, one_mul]
    have hterm : ∀ w : V,
        signZ (dotProduct a (rot 1 w + row) + dotProduct b (rot 3 w + col) + dotProduct q w) =
          signZ (dotProduct a row + dotProduct b col) *
            signZ (dotProduct (q + back 1 a + back 3 b) w) := by
      intro w
      rw [← signZ_add]
      congr 1
      rw [dot_add_right, dot_add_right, dot_rot 1 a w, dot_rot 3 b w,
        dot_add_left, dot_add_left]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    have hdot := sum_signZ_dot (q + back 1 a + back 3 b)
    change initial a b q = signZ (dotProduct a row + dotProduct b col) *
      ∑ y : ZMod k → B, signZ (dotProduct (q + back 1 a + back 3 b) y)
    rw [hdot]
    dsimp only [initial, N]
    split_ifs <;> ring
  | succ n ih =>
    intro p s t
    dsimp only
    conv_lhs => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set orbN : V → V × V := fun key =>
      (List.range n).foldl (fun (st : V × V) tick =>
        (nl (mix 1 st.1) + rot (2 * tick) key + C1 tick,
         nl (mix 2 st.2) + rot (3 * (tick + 1) + 1) key + C2 tick))
        (rot 1 key + row, rot 3 key + col)
    have horb_succ : ∀ w : V,
        ((List.range (n + 1)).foldl (fun (st : V × V) tick =>
          (nl (mix 1 st.1) + rot (2 * tick) w + C1 tick,
           nl (mix 2 st.2) + rot (3 * (tick + 1) + 1) w + C2 tick))
          (rot 1 w + row, rot 3 w + col)) =
        (nl (mix 1 (orbN w).1) + rot (2 * n) w + C1 n,
         nl (mix 2 (orbN w).2) + rot (3 * (n + 1) + 1) w + C2 n) := by
      intro w
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp_rw [horb_succ]
    set t' := t + back (2 * n) p + back (3 * (n + 1) + 1) s
    have hih : ∀ a' b' : V,
        ((List.range n).foldl (fun (old : V → V → V → ℤ) roundIndex p s t =>
          signZ (dotProduct p (C1 roundIndex) + dotProduct s (C2 roundIndex)) *
            ∑ a'' : V, ∑ b'' : V, kernel 1 a'' p * kernel 2 b'' s *
              old a'' b'' (t + back (2 * roundIndex) p + back (3 * (roundIndex + 1) + 1) s))
          initial) a' b' t' =
        N ^ (2 * n) *
          ∑ w : V, signZ (dotProduct a' (orbN w).1 + dotProduct b' (orbN w).2 + dotProduct t' w) :=
      fun a' b' => ih a' b' t'
    simp_rw [hih]
    have hpull :
        (∑ a' : V, ∑ b' : V, kernel 1 a' p * kernel 2 b' s *
          (N ^ (2 * n) * ∑ w : V, signZ (dotProduct a' (orbN w).1 + dotProduct b' (orbN w).2 + dotProduct t' w))) =
        N ^ (2 * n) *
          ∑ w : V, signZ (dotProduct t' w) *
            (∑ a' : V, kernel 1 a' p * signZ (dotProduct a' (orbN w).1)) *
            (∑ b' : V, kernel 2 b' s * signZ (dotProduct b' (orbN w).2)) := by
      have h1 : ∀ a' b' : V,
          kernel 1 a' p * kernel 2 b' s *
            (N ^ (2 * n) * ∑ w : V, signZ (dotProduct a' (orbN w).1 + dotProduct b' (orbN w).2 + dotProduct t' w)) =
          N ^ (2 * n) *
            ∑ w : V, signZ (dotProduct t' w) *
              (kernel 1 a' p * signZ (dotProduct a' (orbN w).1)) *
              (kernel 2 b' s * signZ (dotProduct b' (orbN w).2)) := by
        intro a' b'
        rw [← mul_assoc (kernel 1 a' p * kernel 2 b' s),
          mul_comm (kernel 1 a' p * kernel 2 b' s) (N ^ (2 * n)), mul_assoc (N ^ (2 * n))]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        rw [signZ_add, signZ_add]
        ring
      simp_rw [h1, ← Finset.mul_sum]
      congr 1
      calc
        ∑ a' : V, ∑ b' : V, ∑ w : V,
            signZ (dotProduct t' w) * (kernel 1 a' p * signZ (dotProduct a' (orbN w).1)) *
              (kernel 2 b' s * signZ (dotProduct b' (orbN w).2))
          = ∑ a' : V, ∑ w : V, ∑ b' : V,
              signZ (dotProduct t' w) * (kernel 1 a' p * signZ (dotProduct a' (orbN w).1)) *
                (kernel 2 b' s * signZ (dotProduct b' (orbN w).2)) := by
              apply Finset.sum_congr rfl
              intro a' _
              exact Finset.sum_comm
        _ = ∑ w : V, ∑ a' : V, ∑ b' : V,
              signZ (dotProduct t' w) * (kernel 1 a' p * signZ (dotProduct a' (orbN w).1)) *
                (kernel 2 b' s * signZ (dotProduct b' (orbN w).2)) := Finset.sum_comm
        _ = ∑ w : V, signZ (dotProduct t' w) *
              (∑ a' : V, kernel 1 a' p * signZ (dotProduct a' (orbN w).1)) *
              (∑ b' : V, kernel 2 b' s * signZ (dotProduct b' (orbN w).2)) := by
              apply Finset.sum_congr rfl
              intro w _
              simp_rw [← Finset.mul_sum]
              rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hpull]
    have hker1 : ∀ w : V,
        (∑ a' : V, kernel 1 a' p * signZ (dotProduct a' (orbN w).1)) =
          N * signZ (dotProduct p (nl (mix 1 (orbN w).1))) :=
      fun w => sum_kernel_mul_sign 1 p (orbN w).1
    have hker2 : ∀ w : V,
        (∑ b' : V, kernel 2 b' s * signZ (dotProduct b' (orbN w).2)) =
          N * signZ (dotProduct s (nl (mix 2 (orbN w).2))) :=
      fun w => sum_kernel_mul_sign 2 s (orbN w).2
    simp_rw [hker1, hker2]
    have hpow : N ^ (2 * (n + 1)) = N ^ (2 * n) * (N * N) := by
      have : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [this, pow_add, sq]
    rw [hpow]
    rw [mul_left_comm (signZ _), mul_assoc (N ^ (2 * n))]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have hsign_eq :
        signZ (dotProduct p (C1 n) + dotProduct s (C2 n)) *
          (signZ (dotProduct t' w) * signZ (dotProduct p (nl (mix 1 (orbN w).1))) *
            signZ (dotProduct s (nl (mix 2 (orbN w).2)))) =
        signZ (dotProduct p (nl (mix 1 (orbN w).1) + rot (2 * n) w + C1 n) +
          dotProduct s (nl (mix 2 (orbN w).2) + rot (3 * (n + 1) + 1) w + C2 n) +
          dotProduct t w) := by
      rw [← signZ_add, ← signZ_add, ← signZ_add]
      congr 1
      dsimp only [t']
      rw [dot_add_left, dot_add_left, ← dot_rot (2 * n) p w, ← dot_rot (3 * (n + 1) + 1) s w,
        dot_add_right, dot_add_right, dot_add_right, dot_add_right]
      ring
    calc
      signZ (dotProduct p (C1 n) + dotProduct s (C2 n)) *
          (signZ (dotProduct t' w) * (N * signZ (dotProduct p (nl (mix 1 (orbN w).1)))) *
            (N * signZ (dotProduct s (nl (mix 2 (orbN w).2)))))
        = (N * N) * (signZ (dotProduct p (C1 n) + dotProduct s (C2 n)) *
            (signZ (dotProduct t' w) * signZ (dotProduct p (nl (mix 1 (orbN w).1))) *
              signZ (dotProduct s (nl (mix 2 (orbN w).2))))) := by ring
      _ = N * N * signZ (dotProduct p (nl (mix 1 (orbN w).1) + rot (2 * n) w + C1 n) +
            dotProduct s (nl (mix 2 (orbN w).2) + rot (3 * (n + 1) + 1) w + C2 n) +
            dotProduct t w) := by rw [hsign_eq]

lemma card_supported {k : ℕ} [NeZero k] (S : Finset (ZMod k)) :
    (Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0)).card =
      2 ^ S.card := by
  let supp := Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0)
  have hbij : supp.card = Fintype.card (↥S → B) := by
    refine Finset.card_bij (fun mask _ => fun i : ↥S => mask i.1) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro m1 hm1 m2 hm2 hEq
      funext i
      by_cases hi : i ∈ S
      · exact congrFun hEq ⟨i, hi⟩
      · rw [(Finset.mem_filter.mp hm1).2 i hi, (Finset.mem_filter.mp hm2).2 i hi]
    · intro f _
      let m : ZMod k → B := fun i => if h : i ∈ S then f ⟨i, h⟩ else 0
      refine ⟨m, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hi
        simp [m, hi]
      · funext ⟨i, hi⟩
        simp [m, hi]
  rw [hbij, Fintype.card_fun, ZMod.card, Fintype.card_coe]

lemma sum_supported_sign {k : ℕ} [NeZero k] (S : Finset (ZMod k)) (u : ZMod k → B) :
    (∑ a ∈ Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0),
      signZ (dotProduct a u)) =
    if (∀ i ∈ S, u i = 0) then (2 : ℤ) ^ S.card else 0 := by
  let supp := Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0)
  by_cases hall : ∀ i ∈ S, u i = 0
  · rw [if_pos hall]
    have h1 : ∀ a ∈ supp, signZ (dotProduct a u) = 1 := by
      intro a ha
      have hdot : dotProduct a u = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i ∈ S
        · rw [hall i hi, mul_zero]
        · rw [(Finset.mem_filter.mp ha).2 i hi, zero_mul]
      rw [hdot, signZ_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one, card_supported]
    norm_cast
  · rw [if_neg hall]
    have hex : ∃ i0 ∈ S, u i0 ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hall hno
    obtain ⟨i0, hi0S, hi0ne⟩ := hex
    have hi0_one : u i0 = 1 := by
      rcases z2_eq_zero_or_one (u i0) with h0 | h1
      · exact absurd h0 hi0ne
      · exact h1
    let e0 : ZMod k → B := fun i => if i = i0 then 1 else 0
    have hS : (∑ a ∈ supp, signZ (dotProduct a u)) = -(∑ a ∈ supp, signZ (dotProduct a u)) := by
      have hbij : (∑ a ∈ supp, signZ (dotProduct a u)) =
          ∑ a ∈ supp, signZ (dotProduct (a + e0) u) := by
        symm
        refine Finset.sum_bij (fun a _ => a + e0) ?_ ?_ ?_ ?_
        · intro a ha
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro i hi
          have hne : i ≠ i0 := fun h => hi (h ▸ hi0S)
          simp [e0, hne, (Finset.mem_filter.mp ha).2 i hi]
        · intro a1 _ a2 _ hEq
          exact add_right_cancel hEq
        · intro a ha
          refine ⟨a + e0, ?_, ?_⟩
          · apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            intro i hi
            have hne : i ≠ i0 := fun h => hi (h ▸ hi0S)
            simp [e0, hne, (Finset.mem_filter.mp ha).2 i hi]
          · funext i; simp only [Pi.add_apply]; rw [add_assoc, z2_add_self, add_zero]
        · intro _ _; rfl
      calc
        ∑ a ∈ supp, signZ (dotProduct a u)
          = ∑ a ∈ supp, signZ (dotProduct (a + e0) u) := hbij
        _ = ∑ a ∈ supp, (-signZ (dotProduct a u)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [dot_add_left]
            have hs : dotProduct e0 u = 1 := by
              unfold dotProduct
              rw [Finset.sum_eq_single i0]
              · simp [e0, hi0_one]
              · intro j _ hj; simp [e0, hj]
              · intro h; exact (h (Finset.mem_univ i0)).elim
            rw [hs, signZ_add, signZ_one]
            ring
        _ = -(∑ a ∈ supp, signZ (dotProduct a u)) := by rw [Finset.sum_neg_distrib]
    change ∑ a ∈ supp, signZ (dotProduct a u) = 0
    omega

end PEqualNP.Outside.L_meta_25754

theorem PEqualNP.Outside.L_meta_25754 : (∀ (k : ℕ) [NeZero k] (r : ℕ),
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let N := (2:ℤ)^k
  let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
  let rot := fun (s : ℕ) (word : V) (i : I) => word (i-(s : I))
  let back := fun (s : ℕ) (b : V) (i : I) => b (i+(s : I))
  let mix := fun (d : ℕ) (x : V) (i : I) => x (i-(d : I)) + x i + x (i+(d : I))
  let nl := fun (y : V) (j : I) => y j + (1+y (j+1))*y (j+2)
  let kernel := fun (d : ℕ) (a b : V) =>
    ∑ u ∈ Finset.univ.filter (fun v : V => mix d v = a),
      Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j =>
        let i := (j : I)
        (fun (l h : B) => sign ((u i+b i+b (i-2))*l+b (i-1)*l*h) : Matrix B B ℤ))))
  ∀ (row col : V) (C : ℕ → V),
    let orbit := fun (key : V) =>
      (List.range r).foldl (fun (st : V × V) tick =>
        (nl (mix 1 st.1) + rot (2*tick) key + C (tick+1),
         nl (mix 2 st.2) + rot (3*(tick+1)+1) key + C (r+tick+1)))
        (rot 1 key + row, rot 3 key + col)
    let initial := fun (a b q : V) =>
      if q + back 1 a + back 3 b = 0 then N*sign (dotProduct a row + dotProduct b col) else 0
    let H := (List.range r).foldl (fun (old : V → V → V → ℤ) roundIndex p s t =>
      sign (dotProduct p (C (roundIndex+1)) + dotProduct s (C (r+roundIndex+1))) *
        ∑ a : V, ∑ b : V, kernel 1 a p * kernel 2 b s *
          old a b (t + back (2*roundIndex) p + back (3*(roundIndex+1)+1) s)) initial
    (∀ a b q : V, H a b q = N^(2*r) *
      ∑ w : V, sign (dotProduct a (orbit w).1 + dotProduct b (orbit w).2 + dotProduct q w)) ∧
    ∀ (S T : Finset I) (y z : V),
      let supported := fun (sites : Finset I) => Finset.univ.filter (fun mask : V =>
        ∀ i : I, i ∉ sites → mask i = 0)
      let passing := Finset.univ.filter (fun w : V =>
        (∀ i ∈ S, (orbit w).1 i = y i) ∧ (∀ j ∈ T, (orbit w).2 j = z j))
      (∑ a ∈ supported S, ∑ b ∈ supported T,
        sign (dotProduct a y + dotProduct b z) * H a b 0) =
        N^(2*r) * (2:ℤ)^(S.card+T.card) * (passing.card : ℤ)) := by
  open PEqualNP.Outside.L_meta_25754 in
  intro k _ r I B V N sign rot back mix nl kernel row col C orbit initial H
  have hH : ∀ a b q : V, H a b q = N ^ (2 * r) *
      ∑ w : V, sign (dotProduct a (orbit w).1 + dotProduct b (orbit w).2 + dotProduct q w) :=
    H_formula_gen k row col (fun tick => C (tick + 1)) (fun tick => C (r + tick + 1)) r
  refine ⟨hH, ?_⟩
  intro S T y z supported passing
  have hsub : ∀ a b : V,
      sign (dotProduct a y + dotProduct b z) * H a b 0 =
        N ^ (2 * r) * ∑ w : V,
          signZ (dotProduct a ((orbit w).1 + y)) * signZ (dotProduct b ((orbit w).2 + z)) := by
    intro a b
    rw [hH a b 0, ← mul_assoc, mul_comm (sign _), mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    change signZ (dotProduct a y + dotProduct b z) *
        signZ (dotProduct a (orbit w).1 + dotProduct b (orbit w).2 + dotProduct 0 w) = _
    rw [dot_zero_left, add_zero, ← signZ_add, ← signZ_add]
    congr 1
    rw [dot_add_right, dot_add_right]
    ring
  simp_rw [hsub]
  simp_rw [← Finset.mul_sum]
  have hswap :
      (∑ a ∈ supported S, ∑ b ∈ supported T, ∑ w : V,
        signZ (dotProduct a ((orbit w).1 + y)) * signZ (dotProduct b ((orbit w).2 + z))) =
      ∑ w : V,
        (∑ a ∈ supported S, signZ (dotProduct a ((orbit w).1 + y))) *
        (∑ b ∈ supported T, signZ (dotProduct b ((orbit w).2 + z))) := by
    calc
      ∑ a ∈ supported S, ∑ b ∈ supported T, ∑ w : V,
          signZ (dotProduct a ((orbit w).1 + y)) * signZ (dotProduct b ((orbit w).2 + z))
        = ∑ a ∈ supported S, ∑ w : V, ∑ b ∈ supported T,
            signZ (dotProduct a ((orbit w).1 + y)) * signZ (dotProduct b ((orbit w).2 + z)) := by
            apply Finset.sum_congr rfl
            intro a _
            exact Finset.sum_comm
      _ = ∑ w : V, ∑ a ∈ supported S, ∑ b ∈ supported T,
            signZ (dotProduct a ((orbit w).1 + y)) * signZ (dotProduct b ((orbit w).2 + z)) :=
            Finset.sum_comm
      _ = ∑ w : V,
            (∑ a ∈ supported S, signZ (dotProduct a ((orbit w).1 + y))) *
            (∑ b ∈ supported T, signZ (dotProduct b ((orbit w).2 + z))) := by
            apply Finset.sum_congr rfl
            intro w _
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hswap]
  have hterm : ∀ w : V,
      (∑ a ∈ supported S, signZ (dotProduct a ((orbit w).1 + y))) *
      (∑ b ∈ supported T, signZ (dotProduct b ((orbit w).2 + z))) =
      if (∀ i ∈ S, (orbit w).1 i = y i) ∧ (∀ j ∈ T, (orbit w).2 j = z j) then
        (2 : ℤ) ^ (S.card + T.card)
      else 0 := by
    intro w
    have h1 := sum_supported_sign S ((orbit w).1 + y)
    have h2 := sum_supported_sign T ((orbit w).2 + z)
    change (∑ a ∈ Finset.univ.filter (fun mask : ZMod k → PEqualNP.Outside.L_meta_25754.B => ∀ i : ZMod k, i ∉ S → mask i = 0),
        signZ (dotProduct a ((orbit w).1 + y))) *
      (∑ b ∈ Finset.univ.filter (fun mask : ZMod k → PEqualNP.Outside.L_meta_25754.B => ∀ i : ZMod k, i ∉ T → mask i = 0),
        signZ (dotProduct b ((orbit w).2 + z))) = _
    rw [h1, h2]
    have hiff1 : (∀ i ∈ S, ((orbit w).1 + y) i = 0) ↔ (∀ i ∈ S, (orbit w).1 i = y i) := by
      constructor <;> intro h i hi
      · exact (z2_add_eq_zero_iff _ _).mp (h i hi)
      · exact (z2_add_eq_zero_iff _ _).mpr (h i hi)
    have hiff2 : (∀ j ∈ T, ((orbit w).2 + z) j = 0) ↔ (∀ j ∈ T, (orbit w).2 j = z j) := by
      constructor <;> intro h j hj
      · exact (z2_add_eq_zero_iff _ _).mp (h j hj)
      · exact (z2_add_eq_zero_iff _ _).mpr (h j hj)
    split_ifs <;> simp_all [hiff1, hiff2, pow_add]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  change N ^ (2 * r) * ∑ _w ∈ passing, (2 : ℤ) ^ (S.card + T.card) = _
  rw [Finset.sum_const, nsmul_eq_mul]
  ring
