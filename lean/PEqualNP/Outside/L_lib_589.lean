import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_589_aux

open scoped BigOperators

private def satF {n : ℕ} (C : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (w : Fin n → Bool) : Bool :=
  decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)

private lemma card_proj_eq {n m : ℕ} (f : Fin m ↪ Fin n) (P : (Fin m → Bool) → Bool) :
    (Finset.univ.filter (fun w : Fin n → Bool => P (fun i => w (f i)) = true)).card * 2 ^ m =
    (Finset.univ.filter (fun u : Fin m → Bool => P u = true)).card * 2 ^ n := by
  classical
  let S : Finset (Fin n) := Finset.univ.map f
  let Sc : Finset (Fin n) := Finset.univ \ S
  have hSc_card : Sc.card + m = n := by
    have hS : S.card = m := by simp [S]
    have hle : S.card ≤ n := by
      calc S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    have hsd : Sc.card = n - m := by
      simp [Sc, Finset.card_sdiff, hS]
    omega
  let e : (Fin n → Bool) ≃ (Fin m → Bool) × ({x : Fin n // x ∈ Sc} → Bool) :=
    { toFun := fun w => (fun i => w (f i), fun x => w x.1)
      invFun := fun p x =>
        if hx : ∃ i, f i = x then p.1 (Classical.choose hx)
        else p.2 ⟨x, by
          simp only [Sc, S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_map, true_and]
          intro ⟨i, hi⟩
          exact hx ⟨i, hi⟩⟩
      left_inv := fun w => by
        funext x
        by_cases hx : ∃ i, f i = x
        · simp only [dite_eq_left hx]
          rw [Classical.choose_spec hx]
        · simp only [dite_eq_right hx]
      right_inv := fun ⟨u, v⟩ => by
        apply Prod.ext
        · funext i
          have hx : ∃ j, f j = f i := ⟨i, rfl⟩
          simp only [dite_eq_left hx]
          congr 1
          exact f.injective (Classical.choose_spec hx)
        · funext ⟨x, hxSc⟩
          have hx : ¬ ∃ i, f i = x := by
            intro ⟨i, hi⟩
            simp only [Sc, S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_map, true_and] at hxSc
            exact hxSc ⟨i, hi⟩
          simp only [dite_eq_right hx] }
  let A : Finset (Fin n → Bool) := Finset.univ.filter (fun w => P (fun i => w (f i)) = true)
  let B : Finset ((Fin m → Bool) × ({x : Fin n // x ∈ Sc} → Bool)) :=
    (Finset.univ.filter (fun u : Fin m → Bool => P u = true)) ×ˢ
      (Finset.univ : Finset ({x : Fin n // x ∈ Sc} → Bool))
  have hcard : A.card = B.card := by
    refine Finset.card_bij (fun w _ => e w) ?_ ?_ ?_
    · intro w hw
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [B, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true, e,
        Equiv.coe_fn_mk]
      exact hw
    · intro w1 _ w2 _ h
      exact e.injective h
    · intro p hp
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      simp only [B, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : (fun i => (e.symm p) (f i)) = p.1 := by
        have := congrArg Prod.fst (e.apply_symm_apply p)
        exact this
      rw [h1]
      exact hp
  have hB : B.card = (Finset.univ.filter (fun u : Fin m → Bool => P u = true)).card * 2 ^ Sc.card := by
    simp only [B, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe]
  rw [hcard, hB, mul_assoc, ← pow_add, hSc_card]

private lemma card_filter_le_of_proj {n m : ℕ} (f : Fin m ↪ Fin n)
    (P : (Fin m → Bool) → Bool) (Q : (Fin n → Bool) → Bool)
    (himp : ∀ w, Q w = true → P (fun i => w (f i)) = true)
    (hc : (Finset.univ.filter (fun u : Fin m → Bool => P u = true)).card * 2 ≤ 2 ^ m) :
    2 * (Finset.univ.filter (fun w : Fin n → Bool => Q w = true)).card ≤ 2 ^ n := by
  have hsub : (Finset.univ.filter (fun w : Fin n → Bool => Q w = true)).card ≤
      (Finset.univ.filter (fun w : Fin n → Bool => P (fun i => w (f i)) = true)).card := by
    apply Finset.card_le_card
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact himp w hw
  have hproj := card_proj_eq f P
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hmul : 2 * (Finset.univ.filter (fun w : Fin n → Bool => Q w = true)).card * 2 ^ m ≤ 2 ^ n * 2 ^ m := by
    calc 2 * (Finset.univ.filter (fun w : Fin n → Bool => Q w = true)).card * 2 ^ m
        ≤ 2 * (Finset.univ.filter (fun w : Fin n → Bool => P (fun i => w (f i)) = true)).card * 2 ^ m := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hsub)
      _ = 2 * ((Finset.univ.filter (fun w : Fin n → Bool => P (fun i => w (f i)) = true)).card * 2 ^ m) := by ring
      _ = 2 * ((Finset.univ.filter (fun u : Fin m → Bool => P u = true)).card * 2 ^ n) := by rw [hproj]
      _ = ((Finset.univ.filter (fun u : Fin m → Bool => P u = true)).card * 2) * 2 ^ n := by ring
      _ ≤ 2 ^ m * 2 ^ n := Nat.mul_le_mul_right _ hc
      _ = 2 ^ n * 2 ^ m := mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hmul hpos

private lemma half_lt_of_high {n s : ℕ} (hs : 3 ≤ s)
    (C : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (hhigh : 2 ^ n * (2 ^ (s - 1) + 1) ≤
      2 ^ s * (Finset.univ.filter (fun w => satF C w = true)).card) :
    2 ^ n < 2 * (Finset.univ.filter (fun w => satF C w = true)).card := by
  have hs1 : 2 ^ s = 2 * 2 ^ (s - 1) := by
    have : s = (s - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ']
  have hpos : 0 < 2 ^ (s - 1) := Nat.two_pow_pos (s - 1)
  have hlt : 2 ^ n * 2 ^ (s - 1) <
      (2 * (Finset.univ.filter (fun w => satF C w = true)).card) * 2 ^ (s - 1) := by
    have h1 : 2 ^ n * 2 ^ (s - 1) < 2 ^ n * (2 ^ (s - 1) + 1) := by
      have : 0 < 2 ^ n := Nat.two_pow_pos n
      nlinarith
    have h2 : 2 ^ s * (Finset.univ.filter (fun w => satF C w = true)).card =
        (2 * (Finset.univ.filter (fun w => satF C w = true)).card) * 2 ^ (s - 1) := by
      rw [hs1]; ring
    omega
  exact Nat.lt_of_mul_lt_mul_right hlt

private lemma card_gt_half_k3 {n : ℕ} (Adj : Fin n → Fin n → Prop) (σ : Fin n → Bool)
    (Q : (Fin n → Bool) → Bool)
    (hQ : ∀ w, Q w = true → ∀ i j, Adj i j → w i ≠ σ i ∨ w j ≠ σ j)
    (hgt : 2 ^ n < 2 * (Finset.univ.filter (fun w => Q w = true)).card)
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : Adj a b) (h2 : Adj b c) (h3 : Adj a c) : False := by
  let f : Fin 3 ↪ Fin n :=
    ⟨fun i => match i with | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c, by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all⟩
  let P : (Fin 3 → Bool) → Bool := fun u =>
    decide ((u 0 ≠ σ a ∨ u 1 ≠ σ b) ∧ (u 1 ≠ σ b ∨ u 2 ≠ σ c) ∧ (u 0 ≠ σ a ∨ u 2 ≠ σ c))
  have hc : (Finset.univ.filter (fun u : Fin 3 → Bool => P u = true)).card * 2 ≤ 2 ^ 3 := by
    have hdec : ∀ sa sb sc : Bool,
        (Finset.univ.filter (fun u : Fin 3 → Bool =>
          decide ((u 0 ≠ sa ∨ u 1 ≠ sb) ∧ (u 1 ≠ sb ∨ u 2 ≠ sc) ∧ (u 0 ≠ sa ∨ u 2 ≠ sc)) = true)).card * 2 ≤ 2 ^ 3 := by
      decide
    exact hdec (σ a) (σ b) (σ c)
  have hle := card_filter_le_of_proj f P Q (fun w hw => by
    simp only [P, f, decide_eq_true_eq]
    exact ⟨hQ w hw a b h1, hQ w hw b c h2, hQ w hw a c h3⟩) hc
  omega

private lemma card_gt_half_p4 {n : ℕ} (Adj : Fin n → Fin n → Prop) (σ : Fin n → Bool)
    (Q : (Fin n → Bool) → Bool)
    (hQ : ∀ w, Q w = true → ∀ i j, Adj i j → w i ≠ σ i ∨ w j ≠ σ j)
    (hgt : 2 ^ n < 2 * (Finset.univ.filter (fun w => Q w = true)).card)
    {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : Adj a b) (h2 : Adj b c) (h3 : Adj c d) : False := by
  let f : Fin 4 ↪ Fin n :=
    ⟨fun i => match i with | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d, by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all⟩
  let P : (Fin 4 → Bool) → Bool := fun u =>
    decide ((u 0 ≠ σ a ∨ u 1 ≠ σ b) ∧ (u 1 ≠ σ b ∨ u 2 ≠ σ c) ∧ (u 2 ≠ σ c ∨ u 3 ≠ σ d))
  have hc : (Finset.univ.filter (fun u : Fin 4 → Bool => P u = true)).card * 2 ≤ 2 ^ 4 := by
    have hdec : ∀ sa sb sc sd : Bool,
        (Finset.univ.filter (fun u : Fin 4 → Bool =>
          decide ((u 0 ≠ sa ∨ u 1 ≠ sb) ∧ (u 1 ≠ sb ∨ u 2 ≠ sc) ∧ (u 2 ≠ sc ∨ u 3 ≠ sd)) = true)).card * 2 ≤ 2 ^ 4 := by
      decide
    exact hdec (σ a) (σ b) (σ c) (σ d)
  have hle := card_filter_le_of_proj f P Q (fun w hw => by
    simp only [P, f, decide_eq_true_eq]
    exact ⟨hQ w hw a b h1, hQ w hw b c h2, hQ w hw c d h3⟩) hc
  omega

private lemma card_gt_half_k12_k2 {n : ℕ} (Adj : Fin n → Fin n → Prop) (σ : Fin n → Bool)
    (Q : (Fin n → Bool) → Bool)
    (hQ : ∀ w, Q w = true → ∀ i j, Adj i j → w i ≠ σ i ∨ w j ≠ σ j)
    (hgt : 2 ^ n < 2 * (Finset.univ.filter (fun w => Q w = true)).card)
    {a b c d e : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (h1 : Adj a b) (h2 : Adj a c) (h3 : Adj d e) : False := by
  let f : Fin 5 ↪ Fin n :=
    ⟨fun i => match i with
      | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d | ⟨4, _⟩ => e, by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all⟩
  let P : (Fin 5 → Bool) → Bool := fun u =>
    decide ((u 0 ≠ σ a ∨ u 1 ≠ σ b) ∧ (u 0 ≠ σ a ∨ u 2 ≠ σ c) ∧ (u 3 ≠ σ d ∨ u 4 ≠ σ e))
  have hc : (Finset.univ.filter (fun u : Fin 5 → Bool => P u = true)).card * 2 ≤ 2 ^ 5 := by
    have hdec : ∀ sa sb sc sd se : Bool,
        (Finset.univ.filter (fun u : Fin 5 → Bool =>
          decide ((u 0 ≠ sa ∨ u 1 ≠ sb) ∧ (u 0 ≠ sa ∨ u 2 ≠ sc) ∧ (u 3 ≠ sd ∨ u 4 ≠ se)) = true)).card * 2 ≤ 2 ^ 5 := by
      decide
    exact hdec (σ a) (σ b) (σ c) (σ d) (σ e)
  have hle := card_filter_le_of_proj f P Q (fun w hw => by
    simp only [P, f, decide_eq_true_eq]
    exact ⟨hQ w hw a b h1, hQ w hw a c h2, hQ w hw d e h3⟩) hc
  omega

private lemma card_gt_half_3k2 {n : ℕ} (Adj : Fin n → Fin n → Prop) (σ : Fin n → Bool)
    (Q : (Fin n → Bool) → Bool)
    (hQ : ∀ w, Q w = true → ∀ i j, Adj i j → w i ≠ σ i ∨ w j ≠ σ j)
    (hgt : 2 ^ n < 2 * (Finset.univ.filter (fun w => Q w = true)).card)
    {a b c d e x : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hax : a ≠ x)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbx : b ≠ x)
    (hcd : c ≠ d) (hce : c ≠ e) (hcx : c ≠ x)
    (hde : d ≠ e) (hdx : d ≠ x) (hex : e ≠ x)
    (h1 : Adj a b) (h2 : Adj c d) (h3 : Adj e x) : False := by
  let f : Fin 6 ↪ Fin n :=
    ⟨fun i => match i with
      | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d | ⟨4, _⟩ => e | ⟨5, _⟩ => x, by
      intro i1 i2 hi
      fin_cases i1 <;> fin_cases i2 <;> simp_all⟩
  let P : (Fin 6 → Bool) → Bool := fun u =>
    decide ((u 0 ≠ σ a ∨ u 1 ≠ σ b) ∧ (u 2 ≠ σ c ∨ u 3 ≠ σ d) ∧ (u 4 ≠ σ e ∨ u 5 ≠ σ x))
  have hc : (Finset.univ.filter (fun u : Fin 6 → Bool => P u = true)).card * 2 ≤ 2 ^ 6 := by
    have hdec : ∀ sa sb sc sd se sx : Bool,
        (Finset.univ.filter (fun u : Fin 6 → Bool =>
          decide ((u 0 ≠ sa ∨ u 1 ≠ sb) ∧ (u 2 ≠ sc ∨ u 3 ≠ sd) ∧ (u 4 ≠ se ∨ u 5 ≠ sx)) = true)).card * 2 ≤ 2 ^ 6 := by
      decide
    exact hdec (σ a) (σ b) (σ c) (σ d) (σ e) (σ x)
  have hle := card_filter_le_of_proj f P Q (fun w hw => by
    simp only [P, f, decide_eq_true_eq]
    exact ⟨hQ w hw a b h1, hQ w hw c d h2, hQ w hw e x h3⟩) hc
  omega

private lemma star_card_eq {n : ℕ} (v : Fin n) (U : Finset (Fin n)) (hv : v ∉ U)
    (σ : Fin n → Bool) :
    (Finset.univ.filter (fun w : Fin n → Bool =>
      decide (∀ u ∈ U, w v ≠ σ v ∨ w u ≠ σ u) = true)).card * 2 ^ (U.card + 1) =
    (2 ^ U.card + 1) * 2 ^ n := by
  classical
  let eU : Fin U.card ≃ U := (Fintype.equivFinOfCardEq (by simp)).symm
  let f : Fin (U.card + 1) ↪ Fin n :=
    ⟨fun i => if h : i.val < U.card then (eU ⟨i.val, h⟩).1 else v, by
      intro i j hij
      by_cases hi : i.val < U.card <;> by_cases hj : j.val < U.card
      · simp only [dite_eq_left hi, dite_eq_left hj] at hij
        have heq : eU ⟨i.val, hi⟩ = eU ⟨j.val, hj⟩ := Subtype.ext hij
        have hfin := eU.injective heq
        exact Fin.ext (congrArg (fun x : Fin U.card => x.val) hfin)
      · simp only [dite_eq_left hi, dite_eq_right hj] at hij
        exact (hv (hij ▸ (eU ⟨i.val, hi⟩).2)).elim
      · simp only [dite_eq_right hi, dite_eq_left hj] at hij
        exact (hv (hij.symm ▸ (eU ⟨j.val, hj⟩).2)).elim
      · exact Fin.ext (by omega)⟩
  let P : (Fin (U.card + 1) → Bool) → Bool := fun u =>
    decide (u (Fin.last U.card) ≠ σ v ∨ ∀ i : Fin U.card, u i.castSucc ≠ σ (eU i).1)
  have hflast : f (Fin.last U.card) = v := by
    change (if h : (Fin.last U.card).val < U.card then _ else v) = v
    simp only [Fin.val_last, dite_eq_right (Nat.lt_irrefl U.card)]
  have hfcast : ∀ i : Fin U.card, f i.castSucc = (eU i).1 := by
    intro i
    change (if h : i.castSucc.val < U.card then (eU ⟨i.castSucc.val, h⟩).1 else v) = (eU i).1
    simp only [Fin.val_castSucc, dite_eq_left i.isLt]
  have hfeq :
      Finset.univ.filter (fun w : Fin n → Bool =>
        decide (∀ u ∈ U, w v ≠ σ v ∨ w u ≠ σ u) = true) =
      Finset.univ.filter (fun w : Fin n → Bool => P (fun i => w (f i)) = true) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, P, hflast, hfcast]
    constructor
    · intro h
      by_cases hwv : w v = σ v
      · right
        intro i
        rcases h (eU i).1 (eU i).2 with h1 | h2
        · exact (h1 hwv).elim
        · exact h2
      · left; exact hwv
    · intro h u hu
      rcases h with h1 | h2
      · left; exact h1
      · right
        let i := eU.symm ⟨u, hu⟩
        have hi := h2 i
        simp only [i, Equiv.apply_symm_apply] at hi
        exact hi
  rw [hfeq, card_proj_eq f P]
  congr 1
  let S0 : Finset (Fin (U.card + 1) → Bool) :=
    Finset.univ.filter (fun u => u (Fin.last U.card) ≠ σ v)
  let u1 : Fin (U.card + 1) → Bool := fun i =>
    if h : i.val < U.card then !(σ (eU ⟨i.val, h⟩).1) else σ v
  have hpart : Finset.univ.filter (fun u : Fin (U.card + 1) → Bool => P u = true) = insert u1 S0 := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, S0, P,
      decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · right; exact h
      · by_cases hlast : u (Fin.last U.card) = σ v
        · left
          funext i
          by_cases hi : i.val < U.card
          · simp only [u1, dite_eq_left hi]
            have hne := h ⟨i.val, hi⟩
            change u ⟨i.val, _⟩ ≠ σ (eU ⟨i.val, hi⟩).1 at hne
            cases hu : u i <;> cases hs : σ (eU ⟨i.val, hi⟩).1 <;> simp_all
          · have hil : i = Fin.last U.card := Fin.ext (by simp only [Fin.val_last]; omega)
            subst hil
            simp only [u1, Fin.val_last, dite_eq_right (Nat.lt_irrefl U.card)]
            exact hlast
        · right; exact hlast
    · rintro (rfl | h)
      · right
        intro i
        simp only [u1, Fin.val_castSucc, dite_eq_left i.isLt]
        cases σ (eU i).1 <;> decide
      · left; exact h
  have hu1_not : u1 ∉ S0 := by
    simp [S0, u1, Fin.val_last]
  have hS0 : S0.card = 2 ^ U.card := by
    let g : (Fin U.card → Bool) → (Fin (U.card + 1) → Bool) := fun a i =>
      if h : i.val < U.card then a ⟨i.val, h⟩ else !(σ v)
    have hg : S0 = Finset.univ.image g := by
      ext u
      simp only [S0, Finset.mem_filter, Finset.mem_univ, Finset.mem_image, true_and]
      constructor
      · intro h
        refine ⟨fun i => u i.castSucc, ?_⟩
        funext i
        by_cases hi : i.val < U.card
        · simp only [g, dite_eq_left hi]; rfl
        · have hil : i = Fin.last U.card := Fin.ext (by simp only [Fin.val_last]; omega)
          subst hil
          simp only [g, Fin.val_last, dite_eq_right (Nat.lt_irrefl U.card)]
          cases hu : u (Fin.last U.card) <;> cases hs : σ v <;> simp_all
      · rintro ⟨a, rfl⟩
        simp only [g, Fin.val_last, dite_eq_right (Nat.lt_irrefl U.card)]
        cases σ v <;> decide
    rw [hg, Finset.card_image_of_injective]
    · simp
    · intro a1 a2 h
      funext i
      have := congrFun h i.castSucc
      simpa [g, Fin.val_castSucc, i.isLt] using this
  rw [hpart, Finset.card_insert_of_notMem hu1_not, hS0, add_comm]

private lemma classify_high {n s : ℕ} (hs : 3 ≤ s)
    (C : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (hhigh : 2 ^ n * (2 ^ (s - 1) + 1) ≤
      2 ^ s * (Finset.univ.filter (fun w => satF C w = true)).card) :
    (∀ w, satF C w = true) ∨
    (∃ (a b c d : Fin n) (sa sb sc sd : Bool),
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ∀ w, satF C w = decide ((w a ≠ sa ∨ w b ≠ sb) ∧ (w c ≠ sc ∨ w d ≠ sd))) ∨
    (∃ (v : Fin n) (U : Finset (Fin n)) (σ : Fin n → Bool),
      v ∉ U ∧ 1 ≤ U.card ∧ U.card ≤ s - 1 ∧
      ∀ w, satF C w = decide (∀ u ∈ U, w v ≠ σ v ∨ w u ≠ σ u)) := by
  classical
  have hgt : 2 ^ n < 2 * (Finset.univ.filter (fun w => satF C w = true)).card :=
    half_lt_of_high hs C hhigh
  let C' := C.filter (fun c => c.1.1 ≠ c.2.1 ∨ c.1.2 = c.2.2)
  have hsatC' : ∀ w, satF C w = satF C' w := by
    intro w
    simp only [satF, C']
    congr 1
    apply propext
    constructor
    · intro h c hc
      exact h c (Finset.mem_filter.mp hc).1
    · intro h c hc
      by_cases hnt : c.1.1 ≠ c.2.1 ∨ c.1.2 = c.2.2
      · exact h c (Finset.mem_filter.mpr ⟨hc, hnt⟩)
      · push Not at hnt
        rcases hnt with ⟨heq, hne⟩
        rw [heq]
        cases hw : w c.2.1 <;> cases h1 : c.1.2 <;> cases h2 : c.2.2 <;> simp_all
  have hno_unit : ∀ c ∈ C', c.1.1 ≠ c.2.1 := by
    intro c hc heq
    have hsame : c.1.2 = c.2.2 := by
      rcases (Finset.mem_filter.mp hc).2 with h | h
      · exact (h heq).elim
      · exact h
    let f : Fin 1 ↪ Fin n := ⟨fun _ => c.1.1, fun i j _ => Subsingleton.elim i j⟩
    let P : (Fin 1 → Bool) → Bool := fun u => decide (u 0 ≠ c.1.2)
    have hP : (Finset.univ.filter (fun u : Fin 1 → Bool => P u = true)).card * 2 ≤ 2 ^ 1 := by
      have hdec : ∀ b : Bool, (Finset.univ.filter (fun u : Fin 1 → Bool => decide (u 0 ≠ b) = true)).card * 2 ≤ 2 ^ 1 := by
        decide
      exact hdec c.1.2
    have hle := card_filter_le_of_proj f P (satF C) (fun w hw => by
      rw [hsatC'] at hw
      have hcl := (decide_eq_true_eq.mp hw) c hc
      simp only [P, f, decide_eq_true_eq]
      rw [← heq, ← hsame] at hcl
      rcases hcl with h | h <;> exact h) hP
    omega
  have hunate : ∀ (v : Fin n), ∀ c1 ∈ C', ∀ c2 ∈ C',
      (c1.1 = (v, true) ∨ c1.2 = (v, true)) →
      (c2.1 = (v, false) ∨ c2.2 = (v, false)) → False := by
    intro v c1 hc1 c2 hc2 h1 h2
    have hget1 : ∃ u1 b1, u1 ≠ v ∧ ∀ w, satF C w = true → w v = true → w u1 ≠ b1 := by
      have hne1 := hno_unit c1 hc1
      rcases h1 with h1 | h1
      · refine ⟨c1.2.1, c1.2.2, Ne.symm (by simpa [h1] using hne1), ?_⟩
        intro w hw hwv
        rw [hsatC'] at hw
        rcases (decide_eq_true_eq.mp hw) c1 hc1 with ha | hb
        · exfalso; apply ha; rw [h1]; exact hwv
        · exact hb
      · refine ⟨c1.1.1, c1.1.2, by simpa [h1] using hne1, ?_⟩
        intro w hw hwv
        rw [hsatC'] at hw
        rcases (decide_eq_true_eq.mp hw) c1 hc1 with ha | hb
        · exact ha
        · exfalso; apply hb; rw [h1]; exact hwv
    have hget2 : ∃ u2 b2, u2 ≠ v ∧ ∀ w, satF C w = true → w v = false → w u2 ≠ b2 := by
      have hne2 := hno_unit c2 hc2
      rcases h2 with h2 | h2
      · refine ⟨c2.2.1, c2.2.2, Ne.symm (by simpa [h2] using hne2), ?_⟩
        intro w hw hwv
        rw [hsatC'] at hw
        rcases (decide_eq_true_eq.mp hw) c2 hc2 with ha | hb
        · exfalso; apply ha; rw [h2]; exact hwv
        · exact hb
      · refine ⟨c2.1.1, c2.1.2, by simpa [h2] using hne2, ?_⟩
        intro w hw hwv
        rw [hsatC'] at hw
        rcases (decide_eq_true_eq.mp hw) c2 hc2 with ha | hb
        · exact ha
        · exfalso; apply hb; rw [h2]; exact hwv
    rcases hget1 with ⟨u1, b1, hu1, hsat1⟩
    rcases hget2 with ⟨u2, b2, hu2, hsat2⟩
    by_cases hu : u1 = u2
    · subst hu
      let f : Fin 2 ↪ Fin n :=
        ⟨fun i => match i with | ⟨0, _⟩ => v | ⟨1, _⟩ => u1, by
          intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all⟩
      let P : (Fin 2 → Bool) → Bool := fun u =>
        decide ((u 0 = true → u 1 ≠ b1) ∧ (u 0 = false → u 1 ≠ b2))
      have hP : (Finset.univ.filter (fun u : Fin 2 → Bool => P u = true)).card * 2 ≤ 2 ^ 2 := by
        have hdec : ∀ d1 d2 : Bool,
            (Finset.univ.filter (fun u : Fin 2 → Bool =>
              decide ((u 0 = true → u 1 ≠ d1) ∧ (u 0 = false → u 1 ≠ d2)) = true)).card * 2 ≤ 2 ^ 2 := by
          decide
        exact hdec b1 b2
      have hle := card_filter_le_of_proj f P (satF C) (fun w hw => by
        simp only [P, f, decide_eq_true_eq]
        exact ⟨hsat1 w hw, hsat2 w hw⟩) hP
      omega
    · let f : Fin 3 ↪ Fin n :=
        ⟨fun i => match i with | ⟨0, _⟩ => v | ⟨1, _⟩ => u1 | ⟨2, _⟩ => u2, by
          intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all⟩
      let P : (Fin 3 → Bool) → Bool := fun u =>
        decide ((u 0 = true → u 1 ≠ b1) ∧ (u 0 = false → u 2 ≠ b2))
      have hP : (Finset.univ.filter (fun u : Fin 3 → Bool => P u = true)).card * 2 ≤ 2 ^ 3 := by
        have hdec : ∀ d1 d2 : Bool,
            (Finset.univ.filter (fun u : Fin 3 → Bool =>
              decide ((u 0 = true → u 1 ≠ d1) ∧ (u 0 = false → u 2 ≠ d2)) = true)).card * 2 ≤ 2 ^ 3 := by
          decide
        exact hdec b1 b2
      have hle := card_filter_le_of_proj f P (satF C) (fun w hw => by
        simp only [P, f, decide_eq_true_eq]
        exact ⟨hsat1 w hw, hsat2 w hw⟩) hP
      omega
  let σ : Fin n → Bool := fun v =>
    decide (∃ c ∈ C', c.1 = (v, true) ∨ c.2 = (v, true))
  have hsign1 : ∀ c ∈ C', c.1.2 = σ c.1.1 := by
    intro c hc
    cases hb : c.1.2
    · symm
      simp only [σ, decide_eq_false_iff_not]
      intro ⟨c1, hc1, h1⟩
      exact hunate c.1.1 c1 hc1 c hc h1 (Or.inl (Prod.ext rfl hb))
    · symm
      simp only [σ, decide_eq_true_eq]
      exact ⟨c, hc, Or.inl (Prod.ext rfl hb)⟩
  have hsign2 : ∀ c ∈ C', c.2.2 = σ c.2.1 := by
    intro c hc
    cases hb : c.2.2
    · symm
      simp only [σ, decide_eq_false_iff_not]
      intro ⟨c1, hc1, h1⟩
      exact hunate c.2.1 c1 hc1 c hc h1 (Or.inr (Prod.ext rfl hb))
    · symm
      simp only [σ, decide_eq_true_eq]
      exact ⟨c, hc, Or.inr (Prod.ext rfl hb)⟩
  let Adj : Fin n → Fin n → Prop := fun i j =>
    ∃ c ∈ C', (c.1.1 = i ∧ c.2.1 = j) ∨ (c.1.1 = j ∧ c.2.1 = i)
  have hAdj_symm : ∀ i j, Adj i j → Adj j i := by
    intro i j ⟨c, hc, h⟩
    exact ⟨c, hc, h.symm⟩
  have hAdj_irrefl : ∀ i, ¬ Adj i i := by
    intro i ⟨c, hc, h⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hno_unit c hc (h1.trans h2.symm)
  have hsat_adj : ∀ w, satF C w = decide (∀ i j, Adj i j → w i ≠ σ i ∨ w j ≠ σ j) := by
    intro w
    rw [hsatC']
    simp only [satF]
    congr 1
    apply propext
    constructor
    · intro h i j ⟨c, hc, hij⟩
      have hcl := h c hc
      rw [hsign1 c hc, hsign2 c hc] at hcl
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcl
      · exact hcl.symm
    · intro h c hc
      rw [hsign1 c hc, hsign2 c hc]
      exact h c.1.1 c.2.1 ⟨c, hc, Or.inl ⟨rfl, rfl⟩⟩
  have hQ : ∀ w, satF C w = true → ∀ i j, Adj i j → w i ≠ σ i ∨ w j ≠ σ j := by
    intro w hw
    rw [hsat_adj w, decide_eq_true_eq] at hw
    exact hw
  by_cases hempty : ∀ i j, ¬ Adj i j
  · left
    intro w
    rw [hsat_adj w, decide_eq_true_eq]
    intro i j hij
    exact (hempty i j hij).elim
  · push Not at hempty
    rcases hempty with ⟨a, b, hab_adj⟩
    have hab : a ≠ b := fun h => hAdj_irrefl a (h ▸ hab_adj)
    by_cases hall_a : ∀ i j, Adj i j → i = a ∨ j = a
    · right; right
      let U : Finset (Fin n) := Finset.univ.filter (fun u => Adj a u)
      have haU : a ∉ U := by
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hAdj_irrefl a
      have hU_pos : 1 ≤ U.card :=
        Finset.card_pos.mpr ⟨b, by simp [U, hab_adj]⟩
      have hsat_star : ∀ w, satF C w = decide (∀ u ∈ U, w a ≠ σ a ∨ w u ≠ σ u) := by
        intro w
        rw [hsat_adj w]
        congr 1
        apply propext
        constructor
        · intro h u hu
          exact h a u (Finset.mem_filter.mp hu).2
        · intro h i j hij
          rcases hall_a i j hij with rfl | rfl
          · exact h j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
          · exact (h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj_symm _ _ hij⟩)).symm
      have hU_le : U.card ≤ s - 1 := by
        have hsc := star_card_eq a U haU σ
        have hfeq : Finset.univ.filter (fun w => satF C w = true) =
            Finset.univ.filter (fun w => decide (∀ u ∈ U, w a ≠ σ a ∨ w u ≠ σ u) = true) := by
          ext w; simp [hsat_star w]
        rw [← hfeq] at hsc
        by_contra hgtU
        have hge : s ≤ U.card := by omega
        have hpow_le : 2 ^ s * (2 ^ U.card + 1) < (2 ^ (s - 1) + 1) * 2 ^ (U.card + 1) := by
          have hs1 : 2 ^ s = 2 * 2 ^ (s - 1) := by
            have : s = (s - 1) + 1 := by omega
            conv_lhs => rw [this, pow_succ']
          have hpowU : 2 ^ s < 2 ^ (U.card + 1) :=
            Nat.pow_lt_pow_right (by omega) (by omega)
          have hpowU2 : 2 ^ (U.card + 1) = 2 * 2 ^ U.card := by rw [pow_succ']
          rw [hs1, hpowU2] at hpowU ⊢
          nlinarith
        have hmul1 : 2 ^ n * ((2 ^ (s - 1) + 1) * 2 ^ (U.card + 1)) ≤
            2 ^ s * ((2 ^ U.card + 1) * 2 ^ n) := by
          calc 2 ^ n * ((2 ^ (s - 1) + 1) * 2 ^ (U.card + 1))
              = (2 ^ n * (2 ^ (s - 1) + 1)) * 2 ^ (U.card + 1) := by ring
            _ ≤ (2 ^ s * (Finset.univ.filter (fun w => satF C w = true)).card) * 2 ^ (U.card + 1) :=
                Nat.mul_le_mul_right _ hhigh
            _ = 2 ^ s * ((Finset.univ.filter (fun w => satF C w = true)).card * 2 ^ (U.card + 1)) := by ring
            _ = 2 ^ s * ((2 ^ U.card + 1) * 2 ^ n) := by rw [hsc]
        have hposn : 0 < 2 ^ n := Nat.two_pow_pos n
        nlinarith
      exact ⟨a, U, σ, haU, hU_pos, hU_le, hsat_star⟩
    · by_cases hall_b : ∀ i j, Adj i j → i = b ∨ j = b
      · right; right
        let U : Finset (Fin n) := Finset.univ.filter (fun u => Adj b u)
        have hbU : b ∉ U := by
          simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hAdj_irrefl b
        have hU_pos : 1 ≤ U.card :=
          Finset.card_pos.mpr ⟨a, by simp [U, hAdj_symm _ _ hab_adj]⟩
        have hsat_star : ∀ w, satF C w = decide (∀ u ∈ U, w b ≠ σ b ∨ w u ≠ σ u) := by
          intro w
          rw [hsat_adj w]
          congr 1
          apply propext
          constructor
          · intro h u hu
            exact h b u (Finset.mem_filter.mp hu).2
          · intro h i j hij
            rcases hall_b i j hij with rfl | rfl
            · exact h j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
            · exact (h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj_symm _ _ hij⟩)).symm
        have hU_le : U.card ≤ s - 1 := by
          have hsc := star_card_eq b U hbU σ
          have hfeq : Finset.univ.filter (fun w => satF C w = true) =
              Finset.univ.filter (fun w => decide (∀ u ∈ U, w b ≠ σ b ∨ w u ≠ σ u) = true) := by
            ext w; simp [hsat_star w]
          rw [← hfeq] at hsc
          by_contra hgtU
          have hge : s ≤ U.card := by omega
          have hpow_le : 2 ^ s * (2 ^ U.card + 1) < (2 ^ (s - 1) + 1) * 2 ^ (U.card + 1) := by
            have hs1 : 2 ^ s = 2 * 2 ^ (s - 1) := by
              have : s = (s - 1) + 1 := by omega
              conv_lhs => rw [this, pow_succ']
            have hpowU : 2 ^ s < 2 ^ (U.card + 1) :=
              Nat.pow_lt_pow_right (by omega) (by omega)
            have hpowU2 : 2 ^ (U.card + 1) = 2 * 2 ^ U.card := by rw [pow_succ']
            rw [hs1, hpowU2] at hpowU ⊢
            nlinarith
          have hmul1 : 2 ^ n * ((2 ^ (s - 1) + 1) * 2 ^ (U.card + 1)) ≤
              2 ^ s * ((2 ^ U.card + 1) * 2 ^ n) := by
            calc 2 ^ n * ((2 ^ (s - 1) + 1) * 2 ^ (U.card + 1))
                = (2 ^ n * (2 ^ (s - 1) + 1)) * 2 ^ (U.card + 1) := by ring
              _ ≤ (2 ^ s * (Finset.univ.filter (fun w => satF C w = true)).card) * 2 ^ (U.card + 1) :=
                  Nat.mul_le_mul_right _ hhigh
              _ = 2 ^ s * ((Finset.univ.filter (fun w => satF C w = true)).card * 2 ^ (U.card + 1)) := by ring
              _ = 2 ^ s * ((2 ^ U.card + 1) * 2 ^ n) := by rw [hsc]
          have hposn : 0 < 2 ^ n := Nat.two_pow_pos n
          nlinarith
        exact ⟨b, U, σ, hbU, hU_pos, hU_le, hsat_star⟩
      ·
        push Not at hall_a hall_b
        rcases hall_a with ⟨c1, d1, hcd1, hc1a, hd1a⟩
        rcases hall_b with ⟨c2, d2, hcd2, hc2b, hd2b⟩
        have hc1d1 : c1 ≠ d1 := fun h => hAdj_irrefl c1 (h ▸ hcd1)
        have hc2d2 : c2 ≠ d2 := fun h => hAdj_irrefl c2 (h ▸ hcd2)
        have hex_disj : ∃ c d, a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ Adj c d := by
          by_cases hc1b : c1 = b
          · subst hc1b
            by_cases hc2a : c2 = a
            · subst hc2a
              by_cases hd12 : d1 = d2
              · subst hd12
                exact (card_gt_half_k3 Adj σ (satF C) hQ hgt hab (Ne.symm hd1a) hc1d1
                  hab_adj hcd1 hcd2).elim
              · exact (card_gt_half_p4 Adj σ (satF C) hQ hgt
                  hc1d1.symm hd1a hd12 hab.symm hd2b.symm hc2d2
                  (hAdj_symm _ _ hcd1) (hAdj_symm _ _ hab_adj) hcd2).elim
            · by_cases hd2a : d2 = a
              · subst hd2a
                by_cases hd1c2 : d1 = c2
                · subst hd1c2
                  exact (card_gt_half_k3 Adj σ (satF C) hQ hgt hab (Ne.symm hd1a) hc1d1
                    hab_adj hcd1 (hAdj_symm _ _ hcd2)).elim
                · exact (card_gt_half_p4 Adj σ (satF C) hQ hgt
                    hc1d1.symm hd1a hd1c2 hab.symm hc2b.symm hc2d2.symm
                    (hAdj_symm _ _ hcd1) (hAdj_symm _ _ hab_adj) (hAdj_symm _ _ hcd2)).elim
              · exact ⟨c2, d2, Ne.symm hc2a, Ne.symm hd2a, Ne.symm hc2b, Ne.symm hd2b, hc2d2, hcd2⟩
          · by_cases hd1b : d1 = b
            · subst hd1b
              by_cases hc2a : c2 = a
              · subst hc2a
                by_cases hc1d2 : c1 = d2
                · subst hc1d2
                  exact (card_gt_half_k3 Adj σ (satF C) hQ hgt hab (Ne.symm hc1a) hc1d1.symm
                    hab_adj (hAdj_symm _ _ hcd1) hcd2).elim
                · exact (card_gt_half_p4 Adj σ (satF C) hQ hgt
                    hc1d1 hc1a hc1d2 hab.symm hd2b.symm hc2d2
                    hcd1 (hAdj_symm _ _ hab_adj) hcd2).elim
              · by_cases hd2a : d2 = a
                · subst hd2a
                  by_cases hc12 : c1 = c2
                  · subst hc12
                    exact (card_gt_half_k3 Adj σ (satF C) hQ hgt hab (Ne.symm hc1a) hc1d1.symm
                      hab_adj (hAdj_symm _ _ hcd1) (hAdj_symm _ _ hcd2)).elim
                  · exact (card_gt_half_p4 Adj σ (satF C) hQ hgt
                      hc1d1 hc1a hc12 hab.symm hc2b.symm hc2d2.symm
                      hcd1 (hAdj_symm _ _ hab_adj) (hAdj_symm _ _ hcd2)).elim
                · exact ⟨c2, d2, Ne.symm hc2a, Ne.symm hd2a, Ne.symm hc2b, Ne.symm hd2b, hc2d2, hcd2⟩
            · exact ⟨c1, d1, Ne.symm hc1a, Ne.symm hd1a, Ne.symm hc1b, Ne.symm hd1b, hc1d1, hcd1⟩
        rcases hex_disj with ⟨c, d, hac, had, hbc, hbd, hcd, hcd_adj⟩
        have hno_other : ∀ i j, Adj i j →
            (i = a ∧ j = b) ∨ (i = b ∧ j = a) ∨ (i = c ∧ j = d) ∨ (i = d ∧ j = c) := by
          intro i j hij
          have hne : i ≠ j := fun h => hAdj_irrefl i (h ▸ hij)
          by_cases hia : i = a
          · subst hia
            by_cases hjb : j = b
            · left; exact ⟨rfl, hjb⟩
            · by_cases hjc : j = c
              · subst hjc
                exact (card_gt_half_p4 Adj σ (satF C) hQ hgt hab.symm hbc hbd hac had hcd
                  (hAdj_symm _ _ hab_adj) hij hcd_adj).elim
              · by_cases hjd : j = d
                · subst hjd
                  exact (card_gt_half_p4 Adj σ (satF C) hQ hgt hab.symm hbd hbc had hac hcd.symm
                    (hAdj_symm _ _ hab_adj) hij (hAdj_symm _ _ hcd_adj)).elim
                · exact (card_gt_half_k12_k2 Adj σ (satF C) hQ hgt hab hne hac had
                    (Ne.symm hjb) hbc hbd hjc hjd hcd hab_adj hij hcd_adj).elim
          · by_cases hib : i = b
            · subst hib
              by_cases hja : j = a
              · right; left; exact ⟨rfl, hja⟩
              · by_cases hjc : j = c
                · subst hjc
                  exact (card_gt_half_p4 Adj σ (satF C) hQ hgt hab hac had hbc hbd hcd
                    hab_adj hij hcd_adj).elim
                · by_cases hjd : j = d
                  · subst hjd
                    exact (card_gt_half_p4 Adj σ (satF C) hQ hgt hab had hac hbd hbc hcd.symm
                      hab_adj hij (hAdj_symm _ _ hcd_adj)).elim
                  · exact (card_gt_half_k12_k2 Adj σ (satF C) hQ hgt hab.symm hne hbc hbd
                      (Ne.symm hja) hac had hjc hjd hcd (hAdj_symm _ _ hab_adj) hij hcd_adj).elim
            · by_cases hic : i = c
              · subst hic
                by_cases hjd : j = d
                · right; right; left; exact ⟨rfl, hjd⟩
                · by_cases hja : j = a
                  · subst hja
                    exact (card_gt_half_p4 Adj σ (satF C) hQ hgt hcd.symm had.symm hbd.symm hac.symm hbc.symm hab
                      (hAdj_symm _ _ hcd_adj) hij hab_adj).elim
                  · by_cases hjb : j = b
                    · subst hjb
                      exact (card_gt_half_p4 Adj σ (satF C) hQ hgt hcd.symm hbd.symm had.symm hbc.symm hac.symm hab.symm
                        (hAdj_symm _ _ hcd_adj) hij (hAdj_symm _ _ hab_adj)).elim
                    · exact (card_gt_half_k12_k2 Adj σ (satF C) hQ hgt hcd hne hac.symm hbc.symm
                        (Ne.symm hjd) had.symm hbd.symm hja hjb hab hcd_adj hij hab_adj).elim
              · by_cases hid : i = d
                · subst hid
                  by_cases hjc : j = c
                  · right; right; right; exact ⟨rfl, hjc⟩
                  · by_cases hja : j = a
                    · subst hja
                      exact (card_gt_half_p4 Adj σ (satF C) hQ hgt hcd hac.symm hbc.symm had.symm hbd.symm hab
                        hcd_adj hij hab_adj).elim
                    · by_cases hjb : j = b
                      · subst hjb
                        exact (card_gt_half_p4 Adj σ (satF C) hQ hgt hcd hbc.symm hac.symm hbd.symm had.symm hab.symm
                          hcd_adj hij (hAdj_symm _ _ hab_adj)).elim
                      · exact (card_gt_half_k12_k2 Adj σ (satF C) hQ hgt hcd.symm hne had.symm hbd.symm
                          (Ne.symm hjc) hac.symm hbc.symm hja hjb hab (hAdj_symm _ _ hcd_adj) hij hab_adj).elim
                · by_cases hja : j = a
                  · subst hja
                    exact (card_gt_half_k12_k2 Adj σ (satF C) hQ hgt hab (Ne.symm hia) hac had
                      (Ne.symm hib) hbc hbd hic hid hcd hab_adj (hAdj_symm _ _ hij) hcd_adj).elim
                  · by_cases hjb : j = b
                    · subst hjb
                      exact (card_gt_half_k12_k2 Adj σ (satF C) hQ hgt hab.symm (Ne.symm hib) hbc hbd
                        (Ne.symm hia) hac had hic hid hcd (hAdj_symm _ _ hab_adj) (hAdj_symm _ _ hij) hcd_adj).elim
                    · by_cases hjc : j = c
                      · subst hjc
                        exact (card_gt_half_k12_k2 Adj σ (satF C) hQ hgt hcd (Ne.symm hic) hac.symm hbc.symm
                          (Ne.symm hid) had.symm hbd.symm hia hib hab hcd_adj (hAdj_symm _ _ hij) hab_adj).elim
                      · by_cases hjd : j = d
                        · subst hjd
                          exact (card_gt_half_k12_k2 Adj σ (satF C) hQ hgt hcd.symm (Ne.symm hid) had.symm hbd.symm
                            (Ne.symm hic) hac.symm hbc.symm hia hib hab (hAdj_symm _ _ hcd_adj) (hAdj_symm _ _ hij) hab_adj).elim
                        · exact (card_gt_half_3k2 Adj σ (satF C) hQ hgt
                            hab hac had (Ne.symm hia) (Ne.symm hja)
                            hbc hbd (Ne.symm hib) (Ne.symm hjb)
                            hcd (Ne.symm hic) (Ne.symm hjc)
                            (Ne.symm hid) (Ne.symm hjd) hne
                            hab_adj hcd_adj hij).elim
        right; left
        refine ⟨a, b, c, d, σ a, σ b, σ c, σ d, hab, hac, had, hbc, hbd, hcd, ?_⟩
        intro w
        rw [hsat_adj w]
        congr 1
        apply propext
        constructor
        · intro h
          exact ⟨h a b hab_adj, h c d hcd_adj⟩
        · intro ⟨h1, h2⟩ i j hij
          rcases hno_other i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h1
          · exact h1.symm
          · exact h2
          · exact h2.symm

private def Surj4 {n a : ℕ} (cal : Fin a → Fin n → Bool) : Prop :=
  ∀ (S : Finset (Fin n)), S.card ≤ 4 → ∀ (g : Fin n → Bool),
    ∃ slot : Fin a, ∀ i ∈ S, cal slot i = g i

private lemma two_mul_fifteen_pow : 2 * 15 ^ 16 ≤ 16 ^ 16 := by decide

private lemma exists_surj4 {n : ℕ} :
    let L := Nat.clog 2 (n + 1)
    let a := 16 * (1 + 4 * (1 + L))
    ∃ cal : Fin a → Fin n → Bool, Surj4 cal := by
  classical
  intro L a
  let Pat := Fin 4 → Option (Fin n × Bool)
  let matchesPat : Pat → (Fin n → Bool) → Bool := fun pat w =>
    decide (∀ r : Fin 4, ∀ x b, pat r = some (x, b) → w x = b)
  let validPat : Pat → Prop := fun pat =>
    ∃ w : Fin n → Bool, matchesPat pat w = true
  let BadCal : Pat → Finset (Fin a → Fin n → Bool) := fun pat =>
    if validPat pat then
      Finset.univ.filter (fun cal => ∀ slot : Fin a, matchesPat pat (cal slot) = false)
    else ∅
  have hsingle : ∀ pat : Pat,
      16 ^ a * (BadCal pat).card ≤ 15 ^ a * (2 ^ n) ^ a := by
    intro pat
    by_cases hval : validPat pat
    · simp only [BadCal, ite_eq_left hval]
      rcases hval with ⟨w0, hw0⟩
      let S : Finset (Fin n) := Finset.univ.filter (fun x => ∃ r : Fin 4, ∃ b, pat r = some (x, b))
      have hS_le : S.card ≤ 4 := by
        let gPat : Fin 4 → Finset (Fin n) := fun r =>
          match pat r with | some (x, _) => {x} | none => ∅
        have hsub : S ⊆ (Finset.univ : Finset (Fin 4)).biUnion gPat := by
          intro x hx
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          rcases hx with ⟨r, b, hr⟩
          rw [Finset.mem_biUnion]
          refine ⟨r, Finset.mem_univ _, ?_⟩
          simp [gPat, hr]
        calc S.card
            ≤ ((Finset.univ : Finset (Fin 4)).biUnion gPat).card := Finset.card_le_card hsub
          _ ≤ ∑ r : Fin 4, (gPat r).card := Finset.card_biUnion_le
          _ ≤ ∑ _r : Fin 4, 1 := Finset.sum_le_sum (fun r _ => by dsimp only [gPat]; cases pat r <;> simp)
          _ = 4 := by simp
      let eS : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp)).symm
      let f : Fin S.card ↪ Fin n := ⟨fun i => (eS i).1, fun i j h => eS.injective (Subtype.ext h)⟩
      let P : (Fin S.card → Bool) → Bool := fun u => decide (∀ i : Fin S.card, u i = w0 (f i))
      have hmatch_eq : ∀ w : Fin n → Bool,
          matchesPat pat w = true ↔ P (fun i => w (f i)) = true := by
        intro w
        simp only [matchesPat, P, decide_eq_true_eq]
        constructor
        · intro hw i
          have hmem : f i ∈ S := (eS i).2
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          rcases hmem with ⟨r, b, hr⟩
          rw [hw r (f i) b hr, (decide_eq_true_eq.mp hw0) r (f i) b hr]
        · intro hw r x b hr
          have hxS : x ∈ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨r, b, hr⟩
          let i := eS.symm ⟨x, hxS⟩
          have hi := hw i
          have hfi : f i = x := by
            change (eS (eS.symm ⟨x, hxS⟩)).1 = x
            rw [Equiv.apply_symm_apply]
          rw [hfi] at hi
          rw [hi, (decide_eq_true_eq.mp hw0) r x b hr]
      have hgood_card :
          (Finset.univ.filter (fun w : Fin n → Bool => matchesPat pat w = true)).card * 2 ^ S.card =
          2 ^ n := by
        have hfeq : Finset.univ.filter (fun w => matchesPat pat w = true) =
            Finset.univ.filter (fun w => P (fun i => w (f i)) = true) := by
          ext w; simp [hmatch_eq w]
        rw [hfeq, card_proj_eq f P]
        have hP1 : (Finset.univ.filter (fun u : Fin S.card → Bool => P u = true)) =
            {fun i => w0 (f i)} := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, P,
            decide_eq_true_eq, funext_iff]
        rw [hP1, Finset.card_singleton, one_mul]
      let Miss : Finset (Fin n → Bool) :=
        Finset.univ.filter (fun w => matchesPat pat w = false)
      have hMiss_add : Miss.card +
          (Finset.univ.filter (fun w => matchesPat pat w = true)).card = 2 ^ n := by
        have hun : Miss ∪ Finset.univ.filter (fun w => matchesPat pat w = true) = Finset.univ := by
          ext w
          simp only [Miss, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          cases matchesPat pat w <;> simp
        have hdisj : Disjoint Miss (Finset.univ.filter (fun w => matchesPat pat w = true)) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          simp only [Miss, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
          rw [hw1] at hw2
          exact Bool.false_ne_true hw2
        rw [← Finset.card_union_of_disjoint hdisj, hun]
        simp
      have hMiss_le : 16 * Miss.card ≤ 15 * 2 ^ n := by
        have hpow : 2 ^ S.card ≤ 16 := by
          calc 2 ^ S.card ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) hS_le
            _ = 16 := by decide
        have h1 : 2 ^ n ≤ 16 * (Finset.univ.filter (fun w => matchesPat pat w = true)).card := by
          calc 2 ^ n = (Finset.univ.filter (fun w => matchesPat pat w = true)).card * 2 ^ S.card :=
                hgood_card.symm
            _ ≤ (Finset.univ.filter (fun w => matchesPat pat w = true)).card * 16 :=
                Nat.mul_le_mul_left _ hpow
            _ = 16 * (Finset.univ.filter (fun w => matchesPat pat w = true)).card := mul_comm _ _
        omega
      have hBad_card : (Finset.univ.filter (fun cal : Fin a → Fin n → Bool =>
          ∀ slot : Fin a, matchesPat pat (cal slot) = false)).card = Miss.card ^ a := by
        have hbij : (Finset.univ.filter (fun cal : Fin a → Fin n → Bool =>
            ∀ slot : Fin a, matchesPat pat (cal slot) = false)).card =
            (Fintype.piFinset (fun _ : Fin a => Miss)).card := by
          congr 1
          ext cal
          simp [Miss, Fintype.mem_piFinset]
        rw [hbij, Fintype.card_piFinset]
        simp
      rw [hBad_card, ← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left hMiss_le a
    · simp [BadCal, hval]
  let AllBad : Finset (Fin a → Fin n → Bool) := Finset.univ.biUnion BadCal
  have hPat_card : Fintype.card Pat = (2 * n + 1) ^ 4 := by
    simp only [Pat, Fintype.card_fun, Fintype.card_option, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool]
    ring_nf
  have hlt_num : (2 * n + 1) ^ 4 * 15 ^ a < 16 ^ a := by
    let m := 1 + 4 * (1 + L)
    have hpow2 : 2 ^ m * 15 ^ a ≤ 16 ^ a := by
      have ha_eq : a = 16 * m := rfl
      rw [ha_eq, pow_mul, pow_mul, ← mul_pow]
      exact Nat.pow_le_pow_left two_mul_fifteen_pow m
    have hclog : n + 1 ≤ 2 ^ L := Nat.le_pow_clog (by omega) (n + 1)
    have hbase : 2 * n + 1 < 2 * 2 ^ L := by omega
    have hlt4 : (2 * n + 1) ^ 4 < 2 ^ m := by
      have hm : 2 ^ m = 2 * (2 * 2 ^ L) ^ 4 := by
        simp only [m]
        rw [pow_add, pow_one, mul_pow, ← pow_mul]
        ring
      rw [hm]
      have h1 : (2 * n + 1) ^ 4 < (2 * 2 ^ L) ^ 4 :=
        Nat.pow_lt_pow_left hbase (by omega)
      omega
    have hpos15 : 0 < 15 ^ a := Nat.pow_pos (by omega)
    calc (2 * n + 1) ^ 4 * 15 ^ a
        < 2 ^ m * 15 ^ a := Nat.mul_lt_mul_of_pos_right hlt4 hpos15
      _ ≤ 16 ^ a := hpow2
  have hAll_lt : AllBad.card < (Finset.univ : Finset (Fin a → Fin n → Bool)).card := by
    have huniv : (Finset.univ : Finset (Fin a → Fin n → Bool)).card = (2 ^ n) ^ a := by
      simp [Fintype.card_bool]
    rw [huniv]
    have hmul : 16 ^ a * AllBad.card < 16 ^ a * (2 ^ n) ^ a := by
      calc 16 ^ a * AllBad.card
          ≤ 16 ^ a * ∑ pat : Pat, (BadCal pat).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ pat : Pat, 16 ^ a * (BadCal pat).card := Finset.mul_sum _ _ _
        _ ≤ ∑ _pat : Pat, 15 ^ a * (2 ^ n) ^ a :=
            Finset.sum_le_sum (fun pat _ => hsingle pat)
        _ = (2 * n + 1) ^ 4 * (15 ^ a * (2 ^ n) ^ a) := by
            rw [Finset.sum_const, Finset.card_univ, hPat_card, smul_eq_mul]
        _ = ((2 * n + 1) ^ 4 * 15 ^ a) * (2 ^ n) ^ a := by ring
        _ < 16 ^ a * (2 ^ n) ^ a :=
            Nat.mul_lt_mul_of_pos_right hlt_num (Nat.pow_pos (Nat.two_pow_pos n))
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hne : (Finset.univ \ AllBad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin a → Fin n → Bool)) ⊆ AllBad :=
      Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  rcases hne with ⟨cal, hcal⟩
  refine ⟨cal, ?_⟩
  intro S hS g
  have hcal_not : cal ∉ AllBad := (Finset.mem_sdiff.mp hcal).2
  let eS : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp)).symm
  let pat : Pat := fun r =>
    if h : r.val < S.card then
      let x := (eS ⟨r.val, h⟩).1
      some (x, g x)
    else none
  have hval : validPat pat := by
    refine ⟨g, ?_⟩
    simp only [matchesPat, decide_eq_true_eq]
    intro r x b hr
    by_cases h : r.val < S.card
    · simp only [pat, dite_eq_left h, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      rfl
    · simp only [pat, dite_eq_right h, reduceCtorEq] at hr
  have hnot_bad : cal ∉ BadCal pat := by
    intro hmem
    exact hcal_not (Finset.mem_biUnion.mpr ⟨pat, Finset.mem_univ _, hmem⟩)
  simp only [BadCal, ite_eq_left hval, Finset.mem_filter, Finset.mem_univ, true_and] at hnot_bad
  push Not at hnot_bad
  rcases hnot_bad with ⟨slot, hslot⟩
  have hslot_t : matchesPat pat (cal slot) = true := by
    cases hm : matchesPat pat (cal slot)
    · exact (hslot hm).elim
    · rfl
  refine ⟨slot, ?_⟩
  intro i hi
  let k := eS.symm ⟨i, hi⟩
  have hk4 : k.val < 4 := lt_of_lt_of_le k.isLt hS
  have hpat_k : pat ⟨k.val, hk4⟩ = some (i, g i) := by
    simp only [pat, dite_eq_left k.isLt]
    have hk_eq : (⟨k.val, k.isLt⟩ : Fin S.card) = k := Fin.eta k k.isLt
    rw [hk_eq]
    simp [k]
  exact (decide_eq_true_eq.mp hslot_t) ⟨k.val, hk4⟩ i (g i) hpat_k

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private def b2zVec {d : ℕ} (v : Fin d → Bool) : Fin d → ZMod 2 := fun l => b2z (v l)

private def linEval {n d : ℕ} (A : Fin n → Fin d → Bool) (input : Fin d → Bool) : Fin n → Bool :=
  fun bit => (∑ l : Fin d, ((A bit l) && input l).toNat) % 2 == 1

private lemma zmod2_of_mod2 (N : ℕ) : b2z (N % 2 == 1) = (N : ZMod 2) := by
  have hmod : (N : ZMod 2) = ((N % 2 : ℕ) : ZMod 2) := by
    have h := (Nat.div_add_mod N 2).symm
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := rfl
    conv_lhs => rw [h, Nat.cast_add, Nat.cast_mul, h2, zero_mul, zero_add]
  rw [hmod]
  have hlt : N % 2 < 2 := Nat.mod_lt N (by omega)
  have hcases : N % 2 = 0 ∨ N % 2 = 1 := by omega
  rcases hcases with h0 | h1
  · simp [b2z, h0]
  · simp [b2z, h1]

private lemma b2z_decide_eq_one (z : ZMod 2) : b2z (decide (z = 1)) = z := by
  fin_cases z <;> rfl

private lemma zmod2_eq_of_add_eq_zero (x y : ZMod 2) (h : x + y = 0) : y = x := by
  have hall : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  exact hall x y h

private lemma zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hall : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact hall z

private lemma linEval_eq_dot {n d : ℕ} (A : Fin n → Fin d → Bool) (input : Fin d → Bool)
    (bit : Fin n) :
    b2z (linEval A input bit) = ∑ l : Fin d, b2z (A bit l) * b2z (input l) := by
  have hsum : ((∑ l : Fin d, ((A bit l) && input l).toNat : ℕ) : ZMod 2) =
      ∑ l : Fin d, b2z (A bit l) * b2z (input l) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    cases A bit l <;> cases input l <;> decide
  rw [← hsum]
  exact zmod2_of_mod2 _

private lemma linIndep_surj {n d : ℕ} (A : Fin n → Fin d → Bool) (S : Finset (Fin n))
    (hli : LinearIndependent (ZMod 2) (fun x : S => b2zVec (A x.1)))
    (g : Fin n → Bool) :
    ∃ input : Fin d → Bool, ∀ x ∈ S, linEval A input x = g x := by
  classical
  let v : S → (Fin d → ZMod 2) := fun x => b2zVec (A x.1)
  let Wsub : Submodule (ZMod 2) (Fin d → ZMod 2) := Submodule.span (ZMod 2) (Set.range v)
  let b : Module.Basis S (ZMod 2) Wsub := Module.Basis.span hli
  let fsub : Wsub →ₗ[ZMod 2] ZMod 2 := b.constr (ZMod 2) (fun x => b2z (g x.1))
  rcases Submodule.exists_isCompl Wsub with ⟨Wcomp, hcompl⟩
  let ψ : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    fsub.comp (Submodule.projectionOnto Wsub Wcomp hcompl)
  let u : Fin d → ZMod 2 := fun l => ψ (Pi.single l 1)
  let input : Fin d → Bool := fun l => decide (u l = 1)
  have hu : ∀ l : Fin d, b2z (input l) = u l := fun l => b2z_decide_eq_one (u l)
  refine ⟨input, ?_⟩
  intro x hx
  have hdot : ∑ l : Fin d, b2z (A x l) * b2z (input l) = b2z (g x) := by
    have hvec : v ⟨x, hx⟩ = ∑ l : Fin d, v ⟨x, hx⟩ l • Pi.single l (1 : ZMod 2) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    calc ∑ l : Fin d, b2z (A x l) * b2z (input l)
        = ∑ l : Fin d, v ⟨x, hx⟩ l * ψ (Pi.single l 1) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hu l]; rfl
      _ = ψ (∑ l : Fin d, v ⟨x, hx⟩ l • Pi.single l (1 : ZMod 2)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [LinearMap.map_smul, smul_eq_mul]
      _ = ψ (v ⟨x, hx⟩) := by rw [← hvec]
      _ = fsub ⟨v ⟨x, hx⟩, Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩⟩ := by
          simp only [ψ, LinearMap.comp_apply]
          congr 1
          exact Submodule.projectionOnto_apply_left hcompl ⟨v ⟨x, hx⟩, Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩⟩
      _ = fsub (b ⟨x, hx⟩) := by
          congr 1
          exact (Module.Basis.span_apply hli ⟨x, hx⟩).symm
      _ = b2z (g x) := by
          simp only [fsub, Module.Basis.constr_basis]
  have hb : b2z (linEval A input x) = b2z (g x) := by
    rw [linEval_eq_dot, hdot]
  cases h1 : linEval A input x <;> cases h2 : g x <;> simp_all [b2z]

open Classical in
private lemma card_dep_fin {d : ℕ} :
    ∀ m : ℕ, m ≤ d →
      (Finset.univ.filter (fun v : Fin m → Fin d → Bool =>
        ¬ LinearIndependent (ZMod 2) (fun i => b2zVec (v i)))).card * 2 ^ d ≤
      (2 ^ m - 1) * (2 ^ d) ^ m := by
  intro m
  induction m with
  | zero =>
    intro _
    have hempty : (Finset.univ.filter (fun v : Fin 0 → Fin d → Bool =>
        ¬ LinearIndependent (ZMod 2) (fun i => b2zVec (v i)))) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_not]
      exact linearIndependent_empty_type
    rw [hempty]
    simp
  | succ m ih =>
    intro hm
    let V := Fin d → Bool
    have hV : Fintype.card V = 2 ^ d := by simp [V, Fintype.card_bool]
    let e : (Fin (m + 1) → V) ≃ (Fin m → V) × V :=
      { toFun := fun v => (fun i => v i.castSucc, v (Fin.last m))
        invFun := fun p i => if h : i.val < m then p.1 ⟨i.val, h⟩ else p.2
        left_inv := fun v => by
          funext i
          by_cases h : i.val < m
          · simp only [dite_eq_left h]; rfl
          · have hi : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
            subst hi
            simp only [Fin.val_last, dite_eq_right (Nat.lt_irrefl m)]
        right_inv := fun ⟨v', u⟩ => by
          apply Prod.ext
          · funext i
            simp only [Fin.val_castSucc, dite_eq_left i.isLt]
          · simp only [Fin.val_last, dite_eq_right (Nat.lt_irrefl m)] }
    let DepM : Finset (Fin m → V) :=
      Finset.univ.filter (fun v' => ¬ LinearIndependent (ZMod 2) (fun i => b2zVec (v' i)))
    let IndM : Finset (Fin m → V) :=
      Finset.univ.filter (fun v' => LinearIndependent (ZMod 2) (fun i => b2zVec (v' i)))
    let spanSet : (Fin m → V) → Finset V := fun v' =>
      Finset.univ.filter (fun u : V =>
        b2zVec u ∈ Submodule.span (ZMod 2) (Set.range (fun i : Fin m => b2zVec (v' i))))
    have hspan_card : ∀ v' : Fin m → V, (spanSet v').card ≤ 2 ^ m := by
      intro v'
      let img : Finset (Fin d → ZMod 2) :=
        Finset.univ.image (fun c : Fin m → ZMod 2 => ∑ i : Fin m, c i • b2zVec (v' i))
      have hinj : Function.Injective (b2zVec (d := d)) := by
        intro u1 u2 h
        funext l
        have hl := congrFun h l
        cases h1 : u1 l <;> cases h2 : u2 l <;> simp_all [b2zVec, b2z]
      have hsub : (spanSet v').image b2zVec ⊆ img := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
        simp only [spanSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        rw [Finsupp.mem_span_range_iff_exists_finsupp] at hu
        rcases hu with ⟨c, hc⟩
        rw [Finset.mem_image]
        refine ⟨fun i => c i, Finset.mem_univ _, ?_⟩
        rw [← hc]
        exact (Finsupp.sum_fintype c (fun i a => a • b2zVec (v' i)) (fun _ => zero_smul _ _)).symm
      calc (spanSet v').card
          = ((spanSet v').image b2zVec).card := (Finset.card_image_of_injective _ hinj).symm
        _ ≤ img.card := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Fin m → ZMod 2)).card := Finset.card_image_le
        _ = 2 ^ m := by simp
    have hli_ext : ∀ (v' : Fin m → V) (u : V),
        LinearIndependent (ZMod 2) (fun i => b2zVec (v' i)) →
        b2zVec u ∉ Submodule.span (ZMod 2) (Set.range (fun i : Fin m => b2zVec (v' i))) →
        LinearIndependent (ZMod 2) (fun i => b2zVec (e.symm (v', u) i)) := by
      intro v' u hv' hu
      rw [Fintype.linearIndependent_iff]
      intro c hc
      rw [Fin.sum_univ_castSucc] at hc
      have hlast_eq : e.symm (v', u) (Fin.last m) = u := by
        simp [e, Fin.val_last]
      have hcast_eq : ∀ i : Fin m, e.symm (v', u) i.castSucc = v' i := by
        intro i
        simp [e, Fin.val_castSucc, i.isLt]
      simp only [hlast_eq, hcast_eq] at hc
      have hclast : c (Fin.last m) = 0 := by
        rcases zmod2_eq_zero_or_one (c (Fin.last m)) with h0 | h1
        · exact h0
        · exfalso
          apply hu
          have hadd : (∑ i : Fin m, c i.castSucc • b2zVec (v' i)) + b2zVec u = 0 := by
            rw [h1, one_smul] at hc
            exact hc
          have hu_eq : b2zVec u = ∑ i : Fin m, c i.castSucc • b2zVec (v' i) := by
            funext l
            have hl := congrFun hadd l
            simp only [Pi.add_apply, Pi.zero_apply] at hl
            exact zmod2_eq_of_add_eq_zero _ _ hl
          rw [hu_eq]
          exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      rw [hclast, zero_smul, add_zero] at hc
      have hc' : ∀ i : Fin m, c i.castSucc = 0 := (Fintype.linearIndependent_iff.mp hv') _ hc
      intro i
      refine Fin.lastCases hclast hc' i
    let DepSucc := Finset.univ.filter (fun v : Fin (m + 1) → V =>
      ¬ LinearIndependent (ZMod 2) (fun i => b2zVec (v i)))
    have hdep_le : DepSucc.card ≤ DepM.card * 2 ^ d + (2 ^ d) ^ m * 2 ^ m := by
      let B1 : Finset ((Fin m → V) × V) := DepM ×ˢ (Finset.univ : Finset V)
      let B2 : Finset ((Fin m → V) × V) := IndM.biUnion (fun v' => (spanSet v').map
        ⟨fun u => (v', u), fun u1 u2 h => (Prod.mk.inj h).2⟩)
      have hsub : DepSucc.map e.toEmbedding ⊆ B1 ∪ B2 := by
        intro p hp
        rcases Finset.mem_map.mp hp with ⟨v, hv, rfl⟩
        simp only [DepSucc, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rw [Finset.mem_union]
        by_cases hli : LinearIndependent (ZMod 2) (fun i => b2zVec ((e v).1 i))
        · right
          rw [Finset.mem_biUnion]
          refine ⟨(e v).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli⟩, ?_⟩
          rw [Finset.mem_map]
          refine ⟨(e v).2, ?_, rfl⟩
          simp only [spanSet, Finset.mem_filter, Finset.mem_univ, true_and]
          by_contra hnot
          apply hv
          have h1 := hli_ext (e v).1 (e v).2 hli hnot
          have hsymm : e.symm ((e v).1, (e v).2) = v := e.symm_apply_apply v
          rwa [hsymm] at h1
        · left
          simp only [B1, DepM, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          exact hli
      have hB1 : B1.card = DepM.card * 2 ^ d := by
        simp [B1, Finset.card_product, hV]
      have hB2 : B2.card ≤ (2 ^ d) ^ m * 2 ^ m := by
        calc B2.card
            ≤ ∑ v' ∈ IndM, ((spanSet v').map
                ⟨fun u => (v', u), fun u1 u2 h => (Prod.mk.inj h).2⟩).card :=
              Finset.card_biUnion_le
          _ = ∑ v' ∈ IndM, (spanSet v').card := by
              refine Finset.sum_congr rfl (fun v' _ => Finset.card_map _)
          _ ≤ ∑ _v' ∈ IndM, 2 ^ m := Finset.sum_le_sum (fun v' _ => hspan_card v')
          _ = IndM.card * 2 ^ m := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (Finset.univ : Finset (Fin m → V)).card * 2 ^ m :=
              Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.subset_univ _))
          _ = (2 ^ d) ^ m * 2 ^ m := by simp [hV]
      calc DepSucc.card
          = (DepSucc.map e.toEmbedding).card := (Finset.card_map _).symm
        _ ≤ (B1 ∪ B2).card := Finset.card_le_card hsub
        _ ≤ B1.card + B2.card := Finset.card_union_le _ _
        _ ≤ DepM.card * 2 ^ d + (2 ^ d) ^ m * 2 ^ m := by rw [hB1]; exact Nat.add_le_add_left hB2 _
    have hih := ih (Nat.le_of_succ_le hm)
    have hpow_m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hpow_succ : 2 ^ (m + 1) - 1 = (2 ^ m - 1) + 2 ^ m := by
      rw [pow_succ']
      omega
    calc DepSucc.card * 2 ^ d
        ≤ (DepM.card * 2 ^ d + (2 ^ d) ^ m * 2 ^ m) * 2 ^ d :=
          Nat.mul_le_mul_right _ hdep_le
      _ = (DepM.card * 2 ^ d) * 2 ^ d + 2 ^ m * ((2 ^ d) ^ m * 2 ^ d) := by ring
      _ ≤ ((2 ^ m - 1) * (2 ^ d) ^ m) * 2 ^ d + 2 ^ m * ((2 ^ d) ^ m * 2 ^ d) :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ hih) _
      _ = ((2 ^ m - 1) + 2 ^ m) * ((2 ^ d) ^ m * 2 ^ d) := by ring
      _ = (2 ^ (m + 1) - 1) * (2 ^ d) ^ (m + 1) := by rw [← hpow_succ, ← pow_succ]

open Classical in
private lemma card_dep_subset {n d : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ d) :
    (Finset.univ.filter (fun A : Fin n → Fin d → Bool =>
      ¬ LinearIndependent (ZMod 2) (fun x : S => b2zVec (A x.1)))).card * 2 ^ (d - S.card) ≤
    (2 ^ d) ^ n := by
  let V := Fin d → Bool
  have hV : Fintype.card V = 2 ^ d := by simp [V, Fintype.card_bool]
  let eS : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp)).symm
  let Sc : Finset (Fin n) := Finset.univ \ S
  have hSc : Sc.card + S.card = n := by
    have hle : S.card ≤ n := by
      calc S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    have hsd : Sc.card = n - S.card := by simp [Sc, Finset.card_sdiff]
    omega
  let e : (Fin n → V) ≃ (Fin S.card → V) × ({x : Fin n // x ∈ Sc} → V) :=
    { toFun := fun A => (fun i => A (eS i).1, fun x => A x.1)
      invFun := fun p x =>
        if hx : x ∈ S then p.1 (eS.symm ⟨x, hx⟩)
        else p.2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩
      left_inv := fun A => by
        funext x
        by_cases hx : x ∈ S
        · simp only [dite_eq_left hx, Equiv.apply_symm_apply]
        · simp only [dite_eq_right hx]
      right_inv := fun ⟨v, w⟩ => by
        apply Prod.ext
        · funext i
          simp only [dite_eq_left (eS i).2]
          congr 1
          exact eS.symm_apply_apply i
        · funext ⟨x, hxSc⟩
          have hx : x ∉ S := (Finset.mem_sdiff.mp hxSc).2
          simp only [dite_eq_right hx] }
  have hli_iff : ∀ A : Fin n → V,
      LinearIndependent (ZMod 2) (fun x : S => b2zVec (A x.1)) ↔
      LinearIndependent (ZMod 2) (fun i : Fin S.card => b2zVec (A (eS i).1)) := by
    intro A
    exact (linearIndependent_equiv eS).symm
  let DepA := Finset.univ.filter (fun A : Fin n → V =>
    ¬ LinearIndependent (ZMod 2) (fun x : S => b2zVec (A x.1)))
  let DepM := Finset.univ.filter (fun v : Fin S.card → V =>
    ¬ LinearIndependent (ZMod 2) (fun i : Fin S.card => b2zVec (v i)))
  have hcard : DepA.card = DepM.card * (2 ^ d) ^ Sc.card := by
    have hbij : DepA.card = (DepM ×ˢ (Finset.univ : Finset ({x : Fin n // x ∈ Sc} → V))).card := by
      refine Finset.card_bij (fun A _ => e A) ?_ ?_ ?_
      · intro A hA
        simp only [DepA, Finset.mem_filter, Finset.mem_univ, true_and] at hA
        simp only [DepM, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
          e, Equiv.coe_fn_mk]
        rwa [← hli_iff A]
      · intro A1 _ A2 _ h; exact e.injective h
      · intro p hp
        refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
        simp only [DepM, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp
        simp only [DepA, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hli_iff]
        have h1 : (fun i : Fin S.card => b2zVec ((e.symm p) (eS i).1)) =
            (fun i : Fin S.card => b2zVec (p.1 i)) := by
          funext i
          exact congrArg b2zVec (congrFun (congrArg Prod.fst (e.apply_symm_apply p)) i)
        rwa [h1]
    rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, hV]
  have hdep := card_dep_fin (d := d) S.card hS
  have hdep2 : DepM.card * 2 ^ (d - S.card) ≤ (2 ^ d) ^ S.card := by
    have hsplit : 2 ^ d = 2 ^ S.card * 2 ^ (d - S.card) := by
      rw [← pow_add, Nat.add_sub_of_le hS]
    have hle : DepM.card * 2 ^ (d - S.card) * 2 ^ S.card ≤ (2 ^ d) ^ S.card * 2 ^ S.card := by
      calc DepM.card * 2 ^ (d - S.card) * 2 ^ S.card
          = DepM.card * (2 ^ S.card * 2 ^ (d - S.card)) := by ring
        _ = DepM.card * 2 ^ d := by rw [← hsplit]
        _ ≤ (2 ^ S.card - 1) * (2 ^ d) ^ S.card := hdep
        _ ≤ 2 ^ S.card * (2 ^ d) ^ S.card := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ = (2 ^ d) ^ S.card * 2 ^ S.card := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hle (Nat.two_pow_pos S.card)
  calc DepA.card * 2 ^ (d - S.card)
      = (DepM.card * 2 ^ (d - S.card)) * (2 ^ d) ^ Sc.card := by rw [hcard]; ring
    _ ≤ (2 ^ d) ^ S.card * (2 ^ d) ^ Sc.card := Nat.mul_le_mul_right _ hdep2
    _ = (2 ^ d) ^ (Sc.card + S.card) := by rw [← pow_add, add_comm]
    _ = (2 ^ d) ^ n := by rw [hSc]

private lemma choose_four_mul_bound (K : ℕ) :
    (4 * K).choose K * 27 ^ K ≤ 256 ^ K := by
  have hbin : (1 + 3 : ℕ) ^ (4 * K) = ∑ r ∈ Finset.range (4 * K + 1),
      1 ^ r * 3 ^ (4 * K - r) * (4 * K).choose r := add_pow 1 3 (4 * K)
  have hmem : K ∈ Finset.range (4 * K + 1) := Finset.mem_range.mpr (by omega)
  have hsingle : 1 ^ K * 3 ^ (4 * K - K) * (4 * K).choose K ≤ (1 + 3 : ℕ) ^ (4 * K) := by
    rw [hbin]
    exact Finset.single_le_sum (f := fun r => 1 ^ r * 3 ^ (4 * K - r) * (4 * K).choose r)
      (fun _ _ => Nat.zero_le _) hmem
  have h27 : 3 ^ (4 * K - K) = 27 ^ K := by
    have : 4 * K - K = 3 * K := by omega
    rw [this, pow_mul]
    norm_num
  have h256 : (1 + 3 : ℕ) ^ (4 * K) = 256 ^ K := by
    have : (1 + 3 : ℕ) = 4 := rfl
    rw [this, pow_mul]
    norm_num
  rw [one_pow, one_mul, h27, h256, mul_comm] at hsingle
  exact hsingle

private lemma pow_256_ge_mul (k : ℕ) (hk : 1 ≤ k) : 256 * k ≤ 256 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0; decide
    · have hk1 : 1 ≤ k := by omega
      have h := ih hk1
      rw [pow_succ]
      nlinarith

private def GoodTrialFor {n s T : ℕ} (S : Finset (Fin n))
    (B : Fin T → Fin n → Fin (s + 2) → Bool) : Prop :=
  (∃ block : Fin T, LinearIndependent (ZMod 2) (fun x : S => b2zVec (B block x.1))) ∧
  (∀ j : Fin n, j ∉ S →
    ∃ block : Fin T, LinearIndependent (ZMod 2) (fun x : ↥(insert j S) => b2zVec (B block x.1)))

open Classical in
private lemma exists_good_row {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n) :
    let L := Nat.clog 2 (n + 1)
    let T := 8 + Nat.clog 2 (n - s + 1)
    let M := 2 ^ Nat.clog 2 (4 + (s + 4) * (1 + L))
    let V := Fin (s + 2) → Bool
    ∃ row : Fin M → Fin T → Fin n → V,
      ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ s →
        3 * M ≤ 4 * (Finset.univ.filter (fun u : Fin M => GoodTrialFor S (row u))).card := by
  intro L T M V
  let Block := Fin n → V
  let Trial := Fin T → Block
  let Nblock : ℕ := (2 ^ (s + 2)) ^ n
  let Ntrial : ℕ := Nblock ^ T
  have hBlock_card : Fintype.card Block = Nblock := by
    simp [Block, V, Nblock, Fintype.card_bool]
  have hTrial_card : Fintype.card Trial = Ntrial := by
    simp [Trial, Ntrial, hBlock_card]
  have hNblock_pos : 0 < Nblock := Nat.pow_pos (Nat.two_pow_pos _)
  have hNtrial_pos : 0 < Ntrial := Nat.pow_pos hNblock_pos
  have hBadTrial_le : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ s →
      250 * (Finset.univ.filter (fun B : Trial => ¬ GoodTrialFor S B)).card ≤ Ntrial := by
    intro S hS1 hSs
    let BadS : Finset Trial :=
      Finset.univ.filter (fun B => ∀ block : Fin T,
        ¬ LinearIndependent (ZMod 2) (fun x : S => b2zVec (B block x.1)))
    let BadJ : Fin n → Finset Trial := fun j =>
      Finset.univ.filter (fun B => ∀ block : Fin T,
        ¬ LinearIndependent (ZMod 2) (fun x : ↥(insert j S) => b2zVec (B block x.1)))
    let Sc : Finset (Fin n) := Finset.univ \ S
    have hsub : Finset.univ.filter (fun B : Trial => ¬ GoodTrialFor S B) ⊆
        BadS ∪ Sc.biUnion BadJ := by
      intro B hB
      have hB' : ¬ GoodTrialFor S B := (Finset.mem_filter.mp hB).2
      rw [Finset.mem_union]
      by_cases h1 : ∃ block : Fin T, LinearIndependent (ZMod 2) (fun x : S => b2zVec (B block x.1))
      · right
        have h2 : ¬ ∀ j : Fin n, j ∉ S →
            ∃ block : Fin T, LinearIndependent (ZMod 2) (fun x : ↥(insert j S) => b2zVec (B block x.1)) :=
          fun h => hB' ⟨h1, h⟩
        push Not at h2
        rcases h2 with ⟨j, hjS, hjbad⟩
        rw [Finset.mem_biUnion]
        exact ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjS⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjbad⟩⟩
      · left
        push Not at h1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
    have hBadS_card : 65536 * BadS.card ≤ Ntrial := by
      let DepS : Finset Block := Finset.univ.filter (fun A =>
        ¬ LinearIndependent (ZMod 2) (fun x : S => b2zVec (A x.1)))
      have hBadS_eq : BadS.card = DepS.card ^ T := by
        have h1 : BadS = Fintype.piFinset (fun _ : Fin T => DepS) := by
          ext B; rw [Fintype.mem_piFinset]; simp [BadS, DepS]
        rw [h1, Fintype.card_piFinset]
        simp
      have hdepS := card_dep_subset (d := s + 2) S (by omega)
      have hge2 : 2 ≤ s + 2 - S.card := by omega
      have h4 : 4 * DepS.card ≤ Nblock := by
        calc 4 * DepS.card = DepS.card * 2 ^ 2 := by ring
          _ ≤ DepS.card * 2 ^ (s + 2 - S.card) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hge2)
          _ ≤ Nblock := hdepS
      have hT8 : 8 ≤ T := by omega
      calc 65536 * BadS.card
          = 4 ^ 8 * DepS.card ^ T := by rw [hBadS_eq]
        _ ≤ 4 ^ T * DepS.card ^ T := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hT8)
        _ = (4 * DepS.card) ^ T := (mul_pow 4 DepS.card T).symm
        _ ≤ Nblock ^ T := Nat.pow_le_pow_left h4 T
    let k := s + 1 - S.card
    have hk1 : 1 ≤ k := by omega
    have hBadJ_each : ∀ j ∈ Sc, (2 ^ k) ^ T * (BadJ j).card ≤ Ntrial := by
      intro j hj
      have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
      have hcard_ins : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hjS
      let DepJ : Finset Block := Finset.univ.filter (fun A =>
        ¬ LinearIndependent (ZMod 2) (fun x : ↥(insert j S) => b2zVec (A x.1)))
      have hBadJ_eq : (BadJ j).card = DepJ.card ^ T := by
        have h1 : BadJ j = Fintype.piFinset (fun _ : Fin T => DepJ) := by
          ext B; rw [Fintype.mem_piFinset]; simp [BadJ, DepJ]
        rw [h1, Fintype.card_piFinset]
        simp
      have hdepJ := card_dep_subset (d := s + 2) (insert j S) (by omega)
      have hsub_eq : s + 2 - (insert j S).card = k := by omega
      rw [hsub_eq] at hdepJ
      rw [hBadJ_eq, ← mul_pow, mul_comm]
      exact Nat.pow_le_pow_left hdepJ T
    have hSc_card : Sc.card = n - S.card := by
      simp [Sc, Finset.card_sdiff]
    have h256_Sc : 256 * Sc.card ≤ (2 ^ k) ^ T := by
      let D := n - s + 1
      have hD1 : 1 ≤ D := by omega
      have hSc_le_Dk : Sc.card ≤ D * k := by
        have : Sc.card = (n - s) + (k - 1) := by omega
        have h1 : (D - 1) + (k - 1) ≤ D * k := by
          obtain ⟨d', hd'⟩ := Nat.exists_eq_add_of_le' hD1
          obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le' hk1
          rw [hd', hk']
          simp only [Nat.add_sub_cancel]
          nlinarith
        omega
      have h2T : 256 * D ≤ 2 ^ T := by
        have hclog : D ≤ 2 ^ Nat.clog 2 D := Nat.le_pow_clog (by omega) D
        have hTeq : 2 ^ T = 256 * 2 ^ Nat.clog 2 D := by
          simp only [T, D, pow_add]
          norm_num
        rw [hTeq]
        exact Nat.mul_le_mul_left 256 hclog
      have hDk : D ≤ D ^ k := by
        calc D = D ^ 1 := (pow_one D).symm
          _ ≤ D ^ k := Nat.pow_le_pow_right hD1 hk1
      calc 256 * Sc.card
          ≤ 256 * (D * k) := Nat.mul_le_mul_left 256 hSc_le_Dk
        _ = (256 * k) * D := by ring
        _ ≤ 256 ^ k * D ^ k := Nat.mul_le_mul (pow_256_ge_mul k hk1) hDk
        _ = (256 * D) ^ k := (mul_pow 256 D k).symm
        _ ≤ (2 ^ T) ^ k := Nat.pow_le_pow_left h2T k
        _ = (2 ^ k) ^ T := by rw [← pow_mul, ← pow_mul, mul_comm]
    have hBadJ_sum : 256 * (Sc.biUnion BadJ).card ≤ Ntrial := by
      have hmul : (2 ^ k) ^ T * (Sc.biUnion BadJ).card ≤ Sc.card * Ntrial := by
        calc (2 ^ k) ^ T * (Sc.biUnion BadJ).card
            ≤ (2 ^ k) ^ T * ∑ j ∈ Sc, (BadJ j).card :=
              Nat.mul_le_mul_left _ Finset.card_biUnion_le
          _ = ∑ j ∈ Sc, (2 ^ k) ^ T * (BadJ j).card := Finset.mul_sum _ _ _
          _ ≤ ∑ _j ∈ Sc, Ntrial := Finset.sum_le_sum hBadJ_each
          _ = Sc.card * Ntrial := by rw [Finset.sum_const, smul_eq_mul]
      have hpos : 0 < (2 ^ k) ^ T := Nat.pow_pos (Nat.two_pow_pos k)
      have h2 : (256 * (Sc.biUnion BadJ).card) * (2 ^ k) ^ T ≤ Ntrial * (2 ^ k) ^ T := by
        calc (256 * (Sc.biUnion BadJ).card) * (2 ^ k) ^ T
            = 256 * ((2 ^ k) ^ T * (Sc.biUnion BadJ).card) := by ring
          _ ≤ 256 * (Sc.card * Ntrial) := Nat.mul_le_mul_left 256 hmul
          _ = (256 * Sc.card) * Ntrial := by ring
          _ ≤ (2 ^ k) ^ T * Ntrial := Nat.mul_le_mul_right Ntrial h256_Sc
          _ = Ntrial * (2 ^ k) ^ T := mul_comm _ _
      exact Nat.le_of_mul_le_mul_right h2 hpos
    have hcard_le : (Finset.univ.filter (fun B : Trial => ¬ GoodTrialFor S B)).card ≤
        BadS.card + (Sc.biUnion BadJ).card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have h65536 : 65536 * (Finset.univ.filter (fun B : Trial => ¬ GoodTrialFor S B)).card ≤
        257 * Ntrial := by
      calc 65536 * (Finset.univ.filter (fun B : Trial => ¬ GoodTrialFor S B)).card
          ≤ 65536 * (BadS.card + (Sc.biUnion BadJ).card) := Nat.mul_le_mul_left _ hcard_le
        _ = 65536 * BadS.card + 256 * (256 * (Sc.biUnion BadJ).card) := by ring
        _ ≤ Ntrial + 256 * Ntrial := Nat.add_le_add hBadS_card (Nat.mul_le_mul_left 256 hBadJ_sum)
        _ = 257 * Ntrial := by ring
    omega
  have hM_ge : 4 + (s + 4) * (1 + L) ≤ M := Nat.le_pow_clog (by omega) _
  have hclog_ge : 2 ≤ Nat.clog 2 (4 + (s + 4) * (1 + L)) := by
    by_contra hlt
    have hle1 : Nat.clog 2 (4 + (s + 4) * (1 + L)) ≤ 1 := by omega
    have hpow : 4 + (s + 4) * (1 + L) ≤ 2 ^ 1 :=
      le_trans (Nat.le_pow_clog (by omega) _) (Nat.pow_le_pow_right (by omega) hle1)
    omega
  let K := 2 ^ (Nat.clog 2 (4 + (s + 4) * (1 + L)) - 2)
  have hM_eq : M = 4 * K := by
    have hsub : Nat.clog 2 (4 + (s + 4) * (1 + L)) = (Nat.clog 2 (4 + (s + 4) * (1 + L)) - 2) + 2 := by
      omega
    simp only [M, K]
    conv_lhs => rw [hsub, pow_add]
    ring
  have hFailRow_le : ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ s →
      2 ^ M * (Finset.univ.filter (fun row : Fin M → Trial =>
        ¬ (3 * M ≤ 4 * (Finset.univ.filter (fun u : Fin M => GoodTrialFor S (row u))).card))).card ≤
      Ntrial ^ M := by
    intro S hS1 hSs
    let BadT : Finset Trial := Finset.univ.filter (fun B : Trial => ¬ GoodTrialFor S B)
    have hBadT : 250 * BadT.card ≤ Ntrial := hBadTrial_le S hS1 hSs
    let SubsetsK : Finset (Finset (Fin M)) := Finset.univ.powersetCard K
    let BadForI : Finset (Fin M) → Finset (Fin M → Trial) := fun I =>
      Finset.univ.filter (fun row => ∀ u ∈ I, row u ∈ BadT)
    have hsub : Finset.univ.filter (fun row : Fin M → Trial =>
        ¬ (3 * M ≤ 4 * (Finset.univ.filter (fun u : Fin M => GoodTrialFor S (row u))).card)) ⊆
        SubsetsK.biUnion BadForI := by
      intro row hrow
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrow
      let GoodU : Finset (Fin M) := Finset.univ.filter (fun u => GoodTrialFor S (row u))
      let BadU : Finset (Fin M) := Finset.univ.filter (fun u => ¬ GoodTrialFor S (row u))
      have hpart : GoodU.card + BadU.card = M := by
        have hun : GoodU ∪ BadU = Finset.univ := by
          ext u
          simp only [GoodU, BadU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            iff_true]
          exact Classical.em _
        have hdisj : Disjoint GoodU BadU := by
          rw [Finset.disjoint_left]
          intro u h1 h2
          simp only [GoodU, BadU, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          exact h2 h1
        rw [← Finset.card_union_of_disjoint hdisj, hun]
        simp
      have hlt_good : 4 * GoodU.card < 3 * M := Nat.lt_of_not_ge hrow
      have hK_le : K ≤ BadU.card := by omega
      rcases Finset.exists_subset_card_eq hK_le with ⟨I, hIsub, hIcard⟩
      rw [Finset.mem_biUnion]
      refine ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hIcard⟩, ?_⟩
      simp only [BadForI, Finset.mem_filter, Finset.mem_univ, true_and]
      intro u hu
      have hbu := hIsub hu
      simp only [BadU, BadT, Finset.mem_filter, Finset.mem_univ, true_and] at hbu ⊢
      exact hbu
    have hBadForI_card : ∀ I ∈ SubsetsK, (BadForI I).card = BadT.card ^ K * Ntrial ^ (M - K) := by
      intro I hI
      have hIcard : I.card = K := (Finset.mem_powersetCard.mp hI).2
      have hbij : BadForI I = Fintype.piFinset (fun u : Fin M => if u ∈ I then BadT else Finset.univ) := by
        ext row
        simp only [BadForI, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        constructor
        · intro h u
          by_cases hu : u ∈ I
          · simp only [ite_eq_left hu]; exact h u hu
          · simp only [ite_eq_right hu]; exact Finset.mem_univ _
        · intro h u hu
          have := h u
          simpa [hu] using this
      rw [hbij, Fintype.card_piFinset]
      have hsplit : (∏ u : Fin M, (if u ∈ I then BadT else Finset.univ).card) =
          (∏ u ∈ I, BadT.card) * (∏ u ∈ Finset.univ \ I, (Finset.univ : Finset Trial).card) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun u => u ∈ I)]
        congr 1
        · have h1 : Finset.univ.filter (fun u : Fin M => u ∈ I) = I := by ext u; simp
          rw [h1]
          exact Finset.prod_congr rfl (fun u hu => by simp [hu])
        · have h2 : Finset.univ.filter (fun u : Fin M => u ∉ I) = Finset.univ \ I := by
            ext u; simp
          rw [h2]
          exact Finset.prod_congr rfl (fun u hu => by
            have : u ∉ I := (Finset.mem_sdiff.mp hu).2
            simp [this])
      rw [hsplit, Finset.prod_const, Finset.prod_const, hIcard, Finset.card_univ, hTrial_card]
      have hsd : (Finset.univ \ I).card = M - K := by
        simp [Finset.card_sdiff, hIcard]
      rw [hsd]
    have hcard_union :
        (Finset.univ.filter (fun row : Fin M → Trial =>
          ¬ (3 * M ≤ 4 * (Finset.univ.filter (fun u : Fin M => GoodTrialFor S (row u))).card))).card ≤
        M.choose K * (BadT.card ^ K * Ntrial ^ (M - K)) := by
      calc (Finset.univ.filter (fun row : Fin M → Trial =>
              ¬ (3 * M ≤ 4 * (Finset.univ.filter (fun u : Fin M => GoodTrialFor S (row u))).card))).card
          ≤ (SubsetsK.biUnion BadForI).card := Finset.card_le_card hsub
        _ ≤ ∑ I ∈ SubsetsK, (BadForI I).card := Finset.card_biUnion_le
        _ = ∑ _I ∈ SubsetsK, BadT.card ^ K * Ntrial ^ (M - K) :=
            Finset.sum_congr rfl hBadForI_card
        _ = SubsetsK.card * (BadT.card ^ K * Ntrial ^ (M - K)) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = M.choose K * (BadT.card ^ K * Ntrial ^ (M - K)) := by
            simp [SubsetsK, Finset.card_powersetCard]
    have hpos : 0 < 27 ^ K * 250 ^ K := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
    have h2M : 2 ^ M = 16 ^ K := by
      rw [hM_eq, pow_mul]
      norm_num
    have h4096 : 16 ^ K * 256 ^ K ≤ 27 ^ K * 250 ^ K := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left (by decide) K
    have hKm : K + (M - K) = M := by omega
    have hmul : (2 ^ M * (Finset.univ.filter (fun row : Fin M → Trial =>
        ¬ (3 * M ≤ 4 * (Finset.univ.filter (fun u : Fin M => GoodTrialFor S (row u))).card))).card) *
        (27 ^ K * 250 ^ K) ≤ Ntrial ^ M * (27 ^ K * 250 ^ K) := by
      calc (2 ^ M * (Finset.univ.filter (fun row : Fin M → Trial =>
              ¬ (3 * M ≤ 4 * (Finset.univ.filter (fun u : Fin M => GoodTrialFor S (row u))).card))).card) *
              (27 ^ K * 250 ^ K)
          ≤ (16 ^ K * (M.choose K * (BadT.card ^ K * Ntrial ^ (M - K)))) * (27 ^ K * 250 ^ K) := by
            rw [h2M]
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcard_union)
        _ = 16 ^ K * (M.choose K * 27 ^ K) * ((250 * BadT.card) ^ K * Ntrial ^ (M - K)) := by
            rw [mul_pow]; ring
        _ ≤ 16 ^ K * 256 ^ K * (Ntrial ^ K * Ntrial ^ (M - K)) := by
            have h1 : M.choose K * 27 ^ K ≤ 256 ^ K := by
              rw [hM_eq]; exact choose_four_mul_bound K
            have h2 : (250 * BadT.card) ^ K ≤ Ntrial ^ K := Nat.pow_le_pow_left hBadT K
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_right _ h2)
        _ = (16 ^ K * 256 ^ K) * Ntrial ^ M := by rw [← pow_add, hKm]
        _ ≤ (27 ^ K * 250 ^ K) * Ntrial ^ M := Nat.mul_le_mul_right _ h4096
        _ = Ntrial ^ M * (27 ^ K * 250 ^ K) := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hmul hpos
  let Enc := Fin s → Option (Fin n)
  let setOfEnc : Enc → Finset (Fin n) := fun f =>
    Finset.univ.filter (fun x : Fin n => ∃ i : Fin s, f i = some x)
  let FailRow : Enc → Finset (Fin M → Trial) := fun f =>
    if 1 ≤ (setOfEnc f).card then
      Finset.univ.filter (fun row =>
        ¬ (3 * M ≤ 4 * (Finset.univ.filter (fun u : Fin M => GoodTrialFor (setOfEnc f) (row u))).card))
    else ∅
  have hEnc_le : ∀ f : Enc, (setOfEnc f).card ≤ s := by
    intro f
    let gEnc : Fin s → Finset (Fin n) := fun i =>
      match f i with | some x => {x} | none => ∅
    have hsub : setOfEnc f ⊆ (Finset.univ : Finset (Fin s)).biUnion gEnc := by
      intro x hx
      simp only [setOfEnc, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨i, hi⟩
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simp [gEnc, hi]
    calc (setOfEnc f).card
        ≤ ((Finset.univ : Finset (Fin s)).biUnion gEnc).card := Finset.card_le_card hsub
      _ ≤ ∑ i : Fin s, (gEnc i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin s, 1 := Finset.sum_le_sum (fun i _ => by dsimp only [gEnc]; cases f i <;> simp)
      _ = s := by simp
  have hFailRow_enc : ∀ f : Enc, 2 ^ M * (FailRow f).card ≤ Ntrial ^ M := by
    intro f
    by_cases h1 : 1 ≤ (setOfEnc f).card
    · simp only [FailRow, ite_eq_left h1]
      exact hFailRow_le (setOfEnc f) h1 (hEnc_le f)
    · simp only [FailRow, ite_eq_right h1, Finset.card_empty, mul_zero]
      exact Nat.zero_le _
  let AllFail : Finset (Fin M → Trial) := Finset.univ.biUnion FailRow
  have hEnc_card : Fintype.card Enc = (n + 1) ^ s := by
    simp [Enc, Fintype.card_option]
  have hEnc_lt : (n + 1) ^ s < 2 ^ M := by
    have hclog : n + 1 ≤ 2 ^ L := Nat.le_pow_clog (by omega) (n + 1)
    have h1 : (n + 1) ^ s ≤ 2 ^ (L * s) := by
      calc (n + 1) ^ s ≤ (2 ^ L) ^ s := Nat.pow_le_pow_left hclog s
        _ = 2 ^ (L * s) := (pow_mul 2 L s).symm
    have h2 : L * s < M := by nlinarith
    exact lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by omega) h2)
  have hAll_lt : AllFail.card < (Finset.univ : Finset (Fin M → Trial)).card := by
    have huniv : (Finset.univ : Finset (Fin M → Trial)).card = Ntrial ^ M := by
      simp [hTrial_card]
    rw [huniv]
    have hmul : 2 ^ M * AllFail.card < 2 ^ M * Ntrial ^ M := by
      calc 2 ^ M * AllFail.card
          ≤ 2 ^ M * ∑ f : Enc, (FailRow f).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ f : Enc, 2 ^ M * (FailRow f).card := Finset.mul_sum _ _ _
        _ ≤ ∑ _f : Enc, Ntrial ^ M := Finset.sum_le_sum (fun f _ => hFailRow_enc f)
        _ = (n + 1) ^ s * Ntrial ^ M := by
            rw [Finset.sum_const, Finset.card_univ, hEnc_card, smul_eq_mul]
        _ < 2 ^ M * Ntrial ^ M := Nat.mul_lt_mul_of_pos_right hEnc_lt (Nat.pow_pos hNtrial_pos)
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hne : (Finset.univ \ AllFail).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin M → Trial)) ⊆ AllFail :=
      Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  rcases hne with ⟨row, hrow⟩
  refine ⟨row, ?_⟩
  intro S hS1 hSs
  have hrow_not : row ∉ AllFail := (Finset.mem_sdiff.mp hrow).2
  let eS : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp)).symm
  let f : Enc := fun i => if h : i.val < S.card then some (eS ⟨i.val, h⟩).1 else none
  have hf_eq : setOfEnc f = S := by
    ext x
    simp only [setOfEnc, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i.val < S.card
      · simp only [f, dite_eq_left h, Option.some.injEq] at hi
        rw [← hi]; exact (eS ⟨i.val, h⟩).2
      · simp only [f, dite_eq_right h, reduceCtorEq] at hi
    · intro hx
      let k := eS.symm ⟨x, hx⟩
      refine ⟨⟨k.val, lt_of_lt_of_le k.isLt hSs⟩, ?_⟩
      simp only [f, dite_eq_left k.isLt]
      have hk_eq : (⟨k.val, k.isLt⟩ : Fin S.card) = k := Fin.eta k k.isLt
      rw [hk_eq]
      simp [k]
  have hnot_fail : row ∉ FailRow f := by
    intro hmem
    exact hrow_not (Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, hmem⟩)
  simp only [FailRow, hf_eq, ite_eq_left hS1, Finset.mem_filter, Finset.mem_univ, true_and,
    not_not] at hnot_fail
  exact hnot_fail

private lemma certify_empty {n a : ℕ} (cal : Fin a → Fin n → Bool) (hcal : Surj4 cal)
    (C C' : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (hempty : ∀ w, satF C w = true)
    (hagree : ∀ slot : Fin a, satF C' (cal slot) = satF C (cal slot)) :
    ∀ z, satF C' z = satF C z := by
  intro z
  rw [hempty z]
  simp only [satF, decide_eq_true_eq]
  intro c hc
  by_contra hbad
  push Not at hbad
  rcases hbad with ⟨h1, h2⟩
  let S : Finset (Fin n) := {c.1.1, c.2.1}
  have hS : S.card ≤ 4 := by
    have : S.card ≤ 2 := Finset.card_le_two
    omega
  rcases hcal S hS z with ⟨slot, hslot⟩
  have hsat := hagree slot
  rw [hempty (cal slot)] at hsat
  have hcl := (decide_eq_true_eq.mp hsat) c hc
  have h1' : cal slot c.1.1 = c.1.2 := by rw [hslot c.1.1 (by simp [S]), h1]
  have h2' : cal slot c.2.1 = c.2.2 := by rw [hslot c.2.1 (by simp [S]), h2]
  rcases hcl with ha | hb
  · exact ha h1'
  · exact hb h2'

private lemma certify_pair {n a : ℕ} (cal : Fin a → Fin n → Bool) (hcal : Surj4 cal)
    (C C' : Finset ((Fin n × Bool) × (Fin n × Bool)))
    {x1 x2 x3 x4 : Fin n} {s1 s2 s3 s4 : Bool}
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4)
    (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h34 : x3 ≠ x4)
    (hC : ∀ w, satF C w = decide ((w x1 ≠ s1 ∨ w x2 ≠ s2) ∧ (w x3 ≠ s3 ∨ w x4 ≠ s4)))
    (hagree : ∀ slot : Fin a, satF C' (cal slot) = satF C (cal slot)) :
    ∀ z, satF C' z = satF C z := by
  have hdir1 : ∀ z, satF C z = true → satF C' z = true := by
    intro z hz
    simp only [satF, decide_eq_true_eq]
    intro c hc
    by_contra hbad
    push Not at hbad
    rcases hbad with ⟨hc1, hc2⟩
    have hz' := decide_eq_true_eq.mp (by rw [← hC z]; exact hz)
    have hp1 : ∃ y1 : Fin n, (y1 = x1 ∧ z y1 ≠ s1) ∨ (y1 = x2 ∧ z y1 ≠ s2) := by
      rcases hz'.1 with h | h
      · exact ⟨x1, Or.inl ⟨rfl, h⟩⟩
      · exact ⟨x2, Or.inr ⟨rfl, h⟩⟩
    have hp2 : ∃ y2 : Fin n, (y2 = x3 ∧ z y2 ≠ s3) ∨ (y2 = x4 ∧ z y2 ≠ s4) := by
      rcases hz'.2 with h | h
      · exact ⟨x3, Or.inl ⟨rfl, h⟩⟩
      · exact ⟨x4, Or.inr ⟨rfl, h⟩⟩
    rcases hp1 with ⟨y1, hy1⟩
    rcases hp2 with ⟨y2, hy2⟩
    let S : Finset (Fin n) := {c.1.1, c.2.1, y1, y2}
    have hS : S.card ≤ 4 := by
      have h1 := Finset.card_insert_le c.1.1 ({c.2.1, y1, y2} : Finset (Fin n))
      have h2 := Finset.card_insert_le c.2.1 ({y1, y2} : Finset (Fin n))
      have h3 := Finset.card_insert_le y1 ({y2} : Finset (Fin n))
      simp only [Finset.card_singleton] at h3
      change ({c.1.1, c.2.1, y1, y2} : Finset (Fin n)).card ≤ 4
      omega
    rcases hcal S hS z with ⟨slot, hslot⟩
    have hsatC : satF C (cal slot) = true := by
      rw [hC, decide_eq_true_eq]
      constructor
      · rcases hy1 with ⟨rfl, h⟩ | ⟨rfl, h⟩
        · left; rw [hslot y1 (by simp [S])]; exact h
        · right; rw [hslot y1 (by simp [S])]; exact h
      · rcases hy2 with ⟨rfl, h⟩ | ⟨rfl, h⟩
        · left; rw [hslot y2 (by simp [S])]; exact h
        · right; rw [hslot y2 (by simp [S])]; exact h
    have hsatC' : satF C' (cal slot) = true := by rw [hagree slot, hsatC]
    have hcl := (decide_eq_true_eq.mp hsatC') c hc
    have h1' : cal slot c.1.1 = c.1.2 := by rw [hslot c.1.1 (by simp [S]), hc1]
    have h2' : cal slot c.2.1 = c.2.2 := by rw [hslot c.2.1 (by simp [S]), hc2]
    rcases hcl with ha | hb
    · exact ha h1'
    · exact hb h2'
  have hdir2 : ∀ z, satF C' z = true → satF C z = true := by
    intro z hz
    have hcl_only : ∀ c ∈ C', ∀ w : Fin n → Bool, w c.1.1 = c.1.2 → w c.2.1 = c.2.2 →
        (w x1 = s1 ∧ w x2 = s2) ∨ (w x3 = s3 ∧ w x4 = s4) := by
      intro c hc w hw1 hw2
      by_contra hneither
      push Not at hneither
      have hsatCw : satF C w = true := by
        rw [hC, decide_eq_true_eq]
        constructor
        · by_cases h : w x1 = s1
          · right; exact hneither.1 h
          · left; exact h
        · by_cases h : w x3 = s3
          · right; exact hneither.2 h
          · left; exact h
      have hsatC'w := hdir1 w hsatCw
      rcases (decide_eq_true_eq.mp hsatC'w) c hc with ha | hb
      · exact ha hw1
      · exact hb hw2
    have hS4 : ({x1, x2, x3, x4} : Finset (Fin n)).card ≤ 4 := by
      have h1 := Finset.card_insert_le x1 ({x2, x3, x4} : Finset (Fin n))
      have h2 := Finset.card_insert_le x2 ({x3, x4} : Finset (Fin n))
      have h3 := Finset.card_insert_le x3 ({x4} : Finset (Fin n))
      simp only [Finset.card_singleton] at h3
      omega
    have hhas1 : ∃ c ∈ C',
        ((c.1 = (x1, s1) ∧ c.2 = (x2, s2)) ∨ (c.1 = (x2, s2) ∧ c.2 = (x1, s1))) := by
      let g : Fin n → Bool := fun i =>
        if i = x1 then s1 else if i = x2 then s2 else if i = x3 then !s3 else !s4
      rcases hcal {x1, x2, x3, x4} hS4 g with ⟨slot, hslot⟩
      have hx1 : cal slot x1 = s1 := by rw [hslot x1 (by simp)]; simp [g]
      have hx2 : cal slot x2 = s2 := by rw [hslot x2 (by simp)]; simp [g, h12.symm]
      have hx3 : cal slot x3 = !s3 := by rw [hslot x3 (by simp)]; simp [g, h13.symm, h23.symm]
      have hx4 : cal slot x4 = !s4 := by rw [hslot x4 (by simp)]; simp [g, h14.symm, h24.symm, h34.symm]
      have hfalseC : satF C (cal slot) = false := by
        rw [hC, decide_eq_false_iff_not]
        intro ⟨h, _⟩
        rcases h with h | h
        · exact h hx1
        · exact h hx2
      have hfalseC' : satF C' (cal slot) = false := by rw [hagree slot, hfalseC]
      rw [satF, decide_eq_false_iff_not] at hfalseC'
      push Not at hfalseC'
      rcases hfalseC' with ⟨c, hc, hc1, hc2⟩
      refine ⟨c, hc, ?_⟩
      have hforce : ∀ i : Fin n, i = x1 ∨ i = x2 →
          (c.1.1 = i ∧ c.1.2 = (if i = x1 then s1 else s2)) ∨
          (c.2.1 = i ∧ c.2.2 = (if i = x1 then s1 else s2)) := by
        intro i hi
        by_contra hnot
        let w : Fin n → Bool := fun j =>
          if j = i then !(if i = x1 then s1 else s2) else cal slot j
        have hw1 : w c.1.1 = c.1.2 := by
          by_cases hj : c.1.1 = i
          · exfalso; apply hnot; left; refine ⟨hj, ?_⟩
            rw [← hc1, hj]
            rcases hi with rfl | rfl
            · simp [hx1]
            · simp [hx2, h12.symm]
          · simp [w, hj, hc1]
        have hw2 : w c.2.1 = c.2.2 := by
          by_cases hj : c.2.1 = i
          · exfalso; apply hnot; right; refine ⟨hj, ?_⟩
            rw [← hc2, hj]
            rcases hi with rfl | rfl
            · simp [hx1]
            · simp [hx2, h12.symm]
          · simp [w, hj, hc2]
        rcases hcl_only c hc w hw1 hw2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rcases hi with rfl | rfl
          · simp [w] at ha
          · simp [w, h12.symm] at hb
        · rcases hi with rfl | rfl
          · simp [w, h13.symm, hx3] at ha
          · simp [w, h23.symm, hx3] at ha
      rcases hforce x1 (Or.inl rfl) with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
        rcases hforce x2 (Or.inr rfl) with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
      · exfalso; exact h12 (h1a.symm.trans h2a)
      · left; simp only [ite_true, h12.symm, ite_false] at h1b h2b
        exact ⟨Prod.ext h1a h1b, Prod.ext h2a h2b⟩
      · right; simp only [ite_true, h12.symm, ite_false] at h1b h2b
        exact ⟨Prod.ext h2a h2b, Prod.ext h1a h1b⟩
      · exfalso; exact h12 (h1a.symm.trans h2a)
    have hhas2 : ∃ c ∈ C',
        ((c.1 = (x3, s3) ∧ c.2 = (x4, s4)) ∨ (c.1 = (x4, s4) ∧ c.2 = (x3, s3))) := by
      let g : Fin n → Bool := fun i =>
        if i = x3 then s3 else if i = x4 then s4 else if i = x1 then !s1 else !s2
      rcases hcal {x1, x2, x3, x4} hS4 g with ⟨slot, hslot⟩
      have hx3 : cal slot x3 = s3 := by rw [hslot x3 (by simp)]; simp [g]
      have hx4 : cal slot x4 = s4 := by rw [hslot x4 (by simp)]; simp [g, h34.symm]
      have hx1 : cal slot x1 = !s1 := by rw [hslot x1 (by simp)]; simp [g, h13, h14]
      have hx2 : cal slot x2 = !s2 := by rw [hslot x2 (by simp)]; simp [g, h23, h24, h12.symm]
      have hfalseC : satF C (cal slot) = false := by
        rw [hC, decide_eq_false_iff_not]
        intro ⟨_, h⟩
        rcases h with h | h
        · exact h hx3
        · exact h hx4
      have hfalseC' : satF C' (cal slot) = false := by rw [hagree slot, hfalseC]
      rw [satF, decide_eq_false_iff_not] at hfalseC'
      push Not at hfalseC'
      rcases hfalseC' with ⟨c, hc, hc1, hc2⟩
      refine ⟨c, hc, ?_⟩
      have hforce : ∀ i : Fin n, i = x3 ∨ i = x4 →
          (c.1.1 = i ∧ c.1.2 = (if i = x3 then s3 else s4)) ∨
          (c.2.1 = i ∧ c.2.2 = (if i = x3 then s3 else s4)) := by
        intro i hi
        by_contra hnot
        let w : Fin n → Bool := fun j =>
          if j = i then !(if i = x3 then s3 else s4) else cal slot j
        have hw1 : w c.1.1 = c.1.2 := by
          by_cases hj : c.1.1 = i
          · exfalso; apply hnot; left; refine ⟨hj, ?_⟩
            rw [← hc1, hj]
            rcases hi with rfl | rfl
            · simp [hx3]
            · simp [hx4, h34.symm]
          · simp [w, hj, hc1]
        have hw2 : w c.2.1 = c.2.2 := by
          by_cases hj : c.2.1 = i
          · exfalso; apply hnot; right; refine ⟨hj, ?_⟩
            rw [← hc2, hj]
            rcases hi with rfl | rfl
            · simp [hx3]
            · simp [hx4, h34.symm]
          · simp [w, hj, hc2]
        rcases hcl_only c hc w hw1 hw2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rcases hi with rfl | rfl
          · simp [w, h13, hx1] at ha
          · simp [w, h14, hx1] at ha
        · rcases hi with rfl | rfl
          · simp [w] at ha
          · simp [w, h34.symm] at hb
      rcases hforce x3 (Or.inl rfl) with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
        rcases hforce x4 (Or.inr rfl) with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
      · exfalso; exact h34 (h1a.symm.trans h2a)
      · left; simp only [ite_true, h34.symm, ite_false] at h1b h2b
        exact ⟨Prod.ext h1a h1b, Prod.ext h2a h2b⟩
      · right; simp only [ite_true, h34.symm, ite_false] at h1b h2b
        exact ⟨Prod.ext h2a h2b, Prod.ext h1a h1b⟩
      · exfalso; exact h34 (h1a.symm.trans h2a)
    rw [hC, decide_eq_true_eq]
    have hz' := decide_eq_true_eq.mp hz
    constructor
    · rcases hhas1 with ⟨c, hc, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · have := hz' c hc; rwa [h1, h2] at this
      · have := hz' c hc; rw [h1, h2] at this; exact this.symm
    · rcases hhas2 with ⟨c, hc, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · have := hz' c hc; rwa [h1, h2] at this
      · have := hz' c hc; rw [h1, h2] at this; exact this.symm
  intro z
  cases h1 : satF C z <;> cases h2 : satF C' z
  · rfl
  · exfalso; have := hdir2 z h2; rw [h1] at this; exact Bool.false_ne_true this
  · exfalso; have := hdir1 z h1; rw [h2] at this; exact Bool.false_ne_true this
  · rfl

private lemma certify_star {n s a T : ℕ} (cal : Fin a → Fin n → Bool) (hcal : Surj4 cal)
    (B : Fin T → Fin n → Fin (s + 2) → Bool)
    (C C' : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (v : Fin n) (U : Finset (Fin n)) (σ : Fin n → Bool)
    (hvU : v ∉ U)
    (hC : ∀ w, satF C w = decide (∀ u ∈ U, w v ≠ σ v ∨ w u ≠ σ u))
    (hgood : GoodTrialFor (insert v U) B)
    (hagree_cal : ∀ slot : Fin a, satF C' (cal slot) = satF C (cal slot))
    (hagree_lin : ∀ (block : Fin T) (inp : Fin (s + 2) → Bool),
      satF C' (linEval (B block) inp) = satF C (linEval (B block) inp)) :
    ∀ z, satF C' z = satF C z := by
  let S : Finset (Fin n) := insert v U
  have hdir1 : ∀ z, satF C z = true → satF C' z = true := by
    intro z hz
    simp only [satF, decide_eq_true_eq]
    intro c hc
    by_contra hbad
    push Not at hbad
    rcases hbad with ⟨hc1, hc2⟩
    by_cases hhit : c.1 = (v, σ v) ∨ c.2 = (v, σ v)
    · have hother : ∃ j : Fin n, (c.1 = (v, σ v) ∧ c.2.1 = j) ∨ (c.2 = (v, σ v) ∧ c.1.1 = j) := by
        rcases hhit with h | h
        · exact ⟨c.2.1, Or.inl ⟨h, rfl⟩⟩
        · exact ⟨c.1.1, Or.inr ⟨h, rfl⟩⟩
      rcases hother with ⟨j, hj⟩
      have hex_w : ∃ w : Fin n → Bool,
          (∀ x ∈ S, w x = z x) ∧ w j = z j ∧ satF C' w = satF C w := by
        by_cases hjS : j ∈ S
        · rcases hgood.1 with ⟨block, hli⟩
          rcases linIndep_surj (B block) S hli z with ⟨inp, hinp⟩
          exact ⟨linEval (B block) inp, hinp, hinp j hjS, hagree_lin block inp⟩
        · rcases hgood.2 j hjS with ⟨block, hli⟩
          rcases linIndep_surj (B block) (insert j S) hli z with ⟨inp, hinp⟩
          exact ⟨linEval (B block) inp, fun x hx => hinp x (Finset.mem_insert_of_mem hx),
            hinp j (Finset.mem_insert_self j S), hagree_lin block inp⟩
      rcases hex_w with ⟨w, hwS, hwj, hagree_w⟩
      have hsatCw : satF C w = true := by
        rw [hC, decide_eq_true_eq]
        intro u hu
        rw [hwS v (Finset.mem_insert_self v U), hwS u (Finset.mem_insert_of_mem hu)]
        have hz' : decide (∀ u ∈ U, z v ≠ σ v ∨ z u ≠ σ u) = true := by rw [← hC z]; exact hz
        exact (decide_eq_true_eq.mp hz') u hu
      have hsatC'w : satF C' w = true := by rw [hagree_w, hsatCw]
      have hcl := (decide_eq_true_eq.mp hsatC'w) c hc
      have hwv : w v = z v := hwS v (Finset.mem_insert_self v U)
      rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hc1' : z v = σ v := by rwa [h1] at hc1
        have hw_c1 : w c.1.1 = c.1.2 := by rw [h1]; exact hwv.trans hc1'
        have hw_c2 : w c.2.1 = c.2.2 := by rw [h2]; exact hwj.trans (h2 ▸ hc2)
        rcases hcl with ha | hb
        · exact ha hw_c1
        · exact hb hw_c2
      · have hc2' : z v = σ v := by rwa [h1] at hc2
        have hw_c2 : w c.2.1 = c.2.2 := by rw [h1]; exact hwv.trans hc2'
        have hw_c1 : w c.1.1 = c.1.2 := by rw [h2]; exact hwj.trans (h2 ▸ hc1)
        rcases hcl with ha | hb
        · exact ha hw_c1
        · exact hb hw_c2
    · push Not at hhit
      let g : Fin n → Bool := fun x => if x = v then !(σ v) else z x
      let T3 : Finset (Fin n) := {v, c.1.1, c.2.1}
      have hT3 : T3.card ≤ 4 := by
        have h1 := Finset.card_insert_le v ({c.1.1, c.2.1} : Finset (Fin n))
        have h2 : ({c.1.1, c.2.1} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
        change ({v, c.1.1, c.2.1} : Finset (Fin n)).card ≤ 4
        omega
      rcases hcal T3 hT3 g with ⟨slot, hslot⟩
      have hsatC : satF C (cal slot) = true := by
        rw [hC, decide_eq_true_eq]
        intro u _
        left
        rw [hslot v (by simp [T3])]
        simp [g]
      have hsatC' : satF C' (cal slot) = true := by rw [hagree_cal slot, hsatC]
      have hcl := (decide_eq_true_eq.mp hsatC') c hc
      have h1' : cal slot c.1.1 = c.1.2 := by
        rw [hslot c.1.1 (by simp [T3])]
        by_cases hv1 : c.1.1 = v
        · simp only [g, ite_eq_left hv1]
          cases hb1 : c.1.2 <;> cases hsv : σ v
          · exfalso; exact hhit.1 (Prod.ext hv1 (by rw [hb1, hsv]))
          · rfl
          · rfl
          · exfalso; exact hhit.1 (Prod.ext hv1 (by rw [hb1, hsv]))
        · simp [g, hv1, hc1]
      have h2' : cal slot c.2.1 = c.2.2 := by
        rw [hslot c.2.1 (by simp [T3])]
        by_cases hv2 : c.2.1 = v
        · simp only [g, ite_eq_left hv2]
          cases hb2 : c.2.2 <;> cases hsv : σ v
          · exfalso; exact hhit.2 (Prod.ext hv2 (by rw [hb2, hsv]))
          · rfl
          · rfl
          · exfalso; exact hhit.2 (Prod.ext hv2 (by rw [hb2, hsv]))
        · simp [g, hv2, hc2]
      rcases hcl with ha | hb
      · exact ha h1'
      · exact hb h2'
  have hdir2 : ∀ z, satF C' z = true → satF C z = true := by
    intro z hz
    rw [hC, decide_eq_true_eq]
    intro u hu
    by_contra hboth
    push Not at hboth
    rcases hboth with ⟨hzv, hzu⟩
    let g : Fin n → Bool := fun x =>
      if x = v then σ v else if x = u then σ u else !(σ x)
    rcases hgood.1 with ⟨block, hli⟩
    rcases linIndep_surj (B block) S hli g with ⟨inp, hinp⟩
    let w := linEval (B block) inp
    have hwv : w v = σ v := by
      dsimp only [w]
      rw [hinp v (Finset.mem_insert_self v U)]; simp [g]
    have hwu : w u = σ u := by
      have huv : u ≠ v := fun h => hvU (h ▸ hu)
      dsimp only [w]
      rw [hinp u (Finset.mem_insert_of_mem hu)]; simp [g, huv]
    have hw_other : ∀ u' ∈ U, u' ≠ u → w u' = !(σ u') := by
      intro u' hu' hne
      have hu'v : u' ≠ v := fun h => hvU (h ▸ hu')
      dsimp only [w]
      rw [hinp u' (Finset.mem_insert_of_mem hu')]; simp [g, hu'v, hne]
    have hfalseC : satF C w = false := by
      rw [hC, decide_eq_false_iff_not]
      intro h
      rcases h u hu with ha | hb
      · exact ha hwv
      · exact hb hwu
    have hfalseC' : satF C' w = false := by rw [hagree_lin block inp, hfalseC]
    rw [satF, decide_eq_false_iff_not] at hfalseC'
    push Not at hfalseC'
    rcases hfalseC' with ⟨c, hc, hc1, hc2⟩
    have hcl_is_vu :
        (c.1 = (v, σ v) ∧ c.2 = (u, σ u)) ∨ (c.1 = (u, σ u) ∧ c.2 = (v, σ v)) := by
      have hmust_v : c.1 = (v, σ v) ∨ c.2 = (v, σ v) := by
        by_contra hnotv
        push Not at hnotv
        let y : Fin n → Bool := fun x => if x = v then !(σ v) else w x
        have hyC : satF C y = true := by
          rw [hC, decide_eq_true_eq]
          intro u' _; left; simp [y]
        have hyC' := hdir1 y hyC
        have hy1 : y c.1.1 = c.1.2 := by
          by_cases hv1 : c.1.1 = v
          · exfalso; apply hnotv.1
            exact Prod.ext hv1 (by rw [← hc1, hv1, hwv])
          · simp [y, hv1, hc1]
        have hy2 : y c.2.1 = c.2.2 := by
          by_cases hv2 : c.2.1 = v
          · exfalso; apply hnotv.2
            exact Prod.ext hv2 (by rw [← hc2, hv2, hwv])
          · simp [y, hv2, hc2]
        rcases (decide_eq_true_eq.mp hyC') c hc with ha | hb
        · exact ha hy1
        · exact hb hy2
      have hmust_u : c.1 = (u, σ u) ∨ c.2 = (u, σ u) := by
        by_contra hnotu
        push Not at hnotu
        let y : Fin n → Bool := fun x => if x = u then !(σ u) else w x
        have hyC : satF C y = true := by
          rw [hC, decide_eq_true_eq]
          intro u' hu'
          right
          by_cases hEq : u' = u
          · subst hEq; simp [y]
          · simp [y, hEq, hw_other u' hu' hEq]
        have hyC' := hdir1 y hyC
        have hy1 : y c.1.1 = c.1.2 := by
          by_cases hu1 : c.1.1 = u
          · exfalso; apply hnotu.1
            exact Prod.ext hu1 (by rw [← hc1, hu1, hwu])
          · simp [y, hu1, hc1]
        have hy2 : y c.2.1 = c.2.2 := by
          by_cases hu2 : c.2.1 = u
          · exfalso; apply hnotu.2
            exact Prod.ext hu2 (by rw [← hc2, hu2, hwu])
          · simp [y, hu2, hc2]
        rcases (decide_eq_true_eq.mp hyC') c hc with ha | hb
        · exact ha hy1
        · exact hb hy2
      have huv : v ≠ u := fun h => hvU (h ▸ hu)
      rcases hmust_v with h1 | h1 <;> rcases hmust_u with h2 | h2
      · exfalso; exact huv (congrArg Prod.fst (h1.symm.trans h2))
      · left; exact ⟨h1, h2⟩
      · right; exact ⟨h2, h1⟩
      · exfalso; exact huv (congrArg Prod.fst (h1.symm.trans h2))
    have hzc := (decide_eq_true_eq.mp hz) c hc
    rcases hcl_is_vu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hzc
      rcases hzc with ha | hb
      · exact ha hzv
      · exact hb hzu
    · rw [h1, h2] at hzc
      rcases hzc with ha | hb
      · exact ha hzu
      · exact hb hzv
  intro z
  cases h1 : satF C z <;> cases h2 : satF C' z
  · rfl
  · exfalso; have := hdir2 z h2; rw [h1] at this; exact Bool.false_ne_true this
  · exfalso; have := hdir1 z h1; rw [h2] at this; exact Bool.false_ne_true this
  · rfl

end PEqualNP.Outside.L_lib_589_aux

theorem PEqualNP.Outside.L_lib_589 :
    ∀ (n s : ℕ), 3 ≤ s → s ≤ n →
      let W := Fin n → Bool
      let Lit := Fin n × Bool
      let F := Finset (Lit × Lit)
      let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
        w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
      let high := fun (C : F) =>
        2 ^ n * (2 ^ (s - 1) + 1) ≤
          2 ^ s * (Finset.univ.filter (fun word => sat C word = true)).card
      let L := Nat.clog 2 (n + 1)
      let a := 16 * (1 + 4 * (1 + L))
      let T := 8 + Nat.clog 2 (n - s + 1)
      let M := 2 ^ Nat.clog 2 (4 + (s + 4) * (1 + L))
      let V := Fin (s + 2) → Bool
      ∃ (cal : Fin a → W) (row : Fin M → Fin T → Fin n → V)
        (report : Fin M → (Fin a → Bool) → (Fin T → V → Bool) → Option F),
        ∀ C : F,
          let result := fun seed : Fin M =>
            report seed (fun slot => sat C (cal slot)) (fun block input => sat C (fun bit =>
              (∑ l : Fin (s + 2), ((row seed block bit l) && input l).toNat) % 2 == 1))
          (∀ trial B, result trial = some B → high C ∧ ∀ z, sat B z = sat C z) ∧
          (high C → 3 * M ≤ 4 * (Finset.univ.filter
            (fun u : Fin M => (result u).isSome = true)).card) := by
  classical
  intro n s hs hsn W Lit F sat high L a T M V
  rcases PEqualNP.Outside.L_lib_589_aux.exists_surj4 (n := n) with ⟨cal, hcal⟩
  rcases PEqualNP.Outside.L_lib_589_aux.exists_good_row hs hsn with ⟨row, hrow⟩
  let obsCal : F → Fin a → Bool := fun C slot => sat C (cal slot)
  let obsLin : Fin M → F → Fin T → V → Bool := fun seed C block input =>
    sat C (PEqualNP.Outside.L_lib_589_aux.linEval (row seed block) input)
  let validObs : Fin M → (Fin a → Bool) → (Fin T → V → Bool) → Prop := fun seed oc ol =>
    ∃ B : F, high B ∧ obsCal B = oc ∧ obsLin seed B = ol ∧
      ∀ C' : F, obsCal C' = oc → obsLin seed C' = ol → ∀ z, sat B z = sat C' z
  let report : Fin M → (Fin a → Bool) → (Fin T → V → Bool) → Option F := fun seed oc ol =>
    if h : validObs seed oc ol then some (Classical.choose h) else none
  refine ⟨cal, row, report, ?_⟩
  intro C result
  have hresult_eq : ∀ seed : Fin M, result seed = report seed (obsCal C) (obsLin seed C) :=
    fun _ => rfl
  constructor
  · intro trial B hres
    rw [hresult_eq trial] at hres
    by_cases hv : validObs trial (obsCal C) (obsLin trial C)
    · simp only [report, dite_eq_left hv, Option.some.injEq] at hres
      have hspec := Classical.choose_spec hv
      rw [hres] at hspec
      have heq : ∀ z, sat B z = sat C z := hspec.2.2.2 C rfl rfl
      have hhighC : high C := by
        have hfeq : Finset.univ.filter (fun word => sat B word = true) =
            Finset.univ.filter (fun word => sat C word = true) := by
          ext w; simp [heq w]
        have hB := hspec.1
        dsimp only [high] at hB ⊢
        rwa [← hfeq]
      exact ⟨hhighC, heq⟩
    · simp only [report, dite_eq_right hv, reduceCtorEq] at hres
  · intro hhighC
    have hisSome_of_unique : ∀ seed : Fin M,
        (∀ C' : F, obsCal C' = obsCal C → obsLin seed C' = obsLin seed C →
          ∀ z, sat C' z = sat C z) →
        (result seed).isSome = true := by
      intro seed huniq
      have hv : validObs seed (obsCal C) (obsLin seed C) :=
        ⟨C, hhighC, rfl, rfl, fun C' h1 h2 z => (huniq C' h1 h2 z).symm⟩
      rw [hresult_eq seed]
      simp [report, dite_eq_left hv]
    rcases PEqualNP.Outside.L_lib_589_aux.classify_high hs C hhighC with
      hempty | ⟨x1, x2, x3, x4, s1, s2, s3, s4, h12, h13, h14, h23, h24, h34, hpair⟩ |
      ⟨v, U, σ, hvU, hU1, hUs, hstar⟩
    · have hall : Finset.univ.filter (fun u : Fin M => (result u).isSome = true) = Finset.univ := by
        ext seed
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        apply hisSome_of_unique
        intro C' h1 _
        exact PEqualNP.Outside.L_lib_589_aux.certify_empty cal hcal C C' hempty
          (fun slot => congrFun h1 slot)
      rw [hall, Finset.card_univ, Fintype.card_fin]
      omega
    · have hall : Finset.univ.filter (fun u : Fin M => (result u).isSome = true) = Finset.univ := by
        ext seed
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        apply hisSome_of_unique
        intro C' h1 _
        exact PEqualNP.Outside.L_lib_589_aux.certify_pair cal hcal C C' h12 h13 h14 h23 h24 h34
          hpair (fun slot => congrFun h1 slot)
      rw [hall, Finset.card_univ, Fintype.card_fin]
      omega
    · let S : Finset (Fin n) := insert v U
      have hS1 : 1 ≤ S.card := by
        rw [Finset.card_insert_of_notMem hvU]; omega
      have hSs : S.card ≤ s := by
        rw [Finset.card_insert_of_notMem hvU]; omega
      have hgood_cnt := hrow S hS1 hSs
      have hsub : Finset.univ.filter (fun u : Fin M =>
          PEqualNP.Outside.L_lib_589_aux.GoodTrialFor S (row u)) ⊆
          Finset.univ.filter (fun u : Fin M => (result u).isSome = true) := by
        intro seed hseed
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hseed ⊢
        apply hisSome_of_unique
        intro C' h1 h2
        exact PEqualNP.Outside.L_lib_589_aux.certify_star cal hcal (row seed) C C' v U σ hvU
          hstar hseed (fun slot => congrFun h1 slot)
          (fun block inp => congrFun (congrFun h2 block) inp)
      exact le_trans hgood_cnt (Nat.mul_le_mul_left 4 (Finset.card_le_card hsub))
