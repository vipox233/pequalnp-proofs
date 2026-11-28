import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_872
def k_pick (n m x : ℕ) (hn : 2 ≤ n) (b : Bool) : Fin n :=
  ⟨min (cond b (x % m) (x / m)) (n - 1), lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩
theorem k_run_cons {n L : ℕ} (z : Fin n → Bool → Fin n) (u : Fin L → Fin n → Bool → Fin n)
    (q : Fin n) (w : Fin (L + 1) → Bool) :
    (List.finRange (L + 1)).foldl
      (fun state pos => (Fin.cons z u : Fin (L + 1) → Fin n → Bool → Fin n) pos state (w pos)) q =
    (List.finRange L).foldl (fun state pos => u pos state (w pos.succ)) (z q (w 0)) := by
  simp only [List.finRange_succ, List.foldl_cons, List.foldl_map, Fin.cons_zero, Fin.cons_succ]
theorem k_idx (S : Finset ℕ) : ∃ c : ℕ → ℕ, (∀ x ∈ S, c x < S.card) ∧
    (∀ x ∈ S, ∀ y ∈ S, c x = c y → x = y) := by
  refine ⟨fun x => if hx : x ∈ S then (S.equivFin ⟨x, hx⟩).val else 0, ?_, ?_⟩
  · intro x hx
    simp only [dif_pos hx]
    exact (S.equivFin ⟨x, hx⟩).isLt
  · intro x hx y hy hxy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have h3 := S.equivFin.injective (Fin.ext hxy)
    exact congrArg Subtype.val h3
theorem k_gen (n : ℕ) (hn : 2 ≤ n) : ∀ (len : ℕ) (c1 c2 : Fin n → ℕ),
    (∀ i, c1 i < min (n * n) (2 ^ (2 ^ len))) → (∀ j, c2 j < min (n * n) (2 ^ (2 ^ len))) →
    ∃ (s t : Fin len → Fin n → Bool → Fin n) (f g : Fin n → Bool), ∀ i j,
      c1 i = c2 j ↔ ∀ w : Fin len → Bool,
        f ((List.finRange len).foldl (fun state pos => s pos state (w pos)) i) =
        g ((List.finRange len).foldl (fun state pos => t pos state (w pos)) j) := by
  intro len
  induction len with
  | zero =>
    intro c1 c2 h1 h2
    refine ⟨fun p => p.elim0, fun p => p.elim0, fun i => decide (c1 i = 1),
      fun j => decide (c2 j = 1), fun i j => ?_⟩
    have hi : c1 i < 2 := lt_of_lt_of_le (h1 i) ((min_le_right _ _).trans (by norm_num))
    have hj : c2 j < 2 := lt_of_lt_of_le (h2 j) ((min_le_right _ _).trans (by norm_num))
    simp only [List.finRange_zero, List.foldl_nil]
    constructor
    · intro e w
      rw [e]
    · intro hw
      have h3 := hw (fun p => p.elim0)
      rw [decide_eq_decide] at h3
      omega
  | succ L ih =>
    intro c1 c2 h1 h2
    obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ (2 ^ L) := ⟨_, rfl⟩
    have hMM : 2 ^ (2 ^ (L + 1)) = M * M := by rw [hM, pow_succ, pow_mul, sq]
    rw [hMM] at h1 h2
    rw [← hM] at ih
    have hMpos : 0 < M := by rw [hM]; positivity
    obtain ⟨m, hm⟩ : ∃ m, m = min n M := ⟨_, rfl⟩
    have hm0 : 0 < m := by rw [hm]; exact lt_min (by omega) hMpos
    have hmn : m ≤ n := by rw [hm]; exact min_le_left _ _
    have hmM : m ≤ M := by rw [hm]; exact min_le_right _ _
    have hnn : n ≤ n * n := Nat.le_mul_self n
    have hsq : ∀ x, x < min (n * n) (M * M) → x < m * m := by
      intro x hx
      rcases le_total n M with h | h
      · have e : m = n := by rw [hm]; exact min_eq_left h
        rw [e]; exact lt_of_lt_of_le hx (min_le_left _ _)
      · have e : m = M := by rw [hm]; exact min_eq_right h
        rw [e]; exact lt_of_lt_of_le hx (min_le_right _ _)
    obtain ⟨s0, t0, f0, g0, H0⟩ := ih (fun q => min q.val (m - 1)) (fun q => min q.val (m - 1))
      (fun q => lt_of_le_of_lt (Nat.min_le_right _ _) (lt_min (by omega) (by omega)))
      (fun q => lt_of_le_of_lt (Nat.min_le_right _ _) (lt_min (by omega) (by omega)))
    refine ⟨Fin.cons (fun q b => k_pick n m (c1 q) hn b) s0,
      Fin.cons (fun q b => k_pick n m (c2 q) hn b) t0, f0, g0, fun i j => ?_⟩
    simp only [k_run_cons]
    constructor
    · intro e w
      rw [e]
      exact (H0 (k_pick n m (c2 j) hn (w 0)) (k_pick n m (c2 j) hn (w 0))).1 rfl
        (fun p => w p.succ)
    · intro hw
      have e0 : ∀ b : Bool, min (k_pick n m (c1 i) hn b).val (m - 1) =
          min (k_pick n m (c2 j) hn b).val (m - 1) := by
        intro b
        apply (H0 _ _).2
        intro v
        have h3 := hw (Fin.cons b v)
        simpa only [Fin.cons_zero, Fin.cons_succ] using h3
      have ef : min (min (c1 i / m) (n - 1)) (m - 1) = min (min (c2 j / m) (n - 1)) (m - 1) :=
        e0 false
      have et : min (min (c1 i % m) (n - 1)) (m - 1) = min (min (c2 j % m) (n - 1)) (m - 1) :=
        e0 true
      have hx := hsq _ (h1 i)
      have hy := hsq _ (h2 j)
      have hxd : c1 i / m < m := (Nat.div_lt_iff_lt_mul hm0).2 hx
      have hyd : c2 j / m < m := (Nat.div_lt_iff_lt_mul hm0).2 hy
      have hxm : c1 i % m < m := Nat.mod_lt _ hm0
      have hym : c2 j % m < m := Nat.mod_lt _ hm0
      have e1 : c1 i / m = c2 j / m := by omega
      have e2 : c1 i % m = c2 j % m := by omega
      calc c1 i = m * (c1 i / m) + c1 i % m := (Nat.div_add_mod _ _).symm
        _ = m * (c2 j / m) + c2 j % m := by rw [e1, e2]
        _ = c2 j := Nat.div_add_mod _ _
theorem h_pool (n len : ℕ) (hn : 2 ≤ n) (a b : Fin n → ℕ)
    (hcard : ((Finset.univ.image a) ∪ (Finset.univ.image b)).card ≤ 2^(2^len)) :
    ∃ (s t : Fin len → Fin n → Bool → Fin n) (f g : Fin n → Bool), ∀ i j,
      a i = b j ↔ ∀ w : Fin len → Bool,
        f ((List.finRange len).foldl (fun state pos => s pos state (w pos)) i) =
        g ((List.finRange len).foldl (fun state pos => t pos state (w pos)) j) := by
  obtain ⟨c, hc1, hc2⟩ := k_idx ((Finset.univ.image a) ∪ (Finset.univ.image b))
  have ha : ∀ i, a i ∈ (Finset.univ.image a) ∪ (Finset.univ.image b) := fun i =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ i))
  have hb : ∀ j, b j ∈ (Finset.univ.image a) ∪ (Finset.univ.image b) := fun j =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ j))
  have hA : (Finset.univ.image a).card ≤ n := le_trans Finset.card_image_le (by simp)
  have hB : (Finset.univ.image b).card ≤ n := le_trans Finset.card_image_le (by simp)
  have hU := Finset.card_union_le (Finset.univ.image a) (Finset.univ.image b)
  have h2n : 2 * n ≤ n * n := Nat.mul_le_mul hn (le_refl n)
  have hbd : ∀ x ∈ (Finset.univ.image a) ∪ (Finset.univ.image b),
      c x < min (n * n) (2 ^ (2 ^ len)) := fun x hx =>
    lt_min (by have h3 := hc1 x hx; omega) (lt_of_lt_of_le (hc1 x hx) hcard)
  obtain ⟨s, t, f, g, H⟩ := k_gen n hn len (fun i => c (a i)) (fun j => c (b j))
    (fun i => hbd _ (ha i)) (fun j => hbd _ (hb j))
  refine ⟨s, t, f, g, fun i j => Iff.trans ?_ (H i j)⟩
  exact ⟨fun e => congrArg c e, fun e => hc2 _ (ha i) _ (hb j) e⟩
def s_e1 (n : ℕ) (β : Type) :
    {f : Fin (n+1) → β // Function.Surjective f} ≃
      {x : β × (Fin n → β) // ∀ b, b ≠ x.1 → ∃ i, x.2 i = b} where
  toFun f := ⟨(f.1 0, Fin.tail f.1), fun b hb => by
    obtain ⟨j, hj⟩ := f.2 b
    induction j using Fin.cases with
    | zero => exact absurd hj.symm hb
    | succ i => exact ⟨i, hj⟩⟩
  invFun x := ⟨Fin.cons x.1.1 x.1.2, fun b => by
    by_cases hb : b = x.1.1
    · exact ⟨0, by rw [Fin.cons_zero]; exact hb.symm⟩
    · obtain ⟨i, hi⟩ := x.2 b hb
      exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩⟩
  left_inv f := Subtype.ext (Fin.cons_self_tail f.1)
  right_inv x := by ext <;> simp
theorem s_step (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Fintype.card {f : Fin (n+1) → β // Function.Surjective f} =
      ∑ a : β, Fintype.card {g : Fin n → β // ∀ b, b ≠ a → ∃ i, g i = b} := by
  rw [Fintype.card_congr ((s_e1 n β).trans (Equiv.subtypeProdEquivSigmaSubtype
    (fun (a : β) (g : Fin n → β) => ∀ b, b ≠ a → ∃ i, g i = b)))]
  exact Fintype.card_sigma
theorem s_split (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] (a : β) :
    Fintype.card {g : Fin n → β // ∀ b, b ≠ a → ∃ i, g i = b} =
      Fintype.card {g : Fin n → β // Function.Surjective g} +
      Fintype.card {g : Fin n → {b // b ≠ a} // Function.Surjective g} := by
  rw [← Fintype.card_congr (Equiv.sumCompl
    (fun g : {g : Fin n → β // ∀ b, b ≠ a → ∃ i, g i = b} => ∃ i, g.1 i = a)), Fintype.card_sum]
  congr 1
  · exact Fintype.card_congr
      { toFun := fun g => ⟨g.1.1, fun b => by
          by_cases hb : b = a
          · rw [hb]; exact g.2
          · exact g.1.2 b hb⟩
        invFun := fun g => ⟨⟨g.1, fun b _ => g.2 b⟩, g.2 a⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  · exact Fintype.card_congr
      { toFun := fun g => ⟨fun i => ⟨g.1.1 i, fun h => g.2 ⟨i, h⟩⟩, fun b => by
          obtain ⟨i, hi⟩ := g.1.2 b.1 b.2
          exact ⟨i, Subtype.ext hi⟩⟩
        invFun := fun g => ⟨⟨fun i => (g.1 i).1, fun b hb => by
          obtain ⟨i, hi⟩ := g.2 ⟨b, hb⟩
          exact ⟨i, congrArg Subtype.val hi⟩⟩, fun h => by
          obtain ⟨i, hi⟩ := h
          exact (g.1 i).2 hi⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
theorem s_card_ne (β : Type) [Fintype β] [DecidableEq β] (a : β) :
    Fintype.card {b // b ≠ a} = Fintype.card β - 1 := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ]
theorem s_base (β : Type) [Fintype β] [DecidableEq β] :
    Fintype.card {f : Fin 0 → β // Function.Surjective f} =
      (Fintype.card β).factorial * Nat.stirlingSecond 0 (Fintype.card β) := by
  cases h : Fintype.card β with
  | zero =>
    simp only [Nat.stirlingSecond_zero, Nat.factorial_zero, mul_one]
    rw [Fintype.card_eq_one_iff]
    haveI : IsEmpty β := Fintype.card_eq_zero_iff.mp h
    exact ⟨⟨Fin.elim0, fun b => isEmptyElim b⟩, fun y => Subtype.ext (funext fun i => Fin.elim0 i)⟩
  | succ k =>
    rw [Nat.stirlingSecond_zero_succ, mul_zero, Fintype.card_eq_zero_iff]
    obtain ⟨b⟩ : Nonempty β := Fintype.card_pos_iff.mp (by omega)
    exact ⟨fun f => by
      obtain ⟨i, _⟩ := f.2 b
      exact Fin.elim0 i⟩
theorem s_gen (n : ℕ) : ∀ (β : Type) [Fintype β] [DecidableEq β],
    Fintype.card {f : Fin n → β // Function.Surjective f} =
      (Fintype.card β).factorial * Nat.stirlingSecond n (Fintype.card β) := by
  induction n with
  | zero => intro β _ _; exact s_base β
  | succ n ih =>
    intro β _ _
    have key : ∀ a : β, Fintype.card {g : Fin n → β // ∀ b, b ≠ a → ∃ i, g i = b} =
        (Fintype.card β).factorial * Nat.stirlingSecond n (Fintype.card β) +
        (Fintype.card β - 1).factorial * Nat.stirlingSecond n (Fintype.card β - 1) := by
      intro a
      rw [s_split n β a, ih β, ih {b // b ≠ a}, s_card_ne β a]
    rw [s_step n β]
    simp only [key, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    cases h : Fintype.card β with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      ring
theorem h_surj (n k : ℕ) :
    Fintype.card {f : Fin n → Fin k // Function.Surjective f} = k.factorial * Nat.stirlingSecond n k := by
  rw [s_gen n (Fin k), Fintype.card_fin]
def f_Phi {n u : ℕ} (α β : Fin n → Option (Fin u)) (i p : Fin n) : Bool :=
  decide (∃ c, α i = some c ∧ β p = some c)
def f_Lab {n u : ℕ} (β : Fin n → Option (Fin u)) (c : Fin u) (p : Fin n) : Bool :=
  decide (β p = some c)
def f_A (n u a : ℕ) : Finset (Fin n → Option (Fin u)) :=
  Finset.univ.filter (fun α => (∀ c, ∃ i, α i = some c) ∧ ((∃ i, α i = none) ↔ a = 1))
def f_F (n u a b : ℕ) : Finset (Fin n → Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun R =>
      (∀ i j p q, R i p = true → R j p = true → R j q = true → R i q = true) ∧
      ((Finset.univ.image R).erase (fun _ => false)).card = u ∧
      (decide (∃ i, ∀ p, R i p = false)).toNat = a ∧
      (decide (∃ p, ∀ i, R i p = false)).toNat = b)
theorem f_toNat {P : Prop} [Decidable P] {a : ℕ} (ha : a < 2) (h : P ↔ a = 1) :
    (decide P).toNat = a := by
  by_cases hP : P
  · simp only [decide_eq_true hP, Bool.toNat_true]
    exact (h.mp hP).symm
  · simp only [decide_eq_false hP, Bool.toNat_false]
    have : a ≠ 1 := fun e => hP (h.mpr e)
    omega
theorem f_ofNat {P : Prop} [Decidable P] {a : ℕ} (h : (decide P).toNat = a) : P ↔ a = 1 := by
  by_cases hP : P
  · simp only [decide_eq_true hP, Bool.toNat_true] at h
    exact ⟨fun _ => h.symm, fun _ => hP⟩
  · simp only [decide_eq_false hP, Bool.toNat_false] at h
    exact ⟨fun hp => absurd hp hP, fun e => absurd (h.trans e) (by decide)⟩
theorem f_rowEq {n : ℕ} (R : Fin n → Fin n → Bool)
    (hR : ∀ i j p q, R i p = true → R j p = true → R j q = true → R i q = true)
    {i j p : Fin n} (h1 : R i p = true) (h2 : R j p = true) : R i = R j := by
  funext q
  cases h : R j q
  · cases h' : R i q
    · rfl
    · exact absurd (hR j i p q h2 h1 h') (by simp [h])
  · exact hR i j p q h1 h2 h
theorem f_Phi_some {n u : ℕ} {α β : Fin n → Option (Fin u)} {i : Fin n} {c : Fin u}
    (h : α i = some c) : f_Phi α β i = f_Lab β c := by
  funext p
  simp [f_Phi, f_Lab, h]
theorem f_Phi_none {n u : ℕ} {α β : Fin n → Option (Fin u)} {i : Fin n}
    (h : α i = none) : f_Phi α β i = fun _ => false := by
  funext p
  simp [f_Phi, h]
theorem f_Lab_ne {n u : ℕ} {β : Fin n → Option (Fin u)} (hβ : ∀ c, ∃ p, β p = some c)
    (c : Fin u) : f_Lab β c ≠ fun _ => false := by
  intro h
  obtain ⟨p, hp⟩ := hβ c
  have := congrFun h p
  simp [f_Lab, hp] at this
theorem f_Lab_inj {n u : ℕ} {β : Fin n → Option (Fin u)} (hβ : ∀ c, ∃ p, β p = some c) :
    Function.Injective (f_Lab β) := by
  intro c c' h
  obtain ⟨p, hp⟩ := hβ c
  have h2 : f_Lab β c' p = true := by rw [← h]; simp [f_Lab, hp]
  simp only [f_Lab, hp, decide_eq_true_eq, Option.some.injEq] at h2
  exact h2
theorem f_img {n u : ℕ} {α β : Fin n → Option (Fin u)} (hα : ∀ c, ∃ i, α i = some c)
    (hβ : ∀ c, ∃ p, β p = some c) :
    Finset.univ.image (f_Lab β) = (Finset.univ.image (f_Phi α β)).erase (fun _ => false) := by
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨i, hi⟩ := hα c
    exact ⟨f_Lab_ne hβ c, i, f_Phi_some hi⟩
  · rintro ⟨hr, i, rfl⟩
    cases h : α i with
    | none => exact absurd (f_Phi_none h) hr
    | some c => exact ⟨c, (f_Phi_some h).symm⟩
theorem f_rect {n u : ℕ} (α β : Fin n → Option (Fin u)) :
    ∀ i j p q, f_Phi α β i p = true → f_Phi α β j p = true → f_Phi α β j q = true →
      f_Phi α β i q = true := by
  intro i j p q h1 h2 h3
  simp only [f_Phi, decide_eq_true_eq] at h1 h2 h3 ⊢
  obtain ⟨c, h1a, h1b⟩ := h1
  obtain ⟨c', h2a, h2b⟩ := h2
  obtain ⟨c'', h3a, h3b⟩ := h3
  have e1 : c = c' := Option.some.inj (h1b.symm.trans h2b)
  have e2 : c' = c'' := Option.some.inj (h2a.symm.trans h3a)
  subst e1 e2
  exact ⟨c, h1a, h3b⟩
theorem f_zrow {n u : ℕ} {α β : Fin n → Option (Fin u)} (hβ : ∀ c, ∃ p, β p = some c)
    (i : Fin n) : (∀ p, f_Phi α β i p = false) ↔ α i = none := by
  constructor
  · intro h
    cases hi : α i with
    | none => rfl
    | some c =>
      obtain ⟨p, hp⟩ := hβ c
      have := h p
      simp [f_Phi, hi, hp] at this
  · intro h p
    simp [f_Phi, h]
theorem f_zcol {n u : ℕ} {α β : Fin n → Option (Fin u)} (hα : ∀ c, ∃ i, α i = some c)
    (p : Fin n) : (∀ i, f_Phi α β i p = false) ↔ β p = none := by
  constructor
  · intro h
    cases hp : β p with
    | none => rfl
    | some c =>
      obtain ⟨i, hi⟩ := hα c
      have := h i
      simp [f_Phi, hi, hp] at this
  · intro h i
    simp [f_Phi, h]
theorem f_A_hit {n u a : ℕ} {α : Fin n → Option (Fin u)} (h : α ∈ f_A n u a) :
    ∀ c, ∃ i, α i = some c := by
  simp only [f_A, Finset.mem_filter] at h
  exact h.2.1
theorem f_cardS {n u a b : ℕ} {R : Fin n → Fin n → Bool} (hR : R ∈ f_F n u a b) :
    ((Finset.univ.image R).erase (fun _ => false)).card = u := by
  simp only [f_F, Finset.mem_filter] at hR
  exact hR.2.2.1
theorem f_memF {n u a b : ℕ} (ha : a < 2) (hb : b < 2) {α β : Fin n → Option (Fin u)}
    (hα : α ∈ f_A n u a) (hβ : β ∈ f_A n u b) : f_Phi α β ∈ f_F n u a b := by
  simp only [f_A, Finset.mem_filter, Finset.mem_univ, true_and] at hα hβ
  simp only [f_F, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨f_rect α β, ?_, ?_, ?_⟩
  · rw [← f_img hα.1 hβ.1, Finset.card_image_of_injective _ (f_Lab_inj hβ.1)]
    simp
  · apply f_toNat ha
    rw [← hα.2]
    exact exists_congr (fun i => f_zrow hβ.1 i)
  · apply f_toNat hb
    rw [← hβ.2]
    exact exists_congr (fun p => f_zcol hα.1 p)
theorem f_alpha_eq {n u : ℕ} {α β : Fin n → Option (Fin u)} (hβ : ∀ c, ∃ p, β p = some c)
    (i : Fin n) (c : Fin u) : α i = some c ↔ f_Phi α β i = f_Lab β c := by
  refine ⟨f_Phi_some, fun h => ?_⟩
  obtain ⟨p, hp⟩ := hβ c
  have h1 : f_Phi α β i p = true := by rw [h]; simp [f_Lab, hp]
  simp only [f_Phi, decide_eq_true_eq] at h1
  obtain ⟨c', h2, h3⟩ := h1
  rw [hp] at h3
  exact h2.trans h3.symm
theorem f_inj {n u : ℕ} {α β α' β' : Fin n → Option (Fin u)}
    (hβ : ∀ c, ∃ p, β p = some c)
    (h1 : f_Phi α β = f_Phi α' β') (h2 : f_Lab β = f_Lab β') : α = α' ∧ β = β' := by
  have hb : β = β' := by
    funext p
    apply Option.ext
    intro c
    have := congrFun (congrFun h2 c) p
    simp only [f_Lab, decide_eq_decide] at this
    exact this
  subst hb
  refine ⟨?_, rfl⟩
  funext i
  apply Option.ext
  intro c
  rw [f_alpha_eq (α := α) hβ i c, f_alpha_eq (α := α') hβ i c, h1]
theorem f_exOpt {X : Type} {u : ℕ} (P : X → Fin u → Prop)
    (hP : ∀ x c c', P x c → P x c' → c = c') :
    ∃ γ : X → Option (Fin u), ∀ x c, γ x = some c ↔ P x c := by
  classical
  refine ⟨fun x => if h : ∃ c, P x c then some h.choose else none, fun x c => ?_⟩
  dsimp only
  split
  · rename_i h
    constructor
    · intro e
      rw [← Option.some.inj e]
      exact h.choose_spec
    · intro hc
      rw [hP x _ _ h.choose_spec hc]
  · rename_i h
    exact ⟨fun e => (by cases e), fun hc => absurd ⟨c, hc⟩ h⟩
theorem f_G {X : Type} [DecidableEq X] [Fintype X] {u : ℕ} (S : Finset X) (hS : S.card = u) :
    ((Finset.univ : Finset (Fin u → X)).filter (fun L => Finset.univ.image L = S)).card =
      u.factorial := by
  have injOf : ∀ L : Fin u → X, Finset.univ.image L = S → Function.Injective L := by
    intro L hL x y hxy
    have h1 : (Finset.univ.image L).card = (Finset.univ : Finset (Fin u)).card := by
      rw [hL, hS]; simp
    exact Finset.card_image_iff.mp h1 (Finset.mem_coe.mpr (Finset.mem_univ x))
      (Finset.mem_coe.mpr (Finset.mem_univ y)) hxy
  obtain ⟨g, hg⟩ : ∃ g : Fin u → X, Finset.univ.image g = S := by
    let e : S ≃ Fin u := Fintype.equivFinOfCardEq (by simp [hS])
    refine ⟨fun c => (e.symm c : X), ?_⟩
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, rfl⟩
      exact (e.symm c).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
  have ginj : Function.Injective g := injOf g hg
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin u))).card = u.factorial := by
    simp [Fintype.card_perm]
  rw [← hperm]
  symm
  refine Finset.card_bij (fun σ _ => fun c => g (σ c)) ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hg]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨σ c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨σ.symm c, by simp⟩
  · intro σ _ σ' _ h
    exact Equiv.ext (fun c => ginj (congrFun h c))
  · intro L hL
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL
    have hex : ∀ c, ∃ d, g d = L c := by
      intro c
      have : L c ∈ Finset.univ.image g := by
        rw [hg, ← hL]
        exact Finset.mem_image_of_mem L (Finset.mem_univ c)
      simpa using this
    choose τ hτ using hex
    have τinj : Function.Injective τ := by
      intro x y hxy
      apply injOf L hL
      rw [← hτ x, ← hτ y, hxy]
    refine ⟨Equiv.ofBijective τ (Finite.injective_iff_bijective.mp τinj), Finset.mem_univ _, ?_⟩
    funext c
    exact hτ c
theorem f_surj_aux {n u a b : ℕ} (R : Fin n → Fin n → Bool) (L : Fin u → Fin n → Bool)
    (hR : R ∈ f_F n u a b)
    (hL : Finset.univ.image L = (Finset.univ.image R).erase (fun _ => false)) :
    ∃ α β, α ∈ f_A n u a ∧ β ∈ f_A n u b ∧ f_Phi α β = R ∧ f_Lab β = L := by
  simp only [f_F, Finset.mem_filter, Finset.mem_univ, true_and] at hR
  obtain ⟨hrect, hcard, hza, hzb⟩ := hR
  have Linj : Function.Injective L := by
    intro x y hxy
    have h1 : (Finset.univ.image L).card = (Finset.univ : Finset (Fin u)).card := by
      rw [hL, hcard]; simp
    exact Finset.card_image_iff.mp h1 (Finset.mem_coe.mpr (Finset.mem_univ x))
      (Finset.mem_coe.mpr (Finset.mem_univ y)) hxy
  have memS : ∀ r, (∃ c, L c = r) ↔ (r ≠ fun _ => false) ∧ ∃ i, R i = r := by
    intro r
    have := Finset.ext_iff.mp hL r
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase] at this
    exact this
  have ne0 : ∀ (r : Fin n → Bool) (p : Fin n), r p = true → r ≠ fun _ => false := by
    intro r p h e
    rw [e] at h
    exact Bool.false_ne_true h
  have rowL : ∀ i, R i ≠ (fun _ => false) → ∃ c, L c = R i := by
    intro i h
    exact (memS (R i)).mpr ⟨h, i, rfl⟩
  have Lrow : ∀ c, ∃ i, R i = L c := fun c => ((memS (L c)).mp ⟨c, rfl⟩).2
  have Lne : ∀ c, L c ≠ fun _ => false := fun c => ((memS (L c)).mp ⟨c, rfl⟩).1
  have uniq : ∀ p c c', L c p = true → L c' p = true → c = c' := by
    intro p c c' h1 h2
    obtain ⟨i, hi⟩ := Lrow c
    obtain ⟨j, hj⟩ := Lrow c'
    apply Linj
    rw [← hi, ← hj]
    rw [← hi] at h1
    rw [← hj] at h2
    exact f_rowEq R hrect h1 h2
  obtain ⟨α, hα⟩ : ∃ α : Fin n → Option (Fin u), ∀ i c, α i = some c ↔ L c = R i :=
    f_exOpt _ (fun i c c' (h1 : L c = R i) (h2 : L c' = R i) => Linj (h1.trans h2.symm))
  obtain ⟨β, hβ⟩ : ∃ β : Fin n → Option (Fin u), ∀ p c, β p = some c ↔ L c p = true :=
    f_exOpt _ uniq
  have hαn : ∀ i, α i = none ↔ R i = fun _ => false := by
    intro i
    cases h : α i with
    | none =>
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      by_contra hne
      obtain ⟨c, hc⟩ := rowL i hne
      have := (hα i c).mpr hc
      rw [h] at this
      cases this
    | some c =>
      refine ⟨fun e => (by cases e), fun hz => ?_⟩
      have := (hα i c).mp h
      exact absurd (this.trans hz) (Lne c)
  have hβn : ∀ p, β p = none ↔ ∀ i, R i p = false := by
    intro p
    cases h : β p with
    | none =>
      refine ⟨fun _ i => ?_, fun _ => rfl⟩
      cases hr : R i p
      · rfl
      · obtain ⟨c, hc⟩ := rowL i (ne0 _ p hr)
        have := (hβ p c).mpr (by rw [hc]; exact hr)
        rw [h] at this
        cases this
    | some c =>
      refine ⟨fun e => (by cases e), fun hz => ?_⟩
      have h1 := (hβ p c).mp h
      obtain ⟨i, hi⟩ := Lrow c
      have h2 := hz i
      rw [hi, h1] at h2
      cases h2
  refine ⟨α, β, ?_, ?_, ?_, ?_⟩
  · simp only [f_A, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun c => ?_, ?_⟩
    · obtain ⟨i, hi⟩ := Lrow c
      exact ⟨i, (hα i c).mpr hi.symm⟩
    · rw [← f_ofNat hza]
      exact exists_congr (fun i => (hαn i).trans ⟨fun h p => by rw [h], fun h => funext h⟩)
  · simp only [f_A, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun c => ?_, ?_⟩
    · have : ∃ p, L c p = true := by
        by_contra hno
        apply Lne c
        funext p
        cases h : L c p
        · rfl
        · exact absurd ⟨p, h⟩ hno
      obtain ⟨p, hp⟩ := this
      exact ⟨p, (hβ p c).mpr hp⟩
    · rw [← f_ofNat hzb]
      exact exists_congr (fun p => hβn p)
  · funext i p
    simp only [f_Phi, hα, hβ]
    cases hr : R i p
    · simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro c hc
      rw [hc, hr]
      exact Bool.false_ne_true
    · simp only [decide_eq_true_eq]
      obtain ⟨c, hc⟩ := rowL i (ne0 _ p hr)
      exact ⟨c, hc, by rw [hc]; exact hr⟩
  · funext c p
    simp [f_Lab, hβ]
theorem f_cardA (n u a : ℕ) (ha : a < 2) :
    (f_A n u a).card = u.factorial *
      (if a = 0 then Nat.stirlingSecond n u else
        Nat.stirlingSecond (n+1) (u+1) - Nat.stirlingSecond n u) := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · rw [ite_eq_left rfl, ← h_surj n u, Fintype.card_subtype]
    symm
    refine Finset.card_bij (fun f _ => fun i => some (f i)) ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      simp only [f_A, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun c => ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hf c
        exact ⟨i, by rw [hi]⟩
      · simp
    · intro f _ g _ h
      funext i
      exact Option.some.inj (congrFun h i)
    · intro α hα
      simp only [f_A, Finset.mem_filter, Finset.mem_univ, true_and] at hα
      have hne : ∀ i, (α i).isSome = true := by
        intro i
        cases h : α i with
        | none => exact False.elim (by have := hα.2.mp ⟨i, h⟩; omega)
        | some c => rfl
      refine ⟨fun i => (α i).get (hne i), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro c
        obtain ⟨i, hi⟩ := hα.1 c
        exact ⟨i, Option.some.inj ((Option.some_get (hne i)).trans hi)⟩
      · funext i
        exact Option.some_get (hne i)
  · rw [ite_eq_right one_ne_zero, Nat.stirlingSecond_succ_succ, Nat.add_sub_cancel]
    have key : (f_A n u 1).card =
        Fintype.card {f : Fin n → Fin (u+1) // Function.Surjective f} := by
      rw [Fintype.card_subtype]
      symm
      refine Finset.card_bij (fun f _ => fun i => finSuccEquiv u (f i)) ?_ ?_ ?_
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        simp only [f_A, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun c => ?_, ?_⟩
        · obtain ⟨i, hi⟩ := hf ((finSuccEquiv u).symm (some c))
          exact ⟨i, by simp [hi]⟩
        · obtain ⟨i, hi⟩ := hf ((finSuccEquiv u).symm none)
          exact iff_of_true ⟨i, by simp [hi]⟩ trivial
      · intro f _ g _ h
        funext i
        exact (finSuccEquiv u).injective (congrFun h i)
      · intro α hα
        simp only [f_A, Finset.mem_filter, Finset.mem_univ, true_and] at hα
        refine ⟨fun i => (finSuccEquiv u).symm (α i), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro y
          cases hy : finSuccEquiv u y with
          | none =>
            obtain ⟨i, hi⟩ := hα.2.mpr trivial
            exact ⟨i, by simp only [hi]; exact (Equiv.symm_apply_eq _).mpr hy.symm⟩
          | some c =>
            obtain ⟨i, hi⟩ := hα.1 c
            exact ⟨i, by simp only [hi]; exact (Equiv.symm_apply_eq _).mpr hy.symm⟩
        · funext i
          simp
    rw [key, h_surj n (u+1), Nat.factorial_succ]
    ring
theorem h_fiber (n u a b : ℕ) (ha : a < 2) (hb : b < 2) :
    ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun R =>
      (∀ i j p q, R i p = true → R j p = true → R j q = true → R i q = true) ∧
      ((Finset.univ.image R).erase (fun _ => false)).card = u ∧
      (decide (∃ i, ∀ p, R i p = false)).toNat = a ∧
      (decide (∃ p, ∀ i, R i p = false)).toNat = b)).card =
    u.factorial *
      (if a = 0 then Nat.stirlingSecond n u else Nat.stirlingSecond (n+1) (u+1) - Nat.stirlingSecond n u) *
      (if b = 0 then Nat.stirlingSecond n u else Nat.stirlingSecond (n+1) (u+1) - Nat.stirlingSecond n u) := by
  change (f_F n u a b).card = _
  have hT : (f_A n u a ×ˢ f_A n u b).card = (f_F n u a b).card * u.factorial := by
    have h1 : (f_A n u a ×ˢ f_A n u b).card =
        ((f_F n u a b).sigma (fun R => (Finset.univ : Finset (Fin u → Fin n → Bool)).filter
          (fun L => Finset.univ.image L = (Finset.univ.image R).erase (fun _ => false)))).card := by
      refine Finset.card_bij (fun t _ => (⟨f_Phi t.1 t.2, f_Lab t.2⟩ :
        Σ _ : (Fin n → Fin n → Bool), (Fin u → Fin n → Bool))) ?_ ?_ ?_
      · rintro ⟨α, β⟩ ht
        simp only [Finset.mem_product] at ht
        simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨f_memF ha hb ht.1 ht.2, f_img (f_A_hit ht.1) (f_A_hit ht.2)⟩
      · rintro ⟨α, β⟩ ht ⟨α', β'⟩ ht' h
        simp only [Finset.mem_product] at ht
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
        obtain ⟨e1, e2⟩ := f_inj (f_A_hit ht.2) h.1 h.2
        rw [e1, e2]
      · rintro ⟨R, L⟩ hRL
        simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hRL
        obtain ⟨α, β, hα, hβ, e1, e2⟩ := f_surj_aux R L hRL.1 hRL.2
        exact ⟨(α, β), Finset.mem_product.mpr ⟨hα, hβ⟩, by simp only [e1, e2]⟩
    rw [h1, Finset.card_sigma]
    exact Finset.sum_const_nat (fun R hR => f_G _ (f_cardS hR))
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos u)
  rw [← hT, Finset.card_product, f_cardA n u a ha, f_cardA n u b hb]
  ring
theorem n_tf {b : Bool} (h1 : b = true) (h2 : b = false) : False := by
  rw [h1] at h2
  exact Bool.noConfusion h2
theorem n_nb {α : Type} {P : α → Bool} (h : ¬∃ x, P x = true) : ∀ x, P x = false := by
  intro x
  cases hx : P x
  · rfl
  · exact (h ⟨x, hx⟩).elim
theorem n_ite (P : Prop) [Decidable P] (x : ℕ) :
    (if P then ({x} : Finset ℕ) else ∅).card ≤ (decide P).toNat := by
  by_cases h : P <;> simp [h]
theorem n_fwd {n : ℕ} {X : Type} [Fintype X] [DecidableEq X] (R : Fin n → Fin n → Bool)
    (A B : Fin n → X) (hR : ∀ i j, R i j = true ↔ A i = B j) :
    (∀ i j p q, R i p = true → R j p = true → R j q = true → R i q = true) ∧
    ((Finset.univ.image R).erase (fun _ => false)).card +
      (decide (∃ i, ∀ p, R i p = false)).toNat +
      (decide (∃ p, ∀ i, R i p = false)).toNat ≤ Fintype.card X := by
  refine ⟨fun i j p q h1 h2 h3 => (hR i q).2 ?_, ?_⟩
  · rw [(hR i p).1 h1, ← (hR j p).1 h2, (hR j q).1 h3]
  have hsub : (Finset.univ.image R).erase (fun _ => false) ⊆
      ((Finset.univ.image A) ∩ (Finset.univ.image B)).image
        (fun x => fun j => decide (x = B j)) := by
    intro r hr
    rw [Finset.mem_erase, Finset.mem_image] at hr
    obtain ⟨hr0, i, -, rfl⟩ := hr
    have hp : ∃ p, R i p = true := by
      by_contra hc
      exact hr0 (funext (n_nb hc))
    obtain ⟨p, hp⟩ := hp
    rw [Finset.mem_image]
    refine ⟨A i, Finset.mem_inter.2 ⟨Finset.mem_image_of_mem A (Finset.mem_univ i), ?_⟩, ?_⟩
    · rw [(hR i p).1 hp]
      exact Finset.mem_image_of_mem B (Finset.mem_univ p)
    · funext j
      show decide (A i = B j) = R i j
      by_cases hj : A i = B j
      · rw [decide_eq_true hj, (hR i j).2 hj]
      · rw [decide_eq_false hj]
        cases h : R i j
        · rfl
        · exact (hj ((hR i j).1 h)).elim
  have h1 := le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have h2 : (decide (∃ i, ∀ p, R i p = false)).toNat ≤
      ((Finset.univ.image A) \ (Finset.univ.image B)).card := by
    by_cases h : ∃ i, ∀ p, R i p = false
    · rw [decide_eq_true h, Bool.toNat_true]
      obtain ⟨i, hi⟩ := h
      have hne : ((Finset.univ.image A) \ (Finset.univ.image B)).Nonempty := by
        refine ⟨A i, Finset.mem_sdiff.2 ⟨Finset.mem_image_of_mem A (Finset.mem_univ i), ?_⟩⟩
        rw [Finset.mem_image]
        rintro ⟨p, -, hp⟩
        exact n_tf ((hR i p).2 hp.symm) (hi p)
      have := Finset.card_pos.2 hne
      omega
    · rw [decide_eq_false h, Bool.toNat_false]
      exact Nat.zero_le _
  have h3 : (decide (∃ p, ∀ i, R i p = false)).toNat ≤
      ((Finset.univ.image B) \ (Finset.univ.image A)).card := by
    by_cases h : ∃ p, ∀ i, R i p = false
    · rw [decide_eq_true h, Bool.toNat_true]
      obtain ⟨p, hp⟩ := h
      have hne : ((Finset.univ.image B) \ (Finset.univ.image A)).Nonempty := by
        refine ⟨B p, Finset.mem_sdiff.2 ⟨Finset.mem_image_of_mem B (Finset.mem_univ p), ?_⟩⟩
        rw [Finset.mem_image]
        rintro ⟨i, -, hi⟩
        exact n_tf ((hR i p).2 hi) (hp i)
      have := Finset.card_pos.2 hne
      omega
    · rw [decide_eq_false h, Bool.toNat_false]
      exact Nat.zero_le _
  have h4 := Finset.card_sdiff_add_card_inter (Finset.univ.image A) (Finset.univ.image B)
  have h5 := Finset.card_sdiff_add_card (Finset.univ.image B) (Finset.univ.image A)
  have h6 := Finset.card_le_univ ((Finset.univ.image B) ∪ (Finset.univ.image A))
  omega
theorem n_bwd {n : ℕ} (R : Fin n → Fin n → Bool)
    (hrect : ∀ i j p q, R i p = true → R j p = true → R j q = true → R i q = true) :
    ∃ a b : Fin n → ℕ, (∀ i j, R i j = true ↔ a i = b j) ∧
      ((Finset.univ.image a) ∪ (Finset.univ.image b)).card ≤
        ((Finset.univ.image R).erase (fun _ => false)).card +
        (decide (∃ i, ∀ p, R i p = false)).toNat +
        (decide (∃ p, ∀ i, R i p = false)).toNat := by
  obtain ⟨c, hc⟩ := Countable.exists_injective_nat (Fin n → Bool)
  have hrow : ∀ i j p, R i p = true → R j p = true → R i = R j := by
    intro i j p hi hj
    funext q
    rw [Bool.eq_iff_iff]
    exact ⟨fun h => hrect j i p q hj hi h, fun h => hrect i j p q hi hj h⟩
  obtain ⟨a, ha1, ha0⟩ : ∃ a : Fin n → ℕ, (∀ i p, R i p = true → a i = c (R i) + 2) ∧
      (∀ i, (∀ p, R i p = false) → a i = 0) := by
    refine ⟨fun i => if ∃ p, R i p = true then c (R i) + 2 else 0, ?_, ?_⟩
    · intro i p h
      show (if ∃ p, R i p = true then c (R i) + 2 else 0) = c (R i) + 2
      rw [ite_eq_left (show ∃ p, R i p = true from ⟨p, h⟩)]
    · intro i h
      show (if ∃ p, R i p = true then c (R i) + 2 else 0) = 0
      rw [ite_eq_right]
      rintro ⟨p, hp⟩
      exact n_tf hp (h p)
  obtain ⟨b, hb1, hb0⟩ : ∃ b : Fin n → ℕ, (∀ i p, R i p = true → b p = c (R i) + 2) ∧
      (∀ p, (∀ i, R i p = false) → b p = 1) := by
    refine ⟨fun p => if h : ∃ i, R i p = true then c (R (Classical.choose h)) + 2 else 1,
      ?_, ?_⟩
    · intro i p h
      have hex : ∃ i, R i p = true := ⟨i, h⟩
      show (if h : ∃ i, R i p = true then c (R (Classical.choose h)) + 2 else 1) = c (R i) + 2
      rw [dite_eq_left hex, hrow (Classical.choose hex) i p (Classical.choose_spec hex) h]
    · intro p h
      show (if h : ∃ i, R i p = true then c (R (Classical.choose h)) + 2 else 1) = 1
      rw [dite_eq_right]
      rintro ⟨i, hi⟩
      exact n_tf hi (h i)
  refine ⟨a, b, fun i p => ⟨fun h => by rw [ha1 i p h, hb1 i p h], fun heq => ?_⟩, ?_⟩
  · by_cases hi : ∃ q, R i q = true
    · obtain ⟨q, hq⟩ := hi
      rw [ha1 i q hq] at heq
      by_cases hp : ∃ j, R j p = true
      · obtain ⟨j, hj⟩ := hp
        rw [hb1 j p hj] at heq
        rw [hc (show c (R i) = c (R j) by omega)]
        exact hj
      · rw [hb0 p (n_nb hp)] at heq
        omega
    · rw [ha0 i (n_nb hi)] at heq
      by_cases hp : ∃ j, R j p = true
      · obtain ⟨j, hj⟩ := hp
        rw [hb1 j p hj] at heq
        omega
      · rw [hb0 p (n_nb hp)] at heq
        omega
  · have hsub : (Finset.univ.image a) ∪ (Finset.univ.image b) ⊆
        (((Finset.univ.image R).erase (fun _ => false)).image (fun r => c r + 2) ∪
          (if ∃ i, ∀ p, R i p = false then ({0} : Finset ℕ) else ∅)) ∪
          (if ∃ p, ∀ i, R i p = false then ({1} : Finset ℕ) else ∅) := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
      rcases hx with ⟨i, -, rfl⟩ | ⟨p, -, rfl⟩
      · by_cases hi : ∃ q, R i q = true
        · obtain ⟨q, hq⟩ := hi
          rw [ha1 i q hq]
          refine Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image_of_mem (fun r => c r + 2) ?_))
          rw [Finset.mem_erase]
          exact ⟨fun h0 => n_tf hq (congrFun h0 q), Finset.mem_image_of_mem R (Finset.mem_univ i)⟩
        · have hi0 := n_nb hi
          rw [ha0 i hi0]
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          rw [ite_eq_left (show ∃ i, ∀ p, R i p = false from ⟨i, hi0⟩)]
          exact Finset.mem_singleton_self 0
      · by_cases hp : ∃ j, R j p = true
        · obtain ⟨j, hj⟩ := hp
          rw [hb1 j p hj]
          refine Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image_of_mem (fun r => c r + 2) ?_))
          rw [Finset.mem_erase]
          exact ⟨fun h0 => n_tf hj (congrFun h0 p), Finset.mem_image_of_mem R (Finset.mem_univ j)⟩
        · have hp0 := n_nb hp
          rw [hb0 p hp0]
          refine Finset.mem_union_right _ ?_
          rw [ite_eq_left (show ∃ p, ∀ i, R i p = false from ⟨p, hp0⟩)]
          exact Finset.mem_singleton_self 1
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add Finset.card_image_le (n_ite _ 0))) (n_ite _ 1)))
theorem h_char : ∀ n len : ℕ, 2 ≤ n →
  let State := Fin n
  let Word := Fin len → Bool
  let stepRun := fun (t : Fin len → State → Bool → State) (label : State → Bool)
      (q : State) (word : Word) =>
    label ((List.finRange len).foldl (fun state pos => t pos state (word pos)) q)
  let realizable := fun R : State → State → Bool =>
    ∃ (s t : Fin len → State → Bool → State) (f g : State → Bool),
      ∀ i j, R i j = true ↔ ∀ w : Word, stepRun s f i w = stepRun t g j w
  let budget := 2^(2^len)
  let ways := fun (j flag : ℕ) =>
    if flag = 0 then Nat.stirlingSecond n j else
      Nat.stirlingSecond (n+1) (j+1) - Nat.stirlingSecond n j
  (∀ R : State → State → Bool, realizable R ↔
    (∀ i j p q, R i p = true → R j p = true → R j q = true → R i q = true) ∧
    let components := ((Finset.univ.image R).erase (fun _ => false)).card
    let left := (decide (∃ i, ∀ p, R i p = false)).toNat
    let right := (decide (∃ p, ∀ i, R i p = false)).toNat
    components + left + right ≤ budget) := by
  intro n len hn
  dsimp only
  intro R
  constructor
  · rintro ⟨s, t, f, g, h⟩
    have key := n_fwd R
      (fun i w => f ((List.finRange len).foldl (fun state pos => s pos state (w pos)) i))
      (fun j w => g ((List.finRange len).foldl (fun state pos => t pos state (w pos)) j))
      (fun i j => (h i j).trans ⟨fun e => funext e, fun e w => congrFun e w⟩)
    refine ⟨key.1, le_trans key.2 ?_⟩
    simp
  · rintro ⟨hrect, hcard⟩
    obtain ⟨a, b, hab, habc⟩ := n_bwd R hrect
    obtain ⟨s, t, f, g, h⟩ := h_pool n len hn a b (le_trans habc hcard)
    exact ⟨s, t, f, g, fun i j => (hab i j).trans (h i j)⟩
theorem g_comp_le {n : ℕ} (R : Fin n → Fin n → Bool) :
    ((Finset.univ.image R).erase (fun _ => false)).card ≤ n :=
  calc ((Finset.univ.image R).erase (fun _ => false)).card ≤ (Finset.univ.image R).card :=
        Finset.card_erase_le
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp
theorem g_count (n B : ℕ) (P : (Fin n → Fin n → Bool) → Prop)
    (hP : ∀ R, P R ↔ (∀ i j p q, R i p = true → R j p = true → R j q = true → R i q = true) ∧
      ((Finset.univ.image R).erase (fun _ => false)).card + (decide (∃ i, ∀ p, R i p = false)).toNat +
        (decide (∃ p, ∀ i, R i p = false)).toNat ≤ B) :
    Nat.card {R : Fin n → Fin n → Bool // P R} =
    (Finset.range (n+1)).sum (fun u => (Finset.range 2).sum (fun a =>
      (Finset.range 2).sum (fun b =>
        if u+a+b ≤ B then u.factorial *
          (if a = 0 then Nat.stirlingSecond n u else Nat.stirlingSecond (n+1) (u+1) - Nat.stirlingSecond n u) *
          (if b = 0 then Nat.stirlingSecond n u else Nat.stirlingSecond (n+1) (u+1) - Nat.stirlingSecond n u)
        else 0))) := by
  classical
  have h1 : Nat.card {R : Fin n → Fin n → Bool // P R} = (Finset.univ.filter P).card :=
    Nat.subtype_card _ (fun R => by simp)
  rw [h1]
  rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter P)
      (f := fun R : Fin n → Fin n → Bool =>
        (((Finset.univ.image R).erase (fun _ => false)).card,
          (decide (∃ i, ∀ p, R i p = false)).toNat, (decide (∃ p, ∀ i, R i p = false)).toNat))
      (t := Finset.range (n+1) ×ˢ (Finset.range 2 ×ˢ Finset.range 2))
      (fun R _ => by
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
        refine ⟨?_, Bool.toNat_lt _, Bool.toNat_lt _⟩
        have := g_comp_le R
        omega)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
  rw [Finset.mem_range] at ha hb
  rw [← h_fiber n u a b ha hb]
  split_ifs with h
  · congr 1
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, hP]
    constructor
    · rintro ⟨⟨h1, _⟩, h3, h4, h5⟩
      exact ⟨h1, h3, h4, h5⟩
    · rintro ⟨h1, h3, h4, h5⟩
      exact ⟨⟨h1, by omega⟩, h3, h4, h5⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP] at hR
    obtain ⟨_, hR2⟩ := hR
    simp only [Prod.mk.injEq, not_and]
    intro h3 h4 h5
    omega
theorem h_count : ∀ n len : ℕ, 2 ≤ n →
  let State := Fin n
  let Word := Fin len → Bool
  let stepRun := fun (t : Fin len → State → Bool → State) (label : State → Bool)
      (q : State) (word : Word) =>
    label ((List.finRange len).foldl (fun state pos => t pos state (word pos)) q)
  let realizable := fun R : State → State → Bool =>
    ∃ (s t : Fin len → State → Bool → State) (f g : State → Bool),
      ∀ i j, R i j = true ↔ ∀ w : Word, stepRun s f i w = stepRun t g j w
  let budget := 2^(2^len)
  let ways := fun (j flag : ℕ) =>
    if flag = 0 then Nat.stirlingSecond n j else
      Nat.stirlingSecond (n+1) (j+1) - Nat.stirlingSecond n j
  Nat.card {R : State → State → Bool // realizable R} =
    (Finset.range (n+1)).sum (fun u => (Finset.range 2).sum (fun a =>
      (Finset.range 2).sum (fun b =>
        if u+a+b ≤ budget then u.factorial * ways u a * ways u b else 0))) := by
  intro n len hn State Word stepRun realizable budget ways
  exact g_count n budget realizable (h_char n len hn)
end PEqualNP.Outside.L_lib_872
theorem PEqualNP.Outside.L_lib_872 : ∀ n len : ℕ, 2 ≤ n →
  let State := Fin n
  let Word := Fin len → Bool
  let stepRun := fun (t : Fin len → State → Bool → State) (label : State → Bool)
      (q : State) (word : Word) =>
    label ((List.finRange len).foldl (fun state pos => t pos state (word pos)) q)
  let realizable := fun R : State → State → Bool =>
    ∃ (s t : Fin len → State → Bool → State) (f g : State → Bool),
      ∀ i j, R i j = true ↔ ∀ w : Word, stepRun s f i w = stepRun t g j w
  let budget := 2^(2^len)
  let ways := fun (j flag : ℕ) =>
    if flag = 0 then Nat.stirlingSecond n j else
      Nat.stirlingSecond (n+1) (j+1) - Nat.stirlingSecond n j
  (∀ R : State → State → Bool, realizable R ↔
    (∀ i j p q, R i p = true → R j p = true → R j q = true → R i q = true) ∧
    let components := ((Finset.univ.image R).erase (fun _ => false)).card
    let left := (decide (∃ i, ∀ p, R i p = false)).toNat
    let right := (decide (∃ p, ∀ i, R i p = false)).toNat
    components + left + right ≤ budget) ∧
  Nat.card {R : State → State → Bool // realizable R} =
    (Finset.range (n+1)).sum (fun u => (Finset.range 2).sum (fun a =>
      (Finset.range 2).sum (fun b =>
        if u+a+b ≤ budget then u.factorial * ways u a * ways u b else 0))) := by
  intro n len hn State Word stepRun realizable budget ways
  exact ⟨PEqualNP.Outside.L_lib_872.h_char n len hn, PEqualNP.Outside.L_lib_872.h_count n len hn⟩
