import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_app_ge (l l2 : List Bool) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l2).getD i false = l2.getD (i - l.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_row {n : ℕ} (u v a : Fin n) :
    (oneEach u v).getD a.val false = decide (a = u) := by
  unfold oneEach
  rw [getD_app_lt _ _ _ (by simp), ofFn_getD _ a.val a.isLt]

theorem oneEach_col {n : ℕ} (u v b : Fin n) :
    (oneEach u v).getD (n + b.val) false = decide (b = v) := by
  unfold oneEach
  rw [getD_app_ge _ _ _ (by simp), List.length_ofFn, ofFn_getD _ (n + b.val - n) (by omega)]
  congr 1
  simp [Fin.ext_iff]

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

def Mono (e : List Gate) : Prop :=
  ∀ g ∈ e, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Reach (gs : List Gate) (c : ℕ) (gs' : List Gate) : Prop :=
  ∃ e, gs' = gs ++ e ∧ Mono e ∧ e.length ≤ c

theorem reach_refl (gs : List Gate) : Reach gs 0 gs := by
  refine ⟨[], (List.append_nil gs).symm, ?_, Nat.le_refl 0⟩
  intro g hg
  cases hg

theorem reach_trans {gs gs1 gs2 : List Gate} {c1 c2 c : ℕ} (h1 : Reach gs c1 gs1)
    (h2 : Reach gs1 c2 gs2) (hc : c1 + c2 ≤ c) : Reach gs c gs2 := by
  obtain ⟨e1, rfl, m1, l1⟩ := h1
  obtain ⟨e2, rfl, m2, l2⟩ := h2
  refine ⟨e1 ++ e2, List.append_assoc _ _ _, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact m1 g h
    · exact m2 g h
  · rw [List.length_append]; omega

def Has (n : ℕ) (gs : List Gate) (w : ℕ) (f : Fin n → Fin n → Bool) : Prop :=
  w < n + n + gs.length ∧ ∀ u v : Fin n, (W gs (oneEach u v)).getD w false = f u v

theorem has_reach {n : ℕ} {gs gs' : List Gate} {c w : ℕ} {f : Fin n → Fin n → Bool}
    (h : Reach gs c gs') (hw : Has n gs w f) : Has n gs' w f := by
  obtain ⟨e, rfl, _, _⟩ := h
  refine ⟨by rw [List.length_append]; have := hw.1; omega, fun u v => ?_⟩
  rw [W_append, W_prefix e _ w (by rw [W_length, oneEach_length]; exact hw.1)]
  exact hw.2 u v

theorem has_congr {n : ℕ} {gs : List Gate} {w : ℕ} {f g : Fin n → Fin n → Bool}
    (h : ∀ u v, f u v = g u v) (hw : Has n gs w f) : Has n gs w g :=
  ⟨hw.1, fun u v => (hw.2 u v).trans (h u v)⟩

theorem has_row {n : ℕ} (gs : List Gate) (a : Fin n) :
    Has n gs a.val (fun u _ => decide (a = u)) := by
  refine ⟨by have := a.isLt; omega, fun u v => ?_⟩
  rw [W_prefix gs _ _ (by rw [oneEach_length]; have := a.isLt; omega), oneEach_row]

theorem has_col {n : ℕ} (gs : List Gate) (b : Fin n) :
    Has n gs (n + b.val) (fun _ v => decide (b = v)) := by
  refine ⟨by have := b.isLt; omega, fun u v => ?_⟩
  rw [W_prefix gs _ _ (by rw [oneEach_length]; have := b.isLt; omega), oneEach_col]

theorem has_or {n : ℕ} {gs : List Gate} {a b : ℕ} {f g : Fin n → Fin n → Bool}
    (ha : Has n gs a f) (hb : Has n gs b g) :
    ∃ gs' w, Reach gs 1 gs' ∧ Has n gs' w (fun u v => f u v || g u v) := by
  refine ⟨gs ++ [⟨GateOp.or, [a, b]⟩], n + n + gs.length, ⟨_, rfl, ?_, Nat.le_refl 1⟩, ?_,
    fun u v => ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Or.inr rfl, Nat.le_refl 2⟩
  · rw [List.length_append, List.length_singleton]; omega
  · rw [W_snoc, step_last _ _ _ (by rw [W_length, oneEach_length])]
    show GateOp.or.eval [(W gs (oneEach u v)).getD a false, (W gs (oneEach u v)).getD b false] = _
    rw [ha.2 u v, hb.2 u v, eval_or2]

theorem has_and {n : ℕ} {gs : List Gate} {a b : ℕ} {f g : Fin n → Fin n → Bool}
    (ha : Has n gs a f) (hb : Has n gs b g) :
    ∃ gs' w, Reach gs 1 gs' ∧ Has n gs' w (fun u v => f u v && g u v) := by
  refine ⟨gs ++ [⟨GateOp.and, [a, b]⟩], n + n + gs.length, ⟨_, rfl, ?_, Nat.le_refl 1⟩, ?_,
    fun u v => ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Or.inl rfl, Nat.le_refl 2⟩
  · rw [List.length_append, List.length_singleton]; omega
  · rw [W_snoc, step_last _ _ _ (by rw [W_length, oneEach_length])]
    show GateOp.and.eval [(W gs (oneEach u v)).getD a false, (W gs (oneEach u v)).getD b false] = _
    rw [ha.2 u v, hb.2 u v, eval_and2]

theorem or_dec (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] (h : (p ∨ q) ↔ r) :
    (decide p || decide q) = decide r := by
  rw [← Bool.decide_or]
  exact decide_eq_decide.mpr h

theorem colrun {n : ℕ} (a : ℕ) : ∀ (j : ℕ) (gs : List Gate), a + j < n →
    ∃ gs', Reach gs j gs' ∧ ∀ i, i ≤ j →
      ∃ w, Has n gs' w (fun _ v => decide (a ≤ v.val ∧ v.val ≤ a + i)) := by
  intro j
  induction j with
  | zero =>
    intro gs h
    refine ⟨gs, reach_refl gs, fun i hi => ⟨n + a, ?_⟩⟩
    have hi0 : i = 0 := by omega
    subst hi0
    refine has_congr (fun u v => ?_) (has_col gs ⟨a, by omega⟩)
    apply decide_eq_decide.mpr
    rw [Fin.ext_iff]
    show a = v.val ↔ _
    omega
  | succ j ih =>
    intro gs h
    obtain ⟨gs1, r1, h1⟩ := ih gs (by omega)
    obtain ⟨w1, hw1⟩ := h1 j (Nat.le_refl j)
    obtain ⟨gs2, w2, r2, hw2⟩ := has_or hw1 (has_col gs1 ⟨a + (j + 1), h⟩)
    refine ⟨gs2, reach_trans r1 r2 (Nat.le_refl _), fun i hi => ?_⟩
    by_cases hij : i ≤ j
    · obtain ⟨w, hw⟩ := h1 i hij
      exact ⟨w, has_reach r2 hw⟩
    · have hi1 : i = j + 1 := by omega
      subst hi1
      refine ⟨w2, has_congr (fun u v => ?_) hw2⟩
      apply or_dec
      rw [Fin.ext_iff]
      show _ ∨ a + (j + 1) = v.val ↔ _
      omega

theorem rowsOr {n : ℕ} (S : Finset (Fin n)) :
    ∀ (gs : List Gate) (a : ℕ) (f0 : Fin n → Fin n → Bool), Has n gs a f0 →
      ∃ gs' w, Reach gs S.card gs' ∧ Has n gs' w (fun u v => f0 u v || decide (u ∈ S)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro gs a f0 h
    exact ⟨gs, a, reach_refl gs, has_congr (fun u v => by simp) h⟩
  | insert x S hx ih =>
    intro gs a f0 h
    obtain ⟨gs1, w1, r1, h1⟩ := ih gs a f0 h
    obtain ⟨gs2, w2, r2, h2⟩ := has_or h1 (has_row gs1 x)
    refine ⟨gs2, w2, reach_trans r1 r2 (by rw [Finset.card_insert_of_notMem hx]),
      has_congr (fun u v => ?_) h2⟩
    rw [Bool.or_assoc]
    congr 1
    apply or_dec
    rw [Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

theorem classOr {n : ℕ} (t : Fin n → ℕ) (u0 : Fin n) (gs : List Gate) :
    ∃ gs' w, Reach gs ((Finset.univ.filter (fun u => t u = t u0)).card - 1) gs' ∧
      Has n gs' w (fun u _ => decide (t u = t u0)) := by
  have hmem : u0 ∈ Finset.univ.filter (fun u => t u = t u0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ u0, rfl⟩
  obtain ⟨gs1, w1, r1, h1⟩ := rowsOr ((Finset.univ.filter (fun u => t u = t u0)).erase u0) gs
    u0.val _ (has_row gs u0)
  rw [Finset.card_erase_of_mem hmem] at r1
  refine ⟨gs1, w1, r1, has_congr (fun u v => ?_) h1⟩
  apply or_dec
  rw [Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro (h | h)
    · rw [h]
    · exact h.2.2
  · intro h
    by_cases h2 : u0 = u
    · exact Or.inl h2
    · exact Or.inr ⟨fun e => h2 e.symm, Finset.mem_univ u, h⟩

theorem classFold {n : ℕ} (t : Fin n → ℕ) (m : ℕ) (S : Finset ℕ) :
    (∀ τ ∈ S, τ ∈ Finset.univ.image t) →
    ∀ (gs : List Gate) (a : ℕ) (f0 : Fin n → Fin n → Bool), Has n gs a f0 →
    (∀ τ ∈ S, ∃ q, Has n gs q (fun _ v => decide (m ≤ v.val ∧ v.val < τ))) →
    ∃ gs' w, Reach gs (∑ τ ∈ S, ((Finset.univ.filter (fun u => t u = τ)).card + 1)) gs' ∧
      Has n gs' w
        (fun u v => f0 u v || (decide (t u ∈ S) && decide (m ≤ v.val ∧ v.val < t u))) := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ gs a f0 h _
    refine ⟨gs, a, ?_, has_congr (fun u v => by simp) h⟩
    rw [Finset.sum_empty]
    exact reach_refl gs
  | insert x S hx ih =>
    intro hS gs a f0 h hq
    obtain ⟨gs1, w1, r1, h1⟩ := ih (fun τ hτ => hS τ (Finset.mem_insert_of_mem hτ)) gs a f0 h
      (fun τ hτ => hq τ (Finset.mem_insert_of_mem hτ))
    obtain ⟨u0, _, hu0⟩ := Finset.mem_image.mp (hS x (Finset.mem_insert_self x S))
    subst hu0
    obtain ⟨gs2, w2, r2, h2⟩ := classOr t u0 gs1
    obtain ⟨q, hq0⟩ := hq (t u0) (Finset.mem_insert_self _ S)
    obtain ⟨gs3, w3, r3, h3⟩ :=
      has_and h2 (has_reach (reach_trans r1 r2 (Nat.le_refl _)) hq0)
    obtain ⟨gs4, w4, r4, h4⟩ := has_or (has_reach (reach_trans r2 r3 (Nat.le_refl _)) h1) h3
    have hc : 1 ≤ (Finset.univ.filter (fun u => t u = t u0)).card :=
      Finset.card_pos.mpr ⟨u0, Finset.mem_filter.mpr ⟨Finset.mem_univ u0, rfl⟩⟩
    refine ⟨gs4, w4, reach_trans (reach_trans (reach_trans r1 r2 (Nat.le_refl _)) r3
      (Nat.le_refl _)) r4 ?_, has_congr (fun u v => ?_) h4⟩
    · rw [Finset.sum_insert hx]; omega
    · by_cases hu : t u = t u0
      · rw [hu]
        simp [hx]
      · simp [hu]

theorem main : ∀ n k a b : ℕ, 3 ≤ k → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) (2 * n + k - 4 - a - b) := by
  intro n k a b hk t ht htop hcard ha hb
  obtain ⟨un, hun⟩ := htop
  obtain ⟨um, -, hmin⟩ := Finset.exists_min_image Finset.univ t ⟨un, Finset.mem_univ un⟩
  have hmin' : ∀ u, t um ≤ t u := fun u => hmin u (Finset.mem_univ u)
  have hmem_n : n ∈ Finset.univ.image t := Finset.mem_image.mpr ⟨un, Finset.mem_univ un, hun⟩
  have himg : ∀ u, t u ∈ Finset.univ.image t := fun u =>
    Finset.mem_image_of_mem t (Finset.mem_univ u)
  obtain ⟨S, hSdef⟩ : ∃ S, S = ((Finset.univ.image t).erase n).erase (t um) := ⟨_, rfl⟩
  have hSmem : ∀ τ, τ ∈ S ↔ τ ≠ t um ∧ τ ≠ n ∧ τ ∈ Finset.univ.image t := by
    intro τ
    rw [hSdef, Finset.mem_erase, Finset.mem_erase]
  have hSge : k - 2 ≤ S.card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.image t) (a := n)
    have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ.image t).erase n) (a := t um)
    rw [← hSdef] at h2
    omega
  obtain ⟨τ0, hτ0⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨hτ1, hτ2, hτ3⟩ := (hSmem τ0).mp hτ0
  obtain ⟨u1, _, hu1⟩ := Finset.mem_image.mp hτ3
  have hb1 := hmin' u1
  have hb2 := (ht u1).2
  have hm1 := (ht um).1
  have hmn : t um + 2 ≤ n := by omega
  have hne : t um ≠ n := by omega
  have hSbd : ∀ τ ∈ S, t um < τ ∧ τ < n := by
    intro τ hτ
    obtain ⟨h1, h2, h3⟩ := (hSmem τ).mp hτ
    obtain ⟨u2, _, hu2⟩ := Finset.mem_image.mp h3
    have := hmin' u2
    have := (ht u2).2
    omega
  have hScard : S.card = k - 2 := by
    rw [hSdef, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, himg um⟩),
      Finset.card_erase_of_mem hmem_n, hcard]
    omega
  have hsum : (Finset.univ.filter (fun u => t u = n)).card +
      ((Finset.univ.filter (fun u => t u = t um)).card +
        ∑ τ ∈ S, (Finset.univ.filter (fun u => t u = τ)).card) = n := by
    rw [hSdef, Finset.add_sum_erase _ (fun τ => (Finset.univ.filter (fun u => t u = τ)).card)
      (Finset.mem_erase.mpr ⟨hne, himg um⟩),
      Finset.add_sum_erase _ (fun τ => (Finset.univ.filter (fun u => t u = τ)).card) hmem_n,
      ← Finset.card_eq_sum_card_image, Finset.card_univ, Fintype.card_fin]
  have hafilt : (Finset.univ.filter (fun u => t u = t um)).card = a := by
    rw [← ha]
    congr 1
    apply Finset.filter_congr
    intro u _
    constructor
    · intro h u'
      rw [h]
      exact hmin' u'
    · intro h
      exact Nat.le_antisymm (h um) (hmin' u)
  have hSb : ∀ τ ∈ S, τ + b ≤ n := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := hSbd τ hτ
    obtain ⟨u2, _, hu2⟩ := Finset.mem_image.mp ((hSmem τ).mp hτ).2.2
    have hge : ∀ v ∈ Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n,
        (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤
          (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card), τ ≤ v.val := by
      intro v hv
      have hv2 : (Finset.univ.filter (fun u => v.val < t u)).card ≤
          (Finset.univ.filter (fun u => n - 1 < t u)).card :=
        (Finset.mem_filter.mp hv).2 ⟨n - 1, by omega⟩
      by_contra hlt
      have hsub : Finset.univ.filter (fun u => n - 1 < t u) ⊆
          Finset.univ.filter (fun u => v.val < t u) := by
        intro u hu
        have h3 := (Finset.mem_filter.mp hu).2
        have h4 := v.isLt
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, by omega⟩
      have hss := (Finset.ssubset_iff_of_subset hsub).mpr
        ⟨u2, Finset.mem_filter.mpr ⟨Finset.mem_univ u2, by omega⟩, fun hc => by
          have h3 := (Finset.mem_filter.mp hc).2
          omega⟩
      have h5 := Finset.card_lt_card hss
      omega
    have hle : b ≤ (Finset.range (n - τ)).card := by
      rw [← hb]
      apply Finset.card_le_card_of_injOn (fun v : Fin n => v.val - τ)
      · intro v hv
        have h3 := hge v hv
        have h4 := v.isLt
        show v.val - τ ∈ Finset.range (n - τ)
        exact Finset.mem_range.mpr (by omega)
      · intro v1 hv1 v2 hv2 heq
        have h3 := hge v1 (Finset.mem_coe.mp hv1)
        have h4 := hge v2 (Finset.mem_coe.mp hv2)
        have h5 : v1.val - τ = v2.val - τ := heq
        exact Fin.ext (by omega)
    rw [Finset.card_range] at hle
    omega
  have hτb := hSb τ0 hτ0
  have hcost : ∑ τ ∈ S, ((Finset.univ.filter (fun u => t u = τ)).card + 1) =
      ∑ τ ∈ S, (Finset.univ.filter (fun u => t u = τ)).card + S.card := by
    rw [Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  obtain ⟨gs1, r1, p1⟩ := colrun (n := n) 0 (t um - 1) [] (by omega)
  obtain ⟨wp, hp⟩ := p1 (t um - 1) (Nat.le_refl _)
  obtain ⟨gs2, r2, q2⟩ := colrun (n := n) (t um) (n - b - t um - 1) gs1 (by omega)
  have hq : ∀ τ ∈ S, ∃ q, Has n gs2 q (fun _ v => decide (t um ≤ v.val ∧ v.val < τ)) := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := hSbd τ hτ
    have h3 := hSb τ hτ
    obtain ⟨q, hq⟩ := q2 (τ - t um - 1) (by omega)
    refine ⟨q, has_congr (fun u v => ?_) hq⟩
    apply decide_eq_decide.mpr
    omega
  obtain ⟨gs3, w3, r3, h3⟩ := classFold t (t um) S (fun τ hτ => ((hSmem τ).mp hτ).2.2) gs2 wp _
    (has_reach r2 hp) hq
  obtain ⟨gs4, w4, r4, h4⟩ := rowsOr (Finset.univ.filter (fun u => t u = n)) gs3 w3 _ h3
  obtain ⟨e, he, hmono, hlen⟩ := reach_trans (reach_trans (reach_trans r1 r2 (Nat.le_refl _)) r3
    (Nat.le_refl _)) r4 (Nat.le_refl _)
  subst he
  refine ⟨⟨gs4, w4⟩, fun g hg => hmono g hg, ?_, ?_⟩
  · show gs4.length ≤ _
    omega
  · intro u v
    rw [eval_W]
    show (W gs4 (oneEach u v)).getD w4 false = _
    rw [h4.2 u v]
    have hv := v.isLt
    have h1 := hmin' u
    have h2 := (ht u).2
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_filter,
      Finset.mem_univ, true_and, hSmem, himg u, and_true]
    omega

end PEqualNP.Outside.L_meta_19451

theorem PEqualNP.Outside.L_meta_19451 : ∀ n k a b : ℕ, 3 ≤ k → ∀ t : Fin n → ℕ, (∀ u, 1 ≤ t u ∧ t u ≤ n) → (∃ u, t u = n) → (Finset.univ.image t).card = k → (Finset.univ.filter (fun u => ∀ u', t u ≤ t u')).card = a → (Finset.univ.filter (fun v : Fin n => ∀ v' : Fin n, (Finset.univ.filter (fun u => (v : ℕ) < t u)).card ≤ (Finset.univ.filter (fun u => (v' : ℕ) < t u)).card)).card = b → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((v : ℕ) < t u)) (2 * n + k - 4 - a - b) :=
  PEqualNP.Outside.L_meta_19451.main
