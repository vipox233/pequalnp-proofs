import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1287_aux
open PEqualNP.CircuitLowerBounds

open Relation

section TwoSat
variable {α : Type} [Fintype α] [DecidableEq α]

lemma rtg_skew (r : α → α → Prop) (ng : α → α)
    (skew : ∀ p q, r p q → r (ng q) (ng p)) {a b : α} (h : ReflTransGen r a b) :
    ReflTransGen r (ng b) (ng a) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (skew _ _ hbc) ih

theorem two_sat (r : α → α → Prop) (ng : α → α) (inv : ∀ p, ng (ng p) = p)
    (skew : ∀ p q, r p q → r (ng q) (ng p))
    (clean : ∀ p, ¬ (ReflTransGen r p (ng p) ∧ ReflTransGen r (ng p) p))
    (l : α) (hl : ¬ ReflTransGen r l (ng l)) :
    ∃ S : Finset α, l ∈ S ∧ (∀ p ∈ S, ∀ q, ReflTransGen r p q → q ∈ S) ∧
      (∀ p, p ∈ S ∨ ng p ∈ S) ∧ (∀ p, ¬ (p ∈ S ∧ ng p ∈ S)) := by
  classical
  let R := ReflTransGen r
  let reachS : α → Finset α := fun c => Finset.univ.filter (fun q => R c q)
  have hreach_cons : ∀ c, ¬ R c (ng c) → ∀ q, ¬ (R c q ∧ R c (ng q)) := by
    intro c hc q ⟨h1, h2⟩
    have h3 : R (ng (ng q)) (ng c) := rtg_skew r ng skew h2
    rw [inv] at h3
    exact hc (h1.trans h3)
  let good : Finset α → Prop := fun S => l ∈ S ∧ (∀ p ∈ S, ∀ q, R p q → q ∈ S) ∧
      (∀ p, ¬ (p ∈ S ∧ ng p ∈ S))
  have hgood0 : good (reachS l) := by
    refine ⟨by simp [reachS]; exact ReflTransGen.refl, ?_, ?_⟩
    · intro p hp q hq
      simp only [reachS, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.trans hq
    · intro p ⟨h1, h2⟩
      simp only [reachS, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hreach_cons l hl p ⟨h1, h2⟩
  let cands := (Finset.univ : Finset (Finset α)).filter good
  have hne : cands.Nonempty := ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood0⟩⟩
  obtain ⟨S, hSc, hmax⟩ := Finset.exists_max_image cands Finset.card hne
  have hS : good S := (Finset.mem_filter.mp hSc).2
  obtain ⟨hlS, hclosed, hcons⟩ := hS
  refine ⟨S, hlS, hclosed, ?_, hcons⟩
  by_contra hall
  push_neg at hall
  obtain ⟨p, hp1, hp2⟩ := hall

  have : ∃ c, (c = p ∨ c = ng p) ∧ ¬ R c (ng c) := by
    by_cases h : R p (ng p)
    · refine ⟨ng p, Or.inr rfl, ?_⟩
      rw [inv]
      intro h'
      exact clean p ⟨h, h'⟩
    · exact ⟨p, Or.inl rfl, h⟩
  obtain ⟨c, hcp, hc⟩ := this
  have hcS : c ∉ S := by rcases hcp with rfl | rfl <;> assumption
  have hncS : ng c ∉ S := by
    rcases hcp with rfl | rfl
    · exact hp2
    · rw [inv]; exact hp1
  let S' := S ∪ reachS c
  have hgood' : good S' := by
    refine ⟨Finset.mem_union_left _ hlS, ?_, ?_⟩
    · intro a ha q hq
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.mem_union_left _ (hclosed a ha q hq)
      · simp only [reachS, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact Finset.mem_union_right _ (by simp [reachS]; exact ha.trans hq)
    · intro a ⟨h1, h2⟩
      have key : ∀ b, b ∈ S → R c (ng b) → False := by
        intro b hb hcb
        have h3 : R (ng (ng b)) (ng c) := rtg_skew r ng skew hcb
        rw [inv] at h3
        exact hncS (hclosed b hb _ h3)
      rcases Finset.mem_union.mp h1 with h1 | h1 <;>
        rcases Finset.mem_union.mp h2 with h2 | h2
      · exact hcons a ⟨h1, h2⟩
      · simp only [reachS, Finset.mem_filter, Finset.mem_univ, true_and] at h2
        exact key a h1 h2
      · simp only [reachS, Finset.mem_filter, Finset.mem_univ, true_and] at h1
        exact key (ng a) h2 (by rw [inv]; exact h1)
      · simp only [reachS, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact hreach_cons c hc a ⟨h1, h2⟩
  have hlt : S.card < S'.card := by
    apply Finset.card_lt_card
    refine ⟨Finset.subset_union_left, fun hsub => hcS (hsub ?_)⟩
    exact Finset.mem_union_right _ (by simp [reachS]; exact ReflTransGen.refl)
  have := hmax S' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood'⟩)
  omega

end TwoSat

def maj3 (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem baker_pixley {t : ℕ} (ok : (Fin t → Bool) → Prop) (hne : ∃ z, ok z)
    (hmaj : ∀ a b c, ok a → ok b → ok c → ok (fun k => (a k && b k) || (a k && c k) || (b k && c k)))
    (z : Fin t → Bool) (hpair : ∀ k l, ∃ w, ok w ∧ w k = z k ∧ w l = z l) : ok z := by
  classical
  have key : ∀ N, ∀ S : Finset (Fin t), S.card = N → ∃ w, ok w ∧ ∀ k ∈ S, w k = z k := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro S hS
      by_cases h3 : N ≤ 2
      ·
        rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
        · obtain ⟨w, hw⟩ := hne; exact ⟨w, hw, by simp⟩
        · rcases (S.erase a).eq_empty_or_nonempty with he | ⟨b, hb⟩
          · obtain ⟨w, hw, h1, -⟩ := hpair a a
            refine ⟨w, hw, fun k hk => ?_⟩
            by_cases hka : k = a
            · subst hka; exact h1
            · have : k ∈ S.erase a := Finset.mem_erase.mpr ⟨hka, hk⟩
              simp [he] at this
          · obtain ⟨w, hw, h1, h2⟩ := hpair a b
            refine ⟨w, hw, fun k hk => ?_⟩
            by_cases hka : k = a
            · subst hka; exact h1
            by_cases hkb : k = b
            · subst hkb; exact h2
            exfalso
            have hsub : ({a, b, k} : Finset (Fin t)) ⊆ S := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · exact ha
              · exact (Finset.mem_erase.mp hb).2
              · exact hk
            have hab : a ≠ b := fun h => (Finset.mem_erase.mp hb).1 h.symm
            have hc : ({a, b, k} : Finset (Fin t)).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hkb)]
              simp [hab, Ne.symm hka]
            have := Finset.card_le_card hsub
            omega
      · push_neg at h3
        obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
        have h1 : (S.erase a).card = N - 1 := by rw [Finset.card_erase_of_mem ha, hS]
        obtain ⟨b, hb⟩ : (S.erase a).Nonempty := Finset.card_pos.mp (by omega)
        have h2 : ((S.erase a).erase b).card = N - 2 := by
          rw [Finset.card_erase_of_mem hb, h1]; omega
        obtain ⟨c, hc⟩ : ((S.erase a).erase b).Nonempty := Finset.card_pos.mp (by omega)
        have hba : b ≠ a := (Finset.mem_erase.mp hb).1
        have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
        have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
        have hbS : b ∈ S := (Finset.mem_erase.mp hb).2
        have hcS : c ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
        have hca' : (S.erase a).card < N := by omega
        have hcb' : (S.erase b).card < N := by rw [Finset.card_erase_of_mem hbS]; omega
        have hcc' : (S.erase c).card < N := by rw [Finset.card_erase_of_mem hcS]; omega
        obtain ⟨wa, hwa, ea⟩ := ih _ hca' (S.erase a) rfl
        obtain ⟨wb, hwb, eb⟩ := ih _ hcb' (S.erase b) rfl
        obtain ⟨wc, hwc, ec⟩ := ih _ hcc' (S.erase c) rfl
        refine ⟨_, hmaj wa wb wc hwa hwb hwc, fun k hk => ?_⟩
        by_cases hka : k = a
        · subst hka
          rw [eb k (Finset.mem_erase.mpr ⟨Ne.symm hba, hk⟩),
            ec k (Finset.mem_erase.mpr ⟨Ne.symm hca, hk⟩)]
          cases wa k <;> cases z k <;> rfl
        · rw [ea k (Finset.mem_erase.mpr ⟨hka, hk⟩)]
          by_cases hkb : k = b
          · subst hkb
            rw [ec k (Finset.mem_erase.mpr ⟨Ne.symm hcb, hk⟩)]
            cases wb k <;> cases z k <;> rfl
          · rw [eb k (Finset.mem_erase.mpr ⟨hkb, hk⟩)]
            cases wc k <;> cases z k <;> rfl
  obtain ⟨w, hw, e⟩ := key _ Finset.univ rfl
  have : w = z := funext fun k => e k (Finset.mem_univ k)
  exact this ▸ hw

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stepW x

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma W_append (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stepW (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_append]; simp [stepW, ih]; omega

lemma W_getD_lt (gs : List Gate) (g : Gate) (x : List Bool) (k : ℕ)
    (hk : k < (W gs x).length) : (W (gs ++ [g]) x).getD k false = (W gs x).getD k false := by
  rw [W_append, stepW]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma W_getD_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (W (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
  rw [W_append, stepW]
  have := W_length gs x
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [this]

lemma W_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hxy : ∀ k, x.getD k false = true → y.getD k false = true)
    (hlen : x.length = y.length) :
    ∀ k, (W gs x).getD k false = true → (W gs y).getD k false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hgs g' (List.mem_append_left _ hg'))
    intro k hk
    have hlx := W_length gs x
    have hly := W_length gs y
    by_cases hlt : k < x.length + gs.length
    · rw [W_getD_lt gs g x k (by omega)] at hk
      rw [W_getD_lt gs g y k (by omega)]
      exact ih k hk
    by_cases heq : k = x.length + gs.length
    · subst heq
      rw [W_getD_last] at hk
      rw [hlen, W_getD_last]
      have hop := hgs g (List.mem_append_right _ (List.mem_singleton_self g))
      rcases hop with hop | hop <;> rw [hop] at hk ⊢ <;>
        simp only [GateOp.eval, List.all_map, List.any_map, List.all_eq_true,
          List.any_eq_true, Function.comp, id] at hk ⊢
      · intro i hi; exact ih i (hk i hi)
      · obtain ⟨i, hi, h⟩ := hk; exact ⟨i, hi, ih i h⟩
    · exfalso
      have : (W (gs ++ [g]) x).length = x.length + gs.length + 1 := by
        rw [W_length]; simp; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hk
      simp at hk

lemma W_prefix (as bs : List Gate) (x : List Bool) (k : ℕ) (hk : k < x.length + as.length) :
    (W (as ++ bs) x).getD k false = (W as x).getD k false := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs g ih =>
    rw [← List.append_assoc, W_getD_lt _ _ _ _ (by rw [W_length]; simp; omega), ih]

lemma W_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (W gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (W gs x).getD i false) := by
  have hsplit : gs = (gs.take j ++ [gs[j]]) ++ gs.drop (j+1) := by
    simp
  have hlt : (gs.take j).length = j := by simp; omega
  have e1 : (W gs x).getD (x.length + j) false =
      (W (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    exact W_prefix _ _ _ _ (by simp; omega)
  have hl := W_getD_last (gs.take j) gs[j] x
  rw [hlt] at hl
  rw [e1, hl]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := hrb i hi
  conv_rhs => rw [hsplit]
  rw [W_prefix _ _ _ _ (by simp; omega), W_getD_lt _ _ _ _ (by rw [W_length]; omega)]

def inp (n : ℕ) (b : Fin n → Bool) : List Bool := List.ofFn b ++ [false, true]

lemma inp_length (n : ℕ) (b : Fin n → Bool) : (inp n b).length = n + 2 := by simp [inp]

lemma inp_lt (n : ℕ) (b : Fin n → Bool) (s : ℕ) (hs : s < n) :
    (inp n b).getD s false = b ⟨s, hs⟩ := by
  rw [inp, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hs])]
  simp [hs]

lemma inp_false (n : ℕ) (b : Fin n → Bool) : (inp n b).getD n false = false := by
  simp [inp, List.getD_eq_getElem?_getD]

lemma inp_true (n : ℕ) (b : Fin n → Bool) : (inp n b).getD (n+1) false = true := by
  simp [inp, List.getD_eq_getElem?_getD]

def T (n i : ℕ) : ℕ := if n = 0 then n + 1 else n + 2 + i * n + (n - 1)

def G (n m : ℕ) (mem sel : ℕ → ℕ → Bool) (j : ℕ) : Gate :=
  if j < m * n then
    ⟨GateOp.and, [if j % n = 0 then n + 1 else n + 2 + j - 1] ++
      (if mem (j / n) (j % n) then [j % n] else [])⟩
  else
    ⟨GateOp.or, [if (j - m * n) % m = 0 then n else n + 2 + j - 1] ++
      (if sel ((j - m * n) / m) ((j - m * n) % m) then [T n ((j - m * n) % m)] else [])⟩

def gates (n m t : ℕ) (mem sel : ℕ → ℕ → Bool) : List Gate :=
  (List.range (m * n + t * m)).map (G n m mem sel)

def tap (n m k : ℕ) : ℕ := if m = 0 then n else n + 2 + m * n + k * m + (m - 1)

lemma gates_length (n m t : ℕ) (mem sel : ℕ → ℕ → Bool) :
    (gates n m t mem sel).length = m * n + t * m := by simp [gates]

lemma gates_get (n m t : ℕ) (mem sel : ℕ → ℕ → Bool) (j : ℕ) (hj : j < (gates n m t mem sel).length) :
    (gates n m t mem sel)[j] = G n m mem sel j := by simp [gates]

lemma G_readsBack (n m t : ℕ) (mem sel : ℕ → ℕ → Bool) (j : ℕ) (hj : j < m * n + t * m) :
    ∀ i ∈ (G n m mem sel j).inputs, i < n + 2 + j := by
  intro i hi
  unfold G at hi
  by_cases h1 : j < m * n
  · rw [if_pos h1] at hi
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at h1
      · exact h
    have hmod := Nat.mod_lt j hn
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | hi
    · split_ifs at hi with h2
      · omega
      · have : j ≠ 0 := by rintro rfl; simp at h2
        omega
    · split_ifs at hi with h2
      · simp at hi; omega
      · simp at hi
  · rw [if_neg h1] at hi
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hj
      · exact h
    have hmod := Nat.mod_lt (j - m * n) hm
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | hi
    · split_ifs at hi with h2
      · omega
      · have : j - m * n ≠ 0 := by intro h; rw [h] at h2; simp at h2
        omega
    · split_ifs at hi with h2
      · simp at hi
        subst hi
        unfold T
        split_ifs with h3
        · omega
        · have : ((j - m * n) % m) * n + n ≤ m * n := by
            have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hmod)
            simpa [Nat.succ_mul] using this
          omega
      · simp at hi

lemma dm (n i s : ℕ) (hs : s < n) : (i * n + s) / n = i ∧ (i * n + s) % n = s := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hs, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

section Sem
variable (n m t : ℕ) (mem sel : ℕ → ℕ → Bool) (b : Fin n → Bool)

def val (w : ℕ) : Bool := (W (gates n m t mem sel) (inp n b)).getD w false

lemma val_inp (w : ℕ) (hw : w < n + 2) : val n m t mem sel b w = (inp n b).getD w false := by
  unfold val
  have := W_prefix [] (gates n m t mem sel) (inp n b) w (by simp [inp_length]; omega)
  simpa [W] using this

lemma val_gate (j : ℕ) (hj : j < m * n + t * m) :
    val n m t mem sel b (n + 2 + j) =
      (G n m mem sel j).op.eval ((G n m mem sel j).inputs.map (val n m t mem sel b)) := by
  unfold val
  have hl := gates_length n m t mem sel
  have h := W_gate (gates n m t mem sel) (inp n b) j (by omega) (by
    rw [gates_get, inp_length]; exact G_readsBack n m t mem sel j hj)
  rw [inp_length, gates_get] at h
  exact h

lemma evalAnd (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ w ∈ l, f w = true := by
  simp [GateOp.eval]

lemma evalOr (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ w ∈ l, f w = true := by
  simp [GateOp.eval]

lemma val_A (i : ℕ) (hi : i < m) : ∀ s (hs : s < n),
    (val n m t mem sel b (n + 2 + (i * n + s)) = true ↔
      ∀ s' ≤ s, mem i s' = true → (inp n b).getD s' false = true) := by
  intro s
  induction s with
  | zero =>
    intro hs
    have hj : i * n + 0 < m * n := by
      have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi); simp [Nat.succ_mul] at this; omega
    rw [val_gate _ _ _ _ _ _ _ (by omega)]
    obtain ⟨hd, hmd⟩ := dm n i 0 hs
    simp only [G, if_pos hj, hd, hmd, if_true]
    rw [evalAnd]
    have e1 : val n m t mem sel b (n+1) = true := by
      rw [val_inp _ _ _ _ _ _ _ (by omega), inp_true]
    have e0 : val n m t mem sel b 0 = (inp n b).getD 0 false := val_inp _ _ _ _ _ _ _ (by omega)
    cases hmi : mem i 0
    · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_singleton, forall_eq, e1, true_iff]
      intro s' hs' h; have : s' = 0 := by omega
      subst this; simp [hmi] at h
    · simp only [hmi, if_true, List.mem_append, List.mem_singleton]
      constructor
      · intro h s' hs' _; have : s' = 0 := by omega
        subst this; rw [← e0]; exact h 0 (Or.inr rfl)
      · rintro h w (rfl | rfl)
        · exact e1
        · rw [e0]; exact h 0 (le_refl _) hmi
  | succ s ih =>
    intro hs
    have hj : i * n + (s+1) < m * n := by
      have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi); simp [Nat.succ_mul] at this; omega
    rw [val_gate _ _ _ _ _ _ _ (by omega)]
    obtain ⟨hd, hmd⟩ := dm n i (s+1) hs
    simp only [G, if_pos hj, hd, hmd, Nat.add_one_ne_zero, if_false]
    have hprev : n + 2 + (i * n + (s + 1)) - 1 = n + 2 + (i * n + s) := by omega
    rw [hprev, evalAnd]
    have ih' := ih (by omega)
    have e0 : val n m t mem sel b (s+1) = (inp n b).getD (s+1) false :=
      val_inp _ _ _ _ _ _ _ (by omega)
    cases hmi : mem i (s+1)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_singleton, forall_eq]
      rw [ih']
      constructor
      · intro h s' hs' hm
        rcases Nat.lt_or_ge s' (s+1) with h' | h'
        · exact h s' (by omega) hm
        · have : s' = s + 1 := by omega
          subst this; simp [hmi] at hm
      · intro h s' hs' hm; exact h s' (by omega) hm
    · simp only [hmi, if_true, List.mem_append, List.mem_singleton]
      constructor
      · intro h s' hs' hm
        have hA := ih'.mp (h _ (Or.inl rfl))
        rcases Nat.lt_or_ge s' (s+1) with h' | h'
        · exact hA s' (by omega) hm
        · have : s' = s + 1 := by omega
          subst this; rw [← e0]; exact h _ (Or.inr rfl)
      · rintro h w (rfl | rfl)
        · exact ih'.mpr (fun s' hs' hm => h s' (by omega) hm)
        · rw [e0]; exact h (s+1) (le_refl _) hmi

lemma val_T (i : ℕ) (hi : i < m) :
    (val n m t mem sel b (T n i) = true ↔
      ∀ s' < n, mem i s' = true → (inp n b).getD s' false = true) := by
  unfold T
  split_ifs with hn
  · subst hn
    rw [val_inp _ _ _ _ _ _ _ (by omega), inp_true]; simp
  · have := val_A n m t mem sel b i hi (n - 1) (by omega)
    rw [show n + 2 + i * n + (n - 1) = n + 2 + (i * n + (n - 1)) by omega, this]
    constructor
    · intro h s' hs' hm; exact h s' (by omega) hm
    · intro h s' hs' hm; exact h s' (by omega) hm

lemma val_B (k : ℕ) (hk : k < t) : ∀ i (hi : i < m),
    (val n m t mem sel b (n + 2 + (m * n + (k * m + i))) = true ↔
      ∃ i' ≤ i, sel k i' = true ∧ val n m t mem sel b (T n i') = true) := by
  have hkm : ∀ i, i < m → k * m + i < t * m := by
    intro i hi
    have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hk); simp [Nat.succ_mul] at this; omega
  intro i
  induction i with
  | zero =>
    intro hi
    rw [val_gate _ _ _ _ _ _ _ (by have := hkm 0 hi; omega)]
    obtain ⟨hd, hmd⟩ := dm m k 0 hi
    have hsub : m * n + (k * m + 0) - m * n = k * m + 0 := by omega
    simp only [G, show ¬ (m * n + (k * m + 0) < m * n) by omega, ↓reduceIte, hsub, hd, hmd]
    rw [evalOr]
    have e1 : val n m t mem sel b n = false := by
      rw [val_inp _ _ _ _ _ _ _ (by omega), inp_false]
    cases hsk : sel k 0
    · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_singleton,
        exists_eq_left, e1, false_iff]
      rintro ⟨i', hi', h1, -⟩; have : i' = 0 := by omega
      subst this; simp [hsk] at h1
    · simp only [↓reduceIte, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨w, (rfl | rfl), h⟩
        · simp [e1] at h
        · exact ⟨0, le_refl _, hsk, h⟩
      · rintro ⟨i', hi', -, h⟩
        have : i' = 0 := by omega
        subst this; exact ⟨_, Or.inr rfl, h⟩
  | succ i ih =>
    intro hi
    rw [val_gate _ _ _ _ _ _ _ (by have := hkm (i+1) hi; omega)]
    obtain ⟨hd, hmd⟩ := dm m k (i+1) hi
    have hsub : m * n + (k * m + (i+1)) - m * n = k * m + (i+1) := by omega
    simp only [G, show ¬ (m * n + (k * m + (i+1)) < m * n) by omega, ↓reduceIte, hsub, hd, hmd,
      Nat.add_one_ne_zero]
    have hprev : n + 2 + (m * n + (k * m + (i + 1))) - 1 = n + 2 + (m * n + (k * m + i)) := by
      omega
    rw [hprev, evalOr]
    have ih' := ih (by omega)
    cases hsk : sel k (i+1)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_singleton,
        exists_eq_left]
      rw [ih']
      constructor
      · rintro ⟨i', hi', h⟩; exact ⟨i', by omega, h⟩
      · rintro ⟨i', hi', h1, h2⟩
        rcases Nat.lt_or_ge i' (i+1) with h' | h'
        · exact ⟨i', by omega, h1, h2⟩
        · have : i' = i + 1 := by omega
          subst this; simp [hsk] at h1
    · simp only [↓reduceIte, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨w, (rfl | rfl), h⟩
        · obtain ⟨i', hi', h'⟩ := ih'.mp h; exact ⟨i', by omega, h'⟩
        · exact ⟨i+1, le_refl _, hsk, h⟩
      · rintro ⟨i', hi', h1, h2⟩
        rcases Nat.lt_or_ge i' (i+1) with h' | h'
        · exact ⟨_, Or.inl rfl, ih'.mpr ⟨i', by omega, h1, h2⟩⟩
        · have : i' = i + 1 := by omega
          subst this; exact ⟨_, Or.inr rfl, h2⟩

lemma val_tap (k : ℕ) (hk : k < t) :
    (val n m t mem sel b (tap n m k) = true ↔
      ∃ i < m, sel k i = true ∧ val n m t mem sel b (T n i) = true) := by
  unfold tap
  split_ifs with hm
  · subst hm
    rw [val_inp _ _ _ _ _ _ _ (by omega), inp_false]; simp
  · have := val_B n m t mem sel b k hk (m - 1) (by omega)
    rw [show n + 2 + m * n + k * m + (m - 1) = n + 2 + (m * n + (k * m + (m - 1))) by omega, this]
    constructor
    · rintro ⟨i', hi', h⟩; exact ⟨i', by omega, h⟩
    · rintro ⟨i', hi', h⟩; exact ⟨i', by omega, h⟩

end Sem

lemma inp_mono {n : ℕ} (b c : Fin n → Bool) (h : ∀ j, b j = true → c j = true) :
    ∀ k, (inp n b).getD k false = true → (inp n c).getD k false = true := by
  intro k hk
  rcases Nat.lt_or_ge k n with hkn | hkn
  · rw [inp_lt _ _ _ hkn] at hk ⊢; exact h _ hk
  · rcases Nat.lt_or_ge k (n+2) with hk2 | hk2
    · rcases (show k = n ∨ k = n + 1 by omega) with rfl | rfl
      · rw [inp_false] at hk; exact absurd hk (by simp)
      · rw [inp_true]
    · exfalso
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [inp_length]; omega)] at hk
      simp at hk

lemma wire_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (b c : Fin n → Bool) (h : ∀ j, b j = true → c j = true) (w : ℕ) :
    (C.wires (inp n b)).getD w false = true → (C.wires (inp n c)).getD w false = true := by
  have := W_mono C.gates (fun g hg => by
      have := (hC g hg).1
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this)
    (inp n b) (inp n c) (inp_mono b c h) (by simp [inp_length])
  exact this w

lemma build (n m t : ℕ) (x : Fin m → Finset (Fin n)) (z : Fin m → Fin t → Bool)
    (hz : ∀ i j k, x i ⊆ x j → z i k = true → z j k = true) :
    ∃ (C : Circuit) (p : Fin t → ℕ), PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n + 2 + C.size ∧
      (∀ k, p k < n + 2 + C.size) ∧ C.size ≤ (n + t) * m ∧
      ∀ i k, (C.wires (inp n (fun j => decide (j ∈ x i)))).getD (p k) false = z i k := by
  classical
  let mem : ℕ → ℕ → Bool := fun i s =>
    if h : i < m ∧ s < n then decide ((⟨s, h.2⟩ : Fin n) ∈ x ⟨i, h.1⟩) else false
  let sel : ℕ → ℕ → Bool := fun k i =>
    if h : k < t ∧ i < m then z ⟨i, h.2⟩ ⟨k, h.1⟩ else false
  let C : Circuit := ⟨gates n m t mem sel, 0⟩
  have hsize : C.size = m * n + t * m := gates_length n m t mem sel
  refine ⟨C, fun k => tap n m k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
    unfold G
    split_ifs <;> simp <;> split_ifs <;> simp
  · intro j hj i hi
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = G n m mem sel j := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact gates_get n m t mem sel j hj
    rw [hg] at hi
    have hj' : j < m * n + t * m := by rw [← hsize]; exact hj
    exact G_readsBack n m t mem sel j hj' i hi
  · show 0 < n + 2 + C.size; omega
  · intro k
    rw [hsize]
    show tap n m k < _
    unfold tap
    split_ifs with hm
    · omega
    · have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt k.2)
      simp [Nat.succ_mul] at this
      omega
  · rw [hsize, Nat.add_mul, Nat.mul_comm n m]
  · intro i k
    have key : (C.wires (inp n (fun j => decide (j ∈ x i)))).getD (tap n m k) false = true ↔
        z i k = true := by
      show val n m t mem sel _ (tap n m k) = true ↔ _
      rw [val_tap n m t mem sel _ k k.2]
      constructor
      · rintro ⟨i', hi', hs, hT⟩
        rw [val_T n m t mem sel _ i' hi'] at hT
        have hs' : z ⟨i', hi'⟩ k = true := by simpa [sel, k.2, hi'] using hs
        apply hz ⟨i', hi'⟩ i k _ hs'
        intro s hsx
        have := hT s.val s.2 (by simp [mem, hi', s.2, hsx])
        rw [inp_lt _ _ _ s.2] at this
        simpa using this
      · intro h
        refine ⟨i.val, i.2, by simpa [sel, k.2, i.2] using h, ?_⟩
        rw [val_T n m t mem sel _ i.val i.2]
        intro s' hs' hm
        rw [inp_lt _ _ _ hs']
        simpa [mem, i.2, hs'] using hm
    cases h : z i k
    · cases h' : (C.wires (inp n (fun j => decide (j ∈ x i)))).getD (tap n m k) false
      · rfl
      · exact absurd (key.mp h') (by simp [h])
    · exact key.mpr h

end PEqualNP.Outside.L_lib_1287_aux

theorem PEqualNP.Outside.L_lib_1287 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m t : Nat) (x : Fin m → Finset (Fin n)) (ok : Fin m → (Fin t → Bool) → Prop),
  (∀ i, ∃ z, ok i z) →
  (∀ i a b c, ok i a → ok i b → ok i c →
    ok i (fun k => (a k && b k) || (a k && c k) || (b k && c k))) →
  let arc := fun (p q : Fin m × Fin t × Bool) =>
    (∃ (i j : Fin m) (k : Fin t), x i ⊆ x j ∧
      ((p = (i,k,true) ∧ q = (j,k,true)) ∨ (p = (j,k,false) ∧ q = (i,k,false)))) ∨
    (∃ (i : Fin m) (k l : Fin t) (a b : Bool),
      (¬ ∃ z, ok i z ∧ z k = a ∧ z l = b) ∧ p = (i,k,a) ∧ q = (i,l,!b))
  let reach := Relation.ReflTransGen arc
  let clean := ∀ (i : Fin m) (k : Fin t),
    ¬ (reach (i,k,false) (i,k,true) ∧ reach (i,k,true) (i,k,false))
  let wire := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (i : Fin m) (k : Nat) =>
    (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD k false
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin t → Nat) =>
    PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ k, p k < n+2+C.size) ∧
    ∀ i, ok i (fun k => wire C i (p k))
  (clean ↔ ∃ C p, fits C p) ∧ (clean → ∃ C p, fits C p ∧ C.size ≤ (n+t)*m) ∧
  (clean → ∀ (i : Fin m) (k : Fin t) (v : Bool), ¬ reach (i,k,v) (i,k,!v) ↔
    ∃ C p, fits C p ∧ C.size ≤ (n+t)*m ∧ wire C i (p k) = v)) := by
  intro n m t x ok hne hmaj arc reach clean wire fits
  classical
  let ng : Fin m × Fin t × Bool → Fin m × Fin t × Bool := fun p => (p.1, p.2.1, !p.2.2)
  have inv : ∀ p, ng (ng p) = p := by rintro ⟨i, k, v⟩; simp [ng]
  have skew : ∀ p q, arc p q → arc (ng q) (ng p) := by
    rintro p q (⟨i, j, k, hij, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨i, k, l, a, b, hno, rfl, rfl⟩)
    · exact Or.inl ⟨i, j, k, hij, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨i, j, k, hij, Or.inl ⟨rfl, rfl⟩⟩
    · refine Or.inr ⟨i, l, k, b, a, ?_, by simp [ng], by simp [ng]⟩
      rintro ⟨z, hz, h1, h2⟩
      exact hno ⟨z, hz, h2, h1⟩
  have cleanP : clean → ∀ p, ¬ (reach p (ng p) ∧ reach (ng p) p) := by
    intro hc
    have hc' : ∀ (i : Fin m) (k : Fin t),
        ¬ (reach (i, k, false) (i, k, true) ∧ reach (i, k, true) (i, k, false)) := hc
    rintro ⟨i, k, v⟩ h
    cases v
    · exact hc' i k ⟨h.1, h.2⟩
    · exact hc' i k ⟨h.2, h.1⟩

  have fromS : ∀ S : Finset (Fin m × Fin t × Bool),
      (∀ p ∈ S, ∀ q, reach p q → q ∈ S) → (∀ p, p ∈ S ∨ ng p ∈ S) →
      (∀ p, ¬ (p ∈ S ∧ ng p ∈ S)) →
      ∃ C p, fits C p ∧ C.size ≤ (n + t) * m ∧
        ∀ i k, wire C i (p k) = decide ((i, k, true) ∈ S) := by
    intro S hcl htot hcons
    let z : Fin m → Fin t → Bool := fun i k => decide ((i, k, true) ∈ S)
    have memz : ∀ i k v, (i, k, v) ∈ S ↔ z i k = v := by
      intro i k v
      cases v
      · have h1 := htot (i, k, false)
        have h2 := hcons (i, k, false)
        simp only [ng, Bool.not_false] at h1 h2
        simp only [z, decide_eq_false_iff_not]
        constructor
        · intro h h'; exact h2 ⟨h, h'⟩
        · intro h; tauto
      · simp [z]
    have hz : ∀ i j k, x i ⊆ x j → z i k = true → z j k = true := by
      intro i j k hij h
      rw [← memz] at h ⊢
      exact hcl _ h _ (Relation.ReflTransGen.single (Or.inl ⟨i, j, k, hij, Or.inl ⟨rfl, rfl⟩⟩))
    obtain ⟨C, p, hM, hR, hout, hp, hsz, hval⟩ := L_lib_1287_aux.build n m t x z hz
    have hw : ∀ i k, wire C i (p k) = z i k := by
      intro i k
      convert hval i k using 3
      unfold L_lib_1287_aux.inp
      congr 2
      funext j
      first
        | exact decide_eq_decide.mpr Iff.rfl
        | (congr 1; exact Subsingleton.elim _ _)
    refine ⟨C, p, ⟨hM, hR, hout, hp, fun i => ?_⟩, hsz, hw⟩
    have : (fun k => wire C i (p k)) = z i := funext fun k => hw i k
    rw [this]
    apply L_lib_1287_aux.baker_pixley (ok i) (hne i) (hmaj i) (z i)
    intro k l
    by_contra hcon
    have harc : arc (i, k, z i k) (i, l, !(z i l)) :=
      Or.inr ⟨i, k, l, z i k, z i l, hcon, rfl, rfl⟩
    have h1 : (i, k, z i k) ∈ S := (memz i k _).mpr rfl
    have h2 := (memz i l _).mp (hcl _ h1 _ (Relation.ReflTransGen.single harc))
    cases h : z i l <;> rw [h] at h2 <;> simp at h2

  let bf : Fin m → Fin n → Bool := fun i j => @decide (j ∈ x i) (Classical.propDecidable _)
  have arcStep : ∀ C p, fits C p → ∀ a b, arc a b →
      wire C a.1 (p a.2.1) = a.2.2 → wire C b.1 (p b.2.1) = b.2.2 := by
    intro C p hf a b hab
    rcases hab with ⟨i, j, k, hij, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨i, k, l, a', b', hno, rfl, rfl⟩
    · intro h
      exact L_lib_1287_aux.wire_mono C hf.1 (bf i) (bf j) (fun s hs => by
        simp only [bf, decide_eq_true_eq] at hs ⊢; exact hij hs) _ h
    · intro h
      dsimp only at h ⊢
      cases h' : wire C i (p k)
      · rfl
      · have := L_lib_1287_aux.wire_mono C hf.1 (bf i) (bf j) (fun s hs => by
          simp only [bf, decide_eq_true_eq] at hs ⊢; exact hij hs) _ h'
        exact absurd (this.symm.trans h) (by simp)
    · intro h
      dsimp only at h ⊢
      have hok := hf.2.2.2.2 i
      cases h' : wire C i (p l)
      · cases b'
        · exact absurd ⟨_, hok, h, h'⟩ hno
        · rfl
      · cases b'
        · rfl
        · exact absurd ⟨_, hok, h, h'⟩ hno
  have preserve : ∀ C p, fits C p → ∀ a b, reach a b →
      wire C a.1 (p a.2.1) = a.2.2 → wire C b.1 (p b.2.1) = b.2.2 := by
    intro C p hf a b hab
    induction hab with
    | refl => exact id
    | tail _ hbc ih => exact fun h => arcStep C p hf _ _ hbc (ih h)
  have existS : clean → ∀ l, ¬ reach l (ng l) → ∃ S : Finset (Fin m × Fin t × Bool), l ∈ S ∧
      (∀ p ∈ S, ∀ q, reach p q → q ∈ S) ∧ (∀ p, p ∈ S ∨ ng p ∈ S) ∧
      (∀ p, ¬ (p ∈ S ∧ ng p ∈ S)) :=
    fun hc l hl => L_lib_1287_aux.two_sat arc ng inv skew (cleanP hc) l hl
  have existS0 : clean → ∃ S : Finset (Fin m × Fin t × Bool),
      (∀ p ∈ S, ∀ q, reach p q → q ∈ S) ∧ (∀ p, p ∈ S ∨ ng p ∈ S) ∧
      (∀ p, ¬ (p ∈ S ∧ ng p ∈ S)) := by
    intro hc
    by_cases hL : Nonempty (Fin m × Fin t × Bool)
    · obtain ⟨l0⟩ := hL
      by_cases h : reach l0 (ng l0)
      · have hl : ¬ reach (ng l0) (ng (ng l0)) := by
          rw [inv]; intro h'; exact cleanP hc l0 ⟨h, h'⟩
        obtain ⟨S, -, h1, h2, h3⟩ := existS hc _ hl
        exact ⟨S, h1, h2, h3⟩
      · obtain ⟨S, -, h1, h2, h3⟩ := existS hc _ h
        exact ⟨S, h1, h2, h3⟩
    · refine ⟨∅, by simp, fun p => absurd ⟨p⟩ hL, by simp⟩
  refine ⟨⟨fun hc => ?_, ?_⟩, fun hc => ?_, fun hc i k v => ⟨fun hnr => ?_, ?_⟩⟩
  · obtain ⟨S, h1, h2, h3⟩ := existS0 hc
    obtain ⟨C, p, hf, -, -⟩ := fromS S h1 h2 h3
    exact ⟨C, p, hf⟩
  · rintro ⟨C, p, hf⟩ i k ⟨h1, h2⟩
    cases hv : wire C i (p k)
    · have := preserve C p hf _ _ h1 hv
      simp [hv] at this
    · have := preserve C p hf _ _ h2 hv
      simp [hv] at this
  · obtain ⟨S, h1, h2, h3⟩ := existS0 hc
    obtain ⟨C, p, hf, hsz, -⟩ := fromS S h1 h2 h3
    exact ⟨C, p, hf, hsz⟩
  · obtain ⟨S, hl, h1, h2, h3⟩ := existS hc (i, k, v) hnr
    obtain ⟨C, p, hf, hsz, hw⟩ := fromS S h1 h2 h3
    refine ⟨C, p, hf, hsz, ?_⟩
    rw [hw]
    cases v
    · have := h2 (i, k, false)
      have h3' := h3 (i, k, false)
      simp only [ng, Bool.not_false] at this h3'
      simp only [decide_eq_false_iff_not]
      intro h; exact h3' ⟨hl, h⟩
    · simpa using hl
  · rintro ⟨C, p, hf, -, hw⟩ hr
    have := preserve C p hf _ _ hr hw
    rw [hw] at this
    cases v <;> simp at this
