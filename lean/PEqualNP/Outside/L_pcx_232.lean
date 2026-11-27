import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_232

abbrev Pat (w : ℕ) : Type := Fin (w + 1) → Bool

abbrev Var (n w : ℕ) : Type := Sum (Fin n) (Fin n × Pat w)

abbrev Pin (n w : ℕ) : Type := PEqualNP.ProofComplexity.Literal (Var n w)

def accepts {n : ℕ} (w : ℕ) (hn : 0 < n) (a : Var n w → Bool) : Prop :=
  ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
    a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true

def fits {n w : ℕ} (pins : Finset (Pin n w)) (a : Var n w → Bool) : Prop :=
  ∀ l ∈ pins, a l.1 = l.2

def core {n : ℕ} (w : ℕ) (hn : 0 < n) (c : Finset (Pin n w)) : Prop :=
  (∃ a, fits c a) ∧ (¬ ∃ a, accepts w hn a ∧ fits c a) ∧
    ∀ e ∈ c, ∃ a, accepts w hn a ∧ fits (c.erase e) a

def win {n : ℕ} (w : ℕ) (hn : 0 < n) (x : Fin n → Bool) (i : Fin n) : Pat w :=
  fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

def rd {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (m : ℕ) : Bool := x ⟨m % n, Nat.mod_lt _ hn⟩

lemma bnot_of_ne : ∀ a b : Bool, a ≠ b → (!a) = b := by decide

lemma bool_ne_not : ∀ b : Bool, b ≠ !b := by decide

lemma win_zero {n : ℕ} (w : ℕ) (hn : 0 < n) (x : Fin n → Bool) (k : Fin n) :
    win w hn x k 0 = x k := by
  show x ⟨(k.val + (0 : Fin (w + 1)).val) % n, Nat.mod_lt _ hn⟩ = x k
  exact congrArg x (Fin.ext (by simp [Nat.mod_eq_of_lt k.isLt]))

lemma rd_congr {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) {a b : ℕ} (h : a % n = b % n) :
    rd hn x a = rd hn x b := by
  show x ⟨a % n, Nat.mod_lt _ hn⟩ = x ⟨b % n, Nat.mod_lt _ hn⟩
  exact congrArg x (Fin.ext h)

lemma rd_val {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (i : Fin n) : rd hn x i.val = x i := by
  show x ⟨i.val % n, Nat.mod_lt _ hn⟩ = x i
  exact congrArg x (Fin.ext (Nat.mod_eq_of_lt i.isLt))

def Unsat {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w)) : Prop :=
  ∀ x : Fin n → Bool, ∃ i : Fin n, (i, win w hn x i) ∈ F

def MinUnsat {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w)) : Prop :=
  Unsat w hn F ∧ ∀ e ∈ F, ∃ x : Fin n → Bool,
    ∀ i : Fin n, (i, win w hn x i) ∈ F → (i, win w hn x i) = e

lemma exists_min {n : ℕ} (w : ℕ) (hn : 0 < n) (G0 : Finset (Fin n × Pat w))
    (h0 : Unsat w hn G0) : ∃ F, F ⊆ G0 ∧ MinUnsat w hn F := by
  classical
  obtain ⟨G, hG, hGmin⟩ := Finset.exists_min_image
    (G0.powerset.filter (fun G => Unsat w hn G)) Finset.card
    ⟨G0, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), h0⟩⟩
  obtain ⟨hGsub, hGU⟩ := Finset.mem_filter.mp hG
  rw [Finset.mem_powerset] at hGsub
  refine ⟨G, hGsub, hGU, fun e he => ?_⟩
  by_contra hno
  push Not at hno
  have hU' : Unsat w hn (G.erase e) := fun x => by
    obtain ⟨i, hi, hne⟩ := hno x
    exact ⟨i, Finset.mem_erase.mpr ⟨hne, hi⟩⟩
  have hle := hGmin (G.erase e) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hGsub), hU'⟩)
  have hlt := Finset.card_erase_lt_of_mem he
  omega

def toPins {n w : ℕ} (F : Finset (Fin n × Pat w)) : Finset (Pin n w) :=
  F.map ⟨fun e => ((Sum.inr e : Var n w), false),
    fun _ _ h => Sum.inr_injective (congrArg Prod.fst h)⟩

lemma mem_toPins {n w : ℕ} {F : Finset (Fin n × Pat w)} {l : Pin n w} :
    l ∈ toPins F ↔ ∃ e ∈ F, ((Sum.inr e : Var n w), false) = l := by
  unfold toPins
  exact Finset.mem_map

lemma card_toPins {n w : ℕ} (F : Finset (Fin n × Pat w)) : (toPins F).card = F.card := by
  unfold toPins
  exact Finset.card_map _

lemma core_toPins {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w))
    (hF : MinUnsat w hn F) : core w hn (toPins F) := by
  obtain ⟨hU, hpriv⟩ := hF
  refine ⟨⟨fun _ => false, ?_⟩, ?_, ?_⟩
  · intro l hl
    obtain ⟨e, -, rfl⟩ := mem_toPins.mp hl
    rfl
  · rintro ⟨a, hacc, hfit⟩
    obtain ⟨i, hi⟩ := hU (fun k => a (Sum.inl k))
    have h1 : a (Sum.inr (i, win w hn (fun k => a (Sum.inl k)) i)) = false :=
      hfit _ (mem_toPins.mpr ⟨_, hi, rfl⟩)
    have h2 : a (Sum.inr (i, win w hn (fun k => a (Sum.inl k)) i)) = true := hacc i
    rw [h2] at h1
    exact absurd h1 (by decide)
  · intro l hl
    obtain ⟨e, he, rfl⟩ := mem_toPins.mp hl
    obtain ⟨x, hx⟩ := hpriv e he
    refine ⟨Sum.elim x (fun e' => decide (e' ∉ F ∨ e' = e)), ?_, ?_⟩
    · intro i
      show decide ((i, win w hn x i) ∉ F ∨ (i, win w hn x i) = e) = true
      apply decide_eq_true
      by_cases hm : (i, win w hn x i) ∈ F
      · exact Or.inr (hx i hm)
      · exact Or.inl hm
    · intro l' hl'
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hl'
      obtain ⟨e', he', rfl⟩ := mem_toPins.mp hmem
      show decide (e' ∉ F ∨ e' = e) = false
      apply decide_eq_false
      rintro (h | h)
      · exact h he'
      · exact hne (by rw [h])

def tab {n w : ℕ} (Q : Finset (Pin n w)) : Finset (Fin n × Pat w) :=
  Finset.univ.filter (fun e : Fin n × Pat w => ((Sum.inr e : Var n w), false) ∈ Q) ∪
    Finset.univ.filter (fun e : Fin n × Pat w => ((Sum.inl e.1 : Var n w), !(e.2 0)) ∈ Q)

lemma mem_tab {n w : ℕ} {Q : Finset (Pin n w)} {e : Fin n × Pat w} :
    e ∈ tab Q ↔ (((Sum.inr e : Var n w), false) ∈ Q ∨
      ((Sum.inl e.1 : Var n w), !(e.2 0)) ∈ Q) := by
  simp [tab]

lemma tab_unsat {n : ℕ} (w : ℕ) (hn : 0 < n) (Q : Finset (Pin n w)) (a0 : Var n w → Bool)
    (ha0 : fits Q a0) (hunsat : ¬ ∃ a, accepts w hn a ∧ fits Q a) : Unsat w hn (tab Q) := by
  intro x
  by_contra hno
  apply hunsat
  refine ⟨Sum.elim x (fun e => decide (((Sum.inr e : Var n w), false) ∉ Q)), ?_, ?_⟩
  · intro i
    show decide (((Sum.inr (i, win w hn x i) : Var n w), false) ∉ Q) = true
    apply decide_eq_true
    intro hmem
    exact hno ⟨i, mem_tab.mpr (Or.inl hmem)⟩
  · rintro ⟨v, b⟩ hl
    cases v with
    | inl k =>
      show x k = b
      by_contra hne
      apply hno
      refine ⟨k, mem_tab.mpr (Or.inr ?_)⟩
      show ((Sum.inl k : Var n w), !(win w hn x k 0)) ∈ Q
      rw [win_zero, bnot_of_ne _ _ hne]
      exact hl
    | inr e =>
      show decide (((Sum.inr e : Var n w), false) ∉ Q) = b
      cases b with
      | false => exact decide_eq_false (fun h => h hl)
      | true =>
        apply decide_eq_true
        intro h
        have h1 : a0 (Sum.inr e) = false := ha0 _ h
        have h2 : a0 (Sum.inr e) = true := ha0 _ hl
        rw [h2] at h1
        exact absurd h1 (by decide)

lemma shape {n : ℕ} (w : ℕ) (hn : 0 < n) (Q : Finset (Pin n w)) (F : Finset (Fin n × Pat w))
    (hF : Unsat w hn F)
    (hsub : ∀ e ∈ F, ((Sum.inr e : Var n w), false) ∈ Q ∨
      ((Sum.inl e.1 : Var n w), !(e.2 0)) ∈ Q)
    (l : Pin n w) (a : Var n w → Bool) (hacc : accepts w hn a) (hfit : fits (Q.erase l) a) :
    ∃ e : Fin n × Pat w, e ∈ F ∧
      ((((Sum.inr e : Var n w), false) = l) ∨ ∃ b : Bool, ((Sum.inl e.1 : Var n w), b) = l) ∧
      (((Sum.inr e : Var n w), false) ∈ Q → ((Sum.inr e : Var n w), false) = l) := by
  obtain ⟨i, hi⟩ := hF (fun k => a (Sum.inl k))
  have hN : ((Sum.inr (i, win w hn (fun k => a (Sum.inl k)) i) : Var n w), false) ∈ Q →
      ((Sum.inr (i, win w hn (fun k => a (Sum.inl k)) i) : Var n w), false) = l := by
    intro hmem
    by_contra hne
    have h1 : a (Sum.inr (i, win w hn (fun k => a (Sum.inl k)) i)) = false :=
      hfit _ (Finset.mem_erase.mpr ⟨hne, hmem⟩)
    have h2 : a (Sum.inr (i, win w hn (fun k => a (Sum.inl k)) i)) = true := hacc i
    rw [h2] at h1
    exact absurd h1 (by decide)
  refine ⟨(i, win w hn (fun k => a (Sum.inl k)) i), hi, ?_, hN⟩
  rcases hsub _ hi with h | h
  · exact Or.inl (hN h)
  · right
    have h' : ((Sum.inl i : Var n w), !(a (Sum.inl i))) ∈ Q := by
      have h'' : ((Sum.inl i : Var n w), !(win w hn (fun k => a (Sum.inl k)) i 0)) ∈ Q := h
      rw [win_zero] at h''
      exact h''
    by_cases hpin : ((Sum.inl i : Var n w), !(a (Sum.inl i))) = l
    · exact ⟨_, hpin⟩
    · exfalso
      have h3 : a (Sum.inl i) = !(a (Sum.inl i)) := hfit _ (Finset.mem_erase.mpr ⟨hpin, h'⟩)
      exact bool_ne_not _ h3

lemma to_table {n : ℕ} (w : ℕ) (hn : 0 < n) (Q : Finset (Pin n w)) (hQ : core w hn Q) :
    ∃ F : Finset (Fin n × Pat w), MinUnsat w hn F ∧ Q.card ≤ F.card := by
  obtain ⟨⟨a0, ha0⟩, hunsat, hmin⟩ := hQ
  obtain ⟨F, hsub, hF⟩ := exists_min w hn (tab Q) (tab_unsat w hn Q a0 ha0 hunsat)
  have hex : ∀ l : Pin n w, ∃ e : Fin n × Pat w, l ∈ Q →
      (e ∈ F ∧
        ((((Sum.inr e : Var n w), false) = l) ∨ ∃ b : Bool, ((Sum.inl e.1 : Var n w), b) = l) ∧
        (((Sum.inr e : Var n w), false) ∈ Q → ((Sum.inr e : Var n w), false) = l)) := by
    intro l
    by_cases hl : l ∈ Q
    · obtain ⟨a, hacc, hfit⟩ := hmin l hl
      obtain ⟨e, he⟩ := shape w hn Q F hF.1 (fun e he => mem_tab.mp (hsub he)) l a hacc hfit
      exact ⟨e, fun _ => he⟩
    · exact ⟨(⟨0, hn⟩, fun _ => false), fun h => absurd h hl⟩
  choose psi hpsi using hex
  refine ⟨F, hF, Finset.card_le_card_of_injOn psi (fun l hl => (hpsi l hl).1) ?_⟩
  intro l1 h1 l2 h2 heq
  have h1' : l1 ∈ Q := h1
  have h2' : l2 ∈ Q := h2
  obtain ⟨-, hs1, hn1⟩ := hpsi l1 h1'
  obtain ⟨-, hs2, hn2⟩ := hpsi l2 h2'
  rw [← heq] at hs2 hn2
  rcases hs1 with t1 | ⟨b1, w1⟩
  · have hm : ((Sum.inr (psi l1) : Var n w), false) ∈ Q := by rw [t1]; exact h1'
    exact t1.symm.trans (hn2 hm)
  · rcases hs2 with t2 | ⟨b2, w2⟩
    · have hm : ((Sum.inr (psi l1) : Var n w), false) ∈ Q := by rw [t2]; exact h2'
      exact (hn1 hm).symm.trans t2
    · have m1 : ((Sum.inl (psi l1).1 : Var n w), b1) ∈ Q := by rw [w1]; exact h1'
      have m2 : ((Sum.inl (psi l1).1 : Var n w), b2) ∈ Q := by rw [w2]; exact h2'
      have e1 : a0 (Sum.inl (psi l1).1) = b1 := ha0 _ m1
      have e2 : a0 (Sum.inl (psi l1).1) = b2 := ha0 _ m2
      exact w1.symm.trans ((congrArg (fun b => ((Sum.inl (psi l1).1 : Var n w), b))
        (e1.symm.trans e2)).trans w2)

lemma card_le_two_pow {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w))
    (hF : MinUnsat w hn F) : F.card ≤ 2 ^ n := by
  obtain ⟨hU, hpriv⟩ := hF
  have hex : ∀ e : Fin n × Pat w, ∃ x : Fin n → Bool, e ∈ F →
      ∀ i : Fin n, (i, win w hn x i) ∈ F → (i, win w hn x i) = e := by
    intro e
    by_cases he : e ∈ F
    · obtain ⟨x, hx⟩ := hpriv e he
      exact ⟨x, fun _ => hx⟩
    · exact ⟨fun _ => false, fun h => absurd h he⟩
  choose X hX using hex
  have hinj : Set.InjOn X (F : Set (Fin n × Pat w)) := by
    intro e1 h1 e2 h2 heq
    obtain ⟨i, hi⟩ := hU (X e1)
    have a1 := hX e1 h1 i hi
    rw [heq] at hi a1
    have a2 := hX e2 h2 i hi
    exact a1.symm.trans a2
  have h := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (Fin n → Bool))) X
    (fun e _ => Finset.mem_univ _) hinj
  have hc : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  rw [hc] at h
  exact h

def ind {n : ℕ} (w : ℕ) (hn : 0 < n) (e : Fin n × Pat w) (x : Fin n → Bool) : ℚ :=
  if win w hn x e.1 = e.2 then 1 else 0

lemma ind_nonneg {n : ℕ} (w : ℕ) (hn : 0 < n) (e : Fin n × Pat w) (x : Fin n → Bool) :
    0 ≤ ind w hn e x := by
  unfold ind
  split_ifs <;> norm_num

lemma ind_self {n : ℕ} (w : ℕ) (hn : 0 < n) (x : Fin n → Bool) (i : Fin n) :
    ind w hn (i, win w hn x i) x = 1 := by
  show (if win w hn x i = win w hn x i then (1 : ℚ) else 0) = 1
  exact ite_eq_left rfl

lemma ind_priv_self {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w))
    (hU : Unsat w hn F) (e : Fin n × Pat w) (x : Fin n → Bool)
    (hx : ∀ i : Fin n, (i, win w hn x i) ∈ F → (i, win w hn x i) = e) : ind w hn e x = 1 := by
  obtain ⟨i, hi⟩ := hU x
  have h := hx i hi
  rw [← h]
  exact ind_self w hn x i

lemma ind_priv_ne {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w))
    (e e' : Fin n × Pat w) (he' : e' ∈ F) (hne : e' ≠ e) (x : Fin n → Bool)
    (hx : ∀ i : Fin n, (i, win w hn x i) ∈ F → (i, win w hn x i) = e) : ind w hn e' x = 0 := by
  show (if win w hn x e'.1 = e'.2 then (1 : ℚ) else 0) = 0
  apply ite_eq_right
  intro h
  apply hne
  have h2 : (e'.1, win w hn x e'.1) = e' := Prod.ext rfl h
  have h3 : (e'.1, win w hn x e'.1) ∈ F := by rw [h2]; exact he'
  exact h2.symm.trans (hx e'.1 h3)

lemma sum_priv {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w)) (hU : Unsat w hn F)
    (c : Fin n × Pat w → ℚ) (e : Fin n × Pat w) (he : e ∈ F) (x : Fin n → Bool)
    (hx : ∀ i : Fin n, (i, win w hn x i) ∈ F → (i, win w hn x i) = e) :
    ∑ e' ∈ F, c e' * ind w hn e' x = c e := by
  have h0 : ∀ e' ∈ F, e' ≠ e → c e' * ind w hn e' x = 0 := fun e' he' hne => by
    rw [ind_priv_ne w hn F e e' he' hne x hx, mul_zero]
  rw [Finset.sum_eq_single_of_mem e he h0, ind_priv_self w hn F hU e x hx, mul_one]

def Kf {n : ℕ} (hn : 0 < n) (s k : ℕ) (q : ℕ → Bool) : (Fin n → Bool) → ℚ :=
  fun x => if rd hn x s = true ∧ ∀ j < k, rd hn x (s + 1 + j) = q j then 1 else 0

def Hf {n : ℕ} (hn : 0 < n) (s k : ℕ) (q : ℕ → Bool) : (Fin n → Bool) → ℚ :=
  fun x => if ∀ j < k, rd hn x (s + j) = q j then 1 else 0

def gfam {n : ℕ} (w : ℕ) (hn : 0 < n) :
    Option (Fin n × (Fin w → Bool)) → ((Fin n → Bool) → ℚ)
  | none => fun _ => 1
  | some ir => Kf hn ir.1.val w (fun j => if hj : j < w then ir.2 ⟨j, hj⟩ else false)

lemma ite_split (r : Bool) (A B C1 C2 : Prop) [Decidable (A ∧ B)] [Decidable C1] [Decidable C2]
    (h1 : C1 ↔ A ∧ B ∧ r = true) (h2 : C2 ↔ A ∧ B ∧ r = false) :
    (if A ∧ B then (1 : ℚ) else 0) = (if C1 then (1 : ℚ) else 0) + (if C2 then (1 : ℚ) else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> cases r <;> simp [h1, h2, hA, hB]

lemma ite_false_case (r : Bool) (B C : Prop) [Decidable C] [Decidable B]
    [Decidable (r = true ∧ B)] (h : C ↔ r = false ∧ B) :
    (if C then (1 : ℚ) else 0) =
      (if B then (1 : ℚ) else 0) - (if r = true ∧ B then (1 : ℚ) else 0) := by
  by_cases hB : B <;> cases r <;> simp [h, hB]

lemma K_top {n : ℕ} (w : ℕ) (hn : 0 < n) (s : ℕ) (q : ℕ → Bool) :
    Kf hn s w q ∈ Submodule.span ℚ (Set.range (gfam w hn)) := by
  have h : Kf hn s w q =
      gfam w hn (some (⟨s % n, Nat.mod_lt _ hn⟩, fun j : Fin w => q j.val)) := by
    funext x
    show (if rd hn x s = true ∧ ∀ j < w, rd hn x (s + 1 + j) = q j then (1 : ℚ) else 0) =
      (if rd hn x (s % n) = true ∧ ∀ j < w, rd hn x (s % n + 1 + j) =
        (if _hj : j < w then q j else false) then (1 : ℚ) else 0)
    have e1 : rd hn x (s % n) = rd hn x s := rd_congr hn x (Nat.mod_mod _ _)
    have e2 : ∀ j, rd hn x (s % n + 1 + j) = rd hn x (s + 1 + j) := fun j =>
      rd_congr hn x (((Nat.mod_modEq s n).add_right 1).add_right j)
    refine if_congr (and_congr (by rw [e1]) ⟨fun h j hj => ?_, fun h j hj => ?_⟩) rfl rfl
    · rw [e2, dite_eq_left hj]
      exact h j hj
    · have h1 := h j hj
      rw [e2, dite_eq_left hj] at h1
      exact h1
  rw [h]
  exact Submodule.subset_span ⟨_, rfl⟩

lemma K_mem {n : ℕ} (w : ℕ) (hn : 0 < n) : ∀ (d k : ℕ), k + d = w → ∀ (s : ℕ) (q : ℕ → Bool),
    Kf hn s k q ∈ Submodule.span ℚ (Set.range (gfam w hn)) := by
  intro d
  induction d with
  | zero =>
    intro k hk s q
    have hkw : k = w := by omega
    rw [hkw]
    exact K_top w hn s q
  | succ d ih =>
    intro k hk s q
    have hsplit : Kf hn s k q = Kf hn s (k + 1) (Function.update q k true) +
        Kf hn s (k + 1) (Function.update q k false) := by
      funext x
      have hb : ∀ b : Bool, (∀ j < k + 1, rd hn x (s + 1 + j) = Function.update q k b j) ↔
          ((∀ j < k, rd hn x (s + 1 + j) = q j) ∧ rd hn x (s + 1 + k) = b) := by
        intro b
        constructor
        · intro h
          refine ⟨fun j hj => ?_, ?_⟩
          · have h1 := h j (by omega)
            rw [Function.update_of_ne (show j ≠ k by omega)] at h1
            exact h1
          · have h1 := h k (by omega)
            rw [Function.update_self] at h1
            exact h1
        · rintro ⟨h1, h2⟩ j hj
          by_cases hjk : j = k
          · rw [hjk, Function.update_self]
            exact h2
          · rw [Function.update_of_ne hjk]
            exact h1 j (by omega)
      exact ite_split (rd hn x (s + 1 + k)) (rd hn x s = true)
        (∀ j < k, rd hn x (s + 1 + j) = q j) _ _
        (and_congr Iff.rfl (hb true)) (and_congr Iff.rfl (hb false))
    rw [hsplit]
    exact Submodule.add_mem _ (ih (k + 1) (by omega) s _) (ih (k + 1) (by omega) s _)

lemma H_mem {n : ℕ} (w : ℕ) (hn : 0 < n) : ∀ (k : ℕ), k ≤ w + 1 → ∀ (s : ℕ) (q : ℕ → Bool),
    Hf hn s k q ∈ Submodule.span ℚ (Set.range (gfam w hn)) := by
  intro k
  induction k with
  | zero =>
    intro _ s q
    have h : Hf hn s 0 q = gfam w hn none := by
      funext x
      simp [Hf, gfam]
    rw [h]
    exact Submodule.subset_span ⟨none, rfl⟩
  | succ k ih =>
    intro hk s q
    have hK := K_mem w hn (w - k) k (by omega) s (fun j => q (j + 1))
    have hH := ih (by omega) (s + 1) (fun j => q (j + 1))
    have hc : ∀ x : Fin n → Bool, (∀ j < k + 1, rd hn x (s + j) = q j) ↔
        (rd hn x s = q 0 ∧ ∀ j < k, rd hn x (s + 1 + j) = q (j + 1)) := by
      intro x
      constructor
      · intro h
        refine ⟨h 0 (by omega), fun j hj => ?_⟩
        have h1 := h (j + 1) (by omega)
        rw [show s + (j + 1) = s + 1 + j by omega] at h1
        exact h1
      · rintro ⟨h0, h1⟩ j hj
        cases j with
        | zero => exact h0
        | succ j =>
          have h2 := h1 j (by omega)
          rw [show s + 1 + j = s + (j + 1) by omega] at h2
          exact h2
    cases hq : q 0 with
    | true =>
      have hsplit : Hf hn s (k + 1) q = Kf hn s k (fun j => q (j + 1)) := by
        funext x
        exact if_congr ((hc x).trans (by rw [hq])) rfl rfl
      rw [hsplit]
      exact hK
    | false =>
      have hsplit : Hf hn s (k + 1) q =
          Hf hn (s + 1) k (fun j => q (j + 1)) - Kf hn s k (fun j => q (j + 1)) := by
        funext x
        exact ite_false_case (rd hn x s) (∀ j < k, rd hn x (s + 1 + j) = q (j + 1)) _
          ((hc x).trans (by rw [hq]))
      rw [hsplit]
      exact Submodule.sub_mem _ hH hK

lemma ind_mem {n : ℕ} (w : ℕ) (hn : 0 < n) (e : Fin n × Pat w) :
    ind w hn e ∈ Submodule.span ℚ (Set.range (gfam w hn)) := by
  have h : ind w hn e =
      Hf hn e.1.val (w + 1) (fun j => if hj : j < w + 1 then e.2 ⟨j, hj⟩ else false) := by
    funext x
    show (if win w hn x e.1 = e.2 then (1 : ℚ) else 0) =
      (if ∀ j < w + 1, rd hn x (e.1.val + j) =
        (if hj : j < w + 1 then e.2 ⟨j, hj⟩ else false) then (1 : ℚ) else 0)
    refine if_congr ⟨fun h j hj => ?_, fun h => ?_⟩ rfl rfl
    · rw [dite_eq_left hj]
      exact congrFun h ⟨j, hj⟩
    · funext j
      have h1 := h j.val j.isLt
      rw [dite_eq_left j.isLt] at h1
      exact h1
  rw [h]
  exact H_mem w hn (w + 1) (le_refl _) _ _

def vfam {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w))
    (g : (Fin n → Bool) → ℚ) :
    Option {e : Fin n × Pat w // e ∈ F} → ((Fin n → Bool) → ℚ)
  | none => g
  | some e => ind w hn e.1

lemma la_bound {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w))
    (hF : MinUnsat w hn F) (g : (Fin n → Bool) → ℚ)
    (hg : g ∈ Submodule.span ℚ (Set.range (gfam w hn)))
    (hcert : ∀ (c0 : ℚ) (c : Fin n × Pat w → ℚ),
      (∀ x : Fin n → Bool, c0 * g x + ∑ e ∈ F, c e * ind w hn e x = 0) → c0 = 0) :
    F.card ≤ n * 2 ^ w := by
  have hli : LinearIndependent ℚ (vfam w hn F g) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hx : ∀ x : Fin n → Bool, c none * g x +
        ∑ e ∈ F, (if he : e ∈ F then c (some ⟨e, he⟩) else 0) * ind w hn e x = 0 := by
      intro x
      have h := congrFun hc x
      rw [Fintype.sum_option] at h
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        vfam] at h
      have hsum : ∑ e ∈ F, (if he : e ∈ F then c (some ⟨e, he⟩) else 0) * ind w hn e x =
          ∑ e : {e : Fin n × Pat w // e ∈ F}, c (some e) * ind w hn e.1 x := by
        rw [← Finset.sum_coe_sort F
          (fun e => (if he : e ∈ F then c (some ⟨e, he⟩) else 0) * ind w hn e x)]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rcases e with ⟨e, he⟩
        simp only [dite_eq_left he]
      rw [hsum]
      exact h
    have h0 : c none = 0 := hcert _ _ hx
    intro o
    cases o with
    | none => exact h0
    | some e0 =>
      obtain ⟨x, hx0⟩ := hF.2 e0.1 e0.2
      have h := hx x
      rw [h0, zero_mul, zero_add,
        sum_priv w hn F hF.1 (fun e => if he : e ∈ F then c (some ⟨e, he⟩) else 0)
          e0.1 e0.2 x hx0] at h
      have h3 : (if he : e0.1 ∈ F then c (some ⟨e0.1, he⟩) else 0) = 0 := h
      rw [dite_eq_left e0.2] at h3
      exact h3
  have hrange : Set.range (vfam w hn F g) ⊆
      (Submodule.span ℚ (Set.range (gfam w hn)) : Set ((Fin n → Bool) → ℚ)) := by
    rintro _ ⟨o, rfl⟩
    cases o with
    | none => exact hg
    | some e => exact ind_mem w hn e.1
  have h1 := linearIndependent_iff_card_eq_finrank_span.mp hli
  have h2 : (Set.range (vfam w hn F g)).finrank ℚ ≤ (Set.range (gfam w hn)).finrank ℚ :=
    Submodule.finrank_mono (Submodule.span_le.mpr hrange)
  have h3 := finrank_range_le_card (R := ℚ) (gfam w hn)
  have c1 : Fintype.card (Option {e : Fin n × Pat w // e ∈ F}) = F.card + 1 := by
    rw [Fintype.card_option, Fintype.card_coe]
  have c2 : Fintype.card (Option (Fin n × (Fin w → Bool))) = n * 2 ^ w + 1 := by
    simp [Fintype.card_option, Fintype.card_prod]
  have hfin : F.card + 1 ≤ n * 2 ^ w + 1 := by
    rw [← c1, ← c2, h1]
    exact h2.trans h3
  exact Nat.le_of_succ_le_succ hfin

lemma mod_ne (n a j w : ℕ) (hn : w + 2 ≤ n) (hj : j ≤ w) :
    (a + j) % n ≠ (a + w + 1) % n := by
  intro h
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  have h2 : a + w + 1 - (a + j) = w + 1 - j := by omega
  rw [h2, Nat.mod_eq_of_lt (show w + 1 - j < n by omega)] at h1
  omega

lemma perfect_bound {n : ℕ} (w : ℕ) (hn : 0 < n) (F : Finset (Fin n × Pat w))
    (hF : MinUnsat w hn F)
    (hperf : ∀ (x : Fin n → Bool) (i1 i2 : Fin n), i1 ≠ i2 → (i1, win w hn x i1) ∈ F →
      (i2, win w hn x i2) ∉ F)
    (y y' : Fin n → Bool) (i0 j0 : Fin n) (hy : (i0, win w hn y i0) ∈ F)
    (hw : win w hn y' i0 = win w hn y i0) (hg : y j0 = false) (hg' : y' j0 = true) :
    F.card ≤ n * 2 ^ w := by
  have hind : ∀ e ∈ F, ind w hn e y' = ind w hn e y := by
    intro e he
    by_cases hs : e.1 = i0
    · show (if win w hn y' e.1 = e.2 then (1 : ℚ) else 0) =
        (if win w hn y e.1 = e.2 then (1 : ℚ) else 0)
      rw [hs, hw]
    · have a1 : ¬ (win w hn y' e.1 = e.2) := by
        intro h
        refine hperf y' i0 e.1 (Ne.symm hs) (by rw [hw]; exact hy) ?_
        rw [h]
        exact he
      have a2 : ¬ (win w hn y e.1 = e.2) := by
        intro h
        refine hperf y i0 e.1 (Ne.symm hs) hy ?_
        rw [h]
        exact he
      show (if win w hn y' e.1 = e.2 then (1 : ℚ) else 0) =
        (if win w hn y e.1 = e.2 then (1 : ℚ) else 0)
      rw [ite_eq_right a1, ite_eq_right a2]
  refine la_bound w hn F hF (Kf hn j0.val 0 (fun _ => false))
    (K_mem w hn w 0 (by omega) _ _) ?_
  intro c0 c hc
  have h1 := hc y
  have h2 := hc y'
  have hs : ∑ e ∈ F, c e * ind w hn e y' = ∑ e ∈ F, c e * ind w hn e y :=
    Finset.sum_congr rfl (fun e he => by rw [hind e he])
  rw [hs] at h2
  have g1 : Kf hn j0.val 0 (fun _ => false) y = 0 := by
    simp [Kf, rd_val, hg]
  have g2 : Kf hn j0.val 0 (fun _ => false) y' = 1 := by
    simp [Kf, rd_val, hg']
  rw [g1] at h1
  rw [g2] at h2
  linarith

lemma card_le_mul {n : ℕ} (w : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) (F : Finset (Fin n × Pat w))
    (hF : MinUnsat w hn F) : F.card ≤ n * 2 ^ w := by
  by_cases hnw : n ≤ w + 1
  · calc F.card ≤ 2 ^ n := card_le_two_pow w hn F hF
      _ ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by norm_num) hnw
      _ = 2 * 2 ^ w := by ring
      _ ≤ n * 2 ^ w := Nat.mul_le_mul_right _ h2
  by_cases hperf : ∃ (x : Fin n → Bool) (i1 i2 : Fin n), i1 ≠ i2 ∧
      (i1, win w hn x i1) ∈ F ∧ (i2, win w hn x i2) ∈ F
  · obtain ⟨xs, i1, i2, hne, hm1, hm2⟩ := hperf
    refine la_bound w hn F hF (fun _ => 1) (Submodule.subset_span ⟨none, rfl⟩) ?_
    intro c0 c hc
    have hce : ∀ e ∈ F, c e = -c0 := by
      intro e he
      obtain ⟨x, hx⟩ := hF.2 e he
      have h : c0 * 1 + ∑ e' ∈ F, c e' * ind w hn e' x = 0 := hc x
      rw [sum_priv w hn F hF.1 c e he x hx] at h
      linarith
    have h : c0 * 1 + ∑ e ∈ F, c e * ind w hn e xs = 0 := hc xs
    have hs : ∑ e ∈ F, c e * ind w hn e xs = -c0 * ∑ e ∈ F, ind w hn e xs := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e he => by rw [hce e he])
    rw [hs] at h
    have hm : (2 : ℚ) ≤ ∑ e ∈ F, ind w hn e xs := by
      have hsub : ({(i1, win w hn xs i1), (i2, win w hn xs i2)} : Finset (Fin n × Pat w)) ⊆
          F := by
        intro e he
        rcases Finset.mem_insert.mp he with h | h
        · rw [h]
          exact hm1
        · rw [Finset.mem_singleton.mp h]
          exact hm2
      have hle : ∑ e ∈ ({(i1, win w hn xs i1), (i2, win w hn xs i2)} :
          Finset (Fin n × Pat w)), ind w hn e xs ≤ ∑ e ∈ F, ind w hn e xs :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => ind_nonneg w hn e xs)
      rw [Finset.sum_pair (fun h => hne (congrArg Prod.fst h)), ind_self, ind_self] at hle
      linarith
    have hz : c0 * ((∑ e ∈ F, ind w hn e xs) - 1) =
        -(c0 * 1 + -c0 * ∑ e ∈ F, ind w hn e xs) := by ring
    rw [h, neg_zero] at hz
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact h0
    · linarith
  · push Not at hperf
    obtain ⟨i0, hi0⟩ := hF.1 (fun _ => false)
    have hne : ∀ j : Fin (w + 1), (⟨(i0.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) ≠
        ⟨(i0.val + w + 1) % n, Nat.mod_lt _ hn⟩ := by
      intro j heq
      have hj := j.isLt
      exact mod_ne n i0.val j.val w (by omega) (by omega) (congrArg Fin.val heq)
    exact perfect_bound w hn F hF hperf (fun _ => false)
      (Function.update (fun _ : Fin n => false) ⟨(i0.val + w + 1) % n, Nat.mod_lt _ hn⟩ true) i0
      ⟨(i0.val + w + 1) % n, Nat.mod_lt _ hn⟩ hi0
      (by
        funext j
        exact Function.update_of_ne (hne j) true (fun _ : Fin n => false))
      rfl (Function.update_self _ _ _)

lemma win_w0 {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (i : Fin n) :
    win 0 hn x i = fun _ => x i := by
  funext j
  show x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ = x i
  exact congrArg x (Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt]))

lemma card_w0 {n : ℕ} (hn : 0 < n) (F : Finset (Fin n × Pat 0)) (hF : MinUnsat 0 hn F) :
    F.card = 2 := by
  obtain ⟨hU, hpriv⟩ := hF
  have hex : ∃ i : Fin n, ∀ b : Bool, (i, (fun _ => b : Pat 0)) ∈ F := by
    by_contra hno
    push Not at hno
    choose B hB using hno
    obtain ⟨i, hi⟩ := hU B
    rw [win_w0] at hi
    exact hB i hi
  obtain ⟨i, hi⟩ := hex
  have hne : ((i, fun _ => false) : Fin n × Pat 0) ≠ (i, fun _ => true) := by
    intro h
    have h2 : false = true := congrFun (congrArg Prod.snd h) 0
    exact absurd h2 (by decide)
  have hF2 : F = {(i, (fun _ => false : Pat 0)), (i, (fun _ => true : Pat 0))} := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨x, hx⟩ := hpriv e he
      have h3 : (i, win 0 hn x i) ∈ F := by
        rw [win_w0]
        exact hi (x i)
      have h4 := hx i h3
      rw [← h4, win_w0]
      by_cases hx0 : x i = true
      · rw [hx0]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · rw [Bool.eq_false_iff.mpr hx0]
        exact Finset.mem_insert_self _ _
    · intro e he
      rcases Finset.mem_insert.mp he with h | h
      · rw [h]
        exact hi false
      · rw [Finset.mem_singleton.mp h]
        exact hi true
  rw [hF2, Finset.card_pair hne]

lemma fin2_ext (p q : Pat 1) (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  funext k
  fin_cases k
  · exact h0
  · exact h1

def Fx (n : ℕ) : Finset (Fin n × Pat 1) :=
  Finset.univ.filter (fun e => e.2 1 = (if e.1.val + 1 = n then e.2 0 else !(e.2 0)))

lemma mem_Fx {n : ℕ} (e : Fin n × Pat 1) :
    e ∈ Fx n ↔ e.2 1 = (if e.1.val + 1 = n then e.2 0 else !(e.2 0)) := by
  simp [Fx]

lemma hit_Fx {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (j : Fin n) :
    (j, win 1 hn x j) ∈ Fx n ↔
      x ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩ = (if j.val + 1 = n then x j else !(x j)) := by
  rw [mem_Fx]
  show win 1 hn x j 1 = (if j.val + 1 = n then win 1 hn x j 0 else !(win 1 hn x j 0)) ↔
    x ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩ = (if j.val + 1 = n then x j else !(x j))
  rw [win_zero]
  exact Iff.rfl

lemma Fx_unsat {n : ℕ} (hn : 0 < n) : Unsat 1 hn (Fx n) := by
  intro x
  by_contra hno
  have hall : ∀ k (hk : k < n), x ⟨k, hk⟩ = x ⟨0, hn⟩ := by
    intro k
    induction k with
    | zero =>
      intro _
      rfl
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      rw [← ih hk']
      by_contra hne
      apply hno
      refine ⟨⟨k, hk'⟩, ?_⟩
      rw [hit_Fx]
      show x ⟨(k + 1) % n, Nat.mod_lt _ hn⟩ =
        (if k + 1 = n then x ⟨k, hk'⟩ else !(x ⟨k, hk'⟩))
      rw [ite_eq_right (show ¬ (k + 1 = n) by omega)]
      have e : (⟨(k + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨k + 1, hk⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hk)
      rw [e]
      exact (bnot_of_ne _ _ (Ne.symm hne)).symm
  have hlast : n - 1 < n := by omega
  apply hno
  refine ⟨⟨n - 1, hlast⟩, ?_⟩
  rw [hit_Fx]
  show x ⟨(n - 1 + 1) % n, Nat.mod_lt _ hn⟩ =
    (if n - 1 + 1 = n then x ⟨n - 1, hlast⟩ else !(x ⟨n - 1, hlast⟩))
  rw [ite_eq_left (show n - 1 + 1 = n by omega)]
  have e : (⟨(n - 1 + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ := by
    apply Fin.ext
    show (n - 1 + 1) % n = 0
    rw [show n - 1 + 1 = n by omega, Nat.mod_self]
  rw [e, hall (n - 1) hlast]

lemma Fx_priv {n : ℕ} (hn : 0 < n) (e : Fin n × Pat 1) (he : e ∈ Fx n) :
    ∃ x : Fin n → Bool, ∀ j : Fin n, (j, win 1 hn x j) ∈ Fx n → (j, win 1 hn x j) = e := by
  rcases e with ⟨i, p⟩
  rw [mem_Fx] at he
  have he' : p 1 = (if i.val + 1 = n then p 0 else !(p 0)) := he
  refine ⟨fun j => if j.val ≤ i.val then p 0 else p 1, fun j hj => ?_⟩
  rw [hit_Fx] at hj
  have hj' : (if (j.val + 1) % n ≤ i.val then p 0 else p 1) =
      (if j.val + 1 = n then (if j.val ≤ i.val then p 0 else p 1)
        else !(if j.val ≤ i.val then p 0 else p 1)) := hj
  have hil := i.isLt
  have hjl := j.isLt
  rcases Nat.lt_trichotomy j.val i.val with hlt | heq | hgt
  · exfalso
    rw [Nat.mod_eq_of_lt (show j.val + 1 < n by omega),
      ite_eq_left (show j.val + 1 ≤ i.val by omega),
      ite_eq_right (show ¬ (j.val + 1 = n) by omega),
      ite_eq_left (show j.val ≤ i.val by omega)] at hj'
    exact bool_ne_not _ hj'
  · have hji : j = i := Fin.ext heq
    rw [hji]
    refine Prod.ext rfl ?_
    show win 1 hn (fun j' : Fin n => if j'.val ≤ i.val then p 0 else p 1) i = p
    apply fin2_ext
    · rw [win_zero]
      exact ite_eq_left (le_refl _)
    · show (if (i.val + 1) % n ≤ i.val then p 0 else p 1) = p 1
      by_cases hin : i.val + 1 = n
      · rw [hin, Nat.mod_self, ite_eq_left (Nat.zero_le _), he', ite_eq_left hin]
      · rw [Nat.mod_eq_of_lt (show i.val + 1 < n by omega),
          ite_eq_right (show ¬ (i.val + 1 ≤ i.val) by omega)]
  · exfalso
    have hp : p 1 = !(p 0) := by
      rw [he', ite_eq_right (show ¬ (i.val + 1 = n) by omega)]
    by_cases hjn : j.val + 1 = n
    · rw [hjn, Nat.mod_self, ite_eq_left (Nat.zero_le _), ite_eq_left rfl,
        ite_eq_right (show ¬ (j.val ≤ i.val) by omega), hp] at hj'
      exact bool_ne_not _ hj'
    · rw [Nat.mod_eq_of_lt (show j.val + 1 < n by omega),
        ite_eq_right (show ¬ (j.val + 1 ≤ i.val) by omega),
        ite_eq_right hjn,
        ite_eq_right (show ¬ (j.val ≤ i.val) by omega)] at hj'
      exact bool_ne_not _ hj'

lemma Fx_card {n : ℕ} : 2 * n ≤ (Fx n).card := by
  have h := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Fin n × Bool))) (t := Fx n)
    (fun ib => (ib.1, fun k : Fin (1 + 1) =>
      if k.val = 0 then ib.2 else (if ib.1.val + 1 = n then ib.2 else !ib.2)))
    (fun ib _ => by
      rw [Finset.mem_coe, mem_Fx]
      rfl)
    (by
      intro a _ b _ hab
      have h1 : a.1 = b.1 := by
        have h3 := congrArg Prod.fst hab
        exact h3
      have h2 : a.2 = b.2 := by
        have h3 := congrFun (congrArg Prod.snd hab) 0
        exact h3
      exact Prod.ext h1 h2)
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
  omega

lemma main (n w : ℕ) (hn : 0 < n) :
    ∃ P : Finset (Pin n w), core w hn P ∧
      (∀ l ∈ P, ∃ i : Fin n, ∃ p : Pat w, l = (Sum.inr (i, p), false)) ∧
      (∀ Q, core w hn Q → Q.card ≤ P.card) ∧
      P.card ≤ min (2 ^ n) (max 2 (n * 2 ^ w)) ∧
      (w = 0 → P.card = 2) ∧ (w = 1 → P.card = 2 * n) := by
  classical
  obtain ⟨G0, -, hG0⟩ := exists_min w hn (Finset.univ : Finset (Fin n × Pat w))
    (fun _ => ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
  obtain ⟨F, hFm, hFmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun F : Finset (Fin n × Pat w) => MinUnsat w hn F)) Finset.card
    ⟨G0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG0⟩⟩
  have hF : MinUnsat w hn F := (Finset.mem_filter.mp hFm).2
  have hmax : ∀ F' : Finset (Fin n × Pat w), MinUnsat w hn F' → F'.card ≤ F.card :=
    fun F' hF' => hFmax F' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF'⟩)
  have h2n := card_le_two_pow w hn F hF
  refine ⟨toPins F, core_toPins w hn F hF, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨e, -, rfl⟩ := mem_toPins.mp hl
    exact ⟨e.1, e.2, rfl⟩
  · intro Q hQ
    obtain ⟨F', hF', hle⟩ := to_table w hn Q hQ
    rw [card_toPins]
    exact hle.trans (hmax F' hF')
  · rw [card_toPins]
    refine le_min h2n ?_
    by_cases h2 : 2 ≤ n
    · exact (card_le_mul w hn h2 F hF).trans (le_max_right _ _)
    · have h1 : 2 ^ n = 2 := by
        have hn1 : n = 1 := by omega
        simp [hn1]
      rw [h1] at h2n
      exact h2n.trans (le_max_left _ _)
  · intro hw
    subst hw
    rw [card_toPins]
    exact card_w0 hn F hF
  · intro hw
    subst hw
    rw [card_toPins]
    apply le_antisymm
    · by_cases h2 : 2 ≤ n
      · have h3 := card_le_mul 1 hn h2 F hF
        rw [pow_one] at h3
        omega
      · have h1 : 2 ^ n = 2 := by
          have hn1 : n = 1 := by omega
          simp [hn1]
        rw [h1] at h2n
        omega
    · have h3 := hmax (Fx n) ⟨Fx_unsat hn, fun e he => Fx_priv hn e he⟩
      have h4 := Fx_card (n := n)
      omega

end PEqualNP.Outside.L_pcx_232

theorem PEqualNP.Outside.L_pcx_232 : (∀ (n w : ℕ) (hn : 0 < n),
  let Pat := Fin (w + 1) → Bool
  let V := Sum (Fin n) (Fin n × Pat)
  let Pin := PEqualNP.ProofComplexity.Literal V
  let accepts := fun (a : V → Bool) =>
    ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true
  let fits := fun (pins : Finset Pin) (a : V → Bool) => ∀ l ∈ pins, a l.1 = l.2
  let core := fun (candidate : Finset Pin) =>
    (∃ a, fits candidate a) ∧ (¬ ∃ a, accepts a ∧ fits candidate a) ∧
    ∀ e ∈ candidate, ∃ a, accepts a ∧ fits (candidate.erase e) a
  ∃ P : Finset Pin, core P ∧
    (∀ l ∈ P, ∃ i : Fin n, ∃ p : Pat, l = (Sum.inr (i, p), false)) ∧
    (∀ Q, core Q → Q.card ≤ P.card) ∧
    P.card ≤ min (2 ^ n) (max 2 (n * 2 ^ w)) ∧
    (w = 0 → P.card = 2) ∧ (w = 1 → P.card = 2 * n)) := by
  intro n w hn
  exact PEqualNP.Outside.L_pcx_232.main n w hn
