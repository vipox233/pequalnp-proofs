import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_993_aux

-- Part T: runs of a parity decision tree (copied from the merged step L-lib-992).

def adv_st (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) : List Bool :=
  (List.range k).foldl (fun (p : List Bool) _ => if p ∈ T then p ++ [b p] else p) []

theorem adv_st_succ (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) :
    adv_st T b (k + 1) = if adv_st T b k ∈ T then adv_st T b k ++ [b (adv_st T b k)] else adv_st T b k := by
  have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
  unfold adv_st
  rw [hr, List.foldl_append]
  rfl

theorem adv_st_inv (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) :
    (adv_st T b k).length ≤ k ∧ ((adv_st T b k).length = k ∨ adv_st T b k ∉ T) ∧
      ∀ j < (adv_st T b k).length, (adv_st T b k).take j ∈ T := by
  induction k with
  | zero => simp [adv_st]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [adv_st_succ]
    by_cases hk : adv_st T b k ∈ T
    · rw [if_pos hk]
      have hl : (adv_st T b k).length = k := by
        rcases h2 with h2 | h2
        · exact h2
        · exact absurd hk h2
      refine ⟨by simp [hl], Or.inl (by simp [hl]), ?_⟩
      intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjk : j < (adv_st T b k).length
      · rw [List.take_append_of_le_length (by omega)]
        exact h3 j hjk
      · have hjeq : j = (adv_st T b k).length := by omega
        rw [hjeq, List.take_left]
        exact hk
    · rw [if_neg hk]
      exact ⟨by omega, Or.inr hk, h3⟩

theorem adv_st_stat (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) (hk : adv_st T b k ∉ T) :
    ∀ i, adv_st T b (k + i) = adv_st T b k := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← Nat.add_assoc, adv_st_succ, ih, if_neg hk]

theorem adv_st_prefix (T : Finset (List Bool)) (b : List Bool → Bool) (k : Nat) :
    ∀ i, adv_st T b k <+: adv_st T b (k + i) := by
  intro i
  induction i with
  | zero => exact List.prefix_refl _
  | succ i ih =>
    rw [← Nat.add_assoc, adv_st_succ]
    by_cases hq : adv_st T b (k + i) ∈ T
    · rw [if_pos hq]
      exact ih.trans (List.prefix_append _ _)
    · rw [if_neg hq]
      exact ih

theorem adv_st_take (T : Finset (List Bool)) (b : List Bool → Bool) (N k : Nat) (hk : k ≤ N) :
    adv_st T b k = (adv_st T b N).take k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨h1, h2, -⟩ := adv_st_inv T b k
  rcases h2 with h2 | h2
  · have h := List.prefix_iff_eq_take.mp (adv_st_prefix T b k i)
    rw [h2] at h
    exact h
  · rw [adv_st_stat T b k h2 i, List.take_of_length_le h1]

theorem adv_st_bit (T : Finset (List Bool)) (b : List Bool → Bool) (N j : Nat)
    (hj : j < (adv_st T b N).length) :
    (adv_st T b N).take (j + 1) = (adv_st T b N).take j ++ [b ((adv_st T b N).take j)] := by
  have hN := (adv_st_inv T b N).1
  have h1 := adv_st_take T b N j (by omega)
  have h2 := adv_st_take T b N (j + 1) (by omega)
  rw [adv_st_succ] at h2
  by_cases hq : adv_st T b j ∈ T
  · rw [if_pos hq] at h2
    rw [← h1, ← h2]
  · rw [if_neg hq] at h2
    have h3 := congrArg List.length (h1.symm.trans h2)
    simp only [List.length_take] at h3
    omega

theorem adv_st_congr (T : Finset (List Bool)) (b b' : List Bool → Bool) (N : Nat)
    (h : ∀ j < (adv_st T b N).length, b' ((adv_st T b N).take j) = b ((adv_st T b N).take j)) :
    adv_st T b' N = adv_st T b N := by
  have key : ∀ k ≤ N, adv_st T b' k = adv_st T b k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      rw [adv_st_succ, adv_st_succ, ih']
      by_cases hq : adv_st T b k ∈ T
      · rw [if_pos hq, if_pos hq]
        have hlen : (adv_st T b k).length = k := by
          rcases (adv_st_inv T b k).2.1 with h2 | h2
          · exact h2
          · exact absurd hq h2
        have htk : adv_st T b k = (adv_st T b N).take k := adv_st_take T b N k (by omega)
        have hk1 := adv_st_take T b N (k + 1) hk
        rw [adv_st_succ, if_pos hq] at hk1
        have hlt : k < (adv_st T b N).length := by
          have h4 := congrArg List.length hk1
          simp only [List.length_append, List.length_singleton, List.length_take, hlen] at h4
          omega
        have hb : b' (adv_st T b k) = b (adv_st T b k) := by
          rw [htk]
          exact h k hlt
        rw [hb]
      · rw [if_neg hq, if_neg hq]
  exact key N le_rfl

theorem adv_st_bits_eq (T : Finset (List Bool)) (b b' : List Bool → Bool) (N : Nat)
    (h : adv_st T b' N = adv_st T b N) :
    ∀ j < (adv_st T b N).length, b' ((adv_st T b N).take j) = b ((adv_st T b N).take j) := by
  intro j hj
  have e1 := adv_st_bit T b N j hj
  have e2 := adv_st_bit T b' N j (by rw [h]; exact hj)
  rw [h] at e2
  have e3 := e1.symm.trans e2
  rw [List.append_cancel_left_eq, List.singleton_inj] at e3
  exact e3.symm

theorem adv_st_leaf (T : Finset (List Bool)) (b : List Bool → Bool) :
    adv_st T b T.card ∉ T ∧ ∀ j < (adv_st T b T.card).length, (adv_st T b T.card).take j ∈ T := by
  obtain ⟨h1, h2, h3⟩ := adv_st_inv T b T.card
  refine ⟨?_, h3⟩
  intro hmem
  rcases h2 with h2 | h2
  · have hsub : (Finset.range (T.card + 1)).image (fun j => (adv_st T b T.card).take j) ⊆ T := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      rw [Finset.mem_range] at hj
      by_cases hjk : j < T.card
      · exact h3 j (by omega)
      · have hjeq : j = (adv_st T b T.card).length := by omega
        rw [hjeq, List.take_length]
        exact hmem
    have hcard : ((Finset.range (T.card + 1)).image
        (fun j => (adv_st T b T.card).take j)).card = T.card + 1 := by
      rw [Finset.card_image_of_injOn]
      · exact Finset.card_range _
      · intro i hi j hj hij
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        have h4 := congrArg List.length hij
        simp only [List.length_take] at h4
        omega
    have := Finset.card_le_card hsub
    omega
  · exact h2 hmem

theorem adv_decomp (p : List Bool) : ∃ r : List Bool, ∃ k : Nat,
    p = r ++ List.replicate k true ∧ (r = [] ∨ ∃ q, r = q ++ [false]) := by
  induction p using List.reverseRecOn with
  | nil => exact ⟨[], 0, rfl, Or.inl rfl⟩
  | append_singleton p a ih =>
    cases a with
    | false => exact ⟨p ++ [false], 0, by simp, Or.inr ⟨p, rfl⟩⟩
    | true =>
      obtain ⟨r, k, hp, hr⟩ := ih
      refine ⟨r, k + 1, ?_, hr⟩
      rw [hp, List.replicate_succ', List.append_assoc]

theorem leaf_card {X : Type*} (Ω : Finset X) (T : Finset (List Bool)) (b : X → List Bool → Bool) :
    (Ω.image (fun x => adv_st T (b x) T.card)).card ≤ T.card + 1 := by
  classical
  set R := Ω.image (fun x => adv_st T (b x) T.card) with hR
  have hleaf : ∀ p ∈ R, p ∉ T ∧ ∀ j < p.length, p.take j ∈ T := by
    intro p hp
    rw [hR, Finset.mem_image] at hp
    obtain ⟨x, -, rfl⟩ := hp
    exact adv_st_leaf T (b x)
  have hpre : ∀ p ∈ R, ∀ p' ∈ R, p <+: p' → p = p' := by
    intro p hp p' hp' hpp
    by_contra hne
    have hlt : p.length < p'.length := by
      rcases Nat.lt_or_ge p.length p'.length with h | h
      · exact h
      · exact absurd (hpp.eq_of_length_le h) hne
    have h5 := (hleaf p' hp').2 p.length hlt
    rw [← List.prefix_iff_eq_take.mp hpp] at h5
    exact (hleaf p hp).1 h5
  let θ : List Bool → List Bool := fun p => (adv_decomp p).choose
  have hθ : ∀ p, ∃ k, p = θ p ++ List.replicate k true ∧ (θ p = [] ∨ ∃ q, θ p = q ++ [false]) :=
    fun p => (adv_decomp p).choose_spec
  have hmaps : ∀ p ∈ R, θ p ∈ insert [] (T.image (fun q => q ++ [false])) := by
    intro p hp
    obtain ⟨k, hk, hr⟩ := hθ p
    rcases hr with hr | ⟨q, hq⟩
    · rw [hr]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_image]
      refine ⟨q, ?_, hq.symm⟩
      have hqp : q = p.take q.length := by
        rw [hk, hq, List.append_assoc, List.take_left]
      have hlt : q.length < p.length := by
        rw [hk, hq]
        simp only [List.length_append, List.length_singleton, List.length_replicate]
        omega
      rw [hqp]
      exact (hleaf p hp).2 q.length hlt
  have hinj : Set.InjOn θ (R : Set (List Bool)) := by
    intro p hp p' hp' hpp
    obtain ⟨k, hk, -⟩ := hθ p
    obtain ⟨k', hk', -⟩ := hθ p'
    rcases Nat.le_total k k' with h | h
    · apply hpre p hp p' hp'
      rw [hk, hk', hpp]
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [List.replicate_add, ← List.append_assoc]
      exact List.prefix_append _ _
    · symm
      apply hpre p' hp' p hp
      rw [hk, hk', hpp]
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [List.replicate_add, ← List.append_assoc]
      exact List.prefix_append _ _
  calc R.card ≤ (insert [] (T.image (fun q => q ++ [false]))).card :=
        Finset.card_le_card_of_injOn θ (fun p hp => hmaps p hp) hinj
    _ ≤ (T.image (fun q => q ++ [false])).card + 1 := Finset.card_insert_le _ _
    _ ≤ T.card + 1 := by
        have := Finset.card_image_le (s := T) (f := fun q => q ++ [false])
        omega

-- the tree part: a largest leaf is a coset of a subspace U, and 2^(n+m) is at most (card T + 1) 2^(dim U)

abbrev XX (m : ℕ) := Fin m → Fin 2 → ZMod 2
abbrev QQ := Fin 2 → ZMod 2

open Classical in
theorem tree_part {m : ℕ} (Ω : Finset (XX m)) (hΩ : Ω.Nonempty) (T : Finset (List Bool))
    (ask : List Bool → XX m →ₗ[ZMod 2] ZMod 2) (bias : List Bool → ZMod 2) :
    ∃ x0 ∈ Ω, ∃ U : Submodule (ZMod 2) (XX m),
      (∀ u ∈ U, adv_st T (fun p => decide (ask p (x0 + u) + bias p ≠ 0)) T.card =
        adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card) ∧
      Ω.card ≤ (T.card + 1) * (Ω.filter (fun x => x - x0 ∈ U)).card := by
  classical
  set leaf : XX m → List Bool :=
    fun x => adv_st T (fun p => decide (ask p x + bias p ≠ 0)) T.card with hleaf
  set R := Ω.image leaf with hR
  have hRc : R.card ≤ T.card + 1 := leaf_card Ω T (fun x p => decide (ask p x + bias p ≠ 0))
  have hpig : ∃ p0 ∈ R, Ω.card ≤ R.card * (Ω.filter (fun x => leaf x = p0)).card := by
    by_contra hcon
    push_neg at hcon
    have hsum := Finset.card_eq_sum_card_fiberwise (f := leaf) (s := Ω) (t := R)
      (fun x hx => Finset.mem_image_of_mem leaf hx)
    have hne : R.Nonempty := hΩ.image leaf
    have hlt := Finset.sum_lt_sum_of_nonempty hne hcon
    rw [← Finset.mul_sum, ← hsum, Finset.sum_const, smul_eq_mul] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨p0, hp0R, hp0⟩ := hpig
  rw [hR, Finset.mem_image] at hp0R
  obtain ⟨x0, hx0Ω, hx0⟩ := hp0R
  have hp0e : adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card = p0 := hx0
  let U : Submodule (ZMod 2) (XX m) :=
    ⨅ j : Fin p0.length, LinearMap.ker (ask (p0.take j))
  have hcongr : ∀ x, (∀ j < p0.length, ask (p0.take j) x = ask (p0.take j) x0) →
      adv_st T (fun p => decide (ask p x + bias p ≠ 0)) T.card =
        adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card := by
    intro x hx
    apply adv_st_congr
    rw [hp0e]
    intro j hj
    show decide (ask (p0.take j) x + bias (p0.take j) ≠ 0) =
      decide (ask (p0.take j) x0 + bias (p0.take j) ≠ 0)
    rw [hx j hj]
  have hconv : ∀ x, leaf x = leaf x0 → ∀ j < p0.length, ask (p0.take j) x = ask (p0.take j) x0 := by
    intro x hx j hj
    have h1 := adv_st_bits_eq T (fun p => decide (ask p x0 + bias p ≠ 0))
      (fun p => decide (ask p x + bias p ≠ 0)) T.card hx
    rw [hp0e] at h1
    have h2 : decide (ask (p0.take j) x + bias (p0.take j) ≠ 0) =
        decide (ask (p0.take j) x0 + bias (p0.take j) ≠ 0) := h1 j hj
    have key : ∀ a b c : ZMod 2, decide (a + c ≠ 0) = decide (b + c ≠ 0) → a = b := by decide
    exact key _ _ _ h2
  have hmemU : ∀ x, leaf x = p0 → x - x0 ∈ U := by
    intro x hx
    rw [Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker, map_sub, hconv x (hx.trans hx0.symm) j j.2, sub_self]
  refine ⟨x0, hx0Ω, U, fun u hu => ?_, ?_⟩
  · apply hcongr
    intro j hj
    have h1 : ask (p0.take j) u = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hu ⟨j, hj⟩)
    rw [map_add, h1, add_zero]
  · calc Ω.card ≤ R.card * (Ω.filter (fun x => leaf x = p0)).card := hp0
      _ ≤ (T.card + 1) * (Ω.filter (fun x => x - x0 ∈ U)).card := by
        apply Nat.mul_le_mul hRc
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hmemU x hx.2⟩

-- Part F: a tree asking fixed questions (adapted from L-lib-992).

noncomputable def C_tree : ℕ → Finset (List Bool)
  | 0 => ∅
  | k + 1 => insert [] ((C_tree k).image (List.cons true) ∪ (C_tree k).image (List.cons false))

theorem C_tree_zero : C_tree 0 = ∅ := rfl

theorem C_tree_succ (k : ℕ) : C_tree (k + 1) =
    insert [] ((C_tree k).image (List.cons true) ∪ (C_tree k).image (List.cons false)) := rfl

theorem C_tree_mem (k : ℕ) : ∀ p : List Bool, p ∈ C_tree k ↔ p.length < k := by
  induction k with
  | zero =>
    intro p
    rw [C_tree_zero]
    exact ⟨fun hp => absurd hp (Finset.notMem_empty p), fun hp => absurd hp (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro p
    rw [C_tree_succ, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (hp | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · rw [hp]
        exact Nat.succ_pos k
      · exact Nat.succ_lt_succ ((ih a).mp ha)
      · exact Nat.succ_lt_succ ((ih a).mp ha)
    · intro hp
      cases p with
      | nil => exact Or.inl rfl
      | cons b q =>
        have hq : q ∈ C_tree k := (ih q).mpr (Nat.lt_of_succ_lt_succ hp)
        cases b with
        | true => exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
        | false => exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

theorem C_tree_card (k : ℕ) : (C_tree k).card + 1 = 2 ^ k := by
  induction k with
  | zero => simp [C_tree_zero]
  | succ k ih =>
    have hA : ((C_tree k).image (List.cons true)).card = (C_tree k).card :=
      Finset.card_image_of_injective _ List.cons_injective
    have hB : ((C_tree k).image (List.cons false)).card = (C_tree k).card :=
      Finset.card_image_of_injective _ List.cons_injective
    have hdisj : Disjoint ((C_tree k).image (List.cons true)) ((C_tree k).image (List.cons false)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [Finset.mem_image] at hp1 hp2
      obtain ⟨a, _, rfl⟩ := hp1
      obtain ⟨b, _, hb⟩ := hp2
      exact absurd (List.cons.inj hb).1 (by decide)
    have hnil : ([] : List Bool) ∉
        (C_tree k).image (List.cons true) ∪ (C_tree k).image (List.cons false) := by
      intro hm
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hm
      rcases hm with ⟨a, _, ha⟩ | ⟨a, _, ha⟩
      · exact List.cons_ne_nil _ _ ha
      · exact List.cons_ne_nil _ _ ha
    rw [C_tree_succ, Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hdisj, hA, hB,
      pow_succ]
    omega
theorem C_foldl_iter {α β : Type} (g : α → α) (l : List β) (a : α) :
    l.foldl (fun p _ => g p) a = Nat.iterate g l.length a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih (g a)

theorem C_iter {α : Type} (g : α → α) (f : ℕ → α) (h : ℕ)
    (hs : ∀ k, k < h → g (f k) = f (k + 1)) (hh : g (f h) = f h) :
    ∀ k, Nat.iterate g k (f 0) = f (min k h) := by
  intro k
  induction k with
  | zero =>
    show f 0 = f (min 0 h)
    rw [Nat.zero_min]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rcases Nat.lt_or_ge k h with hk | hk
    · have e1 : min k h = k := Nat.min_eq_left (Nat.le_of_lt hk)
      have e2 : min (k + 1) h = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hk)
      rw [e1, e2]
      exact hs k hk
    · have e1 : min k h = h := Nat.min_eq_right hk
      have e2 : min (k + 1) h = h := Nat.min_eq_right (Nat.le_succ_of_le hk)
      rw [e1, e2]
      exact hh


noncomputable def F_hist {m h : ℕ} (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (s : XX m) (k : ℕ) : List Bool :=
  (List.range k).map (fun j => if hj : j < h then decide (ask ⟨j, hj⟩ s ≠ 0) else false)

theorem F_hist_length {m h : ℕ} (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (s : XX m) (k : ℕ) : (F_hist ask s k).length = k := by
  rw [F_hist, List.length_map, List.length_range]

theorem F_hist_succ {m h : ℕ} (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (s : XX m) (k : ℕ) (hk : k < h) :
    F_hist ask s (k + 1) = F_hist ask s k ++ [decide (ask ⟨k, hk⟩ s ≠ 0)] := by
  rw [F_hist, F_hist, List.range_succ, List.map_append]
  show _ ++ [if hj : k < h then decide (ask ⟨k, hj⟩ s ≠ 0) else false] = _
  rw [dite_eq_left hk]

noncomputable def F_ask {m h : ℕ} (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (p : List Bool) : XX m →ₗ[ZMod 2] ZMod 2 :=
  if hp : p.length < h then ask ⟨p.length, hp⟩ else 0

theorem F_ask_hist {m h : ℕ} (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (x : XX m) (k : ℕ) (hk : k < h) :
    F_ask ask (F_hist ask x k) x = ask ⟨k, hk⟩ x := by
  have hl : (F_hist ask x k).length < h := by
    rw [F_hist_length]
    exact hk
  have hf : (⟨(F_hist ask x k).length, hl⟩ : Fin h) = ⟨k, hk⟩ :=
    Fin.ext (F_hist_length ask x k)
  rw [F_ask, dite_eq_left hl, hf]

noncomputable def F_step {m h : ℕ} (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (x : XX m) (bias : List Bool → ZMod 2) (p : List Bool) : List Bool :=
  if p ∈ C_tree h then p ++ [decide (F_ask ask p x + bias p ≠ 0)] else p

theorem F_run {m h : ℕ} (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (x : XX m) (bias : List Bool → ZMod 2) (hb : ∀ p, bias p = 0) :
    (List.range (C_tree h).card).foldl (fun (p : List Bool) (_ : ℕ) =>
      if p ∈ C_tree h then p ++ [decide (F_ask ask p x + bias p ≠ 0)] else p) [] =
      F_hist ask x h := by
  have hs : ∀ k, k < h → F_step ask x bias (F_hist ask x k) = F_hist ask x (k + 1) := by
    intro k hk
    have hmem : F_hist ask x k ∈ C_tree h := by
      rw [C_tree_mem, F_hist_length]
      exact hk
    rw [F_step, ite_eq_left hmem, F_ask_hist ask x k hk, hb, add_zero, F_hist_succ ask x k hk]
  have hh : F_step ask x bias (F_hist ask x h) = F_hist ask x h := by
    have hmem : F_hist ask x h ∉ C_tree h := by
      rw [C_tree_mem, F_hist_length]
      exact Nat.lt_irrefl h
    rw [F_step, ite_eq_right hmem]
  have hN : h ≤ (C_tree h).card := by
    have h1 := C_tree_card h
    have h2 : h < 2 ^ h := Nat.lt_two_pow_self
    omega
  have hit := C_iter (F_step ask x bias) (F_hist ask x) h hs hh (C_tree h).card
  rw [Nat.min_eq_right hN] at hit
  exact (C_foldl_iter (F_step ask x bias) (List.range (C_tree h).card) []).trans
    ((congrArg (fun t => Nat.iterate (F_step ask x bias) t [])
      (List.length_range (n := (C_tree h).card))).trans hit)

noncomputable def C_dec (h : ℕ) (p : List Bool) : Fin h → ZMod 2 :=
  fun j => if p[j.val]? = some true then 1 else 0

theorem C_bit2 : ∀ a : ZMod 2, (if some (decide (a ≠ 0)) = some true then (1 : ZMod 2) else 0) = a := by
  decide

theorem F_dec_hist {m h : ℕ} (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (s : XX m) : C_dec h (F_hist ask s h) = fun j => ask j s := by
  funext j
  have e1 : (F_hist ask s h)[j.val]? = some (decide (ask j s ≠ 0)) := by
    rw [F_hist, List.getElem?_map, List.getElem?_range j.isLt]
    show some (if hj : j.val < h then decide (ask ⟨j.val, hj⟩ s ≠ 0) else false) =
      some (decide (ask j s ≠ 0))
    rw [dite_eq_left j.isLt]
  show (if (F_hist ask s h)[j.val]? = some true then (1 : ZMod 2) else 0) = ask j s
  rw [e1]
  exact C_bit2 (ask j s)

def errs {m : ℕ} (P : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (d : Fin m → ZMod 2) (x : XX m) :
    Finset (Fin m) :=
  Finset.univ.filter (fun i => x i 0 * x i 1 ≠ P i x + d i)

theorem fixed_tree {m e L h : ℕ} (good : XX m → Prop) (ask : Fin h → XX m →ₗ[ZMod 2] ZMod 2)
    (P : (Fin h → ZMod 2) → Fin m → XX m →ₗ[ZMod 2] ZMod 2)
    (d : (Fin h → ZMod 2) → Fin m → ZMod 2) (hL : 2 ^ h ≤ L)
    (hok : ∀ x, good x → (errs (P (fun j => ask j x)) (d (fun j => ask j x)) x).card ≤ e) :
    ∃ (T : Finset (List Bool)) (ask' : List Bool → XX m →ₗ[ZMod 2] ZMod 2)
      (bias : List Bool → ZMod 2) (P' : List Bool → Fin m → XX m →ₗ[ZMod 2] ZMod 2)
      (d' : List Bool → Fin m → ZMod 2),
      T.card < L ∧ ∀ x, good x →
        (errs (P' ((List.range T.card).foldl (fun (p : List Bool) _ =>
            if p ∈ T then p ++ [decide (ask' p x + bias p ≠ 0)] else p) []))
          (d' ((List.range T.card).foldl (fun (p : List Bool) _ =>
            if p ∈ T then p ++ [decide (ask' p x + bias p ≠ 0)] else p) [])) x).card ≤ e := by
  refine ⟨C_tree h, F_ask ask, fun _ => 0, fun p => P (C_dec h p), fun p => d (C_dec h p), ?_, ?_⟩
  · have h1 := C_tree_card h
    omega
  · intro x hx
    have key := (congrArg (C_dec h) (F_run ask x (fun _ => 0) (fun _ => rfl))).trans
      (F_dec_hist ask x)
    beta_reduce
    rw [key]
    exact hok x hx

-- Part G: translation of predictors.

def projL {m : ℕ} (i : Fin m) (u : Fin 2) : XX m →ₗ[ZMod 2] ZMod 2 where
  toFun x := x i u
  map_add' x y := rfl
  map_smul' a x := rfl

theorem projL_apply {m : ℕ} (i : Fin m) (u : Fin 2) (x : XX m) : projL i u x = x i u := rfl

theorem translate {m : ℕ} (P : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (d : Fin m → ZMod 2) (x0 : XX m) :
    ∃ (P' : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (d' : Fin m → ZMod 2),
      ∀ v, errs P' d' (x0 + v) = errs P d v := by
  refine ⟨fun i => P i + x0 i 0 • projL i 1 + x0 i 1 • projL i 0,
    fun i => d i - P i x0 - x0 i 0 * x0 i 1, fun v => ?_⟩
  unfold errs
  apply Finset.filter_congr
  intro i _
  simp only [LinearMap.add_apply, LinearMap.smul_apply, projL_apply, Pi.add_apply, smul_eq_mul,
    map_add]
  constructor <;> intro h1 h2 <;> apply h1 <;> linear_combination h2

-- the syndrome map

def syn {m : ℕ} (c : Fin m → Fin 2 → QQ) : XX m →ₗ[ZMod 2] QQ where
  toFun x j := ∑ i, ∑ u, c i u j * x i u
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro u _
    ring

theorem syn_apply {m : ℕ} (c : Fin m → Fin 2 → QQ) (x : XX m) (j : Fin 2) :
    syn c x j = ∑ i, ∑ u, c i u j * x i u := rfl

-- Glue for the upper bound: questions S whose common kernel inside ker syn is good.

theorem upper_glue {m e L : ℕ} (c : Fin m → Fin 2 → QQ) (base : XX m)
    (S : Finset (XX m →ₗ[ZMod 2] ZMod 2)) (hL : 2 ^ S.card ≤ L)
    (P : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (d : Fin m → ZMod 2)
    (hgood : ∀ x, syn c x = 0 → (∀ f ∈ S, f x = 0) → (errs P d x).card ≤ e) :
    ∃ (T : Finset (List Bool)) (ask' : List Bool → XX m →ₗ[ZMod 2] ZMod 2)
      (bias : List Bool → ZMod 2) (P' : List Bool → Fin m → XX m →ₗ[ZMod 2] ZMod 2)
      (d' : List Bool → Fin m → ZMod 2),
      T.card < L ∧ ∀ x, syn c x = syn c base →
        (errs (P' ((List.range T.card).foldl (fun (p : List Bool) _ =>
            if p ∈ T then p ++ [decide (ask' p x + bias p ≠ 0)] else p) []))
          (d' ((List.range T.card).foldl (fun (p : List Bool) _ =>
            if p ∈ T then p ++ [decide (ask' p x + bias p ≠ 0)] else p) [])) x).card ≤ e := by
  classical
  let ask : Fin S.card → XX m →ₗ[ZMod 2] ZMod 2 := fun j => (S.equivFin.symm j).val
  have hpt : ∀ y : Fin S.card → ZMod 2, ∃ (P' : Fin m → XX m →ₗ[ZMod 2] ZMod 2)
      (d' : Fin m → ZMod 2), ∀ x, syn c x = syn c base → (fun j => ask j x) = y →
        (errs P' d' x).card ≤ e := by
    intro y
    by_cases hex : ∃ x0, syn c x0 = syn c base ∧ (fun j => ask j x0) = y
    · obtain ⟨x0, hx0, hy0⟩ := hex
      obtain ⟨P', d', hPd⟩ := translate P d x0
      refine ⟨P', d', fun x hx hy => ?_⟩
      have hxx : x = x0 + (x - x0) := by abel
      rw [hxx, hPd]
      apply hgood
      · rw [map_sub, hx, hx0, sub_self]
      · intro f hf
        have h1 := congrFun (hy.trans hy0.symm) (S.equivFin ⟨f, hf⟩)
        simp only [ask, Equiv.symm_apply_apply] at h1
        rw [map_sub, h1, sub_self]
    · refine ⟨P, d, fun x hx hy => absurd ⟨x, hx, hy⟩ hex⟩
  choose P' d' hPd using hpt
  exact fixed_tree (fun x => syn c x = syn c base) ask P' d' hL
    (fun x hx => hPd _ x hx rfl)

-- Glue for the lower bound.

theorem natCard_eq_filter {m : ℕ} (V : Submodule (ZMod 2) (XX m)) [DecidablePred (· ∈ V)] :
    Nat.card V = (Finset.univ.filter (fun x => x ∈ V)).card := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp))

theorem lower_glue {m e L : ℕ} (c : Fin m → Fin 2 → QQ) (base : XX m) (p : ℕ)
    (hcore : ∀ (V : Submodule (ZMod 2) (XX m)), V ≤ LinearMap.ker (syn c) →
      ∀ (x0 : XX m) (P : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (d : Fin m → ZMod 2),
        (∀ v ∈ V, (errs P d (x0 + v)).card ≤ e) →
        2 ^ p * Nat.card V ≤ Nat.card (LinearMap.ker (syn c)))
    (T : Finset (List Bool)) (ask : List Bool → XX m →ₗ[ZMod 2] ZMod 2)
    (bias : List Bool → ZMod 2) (P : List Bool → Fin m → XX m →ₗ[ZMod 2] ZMod 2)
    (d : List Bool → Fin m → ZMod 2) (hT : T.card < L)
    (hok : ∀ x, syn c x = syn c base →
        (errs (P ((List.range T.card).foldl (fun (p : List Bool) _ =>
            if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []))
          (d ((List.range T.card).foldl (fun (p : List Bool) _ =>
            if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) [])) x).card ≤ e) :
    2 ^ p ≤ L := by
  classical
  set Ω := Finset.univ.filter (fun x : XX m => syn c x = syn c base) with hΩ
  have hne : Ω.Nonempty := ⟨base, by simp [hΩ]⟩
  obtain ⟨x0, hx0, U, hU, hcard⟩ := tree_part Ω hne T ask bias
  rw [hΩ, Finset.mem_filter] at hx0
  let V : Submodule (ZMod 2) (XX m) := U ⊓ LinearMap.ker (syn c)
  have hVK : V ≤ LinearMap.ker (syn c) := inf_le_right
  have hgood : ∀ v ∈ V, (errs (P (adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card))
      (d (adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card)) (x0 + v)).card ≤ e := by
    intro v hv
    have hvU : v ∈ U := (Submodule.mem_inf.mp hv).1
    have hvK : syn c v = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hv).2
    have h1 := hok (x0 + v) (by rw [map_add, hvK, add_zero, hx0.2])
    have h2 : (List.range T.card).foldl (fun (p : List Bool) _ =>
        if p ∈ T then p ++ [decide (ask p (x0 + v) + bias p ≠ 0)] else p) [] =
        adv_st T (fun p => decide (ask p x0 + bias p ≠ 0)) T.card := hU v hvU
    rw [h2] at h1
    exact h1
  have hc := hcore V hVK x0 _ _ hgood
  have hK : Nat.card (LinearMap.ker (syn c)) ≤ Ω.card := by
    rw [natCard_eq_filter]
    refine Finset.card_le_card_of_injOn (fun v => base + v) ?_ ?_
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        LinearMap.mem_ker] at hv
      simp only [hΩ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [map_add, hv, add_zero]
    · intro v _ w _ hvw
      exact add_left_cancel hvw
  have hF : (Ω.filter (fun x => x - x0 ∈ U)).card ≤ Nat.card V := by
    rw [natCard_eq_filter]
    refine Finset.card_le_card_of_injOn (fun x => x - x0) ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, hΩ, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      refine Submodule.mem_inf.mpr ⟨hx.2, ?_⟩
      rw [LinearMap.mem_ker, map_sub, hx.1, hx0.2, sub_self]
    · intro x _ y _ hxy
      exact sub_left_inj.mp hxy
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have h3 : 2 ^ p * Nat.card V ≤ L * Nat.card V := by
    calc 2 ^ p * Nat.card V ≤ Nat.card (LinearMap.ker (syn c)) := hc
      _ ≤ Ω.card := hK
      _ ≤ (T.card + 1) * (Ω.filter (fun x => x - x0 ∈ U)).card := hcard
      _ ≤ L * Nat.card V := Nat.mul_le_mul (by omega) hF
  exact Nat.le_of_mul_le_mul_right h3 hVpos

-- Part M: the counting core.

theorem card_eq_pow {m : ℕ} (V : Submodule (ZMod 2) (XX m)) :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [Nat.card_zmod] at h1
  exact h1

def labOf {m : ℕ} (c : Fin m → Fin 2 → QQ) : Finset QQ :=
  (Finset.univ : Finset (Fin m)).biUnion (fun i => ({c i 0, c i 1} : Finset QQ))

noncomputable def hOf {m : ℕ} (c : Fin m → Fin 2 → QQ) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (↑(labOf c) : Set QQ))

def FP {m : ℕ} (c : Fin m → Fin 2 → QQ) : Prop := ∃ i, c i 0 ≠ 0 ∧ c i 1 ≠ 0 ∧ c i 0 ≠ c i 1

def GoodS {m : ℕ} (c : Fin m → Fin 2 → QQ) (e : ℕ) (S : Finset (XX m →ₗ[ZMod 2] ZMod 2)) : Prop :=
  ∃ (P : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (d : Fin m → ZMod 2),
    ∀ x, syn c x = 0 → (∀ f ∈ S, f x = 0) → (errs P d x).card ≤ e

def GoodV {m : ℕ} (e : ℕ) (V : Submodule (ZMod 2) (XX m)) : Prop :=
  ∃ (x0 : XX m) (P : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (d : Fin m → ZMod 2),
    ∀ v ∈ V, (errs P d (x0 + v)).card ≤ e

-- Part P: forcing errors at independent sites.

def rho {m : ℕ} (J : Finset (Fin m)) : XX m →ₗ[ZMod 2] XX m where
  toFun x i := if i ∈ J then x i else 0
  map_add' x y := by
    funext i
    by_cases hi : i ∈ J <;> simp [hi]
  map_smul' a x := by
    funext i
    by_cases hi : i ∈ J <;> simp [hi]

theorem rho_apply {m : ℕ} (J : Finset (Fin m)) (x : XX m) (i : Fin m) :
    rho J x i = if i ∈ J then x i else 0 := rfl

theorem odd_pick (g : QQ →ₗ[ZMod 2] ZMod 2) :
    ∃ w0 w1 : QQ, w0 0 * w0 1 + g w0 = 0 ∧ w1 0 * w1 1 + g w1 = 1 := by
  have hg : ∀ w : QQ, g w = w 0 * g (Pi.single 0 1) + w 1 * g (Pi.single 1 1) := by
    intro w
    have hw : w = w 0 • (Pi.single 0 1 : QQ) + w 1 • (Pi.single 1 1 : QQ) := by
      funext j
      fin_cases j <;> simp
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have key : ∀ a b : ZMod 2, ∃ p0 p1 q0 q1 : ZMod 2,
      p0 * p1 + (p0 * a + p1 * b) = 0 ∧ q0 * q1 + (q0 * a + q1 * b) = 1 := by decide
  obtain ⟨p0, p1, q0, q1, h0, h1⟩ := key (g (Pi.single 0 1)) (g (Pi.single 1 1))
  refine ⟨![p0, p1], ![q0, q1], ?_, ?_⟩
  · rw [hg]
    simpa using h0
  · rw [hg]
    simpa using h1

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem zmod2_two : ∀ a : ZMod 2, a + a = 0 := by decide

theorem PL {m : ℕ} (U : Finset (Fin m)) : ∀ (ℓ : Fin m → XX m →ₗ[ZMod 2] ZMod 2)
    (κ : Fin m → ZMod 2), ∃ z : XX m, ∀ i ∈ U, z i 0 * z i 1 + ℓ i z + κ i ≠ 0 := by
  classical
  induction U using Finset.induction_on with
  | empty => intro ℓ κ; exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert k U' hk ih =>
    intro ℓ κ
    let Z : XX m →ₗ[ZMod 2] XX m := rho (Finset.univ.erase k)
    let sk : QQ →ₗ[ZMod 2] XX m := LinearMap.single (ZMod 2) (fun _ => QQ) k
    let g : QQ →ₗ[ZMod 2] ZMod 2 := (ℓ k).comp sk
    obtain ⟨w0, w1, hw0, hw1⟩ := odd_pick g
    let δ : XX m := sk (w0 + w1)
    let b : XX m := sk w1 + κ k • δ
    let Lφ : XX m →ₗ[ZMod 2] XX m := Z + ((ℓ k).comp Z).smulRight δ
    obtain ⟨z, hz⟩ := ih (fun i => (ℓ i).comp Lφ) (fun i => ℓ i b + κ i)
    have hsk : ∀ (w : QQ) (i : Fin m), sk w i = if i = k then w else 0 := by
      intro w i
      by_cases hi : i = k
      · subst hi
        simp [sk]
      · simp [sk, hi, Pi.single_apply]
    have hZ : ∀ (y : XX m) (i : Fin m), Z y i = if i = k then 0 else y i := by
      intro y i
      by_cases hi : i = k <;> simp [Z, rho_apply, hi]
    have hoff : ∀ i, i ≠ k → (Lφ z + b) i = z i := by
      intro i hik
      simp only [Lφ, b, δ, Pi.add_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        Pi.smul_apply, hZ, hsk, if_neg hik, smul_zero, add_zero]
    have hdec : ∀ y : XX m, ℓ k y = ℓ k (Z y) + g (y k) := by
      intro y
      have hy : y = Z y + sk (y k) := by
        funext i
        rw [Pi.add_apply, hZ, hsk]
        by_cases hi : i = k
        · subst hi
          simp
        · simp [hi]
      conv_lhs => rw [hy]
      rw [map_add]
      rfl
    refine ⟨Lφ z + b, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with hik | hi'
    · subst hik
      set y := Lφ z + b with hydef
      have hZy : Z y = Z z := by
        funext j
        rw [hZ, hZ]
        by_cases hj : j = i
        · simp [hj]
        · rw [if_neg hj, if_neg hj, hoff j hj]
      have hyk : y i = w1 + (ℓ i (Z z) + κ i) • (w0 + w1) := by
        funext u
        simp only [hydef, Lφ, b, δ, Pi.add_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
          Pi.smul_apply, hZ, hsk, ite_true, smul_eq_mul, LinearMap.comp_apply, Pi.zero_apply]
        ring
      rw [hdec y, hZy]
      rcases zmod2_cases (ℓ i (Z z) + κ i) with hν | hν
      · rw [hν, zero_smul, add_zero] at hyk
        rw [hyk]
        have : w1 0 * w1 1 + (ℓ i (Z z) + g w1) + κ i = 1 := by
          linear_combination hw1 + hν
        rw [this]
        decide
      · have hyk' : y i = w0 := by
          rw [hyk, hν, one_smul]
          funext u
          simp only [Pi.add_apply]
          linear_combination zmod2_two (w1 u)
        rw [hyk']
        have : w0 0 * w0 1 + (ℓ i (Z z) + g w0) + κ i = 1 := by
          linear_combination hw0 + hν
        rw [this]
        decide
    · have hik : i ≠ k := fun h => hk (h ▸ hi')
      rw [hoff i hik]
      have h1 := hz i hi'
      simp only [LinearMap.comp_apply] at h1
      rw [map_add]
      intro h2
      apply h1
      linear_combination h2

def Free {m : ℕ} (V : Submodule (ZMod 2) (XX m)) (U : Finset (Fin m)) : Prop :=
  ∃ lift : XX m →ₗ[ZMod 2] XX m, (∀ y, lift y ∈ V) ∧ ∀ y, ∀ i ∈ U, lift y i = y i

theorem free_err {m e : ℕ} (V : Submodule (ZMod 2) (XX m)) (U J : Finset (Fin m))
    (hU : Free V U) (hUJ : U ⊆ J) (x0 : XX m) (P : Fin m → XX m →ₗ[ZMod 2] ZMod 2)
    (d : Fin m → ZMod 2)
    (hgood : ∀ v ∈ V, (J.filter (fun i => (x0 + v) i 0 * (x0 + v) i 1 ≠
      P i (x0 + v) + d i)).card ≤ e) : U.card ≤ e := by
  classical
  obtain ⟨lift, hlV, hlU⟩ := hU
  obtain ⟨z, hz⟩ := PL U (fun i => x0 i 0 • projL i 1 + x0 i 1 • projL i 0 - (P i).comp lift)
    (fun i => x0 i 0 * x0 i 1 - P i x0 - d i)
  refine le_trans (Finset.card_le_card ?_) (hgood (lift z) (hlV z))
  intro i hi
  rw [Finset.mem_filter]
  refine ⟨hUJ hi, ?_⟩
  have h1 := hz i hi
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, projL_apply,
    smul_eq_mul, LinearMap.comp_apply] at h1
  rw [Pi.add_apply, Pi.add_apply, hlU z i hi, map_add]
  intro h2
  apply h1
  simp only [Pi.add_apply] at h2
  linear_combination h2

theorem rho_rho {m : ℕ} (J K : Finset (Fin m)) (hJK : J ⊆ K) (x : XX m) :
    rho J (rho K x) = rho J x := by
  funext i
  simp only [rho_apply]
  by_cases hi : i ∈ J
  · rw [if_pos hi, if_pos hi, if_pos (hJK hi)]
  · rw [if_neg hi, if_neg hi]

theorem dim_step {m : ℕ} (V : Submodule (ZMod 2) (XX m)) (J : Finset (Fin m)) (k : Fin m)
    (hk : k ∉ J) (t : ℕ)
    (hker : ∀ A : Submodule (ZMod 2) QQ,
      (∀ a ∈ A, ∃ v ∈ V, rho J v = 0 ∧ v k = a) → Module.finrank (ZMod 2) A ≤ t) :
    Module.finrank (ZMod 2) (V.map (rho (insert k J))) ≤
      Module.finrank (ZMod 2) (V.map (rho J)) + t := by
  classical
  set A := V.map (rho (insert k J)) with hA
  let f : A →ₗ[ZMod 2] XX m := (rho J).comp A.subtype
  have hrange : LinearMap.range f = V.map (rho J) := by
    apply le_antisymm
    · rintro y ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp ha
      exact Submodule.mem_map.mpr ⟨v, hv, (rho_rho J _ (Finset.subset_insert k J) v).symm⟩
    · rintro y hy
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
      refine ⟨⟨rho (insert k J) v, Submodule.mem_map.mpr ⟨v, hv, rfl⟩⟩, ?_⟩
      exact rho_rho J _ (Finset.subset_insert k J) v
  let g : LinearMap.ker f →ₗ[ZMod 2] QQ :=
    (LinearMap.proj k).comp (A.subtype.comp (LinearMap.ker f).subtype)
  have hg : Function.Injective g := by
    intro a1 a2 h12
    obtain ⟨⟨y1, hy1⟩, hk1⟩ := a1
    obtain ⟨⟨y2, hy2⟩, hk2⟩ := a2
    have e1 : rho J y1 = 0 := LinearMap.mem_ker.mp hk1
    have e2 : rho J y2 = 0 := LinearMap.mem_ker.mp hk2
    obtain ⟨v1, -, rfl⟩ := Submodule.mem_map.mp hy1
    obtain ⟨v2, -, rfl⟩ := Submodule.mem_map.mp hy2
    have hkk : rho (insert k J) v1 k = rho (insert k J) v2 k := h12
    have hyy : rho (insert k J) v1 = rho (insert k J) v2 := by
      funext i
      by_cases hik : i = k
      · subst hik
        exact hkk
      · by_cases hiJ : i ∈ J
        · have f1 := congrFun e1 i
          have f2 := congrFun e2 i
          rw [rho_apply, if_pos hiJ] at f1 f2
          rw [f1, f2]
        · have hni : i ∉ insert k J := by
            rw [Finset.mem_insert]
            push_neg
            exact ⟨hik, hiJ⟩
          rw [rho_apply, rho_apply, if_neg hni, if_neg hni]
    simp only [hyy]
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  have hkerdim : Module.finrank (ZMod 2) (LinearMap.ker f) ≤ t := by
    rw [← LinearMap.finrank_range_of_inj hg]
    apply hker
    rintro a ⟨⟨⟨y, hy⟩, hky⟩, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
    refine ⟨v, hv, ?_, ?_⟩
    · have e1 : rho J (rho (insert k J) v) = 0 := LinearMap.mem_ker.mp hky
      rwa [rho_rho J _ (Finset.subset_insert k J)] at e1
    · show v k = rho (insert k J) v k
      rw [rho_apply, if_pos (Finset.mem_insert_self k J)]
  rw [hrange] at hdim
  omega

theorem free_claim {m : ℕ} (V : Submodule (ZMod 2) (XX m)) (J : Finset (Fin m)) :
    ∃ U ⊆ J, Free V U ∧ Module.finrank (ZMod 2) (V.map (rho J)) ≤ J.card + U.card := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.Subset.refl _, ⟨0, fun y => V.zero_mem, fun y i hi => absurd hi
      (Finset.notMem_empty i)⟩, ?_⟩
    have hb : V.map (rho (∅ : Finset (Fin m))) = ⊥ := by
      rw [eq_bot_iff]
      rintro y hy
      obtain ⟨v, -, rfl⟩ := Submodule.mem_map.mp hy
      rw [Submodule.mem_bot]
      funext i
      simp [rho_apply]
    rw [hb, finrank_bot]
    simp
  | insert k J hk ih =>
    obtain ⟨U, hUJ, ⟨lift, hlV, hlU⟩, hdim⟩ := ih
    by_cases hA : ∀ w : QQ, ∃ v ∈ V, rho J v = 0 ∧ v k = w
    · obtain ⟨g0, hg0V, hg0J, hg0k⟩ := hA (Pi.single 0 1)
      obtain ⟨g1, hg1V, hg1J, hg1k⟩ := hA (Pi.single 1 1)
      let G : QQ →ₗ[ZMod 2] XX m :=
        (LinearMap.proj 0).smulRight g0 + (LinearMap.proj 1).smulRight g1
      have hGV : ∀ w, G w ∈ V := fun w =>
        V.add_mem (V.smul_mem _ hg0V) (V.smul_mem _ hg1V)
      have hGJ : ∀ w, ∀ i ∈ J, G w i = 0 := by
        intro w i hi
        have f0 := congrFun hg0J i
        have f1 := congrFun hg1J i
        rw [rho_apply, if_pos hi] at f0 f1
        simp [G, f0, f1]
      have hGk : ∀ w, G w k = w := by
        intro w
        funext u
        simp only [G, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, hg0k, hg1k]
        fin_cases u <;> simp
      refine ⟨insert k U, Finset.insert_subset_insert k hUJ,
        ⟨lift + G.comp ((LinearMap.proj k) - (LinearMap.proj k).comp lift), fun y => ?_,
          fun y i hi => ?_⟩, ?_⟩
      · exact V.add_mem (hlV y) (hGV _)
      · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.proj_apply, Pi.add_apply]
        rcases Finset.mem_insert.mp hi with rfl | hiU
        · rw [hGk]
          abel
        · rw [hGJ _ i (hUJ hiU), add_zero, hlU y i hiU]
      · have h1 := dim_step V J k hk 2 (fun A _ => by
          have := Submodule.finrank_le A
          simpa using this)
        rw [Finset.card_insert_of_notMem hk,
          Finset.card_insert_of_notMem (fun h => hk (hUJ h))]
        omega
    · push_neg at hA
      obtain ⟨w, hw⟩ := hA
      refine ⟨U, hUJ.trans (Finset.subset_insert k J), ⟨lift, hlV, hlU⟩, ?_⟩
      have h1 := dim_step V J k hk 1 (fun A hAV => by
        have hlt : A < ⊤ := by
          rw [lt_top_iff_ne_top]
          intro htop
          obtain ⟨v, hv, hvJ, hvk⟩ := hAV w (htop ▸ Submodule.mem_top)
          exact hw v hv hvJ hvk
        have := Submodule.finrank_lt (lt_top_iff_ne_top.mp hlt)
        simp at this
        omega)
      rw [Finset.card_insert_of_notMem hk]
      omega

theorem rho_univ {m : ℕ} (x : XX m) : rho Finset.univ x = x := by
  funext i
  simp [rho_apply]

theorem lower_gen_proof {m e : ℕ} (V : Submodule (ZMod 2) (XX m))
    (hV : GoodV e V) : Module.finrank (ZMod 2) V ≤ m + e := by
  classical
  obtain ⟨x0, P, d, hgood⟩ := hV
  obtain ⟨U, -, hU, hdim⟩ := free_claim V Finset.univ
  have hUe := free_err V U Finset.univ hU (Finset.subset_univ U) x0 P d hgood
  have hmap : V.map (rho Finset.univ) = V := by
    ext y
    constructor
    · intro hy
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
      rwa [rho_univ]
    · intro hy
      exact Submodule.mem_map.mpr ⟨y, hy, rho_univ y⟩
  rw [hmap, Finset.card_univ, Fintype.card_fin] at hdim
  omega

-- Part R: ranks.

theorem qq_ne {q : QQ} (hq : q ≠ 0) : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
  by_contra h
  push_neg at h
  apply hq
  funext j
  fin_cases j
  · exact h.1
  · exact h.2

theorem qq_ne2 {q r : QQ} (hq : q ≠ r) : q 0 ≠ r 0 ∨ q 1 ≠ r 1 := by
  by_contra h
  push_neg at h
  apply hq
  funext j
  fin_cases j
  · exact h.1
  · exact h.2

theorem syn_eq_sum {m : ℕ} (c : Fin m → Fin 2 → QQ) (x : XX m) :
    syn c x = ∑ i, ∑ u, x i u • c i u := by
  funext j
  rw [syn_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro u _
  simp [mul_comm]

theorem syn_single {m : ℕ} (c : Fin m → Fin 2 → QQ) (i : Fin m) (u : Fin 2) :
    syn c (Pi.single i (Pi.single u 1)) = c i u := by
  rw [syn_eq_sum, Finset.sum_eq_single i, Finset.sum_eq_single u]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ u) h
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem range_syn {m : ℕ} (c : Fin m → Fin 2 → QQ) :
    LinearMap.range (syn c) = Submodule.span (ZMod 2) (↑(labOf c) : Set QQ) := by
  apply le_antisymm
  · rintro q ⟨x, rfl⟩
    rw [syn_eq_sum]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro u _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [labOf, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    refine ⟨i, ?_⟩
    fin_cases u
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [Submodule.span_le]
    intro q hq
    simp only [labOf, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    obtain ⟨i, hi | hi⟩ := hq
    · exact ⟨_, (syn_single c i 0).trans hi.symm⟩
    · exact ⟨_, (syn_single c i 1).trans hi.symm⟩

theorem finrank_XX (m : ℕ) : Module.finrank (ZMod 2) (XX m) = 2 * m := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_fin_fun, mul_comm]

theorem dimK_proof {m : ℕ} (c : Fin m → Fin 2 → QQ) :
    Module.finrank (ZMod 2) (LinearMap.ker (syn c)) + hOf c = 2 * m := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (syn c)
  rw [range_syn, finrank_XX] at h1
  unfold hOf
  omega

theorem h_le_two_proof {m : ℕ} (c : Fin m → Fin 2 → QQ) : hOf c ≤ 2 := by
  unfold hOf
  have := Submodule.finrank_le (Submodule.span (ZMod 2) (↑(labOf c) : Set QQ))
  simpa [Module.finrank_fin_fun] using this

theorem span_fin : ∀ p0 p1 r0 r1 s0 s1 : ZMod 2, (p0 ≠ 0 ∨ p1 ≠ 0) → (r0 ≠ 0 ∨ r1 ≠ 0) →
    (p0 ≠ r0 ∨ p1 ≠ r1) → ∃ a b : ZMod 2, s0 = a * p0 + b * r0 ∧ s1 = a * p1 + b * r1 := by
  decide

theorem fp_h_proof {m : ℕ} (c : Fin m → Fin 2 → QQ) (hf : FP c) : hOf c = 2 := by
  obtain ⟨i, h0, h1, h01⟩ := hf
  have key := span_fin
  have htop : Submodule.span (ZMod 2) (↑(labOf c) : Set QQ) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨a, b, ha, hb⟩ := key _ _ _ _ (q 0) (q 1) (qq_ne h0) (qq_ne h1) (qq_ne2 h01)
    have hq : q = a • c i 0 + b • c i 1 := by
      funext j
      fin_cases j
      · simpa using ha
      · simpa using hb
    rw [hq]
    have m0 : c i 0 ∈ (↑(labOf c) : Set QQ) := by
      simp [labOf]
      exact ⟨i, Or.inl rfl⟩
    have m1 : c i 1 ∈ (↑(labOf c) : Set QQ) := by
      simp [labOf]
      exact ⟨i, Or.inr rfl⟩
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span m0))
      (Submodule.smul_mem _ _ (Submodule.subset_span m1))
  unfold hOf
  rw [htop, finrank_top]
  simp [Module.finrank_fin_fun]

theorem indep_fin0 : ∀ p0 p1 r0 r1 a b : ZMod 2, ((p0 ≠ 0 ∨ p1 ≠ 0) ∧ (r0 ≠ 0 ∨ r1 ≠ 0) ∧
    (p0 ≠ r0 ∨ p1 ≠ r1) ∧ p0 * a + r0 * b = 0 ∧ p1 * a + r1 * b = 0) → a = 0 ∧ b = 0 := by
  decide

theorem indep_fin (p0 p1 r0 r1 a b : ZMod 2) (h1 : p0 ≠ 0 ∨ p1 ≠ 0) (h2 : r0 ≠ 0 ∨ r1 ≠ 0)
    (h3 : p0 ≠ r0 ∨ p1 ≠ r1) (h4 : p0 * a + r0 * b = 0) (h5 : p1 * a + r1 * b = 0) :
    a = 0 ∧ b = 0 := indep_fin0 p0 p1 r0 r1 a b ⟨h1, h2, h3, h4, h5⟩

theorem lower_fp_proof {m e : ℕ} (c : Fin m → Fin 2 → QQ) (hf : FP c)
    (V : Submodule (ZMod 2) (XX m))
    (hVK : V ≤ LinearMap.ker (syn c)) (hV : GoodV e V) :
    Module.finrank (ZMod 2) V + 1 ≤ m + e := by
  classical
  obtain ⟨i0, h0, h1, h01⟩ := hf
  obtain ⟨x0, P, d, hgood⟩ := hV
  set J := Finset.univ.erase i0 with hJ
  obtain ⟨U, hUJ, hU, hdim⟩ := free_claim V J
  have hUe := free_err V U J hU hUJ x0 P d (fun v hv => le_trans (Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.subset_univ J))) (hgood v hv))
  have key := indep_fin
  let f : V →ₗ[ZMod 2] XX m := (rho J).comp V.subtype
  have hfi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨v, hv⟩ hker
    have hr : rho J v = 0 := LinearMap.mem_ker.mp hker
    have hs : syn c v = 0 := LinearMap.mem_ker.mp (hVK hv)
    have hoff : ∀ i, i ≠ i0 → v i = 0 := by
      intro i hi
      have := congrFun hr i
      rwa [rho_apply, if_pos (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)] at this
    have hsj : ∀ j, c i0 0 j * v i0 0 + c i0 1 j * v i0 1 = 0 := by
      intro j
      have := congrFun hs j
      rw [syn_apply, Finset.sum_eq_single i0, Fin.sum_univ_two] at this
      · exact this
      · intro b _ hb
        simp [hoff b hb]
      · intro h
        exact absurd (Finset.mem_univ i0) h
    obtain ⟨ha, hb⟩ := key _ _ _ _ _ _ (qq_ne h0) (qq_ne h1) (qq_ne2 h01) (hsj 0) (hsj 1)
    rw [Submodule.mem_bot]
    apply Subtype.ext
    show v = 0
    funext i u
    by_cases hi : i = i0
    · subst hi
      fin_cases u
      · exact ha
      · exact hb
    · simp [hoff i hi]
  have hrange : LinearMap.range f = V.map (rho J) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h2 := LinearMap.finrank_range_of_inj hfi
  rw [hrange] at h2
  have hJc : J.card + 1 = m := by
    rw [hJ, Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
    have := i0.pos
    omega
  omega

theorem upper_h0_proof {m e : ℕ} (c : Fin m → Fin 2 → QQ) :
    ∃ S, S.card ≤ m - e ∧ GoodS c e S := by
  classical
  obtain ⟨B, -, hB⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin m)))
    (n := m - e) (by simp)
  refine ⟨B.image (fun i => projL i 0), le_trans Finset.card_image_le hB.le, 0, 0,
    fun x _ hx => ?_⟩
  have hsub : errs 0 0 x ⊆ Finset.univ \ B := by
    intro i hi
    simp only [errs, Finset.mem_filter, LinearMap.zero_apply, Pi.zero_apply, add_zero] at hi
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ i, fun hiB => hi.2 ?_⟩
    have := hx (projL i 0) (Finset.mem_image_of_mem _ hiB)
    rw [projL_apply] at this
    rw [this, zero_mul]
  calc (errs 0 0 x).card ≤ (Finset.univ \ B).card := Finset.card_le_card hsub
    _ = m - (m - e) := by rw [Finset.card_univ_diff, Fintype.card_fin, hB]
    _ ≤ e := by omega

theorem dimK {m : ℕ} (c : Fin m → Fin 2 → QQ) :
    Module.finrank (ZMod 2) (LinearMap.ker (syn c)) + hOf c = 2 * m := dimK_proof c

theorem h_le_two {m : ℕ} (c : Fin m → Fin 2 → QQ) : hOf c ≤ 2 := h_le_two_proof c

theorem fp_h {m : ℕ} (c : Fin m → Fin 2 → QQ) (hf : FP c) : hOf c = 2 := fp_h_proof c hf

theorem lower_gen {m e : ℕ} (c : Fin m → Fin 2 → QQ) (V : Submodule (ZMod 2) (XX m))
    (hV : GoodV e V) : Module.finrank (ZMod 2) V ≤ m + e := lower_gen_proof V hV

theorem lower_fp {m e : ℕ} (c : Fin m → Fin 2 → QQ) (hf : FP c) (V : Submodule (ZMod 2) (XX m))
    (hVK : V ≤ LinearMap.ker (syn c)) (hV : GoodV e V) :
    Module.finrank (ZMod 2) V + 1 ≤ m + e := lower_fp_proof c hf V hVK hV

-- Part S: rank two with three types and redundancy two.

def maj (x y w : ZMod 2) : ZMod 2 := x * y + x * w + y * w

theorem syn_pi_single {m : ℕ} (c : Fin m → Fin 2 → QQ) (k : Fin m) (w : QQ) :
    syn c (Pi.single k w) = w 0 • c k 0 + w 1 • c k 1 := by
  rw [syn_eq_sum, Finset.sum_eq_single k]
  · simp [Fin.sum_univ_two]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem qq_ne_of {q : QQ} (h : q 0 ≠ 0 ∨ q 1 ≠ 0) : q ≠ 0 := by
  rintro rfl
  rcases h with h | h <;> exact h rfl

theorem qq_ne2_of {q r : QQ} (h : q 0 ≠ r 0 ∨ q 1 ≠ r 1) : q ≠ r := by
  rintro rfl
  rcases h with h | h <;> exact h rfl

theorem pair_fin : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : ZMod 2,
    (∀ s t1 t2 : ZMod 2, (s * t1 + a0 + a1 * s + a2 * t1 + a3 * t2) *
      (s * t2 + b0 + b1 * s + b2 * t1 + b3 * t2) = 0) → a2 + b3 = 1 := by
  decide

theorem quad_fin : ∀ t u0 u1 d0 d1 : ZMod 2, u0 * d1 + u1 * d0 = 1 → ∃ k0 k1 k2 : ZMod 2,
    ∀ s r : ZMod 2, ((t + s) * u0 + r * d0) * ((t + s) * u1 + r * d1) =
      s * r + k0 + k1 * s + k2 * r := by
  decide

theorem three_fin : ∀ x y w : ZMod 2, x + y = 1 → x + w = 1 → y + w = 1 → False := by
  decide

theorem maj_zero : ∀ x y w : ZMod 2, x * y + x * w + y * w = 0 →
    x * y = 0 ∧ x * w = 0 ∧ y * w = 0 := by
  decide

theorem maj_ne : ∀ x y w : ZMod 2, x * y + x * w + y * w ≠ 0 →
    (x ≠ 0 ∧ y ≠ 0) ∨ (x ≠ 0 ∧ w ≠ 0) ∨ (y ≠ 0 ∧ w ≠ 0) := by
  decide

theorem site_form {m : ℕ} (ℓ : XX m →ₗ[ZMod 2] ZMod 2) (κ : ZMod 2) (i : Fin m)
    (z0 zs z1 z2 z3 : XX m) (t : ZMod 2) (u dv : QQ)
    (h0 : z0 i = t • u) (hs : zs i = u) (h1 : z1 i = dv) (h2 : z2 i = 0) (h3 : z3 i = 0)
    (hB : u 0 * dv 1 + u 1 * dv 0 = 1) :
    ∃ k0 ks k1 k2 k3 : ZMod 2, ∀ s r1 r2 r3 : ZMod 2,
      (z0 + s • zs + r1 • z1 + r2 • z2 + r3 • z3) i 0 *
        (z0 + s • zs + r1 • z1 + r2 • z2 + r3 • z3) i 1 +
        ℓ (z0 + s • zs + r1 • z1 + r2 • z2 + r3 • z3) + κ =
      s * r1 + k0 + ks * s + k1 * r1 + k2 * r2 + k3 * r3 := by
  obtain ⟨q0, q1, q2, hq⟩ := quad_fin t (u 0) (u 1) (dv 0) (dv 1) hB
  refine ⟨q0 + ℓ z0 + κ, q1 + ℓ zs, q2 + ℓ z1, ℓ z2, ℓ z3, fun s r1 r2 r3 => ?_⟩
  have e0 : (z0 + s • zs + r1 • z1 + r2 • z2 + r3 • z3) i 0 = (t + s) * u 0 + r1 * dv 0 := by
    simp only [Pi.add_apply, Pi.smul_apply, h0, hs, h1, h2, h3, smul_eq_mul, Pi.zero_apply,
      mul_zero, add_zero]
    ring
  have e1 : (z0 + s • zs + r1 • z1 + r2 • z2 + r3 • z3) i 1 = (t + s) * u 1 + r1 * dv 1 := by
    simp only [Pi.add_apply, Pi.smul_apply, h0, hs, h1, h2, h3, smul_eq_mul, Pi.zero_apply,
      mul_zero, add_zero]
    ring
  rw [e0, e1, hq s r1]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

theorem base_case {m : ℕ} (a1 a2 a3 : Fin m)
    (z0 zs za zb zk : XX m) (t1 t2 : ZMod 2) (u1 d1 u2 d2 u3 d3 : QQ)
    (v1 : z0 a1 = t1 • u1 ∧ zs a1 = u1 ∧ za a1 = d1 ∧ zb a1 = 0 ∧ zk a1 = 0)
    (v2 : z0 a2 = t2 • u2 ∧ zs a2 = u2 ∧ zb a2 = d2 ∧ za a2 = 0 ∧ zk a2 = 0)
    (v3 : z0 a3 = (0 : ZMod 2) • u3 ∧ zs a3 = u3 ∧ zk a3 = d3 ∧ za a3 = 0 ∧ zb a3 = 0)
    (B1 : u1 0 * d1 1 + u1 1 * d1 0 = 1) (B2 : u2 0 * d2 1 + u2 1 * d2 0 = 1)
    (B3 : u3 0 * d3 1 + u3 1 * d3 0 = 1)
    (ℓ : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (κ : Fin m → ZMod 2) :
    ∃ s r1 r2 r3 : ZMod 2,
      maj ((z0 + s • zs + r1 • za + r2 • zb + r3 • zk) a1 0 *
          (z0 + s • zs + r1 • za + r2 • zb + r3 • zk) a1 1 +
          ℓ a1 (z0 + s • zs + r1 • za + r2 • zb + r3 • zk) + κ a1)
        ((z0 + s • zs + r1 • za + r2 • zb + r3 • zk) a2 0 *
          (z0 + s • zs + r1 • za + r2 • zb + r3 • zk) a2 1 +
          ℓ a2 (z0 + s • zs + r1 • za + r2 • zb + r3 • zk) + κ a2)
        ((z0 + s • zs + r1 • za + r2 • zb + r3 • zk) a3 0 *
          (z0 + s • zs + r1 • za + r2 • zb + r3 • zk) a3 1 +
          ℓ a3 (z0 + s • zs + r1 • za + r2 • zb + r3 • zk) + κ a3) ≠ 0 := by
  obtain ⟨A0, As, Aa, Ab, Ak, hA⟩ := site_form (ℓ a1) (κ a1) a1 z0 zs za zb zk t1 u1 d1
    v1.1 v1.2.1 v1.2.2.1 v1.2.2.2.1 v1.2.2.2.2 B1
  obtain ⟨B0, Bs, Bb, Ba, Bk, hB⟩ := site_form (ℓ a2) (κ a2) a2 z0 zs zb za zk t2 u2 d2
    v2.1 v2.2.1 v2.2.2.1 v2.2.2.2.1 v2.2.2.2.2 B2
  obtain ⟨C0, Cs, Ck, Ca, Cb, hC⟩ := site_form (ℓ a3) (κ a3) a3 z0 zs zk za zb 0 u3 d3
    v3.1 v3.2.1 v3.2.2.1 v3.2.2.2.1 v3.2.2.2.2 B3
  have hp2 : ∀ s r1 r2 r3 : ZMod 2, z0 + s • zs + r2 • zb + r1 • za + r3 • zk =
      z0 + s • zs + r1 • za + r2 • zb + r3 • zk := by
    intros
    abel
  have hp3 : ∀ s r1 r2 r3 : ZMod 2, z0 + s • zs + r3 • zk + r1 • za + r2 • zb =
      z0 + s • zs + r1 • za + r2 • zb + r3 • zk := by
    intros
    abel
  by_contra hno
  push_neg at hno
  have q1 : Aa + Bb = 1 := pair_fin A0 As Aa Ab B0 Bs Ba Bb (fun s r1 r2 => by
    have h := (maj_zero _ _ _ (hno s r1 r2 0)).1
    have e1 := hA s r1 r2 0
    have e2 := hB s r2 r1 0
    rw [hp2] at e2
    rw [e1, e2] at h
    linear_combination h)
  have q2 : Aa + Ck = 1 := pair_fin A0 As Aa Ak C0 Cs Ca Ck (fun s r1 r3 => by
    have h := (maj_zero _ _ _ (hno s r1 0 r3)).2.1
    have e1 := hA s r1 0 r3
    have e3 := hC s r3 r1 0
    rw [hp3] at e3
    rw [e1, e3] at h
    linear_combination h)
  have q3 : Bb + Ck = 1 := pair_fin B0 Bs Bb Bk C0 Cs Cb Ck (fun s r2 r3 => by
    have h := (maj_zero _ _ _ (hno s 0 r2 r3)).2.2
    have e2 := hB s r2 0 r3
    have e3 := hC s r3 0 r2
    rw [hp2] at e2
    rw [hp3] at e3
    rw [e2, e3] at h
    linear_combination h)
  exact three_fin _ _ _ q1 q2 q3

theorem dir_pick (g : QQ →ₗ[ZMod 2] ZMod 2) (dv : QQ) (hd : dv 0 ≠ 0 ∨ dv 1 ≠ 0) :
    ∃ w0 w1 : QQ, w0 0 * w0 1 + g w0 = 0 ∧ w1 0 * w1 1 + g w1 = 1 ∧ w0 + w1 = dv := by
  have hg : ∀ w : QQ, g w = w 0 * g (Pi.single 0 1) + w 1 * g (Pi.single 1 1) := by
    intro w
    have hw : w = w 0 • (Pi.single 0 1 : QQ) + w 1 • (Pi.single 1 1 : QQ) := by
      funext j
      fin_cases j <;> simp
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have key : ∀ a b d0 d1 : ZMod 2, (d0 ≠ 0 ∨ d1 ≠ 0) → ∃ p0 p1 q0 q1 : ZMod 2,
      p0 * p1 + (p0 * a + p1 * b) = 0 ∧ q0 * q1 + (q0 * a + q1 * b) = 1 ∧
        p0 + q0 = d0 ∧ p1 + q1 = d1 := by decide
  obtain ⟨p0, p1, q0, q1, h0, h1, h2, h3⟩ :=
    key (g (Pi.single 0 1)) (g (Pi.single 1 1)) (dv 0) (dv 1) hd
  refine ⟨![p0, p1], ![q0, q1], ?_, ?_, ?_⟩
  · rw [hg]
    simpa using h0
  · rw [hg]
    simpa using h1
  · funext j
    fin_cases j
    · simpa using h2
    · simpa using h3

theorem spec_step {m : ℕ} (c : Fin m → Fin 2 → QQ) (a1 a2 a3 : Fin m)
    (hd : ∀ k : Fin m, ∃ dv : QQ, (dv 0 ≠ 0 ∨ dv 1 ≠ 0) ∧ syn c (Pi.single k dv) = 0)
    (base : ∀ (ℓ : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (κ : Fin m → ZMod 2) (τ : QQ),
      ∃ z : XX m, (∀ j, j ≠ a1 → j ≠ a2 → j ≠ a3 → z j = 0) ∧ syn c z = τ ∧
        maj (z a1 0 * z a1 1 + ℓ a1 z + κ a1) (z a2 0 * z a2 1 + ℓ a2 z + κ a2)
          (z a3 0 * z a3 1 + ℓ a3 z + κ a3) ≠ 0)
    (K : Finset (Fin m)) : a1 ∉ K → a2 ∉ K → a3 ∉ K →
    ∀ (ℓ : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (κ : Fin m → ZMod 2) (τ : QQ),
      ∃ z : XX m, (∀ j, j ∉ K → j ≠ a1 → j ≠ a2 → j ≠ a3 → z j = 0) ∧ syn c z = τ ∧
        (∀ i ∈ K, z i 0 * z i 1 + ℓ i z + κ i ≠ 0) ∧
        maj (z a1 0 * z a1 1 + ℓ a1 z + κ a1) (z a2 0 * z a2 1 + ℓ a2 z + κ a2)
          (z a3 0 * z a3 1 + ℓ a3 z + κ a3) ≠ 0 := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    intro _ _ _ ℓ κ τ
    obtain ⟨z, hz1, hz2, hz3⟩ := base ℓ κ τ
    exact ⟨z, fun j _ => hz1 j, hz2, fun i hi => absurd hi (Finset.notMem_empty i), hz3⟩
  | insert k K' hk ih =>
    intro ha1 ha2 ha3 ℓ κ τ
    have hk1 : k ≠ a1 := fun h => ha1 (h ▸ Finset.mem_insert_self k K')
    have hk2 : k ≠ a2 := fun h => ha2 (h ▸ Finset.mem_insert_self k K')
    have hk3 : k ≠ a3 := fun h => ha3 (h ▸ Finset.mem_insert_self k K')
    have ha1' : a1 ∉ K' := fun h => ha1 (Finset.mem_insert_of_mem h)
    have ha2' : a2 ∉ K' := fun h => ha2 (Finset.mem_insert_of_mem h)
    have ha3' : a3 ∉ K' := fun h => ha3 (Finset.mem_insert_of_mem h)
    obtain ⟨dv, hdv, hcol⟩ := hd k
    let Z : XX m →ₗ[ZMod 2] XX m := rho (Finset.univ.erase k)
    let sk : QQ →ₗ[ZMod 2] XX m := LinearMap.single (ZMod 2) (fun _ => QQ) k
    let g : QQ →ₗ[ZMod 2] ZMod 2 := (ℓ k).comp sk
    obtain ⟨w0, w1, hw0, hw1, hw01⟩ := dir_pick g dv hdv
    let δ : XX m := sk (w0 + w1)
    let bb : XX m := sk w1 + κ k • δ
    let Lφ : XX m →ₗ[ZMod 2] XX m := Z + ((ℓ k).comp Z).smulRight δ
    obtain ⟨z, hzs, hzsyn, hzK, hzmaj⟩ := ih ha1' ha2' ha3' (fun i => (ℓ i).comp Lφ)
      (fun i => ℓ i bb + κ i) (τ - syn c (Pi.single k w1))
    have hsk : ∀ (w : QQ) (i : Fin m), sk w i = if i = k then w else 0 := by
      intro w i
      by_cases hi : i = k
      · subst hi
        simp [sk]
      · simp [sk, hi, Pi.single_apply]
    have hZ : ∀ (y : XX m) (i : Fin m), Z y i = if i = k then 0 else y i := by
      intro y i
      by_cases hi : i = k <;> simp [Z, rho_apply, hi]
    have hoff : ∀ i, i ≠ k → (Lφ z + bb) i = z i := by
      intro i hik
      simp only [Lφ, bb, δ, Pi.add_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        Pi.smul_apply, hZ, hsk, if_neg hik, smul_zero, add_zero]
    have hdec : ∀ y : XX m, ℓ k y = ℓ k (Z y) + g (y k) := by
      intro y
      have hy : y = Z y + sk (y k) := by
        funext i
        rw [Pi.add_apply, hZ, hsk]
        by_cases hi : i = k
        · subst hi
          simp
        · simp [hi]
      conv_lhs => rw [hy]
      rw [map_add]
      rfl
    have hyk : (Lφ z + bb) k = w1 + (ℓ k (Z z) + κ k) • (w0 + w1) := by
      funext u
      simp only [Lφ, bb, δ, Pi.add_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        Pi.smul_apply, hZ, hsk, ite_true, smul_eq_mul, LinearMap.comp_apply, Pi.zero_apply]
      ring
    have hzk : z k = 0 := hzs k hk hk1 hk2 hk3
    have herr : ∀ i, i ≠ k → (Lφ z + bb) i 0 * (Lφ z + bb) i 1 + ℓ i (Lφ z + bb) + κ i =
        z i 0 * z i 1 + (ℓ i).comp Lφ z + (ℓ i bb + κ i) := by
      intro i hi
      rw [hoff i hi, map_add, LinearMap.comp_apply]
      ring
    refine ⟨Lφ z + bb, ?_, ?_, ?_, ?_⟩
    · intro j hj hj1 hj2 hj3
      have hjk : j ≠ k := fun h => hj (h ▸ Finset.mem_insert_self k K')
      rw [hoff j hjk]
      exact hzs j (fun h => hj (Finset.mem_insert_of_mem h)) hj1 hj2 hj3
    · have hy : Lφ z + bb = z + sk (w1 + (ℓ k (Z z) + κ k) • (w0 + w1)) := by
        funext i
        show (Lφ z + bb) i = z i + sk (w1 + (ℓ k (Z z) + κ k) • (w0 + w1)) i
        rw [hsk]
        by_cases hi : i = k
        · rw [hi, hyk, if_pos rfl, hzk, zero_add]
        · rw [hoff i hi, if_neg hi, add_zero]
      have e1 : syn c (sk dv) = 0 := hcol
      have e2 : syn c (sk w1) = syn c (Pi.single k w1) := rfl
      rw [hy, map_add, hzsyn, map_add, map_add, map_smul, hw01, map_smul, e1, e2,
        smul_zero, add_zero, sub_add_cancel]
    · intro i hi
      rcases Finset.mem_insert.mp hi with hik | hi'
      · rw [hik]
        have hZy : Z (Lφ z + bb) = Z z := by
          funext j
          rw [hZ, hZ]
          by_cases hj : j = k
          · simp [hj]
          · rw [if_neg hj, if_neg hj, hoff j hj]
        rw [hdec (Lφ z + bb), hZy]
        rcases zmod2_cases (ℓ k (Z z) + κ k) with hν | hν
        · have hyk0 : (Lφ z + bb) k = w1 := by
            rw [hyk, hν, zero_smul, add_zero]
          rw [hyk0]
          have : w1 0 * w1 1 + (ℓ k (Z z) + g w1) + κ k = 1 := by
            linear_combination hw1 + hν
          rw [this]
          decide
        · have hyk1 : (Lφ z + bb) k = w0 := by
            rw [hyk, hν, one_smul]
            funext u
            simp only [Pi.add_apply]
            linear_combination zmod2_two (w1 u)
          rw [hyk1]
          have : w0 0 * w0 1 + (ℓ k (Z z) + g w0) + κ k = 1 := by
            linear_combination hw0 + hν
          rw [this]
          decide
      · rw [herr i (fun h => hk (h ▸ hi'))]
        exact hzK i hi'
    · rw [herr a1 hk1.symm, herr a2 hk2.symm, herr a3 hk3.symm]
      exact hzmaj

theorem site_ne {m : ℕ} (c : Fin m → Fin 2 → QQ) (hf : ¬ FP c) {i j : Fin m} {p q : QQ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) (hi : p = c i 0 ∨ p = c i 1)
    (hj : q = c j 0 ∨ q = c j 1) : i ≠ j := by
  rintro rfl
  apply hf
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hpq
  · exact ⟨i, hp, hq, hpq⟩
  · exact ⟨i, hq, hp, fun h => hpq h.symm⟩
  · exact absurd rfl hpq

theorem no_fp_at {m : ℕ} (c : Fin m → Fin 2 → QQ) (hf : ¬ FP c) (j : Fin m) :
    ¬ ((c j 0 0 ≠ 0 ∨ c j 0 1 ≠ 0) ∧ (c j 1 0 ≠ 0 ∨ c j 1 1 ≠ 0) ∧
      (c j 0 0 ≠ c j 1 0 ∨ c j 0 1 ≠ c j 1 1)) := by
  rintro ⟨h1, h2, h3⟩
  exact hf ⟨j, qq_ne_of h1, qq_ne_of h2, qq_ne2_of h3⟩

theorem site_finp : ∀ p0 p1 r0 r1 : ZMod 2,
    (¬ ((p0 ≠ 0 ∨ p1 ≠ 0) ∧ (r0 ≠ 0 ∨ r1 ≠ 0) ∧ (p0 ≠ r0 ∨ p1 ≠ r1)) ∧ (p0 ≠ 0 ∨ p1 ≠ 0)) →
    ∃ d0 d1 : ZMod 2, (d0 * p0 + d1 * r0 = 0 ∧ d0 * p1 + d1 * r1 = 0) ∧
      ∃ u0 u1 : ZMod 2, u0 * d1 + u1 * d0 = 1 ∧ u0 * p0 + u1 * r0 = p0 ∧
        u0 * p1 + u1 * r1 = p1 := by
  decide

theorem site_finr : ∀ p0 p1 r0 r1 : ZMod 2,
    (¬ ((p0 ≠ 0 ∨ p1 ≠ 0) ∧ (r0 ≠ 0 ∨ r1 ≠ 0) ∧ (p0 ≠ r0 ∨ p1 ≠ r1)) ∧ (r0 ≠ 0 ∨ r1 ≠ 0)) →
    ∃ d0 d1 : ZMod 2, (d0 * p0 + d1 * r0 = 0 ∧ d0 * p1 + d1 * r1 = 0) ∧
      ∃ u0 u1 : ZMod 2, u0 * d1 + u1 * d0 = 1 ∧ u0 * p0 + u1 * r0 = r0 ∧
        u0 * p1 + u1 * r1 = r1 := by
  decide

theorem site_vec {m : ℕ} (c : Fin m → Fin 2 → QQ) (hf : ¬ FP c) (j : Fin m) (q : QQ)
    (hq : q ≠ 0) (hj : q = c j 0 ∨ q = c j 1) :
    ∃ u dv : QQ, syn c (Pi.single j dv) = 0 ∧ u 0 * dv 1 + u 1 * dv 0 = 1 ∧
      syn c (Pi.single j u) = q := by
  have hnf := no_fp_at c hf j
  have hq' := qq_ne hq
  obtain ⟨d0, d1, ⟨e1, e2⟩, u0, u1, e3, e4, e5⟩ : ∃ d0 d1 : ZMod 2,
      (d0 * c j 0 0 + d1 * c j 1 0 = 0 ∧ d0 * c j 0 1 + d1 * c j 1 1 = 0) ∧
      ∃ u0 u1 : ZMod 2, u0 * d1 + u1 * d0 = 1 ∧ u0 * c j 0 0 + u1 * c j 1 0 = q 0 ∧
        u0 * c j 0 1 + u1 * c j 1 1 = q 1 := by
    rcases hj with h | h
    · rw [h] at hq' ⊢
      exact site_finp _ _ _ _ ⟨hnf, hq'⟩
    · rw [h] at hq' ⊢
      exact site_finr _ _ _ _ ⟨hnf, hq'⟩
  refine ⟨![u0, u1], ![d0, d1], ?_, ?_, ?_⟩
  · rw [syn_pi_single]
    funext t
    fin_cases t
    · simpa using e1
    · simpa using e2
  · simpa using e3
  · rw [syn_pi_single]
    funext t
    fin_cases t
    · simpa using e4
    · simpa using e5

theorem site_ker {m : ℕ} (c : Fin m → Fin 2 → QQ) (hf : ¬ FP c) (j : Fin m) :
    ∃ dv : QQ, (dv 0 ≠ 0 ∨ dv 1 ≠ 0) ∧ syn c (Pi.single j dv) = 0 := by
  have key : ∀ p0 p1 r0 r1 : ZMod 2,
      ¬ ((p0 ≠ 0 ∨ p1 ≠ 0) ∧ (r0 ≠ 0 ∨ r1 ≠ 0) ∧ (p0 ≠ r0 ∨ p1 ≠ r1)) →
      ∃ d0 d1 : ZMod 2, (d0 ≠ 0 ∨ d1 ≠ 0) ∧ d0 * p0 + d1 * r0 = 0 ∧ d0 * p1 + d1 * r1 = 0 := by
    decide
  obtain ⟨d0, d1, e0, e1, e2⟩ := key _ _ _ _ (no_fp_at c hf j)
  refine ⟨![d0, d1], by simpa using e0, ?_⟩
  rw [syn_pi_single]
  funext t
  fin_cases t
  · simpa using e1
  · simpa using e2

theorem sum3_fin0 : ∀ p0 p1 q0 q1 r0 r1 : ZMod 2, ((p0 ≠ 0 ∨ p1 ≠ 0) ∧ (q0 ≠ 0 ∨ q1 ≠ 0) ∧
    (r0 ≠ 0 ∨ r1 ≠ 0) ∧ (p0 ≠ q0 ∨ p1 ≠ q1) ∧ (p0 ≠ r0 ∨ p1 ≠ r1) ∧ (q0 ≠ r0 ∨ q1 ≠ r1)) →
    p0 + q0 + r0 = 0 ∧ p1 + q1 + r1 = 0 := by
  decide

theorem sum3_fin (p0 p1 q0 q1 r0 r1 : ZMod 2) (h1 : p0 ≠ 0 ∨ p1 ≠ 0) (h2 : q0 ≠ 0 ∨ q1 ≠ 0)
    (h3 : r0 ≠ 0 ∨ r1 ≠ 0) (h4 : p0 ≠ q0 ∨ p1 ≠ q1) (h5 : p0 ≠ r0 ∨ p1 ≠ r1)
    (h6 : q0 ≠ r0 ∨ q1 ≠ r1) : p0 + q0 + r0 = 0 ∧ p1 + q1 + r1 = 0 :=
  sum3_fin0 p0 p1 q0 q1 r0 r1 ⟨h1, h2, h3, h4, h5, h6⟩

theorem special_proof {m e : ℕ} (c : Fin m → Fin 2 → QQ) (hf : ¬ FP c)
    (hr : m - e = 2) (h3 : ((labOf c).erase 0).card = 3) :
    ¬ GoodV e (LinearMap.ker (syn c)) := by
  classical
  rintro ⟨x0, P, d, hgood⟩
  obtain ⟨qa, qb, qc, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp h3
  have hmem : ∀ q ∈ (labOf c).erase 0, q ≠ 0 ∧ ∃ j, q = c j 0 ∨ q = c j 1 := by
    intro q hq
    rw [Finset.mem_erase] at hq
    refine ⟨hq.1, ?_⟩
    have := hq.2
    simp only [labOf, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at this
    exact this
  obtain ⟨hqa, a1, ha1⟩ := hmem qa (by rw [hset]; simp)
  obtain ⟨hqb, a2, ha2⟩ := hmem qb (by rw [hset]; simp)
  obtain ⟨hqc, a3, ha3⟩ := hmem qc (by rw [hset]; simp)
  have h12 := site_ne c hf hqa hqb hab ha1 ha2
  have h13 := site_ne c hf hqa hqc hac ha1 ha3
  have h23 := site_ne c hf hqb hqc hbc ha2 ha3
  obtain ⟨u1, d1, hd1, B1, hu1⟩ := site_vec c hf a1 qa hqa ha1
  obtain ⟨u2, d2, hd2, B2, hu2⟩ := site_vec c hf a2 qb hqb ha2
  obtain ⟨u3, d3, hd3, B3, hu3⟩ := site_vec c hf a3 qc hqc ha3
  have hsum : qa + qb + qc = 0 := by
    obtain ⟨s0, s1⟩ := sum3_fin _ _ _ _ _ _ (qq_ne hqa) (qq_ne hqb) (qq_ne hqc) (qq_ne2 hab)
      (qq_ne2 hac) (qq_ne2 hbc)
    funext t
    fin_cases t
    · simpa using s0
    · simpa using s1
  have hspan : ∀ τ : QQ, ∃ t1 t2 : ZMod 2, t1 • qa + t2 • qb = τ := by
    intro τ
    obtain ⟨t1, t2, e0, e1⟩ := span_fin _ _ _ _ (τ 0) (τ 1) (qq_ne hqa) (qq_ne hqb) (qq_ne2 hab)
    refine ⟨t1, t2, ?_⟩
    funext t
    fin_cases t
    · simp [e0, mul_comm]
    · simp [e1, mul_comm]
  have base : ∀ (ℓ : Fin m → XX m →ₗ[ZMod 2] ZMod 2) (κ : Fin m → ZMod 2) (τ : QQ),
      ∃ z : XX m, (∀ j, j ≠ a1 → j ≠ a2 → j ≠ a3 → z j = 0) ∧ syn c z = τ ∧
        maj (z a1 0 * z a1 1 + ℓ a1 z + κ a1) (z a2 0 * z a2 1 + ℓ a2 z + κ a2)
          (z a3 0 * z a3 1 + ℓ a3 z + κ a3) ≠ 0 := by
    intro ℓ κ τ
    obtain ⟨t1, t2, ht⟩ := hspan τ
    obtain ⟨s, r1, r2, r3, hmj⟩ := base_case a1 a2 a3
      (t1 • (Pi.single a1 u1 : XX m) + t2 • (Pi.single a2 u2 : XX m))
      ((Pi.single a1 u1 : XX m) + (Pi.single a2 u2 : XX m) + (Pi.single a3 u3 : XX m))
      (Pi.single a1 d1 : XX m) (Pi.single a2 d2 : XX m) (Pi.single a3 d3 : XX m)
      t1 t2 u1 d1 u2 d2 u3 d3
      (by simp [Pi.single_apply, h12, h13, h23, h12.symm, h13.symm, h23.symm])
      (by simp [Pi.single_apply, h12, h13, h23, h12.symm, h13.symm, h23.symm])
      (by simp [Pi.single_apply, h12, h13, h23, h12.symm, h13.symm, h23.symm])
      B1 B2 B3 ℓ κ
    refine ⟨_, ?_, ?_, hmj⟩
    · intro j hj1 hj2 hj3
      simp [Pi.single_apply, hj1, hj2, hj3]
    · simp only [map_add, map_smul]
      rw [hu1, hu2, hu3, hd1, hd2, hd3, ht, hsum]
      simp
  obtain ⟨z, -, hzsyn, hzK, hzmaj⟩ := spec_step c a1 a2 a3 (site_ker c hf) base
    (Finset.univ \ {a1, a2, a3}) (by simp) (by simp) (by simp)
    (fun i => x0 i 0 • projL i 1 + x0 i 1 • projL i 0 - P i)
    (fun i => x0 i 0 * x0 i 1 - P i x0 - d i) 0
  have hg := hgood z hzsyn
  have herr : ∀ i, z i 0 * z i 1 + (x0 i 0 • projL i 1 + x0 i 1 • projL i 0 - P i) z +
      (x0 i 0 * x0 i 1 - P i x0 - d i) ≠ 0 → i ∈ errs P d (x0 + z) := by
    intro i hi
    simp only [errs, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h2
    apply hi
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, projL_apply,
      smul_eq_mul, Pi.add_apply, map_add] at h2 ⊢
    linear_combination h2
  have hcount : ∀ r : Fin m, (∀ i, i ≠ r → i ∈ errs P d (x0 + z)) → False := by
    intro r hr'
    have h1 : (Finset.univ.erase r).card ≤ (errs P d (x0 + z)).card :=
      Finset.card_le_card (fun i hi => hr' i (Finset.ne_of_mem_erase hi))
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hK : ∀ i, i ≠ a1 → i ≠ a2 → i ≠ a3 → i ∈ errs P d (x0 + z) :=
    fun i h1 h2 h3 => herr i (hzK i (by simp [h1, h2, h3]))
  rcases maj_ne _ _ _ hzmaj with ⟨e1, e2⟩ | ⟨e1, e3⟩ | ⟨e2, e3⟩
  · apply hcount a3
    intro i hi
    by_cases h1 : i = a1
    · rw [h1]
      exact herr _ e1
    by_cases h2 : i = a2
    · rw [h2]
      exact herr _ e2
    exact hK i h1 h2 hi
  · apply hcount a2
    intro i hi
    by_cases h1 : i = a1
    · rw [h1]
      exact herr _ e1
    by_cases h3 : i = a3
    · rw [h3]
      exact herr _ e3
    exact hK i h1 hi h3
  · apply hcount a1
    intro i hi
    by_cases h2 : i = a2
    · rw [h2]
      exact herr _ e2
    by_cases h3 : i = a3
    · rw [h3]
      exact herr _ e3
    exact hK i hi h2 h3

-- Part C2: rank two without a full pair.

theorem coset_fin : ∀ s0 s1 k : ZMod 2, (s0 ≠ 0 ∨ s1 ≠ 0) → ∃ α β γ : ZMod 2,
    ∀ z0 z1 : ZMod 2, s0 * z0 + s1 * z1 = k → z0 * z1 = α * z0 + β * z1 + γ := by
  decide

theorem upper_core {m e : ℕ} (c : Fin m → Fin 2 → QQ) (σ0 σ1 : Fin m → ZMod 2)
    (hσ : ∀ j, σ0 j ≠ 0 ∨ σ1 j ≠ 0) (B R : Finset (Fin m)) (hBR : Disjoint B R)
    (hE : ((Finset.univ \ B) \ R).card ≤ e)
    (Ea : Fin m → Finset (Fin m)) (hEa : ∀ a ∈ R, Ea a ⊆ (Finset.univ \ B) \ R)
    (hdisj : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (Ea a) (Ea b))
    (S : Finset (XX m →ₗ[ZMod 2] ZMod 2))
    (hS : ∀ x, syn c x = 0 → (∀ f ∈ S, f x = 0) →
      (∀ j ∈ B, σ0 j * x j 0 + σ1 j * x j 1 = 0) ∧
      (∀ a ∈ R, σ0 a * x a 0 + σ1 a * x a 1 = ∑ j ∈ Ea a, (σ0 j * x j 0 + σ1 j * x j 1))) :
    GoodS c e S := by
  classical
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Fin m), E = (Finset.univ \ B) \ R := ⟨_, rfl⟩
  rw [← hEdef] at hE hEa
  let κ : Fin m → ZMod 2 := fun j => if j ∈ B then 0 else ∑ i ∈ Ea j, (σ0 i + σ1 i)
  have hcf : ∀ j, ∃ α β γ : ZMod 2, ∀ z0 z1 : ZMod 2, σ0 j * z0 + σ1 j * z1 = κ j →
      z0 * z1 = α * z0 + β * z1 + γ := fun j => coset_fin _ _ _ (hσ j)
  choose α β γ hαβγ using hcf
  let P : Fin m → XX m →ₗ[ZMod 2] ZMod 2 := fun j =>
    if j ∈ E then 0 else α j • projL j 0 + β j • projL j 1
  let d : Fin m → ZMod 2 := fun j => if j ∈ E then 0 else γ j
  refine ⟨P, d, fun x hsyn hq => ?_⟩
  obtain ⟨hB, hR⟩ := hS x hsyn hq
  have hsub : errs P d x ⊆ E.filter (fun j => x j 0 * x j 1 ≠ 0) ∪
      R.filter (fun a => σ0 a * x a 0 + σ1 a * x a 1 ≠ κ a) := by
    intro j hj
    simp only [errs, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hjE : j ∈ E
    · left
      refine ⟨hjE, ?_⟩
      simpa [P, d, hjE] using hj
    · right
      have hjBR : j ∈ B ∨ j ∈ R := by
        by_contra hc
        push_neg at hc
        apply hjE
        rw [hEdef, Finset.mem_sdiff, Finset.mem_sdiff]
        exact ⟨⟨Finset.mem_univ j, hc.1⟩, hc.2⟩
      have hex : σ0 j * x j 0 + σ1 j * x j 1 ≠ κ j := by
        intro hk
        apply hj
        simp only [P, d, if_neg hjE, LinearMap.add_apply, LinearMap.smul_apply, projL_apply,
          smul_eq_mul]
        exact hαβγ j _ _ hk
      rcases hjBR with hjB | hjR
      · exfalso
        apply hex
        rw [hB j hjB]
        simp [κ, hjB]
      · exact ⟨hjR, hex⟩
  have hpt : ∀ a ∈ R.filter (fun a => σ0 a * x a 0 + σ1 a * x a 1 ≠ κ a),
      ∃ j ∈ Ea a, x j 0 * x j 1 = 0 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hBR h ha.1
    by_contra hall
    push_neg at hall
    apply ha.2
    rw [hR a ha.1]
    simp only [κ, if_neg haB]
    apply Finset.sum_congr rfl
    intro j hj
    have h1 := hall j hj
    have key : ∀ a b : ZMod 2, a * b ≠ 0 → a = 1 ∧ b = 1 := by decide
    obtain ⟨e0, e1⟩ := key _ _ h1
    rw [e0, e1, mul_one, mul_one]
  let f : Fin m → Fin m := fun a =>
    if h : ∃ j ∈ Ea a, x j 0 * x j 1 = 0 then h.choose else a
  have hf : ∀ a ∈ R.filter (fun a => σ0 a * x a 0 + σ1 a * x a 1 ≠ κ a),
      f a ∈ Ea a ∧ x (f a) 0 * x (f a) 1 = 0 := by
    intro a ha
    have h := hpt a ha
    simp only [f, dif_pos h]
    exact h.choose_spec
  have hcard1 : (R.filter (fun a => σ0 a * x a 0 + σ1 a * x a 1 ≠ κ a)).card ≤
      (E.filter (fun j => ¬ (x j 0 * x j 1 ≠ 0))).card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      rw [Finset.mem_coe] at ha
      have h := hf a ha
      have haR : a ∈ R := (Finset.mem_filter.mp ha).1
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hEa a haR h.1, not_not.mpr h.2⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      by_contra hne
      have haR := (Finset.mem_filter.mp ha).1
      have hbR := (Finset.mem_filter.mp hb).1
      have hb1 : f a ∈ Ea b := by
        rw [hab]
        exact (hf b hb).1
      exact Finset.disjoint_left.mp (hdisj a haR b hbR hne) (hf a ha).1 hb1
  have hcard2 := Finset.card_filter_add_card_filter_not (s := E)
    (fun j => x j 0 * x j 1 ≠ 0)
  calc (errs P d x).card ≤ (E.filter (fun j => x j 0 * x j 1 ≠ 0) ∪
        R.filter (fun a => σ0 a * x a 0 + σ1 a * x a 1 ≠ κ a)).card := Finset.card_le_card hsub
    _ ≤ (E.filter (fun j => x j 0 * x j 1 ≠ 0)).card +
        (R.filter (fun a => σ0 a * x a 0 + σ1 a * x a 1 ≠ κ a)).card := Finset.card_union_le _ _
    _ ≤ E.card := by omega
    _ ≤ e := hE

theorem split_sum {m : ℕ} (B R : Finset (Fin m)) (hBR : Disjoint B R) (F : Fin m → QQ)
    (hB : ∀ j ∈ B, F j = 0) :
    ∑ j, F j = ∑ j ∈ R, F j + ∑ j ∈ (Finset.univ \ B) \ R, F j := by
  have hRsub : R ⊆ Finset.univ \ B := fun j hj =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun h => Finset.disjoint_left.mp hBR h hj⟩
  rw [← Finset.sum_sdiff (Finset.subset_univ B), Finset.sum_eq_zero hB, add_zero,
    ← Finset.sum_sdiff hRsub, add_comm]

theorem class3 {m : ℕ} (E : Finset (Fin m)) (lab : Fin m → QQ) (s : Fin m → ZMod 2)
    (g1 g2 g3 : QQ) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) (h3 : g3 ≠ 0) (h12 : g1 ≠ g2) (h13 : g1 ≠ g3)
    (h23 : g2 ≠ g3) (hl : ∀ j ∈ E, lab j = 0 ∨ lab j = g1 ∨ lab j = g2 ∨ lab j = g3) :
    ∑ j ∈ E, s j • lab j = (∑ j ∈ E.filter (fun j => lab j = g1), s j) • g1 +
      (∑ j ∈ E.filter (fun j => lab j = g2), s j) • g2 +
      (∑ j ∈ E.filter (fun j => lab j = g3), s j) • g3 := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_smul, Finset.sum_smul,
    Finset.sum_smul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases hl j hj with h | h | h | h <;> rw [h] <;>
    simp [h1, h2, h3, h12, h13, h23, h1.symm, h2.symm, h3.symm, h12.symm, h13.symm, h23.symm]

theorem class2 {m : ℕ} (E : Finset (Fin m)) (lab : Fin m → QQ) (s : Fin m → ZMod 2)
    (g1 g2 : QQ) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) (h12 : g1 ≠ g2)
    (hl : ∀ j ∈ E, lab j = 0 ∨ lab j = g1 ∨ lab j = g2) :
    ∑ j ∈ E, s j • lab j = (∑ j ∈ E.filter (fun j => lab j = g1), s j) • g1 +
      (∑ j ∈ E.filter (fun j => lab j = g2), s j) • g2 := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_smul, Finset.sum_smul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases hl j hj with h | h | h <;> rw [h] <;>
    simp [h1, h2, h12, h1.symm, h2.symm, h12.symm]

theorem indep_qq {p q : QQ} {u v : ZMod 2} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q)
    (h : u • p + v • q = 0) : u = 0 ∧ v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  exact indep_fin (p 0) (p 1) (q 0) (q 1) u v (qq_ne hp) (qq_ne hq) (qq_ne2 hpq)
    (by linear_combination h0) (by linear_combination h1)

theorem four_fin0 : ∀ p0 p1 q0 q1 r0 r1 x0 x1 : ZMod 2, ((p0 ≠ 0 ∨ p1 ≠ 0) ∧
    (q0 ≠ 0 ∨ q1 ≠ 0) ∧ (r0 ≠ 0 ∨ r1 ≠ 0) ∧ (p0 ≠ q0 ∨ p1 ≠ q1) ∧ (p0 ≠ r0 ∨ p1 ≠ r1) ∧
    (q0 ≠ r0 ∨ q1 ≠ r1)) → (x0 = 0 ∧ x1 = 0) ∨ (x0 = p0 ∧ x1 = p1) ∨ (x0 = q0 ∧ x1 = q1) ∨
      (x0 = r0 ∧ x1 = r1) := by
  decide

theorem four_fin (p0 p1 q0 q1 r0 r1 x0 x1 : ZMod 2) (h1 : p0 ≠ 0 ∨ p1 ≠ 0)
    (h2 : q0 ≠ 0 ∨ q1 ≠ 0) (h3 : r0 ≠ 0 ∨ r1 ≠ 0) (h4 : p0 ≠ q0 ∨ p1 ≠ q1)
    (h5 : p0 ≠ r0 ∨ p1 ≠ r1) (h6 : q0 ≠ r0 ∨ q1 ≠ r1) :
    (x0 = 0 ∧ x1 = 0) ∨ (x0 = p0 ∧ x1 = p1) ∨ (x0 = q0 ∧ x1 = q1) ∨ (x0 = r0 ∧ x1 = r1) :=
  four_fin0 p0 p1 q0 q1 r0 r1 x0 x1 ⟨h1, h2, h3, h4, h5, h6⟩

theorem qq_ext {p q : QQ} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  funext t
  fin_cases t
  · exact h0
  · exact h1

theorem four_qq {p q r : QQ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (x : QQ) : x = 0 ∨ x = p ∨ x = q ∨ x = r := by
  rcases four_fin _ _ _ _ _ _ (x 0) (x 1) (qq_ne hp) (qq_ne hq) (qq_ne hr) (qq_ne2 hpq)
    (qq_ne2 hpr) (qq_ne2 hqr) with ⟨a0, a1⟩ | ⟨a0, a1⟩ | ⟨a0, a1⟩ | ⟨a0, a1⟩
  · exact Or.inl (qq_ext a0 a1)
  · exact Or.inr (Or.inl (qq_ext a0 a1))
  · exact Or.inr (Or.inr (Or.inl (qq_ext a0 a1)))
  · exact Or.inr (Or.inr (Or.inr (qq_ext a0 a1)))

theorem decomp {m : ℕ} (c : Fin m → Fin 2 → QQ) (hf : ¬ FP c) :
    ∃ (σ0 σ1 : Fin m → ZMod 2) (lab : Fin m → QQ), (∀ j, σ0 j ≠ 0 ∨ σ1 j ≠ 0) ∧
      (∀ x : XX m, syn c x = ∑ j, (σ0 j * x j 0 + σ1 j * x j 1) • lab j) ∧
      (∀ q ∈ labOf c, q ≠ 0 → ∃ j, lab j = q) ∧ (∀ j, lab j ∈ labOf c) := by
  classical
  refine ⟨fun j => if c j 0 = 0 then 0 else 1,
    fun j => if c j 0 = 0 then 1 else if c j 1 = 0 then 0 else 1,
    fun j => if c j 0 = 0 then c j 1 else c j 0, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h0 : c j 0 = 0
    · right
      simp [h0]
    · left
      simp [h0]
  · intro x
    rw [syn_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Fin.sum_univ_two]
    by_cases h0 : c j 0 = 0
    · simp [h0]
    · by_cases h1 : c j 1 = 0
      · simp [h0, h1]
      · have heq : c j 0 = c j 1 := by
          by_contra hne
          exact hf ⟨j, h0, h1, hne⟩
        simp only [h0, h1, if_false, one_mul]
        rw [heq, add_smul]
  · intro q hq hq0
    simp only [labOf, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hq
    obtain ⟨j, hj | hj⟩ := hq
    · refine ⟨j, ?_⟩
      have h0 : c j 0 ≠ 0 := hj ▸ hq0
      simp [h0, hj]
    · refine ⟨j, ?_⟩
      by_cases h0 : c j 0 = 0
      · simp [h0, hj]
      · have h1 : c j 1 ≠ 0 := hj ▸ hq0
        have heq : c j 0 = c j 1 := by
          by_contra hne
          exact hf ⟨j, h0, h1, hne⟩
        simp [h0, heq, hj]
  · intro j
    simp only [labOf, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    refine ⟨j, ?_⟩
    by_cases h0 : c j 0 = 0
    · right
      simp [h0]
    · left
      simp [h0]

theorem two_labels {m : ℕ} (c : Fin m → Fin 2 → QQ) (h2 : hOf c = 2) (lab : Fin m → QQ)
    (hlabmem : ∀ q ∈ labOf c, q ≠ 0 → ∃ j, lab j = q) :
    ∃ a b, lab a ≠ 0 ∧ lab b ≠ 0 ∧ lab a ≠ lab b := by
  by_contra hno
  push_neg at hno
  have hle : hOf c ≤ 1 := by
    by_cases hz : ∃ a, lab a ≠ 0
    · obtain ⟨a, ha⟩ := hz
      have hsub : (↑(labOf c) : Set QQ) ⊆ insert 0 {lab a} := by
        intro q hq
        by_cases hq0 : q = 0
        · exact Set.mem_insert_iff.mpr (Or.inl hq0)
        · apply Set.mem_insert_of_mem
          obtain ⟨j, hj⟩ := hlabmem q hq hq0
          rw [Set.mem_singleton_iff, ← hj]
          exact hno j a (hj ▸ hq0) ha
      unfold hOf
      calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (↑(labOf c) : Set QQ))
          ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (insert 0 {lab a} : Set QQ)) :=
            Submodule.finrank_mono (Submodule.span_mono hsub)
        _ = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({lab a} : Set QQ)) := by
            rw [Submodule.span_insert_zero]
        _ = 1 := finrank_span_singleton ha
        _ ≤ 1 := le_refl 1
    · push_neg at hz
      have hb : Submodule.span (ZMod 2) (↑(labOf c) : Set QQ) = ⊥ := by
        rw [Submodule.span_eq_bot]
        intro q hq
        by_contra hq0
        obtain ⟨j, hj⟩ := hlabmem q hq hq0
        exact hq0 (hj ▸ hz j)
      unfold hOf
      rw [hb, finrank_bot]
      omega
  omega

theorem upper_two_proof {m e : ℕ} (c : Fin m → Fin 2 → QQ) (h2 : hOf c = 2) (hf : ¬ FP c)
    (hr : 2 ≤ m - e) :
    ∃ S, S.card ≤ (m - e - 2) + (if m - e = 2 ∧ ((labOf c).erase 0).card = 3 then 1 else 0) ∧
      GoodS c e S := by
  classical
  obtain ⟨σ0, σ1, lab, hσ, hsyn, hlabmem, hlab_in⟩ := decomp c hf
  obtain ⟨a, b, ha0, hb0, hab⟩ := two_labels c h2 lab hlabmem
  have hne : a ≠ b := fun h => hab (by rw [h])
  let sel : Fin m → XX m →ₗ[ZMod 2] ZMod 2 := fun j => σ0 j • projL j 0 + σ1 j • projL j 1
  have hsel : ∀ j x, sel j x = σ0 j * x j 0 + σ1 j * x j 1 := fun j x => by
    simp [sel, projL_apply]
  by_cases h3 : ∃ k, lab k ≠ 0 ∧ lab k ≠ lab a ∧ lab k ≠ lab b
  · obtain ⟨k, hk0, hka, hkb⟩ := h3
    have hak : a ≠ k := fun h => hka (by rw [h])
    have hbk : b ≠ k := fun h => hkb (by rw [h])
    have hlab4 : ∀ j, lab j = 0 ∨ lab j = lab a ∨ lab j = lab b ∨ lab j = lab k := fun j =>
      four_qq ha0 hb0 hk0 hab (Ne.symm hka) (Ne.symm hkb) (lab j)
    have nz3 : ((labOf c).erase 0).card = 3 := by
      apply le_antisymm
      · have h1 : (labOf c).erase 0 ⊆ Finset.univ.erase 0 :=
          Finset.erase_subset_erase _ (Finset.subset_univ _)
        have h4 := Finset.card_le_card h1
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h4
        have h5 : Fintype.card QQ = 4 := by simp
        omega
      · have h1 : ({lab a, lab b, lab k} : Finset QQ) ⊆ (labOf c).erase 0 := by
          intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with h | h | h <;> rw [h]
          · exact Finset.mem_erase.mpr ⟨ha0, hlab_in a⟩
          · exact Finset.mem_erase.mpr ⟨hb0, hlab_in b⟩
          · exact Finset.mem_erase.mpr ⟨hk0, hlab_in k⟩
        have h4 := Finset.card_le_card h1
        rw [Finset.card_eq_three.mpr ⟨lab a, lab b, lab k, hab, Ne.symm hka, Ne.symm hkb, rfl⟩]
          at h4
        exact h4
    obtain ⟨R, hRdef⟩ : ∃ R : Finset (Fin m), R = {a, b, k} := ⟨_, rfl⟩
    have hRc : R.card = 3 := by
      rw [hRdef]
      exact Finset.card_eq_three.mpr ⟨a, b, k, hne, hak, hbk, rfl⟩
    obtain ⟨B, hBsub, hBc⟩ := Finset.exists_subset_card_eq (s := Finset.univ \ R)
      (n := m - e - 3) (by rw [Finset.card_univ_diff, Fintype.card_fin, hRc]; omega)
    have hBR : Disjoint B R := Finset.disjoint_of_subset_left hBsub Finset.sdiff_disjoint
    obtain ⟨E, hEdef⟩ : ∃ E : Finset (Fin m), E = (Finset.univ \ B) \ R := ⟨_, rfl⟩
    have hRsub : R ⊆ Finset.univ \ B := fun j hj =>
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun h => Finset.disjoint_left.mp hBR h hj⟩
    have hEc : E.card ≤ e := by
      have h1 : E.card = (Finset.univ \ B).card - R.card := by
        rw [hEdef, Finset.card_sdiff_of_subset hRsub]
      have h4 := Finset.card_le_card hRsub
      rw [Finset.card_univ_diff, Fintype.card_fin] at h1 h4
      omega
    let Ea : Fin m → Finset (Fin m) := fun r => E.filter (fun j => lab j = lab r)
    let G3 : XX m →ₗ[ZMod 2] ZMod 2 := sel k + ∑ j ∈ Ea k, sel j
    have hRlab : ∀ r1 ∈ R, ∀ r2 ∈ R, r1 ≠ r2 → lab r1 ≠ lab r2 := by
      intro r1 hr1 r2 hr2 h12
      rw [hRdef] at hr1 hr2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr1 hr2
      rcases hr1 with h1 | h1 | h1 <;> rcases hr2 with h2 | h2 | h2 <;> rw [h1, h2] <;>
        rw [h1, h2] at h12 <;>
        (first
          | exact absurd rfl h12
          | exact hab
          | exact Ne.symm hab
          | exact hka
          | exact Ne.symm hka
          | exact hkb
          | exact Ne.symm hkb)
    refine ⟨insert G3 (B.image sel), ?_, upper_core c σ0 σ1 hσ B R hBR (by rw [← hEdef]; exact hEc)
      Ea (fun r _ => by rw [← hEdef]; exact Finset.filter_subset _ _) ?_ _ ?_⟩
    · have h1 := Finset.card_insert_le G3 (B.image sel)
      have h4 := Finset.card_image_le (s := B) (f := sel)
      by_cases hr2 : m - e = 2
      · rw [if_pos ⟨hr2, nz3⟩]
        omega
      · omega
    · intro r1 hr1 r2 hr2 h12
      rw [Finset.disjoint_filter]
      intro j _ e1 e2
      exact hRlab r1 hr1 r2 hr2 h12 (e1.symm.trans e2)
    · intro x hx hq
      have hBz : ∀ j ∈ B, σ0 j * x j 0 + σ1 j * x j 1 = 0 := by
        intro j hj
        rw [← hsel]
        exact hq _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))
      have hG : σ0 k * x k 0 + σ1 k * x k 1 +
          ∑ j ∈ E.filter (fun j => lab j = lab k), (σ0 j * x j 0 + σ1 j * x j 1) = 0 := by
        have h1 := hq G3 (Finset.mem_insert_self _ _)
        simp only [G3, Ea, LinearMap.add_apply, LinearMap.sum_apply, hsel] at h1
        exact h1
      have h0 : ∑ j, (σ0 j * x j 0 + σ1 j * x j 1) • lab j = 0 := (hsyn x).symm.trans hx
      rw [split_sum B R hBR _ (fun j hj => by rw [hBz j hj, zero_smul]), ← hEdef, hRdef,
        Finset.sum_insert (by simp [hne, hak]), Finset.sum_pair hbk,
        class3 E lab _ (lab a) (lab b) (lab k) ha0 hb0 hk0 hab (Ne.symm hka) (Ne.symm hkb)
          (fun j _ => hlab4 j)] at h0
      have hk' : (σ0 k * x k 0 + σ1 k * x k 1 +
          ∑ j ∈ E.filter (fun j => lab j = lab k), (σ0 j * x j 0 + σ1 j * x j 1)) • lab k = 0 := by
        rw [hG, zero_smul]
      have hkey : (σ0 a * x a 0 + σ1 a * x a 1 +
          ∑ j ∈ E.filter (fun j => lab j = lab a), (σ0 j * x j 0 + σ1 j * x j 1)) • lab a +
          (σ0 b * x b 0 + σ1 b * x b 1 +
          ∑ j ∈ E.filter (fun j => lab j = lab b), (σ0 j * x j 0 + σ1 j * x j 1)) • lab b = 0 := by
        linear_combination (norm := module) h0 - hk'
      obtain ⟨ia, ib⟩ := indep_qq ha0 hb0 hab hkey
      refine ⟨hBz, fun r hr => ?_⟩
      rw [hRdef] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      show _ = ∑ j ∈ E.filter (fun j => lab j = lab r), (σ0 j * x j 0 + σ1 j * x j 1)
      rcases hr with h | h | h <;> rw [h]
      · linear_combination ia - zmod2_two (∑ j ∈ E.filter (fun j => lab j = lab a),
          (σ0 j * x j 0 + σ1 j * x j 1))
      · linear_combination ib - zmod2_two (∑ j ∈ E.filter (fun j => lab j = lab b),
          (σ0 j * x j 0 + σ1 j * x j 1))
      · linear_combination hG - zmod2_two (∑ j ∈ E.filter (fun j => lab j = lab k),
          (σ0 j * x j 0 + σ1 j * x j 1))
  · push_neg at h3
    have hlab3 : ∀ j, lab j = 0 ∨ lab j = lab a ∨ lab j = lab b := by
      intro j
      by_cases hj0 : lab j = 0
      · exact Or.inl hj0
      by_cases hja : lab j = lab a
      · exact Or.inr (Or.inl hja)
      exact Or.inr (Or.inr (h3 j hj0 hja))
    obtain ⟨R, hRdef⟩ : ∃ R : Finset (Fin m), R = {a, b} := ⟨_, rfl⟩
    have hRc : R.card = 2 := by
      rw [hRdef]
      exact Finset.card_pair hne
    obtain ⟨B, hBsub, hBc⟩ := Finset.exists_subset_card_eq (s := Finset.univ \ R)
      (n := m - e - 2) (by rw [Finset.card_univ_diff, Fintype.card_fin, hRc]; omega)
    have hBR : Disjoint B R := Finset.disjoint_of_subset_left hBsub Finset.sdiff_disjoint
    obtain ⟨E, hEdef⟩ : ∃ E : Finset (Fin m), E = (Finset.univ \ B) \ R := ⟨_, rfl⟩
    have hRsub : R ⊆ Finset.univ \ B := fun j hj =>
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun h => Finset.disjoint_left.mp hBR h hj⟩
    have hEc : E.card ≤ e := by
      have h1 : E.card = (Finset.univ \ B).card - R.card := by
        rw [hEdef, Finset.card_sdiff_of_subset hRsub]
      have h4 := Finset.card_le_card hRsub
      rw [Finset.card_univ_diff, Fintype.card_fin] at h1 h4
      omega
    let Ea : Fin m → Finset (Fin m) := fun r => E.filter (fun j => lab j = lab r)
    have hRlab : ∀ r1 ∈ R, ∀ r2 ∈ R, r1 ≠ r2 → lab r1 ≠ lab r2 := by
      intro r1 hr1 r2 hr2 h12
      rw [hRdef] at hr1 hr2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr1 hr2
      rcases hr1 with h1 | h1 <;> rcases hr2 with h2 | h2 <;> rw [h1, h2] <;>
        rw [h1, h2] at h12 <;>
        (first
          | exact absurd rfl h12
          | exact hab
          | exact Ne.symm hab)
    refine ⟨B.image sel, ?_, upper_core c σ0 σ1 hσ B R hBR (by rw [← hEdef]; exact hEc)
      Ea (fun r _ => by rw [← hEdef]; exact Finset.filter_subset _ _) ?_ _ ?_⟩
    · have h4 := Finset.card_image_le (s := B) (f := sel)
      omega
    · intro r1 hr1 r2 hr2 h12
      rw [Finset.disjoint_filter]
      intro j _ e1 e2
      exact hRlab r1 hr1 r2 hr2 h12 (e1.symm.trans e2)
    · intro x hx hq
      have hBz : ∀ j ∈ B, σ0 j * x j 0 + σ1 j * x j 1 = 0 := by
        intro j hj
        rw [← hsel]
        exact hq _ (Finset.mem_image_of_mem _ hj)
      have h0 : ∑ j, (σ0 j * x j 0 + σ1 j * x j 1) • lab j = 0 := (hsyn x).symm.trans hx
      rw [split_sum B R hBR _ (fun j hj => by rw [hBz j hj, zero_smul]), ← hEdef, hRdef,
        Finset.sum_pair hne,
        class2 E lab _ (lab a) (lab b) ha0 hb0 hab (fun j _ => hlab3 j)] at h0
      have hkey : (σ0 a * x a 0 + σ1 a * x a 1 +
          ∑ j ∈ E.filter (fun j => lab j = lab a), (σ0 j * x j 0 + σ1 j * x j 1)) • lab a +
          (σ0 b * x b 0 + σ1 b * x b 1 +
          ∑ j ∈ E.filter (fun j => lab j = lab b), (σ0 j * x j 0 + σ1 j * x j 1)) • lab b = 0 := by
        linear_combination (norm := module) h0
      obtain ⟨ia, ib⟩ := indep_qq ha0 hb0 hab hkey
      refine ⟨hBz, fun r hr => ?_⟩
      rw [hRdef] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      show _ = ∑ j ∈ E.filter (fun j => lab j = lab r), (σ0 j * x j 0 + σ1 j * x j 1)
      rcases hr with h | h <;> rw [h]
      · linear_combination ia - zmod2_two (∑ j ∈ E.filter (fun j => lab j = lab a),
          (σ0 j * x j 0 + σ1 j * x j 1))
      · linear_combination ib - zmod2_two (∑ j ∈ E.filter (fun j => lab j = lab b),
          (σ0 j * x j 0 + σ1 j * x j 1))

theorem special {m e : ℕ} (c : Fin m → Fin 2 → QQ) (h2 : hOf c = 2) (hf : ¬ FP c)
    (hr : m - e = 2) (h3 : ((labOf c).erase 0).card = 3) :
    ¬ GoodV e (LinearMap.ker (syn c)) := special_proof c hf hr h3

theorem upper_h0 {m e : ℕ} (c : Fin m → Fin 2 → QQ) (h0 : hOf c = 0) :
    ∃ S, S.card ≤ m - e ∧ GoodS c e S := upper_h0_proof c

-- Part C1: one special site absorbs the checks.

theorem exists_site {m : ℕ} (c : Fin m → Fin 2 → QQ) (h0 : hOf c ≠ 0) :
    ∃ i, c i 0 ≠ 0 ∨ c i 1 ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply h0
  unfold hOf
  have hb : Submodule.span (ZMod 2) (↑(labOf c) : Set QQ) = ⊥ := by
    rw [Submodule.span_eq_bot]
    intro q hq
    simp only [labOf, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    obtain ⟨i, hi | hi⟩ := hq
    · rw [hi, (hall i).1]
    · rw [hi, (hall i).2]
  rw [hb, finrank_bot]

theorem LB_fin : ∀ p0 p1 r0 r1 : ZMod 2, (p0 ≠ 0 ∨ p1 ≠ 0 ∨ r0 ≠ 0 ∨ r1 ≠ 0) →
    ∃ w0 w1 : ZMod 2, (w0 ≠ 0 ∨ w1 ≠ 0) ∧ ∀ k0 k1 : ZMod 2, ∃ α β γ : ZMod 2,
      ∀ z0 z1 : ZMod 2, ((p0 * z0 + r0 * z1 = k0 ∧ p1 * z0 + r1 * z1 = k1) ∨
        (p0 * z0 + r0 * z1 = k0 + w0 ∧ p1 * z0 + r1 * z1 = k1 + w1)) →
        z0 * z1 = α * z0 + β * z1 + γ := by
  decide

theorem LA_fin : ∀ p0 p1 r0 r1 w0 w1 : ZMod 2, (w0 ≠ 0 ∨ w1 ≠ 0) →
    ∃ d0 d1 : ZMod 2, (d0 ≠ 0 ∨ d1 ≠ 0) ∧ ((p0 * d0 + r0 * d1 = 0 ∧ p1 * d0 + r1 * d1 = 0) ∨
      (p0 * d0 + r0 * d1 = w0 ∧ p1 * d0 + r1 * d1 = w1)) := by
  decide

theorem line_fin : ∀ d0 d1 z0 z1 : ZMod 2, (d0 ≠ 0 ∨ d1 ≠ 0) → d1 * z0 + d0 * z1 = 0 →
    (z0 = 0 ∧ z1 = 0) ∨ (z0 = d0 ∧ z1 = d1) := by
  decide

theorem sum_closed {ι : Type*} (s : Finset ι) (f g : ι → ZMod 2) (w0 w1 : ZMod 2)
    (h : ∀ j ∈ s, (f j = 0 ∧ g j = 0) ∨ (f j = w0 ∧ g j = w1)) :
    ((∑ j ∈ s, f j) = 0 ∧ (∑ j ∈ s, g j) = 0) ∨ ((∑ j ∈ s, f j) = w0 ∧ (∑ j ∈ s, g j) = w1) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert k s' hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have h1 := h k (Finset.mem_insert_self k s')
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
      rw [a1, b1, a2, b2]
    · left; simp
    · right; simp
    · right; simp
    · left; exact ⟨zmod2_two _, zmod2_two _⟩

theorem upper_one_proof {m e : ℕ} (c : Fin m → Fin 2 → QQ) (h0 : hOf c ≠ 0) :
    ∃ S, S.card ≤ m - e - 1 ∧ GoodS c e S := by
  classical
  obtain ⟨i1, hi1⟩ := exists_site c h0
  have hnz : c i1 0 0 ≠ 0 ∨ c i1 0 1 ≠ 0 ∨ c i1 1 0 ≠ 0 ∨ c i1 1 1 ≠ 0 := by
    rcases hi1 with h | h
    · rcases qq_ne h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases qq_ne h with h' | h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
  obtain ⟨w0, w1, hw, hLB⟩ := LB_fin _ _ _ _ hnz
  have hdd : ∀ j : Fin m, ∃ d0 d1 : ZMod 2, (d0 ≠ 0 ∨ d1 ≠ 0) ∧
      ((c j 0 0 * d0 + c j 1 0 * d1 = 0 ∧ c j 0 1 * d0 + c j 1 1 * d1 = 0) ∨
      (c j 0 0 * d0 + c j 1 0 * d1 = w0 ∧ c j 0 1 * d0 + c j 1 1 * d1 = w1)) :=
    fun j => LA_fin _ _ _ _ _ _ hw
  choose dd0 dd1 hdne hdc using hdd
  have hcardR : m - e - 1 ≤ (Finset.univ.erase i1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i1), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨R, hRsub, hRc⟩ := Finset.exists_subset_card_eq hcardR
  set E := (Finset.univ.erase i1) \ R with hE
  have hEc : E.card ≤ e := by
    rw [hE, Finset.card_sdiff_of_subset hRsub, Finset.card_erase_of_mem (Finset.mem_univ i1),
      Finset.card_univ, Fintype.card_fin, hRc]
    omega
  let κ0 : ZMod 2 := ∑ j ∈ E, (c j 0 0 + c j 1 0)
  let κ1 : ZMod 2 := ∑ j ∈ E, (c j 0 1 + c j 1 1)
  obtain ⟨α, β, γ, hαβγ⟩ := hLB κ0 κ1
  let qR : Fin m → XX m →ₗ[ZMod 2] ZMod 2 := fun j => dd1 j • projL j 0 + dd0 j • projL j 1
  let P : Fin m → XX m →ₗ[ZMod 2] ZMod 2 := fun j => if j ∈ R then (dd0 j * dd1 j) • projL j 0 else
      if j = i1 then α • projL j 0 + β • projL j 1 else 0
  let d : Fin m → ZMod 2 := fun j => if j ∈ R then 0 else if j = i1 then γ else 0
  refine ⟨R.image qR, le_trans Finset.card_image_le hRc.le, P, d, fun x hsyn hq => ?_⟩
  have hline : ∀ j ∈ R, (x j 0 = 0 ∧ x j 1 = 0) ∨ (x j 0 = dd0 j ∧ x j 1 = dd1 j) := by
    intro j hj
    have := hq (qR j) (Finset.mem_image_of_mem _ hj)
    simp only [qR, LinearMap.add_apply, LinearMap.smul_apply, projL_apply, smul_eq_mul] at this
    exact line_fin _ _ _ _ (hdne j) this
  -- the R sites are exact
  have hRok : ∀ j ∈ R, j ∉ errs P d x := by
    intro j hj hmem
    simp only [errs, P, d, Finset.mem_filter, if_pos hj, LinearMap.smul_apply, projL_apply,
      smul_eq_mul, add_zero] at hmem
    apply hmem.2
    rcases hline j hj with ⟨a0, a1⟩ | ⟨a0, a1⟩
    · rw [a0, a1]
      ring
    · rw [a0, a1]
      have : ∀ a b : ZMod 2, a * b = a * b * a := by decide
      exact this _ _
  -- the special site is right when every site of E is (1,1)
  have hspec : (∀ j ∈ E, x j 0 = 1 ∧ x j 1 = 1) → i1 ∉ errs P d x := by
    intro hall hmem
    have hi1R : i1 ∉ R := fun h => by simpa using hRsub h
    simp only [errs, P, d, Finset.mem_filter, if_neg hi1R, if_pos rfl, LinearMap.add_apply,
      LinearMap.smul_apply, projL_apply, smul_eq_mul] at hmem
    apply hmem.2
    have hsplit : ∀ t : Fin 2, ∑ i, ∑ u, c i u t * x i u =
        (c i1 0 t * x i1 0 + c i1 1 t * x i1 1) + ∑ j ∈ R, (c j 0 t * x j 0 + c j 1 t * x j 1) +
          ∑ j ∈ E, (c j 0 t * x j 0 + c j 1 t * x j 1) := by
      intro t
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i1), Fin.sum_univ_two,
        ← Finset.sum_sdiff hRsub]
      simp only [Fin.sum_univ_two]
      rw [hE]
      ring
    have hEv : ∀ t : Fin 2, ∑ j ∈ E, (c j 0 t * x j 0 + c j 1 t * x j 1) =
        ∑ j ∈ E, (c j 0 t + c j 1 t) := by
      intro t
      apply Finset.sum_congr rfl
      intro j hj
      rw [(hall j hj).1, (hall j hj).2]
      ring
    have hRv : (∑ j ∈ R, (c j 0 0 * x j 0 + c j 1 0 * x j 1) = 0 ∧
        ∑ j ∈ R, (c j 0 1 * x j 0 + c j 1 1 * x j 1) = 0) ∨
        (∑ j ∈ R, (c j 0 0 * x j 0 + c j 1 0 * x j 1) = w0 ∧
        ∑ j ∈ R, (c j 0 1 * x j 0 + c j 1 1 * x j 1) = w1) := by
      apply sum_closed R (fun j => c j 0 0 * x j 0 + c j 1 0 * x j 1)
        (fun j => c j 0 1 * x j 0 + c j 1 1 * x j 1) w0 w1
      intro j hj
      rcases hline j hj with ⟨a0, a1⟩ | ⟨a0, a1⟩
      · left
        rw [a0, a1]
        simp
      · rw [a0, a1]
        exact hdc j
    have s0 := congrFun hsyn 0
    have s1 := congrFun hsyn 1
    rw [syn_apply, hsplit, hEv] at s0 s1
    simp only [Pi.zero_apply] at s0 s1
    apply hαβγ
    rcases hRv with ⟨r0, r1⟩ | ⟨r0, r1⟩
    · left
      rw [r0] at s0
      rw [r1] at s1
      constructor
      · linear_combination s0 - zmod2_two κ0
      · linear_combination s1 - zmod2_two κ1
    · right
      rw [r0] at s0
      rw [r1] at s1
      constructor
      · linear_combination s0 - zmod2_two κ0 - zmod2_two w0
      · linear_combination s1 - zmod2_two κ1 - zmod2_two w1
  have hsub : errs P d x ⊆ insert i1 (E.filter (fun j => x j 0 = 1 ∧ x j 1 = 1)) := by
    intro j hj
    by_cases hjR : j ∈ R
    · exact absurd hj (hRok j hjR)
    by_cases hji : j = i1
    · rw [hji]
      exact Finset.mem_insert_self _ _
    apply Finset.mem_insert_of_mem
    rw [Finset.mem_filter]
    have hjE : j ∈ E := by
      rw [hE, Finset.mem_sdiff, Finset.mem_erase]
      exact ⟨⟨hji, Finset.mem_univ j⟩, hjR⟩
    simp only [errs, P, d, Finset.mem_filter, if_neg hjR, if_neg hji,
      LinearMap.zero_apply, add_zero] at hj
    refine ⟨hjE, ?_⟩
    have key : ∀ a b : ZMod 2, a * b ≠ 0 → a = 1 ∧ b = 1 := by decide
    exact key _ _ hj.2
  by_cases hall : ∀ j ∈ E, x j 0 = 1 ∧ x j 1 = 1
  · have hs2 : errs P d x ⊆ E.filter (fun j => x j 0 = 1 ∧ x j 1 = 1) := by
      intro j hj
      rcases Finset.mem_insert.mp (hsub hj) with h | h
      · exact absurd (h ▸ hj) (hspec hall)
      · exact h
    exact (Finset.card_le_card hs2).trans ((Finset.card_filter_le _ _).trans hEc)
  · have hex : ∃ j ∈ E, ¬ (x j 0 = 1 ∧ x j 1 = 1) := by
      by_contra hc
      push_neg at hc
      exact hall (fun j hj => hc j hj)
    have hlt : (E.filter (fun j => x j 0 = 1 ∧ x j 1 = 1)).card < E.card :=
      Finset.card_lt_card (Finset.filter_ssubset.mpr hex)
    calc (errs P d x).card ≤ (insert i1 (E.filter (fun j => x j 0 = 1 ∧ x j 1 = 1))).card :=
          Finset.card_le_card hsub
      _ ≤ (E.filter (fun j => x j 0 = 1 ∧ x j 1 = 1)).card + 1 := Finset.card_insert_le _ _
      _ ≤ e := by omega

theorem upper_one {m e : ℕ} (c : Fin m → Fin 2 → QQ) (h0 : hOf c ≠ 0) :
    ∃ S, S.card ≤ m - e - 1 ∧ GoodS c e S := upper_one_proof c h0

theorem upper_two {m e : ℕ} (c : Fin m → Fin 2 → QQ) (h2 : hOf c = 2) (hf : ¬ FP c)
    (hr : 2 ≤ m - e) :
    ∃ S, S.card ≤ (m - e - 2) + (if m - e = 2 ∧ ((labOf c).erase 0).card = 3 then 1 else 0) ∧
      GoodS c e S := upper_two_proof c h2 hf hr

theorem main : ∀ (m e L : Nat),
  let F := ZMod 2
  let Q := Fin 2 → F
  let I := Fin m
  let X := I → Fin 2 → F
  ∀ (c : I → Fin 2 → Q) (base : X),
    let H := List Bool
    let D := X →ₗ[F] F
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    let syndrome := fun (x : X) (j : Fin 2) => ∑ i : I, ∑ u : Fin 2, (c i u j) * x i u
    let labels := (Finset.univ : Finset I).biUnion (fun i => ({c i 0, c i 1} : Finset Q))
    let h := Module.finrank F (Submodule.span F (↑labels : Set Q))
    let fullPair := ∃ i, c i 0 ≠ 0 ∧ c i 1 ≠ 0 ∧ c i 0 ≠ c i 1
    let r := m-e
    let p := if h = 0 then r else if h = 1 ∨ fullPair then r-1
      else (r-2) + (if r = 2 ∧ (labels.erase 0).card = 3 then 1 else 0)
    (∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → I → D) (d : H → I → F),
      T.card < L ∧ ∀ x : X, syndrome x = syndrome base →
        let path := run T ask bias x
        ((Finset.univ : Finset I).filter (fun i => x i 0 * x i 1 ≠ P path i x+d path i)).card ≤ e) ↔
      2^p ≤ L := by
  intro m e L F Q I X c base H D run syndrome labels h fullPair r p
  have hh : h = hOf c := rfl
  have hfp : fullPair = FP c := rfl
  have hlab : labels = labOf c := rfl
  have hcases : (hOf c = 0 ∧ p = m - e) ∨
      (hOf c ≠ 0 ∧ (hOf c = 1 ∨ FP c) ∧ p = m - e - 1) ∨
      (hOf c = 2 ∧ ¬ FP c ∧
        p = (m - e - 2) + (if m - e = 2 ∧ ((labOf c).erase 0).card = 3 then 1 else 0)) := by
    by_cases h0 : h = 0
    · exact Or.inl ⟨h0, if_pos h0⟩
    · right
      by_cases h1 : h = 1 ∨ fullPair
      · exact Or.inl ⟨h0, h1, (if_neg h0).trans (if_pos h1)⟩
      · right
        have h2 := h_le_two c
        refine ⟨by rw [← hh]; push_neg at h1; omega, fun hf => h1 (Or.inr hf), ?_⟩
        exact (if_neg h0).trans (if_neg h1)
  constructor
  · rintro ⟨T, ask, bias, P, d, hT, hok⟩
    refine lower_glue c base p ?_ T ask bias P d hT (fun x hx => hok x hx)
    intro V hVK x0 P0 d0 hgood
    have hG : GoodV e V := ⟨x0, P0, d0, hgood⟩
    rw [card_eq_pow, card_eq_pow, ← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have hdim := dimK c
    have hmono := Submodule.finrank_mono hVK
    have hgen := lower_gen c V hG
    rcases hcases with ⟨h0, hp⟩ | ⟨h0, h1, hp⟩ | ⟨h2, hf, hp⟩
    · rw [hp]
      omega
    · rw [hp]
      rcases h1 with h1 | hf
      · omega
      · have h2 := fp_h c hf
        have := lower_fp c hf V hVK hG
        omega
    · rw [hp]
      split_ifs with hs
      · have hlt : Module.finrank (ZMod 2) V < Module.finrank (ZMod 2) (LinearMap.ker (syn c)) := by
          by_contra hge
          push_neg at hge
          have heq := Submodule.eq_of_le_of_finrank_eq hVK (le_antisymm hmono hge)
          exact special c h2 hf hs.1 hs.2 (heq ▸ hG)
        omega
      · omega
  · intro hp
    have key : ∃ S, S.card ≤ p ∧ GoodS c e S := by
      rcases hcases with ⟨h0, hp⟩ | ⟨h0, h1, hp⟩ | ⟨h2, hf, hp⟩
      · rw [hp]
        exact upper_h0 c h0
      · rw [hp]
        exact upper_one c h0
      · by_cases hr : 2 ≤ m - e
        · rw [hp]
          exact upper_two c h2 hf hr
        · obtain ⟨S, hS, hg⟩ := upper_one c (by omega : hOf c ≠ 0)
          exact ⟨S, by omega, hg⟩
    obtain ⟨S, hS, P, d, hgood⟩ := key
    obtain ⟨T, ask', bias, P', d', hT, hok⟩ :=
      upper_glue c base S (le_trans (Nat.pow_le_pow_right (by norm_num) hS) hp) P d hgood
    exact ⟨T, ask', bias, P', d', hT, fun x hx => hok x hx⟩

end PEqualNP.Outside.L_lib_993_aux

theorem PEqualNP.Outside.L_lib_993 : ∀ (m e L : Nat),
  let F := ZMod 2
  let Q := Fin 2 → F
  let I := Fin m
  let X := I → Fin 2 → F
  ∀ (c : I → Fin 2 → Q) (base : X),
    let H := List Bool
    let D := X →ₗ[F] F
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : X) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) []
    let syndrome := fun (x : X) (j : Fin 2) => ∑ i : I, ∑ u : Fin 2, (c i u j) * x i u
    let labels := (Finset.univ : Finset I).biUnion (fun i => ({c i 0, c i 1} : Finset Q))
    let h := Module.finrank F (Submodule.span F (↑labels : Set Q))
    let fullPair := ∃ i, c i 0 ≠ 0 ∧ c i 1 ≠ 0 ∧ c i 0 ≠ c i 1
    let r := m-e
    let p := if h = 0 then r else if h = 1 ∨ fullPair then r-1
      else (r-2) + (if r = 2 ∧ (labels.erase 0).card = 3 then 1 else 0)
    (∃ (T : Finset H) (ask : H → D) (bias : H → F) (P : H → I → D) (d : H → I → F),
      T.card < L ∧ ∀ x : X, syndrome x = syndrome base →
        let path := run T ask bias x
        ((Finset.univ : Finset I).filter (fun i => x i 0 * x i 1 ≠ P path i x+d path i)).card ≤ e) ↔
      2^p ≤ L :=
  PEqualNP.Outside.L_lib_993_aux.main
