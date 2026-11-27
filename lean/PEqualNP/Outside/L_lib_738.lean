import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_738_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_prefix (gs : List Gate) (init : List Bool) :
    ∃ e, gs.foldl step init = init ++ e := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨e, he⟩ := ih (step init g)
    refine ⟨[g.op.eval (g.inputs.map fun i => init.getD i false)] ++ e, ?_⟩
    rw [List.foldl_cons, he]
    simp [step]

theorem foldl_length (gs : List Gate) (init : List Bool) :
    (gs.foldl step init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_prefix (gs : List Gate) (init : List Bool) (c : ℕ) (hc : c < init.length) :
    (gs.foldl step init).getD c false = init.getD c false := by
  obtain ⟨e, he⟩ := foldl_prefix gs init
  rw [he, List.getD_append _ _ _ _ hc]

theorem foldl_gate (gs : List Gate) (init : List Bool) (p : ℕ) (hp : p < gs.length) :
    (gs.foldl step init).getD (init.length + p) false =
      gs[p].op.eval (gs[p].inputs.map fun c =>
        if c < init.length + p then (gs.foldl step init).getD c false else false) := by
  set W0 := (gs.take p).foldl step init with hW0
  have hlen0 : W0.length = init.length + p := by
    rw [hW0, foldl_length, List.length_take]; omega
  have hfull : gs.foldl step init = (gs.drop (p+1)).foldl step (step W0 gs[p]) := by
    calc gs.foldl step init = (gs.take p ++ gs.drop p).foldl step init := by
          rw [List.take_append_drop]
      _ = _ := by rw [List.foldl_append, List.drop_eq_getElem_cons hp, List.foldl_cons]
  have hslen : (step W0 gs[p]).length = W0.length + 1 := by simp [step]
  rw [hfull, getD_prefix _ _ _ (by rw [hslen, hlen0]; omega)]
  have hv : (step W0 gs[p]).getD (init.length + p) false =
      gs[p].op.eval (gs[p].inputs.map fun i => W0.getD i false) := by
    rw [step, List.getD_append_right _ _ _ _ (by omega)]
    simp [hlen0]
  rw [hv]
  congr 1
  apply List.map_congr_left
  intro c _
  split_ifs with hc
  · rw [getD_prefix (gs.drop (p+1)) (step W0 gs[p]) c (by rw [hslen, hlen0]; omega)]
    simp only [step]
    rw [List.getD_append _ _ _ _ (by rw [hlen0]; omega)]
  · exact List.getD_eq_default _ _ (by omega)

theorem foldl_map_eval (hs : List Gate) (W : List Bool)
    (h : ∀ g ∈ hs, ∀ c ∈ g.inputs, c < W.length) :
    hs.foldl step W = W ++ hs.map (fun g => g.op.eval (g.inputs.map fun c => W.getD c false)) := by
  induction hs generalizing W with
  | nil => simp
  | cons g hs ih =>
    rw [List.foldl_cons, ih]
    · have : (hs.map fun g' => g'.op.eval (g'.inputs.map fun c => (step W g).getD c false)) =
          hs.map (fun g' => g'.op.eval (g'.inputs.map fun c => W.getD c false)) := by
        apply List.map_congr_left
        intro g' hg'
        congr 1
        apply List.map_congr_left
        intro c hc
        simp only [step]
        rw [List.getD_append _ _ _ _ (h g' (by simp [hg']) c hc)]
      rw [this]
      simp [step]
    · intro g' hg' c hc
      have := h g' (by simp [hg']) c hc
      simp [step]
      omega

def names (r : ℕ) (x : Fin (2 ^ r)) : Finset (Fin (2 * r)) :=
  Finset.univ.filter (fun i : Fin (2 * r) => Nat.testBit x.val (i.val / 2) = decide (i.val % 2 = 1))

def supp (r : ℕ) (E : Circuit) (w : ℕ) : Finset (Fin (2 * r)) :=
  Finset.univ.filter (fun i : Fin (2 * r) =>
    (E.wires (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD w false = true)

noncomputable def price (r : ℕ) (C : Circuit) (p : Fin C.gates.length) : ℕ :=
  let S := supp r C (2 * r + p.val)
  @ite ℕ ((C.gates.get p).op = GateOp.or)
    (Classical.propDecidable _) 2 (if (∃ x, S ⊆ names r x) then
    (if S.card = 2 then 2 else if 3 ≤ S.card then 3 else 0)
  else 0)

def G : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => 2 ^ (n + 2) + Finset.univ.inf' Finset.univ_nonempty
      (fun a : Fin (n + 1) => G (a.val + 1) + G (n + 1 - a.val))
decreasing_by all_goals (have := a.isLt; omega)

theorem G_zero : G 0 = 0 := by rw [G]
theorem G_one : G 1 = 0 := by rw [G]

theorem G_split (a b : ℕ) : G (a + b) ≤ 2 ^ (a + b) + G a + G b := by
  rcases a with _ | a
  · simp [G_zero]
  rcases b with _ | b
  · simp [G_zero]
  rw [show a + 1 + (b + 1) = (a + b) + 2 by omega, G]
  have := Finset.inf'_le (s := Finset.univ)
    (fun c : Fin (a + b + 1) => G (c.val + 1) + G (a + b + 1 - c.val))
    (Finset.mem_univ (⟨a, by omega⟩ : Fin (a + b + 1)))
  simp only at this
  rw [show a + b + 1 - a = b + 1 by omega] at this
  omega

theorem G_exists (n : ℕ) : ∃ a : Fin (n + 1), G (n + 2) = 2 ^ (n + 2) + (G (a.val + 1) + G (n + 1 - a.val)) := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin (n + 1))))
    Finset.univ_nonempty (fun a : Fin (n + 1) => G (a.val + 1) + G (n + 1 - a.val))
  exact ⟨a, by rw [G, ha]⟩

theorem G_two : G 2 ≤ 4 := by
  have := G_split 1 1; simp [G_one] at this; omega

theorem G_le (m : ℕ) : 2 * G m ≤ 3 * 2 ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m 6 with h | h
  · have h2 := G_two
    have h3 := G_split 1 2
    have h4 := G_split 2 2
    have h5 := G_split 2 3
    simp only [G_one] at h3
    interval_cases m <;> simp_all [G_zero, G_one] <;> omega
  · have hs := G_split (m / 2) (m - m / 2)
    rw [show m / 2 + (m - m / 2) = m by omega] at hs
    have ha := ih (m / 2) (by omega)
    have hb := ih (m - m / 2) (by omega)
    have hu : 8 ≤ 2 ^ (m / 2) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hv : 2 ^ (m / 2) ≤ 2 ^ (m - m / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : 2 ^ m = 2 ^ (m / 2) * 2 ^ (m - m / 2) := by
      rw [← pow_add]; congr 1; omega
    rw [hm] at hs ⊢
    nlinarith

section lower

variable (r : ℕ) (C : Circuit)

theorem getD_ofFn_input (i : Fin (2 * r)) (j : ℕ) (hj : j < 2 * r) :
    (List.ofFn (fun h : Fin (2 * r) => decide (h = i))).getD j false = decide (j = i.val) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem mem_supp (E : Circuit) (w : ℕ) (i : Fin (2 * r)) : i ∈ supp r E w ↔
    (E.gates.foldl step (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD w false = true := by
  unfold supp; rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]; rfl

theorem supp_input (w : ℕ) (hw : w < 2 * r) : (supp r C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [mem_supp] at ha hb
  rw [getD_prefix _ _ _ (by simpa using hw), getD_ofFn_input r _ _ hw] at ha hb
  simp at ha hb
  exact Fin.ext (by omega)

theorem supp_out (w : ℕ) (hw : 2 * r + C.gates.length ≤ w) : supp r C w = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i
  rw [mem_supp, List.getD_eq_default _ _ (by rw [foldl_length]; simpa using hw)]
  simp

theorem supp_mem_gate (p : ℕ) (hp : p < C.gates.length) (i : Fin (2 * r)) :
    i ∈ supp r C (2 * r + p) ↔ (C.gates[p]).op.eval ((C.gates[p]).inputs.map
      fun c => decide (c < 2 * r + p ∧ i ∈ supp r C c)) = true := by
  have h := foldl_gate C.gates (List.ofFn (fun h : Fin (2 * r) => decide (h = i))) p hp
  rw [List.length_ofFn] at h
  have hf : ∀ c, (if c < 2 * r + p then
      (C.gates.foldl step (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD c false
      else false) = decide (c < 2 * r + p ∧ i ∈ supp r C c) := by
    intro c
    split_ifs with hc <;> simp [hc, mem_supp]
  simp only [hf] at h
  rw [mem_supp, h]

noncomputable def wt (p : Fin C.gates.length) : ℕ := price r C p * 2 ^ (supp r C (2 * r + p.val)).card

def fam (S U : Finset (Fin (2 * r))) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun p => supp r C (2 * r + p.val) ⊆ S ∧ ¬ supp r C (2 * r + p.val) ⊆ U)

def Claim (S : Finset (Fin (2 * r))) : Prop :=
  ∀ U, 2 * G (S \ U).card ≤ ∑ p ∈ fam r C S U, wt r C p

theorem claim_small (S : Finset (Fin (2 * r))) (hS : S.card ≤ 1) : Claim r C S := by
  intro U
  have : (S \ U).card ≤ 1 := (Finset.card_le_card Finset.sdiff_subset).trans hS
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> simp [G_zero, G_one]

theorem claim_union (A B S : Finset (Fin (2 * r))) (hA : Claim r C A) (hB : Claim r C B)
    (hAB : A ∪ B = S) (p0 : Fin C.gates.length) (h0 : supp r C (2 * r + p0.val) = S)
    (hpr : price r C p0 = 2) : Claim r C S := by
  intro U
  by_cases hAS : A = S
  · subst hAS; exact hA U
  by_cases hBS : B = S
  · subst hBS; exact hB U
  by_cases hSU : S ⊆ U
  · simp [Finset.sdiff_eq_empty_iff_subset.mpr hSU, G_zero]
  have hAs : A ⊆ S := hAB ▸ Finset.subset_union_left
  have hBs : B ⊆ S := hAB ▸ Finset.subset_union_right
  have hcard : (S \ U).card = (A \ U).card + (B \ (U ∪ A)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_union]
      rw [← hAB]
      simp only [Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [Finset.mem_sdiff, Finset.mem_union] at h1 h2
      tauto
  have hsub : insert p0 (fam r C A U ∪ fam r C B (U ∪ A)) ⊆ fam r C S U := by
    intro p hp
    simp only [fam, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp ⊢
    rcases hp with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h0]; exact ⟨subset_rfl, hSU⟩
    · exact ⟨h1.trans hAs, h2⟩
    · exact ⟨h1.trans hBs, fun h => h2 (h.trans Finset.subset_union_left)⟩
  have hnot : p0 ∉ fam r C A U ∪ fam r C B (U ∪ A) := by
    simp only [fam, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, h0]
    rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact hAS (Finset.Subset.antisymm hAs h1)
    · exact hBS (Finset.Subset.antisymm hBs h1)
  have hdisj : Disjoint (fam r C A U) (fam r C B (U ∪ A)) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [fam, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2.2 (h1.1.trans Finset.subset_union_right)
  have hsum := Finset.sum_le_sum_of_subset (f := wt r C) hsub
  rw [Finset.sum_insert hnot, Finset.sum_union hdisj] at hsum
  have h1 := hA U
  have h2 := hB (U ∪ A)
  have hG := G_split (A \ U).card (B \ (U ∪ A)).card
  rw [← hcard] at hG
  have hw : wt r C p0 = 2 * 2 ^ S.card := by simp only [wt, hpr, h0]
  have hpow : 2 ^ (S \ U).card ≤ 2 ^ S.card :=
    Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card Finset.sdiff_subset)
  omega

theorem claim_bought (S : Finset (Fin (2 * r))) (p0 : Fin C.gates.length)
    (h0 : supp r C (2 * r + p0.val) = S) (hop : ¬ (C.gates.get p0).op = GateOp.or)
    (hx : ∃ x, S ⊆ names r x) : Claim r C S := by
  intro U
  by_cases hSU : S ⊆ U
  · simp [Finset.sdiff_eq_empty_iff_subset.mpr hSU, G_zero]
  have hmem : p0 ∈ fam r C S U := by simp [fam, h0, hSU]
  have hle : wt r C p0 ≤ ∑ p ∈ fam r C S U, wt r C p :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  have hpr : price r C p0 = if S.card = 2 then 2 else if 3 ≤ S.card then 3 else 0 := by
    simp only [price, h0]
    rw [if_neg hop, if_pos hx]
  have hm : (S \ U).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
  have key : 2 * G (S \ U).card ≤ wt r C p0 := by
    rw [wt, hpr, h0]
    rcases Nat.lt_or_ge S.card 2 with h | h
    · have : (S \ U).card ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h' | h' <;> rw [h'] <;>
        simp [G_zero, G_one]
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [if_pos h.symm, ← h]
      have h2 := G_two
      have : (S \ U).card ≤ 2 := by omega
      interval_cases hc : (S \ U).card <;> simp [G_zero, G_one] <;> omega
    · rw [if_neg (by omega), if_pos (by omega)]
      have := G_le (S \ U).card
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm
      nlinarith
  omega

theorem claim_all (hC : ∀ g ∈ C.gates, g.op = GateOp.or → g.inputs.length ≤ 2) :
    ∀ w, (∃ x, supp r C w ⊆ names r x) → Claim r C (supp r C w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hx
  by_cases hw1 : w < 2 * r
  · exact claim_small r C _ (supp_input r C w hw1)
  by_cases hw2 : w < 2 * r + C.gates.length
  swap
  · rw [supp_out r C w (by omega)]; exact claim_small r C _ (by simp)
  obtain ⟨p, rfl⟩ : ∃ p, w = 2 * r + p := ⟨w - 2 * r, by omega⟩
  have hp : p < C.gates.length := by omega
  by_cases hop : (C.gates[p]).op = GateOp.or
  · have hlen := hC _ (List.getElem_mem hp) hop
    have hS : ∀ i, i ∈ supp r C (2 * r + p) ↔
        ∃ c ∈ (C.gates[p]).inputs, c < 2 * r + p ∧ i ∈ supp r C c := by
      intro i
      rw [supp_mem_gate r C p hp i, hop]
      simp [GateOp.eval, List.any_map]
    let eff : ℕ → Finset (Fin (2 * r)) := fun c => if c < 2 * r + p then supp r C c else ∅
    have heff : ∀ c ∈ (C.gates[p]).inputs, Claim r C (eff c) ∧ eff c ⊆ supp r C (2 * r + p) := by
      intro c hc
      by_cases hcw : c < 2 * r + p
      · have hsub : supp r C c ⊆ supp r C (2 * r + p) := by
          intro i hi; rw [hS]; exact ⟨c, hc, hcw, hi⟩
        obtain ⟨x, hx⟩ := hx
        simp only [eff, if_pos hcw]
        exact ⟨ih c hcw ⟨x, hsub.trans hx⟩, hsub⟩
      · simp only [eff, if_neg hcw]
        exact ⟨claim_small r C _ (by simp), Finset.empty_subset _⟩
    have heq : ∀ i, i ∈ supp r C (2 * r + p) ↔ ∃ c ∈ (C.gates[p]).inputs, i ∈ eff c := by
      intro i
      rw [hS]
      constructor
      · rintro ⟨c, hc, hcw, hi⟩; exact ⟨c, hc, by simp [eff, hcw, hi]⟩
      · rintro ⟨c, hc, hi⟩
        by_cases hcw : c < 2 * r + p
        · simp [eff, hcw] at hi; exact ⟨c, hc, hcw, hi⟩
        · simp [eff, hcw] at hi
    have hpr : price r C ⟨p, hp⟩ = 2 := by
      simp only [price]
      rw [if_pos (by simpa using hop)]
    rcases hin : (C.gates[p]).inputs with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, l⟩⟩⟩
    · have : supp r C (2 * r + p) = ∅ := by
        ext i; rw [heq, hin]; simp
      rw [this]; exact claim_small r C _ (by simp)
    · have : supp r C (2 * r + p) = eff c1 := by
        ext i; rw [heq, hin]; simp
      rw [this]; exact (heff c1 (by simp [hin])).1
    · have : eff c1 ∪ eff c2 = supp r C (2 * r + p) := by
        ext i; rw [heq, hin]; simp
      exact claim_union r C _ _ _ (heff c1 (by simp [hin])).1 (heff c2 (by simp [hin])).1 this
        ⟨p, hp⟩ rfl hpr
    · rw [hin] at hlen; simp at hlen
  · exact claim_bought r C _ ⟨p, hp⟩ rfl (by simpa using hop) hx

end lower

theorem card_names (r : ℕ) (x : Fin (2 ^ r)) : (names r x).card = r := by
  have : (names r x).card = (Finset.univ : Finset (Fin r)).card := by
    apply Finset.card_bij (fun i _ => (⟨i.val / 2, by omega⟩ : Fin r))
    · intros; simp
    · intro i hi j hj hij
      simp only [names, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      simp only [Fin.mk.injEq] at hij
      rw [hij, hj] at hi
      apply Fin.ext
      by_cases h1 : i.val % 2 = 1 <;> by_cases h2 : j.val % 2 = 1 <;> simp [h1, h2] at hi <;> omega
    · intro k _
      refine ⟨⟨2 * k.val + (if Nat.testBit x.val k then 1 else 0), ?_⟩, ?_, ?_⟩
      · have := k.isLt; split_ifs <;> omega
      · simp only [names, Finset.mem_filter, Finset.mem_univ, true_and]
        have e : (2 * k.val + (if Nat.testBit x.val k then 1 else 0)) / 2 = k.val := by
          split_ifs <;> omega
        rw [e]
        split_ifs with hb <;> simp [hb] <;> omega
      · apply Fin.ext; simp only; split_ifs <;> omega
  simpa using this

theorem count (r : ℕ) (T : Finset (Fin (2 * r))) :
    (Finset.univ.filter (fun x : Fin (2 ^ r) => T ⊆ names r x)).card * 2 ^ T.card ≤ 2 ^ r := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    set X := Finset.univ.filter (fun x : Fin (2 ^ r) => T ⊆ names r x) with hX
    set X' := Finset.univ.filter (fun x : Fin (2 ^ r) => insert i T ⊆ names r x) with hX'
    have hk : i.val / 2 < r := by omega
    let fl : Fin (2 ^ r) → Fin (2 ^ r) := fun x =>
      ⟨x.val ^^^ 2 ^ (i.val / 2), Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by norm_num) hk)⟩
    have hbit : ∀ x : Fin (2 ^ r), ∀ j, Nat.testBit (fl x).val j =
        (Nat.testBit x.val j ^^ decide (i.val / 2 = j)) := by
      intro x j; simp [fl, Nat.testBit_xor, Nat.testBit_two_pow]
    have hinj : Function.Injective fl := by
      intro x y h
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro j
      have h1 := hbit x j
      have h2 := hbit y j
      rw [h] at h1
      rw [h1] at h2
      revert h2
      cases Nat.testBit x.val j <;> cases Nat.testBit y.val j <;> cases decide (i.val / 2 = j) <;>
        simp
    have hmemn : ∀ (x : Fin (2 ^ r)) (t : Fin (2 * r)), t ∈ names r x ↔
        Nat.testBit x.val (t.val / 2) = decide (t.val % 2 = 1) := by
      intro x t; simp [names]
    have hsub : X' ⊆ X := by
      intro x hx
      simp only [hX', hX, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (Finset.subset_insert _ _).trans hx
    have himg : X'.image fl ⊆ X := by
      intro z hz
      simp only [Finset.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      simp only [hX', Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff]
        at hx
      simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and]
      intro t ht
      rw [hmemn, hbit]
      have htx := (hmemn x t).mp (hx.2 ht)
      have hix := (hmemn x i).mp hx.1
      by_cases hti : i.val / 2 = t.val / 2
      · exfalso
        rw [hti, htx] at hix
        have : t = i := by
          apply Fin.ext
          by_cases h1 : t.val % 2 = 1 <;> by_cases h2 : i.val % 2 = 1 <;> simp [h1, h2] at hix <;>
            omega
        exact hi (this ▸ ht)
      · simp [hti, htx]
    have hdisj : Disjoint X' (X'.image fl) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      simp only [Finset.mem_image] at hz'
      obtain ⟨x, hx, rfl⟩ := hz'
      simp only [hX', Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff]
        at hx hz
      have h1 := (hmemn _ i).mp hz.1
      have h2 := (hmemn x i).mp hx.1
      rw [hbit, h2] at h1
      simp at h1
    have hcard : X'.card + X'.card ≤ X.card := by
      have := Finset.card_le_card (Finset.union_subset hsub himg)
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj] at this
      exact this
    rw [Finset.card_insert_of_notMem hi, pow_succ]
    calc X'.card * (2 ^ T.card * 2) = (X'.card + X'.card) * 2 ^ T.card := by ring
      _ ≤ X.card * 2 ^ T.card := Nat.mul_le_mul_right _ hcard
      _ ≤ 2 ^ r := ih

theorem lower (r : ℕ) (C : Circuit) (hreal : ∀ x : Fin (2 ^ r), ∃ w, supp r C w = names r x)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.or → g.inputs.length ≤ 2) :
    2 * G r ≤ ∑ p, price r C p := by
  have hx : ∀ x : Fin (2 ^ r), 2 * G r ≤
      ∑ p, if supp r C (2 * r + p.val) ⊆ names r x then wt r C p else 0 := by
    intro x
    obtain ⟨w, hw⟩ := hreal x
    have hcl := claim_all r C hC w ⟨x, hw ▸ Finset.Subset.refl _⟩
    rw [hw] at hcl
    have h := hcl ∅
    rw [Finset.sdiff_empty, card_names] at h
    rw [← Finset.sum_filter]
    refine h.trans (Finset.sum_le_sum_of_subset ?_)
    intro p hp
    simp only [fam, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin (2 ^ r)))) => hx x)
  rw [Finset.sum_comm] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hp : ∀ p : Fin C.gates.length,
      (∑ x : Fin (2 ^ r), if supp r C (2 * r + p.val) ⊆ names r x then wt r C p else 0) ≤
        2 ^ r * price r C p := by
    intro p
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, wt]
    have := count r (supp r C (2 * r + p.val))
    calc _ = price r C p * ((Finset.univ.filter fun x : Fin (2 ^ r) =>
            supp r C (2 * r + p.val) ⊆ names r x).card * 2 ^ (supp r C (2 * r + p.val)).card) := by
          ring
      _ ≤ price r C p * 2 ^ r := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have h2 := hsum.trans (Finset.sum_le_sum (fun p _ => hp p))
  rw [← Finset.mul_sum] at h2
  exact Nat.le_of_mul_le_mul_left h2 (by positivity)

abbrev Pd (lo n y i : ℕ) : Prop :=
  lo ≤ i / 2 ∧ i / 2 < lo + n ∧ Nat.testBit y (i / 2 - lo) = decide (i % 2 = 1)

theorem Pd_split (lo a b y i : ℕ) :
    Pd lo (a + b) y i ↔ Pd lo a (y % 2 ^ a) i ∨ Pd (lo + a) b (y / 2 ^ a) i := by
  unfold Pd
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases h : i / 2 - lo < a
    · left; exact ⟨h1, by omega, by simp [h, h3]⟩
    · right
      refine ⟨by omega, by omega, ?_⟩
      rw [show i / 2 - (lo + a) + a = i / 2 - lo by omega]; exact h3
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · refine ⟨h1, by omega, ?_⟩
      have hlt : i / 2 - lo < a := by omega
      simpa [hlt] using h3
    · refine ⟨by omega, by omega, ?_⟩
      rw [show i / 2 - (lo + a) + a = i / 2 - lo by omega] at h3; exact h3

theorem build (r : ℕ) : ∀ n, 1 ≤ n → ∀ lo off, lo + n ≤ r → 2 * r ≤ off →
    ∃ (gs : List Gate) (loc : ℕ → ℕ), gs.length = G n ∧
      (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      (∀ y, loc y < off + gs.length) ∧
      ∀ (i : ℕ) (init : List Bool), init.length = off →
        (∀ j < 2 * r, init.getD j false = decide (j = i)) → i < 2 * r →
        ∀ y < 2 ^ n, (gs.foldl step init).getD (loc y) false = decide (Pd lo n y i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn lo off hlo hoff
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    refine ⟨[], fun y => 2 * lo + y % 2, by simp [G_one], by simp, fun y => by
      simp; omega, ?_⟩
    intro i init hlen hinit hi y hy
    simp only [List.foldl_nil]
    rw [hinit _ (by omega)]
    unfold Pd
    interval_cases y
    · simp only [Nat.zero_mod, add_zero, Nat.zero_testBit]
      rw [decide_eq_decide]
      constructor
      · intro h; subst h; refine ⟨by omega, by omega, ?_⟩; simp
      · rintro ⟨h1, h2, h3⟩
        have : ¬ i % 2 = 1 := by simpa using h3.symm
        omega
    · rw [decide_eq_decide]
      constructor
      · intro h; subst h
        refine ⟨by omega, by omega, ?_⟩
        rw [show (2 * lo + 1 % 2) / 2 - lo = 0 by omega]; simp
      · rintro ⟨h1, h2, h3⟩
        rw [show i / 2 - lo = 0 by omega] at h3
        have : i % 2 = 1 := by simpa using h3.symm
        omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨a, ha⟩ := G_exists m
  have haL := a.isLt
  obtain ⟨gs1, loc1, hl1, hor1, hloc1, hsem1⟩ :=
    ih (a.val + 1) (by omega) (by omega) lo off (by omega) hoff
  obtain ⟨gs2, loc2, hl2, hor2, hloc2, hsem2⟩ :=
    ih (m + 1 - a.val) (by omega) (by omega) (lo + (a.val + 1)) (off + gs1.length) (by omega)
      (by omega)
  let gs3 : List Gate := (List.range (2 ^ (m + 2))).map (fun y =>
    (⟨GateOp.or, [loc1 (y % 2 ^ (a.val + 1)), loc2 (y / 2 ^ (a.val + 1))]⟩ : Gate))
  have hl3 : gs3.length = 2 ^ (m + 2) := by simp [gs3]
  refine ⟨gs1 ++ gs2 ++ gs3, fun y => off + gs1.length + gs2.length + y % 2 ^ (m + 2), ?_, ?_,
    ?_, ?_⟩
  · simp only [List.length_append, hl3, hl1, hl2, ha]; ring
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact hor1 g hg
    · exact hor2 g hg
    · simp only [gs3, List.mem_map] at hg
      obtain ⟨y, _, rfl⟩ := hg
      simp
  · intro y
    have := Nat.mod_lt y (show 2 ^ (m + 2) > 0 by positivity)
    simp only [List.length_append, hl3]
    omega
  · intro i init hlen hinit hi y hy
    set W1 := gs1.foldl step init with hW1
    set W2 := gs2.foldl step W1 with hW2
    have hW1len : W1.length = off + gs1.length := by rw [hW1, foldl_length, hlen]
    have hW2len : W2.length = off + gs1.length + gs2.length := by rw [hW2, foldl_length, hW1len]
    have hinit1 : ∀ j < 2 * r, W1.getD j false = decide (j = i) := by
      intro j hj
      rw [hW1, getD_prefix _ _ _ (by omega), hinit j hj]
    have hfold : (gs1 ++ gs2 ++ gs3).foldl step init = gs3.foldl step W2 := by
      rw [List.foldl_append, List.foldl_append]
    have hmap := foldl_map_eval gs3 W2 (by
      intro g hg c hc
      simp only [gs3, List.mem_map] at hg
      obtain ⟨z, _, rfl⟩ := hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have := hloc1 (z % 2 ^ (a.val + 1)); omega
      · have := hloc2 (z / 2 ^ (a.val + 1)); omega)
    simp only []
    rw [hfold, hmap, Nat.mod_eq_of_lt hy, show off + gs1.length + gs2.length + y = W2.length + y by
      omega, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simp [hl3]; exact hy)]
    simp only [gs3, List.getElem_map, List.getElem_range, GateOp.eval, List.map_cons,
      List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
    have hy1 : y % 2 ^ (a.val + 1) < 2 ^ (a.val + 1) := Nat.mod_lt _ (by positivity)
    have hy2 : y / 2 ^ (a.val + 1) < 2 ^ (m + 1 - a.val) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      rw [show m + 1 - a.val + (a.val + 1) = m + 2 by omega]; exact hy
    have e1 : W2.getD (loc1 (y % 2 ^ (a.val + 1))) false =
        decide (Pd lo (a.val + 1) (y % 2 ^ (a.val + 1)) i) := by
      rw [hW2, getD_prefix _ _ _ (by have := hloc1 (y % 2 ^ (a.val + 1)); omega)]
      exact hsem1 i init hlen hinit hi _ hy1
    have e2 : W2.getD (loc2 (y / 2 ^ (a.val + 1))) false =
        decide (Pd (lo + (a.val + 1)) (m + 1 - a.val) (y / 2 ^ (a.val + 1)) i) :=
      hsem2 i W1 hW1len hinit1 hi _ hy2
    rw [e1, e2]
    have hsp := Pd_split lo (a.val + 1) (m + 1 - a.val) y i
    rw [show a.val + 1 + (m + 1 - a.val) = m + 2 by omega] at hsp
    rw [← Bool.decide_or, decide_eq_decide]
    exact hsp.symm

theorem main (r : ℕ) (hr : 1 ≤ r) (C : Circuit)
    (hreal : ∀ x : Fin (2 ^ r), ∃ w, supp r C w = names r x)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.or → g.inputs.length ≤ 2) :
    ∃ D : Circuit, (∀ x : Fin (2 ^ r), ∃ w, supp r D w = names r x) ∧
      (∀ g ∈ D.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      2 * D.size ≤ ∑ p, price r C p := by
  obtain ⟨gs, loc, hlen, hor, -, hsem⟩ := build r r hr 0 (2 * r) (by omega) le_rfl
  refine ⟨⟨gs, 0⟩, ?_, hor, ?_⟩
  · intro x
    refine ⟨loc x.val, ?_⟩
    ext i
    rw [mem_supp]
    have := hsem i.val (List.ofFn (fun h : Fin (2 * r) => decide (h = i))) (by simp)
      (fun j hj => getD_ofFn_input r i j hj) i.isLt x.val x.isLt
    rw [this]
    simp only [names, Finset.mem_filter, Finset.mem_univ, true_and, Pd, decide_eq_true_eq,
      Nat.sub_zero, zero_le, zero_add, true_and]
    have := i.isLt
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by omega, h⟩
  · have := lower r C hreal hC
    simp only [Circuit.size, hlen]
    exact this

end PEqualNP.Outside.L_lib_738_aux

theorem PEqualNP.Outside.L_lib_738 : (∀ r : ℕ, 1 ≤ r →
  let I := Fin (2 * r)
  let names := fun (x : Fin (2 ^ r)) =>
    Finset.univ.filter (fun i : I => Nat.testBit x.val (i.val / 2) = decide (i.val % 2 = 1))
  let supp := fun (E : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ) =>
    Finset.univ.filter (fun i : I =>
      (E.wires (List.ofFn (fun h : I => decide (h = i)))).getD w false = true)
  let realizes := fun (E : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∀ x : Fin (2 ^ r), ∃ w : ℕ, supp E w = names x
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, realizes C →
    (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or → g.inputs.length ≤ 2) →
    let price := fun (p : Fin C.gates.length) =>
      let S := supp C (2 * r + p.val)
      @ite ℕ ((C.gates.get p).op = PEqualNP.CircuitLowerBounds.GateOp.or)
        (Classical.propDecidable _) 2 (if (∃ x, S ⊆ names x) then
        (if S.card = 2 then 2 else if 3 ≤ S.card then 3 else 0)
      else 0)
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, realizes D ∧
      (∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧
      2 * D.size ≤ ∑ p, price p) := by
  intro r hr I names supp realizes C hreal hC price
  exact PEqualNP.Outside.L_lib_738_aux.main r hr C hreal hC
