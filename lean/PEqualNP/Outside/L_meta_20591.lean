import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20591

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj


def Rd (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  n ≤ a ∧ a - n < C.gates.length ∧ b ∈ (gateAt C (a - n)).inputs ∧ b < a

def Cone (n : ℕ) (C : Circuit) (w : ℕ) : Prop := Relation.ReflTransGen (Rd n C) C.output w

lemma cone_step {n : ℕ} {C : Circuit} {j i : ℕ} (hj : j < C.gates.length)
    (hw : Cone n C (n + j)) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j) : Cone n C i := by
  refine Relation.ReflTransGen.tail hw ?_
  refine ⟨by omega, ?_, ?_, hlt⟩
  · rw [Nat.add_sub_cancel_left]; exact hj
  · rw [Nat.add_sub_cancel_left]; exact hi

lemma local_eq {n : ℕ} {C : Circuit} {x y : List Bool} (hx : x.length = n) (hy : y.length = n)
    (hagree : ∀ i, i < n → Cone n C i → x.getD i false = y.getD i false) :
    ∀ w, Cone n C w → val C x w = val C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_input hx h1, val_input hy h1]; exact hagree w h1 hw
    · by_cases h2 : n + C.gates.length ≤ w
      · rw [val_ge hx h2, val_ge hy h2]
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [val_gate hx hj, val_gate hy hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + j
        · rw [if_pos hlt, if_pos hlt]
          exact ih i hlt (cone_step hj hw hi hlt)
        · rw [if_neg hlt, if_neg hlt]

lemma mono_val {n : ℕ} {C : Circuit} (hM : Monotone2 C) {x y : List Bool}
    (hx : x.length = n) (hy : y.length = n)
    (hle : ∀ i, i < n → x.getD i false = true → y.getD i false = true) :
    ∀ w, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_input hx h1] at hw; rw [val_input hy h1]; exact hle w h1 hw
    · by_cases h2 : n + C.gates.length ≤ w
      · rw [val_ge hx h2] at hw; exact absurd hw (by simp)
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [val_gate hx hj] at hw
        rw [val_gate hy hj]
        have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq hj]; exact List.getElem_mem hj
        have hop := (hM _ hg).1
        have hstep : ∀ i ∈ (gateAt C j).inputs,
            (if i < n + j then val C x i else false) = true →
            (if i < n + j then val C y i else false) = true := by
          intro i _ hi
          by_cases hlt : i < n + j
          · rw [if_pos hlt] at hi ⊢; exact ih i hlt hi
          · rw [if_neg hlt] at hi; exact absurd hi (by simp)
        rcases hop with h | h
        · rw [h] at hw ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hw ⊢
          rintro b ⟨i, hi, rfl⟩
          exact hstep i hi (hw _ ⟨i, hi, rfl⟩)
        · have h' : (gateAt C j).op = GateOp.or := h
          rw [h'] at hw ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hw ⊢
          obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hw
          exact ⟨_, ⟨i, hi, rfl⟩, hstep i hi hb⟩

lemma count_bound {n : ℕ} {C : Circuit} (hM : Monotone2 C)
    (ho : n ≤ C.output ∧ C.output - n < C.gates.length)
    (E : Finset ℕ) (hE : ∀ e ∈ E, e < n ∧ Cone n C e) : E.card ≤ C.gates.length + 1 := by
  classical
  let G : Finset ℕ := (Finset.range C.gates.length).filter (fun k => Cone n C (n + k))
  have hk0 : C.output - n ∈ G := by
    simp only [G, Finset.mem_filter, Finset.mem_range]
    refine ⟨ho.2, ?_⟩
    have : n + (C.output - n) = C.output := by omega
    rw [this]; exact Relation.ReflTransGen.refl
  let T : Finset ℕ := E ∪ ((G.erase (C.output - n)).image (fun k => n + k))
  have hsub : T ⊆ G.biUnion (fun k => (gateAt C k).inputs.toFinset) := by
    intro t ht
    have hcone : Cone n C t ∧ t ≠ C.output := by
      rcases Finset.mem_union.mp ht with h | h
      · obtain ⟨h1, h2⟩ := hE t h
        exact ⟨h2, by omega⟩
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨hk1, hk2⟩ := Finset.mem_erase.mp hk
        simp only [G, Finset.mem_filter, Finset.mem_range] at hk2
        refine ⟨hk2.2, ?_⟩
        intro h
        apply hk1
        omega
    obtain ⟨hc, hne⟩ := hcone
    rcases Relation.ReflTransGen.cases_tail hc with h | ⟨b, hb, hbt⟩
    · exact absurd h hne
    · obtain ⟨hb1, hb2, hb3, hb4⟩ := hbt
      refine Finset.mem_biUnion.mpr ⟨b - n, ?_, ?_⟩
      · simp only [G, Finset.mem_filter, Finset.mem_range]
        refine ⟨hb2, ?_⟩
        have : n + (b - n) = b := by omega
        rw [this]; exact hb
      · exact List.mem_toFinset.mpr hb3
  have hcard1 : T.card ≤ ∑ k ∈ G, ((gateAt C k).inputs.toFinset).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcard2 : ∀ k ∈ G, ((gateAt C k).inputs.toFinset).card ≤ 2 := by
    intro k hk
    simp only [G, Finset.mem_filter, Finset.mem_range] at hk
    have hg : gateAt C k ∈ C.gates := by rw [gateAt_eq hk.1]; exact List.getElem_mem hk.1
    exact (List.toFinset_card_le _).trans (hM _ hg).2
  have hcard3 : T.card ≤ 2 * G.card := by
    refine hcard1.trans ?_
    calc ∑ k ∈ G, ((gateAt C k).inputs.toFinset).card ≤ ∑ k ∈ G, 2 := Finset.sum_le_sum hcard2
      _ = 2 * G.card := by simp [mul_comm]
  have hdisj : Disjoint E ((G.erase (C.output - n)).image (fun k => n + k)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht'
    have := (hE _ ht).1
    omega
  have hinj : Function.Injective (fun k : ℕ => n + k) := fun a b h => by simpa using h
  have hcardT : T.card = E.card + (G.card - 1) := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
      Finset.card_erase_of_mem hk0]
  have hGs : G.card ≤ C.gates.length := by
    calc G.card ≤ (Finset.range C.gates.length).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = C.gates.length := Finset.card_range _
  have hG1 : 1 ≤ G.card := Finset.card_pos.mpr ⟨_, hk0⟩
  omega

lemma key {n : ℕ} {C : Circuit} (hM : Monotone2 C) {E F : List Bool}
    (hE : E.length = n) (hF : F.length = n) {i : ℕ} (hi : i < n) (hnot : ¬ Cone n C i)
    (hle : ∀ w, w < n → w ≠ i → E.getD w false = true → F.getD w false = true)
    (htrue : C.eval E = true) : C.eval F = true := by
  have hE1len : (E.set i (F.getD i false)).length = n := by simp [hE]
  have hget : ∀ w, w < n → w ≠ i → (E.set i (F.getD i false)).getD w false = E.getD w false := by
    intro w hw hwi
    simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm hwi]
  have hgeti : (E.set i (F.getD i false)).getD i false = F.getD i false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_set, hE ▸ hi]
  have h1 : val C (E.set i (F.getD i false)) C.output = val C E C.output := by
    refine local_eq hE1len hE ?_ C.output Relation.ReflTransGen.refl
    intro w hw hc
    have hwi : w ≠ i := fun h => hnot (h ▸ hc)
    exact hget w hw hwi
  have h2 : val C F C.output = true := by
    refine mono_val hM hE1len hF ?_ C.output (by rw [h1]; exact htrue)
    intro w hw hw1
    by_cases hwi : w = i
    · subst hwi; rw [hgeti] at hw1; exact hw1
    · rw [hget w hw hwi] at hw1; exact hle w hw hwi hw1
  exact h2


def A : Fin 5 → Fin 5 → Bool := fun u v => (32607232 : ℕ).testBit (5 * u.val + v.val)

lemma hlen (u v : Fin 5) : (PEqualNP.Represents.oneEach u v : List Bool).length = 10 := by
  simp [PEqualNP.Represents.oneEach]

lemma ess {C : Circuit} (hM : Monotone2 C) (hr : PEqualNP.Represents.Represents A C)
    (i : ℕ) (hi : i < 10) (u v u' v' : Fin 5) (h1 : A u v = true) (h2 : A u' v' = false)
    (hle : ∀ w, w < 10 → w ≠ i → (PEqualNP.Represents.oneEach u v : List Bool).getD w false = true →
      (PEqualNP.Represents.oneEach u' v' : List Bool).getD w false = true) : Cone 10 C i := by
  by_contra hnot
  have := key hM (hlen u v) (hlen u' v') hi hnot hle (by rw [hr u v]; exact h1)
  rw [hr u' v', h2] at this
  exact absurd this (by simp)

lemma cone_eq {n : ℕ} {C : Circuit} (ho : ¬ (n ≤ C.output ∧ C.output - n < C.gates.length))
    {t : ℕ} (h : Cone n C t) : t = C.output := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
  · exact h.symm
  · exact absurd ⟨hc.1, hc.2.1⟩ ho

lemma lower (C : Circuit) (hM : Monotone2 C) (hs : C.size ≤ 3)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  have e2 := ess hM hr 2 (by norm_num) 2 0 0 0 (by decide) (by decide) (by decide)
  have e3 := ess hM hr 3 (by norm_num) 3 0 0 0 (by decide) (by decide) (by decide)
  have e4 := ess hM hr 4 (by norm_num) 4 0 0 0 (by decide) (by decide) (by decide)
  have e5 := ess hM hr 5 (by norm_num) 2 0 2 2 (by decide) (by decide) (by decide)
  have e6 := ess hM hr 6 (by norm_num) 2 1 2 2 (by decide) (by decide) (by decide)
  by_cases ho : 10 ≤ C.output ∧ C.output - 10 < C.gates.length
  · have h := count_bound hM ho {2, 3, 4, 5, 6} (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      · exact ⟨by norm_num, e2⟩
      · exact ⟨by norm_num, e3⟩
      · exact ⟨by norm_num, e4⟩
      · exact ⟨by norm_num, e5⟩
      · exact ⟨by norm_num, e6⟩)
    simp only [Circuit.size] at hs
    have hc : ({2, 3, 4, 5, 6} : Finset ℕ).card = 5 := by decide
    omega
  · have a := cone_eq ho e2
    have b := cone_eq ho e3
    omega

def C4 : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [4, 12]⟩], 13⟩

lemma C4_mono : Monotone2 C4 := by
  intro g hg
  simp only [C4, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

lemma C4_rep : PEqualNP.Represents.Represents A C4 := by
  unfold PEqualNP.Represents.Represents
  decide

lemma C4_size : C4.size ≤ 4 := by decide

end PEqualNP.Outside.L_meta_20591

theorem PEqualNP.Outside.L_meta_20591 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32607232 : ℕ).testBit (5 * u.val + v.val)) 4 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32607232 : ℕ).testBit (5 * u.val + v.val)) 3 := by
  refine ⟨⟨PEqualNP.Outside.L_meta_20591.C4, PEqualNP.Outside.L_meta_20591.C4_mono,
    PEqualNP.Outside.L_meta_20591.C4_size, PEqualNP.Outside.L_meta_20591.C4_rep⟩, ?_⟩
  rintro ⟨C, hM, hs, hr⟩
  exact PEqualNP.Outside.L_meta_20591.lower C hM hs hr
