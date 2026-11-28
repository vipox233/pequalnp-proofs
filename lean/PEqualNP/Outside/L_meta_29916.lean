import PEqualNP.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Union


namespace PEqualNP.Outside.L_meta_29916.InternalMask

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_prefix (gs : List Gate) (w : List Bool) (k : Nat) (hk : k < w.length) :
    (run gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD k false = w.getD k false
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hk

lemma append_agree (w v : List Bool) (b : Bool) (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false) :
    ∀ k, k ≠ 0 → (w ++ [b]).getD k false = (v ++ [b]).getD k false := by
  intro k hk
  by_cases hkw : k < w.length
  · rw [List.getD_append _ _ _ _ hkw,
      List.getD_append _ _ _ _ (by omega)]
    exact heq k hk
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

lemma or_true (w : List Bool) (g : Gate) (j : Nat)
    (hop : g.op = GateOp.or) (hmem : j ∈ g.inputs) (hj : w.getD j false = true) :
    g.op.eval (g.inputs.map fun k => w.getD k false) = true := by
  rw [hop]
  change (g.inputs.map fun k => w.getD k false).any id = true
  apply List.any_eq_true.mpr
  exact ⟨true, List.mem_map.mpr ⟨j, hmem, hj⟩, rfl⟩

lemma run_masked_agree (gs : List Gate) (w v : List Bool) (j : Nat)
    (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false)
    (hjw : (run gs w).getD j false = true)
    (hjv : (run gs v).getD j false = true)
    (hgood : ∀ k : Fin gs.length, 0 ∈ (gs.get k).inputs →
      (gs.get k).op = GateOp.or ∧ j ∈ (gs.get k).inputs ∧ j < w.length + k.val) :
    ∀ k, k ≠ 0 → (run gs w).getD k false = (run gs v).getD k false := by
  induction gs generalizing w v with
  | nil => exact heq
  | cons g gs ih =>
    have hval : g.op.eval (g.inputs.map fun k => w.getD k false) =
        g.op.eval (g.inputs.map fun k => v.getD k false) := by
      by_cases h0 : 0 ∈ g.inputs
      · have hg := hgood ⟨0, by simp⟩ h0
        simp only [List.get_eq_getElem, List.getElem_cons_zero, Nat.add_zero] at hg
        obtain ⟨hop, hmem, hjl⟩ := hg
        have hw : w.getD j false = true := by
          rw [← run_prefix (g :: gs) w j hjl]
          exact hjw
        have hv : v.getD j false = true := by
          rw [← run_prefix (g :: gs) v j (by omega)]
          exact hjv
        rw [or_true w g j hop hmem hw, or_true v g j hop hmem hv]
      · congr 1
        apply List.map_congr_left
        intro k hk
        apply heq k
        intro hz
        subst k
        exact h0 hk
    have hext : ∀ k, k ≠ 0 → (step w g).getD k false = (step v g).getD k false := by
      unfold step
      rw [hval]
      exact append_agree w v _ hlen heq
    change ∀ k, k ≠ 0 → (run gs (step w g)).getD k false =
      (run gs (step v g)).getD k false
    apply ih (step w g) (step v g)
    · simp [step, hlen]
    · exact hext
    · exact hjw
    · exact hjv
    · intro k hk
      have h := hgood k.succ hk
      simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] at h
      obtain ⟨hop, hmem, hlt⟩ := h
      refine ⟨hop, hmem, ?_⟩
      simp only [step, List.length_append, List.length_singleton]
      omega

lemma run_unread_prefix (gs : List Gate) (w v : List Bool) (j : Nat)
    (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false)
    (hj : j ≠ 0)
    (hbefore : ∀ k : Fin gs.length, 0 ∈ (gs.get k).inputs → j < w.length + k.val) :
    (run gs w).getD j false = (run gs v).getD j false := by
  induction gs generalizing w v with
  | nil => exact heq j hj
  | cons g gs ih =>
    by_cases hjl : j < w.length
    · rw [run_prefix (g :: gs) w j hjl,
        run_prefix (g :: gs) v j (by omega)]
      exact heq j hj
    · have h0 : 0 ∉ g.inputs := by
        intro hmem
        have h := hbefore ⟨0, by simp⟩ hmem
        simp only [Nat.add_zero] at h
        omega
      have hval : g.op.eval (g.inputs.map fun k => w.getD k false) =
          g.op.eval (g.inputs.map fun k => v.getD k false) := by
        congr 1
        apply List.map_congr_left
        intro k hk
        apply heq k
        intro hz
        subst k
        exact h0 hk
      have hext : ∀ k, k ≠ 0 → (step w g).getD k false = (step v g).getD k false := by
        unfold step
        rw [hval]
        exact append_agree w v _ hlen heq
      change (run gs (step w g)).getD j false = (run gs (step v g)).getD j false
      apply ih (step w g) (step v g)
      · simp [step, hlen]
      · exact hext
      · intro k hk
        have h := hbefore k.succ hk
        simp only [Fin.val_succ] at h
        simp only [step, List.length_append, List.length_singleton]
        omega

theorem circuit_collision (C : Circuit) (i : Fin C.gates.length)
    (j : Nat) (w v : List Bool)
    (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false)
    (hjw : (C.wires w).getD j false = true)
    (hjv : (C.wires v).getD j false = true)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or)
    (hmem : j ∈ (C.gates.get i).inputs)
    (hj : j < w.length + i.val) (hout : C.output ≠ 0) :
    C.eval w = C.eval v := by
  apply run_masked_agree C.gates w v j hlen heq hjw hjv ?_ C.output hout
  intro q hq
  have hi := hunique q hq
  subst q
  exact ⟨hop, hmem, hj⟩

theorem circuit_collision_of_one_true (C : Circuit) (i : Fin C.gates.length)
    (j : Nat) (w v : List Bool)
    (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false)
    (hjw : (C.wires w).getD j false = true)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or)
    (hmem : j ∈ (C.gates.get i).inputs)
    (hj : j < w.length + i.val) (hj0 : j ≠ 0) (hout : C.output ≠ 0) :
    C.eval w = C.eval v := by
  have hwire : (C.wires w).getD j false = (C.wires v).getD j false := by
    apply run_unread_prefix C.gates w v j hlen heq hj0
    intro q hq
    have hi := hunique q hq
    subst q
    exact hj
  have hjv : (C.wires v).getD j false = true := hwire.symm.trans hjw
  exact circuit_collision C i j w v hlen heq hjw hjv hunique hop hmem hj hout

end PEqualNP.Outside.L_meta_29916.InternalMask


namespace PEqualNP.Outside.L_meta_29916.SupportBound

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this


theorem getD_take_eq (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD w false =
      (wiresFrom (C.gates.take k) (List.ofFn x)).getD w false := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  conv_lhs => rw [← List.take_append_drop k C.gates]
  rw [wiresFrom_append]
  apply getD_wiresFrom
  rw [length_wiresFrom]
  simpa [List.length_take, Nat.min_eq_left hk] using hw

theorem wire_support (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ k + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) →
        (C.wires (List.ofFn x)).getD w false =
          (C.wires (List.ofFn y)).getD w false := by
  let S := (suppsFrom (C.gates.take k) (inputSupps n)).getD w ∅
  refine ⟨S, ?_, ?_⟩
  · have hc := cnt_suppsFrom (C.gates.take k) 0 (inputSupps n)
      (fun g hg => hfan g (List.mem_of_mem_take hg)) cnt_inputs {w}
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add,
      List.length_take, Nat.min_eq_left hk] using hc
  · intro x y heq
    rw [getD_take_eq C n k w hk hw x, getD_take_eq C n k w hk hw y]
    exact (agree_wiresFrom x y (C.gates.take k) _ _ _ (agree_inputs x y)).2.2 w heq

theorem wire_essential_bound (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (E : Finset (Fin n))
    (hsens : ∀ i ∈ E, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
        (C.wires (List.ofFn x)).getD w false ≠
          (C.wires (List.ofFn y)).getD w false) :
    E.card ≤ k + 1 := by
  obtain ⟨S, hcard, hdep⟩ := wire_support C n k w hk hw hfan
  apply le_trans (Finset.card_le_card (t := S) ?_) hcard
  intro i hi
  by_contra hni
  obtain ⟨x, y, hxy, hne⟩ := hsens i hi
  apply hne (hdep x y ?_)
  intro j hj
  apply hxy j
  intro hji
  subst j
  exact hni hj

theorem six_inputs_no_early_wire (C : Circuit) (w : Nat)
    (hk : 4 ≤ C.gates.length) (hw : w < 11)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hsens : ∀ i : Fin 7, i ≠ 0 → ∃ x y : Fin 7 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
        (C.wires (List.ofFn x)).getD w false ≠
          (C.wires (List.ofFn y)).getD w false) : False := by
  have h := wire_essential_bound C 7 4 w hk hw hfan
    (Finset.univ.erase 0) (fun i hi => hsens i (Finset.mem_erase.mp hi).1)
  have hc : (Finset.univ.erase (0 : Fin 7)).card = 6 := by decide
  rw [hc] at h
  omega

end PEqualNP.Outside.L_meta_29916.SupportBound


namespace PEqualNP.Outside.L_meta_29916.Gate8

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_29916.InternalMask

def cycle7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def bits (m : Nat) : Fin 7 → Bool := fun k => m.testBit k.val

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma output_nonzero (C : Circuit)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x) : C.output ≠ 0 := by
  intro hz
  have h := hc (bits 6)
  change (run C.gates (List.ofFn (bits 6))).getD C.output false = _ at h
  rw [hz, run_prefix C.gates (List.ofFn (bits 6)) 0 (by simp)] at h
  have hl : (List.ofFn (bits 6)).getD 0 false = false := by decide
  have hr : cycle7 (bits 6) = true := by decide
  rw [hl, hr] at h
  cases h

lemma two_tail (gs : List Gate) (h : gs.length = 10) :
    ∃ p : List Gate, ∃ a b : Gate, p.length = 8 ∧ gs = p ++ [a,b] := by
  have hd : (gs.drop 8).length = 2 := by simp [h]
  have hs : ∃ a b : Gate, gs.drop 8 = [a,b] := by
    generalize gs.drop 8 = ds at hd ⊢
    cases ds with
    | nil => simp at hd
    | cons a ds =>
      cases ds with
      | nil => simp at hd
      | cons b ds =>
        cases ds with
        | nil => exact ⟨a,b,rfl⟩
        | cons c ds => simp only [List.length_cons] at hd; omega
  obtain ⟨a,b,hab⟩ := hs
  exact ⟨gs.take 8,a,b,by simp [h],by rw [← hab, List.take_append_drop]⟩

lemma ofFn_agree_zero (x y : Fin 7 → Bool)
    (h : ∀ k : Fin 7, k ≠ 0 → x k = y k) :
    ∀ k, k ≠ 0 → (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
  intro k hk
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with hlt
  · simp only [Option.getD_some]
    apply h
    intro hz
    have hzv := congrArg Fin.val hz
    simp only [Fin.val_zero] at hzv
    exact hk hzv
  · rfl

lemma pair64_agree : ∀ k : Fin 7, k ≠ 0 → bits 64 k = bits 65 k := by decide

lemma output_lower (C : Circuit) (i : Fin C.gates.length)
    (hi : i.val = 8)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i) :
    15 ≤ C.output := by
  by_contra h
  have he := run_unread_prefix C.gates (List.ofFn (bits 64)) (List.ofFn (bits 65))
    C.output (by simp) (ofFn_agree_zero _ _ pair64_agree) (output_nonzero C hc) ?_
  · change C.eval (List.ofFn (bits 64)) = C.eval (List.ofFn (bits 65)) at he
    rw [hc, hc] at he
    have hf : cycle7 (bits 64) = false := by decide
    have ht : cycle7 (bits 65) = true := by decide
    rw [hf,ht] at he
    cases he
  · intro q hq
    have hqi := hunique q hq
    subst q
    simp only [List.length_ofFn,hi]
    omega

lemma output_upper (C : Circuit) (hsize : C.size = 10)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x) :
    C.output < 17 := by
  by_contra h
  have he := hc (bits 3)
  have hl : (run C.gates (List.ofFn (bits 3))).length = 17 := by
    rw [run_length]
    simp only [List.length_ofFn]
    change 7 + C.size = 17
    omega
  change (run C.gates (List.ofFn (bits 3))).getD C.output false = _ at he
  rw [List.getD_eq_default _ _ (by omega)] at he
  have ht : cycle7 (bits 3) = true := by decide
  rw [ht] at he
  cases he

lemma get_eight (C : Circuit) (i : Fin C.gates.length) (hi : i.val = 8)
    (p : List Gate) (a b : Gate) (hp : p.length = 8) (hgs : C.gates = p ++ [a,b]) :
    C.gates.get i = a := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_eq_getD a,hi,hgs,List.getD_append_right _ _ _ _ (by omega)]
  simp [hp]

lemma output_not_eight (C : Circuit) (i : Fin C.gates.length)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hread : 0 ∈ (C.gates.get i).inputs)
    (hop : (C.gates.get i).op = GateOp.or) : C.output ≠ 15 := by
  obtain ⟨p,a,b,hp,hgs⟩ := two_tail C.gates hsize
  have hga := get_eight C i hi p a b hp hgs
  have hread' : 0 ∈ a.inputs := by rw [← hga]; exact hread
  have hop' : a.op = GateOp.or := by rw [← hga]; exact hop
  let w := run p (List.ofFn (bits 1))
  have hwlen : w.length = 15 := by simp [w,run_length,hp]
  have hw0 : w.getD 0 false = true := by
    rw [show w = run p (List.ofFn (bits 1)) from rfl, run_prefix p _ 0 (by simp)]
    decide
  have ha : a.op.eval (a.inputs.map fun k => w.getD k false) = true :=
    or_true w a 0 hop' hread' hw0
  intro hout
  have he := hc (bits 1)
  change (run C.gates (List.ofFn (bits 1))).getD C.output false = _ at he
  rw [hgs,hout] at he
  simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil] at he
  change (step (step w a) b).getD 15 false = _ at he
  have hslen : (step w a).length = 16 := by simp [step,hwlen]
  change (step w a ++ [_]).getD 15 false = _ at he
  rw [List.getD_append _ _ _ _ (by omega)] at he
  change (w ++ [_]).getD 15 false = _ at he
  rw [List.getD_append_right _ _ _ _ (by omega)] at he
  simp only [hwlen,Nat.sub_self,List.getD_cons_zero,ha] at he
  have hf : cycle7 (bits 1) = false := by decide
  rw [hf] at he
  cases he

lemma output_last (C : Circuit) (i : Fin C.gates.length)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hread : 0 ∈ (C.gates.get i).inputs)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or) : C.output = 16 := by
  have h₁ := output_lower C i hi hc hunique
  have h₂ := output_upper C hsize hc
  have h₃ := output_not_eight C i hi hsize hc hread hop
  omega

lemma inputs_pair (l : List Nat) (j : Nat) (hl : l.length ≤ 2)
    (h0 : 0 ∈ l) (hj : j ∈ l) (hne : j ≠ 0) :
    l = [0,j] ∨ l = [j,0] := by
  cases l with
  | nil => simp at h0
  | cons a l =>
    cases l with
    | nil =>
      simp only [List.mem_singleton] at h0 hj
      omega
    | cons b l =>
      cases l with
      | cons c l => simp only [List.length_cons] at hl; omega
      | nil =>
        simp at h0 hj
        rcases h0 with h0 | h0
        · subst a
          rcases hj with hj | hj
          · exact (hne hj).elim
          · subst b; exact Or.inl rfl
        · subst b
          rcases hj with hj | hj
          · subst a; exact Or.inr rfl
          · exact (hne hj).elim

lemma get_nine (C : Circuit) (k : Fin C.gates.length) (hk : k.val = 9)
    (p : List Gate) (a b : Gate) (hp : p.length = 8) (hgs : C.gates = p ++ [a,b]) :
    C.gates.get k = b := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_eq_getD b,hk,hgs,List.getD_append_right _ _ _ _ (by omega)]
  simp [hp]

lemma partner_true_on_positive (C : Circuit) (i k : Fin C.gates.length) (j : Nat)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hread : 0 ∈ (C.gates.get i).inputs)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or)
    (hkop : (C.gates.get k).op = GateOp.and) (hik : i.val < k.val)
    (hreadik : 7 + i.val ∈ (C.gates.get k).inputs)
    (hpartner : j ∈ (C.gates.get i).inputs) (hj0 : j ≠ 0) (hjl : j < 7+i.val)
    (x : Fin 7 → Bool) (hx0 : x 0 = false) (hxf : cycle7 x = true) :
    (C.wires (List.ofFn x)).getD j false = true := by
  have hk : k.val = 9 := by
    have hkb := k.isLt
    change k.val < C.size at hkb
    omega
  have hout := output_last C i hi hsize hc hread hunique hop
  obtain ⟨p,a,b,hp,hgs⟩ := two_tail C.gates hsize
  have hga := get_eight C i hi p a b hp hgs
  have hgb := get_nine C k hk p a b hp hgs
  have hread' : 0 ∈ a.inputs := by rw [← hga]; exact hread
  have hpartner' : j ∈ a.inputs := by rw [← hga]; exact hpartner
  have hop' : a.op = GateOp.or := by rw [← hga]; exact hop
  have hkop' : b.op = GateOp.and := by rw [← hgb]; exact hkop
  have hreadik' : 15 ∈ b.inputs := by rw [← hgb]; simpa [hi] using hreadik
  have hfan' : a.inputs.length ≤ 2 := by apply hfan; rw [hgs]; simp
  have hpair := inputs_pair a.inputs j hfan' hread' hpartner' hj0
  let w := run p (List.ofFn x)
  have hwlen : w.length = 15 := by simp [w,run_length,hp]
  have hslen : (step w a).length = 16 := by simp [step,hwlen]
  have hw0 : w.getD 0 false = false := by
    rw [show w = run p (List.ofFn x) from rfl,run_prefix p _ 0 (by simp)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn] using hx0
  have he := hc x
  rw [hxf] at he
  change (run C.gates (List.ofFn x)).getD C.output false = true at he
  rw [hgs,hout] at he
  simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil] at he
  change (step w a ++ [b.op.eval (b.inputs.map fun l => (step w a).getD l false)]).getD 16 false = true at he
  rw [List.getD_append_right _ _ _ _ (by omega)] at he
  simp only [hslen,Nat.sub_self,List.getD_cons_zero] at he
  rw [hkop'] at he
  change (b.inputs.map fun l => (step w a).getD l false).all id = true at he
  have he8 : (step w a).getD 15 false = true := by
    exact List.all_eq_true.mp he _ (List.mem_map.mpr ⟨15,hreadik',rfl⟩)
  change (w ++ [a.op.eval (a.inputs.map fun l => w.getD l false)]).getD 15 false = true at he8
  rw [List.getD_append_right _ _ _ _ (by omega)] at he8
  simp only [hwlen,Nat.sub_self,List.getD_cons_zero] at he8
  rw [hop'] at he8
  have hq : w.getD j false = true := by
    rcases hpair with ha | ha
    · rw [ha] at he8
      simpa only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
        id_eq,Bool.or_false,hw0,Bool.false_or] using he8
    · rw [ha] at he8
      simpa only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
        id_eq,Bool.or_false,hw0,Bool.false_or] using he8
  change (run C.gates (List.ofFn x)).getD j false = true
  rw [hgs]
  simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (run [a,b] w).getD j false = true
  rw [run_prefix [a,b] w j (by omega)]
  exact hq

def negative : Fin 7 → Nat := ![0,68,2,18,10,18,34]
def positive : Fin 7 → Nat := ![0,70,6,26,26,50,98]
def flipped : Fin 7 → Nat := ![0,69,3,19,11,19,35]

lemma witness_facts : ∀ r : Fin 7, r ≠ 0 →
    bits (negative r) 0 = false ∧ bits (positive r) 0 = false ∧
    cycle7 (bits (negative r)) = false ∧ cycle7 (bits (positive r)) = true ∧
    cycle7 (bits (flipped r)) = true ∧
    (∀ s : Fin 7, s ≠ 0 → bits (negative r) s = bits (flipped r) s) ∧
    (∀ s : Fin 7, s ≠ r → bits (negative r) s = bits (positive r) s) := by
  decide

theorem partner_sensitive (C : Circuit) (i k : Fin C.gates.length) (j : Nat)
    (hi : i.val = 8) (hsize : C.size = 10)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hread : 0 ∈ (C.gates.get i).inputs)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or)
    (hkop : (C.gates.get k).op = GateOp.and) (hik : i.val < k.val)
    (hreadik : 7 + i.val ∈ (C.gates.get k).inputs)
    (hpartner : j ∈ (C.gates.get i).inputs) (hj0 : j ≠ 0) (hjl : j < 7+i.val) :
    ∀ r : Fin 7, r ≠ 0 → ∃ x y : Fin 7 → Bool,
      (∀ s, s ≠ r → x s = y s) ∧
      (C.wires (List.ofFn x)).getD j false ≠ (C.wires (List.ofFn y)).getD j false := by
  intro r hr
  obtain ⟨hn0,hp0,hnf,hpf,hff,hnflip,hchange⟩ := witness_facts r hr
  have hqpos := partner_true_on_positive C i k j hi hsize hfan hc hread hunique hop
    hkop hik hreadik hpartner hj0 hjl (bits (positive r)) hp0 hpf
  have hqneg : (C.wires (List.ofFn (bits (negative r)))).getD j false = false := by
    cases hv : (C.wires (List.ofFn (bits (negative r)))).getD j false with
    | false => rfl
    | true =>
      have he := circuit_collision_of_one_true C i j
        (List.ofFn (bits (negative r))) (List.ofFn (bits (flipped r)))
        (by simp) (ofFn_agree_zero _ _ hnflip) hv hunique hop hpartner
        (by simpa only [List.length_ofFn] using hjl) hj0 (output_nonzero C hc)
      rw [hc,hc,hnf,hff] at he
      cases he
  refine ⟨bits (negative r),bits (positive r),hchange,?_⟩
  rw [hqneg,hqpos]
  decide

end PEqualNP.Outside.L_meta_29916.Gate8

theorem PEqualNP.Outside.L_meta_29916 :
¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 9 ∈ (C.gates.get i).inputs ∧ 9 ≠ 0 ∧ 9 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 9 false = true) := by
  rintro ⟨C,i,k,hi,hfan,hsize,hc,hread,hunique,hop,hkop,hik,hreadik,hpartner,hj0,hjl,hx⟩
  have hlen : C.gates.length = 10 := hsize
  have hfan' : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hfan g hg).2
  apply PEqualNP.Outside.L_meta_29916.SupportBound.six_inputs_no_early_wire C 9 (by omega) (by omega) hfan'
  exact PEqualNP.Outside.L_meta_29916.Gate8.partner_sensitive C i k 9 hi hsize hfan' hc hread hunique hop
    hkop hik hreadik hpartner hj0 hjl
