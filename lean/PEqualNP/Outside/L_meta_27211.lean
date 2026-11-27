import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27211

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl stepW w

lemma runW_nil (w : List Bool) : runW [] w = w := rfl

lemma runW_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    runW (gs ++ [g]) w = stepW (runW gs w) g := by
  simp [runW, List.foldl_append]

lemma runW_length (gs : List Gate) (w : List Bool) :
    (runW gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runW]
  | cons g gs ih =>
    simp only [runW, List.foldl_cons] at ih ⊢
    rw [ih, stepW, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma getD_snoc_lt (l : List Bool) (v : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [v]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (l : List Bool) (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma runW_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (runW gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (runW gs (stepW w g)).getD i false = w.getD i false
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt, stepW, getD_snoc_lt w _ i hi]

lemma runW_take_getD (gs : List Gate) (w : List Bool) (k i : ℕ) (hi : i < w.length + k) :
    (runW gs w).getD i false = (runW (gs.take k) w).getD i false := by
  have hsp : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsp]
  simp only [runW, List.foldl_append]
  by_cases hk : k ≤ gs.length
  · apply runW_prefix
    change i < (runW (gs.take k) w).length
    rw [runW_length, List.length_take, Nat.min_eq_left hk]
    exact hi
  · rw [List.drop_eq_nil_of_le (by omega), List.foldl_nil]

lemma runW_getD_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (runW gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < x.length + j then (runW gs x).getD i false else false) := by
  have h1 := runW_take_getD gs x (j + 1) (x.length + j) (by omega)
  rw [h1, List.take_succ_eq_append_getElem hj, runW_snoc, stepW]
  have hlen : (runW (gs.take j) x).length = x.length + j := by
    rw [runW_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [← hlen, getD_snoc_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < (runW (gs.take j) x).length
  · simp only [hi, ↓reduceIte]
    exact (runW_take_getD gs x j i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge _ _ (by omega)

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

def wv {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wv_eq_runW {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    wv C x w = (runW C.gates (List.ofFn x)).getD w false := rfl

lemma wv_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wv C x i.val = x i := by
  rw [wv_eq_runW, runW_prefix C.gates (List.ofFn x) i.val (by simp [i.isLt])]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma wv_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.size ≤ w) :
    wv C x w = false := by
  rw [wv_eq_runW]
  apply getD_ge
  rw [runW_length, List.length_ofFn]
  exact hw

lemma wv_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.size) :
    wv C x (n + j) = C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
      if i < n + j then wv C x i else false) := by
  have h := runW_getD_gate C.gates (List.ofFn x) j hj
  simpa [wv_eq_runW, List.length_ofFn] using h

lemma eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

lemma eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by
  cases a <;> rfl

lemma eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by
  cases a <;> rfl

lemma eval_not1 (a : Bool) : GateOp.not.eval [a] = !a := rfl

def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => match g.inputs with | [] => [] | a :: _ => [a]
  | _ => g.inputs

lemma eff_eval_eq (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (val : ℕ → Bool) :
    g.op.eval (g.inputs.map val) = g.op.eval ((eff g).map val) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp [eff, h]
  · simp [eff, h]
  · simp only [eff, h]
    cases g.inputs with
    | nil => rfl
    | cons a tl => rfl

def IsConst {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∃ c : Bool, ∀ x, f x = c

def Drops {m : ℕ} (n_orig : ℕ) (F : ℕ → (Fin m → Bool) → Bool) (j : ℕ) : Prop :=
  IsConst (F (n_orig + j)) ∨ ∃ w < n_orig + j, ∀ x, F (n_orig + j) x = F w x

lemma restrict_build (n_orig m : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (F : ℕ → (Fin m → Bool) → Bool)
    (hin : ∀ i < n_orig, IsConst (F i) ∨ ∃ k < m, ∀ x : Fin m → Bool, F i x = (List.ofFn x).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (x : Fin m → Bool),
      F (n_orig + j) x = gs[j].op.eval (gs[j].inputs.map fun i => if i < n_orig + j then F i x else false)) :
    ∀ K ≤ gs.length,
      ∃ (ds : List Gate) (S : Finset ℕ),
        (∀ g ∈ ds, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (∀ j ∈ S, j < K ∧ ¬ Drops n_orig F j) ∧
        ds.length ≤ S.card ∧
        ∀ w < n_orig + K, IsConst (F w) ∨
          ∃ k < m + ds.length, ∀ x : Fin m → Bool, F w x = (runW ds (List.ofFn x)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [runW] using hin w hw
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, h2, h3, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drops n_orig F j := fun j hj =>
      ⟨Nat.lt_succ_of_lt (h2 j hj).1, (h2 j hj).2⟩
    by_cases hd : Drops n_orig F K
    · refine ⟨ds, S, h1, h2', h3, fun w hw => ?_⟩
      by_cases hlt : w < n_orig + K
      · exact h4 w hlt
      · have heq : w = n_orig + K := by omega
        subst heq
        rcases hd with hc | ⟨u, hu, hu'⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun x => (hu' x).trans (hc x)⟩
          · exact Or.inr ⟨k, hk, fun x => (hu' x).trans (hk' x)⟩
    · have addg : ∀ g : Gate,
          g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
          g.inputs.length ≤ 2 →
          (∀ x : Fin m → Bool, F (n_orig + K) x =
            g.op.eval (g.inputs.map fun i => (runW ds (List.ofFn x)).getD i false)) →
          ∃ (ds' : List Gate) (S' : Finset ℕ),
            (∀ g ∈ ds', g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
            (∀ j ∈ S', j < K + 1 ∧ ¬ Drops n_orig F j) ∧
            ds'.length ≤ S'.card ∧
            ∀ w < n_orig + (K + 1), IsConst (F w) ∨
              ∃ k < m + ds'.length, ∀ x : Fin m → Bool, F w x = (runW ds' (List.ofFn x)).getD k false := by
        intro g hg1 hg2 hg
        have hnotS : K ∉ S := fun hm => Nat.lt_irrefl K (h2 K hm).1
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h' | rfl
          · exact h1 g' h'
          · exact ⟨hg1, hg2⟩
        · intro j hj
          simp only [Finset.mem_insert] at hj
          rcases hj with hjK | hj
          · subst hjK; exact ⟨Nat.lt_succ_self _, hd⟩
          · exact h2' j hj
        · rw [List.length_append, List.length_singleton, Finset.card_insert_of_notMem hnotS]
          omega
        · intro w hw
          by_cases hlt : w < n_orig + K
          · rcases h4 w hlt with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun x => ?_⟩
              rw [runW_snoc, stepW, getD_snoc_lt _ _ _ (by rw [runW_length, List.length_ofFn]; exact hk)]
              exact hk' x
          · refine Or.inr ⟨m + ds.length, by simp, fun x => ?_⟩
            have hl' : (runW ds (List.ofFn x)).length = m + ds.length := by
              rw [runW_length, List.length_ofFn]
            rw [show w = n_orig + K by omega, runW_snoc, stepW, ← hl', getD_snoc_eq]
            exact hg x
      have hval : ∀ i, (∃ c, ∀ x, (if i < n_orig + K then F i x else false) = c) ∨
          (∃ k < m + ds.length, ∀ x, (if i < n_orig + K then F i x else false) =
            (runW ds (List.ofFn x)).getD k false) := by
        intro i
        by_cases hi : i < n_orig + K
        · rcases h4 i hi with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun x => by simp only [hi, ↓reduceIte]; exact hc x⟩
          · exact Or.inr ⟨k, hk, fun x => by simp only [hi, ↓reduceIte]; exact hk' x⟩
        · exact Or.inl ⟨false, fun x => by simp only [hi, ↓reduceIte]⟩
      have hKlt : K < gs.length := by omega
      have hFK := hF K hKlt
      obtain ⟨hop, hlen⟩ := hfan gs[K] (List.getElem_mem hKlt)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · rcases hls : gs[K].inputs with _ | ⟨a, _ | ⟨b, tl⟩⟩
        · exfalso; apply hd; left; refine ⟨true, fun x => ?_⟩; rw [hFK, hop, hls]; rfl
        · exfalso; apply hd
          by_cases ha : a < n_orig + K
          · exact Or.inr ⟨a, ha, fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, ha, ↓reduceIte, eval_and1]⟩
          · exact Or.inl ⟨false, fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, ha, ↓reduceIte, eval_and1]⟩
        · have htl : tl = [] := by
            rw [hls] at hlen; cases tl <;> simp at hlen ⊢
          subst htl
          rcases hval a with ⟨ca, hca⟩ | ⟨ka, _, hka⟩ <;>
            rcases hval b with ⟨cb, hcb⟩ | ⟨kb, _, hkb⟩
          · exfalso; apply hd; left; refine ⟨ca && cb, fun x => ?_⟩
            rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, hcb x, eval_and2]
          · cases ca
            · exfalso; apply hd; left; refine ⟨false, fun x => ?_⟩
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, eval_and2, Bool.false_and]
            · exfalso; apply hd
              by_cases hb : b < n_orig + K
              · exact Or.inr ⟨b, hb, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, hb, ↓reduceIte, eval_and2, Bool.true_and]⟩
              · exact Or.inl ⟨false, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, hb, ↓reduceIte, eval_and2, Bool.true_and]⟩
          · cases cb
            · exfalso; apply hd; left; refine ⟨false, fun x => ?_⟩
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, eval_and2, Bool.and_false]
            · exfalso; apply hd
              by_cases ha : a < n_orig + K
              · exact Or.inr ⟨a, ha, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, ha, ↓reduceIte, eval_and2, Bool.and_true]⟩
              · exact Or.inl ⟨false, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, ha, ↓reduceIte, eval_and2, Bool.and_true]⟩
          · exact addg ⟨GateOp.and, [ka, kb]⟩ (by simp) (by simp) (fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hka x, hkb x, eval_and2])
      · rcases hls : gs[K].inputs with _ | ⟨a, _ | ⟨b, tl⟩⟩
        · exfalso; apply hd; left; refine ⟨false, fun x => ?_⟩; rw [hFK, hop, hls]; rfl
        · exfalso; apply hd
          by_cases ha : a < n_orig + K
          · exact Or.inr ⟨a, ha, fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, ha, ↓reduceIte, eval_or1]⟩
          · exact Or.inl ⟨false, fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, ha, ↓reduceIte, eval_or1]⟩
        · have htl : tl = [] := by
            rw [hls] at hlen; cases tl <;> simp at hlen ⊢
          subst htl
          rcases hval a with ⟨ca, hca⟩ | ⟨ka, _, hka⟩ <;>
            rcases hval b with ⟨cb, hcb⟩ | ⟨kb, _, hkb⟩
          · exfalso; apply hd; left; refine ⟨ca || cb, fun x => ?_⟩
            rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, hcb x, eval_or2]
          · cases ca
            · exfalso; apply hd
              by_cases hb : b < n_orig + K
              · exact Or.inr ⟨b, hb, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, hb, ↓reduceIte, eval_or2, Bool.false_or]⟩
              · exact Or.inl ⟨false, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, hb, ↓reduceIte, eval_or2, Bool.false_or]⟩
            · exfalso; apply hd; left; refine ⟨true, fun x => ?_⟩
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hca x, eval_or2, Bool.true_or]
          · cases cb
            · exfalso; apply hd
              by_cases ha : a < n_orig + K
              · exact Or.inr ⟨a, ha, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, ha, ↓reduceIte, eval_or2, Bool.or_false]⟩
              · exact Or.inl ⟨false, fun x => by
                  rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, ha, ↓reduceIte, eval_or2, Bool.or_false]⟩
            · exfalso; apply hd; left; refine ⟨true, fun x => ?_⟩
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hcb x, eval_or2, Bool.or_true]
          · exact addg ⟨GateOp.or, [ka, kb]⟩ (by simp) (by simp) (fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, List.map_nil, hka x, hkb x, eval_or2])
      · rcases hls : gs[K].inputs with _ | ⟨a, tl⟩
        · exfalso; apply hd; left; refine ⟨true, fun x => ?_⟩; rw [hFK, hop, hls]; rfl
        · rcases hval a with ⟨ca, hca⟩ | ⟨ka, _, hka⟩
          · exfalso; apply hd; left; refine ⟨!ca, fun x => ?_⟩
            rw [hFK, hop, hls]; simp only [List.map_cons, GateOp.eval, List.headD, hca x]
          · exact addg ⟨GateOp.not, [ka]⟩ (by simp) (by simp) (fun x => by
              rw [hFK, hop, hls]; simp only [List.map_cons, GateOp.eval, List.headD, hka x])

lemma shrink_of_drop {n : ℕ} (D : Circuit) (hfan : FanInTwo D)
    (F : ℕ → (Fin n → Bool) → Bool)
    (hin : ∀ i < n, IsConst (F i) ∨ ∃ k < n, ∀ x, F i x = (List.ofFn x).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < D.size) (x : Fin n → Bool),
      F (n + j) x = D.gates[j].op.eval (D.gates[j].inputs.map fun i => if i < n + j then F i x else false))
    (hout_lt : D.output < n + D.size)
    (hnc : ¬ IsConst (F D.output))
    (j0 : ℕ) (hj0 : j0 < D.size) (hdrop : Drops n F j0) :
    ∃ E : Circuit, FanInTwo E ∧ E.size < D.size ∧ ∀ x : Fin n → Bool, E.eval (List.ofFn x) = F D.output x := by
  obtain ⟨ds, S, h1, h2, h3, h4⟩ := restrict_build n n D.gates hfan F hin hF D.size le_rfl
  have hSsub : S ⊆ (Finset.range D.size).erase j0 := by
    intro j hj
    have ⟨hlt, hnd⟩ := h2 j hj
    exact Finset.mem_erase.mpr ⟨fun heq => hnd (heq ▸ hdrop), Finset.mem_range.mpr hlt⟩
  have hScard : S.card ≤ D.size - 1 := by
    have hle := Finset.card_le_card hSsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj0), Finset.card_range] at hle
    exact hle
  rcases h4 D.output hout_lt with hc | ⟨k, _, hk'⟩
  · exact (hnc hc).elim
  · refine ⟨⟨ds, k⟩, h1, ?_, fun x => (hk' x).symm⟩
    change ds.length < D.gates.length
    have hDsz : D.size = D.gates.length := rfl
    omega

lemma shrink_of_dead {n : ℕ} (D : Circuit) (hfan : FanInTwo D)
    (j0 : ℕ) (hj0 : j0 < D.size) (hne_out : D.output ≠ n + j0)
    (hdead : ∀ (k : ℕ) (hk : k < D.size), j0 < k → n + j0 ∉ eff D.gates[k]) :
    ∃ E : Circuit, FanInTwo E ∧ E.size < D.size ∧ ∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x) := by
  have hDsz : D.size = D.gates.length := rfl
  let shift (w : ℕ) : ℕ := if n + j0 < w then w - 1 else w
  let mapG (g : Gate) : Gate := ⟨g.op, (eff g).map shift⟩
  let ds : List Gate := (List.range (D.size - 1)).map fun k =>
    if k < j0 then mapG (D.gates.getD k ⟨GateOp.or, []⟩)
    else mapG (D.gates.getD (k + 1) ⟨GateOp.or, []⟩)
  let E : Circuit := ⟨ds, shift D.output⟩
  have hElen : E.gates.length = D.gates.length - 1 := by simp [E, ds, Circuit.size]
  have hEsz : E.size = E.gates.length := rfl
  have hEfan : FanInTwo E := by
    intro g hg
    simp only [E, ds, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with hlt
    · have hk' : k < D.gates.length := by omega
      have hget : D.gates.getD k ⟨GateOp.or, []⟩ = D.gates[k] := by
        simp [List.getD_eq_getElem?_getD, hk']
      rw [hget]
      obtain ⟨hop, hlen⟩ := hfan D.gates[k] (List.getElem_mem hk')
      refine ⟨hop, ?_⟩
      simp only [mapG, List.length_map]
      unfold eff
      cases D.gates[k].op <;> simp only [hlen]
      cases D.gates[k].inputs <;> simp
    · have hk' : k + 1 < D.gates.length := by omega
      have hget : D.gates.getD (k + 1) ⟨GateOp.or, []⟩ = D.gates[k + 1] := by
        simp [List.getD_eq_getElem?_getD, hk']
      rw [hget]
      obtain ⟨hop, hlen⟩ := hfan D.gates[k + 1] (List.getElem_mem hk')
      refine ⟨hop, ?_⟩
      simp only [mapG, List.length_map]
      unfold eff
      cases D.gates[k + 1].op <;> simp only [hlen]
      cases D.gates[k + 1].inputs <;> simp
  have hval : ∀ (x : Fin n → Bool) (w : ℕ), w ≠ n + j0 → wv E x (shift w) = wv D x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hne
      by_cases hw : w < n
      · have hs : shift w = w := by simp [shift]; omega
        rw [hs, wv_input E x ⟨w, hw⟩, wv_input D x ⟨w, hw⟩]
      · by_cases hge : n + D.size ≤ w
        · have hs : n + E.size ≤ shift w := by
            simp only [shift]; split_ifs <;> omega
          rw [wv_ge E x (shift w) hs, wv_ge D x w hge]
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < D.size := by omega
          have hk' : k < D.gates.length := by omega
          by_cases hlt : k < j0
          · have hs : shift (n + k) = n + k := by simp [shift]; omega
            have hkE : k < E.size := by omega
            rw [hs, wv_gate E x k hkE, wv_gate D x k hk]
            have hgE : E.gates[k]'hkE = mapG D.gates[k] := by
              simp [E, ds, hlt, List.getD_eq_getElem?_getD, hk']
            rw [hgE, eff_eval_eq _ (hfan _ (List.getElem_mem hk)).1]
            simp only [mapG, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u _
            simp only [Function.comp_apply]
            by_cases hu : u < n + k
            · have hsu : shift u = u := by simp [shift]; omega
              simp only [hu, hsu, ↓reduceIte]
              have := ih u hu (by omega)
              rwa [hsu] at this
            · by_cases hsu : shift u < n + k
              · exfalso; simp only [shift] at hsu; split_ifs at hsu <;> omega
              · simp only [hsu, hu, ↓reduceIte]
          · have hgt : j0 < k := by omega
            have hs : shift (n + k) = n + (k - 1) := by simp only [shift]; split_ifs <;> omega
            have hkE : k - 1 < E.size := by omega
            rw [hs, wv_gate E x (k - 1) hkE, wv_gate D x k hk]
            have hgE : E.gates[k - 1]'hkE = mapG D.gates[k] := by
              have hnot : ¬ (k - 1 < j0) := by omega
              have hadd : k - 1 + 1 = k := by omega
              simp [E, ds, hnot, hadd, List.getD_eq_getElem?_getD, hk']
            rw [hgE, eff_eval_eq _ (hfan _ (List.getElem_mem hk)).1]
            simp only [mapG, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu_mem
            simp only [Function.comp_apply]
            have hune : u ≠ n + j0 := fun h => hdead k hk hgt (h ▸ hu_mem)
            by_cases hu : u < n + k
            · have hsu : shift u < n + (k - 1) := by simp only [shift]; split_ifs <;> omega
              simp only [hsu, hu, ↓reduceIte]
              exact ih u hu hune
            · have hsu : ¬ shift u < n + (k - 1) := by simp only [shift]; split_ifs <;> omega
              simp only [hsu, hu, ↓reduceIte]
  refine ⟨E, hEfan, by change E.gates.length < D.gates.length; omega, fun x => hval x D.output hne_out⟩

private lemma bool_and_le {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    (a₁ && b₁) ≤ (a₂ && b₂) := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp_all

private lemma bool_or_le {a₁ a₂ b₁ b₂ : Bool} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    (a₁ || b₁) ≤ (a₂ || b₂) := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp_all

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def embed (y : Fin 7 → Bool) : Fin 9 → Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => y 0
  | ⟨2, _⟩ => y 1
  | ⟨3, _⟩ => y 2
  | ⟨4, _⟩ => false
  | ⟨5, _⟩ => y 3
  | ⟨6, _⟩ => y 4
  | ⟨7, _⟩ => y 5
  | ⟨8, _⟩ => y 6

def hfun (y : Fin 7 → Bool) : Bool :=
  (y 3 && y 5) || (y 0 && y 2 && y 6) || (y 0 && y 3 && y 4) || (y 1 && y 2 && y 5)

lemma pm3_embed (y : Fin 7 → Bool) : pm3 (embed y) = hfun y := by
  unfold pm3 embed hfun
  cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;> cases y 4 <;> cases y 5 <;> cases y 6 <;> rfl

lemma hfun_ess (i : Fin 7) : ∃ y : Fin 7 → Bool,
    hfun (Function.update y i false) ≠ hfun (Function.update y i true) := by
  fin_cases i
  · refine ⟨fun j => j == 2 || j == 6, by decide⟩
  · refine ⟨fun j => j == 2 || j == 5, by decide⟩
  · refine ⟨fun j => j == 0 || j == 6, by decide⟩
  · refine ⟨fun j => j == 5, by decide⟩
  · refine ⟨fun j => j == 0 || j == 3, by decide⟩
  · refine ⟨fun j => j == 3, by decide⟩
  · refine ⟨fun j => j == 0 || j == 2, by decide⟩

lemma hfun_nonconst : ¬ IsConst hfun := by
  rintro ⟨c, hc⟩
  have h0 := hc (fun _ => false)
  have h1 := hc (fun _ => true)
  have : hfun (fun _ => false) = hfun (fun _ => true) := h0.trans h1.symm
  exact absurd this (by decide)

lemma no_circuit_le6 (E : Circuit) (hEfan : FanInTwo E) (hEsz : E.size ≤ 6)
    (hEeval : ∀ y : Fin 7 → Bool, E.eval (List.ofFn y) = hfun y) : False := by
  classical
  let P (k : ℕ) : Prop := ∃ D : Circuit, FanInTwo D ∧ D.size = k ∧ ∀ y : Fin 7 → Bool, D.eval (List.ofFn y) = hfun y
  have hPex : ∃ k, P k := ⟨E.size, E, hEfan, rfl, hEeval⟩
  obtain ⟨D, hDfan, hDsz, hDeval⟩ := Nat.find_spec hPex
  have hDle6 : D.size ≤ 6 := le_trans (hDsz ▸ Nat.find_min' hPex ⟨E, hEfan, rfl, hEeval⟩) hEsz
  have hDmin : ∀ E' : Circuit, FanInTwo E' → (∀ y, E'.eval (List.ofFn y) = hfun y) → D.size ≤ E'.size := by
    intro E' h1 h2; rw [hDsz]; exact Nat.find_min' hPex ⟨E', h1, rfl, h2⟩

  have hout_lt : D.output < 7 + D.size := by
    by_contra hge
    apply hfun_nonconst
    refine ⟨false, fun y => ?_⟩
    rw [← hDeval y]; exact wv_ge D y D.output (by omega)
  have hout_ge : 7 ≤ D.output := by
    by_contra hlt
    have hlt' : D.output < 7 := by omega
    have hdep : ∀ y : Fin 7 → Bool, hfun y = y ⟨D.output, hlt'⟩ := fun y => by
      rw [← hDeval y]; exact wv_input D y ⟨D.output, hlt'⟩
    have hne : ∃ i : Fin 7, i ≠ ⟨D.output, hlt'⟩ := by
      by_cases h0 : (⟨0, by omega⟩ : Fin 7) = ⟨D.output, hlt'⟩
      · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val (h.trans h0.symm); dsimp at this; omega⟩
      · exact ⟨⟨0, by omega⟩, h0⟩
    obtain ⟨i, hi⟩ := hne
    obtain ⟨y, hy⟩ := hfun_ess i
    apply hy
    rw [hdep, hdep, Function.update_of_ne (Ne.symm hi), Function.update_of_ne (Ne.symm hi)]

  have hno_drop : ∀ j < D.size, ¬ Drops 7 (fun w (y : Fin 7 → Bool) => wv D y w) j := by
    intro j hj hdrop
    have hout_eq : ∀ y, wv D y D.output = hfun y := hDeval
    obtain ⟨E', hE'fan, hE'lt, hE'eval⟩ := shrink_of_drop D hDfan (fun w (y : Fin 7 → Bool) => wv D y w)
      (fun i hi => Or.inr ⟨i, hi, fun y => (wv_input D y ⟨i, hi⟩).trans (getD_ofFn y i hi).symm⟩)
      (fun k hk y => wv_gate D y k hk) hout_lt (by have : (fun y => wv D y D.output) = hfun := funext hout_eq; rw [this]; exact hfun_nonconst) j hj hdrop
    have hle := hDmin E' hE'fan (fun y => (hE'eval y).trans (hout_eq y))
    omega

  have hgate_clean : ∀ j (hj : j < D.size),
      (D.gates[j].op = GateOp.not → ∃ u < 7 + j, eff D.gates[j] = [u]) ∧
      ((D.gates[j].op = GateOp.and ∨ D.gates[j].op = GateOp.or) →
        ∃ u v, u < 7 + j ∧ v < 7 + j ∧ u ≠ v ∧ eff D.gates[j] = [u, v]) := by
    intro j hj
    obtain ⟨hop, hlen⟩ := hDfan D.gates[j] (List.getElem_mem hj)
    constructor
    · intro hnot
      rcases hls : D.gates[j].inputs with _ | ⟨u, tl⟩
      · exfalso; apply hno_drop j hj; left
        refine ⟨true, fun y => ?_⟩; dsimp only; rw [wv_gate D y j hj, hnot, hls]; rfl
      · by_cases hu : u < 7 + j
        · exact ⟨u, hu, by simp [eff, hnot, hls]⟩
        · exfalso; apply hno_drop j hj; left
          refine ⟨true, fun y => ?_⟩; dsimp only; rw [wv_gate D y j hj, hnot, hls]; simp [GateOp.eval, hu]
    · intro hbin
      have heff : eff D.gates[j] = D.gates[j].inputs := by
        rcases hbin with h | h <;> simp [eff, h]
      rcases hls : D.gates[j].inputs with _ | ⟨u, _ | ⟨v, tl⟩⟩
      · exfalso; apply hno_drop j hj; left
        rcases hbin with h | h
        · exact ⟨true, fun y => by dsimp only; rw [wv_gate D y j hj, h, hls]; rfl⟩
        · exact ⟨false, fun y => by dsimp only; rw [wv_gate D y j hj, h, hls]; rfl⟩
      · exfalso; apply hno_drop j hj
        by_cases hu : u < 7 + j
        · right; refine ⟨u, hu, fun y => ?_⟩
          rcases hbin with h | h <;> simp [wv_gate D y j hj, h, hls, hu, eval_and1, eval_or1]
        · left; refine ⟨false, fun y => ?_⟩
          rcases hbin with h | h <;> simp [wv_gate D y j hj, h, hls, hu, eval_and1, eval_or1]
      · have htl : tl = [] := by rw [hls] at hlen; cases tl <;> simp at hlen ⊢
        subst htl
        by_cases hu : u < 7 + j
        · by_cases hv : v < 7 + j
          · by_cases huv : u = v
            · subst huv
              exfalso; apply hno_drop j hj; right
              refine ⟨u, hu, fun y => ?_⟩
              rcases hbin with h | h <;> simp [wv_gate D y j hj, h, hls, hu, eval_and2, eval_or2]
            · exact ⟨u, v, hu, hv, huv, by rw [heff, hls]⟩
          · exfalso; apply hno_drop j hj
            rcases hbin with h | h
            · left; exact ⟨false, fun y => by simp [wv_gate D y j hj, h, hls, hu, hv, eval_and2]⟩
            · right; exact ⟨u, hu, fun y => by simp [wv_gate D y j hj, h, hls, hu, hv, eval_or2]⟩
        · exfalso; apply hno_drop j hj
          rcases hbin with h | h
          · left; exact ⟨false, fun y => by simp [wv_gate D y j hj, h, hls, hu, eval_and2]⟩
          · by_cases hv : v < 7 + j
            · right; exact ⟨v, hv, fun y => by simp [wv_gate D y j hj, h, hls, hu, hv, eval_or2]⟩
            · left; exact ⟨false, fun y => by simp [wv_gate D y j hj, h, hls, hu, hv, eval_or2]⟩

  have heff_lt : ∀ k (hk : k < D.size) u, u ∈ eff D.gates[k] → u < 7 + k := by
    intro k hk u hu
    obtain ⟨hop, _⟩ := hDfan D.gates[k] (List.getElem_mem hk)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inl h)
      rw [heff] at hu; simp at hu; rcases hu with rfl | rfl <;> assumption
    · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inr h)
      rw [heff] at hu; simp at hu; rcases hu with rfl | rfl <;> assumption
    · obtain ⟨p, hp, heff⟩ := (hgate_clean k hk).1 h
      rw [heff] at hu; simp at hu; subst hu; exact hp

  have hgate_live : ∀ j < D.size, D.output ≠ 7 + j →
      ∃ k, ∃ hk : k < D.size, j < k ∧ 7 + j ∈ eff D.gates[k] := by
    intro j hj hne
    by_contra hdead
    push Not at hdead
    obtain ⟨E', hE'fan, hE'lt, hE'eval⟩ := shrink_of_dead D hDfan j hj hne hdead
    have hle := hDmin E' hE'fan (fun y => (hE'eval y).trans (hDeval y))
    omega

  have hout_last : D.output = 7 + (D.size - 1) := by
    by_contra hne
    obtain ⟨k, hk, hlt, _⟩ := hgate_live (D.size - 1) (by omega) hne
    omega

  have hess_read : ∀ i : Fin 7, ∃ k, ∃ hk : k < D.size, i.val ∈ eff D.gates[k] := by
    intro i
    by_contra hno
    push Not at hno
    have hsame : ∀ (x y : Fin 7 → Bool), (∀ j : Fin 7, j ≠ i → x j = y j) →
        ∀ w, w ≠ i.val → wv D x w = wv D y w := by
      intro x y hxy w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hne
        by_cases hw : w < 7
        · rw [wv_input D x ⟨w, hw⟩, wv_input D y ⟨w, hw⟩]
          exact hxy ⟨w, hw⟩ (fun h => hne (congrArg Fin.val h))
        · by_cases hge : 7 + D.size ≤ w
          · rw [wv_ge D x w hge, wv_ge D y w hge]
          · obtain ⟨k, rfl⟩ : ∃ k, w = 7 + k := ⟨w - 7, by omega⟩
            have hk : k < D.size := by omega
            rw [wv_gate D x k hk, wv_gate D y k hk,
              eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1,
              eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := heff_lt k hk u hu
            simp only [hult, ↓reduceIte]
            exact ih u hult (fun h => hno k hk (h ▸ hu))
    obtain ⟨y, hy⟩ := hfun_ess i
    apply hy
    rw [← hDeval, ← hDeval]
    exact hsame _ _ (fun j hj => by simp [hj]) D.output (by have := i.isLt; omega)

  let Nodes : Finset ℕ := Finset.range (7 + D.size)
  let readers (u : ℕ) : Finset ℕ :=
    (Finset.range D.size).filter (fun k => if hk : k < D.size then u ∈ eff D.gates[k] else false)
  let outdeg (u : ℕ) : ℕ := (readers u).card
  let Gnot : Finset ℕ := (Finset.range D.size).filter (fun k =>
    if hk : k < D.size then D.gates[k].op = GateOp.not else false)
  let Gbin : Finset ℕ := (Finset.range D.size).filter (fun k =>
    if hk : k < D.size then D.gates[k].op = GateOp.and ∨ D.gates[k].op = GateOp.or else false)
  have hBN : Gbin.card + Gnot.card = D.size := by
    have hdisj : Disjoint Gbin Gnot := by
      rw [Finset.disjoint_left]
      intro k h1 h2
      simp only [Gbin, Gnot, Finset.mem_filter, Finset.mem_range] at h1 h2
      have hk := h1.1
      simp only [hk, ↓reduceDIte] at h1 h2
      rcases h1.2 with h | h <;> rw [h] at h2 <;> cases h2.2
    have hunion : Gbin ∪ Gnot = Finset.range D.size := by
      ext k
      simp only [Gbin, Gnot, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hk
        have hop := (hDfan D.gates[k] (List.getElem_mem hk)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with h | h | h
        · left; exact ⟨hk, by simp only [hk, ↓reduceDIte]; exact Or.inl h⟩
        · left; exact ⟨hk, by simp only [hk, ↓reduceDIte]; exact Or.inr h⟩
        · right; exact ⟨hk, by simp only [hk, ↓reduceDIte]; exact h⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
  have hsum_deg : ∑ u ∈ Nodes, outdeg u = 2 * Gbin.card + Gnot.card := by
    have hswap : ∑ u ∈ Nodes, outdeg u =
        ∑ k ∈ Finset.range D.size, (Nodes.filter (fun u =>
          if hk : k < D.size then u ∈ eff D.gates[k] else false)).card := by
      simp only [outdeg, readers, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap]
    have hterm : ∀ k ∈ Finset.range D.size,
        (Nodes.filter (fun u => if hk : k < D.size then u ∈ eff D.gates[k] else false)).card =
          if k ∈ Gbin then 2 else 1 := by
      intro k hk
      have hk' : k < D.size := Finset.mem_range.mp hk
      have hmem_nodes : ∀ u, u ∈ eff D.gates[k] → u ∈ Nodes := fun u hu =>
        Finset.mem_range.mpr (by have := heff_lt k hk' u hu; omega)
      have hop := (hDfan D.gates[k] (List.getElem_mem hk')).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · obtain ⟨p, q, _, _, hpq, heff⟩ := (hgate_clean k hk').2 (Or.inl h)
        have hkb : k ∈ Gbin := Finset.mem_filter.mpr ⟨hk, by simp only [hk', ↓reduceDIte]; exact Or.inl h⟩
        simp only [hkb, ↓reduceIte]
        have hfilt : Nodes.filter (fun u => if hk2 : k < D.size then u ∈ eff D.gates[k] else false) = {p, q} := by
          ext u
          simp only [Finset.mem_filter, hk', ↓reduceDIte, heff, List.mem_cons, List.not_mem_nil, or_false,
            Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨hmem_nodes u (by rw [heff]; simpa using h), h⟩⟩
        rw [hfilt, Finset.card_pair hpq]
      · obtain ⟨p, q, _, _, hpq, heff⟩ := (hgate_clean k hk').2 (Or.inr h)
        have hkb : k ∈ Gbin := Finset.mem_filter.mpr ⟨hk, by simp only [hk', ↓reduceDIte]; exact Or.inr h⟩
        simp only [hkb, ↓reduceIte]
        have hfilt : Nodes.filter (fun u => if hk2 : k < D.size then u ∈ eff D.gates[k] else false) = {p, q} := by
          ext u
          simp only [Finset.mem_filter, hk', ↓reduceDIte, heff, List.mem_cons, List.not_mem_nil, or_false,
            Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨hmem_nodes u (by rw [heff]; simpa using h), h⟩⟩
        rw [hfilt, Finset.card_pair hpq]
      · obtain ⟨p, _, heff⟩ := (hgate_clean k hk').1 h
        have hkb : k ∉ Gbin := by
          intro hm; simp only [Gbin, Finset.mem_filter, hk', ↓reduceDIte, h] at hm
          rcases hm.2 with h1 | h1 <;> cases h1
        simp only [hkb, ↓reduceIte]
        have hfilt : Nodes.filter (fun u => if hk2 : k < D.size then u ∈ eff D.gates[k] else false) = {p} := by
          ext u
          simp only [Finset.mem_filter, hk', ↓reduceDIte, heff, List.mem_singleton, Finset.mem_singleton]
          exact ⟨fun h => h.2, fun h => ⟨hmem_nodes u (by rw [heff]; simpa using h), h⟩⟩
        rw [hfilt, Finset.card_singleton]
    rw [Finset.sum_congr rfl hterm]
    have hsub : Gbin ⊆ Finset.range D.size := Finset.filter_subset _ _
    have hsplit : ∑ k ∈ Finset.range D.size, (if k ∈ Gbin then (2 : ℕ) else 1) =
        2 * Gbin.card + (Finset.range D.size \ Gbin).card := by
      rw [← Finset.sum_sdiff hsub]
      have h1 : ∑ k ∈ Gbin, (if k ∈ Gbin then (2 : ℕ) else 1) = 2 * Gbin.card := by
        rw [Finset.sum_congr rfl (fun k hk => by show (if k ∈ Gbin then (2 : ℕ) else 1) = 2; simp only [hk, ↓reduceIte]),
          Finset.sum_const, smul_eq_mul, mul_comm]
      have h2 : ∑ k ∈ Finset.range D.size \ Gbin, (if k ∈ Gbin then (2 : ℕ) else 1) =
          (Finset.range D.size \ Gbin).card := by
        rw [Finset.sum_congr rfl (fun k hk => by show (if k ∈ Gbin then (2 : ℕ) else 1) = 1; simp only [(Finset.mem_sdiff.mp hk).2, ↓reduceIte]),
          Finset.sum_const, smul_eq_mul, mul_one]
      rw [h1, h2, add_comm]
    rw [hsplit]
    have hsdiff : (Finset.range D.size \ Gbin).card = Gnot.card := by
      have := Finset.card_sdiff (s := Gbin) (t := Finset.range D.size)
      rw [Finset.inter_eq_left.mpr hsub, Finset.card_range] at this
      omega
    rw [hsdiff]

  have hout_mem : D.output ∈ Nodes := Finset.mem_range.mpr hout_lt
  have hout_deg0 : outdeg D.output = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hk
    have hk' := hk.1
    simp only [hk', ↓reduceDIte] at hk
    have hlt := heff_lt k hk' D.output hk.2
    omega
  have hpos_deg : ∀ u ∈ Nodes.erase D.output, 1 ≤ outdeg u := by
    intro u hu
    have ⟨hne, hmem⟩ := Finset.mem_erase.mp hu
    have hult : u < 7 + D.size := Finset.mem_range.mp hmem
    by_cases hun : u < 7
    · obtain ⟨k, hk, hkin⟩ := hess_read ⟨u, hun⟩
      exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by simp only [hk, ↓reduceDIte]; exact hkin⟩⟩
    · obtain ⟨k, hk, _, hkin⟩ := hgate_live (u - 7) (by omega) (by omega)
      exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by
        simp only [hk, ↓reduceDIte]; rwa [show 7 + (u - 7) = u by omega] at hkin⟩⟩
  let F : ℕ := ∑ u ∈ Nodes.erase D.output, (outdeg u - 1)
  have hF_eq : 7 + D.size - 1 + F = 2 * Gbin.card + Gnot.card := by
    have h1 : ∑ u ∈ Nodes, outdeg u = outdeg D.output + ∑ u ∈ Nodes.erase D.output, outdeg u :=
      (Finset.add_sum_erase Nodes outdeg hout_mem).symm
    have h2 : ∑ u ∈ Nodes.erase D.output, outdeg u = (Nodes.erase D.output).card + F := by
      have hterm : ∀ u ∈ Nodes.erase D.output, outdeg u = 1 + (outdeg u - 1) := fun u hu => by
        have := hpos_deg u hu; omega
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    rw [hsum_deg, hout_deg0, zero_add, h2, Finset.card_erase_of_mem hout_mem, Finset.card_range] at h1
    omega

  have hD6 : D.size = 6 := by omega
  have hF0 : F = 0 := by omega
  have hN0 : Gnot.card = 0 := by omega
  have hnoNot : ∀ k (hk : k < D.size), D.gates[k].op ≠ GateOp.not := by
    intro k hk hnot
    have hmem : k ∈ Gnot := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by simp only [hk, ↓reduceDIte]; exact hnot⟩
    have hpos : 0 < Gnot.card := Finset.card_pos.mpr ⟨k, hmem⟩
    omega
  have hout1 : ∀ u, outdeg u ≤ 1 := by
    intro u
    by_cases hmem : u ∈ Nodes.erase D.output
    · have h0 : outdeg u - 1 = 0 := by
        have := Finset.single_le_sum (f := fun z => outdeg z - 1) (fun _ _ => Nat.zero_le _) hmem
        omega
      omega
    · by_cases heq : u = D.output
      · rw [heq, hout_deg0]; omega
      · have hnot : u ∉ Nodes := fun hm => hmem (Finset.mem_erase.mpr ⟨heq, hm⟩)
        have h0 : outdeg u = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro k hk
          simp only [readers, Finset.mem_filter, Finset.mem_range] at hk
          have hk' := hk.1
          simp only [hk', ↓reduceDIte] at hk
          have := heff_lt k hk' u hk.2
          exact hnot (Finset.mem_range.mpr (by omega))
        omega

  have hmono : ∀ (x y : Fin 7 → Bool), (∀ i, x i ≤ y i) → ∀ w, wv D x w ≤ wv D y w := by
    intro x y hxy w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hw : w < 7
      · rw [wv_input D x ⟨w, hw⟩, wv_input D y ⟨w, hw⟩]; exact hxy ⟨w, hw⟩
      · by_cases hge : 7 + D.size ≤ w
        · rw [wv_ge D x w hge, wv_ge D y w hge]
        · obtain ⟨k, rfl⟩ : ∃ k, w = 7 + k := ⟨w - 7, by omega⟩
          have hk : k < D.size := by omega
          have hop := (hDfan D.gates[k] (List.getElem_mem hk)).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hand | hor | hnot
          · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inl hand)
            rw [wv_gate D x k hk, wv_gate D y k hk,
              eff_eval_eq _ (by simp [hand]), eff_eval_eq _ (by simp [hand]), heff, hand]
            simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_and2]
            exact bool_and_le (ih p hp) (ih q hq)
          · obtain ⟨p, q, hp, hq, _, heff⟩ := (hgate_clean k hk).2 (Or.inr hor)
            rw [wv_gate D x k hk, wv_gate D y k hk,
              eff_eval_eq _ (by simp [hor]), eff_eval_eq _ (by simp [hor]), heff, hor]
            simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_or2]
            exact bool_or_le (ih p hp) (ih q hq)
          · exact (hnoNot k hk hnot).elim

  let Step (u w : ℕ) : Prop := ∃ k, ∃ hk : k < D.size, w = 7 + k ∧ u ∈ eff D.gates[k]
  let Reach (u w : ℕ) : Prop := Relation.ReflTransGen Step u w
  have hReach_le : ∀ u w, Reach u w → u ≤ w := by
    intro u w h
    induction h with
    | refl => exact le_rfl
    | @tail y z _ hstep ih =>
      obtain ⟨k, hk, rfl, hmem⟩ := hstep
      have := heff_lt k hk y hmem
      omega
  have hstep_det : ∀ u w₁ w₂, Step u w₁ → Step u w₂ → w₁ = w₂ := by
    intro u w₁ w₂ ⟨k₁, hk₁, h1eq, hm₁⟩ ⟨k₂, hk₂, h2eq, hm₂⟩
    have h1 : k₁ ∈ readers u := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk₁, by simp only [hk₁, ↓reduceDIte]; exact hm₁⟩
    have h2 : k₂ ∈ readers u := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk₂, by simp only [hk₂, ↓reduceDIte]; exact hm₂⟩
    have heq := Finset.card_le_one.mp (hout1 u) k₁ h1 k₂ h2
    rw [h1eq, h2eq, heq]
  have hreach_total : ∀ u w₁ w₂, Reach u w₁ → Reach u w₂ → Reach w₁ w₂ ∨ Reach w₂ w₁ := by
    intro u w₁ w₂ h1
    induction h1 using Relation.ReflTransGen.head_induction_on with
    | refl => intro h2; exact Or.inl h2
    | @head a b hstep h1' ih =>
      intro h2
      rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨b', hstep', h2'⟩
      · exact Or.inr (Relation.ReflTransGen.head hstep h1')
      · have hbb : b = b' := hstep_det a b b' hstep hstep'
        subst hbb
        exact ih h2'
  have hw_congr : ∀ (w : ℕ) (x y : Fin 7 → Bool),
      (∀ i : Fin 7, Reach i.val w → x i = y i) → wv D x w = wv D y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro x y hag
      by_cases hw : w < 7
      · rw [wv_input D x ⟨w, hw⟩, wv_input D y ⟨w, hw⟩]
        exact hag ⟨w, hw⟩ Relation.ReflTransGen.refl
      · by_cases hge : 7 + D.size ≤ w
        · rw [wv_ge D x w hge, wv_ge D y w hge]
        · obtain ⟨k, rfl⟩ : ∃ k, w = 7 + k := ⟨w - 7, by omega⟩
          have hk : k < D.size := by omega
          rw [wv_gate D x k hk, wv_gate D y k hk,
            eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1,
            eff_eval_eq _ (hDfan _ (List.getElem_mem hk)).1]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := heff_lt k hk u hu
          simp only [hult, ↓reduceIte]
          exact ih u hult x y (fun i hir => hag i (Relation.ReflTransGen.tail hir ⟨k, hk, rfl, hu⟩))

  have h5 : 5 < D.size := by omega
  have hout5 : D.output = 7 + 5 := by omega
  have hop5 := (hDfan D.gates[5] (List.getElem_mem h5)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop5
  have hbin5 : D.gates[5].op = GateOp.and ∨ D.gates[5].op = GateOp.or := by
    rcases hop5 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnoNot 5 h5 h).elim
  obtain ⟨p, q, hp, hq, hpq, heff5⟩ := (hgate_clean 5 h5).2 hbin5

  have hdisj_AB : ∀ i : Fin 7, ¬ (Reach i.val p ∧ Reach i.val q) := by
    rintro i ⟨hrp, hrq⟩
    rcases hreach_total i.val p q hrp hrq with hpqr | hqpr
    · rcases Relation.ReflTransGen.cases_head hpqr with rfl | ⟨y, hpy, hyq⟩
      · exact hpq rfl
      · have hyeq : y = 7 + 5 := hstep_det p y (7 + 5) hpy ⟨5, h5, rfl, by rw [heff5]; simp⟩
        subst hyeq; have := hReach_le (7 + 5) q hyq; omega
    · rcases Relation.ReflTransGen.cases_head hqpr with rfl | ⟨y, hqy, hyp⟩
      · exact hpq rfl
      · have hyeq : y = 7 + 5 := hstep_det q y (7 + 5) hqy ⟨5, h5, rfl, by rw [heff5]; simp⟩
        subst hyeq; have := hReach_le (7 + 5) p hyp; omega

  have hcover_AB : ∀ i : Fin 7, Reach i.val p ∨ Reach i.val q := by
    intro i
    have hreach_out : Reach i.val (7 + 5) := by
      by_contra hnr
      obtain ⟨y, hy⟩ := hfun_ess i
      apply hy
      rw [← hDeval, ← hDeval]
      change wv D _ D.output = wv D _ D.output
      rw [hout5]
      apply hw_congr (7 + 5)
      intro j hj
      have hji : j ≠ i := fun h => hnr (h ▸ hj)
      simp [hji]
    rcases Relation.ReflTransGen.cases_tail hreach_out with heq | ⟨u, hiu, hu5⟩
    · have := i.isLt; omega
    · obtain ⟨k, hk, hkeq, huin⟩ := hu5
      have hk5 : k = 5 := by omega
      subst hk5
      rw [heff5] at huin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at huin
      rcases huin with rfl | rfl
      · exact Or.inl hiu
      · exact Or.inr hiu

  have hp_nonconst : ¬ IsConst (fun (y : Fin 7 → Bool) => wv D y p) := by
    rintro ⟨c, hc⟩
    apply hno_drop 5 h5
    rcases hbin5 with hand | hor
    · cases c
      · left; refine ⟨false, fun y => ?_⟩
        dsimp only; rw [wv_gate D y 5 h5, eff_eval_eq _ (by simp [hand]), heff5, hand]
        simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_and2, hc y, Bool.false_and]
      · right; refine ⟨q, hq, fun y => ?_⟩
        dsimp only; rw [wv_gate D y 5 h5, eff_eval_eq _ (by simp [hand]), heff5, hand]
        simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_and2, hc y, Bool.true_and]
    · cases c
      · right; refine ⟨q, hq, fun y => ?_⟩
        dsimp only; rw [wv_gate D y 5 h5, eff_eval_eq _ (by simp [hor]), heff5, hor]
        simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_or2, hc y, Bool.false_or]
      · left; refine ⟨true, fun y => ?_⟩
        dsimp only; rw [wv_gate D y 5 h5, eff_eval_eq _ (by simp [hor]), heff5, hor]
        simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_or2, hc y, Bool.true_or]

  have hq_nonconst : ¬ IsConst (fun (y : Fin 7 → Bool) => wv D y q) := by
    rintro ⟨c, hc⟩
    apply hno_drop 5 h5
    rcases hbin5 with hand | hor
    · cases c
      · left; refine ⟨false, fun y => ?_⟩
        dsimp only; rw [wv_gate D y 5 h5, eff_eval_eq _ (by simp [hand]), heff5, hand]
        simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_and2, hc y, Bool.and_false]
      · right; refine ⟨p, hp, fun y => ?_⟩
        dsimp only; rw [wv_gate D y 5 h5, eff_eval_eq _ (by simp [hand]), heff5, hand]
        simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_and2, hc y, Bool.and_true]
    · cases c
      · right; refine ⟨p, hp, fun y => ?_⟩
        dsimp only; rw [wv_gate D y 5 h5, eff_eval_eq _ (by simp [hor]), heff5, hor]
        simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_or2, hc y, Bool.or_false]
      · left; refine ⟨true, fun y => ?_⟩
        dsimp only; rw [wv_gate D y 5 h5, eff_eval_eq _ (by simp [hor]), heff5, hor]
        simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_or2, hc y, Bool.or_true]

  have hp_zero : wv D (fun _ : Fin 7 => false) p = false := by
    cases h0 : wv D (fun _ : Fin 7 => false) p
    · rfl
    · exfalso; apply hp_nonconst; refine ⟨true, fun y => ?_⟩
      have hle := hmono (fun _ : Fin 7 => false) y (fun _ => Bool.false_le _) p
      rw [h0] at hle; cases h1 : wv D y p
      · rw [h1] at hle; exact absurd hle (by decide)
      · exact h1

  have hq_zero : wv D (fun _ : Fin 7 => false) q = false := by
    cases h0 : wv D (fun _ : Fin 7 => false) q
    · rfl
    · exfalso; apply hq_nonconst; refine ⟨true, fun y => ?_⟩
      have hle := hmono (fun _ : Fin 7 => false) y (fun _ => Bool.false_le _) q
      rw [h0] at hle; cases h1 : wv D y q
      · rw [h1] at hle; exact absurd hle (by decide)
      · exact h1

  have hA_nonempty : ∃ i : Fin 7, Reach i.val p := by
    by_contra hno
    push Not at hno
    apply hp_nonconst
    refine ⟨wv D (fun _ : Fin 7 => false) p, fun y => ?_⟩
    exact hw_congr p y (fun _ : Fin 7 => false) (fun i hi => (hno i hi).elim)

  have hB_nonempty : ∃ i : Fin 7, Reach i.val q := by
    by_contra hno
    push Not at hno
    apply hq_nonconst
    refine ⟨wv D (fun _ : Fin 7 => false) q, fun y => ?_⟩
    exact hw_congr q y (fun _ : Fin 7 => false) (fun i hi => (hno i hi).elim)

  rcases hbin5 with hand | hor
  · have hh_and : ∀ y, hfun y = (wv D y p && wv D y q) := fun y => by
      rw [← hDeval y]
      change wv D y D.output = _
      rw [hout5, wv_gate D y 5 h5, eff_eval_eq _ (by simp [hand]), heff5, hand]
      simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_and2]
    have hhit_A : ∀ y : Fin 7 → Bool, hfun y = true → ∃ i : Fin 7, Reach i.val p ∧ y i = true := by
      intro y hy
      rw [hh_and, Bool.and_eq_true] at hy
      by_contra hno
      push Not at hno
      have heq : wv D y p = wv D (fun _ => false) p :=
        hw_congr p y (fun _ => false) (fun i hi => by
          cases hyi : y i
          · rfl
          · exact (hno i hi hyi).elim)
      rw [hp_zero] at heq
      rw [heq] at hy
      exact absurd hy.1 (by decide)
    have hhit_B : ∀ y : Fin 7 → Bool, hfun y = true → ∃ i : Fin 7, Reach i.val q ∧ y i = true := by
      intro y hy
      rw [hh_and, Bool.and_eq_true] at hy
      by_contra hno
      push Not at hno
      have heq : wv D y q = wv D (fun _ => false) q :=
        hw_congr q y (fun _ => false) (fun i hi => by
          cases hyi : y i
          · rfl
          · exact (hno i hi hyi).elim)
      rw [hq_zero] at heq
      rw [heq] at hy
      exact absurd hy.2 (by decide)
    have hmix : ∀ y₁ y₂ : Fin 7 → Bool, hfun y₁ = true → hfun y₂ = true →
        hfun (fun i => if Reach i.val p then y₁ i else y₂ i) = true := by
      intro y₁ y₂ hy₁ hy₂
      rw [hh_and, Bool.and_eq_true] at hy₁ hy₂ ⊢
      constructor
      · rw [← hy₁.1]; exact hw_congr p _ y₁ (fun i hi => by simp only [hi, ↓reduceIte])
      · rw [← hy₂.2]; exact hw_congr q _ y₂ (fun i hi => by
          have hnp : ¬ Reach i.val p := fun hp' => hdisj_AB i ⟨hp', hi⟩
          simp only [hnp, ↓reduceIte])
    let m1 : Fin 7 → Bool := fun i => i == 3 || i == 5
    let m2 : Fin 7 → Bool := fun i => i == 0 || i == 2 || i == 6
    have hm1 : hfun m1 = true := by decide
    have hm2 : hfun m2 = true := by decide
    obtain ⟨i1, hi1p, hm1i1⟩ := hhit_A m1 hm1
    obtain ⟨j1, hj1q, hm1j1⟩ := hhit_B m1 hm1
    have h35 : (Reach (3 : Fin 7).val p ∧ Reach (5 : Fin 7).val q) ∨
        (Reach (5 : Fin 7).val p ∧ Reach (3 : Fin 7).val q) := by
      have hi1_35 : i1 = 3 ∨ i1 = 5 := by
        simpa only [m1, Bool.or_eq_true, beq_iff_eq] using hm1i1
      have hj1_35 : j1 = 3 ∨ j1 = 5 := by
        simpa only [m1, Bool.or_eq_true, beq_iff_eq] using hm1j1
      rcases hi1_35 with rfl | rfl <;> rcases hj1_35 with rfl | rfl
      · exact (hdisj_AB 3 ⟨hi1p, hj1q⟩).elim
      · exact Or.inl ⟨hi1p, hj1q⟩
      · exact Or.inr ⟨hi1p, hj1q⟩
      · exact (hdisj_AB 5 ⟨hi1p, hj1q⟩).elim
    rcases h35 with ⟨h3p, h5q⟩ | ⟨h5p, h3q⟩
    · have hz := hmix m1 m2 hm1 hm2
      obtain ⟨ia, hiap, hm2ia⟩ := hhit_A m2 hm2
      have hia_026 : ia = 0 ∨ ia = 2 ∨ ia = 6 := by
        simp only [m2, Bool.or_eq_true, beq_iff_eq] at hm2ia
        rcases hm2ia with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      let z : Fin 7 → Bool := fun i => if Reach i.val p then m1 i else m2 i
      have hz1 : z 1 = false := by simp only [z]; split_ifs <;> rfl
      have hz4 : z 4 = false := by simp only [z]; split_ifs <;> rfl
      have hz5 : z 5 = false := by
        have h5np : ¬ Reach (5 : Fin 7).val p := fun hp' => hdisj_AB 5 ⟨hp', h5q⟩
        simp only [z, h5np, ↓reduceIte]; rfl
      have hzia : z ia = false := by
        simp only [z, hiap, ↓reduceIte]
        rcases hia_026 with rfl | rfl | rfl <;> rfl
      have hzf : hfun z = false := by
        unfold hfun
        rw [hz1, hz4, hz5]
        rcases hia_026 with rfl | rfl | rfl <;> rw [hzia] <;> simp
      rw [hzf] at hz; exact absurd hz (by decide)
    · have hz := hmix m2 m1 hm2 hm1
      obtain ⟨ib, hibq, hm2ib⟩ := hhit_B m2 hm2
      have hib_026 : ib = 0 ∨ ib = 2 ∨ ib = 6 := by
        simp only [m2, Bool.or_eq_true, beq_iff_eq] at hm2ib
        rcases hm2ib with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      let z : Fin 7 → Bool := fun i => if Reach i.val p then m2 i else m1 i
      have hz1 : z 1 = false := by simp only [z]; split_ifs <;> rfl
      have hz4 : z 4 = false := by simp only [z]; split_ifs <;> rfl
      have hz5 : z 5 = false := by simp only [z, h5p, ↓reduceIte]; rfl
      have hzib : z ib = false := by
        have hibnp : ¬ Reach ib.val p := fun hp' => hdisj_AB ib ⟨hp', hibq⟩
        simp only [z, hibnp, ↓reduceIte]
        rcases hib_026 with rfl | rfl | rfl <;> rfl
      have hzf : hfun z = false := by
        unfold hfun
        rw [hz1, hz4, hz5]
        rcases hib_026 with rfl | rfl | rfl <;> rw [hzib] <;> simp
      rw [hzf] at hz; exact absurd hz (by decide)
  · have hh_or : ∀ y, hfun y = (wv D y p || wv D y q) := fun y => by
      rw [← hDeval y]
      change wv D y D.output = _
      rw [hout5, wv_gate D y 5 h5, eff_eval_eq _ (by simp [hor]), heff5, hor]
      simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte, eval_or2]
    have hprime : ∀ y : Fin 7 → Bool, hfun y = true →
        (∀ i : Fin 7, y i = true → hfun (Function.update y i false) = false) →
        (∀ i : Fin 7, y i = true → Reach i.val p) ∨ (∀ i : Fin 7, y i = true → Reach i.val q) := by
      intro y hy hmin
      rw [hh_or, Bool.or_eq_true] at hy
      rcases hy with hyp | hyq
      · left
        intro i hyi
        by_contra hnp
        have hle : ∀ j : Fin 7, (if Reach j.val p then y j else false) ≤ Function.update y i false j := by
          intro j
          by_cases hji : j = i
          · subst hji; simp [hnp]
          · simp only [Function.update_of_ne hji]; split_ifs <;> simp
        have hres_t : hfun (fun j => if Reach j.val p then y j else false) = true := by
          rw [hh_or, Bool.or_eq_true]; left
          rw [← hyp]; exact hw_congr p _ y (fun j hj => by simp only [hj, ↓reduceIte])
        have hmon : hfun (fun j => if Reach j.val p then y j else false) ≤ hfun (Function.update y i false) := by
          rw [← hDeval, ← hDeval]; exact hmono _ _ hle D.output
        rw [hres_t, hmin i hyi] at hmon
        exact absurd hmon (by decide)
      · right
        intro i hyi
        by_contra hnq
        have hle : ∀ j : Fin 7, (if Reach j.val q then y j else false) ≤ Function.update y i false j := by
          intro j
          by_cases hji : j = i
          · subst hji; simp [hnq]
          · simp only [Function.update_of_ne hji]; split_ifs <;> simp
        have hres_t : hfun (fun j => if Reach j.val q then y j else false) = true := by
          rw [hh_or, Bool.or_eq_true]; right
          rw [← hyq]; exact hw_congr q _ y (fun j hj => by simp only [hj, ↓reduceIte])
        have hmon : hfun (fun j => if Reach j.val q then y j else false) ≤ hfun (Function.update y i false) := by
          rw [← hDeval, ← hDeval]; exact hmono _ _ hle D.output
        rw [hres_t, hmin i hyi] at hmon
        exact absurd hmon (by decide)
    have hp1 := hprime (fun i => i == 3 || i == 5) (by decide) (by decide)
    have hp2 := hprime (fun i => i == 0 || i == 2 || i == 6) (by decide) (by decide)
    have hp3 := hprime (fun i => i == 0 || i == 3 || i == 4) (by decide) (by decide)
    have hp4 := hprime (fun i => i == 1 || i == 2 || i == 5) (by decide) (by decide)
    have hall : (∀ i : Fin 7, Reach i.val p) ∨ (∀ i : Fin 7, Reach i.val q) := by
      rcases hp1 with h1p | h1q
      · have h3p : Reach (3 : Fin 7).val p := h1p 3 (by decide)
        have h5p : Reach (5 : Fin 7).val p := h1p 5 (by decide)
        have h3_p : ∀ i : Fin 7, (i == 0 || i == 3 || i == 4) = true → Reach i.val p :=
          hp3.resolve_right (fun h => hdisj_AB 3 ⟨h3p, h 3 (by decide)⟩)
        have h4_p : ∀ i : Fin 7, (i == 1 || i == 2 || i == 5) = true → Reach i.val p :=
          hp4.resolve_right (fun h => hdisj_AB 5 ⟨h5p, h 5 (by decide)⟩)
        have h2_p : ∀ i : Fin 7, (i == 0 || i == 2 || i == 6) = true → Reach i.val p :=
          hp2.resolve_right (fun h => hdisj_AB 0 ⟨h3_p 0 (by decide), h 0 (by decide)⟩)
        left; intro i; fin_cases i
        · exact h3_p 0 (by decide)
        · exact h4_p 1 (by decide)
        · exact h4_p 2 (by decide)
        · exact h3p
        · exact h3_p 4 (by decide)
        · exact h5p
        · exact h2_p 6 (by decide)
      · have h3q : Reach (3 : Fin 7).val q := h1q 3 (by decide)
        have h5q : Reach (5 : Fin 7).val q := h1q 5 (by decide)
        have h3_q : ∀ i : Fin 7, (i == 0 || i == 3 || i == 4) = true → Reach i.val q :=
          hp3.resolve_left (fun h => hdisj_AB 3 ⟨h 3 (by decide), h3q⟩)
        have h4_q : ∀ i : Fin 7, (i == 1 || i == 2 || i == 5) = true → Reach i.val q :=
          hp4.resolve_left (fun h => hdisj_AB 5 ⟨h 5 (by decide), h5q⟩)
        have h2_q : ∀ i : Fin 7, (i == 0 || i == 2 || i == 6) = true → Reach i.val q :=
          hp2.resolve_left (fun h => hdisj_AB 0 ⟨h 0 (by decide), h3_q 0 (by decide)⟩)
        right; intro i; fin_cases i
        · exact h3_q 0 (by decide)
        · exact h4_q 1 (by decide)
        · exact h4_q 2 (by decide)
        · exact h3q
        · exact h3_q 4 (by decide)
        · exact h5q
        · exact h2_q 6 (by decide)
    rcases hall with hallp | hallq
    · obtain ⟨i, hiq⟩ := hB_nonempty; exact hdisj_AB i ⟨hallp i, hiq⟩
    · obtain ⟨i, hip⟩ := hA_nonempty; exact hdisj_AB i ⟨hip, hallq i⟩

lemma main_proof : ¬ (∃ C : Circuit,
    FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨
          (C.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨GateOp.and, [2, 9]⟩) := by
  classical
  rintro ⟨C, hfan, hsize, heval, hout, hstruct, _, hlive, hg0, hg1⟩
  obtain ⟨g0, g1, gs_rest, hgates⟩ : ∃ g0 g1 rest, C.gates = g0 :: g1 :: rest := by
    cases h : C.gates with
    | nil => simp [h] at hg0
    | cons a tl =>
      cases h2 : tl with
      | nil => simp [h, h2] at hg1
      | cons b rest => exact ⟨a, b, rest, rfl⟩
  have hg0_eq : g0 = ⟨GateOp.and, [0, 4]⟩ := by simpa [hgates] using hg0
  have hg1_eq : g1 = ⟨GateOp.and, [2, 9]⟩ := by simpa [hgates] using hg1
  subst hg0_eq; subst hg1_eq
  have hCsz : C.size = C.gates.length := rfl
  have hlen_ge2 : 2 ≤ C.size := by rw [hCsz]; simp [hgates]

  have hin_lt : ∀ (k : ℕ) (hk : k < C.gates.length) (u : ℕ), u ∈ C.gates[k].inputs → u < 9 + k := by
    intro k hk u hu
    rcases hstruct ⟨k, hk⟩ with ⟨_, a, ha, hins⟩ | ⟨_, a, b, hab, hb, hins⟩
    · rw [List.get_eq_getElem] at hins; change C.gates[k].inputs = [a] at hins
      dsimp only at ha; rw [hins] at hu; simp at hu; omega
    · rw [List.get_eq_getElem] at hins; change C.gates[k].inputs = [a, b] at hins
      dsimp only at hb; rw [hins] at hu; simp at hu; rcases hu with rfl | rfl <;> omega

  have hw9_eq : ∀ x : Fin 9 → Bool, wv C x 9 = (x 0 && x 4) := fun x => by
    have h := wv_gate C x 0 (by omega)
    have h0 : wv C x 0 = x 0 := wv_input C x 0
    have h4 : wv C x 4 = x 4 := wv_input C x 4
    simp only [hgates, List.getElem_cons_zero] at h
    simpa [eval_and2, h0, h4] using h

  have hw10_eq : ∀ x : Fin 9 → Bool, wv C x 10 = (x 2 && (x 0 && x 4)) := fun x => by
    have h := wv_gate C x 1 (by omega)
    have h2 : wv C x 2 = x 2 := wv_input C x 2
    simp only [hgates, List.getElem_cons_succ, List.getElem_cons_zero] at h
    simpa [eval_and2, h2, hw9_eq x] using h

  have hlen_ge3 : 3 ≤ C.size := by
    by_contra hlt
    have hsz2 : C.size = 2 := by omega
    have hout10 : C.output = 10 := by omega
    have h1 := heval (embed (fun _ => true))
    change wv C (embed (fun _ => true)) C.output = _ at h1
    rw [hout10, hw10_eq, pm3_embed] at h1
    exact absurd h1 (by decide)

  have hread10 : ∃ k, ∃ hk : k < C.gates.length, 2 ≤ k ∧ 10 ∈ C.gates[k].inputs := by
    obtain ⟨k, hgt, hin⟩ := hlive ⟨1, by omega⟩ (by dsimp; omega)
    dsimp only at hgt
    exact ⟨k.val, k.isLt, by omega, by simpa [List.get_eq_getElem] using hin⟩

  have hread0 : ∃ k, ∃ hk : k < C.gates.length, 2 ≤ k ∧ 0 ∈ C.gates[k].inputs := by
    by_contra hno
    push Not at hno
    let a : Fin 9 → Bool := fun i => i == 5 || i == 7
    let b : Fin 9 → Bool := fun i => i == 0 || i == 5 || i == 7
    have hsame : ∀ w, w ≠ 0 → wv C a w = wv C b w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hne
        by_cases hw : w < 9
        · rw [wv_input C a ⟨w, hw⟩, wv_input C b ⟨w, hw⟩]
          have hne0 : (⟨w, hw⟩ : Fin 9) ≠ 0 := fun h => hne (congrArg Fin.val h)
          have h0 : ((⟨w, hw⟩ : Fin 9) == 0) = false := beq_false_of_ne hne0
          simp only [a, b, h0, Bool.false_or]
        · by_cases hge : 9 + C.size ≤ w
          · rw [wv_ge C a w hge, wv_ge C b w hge]
          · obtain ⟨k, rfl⟩ : ∃ k, w = 9 + k := ⟨w - 9, by omega⟩
            have hk : k < C.size := by omega
            have hk' : k < C.gates.length := by omega
            by_cases hk0 : k = 0
            · subst hk0; rw [hw9_eq, hw9_eq]; decide
            · by_cases hk1 : k = 1
              · subst hk1; rw [hw10_eq, hw10_eq]; decide
              · rw [wv_gate C a k hk, wv_gate C b k hk]
                congr 1
                apply List.map_congr_left
                intro u hu
                have hult := hin_lt k hk' u hu
                simp only [hult, ↓reduceIte]
                exact ih u hult (fun h => hno k hk' (by omega) (h ▸ hu))
    have heq : pm3 a = pm3 b := by
      rw [← heval a, ← heval b]
      exact hsame C.output (by omega)
    exact absurd heq (by decide)

  have hread4 : ∃ k, ∃ hk : k < C.gates.length, 2 ≤ k ∧ 4 ∈ C.gates[k].inputs := by
    by_contra hno
    push Not at hno
    let a : Fin 9 → Bool := fun i => i == 2 || i == 6
    let b : Fin 9 → Bool := fun i => i == 2 || i == 4 || i == 6
    have hsame : ∀ w, w ≠ 4 → wv C a w = wv C b w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hne
        by_cases hw : w < 9
        · rw [wv_input C a ⟨w, hw⟩, wv_input C b ⟨w, hw⟩]
          have hne4 : (⟨w, hw⟩ : Fin 9) ≠ 4 := fun h => hne (congrArg Fin.val h)
          have h4 : ((⟨w, hw⟩ : Fin 9) == 4) = false := beq_false_of_ne hne4
          simp only [a, b, h4, Bool.or_false]
        · by_cases hge : 9 + C.size ≤ w
          · rw [wv_ge C a w hge, wv_ge C b w hge]
          · obtain ⟨k, rfl⟩ : ∃ k, w = 9 + k := ⟨w - 9, by omega⟩
            have hk : k < C.size := by omega
            have hk' : k < C.gates.length := by omega
            by_cases hk0 : k = 0
            · subst hk0; rw [hw9_eq, hw9_eq]; decide
            · by_cases hk1 : k = 1
              · subst hk1; rw [hw10_eq, hw10_eq]; decide
              · rw [wv_gate C a k hk, wv_gate C b k hk]
                congr 1
                apply List.map_congr_left
                intro u hu
                have hult := hin_lt k hk' u hu
                simp only [hult, ↓reduceIte]
                exact ih u hult (fun h => hno k hk' (by omega) (h ▸ hu))
    have heq : pm3 a = pm3 b := by
      rw [← heval a, ← heval b]
      exact hsame C.output (by omega)
    exact absurd heq (by decide)

  let F : ℕ → (Fin 7 → Bool) → Bool := fun w y => wv C (embed y) w
  have hFout : ∀ y, F C.output y = hfun y := fun y => (heval (embed y)).trans (pm3_embed y)
  have hF0 : ∀ y, F 0 y = true := fun y => by
    change wv C (embed y) (0 : Fin 9).val = true; rw [wv_input]; rfl
  have hF4 : ∀ y, F 4 y = false := fun y => by
    change wv C (embed y) (4 : Fin 9).val = false; rw [wv_input]; rfl
  have hF9 : ∀ y, F 9 y = false := fun y => by dsimp only [F]; rw [hw9_eq]; simp [embed]
  have hF10 : ∀ y, F 10 y = false := fun y => by dsimp only [F]; rw [hw10_eq]; simp [embed]

  let Cconst : Finset ℕ := (Finset.range (9 + C.size)).filter (fun w => IsConst (F w))
  let Dconst : Finset ℕ := (Finset.range C.size).filter (fun g => 2 ≤ g ∧ 9 + g ∈ Cconst)
  let Sdrop : Finset ℕ := (Finset.range C.size).filter (fun g =>
    2 ≤ g ∧ (g ∈ Dconst ∨ ∃ u ∈ Cconst, if hg : g < C.gates.length then u ∈ C.gates[g].inputs else false))
  let K : Finset ℕ := {0, 4, 10} ∪ Dconst.image (9 + ·)

  have h0C : 0 ∈ Cconst := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), true, hF0⟩
  have h4C : 4 ∈ Cconst := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), false, hF4⟩
  have h10C : 10 ∈ Cconst := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), false, hF10⟩
  have hKC : K ⊆ Cconst := by
    intro u hu
    rcases Finset.mem_union.mp hu with h1 | h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with rfl | rfl | rfl
      · exact h0C
      · exact h4C
      · exact h10C
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h2
      exact (Finset.mem_filter.mp hd).2.2
  have hKcard : K.card = 3 + Dconst.card := by
    have hdisj : Disjoint ({0, 4, 10} : Finset ℕ) (Dconst.image (9 + ·)) := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h2
      have hd2 := (Finset.mem_filter.mp hd).2.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      omega
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => by omega)]
    rfl
  have hDsubS : Dconst ⊆ Sdrop := fun g hg => by
    have hg' := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨hg'.1, hg'.2.1, Or.inl hg⟩

  have hK_read : ∀ u ∈ K, ∃ g ∈ Sdrop, if hg : g < C.gates.length then u ∈ C.gates[g].inputs else false := by
    intro u hu
    rcases Finset.mem_union.mp hu with h1 | h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with rfl | rfl | rfl
      · obtain ⟨k, hk, hk2, hkin⟩ := hread0
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hk2, Or.inr ⟨0, h0C, by simp only [hk, ↓reduceDIte]; exact hkin⟩⟩,
          by simp only [hk, ↓reduceDIte]; exact hkin⟩
      · obtain ⟨k, hk, hk2, hkin⟩ := hread4
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hk2, Or.inr ⟨4, h4C, by simp only [hk, ↓reduceDIte]; exact hkin⟩⟩,
          by simp only [hk, ↓reduceDIte]; exact hkin⟩
      · obtain ⟨k, hk, hk2, hkin⟩ := hread10
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hk2, Or.inr ⟨10, h10C, by simp only [hk, ↓reduceDIte]; exact hkin⟩⟩,
          by simp only [hk, ↓reduceDIte]; exact hkin⟩
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h2
      have hd_m := Finset.mem_filter.mp hd
      have hdlt : d < C.gates.length := Finset.mem_range.mp hd_m.1
      have hd2 : 2 ≤ d := hd_m.2.1
      have hdC : 9 + d ∈ Cconst := hd_m.2.2
      have hd_not_last : d + 1 < C.gates.length := by
        by_contra hge
        have heq : 9 + d = C.output := by omega
        have hc : IsConst (F (9 + d)) := (Finset.mem_filter.mp hdC).2
        rw [heq] at hc
        apply hfun_nonconst
        have : F C.output = hfun := funext hFout
        rwa [← this]
      obtain ⟨k, hdk, hkin⟩ := hlive ⟨d, hdlt⟩ hd_not_last
      dsimp only at hdk
      have hkin' : 9 + d ∈ C.gates[k.val].inputs := by simpa [List.get_eq_getElem] using hkin
      exact ⟨k.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, by omega,
        Or.inr ⟨9 + d, hdC, by simp only [k.isLt, ↓reduceDIte]; exact hkin'⟩⟩,
        by simp only [k.isLt, ↓reduceDIte]; exact hkin'⟩

  have hSdrop_ge3 : 3 ≤ Sdrop.card := by
    let inK (g : ℕ) : Finset ℕ := K.filter (fun u => if hg : g < C.gates.length then u ∈ C.gates[g].inputs else false)
    have hlow : K.card ≤ ∑ g ∈ Sdrop, (inK g).card := by
      have hswap : ∑ u ∈ K, (Sdrop.filter (fun g => if hg : g < C.gates.length then u ∈ C.gates[g].inputs else false)).card =
          ∑ g ∈ Sdrop, (inK g).card := by
        simp only [inK, Finset.card_filter]
        rw [Finset.sum_comm]
      rw [← hswap]
      have h1 : ∀ u ∈ K, 1 ≤ (Sdrop.filter (fun g => if hg : g < C.gates.length then u ∈ C.gates[g].inputs else false)).card := fun u hu => by
        obtain ⟨g, hg, hgin⟩ := hK_read u hu
        exact Finset.card_pos.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hgin⟩⟩
      calc K.card = ∑ _u ∈ K, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum h1
    have hhi_D : ∀ g ∈ Dconst, (inK g).card ≤ 2 := by
      intro g hg
      have hglt : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
      have hsub : inK g ⊆ C.gates[g].inputs.toFinset := by
        intro u hu
        have hu' := (Finset.mem_filter.mp hu).2
        simp only [hglt, ↓reduceDIte] at hu'
        exact List.mem_toFinset.mpr hu'
      calc (inK g).card ≤ C.gates[g].inputs.toFinset.card := Finset.card_le_card hsub
        _ ≤ C.gates[g].inputs.length := List.toFinset_card_le _
        _ ≤ 2 := (hfan C.gates[g] (List.getElem_mem hglt)).2
    have hhi_notD : ∀ g ∈ Sdrop \ Dconst, (inK g).card ≤ 1 := by
      intro g hg
      have hgS := (Finset.mem_sdiff.mp hg).1
      have hgnD := (Finset.mem_sdiff.mp hg).2
      have hglt : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hgS).1
      have hg2 : 2 ≤ g := (Finset.mem_filter.mp hgS).2.1
      by_contra hgt1
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < (inK g).card)
      have huK := (Finset.mem_filter.mp hu).1
      have hvK := (Finset.mem_filter.mp hv).1
      have huin := (Finset.mem_filter.mp hu).2
      have hvin := (Finset.mem_filter.mp hv).2
      simp only [hglt, ↓reduceDIte] at huin hvin
      have huC : IsConst (F u) := (Finset.mem_filter.mp (hKC huK)).2
      have hvC : IsConst (F v) := (Finset.mem_filter.mp (hKC hvK)).2
      obtain ⟨cu, hcu⟩ := huC
      obtain ⟨cv, hcv⟩ := hvC
      have hg_const : IsConst (F (9 + g)) := by
        rcases hstruct ⟨g, hglt⟩ with ⟨_, a, _, hins⟩ | ⟨hbin, a, b, hab, hb, hins⟩
        · simp only [List.get_eq_getElem] at hins
          rw [hins] at huin hvin; simp at huin hvin; exact (huv (huin.trans hvin.symm)).elim
        · simp only [List.get_eq_getElem] at hins hbin; dsimp only at hb
          rw [hins] at huin hvin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at huin hvin
          have ha_c : ∃ ca, ∀ y, F a y = ca := by
            rcases huin with rfl | rfl
            · exact ⟨cu, hcu⟩
            · rcases hvin with rfl | rfl
              · exact ⟨cv, hcv⟩
              · exact (huv rfl).elim
          have hb_c : ∃ cb, ∀ y, F b y = cb := by
            rcases huin with rfl | rfl
            · rcases hvin with rfl | rfl
              · exact (huv rfl).elim
              · exact ⟨cv, hcv⟩
            · exact ⟨cu, hcu⟩
          obtain ⟨ca, hca⟩ := ha_c
          obtain ⟨cb, hcb⟩ := hb_c
          rcases hbin with hand | hor
          · refine ⟨ca && cb, fun y => ?_⟩
            dsimp only [F]; rw [wv_gate C (embed y) g hglt, hand, hins]
            simp only [List.map_cons, List.map_nil, show a < 9 + g by omega, hb, ↓reduceIte, eval_and2]
            change (F a y && F b y) = _; rw [hca y, hcb y]
          · refine ⟨ca || cb, fun y => ?_⟩
            dsimp only [F]; rw [wv_gate C (embed y) g hglt, hor, hins]
            simp only [List.map_cons, List.map_nil, show a < 9 + g by omega, hb, ↓reduceIte, eval_or2]
            change (F a y || F b y) = _; rw [hca y, hcb y]
      exact hgnD (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hglt, hg2,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hg_const⟩⟩)
    have hsum_hi : ∑ g ∈ Sdrop, (inK g).card ≤ Sdrop.card + Dconst.card := by
      rw [← Finset.sum_sdiff hDsubS]
      have h1 : ∑ g ∈ Sdrop \ Dconst, (inK g).card ≤ (Sdrop \ Dconst).card :=
        calc ∑ g ∈ Sdrop \ Dconst, (inK g).card ≤ ∑ _g ∈ Sdrop \ Dconst, 1 := Finset.sum_le_sum hhi_notD
          _ = (Sdrop \ Dconst).card := by simp
      have h2 : ∑ g ∈ Dconst, (inK g).card ≤ 2 * Dconst.card :=
        calc ∑ g ∈ Dconst, (inK g).card ≤ ∑ _g ∈ Dconst, 2 := Finset.sum_le_sum hhi_D
          _ = 2 * Dconst.card := by simp [mul_comm]
      have hcard_sdiff : (Sdrop \ Dconst).card + Dconst.card = Sdrop.card := by
        have := Finset.card_sdiff (s := Dconst) (t := Sdrop)
        rw [Finset.inter_eq_left.mpr hDsubS] at this
        have hle := Finset.card_le_card hDsubS
        omega
      omega
    omega

  let Dropped : Finset ℕ := {0, 1} ∪ Sdrop
  have hDrop_sub : Dropped ⊆ Finset.range C.size := by
    intro j hj
    rcases Finset.mem_union.mp hj with h1 | h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    · exact (Finset.mem_filter.mp h2).1
  have hDrop_card : 5 ≤ Dropped.card := by
    have hdisj : Disjoint ({0, 1} : Finset ℕ) Sdrop := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      have hj2 := (Finset.mem_filter.mp h2).2.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      omega
    rw [Finset.card_union_of_disjoint hdisj]
    have h01 : ({0, 1} : Finset ℕ).card = 2 := by decide
    omega
  have hDrop_drops : ∀ j ∈ Dropped, Drops 9 F j := by
    intro j hj
    rcases Finset.mem_union.mp hj with h1 | h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with rfl | rfl
      · exact Or.inl ⟨false, hF9⟩
      · exact Or.inl ⟨false, hF10⟩
    · have hj' := Finset.mem_filter.mp h2
      have hjlt : j < C.gates.length := Finset.mem_range.mp hj'.1
      rcases hj'.2.2 with hD | ⟨u, huC, huin⟩
      · exact Or.inl (Finset.mem_filter.mp (Finset.mem_filter.mp hD).2.2).2
      · simp only [hjlt, ↓reduceDIte] at huin
        obtain ⟨cu, hcu⟩ := (Finset.mem_filter.mp huC).2
        rcases hstruct ⟨j, hjlt⟩ with ⟨hnot, a, ha, hins⟩ | ⟨hbin, a, b, hab, hb, hins⟩
        · simp only [List.get_eq_getElem] at hnot hins; dsimp only at ha
          rw [hins, List.mem_singleton] at huin; subst huin
          left; refine ⟨!cu, fun y => ?_⟩
          dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hnot, hins]
          simp only [List.map_cons, List.map_nil, ha, ↓reduceIte, eval_not1]
          change (!(F u y)) = !cu; rw [hcu y]
        · simp only [List.get_eq_getElem] at hbin hins; dsimp only at hb
          rw [hins] at huin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at huin
          rcases hbin with hand | hor
          · rcases huin with rfl | rfl
            · cases cu
              · left; refine ⟨false, fun y => ?_⟩
                dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hand, hins]
                simp only [List.map_cons, List.map_nil, show u < 9 + j by omega, hb, ↓reduceIte, eval_and2]
                change (F u y && _) = false; rw [hcu y]; rfl
              · right; refine ⟨b, hb, fun y => ?_⟩
                dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hand, hins]
                simp only [List.map_cons, List.map_nil, show u < 9 + j by omega, hb, ↓reduceIte, eval_and2]
                change (F u y && F b y) = F b y; rw [hcu y]; rfl
            · cases cu
              · left; refine ⟨false, fun y => ?_⟩
                dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hand, hins]
                simp only [List.map_cons, List.map_nil, show a < 9 + j by omega, hb, ↓reduceIte, eval_and2]
                change (_ && F u y) = false; rw [hcu y]; simp
              · right; refine ⟨a, by omega, fun y => ?_⟩
                dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hand, hins]
                simp only [List.map_cons, List.map_nil, show a < 9 + j by omega, hb, ↓reduceIte, eval_and2]
                change (F a y && F u y) = F a y; rw [hcu y]; simp
          · rcases huin with rfl | rfl
            · cases cu
              · right; refine ⟨b, hb, fun y => ?_⟩
                dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hor, hins]
                simp only [List.map_cons, List.map_nil, show u < 9 + j by omega, hb, ↓reduceIte, eval_or2]
                change (F u y || F b y) = F b y; rw [hcu y]; rfl
              · left; refine ⟨true, fun y => ?_⟩
                dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hor, hins]
                simp only [List.map_cons, List.map_nil, show u < 9 + j by omega, hb, ↓reduceIte, eval_or2]
                change (F u y || _) = true; rw [hcu y]; rfl
            · cases cu
              · right; refine ⟨a, by omega, fun y => ?_⟩
                dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hor, hins]
                simp only [List.map_cons, List.map_nil, show a < 9 + j by omega, hb, ↓reduceIte, eval_or2]
                change (F a y || F u y) = F a y; rw [hcu y]; simp
              · left; refine ⟨true, fun y => ?_⟩
                dsimp only [F]; rw [wv_gate C (embed y) j hjlt, hor, hins]
                simp only [List.map_cons, List.map_nil, show a < 9 + j by omega, hb, ↓reduceIte, eval_or2]
                change (_ || F u y) = true; rw [hcu y]; simp

  have hin_F : ∀ i < 9, IsConst (F i) ∨ ∃ k < 7, ∀ y : Fin 7 → Bool, F i y = (List.ofFn y).getD k false := by
    intro i hi
    have hidx : ∀ (k : Fin 7) (j : Fin 9), (∀ y, embed y j = y k) →
        ∀ y : Fin 7 → Bool, F j.val y = (List.ofFn y).getD k.val false := fun k j h y =>
      (wv_input C (embed y) j).trans ((h y).trans (getD_ofFn y k.val k.isLt).symm)
    match i with
    | 0 => exact Or.inl ⟨true, hF0⟩
    | 1 => exact Or.inr ⟨0, by omega, hidx 0 1 (fun _ => rfl)⟩
    | 2 => exact Or.inr ⟨1, by omega, hidx 1 2 (fun _ => rfl)⟩
    | 3 => exact Or.inr ⟨2, by omega, hidx 2 3 (fun _ => rfl)⟩
    | 4 => exact Or.inl ⟨false, hF4⟩
    | 5 => exact Or.inr ⟨3, by omega, hidx 3 5 (fun _ => rfl)⟩
    | 6 => exact Or.inr ⟨4, by omega, hidx 4 6 (fun _ => rfl)⟩
    | 7 => exact Or.inr ⟨5, by omega, hidx 5 7 (fun _ => rfl)⟩
    | 8 => exact Or.inr ⟨6, by omega, hidx 6 8 (fun _ => rfl)⟩
    | i + 9 => omega

  obtain ⟨ds, S, h1, h2, h3, h4⟩ := restrict_build 9 7 C.gates hfan F hin_F
    (fun j hj y => wv_gate C (embed y) j hj) C.size le_rfl
  have hSsub : S ⊆ Finset.range C.size \ Dropped := by
    intro j hj
    have ⟨hlt, hnd⟩ := h2 j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hlt, fun hm => hnd (hDrop_drops j hm)⟩
  have hds_le6 : ds.length ≤ 6 := by
    have hcard := Finset.card_le_card hSsub
    have hsdiff := Finset.card_sdiff (s := Dropped) (t := Finset.range C.size)
    rw [Finset.inter_eq_left.mpr hDrop_sub, Finset.card_range] at hsdiff
    omega
  rcases h4 C.output (by omega) with hc | ⟨k, _, hk'⟩
  · apply hfun_nonconst
    have : F C.output = hfun := funext hFout
    rwa [← this]
  · exact no_circuit_le6 ⟨ds, k⟩ h1 hds_le6 (fun y => (hk' y).symm.trans (hFout y))

end PEqualNP.Outside.L_meta_27211

theorem PEqualNP.Outside.L_meta_27211 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩)) :=
  PEqualNP.Outside.L_meta_27211.main_proof
