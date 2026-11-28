import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1479_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

section Fold

variable {α : Type}

def sfold (F : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun W g => W ++ [F W g]) init

theorem sfold_length (F : List α → Gate → α) (init : List α) (gs : List Gate) :
    (sfold F init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [sfold]
  | cons g rest ih =>
    simp only [sfold, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

theorem sfold_old (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) {j : ℕ}
    (hj : j < init.length) : (sfold F init gs).getD j d = init.getD j d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [sfold, List.foldl_cons] at ih ⊢
    rw [ih (init ++ [F init g]) (by simp; omega)]
    exact List.getD_append _ _ _ _ hj

theorem sfold_append (F : List α → Gate → α) (init : List α) (gs1 gs2 : List Gate) :
    sfold F init (gs1 ++ gs2) = sfold F (sfold F init gs1) gs2 := by
  simp [sfold, List.foldl_append]

theorem sfold_at (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) (m : ℕ)
    (hm : m < gs.length) :
    (sfold F init gs).getD (init.length + m) d = F (sfold F init (gs.take m)) gs[m] := by
  have hsplit : gs.take m ++ (gs[m] :: gs.drop (m+1)) = gs := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hlen := sfold_length F init (gs.take m)
  rw [List.length_take, min_eq_left hm.le] at hlen
  conv_lhs => rw [← hsplit]
  rw [sfold_append]
  show (sfold F (sfold F init (gs.take m) ++ [F (sfold F init (gs.take m)) gs[m]])
    (gs.drop (m+1))).getD (init.length + m) d = _
  rw [sfold_old _ _ _ _ (by simp [hlen])]
  rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
  simp [hlen]

theorem sfold_gate (F : List α → Gate → α) (d : α)
    (hloc : ∀ W1 W2 g, (∀ j ∈ g.inputs, W1.getD j d = W2.getD j d) → F W1 g = F W2 g)
    (init : List α) (gs : List Gate)
    (hreads : ∀ m (hm : m < gs.length), ∀ j ∈ gs[m].inputs, j < init.length + m)
    (m : ℕ) (hm : m < gs.length) :
    (sfold F init gs).getD (init.length + m) d = F (sfold F init gs) gs[m] := by
  rw [sfold_at F init gs d m hm]
  apply hloc
  intro j hj
  have hjl := hreads m hm j hj
  have hfull : sfold F init gs = sfold F (sfold F init (gs.take m)) (gs.drop m) := by
    rw [← sfold_append, List.take_append_drop]
  rw [hfull]
  exact (sfold_old F (sfold F init (gs.take m)) (gs.drop m) d
    (by rw [sfold_length, List.length_take, min_eq_left hm.le]; exact hjl)).symm

theorem sfold_beyond (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) {j : ℕ}
    (hj : init.length + gs.length ≤ j) : (sfold F init gs).getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [sfold_length]; exact hj)]
  rfl

end Fold

theorem reads_get {n : ℕ} {D : Circuit} (hr : ReadsBack n D) :
    ∀ m (hm : m < D.gates.length), ∀ j ∈ D.gates[m].inputs, j < n + m := by
  intro m hm j hj
  apply hr m hm j
  show j ∈ (D.gates.getD m ⟨GateOp.or, []⟩).inputs
  rw [List.getD_eq_getElem _ _ hm]
  exact hj



theorem mem_foldl_union' {β : Type} {inst : DecidableEq β} (F : ℕ → Finset β) (l : List ℕ) (base : Finset β)
    (z : β) : z ∈ l.foldl (fun acc j => acc ∪ F j) base ↔ z ∈ base ∨ ∃ j ∈ l, z ∈ F j := by
  induction l generalizing base with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons, ih, Finset.mem_union]
    constructor
    · rintro ((h | h) | ⟨j', hj', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', h⟩
    · rintro (h | ⟨j', hj', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hj' with rfl | h2
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨j', h2, h⟩

theorem foldl_pair_fst {β : Type} {inst : DecidableEq β} (G1 G2 : ℕ → Finset β) (l : List ℕ)
    (base : Finset β × Finset β) :
    (l.foldl (fun v t => (v.1 ∪ G1 t, v.2 ∪ G2 t)) base).1 = l.foldl (fun acc t => acc ∪ G1 t) base.1 := by
  induction l generalizing base with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.foldl_cons]
    exact ih _

theorem foldl_pair_snd {β : Type} {inst : DecidableEq β} (G1 G2 : ℕ → Finset β) (l : List ℕ)
    (base : Finset β × Finset β) :
    (l.foldl (fun v t => (v.1 ∪ G1 t, v.2 ∪ G2 t)) base).2 = l.foldl (fun acc t => acc ∪ G2 t) base.2 := by
  induction l generalizing base with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.foldl_cons]
    exact ih _

noncomputable def FI {k : ℕ} (ts : List (Finset (Fin k) × Finset (Fin k))) (g : Gate) :
    Finset (Fin k) × Finset (Fin k) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  g.inputs.foldl (fun v t => (v.1 ∪ (ts.getD t (∅,∅)).1, v.2 ∪ (ts.getD t (∅,∅)).2)) (∅,∅)

theorem mem_FI1 {k : ℕ} (W : List (Finset (Fin k) × Finset (Fin k))) (g : Gate) (x : Fin k) :
    x ∈ (FI W g).1 ↔ ∃ j ∈ g.inputs, x ∈ (W.getD j (∅,∅)).1 := by
  unfold FI
  rw [foldl_pair_fst, mem_foldl_union']
  simp

theorem mem_FI2 {k : ℕ} (W : List (Finset (Fin k) × Finset (Fin k))) (g : Gate) (x : Fin k) :
    x ∈ (FI W g).2 ↔ ∃ j ∈ g.inputs, x ∈ (W.getD j (∅,∅)).2 := by
  unfold FI
  rw [foldl_pair_snd, mem_foldl_union']
  simp

theorem FI_loc {k : ℕ} (W1 W2 : List (Finset (Fin k) × Finset (Fin k))) (g : Gate)
    (h : ∀ j ∈ g.inputs, W1.getD j (∅,∅) = W2.getD j (∅,∅)) : FI W1 g = FI W2 g := by
  apply Prod.ext
  · apply Finset.ext
    intro x
    rw [mem_FI1, mem_FI1]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by rw [← h j hj]; exact hx⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by rw [h j hj]; exact hx⟩
  · apply Finset.ext
    intro x
    rw [mem_FI2, mem_FI2]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by rw [← h j hj]; exact hx⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by rw [h j hj]; exact hx⟩

theorem mem_foldl_insert {inst : DecidableEq ℕ} (W : List (Finset ℕ)) (l : List ℕ) (base : Finset ℕ) (y : ℕ) :
    y ∈ l.foldl (fun acc j => insert j (acc ∪ W.getD j ∅)) base ↔ y ∈ base ∨ ∃ j ∈ l, y = j ∨ y ∈ W.getD j ∅ := by
  induction l generalizing base with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons, ih, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ((h | h | h) | ⟨j', hj', h⟩)
      · exact Or.inr ⟨j, List.mem_cons_self .., Or.inl h⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, List.mem_cons_self .., Or.inr h⟩
      · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', h⟩
    · rintro (h | ⟨j', hj', h⟩)
      · exact Or.inl (Or.inr (Or.inl h))
      · rcases List.mem_cons.1 hj' with rfl | h2
        · rcases h with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr ⟨j', h2, h⟩

noncomputable def FD (ts : List (Finset ℕ)) (g : Gate) : Finset ℕ :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  g.inputs.foldl (fun acc j => insert j (acc ∪ ts.getD j ∅)) ∅

theorem mem_FD (W : List (Finset ℕ)) (g : Gate) (y : ℕ) :
    y ∈ FD W g ↔ ∃ j ∈ g.inputs, y = j ∨ y ∈ W.getD j ∅ := by
  unfold FD
  rw [mem_foldl_insert]
  simp

theorem FD_loc (W1 W2 : List (Finset ℕ)) (g : Gate) (h : ∀ j ∈ g.inputs, W1.getD j ∅ = W2.getD j ∅) :
    FD W1 g = FD W2 g := by
  apply Finset.ext
  intro y
  rw [mem_FD, mem_FD]
  constructor
  · rintro ⟨j, hj, hy⟩
    exact ⟨j, hj, by rw [← h j hj]; exact hy⟩
  · rintro ⟨j, hj, hy⟩
    exact ⟨j, hj, by rw [h j hj]; exact hy⟩


theorem mem_union' {α : Type} {inst : DecidableEq α} {s t : Finset α} {a : α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  Finset.mem_union

theorem mem_inter' {α : Type} {inst : DecidableEq α} {s t : Finset α} {a : α} : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=
  Finset.mem_inter

theorem mem_biUnion' {α β : Type} {inst : DecidableEq β} {s : Finset α} {t : α → Finset β} {b : β} :
    b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a := Finset.mem_biUnion

theorem mem_filter' {α : Type} {p : α → Prop} {inst : DecidablePred p} {s : Finset α} {a : α} :
    a ∈ s.filter p ↔ a ∈ s ∧ p a := Finset.mem_filter

theorem union_subset_union' {α : Type} {inst : DecidableEq α} {s t u v : Finset α} (h1 : s ⊆ u) (h2 : t ⊆ v) :
    s ∪ t ⊆ u ∪ v := Finset.union_subset_union h1 h2

end PEqualNP.Outside.L_lib_1479_aux

theorem PEqualNP.Outside.L_lib_1479 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) D ∧ D.output < h+2+D.size
let pos := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => valid h D ∧ PEqualNP.NotBracket.notCount D=0
let wireInfo := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let Z : Finset (Fin k) × Finset (Fin k) := (∅,∅)
  let xs := List.ofFn (fun j : Fin k => (({j},∅) : Finset (Fin k) × Finset (Fin k))) ++
    List.ofFn (fun j : Fin k => ((∅,{j}) : Finset (Fin k) × Finset (Fin k))) ++ [Z,Z]
  D.gates.foldl (fun (ts : List (Finset (Fin k) × Finset (Fin k))) g =>
    ts ++ [g.inputs.foldl (fun v t => let a := ts.getD t Z
                                      (v.1 ∪ a.1,v.2 ∪ a.2)) Z]) xs
let gateAt := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (t : Nat) => D.gates.getD t ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
∀ (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit), pos (2*k) D →
let src := 2*k+2
let Z : Finset (Fin k) × Finset (Fin k) := (∅,∅)
let info := wireInfo k D
let vars := fun (j : Nat) => let s := info.getD j Z
                             s.1 ∪ s.2
let cross := fun (t : Nat) =>
  let g := gateAt D t
  let a := (g.inputs.head?.map (fun j => info.getD j Z)).getD Z
  let b := (g.inputs[1]?.map (fun j => info.getD j Z)).getD Z
  if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then (a.1 ∩ b.2) ∪ (a.2 ∩ b.1) else ∅
let legal := fun (B : Nat → Finset (Fin k)) =>
  (∀ j, j<src+D.size → B j ⊆ vars j) ∧
  ∀ t, t<D.size → ∀ j ∈ (gateAt D t).inputs, (B (src+t) ∪ cross t) ∩ vars j ⊆ B j
let bounded := fun (w : Nat) (B : Nat → Finset (Fin k)) =>
  (∀ j, j<src → (B j).card ≤ w) ∧ ∀ t, t<D.size → (B (src+t) ∪ cross t).card ≤ w
let deps := D.gates.foldl (fun (ts : List (Finset Nat)) g =>
  ts ++ [g.inputs.foldl (fun acc j => insert j (acc ∪ ts.getD j ∅)) ∅]) (List.replicate src ∅)
let least := fun (j : Nat) => vars j ∩
  (((Finset.range D.size).filter (fun t => j ∈ deps.getD (src+t) ∅)).biUnion cross)
legal least ∧ (∀ B, legal B → ∀ j, j<src+D.size → least j ⊆ B j) ∧
∀ w : Nat, bounded w least ↔ ∃ B, legal B ∧ bounded w B) := by
  intro valid pos wireInfo gateAt k D hpos src Z info vars cross legal bounded deps least
  obtain ⟨⟨hfan, hrb, hout⟩, hnc⟩ := hpos
  have hreads := PEqualNP.Outside.L_lib_1479_aux.reads_get hrb
  have hgate : ∀ t (ht : t < D.size), gateAt D t = D.gates[t]'ht := fun t ht => List.getD_eq_getElem _ _ ht
  obtain ⟨init, hinit, hI⟩ : ∃ init : List (Finset (Fin k) × Finset (Fin k)), init.length = 2*k+2 ∧
      info = PEqualNP.Outside.L_lib_1479_aux.sfold PEqualNP.Outside.L_lib_1479_aux.FI init D.gates :=
    ⟨_, by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega, rfl⟩
  have hIg : ∀ t (ht : t < D.size), info.getD (src+t) (∅,∅) = PEqualNP.Outside.L_lib_1479_aux.FI info (D.gates[t]'ht) := by
    intro t ht
    rw [hI]
    have := PEqualNP.Outside.L_lib_1479_aux.sfold_gate PEqualNP.Outside.L_lib_1479_aux.FI (∅,∅) PEqualNP.Outside.L_lib_1479_aux.FI_loc init D.gates
      (fun m hm j hj => by rw [hinit]; exact hreads m hm j hj) t ht
    rw [hinit] at this
    exact this
  have hvars : ∀ j x, x ∈ vars j ↔ x ∈ (info.getD j (∅,∅)).1 ∨ x ∈ (info.getD j (∅,∅)).2 :=
    fun j x => PEqualNP.Outside.L_lib_1479_aux.mem_union'
  have hvars_gate : ∀ t (ht : t < D.size) x, x ∈ vars (src+t) ↔ ∃ j ∈ (gateAt D t).inputs, x ∈ vars j := by
    intro t ht x
    rw [hvars, hIg t ht, hgate t ht, PEqualNP.Outside.L_lib_1479_aux.mem_FI1, PEqualNP.Outside.L_lib_1479_aux.mem_FI2]
    constructor
    · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
      · exact ⟨j, hj, (hvars j x).2 (Or.inl h)⟩
      · exact ⟨j, hj, (hvars j x).2 (Or.inr h)⟩
    · rintro ⟨j, hj, h⟩
      rcases (hvars j x).1 h with h | h
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr ⟨j, hj, h⟩
  have hD : deps = PEqualNP.Outside.L_lib_1479_aux.sfold PEqualNP.Outside.L_lib_1479_aux.FD (List.replicate (2*k+2) ∅) D.gates := rfl
  have hDg : ∀ t (ht : t < D.size) y, y ∈ deps.getD (src+t) ∅ ↔
      ∃ j ∈ (gateAt D t).inputs, y = j ∨ y ∈ deps.getD j ∅ := by
    intro t ht y
    have := PEqualNP.Outside.L_lib_1479_aux.sfold_gate PEqualNP.Outside.L_lib_1479_aux.FD ∅ PEqualNP.Outside.L_lib_1479_aux.FD_loc (List.replicate (2*k+2) ∅) D.gates
      (fun m hm j hj => by rw [List.length_replicate]; exact hreads m hm j hj) t ht
    rw [List.length_replicate] at this
    rw [hgate t ht, hD]
    show y ∈ (PEqualNP.Outside.L_lib_1479_aux.sfold PEqualNP.Outside.L_lib_1479_aux.FD (List.replicate (2*k+2) ∅) D.gates).getD (2*k+2+t) ∅ ↔ _
    rw [this, PEqualNP.Outside.L_lib_1479_aux.mem_FD]
  have hDsmall : ∀ j, j < src → deps.getD j ∅ = ∅ := by
    intro j hj
    rw [hD, PEqualNP.Outside.L_lib_1479_aux.sfold_old _ _ _ _ (by rw [List.length_replicate]; exact hj),
      List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  have hDbig : ∀ j, src + D.size ≤ j → deps.getD j ∅ = ∅ := by
    intro j hj
    rw [hD]
    exact PEqualNP.Outside.L_lib_1479_aux.sfold_beyond _ _ _ _ (by rw [List.length_replicate]; exact hj)
  have hDrange : ∀ v y, y ∈ deps.getD v ∅ → ∃ t, t < D.size ∧ v = src + t := by
    intro v y hy
    by_cases h1 : v < src
    · rw [hDsmall v h1] at hy
      simp at hy
    by_cases h2 : src + D.size ≤ v
    · rw [hDbig v h2] at hy
      simp at hy
    exact ⟨v - src, by omega, by omega⟩
  have hin_lt : ∀ t (ht : t < D.size), ∀ i ∈ (gateAt D t).inputs, i < src + t := by
    intro t ht i hi
    rw [hgate t ht] at hi
    exact hreads t ht i hi
  have htrans : ∀ v w, w ∈ deps.getD v ∅ → ∀ y, y ∈ deps.getD w ∅ → y ∈ deps.getD v ∅ := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
    intro w hw y hy
    obtain ⟨t, ht, rfl⟩ := hDrange v w hw
    rw [hDg t ht] at hw ⊢
    obtain ⟨i, hi, hwi | hwi⟩ := hw
    · subst hwi
      exact ⟨w, hi, Or.inr hy⟩
    · exact ⟨i, hi, Or.inr (ih i (hin_lt t ht i hi) w hwi y hy)⟩
  have hvars_mono : ∀ v j, j ∈ deps.getD v ∅ → ∀ x, x ∈ vars j → x ∈ vars v := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
    intro j hj x hx
    obtain ⟨t, ht, rfl⟩ := hDrange v j hj
    rw [hDg t ht] at hj
    rw [hvars_gate t ht]
    obtain ⟨i, hi, hji | hji⟩ := hj
    · subst hji
      exact ⟨j, hi, hx⟩
    · exact ⟨i, hi, ih i (hin_lt t ht i hi) j hji x hx⟩
  have hleast : ∀ j x, x ∈ least j ↔ x ∈ vars j ∧ ∃ t, (t < D.size ∧ j ∈ deps.getD (src+t) ∅) ∧ x ∈ cross t := by
    intro j x
    simp only [least, PEqualNP.Outside.L_lib_1479_aux.mem_inter', PEqualNP.Outside.L_lib_1479_aux.mem_biUnion', PEqualNP.Outside.L_lib_1479_aux.mem_filter', Finset.mem_range]
  have legal_least : legal least := by
    refine ⟨fun j _ x hx => ((hleast j x).1 hx).1, ?_⟩
    intro t ht j hj x hx
    rw [PEqualNP.Outside.L_lib_1479_aux.mem_inter', PEqualNP.Outside.L_lib_1479_aux.mem_union'] at hx
    rw [hleast]
    obtain ⟨hx1 | hx1, hx2⟩ := hx
    · obtain ⟨_, t', ⟨ht', hdep⟩, hc⟩ := (hleast (src+t) x).1 hx1
      exact ⟨hx2, t', ⟨ht', htrans _ _ hdep j ((hDg t ht j).2 ⟨j, hj, Or.inl rfl⟩)⟩, hc⟩
    · exact ⟨hx2, t, ⟨ht, (hDg t ht j).2 ⟨j, hj, Or.inl rfl⟩⟩, hx1⟩
  have least_sub : ∀ B, legal B → ∀ j, j < src + D.size → least j ⊆ B j := by
    intro B hB j _ x hx
    obtain ⟨hB1, hB2⟩ := hB
    have P : ∀ t, t < D.size → x ∈ B (src+t) → ∀ j, j ∈ deps.getD (src+t) ∅ → x ∈ vars j → x ∈ B j := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
      intro ht hxB j hj hxv
      rw [hDg t ht] at hj
      obtain ⟨i, hi, hji | hji⟩ := hj
      · subst hji
        exact hB2 t ht j hi (PEqualNP.Outside.L_lib_1479_aux.mem_inter'.2 ⟨PEqualNP.Outside.L_lib_1479_aux.mem_union'.2 (Or.inl hxB), hxv⟩)
      · have hxi : x ∈ vars i := hvars_mono i j hji x hxv
        have hxBi : x ∈ B i := hB2 t ht i hi (PEqualNP.Outside.L_lib_1479_aux.mem_inter'.2 ⟨PEqualNP.Outside.L_lib_1479_aux.mem_union'.2 (Or.inl hxB), hxi⟩)
        have hilt := hin_lt t ht i hi
        obtain ⟨t'', ht'', rfl⟩ := hDrange i j hji
        exact ih t'' (by omega) ht'' hxBi j hji hxv
    rw [hleast] at hx
    obtain ⟨hxv, t', ⟨ht', hdep⟩, hc⟩ := hx
    rw [hDg t' ht'] at hdep
    obtain ⟨i, hi, hji | hji⟩ := hdep
    · subst hji
      exact hB2 t' ht' j hi (PEqualNP.Outside.L_lib_1479_aux.mem_inter'.2 ⟨PEqualNP.Outside.L_lib_1479_aux.mem_union'.2 (Or.inr hc), hxv⟩)
    · have hxi : x ∈ vars i := hvars_mono i j hji x hxv
      have hxBi : x ∈ B i := hB2 t' ht' i hi (PEqualNP.Outside.L_lib_1479_aux.mem_inter'.2 ⟨PEqualNP.Outside.L_lib_1479_aux.mem_union'.2 (Or.inr hc), hxi⟩)
      obtain ⟨t'', ht'', rfl⟩ := hDrange i j hji
      exact P t'' ht'' hxBi j hji hxv
  refine ⟨legal_least, least_sub, ?_⟩
  intro w
  constructor
  · intro hb
    exact ⟨least, legal_least, hb⟩
  · rintro ⟨B, hB, hb1, hb2⟩
    refine ⟨fun j hj => le_trans (Finset.card_le_card (least_sub B hB j (by omega))) (hb1 j hj), fun t ht => ?_⟩
    exact le_trans (Finset.card_le_card (PEqualNP.Outside.L_lib_1479_aux.union_subset_union' (least_sub B hB (src+t) (by omega))
      (Finset.Subset.refl _))) (hb2 t ht)
