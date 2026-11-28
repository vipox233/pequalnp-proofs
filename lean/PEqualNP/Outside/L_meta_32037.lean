import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32037

open Finset PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton l g ih =>
    unfold run at ih ⊢
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.length_append, ih, List.length_singleton]
    omega

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_low (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton l g ih =>
    rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_length]; omega), ih]

lemma run_gate (n : ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = n)
    (back : ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < n + j)
    (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (n + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (run gs x).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton l g ih =>
    have lenl : (run l x).length = n + l.length := by rw [run_length, hx]
    have back' : ∀ j (hj : j < l.length), ∀ i ∈ (l[j]).inputs, i < n + j := by
      intro j hj i hi
      have := back j (by simp; omega) i (by rwa [List.getElem_append_left hj])
      exact this
    have same : ∀ (k : ℕ) (is : List ℕ), k ≤ l.length → (∀ i ∈ is, i < n + k) →
        (is.map fun i => (run (l ++ [g]) x).getD i false) = is.map fun i => (run l x).getD i false := by
      intro k is hk h
      refine List.map_congr_left fun i hi => ?_
      have := h i hi
      rw [run_snoc, List.getD_append _ _ _ _ (by omega)]
    rcases Nat.lt_or_ge j l.length with lt | ge
    · have gj : (l ++ [g])[j] = l[j] := List.getElem_append_left lt
      rw [gj, same j _ (by omega) (back' j lt), ← ih back' lt, run_snoc,
        List.getD_append _ _ _ _ (by omega)]
    · have e : j = l.length := by simp at hj; omega
      subst e
      have gj : (l ++ [g])[l.length] = g := by simp
      have bg : ∀ i ∈ g.inputs, i < n + l.length := by
        intro i hi
        exact back l.length (by simp) i (by rwa [gj])
      rw [gj, same l.length _ le_rfl bg, run_snoc, List.getD_append_right _ _ _ _ (by omega), lenl]
      simp

lemma main (n g : ℕ) (C : Circuit) (back : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (out : C.output < n + C.size)
    (legal : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (size : C.size ≤ g) :
    ∃ S : Finset ℕ, S.card ≤ g + 1 ∧ (∀ i ∈ S, i < n) ∧
      (∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) → C.eval x = C.eval y) ∧
      (S.card ≤ g ∨ ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = true → y.getD i false = true) →
        C.eval x = true → C.eval y = true) := by
  classical
  have back' : ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < n + j := by
    intro j hj i hi
    apply back j hj i
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj] using hi
  let step : ℕ → ℕ → Prop := fun a b =>
    ∃ (j : ℕ) (hj : j < C.gates.length), a = n + j ∧ b ∈ (C.gates[j]).inputs
  let cone := (range (n + C.size)).filter fun i => Relation.ReflTransGen step C.output i
  have mem : ∀ i, i ∈ cone ↔ Relation.ReflTransGen step C.output i := by
    intro i
    simp only [cone, mem_filter, mem_range, and_iff_right_iff_imp]
    intro h
    induction h with
    | refl => exact out
    | tail _ s _ =>
      obtain ⟨j, hj, _, hb⟩ := s
      have := back' j hj _ hb
      change _ < n + C.gates.length
      omega
  have closed : ∀ j (hj : j < C.gates.length), n + j ∈ cone → ∀ i ∈ (C.gates[j]).inputs, i ∈ cone := by
    intro j hj h i hi
    exact (mem i).mpr (((mem _).mp h).tail ⟨j, hj, rfl, hi⟩)
  let S := cone.filter fun i => i < n
  let G := (range C.gates.length).filter fun j => n + j ∈ cone
  have split : cone.card = S.card + G.card := by
    have e : cone.filter (fun i => ¬i < n) = G.image fun j => n + j := by
      ext i
      simp only [mem_filter, mem_image, G, mem_range]
      constructor
      · rintro ⟨h, hn⟩
        have lt : i < n + C.gates.length := by
          have := (mem_filter.mp h).1
          exact mem_range.mp this
        refine ⟨i - n, ⟨by omega, ?_⟩, by omega⟩
        rwa [show n + (i - n) = i by omega]
      · rintro ⟨j, ⟨_, h⟩, rfl⟩
        exact ⟨h, by omega⟩
    have := card_filter_add_card_filter_not (s := cone) (fun i => i < n)
    rw [e, card_image_of_injective _ (add_right_injective n)] at this
    exact this.symm
  let len : ℕ → ℕ := fun j => (C.gates.getD j ⟨.or, []⟩).inputs.length
  have lenj : ∀ j (hj : j < C.gates.length), len j = (C.gates[j]).inputs.length := by
    intro j hj
    simp [len, List.getD_eq_getElem?_getD, hj]
  have cover : cone.erase C.output ⊆ G.biUnion fun j => (C.gates.getD j ⟨.or, []⟩).inputs.toFinset := by
    intro i hi
    obtain ⟨ne, hi⟩ := mem_erase.mp hi
    rcases Relation.ReflTransGen.cases_tail ((mem i).mp hi) with h | ⟨a, ha, j, hj, rfl, hb⟩
    · exact absurd h ne
    · refine mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, (mem _).mpr ha⟩, ?_⟩
      simpa [List.getD_eq_getElem?_getD, hj] using hb
  have count : cone.card ≤ (∑ j ∈ G, len j) + 1 := by
    have h1 := card_le_card cover
    have h2 := h1.trans card_biUnion_le
    have h3 : ∑ j ∈ G, (C.gates.getD j ⟨.or, []⟩).inputs.toFinset.card ≤ ∑ j ∈ G, len j :=
      sum_le_sum fun j _ => List.toFinset_card_le _
    have := pred_card_le_card_erase (s := cone) (a := C.output)
    omega
  have two : ∀ j ∈ G, len j ≤ 2 := by
    intro j hj
    have lt := mem_range.mp (mem_filter.mp hj).1
    rw [lenj j lt]
    exact (legal _ (List.getElem_mem lt)).1
  have Gg : G.card ≤ g := by
    have := card_filter_le (range C.gates.length) (fun j => n + j ∈ cone)
    rw [card_range] at this
    exact this.trans size
  have total : (∑ j ∈ G, len j) ≤ 2 * G.card := by
    have := sum_le_card_nsmul G len 2 two
    simpa [mul_comm] using this
  have agree : ∀ (R : Bool → Bool → Prop) (x y : List Bool), x.length = n → y.length = n →
      (∀ i ∈ S, R (x.getD i false) (y.getD i false)) →
      (∀ j (hj : j < C.gates.length), n + j ∈ cone →
        (∀ i ∈ (C.gates[j]).inputs, R ((run C.gates x).getD i false) ((run C.gates y).getD i false)) →
        R ((C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (run C.gates x).getD i false))
          ((C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (run C.gates y).getD i false))) →
      ∀ i ∈ cone, R ((run C.gates x).getD i false) ((run C.gates y).getD i false) := by
    intro R x y hx hy base gate i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases low : i < n
      · rw [run_low _ _ _ (by omega), run_low _ _ _ (by omega)]
        exact base i (mem_filter.mpr ⟨hi, low⟩)
      · have lt : i < n + C.gates.length := mem_range.mp (mem_filter.mp hi).1
        obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [run_gate n _ x hx back' j hj, run_gate n _ y hy back' j hj]
        refine gate j hj hi fun k hk => ?_
        exact ih k (back' j hj k hk) (closed j hj hi k hk)
  have outc : C.output ∈ cone := (mem _).mpr Relation.ReflTransGen.refl
  refine ⟨S, by omega, fun i hi => (mem_filter.mp hi).2, ?_, ?_⟩
  · intro x y hx hy h
    exact agree (fun a b => a = b) x y hx hy h
      (fun j hj _ ih => congrArg _ (List.map_congr_left ih)) _ outc
  · by_cases nt : ∃ j ∈ G, (C.gates.getD j ⟨.or, []⟩).op = .not
    · left
      obtain ⟨j, hj, ho⟩ := nt
      have lt := mem_range.mp (mem_filter.mp hj).1
      have one : len j = 1 := by
        rw [lenj j lt]
        have o : (C.gates[j]).op = .not := by
          simpa [List.getD_eq_getElem?_getD, lt] using ho
        rcases (legal _ (List.getElem_mem lt)).2 with h | h | h
        · rw [o] at h; cases h
        · rw [o] at h; cases h
        · exact h.2
      have less : (∑ j ∈ G, len j) + 1 ≤ 2 * G.card := by
        have a := sum_erase_add G len hj
        have b : ∑ k ∈ G.erase j, len k ≤ (G.erase j).card • 2 :=
          sum_le_card_nsmul (G.erase j) len 2 fun k hk => two k (mem_of_mem_erase hk)
        rw [smul_eq_mul] at b
        have c : (G.erase j).card + 1 = G.card := card_erase_add_one hj
        have d : ∑ k ∈ G, len k = (∑ k ∈ G.erase j, len k) + 1 := by rw [← one]; exact a.symm
        rw [d]
        omega
      omega
    · right
      intro x y hx hy h
      apply agree (fun a b => a = true → b = true) x y hx hy h ?_ _ outc
      intro j hj hc ih
      have o : (C.gates[j]).op = .and ∨ (C.gates[j]).op = .or := by
        rcases (legal _ (List.getElem_mem hj)).2 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · refine absurd ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, hc⟩, ?_⟩ nt
          simpa [List.getD_eq_getElem?_getD, hj] using h.1
      rcases o with o | o <;> rw [o]
      · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
        exact fun a i hi => ih i hi (a i hi)
      · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        rintro ⟨i, hi, a⟩
        exact ⟨i, hi, ih i hi a⟩

end PEqualNP.Outside.L_meta_32037

theorem PEqualNP.Outside.L_meta_32037 : (∀ (N g : ℕ), g+1 < N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let area := fun (H : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 = true)).card
  let stripes := fun (h : ℕ) (C : Circ) (s : ℕ) =>
    ∃ T : Finset X, T.card = s ∧
      ((∀ (w : Fin h → Bool) (x y : X), table h C w x y = decide (x ∈ T)) ∨
       (∀ (w : Fin h → Bool) (x y : X), table h C w x y = decide (y ∈ T)))
  ∀ (h : ℕ) (C : Circ), legal h C → C.size ≤ g →
    ∀ w : Fin h → Bool,
      let A := area (table h C w)
      A < N*N →
      ((A ≤ N*(g+1) ∧ (A = N*(g+1) → stripes h C (g+1))) ∨
       (N*N-A ≤ N*g ∧ (N*N-A = N*g → stripes h C (N-g))))) := by
  intro N g hg X Circ legal table area stripes h C hl size w A hA
  obtain ⟨back, out, ops⟩ := hl
  obtain ⟨S, Sg, Sn, same, mono⟩ := PEqualNP.Outside.L_meta_32037.main (N + N + h) g C back out ops size
  have N0 : 0 < N := by omega
  let L : Finset (Fin N) := Finset.univ.filter fun i => i.val ∈ S
  let R : Finset (Fin N) := Finset.univ.filter fun i => N + i.val ∈ S
  let Q : Finset (Fin h) := Finset.univ.filter fun i => N + N + i.val ∈ S
  have count : L.card + R.card + Q.card ≤ S.card := by
    have a : (L.image fun i => i.val).card = L.card := Finset.card_image_of_injective _ Fin.val_injective
    have b : (R.image fun i => N + i.val).card = R.card :=
      Finset.card_image_of_injective _ fun x y e => Fin.ext (by simpa using e)
    have c : (Q.image fun i => N + N + i.val).card = Q.card :=
      Finset.card_image_of_injective _ fun x y e => Fin.ext (by simpa using e)
    have d1 : Disjoint (L.image fun i => i.val) (R.image fun i => N + i.val) := by
      rw [Finset.disjoint_left]
      intro v hv hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j, _, e⟩ := Finset.mem_image.mp hw
      have := i.isLt
      omega
    have d2 : Disjoint ((L.image fun i => i.val) ∪ (R.image fun i => N + i.val))
        (Q.image fun i => N + N + i.val) := by
      rw [Finset.disjoint_left]
      intro v hv hw
      obtain ⟨k, _, e⟩ := Finset.mem_image.mp hw
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        have := i.isLt
        omega
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
        have := j.isLt
        omega
    rw [← a, ← b, ← c, ← Finset.card_union_of_disjoint d1, ← Finset.card_union_of_disjoint d2]
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_union, Finset.mem_image, L, R, Q, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv
    rcases hv with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩ <;> exact hi
  let inp := fun (w : Fin h → Bool) (x y : Fin N) =>
    PEqualNP.Represents.oneEach x y ++ List.ofFn w
  have len : ∀ w x y, (inp w x y).length = N + N + h := by
    intro w x y
    simp [inp, PEqualNP.Represents.oneEach]
    omega
  have bitL : ∀ w x y (i : ℕ) (hi : i < N), (inp w x y).getD i false = decide ((⟨i, hi⟩ : Fin N) = x) := by
    intro w x y i hi
    simp only [inp, PEqualNP.Represents.oneEach, List.append_assoc]
    rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, dif_pos hi, Option.getD_some]
  have bitR : ∀ w x y (i : ℕ) (hi : i < N), (inp w x y).getD (N + i) false = decide ((⟨i, hi⟩ : Fin N) = y) := by
    intro w x y i hi
    simp only [inp, PEqualNP.Represents.oneEach, List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, dif_pos hi, Option.getD_some]
  have bitQ : ∀ w x y (i : ℕ) (hi : i < h), (inp w x y).getD (N + N + i) false = w ⟨i, hi⟩ := by
    intro w x y i hi
    unfold inp
    have l : (PEqualNP.Represents.oneEach x y).length = N + N := by
      simp [PEqualNP.Represents.oneEach]
    rw [List.getD_append_right _ _ _ _ (by omega), l, Nat.add_sub_cancel_left,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi, Option.getD_some]
  have cases3 : ∀ i ∈ S, (∃ a : Fin N, a ∈ L ∧ i = a.val) ∨ (∃ b : Fin N, b ∈ R ∧ i = N + b.val) ∨
      (∃ c : Fin h, c ∈ Q ∧ i = N + N + c.val) := by
    intro i hi
    have lt := Sn i hi
    by_cases h1 : i < N
    · exact Or.inl ⟨⟨i, h1⟩, by simpa [L] using hi, rfl⟩
    by_cases h2 : i < N + N
    · refine Or.inr (Or.inl ⟨⟨i - N, by omega⟩, ?_, by simp; omega⟩)
      simpa [R, show N + (i - N) = i by omega] using hi
    · refine Or.inr (Or.inr ⟨⟨i - (N + N), by omega⟩, ?_, by simp; omega⟩)
      simpa [Q, show N + N + (i - (N + N)) = i by omega] using hi
  have offL : ∀ w x y (a : Fin N), a ∈ L → x ∉ L → (inp w x y).getD a.val false = false := by
    intro w x y a ha hx
    rw [bitL w x y a.val a.isLt]
    exact decide_eq_false fun e => hx (e ▸ ha)
  have offR : ∀ w x y (b : Fin N), b ∈ R → y ∉ R → (inp w x y).getD (N + b.val) false = false := by
    intro w x y b hb hy
    rw [bitR w x y b.val b.isLt]
    exact decide_eq_false fun e => hy (e ▸ hb)
  have named : ∃ x0 y0 : Fin N, x0 ∉ L ∧ y0 ∉ R := by
    have lt : L.card < N ∧ R.card < N := by omega
    have a : ∃ x0, x0 ∉ L := by
      by_contra c
      push Not at c
      have : L = Finset.univ := Finset.eq_univ_iff_forall.mpr c
      rw [this, Finset.card_univ, Fintype.card_fin] at lt
      omega
    have b : ∃ y0, y0 ∉ R := by
      by_contra c
      push Not at c
      have : R = Finset.univ := Finset.eq_univ_iff_forall.mpr c
      rw [this, Finset.card_univ, Fintype.card_fin] at lt
      omega
    obtain ⟨x0, hx⟩ := a
    obtain ⟨y0, hy⟩ := b
    exact ⟨x0, y0, hx, hy⟩
  obtain ⟨x0, y0, hx0, hy0⟩ := named
  have unnamed : ∀ x y, x ∉ L → y ∉ R → table h C w x y = table h C w x0 y0 := by
    intro x y hx hy
    refine same _ _ (len w x y) (len w x0 y0) fun i hi => ?_
    rcases cases3 i hi with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, _, rfl⟩
    · change (inp w x y).getD _ false = (inp w x0 y0).getD _ false
      rw [offL w x y a ha hx, offL w x0 y0 a ha hx0]
    · change (inp w x y).getD _ false = (inp w x0 y0).getD _ false
      rw [offR w x y b hb hy, offR w x0 y0 b hb hy0]
    · change (inp w x y).getD _ false = (inp w x0 y0).getD _ false
      rw [bitQ w x y c.val c.isLt, bitQ w x0 y0 c.val c.isLt]
  let lines : Finset (Fin N × Fin N) := (L ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ R)
  have lc : lines.card ≤ N * (L.card + R.card) := by
    refine (Finset.card_union_le _ _).trans (le_of_eq ?_)
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    ring
  have inl : ∀ z : Fin N × Fin N, z ∉ lines → z.1 ∉ L ∧ z.2 ∉ R := by
    intro z hz
    simp only [lines, Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true, true_and,
      not_or] at hz
    exact hz
  have tight : ∀ (s : ℕ) (E : Finset (Fin N × Fin N)), E ⊆ lines → E.card = N * s →
      L.card + R.card ≤ s → (R = ∅ ∧ L.card = s ∧ E = L ×ˢ Finset.univ) ∨
        (L = ∅ ∧ R.card = s ∧ E = Finset.univ ×ˢ R) := by
    intro s E sub eq le
    have e1 : N * s ≤ lines.card := eq ▸ Finset.card_le_card sub
    have e2 : N * (L.card + R.card) ≤ N * s := Nat.mul_le_mul_left N le
    have es : L.card + R.card = s :=
      Nat.le_antisymm le (Nat.le_of_mul_le_mul_left (e1.trans lc) N0)
    have full : E = lines := Finset.eq_of_subset_of_card_le sub (by rw [eq, ← es]; exact lc)
    have both : L.card * R.card = 0 := by
      have u := Finset.card_union_add_card_inter (L ×ˢ (Finset.univ : Finset (Fin N)))
        ((Finset.univ : Finset (Fin N)) ×ˢ R)
      have i : (L ×ˢ (Finset.univ : Finset (Fin N))) ∩ ((Finset.univ : Finset (Fin N)) ×ˢ R) = L ×ˢ R := by
        rw [Finset.product_inter_product, Finset.inter_univ, Finset.univ_inter]
      rw [i, Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ,
        Fintype.card_fin] at u
      change lines.card + _ = _ at u
      rw [← full, eq, ← es] at u
      have : N * (L.card + R.card) = L.card * N + N * R.card := by ring
      omega
    rcases Nat.mul_eq_zero.mp both with z | z
    · have z' := Finset.card_eq_zero.mp z
      refine Or.inr ⟨z', by omega, ?_⟩
      rw [full]
      simp [lines, z']
    · have z' := Finset.card_eq_zero.mp z
      refine Or.inl ⟨z', by omega, ?_⟩
      rw [full]
      simp [lines, z']
  have noseed : S.card ≤ L.card + R.card → ∀ w' x y, table h C w' x y = table h C w x y := by
    intro le w' x y
    have Q0 : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    refine same _ _ (len w' x y) (len w x y) fun i hi => ?_
    rcases cases3 i hi with ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩ | ⟨c, hc, rfl⟩
    · change (inp w' x y).getD _ false = (inp w x y).getD _ false
      rw [bitL w' x y a.val a.isLt, bitL w x y a.val a.isLt]
    · change (inp w' x y).getD _ false = (inp w x y).getD _ false
      rw [bitR w' x y b.val b.isLt, bitR w x y b.val b.isLt]
    · rw [Q0] at hc
      simp at hc
  let E1 : Finset (Fin N × Fin N) := Finset.univ.filter fun z => table h C w z.1 z.2 = true
  have AE : A = E1.card := rfl
  cases v : table h C w x0 y0
  · left
    have sub : E1 ⊆ lines := by
      intro z hz
      by_contra c
      have o := inl z c
      have := (Finset.mem_filter.mp hz).2
      rw [unnamed _ _ o.1 o.2, v] at this
      exact Bool.noConfusion this
    have le : L.card + R.card ≤ g + 1 := by omega
    refine ⟨AE ▸ (Finset.card_le_card sub).trans (lc.trans (Nat.mul_le_mul_left N le)), fun eq => ?_⟩
    have mE : ∀ w' x y, table h C w' x y = decide ((x, y) ∈ E1) := by
      intro w' x y
      have sq : S.card ≤ L.card + R.card := by
        have : N * (g + 1) ≤ N * (L.card + R.card) :=
          (eq.symm.trans AE) ▸ (Finset.card_le_card sub).trans lc
        have := Nat.le_of_mul_le_mul_left this N0
        omega
      rw [noseed sq]
      simp [E1]
    rcases tight (g + 1) E1 sub (AE ▸ eq) le with ⟨_, c, e⟩ | ⟨_, c, e⟩
    · refine ⟨L, c, Or.inl fun w' x y => ?_⟩
      rw [mE, e]
      simp
    · refine ⟨R, c, Or.inr fun w' x y => ?_⟩
      rw [mE, e]
      simp
  · right
    let E0 : Finset (Fin N × Fin N) := Finset.univ.filter fun z => ¬table h C w z.1 z.2 = true
    have sum : E1.card + E0.card = N * N := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N × Fin N)))
        (fun z => table h C w z.1 z.2 = true)
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at this
      exact this
    have E0c : N * N - A = E0.card := by omega
    have sub : E0 ⊆ lines := by
      intro z hz
      by_contra c
      have o := inl z c
      apply (Finset.mem_filter.mp hz).2
      rw [unnamed _ _ o.1 o.2, v]
    have Sle : S.card ≤ g := by
      rcases mono with m | m
      · exact m
      exfalso
      have all : ∀ x y, table h C w x y = true := by
        intro x y
        refine m _ _ (len w x0 y0) (len w x y) (fun i hi => ?_) v
        rcases cases3 i hi with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, _, rfl⟩
        · change (inp w x0 y0).getD _ false = true → (inp w x y).getD _ false = true
          rw [offL w x0 y0 a ha hx0]
          exact fun q => Bool.noConfusion q
        · change (inp w x0 y0).getD _ false = true → (inp w x y).getD _ false = true
          rw [offR w x0 y0 b hb hy0]
          exact fun q => Bool.noConfusion q
        · change (inp w x0 y0).getD _ false = true → (inp w x y).getD _ false = true
          rw [bitQ w x0 y0 c.val c.isLt, bitQ w x y c.val c.isLt]
          exact id
      have : E0 = ∅ := Finset.filter_eq_empty_iff.mpr fun z _ => not_not.mpr (all _ _)
      rw [this, Finset.card_empty] at E0c
      omega
    have le : L.card + R.card ≤ g := by omega
    refine ⟨E0c ▸ (Finset.card_le_card sub).trans (lc.trans (Nat.mul_le_mul_left N le)), fun eq => ?_⟩
    have mE : ∀ w' x y, table h C w' x y = decide ((x, y) ∉ E0) := by
      intro w' x y
      have sq : S.card ≤ L.card + R.card := by
        have : N * g ≤ N * (L.card + R.card) :=
          (eq.symm.trans E0c) ▸ (Finset.card_le_card sub).trans lc
        have := Nat.le_of_mul_le_mul_left this N0
        omega
      rw [noseed sq]
      simp [E0]
    have comp : ∀ T : Finset (Fin N), T.card = g → Tᶜ.card = N - g := by
      intro T c
      rw [Finset.card_compl, Fintype.card_fin, c]
    rcases tight g E0 sub (E0c ▸ eq) le with ⟨_, c, e⟩ | ⟨_, c, e⟩
    · refine ⟨Lᶜ, comp L c, Or.inl fun w' x y => ?_⟩
      rw [mE, e]
      simp
    · refine ⟨Rᶜ, comp R c, Or.inr fun w' x y => ?_⟩
      rw [mE, e]
      simp
