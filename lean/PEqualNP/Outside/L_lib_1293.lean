import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1293

open PEqualNP.CircuitLowerBounds

def dg : Gate := ⟨GateOp.or, []⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_nil (w : List Bool) : run [] w = w := rfl

lemma run_append (gs1 gs2 : List Gate) (w : List Bool) :
    run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
  simp [run, List.foldl_append]

lemma run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma run_low (gs : List Gate) (w : List Bool) (q : Nat) (hq : q < w.length) :
    (run gs w).getD q false = w.getD q false := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_length]; omega)]
    exact ih

lemma run_prefix (gs1 gs2 : List Gate) (w : List Bool) (q : Nat)
    (hq : q < w.length + gs1.length) :
    (run (gs1 ++ gs2) w).getD q false = (run gs1 w).getD q false := by
  rw [run_append, run_low _ _ _ (by rw [run_length]; exact hq)]

lemma run_ge (gs : List Gate) (w : List Bool) (q : Nat) (hq : w.length + gs.length ≤ q) :
    (run gs w).getD q false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [run_length]; exact hq)]
  rfl

lemma run_snoc_last (gs : List Gate) (g : Gate) (w : List Bool) :
    (run (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (run gs w).getD i false) := by
  rw [run_snoc, List.getD_append_right _ _ _ _ (by rw [run_length]), run_length]
  simp only [Nat.sub_self, List.getD_cons_zero]

lemma run_gate (gs : List Gate) (w : List Bool) (k : Nat) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k dg).inputs, i < w.length + k) :
    (run gs w).getD (w.length + k) false =
      (gs.getD k dg).op.eval ((gs.getD k dg).inputs.map fun i => (run gs w).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [run_snoc]
    by_cases h : k < gs.length
    · have e : (gs ++ [g]).getD k dg = gs.getD k dg := List.getD_append _ _ _ _ h
      rw [e] at hr ⊢
      rw [List.getD_append _ _ _ _ (by rw [run_length]; omega), ih h hr]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [List.getD_append _ _ _ _ (by rw [run_length]; have := hr i hi; omega)]
    · have hk' : k = gs.length := by simp at hk; omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length dg = g := by
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [e] at hr ⊢
      rw [List.getD_append_right _ _ _ _ (by rw [run_length]), run_length]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [List.getD_append _ _ _ _ (by rw [run_length]; have := hr i hi; omega)]

lemma any_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

def ValidGates (m : Nat) (gs : List Gate) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs, 0⟩

def notCnt (gs : List Gate) : Nat :=
  PEqualNP.NotBracket.notCount ⟨gs, 0⟩

lemma valid_nil (m : Nat) : ValidGates m [] := by
  refine ⟨?_, ?_⟩
  · intro g hg; simp at hg
  · intro j hj; simp at hj

lemma valid_snoc (m : Nat) (gs : List Gate) (g : Gate) (hv : ValidGates m gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hins : ∀ i ∈ g.inputs, i < m + gs.length) :
    ValidGates m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hv.1 x hx
    · refine ⟨?_, hlen⟩
      rcases hop with h | h | h <;> simp [h]
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], 0⟩ j =
          PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        exact List.getD_append _ _ _ _ hlt
      rw [e] at hi
      exact hv.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [e] at hi
      exact hins i hi

lemma notCnt_nil : notCnt [] = 0 := rfl

lemma notCnt_snoc_or (gs : List Gate) (ins : List Nat) :
    notCnt (gs ++ [⟨GateOp.or, ins⟩]) = notCnt gs := by
  simp [notCnt, PEqualNP.NotBracket.notCount, List.filter_append]

lemma notCnt_snoc_and (gs : List Gate) (ins : List Nat) :
    notCnt (gs ++ [⟨GateOp.and, ins⟩]) = notCnt gs := by
  simp [notCnt, PEqualNP.NotBracket.notCount, List.filter_append]

lemma notCnt_snoc_not (gs : List Gate) (ins : List Nat) :
    notCnt (gs ++ [⟨GateOp.not, ins⟩]) = notCnt gs + 1 := by
  simp [notCnt, PEqualNP.NotBracket.notCount, List.filter_append]

def orFold (m : Nat) : List Gate → Nat → List Nat → List Gate × Nat
  | gs, acc, [] => (gs, acc)
  | gs, acc, u :: us =>
    orFold m (gs ++ [⟨GateOp.or, [acc, u]⟩]) (m + gs.length) us

lemma orFold_spec (m : Nat) (ws : List Nat) :
    ∀ (gs : List Gate) (acc : Nat),
      ValidGates m gs → acc < m + gs.length → (∀ u ∈ ws, u < m + gs.length) →
      (∃ ext, (orFold m gs acc ws).1 = gs ++ ext) ∧
      (orFold m gs acc ws).1.length = gs.length + ws.length ∧
      ValidGates m (orFold m gs acc ws).1 ∧
      notCnt (orFold m gs acc ws).1 = notCnt gs ∧
      (orFold m gs acc ws).2 < m + (orFold m gs acc ws).1.length ∧
      ∀ (w : List Bool), w.length = m →
        (run (orFold m gs acc ws).1 w).getD (orFold m gs acc ws).2 false =
          ((run gs w).getD acc false || ws.any (fun u => (run gs w).getD u false)) := by
  induction ws with
  | nil =>
    intro gs acc hv hacc _
    refine ⟨⟨[], by simp [orFold]⟩, by simp [orFold], hv, rfl, hacc, ?_⟩
    intro w _
    simp only [orFold, List.any_nil, Bool.or_false]
  | cons u us ih =>
    intro gs acc hv hacc hws
    have hu : u < m + gs.length := hws u (by simp)
    let g0 : Gate := ⟨GateOp.or, [acc, u]⟩
    let gs1 : List Gate := gs ++ [g0]
    let acc1 : Nat := m + gs.length
    have hv1 : ValidGates m gs1 := by
      apply valid_snoc m gs g0 hv (Or.inr (Or.inl rfl)) (by simp [g0])
      intro i hi
      simp [g0] at hi
      rcases hi with rfl | rfl
      · exact hacc
      · exact hu
    have hacc1 : acc1 < m + gs1.length := by
      simp [gs1, acc1]
    have hus : ∀ v ∈ us, v < m + gs1.length := by
      intro v hv'
      have := hws v (by simp [hv'])
      simp [gs1]; omega
    obtain ⟨⟨ext, hext⟩, hlen, hv', hnc, hout, heval⟩ := ih gs1 acc1 hv1 hacc1 hus
    refine ⟨⟨g0 :: ext, by simpa [orFold, gs1, acc1, List.append_assoc] using hext⟩,
      by simp only [orFold]; rw [hlen]; simp [gs1]; omega,
      hv',
      by simp only [orFold]; rw [hnc]; exact notCnt_snoc_or gs [acc, u],
      hout,
      ?_⟩
    intro w hwl
    simp only [orFold]
    rw [heval w hwl]
    have h1 : (run gs1 w).getD acc1 false =
        ((run gs w).getD acc false || (run gs w).getD u false) := by
      have hlast := run_snoc_last gs g0 w
      rw [hwl] at hlast
      simp only [g0, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false] at hlast
      exact hlast
    have h2 : us.any (fun v => (run gs1 w).getD v false) =
        us.any (fun v => (run gs w).getD v false) := by
      apply any_congr
      intro v hv'
      have hvl : v < w.length + gs.length := by rw [hwl]; exact hws v (by simp [hv'])
      exact run_prefix gs [g0] w v hvl
    rw [h1, h2]
    simp only [List.any_cons, Bool.or_assoc]

def selWires (n base : Nat) (P : Fin n → Bool) : List Nat :=
  ((List.finRange n).filter P).map (fun k => base + k.val)

lemma selWires_length_le (n base : Nat) (P : Fin n → Bool) :
    (selWires n base P).length ≤ n := by
  unfold selWires
  rw [List.length_map]
  calc ((List.finRange n).filter P).length
      ≤ (List.finRange n).length := List.length_filter_le P (List.finRange n)
    _ = n := List.length_finRange

lemma selWires_lt (n base : Nat) (P : Fin n → Bool) :
    ∀ u ∈ selWires n base P, u < base + n := by
  intro u hu
  unfold selWires at hu
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hu
  rcases hu with ⟨k, _, rfl⟩
  omega

lemma selWires_any (n base : Nat) (P : Fin n → Bool) (f : Nat → Bool) :
    (selWires n base P).any f = true ↔ ∃ k : Fin n, P k = true ∧ f (base + k.val) = true := by
  unfold selWires
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨u, ⟨k, hk, rfl⟩, hfu⟩
    exact ⟨k, hk, hfu⟩
  · rintro ⟨k, hk, hfk⟩
    exact ⟨base + k.val, ⟨k, hk, rfl⟩, hfk⟩

lemma getD_three_blocks (n : Nat) (a b c : List Bool)
    (ha : a.length = n) (hb : b.length = n) (hc : c.length = n) :
    let xs := (a ++ b ++ c) ++ [false, true]
    xs.length = 3 * n + 2 ∧
    (∀ k : Fin n, xs.getD k.val false = a.getD k.val false) ∧
    (∀ k : Fin n, xs.getD (n + k.val) false = b.getD k.val false) ∧
    (∀ k : Fin n, xs.getD (2 * n + k.val) false = c.getD k.val false) ∧
    xs.getD (3 * n) false = false ∧
    xs.getD (3 * n + 1) false = true := by
  intro xs
  have h1 : (a ++ b).length = 2 * n := by simp [ha, hb]; omega
  have h2 : (a ++ b ++ c).length = 3 * n := by simp [ha, hb, hc]; omega
  refine ⟨by simp [xs, ha, hb, hc]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have hk : k.val < a.length := by omega
    simp only [xs]
    rw [List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ hk]
  · intro k
    simp only [xs]
    rw [List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), ha, Nat.add_sub_cancel_left]
  · intro k
    simp only [xs]
    rw [List.getD_append _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), h1, Nat.add_sub_cancel_left]
  · simp only [xs]
    rw [List.getD_append_right _ _ _ _ (by omega), h2, Nat.sub_self]
    rfl
  · simp only [xs]
    rw [List.getD_append_right _ _ _ _ (by omega), h2]
    have e : 3 * n + 1 - 3 * n = 1 := by omega
    rw [e]
    rfl

lemma ofFn_getD {n : Nat} (f : Fin n → Bool) (k : Fin n) :
    (List.ofFn f).getD k.val false = f k := by
  simp [List.getD_eq_getElem?_getD, k.isLt]

lemma replicate_false_getD (n : Nat) (k : Nat) :
    (List.replicate n false).getD k false = false := by
  by_cases h : k < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

def mkCore {n : Nat} (ordb : Fin n → Fin n → Bool) (i : Fin n) : List Bool :=
  List.ofFn (fun k => ordb k i) ++ List.ofFn (fun k => ordb k i) ++ List.replicate n false

def mkLo {n : Nat} (eqb : Fin n → Fin n → Bool) (i : Fin n) : List Bool :=
  List.ofFn (fun k => eqb k i) ++ List.replicate n false ++ List.replicate n false

def mkHi {n : Nat} (ordb eqb : Fin n → Fin n → Bool) (i : Fin n) : List Bool :=
  List.ofFn (fun k => ordb k i) ++ List.ofFn (fun k => ordb k i) ++ List.ofFn (fun k => eqb k i)

lemma core_blocks {n : Nat} (ordb : Fin n → Fin n → Bool) (i : Fin n) :
    let xs := mkCore ordb i ++ [false, true]
    xs.length = 3 * n + 2 ∧
    (∀ k : Fin n, xs.getD k.val false = ordb k i) ∧
    (∀ k : Fin n, xs.getD (n + k.val) false = ordb k i) ∧
    (∀ k : Fin n, xs.getD (2 * n + k.val) false = false) ∧
    xs.getD (3 * n) false = false ∧
    xs.getD (3 * n + 1) false = true := by
  have hb := getD_three_blocks n (List.ofFn (fun k => ordb k i))
    (List.ofFn (fun k => ordb k i)) (List.replicate n false)
    (by simp) (by simp) (by simp)
  refine ⟨hb.1, fun k => ?_, fun k => ?_, fun k => ?_, hb.2.2.2.2.1, hb.2.2.2.2.2⟩
  · exact (hb.2.1 k).trans (ofFn_getD _ k)
  · exact (hb.2.2.1 k).trans (ofFn_getD _ k)
  · exact (hb.2.2.2.1 k).trans (replicate_false_getD n k.val)

lemma lo_blocks {n : Nat} (eqb : Fin n → Fin n → Bool) (i : Fin n) :
    let xs := mkLo eqb i ++ [false, true]
    xs.length = 3 * n + 2 ∧
    (∀ k : Fin n, xs.getD k.val false = eqb k i) ∧
    (∀ k : Fin n, xs.getD (n + k.val) false = false) ∧
    (∀ k : Fin n, xs.getD (2 * n + k.val) false = false) ∧
    xs.getD (3 * n) false = false ∧
    xs.getD (3 * n + 1) false = true := by
  have hb := getD_three_blocks n (List.ofFn (fun k => eqb k i))
    (List.replicate n false) (List.replicate n false)
    (by simp) (by simp) (by simp)
  refine ⟨hb.1, fun k => ?_, fun k => ?_, fun k => ?_, hb.2.2.2.2.1, hb.2.2.2.2.2⟩
  · exact (hb.2.1 k).trans (ofFn_getD _ k)
  · exact (hb.2.2.1 k).trans (replicate_false_getD n k.val)
  · exact (hb.2.2.2.1 k).trans (replicate_false_getD n k.val)

lemma hi_blocks {n : Nat} (ordb eqb : Fin n → Fin n → Bool) (i : Fin n) :
    let xs := mkHi ordb eqb i ++ [false, true]
    xs.length = 3 * n + 2 ∧
    (∀ k : Fin n, xs.getD k.val false = ordb k i) ∧
    (∀ k : Fin n, xs.getD (n + k.val) false = ordb k i) ∧
    (∀ k : Fin n, xs.getD (2 * n + k.val) false = eqb k i) ∧
    xs.getD (3 * n) false = false ∧
    xs.getD (3 * n + 1) false = true := by
  have hb := getD_three_blocks n (List.ofFn (fun k => ordb k i))
    (List.ofFn (fun k => ordb k i)) (List.ofFn (fun k => eqb k i))
    (by simp) (by simp) (by simp)
  refine ⟨hb.1, fun k => ?_, fun k => ?_, fun k => ?_, hb.2.2.2.2.1, hb.2.2.2.2.2⟩
  · exact (hb.2.1 k).trans (ofFn_getD _ k)
  · exact (hb.2.2.1 k).trans (ofFn_getD _ k)
  · exact (hb.2.2.2.1 k).trans (ofFn_getD _ k)

def leVec (x y : List Bool) : Prop :=
  ∀ q, x.getD q false = true → y.getD q false = true

lemma leVec_core_core {n : Nat} (ord : Fin n → Fin n → Prop)
    (htrans : ∀ i j k, ord i j → ord j k → ord i k)
    (ordb : Fin n → Fin n → Bool) (hordb : ∀ k i, ordb k i = true ↔ ord k i)
    (i j : Fin n) (hij : ord i j) :
    leVec (mkCore ordb i ++ [false, true]) (mkCore ordb j ++ [false, true]) := by
  have hi := core_blocks ordb i
  have hj := core_blocks ordb j
  intro q hq
  by_cases h1 : q < n
  · let k : Fin n := ⟨q, h1⟩
    rw [hi.2.1 k] at hq
    rw [hj.2.1 k]
    exact (hordb k j).mpr (htrans k i j ((hordb k i).mp hq) hij)
  · by_cases h2 : q < 2 * n
    · let k : Fin n := ⟨q - n, by omega⟩
      have eqk : q = n + k.val := by simp [k]; omega
      rw [eqk] at hq ⊢
      rw [hi.2.2.1 k] at hq
      rw [hj.2.2.1 k]
      exact (hordb k j).mpr (htrans k i j ((hordb k i).mp hq) hij)
    · by_cases h3 : q < 3 * n
      · let k : Fin n := ⟨q - 2 * n, by omega⟩
        have eqk : q = 2 * n + k.val := by simp [k]; omega
        rw [eqk, hi.2.2.2.1 k] at hq
        contradiction
      · by_cases h4 : q = 3 * n
        · subst h4; rw [hi.2.2.2.2.1] at hq; contradiction
        · by_cases h5 : q = 3 * n + 1
          · subst h5; exact hj.2.2.2.2.2
          · have hge : (mkCore ordb i ++ [false, true]).length ≤ q := by
              have := hi.1; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hq
            contradiction

lemma leVec_lo_core {n : Nat} (ord : Fin n → Fin n → Prop)
    (hrefl : ∀ i, ord i i)
    (ordb eqb : Fin n → Fin n → Bool)
    (hordb : ∀ k i, ordb k i = true ↔ ord k i)
    (heqb : ∀ k i, eqb k i = true ↔ k = i)
    (i : Fin n) :
    leVec (mkLo eqb i ++ [false, true]) (mkCore ordb i ++ [false, true]) := by
  have hi := lo_blocks eqb i
  have hj := core_blocks ordb i
  intro q hq
  by_cases h1 : q < n
  · let k : Fin n := ⟨q, h1⟩
    rw [hi.2.1 k] at hq
    rw [hj.2.1 k]
    have hki : k = i := (heqb k i).mp hq
    subst hki
    exact (hordb k k).mpr (hrefl k)
  · by_cases h2 : q < 2 * n
    · let k : Fin n := ⟨q - n, by omega⟩
      have eqk : q = n + k.val := by simp [k]; omega
      rw [eqk, hi.2.2.1 k] at hq
      contradiction
    · by_cases h3 : q < 3 * n
      · let k : Fin n := ⟨q - 2 * n, by omega⟩
        have eqk : q = 2 * n + k.val := by simp [k]; omega
        rw [eqk, hi.2.2.2.1 k] at hq
        contradiction
      · by_cases h4 : q = 3 * n
        · subst h4; rw [hi.2.2.2.2.1] at hq; contradiction
        · by_cases h5 : q = 3 * n + 1
          · subst h5; exact hj.2.2.2.2.2
          · have hge : (mkLo eqb i ++ [false, true]).length ≤ q := by
              have := hi.1; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hq
            contradiction

lemma leVec_core_hi {n : Nat}
    (ordb eqb : Fin n → Fin n → Bool) (i : Fin n) :
    leVec (mkCore ordb i ++ [false, true]) (mkHi ordb eqb i ++ [false, true]) := by
  have hi := core_blocks ordb i
  have hj := hi_blocks ordb eqb i
  intro q hq
  by_cases h1 : q < n
  · let k : Fin n := ⟨q, h1⟩
    rw [hi.2.1 k] at hq
    rw [hj.2.1 k]
    exact hq
  · by_cases h2 : q < 2 * n
    · let k : Fin n := ⟨q - n, by omega⟩
      have eqk : q = n + k.val := by simp [k]; omega
      rw [eqk] at hq ⊢
      rw [hi.2.2.1 k] at hq
      rw [hj.2.2.1 k]
      exact hq
    · by_cases h3 : q < 3 * n
      · let k : Fin n := ⟨q - 2 * n, by omega⟩
        have eqk : q = 2 * n + k.val := by simp [k]; omega
        rw [eqk, hi.2.2.2.1 k] at hq
        contradiction
      · by_cases h4 : q = 3 * n
        · subst h4; rw [hi.2.2.2.2.1] at hq; contradiction
        · by_cases h5 : q = 3 * n + 1
          · subst h5; exact hj.2.2.2.2.2
          · have hge : (mkCore ordb i ++ [false, true]).length ≤ q := by
              have := hi.1; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hq
            contradiction

lemma run_mono_prefix (gs : List Gate) (x y : List Bool)
    (hxy : leVec x y) (hlen : x.length = y.length)
    (hfit : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack x.length ⟨gs, 0⟩)
    (K : Nat) (hno : ∀ j < K, j < gs.length → (gs.getD j dg).op ≠ GateOp.not) :
    ∀ q < x.length + K, (run gs x).getD q false = true → (run gs y).getD q false = true := by
  intro q
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    intro hqK hqx
    by_cases hlt : q < x.length
    · rw [run_low gs x q hlt] at hqx
      rw [run_low gs y q (by omega)]
      exact hxy q hqx
    · let j := q - x.length
      have hqj : q = x.length + j := by omega
      have hqy : q = y.length + j := by omega
      by_cases hj : j < gs.length
      · have hr : ∀ i ∈ (gs.getD j dg).inputs, i < x.length + j := hrb j hj
        have hry : ∀ i ∈ (gs.getD j dg).inputs, i < y.length + j := by
          intro i hi; have := hr i hi; omega
        rw [hqj] at hqx
        rw [run_gate gs x j hj hr] at hqx
        rw [hqy, run_gate gs y j hj hry]
        have hmem : gs.getD j dg ∈ gs := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        have hop := (hfit (gs.getD j dg) hmem).1
        have hne := hno j (by omega) hj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hand | hor | hnot
        · rw [hand] at hqx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hqx ⊢
          rintro b ⟨r, hr_in, rfl⟩
          have hr_lt : r < q := by have := hr r hr_in; omega
          exact ih r hr_lt (by omega) (hqx _ ⟨r, hr_in, rfl⟩)
        · rw [hor] at hqx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hqx ⊢
          rcases hqx with ⟨_, ⟨r, hr_in, rfl⟩, hrx⟩
          have hr_lt : r < q := by have := hr r hr_in; omega
          exact ⟨_, ⟨r, hr_in, rfl⟩, ih r hr_lt (by omega) hrx⟩
        · exact absurd hnot hne
      · rw [run_ge gs x q (by omega)] at hqx
        contradiction

lemma run_mono_all (gs : List Gate) (x y : List Bool)
    (hxy : leVec x y) (hlen : x.length = y.length)
    (hfit : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack x.length ⟨gs, 0⟩)
    (hnot : ∀ j < gs.length, (gs.getD j dg).op = GateOp.not →
      (run gs x).getD (x.length + j) false = true →
      (run gs y).getD (y.length + j) false = true) :
    ∀ q, (run gs x).getD q false = true → (run gs y).getD q false = true := by
  intro q
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    intro hqx
    by_cases hlt : q < x.length
    · rw [run_low gs x q hlt] at hqx
      rw [run_low gs y q (by omega)]
      exact hxy q hqx
    · let j := q - x.length
      have hqj : q = x.length + j := by omega
      have hqy : q = y.length + j := by omega
      by_cases hj : j < gs.length
      · have hmem : gs.getD j dg ∈ gs := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        have hop := (hfit (gs.getD j dg) hmem).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hand | hor | hnotop
        · have hr : ∀ i ∈ (gs.getD j dg).inputs, i < x.length + j := hrb j hj
          have hry : ∀ i ∈ (gs.getD j dg).inputs, i < y.length + j := by
            intro i hi; have := hr i hi; omega
          rw [hqj] at hqx
          rw [run_gate gs x j hj hr] at hqx
          rw [hqy, run_gate gs y j hj hry]
          rw [hand] at hqx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hqx ⊢
          rintro b ⟨r, hr_in, rfl⟩
          have hr_lt : r < q := by have := hr r hr_in; omega
          exact ih r hr_lt (hqx _ ⟨r, hr_in, rfl⟩)
        · have hr : ∀ i ∈ (gs.getD j dg).inputs, i < x.length + j := hrb j hj
          have hry : ∀ i ∈ (gs.getD j dg).inputs, i < y.length + j := by
            intro i hi; have := hr i hi; omega
          rw [hqj] at hqx
          rw [run_gate gs x j hj hr] at hqx
          rw [hqy, run_gate gs y j hj hry]
          rw [hor] at hqx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hqx ⊢
          rcases hqx with ⟨_, ⟨r, hr_in, rfl⟩, hrx⟩
          have hr_lt : r < q := by have := hr r hr_in; omega
          exact ⟨_, ⟨r, hr_in, rfl⟩, ih r hr_lt hrx⟩
        · rw [hqj] at hqx
          rw [hqy]
          exact hnot j hj hnotop hqx
      · rw [run_ge gs x q (by omega)] at hqx
        contradiction

lemma pair_eq_of_mono (gs : List Gate) (x y : List Bool) (out p : Nat)
    (hmono : ∀ q, (run gs x).getD q false = true → (run gs y).getD q false = true)
    (hx : (run gs x).getD p false = !((run gs x).getD out false))
    (hy : (run gs y).getD p false = !((run gs y).getD out false)) :
    (run gs x).getD out false = (run gs y).getD out false := by
  cases h1 : (run gs x).getD out false <;> cases h2 : (run gs y).getD out false
  · rfl
  · have hp : (run gs x).getD p false = true := by rw [hx, h1]; rfl
    have hpy := hmono p hp
    rw [hy, h2] at hpy
    contradiction
  · have hmy := hmono out h1
    rw [h2] at hmy
    contradiction
  · rfl

lemma notCnt_zero_no_not (gs : List Gate) (h0 : notCnt gs = 0) :
    ∀ j < gs.length, (gs.getD j dg).op ≠ GateOp.not := by
  intro j hj heq
  have hmem : gs.getD j dg ∈ gs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  let pred : Gate → Bool := fun g =>
    @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)
  have hnil : gs.filter pred = [] := List.length_eq_zero_iff.mp h0
  have hpred : pred (gs.getD j dg) = true := by
    dsimp only [pred]
    exact @decide_eq_true _ (lineDegreeGateOpDecEq _ _) heq
  have hmemf : gs.getD j dg ∈ gs.filter pred :=
    List.mem_filter.mpr ⟨hmem, hpred⟩
  rw [hnil] at hmemf
  simp at hmemf

lemma filter_len_one {α : Type*} (l : List α) (p : α → Bool) (h1 : (l.filter p).length = 1)
    (d : α) :
    ∃ j0 < l.length, p (l.getD j0 d) = true ∧
      ∀ j < l.length, p (l.getD j d) = true → j = j0 := by
  induction l with
  | nil => simp at h1
  | cons a t ih =>
    cases hpa : p a
    · simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte] at h1
      obtain ⟨j0, hj0, hp0, huniq⟩ := ih h1
      refine ⟨j0 + 1, by simp; omega, ?_, ?_⟩
      · simpa only [List.getD_cons_succ] using hp0
      · intro j hj hpj
        cases j with
        | zero => simp only [List.getD_cons_zero] at hpj; rw [hpa] at hpj; contradiction
        | succ k =>
          have hk : k < t.length := by simp at hj; omega
          simp only [List.getD_cons_succ] at hpj
          have := huniq k hk hpj
          omega
    · simp only [List.filter_cons, hpa, ↓reduceIte, List.length_cons] at h1
      have h0 : (t.filter p).length = 0 := by omega
      have hnil : t.filter p = [] := List.length_eq_zero_iff.mp h0
      refine ⟨0, by simp, ?_, ?_⟩
      · simpa only [List.getD_cons_zero] using hpa
      · intro j hj hpj
        cases j with
        | zero => rfl
        | succ k =>
          have hk : k < t.length := by simp at hj; omega
          simp only [List.getD_cons_succ] at hpj
          have hmem : t.getD k d ∈ t := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
            exact List.getElem_mem hk
          have hmemf : t.getD k d ∈ t.filter p :=
            List.mem_filter.mpr ⟨hmem, hpj⟩
          rw [hnil] at hmemf
          simp at hmemf

lemma notCnt_one_unique (gs : List Gate) (h1 : notCnt gs = 1) :
    ∃ j0 < gs.length, (gs.getD j0 dg).op = GateOp.not ∧
      ∀ j < gs.length, (gs.getD j dg).op = GateOp.not → j = j0 := by
  let pred : Gate → Bool := fun g =>
    @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)
  obtain ⟨j0, hj0, hp0, huniq⟩ := filter_len_one gs pred h1 dg
  refine ⟨j0, hj0, @of_decide_eq_true _ (lineDegreeGateOpDecEq _ _) hp0, ?_⟩
  intro j hj hop
  exact huniq j hj (@decide_eq_true _ (lineDegreeGateOpDecEq _ _) hop)

lemma not_gate_anti (gs : List Gate) (x y : List Bool)
    (hxy : leVec x y) (hlen : x.length = y.length)
    (hfit : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack x.length ⟨gs, 0⟩)
    (j0 : Nat) (hj0 : j0 < gs.length)
    (hop : (gs.getD j0 dg).op = GateOp.not)
    (huniq : ∀ j < gs.length, (gs.getD j dg).op = GateOp.not → j = j0) :
    (run gs y).getD (y.length + j0) false = true →
    (run gs x).getD (x.length + j0) false = true := by
  have hno : ∀ j < j0, j < gs.length → (gs.getD j dg).op ≠ GateOp.not := by
    intro j hjlt hjlen heq
    have := huniq j hjlen heq
    omega
  have hpre := run_mono_prefix gs x y hxy hlen hfit hrb j0 hno
  have hr : ∀ i ∈ (gs.getD j0 dg).inputs, i < x.length + j0 := hrb j0 hj0
  have hry : ∀ i ∈ (gs.getD j0 dg).inputs, i < y.length + j0 := by
    intro i hi; have := hr i hi; omega
  rw [run_gate gs y j0 hj0 hry, run_gate gs x j0 hj0 hr, hop]
  cases hins : (gs.getD j0 dg).inputs with
  | nil => simp [GateOp.eval]
  | cons r rs =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    have hrlt : r < x.length + j0 := hr r (by rw [hins]; simp)
    cases hrx : (run gs x).getD r false
    · simp
    · have hry' := hpre r hrlt hrx
      rw [hry']
      simp

lemma ext_of_notCount_le_one {n : Nat}
    (ord : Fin n → Fin n → Prop) (pin : Fin n → Option (Bool × Bool))
    (hrefl : ∀ i, ord i i) (htrans : ∀ i j k, ord i j → ord j k → ord i k)
    (ordb eqb : Fin n → Fin n → Bool)
    (hordb : ∀ k i, ordb k i = true ↔ ord k i)
    (heqb : ∀ k i, eqb k i = true ↔ k = i)
    (C : Circuit) (p : Nat)
    (hfit : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (3 * n + 2) C)
    (hcomp : ∀ i, (run C.gates (mkCore ordb i ++ [false, true])).getD p false =
      !((run C.gates (mkCore ordb i ++ [false, true])).getD C.output false))
    (hpin : ∀ i v, pin i = some v →
      (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = v.2 ∧
      (run C.gates ((if v.1 then mkLo eqb i else mkHi ordb eqb i) ++ [false, true])).getD C.output false = !v.2 ∧
      (run C.gates ((if v.1 then mkLo eqb i else mkHi ordb eqb i) ++ [false, true])).getD p false = v.2)
    (hnc : PEqualNP.NotBracket.notCount C ≤ 1) :
    ∃ g : Fin n → Bool × Bool,
      (∀ i j, ord i j → g i = g j ∨ ((g i).1 = false ∧ (g j).1 = true)) ∧
      ∀ i v, pin i = some v → g i = v := by
  have hlen_core : ∀ i, (mkCore ordb i ++ [false, true]).length = 3 * n + 2 :=
    fun i => (core_blocks ordb i).1
  have hlen_lo : ∀ i, (mkLo eqb i ++ [false, true]).length = 3 * n + 2 :=
    fun i => (lo_blocks eqb i).1
  have hlen_hi : ∀ i, (mkHi ordb eqb i ++ [false, true]).length = 3 * n + 2 :=
    fun i => (hi_blocks ordb eqb i).1
  have hfit' : PEqualNP.MetaComplexity.FanInTwo ⟨C.gates, 0⟩ := hfit
  have hrb' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (3 * n + 2) ⟨C.gates, 0⟩ := hrb
  have hnc_cases : notCnt C.gates = 0 ∨ notCnt C.gates = 1 := by
    change PEqualNP.NotBracket.notCount C = 0 ∨ PEqualNP.NotBracket.notCount C = 1
    omega
  rcases hnc_cases with h0 | h1
  · have hno := notCnt_zero_no_not C.gates h0
    refine ⟨fun i => (false, (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false), ?_, ?_⟩
    · intro i j hij
      left
      have hmono := run_mono_all C.gates
        (mkCore ordb i ++ [false, true]) (mkCore ordb j ++ [false, true])
        (leVec_core_core ord htrans ordb hordb i j hij)
        (by rw [hlen_core, hlen_core]) hfit' (by rw [hlen_core]; exact hrb')
        (fun k hk hop => absurd hop (hno k hk))
      have heq := pair_eq_of_mono C.gates _ _ C.output p hmono (hcomp i) (hcomp j)
      exact Prod.ext rfl heq
    · intro i v hv
      have hp := hpin i v hv
      cases hv1 : v.1
      · simp only [hv1, Bool.false_eq_true, ↓reduceIte] at hp
        have hmono := run_mono_all C.gates
          (mkCore ordb i ++ [false, true]) (mkHi ordb eqb i ++ [false, true])
          (leVec_core_hi ordb eqb i)
          (by rw [hlen_core, hlen_hi]) hfit' (by rw [hlen_core]; exact hrb')
          (fun k hk hop => absurd hop (hno k hk))
        have hcy : (run C.gates (mkHi ordb eqb i ++ [false, true])).getD p false =
            !((run C.gates (mkHi ordb eqb i ++ [false, true])).getD C.output false) := by
          rw [hp.2.1, hp.2.2, Bool.not_not]
        have heq := pair_eq_of_mono C.gates _ _ C.output p hmono (hcomp i) hcy
        rw [hp.1, hp.2.1] at heq
        cases hv2 : v.2 <;> simp [hv2] at heq
      · simp only [hv1, ↓reduceIte] at hp
        have hmono := run_mono_all C.gates
          (mkLo eqb i ++ [false, true]) (mkCore ordb i ++ [false, true])
          (leVec_lo_core ord hrefl ordb eqb hordb heqb i)
          (by rw [hlen_lo, hlen_core]) hfit' (by rw [hlen_lo]; exact hrb')
          (fun k hk hop => absurd hop (hno k hk))
        have hcy : (run C.gates (mkLo eqb i ++ [false, true])).getD p false =
            !((run C.gates (mkLo eqb i ++ [false, true])).getD C.output false) := by
          rw [hp.2.1, hp.2.2, Bool.not_not]
        have heq := pair_eq_of_mono C.gates _ _ C.output p hmono hcy (hcomp i)
        rw [hp.1, hp.2.1] at heq
        cases hv2 : v.2 <;> simp [hv2] at heq
  · obtain ⟨j0, hj0, hop0, huniq0⟩ := notCnt_one_unique C.gates h1
    let g : Fin n → Bool × Bool := fun i =>
      (!((run C.gates (mkCore ordb i ++ [false, true])).getD (3 * n + 2 + j0) false),
        (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false)
    refine ⟨g, ?_, ?_⟩
    · intro i j hij
      have hanti := not_gate_anti C.gates
        (mkCore ordb i ++ [false, true]) (mkCore ordb j ++ [false, true])
        (leVec_core_core ord htrans ordb hordb i j hij)
        (by rw [hlen_core, hlen_core]) hfit' (by rw [hlen_core]; exact hrb')
        j0 hj0 hop0 huniq0
      rw [hlen_core, hlen_core] at hanti
      cases hi0 : (run C.gates (mkCore ordb i ++ [false, true])).getD (3 * n + 2 + j0) false <;>
      cases hj0' : (run C.gates (mkCore ordb j ++ [false, true])).getD (3 * n + 2 + j0) false
      · left
        have hmono := run_mono_all C.gates
          (mkCore ordb i ++ [false, true]) (mkCore ordb j ++ [false, true])
          (leVec_core_core ord htrans ordb hordb i j hij)
          (by rw [hlen_core, hlen_core]) hfit' (by rw [hlen_core]; exact hrb')
          (fun k hk hop => by
            have heqk := huniq0 k hk hop
            subst heqk
            rw [hlen_core, hlen_core, hi0]; intro h; contradiction)
        have heq := pair_eq_of_mono C.gates _ _ C.output p hmono (hcomp i) (hcomp j)
        exact Prod.ext (by dsimp only [g]; rw [hi0, hj0']) heq
      · have := hanti hj0'
        rw [hi0] at this; contradiction
      · right
        exact ⟨by dsimp only [g]; rw [hi0]; rfl, by dsimp only [g]; rw [hj0']; rfl⟩
      · left
        have hmono := run_mono_all C.gates
          (mkCore ordb i ++ [false, true]) (mkCore ordb j ++ [false, true])
          (leVec_core_core ord htrans ordb hordb i j hij)
          (by rw [hlen_core, hlen_core]) hfit' (by rw [hlen_core]; exact hrb')
          (fun k hk hop => by
            have heqk := huniq0 k hk hop
            subst heqk
            rw [hlen_core, hlen_core, hj0']; intro _; rfl)
        have heq := pair_eq_of_mono C.gates _ _ C.output p hmono (hcomp i) (hcomp j)
        exact Prod.ext (by dsimp only [g]; rw [hi0, hj0']) heq
    · intro i v hv
      have hp := hpin i v hv
      cases hv1 : v.1
      · simp only [hv1, Bool.false_eq_true, ↓reduceIte] at hp
        have hval : (run C.gates (mkCore ordb i ++ [false, true])).getD (3 * n + 2 + j0) false = true := by
          cases hcur : (run C.gates (mkCore ordb i ++ [false, true])).getD (3 * n + 2 + j0) false
          · have hmono := run_mono_all C.gates
              (mkCore ordb i ++ [false, true]) (mkHi ordb eqb i ++ [false, true])
              (leVec_core_hi ordb eqb i)
              (by rw [hlen_core, hlen_hi]) hfit' (by rw [hlen_core]; exact hrb')
              (fun k hk hop => by
                have heqk := huniq0 k hk hop
                subst heqk
                rw [hlen_core, hcur]; intro h; contradiction)
            have hcy : (run C.gates (mkHi ordb eqb i ++ [false, true])).getD p false =
                !((run C.gates (mkHi ordb eqb i ++ [false, true])).getD C.output false) := by
              rw [hp.2.1, hp.2.2, Bool.not_not]
            have heq := pair_eq_of_mono C.gates _ _ C.output p hmono (hcomp i) hcy
            rw [hp.1, hp.2.1] at heq
            cases hv2 : v.2 <;> simp [hv2] at heq
          · rfl
        have hfst : (g i).1 = v.1 := by dsimp only [g]; rw [hval, hv1]; rfl
        have hsnd : (g i).2 = v.2 := by dsimp only [g]; exact hp.1
        exact Prod.ext hfst hsnd
      · simp only [hv1, ↓reduceIte] at hp
        have hval : (run C.gates (mkCore ordb i ++ [false, true])).getD (3 * n + 2 + j0) false = false := by
          cases hcur : (run C.gates (mkCore ordb i ++ [false, true])).getD (3 * n + 2 + j0) false
          · rfl
          · have hmono := run_mono_all C.gates
              (mkLo eqb i ++ [false, true]) (mkCore ordb i ++ [false, true])
              (leVec_lo_core ord hrefl ordb eqb hordb heqb i)
              (by rw [hlen_lo, hlen_core]) hfit' (by rw [hlen_lo]; exact hrb')
              (fun k hk hop => by
                have heqk := huniq0 k hk hop
                subst heqk
                rw [hlen_core, hcur]; intro _; rfl)
            have hcy : (run C.gates (mkLo eqb i ++ [false, true])).getD p false =
                !((run C.gates (mkLo eqb i ++ [false, true])).getD C.output false) := by
              rw [hp.2.1, hp.2.2, Bool.not_not]
            have heq := pair_eq_of_mono C.gates _ _ C.output p hmono hcy (hcomp i)
            rw [hp.1, hp.2.1] at heq
            cases hv2 : v.2 <;> simp [hv2] at heq
        have hfst : (g i).1 = v.1 := by dsimp only [g]; rw [hval, hv1]; rfl
        have hsnd : (g i).2 = v.2 := by dsimp only [g]; exact hp.1
        exact Prod.ext hfst hsnd

def mkBranch (n : Nat) (g : Fin n → Bool × Bool) (wN : Nat) (gs : List Gate) (c : Bool) :
    List Gate × Nat :=
  let m := 3 * n + 2
  let wF := 3 * n
  let r1 := orFold m gs wF (selWires n n (fun k => !(g k).1 && ((g k).2 == c)))
  let r2 := orFold m r1.1 r1.2 (selWires n 0 (fun k => (g k).1 && ((g k).2 == !c)))
  let wA := m + r2.1.length
  let g3 := r2.1 ++ [⟨GateOp.and, [wN, r2.2]⟩]
  let r4 := orFold m g3 wA (selWires n n (fun k => (g k).1 && ((g k).2 == c)))
  orFold m r4.1 r4.2 (selWires n (2 * n) (fun k => !(g k).1 && ((g k).2 == !c)))

lemma mkBranch_spec (n : Nat) (g : Fin n → Bool × Bool) (wN : Nat) (gs : List Gate) (c : Bool)
    (hv : ValidGates (3 * n + 2) gs) (hwN : wN < 3 * n + 2 + gs.length) :
    (∃ ext, (mkBranch n g wN gs c).1 = gs ++ ext) ∧
    (mkBranch n g wN gs c).1.length ≤ gs.length + 4 * n + 1 ∧
    ValidGates (3 * n + 2) (mkBranch n g wN gs c).1 ∧
    notCnt (mkBranch n g wN gs c).1 = notCnt gs ∧
    (mkBranch n g wN gs c).2 < 3 * n + 2 + (mkBranch n g wN gs c).1.length ∧
    ∀ (w : List Bool), w.length = 3 * n + 2 → w.getD (3 * n) false = false →
      (run (mkBranch n g wN gs c).1 w).getD (mkBranch n g wN gs c).2 false =
        ((((run gs w).getD wN false &&
          ((selWires n n (fun k => !(g k).1 && ((g k).2 == c))).any (fun u => w.getD u false) ||
           (selWires n 0 (fun k => (g k).1 && ((g k).2 == !c))).any (fun u => w.getD u false))) ||
         (selWires n n (fun k => (g k).1 && ((g k).2 == c))).any (fun u => w.getD u false)) ||
         (selWires n (2 * n) (fun k => !(g k).1 && ((g k).2 == !c))).any (fun u => w.getD u false)) := by
  let m := 3 * n + 2
  let wF := 3 * n
  let ws1 := selWires n n (fun k => !(g k).1 && ((g k).2 == c))
  let ws2 := selWires n 0 (fun k => (g k).1 && ((g k).2 == !c))
  let ws4 := selWires n n (fun k => (g k).1 && ((g k).2 == c))
  let ws5 := selWires n (2 * n) (fun k => !(g k).1 && ((g k).2 == !c))
  let r1 := orFold m gs wF ws1
  have h1 := orFold_spec m ws1 gs wF hv (by omega)
    (fun u hu => by have := selWires_lt n n _ u hu; omega)
  have he1' : ∃ ext, r1.1 = gs ++ ext := h1.1
  obtain ⟨e1, he1⟩ := he1'
  have hl1 : r1.1.length = gs.length + ws1.length := h1.2.1
  have hv1 : ValidGates m r1.1 := h1.2.2.1
  have hn1 : notCnt r1.1 = notCnt gs := h1.2.2.2.1
  have ho1 : r1.2 < m + r1.1.length := h1.2.2.2.2.1
  have hev1 := h1.2.2.2.2.2
  let r2 := orFold m r1.1 r1.2 ws2
  have h2 := orFold_spec m ws2 r1.1 r1.2 hv1 ho1
    (fun u hu => by have := selWires_lt n 0 _ u hu; omega)
  have he2' : ∃ ext, r2.1 = r1.1 ++ ext := h2.1
  obtain ⟨e2, he2⟩ := he2'
  have hl2 : r2.1.length = r1.1.length + ws2.length := h2.2.1
  have hv2 : ValidGates m r2.1 := h2.2.2.1
  have hn2 : notCnt r2.1 = notCnt r1.1 := h2.2.2.2.1
  have ho2 : r2.2 < m + r2.1.length := h2.2.2.2.2.1
  have hev2 := h2.2.2.2.2.2
  let gAnd : Gate := ⟨GateOp.and, [wN, r2.2]⟩
  let g3 := r2.1 ++ [gAnd]
  let wA := m + r2.1.length
  have hwN2 : wN < m + r2.1.length := by omega
  have hv3 : ValidGates m g3 := by
    apply valid_snoc m r2.1 gAnd hv2 (Or.inl rfl) (by simp [gAnd])
    intro i hi; simp [gAnd] at hi; rcases hi with rfl | rfl; exact hwN2; exact ho2
  have hn3 : notCnt g3 = notCnt r2.1 := notCnt_snoc_and r2.1 [wN, r2.2]
  have hl3 : g3.length = r2.1.length + 1 := by simp [g3]
  have hwA3 : wA < m + g3.length := by simp [g3, wA]
  let r4 := orFold m g3 wA ws4
  have h4 := orFold_spec m ws4 g3 wA hv3 hwA3
    (fun u hu => by have := selWires_lt n n _ u hu; omega)
  have he4' : ∃ ext, r4.1 = g3 ++ ext := h4.1
  obtain ⟨e4, he4⟩ := he4'
  have hl4 : r4.1.length = g3.length + ws4.length := h4.2.1
  have hv4 : ValidGates m r4.1 := h4.2.2.1
  have hn4 : notCnt r4.1 = notCnt g3 := h4.2.2.2.1
  have ho4 : r4.2 < m + r4.1.length := h4.2.2.2.2.1
  have hev4 := h4.2.2.2.2.2
  let r5 := orFold m r4.1 r4.2 ws5
  have h5 := orFold_spec m ws5 r4.1 r4.2 hv4 ho4
    (fun u hu => by have := selWires_lt n (2 * n) _ u hu; omega)
  have he5' : ∃ ext, r5.1 = r4.1 ++ ext := h5.1
  obtain ⟨e5, he5⟩ := he5'
  have hl5 : r5.1.length = r4.1.length + ws5.length := h5.2.1
  have hv5 : ValidGates m r5.1 := h5.2.2.1
  have hn5 : notCnt r5.1 = notCnt r4.1 := h5.2.2.2.1
  have ho5 : r5.2 < m + r5.1.length := h5.2.2.2.2.1
  have hev5 := h5.2.2.2.2.2
  have hlen1 : ws1.length ≤ n := selWires_length_le n n _
  have hlen2 : ws2.length ≤ n := selWires_length_le n 0 _
  have hlen4 : ws4.length ≤ n := selWires_length_le n n _
  have hlen5 : ws5.length ≤ n := selWires_length_le n (2 * n) _
  refine ⟨⟨e1 ++ e2 ++ [gAnd] ++ e4 ++ e5, ?_⟩, ?_, hv5, ?_, ho5, ?_⟩
  · change r5.1 = gs ++ (e1 ++ e2 ++ [gAnd] ++ e4 ++ e5)
    rw [he5, he4]
    change r2.1 ++ [gAnd] ++ e4 ++ e5 = _
    rw [he2, he1]
    simp [List.append_assoc]
  · change r5.1.length ≤ gs.length + 4 * n + 1
    omega
  · change notCnt r5.1 = notCnt gs
    rw [hn5, hn4, hn3, hn2, hn1]
  · intro w hwl hwF
    change (run r5.1 w).getD r5.2 false = _
    have h5e : (run r5.1 w).getD r5.2 false =
        ((run r4.1 w).getD r4.2 false || ws5.any (fun u => (run r4.1 w).getD u false)) :=
      hev5 w hwl
    have h4e : (run r4.1 w).getD r4.2 false =
        ((run g3 w).getD wA false || ws4.any (fun u => (run g3 w).getD u false)) :=
      hev4 w hwl
    have h2e : (run r2.1 w).getD r2.2 false =
        ((run r1.1 w).getD r1.2 false || ws2.any (fun u => (run r1.1 w).getD u false)) :=
      hev2 w hwl
    have h1e : (run r1.1 w).getD r1.2 false =
        ((run gs w).getD wF false || ws1.any (fun u => (run gs w).getD u false)) :=
      hev1 w hwl
    have hlow : ∀ (gl : List Gate) (base : Nat) (P : Fin n → Bool),
        base + n ≤ m →
        (selWires n base P).any (fun u => (run gl w).getD u false) =
        (selWires n base P).any (fun u => w.getD u false) := by
      intro gl base P hbn
      apply any_congr
      intro u hu
      have ult := selWires_lt n base P u hu
      exact run_low gl w u (by omega)
    have hrunF : (run gs w).getD wF false = false := by
      rw [run_low gs w wF (by omega), hwF]
    have hrunN : (run r2.1 w).getD wN false = (run gs w).getD wN false := by
      have he12 : r2.1 = gs ++ (e1 ++ e2) := by
        rw [he2, he1, List.append_assoc]
      rw [he12]
      exact run_prefix gs (e1 ++ e2) w wN (by rw [hwl]; exact hwN)
    have hrunA : (run g3 w).getD wA false =
        ((run r2.1 w).getD wN false && (run r2.1 w).getD r2.2 false) := by
      have hlast := run_snoc_last r2.1 gAnd w
      rw [hwl] at hlast
      simp only [gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at hlast
      exact hlast
    rw [h5e, h4e, hrunA, hrunN, h2e, h1e, hrunF, Bool.false_or]
    rw [hlow gs n _ (by omega), hlow r1.1 0 _ (by omega),
        hlow g3 n _ (by omega), hlow r4.1 (2 * n) _ (by omega)]

lemma build_one_not {n : Nat}
    (ord : Fin n → Fin n → Prop) (pin : Fin n → Option (Bool × Bool))
    (hrefl : ∀ i, ord i i)
    (ordb eqb : Fin n → Fin n → Bool)
    (hordb : ∀ k i, ordb k i = true ↔ ord k i)
    (heqb : ∀ k i, eqb k i = true ↔ k = i)
    (g : Fin n → Bool × Bool)
    (hmono : ∀ i j, ord i j → g i = g j ∨ ((g i).1 = false ∧ (g j).1 = true))
    (hpin : ∀ i v, pin i = some v → g i = v) :
    ∃ C p,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (3 * n + 2) C ∧
      C.output < 3 * n + 2 + C.size ∧ p < 3 * n + 2 + C.size ∧
      (∀ i, (run C.gates (mkCore ordb i ++ [false, true])).getD p false =
        !((run C.gates (mkCore ordb i ++ [false, true])).getD C.output false)) ∧
      (∀ i v, pin i = some v →
        (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = v.2 ∧
        (run C.gates ((if v.1 then mkLo eqb i else mkHi ordb eqb i) ++ [false, true])).getD C.output false = !v.2 ∧
        (run C.gates ((if v.1 then mkLo eqb i else mkHi ordb eqb i) ++ [false, true])).getD p false = v.2) ∧
      C.size ≤ 32 * (n + 1) ^ 2 ∧
      PEqualNP.NotBracket.notCount C = 1 ∧
      ∃ j : Fin C.size,
        (C.gates.getD j.val dg).op = GateOp.not ∧
        ∀ i, (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = (g i).2 ∧
             (run C.gates (mkCore ordb i ++ [false, true])).getD (3 * n + 2 + j.val) false = !(g i).1 := by
  let m := 3 * n + 2
  let wF := 3 * n
  let wsH1 := selWires n n (fun k => (g k).1)
  let wsH2 := selWires n (2 * n) (fun _ => true)
  let rH1 := orFold m [] wF wsH1
  have hh1 := orFold_spec m wsH1 [] wF (valid_nil m) (by omega)
    (fun u hu => by have := selWires_lt n n _ u hu; omega)
  have hlh1 : rH1.1.length = wsH1.length := by simpa using hh1.2.1
  have hvh1 : ValidGates m rH1.1 := hh1.2.2.1
  have hnh1 : notCnt rH1.1 = 0 := hh1.2.2.2.1
  have hoh1 : rH1.2 < m + rH1.1.length := hh1.2.2.2.2.1
  have hevh1 := hh1.2.2.2.2.2
  let rH2 := orFold m rH1.1 rH1.2 wsH2
  have hh2 := orFold_spec m wsH2 rH1.1 rH1.2 hvh1 hoh1
    (fun u hu => by have := selWires_lt n (2 * n) _ u hu; omega)
  have hlh2 : rH2.1.length = rH1.1.length + wsH2.length := hh2.2.1
  have hvh2 : ValidGates m rH2.1 := hh2.2.2.1
  have hnh2 : notCnt rH2.1 = notCnt rH1.1 := hh2.2.2.2.1
  have hoh2 : rH2.2 < m + rH2.1.length := hh2.2.2.2.2.1
  have hevh2 := hh2.2.2.2.2.2
  let jNot := rH2.1.length
  let wN := m + jNot
  let gNot : Gate := ⟨GateOp.not, [rH2.2]⟩
  let gsN := rH2.1 ++ [gNot]
  have hvN : ValidGates m gsN := by
    apply valid_snoc m rH2.1 gNot hvh2 (Or.inr (Or.inr rfl)) (by simp [gNot])
    intro i hi; simp [gNot] at hi; subst hi; exact hoh2
  have hnN : notCnt gsN = 1 := by
    rw [notCnt_snoc_not, hnh2, hnh1]
  have hlN : gsN.length = rH2.1.length + 1 := by simp [gsN]
  have hwN : wN < m + gsN.length := by simp [gsN, wN, jNot]
  let rT := mkBranch n g wN gsN true
  have hbT := mkBranch_spec n g wN gsN true hvN hwN
  have heT' : ∃ ext, rT.1 = gsN ++ ext := hbT.1
  obtain ⟨eT, heT⟩ := heT'
  have hlT : rT.1.length ≤ gsN.length + 4 * n + 1 := hbT.2.1
  have hvT : ValidGates m rT.1 := hbT.2.2.1
  have hnT : notCnt rT.1 = notCnt gsN := hbT.2.2.2.1
  have hoT : rT.2 < m + rT.1.length := hbT.2.2.2.2.1
  have hevT := hbT.2.2.2.2.2
  have hwNT : wN < m + rT.1.length := by
    have : gsN.length ≤ rT.1.length := by rw [heT]; simp
    omega
  let rF := mkBranch n g wN rT.1 false
  have hbF := mkBranch_spec n g wN rT.1 false hvT hwNT
  have heF' : ∃ ext, rF.1 = rT.1 ++ ext := hbF.1
  obtain ⟨eF, heF⟩ := heF'
  have hlF : rF.1.length ≤ rT.1.length + 4 * n + 1 := hbF.2.1
  have hvF : ValidGates m rF.1 := hbF.2.2.1
  have hnF : notCnt rF.1 = notCnt rT.1 := hbF.2.2.2.1
  have hoF : rF.2 < m + rF.1.length := hbF.2.2.2.2.1
  have hevF := hbF.2.2.2.2.2
  let C : Circuit := ⟨rF.1, rT.2⟩
  let p : Nat := rF.2
  have hCsize : C.size ≤ 32 * (n + 1) ^ 2 := by
    change rF.1.length ≤ 32 * (n + 1) ^ 2
    have h1 : wsH1.length ≤ n := selWires_length_le n n _
    have h2 : wsH2.length ≤ n := selWires_length_le n (2 * n) _
    have h4 : rF.1.length ≤ 10 * n + 3 := by omega
    have hsq := Nat.le_mul_self (n + 1)
    rw [Nat.pow_two]
    omega
  have hCnc : PEqualNP.NotBracket.notCount C = 1 := by
    change notCnt rF.1 = 1
    rw [hnF, hnT, hnN]
  have hCout : C.output < m + C.size := by
    have : rT.1.length ≤ rF.1.length := by rw [heF]; simp
    change rT.2 < m + rF.1.length
    omega
  have hjNot_lt : jNot < C.size := by
    change jNot < rF.1.length
    have hpre : rF.1 = rH2.1 ++ ([gNot] ++ eT ++ eF) := by
      rw [heF, heT]; simp [gsN, List.append_assoc]
    rw [hpre]; simp [jNot]
  have hjNot_op : (C.gates.getD jNot dg).op = GateOp.not := by
    have hpre : rF.1 = gsN ++ (eT ++ eF) := by
      rw [heF, heT, List.append_assoc]
    change (rF.1.getD jNot dg).op = GateOp.not
    rw [hpre, List.getD_append _ _ _ _ (by simp [gsN, jNot])]
    change ((rH2.1 ++ [gNot]).getD rH2.1.length dg).op = GateOp.not
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  have hevalN : ∀ w : List Bool, w.length = m → w.getD wF false = false →
      (run gsN w).getD wN false =
        !(wsH1.any (fun u => w.getD u false) || wsH2.any (fun u => w.getD u false)) := by
    intro w hwl hwF
    have hlast := run_snoc_last rH2.1 gNot w
    rw [hwl] at hlast
    have h1e : (run rH1.1 w).getD rH1.2 false =
        ((run [] w).getD wF false || wsH1.any (fun u => (run [] w).getD u false)) :=
      hevh1 w hwl
    have h2e : (run rH2.1 w).getD rH2.2 false =
        ((run rH1.1 w).getD rH1.2 false || wsH2.any (fun u => (run rH1.1 w).getD u false)) :=
      hevh2 w hwl
    have hlow1 : wsH1.any (fun u => (run [] w).getD u false) =
        wsH1.any (fun u => w.getD u false) := by
      apply any_congr; intro u hu
      exact run_low [] w u (by have := selWires_lt n n _ u hu; omega)
    have hlow2 : wsH2.any (fun u => (run rH1.1 w).getD u false) =
        wsH2.any (fun u => w.getD u false) := by
      apply any_congr; intro u hu
      exact run_low rH1.1 w u (by have := selWires_lt n (2 * n) _ u hu; omega)
    have hrF0 : (run [] w).getD wF false = false := by
      rw [run_low [] w wF (by omega), hwF]
    change (run (rH2.1 ++ [gNot]) w).getD (m + rH2.1.length) false = _
    rw [hlast]
    simp only [gNot, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    rw [h2e, h1e, hrF0, Bool.false_or, hlow1, hlow2]
  have hrunN_C : ∀ w : List Bool, w.length = m →
      (run C.gates w).getD wN false = (run gsN w).getD wN false := by
    intro w hwl
    have hpre : C.gates = gsN ++ (eT ++ eF) := by
      change rF.1 = _; rw [heF, heT, List.append_assoc]
    rw [hpre]
    exact run_prefix gsN (eT ++ eF) w wN (by rw [hwl]; exact hwN)
  have hrunOut_C : ∀ w : List Bool, w.length = m →
      (run C.gates w).getD C.output false = (run rT.1 w).getD rT.2 false := by
    intro w hwl
    have hpre : C.gates = rT.1 ++ eF := heF
    rw [hpre]
    exact run_prefix rT.1 eF w rT.2 (by rw [hwl]; exact hoT)
  have hrunN_T : ∀ w : List Bool, w.length = m →
      (run rT.1 w).getD wN false = (run gsN w).getD wN false := by
    intro w hwl
    rw [heT]
    exact run_prefix gsN eT w wN (by rw [hwl]; exact hwN)
  have hcore_N : ∀ i : Fin n,
      (run gsN (mkCore ordb i ++ [false, true])).getD wN false = !(g i).1 := by
    intro i
    have hb := core_blocks ordb i
    rw [hevalN _ hb.1 hb.2.2.2.2.1]
    have h2f : wsH2.any (fun u => (mkCore ordb i ++ [false, true]).getD u false) = false := by
      cases h : wsH2.any (fun u => (mkCore ordb i ++ [false, true]).getD u false)
      · rfl
      · rw [selWires_any] at h
        rcases h with ⟨k, _, hk⟩
        rw [hb.2.2.2.1 k] at hk
        contradiction
    have h1v : wsH1.any (fun u => (mkCore ordb i ++ [false, true]).getD u false) = (g i).1 := by
      cases hgi : (g i).1
      · cases h : wsH1.any (fun u => (mkCore ordb i ++ [false, true]).getD u false)
        · rfl
        · rw [selWires_any] at h
          rcases h with ⟨k, hgk, hk⟩
          rw [hb.2.2.1 k] at hk
          have hki := (hordb k i).mp hk
          rcases hmono k i hki with heq | ⟨hkf, _⟩
          · rw [heq] at hgk; rw [hgi] at hgk; contradiction
          · rw [hkf] at hgk; contradiction
      · rw [selWires_any]
        refine ⟨i, hgi, ?_⟩
        rw [hb.2.2.1 i]
        exact (hordb i i).mpr (hrefl i)
    rw [h1v, h2f, Bool.or_false]
  have hcore_branch : ∀ (i : Fin n) (c : Bool),
      ((((!(g i).1 &&
        ((selWires n n (fun k => !(g k).1 && ((g k).2 == c))).any
            (fun u => (mkCore ordb i ++ [false, true]).getD u false) ||
         (selWires n 0 (fun k => (g k).1 && ((g k).2 == !c))).any
            (fun u => (mkCore ordb i ++ [false, true]).getD u false))) ||
       (selWires n n (fun k => (g k).1 && ((g k).2 == c))).any
          (fun u => (mkCore ordb i ++ [false, true]).getD u false)) ||
       (selWires n (2 * n) (fun k => !(g k).1 && ((g k).2 == !c))).any
          (fun u => (mkCore ordb i ++ [false, true]).getD u false))) = ((g i).2 == c) := by
    intro i c
    have hb := core_blocks ordb i
    have h4f : (selWires n (2 * n) (fun k => !(g k).1 && ((g k).2 == !c))).any
        (fun u => (mkCore ordb i ++ [false, true]).getD u false) = false := by
      cases h : (selWires n (2 * n) (fun k => !(g k).1 && ((g k).2 == !c))).any
          (fun u => (mkCore ordb i ++ [false, true]).getD u false)
      · rfl
      · rw [selWires_any] at h
        rcases h with ⟨k, _, hk⟩
        rw [hb.2.2.2.1 k] at hk
        contradiction
    rw [h4f, Bool.or_false]
    cases hgi1 : (g i).1
    · have hnoU : ∀ (P : Fin n → Bool) (base : Nat),
          (∀ k, P k = true → (g k).1 = true) →
          (∀ k : Fin n, (mkCore ordb i ++ [false, true]).getD (base + k.val) false = ordb k i) →
          (selWires n base P).any (fun u => (mkCore ordb i ++ [false, true]).getD u false) = false := by
        intro P base hPU hget
        cases h : (selWires n base P).any (fun u => (mkCore ordb i ++ [false, true]).getD u false)
        · rfl
        · rw [selWires_any] at h
          rcases h with ⟨k, hPk, hk⟩
          rw [hget k] at hk
          have hki := (hordb k i).mp hk
          have hgk1 := hPU k hPk
          rcases hmono k i hki with heq | ⟨hkf, _⟩
          · rw [heq] at hgk1; rw [hgi1] at hgk1; contradiction
          · rw [hkf] at hgk1; contradiction
      have h2f : (selWires n 0 (fun k => (g k).1 && ((g k).2 == !c))).any
          (fun u => (mkCore ordb i ++ [false, true]).getD u false) = false :=
        hnoU _ 0 (fun k hk => (Bool.and_eq_true _ _).mp hk |>.1)
          (fun k => by rw [Nat.zero_add]; exact hb.2.1 k)
      have h3f : (selWires n n (fun k => (g k).1 && ((g k).2 == c))).any
          (fun u => (mkCore ordb i ++ [false, true]).getD u false) = false :=
        hnoU _ n (fun k hk => (Bool.and_eq_true _ _).mp hk |>.1) hb.2.2.1
      rw [h2f, h3f]
      simp only [Bool.not_false, Bool.true_and, Bool.or_false]
      cases hEq : ((g i).2 == c)
      · cases h : (selWires n n (fun k => !(g k).1 && ((g k).2 == c))).any
            (fun u => (mkCore ordb i ++ [false, true]).getD u false)
        · rfl
        · rw [selWires_any] at h
          rcases h with ⟨k, hPk, hk⟩
          rw [hb.2.2.1 k] at hk
          have hki := (hordb k i).mp hk
          rcases hmono k i hki with heq | ⟨_, hif⟩
          · rw [heq] at hPk
            have := ((Bool.and_eq_true _ _).mp hPk).2
            rw [hEq] at this; contradiction
          · rw [hgi1] at hif; contradiction
      · rw [selWires_any]
        refine ⟨i, by simp [hgi1, hEq], ?_⟩
        rw [hb.2.2.1 i]
        exact (hordb i i).mpr (hrefl i)
    · simp only [Bool.not_true, Bool.false_and, Bool.false_or]
      cases hEq : ((g i).2 == c)
      · cases h : (selWires n n (fun k => (g k).1 && ((g k).2 == c))).any
            (fun u => (mkCore ordb i ++ [false, true]).getD u false)
        · rfl
        · rw [selWires_any] at h
          rcases h with ⟨k, hPk, hk⟩
          rw [hb.2.2.1 k] at hk
          have hki := (hordb k i).mp hk
          have hgk1 := ((Bool.and_eq_true _ _).mp hPk).1
          have hgk2 := ((Bool.and_eq_true _ _).mp hPk).2
          rcases hmono k i hki with heq | ⟨hkf, _⟩
          · rw [heq] at hgk2; rw [hEq] at hgk2; contradiction
          · rw [hkf] at hgk1; contradiction
      · rw [selWires_any]
        refine ⟨i, by simp [hgi1, hEq], ?_⟩
        rw [hb.2.2.1 i]
        exact (hordb i i).mpr (hrefl i)
  have hcore_out : ∀ i : Fin n,
      (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = (g i).2 := by
    intro i
    have hb := core_blocks ordb i
    rw [hrunOut_C _ hb.1]
    have hTe := hevT _ hb.1 hb.2.2.2.2.1
    change (run rT.1 _).getD rT.2 false = _ at hTe
    rw [hTe, hcore_N i, hcore_branch i true]
    cases (g i).2 <;> rfl
  have hcore_p : ∀ i : Fin n,
      (run C.gates (mkCore ordb i ++ [false, true])).getD p false = !((g i).2) := by
    intro i
    have hb := core_blocks ordb i
    have hFe := hevF _ hb.1 hb.2.2.2.2.1
    change (run rF.1 _).getD rF.2 false = _ at hFe
    change (run rF.1 _).getD rF.2 false = _
    rw [hFe, hrunN_T _ hb.1, hcore_N i, hcore_branch i false]
    cases (g i).2 <;> rfl
  refine ⟨C, p, hvF.1, hvF.2, hCout, hoF, ?_, ?_, hCsize, hCnc, ⟨jNot, hjNot_lt⟩, hjNot_op, ?_⟩
  · intro i
    rw [hcore_out i, hcore_p i]
  · intro i v hv
    have hgiv : g i = v := hpin i v hv
    refine ⟨by rw [hcore_out i, hgiv], ?_, ?_⟩
    · cases hv1 : v.1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hb := hi_blocks ordb eqb i
        have hN : (run gsN (mkHi ordb eqb i ++ [false, true])).getD wN false = false := by
          rw [hevalN _ hb.1 hb.2.2.2.2.1]
          have h2t : wsH2.any (fun u => (mkHi ordb eqb i ++ [false, true]).getD u false) = true := by
            rw [selWires_any]
            refine ⟨i, rfl, ?_⟩
            rw [hb.2.2.2.1 i]; exact (heqb i i).mpr rfl
          rw [h2t]; simp
        have h3f : (selWires n n (fun k => (g k).1 && ((g k).2 == true))).any
            (fun u => (mkHi ordb eqb i ++ [false, true]).getD u false) = false := by
          cases h : (selWires n n (fun k => (g k).1 && ((g k).2 == true))).any
              (fun u => (mkHi ordb eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h
            rcases h with ⟨k, hPk, hk⟩
            rw [hb.2.2.1 k] at hk
            have hki := (hordb k i).mp hk
            have hgk1 := ((Bool.and_eq_true _ _).mp hPk).1
            rcases hmono k i hki with heq | ⟨hkf, _⟩
            · rw [heq, hgiv, hv1] at hgk1; contradiction
            · rw [hkf] at hgk1; contradiction
        rw [hrunOut_C _ hb.1]
        have hTe := hevT _ hb.1 hb.2.2.2.2.1
        change (run rT.1 _).getD rT.2 false = _ at hTe
        rw [hTe, hN, h3f]
        simp only [Bool.false_and, Bool.false_or]
        cases hv2 : v.2
        · rw [Bool.not_false, selWires_any]
          refine ⟨i, by simp [hgiv, hv1, hv2], ?_⟩
          rw [hb.2.2.2.1 i]; exact (heqb i i).mpr rfl
        · cases h : (selWires n (2 * n) (fun k => !(g k).1 && ((g k).2 == !true))).any
              (fun u => (mkHi ordb eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h
            rcases h with ⟨k, hPk, hk⟩
            rw [hb.2.2.2.1 k] at hk
            have hki : k = i := (heqb k i).mp hk
            subst hki
            simp [hgiv, hv1, hv2] at hPk
      · simp only [↓reduceIte]
        have hb := lo_blocks eqb i
        have hN : (run gsN (mkLo eqb i ++ [false, true])).getD wN false = true := by
          rw [hevalN _ hb.1 hb.2.2.2.2.1]
          have h1f : wsH1.any (fun u => (mkLo eqb i ++ [false, true]).getD u false) = false := by
            cases h : wsH1.any (fun u => (mkLo eqb i ++ [false, true]).getD u false)
            · rfl
            · rw [selWires_any] at h; rcases h with ⟨k, _, hk⟩
              rw [hb.2.2.1 k] at hk; contradiction
          have h2f : wsH2.any (fun u => (mkLo eqb i ++ [false, true]).getD u false) = false := by
            cases h : wsH2.any (fun u => (mkLo eqb i ++ [false, true]).getD u false)
            · rfl
            · rw [selWires_any] at h; rcases h with ⟨k, _, hk⟩
              rw [hb.2.2.2.1 k] at hk; contradiction
          rw [h1f, h2f]; rfl
        have hbf : ∀ (P : Fin n → Bool),
            (selWires n n P).any (fun u => (mkLo eqb i ++ [false, true]).getD u false) = false := by
          intro P
          cases h : (selWires n n P).any (fun u => (mkLo eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h; rcases h with ⟨k, _, hk⟩
            rw [hb.2.2.1 k] at hk; contradiction
        have hcf : ∀ (P : Fin n → Bool),
            (selWires n (2 * n) P).any (fun u => (mkLo eqb i ++ [false, true]).getD u false) = false := by
          intro P
          cases h : (selWires n (2 * n) P).any (fun u => (mkLo eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h; rcases h with ⟨k, _, hk⟩
            rw [hb.2.2.2.1 k] at hk; contradiction
        rw [hrunOut_C _ hb.1]
        have hTe := hevT _ hb.1 hb.2.2.2.2.1
        change (run rT.1 _).getD rT.2 false = _ at hTe
        rw [hTe, hN, hbf, hbf, hcf]
        simp only [Bool.false_or, Bool.true_and, Bool.or_false]
        cases hv2 : v.2
        · rw [Bool.not_false, selWires_any]
          refine ⟨i, by simp [hgiv, hv1, hv2], ?_⟩
          rw [Nat.zero_add, hb.2.1 i]; exact (heqb i i).mpr rfl
        · cases h : (selWires n 0 (fun k => (g k).1 && ((g k).2 == !true))).any
              (fun u => (mkLo eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h
            rcases h with ⟨k, hPk, hk⟩
            rw [Nat.zero_add, hb.2.1 k] at hk
            have hki : k = i := (heqb k i).mp hk
            subst hki
            simp [hgiv, hv1, hv2] at hPk
    · cases hv1 : v.1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hb := hi_blocks ordb eqb i
        have hN : (run gsN (mkHi ordb eqb i ++ [false, true])).getD wN false = false := by
          rw [hevalN _ hb.1 hb.2.2.2.2.1]
          have h2t : wsH2.any (fun u => (mkHi ordb eqb i ++ [false, true]).getD u false) = true := by
            rw [selWires_any]
            refine ⟨i, rfl, ?_⟩
            rw [hb.2.2.2.1 i]; exact (heqb i i).mpr rfl
          rw [h2t]; simp
        have h3f : (selWires n n (fun k => (g k).1 && ((g k).2 == false))).any
            (fun u => (mkHi ordb eqb i ++ [false, true]).getD u false) = false := by
          cases h : (selWires n n (fun k => (g k).1 && ((g k).2 == false))).any
              (fun u => (mkHi ordb eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h
            rcases h with ⟨k, hPk, hk⟩
            rw [hb.2.2.1 k] at hk
            have hki := (hordb k i).mp hk
            have hgk1 := ((Bool.and_eq_true _ _).mp hPk).1
            rcases hmono k i hki with heq | ⟨hkf, _⟩
            · rw [heq, hgiv, hv1] at hgk1; contradiction
            · rw [hkf] at hgk1; contradiction
        have hFe := hevF _ hb.1 hb.2.2.2.2.1
        change (run rF.1 _).getD rF.2 false = _ at hFe
        change (run rF.1 _).getD rF.2 false = v.2
        rw [hFe, hrunN_T _ hb.1, hN, h3f]
        simp only [Bool.false_and, Bool.false_or]
        cases hv2 : v.2
        · cases h : (selWires n (2 * n) (fun k => !(g k).1 && ((g k).2 == !false))).any
              (fun u => (mkHi ordb eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h
            rcases h with ⟨k, hPk, hk⟩
            rw [hb.2.2.2.1 k] at hk
            have hki : k = i := (heqb k i).mp hk
            subst hki
            simp [hgiv, hv1, hv2] at hPk
        · rw [selWires_any]
          refine ⟨i, by simp [hgiv, hv1, hv2], ?_⟩
          rw [hb.2.2.2.1 i]; exact (heqb i i).mpr rfl
      · simp only [↓reduceIte]
        have hb := lo_blocks eqb i
        have hN : (run gsN (mkLo eqb i ++ [false, true])).getD wN false = true := by
          rw [hevalN _ hb.1 hb.2.2.2.2.1]
          have h1f : wsH1.any (fun u => (mkLo eqb i ++ [false, true]).getD u false) = false := by
            cases h : wsH1.any (fun u => (mkLo eqb i ++ [false, true]).getD u false)
            · rfl
            · rw [selWires_any] at h; rcases h with ⟨k, _, hk⟩
              rw [hb.2.2.1 k] at hk; contradiction
          have h2f : wsH2.any (fun u => (mkLo eqb i ++ [false, true]).getD u false) = false := by
            cases h : wsH2.any (fun u => (mkLo eqb i ++ [false, true]).getD u false)
            · rfl
            · rw [selWires_any] at h; rcases h with ⟨k, _, hk⟩
              rw [hb.2.2.2.1 k] at hk; contradiction
          rw [h1f, h2f]; rfl
        have hbf : ∀ (P : Fin n → Bool),
            (selWires n n P).any (fun u => (mkLo eqb i ++ [false, true]).getD u false) = false := by
          intro P
          cases h : (selWires n n P).any (fun u => (mkLo eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h; rcases h with ⟨k, _, hk⟩
            rw [hb.2.2.1 k] at hk; contradiction
        have hcf : ∀ (P : Fin n → Bool),
            (selWires n (2 * n) P).any (fun u => (mkLo eqb i ++ [false, true]).getD u false) = false := by
          intro P
          cases h : (selWires n (2 * n) P).any (fun u => (mkLo eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h; rcases h with ⟨k, _, hk⟩
            rw [hb.2.2.2.1 k] at hk; contradiction
        have hFe := hevF _ hb.1 hb.2.2.2.2.1
        change (run rF.1 _).getD rF.2 false = _ at hFe
        change (run rF.1 _).getD rF.2 false = v.2
        rw [hFe, hrunN_T _ hb.1, hN, hbf, hbf, hcf]
        simp only [Bool.false_or, Bool.true_and, Bool.or_false]
        cases hv2 : v.2
        · cases h : (selWires n 0 (fun k => (g k).1 && ((g k).2 == !false))).any
              (fun u => (mkLo eqb i ++ [false, true]).getD u false)
          · rfl
          · rw [selWires_any] at h
            rcases h with ⟨k, hPk, hk⟩
            rw [Nat.zero_add, hb.2.1 k] at hk
            have hki : k = i := (heqb k i).mp hk
            subst hki
            simp [hgiv, hv1, hv2] at hPk
        · rw [selWires_any]
          refine ⟨i, by simp [hgiv, hv1, hv2], ?_⟩
          rw [Nat.zero_add, hb.2.1 i]; exact (heqb i i).mpr rfl
  · intro i
    have hb := core_blocks ordb i
    refine ⟨hcore_out i, ?_⟩
    rw [hrunN_C _ hb.1, hcore_N i]

def isPin {n : Nat} (pin : Fin n → Option (Bool × Bool)) (b1 b2 : Bool) (k : Fin n) : Bool :=
  match pin k with
  | some v => (v.1 == b1) && (v.2 == b2)
  | none => false

lemma isPin_eq_true {n : Nat} (pin : Fin n → Option (Bool × Bool)) (b1 b2 : Bool) (k : Fin n) :
    isPin pin b1 b2 k = true ↔ pin k = some (b1, b2) := by
  unfold isPin
  cases h : pin k with
  | none => simp
  | some v =>
    rcases v with ⟨v1, v2⟩
    simp

lemma build_two_not {n : Nat}
    (ord : Fin n → Fin n → Prop) (pin : Fin n → Option (Bool × Bool))
    (hrefl : ∀ i, ord i i)
    (ordb eqb : Fin n → Fin n → Bool)
    (hordb : ∀ k i, ordb k i = true ↔ ord k i)
    (heqb : ∀ k i, eqb k i = true ↔ k = i)
    (hcons : ∀ i j a b, pin i = some a → pin j = some b → ord i j →
      a = b ∨ (a.1 = false ∧ b.1 = true)) :
    ∃ C p,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (3 * n + 2) C ∧
      C.output < 3 * n + 2 + C.size ∧ p < 3 * n + 2 + C.size ∧
      (∀ i, (run C.gates (mkCore ordb i ++ [false, true])).getD p false =
        !((run C.gates (mkCore ordb i ++ [false, true])).getD C.output false)) ∧
      (∀ i v, pin i = some v →
        (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = v.2 ∧
        (run C.gates ((if v.1 then mkLo eqb i else mkHi ordb eqb i) ++ [false, true])).getD C.output false = !v.2 ∧
        (run C.gates ((if v.1 then mkLo eqb i else mkHi ordb eqb i) ++ [false, true])).getD p false = v.2) ∧
      PEqualNP.NotBracket.notCount C ≤ 2 ∧
      C.size ≤ 32 * (n + 1) ^ 2 := by
  let m := 3 * n + 2
  let wF := 3 * n
  let wsBU1 := selWires n n (isPin pin true true)
  let wsBU0 := selWires n n (isPin pin true false)
  let wsCL1 := selWires n (2 * n) (isPin pin false true)
  let wsAU0 := selWires n 0 (isPin pin true false)
  let wsBL1 := selWires n n (isPin pin false true)
  let wsCL0 := selWires n (2 * n) (isPin pin false false)
  let r1 := orFold m [] wF wsBU1
  have h1 := orFold_spec m wsBU1 [] wF (valid_nil m) (by omega)
    (fun u hu => by have := selWires_lt n n _ u hu; omega)
  have hl1 : r1.1.length = wsBU1.length := by simpa using h1.2.1
  have hv1 : ValidGates m r1.1 := h1.2.2.1
  have hn1 : notCnt r1.1 = 0 := h1.2.2.2.1
  have ho1 : r1.2 < m + r1.1.length := h1.2.2.2.2.1
  have hev1 := h1.2.2.2.2.2
  let r2 := orFold m r1.1 r1.2 wsBU0
  have h2 := orFold_spec m wsBU0 r1.1 r1.2 hv1 ho1
    (fun u hu => by have := selWires_lt n n _ u hu; omega)
  have he2' : ∃ ext, r2.1 = r1.1 ++ ext := h2.1
  obtain ⟨e2, he2⟩ := he2'
  have hl2 : r2.1.length = r1.1.length + wsBU0.length := h2.2.1
  have hv2 : ValidGates m r2.1 := h2.2.2.1
  have hn2 : notCnt r2.1 = notCnt r1.1 := h2.2.2.2.1
  have ho2 : r2.2 < m + r2.1.length := h2.2.2.2.2.1
  have hev2 := h2.2.2.2.2.2
  let r3 := orFold m r2.1 r2.2 wsCL1
  have h3 := orFold_spec m wsCL1 r2.1 r2.2 hv2 ho2
    (fun u hu => by have := selWires_lt n (2 * n) _ u hu; omega)
  have he3' : ∃ ext, r3.1 = r2.1 ++ ext := h3.1
  obtain ⟨e3, he3⟩ := he3'
  have hl3 : r3.1.length = r2.1.length + wsCL1.length := h3.2.1
  have hv3 : ValidGates m r3.1 := h3.2.2.1
  have hn3 : notCnt r3.1 = notCnt r2.1 := h3.2.2.2.1
  have ho3 : r3.2 < m + r3.1.length := h3.2.2.2.2.1
  have hev3 := h3.2.2.2.2.2
  let r4 := orFold m r3.1 r3.2 wsAU0
  have h4 := orFold_spec m wsAU0 r3.1 r3.2 hv3 ho3
    (fun u hu => by have := selWires_lt n 0 _ u hu; omega)
  have he4' : ∃ ext, r4.1 = r3.1 ++ ext := h4.1
  obtain ⟨e4, he4⟩ := he4'
  have hl4 : r4.1.length = r3.1.length + wsAU0.length := h4.2.1
  have hv4 : ValidGates m r4.1 := h4.2.2.1
  have hn4 : notCnt r4.1 = notCnt r3.1 := h4.2.2.2.1
  have ho4 : r4.2 < m + r4.1.length := h4.2.2.2.2.1
  have hev4 := h4.2.2.2.2.2
  let r5 := orFold m r4.1 r4.2 wsBL1
  have h5 := orFold_spec m wsBL1 r4.1 r4.2 hv4 ho4
    (fun u hu => by have := selWires_lt n n _ u hu; omega)
  have he5' : ∃ ext, r5.1 = r4.1 ++ ext := h5.1
  obtain ⟨e5, he5⟩ := he5'
  have hl5 : r5.1.length = r4.1.length + wsBL1.length := h5.2.1
  have hv5 : ValidGates m r5.1 := h5.2.2.1
  have hn5 : notCnt r5.1 = notCnt r4.1 := h5.2.2.2.1
  have ho5 : r5.2 < m + r5.1.length := h5.2.2.2.2.1
  have hev5 := h5.2.2.2.2.2
  let r6 := orFold m r5.1 r5.2 wsCL0
  have h6 := orFold_spec m wsCL0 r5.1 r5.2 hv5 ho5
    (fun u hu => by have := selWires_lt n (2 * n) _ u hu; omega)
  have he6' : ∃ ext, r6.1 = r5.1 ++ ext := h6.1
  obtain ⟨e6, he6⟩ := he6'
  have hl6 : r6.1.length = r5.1.length + wsCL0.length := h6.2.1
  have hv6 : ValidGates m r6.1 := h6.2.2.1
  have hn6 : notCnt r6.1 = notCnt r5.1 := h6.2.2.2.1
  have ho6 : r6.2 < m + r6.1.length := h6.2.2.2.2.1
  have hev6 := h6.2.2.2.2.2
  let wT3 := r1.2
  let wT2 := r3.2
  let wT1 := r6.2
  let gN1 : Gate := ⟨GateOp.not, [wT2]⟩
  let gs7 := r6.1 ++ [gN1]
  let wN1 := m + r6.1.length
  have ho3_6 : wT2 < m + r6.1.length := by omega
  have hv7 : ValidGates m gs7 := by
    apply valid_snoc m r6.1 gN1 hv6 (Or.inr (Or.inr rfl)) (by simp [gN1])
    intro i hi; simp [gN1] at hi; subst hi; exact ho3_6
  let gAnd : Gate := ⟨GateOp.and, [wT1, wN1]⟩
  let gs8 := gs7 ++ [gAnd]
  let wA := m + gs7.length
  have hv8 : ValidGates m gs8 := by
    apply valid_snoc m gs7 gAnd hv7 (Or.inl rfl) (by simp [gAnd])
    intro i hi; simp [gAnd] at hi
    rcases hi with rfl | rfl
    · simp [gs7]; omega
    · simp [gs7, wN1]
  let gOr : Gate := ⟨GateOp.or, [wA, wT3]⟩
  let gs9 := gs8 ++ [gOr]
  let wOut := m + gs8.length
  have ho1_8 : wT3 < m + gs8.length := by
    simp [gs8, gs7]; omega
  have hv9 : ValidGates m gs9 := by
    apply valid_snoc m gs8 gOr hv8 (Or.inr (Or.inl rfl)) (by simp [gOr])
    intro i hi; simp [gOr] at hi
    rcases hi with rfl | rfl
    · simp [gs8, wA]
    · exact ho1_8
  let gN2 : Gate := ⟨GateOp.not, [wOut]⟩
  let gs10 := gs9 ++ [gN2]
  let wP := m + gs9.length
  have hv10 : ValidGates m gs10 := by
    apply valid_snoc m gs9 gN2 hv9 (Or.inr (Or.inr rfl)) (by simp [gN2])
    intro i hi; simp [gN2] at hi; subst hi; simp [gs9, wOut]
  let C : Circuit := ⟨gs10, wOut⟩
  let p : Nat := wP
  have hncC : PEqualNP.NotBracket.notCount C ≤ 2 := by
    change notCnt gs10 ≤ 2
    rw [notCnt_snoc_not, notCnt_snoc_or, notCnt_snoc_and, notCnt_snoc_not,
        hn6, hn5, hn4, hn3, hn2, hn1]
  have hszC : C.size ≤ 32 * (n + 1) ^ 2 := by
    change gs10.length ≤ 32 * (n + 1) ^ 2
    have l1 : wsBU1.length ≤ n := selWires_length_le n n _
    have l2 : wsBU0.length ≤ n := selWires_length_le n n _
    have l3 : wsCL1.length ≤ n := selWires_length_le n (2 * n) _
    have l4 : wsAU0.length ≤ n := selWires_length_le n 0 _
    have l5 : wsBL1.length ≤ n := selWires_length_le n n _
    have l6 : wsCL0.length ≤ n := selWires_length_le n (2 * n) _
    have hgs10 : gs10.length = r6.1.length + 4 := by simp [gs10, gs9, gs8, gs7]
    have hsq := Nat.le_mul_self (n + 1)
    rw [Nat.pow_two]
    omega
  have hcomp_all : ∀ w : List Bool, w.length = m →
      (run C.gates w).getD p false = !((run C.gates w).getD C.output false) := by
    intro w hwl
    have hlast := run_snoc_last gs9 gN2 w
    rw [hwl] at hlast
    have hpre : (run gs10 w).getD wOut false = (run gs9 w).getD wOut false :=
      run_prefix gs9 [gN2] w wOut (by rw [hwl]; simp [gs9, wOut])
    change (run (gs9 ++ [gN2]) w).getD (m + gs9.length) false = !((run gs10 w).getD wOut false)
    rw [hlast, hpre]
    rfl
  have heval_out : ∀ w : List Bool, w.length = m → w.getD wF false = false →
      let t3 := wsBU1.any (fun u => w.getD u false)
      let t2 := (t3 || wsBU0.any (fun u => w.getD u false)) || wsCL1.any (fun u => w.getD u false)
      let t1 := ((t2 || wsAU0.any (fun u => w.getD u false)) || wsBL1.any (fun u => w.getD u false)) ||
          wsCL0.any (fun u => w.getD u false)
      (run C.gates w).getD C.output false = ((t1 && !t2) || t3) := by
    intro w hwl hwF
    have hlow : ∀ (gl : List Gate) (base : Nat) (P : Fin n → Bool),
        base + n ≤ m →
        (selWires n base P).any (fun u => (run gl w).getD u false) =
        (selWires n base P).any (fun u => w.getD u false) := by
      intro gl base P hbn
      apply any_congr
      intro u hu
      exact run_low gl w u (by have := selWires_lt n base P u hu; omega)
    have hpre_out : (run gs10 w).getD wOut false = (run gs9 w).getD wOut false :=
      run_prefix gs9 [gN2] w wOut (by rw [hwl]; simp [gs9, wOut])
    have hlast9 := run_snoc_last gs8 gOr w
    rw [hwl] at hlast9
    have hpre_A : (run gs8 w).getD wA false =
        ((run gs7 w).getD wT1 false && (run gs7 w).getD wN1 false) := by
      have hlast := run_snoc_last gs7 gAnd w
      rw [hwl] at hlast
      simp only [gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at hlast
      exact hlast
    have hpre_T1 : (run gs7 w).getD wT1 false = (run r6.1 w).getD wT1 false :=
      run_prefix r6.1 [gN1] w wT1 (by rw [hwl]; exact ho6)
    have hpre_N1 : (run gs7 w).getD wN1 false = !((run r6.1 w).getD wT2 false) := by
      have hlast := run_snoc_last r6.1 gN1 w
      rw [hwl] at hlast
      simp only [gN1, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at hlast
      exact hlast
    have hpre_T2 : (run r6.1 w).getD wT2 false = (run r3.1 w).getD wT2 false := by
      have hr6 : r6.1 = r3.1 ++ (e4 ++ e5 ++ e6) := by
        rw [he6, he5, he4]; simp [List.append_assoc]
      rw [hr6]
      exact run_prefix r3.1 _ w wT2 (by rw [hwl]; exact ho3)
    have hpre_T3 : (run gs8 w).getD wT3 false = (run r1.1 w).getD wT3 false := by
      have hgs8 : gs8 = r1.1 ++ (e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ [gN1, gAnd]) := by
        simp only [gs8, gs7]
        rw [he6, he5, he4, he3, he2]
        simp [List.append_assoc]
      rw [hgs8]
      exact run_prefix r1.1 _ w wT3 (by rw [hwl]; exact ho1)
    have hrF0 : (run [] w).getD wF false = false := by
      rw [run_low [] w wF (by omega), hwF]
    have ht3 : (run r1.1 w).getD wT3 false = wsBU1.any (fun u => w.getD u false) := by
      have h1e := hev1 w hwl
      change (run r1.1 w).getD r1.2 false = _ at h1e
      change (run r1.1 w).getD r1.2 false = _
      rw [h1e, hrF0, Bool.false_or, hlow [] n _ (by omega)]
    have ht2 : (run r3.1 w).getD wT2 false =
        ((wsBU1.any (fun u => w.getD u false) || wsBU0.any (fun u => w.getD u false)) ||
          wsCL1.any (fun u => w.getD u false)) := by
      have h3e := hev3 w hwl
      have h2e := hev2 w hwl
      change (run r3.1 w).getD r3.2 false = _ at h3e
      change (run r2.1 w).getD r2.2 false = _ at h2e
      change (run r3.1 w).getD r3.2 false = _
      rw [h3e, h2e, ht3, hlow r1.1 n _ (by omega), hlow r2.1 (2 * n) _ (by omega)]
    have ht1 : (run r6.1 w).getD wT1 false =
        (((((wsBU1.any (fun u => w.getD u false) || wsBU0.any (fun u => w.getD u false)) ||
            wsCL1.any (fun u => w.getD u false)) ||
          wsAU0.any (fun u => w.getD u false)) ||
          wsBL1.any (fun u => w.getD u false)) ||
          wsCL0.any (fun u => w.getD u false)) := by
      have h6e := hev6 w hwl
      have h5e := hev5 w hwl
      have h4e := hev4 w hwl
      change (run r6.1 w).getD r6.2 false = _ at h6e
      change (run r5.1 w).getD r5.2 false = _ at h5e
      change (run r4.1 w).getD r4.2 false = _ at h4e
      change (run r6.1 w).getD r6.2 false = _
      rw [h6e, h5e, h4e, ht2,
          hlow r3.1 0 _ (by omega), hlow r4.1 n _ (by omega), hlow r5.1 (2 * n) _ (by omega)]
    change (run gs10 w).getD wOut false = _
    rw [hpre_out]
    change (run (gs8 ++ [gOr]) w).getD (m + gs8.length) false = _
    rw [hlast9]
    simp only [gOr, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
    rw [hpre_A, hpre_T1, hpre_N1, hpre_T2, hpre_T3, ht1, ht2, ht3]
  have hnoOrd : ∀ (i : Fin n) (a b : Bool × Bool),
      pin i = some b → ¬ (a = b ∨ (a.1 = false ∧ b.1 = true)) →
      ∀ (w : List Bool) (base : Nat),
        (∀ k : Fin n, w.getD (base + k.val) false = ordb k i) →
        (selWires n base (isPin pin a.1 a.2)).any (fun u => w.getD u false) = false := by
    intro i a b hpi hnot w base hget
    cases h : (selWires n base (isPin pin a.1 a.2)).any (fun u => w.getD u false)
    · rfl
    · rw [selWires_any] at h
      rcases h with ⟨k, hpk, hwk⟩
      rw [isPin_eq_true] at hpk
      rw [hget k] at hwk
      have hki := (hordb k i).mp hwk
      exact False.elim (hnot (by simpa using hcons k i (a.1, a.2) b hpk hpi hki))
  have hyesOrd : ∀ (i : Fin n) (b1 b2 : Bool),
      pin i = some (b1, b2) →
      ∀ (w : List Bool) (base : Nat),
        (∀ k : Fin n, w.getD (base + k.val) false = ordb k i) →
        (selWires n base (isPin pin b1 b2)).any (fun u => w.getD u false) = true := by
    intro i b1 b2 hpi w base hget
    rw [selWires_any]
    refine ⟨i, (isPin_eq_true pin b1 b2 i).mpr hpi, ?_⟩
    rw [hget i]
    exact (hordb i i).mpr (hrefl i)
  have hnoUnit : ∀ (i : Fin n) (a b : Bool × Bool),
      pin i = some b → a ≠ b →
      ∀ (w : List Bool) (base : Nat),
        (∀ k : Fin n, w.getD (base + k.val) false = eqb k i) →
        (selWires n base (isPin pin a.1 a.2)).any (fun u => w.getD u false) = false := by
    intro i a b hpi hne w base hget
    cases h : (selWires n base (isPin pin a.1 a.2)).any (fun u => w.getD u false)
    · rfl
    · rw [selWires_any] at h
      rcases h with ⟨k, hpk, hwk⟩
      rw [isPin_eq_true] at hpk
      rw [hget k] at hwk
      have hki : k = i := (heqb k i).mp hwk
      subst hki
      rw [hpi] at hpk
      have : (a.1, a.2) = b := Option.some.inj hpk.symm
      exact False.elim (hne (by cases a; exact this))
  have hyesUnit : ∀ (i : Fin n) (b1 b2 : Bool),
      pin i = some (b1, b2) →
      ∀ (w : List Bool) (base : Nat),
        (∀ k : Fin n, w.getD (base + k.val) false = eqb k i) →
        (selWires n base (isPin pin b1 b2)).any (fun u => w.getD u false) = true := by
    intro i b1 b2 hpi w base hget
    rw [selWires_any]
    refine ⟨i, (isPin_eq_true pin b1 b2 i).mpr hpi, ?_⟩
    rw [hget i]
    exact (heqb i i).mpr rfl
  have hnoBlank : ∀ (P : Fin n → Bool) (w : List Bool) (base : Nat),
      (∀ k : Fin n, w.getD (base + k.val) false = false) →
      (selWires n base P).any (fun u => w.getD u false) = false := by
    intro P w base hget
    cases h : (selWires n base P).any (fun u => w.getD u false)
    · rfl
    · rw [selWires_any] at h
      rcases h with ⟨k, _, hwk⟩
      rw [hget k] at hwk
      contradiction
  have hCout : C.output < 3 * n + 2 + C.size := by
    change m + gs8.length < m + (gs8 ++ [gOr] ++ [gN2]).length
    simp
  have hpLt : p < 3 * n + 2 + C.size := by
    change m + gs9.length < m + (gs9 ++ [gN2]).length
    simp
  refine ⟨C, p, hv10.1, hv10.2, hCout, hpLt, ?_, ?_, hncC, hszC⟩
  · intro i
    have hb := core_blocks ordb i
    exact hcomp_all _ hb.1
  · intro i v hpi
    have hbc := core_blocks ordb i
    have hcA : ∀ k : Fin n, (mkCore ordb i ++ [false, true]).getD (0 + k.val) false = ordb k i :=
      fun k => by rw [Nat.zero_add]; exact hbc.2.1 k
    have hcB := hbc.2.2.1
    have hcC := hbc.2.2.2.1
    rcases v with ⟨v1, v2⟩
    cases v1 <;> cases v2
    · have hOutC : (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = false := by
        rw [heval_out _ hbc.1 hbc.2.2.2.2.1]
        have e1 := hnoOrd i (true, true) (false, false) hpi (by simp) _ n hcB
        have e2 := hnoOrd i (true, false) (false, false) hpi (by simp) _ n hcB
        have e3 := hnoBlank (isPin pin false true) _ (2 * n) hcC
        have e4 := hnoOrd i (true, false) (false, false) hpi (by simp) _ 0 hcA
        have e5 := hnoOrd i (false, true) (false, false) hpi (by simp) _ n hcB
        have e6 := hnoBlank (isPin pin false false) _ (2 * n) hcC
        simp only [wsBU1, wsBU0, wsCL1, wsAU0, wsBL1, wsCL0]
        rw [e1, e2, e3, e4, e5, e6]; rfl
      have hbh := hi_blocks ordb eqb i
      have hhB := hbh.2.2.1
      have hhC := hbh.2.2.2.1
      have hOutH : (run C.gates (mkHi ordb eqb i ++ [false, true])).getD C.output false = true := by
        rw [heval_out _ hbh.1 hbh.2.2.2.2.1]
        have e1 := hnoOrd i (true, true) (false, false) hpi (by simp) _ n hhB
        have e2 := hnoOrd i (true, false) (false, false) hpi (by simp) _ n hhB
        have e3 := hnoUnit i (false, true) (false, false) hpi (by simp) _ (2 * n) hhC
        have e6 := hyesUnit i false false hpi _ (2 * n) hhC
        simp only [wsBU1, wsBU0, wsCL1, wsAU0, wsBL1, wsCL0]
        rw [e1, e2, e3, e6]; simp
      refine ⟨hOutC, hOutH, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hcomp_all _ hbh.1, hOutH]; rfl
    · have hOutC : (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = true := by
        rw [heval_out _ hbc.1 hbc.2.2.2.2.1]
        have e1 := hnoOrd i (true, true) (false, true) hpi (by simp) _ n hcB
        have e2 := hnoOrd i (true, false) (false, true) hpi (by simp) _ n hcB
        have e3 := hnoBlank (isPin pin false true) _ (2 * n) hcC
        have e5 := hyesOrd i false true hpi _ n hcB
        simp only [wsBU1, wsBU0, wsCL1, wsAU0, wsBL1, wsCL0]
        rw [e1, e2, e3, e5]; simp
      have hbh := hi_blocks ordb eqb i
      have hhB := hbh.2.2.1
      have hhC := hbh.2.2.2.1
      have hOutH : (run C.gates (mkHi ordb eqb i ++ [false, true])).getD C.output false = false := by
        rw [heval_out _ hbh.1 hbh.2.2.2.2.1]
        have e1 := hnoOrd i (true, true) (false, true) hpi (by simp) _ n hhB
        have e3 := hyesUnit i false true hpi _ (2 * n) hhC
        simp only [wsBU1, wsBU0, wsCL1, wsAU0, wsBL1, wsCL0]
        rw [e1, e3]; simp
      refine ⟨hOutC, hOutH, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hcomp_all _ hbh.1, hOutH]; rfl
    · have hOutC : (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = false := by
        rw [heval_out _ hbc.1 hbc.2.2.2.2.1]
        have e1 := hnoOrd i (true, true) (true, false) hpi (by simp) _ n hcB
        have e2 := hyesOrd i true false hpi _ n hcB
        simp only [wsBU1, wsBU0, wsCL1, wsAU0, wsBL1, wsCL0]
        rw [e1, e2]; simp
      have hbl := lo_blocks eqb i
      have hlA : ∀ k : Fin n, (mkLo eqb i ++ [false, true]).getD (0 + k.val) false = eqb k i :=
        fun k => by rw [Nat.zero_add]; exact hbl.2.1 k
      have hlB := hbl.2.2.1
      have hlC := hbl.2.2.2.1
      have hOutL : (run C.gates (mkLo eqb i ++ [false, true])).getD C.output false = true := by
        rw [heval_out _ hbl.1 hbl.2.2.2.2.1]
        have e1 := hnoBlank (isPin pin true true) _ n hlB
        have e2 := hnoBlank (isPin pin true false) _ n hlB
        have e3 := hnoBlank (isPin pin false true) _ (2 * n) hlC
        have e4 := hyesUnit i true false hpi _ 0 hlA
        simp only [wsBU1, wsBU0, wsCL1, wsAU0, wsBL1, wsCL0]
        rw [e1, e2, e3, e4]; simp
      refine ⟨hOutC, hOutL, ?_⟩
      simp only [↓reduceIte]
      rw [hcomp_all _ hbl.1, hOutL]; rfl
    · have hOutC : (run C.gates (mkCore ordb i ++ [false, true])).getD C.output false = true := by
        rw [heval_out _ hbc.1 hbc.2.2.2.2.1]
        have e1 := hyesOrd i true true hpi _ n hcB
        simp only [wsBU1, wsBU0, wsCL1, wsAU0, wsBL1, wsCL0]
        rw [e1]; simp
      have hbl := lo_blocks eqb i
      have hlA : ∀ k : Fin n, (mkLo eqb i ++ [false, true]).getD (0 + k.val) false = eqb k i :=
        fun k => by rw [Nat.zero_add]; exact hbl.2.1 k
      have hlB := hbl.2.2.1
      have hlC := hbl.2.2.2.1
      have hOutL : (run C.gates (mkLo eqb i ++ [false, true])).getD C.output false = false := by
        rw [heval_out _ hbl.1 hbl.2.2.2.2.1]
        have e1 := hnoBlank (isPin pin true true) _ n hlB
        have e2 := hnoBlank (isPin pin true false) _ n hlB
        have e3 := hnoBlank (isPin pin false true) _ (2 * n) hlC
        have e4 := hnoUnit i (true, false) (true, true) hpi (by simp) _ 0 hlA
        have e5 := hnoBlank (isPin pin false true) _ n hlB
        have e6 := hnoBlank (isPin pin false false) _ (2 * n) hlC
        simp only [wsBU1, wsBU0, wsCL1, wsAU0, wsBL1, wsCL0]
        rw [e1, e2, e3, e4, e5, e6]; rfl
      refine ⟨hOutC, hOutL, ?_⟩
      simp only [↓reduceIte]
      rw [hcomp_all _ hbl.1, hOutL]; rfl

end PEqualNP.Outside.L_lib_1293

theorem PEqualNP.Outside.L_lib_1293 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n : Nat) (ord : Fin n → Fin n → Prop) (pin : Fin n → Option (Bool × Bool)),
  (∀ i, ord i i) → (∀ i j k, ord i j → ord j k → ord i k) →
  (∀ i j, ord i j → ord j i → i=j) →
  let le := fun (a b : Bool × Bool) => a=b ∨ (a.1=false ∧ b.1=true)
  let ext := fun (g : Fin n → Bool × Bool) =>
    (∀ i j, ord i j → le (g i) (g j)) ∧ ∀ i v, pin i=some v → g i=v
  let blank := List.replicate n false
  let unit := fun (i : Fin n) => List.ofFn (fun k : Fin n => decide (k=i))
  let down := fun (i : Fin n) => List.ofFn (fun k : Fin n => decide (ord k i))
  let core := fun i => down i ++ down i ++ blank
  let lo := fun i => unit i ++ blank ++ blank
  let hi := fun i => down i ++ down i ++ unit i
  let wire := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (q : Nat) =>
    (C.wires (x ++ [false,true])).getD q false
  let fit := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*n+2) C ∧
    C.output < 3*n+2+C.size ∧ p < 3*n+2+C.size ∧
    (∀ i, wire C (core i) p = !(wire C (core i) C.output)) ∧
    ∀ i v, pin i=some v → let y := if v.1 then lo i else hi i
      wire C (core i) C.output=v.2 ∧ wire C y C.output= !v.2 ∧ wire C y p=v.2
  ((∃ g, ext g) ↔ ∃ C p, fit C p ∧ PEqualNP.NotBracket.notCount C ≤ 1) ∧
  (∀ g, ext g → ∃ C p, fit C p ∧ C.size ≤ 32*(n+1)^2 ∧ PEqualNP.NotBracket.notCount C=1 ∧
    ∃ j : Fin C.size, (C.gates.getD j.val ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
      PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ i,
      wire C (core i) C.output=(g i).2 ∧ wire C (core i) (3*n+2+j.val)= !(g i).1) ∧
  ((∀ i j a b, pin i=some a → pin j=some b → ord i j → le a b) →
    ∃ C p, fit C p ∧ PEqualNP.NotBracket.notCount C ≤ 2 ∧ C.size ≤ 32*(n+1)^2) := by
  intro n ord pin hrefl htrans _
  dsimp only
  let ordb : Fin n → Fin n → Bool := fun k i => @decide (ord k i) (Classical.propDecidable _)
  let eqb : Fin n → Fin n → Bool := fun k i => @decide (k = i) (Classical.propDecidable _)
  have hordb : ∀ k i, ordb k i = true ↔ ord k i := fun _ _ => @decide_eq_true_iff _ (Classical.propDecidable _)
  have heqb : ∀ k i, eqb k i = true ↔ k = i := fun _ _ => @decide_eq_true_iff _ (Classical.propDecidable _)
  have hpart2 : ∀ g : Fin n → Bool × Bool,
      ((∀ i j, ord i j → g i = g j ∨ (g i).1 = false ∧ (g j).1 = true) ∧
        ∀ i v, pin i = some v → g i = v) →
      ∃ C p,
        (PEqualNP.MetaComplexity.FanInTwo C ∧
         PEqualNP.MetaComplexity.NestedCover.ReadsBack (3 * n + 2) C ∧
         C.output < 3 * n + 2 + C.size ∧ p < 3 * n + 2 + C.size ∧
         (∀ i, (C.wires (PEqualNP.Outside.L_lib_1293.mkCore ordb i ++ [false, true])).getD p false =
           !((C.wires (PEqualNP.Outside.L_lib_1293.mkCore ordb i ++ [false, true])).getD C.output false)) ∧
         ∀ i v, pin i = some v →
           (C.wires (PEqualNP.Outside.L_lib_1293.mkCore ordb i ++ [false, true])).getD C.output false = v.2 ∧
           (C.wires ((@ite _ (v.1 = true) (Classical.propDecidable _) (PEqualNP.Outside.L_lib_1293.mkLo eqb i)
             (PEqualNP.Outside.L_lib_1293.mkHi ordb eqb i)) ++ [false, true])).getD C.output false = !v.2 ∧
           (C.wires ((@ite _ (v.1 = true) (Classical.propDecidable _) (PEqualNP.Outside.L_lib_1293.mkLo eqb i)
             (PEqualNP.Outside.L_lib_1293.mkHi ordb eqb i)) ++ [false, true])).getD p false = v.2) ∧
        C.size ≤ 32 * (n + 1) ^ 2 ∧
        PEqualNP.NotBracket.notCount C = 1 ∧
        ∃ j : Fin C.size,
          (C.gates.getD j.val ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op =
            PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∀ i,
            (C.wires (PEqualNP.Outside.L_lib_1293.mkCore ordb i ++ [false, true])).getD C.output false = (g i).2 ∧
            (C.wires (PEqualNP.Outside.L_lib_1293.mkCore ordb i ++ [false, true])).getD (3 * n + 2 + j.val) false = !(g i).1 := by
    intro g hg
    obtain ⟨C, p, h1, h2, h3, h4, h5, h6, h7, h8, j, hj1, hj2⟩ :=
      PEqualNP.Outside.L_lib_1293.build_one_not ord pin hrefl ordb eqb hordb heqb g hg.1 hg.2
    refine ⟨C, p, ⟨h1, h2, h3, h4, h5, fun i v hv => ?_⟩, h7, h8, j, hj1, hj2⟩
    have h := h6 i v hv
    cases hv1 : v.1
    · simp only [hv1, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact h
    · simp only [hv1, ↓reduceIte] at h ⊢; exact h
  refine ⟨⟨?_, ?_⟩, hpart2, ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨C, p, hfit, _, hnc, _⟩ := hpart2 g hg
    exact ⟨C, p, hfit, Nat.le_of_eq hnc⟩
  · rintro ⟨C, p, ⟨h1, h2, _, _, h5, h6⟩, hnc⟩
    refine PEqualNP.Outside.L_lib_1293.ext_of_notCount_le_one ord pin hrefl htrans
      ordb eqb hordb heqb C p h1 h2 h5 (fun i v hv => ?_) hnc
    have h := h6 i v hv
    cases hv1 : v.1
    · simp only [hv1, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact h
    · simp only [hv1, ↓reduceIte] at h ⊢; exact h
  · intro hcons
    obtain ⟨C, p, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      PEqualNP.Outside.L_lib_1293.build_two_not ord pin hrefl ordb eqb hordb heqb hcons
    refine ⟨C, p, ⟨h1, h2, h3, h4, h5, fun i v hv => ?_⟩, h7, h8⟩
    have h := h6 i v hv
    cases hv1 : v.1
    · simp only [hv1, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact h
    · simp only [hv1, ↓reduceIte] at h ⊢; exact h
