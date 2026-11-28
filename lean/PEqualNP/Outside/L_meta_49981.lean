import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49981

open PEqualNP.CircuitLowerBounds

def gm (W : List ℕ) (g : Gate) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => W.getD i 0).foldr (fun a b => a &&& b) 31
  | GateOp.or => (g.inputs.map fun i => W.getD i 0).foldr (fun a b => a ||| b) 0
  | GateOp.not => 31 ^^^ ((g.inputs.map fun i => W.getD i 0).headD 0)
  | _ => 0

def masks (gs : List Gate) (W : List ℕ) : List ℕ := gs.foldl (fun W g => W ++ [gm W g]) W

def init : List ℕ := [30, 28, 24, 16, 0, 31]

def cnt (W : List ℕ) : ℕ := ([8, 14, 26].filter (fun T => decide (T ∉ W))).length

def monoL (W : List ℕ) : List ℕ := 31 :: 0 :: (W ++ W.flatMap (fun a => W.flatMap (fun b => [a &&& b, a ||| b])))

def notL (W : List ℕ) : List ℕ := 31 :: W.map (fun a => 31 ^^^ a)

def bits (L : List ℕ) : ℕ := L.foldr (fun v s => s ||| (1 <<< v)) 0

def anyBits (m : ℕ) (f : ℕ → Bool) : Bool := (List.range 32).any (fun v => m.testBit v && f v)

def explore : ℕ → ℕ → List ℕ → Bool
  | 0, _, W => cnt W == 0
  | g + 1, n, W => cnt W == 0 || (decide (cnt W ≤ g + 1) &&
      (anyBits (bits (monoL W)) (fun v => explore g n (W ++ [v])) ||
       (decide (0 < n) && anyBits (bits (notL W)) (fun v => explore g (n - 1) (W ++ [v])))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check : explore 5 2 init = false := by decide +kernel

theorem bits_mem : ∀ (L : List ℕ) (v : ℕ), v ∈ L → (bits L).testBit v = true := by
  intro L
  induction L with
  | nil => intro v h; simp at h
  | cons x L ih =>
    intro v h
    simp only [bits, List.foldr_cons] at *
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp h with rfl | h
    · simp [Nat.testBit_shiftLeft]
    · rw [ih v h]; simp

theorem anyBits_of {m : ℕ} {f : ℕ → Bool} {v : ℕ} (hv : v < 32) (hm : m.testBit v = true) (hf : f v = true) :
    anyBits m f = true := by
  unfold anyBits
  rw [List.any_eq_true]
  exact ⟨v, List.mem_range.mpr hv, by simp [hm, hf]⟩

theorem lt32_testBit {x : ℕ} (hx : x < 32) {i : ℕ} (hi : 5 ≤ i) : x.testBit i = false := by
  apply Nat.testBit_eq_false_of_lt
  calc x < 32 := hx
    _ = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

theorem testBit31 {t : ℕ} (ht : t < 5) : (31 : ℕ).testBit t = true := by
  interval_cases t <;> decide

theorem foldr_and_testBit (ms : List ℕ) {t : ℕ} (ht : t < 5) :
    (ms.foldr (fun a b => a &&& b) 31).testBit t = ms.all (fun m => m.testBit t) := by
  induction ms with
  | nil => simp [testBit31 ht]
  | cons x ms ih => simp [Nat.testBit_and, ih]

theorem foldr_or_testBit (ms : List ℕ) (t : ℕ) :
    (ms.foldr (fun a b => a ||| b) 0).testBit t = ms.any (fun m => m.testBit t) := by
  induction ms with
  | nil => simp
  | cons x ms ih => simp [Nat.testBit_or, ih]

theorem xor31_testBit (m : ℕ) {t : ℕ} (ht : t < 5) : (31 ^^^ m).testBit t = !(m.testBit t) := by
  rw [Nat.testBit_xor, testBit31 ht]; simp

def Rel (t : ℕ) (w : List Bool) (W : List ℕ) : Prop :=
  w.length = W.length ∧ ∀ k, w.getD k false = (W.getD k 0).testBit t

theorem gate_val {t : ℕ} (ht : t < 5) {w : List Bool} {W : List ℕ} (h : Rel t w W) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (gm W g).testBit t := by
  have hmap : (g.inputs.map fun i => w.getD i false) =
      (g.inputs.map fun i => W.getD i 0).map (fun m => m.testBit t) := by
    simp only [List.map_map, Function.comp_def, h.2]
  rw [hmap]
  rcases hg with h1 | h1 | h1
  · rw [h1]; simp only [gm, h1]
    rw [foldr_and_testBit _ ht]
    simp [GateOp.eval, List.all_map, Function.comp_def]
  · rw [h1]; simp only [gm, h1]
    rw [foldr_or_testBit]
    simp [GateOp.eval, List.any_map, Function.comp_def]
  · rw [h1]; simp only [gm, h1, GateOp.eval, xor31_testBit _ ht]
    cases (g.inputs.map fun i => W.getD i 0) with
    | nil => simp
    | cons a l => simp

theorem rel_step {t : ℕ} (ht : t < 5) {w : List Bool} {W : List ℕ} (h : Rel t w W) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    Rel t (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W ++ [gm W g]) := by
  refine ⟨by simp [h.1], fun k => ?_⟩
  rcases lt_trichotomy k w.length with hk | hk | hk
  · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (h.1 ▸ hk)]
    exact h.2 k
  · subst hk
    rw [gate_val ht h g hg, List.getD_append_right _ _ _ _ (le_refl _),
      List.getD_append_right _ _ _ _ (h.1 ▸ le_refl _)]
    simp [h.1]
  · have h1 := h.1
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem rel_fold {t : ℕ} (ht : t < 5) : ∀ (gs : List Gate) (w : List Bool) (W : List ℕ),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) → Rel t w W →
    Rel t (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) (masks gs W) := by
  intro gs
  induction gs with
  | nil => intro w W _ h; simpa [masks] using h
  | cons g gs ih =>
    intro w W hg h
    simp only [List.foldl_cons, masks] at *
    exact ih _ _ (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (rel_step ht h g (hg g List.mem_cons_self))

theorem masks_append : ∀ (gs : List Gate) (W : List ℕ), ∃ L : List ℕ, masks gs W = W ++ L ∧ L.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro W; exact ⟨[], by simp [masks], rfl⟩
  | cons g gs ih =>
    intro W
    obtain ⟨L, hL, hl⟩ := ih (W ++ [gm W g])
    refine ⟨gm W g :: L, ?_, by simp [hl]⟩
    simp only [masks, List.foldl_cons] at *
    rw [hL]; simp

theorem getD_cases (W : List ℕ) (i : ℕ) : W.getD i 0 = 0 ∨ W.getD i 0 ∈ W := by
  by_cases hi : i < W.length
  · right; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · left; exact List.getD_eq_default _ _ (by omega)

theorem getD_lt {W : List ℕ} (hW : ∀ x ∈ W, x < 32) (i : ℕ) : W.getD i 0 < 32 := by
  rcases getD_cases W i with h | h
  · rw [h]; norm_num
  · exact hW _ h

theorem gm_lt {W : List ℕ} (hW : ∀ x ∈ W, x < 32) (g : Gate) : gm W g < 32 := by
  unfold gm
  split
  · have : ∀ ms : List ℕ, ms.foldr (fun a b => a &&& b) 31 ≤ 31 := by
      intro ms; induction ms with
      | nil => simp
      | cons x ms ih => simp only [List.foldr_cons]; exact le_trans Nat.and_le_right ih
    exact lt_of_le_of_lt (this _) (by norm_num)
  · have : ∀ ms : List ℕ, (∀ m ∈ ms, m < 32) → ms.foldr (fun a b => a ||| b) 0 < 32 := by
      intro ms; induction ms with
      | nil => intro _; simp
      | cons x ms ih =>
        intro hm
        simp only [List.foldr_cons]
        have h1 : x < 2 ^ 5 := by simpa using hm x List.mem_cons_self
        have h2 : ms.foldr (fun a b => a ||| b) 0 < 2 ^ 5 := by simpa using ih (fun m hm' => hm m (List.mem_cons_of_mem _ hm'))
        simpa using Nat.or_lt_two_pow h1 h2
    exact this _ (by intro m hm; simp only [List.mem_map] at hm; obtain ⟨i, _, rfl⟩ := hm; exact getD_lt hW i)
  · have hh : ((g.inputs.map fun i => W.getD i 0).headD 0) < 2 ^ 5 := by
      cases hc : g.inputs with
      | nil => simp
      | cons i l => simpa using getD_lt hW i
    have : 31 ^^^ ((g.inputs.map fun i => W.getD i 0).headD 0) < 2 ^ 5 := Nat.xor_lt_two_pow (by norm_num) hh
    simpa using this
  · norm_num

theorem masks_lt : ∀ (gs : List Gate) (W : List ℕ), (∀ x ∈ W, x < 32) → ∀ x ∈ masks gs W, x < 32 := by
  intro gs
  induction gs with
  | nil => intro W h; simpa [masks] using h
  | cons g gs ih =>
    intro W h
    simp only [masks, List.foldl_cons] at *
    apply ih
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h x hx
    · simp at hx; rw [hx]; exact gm_lt h g

theorem and31 {u : ℕ} (hu : u < 32) : u &&& 31 = u := by
  have : (31 : ℕ) = 2 ^ 5 - 1 := by norm_num
  rw [this, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt (by simpa using hu)

theorem gm_mono {W : List ℕ} (hW : ∀ x ∈ W, x < 32) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2) : gm W g ∈ monoL W := by
  have mem2 : ∀ a b, a ∈ W → b ∈ W → (a &&& b) ∈ monoL W ∧ (a ||| b) ∈ monoL W := by
    intro a b ha hb
    constructor
    · simp only [monoL, List.mem_cons, List.mem_append, List.mem_flatMap]
      right; right; right; exact ⟨a, ha, b, hb, by simp⟩
    · simp only [monoL, List.mem_cons, List.mem_append, List.mem_flatMap]
      right; right; right; exact ⟨a, ha, b, hb, by simp⟩
  have memW : ∀ a, a ∈ W → a ∈ monoL W := fun a ha => by
    apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; exact List.mem_append_left _ ha
  have mem0 : (0 : ℕ) ∈ monoL W := by simp [monoL]
  have mem31 : (31 : ℕ) ∈ monoL W := by simp [monoL]
  have memu : ∀ i, W.getD i 0 ∈ monoL W := fun i => by
    rcases getD_cases W i with h | h
    · rw [h]; exact mem0
    · exact memW _ h
  match hc : g.inputs, hl with
  | [], _ => rcases hg with h1 | h1 <;> simp [gm, h1, hc, mem31, mem0]
  | [i], _ =>
    rcases hg with h1 | h1
    · simp only [gm, h1, hc, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      rw [and31 (getD_lt hW i)]; exact memu i
    · simp only [gm, h1, hc, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
      exact memu i
  | [i, j], _ =>
    rcases getD_cases W i with hi | hi <;> rcases getD_cases W j with hj | hj <;> rcases hg with h1 | h1 <;>
      simp only [gm, h1, hc, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero,
        and31 (getD_lt hW j), hi, hj, Nat.zero_and, Nat.and_zero, Nat.zero_or, Nat.or_zero] <;>
      (first | exact mem0 | exact memu i | exact memu j | exact (mem2 _ _ hi hj).1 | exact (mem2 _ _ hi hj).2 | (rw [← hi]; exact memu i) | (rw [← hj]; exact memu j))
  | _ :: _ :: _ :: _, h => simp at h

theorem gm_not {W : List ℕ} (g : Gate) (hg : g.op = GateOp.not) : gm W g ∈ notL W := by
  simp only [gm, hg]
  cases hc : g.inputs with
  | nil => simp [notL]
  | cons i l =>
    simp only [List.map_cons, List.headD_cons]
    rcases getD_cases W i with h | h
    · rw [h]; simp [notL]
    · simp only [notL]; apply List.mem_cons_of_mem; exact List.mem_map_of_mem h

theorem cnt_le {W L : List ℕ} (h : cnt (W ++ L) = 0) : cnt W ≤ L.length := by
  unfold cnt at *
  have hsub : ([8, 14, 26].filter (fun T => decide (T ∉ W))) ⊆ L := by
    intro T hT
    simp only [List.mem_filter, decide_eq_true_eq] at hT
    have : T ∉ (([8, 14, 26] : List ℕ).filter (fun T => decide (T ∉ W ++ L))) := by
      rw [List.length_eq_zero_iff.mp h]; simp
    simp only [List.mem_filter, decide_eq_true_eq, not_and, not_not] at this
    rcases List.mem_append.mp (this hT.1) with h1 | h1
    · exact absurd h1 hT.2
    · exact h1
  have hnd : ([8, 14, 26].filter (fun T => decide (T ∉ W))).Nodup := List.Nodup.filter _ (by decide)
  exact (hnd.subperm hsub).length_le

theorem sound : ∀ (gs : List Gate) (W : List ℕ) (g n : ℕ), (∀ x ∈ W, x < 32) →
    (∀ gt ∈ gs, (gt.op = GateOp.and ∨ gt.op = GateOp.or ∨ gt.op = GateOp.not) ∧ gt.inputs.length ≤ 2) →
    gs.length ≤ g → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n →
    cnt (masks gs W) = 0 → explore g n W = true := by
  intro gs
  induction gs with
  | nil =>
    intro W g n _ _ _ _ h
    simp only [masks, List.foldl_nil] at h
    cases g with
    | zero => simp [explore, h]
    | succ g => simp [explore, h]
  | cons gt gs ih =>
    intro W g n hW hg hlen hn h
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hlen; omega⟩
    have hgt := hg gt List.mem_cons_self
    have hrest : ∀ x ∈ gs, (x.op = GateOp.and ∨ x.op = GateOp.or ∨ x.op = GateOp.not) ∧ x.inputs.length ≤ 2 :=
      fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have hW' : ∀ x ∈ W ++ [gm W gt], x < 32 := by
      intro x hx; rcases List.mem_append.mp hx with hx | hx
      · exact hW x hx
      · simp at hx; rw [hx]; exact gm_lt hW gt
    have hm : masks (gt :: gs) W = masks gs (W ++ [gm W gt]) := by simp [masks]
    have hcnt : cnt W ≤ g' + 1 := by
      obtain ⟨L, hL, hl⟩ := masks_append (gt :: gs) W
      rw [hL] at h
      have := cnt_le h
      simp at hl hlen; omega
    rw [hm] at h
    simp only [explore, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    right
    refine ⟨hcnt, ?_⟩
    have hv := gm_lt hW gt
    by_cases hnot : gt.op = GateOp.not
    · right
      have hn' : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n - 1 := by
        simp only [PEqualNP.NotBracket.notCount, List.filter_cons] at hn ⊢
        simp [hnot] at hn; omega
      have hpos : 0 < n := by
        simp only [PEqualNP.NotBracket.notCount, List.filter_cons] at hn
        simp [hnot] at hn; omega
      refine ⟨hpos, anyBits_of hv (bits_mem _ _ (gm_not gt hnot)) ?_⟩
      exact ih _ g' (n - 1) hW' hrest (by simp at hlen; omega) hn' h
    · left
      have hmo : gt.op = GateOp.and ∨ gt.op = GateOp.or := by
        rcases hgt.1 with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · exact absurd h1 hnot
      have hn' : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n := by
        simp only [PEqualNP.NotBracket.notCount, List.filter_cons] at hn ⊢
        simp [hnot] at hn; omega
      refine anyBits_of hv (bits_mem _ _ (gm_mono hW gt hmo hgt.2)) ?_
      exact ih _ g' n hW' hrest (by simp at hlen; omega) hn' h

theorem base (t : Fin 5) :
    Rel t.val ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true]) init := by
  refine ⟨by simp [init], fun k => ?_⟩
  by_cases hk : k < 6
  · fin_cases t <;> interval_cases k <;> decide
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [init]; omega)]
    simp

theorem pins {M : List ℕ} (hM : ∀ x ∈ M, x < 32) (k : ℕ) (hk : k < M.length) (c : ℕ) (hc : c < 32)
    (h : ∀ t : Fin 5, (M.getD k 0).testBit t.val = c.testBit t.val) : c ∈ M := by
  have hlt : M.getD k 0 < 32 := getD_lt hM k
  have heq : M.getD k 0 = c := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 5
    · exact h ⟨i, hi⟩
    · rw [lt32_testBit hlt (by omega), lt32_testBit hc (by omega)]
  rw [← heq, List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

end PEqualNP.Outside.L_meta_49981

open PEqualNP.Outside.L_meta_49981 in
theorem PEqualNP.Outside.L_meta_49981 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (14 : Nat).testBit t.val ∧
    w.getD r.val false = (26 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsize, hall⟩
  set M := masks D.gates init with hMdef
  have hg : ∀ gt ∈ D.gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      gt.inputs.length ≤ 2 := by
    intro gt hgt
    obtain ⟨h1, h2⟩ := hfan gt hgt
    refine ⟨?_, h2⟩
    simpa using h1
  have hrel : ∀ t : Fin 5, Rel t.val (D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true])) M :=
    fun t => rel_fold t.isLt D.gates _ _ (fun x hx => (hg x hx).1) (base t)
  have hMlt : ∀ x ∈ M, x < 32 := masks_lt _ _ (by decide)
  have hlen : M.length = 6 + D.size := by
    obtain ⟨L, hL, hl⟩ := masks_append D.gates init
    rw [hMdef, hL]; simp [init, hl, PEqualNP.CircuitLowerBounds.Circuit.size]; omega
  have hpin : ∀ (k : Fin (6 + D.size)) (c : ℕ), c < 32 →
      (∀ t : Fin 5, (D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true])).getD k.val false = c.testBit t.val) → c ∈ M := by
    intro k c hc h
    refine pins hMlt k.val (by rw [hlen]; exact k.isLt) c hc (fun t => ?_)
    rw [← (hrel t).2 k.val]; exact h t
  have h8 : 8 ∈ M := hpin p 8 (by norm_num) (fun t => (hall t).1)
  have h14 : 14 ∈ M := hpin q 14 (by norm_num) (fun t => (hall t).2.1)
  have h26 : 26 ∈ M := hpin r 26 (by norm_num) (fun t => (hall t).2.2)
  have hc : cnt M = 0 := by simp [cnt, h8, h14, h26]
  have := sound D.gates init 5 2 (by decide) hg hsize hnot (hMdef ▸ hc)
  rw [check] at this
  exact Bool.false_ne_true this
