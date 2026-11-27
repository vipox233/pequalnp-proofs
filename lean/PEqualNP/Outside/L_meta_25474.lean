import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25474_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def A6 (u v : Fin 6) : Bool :=
  (1108391270 : ℕ).testBit (6 * u.val + v.val)

def D13 : Circuit :=
  { gates :=
      [ ⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 8]⟩,
        ⟨.or, [3, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [5, 11]⟩,
        ⟨.or, [14, 17]⟩, ⟨.or, [12, 15]⟩, ⟨.and, [18, 19]⟩,
        ⟨.or, [12, 14]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [13, 20]⟩,
        ⟨.and, [22, 23]⟩ ]
    output := 24 }

lemma D13_mono : Monotone2 D13 := by
  intro g hg
  simp only [D13, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

lemma D13_rep : Represents A6 D13 := by
  intro u v
  revert u v
  decide

lemma D13_size : D13.size ≤ 13 := by
  decide

lemma A6_repSize : RepSizeAtMost A6 13 :=
  ⟨D13, D13_mono, D13_size, D13_rep⟩

lemma A6_not_all_row : ∀ u : Fin 6, ∃ v : Fin 6, A6 u v = false := by decide
lemma A6_not_all_col : ∀ v : Fin 6, ∃ u : Fin 6, A6 u v = false := by decide
lemma A6_row_not_le_all : ∀ a : Fin 6, ∃ b : Fin 6, b ≠ a ∧ ∃ v : Fin 6, A6 a v = true ∧ A6 b v = false := by decide
lemma A6_col_not_le_all : ∀ v : Fin 6, ∃ w : Fin 6, w ≠ v ∧ ∃ a : Fin 6, A6 a v = true ∧ A6 a w = false := by decide
lemma A6_k22_free : ∀ u1 u2 : Fin 6, u1 ≠ u2 → ∀ v1 v2 : Fin 6, v1 ≠ v2 →
    ¬ (A6 u1 v1 = true ∧ A6 u1 v2 = true ∧ A6 u2 v1 = true ∧ A6 u2 v2 = true) := by decide
lemma A6_00_false : A6 0 0 = false := by decide
lemma A6_has_edge : ∃ u v : Fin 6, A6 u v = true := by decide

def edges6 : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun p => A6 p.1 p.2 = true)

lemma edges6_card : edges6.card = 12 := by decide

def fool6 : Fin 6 → Fin 6 × Fin 6
  | ⟨0, _⟩ => (3, 2)
  | ⟨1, _⟩ => (4, 1)
  | ⟨2, _⟩ => (5, 0)
  | ⟨3, _⟩ => (2, 3)
  | ⟨4, _⟩ => (1, 4)
  | ⟨5, _⟩ => (0, 5)

lemma fool6_edge : ∀ i : Fin 6, A6 (fool6 i).1 (fool6 i).2 = true := by decide

lemma fool6_sep : ∀ i j : Fin 6, i ≠ j →
    ¬ (A6 (fool6 i).1 (fool6 j).2 = true ∧ A6 (fool6 j).1 (fool6 i).2 = true) := by decide

def StrictC (C : Circuit) : Prop :=
  Monotone2 C ∧ Represents A6 C ∧
  ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → g.op = .and →
    ∀ (u v : Fin 6), (C.wires (oneEach u v)).getD (12 + k) false = true → A6 u v = true

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl evalStep x := rfl

lemma foldl_evalStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl evalStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, evalStep, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_evalStep_getD_prefix (gs : List Gate) (acc : List Bool) (i : ℕ)
    (hi : i < acc.length) :
    (gs.foldl evalStep acc).getD i false = acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (evalStep acc g).length := by
      simp only [evalStep, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih (evalStep acc g) hlt]
    simp only [evalStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma evalStep_getD_self (acc : List Bool) (g : Gate) :
    (evalStep acc g).getD acc.length false = g.op.eval (g.inputs.map fun i => acc.getD i false) := by
  simp [evalStep, List.getD_eq_getElem?_getD]

lemma evalStep_getD_lt (acc : List Bool) (g : Gate) (i : ℕ) (hi : i < acc.length) :
    (evalStep acc g).getD i false = acc.getD i false := by
  simp [evalStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma gateOp_mono (op : GateOp) (hop : op = .and ∨ op = .or) (l1 l2 : List Bool)
    (hlen : l1.length = l2.length)
    (hle : ∀ i, l1.getD i false = true → l2.getD i false = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true]
    intro h x hx
    rcases List.getElem_of_mem hx with ⟨i, hi, rfl⟩
    have hi1 : i < l1.length := by omega
    have h1 : l1.getD i false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
      exact h l1[i] (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h2
  · simp only [GateOp.eval, List.any_eq_true]
    rintro ⟨x, hx, rfl⟩
    rcases List.getElem_of_mem hx with ⟨i, hi, hxi⟩
    have hi2 : i < l2.length := by omega
    have h1 : l1.getD i false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact hxi
    have h2 := hle i h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2] at h2
    exact ⟨l2[i], List.getElem_mem hi2, h2⟩

lemma foldl_evalStep_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (acc1 acc2 : List Bool) (hlen : acc1.length = acc2.length)
    (hle : ∀ i, acc1.getD i false = true → acc2.getD i false = true) :
    ∀ i, (gs.foldl evalStep acc1).getD i false = true →
      (gs.foldl evalStep acc2).getD i false = true := by
  induction gs generalizing acc1 acc2 with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hmono g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op = .and ∨ g'.op = .or := fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    apply ih hgs (evalStep acc1 g) (evalStep acc2 g)
    · simp [evalStep, hlen]
    · intro i hi
      by_cases hlt : i < acc1.length
      · rw [evalStep_getD_lt acc1 g i hlt] at hi
        rw [evalStep_getD_lt acc2 g i (by omega)]
        exact hle i hi
      · by_cases heq : i = acc1.length
        · subst heq
          rw [evalStep_getD_self] at hi
          rw [hlen, evalStep_getD_self]
          apply gateOp_mono g.op hg _ _ (by simp) _ hi
          intro idx hidx
          by_cases hix : idx < g.inputs.length
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hix,
              Option.map_some, Option.getD_some] at hidx ⊢
            exact hle g.inputs[idx] hidx
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hidx
            cases hidx
        · have hge : (evalStep acc1 g).length ≤ i := by simp [evalStep]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hi
          cases hi

lemma foldl_evalStep_agree_without (gs : List Gate) (w0 : ℕ)
    (hno : ∀ g ∈ gs, w0 ∉ g.inputs)
    (acc1 acc2 : List Bool) (hlen : acc1.length = acc2.length)
    (hagree : ∀ i, i ≠ w0 → acc1.getD i false = acc2.getD i false) :
    ∀ i, i ≠ w0 → (gs.foldl evalStep acc1).getD i false = (gs.foldl evalStep acc2).getD i false := by
  induction gs generalizing acc1 acc2 with
  | nil => exact hagree
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg0 : w0 ∉ g.inputs := hno g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, w0 ∉ g'.inputs := fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
    apply ih hgs (evalStep acc1 g) (evalStep acc2 g)
    · simp [evalStep, hlen]
    · intro i hi
      by_cases hlt : i < acc1.length
      · rw [evalStep_getD_lt acc1 g i hlt, evalStep_getD_lt acc2 g i (by omega)]
        exact hagree i hi
      · by_cases heq : i = acc1.length
        · subst heq
          rw [evalStep_getD_self, hlen, evalStep_getD_self]
          congr 1
          apply List.map_congr_left
          intro z hz
          exact hagree z (fun h => hg0 (h ▸ hz))
        · have hge1 : (evalStep acc1 g).length ≤ i := by simp [evalStep]; omega
          have hge2 : (evalStep acc2 g).length ≤ i := by simp [evalStep, ← hlen]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
              List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]

lemma oneEach_length (u v : Fin 6) : (oneEach u v).length = 12 := by
  simp [oneEach]

lemma oneEach_getD (u v : Fin 6) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = 6 + v.val) := by
  unfold oneEach
  by_cases hi : i < 6
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hi])]
    simp only [List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some, Fin.ext_iff]
    rw [Bool.eq_iff_iff]; simp; omega
  · by_cases h12 : i < 12
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      have hj : i - 6 < 6 := by omega
      simp only [List.length_ofFn, List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some, Fin.ext_iff]
      rw [Bool.eq_iff_iff]; simp; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      have h1 : i ≠ u.val := by omega
      have h2 : i ≠ 6 + v.val := by omega
      simp [h1, h2]

def oneLeft6 (u : Fin 6) : List Bool :=
  List.ofFn (fun i : Fin 6 => decide (i = u)) ++ List.replicate 6 false

def oneRight6 (v : Fin 6) : List Bool :=
  List.replicate 6 false ++ List.ofFn (fun j : Fin 6 => decide (j = v))

lemma oneLeft6_length (u : Fin 6) : (oneLeft6 u).length = 12 := by simp [oneLeft6]
lemma oneRight6_length (v : Fin 6) : (oneRight6 v).length = 12 := by simp [oneRight6]

lemma oneLeft6_getD (u : Fin 6) (i : ℕ) :
    (oneLeft6 u).getD i false = decide (i = u.val) := by
  unfold oneLeft6
  by_cases hi : i < 6
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hi])]
    simp only [List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some, Fin.ext_iff]
  · by_cases h12 : i < 12
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem?_replicate, show i - 6 < 6 by omega, ↓reduceIte,
        Option.getD_some]
      have : i ≠ u.val := by omega
      simp [this]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      have : i ≠ u.val := by omega
      simp [this]

lemma oneRight6_getD (v : Fin 6) (i : ℕ) :
    (oneRight6 v).getD i false = decide (i = 6 + v.val) := by
  unfold oneRight6
  by_cases hi : i < 6
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hi])]
    simp only [List.getElem?_replicate, hi, ↓reduceIte, Option.getD_some]
    have : i ≠ 6 + v.val := by omega
    simp [this]
  · by_cases h12 : i < 12
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      have hj : i - 6 < 6 := by omega
      simp only [List.length_replicate, List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some,
        Fin.ext_iff]
      rw [Bool.eq_iff_iff]; simp; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      have : i ≠ 6 + v.val := by omega
      simp [this]

lemma wires_getD_input (C : Circuit) (u v : Fin 6) (i : ℕ) (hi : i < 12) :
    (C.wires (oneEach u v)).getD i false = (oneEach u v).getD i false := by
  rw [wires_eq_foldl]
  exact foldl_evalStep_getD_prefix C.gates (oneEach u v) i (by rw [oneEach_length]; exact hi)

lemma wires_getD_gate (C : Circuit) (x : List Bool) (hx : x.length = 12)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (12 + k) false =
      let g := C.gates.getD k ⟨.or, []⟩
      g.op.eval (g.inputs.map fun i => if i < 12 + k then (C.wires x).getD i false else false) := by
  rw [wires_eq_foldl]
  let gs1 := C.gates.take k
  let gk := C.gates.getD k ⟨.or, []⟩
  let gs2 := C.gates.drop (k + 1)
  have hsplit : C.gates = gs1 ++ gk :: gs2 := by
    have h1 : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    have h2 : C.gates.drop k = gk :: gs2 :=
      (List.drop_eq_getElem_cons hk).trans (by simp [gk, gs2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk])
    rw [h1, h2]
  have hlen1 : gs1.length = k := List.length_take_of_le (by omega)
  let acc1 := gs1.foldl evalStep x
  have hl1 : acc1.length = 12 + k := by rw [foldl_evalStep_length, hx, hlen1]
  have hpref : ∀ w < 12 + k, (C.gates.foldl evalStep x).getD w false = acc1.getD w false := by
    intro w hw
    conv_lhs => rw [hsplit, List.foldl_append]
    exact foldl_evalStep_getD_prefix (gk :: gs2) acc1 w (by omega)
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_evalStep_getD_prefix gs2 (evalStep acc1 gk) (12 + k) (by simp [evalStep, hl1]),
      ← hl1, evalStep_getD_self]
  dsimp only
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 12 + k
  · have hi' : i < acc1.length := by rw [hl1]; exact hi
    rw [if_pos hi', hpref i hi]
  · have hi' : ¬ (i < acc1.length) := by rw [hl1]; exact hi
    rw [if_neg hi', List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hl1]; omega)]
    rfl

lemma delete_gate_strict (C : Circuit) (hC : StrictC C)
    (k : ℕ) (hk : k < C.gates.length) (sub : ℕ)
    (hsub : sub < 12 + k ∨ sub = 12 + C.gates.length)
    (hcond :
      (12 + k ≠ C.output ∧ ∀ j, k < j → j < C.gates.length → 12 + k ∉ (C.gates.getD j ⟨.or, []⟩).inputs) ∨
      (∀ u v : Fin 6, (C.wires (oneEach u v)).getD (12 + k) false =
        if sub < 12 + k then (C.wires (oneEach u v)).getD sub false else false)) :
    ∃ D : Circuit, StrictC D ∧ D.size = C.size - 1 := by
  let s := C.gates.length
  let remap (w : ℕ) : ℕ := if w < 12 + k then w else if w = 12 + k then sub else w - 1
  let gs1 := C.gates.take k
  let gk := C.gates.getD k ⟨.or, []⟩
  let gs2 := C.gates.drop (k + 1)
  have hsplit : C.gates = gs1 ++ gk :: gs2 := by
    have h1 : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    have h2 : C.gates.drop k = gk :: gs2 :=
      (List.drop_eq_getElem_cons hk).trans (by simp [gk, gs2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk])
    rw [h1, h2]
  have hlen1 : gs1.length = k := List.length_take_of_le (by omega)
  let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map remap⟩
  let D : Circuit := ⟨gs1 ++ gs2.map mapG, remap C.output⟩
  have hDlen : D.gates.length = s - 1 := by
    simp only [D, List.length_append, List.length_map, gs1, gs2, List.length_take, List.length_drop]
    omega
  have hDwires : ∀ (u v : Fin 6),
      ∀ z, (z ≠ 12 + k ∨
        (C.wires (oneEach u v)).getD (12 + k) false =
          if sub < 12 + k then (C.wires (oneEach u v)).getD sub false else false) →
      (D.wires (oneEach u v)).getD (remap z) false = (C.wires (oneEach u v)).getD z false := by
    intro u v
    let x := oneEach u v
    have hxlen : x.length = 12 := oneEach_length u v
    let acc1 := gs1.foldl evalStep x
    have hl1 : acc1.length = 12 + k := by rw [foldl_evalStep_length, hxlen, hlen1]
    have hprefC : ∀ w < 12 + k, (C.wires x).getD w false = acc1.getD w false := by
      intro w hw
      rw [wires_eq_foldl, hsplit, List.foldl_append]
      exact foldl_evalStep_getD_prefix (gk :: gs2) acc1 w (by omega)
    have hgkC : (C.wires x).getD (12 + k) false = (evalStep acc1 gk).getD (12 + k) false := by
      rw [wires_eq_foldl, hsplit, List.foldl_append, List.foldl_cons]
      exact foldl_evalStep_getD_prefix gs2 (evalStep acc1 gk) (12 + k) (by simp [evalStep, hl1])
    have hbase : ∀ z, (z ≠ 12 + k ∨
        (C.wires x).getD (12 + k) false = if sub < 12 + k then (C.wires x).getD sub false else false) →
        acc1.getD (remap z) false = (evalStep acc1 gk).getD z false := by
      intro z hz
      by_cases hlt : z < 12 + k
      · have hrm : remap z = z := by simp [remap, hlt]
        rw [hrm, evalStep_getD_lt acc1 gk z (by omega)]
      · by_cases heq : z = 12 + k
        · subst heq
          rcases hz with hne | heqv
          · exact absurd rfl hne
          · have hrm : remap (12 + k) = sub := by simp [remap]
            rw [hrm, ← hgkC, heqv]
            split_ifs with hs
            · exact (hprefC sub hs).symm
            · have hsge : 12 + k ≤ sub := by omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
        · have hrm : remap z = z - 1 := by simp [remap, hlt, heq]
          rw [hrm, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
              List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [evalStep, hl1]; omega)]
    have hphase2 : ∀ (L : List Gate) (acc acc' : List Bool),
        acc.length = acc'.length + 1 →
        12 + k ≤ acc'.length →
        acc'.length + L.length ≤ 12 + s - 1 →
        (∀ g ∈ L, 12 + k ∉ g.inputs ∨
          (C.wires x).getD (12 + k) false = if sub < 12 + k then (C.wires x).getD sub false else false) →
        (∀ z, (z ≠ 12 + k ∨
          (C.wires x).getD (12 + k) false = if sub < 12 + k then (C.wires x).getD sub false else false) →
          acc'.getD (remap z) false = acc.getD z false) →
        ∀ z, (z ≠ 12 + k ∨
          (C.wires x).getD (12 + k) false = if sub < 12 + k then (C.wires x).getD sub false else false) →
          ((L.map mapG).foldl evalStep acc').getD (remap z) false =
          (L.foldl evalStep acc).getD z false := by
      intro L
      induction L with
      | nil => intro acc acc' _ _ _ _ hinv z hz; exact hinv z hz
      | cons g rest ih =>
        intro acc acc' hl hge hbd hno hinv z hz
        simp only [List.map_cons, List.foldl_cons]
        have hgno := hno g (List.mem_cons_self ..)
        have hval : (mapG g).op.eval ((mapG g).inputs.map fun i => acc'.getD i false) =
            g.op.eval (g.inputs.map fun i => acc.getD i false) := by
          simp only [mapG, List.map_map]
          congr 1; apply List.map_congr_left
          intro w hw
          apply hinv w
          rcases hgno with hnot | heqv
          · exact Or.inl (fun h => hnot (h ▸ hw))
          · exact Or.inr heqv
        have hstep_len : (evalStep acc' (mapG g)).length = acc'.length + 1 := by
          simp only [evalStep, List.length_append, List.length_cons, List.length_nil]
        have hbd_cons : acc'.length + (rest.length + 1) ≤ 12 + s - 1 := by
          simpa [List.length_cons] using hbd
        apply ih (evalStep acc g) (evalStep acc' (mapG g))
        · simp [evalStep, hl]
        · omega
        · omega
        · exact fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
        · intro w hw
          by_cases hlt : w < 12 + k
          · have hrm : remap w = w := by simp [remap, hlt]
            rw [hrm, evalStep_getD_lt acc' _ w (by omega), evalStep_getD_lt acc _ w (by omega)]
            have := hinv w hw; rwa [hrm] at this
          · by_cases heq : w = 12 + k
            · subst heq
              have hrm : remap (12 + k) = sub := by simp [remap]
              rw [hrm]
              rcases hsub with hs | hs
              · rw [evalStep_getD_lt acc' _ sub (by omega), evalStep_getD_lt acc _ (12 + k) (by omega)]
                have := hinv (12 + k) hw; rwa [hrm] at this
              · have hge' : (evalStep acc' (mapG g)).length ≤ sub := by
                  have : s = C.gates.length := rfl
                  omega
                rw [evalStep_getD_lt acc _ (12 + k) (by omega)]
                have := hinv (12 + k) hw; rw [hrm] at this
                rw [← this]
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge',
                    List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            · have hrm : remap w = w - 1 := by simp [remap, hlt, heq]
              rw [hrm]
              by_cases hlt2 : w < acc.length
              · rw [evalStep_getD_lt acc' _ (w - 1) (by omega), evalStep_getD_lt acc _ w hlt2]
                have := hinv w hw; rwa [hrm] at this
              · by_cases heq2 : w = acc.length
                · have heq' : w - 1 = acc'.length := by omega
                  rw [heq', heq2, evalStep_getD_self, evalStep_getD_self, hval]
                · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [evalStep]; omega),
                      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [evalStep]; omega)]
        · exact hz
    have hgs2_no : ∀ g ∈ gs2, 12 + k ∉ g.inputs ∨
        (C.wires x).getD (12 + k) false = if sub < 12 + k then (C.wires x).getD sub false else false := by
      intro g hg
      rcases hcond with ⟨_, hdead⟩ | heqv
      · left
        rcases List.getElem_of_mem hg with ⟨t, ht, rfl⟩
        have hidx : k + 1 + t < C.gates.length := by simp [gs2] at ht; omega
        have hget : gs2[t] = C.gates.getD (k + 1 + t) ⟨.or, []⟩ := by
          simp [gs2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        rw [hget]
        exact hdead (k + 1 + t) (by omega) hidx
      · exact Or.inr (heqv u v)
    intro z hz
    rw [wires_eq_foldl, wires_eq_foldl]
    change ((gs1 ++ gs2.map mapG).foldl evalStep x).getD (remap z) false =
      (C.gates.foldl evalStep x).getD z false
    rw [List.foldl_append, hsplit, List.foldl_append, List.foldl_cons]
    exact hphase2 gs2 (evalStep acc1 gk) acc1 (by simp [evalStep]) (by omega)
      (by simp [hl1, gs2]; omega) hgs2_no hbase z hz
  refine ⟨D, ⟨?_, ?_, ?_⟩, hDlen⟩
  · intro g hg
    simp only [D, List.mem_append, List.mem_map] at hg
    rcases hg with hg1 | ⟨g0, hg0, rfl⟩
    · exact hC.1 g (List.mem_of_mem_take hg1)
    · have := hC.1 g0 (List.mem_of_mem_drop hg0); exact ⟨this.1, by simp [mapG, this.2]⟩
  · intro u v
    rw [← hC.2.1 u v]
    change (D.wires (oneEach u v)).getD (remap C.output) false =
      (C.wires (oneEach u v)).getD C.output false
    apply hDwires u v C.output
    rcases hcond with ⟨hne, _⟩ | heqv
    · exact Or.inl hne.symm
    · exact Or.inr (heqv u v)
  · intro j g hj hgop u v htrue
    have hltj : j < D.gates.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hj
      cases hj
    by_cases hjk : j < k
    · have hgetD : D.gates[j]? = C.gates[j]? := by
        simp only [D, List.getElem?_append_left (by rw [hlen1]; exact hjk), gs1, List.getElem?_take_of_lt hjk]
      rw [hgetD] at hj
      have hw : (D.wires (oneEach u v)).getD (12 + j) false = (C.wires (oneEach u v)).getD (12 + j) false := by
        have hrm : remap (12 + j) = 12 + j := by simp [remap]; omega
        have := hDwires u v (12 + j) (Or.inl (by omega))
        rwa [hrm] at this
      rw [hw] at htrue
      exact hC.2.2 j g hj hgop u v htrue
    · have hidx : j + 1 < C.gates.length := by omega
      have hgetD : D.gates[j]? = some (mapG (C.gates[j + 1]'hidx)) := by
        change (gs1 ++ gs2.map mapG)[j]? = _
        rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1, List.getElem?_map,
            List.getElem?_drop]
        have heq : k + 1 + (j - k) = j + 1 := by omega
        rw [heq, List.getElem?_eq_getElem hidx]
        rfl
      rw [hgetD] at hj
      have hg_eq : mapG (C.gates[j + 1]'hidx) = g := Option.some.inj hj
      have hopC : (C.gates[j + 1]'hidx).op = .and := by
        have : (mapG (C.gates[j + 1]'hidx)).op = g.op := congrArg Gate.op hg_eq
        simpa [mapG] using this.trans hgop
      have hw : (D.wires (oneEach u v)).getD (12 + j) false =
          (C.wires (oneEach u v)).getD (12 + (j + 1)) false := by
        have hrm : remap (12 + (j + 1)) = 12 + j := by
          simp only [remap]
          split_ifs <;> omega
        have := hDwires u v (12 + (j + 1)) (Or.inl (by omega))
        rwa [hrm] at this
      rw [hw] at htrue
      exact hC.2.2 (j + 1) (C.gates[j + 1]'hidx) (List.getElem?_eq_getElem hidx) hopC u v htrue

lemma minimal_strict_props (C : Circuit) (hC : StrictC C)
    (hmin : ∀ D : Circuit, StrictC D → C.size ≤ D.size) :
    1 ≤ C.gates.length ∧
    C.output = 12 + C.gates.length - 1 ∧
    (∀ k < C.gates.length, (C.gates.getD k ⟨.or, []⟩).inputs.length = 2 ∧
      ∀ i ∈ (C.gates.getD k ⟨.or, []⟩).inputs, i < 12 + k) ∧
    (∀ w < 12, ∃ k < C.gates.length, w ∈ (C.gates.getD k ⟨.or, []⟩).inputs) ∧
    (∀ k, k + 1 < C.gates.length → ∃ j, k < j ∧ j < C.gates.length ∧
      12 + k ∈ (C.gates.getD j ⟨.or, []⟩).inputs) := by
  have hs_pos : 1 ≤ C.gates.length := by
    by_contra h0
    have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hrep : ∀ u v : Fin 6, (oneEach u v).getD C.output false = A6 u v := by
      intro u v
      have h := hC.2.1 u v
      change (C.gates.foldl evalStep (oneEach u v)).getD C.output false = A6 u v at h
      rw [hnil] at h
      exact h
    by_cases ho : C.output < 6
    · rcases A6_not_all_row ⟨C.output, ho⟩ with ⟨v, hv⟩
      have h1 := hrep ⟨C.output, ho⟩ v
      rw [oneEach_getD, hv, decide_eq_false_iff_not] at h1
      exact h1 (Or.inl rfl)
    · by_cases ho2 : C.output < 12
      · rcases A6_not_all_col ⟨C.output - 6, by omega⟩ with ⟨u, hu⟩
        have h1 := hrep u ⟨C.output - 6, by omega⟩
        rw [oneEach_getD, hu, decide_eq_false_iff_not] at h1
        exact h1 (Or.inr (by show C.output = 6 + (C.output - 6); omega))
      · rcases A6_has_edge with ⟨u, v, huv⟩
        have h1 := hrep u v
        rw [oneEach_getD, huv, decide_eq_true_eq] at h1
        omega
  have hout : C.output = 12 + C.gates.length - 1 := by
    by_contra hne
    have hlt : C.gates.length - 1 < C.gates.length := by omega
    have hne' : 12 + (C.gates.length - 1) ≠ C.output := by omega
    rcases delete_gate_strict C hC (C.gates.length - 1) hlt (12 + C.gates.length) (Or.inr rfl)
      (Or.inl ⟨hne', fun j hj1 hj2 => by omega⟩) with ⟨D, hD, hDsz⟩
    have := hmin D hD
    simp only [Circuit.size] at this hDsz
    omega
  have hdead_all : ∀ k, k + 1 < C.gates.length → ∃ j, k < j ∧ j < C.gates.length ∧
      12 + k ∈ (C.gates.getD j ⟨.or, []⟩).inputs := by
    intro k hk
    by_contra hno
    push Not at hno
    rcases delete_gate_strict C hC k (by omega) (12 + C.gates.length) (Or.inr rfl)
      (Or.inl ⟨by omega, hno⟩) with ⟨D, hD, hDsz⟩
    have := hmin D hD
    simp only [Circuit.size] at this hDsz
    omega
  have hclean : ∀ k < C.gates.length, (C.gates.getD k ⟨.or, []⟩).inputs.length = 2 ∧
      ∀ i ∈ (C.gates.getD k ⟨.or, []⟩).inputs, i < 12 + k := by
    intro k hk
    have hget : C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    have hgmem : C.gates.getD k ⟨.or, []⟩ ∈ C.gates := List.mem_of_getElem? hget
    have hgm := hC.1 _ hgmem
    have hgop : (C.gates.getD k ⟨.or, []⟩).op = .and ∨ (C.gates.getD k ⟨.or, []⟩).op = .or := by
      simpa using hgm.1
    have hglen : (C.gates.getD k ⟨.or, []⟩).inputs.length ≤ 2 := hgm.2
    have hnot_sub : ¬ (12 + C.gates.length < 12 + k) := by omega
    have hneq0 : (C.gates.getD k ⟨.or, []⟩).inputs.length ≠ 0 := by
      intro h0
      have hnil : (C.gates.getD k ⟨.or, []⟩).inputs = [] := List.eq_nil_of_length_eq_zero h0
      rcases hgop with hand | hor
      · have htrue : (C.wires (oneEach (0 : Fin 6) (0 : Fin 6))).getD (12 + k) false = true := by
          rw [wires_getD_gate C (oneEach (0 : Fin 6) (0 : Fin 6)) (oneEach_length 0 0) k hk]
          dsimp only; rw [hnil, hand]; rfl
        have := hC.2.2 k _ hget hand 0 0 htrue
        rw [A6_00_false] at this
        cases this
      · have hfls : ∀ u v : Fin 6, (C.wires (oneEach u v)).getD (12 + k) false =
            if 12 + C.gates.length < 12 + k then (C.wires (oneEach u v)).getD (12 + C.gates.length) false else false := by
          intro u v
          rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk, if_neg hnot_sub]
          dsimp only; rw [hnil, hor]; rfl
        rcases delete_gate_strict C hC k hk (12 + C.gates.length) (Or.inr rfl) (Or.inr hfls) with ⟨D, hD, hDsz⟩
        have := hmin D hD; simp only [Circuit.size] at this hDsz; omega
    have hneq1 : (C.gates.getD k ⟨.or, []⟩).inputs.length ≠ 1 := by
      intro h1
      rcases List.length_eq_one_iff.1 h1 with ⟨a, ha⟩
      by_cases halt : a < 12 + k
      · have heq : ∀ u v : Fin 6, (C.wires (oneEach u v)).getD (12 + k) false =
            if a < 12 + k then (C.wires (oneEach u v)).getD a false else false := by
          intro u v
          rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk, if_pos halt]
          dsimp only; rw [ha]
          rcases hgop with hand | hor
          · rw [hand]; simp [halt, GateOp.eval]
          · rw [hor]; simp [halt, GateOp.eval]
        rcases delete_gate_strict C hC k hk a (Or.inl halt) (Or.inr heq) with ⟨D, hD, hDsz⟩
        have := hmin D hD; simp only [Circuit.size] at this hDsz; omega
      · have hfls : ∀ u v : Fin 6, (C.wires (oneEach u v)).getD (12 + k) false =
            if 12 + C.gates.length < 12 + k then (C.wires (oneEach u v)).getD (12 + C.gates.length) false else false := by
          intro u v
          rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk, if_neg hnot_sub]
          dsimp only; rw [ha]
          rcases hgop with hand | hor
          · rw [hand]; simp [halt, GateOp.eval]
          · rw [hor]; simp [halt, GateOp.eval]
        rcases delete_gate_strict C hC k hk (12 + C.gates.length) (Or.inr rfl) (Or.inr hfls) with ⟨D, hD, hDsz⟩
        have := hmin D hD; simp only [Circuit.size] at this hDsz; omega
    have hlen2 : (C.gates.getD k ⟨.or, []⟩).inputs.length = 2 := by omega
    refine ⟨hlen2, ?_⟩
    rcases List.length_eq_two.1 hlen2 with ⟨a, b, hab⟩
    intro i hi
    rw [hab] at hi
    by_contra hge
    have ha_or_b : ¬ (a < 12 + k) ∨ ¬ (b < 12 + k) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> [left; right] <;> exact hge
    rcases hgop with hand | hor
    · have hfls : ∀ u v : Fin 6, (C.wires (oneEach u v)).getD (12 + k) false =
          if 12 + C.gates.length < 12 + k then (C.wires (oneEach u v)).getD (12 + C.gates.length) false else false := by
        intro u v
        rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk, if_neg hnot_sub]
        dsimp only; rw [hab, hand]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true]
        rcases ha_or_b with ha | hb
        · simp [ha]
        · simp [hb]
      rcases delete_gate_strict C hC k hk (12 + C.gates.length) (Or.inr rfl) (Or.inr hfls) with ⟨D, hD, hDsz⟩
      have := hmin D hD; simp only [Circuit.size] at this hDsz; omega
    · by_cases ha : a < 12 + k
      · have hb : ¬ (b < 12 + k) := by rcases ha_or_b with h | h; exact absurd ha h; exact h
        have heq : ∀ u v : Fin 6, (C.wires (oneEach u v)).getD (12 + k) false =
            if a < 12 + k then (C.wires (oneEach u v)).getD a false else false := by
          intro u v
          rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk, if_pos ha]
          dsimp only; rw [hab, hor]; simp [ha, hb, GateOp.eval]
        rcases delete_gate_strict C hC k hk a (Or.inl ha) (Or.inr heq) with ⟨D, hD, hDsz⟩
        have := hmin D hD; simp only [Circuit.size] at this hDsz; omega
      · by_cases hb : b < 12 + k
        · have heq : ∀ u v : Fin 6, (C.wires (oneEach u v)).getD (12 + k) false =
              if b < 12 + k then (C.wires (oneEach u v)).getD b false else false := by
            intro u v
            rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk, if_pos hb]
            dsimp only; rw [hab, hor]; simp [ha, hb, GateOp.eval]
          rcases delete_gate_strict C hC k hk b (Or.inl hb) (Or.inr heq) with ⟨D, hD, hDsz⟩
          have := hmin D hD; simp only [Circuit.size] at this hDsz; omega
        · have hfls : ∀ u v : Fin 6, (C.wires (oneEach u v)).getD (12 + k) false =
              if 12 + C.gates.length < 12 + k then (C.wires (oneEach u v)).getD (12 + C.gates.length) false else false := by
            intro u v
            rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk, if_neg hnot_sub]
            dsimp only; rw [hab, hor]; simp [ha, hb, GateOp.eval]
          rcases delete_gate_strict C hC k hk (12 + C.gates.length) (Or.inr rfl) (Or.inr hfls) with ⟨D, hD, hDsz⟩
          have := hmin D hD; simp only [Circuit.size] at this hDsz; omega
  have hall_in : ∀ w < 12, ∃ k < C.gates.length, w ∈ (C.gates.getD k ⟨.or, []⟩).inputs := by
    intro w hw
    by_contra hno
    push Not at hno
    have hno_g : ∀ g ∈ C.gates, w ∉ g.inputs := by
      intro g hg
      rcases List.getElem_of_mem hg with ⟨k, hk, rfl⟩
      have := hno k hk
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this
    have hmono_g : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := fun g hg => by simpa using (hC.1 g hg).1
    have hw_ne_out : C.output ≠ w := by omega
    by_cases hw6 : w < 6
    · rcases A6_row_not_le_all ⟨w, hw6⟩ with ⟨b, hba, v, hav, hbv⟩
      have h1 : (C.wires (oneEach ⟨w, hw6⟩ v)).getD C.output false = true := by
        have := hC.2.1 ⟨w, hw6⟩ v; rwa [hav] at this
      have h2 : (C.wires (oneRight6 v)).getD C.output false = true := by
        have hag := foldl_evalStep_agree_without C.gates w hno_g (oneEach ⟨w, hw6⟩ v) (oneRight6 v)
          (by rw [oneEach_length, oneRight6_length])
          (fun i hi => by rw [oneEach_getD, oneRight6_getD]; simp [hi])
          C.output hw_ne_out
        rw [← wires_eq_foldl, ← wires_eq_foldl] at hag
        rwa [← hag]
      have h3 : (C.wires (oneEach b v)).getD C.output false = true := by
        have hmo := foldl_evalStep_mono C.gates hmono_g (oneRight6 v) (oneEach b v)
          (by rw [oneRight6_length, oneEach_length])
          (fun i hi => by
            rw [oneRight6_getD, decide_eq_true_eq] at hi
            rw [oneEach_getD, decide_eq_true_eq]; exact Or.inr hi)
          C.output h2
        simpa [wires_eq_foldl] using hmo
      have h4 := hC.2.1 b v
      rw [hbv] at h4
      change (C.wires (oneEach b v)).getD C.output false = false at h4
      rw [h3] at h4; cases h4
    · have hw_sub : w - 6 < 6 := by omega
      rcases A6_col_not_le_all ⟨w - 6, hw_sub⟩ with ⟨w2, hw2ne, a, hav, haw⟩
      have h1 : (C.wires (oneEach a ⟨w - 6, hw_sub⟩)).getD C.output false = true := by
        have := hC.2.1 a ⟨w - 6, hw_sub⟩; rwa [hav] at this
      have h2 : (C.wires (oneLeft6 a)).getD C.output false = true := by
        have hag := foldl_evalStep_agree_without C.gates w hno_g (oneEach a ⟨w - 6, hw_sub⟩) (oneLeft6 a)
          (by rw [oneEach_length, oneLeft6_length])
          (fun i hi => by
            rw [oneEach_getD, oneLeft6_getD]
            have h6 : 6 + (w - 6) = w := by omega
            simp [h6, hi])
          C.output hw_ne_out
        rw [← wires_eq_foldl, ← wires_eq_foldl] at hag
        rwa [← hag]
      have h3 : (C.wires (oneEach a w2)).getD C.output false = true := by
        have hmo := foldl_evalStep_mono C.gates hmono_g (oneLeft6 a) (oneEach a w2)
          (by rw [oneLeft6_length, oneEach_length])
          (fun i hi => by
            rw [oneLeft6_getD, decide_eq_true_eq] at hi
            rw [oneEach_getD, decide_eq_true_eq]; exact Or.inl hi)
          C.output h2
        simpa [wires_eq_foldl] using hmo
      have h4 := hC.2.1 a w2
      rw [haw] at h4
      change (C.wires (oneEach a w2)).getD C.output false = false at h4
      rw [h3] at h4; cases h4
  exact ⟨hs_pos, hout, hclean, hall_in, hdead_all⟩

def supLAux (gs : List Gate) : ℕ → ℕ → Finset (Fin 6)
  | 0, _ => ∅
  | fuel + 1, w =>
    if h6 : w < 6 then {⟨w, h6⟩}
    else if w < 12 then ∅
    else
      let g := gs.getD (w - 12) ⟨.or, []⟩
      match g.op with
      | .or =>
        let a := g.inputs.getD 0 0
        let b := g.inputs.getD 1 0
        (if a < w then supLAux gs fuel a else ∅) ∪ (if b < w then supLAux gs fuel b else ∅)
      | _ => ∅

def supRAux (gs : List Gate) : ℕ → ℕ → Finset (Fin 6)
  | 0, _ => ∅
  | fuel + 1, w =>
    if w < 6 then ∅
    else if h12 : w < 12 then {⟨w - 6, by omega⟩}
    else
      let g := gs.getD (w - 12) ⟨.or, []⟩
      match g.op with
      | .or =>
        let a := g.inputs.getD 0 0
        let b := g.inputs.getD 1 0
        (if a < w then supRAux gs fuel a else ∅) ∪ (if b < w then supRAux gs fuel b else ∅)
      | _ => ∅

lemma supLAux_indep (gs : List Gate) : ∀ w f1 f2, w < f1 → w < f2 → supLAux gs f1 w = supLAux gs f2 w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro f1 f2 hf1 hf2
    cases f1 with
    | zero => omega
    | succ f1' =>
      cases f2 with
      | zero => omega
      | succ f2' =>
        simp only [supLAux]
        by_cases h6 : w < 6
        · simp [h6]
        · by_cases h12 : w < 12
          · simp [h6, h12]
          · simp only [h6, h12, ↓reduceDIte, ↓reduceIte]
            cases (gs.getD (w - 12) ⟨.or, []⟩).op with
            | or =>
              dsimp only
              by_cases ha : (gs.getD (w - 12) ⟨.or, []⟩).inputs.getD 0 0 < w <;>
                by_cases hb : (gs.getD (w - 12) ⟨.or, []⟩).inputs.getD 1 0 < w <;>
                simp only [ha, hb, ↓reduceIte]
              · rw [ih _ ha f1' f2' (by omega) (by omega), ih _ hb f1' f2' (by omega) (by omega)]
              · rw [ih _ ha f1' f2' (by omega) (by omega)]
              · rw [ih _ hb f1' f2' (by omega) (by omega)]
            | _ => rfl

lemma supRAux_indep (gs : List Gate) : ∀ w f1 f2, w < f1 → w < f2 → supRAux gs f1 w = supRAux gs f2 w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro f1 f2 hf1 hf2
    cases f1 with
    | zero => omega
    | succ f1' =>
      cases f2 with
      | zero => omega
      | succ f2' =>
        simp only [supRAux]
        by_cases h6 : w < 6
        · simp [h6]
        · by_cases h12 : w < 12
          · simp [h6, h12]
          · simp only [h6, h12, ↓reduceDIte, ↓reduceIte]
            cases (gs.getD (w - 12) ⟨.or, []⟩).op with
            | or =>
              dsimp only
              by_cases ha : (gs.getD (w - 12) ⟨.or, []⟩).inputs.getD 0 0 < w <;>
                by_cases hb : (gs.getD (w - 12) ⟨.or, []⟩).inputs.getD 1 0 < w <;>
                simp only [ha, hb, ↓reduceIte]
              · rw [ih _ ha f1' f2' (by omega) (by omega), ih _ hb f1' f2' (by omega) (by omega)]
              · rw [ih _ ha f1' f2' (by omega) (by omega)]
              · rw [ih _ hb f1' f2' (by omega) (by omega)]
            | _ => rfl

def supL (gs : List Gate) (w : ℕ) : Finset (Fin 6) := supLAux gs (w + 1) w
def supR (gs : List Gate) (w : ℕ) : Finset (Fin 6) := supRAux gs (w + 1) w

lemma supL_lt6 (gs : List Gate) (w : ℕ) (hw : w < 6) : supL gs w = {⟨w, hw⟩} := by
  simp [supL, supLAux, hw]

lemma supL_6_12 (gs : List Gate) (w : ℕ) (h1 : 6 ≤ w) (h2 : w < 12) : supL gs w = ∅ := by
  have hnot : ¬ (w < 6) := by omega
  simp [supL, supLAux, hnot, h2]

lemma supR_lt6 (gs : List Gate) (w : ℕ) (hw : w < 6) : supR gs w = ∅ := by
  simp [supR, supRAux, hw]

lemma supR_6_12 (gs : List Gate) (w : ℕ) (h1 : 6 ≤ w) (h2 : w < 12) : supR gs w = {⟨w - 6, by omega⟩} := by
  have hnot : ¬ (w < 6) := by omega
  simp [supR, supRAux, hnot, h2]

lemma supL_gate_or (gs : List Gate) (k a b : ℕ)
    (hop : (gs.getD k ⟨.or, []⟩).op = .or)
    (hin : (gs.getD k ⟨.or, []⟩).inputs = [a, b])
    (ha : a < 12 + k) (hb : b < 12 + k) :
    supL gs (12 + k) = supL gs a ∪ supL gs b := by
  conv_lhs =>
    simp only [supL, supLAux, show ¬ (12 + k < 6) by omega, show ¬ (12 + k < 12) by omega,
      ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hop, hin, List.getD_cons_zero, List.getD_cons_succ, ha, hb]
  rw [supLAux_indep gs a (12 + k) (a + 1) ha (by omega),
      supLAux_indep gs b (12 + k) (b + 1) hb (by omega)]
  rfl

lemma supR_gate_or (gs : List Gate) (k a b : ℕ)
    (hop : (gs.getD k ⟨.or, []⟩).op = .or)
    (hin : (gs.getD k ⟨.or, []⟩).inputs = [a, b])
    (ha : a < 12 + k) (hb : b < 12 + k) :
    supR gs (12 + k) = supR gs a ∪ supR gs b := by
  conv_lhs =>
    simp only [supR, supRAux, show ¬ (12 + k < 6) by omega, show ¬ (12 + k < 12) by omega,
      ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hop, hin, List.getD_cons_zero, List.getD_cons_succ, ha, hb]
  rw [supRAux_indep gs a (12 + k) (a + 1) ha (by omega),
      supRAux_indep gs b (12 + k) (b + 1) hb (by omega)]
  rfl

lemma supL_gate_and (gs : List Gate) (k : ℕ) (hop : (gs.getD k ⟨.or, []⟩).op = .and) :
    supL gs (12 + k) = ∅ := by
  have h1 : ¬ (12 + k < 6) := by omega
  have h2 : ¬ (12 + k < 12) := by omega
  simp only [supL, supLAux, h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hop]

lemma supR_gate_and (gs : List Gate) (k : ℕ) (hop : (gs.getD k ⟨.or, []⟩).op = .and) :
    supR gs (12 + k) = ∅ := by
  have h1 : ¬ (12 + k < 6) := by omega
  have h2 : ¬ (12 + k < 12) := by omega
  simp only [supR, supRAux, h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hop]

lemma sup_sound (C : Circuit) (hclean : ∀ k < C.gates.length, (C.gates.getD k ⟨.or, []⟩).inputs.length = 2 ∧
    ∀ i ∈ (C.gates.getD k ⟨.or, []⟩).inputs, i < 12 + k)
    (hmono : Monotone2 C) (u v : Fin 6) :
    ∀ w < 12 + C.gates.length,
      (u ∈ supL C.gates w ∨ v ∈ supR C.gates w) →
      (C.wires (oneEach u v)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hmem
    by_cases h6 : w < 6
    · rw [supL_lt6 C.gates w h6, supR_lt6 C.gates w h6] at hmem
      simp only [Finset.mem_singleton, Finset.notMem_empty, or_false] at hmem
      rw [wires_getD_input C u v w (by omega), oneEach_getD, decide_eq_true_eq]
      exact Or.inl (congrArg Fin.val hmem).symm
    · by_cases h12 : w < 12
      · rw [supL_6_12 C.gates w (by omega) h12, supR_6_12 C.gates w (by omega) h12] at hmem
        simp only [Finset.notMem_empty, Finset.mem_singleton, false_or] at hmem
        have hv_eq : v.val = w - 6 := congrArg Fin.val hmem
        rw [wires_getD_input C u v w h12, oneEach_getD, decide_eq_true_eq]
        exact Or.inr (by omega)
      · obtain ⟨k, rfl⟩ : ∃ k, w = 12 + k := ⟨w - 12, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hclean k hk with ⟨hlen2, hrb⟩
        rcases List.length_eq_two.1 hlen2 with ⟨a, b, hab⟩
        have ha : a < 12 + k := hrb a (by rw [hab]; simp)
        have hb : b < 12 + k := hrb b (by rw [hab]; simp)
        have hget : C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        have hgop : (C.gates.getD k ⟨.or, []⟩).op = .and ∨ (C.gates.getD k ⟨.or, []⟩).op = .or := by
          simpa using (hmono _ (List.mem_of_getElem? hget)).1
        rcases hgop with hand | hor
        · rw [supL_gate_and C.gates k hand, supR_gate_and C.gates k hand] at hmem
          simp at hmem
        · rw [supL_gate_or C.gates k a b hor hab ha hb, supR_gate_or C.gates k a b hor hab ha hb] at hmem
          rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk]
          dsimp only
          simp only [hab, hor, ha, hb, ↓reduceIte, List.map_cons, List.map_nil, GateOp.eval,
            List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
          simp only [Finset.mem_union] at hmem
          rcases hmem with (hua | hub) | (hva | hvb)
          · exact Or.inl (ih a ha (by omega) (Or.inl hua))
          · exact Or.inr (ih b hb (by omega) (Or.inl hub))
          · exact Or.inl (ih a ha (by omega) (Or.inr hva))
          · exact Or.inr (ih b hb (by omega) (Or.inr hvb))

lemma and_strict_props (C : Circuit) (hC : StrictC C)
    (hclean : ∀ k < C.gates.length, (C.gates.getD k ⟨.or, []⟩).inputs.length = 2 ∧
      ∀ i ∈ (C.gates.getD k ⟨.or, []⟩).inputs, i < 12 + k)
    (k : ℕ) (hk : k < C.gates.length) (hop : (C.gates.getD k ⟨.or, []⟩).op = .and)
    (a b : ℕ) (hab : (C.gates.getD k ⟨.or, []⟩).inputs = [a, b]) :
    (∀ u ∈ supL C.gates a, ∀ v ∈ supR C.gates b, A6 u v = true) ∧
    (∀ u ∈ supL C.gates b, ∀ v ∈ supR C.gates a, A6 u v = true) ∧
    (∀ u ∈ supL C.gates a, u ∉ supL C.gates b) ∧
    (∀ v ∈ supR C.gates a, v ∉ supR C.gates b) := by
  have ha : a < 12 + k := (hclean k hk).2 a (by rw [hab]; simp)
  have hb : b < 12 + k := (hclean k hk).2 b (by rw [hab]; simp)
  have hget : C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have heval_and : ∀ u v : Fin 6,
      (C.wires (oneEach u v)).getD a false = true →
      (C.wires (oneEach u v)).getD b false = true →
      A6 u v = true := by
    intro u v hwa hwb
    apply hC.2.2 k _ hget hop u v
    rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk]
    dsimp only
    rw [hab, hop]
    simp only [ha, hb, ↓reduceIte, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, hwa, hwb, Bool.and_self]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    exact heval_and u v (sup_sound C hclean hC.1 u v a (by omega) (Or.inl hu))
      (sup_sound C hclean hC.1 u v b (by omega) (Or.inr hv))
  · intro u hu v hv
    exact heval_and u v (sup_sound C hclean hC.1 u v a (by omega) (Or.inr hv))
      (sup_sound C hclean hC.1 u v b (by omega) (Or.inl hu))
  · intro u hua hub
    rcases A6_not_all_row u with ⟨v, hv⟩
    have ht := heval_and u v (sup_sound C hclean hC.1 u v a (by omega) (Or.inl hua))
      (sup_sound C hclean hC.1 u v b (by omega) (Or.inl hub))
    rw [hv] at ht; cases ht
  · intro v hva hvb
    rcases A6_not_all_col v with ⟨u, hu⟩
    have ht := heval_and u v (sup_sound C hclean hC.1 u v a (by omega) (Or.inr hva))
      (sup_sound C hclean hC.1 u v b (by omega) (Or.inr hvb))
    rw [hu] at ht; cases ht

lemma val_cover (C : Circuit) (hC : StrictC C)
    (hclean : ∀ k < C.gates.length, (C.gates.getD k ⟨.or, []⟩).inputs.length = 2 ∧
      ∀ i ∈ (C.gates.getD k ⟨.or, []⟩).inputs, i < 12 + k)
    (u v : Fin 6) :
    ∀ w < 12 + C.gates.length,
      (C.wires (oneEach u v)).getD w false = true →
      u ∈ supL C.gates w ∨ v ∈ supR C.gates w ∨
      ∃ (k : Fin C.gates.length) (side : Fin 2),
        (C.gates.getD k.val ⟨.or, []⟩).op = .and ∧
        u ∈ supL C.gates ((C.gates.getD k.val ⟨.or, []⟩).inputs.getD side.val 0) ∧
        v ∈ supR C.gates ((C.gates.getD k.val ⟨.or, []⟩).inputs.getD (1 - side.val) 0) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases h6 : w < 6
    · rw [wires_getD_input C u v w (by omega), oneEach_getD, decide_eq_true_eq] at htrue
      have hwu : w = u.val := by omega
      left
      rw [supL_lt6 C.gates w h6, Finset.mem_singleton]
      exact Fin.ext hwu.symm
    · by_cases h12 : w < 12
      · rw [wires_getD_input C u v w h12, oneEach_getD, decide_eq_true_eq] at htrue
        have hwv : w = 6 + v.val := by omega
        right; left
        rw [supR_6_12 C.gates w (by omega) h12, Finset.mem_singleton]
        apply Fin.ext
        show v.val = w - 6
        omega
      · obtain ⟨k, rfl⟩ : ∃ k, w = 12 + k := ⟨w - 12, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hclean k hk with ⟨hlen2, hrb⟩
        rcases List.length_eq_two.1 hlen2 with ⟨a, b, hab⟩
        have ha : a < 12 + k := hrb a (by rw [hab]; simp)
        have hb : b < 12 + k := hrb b (by rw [hab]; simp)
        have hget : C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        have hgop : (C.gates.getD k ⟨.or, []⟩).op = .and ∨ (C.gates.getD k ⟨.or, []⟩).op = .or := by
          simpa using (hC.1 _ (List.mem_of_getElem? hget)).1
        rw [wires_getD_gate C (oneEach u v) (oneEach_length u v) k hk] at htrue
        dsimp only at htrue
        rcases hgop with hand | hor
        · simp only [hab, hand, ha, hb, ↓reduceIte, List.map_cons, List.map_nil, GateOp.eval,
            List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htrue
          rcases ih a ha (by omega) htrue.1 with hua | hva | hex
          · rcases ih b hb (by omega) htrue.2 with hub | hvb | hex
            · exact absurd hub ((and_strict_props C hC hclean k hk hand a b hab).2.2.1 u hua)
            · right; right
              refine ⟨⟨k, hk⟩, 0, hand, ?_, ?_⟩
              · dsimp only; rw [hab]; exact hua
              · dsimp only; rw [hab]; exact hvb
            · exact Or.inr (Or.inr hex)
          · rcases ih b hb (by omega) htrue.2 with hub | hvb | hex
            · right; right
              refine ⟨⟨k, hk⟩, 1, hand, ?_, ?_⟩
              · dsimp only; rw [hab]; exact hub
              · dsimp only; rw [hab]; exact hva
            · exact absurd hvb ((and_strict_props C hC hclean k hk hand a b hab).2.2.2 v hva)
            · exact Or.inr (Or.inr hex)
          · exact Or.inr (Or.inr hex)
        · simp only [hab, hor, ha, hb, ↓reduceIte, List.map_cons, List.map_nil, GateOp.eval,
            List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at htrue
          rw [supL_gate_or C.gates k a b hor hab ha hb, supR_gate_or C.gates k a b hor hab ha hb]
          rcases htrue with hta | htb
          · rcases ih a ha (by omega) hta with hua | hva | hex
            · exact Or.inl (Finset.mem_union_left _ hua)
            · exact Or.inr (Or.inl (Finset.mem_union_left _ hva))
            · exact Or.inr (Or.inr hex)
          · rcases ih b hb (by omega) htb with hub | hvb | hex
            · exact Or.inl (Finset.mem_union_right _ hub)
            · exact Or.inr (Or.inl (Finset.mem_union_right _ hvb))
            · exact Or.inr (Or.inr hex)

lemma no_strict_le_13 : ¬ ∃ C : Circuit, StrictC C ∧ C.size ≤ 13 := by
  classical
  rintro ⟨C0, hC0, hC0le⟩
  have hex : ∃ s, ∃ C : Circuit, StrictC C ∧ C.size = s := ⟨C0.size, C0, hC0, rfl⟩
  let s := Nat.find hex
  have hs_le : s ≤ 13 := le_trans (Nat.find_min' hex ⟨C0, hC0, rfl⟩) hC0le
  rcases Nat.find_spec hex with ⟨C, hC, hCs⟩
  have hmin : ∀ D : Circuit, StrictC D → C.size ≤ D.size := by
    intro D hD
    rw [hCs]
    exact Nat.find_min' hex ⟨D, hD, rfl⟩
  have hlen_eq : C.gates.length = s := hCs
  rcases minimal_strict_props C hC hmin with ⟨hs_pos, hout, hclean, hall_in, hdead_all⟩
  rw [hlen_eq] at hs_pos hout
  let slotWire (p : Fin s × Fin 2) : ℕ :=
    (C.gates.getD p.1.val ⟨.or, []⟩).inputs.getD p.2.val 0
  let otherSlot (p : Fin s × Fin 2) : Fin s × Fin 2 :=
    (p.1, ⟨1 - p.2.val, by omega⟩)
  have hslot_lt : ∀ p : Fin s × Fin 2, slotWire p < 12 + p.1.val := by
    rintro ⟨p1, p2⟩
    have hp1 : p1.val < C.gates.length := by omega
    rcases hclean p1.val hp1 with ⟨hl2, hrb⟩
    rcases List.length_eq_two.1 hl2 with ⟨a, b, hab⟩
    have ha : a < 12 + p1.val := hrb a (by rw [hab]; simp)
    have hb : b < 12 + p1.val := hrb b (by rw [hab]; simp)
    fin_cases p2
    · dsimp only [slotWire]; rw [hab]; exact ha
    · dsimp only [slotWire]; rw [hab]; exact hb
  have hslot_lt_top : ∀ p : Fin s × Fin 2, slotWire p < 12 + s - 1 := by
    intro p; have := hslot_lt p; omega
  let Wtop := Finset.range (12 + s - 1)
  let deg (w : ℕ) : ℕ := (Finset.univ.filter (fun p : Fin s × Fin 2 => slotWire p = w)).card
  have hdeg_pos : ∀ w ∈ Wtop, 1 ≤ deg w := by
    intro w hw
    rw [Finset.mem_range] at hw
    suffices ∃ p : Fin s × Fin 2, slotWire p = w by
      rcases this with ⟨p, hp⟩
      exact Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ p, hp⟩⟩
    by_cases hw12 : w < 12
    · rcases hall_in w hw12 with ⟨k, hk, hmem⟩
      rcases List.length_eq_two.1 (hclean k hk).1 with ⟨a, b, hab⟩
      rw [hab] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact ⟨(⟨k, by omega⟩, 0), by dsimp only [slotWire]; rw [hab]; rfl⟩
      · exact ⟨(⟨k, by omega⟩, 1), by dsimp only [slotWire]; rw [hab]; rfl⟩
    · let k := w - 12
      have hk1 : k + 1 < C.gates.length := by omega
      rcases hdead_all k hk1 with ⟨j, _, hj, hmem⟩
      have hw_eq : 12 + k = w := by omega
      rw [hw_eq] at hmem
      rcases List.length_eq_two.1 (hclean j hj).1 with ⟨a, b, hab⟩
      rw [hab] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact ⟨(⟨j, by omega⟩, 0), by dsimp only [slotWire]; rw [hab]; rfl⟩
      · exact ⟨(⟨j, by omega⟩, 1), by dsimp only [slotWire]; rw [hab]; rfl⟩
  have hsum_deg : ∑ w ∈ Wtop, deg w = 2 * s := by
    have hfib := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin s × Fin 2)))
      (t := Wtop) (f := slotWire) (fun p _ => Finset.mem_range.2 (hslot_lt_top p))
    have hcard : (Finset.univ : Finset (Fin s × Fin 2)).card = 2 * s := by simp [Nat.mul_comm]
    simpa [deg, hcard] using hfib.symm
  have hsum_surplus : ∑ w ∈ Wtop, (deg w - 1) = s - 11 := by
    have hadd : ∑ w ∈ Wtop, ((deg w - 1) + 1) = ∑ w ∈ Wtop, deg w := by
      apply Finset.sum_congr rfl
      intro w hw
      have := hdeg_pos w hw; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at hadd
    omega
  have hout_supL : supL C.gates C.output = ∅ := by
    ext u; simp only [Finset.notMem_empty, iff_false]
    intro hu
    rcases A6_not_all_row u with ⟨v, hv⟩
    have ht := sup_sound C hclean hC.1 u v C.output (by omega) (Or.inl hu)
    have hr := hC.2.1 u v
    rw [hv] at hr
    change (C.wires (oneEach u v)).getD C.output false = false at hr
    rw [ht] at hr; cases hr
  have hout_supR : supR C.gates C.output = ∅ := by
    ext v; simp only [Finset.notMem_empty, iff_false]
    intro hv
    rcases A6_not_all_col v with ⟨u, hu⟩
    have ht := sup_sound C hclean hC.1 u v C.output (by omega) (Or.inr hv)
    have hr := hC.2.1 u v
    rw [hu] at hr
    change (C.wires (oneEach u v)).getD C.output false = false at hr
    rw [ht] at hr; cases hr
  have hedge_cov : ∀ e : Fin 6 × Fin 6, A6 e.1 e.2 = true →
      ∃ p : Fin s × Fin 2,
        (C.gates.getD p.1.val ⟨.or, []⟩).op = .and ∧
        e.1 ∈ supL C.gates (slotWire p) ∧
        e.2 ∈ supR C.gates (slotWire (otherSlot p)) := by
    intro e he
    have ht : (C.wires (oneEach e.1 e.2)).getD C.output false = true := by
      have := hC.2.1 e.1 e.2; rwa [he] at this
    rcases val_cover C hC hclean e.1 e.2 C.output (by omega) ht with hL | hR | ⟨k, side, hand, hu, hv⟩
    · rw [hout_supL] at hL; simp at hL
    · rw [hout_supR] at hR; simp at hR
    · exact ⟨(⟨k.val, by omega⟩, side), hand, hu, hv⟩
  let chosen (e : Fin 6 × Fin 6) : Fin s × Fin 2 :=
    if h : A6 e.1 e.2 = true then Classical.choose (hedge_cov e h) else (⟨0, by omega⟩, 0)
  have hchosen_spec : ∀ e : Fin 6 × Fin 6, A6 e.1 e.2 = true →
      (C.gates.getD (chosen e).1.val ⟨.or, []⟩).op = .and ∧
      e.1 ∈ supL C.gates (slotWire (chosen e)) ∧
      e.2 ∈ supR C.gates (slotWire (otherSlot (chosen e))) := by
    intro e he
    simp only [chosen, he, ↓reduceDIte]
    exact Classical.choose_spec (hedge_cov e he)
  have hrect_A6 : ∀ p : Fin s × Fin 2, (C.gates.getD p.1.val ⟨.or, []⟩).op = .and →
      ∀ u ∈ supL C.gates (slotWire p), ∀ v ∈ supR C.gates (slotWire (otherSlot p)), A6 u v = true := by
    rintro ⟨p1, p2⟩ hand u hu v hv
    have hp1 : p1.val < C.gates.length := by omega
    rcases List.length_eq_two.1 (hclean p1.val hp1).1 with ⟨a, b, hab⟩
    have hsp := and_strict_props C hC hclean p1.val hp1 hand a b hab
    fin_cases p2
    · simp only [slotWire, otherSlot, hab, Fin.val_zero, Nat.sub_zero, List.getD_cons_zero,
        List.getD_cons_succ] at hu hv
      exact hsp.1 u hu v hv
    · simp only [slotWire, otherSlot, hab, Fin.val_one, Nat.sub_self, List.getD_cons_zero,
        List.getD_cons_succ] at hu hv
      exact hsp.2.1 u hu v hv
  let Ep (p : Fin s × Fin 2) : Finset (Fin 6 × Fin 6) := edges6.filter (fun e => chosen e = p)
  let Lp (p : Fin s × Fin 2) : Finset (Fin 6) := (Ep p).image Prod.fst
  let Rp (p : Fin s × Fin 2) : Finset (Fin 6) := (Ep p).image Prod.snd
  have hEp_bound : ∀ p : Fin s × Fin 2, (Ep p).Nonempty →
      (Ep p).card + 1 ≤ (Lp p).card + (Rp p).card := by
    intro p hne
    rcases hne with ⟨e0, he0⟩
    have he0_mem := Finset.mem_filter.1 he0
    have he0_A6 : A6 e0.1 e0.2 = true := (Finset.mem_filter.1 he0_mem.1).2
    have hand : (C.gates.getD p.1.val ⟨.or, []⟩).op = .and := by
      rw [← he0_mem.2]; exact (hchosen_spec e0 he0_A6).1
    have hLp_sub : ∀ u ∈ Lp p, u ∈ supL C.gates (slotWire p) := by
      intro u hu
      rcases Finset.mem_image.1 hu with ⟨e, he, rfl⟩
      have hm := Finset.mem_filter.1 he
      rw [← hm.2]; exact (hchosen_spec e (Finset.mem_filter.1 hm.1).2).2.1
    have hRp_sub : ∀ v ∈ Rp p, v ∈ supR C.gates (slotWire (otherSlot p)) := by
      intro v hv
      rcases Finset.mem_image.1 hv with ⟨e, he, rfl⟩
      have hm := Finset.mem_filter.1 he
      rw [← hm.2]; exact (hchosen_spec e (Finset.mem_filter.1 hm.1).2).2.2
    have hrect : ∀ u ∈ Lp p, ∀ v ∈ Rp p, A6 u v = true :=
      fun u hu v hv => hrect_A6 p hand u (hLp_sub u hu) v (hRp_sub v hv)
    have hle1 : (Lp p).card ≤ 1 ∨ (Rp p).card ≤ 1 := by
      by_contra hboth
      push Not at hboth
      rcases Finset.one_lt_card.1 hboth.1 with ⟨u1, hu1, u2, hu2, hune⟩
      rcases Finset.one_lt_card.1 hboth.2 with ⟨v1, hv1, v2, hv2, hvne⟩
      exact A6_k22_free u1 u2 hune v1 v2 hvne ⟨hrect u1 hu1 v1 hv1, hrect u1 hu1 v2 hv2,
        hrect u2 hu2 v1 hv1, hrect u2 hu2 v2 hv2⟩
    have hsub_prod : Ep p ⊆ (Lp p) ×ˢ (Rp p) := by
      intro e he
      exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem Prod.fst he, Finset.mem_image_of_mem Prod.snd he⟩
    have hcard_le : (Ep p).card ≤ (Lp p).card * (Rp p).card := by
      calc (Ep p).card ≤ ((Lp p) ×ˢ (Rp p)).card := Finset.card_le_card hsub_prod
      _ = (Lp p).card * (Rp p).card := Finset.card_product _ _
    have hLp_pos : 1 ≤ (Lp p).card := Finset.card_pos.2 ⟨e0.1, Finset.mem_image_of_mem Prod.fst he0⟩
    have hRp_pos : 1 ≤ (Rp p).card := Finset.card_pos.2 ⟨e0.2, Finset.mem_image_of_mem Prod.snd he0⟩
    rcases hle1 with hL1 | hR1
    · have : (Lp p).card = 1 := by omega
      rw [this, one_mul] at hcard_le; omega
    · have : (Rp p).card = 1 := by omega
      rw [this, mul_one] at hcard_le; omega
  let activeP : Finset (Fin s × Fin 2) := Finset.univ.filter (fun p => (Ep p).Nonempty)
  have hactive_ge6 : 6 ≤ activeP.card := by
    have hinj : Function.Injective (fun i : Fin 6 => chosen (fool6 i)) := by
      intro i j hij
      dsimp only at hij
      by_contra hne
      have hi := hchosen_spec (fool6 i) (fool6_edge i)
      have hj := hchosen_spec (fool6 j) (fool6_edge j)
      rw [hij] at hi
      exact fool6_sep i j hne ⟨hrect_A6 _ hj.1 _ hi.2.1 _ hj.2.2, hrect_A6 _ hj.1 _ hj.2.1 _ hi.2.2⟩
    have hsub : Finset.univ.image (fun i : Fin 6 => chosen (fool6 i)) ⊆ activeP := by
      intro p hp
      rcases Finset.mem_image.1 hp with ⟨i, _, rfl⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨fool6 i,
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, fool6_edge i⟩, rfl⟩⟩⟩
    calc 6 = (Finset.univ : Finset (Fin 6)).card := by simp
    _ = (Finset.univ.image (fun i : Fin 6 => chosen (fool6 i))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ activeP.card := Finset.card_le_card hsub
  have hsum_Ep : ∑ p : Fin s × Fin 2, (Ep p).card = 12 := by
    have hfib := Finset.card_eq_sum_card_fiberwise (s := edges6)
      (t := (Finset.univ : Finset (Fin s × Fin 2))) (f := chosen) (fun _ _ => Finset.mem_univ _)
    simpa [Ep, edges6_card] using hfib.symm
  have hTL_TR_ge18 : 18 ≤ (∑ p : Fin s × Fin 2, (Lp p).card) + (∑ p : Fin s × Fin 2, (Rp p).card) := by
    have h1 : ∑ p ∈ activeP, ((Ep p).card + 1) ≤ ∑ p ∈ activeP, ((Lp p).card + (Rp p).card) :=
      Finset.sum_le_sum (fun p hp => hEp_bound p (Finset.mem_filter.1 hp).2)
    have h2 : ∑ p ∈ activeP, (Ep p).card = ∑ p : Fin s × Fin 2, (Ep p).card := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro p _ hnot
      have hem : ¬ (Ep p).Nonempty := fun h => hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      exact Finset.not_nonempty_iff_eq_empty.1 hem ▸ rfl
    have h3 : ∑ p ∈ activeP, ((Lp p).card + (Rp p).card) ≤
        ∑ p : Fin s × Fin 2, ((Lp p).card + (Rp p).card) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h13 : ∑ p ∈ activeP, ((Ep p).card + 1) ≤ ∑ p : Fin s × Fin 2, ((Lp p).card + (Rp p).card) :=
      le_trans h1 h3
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, h2, hsum_Ep,
        Finset.sum_add_distrib] at h13
    omega
  have hexits_L : ∀ (u : Fin 6) (w : ℕ), w < 12 + s - 1 → u ∈ supL C.gates w →
      supL C.gates w = {u} ∨
      ∃ q : Fin s × Fin 2,
        supL C.gates (slotWire q) = {u} ∧
        supL C.gates (12 + q.1.val) ≠ {u} ∧
        (C.gates.getD q.1.val ⟨.or, []⟩).op = .or ∧
        2 ≤ (supL C.gates (12 + q.1.val)).card ∧
        supL C.gates (12 + q.1.val) ⊆ supL C.gates w := by
    intro u w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hu
      by_cases hsing : supL C.gates w = {u}
      · exact Or.inl hsing
      · right
        have hcard2 : 2 ≤ (supL C.gates w).card := by
          have h1 : {u} ⊂ supL C.gates w := Finset.ssubset_iff_subset_ne.2
            ⟨Finset.singleton_subset_iff.2 hu, fun h => hsing h.symm⟩
          have := Finset.card_lt_card h1; simp at this; omega
        have hw12 : 12 ≤ w := by
          by_contra hlt
          by_cases h6 : w < 6
          · rw [supL_lt6 C.gates w h6] at hu hsing
            simp only [Finset.mem_singleton] at hu
            subst hu; exact hsing rfl
          · rw [supL_6_12 C.gates w (by omega) (by omega)] at hu
            simp at hu
        obtain ⟨k, rfl⟩ : ∃ k, w = 12 + k := ⟨w - 12, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hclean k hk with ⟨hl2, hrb⟩
        rcases List.length_eq_two.1 hl2 with ⟨a, b, hab⟩
        have ha : a < 12 + k := hrb a (by rw [hab]; simp)
        have hb : b < 12 + k := hrb b (by rw [hab]; simp)
        have hget : C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        have hgop : (C.gates.getD k ⟨.or, []⟩).op = .and ∨ (C.gates.getD k ⟨.or, []⟩).op = .or := by
          simpa using (hC.1 _ (List.mem_of_getElem? hget)).1
        rcases hgop with hand | hor
        · rw [supL_gate_and C.gates k hand] at hu; simp at hu
        · have hun := supL_gate_or C.gates k a b hor hab ha hb
          rw [hun, Finset.mem_union] at hu
          rcases hu with hua | hub
          · rcases ih a ha (by omega) hua with hasing | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
            · exact ⟨(⟨k, by omega⟩, 0), by dsimp only [slotWire]; rw [hab]; exact hasing,
                hsing, hor, hcard2, Finset.Subset.refl _⟩
            · exact ⟨q, hq1, hq2, hq3, hq4, Finset.Subset.trans hq5 (by rw [hun]; exact Finset.subset_union_left)⟩
          · rcases ih b hb (by omega) hub with hbsing | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
            · exact ⟨(⟨k, by omega⟩, 1), by dsimp only [slotWire]; rw [hab]; exact hbsing,
                hsing, hor, hcard2, Finset.Subset.refl _⟩
            · exact ⟨q, hq1, hq2, hq3, hq4, Finset.Subset.trans hq5 (by rw [hun]; exact Finset.subset_union_right)⟩
  have hexits_R : ∀ (v : Fin 6) (w : ℕ), w < 12 + s - 1 → v ∈ supR C.gates w →
      supR C.gates w = {v} ∨
      ∃ q : Fin s × Fin 2,
        supR C.gates (slotWire q) = {v} ∧
        supR C.gates (12 + q.1.val) ≠ {v} ∧
        (C.gates.getD q.1.val ⟨.or, []⟩).op = .or ∧
        2 ≤ (supR C.gates (12 + q.1.val)).card ∧
        supR C.gates (12 + q.1.val) ⊆ supR C.gates w := by
    intro v w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hv
      by_cases hsing : supR C.gates w = {v}
      · exact Or.inl hsing
      · right
        have hcard2 : 2 ≤ (supR C.gates w).card := by
          have h1 : {v} ⊂ supR C.gates w := Finset.ssubset_iff_subset_ne.2
            ⟨Finset.singleton_subset_iff.2 hv, fun h => hsing h.symm⟩
          have := Finset.card_lt_card h1; simp at this; omega
        have hw12 : 12 ≤ w := by
          by_contra hlt
          by_cases h6 : w < 6
          · rw [supR_lt6 C.gates w h6] at hv; simp at hv
          · rw [supR_6_12 C.gates w (by omega) (by omega)] at hv hsing
            simp only [Finset.mem_singleton] at hv
            subst hv; exact hsing rfl
        obtain ⟨k, rfl⟩ : ∃ k, w = 12 + k := ⟨w - 12, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hclean k hk with ⟨hl2, hrb⟩
        rcases List.length_eq_two.1 hl2 with ⟨a, b, hab⟩
        have ha : a < 12 + k := hrb a (by rw [hab]; simp)
        have hb : b < 12 + k := hrb b (by rw [hab]; simp)
        have hget : C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        have hgop : (C.gates.getD k ⟨.or, []⟩).op = .and ∨ (C.gates.getD k ⟨.or, []⟩).op = .or := by
          simpa using (hC.1 _ (List.mem_of_getElem? hget)).1
        rcases hgop with hand | hor
        · rw [supR_gate_and C.gates k hand] at hv; simp at hv
        · have hun := supR_gate_or C.gates k a b hor hab ha hb
          rw [hun, Finset.mem_union] at hv
          rcases hv with hva | hvb
          · rcases ih a ha (by omega) hva with hasing | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
            · exact ⟨(⟨k, by omega⟩, 0), by dsimp only [slotWire]; rw [hab]; exact hasing,
                hsing, hor, hcard2, Finset.Subset.refl _⟩
            · exact ⟨q, hq1, hq2, hq3, hq4, Finset.Subset.trans hq5 (by rw [hun]; exact Finset.subset_union_left)⟩
          · rcases ih b hb (by omega) hvb with hbsing | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
            · exact ⟨(⟨k, by omega⟩, 1), by dsimp only [slotWire]; rw [hab]; exact hbsing,
                hsing, hor, hcard2, Finset.Subset.refl _⟩
            · exact ⟨q, hq1, hq2, hq3, hq4, Finset.Subset.trans hq5 (by rw [hun]; exact Finset.subset_union_right)⟩
  have hTL_le : ∑ p : Fin s × Fin 2, (Lp p).card ≤ 6 + (s - 11) := by
    let Gu (u : Fin 6) : Finset ℕ := Wtop.filter (fun w => supL C.gates w = {u})
    have hper_u : ∀ u : Fin 6,
        (Finset.univ.filter (fun p : Fin s × Fin 2 => u ∈ Lp p)).card ≤
          1 + ∑ w ∈ Gu u, (deg w - 1) := by
      intro u
      let Pu := Finset.univ.filter (fun p : Fin s × Fin 2 => u ∈ Lp p)
      let exitU := Finset.univ.filter (fun q : Fin s × Fin 2 =>
        supL C.gates (slotWire q) = {u} ∧ supL C.gates (12 + q.1.val) ≠ {u})
      let intU := Finset.univ.filter (fun q : Fin s × Fin 2 =>
        supL C.gates (slotWire q) = {u} ∧ supL C.gates (12 + q.1.val) = {u})
      have hex_map : ∀ p ∈ Pu, ∃ q ∈ exitU,
          (q = p ∧ (C.gates.getD p.1.val ⟨.or, []⟩).op = .and) ∨
          ((C.gates.getD q.1.val ⟨.or, []⟩).op = .or ∧ 2 ≤ (supL C.gates (12 + q.1.val)).card ∧
            supL C.gates (12 + q.1.val) ⊆ supL C.gates (slotWire p)) := by
        intro p hp
        have huLp : u ∈ Lp p := (Finset.mem_filter.1 hp).2
        rcases Finset.mem_image.1 huLp with ⟨e, he, rfl⟩
        have hm := Finset.mem_filter.1 he
        have hspec := hchosen_spec e (Finset.mem_filter.1 hm.1).2
        rw [hm.2] at hspec
        rcases hexits_L e.1 (slotWire p) (hslot_lt_top p) hspec.2.1 with hsing | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
        · refine ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hsing, ?_⟩, Or.inl ⟨rfl, hspec.1⟩⟩
          rw [supL_gate_and C.gates p.1.val hspec.1]
          exact Finset.empty_ne_singleton e.1
        · exact ⟨q, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq1, hq2⟩, Or.inr ⟨hq3, hq4, hq5⟩⟩
      let fU (p : Fin s × Fin 2) : Fin s × Fin 2 :=
        if h : p ∈ Pu then Classical.choose (hex_map p h) else p
      have hPu_le_exit : Pu.card ≤ exitU.card := by
        apply Finset.card_le_card_of_injOn fU
        · intro p hp
          have hp' : p ∈ Pu := Finset.mem_coe.1 hp
          dsimp only [fU]
          rw [dif_pos hp']
          exact Finset.mem_coe.2 (Classical.choose_spec (hex_map p hp')).1
        · intro p1 hp1 p2 hp2 hfeq
          have hp1' : p1 ∈ Pu := Finset.mem_coe.1 hp1
          have hp2' : p2 ∈ Pu := Finset.mem_coe.1 hp2
          have hs1 := (Classical.choose_spec (hex_map p1 hp1')).2
          have hs2 := (Classical.choose_spec (hex_map p2 hp2')).2
          dsimp only [fU] at hfeq
          rw [dif_pos hp1', dif_pos hp2'] at hfeq
          set q := Classical.choose (hex_map p1 hp1')
          rw [← hfeq] at hs2
          rcases hs1 with ⟨hq1, hand1⟩ | ⟨hor1, hcard1, hsub1⟩
          · rcases hs2 with ⟨hqp, _⟩ | ⟨hor2, _, _⟩
            · exact hq1.symm.trans hqp
            · rw [hq1, hand1] at hor2; cases hor2
          · rcases hs2 with ⟨hq2, hand2⟩ | ⟨_, _, hsub2⟩
            · rw [hq2, hand2] at hor1; cases hor1
            · rcases Finset.mem_image.1 (Finset.mem_filter.1 hp1').2 with ⟨e1, he1, he1u⟩
              rcases Finset.mem_image.1 (Finset.mem_filter.1 hp2').2 with ⟨e2, he2, he2u⟩
              have hm1 := Finset.mem_filter.1 he1
              have hm2 := Finset.mem_filter.1 he2
              have hsp1 := hchosen_spec e1 (Finset.mem_filter.1 hm1.1).2
              have hsp2 := hchosen_spec e2 (Finset.mem_filter.1 hm2.1).2
              rw [hm1.2] at hsp1
              rw [hm2.2] at hsp2
              rcases Finset.exists_mem_ne (by omega : 1 < (supL C.gates (12 + q.1.val)).card) u with ⟨u', hu', hune⟩
              have hu_in : u ∈ supL C.gates (12 + q.1.val) := by
                have hqk : q.1.val < C.gates.length := by omega
                rcases List.length_eq_two.1 (hclean q.1.val hqk).1 with ⟨a, b, hab⟩
                have ha : a < 12 + q.1.val := (hclean q.1.val hqk).2 a (by rw [hab]; simp)
                have hb : b < 12 + q.1.val := (hclean q.1.val hqk).2 b (by rw [hab]; simp)
                rw [supL_gate_or C.gates q.1.val a b hor1 hab ha hb]
                have hqmem : supL C.gates (slotWire q) = {u} :=
                  (Finset.mem_filter.1 (Classical.choose_spec (hex_map p1 hp1')).1).2.1
                rcases q with ⟨q1, q2⟩
                fin_cases q2
                · dsimp only [slotWire] at hqmem
                  rw [hab] at hqmem
                  change supL C.gates a = {u} at hqmem
                  rw [hqmem]; exact Finset.mem_union_left _ (Finset.mem_singleton_self u)
                · dsimp only [slotWire] at hqmem
                  rw [hab] at hqmem
                  change supL C.gates b = {u} at hqmem
                  rw [hqmem]; exact Finset.mem_union_right _ (Finset.mem_singleton_self u)
              have hv_eq : e1.2 = e2.2 := by
                by_contra hvne
                exact A6_k22_free u u' hune.symm e1.2 e2.2 hvne
                  ⟨hrect_A6 p1 hsp1.1 u (hsub1 hu_in) e1.2 hsp1.2.2,
                   hrect_A6 p2 hsp2.1 u (hsub2 hu_in) e2.2 hsp2.2.2,
                   hrect_A6 p1 hsp1.1 u' (hsub1 hu') e1.2 hsp1.2.2,
                   hrect_A6 p2 hsp2.1 u' (hsub2 hu') e2.2 hsp2.2.2⟩
              have he_eq : e1 = e2 := Prod.ext (he1u.trans he2u.symm) hv_eq
              rw [← hm1.2, ← hm2.2, he_eq]
      have hu_in_Gu : u.val ∈ Gu u :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), supL_lt6 C.gates u.val u.isLt⟩
      have hint_ge : (Gu u).card - 1 ≤ intU.card := by
        have hex_int : ∀ w ∈ (Gu u).erase u.val, ∃ q ∈ intU, 12 + q.1.val = w := by
          intro w hw
          rcases Finset.mem_erase.1 hw with ⟨hne, hwGu⟩
          rcases Finset.mem_filter.1 hwGu with ⟨hwR, hwL⟩
          rw [Finset.mem_range] at hwR
          have hw12 : 12 ≤ w := by
            by_contra hlt
            by_cases h6 : w < 6
            · rw [supL_lt6 C.gates w h6] at hwL
              have : (⟨w, h6⟩ : Fin 6) = u := Finset.singleton_injective hwL
              exact hne (congrArg Fin.val this)
            · rw [supL_6_12 C.gates w (by omega) (by omega)] at hwL
              exact Finset.empty_ne_singleton u hwL
          let k := w - 12
          have hw_eq : w = 12 + k := by omega
          have hk : k < C.gates.length := by omega
          rcases List.length_eq_two.1 (hclean k hk).1 with ⟨a, b, hab⟩
          have ha : a < 12 + k := (hclean k hk).2 a (by rw [hab]; simp)
          have hb : b < 12 + k := (hclean k hk).2 b (by rw [hab]; simp)
          have hget : C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩) := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          have hgop : (C.gates.getD k ⟨.or, []⟩).op = .and ∨ (C.gates.getD k ⟨.or, []⟩).op = .or := by
            simpa using (hC.1 _ (List.mem_of_getElem? hget)).1
          rw [hw_eq] at hwL
          have hwL0 : supL C.gates (12 + k) = {u} := hwL
          rcases hgop with hand | hor
          · rw [supL_gate_and C.gates k hand] at hwL
            exact absurd hwL (Finset.empty_ne_singleton u)
          · rw [supL_gate_or C.gates k a b hor hab ha hb] at hwL
            have huab : u ∈ supL C.gates a ∨ u ∈ supL C.gates b := by
              have : u ∈ supL C.gates a ∪ supL C.gates b := by rw [hwL]; exact Finset.mem_singleton_self u
              exact Finset.mem_union.1 this
            rcases huab with hua | hub
            · have hsa : supL C.gates a = {u} := by
                apply Finset.Subset.antisymm
                · rw [← hwL]; exact Finset.subset_union_left
                · exact Finset.singleton_subset_iff.2 hua
              exact ⟨(⟨k, by omega⟩, 0), Finset.mem_filter.2 ⟨Finset.mem_univ _,
                by dsimp only [slotWire]; rw [hab]; exact hsa, hwL0⟩, hw_eq.symm⟩
            · have hsb : supL C.gates b = {u} := by
                apply Finset.Subset.antisymm
                · rw [← hwL]; exact Finset.subset_union_right
                · exact Finset.singleton_subset_iff.2 hub
              exact ⟨(⟨k, by omega⟩, 1), Finset.mem_filter.2 ⟨Finset.mem_univ _,
                by dsimp only [slotWire]; rw [hab]; exact hsb, hwL0⟩, hw_eq.symm⟩
        let gU (w : ℕ) : Fin s × Fin 2 :=
          if h : w ∈ (Gu u).erase u.val then Classical.choose (hex_int w h) else (⟨0, by omega⟩, 0)
        have hle : ((Gu u).erase u.val).card ≤ intU.card := by
          apply Finset.card_le_card_of_injOn gU
          · intro w hw
            have hw' : w ∈ (Gu u).erase u.val := Finset.mem_coe.1 hw
            dsimp only [gU]; rw [dif_pos hw']
            exact Finset.mem_coe.2 (Classical.choose_spec (hex_int w hw')).1
          · intro w1 hw1 w2 hw2 hgeq
            have hw1' : w1 ∈ (Gu u).erase u.val := Finset.mem_coe.1 hw1
            have hw2' : w2 ∈ (Gu u).erase u.val := Finset.mem_coe.1 hw2
            have h1 := (Classical.choose_spec (hex_int w1 hw1')).2
            have h2 := (Classical.choose_spec (hex_int w2 hw2')).2
            dsimp only [gU] at hgeq; rw [dif_pos hw1', dif_pos hw2'] at hgeq
            rw [← h1, ← h2, hgeq]
        rwa [Finset.card_erase_of_mem hu_in_Gu] at hle
      have htot : intU.card + exitU.card = ∑ w ∈ Gu u, deg w := by
        let allU := Finset.univ.filter (fun q : Fin s × Fin 2 => supL C.gates (slotWire q) = {u})
        have hdisj : Disjoint intU exitU := by
          rw [Finset.disjoint_filter]
          intro q _ h1 h2; exact h2.2 h1.2
        have hun : intU ∪ exitU = allU := by
          ext q; simp only [Finset.mem_union, intU, exitU, allU, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases h : supL C.gates (12 + q.1.val) = {u} <;> simp [h]
        have hcard_all : allU.card = ∑ w ∈ Gu u, deg w := by
          have hfib := Finset.card_eq_sum_card_fiberwise (s := allU) (t := Gu u) (f := slotWire)
            (fun q hq => Finset.mem_filter.2 ⟨Finset.mem_range.2 (hslot_lt_top q), (Finset.mem_filter.1 hq).2⟩)
          rw [hfib]
          apply Finset.sum_congr rfl
          intro w hw
          congr 1; ext q
          simp only [allU, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact (Finset.mem_filter.1 hw).2, h⟩⟩
        rw [← Finset.card_union_of_disjoint hdisj, hun, hcard_all]
      have hsum_split : (Gu u).card + ∑ w ∈ Gu u, (deg w - 1) = ∑ w ∈ Gu u, deg w := by
        have : ∑ w ∈ Gu u, (1 + (deg w - 1)) = ∑ w ∈ Gu u, deg w := by
          apply Finset.sum_congr rfl
          intro w hw
          have := hdeg_pos w (Finset.mem_filter.1 hw).1; omega
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at this
        exact this
      have hGu_pos : 1 ≤ (Gu u).card := Finset.card_pos.2 ⟨u.val, hu_in_Gu⟩
      change Pu.card ≤ 1 + ∑ w ∈ Gu u, (deg w - 1)
      omega
    have hswap : ∑ p : Fin s × Fin 2, (Lp p).card =
        ∑ u : Fin 6, (Finset.univ.filter (fun p : Fin s × Fin 2 => u ∈ Lp p)).card := by
      have h1 : ∀ p : Fin s × Fin 2, (Lp p).card = ∑ u : Fin 6, if u ∈ Lp p then 1 else 0 := fun p => by
        simp
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      simp
    have hdisjG : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 6)) Gu := by
      intro u1 _ u2 _ hne
      change Disjoint (Gu u1) (Gu u2)
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have e1 := (Finset.mem_filter.1 hw1).2
      have e2 := (Finset.mem_filter.1 hw2).2
      exact hne (Finset.singleton_injective (e1.symm.trans e2))
    have hsubG : (Finset.univ : Finset (Fin 6)).biUnion Gu ⊆ Wtop := by
      intro w hw
      rcases Finset.mem_biUnion.1 hw with ⟨u, _, hwu⟩
      exact (Finset.mem_filter.1 hwu).1
    calc ∑ p : Fin s × Fin 2, (Lp p).card
        = ∑ u : Fin 6, (Finset.univ.filter (fun p : Fin s × Fin 2 => u ∈ Lp p)).card := hswap
      _ ≤ ∑ u : Fin 6, (1 + ∑ w ∈ Gu u, (deg w - 1)) := Finset.sum_le_sum (fun u _ => hper_u u)
      _ = 6 + ∑ u : Fin 6, ∑ w ∈ Gu u, (deg w - 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      _ = 6 + ∑ w ∈ (Finset.univ : Finset (Fin 6)).biUnion Gu, (deg w - 1) := by
          rw [Finset.sum_biUnion hdisjG]
      _ ≤ 6 + ∑ w ∈ Wtop, (deg w - 1) := Nat.add_le_add_left (Finset.sum_le_sum_of_subset hsubG) 6
      _ = 6 + (s - 11) := by rw [hsum_surplus]
  have hTR_le : ∑ p : Fin s × Fin 2, (Rp p).card ≤ 6 + (s - 11) := by
    let Gv (v : Fin 6) : Finset ℕ := Wtop.filter (fun w => supR C.gates w = {v})
    have hper_v : ∀ v : Fin 6,
        (Finset.univ.filter (fun p : Fin s × Fin 2 => v ∈ Rp p)).card ≤
          1 + ∑ w ∈ Gv v, (deg w - 1) := by
      intro v
      let Pv := Finset.univ.filter (fun p : Fin s × Fin 2 => v ∈ Rp p)
      let exitV := Finset.univ.filter (fun q : Fin s × Fin 2 =>
        supR C.gates (slotWire q) = {v} ∧ supR C.gates (12 + q.1.val) ≠ {v})
      let intV := Finset.univ.filter (fun q : Fin s × Fin 2 =>
        supR C.gates (slotWire q) = {v} ∧ supR C.gates (12 + q.1.val) = {v})
      have hex_map : ∀ p ∈ Pv, ∃ q ∈ exitV,
          (q = otherSlot p ∧ (C.gates.getD p.1.val ⟨.or, []⟩).op = .and) ∨
          ((C.gates.getD q.1.val ⟨.or, []⟩).op = .or ∧ 2 ≤ (supR C.gates (12 + q.1.val)).card ∧
            supR C.gates (12 + q.1.val) ⊆ supR C.gates (slotWire (otherSlot p))) := by
        intro p hp
        have hvRp : v ∈ Rp p := (Finset.mem_filter.1 hp).2
        rcases Finset.mem_image.1 hvRp with ⟨e, he, rfl⟩
        have hm := Finset.mem_filter.1 he
        have hspec := hchosen_spec e (Finset.mem_filter.1 hm.1).2
        rw [hm.2] at hspec
        rcases hexits_R e.2 (slotWire (otherSlot p)) (hslot_lt_top (otherSlot p)) hspec.2.2 with hsing | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
        · refine ⟨otherSlot p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hsing, ?_⟩, Or.inl ⟨rfl, hspec.1⟩⟩
          change supR C.gates (12 + p.1.val) ≠ {e.2}
          rw [supR_gate_and C.gates p.1.val hspec.1]
          exact Finset.empty_ne_singleton e.2
        · exact ⟨q, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq1, hq2⟩, Or.inr ⟨hq3, hq4, hq5⟩⟩
      let fV (p : Fin s × Fin 2) : Fin s × Fin 2 :=
        if h : p ∈ Pv then Classical.choose (hex_map p h) else p
      have hother_inj : Function.Injective otherSlot := by
        intro p1 p2 h
        have h1 : (otherSlot p1).1 = (otherSlot p2).1 := congrArg Prod.fst h
        have h2 : (otherSlot p1).2.val = (otherSlot p2).2.val := congrArg (fun x => x.2.val) h
        dsimp only [otherSlot] at h1 h2
        exact Prod.ext h1 (Fin.ext (by omega))
      have hPv_le_exit : Pv.card ≤ exitV.card := by
        apply Finset.card_le_card_of_injOn fV
        · intro p hp
          have hp' : p ∈ Pv := Finset.mem_coe.1 hp
          dsimp only [fV]; rw [dif_pos hp']
          exact Finset.mem_coe.2 (Classical.choose_spec (hex_map p hp')).1
        · intro p1 hp1 p2 hp2 hfeq
          have hp1' : p1 ∈ Pv := Finset.mem_coe.1 hp1
          have hp2' : p2 ∈ Pv := Finset.mem_coe.1 hp2
          have hs1 := (Classical.choose_spec (hex_map p1 hp1')).2
          have hs2 := (Classical.choose_spec (hex_map p2 hp2')).2
          dsimp only [fV] at hfeq; rw [dif_pos hp1', dif_pos hp2'] at hfeq
          set q := Classical.choose (hex_map p1 hp1')
          rw [← hfeq] at hs2
          rcases hs1 with ⟨hq1, hand1⟩ | ⟨hor1, hcard1, hsub1⟩
          · rcases hs2 with ⟨hq2, _⟩ | ⟨hor2, _, _⟩
            · exact hother_inj (hq1.symm.trans hq2)
            · have : q.1 = (otherSlot p1).1 := congrArg Prod.fst hq1
              dsimp only [otherSlot] at this
              rw [this, hand1] at hor2; cases hor2
          · rcases hs2 with ⟨hq2, hand2⟩ | ⟨_, _, hsub2⟩
            · have : q.1 = (otherSlot p2).1 := congrArg Prod.fst hq2
              dsimp only [otherSlot] at this
              rw [this, hand2] at hor1; cases hor1
            · rcases Finset.mem_image.1 (Finset.mem_filter.1 hp1').2 with ⟨e1, he1, he1v⟩
              rcases Finset.mem_image.1 (Finset.mem_filter.1 hp2').2 with ⟨e2, he2, he2v⟩
              have hm1 := Finset.mem_filter.1 he1
              have hm2 := Finset.mem_filter.1 he2
              have hsp1 := hchosen_spec e1 (Finset.mem_filter.1 hm1.1).2
              have hsp2 := hchosen_spec e2 (Finset.mem_filter.1 hm2.1).2
              rw [hm1.2] at hsp1
              rw [hm2.2] at hsp2
              rcases Finset.exists_mem_ne (by omega : 1 < (supR C.gates (12 + q.1.val)).card) v with ⟨v', hv', hvne⟩
              have hv_in : v ∈ supR C.gates (12 + q.1.val) := by
                have hqk : q.1.val < C.gates.length := by omega
                rcases List.length_eq_two.1 (hclean q.1.val hqk).1 with ⟨a, b, hab⟩
                have ha : a < 12 + q.1.val := (hclean q.1.val hqk).2 a (by rw [hab]; simp)
                have hb : b < 12 + q.1.val := (hclean q.1.val hqk).2 b (by rw [hab]; simp)
                rw [supR_gate_or C.gates q.1.val a b hor1 hab ha hb]
                have hqmem : supR C.gates (slotWire q) = {v} :=
                  (Finset.mem_filter.1 (Classical.choose_spec (hex_map p1 hp1')).1).2.1
                rcases q with ⟨q1, q2⟩
                fin_cases q2
                · dsimp only [slotWire] at hqmem
                  rw [hab] at hqmem
                  change supR C.gates a = {v} at hqmem
                  rw [hqmem]; exact Finset.mem_union_left _ (Finset.mem_singleton_self v)
                · dsimp only [slotWire] at hqmem
                  rw [hab] at hqmem
                  change supR C.gates b = {v} at hqmem
                  rw [hqmem]; exact Finset.mem_union_right _ (Finset.mem_singleton_self v)
              have hu_eq : e1.1 = e2.1 := by
                by_contra hune
                exact A6_k22_free e1.1 e2.1 hune v v' hvne.symm
                  ⟨hrect_A6 p1 hsp1.1 e1.1 hsp1.2.1 v (hsub1 hv_in),
                   hrect_A6 p1 hsp1.1 e1.1 hsp1.2.1 v' (hsub1 hv'),
                   hrect_A6 p2 hsp2.1 e2.1 hsp2.2.1 v (hsub2 hv_in),
                   hrect_A6 p2 hsp2.1 e2.1 hsp2.2.1 v' (hsub2 hv')⟩
              have he_eq : e1 = e2 := Prod.ext hu_eq (he1v.trans he2v.symm)
              rw [← hm1.2, ← hm2.2, he_eq]
      have hv_in_Gv : 6 + v.val ∈ Gv v :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
          by simpa using supR_6_12 C.gates (6 + v.val) (by omega) (by omega)⟩
      have hint_ge : (Gv v).card - 1 ≤ intV.card := by
        have hex_int : ∀ w ∈ (Gv v).erase (6 + v.val), ∃ q ∈ intV, 12 + q.1.val = w := by
          intro w hw
          rcases Finset.mem_erase.1 hw with ⟨hne, hwGv⟩
          rcases Finset.mem_filter.1 hwGv with ⟨hwR, hwR_eq⟩
          rw [Finset.mem_range] at hwR
          have hw12 : 12 ≤ w := by
            by_contra hlt
            by_cases h6 : w < 6
            · rw [supR_lt6 C.gates w h6] at hwR_eq
              exact Finset.empty_ne_singleton v hwR_eq
            · rw [supR_6_12 C.gates w (by omega) (by omega)] at hwR_eq
              have : (⟨w - 6, by omega⟩ : Fin 6) = v := Finset.singleton_injective hwR_eq
              have hvval : w - 6 = v.val := congrArg Fin.val this
              omega
          let k := w - 12
          have hw_eq : w = 12 + k := by omega
          have hk : k < C.gates.length := by omega
          rcases List.length_eq_two.1 (hclean k hk).1 with ⟨a, b, hab⟩
          have ha : a < 12 + k := (hclean k hk).2 a (by rw [hab]; simp)
          have hb : b < 12 + k := (hclean k hk).2 b (by rw [hab]; simp)
          have hget : C.gates[k]? = some (C.gates.getD k ⟨.or, []⟩) := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          have hgop : (C.gates.getD k ⟨.or, []⟩).op = .and ∨ (C.gates.getD k ⟨.or, []⟩).op = .or := by
            simpa using (hC.1 _ (List.mem_of_getElem? hget)).1
          rw [hw_eq] at hwR_eq
          have hwR0 : supR C.gates (12 + k) = {v} := hwR_eq
          rcases hgop with hand | hor
          · rw [supR_gate_and C.gates k hand] at hwR_eq
            exact absurd hwR_eq (Finset.empty_ne_singleton v)
          · rw [supR_gate_or C.gates k a b hor hab ha hb] at hwR_eq
            have hvab : v ∈ supR C.gates a ∨ v ∈ supR C.gates b := by
              have : v ∈ supR C.gates a ∪ supR C.gates b := by rw [hwR_eq]; exact Finset.mem_singleton_self v
              exact Finset.mem_union.1 this
            rcases hvab with hva | hvb
            · have hsa : supR C.gates a = {v} := by
                apply Finset.Subset.antisymm
                · rw [← hwR_eq]; exact Finset.subset_union_left
                · exact Finset.singleton_subset_iff.2 hva
              exact ⟨(⟨k, by omega⟩, 0), Finset.mem_filter.2 ⟨Finset.mem_univ _,
                by dsimp only [slotWire]; rw [hab]; exact hsa, hwR0⟩, hw_eq.symm⟩
            · have hsb : supR C.gates b = {v} := by
                apply Finset.Subset.antisymm
                · rw [← hwR_eq]; exact Finset.subset_union_right
                · exact Finset.singleton_subset_iff.2 hvb
              exact ⟨(⟨k, by omega⟩, 1), Finset.mem_filter.2 ⟨Finset.mem_univ _,
                by dsimp only [slotWire]; rw [hab]; exact hsb, hwR0⟩, hw_eq.symm⟩
        let gV (w : ℕ) : Fin s × Fin 2 :=
          if h : w ∈ (Gv v).erase (6 + v.val) then Classical.choose (hex_int w h) else (⟨0, by omega⟩, 0)
        have hle : ((Gv v).erase (6 + v.val)).card ≤ intV.card := by
          apply Finset.card_le_card_of_injOn gV
          · intro w hw
            have hw' : w ∈ (Gv v).erase (6 + v.val) := Finset.mem_coe.1 hw
            dsimp only [gV]; rw [dif_pos hw']
            exact Finset.mem_coe.2 (Classical.choose_spec (hex_int w hw')).1
          · intro w1 hw1 w2 hw2 hgeq
            have hw1' : w1 ∈ (Gv v).erase (6 + v.val) := Finset.mem_coe.1 hw1
            have hw2' : w2 ∈ (Gv v).erase (6 + v.val) := Finset.mem_coe.1 hw2
            have h1 := (Classical.choose_spec (hex_int w1 hw1')).2
            have h2 := (Classical.choose_spec (hex_int w2 hw2')).2
            dsimp only [gV] at hgeq; rw [dif_pos hw1', dif_pos hw2'] at hgeq
            rw [← h1, ← h2, hgeq]
        rwa [Finset.card_erase_of_mem hv_in_Gv] at hle
      have htot : intV.card + exitV.card = ∑ w ∈ Gv v, deg w := by
        let allV := Finset.univ.filter (fun q : Fin s × Fin 2 => supR C.gates (slotWire q) = {v})
        have hdisj : Disjoint intV exitV := by
          rw [Finset.disjoint_filter]
          intro q _ h1 h2; exact h2.2 h1.2
        have hun : intV ∪ exitV = allV := by
          ext q; simp only [Finset.mem_union, intV, exitV, allV, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases h : supR C.gates (12 + q.1.val) = {v} <;> simp [h]
        have hcard_all : allV.card = ∑ w ∈ Gv v, deg w := by
          have hfib := Finset.card_eq_sum_card_fiberwise (s := allV) (t := Gv v) (f := slotWire)
            (fun q hq => Finset.mem_filter.2 ⟨Finset.mem_range.2 (hslot_lt_top q), (Finset.mem_filter.1 hq).2⟩)
          rw [hfib]
          apply Finset.sum_congr rfl
          intro w hw
          congr 1; ext q
          simp only [allV, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact (Finset.mem_filter.1 hw).2, h⟩⟩
        rw [← Finset.card_union_of_disjoint hdisj, hun, hcard_all]
      have hsum_split : (Gv v).card + ∑ w ∈ Gv v, (deg w - 1) = ∑ w ∈ Gv v, deg w := by
        have : ∑ w ∈ Gv v, (1 + (deg w - 1)) = ∑ w ∈ Gv v, deg w := by
          apply Finset.sum_congr rfl
          intro w hw
          have := hdeg_pos w (Finset.mem_filter.1 hw).1; omega
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at this
        exact this
      have hGv_pos : 1 ≤ (Gv v).card := Finset.card_pos.2 ⟨6 + v.val, hv_in_Gv⟩
      change Pv.card ≤ 1 + ∑ w ∈ Gv v, (deg w - 1)
      omega
    have hswap : ∑ p : Fin s × Fin 2, (Rp p).card =
        ∑ v : Fin 6, (Finset.univ.filter (fun p : Fin s × Fin 2 => v ∈ Rp p)).card := by
      have h1 : ∀ p : Fin s × Fin 2, (Rp p).card = ∑ v : Fin 6, if v ∈ Rp p then 1 else 0 := fun p => by
        simp
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      simp
    have hdisjG : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 6)) Gv := by
      intro v1 _ v2 _ hne
      change Disjoint (Gv v1) (Gv v2)
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have e1 := (Finset.mem_filter.1 hw1).2
      have e2 := (Finset.mem_filter.1 hw2).2
      exact hne (Finset.singleton_injective (e1.symm.trans e2))
    have hsubG : (Finset.univ : Finset (Fin 6)).biUnion Gv ⊆ Wtop := by
      intro w hw
      rcases Finset.mem_biUnion.1 hw with ⟨v, _, hwv⟩
      exact (Finset.mem_filter.1 hwv).1
    calc ∑ p : Fin s × Fin 2, (Rp p).card
        = ∑ v : Fin 6, (Finset.univ.filter (fun p : Fin s × Fin 2 => v ∈ Rp p)).card := hswap
      _ ≤ ∑ v : Fin 6, (1 + ∑ w ∈ Gv v, (deg w - 1)) := Finset.sum_le_sum (fun v _ => hper_v v)
      _ = 6 + ∑ v : Fin 6, ∑ w ∈ Gv v, (deg w - 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      _ = 6 + ∑ w ∈ (Finset.univ : Finset (Fin 6)).biUnion Gv, (deg w - 1) := by
          rw [Finset.sum_biUnion hdisjG]
      _ ≤ 6 + ∑ w ∈ Wtop, (deg w - 1) := Nat.add_le_add_left (Finset.sum_le_sum_of_subset hsubG) 6
      _ = 6 + (s - 11) := by rw [hsum_surplus]
  omega

end PEqualNP.Outside.L_meta_25474_aux

theorem PEqualNP.Outside.L_meta_25474 :
    (∃ (n m : ℕ) (A : Fin n → Fin m → Bool) (s : ℕ), n ≤ 6 ∧ m ≤ 6 ∧ PEqualNP.Represents.RepSizeAtMost A s ∧ ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C ∧ ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + k) false = true → A u v = true)) := by
  refine ⟨6, 6, PEqualNP.Outside.L_meta_25474_aux.A6, 13, le_rfl, le_rfl,
    PEqualNP.Outside.L_meta_25474_aux.A6_repSize, ?_⟩
  rintro ⟨C, hCm, hCs, hCrep, hCand⟩
  exact PEqualNP.Outside.L_meta_25474_aux.no_strict_le_13 ⟨C, ⟨hCm, hCrep, hCand⟩, hCs⟩
