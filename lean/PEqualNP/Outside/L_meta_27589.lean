import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27589_aux.Ledger

open PEqualNP.CircuitLowerBounds

inductive Atom
  | off | p | q | meet | join | on
  deriving DecidableEq

def dual : Atom → Atom
  | .off => .on
  | .on => .off
  | .meet => .join
  | .join => .meet
  | .p => .p
  | .q => .q

def infimum : Atom → Atom → Atom
  | .off, _ | _, .off => .off
  | .on, y | y, .on => y
  | .meet, _ | _, .meet => .meet
  | .join, y | y, .join => y
  | .p, .p => .p
  | .q, .q => .q
  | _, _ => .meet

def op (s : Bool) (a b : Atom) : Atom :=
  if s then dual (infimum (dual a) (dual b)) else infimum a b

abbrev Col := Atom × Atom
def dead : Col := (.off, .off)
def goalCol : Col := (.meet, .join)
def good (w : Col) : Prop := w ≠ goalCol ∧ w ≠ (.join, .meet)
instance (w : Col) : Decidable (good w) := inferInstanceAs (Decidable (_ ∧ _))
def blend (s : Bool) (u v : Col) : Col := (op s u.1 v.1, op s u.2 v.2)

def uses (axis : Bool) : Atom → Bool
  | .off | .on => false
  | .p => !axis
  | .q => axis
  | _ => true

def cost (axis : Bool) (w : Col) := (uses axis w.1 || uses axis w.2).toNat

def allAtoms : List Atom := [.off, .p, .q, .meet, .join, .on]
def allCols : List Col := allAtoms.flatMap fun a => allAtoms.map fun b => (a, b)

lemma mem_allAtoms (a : Atom) : a ∈ allAtoms := by cases a <;> decide
lemma mem_allCols (c : Col) : c ∈ allCols := by
  rcases c with ⟨a, b⟩
  exact List.mem_flatMap.mpr ⟨a, mem_allAtoms a, List.mem_map.mpr ⟨b, mem_allAtoms b, rfl⟩⟩

theorem blend_good (s : Bool) (u v : Col) (hu : good u) (hv : good v)
    (hb : ∀ t : Bool, cost t u + cost t v ≤ 1) : good (blend s u v) := by
  have h : (([false, true] : List Bool).all fun s =>
      allCols.all fun u => allCols.all fun v =>
        if decide (good u) && decide (good v) && decide (cost false u + cost false v ≤ 1) &&
           decide (cost true u + cost true v ≤ 1)
        then decide (good (blend s u v)) else true) = true := by decide +kernel
  have h1 := List.all_eq_true.mp h s (by cases s <;> decide)
  have h2 := List.all_eq_true.mp h1 u (mem_allCols u)
  have h3 := List.all_eq_true.mp h2 v (mem_allCols v)
  have hc : (decide (good u) && decide (good v) && decide (cost false u + cost false v ≤ 1) &&
      decide (cost true u + cost true v ≤ 1)) = true := by
    simp [hu, hv, hb false, hb true]
  rw [hc] at h3
  exact of_decide_eq_true (by simpa using h3)

theorem blend_cost (s t : Bool) (u v : Col) :
    cost t (blend s u v) ≤ cost t u + cost t v := by
  have h : (([false, true] : List Bool).all fun s =>
      ([false, true] : List Bool).all fun t =>
      allCols.all fun u => allCols.all fun v =>
        decide (cost t (blend s u v) ≤ cost t u + cost t v)) = true := by decide +kernel
  have h1 := List.all_eq_true.mp h s (by cases s <;> decide)
  have h2 := List.all_eq_true.mp h1 t (by cases t <;> decide)
  have h3 := List.all_eq_true.mp h2 u (mem_allCols u)
  have h4 := List.all_eq_true.mp h3 v (mem_allCols v)
  exact of_decide_eq_true h4

def observe (p q : Bool) : Atom → Bool
  | .off => false
  | .p => p
  | .q => q
  | .meet => p && q
  | .join => p || q
  | .on => true

def view (s p q : Bool) (w : Col) : Bool := observe p q (if s then w.2 else w.1)

theorem blend_view (b s p q : Bool) (u v : Col) :
    view s p q (blend b u v) =
      if b then view s p q u || view s p q v else view s p q u && view s p q v := by
  have h : (([false, true] : List Bool).all fun b =>
      ([false, true] : List Bool).all fun s =>
      ([false, true] : List Bool).all fun p =>
      ([false, true] : List Bool).all fun q =>
      allCols.all fun u => allCols.all fun v =>
        decide (view s p q (blend b u v) =
          if b then view s p q u || view s p q v else view s p q u && view s p q v)) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp h b (by cases b <;> decide)
  have h2 := List.all_eq_true.mp h1 s (by cases s <;> decide)
  have h3 := List.all_eq_true.mp h2 p (by cases p <;> decide)
  have h4 := List.all_eq_true.mp h3 q (by cases q <;> decide)
  have h5 := List.all_eq_true.mp h4 u (mem_allCols u)
  have h6 := List.all_eq_true.mp h5 v (mem_allCols v)
  exact of_decide_eq_true h6

theorem distinguish (w : Col) (h : ∀ s p q, view s p q w = view s p q goalCol) : w = goalCol := by
  have hall : (allCols.all fun w =>
      if ([false, true] : List Bool).all (fun s =>
          ([false, true] : List Bool).all fun p =>
          ([false, true] : List Bool).all fun q =>
            decide (view s p q w = view s p q goalCol))
      then decide (w = goalCol) else true) = true := by decide +kernel
  have h1 := List.all_eq_true.mp hall w (mem_allCols w)
  have hcond : (([false, true] : List Bool).all fun s =>
      ([false, true] : List Bool).all fun p =>
      ([false, true] : List Bool).all fun q =>
        decide (view s p q w = view s p q goalCol)) = true := by
    simp [h]
  rw [hcond] at h1
  exact of_decide_eq_true (by simpa using h1)

def bin (op : Bool) (a b : Nat) : Gate := ⟨if op then .or else .and, [a, b]⟩

def reads (gs : List Gate) (o : Nat) := gs.flatMap Gate.inputs ++ [o]

def need (t : Bool) (w : List Col) (rs : List Nat) : Nat :=
  (rs.map fun j => cost t (w.getD j dead)).sum

theorem need_cons (t : Bool) (w : List Col) (a : Nat) (rs : List Nat) :
    need t w (a :: rs) = cost t (w.getD a dead) + need t w rs := rfl

theorem snoc_eq (w : List Col) (v : Col) : (w ++ [v]).getD w.length dead = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]; simp

theorem snoc_ne (w : List Col) (v : Col) (j : Nat) (hn : j ≠ w.length) :
    (w ++ [v]).getD j dead = w.getD j dead := by
  by_cases h : j < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem need_snoc (t : Bool) (w : List Col) (v : Col) (rs : List Nat) :
    need t (w ++ [v]) rs ≤ need t w rs + rs.count w.length * cost t v := by
  induction rs with
  | nil => simp [need]
  | cons j rs ih =>
    rw [need_cons, need_cons, List.count_cons]
    by_cases h : j = w.length
    · subst j; rw [snoc_eq]; simp only [beq_self_eq_true, ite_true, Nat.add_mul, Nat.one_mul]; omega
    · rw [snoc_ne _ _ _ h]; simp [h]; omega

def gateCol (g : Gate) (w : List Col) : Col :=
  let s := match g.op with | .or => true | _ => false
  blend s (w.getD (g.inputs.getD 0 0) dead) (w.getD (g.inputs.getD 1 0) dead)

theorem gate_bin (s : Bool) (a b : Nat) (w : List Col) :
    gateCol (bin s a b) w = blend s (w.getD a dead) (w.getD b dead) := by cases s <;> rfl

def run : List Gate → List Col → List Col
  | [], w => w
  | g :: gs, w => run gs (w ++ [gateCol g w])

theorem flow (gs : List Gate) (o : Nat) (w : List Col)
    (binary : ∀ g ∈ gs, ∃ s a b, g = bin s a b)
    (ok : ∀ i, good (w.getD i dead))
    (budget : ∀ t, need t w (reads gs o) ≤ 1)
    (single : ∀ j, w.length ≤ j → (reads gs o).count j ≤ 1) :
    good ((run gs w).getD o dead) := by
  induction gs generalizing w with
  | nil => exact ok o
  | cons g gs ih =>
    obtain ⟨s, a, b, rfl⟩ := binary g List.mem_cons_self
    let z := blend s (w.getD a dead) (w.getD b dead)
    have reads_eq : reads (bin s a b :: gs) o = a :: b :: reads gs o := by simp [reads, bin]
    have bounded (t : Bool) : cost t (w.getD a dead) + cost t (w.getD b dead) +
        need t w (reads gs o) ≤ 1 := by
      simpa only [reads_eq, need_cons, Nat.add_assoc] using budget t
    have rest_count (j : Nat) (hj : w.length ≤ j) : (reads gs o).count j ≤ 1 := by
      have hc := single j hj
      rw [reads_eq, List.count_cons, List.count_cons] at hc
      omega
    rw [run, gate_bin]
    apply ih (w ++ [z]) (fun g hm => binary g (List.mem_cons_of_mem _ hm))
    · intro i
      by_cases hi : i = w.length
      · subst i; rw [snoc_eq]; exact blend_good s _ _ (ok a) (ok b) (fun t => by have := bounded t; omega)
      · rw [snoc_ne _ _ _ hi]; exact ok i
    · intro t
      have h1 := need_snoc t w z (reads gs o)
      have hc := Nat.mul_le_mul_right (cost t z) (rest_count w.length le_rfl)
      simp only [Nat.one_mul] at hc
      have hcost : cost t z ≤ cost t (w.getD a dead) + cost t (w.getD b dead) := blend_cost s t _ _
      have hb := bounded t
      omega
    · intro j hj
      exact rest_count j (by simp at hj; omega)

theorem read_view (w : List Col) (s p q : Bool) (j : Nat) :
    (w.map (view s p q)).getD j false = view s p q (w.getD j dead) := by
  cases h : w[j]? <;> simp [List.getD, h, view, dead, observe]

def stepBool (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem one_view (w : List Col) (s p q b : Bool) (a d : Nat) :
    (w ++ [gateCol (bin b a d) w]).map (view s p q) =
      stepBool (w.map (view s p q)) (bin b a d) := by
  simp only [List.map_append, List.map_cons, List.map_nil, gate_bin, blend_view]
  rw [← read_view, ← read_view]
  cases b <;> simp [stepBool, bin, GateOp.eval]

theorem run_view (gs : List Gate) (w : List Col) (s p q : Bool)
    (hb : ∀ g ∈ gs, ∃ t a b, g = bin t a b) :
    (run gs w).map (view s p q) = gs.foldl stepBool (w.map (view s p q)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨t, a, b, rfl⟩ := hb g List.mem_cons_self
    rw [run, List.foldl_cons, ih _ (fun g hg => hb g (List.mem_cons_of_mem _ hg)), one_view]

def start : List Col := [(.off,.on), (.on,.on), (.on,.on), (.p,.p), dead, (.on,.on), dead, (.q,.q), (.off,.on)]

def assign (s p q : Bool) (i : Fin 9) := view s p q (start.getD i.val dead)

def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

theorem start_view : ∀ s p q, start.map (view s p q) = List.ofFn (assign s p q) := by decide

theorem target : ∀ s p q, matching (assign s p q) = view s p q goalCol := by decide

theorem start_valid (i : Nat) : good (start.getD i dead) := by
  by_cases h : i < 9
  · exact (by decide : ∀ i : Fin 9, good (start.getD i.val dead)) ⟨i, h⟩
  · rw [List.getD_eq_default _ _ (by change 9 ≤ i; omega)]; decide

def index (t : Bool) : Nat := if t then 7 else 3

theorem start_cost (t : Bool) (j : Nat) : cost t (start.getD j dead) = if j = index t then 1 else 0 := by
  by_cases h : j < 9
  · exact (by decide : ∀ t (j : Fin 9), cost t (start.getD j.val dead) =
      if j.val = index t then 1 else 0) t ⟨j, h⟩
  · rw [List.getD_eq_default _ _ (by change 9 ≤ j; omega)]
    cases t <;> simp [index, cost, dead, uses] <;> omega

theorem start_need (t : Bool) (rs : List Nat) : need t start rs = rs.count (index t) := by
  induction rs with
  | nil => rfl
  | cons j rs ih =>
    rw [need_cons, start_cost, ih, List.count_cons]
    by_cases h : j = index t <;> simp [h, Nat.add_comm]

theorem impossible (C : Circuit)
    (hc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x)
    (hb : ∀ g ∈ C.gates, ∃ t a b, g = bin t a b)
    (ha : (reads C.gates C.output).count 3 ≤ 1)
    (hb2 : (reads C.gates C.output).count 7 ≤ 1)
    (hs : ∀ j, 9 ≤ j → (reads C.gates C.output).count j ≤ 1) : False := by
  have hg := flow C.gates C.output start hb start_valid (fun t => by
    rw [start_need]; cases t <;> first | exact ha | exact hb2) hs
  apply hg.1
  apply distinguish
  intro s p q
  rw [← read_view, run_view _ _ _ _ _ hb, start_view]
  change C.eval (List.ofFn (assign s p q)) = _
  rw [hc, target]

end PEqualNP.Outside.L_meta_27589_aux.Ledger

namespace PEqualNP.Outside.L_meta_27589_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def target (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

private def g0 : Gate := ⟨.or, [0, 1]⟩
private def g1 : Gate := ⟨.and, [2, 5]⟩

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_indep (gs : List Gate) (i : ℕ) (hi : i ∉ gs.flatMap Gate.inputs)
    (a b : List Bool) (hl : a.length = b.length)
    (h : ∀ j : ℕ, j ≠ i → a.getD j false = b.getD j false) :
    ∀ j : ℕ, j ≠ i → (gs.foldl stepW a).getD j false = (gs.foldl stepW b).getD j false := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hn : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by simpa using hi
    have hm : g.inputs.map (fun j => a.getD j false) =
        g.inputs.map (fun j => b.getD j false) :=
      List.map_congr_left fun j hj => h j (fun he => hn.1 (he ▸ hj))
    simp only [List.foldl_cons]
    apply ih hn.2 (stepW a g) (stepW b g)
    · simp [stepW, hl]
    · intro j hj
      by_cases hk : j < a.length
      · simpa only [stepW, List.getD_append _ _ _ _ hk,
          List.getD_append _ _ _ _ (hl ▸ hk)] using h j hj
      · rw [stepW, stepW, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hk),
          List.getD_append_right _ _ _ _ (hl ▸ Nat.le_of_not_gt hk), hm, hl]

private def pfx (x : Fin 9 → Bool) : List Bool := stepW (stepW (List.ofFn x) g0) g1

private def witRow (i : Fin 9) (flip : Bool) (j : Fin 9) : Bool :=
  (([162, 97, 80, 132, 68, 66, 20, 12, 10] : List ℕ).getD i.val 0).testBit j.val || (flip && (j == i))

private theorem witRows (i : Fin 9) :
    target (witRow i false) ≠ target (witRow i true) ∧
      ∀ j : Fin 11, j.val ≠ i.val →
        (pfx (witRow i false)).getD j.val false = (pfx (witRow i true)).getD j.val false := by
  fin_cases i <;> decide +kernel

private theorem forceInputs (C : Circuit)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x)
    (ho : C.output + 1 = 9 + C.size)
    (gs : List Gate) (hg : C.gates = g0 :: g1 :: gs) :
    ∀ i : ℕ, i < 9 → i ∈ gs.flatMap Gate.inputs := by
  intro i hi
  by_contra hn
  let k : Fin 9 := ⟨i, hi⟩
  have hlen (x : Fin 9 → Bool) : (pfx x).length = 11 := by simp [pfx, stepW]
  have hrows := witRows k
  have hagree : ∀ j : ℕ, j ≠ i →
      (pfx (witRow k false)).getD j false = (pfx (witRow k true)).getD j false := by
    intro j hj
    by_cases hj' : j < 11
    · exact hrows.2 ⟨j, hj'⟩ hj
    · have ha : (pfx (witRow k false)).length ≤ j := by rw [hlen]; omega
      have hb : (pfx (witRow k true)).length ≤ j := by rw [hlen]; omega
      simp [ha, hb]
  have hout : C.output ≠ i := by simp [Circuit.size, hg] at ho; omega
  have hEq := fold_indep gs i hn _ _ (by rw [hlen, hlen]) hagree C.output hout
  have heval (x : Fin 9 → Bool) : C.eval (List.ofFn x) =
      (gs.foldl stepW (pfx x)).getD C.output false := by
    simp only [Circuit.eval, Circuit.wires, hg, List.foldl_cons]; rfl
  rw [← heval, ← heval, he, he] at hEq
  exact hrows.1 hEq

private theorem occCap (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht := ih (fun a ha => hf a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private theorem occTight (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (he : (gs.flatMap Gate.inputs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => hf a (by simp [ha])
    have hc := occCap gs ht
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at he
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact ih ht (by omega) a ha

private theorem main_contra (C : Circuit) (hfan : FanInTwo C) (hsz : C.size ≤ 12)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x)
    (ho : C.output + 1 = 9 + C.size)
    (hnorm : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b]))
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h0 : C.gates.head? = some g0) (h1 : C.gates.tail.head? = some g1) : False := by
  cases hg : C.gates with
  | nil => simp [hg] at h0
  | cons a rest =>
    cases rest with
    | nil => simp [hg] at h1
    | cons b gs =>
      have ha : a = g0 := by simpa [hg] using h0
      have hb : b = g1 := by simpa [hg] using h1
      subst a; subst b
      have hinputs := forceInputs C he ho gs hg
      let r := gs.flatMap Gate.inputs ++ [C.output]
      have hlenC : C.size = gs.length + 2 := by simp [Circuit.size, hg]
      have hlenG : C.gates.length = C.size := rfl
      have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hm => (hfan g (by simp [hg, hm])).2
      have hsub : Finset.range (9 + C.size) ⊆ r.toFinset := by
        intro z hz
        rw [Finset.mem_range] at hz
        rw [List.mem_toFinset]
        by_cases hz9 : z < 9
        · exact List.mem_append_left _ (hinputs z hz9)
        · by_cases hzo : z = C.output
          · subst hzo; exact List.mem_append_right _ (by simp)
          · let j : Fin C.gates.length := ⟨z - 9, by omega⟩
            obtain ⟨k, _, hk⟩ := hlive j (by dsimp [j]; omega)
            let g := C.gates.get k
            have hzg : z ∈ g.inputs := by
              have : 9 + j.val = z := by dsimp [j]; omega
              rwa [this] at hk
            have hmem : g ∈ gs := by
              have hm : g ∈ g0 :: g1 :: gs := hg ▸ List.get_mem _ k
              rcases List.mem_cons.mp hm with e | hrest
              · have hh : z ∈ g0.inputs := e ▸ hzg; simp [g0] at hh; omega
              · rcases List.mem_cons.mp hrest with e | htail
                · have hh : z ∈ g1.inputs := e ▸ hzg; simp [g1] at hh; omega
                · exact htail
            exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g, hmem, hzg⟩)
      have hcard : 9 + C.size ≤ r.toFinset.card := by
        simpa only [Finset.card_range] using Finset.card_le_card hsub
      have hcl := List.toFinset_card_le r
      have hrl : r.length = (gs.flatMap Gate.inputs).length + 1 := by simp [r]
      have hc := occCap gs hgs
      have hnd : r.Nodup :=
        (Multiset.toFinset_card_eq_card_iff_nodup (m := (r : Multiset ℕ))).mp
          (show r.toFinset.card = r.length by omega)
      have hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := by
        intro g hm
        rw [hg] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · rfl
        rcases List.mem_cons.mp hm with rfl | hm
        · rfl
        exact occTight gs hgs (by omega) g hm
      have hbin : ∀ g ∈ C.gates, ∃ t a b, g = Ledger.bin t a b := by
        intro g hm
        obtain ⟨n, hn⟩ := List.get_of_mem hm
        have hnrm := hnorm n
        rw [hn] at hnrm
        rcases hnrm with ⟨_, u, _, hu⟩ | ⟨hop, u, v, _, _, hp⟩
        · have hl := hlen2 g hm; simp [hu] at hl
        · have heq : g = ⟨g.op, g.inputs⟩ := rfl
          rcases hop with hop | hop
          · exact ⟨false, u, v, heq.trans (by rw [hop, hp]; rfl)⟩
          · exact ⟨true, u, v, heq.trans (by rw [hop, hp]; rfl)⟩
      have hreads : Ledger.reads C.gates C.output = 0 :: 1 :: 2 :: 5 :: r := by
        simp [Ledger.reads, hg, g0, g1, r]
      have hu (j : ℕ) (h0' : j ≠ 0) (h1' : j ≠ 1) (h2' : j ≠ 2) (h3' : j ≠ 5) :
          (Ledger.reads C.gates C.output).count j ≤ 1 := by
        rw [hreads]
        simpa [List.count_cons, Ne.symm h0', Ne.symm h1', Ne.symm h2', Ne.symm h3'] using
          List.nodup_iff_count_le_one.mp hnd j
      have hca := hu 3 (by decide) (by decide) (by decide) (by decide)
      have hcb := hu 7 (by decide) (by decide) (by decide) (by decide)
      have hcj : ∀ j, 9 ≤ j → (Ledger.reads C.gates C.output).count j ≤ 1 :=
        fun j hj => hu j (by omega) (by omega) (by omega) (by omega)
      exact Ledger.impossible C he hbin hca hcb hcj

end PEqualNP.Outside.L_meta_27589_aux

theorem PEqualNP.Outside.L_meta_27589 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩) := by
  rintro ⟨C, hfan, hsz, he, ho, hnorm, _, hlive, h0, h1⟩
  exact PEqualNP.Outside.L_meta_27589_aux.main_contra C hfan hsz he ho hnorm hlive h0 h1
