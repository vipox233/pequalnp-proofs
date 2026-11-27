import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27481_aux
open PEqualNP.CircuitLowerBounds

def A : Gate := ⟨.not, [0]⟩
def B : Gate := ⟨.or, [1,4]⟩
def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def seed (x : Fin 9 → Bool) := step (step (List.ofFn x) A) B
theorem seed_len (x) : (seed x).length = 11 := by simp [seed, step]
def pm (x : Fin 9 → Bool) :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
def mask (i : Fin 9) : Nat := [0,112,80,132,70,66,20,12,10][i.val]!
def low (i j : Fin 9) := (mask i).testBit j.val
def high (i j : Fin 9) := decide (j = i) || low i j
theorem cert : ∀ i : Fin 9, i.val ≠ 0 → pm (low i) ≠ pm (high i) ∧
    ∀ j : Fin 11, j.val ≠ i.val → (seed (low i)).getD j false = (seed (high i)).getD j false := by
  decide

def u (j : Fin 9) : Bool := decide (j = 0) || decide (j = 4) || decide (j = 8)
def v (j : Fin 9) : Bool := decide (j = 4) || decide (j = 8)
theorem uv : pm u = true ∧ pm v = false ∧
    ∀ j : Fin 11, j.val ≠ 0 → (seed u).getD j false = true → (seed v).getD j false = true := by
  decide

theorem runAgree (gs : List Gate) (i : Nat) (u v : List Bool)
    (hl : u.length = v.length) (ha : ∀ j, j ≠ i → u.getD j false = v.getD j false)
    (hn : i ∉ gs.flatMap Gate.inputs) : ∀ j, j ≠ i →
    (gs.foldl step u).getD j false = (gs.foldl step v).getD j false := by
  induction gs generalizing u v with
  | nil => exact ha
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hn
    have e : g.inputs.map (fun j => u.getD j false) = g.inputs.map (fun j => v.getD j false) :=
      List.map_congr_left fun j hj => ha j (fun eq => hn.1 (eq ▸ hj))
    apply ih (step u g) (step v g) (by simp [step,hl]) _ hn.2
    intro j hj
    by_cases h : j < u.length
    · simpa only [step, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hl ▸ h)] using ha j hj
    · simp only [step, List.getD_append_right _ _ _ _ (by omega : u.length ≤ j),
        List.getD_append_right _ _ _ _ (by omega : v.length ≤ j), hl, e]

theorem evalMono (g : Gate) (hop : g.op = .and ∨ g.op = .or) (f h : Nat → Bool)
    (hfh : ∀ i ∈ g.inputs, f i = true → h i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map h) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    intro H i hi
    exact hfh i hi (H i hi)
  · rw [hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨i, hi, H⟩
    exact ⟨i, hi, hfh i hi H⟩

theorem runMono (gs : List Gate) (u v : List Bool)
    (hl : u.length = v.length) (ha : ∀ j, j ≠ 0 → u.getD j false = true → v.getD j false = true)
    (hn : 0 ∉ gs.flatMap Gate.inputs) (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) : ∀ j, j ≠ 0 →
    (gs.foldl step u).getD j false = true → (gs.foldl step v).getD j false = true := by
  induction gs generalizing u v with
  | nil => exact ha
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hn
    have e : g.op.eval (g.inputs.map (fun j => u.getD j false)) = true →
        g.op.eval (g.inputs.map (fun j => v.getD j false)) = true :=
      evalMono g (hop g (by simp)) _ _ fun j hj => ha j (fun eq => hn.1 (eq ▸ hj))
    apply ih (step u g) (step v g) (by simp [step,hl]) _ hn.2 (fun k hk => hop k (by simp [hk]))
    intro j hj
    by_cases h : j < u.length
    · simpa only [step, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hl ▸ h)] using ha j hj
    · by_cases h2 : j = u.length
      · subst h2
        have e1 : (step u g).getD u.length false =
            g.op.eval (g.inputs.map (fun j => u.getD j false)) := by
          simp [step]
        have e2 : (step v g).getD u.length false =
            g.op.eval (g.inputs.map (fun j => v.getD j false)) := by
          rw [hl]; simp [step]
        rw [e1, e2]; exact e
      · have h3 : (step u g).length ≤ j := by simp [step]; omega
        have h4 : (step v g).length ≤ j := by simp [step]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h3]

theorem pinBound (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have := hf g (by simp)
    have := ih (fun k hk => hf k (by simp [hk]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

theorem pinBound1 (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (g0 : Gate) (h0 : g0 ∈ gs) (h1 : g0.inputs.length ≤ 1) :
    (gs.flatMap Gate.inputs).length + 1 ≤ 2 * gs.length := by
  induction gs with
  | nil => simp at h0
  | cons g gs ih =>
    have hg := hf g (by simp)
    have hr := pinBound gs (fun k hk => hf k (by simp [hk]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rcases List.mem_cons.mp h0 with eq | mem
    · subst eq; omega
    · have := ih (fun k hk => hf k (by simp [hk])) mem; omega

end PEqualNP.Outside.L_meta_27481_aux

open PEqualNP.Outside.L_meta_27481_aux PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_27481 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩) := by
  rintro ⟨⟨gates,out⟩, hf, hs, hc, ho, nf, _, live, hA, hB⟩
  cases gates with
  | nil => contradiction
  | cons a rest =>
    cases rest with
    | nil => contradiction
    | cons b gs =>
      change some a = some A at hA
      change some b = some B at hB
      cases Option.some.inj hA; cases Option.some.inj hB
      change (A :: B :: gs).length ≤ 11 at hs
      change out + 1 = 9 + (A :: B :: gs).length at ho
      simp only [List.length_cons] at hs ho
      change ∀ x, (gs.foldl step (seed x)).getD out false = pm x at hc
      let pins := out :: gs.flatMap Gate.inputs
      have raw (i : Fin 9) (hi : i.val ≠ 0) : i.val ∈ pins := by
        by_contra hn
        change i.val ∉ out :: gs.flatMap Gate.inputs at hn
        simp only [List.mem_cons, not_or] at hn
        apply (cert i hi).1
        rw [← hc, ← hc]
        apply runAgree _ i.val _ _ (by simp [seed_len]) _ hn.2 _ (Ne.symm hn.1)
        intro j hj
        by_cases h : j < 11
        · exact (cert i hi).2 ⟨j,h⟩ hj
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [seed_len]; omega : (seed (low i)).length ≤ j), List.getElem?_eq_none (by simp [seed_len]; omega : (seed (high i)).length ≤ j)]
      have memPins : ∀ n, n < 11 + gs.length → n ≠ 0 → n ∈ pins := by
        intro n hn h0
        by_cases h : n < 9
        · exact raw ⟨n,h⟩ h0
        by_cases last : n = out
        · simp [pins,last]
        let j : Fin (A :: B :: gs).length := ⟨n-9, by simp; omega⟩
        obtain ⟨k, _, hk⟩ := live j (by change n-9+1 < (A :: B :: gs).length; simp; omega)
        have en : 9 + j.val = n := by dsimp [j]; omega
        rw [en] at hk
        have mem := (A :: B :: gs).get_mem k
        simp only [List.mem_cons] at mem
        rcases mem with eq | eq | mem
        · rw [eq] at hk; simp [A] at hk; omega
        · rw [eq] at hk; simp [B] at hk; omega
        · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,mem,hk⟩)
      have plen := List.toFinset_card_le pins
      change pins.toFinset.card ≤ (gs.flatMap Gate.inputs).length + 1 at plen
      have hf2 : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hg => (hf g (by simp [hg])).2
      have bound := pinBound gs hf2
      by_cases h0 : 0 ∈ gs.flatMap Gate.inputs
      · have sub : Finset.range (11 + gs.length) ⊆ pins.toFinset := by
          intro n hn
          apply List.mem_toFinset.mpr
          have hn := Finset.mem_range.mp hn
          by_cases hz : n = 0
          · subst hz; exact List.mem_cons_of_mem _ h0
          · exact memPins n hn hz
        have hcard := Finset.card_le_card sub
        rw [Finset.card_range] at hcard
        omega
      have sub : (Finset.range (11 + gs.length)).erase 0 ⊆ pins.toFinset := by
        intro n hn
        apply List.mem_toFinset.mpr
        obtain ⟨hz, hn⟩ := Finset.mem_erase.mp hn
        exact memPins n (Finset.mem_range.mp hn) hz
      have hcard := Finset.card_le_card sub
      rw [Finset.card_erase_of_mem (by simp), Finset.card_range] at hcard
      have nfg : ∀ g ∈ gs, (g.op = .not ∧ g.inputs.length = 1) ∨ (g.op = .and ∨ g.op = .or) := by
        intro g hg
        obtain ⟨k, hk⟩ := List.get_of_mem (List.mem_cons_of_mem A (List.mem_cons_of_mem B hg))
        rcases nf k with ⟨hop, a, _, hin⟩ | ⟨hop, _⟩
        · left; rw [← hk]; exact ⟨hop, by rw [hin]; rfl⟩
        · right; rw [← hk]; exact hop
      by_cases hnot : ∃ g ∈ gs, g.op = .not
      · obtain ⟨g, hg, hgn⟩ := hnot
        have h1 : g.inputs.length ≤ 1 := by
          rcases nfg g hg with ⟨_, hl⟩ | hop
          · omega
          · rcases hop with hop | hop <;> rw [hop] at hgn <;> cases hgn
        have := pinBound1 gs hf2 g hg h1
        omega
      · push Not at hnot
        have hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or := by
          intro g hg
          rcases nfg g hg with ⟨hn, _⟩ | hop
          · exact absurd hn (hnot g hg)
          · exact hop
        have key := runMono gs (seed u) (seed v) (by simp [seed_len]) (by
          intro j hj hu
          by_cases h : j < 11
          · exact uv.2.2 ⟨j, h⟩ hj hu
          · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [seed_len]; omega : (seed u).length ≤ j)] at hu) h0 hop out (by omega)
        rw [hc u, hc v] at key
        have := key uv.1
        rw [uv.2.1] at this
        exact absurd this (by decide)
