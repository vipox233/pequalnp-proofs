import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27635

open PEqualNP.CircuitLowerBounds

private def pm (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def rows : Fin 9 → ℕ × ℕ :=
  ![(274, 275), (265, 267), (136, 140), (258, 266), (257, 273),
    (129, 161), (34, 98), (33, 161), (17, 273)]

private def low (i : Fin 9) (j : Fin 9) : Bool := (rows i).1.testBit j.val
private def high (i : Fin 9) (j : Fin 9) : Bool := (rows i).2.testBit j.val

private theorem witness (i : Fin 9) :
    (∀ j : Fin 9, j ≠ i → low i j = high i j) ∧
    (low i 0 || low i 1) = (high i 0 || high i 1) ∧
    low i i = false ∧ high i i = true ∧ pm (low i) = false ∧ pm (high i) = true := by
  fin_cases i <;> decide

private def firstGate : Gate := ⟨.or, [0, 1]⟩
private def secondGate (r : Fin 9) : Gate := ⟨.not, [r.val]⟩

private theorem splitGates (r : Fin 9) (gs : List Gate)
    (h₁ : gs.head? = some firstGate) (h₂ : gs.tail.head? = some (secondGate r)) :
    ∃ rest, gs = firstGate :: secondGate r :: rest := by
  cases gs with
  | nil => simp at h₁
  | cons g tail =>
    have hg : g = firstGate := Option.some.inj h₁
    subst g
    cases tail with
    | nil => simp at h₂
    | cons g rest =>
      have hg : g = secondGate r := Option.some.inj h₂
      exact ⟨rest, by rw [hg]⟩

private def reads (gs : List Gate) : List ℕ := gs.flatMap Gate.inputs

private def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue w g]

private def seed (r : Fin 9) (x : Fin 9 → Bool) : List Bool :=
  (List.ofFn x ++ [x 0 || x 1]) ++ [!(x r)]

private theorem inputGet (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi]
  rfl

private theorem evalWithSeed (C : Circuit) (r : Fin 9) (gs : List Gate)
    (hgs : C.gates = firstGate :: secondGate r :: gs) (x : Fin 9 → Bool) :
    C.eval (List.ofFn x) = (gs.foldl step (seed r x)).getD C.output false := by
  change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
  rw [hgs]
  simp only [List.foldl_cons]
  have h₀ : (List.ofFn x).getD 0 false = x 0 := inputGet x 0 (by decide)
  have h₁ : (List.ofFn x).getD 1 false = x 1 := inputGet x 1 (by decide)
  have hr : r.val < (List.ofFn x).length := by simp
  have hfirst : step (List.ofFn x) firstGate = List.ofFn x ++ [x 0 || x 1] := by
    simp only [step, gateValue, firstGate, GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id_eq, Bool.or_false, h₀, h₁]
  rw [hfirst]
  have hread : (List.ofFn x ++ [x 0 || x 1]).getD r.val false = x r := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hr,
      ← List.getD_eq_getElem?_getD, inputGet x _ r.isLt]
  have hsecond : step (List.ofFn x ++ [x 0 || x 1]) (secondGate r) = seed r x := by
    simp only [step, gateValue, secondGate, GateOp.eval, List.map_cons, List.map_nil,
      List.headD_cons, hread, seed]
  rw [hsecond]

private def RelatedAt (R : Bool → Bool → Prop) (r : ℕ) (u v : List Bool) : Prop :=
  ∀ i, i ≠ r → R (u.getD i false) (v.getD i false)

private theorem extendRelated {R : Bool → Bool → Prop} {r : ℕ} {u v : List Bool}
    (hf : R false false) (hlen : u.length = v.length) (h : RelatedAt R r u v)
    {a b : Bool} (hab : R a b) : RelatedAt R r (u ++ [a]) (v ++ [b]) := by
  intro i hi
  by_cases hlt : i < u.length
  · have hv : i < v.length := hlen ▸ hlt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
      List.getElem?_append_left hv] using h i hi
  · have hu : u.length ≤ i := Nat.le_of_not_gt hlt
    have hv : v.length ≤ i := hlen ▸ hu
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right hu, List.getElem?_append_right hv, ← hlen]
    cases i - u.length with
    | zero => simpa using hab
    | succ n => simpa using hf

private theorem seedRelated {R : Bool → Bool → Prop} {r i : Fin 9} {x y : Fin 9 → Bool}
    (refl : ∀ z, R z z) (h : ∀ j : Fin 9, j ≠ i → x j = y j)
    (hor : (x 0 || x 1) = (y 0 || y 1)) (hnot : R (!(x r)) (!(y r))) :
    RelatedAt R i.val (seed r x) (seed r y) := by
  apply extendRelated (refl false) (by simp) _ hnot
  apply extendRelated (refl false) (by simp)
  · intro j hj
    by_cases hj' : j < 9
    · rw [inputGet x j hj', inputGet y j hj', h _ (fun eq => hj (congrArg Fin.val eq))]
      exact refl _
    · simpa [List.getD_eq_getElem?_getD, hj'] using refl false
  · rw [hor]
    exact refl _

private theorem foldRelated (gs : List Gate) {R : Bool → Bool → Prop} {r : ℕ}
    (hf : R false false) (hn : r ∉ reads gs)
    (hg : ∀ g ∈ gs, ∀ u v : List Bool,
      (∀ i ∈ g.inputs, R (u.getD i false) (v.getD i false)) → R (gateValue u g) (gateValue v g))
    {u v : List Bool} (hlen : u.length = v.length) (h : RelatedAt R r u v) :
    RelatedAt R r (gs.foldl step u) (gs.foldl step v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro hr
      apply hn
      exact List.mem_append.mpr (Or.inr hr)
    · exact fun g' hm => hg g' (List.mem_cons_of_mem g hm)
    · simp [step, hlen]
    · apply extendRelated hf hlen h
      apply hg g (List.mem_cons_self) u v
      intro i hi
      apply h i
      intro eq
      subst i
      exact hn (by simp [reads, hi])

private theorem gateEqual (g : Gate) (u v : List Bool)
    (h : ∀ i ∈ g.inputs, u.getD i false = v.getD i false) : gateValue u g = gateValue v g :=
  congrArg g.op.eval (List.map_congr_left h)

private theorem binaryMonotone : ∀ a b c d : Bool, a ≤ c → b ≤ d →
    ((a && b) ≤ (c && d)) ∧ ((a || b) ≤ (c || d)) := by decide

private theorem gateOrdered (g : Gate) (a b : ℕ)
    (hop : g.op = .and ∨ g.op = .or) (hs : g.inputs = [a, b]) (u v : List Bool)
    (h : ∀ i ∈ g.inputs, u.getD i false ≤ v.getD i false) : gateValue u g ≤ gateValue v g := by
  have hp := h a (by simp [hs])
  have hq := h b (by simp [hs])
  have hmono := binaryMonotone _ _ _ _ hp hq
  rcases hop with hop | hop
  · simpa [gateValue, hs, hop, GateOp.eval] using hmono.1
  · simpa [gateValue, hs, hop, GateOp.eval] using hmono.2

private theorem mustRead (C : Circuit) (r i : Fin 9) (gs : List Gate)
    (hgs : C.gates = firstGate :: secondGate r :: gs) (hne : i.val ≠ r.val)
    (hout : C.output ≠ i.val) (hpm : ∀ x, C.eval (List.ofFn x) = pm x) : i.val ∈ reads gs := by
  by_contra hn
  obtain ⟨he, hor, _, _, hlo, hhi⟩ := witness i
  have hr : low i r = high i r := he r (fun eq => hne (congrArg Fin.val eq.symm))
  have hseed : RelatedAt Eq i.val (seed r (low i)) (seed r (high i)) :=
    seedRelated (fun _ => rfl) he hor (congrArg (fun b => !b) hr)
  have hfold := foldRelated gs rfl hn (fun g _ => gateEqual g) (by simp [seed]) hseed
  have heval := hfold C.output hout
  rw [← evalWithSeed C r gs hgs, ← evalWithSeed C r gs hgs, hpm, hpm, hlo, hhi] at heval
  exact Bool.false_ne_true heval

private theorem boundReads (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (reads gs).length ≤ 2 * gs.length ∧
    ((reads gs).length = 2 * gs.length → ∀ g ∈ gs, g.inputs.length = 2) := by
  induction gs with
  | nil => simp [reads]
  | cons g gs ih =>
    obtain ⟨hbound, heq⟩ := ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
    have hg := h g (List.mem_cons_self)
    have hs : (reads (g :: gs)).length = g.inputs.length + (reads gs).length := by
      simp [reads]
    simp only [hs, List.length_cons]
    constructor
    · omega
    · intro hfull g' hm
      rcases List.mem_cons.mp hm with rfl | hm
      · omega
      · exact heq (by omega) g' hm

private def Shaped (gs : List Gate) : Prop :=
  ∀ j : Fin gs.length,
    ((gs.get j).op = .not ∧ ∃ a, a < 9 + j.val ∧ (gs.get j).inputs = [a]) ∨
    (((gs.get j).op = .and ∨ (gs.get j).op = .or) ∧
      ∃ a b, a < b ∧ b < 9 + j.val ∧ (gs.get j).inputs = [a, b])

private theorem noWithInput (r : Fin 9) (C : Circuit) (hsize : C.size ≤ 11)
    (hpm : ∀ x, C.eval (List.ofFn x) = pm x) (hout : C.output + 1 = 9 + C.size)
    (hshape : Shaped C.gates)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h₁ : C.gates.head? = some firstGate) (h₂ : C.gates.tail.head? = some (secondGate r)) : False := by
  obtain ⟨gs, hgs⟩ := splitGates r C.gates h₁ h₂
  have hlen : C.gates.length = gs.length + 2 := by simp [hgs, Nat.add_assoc]
  change C.gates.length ≤ 11 at hsize
  change C.output + 1 = 9 + C.gates.length at hout
  have hforms : ∀ g ∈ gs, (∃ a, g.inputs = [a]) ∨
      (∃ a b, (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a, b]) := by
    intro g hg
    have hmem : g ∈ C.gates := by simp [hgs, hg]
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hmem
    rcases hshape j with ⟨_, a, _, ha⟩ | ⟨hop, a, b, _, _, hab⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨a, b, hop, hab⟩
  obtain ⟨hbound, hfull⟩ := boundReads gs (by
    intro g hg
    rcases hforms g hg with ⟨a, ha⟩ | ⟨a, b, _, hab⟩
    · simp [ha]
    · simp [hab])

  let required := (Finset.range (10 + gs.length)).erase r.val
  have hsub : required ⊆ (reads gs).toFinset := by
    intro w hw
    obtain ⟨hne, hwr⟩ := Finset.mem_erase.mp hw
    have hwlt := Finset.mem_range.mp hwr
    apply List.mem_toFinset.mpr
    by_cases hi : w < 9
    · exact mustRead C r ⟨w, hi⟩ gs hgs hne (by omega) hpm
    · let j : Fin C.gates.length := ⟨w - 9, by omega⟩
      obtain ⟨k, _, hk⟩ := hlive j (by dsimp [j]; omega)
      have hwj : 9 + j.val = w := by dsimp [j]; omega
      rw [hwj] at hk
      have hm : C.gates.get k ∈ firstGate :: secondGate r :: gs := by
        rw [← hgs]
        exact List.get_mem C.gates k
      simp only [List.mem_cons] at hm
      rcases hm with h | h | h
      · rw [h] at hk
        simp [firstGate] at hk
        omega
      · rw [h] at hk
        simp [secondGate] at hk
        omega
      · exact List.mem_flatMap.mpr ⟨_, h, hk⟩
  have hr := r.isLt
  have hcard : required.card = 9 + gs.length := by
    have hmem : r.val ∈ Finset.range (10 + gs.length) := Finset.mem_range.mpr (by omega)
    dsimp [required]
    rw [Finset.card_erase_of_mem hmem, Finset.card_range]
    omega
  have hrequired := Finset.card_le_card hsub
  have hreadCard := (reads gs).toFinset_card_le
  have htwo : ∀ g ∈ gs, g.inputs.length = 2 := hfull (by omega)
  have hnotRead : r.val ∉ reads gs := by
    intro hm
    have hall : Finset.range (10 + gs.length) ⊆ (reads gs).toFinset := by
      intro w hw
      by_cases e : w = r.val
      · exact List.mem_toFinset.mpr (e.symm ▸ hm)
      · exact hsub (Finset.mem_erase.mpr ⟨e, hw⟩)
    have hc := Finset.card_le_card hall
    rw [Finset.card_range] at hc
    omega

  obtain ⟨he, hor, hlow, hhigh, hlo, hhi⟩ := witness r
  have hseed : RelatedAt (· ≤ ·) r.val (seed r (high r)) (seed r (low r)) :=
    seedRelated (fun _ => le_rfl) (fun j hj => (he j hj).symm) hor.symm (by simp [hlow, hhigh])
  have hg : ∀ g ∈ gs, ∀ u v : List Bool,
      (∀ i ∈ g.inputs, u.getD i false ≤ v.getD i false) → gateValue u g ≤ gateValue v g := by
    intro g hm
    rcases hforms g hm with ⟨a, ha⟩ | ⟨a, b, hop, hab⟩
    · have ht := htwo g hm
      simp [ha] at ht
    · exact gateOrdered g a b hop hab
  have hfold := foldRelated gs (by decide) hnotRead hg (by simp [seed]) hseed
  have heval := hfold C.output (by omega)
  rw [← evalWithSeed C r gs hgs, ← evalWithSeed C r gs hgs, hpm, hpm, hhi, hlo] at heval
  exact (by decide : ¬ true ≤ false) heval

end PEqualNP.Outside.L_meta_27635

theorem PEqualNP.Outside.L_meta_27635 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩) := by
  rintro ⟨C, _, hsize, hpm, hout, hshape, _, hlive, h₁, h₂⟩
  exact L_meta_27635.noWithInput 2 C hsize hpm hout hshape hlive h₁ h₂
