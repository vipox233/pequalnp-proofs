import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace PEqualNP.Outside.L_lib_1315_aux

open PEqualNP.CircuitLowerBounds

def GateOK (m : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < m + j

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def notCnt (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

def evalWires (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

def wVal (gs : List Gate) (inp : List Bool) (i : ℕ) : Bool :=
  (evalWires gs inp).getD i false

lemma evalWires_length (gs : List Gate) (inp : List Bool) :
    (evalWires gs inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp; omega

lemma evalWires_append (g1 g2 : List Gate) (inp : List Bool) :
    evalWires (g1 ++ g2) inp = evalWires g2 (evalWires g1 inp) := by
  simp [evalWires, List.foldl_append]

lemma evalWires_prefix_getD (g1 g2 : List Gate) (inp : List Bool) {i : ℕ}
    (hi : i < inp.length + g1.length) :
    wVal (g1 ++ g2) inp i = wVal g1 inp i := by
  unfold wVal
  rw [evalWires_append]
  have hiw : i < (evalWires g1 inp).length := by rw [evalWires_length]; exact hi
  generalize evalWires g1 inp = w at hiw ⊢
  induction g2 generalizing w with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    have hi' : i < (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length := by
      simp; omega
    rw [ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiw]

lemma evalWires_input (gs : List Gate) (inp : List Bool) {i : ℕ} (hi : i < inp.length) :
    wVal gs inp i = inp.getD i false := by
  have h := evalWires_prefix_getD [] gs inp (i := i) (by simpa using hi)
  simpa [wVal, evalWires] using h

lemma notCnt_append (g1 g2 : List Gate) : notCnt (g1 ++ g2) = notCnt g1 + notCnt g2 := by
  simp [notCnt, List.filter_append]

lemma GateOK_nil (m : ℕ) : GateOK m [] := by
  refine ⟨by simp, fun j hj => by simp at hj⟩

lemma GateOK_append_gate {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < m + gs.length) :
    GateOK m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hgs.1 g' hg'
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hgs.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hin i hi

lemma wVal_append_gate (gs : List Gate) (g : Gate) (inp : List Bool) :
    wVal (gs ++ [g]) inp (inp.length + gs.length) =
    g.op.eval (g.inputs.map fun i => wVal gs inp i) := by
  unfold wVal
  rw [evalWires_append]
  have hlen : (evalWires gs inp).length = inp.length + gs.length := evalWires_length gs inp
  generalize evalWires gs inp = w at hlen ⊢
  simp only [evalWires, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, ← hlen]
  rw [List.getElem?_append_right le_rfl]
  simp

lemma mkAnd_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.and, [a, b]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = (wVal gs inp a && wVal gs inp b)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.and, [a, b]⟩ (Or.inl rfl) (by simp)
      (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

lemma mkOr_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.or, [a, b]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = (wVal gs inp a || wVal gs inp b)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.or, [a, b]⟩ (Or.inr (Or.inl rfl)) (by simp)
      (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

lemma mkNot_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a : ℕ}
    (ha : a < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.not, [a]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs + 1 ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = !(wVal gs inp a)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.not, [a]⟩ (Or.inr (Or.inr rfl)) (by simp)
      (by intro i hi; simp at hi; subst hi; exact ha),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

def Extends (gs gs' : List Gate) : Prop := ∃ suf, gs' = gs ++ suf

lemma Extends.refl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma Extends.trans {g1 g2 g3 : List Gate} (h1 : Extends g1 g2) (h2 : Extends g2 g3) :
    Extends g1 g3 := by
  rcases h1 with ⟨s1, rfl⟩; rcases h2 with ⟨s2, rfl⟩
  exact ⟨s1 ++ s2, by simp [List.append_assoc]⟩

lemma Extends.length_le {g1 g2 : List Gate} (h : Extends g1 g2) : g1.length ≤ g2.length := by
  rcases h with ⟨s, rfl⟩; simp

lemma Extends.wVal_eq {g1 g2 : List Gate} (h : Extends g1 g2) (inp : List Bool)
    {i : ℕ} (hi : i < inp.length + g1.length) :
    wVal g2 inp i = wVal g1 inp i := by
  rcases h with ⟨s, rfl⟩
  exact evalWires_prefix_getD g1 s inp hi

lemma Extends.map_wVal_eq {g1 g2 : List Gate} (h : Extends g1 g2) (inp : List Bool)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < inp.length + g1.length) :
    ws.map (wVal g2 inp) = ws.map (wVal g1 inp) := by
  apply List.map_congr_left
  intro w hw
  exact h.wVal_eq inp (hws w hw)

lemma mkAnd_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = (wVal gs inp a && wVal gs inp b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkAnd_step hgs ha hb
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

lemma mkOr_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = (wVal gs inp a || wVal gs inp b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkOr_step hgs ha hb
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

lemma mkNot_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a : ℕ}
    (ha : a < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs + 1 ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = !(wVal gs inp a) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkNot_step hgs ha
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

def inpVec (m : ℕ) (x : Finset (Fin m)) : List Bool :=
  List.ofFn (fun i : Fin m => decide (i ∈ x)) ++ [false, true]

lemma inpVec_length (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).length = m + 2 := by
  simp [inpVec]

lemma inpVec_getD_lt (m : ℕ) (x : Finset (Fin m)) (i : Fin m) :
    (inpVec m x).getD i.val false = decide (i ∈ x) := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp : i.val < (List.ofFn (fun j : Fin m => decide (j ∈ x))).length)]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

lemma inpVec_getD_m (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).getD m false = false := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp : (List.ofFn (fun j : Fin m => decide (j ∈ x))).length ≤ m)]
  simp

lemma inpVec_getD_m1 (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).getD (m + 1) false = true := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp : (List.ofFn (fun j : Fin m => decide (j ∈ x))).length ≤ m + 1)]
  simp

lemma exists_map_build {m : ℕ} (c len : ℕ) (gs0 : List Gate) (P : ℕ → List Gate → ℕ → Prop)
    (hP_mono : ∀ i < len, ∀ gs1 gs2 w, w < m + gs1.length → Extends gs1 gs2 → P i gs1 w → P i gs2 w)
    (hstep : ∀ i < len, ∀ gs, Extends gs0 gs → GateOK m gs →
      ∃ gs' w, Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + c ∧ w < m + gs'.length ∧ P i gs' w)
    (hgs0 : GateOK m gs0) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      Extends gs0 gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs0 ∧
      gs'.length ≤ gs0.length + c * len ∧ ws.length = len ∧
      (∀ w ∈ ws, w < m + gs'.length) ∧
      ∀ i < len, P i gs' (ws.getD i 0) := by
  suffices h : ∀ k ≤ len,
      ∃ (gs' : List Gate) (ws : List ℕ),
        Extends gs0 gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs0 ∧
        gs'.length ≤ gs0.length + c * k ∧ ws.length = k ∧
        (∀ w ∈ ws, w < m + gs'.length) ∧
        ∀ i < k, P i gs' (ws.getD i 0) from h len le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨gs0, [], Extends.refl gs0, hgs0, rfl, by simp, rfl, by simp, fun i hi => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨gs1, ws1, hext01, hgs1, hnc1, hlen1, hwl1, hwsW1, hP1⟩ := ih (by omega)
    obtain ⟨gs2, wk, hext12, hgs2, hnc2, hlen2, hwk, hPk⟩ := hstep k (by omega) gs1 hext01 hgs1
    refine ⟨gs2, ws1 ++ [wk], hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by have hmul : c * (k + 1) = c * k + c := by ring
         omega,
      by simp [hwl1],
      fun w hw => by
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have := hext12.length_le; have := hwsW1 w hw; omega
        · exact hwk,
      ?_⟩
    intro i hi
    by_cases hik : i < k
    · have hget : (ws1 ++ [wk]).getD i 0 = ws1.getD i 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < ws1.length)]
      rw [hget]
      have hmem : ws1.getD i 0 ∈ ws1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      exact hP_mono i (by omega) gs1 gs2 _ (hwsW1 _ hmem) hext12 (hP1 i hik)
    · have hieq : i = k := by omega
      rw [hieq]
      have hget : (ws1 ++ [wk]).getD k 0 = wk := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ws1.length ≤ k)]
        simp [hwl1]
      rw [hget]
      exact hPk

lemma exists_b_decoder_aux {m : ℕ} (b : ℕ) (wF wT : ℕ) (hwF : wF < m) (hwT : wT < m)
    (T : List ℕ) (hTl : T.length = 2 ^ b) :
    ∀ (d : ℕ) (_hd : d ≤ b) (gs : List Gate), GateOK m gs →
      (∀ w ∈ T, w < m + gs.length) →
      ∃ (gs' : List Gate) (eqP : List ℕ),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs + d ∧
        gs'.length ≤ gs.length + 5 * 2 ^ d ∧ eqP.length = 2 ^ d ∧
        (∀ w ∈ eqP, w < m + gs'.length) ∧
        ∀ (inp : List Bool) (v : ℕ), inp.length = m →
          inp.getD wF false = false → inp.getD wT false = true →
          v < 2 ^ b →
          (∀ k, 1 ≤ k → k < 2 ^ b → wVal gs inp (T.getD k 0) = decide (k ≤ v)) →
          ∀ u < 2 ^ d, wVal gs' inp (eqP.getD u 0) = decide (v / 2 ^ (b - d) = u) := by
  intro d
  induction d with
  | zero =>
    intro _ gs hgs _
    refine ⟨gs, [wT], Extends.refl gs, hgs, by simp, by simp, by simp,
      fun w hw => by simp at hw; subst hw; omega, ?_⟩
    intro inp v hinp _ hT hv _ u hu
    have hu0 : u = 0 := by omega
    subst hu0
    have hdiv : v / 2 ^ b = 0 := Nat.div_eq_of_lt hv
    simp only [Nat.sub_zero, hdiv, decide_true, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, Option.getD_some]
    rw [evalWires_input gs inp (by omega), hT]
  | succ d ih =>
    intro hdb gs hgs hTW
    obtain ⟨gs1, eqP, hext01, hgs1, hnc1, hlen1, heqPl, heqPW, hev1⟩ :=
      ih (by omega) gs hgs hTW
    let p := b - (d + 1)
    have hbd : b - d = p + 1 := by dsimp only [p]; omega

    have hbp_build : ∀ (cnt : ℕ) (_hcnt : cnt ≤ 2 ^ d) (gsA : List Gate),
        Extends gs1 gsA → GateOK m gsA →
        ∃ (gsB : List Gate) (acc : ℕ),
          Extends gsA gsB ∧ GateOK m gsB ∧ notCnt gsB = notCnt gsA ∧
          gsB.length ≤ gsA.length + 2 * cnt ∧ acc < m + gsB.length ∧
          ∀ (inp : List Bool), inp.length = m → inp.getD wF false = false →
            wVal gsB inp acc = decide (∃ u < cnt,
              wVal gs1 inp (eqP.getD u 0) = true ∧
              wVal gs inp (T.getD (u * 2 ^ (p + 1) + 2 ^ p) 0) = true) := by
      intro cnt
      induction cnt with
      | zero =>
        intro _ gsA _ hgsA
        refine ⟨gsA, wF, Extends.refl gsA, hgsA, rfl, by simp, by omega, ?_⟩
        intro inp hinp hF
        rw [evalWires_input gsA inp (by omega), hF]
        simp
      | succ c ihc =>
        intro hc gsA hext1A hgsA
        obtain ⟨gsB, acc, hextAB, hgsB, hncB, hlenB, haccW, hevB⟩ := ihc (by omega) gsA hext1A hgsA
        have hext1B : Extends gs1 gsB := hext1A.trans hextAB
        have hext0B : Extends gs gsB := hext01.trans hext1B
        let eu := eqP.getD c 0
        have heu_mem : eu ∈ eqP := by
          dsimp only [eu]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have heuW : eu < m + gsB.length := by have := hext1B.length_le; have := heqPW _ heu_mem; omega
        have hidx_lt : c * 2 ^ (p + 1) + 2 ^ p < 2 ^ b := by
          have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
          have h2 : c + 1 ≤ 2 ^ d := hc
          have h3 : (c + 1) * 2 ^ (p + 1) ≤ 2 ^ d * 2 ^ (p + 1) := Nat.mul_le_mul_right _ h2
          have h4 : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
          have h5 : 0 < 2 ^ p := Nat.two_pow_pos p
          nlinarith
        let tu := T.getD (c * 2 ^ (p + 1) + 2 ^ p) 0
        have htu_mem : tu ∈ T := by
          dsimp only [tu]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have htuW : tu < m + gsB.length := by have := hext0B.length_le; have := hTW _ htu_mem; omega
        obtain ⟨hgC, hnC, hlC, hwC, heC⟩ := mkAnd_step hgsB heuW htuW
        let gsC := gsB ++ [⟨GateOp.and, [eu, tu]⟩]
        let wC := m + gsB.length
        have hgsCl : gsC.length = gsB.length + 1 := hlC
        obtain ⟨hgD, hnD, hlD, hwD, heD⟩ := mkOr_step hgC (by omega : acc < m + gsC.length) hwC
        let gsD := gsC ++ [⟨GateOp.or, [acc, wC]⟩]
        let wD := m + gsC.length
        refine ⟨gsD, wD, hextAB.trans (Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩), hgD,
          hnD.trans (hnC.trans hncB), by simp only [gsD, gsC, List.length_append, List.length_singleton]; omega, hwD, ?_⟩
        intro inp hinp hF
        have eC := heC inp hinp; have eD := heD inp hinp
        rw [eD.2, eC.1 acc haccW, eC.2, hevB inp hinp hF,
          hext1B.wVal_eq inp (by have := heqPW _ heu_mem; omega),
          hext0B.wVal_eq inp (by have := hTW _ htu_mem; omega)]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨u, hu, h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨u, by omega, h1, h2⟩
          · exact ⟨c, by omega, h1, h2⟩
        · rintro ⟨u, hu, h1, h2⟩
          by_cases huc : u < c
          · exact Or.inl ⟨u, huc, h1, h2⟩
          · have : u = c := by omega
            subst this; exact Or.inr ⟨h1, h2⟩
    obtain ⟨gs2, bp, hext12, hgs2, hnc2, hlen2, hbpW, hev_bp⟩ := hbp_build (2 ^ d) le_rfl gs1 (Extends.refl gs1) hgs1

    obtain ⟨hgs3, hnc3, hlen3, hnbpW, hev3⟩ := mkNot_step hgs2 hbpW
    let gs3 := gs2 ++ [⟨GateOp.not, [bp]⟩]
    let nbp := m + gs2.length
    have hext23 : Extends gs2 gs3 := ⟨_, rfl⟩
    have hext13 : Extends gs1 gs3 := hext12.trans hext23
    have hgs3l : gs3.length = gs2.length + 1 := hlen3

    have hbp3 : bp < m + gs3.length := by omega
    obtain ⟨gs4, nextP, hext34, hgs4, hnc4, hlen4, hnextl, hnextW, hnextP⟩ :=
      exists_map_build (m := m) 1 (2 ^ (d + 1)) gs3
        (fun u gsX w => ∀ (inp : List Bool), inp.length = m →
          wVal gsX inp w = (wVal gs1 inp (eqP.getD (u / 2) 0) &&
            if u % 2 = 0 then wVal gs3 inp nbp else wVal gs3 inp bp))
        (fun u _ gsA gsB w hw hext hP inp hinp => by rw [hext.wVal_eq inp (by omega)]; exact hP inp hinp)
        (fun u hu gsA hext3A hgsA => by
          have hud : u / 2 < 2 ^ d := by
            have h2d : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
            omega
          let eu := eqP.getD (u / 2) 0
          have heu_mem : eu ∈ eqP := by
            dsimp only [eu]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
          have hext1A : Extends gs1 gsA := hext13.trans hext3A
          have heuA : eu < m + gsA.length := by have := hext1A.length_le; have := heqPW _ heu_mem; omega
          let bitW := if u % 2 = 0 then nbp else bp
          have hbitA : bitW < m + gsA.length := by
            have := hext3A.length_le; dsimp only [bitW]; split_ifs <;> omega
          obtain ⟨hgB, hnB, hlB, hwB, heB⟩ := mkAnd_step hgsA heuA hbitA
          refine ⟨gsA ++ [⟨GateOp.and, [eu, bitW]⟩], m + gsA.length, ⟨_, rfl⟩, hgB, hnB, by omega, hwB, ?_⟩
          intro inp hinp
          rw [(heB inp hinp).2, hext1A.wVal_eq inp (by have := heqPW _ heu_mem; omega)]
          congr 1
          dsimp only [bitW]
          split_ifs
          · exact hext3A.wVal_eq inp (by omega)
          · exact hext3A.wVal_eq inp (by omega))
        hgs3
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hlen_tot : gs4.length ≤ gs.length + 5 * 2 ^ (d + 1) := by omega
    have hnc_tot : notCnt gs4 = notCnt gs + (d + 1) := by rw [hnc4, hnc3, hnc2, hnc1]; omega
    refine ⟨gs4, nextP, hext01.trans (hext13.trans hext34), hgs4, hnc_tot, hlen_tot, hnextl, hnextW, ?_⟩
    intro inp v hinp hF hT hv hTspec u hu
    rw [hnextP u hu inp hinp]
    have hud : u / 2 < 2 ^ d := by omega
    have heq_u2 : wVal gs1 inp (eqP.getD (u / 2) 0) = decide (v / 2 ^ (p + 1) = u / 2) := by
      rw [hev1 inp v hinp hF hT hv hTspec (u / 2) hud, hbd]
    have hbp_val : wVal gs2 inp bp = decide ((v / 2 ^ p) % 2 = 1) := by
      rw [hev_bp inp hinp hF]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      have hdiv2 : v / 2 ^ (p + 1) = (v / 2 ^ p) / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      have hvp_lt : v / 2 ^ (p + 1) < 2 ^ d := by
        have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        omega
      have hidx_pos : 1 ≤ (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p := by
        have := Nat.two_pow_pos p; omega
      have hidx_lt : (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p < 2 ^ b := by
        have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
        have h2 : (v / 2 ^ (p + 1) + 1) * 2 ^ (p + 1) ≤ 2 ^ d * 2 ^ (p + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h3 : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
        have h4 := Nat.two_pow_pos p
        nlinarith
      have hiff_arith : (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p ≤ v ↔ (v / 2 ^ p) % 2 = 1 := by
        have hm := Nat.div_add_mod v (2 ^ p)
        have hmlt := Nat.mod_lt v (Nat.two_pow_pos p)
        have hm2 := Nat.div_add_mod (v / 2 ^ p) 2
        have hm2lt : (v / 2 ^ p) % 2 < 2 := Nat.mod_lt _ (by omega)
        have hp2 : 2 ^ (p + 1) = 2 * 2 ^ p := by ring
        rw [hdiv2, hp2]
        generalize 2 ^ p = P at hm hmlt ⊢
        generalize v / P = A at hm hm2 hm2lt ⊢
        have hA2 : A % 2 = 0 ∨ A % 2 = 1 := by omega
        rcases hA2 with h0 | h1
        · have hAeq : A = 2 * (A / 2) := by omega
          have hmul : A / 2 * (2 * P) = P * A := by (conv_rhs => rw [hAeq]); ring
          rw [h0, hmul]
          constructor
          · intro h; omega
          · intro h; omega
        · have hAeq : A = 2 * (A / 2) + 1 := by omega
          have hmul : A / 2 * (2 * P) + P = P * A := by (conv_rhs => rw [hAeq]); ring
          rw [h1, hmul]
          constructor
          · intro _; rfl
          · intro _; omega
      constructor
      · rintro ⟨w, hw, hw1, hw2⟩
        rw [hev1 inp v hinp hF hT hv hTspec w hw, hbd, decide_eq_true_eq] at hw1
        subst hw1
        rw [hTspec _ hidx_pos hidx_lt, decide_eq_true_eq] at hw2
        exact hiff_arith.1 hw2
      · intro hmod
        refine ⟨v / 2 ^ (p + 1), hvp_lt, ?_, ?_⟩
        · rw [hev1 inp v hinp hF hT hv hTspec _ hvp_lt, hbd]; simp
        · rw [hTspec _ hidx_pos hidx_lt, decide_eq_true_eq]
          exact hiff_arith.2 hmod
    have hbp3_val : wVal gs3 inp bp = decide ((v / 2 ^ p) % 2 = 1) := by
      rw [(hev3 inp hinp).1 bp hbpW, hbp_val]
    have hnbp3_val : wVal gs3 inp nbp = decide ((v / 2 ^ p) % 2 = 0) := by
      rw [(hev3 inp hinp).2, hbp_val]
      have hmod2 : (v / 2 ^ p) % 2 = 0 ∨ (v / 2 ^ p) % 2 = 1 := by omega
      rcases hmod2 with h | h <;> simp [h]
    have hdiv2 : v / 2 ^ (p + 1) = (v / 2 ^ p) / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [heq_u2, hbp3_val, hnbp3_val, hdiv2]
    split_ifs with hpar
    · apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      dsimp only [p]; omega
    · apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      dsimp only [p]; omega

def notInBit (w : List Bool) (g : Gate) : ℕ :=
  if (g.inputs.map fun i => w.getD i false).headD false then 1 else 0

def notCodeFrom (w : List Bool) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let w' := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      if isNotOp g.op then
        notInBit w g * 2 ^ notCnt gs + notCodeFrom w' gs
      else
        notCodeFrom w' gs

lemma notCnt_cons (g : Gate) (gs : List Gate) :
    notCnt (g :: gs) = (if isNotOp g.op then 1 else 0) + notCnt gs := by
  unfold notCnt
  rw [List.filter_cons]
  cases isNotOp g.op <;> simp [Nat.add_comm]

lemma notCodeFrom_lt (gs : List Gate) (w : List Bool) :
    notCodeFrom w gs < 2 ^ notCnt gs := by
  induction gs generalizing w with
  | nil => simp [notCodeFrom, notCnt]
  | cons g gs ih =>
    simp only [notCodeFrom, notCnt_cons]
    split_ifs with hnot
    · have hih := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      have hbit : notInBit w g ≤ 1 := by unfold notInBit; split_ifs <;> omega
      have hpow : 2 ^ (1 + notCnt gs) = 2 ^ notCnt gs + 2 ^ notCnt gs := by
        rw [pow_add, pow_one]; ring
      rw [hpow]
      nlinarith
    · simp only [zero_add]
      exact ih _

lemma notCodeFrom_mono_and_fall (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) →
      notCodeFrom w1 gs ≤ notCodeFrom w2 gs ∧
      ((∃ i : ℕ, (evalWires gs w1).getD i false = true ∧ (evalWires gs w2).getD i false = false) →
       notCodeFrom w1 gs < notCodeFrom w2 gs) := by
  induction gs with
  | nil =>
    intro w1 w2 _ hle
    refine ⟨le_rfl, ?_⟩
    rintro ⟨i, h1, h2⟩
    simp only [evalWires, List.foldl_nil] at h1 h2
    have := hle i h1
    rw [h2] at this; cases this
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg := hop g (by simp)
    have hrest : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not :=
      fun g' hg' => hop g' (by simp [hg'])
    let v1 := g.op.eval (g.inputs.map fun i => w1.getD i false)
    let v2 := g.op.eval (g.inputs.map fun i => w2.getD i false)
    let w1' := w1 ++ [v1]
    let w2' := w2 ++ [v2]
    have hstep_le : (v1 = true → v2 = true) →
        ∀ i : ℕ, w1'.getD i false = true → w2'.getD i false = true := by
      intro hv i hi
      by_cases hilt : i < w1.length
      · have h1 : w1'.getD i false = w1.getD i false := by
          simp only [w1', List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
        have h2 : w2'.getD i false = w2.getD i false := by
          simp only [w2', List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w2.length)]
        rw [h1] at hi; rw [h2]; exact hle i hi
      · by_cases hieq : i = w1.length
        · subst hieq
          have h1 : w1'.getD w1.length false = v1 := by simp [w1', List.getD_eq_getElem?_getD]
          have h2 : w2'.getD w1.length false = v2 := by simp [w2', hlen, List.getD_eq_getElem?_getD]
          rw [h1] at hi; rw [h2]; exact hv hi
        · have h1 : w1'.getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [w1']; omega)]; rfl
          rw [h1] at hi; cases hi
    rcases hg with hAnd | hOr | hNot
    · have hnotF : isNotOp g.op = false := by rw [hAnd]; rfl
      have hv : v1 = true → v2 = true := by
        dsimp only [v1, v2]; rw [hAnd]; simp only [GateOp.eval, List.all_eq_true, id_eq]
        intro hall b hb
        rcases List.mem_map.1 hb with ⟨i, hi, rfl⟩
        exact hle i (hall (w1.getD i false) (List.mem_map_of_mem hi))
      have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
      simpa [notCodeFrom, hnotF, evalWires, List.foldl_cons, w1', w2', v1, v2] using hih
    · have hnotF : isNotOp g.op = false := by rw [hOr]; rfl
      have hv : v1 = true → v2 = true := by
        dsimp only [v1, v2]; rw [hOr]; simp only [GateOp.eval, List.any_eq_true, id_eq]
        rintro ⟨b, hb, rfl⟩
        rcases List.mem_map.1 hb with ⟨i, hi, hwi⟩
        exact ⟨w2.getD i false, List.mem_map_of_mem hi, hle i hwi⟩
      have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
      simpa [notCodeFrom, hnotF, evalWires, List.foldl_cons, w1', w2', v1, v2] using hih
    · have hnotT : isNotOp g.op = true := by rw [hNot]; rfl
      let b1 := (g.inputs.map fun i => w1.getD i false).headD false
      let b2 := (g.inputs.map fun i => w2.getD i false).headD false
      have hb_le : b1 = true → b2 = true := by
        dsimp only [b1, b2]
        cases hgin : g.inputs with
        | nil => intro h; simp at h
        | cons a _ => simp only [List.map_cons, List.headD_cons]; exact hle a
      have hv1 : v1 = !b1 := by dsimp only [v1, b1]; rw [hNot]; rfl
      have hv2 : v2 = !b2 := by dsimp only [v2, b2]; rw [hNot]; rfl
      by_cases hbeq : b1 = b2
      · have hbit : notInBit w1 g = notInBit w2 g := by
          unfold notInBit; change (if b1 then 1 else 0) = (if b2 then 1 else 0); rw [hbeq]
        have hv : v1 = true → v2 = true := by rw [hv1, hv2, hbeq]; exact id
        have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
        simp only [notCodeFrom, hnotT, ↓reduceIte, evalWires, List.foldl_cons] at hih ⊢
        rw [hbit]
        exact ⟨Nat.add_le_add_left hih.1 _, fun hex => Nat.add_lt_add_left (hih.2 hex) _⟩
      · have hb1F : b1 = false := by
          cases hb1 : b1 with
          | false => rfl
          | true => exact absurd (hb_le hb1).symm (by rw [hb1] at hbeq; exact hbeq)
        have hb2T : b2 = true := by
          cases hb2 : b2 with
          | true => rfl
          | false => exact absurd (hb1F.trans hb2.symm) hbeq
        have hbit1 : notInBit w1 g = 0 := by unfold notInBit; change (if b1 then 1 else 0) = 0; rw [hb1F]; rfl
        have hbit2 : notInBit w2 g = 1 := by unfold notInBit; change (if b2 then 1 else 0) = 1; rw [hb2T]; rfl
        have hlt1 := notCodeFrom_lt gs w1'
        have hstrict : notCodeFrom w1 (g :: gs) < notCodeFrom w2 (g :: gs) := by
          simp only [notCodeFrom, hnotT, ↓reduceIte, hbit1, hbit2, zero_mul, zero_add, one_mul]
          dsimp only [w1', v1] at hlt1
          omega
        exact ⟨le_of_lt hstrict, fun _ => hstrict⟩

lemma inpVec_le_of_subset {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) :
    (inpVec n u).length = (inpVec n v).length ∧
    ∀ i : ℕ, (inpVec n u).getD i false = true → (inpVec n v).getD i false = true := by
  refine ⟨by rw [inpVec_length, inpVec_length], ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [inpVec_getD_lt n u ⟨i, hin⟩, decide_eq_true_eq] at hi
    rw [inpVec_getD_lt n v ⟨i, hin⟩, decide_eq_true_eq]
    exact huv hi
  · by_cases him : i = n
    · rw [him, inpVec_getD_m n u] at hi; cases hi
    · by_cases him1 : i = n + 1
      · rw [him1]; exact inpVec_getD_m1 n v
      · have hnone : (inpVec n u).getD i false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [inpVec_length]; omega)]; rfl
        rw [hnone] at hi; cases hi

lemma notCnt_eq_notCount (C : Circuit) : notCnt C.gates = PEqualNP.NotBracket.notCount C := by
  unfold notCnt PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> rfl

open Classical in
lemma exists_and_finset {d : ℕ} (s : Finset (Fin d)) (gs : List Gate) (hgs : GateOK (d + 2) gs) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK (d + 2) gs' ∧ notCnt gs' = notCnt gs ∧
      w < d + 2 + gs'.length ∧
      ∀ u : Finset (Fin d), wVal gs' (inpVec d u) w = decide (s ⊆ u) := by
  induction s using Finset.induction_on generalizing gs with
  | empty =>
    refine ⟨gs, d + 1, Extends.refl gs, hgs, rfl, by omega, ?_⟩
    intro u
    rw [evalWires_input gs (inpVec d u) (by rw [inpVec_length]; omega), inpVec_getD_m1]
    simp
  | insert i s' hi ih =>
    obtain ⟨gs1, w1, hext1, hgs1, hnc1, hw1, hev1⟩ := ih gs hgs
    obtain ⟨gs2, w2, hext2, hgs2, hnc2, _, hw2, hev2⟩ :=
      mkAnd_ex hgs1 (by omega : i.val < d + 2 + gs1.length) hw1
    refine ⟨gs2, w2, hext1.trans hext2, hgs2, hnc2.trans hnc1, hw2, ?_⟩
    intro u
    rw [hev2 (inpVec d u) (inpVec_length d u),
      evalWires_input gs1 (inpVec d u) (by rw [inpVec_length]; omega),
      inpVec_getD_lt d u i, hev1 u]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.insert_subset_iff]

open Classical in
lemma exists_or_monotone {d : ℕ} (F : Finset (Finset (Fin d))) (gs : List Gate) (hgs : GateOK (d + 2) gs) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK (d + 2) gs' ∧ notCnt gs' = notCnt gs ∧
      w < d + 2 + gs'.length ∧
      ∀ u : Finset (Fin d), wVal gs' (inpVec d u) w = decide (∃ s ∈ F, s ⊆ u) := by
  induction F using Finset.induction_on generalizing gs with
  | empty =>
    refine ⟨gs, d, Extends.refl gs, hgs, rfl, by omega, ?_⟩
    intro u
    rw [evalWires_input gs (inpVec d u) (by rw [inpVec_length]; omega), inpVec_getD_m]
    simp
  | insert s F' hs ih =>
    obtain ⟨gs1, w1, hext1, hgs1, hnc1, hw1, hev1⟩ := ih gs hgs
    obtain ⟨gs2, w2, hext2, hgs2, hnc2, hw2, hev2⟩ := exists_and_finset s gs1 hgs1
    have hw1_2 : w1 < d + 2 + gs2.length := by have := hext2.length_le; omega
    obtain ⟨gs3, w3, hext3, hgs3, hnc3, _, hw3, hev3⟩ := mkOr_ex hgs2 hw1_2 hw2
    refine ⟨gs3, w3, hext1.trans (hext2.trans hext3), hgs3, hnc3.trans (hnc2.trans hnc1), hw3, ?_⟩
    intro u
    rw [hev3 (inpVec d u) (inpVec_length d u),
      hext2.wVal_eq (inpVec d u) (by rw [inpVec_length]; omega), hev1 u, hev2 u]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
    constructor
    · rintro (⟨s0, hs0, hsub⟩ | hsub)
      · exact ⟨s0, Or.inr hs0, hsub⟩
      · exact ⟨s, Or.inl rfl, hsub⟩
    · rintro ⟨s0, rfl | hs0, hsub⟩
      · exact Or.inr hsub
      · exact Or.inl ⟨s0, hs0, hsub⟩

open Classical in
lemma exists_monotone_wire {d : ℕ} (P : Finset (Fin d) → Prop)
    (hmono : ∀ u v : Finset (Fin d), u ⊆ v → P u → P v)
    (gs : List Gate) (hgs : GateOK (d + 2) gs) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK (d + 2) gs' ∧ notCnt gs' = notCnt gs ∧
      w < d + 2 + gs'.length ∧
      ∀ u : Finset (Fin d), wVal gs' (inpVec d u) w = decide (P u) := by
  let F : Finset (Finset (Fin d)) := Finset.univ.filter fun s => P s
  obtain ⟨gs', w, hext, hgs', hnc, hw, hev⟩ := exists_or_monotone F gs hgs
  refine ⟨gs', w, hext, hgs', hnc, hw, ?_⟩
  intro u
  rw [hev u]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, F, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨s, hs, hsub⟩ => hmono s u hsub hs, fun hu => ⟨u, hu, Finset.Subset.refl u⟩⟩

lemma exists_list_build_unbounded {M : ℕ} (len : ℕ) (gs0 : List Gate)
    (P : ℕ → List Gate → ℕ → Prop)
    (hmono : ∀ i < len, ∀ gs1 gs2 w, w < M + gs1.length → Extends gs1 gs2 → P i gs1 w → P i gs2 w)
    (hstep : ∀ i < len, ∀ gs, Extends gs0 gs → GateOK M gs →
      ∃ gs' w, Extends gs gs' ∧ GateOK M gs' ∧ notCnt gs' = notCnt gs ∧
        w < M + gs'.length ∧ P i gs' w)
    (hgs0 : GateOK M gs0) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      Extends gs0 gs' ∧ GateOK M gs' ∧ notCnt gs' = notCnt gs0 ∧
      ws.length = len ∧ (∀ w ∈ ws, w < M + gs'.length) ∧
      ∀ i < len, P i gs' (ws.getD i 0) := by
  have haux : ∀ k ≤ len,
      ∃ (gs' : List Gate) (ws : List ℕ),
        Extends gs0 gs' ∧ GateOK M gs' ∧ notCnt gs' = notCnt gs0 ∧
        ws.length = k ∧ (∀ w ∈ ws, w < M + gs'.length) ∧
        ∀ i < k, P i gs' (ws.getD i 0) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨gs0, [], Extends.refl gs0, hgs0, rfl, rfl, by simp, fun _ hi => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨gs1, ws1, hext1, hgs1, hnc1, hwl1, hwsW1, hP1⟩ := ih (by omega)
      obtain ⟨gs2, w, hext2, hgs2, hnc2, hw2, hPw⟩ := hstep k (by omega) gs1 hext1 hgs1
      refine ⟨gs2, ws1 ++ [w], hext1.trans hext2, hgs2, hnc2.trans hnc1, by simp [hwl1], ?_, ?_⟩
      · intro u hu
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hu | rfl
        · have := hext2.length_le; have := hwsW1 u hu; omega
        · exact hw2
      · intro i hi
        by_cases hik : i < k
        · have hgt : (ws1 ++ [w]).getD i 0 = ws1.getD i 0 := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < ws1.length)]
          have hm : ws1.getD i 0 ∈ ws1 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
          rw [hgt]
          exact hmono i (by omega) gs1 gs2 _ (hwsW1 _ hm) hext2 (hP1 i hik)
        · have hieq : i = k := by omega
          rw [hieq]
          have hgt : (ws1 ++ [w]).getD k 0 = w := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ws1.length ≤ k)]
            simp [hwl1]
          rw [hgt]; exact hPw
  exact haux len le_rfl

open Classical in
lemma exists_circuit_of_level {d t k : ℕ}
    (dom : Finset (Finset (Fin d)))
    (L : Finset (Fin d) → ℕ) (f : Finset (Fin d) → Finset (Fin t))
    (hLmono : ∀ u v : Finset (Fin d), u ⊆ v → L u ≤ L v)
    (hLlt : ∀ u : Finset (Fin d), L u < 2 ^ k)
    (hcons : ∀ u ∈ dom, ∀ v ∈ dom, u ⊆ v → L u = L v → f u ⊆ f v) :
    ∃ (C : Circuit) (tap : Fin t → ℕ),
      GateOK (d + 2) C.gates ∧ C.output < d + 2 + C.gates.length ∧
      (∀ a : Fin t, tap a < d + 2 + C.gates.length) ∧
      notCnt C.gates = k ∧
      ∀ u ∈ dom, (Finset.univ.filter fun a : Fin t =>
        wVal C.gates (inpVec d u) (tap a) = true) = f u := by
  let M := d + 2
  let wF := d
  let wT := d + 1

  obtain ⟨gs1, T, _, hgs1, hnc1, hTl, hTW, hT_ev⟩ :=
    exists_list_build_unbounded (M := M) (2 ^ k) []
      (fun r gsX w => ∀ u : Finset (Fin d), wVal gsX (inpVec d u) w = decide (r ≤ L u))
      (fun _ _ gsA gsB w hw hext hP u => by
        rw [hext.wVal_eq (inpVec d u) (by rw [inpVec_length]; exact hw)]; exact hP u)
      (fun r _ gsA _ hgsA => by
        obtain ⟨gsB, w, hx, hg, hn, hw, hev⟩ :=
          exists_monotone_wire (fun u => r ≤ L u) (fun u v huv hr => le_trans hr (hLmono u v huv)) gsA hgsA
        exact ⟨gsB, w, hx, hg, hn, hw, fun u => by rw [hev u]; apply Bool.eq_iff_iff.2; simp⟩)
      (GateOK_nil M)

  obtain ⟨gs2, eqL, hext12, hgs2, hnc2, _, heqLl, heqLW, heqL_ev⟩ :=
    exists_b_decoder_aux k wF wT (by dsimp only [wF, M]; omega) (by dsimp only [wT, M]; omega)
      T hTl k le_rfl gs1 hgs1 hTW
  have heqL_spec : ∀ (u : Finset (Fin d)) (l : ℕ), l < 2 ^ k →
      wVal gs2 (inpVec d u) (eqL.getD l 0) = decide (L u = l) := by
    intro u l hl
    have h := heqL_ev (inpVec d u) (L u) (inpVec_length d u)
      (inpVec_getD_m d u) (inpVec_getD_m1 d u) (hLlt u)
      (fun r _ hrb => hT_ev r hrb u) l hl
    simpa using h

  have hbuild_tap : ∀ (a : Fin t) (cnt : ℕ) (_hcnt : cnt ≤ 2 ^ k) (gsA : List Gate),
      Extends gs2 gsA → GateOK M gsA →
      ∃ (gsB : List Gate) (w : ℕ),
        Extends gsA gsB ∧ GateOK M gsB ∧ notCnt gsB = notCnt gsA ∧
        w < M + gsB.length ∧
        ∀ u : Finset (Fin d), wVal gsB (inpVec d u) w =
          decide (∃ l < cnt, L u = l ∧ ∃ u0 ∈ dom, u0 ⊆ u ∧ L u0 = l ∧ a ∈ f u0) := by
    intro a cnt
    induction cnt with
    | zero =>
      intro _ gsA _ hgsA
      refine ⟨gsA, wF, Extends.refl gsA, hgsA, rfl, by dsimp only [wF, M]; omega, ?_⟩
      intro u
      rw [evalWires_input gsA (inpVec d u) (by rw [inpVec_length]; dsimp only [wF]; omega), inpVec_getD_m]
      simp
    | succ cnt ih =>
      intro hcnt gsA hext2A hgsA
      obtain ⟨gsB1, acc, hextAB1, hgsB1, hncB1, haccW, hacc_ev⟩ := ih (by omega) gsA hext2A hgsA
      obtain ⟨gsB2, mw, hext12', hgsB2, hncB2, hmwW, hmw_ev⟩ :=
        exists_monotone_wire (fun u => ∃ u0 ∈ dom, u0 ⊆ u ∧ L u0 = cnt ∧ a ∈ f u0)
          (fun u v huv ⟨u0, hu0, hsub, hL0, haf⟩ => ⟨u0, hu0, hsub.trans huv, hL0, haf⟩) gsB1 hgsB1
      have heq_m : eqL.getD cnt 0 ∈ eqL := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      have hext2_B2 : Extends gs2 gsB2 := (hext2A.trans hextAB1).trans hext12'
      have heq_B2 : eqL.getD cnt 0 < M + gsB2.length := by
        have := hext2_B2.length_le; have := heqLW _ heq_m; omega
      obtain ⟨gsB3, wa, hx3, hgsB3, hncB3, _, hwaW, hev3⟩ := mkAnd_ex hgsB2 heq_B2 hmwW
      have hacc_B3 : acc < M + gsB3.length := by
        have := (hext12'.trans hx3).length_le; omega
      obtain ⟨gsB4, wo, hx4, hgsB4, hncB4, _, hwoW, hev4⟩ := mkOr_ex hgsB3 hacc_B3 hwaW
      refine ⟨gsB4, wo, hextAB1.trans (hext12'.trans (hx3.trans hx4)), hgsB4,
        hncB4.trans (hncB3.trans (hncB2.trans hncB1)), hwoW, ?_⟩
      intro u
      have hinp := inpVec_length d u
      rw [hev4 (inpVec d u) hinp,
        (hext12'.trans hx3).wVal_eq (inpVec d u) (by rw [hinp]; exact haccW),
        hev3 (inpVec d u) hinp, hacc_ev u,
        hext2_B2.wVal_eq (inpVec d u) (by rw [hinp]; exact heqLW _ heq_m),
        heqL_spec u cnt (by omega), hmw_ev u]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨l, hl, hLu, hex⟩ | ⟨hLu, hex⟩)
        · exact ⟨l, by omega, hLu, hex⟩
        · exact ⟨cnt, by omega, hLu, hex⟩
      · rintro ⟨l, hl, hLu, hex⟩
        by_cases hlc : l < cnt
        · exact Or.inl ⟨l, hlc, hLu, hex⟩
        · have hleq : l = cnt := by omega
          rw [hleq] at hLu hex
          exact Or.inr ⟨hLu, hex⟩
  obtain ⟨gs3, taps, hext23, hgs3, hnc3, htapsL, htapsW, htaps_ev⟩ :=
    exists_list_build_unbounded (M := M) t gs2
      (fun a gsX w => ∀ (ha : a < t) (u : Finset (Fin d)), wVal gsX (inpVec d u) w =
        decide (∃ l < 2 ^ k, L u = l ∧ ∃ u0 ∈ dom, u0 ⊆ u ∧ L u0 = l ∧ ⟨a, ha⟩ ∈ f u0))
      (fun _ _ gsA gsB w hw hext hP ha u => by
        rw [hext.wVal_eq (inpVec d u) (by rw [inpVec_length]; exact hw)]; exact hP ha u)
      (fun a ha gsA hext2A hgsA => by
        obtain ⟨gsB, w, hextAB, hgsB, hncB, hwB, hevB⟩ := hbuild_tap ⟨a, ha⟩ (2 ^ k) le_rfl gsA hext2A hgsA
        exact ⟨gsB, w, hextAB, hgsB, hncB, hwB, fun _ u => hevB u⟩)
      hgs2
  have hnc_tot : notCnt gs3 = k := by
    have h0 : notCnt ([] : List Gate) = 0 := rfl
    rw [hnc3, hnc2, hnc1, h0]; omega
  refine ⟨⟨gs3, wF⟩, fun a => taps.getD a.val 0, hgs3, by dsimp only [wF, M]; omega, ?_, hnc_tot, ?_⟩
  · intro a
    have hm : taps.getD a.val 0 ∈ taps := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
    exact htapsW _ hm
  · intro u hu
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [htaps_ev a.val a.isLt a.isLt u, decide_eq_true_eq]
    constructor
    · rintro ⟨l, _, hLu, u0, hu0, hsub, hLu0, haf⟩
      exact hcons u0 hu0 u hu hsub (hLu0.trans hLu.symm) haf
    · intro haf
      exact ⟨L u, hLlt u, rfl, u, hu, Finset.Subset.refl u, rfl, haf⟩

def copyMask {n m p : ℕ} (x : Fin m → Finset (Fin n)) (ia : Fin (2 ^ p) × Fin m) :
    Finset (Fin (2 ^ p * (n + 1))) :=
  Finset.univ.filter fun u : Fin (2 ^ p * (n + 1)) =>
    u.val / (n + 1) < ia.1.val ∨
    (u.val / (n + 1) = ia.1.val ∧ ∃ hlt : u.val % (n + 1) < n, ⟨u.val % (n + 1), hlt⟩ ∈ x ia.2)

lemma copyMask_subset_iff {n m p : ℕ} (x : Fin m → Finset (Fin n))
    (i j : Fin (2 ^ p)) (a b : Fin m) :
    copyMask (p := p) x (i, a) ⊆ copyMask (p := p) x (j, b) ↔ i < j ∨ (i = j ∧ x a ⊆ x b) := by
  constructor
  · intro hsub
    have hij_le : i.val ≤ j.val := by
      by_contra hlt
      have hjlt : j.val < i.val := by omega
      have hu_lt : j.val * (n + 1) + n < 2 ^ p * (n + 1) := by
        have h1 : (j.val + 1) * (n + 1) ≤ 2 ^ p * (n + 1) :=
          Nat.mul_le_mul_right (n + 1) (by omega)
        nlinarith
      let u : Fin (2 ^ p * (n + 1)) := ⟨j.val * (n + 1) + n, hu_lt⟩
      have hdiv : u.val / (n + 1) = j.val := by
        dsimp only [u]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n + 1), Nat.div_eq_of_lt (by omega)]
        omega
      have hmod : u.val % (n + 1) = n := by
        dsimp only [u]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hmem1 : u ∈ copyMask (p := p) x (i, a) := by
        simp only [copyMask, Finset.mem_filter, Finset.mem_univ, true_and]
        left; rw [hdiv]; exact hjlt
      have hmem2 := hsub hmem1
      simp only [copyMask, Finset.mem_filter, Finset.mem_univ, true_and, hdiv, hmod] at hmem2
      rcases hmem2 with h1 | ⟨h2, _⟩ <;> omega
    by_cases hij : i.val < j.val
    · left; exact hij
    · right
      have heq : i = j := Fin.ext (by omega)
      refine ⟨heq, ?_⟩
      intro r hr
      have hu_lt : i.val * (n + 1) + r.val < 2 ^ p * (n + 1) := by
        have h1 : (i.val + 1) * (n + 1) ≤ 2 ^ p * (n + 1) :=
          Nat.mul_le_mul_right (n + 1) (by omega)
        nlinarith [r.isLt]
      let u : Fin (2 ^ p * (n + 1)) := ⟨i.val * (n + 1) + r.val, hu_lt⟩
      have hdiv : u.val / (n + 1) = i.val := by
        dsimp only [u]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n + 1), Nat.div_eq_of_lt (by omega)]
        omega
      have hmod : u.val % (n + 1) = r.val := by
        dsimp only [u]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hmem1 : u ∈ copyMask (p := p) x (i, a) := by
        simp only [copyMask, Finset.mem_filter, Finset.mem_univ, true_and, hdiv]
        right
        refine ⟨by rw [hmod]; exact r.isLt, ?_⟩
        convert hr using 1; exact Fin.ext hmod
      have hmem2 := hsub hmem1
      rw [← heq] at hmem2
      simp only [copyMask, Finset.mem_filter, Finset.mem_univ, true_and, hdiv] at hmem2
      rcases hmem2 with h1 | ⟨_, hr'⟩
      · omega
      · convert hr' using 1; exact Fin.ext hmod.symm
  · intro h u hu
    simp only [copyMask, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rcases h with hij | ⟨rfl, hsub⟩
    · left
      rcases hu with h1 | ⟨h1, _⟩
      · exact lt_trans h1 hij
      · rw [h1]; exact hij
    · rcases hu with h1 | ⟨h1, hlt, hm⟩
      · left; exact h1
      · right; exact ⟨h1, hlt, hsub hm⟩

lemma copyMask_injective {n m p : ℕ} {x : Fin m → Finset (Fin n)} (hx : Function.Injective x) :
    Function.Injective (copyMask (p := p) x) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ heq
  have h1 := (copyMask_subset_iff x i j a b).1 (le_of_eq heq)
  have h2 := (copyMask_subset_iff x j i b a).1 (le_of_eq heq.symm)
  rcases h1 with hij | ⟨rfl, hab⟩
  · rcases h2 with hji | ⟨rfl, _⟩
    · exact absurd (lt_trans hij hji) (lt_irrefl _)
    · exact absurd hij (lt_irrefl _)
  · rcases h2 with hji | ⟨_, hba⟩
    · exact absurd hji (lt_irrefl _)
    · exact Prod.ext rfl (hx (Finset.Subset.antisymm hab hba))

open Classical in
lemma L_lib_1315_core :
    ∀ (n m p : Nat) (x : Fin m → Finset (Fin n)), Function.Injective x →
      let q := 2 ^ p
      let N := q * (n + 1)
      ∃ y : Fin q × Fin m → Finset (Fin N), Function.Injective y ∧
        (∀ (i j : Fin q) (a b : Fin m), y (i, a) ⊆ y (j, b) ↔ i < j ∨ (i = j ∧ x a ⊆ x b)) ∧
        ∀ t s : Nat,
          let fits := fun (I : Type) (d k : Nat) (z : I → Finset (Fin d))
            (A : I → Finset (Finset (Fin t))) (keep : I → Prop) =>
              ∃ (C : Circuit) (tap : Fin t → Nat),
                PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C ∧
                C.output < d + 2 + C.size ∧ (∀ a, tap a < d + 2 + C.size) ∧ PEqualNP.NotBracket.notCount C ≤ k ∧
                ∀ i, keep i → (Finset.univ.filter (fun a =>
                  (C.wires (inpVec d (z i))).getD (tap a) false = true)) ∈ A i
          ∀ (A : Fin q → Fin m → Finset (Finset (Fin t))) (keep : Fin q → Fin m → Prop),
            let each := fun i => fits (Fin m) n s x (A i) (keep i)
            let allFit := fits (Fin q × Fin m) N (s + p) y (fun z => A z.1 z.2) (fun z => keep z.1 z.2)
            ((∀ i, each i) → allFit) ∧ (allFit → ∃ i, each i) := by
  intro n m p x hx q N
  let y := copyMask (p := p) x
  refine ⟨y, copyMask_injective hx, copyMask_subset_iff x, ?_⟩
  intro t s fits A keep each allFit
  have h2sp : 2 ^ (s + p) = q * 2 ^ s := by
    dsimp only [q]; rw [pow_add, Nat.mul_comm]
  constructor

  · intro hall
    choose C tap hCf hCr hCo htap hCnot hCmem using hall
    have hCnot' : ∀ i : Fin q, notCnt (C i).gates ≤ s := fun i => by
      rw [notCnt_eq_notCount (C i)]; exact hCnot i
    let Li : Fin q → Finset (Fin n) → ℕ := fun i u => notCodeFrom (inpVec n u) (C i).gates
    have hLi_lt : ∀ i u, Li i u < 2 ^ s := fun i u =>
      lt_of_lt_of_le (notCodeFrom_lt (C i).gates (inpVec n u))
        (Nat.pow_le_pow_right (by omega) (hCnot' i))
    have hLi_mono : ∀ i u v, u ⊆ v → Li i u ≤ Li i v := fun i u v huv =>
      (notCodeFrom_mono_and_fall (C i).gates (fun g hg => (hCf i g hg).1)
        (inpVec n u) (inpVec n v) (by rw [inpVec_length, inpVec_length]) (inpVec_le_of_subset huv).2).1
    let fi : Fin q → Finset (Fin n) → Finset (Fin t) := fun i u =>
      Finset.univ.filter fun c => wVal (C i).gates (inpVec n u) (tap i c) = true
    have hfi_cons : ∀ i u v, u ⊆ v → Li i u = Li i v → fi i u ⊆ fi i v := by
      intro i u v huv hLeq c hc
      simp only [fi, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      by_contra hnf
      have hfalse : wVal (C i).gates (inpVec n v) (tap i c) = false := by
        cases h : wVal (C i).gates (inpVec n v) (tap i c) <;> simp_all
      have hlt := (notCodeFrom_mono_and_fall (C i).gates (fun g hg => (hCf i g hg).1)
        (inpVec n u) (inpVec n v) (by rw [inpVec_length, inpVec_length]) (inpVec_le_of_subset huv).2).2
        ⟨tap i c, hc, hfalse⟩
      exact absurd hLeq (ne_of_lt hlt)
    let L : Finset (Fin N) → ℕ := fun u =>
      ((Finset.univ : Finset (Fin q × Fin m)).filter fun z => y z ⊆ u).sup fun z =>
        z.1.val * 2 ^ s + Li z.1 (x z.2)
    have hL_mono : ∀ u v : Finset (Fin N), u ⊆ v → L u ≤ L v := by
      intro u v huv
      apply Finset.sup_mono
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.trans huv
    have hL_lt : ∀ u : Finset (Fin N), L u < 2 ^ (s + p) := by
      intro u
      rw [h2sp]
      have hpos : 0 < q * 2 ^ s := Nat.mul_pos (Nat.two_pow_pos p) (Nat.two_pow_pos s)
      have hle : L u ≤ q * 2 ^ s - 1 := by
        apply Finset.sup_le
        intro z _
        have h1 := hLi_lt z.1 (x z.2)
        have h2 : (z.1.val + 1) * 2 ^ s ≤ q * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) (by omega)
        have hlt : z.1.val * 2 ^ s + Li z.1 (x z.2) < q * 2 ^ s := by nlinarith
        omega
      omega
    have hL_at : ∀ (i : Fin q) (a : Fin m), L (y (i, a)) = i.val * 2 ^ s + Li i (x a) := by
      intro i a
      apply le_antisymm
      · apply Finset.sup_le
        rintro ⟨j, b⟩ hjb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjb
        rcases (copyMask_subset_iff x j i b a).1 hjb with hlt | ⟨rfl, hsub⟩
        · have h1 := hLi_lt j (x b)
          have h2 : (j.val + 1) * 2 ^ s ≤ i.val * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) (by omega)
          dsimp only; nlinarith
        · have := hLi_mono j (x b) (x a) hsub
          dsimp only; omega
      · exact Finset.le_sup (f := fun z : Fin q × Fin m => z.1.val * 2 ^ s + Li z.1 (x z.2))
          (Finset.mem_filter.2 ⟨Finset.mem_univ (i, a), Finset.Subset.refl _⟩)
    let dom : Finset (Finset (Fin N)) := Finset.univ.image y
    let fAll : Finset (Fin N) → Finset (Fin t) := fun u =>
      if h : ∃ z : Fin q × Fin m, y z = u then fi (Classical.choose h).1 (x (Classical.choose h).2) else ∅
    have hfAll_at : ∀ z : Fin q × Fin m, fAll (y z) = fi z.1 (x z.2) := by
      intro z
      have hex : ∃ z' : Fin q × Fin m, y z' = y z := ⟨z, rfl⟩
      dsimp only [fAll]
      simp only [hex, ↓reduceDIte]
      have heq := copyMask_injective hx (Classical.choose_spec hex)
      rw [heq]
    have hfAll_cons : ∀ u ∈ dom, ∀ v ∈ dom, u ⊆ v → L u = L v → fAll u ⊆ fAll v := by
      intro u hu v hv huv hLeq
      rcases Finset.mem_image.1 hu with ⟨⟨i, a⟩, _, rfl⟩
      rcases Finset.mem_image.1 hv with ⟨⟨j, b⟩, _, rfl⟩
      rw [hfAll_at (i, a), hfAll_at (j, b)]
      rw [hL_at i a, hL_at j b] at hLeq
      rcases (copyMask_subset_iff x i j a b).1 huv with hlt | ⟨rfl, hsub⟩
      · exfalso
        have h1 := hLi_lt i (x a)
        have h2 : (i.val + 1) * 2 ^ s ≤ j.val * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) (by omega)
        nlinarith
      · exact hfi_cons i (x a) (x b) hsub (by omega)
    obtain ⟨Ctot, taptot, hCtotOK, hCtotO, htaptotW, hCtotNot, hCtotEv⟩ :=
      exists_circuit_of_level dom L fAll hL_mono hL_lt hfAll_cons
    refine ⟨Ctot, taptot, hCtotOK.1, hCtotOK.2, hCtotO, htaptotW,
      by rw [← notCnt_eq_notCount Ctot, hCtotNot], ?_⟩
    intro z hz
    have hmem : y z ∈ dom := Finset.mem_image.2 ⟨z, Finset.mem_univ z, rfl⟩
    have hev := hCtotEv (y z) hmem
    rw [hfAll_at z] at hev
    change (Finset.univ.filter fun a => wVal Ctot.gates (inpVec N (y z)) (taptot a) = true) ∈ A z.1 z.2
    rw [hev]
    exact hCmem z.1 z.2 hz

  · rintro ⟨C, tap, hCf, hCr, hCo, htapW, hCnot, hCmem⟩
    have hCnot' : notCnt C.gates ≤ s + p := by rw [notCnt_eq_notCount C]; exact hCnot
    let L : Finset (Fin N) → ℕ := fun u => notCodeFrom (inpVec N u) C.gates
    have hL_lt : ∀ u, L u < q * 2 ^ s := fun u => by
      rw [← h2sp]
      exact lt_of_lt_of_le (notCodeFrom_lt C.gates (inpVec N u))
        (Nat.pow_le_pow_right (by omega) hCnot')
    have hL_mono : ∀ u v, u ⊆ v → L u ≤ L v := fun u v huv =>
      (notCodeFrom_mono_and_fall C.gates (fun g hg => (hCf g hg).1)
        (inpVec N u) (inpVec N v) (by rw [inpVec_length, inpVec_length]) (inpVec_le_of_subset huv).2).1
    let outC : Finset (Fin N) → Finset (Fin t) := fun u =>
      Finset.univ.filter fun c => wVal C.gates (inpVec N u) (tap c) = true
    have hout_cons : ∀ u v, u ⊆ v → L u = L v → outC u ⊆ outC v := by
      intro u v huv hLeq c hc
      simp only [outC, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      by_contra hnf
      have hfalse : wVal C.gates (inpVec N v) (tap c) = false := by
        cases h : wVal C.gates (inpVec N v) (tap c) <;> simp_all
      have hlt := (notCodeFrom_mono_and_fall C.gates (fun g hg => (hCf g hg).1)
        (inpVec N u) (inpVec N v) (by rw [inpVec_length, inpVec_length]) (inpVec_le_of_subset huv).2).2
        ⟨tap c, hc, hfalse⟩
      exact absurd hLeq (ne_of_lt hlt)
    by_contra hnone
    push Not at hnone
    let Si : Fin q → Finset (Fin m) := fun i => Finset.univ.filter fun a => keep i a
    have hSi_ne : ∀ i : Fin q, (Si i).Nonempty := by
      intro i
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      apply hnone i
      refine ⟨⟨[], 0⟩, fun _ => 0, (GateOK_nil (n + 2)).1, (GateOK_nil (n + 2)).2,
        by simp [Circuit.size], fun _ => by simp [Circuit.size], by simp [PEqualNP.NotBracket.notCount], ?_⟩
      intro a hka
      have : a ∈ Si i := Finset.mem_filter.2 ⟨Finset.mem_univ a, hka⟩
      rw [hem] at this; exact absurd this (Finset.notMem_empty a)
    have hspan : ∀ i : Fin q, ∃ a ∈ Si i, ∃ b ∈ Si i, L (y (i, a)) + 2 ^ s ≤ L (y (i, b)) := by
      intro i
      obtain ⟨a0, ha0, hmin⟩ := Finset.exists_min_image (Si i) (fun a => L (y (i, a))) (hSi_ne i)
      obtain ⟨b0, hb0, hmax⟩ := Finset.exists_max_image (Si i) (fun a => L (y (i, a))) (hSi_ne i)
      by_contra hsmall
      push Not at hsmall
      have hlt_s : L (y (i, b0)) < L (y (i, a0)) + 2 ^ s := hsmall a0 ha0 b0 hb0
      let lo := L (y (i, a0))
      let L' : Finset (Fin n) → ℕ := fun u =>
        ((Si i).filter fun a => x a ⊆ u).sup fun a => L (y (i, a)) - lo
      have hL'_mono : ∀ u v : Finset (Fin n), u ⊆ v → L' u ≤ L' v := by
        intro u v huv
        apply Finset.sup_mono
        intro a ha
        simp only [Finset.mem_filter] at ha ⊢
        exact ⟨ha.1, ha.2.trans huv⟩
      have hL'_lt : ∀ u : Finset (Fin n), L' u < 2 ^ s := by
        intro u
        have h2s : 1 ≤ 2 ^ s := Nat.one_le_two_pow
        have hle : L' u ≤ L (y (i, b0)) - lo := by
          apply Finset.sup_le
          intro a ha
          have haS : a ∈ Si i := (Finset.mem_filter.1 ha).1
          have := hmax a haS
          omega
        omega
      have hL'_at : ∀ a ∈ Si i, L' (x a) = L (y (i, a)) - lo := by
        intro a ha
        apply le_antisymm
        · apply Finset.sup_le
          intro b hb
          simp only [Finset.mem_filter] at hb
          have hsub : y (i, b) ⊆ y (i, a) := (copyMask_subset_iff x i i b a).2 (Or.inr ⟨rfl, hb.2⟩)
          have := hL_mono _ _ hsub
          omega
        · exact Finset.le_sup (f := fun b : Fin m => L (y (i, b)) - lo)
            (Finset.mem_filter.2 ⟨ha, Finset.Subset.refl _⟩)
      let domi : Finset (Finset (Fin n)) := (Si i).image x
      let fi : Finset (Fin n) → Finset (Fin t) := fun u =>
        if h : ∃ a : Fin m, x a = u then outC (y (i, Classical.choose h)) else ∅
      have hfi_at : ∀ a : Fin m, fi (x a) = outC (y (i, a)) := by
        intro a
        have hex : ∃ a' : Fin m, x a' = x a := ⟨a, rfl⟩
        dsimp only [fi]
        simp only [hex, ↓reduceDIte]
        rw [hx (Classical.choose_spec hex)]
      have hfi_cons : ∀ u ∈ domi, ∀ v ∈ domi, u ⊆ v → L' u = L' v → fi u ⊆ fi v := by
        intro u hu v hv huv hLeq
        rcases Finset.mem_image.1 hu with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.1 hv with ⟨b, hb, rfl⟩
        rw [hfi_at a, hfi_at b]
        rw [hL'_at a ha, hL'_at b hb] at hLeq
        have hlo_a : lo ≤ L (y (i, a)) := hmin a ha
        have hlo_b : lo ≤ L (y (i, b)) := hmin b hb
        have hLeq' : L (y (i, a)) = L (y (i, b)) := by omega
        have hsub : y (i, a) ⊆ y (i, b) := (copyMask_subset_iff x i i a b).2 (Or.inr ⟨rfl, huv⟩)
        exact hout_cons _ _ hsub hLeq'
      obtain ⟨Ci, tapi, hCiOK, hCiO, htapiW, hCiNot, hCiEv⟩ :=
        exists_circuit_of_level domi L' fi hL'_mono hL'_lt hfi_cons
      apply hnone i
      refine ⟨Ci, tapi, hCiOK.1, hCiOK.2, hCiO, htapiW,
        by rw [← notCnt_eq_notCount Ci, hCiNot], ?_⟩
      intro a hka
      have haS : a ∈ Si i := Finset.mem_filter.2 ⟨Finset.mem_univ a, hka⟩
      have hmem : x a ∈ domi := Finset.mem_image.2 ⟨a, haS, rfl⟩
      have hev := hCiEv (x a) hmem
      rw [hfi_at a] at hev
      change (Finset.univ.filter fun c => wVal Ci.gates (inpVec n (x a)) (tapi c) = true) ∈ A i a
      rw [hev]
      exact hCmem (i, a) hka

    have hchain : ∀ r (hr : r < q), ∃ b ∈ Si ⟨r, hr⟩, (r + 1) * 2 ^ s ≤ L (y (⟨r, hr⟩, b)) := by
      intro r
      induction r with
      | zero =>
        intro hr
        obtain ⟨a, _, b, hb, hge⟩ := hspan ⟨0, hr⟩
        exact ⟨b, hb, by omega⟩
      | succ r ih =>
        intro hr
        obtain ⟨bprev, _, hprev⟩ := ih (by omega)
        obtain ⟨a, _, b, hb, hge⟩ := hspan ⟨r + 1, hr⟩
        have hsub : y (⟨r, by omega⟩, bprev) ⊆ y (⟨r + 1, hr⟩, a) :=
          (copyMask_subset_iff x ⟨r, by omega⟩ ⟨r + 1, hr⟩ bprev a).2 (Or.inl (by simp))
        have hstep := hL_mono _ _ hsub
        refine ⟨b, hb, ?_⟩
        have hmul : (r + 1 + 1) * 2 ^ s = (r + 1) * 2 ^ s + 2 ^ s := by ring
        omega
    have hq_pos : 0 < q := Nat.two_pow_pos p
    obtain ⟨blast, _, hge⟩ := hchain (q - 1) (by omega)
    have hlt := hL_lt (y (⟨q - 1, by omega⟩, blast))
    have hqeq : q - 1 + 1 = q := by omega
    rw [hqeq] at hge
    omega

end PEqualNP.Outside.L_lib_1315_aux

theorem PEqualNP.Outside.L_lib_1315 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n m p : Nat) (x : Fin m → Finset (Fin n)), Function.Injective x →
      let q := 2^p
      let N := q*(n+1)
      ∃ y : Fin q × Fin m → Finset (Fin N), Function.Injective y ∧
        (∀ (i j : Fin q) (a b : Fin m), y (i,a) ⊆ y (j,b) ↔ i<j ∨ (i=j ∧ x a ⊆ x b)) ∧
        ∀ t s : Nat,
          let fits := fun (I : Type) (d k : Nat) (z : I → Finset (Fin d))
            (A : I → Finset (Finset (Fin t))) (keep : I → Prop) =>
              ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat),
                PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
                C.output < d+2+C.size ∧ (∀ a, tap a < d+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ k ∧
                ∀ i, keep i → (Finset.univ.filter (fun a =>
                  (C.wires (List.ofFn (fun j : Fin d => decide (j ∈ z i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i
          ∀ (A : Fin q → Fin m → Finset (Finset (Fin t))) (keep : Fin q → Fin m → Prop),
            let each := fun i => fits (Fin m) n s x (A i) (keep i)
            let allFit := fits (Fin q × Fin m) N (s+p) y (fun z => A z.1 z.2) (fun z => keep z.1 z.2)
            ((∀ i, each i) → allFit) ∧ (allFit → ∃ i, each i) := by
  dsimp only
  intro n m p x hx
  have hinp : ∀ (d : Nat) (u : Finset (Fin d)),
      (List.ofFn (fun j : Fin d => @decide (j ∈ u) (Classical.propDecidable _)) ++ [false, true]) =
        PEqualNP.Outside.L_lib_1315_aux.inpVec d u := by
    intro d u
    unfold PEqualNP.Outside.L_lib_1315_aux.inpVec
    congr 1
    apply List.ext_getElem (by simp)
    intro i _ _
    simp only [List.getElem_ofFn]
    apply Bool.eq_iff_iff.2; simp
  have hflt_eq : ∀ (t : Nat) (P : Fin t → Prop) (inst1 inst2 : DecidablePred P),
      @Finset.filter (Fin t) P inst1 Finset.univ = @Finset.filter (Fin t) P inst2 Finset.univ := by
    intro t P inst1 inst2
    ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hcore := PEqualNP.Outside.L_lib_1315_aux.L_lib_1315_core n m p x hx
  dsimp only at hcore
  rcases hcore with ⟨y, hyinj, hysub, hmain⟩
  refine ⟨y, hyinj, hysub, ?_⟩
  intro t s A keep
  have h := hmain t s A keep
  simpa only [hinp, hflt_eq t _ (fun a => Classical.propDecidable _) (fun a => Classical.decPred _ a)] using h
