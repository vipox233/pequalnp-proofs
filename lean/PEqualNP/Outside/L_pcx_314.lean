import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_314_aux

open PEqualNP.MetaComplexity

abbrev MGate := Bool × ℕ × ℕ

def mstep (w : List Bool) (g : MGate) : List Bool :=
  let l := w.getD g.2.1 false
  let r := w.getD g.2.2 false
  w ++ [if g.1 then l && r else l || r]

def dstep (w : List ℕ) (g : MGate) : List ℕ :=
  w ++ [max (w.getD g.2.1 0) (w.getD g.2.2 0) + 1]

noncomputable def msource {P : Type} [Fintype P] (a : P → Bool) : List Bool :=
  [false, true] ++ List.ofFn (fun j : Fin (Fintype.card P) => a ((Fintype.equivFin P).symm j))

noncomputable def mrun {P : Type} [Fintype P] (G : List MGate) (a : P → Bool) : List Bool :=
  G.foldl mstep (msource a)

def mdepths (N : ℕ) (G : List MGate) : List ℕ :=
  G.foldl dstep (List.replicate N 0)

def WellFormed (N : ℕ) (G : List MGate) : Prop :=
  ∀ i : Fin G.length, (G.get i).2.1 < N + i.val ∧ (G.get i).2.2 < N + i.val

def Extends (G1 G2 : List MGate) : Prop :=
  ∃ d, G2 = G1 ++ d

lemma extends_rfl (G : List MGate) : Extends G G := ⟨[], by simp⟩

lemma extends_trans {A B C : List MGate} (h1 : Extends A B) (h2 : Extends B C) : Extends A C := by
  rcases h1 with ⟨d1, rfl⟩
  rcases h2 with ⟨d2, rfl⟩
  exact ⟨d1 ++ d2, by simp [List.append_assoc]⟩

lemma extends_len {A B : List MGate} (h : Extends A B) : A.length ≤ B.length := by
  rcases h with ⟨d, rfl⟩; simp

lemma getD_append_left {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type} (l r : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    (l ++ r).getD i d = r.getD (i - l.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma foldl_mstep_len (G : List MGate) (base : List Bool) :
    (G.foldl mstep base).length = base.length + G.length := by
  induction G generalizing base with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, mstep, List.length_append, List.length_nil]
    omega

lemma foldl_dstep_len (G : List MGate) (base : List ℕ) :
    (G.foldl dstep base).length = base.length + G.length := by
  induction G generalizing base with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, dstep, List.length_append, List.length_nil]
    omega

lemma foldl_mstep_getD_lt (G : List MGate) (base : List Bool) (w : ℕ) (hw : w < base.length) :
    (G.foldl mstep base).getD w false = base.getD w false := by
  induction G generalizing base with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (mstep base g).length := by simp [mstep]; omega
    rw [ih (mstep base g) hw']
    exact getD_append_left base _ w false hw

lemma foldl_dstep_getD_lt (G : List MGate) (base : List ℕ) (w : ℕ) (hw : w < base.length) :
    (G.foldl dstep base).getD w 0 = base.getD w 0 := by
  induction G generalizing base with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (dstep base g).length := by simp [dstep]; omega
    rw [ih (dstep base g) hw']
    exact getD_append_left base _ w 0 hw

lemma msource_len {P : Type} [Fintype P] (a : P → Bool) :
    (msource a).length = 2 + Fintype.card P := by
  simp [msource]; omega

lemma mrun_of_extends {P : Type} [Fintype P] {G1 G2 : List MGate} (hext : Extends G1 G2)
    (a : P → Bool) (w : ℕ) (hw : w < 2 + Fintype.card P + G1.length) :
    (mrun G2 a).getD w false = (mrun G1 a).getD w false := by
  rcases hext with ⟨d, rfl⟩
  unfold mrun
  rw [List.foldl_append]
  have hlen : (G1.foldl mstep (msource a)).length = 2 + Fintype.card P + G1.length := by
    rw [foldl_mstep_len, msource_len]
  exact foldl_mstep_getD_lt d _ w (by omega)

lemma mdepths_of_extends {N : ℕ} {G1 G2 : List MGate} (hext : Extends G1 G2)
    (w : ℕ) (hw : w < N + G1.length) :
    (mdepths N G2).getD w 0 = (mdepths N G1).getD w 0 := by
  rcases hext with ⟨d, rfl⟩
  unfold mdepths
  rw [List.foldl_append]
  have hlen : (G1.foldl dstep (List.replicate N 0)).length = N + G1.length := by
    rw [foldl_dstep_len, List.length_replicate]
  exact foldl_dstep_getD_lt d _ w (by omega)

lemma mrun_const0 {P : Type} [Fintype P] (G : List MGate) (a : P → Bool) :
    (mrun G a).getD 0 false = false := by
  have h := mrun_of_extends (P := P) (G1 := []) (G2 := G) ⟨G, by simp⟩ a 0 (by simp)
  simpa [mrun, msource] using h

lemma mrun_const1 {P : Type} [Fintype P] (G : List MGate) (a : P → Bool) :
    (mrun G a).getD 1 false = true := by
  have h := mrun_of_extends (P := P) (G1 := []) (G2 := G) ⟨G, by simp⟩ a 1 (by simp; omega)
  simpa [mrun, msource] using h

lemma mrun_input {P : Type} [Fintype P] (G : List MGate) (a : P → Bool) (p : P) :
    (mrun G a).getD (2 + (Fintype.equivFin P p).val) false = a p := by
  have hlt : 2 + (Fintype.equivFin P p).val < 2 + Fintype.card P := by
    have := (Fintype.equivFin P p).isLt; omega
  have h := mrun_of_extends (P := P) (G1 := []) (G2 := G) ⟨G, by simp⟩ a
    (2 + (Fintype.equivFin P p).val) (by simp [hlt])
  rw [h]
  unfold mrun msource
  simp only [List.foldl_nil]
  rw [getD_append_right [false, true] _ _ false (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp

lemma mdepths_base {N : ℕ} (G : List MGate) (w : ℕ) (hw : w < N) :
    (mdepths N G).getD w 0 = 0 := by
  have h := mdepths_of_extends (N := N) (G1 := []) (G2 := G) ⟨G, by simp⟩ w (by simp [hw])
  rw [h]
  unfold mdepths
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hw])]
  simp

def addMGate (N : ℕ) (G : List MGate) (isAnd : Bool) (l r : ℕ) : List MGate × ℕ :=
  (G ++ [(isAnd, l, r)], N + G.length)

lemma addMGate_wf {N : ℕ} {G : List MGate} (hwf : WellFormed N G)
    (isAnd : Bool) {l r : ℕ} (hl : l < N + G.length) (hr : r < N + G.length) :
    WellFormed N (addMGate N G isAnd l r).1 := by
  intro i
  unfold addMGate at i ⊢
  have hilt : i.val < G.length + 1 := by simpa using i.isLt
  by_cases h1 : i.val < G.length
  · have hget : (G ++ [(isAnd, l, r)]).get i = G.get ⟨i.val, h1⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left h1]
    rw [hget]
    exact hwf ⟨i.val, h1⟩
  · have heq : i.val = G.length := by omega
    have hget : (G ++ [(isAnd, l, r)]).get i = (isAnd, l, r) := by
      simp [List.get_eq_getElem, heq]
    rw [hget, heq]
    exact ⟨hl, hr⟩

lemma addMGate_extends (N : ℕ) (G : List MGate) (isAnd : Bool) (l r : ℕ) :
    Extends G (addMGate N G isAnd l r).1 := ⟨[(isAnd, l, r)], rfl⟩

lemma addMGate_len (N : ℕ) (G : List MGate) (isAnd : Bool) (l r : ℕ) :
    (addMGate N G isAnd l r).1.length = G.length + 1 := by simp [addMGate]

lemma addMGate_out_lt (N : ℕ) (G : List MGate) (isAnd : Bool) (l r : ℕ) :
    (addMGate N G isAnd l r).2 < N + (addMGate N G isAnd l r).1.length := by simp [addMGate]

lemma addMGate_val {P : Type} [Fintype P] (G : List MGate) (isAnd : Bool) (l r : ℕ) (a : P → Bool) :
    (mrun (addMGate (2 + Fintype.card P) G isAnd l r).1 a).getD
      (addMGate (2 + Fintype.card P) G isAnd l r).2 false =
    if isAnd then (mrun G a).getD l false && (mrun G a).getD r false
    else (mrun G a).getD l false || (mrun G a).getD r false := by
  unfold addMGate mrun
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, mstep]
  have hlen : (G.foldl mstep (msource a)).length = 2 + Fintype.card P + G.length := by
    rw [foldl_mstep_len, msource_len]
  rw [getD_append_right _ _ _ false (by omega), hlen, Nat.sub_self, List.getD_cons_zero]

lemma addMGate_depth (N : ℕ) (G : List MGate) (isAnd : Bool) (l r : ℕ) :
    (mdepths N (addMGate N G isAnd l r).1).getD (addMGate N G isAnd l r).2 0 =
    max ((mdepths N G).getD l 0) ((mdepths N G).getD r 0) + 1 := by
  unfold addMGate mdepths
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, dstep]
  have hlen : (G.foldl dstep (List.replicate N 0)).length = N + G.length := by
    rw [foldl_dstep_len, List.length_replicate]
  rw [getD_append_right _ _ _ 0 (by omega), hlen, Nat.sub_self, List.getD_cons_zero]

def pairPass (isAnd : Bool) (N : ℕ) (G : List MGate) : List ℕ → List MGate × List ℕ
  | [] => (G, [])
  | [w] => (G, [w])
  | w1 :: w2 :: rest =>
    let r1 := addMGate N G isAnd w1 w2
    let r2 := pairPass isAnd N r1.1 rest
    (r2.1, r1.2 :: r2.2)

def evalList (isAnd : Bool) (f : ℕ → Bool) (ws : List ℕ) : Bool :=
  if isAnd then ws.all f else ws.any f

lemma evalList_congr (isAnd : Bool) {f g : ℕ → Bool} {ws : List ℕ}
    (h : ∀ w ∈ ws, f w = g w) : evalList isAnd f ws = evalList isAnd g ws := by
  unfold evalList
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction ws with
    | nil => rfl
    | cons a l ih =>
      simp only [List.any_cons, h a (by simp)]
      congr 1; exact ih (fun w hw => h w (by simp [hw]))
  · simp only [↓reduceIte]
    induction ws with
    | nil => rfl
    | cons a l ih =>
      simp only [List.all_cons, h a (by simp)]
      congr 1; exact ih (fun w hw => h w (by simp [hw]))

lemma pairPass_spec {P : Type} [Fintype P] (isAnd : Bool)
    (G : List MGate) (ws : List ℕ) (dmax : ℕ)
    (hwf : WellFormed (2 + Fintype.card P) G)
    (hbd : ∀ w ∈ ws, w < 2 + Fintype.card P + G.length)
    (hdep : ∀ w ∈ ws, (mdepths (2 + Fintype.card P) G).getD w 0 ≤ dmax) :
    let N := 2 + Fintype.card P
    let r := pairPass isAnd N G ws
    WellFormed N r.1 ∧ Extends G r.1 ∧
    r.1.length = G.length + ws.length / 2 ∧
    r.2.length = (ws.length + 1) / 2 ∧
    (∀ w ∈ r.2, w < N + r.1.length) ∧
    (∀ w ∈ r.2, (mdepths N r.1).getD w 0 ≤ dmax + 1) ∧
    (∀ a : P → Bool, evalList isAnd (fun w => (mrun r.1 a).getD w false) r.2 =
      evalList isAnd (fun w => (mrun G a).getD w false) ws) := by
  induction hL : ws.length using Nat.strong_induction_on generalizing ws G with
  | ind L ih =>
    cases ws with
    | nil =>
      subst hL
      refine ⟨hwf, extends_rfl G, by simp [pairPass], by simp [pairPass],
        fun _ h => by simp [pairPass] at h, fun _ h => by simp [pairPass] at h, fun a => by simp [pairPass]⟩
    | cons w1 tail =>
      cases tail with
      | nil =>
        subst hL
        refine ⟨hwf, extends_rfl G, by simp [pairPass], by simp [pairPass], ?_, ?_, ?_⟩
        · intro w hw; simp [pairPass] at hw; subst hw; exact hbd w (by simp)
        · intro w hw; simp [pairPass] at hw; subst hw
          exact le_trans (hdep w (by simp)) (by omega)
        · intro a; simp [pairPass]
      | cons w2 rest =>
        subst hL
        have hw1 : w1 < 2 + Fintype.card P + G.length := hbd w1 (by simp)
        have hw2 : w2 < 2 + Fintype.card P + G.length := hbd w2 (by simp)
        have hd1 : (mdepths (2 + Fintype.card P) G).getD w1 0 ≤ dmax := hdep w1 (by simp)
        have hd2 : (mdepths (2 + Fintype.card P) G).getD w2 0 ≤ dmax := hdep w2 (by simp)
        set r1 := addMGate (2 + Fintype.card P) G isAnd w1 w2 with hr1
        have hwf1 : WellFormed (2 + Fintype.card P) r1.1 := addMGate_wf hwf isAnd hw1 hw2
        have hext1 : Extends G r1.1 := addMGate_extends (2 + Fintype.card P) G isAnd w1 w2
        have hlen1 : r1.1.length = G.length + 1 := addMGate_len (2 + Fintype.card P) G isAnd w1 w2
        have hlt1 : r1.2 < 2 + Fintype.card P + r1.1.length := addMGate_out_lt (2 + Fintype.card P) G isAnd w1 w2
        have hdep1 : (mdepths (2 + Fintype.card P) r1.1).getD r1.2 0 ≤ dmax + 1 := by
          rw [hr1, addMGate_depth]; omega
        have hbd_rest : ∀ w ∈ rest, w < 2 + Fintype.card P + r1.1.length := fun w hw => by
          have := hbd w (by simp [hw]); omega
        have hdep_rest : ∀ w ∈ rest, (mdepths (2 + Fintype.card P) r1.1).getD w 0 ≤ dmax := fun w hw => by
          have hlt := hbd w (by simp [hw])
          rw [mdepths_of_extends hext1 w hlt]
          exact hdep w (by simp [hw])
        have h2 := ih rest.length (by simp) r1.1 rest hwf1 hbd_rest hdep_rest rfl
        rcases h2 with ⟨hwf2, hext2, hlen2, houtlen2, hbd2, hdep2, hev2⟩
        set r2 := pairPass isAnd (2 + Fintype.card P) r1.1 rest with hr2
        have hextAll : Extends G r2.1 := extends_trans hext1 hext2
        have hlen_le : r1.1.length ≤ r2.1.length := extends_len hext2
        change WellFormed (2 + Fintype.card P) r2.1 ∧ Extends G r2.1 ∧
          r2.1.length = G.length + (w1 :: w2 :: rest).length / 2 ∧
          (r1.2 :: r2.2).length = ((w1 :: w2 :: rest).length + 1) / 2 ∧
          (∀ w ∈ r1.2 :: r2.2, w < 2 + Fintype.card P + r2.1.length) ∧
          (∀ w ∈ r1.2 :: r2.2, (mdepths (2 + Fintype.card P) r2.1).getD w 0 ≤ dmax + 1) ∧
          (∀ a : P → Bool, evalList isAnd (fun w => (mrun r2.1 a).getD w false) (r1.2 :: r2.2) =
            evalList isAnd (fun w => (mrun G a).getD w false) (w1 :: w2 :: rest))
        refine ⟨hwf2, hextAll, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hmem
          · omega
          · exact hbd2 w hmem
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hmem
          · rw [mdepths_of_extends hext2 r1.2 hlt1]; exact hdep1
          · exact hdep2 w hmem
        · intro a
          have hv1 : (mrun r2.1 a).getD r1.2 false =
              if isAnd then (mrun G a).getD w1 false && (mrun G a).getD w2 false
              else (mrun G a).getD w1 false || (mrun G a).getD w2 false := by
            rw [mrun_of_extends hext2 a r1.2 hlt1, hr1, addMGate_val]
          have hvrest : evalList isAnd (fun w => (mrun r2.1 a).getD w false) r2.2 =
              evalList isAnd (fun w => (mrun G a).getD w false) rest := by
            rw [hev2 a]
            apply evalList_congr
            intro w hw
            exact mrun_of_extends hext1 a w (hbd w (by simp [hw]))
          cases isAnd
          · simp only [evalList, Bool.false_eq_true, ↓reduceIte, List.any_cons] at hvrest ⊢
            rw [hv1, hvrest]; simp [Bool.or_assoc]
          · simp only [evalList, ↓reduceIte, List.all_cons] at hvrest ⊢
            rw [hv1, hvrest]; simp [Bool.and_assoc]

def reduceTree (isAnd : Bool) (N : ℕ) : ℕ → List MGate → List ℕ → List MGate × List ℕ
  | 0, G, ws => (G, ws)
  | k + 1, G, ws =>
    let r1 := pairPass isAnd N G ws
    reduceTree isAnd N k r1.1 r1.2

lemma reduceTree_spec {P : Type} [Fintype P] (isAnd : Bool) (k : ℕ)
    (G : List MGate) (ws : List ℕ) (dmax : ℕ)
    (hpos : 1 ≤ ws.length) (hle : ws.length ≤ 2 ^ k)
    (hwf : WellFormed (2 + Fintype.card P) G)
    (hbd : ∀ w ∈ ws, w < 2 + Fintype.card P + G.length)
    (hdep : ∀ w ∈ ws, (mdepths (2 + Fintype.card P) G).getD w 0 ≤ dmax) :
    let N := 2 + Fintype.card P
    let r := reduceTree isAnd N k G ws
    WellFormed N r.1 ∧ Extends G r.1 ∧
    r.1.length + r.2.length = G.length + ws.length ∧
    r.2.length = 1 ∧
    (∀ w ∈ r.2, w < N + r.1.length) ∧
    (∀ w ∈ r.2, (mdepths N r.1).getD w 0 ≤ dmax + k) ∧
    (∀ a : P → Bool, evalList isAnd (fun w => (mrun r.1 a).getD w false) r.2 =
      evalList isAnd (fun w => (mrun G a).getD w false) ws) := by
  induction k generalizing G ws dmax with
  | zero =>
    simp only [pow_zero] at hle
    exact ⟨hwf, extends_rfl G, by simp [reduceTree], by simp [reduceTree]; omega,
      hbd, hdep, fun a => by simp [reduceTree]⟩
  | succ k ih =>
    have h1 := pairPass_spec isAnd G ws dmax hwf hbd hdep
    rcases h1 with ⟨hwf1, hext1, hlen1, houtlen1, hbd1, hdep1, hev1⟩
    set r1 := pairPass isAnd (2 + Fintype.card P) G ws with hr1
    have hpos1 : 1 ≤ r1.2.length := by omega
    have hle1 : r1.2.length ≤ 2 ^ k := by rw [pow_succ] at hle; omega
    have h2 := ih r1.1 r1.2 (dmax + 1) hpos1 hle1 hwf1 hbd1 hdep1
    rcases h2 with ⟨hwf2, hext2, hsum2, houtlen2, hbd2, hdep2, hev2⟩
    dsimp only [reduceTree]
    rw [← hr1]
    refine ⟨hwf2, extends_trans hext1 hext2, ?_, houtlen2, hbd2, ?_, ?_⟩
    · omega
    · intro w hw; have := hdep2 w hw; omega
    · intro a; rw [hev2 a, hev1 a]

def addTree (isAnd : Bool) (N : ℕ) (G : List MGate) (ws : List ℕ) : List MGate × ℕ :=
  match ws with
  | [] => (G, if isAnd then 1 else 0)
  | _ :: _ =>
    let r := reduceTree isAnd N (Nat.clog 2 ws.length) G ws
    (r.1, r.2.headD 0)

lemma addTree_spec {P : Type} [Fintype P] (isAnd : Bool)
    (G : List MGate) (ws : List ℕ) (dmax : ℕ)
    (hwf : WellFormed (2 + Fintype.card P) G)
    (hbd : ∀ w ∈ ws, w < 2 + Fintype.card P + G.length)
    (hdep : ∀ w ∈ ws, (mdepths (2 + Fintype.card P) G).getD w 0 ≤ dmax) :
    let N := 2 + Fintype.card P
    let r := addTree isAnd N G ws
    WellFormed N r.1 ∧ Extends G r.1 ∧
    r.1.length ≤ G.length + ws.length ∧
    r.2 < N + r.1.length ∧
    (mdepths N r.1).getD r.2 0 ≤ dmax + Nat.clog 2 ws.length ∧
    (∀ a : P → Bool, (mrun r.1 a).getD r.2 false =
      evalList isAnd (fun w => (mrun G a).getD w false) ws) := by
  let N := 2 + Fintype.card P
  cases ws with
  | nil =>
    refine ⟨hwf, extends_rfl G, by simp [addTree], ?_, ?_, ?_⟩
    · dsimp [addTree]; cases isAnd
      · simp
      · simp; omega
    · dsimp [addTree]; cases isAnd
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [mdepths_base G 0 (by omega)]; omega
      · simp only [↓reduceIte]; rw [mdepths_base G 1 (by omega)]; omega
    · intro a; dsimp [addTree, evalList]; cases isAnd
      · simpa using mrun_const0 G a
      · simpa using mrun_const1 G a
  | cons w0 rest =>
    set ws' := w0 :: rest
    have hpos : 1 ≤ ws'.length := by simp [ws']
    have hle : ws'.length ≤ 2 ^ Nat.clog 2 ws'.length := Nat.le_pow_clog (by omega) ws'.length
    have hred := reduceTree_spec isAnd (Nat.clog 2 ws'.length) G ws' dmax hpos hle hwf hbd hdep
    rcases hred with ⟨hwf1, hext1, hsum1, hout1, hbd1, hdep1, hev1⟩
    set r := reduceTree isAnd N (Nat.clog 2 ws'.length) G ws' with hr
    have hhead : ∃ w, r.2 = [w] := by
      cases h : r.2 with
      | nil => simp [h] at hout1
      | cons w l =>
        cases l with
        | nil => exact ⟨w, rfl⟩
        | cons _ _ => simp [h] at hout1
    rcases hhead with ⟨w, hw_eq⟩
    have hw_mem : w ∈ r.2 := by simp [hw_eq]
    change WellFormed N r.1 ∧ Extends G r.1 ∧ r.1.length ≤ G.length + ws'.length ∧
      r.2.headD 0 < N + r.1.length ∧
      (mdepths N r.1).getD (r.2.headD 0) 0 ≤ dmax + Nat.clog 2 ws'.length ∧
      (∀ a : P → Bool, (mrun r.1 a).getD (r.2.headD 0) false =
        evalList isAnd (fun w => (mrun G a).getD w false) ws')
    rw [hw_eq]
    simp only [List.headD_cons]
    refine ⟨hwf1, hext1, by omega, hbd1 w hw_mem, hdep1 w hw_mem, ?_⟩
    intro a
    have h := hev1 a
    rw [hw_eq] at h
    cases isAnd
    · simpa [evalList] using h
    · simpa [evalList] using h

def bpop {m : ℕ} (v : Fin m → Bool) : ℕ :=
  ∑ i : Fin m, (v i).toNat

lemma bpop_le {m : ℕ} (v : Fin m → Bool) : bpop v ≤ m := by
  unfold bpop
  calc ∑ i : Fin m, (v i).toNat
      ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum (fun i _ => by cases v i <;> decide)
    _ = m := by simp

def IsBitonic {k : ℕ} (v : Fin (2 ^ k) → Bool) : Prop :=
  (∃ a b : ℕ, a ≤ b ∧ b ≤ 2 ^ k ∧ ∀ i : Fin (2 ^ k), v i = decide (a ≤ i.val ∧ i.val < b)) ∨
  (∃ a b : ℕ, a ≤ b ∧ b ≤ 2 ^ k ∧ ∀ i : Fin (2 ^ k), v i = decide (i.val < a ∨ b ≤ i.val))

lemma isBitonic_not {k : ℕ} {v : Fin (2 ^ k) → Bool} (h : IsBitonic v) :
    IsBitonic (fun i => !(v i)) := by
  rcases h with ⟨a, b, hab, hb, hv⟩ | ⟨a, b, hab, hb, hv⟩
  · right
    refine ⟨a, b, hab, hb, fun i => ?_⟩
    dsimp only; rw [hv i]
    by_cases h1 : a ≤ i.val ∧ i.val < b
    · have h2 : ¬ (i.val < a ∨ b ≤ i.val) := by omega
      simp [h1, h2]
    · have h2 : i.val < a ∨ b ≤ i.val := by omega
      simp [h1, h2]
  · left
    refine ⟨a, b, hab, hb, fun i => ?_⟩
    dsimp only; rw [hv i]
    by_cases h1 : i.val < a ∨ b ≤ i.val
    · have h2 : ¬ (a ≤ i.val ∧ i.val < b) := by omega
      simp [h1, h2]
    · have h2 : a ≤ i.val ∧ i.val < b := by omega
      simp [h1, h2]

lemma bitonic_split_left {k : ℕ} (v : Fin (2 ^ (k + 1)) → Bool)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 2 ^ (k + 1))
    (hv : ∀ i : Fin (2 ^ (k + 1)), v i = decide (a ≤ i.val ∧ i.val < b)) :
    let lo : Fin (2 ^ k) → Bool := fun i => v ⟨i.val, by rw [pow_succ]; omega⟩ && v ⟨i.val + 2 ^ k, by rw [pow_succ]; omega⟩
    let hi : Fin (2 ^ k) → Bool := fun i => v ⟨i.val, by rw [pow_succ]; omega⟩ || v ⟨i.val + 2 ^ k, by rw [pow_succ]; omega⟩
    IsBitonic lo ∧ IsBitonic hi ∧ ((∀ i, lo i = false) ∨ (∀ i, hi i = true)) := by
  intro lo hi
  have h2k : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  by_cases hlen : b - a ≤ 2 ^ k
  · have hlo : ∀ i : Fin (2 ^ k), lo i = false := by
      intro i
      dsimp only [lo]
      rw [hv ⟨i.val, by omega⟩, hv ⟨i.val + 2 ^ k, by omega⟩]
      by_cases h1 : a ≤ i.val ∧ i.val < b
      · have h2 : ¬ (a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b) := by omega
        simp [h1, h2]
      · simp [h1]
    have hlo_bit : IsBitonic lo := Or.inl ⟨0, 0, le_rfl, by omega, fun i => by simp [hlo i]⟩
    have hhi_bit : IsBitonic hi := by
      by_cases hb1 : b ≤ 2 ^ k
      · left; refine ⟨a, b, hab, hb1, fun i => ?_⟩
        dsimp only [hi]; rw [hv ⟨i.val, by omega⟩, hv ⟨i.val + 2 ^ k, by omega⟩]
        have h2 : ¬ (a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b) := by omega
        simp [h2]
      · by_cases ha1 : 2 ^ k ≤ a
        · left; refine ⟨a - 2 ^ k, b - 2 ^ k, by omega, by omega, fun i => ?_⟩
          dsimp only [hi]; rw [hv ⟨i.val, by omega⟩, hv ⟨i.val + 2 ^ k, by omega⟩]
          have h1 : ¬ (a ≤ i.val ∧ i.val < b) := by omega
          simp only [h1, decide_false, Bool.false_or]
          congr 1; apply propext; omega
        · right; refine ⟨b - 2 ^ k, a, by omega, by omega, fun i => ?_⟩
          dsimp only [hi]; rw [hv ⟨i.val, by omega⟩, hv ⟨i.val + 2 ^ k, by omega⟩]
          by_cases hc1 : i.val < b - 2 ^ k
          · have : a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b := by omega
            simp [hc1, this]
          · by_cases hc2 : a ≤ i.val
            · have : a ≤ i.val ∧ i.val < b := by omega
              simp [hc1, hc2, this]
            · have hn2 : ¬ (a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b) := by omega
              simp [hc1, hc2, hn2]
    exact ⟨hlo_bit, hhi_bit, Or.inl hlo⟩
  · have hhi : ∀ i : Fin (2 ^ k), hi i = true := by
      intro i
      dsimp only [hi]
      rw [hv ⟨i.val, by omega⟩, hv ⟨i.val + 2 ^ k, by omega⟩]
      by_cases h1 : a ≤ i.val
      · have : a ≤ i.val ∧ i.val < b := by omega
        simp [this]
      · have : a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b := by omega
        simp [this]
    have hhi_bit : IsBitonic hi := Or.inl ⟨0, 2 ^ k, by omega, le_rfl, fun i => by simp [hhi i, i.isLt]⟩
    have hlo_bit : IsBitonic lo := by
      left; refine ⟨a, b - 2 ^ k, by omega, by omega, fun i => ?_⟩
      dsimp only [lo]
      rw [hv ⟨i.val, by omega⟩, hv ⟨i.val + 2 ^ k, by omega⟩]
      by_cases h1 : a ≤ i.val ∧ i.val < b - 2 ^ k
      · have ha' : a ≤ i.val ∧ i.val < b := by omega
        have hb' : a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b := by omega
        simp [h1, ha', hb']
      · simp only [h1, decide_false]
        by_cases ha' : a ≤ i.val
        · have hn2 : ¬ (a ≤ i.val + 2 ^ k ∧ i.val + 2 ^ k < b) := by omega
          simp [hn2]
        · have hn1 : ¬ (a ≤ i.val ∧ i.val < b) := by omega
          simp [hn1]
    exact ⟨hlo_bit, hhi_bit, Or.inr hhi⟩

lemma bitonic_split {k : ℕ} (v : Fin (2 ^ (k + 1)) → Bool) (hbit : IsBitonic v) :
    let lo : Fin (2 ^ k) → Bool := fun i => v ⟨i.val, by rw [pow_succ]; omega⟩ && v ⟨i.val + 2 ^ k, by rw [pow_succ]; omega⟩
    let hi : Fin (2 ^ k) → Bool := fun i => v ⟨i.val, by rw [pow_succ]; omega⟩ || v ⟨i.val + 2 ^ k, by rw [pow_succ]; omega⟩
    IsBitonic lo ∧ IsBitonic hi ∧ ((∀ i, lo i = false) ∨ (∀ i, hi i = true)) ∧
      bpop lo + bpop hi = bpop v := by
  intro lo hi
  have hpop : bpop lo + bpop hi = bpop v := by
    have hhalf : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    unfold bpop
    rw [← Finset.sum_add_distrib]
    have hpair : ∀ i : Fin (2 ^ k), (lo i).toNat + (hi i).toNat =
        (v ⟨i.val, by omega⟩).toNat + (v ⟨i.val + 2 ^ k, by omega⟩).toNat := by
      intro i; dsimp only [lo, hi]
      cases v ⟨i.val, by omega⟩ <;> cases v ⟨i.val + 2 ^ k, by omega⟩ <;> rfl
    calc ∑ i : Fin (2 ^ k), ((lo i).toNat + (hi i).toNat)
        = ∑ i : Fin (2 ^ k), ((v ⟨i.val, by omega⟩).toNat + (v ⟨i.val + 2 ^ k, by omega⟩).toNat) :=
          Finset.sum_congr rfl (fun i _ => hpair i)
      _ = ∑ i : Fin (2 ^ k), (v ⟨i.val, by omega⟩).toNat +
          ∑ i : Fin (2 ^ k), (v ⟨2 ^ k + i.val, by omega⟩).toNat := by
          rw [Finset.sum_add_distrib]
          congr 1; apply Finset.sum_congr rfl; intro i _
          congr 2; apply Fin.ext; simp; omega
      _ = ∑ i : Fin (2 ^ k + 2 ^ k), (v ⟨i.val, by omega⟩).toNat :=
          (Fin.sum_univ_add (f := fun i : Fin (2 ^ k + 2 ^ k) => (v ⟨i.val, by omega⟩).toNat)).symm
      _ = ∑ i : Fin (2 ^ (k + 1)), (v i).toNat :=
          (Fintype.sum_equiv (finCongr hhalf) _ _ (fun _ => rfl)).symm
  rcases hbit with ⟨a, b, hab, hb, hv⟩ | ⟨a, b, hab, hb, hv⟩
  · rcases bitonic_split_left v a b hab hb hv with ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3, hpop⟩
  · have hnot : ∀ i : Fin (2 ^ (k + 1)), (!(v i)) = decide (a ≤ i.val ∧ i.val < b) := by
      intro i; rw [hv i]
      by_cases h1 : i.val < a ∨ b ≤ i.val
      · have h2 : ¬ (a ≤ i.val ∧ i.val < b) := by omega
        simp [h1, h2]
      · have h2 : a ≤ i.val ∧ i.val < b := by omega
        simp [h1, h2]
    rcases bitonic_split_left (fun i => !(v i)) a b hab hb hnot with ⟨h1, h2, h3⟩
    have hlo_eq : lo = fun i => !((!(v ⟨i.val, by rw [pow_succ]; omega⟩)) || (!(v ⟨i.val + 2 ^ k, by rw [pow_succ]; omega⟩))) := by
      funext i; dsimp only [lo]; cases v ⟨i.val, by rw [pow_succ]; omega⟩ <;> cases v ⟨i.val + 2 ^ k, by rw [pow_succ]; omega⟩ <;> rfl
    have hhi_eq : hi = fun i => !((!(v ⟨i.val, by rw [pow_succ]; omega⟩)) && (!(v ⟨i.val + 2 ^ k, by rw [pow_succ]; omega⟩))) := by
      funext i; dsimp only [hi]; cases v ⟨i.val, by rw [pow_succ]; omega⟩ <;> cases v ⟨i.val + 2 ^ k, by rw [pow_succ]; omega⟩ <;> rfl
    refine ⟨hlo_eq ▸ isBitonic_not h2, hhi_eq ▸ isBitonic_not h1, ?_, hpop⟩
    rcases h3 with hlo' | hhi'
    · right; intro i; rw [hhi_eq]; simp [hlo' i]
    · left; intro i; rw [hlo_eq]; simp [hhi' i]

def addSplitLayer (N : ℕ) (G : List MGate) (m : ℕ) (ws : Fin (m + m) → ℕ) :
    (t : ℕ) → t ≤ m → List MGate × (Fin m → ℕ) × (Fin m → ℕ)
  | 0, _ => (G, fun _ => 0, fun _ => 0)
  | t + 1, ht =>
    let r1 := addSplitLayer N G m ws t (by omega)
    let r2 := addMGate N r1.1 true (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩)
    let r3 := addMGate N r2.1 false (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩)
    (r3.1,
      fun i => if i.val = t then r2.2 else r1.2.1 i,
      fun i => if i.val = t then r3.2 else r1.2.2 i)

lemma addSplitLayer_spec {P : Type} [Fintype P] (G : List MGate) (m : ℕ)
    (ws : Fin (m + m) → ℕ) (dmax : ℕ)
    (hwf : WellFormed (2 + Fintype.card P) G)
    (hbd : ∀ i, ws i < 2 + Fintype.card P + G.length)
    (hdep : ∀ i, (mdepths (2 + Fintype.card P) G).getD (ws i) 0 ≤ dmax) :
    ∀ (t : ℕ) (ht : t ≤ m),
      let N := 2 + Fintype.card P
      let r := addSplitLayer N G m ws t ht
      WellFormed N r.1 ∧ Extends G r.1 ∧
      r.1.length = G.length + 2 * t ∧
      (∀ i : Fin m, i.val < t → r.2.1 i < N + r.1.length ∧ r.2.2 i < N + r.1.length) ∧
      (∀ i : Fin m, i.val < t → (mdepths N r.1).getD (r.2.1 i) 0 ≤ dmax + 1 ∧
        (mdepths N r.1).getD (r.2.2 i) 0 ≤ dmax + 1) ∧
      (∀ a : P → Bool, ∀ i : Fin m, i.val < t →
        (mrun r.1 a).getD (r.2.1 i) false =
          ((mrun G a).getD (ws ⟨i.val, by omega⟩) false && (mrun G a).getD (ws ⟨i.val + m, by omega⟩) false) ∧
        (mrun r.1 a).getD (r.2.2 i) false =
          ((mrun G a).getD (ws ⟨i.val, by omega⟩) false || (mrun G a).getD (ws ⟨i.val + m, by omega⟩) false)) := by
  intro t ht
  induction t with
  | zero =>
    exact ⟨hwf, extends_rfl G, by simp [addSplitLayer], fun _ h => by omega,
      fun _ h => by omega, fun _ _ h => by omega⟩
  | succ t ih =>
    rcases ih (by omega) with ⟨hwf1, hext1, hlen1, hbd1, hdep1, hev1⟩
    set r1 := addSplitLayer (2 + Fintype.card P) G m ws t (by omega) with hr1
    have hltL : ws ⟨t, by omega⟩ < 2 + Fintype.card P + r1.1.length := by have := hbd ⟨t, by omega⟩; omega
    have hltR : ws ⟨t + m, by omega⟩ < 2 + Fintype.card P + r1.1.length := by have := hbd ⟨t + m, by omega⟩; omega
    set r2 := addMGate (2 + Fintype.card P) r1.1 true (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩) with hr2
    have hwf2 : WellFormed (2 + Fintype.card P) r2.1 := addMGate_wf hwf1 true hltL hltR
    have hext2 : Extends r1.1 r2.1 := addMGate_extends (2 + Fintype.card P) r1.1 true (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩)
    have hlen2 : r2.1.length = r1.1.length + 1 := addMGate_len (2 + Fintype.card P) r1.1 true (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩)
    have hout2 : r2.2 < 2 + Fintype.card P + r2.1.length := addMGate_out_lt (2 + Fintype.card P) r1.1 true (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩)
    set r3 := addMGate (2 + Fintype.card P) r2.1 false (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩) with hr3
    have hwf3 : WellFormed (2 + Fintype.card P) r3.1 :=
      addMGate_wf hwf2 false (l := ws ⟨t, by omega⟩) (r := ws ⟨t + m, by omega⟩) (by omega) (by omega)
    have hext3 : Extends r2.1 r3.1 := addMGate_extends (2 + Fintype.card P) r2.1 false (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩)
    have hlen3 : r3.1.length = r2.1.length + 1 := addMGate_len (2 + Fintype.card P) r2.1 false (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩)
    have hout3 : r3.2 < 2 + Fintype.card P + r3.1.length := addMGate_out_lt (2 + Fintype.card P) r2.1 false (ws ⟨t, by omega⟩) (ws ⟨t + m, by omega⟩)
    have hext13 : Extends r1.1 r3.1 := extends_trans hext2 hext3
    have hextG2 : Extends G r2.1 := extends_trans hext1 hext2
    dsimp only [addSplitLayer]
    rw [← hr1, ← hr2, ← hr3]
    refine ⟨hwf3, extends_trans hext1 hext13, by omega, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hit : i.val = t
      · simp only [hit, ↓reduceIte]
        exact ⟨by omega, hout3⟩
      · simp only [hit, ↓reduceIte]
        have := hbd1 i (by omega); omega
    · intro i hi
      by_cases hit : i.val = t
      · simp only [hit, ↓reduceIte]
        constructor
        · rw [mdepths_of_extends hext3 r2.2 hout2, hr2, addMGate_depth,
            mdepths_of_extends hext1 _ (hbd ⟨t, by omega⟩), mdepths_of_extends hext1 _ (hbd ⟨t + m, by omega⟩)]
          have := hdep ⟨t, by omega⟩; have := hdep ⟨t + m, by omega⟩; omega
        · rw [hr3, addMGate_depth,
            mdepths_of_extends hextG2 _ (hbd ⟨t, by omega⟩), mdepths_of_extends hextG2 _ (hbd ⟨t + m, by omega⟩)]
          have := hdep ⟨t, by omega⟩; have := hdep ⟨t + m, by omega⟩; omega
      · simp only [hit, ↓reduceIte]
        have hb1 := hbd1 i (by omega)
        have hd1 := hdep1 i (by omega)
        rw [mdepths_of_extends hext13 _ hb1.1, mdepths_of_extends hext13 _ hb1.2]
        exact hd1
    · intro a i hi
      by_cases hit : i.val = t
      · simp only [hit, ↓reduceIte]
        constructor
        · rw [mrun_of_extends hext3 a r2.2 hout2, hr2, addMGate_val,
            mrun_of_extends hext1 a _ (hbd ⟨t, by omega⟩), mrun_of_extends hext1 a _ (hbd ⟨t + m, by omega⟩)]
          simp
        · rw [hr3, addMGate_val,
            mrun_of_extends hextG2 a _ (hbd ⟨t, by omega⟩), mrun_of_extends hextG2 a _ (hbd ⟨t + m, by omega⟩)]
          simp
      · simp only [hit, ↓reduceIte]
        have hb1 := hbd1 i (by omega)
        rw [mrun_of_extends hext13 a _ hb1.1, mrun_of_extends hext13 a _ hb1.2]
        exact hev1 a i (by omega)

def addBitonicMerge (N : ℕ) (dir : Bool) : (k : ℕ) → List MGate → (Fin (2 ^ k) → ℕ) → List MGate × (Fin (2 ^ k) → ℕ)
  | 0, G, ws => (G, ws)
  | k + 1, G, ws =>
    let ws2 : Fin (2 ^ k + 2 ^ k) → ℕ := fun i => ws ⟨i.val, by rw [pow_succ]; omega⟩
    let sp := addSplitLayer N G (2 ^ k) ws2 (2 ^ k) le_rfl
    let first := if dir then sp.2.1 else sp.2.2
    let second := if dir then sp.2.2 else sp.2.1
    let r1 := addBitonicMerge N dir k sp.1 first
    let r2 := addBitonicMerge N dir k r1.1 second
    (r2.1, fun i => if h : i.val < 2 ^ k then r1.2 ⟨i.val, h⟩ else r2.2 ⟨i.val - 2 ^ k, by rw [pow_succ] at i; omega⟩)

def sortedBit (dir : Bool) (len w idx : ℕ) : Bool :=
  if dir then decide (len - w ≤ idx) else decide (idx < w)

lemma addBitonicMerge_spec {P : Type} [Fintype P] (dir : Bool) (k : ℕ)
    (G : List MGate) (ws : Fin (2 ^ k) → ℕ) (dmax : ℕ)
    (hwf : WellFormed (2 + Fintype.card P) G)
    (hbd : ∀ i, ws i < 2 + Fintype.card P + G.length)
    (hdep : ∀ i, (mdepths (2 + Fintype.card P) G).getD (ws i) 0 ≤ dmax) :
    let N := 2 + Fintype.card P
    let r := addBitonicMerge N dir k G ws
    WellFormed N r.1 ∧ Extends G r.1 ∧
    r.1.length = G.length + k * 2 ^ k ∧
    (∀ i, r.2 i < N + r.1.length) ∧
    (∀ i, (mdepths N r.1).getD (r.2 i) 0 ≤ dmax + k) ∧
    (∀ a : P → Bool,
      let v : Fin (2 ^ k) → Bool := fun i => (mrun G a).getD (ws i) false
      IsBitonic v → ∀ i : Fin (2 ^ k),
        (mrun r.1 a).getD (r.2 i) false = sortedBit dir (2 ^ k) (bpop v) i.val) := by
  induction k generalizing G dmax with
  | zero =>
    refine ⟨hwf, extends_rfl G, by simp [addBitonicMerge], hbd, hdep, ?_⟩
    intro a v _ i
    fin_cases i
    dsimp [addBitonicMerge, sortedBit, v, bpop]
    simp only [Fintype.sum_unique, Fin.default_eq_zero]
    cases (mrun G a).getD (ws 0) false <;> cases dir <;> rfl
  | succ k ih =>
    let ws2 : Fin (2 ^ k + 2 ^ k) → ℕ := fun i => ws ⟨i.val, by rw [pow_succ]; omega⟩
    have hsp := addSplitLayer_spec G (2 ^ k) ws2 dmax hwf
      (fun i => hbd ⟨i.val, by rw [pow_succ]; omega⟩)
      (fun i => hdep ⟨i.val, by rw [pow_succ]; omega⟩) (2 ^ k) le_rfl
    rcases hsp with ⟨hwfS, hextS, hlenS, hbdS, hdepS, hevS⟩
    set sp := addSplitLayer (2 + Fintype.card P) G (2 ^ k) ws2 (2 ^ k) le_rfl with hsp_def
    let first := if dir then sp.2.1 else sp.2.2
    let second := if dir then sp.2.2 else sp.2.1
    have hbdF : ∀ i, first i < 2 + Fintype.card P + sp.1.length := fun i => by
      dsimp [first]; split_ifs
      · exact (hbdS i i.isLt).1
      · exact (hbdS i i.isLt).2
    have hdepF : ∀ i, (mdepths (2 + Fintype.card P) sp.1).getD (first i) 0 ≤ dmax + 1 := fun i => by
      dsimp [first]; split_ifs
      · exact (hdepS i i.isLt).1
      · exact (hdepS i i.isLt).2
    have h1 := ih sp.1 first (dmax + 1) hwfS hbdF hdepF
    rcases h1 with ⟨hwf1, hext1, hlen1, hbd1, hdep1, hev1⟩
    set r1 := addBitonicMerge (2 + Fintype.card P) dir k sp.1 first with hr1
    have hbdSec : ∀ i, second i < 2 + Fintype.card P + r1.1.length := fun i => by
      have hlen1' := extends_len hext1
      dsimp [second]; split_ifs
      · have := (hbdS i i.isLt).2; omega
      · have := (hbdS i i.isLt).1; omega
    have hdepSec : ∀ i, (mdepths (2 + Fintype.card P) r1.1).getD (second i) 0 ≤ dmax + 1 := fun i => by
      dsimp [second]; split_ifs
      · rw [mdepths_of_extends hext1 _ (hbdS i i.isLt).2]; exact (hdepS i i.isLt).2
      · rw [mdepths_of_extends hext1 _ (hbdS i i.isLt).1]; exact (hdepS i i.isLt).1
    have h2 := ih r1.1 second (dmax + 1) hwf1 hbdSec hdepSec
    rcases h2 with ⟨hwf2, hext2, hlen2, hbd2, hdep2, hev2⟩
    set r2 := addBitonicMerge (2 + Fintype.card P) dir k r1.1 second with hr2
    have hextAll : Extends G r2.1 := extends_trans hextS (extends_trans hext1 hext2)
    have hlen_le2 : r1.1.length ≤ r2.1.length := extends_len hext2
    change WellFormed (2 + Fintype.card P) r2.1 ∧ Extends G r2.1 ∧ r2.1.length = G.length + (k + 1) * 2 ^ (k + 1) ∧
      (∀ i : Fin (2 ^ (k + 1)), (if h : i.val < 2 ^ k then r1.2 ⟨i.val, h⟩ else r2.2 ⟨i.val - 2 ^ k, by rw [pow_succ] at i; omega⟩) < 2 + Fintype.card P + r2.1.length) ∧
      (∀ i : Fin (2 ^ (k + 1)), (mdepths (2 + Fintype.card P) r2.1).getD (if h : i.val < 2 ^ k then r1.2 ⟨i.val, h⟩ else r2.2 ⟨i.val - 2 ^ k, by rw [pow_succ] at i; omega⟩) 0 ≤ dmax + (k + 1)) ∧
      (∀ a : P → Bool, let v : Fin (2 ^ (k + 1)) → Bool := fun i => (mrun G a).getD (ws i) false;
        IsBitonic v → ∀ i : Fin (2 ^ (k + 1)),
          (mrun r2.1 a).getD (if h : i.val < 2 ^ k then r1.2 ⟨i.val, h⟩ else r2.2 ⟨i.val - 2 ^ k, by rw [pow_succ] at i; omega⟩) false =
          sortedBit dir (2 ^ (k + 1)) (bpop v) i.val)
    refine ⟨hwf2, hextAll, ?_, ?_, ?_, ?_⟩
    · rw [hlen2, hlen1, hlenS, pow_succ]; ring
    · intro i
      split_ifs with hi
      · have := hbd1 ⟨i.val, hi⟩; omega
      · exact hbd2 ⟨i.val - 2 ^ k, by rw [pow_succ] at i; omega⟩
    · intro i
      split_ifs with hi
      · rw [mdepths_of_extends hext2 _ (hbd1 ⟨i.val, hi⟩)]
        have := hdep1 ⟨i.val, hi⟩; omega
      · have := hdep2 ⟨i.val - 2 ^ k, by rw [pow_succ] at i; omega⟩; omega
    · intro a v hbit i
      rcases bitonic_split v hbit with ⟨hlo_bit, hhi_bit, hconst, hpop_sum⟩
      set lo : Fin (2 ^ k) → Bool := fun j => v ⟨j.val, by rw [pow_succ]; omega⟩ && v ⟨j.val + 2 ^ k, by rw [pow_succ]; omega⟩
      set hi : Fin (2 ^ k) → Bool := fun j => v ⟨j.val, by rw [pow_succ]; omega⟩ || v ⟨j.val + 2 ^ k, by rw [pow_succ]; omega⟩
      have hsp_lo : (fun j : Fin (2 ^ k) => (mrun sp.1 a).getD (sp.2.1 j) false) = lo := by
        funext j; exact (hevS a j j.isLt).1
      have hsp_hi : (fun j : Fin (2 ^ k) => (mrun sp.1 a).getD (sp.2.2 j) false) = hi := by
        funext j; exact (hevS a j j.isLt).2
      have hsec_eq : (fun j : Fin (2 ^ k) => (mrun r1.1 a).getD (second j) false) =
          if dir then hi else lo := by
        funext j
        dsimp [second]
        split_ifs
        · rw [mrun_of_extends hext1 a _ (hbdS j j.isLt).2]; exact congrFun hsp_hi j
        · rw [mrun_of_extends hext1 a _ (hbdS j j.isLt).1]; exact congrFun hsp_lo j
      have hfst_eq : (fun j : Fin (2 ^ k) => (mrun sp.1 a).getD (first j) false) =
          if dir then lo else hi := by
        funext j; dsimp [first]; split_ifs
        · exact congrFun hsp_lo j
        · exact congrFun hsp_hi j
      have hlo_le : bpop lo ≤ 2 ^ k := bpop_le lo
      have hhi_le : bpop hi ≤ 2 ^ k := bpop_le hi
      have h2k : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have hlo0_or_hi1 : bpop lo = 0 ∨ bpop hi = 2 ^ k := by
        rcases hconst with h0 | h1
        · left; unfold bpop; simp [h0]
        · right; unfold bpop; simp [h1]
      by_cases hilt : i.val < 2 ^ k
      · simp only [hilt, ↓reduceDIte]
        rw [mrun_of_extends hext2 a _ (hbd1 ⟨i.val, hilt⟩)]
        have h1ev := hev1 a (by rw [hfst_eq]; cases dir <;> assumption) ⟨i.val, hilt⟩
        rw [hfst_eq] at h1ev
        rw [h1ev]
        unfold sortedBit
        cases dir
        · simp only [Bool.false_eq_true, ↓reduceIte]
          congr 1; apply propext; omega
        · simp only [↓reduceIte]
          congr 1; apply propext; omega
      · simp only [hilt, ↓reduceDIte]
        have h2ev := hev2 a (by rw [hsec_eq]; cases dir <;> assumption) ⟨i.val - 2 ^ k, by omega⟩
        rw [hsec_eq] at h2ev
        rw [h2ev]
        unfold sortedBit
        cases dir
        · simp only [Bool.false_eq_true, ↓reduceIte]
          congr 1; apply propext; omega
        · simp only [↓reduceIte]
          congr 1; apply propext; omega

def addBitonicSort (N : ℕ) (dir : Bool) : (m : ℕ) → List MGate → (Fin (2 ^ m) → ℕ) → List MGate × (Fin (2 ^ m) → ℕ)
  | 0, G, ws => (G, ws)
  | m + 1, G, ws =>
    let wsL : Fin (2 ^ m) → ℕ := fun i => ws ⟨i.val, by rw [pow_succ]; omega⟩
    let wsR : Fin (2 ^ m) → ℕ := fun i => ws ⟨2 ^ m + i.val, by rw [pow_succ]; omega⟩
    let rL := addBitonicSort N true m G wsL
    let rR := addBitonicSort N false m rL.1 wsR
    let comb : Fin (2 ^ (m + 1)) → ℕ := fun i =>
      if h : i.val < 2 ^ m then rL.2 ⟨i.val, h⟩ else rR.2 ⟨i.val - 2 ^ m, by rw [pow_succ] at i; omega⟩
    addBitonicMerge N dir (m + 1) rR.1 comb

lemma addBitonicSort_spec {P : Type} [Fintype P] (dir : Bool) (m : ℕ)
    (G : List MGate) (ws : Fin (2 ^ m) → ℕ) (dmax : ℕ)
    (hwf : WellFormed (2 + Fintype.card P) G)
    (hbd : ∀ i, ws i < 2 + Fintype.card P + G.length)
    (hdep : ∀ i, (mdepths (2 + Fintype.card P) G).getD (ws i) 0 ≤ dmax) :
    let N := 2 + Fintype.card P
    let r := addBitonicSort N dir m G ws
    WellFormed N r.1 ∧ Extends G r.1 ∧
    r.1.length ≤ G.length + m * (m + 1) * 2 ^ m ∧
    (∀ i, r.2 i < N + r.1.length) ∧
    (∀ i, (mdepths N r.1).getD (r.2 i) 0 ≤ dmax + m * (m + 1)) ∧
    (∀ a : P → Bool, ∀ i : Fin (2 ^ m),
      (mrun r.1 a).getD (r.2 i) false =
        sortedBit dir (2 ^ m) (bpop (fun j => (mrun G a).getD (ws j) false)) i.val) := by
  induction m generalizing dir G dmax with
  | zero =>
    refine ⟨hwf, extends_rfl G, by simp [addBitonicSort], hbd, hdep, ?_⟩
    intro a i
    fin_cases i
    dsimp [addBitonicSort, sortedBit, bpop]
    simp only [Fintype.sum_unique, Fin.default_eq_zero]
    cases (mrun G a).getD (ws 0) false <;> cases dir <;> rfl
  | succ m ih =>
    let wsL : Fin (2 ^ m) → ℕ := fun i => ws ⟨i.val, by rw [pow_succ]; omega⟩
    let wsR : Fin (2 ^ m) → ℕ := fun i => ws ⟨2 ^ m + i.val, by rw [pow_succ]; omega⟩
    have hL := ih true G wsL dmax hwf
      (fun i => hbd ⟨i.val, by rw [pow_succ]; omega⟩)
      (fun i => hdep ⟨i.val, by rw [pow_succ]; omega⟩)
    rcases hL with ⟨hwfL, hextL, hlenL, hbdL, hdepL, hevL⟩
    set rL := addBitonicSort (2 + Fintype.card P) true m G wsL with hrL
    have hlen_leL := extends_len hextL
    have hR := ih false rL.1 wsR dmax hwfL
      (fun i => by dsimp only [wsR]; have := hbd ⟨2 ^ m + i.val, by rw [pow_succ]; omega⟩; omega)
      (fun i => by
        dsimp only [wsR]
        rw [mdepths_of_extends hextL _ (hbd ⟨2 ^ m + i.val, by rw [pow_succ]; omega⟩)]
        exact hdep ⟨2 ^ m + i.val, by rw [pow_succ]; omega⟩)
    rcases hR with ⟨hwfR, hextR, hlenR, hbdR, hdepR, hevR⟩
    set rR := addBitonicSort (2 + Fintype.card P) false m rL.1 wsR with hrR
    have hlen_leR := extends_len hextR
    let comb : Fin (2 ^ (m + 1)) → ℕ := fun i =>
      if h : i.val < 2 ^ m then rL.2 ⟨i.val, h⟩ else rR.2 ⟨i.val - 2 ^ m, by rw [pow_succ] at i; omega⟩
    have hbdC : ∀ i, comb i < 2 + Fintype.card P + rR.1.length := fun i => by
      dsimp [comb]; split_ifs with hi
      · have := hbdL ⟨i.val, hi⟩; omega
      · exact hbdR ⟨i.val - 2 ^ m, by rw [pow_succ] at i; omega⟩
    have hdepC : ∀ i, (mdepths (2 + Fintype.card P) rR.1).getD (comb i) 0 ≤ dmax + m * (m + 1) := fun i => by
      dsimp [comb]; split_ifs with hi
      · rw [mdepths_of_extends hextR _ (hbdL ⟨i.val, hi⟩)]; exact hdepL ⟨i.val, hi⟩
      · exact hdepR ⟨i.val - 2 ^ m, by rw [pow_succ] at i; omega⟩
    have hM := addBitonicMerge_spec dir (m + 1) rR.1 comb (dmax + m * (m + 1)) hwfR hbdC hdepC
    rcases hM with ⟨hwfM, hextM, hlenM, hbdM, hdepM, hevM⟩
    dsimp only [addBitonicSort]
    change WellFormed (2 + Fintype.card P) (addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).1 ∧
      Extends G (addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).1 ∧
      (addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).1.length ≤ G.length + (m + 1) * (m + 1 + 1) * 2 ^ (m + 1) ∧
      (∀ i, (addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).2 i < 2 + Fintype.card P + (addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).1.length) ∧
      (∀ i, (mdepths (2 + Fintype.card P) (addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).1).getD
        ((addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).2 i) 0 ≤ dmax + (m + 1) * (m + 1 + 1)) ∧
      (∀ a : P → Bool, ∀ i : Fin (2 ^ (m + 1)),
        (mrun (addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).1 a).getD
          ((addBitonicMerge (2 + Fintype.card P) dir (m + 1) rR.1 comb).2 i) false =
          sortedBit dir (2 ^ (m + 1)) (bpop (fun j => (mrun G a).getD (ws j) false)) i.val)
    refine ⟨hwfM, extends_trans hextL (extends_trans hextR hextM), ?_, hbdM, ?_, ?_⟩
    · have hcoef : 2 * (m * (m + 1)) + 2 * (m + 1) ≤ 2 * ((m + 1) * (m + 1 + 1)) := by nlinarith
      have hmul : (2 * (m * (m + 1)) + 2 * (m + 1)) * 2 ^ m ≤ 2 * ((m + 1) * (m + 1 + 1)) * 2 ^ m :=
        Nat.mul_le_mul_right (2 ^ m) hcoef
      have heq1 : (2 * (m * (m + 1)) + 2 * (m + 1)) * 2 ^ m =
          m * (m + 1) * 2 ^ m + m * (m + 1) * 2 ^ m + (m + 1) * 2 ^ (m + 1) := by
        rw [pow_succ]; ring
      have heq2 : 2 * ((m + 1) * (m + 1 + 1)) * 2 ^ m = (m + 1) * (m + 1 + 1) * 2 ^ (m + 1) := by
        rw [pow_succ]; ring
      omega
    · intro i
      have := hdepM i
      have : m * (m + 1) + (m + 1) ≤ (m + 1) * (m + 1 + 1) := by nlinarith
      omega
    · intro a i
      set vL : Fin (2 ^ m) → Bool := fun j => (mrun G a).getD (wsL j) false with hvL_def
      set vR : Fin (2 ^ m) → Bool := fun j => (mrun G a).getD (wsR j) false with hvR_def
      have hpopL_le : bpop vL ≤ 2 ^ m := bpop_le vL
      have hpopR_le : bpop vR ≤ 2 ^ m := bpop_le vR
      have hvR_eq : (fun j => (mrun rL.1 a).getD (wsR j) false) = vR := by
        funext j; exact mrun_of_extends hextL a _ (hbd ⟨2 ^ m + j.val, by rw [pow_succ]; omega⟩)
      have hcomb_val : ∀ j : Fin (2 ^ (m + 1)),
          (mrun rR.1 a).getD (comb j) false =
          decide (2 ^ m - bpop vL ≤ j.val ∧ j.val < 2 ^ m + bpop vR) := by
        intro j
        dsimp only [comb]
        split_ifs with hj
        · rw [mrun_of_extends hextR a _ (hbdL ⟨j.val, hj⟩), hevL a ⟨j.val, hj⟩, ← hvL_def]
          unfold sortedBit; simp only [↓reduceIte]
          congr 1; apply propext; omega
        · rw [hevR a ⟨j.val - 2 ^ m, by rw [pow_succ] at j; omega⟩, hvR_eq]
          unfold sortedBit; simp only [Bool.false_eq_true, ↓reduceIte]
          congr 1; apply propext; omega
      have hbit : IsBitonic (fun j => (mrun rR.1 a).getD (comb j) false) :=
        Or.inl ⟨2 ^ m - bpop vL, 2 ^ m + bpop vR, by omega, by rw [pow_succ]; omega, hcomb_val⟩
      have hpopC : bpop (fun j => (mrun rR.1 a).getD (comb j) false) =
          bpop (fun j => (mrun G a).getD (ws j) false) := by
        have hhalf : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
        have hsumLR : bpop vL + bpop vR = bpop (fun j => (mrun G a).getD (ws j) false) := by
          unfold bpop
          symm
          calc ∑ j : Fin (2 ^ (m + 1)), ((mrun G a).getD (ws j) false).toNat
              = ∑ j : Fin (2 ^ m + 2 ^ m), ((mrun G a).getD (ws ⟨j.val, by omega⟩) false).toNat :=
                Fintype.sum_equiv (finCongr hhalf) _ _ (fun _ => rfl)
            _ = ∑ j : Fin (2 ^ m), (vL j).toNat + ∑ j : Fin (2 ^ m), (vR j).toNat :=
                Fin.sum_univ_add (f := fun j : Fin (2 ^ m + 2 ^ m) => ((mrun G a).getD (ws ⟨j.val, by omega⟩) false).toNat)
        rw [← hsumLR]
        have hcardC : bpop (fun j => (mrun rR.1 a).getD (comb j) false) = bpop vL + bpop vR := by
          unfold bpop
          calc ∑ j : Fin (2 ^ (m + 1)), ((mrun rR.1 a).getD (comb j) false).toNat
              = ∑ j : Fin (2 ^ m + 2 ^ m),
                  (decide (2 ^ m - bpop vL ≤ j.val ∧ j.val < 2 ^ m + bpop vR)).toNat := by
                refine Fintype.sum_equiv (finCongr hhalf) _ _ (fun j => ?_)
                rw [hcomb_val j]; rfl
            _ = ∑ j : Fin (2 ^ m), (decide (2 ^ m - bpop vL ≤ j.val)).toNat +
                ∑ j : Fin (2 ^ m), (decide (j.val < bpop vR)).toNat := by
                rw [Fin.sum_univ_add]
                congr 1
                · apply Finset.sum_congr rfl; intro j _
                  have hiff : (2 ^ m - bpop vL ≤ j.val ∧ j.val < 2 ^ m + bpop vR) ↔ (2 ^ m - bpop vL ≤ j.val) := by
                    have := j.isLt; omega
                  simp only [Fin.val_castAdd, hiff]
                · apply Finset.sum_congr rfl; intro j _
                  have hiff : (2 ^ m - bpop vL ≤ 2 ^ m + j.val ∧ 2 ^ m + j.val < 2 ^ m + bpop vR) ↔ (j.val < bpop vR) := by omega
                  simp only [Fin.val_natAdd, hiff]
            _ = bpop vL + bpop vR := by
                congr 1
                · have h1 : (Finset.univ.filter (fun j : Fin (2 ^ m) => 2 ^ m - bpop vL ≤ j.val)).card = bpop vL := by
                    have hbij : (Finset.univ.filter (fun j : Fin (2 ^ m) => 2 ^ m - bpop vL ≤ j.val)).card =
                        (Finset.range (bpop vL)).card := by
                      refine Finset.card_bij (fun j _ => j.val - (2 ^ m - bpop vL)) ?_ ?_ ?_
                      · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hj ⊢; have := j.isLt; omega
                      · intro j1 h1 j2 h2 heq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
                        apply Fin.ext; omega
                      · intro x hx; simp only [Finset.mem_range] at hx
                        refine ⟨⟨2 ^ m - bpop vL + x, by omega⟩, by simp; omega, by simp⟩
                    simpa using hbij
                  conv_rhs => rw [← h1, Finset.card_filter]
                  apply Finset.sum_congr rfl; intro j _
                  by_cases h : 2 ^ m - bpop vL ≤ j.val <;> simp [h]
                · have h2 : (Finset.univ.filter (fun j : Fin (2 ^ m) => j.val < bpop vR)).card = bpop vR := by
                    have hbij : (Finset.univ.filter (fun j : Fin (2 ^ m) => j.val < bpop vR)).card =
                        (Finset.range (bpop vR)).card := by
                      refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
                      · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hj ⊢; exact hj
                      · intro j1 _ j2 _ heq; exact Fin.ext heq
                      · intro x hx; simp only [Finset.mem_range] at hx
                        exact ⟨⟨x, by omega⟩, by simp [hx], rfl⟩
                    simpa using hbij
                  conv_rhs => rw [← h2, Finset.card_filter]
                  apply Finset.sum_congr rfl; intro j _
                  by_cases h : j.val < bpop vR <;> simp [h]
        exact hcardC
      rw [hevM a hbit i, hpopC]

def bitsToNat {B : ℕ} (v : Fin B → Bool) : ℕ :=
  ∑ i : Fin B, (v i).toNat * 2 ^ i.val

lemma bitsToNat_succ {B : ℕ} (v : Fin (B + 1) → Bool) :
    bitsToNat v = (v 0).toNat + 2 * bitsToNat (fun i : Fin B => v i.succ) := by
  unfold bitsToNat
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro i _; ring

lemma bitsToNat_lt {B : ℕ} (v : Fin B → Bool) : bitsToNat v < 2 ^ B := by
  induction B with
  | zero => simp [bitsToNat]
  | succ B ih =>
    rw [bitsToNat_succ, pow_succ]
    have := ih (fun i => v i.succ)
    cases v 0 <;> simp <;> omega

lemma bitsToNat_testBit {B : ℕ} (v : Fin B → Bool) (i : Fin B) :
    (bitsToNat v).testBit i.val = v i := by
  induction B with
  | zero => exact Fin.elim0 i
  | succ B ih =>
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.val_zero, Nat.testBit_zero, bitsToNat_succ]
      cases v 0 <;> simp
    · intro j
      simp only [Fin.val_succ, Nat.testBit_succ, bitsToNat_succ]
      have hdiv : ((v 0).toNat + 2 * bitsToNat (fun k : Fin B => v k.succ)) / 2 =
          bitsToNat (fun k : Fin B => v k.succ) := by
        cases v 0
        · simp
        · simp only [Bool.toNat_true]; omega
      rw [hdiv]
      exact ih (fun k => v k.succ) j

lemma bitsToNat_inj {B : ℕ} {u v : Fin B → Bool} (h : bitsToNat u = bitsToNat v) : u = v := by
  funext i
  rw [← bitsToNat_testBit u i, ← bitsToNat_testBit v i, h]

def xorDotList {n : ℕ} (row v : Fin n → Bool) (l : List (Fin n)) (acc : Bool) : Bool :=
  l.foldl (fun a j => Bool.xor a (row j && v j)) acc

def xorDot {n : ℕ} (row v : Fin n → Bool) : Bool :=
  xorDotList row v (List.finRange n) false

lemma xorDotList_xor {n : ℕ} (row u v : Fin n → Bool) (l : List (Fin n)) (a b : Bool) :
    xorDotList row (fun j => Bool.xor (u j) (v j)) l (Bool.xor a b) =
      Bool.xor (xorDotList row u l a) (xorDotList row v l b) := by
  induction l generalizing a b with
  | nil => rfl
  | cons j l ih =>
    simp only [xorDotList, List.foldl_cons]
    have hstep : Bool.xor (Bool.xor a b) (row j && Bool.xor (u j) (v j)) =
        Bool.xor (Bool.xor a (row j && u j)) (Bool.xor b (row j && v j)) := by
      cases a <;> cases b <;> cases row j <;> cases u j <;> cases v j <;> rfl
    rw [hstep]; exact ih _ _

lemma xorDot_xor {n : ℕ} (row u v : Fin n → Bool) :
    xorDot row (fun j => Bool.xor (u j) (v j)) = Bool.xor (xorDot row u) (xorDot row v) :=
  xorDotList_xor row u v (List.finRange n) false false

lemma xorDotList_not_acc {n : ℕ} (row v : Fin n → Bool) (l : List (Fin n)) (acc : Bool) :
    xorDotList row v l (!acc) = !(xorDotList row v l acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih =>
    simp only [xorDotList, List.foldl_cons]
    have hstep : Bool.xor (!acc) (row j && v j) = !(Bool.xor acc (row j && v j)) := by
      cases acc <;> cases row j <;> cases v j <;> rfl
    rw [hstep]; exact ih _

lemma xorDotList_congr {n : ℕ} (r1 r2 v : Fin n → Bool) (l : List (Fin n)) (acc : Bool)
    (heq : ∀ j ∈ l, r1 j = r2 j) :
    xorDotList r1 v l acc = xorDotList r2 v l acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih =>
    simp only [xorDotList, List.foldl_cons]
    rw [heq j (List.mem_cons_self ..)]
    exact ih _ (fun k hk => heq k (List.mem_cons_of_mem _ hk))

lemma xorDotList_toggle {n : ℕ} (row v : Fin n → Bool) (i₀ : Fin n) (hv : v i₀ = true)
    (l : List (Fin n)) (hnodup : l.Nodup) (hmem : i₀ ∈ l) (acc : Bool) :
    xorDotList (fun j => if j = i₀ then !(row j) else row j) v l acc =
      !(xorDotList row v l acc) := by
  induction l generalizing acc with
  | nil => simp at hmem
  | cons j l ih =>
    rw [List.nodup_cons] at hnodup
    simp only [xorDotList, List.foldl_cons]
    by_cases hji : j = i₀
    · subst hji
      simp only [↓reduceIte, hv, Bool.and_true]
      have hstep : Bool.xor acc (!(row j)) = !(Bool.xor acc (row j)) := by
        cases acc <;> cases row j <;> rfl
      rw [hstep]
      change xorDotList (fun j_1 => if j_1 = j then !row j_1 else row j_1) v l (!(Bool.xor acc (row j))) =
        !(xorDotList row v l (Bool.xor acc (row j)))
      rw [xorDotList_not_acc]
      congr 1
      apply xorDotList_congr
      intro k hk
      have hne : k ≠ j := fun h => hnodup.1 (h ▸ hk)
      simp [hne]
    · simp only [hji, ↓reduceIte]
      have hmem' : i₀ ∈ l := (List.mem_cons.mp hmem).resolve_left (Ne.symm hji)
      exact ih hnodup.2 hmem' _

lemma card_xorDot_false {n : ℕ} (hn : 1 ≤ n) (v : Fin n → Bool) (i₀ : Fin n) (hv : v i₀ = true) :
    (Finset.univ.filter (fun row : Fin n → Bool => xorDot row v = false)).card = 2 ^ (n - 1) := by
  set S0 := Finset.univ.filter (fun row : Fin n → Bool => xorDot row v = false)
  set S1 := Finset.univ.filter (fun row : Fin n → Bool => xorDot row v = true)
  let toggle : (Fin n → Bool) → (Fin n → Bool) := fun row j => if j = i₀ then !(row j) else row j
  have hflip : ∀ row, xorDot (toggle row) v = !(xorDot row v) := fun row =>
    xorDotList_toggle row v i₀ hv (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i₀) false
  have hcard_eq : S0.card = S1.card := by
    refine Finset.card_bij (fun row _ => toggle row) ?_ ?_ ?_
    · intro row hrow
      simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hrow ⊢
      rw [hflip, hrow]; rfl
    · intro r1 _ r2 _ heq
      funext j
      have hj := congrFun heq j
      dsimp [toggle] at hj
      by_cases hji : j = i₀
      · simp only [hji, ↓reduceIte] at hj
        cases h1 : r1 j <;> cases h2 : r2 j <;> simp_all
      · simp only [hji, ↓reduceIte] at hj; exact hj
    · intro row hrow
      refine ⟨toggle row, ?_, ?_⟩
      · simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hrow ⊢
        rw [hflip, hrow]; rfl
      · funext j; dsimp [toggle]; split_ifs <;> simp
  have htot : S0.card + S1.card = 2 ^ n := by
    have hunion : S0 ∪ S1 = Finset.univ := by
      ext row
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases xorDot row v <;> simp
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro row h0 h1
      simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
      rw [h0] at h1; exact Bool.noConfusion h1
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  omega

def sXor {m : ℕ} (a b : Fin (2 ^ m)) : Fin (2 ^ m) :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow a.isLt b.isLt⟩

lemma sXor_self_cancel {m : ℕ} (a b : Fin (2 ^ m)) : sXor (sXor a b) b = a := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  simp [sXor]

def hashCol {m n : ℕ} (A : Fin m → Fin n → Bool) (i : Fin n) : Fin (2 ^ m) :=
  ⟨bitsToNat (fun r : Fin m => A r i), bitsToNat_lt _⟩

def hashPrefix {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Fin n → Bool) :
    (l : ℕ) → l ≤ n → Fin (2 ^ m)
  | 0, _ => ⟨0, by positivity⟩
  | l + 1, hl =>
    let prev := hashPrefix A x l (by omega)
    if x ⟨l, by omega⟩ then sXor prev (hashCol A ⟨l, by omega⟩) else prev

def hashVal {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Fin n → Bool) : Fin (2 ^ m) :=
  hashPrefix A x n le_rfl

lemma hashPrefix_testBit {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Fin n → Bool)
    (l : ℕ) (hl : l ≤ n) (r : Fin m) :
    (hashPrefix A x l hl).val.testBit r.val =
      xorDotList (A r) x ((List.finRange n).take l) false := by
  induction l with
  | zero =>
    simp [hashPrefix, xorDotList]
  | succ l ih =>
    have htake : (List.finRange n).take (l + 1) = (List.finRange n).take l ++ [⟨l, by omega⟩] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]; simp
    rw [htake]
    unfold xorDotList
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    dsimp only [hashPrefix]
    have ih' := ih (by omega)
    unfold xorDotList at ih'
    cases hx : x ⟨l, by omega⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.xor_false]
      exact ih'
    · simp only [↓reduceIte, Bool.and_true, sXor, hashCol, Nat.testBit_xor, bitsToNat_testBit]
      rw [ih']

lemma hashVal_eq_iff {m n : ℕ} (A : Fin m → Fin n → Bool) (x y : Fin n → Bool) :
    hashVal A x = hashVal A y ↔
      ∀ r : Fin m, xorDot (A r) (fun i => Bool.xor (x i) (y i)) = false := by
  constructor
  · intro h r
    rw [xorDot_xor]
    have hx := hashPrefix_testBit A x n le_rfl r
    have hy := hashPrefix_testBit A y n le_rfl r
    have htake : (List.finRange n).take n = List.finRange n := by simp
    simp only [htake] at hx hy
    have hbit : (hashVal A x).val.testBit r.val = (hashVal A y).val.testBit r.val := by rw [h]
    change (hashPrefix A x n le_rfl).val.testBit r.val = (hashPrefix A y n le_rfl).val.testBit r.val at hbit
    rw [hx, hy] at hbit
    unfold xorDot
    rw [hbit]
    cases xorDotList (A r) y (List.finRange n) false <;> rfl
  · intro h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < m
    · have hx := hashPrefix_testBit A x n le_rfl ⟨k, hk⟩
      have hy := hashPrefix_testBit A y n le_rfl ⟨k, hk⟩
      have htake : (List.finRange n).take n = List.finRange n := by simp
      simp only [htake] at hx hy
      have hr := h ⟨k, hk⟩
      rw [xorDot_xor] at hr
      change (hashPrefix A x n le_rfl).val.testBit k = (hashPrefix A y n le_rfl).val.testBit k
      rw [hx, hy]
      unfold xorDot at hr
      cases h1 : xorDotList (A ⟨k, hk⟩) x (List.finRange n) false <;>
        cases h2 : xorDotList (A ⟨k, hk⟩) y (List.finRange n) false <;> simp_all
    · have hmk : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (hashVal A x).isLt hmk)
      have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (hashVal A y).isLt hmk)
      rw [h1, h2]

def candSet (n q : ℕ) (ρ_in : Fin n → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x : Fin n → Bool =>
    (∀ i : Fin n, ∀ b : Bool, ρ_in i = some b → x i = b) ∧
    ∃ path : Fin (n + 1) → Fin q, path 0 = path (Fin.last n) ∧
      ∀ i : Fin n, blocked (i, path i.castSucc, x i, path i.succ) = false)

lemma card_bad_hash_lt {m n K : ℕ} (hn : 1 ≤ n) (hM : (K + 1) ^ 2 ≤ 2 ^ m)
    (S : Finset (Fin n → Bool)) (hS : S.card ≤ K) :
    2 * (Finset.univ.filter (fun A : Fin m → Fin n → Bool =>
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ hashVal A x = hashVal A y)).card < 2 ^ (m * n) := by
  set pairs := (S ×ˢ S).filter (fun p : (Fin n → Bool) × (Fin n → Bool) => bitsToNat p.1 < bitsToNat p.2)
  have hpairs_le : 2 * pairs.card ≤ S.card * S.card := by
    set pairsRev := (S ×ˢ S).filter (fun p : (Fin n → Bool) × (Fin n → Bool) => bitsToNat p.2 < bitsToNat p.1)
    have hdisj : Disjoint pairs pairsRev := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [pairs, pairsRev, Finset.mem_filter] at h1 h2
      omega
    have hcard_rev : pairsRev.card = pairs.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp; simp only [pairs, pairsRev, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p1 _ p2 _ heq; exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
      · intro p hp; refine ⟨(p.2, p.1), ?_, rfl⟩
        simp only [pairs, pairsRev, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    have hsub : pairs ∪ pairsRev ⊆ S ×ˢ S := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hcard_rev, Finset.card_product] at h1
    omega
  let collFor (p : (Fin n → Bool) × (Fin n → Bool)) : Finset (Fin m → Fin n → Bool) :=
    Finset.univ.filter (fun A => hashVal A p.1 = hashVal A p.2)
  have hsub_bad : Finset.univ.filter (fun A : Fin m → Fin n → Bool =>
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ hashVal A x = hashVal A y) ⊆ pairs.biUnion collFor := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rcases hA with ⟨x, hx, y, hy, hne, heq⟩
    have hbn : bitsToNat x ≠ bitsToNat y := fun h => hne (bitsToNat_inj h)
    by_cases hlt : bitsToNat x < bitsToNat y
    · exact Finset.mem_biUnion.mpr ⟨(x, y), by simp [pairs, hx, hy, hlt], by simp [collFor, heq]⟩
    · exact Finset.mem_biUnion.mpr ⟨(y, x), by simp [pairs, hx, hy]; omega, by simp [collFor, heq.symm]⟩
  have hcoll_card : ∀ p ∈ pairs, (collFor p).card = 2 ^ (m * (n - 1)) := by
    intro p hp
    simp only [pairs, Finset.mem_filter] at hp
    have hne : p.1 ≠ p.2 := fun h => by rw [h] at hp; omega
    have hdiff : ∃ i₀ : Fin n, Bool.xor (p.1 i₀) (p.2 i₀) = true := by
      by_contra hall
      push Not at hall
      apply hne
      funext i
      have hi := hall i
      cases h1 : p.1 i <;> cases h2 : p.2 i <;> simp_all
    rcases hdiff with ⟨i₀, hi₀⟩
    let v : Fin n → Bool := fun i => Bool.xor (p.1 i) (p.2 i)
    have hpi : collFor p = Fintype.piFinset (fun _ : Fin m =>
        Finset.univ.filter (fun row : Fin n → Bool => xorDot row v = false)) := by
      ext A
      simp only [collFor, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        hashVal_eq_iff, v]
    rw [hpi, Fintype.card_piFinset]
    simp only [card_xorDot_false hn v i₀ hi₀, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul, Nat.mul_comm]
  have hle1 : (Finset.univ.filter (fun A : Fin m → Fin n → Bool =>
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ hashVal A x = hashVal A y)).card ≤ pairs.card * 2 ^ (m * (n - 1)) := by
    calc _ ≤ (pairs.biUnion collFor).card := Finset.card_le_card hsub_bad
      _ ≤ ∑ p ∈ pairs, (collFor p).card := Finset.card_biUnion_le
      _ = ∑ _p ∈ pairs, 2 ^ (m * (n - 1)) := Finset.sum_congr rfl hcoll_card
      _ = pairs.card * 2 ^ (m * (n - 1)) := by simp
  have h2m : 2 * pairs.card < 2 ^ m := by
    have : S.card * S.card < (K + 1) ^ 2 := by nlinarith
    omega
  have hpow : 2 ^ m * 2 ^ (m * (n - 1)) = 2 ^ (m * n) := by
    rw [← pow_add]
    congr 1
    have : n = (n - 1) + 1 := by omega
    conv_rhs => rw [this, mul_add, mul_one]
    omega
  calc 2 * (Finset.univ.filter _).card
      ≤ 2 * (pairs.card * 2 ^ (m * (n - 1))) := Nat.mul_le_mul_left 2 hle1
    _ = (2 * pairs.card) * 2 ^ (m * (n - 1)) := by ring
    _ < 2 ^ m * 2 ^ (m * (n - 1)) := Nat.mul_lt_mul_of_pos_right h2m (by positivity)
    _ = 2 ^ (m * n) := hpow

lemma hashFamily_exists (n q K : ℕ) :
    let m := 2 * Nat.clog 2 (K + 1)
    let R := 2 * n * q ^ 2 + 2 * n + 1
    ∃ H : Fin R → (Fin m → Fin n → Bool),
      ∀ (ρ_in : Fin n → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
        (candSet n q ρ_in blocked).card ≤ K →
        ∃ idx : Fin R, ∀ x ∈ candSet n q ρ_in blocked, ∀ y ∈ candSet n q ρ_in blocked,
          hashVal (H idx) x = hashVal (H idx) y → x = y := by
  intro m R
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨fun _ _ _ => false, fun ρ_in blocked _ => ⟨⟨0, by omega⟩, fun x _ y _ _ => ?_⟩⟩
    funext i; exact Fin.elim0 i
  · have hn : 1 ≤ n := by omega
    have hM : (K + 1) ^ 2 ≤ 2 ^ m := by
      have h1 : K + 1 ≤ 2 ^ Nat.clog 2 (K + 1) := Nat.le_pow_clog (by omega) (K + 1)
      have h2 : (K + 1) ^ 2 ≤ (2 ^ Nat.clog 2 (K + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      have h3 : (2 ^ Nat.clog 2 (K + 1)) ^ 2 = 2 ^ m := by rw [← pow_mul, Nat.mul_comm]
      omega
    let Inst := (Fin n → Option Bool) × ((Fin n × Fin q × Bool × Fin q) → Bool)
    set Small := (Finset.univ : Finset Inst).filter (fun p => (candSet n q p.1 p.2).card ≤ K)
    let badA (p : Inst) : Finset (Fin m → Fin n → Bool) :=
      Finset.univ.filter (fun A => ∃ x ∈ candSet n q p.1 p.2, ∃ y ∈ candSet n q p.1 p.2,
        x ≠ y ∧ hashVal A x = hashVal A y)
    let badH (p : Inst) : Finset (Fin R → Fin m → Fin n → Bool) :=
      Fintype.piFinset (fun _ : Fin R => badA p)
    set Bad := Small.biUnion badH
    have hInstCard : Fintype.card Inst < 2 ^ R := by
      have h1 : Fintype.card (Fin n → Option Bool) = 3 ^ n := by
        rw [Fintype.card_fun, Fintype.card_option, Fintype.card_bool, Fintype.card_fin]
      have h2 : 3 ^ n ≤ 2 ^ (2 * n) := by
        rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) n
      have h3 : Fintype.card ((Fin n × Fin q × Bool × Fin q) → Bool) = 2 ^ (2 * n * q ^ 2) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_bool]
        congr 1; ring
      rw [Fintype.card_prod, h1, h3]
      calc 3 ^ n * 2 ^ (2 * n * q ^ 2)
          ≤ 2 ^ (2 * n) * 2 ^ (2 * n * q ^ 2) := Nat.mul_le_mul_right _ h2
        _ = 2 ^ (2 * n * q ^ 2 + 2 * n) := by rw [← pow_add]; congr 1; ring
        _ < 2 ^ R := Nat.pow_lt_pow_right (by omega) (by omega)
    have hSmallLt : Small.card < 2 ^ R :=
      lt_of_le_of_lt (Finset.card_le_univ _) (by simpa [Finset.card_univ] using hInstCard)
    have hBadOne : ∀ p ∈ Small, 2 ^ R * (badH p).card ≤ (2 ^ (m * n)) ^ R := by
      intro p hp
      simp only [Small, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hlt := card_bad_hash_lt hn hM (candSet n q p.1 p.2) hp
      have hcard : (badH p).card = (badA p).card ^ R := by
        rw [Fintype.card_piFinset]; simp
      rw [hcard, ← mul_pow]
      exact Nat.pow_le_pow_left (le_of_lt hlt) R
    have hBadLt : Bad.card < (Finset.univ : Finset (Fin R → Fin m → Fin n → Bool)).card := by
      have htot : (Finset.univ : Finset (Fin R → Fin m → Fin n → Bool)).card = (2 ^ (m * n)) ^ R := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
          ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1; ring
      rw [htot]
      have h1 : 2 ^ R * Bad.card ≤ ∑ p ∈ Small, 2 ^ R * (badH p).card := by
        rw [← Finset.mul_sum]
        exact Nat.mul_le_mul_left _ Finset.card_biUnion_le
      have h2 : ∑ p ∈ Small, 2 ^ R * (badH p).card ≤ Small.card * (2 ^ (m * n)) ^ R := by
        calc ∑ p ∈ Small, 2 ^ R * (badH p).card
            ≤ ∑ _p ∈ Small, (2 ^ (m * n)) ^ R := Finset.sum_le_sum hBadOne
          _ = Small.card * (2 ^ (m * n)) ^ R := by simp
      have h3 : Small.card * (2 ^ (m * n)) ^ R < 2 ^ R * (2 ^ (m * n)) ^ R :=
        Nat.mul_lt_mul_of_pos_right hSmallLt (by positivity)
      exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt (le_trans h1 h2) h3)
    have hne : (Finset.univ \ Bad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      exact not_lt_of_ge (Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)) hBadLt
    rcases hne with ⟨H, hH⟩
    rw [Finset.mem_sdiff] at hH
    refine ⟨H, fun ρ_in blocked hcard => ?_⟩
    by_contra hall
    push Not at hall
    apply hH.2
    refine Finset.mem_biUnion.mpr ⟨(ρ_in, blocked), by simp [Small, hcard], ?_⟩
    rw [Fintype.mem_piFinset]
    intro idx
    rcases hall idx with ⟨x, hx, y, hy, heq, hne⟩
    simp only [badA, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx, y, hy, hne, heq⟩

noncomputable def ofFintype {ι : Type} [Fintype ι] (f : ι → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (Fintype.card ι) => f ((Fintype.equivFin ι).symm i))

lemma ofFintype_length {ι : Type} [Fintype ι] (f : ι → ℕ) :
    (ofFintype f).length = Fintype.card ι := by
  simp [ofFintype]

lemma mem_ofFintype_iff {ι : Type} [Fintype ι] (f : ι → ℕ) (w : ℕ) :
    w ∈ ofFintype f ↔ ∃ x : ι, f x = w := by
  constructor
  · intro hw
    rw [ofFintype, List.mem_iff_getElem] at hw
    rcases hw with ⟨i, hi, rfl⟩
    simp only [List.length_ofFn] at hi
    rw [List.getElem_ofFn]
    exact ⟨(Fintype.equivFin ι).symm ⟨i, hi⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    rw [ofFintype, List.mem_iff_getElem]
    refine ⟨(Fintype.equivFin ι x).val, by simp, ?_⟩
    rw [List.getElem_ofFn]
    simp

lemma evalList_ofFintype_true {ι : Type} [Fintype ι] (g : ℕ → Bool) (f : ι → ℕ) :
    evalList true g (ofFintype f) = true ↔ ∀ x : ι, g (f x) = true := by
  simp only [evalList, ↓reduceIte, List.all_eq_true, mem_ofFintype_iff]
  constructor
  · intro h x; exact h (f x) ⟨x, rfl⟩
  · intro h w ⟨x, hx⟩; subst hx; exact h x

lemma evalList_ofFintype_false {ι : Type} [Fintype ι] (g : ℕ → Bool) (f : ι → ℕ) :
    evalList false g (ofFintype f) = true ↔ ∃ x : ι, g (f x) = true := by
  simp only [evalList, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, mem_ofFintype_iff]
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, hgw⟩; exact ⟨x, hgw⟩
  · rintro ⟨x, hgx⟩; exact ⟨f x, ⟨x, rfl⟩, hgx⟩

def finBuild {α : Type} (K : ℕ) (step : List MGate → Fin K → List MGate × α)
    (G : List MGate) : (k : ℕ) → k ≤ K → List MGate × (Fin k → α)
  | 0, _ => (G, fun i => Fin.elim0 i)
  | k + 1, hk =>
    let r1 := finBuild K step G k (by omega)
    let r2 := step r1.1 ⟨k, by omega⟩
    (r2.1, fun i => if h : i.val < k then r1.2 ⟨i.val, h⟩ else r2.2)

lemma finBuild_spec {α : Type} (N K cost : ℕ) (step : List MGate → Fin K → List MGate × α)
    (Inv : List MGate → Fin K → α → Prop)
    (hmono : ∀ {G1 G2 : List MGate} {idx : Fin K} {v : α}, Extends G1 G2 → Inv G1 idx v → Inv G2 idx v)
    (G0 : List MGate) (hwf0 : WellFormed N G0)
    (hstep : ∀ (G : List MGate) (idx : Fin K), WellFormed N G → Extends G0 G →
      WellFormed N (step G idx).1 ∧ Extends G (step G idx).1 ∧
      (step G idx).1.length ≤ G.length + cost ∧ Inv (step G idx).1 idx (step G idx).2) :
    ∀ (k : ℕ) (hk : k ≤ K),
      let r := finBuild K step G0 k hk
      WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + k * cost ∧
      ∀ i : Fin k, Inv r.1 ⟨i.val, by omega⟩ (r.2 i) := by
  intro k hk
  induction k with
  | zero => exact ⟨hwf0, extends_rfl G0, by simp [finBuild], fun i => Fin.elim0 i⟩
  | succ k ih =>
    rcases ih (by omega) with ⟨hwf1, hext1, hlen1, hinv1⟩
    set r1 := finBuild K step G0 k (by omega) with hr1
    rcases hstep r1.1 ⟨k, by omega⟩ hwf1 hext1 with ⟨hwf2, hext2, hlen2, hinv2⟩
    set r2 := step r1.1 ⟨k, by omega⟩ with hr2
    dsimp only [finBuild]
    rw [← hr1, ← hr2]
    refine ⟨hwf2, extends_trans hext1 hext2, ?_, ?_⟩
    · have : (k + 1) * cost = k * cost + cost := by ring
      omega
    · intro i
      split_ifs with hi
      · exact hmono hext2 (hinv1 ⟨i.val, hi⟩)
      · have hkeq : (⟨i.val, by omega⟩ : Fin K) = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
        rw [hkeq]; exact hinv2

noncomputable def fintypeBuild {ι : Type} [Fintype ι] {α : Type}
    (step : List MGate → ι → List MGate × α) (G : List MGate) : List MGate × (ι → α) :=
  let r := finBuild (Fintype.card ι) (fun G' idx => step G' ((Fintype.equivFin ι).symm idx))
    G (Fintype.card ι) le_rfl
  (r.1, fun x => r.2 (Fintype.equivFin ι x))

lemma fintypeBuild_spec {ι : Type} [Fintype ι] {α : Type} (N cost : ℕ)
    (step : List MGate → ι → List MGate × α)
    (Inv : List MGate → ι → α → Prop)
    (hmono : ∀ {G1 G2 : List MGate} {x : ι} {v : α}, Extends G1 G2 → Inv G1 x v → Inv G2 x v)
    (G0 : List MGate) (hwf0 : WellFormed N G0)
    (hstep : ∀ (G : List MGate) (x : ι), WellFormed N G → Extends G0 G →
      WellFormed N (step G x).1 ∧ Extends G (step G x).1 ∧
      (step G x).1.length ≤ G.length + cost ∧ Inv (step G x).1 x (step G x).2) :
    let r := fintypeBuild step G0
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + Fintype.card ι * cost ∧
    ∀ x : ι, Inv r.1 x (r.2 x) := by
  have h := finBuild_spec N (Fintype.card ι) cost
    (fun G' idx => step G' ((Fintype.equivFin ι).symm idx))
    (fun G' idx v => Inv G' ((Fintype.equivFin ι).symm idx) v)
    (fun hext hinv => hmono hext hinv) G0 hwf0
    (fun G idx hwf hext => hstep G ((Fintype.equivFin ι).symm idx) hwf hext)
    (Fintype.card ι) le_rfl
  rcases h with ⟨hwf, hext, hlen, hinv⟩
  refine ⟨hwf, hext, hlen, fun x => ?_⟩
  have hx := hinv (Fintype.equivFin ι x)
  simpa [fintypeBuild] using hx

abbrev PinType (n q t : ℕ) := ((Fin n ⊕ Fin t) × Bool) ⊕ (Fin n × Fin q × Bool × Fin q)

noncomputable def pinWire (n q t : ℕ) (p : PinType n q t) : ℕ :=
  2 + (Fintype.equivFin (PinType n q t) p).val

lemma pinWire_lt (n q t : ℕ) (G : List MGate) (p : PinType n q t) :
    pinWire n q t p < 2 + Fintype.card (PinType n q t) + G.length := by
  unfold pinWire
  have := (Fintype.equivFin (PinType n q t) p).isLt
  omega

lemma pinWire_depth (n q t : ℕ) (G : List MGate) (p : PinType n q t) :
    (mdepths (2 + Fintype.card (PinType n q t)) G).getD (pinWire n q t p) 0 = 0 := by
  apply mdepths_base
  unfold pinWire
  have := (Fintype.equivFin (PinType n q t) p).isLt
  omega

lemma pinWire_val (n q t : ℕ) (G : List MGate) (a : PinType n q t → Bool) (p : PinType n q t) :
    (mrun G a).getD (pinWire n q t p) false = a p :=
  mrun_input G a p

def mkBits {n q t : ℕ} (ρ : (Fin n ⊕ Fin t) → Option Bool)
    (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) : PinType n q t → Bool :=
  Sum.elim (fun p => decide (ρ p.1 = some p.2)) blocked

def edgeOpen {n q : ℕ} (ρ_in : Fin n → Option Bool)
    (blocked : (Fin n × Fin q × Bool × Fin q) → Bool)
    (opt : Option (Fin n × Bool)) (i : Fin n) (u : Fin q) (b : Bool) (v : Fin q) : Prop :=
  blocked (i, u, b, v) = false ∧
  ρ_in i ≠ some (!b) ∧
  (∀ i₀ b₀, opt = some (i₀, b₀) → i = i₀ → b = b₀)

def HasPath (n q m : ℕ) (A : Fin m → Fin n → Bool) (ρ_in : Fin n → Option Bool)
    (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (opt : Option (Fin n × Bool)) :
    (l : ℕ) → l ≤ n → Fin q → Fin q → Fin (2 ^ m) → Prop
  | 0, _, u, v, s => u = v ∧ s.val = 0
  | l + 1, hl, u, v, s =>
    ∃ (w : Fin q) (b : Bool),
      HasPath n q m A ρ_in blocked opt l (by omega) u w
        (if b then sXor s (hashCol A ⟨l, by omega⟩) else s) ∧
      edgeOpen ρ_in blocked opt ⟨l, by omega⟩ w b v

lemma hashPrefix_congr {m n : ℕ} (A : Fin m → Fin n → Bool) (x y : Fin n → Bool)
    (l : ℕ) (hl : l ≤ n) (heq : ∀ i : Fin n, i.val < l → x i = y i) :
    hashPrefix A x l hl = hashPrefix A y l hl := by
  induction l with
  | zero => rfl
  | succ l ih =>
    dsimp only [hashPrefix]
    rw [ih (by omega) (fun i hi => heq i (by omega)), heq ⟨l, by omega⟩ (by simp)]

lemma hasPath_iff (n q m : ℕ) (A : Fin m → Fin n → Bool) (ρ_in : Fin n → Option Bool)
    (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (opt : Option (Fin n × Bool))
    (l : ℕ) (hl : l ≤ n) (u v : Fin q) (s : Fin (2 ^ m)) :
    HasPath n q m A ρ_in blocked opt l hl u v s ↔
      ∃ (x : Fin n → Bool) (path : Fin (l + 1) → Fin q),
        path 0 = u ∧ path ⟨l, Nat.lt_succ_self l⟩ = v ∧
        hashPrefix A x l hl = s ∧
        ∀ i : Fin l, edgeOpen ρ_in blocked opt ⟨i.val, by omega⟩ (path i.castSucc) (x ⟨i.val, by omega⟩) (path i.succ) := by
  induction l generalizing v s with
  | zero =>
    constructor
    · rintro ⟨rfl, hs⟩
      refine ⟨fun _ => false, fun _ => u, rfl, rfl, Fin.ext (by simpa [hashPrefix] using hs.symm), fun i => Fin.elim0 i⟩
    · rintro ⟨_, path, h0, hlast, hs, _⟩
      refine ⟨h0.symm.trans hlast, ?_⟩
      simpa [hashPrefix] using congrArg Fin.val hs.symm
  | succ l ih =>
    constructor
    · rintro ⟨w, b, hp, he⟩
      rcases (ih (by omega) w _).mp hp with ⟨x, path, h0, hlast, hpre, hedges⟩
      let x' : Fin n → Bool := fun j => if j.val = l then b else x j
      let path' : Fin (l + 2) → Fin q := fun k => if hk : k.val ≤ l then path ⟨k.val, by omega⟩ else v
      refine ⟨x', path', ?_, ?_, ?_, ?_⟩
      · simp [path', h0]
      · simp [path']
      · dsimp only [hashPrefix]
        have hcongr : hashPrefix A x' l (by omega) = hashPrefix A x l (by omega) :=
          hashPrefix_congr A x' x l (by omega) (fun j hj => by simp [x', Nat.ne_of_lt hj])
        rw [hcongr, hpre]
        simp only [x', ↓reduceIte]
        cases b
        · rfl
        · exact sXor_self_cancel s (hashCol A ⟨l, by omega⟩)
      · intro i
        by_cases hil : i.val < l
        · have hx' : x' ⟨i.val, by omega⟩ = x ⟨i.val, by omega⟩ := by simp [x', Nat.ne_of_lt hil]
          have hp1 : path' i.castSucc = path ⟨i.val, by omega⟩ := by
            simp only [path', Fin.val_castSucc, show i.val ≤ l by omega, ↓reduceDIte]
          have hp2 : path' i.succ = path ⟨i.val + 1, by omega⟩ := by
            simp only [path', Fin.val_succ, show i.val + 1 ≤ l by omega, ↓reduceDIte]
          rw [hx', hp1, hp2]
          exact hedges ⟨i.val, hil⟩
        · have heql : i.val = l := by omega
          have hx' : x' ⟨i.val, by omega⟩ = b := by simp [x', heql]
          have hp1 : path' i.castSucc = w := by
            simp only [path', Fin.val_castSucc, show i.val ≤ l by omega, ↓reduceDIte]
            convert hlast using 2; exact Fin.ext heql
          have hp2 : path' i.succ = v := by
            simp only [path', Fin.val_succ, show ¬ (i.val + 1 ≤ l) by omega, ↓reduceDIte]
          rw [hx', hp1, hp2]
          have hfin : (⟨i.val, by omega⟩ : Fin n) = ⟨l, by omega⟩ := Fin.ext heql
          rw [hfin]; exact he
    · rintro ⟨x, path, h0, hlast, hpre, hedges⟩
      refine ⟨path ⟨l, by omega⟩, x ⟨l, by omega⟩, ?_, ?_⟩
      · rw [ih (by omega)]
        refine ⟨x, fun k => path k.castSucc, h0, rfl, ?_, fun i => hedges i.castSucc⟩
        dsimp only [hashPrefix] at hpre
        cases hx : x ⟨l, by omega⟩
        · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hpre ⊢; exact hpre
        · simp only [hx, ↓reduceIte] at hpre ⊢
          rw [← hpre, sXor_self_cancel]
      · have hlastE := hedges ⟨l, by omega⟩
        have hsucc : (⟨l, by omega⟩ : Fin (l + 1)).succ = ⟨l + 1, Nat.lt_succ_self (l + 1)⟩ := Fin.ext rfl
        rw [hsucc, hlast] at hlastE
        exact hlastE

lemma exists_hasPath_cycle_iff (n q m : ℕ) (A : Fin m → Fin n → Bool) (ρ_in : Fin n → Option Bool)
    (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (opt : Option (Fin n × Bool)) (s : Fin (2 ^ m)) :
    (∃ u : Fin q, HasPath n q m A ρ_in blocked opt n le_rfl u u s) ↔
      ∃ x ∈ candSet n q ρ_in blocked, hashVal A x = s ∧
        ∀ i₀ b₀, opt = some (i₀, b₀) → x i₀ = b₀ := by
  constructor
  · rintro ⟨u, hp⟩
    rcases (hasPath_iff n q m A ρ_in blocked opt n le_rfl u u s).mp hp with ⟨x, path, h0, hlast, hpre, hedges⟩
    refine ⟨x, ?_, hpre, ?_⟩
    · simp only [candSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ⟨path, h0.trans hlast.symm, fun i => (hedges i).1⟩⟩
      intro i b hρ
      have hne := (hedges i).2.1
      cases hx : x i <;> cases b <;> simp_all
    · intro i₀ b₀ hopt
      exact (hedges i₀).2.2 i₀ b₀ hopt rfl
  · rintro ⟨x, hx, hhash, hopt⟩
    simp only [candSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨hρ, path, hcyc, hblk⟩
    refine ⟨path 0, (hasPath_iff n q m A ρ_in blocked opt n le_rfl (path 0) (path 0) s).mpr ?_⟩
    refine ⟨x, path, rfl, hcyc.symm, hhash, fun i => ⟨hblk i, ?_, ?_⟩⟩
    · intro hEq
      have h := hρ i (!(x i)) hEq
      revert h; cases x i <;> decide
    · intro i₀ b₀ ho hi
      rw [hi]; exact hopt i₀ b₀ ho

noncomputable def buildBaseEdges (n q t : ℕ) (G : List MGate) :
    List MGate × ((Fin n × Fin q × Bool × Fin q) → ℕ) :=
  let N := 2 + Fintype.card (PinType n q t)
  fintypeBuild (fun G' e =>
    addMGate N G' false (pinWire n q t (Sum.inr e)) (pinWire n q t (Sum.inl (Sum.inl e.1, !e.2.2.1)))) G

lemma buildBaseEdges_spec (n q t : ℕ) (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0) :
    let N := 2 + Fintype.card (PinType n q t)
    let r := buildBaseEdges n q t G0
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + 2 * n * q ^ 2 ∧
    (∀ e, r.2 e < N + r.1.length) ∧
    (∀ e, (mdepths N r.1).getD (r.2 e) 0 ≤ 1) ∧
    (∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) e,
      (mrun r.1 (mkBits ρ blocked)).getD (r.2 e) false = true ↔
        ¬ (blocked e = false ∧ ρ (Sum.inl e.1) ≠ some (!e.2.2.1))) := by
  let N := 2 + Fintype.card (PinType n q t)
  let Inv : List MGate → (Fin n × Fin q × Bool × Fin q) → ℕ → Prop := fun G e w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ 1 ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun G (mkBits ρ blocked)).getD w false = true ↔
        ¬ (blocked e = false ∧ ρ (Sum.inl e.1) ≠ some (!e.2.2.1))
  have hmono : ∀ {G1 G2 : List MGate} {e} {w}, Extends G1 G2 → Inv G1 e w → Inv G2 e w := by
    intro G1 G2 e w hext ⟨hlt, hd, hval⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) N), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hval ρ blocked
  have hres := fintypeBuild_spec (ι := Fin n × Fin q × Bool × Fin q) N 1
    (fun G' e => addMGate N G' false (pinWire n q t (Sum.inr e)) (pinWire n q t (Sum.inl (Sum.inl e.1, !e.2.2.1))))
    Inv hmono G0 hwf0 (fun G e hwf _ => by
      refine ⟨addMGate_wf hwf false (pinWire_lt n q t G _) (pinWire_lt n q t G _),
        addMGate_extends N G false _ _, by rw [addMGate_len], addMGate_out_lt N G false _ _, ?_, ?_⟩
      · rw [addMGate_depth, pinWire_depth, pinWire_depth]; simp
      · intro ρ blocked
        rw [addMGate_val]
        simp only [Bool.false_eq_true, ↓reduceIte, pinWire_val, mkBits, Sum.elim_inr, Sum.elim_inl,
          Bool.or_eq_true, decide_eq_true_eq]
        cases blocked e <;> simp)
  rcases hres with ⟨hwf, hext, hlen, hinv⟩
  have hcard : Fintype.card (Fin n × Fin q × Bool × Fin q) = 2 * n * q ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  rw [hcard, mul_one] at hlen
  exact ⟨hwf, hext, hlen, fun e => (hinv e).1, fun e => (hinv e).2.1, fun ρ blocked e => (hinv e).2.2 ρ blocked⟩

def optEdgeWire {n q : ℕ} (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (opt : Option (Fin n × Bool)) (i : Fin n) (w : Fin q) (b : Bool) (v : Fin q) : ℕ :=
  match opt with
  | some (i₀, b₀) => if i = i₀ ∧ b ≠ b₀ then 1 else baseEdge (i, w, b, v)
  | none => baseEdge (i, w, b, v)

lemma optEdgeWire_spec {n q t : ℕ} (G : List MGate)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (hbd : ∀ e, baseEdge e < 2 + Fintype.card (PinType n q t) + G.length)
    (hdep : ∀ e, (mdepths (2 + Fintype.card (PinType n q t)) G).getD (baseEdge e) 0 ≤ 1)
    (hval : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) e,
      (mrun G (mkBits ρ blocked)).getD (baseEdge e) false = true ↔
        ¬ (blocked e = false ∧ ρ (Sum.inl e.1) ≠ some (!e.2.2.1)))
    (opt : Option (Fin n × Bool)) (i : Fin n) (w : Fin q) (b : Bool) (v : Fin q) :
    let wire := optEdgeWire baseEdge opt i w b v
    wire < 2 + Fintype.card (PinType n q t) + G.length ∧
    (mdepths (2 + Fintype.card (PinType n q t)) G).getD wire 0 ≤ 1 ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun G (mkBits ρ blocked)).getD wire false = true ↔
        ¬ edgeOpen (fun j => ρ (Sum.inl j)) blocked opt i w b v := by
  cases opt with
  | none =>
    refine ⟨hbd _, hdep _, fun ρ blocked => ?_⟩
    dsimp [optEdgeWire, edgeOpen]
    rw [hval ρ blocked (i, w, b, v)]
    simp
  | some p =>
    rcases p with ⟨i₀, b₀⟩
    dsimp only [optEdgeWire]
    split_ifs with hforb
    · refine ⟨by omega, ?_, fun ρ blocked => ?_⟩
      · rw [mdepths_base G 1 (by omega)]; omega
      · rw [mrun_const1]
        simp only [true_iff, edgeOpen, not_and]
        intro _ _ h
        exact hforb.2 (h i₀ b₀ rfl hforb.1)
    · refine ⟨hbd _, hdep _, fun ρ blocked => ?_⟩
      rw [hval ρ blocked (i, w, b, v)]
      simp only [edgeOpen, Option.some.injEq, Prod.mk.injEq, not_and]
      constructor
      · intro h h1 h2 _; exact h h1 h2
      · intro h h1 h2
        apply h h1 h2
        intro i₁ b₁ ⟨hi1, hb1⟩ hii1
        subst hi1; subst hb1
        by_contra hne
        exact hforb ⟨hii1, hne⟩

noncomputable def addDpCell {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (opt : Option (Fin n × Bool)) (i : Fin n)
    (prev : (Fin q × Fin q × Fin (2 ^ m)) → ℕ)
    (G : List MGate) (cell : Fin q × Fin q × Fin (2 ^ m)) : List MGate × ℕ :=
  let N := 2 + Fintype.card (PinType n q t)
  let rTerms := fintypeBuild (ι := Fin q × Bool) (fun G' wb =>
    let s' := if wb.2 then sXor cell.2.2 (hashCol A i) else cell.2.2
    addMGate N G' false (prev (cell.1, wb.1, s')) (optEdgeWire baseEdge opt i wb.1 wb.2 cell.2.1)) G
  addTree true N rTerms.1 (ofFintype rTerms.2)

noncomputable def addDpLayer {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (opt : Option (Fin n × Bool)) (i : Fin n)
    (G : List MGate) (prev : (Fin q × Fin q × Fin (2 ^ m)) → ℕ) :
    List MGate × ((Fin q × Fin q × Fin (2 ^ m)) → ℕ) :=
  fintypeBuild (addDpCell (t := t) A baseEdge opt i prev) G

noncomputable def addDpLayers {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (opt : Option (Fin n × Bool)) (G : List MGate) :
    (l : ℕ) → l ≤ n → List MGate × ((Fin q × Fin q × Fin (2 ^ m)) → ℕ)
  | 0, _ => (G, fun cell => if cell.1 = cell.2.1 ∧ cell.2.2.val = 0 then 0 else 1)
  | l + 1, hl =>
    let r1 := addDpLayers (t := t) A baseEdge opt G l (by omega)
    addDpLayer (t := t) A baseEdge opt ⟨l, by omega⟩ r1.1 r1.2

lemma addDpCell_spec {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (opt : Option (Fin n × Bool)) (l : ℕ) (hl : l + 1 ≤ n)
    (G0 : List MGate) (prev : (Fin q × Fin q × Fin (2 ^ m)) → ℕ) (dprev : ℕ)
    (hd1 : 1 ≤ dprev)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0)
    (hbe_bd : ∀ e, baseEdge e < 2 + Fintype.card (PinType n q t) + G0.length)
    (hbe_dep : ∀ e, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (baseEdge e) 0 ≤ 1)
    (hbe_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) e,
      (mrun G0 (mkBits ρ blocked)).getD (baseEdge e) false = true ↔
        ¬ (blocked e = false ∧ ρ (Sum.inl e.1) ≠ some (!e.2.2.1)))
    (hprev_bd : ∀ c, prev c < 2 + Fintype.card (PinType n q t) + G0.length)
    (hprev_dep : ∀ c, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (prev c) 0 ≤ dprev)
    (hprev_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) c,
      (mrun G0 (mkBits ρ blocked)).getD (prev c) false = true ↔
        ¬ HasPath n q m A (fun j => ρ (Sum.inl j)) blocked opt l (by omega) c.1 c.2.1 c.2.2)
    (cell : Fin q × Fin q × Fin (2 ^ m)) :
    let N := 2 + Fintype.card (PinType n q t)
    let r := addDpCell (t := t) A baseEdge opt ⟨l, by omega⟩ prev G0 cell
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + 4 * q ∧
    r.2 < N + r.1.length ∧
    (mdepths N r.1).getD r.2 0 ≤ dprev + 1 + Nat.clog 2 (2 * q) ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun r.1 (mkBits ρ blocked)).getD r.2 false = true ↔
        ¬ HasPath n q m A (fun j => ρ (Sum.inl j)) blocked opt (l + 1) hl cell.1 cell.2.1 cell.2.2 := by
  let N := 2 + Fintype.card (PinType n q t)
  let termStep : List MGate → Fin q × Bool → List MGate × ℕ := fun G' wb =>
    let s' := if wb.2 then sXor cell.2.2 (hashCol A ⟨l, by omega⟩) else cell.2.2
    addMGate N G' false (prev (cell.1, wb.1, s')) (optEdgeWire baseEdge opt ⟨l, by omega⟩ wb.1 wb.2 cell.2.1)
  let TermInv : List MGate → Fin q × Bool → ℕ → Prop := fun G wb wire =>
    wire < N + G.length ∧ (mdepths N G).getD wire 0 ≤ dprev + 1 ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun G (mkBits ρ blocked)).getD wire false = true ↔
        (¬ HasPath n q m A (fun j => ρ (Sum.inl j)) blocked opt l (by omega) cell.1 wb.1
            (if wb.2 then sXor cell.2.2 (hashCol A ⟨l, by omega⟩) else cell.2.2) ∨
          ¬ edgeOpen (fun j => ρ (Sum.inl j)) blocked opt ⟨l, by omega⟩ wb.1 wb.2 cell.2.1)
  have hmono : ∀ {G1 G2 : List MGate} {wb} {w}, Extends G1 G2 → TermInv G1 wb w → TermInv G2 wb w := by
    intro G1 G2 wb w hext ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) N), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hv ρ blocked
  have hterms := fintypeBuild_spec (ι := Fin q × Bool) N 1 termStep TermInv hmono G0 hwf0
    (fun G wb hwf hext => by
      have hlen_le := extends_len hext
      set s' := if wb.2 then sXor cell.2.2 (hashCol A ⟨l, by omega⟩) else cell.2.2
      have ho := optEdgeWire_spec (t := t) G0 baseEdge hbe_bd hbe_dep hbe_val opt ⟨l, by omega⟩ wb.1 wb.2 cell.2.1
      have hlt1 : prev (cell.1, wb.1, s') < N + G.length := lt_of_lt_of_le (hprev_bd _) (by omega)
      have hlt2 : optEdgeWire baseEdge opt ⟨l, by omega⟩ wb.1 wb.2 cell.2.1 < N + G.length :=
        lt_of_lt_of_le ho.1 (by omega)
      refine ⟨addMGate_wf hwf false hlt1 hlt2, addMGate_extends N G false _ _,
        by rw [addMGate_len], addMGate_out_lt N G false _ _, ?_, ?_⟩
      · rw [addMGate_depth, mdepths_of_extends hext _ (hprev_bd _), mdepths_of_extends hext _ ho.1]
        have := hprev_dep (cell.1, wb.1, if wb.2 then sXor cell.2.2 (hashCol A ⟨l, by omega⟩) else cell.2.2)
        have := ho.2.1
        omega
      · intro ρ blocked
        rw [addMGate_val]
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
        rw [mrun_of_extends hext _ _ (hprev_bd _), mrun_of_extends hext _ _ ho.1,
          hprev_val ρ blocked _, ho.2.2 ρ blocked])
  rcases hterms with ⟨hwfT, hextT, hlenT, hinvT⟩
  set rTerms := fintypeBuild termStep G0 with hrTerms
  have hcard : Fintype.card (Fin q × Bool) = 2 * q := by simp [Nat.mul_comm]
  have htree := addTree_spec (P := PinType n q t) true rTerms.1 (ofFintype rTerms.2) (dprev + 1) hwfT
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨wb, rfl⟩; exact (hinvT wb).1)
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨wb, rfl⟩; exact (hinvT wb).2.1)
  rcases htree with ⟨hwfA, hextA, hlenA, hbdA, hdepA, hevA⟩
  rw [ofFintype_length, hcard] at hlenA hdepA
  rw [hcard, mul_one] at hlenT
  change WellFormed (2 + Fintype.card (PinType n q t)) (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).1 ∧
    Extends G0 (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).1 ∧
    (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).1.length ≤ G0.length + 4 * q ∧
    (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).2 <
      2 + Fintype.card (PinType n q t) + (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).1.length ∧
    (mdepths (2 + Fintype.card (PinType n q t)) (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).1).getD
      (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).2 0 ≤ dprev + 1 + Nat.clog 2 (2 * q) ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).1 (mkBits ρ blocked)).getD
        (addTree true (2 + Fintype.card (PinType n q t)) rTerms.1 (ofFintype rTerms.2)).2 false = true ↔
        ¬ HasPath n q m A (fun j => ρ (Sum.inl j)) blocked opt (l + 1) hl cell.1 cell.2.1 cell.2.2
  refine ⟨hwfA, extends_trans hextT hextA, by omega, hbdA, hdepA, ?_⟩
  intro ρ blocked
  rw [hevA (mkBits ρ blocked), evalList_ofFintype_true]
  simp only [HasPath, not_exists, not_and]
  constructor
  · intro hall w b hp he
    have hwb := (hinvT (w, b)).2.2 ρ blocked |>.mp (hall (w, b))
    exact hwb.elim (fun h => h hp) (fun h => h he)
  · intro h ⟨w, b⟩
    rw [(hinvT (w, b)).2.2 ρ blocked]
    by_cases hp : HasPath n q m A (fun j => ρ (Sum.inl j)) blocked opt l (by omega) cell.1 w
        (if b then sXor cell.2.2 (hashCol A ⟨l, by omega⟩) else cell.2.2)
    · exact Or.inr (h w b hp)
    · exact Or.inl hp

lemma addDpLayers_spec {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (opt : Option (Fin n × Bool)) (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0)
    (hbe_bd : ∀ e, baseEdge e < 2 + Fintype.card (PinType n q t) + G0.length)
    (hbe_dep : ∀ e, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (baseEdge e) 0 ≤ 1)
    (hbe_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) e,
      (mrun G0 (mkBits ρ blocked)).getD (baseEdge e) false = true ↔
        ¬ (blocked e = false ∧ ρ (Sum.inl e.1) ≠ some (!e.2.2.1))) :
    ∀ (l : ℕ) (hl : l ≤ n),
      let N := 2 + Fintype.card (PinType n q t)
      let r := addDpLayers (t := t) A baseEdge opt G0 l hl
      WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + l * (4 * q ^ 3 * 2 ^ m) ∧
      (∀ c, r.2 c < N + r.1.length) ∧
      (∀ c, (mdepths N r.1).getD (r.2 c) 0 ≤ 1 + l * (1 + Nat.clog 2 (2 * q))) ∧
      ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) c,
        (mrun r.1 (mkBits ρ blocked)).getD (r.2 c) false = true ↔
          ¬ HasPath n q m A (fun j => ρ (Sum.inl j)) blocked opt l hl c.1 c.2.1 c.2.2 := by
  intro l hl
  induction l with
  | zero =>
    refine ⟨hwf0, extends_rfl G0, by simp [addDpLayers], ?_, ?_, ?_⟩
    · intro c; dsimp [addDpLayers]; split_ifs <;> omega
    · intro c; dsimp [addDpLayers]; split_ifs
      · rw [mdepths_base G0 0 (by omega)]; omega
      · rw [mdepths_base G0 1 (by omega)]; omega
    · intro ρ blocked c
      dsimp [addDpLayers, HasPath]
      split_ifs with h
      · rw [mrun_const0]; simp [h]
      · rw [mrun_const1]; simp only [true_iff]; exact h
  | succ l ih =>
    let N := 2 + Fintype.card (PinType n q t)
    rcases ih (by omega) with ⟨hwf1, hext1, hlen1, hbd1, hdep1, hval1⟩
    set r1 := addDpLayers (t := t) A baseEdge opt G0 l (by omega) with hr1
    let d1 := 1 + l * (1 + Nat.clog 2 (2 * q))
    let CellInv : List MGate → (Fin q × Fin q × Fin (2 ^ m)) → ℕ → Prop := fun G c w =>
      w < N + G.length ∧ (mdepths N G).getD w 0 ≤ d1 + 1 + Nat.clog 2 (2 * q) ∧
      ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
        (mrun G (mkBits ρ blocked)).getD w false = true ↔
          ¬ HasPath n q m A (fun j => ρ (Sum.inl j)) blocked opt (l + 1) hl c.1 c.2.1 c.2.2
    have hmono : ∀ {G1 G2 : List MGate} {c} {w}, Extends G1 G2 → CellInv G1 c w → CellInv G2 c w := by
      intro G1 G2 c w hext ⟨hlt, hd, hv⟩
      refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) N), ?_, ?_⟩
      · rw [mdepths_of_extends hext w hlt]; exact hd
      · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hv ρ blocked
    have hlayer := fintypeBuild_spec (ι := Fin q × Fin q × Fin (2 ^ m)) N (4 * q)
      (addDpCell (t := t) A baseEdge opt ⟨l, by omega⟩ r1.2) CellInv hmono r1.1 hwf1
      (fun G c hwf hext => by
        have hext0 : Extends G0 G := extends_trans hext1 hext
        have hlen0 := extends_len hext0
        have hlenG1 := extends_len hext
        have hcell := addDpCell_spec (t := t) A baseEdge opt l hl G r1.2 d1 (by omega) hwf
          (fun e => lt_of_lt_of_le (hbe_bd e) (by omega))
          (fun e => by rw [mdepths_of_extends hext0 _ (hbe_bd e)]; exact hbe_dep e)
          (fun ρ blocked e => by rw [mrun_of_extends hext0 _ _ (hbe_bd e)]; exact hbe_val ρ blocked e)
          (fun c' => lt_of_lt_of_le (hbd1 c') (by omega))
          (fun c' => by rw [mdepths_of_extends hext _ (hbd1 c')]; exact hdep1 c')
          (fun ρ blocked c' => by rw [mrun_of_extends hext _ _ (hbd1 c')]; exact hval1 ρ blocked c')
          c
        exact ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1, hcell.2.2.2.2.1, hcell.2.2.2.2.2⟩)
    rcases hlayer with ⟨hwf2, hext2, hlen2, hinv2⟩
    have hcard : Fintype.card (Fin q × Fin q × Fin (2 ^ m)) * (4 * q) = 4 * q ^ 3 * 2 ^ m := by
      simp only [Fintype.card_prod, Fintype.card_fin]; ring
    dsimp only [addDpLayers, addDpLayer]
    rw [← hr1]
    refine ⟨hwf2, extends_trans hext1 hext2, ?_, fun c => (hinv2 c).1, ?_, fun ρ blocked c => (hinv2 c).2.2 ρ blocked⟩
    · rw [hcard] at hlen2
      have : (l + 1) * (4 * q ^ 3 * 2 ^ m) = l * (4 * q ^ 3 * 2 ^ m) + 4 * q ^ 3 * 2 ^ m := by ring
      omega
    · intro c
      have hdepc := (hinv2 c).2.1
      dsimp only [N] at hdepc
      have : 1 + (l + 1) * (1 + Nat.clog 2 (2 * q)) = d1 + 1 + Nat.clog 2 (2 * q) := by dsimp [d1]; ring
      omega

noncomputable def addDpScan {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (opt : Option (Fin n × Bool)) (G : List MGate) : List MGate × (Fin (2 ^ m) → ℕ) :=
  let N := 2 + Fintype.card (PinType n q t)
  let rDp := addDpLayers (t := t) A baseEdge opt G n le_rfl
  fintypeBuild (ι := Fin (2 ^ m)) (fun G' s =>
    addTree true N G' (ofFintype (fun u : Fin q => rDp.2 (u, u, s)))) rDp.1

lemma addDpScan_spec {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (opt : Option (Fin n × Bool)) (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0)
    (hbe_bd : ∀ e, baseEdge e < 2 + Fintype.card (PinType n q t) + G0.length)
    (hbe_dep : ∀ e, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (baseEdge e) 0 ≤ 1)
    (hbe_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) e,
      (mrun G0 (mkBits ρ blocked)).getD (baseEdge e) false = true ↔
        ¬ (blocked e = false ∧ ρ (Sum.inl e.1) ≠ some (!e.2.2.1))) :
    let N := 2 + Fintype.card (PinType n q t)
    let r := addDpScan (t := t) A baseEdge opt G0
    WellFormed N r.1 ∧ Extends G0 r.1 ∧
    r.1.length ≤ G0.length + (4 * n * q ^ 3 + q) * 2 ^ m ∧
    (∀ s, r.2 s < N + r.1.length) ∧
    (∀ s, (mdepths N r.1).getD (r.2 s) 0 ≤ 1 + n * (1 + Nat.clog 2 (2 * q)) + Nat.clog 2 q) ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (s : Fin (2 ^ m)),
      (mrun r.1 (mkBits ρ blocked)).getD (r.2 s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked,
            hashVal A x = s ∧ ∀ i₀ b₀, opt = some (i₀, b₀) → x i₀ = b₀ := by
  let N := 2 + Fintype.card (PinType n q t)
  have hdp := addDpLayers_spec (t := t) A baseEdge opt G0 hwf0 hbe_bd hbe_dep hbe_val n le_rfl
  rcases hdp with ⟨hwf1, hext1, hlen1, hbd1, hdep1, hval1⟩
  set rDp := addDpLayers (t := t) A baseEdge opt G0 n le_rfl with hrDp
  let d1 := 1 + n * (1 + Nat.clog 2 (2 * q))
  let ScanInv : List MGate → Fin (2 ^ m) → ℕ → Prop := fun G s w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ d1 + Nat.clog 2 q ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun G (mkBits ρ blocked)).getD w false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked,
            hashVal A x = s ∧ ∀ i₀ b₀, opt = some (i₀, b₀) → x i₀ = b₀
  have hmono : ∀ {G1 G2 : List MGate} {s} {w}, Extends G1 G2 → ScanInv G1 s w → ScanInv G2 s w := by
    intro G1 G2 s w hext ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) N), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hv ρ blocked
  have hscan := fintypeBuild_spec (ι := Fin (2 ^ m)) N q
    (fun G' s => addTree true N G' (ofFintype (fun u : Fin q => rDp.2 (u, u, s))))
    ScanInv hmono rDp.1 hwf1 (fun G s hwf hext => by
      have hlenG := extends_len hext
      have htr := addTree_spec (P := PinType n q t) true G (ofFintype (fun u : Fin q => rDp.2 (u, u, s))) d1 hwf
        (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨u, rfl⟩; exact lt_of_lt_of_le (hbd1 _) (by omega))
        (fun w hw => by
          rcases (mem_ofFintype_iff _ _).mp hw with ⟨u, rfl⟩
          rw [mdepths_of_extends hext _ (hbd1 _)]; exact hdep1 _)
      rcases htr with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
      rw [ofFintype_length, Fintype.card_fin] at hlenT hdepT
      refine ⟨hwfT, hextT, hlenT, hbdT, hdepT, fun ρ blocked => ?_⟩
      rw [hevT (mkBits ρ blocked), evalList_ofFintype_true, ← exists_hasPath_cycle_iff]
      simp only [not_exists]
      apply forall_congr'; intro u
      rw [mrun_of_extends hext _ _ (hbd1 _), hval1 ρ blocked (u, u, s)])
  rcases hscan with ⟨hwf2, hext2, hlen2, hinv2⟩
  rw [Fintype.card_fin] at hlen2
  dsimp only [addDpScan, N] at hlen2 ⊢
  rw [← hrDp]
  refine ⟨hwf2, extends_trans hext1 hext2, ?_, fun s => (hinv2 s).1, fun s => (hinv2 s).2.1,
    fun ρ blocked s => (hinv2 s).2.2 ρ blocked⟩
  have : (4 * n * q ^ 3 + q) * 2 ^ m = n * (4 * q ^ 3 * 2 ^ m) + 2 ^ m * q := by ring
  omega

noncomputable def addAllScans {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ) (G : List MGate) :
    List MGate × (Fin (2 ^ m) → ℕ) × ((Fin n × Bool) → Fin (2 ^ m) → ℕ) :=
  let rEmpty := addDpScan (t := t) A baseEdge none G
  let rExcl := fintypeBuild (ι := Fin n × Bool) (fun G' ib => addDpScan (t := t) A baseEdge (some ib) G') rEmpty.1
  (rExcl.1, rEmpty.2, rExcl.2)

lemma addAllScans_spec {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ) (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0)
    (hbe_bd : ∀ e, baseEdge e < 2 + Fintype.card (PinType n q t) + G0.length)
    (hbe_dep : ∀ e, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (baseEdge e) 0 ≤ 1)
    (hbe_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) e,
      (mrun G0 (mkBits ρ blocked)).getD (baseEdge e) false = true ↔
        ¬ (blocked e = false ∧ ρ (Sum.inl e.1) ≠ some (!e.2.2.1))) :
    let N := 2 + Fintype.card (PinType n q t)
    let r := addAllScans (t := t) A baseEdge G0
    let dpD := 1 + n * (1 + Nat.clog 2 (2 * q)) + Nat.clog 2 q
    WellFormed N r.1 ∧ Extends G0 r.1 ∧
    r.1.length ≤ G0.length + (2 * n + 1) * (4 * n * q ^ 3 + q) * 2 ^ m ∧
    (∀ s, r.2.1 s < N + r.1.length) ∧
    (∀ s, (mdepths N r.1).getD (r.2.1 s) 0 ≤ dpD) ∧
    (∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (s : Fin (2 ^ m)),
      (mrun r.1 (mkBits ρ blocked)).getD (r.2.1 s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s) ∧
    (∀ ib s, r.2.2 ib s < N + r.1.length) ∧
    (∀ ib s, (mdepths N r.1).getD (r.2.2 ib s) 0 ≤ dpD) ∧
    (∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool)
        (i : Fin n) (b : Bool) (s : Fin (2 ^ m)),
      (mrun r.1 (mkBits ρ blocked)).getD (r.2.2 (i, b) s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s ∧ x i = b) := by
  let N := 2 + Fintype.card (PinType n q t)
  let dpD := 1 + n * (1 + Nat.clog 2 (2 * q)) + Nat.clog 2 q
  have hE := addDpScan_spec (t := t) A baseEdge none G0 hwf0 hbe_bd hbe_dep hbe_val
  rcases hE with ⟨hwfE, hextE, hlenE, hbdE, hdepE, hvalE⟩
  set rEmpty := addDpScan (t := t) A baseEdge none G0 with hrE
  let ExclInv : List MGate → Fin n × Bool → (Fin (2 ^ m) → ℕ) → Prop := fun G ib fn =>
    (∀ s, fn s < N + G.length) ∧
    (∀ s, (mdepths N G).getD (fn s) 0 ≤ dpD) ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (s : Fin (2 ^ m)),
      (mrun G (mkBits ρ blocked)).getD (fn s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s ∧ x ib.1 = ib.2
  have hmono : ∀ {G1 G2 : List MGate} {ib} {fn}, Extends G1 G2 → ExclInv G1 ib fn → ExclInv G2 ib fn := by
    intro G1 G2 ib fn hext ⟨hbd, hdep, hval⟩
    refine ⟨fun s => lt_of_lt_of_le (hbd s) (Nat.add_le_add_left (extends_len hext) N), ?_, ?_⟩
    · intro s; rw [mdepths_of_extends hext _ (hbd s)]; exact hdep s
    · intro ρ blocked s; rw [mrun_of_extends hext _ _ (hbd s)]; exact hval ρ blocked s
  have hX := fintypeBuild_spec (ι := Fin n × Bool) N ((4 * n * q ^ 3 + q) * 2 ^ m)
    (fun G' ib => addDpScan (t := t) A baseEdge (some ib) G') ExclInv hmono rEmpty.1 hwfE
    (fun G ib hwf hext => by
      have hext0 := extends_trans hextE hext
      have hlen0 := extends_len hext0
      have hsc := addDpScan_spec (t := t) A baseEdge (some ib) G hwf
        (fun e => lt_of_lt_of_le (hbe_bd e) (by omega))
        (fun e => by rw [mdepths_of_extends hext0 _ (hbe_bd e)]; exact hbe_dep e)
        (fun ρ blocked e => by rw [mrun_of_extends hext0 _ _ (hbe_bd e)]; exact hbe_val ρ blocked e)
      refine ⟨hsc.1, hsc.2.1, hsc.2.2.1, hsc.2.2.2.1, hsc.2.2.2.2.1, fun ρ blocked s => ?_⟩
      rw [hsc.2.2.2.2.2 ρ blocked s]
      constructor <;> intro h ⟨x, hx, hhash, hcond⟩ <;> apply h <;> refine ⟨x, hx, hhash, ?_⟩
      · intro i₀ b₀ hopt; injection hopt with hp; rw [hp] at hcond; exact hcond
      · exact hcond ib.1 ib.2 rfl)
  rcases hX with ⟨hwfX, hextX, hlenX, hinvX⟩
  have hcard : Fintype.card (Fin n × Bool) = 2 * n := by simp [Nat.mul_comm]
  rw [hcard] at hlenX
  have hlenX_le := extends_len hextX
  dsimp only [addAllScans]
  rw [← hrE]
  refine ⟨hwfX, extends_trans hextE hextX, ?_, ?_, ?_, ?_,
    fun ib s => (hinvX ib).1 s, fun ib s => (hinvX ib).2.1 s,
    fun ρ blocked i b s => (hinvX (i, b)).2.2 ρ blocked s⟩
  · have : (2 * n + 1) * (4 * n * q ^ 3 + q) * 2 ^ m =
        (4 * n * q ^ 3 + q) * 2 ^ m + 2 * n * ((4 * n * q ^ 3 + q) * 2 ^ m) := by ring
    omega
  · intro s; have := hbdE s; omega
  · intro s; rw [mdepths_of_extends hextX _ (hbdE s)]; exact hdepE s
  · intro ρ blocked s
    rw [mrun_of_extends hextX _ _ (hbdE s), hvalE ρ blocked s]
    simp

lemma clog2_le_of_le_pow (a k : ℕ) (h : a ≤ 2 ^ k) : Nat.clog 2 a ≤ k :=
  (Nat.clog_le_iff_le_pow (by omega)).mpr h

lemma two_pow_clog2_le (a : ℕ) : 2 ^ Nat.clog 2 (a + 1) ≤ 2 * (a + 1) := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hpos : 0 < Nat.clog 2 (a + 1) := by
      by_contra h0
      have h0' : Nat.clog 2 (a + 1) = 0 := by omega
      have hle := Nat.le_pow_clog (b := 2) (by omega) (a + 1)
      rw [h0', pow_zero] at hle
      omega
    have hlt : 2 ^ (Nat.clog 2 (a + 1) - 1) < a + 1 := by
      by_contra hge
      have hle : a + 1 ≤ 2 ^ (Nat.clog 2 (a + 1) - 1) := by omega
      have hc := clog2_le_of_le_pow (a + 1) (Nat.clog 2 (a + 1) - 1) hle
      omega
    have hpow : 2 ^ Nat.clog 2 (a + 1) = 2 * 2 ^ (Nat.clog 2 (a + 1) - 1) := by
      conv_lhs => rw [show Nat.clog 2 (a + 1) = (Nat.clog 2 (a + 1) - 1) + 1 by omega, pow_succ]
      ring
    omega

lemma clog2_two_mul_le (a : ℕ) : Nat.clog 2 (2 * a) ≤ Nat.clog 2 (a + 1) + 1 := by
  apply clog2_le_of_le_pow
  have h1 : a + 1 ≤ 2 ^ Nat.clog 2 (a + 1) := Nat.le_pow_clog (by omega) (a + 1)
  rw [pow_succ]
  omega

lemma clog2_R_le (n q t : ℕ) :
    Nat.clog 2 (2 * n * q ^ 2 + 2 * n + 1) ≤ 2 + Nat.clog 2 (t + n + 2) + 2 * Nat.clog 2 (q + 1) := by
  apply clog2_le_of_le_pow
  have h1 : n + 1 ≤ 2 ^ Nat.clog 2 (t + n + 2) :=
    le_trans (by omega) (Nat.le_pow_clog (b := 2) (by omega) (t + n + 2))
  have h2 : q + 1 ≤ 2 ^ Nat.clog 2 (q + 1) := Nat.le_pow_clog (by omega) (q + 1)
  have hq2 : (q + 1) ^ 2 ≤ 2 ^ (2 * Nat.clog 2 (q + 1)) := by
    rw [show 2 * Nat.clog 2 (q + 1) = Nat.clog 2 (q + 1) * 2 by ring, pow_mul]
    exact Nat.pow_le_pow_left h2 2
  have hR : 2 * n * q ^ 2 + 2 * n + 1 ≤ 4 * (n + 1) * (q + 1) ^ 2 := by nlinarith
  calc 2 * n * q ^ 2 + 2 * n + 1
      ≤ 4 * (n + 1) * (q + 1) ^ 2 := hR
    _ ≤ 2 ^ 2 * 2 ^ Nat.clog 2 (t + n + 2) * 2 ^ (2 * Nat.clog 2 (q + 1)) := by
        have hm1 : 4 * (n + 1) ≤ 2 ^ 2 * 2 ^ Nat.clog 2 (t + n + 2) := by
          have : (4 : ℕ) = 2 ^ 2 := by norm_num
          rw [this]; exact Nat.mul_le_mul_left _ h1
        exact Nat.mul_le_mul hm1 hq2
    _ = 2 ^ (2 + Nat.clog 2 (t + n + 2) + 2 * Nat.clog 2 (q + 1)) := by
        rw [← pow_add, ← pow_add]

noncomputable def addBucketReady (n q t m : ℕ)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin n × Bool) → Fin (2 ^ m) → ℕ)
    (G : List MGate) (s : Fin (2 ^ m)) : List MGate × ℕ :=
  let N := 2 + Fintype.card (PinType n q t)
  let rOrs := fintypeBuild (ι := Fin n) (fun G' i => addMGate N G' false (excl (i, false) s) (excl (i, true) s)) G
  let rAll := addTree true N rOrs.1 (ofFintype rOrs.2)
  addMGate N rAll.1 false (empty s) rAll.2

noncomputable def addHashReady (n q t m : ℕ)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin n × Bool) → Fin (2 ^ m) → ℕ)
    (G : List MGate) : List MGate × ℕ :=
  let N := 2 + Fintype.card (PinType n q t)
  let rB := fintypeBuild (addBucketReady n q t m empty excl) G
  addTree true N rB.1 (ofFintype rB.2)

lemma addBucketReady_spec {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin n × Bool) → Fin (2 ^ m) → ℕ)
    (G0 : List MGate) (dpD : ℕ)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0)
    (he_bd : ∀ s, empty s < 2 + Fintype.card (PinType n q t) + G0.length)
    (he_dep : ∀ s, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (empty s) 0 ≤ dpD)
    (he_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (s : Fin (2 ^ m)),
      (mrun G0 (mkBits ρ blocked)).getD (empty s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s)
    (hx_bd : ∀ ib s, excl ib s < 2 + Fintype.card (PinType n q t) + G0.length)
    (hx_dep : ∀ ib s, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (excl ib s) 0 ≤ dpD)
    (hx_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool)
        (i : Fin n) (b : Bool) (s : Fin (2 ^ m)),
      (mrun G0 (mkBits ρ blocked)).getD (excl (i, b) s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s ∧ x i = b)
    (s : Fin (2 ^ m)) :
    let N := 2 + Fintype.card (PinType n q t)
    let r := addBucketReady n q t m empty excl G0 s
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + (2 * n + 1) ∧
    r.2 < N + r.1.length ∧
    (mdepths N r.1).getD r.2 0 ≤ dpD + 2 + Nat.clog 2 n ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun r.1 (mkBits ρ blocked)).getD r.2 false = true ↔
        ∀ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked,
          ∀ y ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked,
            hashVal A x = s → hashVal A y = s → x = y := by
  let OrInv : List MGate → Fin n → ℕ → Prop := fun G i w =>
    w < 2 + Fintype.card (PinType n q t) + G.length ∧
    (mdepths (2 + Fintype.card (PinType n q t)) G).getD w 0 ≤ dpD + 1 ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun G (mkBits ρ blocked)).getD w false = true ↔
        ((¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s ∧ x i = false) ∨
         (¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s ∧ x i = true))
  have hmono : ∀ {G1 G2 : List MGate} {i} {w}, Extends G1 G2 → OrInv G1 i w → OrInv G2 i w := by
    intro G1 G2 i w hext ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) _), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hv ρ blocked
  have hOrs := fintypeBuild_spec (ι := Fin n) (2 + Fintype.card (PinType n q t)) 1
    (fun G' i => addMGate (2 + Fintype.card (PinType n q t)) G' false (excl (i, false) s) (excl (i, true) s))
    OrInv hmono G0 hwf0 (fun G i hwf hext => by
      have hlenG := extends_len hext
      have hltF : excl (i, false) s < 2 + Fintype.card (PinType n q t) + G.length :=
        lt_of_lt_of_le (hx_bd (i, false) s) (by omega)
      have hltT : excl (i, true) s < 2 + Fintype.card (PinType n q t) + G.length :=
        lt_of_lt_of_le (hx_bd (i, true) s) (by omega)
      refine ⟨addMGate_wf hwf false hltF hltT, addMGate_extends _ G false _ _,
        by rw [addMGate_len], addMGate_out_lt _ G false _ _, ?_, ?_⟩
      · rw [addMGate_depth, mdepths_of_extends hext _ (hx_bd (i, false) s),
          mdepths_of_extends hext _ (hx_bd (i, true) s)]
        have := hx_dep (i, false) s; have := hx_dep (i, true) s; omega
      · intro ρ blocked
        rw [addMGate_val]
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
        rw [mrun_of_extends hext _ _ (hx_bd (i, false) s), mrun_of_extends hext _ _ (hx_bd (i, true) s),
          hx_val ρ blocked i false s, hx_val ρ blocked i true s])
  rcases hOrs with ⟨hwfO, hextO, hlenO, hinvO⟩
  set rOrs := fintypeBuild (ι := Fin n)
    (fun G' i => addMGate (2 + Fintype.card (PinType n q t)) G' false (excl (i, false) s) (excl (i, true) s)) G0 with hrO
  have hAll := addTree_spec (P := PinType n q t) true rOrs.1 (ofFintype rOrs.2) (dpD + 1) hwfO
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨i, rfl⟩; exact (hinvO i).1)
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨i, rfl⟩; exact (hinvO i).2.1)
  rcases hAll with ⟨hwfA, hextA, hlenA, hbdA, hdepA, hevA⟩
  set rAll := addTree true (2 + Fintype.card (PinType n q t)) rOrs.1 (ofFintype rOrs.2) with hrA
  rw [ofFintype_length, Fintype.card_fin] at hlenA hdepA
  rw [Fintype.card_fin, mul_one] at hlenO
  have hext0A : Extends G0 rAll.1 := extends_trans hextO hextA
  have hlen0A := extends_len hext0A
  have hltE : empty s < 2 + Fintype.card (PinType n q t) + rAll.1.length :=
    lt_of_lt_of_le (he_bd s) (by omega)
  set rFin := addMGate (2 + Fintype.card (PinType n q t)) rAll.1 false (empty s) rAll.2 with hrF
  have hwfF := addMGate_wf hwfA false hltE hbdA
  have hextF := addMGate_extends (2 + Fintype.card (PinType n q t)) rAll.1 false (empty s) rAll.2
  have hlenF : rFin.1.length = rAll.1.length + 1 := addMGate_len _ rAll.1 false (empty s) rAll.2
  have houtF : rFin.2 < 2 + Fintype.card (PinType n q t) + rFin.1.length := addMGate_out_lt _ rAll.1 false (empty s) rAll.2
  dsimp only [addBucketReady]
  rw [← hrO, ← hrA, ← hrF]
  refine ⟨hwfF, extends_trans hext0A hextF, by omega, houtF, ?_, ?_⟩
  · rw [hrF, addMGate_depth, mdepths_of_extends hext0A _ (he_bd s)]
    have := he_dep s; omega
  · intro ρ blocked
    rw [hrF, addMGate_val]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
    rw [mrun_of_extends hext0A _ _ (he_bd s), he_val ρ blocked s, hevA (mkBits ρ blocked), evalList_ofFintype_true]
    constructor
    · intro hor x hx y hy hxs hys
      rcases hor with hemp | hall
      · exact False.elim (hemp ⟨x, hx, hxs⟩)
      · funext i
        have hi := (hinvO i).2.2 ρ blocked |>.mp (hall i)
        rcases hi with hnoF | hnoT
        · cases hxi : x i
          · exact False.elim (hnoF ⟨x, hx, hxs, hxi⟩)
          · cases hyi : y i
            · exact False.elim (hnoF ⟨y, hy, hys, hyi⟩)
            · rfl
        · cases hxi : x i
          · cases hyi : y i
            · rfl
            · exact False.elim (hnoT ⟨y, hy, hys, hyi⟩)
          · exact False.elim (hnoT ⟨x, hx, hxs, hxi⟩)
    · intro hinj
      by_cases hex : ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s
      · right
        rcases hex with ⟨x, hx, hxs⟩
        intro i
        rw [(hinvO i).2.2 ρ blocked]
        cases hxi : x i
        · right
          rintro ⟨y, hy, hys, hyi⟩
          have heq := hinj x hx y hy hxs hys
          rw [heq] at hxi
          rw [hxi] at hyi
          exact Bool.noConfusion hyi
        · left
          rintro ⟨y, hy, hys, hyi⟩
          have heq := hinj x hx y hy hxs hys
          rw [heq] at hxi
          rw [hxi] at hyi
          exact Bool.noConfusion hyi
      · exact Or.inl hex

lemma addHashReady_spec {n q t m : ℕ} (A : Fin m → Fin n → Bool)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin n × Bool) → Fin (2 ^ m) → ℕ)
    (G0 : List MGate) (dpD : ℕ)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0)
    (he_bd : ∀ s, empty s < 2 + Fintype.card (PinType n q t) + G0.length)
    (he_dep : ∀ s, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (empty s) 0 ≤ dpD)
    (he_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (s : Fin (2 ^ m)),
      (mrun G0 (mkBits ρ blocked)).getD (empty s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s)
    (hx_bd : ∀ ib s, excl ib s < 2 + Fintype.card (PinType n q t) + G0.length)
    (hx_dep : ∀ ib s, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (excl ib s) 0 ≤ dpD)
    (hx_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool)
        (i : Fin n) (b : Bool) (s : Fin (2 ^ m)),
      (mrun G0 (mkBits ρ blocked)).getD (excl (i, b) s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s ∧ x i = b) :
    let N := 2 + Fintype.card (PinType n q t)
    let r := addHashReady n q t m empty excl G0
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + (2 * n + 2) * 2 ^ m ∧
    r.2 < N + r.1.length ∧
    (mdepths N r.1).getD r.2 0 ≤ dpD + 2 + Nat.clog 2 n + m ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun r.1 (mkBits ρ blocked)).getD r.2 false = true ↔
        ∀ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked,
          ∀ y ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked,
            hashVal A x = hashVal A y → x = y := by
  let BInv : List MGate → Fin (2 ^ m) → ℕ → Prop := fun G s w =>
    w < 2 + Fintype.card (PinType n q t) + G.length ∧
    (mdepths (2 + Fintype.card (PinType n q t)) G).getD w 0 ≤ dpD + 2 + Nat.clog 2 n ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun G (mkBits ρ blocked)).getD w false = true ↔
        ∀ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked,
          ∀ y ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked,
            hashVal A x = s → hashVal A y = s → x = y
  have hmono : ∀ {G1 G2 : List MGate} {s} {w}, Extends G1 G2 → BInv G1 s w → BInv G2 s w := by
    intro G1 G2 s w hext ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) _), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hv ρ blocked
  have hB := fintypeBuild_spec (ι := Fin (2 ^ m)) (2 + Fintype.card (PinType n q t)) (2 * n + 1)
    (addBucketReady n q t m empty excl) BInv hmono G0 hwf0 (fun G s hwf hext => by
      have hlenG := extends_len hext
      exact addBucketReady_spec A empty excl G dpD hwf
        (fun s' => lt_of_lt_of_le (he_bd s') (by omega))
        (fun s' => by rw [mdepths_of_extends hext _ (he_bd s')]; exact he_dep s')
        (fun ρ blocked s' => by rw [mrun_of_extends hext _ _ (he_bd s')]; exact he_val ρ blocked s')
        (fun ib s' => lt_of_lt_of_le (hx_bd ib s') (by omega))
        (fun ib s' => by rw [mdepths_of_extends hext _ (hx_bd ib s')]; exact hx_dep ib s')
        (fun ρ blocked i b s' => by rw [mrun_of_extends hext _ _ (hx_bd (i, b) s')]; exact hx_val ρ blocked i b s')
        s)
  rcases hB with ⟨hwfB, hextB, hlenB, hinvB⟩
  set rB := fintypeBuild (addBucketReady n q t m empty excl) G0 with hrB
  have hT := addTree_spec (P := PinType n q t) true rB.1 (ofFintype rB.2) (dpD + 2 + Nat.clog 2 n) hwfB
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨s, rfl⟩; exact (hinvB s).1)
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨s, rfl⟩; exact (hinvB s).2.1)
  rcases hT with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
  rw [ofFintype_length, Fintype.card_fin] at hlenT hdepT
  rw [Fintype.card_fin] at hlenB
  have hcl : Nat.clog 2 (2 ^ m) ≤ m := clog2_le_of_le_pow (2 ^ m) m le_rfl
  dsimp only [addHashReady]
  rw [← hrB]
  refine ⟨hwfT, extends_trans hextB hextT, ?_, hbdT, by omega, ?_⟩
  · have : (2 * n + 2) * 2 ^ m = 2 ^ m * (2 * n + 1) + 2 ^ m := by ring
    omega
  · intro ρ blocked
    rw [hevT (mkBits ρ blocked), evalList_ofFintype_true]
    constructor
    · intro hall x hx y hy hxy
      exact ((hinvB (hashVal A x)).2.2 ρ blocked).mp (hall (hashVal A x)) x hx y hy rfl hxy.symm
    · intro hinj s
      rw [(hinvB s).2.2 ρ blocked]
      intro x hx y hy hxs hys
      exact hinj x hx y hy (hxs.trans hys.symm)

def depStep (w : List ℕ) (g : BinaryGate) : List ℕ :=
  w ++ [max (w.getD g.left 0) (w.getD g.right 0) + 1]

def wireStep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

def readRail (tbl : List (ℕ × ℕ)) (w : ℕ) (b : Bool) : ℕ :=
  if b then (tbl.getD w (1, 0)).2 else (tbl.getD w (1, 0)).1

lemma readRail_append_lt (tbl : List (ℕ × ℕ)) (p : ℕ × ℕ) (w : ℕ) (b : Bool) (h : w < tbl.length) :
    readRail (tbl ++ [p]) w b = readRail tbl w b := by
  unfold readRail; rw [getD_append_left tbl [p] w (1, 0) h]

lemma readRail_append_eq (tbl : List (ℕ × ℕ)) (p : ℕ × ℕ) (b : Bool) :
    readRail (tbl ++ [p]) tbl.length b = if b then p.2 else p.1 := by
  unfold readRail
  rw [getD_append_right tbl [p] tbl.length (1, 0) le_rfl, Nat.sub_self, List.getD_cons_zero]

lemma readRail_append_gt (tbl : List (ℕ × ℕ)) (p : ℕ × ℕ) (w : ℕ) (b : Bool) (h : tbl.length < w) :
    readRail (tbl ++ [p]) w b = if b then 0 else 1 := by
  unfold readRail
  rw [getD_append_right tbl [p] w (1, 0) (by omega)]
  have h1 : 1 ≤ w - tbl.length := by omega
  cases hsub : w - tbl.length with
  | zero => omega
  | succ k => simp [List.getD]

lemma getD_oob {α : Type} (l : List α) (w : ℕ) (d : α) (h : l.length ≤ w) :
    l.getD w d = d := by
  simp [List.getD, List.getElem?_eq_none h]

noncomputable def addDualRailBit (N : ℕ) (G : List MGate) (tbl : List (ℕ × ℕ))
    (g : BinaryGate) (target : Bool) : List MGate × ℕ :=
  let rTerms := fintypeBuild (ι := Bool × Bool) (fun G' ab =>
    if g.op ab.1 ab.2 = target then
      addMGate N G' true (readRail tbl g.left ab.1) (readRail tbl g.right ab.2)
    else (G', 0)) G
  addTree false N rTerms.1 (ofFintype rTerms.2)

lemma addDualRailBit_spec {P : Type} [Fintype P] (G0 : List MGate) (tbl : List (ℕ × ℕ))
    (dep0 : List ℕ) (dpD : ℕ) (g : BinaryGate) (target : Bool)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hbd : ∀ w b, readRail tbl w b < 2 + Fintype.card P + G0.length)
    (hdep : ∀ w b, (mdepths (2 + Fintype.card P) G0).getD (readRail tbl w b) 0 ≤ dpD + 3 * dep0.getD w 0) :
    let N := 2 + Fintype.card P
    let r := addDualRailBit N G0 tbl g target
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + 8 ∧
    r.2 < N + r.1.length ∧
    (mdepths N r.1).getD r.2 0 ≤ dpD + 3 * (max (dep0.getD g.left 0) (dep0.getD g.right 0) + 1) ∧
    ∀ a : P → Bool,
      (mrun r.1 a).getD r.2 false = true ↔
        ∃ ab : Bool × Bool, g.op ab.1 ab.2 = target ∧
          (mrun G0 a).getD (readRail tbl g.left ab.1) false = true ∧
          (mrun G0 a).getD (readRail tbl g.right ab.2) false = true := by
  let dmax := dpD + 3 * max (dep0.getD g.left 0) (dep0.getD g.right 0) + 1
  let TInv : List MGate → Bool × Bool → ℕ → Prop := fun G ab w =>
    w < 2 + Fintype.card P + G.length ∧
    (mdepths (2 + Fintype.card P) G).getD w 0 ≤ dmax ∧
    ∀ a : P → Bool, (mrun G a).getD w false = true ↔
      (g.op ab.1 ab.2 = target ∧
        (mrun G0 a).getD (readRail tbl g.left ab.1) false = true ∧
        (mrun G0 a).getD (readRail tbl g.right ab.2) false = true)
  have hmono : ∀ {G1 G2 : List MGate} {ab} {w}, Extends G1 G2 → TInv G1 ab w → TInv G2 ab w := by
    intro G1 G2 ab w hext ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) _), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro a; rw [mrun_of_extends hext a w hlt]; exact hv a
  have hTerms := fintypeBuild_spec (ι := Bool × Bool) (2 + Fintype.card P) 1
    (fun G' ab => if g.op ab.1 ab.2 = target then
        addMGate (2 + Fintype.card P) G' true (readRail tbl g.left ab.1) (readRail tbl g.right ab.2)
      else (G', 0))
    TInv hmono G0 hwf0 (fun G ab hwf hext => by
      have hlenG := extends_len hext
      split_ifs with hop
      · have hltL : readRail tbl g.left ab.1 < 2 + Fintype.card P + G.length :=
          lt_of_lt_of_le (hbd g.left ab.1) (by omega)
        have hltR : readRail tbl g.right ab.2 < 2 + Fintype.card P + G.length :=
          lt_of_lt_of_le (hbd g.right ab.2) (by omega)
        refine ⟨addMGate_wf hwf true hltL hltR, addMGate_extends _ G true _ _,
          by rw [addMGate_len], addMGate_out_lt _ G true _ _, ?_, ?_⟩
        · rw [addMGate_depth, mdepths_of_extends hext _ (hbd g.left ab.1),
            mdepths_of_extends hext _ (hbd g.right ab.2)]
          have h1 := hdep g.left ab.1; have h2 := hdep g.right ab.2
          dsimp [dmax]; omega
        · intro a
          rw [addMGate_val]
          simp only [↓reduceIte, Bool.and_eq_true, hop, true_and]
          rw [mrun_of_extends hext a _ (hbd g.left ab.1), mrun_of_extends hext a _ (hbd g.right ab.2)]
      · refine ⟨hwf, extends_rfl G, by dsimp only; omega, by dsimp only; omega, ?_, ?_⟩
        · dsimp only; rw [mdepths_base G 0 (by omega)]; omega
        · intro a; dsimp only; rw [mrun_const0]; simp [hop])
  rcases hTerms with ⟨hwfT, hextT, hlenT, hinvT⟩
  set rTerms := fintypeBuild (ι := Bool × Bool)
    (fun G' ab => if g.op ab.1 ab.2 = target then
        addMGate (2 + Fintype.card P) G' true (readRail tbl g.left ab.1) (readRail tbl g.right ab.2)
      else (G', 0)) G0 with hrT
  have hcard : Fintype.card (Bool × Bool) = 4 := by decide
  rw [hcard, mul_one] at hlenT
  have hOr := addTree_spec (P := P) false rTerms.1 (ofFintype rTerms.2) dmax hwfT
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨ab, rfl⟩; exact (hinvT ab).1)
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨ab, rfl⟩; exact (hinvT ab).2.1)
  rcases hOr with ⟨hwfO, hextO, hlenO, hbdO, hdepO, hevO⟩
  rw [ofFintype_length, hcard] at hlenO hdepO
  have hcl4 : Nat.clog 2 4 ≤ 2 := clog2_le_of_le_pow 4 2 (by norm_num)
  dsimp only [addDualRailBit]
  rw [← hrT]
  refine ⟨hwfO, extends_trans hextT hextO, by omega, hbdO, ?_, ?_⟩
  · dsimp [dmax] at hdepO; omega
  · intro a
    rw [hevO a, evalList_ofFintype_false]
    apply exists_congr; intro ab
    exact (hinvT ab).2.2 a

noncomputable def addDualRailGate (N : ℕ) (G : List MGate) (tbl : List (ℕ × ℕ))
    (g : BinaryGate) : List MGate × (ℕ × ℕ) :=
  let rF := addDualRailBit N G tbl g false
  let rT := addDualRailBit N rF.1 tbl g true
  (rT.1, (rF.2, rT.2))

noncomputable def addDualRailCircAux (N : ℕ) :
    List BinaryGate → List MGate → List (ℕ × ℕ) → List MGate × List (ℕ × ℕ)
  | [], G, tbl => (G, tbl)
  | g :: gs, G, tbl =>
    let r := addDualRailGate N G tbl g
    addDualRailCircAux N gs r.1 (tbl ++ [r.2])

lemma addDualRailCircAux_spec {P : Type} [Fintype P] (gs : List BinaryGate)
    (G0 : List MGate) (tbl0 : List (ℕ × ℕ)) (dep0 : List ℕ) (dpD : ℕ)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hlen0 : tbl0.length = dep0.length)
    (hbd0 : ∀ w b, readRail tbl0 w b < 2 + Fintype.card P + G0.length)
    (hdep0 : ∀ w b, (mdepths (2 + Fintype.card P) G0).getD (readRail tbl0 w b) 0 ≤ dpD + 3 * dep0.getD w 0) :
    let N := 2 + Fintype.card P
    let r := addDualRailCircAux N gs G0 tbl0
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + 16 * gs.length ∧
    r.2.length = tbl0.length + gs.length ∧
    (∀ w b, readRail r.2 w b < N + r.1.length) ∧
    (∀ w b, (mdepths N r.1).getD (readRail r.2 w b) 0 ≤ dpD + 3 * (gs.foldl depStep dep0).getD w 0) ∧
    (∀ (a : P → Bool) (w0 : List Bool), w0.length = tbl0.length →
      (∀ w b, (mrun G0 a).getD (readRail tbl0 w b) false = true → w0.getD w false = b) →
      ∀ w b, (mrun r.1 a).getD (readRail r.2 w b) false = true → (gs.foldl wireStep w0).getD w false = b) ∧
    (∀ (a : P → Bool) (w0 : List Bool), w0.length = tbl0.length →
      (∀ w b, (mrun G0 a).getD (readRail tbl0 w b) false = true ↔ w0.getD w false = b) →
      ∀ w b, (mrun r.1 a).getD (readRail r.2 w b) false = true ↔ (gs.foldl wireStep w0).getD w false = b) := by
  induction gs generalizing G0 tbl0 dep0 with
  | nil =>
    exact ⟨hwf0, extends_rfl G0, by simp [addDualRailCircAux], by simp [addDualRailCircAux],
      hbd0, hdep0, fun _ _ _ h => h, fun _ _ _ h => h⟩
  | cons g gs ih =>
    have hF := addDualRailBit_spec (P := P) G0 tbl0 dep0 dpD g false hwf0 hbd0 hdep0
    rcases hF with ⟨hwfF, hextF, hlenF, hbdF, hdepF, hevF⟩
    set rF := addDualRailBit (2 + Fintype.card P) G0 tbl0 g false with hrF
    have hlen_leF := extends_len hextF
    have hT := addDualRailBit_spec (P := P) rF.1 tbl0 dep0 dpD g true hwfF
      (fun w b => lt_of_lt_of_le (hbd0 w b) (by omega))
      (fun w b => by rw [mdepths_of_extends hextF _ (hbd0 w b)]; exact hdep0 w b)
    rcases hT with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
    set rT := addDualRailBit (2 + Fintype.card P) rF.1 tbl0 g true with hrT
    have hlen_leT := extends_len hextT
    have hextFT : Extends G0 rT.1 := extends_trans hextF hextT
    have hlen_leFT := extends_len hextFT
    set tbl1 := tbl0 ++ [(rF.2, rT.2)]
    set dep1 := depStep dep0 g
    have hlen1 : tbl1.length = dep1.length := by simp [tbl1, dep1, depStep, hlen0]
    have hbd1 : ∀ w b, readRail tbl1 w b < 2 + Fintype.card P + rT.1.length := by
      intro w b
      by_cases hlt : w < tbl0.length
      · rw [readRail_append_lt tbl0 _ w b hlt]; have := hbd0 w b; omega
      · by_cases heq : w = tbl0.length
        · subst heq; rw [readRail_append_eq]; cases b <;> simp <;> omega
        · rw [readRail_append_gt tbl0 _ w b (by omega)]; cases b <;> simp <;> omega
    have hdep1 : ∀ w b, (mdepths (2 + Fintype.card P) rT.1).getD (readRail tbl1 w b) 0 ≤ dpD + 3 * dep1.getD w 0 := by
      intro w b
      by_cases hlt : w < tbl0.length
      · rw [readRail_append_lt tbl0 _ w b hlt, mdepths_of_extends hextFT _ (hbd0 w b)]
        have hltD : w < dep0.length := by omega
        rw [show dep1.getD w 0 = dep0.getD w 0 from getD_append_left dep0 _ w 0 hltD]
        exact hdep0 w b
      · by_cases heq : w = tbl0.length
        · subst heq
          rw [readRail_append_eq]
          have hdep_eq : dep1.getD tbl0.length 0 = max (dep0.getD g.left 0) (dep0.getD g.right 0) + 1 := by
            dsimp [dep1, depStep]
            rw [getD_append_right dep0 _ tbl0.length 0 (by omega), hlen0, Nat.sub_self, List.getD_cons_zero]
          rw [hdep_eq]
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [mdepths_of_extends hextT _ hbdF]; exact hdepF
          · simp only [↓reduceIte]; exact hdepT
        · rw [readRail_append_gt tbl0 _ w b (by omega)]
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]; rw [mdepths_base rT.1 1 (by omega)]; omega
          · simp only [↓reduceIte]; rw [mdepths_base rT.1 0 (by omega)]; omega
    have hrec := ih rT.1 tbl1 dep1 hwfT hlen1 hbd1 hdep1
    rcases hrec with ⟨hwfR, hextR, hlenR, htblR, hbdR, hdepR, hsndR, hextcR⟩
    dsimp only [addDualRailCircAux, addDualRailGate, List.foldl_cons]
    rw [← hrF, ← hrT]
    refine ⟨hwfR, extends_trans hextFT hextR, ?_, ?_, hbdR, hdepR, ?_, ?_⟩
    · dsimp only [tbl1] at hlenR; simp only [List.length_cons]; omega
    · simp only [List.length_cons, htblR, tbl1, List.length_append, List.length_nil]; omega
    · intro a w0 hw0len hsnd0
      apply hsndR a (wireStep w0 g) (by simp [tbl1, wireStep, hw0len])
      intro w b hw
      by_cases hlt : w < tbl0.length
      · rw [readRail_append_lt tbl0 _ w b hlt, mrun_of_extends hextFT a _ (hbd0 w b)] at hw
        rw [show (wireStep w0 g).getD w false = w0.getD w false from getD_append_left w0 _ w false (by omega)]
        exact hsnd0 w b hw
      · by_cases heq : w = tbl0.length
        · subst heq
          rw [readRail_append_eq] at hw
          have hw_eq : (wireStep w0 g).getD tbl0.length false = g.op (w0.getD g.left false) (w0.getD g.right false) := by
            dsimp [wireStep]
            rw [getD_append_right w0 _ tbl0.length false (by omega), hw0len, Nat.sub_self, List.getD_cons_zero]
          rw [hw_eq]
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte] at hw
            rw [mrun_of_extends hextT a _ hbdF] at hw
            rcases (hevF a).mp hw with ⟨⟨al, ar⟩, hop, hl, hr⟩
            rw [hsnd0 g.left al hl, hsnd0 g.right ar hr]; exact hop
          · simp only [↓reduceIte] at hw
            rcases (hevT a).mp hw with ⟨⟨al, ar⟩, hop, hl, hr⟩
            rw [mrun_of_extends hextF a _ (hbd0 g.left al)] at hl
            rw [mrun_of_extends hextF a _ (hbd0 g.right ar)] at hr
            rw [hsnd0 g.left al hl, hsnd0 g.right ar hr]; exact hop
        · rw [readRail_append_gt tbl0 _ w b (by omega)] at hw
          rw [getD_oob (wireStep w0 g) w false (by simp [wireStep, hw0len]; omega)]
          cases b
          · rfl
          · simp only [↓reduceIte] at hw; rw [mrun_const0] at hw; exact Bool.noConfusion hw
    · intro a w0 hw0len hex0
      apply hextcR a (wireStep w0 g) (by simp [tbl1, wireStep, hw0len])
      intro w b
      by_cases hlt : w < tbl0.length
      · rw [readRail_append_lt tbl0 _ w b hlt, mrun_of_extends hextFT a _ (hbd0 w b)]
        rw [show (wireStep w0 g).getD w false = w0.getD w false from getD_append_left w0 _ w false (by omega)]
        exact hex0 w b
      · by_cases heq : w = tbl0.length
        · subst heq
          rw [readRail_append_eq]
          have hw_eq : (wireStep w0 g).getD tbl0.length false = g.op (w0.getD g.left false) (w0.getD g.right false) := by
            dsimp [wireStep]
            rw [getD_append_right w0 _ tbl0.length false (by omega), hw0len, Nat.sub_self, List.getD_cons_zero]
          rw [hw_eq]
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [mrun_of_extends hextT a _ hbdF, hevF a]
            constructor
            · rintro ⟨⟨al, ar⟩, hop, hl, hr⟩
              rw [(hex0 g.left al).mp hl, (hex0 g.right ar).mp hr]; exact hop
            · intro hop
              exact ⟨(w0.getD g.left false, w0.getD g.right false), hop,
                (hex0 g.left _).mpr rfl, (hex0 g.right _).mpr rfl⟩
          · simp only [↓reduceIte]
            rw [hevT a]
            constructor
            · rintro ⟨⟨al, ar⟩, hop, hl, hr⟩
              rw [mrun_of_extends hextF a _ (hbd0 g.left al)] at hl
              rw [mrun_of_extends hextF a _ (hbd0 g.right ar)] at hr
              rw [(hex0 g.left al).mp hl, (hex0 g.right ar).mp hr]; exact hop
            · intro hop
              refine ⟨(w0.getD g.left false, w0.getD g.right false), hop, ?_, ?_⟩
              · rw [mrun_of_extends hextF a _ (hbd0 g.left _)]; exact (hex0 g.left _).mpr rfl
              · rw [mrun_of_extends hextF a _ (hbd0 g.right _)]; exact (hex0 g.right _).mpr rfl
        · rw [readRail_append_gt tbl0 _ w b (by omega)]
          rw [getD_oob (wireStep w0 g) w false (by simp [wireStep, hw0len]; omega)]
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]; rw [mrun_const1]; simp
          · simp only [↓reduceIte]; rw [mrun_const0]

noncomputable def addBucketFail (n q t m : ℕ) (gates : List BinaryGate) (output : Fin t → ℕ)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin n × Bool) → Fin (2 ^ m) → ℕ)
    (G : List MGate) (s : Fin (2 ^ m)) : List MGate × ℕ :=
  let N := 2 + Fintype.card (PinType n q t)
  let tbl0 : List (ℕ × ℕ) := List.ofFn (fun i : Fin n => (excl (i, true) s, excl (i, false) s))
  let rCirc := addDualRailCircAux N gates G tbl0
  let rMis := fintypeBuild (ι := Fin t × Bool) (fun G' jb =>
    addMGate N G' true (pinWire n q t (Sum.inl (Sum.inr jb.1, jb.2)))
      (readRail rCirc.2 (output jb.1) (!jb.2))) rCirc.1
  let rAny := addTree false N rMis.1 (ofFintype rMis.2)
  addMGate N rAny.1 false (empty s) rAny.2

lemma addBucketFail_spec {n q t m : ℕ} (gates : List BinaryGate) (output : Fin t → ℕ)
    (A : Fin m → Fin n → Bool)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin n × Bool) → Fin (2 ^ m) → ℕ)
    (G0 : List MGate) (dpD : ℕ)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0)
    (he_bd : ∀ s, empty s < 2 + Fintype.card (PinType n q t) + G0.length)
    (he_dep : ∀ s, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (empty s) 0 ≤ dpD)
    (he_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) (s : Fin (2 ^ m)),
      (mrun G0 (mkBits ρ blocked)).getD (empty s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s)
    (hx_bd : ∀ ib s, excl ib s < 2 + Fintype.card (PinType n q t) + G0.length)
    (hx_dep : ∀ ib s, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (excl ib s) 0 ≤ dpD)
    (hx_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool)
        (i : Fin n) (b : Bool) (s : Fin (2 ^ m)),
      (mrun G0 (mkBits ρ blocked)).getD (excl (i, b) s) false = true ↔
        ¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s ∧ x i = b)
    (s : Fin (2 ^ m)) :
    let N := 2 + Fintype.card (PinType n q t)
    let C : BinaryCircuit := ⟨gates, 0⟩
    let dep := gates.foldl depStep (List.replicate n 0)
    let D := (Finset.univ : Finset (Fin t)).sup (fun j => dep.getD (output j) 0)
    let r := addBucketFail n q t m gates output empty excl G0 s
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + (16 * gates.length + 4 * t + 1) ∧
    r.2 < N + r.1.length ∧
    (mdepths N r.1).getD r.2 0 ≤ dpD + 3 * D + 2 + Nat.clog 2 (2 * t) ∧
    (∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      let cand := candSet n q (fun j => ρ (Sum.inl j)) blocked
      (∀ x ∈ cand, hashVal A x = s →
        (∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b → (C.wires (List.ofFn x)).getD (output j) false = b) →
        (mrun r.1 (mkBits ρ blocked)).getD r.2 false = false) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal A x = s → hashVal A y = s → x = y) →
        ((mrun r.1 (mkBits ρ blocked)).getD r.2 false = false ↔
          ∃ x ∈ cand, hashVal A x = s ∧
            ∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b → (C.wires (List.ofFn x)).getD (output j) false = b))) := by
  let dep := gates.foldl depStep (List.replicate n 0)
  let D := (Finset.univ : Finset (Fin t)).sup (fun j => dep.getD (output j) 0)
  let tbl0 : List (ℕ × ℕ) := List.ofFn (fun i : Fin n => (excl (i, true) s, excl (i, false) s))
  have htbl0_bd : ∀ w b, readRail tbl0 w b < 2 + Fintype.card (PinType n q t) + G0.length := by
    intro w b
    unfold readRail
    by_cases hw : w < n
    · have hget : tbl0.getD w (1, 0) = (excl (⟨w, hw⟩, true) s, excl (⟨w, hw⟩, false) s) := by
        rw [List.getD_eq_getElem _ _ (by simp [tbl0, hw])]; simp [tbl0]
      rw [hget]
      cases b
      · exact hx_bd (⟨w, hw⟩, true) s
      · exact hx_bd (⟨w, hw⟩, false) s
    · rw [getD_oob tbl0 w (1, 0) (by simp [tbl0]; omega)]; cases b <;> simp <;> omega
  have htbl0_dep : ∀ w b, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (readRail tbl0 w b) 0 ≤
      dpD + 3 * (List.replicate n 0).getD w 0 := by
    intro w b
    unfold readRail
    by_cases hw : w < n
    · have hget : tbl0.getD w (1, 0) = (excl (⟨w, hw⟩, true) s, excl (⟨w, hw⟩, false) s) := by
        rw [List.getD_eq_getElem _ _ (by simp [tbl0, hw])]; simp [tbl0]
      rw [hget]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]; have := hx_dep (⟨w, hw⟩, true) s; omega
      · simp only [↓reduceIte]; have := hx_dep (⟨w, hw⟩, false) s; omega
    · rw [getD_oob tbl0 w (1, 0) (by simp [tbl0]; omega)]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [mdepths_base G0 1 (by omega)]; omega
      · simp only [↓reduceIte]; rw [mdepths_base G0 0 (by omega)]; omega
  have hCirc := addDualRailCircAux_spec (P := PinType n q t) gates G0 tbl0 (List.replicate n 0) dpD hwf0
    (by simp [tbl0]) htbl0_bd htbl0_dep
  rcases hCirc with ⟨hwfC, hextC, hlenC, _, hbdC, hdepC, hsndC, hexC⟩
  set rCirc := addDualRailCircAux (2 + Fintype.card (PinType n q t)) gates G0 tbl0 with hrC
  let MisInv : List MGate → Fin t × Bool → ℕ → Prop := fun G jb w =>
    w < 2 + Fintype.card (PinType n q t) + G.length ∧
    (mdepths (2 + Fintype.card (PinType n q t)) G).getD w 0 ≤ dpD + 3 * D + 1 ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun G (mkBits ρ blocked)).getD w false = true ↔
        (ρ (Sum.inr jb.1) = some jb.2 ∧
          (mrun rCirc.1 (mkBits ρ blocked)).getD (readRail rCirc.2 (output jb.1) (!jb.2)) false = true)
  have hmonoM : ∀ {G1 G2 : List MGate} {jb} {w}, Extends G1 G2 → MisInv G1 jb w → MisInv G2 jb w := by
    intro G1 G2 jb w hext ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) _), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hv ρ blocked
  have hMis := fintypeBuild_spec (ι := Fin t × Bool) (2 + Fintype.card (PinType n q t)) 1
    (fun G' jb => addMGate (2 + Fintype.card (PinType n q t)) G' true
      (pinWire n q t (Sum.inl (Sum.inr jb.1, jb.2))) (readRail rCirc.2 (output jb.1) (!jb.2)))
    MisInv hmonoM rCirc.1 hwfC (fun G jb hwf hext => by
      have hlenG := extends_len hext
      have hlt2 : readRail rCirc.2 (output jb.1) (!jb.2) < 2 + Fintype.card (PinType n q t) + G.length :=
        lt_of_lt_of_le (hbdC _ _) (by omega)
      refine ⟨addMGate_wf hwf true (pinWire_lt n q t G _) hlt2, addMGate_extends _ G true _ _,
        by rw [addMGate_len], addMGate_out_lt _ G true _ _, ?_, ?_⟩
      · rw [addMGate_depth, pinWire_depth, mdepths_of_extends hext _ (hbdC _ _)]
        have h1 := hdepC (output jb.1) (!jb.2)
        have h2 : (List.foldl depStep (List.replicate n 0) gates).getD (output jb.1) 0 ≤ D :=
          Finset.le_sup (f := fun j => dep.getD (output j) 0) (Finset.mem_univ jb.1)
        change max 0 _ + 1 ≤ dpD + 3 * D + 1
        omega
      · intro ρ blocked
        rw [addMGate_val]
        simp only [↓reduceIte, Bool.and_eq_true, pinWire_val, mkBits, Sum.elim_inl, decide_eq_true_eq]
        rw [mrun_of_extends hext _ _ (hbdC _ _)])
  rcases hMis with ⟨hwfM, hextM, hlenM, hinvM⟩
  set rMis := fintypeBuild (ι := Fin t × Bool) (fun G' jb =>
    addMGate (2 + Fintype.card (PinType n q t)) G' true
      (pinWire n q t (Sum.inl (Sum.inr jb.1, jb.2))) (readRail rCirc.2 (output jb.1) (!jb.2))) rCirc.1 with hrM
  have hcardTB : Fintype.card (Fin t × Bool) = 2 * t := by simp [Nat.mul_comm]
  rw [hcardTB, mul_one] at hlenM
  have hAny := addTree_spec (P := PinType n q t) false rMis.1 (ofFintype rMis.2) (dpD + 3 * D + 1) hwfM
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨jb, rfl⟩; exact (hinvM jb).1)
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨jb, rfl⟩; exact (hinvM jb).2.1)
  rcases hAny with ⟨hwfA, hextA, hlenA, hbdA, hdepA, hevA⟩
  set rAny := addTree false (2 + Fintype.card (PinType n q t)) rMis.1 (ofFintype rMis.2) with hrA
  rw [ofFintype_length, hcardTB] at hlenA hdepA
  have hext0A : Extends G0 rAny.1 := extends_trans hextC (extends_trans hextM hextA)
  have hlen0A := extends_len hext0A
  have hltE : empty s < 2 + Fintype.card (PinType n q t) + rAny.1.length :=
    lt_of_lt_of_le (he_bd s) (by omega)
  set rFin := addMGate (2 + Fintype.card (PinType n q t)) rAny.1 false (empty s) rAny.2 with hrF
  have hwfF := addMGate_wf hwfA false hltE hbdA
  have hextF := addMGate_extends (2 + Fintype.card (PinType n q t)) rAny.1 false (empty s) rAny.2
  have hlenF : rFin.1.length = rAny.1.length + 1 := addMGate_len _ rAny.1 false (empty s) rAny.2
  have houtF : rFin.2 < 2 + Fintype.card (PinType n q t) + rFin.1.length := addMGate_out_lt _ rAny.1 false (empty s) rAny.2
  dsimp only [addBucketFail]
  rw [← hrC, ← hrM, ← hrA, ← hrF]
  refine ⟨hwfF, extends_trans hext0A hextF, by omega, houtF, ?_, ?_⟩
  · change (mdepths (2 + Fintype.card (PinType n q t)) rFin.1).getD rFin.2 0 ≤ dpD + 3 * D + 2 + Nat.clog 2 (2 * t)
    rw [hrF, addMGate_depth, mdepths_of_extends hext0A _ (he_bd s)]
    have := he_dep s; omega
  · intro ρ blocked
    have hfail_iff : (mrun rFin.1 (mkBits ρ blocked)).getD rFin.2 false = true ↔
        (¬ ∃ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s) ∨
        ∃ j : Fin t, ∃ b : Bool, ρ (Sum.inr j) = some b ∧
          (mrun rCirc.1 (mkBits ρ blocked)).getD (readRail rCirc.2 (output j) (!b)) false = true := by
      rw [hrF, addMGate_val]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      rw [mrun_of_extends hext0A _ _ (he_bd s), he_val ρ blocked s, hevA (mkBits ρ blocked), evalList_ofFintype_false]
      constructor
      · rintro (h | ⟨⟨j, b⟩, hjb⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, b, ((hinvM (j, b)).2.2 ρ blocked).mp hjb⟩
      · rintro (h | ⟨j, b, hjb⟩)
        · exact Or.inl h
        · exact Or.inr ⟨(j, b), ((hinvM (j, b)).2.2 ρ blocked).mpr hjb⟩
    have hsnd_x : ∀ x ∈ candSet n q (fun j => ρ (Sum.inl j)) blocked, hashVal A x = s →
        ∀ w b, (mrun rCirc.1 (mkBits ρ blocked)).getD (readRail rCirc.2 w b) false = true →
          ((BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD w false = b := by
      intro x hx hxs
      apply hsndC (mkBits ρ blocked) (List.ofFn x) (by simp [tbl0])
      intro w b hw
      by_cases hlt : w < n
      · have hget : tbl0.getD w (1, 0) = (excl (⟨w, hlt⟩, true) s, excl (⟨w, hlt⟩, false) s) := by
          rw [List.getD_eq_getElem _ _ (by simp [tbl0, hlt])]; simp [tbl0]
        have hxget : (List.ofFn x).getD w false = x ⟨w, hlt⟩ := by
          rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
        rw [hxget]
        unfold readRail at hw
        rw [hget] at hw
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte] at hw
          have hno := (hx_val ρ blocked ⟨w, hlt⟩ true s).mp hw
          cases hxi : x ⟨w, hlt⟩
          · rfl
          · exact False.elim (hno ⟨x, hx, hxs, hxi⟩)
        · simp only [↓reduceIte] at hw
          have hno := (hx_val ρ blocked ⟨w, hlt⟩ false s).mp hw
          cases hxi : x ⟨w, hlt⟩
          · exact False.elim (hno ⟨x, hx, hxs, hxi⟩)
          · rfl
      · unfold readRail at hw
        rw [getD_oob tbl0 w (1, 0) (by simp [tbl0]; omega)] at hw
        rw [getD_oob (List.ofFn x) w false (by simp; omega)]
        cases b
        · rfl
        · simp only [↓reduceIte] at hw; rw [mrun_const0] at hw; exact Bool.noConfusion hw
    constructor
    · intro x hx hxs hacc
      cases hval : (mrun rFin.1 (mkBits ρ blocked)).getD rFin.2 false
      · rfl
      · rcases hfail_iff.mp hval with hemp | ⟨j, b, hρ, hmis⟩
        · exact False.elim (hemp ⟨x, hx, hxs⟩)
        · have h1 := hsnd_x x hx hxs (output j) (!b) hmis
          have h2 := hacc j b hρ
          rw [h2] at h1
          cases b <;> exact Bool.noConfusion h1
    · intro hinj
      constructor
      · intro hfalse
        have hnt : ¬ ((mrun rFin.1 (mkBits ρ blocked)).getD rFin.2 false = true) := by rw [hfalse]; decide
        rw [hfail_iff] at hnt
        push Not at hnt
        rcases hnt with ⟨⟨x, hx, hxs⟩, hnomis⟩
        have hex_x : ∀ w b, (mrun rCirc.1 (mkBits ρ blocked)).getD (readRail rCirc.2 w b) false = true ↔
            ((BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD w false = b := by
          apply hexC (mkBits ρ blocked) (List.ofFn x) (by simp [tbl0])
          intro w b
          by_cases hlt : w < n
          · have hget : tbl0.getD w (1, 0) = (excl (⟨w, hlt⟩, true) s, excl (⟨w, hlt⟩, false) s) := by
              rw [List.getD_eq_getElem _ _ (by simp [tbl0, hlt])]; simp [tbl0]
            have hxget : (List.ofFn x).getD w false = x ⟨w, hlt⟩ := by
              rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
            rw [hxget]; unfold readRail; rw [hget]
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte, hx_val ρ blocked ⟨w, hlt⟩ true s]
              constructor
              · intro hno; cases hxi : x ⟨w, hlt⟩
                · rfl
                · exact False.elim (hno ⟨x, hx, hxs, hxi⟩)
              · rintro hxi ⟨y, hy, hys, hyi⟩
                have heq := hinj x hx y hy hxs hys
                rw [← heq, hxi] at hyi; exact Bool.noConfusion hyi
            · simp only [↓reduceIte, hx_val ρ blocked ⟨w, hlt⟩ false s]
              constructor
              · intro hno; cases hxi : x ⟨w, hlt⟩
                · exact False.elim (hno ⟨x, hx, hxs, hxi⟩)
                · rfl
              · rintro hxi ⟨y, hy, hys, hyi⟩
                have heq := hinj x hx y hy hxs hys
                rw [← heq, hxi] at hyi; exact Bool.noConfusion hyi
          · unfold readRail
            rw [getD_oob tbl0 w (1, 0) (by simp [tbl0]; omega), getD_oob (List.ofFn x) w false (by simp; omega)]
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte]; rw [mrun_const1]; simp
            · simp only [↓reduceIte]; rw [mrun_const0]
        refine ⟨x, hx, hxs, fun j b hρ => ?_⟩
        have hno := hnomis j b hρ
        rw [ne_eq, hex_x (output j) (!b)] at hno
        cases hwire : ((BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD (output j) false <;>
          cases b <;> first | rfl | exact False.elim (hno (by rw [hwire]; rfl))
      · rintro ⟨x, hx, hxs, hacc⟩
        cases hval : (mrun rFin.1 (mkBits ρ blocked)).getD rFin.2 false
        · rfl
        · rcases hfail_iff.mp hval with hemp | ⟨j, b, hρ, hmis⟩
          · exact False.elim (hemp ⟨x, hx, hxs⟩)
          · have h1 := hsnd_x x hx hxs (output j) (!b) hmis
            have h2 := hacc j b hρ
            rw [h2] at h1
            cases b <;> exact Bool.noConfusion h1

lemma bpop_add_card_false {M : ℕ} (f : Fin M → Bool) :
    bpop f + (Finset.univ.filter (fun s : Fin M => f s = false)).card = M := by
  have htrue : bpop f = (Finset.univ.filter (fun s : Fin M => f s = true)).card := by
    unfold bpop
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl; intro s _
    cases f s <;> rfl
  rw [htrue]
  have hdisj : Disjoint (Finset.univ.filter (fun s : Fin M => f s = true))
      (Finset.univ.filter (fun s : Fin M => f s = false)) := by
    rw [Finset.disjoint_left]; intro s h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2; exact Bool.noConfusion h2
  have hunion : Finset.univ.filter (fun s : Fin M => f s = true) ∪
      Finset.univ.filter (fun s : Fin M => f s = false) = Finset.univ := by
    ext s; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases f s <;> simp
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]

lemma K_succ_le_pow_two_clog (K : ℕ) : K + 1 ≤ 2 ^ (2 * Nat.clog 2 (K + 1)) := by
  have h1 : K + 1 ≤ 2 ^ Nat.clog 2 (K + 1) := Nat.le_pow_clog (by omega) (K + 1)
  have h2 : (K + 1) ^ 2 ≤ (2 ^ Nat.clog 2 (K + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : (2 ^ Nat.clog 2 (K + 1)) ^ 2 = 2 ^ (2 * Nat.clog 2 (K + 1)) := by rw [← pow_mul, Nat.mul_comm]
  nlinarith

noncomputable def addSingleHash (n q t K : ℕ) (gates : List BinaryGate) (output : Fin t → ℕ)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (A : Fin (2 * Nat.clog 2 (K + 1)) → Fin n → Bool)
    (G : List MGate) : List MGate × (Fin (K + 1) → ℕ) :=
  let N := 2 + Fintype.card (PinType n q t)
  let m := 2 * Nat.clog 2 (K + 1)
  let rScans := addAllScans (t := t) A baseEdge G
  let rReady := addHashReady n q t m rScans.2.1 rScans.2.2 rScans.1
  let rFails := fintypeBuild (addBucketFail n q t m gates output rScans.2.1 rScans.2.2) rReady.1
  let rSort := addBitonicSort N false m rFails.1 rFails.2
  have hM : K + 1 ≤ 2 ^ m := K_succ_le_pow_two_clog K
  fintypeBuild (ι := Fin (K + 1)) (fun G' j =>
    addMGate N G' true rReady.2 (rSort.2 ⟨2 ^ m - 1 - j.val, by omega⟩)) rSort.1

lemma addSingleHash_spec (n q t K : ℕ) (gates : List BinaryGate) (output : Fin t → ℕ)
    (baseEdge : (Fin n × Fin q × Bool × Fin q) → ℕ)
    (A : Fin (2 * Nat.clog 2 (K + 1)) → Fin n → Bool)
    (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (PinType n q t)) G0)
    (hbe_bd : ∀ e, baseEdge e < 2 + Fintype.card (PinType n q t) + G0.length)
    (hbe_dep : ∀ e, (mdepths (2 + Fintype.card (PinType n q t)) G0).getD (baseEdge e) 0 ≤ 1)
    (hbe_val : ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool) e,
      (mrun G0 (mkBits ρ blocked)).getD (baseEdge e) false = true ↔
        ¬ (blocked e = false ∧ ρ (Sum.inl e.1) ≠ some (!e.2.2.1))) :
    let N := 2 + Fintype.card (PinType n q t)
    let C : BinaryCircuit := ⟨gates, 0⟩
    let dep := gates.foldl depStep (List.replicate n 0)
    let D := (Finset.univ : Finset (Fin t)).sup (fun j => dep.getD (output j) 0)
    let keyLog := Nat.clog 2 (K + 1)
    let m := 2 * keyLog
    let S := (n + 1) ^ 2 * (q + 1) ^ 3 + gates.length + t + n + (keyLog + 1) ^ 2 + 1
    let r := addSingleHash n q t K gates output baseEdge A G0
    WellFormed N r.1 ∧ Extends G0 r.1 ∧
    r.1.length ≤ G0.length + 16 * S * 2 ^ m ∧
    (∀ j, r.2 j < N + r.1.length) ∧
    (∀ j, (mdepths N r.1).getD (r.2 j) 0 ≤
      2 * (n + 1) * (Nat.clog 2 (q + 1) + 1) + 3 * D + 4 * (keyLog + 1) ^ 2 + Nat.clog 2 (t + n + 2) + 4) ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      let cand := candSet n q (fun j => ρ (Sum.inl j)) blocked
      let acc := cand.filter (fun x =>
        ∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b → (C.wires (List.ofFn x)).getD (output j) false = b)
      (∀ j : Fin (K + 1), (mrun r.1 (mkBits ρ blocked)).getD (r.2 j) false = true → acc.card ≤ j.val) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal A x = hashVal A y → x = y) →
        ∀ j : Fin (K + 1), (mrun r.1 (mkBits ρ blocked)).getD (r.2 j) false = true ↔ acc.card ≤ j.val) := by
  let dep := gates.foldl depStep (List.replicate n 0)
  let D := (Finset.univ : Finset (Fin t)).sup (fun j => dep.getD (output j) 0)
  let keyLog := Nat.clog 2 (K + 1)
  let m := 2 * keyLog
  let dpD := 1 + n * (1 + Nat.clog 2 (2 * q)) + Nat.clog 2 q
  have hM : K + 1 ≤ 2 ^ m := K_succ_le_pow_two_clog K
  have hSc := addAllScans_spec (t := t) A baseEdge G0 hwf0 hbe_bd hbe_dep hbe_val
  rcases hSc with ⟨hwfS, hextS, hlenS, he_bd, he_dep, he_val, hx_bd, hx_dep, hx_val⟩
  set rScans := addAllScans (t := t) A baseEdge G0 with hrS
  have hRd := addHashReady_spec A rScans.2.1 rScans.2.2 rScans.1 dpD hwfS
    he_bd he_dep he_val hx_bd hx_dep hx_val
  rcases hRd with ⟨hwfR, hextR, hlenR, hbdR, hdepR, hvalR⟩
  set rReady := addHashReady n q t m rScans.2.1 rScans.2.2 rScans.1 with hrR
  have hlenR_le := extends_len hextR
  let FailInv : List MGate → Fin (2 ^ m) → ℕ → Prop := fun G s w =>
    w < 2 + Fintype.card (PinType n q t) + G.length ∧
    (mdepths (2 + Fintype.card (PinType n q t)) G).getD w 0 ≤ dpD + 3 * D + 2 + Nat.clog 2 (2 * t) ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      let cand := candSet n q (fun j => ρ (Sum.inl j)) blocked
      (∀ x ∈ cand, hashVal A x = s →
        (∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b →
          ((BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD (output j) false = b) →
        (mrun G (mkBits ρ blocked)).getD w false = false) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal A x = s → hashVal A y = s → x = y) →
        ((mrun G (mkBits ρ blocked)).getD w false = false ↔
          ∃ x ∈ cand, hashVal A x = s ∧
            ∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b →
              ((BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD (output j) false = b))
  have hmonoF : ∀ {G1 G2 : List MGate} {s} {w}, Extends G1 G2 → FailInv G1 s w → FailInv G2 s w := by
    intro G1 G2 s w hext hinv
    rcases hinv with ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) _), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro ρ blocked
      have hvb := hv ρ blocked
      constructor
      · intro x hx hxs hacc; rw [mrun_of_extends hext _ w hlt]; exact hvb.1 x hx hxs hacc
      · intro hinj; rw [mrun_of_extends hext _ w hlt]; exact hvb.2 hinj
  have hFails := fintypeBuild_spec (ι := Fin (2 ^ m)) (2 + Fintype.card (PinType n q t))
    (16 * gates.length + 4 * t + 1) (addBucketFail n q t m gates output rScans.2.1 rScans.2.2)
    FailInv hmonoF rReady.1 hwfR (fun G s hwf hext => by
      have hextSG := extends_trans hextR hext
      have hlenSG := extends_len hextSG
      exact addBucketFail_spec gates output A rScans.2.1 rScans.2.2 G dpD hwf
        (fun s' => lt_of_lt_of_le (he_bd s') (by omega))
        (fun s' => by rw [mdepths_of_extends hextSG _ (he_bd s')]; exact he_dep s')
        (fun ρ blocked s' => by rw [mrun_of_extends hextSG _ _ (he_bd s')]; exact he_val ρ blocked s')
        (fun ib s' => lt_of_lt_of_le (hx_bd ib s') (by omega))
        (fun ib s' => by rw [mdepths_of_extends hextSG _ (hx_bd ib s')]; exact hx_dep ib s')
        (fun ρ blocked i b s' => by rw [mrun_of_extends hextSG _ _ (hx_bd (i, b) s')]; exact hx_val ρ blocked i b s')
        s)
  rcases hFails with ⟨hwfF, hextF, hlenF, hinvF⟩
  set rFails := fintypeBuild (addBucketFail n q t m gates output rScans.2.1 rScans.2.2) rReady.1 with hrF
  rw [Fintype.card_fin] at hlenF
  have hSort := addBitonicSort_spec (P := PinType n q t) false m rFails.1 rFails.2
    (dpD + 3 * D + 2 + Nat.clog 2 (2 * t)) hwfF (fun s => (hinvF s).1) (fun s => (hinvF s).2.1)
  rcases hSort with ⟨hwfSo, hextSo, hlenSo, hbdSo, hdepSo, hevSo⟩
  set rSort := addBitonicSort (2 + Fintype.card (PinType n q t)) false m rFails.1 rFails.2 with hrSo
  have hextRSo : Extends rReady.1 rSort.1 := extends_trans hextF hextSo
  have hlenRSo := extends_len hextRSo
  have hdpD_le : dpD ≤ 2 * (n + 1) * (Nat.clog 2 (q + 1) + 1) := by
    have h1 : Nat.clog 2 (2 * q) ≤ Nat.clog 2 (q + 1) + 1 := clog2_two_mul_le q
    have h2 : Nat.clog 2 q ≤ Nat.clog 2 (q + 1) := Nat.clog_mono_right 2 (by omega)
    dsimp [dpD]
    nlinarith
  have hcl_n : Nat.clog 2 n ≤ Nat.clog 2 (t + n + 2) := Nat.clog_mono_right 2 (by omega)
  have hcl_2t : Nat.clog 2 (2 * t) ≤ Nat.clog 2 (t + n + 2) + 1 := by
    have h1 := clog2_two_mul_le t
    have h2 : Nat.clog 2 (t + 1) ≤ Nat.clog 2 (t + n + 2) := Nat.clog_mono_right 2 (by omega)
    omega
  have hm_sq : m * (m + 1) ≤ 4 * (keyLog + 1) ^ 2 := by dsimp [m]; nlinarith
  have hm_le : m ≤ 4 * (keyLog + 1) ^ 2 := by dsimp [m]; nlinarith
  let dOut := 2 * (n + 1) * (Nat.clog 2 (q + 1) + 1) + 3 * D + 4 * (keyLog + 1) ^ 2 + Nat.clog 2 (t + n + 2) + 4
  let RepInv : List MGate → Fin (K + 1) → ℕ → Prop := fun G j w =>
    w < 2 + Fintype.card (PinType n q t) + G.length ∧
    (mdepths (2 + Fintype.card (PinType n q t)) G).getD w 0 ≤ dOut ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      (mrun G (mkBits ρ blocked)).getD w false = true ↔
        ((mrun rReady.1 (mkBits ρ blocked)).getD rReady.2 false = true ∧
          2 ^ m - bpop (fun s => (mrun rFails.1 (mkBits ρ blocked)).getD (rFails.2 s) false) ≤ j.val)
  have hmonoRep : ∀ {G1 G2 : List MGate} {j} {w}, Extends G1 G2 → RepInv G1 j w → RepInv G2 j w := by
    intro G1 G2 j w hext ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) _), ?_, ?_⟩
    · rw [mdepths_of_extends hext w hlt]; exact hd
    · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hv ρ blocked
  have hRep := fintypeBuild_spec (ι := Fin (K + 1)) (2 + Fintype.card (PinType n q t)) 1
    (fun G' j => addMGate (2 + Fintype.card (PinType n q t)) G' true rReady.2
      (rSort.2 ⟨2 ^ m - 1 - j.val, by omega⟩))
    RepInv hmonoRep rSort.1 hwfSo (fun G j hwf hext => by
      have hextRG := extends_trans hextRSo hext
      have hlenRG := extends_len hextRG
      have hlenSoG := extends_len hext
      have hlt1 : rReady.2 < 2 + Fintype.card (PinType n q t) + G.length :=
        lt_of_lt_of_le hbdR (by omega)
      have hlt2 : rSort.2 ⟨2 ^ m - 1 - j.val, by omega⟩ < 2 + Fintype.card (PinType n q t) + G.length :=
        lt_of_lt_of_le (hbdSo _) (by omega)
      refine ⟨addMGate_wf hwf true hlt1 hlt2, addMGate_extends _ G true _ _,
        by rw [addMGate_len], addMGate_out_lt _ G true _ _, ?_, ?_⟩
      · rw [addMGate_depth, mdepths_of_extends hextRG _ hbdR, mdepths_of_extends hext _ (hbdSo _)]
        have h1 := hdepR
        have h2 := hdepSo ⟨2 ^ m - 1 - j.val, by omega⟩
        dsimp [dOut]; omega
      · intro ρ blocked
        rw [addMGate_val]
        simp only [↓reduceIte, Bool.and_eq_true]
        rw [mrun_of_extends hextRG _ _ hbdR, mrun_of_extends hext _ _ (hbdSo _),
          hevSo (mkBits ρ blocked) ⟨2 ^ m - 1 - j.val, by omega⟩]
        simp only [sortedBit, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
        have hbp := bpop_le (fun s => (mrun rFails.1 (mkBits ρ blocked)).getD (rFails.2 s) false)
        have hjlt := j.isLt
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
  rcases hRep with ⟨hwfRep, hextRep, hlenRep, hinvRep⟩
  set rRep := fintypeBuild (ι := Fin (K + 1))
    (fun G' j => addMGate (2 + Fintype.card (PinType n q t)) G' true rReady.2
      (rSort.2 ⟨2 ^ m - 1 - j.val, by omega⟩)) rSort.1 with hrRep
  rw [Fintype.card_fin, mul_one] at hlenRep
  dsimp only [addSingleHash]
  change WellFormed (2 + Fintype.card (PinType n q t)) rRep.1 ∧ Extends G0 rRep.1 ∧
    rRep.1.length ≤ G0.length + 16 * ((n + 1) ^ 2 * (q + 1) ^ 3 + gates.length + t + n + (keyLog + 1) ^ 2 + 1) * 2 ^ m ∧
    (∀ j, rRep.2 j < 2 + Fintype.card (PinType n q t) + rRep.1.length) ∧
    (∀ j, (mdepths (2 + Fintype.card (PinType n q t)) rRep.1).getD (rRep.2 j) 0 ≤ dOut) ∧
    ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
      let cand := candSet n q (fun j => ρ (Sum.inl j)) blocked
      let acc := cand.filter (fun x =>
        ∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b →
          ((BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD (output j) false = b)
      (∀ j : Fin (K + 1), (mrun rRep.1 (mkBits ρ blocked)).getD (rRep.2 j) false = true → acc.card ≤ j.val) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal A x = hashVal A y → x = y) →
        ∀ j : Fin (K + 1), (mrun rRep.1 (mkBits ρ blocked)).getD (rRep.2 j) false = true ↔ acc.card ≤ j.val)
  refine ⟨hwfRep, extends_trans hextS (extends_trans hextR (extends_trans hextRSo hextRep)), ?_,
    fun j => (hinvRep j).1, fun j => (hinvRep j).2.1, ?_⟩
  · have h1a : 2 * n + 1 ≤ 3 * (n + 1) := by omega
    have h1b : 4 * n * q ^ 3 + q ≤ 4 * (n + 1) * (q + 1) ^ 3 := by
      have hq3 : q ^ 3 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have hq1 : q ≤ (q + 1) ^ 3 := le_trans (by omega) (Nat.le_self_pow (by omega) (q + 1))
      have hre : 4 * (n + 1) * (q + 1) ^ 3 = 4 * n * (q + 1) ^ 3 + 4 * (q + 1) ^ 3 := by ring
      have hm1 : 4 * n * q ^ 3 ≤ 4 * n * (q + 1) ^ 3 := Nat.mul_le_mul_left _ hq3
      omega
    have h1 : (2 * n + 1) * (4 * n * q ^ 3 + q) ≤ 12 * ((n + 1) ^ 2 * (q + 1) ^ 3) := by
      calc (2 * n + 1) * (4 * n * q ^ 3 + q)
          ≤ (3 * (n + 1)) * (4 * (n + 1) * (q + 1) ^ 3) := Nat.mul_le_mul h1a h1b
        _ = 12 * ((n + 1) ^ 2 * (q + 1) ^ 3) := by ring
    have hcoef : (2 * n + 1) * (4 * n * q ^ 3 + q) + (2 * n + 2) + (16 * gates.length + 4 * t + 1) +
        m * (m + 1) + 1 ≤
        16 * ((n + 1) ^ 2 * (q + 1) ^ 3 + gates.length + t + n + (keyLog + 1) ^ 2 + 1) := by omega
    have hmul := Nat.mul_le_mul_right (2 ^ m) hcoef
    have hre : ((2 * n + 1) * (4 * n * q ^ 3 + q) + (2 * n + 2) + (16 * gates.length + 4 * t + 1) +
        m * (m + 1) + 1) * 2 ^ m =
        (2 * n + 1) * (4 * n * q ^ 3 + q) * 2 ^ m + (2 * n + 2) * 2 ^ m +
        2 ^ m * (16 * gates.length + 4 * t + 1) + m * (m + 1) * 2 ^ m + 2 ^ m := by ring
    have hlenS' : rScans.1.length ≤ G0.length + (2 * n + 1) * (4 * n * q ^ 3 + q) * 2 ^ m := hlenS
    have hlenR' : rReady.1.length ≤ rScans.1.length + (2 * n + 2) * 2 ^ m := hlenR
    omega
  · intro ρ blocked
    set cand := candSet n q (fun j => ρ (Sum.inl j)) blocked
    set acc := cand.filter (fun x =>
      ∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b →
        ((BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD (output j) false = b)
    set f : Fin (2 ^ m) → Bool := fun s => (mrun rFails.1 (mkBits ρ blocked)).getD (rFails.2 s) false
    set F0 : Finset (Fin (2 ^ m)) := Finset.univ.filter (fun s => f s = false)
    have hF0_eq : 2 ^ m - bpop f = F0.card := by
      have hsum : bpop f + F0.card = 2 ^ m := bpop_add_card_false f
      omega
    have hsub : acc.image (hashVal A) ⊆ F0 := by
      intro s hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨x, hx, rfl⟩
      rw [Finset.mem_filter] at hx
      simp only [F0, Finset.mem_filter, Finset.mem_univ, true_and, f]
      exact ((hinvF (hashVal A x)).2.2 ρ blocked).1 x hx.1 rfl hx.2
    constructor
    · intro j hj
      rcases ((hinvRep j).2.2 ρ blocked).mp hj with ⟨hrdy, hcnt⟩
      have hinj := (hvalR ρ blocked).mp hrdy
      have hcard_img : (acc.image (hashVal A)).card = acc.card :=
        Finset.card_image_of_injOn (fun x hx y hy hxy =>
          hinj x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
      have hle : acc.card ≤ F0.card := by rw [← hcard_img]; exact Finset.card_le_card hsub
      rw [hF0_eq] at hcnt
      exact le_trans hle hcnt
    · intro hinj j
      have hrdy : (mrun rReady.1 (mkBits ρ blocked)).getD rReady.2 false = true :=
        (hvalR ρ blocked).mpr hinj
      have hF0_eq_img : F0 = acc.image (hashVal A) := by
        apply Finset.Subset.antisymm _ hsub
        intro s hs
        simp only [F0, Finset.mem_filter, Finset.mem_univ, true_and, f] at hs
        have hinj_s : ∀ x ∈ cand, ∀ y ∈ cand, hashVal A x = s → hashVal A y = s → x = y :=
          fun x hx y hy hxs hys => hinj x hx y hy (hxs.trans hys.symm)
        rcases (((hinvF s).2.2 ρ blocked).2 hinj_s).mp hs with ⟨x, hx, hxs, hacc⟩
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hacc⟩, hxs⟩
      have hcard_img : (acc.image (hashVal A)).card = acc.card :=
        Finset.card_image_of_injOn (fun x hx y hy hxy =>
          hinj x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
      rw [(hinvRep j).2.2 ρ blocked, hF0_eq, hF0_eq_img, hcard_img, hrdy]
      simp only [true_and]
      rfl

noncomputable def buildFullCircuit (n q t K : ℕ) (gates : List BinaryGate) (output : Fin t → ℕ)
    (H : Fin (2 * n * q ^ 2 + 2 * n + 1) → (Fin (2 * Nat.clog 2 (K + 1)) → Fin n → Bool)) :
    List MGate × (Fin (K + 1) → ℕ) :=
  let N := 2 + Fintype.card (PinType n q t)
  let R := 2 * n * q ^ 2 + 2 * n + 1
  let rBase := buildBaseEdges n q t []
  let rHashes := fintypeBuild (ι := Fin R)
    (fun G' idx => addSingleHash n q t K gates output rBase.2 (H idx) G') rBase.1
  fintypeBuild (ι := Fin (K + 1))
    (fun G' j => addTree false N G' (ofFintype (fun idx : Fin R => rHashes.2 idx j))) rHashes.1

end PEqualNP.Outside.L_pcx_314_aux

theorem PEqualNP.Outside.L_pcx_314 : (∀ (n q t K : ℕ) (gates : List PEqualNP.MetaComplexity.BinaryGate) (output : Fin t → ℕ),
  let X := Fin n → Bool
  let V := Fin n ⊕ Fin t
  let Edge := Fin n × Fin q × Bool × Fin q
  let P := (V × Bool) ⊕ Edge
  let C : PEqualNP.MetaComplexity.BinaryCircuit := ⟨gates,0⟩
  let dep := gates.foldl (fun (w : List ℕ) g =>
    w ++ [max (w.getD g.left 0) (w.getD g.right 0)+1]) (List.replicate n 0)
  let D := (Finset.univ : Finset (Fin t)).sup (fun j => dep.getD (output j) 0)
  let keyLog := Nat.clog 2 (K+1)
  let budget := 65536*(n+1)*(q+1)^2*(K+1)^2*
    ((n+1)^2*(q+1)^3+gates.length+t+n+(keyLog+1)^2+1)
  let rounds := 64*((n+1)*(Nat.clog 2 (q+1)+1)+D+(keyLog+1)^2+Nat.clog 2 (t+n+2)+1)
  let source := fun (a : P → Bool) =>
    [false,true] ++ List.ofFn (fun j : Fin (Fintype.card P) => a ((Fintype.equivFin P).symm j))
  let Gate := Bool × ℕ × ℕ
  let run := fun (G : List Gate) (a : P → Bool) =>
    G.foldl (fun (w : List Bool) g =>
      let l := w.getD g.2.1 false
      let r := w.getD g.2.2 false
      w ++ [if g.1 then l && r else l || r]) (source a)
  let N := 2 + Fintype.card P
  let depths := fun (G : List Gate) =>
    G.foldl (fun (w : List ℕ) g =>
      w ++ [max (w.getD g.2.1 0) (w.getD g.2.2 0) + 1]) (List.replicate N 0)
  ∃ (G : List Gate) (out : Fin (K+1) → ℕ), G.length ≤ budget ∧
    (∀ i : Fin G.length, (G.get i).2.1 < N+i.val ∧ (G.get i).2.2 < N+i.val) ∧
    (∀ j, out j < N+G.length ∧ (depths G).getD (out j) 0 ≤ rounds) ∧
    ∀ (ρ : V → Option Bool) (blocked : Edge → Bool),
      let bits : P → Bool := Sum.elim (fun p => decide (ρ p.1 = some p.2)) blocked
      let candidates := Finset.univ.filter (fun x : X =>
        (∀ i : Fin n, ∀ b : Bool, ρ (Sum.inl i) = some b → x i = b) ∧
        ∃ path : Fin (n+1) → Fin q, path 0 = path (Fin.last n) ∧
          ∀ i : Fin n, blocked (i,path i.castSucc,x i,path i.succ) = false)
      let accepted := candidates.filter (fun x =>
        ∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b →
          (C.wires (List.ofFn x)).getD (output j) false = b)
      (∀ j : Fin (K+1), (run G bits).getD (out j) false = true → accepted.card ≤ j.val) ∧
      (candidates.card ≤ K → ∀ j : Fin (K+1),
        (run G bits).getD (out j) false = true ↔ accepted.card ≤ j.val)) := by
  open PEqualNP.Outside.L_pcx_314_aux in
  intro n q t K gates output
  dsimp only
  by_cases hq0 : q = 0
  · subst hq0
    refine ⟨[], fun _ => 1, Nat.zero_le _, fun i => Fin.elim0 i, ?_, ?_⟩
    · intro j
      refine ⟨by simp; omega, ?_⟩
      change (mdepths (2 + Fintype.card (PinType n 0 t)) []).getD 1 0 ≤ _
      rw [mdepths_base [] 1 (by omega)]
      exact Nat.zero_le _
    · intro ρ blocked
      have hcand_empty : Finset.univ.filter (fun x : Fin n → Bool =>
          (∀ i : Fin n, ∀ b : Bool, ρ (Sum.inl i) = some b → x i = b) ∧
          ∃ path : Fin (n + 1) → Fin 0, path 0 = path (Fin.last n) ∧
            ∀ i : Fin n, blocked (i, path i.castSucc, x i, path i.succ) = false) = ∅ := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨_, path, _⟩; exact Fin.elim0 (path 0)
      have hacc0 : (Finset.filter (fun x =>
          ∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b →
            ((PEqualNP.MetaComplexity.BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD (output j) false = b)
          (Finset.univ.filter (fun x : Fin n → Bool =>
            (∀ i : Fin n, ∀ b : Bool, ρ (Sum.inl i) = some b → x i = b) ∧
            ∃ path : Fin (n + 1) → Fin 0, path 0 = path (Fin.last n) ∧
              ∀ i : Fin n, blocked (i, path i.castSucc, x i, path i.succ) = false))).card = 0 := by
        rw [hcand_empty]; simp
      constructor
      · intro j _; omega
      · intro _ j
        have h1 : (mrun (P := PinType n 0 t) [] (mkBits ρ blocked)).getD 1 false = true :=
          mrun_const1 [] (mkBits ρ blocked)
        change (mrun (P := PinType n 0 t) [] (mkBits ρ blocked)).getD 1 false = true ↔ _
        rw [h1, hacc0]
        simp
  · rcases hashFamily_exists n q K with ⟨H, hH⟩
    let keyLog := Nat.clog 2 (K + 1)
    let m := 2 * keyLog
    let R := 2 * n * q ^ 2 + 2 * n + 1
    let dep := gates.foldl depStep (List.replicate n 0)
    let D := (Finset.univ : Finset (Fin t)).sup (fun j => dep.getD (output j) 0)
    let S := (n + 1) ^ 2 * (q + 1) ^ 3 + gates.length + t + n + (keyLog + 1) ^ 2 + 1
    let dSingle := 2 * (n + 1) * (Nat.clog 2 (q + 1) + 1) + 3 * D + 4 * (keyLog + 1) ^ 2 + Nat.clog 2 (t + n + 2) + 4
    have hBase := buildBaseEdges_spec n q t [] (fun i => Fin.elim0 i)
    rcases hBase with ⟨hwfB, _, hlenB, hbe_bd, hbe_dep, hbe_val⟩
    set rBase := buildBaseEdges n q t [] with hrB
    let HashInv : List MGate → Fin R → (Fin (K + 1) → ℕ) → Prop := fun G idx outH =>
      (∀ j, outH j < 2 + Fintype.card (PinType n q t) + G.length) ∧
      (∀ j, (mdepths (2 + Fintype.card (PinType n q t)) G).getD (outH j) 0 ≤ dSingle) ∧
      ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
        let cand := candSet n q (fun j => ρ (Sum.inl j)) blocked
        let acc := cand.filter (fun x =>
          ∀ j : Fin t, ∀ b : Bool, ρ (Sum.inr j) = some b →
            ((PEqualNP.MetaComplexity.BinaryCircuit.mk gates 0).wires (List.ofFn x)).getD (output j) false = b)
        (∀ j : Fin (K + 1), (mrun G (mkBits ρ blocked)).getD (outH j) false = true → acc.card ≤ j.val) ∧
        ((∀ x ∈ cand, ∀ y ∈ cand, hashVal (H idx) x = hashVal (H idx) y → x = y) →
          ∀ j : Fin (K + 1), (mrun G (mkBits ρ blocked)).getD (outH j) false = true ↔ acc.card ≤ j.val)
    have hmonoH : ∀ {G1 G2 : List MGate} {idx} {outH}, Extends G1 G2 → HashInv G1 idx outH → HashInv G2 idx outH := by
      intro G1 G2 idx outH hext ⟨hbd, hdep, hval⟩
      refine ⟨fun j => lt_of_lt_of_le (hbd j) (Nat.add_le_add_left (extends_len hext) _), ?_, ?_⟩
      · intro j; rw [mdepths_of_extends hext _ (hbd j)]; exact hdep j
      · intro ρ blocked
        have hv := hval ρ blocked
        constructor
        · intro j hj; rw [mrun_of_extends hext _ _ (hbd j)] at hj; exact hv.1 j hj
        · intro hinj j; rw [mrun_of_extends hext _ _ (hbd j)]; exact hv.2 hinj j
    have hHashes := fintypeBuild_spec (ι := Fin R) (2 + Fintype.card (PinType n q t)) (16 * S * 2 ^ m)
      (fun G' idx => addSingleHash n q t K gates output rBase.2 (H idx) G')
      HashInv hmonoH rBase.1 hwfB (fun G idx hwf hext => by
        have hlenG := extends_len hext
        exact addSingleHash_spec n q t K gates output rBase.2 (H idx) G hwf
          (fun e => lt_of_lt_of_le (hbe_bd e) (by omega))
          (fun e => by rw [mdepths_of_extends hext _ (hbe_bd e)]; exact hbe_dep e)
          (fun ρ blocked e => by rw [mrun_of_extends hext _ _ (hbe_bd e)]; exact hbe_val ρ blocked e))
    rcases hHashes with ⟨hwfH, hextH, hlenH, hinvH⟩
    set rHashes := fintypeBuild (ι := Fin R)
      (fun G' idx => addSingleHash n q t K gates output rBase.2 (H idx) G') rBase.1 with hrH
    rw [Fintype.card_fin] at hlenH
    let OutInv : List MGate → Fin (K + 1) → ℕ → Prop := fun G j w =>
      w < 2 + Fintype.card (PinType n q t) + G.length ∧
      (mdepths (2 + Fintype.card (PinType n q t)) G).getD w 0 ≤ dSingle + Nat.clog 2 R ∧
      ∀ (ρ : (Fin n ⊕ Fin t) → Option Bool) (blocked : (Fin n × Fin q × Bool × Fin q) → Bool),
        (mrun G (mkBits ρ blocked)).getD w false = true ↔
          ∃ idx : Fin R, (mrun rHashes.1 (mkBits ρ blocked)).getD (rHashes.2 idx j) false = true
    have hmonoO : ∀ {G1 G2 : List MGate} {j} {w}, Extends G1 G2 → OutInv G1 j w → OutInv G2 j w := by
      intro G1 G2 j w hext ⟨hlt, hd, hv⟩
      refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len hext) _), ?_, ?_⟩
      · rw [mdepths_of_extends hext w hlt]; exact hd
      · intro ρ blocked; rw [mrun_of_extends hext _ w hlt]; exact hv ρ blocked
    have hFinal := fintypeBuild_spec (ι := Fin (K + 1)) (2 + Fintype.card (PinType n q t)) R
      (fun G' j => addTree false (2 + Fintype.card (PinType n q t)) G'
        (ofFintype (fun idx : Fin R => rHashes.2 idx j)))
      OutInv hmonoO rHashes.1 hwfH (fun G j hwf hext => by
        have hlenG := extends_len hext
        have htr := addTree_spec (P := PinType n q t) false G
          (ofFintype (fun idx : Fin R => rHashes.2 idx j)) dSingle hwf
          (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨idx, rfl⟩; exact lt_of_lt_of_le ((hinvH idx).1 j) (by omega))
          (fun w hw => by
            rcases (mem_ofFintype_iff _ _).mp hw with ⟨idx, rfl⟩
            rw [mdepths_of_extends hext _ ((hinvH idx).1 j)]; exact (hinvH idx).2.1 j)
        rcases htr with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
        rw [ofFintype_length, Fintype.card_fin] at hlenT hdepT
        refine ⟨hwfT, hextT, hlenT, hbdT, hdepT, fun ρ blocked => ?_⟩
        rw [hevT (mkBits ρ blocked), evalList_ofFintype_false]
        apply exists_congr; intro idx
        rw [mrun_of_extends hext _ _ ((hinvH idx).1 j)])
    rcases hFinal with ⟨hwfF, _, hlenF, hinvF⟩
    set rFinal := fintypeBuild (ι := Fin (K + 1))
      (fun G' j => addTree false (2 + Fintype.card (PinType n q t)) G'
        (ofFintype (fun idx : Fin R => rHashes.2 idx j))) rHashes.1 with hrF
    rw [Fintype.card_fin] at hlenF
    refine ⟨rFinal.1, rFinal.2, ?_, hwfF, ?_, ?_⟩
    · have hM_le : 2 ^ m ≤ 4 * (K + 1) ^ 2 := by
        have h1 := two_pow_clog2_le K
        have h2 : (2 ^ keyLog) ^ 2 ≤ (2 * (K + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
        have h3 : (2 ^ keyLog) ^ 2 = 2 ^ m := by rw [← pow_mul, Nat.mul_comm]
        nlinarith
      have hR_le : R ≤ 4 * (n + 1) * (q + 1) ^ 2 := by
        have hq2 : q ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow 2 (q + 1) (Nat.succ_pos q)
        have hm1 : 2 * n * q ^ 2 ≤ 2 * n * (q + 1) ^ 2 := Nat.mul_le_mul_left _ hq2
        have hm2 : 2 * n ≤ 2 * n * (q + 1) ^ 2 := Nat.le_mul_of_pos_right _ h1
        have hre : 4 * (n + 1) * (q + 1) ^ 2 = 2 * n * (q + 1) ^ 2 + 2 * n * (q + 1) ^ 2 + 4 * (q + 1) ^ 2 := by ring
        dsimp [R]; omega
      have hM_ge : K + 1 ≤ 2 ^ m := K_succ_le_pow_two_clog K
      have h1_le_S : 1 ≤ S := by dsimp [S]; omega
      have h1_le_M : 1 ≤ 2 ^ m := by omega
      have hbase_le : 2 * n * q ^ 2 ≤ R * S * 2 ^ m := by
        have h1 : 2 * n * q ^ 2 ≤ R := by dsimp [R]; omega
        have h2 : R ≤ R * (S * 2 ^ m) := Nat.le_mul_of_pos_right R (Nat.mul_pos h1_le_S h1_le_M)
        calc 2 * n * q ^ 2 ≤ R := h1
          _ ≤ R * (S * 2 ^ m) := h2
          _ = R * S * 2 ^ m := by ring
      have hfin_le : (K + 1) * R ≤ R * S * 2 ^ m := by
        calc (K + 1) * R ≤ 2 ^ m * R := Nat.mul_le_mul_right R hM_ge
          _ = R * 2 ^ m := by ring
          _ ≤ R * (S * 2 ^ m) := Nat.mul_le_mul_left R (Nat.le_mul_of_pos_left _ h1_le_S)
          _ = R * S * 2 ^ m := by ring
      have hlen0 : ([] : List MGate).length = 0 := rfl
      have htot : rFinal.1.length ≤ 18 * (R * 2 ^ m * S) := by
        have h1 : R * (16 * S * 2 ^ m) = 16 * (R * 2 ^ m * S) := by ring
        have h2 : R * S * 2 ^ m = R * 2 ^ m * S := by ring
        omega
      have hRM_le : R * 2 ^ m ≤ 16 * (n + 1) * (q + 1) ^ 2 * (K + 1) ^ 2 := by
        calc R * 2 ^ m ≤ (4 * (n + 1) * (q + 1) ^ 2) * (4 * (K + 1) ^ 2) := Nat.mul_le_mul hR_le hM_le
          _ = 16 * (n + 1) * (q + 1) ^ 2 * (K + 1) ^ 2 := by ring
      calc rFinal.1.length
          ≤ 18 * (R * 2 ^ m * S) := htot
        _ ≤ 18 * (16 * (n + 1) * (q + 1) ^ 2 * (K + 1) ^ 2 * S) :=
            Nat.mul_le_mul_left 18 (Nat.mul_le_mul_right S hRM_le)
        _ = 288 * ((n + 1) * (q + 1) ^ 2 * (K + 1) ^ 2 * S) := by ring
        _ ≤ 65536 * ((n + 1) * (q + 1) ^ 2 * (K + 1) ^ 2 * S) := Nat.mul_le_mul_right _ (by omega)
        _ = 65536 * (n + 1) * (q + 1) ^ 2 * (K + 1) ^ 2 * S := by ring
    · intro j
      refine ⟨(hinvF j).1, ?_⟩
      have hd := (hinvF j).2.1
      have hclR := clog2_R_le n q t
      change (mdepths (2 + Fintype.card (PinType n q t)) rFinal.1).getD (rFinal.2 j) 0 ≤
        64 * ((n + 1) * (Nat.clog 2 (q + 1) + 1) + D + (keyLog + 1) ^ 2 + Nat.clog 2 (t + n + 2) + 1)
      have hq1 : 2 * Nat.clog 2 (q + 1) ≤ 2 * ((n + 1) * (Nat.clog 2 (q + 1) + 1)) := by
        have hpos : 0 < n + 1 := by omega
        have hle := Nat.le_mul_of_pos_left (Nat.clog 2 (q + 1) + 1) hpos
        omega
      have h2u : 2 * (n + 1) * (Nat.clog 2 (q + 1) + 1) = 2 * ((n + 1) * (Nat.clog 2 (q + 1) + 1)) := by ring
      dsimp only [dSingle, R] at hd
      omega
    · intro ρ blocked
      constructor
      · intro j hj
        change (mrun rFinal.1 (mkBits ρ blocked)).getD (rFinal.2 j) false = true at hj
        rcases ((hinvF j).2.2 ρ blocked).mp hj with ⟨idx, hidx⟩
        exact ((hinvH idx).2.2 ρ blocked).1 j hidx
      · intro hcard j
        change (mrun rFinal.1 (mkBits ρ blocked)).getD (rFinal.2 j) false = true ↔ _
        rw [(hinvF j).2.2 ρ blocked]
        constructor
        · rintro ⟨idx, hidx⟩
          exact ((hinvH idx).2.2 ρ blocked).1 j hidx
        · intro hacc
          rcases hH (fun i => ρ (Sum.inl i)) blocked hcard with ⟨idx, hidx_inj⟩
          exact ⟨idx, (((hinvH idx).2.2 ρ blocked).2 hidx_inj j).mpr hacc⟩
