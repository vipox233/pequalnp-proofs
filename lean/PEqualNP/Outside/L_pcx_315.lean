import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_315_aux

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


-- Part 1: Pins, global hash family, shift-register window, and local evaluation of early rounds

abbrev Pin315 (k : ℕ) := (Fin 7 × Fin k) × Bool

noncomputable def pinWire (k : ℕ) (p : Pin315 k) : ℕ :=
  2 + (Fintype.equivFin (Pin315 k) p).val

lemma pinWire_lt (k : ℕ) (G : List MGate) (p : Pin315 k) :
    pinWire k p < 2 + Fintype.card (Pin315 k) + G.length := by
  unfold pinWire
  have := (Fintype.equivFin (Pin315 k) p).isLt
  omega

lemma pinWire_depth (k : ℕ) (G : List MGate) (p : Pin315 k) :
    (mdepths (2 + Fintype.card (Pin315 k)) G).getD (pinWire k p) 0 = 0 := by
  apply mdepths_base
  unfold pinWire
  have := (Fintype.equivFin (Pin315 k) p).isLt
  omega

lemma pinWire_val (k : ℕ) (G : List MGate) (a : Pin315 k → Bool) (p : Pin315 k) :
    (mrun G a).getD (pinWire k p) false = a p :=
  mrun_input G a p

def mkBits {k : ℕ} (ρ : (Fin 7 × Fin k) → Option Bool) : Pin315 k → Bool :=
  fun p => decide (ρ p.1 = some p.2)

def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def constFn (k j : ℕ) : ℕ := 3 ^ (k + j) % 2 ^ k

def firstFn (k t rowKey rowName : ℕ) : ℕ :=
  (List.range t).foldl (fun rowState rowIndex =>
    stepFn k (rowState ^^^ rotFn k 1 rowState ^^^ rotFn k (k - 1) rowState) ^^^
      rotFn k (2 * rowIndex) rowKey ^^^ constFn k (rowIndex + 1))
    (rotFn k 1 rowKey ^^^ rowName)

def secondFn (k r t colKey colName : ℕ) : ℕ :=
  (List.range t).foldl (fun colState colIndex =>
    stepFn k (colState ^^^ rotFn k 2 colState ^^^ rotFn k (k - 2) colState) ^^^
      rotFn k (3 * (colIndex + 1) + 1) colKey ^^^ constFn k (r + (colIndex + 1)))
    (rotFn k 3 colKey ^^^ colName)

lemma rotFn_lt (k s word : ℕ) (_hk : 0 < k) : rotFn k s word < 2 ^ k := by
  unfold rotFn
  exact Nat.mod_lt _ (by positivity)

lemma constFn_lt (k j : ℕ) : constFn k j < 2 ^ k := by
  unfold constFn
  exact Nat.mod_lt _ (by positivity)

lemma foldBits_lt (l : ℕ) (g : ℕ → Bool) :
    (List.range l).foldl (fun acc i => acc ||| ((g i).toNat <<< i)) 0 < 2 ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (by omega))
    · rw [Nat.shiftLeft_eq, pow_succ]
      cases g l <;> simp

lemma stepFn_lt (k word : ℕ) : stepFn k word < 2 ^ k :=
  foldBits_lt k _

lemma foldBits_testBit (l : ℕ) (g : ℕ → Bool) (j : ℕ) :
    ((List.range l).foldl (fun acc i => acc ||| ((g i).toNat <<< i)) 0).testBit j =
      if j < l then g j else false := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases hjlt : j < l
    · have h1 : ¬ (l ≤ j) := by omega
      simp [hjlt, show j < l + 1 by omega, h1]
    · by_cases hjeq : j = l
      · subst hjeq
        simp [show (g j).toNat.testBit 0 = g j from by cases g j <;> decide]
      · have hgt : l < j := by omega
        have hnot : ¬ (j < l + 1) := by omega
        have hsub : 1 ≤ j - l := by omega
        have hb0 : (g l).toNat.testBit (j - l) = false := by
          apply Nat.testBit_lt_two_pow
          have : (g l).toNat < 2 ^ 1 := by cases g l <;> decide
          exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hsub)
        simp [hjlt, hnot, hb0]

lemma stepFn_testBit (k word i : ℕ) (hi : i < k) :
    (stepFn k word).testBit i =
      Bool.xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  unfold stepFn
  rw [foldBits_testBit]
  simp [hi]

lemma firstFn_lt {k : ℕ} (hk : 0 < k) (t : ℕ) {rowKey rowName : ℕ}
    (_hkey : rowKey < 2 ^ k) (hname : rowName < 2 ^ k) :
    firstFn k t rowKey rowName < 2 ^ k := by
  unfold firstFn
  induction t with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    exact Nat.xor_lt_two_pow (rotFn_lt k 1 rowKey hk) hname
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow (stepFn_lt k _) (rotFn_lt k (2 * t) rowKey hk))
      (constFn_lt k (t + 1))

lemma secondFn_lt {k : ℕ} (hk : 0 < k) (r t : ℕ) {colKey colName : ℕ}
    (_hkey : colKey < 2 ^ k) (hname : colName < 2 ^ k) :
    secondFn k r t colKey colName < 2 ^ k := by
  unfold secondFn
  induction t with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    exact Nat.xor_lt_two_pow (rotFn_lt k 3 colKey hk) hname
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow (stepFn_lt k _) (rotFn_lt k (3 * (t + 1) + 1) colKey hk))
      (constFn_lt k (r + (t + 1)))

lemma rotFn_testBit {k : ℕ} (hk : 0 < k) (s word i : ℕ)
    (hw : word < 2 ^ k) (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + (k - s % k)) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hs : s % k < k := Nat.mod_lt s hk
  by_cases hia : s % k ≤ i
  · have hge : k ≤ i + (k - s % k) := by omega
    have hr0 : word.testBit (k - s % k + i) = false := by
      rw [Nat.add_comm]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + (k - s % k)) % k = i - s % k := by
      rw [show i + (k - s % k) = (i - s % k) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    simp [hia, hr0, hmod]
  · have hlt : i + (k - s % k) < k := by omega
    simp [hia, Nat.mod_eq_of_lt hlt, Nat.add_comm]

lemma rotPos_sub (hk : 0 < k) (C m s : ℕ) (hm : s ≤ m) :
    ((C + m) % k + (k - s % k)) % k = (C + (m - s)) % k := by
  have hs : s % k < k := Nat.mod_lt s hk
  have hdiv : s = k * (s / k) + s % k := (Nat.div_add_mod s k).symm
  rw [Nat.add_mod ((C + m) % k), Nat.mod_mod, ← Nat.add_mod]
  rw [show C + m + (k - s % k) = C + (m - s) + (k * (s / k) + k) by omega,
    show C + (m - s) + (k * (s / k) + k) = C + (m - s) + k * (s / k + 1) by ring,
    Nat.add_mul_mod_self_left]

lemma rotPos_k_sub_one (hk : 0 < k) (C m : ℕ) :
    ((C + m) % k + (k - (k - 1) % k)) % k = (C + (m + 1)) % k := by
  have h1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, show k - (k - 1) = 1 by omega, Nat.add_mod ((C + m) % k), Nat.mod_mod, ← Nat.add_mod]
  ring_nf

lemma rotPos_k_sub_two (hk : 0 < k) (C m : ℕ) :
    ((C + m) % k + (k - (k - 2) % k)) % k = (C + (m + 2)) % k := by
  by_cases hk1 : k = 1
  · subst hk1; simp only [Nat.mod_one]
  · by_cases hk2 : k = 2
    · subst hk2; simp [Nat.add_mod]
    · have h2 : (k - 2) % k = k - 2 := Nat.mod_eq_of_lt (by omega)
      rw [h2, show k - (k - 2) = 2 by omega, Nat.add_mod ((C + m) % k), Nat.mod_mod, ← Nat.add_mod]
      ring_nf

-- Window index definitions
def winShift (k d : ℕ) : ℕ := ((3 * d + 3) / k + 1) * k - (3 * d + 3)

def winPos (k d i m : ℕ) (hk : 0 < k) : Fin k :=
  ⟨(i + winShift k d + m) % k, Nat.mod_lt _ hk⟩

def enterIdx (k d : ℕ) (hk : 0 < k) (l : Fin k) : Fin k :=
  winPos k d l.val (7 * d + 3) hk

def enterInv (k d : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + k - (winShift k d + (7 * d + 3)) % k) % k, Nat.mod_lt _ hk⟩

lemma enterIdx_inv (k d : ℕ) (hk : 0 < k) (i : Fin k) :
    enterIdx k d hk (enterInv k d hk i) = i := by
  apply Fin.ext
  unfold enterIdx enterInv winPos
  dsimp only
  set C := winShift k d + (7 * d + 3)
  have hC : C % k < k := Nat.mod_lt C hk
  have hdiv : C = k * (C / k) + C % k := (Nat.div_add_mod C k).symm
  rw [show (i.val + k - C % k) % k + winShift k d + (7 * d + 3) =
      (i.val + k - C % k) % k + C by omega]
  rw [Nat.add_mod ((i.val + k - C % k) % k), Nat.mod_mod, ← Nat.add_mod]
  rw [show i.val + k - C % k + C = i.val + (k * (C / k) + k) by omega,
    show i.val + (k * (C / k) + k) = i.val + k * (C / k + 1) by ring,
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt i.isLt

lemma enterInv_idx (k d : ℕ) (hk : 0 < k) (l : Fin k) :
    enterInv k d hk (enterIdx k d hk l) = l := by
  apply Fin.ext
  unfold enterIdx enterInv winPos
  dsimp only
  set C := winShift k d + (7 * d + 3)
  have hC : C % k < k := Nat.mod_lt C hk
  have hdiv : C = k * (C / k) + C % k := (Nat.div_add_mod C k).symm
  rw [show l.val + winShift k d + (7 * d + 3) = l.val + C by omega]
  rw [show (l.val + C) % k + k - C % k = (l.val + C) % k + (k - C % k) by
    have := Nat.mod_lt (l.val + C) hk; omega]
  rw [Nat.add_mod ((l.val + C) % k), Nat.mod_mod, ← Nat.add_mod]
  rw [show l.val + C + (k - C % k) = l.val + (k * (C / k) + k) by omega,
    show l.val + (k * (C / k) + k) = l.val + k * (C / k + 1) by ring,
    Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt l.isLt

def enterEquiv (k d : ℕ) (hk : 0 < k) : Equiv.Perm (Fin k) where
  toFun := enterIdx k d hk
  invFun := enterInv k d hk
  left_inv := enterInv_idx k d hk
  right_inv := enterIdx_inv k d hk

lemma winPos_center (k d : ℕ) (hk : 0 < k) (i : Fin k) :
    winPos k d i.val (3 * d + 3) hk = i := by
  apply Fin.ext
  unfold winPos winShift
  dsimp only
  have h1 : (3 * d + 3) ≤ ((3 * d + 3) / k + 1) * k := by
    have hmod := Nat.mod_lt (3 * d + 3) hk
    have hdiv := Nat.div_add_mod (3 * d + 3) k
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((3 * d + 3) / k) k]; omega
  rw [add_assoc i.val, Nat.sub_add_cancel h1]
  rw [Nat.mul_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt i.isLt

def nextWin (B : ℕ) (w : Fin (2 ^ B)) (b : Bool) : Fin (2 ^ B) :=
  ⟨((w.val >>> 1) ||| (b.toNat <<< (B - 1))) % 2 ^ B, Nat.mod_lt _ (by positivity)⟩

def prevWin (B : ℕ) (v : Fin (2 ^ B)) (old0 : Bool) : Fin (2 ^ B) :=
  ⟨((v.val <<< 1) ||| old0.toNat) % 2 ^ B, Nat.mod_lt _ (by positivity)⟩

def joinWin (B : ℕ) (old0 : Bool) (v : Fin (2 ^ B)) : Fin (2 ^ (B + 1)) :=
  ⟨old0.toNat + 2 * v.val, by rw [pow_succ]; have := v.isLt; cases old0 <;> simp <;> omega⟩

lemma nextWin_testBit {B : ℕ} (_hB : 0 < B) (w : Fin (2 ^ B)) (b : Bool) {m : ℕ} (hm : m < B) :
    (nextWin B w b).val.testBit m =
      if m < B - 1 then w.val.testBit (m + 1) else b := by
  unfold nextWin
  rw [Nat.testBit_mod_two_pow, decide_eq_true hm, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  by_cases hlt : m < B - 1
  · have h1 : ¬ (B - 1 ≤ m) := by omega
    simp [hlt, h1, Nat.add_comm 1 m]
  · have heq : m = B - 1 := by omega
    subst heq
    have hw0 : w.val.testBit (1 + (B - 1)) = false := by
      apply Nat.testBit_lt_two_pow
      rw [show 1 + (B - 1) = B by omega]
      exact w.isLt
    simp [hw0, show b.toNat.testBit 0 = b from by cases b <;> decide]

lemma prevWin_testBit {B : ℕ} (_hB : 0 < B) (v : Fin (2 ^ B)) (old0 : Bool) {m : ℕ} (hm : m < B) :
    (prevWin B v old0).val.testBit m =
      if m = 0 then old0 else v.val.testBit (m - 1) := by
  unfold prevWin
  rw [Nat.testBit_mod_two_pow, decide_eq_true hm, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft]
  cases m with
  | zero =>
    have hv0 : v.val.testBit 0 = false → True := fun _ => trivial
    simp [show old0.toNat.testBit 0 = old0 from by cases old0 <;> decide]
  | succ m' =>
    have hb0 : old0.toNat.testBit (m' + 1) = false := by
      apply Nat.testBit_lt_two_pow
      have : old0.toNat < 2 ^ 1 := by cases old0 <;> decide
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by omega))
    simp [hb0]

lemma joinWin_testBit {B : ℕ} (old0 : Bool) (v : Fin (2 ^ B)) {m : ℕ} (hm : m ≤ B) :
    (joinWin B old0 v).val.testBit m =
      if m = 0 then old0 else v.val.testBit (m - 1) := by
  unfold joinWin
  cases m with
  | zero =>
    rw [Nat.testBit_zero]
    cases old0 <;> simp
  | succ m' =>
    rw [Nat.testBit_succ]
    have hdiv : (old0.toNat + 2 * v.val) / 2 = v.val := by
      cases old0 <;> simp <;> omega
    rw [hdiv]; rfl

lemma nextWin_iff_prevWin {B : ℕ} (hB : 0 < B) (w v : Fin (2 ^ B)) (b : Bool) :
    v = nextWin B w b ↔ (b = v.val.testBit (B - 1) ∧ w = prevWin B v (w.val.testBit 0)) := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [nextWin_testBit hB w b (by omega)]; simp
    · apply Fin.ext; apply Nat.eq_of_testBit_eq; intro m
      by_cases hm : m < B
      · rw [prevWin_testBit hB (nextWin B w b) (w.val.testBit 0) hm]
        cases m with
        | zero => rfl
        | succ m' =>
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
          rw [nextWin_testBit hB w b (by omega)]
          simp [show m' < B - 1 by omega]
      · have h2 : 2 ^ B ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le w.isLt h2),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (prevWin B _ _).isLt h2)]
  · rintro ⟨hb, hw⟩
    subst hb
    apply Fin.ext; apply Nat.eq_of_testBit_eq; intro m
    by_cases hm : m < B
    · rw [nextWin_testBit hB w _ hm]
      by_cases hlt : m < B - 1
      · simp only [hlt, ↓reduceIte]
        conv_rhs => rw [hw]
        rw [prevWin_testBit hB v (w.val.testBit 0) (by omega)]
        simp
      · have heq : m = B - 1 := by omega
        subst heq; simp
    · have h2 : 2 ^ B ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le v.isLt h2),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (nextWin B _ _).isLt h2)]

lemma winBefore_shift {k d : ℕ} (hk : 0 < k) (x : Fin k → Bool) (l : ℕ) :
    let B := 7 * d + 3
    let winOf : ℕ → Fin (2 ^ B) := fun i => ⟨bitsToNat (fun m : Fin B => x (winPos k d i m.val hk)), bitsToNat_lt _⟩
    winOf (l + 1) = nextWin B (winOf l) (x (winPos k d l B hk)) := by
  intro B winOf
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro m
  by_cases hm : m < B
  · rw [nextWin_testBit (by omega : 0 < B) (winOf l) _ hm]
    change (bitsToNat _).testBit m = _
    rw [bitsToNat_testBit (i := ⟨m, hm⟩)]
    have hpos : winPos k d (l + 1) m hk = winPos k d l (m + 1) hk := by
      apply Fin.ext; simp [winPos]; ring_nf
    by_cases hlt : m < B - 1
    · simp only [hlt, ↓reduceIte]
      change x (winPos k d (l + 1) m hk) = (bitsToNat _).testBit (m + 1)
      rw [bitsToNat_testBit (i := ⟨m + 1, by omega⟩), hpos]
    · have heq : m = B - 1 := by omega
      subst heq
      simp only [lt_self_iff_false, ↓reduceIte]
      rw [hpos, show B - 1 + 1 = B by omega]
  · have h2 : 2 ^ B ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (winOf (l + 1)).isLt h2),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (nextWin B (winOf l) _).isLt h2)]

lemma nextWin_cycle_unique {k d : ℕ} (hk : 0 < k) (p : Fin (k + 1) → Fin (2 ^ (7 * d + 3)))
    (hp0 : p 0 = p (Fin.last k))
    (hstep : ∀ l : Fin k, p l.succ = nextWin (7 * d + 3) (p l.castSucc) ((p l.succ).val.testBit (7 * d + 3 - 1))) :
    let B := 7 * d + 3
    let x : Fin k → Bool := fun i =>
      (p (enterInv k d hk i).succ).val.testBit (B - 1)
    ∀ l : Fin (k + 1), p l = ⟨bitsToNat (fun m : Fin B => x (winPos k d l.val m.val hk)), bitsToNat_lt _⟩ := by
  intro B x
  have hB : 0 < B := by omega
  let q : ℕ → Fin (2 ^ B) := fun n => p ⟨n % k, Nat.lt_trans (Nat.mod_lt n hk) (Nat.lt_succ_self k)⟩
  let b : ℕ → Bool := fun n => (p (⟨n % k, Nat.mod_lt n hk⟩ : Fin k).succ).val.testBit (B - 1)
  have hq_succ : ∀ n : ℕ, q (n + 1) = nextWin B (q n) (b n) := by
    intro n
    have hlt : n % k < k := Nat.mod_lt n hk
    have hr := hstep ⟨n % k, hlt⟩
    change p (⟨n % k, hlt⟩ : Fin k).succ = nextWin B (q n) (b n) at hr
    rw [← hr]
    by_cases hlast : n % k + 1 < k
    · have hmod1 : (n + 1) % k = n % k + 1 := by
        have hdiv : n + 1 = (n % k + 1) + k * (n / k) := by
          have := Nat.div_add_mod n k; omega
        rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlast]
      simp only [q, Fin.succ]
      congr 1; apply Fin.ext; simp [hmod1]
    · have hmod1 : (n + 1) % k = 0 := by
        have heq : n % k + 1 = k := by omega
        have hdiv := Nat.div_add_mod n k
        rw [show n + 1 = k * (n / k + 1) by rw [Nat.mul_add, Nat.mul_one]; omega, Nat.mul_mod_right]
      have hl : (⟨n % k, hlt⟩ : Fin k).succ = Fin.last k := by
        apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; omega
      rw [hl, ← hp0]
      simp only [q, hmod1]
      rfl
  have hq_shift : ∀ t n : ℕ, t ≤ B - 1 → (q (n + t + 1)).val.testBit (B - 1 - t) = b n := by
    intro t
    induction t with
    | zero =>
      intro n _
      rw [Nat.add_zero, Nat.sub_zero, hq_succ, nextWin_testBit hB (q n) (b n) (by omega)]
      simp
    | succ t ih =>
      intro n htle
      rw [show n + (t + 1) + 1 = (n + t + 1) + 1 by ring, hq_succ,
        nextWin_testBit hB (q (n + t + 1)) (b (n + t + 1)) (by omega)]
      have hlt : B - 1 - (t + 1) < B - 1 := by omega
      simp only [hlt, ↓reduceIte]
      have heq : B - 1 - (t + 1) + 1 = B - 1 - t := by omega
      rw [heq]
      exact ih n (by omega)
  have hq_period : ∀ a c : ℕ, q (a + k * c) = q a := by
    intro a c
    simp only [q, Nat.add_mul_mod_self_left]
  intro l
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro m
  by_cases hm : m < B
  · have hpl : p l = q l.val := by
      by_cases hlk : l.val < k
      · simp only [q, Nat.mod_eq_of_lt hlk]
      · have hle : l = Fin.last k := Fin.ext (show l.val = k by have := l.isLt; omega)
        subst hle
        simp only [q, Fin.val_last, Nat.mod_self, ← hp0]; rfl
    rw [hpl]
    change (q l.val).val.testBit m = (bitsToNat (fun m' : Fin B => x (winPos k d l.val m'.val hk))).testBit m
    rw [bitsToNat_testBit (i := ⟨m, hm⟩)]
    set t := B - 1 - m
    set n := l.val + ((t + 1) / k + 1) * k - (t + 1)
    have ht1 : t + 1 ≤ ((t + 1) / k + 1) * k := by
      have hdiv := Nat.div_add_mod (t + 1) k
      have hmod := Nat.mod_lt (t + 1) hk
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((t + 1) / k) k]; omega
    have hadd : n + t + 1 = l.val + k * ((t + 1) / k + 1) := by
      have : t + 1 ≤ l.val + ((t + 1) / k + 1) * k := Nat.le_trans ht1 (Nat.le_add_left _ _)
      dsimp only [n]
      rw [add_assoc, Nat.sub_add_cancel this, Nat.mul_comm]
    have hq_eq : q (n + t + 1) = q l.val := by rw [hadd, hq_period]
    have hm_eq : m = B - 1 - t := by omega
    rw [← hq_eq]
    have hs := hq_shift t n (by omega)
    rw [← hm_eq] at hs
    rw [hs]
    have hb_eq : b n = x (enterIdx k d hk ⟨n % k, Nat.mod_lt n hk⟩) := by
      dsimp only [b, x]
      rw [enterInv_idx]
    rw [hb_eq]
    congr 1
    apply Fin.ext
    unfold enterIdx winPos
    dsimp only
    have h1 : (n % k + winShift k d + (7 * d + 3)) % k = (n + winShift k d + B) % k := by
      rw [add_assoc (n % k), Nat.add_mod (n % k), Nat.mod_mod, ← Nat.add_mod, ← add_assoc]
    rw [h1]
    have hsum : n + winShift k d + B = l.val + winShift k d + m + k * ((t + 1) / k + 1) := by
      have hnt : n + (t + 1) = l.val + k * ((t + 1) / k + 1) := by rw [← add_assoc, hadd]
      have hmB : m + (t + 1) = B := by omega
      omega
    rw [hsum, Nat.add_mul_mod_self_left]
  · have h2 : 2 ^ B ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (p l).isLt h2),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (bitsToNat_lt _) h2)]

-- Local step evaluator for shifted bit windows
def localXorAdj (B1 stepDist : ℕ) (st : Fin B1 → Bool) (j : ℕ) : Bool :=
  if h : j < B1 then
    let c := st ⟨j, h⟩
    let l := if hl : stepDist ≤ j ∧ j - stepDist < B1 then st ⟨j - stepDist, hl.2⟩ else false
    let r := if hr : j + stepDist < B1 then st ⟨j + stepDist, hr⟩ else false
    Bool.xor c (Bool.xor l r)
  else false

def localStepAt (B1 stepDist : ℕ) (st : Fin B1 → Bool) (m : ℕ) : Bool :=
  let cm := localXorAdj B1 stepDist st m
  let cp1 := localXorAdj B1 stepDist st (m + 1)
  let cp2 := localXorAdj B1 stepDist st (m + 2)
  Bool.xor cm (!cp1 && cp2)

lemma localXorAdj_eq {k d i stepDist B1 : ℕ} (hk : 0 < k)
    (hs : stepDist = 1 ∨ stepDist = 2)
    {stLoc : Fin B1 → Bool} {stGlob : ℕ} (hglob : stGlob < 2 ^ k)
    {lo hi j : ℕ} (hlo : lo + stepDist ≤ j) (hhi : j + stepDist ≤ hi) (hhiB : hi < B1)
    (heq : ∀ m : ℕ, lo ≤ m → m ≤ hi → (hm : m < B1) → stLoc ⟨m, hm⟩ = stGlob.testBit (winPos k d i m hk).val) :
    localXorAdj B1 stepDist stLoc j =
      (stGlob ^^^ rotFn k stepDist stGlob ^^^ rotFn k (k - stepDist) stGlob).testBit (winPos k d i j hk).val := by
  have hjB : j < B1 := by omega
  have hjL : stepDist ≤ j ∧ j - stepDist < B1 := ⟨by omega, by omega⟩
  have hjR : j + stepDist < B1 := by omega
  unfold localXorAdj
  rw [dif_pos hjB, dif_pos hjL, dif_pos hjR]
  rw [Nat.testBit_xor, Nat.testBit_xor,
    rotFn_testBit hk stepDist stGlob _ hglob (winPos k d i j hk).isLt,
    rotFn_testBit hk (k - stepDist) stGlob _ hglob (winPos k d i j hk).isLt]
  have hpC := heq j (by omega) (by omega) hjB
  have hpL := heq (j - stepDist) (by omega) (by omega) hjL.2
  have hpR := heq (j + stepDist) (by omega) (by omega) hjR
  rw [hpC, hpL, hpR]
  unfold winPos
  rw [rotPos_sub hk (i + winShift k d) j stepDist (by omega)]
  rcases hs with rfl | rfl
  · rw [rotPos_k_sub_one hk (i + winShift k d) j, ← Bool.xor_assoc]
  · rw [rotPos_k_sub_two hk (i + winShift k d) j, ← Bool.xor_assoc]

lemma localStepAt_eq {k d i stepDist B1 : ℕ} (hk : 0 < k)
    (hs : stepDist = 1 ∨ stepDist = 2)
    {stLoc : Fin B1 → Bool} {stGlob : ℕ} (hglob : stGlob < 2 ^ k)
    {lo hi m : ℕ} (hlo : lo + stepDist ≤ m) (hhi : m + 2 + stepDist ≤ hi) (hhiB : hi < B1)
    (heq : ∀ j : ℕ, lo ≤ j → j ≤ hi → (hj : j < B1) → stLoc ⟨j, hj⟩ = stGlob.testBit (winPos k d i j hk).val) :
    localStepAt B1 stepDist stLoc m =
      (stepFn k (stGlob ^^^ rotFn k stepDist stGlob ^^^ rotFn k (k - stepDist) stGlob)).testBit
        (winPos k d i m hk).val := by
  unfold localStepAt
  rw [stepFn_testBit k _ _ (winPos k d i m hk).isLt]
  have hx0 := localXorAdj_eq hk hs hglob (j := m) (by omega) (by omega) hhiB heq
  have hx1 := localXorAdj_eq hk hs hglob (j := m + 1) (by omega) (by omega) hhiB heq
  have hx2 := localXorAdj_eq hk hs hglob (j := m + 2) (by omega) (by omega) hhiB heq
  have hp1 : ((winPos k d i m hk).val + 1) % k = (winPos k d i (m + 1) hk).val := by
    unfold winPos; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
  have hp2 : ((winPos k d i m hk).val + 2) % k = (winPos k d i (m + 2) hk).val := by
    unfold winPos; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; ring_nf
  rw [hp1, hp2, hx0, hx1, hx2]

def localFirstState (k d i : ℕ) (hk : 0 < k) (w_ext : Fin (2 ^ (7 * d + 4))) (u : Fin k → Bool) :
    ℕ → Fin (7 * d + 4) → Bool
  | 0, m =>
    if hm : 1 ≤ m.val then
      Bool.xor (w_ext.val.testBit (m.val - 1)) (u (winPos k d i m.val hk))
    else false
  | t + 1, m =>
    let st := localFirstState k d i hk w_ext u t
    let sbit := localStepAt (7 * d + 4) 1 st m.val
    let kbit := if hk1 : 2 * t ≤ m.val then w_ext.val.testBit (m.val - 2 * t) else false
    let cbit := (constFn k (t + 1)).testBit (winPos k d i m.val hk).val
    Bool.xor (Bool.xor sbit kbit) cbit

def localSecondState (k r d i : ℕ) (hk : 0 < k) (w_ext : Fin (2 ^ (7 * d + 4))) (v : Fin k → Bool) :
    ℕ → Fin (7 * d + 4) → Bool
  | 0, m =>
    if hm : 3 ≤ m.val then
      Bool.xor (w_ext.val.testBit (m.val - 3)) (v (winPos k d i m.val hk))
    else false
  | t + 1, m =>
    let st := localSecondState k r d i hk w_ext v t
    let sbit := localStepAt (7 * d + 4) 2 st m.val
    let kbit := if hk1 : 3 * (t + 1) + 1 ≤ m.val then w_ext.val.testBit (m.val - (3 * (t + 1) + 1)) else false
    let cbit := (constFn k (r + t + 1)).testBit (winPos k d i m.val hk).val
    Bool.xor (Bool.xor sbit kbit) cbit

lemma localFirstState_eq {k d i : ℕ} (hk : 0 < k) (x u : Fin k → Bool)
    (w_ext : Fin (2 ^ (7 * d + 4)))
    (hw : ∀ m : ℕ, m ≤ 7 * d + 3 → w_ext.val.testBit m = x (winPos k d i m hk))
    (t : ℕ) (ht : t ≤ d) :
    ∀ m : ℕ, 2 * d + t + 3 ≤ m → m ≤ 6 * d - 3 * t + 3 → (hm : m < 7 * d + 4) →
      localFirstState k d i hk w_ext u t ⟨m, hm⟩ =
        (firstFn k t (bitsToNat x) (bitsToNat u)).testBit (winPos k d i m hk).val := by
  induction t with
  | zero =>
    intro m hlo hhi hm
    unfold localFirstState firstFn
    simp only [List.range_zero, List.foldl_nil, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hlo hhi ⊢
    have hm1 : 1 ≤ m := by omega
    simp only [hm1, ↓reduceDIte]
    rw [Nat.testBit_xor, rotFn_testBit hk 1 (bitsToNat x) _ (bitsToNat_lt x) (winPos k d i m hk).isLt,
      bitsToNat_testBit]
    rw [hw (m - 1) (by omega)]
    have hpos1 : ((winPos k d i m hk).val + (k - 1 % k)) % k = (winPos k d i (m - 1) hk).val := by
      unfold winPos; exact rotPos_sub hk (i + winShift k d) m 1 hm1
    rw [hpos1, bitsToNat_testBit]
  | succ t ih =>
    intro m hlo hhi hm
    unfold localFirstState
    have hm2t : 2 * t ≤ m := by omega
    simp only [hm2t, ↓reduceDIte]
    have hprev := firstFn_lt hk t (bitsToNat_lt x) (bitsToNat_lt u)
    have hs := localStepAt_eq (stepDist := 1) hk (Or.inl rfl) hprev
      (lo := 2 * d + t + 3) (hi := 6 * d - 3 * t + 3) (m := m)
      (by omega) (by omega) (by omega) (fun j hj1 hj2 hjB => ih (by omega) j hj1 hj2 hjB)
    unfold firstFn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_xor, Nat.testBit_xor]
    change Bool.xor (Bool.xor (localStepAt (7 * d + 4) 1 _ m) _) _ = _
    rw [hs]
    rw [rotFn_testBit hk (2 * t) (bitsToNat x) _ (bitsToNat_lt x) (winPos k d i m hk).isLt]
    rw [hw (m - 2 * t) (by omega)]
    have hposk : ((winPos k d i m hk).val + (k - (2 * t) % k)) % k = (winPos k d i (m - 2 * t) hk).val := by
      unfold winPos; exact rotPos_sub hk (i + winShift k d) m (2 * t) hm2t
    rw [hposk, bitsToNat_testBit]
    rfl


lemma localSecondState_eq {k r d i : ℕ} (hk : 0 < k) (x v : Fin k → Bool)
    (w_ext : Fin (2 ^ (7 * d + 4)))
    (hw : ∀ m : ℕ, m ≤ 7 * d + 3 → w_ext.val.testBit m = x (winPos k d i m hk))
    (t : ℕ) (ht : t ≤ d) :
    ∀ m : ℕ, d + 2 * t + 3 ≤ m → m ≤ 7 * d - 4 * t + 3 → (hm : m < 7 * d + 4) →
      localSecondState k r d i hk w_ext v t ⟨m, hm⟩ =
        (secondFn k r t (bitsToNat x) (bitsToNat v)).testBit (winPos k d i m hk).val := by
  induction t with
  | zero =>
    intro m hlo hhi hm
    unfold localSecondState secondFn
    simp only [List.range_zero, List.foldl_nil, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hlo hhi ⊢
    have hm3 : 3 ≤ m := by omega
    simp only [hm3, ↓reduceDIte]
    rw [Nat.testBit_xor, rotFn_testBit hk 3 (bitsToNat x) _ (bitsToNat_lt x) (winPos k d i m hk).isLt,
      bitsToNat_testBit, hw (m - 3) (by omega)]
    have hpos3 : ((winPos k d i m hk).val + (k - 3 % k)) % k = (winPos k d i (m - 3) hk).val := by
      unfold winPos; exact rotPos_sub hk (i + winShift k d) m 3 hm3
    rw [hpos3, bitsToNat_testBit]
  | succ t ih =>
    intro m hlo hhi hm
    unfold localSecondState
    have hm3t : 3 * (t + 1) + 1 ≤ m := by omega
    simp only [hm3t, ↓reduceDIte]
    have hprev := secondFn_lt hk r t (bitsToNat_lt x) (bitsToNat_lt v)
    have hs := localStepAt_eq (stepDist := 2) hk (Or.inr rfl) hprev
      (lo := d + 2 * t + 3) (hi := 7 * d - 4 * t + 3) (m := m)
      (by omega) (by omega) (by omega) (fun j hj1 hj2 hjB => ih (by omega) j hj1 hj2 hjB)
    unfold secondFn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_xor, Nat.testBit_xor]
    change Bool.xor (Bool.xor (localStepAt (7 * d + 4) 2 _ m) _) _ = _
    rw [hs]
    rw [rotFn_testBit hk (3 * (t + 1) + 1) (bitsToNat x) _ (bitsToNat_lt x) (winPos k d i m hk).isLt]
    rw [hw (m - (3 * (t + 1) + 1)) (by omega)]
    have hposk : ((winPos k d i m hk).val + (k - (3 * (t + 1) + 1) % k)) % k =
        (winPos k d i (m - (3 * (t + 1) + 1)) hk).val := by
      unfold winPos; exact rotPos_sub hk (i + winShift k d) m (3 * (t + 1) + 1) hm3t
    rw [hposk, bitsToNat_testBit]
    rfl


-- Part 2: Monotone Dual-Rail Library & Early Window Circuit Builder

abbrev DRWire := ℕ × ℕ

def DRBounds (N : ℕ) (G : List MGate) (d : ℕ) (w : DRWire) : Prop :=
  w.1 < N + G.length ∧ w.2 < N + G.length ∧
  (mdepths N G).getD w.1 0 ≤ d ∧ (mdepths N G).getD w.2 0 ≤ d

def DRSound {P : Type} [Fintype P] (G : List MGate) (a : P → Bool) (w : DRWire) (b : Bool) : Prop :=
  ((mrun G a).getD w.1 false = true → b = false) ∧
  ((mrun G a).getD w.2 false = true → b = true)

def DRExact {P : Type} [Fintype P] (G : List MGate) (a : P → Bool) (w : DRWire) (b : Bool) : Prop :=
  ((mrun G a).getD w.1 false = true ↔ b = false) ∧
  ((mrun G a).getD w.2 false = true ↔ b = true)

lemma drExact_to_sound {P : Type} [Fintype P] {G : List MGate} {a : P → Bool} {w : DRWire} {b : Bool}
    (h : DRExact G a w b) : DRSound G a w b :=
  ⟨h.1.mp, h.2.mp⟩

lemma drBounds_of_extends {N : ℕ} {G1 G2 : List MGate} {d : ℕ} {w : DRWire}
    (hext : Extends G1 G2) (h : DRBounds N G1 d w) : DRBounds N G2 d w := by
  have hlen := extends_len hext
  refine ⟨lt_of_lt_of_le h.1 (by omega), lt_of_lt_of_le h.2.1 (by omega), ?_, ?_⟩
  · rw [mdepths_of_extends hext _ h.1]; exact h.2.2.1
  · rw [mdepths_of_extends hext _ h.2.1]; exact h.2.2.2

lemma drBounds_mono {N : ℕ} {G : List MGate} {d1 d2 : ℕ} {w : DRWire}
    (hd : d1 ≤ d2) (h : DRBounds N G d1 w) : DRBounds N G d2 w :=
  ⟨h.1, h.2.1, le_trans h.2.2.1 hd, le_trans h.2.2.2 hd⟩

lemma drSound_of_extends {P : Type} [Fintype P] {G1 G2 : List MGate} {a : P → Bool} {w : DRWire} {b : Bool}
    (hext : Extends G1 G2) (h1 : w.1 < 2 + Fintype.card P + G1.length) (h2 : w.2 < 2 + Fintype.card P + G1.length)
    (hs : DRSound G1 a w b) : DRSound G2 a w b := by
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · rw [mrun_of_extends hext a _ h1] at hw; exact hs.1 hw
  · rw [mrun_of_extends hext a _ h2] at hw; exact hs.2 hw

lemma drExact_of_extends {P : Type} [Fintype P] {G1 G2 : List MGate} {a : P → Bool} {w : DRWire} {b : Bool}
    (hext : Extends G1 G2) (h1 : w.1 < 2 + Fintype.card P + G1.length) (h2 : w.2 < 2 + Fintype.card P + G1.length)
    (hx : DRExact G1 a w b) : DRExact G2 a w b := by
  refine ⟨?_, ?_⟩
  · rw [mrun_of_extends hext a _ h1]; exact hx.1
  · rw [mrun_of_extends hext a _ h2]; exact hx.2

def drNot (w : DRWire) : DRWire := (w.2, w.1)

def drXorConst (c : Bool) (w : DRWire) : DRWire := if c then (w.2, w.1) else w

lemma drBounds_not {N : ℕ} {G : List MGate} {d : ℕ} {w : DRWire} (h : DRBounds N G d w) :
    DRBounds N G d (drNot w) := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

lemma drBounds_xorConst {N : ℕ} {G : List MGate} {d : ℕ} {w : DRWire} (c : Bool) (h : DRBounds N G d w) :
    DRBounds N G d (drXorConst c w) := by
  cases c
  · exact h
  · exact ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

lemma drSound_not {P : Type} [Fintype P] {G : List MGate} {a : P → Bool} {w : DRWire} {b : Bool}
    (h : DRSound G a w b) : DRSound G a (drNot w) (!b) := by
  cases b <;> refine ⟨fun hw => ?_, fun hw => ?_⟩
  · exact Bool.noConfusion (h.2 hw)
  · rfl
  · rfl
  · exact Bool.noConfusion (h.1 hw)

lemma drExact_not {P : Type} [Fintype P] {G : List MGate} {a : P → Bool} {w : DRWire} {b : Bool}
    (h : DRExact G a w b) : DRExact G a (drNot w) (!b) := by
  cases b
  · exact ⟨by simpa [drNot] using h.2, by simpa [drNot] using h.1⟩
  · exact ⟨by simpa [drNot] using h.2, by simpa [drNot] using h.1⟩

lemma drSound_xorConst {P : Type} [Fintype P] {G : List MGate} {a : P → Bool} {w : DRWire} {c b : Bool}
    (h : DRSound G a w b) : DRSound G a (drXorConst c w) (Bool.xor b c) := by
  cases c
  · dsimp only [drXorConst]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]; exact h
  · dsimp only [drXorConst]; simp only [↓reduceIte, Bool.xor_true]; exact drSound_not h

lemma drExact_xorConst {P : Type} [Fintype P] {G : List MGate} {a : P → Bool} {w : DRWire} {c b : Bool}
    (h : DRExact G a w b) : DRExact G a (drXorConst c w) (Bool.xor b c) := by
  cases c
  · dsimp only [drXorConst]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]; exact h
  · dsimp only [drXorConst]; simp only [↓reduceIte, Bool.xor_true]; exact drExact_not h

lemma drBounds_false {N : ℕ} (hN : 2 ≤ N) (G : List MGate) (d : ℕ) : DRBounds N G d (1, 0) :=
  ⟨by omega, by omega, by rw [mdepths_base G 1 (by omega)]; omega, by rw [mdepths_base G 0 (by omega)]; omega⟩

lemma drExact_false {P : Type} [Fintype P] (G : List MGate) (a : P → Bool) :
    DRExact G a (1, 0) false :=
  ⟨by rw [mrun_const1]; exact ⟨fun _ => rfl, fun _ => rfl⟩, by rw [mrun_const0]⟩

def drAnd (N : ℕ) (G : List MGate) (l r : DRWire) : List MGate × DRWire :=
  let rF := addMGate N G false l.1 r.1
  let rT := addMGate N rF.1 true l.2 r.2
  (rT.1, (rF.2, rT.2))

lemma drAnd_spec {P : Type} [Fintype P] (G0 : List MGate) (dl dr : ℕ) (l r : DRWire)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hbl : DRBounds (2 + Fintype.card P) G0 dl l)
    (hbr : DRBounds (2 + Fintype.card P) G0 dr r) :
    let N := 2 + Fintype.card P
    let res := drAnd N G0 l r
    WellFormed N res.1 ∧ Extends G0 res.1 ∧ res.1.length ≤ G0.length + 2 ∧
    DRBounds N res.1 (max dl dr + 1) res.2 ∧
    (∀ a : P → Bool, ∀ bl br : Bool,
      DRSound G0 a l bl → DRSound G0 a r br → DRSound res.1 a res.2 (bl && br)) ∧
    (∀ a : P → Bool, ∀ bl br : Bool,
      DRExact G0 a l bl → DRExact G0 a r br → DRExact res.1 a res.2 (bl && br)) := by
  intro N res
  dsimp only [res, drAnd]
  set rF := addMGate N G0 false l.1 r.1 with hrF
  have hwfF : WellFormed N rF.1 := addMGate_wf hwf0 false (l := l.1) (r := r.1) hbl.1 hbr.1
  have hextF : Extends G0 rF.1 := addMGate_extends N G0 false l.1 r.1
  have hlenF : rF.1.length = G0.length + 1 := addMGate_len N G0 false l.1 r.1
  have houtF : rF.2 < N + rF.1.length := addMGate_out_lt N G0 false l.1 r.1
  set rT := addMGate N rF.1 true l.2 r.2 with hrT
  have hwfT : WellFormed N rT.1 := addMGate_wf hwfF true (l := l.2) (r := r.2)
    (by have := hbl.2.1; omega) (by have := hbr.2.1; omega)
  have hextT : Extends rF.1 rT.1 := addMGate_extends N rF.1 true l.2 r.2
  have hlenT : rT.1.length = rF.1.length + 1 := addMGate_len N rF.1 true l.2 r.2
  have houtT : rT.2 < N + rT.1.length := addMGate_out_lt N rF.1 true l.2 r.2
  have hext := extends_trans hextF hextT
  change WellFormed N rT.1 ∧ Extends G0 rT.1 ∧ rT.1.length ≤ G0.length + 2 ∧
    DRBounds N rT.1 (max dl dr + 1) (rF.2, rT.2) ∧
    (∀ a : P → Bool, ∀ bl br : Bool,
      DRSound G0 a l bl → DRSound G0 a r br → DRSound rT.1 a (rF.2, rT.2) (bl && br)) ∧
    (∀ a : P → Bool, ∀ bl br : Bool,
      DRExact G0 a l bl → DRExact G0 a r br → DRExact rT.1 a (rF.2, rT.2) (bl && br))
  refine ⟨hwfT, hext, by omega, ⟨by have := extends_len hextT; omega, houtT, ?_, ?_⟩, ?_, ?_⟩
  · rw [mdepths_of_extends hextT _ houtF, hrF, addMGate_depth]
    dsimp only [N]; have := hbl.2.2.1; have := hbr.2.2.1; omega
  · rw [hrT, addMGate_depth, mdepths_of_extends hextF _ hbl.2.1, mdepths_of_extends hextF _ hbr.2.1]
    have := hbl.2.2.2; have := hbr.2.2.2; omega
  · intro a bl br hsl hsr
    constructor
    · intro hw
      rw [mrun_of_extends hextT a _ houtF, hrF, addMGate_val] at hw
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at hw
      rcases hw with hw1 | hw2
      · rw [hsl.1 hw1]; simp
      · rw [hsr.1 hw2]; simp
    · intro hw
      rw [hrT, addMGate_val, mrun_of_extends hextF a _ hbl.2.1, mrun_of_extends hextF a _ hbr.2.1] at hw
      simp only [↓reduceIte, Bool.and_eq_true] at hw
      rw [hsl.2 hw.1, hsr.2 hw.2]; rfl
  · intro a bl br hxl hxr
    constructor
    · rw [mrun_of_extends hextT a _ houtF, hrF, addMGate_val]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, hxl.1, hxr.1]
      cases bl <;> cases br <;> simp
    · rw [hrT, addMGate_val, mrun_of_extends hextF a _ hbl.2.1, mrun_of_extends hextF a _ hbr.2.1]
      simp only [↓reduceIte, Bool.and_eq_true, hxl.2, hxr.2]

def drXor (N : ℕ) (G : List MGate) (l r : DRWire) : List MGate × DRWire :=
  let aTF := addMGate N G true l.2 r.1
  let aFT := addMGate N aTF.1 true l.1 r.2
  let rT := addMGate N aFT.1 false aTF.2 aFT.2
  let aTT := addMGate N rT.1 true l.2 r.2
  let aFF := addMGate N aTT.1 true l.1 r.1
  let rF := addMGate N aFF.1 false aTT.2 aFF.2
  (rF.1, (rF.2, rT.2))

lemma drXor_spec {P : Type} [Fintype P] (G0 : List MGate) (dl dr : ℕ) (l r : DRWire)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hbl : DRBounds (2 + Fintype.card P) G0 dl l)
    (hbr : DRBounds (2 + Fintype.card P) G0 dr r) :
    let N := 2 + Fintype.card P
    let res := drXor N G0 l r
    WellFormed N res.1 ∧ Extends G0 res.1 ∧ res.1.length ≤ G0.length + 6 ∧
    DRBounds N res.1 (max dl dr + 2) res.2 ∧
    (∀ a : P → Bool, ∀ bl br : Bool,
      DRSound G0 a l bl → DRSound G0 a r br → DRSound res.1 a res.2 (Bool.xor bl br)) ∧
    (∀ a : P → Bool, ∀ bl br : Bool,
      DRExact G0 a l bl → DRExact G0 a r br → DRExact res.1 a res.2 (Bool.xor bl br)) := by
  intro N res
  set g1 := addMGate N G0 true l.2 r.1 with hg1
  have hwf1 : WellFormed N g1.1 := addMGate_wf hwf0 true (l := l.2) (r := r.1) hbl.2.1 hbr.1
  have he1 : Extends G0 g1.1 := addMGate_extends N G0 true l.2 r.1
  have hl1 : g1.1.length = G0.length + 1 := addMGate_len N G0 true l.2 r.1
  have ho1 : g1.2 < N + g1.1.length := addMGate_out_lt N G0 true l.2 r.1
  set g2 := addMGate N g1.1 true l.1 r.2 with hg2
  have hwf2 : WellFormed N g2.1 := addMGate_wf hwf1 true (l := l.1) (r := r.2)
    (by have := hbl.1; omega) (by have := hbr.2.1; omega)
  have he2 : Extends g1.1 g2.1 := addMGate_extends N g1.1 true l.1 r.2
  have hl2 : g2.1.length = g1.1.length + 1 := addMGate_len N g1.1 true l.1 r.2
  have ho2 : g2.2 < N + g2.1.length := addMGate_out_lt N g1.1 true l.1 r.2
  set g3 := addMGate N g2.1 false g1.2 g2.2 with hg3
  have hwf3 : WellFormed N g3.1 := addMGate_wf hwf2 false (l := g1.2) (r := g2.2) (by omega) ho2
  have he3 : Extends g2.1 g3.1 := addMGate_extends N g2.1 false g1.2 g2.2
  have hl3 : g3.1.length = g2.1.length + 1 := addMGate_len N g2.1 false g1.2 g2.2
  have ho3 : g3.2 < N + g3.1.length := addMGate_out_lt N g2.1 false g1.2 g2.2
  have he03 := extends_trans he1 (extends_trans he2 he3)
  set g4 := addMGate N g3.1 true l.2 r.2 with hg4
  have hwf4 : WellFormed N g4.1 := addMGate_wf hwf3 true (l := l.2) (r := r.2)
    (by have := hbl.2.1; have := extends_len he03; omega)
    (by have := hbr.2.1; have := extends_len he03; omega)
  have he4 : Extends g3.1 g4.1 := addMGate_extends N g3.1 true l.2 r.2
  have hl4 : g4.1.length = g3.1.length + 1 := addMGate_len N g3.1 true l.2 r.2
  have ho4 : g4.2 < N + g4.1.length := addMGate_out_lt N g3.1 true l.2 r.2
  set g5 := addMGate N g4.1 true l.1 r.1 with hg5
  have he04 := extends_trans he03 he4
  have hwf5 : WellFormed N g5.1 := addMGate_wf hwf4 true (l := l.1) (r := r.1)
    (by have := hbl.1; have := extends_len he04; omega)
    (by have := hbr.1; have := extends_len he04; omega)
  have he5 : Extends g4.1 g5.1 := addMGate_extends N g4.1 true l.1 r.1
  have hl5 : g5.1.length = g4.1.length + 1 := addMGate_len N g4.1 true l.1 r.1
  have ho5 : g5.2 < N + g5.1.length := addMGate_out_lt N g4.1 true l.1 r.1
  set g6 := addMGate N g5.1 false g4.2 g5.2 with hg6
  have hwf6 : WellFormed N g6.1 := addMGate_wf hwf5 false (l := g4.2) (r := g5.2) (by omega) ho5
  have he6 : Extends g5.1 g6.1 := addMGate_extends N g5.1 false g4.2 g5.2
  have hl6 : g6.1.length = g5.1.length + 1 := addMGate_len N g5.1 false g4.2 g5.2
  have ho6 : g6.2 < N + g6.1.length := addMGate_out_lt N g5.1 false g4.2 g5.2
  have he36 := extends_trans he4 (extends_trans he5 he6)
  have he06 := extends_trans he03 he36
  have he12 := extends_trans he2 he3
  have hd1 : (mdepths N g1.1).getD g1.2 0 ≤ max dl dr + 1 := by
    rw [hg1, addMGate_depth]; dsimp only [N]; have := hbl.2.2.2; have := hbr.2.2.1; omega
  have hd2 : (mdepths N g2.1).getD g2.2 0 ≤ max dl dr + 1 := by
    rw [hg2, addMGate_depth, mdepths_of_extends he1 _ hbl.1, mdepths_of_extends he1 _ hbr.2.1]
    have := hbl.2.2.1; have := hbr.2.2.2; omega
  have hd3 : (mdepths N g3.1).getD g3.2 0 ≤ max dl dr + 2 := by
    rw [hg3, addMGate_depth, mdepths_of_extends he2 _ ho1]; dsimp only [N] at hd1 hd2 ⊢; omega
  have hd4 : (mdepths N g4.1).getD g4.2 0 ≤ max dl dr + 1 := by
    rw [hg4, addMGate_depth, mdepths_of_extends he03 _ hbl.2.1, mdepths_of_extends he03 _ hbr.2.1]
    have := hbl.2.2.2; have := hbr.2.2.2; omega
  have hd5 : (mdepths N g5.1).getD g5.2 0 ≤ max dl dr + 1 := by
    rw [hg5, addMGate_depth, mdepths_of_extends he04 _ hbl.1, mdepths_of_extends he04 _ hbr.1]
    have := hbl.2.2.1; have := hbr.2.2.1; omega
  have hd6 : (mdepths N g6.1).getD g6.2 0 ≤ max dl dr + 2 := by
    rw [hg6, addMGate_depth, mdepths_of_extends he5 _ ho4]; dsimp only [N] at hd4 hd5 ⊢; omega
  have hvF_fn : ∀ a : P → Bool, (mrun g6.1 a).getD g6.2 false = true ↔
      ((mrun G0 a).getD l.2 false = true ∧ (mrun G0 a).getD r.2 false = true) ∨
      ((mrun G0 a).getD l.1 false = true ∧ (mrun G0 a).getD r.1 false = true) := fun a => by
    rw [hg6, addMGate_val]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
    rw [mrun_of_extends he5 a _ ho4, hg4, hg5, addMGate_val, addMGate_val]
    simp only [↓reduceIte, Bool.and_eq_true]
    rw [mrun_of_extends he03 a _ hbl.2.1, mrun_of_extends he03 a _ hbr.2.1,
      mrun_of_extends he04 a _ hbl.1, mrun_of_extends he04 a _ hbr.1]
  have hvT_fn : ∀ a : P → Bool, (mrun g6.1 a).getD g3.2 false = true ↔
      ((mrun G0 a).getD l.2 false = true ∧ (mrun G0 a).getD r.1 false = true) ∨
      ((mrun G0 a).getD l.1 false = true ∧ (mrun G0 a).getD r.2 false = true) := fun a => by
    rw [mrun_of_extends he36 a _ ho3, hg3, addMGate_val]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
    rw [mrun_of_extends he2 a _ ho1, hg1, hg2, addMGate_val, addMGate_val]
    simp only [↓reduceIte, Bool.and_eq_true]
    rw [mrun_of_extends he1 a _ hbl.1, mrun_of_extends he1 a _ hbr.2.1]
  dsimp only [res, drXor]
  change WellFormed N g6.1 ∧ Extends G0 g6.1 ∧ g6.1.length ≤ G0.length + 6 ∧
    DRBounds N g6.1 (max dl dr + 2) (g6.2, g3.2) ∧ _ ∧ _
  refine ⟨hwf6, he06, by omega, ⟨ho6, by have := extends_len he36; omega, hd6, ?_⟩, ?_, ?_⟩
  · rw [mdepths_of_extends he36 _ ho3]; exact hd3
  · intro a bl br hsl hsr
    constructor
    · intro hw; rw [hvF_fn] at hw
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hsl.2 h1, hsr.2 h2]; rfl
      · rw [hsl.1 h1, hsr.1 h2]; rfl
    · intro hw; rw [hvT_fn] at hw
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hsl.2 h1, hsr.1 h2]; rfl
      · rw [hsl.1 h1, hsr.2 h2]; rfl
  · intro a bl br hxl hxr
    constructor
    · rw [hvF_fn, hxl.1, hxl.2, hxr.1, hxr.2]; cases bl <;> cases br <;> simp
    · rw [hvT_fn, hxl.1, hxl.2, hxr.1, hxr.2]; cases bl <;> cases br <;> simp

def drLocalAdj (N B1 stepDist : ℕ) (G : List MGate) (st : Fin B1 → DRWire) (j : ℕ) : List MGate × DRWire :=
  if hj : j < B1 then
    let rc := st ⟨j, hj⟩
    let rl := if hl : stepDist ≤ j ∧ j - stepDist < B1 then st ⟨j - stepDist, hl.2⟩ else (1, 0)
    let rr := if hr : j + stepDist < B1 then st ⟨j + stepDist, hr⟩ else (1, 0)
    let x1 := drXor N G rl rr
    drXor N x1.1 rc x1.2
  else (G, (1, 0))

def drLocalStep (N B1 stepDist : ℕ) (G : List MGate) (st : Fin B1 → DRWire) (m : Fin B1) : List MGate × DRWire :=
  let a0 := drLocalAdj N B1 stepDist G st m.val
  let a1 := drLocalAdj N B1 stepDist a0.1 st (m.val + 1)
  let a2 := drLocalAdj N B1 stepDist a1.1 st (m.val + 2)
  let nd := drAnd N a2.1 (drNot a1.2) a2.2
  drXor N nd.1 a0.2 nd.2

lemma drLocalAdj_spec {P : Type} [Fintype P] (B1 stepDist : ℕ) (G0 : List MGate) (dpD : ℕ)
    (st : Fin B1 → DRWire)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hst_bd : ∀ i, DRBounds (2 + Fintype.card P) G0 dpD (st i))
    (j : ℕ) :
    let N := 2 + Fintype.card P
    let r := drLocalAdj N B1 stepDist G0 st j
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + 12 ∧
    DRBounds N r.1 (dpD + 4) r.2 ∧
    ∀ (a : P → Bool) (stB : Fin B1 → Bool),
      (∀ i, DRExact G0 a (st i) (stB i)) →
      DRExact r.1 a r.2 (localXorAdj B1 stepDist stB j) := by
  intro N res
  by_cases hj : j < B1
  · set rc := st ⟨j, hj⟩
    set rl := if hl : stepDist ≤ j ∧ j - stepDist < B1 then st ⟨j - stepDist, hl.2⟩ else (1, 0)
    set rr := if hr : j + stepDist < B1 then st ⟨j + stepDist, hr⟩ else (1, 0)
    have hbc : DRBounds N G0 dpD rc := hst_bd ⟨j, hj⟩
    have hbl : DRBounds N G0 dpD rl := by
      dsimp [rl]; split_ifs
      · exact hst_bd _
      · exact drBounds_false (by omega) G0 dpD
    have hbr : DRBounds N G0 dpD rr := by
      dsimp [rr]; split_ifs
      · exact hst_bd _
      · exact drBounds_false (by omega) G0 dpD
    set x1 := drXor N G0 rl rr
    have hx1_spec := drXor_spec G0 dpD dpD rl rr hwf0 hbl hbr
    dsimp only at hx1_spec
    rcases hx1_spec with ⟨hwf1, he1, hlen1, hbd1, _, hex1⟩
    change WellFormed N x1.1 at hwf1
    change Extends G0 x1.1 at he1
    change x1.1.length ≤ G0.length + 6 at hlen1
    change DRBounds N x1.1 (max dpD dpD + 2) x1.2 at hbd1
    change ∀ (a : P → Bool) (bl br : Bool),
      DRExact G0 a rl bl → DRExact G0 a rr br → DRExact x1.1 a x1.2 (Bool.xor bl br) at hex1
    have hbc1 : DRBounds N x1.1 dpD rc := drBounds_of_extends he1 hbc
    set x2 := drXor N x1.1 rc x1.2
    have hx2_spec := drXor_spec x1.1 dpD (dpD + 2) rc x1.2 hwf1 hbc1
      (drBounds_mono (by omega) hbd1)
    dsimp only at hx2_spec
    rcases hx2_spec with ⟨hwf2, he2, hlen2, hbd2, _, hex2⟩
    change WellFormed N x2.1 at hwf2
    change Extends x1.1 x2.1 at he2
    change x2.1.length ≤ x1.1.length + 6 at hlen2
    change DRBounds N x2.1 (max dpD (dpD + 2) + 2) x2.2 at hbd2
    change ∀ (a : P → Bool) (bl br : Bool),
      DRExact x1.1 a rc bl → DRExact x1.1 a x1.2 br → DRExact x2.1 a x2.2 (Bool.xor bl br) at hex2
    have hlen_fin : x2.1.length ≤ G0.length + 12 := by omega
    dsimp only [res, drLocalAdj]; rw [dif_pos hj]
    change WellFormed N x2.1 ∧ Extends G0 x2.1 ∧ x2.1.length ≤ G0.length + 12 ∧
      DRBounds N x2.1 (dpD + 4) x2.2 ∧ ∀ (a : P → Bool) (stB : Fin B1 → Bool),
        (∀ i, DRExact G0 a (st i) (stB i)) → DRExact x2.1 a x2.2 (localXorAdj B1 stepDist stB j)
    refine ⟨hwf2, extends_trans he1 he2, hlen_fin, drBounds_mono (by omega) hbd2, ?_⟩
    · intro a stB hstx
      unfold localXorAdj
      simp only [hj, ↓reduceDIte]
      have hrl : DRExact G0 a rl (if hl : stepDist ≤ j ∧ j - stepDist < B1 then stB ⟨j - stepDist, hl.2⟩ else false) := by
        dsimp [rl]; split_ifs
        · exact hstx _
        · exact drExact_false G0 a
      have hrr : DRExact G0 a rr (if hr : j + stepDist < B1 then stB ⟨j + stepDist, hr⟩ else false) := by
        dsimp [rr]; split_ifs
        · exact hstx _
        · exact drExact_false G0 a
      have hx1a := hex1 a _ _ hrl hrr
      have hca := drExact_of_extends he1 hbc.1 hbc.2.1 (hstx ⟨j, hj⟩)
      exact hex2 a _ _ hca hx1a
  · dsimp only [res, drLocalAdj, localXorAdj]
    simp only [hj, ↓reduceDIte]
    exact ⟨hwf0, extends_rfl G0, by omega, drBounds_false (by omega) G0 (dpD + 4),
      fun a _ _ => drExact_false G0 a⟩

lemma drLocalStep_spec {P : Type} [Fintype P] (B1 stepDist : ℕ) (G0 : List MGate) (dpD : ℕ)
    (st : Fin B1 → DRWire)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hst_bd : ∀ i, DRBounds (2 + Fintype.card P) G0 dpD (st i))
    (m : Fin B1) :
    let N := 2 + Fintype.card P
    let r := drLocalStep N B1 stepDist G0 st m
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + 44 ∧
    DRBounds N r.1 (dpD + 7) r.2 ∧
    ∀ (a : P → Bool) (stB : Fin B1 → Bool),
      (∀ i, DRExact G0 a (st i) (stB i)) →
      DRExact r.1 a r.2 (localStepAt B1 stepDist stB m.val) := by
  intro N r
  have ha0 := drLocalAdj_spec B1 stepDist G0 dpD st hwf0 hst_bd m.val
  set a0 := drLocalAdj N B1 stepDist G0 st m.val
  dsimp only at ha0
  rcases ha0 with ⟨hwf0', he0, hlen0, hbd0, hex0⟩
  change WellFormed N a0.1 at hwf0'
  change Extends G0 a0.1 at he0
  change a0.1.length ≤ G0.length + 12 at hlen0
  change DRBounds N a0.1 (dpD + 4) a0.2 at hbd0
  change ∀ (a : P → Bool) (stB : Fin B1 → Bool),
    (∀ i, DRExact G0 a (st i) (stB i)) → DRExact a0.1 a a0.2 (localXorAdj B1 stepDist stB m.val) at hex0
  have hst1 : ∀ i, DRBounds N a0.1 dpD (st i) := fun i => drBounds_of_extends he0 (hst_bd i)
  have ha1 := drLocalAdj_spec B1 stepDist a0.1 dpD st hwf0' hst1 (m.val + 1)
  set a1 := drLocalAdj N B1 stepDist a0.1 st (m.val + 1)
  dsimp only at ha1
  rcases ha1 with ⟨hwf1, he1, hlen1, hbd1, hex1⟩
  change WellFormed N a1.1 at hwf1
  change Extends a0.1 a1.1 at he1
  change a1.1.length ≤ a0.1.length + 12 at hlen1
  change DRBounds N a1.1 (dpD + 4) a1.2 at hbd1
  change ∀ (a : P → Bool) (stB : Fin B1 → Bool),
    (∀ i, DRExact a0.1 a (st i) (stB i)) → DRExact a1.1 a a1.2 (localXorAdj B1 stepDist stB (m.val + 1)) at hex1
  have he01 := extends_trans he0 he1
  have hst2 : ∀ i, DRBounds N a1.1 dpD (st i) := fun i => drBounds_of_extends he01 (hst_bd i)
  have ha2 := drLocalAdj_spec B1 stepDist a1.1 dpD st hwf1 hst2 (m.val + 2)
  set a2 := drLocalAdj N B1 stepDist a1.1 st (m.val + 2)
  dsimp only at ha2
  rcases ha2 with ⟨hwf2, he2, hlen2, hbd2, hex2⟩
  change WellFormed N a2.1 at hwf2
  change Extends a1.1 a2.1 at he2
  change a2.1.length ≤ a1.1.length + 12 at hlen2
  change DRBounds N a2.1 (dpD + 4) a2.2 at hbd2
  change ∀ (a : P → Bool) (stB : Fin B1 → Bool),
    (∀ i, DRExact a1.1 a (st i) (stB i)) → DRExact a2.1 a a2.2 (localXorAdj B1 stepDist stB (m.val + 2)) at hex2
  have he12 := extends_trans he1 he2
  have hnd := drAnd_spec a2.1 (dpD + 4) (dpD + 4) (drNot a1.2) a2.2 hwf2
    (drBounds_not (drBounds_of_extends he2 hbd1)) hbd2
  set nd := drAnd N a2.1 (drNot a1.2) a2.2
  dsimp only at hnd
  rcases hnd with ⟨hwf3, he3, hlen3, hbd3, _, hex3⟩
  change WellFormed N nd.1 at hwf3
  change Extends a2.1 nd.1 at he3
  change nd.1.length ≤ a2.1.length + 2 at hlen3
  change DRBounds N nd.1 (max (dpD + 4) (dpD + 4) + 1) nd.2 at hbd3
  change ∀ (a : P → Bool) (bl br : Bool),
    DRExact a2.1 a (drNot a1.2) bl → DRExact a2.1 a a2.2 br → DRExact nd.1 a nd.2 (bl && br) at hex3
  have he03 := extends_trans he12 he3
  have ha0_bd : DRBounds N nd.1 (dpD + 4) a0.2 := drBounds_of_extends he03 hbd0
  have hx := drXor_spec nd.1 (dpD + 4) (dpD + 5) a0.2 nd.2 hwf3 ha0_bd (drBounds_mono (by omega) hbd3)
  set rx := drXor N nd.1 a0.2 nd.2
  dsimp only at hx
  rcases hx with ⟨hwf4, he4, hlen4, hbd4, _, hex4⟩
  change WellFormed N rx.1 at hwf4
  change Extends nd.1 rx.1 at he4
  change rx.1.length ≤ nd.1.length + 6 at hlen4
  change DRBounds N rx.1 (max (dpD + 4) (dpD + 5) + 2) rx.2 at hbd4
  change ∀ (a : P → Bool) (bl br : Bool),
    DRExact nd.1 a a0.2 bl → DRExact nd.1 a nd.2 br → DRExact rx.1 a rx.2 (Bool.xor bl br) at hex4
  have hlen_fin : rx.1.length ≤ G0.length + 44 := by omega
  dsimp only [r, drLocalStep]
  change WellFormed N rx.1 ∧ Extends G0 rx.1 ∧ rx.1.length ≤ G0.length + 44 ∧ DRBounds N rx.1 (dpD + 7) rx.2 ∧
    ∀ (a : P → Bool) (stB : Fin B1 → Bool), (∀ i, DRExact G0 a (st i) (stB i)) →
      DRExact rx.1 a rx.2 (localStepAt B1 stepDist stB m.val)
  refine ⟨hwf4, extends_trans he0 (extends_trans he03 he4), hlen_fin, drBounds_mono (by omega) hbd4, ?_⟩
  intro a stB hstx
  have h0x := hex0 a stB hstx
  have h1x := hex1 a stB (fun i => drExact_of_extends he0 (hst_bd i).1 (hst_bd i).2.1 (hstx i))
  have h2x := hex2 a stB (fun i => drExact_of_extends he01 (hst_bd i).1 (hst_bd i).2.1 (hstx i))
  have h3x := hex3 a _ _ (drExact_not (drExact_of_extends he2 hbd1.1 hbd1.2.1 h1x)) h2x
  have h0x' := drExact_of_extends he03 hbd0.1 hbd0.2.1 h0x
  exact hex4 a _ _ h0x' h3x

noncomputable def drLocalRounds (N B1 stepDist : ℕ)
    (roundMod : ℕ → Fin B1 → Bool) :
    ℕ → List MGate → (Fin B1 → DRWire) → List MGate × (Fin B1 → DRWire)
  | 0, G, st => (G, st)
  | t + 1, G, st =>
    let prev := drLocalRounds N B1 stepDist roundMod t G st
    let rLayer := fintypeBuild (ι := Fin B1) (fun G' m =>
      let res := drLocalStep N B1 stepDist G' prev.2 m
      (res.1, drXorConst (roundMod t m) res.2)) prev.1
    rLayer

lemma drLocalRounds_spec {P : Type} [Fintype P] (B1 stepDist : ℕ)
    (roundMod : ℕ → Fin B1 → Bool) (t : ℕ) (G0 : List MGate) (dpD : ℕ)
    (st0 : Fin B1 → DRWire)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hst0_bd : ∀ i, DRBounds (2 + Fintype.card P) G0 dpD (st0 i)) :
    let N := 2 + Fintype.card P
    let r := drLocalRounds N B1 stepDist roundMod t G0 st0
    WellFormed N r.1 ∧ Extends G0 r.1 ∧ r.1.length ≤ G0.length + 44 * B1 * t ∧
    (∀ i, DRBounds N r.1 (dpD + 7 * t) (r.2 i)) ∧
    ∀ (a : P → Bool) (stB : ℕ → Fin B1 → Bool),
      (∀ i, DRExact G0 a (st0 i) (stB 0 i)) →
      (∀ s m, stB (s + 1) m = Bool.xor (localStepAt B1 stepDist (stB s) m.val) (roundMod s m)) →
      ∀ i, DRExact r.1 a (r.2 i) (stB t i) := by
  intro N r
  dsimp only [r]
  induction t with
  | zero =>
    refine ⟨hwf0, extends_rfl G0, by simp [drLocalRounds], by simpa [drLocalRounds] using hst0_bd, fun a stB h0 _ i => h0 i⟩
  | succ t ih =>
    rcases ih with ⟨hwfp, hextp, hlenp, hbdp, hevp⟩
    set prev := drLocalRounds (2 + Fintype.card P) B1 stepDist roundMod t G0 st0 with hprev
    let LInv : List MGate → Fin B1 → DRWire → Prop := fun G m w =>
      DRBounds (2 + Fintype.card P) G (dpD + 7 * (t + 1)) w ∧
      ∀ (a : P → Bool) (stB : ℕ → Fin B1 → Bool),
        (∀ i, DRExact G0 a (st0 i) (stB 0 i)) →
        (∀ s m', stB (s + 1) m' = Bool.xor (localStepAt B1 stepDist (stB s) m'.val) (roundMod s m')) →
        DRExact G a w (stB (t + 1) m)
    have hmono : ∀ {G1 G2 : List MGate} {m w}, Extends G1 G2 → LInv G1 m w → LInv G2 m w := by
      intro G1 G2 m w he ⟨hb, hx⟩
      exact ⟨drBounds_of_extends he hb, fun a stB h0 hs =>
        drExact_of_extends he hb.1 hb.2.1 (hx a stB h0 hs)⟩
    have hB := fintypeBuild_spec (ι := Fin B1) (2 + Fintype.card P) 44
      (fun G' m =>
        let res := drLocalStep (2 + Fintype.card P) B1 stepDist G' prev.2 m
        (res.1, drXorConst (roundMod t m) res.2))
      LInv hmono prev.1 hwfp (fun G m hwf hext => by
        have hstG : ∀ i, DRBounds (2 + Fintype.card P) G (dpD + 7 * t) (prev.2 i) :=
          fun i => drBounds_of_extends hext (hbdp i)
        have hs := drLocalStep_spec B1 stepDist G (dpD + 7 * t) prev.2 hwf hstG m
        rcases hs with ⟨hwfS, hextS, hlenS, hbdS, hexS⟩
        refine ⟨hwfS, hextS, hlenS, drBounds_mono (by omega) (drBounds_xorConst _ hbdS), ?_⟩
        intro a stB h0 hrec
        rw [hrec t m]
        have hx := hexS a (stB t) (fun i =>
          drExact_of_extends hext (hbdp i).1 (hbdp i).2.1 (hevp a stB h0 hrec i))
        exact drExact_xorConst hx)
    rcases hB with ⟨hwfB, hextB, hlenB, hinvB⟩
    rw [Fintype.card_fin] at hlenB
    change WellFormed N _ ∧ Extends G0 _ ∧ (fintypeBuild _ prev.1).1.length ≤ G0.length + 44 * B1 * (t + 1) ∧ _
    refine ⟨hwfB, extends_trans hextp hextB, ?_, fun i => (hinvB i).1, fun a stB h0 hr i => (hinvB i).2 a stB h0 hr⟩
    have hmul : 44 * B1 * (t + 1) = 44 * B1 * t + B1 * 44 := by ring
    rw [hmul, ← add_assoc]
    exact le_trans hlenB (Nat.add_le_add_right hlenp (B1 * 44))

noncomputable def addEarlyCell (k r d : ℕ) (hk : 0 < k) (G : List MGate)
    (lw : Fin k × Fin (2 ^ (7 * d + 4))) : List MGate × ℕ :=
  let l := lw.1
  let w_ext := lw.2
  let N := 2 + Fintype.card (Pin315 k)
  let B1 := 7 * d + 4
  let uRail : Fin k → DRWire := fun j => (pinWire k ((0, j), false), pinWire k ((0, j), true))
  let vRail : Fin k → DRWire := fun j => (pinWire k ((1, j), false), pinWire k ((1, j), true))
  let initF : Fin B1 → DRWire := fun m =>
    if 1 ≤ m.val then drXorConst (w_ext.val.testBit (m.val - 1)) (uRail (winPos k d l.val m.val hk))
    else (1, 0)
  let modF : ℕ → Fin B1 → Bool := fun t m =>
    let kbit := if 2 * t ≤ m.val then w_ext.val.testBit (m.val - 2 * t) else false
    let cbit := (constFn k (t + 1)).testBit (winPos k d l.val m.val hk).val
    Bool.xor kbit cbit
  let rF := drLocalRounds N B1 1 modF d G initF
  let initS : Fin B1 → DRWire := fun m =>
    if 3 ≤ m.val then drXorConst (w_ext.val.testBit (m.val - 3)) (vRail (winPos k d l.val m.val hk))
    else (1, 0)
  let modS : ℕ → Fin B1 → Bool := fun t m =>
    let kbit := if 3 * (t + 1) + 1 ≤ m.val then w_ext.val.testBit (m.val - (3 * (t + 1) + 1)) else false
    let cbit := (constFn k (r + t + 1)).testBit (winPos k d l.val m.val hk).val
    Bool.xor kbit cbit
  let rS := drLocalRounds N B1 2 modS d rF.1 initS
  let f3 := rF.2 ⟨3 * d + 3, by omega⟩
  let s4 := rS.2 ⟨3 * d + 3, by omega⟩
  let fail2 := pinWire k ((2, l), !(w_ext.val.testBit (3 * d + 3)))
  let f3T := addMGate N rS.1 true (pinWire k ((3, l), true)) f3.1
  let f3F := addMGate N f3T.1 true (pinWire k ((3, l), false)) f3.2
  let fail3 := addMGate N f3F.1 false f3T.2 f3F.2
  let s4T := addMGate N fail3.1 true (pinWire k ((4, l), true)) s4.1
  let s4F := addMGate N s4T.1 true (pinWire k ((4, l), false)) s4.2
  let fail4 := addMGate N s4F.1 false s4T.2 s4F.2
  let f23 := addMGate N fail4.1 false fail2 fail3.2
  addMGate N f23.1 false f23.2 fail4.2

def earlyPassCond (k r d : ℕ) (hk : 0 < k) (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool)
    (l : Fin k) (w_ext : Fin (2 ^ (7 * d + 4))) : Prop :=
  (∀ b : Bool, ρ (2, l) = some b → w_ext.val.testBit (3 * d + 3) = b) ∧
  (∀ b : Bool, ρ (3, l) = some b → localFirstState k d l.val hk w_ext u d ⟨3 * d + 3, by omega⟩ = b) ∧
  (∀ b : Bool, ρ (4, l) = some b → localSecondState k r d l.val hk w_ext v d ⟨3 * d + 3, by omega⟩ = b)

lemma addEarlyCell_spec (k r d : ℕ) (hk : 0 < k) (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (lw : Fin k × Fin (2 ^ (7 * d + 4))) :
    let N := 2 + Fintype.card (Pin315 k)
    let res := addEarlyCell k r d hk G0 lw
    WellFormed N res.1 ∧ Extends G0 res.1 ∧
    res.1.length ≤ G0.length + (88 * d * (7 * d + 4) + 8) ∧
    res.2 < N + res.1.length ∧
    (mdepths N res.1).getD res.2 0 ≤ 7 * d + 4 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool),
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun res.1 (mkBits ρ)).getD res.2 false = true ↔ ¬ earlyPassCond k r d hk u v ρ lw.1 lw.2) := by
  intro N res
  let B1 := 7 * d + 4
  let l := lw.1
  let w_ext := lw.2
  let uRail : Fin k → DRWire := fun j => (pinWire k ((0, j), false), pinWire k ((0, j), true))
  let vRail : Fin k → DRWire := fun j => (pinWire k ((1, j), false), pinWire k ((1, j), true))
  have hrail_bd : ∀ tr j G', DRBounds N G' 0 (pinWire k ((tr, j), false), pinWire k ((tr, j), true)) :=
    fun tr j G' => ⟨pinWire_lt k G' _, pinWire_lt k G' _,
      by rw [pinWire_depth], by rw [pinWire_depth]⟩
  have hrail_exact : ∀ (tr : Fin 7) (fn : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool),
      (∀ i, ρ (tr, i) = some (fn i)) → ∀ G' j,
        DRExact G' (mkBits ρ) (pinWire k ((tr, j), false), pinWire k ((tr, j), true)) (fn j) := by
    intro tr fn ρ htr G' j
    constructor <;> dsimp only <;> rw [pinWire_val] <;> simp [mkBits, htr j]
  let initF : Fin B1 → DRWire := fun m =>
    if 1 ≤ m.val then drXorConst (w_ext.val.testBit (m.val - 1)) (uRail (winPos k d l.val m.val hk))
    else (1, 0)
  let modF : ℕ → Fin B1 → Bool := fun t m =>
    Bool.xor (if 2 * t ≤ m.val then w_ext.val.testBit (m.val - 2 * t) else false)
      ((constFn k (t + 1)).testBit (winPos k d l.val m.val hk).val)
  have hinitF_bd : ∀ m, DRBounds N G0 0 (initF m) := fun m => by
    dsimp [initF]; split_ifs
    · exact drBounds_xorConst _ (hrail_bd 0 _ G0)
    · exact drBounds_false (by omega) G0 0
  have hrF := drLocalRounds_spec B1 1 modF d G0 0 initF hwf0 hinitF_bd
  rcases hrF with ⟨hwfF, hextF, hlenF, hbdF, hevF⟩
  set rF := drLocalRounds N B1 1 modF d G0 initF with hrFdef
  let initS : Fin B1 → DRWire := fun m =>
    if 3 ≤ m.val then drXorConst (w_ext.val.testBit (m.val - 3)) (vRail (winPos k d l.val m.val hk))
    else (1, 0)
  let modS : ℕ → Fin B1 → Bool := fun t m =>
    Bool.xor (if 3 * (t + 1) + 1 ≤ m.val then w_ext.val.testBit (m.val - (3 * (t + 1) + 1)) else false)
      ((constFn k (r + t + 1)).testBit (winPos k d l.val m.val hk).val)
  have hinitS_bd : ∀ m, DRBounds N rF.1 0 (initS m) := fun m => by
    dsimp [initS]; split_ifs
    · exact drBounds_xorConst _ (hrail_bd 1 _ rF.1)
    · exact drBounds_false (by omega) rF.1 0
  have hrS := drLocalRounds_spec B1 2 modS d rF.1 0 initS hwfF hinitS_bd
  rcases hrS with ⟨hwfS, hextS, hlenS, hbdS, hevS⟩
  set rS := drLocalRounds N B1 2 modS d rF.1 initS with hrSdef
  set f3 := rF.2 ⟨3 * d + 3, by omega⟩
  set s4 := rS.2 ⟨3 * d + 3, by omega⟩
  have hf3_bd : DRBounds N rS.1 (7 * d) f3 :=
    drBounds_mono (by omega) (drBounds_of_extends hextS (hbdF ⟨3 * d + 3, by omega⟩))
  have hs4_bd : DRBounds N rS.1 (7 * d) s4 :=
    drBounds_mono (by omega) (hbdS ⟨3 * d + 3, by omega⟩)
  -- 8 final gates for fail2 / fail3 / fail4 / earlyFail
  set fail2 := pinWire k ((2, l), !(w_ext.val.testBit (3 * d + 3)))
  set f3T := addMGate N rS.1 true (pinWire k ((3, l), true)) f3.1 with hf3T
  have hwf1 : WellFormed N f3T.1 := addMGate_wf hwfS true (l := pinWire k ((3, l), true)) (r := f3.1)
    (pinWire_lt k rS.1 ((3, l), true)) hf3_bd.1
  have he1 : Extends rS.1 f3T.1 := addMGate_extends N rS.1 true (pinWire k ((3, l), true)) f3.1
  have hl1 : f3T.1.length = rS.1.length + 1 := addMGate_len N rS.1 true (pinWire k ((3, l), true)) f3.1
  have ho1 : f3T.2 < N + f3T.1.length := addMGate_out_lt N rS.1 true (pinWire k ((3, l), true)) f3.1
  set f3F := addMGate N f3T.1 true (pinWire k ((3, l), false)) f3.2 with hf3F
  have hwf2 : WellFormed N f3F.1 := addMGate_wf hwf1 true (l := pinWire k ((3, l), false)) (r := f3.2)
    (pinWire_lt k f3T.1 ((3, l), false)) (by have := hf3_bd.2.1; have := extends_len he1; omega)
  have he2 : Extends f3T.1 f3F.1 := addMGate_extends N f3T.1 true (pinWire k ((3, l), false)) f3.2
  have hl2 : f3F.1.length = f3T.1.length + 1 := addMGate_len N f3T.1 true (pinWire k ((3, l), false)) f3.2
  have ho2 : f3F.2 < N + f3F.1.length := addMGate_out_lt N f3T.1 true (pinWire k ((3, l), false)) f3.2
  set fail3 := addMGate N f3F.1 false f3T.2 f3F.2 with hfail3
  have hwf3 : WellFormed N fail3.1 := addMGate_wf hwf2 false (l := f3T.2) (r := f3F.2)
    (by have := extends_len he2; omega) ho2
  have he3 : Extends f3F.1 fail3.1 := addMGate_extends N f3F.1 false f3T.2 f3F.2
  have hl3 : fail3.1.length = f3F.1.length + 1 := addMGate_len N f3F.1 false f3T.2 f3F.2
  have ho3 : fail3.2 < N + fail3.1.length := addMGate_out_lt N f3F.1 false f3T.2 f3F.2
  have heS3 := extends_trans he1 (extends_trans he2 he3)
  have hs4_3 : DRBounds N fail3.1 (7 * d) s4 := drBounds_of_extends heS3 hs4_bd
  set s4T := addMGate N fail3.1 true (pinWire k ((4, l), true)) s4.1 with hs4T
  have hwf4 : WellFormed N s4T.1 := addMGate_wf hwf3 true (l := pinWire k ((4, l), true)) (r := s4.1)
    (pinWire_lt k fail3.1 ((4, l), true)) hs4_3.1
  have he4 : Extends fail3.1 s4T.1 := addMGate_extends N fail3.1 true (pinWire k ((4, l), true)) s4.1
  have hl4 : s4T.1.length = fail3.1.length + 1 := addMGate_len N fail3.1 true (pinWire k ((4, l), true)) s4.1
  have ho4 : s4T.2 < N + s4T.1.length := addMGate_out_lt N fail3.1 true (pinWire k ((4, l), true)) s4.1
  set s4F := addMGate N s4T.1 true (pinWire k ((4, l), false)) s4.2 with hs4F
  have hwf5 : WellFormed N s4F.1 := addMGate_wf hwf4 true (l := pinWire k ((4, l), false)) (r := s4.2)
    (pinWire_lt k s4T.1 ((4, l), false)) (by have := hs4_3.2.1; have := extends_len he4; omega)
  have he5 : Extends s4T.1 s4F.1 := addMGate_extends N s4T.1 true (pinWire k ((4, l), false)) s4.2
  have hl5 : s4F.1.length = s4T.1.length + 1 := addMGate_len N s4T.1 true (pinWire k ((4, l), false)) s4.2
  have ho5 : s4F.2 < N + s4F.1.length := addMGate_out_lt N s4T.1 true (pinWire k ((4, l), false)) s4.2
  set fail4 := addMGate N s4F.1 false s4T.2 s4F.2 with hfail4
  have hwf6 : WellFormed N fail4.1 := addMGate_wf hwf5 false (l := s4T.2) (r := s4F.2)
    (by have := extends_len he5; omega) ho5
  have he6 : Extends s4F.1 fail4.1 := addMGate_extends N s4F.1 false s4T.2 s4F.2
  have hl6 : fail4.1.length = s4F.1.length + 1 := addMGate_len N s4F.1 false s4T.2 s4F.2
  have ho6 : fail4.2 < N + fail4.1.length := addMGate_out_lt N s4F.1 false s4T.2 s4F.2
  have he36 := extends_trans he4 (extends_trans he5 he6)
  set f23 := addMGate N fail4.1 false fail2 fail3.2 with hf23
  have hwf7 : WellFormed N f23.1 := addMGate_wf hwf6 false (l := fail2) (r := fail3.2)
    (pinWire_lt k fail4.1 ((2, l), !(w_ext.val.testBit (3 * d + 3)))) (by have := extends_len he36; omega)
  have he7 : Extends fail4.1 f23.1 := addMGate_extends N fail4.1 false fail2 fail3.2
  have hl7 : f23.1.length = fail4.1.length + 1 := addMGate_len N fail4.1 false fail2 fail3.2
  have ho7 : f23.2 < N + f23.1.length := addMGate_out_lt N fail4.1 false fail2 fail3.2
  set early := addMGate N f23.1 false f23.2 fail4.2 with hearly
  have hwf8 : WellFormed N early.1 := addMGate_wf hwf7 false (l := f23.2) (r := fail4.2)
    ho7 (by have := extends_len he7; omega)
  have he8 : Extends f23.1 early.1 := addMGate_extends N f23.1 false f23.2 fail4.2
  have hl8 : early.1.length = f23.1.length + 1 := addMGate_len N f23.1 false f23.2 fail4.2
  have ho8 : early.2 < N + early.1.length := addMGate_out_lt N f23.1 false f23.2 fail4.2
  have hd_f3 : (mdepths N fail3.1).getD fail3.2 0 ≤ 7 * d + 2 := by
    have h1 : (mdepths N f3T.1).getD f3T.2 0 ≤ 7 * d + 1 := by
      rw [hf3T, addMGate_depth, pinWire_depth, mdepths_of_extends hextS _ (hbdF _).1]
      have := (hbdF ⟨3 * d + 3, by omega⟩).2.2.1; omega
    have h2 : (mdepths N f3F.1).getD f3F.2 0 ≤ 7 * d + 1 := by
      rw [hf3F, addMGate_depth, pinWire_depth, mdepths_of_extends he1 _ hf3_bd.2.1]
      have := hf3_bd.2.2.2; omega
    rw [hfail3, addMGate_depth, mdepths_of_extends he2 _ ho1]; omega
  have hd_s4 : (mdepths N fail4.1).getD fail4.2 0 ≤ 7 * d + 2 := by
    have h1 : (mdepths N s4T.1).getD s4T.2 0 ≤ 7 * d + 1 := by
      rw [hs4T, addMGate_depth, pinWire_depth]; have := hs4_3.2.2.1; omega
    have h2 : (mdepths N s4F.1).getD s4F.2 0 ≤ 7 * d + 1 := by
      rw [hs4F, addMGate_depth, pinWire_depth, mdepths_of_extends he4 _ hs4_3.2.1]
      have := hs4_3.2.2.2; omega
    rw [hfail4, addMGate_depth, mdepths_of_extends he5 _ ho4]; omega
  have hd_23 : (mdepths N f23.1).getD f23.2 0 ≤ 7 * d + 3 := by
    rw [hf23, addMGate_depth, pinWire_depth, mdepths_of_extends he36 _ ho3]; omega
  have hd_8 : (mdepths N early.1).getD early.2 0 ≤ 7 * d + 4 := by
    rw [hearly, addMGate_depth, mdepths_of_extends he7 _ ho6]; omega
  have heS8 := extends_trans heS3 (extends_trans he36 (extends_trans he7 he8))
  have hlen_fin : early.1.length ≤ G0.length + (88 * d * (7 * d + 4) + 8) := by
    have hlenS8 : early.1.length = rS.1.length + 8 := by rw [hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]
    have h44 : B1 = 7 * d + 4 := rfl
    calc early.1.length = rS.1.length + 8 := hlenS8
      _ ≤ (rF.1.length + 44 * B1 * d) + 8 := Nat.add_le_add_right hlenS 8
      _ ≤ ((G0.length + 44 * B1 * d) + 44 * B1 * d) + 8 := Nat.add_le_add_right (Nat.add_le_add_right hlenF _) 8
      _ = G0.length + (88 * d * (7 * d + 4) + 8) := by rw [h44]; ring
  dsimp only [res, addEarlyCell]; rw [← hrFdef, ← hrSdef]
  change WellFormed N early.1 ∧ Extends G0 early.1 ∧ early.1.length ≤ G0.length + (88 * d * (7 * d + 4) + 8) ∧
    early.2 < N + early.1.length ∧ (mdepths N early.1).getD early.2 0 ≤ 7 * d + 4 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool),
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun early.1 (mkBits ρ)).getD early.2 false = true ↔ ¬ earlyPassCond k r d hk u v ρ l w_ext)
  refine ⟨hwf8, extends_trans hextF (extends_trans hextS heS8), hlen_fin, ho8, hd_8, ?_⟩
  · intro u v ρ huv
    have hf3_x : DRExact rS.1 (mkBits ρ) f3 (localFirstState k d l.val hk w_ext u d ⟨3 * d + 3, by omega⟩) := by
      have hf := hevF (mkBits ρ) (localFirstState k d l.val hk w_ext u)
        (fun m => by
          dsimp [initF, localFirstState]; split_ifs with hm
          · rw [Bool.xor_comm]
            exact drExact_xorConst (hrail_exact 0 u ρ (fun i => (huv i).1) G0 (winPos k d l.val m.val hk))
          · exact drExact_false G0 _)
        (fun s m => by simp [localFirstState, modF]; rfl) ⟨3 * d + 3, by omega⟩
      exact drExact_of_extends hextS (hbdF _).1 (hbdF _).2.1 hf
    have hs4_x : DRExact rS.1 (mkBits ρ) s4 (localSecondState k r d l.val hk w_ext v d ⟨3 * d + 3, by omega⟩) :=
      hevS (mkBits ρ) (localSecondState k r d l.val hk w_ext v)
        (fun m => by
          dsimp [initS, localSecondState]; split_ifs with hm
          · rw [Bool.xor_comm]
            exact drExact_xorConst (hrail_exact 1 v ρ (fun i => (huv i).2) rF.1 (winPos k d l.val m.val hk))
          · exact drExact_false rF.1 _)
        (fun s m => by simp [localSecondState, modS]; rfl) ⟨3 * d + 3, by omega⟩
    have hv3 : (mrun fail3.1 (mkBits ρ)).getD fail3.2 false = true ↔
        ¬ (∀ b : Bool, ρ (3, l) = some b → localFirstState k d l.val hk w_ext u d ⟨3 * d + 3, by omega⟩ = b) := by
      rw [hfail3, addMGate_val]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      rw [mrun_of_extends he2 _ _ ho1, hf3T, hf3F, addMGate_val, addMGate_val]
      simp only [↓reduceIte, Bool.and_eq_true, pinWire_val, mkBits, decide_eq_true_eq]
      rw [mrun_of_extends he1 _ _ hf3_bd.2.1, hf3_x.1, hf3_x.2]
      cases hval : localFirstState k d l.val hk w_ext u d ⟨3 * d + 3, by omega⟩ <;> simp
    have hv4 : (mrun fail4.1 (mkBits ρ)).getD fail4.2 false = true ↔
        ¬ (∀ b : Bool, ρ (4, l) = some b → localSecondState k r d l.val hk w_ext v d ⟨3 * d + 3, by omega⟩ = b) := by
      rw [hfail4, addMGate_val]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      rw [mrun_of_extends he5 _ _ ho4, hs4T, hs4F, addMGate_val, addMGate_val]
      simp only [↓reduceIte, Bool.and_eq_true, pinWire_val, mkBits, decide_eq_true_eq]
      rw [mrun_of_extends he4 _ _ hs4_3.2.1,
        mrun_of_extends heS3 _ _ hs4_bd.1, mrun_of_extends heS3 _ _ hs4_bd.2.1,
        hs4_x.1, hs4_x.2]
      cases hval : localSecondState k r d l.val hk w_ext v d ⟨3 * d + 3, by omega⟩ <;> simp
    rw [hearly, addMGate_val]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
    rw [mrun_of_extends he7 _ _ ho6, hf23, addMGate_val]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
    rw [pinWire_val, mrun_of_extends he36 _ _ ho3, hv3, hv4]
    have h2' : mkBits ρ ((2, l), !(w_ext.val.testBit (3 * d + 3))) = true ↔
        ¬ (∀ b : Bool, ρ (2, l) = some b → w_ext.val.testBit (3 * d + 3) = b) := by
      simp only [mkBits, decide_eq_true_eq]
      cases w_ext.val.testBit (3 * d + 3) <;> simp
    rw [h2']
    unfold earlyPassCond
    constructor
    · rintro ((h | h) | h) ⟨h2, h3, h4⟩
      · exact h h2
      · exact h h3
      · exact h h4
    · intro h
      by_cases h2 : ∀ b : Bool, ρ (2, l) = some b → w_ext.val.testBit (3 * d + 3) = b
      · by_cases h3 : ∀ b : Bool, ρ (3, l) = some b → localFirstState k d l.val hk w_ext u d ⟨3 * d + 3, by omega⟩ = b
        · exact Or.inr (fun h4 => h ⟨h2, h3, h4⟩)
        · exact Or.inl (Or.inr h3)
      · exact Or.inl (Or.inl h2)

-- Part 3: Global hash family, shift-register DP, singleton checks, late rounds, and full circuit

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


lemma card_bad_hash_315_lt {m k K : ℕ} (hk : 0 < k) (hM : (K + 1) ^ 2 ≤ 2 ^ m)
    (S : Finset (Fin k → Bool)) (hS : S.card ≤ K) :
    2 * (Finset.univ.filter (fun A : Fin m → Fin k → Bool =>
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ hashVal A x = hashVal A y)).card < 2 ^ (m * k) :=
  card_bad_hash_lt hk hM S hS

abbrev fitsTrack {k : ℕ} (ρ : (Fin 7 × Fin k) → Option Bool) (track : Fin 7) (x : ℕ) : Prop :=
  ∀ i : Fin k, ∀ b : Bool, ρ (track, i) = some b → x.testBit i.val = b

def candSet315 (k r d : ℕ) (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun x : Fin k → Bool =>
    fitsTrack ρ 2 (bitsToNat x) ∧
    fitsTrack ρ 3 (firstFn k d (bitsToNat x) (bitsToNat u)) ∧
    fitsTrack ρ 4 (secondFn k r d (bitsToNat x) (bitsToNat v)))

def uOfρ {k : ℕ} (ρ : (Fin 7 × Fin k) → Option Bool) : Fin k → Bool :=
  fun i => decide (ρ (0, i) = some true)

def vOfρ {k : ℕ} (ρ : (Fin 7 × Fin k) → Option Bool) : Fin k → Bool :=
  fun i => decide (ρ (1, i) = some true)

lemma uOfρ_eq {k : ℕ} {u v : Fin k → Bool} {ρ : (Fin 7 × Fin k) → Option Bool}
    (huv : ∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) :
    uOfρ ρ = u ∧ vOfρ ρ = v := by
  constructor <;> funext i <;> [have h := (huv i).1; have h := (huv i).2]
  · simp [uOfρ, h]
  · simp [vOfρ, h]

lemma hashFamily_exists_315 (k r d K : ℕ) (hk : 0 < k) :
    let m := 2 * Nat.clog 2 (K + 1)
    let R := 14 * k + 1
    ∃ H : Fin R → (Fin m → Fin k → Bool),
      ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool),
        (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
        (candSet315 k r d u v ρ).card ≤ K →
        ∃ idx : Fin R, ∀ x ∈ candSet315 k r d u v ρ, ∀ y ∈ candSet315 k r d u v ρ,
          hashVal (H idx) (fun l => x (enterIdx k d hk l)) =
            hashVal (H idx) (fun l => y (enterIdx k d hk l)) → x = y := by
  intro m R
  have hM : (K + 1) ^ 2 ≤ 2 ^ m := by
    have h1 : K + 1 ≤ 2 ^ Nat.clog 2 (K + 1) := Nat.le_pow_clog (by omega) (K + 1)
    have h2 : (K + 1) ^ 2 ≤ (2 ^ Nat.clog 2 (K + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (2 ^ Nat.clog 2 (K + 1)) ^ 2 = 2 ^ m := by rw [← pow_mul, Nat.mul_comm]
    omega
  let Inst := (Fin 7 × Fin k) → Option Bool
  let candShift : Inst → Finset (Fin k → Bool) := fun p =>
    (candSet315 k r d (uOfρ p) (vOfρ p) p).image (fun x l => x (enterIdx k d hk l))
  set Small := (Finset.univ : Finset Inst).filter (fun p => (candShift p).card ≤ K)
  let badA (p : Inst) : Finset (Fin m → Fin k → Bool) :=
    Finset.univ.filter (fun A => ∃ x ∈ candShift p, ∃ y ∈ candShift p, x ≠ y ∧ hashVal A x = hashVal A y)
  let badH (p : Inst) : Finset (Fin R → Fin m → Fin k → Bool) :=
    Fintype.piFinset (fun _ : Fin R => badA p)
  set Bad := Small.biUnion badH
  have hInstCard : Fintype.card Inst < 2 ^ R := by
    have h1 : Fintype.card Inst = 3 ^ (7 * k) := by
      rw [Fintype.card_fun, Fintype.card_option, Fintype.card_bool, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin]
    have h2 : 3 ^ (7 * k) ≤ 2 ^ (14 * k) := by
      have hpow : (3 : ℕ) ^ 7 ≤ 2 ^ 14 := by norm_num
      rw [show 3 ^ (7 * k) = (3 ^ 7) ^ k by rw [← pow_mul],
        show 2 ^ (14 * k) = (2 ^ 14) ^ k by rw [← pow_mul]]
      exact Nat.pow_le_pow_left hpow k
    rw [h1]
    exact lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by omega) (by omega))
  have hSmallLt : Small.card < 2 ^ R :=
    lt_of_le_of_lt (Finset.card_le_univ _) (by simpa [Finset.card_univ] using hInstCard)
  have hBadOne : ∀ p ∈ Small, 2 ^ R * (badH p).card ≤ (2 ^ (m * k)) ^ R := by
    intro p hp
    simp only [Small, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hlt := card_bad_hash_lt hk hM (candShift p) hp
    have hcard : (badH p).card = (badA p).card ^ R := by rw [Fintype.card_piFinset]; simp
    rw [hcard, ← mul_pow]
    exact Nat.pow_le_pow_left (le_of_lt hlt) R
  have hBadLt : Bad.card < (Finset.univ : Finset (Fin R → Fin m → Fin k → Bool)).card := by
    have htot : (Finset.univ : Finset (Fin R → Fin m → Fin k → Bool)).card = (2 ^ (m * k)) ^ R := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
        ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1; ring
    rw [htot]
    have h1 : 2 ^ R * Bad.card ≤ ∑ p ∈ Small, 2 ^ R * (badH p).card := by
      rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ Finset.card_biUnion_le
    have h2 : ∑ p ∈ Small, 2 ^ R * (badH p).card ≤ Small.card * (2 ^ (m * k)) ^ R := by
      calc ∑ p ∈ Small, 2 ^ R * (badH p).card
          ≤ ∑ _p ∈ Small, (2 ^ (m * k)) ^ R := Finset.sum_le_sum hBadOne
        _ = Small.card * (2 ^ (m * k)) ^ R := by simp
    have h3 : Small.card * (2 ^ (m * k)) ^ R < 2 ^ R * (2 ^ (m * k)) ^ R :=
      Nat.mul_lt_mul_of_pos_right hSmallLt (by positivity)
    exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt (le_trans h1 h2) h3)
  have hne : (Finset.univ \ Bad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    exact not_lt_of_ge (Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp hemp)) hBadLt
  rcases hne with ⟨H, hH⟩
  rw [Finset.mem_sdiff] at hH
  refine ⟨H, fun u v ρ huv hcard => ?_⟩
  rcases uOfρ_eq huv with ⟨hu, hv⟩
  have hcard_sh : (candShift ρ).card ≤ K := by
    refine le_trans Finset.card_image_le ?_
    simpa only [hu, hv] using hcard
  by_contra hall
  push Not at hall
  apply hH.2
  refine Finset.mem_biUnion.mpr ⟨ρ, by simp [Small, hcard_sh], ?_⟩
  rw [Fintype.mem_piFinset]
  intro idx
  rcases hall idx with ⟨x, hx, y, hy, heq, hne⟩
  have hx' : (fun l => x (enterIdx k d hk l)) ∈ candShift ρ :=
    Finset.mem_image.mpr ⟨x, by simpa only [hu, hv] using hx, rfl⟩
  have hy' : (fun l => y (enterIdx k d hk l)) ∈ candShift ρ :=
    Finset.mem_image.mpr ⟨y, by simpa only [hu, hv] using hy, rfl⟩
  have hne' : (fun l => x (enterIdx k d hk l)) ≠ (fun l => y (enterIdx k d hk l)) := by
    intro hfn; apply hne; funext i
    rw [← enterIdx_inv k d hk i]
    exact congrFun hfn (enterInv k d hk i)
  simp only [badA, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨_, hx', _, hy', hne', heq⟩

-- Inductive DP path predicate matching two predecessors per transition
def HasPath315 (k r d m : ℕ) (hk : 0 < k) (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool)
    (A : Fin m → Fin k → Bool) (opt : Option (Fin k × Bool)) :
    (l : ℕ) → l ≤ k → Fin (2 ^ (7 * d + 3)) → Fin (2 ^ (7 * d + 3)) → Fin (2 ^ m) → Prop
  | 0, _, st, en, s => st = en ∧ s = 0
  | l + 1, hl, st, en, s =>
    ∃ old0 : Bool,
      let B := 7 * d + 3
      let prevW := prevWin B en old0
      let b := en.val.testBit (B - 1)
      let sPrev := if b then sXor s (hashCol A ⟨l, by omega⟩) else s
      HasPath315 k r d m hk u v ρ A opt l (by omega) st prevW sPrev ∧
      earlyPassCond k r d hk u v ρ ⟨l, by omega⟩ (joinWin B old0 en) ∧
      (∀ l0 b0, opt = some (l0, b0) → l0.val = l → b = b0)

lemma cand_eq_extWin_local {k r d : ℕ} (hk : 0 < k) (u v x : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) :
    let B := 7 * d + 3
    let winAt : ℕ → Fin (2 ^ B) := fun l =>
      ⟨bitsToNat (fun m : Fin B => x (winPos k d l m.val hk)), bitsToNat_lt _⟩
    (∀ l : Fin k, earlyPassCond k r d hk u v ρ l (joinWin B (x (winPos k d l.val 0 hk)) (winAt (l.val + 1)))) ↔
      (x ∈ candSet315 k r d u v ρ) := by
  intro B winAt
  have hB : 0 < B := by omega
  have hw_eq : ∀ (l : Fin k) (m : ℕ), m ≤ B →
      (joinWin B (x (winPos k d l.val 0 hk)) (winAt (l.val + 1))).val.testBit m = x (winPos k d l.val m hk) := by
    intro l m hm
    rw [joinWin_testBit _ _ hm]
    cases m with
    | zero => rfl
    | succ m' =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      change (bitsToNat (fun m'' : Fin B => x (winPos k d (l.val + 1) m''.val hk))).testBit m' = _
      rw [bitsToNat_testBit (i := ⟨m', by omega⟩)]
      congr 1; apply Fin.ext; unfold winPos; ring_nf
  have h1 : ∀ (l : Fin k), localFirstState k d l.val hk
      (joinWin B (x (winPos k d l.val 0 hk)) (winAt (l.val + 1))) u d ⟨3 * d + 3, by omega⟩ =
      (firstFn k d (bitsToNat x) (bitsToNat u)).testBit l.val := by
    intro l
    have heq := localFirstState_eq hk x u _ (hw_eq l) d le_rfl (3 * d + 3)
      (by omega) (by omega) (by omega)
    rw [heq, winPos_center]
  have h2 : ∀ (l : Fin k), localSecondState k r d l.val hk
      (joinWin B (x (winPos k d l.val 0 hk)) (winAt (l.val + 1))) v d ⟨3 * d + 3, by omega⟩ =
      (secondFn k r d (bitsToNat x) (bitsToNat v)).testBit l.val := by
    intro l
    have heq := localSecondState_eq (r := r) hk x v _ (hw_eq l) d le_rfl (3 * d + 3)
      (by omega) (by omega) (by omega)
    rw [heq, winPos_center]
  constructor
  · intro hall
    simp only [candSet315, Finset.mem_filter, Finset.mem_univ, true_and, fitsTrack]
    refine ⟨?_, ?_, ?_⟩
    · intro l b hρ
      have h0 := (hall l).1 b hρ
      rw [hw_eq l (3 * d + 3) (by omega), winPos_center, ← bitsToNat_testBit x l] at h0
      exact h0
    · intro l b hρ
      rw [← h1 l]; exact (hall l).2.1 b hρ
    · intro l b hρ
      rw [← h2 l]; exact (hall l).2.2 b hρ
  · intro hmem l
    simp only [candSet315, Finset.mem_filter, Finset.mem_univ, true_and, fitsTrack] at hmem
    refine ⟨?_, ?_, ?_⟩
    · intro b hρ
      rw [hw_eq l (3 * d + 3) (by omega), winPos_center, ← bitsToNat_testBit x l]
      exact hmem.1 l b hρ
    · intro b hρ
      rw [h1 l]; exact hmem.2.1 l b hρ
    · intro b hρ
      rw [h2 l]; exact hmem.2.2 l b hρ

lemma exists_hasPath_cycle_iff_315 (k r d m : ℕ) (hk : 0 < k) (u v : Fin k → Bool)
    (ρ : (Fin 7 × Fin k) → Option Bool) (A : Fin m → Fin k → Bool) (opt : Option (Fin k × Bool))
    (s : Fin (2 ^ m)) :
    (∃ u_win : Fin (2 ^ (7 * d + 3)), HasPath315 k r d m hk u v ρ A opt k le_rfl u_win u_win s) ↔
      ∃ x ∈ candSet315 k r d u v ρ,
        hashVal A (fun l => x (enterIdx k d hk l)) = s ∧
        ∀ l0 b0, opt = some (l0, b0) → x (enterIdx k d hk l0) = b0 := by
  let B := 7 * d + 3
  have hB : 0 < B := by omega
  constructor
  · rintro ⟨u_win, hp⟩
    -- Build cycle p : Fin (k + 1) → Fin (2 ^ B) recursively backwards
    have hex_seq : ∀ (l : ℕ) (hl : l ≤ k) (en : Fin (2 ^ B)) (s0 : Fin (2 ^ m)),
        HasPath315 k r d m hk u v ρ A opt l hl u_win en s0 →
        ∃ (p : Fin (l + 1) → Fin (2 ^ B)),
          p 0 = u_win ∧ p ⟨l, Nat.lt_succ_self l⟩ = en ∧
          (∀ j : Fin l, p j.succ = nextWin B (p j.castSucc) ((p j.succ).val.testBit (B - 1))) ∧
          (∀ j : Fin l, earlyPassCond k r d hk u v ρ ⟨j.val, by omega⟩
            (joinWin B ((p j.castSucc).val.testBit 0) (p j.succ))) ∧
          (∀ j : Fin l, ∀ l0 b0, opt = some (l0, b0) → l0.val = j.val →
            (p j.succ).val.testBit (B - 1) = b0) ∧
          hashPrefix A (fun j : Fin k => if hj : j.val < l then (p ⟨j.val + 1, by omega⟩).val.testBit (B - 1) else false) l hl = s0 := by
      intro l
      induction l with
      | zero =>
        intro hl en s0 hp0
        rcases hp0 with ⟨rfl, rfl⟩
        exact ⟨fun _ => u_win, rfl, rfl, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
          fun j => Fin.elim0 j, by simp [hashPrefix]⟩
      | succ l ih =>
        intro hl en s0 ⟨old0, hprev, hearly, hopt⟩
        rcases ih (by omega) (prevWin B en old0) _ hprev with ⟨p0, hp0_start, hp0_end, hp0_step, hp0_early, hp0_opt, hp0_hash⟩
        let p : Fin (l + 2) → Fin (2 ^ B) := fun i =>
          if hi : i.val ≤ l then p0 ⟨i.val, by omega⟩ else en
        refine ⟨p, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [p, hp0_start]
        · have : ¬ (l + 1 ≤ l) := by omega
          simp [p, this]
        · intro j
          by_cases hjl : j.val < l
          · have h1 : j.succ.val ≤ l := by simp; omega
            have h2 : j.castSucc.val ≤ l := by simp; omega
            simp only [p, h1, ↓reduceDIte, h2]
            exact hp0_step ⟨j.val, hjl⟩
          · have hjeq : j.val = l := by omega
            have hjc : j.castSucc.val ≤ l := by simp; omega
            have hjs : ¬ (j.succ.val ≤ l) := by simp; omega
            simp only [p, hjc, ↓reduceDIte, hjs]
            have hpeq : p0 ⟨j.castSucc.val, by omega⟩ = prevWin B en old0 := by
              rw [← hp0_end]; congr 1; apply Fin.ext; simp [hjeq]
            rw [hpeq]
            exact (nextWin_iff_prevWin hB _ en _).mpr ⟨rfl, by rw [prevWin_testBit hB en old0 hB]; simp⟩
        · intro j
          by_cases hjl : j.val < l
          · have h1 : j.succ.val ≤ l := by simp; omega
            have h2 : j.castSucc.val ≤ l := by simp; omega
            simp only [p, h1, ↓reduceDIte, h2]
            exact hp0_early ⟨j.val, hjl⟩
          · have hjeq : j.val = l := by omega
            have hjc : j.castSucc.val ≤ l := by simp; omega
            have hjs : ¬ (j.succ.val ≤ l) := by simp; omega
            simp only [p, hjc, ↓reduceDIte, hjs]
            have hpeq : p0 ⟨j.castSucc.val, by omega⟩ = prevWin B en old0 := by
              rw [← hp0_end]; congr 1; apply Fin.ext; simp [hjeq]
            rw [hpeq, prevWin_testBit hB en old0 hB]; simp only [↓reduceIte]
            have hje : (⟨j.val, by omega⟩ : Fin k) = ⟨l, by omega⟩ := Fin.ext hjeq
            rw [hje]
            exact hearly
        · intro j l0 b0 ho hlj
          by_cases hjl : j.val < l
          · have h1 : j.succ.val ≤ l := by simp; omega
            simp only [p, h1, ↓reduceDIte]
            exact hp0_opt ⟨j.val, hjl⟩ l0 b0 ho hlj
          · have hjeq : j.val = l := by omega
            have hjs : ¬ (j.succ.val ≤ l) := by simp; omega
            simp only [p, hjs, ↓reduceDIte]
            exact hopt l0 b0 ho (by omega)
        · unfold hashPrefix
          have hlast_val : (if hl1 : l < l + 1 then (p ⟨l + 1, by omega⟩).val.testBit (B - 1) else false) =
              en.val.testBit (B - 1) := by
            have h1 : ¬ (l + 1 ≤ l) := by omega
            simp [p, h1]
          have hpref_congr : hashPrefix A (fun j : Fin k => if hj : j.val < l + 1 then
              (p ⟨j.val + 1, by omega⟩).val.testBit (B - 1) else false) l (by omega) =
              hashPrefix A (fun j : Fin k => if hj : j.val < l then
              (p0 ⟨j.val + 1, by omega⟩).val.testBit (B - 1) else false) l (by omega) := by
            have hcong : ∀ (n' : ℕ) (hn' : n' ≤ l),
                hashPrefix A (fun j : Fin k => if hj : j.val < l + 1 then
                  (p ⟨j.val + 1, by omega⟩).val.testBit (B - 1) else false) n' (by omega) =
                hashPrefix A (fun j : Fin k => if hj : j.val < l then
                  (p0 ⟨j.val + 1, by omega⟩).val.testBit (B - 1) else false) n' (by omega) := by
              intro n'; induction n' with
              | zero => intro _; rfl
              | succ n' ihn =>
                intro hn'; unfold hashPrefix
                rw [ihn (by omega)]
                have h1 : n' < l + 1 := by omega
                have h2 : n' < l := by omega
                have hle : n' + 1 ≤ l := by omega
                simp only [h1, h2, ↓reduceDIte, p, hle]
            exact hcong l le_rfl
          rw [hpref_congr, hp0_hash, hlast_val]
          cases hb : en.val.testBit (B - 1)
          · simp
          · simp only [↓reduceIte]; exact sXor_self_cancel s0 (hashCol A ⟨l, by omega⟩)
    rcases hex_seq k le_rfl u_win s hp with ⟨p, hp0, hpk, hstep, hearly, hopt, hhash⟩
    have hpk' : p (Fin.last k) = u_win := by simpa [Fin.last] using hpk
    have hcyc := nextWin_cycle_unique hk p (by rw [hp0, hpk']) hstep
    let x : Fin k → Bool := fun i => (p (enterInv k d hk i).succ).val.testBit (B - 1)
    refine ⟨x, ?_, ?_, ?_⟩
    · have hcw := (cand_eq_extWin_local (r := r) (d := d) hk u v x ρ).mp
      apply hcw
      intro l
      have hpl := hcyc l.castSucc
      have hpls := hcyc l.succ
      have hold0 : (p l.castSucc).val.testBit 0 = x (winPos k d l.val 0 hk) := by
        rw [hpl]; change (bitsToNat _).testBit 0 = _
        rw [bitsToNat_testBit (i := ⟨0, hB⟩)]; rfl
      have hps_eq : p l.succ = ⟨bitsToNat (fun m' : Fin B => x (winPos k d (l.val + 1) m'.val hk)), bitsToNat_lt _⟩ :=
        hpls
      have hel := hearly l
      rw [hold0, hps_eq] at hel
      exact hel
    · have hx_fn : (fun l : Fin k => x (enterIdx k d hk l)) =
          (fun j : Fin k => (p ⟨j.val + 1, by omega⟩).val.testBit (B - 1)) := by
        funext l; dsimp only [x]; rw [enterInv_idx]; rfl
      rw [hx_fn]
      simpa [hashVal] using hhash
    · intro l0 b0 ho
      have hx0 : x (enterIdx k d hk l0) = (p l0.succ).val.testBit (B - 1) := by
        dsimp only [x]; rw [enterInv_idx]
      rw [hx0]; exact hopt l0 l0 b0 ho rfl
  · rintro ⟨x, hx_mem, hhash, hopt⟩
    let winAt : ℕ → Fin (2 ^ B) := fun l =>
      ⟨bitsToNat (fun m : Fin B => x (winPos k d l m.val hk)), bitsToNat_lt _⟩
    have hcand := (cand_eq_extWin_local hk u v x ρ).mpr hx_mem
    have hind : ∀ (l : ℕ) (hl : l ≤ k),
        HasPath315 k r d m hk u v ρ A opt l hl (winAt 0) (winAt l)
          (hashPrefix A (fun j => x (enterIdx k d hk j)) l hl) := by
      intro l
      induction l with
      | zero =>
        intro hl; exact ⟨rfl, rfl⟩
      | succ l ih =>
        intro hl
        let old0 := x (winPos k d l 0 hk)
        refine ⟨old0, ?_, hcand ⟨l, by omega⟩, ?_⟩
        · have hsh := winBefore_shift (d := d) hk x l
          have hnp := (nextWin_iff_prevWin hB (winAt l) (winAt (l + 1)) (x (winPos k d l B hk))).mp hsh
          have hpw : prevWin B (winAt (l + 1)) old0 = winAt l := by
            have hold_eq : (winAt l).val.testBit 0 = old0 := by
              change (bitsToNat _).testBit 0 = _
              rw [bitsToNat_testBit (i := ⟨0, hB⟩)]
            rw [← hold_eq]; exact hnp.2.symm
          have hbit : (winAt (l + 1)).val.testBit (B - 1) = x (enterIdx k d hk ⟨l, by omega⟩) := by
            rw [← hnp.1]; rfl
          have hs_eq : (if (winAt (l + 1)).val.testBit (B - 1) then
              sXor (hashPrefix A (fun j => x (enterIdx k d hk j)) (l + 1) hl) (hashCol A ⟨l, by omega⟩)
            else hashPrefix A (fun j => x (enterIdx k d hk j)) (l + 1) hl) =
              hashPrefix A (fun j => x (enterIdx k d hk j)) l (by omega) := by
            rw [hbit]; dsimp only [hashPrefix]
            split_ifs <;> first | exact sXor_self_cancel _ _ | rfl | contradiction
          rw [hpw, hs_eq]
          exact ih (by omega)
        · intro l0 b0 ho hlj
          have hsh := winBefore_shift (d := d) hk x l
          have hnp := (nextWin_iff_prevWin hB (winAt l) (winAt (l + 1)) (x (winPos k d l B hk))).mp hsh
          rw [← hnp.1]
          have heq : (⟨l, by omega⟩ : Fin k) = l0 := Fin.ext hlj.symm
          change x (enterIdx k d hk ⟨l, by omega⟩) = b0
          rw [heq]; exact hopt l0 b0 ho
    refine ⟨winAt 0, ?_⟩
    have hwin_k : winAt k = winAt 0 := by
      apply Fin.ext; dsimp only [winAt]; change bitsToNat _ = bitsToNat _
      congr 1; funext m; congr 1; apply Fin.ext
      unfold winPos; dsimp only; rw [Nat.zero_add]
      rw [show k + winShift k d + m.val = (winShift k d + m.val) + k by ring, Nat.add_mod_right]
    have hp := hind k le_rfl
    rw [hwin_k] at hp
    change HasPath315 k r d m hk u v ρ A opt k le_rfl (winAt 0) (winAt 0)
      (hashVal A (fun j => x (enterIdx k d hk j))) at hp
    rw [hhash] at hp
    exact hp

-- Part 3b: DP Scans, Hash Ready, Late Rounds, AddSingleHash, BuildFullCircuit, Final Theorem

noncomputable def addDpCell (k d m l : ℕ) (hk : 0 < k) (hl : l < k)
    (A : Fin m → Fin k → Bool) (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (opt : Option (Fin k × Bool)) (prev : Fin (2 ^ (7 * d + 3)) × Fin (2 ^ (7 * d + 3)) × Fin (2 ^ m) → ℕ)
    (G : List MGate) (uvs : Fin (2 ^ (7 * d + 3)) × Fin (2 ^ (7 * d + 3)) × Fin (2 ^ m)) : List MGate × ℕ :=
  let B := 7 * d + 3
  let N := 2 + Fintype.card (Pin315 k)
  let u_win := uvs.1
  let en := uvs.2.1
  let s := uvs.2.2
  let b := en.val.testBit (B - 1)
  if (∀ l0 b0, opt = some (l0, b0) → l0.val = l → b = b0) then
    let sPrev := if b then sXor s (hashCol A ⟨l, hl⟩) else s
    let pF := prev (u_win, prevWin B en false, sPrev)
    let pT := prev (u_win, prevWin B en true, sPrev)
    let oF := addMGate N G false pF (earlyFail (⟨l, hl⟩, joinWin B false en))
    let oT := addMGate N oF.1 false pT (earlyFail (⟨l, hl⟩, joinWin B true en))
    addMGate N oT.1 true oF.2 oT.2
  else
    (G, 1)

lemma addDpCell_spec {k r d m l : ℕ} (hk : 0 < k) (hl : l < k)
    (A : Fin m → Fin k → Bool) (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (opt : Option (Fin k × Bool)) (prev : Fin (2 ^ (7 * d + 3)) × Fin (2 ^ (7 * d + 3)) × Fin (2 ^ m) → ℕ)
    (G0 : List MGate) (dpD : ℕ)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (hef_bd : ∀ lw, earlyFail lw < 2 + Fintype.card (Pin315 k) + G0.length)
    (hef_dep : ∀ lw, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (earlyFail lw) 0 ≤ 7 * d + 4)
    (hef_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) lw,
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (earlyFail lw) false = true ↔ ¬ earlyPassCond k r d hk u v ρ lw.1 lw.2))
    (hp_bd : ∀ uvs, prev uvs < 2 + Fintype.card (Pin315 k) + G0.length)
    (hp_dep : ∀ uvs, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (prev uvs) 0 ≤ dpD)
    (hdp_le : 7 * d + 4 ≤ dpD)
    (hp_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) uvs,
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (prev uvs) false = true ↔
        ¬ HasPath315 k r d m hk u v ρ A opt l (by omega) uvs.1 uvs.2.1 uvs.2.2))
    (uvs : Fin (2 ^ (7 * d + 3)) × Fin (2 ^ (7 * d + 3)) × Fin (2 ^ m)) :
    let B := 7 * d + 3
    let N := 2 + Fintype.card (Pin315 k)
    let res := addDpCell k d m l hk hl A earlyFail opt prev G0 uvs
    WellFormed N res.1 ∧ Extends G0 res.1 ∧ res.1.length ≤ G0.length + 3 ∧
    res.2 < N + res.1.length ∧ (mdepths N res.1).getD res.2 0 ≤ dpD + 2 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool),
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun res.1 (mkBits ρ)).getD res.2 false = true ↔
        ¬ HasPath315 k r d m hk u v ρ A opt (l + 1) hl uvs.1 uvs.2.1 uvs.2.2) := by
  intro B N res
  set u_win := uvs.1; set en := uvs.2.1; set s := uvs.2.2
  set b := en.val.testBit (B - 1)
  by_cases hopt : ∀ l0 b0, opt = some (l0, b0) → l0.val = l → b = b0
  · set sPrev := if b then sXor s (hashCol A ⟨l, hl⟩) else s
    set pF := prev (u_win, prevWin B en false, sPrev)
    set pT := prev (u_win, prevWin B en true, sPrev)
    set eF := earlyFail (⟨l, hl⟩, joinWin B false en)
    set eT := earlyFail (⟨l, hl⟩, joinWin B true en)
    set g1 := addMGate N G0 false pF eF with hg1
    have hwf1 : WellFormed N g1.1 := addMGate_wf hwf0 false (l := pF) (r := eF)
      (hp_bd (u_win, prevWin B en false, sPrev)) (hef_bd (⟨l, hl⟩, joinWin B false en))
    have he1 : Extends G0 g1.1 := addMGate_extends N G0 false pF eF
    have hl1 : g1.1.length = G0.length + 1 := addMGate_len N G0 false pF eF
    have ho1 : g1.2 < N + g1.1.length := addMGate_out_lt N G0 false pF eF
    set g2 := addMGate N g1.1 false pT eT with hg2
    have hwf2 : WellFormed N g2.1 := addMGate_wf hwf1 false (l := pT) (r := eT)
      (by have := hp_bd (u_win, prevWin B en true, sPrev); omega)
      (by have := hef_bd (⟨l, hl⟩, joinWin B true en); omega)
    have he2 : Extends g1.1 g2.1 := addMGate_extends N g1.1 false pT eT
    have hl2 : g2.1.length = g1.1.length + 1 := addMGate_len N g1.1 false pT eT
    have ho2 : g2.2 < N + g2.1.length := addMGate_out_lt N g1.1 false pT eT
    have he12 := extends_trans he1 he2
    set g3 := addMGate N g2.1 true g1.2 g2.2 with hg3
    have hwf3 : WellFormed N g3.1 := addMGate_wf hwf2 true (l := g1.2) (r := g2.2)
      (by have := extends_len he2; omega) ho2
    have he3 : Extends g2.1 g3.1 := addMGate_extends N g2.1 true g1.2 g2.2
    have hl3 : g3.1.length = g2.1.length + 1 := addMGate_len N g2.1 true g1.2 g2.2
    have ho3 : g3.2 < N + g3.1.length := addMGate_out_lt N g2.1 true g1.2 g2.2
    have he13 := extends_trans he12 he3
    have hd1 : (mdepths (2 + Fintype.card (Pin315 k)) g1.1).getD g1.2 0 ≤ dpD + 1 := by
      rw [hg1, addMGate_depth]; try dsimp only [N]
      have h1 : (mdepths (2 + Fintype.card (Pin315 k)) G0).getD pF 0 ≤ dpD :=
        hp_dep (u_win, prevWin B en false, sPrev)
      have h2 : (mdepths (2 + Fintype.card (Pin315 k)) G0).getD eF 0 ≤ 7 * d + 4 :=
        hef_dep (⟨l, hl⟩, joinWin B false en)
      omega
    have hd2 : (mdepths (2 + Fintype.card (Pin315 k)) g2.1).getD g2.2 0 ≤ dpD + 1 := by
      rw [hg2, addMGate_depth, mdepths_of_extends he1 pT (hp_bd _), mdepths_of_extends he1 eT (hef_bd _)]
      have h1 : (mdepths (2 + Fintype.card (Pin315 k)) G0).getD pT 0 ≤ dpD :=
        hp_dep (u_win, prevWin B en true, sPrev)
      have h2 : (mdepths (2 + Fintype.card (Pin315 k)) G0).getD eT 0 ≤ 7 * d + 4 :=
        hef_dep (⟨l, hl⟩, joinWin B true en)
      omega
    have hd3 : (mdepths (2 + Fintype.card (Pin315 k)) g3.1).getD g3.2 0 ≤ dpD + 2 := by
      rw [hg3, addMGate_depth, mdepths_of_extends he2 _ ho1]; try dsimp only [N]
      omega
    dsimp only [res, addDpCell]; dsimp only [b, en, B] at hopt; simp only [eq_true hopt, ↓reduceIte]
    change WellFormed N g3.1 ∧ Extends G0 g3.1 ∧ g3.1.length ≤ G0.length + 3 ∧ _
    refine ⟨hwf3, he13, by omega, ho3, hd3, ?_⟩
    intro u v ρ huv
    change (mrun g3.1 (mkBits ρ)).getD g3.2 false = true ↔
      ¬ HasPath315 k r d m hk u v ρ A opt (l + 1) hl u_win en s
    rw [hg3, addMGate_val]; simp only [↓reduceIte, Bool.and_eq_true]
    rw [mrun_of_extends he2 _ g1.2 ho1, hg1, hg2, addMGate_val, addMGate_val]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
    rw [mrun_of_extends he1 _ pT (hp_bd _), mrun_of_extends he1 _ eT (hef_bd _)]
    dsimp only [pF, pT, eF, eT]
    rw [hp_val u v ρ _ huv, hp_val u v ρ _ huv,
      hef_val u v ρ _ huv, hef_val u v ρ _ huv]
    conv_rhs => rw [HasPath315]
    constructor
    · rintro ⟨hF, hT⟩ ⟨old0, hprev, hearly, _⟩
      cases old0
      · rcases hF with hf | hf
        · exact hf hprev
        · exact hf hearly
      · rcases hT with ht | ht
        · exact ht hprev
        · exact ht hearly
    · intro hno
      have hall : ∀ old0 : Bool,
          ¬ HasPath315 k r d m hk u v ρ A opt l (by omega) u_win (prevWin B en old0) sPrev ∨
          ¬ earlyPassCond k r d hk u v ρ ⟨l, hl⟩ (joinWin B old0 en) := by
        intro old0
        by_cases h1 : HasPath315 k r d m hk u v ρ A opt l (by omega) u_win (prevWin B en old0) sPrev
        · right; intro h2; exact hno ⟨old0, h1, h2, hopt⟩
        · exact Or.inl h1
      exact ⟨hall false, hall true⟩
  · dsimp only [res, addDpCell]
    dsimp only [b, en, B] at hopt
    simp only [hopt, ↓reduceIte]
    refine ⟨hwf0, extends_rfl G0, by simp, by omega,
      by rw [mdepths_base G0 1 (by omega)]; omega, ?_⟩
    intro u v ρ _
    rw [mrun_const1]
    simp only [true_iff]
    rintro ⟨_, _, _, hopt'⟩
    exact hopt hopt'

noncomputable def addDpLayers (k d m : ℕ) (hk : 0 < k)
    (A : Fin m → Fin k → Bool) (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (opt : Option (Fin k × Bool)) (G0 : List MGate) :
    (l : ℕ) → l ≤ k → List MGate × (Fin (2 ^ (7 * d + 3)) × Fin (2 ^ (7 * d + 3)) × Fin (2 ^ m) → ℕ)
  | 0, _ => (G0, fun uvs => if uvs.1 = uvs.2.1 ∧ uvs.2.2 = 0 then 0 else 1)
  | l + 1, hl =>
    let prev := addDpLayers k d m hk A earlyFail opt G0 l (by omega)
    fintypeBuild (ι := Fin (2 ^ (7 * d + 3)) × Fin (2 ^ (7 * d + 3)) × Fin (2 ^ m))
      (addDpCell k d m l hk hl A earlyFail opt prev.2) prev.1

lemma addDpLayers_spec {k r d m : ℕ} (hk : 0 < k)
    (A : Fin m → Fin k → Bool) (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (opt : Option (Fin k × Bool)) (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (hef_bd : ∀ lw, earlyFail lw < 2 + Fintype.card (Pin315 k) + G0.length)
    (hef_dep : ∀ lw, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (earlyFail lw) 0 ≤ 7 * d + 4)
    (hef_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) lw,
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (earlyFail lw) false = true ↔ ¬ earlyPassCond k r d hk u v ρ lw.1 lw.2))
    (l : ℕ) (hl : l ≤ k) :
    let B := 7 * d + 3
    let N := 2 + Fintype.card (Pin315 k)
    let res := addDpLayers k d m hk A earlyFail opt G0 l hl
    WellFormed N res.1 ∧ Extends G0 res.1 ∧
    res.1.length ≤ G0.length + 3 * l * 4 ^ B * 2 ^ m ∧
    (∀ uvs, res.2 uvs < N + res.1.length) ∧
    (∀ uvs, (mdepths N res.1).getD (res.2 uvs) 0 ≤ 7 * d + 4 + 2 * l) ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) uvs,
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun res.1 (mkBits ρ)).getD (res.2 uvs) false = true ↔
        ¬ HasPath315 k r d m hk u v ρ A opt l hl uvs.1 uvs.2.1 uvs.2.2) := by
  intro B N res
  dsimp only [res]
  induction l with
  | zero =>
    refine ⟨hwf0, extends_rfl G0, by simp [addDpLayers], ?_, ?_, ?_⟩
    · intro uvs; dsimp [addDpLayers]; split_ifs <;> omega
    · intro uvs; dsimp [addDpLayers]; split_ifs
      · rw [mdepths_base G0 0 (by omega)]; omega
      · rw [mdepths_base G0 1 (by omega)]; omega
    · intro u v ρ uvs _; dsimp [addDpLayers, HasPath315]; split_ifs with h
      · rw [mrun_const0]; simp [h]
      · rw [mrun_const1]; simp [h]
  | succ l ih =>
    rcases ih (by omega) with ⟨hwfp, hextp, hlenp, hbdp, hdepp, hevp⟩
    set prev := addDpLayers k d m hk A earlyFail opt G0 l (by omega) with hprev
    let CInv : List MGate → (Fin (2 ^ B) × Fin (2 ^ B) × Fin (2 ^ m)) → ℕ → Prop := fun G uvs w =>
      w < N + G.length ∧ (mdepths N G).getD w 0 ≤ 7 * d + 4 + 2 * (l + 1) ∧
      ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool),
        (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
        ((mrun G (mkBits ρ)).getD w false = true ↔
          ¬ HasPath315 k r d m hk u v ρ A opt (l + 1) hl uvs.1 uvs.2.1 uvs.2.2)
    have hmono : ∀ {G1 G2 : List MGate} {uvs w}, Extends G1 G2 → CInv G1 uvs w → CInv G2 uvs w := by
      intro G1 G2 uvs w he ⟨hlt, hd, hv⟩
      refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len he) N), ?_, ?_⟩
      · rw [mdepths_of_extends he _ hlt]; exact hd
      · intro u v ρ huv; rw [mrun_of_extends he _ _ hlt]; exact hv u v ρ huv
    have hB := fintypeBuild_spec (ι := Fin (2 ^ B) × Fin (2 ^ B) × Fin (2 ^ m)) N 3
      (addDpCell k d m l hk hl A earlyFail opt prev.2) CInv hmono prev.1 hwfp
      (fun G uvs hwf hext => by
        have he0G := extends_trans hextp hext
        have hlenG := extends_len he0G
        have hlenPG := extends_len hext
        exact addDpCell_spec hk hl A earlyFail opt prev.2 G (7 * d + 4 + 2 * l) hwf
          (fun lw => lt_of_lt_of_le (hef_bd lw) (by omega))
          (fun lw => by rw [mdepths_of_extends he0G _ (hef_bd lw)]; exact hef_dep lw)
          (fun u v ρ lw huv => by rw [mrun_of_extends he0G _ _ (hef_bd lw)]; exact hef_val u v ρ lw huv)
          (fun uvs' => lt_of_lt_of_le (hbdp uvs') (by omega))
          (fun uvs' => by rw [mdepths_of_extends hext _ (hbdp uvs')]; exact hdepp uvs')
          (by omega)
          (fun u v ρ uvs' huv => by rw [mrun_of_extends hext _ _ (hbdp uvs')]; exact hevp u v ρ uvs' huv)
          uvs)
    rcases hB with ⟨hwfB, hextB, hlenB, hinvB⟩
    have hcard : Fintype.card (Fin (2 ^ B) × Fin (2 ^ B) × Fin (2 ^ m)) = 4 ^ B * 2 ^ m := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [show (4 : ℕ) ^ B = 2 ^ B * 2 ^ B by rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow]]
      ring
    rw [hcard] at hlenB
    change WellFormed _ _ ∧ Extends G0 _ ∧ _ ≤ G0.length + 3 * (l + 1) * 4 ^ B * 2 ^ m ∧ _
    refine ⟨hwfB, extends_trans hextp hextB, ?_, fun uvs => (hinvB uvs).1,
      fun uvs => (hinvB uvs).2.1, fun u v ρ uvs huv => (hinvB uvs).2.2 u v ρ huv⟩
    calc _ ≤ prev.1.length + 4 ^ B * 2 ^ m * 3 := hlenB
      _ ≤ (G0.length + 3 * l * 4 ^ B * 2 ^ m) + 4 ^ B * 2 ^ m * 3 := Nat.add_le_add_right hlenp _
      _ = G0.length + 3 * (l + 1) * 4 ^ B * 2 ^ m := by ring

noncomputable def addDpScan (k d m : ℕ) (hk : 0 < k)
    (A : Fin m → Fin k → Bool) (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (opt : Option (Fin k × Bool)) (G0 : List MGate) : List MGate × (Fin (2 ^ m) → ℕ) :=
  let B := 7 * d + 3
  let N := 2 + Fintype.card (Pin315 k)
  let rDp := addDpLayers k d m hk A earlyFail opt G0 k le_rfl
  fintypeBuild (ι := Fin (2 ^ m))
    (fun G' s => addTree true N G' (ofFintype (fun u : Fin (2 ^ B) => rDp.2 (u, u, s)))) rDp.1

lemma addDpScan_spec {k r d m : ℕ} (hk : 0 < k)
    (A : Fin m → Fin k → Bool) (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (opt : Option (Fin k × Bool)) (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (hef_bd : ∀ lw, earlyFail lw < 2 + Fintype.card (Pin315 k) + G0.length)
    (hef_dep : ∀ lw, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (earlyFail lw) 0 ≤ 7 * d + 4)
    (hef_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) lw,
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (earlyFail lw) false = true ↔ ¬ earlyPassCond k r d hk u v ρ lw.1 lw.2)) :
    let B := 7 * d + 3
    let N := 2 + Fintype.card (Pin315 k)
    let res := addDpScan k d m hk A earlyFail opt G0
    WellFormed N res.1 ∧ Extends G0 res.1 ∧
    res.1.length ≤ G0.length + (3 * k + 1) * 4 ^ B * 2 ^ m ∧
    (∀ s, res.2 s < N + res.1.length) ∧
    (∀ s, (mdepths N res.1).getD (res.2 s) 0 ≤ 2 * k + 2 * B + 1) ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) (s : Fin (2 ^ m)),
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun res.1 (mkBits ρ)).getD (res.2 s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun l => x (enterIdx k d hk l)) = s ∧
            ∀ l0 b0, opt = some (l0, b0) → x (enterIdx k d hk l0) = b0) := by
  intro B N res
  have hdp := addDpLayers_spec (r := r) hk A earlyFail opt G0 hwf0 hef_bd hef_dep hef_val k le_rfl
  rcases hdp with ⟨hwf1, hext1, hlen1, hbd1, hdep1, hval1⟩
  set rDp := addDpLayers k d m hk A earlyFail opt G0 k le_rfl with hrDp
  let ScanInv : List MGate → Fin (2 ^ m) → ℕ → Prop := fun G s w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ 2 * k + 2 * B + 1 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool),
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G (mkBits ρ)).getD w false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun l => x (enterIdx k d hk l)) = s ∧
            ∀ l0 b0, opt = some (l0, b0) → x (enterIdx k d hk l0) = b0)
  have hmono : ∀ {G1 G2 : List MGate} {s w}, Extends G1 G2 → ScanInv G1 s w → ScanInv G2 s w := by
    intro G1 G2 s w he ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len he) N), ?_, ?_⟩
    · rw [mdepths_of_extends he _ hlt]; exact hd
    · intro u v ρ huv; rw [mrun_of_extends he _ _ hlt]; exact hv u v ρ huv
  have hsc := fintypeBuild_spec (ι := Fin (2 ^ m)) N (2 ^ B)
    (fun G' s => addTree true N G' (ofFintype (fun u : Fin (2 ^ B) => rDp.2 (u, u, s))))
    ScanInv hmono rDp.1 hwf1 (fun G s hwf hext => by
      have hlenG := extends_len hext
      have htr := addTree_spec (P := Pin315 k) true G (ofFintype (fun u : Fin (2 ^ B) => rDp.2 (u, u, s)))
        (7 * d + 4 + 2 * k) hwf
        (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨u_win, rfl⟩; exact lt_of_lt_of_le (hbd1 _) (by omega))
        (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨u_win, rfl⟩; rw [mdepths_of_extends hext _ (hbd1 _)]; exact hdep1 _)
      rcases htr with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
      rw [ofFintype_length, Fintype.card_fin] at hlenT hdepT
      have hclogB : Nat.clog 2 (2 ^ B) ≤ B := clog2_le_of_le_pow (2 ^ B) B le_rfl
      refine ⟨hwfT, hextT, hlenT, hbdT, by dsimp only [N, B] at hdepT hclogB ⊢; omega, fun u v ρ huv => ?_⟩
      rw [hevT (mkBits ρ), evalList_ofFintype_true, ← exists_hasPath_cycle_iff_315 k r d m hk u v ρ A opt s]
      simp only [not_exists]
      apply forall_congr'; intro u_win
      rw [mrun_of_extends hext _ _ (hbd1 _), hval1 u v ρ _ huv])
  rcases hsc with ⟨hwf2, hext2, hlen2, hinv2⟩
  rw [Fintype.card_fin] at hlen2
  have h2pow : 2 ^ B ≤ 4 ^ B := by
    rw [show (4 : ℕ) ^ B = 2 ^ B * 2 ^ B by rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow]]
    exact Nat.le_mul_of_pos_right (2 ^ B) (by positivity)
  have hadd : (3 * k + 1) * 4 ^ B * 2 ^ m = 3 * k * 4 ^ B * 2 ^ m + 2 ^ m * 4 ^ B := by ring
  have hle2 : 2 ^ m * 2 ^ B ≤ 2 ^ m * 4 ^ B := Nat.mul_le_mul_left _ h2pow
  dsimp only [res, addDpScan]; rw [← hrDp]
  have hlen_fin : (fintypeBuild (fun G' s => addTree true N G' (ofFintype (fun u => rDp.2 (u, u, s)))) rDp.1).1.length ≤
      G0.length + (3 * k + 1) * 4 ^ B * 2 ^ m := by
    calc _ ≤ rDp.1.length + 2 ^ m * 2 ^ B := hlen2
      _ ≤ (G0.length + 3 * k * 4 ^ B * 2 ^ m) + 2 ^ m * 2 ^ B := Nat.add_le_add_right hlen1 _
      _ ≤ (G0.length + 3 * k * 4 ^ B * 2 ^ m) + 2 ^ m * 4 ^ B := Nat.add_le_add_left hle2 _
      _ = G0.length + (3 * k + 1) * 4 ^ B * 2 ^ m := by ring
  refine ⟨hwf2, extends_trans hext1 hext2, hlen_fin,
    fun s => (hinv2 s).1, fun s => (hinv2 s).2.1, fun u v ρ s huv => (hinv2 s).2.2 u v ρ huv⟩

noncomputable def addAllScans (k d m : ℕ) (hk : 0 < k)
    (A : Fin m → Fin k → Bool) (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (G : List MGate) : List MGate × (Fin (2 ^ m) → ℕ) × ((Fin k × Bool) → Fin (2 ^ m) → ℕ) :=
  let rEmpty := addDpScan k d m hk A earlyFail none G
  let rExcl := fintypeBuild (ι := Fin k × Bool) (fun G' lb => addDpScan k d m hk A earlyFail (some lb) G') rEmpty.1
  (rExcl.1, rEmpty.2, rExcl.2)

lemma addAllScans_spec {k r d m : ℕ} (hk : 0 < k)
    (A : Fin m → Fin k → Bool) (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (hef_bd : ∀ lw, earlyFail lw < 2 + Fintype.card (Pin315 k) + G0.length)
    (hef_dep : ∀ lw, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (earlyFail lw) 0 ≤ 7 * d + 4)
    (hef_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) lw,
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (earlyFail lw) false = true ↔ ¬ earlyPassCond k r d hk u v ρ lw.1 lw.2)) :
    let B := 7 * d + 3
    let N := 2 + Fintype.card (Pin315 k)
    let dpD := 2 * k + 2 * B + 1
    let res := addAllScans k d m hk A earlyFail G0
    WellFormed N res.1 ∧ Extends G0 res.1 ∧
    res.1.length ≤ G0.length + (2 * k + 1) * (3 * k + 1) * 4 ^ B * 2 ^ m ∧
    (∀ s, res.2.1 s < N + res.1.length) ∧
    (∀ s, (mdepths N res.1).getD (res.2.1 s) 0 ≤ dpD) ∧
    (∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) s, (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun res.1 (mkBits ρ)).getD (res.2.1 s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ, hashVal A (fun l => x (enterIdx k d hk l)) = s)) ∧
    (∀ lb s, res.2.2 lb s < N + res.1.length) ∧
    (∀ lb s, (mdepths N res.1).getD (res.2.2 lb s) 0 ≤ dpD) ∧
    (∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) l b s, (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun res.1 (mkBits ρ)).getD (res.2.2 (l, b) s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun j => x (enterIdx k d hk j)) = s ∧ x (enterIdx k d hk l) = b)) := by
  intro B N dpD res
  have hE := addDpScan_spec (r := r) hk A earlyFail none G0 hwf0 hef_bd hef_dep hef_val
  rcases hE with ⟨hwfE, hextE, hlenE, hbdE, hdepE, hvalE⟩
  set rEmpty := addDpScan k d m hk A earlyFail none G0 with hrE
  let ExclInv : List MGate → Fin k × Bool → (Fin (2 ^ m) → ℕ) → Prop := fun G lb fn =>
    (∀ s, fn s < N + G.length) ∧
    (∀ s, (mdepths N G).getD (fn s) 0 ≤ dpD) ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) (s : Fin (2 ^ m)),
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G (mkBits ρ)).getD (fn s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun j => x (enterIdx k d hk j)) = s ∧ x (enterIdx k d hk lb.1) = lb.2)
  have hmono : ∀ {G1 G2 : List MGate} {lb fn}, Extends G1 G2 → ExclInv G1 lb fn → ExclInv G2 lb fn := by
    intro G1 G2 lb fn he ⟨hbd, hdep, hv⟩
    refine ⟨fun s => lt_of_lt_of_le (hbd s) (Nat.add_le_add_left (extends_len he) N), ?_, ?_⟩
    · intro s; rw [mdepths_of_extends he _ (hbd s)]; exact hdep s
    · intro u v ρ s huv; rw [mrun_of_extends he _ _ (hbd s)]; exact hv u v ρ s huv
  have hX := fintypeBuild_spec (ι := Fin k × Bool) N ((3 * k + 1) * 4 ^ B * 2 ^ m)
    (fun G' lb => addDpScan k d m hk A earlyFail (some lb) G') ExclInv hmono rEmpty.1 hwfE
    (fun G lb hwf hext => by
      have he0 := extends_trans hextE hext
      have hlen0 := extends_len he0
      have hsc := addDpScan_spec (r := r) hk A earlyFail (some lb) G hwf
        (fun lw => lt_of_lt_of_le (hef_bd lw) (by omega))
        (fun lw => by rw [mdepths_of_extends he0 _ (hef_bd lw)]; exact hef_dep lw)
        (fun u v ρ lw huv => by rw [mrun_of_extends he0 _ _ (hef_bd lw)]; exact hef_val u v ρ lw huv)
      refine ⟨hsc.1, hsc.2.1, hsc.2.2.1, hsc.2.2.2.1, hsc.2.2.2.2.1, fun u v ρ s huv => ?_⟩
      rw [hsc.2.2.2.2.2 u v ρ s huv]
      constructor <;> intro h ⟨x, hx, hh, hcond⟩ <;> apply h <;> refine ⟨x, hx, hh, ?_⟩
      · intro l0 b0 hopt; injection hopt with hp; rw [hp] at hcond; exact hcond
      · exact hcond lb.1 lb.2 rfl)
  rcases hX with ⟨hwfX, hextX, hlenX, hinvX⟩
  have hcard : Fintype.card (Fin k × Bool) = 2 * k := by simp [Nat.mul_comm]
  rw [hcard] at hlenX
  have hlenX_le := extends_len hextX
  dsimp only [res, addAllScans]; rw [← hrE]
  refine ⟨hwfX, extends_trans hextE hextX, ?_, ?_, ?_, ?_,
    fun lb s => (hinvX lb).1 s, fun lb s => (hinvX lb).2.1 s,
    fun u v ρ l b s huv => (hinvX (l, b)).2.2 u v ρ s huv⟩
  · calc _ ≤ rEmpty.1.length + 2 * k * ((3 * k + 1) * 4 ^ B * 2 ^ m) := hlenX
      _ ≤ (G0.length + (3 * k + 1) * 4 ^ B * 2 ^ m) + 2 * k * ((3 * k + 1) * 4 ^ B * 2 ^ m) :=
          Nat.add_le_add_right hlenE _
      _ = G0.length + (2 * k + 1) * (3 * k + 1) * 4 ^ B * 2 ^ m := by ring
  · intro s; exact lt_of_lt_of_le (hbdE s) (by omega)
  · intro s; rw [mdepths_of_extends hextX _ (hbdE s)]; exact hdepE s
  · intro u v ρ s huv; rw [mrun_of_extends hextX _ _ (hbdE s), hvalE u v ρ s huv]; simp

-- Hash Ready (bucket singleton check)
noncomputable def addBucketReady (k m : ℕ) (empty : Fin (2 ^ m) → ℕ)
    (excl : (Fin k × Bool) → Fin (2 ^ m) → ℕ) (G : List MGate) (s : Fin (2 ^ m)) : List MGate × ℕ :=
  let N := 2 + Fintype.card (Pin315 k)
  let rOrs := fintypeBuild (ι := Fin k) (fun G' l => addMGate N G' false (excl (l, false) s) (excl (l, true) s)) G
  let rAll := addTree true N rOrs.1 (ofFintype rOrs.2)
  addMGate N rAll.1 false (empty s) rAll.2

noncomputable def addHashReady (k m : ℕ) (empty : Fin (2 ^ m) → ℕ)
    (excl : (Fin k × Bool) → Fin (2 ^ m) → ℕ) (G : List MGate) : List MGate × ℕ :=
  let N := 2 + Fintype.card (Pin315 k)
  let rB := fintypeBuild (addBucketReady k m empty excl) G
  addTree true N rB.1 (ofFintype rB.2)

lemma addBucketReady_spec {k r d m : ℕ} (hk : 0 < k) (A : Fin m → Fin k → Bool)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin k × Bool) → Fin (2 ^ m) → ℕ)
    (G0 : List MGate) (dpD : ℕ)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (he_bd : ∀ s, empty s < 2 + Fintype.card (Pin315 k) + G0.length)
    (he_dep : ∀ s, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (empty s) 0 ≤ dpD)
    (he_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) s, (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (empty s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ, hashVal A (fun l => x (enterIdx k d hk l)) = s))
    (hx_bd : ∀ lb s, excl lb s < 2 + Fintype.card (Pin315 k) + G0.length)
    (hx_dep : ∀ lb s, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (excl lb s) 0 ≤ dpD)
    (hx_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) l b s, (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (excl (l, b) s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun j => x (enterIdx k d hk j)) = s ∧ x (enterIdx k d hk l) = b))
    (s : Fin (2 ^ m)) :
    let N := 2 + Fintype.card (Pin315 k)
    let res := addBucketReady k m empty excl G0 s
    WellFormed N res.1 ∧ Extends G0 res.1 ∧ res.1.length ≤ G0.length + (2 * k + 1) ∧
    res.2 < N + res.1.length ∧ (mdepths N res.1).getD res.2 0 ≤ dpD + 2 + Nat.clog 2 k ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun res.1 (mkBits ρ)).getD res.2 false = true ↔
        ∀ x ∈ candSet315 k r d u v ρ, ∀ y ∈ candSet315 k r d u v ρ,
          hashVal A (fun j => x (enterIdx k d hk j)) = s →
          hashVal A (fun j => y (enterIdx k d hk j)) = s → x = y) := by
  intro N res
  let OInv : List MGate → Fin k → ℕ → Prop := fun G l w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ dpD + 1 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G (mkBits ρ)).getD w false = true ↔
        (¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun j => x (enterIdx k d hk j)) = s ∧ x (enterIdx k d hk l) = false) ∨
        (¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun j => x (enterIdx k d hk j)) = s ∧ x (enterIdx k d hk l) = true))
  have hmono : ∀ {G1 G2 : List MGate} {l w}, Extends G1 G2 → OInv G1 l w → OInv G2 l w := by
    intro G1 G2 l w he ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len he) N), ?_, ?_⟩
    · rw [mdepths_of_extends he _ hlt]; exact hd
    · intro u v ρ huv; rw [mrun_of_extends he _ _ hlt]; exact hv u v ρ huv
  have hO := fintypeBuild_spec (ι := Fin k) N 1
    (fun G' l => addMGate N G' false (excl (l, false) s) (excl (l, true) s))
    OInv hmono G0 hwf0 (fun G l hwf hext => by
      have hlenG := extends_len hext
      have hltF : excl (l, false) s < N + G.length := lt_of_lt_of_le (hx_bd _ _) (by omega)
      have hltT : excl (l, true) s < N + G.length := lt_of_lt_of_le (hx_bd _ _) (by omega)
      refine ⟨addMGate_wf hwf false hltF hltT, addMGate_extends N G false _ _,
        by rw [addMGate_len], addMGate_out_lt N G false _ _, ?_, fun u v ρ huv => ?_⟩
      · rw [addMGate_depth, mdepths_of_extends hext _ (hx_bd _ _), mdepths_of_extends hext _ (hx_bd _ _)]
        have := hx_dep (l, false) s; have := hx_dep (l, true) s; omega
      · rw [addMGate_val]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
        rw [mrun_of_extends hext _ _ (hx_bd _ _), mrun_of_extends hext _ _ (hx_bd _ _),
          hx_val u v ρ l false s huv, hx_val u v ρ l true s huv])
  rcases hO with ⟨hwfO, hextO, hlenO, hinvO⟩
  set rOrs := fintypeBuild (ι := Fin k) (fun G' l => addMGate N G' false (excl (l, false) s) (excl (l, true) s)) G0 with hrO
  rw [Fintype.card_fin, mul_one] at hlenO
  have hT := addTree_spec (P := Pin315 k) true rOrs.1 (ofFintype rOrs.2) (dpD + 1) hwfO
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨l, rfl⟩; exact (hinvO l).1)
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨l, rfl⟩; exact (hinvO l).2.1)
  rcases hT with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
  rw [ofFintype_length, Fintype.card_fin] at hlenT hdepT
  have heOT := extends_trans hextO hextT
  have hlenOT := extends_len heOT
  have hltE : empty s < N + (addTree true N rOrs.1 (ofFintype rOrs.2)).1.length :=
    lt_of_lt_of_le (he_bd s) (by dsimp only [N] at hlenOT ⊢; omega)
  have hwfF := addMGate_wf hwfT false hltE hbdT
  have heF := addMGate_extends N (addTree true N rOrs.1 (ofFintype rOrs.2)).1 false (empty s)
    (addTree true N rOrs.1 (ofFintype rOrs.2)).2
  have hlenF := addMGate_len N (addTree true N rOrs.1 (ofFintype rOrs.2)).1 false (empty s)
    (addTree true N rOrs.1 (ofFintype rOrs.2)).2
  have hbdF := addMGate_out_lt N (addTree true N rOrs.1 (ofFintype rOrs.2)).1 false (empty s)
    (addTree true N rOrs.1 (ofFintype rOrs.2)).2
  dsimp only [res, addBucketReady]; rw [← hrO]
  refine ⟨hwfF, extends_trans heOT heF, by dsimp only [N] at hlenF hlenO hlenT ⊢; omega, hbdF, ?_, fun u v ρ huv => ?_⟩
  · rw [addMGate_depth, mdepths_of_extends heOT _ (he_bd s)]
    dsimp only [N] at hdepT ⊢; have := he_dep s; omega
  · rw [addMGate_val]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
    rw [mrun_of_extends heOT _ _ (he_bd s), he_val u v ρ s huv, hevT (mkBits ρ), evalList_ofFintype_true]
    simp only [fun l => (hinvO l).2.2 u v ρ huv]
    constructor
    · rintro (hemp | hall) x hx y hy hxs hys
      · exact False.elim (hemp ⟨x, hx, hxs⟩)
      · apply funext; intro i
        rw [← enterIdx_inv k d hk i]
        rcases hall (enterInv k d hk i) with hnoF | hnoT
        · cases hxi : x (enterIdx k d hk (enterInv k d hk i)) <;> cases hyi : y (enterIdx k d hk (enterInv k d hk i))
          · rfl
          · exact False.elim (hnoF ⟨x, hx, hxs, hxi⟩)
          · exact False.elim (hnoF ⟨y, hy, hys, hyi⟩)
          · rfl
        · cases hxi : x (enterIdx k d hk (enterInv k d hk i)) <;> cases hyi : y (enterIdx k d hk (enterInv k d hk i))
          · rfl
          · exact False.elim (hnoT ⟨y, hy, hys, hyi⟩)
          · exact False.elim (hnoT ⟨x, hx, hxs, hxi⟩)
          · rfl
    · intro hinj
      by_cases hex : ∃ x ∈ candSet315 k r d u v ρ, hashVal A (fun j => x (enterIdx k d hk j)) = s
      · right; intro l
        rcases hex with ⟨x, hx, hxs⟩
        cases hxi : x (enterIdx k d hk l)
        · right; rintro ⟨y, hy, hys, hyi⟩
          have heq := hinj x hx y hy hxs hys
          rw [← heq, hxi] at hyi; exact Bool.noConfusion hyi
        · left; rintro ⟨y, hy, hys, hyi⟩
          have heq := hinj x hx y hy hxs hys
          rw [← heq, hxi] at hyi; exact Bool.noConfusion hyi
      · exact Or.inl hex

lemma addHashReady_spec {k r d m : ℕ} (hk : 0 < k) (A : Fin m → Fin k → Bool)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin k × Bool) → Fin (2 ^ m) → ℕ)
    (G0 : List MGate) (dpD : ℕ)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (he_bd : ∀ s, empty s < 2 + Fintype.card (Pin315 k) + G0.length)
    (he_dep : ∀ s, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (empty s) 0 ≤ dpD)
    (he_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) s, (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (empty s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ, hashVal A (fun l => x (enterIdx k d hk l)) = s))
    (hx_bd : ∀ lb s, excl lb s < 2 + Fintype.card (Pin315 k) + G0.length)
    (hx_dep : ∀ lb s, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (excl lb s) 0 ≤ dpD)
    (hx_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) l b s, (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (excl (l, b) s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun j => x (enterIdx k d hk j)) = s ∧ x (enterIdx k d hk l) = b)) :
    let N := 2 + Fintype.card (Pin315 k)
    let res := addHashReady k m empty excl G0
    WellFormed N res.1 ∧ Extends G0 res.1 ∧ res.1.length ≤ G0.length + (2 * k + 2) * 2 ^ m ∧
    res.2 < N + res.1.length ∧ (mdepths N res.1).getD res.2 0 ≤ dpD + 2 + Nat.clog 2 k + m ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun res.1 (mkBits ρ)).getD res.2 false = true ↔
        ∀ x ∈ candSet315 k r d u v ρ, ∀ y ∈ candSet315 k r d u v ρ,
          hashVal A (fun j => x (enterIdx k d hk j)) =
            hashVal A (fun j => y (enterIdx k d hk j)) → x = y) := by
  intro N res
  let BInv : List MGate → Fin (2 ^ m) → ℕ → Prop := fun G s w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ dpD + 2 + Nat.clog 2 k ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G (mkBits ρ)).getD w false = true ↔
        ∀ x ∈ candSet315 k r d u v ρ, ∀ y ∈ candSet315 k r d u v ρ,
          hashVal A (fun j => x (enterIdx k d hk j)) = s →
          hashVal A (fun j => y (enterIdx k d hk j)) = s → x = y)
  have hmono : ∀ {G1 G2 : List MGate} {s w}, Extends G1 G2 → BInv G1 s w → BInv G2 s w := by
    intro G1 G2 s w he ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len he) N), ?_, ?_⟩
    · rw [mdepths_of_extends he _ hlt]; exact hd
    · intro u v ρ huv; rw [mrun_of_extends he _ _ hlt]; exact hv u v ρ huv
  have hB := fintypeBuild_spec (ι := Fin (2 ^ m)) N (2 * k + 1)
    (addBucketReady k m empty excl) BInv hmono G0 hwf0 (fun G s hwf hext => by
      have hlenG := extends_len hext
      exact addBucketReady_spec (r := r) (d := d) hk A empty excl G dpD hwf
        (fun s' => lt_of_lt_of_le (he_bd s') (by omega))
        (fun s' => by rw [mdepths_of_extends hext _ (he_bd s')]; exact he_dep s')
        (fun u v ρ s' huv => by rw [mrun_of_extends hext _ _ (he_bd s')]; exact he_val u v ρ s' huv)
        (fun lb s' => lt_of_lt_of_le (hx_bd lb s') (by omega))
        (fun lb s' => by rw [mdepths_of_extends hext _ (hx_bd lb s')]; exact hx_dep lb s')
        (fun u v ρ l b s' huv => by rw [mrun_of_extends hext _ _ (hx_bd (l, b) s')]; exact hx_val u v ρ l b s' huv)
        s)
  rcases hB with ⟨hwfB, hextB, hlenB, hinvB⟩
  set rB := fintypeBuild (addBucketReady k m empty excl) G0 with hrB
  have hT := addTree_spec (P := Pin315 k) true rB.1 (ofFintype rB.2) (dpD + 2 + Nat.clog 2 k) hwfB
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨s, rfl⟩; exact (hinvB s).1)
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨s, rfl⟩; exact (hinvB s).2.1)
  rcases hT with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
  rw [ofFintype_length, Fintype.card_fin] at hlenT hdepT
  rw [Fintype.card_fin] at hlenB
  have hcl : Nat.clog 2 (2 ^ m) ≤ m := clog2_le_of_le_pow (2 ^ m) m le_rfl
  dsimp only [res, addHashReady]; rw [← hrB]
  refine ⟨hwfT, extends_trans hextB hextT, ?_, hbdT, by dsimp only [N] at hdepT ⊢; omega, fun u v ρ huv => ?_⟩
  · have : (2 * k + 2) * 2 ^ m = 2 ^ m * (2 * k + 1) + 2 ^ m := by ring
    omega
  · rw [hevT (mkBits ρ), evalList_ofFintype_true]
    constructor
    · intro hall x hx y hy hxy
      exact ((hinvB _).2.2 u v ρ huv).mp (hall _) x hx y hy rfl hxy.symm
    · intro hinj s
      rw [(hinvB s).2.2 u v ρ huv]
      intro x hx y hy hxs hys
      exact hinj x hx y hy (hxs.trans hys.symm)

-- Late global evaluation of `first r` and `second r` per bucket
noncomputable def drGlobalRound (N k stepDist keyShift constIdx : ℕ) (hk : 0 < k)
    (G : List MGate) (key st : Fin k → DRWire) : List MGate × (Fin k → DRWire) :=
  let rotWire (s : ℕ) (w : Fin k → DRWire) (i : Fin k) : DRWire :=
    w ⟨(i.val + (k - s % k)) % k, Nat.mod_lt _ hk⟩
  let rAdj := fintypeBuild (ι := Fin k) (fun G' i =>
    let x1 := drXor N G' (rotWire stepDist st i) (rotWire (k - stepDist) st i)
    drXor N x1.1 (st i) x1.2) G
  fintypeBuild (ι := Fin k) (fun G' i =>
    let a0 := rAdj.2 i
    let a1 := rAdj.2 ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
    let a2 := rAdj.2 ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
    let rnd := drAnd N G' (drNot a1) a2
    let rst := drXor N rnd.1 a0 rnd.2
    let rxk := drXor N rst.1 rst.2 (rotWire keyShift key i)
    (rxk.1, drXorConst ((constFn k constIdx).testBit i.val) rxk.2)) rAdj.1

lemma drGlobalRound_spec {P : Type} [Fintype P] {k stepDist keyShift constIdx : ℕ} (hk : 0 < k)
    (G0 : List MGate) (dKey dSt : ℕ) (hle : dKey ≤ dSt + 7)
    (key st : Fin k → DRWire)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hbk : ∀ i, DRBounds (2 + Fintype.card P) G0 dKey (key i))
    (hbs : ∀ i, DRBounds (2 + Fintype.card P) G0 dSt (st i)) :
    let N := 2 + Fintype.card P
    let res := drGlobalRound N k stepDist keyShift constIdx hk G0 key st
    WellFormed N res.1 ∧ Extends G0 res.1 ∧ res.1.length ≤ G0.length + 26 * k ∧
    (∀ i, DRBounds N res.1 (dSt + 9) (res.2 i)) ∧
    (∀ (a : P → Bool) (keyW stW : ℕ), keyW < 2 ^ k → stW < 2 ^ k →
      (∀ i : Fin k, DRSound G0 a (key i) (keyW.testBit i.val)) →
      (∀ i : Fin k, DRSound G0 a (st i) (stW.testBit i.val)) →
      ∀ i : Fin k, DRSound res.1 a (res.2 i)
        ((stepFn k (stW ^^^ rotFn k stepDist stW ^^^ rotFn k (k - stepDist) stW) ^^^
          rotFn k keyShift keyW ^^^ constFn k constIdx).testBit i.val)) ∧
    (∀ (a : P → Bool) (keyW stW : ℕ), keyW < 2 ^ k → stW < 2 ^ k →
      (∀ i : Fin k, DRExact G0 a (key i) (keyW.testBit i.val)) →
      (∀ i : Fin k, DRExact G0 a (st i) (stW.testBit i.val)) →
      ∀ i : Fin k, DRExact res.1 a (res.2 i)
        ((stepFn k (stW ^^^ rotFn k stepDist stW ^^^ rotFn k (k - stepDist) stW) ^^^
          rotFn k keyShift keyW ^^^ constFn k constIdx).testBit i.val)) := by
  intro N res
  let rotWire (s : ℕ) (w : Fin k → DRWire) (i : Fin k) : DRWire :=
    w ⟨(i.val + (k - s % k)) % k, Nat.mod_lt _ hk⟩
  let adjVal (stW : ℕ) (i : Fin k) : Bool :=
    (stW ^^^ rotFn k stepDist stW ^^^ rotFn k (k - stepDist) stW).testBit i.val
  let AdjInv : List MGate → Fin k → DRWire → Prop := fun G i w =>
    DRBounds N G (dSt + 4) w ∧
    (∀ (a : P → Bool) (stW : ℕ), stW < 2 ^ k →
      (∀ j, DRSound G0 a (st j) (stW.testBit j.val)) → DRSound G a w (adjVal stW i)) ∧
    (∀ (a : P → Bool) (stW : ℕ), stW < 2 ^ k →
      (∀ j, DRExact G0 a (st j) (stW.testBit j.val)) → DRExact G a w (adjVal stW i))
  have hmonoA : ∀ {G1 G2 : List MGate} {i w}, Extends G1 G2 → AdjInv G1 i w → AdjInv G2 i w := by
    intro G1 G2 i w he ⟨hb, hs, hx⟩
    exact ⟨drBounds_of_extends he hb,
      fun a stW hst hs0 => drSound_of_extends he hb.1 hb.2.1 (hs a stW hst hs0),
      fun a stW hst hx0 => drExact_of_extends he hb.1 hb.2.1 (hx a stW hst hx0)⟩
  have hAdj := fintypeBuild_spec (ι := Fin k) N 12
    (fun G' i =>
      let x1 := drXor N G' (rotWire stepDist st i) (rotWire (k - stepDist) st i)
      drXor N x1.1 (st i) x1.2)
    AdjInv hmonoA G0 hwf0 (fun G i hwf hext => by
      have hrl := drBounds_of_extends hext (hbs ⟨(i.val + (k - stepDist % k)) % k, Nat.mod_lt _ hk⟩)
      have hrr := drBounds_of_extends hext (hbs ⟨(i.val + (k - (k - stepDist) % k)) % k, Nat.mod_lt _ hk⟩)
      have hx1 := drXor_spec G dSt dSt (rotWire stepDist st i) (rotWire (k - stepDist) st i) hwf hrl hrr
      rcases hx1 with ⟨hwf1, he1, hl1, hb1, hs1, hx1e⟩
      have hrc := drBounds_of_extends (extends_trans hext he1) (hbs i)
      have hx2 := drXor_spec _ dSt (dSt + 2) (st i) _ hwf1 hrc (drBounds_mono (by omega) hb1)
      rcases hx2 with ⟨hwf2, he2, hl2, hb2, hs2, hx2e⟩
      refine ⟨hwf2, extends_trans he1 he2, by dsimp only [N] at hl1 hl2 ⊢; omega, drBounds_mono (by omega) hb2, ?_, ?_⟩
      · intro a stW hlt hs0
        have hlS := drSound_of_extends hext (hbs _).1 (hbs _).2.1 (hs0 ⟨(i.val + (k - stepDist % k)) % k, Nat.mod_lt _ hk⟩)
        have hrS := drSound_of_extends hext (hbs _).1 (hbs _).2.1 (hs0 ⟨(i.val + (k - (k - stepDist) % k)) % k, Nat.mod_lt _ hk⟩)
        have hcS := drSound_of_extends (extends_trans hext he1) (hbs i).1 (hbs i).2.1 (hs0 i)
        have h1S := hs1 a _ _ hlS hrS
        have h2S := hs2 a _ _ hcS h1S
        have heqv : Bool.xor (stW.testBit i.val) (Bool.xor
            (stW.testBit ((i.val + (k - stepDist % k)) % k))
            (stW.testBit ((i.val + (k - (k - stepDist) % k)) % k))) = adjVal stW i := by
          dsimp only [adjVal]; rw [Nat.testBit_xor, Nat.testBit_xor,
            rotFn_testBit hk stepDist stW _ hlt i.isLt, rotFn_testBit hk (k - stepDist) stW _ hlt i.isLt]
          cases stW.testBit i.val <;> cases stW.testBit ((i.val + (k - stepDist % k)) % k) <;>
            cases stW.testBit ((i.val + (k - (k - stepDist) % k)) % k) <;> decide
        rw [heqv] at h2S; exact h2S
      · intro a stW hlt hx0
        have hlX := drExact_of_extends hext (hbs _).1 (hbs _).2.1 (hx0 ⟨(i.val + (k - stepDist % k)) % k, Nat.mod_lt _ hk⟩)
        have hrX := drExact_of_extends hext (hbs _).1 (hbs _).2.1 (hx0 ⟨(i.val + (k - (k - stepDist) % k)) % k, Nat.mod_lt _ hk⟩)
        have hcX := drExact_of_extends (extends_trans hext he1) (hbs i).1 (hbs i).2.1 (hx0 i)
        have h1X := hx1e a _ _ hlX hrX
        have h2X := hx2e a _ _ hcX h1X
        have heqv : Bool.xor (stW.testBit i.val) (Bool.xor
            (stW.testBit ((i.val + (k - stepDist % k)) % k))
            (stW.testBit ((i.val + (k - (k - stepDist) % k)) % k))) = adjVal stW i := by
          dsimp only [adjVal]; rw [Nat.testBit_xor, Nat.testBit_xor,
            rotFn_testBit hk stepDist stW _ hlt i.isLt, rotFn_testBit hk (k - stepDist) stW _ hlt i.isLt]
          cases stW.testBit i.val <;> cases stW.testBit ((i.val + (k - stepDist % k)) % k) <;>
            cases stW.testBit ((i.val + (k - (k - stepDist) % k)) % k) <;> decide
        rw [heqv] at h2X; exact h2X)
  rcases hAdj with ⟨hwfA, hextA, hlenA, hinvA⟩
  set rAdj := fintypeBuild (ι := Fin k) (fun G' i =>
    let x1 := drXor N G' (rotWire stepDist st i) (rotWire (k - stepDist) st i)
    drXor N x1.1 (st i) x1.2) G0 with hrAdj
  let OutInv : List MGate → Fin k → DRWire → Prop := fun G i w =>
    DRBounds N G (dSt + 9) w ∧
    (∀ (a : P → Bool) (keyW stW : ℕ), keyW < 2 ^ k → stW < 2 ^ k →
      (∀ j, DRSound G0 a (key j) (keyW.testBit j.val)) →
      (∀ j, DRSound G0 a (st j) (stW.testBit j.val)) →
      DRSound G a w ((stepFn k (stW ^^^ rotFn k stepDist stW ^^^ rotFn k (k - stepDist) stW) ^^^
        rotFn k keyShift keyW ^^^ constFn k constIdx).testBit i.val)) ∧
    (∀ (a : P → Bool) (keyW stW : ℕ), keyW < 2 ^ k → stW < 2 ^ k →
      (∀ j, DRExact G0 a (key j) (keyW.testBit j.val)) →
      (∀ j, DRExact G0 a (st j) (stW.testBit j.val)) →
      DRExact G a w ((stepFn k (stW ^^^ rotFn k stepDist stW ^^^ rotFn k (k - stepDist) stW) ^^^
        rotFn k keyShift keyW ^^^ constFn k constIdx).testBit i.val))
  have hmonoO : ∀ {G1 G2 : List MGate} {i w}, Extends G1 G2 → OutInv G1 i w → OutInv G2 i w := by
    intro G1 G2 i w he ⟨hb, hs, hx⟩
    exact ⟨drBounds_of_extends he hb,
      fun a kw sw hkw hsw hk0 hs0 => drSound_of_extends he hb.1 hb.2.1 (hs a kw sw hkw hsw hk0 hs0),
      fun a kw sw hkw hsw hk0 hx0 => drExact_of_extends he hb.1 hb.2.1 (hx a kw sw hkw hsw hk0 hx0)⟩
  have hOut := fintypeBuild_spec (ι := Fin k) N 14
    (fun G' i =>
      let a0 := rAdj.2 i
      let a1 := rAdj.2 ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
      let a2 := rAdj.2 ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
      let rnd := drAnd N G' (drNot a1) a2
      let rst := drXor N rnd.1 a0 rnd.2
      let rxk := drXor N rst.1 rst.2 (rotWire keyShift key i)
      (rxk.1, drXorConst ((constFn k constIdx).testBit i.val) rxk.2))
    OutInv hmonoO rAdj.1 hwfA (fun G i hwf hext => by
      have ha1 := drBounds_not (drBounds_of_extends hext (hinvA ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩).1)
      have ha2 := drBounds_of_extends hext (hinvA ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩).1
      have hnd := drAnd_spec G (dSt + 4) (dSt + 4) _ _ hwf ha1 ha2
      rcases hnd with ⟨hwf1, he1, hl1, hb1, hs1, hx1e⟩
      have ha0 := drBounds_of_extends (extends_trans hext he1) (hinvA i).1
      have hrst := drXor_spec _ (dSt + 4) (dSt + 5) _ _ hwf1 ha0 (drBounds_mono (by omega) hb1)
      rcases hrst with ⟨hwf2, he2, hl2, hb2, hs2, hx2e⟩
      have hrk := drBounds_mono hle (drBounds_of_extends (extends_trans (extends_trans hextA hext) (extends_trans he1 he2))
        (hbk ⟨(i.val + (k - keyShift % k)) % k, Nat.mod_lt _ hk⟩))
      have hrxk := drXor_spec _ (dSt + 7) (dSt + 7) _ _ hwf2 (drBounds_mono (by omega) hb2) hrk
      rcases hrxk with ⟨hwf3, he3, hl3, hb3, hs3, hx3e⟩
      refine ⟨hwf3, extends_trans he1 (extends_trans he2 he3), by dsimp only [rotWire] at hl3 ⊢; dsimp only [N] at hl1 hl2 hl3 ⊢; omega, drBounds_mono (by omega) (drBounds_xorConst _ hb3), ?_, ?_⟩
      · intro a kw sw hkw hsw hk0 hs0
        have hS1 := (hinvA ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩).2.1 a sw hsw hs0
        have hS2 := (hinvA ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩).2.1 a sw hsw hs0
        have hS0 := (hinvA i).2.1 a sw hsw hs0
        have hSnd := hs1 a _ _ (drSound_not (drSound_of_extends hext (hinvA _).1.1 (hinvA _).1.2.1 hS1))
          (drSound_of_extends hext (hinvA _).1.1 (hinvA _).1.2.1 hS2)
        have hSst := hs2 a _ _ (drSound_of_extends (extends_trans hext he1) (hinvA _).1.1 (hinvA _).1.2.1 hS0) hSnd
        have hSk := drSound_of_extends (extends_trans (extends_trans hextA hext) (extends_trans he1 he2))
          (hbk ⟨(i.val + (k - keyShift % k)) % k, Nat.mod_lt _ hk⟩).1
          (hbk ⟨(i.val + (k - keyShift % k)) % k, Nat.mod_lt _ hk⟩).2.1
          (hk0 ⟨(i.val + (k - keyShift % k)) % k, Nat.mod_lt _ hk⟩)
        have hSxk := drSound_xorConst (c := (constFn k constIdx).testBit i.val) (hs3 a _ _ hSst hSk)
        rw [Nat.testBit_xor, Nat.testBit_xor, stepFn_testBit k _ _ i.isLt,
          rotFn_testBit hk keyShift kw _ hkw i.isLt]
        exact hSxk
      · intro a kw sw hkw hsw hk0 hx0
        have hX1 := (hinvA ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩).2.2 a sw hsw hx0
        have hX2 := (hinvA ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩).2.2 a sw hsw hx0
        have hX0 := (hinvA i).2.2 a sw hsw hx0
        have hXnd := hx1e a _ _ (drExact_not (drExact_of_extends hext (hinvA _).1.1 (hinvA _).1.2.1 hX1))
          (drExact_of_extends hext (hinvA _).1.1 (hinvA _).1.2.1 hX2)
        have hXst := hx2e a _ _ (drExact_of_extends (extends_trans hext he1) (hinvA _).1.1 (hinvA _).1.2.1 hX0) hXnd
        have hXk := drExact_of_extends (extends_trans (extends_trans hextA hext) (extends_trans he1 he2))
          (hbk ⟨(i.val + (k - keyShift % k)) % k, Nat.mod_lt _ hk⟩).1
          (hbk ⟨(i.val + (k - keyShift % k)) % k, Nat.mod_lt _ hk⟩).2.1
          (hk0 ⟨(i.val + (k - keyShift % k)) % k, Nat.mod_lt _ hk⟩)
        have hXxk := drExact_xorConst (c := (constFn k constIdx).testBit i.val) (hx3e a _ _ hXst hXk)
        rw [Nat.testBit_xor, Nat.testBit_xor, stepFn_testBit k _ _ i.isLt,
          rotFn_testBit hk keyShift kw _ hkw i.isLt]
        exact hXxk)
  rcases hOut with ⟨hwfO, hextO, hlenO, hinvO⟩
  rw [Fintype.card_fin] at hlenA hlenO
  dsimp only [res, drGlobalRound]; rw [← hrAdj]
  refine ⟨hwfO, extends_trans hextA hextO, ?_, fun i => (hinvO i).1, ?_, ?_⟩
  · calc _ ≤ rAdj.1.length + k * 14 := hlenO
      _ ≤ (G0.length + k * 12) + k * 14 := Nat.add_le_add_right hlenA _
      _ = G0.length + 26 * k := by ring
  · intro a kw sw hkw hsw hk0 hs0 i; exact (hinvO i).2.1 a kw sw hkw hsw hk0 hs0
  · intro a kw sw hkw hsw hk0 hx0 i; exact (hinvO i).2.2 a kw sw hkw hsw hk0 hx0

noncomputable def drGlobalEval (N k r : ℕ) (isSecond : Bool) (hk : 0 < k)
    (key name : Fin k → DRWire) : ℕ → List MGate → List MGate × (Fin k → DRWire)
  | 0, G =>
    let rotKey (i : Fin k) : DRWire :=
      key ⟨(i.val + (k - (if isSecond then 3 else 1) % k)) % k, Nat.mod_lt _ hk⟩
    fintypeBuild (ι := Fin k) (fun G' i => drXor N G' (rotKey i) (name i)) G
  | t + 1, G =>
    let prev := drGlobalEval N k r isSecond hk key name t G
    let stepDist := if isSecond then 2 else 1
    let keyShift := if isSecond then 3 * (t + 1) + 1 else 2 * t
    let constIdx := if isSecond then r + (t + 1) else t + 1
    drGlobalRound N k stepDist keyShift constIdx hk prev.1 key prev.2

lemma drGlobalEval_spec {P : Type} [Fintype P] {k r : ℕ} (isSecond : Bool) (hk : 0 < k)
    (G0 : List MGate) (dpD : ℕ) (key name : Fin k → DRWire)
    (hwf0 : WellFormed (2 + Fintype.card P) G0)
    (hbk : ∀ i, DRBounds (2 + Fintype.card P) G0 dpD (key i))
    (hbn : ∀ i, DRBounds (2 + Fintype.card P) G0 dpD (name i)) (t : ℕ) :
    let N := 2 + Fintype.card P
    let res := drGlobalEval N k r isSecond hk key name t G0
    WellFormed N res.1 ∧ Extends G0 res.1 ∧ res.1.length ≤ G0.length + (6 + 26 * t) * k ∧
    (∀ i, DRBounds N res.1 (dpD + 2 + 9 * t) (res.2 i)) ∧
    ∀ (a : P → Bool) (kw nw : ℕ), kw < 2 ^ k → nw < 2 ^ k →
      ((∀ i, DRSound G0 a (key i) (kw.testBit i.val)) → (∀ i, DRSound G0 a (name i) (nw.testBit i.val)) →
        ∀ i, DRSound res.1 a (res.2 i) ((if isSecond then secondFn k r t kw nw else firstFn k t kw nw).testBit i.val)) ∧
      ((∀ i, DRExact G0 a (key i) (kw.testBit i.val)) → (∀ i, DRExact G0 a (name i) (nw.testBit i.val)) →
        ∀ i, DRExact res.1 a (res.2 i) ((if isSecond then secondFn k r t kw nw else firstFn k t kw nw).testBit i.val)) := by
  intro N res
  dsimp only [res]
  induction t with
  | zero =>
    let rotKey (i : Fin k) : DRWire :=
      key ⟨(i.val + (k - (if isSecond then 3 else 1) % k)) % k, Nat.mod_lt _ hk⟩
    let ZInv : List MGate → Fin k → DRWire → Prop := fun G i w =>
      DRBounds N G (dpD + 2) w ∧
      (∀ (a : P → Bool) (kw nw : ℕ), kw < 2 ^ k → nw < 2 ^ k →
        (∀ j, DRSound G0 a (key j) (kw.testBit j.val)) → (∀ j, DRSound G0 a (name j) (nw.testBit j.val)) →
        DRSound G a w ((if isSecond then secondFn k r 0 kw nw else firstFn k 0 kw nw).testBit i.val)) ∧
      (∀ (a : P → Bool) (kw nw : ℕ), kw < 2 ^ k → nw < 2 ^ k →
        (∀ j, DRExact G0 a (key j) (kw.testBit j.val)) → (∀ j, DRExact G0 a (name j) (nw.testBit j.val)) →
        DRExact G a w ((if isSecond then secondFn k r 0 kw nw else firstFn k 0 kw nw).testBit i.val))
    have hmono : ∀ {G1 G2 : List MGate} {i w}, Extends G1 G2 → ZInv G1 i w → ZInv G2 i w := by
      intro G1 G2 i w he ⟨hb, hs, hx⟩
      exact ⟨drBounds_of_extends he hb,
        fun a kw nw hkw hnw hs1 hs2 => drSound_of_extends he hb.1 hb.2.1 (hs a kw nw hkw hnw hs1 hs2),
        fun a kw nw hkw hnw hx1 hx2 => drExact_of_extends he hb.1 hb.2.1 (hx a kw nw hkw hnw hx1 hx2)⟩
    have hZ := fintypeBuild_spec (ι := Fin k) N 6
      (fun G' i => drXor N G' (rotKey i) (name i)) ZInv hmono G0 hwf0 (fun G i hwf hext => by
        have hx := drXor_spec G dpD dpD (rotKey i) (name i) hwf
          (drBounds_of_extends hext (hbk _)) (drBounds_of_extends hext (hbn i))
        rcases hx with ⟨hwf1, he1, hl1, hb1, hs1, hx1e⟩
        refine ⟨hwf1, he1, hl1, drBounds_mono (by omega) hb1, ?_, ?_⟩
        · intro a kw nw hkw hnw hks hns
          have hS := hs1 a _ _ (drSound_of_extends hext (hbk _).1 (hbk _).2.1 (hks _))
            (drSound_of_extends hext (hbn i).1 (hbn i).2.1 (hns i))
          cases isSecond <;> simp [firstFn, secondFn, Nat.testBit_xor, rotFn_testBit hk _ kw _ hkw i.isLt] at hS ⊢ <;> exact hS
        · intro a kw nw hkw hnw hkx hnx
          have hX := hx1e a _ _ (drExact_of_extends hext (hbk _).1 (hbk _).2.1 (hkx _))
            (drExact_of_extends hext (hbn i).1 (hbn i).2.1 (hnx i))
          cases isSecond <;> simp [firstFn, secondFn, Nat.testBit_xor, rotFn_testBit hk _ kw _ hkw i.isLt] at hX ⊢ <;> exact hX)
    rcases hZ with ⟨hwfZ, hextZ, hlenZ, hinvZ⟩
    rw [Fintype.card_fin] at hlenZ
    refine ⟨hwfZ, hextZ, by simp only [Nat.mul_zero, Nat.add_zero]; rw [Nat.mul_comm] at hlenZ; exact hlenZ,
      fun i => (hinvZ i).1, fun a kw nw hkw hnw =>
      ⟨fun hs1 hs2 i => (hinvZ i).2.1 a kw nw hkw hnw hs1 hs2,
       fun hx1 hx2 i => (hinvZ i).2.2 a kw nw hkw hnw hx1 hx2⟩⟩
  | succ t ih =>
    rcases ih with ⟨hwfp, hextp, hlenp, hbdp, hevp⟩
    set prev := drGlobalEval N k r isSecond hk key name t G0 with hprev
    have hbk_p : ∀ i, DRBounds N prev.1 dpD (key i) := fun i => drBounds_of_extends hextp (hbk i)
    have hR := drGlobalRound_spec (stepDist := if isSecond then 2 else 1)
      (keyShift := if isSecond then 3 * (t + 1) + 1 else 2 * t)
      (constIdx := if isSecond then r + (t + 1) else t + 1)
      hk prev.1 dpD (dpD + 2 + 9 * t) (by omega) key prev.2 hwfp hbk_p hbdp
    rcases hR with ⟨hwfR, hextR, hlenR, hbdR, hsR, hxR⟩
    refine ⟨hwfR, extends_trans hextp hextR, ?_, fun i => drBounds_mono (by omega) (hbdR i), ?_⟩
    · change (drGlobalRound N k (if isSecond then 2 else 1) (if isSecond then 3 * (t + 1) + 1 else 2 * t)
          (if isSecond then r + (t + 1) else t + 1) hk prev.1 key prev.2).1.length ≤ G0.length + (6 + 26 * (t + 1)) * k
      calc _ ≤ prev.1.length + 26 * k := hlenR
        _ ≤ (G0.length + (6 + 26 * t) * k) + 26 * k := Nat.add_le_add_right hlenp _
        _ = G0.length + (6 + 26 * (t + 1)) * k := by ring
    · intro a kw nw hkw hnw
      have hevp_a := hevp a kw nw hkw hnw
      constructor
      · intro hs1 hs2 i
        have hlt_prev : (if isSecond then secondFn k r t kw nw else firstFn k t kw nw) < 2 ^ k := by
          cases isSecond
          · exact firstFn_lt hk t hkw hnw
          · exact secondFn_lt hk r t hkw hnw
        have hS := hsR a kw _ hkw hlt_prev (fun j => drSound_of_extends hextp (hbk j).1 (hbk j).2.1 (hs1 j))
          (hevp_a.1 hs1 hs2) i
        cases isSecond <;> simp only [Bool.false_eq_true, ↓reduceIte, firstFn, secondFn,
          List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hS ⊢ <;> exact hS
      · intro hx1 hx2 i
        have hlt_prev : (if isSecond then secondFn k r t kw nw else firstFn k t kw nw) < 2 ^ k := by
          cases isSecond
          · exact firstFn_lt hk t hkw hnw
          · exact secondFn_lt hk r t hkw hnw
        have hX := hxR a kw _ hkw hlt_prev (fun j => drExact_of_extends hextp (hbk j).1 (hbk j).2.1 (hx1 j))
          (hevp_a.2 hx1 hx2) i
        cases isSecond <;> simp only [Bool.false_eq_true, ↓reduceIte, firstFn, secondFn,
          List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hX ⊢ <;> exact hX

noncomputable def addBucketFail (k r d m : ℕ) (hk : 0 < k)
    (empty : Fin (2 ^ m) → ℕ) (excl : (Fin k × Bool) → Fin (2 ^ m) → ℕ)
    (G : List MGate) (s : Fin (2 ^ m)) : List MGate × ℕ :=
  let N := 2 + Fintype.card (Pin315 k)
  let xRail : Fin k → DRWire := fun i => (excl (enterInv k d hk i, true) s, excl (enterInv k d hk i, false) s)
  let uRail : Fin k → DRWire := fun i => (pinWire k ((0, i), false), pinWire k ((0, i), true))
  let vRail : Fin k → DRWire := fun i => (pinWire k ((1, i), false), pinWire k ((1, i), true))
  let rF := drGlobalEval N k r false hk xRail uRail r G
  let rS := drGlobalEval N k r true hk xRail vRail r rF.1
  let rMis := fintypeBuild (ι := Bool × Fin k × Bool) (fun G' cib =>
    let w := if cib.1 then rS.2 cib.2.1 else rF.2 cib.2.1
    let pin := pinWire k (((if cib.1 then (6 : Fin 7) else (5 : Fin 7)), cib.2.1), cib.2.2)
    addMGate N G' true pin (if cib.2.2 then w.1 else w.2)) rS.1
  let rAny := addTree false N rMis.1 (ofFintype rMis.2)
  addMGate N rAny.1 false (empty s) rAny.2

lemma addBucketFail_spec {k r d m : ℕ} (hk : 0 < k)
    (A : Fin m → Fin k → Bool) (empty : Fin (2 ^ m) → ℕ) (excl : (Fin k × Bool) → Fin (2 ^ m) → ℕ)
    (G0 : List MGate) (dpD : ℕ)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (he_bd : ∀ s, empty s < 2 + Fintype.card (Pin315 k) + G0.length)
    (he_dep : ∀ s, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (empty s) 0 ≤ dpD)
    (he_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) s, (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (empty s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ, hashVal A (fun l => x (enterIdx k d hk l)) = s))
    (hx_bd : ∀ lb s, excl lb s < 2 + Fintype.card (Pin315 k) + G0.length)
    (hx_dep : ∀ lb s, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (excl lb s) 0 ≤ dpD)
    (hx_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) l b s, (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (excl (l, b) s) false = true ↔
        ¬ ∃ x ∈ candSet315 k r d u v ρ,
            hashVal A (fun j => x (enterIdx k d hk j)) = s ∧ x (enterIdx k d hk l) = b))
    (s : Fin (2 ^ m)) :
    let N := 2 + Fintype.card (Pin315 k)
    let res := addBucketFail k r d m hk empty excl G0 s
    WellFormed N res.1 ∧ Extends G0 res.1 ∧
    res.1.length ≤ G0.length + (52 * (k + 1) * (r + 1)) ∧
    res.2 < N + res.1.length ∧ (mdepths N res.1).getD res.2 0 ≤ dpD + 9 * r + Nat.clog 2 (4 * k) + 4 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      let cand := candSet315 k r d u v ρ
      (∀ x ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s →
        fitsTrack ρ 5 (firstFn k r (bitsToNat x) (bitsToNat u)) →
        fitsTrack ρ 6 (secondFn k r r (bitsToNat x) (bitsToNat v)) →
        (mrun res.1 (mkBits ρ)).getD res.2 false = false) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s →
          hashVal A (fun j => y (enterIdx k d hk j)) = s → x = y) →
        ((mrun res.1 (mkBits ρ)).getD res.2 false = false ↔
          ∃ x ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s ∧
            fitsTrack ρ 5 (firstFn k r (bitsToNat x) (bitsToNat u)) ∧
            fitsTrack ρ 6 (secondFn k r r (bitsToNat x) (bitsToNat v)))) := by
  intro N res
  let xRail : Fin k → DRWire := fun i => (excl (enterInv k d hk i, true) s, excl (enterInv k d hk i, false) s)
  let uRail : Fin k → DRWire := fun i => (pinWire k ((0, i), false), pinWire k ((0, i), true))
  let vRail : Fin k → DRWire := fun i => (pinWire k ((1, i), false), pinWire k ((1, i), true))
  have hbx0 : ∀ i, DRBounds N G0 dpD (xRail i) := fun i =>
    ⟨hx_bd _ _, hx_bd _ _, hx_dep _ _, hx_dep _ _⟩
  have hbu0 : ∀ i, DRBounds N G0 dpD (uRail i) := fun i =>
    ⟨pinWire_lt k G0 _, pinWire_lt k G0 _,
     by rw [pinWire_depth]; omega, by rw [pinWire_depth]; omega⟩
  have hbv0 : ∀ G', ∀ i, DRBounds N G' dpD (vRail i) := fun G' i =>
    ⟨pinWire_lt k G' _, pinWire_lt k G' _,
     by rw [pinWire_depth]; omega, by rw [pinWire_depth]; omega⟩
  have hrF := drGlobalEval_spec (r := r) false hk G0 dpD xRail uRail hwf0 hbx0 hbu0 r
  rcases hrF with ⟨hwfF, hextF, hlenF, hbdF, hevF⟩
  set rF := drGlobalEval N k r false hk xRail uRail r G0 with hrFdef
  have hbxF : ∀ i, DRBounds N rF.1 dpD (xRail i) := fun i => drBounds_of_extends hextF (hbx0 i)
  have hrS := drGlobalEval_spec (r := r) true hk rF.1 dpD xRail vRail hwfF hbxF (hbv0 rF.1) r
  rcases hrS with ⟨hwfS, hextS, hlenS, hbdS, hevS⟩
  set rS := drGlobalEval N k r true hk xRail vRail r rF.1 with hrSdef
  have heFS := extends_trans hextF hextS
  have hlenFS := extends_len heFS
  let MisInv : List MGate → (Bool × Fin k × Bool) → ℕ → Prop := fun G cib w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ dpD + 9 * r + 3 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      let cand := candSet315 k r d u v ρ
      ((∀ x ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s →
        (mrun G (mkBits ρ)).getD w false = true →
        ρ ((if cib.1 then (6 : Fin 7) else (5 : Fin 7)), cib.2.1) = some cib.2.2 ∧
        ((if cib.1 then secondFn k r r (bitsToNat x) (bitsToNat v)
          else firstFn k r (bitsToNat x) (bitsToNat u)).testBit cib.2.1.val = !cib.2.2)) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s →
          hashVal A (fun j => y (enterIdx k d hk j)) = s → x = y) →
        ∀ x ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s →
          ((mrun G (mkBits ρ)).getD w false = true ↔
            ρ ((if cib.1 then (6 : Fin 7) else (5 : Fin 7)), cib.2.1) = some cib.2.2 ∧
            ((if cib.1 then secondFn k r r (bitsToNat x) (bitsToNat v)
              else firstFn k r (bitsToNat x) (bitsToNat u)).testBit cib.2.1.val = !cib.2.2))))
  have hmonoM : ∀ {G1 G2 : List MGate} {cib w}, Extends G1 G2 → MisInv G1 cib w → MisInv G2 cib w := by
    intro G1 G2 cib w he ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len he) N), ?_, fun u v ρ huv => ?_⟩
    · rw [mdepths_of_extends he _ hlt]; exact hd
    · have hvb := hv u v ρ huv
      refine ⟨fun x hx hxs hw => ?_, fun hinj x hx hxs => ?_⟩
      · rw [mrun_of_extends he _ _ hlt] at hw; exact hvb.1 x hx hxs hw
      · rw [mrun_of_extends he _ _ hlt]; exact hvb.2 hinj x hx hxs
  have hsound_x : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ∀ x ∈ candSet315 k r d u v ρ, hashVal A (fun j => x (enterIdx k d hk j)) = s →
      ∀ i, DRSound G0 (mkBits ρ) (xRail i) ((bitsToNat x).testBit i.val) := by
    intro u v ρ huv x hx hxs i
    rw [bitsToNat_testBit]
    constructor <;> intro hw
    · have hno := (hx_val u v ρ (enterInv k d hk i) true s huv).mp hw
      cases hxi : x i
      · rfl
      · exact False.elim (hno ⟨x, hx, hxs, by rw [enterIdx_inv]; exact hxi⟩)
    · have hno := (hx_val u v ρ (enterInv k d hk i) false s huv).mp hw
      cases hxi : x i
      · exact False.elim (hno ⟨x, hx, hxs, by rw [enterIdx_inv]; exact hxi⟩)
      · rfl
  have hexact_x : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      (∀ x ∈ candSet315 k r d u v ρ, ∀ y ∈ candSet315 k r d u v ρ,
        hashVal A (fun j => x (enterIdx k d hk j)) = s →
        hashVal A (fun j => y (enterIdx k d hk j)) = s → x = y) →
      ∀ x ∈ candSet315 k r d u v ρ, hashVal A (fun j => x (enterIdx k d hk j)) = s →
      ∀ i, DRExact G0 (mkBits ρ) (xRail i) ((bitsToNat x).testBit i.val) := by
    intro u v ρ huv hinj x hx hxs i
    rw [bitsToNat_testBit]
    constructor
    · rw [hx_val u v ρ (enterInv k d hk i) true s huv]
      constructor
      · intro hno; cases hxi : x i
        · rfl
        · exact False.elim (hno ⟨x, hx, hxs, by rw [enterIdx_inv]; exact hxi⟩)
      · rintro hxi ⟨y, hy, hys, hyi⟩
        have heq := hinj x hx y hy hxs hys
        rw [← heq, enterIdx_inv, hxi] at hyi; exact Bool.noConfusion hyi
    · rw [hx_val u v ρ (enterInv k d hk i) false s huv]
      constructor
      · intro hno; cases hxi : x i
        · exact False.elim (hno ⟨x, hx, hxs, by rw [enterIdx_inv]; exact hxi⟩)
        · rfl
      · rintro hxi ⟨y, hy, hys, hyi⟩
        have heq := hinj x hx y hy hxs hys
        rw [← heq, enterIdx_inv, hxi] at hyi; exact Bool.noConfusion hyi
  have hexact_tr : ∀ (tr : Fin 7) (fn : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (tr, i) = some (fn i)) →
      ∀ G' i, DRExact G' (mkBits ρ) (pinWire k ((tr, i), false), pinWire k ((tr, i), true)) ((bitsToNat fn).testBit i.val) := by
    intro tr fn ρ htr G' i
    rw [bitsToNat_testBit]
    constructor <;> dsimp only <;> rw [pinWire_val] <;> simp [mkBits, htr i]
  have hMis := fintypeBuild_spec (ι := Bool × Fin k × Bool) N 1
    (fun G' cib =>
      let w := if cib.1 then rS.2 cib.2.1 else rF.2 cib.2.1
      let pin := pinWire k (((if cib.1 then (6 : Fin 7) else (5 : Fin 7)), cib.2.1), cib.2.2)
      addMGate N G' true pin (if cib.2.2 then w.1 else w.2))
    MisInv hmonoM rS.1 hwfS (fun G cib hwf hext => by
      have hlenG := extends_len hext
      set w := if cib.1 then rS.2 cib.2.1 else rF.2 cib.2.1
      have hwbd : DRBounds N rS.1 (dpD + 2 + 9 * r) w := by
        cases hc : cib.1 <;> dsimp [w] <;> simp only [hc]
        · exact drBounds_of_extends hextS (hbdF cib.2.1)
        · exact hbdS cib.2.1
      have hwb : (if cib.2.2 then w.1 else w.2) < N + G.length := by
        cases hc2 : cib.2.2 <;> [have := hwbd.2.1; have := hwbd.1] <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte] <;> omega
      refine ⟨addMGate_wf hwf true (pinWire_lt k G _) hwb, addMGate_extends N G true _ _,
        by rw [addMGate_len], addMGate_out_lt N G true _ _, ?_, fun u v ρ huv => ?_⟩
      · rw [addMGate_depth, pinWire_depth, mdepths_of_extends hext _ (by cases hc2 : cib.2.2 <;> [exact hwbd.2.1; exact hwbd.1])]
        cases hc2 : cib.2.2 <;> [have := hwbd.2.2.2; have := hwbd.2.2.1] <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte] <;> omega
      · rw [addMGate_val]; simp only [↓reduceIte, Bool.and_eq_true, pinWire_val, mkBits, decide_eq_true_eq]
        rw [mrun_of_extends hext _ _ (by cases cib.2.2 <;> [exact hwbd.2.1; exact hwbd.1])]
        constructor
        · rintro x hx hxs ⟨hρ, hw⟩
          refine ⟨hρ, ?_⟩
          have hwS : DRSound rS.1 (mkBits ρ) w
              ((if cib.1 then secondFn k r r (bitsToNat x) (bitsToNat v)
                else firstFn k r (bitsToNat x) (bitsToNat u)).testBit cib.2.1.val) := by
            cases hc : cib.1 <;> dsimp [w] <;> simp only [hc]
            · have hS := (hevF (mkBits ρ) (bitsToNat x) (bitsToNat u) (bitsToNat_lt x) (bitsToNat_lt u)).1
                (hsound_x u v ρ huv x hx hxs) (fun i => drExact_to_sound (hexact_tr 0 u ρ (fun j => (huv j).1) G0 i)) cib.2.1
              exact drSound_of_extends hextS (hbdF _).1 (hbdF _).2.1 hS
            · have hS := (hevS (mkBits ρ) (bitsToNat x) (bitsToNat v) (bitsToNat_lt x) (bitsToNat_lt v)).1
                (fun i => drSound_of_extends hextF (hbx0 i).1 (hbx0 i).2.1 (hsound_x u v ρ huv x hx hxs i))
                (fun i => drExact_to_sound (hexact_tr 1 v ρ (fun j => (huv j).2) rF.1 i)) cib.2.1
              exact hS
          cases hb : cib.2.2 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at hw ⊢
          · exact hwS.2 hw
          · exact hwS.1 hw
        · intro hinj x hx hxs
          have hwX : DRExact rS.1 (mkBits ρ) w
              ((if cib.1 then secondFn k r r (bitsToNat x) (bitsToNat v)
                else firstFn k r (bitsToNat x) (bitsToNat u)).testBit cib.2.1.val) := by
            cases hc : cib.1 <;> dsimp [w] <;> simp only [hc]
            · have hX := (hevF (mkBits ρ) (bitsToNat x) (bitsToNat u) (bitsToNat_lt x) (bitsToNat_lt u)).2
                (hexact_x u v ρ huv hinj x hx hxs) (hexact_tr 0 u ρ (fun j => (huv j).1) G0) cib.2.1
              exact drExact_of_extends hextS (hbdF _).1 (hbdF _).2.1 hX
            · have hX := (hevS (mkBits ρ) (bitsToNat x) (bitsToNat v) (bitsToNat_lt x) (bitsToNat_lt v)).2
                (fun i => drExact_of_extends hextF (hbx0 i).1 (hbx0 i).2.1 (hexact_x u v ρ huv hinj x hx hxs i))
                (hexact_tr 1 v ρ (fun j => (huv j).2) rF.1) cib.2.1
              exact hX
          apply and_congr_right; intro _
          cases hb : cib.2.2 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
          · exact hwX.2
          · exact hwX.1)
  rcases hMis with ⟨hwfM, hextM, hlenM, hinvM⟩
  set rMis := fintypeBuild (ι := Bool × Fin k × Bool) _ rS.1 with hrM
  have hcardM : Fintype.card (Bool × Fin k × Bool) = 4 * k := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    ring
  rw [hcardM, mul_one] at hlenM
  have hT := addTree_spec (P := Pin315 k) false rMis.1 (ofFintype rMis.2) (dpD + 9 * r + 3) hwfM
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨cib, rfl⟩; exact (hinvM cib).1)
    (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨cib, rfl⟩; exact (hinvM cib).2.1)
  rcases hT with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
  rw [ofFintype_length, hcardM] at hlenT hdepT
  set rAny := addTree false N rMis.1 (ofFintype rMis.2) with hrAny
  have he0A := extends_trans heFS (extends_trans hextM hextT)
  have hlen0A := extends_len he0A
  have hltE : empty s < N + rAny.1.length := lt_of_lt_of_le (he_bd s) (by omega)
  have hwfFin := addMGate_wf hwfT false hltE hbdT
  have heFin := addMGate_extends N rAny.1 false (empty s) rAny.2
  have hlenFin := addMGate_len N rAny.1 false (empty s) rAny.2
  have hbdFin := addMGate_out_lt N rAny.1 false (empty s) rAny.2
  set rFin := addMGate N rAny.1 false (empty s) rAny.2 with hrFin
  dsimp only [res, addBucketFail]; rw [← hrFdef, ← hrSdef, ← hrM, ← hrAny, ← hrFin]
  refine ⟨hwfFin, extends_trans he0A heFin, ?_, hbdFin, ?_, fun u v ρ huv => ?_⟩
  · have hsum_eval : 2 * ((6 + 26 * r) * k) + 8 * k + 1 ≤ 52 * (k + 1) * (r + 1) := by
      have h1 : 52 * (k + 1) * (r + 1) = 52 * r * k + 52 * r + 52 * k + 52 := by ring
      have h2 : 2 * ((6 + 26 * r) * k) + 8 * k + 1 = 52 * r * k + 20 * k + 1 := by ring
      omega
    have hlenFin' : rFin.1.length = rAny.1.length + 1 := hlenFin
    have hlenT' : rAny.1.length ≤ rMis.1.length + 4 * k := hlenT
    calc rFin.1.length = rAny.1.length + 1 := hlenFin'
      _ ≤ (rMis.1.length + 4 * k) + 1 := Nat.add_le_add_right hlenT' 1
      _ ≤ ((rS.1.length + 4 * k) + 4 * k) + 1 := Nat.add_le_add_right (Nat.add_le_add_right hlenM _) 1
      _ ≤ (((rF.1.length + (6 + 26 * r) * k) + 4 * k) + 4 * k) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hlenS _) _) 1
      _ ≤ ((((G0.length + (6 + 26 * r) * k) + (6 + 26 * r) * k) + 4 * k) + 4 * k) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hlenF _) _) _) 1
      _ ≤ G0.length + 52 * (k + 1) * (r + 1) := by
          have : G0.length + (6 + 26 * r) * k + (6 + 26 * r) * k + 4 * k + 4 * k + 1 =
              G0.length + (2 * ((6 + 26 * r) * k) + 8 * k + 1) := by ring
          omega
  · rw [addMGate_depth, mdepths_of_extends he0A _ (he_bd s)]
    dsimp only [N] at hdepT ⊢
    have := he_dep s; omega
  · have hfail_iff : (mrun rFin.1 (mkBits ρ)).getD rFin.2 false = true ↔
        (¬ ∃ x ∈ candSet315 k r d u v ρ, hashVal A (fun j => x (enterIdx k d hk j)) = s) ∨
        (∃ cib : Bool × Fin k × Bool, (mrun rMis.1 (mkBits ρ)).getD (rMis.2 cib) false = true) := by
      rw [addMGate_val]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      rw [mrun_of_extends he0A _ _ (he_bd s), he_val u v ρ s huv, hevT (mkBits ρ), evalList_ofFintype_false]
    constructor
    · intro x hx hxs hf5 hf6
      cases hval : (mrun rFin.1 (mkBits ρ)).getD rFin.2 false
      · rfl
      · rcases hfail_iff.mp hval with hemp | ⟨cib, hmis⟩
        · exact False.elim (hemp ⟨x, hx, hxs⟩)
        · rcases ((hinvM cib).2.2 u v ρ huv).1 x hx hxs hmis with ⟨hρ, hne⟩
          cases hc : cib.1 <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hρ hne
          · have heq := hf5 cib.2.1 cib.2.2 hρ
            rw [heq] at hne; cases hcb : cib.2.2 <;> simp only [hcb, Bool.not_false, Bool.not_true] at hne <;> exact Bool.noConfusion hne
          · have heq := hf6 cib.2.1 cib.2.2 hρ
            rw [heq] at hne; cases hcb : cib.2.2 <;> simp only [hcb, Bool.not_false, Bool.not_true] at hne <;> exact Bool.noConfusion hne
    · intro hinj
      constructor
      · intro hfalse
        have hnt : ¬ ((mrun rFin.1 (mkBits ρ)).getD rFin.2 false = true) := by rw [hfalse]; decide
        rw [hfail_iff] at hnt; push Not at hnt
        rcases hnt with ⟨⟨x, hx, hxs⟩, hnomis⟩
        refine ⟨x, hx, hxs, fun i b hρ => ?_, fun i b hρ => ?_⟩
        · have hno := ((hinvM (false, i, b)).2.2 u v ρ huv).2 hinj x hx hxs
          have hf : ¬ ((mrun rMis.1 (mkBits ρ)).getD (rMis.2 (false, i, b)) false = true) := hnomis (false, i, b)
          rw [hno] at hf; simp only [Bool.false_eq_true, ↓reduceIte, not_and] at hf
          have hbit := hf hρ
          cases hb : b <;> cases ht : (firstFn k r (bitsToNat x) (bitsToNat u)).testBit i.val <;>
            simp only [hb, ht, Bool.not_false, Bool.not_true] at hbit ⊢ <;> first | rfl | exact False.elim (hbit trivial)
        · have hno := ((hinvM (true, i, b)).2.2 u v ρ huv).2 hinj x hx hxs
          have hf : ¬ ((mrun rMis.1 (mkBits ρ)).getD (rMis.2 (true, i, b)) false = true) := hnomis (true, i, b)
          rw [hno] at hf; simp only [↓reduceIte, not_and] at hf
          have hbit := hf hρ
          cases hb : b <;> cases ht : (secondFn k r r (bitsToNat x) (bitsToNat v)).testBit i.val <;>
            simp only [hb, ht, Bool.not_false, Bool.not_true] at hbit ⊢ <;> first | rfl | exact False.elim (hbit trivial)
      · rintro ⟨x, hx, hxs, hf5, hf6⟩
        cases hval : (mrun rFin.1 (mkBits ρ)).getD rFin.2 false
        · rfl
        · rcases hfail_iff.mp hval with hemp | ⟨cib, hmis⟩
          · exact False.elim (hemp ⟨x, hx, hxs⟩)
          · rcases ((hinvM cib).2.2 u v ρ huv).1 x hx hxs hmis with ⟨hρ, hne⟩
            cases hc : cib.1 <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hρ hne
            · have heq := hf5 cib.2.1 cib.2.2 hρ
              rw [heq] at hne; cases hcb : cib.2.2 <;> simp only [hcb, Bool.not_false, Bool.not_true] at hne <;> exact Bool.noConfusion hne
            · have heq := hf6 cib.2.1 cib.2.2 hρ
              rw [heq] at hne; cases hcb : cib.2.2 <;> simp only [hcb, Bool.not_false, Bool.not_true] at hne <;> exact Bool.noConfusion hne

-- Put together `addSingleHash`, `buildFullCircuit`, and final `theorem PEqualNP.Outside.L_pcx_315`!
noncomputable def addSingleHash (k r d K : ℕ) (hk : 0 < k)
    (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (A : Fin (2 * Nat.clog 2 (K + 1)) → Fin k → Bool)
    (G : List MGate) : List MGate × (Fin (K + 1) → ℕ) :=
  let N := 2 + Fintype.card (Pin315 k)
  let m := 2 * Nat.clog 2 (K + 1)
  let rScans := addAllScans k d m hk A earlyFail G
  let rReady := addHashReady k m rScans.2.1 rScans.2.2 rScans.1
  let rFails := fintypeBuild (addBucketFail k r d m hk rScans.2.1 rScans.2.2) rReady.1
  let rSort := addBitonicSort N false m rFails.1 rFails.2
  have hM : K + 1 ≤ 2 ^ m := K_succ_le_pow_two_clog K
  fintypeBuild (ι := Fin (K + 1)) (fun G' j =>
    addMGate N G' true rReady.2 (rSort.2 ⟨2 ^ m - 1 - j.val, by omega⟩)) rSort.1

lemma clog2_four_mul_le (k : ℕ) : Nat.clog 2 (4 * k) ≤ k + 2 := by
  apply clog2_le_of_le_pow
  have hk2 : k ≤ 2 ^ k := le_trans (Nat.lt_succ_self k).le (Nat.lt_pow_self (a := 2) (by omega))
  calc 4 * k ≤ 2 ^ 2 * 2 ^ k := by omega
    _ = 2 ^ (k + 2) := by rw [← pow_add]; congr 1; ring

lemma addSingleHash_spec {k r d K : ℕ} (hk : 0 < k)
    (earlyFail : Fin k × Fin (2 ^ (7 * d + 4)) → ℕ)
    (A : Fin (2 * Nat.clog 2 (K + 1)) → Fin k → Bool) (G0 : List MGate)
    (hwf0 : WellFormed (2 + Fintype.card (Pin315 k)) G0)
    (hef_bd : ∀ lw, earlyFail lw < 2 + Fintype.card (Pin315 k) + G0.length)
    (hef_dep : ∀ lw, (mdepths (2 + Fintype.card (Pin315 k)) G0).getD (earlyFail lw) 0 ≤ 7 * d + 4)
    (hef_val : ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool) lw,
      (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G0 (mkBits ρ)).getD (earlyFail lw) false = true ↔ ¬ earlyPassCond k r d hk u v ρ lw.1 lw.2)) :
    let B := 7 * d + 3
    let N := 2 + Fintype.card (Pin315 k)
    let keyLog := Nat.clog 2 (K + 1)
    let m := 2 * keyLog
    let res := addSingleHash k r d K hk earlyFail A G0
    WellFormed N res.1 ∧ Extends G0 res.1 ∧
    res.1.length ≤ G0.length + (9 * (k + 1) ^ 2 * 4 ^ B + 55 * (k + 1) * (r + 1) + 4 * (keyLog + 1) ^ 2) * 2 ^ m ∧
    (∀ j, res.2 j < N + res.1.length) ∧
    (∀ j, (mdepths N res.1).getD (res.2 j) 0 ≤ 3 * k + 9 * r + 2 * B + 4 * (keyLog + 1) ^ 2 + 8) ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      let cand := candSet315 k r d u v ρ
      let acc := cand.filter (fun x =>
        fitsTrack ρ 5 (firstFn k r (bitsToNat x) (bitsToNat u)) ∧
        fitsTrack ρ 6 (secondFn k r r (bitsToNat x) (bitsToNat v)))
      (∀ j : Fin (K + 1), (mrun res.1 (mkBits ρ)).getD (res.2 j) false = true → acc.card ≤ j.val) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal A (fun l => x (enterIdx k d hk l)) =
          hashVal A (fun l => y (enterIdx k d hk l)) → x = y) →
        ∀ j : Fin (K + 1), (mrun res.1 (mkBits ρ)).getD (res.2 j) false = true ↔ acc.card ≤ j.val) := by
  intro B N keyLog m res
  let dpD := 2 * k + 2 * B + 1
  have hM : K + 1 ≤ 2 ^ m := K_succ_le_pow_two_clog K
  have hSc := addAllScans_spec (r := r) hk A earlyFail G0 hwf0 hef_bd hef_dep hef_val
  rcases hSc with ⟨hwfS, hextS, hlenS, he_bd, he_dep, he_val, hx_bd, hx_dep, hx_val⟩
  set rScans := addAllScans k d m hk A earlyFail G0 with hrS
  have hRd := addHashReady_spec (r := r) (d := d) hk A rScans.2.1 rScans.2.2 rScans.1 dpD hwfS
    he_bd he_dep he_val hx_bd hx_dep hx_val
  rcases hRd with ⟨hwfR, hextR, hlenR, hbdR, hdepR, hvalR⟩
  set rReady := addHashReady k m rScans.2.1 rScans.2.2 rScans.1 with hrR
  have hlenR_le := extends_len hextR
  let FailInv : List MGate → Fin (2 ^ m) → ℕ → Prop := fun G s w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ dpD + 9 * r + Nat.clog 2 (4 * k) + 4 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      let cand := candSet315 k r d u v ρ
      (∀ x ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s →
        fitsTrack ρ 5 (firstFn k r (bitsToNat x) (bitsToNat u)) →
        fitsTrack ρ 6 (secondFn k r r (bitsToNat x) (bitsToNat v)) →
        (mrun G (mkBits ρ)).getD w false = false) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s →
          hashVal A (fun j => y (enterIdx k d hk j)) = s → x = y) →
        ((mrun G (mkBits ρ)).getD w false = false ↔
          ∃ x ∈ cand, hashVal A (fun j => x (enterIdx k d hk j)) = s ∧
            fitsTrack ρ 5 (firstFn k r (bitsToNat x) (bitsToNat u)) ∧
            fitsTrack ρ 6 (secondFn k r r (bitsToNat x) (bitsToNat v))))
  have hmonoF : ∀ {G1 G2 : List MGate} {s w}, Extends G1 G2 → FailInv G1 s w → FailInv G2 s w := by
    intro G1 G2 s w he h
    refine ⟨lt_of_lt_of_le h.1 (Nat.add_le_add_left (extends_len he) N), ?_, fun u v ρ huv => ?_⟩
    · rw [mdepths_of_extends he _ h.1]; exact h.2.1
    · have hvb := h.2.2 u v ρ huv
      refine ⟨fun x hx hxs h5 h6 => ?_, fun hinj => ?_⟩
      · rw [mrun_of_extends he _ _ h.1]; exact hvb.1 x hx hxs h5 h6
      · rw [mrun_of_extends he _ _ h.1]; exact hvb.2 hinj
  have hFails := fintypeBuild_spec (ι := Fin (2 ^ m)) N (52 * (k + 1) * (r + 1))
    (addBucketFail k r d m hk rScans.2.1 rScans.2.2) FailInv hmonoF rReady.1 hwfR
    (fun G s hwf hext => by
      have heSG := extends_trans hextR hext
      have hlenSG := extends_len heSG
      exact addBucketFail_spec (r := r) (d := d) hk A rScans.2.1 rScans.2.2 G dpD hwf
        (fun s' => lt_of_lt_of_le (he_bd s') (by omega))
        (fun s' => by rw [mdepths_of_extends heSG _ (he_bd s')]; exact he_dep s')
        (fun u v ρ s' huv => by rw [mrun_of_extends heSG _ _ (he_bd s')]; exact he_val u v ρ s' huv)
        (fun lb s' => lt_of_lt_of_le (hx_bd lb s') (by omega))
        (fun lb s' => by rw [mdepths_of_extends heSG _ (hx_bd lb s')]; exact hx_dep lb s')
        (fun u v ρ l b s' huv => by rw [mrun_of_extends heSG _ _ (hx_bd (l, b) s')]; exact hx_val u v ρ l b s' huv)
        s)
  rcases hFails with ⟨hwfF, hextF, hlenF, hinvF⟩
  set rFails := fintypeBuild (addBucketFail k r d m hk rScans.2.1 rScans.2.2) rReady.1 with hrF
  rw [Fintype.card_fin] at hlenF
  have hSort := addBitonicSort_spec (P := Pin315 k) false m rFails.1 rFails.2
    (dpD + 9 * r + Nat.clog 2 (4 * k) + 4) hwfF (fun s => (hinvF s).1) (fun s => (hinvF s).2.1)
  rcases hSort with ⟨hwfSo, hextSo, hlenSo, hbdSo, hdepSo, hevSo⟩
  set rSort := addBitonicSort N false m rFails.1 rFails.2 with hrSo
  have heRSo := extends_trans hextF hextSo
  have hlenRSo := extends_len heRSo
  have hm_sq : m * (m + 1) ≤ 4 * (keyLog + 1) ^ 2 := by dsimp [m]; nlinarith
  have hm_le : m ≤ 4 * (keyLog + 1) ^ 2 := by dsimp [m]; nlinarith
  have hcl_4k : Nat.clog 2 (4 * k) ≤ k + 2 := clog2_four_mul_le k
  have hcl_k : Nat.clog 2 k ≤ k + 2 := le_trans (Nat.clog_mono_right 2 (by omega : k ≤ 4 * k)) hcl_4k
  let dOut := 3 * k + 9 * r + 2 * B + 4 * (keyLog + 1) ^ 2 + 8
  let RepInv : List MGate → Fin (K + 1) → ℕ → Prop := fun G j w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ dOut ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G (mkBits ρ)).getD w false = true ↔
        ((mrun rReady.1 (mkBits ρ)).getD rReady.2 false = true ∧
          2 ^ m - bpop (fun s => (mrun rFails.1 (mkBits ρ)).getD (rFails.2 s) false) ≤ j.val))
  have hmonoRep : ∀ {G1 G2 : List MGate} {j w}, Extends G1 G2 → RepInv G1 j w → RepInv G2 j w := by
    intro G1 G2 j w he ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len he) N), ?_, ?_⟩
    · rw [mdepths_of_extends he _ hlt]; exact hd
    · intro u v ρ huv; rw [mrun_of_extends he _ _ hlt]; exact hv u v ρ huv
  have hRep := fintypeBuild_spec (ι := Fin (K + 1)) N 1
    (fun G' j => addMGate N G' true rReady.2 (rSort.2 ⟨2 ^ m - 1 - j.val, by omega⟩))
    RepInv hmonoRep rSort.1 hwfSo (fun G j hwf hext => by
      have heRG := extends_trans heRSo hext
      have hlenRG := extends_len heRG
      have hlenSoG := extends_len hext
      have hlt1 : rReady.2 < N + G.length := lt_of_lt_of_le hbdR (by omega)
      have hlt2 : rSort.2 ⟨2 ^ m - 1 - j.val, by omega⟩ < N + G.length := lt_of_lt_of_le (hbdSo _) (by omega)
      refine ⟨addMGate_wf hwf true hlt1 hlt2, addMGate_extends N G true _ _,
        by rw [addMGate_len], addMGate_out_lt N G true _ _, ?_, fun u v ρ huv => ?_⟩
      · rw [addMGate_depth, mdepths_of_extends heRG _ hbdR, mdepths_of_extends hext _ (hbdSo _)]
        have h1 := hdepR; have h2 := hdepSo ⟨2 ^ m - 1 - j.val, by omega⟩
        dsimp [dpD, dOut] at h1 h2 ⊢; omega
      · rw [addMGate_val]; simp only [↓reduceIte, Bool.and_eq_true]
        rw [mrun_of_extends heRG _ _ hbdR, mrun_of_extends hext _ _ (hbdSo _),
          hevSo (mkBits ρ) ⟨2 ^ m - 1 - j.val, by omega⟩]
        simp only [sortedBit, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
        have hbp := bpop_le (fun s => (mrun rFails.1 (mkBits ρ)).getD (rFails.2 s) false)
        have hjlt := j.isLt
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
  rcases hRep with ⟨hwfRep, hextRep, hlenRep, hinvRep⟩
  set rRep := fintypeBuild (ι := Fin (K + 1))
    (fun G' j => addMGate N G' true rReady.2 (rSort.2 ⟨2 ^ m - 1 - j.val, by omega⟩)) rSort.1 with hrRep
  rw [Fintype.card_fin, mul_one] at hlenRep
  dsimp only [res, addSingleHash]; rw [← hrRep]
  refine ⟨hwfRep, extends_trans hextS (extends_trans hextR (extends_trans hextF (extends_trans hextSo hextRep))), ?_,
    fun j => (hinvRep j).1, fun j => (hinvRep j).2.1, fun u v ρ huv => ?_⟩
  · have hscan_coef : (2 * k + 1) * (3 * k + 1) ≤ 9 * (k + 1) ^ 2 := by nlinarith
    have hcoef : (2 * k + 1) * (3 * k + 1) * 4 ^ B + (2 * k + 2) + 52 * (k + 1) * (r + 1) +
        m * (m + 1) + 1 ≤
        9 * (k + 1) ^ 2 * 4 ^ B + 55 * (k + 1) * (r + 1) + 4 * (keyLog + 1) ^ 2 := by
      have hm1 := Nat.mul_le_mul_right (4 ^ B) hscan_coef
      nlinarith
    have hmul := Nat.mul_le_mul_right (2 ^ m) hcoef
    nlinarith
  · set cand := candSet315 k r d u v ρ
    set acc := cand.filter (fun x =>
      fitsTrack ρ 5 (firstFn k r (bitsToNat x) (bitsToNat u)) ∧
      fitsTrack ρ 6 (secondFn k r r (bitsToNat x) (bitsToNat v)))
    set f : Fin (2 ^ m) → Bool := fun s => (mrun rFails.1 (mkBits ρ)).getD (rFails.2 s) false
    set F0 : Finset (Fin (2 ^ m)) := Finset.univ.filter (fun s => f s = false)
    have hF0_eq : 2 ^ m - bpop f = F0.card := by
      have hsum : bpop f + F0.card = 2 ^ m := bpop_add_card_false f
      omega
    have hsub : acc.image (fun x => hashVal A (fun l => x (enterIdx k d hk l))) ⊆ F0 := by
      intro s hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨x, hx, rfl⟩
      rw [Finset.mem_filter] at hx
      simp only [F0, Finset.mem_filter, Finset.mem_univ, true_and, f]
      exact ((hinvF (hashVal A _)).2.2 u v ρ huv).1 x hx.1 rfl hx.2.1 hx.2.2
    constructor
    · intro j hj
      rcases ((hinvRep j).2.2 u v ρ huv).mp hj with ⟨hrdy, hcnt⟩
      have hinj := (hvalR u v ρ huv).mp hrdy
      have hcard_img : (acc.image (fun x => hashVal A (fun l => x (enterIdx k d hk l)))).card = acc.card :=
        Finset.card_image_of_injOn (fun x hx y hy hxy =>
          hinj x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
      have hle : acc.card ≤ F0.card := by rw [← hcard_img]; exact Finset.card_le_card hsub
      rw [hF0_eq] at hcnt
      exact le_trans hle hcnt
    · intro hinj j
      have hrdy : (mrun rReady.1 (mkBits ρ)).getD rReady.2 false = true :=
        (hvalR u v ρ huv).mpr hinj
      have hF0_eq_img : F0 = acc.image (fun x => hashVal A (fun l => x (enterIdx k d hk l))) := by
        apply Finset.Subset.antisymm _ hsub
        intro s hs
        simp only [F0, Finset.mem_filter, Finset.mem_univ, true_and, f] at hs
        have hinj_s : ∀ x ∈ cand, ∀ y ∈ cand, hashVal A (fun l => x (enterIdx k d hk l)) = s →
            hashVal A (fun l => y (enterIdx k d hk l)) = s → x = y :=
          fun x hx y hy hxs hys => hinj x hx y hy (hxs.trans hys.symm)
        rcases (((hinvF s).2.2 u v ρ huv).2 hinj_s).mp hs with ⟨x, hx, hxs, h5, h6⟩
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h5, h6⟩, hxs⟩
      have hcard_img : (acc.image (fun x => hashVal A (fun l => x (enterIdx k d hk l)))).card = acc.card :=
        Finset.card_image_of_injOn (fun x hx y hy hxy =>
          hinj x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
      rw [(hinvRep j).2.2 u v ρ huv, hF0_eq, hF0_eq_img, hcard_img, hrdy]
      simp only [true_and]

noncomputable def buildFullCircuit (k r d K : ℕ) (hk : 0 < k)
    (H : Fin (14 * k + 1) → (Fin (2 * Nat.clog 2 (K + 1)) → Fin k → Bool)) :
    List MGate × (Fin (K + 1) → ℕ) :=
  let N := 2 + Fintype.card (Pin315 k)
  let R := 14 * k + 1
  let rEarly := fintypeBuild (ι := Fin k × Fin (2 ^ (7 * d + 4))) (addEarlyCell k r d hk) []
  let rHashes := fintypeBuild (ι := Fin R)
    (fun G' idx => addSingleHash k r d K hk rEarly.2 (H idx) G') rEarly.1
  fintypeBuild (ι := Fin (K + 1))
    (fun G' j => addTree false N G' (ofFintype (fun idx : Fin R => rHashes.2 idx j))) rHashes.1

lemma early_cost_le (d : ℕ) : 88 * d * (7 * d + 4) + 8 ≤ 1408 * 2 ^ (7 * d + 3) := by
  have hpow : (7 * d + 4) ^ 2 ≤ 16 * 2 ^ (7 * d + 3) := by
    induction d with
    | zero => norm_num
    | succ d ih =>
      have hp : 2 ^ (7 * (d + 1) + 3) = 128 * 2 ^ (7 * d + 3) := by
        rw [show 7 * (d + 1) + 3 = (7 * d + 3) + 7 by ring, pow_add]; ring
      rw [hp]
      have h1 : 7 * (d + 1) + 4 ≤ 3 * (7 * d + 4) := by omega
      nlinarith
  nlinarith

lemma clog2_R315_le (k : ℕ) : Nat.clog 2 (14 * k + 1) ≤ k + 4 := by
  apply clog2_le_of_le_pow
  have hk1 : k + 1 ≤ 2 ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  calc 14 * k + 1 ≤ 16 * (k + 1) := by omega
    _ ≤ 16 * 2 ^ k := Nat.mul_le_mul_left 16 hk1
    _ = 2 ^ 4 * 2 ^ k := by norm_num
    _ = 2 ^ (k + 4) := by rw [← pow_add]; congr 1; ring

end PEqualNP.Outside.L_pcx_315_aux

theorem PEqualNP.Outside.L_pcx_315 : ∀ (k r d K : ℕ), 0 < k → d ≤ r →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (t rowKey rowName : Nat) =>
    (List.range t).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (t colKey colName : Nat) =>
    (List.range t).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let V := Fin 7 × Fin k
  let P := V × Bool
  let keyLog := Nat.clog 2 (K+1)
  let B := 7*d+3
  let budget := 1048576*(k+1)^2*(K+1)^2*((k+1)*4^B+(r+1)+(keyLog+1)^2)
  let rounds := 128*(k+r+B+(keyLog+1)^2+1)
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
    ∀ (u v : Fin k → Bool) (ρ : V → Option Bool),
      (∀ i, ρ (0,i) = some (u i) ∧ ρ (1,i) = some (v i)) →
      let bits := fun p : P => decide (ρ p.1 = some p.2)
      let word := fun (x : Fin k → Bool) => ∑ j : Fin k, (x j).toNat * 2^j.val
      let fits := fun (track : Fin 7) (x : ℕ) =>
        ∀ i : Fin k, ∀ b : Bool, ρ (track,i) = some b → x.testBit i.val = b
      let candidates := Finset.univ.filter (fun x : Fin k → Bool =>
        fits 2 (word x) ∧ fits 3 (first d (word x) (word u)) ∧
        fits 4 (second d (word x) (word v)))
      let accepted := candidates.filter (fun x =>
        fits 5 (first r (word x) (word u)) ∧ fits 6 (second r (word x) (word v)))
      (∀ j : Fin (K+1), (run G bits).getD (out j) false = true → accepted.card ≤ j.val) ∧
      (candidates.card ≤ K → ∀ j : Fin (K+1),
        (run G bits).getD (out j) false = true ↔ accepted.card ≤ j.val) := by
  open PEqualNP.Outside.L_pcx_315_aux in
  intro k r d K hk hdr
  dsimp only
  let B := 7 * d + 3
  let N := 2 + Fintype.card (Pin315 k)
  let keyLog := Nat.clog 2 (K + 1)
  let m := 2 * keyLog
  let R := 14 * k + 1
  rcases hashFamily_exists_315 k r d K hk with ⟨H, hH⟩
  have hwf0 : WellFormed N [] := fun i => Fin.elim0 i
  let EarlyInv : List MGate → Fin k × Fin (2 ^ (7 * d + 4)) → ℕ → Prop := fun G lw w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ 7 * d + 4 ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G (mkBits ρ)).getD w false = true ↔ ¬ earlyPassCond k r d hk u v ρ lw.1 lw.2)
  have hmonoE : ∀ {G1 G2 : List MGate} {lw w}, Extends G1 G2 → EarlyInv G1 lw w → EarlyInv G2 lw w := by
    intro G1 G2 lw w he ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len he) N), ?_, ?_⟩
    · rw [mdepths_of_extends he _ hlt]; exact hd
    · intro u v ρ huv; rw [mrun_of_extends he _ _ hlt]; exact hv u v ρ huv
  have hEarly := fintypeBuild_spec (ι := Fin k × Fin (2 ^ (7 * d + 4))) N (88 * d * (7 * d + 4) + 8)
    (addEarlyCell k r d hk) EarlyInv hmonoE [] hwf0 (fun G lw hwf _ =>
      addEarlyCell_spec k r d hk G hwf lw)
  rcases hEarly with ⟨hwfE, hextE, hlenE, hinvE⟩
  set rEarly := fintypeBuild (addEarlyCell k r d hk) [] with hrE
  have hcardE : Fintype.card (Fin k × Fin (2 ^ (7 * d + 4))) = 2 * k * 2 ^ B := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, pow_succ]
    ring
  rw [hcardE] at hlenE
  let singleS := 9 * (k + 1) ^ 2 * 4 ^ B + 55 * (k + 1) * (r + 1) + 4 * (keyLog + 1) ^ 2
  let singleD := 3 * k + 9 * r + 2 * B + 4 * (keyLog + 1) ^ 2 + 8
  let HashInv : List MGate → Fin R → (Fin (K + 1) → ℕ) → Prop := fun G idx out =>
    (∀ j, out j < N + G.length) ∧
    (∀ j, (mdepths N G).getD (out j) 0 ≤ singleD) ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      let cand := candSet315 k r d u v ρ
      let acc := cand.filter (fun x =>
        fitsTrack ρ 5 (firstFn k r (bitsToNat x) (bitsToNat u)) ∧
        fitsTrack ρ 6 (secondFn k r r (bitsToNat x) (bitsToNat v)))
      (∀ j : Fin (K + 1), (mrun G (mkBits ρ)).getD (out j) false = true → acc.card ≤ j.val) ∧
      ((∀ x ∈ cand, ∀ y ∈ cand, hashVal (H idx) (fun l => x (enterIdx k d hk l)) =
          hashVal (H idx) (fun l => y (enterIdx k d hk l)) → x = y) →
        ∀ j : Fin (K + 1), (mrun G (mkBits ρ)).getD (out j) false = true ↔ acc.card ≤ j.val)
  have hmonoH : ∀ {G1 G2 : List MGate} {idx out}, Extends G1 G2 → HashInv G1 idx out → HashInv G2 idx out := by
    intro G1 G2 idx out he ⟨hbd, hdep, hv⟩
    refine ⟨fun j => lt_of_lt_of_le (hbd j) (Nat.add_le_add_left (extends_len he) N),
      fun j => by rw [mdepths_of_extends he _ (hbd j)]; exact hdep j, fun u v ρ huv => ?_⟩
    have hvb := hv u v ρ huv
    constructor
    · intro j hj; rw [mrun_of_extends he _ _ (hbd j)] at hj; exact hvb.1 j hj
    · intro hinj j; rw [mrun_of_extends he _ _ (hbd j)]; exact hvb.2 hinj j
  have hHashes := fintypeBuild_spec (ι := Fin R) N (singleS * 2 ^ m)
    (fun G' idx => addSingleHash k r d K hk rEarly.2 (H idx) G') HashInv hmonoH rEarly.1 hwfE
    (fun G idx hwf hext => by
      have hlenG := extends_len hext
      exact addSingleHash_spec hk rEarly.2 (H idx) G hwf
        (fun lw => lt_of_lt_of_le (hinvE lw).1 (by omega))
        (fun lw => by rw [mdepths_of_extends hext _ (hinvE lw).1]; exact (hinvE lw).2.1)
        (fun u v ρ lw huv => by rw [mrun_of_extends hext _ _ (hinvE lw).1]; exact (hinvE lw).2.2 u v ρ huv))
  rcases hHashes with ⟨hwfH, hextH, hlenH, hinvH⟩
  set rHashes := fintypeBuild (fun G' idx => addSingleHash k r d K hk rEarly.2 (H idx) G') rEarly.1 with hrH
  rw [Fintype.card_fin] at hlenH
  let OutInv : List MGate → Fin (K + 1) → ℕ → Prop := fun G j w =>
    w < N + G.length ∧ (mdepths N G).getD w 0 ≤ singleD + Nat.clog 2 R ∧
    ∀ (u v : Fin k → Bool) (ρ : (Fin 7 × Fin k) → Option Bool), (∀ i, ρ (0, i) = some (u i) ∧ ρ (1, i) = some (v i)) →
      ((mrun G (mkBits ρ)).getD w false = true ↔
        ∃ idx : Fin R, (mrun rHashes.1 (mkBits ρ)).getD (rHashes.2 idx j) false = true)
  have hmonoO : ∀ {G1 G2 : List MGate} {j w}, Extends G1 G2 → OutInv G1 j w → OutInv G2 j w := by
    intro G1 G2 j w he ⟨hlt, hd, hv⟩
    refine ⟨lt_of_lt_of_le hlt (Nat.add_le_add_left (extends_len he) N), ?_, ?_⟩
    · rw [mdepths_of_extends he _ hlt]; exact hd
    · intro u v ρ huv; rw [mrun_of_extends he _ _ hlt]; exact hv u v ρ huv
  have hOut := fintypeBuild_spec (ι := Fin (K + 1)) N R
    (fun G' j => addTree false N G' (ofFintype (fun idx : Fin R => rHashes.2 idx j)))
    OutInv hmonoO rHashes.1 hwfH (fun G j hwf hext => by
      have hlenG := extends_len hext
      have htr := addTree_spec (P := Pin315 k) false G (ofFintype (fun idx : Fin R => rHashes.2 idx j))
        singleD hwf
        (fun w hw => by rcases (mem_ofFintype_iff _ _).mp hw with ⟨idx, rfl⟩; exact lt_of_lt_of_le ((hinvH idx).1 j) (by omega))
        (fun w hw => by
          rcases (mem_ofFintype_iff _ _).mp hw with ⟨idx, rfl⟩
          rw [mdepths_of_extends hext _ ((hinvH idx).1 j)]
          exact (hinvH idx).2.1 j)
      rcases htr with ⟨hwfT, hextT, hlenT, hbdT, hdepT, hevT⟩
      rw [ofFintype_length, Fintype.card_fin] at hlenT hdepT
      refine ⟨hwfT, hextT, hlenT, hbdT, hdepT, fun u v ρ huv => ?_⟩
      dsimp only [N]
      rw [hevT (mkBits ρ), evalList_ofFintype_false]
      apply exists_congr; intro idx
      rw [mrun_of_extends hext _ _ ((hinvH idx).1 j)])
  rcases hOut with ⟨hwfOut, hextOut, hlenOut, hinvOut⟩
  set rOut := fintypeBuild (ι := Fin (K + 1))
    (fun G' j => addTree false N G' (ofFintype (fun idx : Fin R => rHashes.2 idx j))) rHashes.1 with hrOut
  rw [Fintype.card_fin] at hlenOut
  refine ⟨rOut.1, rOut.2, ?_, hwfOut, ?_, ?_⟩
  · have h2klog : 2 ^ keyLog ≤ 2 * (K + 1) := two_pow_clog2_le K
    have h2m : 2 ^ m ≤ 4 * (K + 1) ^ 2 := by
      dsimp only [m]
      rw [show 2 * keyLog = keyLog * 2 by ring, pow_mul]
      exact le_trans (Nat.pow_le_pow_left h2klog 2) (by ring_nf; omega)
    set T1 := (k + 1) ^ 2 * (K + 1) ^ 2 * ((k + 1) * 4 ^ B)
    set T2 := (k + 1) ^ 2 * (K + 1) ^ 2 * (r + 1)
    set T3 := (k + 1) ^ 2 * (K + 1) ^ 2 * (keyLog + 1) ^ 2
    have hpowKK : 1 ≤ (k + 1) ^ 2 * (K + 1) ^ 2 := Nat.succ_le_of_lt (by positivity)
    have h4B : 4 ^ B = 2 ^ B * 2 ^ B := by rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow]
    have hearly_bd : rEarly.1.length ≤ 2816 * T1 := by
      have h1 : 2 * k * 2 ^ B * (88 * d * (7 * d + 4) + 8) ≤ 2 * k * 2 ^ B * (1408 * 2 ^ B) :=
        Nat.mul_le_mul_left _ (early_cost_le d)
      have h2 : 2 * k * 2 ^ B * (1408 * 2 ^ B) = 2816 * k * 4 ^ B := by rw [h4B]; ring
      have h3 : 2816 * k * 4 ^ B ≤ 2816 * (k + 1) * 4 ^ B := Nat.mul_le_mul_right _ (by omega)
      have h4 : 2816 * (k + 1) * 4 ^ B ≤ 2816 * ((k + 1) ^ 2 * (K + 1) ^ 2) * (k + 1) * 4 ^ B := by
        calc 2816 * (k + 1) * 4 ^ B = (2816 * (k + 1) * 4 ^ B) * 1 := by ring
          _ ≤ (2816 * (k + 1) * 4 ^ B) * ((k + 1) ^ 2 * (K + 1) ^ 2) := Nat.mul_le_mul_left _ hpowKK
          _ = 2816 * ((k + 1) ^ 2 * (K + 1) ^ 2) * (k + 1) * 4 ^ B := by ring
      have h5 : 2816 * ((k + 1) ^ 2 * (K + 1) ^ 2) * (k + 1) * 4 ^ B = 2816 * T1 := by dsimp [T1]; ring
      calc rEarly.1.length
          ≤ [].length + 2 * k * 2 ^ B * (88 * d * (7 * d + 4) + 8) := hlenE
        _ = 2 * k * 2 ^ B * (88 * d * (7 * d + 4) + 8) := by simp
        _ ≤ 2816 * T1 := by rw [← h5]; exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 h4))
    have hR_le : R ≤ 15 * (k + 1) := by dsimp [R]; omega
    have hmul_H : R * (singleS * 2 ^ m) ≤ 540 * T1 + 3300 * T2 + 240 * T3 := by
      have h1 : R * (singleS * 2 ^ m) ≤ (15 * (k + 1)) * (singleS * (4 * (K + 1) ^ 2)) :=
        Nat.mul_le_mul hR_le (Nat.mul_le_mul_left singleS h2m)
      have h2 : (15 * (k + 1)) * (singleS * (4 * (K + 1) ^ 2)) =
          540 * T1 + 3300 * T2 + 240 * ((k + 1) * (K + 1) ^ 2 * (keyLog + 1) ^ 2) := by
        dsimp only [singleS, T1, T2]; ring
      have h3 : (k + 1) * (K + 1) ^ 2 * (keyLog + 1) ^ 2 ≤ T3 := by
        dsimp only [T3]
        calc (k + 1) * (K + 1) ^ 2 * (keyLog + 1) ^ 2
            = 1 * ((k + 1) * (K + 1) ^ 2 * (keyLog + 1) ^ 2) := by ring
          _ ≤ (k + 1) * ((k + 1) * (K + 1) ^ 2 * (keyLog + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
          _ = (k + 1) ^ 2 * (K + 1) ^ 2 * (keyLog + 1) ^ 2 := by ring
      omega
    have hfinal_R : (K + 1) * R ≤ 15 * T2 := by
      have h1 : (K + 1) * R ≤ (K + 1) * (15 * (k + 1)) := Nat.mul_le_mul_left _ hR_le
      have h2 : (K + 1) * (15 * (k + 1)) ≤ 15 * ((k + 1) * (K + 1)) * ((k + 1) * (K + 1) * (r + 1)) := by
        have hpos : 1 ≤ (k + 1) * (K + 1) * (r + 1) := Nat.succ_le_of_lt (by positivity)
        calc (K + 1) * (15 * (k + 1)) = 15 * ((k + 1) * (K + 1)) * 1 := by ring
          _ ≤ 15 * ((k + 1) * (K + 1)) * ((k + 1) * (K + 1) * (r + 1)) := Nat.mul_le_mul_left _ hpos
      have h3 : 15 * ((k + 1) * (K + 1)) * ((k + 1) * (K + 1) * (r + 1)) = 15 * T2 := by dsimp [T2]; ring
      omega
    have hbudget : 1048576 * (k + 1) ^ 2 * (K + 1) ^ 2 * ((k + 1) * 4 ^ B + (r + 1) + (keyLog + 1) ^ 2) =
        1048576 * (T1 + T2 + T3) := by dsimp [T1, T2, T3]; ring
    rw [hbudget]
    omega
  · intro j
    have hclR := clog2_R315_le k
    have hj := hinvOut j
    refine ⟨hj.1, le_trans hj.2.1 ?_⟩
    dsimp only [singleD, R, B, keyLog]; omega
  · intro u v ρ huv
    constructor
    · intro j hj
      change (mrun rOut.1 (mkBits ρ)).getD (rOut.2 j) false = true at hj
      rcases ((hinvOut j).2.2 u v ρ huv).mp hj with ⟨idx, hidx⟩
      exact ((hinvH idx).2.2 u v ρ huv).1 j hidx
    · intro hcard j
      change (mrun rOut.1 (mkBits ρ)).getD (rOut.2 j) false = true ↔ _
      rcases hH u v ρ huv hcard with ⟨idx0, hidx0⟩
      rw [(hinvOut j).2.2 u v ρ huv]
      constructor
      · rintro ⟨idx, hidx⟩
        exact ((hinvH idx).2.2 u v ρ huv).1 j hidx
      · intro hle
        exact ⟨idx0, (((hinvH idx0).2.2 u v ρ huv).2 hidx0 j).mpr hle⟩
