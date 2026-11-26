import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6373_2
    (h1 : let step (w : List ℕ) (g : Bool × ℕ × ℕ) :=
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [if g.1 = true then a ||| b else a &&& b]
      let initial : List ℕ := [1152938275827089415,15270196031782968,58150373818816,
        94946423956573696,54820275478360064,3870282840506368,133412159488,
        470802710610839569,218716039641317512,189725234880971840,156548607029289472,
        229736628137037828,270286071509057568,288160007407796482]
      ∃ (gs : List (Bool × ℕ × ℕ)) (a b : ℕ), gs.length ≤ 26 ∧ a ≠ b ∧
        a < 14 + gs.length ∧ b < 14 + gs.length ∧
        (∀ i : Fin gs.length, let g := gs.get i
          g.2.1 ≠ g.2.2 ∧ g.2.1 < 14 + i.val ∧ g.2.2 < 14 + i.val) ∧
        let w := gs.foldl step initial
        w.getD a 0 &&& w.getD b 0 = 2097151 ∧
        w.getD a 0 &&& 1441151880758558720 = 0 ∧
        w.getD b 0 &&& 1441151880758558720 = 0)
    (h2 : let mask : ℕ := 1729382256910270463
      let high : ℕ := 2882303761517117440
      let step (w : List ℕ) (g : Bool × ℕ × ℕ) :=
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [if g.1 = true then a ||| b else
          (a &&& b &&& mask) ||| ((((a <<< 1) &&& b) ||| (a &&& (b <<< 1))) &&& high)]
      let step0 (w : List ℕ) (g : Bool × ℕ × ℕ) :=
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [if g.1 = true then a ||| b else a &&& b]
      ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
        (gs.foldl step w).map (fun x => x &&& mask) =
          gs.foldl step0 (w.map fun x => x &&& mask))
    (h3 : ∀ k : ℕ, (2882303761517117440 : ℕ).testBit k = true →
       0 < k ∧ (1441151880758558720 : ℕ).testBit (k - 1) = true) : have x1 : ℕ → ℕ → ℕ := fun (x1 x2 : ℕ) => x1 &&& x2 &&& (1729382256910270463 : ℕ) ||| (x1 <<< (1 : ℕ) &&& x2 ||| x1 &&& x2 <<< (1 : ℕ)) &&& (2882303761517117440 : ℕ); have x2 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) =>   have x4 : ℕ := x2.getD x3.2.1 (0 : ℕ);   have x5 : ℕ := x2.getD x3.2.2 (0 : ℕ);   x2 ++ [if x3.1 = Bool.true then x4 ||| x5 else x1 x4 x5]; ∃ (x3 : List (Bool × ℕ × ℕ)) (x4 : ℕ),   x3.length ≤ (27 : ℕ) ∧     (∀ (x5 : Fin x3.length),         have x6 : Bool × ℕ × ℕ := x3.get x5;         x6.2.1 ≠ x6.2.2 ∧ x6.2.1 < (14 : ℕ) + ↑x5 ∧ x6.2.2 < (14 : ℕ) + ↑x5) ∧       (List.foldl x2 [(1729399028130512903 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (2776645719824533521 : ℕ), (218716039641317512 : ℕ), (189725234880971840 : ℕ), (156548607029289472 : ℕ), (229736628137037828 : ℕ), (270286071509057568 : ℕ), (288160007407796482 : ℕ)] x3).getD x4 (0 : ℕ) = (2097151 : ℕ) := by
  obtain ⟨gs,a,b,size,ne,ha,hb,shape,hval,hclearA,hclearB⟩ := h1
  let mask : ℕ := 1729382256910270463
  let high : ℕ := 2882303761517117440
  let bases : ℕ := 1441151880758558720
  let meet (a b : ℕ) := (a &&& b &&& mask) |||
    ((((a <<< 1) &&& b) ||| (a &&& (b <<< 1))) &&& high)
  let step (w : List ℕ) (g : Bool × ℕ × ℕ) :=
    let a := w.getD g.2.1 0
    let b := w.getD g.2.2 0
    w ++ [if g.1 = true then a ||| b else meet a b]
  let step0 (w : List ℕ) (g : Bool × ℕ × ℕ) :=
    let a := w.getD g.2.1 0
    let b := w.getD g.2.2 0
    w ++ [if g.1 = true then a ||| b else a &&& b]
  let initial : List ℕ := [1729399028130512903,15270196031782968,58150373818816,
    94946423956573696,54820275478360064,3870282840506368,133412159488,
    2776645719824533521,218716039641317512,189725234880971840,156548607029289472,
    229736628137037828,270286071509057568,288160007407796482]
  let project (w : ℕ) := w &&& mask
  let qw := gs.foldl step0 (initial.map project)
  have initProject : initial.map project =
      [1152938275827089415,15270196031782968,58150373818816,
        94946423956573696,54820275478360064,3870282840506368,133412159488,
        470802710610839569,218716039641317512,189725234880971840,156548607029289472,
        229736628137037828,270286071509057568,288160007407796482] := by decide +kernel
  rw [← initProject] at hval hclearA hclearB
  change qw.getD a 0 &&& qw.getD b 0 = 2097151 at hval
  change qw.getD a 0 &&& bases = 0 at hclearA
  change qw.getD b 0 &&& bases = 0 at hclearB
  have maskIdem : mask &&& mask = mask := Nat.and_self _
  have basesMask : mask &&& bases = bases := by decide
  have getMap (w : List ℕ) (i : ℕ) :
      (w.map project).getD i 0 = project (w.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? <;> simp [project]
  have projectProduct (x y : ℕ) :
      project x &&& project y = x &&& y &&& mask := by
    unfold project
    rw [Nat.and_right_comm x mask (y &&& mask), ← Nat.and_assoc x y mask,
      Nat.and_assoc (x &&& y) mask mask, maskIdem]
  have lengthAfter (code : List (Bool × ℕ × ℕ)) (w : List ℕ) :
      (code.foldl step w).length = w.length + code.length := by
    induction code generalizing w with
    | nil => simp
    | cons g code ih =>
      rw [List.foldl_cons, ih]
      simp only [step,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
      omega
  let w := gs.foldl step initial
  let x := w.getD a 0
  let y := w.getD b 0
  have run : w.map project = qw := h2 gs initial
  have ex : project x = qw.getD a 0 := by
    rw [← getMap w a, run]
  have ey : project y = qw.getD b 0 := by
    rw [← getMap w b, run]
  have cx : x &&& bases = 0 := by
    rw [← ex] at hclearA
    simpa only [project, Nat.and_assoc, basesMask] using hclearA
  have cy : y &&& bases = 0 := by
    rw [← ey] at hclearB
    simpa only [project, Nat.and_assoc, basesMask] using hclearB
  have vanish (z : ℕ) (c : z &&& bases = 0) {j : ℕ}
      (hj : bases.testBit j = true) : z.testBit j = false := by
    have eq := congrArg (fun t : ℕ => t.testBit j) c
    simpa [Nat.testBit_and, hj] using eq
  have noHigh : ((((x <<< 1) &&& y) ||| (x &&& (y <<< 1))) &&& high) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : high.testBit k = true
    · obtain ⟨hpos,hprev⟩ := h3 k hk
      have xoff := vanish x cx hprev
      have yoff := vanish y cy hprev
      have one : 1 ≤ k := hpos
      simp [Nat.testBit_shiftLeft, one, xoff, yoff, hk]
    · have hf : high.testBit k = false := Bool.eq_false_of_not_eq_true hk
      simp [hf]
  have finish : meet x y = 2097151 := by
    rw [← ex, ← ey] at hval
    rw [show meet x y = (x &&& y &&& mask) |||
      ((((x <<< 1) &&& y) ||| (x &&& (y <<< 1))) &&& high) from rfl, noHigh, Nat.or_zero]
    simpa only [projectProduct] using hval
  let g : Bool × ℕ × ℕ := (false,a,b)
  change ∃ (code : List (Bool × ℕ × ℕ)) (o : ℕ), code.length ≤ 27 ∧
    (∀ i : Fin code.length, let t := code.get i
      t.2.1 ≠ t.2.2 ∧ t.2.1 < 14 + i.val ∧ t.2.2 < 14 + i.val) ∧
    (code.foldl step initial).getD o 0 = 2097151
  refine ⟨gs ++ [g], 14 + gs.length, by simp; omega, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < gs.length
    · simpa only [List.get_eq_getElem,List.getElem_append_left hi] using shape ⟨i,hi⟩
    · have eq : i.val = gs.length := by
        have h := i.isLt
        simp only [List.length_append,List.length_singleton] at h
        omega
      simp only [List.get_eq_getElem, eq, List.getElem_concat_length, g]
      exact ⟨ne,ha,hb⟩
  · have len : w.length = 14 + gs.length := lengthAfter gs initial
    rw [List.foldl_append, ← len]
    change (w ++ [meet x y]).getD w.length 0 = 2097151
    rwa [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
