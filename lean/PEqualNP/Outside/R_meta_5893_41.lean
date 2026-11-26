import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5893_41
    (h_half29 : ∃ (C : Circuit) (q : ℕ), Monotone2 C ∧ C.size ≤ 29 ∧
      C.output < 17 + C.size ∧ q < 17 + C.size ∧ ∀ x : Fin 17 → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ (i j : Fin 17), i.val < 6 ∧
        (j.val = 15 + i.val / 3 ∨ (6 ≤ j.val ∧ j.val < 15 ∧
          (if i.val < 3 then (j.val - 6) / 3 else (j.val - 6) % 3) = i.val % 3)) ∧
        x i = true ∧ x j = true) ∧
      (C.eval (List.ofFn x) = false → (C.wires (List.ofFn x)).getD q false = (x 15 || x 16)))
    (h_combine61 : ∀ (C1 : Circuit) (q1 : ℕ) (C2 : Circuit) (q2 : ℕ) (f g : Fin 17 → Fin 25),
      Monotone2 C1 → Monotone2 C2 → C1.size ≤ 29 → C2.size ≤ 30 →
      C1.output < 17 + C1.size → q1 < 17 + C1.size →
      C2.output < 17 + C2.size → q2 < 17 + C2.size →
      ∃ (B : Circuit) (r : ℕ), Monotone2 B ∧ B.size = 61 ∧
        B.output < 25 + B.size ∧ r < 25 + B.size ∧ ∀ x : Fin 25 → Bool,
        B.eval (List.ofFn x) =
          (C1.eval (List.ofFn (fun i => x (f i))) || C2.eval (List.ofFn (fun i => x (g i)))) ∧
        (B.wires (List.ofFn x)).getD r false =
          ((C1.wires (List.ofFn (fun i => x (f i)))).getD q1 false ||
           (C2.wires (List.ofFn (fun i => x (g i)))).getD q2 false)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size = (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ))))) := by
  let E : Fin 25 → Fin 25 → Prop := fun i j =>
    i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let H : Fin 17 → Fin 17 → Prop := fun i j =>
    i.val < 6 ∧ (j.val = 15 + i.val / 3 ∨ (6 ≤ j.val ∧ j.val < 15 ∧
      (if i.val < 3 then (j.val - 6) / 3 else (j.val - 6) % 3) = i.val % 3))
  let f : Fin 17 → Fin 25 := fun i =>
    ([0, 2, 8, 1, 7, 11, 24, 20, 14, 23, 18, 22, 19, 17, 16, 12, 13] : List (Fin 25)).getD i.val 0
  let g : Fin 17 → Fin 25 := fun i =>
    ([5, 9, 10, 3, 4, 6, 22, 20, 19, 24, 16, 18, 17, 23, 14, 15, 21] : List (Fin 25)).getD i.val 0
  let invF : Fin 25 → Fin 17 := fun k =>
    ([0, 3, 1, 0, 0, 0, 0, 4, 2, 0, 0, 5, 15, 16, 8, 0, 14, 13, 10, 12, 7, 0, 11, 9, 6] : List (Fin 17)).getD k.val 0
  let invG : Fin 25 → Fin 17 := fun k =>
    ([0, 0, 0, 3, 4, 0, 5, 0, 0, 1, 2, 0, 0, 0, 14, 15, 10, 12, 11, 8, 7, 16, 6, 13, 9] : List (Fin 17)).getD k.val 0
  have hLift : ∀ i j : Fin 17, H i j → E (f i) (f j) ∧ E (g i) (g j) := by decide +kernel
  have hCoverW : ∀ i j : Fin 25, E i j →
      (H (invF i) (invF j) ∧ f (invF i) = i ∧ f (invF j) = j) ∨
      (H (invG i) (invG j) ∧ g (invG i) = i ∧ g (invG j) = j) := by decide +kernel
  have hCover : ∀ i j : Fin 25, E i j →
      (∃ a b : Fin 17, H a b ∧ f a = i ∧ f b = j) ∨
      (∃ a b : Fin 17, H a b ∧ g a = i ∧ g b = j) := by
    intro i j hij
    rcases hCoverW i j hij with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨invF i, invF j, h1, h2, h3⟩
    · exact Or.inr ⟨invG i, invG j, h1, h2, h3⟩
  have hHChar : ∀ i j : Fin 17, H i j ↔
      (i = 0 ∧ (j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 15)) ∨
      (i = 1 ∧ (j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 15)) ∨
      (i = 2 ∧ (j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15)) ∨
      (i = 3 ∧ (j = 6 ∨ j = 9 ∨ j = 12 ∨ j = 16)) ∨
      (i = 4 ∧ (j = 7 ∨ j = 10 ∨ j = 13 ∨ j = 16)) ∨
      (i = 5 ∧ (j = 8 ∨ j = 11 ∨ j = 14 ∨ j = 16)) := by decide +kernel
  have hf15 : f 15 = 12 := rfl
  have hf16 : f 16 = 13 := rfl
  have hg15 : g 15 = 15 := rfl
  have hg16 : g 16 = 21 := rfl
  let stepW : List Bool → Gate → List Bool := fun w gt =>
    w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  have hEvalAnd : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have hEvalOr : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hWires : ∀ (C : Circuit) (x : List Bool), C.wires x = C.gates.foldl stepW x := fun _ _ => rfl
  have hEval : ∀ (C : Circuit) (x : List Bool), C.eval x = (C.wires x).getD C.output false := fun _ _ => rfl
  have hStepLen : ∀ w gt, (stepW w gt).length = w.length + 1 := fun w gt => by simp [stepW]
  have hStepLt : ∀ w gt k, k < w.length → (stepW w gt).getD k false = w.getD k false :=
    fun w gt k hk => List.getD_append w _ false k hk
  have hStepOr : ∀ w a b, (stepW w ⟨GateOp.or, [a, b]⟩).getD w.length false =
      (w.getD a false || w.getD b false) := by
    intro w a b
    dsimp only [stepW]
    rw [List.getD_append_right w _ false w.length (le_refl _), Nat.sub_self]
    simp [hEvalOr]
  have hStepAnd : ∀ w a b, (stepW w ⟨GateOp.and, [a, b]⟩).getD w.length false =
      (w.getD a false && w.getD b false) := by
    intro w a b
    dsimp only [stepW]
    rw [List.getD_append_right w _ false w.length (le_refl _), Nat.sub_self]
    simp [hEvalAnd]
  let starGates : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List Gate := fun L p a b c d =>
    [⟨GateOp.or, [a, b]⟩, ⟨GateOp.or, [L, c]⟩, ⟨GateOp.or, [L + 1, d]⟩, ⟨GateOp.and, [p, L + 2]⟩]
  have hStar : ∀ (ws : List Bool) (L p a b c d : ℕ), ws.length = L →
      p < L → a < L → b < L → c < L → d < L →
      ((starGates L p a b c d).foldl stepW ws).length = L + 4 ∧
      (∀ k < L, ((starGates L p a b c d).foldl stepW ws).getD k false = ws.getD k false) ∧
      ((starGates L p a b c d).foldl stepW ws).getD (L + 3) false =
        (ws.getD p false && (ws.getD a false || ws.getD b false || ws.getD c false || ws.getD d false)) := by
    intro ws L p a b c d hL hp ha hb hc hd
    let w1 := stepW ws ⟨GateOp.or, [a, b]⟩
    let w2 := stepW w1 ⟨GateOp.or, [L, c]⟩
    let w3 := stepW w2 ⟨GateOp.or, [L + 1, d]⟩
    let w4 := stepW w3 ⟨GateOp.and, [p, L + 2]⟩
    have hl1 : w1.length = L + 1 := by rw [hStepLen, hL]
    have hl2 : w2.length = L + 2 := by rw [hStepLen, hl1]
    have hl3 : w3.length = L + 3 := by rw [hStepLen, hl2]
    have hl4 : w4.length = L + 4 := by rw [hStepLen, hl3]
    have hg1 : ∀ k < L, w1.getD k false = ws.getD k false := fun k hk => hStepLt ws _ k (by omega)
    have hg2 : ∀ k < L + 1, w2.getD k false = w1.getD k false := fun k hk => hStepLt w1 _ k (by omega)
    have hg3 : ∀ k < L + 2, w3.getD k false = w2.getD k false := fun k hk => hStepLt w2 _ k (by omega)
    have hg4 : ∀ k < L + 3, w4.getD k false = w3.getD k false := fun k hk => hStepLt w3 _ k (by omega)
    have hv1 : w1.getD L false = (ws.getD a false || ws.getD b false) := by
      have := hStepOr ws a b; rwa [hL] at this
    have hv2 : w2.getD (L + 1) false = (ws.getD a false || ws.getD b false || ws.getD c false) := by
      have := hStepOr w1 L c; rw [hl1] at this
      rw [this, hv1, hg1 c hc]
    have hv3 : w3.getD (L + 2) false =
        (ws.getD a false || ws.getD b false || ws.getD c false || ws.getD d false) := by
      have := hStepOr w2 (L + 1) d; rw [hl2] at this
      rw [this, hv2, hg2 d (by omega), hg1 d hd]
    have hv4 : w4.getD (L + 3) false =
        (ws.getD p false && (ws.getD a false || ws.getD b false || ws.getD c false || ws.getD d false)) := by
      have := hStepAnd w3 p (L + 2); rw [hl3] at this
      rw [this, hv3, hg3 p (by omega), hg2 p (by omega), hg1 p hp]
    change w4.length = L + 4 ∧ (∀ k < L, w4.getD k false = ws.getD k false) ∧ w4.getD (L + 3) false = _
    refine ⟨hl4, fun k hk => ?_, hv4⟩
    rw [hg4 k (by omega), hg3 k (by omega), hg2 k (by omega), hg1 k hk]
  have hStarM : ∀ L p a b c d, ∀ gt ∈ starGates L p a b c d,
      gt.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ gt.inputs.length ≤ 2 := by
    intro L p a b c d gt hgt
    simp only [starGates, List.mem_cons, List.not_mem_nil, or_false] at hgt
    rcases hgt with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩
  let tailGates : List Gate :=
    [⟨GateOp.or, [20, 24]⟩, ⟨GateOp.or, [41, 28]⟩, ⟨GateOp.or, [42, 32]⟩,
     ⟨GateOp.or, [43, 36]⟩, ⟨GateOp.or, [44, 40]⟩, ⟨GateOp.or, [15, 16]⟩]
  let gs2 : List Gate :=
    starGates 17 0 6 7 8 15 ++ starGates 21 1 9 10 11 15 ++ starGates 25 2 12 13 14 15 ++
    starGates 29 3 6 9 12 16 ++ starGates 33 4 7 10 13 16 ++ starGates 37 5 8 11 14 16 ++ tailGates
  let C2 : Circuit := ⟨gs2, 45⟩
  let q2 : ℕ := 46
  have hM2 : Monotone2 C2 := by
    intro gt hgt
    change gt ∈ gs2 at hgt
    simp only [gs2, List.mem_append] at hgt
    rcases hgt with (((((h | h) | h) | h) | h) | h) | h
    · exact hStarM _ _ _ _ _ _ gt h
    · exact hStarM _ _ _ _ _ _ gt h
    · exact hStarM _ _ _ _ _ _ gt h
    · exact hStarM _ _ _ _ _ _ gt h
    · exact hStarM _ _ _ _ _ _ gt h
    · exact hStarM _ _ _ _ _ _ gt h
    · simp only [tailGates, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩
  have hS2 : C2.size ≤ 30 := by decide
  have hO2 : C2.output < 17 + C2.size := by decide
  have hQ2 : q2 < 17 + C2.size := by decide
  have hEval2 : ∀ x : Fin 17 → Bool,
      (C2.eval (List.ofFn x) = true ↔ ∃ i j : Fin 17, H i j ∧ x i = true ∧ x j = true) ∧
      (C2.wires (List.ofFn x)).getD q2 false = (x 15 || x 16) := by
    intro x
    let v0 : List Bool := List.ofFn x
    have hl0 : v0.length = 17 := List.length_ofFn
    have hget0 : ∀ i : Fin 17, v0.getD i.val false = x i := by
      intro i
      rw [List.getD_eq_getElem _ _ (by rw [hl0]; exact i.isLt)]
      exact List.getElem_ofFn i.isLt
    let v1 := (starGates 17 0 6 7 8 15).foldl stepW v0
    let v2 := (starGates 21 1 9 10 11 15).foldl stepW v1
    let v3 := (starGates 25 2 12 13 14 15).foldl stepW v2
    let v4 := (starGates 29 3 6 9 12 16).foldl stepW v3
    let v5 := (starGates 33 4 7 10 13 16).foldl stepW v4
    let v6 := (starGates 37 5 8 11 14 16).foldl stepW v5
    obtain ⟨hl1, hp1, hv20⟩ := hStar v0 17 0 6 7 8 15 hl0 (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨hl2, hp2, hv24⟩ := hStar v1 21 1 9 10 11 15 hl1 (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨hl3, hp3, hv28⟩ := hStar v2 25 2 12 13 14 15 hl2 (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨hl4, hp4, hv32⟩ := hStar v3 29 3 6 9 12 16 hl3 (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨hl5, hp5, hv36⟩ := hStar v4 33 4 7 10 13 16 hl4 (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨hl6, hp6, hv40⟩ := hStar v5 37 5 8 11 14 16 hl5 (by omega) (by omega) (by omega) (by omega) (by omega)
    have h6_0 : ∀ k < 17, v6.getD k false = v0.getD k false := fun k hk => by
      rw [hp6 k (by omega), hp5 k (by omega), hp4 k (by omega), hp3 k (by omega), hp2 k (by omega), hp1 k hk]
    have hs0 : v6.getD 20 false = (x 0 && (x 6 || x 7 || x 8 || x 15)) := by
      rw [hp6 20 (by omega), hp5 20 (by omega), hp4 20 (by omega), hp3 20 (by omega), hp2 20 (by omega), hv20]
      exact congrArg₂ (· && ·) (hget0 0) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (hget0 6) (hget0 7)) (hget0 8)) (hget0 15))
    have hs1 : v6.getD 24 false = (x 1 && (x 9 || x 10 || x 11 || x 15)) := by
      rw [hp6 24 (by omega), hp5 24 (by omega), hp4 24 (by omega), hp3 24 (by omega), hv24,
        hp1 1 (by omega), hp1 9 (by omega), hp1 10 (by omega), hp1 11 (by omega), hp1 15 (by omega)]
      exact congrArg₂ (· && ·) (hget0 1) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (hget0 9) (hget0 10)) (hget0 11)) (hget0 15))
    have hs2 : v6.getD 28 false = (x 2 && (x 12 || x 13 || x 14 || x 15)) := by
      rw [hp6 28 (by omega), hp5 28 (by omega), hp4 28 (by omega), hv28,
        hp2 2 (by omega), hp2 12 (by omega), hp2 13 (by omega), hp2 14 (by omega), hp2 15 (by omega),
        hp1 2 (by omega), hp1 12 (by omega), hp1 13 (by omega), hp1 14 (by omega), hp1 15 (by omega)]
      exact congrArg₂ (· && ·) (hget0 2) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (hget0 12) (hget0 13)) (hget0 14)) (hget0 15))
    have hs3 : v6.getD 32 false = (x 3 && (x 6 || x 9 || x 12 || x 16)) := by
      rw [hp6 32 (by omega), hp5 32 (by omega), hv32,
        hp3 3 (by omega), hp3 6 (by omega), hp3 9 (by omega), hp3 12 (by omega), hp3 16 (by omega),
        hp2 3 (by omega), hp2 6 (by omega), hp2 9 (by omega), hp2 12 (by omega), hp2 16 (by omega),
        hp1 3 (by omega), hp1 6 (by omega), hp1 9 (by omega), hp1 12 (by omega), hp1 16 (by omega)]
      exact congrArg₂ (· && ·) (hget0 3) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (hget0 6) (hget0 9)) (hget0 12)) (hget0 16))
    have hs4 : v6.getD 36 false = (x 4 && (x 7 || x 10 || x 13 || x 16)) := by
      rw [hp6 36 (by omega), hv36,
        hp4 4 (by omega), hp4 7 (by omega), hp4 10 (by omega), hp4 13 (by omega), hp4 16 (by omega),
        hp3 4 (by omega), hp3 7 (by omega), hp3 10 (by omega), hp3 13 (by omega), hp3 16 (by omega),
        hp2 4 (by omega), hp2 7 (by omega), hp2 10 (by omega), hp2 13 (by omega), hp2 16 (by omega),
        hp1 4 (by omega), hp1 7 (by omega), hp1 10 (by omega), hp1 13 (by omega), hp1 16 (by omega)]
      exact congrArg₂ (· && ·) (hget0 4) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (hget0 7) (hget0 10)) (hget0 13)) (hget0 16))
    have hs5 : v6.getD 40 false = (x 5 && (x 8 || x 11 || x 14 || x 16)) := by
      rw [hv40,
        hp5 5 (by omega), hp5 8 (by omega), hp5 11 (by omega), hp5 14 (by omega), hp5 16 (by omega),
        hp4 5 (by omega), hp4 8 (by omega), hp4 11 (by omega), hp4 14 (by omega), hp4 16 (by omega),
        hp3 5 (by omega), hp3 8 (by omega), hp3 11 (by omega), hp3 14 (by omega), hp3 16 (by omega),
        hp2 5 (by omega), hp2 8 (by omega), hp2 11 (by omega), hp2 14 (by omega), hp2 16 (by omega),
        hp1 5 (by omega), hp1 8 (by omega), hp1 11 (by omega), hp1 14 (by omega), hp1 16 (by omega)]
      exact congrArg₂ (· && ·) (hget0 5) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (congrArg₂ (· || ·) (hget0 8) (hget0 11)) (hget0 14)) (hget0 16))
    let t1 := stepW v6 ⟨GateOp.or, [20, 24]⟩
    let t2 := stepW t1 ⟨GateOp.or, [41, 28]⟩
    let t3 := stepW t2 ⟨GateOp.or, [42, 32]⟩
    let t4 := stepW t3 ⟨GateOp.or, [43, 36]⟩
    let t5 := stepW t4 ⟨GateOp.or, [44, 40]⟩
    let t6 := stepW t5 ⟨GateOp.or, [15, 16]⟩
    have hl6' : v6.length = 41 := hl6
    have hlt1 : t1.length = 42 := by rw [hStepLen, hl6']
    have hlt2 : t2.length = 43 := by rw [hStepLen, hlt1]
    have hlt3 : t3.length = 44 := by rw [hStepLen, hlt2]
    have hlt4 : t4.length = 45 := by rw [hStepLen, hlt3]
    have hlt5 : t5.length = 46 := by rw [hStepLen, hlt4]
    have ht1 : t1.getD 41 false = (v6.getD 20 false || v6.getD 24 false) := by
      have := hStepOr v6 20 24; rwa [hl6] at this
    have ht2 : t2.getD 42 false = (v6.getD 20 false || v6.getD 24 false || v6.getD 28 false) := by
      have := hStepOr t1 41 28; rw [hlt1] at this
      rw [this, ht1, hStepLt v6 _ 28 (by omega)]
    have ht3 : t3.getD 43 false = (v6.getD 20 false || v6.getD 24 false || v6.getD 28 false || v6.getD 32 false) := by
      have := hStepOr t2 42 32; rw [hlt2] at this
      rw [this, ht2, hStepLt t1 _ 32 (by omega), hStepLt v6 _ 32 (by omega)]
    have ht4 : t4.getD 44 false = (v6.getD 20 false || v6.getD 24 false || v6.getD 28 false || v6.getD 32 false || v6.getD 36 false) := by
      have := hStepOr t3 43 36; rw [hlt3] at this
      rw [this, ht3, hStepLt t2 _ 36 (by omega), hStepLt t1 _ 36 (by omega), hStepLt v6 _ 36 (by omega)]
    have ht5 : t5.getD 45 false =
        (v6.getD 20 false || v6.getD 24 false || v6.getD 28 false || v6.getD 32 false || v6.getD 36 false || v6.getD 40 false) := by
      have := hStepOr t4 44 40; rw [hlt4] at this
      rw [this, ht4, hStepLt t3 _ 40 (by omega), hStepLt t2 _ 40 (by omega), hStepLt t1 _ 40 (by omega), hStepLt v6 _ 40 (by omega)]
    have ht6_45 : t6.getD 45 false = t5.getD 45 false := hStepLt t5 _ 45 (by omega)
    have ht6_46 : t6.getD 46 false = (x 15 || x 16) := by
      have := hStepOr t5 15 16; rw [hlt5] at this
      rw [this,
        hStepLt t4 _ 15 (by omega), hStepLt t3 _ 15 (by omega), hStepLt t2 _ 15 (by omega),
        hStepLt t1 _ 15 (by omega), hStepLt v6 _ 15 (by omega), h6_0 15 (by omega),
        hStepLt t4 _ 16 (by omega), hStepLt t3 _ 16 (by omega), hStepLt t2 _ 16 (by omega),
        hStepLt t1 _ 16 (by omega), hStepLt v6 _ 16 (by omega), h6_0 16 (by omega)]
      exact congrArg₂ (· || ·) (hget0 15) (hget0 16)
    have hWiresEq : C2.wires (List.ofFn x) = t6 := by
      rw [hWires]
      change gs2.foldl stepW v0 = t6
      simp only [gs2, tailGates, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    constructor
    · rw [hEval, hWiresEq]
      change t6.getD 45 false = true ↔ _
      rw [ht6_45, ht5, hs0, hs1, hs2, hs3, hs4, hs5]
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      constructor
      · intro h
        rcases h with (((((⟨h1, ((h2 | h2) | h2) | h2⟩ | ⟨h1, ((h2 | h2) | h2) | h2⟩) |
          ⟨h1, ((h2 | h2) | h2) | h2⟩) | ⟨h1, ((h2 | h2) | h2) | h2⟩) |
          ⟨h1, ((h2 | h2) | h2) | h2⟩) | ⟨h1, ((h2 | h2) | h2) | h2⟩)
        · exact ⟨0, 6, (hHChar 0 6).mpr (by simp), h1, h2⟩
        · exact ⟨0, 7, (hHChar 0 7).mpr (by simp), h1, h2⟩
        · exact ⟨0, 8, (hHChar 0 8).mpr (by simp), h1, h2⟩
        · exact ⟨0, 15, (hHChar 0 15).mpr (by simp), h1, h2⟩
        · exact ⟨1, 9, (hHChar 1 9).mpr (by simp), h1, h2⟩
        · exact ⟨1, 10, (hHChar 1 10).mpr (by simp), h1, h2⟩
        · exact ⟨1, 11, (hHChar 1 11).mpr (by simp), h1, h2⟩
        · exact ⟨1, 15, (hHChar 1 15).mpr (by simp), h1, h2⟩
        · exact ⟨2, 12, (hHChar 2 12).mpr (by simp), h1, h2⟩
        · exact ⟨2, 13, (hHChar 2 13).mpr (by simp), h1, h2⟩
        · exact ⟨2, 14, (hHChar 2 14).mpr (by simp), h1, h2⟩
        · exact ⟨2, 15, (hHChar 2 15).mpr (by simp), h1, h2⟩
        · exact ⟨3, 6, (hHChar 3 6).mpr (by simp), h1, h2⟩
        · exact ⟨3, 9, (hHChar 3 9).mpr (by simp), h1, h2⟩
        · exact ⟨3, 12, (hHChar 3 12).mpr (by simp), h1, h2⟩
        · exact ⟨3, 16, (hHChar 3 16).mpr (by simp), h1, h2⟩
        · exact ⟨4, 7, (hHChar 4 7).mpr (by simp), h1, h2⟩
        · exact ⟨4, 10, (hHChar 4 10).mpr (by simp), h1, h2⟩
        · exact ⟨4, 13, (hHChar 4 13).mpr (by simp), h1, h2⟩
        · exact ⟨4, 16, (hHChar 4 16).mpr (by simp), h1, h2⟩
        · exact ⟨5, 8, (hHChar 5 8).mpr (by simp), h1, h2⟩
        · exact ⟨5, 11, (hHChar 5 11).mpr (by simp), h1, h2⟩
        · exact ⟨5, 14, (hHChar 5 14).mpr (by simp), h1, h2⟩
        · exact ⟨5, 16, (hHChar 5 16).mpr (by simp), h1, h2⟩
      · intro h
        obtain ⟨i, j, hij, hxi, hxj⟩ := h
        rcases (hHChar i j).mp hij with
          ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ |
          ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ |
          ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ <;> simp [hxi, hxj]
    · rw [hWiresEq]; exact ht6_46
  obtain ⟨C1, q1, hM1, hS1, hO1, hQ1, hEval1⟩ := h_half29
  obtain ⟨B, r, hMB, hSB, hOB, hRB, hEvalB⟩ :=
    h_combine61 C1 q1 C2 q2 f g hM1 hM2 hS1 hS2 hO1 hQ1 hO2 hQ2
  refine ⟨B, r, hMB, hSB, hOB, hRB, ?_⟩
  intro x
  dsimp only
  obtain ⟨hBeval, hBaux⟩ := hEvalB x
  obtain ⟨hC1eval, hC1aux⟩ := hEval1 (fun i => x (f i))
  obtain ⟨hC2eval, hC2aux⟩ := hEval2 (fun i => x (g i))
  constructor
  · rw [hBeval, Bool.or_eq_true, hC1eval, hC2eval]
    constructor
    · intro h
      rcases h with ⟨a, b, ha1, ha2, hxa, hxb⟩ | ⟨a, b, hab, hxa, hxb⟩
      · exact ⟨f a, f b, (hLift a b ⟨ha1, ha2⟩).1, hxa, hxb⟩
      · exact ⟨g a, g b, (hLift a b hab).2, hxa, hxb⟩
    · intro h
      obtain ⟨i, j, hij, hxi, hxj⟩ := h
      rcases hCover i j hij with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
      · exact Or.inl ⟨a, b, hab.1, hab.2, hxi, hxj⟩
      · exact Or.inr ⟨a, b, hab, hxi, hxj⟩
  · intro hBf
    rw [hBeval, Bool.or_eq_false_iff] at hBf
    rw [hBaux, hC1aux hBf.1, hC2aux, hf15, hf16, hg15, hg16]
    cases x 12 <;> cases x 13 <;> cases x 15 <;> cases x 21 <;> rfl
