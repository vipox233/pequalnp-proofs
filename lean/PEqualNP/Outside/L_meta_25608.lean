import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25608_aux

def mix (x : Int → Bool) (z : Int) : Bool :=
  xor (xor (x (z - 1)) (x z)) (x (z + 1))

def evolve (x injection : Int → Bool) (z : Int) : Bool :=
  xor (xor (mix x z) (!(mix x (z + 1)) && mix x (z + 2))) (injection z)

def block (width : Nat) (tape : Int → Bool) (edge : Int) : Nat :=
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge + 1 + (bitIndex : Int))).toNat <<< bitIndex)) 0

def advance (w : Nat) (b : Int) (x inj : Int → Bool) (allowed : Nat) : Int × Nat :=
  let tails := (List.range (2 ^ (2 * w + 5))).filter (fun pattern => allowed.testBit (pattern % 2 ^ w))
  let trial := fun (completionCode : Nat) (site : Int) =>
    if site ≤ b then x site else completionCode.testBit (site - b - 1).toNat
  let reference := evolve x inj
  let fixed := fun (offset : Nat) =>
    let site := b - 2 + (offset : Int)
    tails.all (fun comparisonCode => evolve (trial comparisonCode) inj site == reference site)
  let newEdge := b - 3 + (((List.range (w + 5)).takeWhile fixed).length : Int)
  let newMask := tails.foldl (fun acc outputCode =>
    acc ||| ((1 : Nat) <<< block w (evolve (trial outputCode) inj) newEdge)) 0
  (newEdge, newMask)

theorem block_spec (tape : Int → Bool) (edge : Int) : ∀ w : Nat,
    block w tape edge < 2 ^ w ∧
    ∀ k : Nat, (block w tape edge).testBit k = if k < w then tape (edge + 1 + (k : Int)) else false := by
  intro w
  induction w with
  | zero =>
    refine ⟨by simp [block], fun k => by simp [block]⟩
  | succ w ih =>
    rcases ih with ⟨hlt, hbit⟩
    have hstep : block (w + 1) tape edge =
        block w tape edge ||| ((tape (edge + 1 + (w : Int))).toNat <<< w) := by
      dsimp only [block]
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    set bv : Bool := tape (edge + 1 + (w : Int))
    have hsh : (bv.toNat <<< w) < 2 ^ (w + 1) := by
      rw [Nat.shiftLeft_eq, Nat.pow_succ']
      cases bv <;> simp [Bool.toNat]
    have hlt1 : block w tape edge < 2 ^ (w + 1) :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨Nat.or_lt_two_pow hlt1 hsh, fun k => ?_⟩
    rw [Nat.testBit_or, hbit k, Nat.testBit_shiftLeft]
    by_cases hk : k < w
    · have hk1 : k < w + 1 := by omega
      simp only [hk, hk1, ↓reduceIte, decide_eq_false (show ¬ w ≤ k by omega), Bool.false_and, Bool.or_false]
    · by_cases hkeq : k = w
      · subst hkeq
        simp only [lt_irrefl, ↓reduceIte, Nat.lt_succ_self, ge_iff_le, le_refl, decide_true,
          Bool.true_and, Nat.sub_self, Bool.false_or]
        change bv.toNat.testBit 0 = bv
        cases bv <;> rfl
      · have hnot1 : ¬ k < w + 1 := by omega
        have hbm : bv.toNat.testBit (k - w) = false := by
          apply Nat.testBit_lt_two_pow
          have h1 : bv.toNat < 2 ^ 1 := by cases bv <;> decide
          exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
        simp only [hk, hnot1, ↓reduceIte, hbm, Bool.and_false, Bool.or_false]

theorem foldl_mask_testBit (l : List Nat) (f : Nat → Nat) (acc m : Nat) :
    (l.foldl (fun a c => a ||| ((1 : Nat) <<< f c)) acc).testBit m =
      (acc.testBit m || l.any (fun c => decide (f c = m))) := by
  induction l generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft, List.any_cons]
    have hbit1 : (decide (f c ≤ m) && (1 : Nat).testBit (m - f c)) = decide (f c = m) := by
      by_cases heq : f c = m
      · subst heq; simp
      · by_cases hle : f c ≤ m
        · have hpos : 1 ≤ m - f c := by omega
          have hz : (1 : Nat).testBit (m - f c) = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by omega) hpos))
          simp [heq, hle, hz]
        · simp [heq, hle]
    rw [hbit1, Bool.or_assoc]

theorem takeWhile_length_zero {n : Nat} (hn : 1 ≤ n) (p : Nat → Bool) (h0 : p 0 = false) :
    ((List.range n).takeWhile p).length = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    rw [List.range_succ_eq_map, List.takeWhile_cons, h0]
    rfl

theorem takeWhile_length_one {n : Nat} (hn : 2 ≤ n) (p : Nat → Bool)
    (h0 : p 0 = true) (h1 : p 1 = false) :
    ((List.range n).takeWhile p).length = 1 := by
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ k =>
      rw [List.range_succ_eq_map, List.takeWhile_cons, h0]
      simp only [List.range_succ_eq_map, List.map_cons, List.takeWhile_cons, h1]
      rfl

theorem takeWhile_length_two {n : Nat} (hn : 3 ≤ n) (p : Nat → Bool)
    (h0 : p 0 = true) (h1 : p 1 = true) (h2 : p 2 = false) :
    ((List.range n).takeWhile p).length = 2 := by
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ l =>
        rw [List.range_succ_eq_map, List.takeWhile_cons, h0]
        simp only [List.range_succ_eq_map, List.map_cons, List.takeWhile_cons, h1, h2]
        rfl

theorem evolve_congr {x1 x2 inj : Int → Bool} {z : Int}
    (hm1 : x1 (z - 1) = x2 (z - 1))
    (h0 : x1 z = x2 z)
    (hp1 : x1 (z + 1) = x2 (z + 1))
    (hp2 : x1 (z + 2) = x2 (z + 2))
    (hp3 : x1 (z + 3) = x2 (z + 3)) :
    evolve x1 inj z = evolve x2 inj z := by
  have hz1 : z + 1 - 1 = z := by omega
  have hz2 : z + 1 + 1 = z + 2 := by omega
  have hz3 : z + 2 - 1 = z + 1 := by omega
  have hz4 : z + 2 + 1 = z + 3 := by omega
  simp only [evolve, mix, hz1, hz2, hz3, hz4, hm1, h0, hp1, hp2, hp3]

theorem evolve_admissible_le {x first : Int → Bool} (hx : ∀ j ≤ (0 : Int), x j = false)
    {z : Int} (hz : z ≤ -3) :
    evolve x first z = first z := by
  have hm1 : x (z - 1) = false := hx (z - 1) (by omega)
  have h0 : x z = false := hx z (by omega)
  have hp1 : x (z + 1) = false := hx (z + 1) (by omega)
  have hp2 : x (z + 2) = false := hx (z + 2) (by omega)
  have hp3 : x (z + 3) = false := hx (z + 3) (by omega)
  have hz1 : z + 1 - 1 = z := by omega
  have hz2 : z + 1 + 1 = z + 2 := by omega
  have hz3 : z + 2 - 1 = z + 1 := by omega
  have hz4 : z + 2 + 1 = z + 3 := by omega
  simp [evolve, mix, hz1, hz2, hz3, hz4, hm1, h0, hp1, hp2, hp3]

theorem evolve_admissible_m2 {x first : Int → Bool} (hx : ∀ j ≤ (0 : Int), x j = false) :
    evolve x first (-2) = xor (first (-2)) (x 1) := by
  have h1 : x (-3) = false := hx (-3) (by omega)
  have h2 : x (-2) = false := hx (-2) (by omega)
  have h3 : x (-1) = false := hx (-1) (by omega)
  have h4 : x 0 = false := hx 0 (by omega)
  have he : evolve x first (-2) = xor (xor (mix x (-2)) (!(mix x (-1)) && mix x 0)) (first (-2)) := rfl
  rw [he]
  have hm2 : mix x (-2) = false := by simp [mix, h1, h2, h3]
  have hm1 : mix x (-1) = false := by simp [mix, h2, h3, h4]
  have hm0 : mix x 0 = x 1 := by simp [mix, h3, h4]
  rw [hm2, hm1, hm0]
  cases first (-2) <;> cases x 1 <;> rfl

theorem evolve_admissible_m1 {x first : Int → Bool} (hx : ∀ j ≤ (0 : Int), x j = false) :
    evolve x first (-1) = xor (first (-1)) (!(x 1) && x 2) := by
  have h2 : x (-2) = false := hx (-2) (by omega)
  have h3 : x (-1) = false := hx (-1) (by omega)
  have h4 : x 0 = false := hx 0 (by omega)
  have he : evolve x first (-1) = xor (xor (mix x (-1)) (!(mix x 0) && mix x 1)) (first (-1)) := rfl
  rw [he]
  have hm1 : mix x (-1) = false := by simp [mix, h2, h3, h4]
  have hm0 : mix x 0 = x 1 := by simp [mix, h3, h4]
  have hp1 : mix x 1 = xor (x 1) (x 2) := by simp [mix, h4]
  rw [hm1, hm0, hp1]
  cases first (-1) <;> cases x 1 <;> cases x 2 <;> rfl

theorem evolve_admissible_0_tt {x first : Int → Bool} (hx : ∀ j ≤ (0 : Int), x j = false)
    (hx1 : x 1 = true) (hx2 : x 2 = true) :
    evolve x first 0 = xor (first 0) (!(x 3)) := by
  have h3 : x (-1) = false := hx (-1) (by omega)
  have h4 : x 0 = false := hx 0 (by omega)
  have he : evolve x first 0 = xor (xor (mix x 0) (!(mix x 1) && mix x 2)) (first 0) := rfl
  rw [he]
  have hm0 : mix x 0 = true := by simp [mix, h3, h4, hx1]
  have hp1 : mix x 1 = false := by simp [mix, h4, hx1, hx2]
  have hp2 : mix x 2 = x 3 := by simp [mix, hx1, hx2]
  rw [hm0, hp1, hp2]
  cases first 0 <;> cases x 3 <;> rfl

theorem evolve_flat (first : Int → Bool) (z : Int) :
    evolve (fun _ => false) first z = first z := by
  simp [evolve, mix]

theorem not_missing_pair (f2 f1 a b : Bool) :
    ¬ (xor f2 a = !f2 ∧ xor f1 (!a && b) = !f1) := by
  cases f2 <;> cases f1 <;> cases a <;> cases b <;> decide

theorem second_m5_eq (y first second : Int → Bool)
    (h6 : y (-6) = first (-6)) (h5 : y (-5) = first (-5))
    (h4 : y (-4) = first (-4)) (h3 : y (-3) = first (-3)) :
    evolve y second (-5) =
      xor (xor (xor (xor (first (-6)) (first (-5))) (first (-4)))
        (!(xor (xor (first (-5)) (first (-4))) (first (-3))) &&
          xor (xor (first (-4)) (first (-3))) (y (-2)))) (second (-5)) := by
  have he : evolve y second (-5) = xor (xor (mix y (-5)) (!(mix y (-4)) && mix y (-3))) (second (-5)) := rfl
  rw [he]
  have hm5 : mix y (-5) = xor (xor (first (-6)) (first (-5))) (first (-4)) := by simp [mix, h6, h5, h4]
  have hm4 : mix y (-4) = xor (xor (first (-5)) (first (-4))) (first (-3)) := by simp [mix, h5, h4, h3]
  have hm3 : mix y (-3) = xor (xor (first (-4)) (first (-3))) (y (-2)) := by simp [mix, h4, h3]
  rw [hm5, hm4, hm3]

theorem second_m4_eq (y first second : Int → Bool)
    (h5 : y (-5) = first (-5)) (h4 : y (-4) = first (-4)) (h3 : y (-3) = first (-3)) :
    evolve y second (-4) =
      xor (xor (xor (xor (first (-5)) (first (-4))) (first (-3)))
        (!(xor (xor (first (-4)) (first (-3))) (y (-2))) &&
          xor (xor (first (-3)) (y (-2))) (y (-1)))) (second (-4)) := by
  have he : evolve y second (-4) = xor (xor (mix y (-4)) (!(mix y (-3)) && mix y (-2))) (second (-4)) := rfl
  rw [he]
  have hm4 : mix y (-4) = xor (xor (first (-5)) (first (-4))) (first (-3)) := by simp [mix, h5, h4, h3]
  have hm3 : mix y (-3) = xor (xor (first (-4)) (first (-3))) (y (-2)) := by simp [mix, h4, h3]
  have hm2 : mix y (-2) = xor (xor (first (-3)) (y (-2))) (y (-1)) := by simp [mix, h3]
  rw [hm4, hm3, hm2]

theorem second_m3_eq (y first second : Int → Bool)
    (h4 : y (-4) = first (-4)) (h3 : y (-3) = first (-3)) :
    evolve y second (-3) =
      xor (xor (xor (xor (first (-4)) (first (-3))) (y (-2)))
        (!(xor (xor (first (-3)) (y (-2))) (y (-1))) &&
          xor (xor (y (-2)) (y (-1))) (y 0))) (second (-3)) := by
  have he : evolve y second (-3) = xor (xor (mix y (-3)) (!(mix y (-2)) && mix y (-1))) (second (-3)) := rfl
  rw [he]
  have hm3 : mix y (-3) = xor (xor (first (-4)) (first (-3))) (y (-2)) := by simp [mix, h4, h3]
  have hm2 : mix y (-2) = xor (xor (first (-3)) (y (-2))) (y (-1)) := by simp [mix, h3]
  have hm1 : mix y (-1) = xor (xor (y (-2)) (y (-1))) (y 0) := by simp [mix]
  rw [hm3, hm2, hm1]

theorem term_m4_iff (f4 f3 A B : Bool) :
    (!(xor (xor f4 f3) A) && xor (xor f3 A) B) = true ↔ A = xor f4 f3 ∧ B = (!f4) := by
  cases f4 <;> cases f3 <;> cases A <;> cases B <;> decide

theorem hidden_iff (f4 f3 f2 f1 : Bool) :
    ((xor f4 f3 == !f2) && (f4 == f1)) = true ↔ xor f4 f3 = (!f2) ∧ (!f4) = (!f1) := by
  cases f4 <;> cases f3 <;> cases f2 <;> cases f1 <;> decide

theorem hidden_mix_m2 (f4 f3 f2 f1 : Bool)
    (hh : ((xor f4 f3 == !f2) && (f4 == f1)) = true) :
    xor (xor f3 (!f2)) f1 = false := by
  cases f4 <;> cases f3 <;> cases f2 <;> cases f1 <;> simp_all

theorem xor_neq_of_mid_neq (p q r s : Bool) (h : q ≠ r) :
    xor (xor p q) s ≠ xor (xor p r) s := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp_all

theorem m5_neq_of_guard_false (f6 f5 f4 f3 f2 s5 y2 : Bool)
    (hg : xor (xor f5 f4) f3 = false) (hy : y2 ≠ f2) :
    xor (xor (xor (xor f6 f5) f4) (!(xor (xor f5 f4) f3) && xor (xor f4 f3) y2)) s5 ≠
    xor (xor (xor (xor f6 f5) f4) (!(xor (xor f5 f4) f3) && xor (xor f4 f3) f2)) s5 := by
  rw [hg]
  cases f6 <;> cases f5 <;> cases f4 <;> cases f3 <;> cases f2 <;> cases s5 <;> cases y2 <;> simp_all

theorem m3_neq_of_mix_m2_false (f4 f3 y2 y1 s3 y0A y0B : Bool)
    (hmix : xor (xor f3 y2) y1 = false) (hy0 : y0A ≠ y0B) :
    xor (xor (xor (xor f4 f3) y2) (!(xor (xor f3 y2) y1) && xor (xor y2 y1) y0A)) s3 ≠
    xor (xor (xor (xor f4 f3) y2) (!(xor (xor f3 y2) y1) && xor (xor y2 y1) y0B)) s3 := by
  rw [hmix]
  cases f4 <;> cases f3 <;> cases y2 <;> cases y1 <;> cases s3 <;> cases y0A <;> cases y0B <;> simp_all

theorem hex_c_m4 (f4 f3 f2 f1 : Bool) :
    ∃ c < 4,
      (!(xor (xor f4 f3) (c.testBit 0)) && xor (xor f3 (c.testBit 0)) (c.testBit 1)) ≠
      (!(xor (xor f4 f3) f2) && xor (xor f3 f2) f1) := by
  cases f4 <;> cases f3 <;> cases f2 <;> cases f1
  all_goals first
    | exact ⟨0, by decide, by decide⟩
    | exact ⟨1, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩
    | exact ⟨3, by decide, by decide⟩

theorem hex_ab_m4 (f4 f3 f2 f1 : Bool)
    (hh : ((xor f4 f3 == !f2) && (f4 == f1)) = false) :
    ∃ a b : Bool,
      (!(xor (xor f4 f3) (xor f2 a)) && xor (xor f3 (xor f2 a)) (xor f1 (!a && b))) ≠
      (!(xor (xor f4 f3) f2) && xor (xor f3 f2) f1) := by
  cases f4 <;> cases f3 <;> cases f2 <;> cases f1
  all_goals first
    | exact ⟨false, true, by decide⟩
    | exact ⟨true, false, by decide⟩
    | simp at hh

theorem hidden_term_m4_false (f4 f3 f2 f1 a b : Bool)
    (hh : ((xor f4 f3 == !f2) && (f4 == f1)) = true) :
    (!(xor (xor f4 f3) (xor f2 a)) && xor (xor f3 (xor f2 a)) (xor f1 (!a && b))) = false := by
  cases f4 <;> cases f3 <;> cases f2 <;> cases f1 <;> cases a <;> cases b <;> simp_all

theorem part1_proof (first second : Int → Bool) :
    let flat : Int → Bool := fun _ => false
    let admissible := fun (x : Int → Bool) => ∀ j ≤ (0 : Int), x j = false
    let physical := fun (x : Int → Bool) => evolve (evolve x first) second
    let guard := xor (xor (first (-5)) (first (-4))) (first (-3))
    let hidden := (xor (first (-4)) (first (-3)) == !(first (-2))) &&
      (first (-4) == first (-1))
    let E : Int := if guard then (if hidden then -4 else -5) else -6
    ∀ x, admissible x → ∀ j ≤ E, physical x j = physical flat j := by
  intro flat admissible physical guard hidden E
  have hflat_adm : admissible flat := fun _ _ => rfl
  have hphys_le6 : ∀ x, admissible x → ∀ j ≤ (-6 : Int), physical x j = physical flat j := by
    intro x hx j hj
    apply evolve_congr
    · rw [evolve_admissible_le hx (by omega), evolve_admissible_le hflat_adm (by omega)]
    · rw [evolve_admissible_le hx (by omega), evolve_admissible_le hflat_adm (by omega)]
    · rw [evolve_admissible_le hx (by omega), evolve_admissible_le hflat_adm (by omega)]
    · rw [evolve_admissible_le hx (by omega), evolve_admissible_le hflat_adm (by omega)]
    · rw [evolve_admissible_le hx (by omega), evolve_admissible_le hflat_adm (by omega)]
  have hphys_m5_guard : guard = true → ∀ x, admissible x → physical x (-5) = physical flat (-5) := by
    intro hg x hx
    dsimp only [physical]
    rw [second_m5_eq (evolve x first) first second
        (evolve_admissible_le hx (by omega)) (evolve_admissible_le hx (by omega))
        (evolve_admissible_le hx (by omega)) (evolve_admissible_le hx (by omega))]
    rw [second_m5_eq (evolve flat first) first second
        (evolve_admissible_le hflat_adm (by omega)) (evolve_admissible_le hflat_adm (by omega))
        (evolve_admissible_le hflat_adm (by omega)) (evolve_admissible_le hflat_adm (by omega))]
    have hg' : xor (xor (first (-5)) (first (-4))) (first (-3)) = true := hg
    rw [hg']
    simp
  have hphys_m4_hidden : hidden = true → ∀ x, admissible x → physical x (-4) = physical flat (-4) := by
    intro hh x hx
    dsimp only [physical]
    rw [second_m4_eq (evolve x first) first second
        (evolve_admissible_le hx (by omega)) (evolve_admissible_le hx (by omega))
        (evolve_admissible_le hx (by omega))]
    rw [second_m4_eq (evolve flat first) first second
        (evolve_admissible_le hflat_adm (by omega)) (evolve_admissible_le hflat_adm (by omega))
        (evolve_admissible_le hflat_adm (by omega))]
    rw [evolve_admissible_m2 hx, evolve_admissible_m1 hx, evolve_admissible_m2 hflat_adm, evolve_admissible_m1 hflat_adm]
    rw [hidden_term_m4_false (first (-4)) (first (-3)) (first (-2)) (first (-1)) (x 1) (x 2) hh]
    rw [hidden_term_m4_false (first (-4)) (first (-3)) (first (-2)) (first (-1)) (flat 1) (flat 2) hh]
  intro x hx j hj
  cases hg : guard
  · have hE : E = -6 := by simp [E, hg]
    rw [hE] at hj
    exact hphys_le6 x hx j hj
  · cases hh : hidden
    · have hE : E = -5 := by simp [E, hg, hh]
      rw [hE] at hj
      by_cases hj6 : j ≤ -6
      · exact hphys_le6 x hx j hj6
      · have hjm5 : j = -5 := by omega
        subst hjm5
        exact hphys_m5_guard hg x hx
    · have hE : E = -4 := by simp [E, hg, hh]
      rw [hE] at hj
      by_cases hj6 : j ≤ -6
      · exact hphys_le6 x hx j hj6
      · by_cases hjm5 : j = -5
        · subst hjm5; exact hphys_m5_guard hg x hx
        · have hjm4 : j = -4 := by omega
          subst hjm4; exact hphys_m4_hidden hh x hx

theorem part2_proof (first second : Int → Bool) :
    let flat : Int → Bool := fun _ => false
    let admissible := fun (x : Int → Bool) => ∀ j ≤ (0 : Int), x j = false
    let physical := fun (x : Int → Bool) => evolve (evolve x first) second
    let guard := xor (xor (first (-5)) (first (-4))) (first (-3))
    let hidden := (xor (first (-4)) (first (-3)) == !(first (-2))) &&
      (first (-4) == first (-1))
    let E : Int := if guard then (if hidden then -4 else -5) else -6
    ∃ x, admissible x ∧ physical x (E + 1) ≠ physical flat (E + 1) := by
  intro flat admissible physical guard hidden E
  have hflat_adm : admissible flat := fun _ _ => rfl
  cases hg : guard
  · have hE : E + 1 = -5 := by simp [E, hg]
    rw [hE]
    let x : Int → Bool := fun j => decide (j = 1)
    have hx : admissible x := fun j hj => by simp [x]; omega
    refine ⟨x, hx, ?_⟩
    dsimp only [physical]
    rw [second_m5_eq (evolve x first) first second
        (evolve_admissible_le hx (by omega)) (evolve_admissible_le hx (by omega))
        (evolve_admissible_le hx (by omega)) (evolve_admissible_le hx (by omega))]
    rw [second_m5_eq (evolve flat first) first second
        (evolve_admissible_le hflat_adm (by omega)) (evolve_admissible_le hflat_adm (by omega))
        (evolve_admissible_le hflat_adm (by omega)) (evolve_admissible_le hflat_adm (by omega))]
    rw [evolve_admissible_m2 hx, evolve_admissible_m2 hflat_adm]
    have hx1 : x 1 = true := rfl
    have hf1 : flat 1 = false := rfl
    rw [hx1, hf1, Bool.xor_false]
    apply m5_neq_of_guard_false _ _ _ _ _ _ _ hg
    cases first (-2) <;> decide
  · cases hh : hidden
    · have hE : E + 1 = -4 := by simp [E, hg, hh]
      rw [hE]
      rcases hex_ab_m4 (first (-4)) (first (-3)) (first (-2)) (first (-1)) hh with ⟨a, b, hab⟩
      let x : Int → Bool := fun j => if j = 1 then a else if j = 2 then b else false
      have hx : admissible x := fun j hj => by simp [x, show j ≠ 1 by omega, show j ≠ 2 by omega]
      refine ⟨x, hx, ?_⟩
      dsimp only [physical]
      rw [second_m4_eq (evolve x first) first second
          (evolve_admissible_le hx (by omega)) (evolve_admissible_le hx (by omega))
          (evolve_admissible_le hx (by omega))]
      rw [second_m4_eq (evolve flat first) first second
          (evolve_admissible_le hflat_adm (by omega)) (evolve_admissible_le hflat_adm (by omega))
          (evolve_admissible_le hflat_adm (by omega))]
      rw [evolve_admissible_m2 hx, evolve_admissible_m1 hx, evolve_admissible_m2 hflat_adm, evolve_admissible_m1 hflat_adm]
      have hx1 : x 1 = a := rfl
      have hx2 : x 2 = b := rfl
      simp only [hx1, hx2, flat, Bool.not_false, Bool.true_and, Bool.xor_false]
      exact xor_neq_of_mid_neq _ _ _ _ hab
    · have hE : E + 1 = -3 := by simp [E, hg, hh]
      rw [hE]
      let x0 : Int → Bool := fun j => if j = 1 then true else if j = 2 then true else false
      let x1 : Int → Bool := fun j => if j = 1 then true else if j = 2 then true else if j = 3 then true else false
      have hx0 : admissible x0 := fun j hj => by simp [x0, show j ≠ 1 by omega, show j ≠ 2 by omega]
      have hx1 : admissible x1 := fun j hj => by simp [x1, show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 3 by omega]
      have hdiff : physical x0 (-3) ≠ physical x1 (-3) := by
        dsimp only [physical]
        rw [second_m3_eq (evolve x0 first) first second
            (evolve_admissible_le hx0 (by omega)) (evolve_admissible_le hx0 (by omega))]
        rw [second_m3_eq (evolve x1 first) first second
            (evolve_admissible_le hx1 (by omega)) (evolve_admissible_le hx1 (by omega))]
        rw [evolve_admissible_m2 hx0, evolve_admissible_m1 hx0, evolve_admissible_0_tt hx0 rfl rfl]
        rw [evolve_admissible_m2 hx1, evolve_admissible_m1 hx1, evolve_admissible_0_tt hx1 rfl rfl]
        have h01 : x0 1 = true := rfl
        have h02 : x0 2 = true := rfl
        have h03 : x0 3 = false := rfl
        have h11 : x1 1 = true := rfl
        have h12 : x1 2 = true := rfl
        have h13 : x1 3 = true := rfl
        rw [h01, h02, h03, h11, h12, h13]
        simp only [Bool.xor_true, Bool.not_true, Bool.false_and, Bool.xor_false, Bool.not_false]
        apply m3_neq_of_mix_m2_false _ _ _ _ _ _ _
          (hidden_mix_m2 (first (-4)) (first (-3)) (first (-2)) (first (-1)) hh)
        cases first 0 <;> decide
      by_cases hne0 : physical x0 (-3) ≠ physical flat (-3)
      · exact ⟨x0, hx0, hne0⟩
      · refine ⟨x1, hx1, ?_⟩
        intro heq1
        apply hdiff
        exact (Classical.not_not.mp hne0).trans heq1.symm

theorem part3_proof (first second : Int → Bool) (w : Nat) :
    let flat : Int → Bool := fun _ => false
    let guard := xor (xor (first (-5)) (first (-4))) (first (-3))
    let hidden := (xor (first (-4)) (first (-3)) == !(first (-2))) &&
      (first (-4) == first (-1))
    let E : Int := if guard then (if hidden then -4 else -5) else -6
    let allWords := 2 ^ (2 ^ w) - 1
    let one := advance w 0 flat first allWords
    let two := advance w one.1 (evolve flat first) second one.2
    one.1 = -3 ∧
    two.1 = (if w < 2 ∧ guard = true then (-5 : Int) else E) := by
  intro flat guard hidden E allWords one two
  have hflat_adm : ∀ j ≤ (0 : Int), flat j = false := fun _ _ => rfl
  have hall_lt : ∀ p : Nat, allWords.testBit (p % 2 ^ w) = true := by
    intro p
    dsimp only [allWords]
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (Nat.mod_lt p (Nat.two_pow_pos w))
  have hpow_ge : 32 ≤ 2 ^ (2 * w + 5) :=
    le_trans (by norm_num : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by omega) (by omega))
  have htails1 : (List.range (2 ^ (2 * w + 5))).filter (fun p => allWords.testBit (p % 2 ^ w)) =
      List.range (2 ^ (2 * w + 5)) := by
    apply List.filter_eq_self.mpr
    intro p _; exact hall_lt p
  have htrial1_adm : ∀ code : Nat, ∀ j ≤ (0 : Int),
      (if j ≤ 0 then flat j else code.testBit (j - 0 - 1).toNat) = false := by
    intro code j hj; simp [hj, flat]
  let fixed1 : Nat → Bool := fun offset =>
    (List.range (2 ^ (2 * w + 5))).all (fun comparisonCode =>
      evolve (fun site => if site ≤ 0 then flat site else comparisonCode.testBit (site - 0 - 1).toNat) first
        (0 - 2 + (offset : Int)) == evolve flat first (0 - 2 + (offset : Int)))
  have hf1_0 : fixed1 0 = false := by
    apply List.all_eq_false.mpr
    refine ⟨1, List.mem_range.mpr (by omega), ?_⟩
    have hs : (0 : Int) - 2 + ((0 : Nat) : Int) = -2 := by omega
    rw [hs, evolve_admissible_m2 (htrial1_adm 1), evolve_admissible_m2 hflat_adm]
    have h1 : (if (1 : Int) ≤ 0 then flat 1 else (1 : Nat).testBit ((1 : Int) - 0 - 1).toNat) = true := by decide
    have h0 : flat 1 = false := rfl
    rw [h1, h0]
    cases first (-2) <;> decide
  have hlen1 : ((List.range (w + 5)).takeWhile fixed1).length = 0 :=
    takeWhile_length_zero (n := w + 5) (by omega) fixed1 hf1_0
  have hone1 : one.1 = -3 := by
    dsimp only [one, advance]
    rw [htails1]
    change (0 : Int) - 3 + (((List.range (w + 5)).takeWhile fixed1).length : Int) = -3
    rw [hlen1]; omega
  refine ⟨hone1, ?_⟩
  have hone2_iff : ∀ m : Nat, one.2.testBit m = true ↔
      ∃ c1 < 2 ^ (2 * w + 5),
        block w (evolve (fun site => if site ≤ 0 then flat site else c1.testBit (site - 0 - 1).toNat) first) (-3) = m := by
    intro m
    dsimp only [one, advance]
    rw [htails1]
    have hne : (0 : Int) - 3 + (((List.range (w + 5)).takeWhile fixed1).length : Int) = -3 := by
      rw [hlen1]; omega
    change ((List.range (2 ^ (2 * w + 5))).foldl (fun acc outputCode =>
      acc ||| ((1 : Nat) <<< block w (evolve (fun site => if site ≤ 0 then flat site else outputCode.testBit (site - 0 - 1).toNat) first)
        ((0 : Int) - 3 + (((List.range (w + 5)).takeWhile fixed1).length : Int)))) 0).testBit m = true ↔ _
    rw [hne, foldl_mask_testBit]
    simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  have hmem_t2 : ∀ code : Nat, code < 2 ^ (2 * w + 5) → one.2.testBit (code % 2 ^ w) = true →
      code ∈ (List.range (2 ^ (2 * w + 5))).filter (fun pattern => one.2.testBit (pattern % 2 ^ w)) := by
    intro code hlt htb
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hlt, htb⟩
  have hpow_w_lt : 2 ^ w < 2 ^ (2 * w + 5) := Nat.pow_lt_pow_right (by omega) (by omega)
  let tr2 : Nat → Int → Bool := fun code site =>
    if site ≤ -3 then evolve flat first site else code.testBit (site - (-3) - 1).toNat
  have htr2_le : ∀ code (j : Int), j ≤ -3 → tr2 code j = first j := by
    intro code j hj
    simp only [tr2, hj, ↓reduceIte]
    exact evolve_flat first j
  have htr2_m2 : ∀ code, tr2 code (-2) = code.testBit 0 := by intro code; simp [tr2]
  have htr2_m1 : ∀ code, tr2 code (-1) = code.testBit 1 := by intro code; simp [tr2]
  have htr2_0 : ∀ code, tr2 code 0 = code.testBit 2 := by intro code; simp [tr2]
  let tails2 := (List.range (2 ^ (2 * w + 5))).filter (fun pattern => one.2.testBit (pattern % 2 ^ w))
  let fixed2 : Nat → Bool := fun offset =>
    tails2.all (fun code => evolve (tr2 code) second (-3 - 2 + (offset : Int)) ==
      evolve (evolve flat first) second (-3 - 2 + (offset : Int)))
  have htwo_eq : two.1 = -3 - 3 + (((List.range (w + 5)).takeWhile fixed2).length : Int) := by
    dsimp only [two, advance]
    rw [hone1]
  rw [htwo_eq]
  have hf2_0_true : guard = true → fixed2 0 = true := by
    intro hg
    apply List.all_eq_true.mpr
    intro code _
    have hs : (-3 : Int) - 2 + ((0 : Nat) : Int) = -5 := by omega
    rw [hs, beq_iff_eq]
    rw [second_m5_eq (tr2 code) first second
        (htr2_le code (-6) (by omega)) (htr2_le code (-5) (by omega))
        (htr2_le code (-4) (by omega)) (htr2_le code (-3) (by omega))]
    rw [second_m5_eq (evolve flat first) first second
        (evolve_flat first (-6)) (evolve_flat first (-5))
        (evolve_flat first (-4)) (evolve_flat first (-3))]
    have hg' : xor (xor (first (-5)) (first (-4))) (first (-3)) = true := hg
    rw [hg']; simp
  have hf2_0_false : guard = false → fixed2 0 = false := by
    intro hg
    apply List.all_eq_false.mpr
    have hex_code : ∃ code ∈ tails2, code.testBit 0 = !(first (-2)) := by
      by_cases hw0 : w = 0
      · subst hw0
        have hm0 : one.2.testBit 0 = true := (hone2_iff 0).mpr ⟨0, by omega, by simp [block]⟩
        by_cases hf2 : first (-2)
        · refine ⟨0, hmem_t2 0 (by omega) (by rw [Nat.pow_zero, Nat.mod_one]; exact hm0), by simp [hf2]⟩
        · refine ⟨1, hmem_t2 1 (by omega) (by rw [Nat.pow_zero, Nat.mod_one]; exact hm0), by simp [hf2]⟩
      · have hw1 : 0 < w := by omega
        let m1 := block w (evolve (fun site => if site ≤ 0 then flat site else (1 : Nat).testBit (site - 0 - 1).toNat) first) (-3)
        have hm1_lt : m1 < 2 ^ w := (block_spec _ _ w).1
        have hm1_tb : one.2.testBit m1 = true := (hone2_iff m1).mpr ⟨1, by omega, rfl⟩
        refine ⟨m1, hmem_t2 m1 (lt_trans hm1_lt hpow_w_lt) (by rw [Nat.mod_eq_of_lt hm1_lt]; exact hm1_tb), ?_⟩
        have hb0 := (block_spec (evolve (fun site => if site ≤ 0 then flat site else (1 : Nat).testBit (site - 0 - 1).toNat) first) (-3) w).2 0
        simp only [hw1, ↓reduceIte] at hb0
        have hidx : (-3 : Int) + 1 + ((0 : Nat) : Int) = -2 := by omega
        rw [hidx, evolve_admissible_m2 (htrial1_adm 1)] at hb0
        have hbit : (if (1 : Int) ≤ 0 then flat 1 else (1 : Nat).testBit ((1 : Int) - 0 - 1).toNat) = true := by decide
        rw [hbit] at hb0
        simpa [m1] using hb0
    rcases hex_code with ⟨code, hcmem, hc0⟩
    refine ⟨code, hcmem, ?_⟩
    have hs : (-3 : Int) - 2 + ((0 : Nat) : Int) = -5 := by omega
    rw [hs, beq_iff_eq]
    rw [second_m5_eq (tr2 code) first second
        (htr2_le code (-6) (by omega)) (htr2_le code (-5) (by omega))
        (htr2_le code (-4) (by omega)) (htr2_le code (-3) (by omega))]
    rw [second_m5_eq (evolve flat first) first second
        (evolve_flat first (-6)) (evolve_flat first (-5))
        (evolve_flat first (-4)) (evolve_flat first (-3))]
    rw [htr2_m2, hc0, evolve_flat]
    apply m5_neq_of_guard_false _ _ _ _ _ _ _ hg
    cases first (-2) <;> decide
  cases hg : guard
  · have hlen := takeWhile_length_zero (n := w + 5) (by omega) fixed2 (hf2_0_false hg)
    simp [E, hg, hlen]
  · by_cases hw2 : w < 2
    · have hall4 : ∀ c < 4, c ∈ tails2 := by
        intro c hc
        have hw_cases : w = 0 ∨ w = 1 := by omega
        rcases hw_cases with rfl | rfl
        · have hm0 : one.2.testBit 0 = true := (hone2_iff 0).mpr ⟨0, by omega, by simp [block]⟩
          exact hmem_t2 c (by omega) (by rw [Nat.pow_zero, Nat.mod_one]; exact hm0)
        · have hm_all : ∀ b : Bool, one.2.testBit b.toNat = true := by
            intro b
            let c1 := (xor b (first (-2))).toNat
            have hc1_lt : c1 < 2 ^ (2 * 1 + 5) := by
              dsimp only [c1]
              generalize first (-2) = f2
              cases b <;> cases f2 <;> decide
            apply (hone2_iff b.toNat).mpr
            refine ⟨c1, hc1_lt, ?_⟩
            apply Nat.eq_of_testBit_eq
            intro k
            rw [(block_spec _ _ 1).2 k]
            by_cases hk : k = 0
            · subst hk
              simp only [Nat.lt_one_iff, ↓reduceIte]
              have hidx : (-3 : Int) + 1 + ((0 : Nat) : Int) = -2 := by omega
              rw [hidx, evolve_admissible_m2 (htrial1_adm c1)]
              have h1 : (if (1 : Int) ≤ 0 then flat 1 else c1.testBit ((1 : Int) - 0 - 1).toNat) = xor b (first (-2)) := by
                dsimp only [c1]; generalize first (-2) = f2; cases b <;> cases f2 <;> decide
              rw [h1]
              generalize first (-2) = f2; cases b <;> cases f2 <;> decide
            · have hk1 : ¬ k < 1 := by omega
              simp only [hk1, ↓reduceIte]
              symm
              apply Nat.testBit_lt_two_pow
              have hbl : b.toNat < 2 ^ 1 := by cases b <;> decide
              exact lt_of_lt_of_le hbl (Nat.pow_le_pow_right (by omega) (by omega))
          have hmod : c % 2 ^ 1 = 0 ∨ c % 2 ^ 1 = 1 := by omega
          refine hmem_t2 c (by omega) ?_
          rcases hmod with h0 | h1
          · rw [h0]; exact hm_all false
          · rw [h1]; exact hm_all true
      have hf2_1_false : fixed2 1 = false := by
        apply List.all_eq_false.mpr
        rcases hex_c_m4 (first (-4)) (first (-3)) (first (-2)) (first (-1)) with ⟨c, hc4, hcdiff⟩
        refine ⟨c, hall4 c hc4, ?_⟩
        have hs : (-3 : Int) - 2 + ((1 : Nat) : Int) = -4 := by omega
        rw [hs, beq_iff_eq]
        rw [second_m4_eq (tr2 c) first second
            (htr2_le c (-5) (by omega)) (htr2_le c (-4) (by omega)) (htr2_le c (-3) (by omega))]
        rw [second_m4_eq (evolve flat first) first second
            (evolve_flat first (-5)) (evolve_flat first (-4)) (evolve_flat first (-3))]
        rw [htr2_m2, htr2_m1, evolve_flat, evolve_flat]
        exact xor_neq_of_mid_neq _ _ _ _ hcdiff
      have hlen := takeWhile_length_one (n := w + 5) (by omega) fixed2 (hf2_0_true hg) hf2_1_false
      simp [hw2, hlen]
    · have hw_ge2 : 2 ≤ w := by omega
      cases hh : hidden
      · have hf2_1_false : fixed2 1 = false := by
          apply List.all_eq_false.mpr
          rcases hex_ab_m4 (first (-4)) (first (-3)) (first (-2)) (first (-1)) hh with ⟨a, b, hab⟩
          let c1 := a.toNat + 2 * b.toNat
          have hc1_lt : c1 < 2 ^ (2 * w + 5) := by
            have : c1 < 4 := by dsimp [c1]; cases a <;> cases b <;> decide
            omega
          let m1 := block w (evolve (fun site => if site ≤ 0 then flat site else c1.testBit (site - 0 - 1).toNat) first) (-3)
          have hm1_lt : m1 < 2 ^ w := (block_spec _ _ w).1
          have hm1_mem : m1 ∈ tails2 :=
            hmem_t2 m1 (lt_trans hm1_lt hpow_w_lt) (by rw [Nat.mod_eq_of_lt hm1_lt]; exact (hone2_iff m1).mpr ⟨c1, hc1_lt, rfl⟩)
          have hm1_b0 : m1.testBit 0 = xor (first (-2)) a := by
            rw [(block_spec _ (-3) w).2 0]
            simp only [show 0 < w by omega, ↓reduceIte]
            have hidx : (-3 : Int) + 1 + ((0 : Nat) : Int) = -2 := by omega
            rw [hidx, evolve_admissible_m2 (htrial1_adm c1)]
            have ha1 : (if (1 : Int) ≤ 0 then flat 1 else c1.testBit ((1 : Int) - 0 - 1).toNat) = a := by
              dsimp only [c1]; cases a <;> cases b <;> decide
            rw [ha1]
          have hm1_b1 : m1.testBit 1 = xor (first (-1)) (!a && b) := by
            rw [(block_spec _ (-3) w).2 1]
            simp only [show 1 < w by omega, ↓reduceIte]
            have hidx : (-3 : Int) + 1 + ((1 : Nat) : Int) = -1 := by omega
            rw [hidx, evolve_admissible_m1 (htrial1_adm c1)]
            have ha1 : (if (1 : Int) ≤ 0 then flat 1 else c1.testBit ((1 : Int) - 0 - 1).toNat) = a := by
              dsimp only [c1]; cases a <;> cases b <;> decide
            have hb2 : (if (2 : Int) ≤ 0 then flat 2 else c1.testBit ((2 : Int) - 0 - 1).toNat) = b := by
              dsimp only [c1]; cases a <;> cases b <;> decide
            rw [ha1, hb2]
          refine ⟨m1, hm1_mem, ?_⟩
          have hs : (-3 : Int) - 2 + ((1 : Nat) : Int) = -4 := by omega
          rw [hs, beq_iff_eq]
          rw [second_m4_eq (tr2 m1) first second
              (htr2_le m1 (-5) (by omega)) (htr2_le m1 (-4) (by omega)) (htr2_le m1 (-3) (by omega))]
          rw [second_m4_eq (evolve flat first) first second
              (evolve_flat first (-5)) (evolve_flat first (-4)) (evolve_flat first (-3))]
          rw [htr2_m2, htr2_m1, hm1_b0, hm1_b1, evolve_flat, evolve_flat]
          exact xor_neq_of_mid_neq _ _ _ _ hab
        have hlen := takeWhile_length_one (n := w + 5) (by omega) fixed2 (hf2_0_true hg) hf2_1_false
        simp [hw2, hg, hh, E, hlen]
      · have hf2_1_true : fixed2 1 = true := by
          apply List.all_eq_true.mpr
          intro code hcmem
          have htb : one.2.testBit (code % 2 ^ w) = true := (List.mem_filter.mp hcmem).2
          rcases (hone2_iff (code % 2 ^ w)).mp htb with ⟨c1, _, hc1_eq⟩
          have hc_b0 : code.testBit 0 = evolve (fun site => if site ≤ 0 then flat site else c1.testBit (site - 0 - 1).toNat) first (-2) := by
            have h1 : (code % 2 ^ w).testBit 0 = code.testBit 0 := by
              rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and]
            rw [← h1, ← hc1_eq, (block_spec _ (-3) w).2 0]
            simp only [show 0 < w by omega, ↓reduceIte]
            rfl
          have hc_b1 : code.testBit 1 = evolve (fun site => if site ≤ 0 then flat site else c1.testBit (site - 0 - 1).toNat) first (-1) := by
            have h1 : (code % 2 ^ w).testBit 1 = code.testBit 1 := by
              rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and]
            rw [← h1, ← hc1_eq, (block_spec _ (-3) w).2 1]
            simp only [show 1 < w by omega, ↓reduceIte]
            rfl
          have hs : (-3 : Int) - 2 + ((1 : Nat) : Int) = -4 := by omega
          rw [hs, beq_iff_eq]
          rw [second_m4_eq (tr2 code) first second
              (htr2_le code (-5) (by omega)) (htr2_le code (-4) (by omega)) (htr2_le code (-3) (by omega))]
          rw [second_m4_eq (evolve flat first) first second
              (evolve_flat first (-5)) (evolve_flat first (-4)) (evolve_flat first (-3))]
          rw [htr2_m2, htr2_m1, hc_b0, hc_b1, evolve_flat, evolve_flat]
          rw [evolve_admissible_m2 (htrial1_adm c1), evolve_admissible_m1 (htrial1_adm c1)]
          rw [hidden_term_m4_false (first (-4)) (first (-3)) (first (-2)) (first (-1)) _ _ hh]
          have hf0 := hidden_term_m4_false (first (-4)) (first (-3)) (first (-2)) (first (-1)) false false hh
          simp only [Bool.not_false, Bool.true_and, Bool.xor_false] at hf0
          rw [hf0]
        have hf2_2_false : fixed2 2 = false := by
          apply List.all_eq_false.mpr
          have hex_pair : ∃ cA cB, cA ∈ tails2 ∧ cB ∈ tails2 ∧
              cA.testBit 0 = !(first (-2)) ∧ cA.testBit 1 = first (-1) ∧
              cB.testBit 0 = !(first (-2)) ∧ cB.testBit 1 = first (-1) ∧
              cA.testBit 2 ≠ cB.testBit 2 := by
            by_cases hw3 : 3 ≤ w
            · let mA := block w (evolve (fun site => if site ≤ 0 then flat site else (3 : Nat).testBit (site - 0 - 1).toNat) first) (-3)
              let mB := block w (evolve (fun site => if site ≤ 0 then flat site else (7 : Nat).testBit (site - 0 - 1).toNat) first) (-3)
              have hmA_lt : mA < 2 ^ w := (block_spec _ _ w).1
              have hmB_lt : mB < 2 ^ w := (block_spec _ _ w).1
              have hmA_mem : mA ∈ tails2 :=
                hmem_t2 mA (lt_trans hmA_lt hpow_w_lt) (by rw [Nat.mod_eq_of_lt hmA_lt]; exact (hone2_iff mA).mpr ⟨3, by omega, rfl⟩)
              have hmB_mem : mB ∈ tails2 :=
                hmem_t2 mB (lt_trans hmB_lt hpow_w_lt) (by rw [Nat.mod_eq_of_lt hmB_lt]; exact (hone2_iff mB).mpr ⟨7, by omega, rfl⟩)
              have hbA0 : mA.testBit 0 = !(first (-2)) := by
                rw [(block_spec _ (-3) w).2 0]; simp only [show 0 < w by omega, ↓reduceIte]
                have hidx : (-3 : Int) + 1 + ((0 : Nat) : Int) = -2 := by omega
                rw [hidx, evolve_admissible_m2 (htrial1_adm 3)]
                have h1 : (if (1 : Int) ≤ 0 then flat 1 else (3 : Nat).testBit ((1 : Int) - 0 - 1).toNat) = true := by decide
                rw [h1]; simp
              have hbA1 : mA.testBit 1 = first (-1) := by
                rw [(block_spec _ (-3) w).2 1]; simp only [show 1 < w by omega, ↓reduceIte]
                have hidx : (-3 : Int) + 1 + ((1 : Nat) : Int) = -1 := by omega
                rw [hidx, evolve_admissible_m1 (htrial1_adm 3)]
                have h1 : (if (1 : Int) ≤ 0 then flat 1 else (3 : Nat).testBit ((1 : Int) - 0 - 1).toNat) = true := by decide
                rw [h1]; simp
              have hbA2 : mA.testBit 2 = xor (first 0) true := by
                rw [(block_spec _ (-3) w).2 2]; simp only [show 2 < w by omega, ↓reduceIte]
                have hidx : (-3 : Int) + 1 + ((2 : Nat) : Int) = 0 := by omega
                rw [hidx, evolve_admissible_0_tt (htrial1_adm 3) (by decide) (by decide)]
                have h3 : (if (3 : Int) ≤ 0 then flat 3 else (3 : Nat).testBit ((3 : Int) - 0 - 1).toNat) = false := by decide
                rw [h3]; rfl
              have hbB0 : mB.testBit 0 = !(first (-2)) := by
                rw [(block_spec _ (-3) w).2 0]; simp only [show 0 < w by omega, ↓reduceIte]
                have hidx : (-3 : Int) + 1 + ((0 : Nat) : Int) = -2 := by omega
                rw [hidx, evolve_admissible_m2 (htrial1_adm 7)]
                have h1 : (if (1 : Int) ≤ 0 then flat 1 else (7 : Nat).testBit ((1 : Int) - 0 - 1).toNat) = true := by decide
                rw [h1]; simp
              have hbB1 : mB.testBit 1 = first (-1) := by
                rw [(block_spec _ (-3) w).2 1]; simp only [show 1 < w by omega, ↓reduceIte]
                have hidx : (-3 : Int) + 1 + ((1 : Nat) : Int) = -1 := by omega
                rw [hidx, evolve_admissible_m1 (htrial1_adm 7)]
                have h1 : (if (1 : Int) ≤ 0 then flat 1 else (7 : Nat).testBit ((1 : Int) - 0 - 1).toNat) = true := by decide
                rw [h1]; simp
              have hbB2 : mB.testBit 2 = xor (first 0) false := by
                rw [(block_spec _ (-3) w).2 2]; simp only [show 2 < w by omega, ↓reduceIte]
                have hidx : (-3 : Int) + 1 + ((2 : Nat) : Int) = 0 := by omega
                rw [hidx, evolve_admissible_0_tt (htrial1_adm 7) (by decide) (by decide)]
                have h3 : (if (3 : Int) ≤ 0 then flat 3 else (7 : Nat).testBit ((3 : Int) - 0 - 1).toNat) = true := by decide
                rw [h3]; rfl
              refine ⟨mA, mB, hmA_mem, hmB_mem, hbA0, hbA1, hbB0, hbB1, ?_⟩
              rw [hbA2, hbB2]; cases first 0 <;> decide
            · have hw_eq2 : w = 2 := by omega
              subst hw_eq2
              let mA := block 2 (evolve (fun site => if site ≤ 0 then flat site else (3 : Nat).testBit (site - 0 - 1).toNat) first) (-3)
              have hmA_lt : mA < 4 := (block_spec _ _ 2).1
              have hmA_tb : one.2.testBit mA = true := (hone2_iff mA).mpr ⟨3, by omega, rfl⟩
              have hmA_mem : mA ∈ tails2 :=
                hmem_t2 mA (by omega) (by rw [show (2 ^ 2 : Nat) = 4 by rfl, Nat.mod_eq_of_lt hmA_lt]; exact hmA_tb)
              have hmB_mem : (mA + 4) ∈ tails2 :=
                hmem_t2 (mA + 4) (by omega) (by rw [show (2 ^ 2 : Nat) = 4 by rfl, Nat.add_mod_right, Nat.mod_eq_of_lt hmA_lt]; exact hmA_tb)
              have hbA0 : mA.testBit 0 = !(first (-2)) := by
                rw [(block_spec _ (-3) 2).2 0]; simp only [show (0 : Nat) < 2 by omega, ↓reduceIte]
                have hidx : (-3 : Int) + 1 + ((0 : Nat) : Int) = -2 := by omega
                rw [hidx, evolve_admissible_m2 (htrial1_adm 3)]
                have h1 : (if (1 : Int) ≤ 0 then flat 1 else (3 : Nat).testBit ((1 : Int) - 0 - 1).toNat) = true := by decide
                rw [h1]; simp
              have hbA1 : mA.testBit 1 = first (-1) := by
                rw [(block_spec _ (-3) 2).2 1]; simp only [show (1 : Nat) < 2 by omega, ↓reduceIte]
                have hidx : (-3 : Int) + 1 + ((1 : Nat) : Int) = -1 := by omega
                rw [hidx, evolve_admissible_m1 (htrial1_adm 3)]
                have h1 : (if (1 : Int) ≤ 0 then flat 1 else (3 : Nat).testBit ((1 : Int) - 0 - 1).toNat) = true := by decide
                rw [h1]; simp
              have hbA2 : mA.testBit 2 = false := Nat.testBit_lt_two_pow hmA_lt
              have hbB0 : (mA + 4).testBit 0 = !(first (-2)) := by
                rw [Nat.add_comm, show (4 : Nat) = 2 ^ 2 by rfl, Nat.testBit_two_pow_add_gt (by omega), hbA0]
              have hbB1 : (mA + 4).testBit 1 = first (-1) := by
                rw [Nat.add_comm, show (4 : Nat) = 2 ^ 2 by rfl, Nat.testBit_two_pow_add_gt (by omega), hbA1]
              have hbB2 : (mA + 4).testBit 2 = true := by
                rw [Nat.add_comm, show (4 : Nat) = 2 ^ 2 by rfl, Nat.testBit_two_pow_add_eq, hbA2]; rfl
              refine ⟨mA, mA + 4, hmA_mem, hmB_mem, hbA0, hbA1, hbB0, hbB1, ?_⟩
              rw [hbA2, hbB2]; decide
          rcases hex_pair with ⟨cA, cB, hcA, hcB, hA0, hA1, hB0, hB1, hAB2⟩
          have hdiff : evolve (tr2 cA) second (-3) ≠ evolve (tr2 cB) second (-3) := by
            rw [second_m3_eq (tr2 cA) first second (htr2_le cA (-4) (by omega)) (htr2_le cA (-3) (by omega))]
            rw [second_m3_eq (tr2 cB) first second (htr2_le cB (-4) (by omega)) (htr2_le cB (-3) (by omega))]
            rw [htr2_m2, htr2_m1, htr2_0, htr2_m2, htr2_m1, htr2_0, hA0, hA1, hB0, hB1]
            exact m3_neq_of_mix_m2_false _ _ _ _ _ _ _
              (hidden_mix_m2 (first (-4)) (first (-3)) (first (-2)) (first (-1)) hh) hAB2
          have hs : (-3 : Int) - 2 + ((2 : Nat) : Int) = -3 := by omega
          by_cases hneA : evolve (tr2 cA) second (-3) ≠ evolve (evolve flat first) second (-3)
          · exact ⟨cA, hcA, by rw [hs, beq_iff_eq]; exact hneA⟩
          · refine ⟨cB, hcB, ?_⟩
            rw [hs, beq_iff_eq]
            intro heqB
            exact hdiff ((Classical.not_not.mp hneA).trans heqB.symm)
        have hlen := takeWhile_length_two (n := w + 5) (by omega) fixed2 (hf2_0_true hg) hf2_1_true hf2_2_false
        simp [hw2, hg, hh, E, hlen]

theorem main_proof : ∀ (first second : Int → Bool),
  let flat : Int → Bool := fun _ => false
  let admissible := fun (x : Int → Bool) => ∀ j ≤ (0 : Int), x j = false
  let physical := fun (x : Int → Bool) => evolve (evolve x first) second
  let guard := xor (xor (first (-5)) (first (-4))) (first (-3))
  let hidden := (xor (first (-4)) (first (-3)) == !(first (-2))) &&
    (first (-4) == first (-1))
  let E : Int := if guard then (if hidden then -4 else -5) else -6
  (∀ x, admissible x → ∀ j ≤ E, physical x j = physical flat j) ∧
  (∃ x, admissible x ∧ physical x (E + 1) ≠ physical flat (E + 1)) ∧
  (∀ w : Nat,
    let allWords := 2 ^ (2 ^ w) - 1
    let one := advance w 0 flat first allWords
    let two := advance w one.1 (evolve flat first) second one.2
    one.1 = -3 ∧
    two.1 = (if w < 2 ∧ guard = true then (-5 : Int) else E)) :=
  fun first second => ⟨part1_proof first second, part2_proof first second, part3_proof first second⟩

end PEqualNP.Outside.L_meta_25608_aux

theorem PEqualNP.Outside.L_meta_25608 : (let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
let evolve := fun (x injection : Int → Bool) (z : Int) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
let block := fun (width : Nat) (tape : Int → Bool) (edge : Int) =>
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0
let fits := fun (width : Nat) (edge : Int) (sample : Int → Bool) (mask : Nat) (tape : Int → Bool) =>
  (∀ pos ≤ edge, tape pos = sample pos) ∧ mask.testBit (block width tape edge) = true
let advance := fun (w : Nat) (b : Int) (x inj : Int → Bool) (allowed : Nat) =>
  let tails := (List.range (2 ^ (2*w+5))).filter (fun pattern => allowed.testBit (pattern % 2^w))
  let trial := fun (completionCode : Nat) (site : Int) =>
    if site ≤ b then x site else completionCode.testBit (site-b-1).toNat
  let reference := evolve x inj
  let fixed := fun (offset : Nat) =>
    let site := b-2+(offset : Int)
    tails.all (fun comparisonCode => evolve (trial comparisonCode) inj site == reference site)
  let newEdge := b-3+(((List.range (w+5)).takeWhile fixed).length : Int)
  let newMask := tails.foldl (fun acc outputCode =>
    acc ||| ((1 : Nat) <<< block w (evolve (trial outputCode) inj) newEdge)) 0
  (newEdge, newMask)
∀ (first second : Int → Bool),
  let flat : Int → Bool := fun _ => false
  let admissible := fun (x : Int → Bool) => ∀ j ≤ (0 : Int), x j = false
  let physical := fun (x : Int → Bool) => evolve (evolve x first) second
  let guard := xor (xor (first (-5)) (first (-4))) (first (-3))
  let hidden := (xor (first (-4)) (first (-3)) == !(first (-2))) &&
    (first (-4) == first (-1))
  let E : Int := if guard then (if hidden then -4 else -5) else -6
  (∀ x, admissible x → ∀ j ≤ E, physical x j = physical flat j) ∧
  (∃ x, admissible x ∧ physical x (E+1) ≠ physical flat (E+1)) ∧
  (∀ w : Nat,
    let allWords := 2^(2^w) - 1
    let one := advance w 0 flat first allWords
    let two := advance w one.1 (evolve flat first) second one.2
    one.1 = -3 ∧
    two.1 = (if w < 2 ∧ guard = true then (-5 : Int) else E))) :=
  PEqualNP.Outside.L_meta_25608_aux.main_proof
