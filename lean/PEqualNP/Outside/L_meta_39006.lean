import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39006

private def chiFn (bits : Nat → Bool) (j : Nat) : Bool :=
  xor (bits j) (!(bits (j + 1)) && bits (j + 2))

private def tapFn (k start x j back : Nat) : Bool :=
  x.testBit ((start + j + k - back) % k)

private def pulseFn (k start : Nat) (col : Bool) (x j : Nat) : Bool :=
  if col then xor (tapFn k start x j 1) (xor (tapFn k start x j 3) (tapFn k start x j 5))
  else xor (tapFn k start x j 0) (xor (tapFn k start x j 1) (tapFn k start x j 2))

private def fiberSet (h : Nat) (z : Fin h → Bool) : Set Nat :=
  {u : Nat | u < 2 ^ (h + 2) ∧ ∀ j : Fin h, chiFn (fun i => u.testBit i) j = z j}

private def tailSet (h k start : Nat) (col : Bool) (x len u : Nat) : Finset Nat :=
  (Finset.range len).filter (fun j =>
    chiFn (fun i => xor (u.testBit i) (pulseFn k start col x i)) (h - len + j))

private def okProp (h k start x : Nat) (r c : Fin h → Bool) : Prop :=
  Set.InjOn (tailSet h k start false x 5) (fiberSet h r) ∧
    Set.InjOn (tailSet h k start true x 4) (fiberSet h c)

-- Bit packing helper: packBits b m < 2^m with testBit i = (i < m && b i)
private def packBits (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => (if b 0 then 1 else 0) + 2 * packBits (fun i => b (i + 1)) m

private lemma packBits_lt (b : Nat → Bool) : ∀ m, packBits b m < 2 ^ m
  | 0 => by simp [packBits]
  | m + 1 => by
    have ih := packBits_lt (fun i => b (i + 1)) m
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
    dsimp only [packBits]
    cases b 0 <;> simp <;> omega

private lemma packBits_testBit (b : Nat → Bool) :
    ∀ m i, (packBits b m).testBit i = (decide (i < m) && b i)
  | 0, i => by simp [packBits]
  | m + 1, 0 => by
    dsimp only [packBits]
    rw [Nat.testBit_zero]
    cases b 0 <;> simp
  | m + 1, i + 1 => by
    dsimp only [packBits]
    rw [Nat.testBit_succ]
    have hdiv : ((if b 0 then 1 else 0) + 2 * packBits (fun j => b (j + 1)) m) / 2 =
        packBits (fun j => b (j + 1)) m := by
      cases b 0 <;> simp <;> omega
    rw [hdiv, packBits_testBit (fun j => b (j + 1)) m i]
    have hlt : decide (i < m) = decide (i + 1 < m + 1) := by
      apply Bool.eq_iff_iff.mpr; simp
    rw [hlt]

-- Explicit bijection Fin 4 -> fiberSet h z
private def fibRev {h : Nat} (z : Fin h → Bool) (top0 top1 : Bool) : Nat → Bool
  | 0 => top1
  | 1 => top0
  | m + 2 =>
    if hm : m < h then
      xor (z ⟨h - 1 - m, by omega⟩) (!(fibRev z top0 top1 (m + 1)) && fibRev z top0 top1 m)
    else false

private def fibBit {h : Nat} (z : Fin h → Bool) (top0 top1 : Bool) (i : Nat) : Bool :=
  if i ≤ h + 1 then fibRev z top0 top1 (h + 1 - i) else false

private def liftFiber {h : Nat} (z : Fin h → Bool) (top0 top1 : Bool) : Nat :=
  packBits (fibBit z top0 top1) (h + 2)

private lemma liftFiber_testBit {h : Nat} (z : Fin h → Bool) (top0 top1 : Bool) (i : Nat) :
    (liftFiber z top0 top1).testBit i = fibBit z top0 top1 i := by
  unfold liftFiber
  rw [packBits_testBit]
  by_cases hi : i < h + 2
  · simp [hi]
  · have hle : ¬ (i ≤ h + 1) := by omega
    simp [hi, fibBit, hle]

private lemma liftFiber_mem {h : Nat} (z : Fin h → Bool) (top0 top1 : Bool) :
    liftFiber z top0 top1 ∈ fiberSet h z := by
  refine ⟨packBits_lt _ _, ?_⟩
  intro j
  unfold chiFn
  simp only [liftFiber_testBit]
  have hj0 : j.val ≤ h + 1 := by omega
  have hj1 : j.val + 1 ≤ h + 1 := by omega
  have hj2 : j.val + 2 ≤ h + 1 := by omega
  simp only [fibBit, hj0, hj1, hj2, ↓reduceIte]
  set m := h - 1 - j.val with hm_def
  have hm : m < h := by omega
  have h0 : h + 1 - j.val = m + 2 := by omega
  have h1 : h + 1 - (j.val + 1) = m + 1 := by omega
  have h2 : h + 1 - (j.val + 2) = m := by omega
  have hidx : (⟨h - 1 - m, by omega⟩ : Fin h) = j := Fin.ext (by dsimp only; omega)
  rw [h0, h1, h2, fibRev]
  simp only [hm, ↓reduceDIte, hidx]
  cases z j <;> cases (!(fibRev z top0 top1 (m + 1)) && fibRev z top0 top1 m) <;> decide

private lemma liftFiber_unique {h : Nat} {z : Fin h → Bool} {u : Nat}
    (hu : u ∈ fiberSet h z) :
    u = liftFiber z (u.testBit h) (u.testBit (h + 1)) := by
  have hrev : ∀ m, m ≤ h + 1 →
      u.testBit (h + 1 - m) = fibRev z (u.testBit h) (u.testBit (h + 1)) m := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm
      match m with
      | 0 => simp [fibRev]
      | 1 => simp [fibRev]
      | m + 2 =>
        have hlt : m < h := by omega
        have h1 := ih (m + 1) (by omega) (by omega)
        have h2 := ih m (by omega) (by omega)
        set j : Fin h := ⟨h - 1 - m, by omega⟩
        have hchi := hu.2 j
        unfold chiFn at hchi
        dsimp only at hchi
        have e0 : h + 1 - (m + 2) = j.val := by dsimp only [j]; omega
        have e1 : j.val + 1 = h + 1 - (m + 1) := by dsimp only [j]; omega
        have e2 : j.val + 2 = h + 1 - m := by dsimp only [j]; omega
        rw [e1, e2, h1, h2] at hchi
        rw [e0, fibRev]
        simp only [hlt, ↓reduceDIte]
        have hval : (⟨h - 1 - m, by omega⟩ : Fin h) = j := rfl
        rw [hval]
        cases a : u.testBit j.val <;>
          cases b : (!(fibRev z (u.testBit h) (u.testBit (h + 1)) (m + 1)) &&
            fibRev z (u.testBit h) (u.testBit (h + 1)) m) <;>
          cases c : z j <;> simp [a, b, c] at hchi ⊢
  apply Nat.eq_of_testBit_eq
  intro i
  rw [liftFiber_testBit]
  by_cases hi : i ≤ h + 1
  · simp only [fibBit, hi, ↓reduceIte]
    have hsub : h + 1 - (h + 1 - i) = i := by omega
    have h := hrev (h + 1 - i) (by omega)
    rwa [hsub] at h
  · have hge : h + 2 ≤ i := by omega
    have hlt : u < 2 ^ i := lt_of_lt_of_le hu.1 (Nat.pow_le_pow_right (by omega) hge)
    rw [Nat.testBit_lt_two_pow hlt]
    simp [fibBit, hi]

private lemma liftFiber_inj {h : Nat} (z : Fin h → Bool)
    {a0 a1 b0 b1 : Bool}
    (heq : liftFiber z a0 a1 = liftFiber z b0 b1) : a0 = b0 ∧ a1 = b1 := by
  have h0 := congrArg (fun u => u.testBit h) heq
  have h1 := congrArg (fun u => u.testBit (h + 1)) heq
  simp only [liftFiber_testBit, fibBit, Nat.le_succ, le_refl, ↓reduceIte] at h0 h1
  have e0 : h + 1 - h = 1 := by omega
  have e1 : h + 1 - (h + 1) = 0 := by omega
  rw [e0, fibRev] at h0
  rw [e1, fibRev] at h1
  exact ⟨h0, h1⟩

-- Pure Bool 5-step tail (with constant z0 ^ p0 stripped from bit 0!)
private def tail5Vec (p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 top0 top1 : Bool) :
    Bool × Bool × Bool × Bool × Bool :=
  let u6 := top1
  let u5 := top0
  let u4 := xor z4 (!u5 && u6)
  let u3 := xor z3 (!u4 && u5)
  let u2 := xor z2 (!u3 && u4)
  let u1 := xor z1 (!u2 && u3)
  let b0 := xor (!u1 && u2) (!(xor u1 p1) && (xor u2 p2))
  let b1 := xor (xor u1 p1) (!(xor u2 p2) && (xor u3 p3))
  let b2 := xor (xor u2 p2) (!(xor u3 p3) && (xor u4 p4))
  let b3 := xor (xor u3 p3) (!(xor u4 p4) && (xor u5 p5))
  let b4 := xor (xor u4 p4) (!(xor u5 p5) && (xor u6 p6))
  (b0, b1, b2, b3, b4)

private def ok5Bool (p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 : Bool) : Bool :=
  let v00 := tail5Vec p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 false false
  let v10 := tail5Vec p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 true false
  let v01 := tail5Vec p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 false true
  let v11 := tail5Vec p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 true true
  (v00 != v10) && (v00 != v01) && (v00 != v11) && (v10 != v01) && (v10 != v11) && (v01 != v11)

-- Pure Bool 4-step tail (with constant z1 ^ p1 stripped from bit 0!)
private def tail4Vec (p2 p3 p4 p5 p6 z2 z3 z4 top0 top1 : Bool) :
    Bool × Bool × Bool × Bool :=
  let u6 := top1
  let u5 := top0
  let u4 := xor z4 (!u5 && u6)
  let u3 := xor z3 (!u4 && u5)
  let u2 := xor z2 (!u3 && u4)
  let b0 := xor (!u2 && u3) (!(xor u2 p2) && (xor u3 p3))
  let b1 := xor (xor u2 p2) (!(xor u3 p3) && (xor u4 p4))
  let b2 := xor (xor u3 p3) (!(xor u4 p4) && (xor u5 p5))
  let b3 := xor (xor u4 p4) (!(xor u5 p5) && (xor u6 p6))
  (b0, b1, b2, b3)

private def ok4Bool (p2 p3 p4 p5 p6 z2 z3 z4 : Bool) : Bool :=
  let v00 := tail4Vec p2 p3 p4 p5 p6 z2 z3 z4 false false
  let v10 := tail4Vec p2 p3 p4 p5 p6 z2 z3 z4 true false
  let v01 := tail4Vec p2 p3 p4 p5 p6 z2 z3 z4 false true
  let v11 := tail4Vec p2 p3 p4 p5 p6 z2 z3 z4 true true
  (v00 != v10) && (v00 != v01) && (v00 != v11) && (v10 != v01) && (v10 != v11) && (v01 != v11)

-- Classify p1..p5 into rType in Fin 6 and p2..p5 into cType in Fin 4
private def rCov (rt : Fin 6) (z2 z3 z4 : Bool) : Bool :=
  match rt.val with
  | 0 => !(z2 == true && z3 == false && z4 == false)   -- R0: misses R1=(1,0,0)
  | 1 => !(z2 == false && z3 == false && z4 == false)  -- R1: misses R0=(0,0,0)
  | 2 => !(z3 == true && z4 == true)                   -- R2: misses {R6,R7}=(*,1,1)
  | 3 => !(z3 == true && z4 == false)                  -- R3: misses {R2,R3}=(*,1,0)
  | 4 => !z4                                           -- R4: misses {R4,R5,R6,R7}=(*,*,1)
  | _ => false                                         -- R5: empty

private def rType (p1 p2 p3 p4 p5 : Bool) : Fin 6 :=
  let a0 := ok5Bool p1 p2 p3 p4 p5 false false false false false
  let a1 := ok5Bool p1 p2 p3 p4 p5 false false true false false
  let a2 := ok5Bool p1 p2 p3 p4 p5 false false false true false
  let a4 := ok5Bool p1 p2 p3 p4 p5 false false false false true
  let a6 := ok5Bool p1 p2 p3 p4 p5 false false false true true
  if a0 && !a1 then ⟨0, by omega⟩
  else if !a0 && a1 then ⟨1, by omega⟩
  else if a0 && a1 && a4 && !a6 then ⟨2, by omega⟩
  else if a0 && a1 && !a2 then ⟨3, by omega⟩
  else if a0 && !a4 then ⟨4, by omega⟩
  else ⟨5, by omega⟩

private def cCov (ct : Fin 4) (z3 z4 : Bool) : Bool :=
  match ct.val with
  | 0 => !(z3 == true && z4 == false)                  -- C0: misses C1=(1,0)
  | 1 => !(z3 == false && z4 == false)                 -- C1: misses C0=(0,0)
  | 2 => !z4                                           -- C2: misses {C2,C3}=(*,1)
  | _ => false                                         -- C3: empty

private def cType (p2 p3 p4 p5 : Bool) : Fin 4 :=
  let b0 := ok4Bool p2 p3 p4 p5 false false false false
  let b1 := ok4Bool p2 p3 p4 p5 false false true false
  let b2 := ok4Bool p2 p3 p4 p5 false false false true
  if b0 && !b1 then ⟨0, by omega⟩
  else if !b0 && b1 then ⟨1, by omega⟩
  else if b0 && b1 && !b2 then ⟨2, by omega⟩
  else ⟨3, by omega⟩

-- Fast kernel decide lemmas on pure Bools (1024 and 256 cases)!
private lemma ok5Bool_eq_rCov :
    ∀ p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 : Bool,
      ok5Bool p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 = rCov (rType p1 p2 p3 p4 p5) z2 z3 z4 := by
  decide

private lemma ok4Bool_eq_cCov :
    ∀ p2 p3 p4 p5 p6 z2 z3 z4 : Bool,
      ok4Bool p2 p3 p4 p5 p6 z2 z3 z4 = cCov (cType p2 p3 p4 p5) z3 z4 := by
  decide

-- Map a 9-bit window (b1..b9, representing offsets -3..+5 relative to h-5) to (rType, cType) -> Fin 11
-- Offset m in {1..9} represents tap offset (m - 4), so:
--   p0[i] for i in 1..5 uses offsets i, i-1, i-2 -> b[i+4], b[i+3], b[i+2]
--   p1[i] for i in 2..5 uses offsets i-1, i-3, i-5 -> b[i+3], b[i+1], b[i-1]
private def pairId (rt : Fin 6) (ct : Fin 4) : Fin 11 :=
  match rt.val, ct.val with
  | 0, 2 => ⟨0, by omega⟩   -- (R0, C2): miss R1, {C2,C3}
  | 1, 0 => ⟨1, by omega⟩   -- (R1, C0): miss R0, C1
  | 1, 1 => ⟨2, by omega⟩   -- (R1, C1): miss R0, C0
  | 1, 2 => ⟨3, by omega⟩   -- (R1, C2): miss R0, {C2,C3}
  | 2, 0 => ⟨4, by omega⟩   -- (R2, C0): miss {R6,R7}, C1
  | 2, 1 => ⟨5, by omega⟩   -- (R2, C1): miss {R6,R7}, C0
  | 2, 2 => ⟨6, by omega⟩   -- (R2, C2): miss {R6,R7}, {C2,C3}
  | 4, 0 => ⟨7, by omega⟩   -- (R4, C0): miss {R4..R7}, C1
  | 4, 1 => ⟨8, by omega⟩   -- (R4, C1): miss {R4..R7}, C0
  | 4, 2 => ⟨9, by omega⟩   -- (R4, C2): miss {R4..R7}, {C2,C3}
  | _, _ => ⟨10, by omega⟩  -- empty

private def pairCov (pid : Fin 11) (z2 z3 z4 c3 c4 : Bool) : Bool :=
  match pid.val with
  | 0 => rCov ⟨0, by omega⟩ z2 z3 z4 && cCov ⟨2, by omega⟩ c3 c4
  | 1 => rCov ⟨1, by omega⟩ z2 z3 z4 && cCov ⟨0, by omega⟩ c3 c4
  | 2 => rCov ⟨1, by omega⟩ z2 z3 z4 && cCov ⟨1, by omega⟩ c3 c4
  | 3 => rCov ⟨1, by omega⟩ z2 z3 z4 && cCov ⟨2, by omega⟩ c3 c4
  | 4 => rCov ⟨2, by omega⟩ z2 z3 z4 && cCov ⟨0, by omega⟩ c3 c4
  | 5 => rCov ⟨2, by omega⟩ z2 z3 z4 && cCov ⟨1, by omega⟩ c3 c4
  | 6 => rCov ⟨2, by omega⟩ z2 z3 z4 && cCov ⟨2, by omega⟩ c3 c4
  | 7 => rCov ⟨4, by omega⟩ z2 z3 z4 && cCov ⟨0, by omega⟩ c3 c4
  | 8 => rCov ⟨4, by omega⟩ z2 z3 z4 && cCov ⟨1, by omega⟩ c3 c4
  | 9 => rCov ⟨4, by omega⟩ z2 z3 z4 && cCov ⟨2, by omega⟩ c3 c4
  | _ => false

private def winRType (b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Fin 6 :=
  rType
    (xor b5 (xor b4 b3))
    (xor b6 (xor b5 b4))
    (xor b7 (xor b6 b5))
    (xor b8 (xor b7 b6))
    (xor b9 (xor b8 b7))

private def winCType (b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Fin 4 :=
  cType
    (xor b5 (xor b3 b1))
    (xor b6 (xor b4 b2))
    (xor b7 (xor b5 b3))
    (xor b8 (xor b6 b4))

private lemma win_pairId_exact :
    ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      let rt := winRType b1 b2 b3 b4 b5 b6 b7 b8 b9
      let ct := winCType b1 b2 b3 b4 b5 b6 b7 b8 b9
      (rt.val = 5 ∨ ct.val = 3 ∨
        (rt.val = 0 ∧ ct.val = 2) ∨
        (rt.val = 1 ∧ (ct.val = 0 ∨ ct.val = 1 ∨ ct.val = 2)) ∨
        (rt.val = 2 ∧ (ct.val = 0 ∨ ct.val = 1 ∨ ct.val = 2)) ∨
        (rt.val = 4 ∧ (ct.val = 0 ∨ ct.val = 1 ∨ ct.val = 2))) := by
  decide

private lemma pairCov_eq_of_allowed (rt : Fin 6) (ct : Fin 4)
    (h : rt.val = 5 ∨ ct.val = 3 ∨
      (rt.val = 0 ∧ ct.val = 2) ∨
      (rt.val = 1 ∧ (ct.val = 0 ∨ ct.val = 1 ∨ ct.val = 2)) ∨
      (rt.val = 2 ∧ (ct.val = 0 ∨ ct.val = 1 ∨ ct.val = 2)) ∨
      (rt.val = 4 ∧ (ct.val = 0 ∨ ct.val = 1 ∨ ct.val = 2)))
    (z2 z3 z4 c3 c4 : Bool) :
    (rCov rt z2 z3 z4 && cCov ct c3 c4) = pairCov (pairId rt ct) z2 z3 z4 c3 c4 := by
  revert rt ct z2 z3 z4 c3 c4 h
  decide

-- Three 9-bit witnesses:
-- W0 = 72  (b4=1, b7=1) -> pid 1 (R1, C0: miss R0, C1)
-- W1 = 93  (b1=1, b3=1, b4=1, b5=1, b7=1) -> pid 5 (R2, C1: miss {R6,R7}, C0)
-- W2 = 76  (b3=1, b4=1, b7=1) -> pid 0 (R0, C2: miss R1, {C2,C3})
private lemma witness0_types :
    winRType false false false true false false true false false = ⟨1, by omega⟩ ∧
    winCType false false false true false false true false false = ⟨0, by omega⟩ := by
  decide

private lemma witness1_types :
    winRType true false true true true false true false false = ⟨2, by omega⟩ ∧
    winCType true false true true true false true false false = ⟨1, by omega⟩ := by
  decide

private lemma witness2_types :
    winRType false false true true false false true false false = ⟨0, by omega⟩ ∧
    winCType false false true true false false true false false = ⟨2, by omega⟩ := by
  decide

private def selectMenu (a0 a1 c3 c4 : Bool) : Fin 3 :=
  if !a0 && !a1 then
    if !c3 && !c4 then ⟨2, by omega⟩ else ⟨1, by omega⟩
  else if a0 && !a1 then
    if c3 && !c4 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  else
    if c3 && !c4 then ⟨2, by omega⟩ else ⟨0, by omega⟩

private lemma selectMenu_valid :
    ∀ z2 z3 z4 c3 c4 : Bool,
      let m := selectMenu (xor z2 z3) z4 c3 c4
      (m.val = 0 → rCov ⟨1, by omega⟩ z2 z3 z4 = true ∧ cCov ⟨0, by omega⟩ c3 c4 = true) ∧
      (m.val = 1 → rCov ⟨2, by omega⟩ z2 z3 z4 = true ∧ cCov ⟨1, by omega⟩ c3 c4 = true) ∧
      (m.val = 2 → rCov ⟨0, by omega⟩ z2 z3 z4 = true ∧ cCov ⟨2, by omega⟩ c3 c4 = true) := by
  decide

-- Converse finite theorem over Fin 11 x Fin 11 x Fin 11 (1331 cases!)
private def rPairSep (t0 t1 t2 : Fin 11) (a b : Bool × Bool × Bool) : Bool :=
  [(false, false), (true, false), (false, true), (true, true)].any (fun c =>
    !(pairCov t0 a.1 a.2.1 a.2.2 c.1 c.2 && pairCov t0 b.1 b.2.1 b.2.2 c.1 c.2) &&
    !(pairCov t1 a.1 a.2.1 a.2.2 c.1 c.2 && pairCov t1 b.1 b.2.1 b.2.2 c.1 c.2) &&
    !(pairCov t2 a.1 a.2.1 a.2.2 c.1 c.2 && pairCov t2 b.1 b.2.1 b.2.2 c.1 c.2))

private def cPairSep (t0 t1 t2 : Fin 11) (a b : Bool × Bool) : Bool :=
  [(false, false, false), (true, false, false), (false, true, true)].any (fun r =>
    !(pairCov t0 r.1 r.2.1 r.2.2 a.1 a.2 && pairCov t0 r.1 r.2.1 r.2.2 b.1 b.2) &&
    !(pairCov t1 r.1 r.2.1 r.2.2 a.1 a.2 && pairCov t1 r.1 r.2.1 r.2.2 b.1 b.2) &&
    !(pairCov t2 r.1 r.2.1 r.2.2 a.1 a.2 && pairCov t2 r.1 r.2.1 r.2.2 b.1 b.2))

private def tripleCoversB (t0 t1 t2 : Fin 11) : Bool :=
  [false, true].all fun z2 =>
  [false, true].all fun z3 =>
  [false, true].all fun z4 =>
  [false, true].all fun c3 =>
  [false, true].all fun c4 =>
    pairCov t0 z2 z3 z4 c3 c4 || pairCov t1 z2 z3 z4 c3 c4 || pairCov t2 z2 z3 z4 c3 c4

private lemma converse_finite :
    ∀ t0 t1 t2 : Fin 11, tripleCoversB t0 t1 t2 = true →
      rPairSep t0 t1 t2 (false, false, false) (true, false, false) = true ∧
      rPairSep t0 t1 t2 (false, false, false) (false, true, true) = true ∧
      rPairSep t0 t1 t2 (true, false, false) (false, true, true) = true ∧
      cPairSep t0 t1 t2 (false, false) (true, false) = true ∧
      cPairSep t0 t1 t2 (false, false) (false, true) = true ∧
      cPairSep t0 t1 t2 (true, false) (false, true) = true := by
  decide

-- Bridge between tailSet / fiberSet and ok5Bool / ok4Bool
private lemma tapFn_shift {h k start x : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    {i back : Nat} (hb : back ≤ 5) (hib : back ≤ i + 4) :
    tapFn k start x (h - 5 + i) back =
      x.testBit ((start + (h - 5) + (i + 4 - back) + k - 4) % k) := by
  unfold tapFn
  congr 2
  omega

private def winBit (h k start x : Nat) (m : Nat) : Bool :=
  x.testBit ((start + (h - 5) + m + k - 4) % k)

private lemma pulse_false_eq {h k start x : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    {i : Nat} :
    pulseFn k start false x (h - 5 + i) =
      xor (winBit h k start x (i + 4))
        (xor (winBit h k start x (i + 3)) (winBit h k start x (i + 2))) := by
  unfold pulseFn winBit
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [tapFn_shift hh hk (by omega) (by omega),
      tapFn_shift hh hk (by omega) (by omega),
      tapFn_shift hh hk (by omega) (by omega)]
  have e0 : i + 4 - 0 = i + 4 := by omega
  have e1 : i + 4 - 1 = i + 3 := by omega
  have e2 : i + 4 - 2 = i + 2 := by omega
  rw [e0, e1, e2]

private lemma pulse_true_eq {h k start x : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    {i : Nat} (hi : 1 ≤ i) :
    pulseFn k start true x (h - 5 + i) =
      xor (winBit h k start x (i + 3))
        (xor (winBit h k start x (i + 1)) (winBit h k start x (i - 1))) := by
  unfold pulseFn winBit
  simp only [↓reduceIte]
  rw [tapFn_shift hh hk (by omega) (by omega),
      tapFn_shift hh hk (by omega) (by omega),
      tapFn_shift hh hk (by omega) (by omega)]
  have e1 : i + 4 - 1 = i + 3 := by omega
  have e3 : i + 4 - 3 = i + 1 := by omega
  have e5 : i + 4 - 5 = i - 1 := by omega
  rw [e1, e3, e5]

private lemma liftFiber_top_bits {h : Nat} (hh : 5 ≤ h) (z : Fin h → Bool) (top0 top1 : Bool) :
    let u := liftFiber z top0 top1
    let z4 := z ⟨h - 1, by omega⟩
    let z3 := z ⟨h - 2, by omega⟩
    let z2 := z ⟨h - 3, by omega⟩
    let z1 := z ⟨h - 4, by omega⟩
    let z0 := z ⟨h - 5, by omega⟩
    let u6 := top1
    let u5 := top0
    let u4 := xor z4 (!u5 && u6)
    let u3 := xor z3 (!u4 && u5)
    let u2 := xor z2 (!u3 && u4)
    let u1 := xor z1 (!u2 && u3)
    let u0 := xor z0 (!u1 && u2)
    u.testBit (h - 5 + 6) = u6 ∧
    u.testBit (h - 5 + 5) = u5 ∧
    u.testBit (h - 5 + 4) = u4 ∧
    u.testBit (h - 5 + 3) = u3 ∧
    u.testBit (h - 5 + 2) = u2 ∧
    u.testBit (h - 5 + 1) = u1 ∧
    u.testBit (h - 5 + 0) = u0 := by
  dsimp only
  have hmem := liftFiber_mem z top0 top1
  have hu6 : (liftFiber z top0 top1).testBit (h - 5 + 6) = top1 := by
    have e : h - 5 + 6 = h + 1 := by omega
    rw [e, liftFiber_testBit, fibBit]
    simp only [le_refl, ↓reduceIte, Nat.sub_self, fibRev]
  have hu5 : (liftFiber z top0 top1).testBit (h - 5 + 5) = top0 := by
    have e : h - 5 + 5 = h := by omega
    rw [e, liftFiber_testBit, fibBit]
    have hle : h ≤ h + 1 := by omega
    have es : h + 1 - h = 1 := by omega
    simp only [hle, ↓reduceIte, es, fibRev]
  have hstep : ∀ (j : Fin h),
      (liftFiber z top0 top1).testBit j.val =
        xor (z j) (!((liftFiber z top0 top1).testBit (j.val + 1)) &&
          (liftFiber z top0 top1).testBit (j.val + 2)) := by
    intro j
    have hc := hmem.2 j
    unfold chiFn at hc
    cases a : (liftFiber z top0 top1).testBit j.val <;>
      cases b : (!((liftFiber z top0 top1).testBit (j.val + 1)) &&
        (liftFiber z top0 top1).testBit (j.val + 2)) <;>
      cases c : z j <;> simp [a, b, c] at hc ⊢
  have hu4 : (liftFiber z top0 top1).testBit (h - 5 + 4) = xor (z ⟨h - 1, by omega⟩) (!top0 && top1) := by
    have e0 : h - 5 + 4 = (⟨h - 1, by omega⟩ : Fin h).val := by dsimp only; omega
    have e1 : (⟨h - 1, by omega⟩ : Fin h).val + 1 = h - 5 + 5 := by dsimp only; omega
    have e2 : (⟨h - 1, by omega⟩ : Fin h).val + 2 = h - 5 + 6 := by dsimp only; omega
    rw [e0, hstep ⟨h - 1, by omega⟩, e1, e2, hu5, hu6]
  have hu3 : (liftFiber z top0 top1).testBit (h - 5 + 3) =
      xor (z ⟨h - 2, by omega⟩) (!(xor (z ⟨h - 1, by omega⟩) (!top0 && top1)) && top0) := by
    have e0 : h - 5 + 3 = (⟨h - 2, by omega⟩ : Fin h).val := by dsimp only; omega
    have e1 : (⟨h - 2, by omega⟩ : Fin h).val + 1 = h - 5 + 4 := by dsimp only; omega
    have e2 : (⟨h - 2, by omega⟩ : Fin h).val + 2 = h - 5 + 5 := by dsimp only; omega
    rw [e0, hstep ⟨h - 2, by omega⟩, e1, e2, hu4, hu5]
  have hu2 : (liftFiber z top0 top1).testBit (h - 5 + 2) =
      xor (z ⟨h - 3, by omega⟩) (!(xor (z ⟨h - 2, by omega⟩)
        (!(xor (z ⟨h - 1, by omega⟩) (!top0 && top1)) && top0)) &&
        xor (z ⟨h - 1, by omega⟩) (!top0 && top1)) := by
    have e0 : h - 5 + 2 = (⟨h - 3, by omega⟩ : Fin h).val := by dsimp only; omega
    have e1 : (⟨h - 3, by omega⟩ : Fin h).val + 1 = h - 5 + 3 := by dsimp only; omega
    have e2 : (⟨h - 3, by omega⟩ : Fin h).val + 2 = h - 5 + 4 := by dsimp only; omega
    rw [e0, hstep ⟨h - 3, by omega⟩, e1, e2, hu3, hu4]
  have hu1 : (liftFiber z top0 top1).testBit (h - 5 + 1) =
      xor (z ⟨h - 4, by omega⟩) (!((liftFiber z top0 top1).testBit (h - 5 + 2)) &&
        (liftFiber z top0 top1).testBit (h - 5 + 3)) := by
    have e0 : h - 5 + 1 = (⟨h - 4, by omega⟩ : Fin h).val := by dsimp only; omega
    have e1 : (⟨h - 4, by omega⟩ : Fin h).val + 1 = h - 5 + 2 := by dsimp only; omega
    have e2 : (⟨h - 4, by omega⟩ : Fin h).val + 2 = h - 5 + 3 := by dsimp only; omega
    rw [e0, hstep ⟨h - 4, by omega⟩, e1, e2]
  have hu0 : (liftFiber z top0 top1).testBit (h - 5 + 0) =
      xor (z ⟨h - 5, by omega⟩) (!((liftFiber z top0 top1).testBit (h - 5 + 1)) &&
        (liftFiber z top0 top1).testBit (h - 5 + 2)) := by
    have e0 : h - 5 + 0 = (⟨h - 5, by omega⟩ : Fin h).val := by dsimp only; omega
    have e1 : (⟨h - 5, by omega⟩ : Fin h).val + 1 = h - 5 + 1 := rfl
    have e2 : (⟨h - 5, by omega⟩ : Fin h).val + 2 = h - 5 + 2 := rfl
    rw [e0, hstep ⟨h - 5, by omega⟩, e1, e2]
  refine ⟨hu6, hu5, hu4, hu3, hu2, ?_, ?_⟩
  · rw [hu1, hu2, hu3]
  · rw [hu0, hu1, hu2, hu3]

private lemma xor_const_eq_iff (c a b : Bool) : (xor c a = xor c b) ↔ a = b := by
  cases c <;> cases a <;> cases b <;> decide

private lemma xor_reassoc (a b c d : Bool) :
    xor (xor (xor a b) c) d = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma injOn_tail5_iff {h k start x : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (r : Fin h → Bool) :
    Set.InjOn (tailSet h k start false x 5) (fiberSet h r) ↔
      rCov (winRType
        (winBit h k start x 1) (winBit h k start x 2) (winBit h k start x 3)
        (winBit h k start x 4) (winBit h k start x 5) (winBit h k start x 6)
        (winBit h k start x 7) (winBit h k start x 8) (winBit h k start x 9))
        (r ⟨h - 3, by omega⟩) (r ⟨h - 2, by omega⟩) (r ⟨h - 1, by omega⟩) = true := by
  let p0 := pulseFn k start false x (h - 5 + 0)
  let p1 := pulseFn k start false x (h - 5 + 1)
  let p2 := pulseFn k start false x (h - 5 + 2)
  let p3 := pulseFn k start false x (h - 5 + 3)
  let p4 := pulseFn k start false x (h - 5 + 4)
  let p5 := pulseFn k start false x (h - 5 + 5)
  let p6 := pulseFn k start false x (h - 5 + 6)
  let z0 := r ⟨h - 5, by omega⟩
  let z1 := r ⟨h - 4, by omega⟩
  let z2 := r ⟨h - 3, by omega⟩
  let z3 := r ⟨h - 2, by omega⟩
  let z4 := r ⟨h - 1, by omega⟩
  have htail_eq : ∀ (a0 a1 b0 b1 : Bool),
      tailSet h k start false x 5 (liftFiber r a0 a1) =
        tailSet h k start false x 5 (liftFiber r b0 b1) ↔
      tail5Vec p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 a0 a1 =
        tail5Vec p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 b0 b1 := by
    intro a0 a1 b0 b1
    have hA := liftFiber_top_bits hh r a0 a1
    have hB := liftFiber_top_bits hh r b0 b1
    dsimp only at hA hB
    have heval : ∀ (t0 t1 : Bool) (j : Nat), j < 5 →
        (j ∈ tailSet h k start false x 5 (liftFiber r t0 t1) ↔
          chiFn (fun i => xor ((liftFiber r t0 t1).testBit i) (pulseFn k start false x i))
            (h - 5 + j) = true) := by
      intro t0 t1 j hj
      simp [tailSet, hj]
    have hset_iff :
        tailSet h k start false x 5 (liftFiber r a0 a1) =
          tailSet h k start false x 5 (liftFiber r b0 b1) ↔
        ∀ j < 5,
          chiFn (fun i => xor ((liftFiber r a0 a1).testBit i) (pulseFn k start false x i))
            (h - 5 + j) =
          chiFn (fun i => xor ((liftFiber r b0 b1).testBit i) (pulseFn k start false x i))
            (h - 5 + j) := by
      constructor
      · intro heq j hj
        apply Bool.eq_iff_iff.mpr
        rw [← heval a0 a1 j hj, ← heval b0 b1 j hj, heq]
      · intro hall
        ext j
        by_cases hj : j < 5
        · rw [heval a0 a1 j hj, heval b0 b1 j hj, hall j hj]
        · simp [tailSet, hj]
    rw [hset_iff]
    have h5 : (∀ j < 5,
        chiFn (fun i => xor ((liftFiber r a0 a1).testBit i) (pulseFn k start false x i)) (h - 5 + j) =
        chiFn (fun i => xor ((liftFiber r b0 b1).testBit i) (pulseFn k start false x i)) (h - 5 + j)) ↔
        (chiFn (fun i => xor ((liftFiber r a0 a1).testBit i) (pulseFn k start false x i)) (h - 5 + 0) =
         chiFn (fun i => xor ((liftFiber r b0 b1).testBit i) (pulseFn k start false x i)) (h - 5 + 0) ∧
         chiFn (fun i => xor ((liftFiber r a0 a1).testBit i) (pulseFn k start false x i)) (h - 5 + 1) =
         chiFn (fun i => xor ((liftFiber r b0 b1).testBit i) (pulseFn k start false x i)) (h - 5 + 1) ∧
         chiFn (fun i => xor ((liftFiber r a0 a1).testBit i) (pulseFn k start false x i)) (h - 5 + 2) =
         chiFn (fun i => xor ((liftFiber r b0 b1).testBit i) (pulseFn k start false x i)) (h - 5 + 2) ∧
         chiFn (fun i => xor ((liftFiber r a0 a1).testBit i) (pulseFn k start false x i)) (h - 5 + 3) =
         chiFn (fun i => xor ((liftFiber r b0 b1).testBit i) (pulseFn k start false x i)) (h - 5 + 3) ∧
         chiFn (fun i => xor ((liftFiber r a0 a1).testBit i) (pulseFn k start false x i)) (h - 5 + 4) =
         chiFn (fun i => xor ((liftFiber r b0 b1).testBit i) (pulseFn k start false x i)) (h - 5 + 4)) := by
      constructor
      · intro h; exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)⟩
      · rintro ⟨c0, c1, c2, c3, c4⟩ j hj
        interval_cases j <;> assumption
    rw [h5]
    unfold chiFn tail5Vec
    simp only [Nat.add_assoc, Prod.mk.injEq]
    rcases hA with ⟨hA6, hA5, hA4, hA3, hA2, hA1, hA0⟩
    rcases hB with ⟨hB6, hB5, hB4, hB3, hB2, hB1, hB0⟩
    rw [hA6, hA5, hA4, hA3, hA2, hA1, hA0, hB6, hB5, hB4, hB3, hB2, hB1, hB0]
    dsimp only [p0, p1, p2, p3, p4, p5, p6, z0, z1, z2, z3, z4]
    rw [xor_reassoc, xor_reassoc, xor_const_eq_iff]
  have hinj_iff : Set.InjOn (tailSet h k start false x 5) (fiberSet h r) ↔
      ok5Bool p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 = true := by
    unfold ok5Bool
    simp only [Bool.and_eq_true, bne_iff_ne]
    constructor
    · intro hinj
      have hne : ∀ a0 a1 b0 b1 : Bool, (a0 ≠ b0 ∨ a1 ≠ b1) →
          tail5Vec p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 a0 a1 ≠
            tail5Vec p1 p2 p3 p4 p5 p6 z1 z2 z3 z4 b0 b1 := by
        intro a0 a1 b0 b1 hdiff heq
        have ht := (htail_eq a0 a1 b0 b1).mpr heq
        have hu := hinj (liftFiber_mem r a0 a1) (liftFiber_mem r b0 b1) ht
        have hp := liftFiber_inj r hu
        rcases hdiff with h | h <;> [exact h hp.1; exact h hp.2]
      exact ⟨⟨⟨⟨⟨hne false false true false (Or.inl (by decide)),
                 hne false false false true (Or.inr (by decide))⟩,
                hne false false true true (Or.inl (by decide))⟩,
               hne true false false true (Or.inl (by decide))⟩,
              hne true false true true (Or.inr (by decide))⟩,
             hne false true true true (Or.inl (by decide))⟩
    · rintro ⟨⟨⟨⟨⟨h01, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩ u₁ hu1 u₂ hu2 heq
      rw [liftFiber_unique hu1, liftFiber_unique hu2] at heq ⊢
      have hv := (htail_eq _ _ _ _).mp heq
      generalize u₁.testBit h = a0 at hv ⊢
      generalize u₁.testBit (h + 1) = a1 at hv ⊢
      generalize u₂.testBit h = b0 at hv ⊢
      generalize u₂.testBit (h + 1) = b1 at hv ⊢
      cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> first
        | rfl
        | exact absurd hv h01 | exact absurd hv.symm h01
        | exact absurd hv h02 | exact absurd hv.symm h02
        | exact absurd hv h03 | exact absurd hv.symm h03
        | exact absurd hv h12 | exact absurd hv.symm h12
        | exact absurd hv h13 | exact absurd hv.symm h13
        | exact absurd hv h23 | exact absurd hv.symm h23
  rw [hinj_iff, ok5Bool_eq_rCov]
  have hp1 : p1 = xor (winBit h k start x 5) (xor (winBit h k start x 4) (winBit h k start x 3)) :=
    pulse_false_eq hh hk (i := 1)
  have hp2 : p2 = xor (winBit h k start x 6) (xor (winBit h k start x 5) (winBit h k start x 4)) :=
    pulse_false_eq hh hk (i := 2)
  have hp3 : p3 = xor (winBit h k start x 7) (xor (winBit h k start x 6) (winBit h k start x 5)) :=
    pulse_false_eq hh hk (i := 3)
  have hp4 : p4 = xor (winBit h k start x 8) (xor (winBit h k start x 7) (winBit h k start x 6)) :=
    pulse_false_eq hh hk (i := 4)
  have hp5 : p5 = xor (winBit h k start x 9) (xor (winBit h k start x 8) (winBit h k start x 7)) :=
    pulse_false_eq hh hk (i := 5)
  rw [hp1, hp2, hp3, hp4, hp5]
  rfl

private lemma injOn_tail4_iff {h k start x : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (c : Fin h → Bool) :
    Set.InjOn (tailSet h k start true x 4) (fiberSet h c) ↔
      cCov (winCType
        (winBit h k start x 1) (winBit h k start x 2) (winBit h k start x 3)
        (winBit h k start x 4) (winBit h k start x 5) (winBit h k start x 6)
        (winBit h k start x 7) (winBit h k start x 8) (winBit h k start x 9))
        (c ⟨h - 2, by omega⟩) (c ⟨h - 1, by omega⟩) = true := by
  let p1 := pulseFn k start true x (h - 5 + 1)
  let p2 := pulseFn k start true x (h - 5 + 2)
  let p3 := pulseFn k start true x (h - 5 + 3)
  let p4 := pulseFn k start true x (h - 5 + 4)
  let p5 := pulseFn k start true x (h - 5 + 5)
  let p6 := pulseFn k start true x (h - 5 + 6)
  let z1 := c ⟨h - 4, by omega⟩
  let z2 := c ⟨h - 3, by omega⟩
  let z3 := c ⟨h - 2, by omega⟩
  let z4 := c ⟨h - 1, by omega⟩
  have htail_eq : ∀ (a0 a1 b0 b1 : Bool),
      tailSet h k start true x 4 (liftFiber c a0 a1) =
        tailSet h k start true x 4 (liftFiber c b0 b1) ↔
      tail4Vec p2 p3 p4 p5 p6 z2 z3 z4 a0 a1 =
        tail4Vec p2 p3 p4 p5 p6 z2 z3 z4 b0 b1 := by
    intro a0 a1 b0 b1
    have hA := liftFiber_top_bits hh c a0 a1
    have hB := liftFiber_top_bits hh c b0 b1
    dsimp only at hA hB
    have heval : ∀ (t0 t1 : Bool) (j : Nat), j < 4 →
        (j ∈ tailSet h k start true x 4 (liftFiber c t0 t1) ↔
          chiFn (fun i => xor ((liftFiber c t0 t1).testBit i) (pulseFn k start true x i))
            (h - 4 + j) = true) := by
      intro t0 t1 j hj
      simp [tailSet, hj]
    have hset_iff :
        tailSet h k start true x 4 (liftFiber c a0 a1) =
          tailSet h k start true x 4 (liftFiber c b0 b1) ↔
        ∀ j < 4,
          chiFn (fun i => xor ((liftFiber c a0 a1).testBit i) (pulseFn k start true x i))
            (h - 4 + j) =
          chiFn (fun i => xor ((liftFiber c b0 b1).testBit i) (pulseFn k start true x i))
            (h - 4 + j) := by
      constructor
      · intro heq j hj
        apply Bool.eq_iff_iff.mpr
        rw [← heval a0 a1 j hj, ← heval b0 b1 j hj, heq]
      · intro hall
        ext j
        by_cases hj : j < 4
        · rw [heval a0 a1 j hj, heval b0 b1 j hj, hall j hj]
        · simp [tailSet, hj]
    rw [hset_iff]
    have h4 : (∀ j < 4,
        chiFn (fun i => xor ((liftFiber c a0 a1).testBit i) (pulseFn k start true x i)) (h - 4 + j) =
        chiFn (fun i => xor ((liftFiber c b0 b1).testBit i) (pulseFn k start true x i)) (h - 4 + j)) ↔
        (chiFn (fun i => xor ((liftFiber c a0 a1).testBit i) (pulseFn k start true x i)) (h - 5 + 1) =
         chiFn (fun i => xor ((liftFiber c b0 b1).testBit i) (pulseFn k start true x i)) (h - 5 + 1) ∧
         chiFn (fun i => xor ((liftFiber c a0 a1).testBit i) (pulseFn k start true x i)) (h - 5 + 2) =
         chiFn (fun i => xor ((liftFiber c b0 b1).testBit i) (pulseFn k start true x i)) (h - 5 + 2) ∧
         chiFn (fun i => xor ((liftFiber c a0 a1).testBit i) (pulseFn k start true x i)) (h - 5 + 3) =
         chiFn (fun i => xor ((liftFiber c b0 b1).testBit i) (pulseFn k start true x i)) (h - 5 + 3) ∧
         chiFn (fun i => xor ((liftFiber c a0 a1).testBit i) (pulseFn k start true x i)) (h - 5 + 4) =
         chiFn (fun i => xor ((liftFiber c b0 b1).testBit i) (pulseFn k start true x i)) (h - 5 + 4)) := by
      have e0 : h - 4 + 0 = h - 5 + 1 := by omega
      have e1 : h - 4 + 1 = h - 5 + 2 := by omega
      have e2 : h - 4 + 2 = h - 5 + 3 := by omega
      have e3 : h - 4 + 3 = h - 5 + 4 := by omega
      constructor
      · intro h
        exact ⟨e0 ▸ h 0 (by omega), e1 ▸ h 1 (by omega), e2 ▸ h 2 (by omega), e3 ▸ h 3 (by omega)⟩
      · rintro ⟨c0, c1, c2, c3⟩ j hj
        interval_cases j
        · rwa [e0]
        · rwa [e1]
        · rwa [e2]
        · rwa [e3]
    rw [h4]
    unfold chiFn tail4Vec
    simp only [Nat.add_assoc, Prod.mk.injEq]
    rcases hA with ⟨hA6, hA5, hA4, hA3, hA2, hA1, _⟩
    rcases hB with ⟨hB6, hB5, hB4, hB3, hB2, hB1, _⟩
    rw [hA6, hA5, hA4, hA3, hA2, hA1, hB6, hB5, hB4, hB3, hB2, hB1]
    dsimp only [p1, p2, p3, p4, p5, p6, z1, z2, z3, z4]
    rw [xor_reassoc, xor_reassoc, xor_const_eq_iff]
  have hinj_iff : Set.InjOn (tailSet h k start true x 4) (fiberSet h c) ↔
      ok4Bool p2 p3 p4 p5 p6 z2 z3 z4 = true := by
    unfold ok4Bool
    simp only [Bool.and_eq_true, bne_iff_ne]
    constructor
    · intro hinj
      have hne : ∀ a0 a1 b0 b1 : Bool, (a0 ≠ b0 ∨ a1 ≠ b1) →
          tail4Vec p2 p3 p4 p5 p6 z2 z3 z4 a0 a1 ≠
            tail4Vec p2 p3 p4 p5 p6 z2 z3 z4 b0 b1 := by
        intro a0 a1 b0 b1 hdiff heq
        have ht := (htail_eq a0 a1 b0 b1).mpr heq
        have hu := hinj (liftFiber_mem c a0 a1) (liftFiber_mem c b0 b1) ht
        have hp := liftFiber_inj c hu
        rcases hdiff with h | h <;> [exact h hp.1; exact h hp.2]
      exact ⟨⟨⟨⟨⟨hne false false true false (Or.inl (by decide)),
                 hne false false false true (Or.inr (by decide))⟩,
                hne false false true true (Or.inl (by decide))⟩,
               hne true false false true (Or.inl (by decide))⟩,
              hne true false true true (Or.inr (by decide))⟩,
             hne false true true true (Or.inl (by decide))⟩
    · rintro ⟨⟨⟨⟨⟨h01, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩ u₁ hu1 u₂ hu2 heq
      rw [liftFiber_unique hu1, liftFiber_unique hu2] at heq ⊢
      have hv := (htail_eq _ _ _ _).mp heq
      generalize u₁.testBit h = a0 at hv ⊢
      generalize u₁.testBit (h + 1) = a1 at hv ⊢
      generalize u₂.testBit h = b0 at hv ⊢
      generalize u₂.testBit (h + 1) = b1 at hv ⊢
      cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> first
        | rfl
        | exact absurd hv h01 | exact absurd hv.symm h01
        | exact absurd hv h02 | exact absurd hv.symm h02
        | exact absurd hv h03 | exact absurd hv.symm h03
        | exact absurd hv h12 | exact absurd hv.symm h12
        | exact absurd hv h13 | exact absurd hv.symm h13
        | exact absurd hv h23 | exact absurd hv.symm h23
  rw [hinj_iff, ok4Bool_eq_cCov]
  have hp2 : p2 = xor (winBit h k start x 5) (xor (winBit h k start x 3) (winBit h k start x 1)) :=
    pulse_true_eq hh hk (i := 2) (by omega)
  have hp3 : p3 = xor (winBit h k start x 6) (xor (winBit h k start x 4) (winBit h k start x 2)) :=
    pulse_true_eq hh hk (i := 3) (by omega)
  have hp4 : p4 = xor (winBit h k start x 7) (xor (winBit h k start x 5) (winBit h k start x 3)) :=
    pulse_true_eq hh hk (i := 4) (by omega)
  have hp5 : p5 = xor (winBit h k start x 8) (xor (winBit h k start x 6) (winBit h k start x 4)) :=
    pulse_true_eq hh hk (i := 5) (by omega)
  rw [hp2, hp3, hp4, hp5]
  rfl

private def xPairId (h k start x : Nat) : Fin 11 :=
  pairId
    (winRType
      (winBit h k start x 1) (winBit h k start x 2) (winBit h k start x 3)
      (winBit h k start x 4) (winBit h k start x 5) (winBit h k start x 6)
      (winBit h k start x 7) (winBit h k start x 8) (winBit h k start x 9))
    (winCType
      (winBit h k start x 1) (winBit h k start x 2) (winBit h k start x 3)
      (winBit h k start x 4) (winBit h k start x 5) (winBit h k start x 6)
      (winBit h k start x 7) (winBit h k start x 8) (winBit h k start x 9))

private lemma okProp_iff_pairCov {h k start x : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (r c : Fin h → Bool) :
    okProp h k start x r c ↔
      pairCov (xPairId h k start x)
        (r ⟨h - 3, by omega⟩) (r ⟨h - 2, by omega⟩) (r ⟨h - 1, by omega⟩)
        (c ⟨h - 2, by omega⟩) (c ⟨h - 1, by omega⟩) = true := by
  unfold okProp
  rw [injOn_tail5_iff hh hk r, injOn_tail4_iff hh hk c]
  rw [← Bool.and_eq_true]
  have hall := win_pairId_exact
    (winBit h k start x 1) (winBit h k start x 2) (winBit h k start x 3)
    (winBit h k start x 4) (winBit h k start x 5) (winBit h k start x 6)
    (winBit h k start x 7) (winBit h k start x 8) (winBit h k start x 9)
  rw [pairCov_eq_of_allowed _ _ hall]
  rfl

-- Construct x < 2^k with prescribed winBit m for m = 1..9!
private def buildX (h k start : Nat) (w : Nat → Bool) : Fin (2 ^ k) :=
  ⟨packBits (fun idx =>
    (List.range 9).any (fun t =>
      decide ((start + (h - 5) + (t + 1) + k - 4) % k = idx) && w (t + 1))) k,
    packBits_lt _ k⟩

private lemma pos_mod_inj {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    {t₁ t₂ : Nat} (h1 : t₁ < 9) (h2 : t₂ < 9)
    (heq : (start + (h - 5) + (t₁ + 1) + k - 4) % k =
           (start + (h - 5) + (t₂ + 1) + k - 4) % k) : t₁ = t₂ := by
  have hk11 : 11 ≤ k := by omega
  have hbase : ∀ t < 9, start + (h - 5) + (t + 1) + k - 4 = (start + (h - 5) + (k - 3)) + t := by
    intro t _; omega
  rw [hbase t₁ h1, hbase t₂ h2] at heq
  set B := start + (h - 5) + (k - 3)
  have e1 := Nat.div_add_mod (B + t₁) k
  have e2 := Nat.div_add_mod (B + t₂) k
  rw [heq] at e1
  set q1 := (B + t₁) / k
  set q2 := (B + t₂) / k
  by_cases hq : q1 = q2
  · rw [hq] at e1; omega
  · rcases Nat.lt_or_gt_of_ne hq with hlt | hgt
    · have hmul : k * (q1 + 1) ≤ k * q2 := Nat.mul_le_mul_left k hlt
      have : k * (q1 + 1) = k * q1 + k := by ring
      omega
    · have hmul : k * (q2 + 1) ≤ k * q1 := Nat.mul_le_mul_left k hgt
      have : k * (q2 + 1) = k * q2 + k := by ring
      omega

private lemma winBit_buildX {h k start : Nat} (hh : 5 ≤ h) (hk : h + 6 ≤ k)
    (w : Nat → Bool) {m : Nat} (hm1 : 1 ≤ m) (hm9 : m ≤ 9) :
    winBit h k start (buildX h k start w).val m = w m := by
  unfold winBit buildX
  dsimp only
  rw [packBits_testBit]
  have hkpos : 0 < k := by omega
  have hlt : (start + (h - 5) + m + k - 4) % k < k := Nat.mod_lt _ hkpos
  simp only [hlt, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hboth⟩
    rw [List.mem_range] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hboth
    have htm : t = m - 1 := pos_mod_inj hh hk ht (by omega) (by
      have em : m - 1 + 1 = m := by omega
      rw [em]; exact hboth.1)
    have em : t + 1 = m := by omega
    rw [← em]
    exact hboth.2
  · intro hwm
    refine ⟨m - 1, List.mem_range.mpr (by omega), ?_⟩
    have em : m - 1 + 1 = m := by omega
    simp [em, hwm]

-- Hamming distance helpers over ZMod 2
private def hamDist {m : Nat} (x y : Fin m → ZMod 2) : Nat :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

private lemma hamDist_symm {m : Nat} (x y : Fin m → ZMod 2) :
    hamDist x y = hamDist y x := by
  unfold hamDist
  congr 1; ext i; simp [ne_comm]

private lemma hamDist_self {m : Nat} (x : Fin m → ZMod 2) : hamDist x x = 0 := by
  simp [hamDist]

private lemma hamDist_triangle {m : Nat} (x y z : Fin m → ZMod 2) :
    hamDist x z ≤ hamDist x y + hamDist y z := by
  unfold hamDist
  have hsub : Finset.univ.filter (fun i => x i ≠ z i) ⊆
      Finset.univ.filter (fun i => x i ≠ y i) ∪ Finset.univ.filter (fun i => y i ≠ z i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_cases hxy : x i = y i
    · exact Or.inr (by rwa [← hxy])
    · exact Or.inl hxy
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private lemma hamDist_sub_eq {m : Nat} (x y : Fin m → ZMod 2) :
    hamDist x y = hamDist (x - y) 0 := by
  unfold hamDist
  congr 1; ext i
  simp [sub_ne_zero]

private lemma exists_midpoint {m e : Nat} {x y : Fin m → ZMod 2}
    (h : hamDist x y ≤ 2 * e) :
    ∃ s : Fin m → ZMod 2, hamDist x s ≤ e ∧ hamDist y s ≤ e := by
  let D : Finset (Fin m) := Finset.univ.filter (fun i => x i ≠ y i)
  have hD : D.card ≤ 2 * e := h
  by_cases hle : D.card ≤ e
  · exact ⟨y, hle, by rw [hamDist_self]; exact Nat.zero_le _⟩
  · have hge : e ≤ D.card := by omega
    rcases Finset.exists_subset_card_eq hge with ⟨S, hSD, hScard⟩
    let s : Fin m → ZMod 2 := fun i => if i ∈ S then y i else x i
    refine ⟨s, ?_, ?_⟩
    · have hsub : Finset.univ.filter (fun i => x i ≠ s i) ⊆ S := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, s] at hi
        by_contra hni
        simp [hni] at hi
      calc hamDist x s ≤ S.card := Finset.card_le_card hsub
        _ = e := hScard
    · have hsub : Finset.univ.filter (fun i => y i ≠ s i) ⊆ D \ S := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, s] at hi
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · intro hxy
          by_cases hS : i ∈ S <;> simp [hS, hxy] at hi
        · intro hS
          simp [hS] at hi
      have hds : (D \ S).card = D.card - S.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSD]
      calc hamDist y s ≤ (D \ S).card := Finset.card_le_card hsub
        _ = D.card - e := by rw [hds, hScard]
        _ ≤ e := by omega

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma zmod2_decide_ne_zero_add (a b : ZMod 2) :
    decide (a + b ≠ 0) = xor (decide (a ≠ 0)) (decide (b ≠ 0)) := by
  fin_cases a <;> fin_cases b <;> decide

private lemma zmod2_of_bool_ne_zero (b : Bool) :
    decide ((if b then (1 : ZMod 2) else 0) ≠ 0) = b := by
  cases b <;> decide

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem main_proof :
    ∀ (h k start n a b e : Nat), 5 ≤ h → h+6 ≤ k →
      let tap := fun (x j back : Nat) => x.testBit ((start+j+k-back) % k)
      let pulse := fun (col : Bool) (x j : Nat) =>
        if col then xor (tap x j 1) (xor (tap x j 3) (tap x j 5))
        else xor (tap x j 0) (xor (tap x j 1) (tap x j 2))
      let chi := fun (bits : Nat → Bool) (j : Nat) =>
        xor (bits j) (!(bits (j+1)) && bits (j+2))
      let fiber := fun (z : Fin h → Bool) =>
        {u : Nat | u < 2^(h+2) ∧ ∀ j : Fin h, chi (fun i => u.testBit i) j = z j}
      let tail := fun (col : Bool) (x len u : Nat) =>
        (Finset.range len).filter (fun j =>
          chi (fun i => xor (u.testBit i) (pulse col x i)) (h-len+j))
      let ok := fun (x : Nat) (r c : Fin h → Bool) =>
        Set.InjOn (tail false x 5) (fiber r) ∧ Set.InjOn (tail true x 4) (fiber c)
      let F := ZMod 2
      let V := Fin n → Fin h → F
      let dist := fun {m : Nat} (x y : Fin m → F) =>
        (Finset.univ.filter (fun i => x i ≠ y i)).card
      let code := fun (m : Nat) =>
        ∃ E : (Fin (2*n) → F) →ₗ[F] (Fin m → F),
          ∀ u v, u ≠ v → 2*e < dist (E u) (E v)
      (∃ (menu : Fin 3 → Fin (2^k)) (L : V →ₗ[F] (Fin a → F))
         (R : V →ₗ[F] (Fin b → F)) (out : (Fin a → F) → (Fin b → F) → Fin n → Fin 3),
        Function.Injective menu ∧ ∀ (r c : V) (s : Fin a → F) (t : Fin b → F),
          dist (L r) s + dist (R c) t ≤ e →
          ∀ j, ok (menu (out s t j)).val (fun i => decide (r j i ≠ 0))
            (fun i => decide (c j i ≠ 0))) ↔ code a ∧ code b := by
  intro h k start n a b e hh hk
  dsimp only
  let F := ZMod 2
  let V := Fin n → Fin h → F
  constructor
  · rintro ⟨menu, L, R, out, _, hprot⟩
    by_cases hn : n = 0
    · subst hn
      constructor
      · refine ⟨0, ?_⟩
        intro u v huv
        exfalso; apply huv; funext i; exact Fin.elim0 i
      · refine ⟨0, ?_⟩
        intro u v huv
        exfalso; apply huv; funext i; exact Fin.elim0 i
    · have hn0 : 0 < n := by omega
      let t0 := xPairId h k start (menu ⟨0, by omega⟩).val
      let t1 := xPairId h k start (menu ⟨1, by omega⟩).val
      let t2 := xPairId h k start (menu ⟨2, by omega⟩).val
      -- Helper to build a Fin h -> F vector with given top 3 bits (z2, z3, z4)
      let mkR : Bool → Bool → Bool → (Fin h → F) := fun z2 z3 z4 i =>
        if i.val = h - 3 then (if z2 then 1 else 0)
        else if i.val = h - 2 then (if z3 then 1 else 0)
        else if i.val = h - 1 then (if z4 then 1 else 0)
        else 0
      let mkC : Bool → Bool → (Fin h → F) := fun c3 c4 i =>
        if i.val = h - 2 then (if c3 then 1 else 0)
        else if i.val = h - 1 then (if c4 then 1 else 0)
        else 0
      have hmkR_bits : ∀ z2 z3 z4,
          decide (mkR z2 z3 z4 ⟨h - 3, by omega⟩ ≠ 0) = z2 ∧
          decide (mkR z2 z3 z4 ⟨h - 2, by omega⟩ ≠ 0) = z3 ∧
          decide (mkR z2 z3 z4 ⟨h - 1, by omega⟩ ≠ 0) = z4 := by
        intro z2 z3 z4
        refine ⟨?_, ?_, ?_⟩
        · dsimp only [mkR]; simp only [↓reduceIte]; exact zmod2_of_bool_ne_zero z2
        · have hne : h - 2 ≠ h - 3 := by omega
          dsimp only [mkR]; simp only [hne, ↓reduceIte]; exact zmod2_of_bool_ne_zero z3
        · have hne1 : h - 1 ≠ h - 3 := by omega
          have hne2 : h - 1 ≠ h - 2 := by omega
          dsimp only [mkR]; simp only [hne1, hne2, ↓reduceIte]; exact zmod2_of_bool_ne_zero z4
      have hmkC_bits : ∀ c3 c4,
          decide (mkC c3 c4 ⟨h - 2, by omega⟩ ≠ 0) = c3 ∧
          decide (mkC c3 c4 ⟨h - 1, by omega⟩ ≠ 0) = c4 := by
        intro c3 c4
        refine ⟨?_, ?_⟩
        · dsimp only [mkC]; simp only [↓reduceIte]; exact zmod2_of_bool_ne_zero c3
        · have hne : h - 1 ≠ h - 2 := by omega
          dsimp only [mkC]; simp only [hne, ↓reduceIte]; exact zmod2_of_bool_ne_zero c4
      have hcov_all : ∀ z2 z3 z4 c3 c4 : Bool,
          pairCov t0 z2 z3 z4 c3 c4 = true ∨
          pairCov t1 z2 z3 z4 c3 c4 = true ∨
          pairCov t2 z2 z3 z4 c3 c4 = true := by
        intro z2 z3 z4 c3 c4
        let r : V := fun _ => mkR z2 z3 z4
        let c : V := fun _ => mkC c3 c4
        have hok := hprot r c (L r) (R c) (by
          change hamDist (L r) (L r) + hamDist (R c) (R c) ≤ e
          rw [hamDist_self, hamDist_self]; exact Nat.zero_le _) ⟨0, hn0⟩
        have hpc : pairCov (xPairId h k start (menu (out (L r) (R c) ⟨0, hn0⟩)).val)
            z2 z3 z4 c3 c4 = true := by
          have h1 := (okProp_iff_pairCov hh hk _ _).mp hok
          rcases hmkR_bits z2 z3 z4 with ⟨hr2, hr3, hr4⟩
          rcases hmkC_bits c3 c4 with ⟨hc3, hc4⟩
          simpa only [r, c, hr2, hr3, hr4, hc3, hc4] using h1
        have hidx := (out (L r) (R c) ⟨0, hn0⟩).isLt
        generalize hm : out (L r) (R c) ⟨0, hn0⟩ = m at hpc hidx
        rcases m with ⟨mv, hmv⟩
        interval_cases mv
        · exact Or.inl hpc
        · exact Or.inr (Or.inl hpc)
        · exact Or.inr (Or.inr hpc)
      have hcovB : tripleCoversB t0 t1 t2 = true := by
        unfold tripleCoversB
        simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true]
        intro z2 _ z3 _ z4 _ c3 _ c4 _
        rcases hcov_all z2 z3 z4 c3 c4 with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      have hsep := converse_finite t0 t1 t2 hcovB
      have hsepR : ∀ a b : Bool × Bool × Bool,
          rPairSep t0 t1 t2 a b = true →
          ∃ c3 c4 : Bool, ∀ m : Fin 3,
            ¬(pairCov (xPairId h k start (menu m).val) a.1 a.2.1 a.2.2 c3 c4 = true ∧
              pairCov (xPairId h k start (menu m).val) b.1 b.2.1 b.2.2 c3 c4 = true) := by
        intro a b hs
        unfold rPairSep at hs
        rw [List.any_eq_true] at hs
        rcases hs with ⟨⟨c3, c4⟩, _, hcond⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hcond
        refine ⟨c3, c4, ?_⟩
        rintro ⟨mv, hmv⟩ ⟨ha, hb⟩
        interval_cases mv
        · rcases hcond.1.1 with h | h <;> [exact Bool.false_ne_true (h.symm.trans ha);
            exact Bool.false_ne_true (h.symm.trans hb)]
        · rcases hcond.1.2 with h | h <;> [exact Bool.false_ne_true (h.symm.trans ha);
            exact Bool.false_ne_true (h.symm.trans hb)]
        · rcases hcond.2 with h | h <;> [exact Bool.false_ne_true (h.symm.trans ha);
            exact Bool.false_ne_true (h.symm.trans hb)]
      have hsepC : ∀ a b : Bool × Bool,
          cPairSep t0 t1 t2 a b = true →
          ∃ z2 z3 z4 : Bool, ∀ m : Fin 3,
            ¬(pairCov (xPairId h k start (menu m).val) z2 z3 z4 a.1 a.2 = true ∧
              pairCov (xPairId h k start (menu m).val) z2 z3 z4 b.1 b.2 = true) := by
        intro a b hs
        unfold cPairSep at hs
        rw [List.any_eq_true] at hs
        rcases hs with ⟨⟨z2, z3, z4⟩, _, hcond⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hcond
        refine ⟨z2, z3, z4, ?_⟩
        rintro ⟨mv, hmv⟩ ⟨ha, hb⟩
        interval_cases mv
        · rcases hcond.1.1 with h | h <;> [exact Bool.false_ne_true (h.symm.trans ha);
            exact Bool.false_ne_true (h.symm.trans hb)]
        · rcases hcond.1.2 with h | h <;> [exact Bool.false_ne_true (h.symm.trans ha);
            exact Bool.false_ne_true (h.symm.trans hb)]
        · rcases hcond.2 with h | h <;> [exact Bool.false_ne_true (h.symm.trans ha);
            exact Bool.false_ne_true (h.symm.trans hb)]
      -- Now construct code a and code b!
      constructor
      · -- code a: embL puts u_{2j} at h-3 and u_{2j+1} at h-2 and h-1
        let embL : (Fin (2 * n) → F) →ₗ[F] V :=
          { toFun := fun u j i =>
              if i.val = h - 3 then u ⟨2 * j.val, by omega⟩
              else if i.val = h - 2 ∨ i.val = h - 1 then u ⟨2 * j.val + 1, by omega⟩
              else 0
            map_add' := fun u v => by
              funext j i
              change (if i.val = h - 3 then (u + v) ⟨2 * j.val, by omega⟩
                else if i.val = h - 2 ∨ i.val = h - 1 then (u + v) ⟨2 * j.val + 1, by omega⟩ else 0) =
                (if i.val = h - 3 then u ⟨2 * j.val, by omega⟩
                else if i.val = h - 2 ∨ i.val = h - 1 then u ⟨2 * j.val + 1, by omega⟩ else 0) +
                (if i.val = h - 3 then v ⟨2 * j.val, by omega⟩
                else if i.val = h - 2 ∨ i.val = h - 1 then v ⟨2 * j.val + 1, by omega⟩ else 0)
              by_cases h3 : i.val = h - 3
              · simp [h3]
              · by_cases h21 : i.val = h - 2 ∨ i.val = h - 1 <;> simp [h3, h21]
            map_smul' := fun s u => by
              funext j i
              change (if i.val = h - 3 then (s • u) ⟨2 * j.val, by omega⟩
                else if i.val = h - 2 ∨ i.val = h - 1 then (s • u) ⟨2 * j.val + 1, by omega⟩ else 0) =
                s * (if i.val = h - 3 then u ⟨2 * j.val, by omega⟩
                else if i.val = h - 2 ∨ i.val = h - 1 then u ⟨2 * j.val + 1, by omega⟩ else 0)
              by_cases h3 : i.val = h - 3
              · simp [h3]
              · by_cases h21 : i.val = h - 2 ∨ i.val = h - 1 <;> simp [h3, h21] }
        refine ⟨L.comp embL, ?_⟩
        intro u v huv
        by_contra hle
        push_neg at hle
        let w : Fin (2 * n) → F := u - v
        have hw_ne : w ≠ 0 := sub_ne_zero.mpr huv
        have hex_idx : ∃ p : Fin (2 * n), w p ≠ 0 := by
          by_contra hall
          push_neg at hall
          exact hw_ne (funext hall)
        rcases hex_idx with ⟨p, hp⟩
        let j₀ : Fin n := ⟨p.val / 2, by omega⟩
        have hwj0 : w ⟨2 * j₀.val, by omega⟩ ≠ 0 ∨ w ⟨2 * j₀.val + 1, by omega⟩ ≠ 0 := by
          by_cases hev : p.val % 2 = 0
          · left
            have heq : (⟨2 * j₀.val, by omega⟩ : Fin (2 * n)) = p := Fin.ext (by dsimp [j₀]; omega)
            rwa [heq]
          · right
            have heq : (⟨2 * j₀.val + 1, by omega⟩ : Fin (2 * n)) = p :=
              Fin.ext (by dsimp [j₀]; omega)
            rwa [heq]
        -- Split w at every j into r1 j - r2 j = embL w j with r1, r2 in {R0, R1, R6}!
        let r1 : V := fun j =>
          let a0 := decide (w ⟨2 * j.val, by omega⟩ ≠ 0)
          let a1 := decide (w ⟨2 * j.val + 1, by omega⟩ ≠ 0)
          if a0 && a1 then mkR true false false else mkR false false false
        let r2 : V := fun j =>
          let a0 := decide (w ⟨2 * j.val, by omega⟩ ≠ 0)
          let a1 := decide (w ⟨2 * j.val + 1, by omega⟩ ≠ 0)
          if a0 && a1 then mkR false true true
          else if a0 then mkR true false false
          else if a1 then mkR false true true
          else mkR false false false
        have hdiff_r : r1 - r2 = embL w := by
          funext j i
          change r1 j i - r2 j i = embL w j i
          rw [zmod2_sub_eq_add]
          dsimp only [r1, r2, embL, LinearMap.coe_mk, AddHom.coe_mk]
          have hne23 : h - 2 ≠ h - 3 := by omega
          have hne13 : h - 1 ≠ h - 3 := by omega
          have hne12 : h - 1 ≠ h - 2 := by omega
          generalize hw0 : w ⟨2 * j.val, by omega⟩ = x0
          generalize hw1 : w ⟨2 * j.val + 1, by omega⟩ = x1
          have hd0 : decide ((0 : F) ≠ 0) = false := rfl
          have hd1 : decide ((1 : F) ≠ 0) = true := rfl
          by_cases h3 : i.val = h - 3
          · rcases zmod2_eq_zero_or_one x0 with rfl | rfl <;>
              rcases zmod2_eq_zero_or_one x1 with rfl | rfl <;>
              simp only [hd0, hd1, Bool.false_and, Bool.and_false, Bool.and_self,
                Bool.false_eq_true, ↓reduceIte, mkR, h3] <;> decide
          · by_cases h2 : i.val = h - 2
            · rcases zmod2_eq_zero_or_one x0 with rfl | rfl <;>
                rcases zmod2_eq_zero_or_one x1 with rfl | rfl <;>
                simp only [hd0, hd1, Bool.false_and, Bool.and_false, Bool.and_self,
                  Bool.false_eq_true, ↓reduceIte, mkR, h2, hne23, true_or] <;> decide
            · by_cases h1 : i.val = h - 1
              · rcases zmod2_eq_zero_or_one x0 with rfl | rfl <;>
                  rcases zmod2_eq_zero_or_one x1 with rfl | rfl <;>
                  simp only [hd0, hd1, Bool.false_and, Bool.and_false, Bool.and_self,
                    Bool.false_eq_true, ↓reduceIte, mkR, h1, hne13, hne12, or_true] <;> decide
              · rcases zmod2_eq_zero_or_one x0 with rfl | rfl <;>
                  rcases zmod2_eq_zero_or_one x1 with rfl | rfl <;>
                  simp only [hd0, hd1, Bool.false_and, Bool.and_false, Bool.and_self,
                    Bool.false_eq_true, ↓reduceIte, mkR, h3, h2, h1, or_self] <;> decide
        have hdist_r : hamDist (L r1) (L r2) ≤ 2 * e := by
          have h1 : hamDist (L r1) (L r2) = hamDist (L (embL w)) 0 := by
            rw [hamDist_sub_eq, ← map_sub, hdiff_r]
          have h2 : hamDist (L (embL u)) (L (embL v)) = hamDist (L (embL w)) 0 := by
            rw [hamDist_sub_eq, ← map_sub, ← map_sub]
          change hamDist (L (embL u)) (L (embL v)) ≤ 2 * e at hle
          omega
        rcases exists_midpoint hdist_r with ⟨s, hs1, hs2⟩
        -- Get separating c3, c4 at j0!
        have hpair_sep : ∃ c3 c4 : Bool, ∀ m : Fin 3,
            ¬(pairCov (xPairId h k start (menu m).val)
                (decide (r1 j₀ ⟨h - 3, by omega⟩ ≠ 0))
                (decide (r1 j₀ ⟨h - 2, by omega⟩ ≠ 0))
                (decide (r1 j₀ ⟨h - 1, by omega⟩ ≠ 0)) c3 c4 = true ∧
              pairCov (xPairId h k start (menu m).val)
                (decide (r2 j₀ ⟨h - 3, by omega⟩ ≠ 0))
                (decide (r2 j₀ ⟨h - 2, by omega⟩ ≠ 0))
                (decide (r2 j₀ ⟨h - 1, by omega⟩ ≠ 0)) c3 c4 = true) := by
          have hb0 := hmkR_bits false false false
          have hb1 := hmkR_bits true false false
          have hb6 := hmkR_bits false true true
          by_cases ha0 : decide (w ⟨2 * j₀.val, by omega⟩ ≠ 0) = true
          · by_cases ha1 : decide (w ⟨2 * j₀.val + 1, by omega⟩ ≠ 0) = true
            · rcases hsepR _ _ hsep.2.2.1 with ⟨c3, c4, hc⟩
              refine ⟨c3, c4, fun m => ?_⟩
              simpa only [r1, r2, ha0, ha1, Bool.and_self, ↓reduceIte,
                hb1.1, hb1.2.1, hb1.2.2, hb6.1, hb6.2.1, hb6.2.2] using hc m
            · have ha1f : decide (w ⟨2 * j₀.val + 1, by omega⟩ ≠ 0) = false :=
                Bool.eq_false_iff.mpr ha1
              rcases hsepR _ _ hsep.1 with ⟨c3, c4, hc⟩
              refine ⟨c3, c4, fun m => ?_⟩
              simpa only [r1, r2, ha0, ha1f, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                hb0.1, hb0.2.1, hb0.2.2, hb1.1, hb1.2.1, hb1.2.2] using hc m
          · have ha0f : decide (w ⟨2 * j₀.val, by omega⟩ ≠ 0) = false :=
              Bool.eq_false_iff.mpr ha0
            have ha1 : decide (w ⟨2 * j₀.val + 1, by omega⟩ ≠ 0) = true := by
              rcases hwj0 with h0 | h1
              · exfalso; exact ha0 (decide_eq_true h0)
              · exact decide_eq_true h1
            rcases hsepR _ _ hsep.2.1 with ⟨c3, c4, hc⟩
            refine ⟨c3, c4, fun m => ?_⟩
            simpa only [r1, r2, ha0f, ha1, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              hb0.1, hb0.2.1, hb0.2.2, hb6.1, hb6.2.1, hb6.2.2] using hc m
        rcases hpair_sep with ⟨c3, c4, hno⟩
        let c : V := fun _ => mkC c3 c4
        have hok1 := hprot r1 c s (R c) (by
          change hamDist (L r1) s + hamDist (R c) (R c) ≤ e
          rw [hamDist_self, Nat.add_zero]; exact hs1) j₀
        have hok2 := hprot r2 c s (R c) (by
          change hamDist (L r2) s + hamDist (R c) (R c) ≤ e
          rw [hamDist_self, Nat.add_zero]; exact hs2) j₀
        have hp1 := (okProp_iff_pairCov hh hk _ _).mp hok1
        have hp2 := (okProp_iff_pairCov hh hk _ _).mp hok2
        rcases hmkC_bits c3 c4 with ⟨hc3, hc4⟩
        simp only [c, hc3, hc4] at hp1 hp2
        exact hno (out s (R c) j₀) ⟨hp1, hp2⟩
      · -- code b: embR puts u_{2j} at h-2 and u_{2j+1} at h-1
        let embR : (Fin (2 * n) → F) →ₗ[F] V :=
          { toFun := fun u j i =>
              if i.val = h - 2 then u ⟨2 * j.val, by omega⟩
              else if i.val = h - 1 then u ⟨2 * j.val + 1, by omega⟩
              else 0
            map_add' := fun u v => by
              funext j i
              change (if i.val = h - 2 then (u + v) ⟨2 * j.val, by omega⟩
                else if i.val = h - 1 then (u + v) ⟨2 * j.val + 1, by omega⟩ else 0) =
                (if i.val = h - 2 then u ⟨2 * j.val, by omega⟩
                else if i.val = h - 1 then u ⟨2 * j.val + 1, by omega⟩ else 0) +
                (if i.val = h - 2 then v ⟨2 * j.val, by omega⟩
                else if i.val = h - 1 then v ⟨2 * j.val + 1, by omega⟩ else 0)
              have hne12 : h - 1 ≠ h - 2 := by omega
              by_cases h2 : i.val = h - 2
              · simp [h2]
              · by_cases h1 : i.val = h - 1
                · simp [h1, hne12]
                · simp [h2, h1]
            map_smul' := fun s u => by
              funext j i
              change (if i.val = h - 2 then (s • u) ⟨2 * j.val, by omega⟩
                else if i.val = h - 1 then (s • u) ⟨2 * j.val + 1, by omega⟩ else 0) =
                s * (if i.val = h - 2 then u ⟨2 * j.val, by omega⟩
                else if i.val = h - 1 then u ⟨2 * j.val + 1, by omega⟩ else 0)
              have hne12 : h - 1 ≠ h - 2 := by omega
              by_cases h2 : i.val = h - 2
              · simp [h2]
              · by_cases h1 : i.val = h - 1
                · simp [h1, hne12]
                · simp [h2, h1] }
        refine ⟨R.comp embR, ?_⟩
        intro u v huv
        by_contra hle
        push_neg at hle
        let w : Fin (2 * n) → F := u - v
        have hw_ne : w ≠ 0 := sub_ne_zero.mpr huv
        have hex_idx : ∃ p : Fin (2 * n), w p ≠ 0 := by
          by_contra hall
          push_neg at hall
          exact hw_ne (funext hall)
        rcases hex_idx with ⟨p, hp⟩
        let j₀ : Fin n := ⟨p.val / 2, by omega⟩
        have hwj0 : w ⟨2 * j₀.val, by omega⟩ ≠ 0 ∨ w ⟨2 * j₀.val + 1, by omega⟩ ≠ 0 := by
          by_cases hev : p.val % 2 = 0
          · left
            have heq : (⟨2 * j₀.val, by omega⟩ : Fin (2 * n)) = p := Fin.ext (by dsimp [j₀]; omega)
            rwa [heq]
          · right
            have heq : (⟨2 * j₀.val + 1, by omega⟩ : Fin (2 * n)) = p :=
              Fin.ext (by dsimp [j₀]; omega)
            rwa [heq]
        let c1 : V := fun j =>
          let a0 := decide (w ⟨2 * j.val, by omega⟩ ≠ 0)
          let a1 := decide (w ⟨2 * j.val + 1, by omega⟩ ≠ 0)
          if a0 && a1 then mkC true false else mkC false false
        let c2 : V := fun j =>
          let a0 := decide (w ⟨2 * j.val, by omega⟩ ≠ 0)
          let a1 := decide (w ⟨2 * j.val + 1, by omega⟩ ≠ 0)
          if a0 && a1 then mkC false true
          else if a0 then mkC true false
          else if a1 then mkC false true
          else mkC false false
        have hdiff_c : c1 - c2 = embR w := by
          funext j i
          change c1 j i - c2 j i = embR w j i
          rw [zmod2_sub_eq_add]
          dsimp only [c1, c2, embR, LinearMap.coe_mk, AddHom.coe_mk]
          generalize hw0 : w ⟨2 * j.val, by omega⟩ = x0
          generalize hw1 : w ⟨2 * j.val + 1, by omega⟩ = x1
          have hd0 : decide ((0 : F) ≠ 0) = false := rfl
          have hd1 : decide ((1 : F) ≠ 0) = true := rfl
          have hne12 : h - 1 ≠ h - 2 := by omega
          by_cases h2 : i.val = h - 2
          · rcases zmod2_eq_zero_or_one x0 with rfl | rfl <;>
              rcases zmod2_eq_zero_or_one x1 with rfl | rfl <;>
              simp only [hd0, hd1, Bool.false_and, Bool.and_false, Bool.and_self,
                Bool.false_eq_true, ↓reduceIte, mkC, h2] <;> decide
          · by_cases h1 : i.val = h - 1
            · rcases zmod2_eq_zero_or_one x0 with rfl | rfl <;>
                rcases zmod2_eq_zero_or_one x1 with rfl | rfl <;>
                simp only [hd0, hd1, Bool.false_and, Bool.and_false, Bool.and_self,
                  Bool.false_eq_true, ↓reduceIte, mkC, h1, hne12] <;> decide
            · rcases zmod2_eq_zero_or_one x0 with rfl | rfl <;>
                rcases zmod2_eq_zero_or_one x1 with rfl | rfl <;>
                simp only [hd0, hd1, Bool.false_and, Bool.and_false, Bool.and_self,
                  Bool.false_eq_true, ↓reduceIte, mkC, h2, h1] <;> decide
        have hdist_c : hamDist (R c1) (R c2) ≤ 2 * e := by
          have h1 : hamDist (R c1) (R c2) = hamDist (R (embR w)) 0 := by
            rw [hamDist_sub_eq, ← map_sub, hdiff_c]
          have h2 : hamDist (R (embR u)) (R (embR v)) = hamDist (R (embR w)) 0 := by
            rw [hamDist_sub_eq, ← map_sub, ← map_sub]
          change hamDist (R (embR u)) (R (embR v)) ≤ 2 * e at hle
          omega
        rcases exists_midpoint hdist_c with ⟨t, ht1, ht2⟩
        have hpair_sep : ∃ z2 z3 z4 : Bool, ∀ m : Fin 3,
            ¬(pairCov (xPairId h k start (menu m).val) z2 z3 z4
                (decide (c1 j₀ ⟨h - 2, by omega⟩ ≠ 0))
                (decide (c1 j₀ ⟨h - 1, by omega⟩ ≠ 0)) = true ∧
              pairCov (xPairId h k start (menu m).val) z2 z3 z4
                (decide (c2 j₀ ⟨h - 2, by omega⟩ ≠ 0))
                (decide (c2 j₀ ⟨h - 1, by omega⟩ ≠ 0)) = true) := by
          have hb0 := hmkC_bits false false
          have hb1 := hmkC_bits true false
          have hb2 := hmkC_bits false true
          by_cases ha0 : decide (w ⟨2 * j₀.val, by omega⟩ ≠ 0) = true
          · by_cases ha1 : decide (w ⟨2 * j₀.val + 1, by omega⟩ ≠ 0) = true
            · rcases hsepC _ _ hsep.2.2.2.2.2 with ⟨z2, z3, z4, hr⟩
              refine ⟨z2, z3, z4, fun m => ?_⟩
              simpa only [c1, c2, ha0, ha1, Bool.and_self, ↓reduceIte,
                hb1.1, hb1.2, hb2.1, hb2.2] using hr m
            · have ha1f : decide (w ⟨2 * j₀.val + 1, by omega⟩ ≠ 0) = false :=
                Bool.eq_false_iff.mpr ha1
              rcases hsepC _ _ hsep.2.2.2.1 with ⟨z2, z3, z4, hr⟩
              refine ⟨z2, z3, z4, fun m => ?_⟩
              simpa only [c1, c2, ha0, ha1f, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                hb0.1, hb0.2, hb1.1, hb1.2] using hr m
          · have ha0f : decide (w ⟨2 * j₀.val, by omega⟩ ≠ 0) = false :=
              Bool.eq_false_iff.mpr ha0
            have ha1 : decide (w ⟨2 * j₀.val + 1, by omega⟩ ≠ 0) = true := by
              rcases hwj0 with h0 | h1
              · exfalso; exact ha0 (decide_eq_true h0)
              · exact decide_eq_true h1
            rcases hsepC _ _ hsep.2.2.2.2.1 with ⟨z2, z3, z4, hr⟩
            refine ⟨z2, z3, z4, fun m => ?_⟩
            simpa only [c1, c2, ha0f, ha1, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              hb0.1, hb0.2, hb2.1, hb2.2] using hr m
        rcases hpair_sep with ⟨z2, z3, z4, hno⟩
        let r : V := fun _ => mkR z2 z3 z4
        have hok1 := hprot r c1 (L r) t (by
          change hamDist (L r) (L r) + hamDist (R c1) t ≤ e
          rw [hamDist_self, Nat.zero_add]; exact ht1) j₀
        have hok2 := hprot r c2 (L r) t (by
          change hamDist (L r) (L r) + hamDist (R c2) t ≤ e
          rw [hamDist_self, Nat.zero_add]; exact ht2) j₀
        have hp1 := (okProp_iff_pairCov hh hk _ _).mp hok1
        have hp2 := (okProp_iff_pairCov hh hk _ _).mp hok2
        rcases hmkR_bits z2 z3 z4 with ⟨hr2, hr3, hr4⟩
        simp only [r, hr2, hr3, hr4] at hp1 hp2
        exact hno (out (L r) t j₀) ⟨hp1, hp2⟩
  · -- Sufficiency: code a ∧ code b -> protocol!
    rintro ⟨⟨Ea, hEa⟩, ⟨Eb, hEb⟩⟩
    let w0 : Nat → Bool := fun m => decide (m = 4 ∨ m = 7)
    let w1 : Nat → Bool := fun m => decide (m = 1 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 7)
    let w2 : Nat → Bool := fun m => decide (m = 3 ∨ m = 4 ∨ m = 7)
    let menu : Fin 3 → Fin (2 ^ k) := fun idx =>
      match idx.val with
      | 0 => buildX h k start w0
      | 1 => buildX h k start w1
      | _ => buildX h k start w2
    have hmenu_inj : Function.Injective menu := by
      intro i₁ i₂ heq
      have hwb : ∀ m, 1 ≤ m → m ≤ 9 →
          winBit h k start (menu i₁).val m = winBit h k start (menu i₂).val m := by
        intro m _ _; rw [heq]
      have hm0 : menu ⟨0, by omega⟩ = buildX h k start w0 := rfl
      have hm1 : menu ⟨1, by omega⟩ = buildX h k start w1 := rfl
      have hm2 : menu ⟨2, by omega⟩ = buildX h k start w2 := rfl
      rcases i₁ with ⟨v1, hv1⟩
      rcases i₂ with ⟨v2, hv2⟩
      interval_cases v1 <;> interval_cases v2
      · rfl
      · exfalso
        have h1 := hwb 1 (by omega) (by omega)
        rw [hm0, hm1, winBit_buildX hh hk w0 (by omega) (by omega),
            winBit_buildX hh hk w1 (by omega) (by omega)] at h1
        exact Bool.false_ne_true h1
      · exfalso
        have h3 := hwb 3 (by omega) (by omega)
        rw [hm0, hm2, winBit_buildX hh hk w0 (by omega) (by omega),
            winBit_buildX hh hk w2 (by omega) (by omega)] at h3
        exact Bool.false_ne_true h3
      · exfalso
        have h1 := hwb 1 (by omega) (by omega)
        rw [hm1, hm0, winBit_buildX hh hk w1 (by omega) (by omega),
            winBit_buildX hh hk w0 (by omega) (by omega)] at h1
        exact Bool.false_ne_true h1.symm
      · rfl
      · exfalso
        have h1 := hwb 1 (by omega) (by omega)
        rw [hm1, hm2, winBit_buildX hh hk w1 (by omega) (by omega),
            winBit_buildX hh hk w2 (by omega) (by omega)] at h1
        exact Bool.false_ne_true h1.symm
      · exfalso
        have h3 := hwb 3 (by omega) (by omega)
        rw [hm2, hm0, winBit_buildX hh hk w2 (by omega) (by omega),
            winBit_buildX hh hk w0 (by omega) (by omega)] at h3
        exact Bool.false_ne_true h3.symm
      · exfalso
        have h1 := hwb 1 (by omega) (by omega)
        rw [hm2, hm1, winBit_buildX hh hk w2 (by omega) (by omega),
            winBit_buildX hh hk w1 (by omega) (by omega)] at h1
        exact Bool.false_ne_true h1
      · rfl
    -- Linear extractors projL, projR : V ->ₗ (Fin (2*n) -> F)
    let projL : V →ₗ[F] (Fin (2 * n) → F) :=
      { toFun := fun r p =>
          let j : Fin n := ⟨p.val / 2, by omega⟩
          if p.val % 2 = 0 then r j ⟨h - 3, by omega⟩ + r j ⟨h - 2, by omega⟩
          else r j ⟨h - 1, by omega⟩
        map_add' := fun r₁ r₂ => by
          funext p
          let j : Fin n := ⟨p.val / 2, by omega⟩
          change (if p.val % 2 = 0 then (r₁ j ⟨h - 3, by omega⟩ + r₂ j ⟨h - 3, by omega⟩) +
              (r₁ j ⟨h - 2, by omega⟩ + r₂ j ⟨h - 2, by omega⟩)
            else r₁ j ⟨h - 1, by omega⟩ + r₂ j ⟨h - 1, by omega⟩) =
            (if p.val % 2 = 0 then r₁ j ⟨h - 3, by omega⟩ + r₁ j ⟨h - 2, by omega⟩
            else r₁ j ⟨h - 1, by omega⟩) +
            (if p.val % 2 = 0 then r₂ j ⟨h - 3, by omega⟩ + r₂ j ⟨h - 2, by omega⟩
            else r₂ j ⟨h - 1, by omega⟩)
          by_cases hev : p.val % 2 = 0
          · simp [hev]; ring
          · simp [hev]
        map_smul' := fun s r => by
          funext p
          let j : Fin n := ⟨p.val / 2, by omega⟩
          change (if p.val % 2 = 0 then s * r j ⟨h - 3, by omega⟩ + s * r j ⟨h - 2, by omega⟩
            else s * r j ⟨h - 1, by omega⟩) =
            s * (if p.val % 2 = 0 then r j ⟨h - 3, by omega⟩ + r j ⟨h - 2, by omega⟩
            else r j ⟨h - 1, by omega⟩)
          by_cases hev : p.val % 2 = 0
          · simp [hev, mul_add]
          · simp [hev] }
    let projR : V →ₗ[F] (Fin (2 * n) → F) :=
      { toFun := fun c p =>
          let j : Fin n := ⟨p.val / 2, by omega⟩
          if p.val % 2 = 0 then c j ⟨h - 2, by omega⟩
          else c j ⟨h - 1, by omega⟩
        map_add' := fun c₁ c₂ => by
          funext p
          let j : Fin n := ⟨p.val / 2, by omega⟩
          change (if p.val % 2 = 0 then c₁ j ⟨h - 2, by omega⟩ + c₂ j ⟨h - 2, by omega⟩
            else c₁ j ⟨h - 1, by omega⟩ + c₂ j ⟨h - 1, by omega⟩) =
            (if p.val % 2 = 0 then c₁ j ⟨h - 2, by omega⟩ else c₁ j ⟨h - 1, by omega⟩) +
            (if p.val % 2 = 0 then c₂ j ⟨h - 2, by omega⟩ else c₂ j ⟨h - 1, by omega⟩)
          by_cases hev : p.val % 2 = 0 <;> simp [hev]
        map_smul' := fun s c => by
          funext p
          let j : Fin n := ⟨p.val / 2, by omega⟩
          change (if p.val % 2 = 0 then s * c j ⟨h - 2, by omega⟩
            else s * c j ⟨h - 1, by omega⟩) =
            s * (if p.val % 2 = 0 then c j ⟨h - 2, by omega⟩ else c j ⟨h - 1, by omega⟩)
          by_cases hev : p.val % 2 = 0 <;> simp [hev] }
    let L : V →ₗ[F] (Fin a → F) := Ea.comp projL
    let R : V →ₗ[F] (Fin b → F) := Eb.comp projR
    -- Nearest-neighbor decoders (noncomputable via Classical.choose)
    let decA : (Fin a → F) → (Fin (2 * n) → F) := fun s =>
      if hex : ∃ u : Fin (2 * n) → F, hamDist (Ea u) s ≤ e then Classical.choose hex else 0
    let decB : (Fin b → F) → (Fin (2 * n) → F) := fun t =>
      if hex : ∃ u : Fin (2 * n) → F, hamDist (Eb u) t ≤ e then Classical.choose hex else 0
    have hdecA_exact : ∀ (u : Fin (2 * n) → F) (s : Fin a → F),
        hamDist (Ea u) s ≤ e → decA s = u := by
      intro u s hus
      have hex : ∃ v : Fin (2 * n) → F, hamDist (Ea v) s ≤ e := ⟨u, hus⟩
      dsimp only [decA]
      rw [dif_pos hex]
      have hspec : hamDist (Ea (Classical.choose hex)) s ≤ e := Classical.choose_spec hex
      by_contra hne
      have hgt : 2 * e < hamDist (Ea (Classical.choose hex)) (Ea u) := hEa _ _ hne
      have htri : hamDist (Ea (Classical.choose hex)) (Ea u) ≤
          hamDist (Ea (Classical.choose hex)) s + hamDist s (Ea u) :=
        hamDist_triangle _ _ _
      rw [hamDist_symm s (Ea u)] at htri
      omega
    have hdecB_exact : ∀ (u : Fin (2 * n) → F) (t : Fin b → F),
        hamDist (Eb u) t ≤ e → decB t = u := by
      intro u t hut
      have hex : ∃ v : Fin (2 * n) → F, hamDist (Eb v) t ≤ e := ⟨u, hut⟩
      dsimp only [decB]
      rw [dif_pos hex]
      have hspec : hamDist (Eb (Classical.choose hex)) t ≤ e := Classical.choose_spec hex
      by_contra hne
      have hgt : 2 * e < hamDist (Eb (Classical.choose hex)) (Eb u) := hEb _ _ hne
      have htri : hamDist (Eb (Classical.choose hex)) (Eb u) ≤
          hamDist (Eb (Classical.choose hex)) t + hamDist t (Eb u) :=
        hamDist_triangle _ _ _
      rw [hamDist_symm t (Eb u)] at htri
      omega
    let out : (Fin a → F) → (Fin b → F) → Fin n → Fin 3 := fun s t j =>
      let uA := decA s
      let uB := decB t
      selectMenu
        (decide (uA ⟨2 * j.val, by omega⟩ ≠ 0))
        (decide (uA ⟨2 * j.val + 1, by omega⟩ ≠ 0))
        (decide (uB ⟨2 * j.val, by omega⟩ ≠ 0))
        (decide (uB ⟨2 * j.val + 1, by omega⟩ ≠ 0))
    refine ⟨menu, L, R, out, hmenu_inj, ?_⟩
    intro r c s t hdist j
    change hamDist (Ea (projL r)) s + hamDist (Eb (projR c)) t ≤ e at hdist
    have hda : decA s = projL r := hdecA_exact (projL r) s (by omega)
    have hdb : decB t = projR c := hdecB_exact (projR c) t (by omega)
    have ha0 : decide ((decA s) ⟨2 * j.val, by omega⟩ ≠ 0) =
        xor (decide (r j ⟨h - 3, by omega⟩ ≠ 0)) (decide (r j ⟨h - 2, by omega⟩ ≠ 0)) := by
      rw [hda]
      dsimp only [projL, LinearMap.coe_mk, AddHom.coe_mk]
      have hm0 : (2 * j.val) % 2 = 0 := by omega
      have hd0 : (⟨(2 * j.val) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
      simp only [hm0, ↓reduceIte, hd0]
      exact zmod2_decide_ne_zero_add _ _
    have ha1 : decide ((decA s) ⟨2 * j.val + 1, by omega⟩ ≠ 0) =
        decide (r j ⟨h - 1, by omega⟩ ≠ 0) := by
      rw [hda]
      dsimp only [projL, LinearMap.coe_mk, AddHom.coe_mk]
      have hm1 : ¬ ((2 * j.val + 1) % 2 = 0) := by omega
      have hd1 : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
      simp only [hm1, ↓reduceIte, hd1]
    have hb0 : decide ((decB t) ⟨2 * j.val, by omega⟩ ≠ 0) =
        decide (c j ⟨h - 2, by omega⟩ ≠ 0) := by
      rw [hdb]
      dsimp only [projR, LinearMap.coe_mk, AddHom.coe_mk]
      have hm0 : (2 * j.val) % 2 = 0 := by omega
      have hd0 : (⟨(2 * j.val) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
      simp only [hm0, ↓reduceIte, hd0]
    have hb1 : decide ((decB t) ⟨2 * j.val + 1, by omega⟩ ≠ 0) =
        decide (c j ⟨h - 1, by omega⟩ ≠ 0) := by
      rw [hdb]
      dsimp only [projR, LinearMap.coe_mk, AddHom.coe_mk]
      have hm1 : ¬ ((2 * j.val + 1) % 2 = 0) := by omega
      have hd1 : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp only; omega)
      simp only [hm1, ↓reduceIte, hd1]
    change okProp h k start (menu (out s t j)).val
      (fun i => decide (r j i ≠ 0)) (fun i => decide (c j i ≠ 0))
    unfold okProp
    rw [injOn_tail5_iff hh hk, injOn_tail4_iff hh hk]
    have hsel := selectMenu_valid
      (decide (r j ⟨h - 3, by omega⟩ ≠ 0))
      (decide (r j ⟨h - 2, by omega⟩ ≠ 0))
      (decide (r j ⟨h - 1, by omega⟩ ≠ 0))
      (decide (c j ⟨h - 2, by omega⟩ ≠ 0))
      (decide (c j ⟨h - 1, by omega⟩ ≠ 0))
    have hout_eq : out s t j = selectMenu
        (xor (decide (r j ⟨h - 3, by omega⟩ ≠ 0)) (decide (r j ⟨h - 2, by omega⟩ ≠ 0)))
        (decide (r j ⟨h - 1, by omega⟩ ≠ 0))
        (decide (c j ⟨h - 2, by omega⟩ ≠ 0))
        (decide (c j ⟨h - 1, by omega⟩ ≠ 0)) := by
      dsimp only [out]
      rw [ha0, ha1, hb0, hb1]
    rw [hout_eq]
    generalize hmv : selectMenu
      (xor (decide (r j ⟨h - 3, by omega⟩ ≠ 0)) (decide (r j ⟨h - 2, by omega⟩ ≠ 0)))
      (decide (r j ⟨h - 1, by omega⟩ ≠ 0))
      (decide (c j ⟨h - 2, by omega⟩ ≠ 0))
      (decide (c j ⟨h - 1, by omega⟩ ≠ 0)) = m at hsel
    have hm0 : menu ⟨0, by omega⟩ = buildX h k start w0 := rfl
    have hm1 : menu ⟨1, by omega⟩ = buildX h k start w1 := rfl
    have hm2 : menu ⟨2, by omega⟩ = buildX h k start w2 := rfl
    rcases m with ⟨mv, hmlt⟩
    interval_cases mv
    · have hok := hsel.1 rfl
      rw [hm0,
        winBit_buildX hh hk w0 (m := 1) (by omega) (by omega),
        winBit_buildX hh hk w0 (m := 2) (by omega) (by omega),
        winBit_buildX hh hk w0 (m := 3) (by omega) (by omega),
        winBit_buildX hh hk w0 (m := 4) (by omega) (by omega),
        winBit_buildX hh hk w0 (m := 5) (by omega) (by omega),
        winBit_buildX hh hk w0 (m := 6) (by omega) (by omega),
        winBit_buildX hh hk w0 (m := 7) (by omega) (by omega),
        winBit_buildX hh hk w0 (m := 8) (by omega) (by omega),
        winBit_buildX hh hk w0 (m := 9) (by omega) (by omega)]
      have ht1 : winRType (w0 1) (w0 2) (w0 3) (w0 4) (w0 5) (w0 6) (w0 7) (w0 8) (w0 9) =
          ⟨1, by omega⟩ := witness0_types.1
      have ht2 : winCType (w0 1) (w0 2) (w0 3) (w0 4) (w0 5) (w0 6) (w0 7) (w0 8) (w0 9) =
          ⟨0, by omega⟩ := witness0_types.2
      rw [ht1, ht2]
      exact hok
    · have hok := hsel.2.1 rfl
      rw [hm1,
        winBit_buildX hh hk w1 (m := 1) (by omega) (by omega),
        winBit_buildX hh hk w1 (m := 2) (by omega) (by omega),
        winBit_buildX hh hk w1 (m := 3) (by omega) (by omega),
        winBit_buildX hh hk w1 (m := 4) (by omega) (by omega),
        winBit_buildX hh hk w1 (m := 5) (by omega) (by omega),
        winBit_buildX hh hk w1 (m := 6) (by omega) (by omega),
        winBit_buildX hh hk w1 (m := 7) (by omega) (by omega),
        winBit_buildX hh hk w1 (m := 8) (by omega) (by omega),
        winBit_buildX hh hk w1 (m := 9) (by omega) (by omega)]
      have ht1 : winRType (w1 1) (w1 2) (w1 3) (w1 4) (w1 5) (w1 6) (w1 7) (w1 8) (w1 9) =
          ⟨2, by omega⟩ := witness1_types.1
      have ht2 : winCType (w1 1) (w1 2) (w1 3) (w1 4) (w1 5) (w1 6) (w1 7) (w1 8) (w1 9) =
          ⟨1, by omega⟩ := witness1_types.2
      rw [ht1, ht2]
      exact hok
    · have hok := hsel.2.2 rfl
      rw [hm2,
        winBit_buildX hh hk w2 (m := 1) (by omega) (by omega),
        winBit_buildX hh hk w2 (m := 2) (by omega) (by omega),
        winBit_buildX hh hk w2 (m := 3) (by omega) (by omega),
        winBit_buildX hh hk w2 (m := 4) (by omega) (by omega),
        winBit_buildX hh hk w2 (m := 5) (by omega) (by omega),
        winBit_buildX hh hk w2 (m := 6) (by omega) (by omega),
        winBit_buildX hh hk w2 (m := 7) (by omega) (by omega),
        winBit_buildX hh hk w2 (m := 8) (by omega) (by omega),
        winBit_buildX hh hk w2 (m := 9) (by omega) (by omega)]
      have ht1 : winRType (w2 1) (w2 2) (w2 3) (w2 4) (w2 5) (w2 6) (w2 7) (w2 8) (w2 9) =
          ⟨0, by omega⟩ := witness2_types.1
      have ht2 : winCType (w2 1) (w2 2) (w2 3) (w2 4) (w2 5) (w2 6) (w2 7) (w2 8) (w2 9) =
          ⟨2, by omega⟩ := witness2_types.2
      rw [ht1, ht2]
      exact hok

end PEqualNP.Outside.L_meta_39006

theorem PEqualNP.Outside.L_meta_39006 :
∀ (h k start n a b e : Nat), 5 ≤ h → h+6 ≤ k →
  let tap := fun (x j back : Nat) => x.testBit ((start+j+k-back) % k)
  let pulse := fun (col : Bool) (x j : Nat) =>
    if col then xor (tap x j 1) (xor (tap x j 3) (tap x j 5))
    else xor (tap x j 0) (xor (tap x j 1) (tap x j 2))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let fiber := fun (z : Fin h → Bool) =>
    {u : Nat | u < 2^(h+2) ∧ ∀ j : Fin h, chi (fun i => u.testBit i) j = z j}
  let tail := fun (col : Bool) (x len u : Nat) =>
    (Finset.range len).filter (fun j =>
      chi (fun i => xor (u.testBit i) (pulse col x i)) (h-len+j))
  let ok := fun (x : Nat) (r c : Fin h → Bool) =>
    Set.InjOn (tail false x 5) (fiber r) ∧ Set.InjOn (tail true x 4) (fiber c)
  let F := ZMod 2
  let V := Fin n → Fin h → F
  let dist := fun {m : Nat} (x y : Fin m → F) =>
    (Finset.univ.filter (fun i => x i ≠ y i)).card
  let code := fun (m : Nat) =>
    ∃ E : (Fin (2*n) → F) →ₗ[F] (Fin m → F),
      ∀ u v, u ≠ v → 2*e < dist (E u) (E v)
  (∃ (menu : Fin 3 → Fin (2^k)) (L : V →ₗ[F] (Fin a → F))
     (R : V →ₗ[F] (Fin b → F)) (out : (Fin a → F) → (Fin b → F) → Fin n → Fin 3),
    Function.Injective menu ∧ ∀ (r c : V) (s : Fin a → F) (t : Fin b → F),
      dist (L r) s + dist (R c) t ≤ e →
      ∀ j, ok (menu (out s t j)).val (fun i => decide (r j i ≠ 0))
        (fun i => decide (c j i ≠ 0))) ↔ code a ∧ code b :=
  PEqualNP.Outside.L_meta_39006.main_proof
