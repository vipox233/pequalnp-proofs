import PEqualNP.Library.Helpers.K4Parity

namespace PEqualNP.Library.PrefixTripleExclusion

open PEqualNP.CircuitLowerBounds PEqualNP.Library.K4Parity

/-- Columns for four successively enabled inputs, followed by the two constants. -/
def initial : List Mask := [30, 28, 24, 16, 0, 31]

def targets (w : List Mask) : Prop :=
  20 ∈ w ∧ ((4 ∈ w ∧ 18 ∈ w) ∨ (6 ∈ w ∧ 17 ∈ w))

def hit (s : Nat) : Bool :=
  s.testBit 20 && ((s.testBit 4 && s.testBit 18) || (s.testBit 6 && s.testBit 17))

theorem covers_hit {s : Nat} {w : List Mask} (hw : covers s w) (h : targets w) :
    hit s = true := by
  obtain ⟨a, ⟨b,c⟩ | ⟨b,c⟩⟩ := h
  · have h20 := hw 20 a
    have h4 := hw 4 b
    have h18 := hw 18 c
    change s.testBit 20 = true at h20
    change s.testBit 4 = true at h4
    change s.testBit 18 = true at h18
    simp [hit, h20, h4, h18]
  · have h20 := hw 20 a
    have h6 := hw 6 b
    have h17 := hw 17 c
    change s.testBit 20 = true at h20
    change s.testBit 6 = true at h6
    change s.testBit 17 = true at h17
    simp [hit, h20, h6, h17]

def transitions (next : Nat → Bool) (s : Nat) : Bool :=
  let xs := pool s
  xs.all fun a => next (add s (~~~a)) && xs.all fun b =>
    next (add s (a &&& b)) && next (add s (a ||| b))

/-- Every admitted bank excludes both triples for every remaining gate sequence. -/
def safe (accept : Nat → Bool) (k : Nat) : Prop :=
  ∀ s, accept s = true → ∀ w : List Mask, covers s w → 0 ∈ w → 31 ∈ w →
    ∀ gs : List Gate, gs.length ≤ k → ¬ targets (run gs w)

theorem bottom : safe (fun s => !hit s) 0 := by
  intro s hs w hw _ _ gs hg h
  have eq : gs = [] := List.length_eq_zero_iff.mp (by omega)
  subst gs
  have ht := covers_hit hw h
  simp [ht] at hs

theorem transferLayer (cur : Tree) (next : Nat → Bool) (k : Nat)
    (tested : cur.every (fun s => !hit s && transitions next s) = true)
    (tailSafe : safe next k) : safe cur.has (k+1) := by
  intro s hs w hw h0 h31 gs hg h
  obtain ⟨noHit, moves⟩ := Bool.and_eq_true_iff.mp (cur.pass _ tested s hs)
  cases gs with
  | nil =>
    have ht := covers_hit hw h
    simp [ht] at noHit
  | cons g rest =>
    let t := make w g
    obtain ⟨ha,hb⟩ := make_operands w w g (fun _ h => h) h0 h31
    have qa := List.all_eq_true.mp moves t.a (poolMem (hw _ ha))
    obtain ⟨qn, qb⟩ := Bool.and_eq_true_iff.mp qa
    obtain ⟨qi, qu⟩ := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp qb t.b (poolMem (hw _ hb)))
    have hn : next (add s t.val) = true := by
      simp only [Step.val]
      split
      · exact qn
      · split
        · exact qu
        · exact qi
    have hc : covers (add s t.val) (w ++ [t.val]) := by
      intro m hm
      have hm' : m ∈ t.val :: w := by simpa [or_comm] using hm
      exact addCovers s t.val w hw m hm'
    apply tailSafe _ hn _ hc (List.mem_append_left _ h0) (List.mem_append_left _ h31) rest (by simpa using hg)
    exact h

def prefixRows (r : Fin 5) := List.ofFn (fun i : Fin 4 => decide (i.val < r.val)) ++ [false,true]

theorem initial_bits : ∀ r : Fin 5, initial.map (bit r) = prefixRows r := by decide

theorem atTap (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (i : Nat)
    (m : Mask) (nz : m ≠ 0) (h : ∀ r : Fin 5, (C.wires (prefixRows r)).getD i false = bit r m) :
    m ∈ run C.gates initial := by
  have goodG : ∀ g ∈ C.gates, good g := fun g hg => fan g hg
  let ws := run C.gates initial
  have eq : ws.getD i 0 = m := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro j hj
    let r : Fin 5 := ⟨j,hj⟩
    change bit r (ws.getD i 0) = bit r m
    rw [← read_bit, show ws.map (bit r) = C.wires (prefixRows r) by
      rw [show ws.map (bit r) = _ from run_bit r C.gates initial goodG, initial_bits]
      rfl]
    exact h r
  rcases get_mem ws i 0 with hm | hm
  · exact eq ▸ hm
  · exact False.elim (nz (eq.symm.trans hm))

end PEqualNP.Library.PrefixTripleExclusion
