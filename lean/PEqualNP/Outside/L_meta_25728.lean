import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_567

namespace PEqualNP.Outside.L_meta_25728_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

def b2r (b : Bool) : ℝ := if b then -1 else 1

def z2r (x : ZMod 2) : ℝ := if x = 1 then -1 else 1

def z2b (x : ZMod 2) : Bool := decide (x = 1)

lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

lemma z2r_b2z (b : Bool) : z2r (b2z b) = b2r b := by
  cases b <;> simp [b2z, b2r, z2r]

lemma z2r_zero : z2r 0 = 1 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [z2r, h01]

lemma z2r_one : z2r 1 = -1 := by
  simp [z2r]

lemma z2r_add (x y : ZMod 2) : z2r (x + y) = z2r x * z2r y := by
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> [left; right] <;> rfl
  have hy : y = 0 ∨ y = 1 := by fin_cases y <;> [left; right] <;> rfl
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp [z2r_zero]
  · simp [z2r_zero, z2r_one]
  · simp [z2r_zero, z2r_one]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h11, z2r_zero, z2r_one]
    norm_num

lemma z2r_mul_self (x : ZMod 2) : z2r x * z2r x = 1 := by
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> [left; right] <;> rfl
  rcases hx with rfl | rfl
  · simp [z2r_zero]
  · rw [z2r_one]
    norm_num

lemma b2r_xor (a b : Bool) : b2r (xor a b) = b2r a * b2r b := by
  cases a <;> cases b <;> norm_num [b2r]

lemma b2r_mul_self (a : Bool) : b2r a * b2r a = 1 := by
  cases a <;> norm_num [b2r]

lemma b2r_inj_neg (a b : Bool) : b2r a * b2r b = 2 * (if a = b then (1 : ℝ) else 0) - 1 := by
  cases a <;> cases b <;> norm_num [b2r]

lemma anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

lemma anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_snoc (x : List Bool) (gs : List Gate) (g : Gate) :
    wiresOf x (gs ++ [g]) =
      wiresOf x gs ++ [g.op.eval (g.inputs.map fun i => (wiresOf x gs).getD i false)] := by
  unfold wiresOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma wiresOf_snoc_getD_lt (x : List Bool) (gs : List Gate) (g : Gate) {k : ℕ}
    (hk : k < x.length + gs.length) :
    (wiresOf x (gs ++ [g])).getD k false = (wiresOf x gs).getD k false := by
  rw [wiresOf_snoc, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

lemma wiresOf_snoc_getD_eq (x : List Bool) (gs : List Gate) (g : Gate) :
    (wiresOf x (gs ++ [g])).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf x gs).getD i false) := by
  rw [wiresOf_snoc, List.getD_append_right _ _ _ _ (by rw [wiresOf_length])]
  simp [wiresOf_length]

lemma wiresOf_snoc_getD_gt (x : List Bool) (gs : List Gate) (g : Gate) {k : ℕ}
    (hk : x.length + gs.length < k) :
    (wiresOf x (gs ++ [g])).getD k false = false := by
  rw [List.getD_eq_default]
  rw [wiresOf_length, List.length_append, List.length_singleton]
  omega

lemma wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [wiresOf_snoc_getD_lt x gs g (by omega)]
    exact ih

lemma oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

lemma oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

lemma circuit_decomp {N : ℕ} (gs : List Gate)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (σ : Fin N → (Fin (2 * gs.countP nlGate) → ZMod 2))
      (L : ℕ → Fin N → ZMod 2)
      (R : ℕ → (Fin (2 * gs.countP nlGate) → ZMod 2) → Fin N → ZMod 2),
      ∀ (k : ℕ) (x y : Fin N),
        b2z ((wiresOf (oneEach x y) gs).getD k false) = L k x + R k (σ x) y := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ => Fin.elim0,
      fun k x => if k < N then b2z (decide (k = x.val)) else 0,
      fun k _ y => if N ≤ k ∧ k < N + N then b2z (decide (k - N = y.val)) else 0, ?_⟩
    intro k x y
    change b2z ((oneEach x y).getD k false) = _
    by_cases h1 : k < N
    · have h2 : ¬ (N ≤ k ∧ k < N + N) := by omega
      rw [oneEach_getD_left x y h1]
      simp [h1, h2]
    · by_cases h2 : k < N + N
      · have h3 : N ≤ k ∧ k < N + N := ⟨by omega, h2⟩
        rw [oneEach_getD_right x y (by omega) h2]
        simp [h1, h3]
      · have h3 : ¬ (N ≤ k ∧ k < N + N) := by omega
        rw [List.getD_eq_default _ _ (by rw [oneEach_length]; omega)]
        simp [h1, h3, b2z]
  | append_singleton gs g ih =>
    have hlen_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 :=
      fun g' hg' => hlen g' (List.mem_append_left [g] hg')
    have hlen_g : g.inputs.length ≤ 2 := hlen g (List.mem_append_right gs (List.mem_singleton_self g))
    set r := gs.countP nlGate
    obtain ⟨σ0, L0, R0, hspec⟩ := ih hlen_gs
    have hcount : (gs ++ [g]).countP nlGate = r + (if nlGate g then 1 else 0) := by
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases nlGate g <;> simp [r]
    by_cases hnl : nlGate g = true
    · have hlen2 : g.inputs.length = 2 := by
        unfold nlGate at hnl
        simp only [Bool.and_eq_true, beq_iff_eq] at hnl
        exact hnl.1
      have hpair : ∃ a b, g.inputs = [a, b] := by
        rcases hgs : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · simp [hgs] at hlen2
        · simp [hgs] at hlen2
        · exact ⟨a, b, rfl⟩
        · simp [hgs] at hlen2
      obtain ⟨a, b, hgs⟩ := hpair
      have hcnt2 : 2 * (gs ++ [g]).countP nlGate = 2 * r + 2 := by
        rw [hcount, hnl]; simp; omega
      let σ' : Fin N → (Fin (2 * (gs ++ [g]).countP nlGate) → ZMod 2) := fun x idx =>
        if hlt : idx.val < 2 * r then σ0 x ⟨idx.val, hlt⟩
        else if idx.val = 2 * r then L0 a x
        else L0 b x
      let proj : (Fin (2 * (gs ++ [g]).countP nlGate) → ZMod 2) → (Fin (2 * r) → ZMod 2) :=
        fun τ idx => τ ⟨idx.val, by omega⟩
      let bit1 : (Fin (2 * (gs ++ [g]).countP nlGate) → ZMod 2) → ZMod 2 :=
        fun τ => τ ⟨2 * r, by omega⟩
      let bit2 : (Fin (2 * (gs ++ [g]).countP nlGate) → ZMod 2) → ZMod 2 :=
        fun τ => τ ⟨2 * r + 1, by omega⟩
      have hproj : ∀ x, proj (σ' x) = σ0 x := by
        intro x; funext idx
        simp [proj, σ', idx.isLt]
      have hbit1 : ∀ x, bit1 (σ' x) = L0 a x := by
        intro x; simp [bit1, σ']
      have hbit2 : ∀ x, bit2 (σ' x) = L0 b x := by
        intro x; simp [bit2, σ']
      let L' : ℕ → Fin N → ZMod 2 := fun k x =>
        if k < N + N + gs.length then L0 k x else 0
      let R' : ℕ → (Fin (2 * (gs ++ [g]).countP nlGate) → ZMod 2) → Fin N → ZMod 2 := fun k τ y =>
        if k < N + N + gs.length then R0 k (proj τ) y
        else if k = N + N + gs.length then
          b2z (g.op.eval [z2b (bit1 τ + R0 a (proj τ) y), z2b (bit2 τ + R0 b (proj τ) y)])
        else 0
      refine ⟨σ', L', R', ?_⟩
      intro k x y
      by_cases hk1 : k < N + N + gs.length
      · have hk1' : k < (oneEach x y).length + gs.length := by rw [oneEach_length]; exact hk1
        rw [wiresOf_snoc_getD_lt _ gs g hk1']
        simp only [L', R', hk1, ite_true, hproj]
        exact hspec k x y
      · by_cases hk2 : k = N + N + gs.length
        · subst hk2
          have hlen_in : (oneEach x y).length + gs.length = N + N + gs.length := by
            rw [oneEach_length]
          rw [← hlen_in, wiresOf_snoc_getD_eq, hgs]
          simp only [List.map_cons, L', R', hlen_in, lt_irrefl, ite_false,
            ite_true, zero_add, hproj, hbit1, hbit2]
          rw [← hspec a x y, ← hspec b x y, z2b_b2z, z2b_b2z]
          rfl
        · have hk3 : (oneEach x y).length + gs.length < k := by rw [oneEach_length]; omega
          rw [wiresOf_snoc_getD_gt _ gs g hk3]
          simp [L', R', hk1, hk2, b2z]
    · have hnlF : nlGate g = false := Bool.eq_false_iff.mpr hnl
      have hcntEq : 2 * (gs ++ [g]).countP nlGate = 2 * r := by
        rw [hcount, hnlF]; simp
      let castσ : Fin N → (Fin (2 * (gs ++ [g]).countP nlGate) → ZMod 2) :=
        fun x idx => σ0 x (idx.cast hcntEq)
      let uncast : (Fin (2 * (gs ++ [g]).countP nlGate) → ZMod 2) → (Fin (2 * r) → ZMod 2) :=
        fun τ idx => τ (idx.cast hcntEq.symm)
      have huncast : ∀ x, uncast (castσ x) = σ0 x := by
        intro x; funext idx; simp [uncast, castσ]
      have hlin : ∃ (c0 : ZMod 2) (fL : Fin N → ZMod 2) (fR : (Fin (2 * r) → ZMod 2) → Fin N → ZMod 2),
          ∀ x y, b2z (g.op.eval (g.inputs.map fun i => (wiresOf (oneEach x y) gs).getD i false)) =
            fL x + (c0 + fR (σ0 x) y) := by
        rcases hgs : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · refine ⟨b2z (g.op.eval []), fun _ => 0, fun _ _ => 0, fun x y => ?_⟩
          simp
        · refine ⟨b2z (g.op.eval [false]),
            fun x => (b2z (g.op.eval [false]) + b2z (g.op.eval [true])) * L0 a x,
            fun τ y => (b2z (g.op.eval [false]) + b2z (g.op.eval [true])) * R0 a τ y,
            fun x y => ?_⟩
          simp only [List.map_cons, List.map_nil]
          have ha := anf_one (fun u => g.op.eval [u]) ((wiresOf (oneEach x y) gs).getD a false)
          rw [ha, hspec a x y]
          ring
        · have hxor0 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
              (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
            unfold nlGate at hnlF
            rw [hgs] at hnlF
            simpa using hnlF
          refine ⟨b2z (g.op.eval [false, false]),
            fun x => (b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])) * L0 a x +
              (b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])) * L0 b x,
            fun τ y => (b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])) * R0 a τ y +
              (b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])) * R0 b τ y,
            fun x y => ?_⟩
          simp only [List.map_cons, List.map_nil]
          have hab := anf_two (fun u v => g.op.eval [u, v])
            ((wiresOf (oneEach x y) gs).getD a false)
            ((wiresOf (oneEach x y) gs).getD b false)
          have hb0 : b2z false = 0 := rfl
          rw [hab, hxor0, hb0, zero_mul, add_zero, hspec a x y, hspec b x y]
          ring
        · simp [hgs] at hlen_g
      obtain ⟨c0, fL, fR, hf⟩ := hlin
      let L' : ℕ → Fin N → ZMod 2 := fun k x =>
        if k < N + N + gs.length then L0 k x
        else if k = N + N + gs.length then fL x
        else 0
      let R' : ℕ → (Fin (2 * (gs ++ [g]).countP nlGate) → ZMod 2) → Fin N → ZMod 2 := fun k τ y =>
        if k < N + N + gs.length then R0 k (uncast τ) y
        else if k = N + N + gs.length then c0 + fR (uncast τ) y
        else 0
      refine ⟨castσ, L', R', ?_⟩
      intro k x y
      by_cases hk1 : k < N + N + gs.length
      · have hk1' : k < (oneEach x y).length + gs.length := by rw [oneEach_length]; exact hk1
        rw [wiresOf_snoc_getD_lt _ gs g hk1']
        simp only [L', R', hk1, ite_true, huncast]
        exact hspec k x y
      · by_cases hk2 : k = N + N + gs.length
        · subst hk2
          have hlen_in : (oneEach x y).length + gs.length = N + N + gs.length := by
            rw [oneEach_length]
          rw [← hlen_in, wiresOf_snoc_getD_eq]
          simp only [L', R', hlen_in, lt_irrefl, ite_false, ite_true, huncast]
          exact hf x y
        · have hk3 : (oneEach x y).length + gs.length < k := by rw [oneEach_length]; omega
          rw [wiresOf_snoc_getD_gt _ gs g hk3]
          simp [L', R', hk1, hk2, b2z]

lemma circuit_orthonormal_span {N t : ℕ} (hN : 0 < N) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP nlGate ≤ t) :
    ∃ (m : ℕ) (e : Fin m → Fin N → ℝ) (coeff : Fin m → Fin N → ℝ),
      0 < m ∧ m ≤ 2 ^ (2 * t) ∧
      (∀ a b, ∑ x : Fin N, e a x * e b x = if a = b then 1 else 0) ∧
      (∀ x y : Fin N, b2r (C.eval (oneEach x y)) = ∑ a : Fin m, coeff a y * e a x) := by
  classical
  obtain ⟨σ, L, R, hspec⟩ := circuit_decomp (N := N) C.gates hlen
  let T : Finset (Fin (2 * C.gates.countP nlGate) → ZMod 2) := Finset.univ.image σ
  have hT_pos : 0 < T.card := by
    rw [Finset.card_pos]
    exact ⟨σ ⟨0, hN⟩, Finset.mem_image.mpr ⟨⟨0, hN⟩, Finset.mem_univ _, rfl⟩⟩
  have hT_le : T.card ≤ 2 ^ (2 * t) := by
    calc T.card ≤ Fintype.card (Fin (2 * C.gates.countP nlGate) → ZMod 2) := Finset.card_le_univ T
      _ = 2 ^ (2 * C.gates.countP nlGate) := by simp [ZMod.card]
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by omega) (by omega)
  let eqv : Fin T.card ≃ {τ // τ ∈ T} := T.equivFin.symm
  let blk : Fin T.card → Finset (Fin N) :=
    fun a => Finset.univ.filter (fun x : Fin N => σ x = (eqv a).val)
  have hblk_pos : ∀ a, 0 < (blk a).card := by
    intro a
    rw [Finset.card_pos]
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (eqv a).2
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  let e : Fin T.card → Fin N → ℝ := fun a x =>
    if σ x = (eqv a).val then z2r (L C.output x) / Real.sqrt ((blk a).card : ℝ) else 0
  let coeff : Fin T.card → Fin N → ℝ := fun a y =>
    Real.sqrt ((blk a).card : ℝ) * z2r (R C.output (eqv a).val y)
  refine ⟨T.card, e, coeff, hT_pos, hT_le, ?_, ?_⟩
  · intro a b
    by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      have hcard_pos : (0 : ℝ) < ((blk a).card : ℝ) := by exact_mod_cast hblk_pos a
      have hsq : Real.sqrt ((blk a).card : ℝ) * Real.sqrt ((blk a).card : ℝ) = ((blk a).card : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hcard_pos)
      have hterm : ∀ x : Fin N, e a x * e a x =
          if x ∈ blk a then ((blk a).card : ℝ)⁻¹ else 0 := by
        intro x
        simp only [e, blk, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with h
        · rw [div_mul_div_comm, z2r_mul_self, hsq, one_div]
        · ring
      simp only [hterm, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt hcard_pos)
    · simp only [hab, ite_false]
      apply Finset.sum_eq_zero
      intro x _
      simp only [e]
      split_ifs with h1 h2
      · exfalso
        apply hab
        apply eqv.injective
        apply Subtype.ext
        exact h1.symm.trans h2
      · simp
      · simp
      · simp
  · intro x y
    have hval : b2r (C.eval (oneEach x y)) = z2r (L C.output x) * z2r (R C.output (σ x) y) := by
      change b2r ((wiresOf (oneEach x y) C.gates).getD C.output false) = _
      rw [← z2r_b2z, hspec C.output x y, z2r_add]
    rw [hval]
    have hmem : σ x ∈ T := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    let a0 : Fin T.card := eqv.symm ⟨σ x, hmem⟩
    have ha0 : (eqv a0).val = σ x := by
      simp [a0]
    rw [Finset.sum_eq_single a0]
    · have hcard_pos : (0 : ℝ) < ((blk a0).card : ℝ) := by exact_mod_cast hblk_pos a0
      have hsqrt_ne : Real.sqrt ((blk a0).card : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcard_pos)
      simp only [coeff, e, ha0, ite_true]
      field_simp [hsqrt_ne]
    · intro a _ hne
      simp only [e]
      have hne' : σ x ≠ (eqv a).val := by
        intro h
        apply hne
        have : eqv a = ⟨σ x, hmem⟩ := Subtype.ext h.symm
        simpa [a0] using congrArg eqv.symm this
      simp [hne']
    · intro h; exact absurd (Finset.mem_univ a0) h

def dotBit (k : ℕ) (x y : ℕ) : Bool :=
  ((Finset.univ : Finset (Fin k)).filter (fun b => x.testBit b.val && y.testBit b.val)).card % 2 == 1

def hBit (k : ℕ) (x y : ℕ) : ℝ := b2r (dotBit k x y)

lemma neg_one_pow_eq_mod2 (n : ℕ) : (-1 : ℝ) ^ n = if n % 2 == 1 then -1 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h1 : (n + 1) % 2 = 1 := by omega
      simp [h, h1]
    · have h1 : (n + 1) % 2 = 0 := by omega
      simp [h, h1]

lemma hBit_eq_prod (k x y : ℕ) :
    hBit k x y = ∏ b ∈ Finset.range k, (if x.testBit b && y.testBit b then (-1 : ℝ) else 1) := by
  unfold hBit dotBit b2r
  rw [← neg_one_pow_eq_mod2]
  have h1 : (∏ b ∈ Finset.range k, (if x.testBit b && y.testBit b then (-1 : ℝ) else 1)) =
      ∏ b : Fin k, (if x.testBit b.val && y.testBit b.val then (-1 : ℝ) else 1) :=
    (Fin.prod_univ_eq_prod_range (fun b => if x.testBit b && y.testBit b then (-1 : ℝ) else 1) k).symm
  rw [h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

lemma hBit_comm (k x y : ℕ) : hBit k x y = hBit k y x := by
  rw [hBit_eq_prod, hBit_eq_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Bool.and_comm]

lemma hBit_xor_right (k x y1 y2 : ℕ) : hBit k x (y1 ^^^ y2) = hBit k x y1 * hBit k x y2 := by
  rw [hBit_eq_prod, hBit_eq_prod, hBit_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Nat.testBit_xor]
  cases x.testBit b <;> cases y1.testBit b <;> cases y2.testBit b <;> norm_num

lemma hBit_pow2 (k x b : ℕ) (hb : b < k) :
    hBit k x (2 ^ b) = if x.testBit b then -1 else 1 := by
  rw [hBit_eq_prod]
  rw [Finset.prod_eq_single b]
  · simp [Nat.testBit_two_pow_self]
  · intro c _ hcb
    have htb : (2 ^ b).testBit c = false := by
      rw [Nat.testBit_two_pow]
      simp [Ne.symm hcb]
    simp [htb]
  · intro h; exact absurd (Finset.mem_range.mpr hb) h

lemma hBit_ortho (k : ℕ) (x x' : Fin (2 ^ k)) :
    ∑ y : Fin (2 ^ k), hBit k x.val y.val * hBit k x'.val y.val =
      if x = x' then (2 ^ k : ℝ) else 0 := by
  by_cases hxx : x = x'
  · subst hxx
    simp only [ite_true]
    have h1 : ∀ y : Fin (2 ^ k), hBit k x.val y.val * hBit k x.val y.val = 1 :=
      fun y => b2r_mul_self _
    simp [h1]
  · simp only [hxx, ite_false]
    have hne : x.val ≠ x'.val := fun h => hxx (Fin.ext h)
    have hex : ∃ b < k, x.val.testBit b ≠ x'.val.testBit b := by
      by_contra hall
      push Not at hall
      apply hne
      apply Nat.eq_of_testBit_eq
      intro b
      by_cases hb : b < k
      · exact hall b hb
      · have h1 : x.val.testBit b = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
        have h2 : x'.val.testBit b = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le x'.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
        rw [h1, h2]
    obtain ⟨b, hb, hdiff⟩ := hex
    have h2b : 2 ^ b < 2 ^ k := Nat.pow_lt_pow_right (by omega) hb
    let flip : Fin (2 ^ k) ≃ Fin (2 ^ k) :=
      { toFun := fun y => ⟨y.val ^^^ 2 ^ b, Nat.xor_lt_two_pow y.isLt h2b⟩
        invFun := fun y => ⟨y.val ^^^ 2 ^ b, Nat.xor_lt_two_pow y.isLt h2b⟩
        left_inv := fun y => Fin.ext (by simp)
        right_inv := fun y => Fin.ext (by simp) }
    have hneg : hBit k x.val (2 ^ b) * hBit k x'.val (2 ^ b) = -1 := by
      rw [hBit_pow2 k x.val b hb, hBit_pow2 k x'.val b hb]
      cases hx : x.val.testBit b <;> cases hx' : x'.val.testBit b <;> simp_all
    have hsum : (∑ y : Fin (2 ^ k), hBit k x.val y.val * hBit k x'.val y.val) =
        ∑ y : Fin (2 ^ k), hBit k x.val (flip y).val * hBit k x'.val (flip y).val :=
      (Equiv.sum_comp flip (fun y : Fin (2 ^ k) => hBit k x.val y.val * hBit k x'.val y.val)).symm
    have hstep : ∀ y : Fin (2 ^ k),
        hBit k x.val (flip y).val * hBit k x'.val (flip y).val =
          -(hBit k x.val y.val * hBit k x'.val y.val) := by
      intro y
      change hBit k x.val (y.val ^^^ 2 ^ b) * hBit k x'.val (y.val ^^^ 2 ^ b) = _
      rw [hBit_xor_right, hBit_xor_right]
      calc (hBit k x.val y.val * hBit k x.val (2 ^ b)) *
            (hBit k x'.val y.val * hBit k x'.val (2 ^ b))
          = (hBit k x.val y.val * hBit k x'.val y.val) *
              (hBit k x.val (2 ^ b) * hBit k x'.val (2 ^ b)) := by ring
        _ = (hBit k x.val y.val * hBit k x'.val y.val) * (-1) := by rw [hneg]
        _ = -(hBit k x.val y.val * hBit k x'.val y.val) := by ring
    simp only [hstep, Finset.sum_neg_distrib] at hsum
    linarith

lemma hBit_split (a b x y : ℕ) :
    hBit (a + b) x y = hBit a x y * hBit b (x >>> a) (y >>> a) := by
  rw [hBit_eq_prod, hBit_eq_prod, hBit_eq_prod, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]

lemma hBit_mod_right (k x y : ℕ) : hBit k x (y % 2 ^ k) = hBit k x y := by
  rw [hBit_eq_prod, hBit_eq_prod]
  refine Finset.prod_congr rfl fun b hb => ?_
  have hlt : b < k := Finset.mem_range.mp hb
  rw [Nat.testBit_mod_two_pow, decide_eq_true hlt, Bool.true_and]

lemma hBit_mod_left (k x y : ℕ) : hBit k (x % 2 ^ k) y = hBit k x y := by
  rw [hBit_comm, hBit_mod_right, hBit_comm]

lemma b2r_eq_imp {a b : Bool} (h : b2r a = b2r b) : a = b := by
  cases a <;> cases b <;> simp [b2r] at h ⊢ <;> norm_num at h

lemma dotBit_split (a b x y : ℕ) :
    dotBit (a + b) x y = xor (dotBit a x y) (dotBit b (x >>> a) (y >>> a)) := by
  apply b2r_eq_imp
  rw [b2r_xor]
  exact hBit_split a b x y

lemma dotBit_succ (k x y : ℕ) :
    dotBit (k + 1) x y = xor (dotBit k x y) (x.testBit k && y.testBit k) := by
  apply b2r_eq_imp
  rw [b2r_xor]
  change hBit (k + 1) x y = hBit k x y * b2r (x.testBit k && y.testBit k)
  rw [hBit_eq_prod, Finset.prod_range_succ, ← hBit_eq_prod]
  rfl

lemma part1_bounds (s t : ℕ) (hts : t ≤ s) :
    let N := 2 ^ (2 * s)
    let h : ℕ := 2 ^ (s - t)
    ∀ (l : ℕ) (Cs : Fin l → Circuit) (p : Fin l → ℚ),
      (∀ i, (∀ g ∈ (Cs i).gates, g.inputs.length ≤ 2) ∧
        ReadsBack (N + N) (Cs i) ∧ (Cs i).gates.countP nlGate ≤ t) →
      (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
      let success := fun (x y : Fin N) =>
        ∑ i : Fin l, if (Cs i).eval (oneEach x y) = dotBit (2 * s) x.val y.val then p i else 0
      (∃ x y, 2 * (h : ℚ) * success x y ≤ (h : ℚ) + 1) ∧
      ((∀ x y, (h : ℚ) + 1 ≤ 2 * (h : ℚ) * success x y) →
        ∀ i, (h : ℚ) ^ 2 * p i ≤ 1) := by
  intro N h l Cs p hval hp hsum success
  have hN_pos : 0 < N := by positivity
  have hN_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hh_pos : 0 < h := by positivity
  have hNh : (h : ℝ) ^ 2 * (2 ^ (2 * t) : ℝ) = (N : ℝ) := by
    have hnat : h ^ 2 * 2 ^ (2 * t) = N := by
      dsimp only [h, N]
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    exact_mod_cast hnat
  have hbasis : ∀ i : Fin l, ∃ (m : ℕ) (e : Fin m → Fin N → ℝ) (coeff : Fin m → Fin N → ℝ),
      0 < m ∧ m ≤ 2 ^ (2 * t) ∧
      (∀ a b, ∑ x : Fin N, e a x * e b x = if a = b then 1 else 0) ∧
      (∀ x y : Fin N, b2r ((Cs i).eval (oneEach x y)) = ∑ a : Fin m, coeff a y * e a x) :=
    fun i => circuit_orthonormal_span hN_pos (Cs i) (hval i).1 (hval i).2.2
  choose m e coeff hm_pos hm_le horth hspan using hbasis
  let H : Fin N → Fin N → ℝ := fun x y => hBit (2 * s) x.val y.val
  let K : Fin l → Fin N → Fin N → ℝ := fun i x y => b2r ((Cs i).eval (oneEach x y))
  let PH : Fin l → Fin N → Fin N → ℝ := fun i x y =>
    ∑ a : Fin (m i), (∑ z : Fin N, e i a z * H z y) * e i a x
  have hH_ortho : ∀ x x' : Fin N, ∑ y : Fin N, H x y * H x' y = if x = x' then (N : ℝ) else 0 := by
    intro x x'
    have h0 := hBit_ortho (2 * s) x x'
    simpa [H, N] using h0
  have hPH_norm : ∀ i : Fin l,
      ∑ x : Fin N, ∑ y : Fin N, (PH i x y) ^ 2 = (N : ℝ) * (m i : ℝ) := by
    intro i
    have h1 : ∀ y : Fin N, ∑ x : Fin N, (PH i x y) ^ 2 =
        ∑ a : Fin (m i), (∑ z : Fin N, e i a z * H z y) ^ 2 := by
      intro y
      let c : Fin (m i) → ℝ := fun a => ∑ z : Fin N, e i a z * H z y
      have h1a : ∑ x : Fin N, (PH i x y) ^ 2 =
          ∑ a : Fin (m i), ∑ b : Fin (m i),
            (c a * c b) * (∑ x : Fin N, e i a x * e i b x) := by
        have hPHc : ∀ x : Fin N, PH i x y = ∑ a : Fin (m i), c a * e i a x := fun _ => rfl
        simp only [hPHc, sq, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [h1a]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [horth i a, sq, c]
    rw [Finset.sum_comm]
    simp only [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ a : Fin (m i), ∑ y : Fin N, (∑ z : Fin N, e i a z * H z y) ^ 2 = (N : ℝ) := by
      intro a
      have h2a : ∑ y : Fin N, (∑ z : Fin N, e i a z * H z y) ^ 2 =
          ∑ z : Fin N, ∑ z' : Fin N, (e i a z * e i a z') * (∑ y : Fin N, H z y * H z' y) := by
        simp only [sq, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by ring
      rw [h2a]
      simp only [hH_ortho, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← Finset.sum_mul, horth i a a]
      simp
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hKH_eq : ∀ i : Fin l,
      ∑ x : Fin N, ∑ y : Fin N, K i x y * PH i x y =
        ∑ x : Fin N, ∑ y : Fin N, K i x y * H x y := by
    intro i
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hL : ∑ x : Fin N, K i x y * PH i x y =
        ∑ a : Fin (m i), coeff i a y * (∑ z : Fin N, e i a z * H z y) := by
      have hL1 : ∑ x : Fin N, K i x y * PH i x y =
          ∑ a : Fin (m i), ∑ b : Fin (m i),
            (coeff i a y * (∑ z : Fin N, e i b z * H z y)) * (∑ x : Fin N, e i a x * e i b x) := by
        dsimp only [K, PH]
        simp only [hspan i, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [hL1]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [horth i a]
    have hR : ∑ x : Fin N, K i x y * H x y =
        ∑ a : Fin (m i), coeff i a y * (∑ z : Fin N, e i a z * H z y) := by
      dsimp only [K]
      simp only [hspan i, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [hL, hR]
  let D : Fin l → ℝ := fun i =>
    ∑ x : Fin N, ∑ y : Fin N, (K i x y - (h : ℝ) * PH i x y) ^ 2
  have hD_nonneg : ∀ i, 0 ≤ D i := fun i =>
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hD_expand : ∀ i : Fin l,
      D i = (N : ℝ) ^ 2 - 2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, K i x y * H x y) +
        (h : ℝ) ^ 2 * ((N : ℝ) * (m i : ℝ)) := by
    intro i
    have hK2 : ∑ x : Fin N, ∑ y : Fin N, (K i x y) ^ 2 = (N : ℝ) ^ 2 := by
      have h1 : ∀ x y : Fin N, (K i x y) ^ 2 = 1 := fun x y => by
        rw [sq]; exact b2r_mul_self _
      simp [h1, sq]
    calc D i
        = ∑ x : Fin N, ∑ y : Fin N,
            ((K i x y) ^ 2 - 2 * (h : ℝ) * (K i x y * PH i x y) +
              (h : ℝ) ^ 2 * (PH i x y) ^ 2) := by
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
      _ = (∑ x : Fin N, ∑ y : Fin N, (K i x y) ^ 2) -
            2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, K i x y * PH i x y) +
            (h : ℝ) ^ 2 * (∑ x : Fin N, ∑ y : Fin N, (PH i x y) ^ 2) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = (N : ℝ) ^ 2 - 2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, K i x y * H x y) +
            (h : ℝ) ^ 2 * ((N : ℝ) * (m i : ℝ)) := by
            rw [hK2, hKH_eq i, hPH_norm i]
  have hKH_le : ∀ i : Fin l,
      2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, K i x y * H x y) + D i ≤ 2 * (N : ℝ) ^ 2 := by
    intro i
    have hm_r : (m i : ℝ) ≤ (2 ^ (2 * t) : ℝ) := by exact_mod_cast hm_le i
    have hterm : (h : ℝ) ^ 2 * ((N : ℝ) * (m i : ℝ)) ≤ (N : ℝ) ^ 2 := by
      calc (h : ℝ) ^ 2 * ((N : ℝ) * (m i : ℝ))
          ≤ (h : ℝ) ^ 2 * ((N : ℝ) * (2 ^ (2 * t) : ℝ)) := by
            gcongr
        _ = (N : ℝ) * ((h : ℝ) ^ 2 * (2 ^ (2 * t) : ℝ)) := by ring
        _ = (N : ℝ) * (N : ℝ) := by rw [hNh]
        _ = (N : ℝ) ^ 2 := by ring
    linarith [hD_expand i]
  have hp_real : ∀ i, (0 : ℝ) ≤ (p i : ℝ) := fun i => by exact_mod_cast hp i
  have hsum_real : ∑ i : Fin l, (p i : ℝ) = 1 := by exact_mod_cast hsum
  have hcell : ∀ x y : Fin N,
      (∑ i : Fin l, (p i : ℝ) * (K i x y * H x y)) =
        2 * (success x y : ℝ) - 1 := by
    intro x y
    have h1 : (success x y : ℝ) =
        ∑ i : Fin l, if (Cs i).eval (oneEach x y) = dotBit (2 * s) x.val y.val
          then (p i : ℝ) else 0 := by
      simp only [success, Rat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    rw [h1, Finset.mul_sum]
    have h2 : ∑ i : Fin l, (p i : ℝ) * (K i x y * H x y) =
        ∑ i : Fin l, ((if (Cs i).eval (oneEach x y) = dotBit (2 * s) x.val y.val
          then 2 * (p i : ℝ) else 0) - (p i : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [K, H, hBit]
      rw [b2r_inj_neg]
      split_ifs <;> ring
    rw [h2, Finset.sum_sub_distrib, hsum_real]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have havg : 2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, (2 * (success x y : ℝ) - 1)) +
      ∑ i : Fin l, (p i : ℝ) * D i ≤ 2 * (N : ℝ) ^ 2 := by
    have hswap : ∑ x : Fin N, ∑ y : Fin N, (2 * (success x y : ℝ) - 1) =
        ∑ i : Fin l, (p i : ℝ) * (∑ x : Fin N, ∑ y : Fin N, K i x y * H x y) := by
      simp only [← hcell]
      rw [Finset.sum_comm]
      conv_lhs => enter [2, y]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
    rw [hswap, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc ∑ i : Fin l,
            (2 * (h : ℝ) * ((p i : ℝ) * ∑ x : Fin N, ∑ y : Fin N, K i x y * H x y) +
              (p i : ℝ) * D i)
        = ∑ i : Fin l, (p i : ℝ) *
            (2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, K i x y * H x y) + D i) := by
          refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i : Fin l, (p i : ℝ) * (2 * (N : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hKH_le i) (hp_real i)
      _ = 2 * (N : ℝ) ^ 2 := by rw [← Finset.sum_mul, hsum_real, one_mul]
  constructor
  · by_contra hall
    push Not at hall
    have hgt : ∀ x y : Fin N, (1 : ℝ) < (h : ℝ) * (2 * (success x y : ℝ) - 1) := by
      intro x y
      have hq : ((h : ℚ) + 1 : ℝ) < (2 * (h : ℚ) * success x y : ℝ) := by
        exact_mod_cast hall x y
      push_cast at hq
      linarith
    have hsum_gt : (N : ℝ) ^ 2 <
        ∑ x : Fin N, ∑ y : Fin N, (h : ℝ) * (2 * (success x y : ℝ) - 1) := by
      have hN2 : (N : ℝ) ^ 2 = ∑ _x : Fin N, ∑ _y : Fin N, (1 : ℝ) := by simp [sq]
      rw [hN2]
      refine Finset.sum_lt_sum (fun x _ => Finset.sum_le_sum fun y _ => le_of_lt (hgt x y)) ?_
      exact ⟨⟨0, hN_pos⟩, Finset.mem_univ _,
        Finset.sum_lt_sum (fun y _ => le_of_lt (hgt ⟨0, hN_pos⟩ y))
          ⟨⟨0, hN_pos⟩, Finset.mem_univ _, hgt ⟨0, hN_pos⟩ ⟨0, hN_pos⟩⟩⟩
    have hDsum : 0 ≤ ∑ i : Fin l, (p i : ℝ) * D i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hp_real i) (hD_nonneg i)
    have hsum_gt2 : 2 * (N : ℝ) ^ 2 <
        2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, (2 * (success x y : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum]
      have h3 : ∑ x : Fin N, ∑ y : Fin N, 2 * (h : ℝ) * (2 * (success x y : ℝ) - 1) =
          2 * ∑ x : Fin N, ∑ y : Fin N, (h : ℝ) * (2 * (success x y : ℝ) - 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by ring
      rw [h3]
      linarith
    linarith
  · intro hall
    have hge : ∀ x y : Fin N, (1 : ℝ) ≤ (h : ℝ) * (2 * (success x y : ℝ) - 1) := by
      intro x y
      have hq : ((h : ℚ) + 1 : ℝ) ≤ (2 * (h : ℚ) * success x y : ℝ) := by
        exact_mod_cast hall x y
      push_cast at hq
      linarith
    have hsum_ge : 2 * (N : ℝ) ^ 2 ≤
        2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, (2 * (success x y : ℝ) - 1)) := by
      have hN2 : 2 * (N : ℝ) ^ 2 = ∑ _x : Fin N, ∑ _y : Fin N, (2 : ℝ) := by simp [sq]; ring
      rw [hN2, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      linarith [hge x y]
    have hDsum_nonneg : 0 ≤ ∑ i : Fin l, (p i : ℝ) * D i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hp_real i) (hD_nonneg i)
    have hDsum_zero : ∑ i : Fin l, (p i : ℝ) * D i = 0 := by linarith
    have hsum_eq : 2 * (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, (2 * (success x y : ℝ) - 1)) =
        2 * (N : ℝ) ^ 2 := by linarith
    have hcell_eq : ∀ x y : Fin N, (h : ℝ) * (2 * (success x y : ℝ) - 1) = 1 := by
      have hdiff0 : ∑ x : Fin N, ∑ y : Fin N, ((h : ℝ) * (2 * (success x y : ℝ) - 1) - 1) = 0 := by
        have hrow : ∀ x : Fin N,
            ∑ y : Fin N, ((h : ℝ) * (2 * (success x y : ℝ) - 1) - 1) =
              (h : ℝ) * (∑ y : Fin N, (2 * (success x y : ℝ) - 1)) - (N : ℝ) := by
          intro x
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp
        have htot : ∑ x : Fin N, ∑ y : Fin N, ((h : ℝ) * (2 * (success x y : ℝ) - 1) - 1) =
            (h : ℝ) * (∑ x : Fin N, ∑ y : Fin N, (2 * (success x y : ℝ) - 1)) - (N : ℝ) ^ 2 := by
          simp only [hrow]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp [sq]
        rw [htot]
        linarith [hsum_eq]
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Finset.sum_nonneg fun y _ => by linarith [hge x y])] at hdiff0
      intro x y
      have hx := hdiff0 x (Finset.mem_univ x)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun y' _ => by linarith [hge x y'])] at hx
      linarith [hx y (Finset.mem_univ y)]
    have hDi_zero : ∀ i : Fin l, (p i : ℝ) * D i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hp_real j) (hD_nonneg j))).mp
        hDsum_zero i (Finset.mem_univ i)
    have hKi_eq : ∀ (i : Fin l) (x y : Fin N),
        (p i : ℝ) * K i x y = (p i : ℝ) * ((h : ℝ) * PH i x y) := by
      intro i x y
      rcases mul_eq_zero.mp (hDi_zero i) with hp0 | hD0
      · simp [hp0]
      · have hsq0 : (K i x y - (h : ℝ) * PH i x y) ^ 2 = 0 := by
          have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x' _ =>
            Finset.sum_nonneg fun y' _ => sq_nonneg _)).mp hD0 x (Finset.mem_univ x)
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun y' _ => sq_nonneg _)).mp hx y (Finset.mem_univ y)
        have heq : K i x y = (h : ℝ) * PH i x y := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
        rw [heq]
    have hmat_eq : ∀ x y : Fin N,
        ∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) * PH i x y = H x y := by
      intro x y
      have h1 : (h : ℝ) * (∑ i : Fin l, (p i : ℝ) * K i x y) * H x y = 1 := by
        have hc := hcell_eq x y
        rw [← hcell x y] at hc
        calc (h : ℝ) * (∑ i : Fin l, (p i : ℝ) * K i x y) * H x y
            = (h : ℝ) * ((∑ i : Fin l, (p i : ℝ) * K i x y) * H x y) := by ring
          _ = (h : ℝ) * (∑ i : Fin l, (p i : ℝ) * (K i x y * H x y)) := by
              congr 1
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => by ring
          _ = 1 := hc
      have h2 : (h : ℝ) * (∑ i : Fin l, (p i : ℝ) * K i x y) = H x y := by
        have hH2 : H x y * H x y = 1 := b2r_mul_self _
        calc (h : ℝ) * (∑ i : Fin l, (p i : ℝ) * K i x y)
            = ((h : ℝ) * (∑ i : Fin l, (p i : ℝ) * K i x y) * H x y) * H x y := by
              rw [mul_assoc, hH2, mul_one]
          _ = 1 * H x y := by rw [h1]
          _ = H x y := one_mul _
      rw [← h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hKi_eq i x y]
      ring
    have hparseval : ∀ u : Fin N → ℝ,
        ∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) *
          (∑ a : Fin (m i), (∑ x : Fin N, u x * e i a x) ^ 2) =
        ∑ x : Fin N, u x * u x := by
      intro u
      let v : Fin N → ℝ := fun y => ∑ z : Fin N, H z y * u z
      have hHv : ∀ x : Fin N, ∑ y : Fin N, H x y * v y = (N : ℝ) * u x := by
        intro x
        simp only [v, Finset.mul_sum]
        rw [Finset.sum_comm]
        have h1 : ∀ z : Fin N, ∑ y : Fin N, H x y * (H z y * u z) =
            (if x = z then (N : ℝ) else 0) * u z := by
          intro z
          rw [← hH_ortho x z, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => by ring
        simp [h1]
      have hPHv : ∀ (i : Fin l) (x : Fin N),
          ∑ y : Fin N, PH i x y * v y =
            (N : ℝ) * ∑ a : Fin (m i), (∑ z : Fin N, u z * e i a z) * e i a x := by
        intro i x
        have hstep : ∑ y : Fin N, PH i x y * v y =
            ∑ a : Fin (m i), (∑ z : Fin N, e i a z * (∑ y : Fin N, H z y * v y)) * e i a x := by
          dsimp only [PH]
          trans ∑ y : Fin N, ∑ a : Fin (m i), (∑ z : Fin N, e i a z * H z y) * e i a x * v y
          · refine Finset.sum_congr rfl fun y _ => Finset.sum_mul _ _ _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          trans ∑ y : Fin N, ∑ z : Fin N, e i a z * H z y * e i a x * v y
          · refine Finset.sum_congr rfl fun y _ => by rw [Finset.sum_mul, Finset.sum_mul]
          rw [Finset.sum_comm, Finset.sum_mul]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y _ => by ring
        rw [hstep, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [hHv]
        rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by ring
      have hvec : ∀ x : Fin N,
          ∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) *
            (∑ a : Fin (m i), (∑ z : Fin N, u z * e i a z) * e i a x) = u x := by
        intro x
        have h1 : ∑ y : Fin N, (∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) * PH i x y) * v y =
            ∑ y : Fin N, H x y * v y := by
          refine Finset.sum_congr rfl fun y _ => by rw [hmat_eq x y]
        rw [hHv x] at h1
        have h2 : ∑ y : Fin N, (∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) * PH i x y) * v y =
            (N : ℝ) * ∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) *
              (∑ a : Fin (m i), (∑ z : Fin N, u z * e i a z) * e i a x) := by
          trans ∑ y : Fin N, ∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) * (PH i x y * v y)
          · refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, hPHv i x]
          ring
        rw [h2] at h1
        exact mul_left_cancel₀ (ne_of_gt hN_real) h1
      have hre : ∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) *
            (∑ a : Fin (m i), (∑ x : Fin N, u x * e i a x) ^ 2) =
          ∑ x : Fin N, u x * (∑ i : Fin l, ((h : ℝ) ^ 2 * (p i : ℝ)) *
            (∑ a : Fin (m i), (∑ z : Fin N, u z * e i a z) * e i a x)) := by
        have hinner : ∀ i : Fin l,
            ((h : ℝ) ^ 2 * (p i : ℝ)) * (∑ a : Fin (m i), (∑ x : Fin N, u x * e i a x) ^ 2) =
            ∑ x : Fin N, u x * (((h : ℝ) ^ 2 * (p i : ℝ)) *
              (∑ a : Fin (m i), (∑ z : Fin N, u z * e i a z) * e i a x)) := by
          intro i
          rw [Finset.mul_sum]
          trans ∑ a : Fin (m i), ∑ x : Fin N,
              u x * (((h : ℝ) ^ 2 * (p i : ℝ)) * ((∑ z : Fin N, u z * e i a z) * e i a x))
          · refine Finset.sum_congr rfl fun a _ => ?_
            rw [show (∑ x : Fin N, u x * e i a x) ^ 2 =
                  (∑ z : Fin N, u z * e i a z) * (∑ x : Fin N, u x * e i a x) from sq _,
              ← mul_assoc, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
        simp only [hinner]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
      rw [hre]
      refine Finset.sum_congr rfl fun x _ => by rw [hvec x]
    have hlib := PEqualNP.Outside.L_lib_567 N l m e (fun i => (h : ℝ) ^ 2 * (p i : ℝ))
      hm_pos (fun i => mul_nonneg (sq_nonneg _) (hp_real i)) horth hparseval
    intro i
    have hr : ((h : ℚ) ^ 2 * p i : ℝ) ≤ (1 : ℝ) := by
      push_cast
      exact hlib.1 i
    exact_mod_cast hr

def bent (r : ℕ) (w : ℕ) : Bool := dotBit r w (w >>> r)

def rowCorr (r : ℕ) (z u : ℕ) : Bool := xor (bent r u) (dotBit (2 * r) u z)

def colShift (r : ℕ) (z v : ℕ) : Bool := bent r (v ^^^ z)

lemma bent_walsh (r : ℕ) (u : Fin (2 ^ (2 * r))) :
    ∑ w : Fin (2 ^ (2 * r)), b2r (bent r w.val) * hBit (2 * r) u.val w.val =
      (2 ^ r : ℝ) * b2r (bent r u.val) := by
  have h2r : 2 ^ (2 * r) = 2 ^ r * 2 ^ r := by rw [← pow_add, two_mul]
  let eqv : Fin (2 ^ r) × Fin (2 ^ r) ≃ Fin (2 ^ (2 * r)) :=
    (finProdFinEquiv (m := 2 ^ r) (n := 2 ^ r)).trans (finCongr h2r.symm)
  rw [← Equiv.sum_comp eqv]
  rw [Fintype.sum_prod_type]
  have hval : ∀ (p : Fin (2 ^ r) × Fin (2 ^ r)),
      (eqv p).val = p.2.val + 2 ^ r * p.1.val := by
    intro p
    simp [eqv, finProdFinEquiv, mul_comm]
  have hterm : ∀ (w2 w1 : Fin (2 ^ r)),
      b2r (bent r (eqv (w2, w1)).val) * hBit (2 * r) u.val (eqv (w2, w1)).val =
        (hBit r w1.val w2.val * hBit r (u.val >>> r) w2.val) * hBit r u.val w1.val := by
    intro w2 w1
    have hv : (eqv (w2, w1)).val = w1.val + 2 ^ r * w2.val := hval (w2, w1)
    have hshift : (eqv (w2, w1)).val >>> r = w2.val := by
      rw [hv, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt w1.isLt, zero_add]
    have hmod : (eqv (w2, w1)).val % 2 ^ r = w1.val := by
      rw [hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt w1.isLt]
    have hbent : b2r (bent r (eqv (w2, w1)).val) = hBit r w1.val w2.val := by
      unfold bent
      change hBit r (eqv (w2, w1)).val ((eqv (w2, w1)).val >>> r) = _
      rw [hshift, ← hBit_mod_left r, hmod]
    have hH : hBit (2 * r) u.val (eqv (w2, w1)).val =
        hBit r u.val w1.val * hBit r (u.val >>> r) w2.val := by
      have hsp := hBit_split r r u.val (eqv (w2, w1)).val
      rw [← two_mul] at hsp
      rw [hsp, hshift, ← hBit_mod_right r u.val, hmod]
    rw [hbent, hH]
    ring
  simp only [hterm]
  rw [Finset.sum_comm]
  have hu_hi : u.val >>> r < 2 ^ r := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    calc u.val < 2 ^ (2 * r) := u.isLt
      _ = 2 ^ r * 2 ^ r := h2r
  let u2 : Fin (2 ^ r) := ⟨u.val >>> r, hu_hi⟩
  have hinner : ∀ w1 : Fin (2 ^ r),
      ∑ w2 : Fin (2 ^ r), (hBit r w1.val w2.val * hBit r (u.val >>> r) w2.val) * hBit r u.val w1.val =
        (if w1 = u2 then (2 ^ r : ℝ) else 0) * hBit r u.val w1.val := by
    intro w1
    rw [← Finset.sum_mul, ← hBit_ortho r w1 u2]
  simp only [hinner, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold bent hBit
  rfl

lemma bent_agree_count (r : ℕ) (u v : Fin (2 ^ (2 * r))) :
    2 * (2 ^ r) * ((Finset.univ : Finset (Fin (2 ^ (2 * r)))).filter
      (fun z => xor (rowCorr r z.val u.val) (colShift r z.val v.val) = dotBit (2 * r) u.val v.val)).card =
      (2 ^ r + 1) * (2 ^ r) ^ 2 := by
  let S := (Finset.univ : Finset (Fin (2 ^ (2 * r)))).filter
    (fun z => xor (rowCorr r z.val u.val) (colShift r z.val v.val) = dotBit (2 * r) u.val v.val)
  let eqv : Fin (2 ^ (2 * r)) ≃ Fin (2 ^ (2 * r)) :=
    { toFun := fun z => ⟨v.val ^^^ z.val, Nat.xor_lt_two_pow v.isLt z.isLt⟩
      invFun := fun z => ⟨v.val ^^^ z.val, Nat.xor_lt_two_pow v.isLt z.isLt⟩
      left_inv := fun z => Fin.ext (by simp)
      right_inv := fun z => Fin.ext (by simp) }
  have hsum : ∑ z : Fin (2 ^ (2 * r)),
      b2r (xor (rowCorr r z.val u.val) (colShift r z.val v.val)) * hBit (2 * r) u.val v.val =
      (2 ^ r : ℝ) := by
    have h1 : ∀ z : Fin (2 ^ (2 * r)),
        b2r (xor (rowCorr r z.val u.val) (colShift r z.val v.val)) * hBit (2 * r) u.val v.val =
          b2r (bent r u.val) * (b2r (bent r (eqv z).val) * hBit (2 * r) u.val (eqv z).val) := by
      intro z
      unfold rowCorr colShift
      rw [b2r_xor, b2r_xor]
      change (b2r (bent r u.val) * hBit (2 * r) u.val z.val) *
        b2r (bent r (v.val ^^^ z.val)) * hBit (2 * r) u.val v.val = _
      have hxv : hBit (2 * r) u.val (eqv z).val =
          hBit (2 * r) u.val v.val * hBit (2 * r) u.val z.val := hBit_xor_right (2 * r) u.val v.val z.val
      rw [hxv]
      change _ = b2r (bent r u.val) * (b2r (bent r (v.val ^^^ z.val)) *
        (hBit (2 * r) u.val v.val * hBit (2 * r) u.val z.val))
      ring
    simp only [h1, ← Finset.mul_sum]
    rw [Equiv.sum_comp eqv (fun w => b2r (bent r w.val) * hBit (2 * r) u.val w.val),
      bent_walsh r u]
    calc b2r (bent r u.val) * ((2 ^ r : ℝ) * b2r (bent r u.val))
        = (2 ^ r : ℝ) * (b2r (bent r u.val) * b2r (bent r u.val)) := by ring
      _ = (2 ^ r : ℝ) * 1 := by rw [b2r_mul_self]
      _ = (2 ^ r : ℝ) := mul_one _
  have hsum2 : ∑ z : Fin (2 ^ (2 * r)),
      b2r (xor (rowCorr r z.val u.val) (colShift r z.val v.val)) * hBit (2 * r) u.val v.val =
      2 * (S.card : ℝ) - (2 ^ (2 * r) : ℝ) := by
    have h2 : ∀ z : Fin (2 ^ (2 * r)),
        b2r (xor (rowCorr r z.val u.val) (colShift r z.val v.val)) * hBit (2 * r) u.val v.val =
          2 * (if z ∈ S then (1 : ℝ) else 0) - 1 := by
      intro z
      dsimp only [S, hBit]
      rw [b2r_inj_neg]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    push_cast
    rfl
  have h2r : (2 ^ (2 * r) : ℝ) = ((2 ^ r : ℝ) ^ 2) := by
    rw [← pow_mul, mul_comm]
  have hEqR : (2 * (2 ^ r) * S.card : ℝ) = ((2 ^ r + 1) * (2 ^ r) ^ 2 : ℝ) := by
    have h3 : 2 * (S.card : ℝ) = (2 ^ r : ℝ) + (2 ^ r : ℝ) ^ 2 := by linarith [hsum, hsum2, h2r]
    calc (2 * (2 ^ r) * S.card : ℝ) = (2 ^ r : ℝ) * (2 * (S.card : ℝ)) := by ring
      _ = (2 ^ r : ℝ) * ((2 ^ r : ℝ) + (2 ^ r : ℝ) ^ 2) := by rw [h3]
      _ = ((2 ^ r + 1) * (2 ^ r) ^ 2 : ℝ) := by ring
  exact_mod_cast hEqR

def pairSelf : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, x => xor (pairSelf k x) (x.testBit (2 * k) && x.testBit (2 * k + 1))

def pairCross : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | k + 1, x, y =>
    xor (pairCross k x y)
      (xor (x.testBit (2 * k)) (y.testBit (2 * k + 1)) &&
       xor (x.testBit (2 * k + 1)) (y.testBit (2 * k)))

lemma bool_pair_step (a0 a1 b0 b1 pL pR pC : Bool) :
    xor (xor (xor pL (a0 && a1)) (xor pR (b0 && b1)))
        (xor pC (xor a0 b1 && xor a1 b0)) =
      xor (xor (xor (xor pL pR) pC) (a0 && b0)) (a1 && b1) := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases pL <;> cases pR <;> cases pC <;> decide

lemma pair_identity (t x y : ℕ) :
    xor (xor (pairSelf t x) (pairSelf t y)) (pairCross t x y) = dotBit (2 * t) x y := by
  induction t with
  | zero =>
    unfold pairSelf pairCross dotBit
    simp
  | succ k ih =>
    unfold pairSelf pairCross
    rw [bool_pair_step, ih]
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1, dotBit_succ, dotBit_succ]

structure BState (W : ℕ) where
  gates : List Gate
  hlen : ∀ g ∈ gates, g.inputs.length ≤ 2
  hrb : ∀ j (hj : j < gates.length), ∀ i ∈ (gates[j]).inputs, i < W + j

lemma BState_readsBack {W : ℕ} (st : BState W) (out : ℕ) :
    ReadsBack W ⟨st.gates, out⟩ := by
  intro j hj i hi
  have hga : gateAt ⟨st.gates, out⟩ j = st.gates[j] := by
    unfold gateAt
    exact List.getD_eq_getElem st.gates _ hj
  rw [hga] at hi
  exact st.hrb j hj i hi

def pushGate {W : ℕ} (st : BState W) (g : Gate)
    (hg : g.inputs.length ≤ 2)
    (hgrb : ∀ i ∈ g.inputs, i < W + st.gates.length) : BState W :=
  { gates := st.gates ++ [g]
    hlen := fun g' hg' => by
      rcases List.mem_append.mp hg' with h1 | h2
      · exact st.hlen g' h1
      · rw [List.mem_singleton.mp h2]; exact hg
    hrb := fun j hj i hi => by
      by_cases hlt : j < st.gates.length
      · rw [List.getElem_append_left hlt] at hi
        exact st.hrb j hlt i hi
      · have heq : j = st.gates.length := by
          rw [List.length_append, List.length_singleton] at hj
          omega
        subst heq
        rw [List.getElem_append_right (le_refl _)] at hi
        simp only [Nat.sub_self, List.getElem_singleton] at hi
        exact hgrb i hi }

def pushConstFalse {W : ℕ} (st : BState W) : BState W × ℕ :=
  (pushGate st ⟨GateOp.or, []⟩ (by simp) (by simp), W + st.gates.length)

def pushXor {W : ℕ} (st : BState W) (a b : ℕ)
    (ha : a < W + st.gates.length) (hb : b < W + st.gates.length) : BState W × ℕ :=
  let w1 := W + st.gates.length
  let g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  let st1 := pushGate st g1 (by simp [g1]) (by
    intro i hi
    simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption)
  let st2 := pushGate st1 ⟨GateOp.not, [w1]⟩ (by simp) (by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    change W + st.gates.length < W + (st.gates ++ [g1]).length
    simp)
  (st2, w1 + 1)

def pushAnd {W : ℕ} (st : BState W) (a b : ℕ)
    (ha : a < W + st.gates.length) (hb : b < W + st.gates.length) : BState W × ℕ :=
  (pushGate st ⟨GateOp.and, [a, b]⟩ (by simp) (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption), W + st.gates.length)

lemma nlGate_constFalse : nlGate ⟨GateOp.or, []⟩ = false := rfl
lemma nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := rfl
lemma nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := rfl
lemma nlGate_and (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := rfl

lemma eval_not_mod2 (u v : Bool) :
    GateOp.not.eval [(GateOp.mod 2).eval [u, v]] = xor u v := by
  cases u <;> cases v <;> decide

lemma eval_and2 (u v : Bool) :
    GateOp.and.eval [u, v] = (u && v) := by
  cases u <;> cases v <;> decide

lemma pushGate_extends {W : ℕ} (st : BState W) (g : Gate)
    (hg : g.inputs.length ≤ 2) (hgrb : ∀ i ∈ g.inputs, i < W + st.gates.length)
    (x : List Bool) (hx : x.length = W) {k : ℕ} (hk : k < W + st.gates.length) :
    (wiresOf x (pushGate st g hg hgrb).gates).getD k false = (wiresOf x st.gates).getD k false :=
  wiresOf_snoc_getD_lt x st.gates g (by omega)

lemma pushConstFalse_spec {W : ℕ} (st : BState W) :
    st.gates.length ≤ (pushConstFalse st).1.gates.length ∧
    (pushConstFalse st).2 < W + (pushConstFalse st).1.gates.length ∧
    (pushConstFalse st).1.gates.countP nlGate = st.gates.countP nlGate ∧
    (∀ x : List Bool, x.length = W →
      (∀ k < W + st.gates.length,
        (wiresOf x (pushConstFalse st).1.gates).getD k false = (wiresOf x st.gates).getD k false) ∧
      (wiresOf x (pushConstFalse st).1.gates).getD (pushConstFalse st).2 false = false) := by
  dsimp only [pushConstFalse]
  refine ⟨by simp [pushGate], by simp [pushGate],
    by simp [pushGate, List.countP_append, nlGate_constFalse], ?_⟩
  intro x hx
  refine ⟨fun k hk => pushGate_extends st _ _ _ x hx hk, ?_⟩
  have h1 : W + st.gates.length = x.length + st.gates.length := by rw [hx]
  rw [h1]
  change (wiresOf x (st.gates ++ [⟨GateOp.or, []⟩])).getD (x.length + st.gates.length) false = false
  rw [wiresOf_snoc_getD_eq]
  simp [GateOp.eval]

lemma pushXor_spec {W : ℕ} (st : BState W) (a b : ℕ)
    (ha : a < W + st.gates.length) (hb : b < W + st.gates.length) :
    st.gates.length ≤ (pushXor st a b ha hb).1.gates.length ∧
    (pushXor st a b ha hb).2 < W + (pushXor st a b ha hb).1.gates.length ∧
    (pushXor st a b ha hb).1.gates.countP nlGate = st.gates.countP nlGate ∧
    (∀ x : List Bool, x.length = W →
      (∀ k < W + st.gates.length,
        (wiresOf x (pushXor st a b ha hb).1.gates).getD k false = (wiresOf x st.gates).getD k false) ∧
      (wiresOf x (pushXor st a b ha hb).1.gates).getD (pushXor st a b ha hb).2 false =
        xor ((wiresOf x st.gates).getD a false) ((wiresOf x st.gates).getD b false)) := by
  dsimp only [pushXor]
  refine ⟨by simp [pushGate], by simp [pushGate]; omega,
    by simp [pushGate, List.countP_append, nlGate_mod2, nlGate_not], ?_⟩
  intro x hx
  set g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  set g2 : Gate := ⟨GateOp.not, [W + st.gates.length]⟩
  refine ⟨fun k hk => ?_, ?_⟩
  · change (wiresOf x ((st.gates ++ [g1]) ++ [g2])).getD k false = _
    rw [wiresOf_snoc_getD_lt x (st.gates ++ [g1]) g2 (by simp; omega)]
    exact wiresOf_snoc_getD_lt x st.gates g1 (by omega)
  · change (wiresOf x ((st.gates ++ [g1]) ++ [g2])).getD (W + st.gates.length + 1) false = _
    have hlen1 : x.length + (st.gates ++ [g1]).length = W + st.gates.length + 1 := by
      simp [hx]; omega
    rw [← hlen1, wiresOf_snoc_getD_eq]
    simp only [g2, List.map_cons, List.map_nil]
    have hlen0 : x.length + st.gates.length = W + st.gates.length := by rw [hx]
    rw [← hlen0, wiresOf_snoc_getD_eq]
    simp only [g1, List.map_cons, List.map_nil]
    exact eval_not_mod2 _ _

lemma pushAnd_spec {W : ℕ} (st : BState W) (a b : ℕ)
    (ha : a < W + st.gates.length) (hb : b < W + st.gates.length) :
    st.gates.length ≤ (pushAnd st a b ha hb).1.gates.length ∧
    (pushAnd st a b ha hb).2 < W + (pushAnd st a b ha hb).1.gates.length ∧
    (pushAnd st a b ha hb).1.gates.countP nlGate = st.gates.countP nlGate + 1 ∧
    (∀ x : List Bool, x.length = W →
      (∀ k < W + st.gates.length,
        (wiresOf x (pushAnd st a b ha hb).1.gates).getD k false = (wiresOf x st.gates).getD k false) ∧
      (wiresOf x (pushAnd st a b ha hb).1.gates).getD (pushAnd st a b ha hb).2 false =
        ((wiresOf x st.gates).getD a false && (wiresOf x st.gates).getD b false)) := by
  dsimp only [pushAnd]
  refine ⟨by simp [pushGate], by simp [pushGate],
    by simp [pushGate, List.countP_append, nlGate_and], ?_⟩
  intro x hx
  refine ⟨fun k hk => pushGate_extends st _ _ _ x hx hk, ?_⟩
  have h1 : W + st.gates.length = x.length + st.gates.length := by rw [hx]
  rw [h1]
  change (wiresOf x (st.gates ++ [⟨GateOp.and, [a, b]⟩])).getD (x.length + st.gates.length) false = _
  rw [wiresOf_snoc_getD_eq]
  simp only [List.map_cons, List.map_nil]
  exact eval_and2 _ _

lemma pushLeftXor {N : ℕ} (st : BState (N + N)) (acc : ℕ) (hacc : acc < N + N + st.gates.length)
    (gL : Fin N → Bool) (m : ℕ) (hm : m ≤ N) :
    ∃ (st' : BState (N + N)) (acc' : ℕ),
      st.gates.length ≤ st'.gates.length ∧
      acc' < N + N + st'.gates.length ∧
      st'.gates.countP nlGate = st.gates.countP nlGate ∧
      (∀ x y : Fin N,
        (∀ k < N + N + st.gates.length,
          (wiresOf (oneEach x y) st'.gates).getD k false =
            (wiresOf (oneEach x y) st.gates).getD k false) ∧
        (wiresOf (oneEach x y) st'.gates).getD acc' false =
          if x.val < m then xor ((wiresOf (oneEach x y) st.gates).getD acc false) (gL x)
          else (wiresOf (oneEach x y) st.gates).getD acc false) := by
  induction m with
  | zero =>
    refine ⟨st, acc, le_refl _, hacc, rfl, fun x y => ⟨fun _ _ => rfl, by simp⟩⟩
  | succ m ih =>
    obtain ⟨st1, acc1, hlen1, hacc1, hcnt1, hspec1⟩ := ih (by omega)
    by_cases hbit : gL ⟨m, hm⟩ = true
    · have hm_lt : m < N + N + st1.gates.length := by omega
      obtain ⟨hres_len, hres_lt, hres_cnt, hres_eval⟩ := pushXor_spec st1 acc1 m hacc1 hm_lt
      refine ⟨(pushXor st1 acc1 m hacc1 hm_lt).1, (pushXor st1 acc1 m hacc1 hm_lt).2,
        le_trans hlen1 hres_len, hres_lt, by rw [hres_cnt, hcnt1], fun x y => ?_⟩
      have hlen : (oneEach x y).length = N + N := oneEach_length x y
      obtain ⟨hpres1, hval1⟩ := hspec1 x y
      obtain ⟨hpres2, hval2⟩ := hres_eval (oneEach x y) hlen
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [hpres2 k (by omega), hpres1 k hk]
      · rw [hval2]
        have hwirem : (wiresOf (oneEach x y) st1.gates).getD m false = decide (m = x.val) := by
          rw [wiresOf_getD_input _ _ (by rw [hlen]; omega), oneEach_getD_left x y (by omega)]
        rw [hwirem, hval1]
        by_cases hxm : x.val < m
        · have hne : m ≠ x.val := by omega
          have hxm2 : x.val < m + 1 := by omega
          simp [hxm, hxm2, hne]
        · by_cases hxeq : x.val = m
          · have hxm2 : x.val < m + 1 := by omega
            have hfx : gL x = true := by
              have : x = ⟨m, hm⟩ := Fin.ext hxeq
              rw [this]; exact hbit
            simp [hxm, hxm2, hxeq, hfx]
          · have hxm2 : ¬ (x.val < m + 1) := by omega
            have hne : m ≠ x.val := by omega
            simp [hxm, hxm2, hne]
    · refine ⟨st1, acc1, hlen1, hacc1, hcnt1, fun x y => ?_⟩
      obtain ⟨hpres1, hval1⟩ := hspec1 x y
      refine ⟨hpres1, ?_⟩
      rw [hval1]
      by_cases hxm : x.val < m
      · have hxm2 : x.val < m + 1 := by omega
        simp [hxm, hxm2]
      · by_cases hxeq : x.val = m
        · have hxm2 : x.val < m + 1 := by omega
          have hfx : gL x = false := by
            have : x = ⟨m, hm⟩ := Fin.ext hxeq
            rw [this]
            exact Bool.eq_false_iff.mpr hbit
          simp [hxm, hxm2, hfx]
        · have hxm2 : ¬ (x.val < m + 1) := by omega
          simp [hxm, hxm2]

lemma pushRightXor {N : ℕ} (st : BState (N + N)) (acc : ℕ) (hacc : acc < N + N + st.gates.length)
    (gR : Fin N → Bool) (m : ℕ) (hm : m ≤ N) :
    ∃ (st' : BState (N + N)) (acc' : ℕ),
      st.gates.length ≤ st'.gates.length ∧
      acc' < N + N + st'.gates.length ∧
      st'.gates.countP nlGate = st.gates.countP nlGate ∧
      (∀ x y : Fin N,
        (∀ k < N + N + st.gates.length,
          (wiresOf (oneEach x y) st'.gates).getD k false =
            (wiresOf (oneEach x y) st.gates).getD k false) ∧
        (wiresOf (oneEach x y) st'.gates).getD acc' false =
          if y.val < m then xor ((wiresOf (oneEach x y) st.gates).getD acc false) (gR y)
          else (wiresOf (oneEach x y) st.gates).getD acc false) := by
  induction m with
  | zero =>
    refine ⟨st, acc, le_refl _, hacc, rfl, fun x y => ⟨fun _ _ => rfl, by simp⟩⟩
  | succ m ih =>
    obtain ⟨st1, acc1, hlen1, hacc1, hcnt1, hspec1⟩ := ih (by omega)
    by_cases hbit : gR ⟨m, hm⟩ = true
    · have hm_lt : N + m < N + N + st1.gates.length := by omega
      obtain ⟨hres_len, hres_lt, hres_cnt, hres_eval⟩ := pushXor_spec st1 acc1 (N + m) hacc1 hm_lt
      refine ⟨(pushXor st1 acc1 (N + m) hacc1 hm_lt).1, (pushXor st1 acc1 (N + m) hacc1 hm_lt).2,
        le_trans hlen1 hres_len, hres_lt, by rw [hres_cnt, hcnt1], fun x y => ?_⟩
      have hlen : (oneEach x y).length = N + N := oneEach_length x y
      obtain ⟨hpres1, hval1⟩ := hspec1 x y
      obtain ⟨hpres2, hval2⟩ := hres_eval (oneEach x y) hlen
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [hpres2 k (by omega), hpres1 k hk]
      · rw [hval2]
        have hwirem : (wiresOf (oneEach x y) st1.gates).getD (N + m) false = decide (m = y.val) := by
          rw [wiresOf_getD_input _ _ (by rw [hlen]; omega),
            oneEach_getD_right x y (by omega) (by omega)]
          simp [Nat.add_sub_cancel_left]
        rw [hwirem, hval1]
        by_cases hym : y.val < m
        · have hne : m ≠ y.val := by omega
          have hym2 : y.val < m + 1 := by omega
          simp [hym, hym2, hne]
        · by_cases hyeq : y.val = m
          · have hym2 : y.val < m + 1 := by omega
            have hfy : gR y = true := by
              have : y = ⟨m, hm⟩ := Fin.ext hyeq
              rw [this]; exact hbit
            simp [hym, hym2, hyeq, hfy]
          · have hym2 : ¬ (y.val < m + 1) := by omega
            have hne : m ≠ y.val := by omega
            simp [hym, hym2, hne]
    · refine ⟨st1, acc1, hlen1, hacc1, hcnt1, fun x y => ?_⟩
      obtain ⟨hpres1, hval1⟩ := hspec1 x y
      refine ⟨hpres1, ?_⟩
      rw [hval1]
      by_cases hym : y.val < m
      · have hym2 : y.val < m + 1 := by omega
        simp [hym, hym2]
      · by_cases hyeq : y.val = m
        · have hym2 : y.val < m + 1 := by omega
          have hfy : gR y = false := by
            have : y = ⟨m, hm⟩ := Fin.ext hyeq
            rw [this]
            exact Bool.eq_false_iff.mpr hbit
          simp [hym, hym2, hyeq, hfy]
        · have hym2 : ¬ (y.val < m + 1) := by omega
          simp [hym, hym2]

lemma pushLinearComb {N : ℕ} (st : BState (N + N)) (gL gR : Fin N → Bool) :
    ∃ (st' : BState (N + N)) (w : ℕ),
      st.gates.length ≤ st'.gates.length ∧
      w < N + N + st'.gates.length ∧
      st'.gates.countP nlGate = st.gates.countP nlGate ∧
      (∀ x y : Fin N,
        (∀ k < N + N + st.gates.length,
          (wiresOf (oneEach x y) st'.gates).getD k false =
            (wiresOf (oneEach x y) st.gates).getD k false) ∧
        (wiresOf (oneEach x y) st'.gates).getD w false = xor (gL x) (gR y)) := by
  obtain ⟨hc_len, hc_lt, hc_cnt, hc_eval⟩ := pushConstFalse_spec st
  obtain ⟨st1, w1, h1_len, h1_lt, h1_cnt, h1_spec⟩ :=
    pushLeftXor (pushConstFalse st).1 (pushConstFalse st).2 hc_lt gL N (le_refl N)
  obtain ⟨st2, w2, h2_len, h2_lt, h2_cnt, h2_spec⟩ :=
    pushRightXor st1 w1 h1_lt gR N (le_refl N)
  refine ⟨st2, w2, le_trans hc_len (le_trans h1_len h2_len), h2_lt,
    by rw [h2_cnt, h1_cnt, hc_cnt], fun x y => ?_⟩
  have hlen := oneEach_length x y
  obtain ⟨hc_pres, hc_val⟩ := hc_eval (oneEach x y) hlen
  obtain ⟨h1_pres, h1_val⟩ := h1_spec x y
  obtain ⟨h2_pres, h2_val⟩ := h2_spec x y
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [h2_pres k (by omega), h1_pres k (by omega), hc_pres k hk]
  · rw [h2_val]
    simp only [y.isLt, ↓reduceIte]
    rw [h1_val]
    simp only [x.isLt, ↓reduceIte]
    rw [hc_val, Bool.false_xor]

lemma pushPairs {N : ℕ} (st : BState (N + N)) (acc : ℕ) (hacc : acc < N + N + st.gates.length)
    (t : ℕ) :
    ∃ (st' : BState (N + N)) (acc' : ℕ),
      st.gates.length ≤ st'.gates.length ∧
      acc' < N + N + st'.gates.length ∧
      st'.gates.countP nlGate = st.gates.countP nlGate + t ∧
      (∀ x y : Fin N,
        (∀ k < N + N + st.gates.length,
          (wiresOf (oneEach x y) st'.gates).getD k false =
            (wiresOf (oneEach x y) st.gates).getD k false) ∧
        (wiresOf (oneEach x y) st'.gates).getD acc' false =
          xor ((wiresOf (oneEach x y) st.gates).getD acc false) (pairCross t x.val y.val)) := by
  induction t with
  | zero =>
    refine ⟨st, acc, le_refl _, hacc, by omega, fun x y => ⟨fun _ _ => rfl, by simp [pairCross]⟩⟩
  | succ k ih =>
    obtain ⟨st1, acc1, h1_len, h1_lt, h1_cnt, h1_spec⟩ := ih
    obtain ⟨st2, wA, h2_len, h2_lt, h2_cnt, h2_spec⟩ :=
      pushLinearComb st1 (fun x : Fin N => x.val.testBit (2 * k))
        (fun y : Fin N => y.val.testBit (2 * k + 1))
    obtain ⟨st3, wB, h3_len, h3_lt, h3_cnt, h3_spec⟩ :=
      pushLinearComb st2 (fun x : Fin N => x.val.testBit (2 * k + 1))
        (fun y : Fin N => y.val.testBit (2 * k))
    have hwA_lt : wA < N + N + st3.gates.length := by omega
    obtain ⟨hp_len, hp_lt, hp_cnt, hp_eval⟩ := pushAnd_spec st3 wA wB hwA_lt h3_lt
    have hacc1_lt : acc1 < N + N + (pushAnd st3 wA wB hwA_lt h3_lt).1.gates.length := by omega
    obtain ⟨hx_len, hx_lt, hx_cnt, hx_eval⟩ :=
      pushXor_spec (pushAnd st3 wA wB hwA_lt h3_lt).1 acc1
        (pushAnd st3 wA wB hwA_lt h3_lt).2 hacc1_lt hp_lt
    refine ⟨(pushXor (pushAnd st3 wA wB hwA_lt h3_lt).1 acc1
        (pushAnd st3 wA wB hwA_lt h3_lt).2 hacc1_lt hp_lt).1,
      (pushXor (pushAnd st3 wA wB hwA_lt h3_lt).1 acc1
        (pushAnd st3 wA wB hwA_lt h3_lt).2 hacc1_lt hp_lt).2,
      le_trans h1_len (le_trans h2_len (le_trans h3_len (le_trans hp_len hx_len))),
      hx_lt, by omega, fun x y => ?_⟩
    have hlen := oneEach_length x y
    obtain ⟨h1_pres, h1_val⟩ := h1_spec x y
    obtain ⟨h2_pres, h2_val⟩ := h2_spec x y
    obtain ⟨h3_pres, h3_val⟩ := h3_spec x y
    obtain ⟨hp_pres, hp_val⟩ := hp_eval (oneEach x y) hlen
    obtain ⟨hx_pres, hx_val⟩ := hx_eval (oneEach x y) hlen
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hx_pres j (by omega), hp_pres j (by omega), h3_pres j (by omega),
        h2_pres j (by omega), h1_pres j hj]
    · rw [hx_val, hp_pres acc1 (by omega), h3_pres acc1 (by omega), h2_pres acc1 h1_lt,
        h1_val, hp_val, h3_pres wA h2_lt, h2_val, h3_val]
      simp [pairCross]

lemma part2_construct (s t : ℕ) (hts : t ≤ s) :
    let N := 2 ^ (2 * s)
    let h : ℕ := 2 ^ (s - t)
    ∃ Cs : Fin (h ^ 2) → Circuit,
      (∀ z, (∀ g ∈ (Cs z).gates, g.inputs.length ≤ 2) ∧
        ReadsBack (N + N) (Cs z) ∧ (Cs z).gates.countP nlGate ≤ t) ∧
      ∀ x y : Fin N, 2 * h * ((Finset.univ : Finset (Fin (h ^ 2))).filter
        (fun z => (Cs z).eval (oneEach x y) = dotBit (2 * s) x.val y.val)).card = (h + 1) * h ^ 2 := by
  intro N h
  set r := s - t
  have h2s : 2 * s = 2 * t + 2 * r := by omega
  have hh2 : h ^ 2 = 2 ^ (2 * r) := by
    dsimp only [h]
    rw [← pow_mul, mul_comm]
  have hbuild : ∀ z : Fin (h ^ 2), ∃ C : Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (N + N) C ∧
      C.gates.countP nlGate ≤ t ∧
      ∀ x y : Fin N, C.eval (oneEach x y) =
        xor (dotBit (2 * t) x.val y.val)
          (xor (rowCorr r z.val (x.val >>> (2 * t))) (colShift r z.val (y.val >>> (2 * t)))) := by
    intro z
    let st0 : BState (N + N) := ⟨[], by simp, by simp⟩
    obtain ⟨st1, w1, _, h1_lt, h1_cnt, h1_spec⟩ :=
      pushLinearComb st0
        (fun x : Fin N => xor (rowCorr r z.val (x.val >>> (2 * t))) (pairSelf t x.val))
        (fun y : Fin N => xor (colShift r z.val (y.val >>> (2 * t))) (pairSelf t y.val))
    obtain ⟨st2, w2, _, _, h2_cnt, h2_spec⟩ := pushPairs st1 w1 h1_lt t
    refine ⟨⟨st2.gates, w2⟩, st2.hlen, BState_readsBack st2 w2, ?_, ?_⟩
    · have h0 : st0.gates.countP nlGate = 0 := rfl
      dsimp only
      omega
    · intro x y
      change (wiresOf (oneEach x y) st2.gates).getD w2 false = _
      rw [(h2_spec x y).2, (h1_spec x y).2, ← pair_identity t x.val y.val]
      cases rowCorr r z.val (x.val >>> (2 * t)) <;>
        cases colShift r z.val (y.val >>> (2 * t)) <;>
        cases pairSelf t x.val <;>
        cases pairSelf t y.val <;>
        cases pairCross t x.val y.val <;> decide
  choose Cs hCs_len hCs_rb hCs_cnt hCs_eval using hbuild
  refine ⟨Cs, fun z => ⟨hCs_len z, hCs_rb z, hCs_cnt z⟩, ?_⟩
  intro x y
  have hx_hi : x.val >>> (2 * t) < 2 ^ (2 * r) := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    calc x.val < 2 ^ (2 * s) := x.isLt
      _ = 2 ^ (2 * t) * 2 ^ (2 * r) := by rw [h2s, pow_add]
  have hy_hi : y.val >>> (2 * t) < 2 ^ (2 * r) := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    calc y.val < 2 ^ (2 * s) := y.isLt
      _ = 2 ^ (2 * t) * 2 ^ (2 * r) := by rw [h2s, pow_add]
  let u : Fin (2 ^ (2 * r)) := ⟨x.val >>> (2 * t), hx_hi⟩
  let v : Fin (2 ^ (2 * r)) := ⟨y.val >>> (2 * t), hy_hi⟩
  have htarget : dotBit (2 * s) x.val y.val =
      xor (dotBit (2 * t) x.val y.val) (dotBit (2 * r) u.val v.val) := by
    rw [h2s, dotBit_split]
  have hcard : ((Finset.univ : Finset (Fin (h ^ 2))).filter
      (fun z => (Cs z).eval (oneEach x y) = dotBit (2 * s) x.val y.val)).card =
      ((Finset.univ : Finset (Fin (2 ^ (2 * r)))).filter
      (fun z => xor (rowCorr r z.val u.val) (colShift r z.val v.val) = dotBit (2 * r) u.val v.val)).card := by
    refine Finset.card_bij (fun z _ => z.cast hh2) ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [hCs_eval z x y, htarget] at hz
      have hcancel : ∀ c a b : Bool, xor c a = xor c b → a = b := by
        intro c a b; cases c <;> cases a <;> cases b <;> decide
      exact hcancel _ _ _ hz
    · intro z1 _ z2 _ heq
      exact Fin.ext (by simpa using congrArg Fin.val heq)
    · intro z hz
      refine ⟨z.cast hh2.symm, ?_, by ext; simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [hCs_eval, htarget]
      simpa using congrArg (xor (dotBit (2 * t) x.val y.val)) hz
  rw [hcard]
  exact bent_agree_count r u v

end PEqualNP.Outside.L_meta_25728_aux

theorem PEqualNP.Outside.L_meta_25728 :
  (let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  ∀ s t : ℕ, t ≤ s →
    let N := 2^(2*s)
    let h : ℕ := 2^(s-t)
    let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.gates.countP nonlinear ≤ t
    let value := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin N) =>
      C.eval (PEqualNP.Represents.oneEach x y)
    let target := fun (i j : Fin N) =>
      ((Finset.univ : Finset (Fin (2*s))).filter (fun b =>
        i.val.testBit b.val && j.val.testBit b.val)).card % 2 == 1
    (∀ (l : ℕ) (Cs : Fin l → PEqualNP.CircuitLowerBounds.Circuit) (p : Fin l → ℚ),
      (∀ i, valid (Cs i)) → (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
      let success := fun (x y : Fin N) =>
        ∑ i : Fin l, if value (Cs i) x y = target x y then p i else 0
      (∃ x y, 2*(h : ℚ)*success x y ≤ (h : ℚ)+1) ∧
      ((∀ x y, (h : ℚ)+1 ≤ 2*(h : ℚ)*success x y) →
        ∀ i, (h : ℚ)^2 * p i ≤ 1)) ∧
    ∃ Cs : Fin (h^2) → PEqualNP.CircuitLowerBounds.Circuit, (∀ z, valid (Cs z)) ∧
      ∀ x y, 2*h*((Finset.univ : Finset (Fin (h^2))).filter
        (fun z => value (Cs z) x y = target x y)).card = (h+1)*h^2) := by
  dsimp only
  intro s t hts
  exact ⟨PEqualNP.Outside.L_meta_25728_aux.part1_bounds s t hts,
    PEqualNP.Outside.L_meta_25728_aux.part2_construct s t hts⟩
