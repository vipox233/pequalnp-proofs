import PEqualNP.Defs

-- Binary frontier checker and projected bounds adapted from pin
-- 803b95cc911a2d3bbfe288546bd33bd79d945b8b, lean/PEqualNP/Outside/L_meta_49309.lean.
-- Recheck the root on permuted, complemented inputs for the posted table.

namespace PEqualNP.Outside.L_meta_45458_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def fullMask : Nat := 0xffffffffffffffff
abbrev Masked (mask w : Nat) : Prop := w &&& mask = w
def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c
theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl
theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h
theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp
theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]
theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp
theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all
theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all
def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)
theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]
theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]
theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]
theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩
theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]
theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w
theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]
theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne
theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]
def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))
theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _
theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩
theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]
theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h
theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1
def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank
def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b
def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs
def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length
theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)
theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩
theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)
theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2
def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S
theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _
theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega
inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S
theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega
theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1
theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩
theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))
def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w
theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl
def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k
theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]
def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws
theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢
theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha
theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq
def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)
theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]
theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega
theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit
def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws
theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]
def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w
theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]
def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l
def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws
def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed
def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1
def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l
theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]
theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩
def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l
theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩
theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2
theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]
def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits
theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)
theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)
theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩
def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])
def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)
theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)
def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i
theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2
def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi
theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2
theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2
theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]
theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length
def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k
def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0
theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide
theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]
theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]
def rawVars : List Nat :=
  [0x5555555555555555, 0x0f0f0f0f0f0f0f0f, 0x3333333333333333,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]
def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]
theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)
theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)
theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276678376 * 2 ^ 32 + 4209568384)
    (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)
def oriented : Nat := 0x01571777175f177f
def sample (r : Nat) (i : Fin 6) : Bool := (rawVars.getD i.val 0).testBit r
theorem oriented_canon : canon fullMask oriented = oriented := by decide
theorem sample_list (r : Fin 64) : List.ofFn (sample r.val) = rawVars.map (evalBit r.val) := by
  revert r
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sample_truth : ∀ r : Fin 64, target (sample r.val) = oriented.testBit r.val := by
  decide +kernel
theorem table2_from_lowerBin (m : Nat)
    (hlow : LowerBin fullMask rootStock oriented (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      target x) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      target x) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = target x := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = oriented &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let r : Fin 64 := ⟨k, hk⟩
        have h1 := hC (sample k)
        change C.eval (List.ofFn (sample r.val)) = target (sample r.val) at h1
        rw [sample_list r, sample_truth r] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = oriented.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) oriented := by
      rw [← oriented_canon, ← canon_land fullMask oriented, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l
theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]
def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l
theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]
def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i
theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl
def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1
theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]
def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)
theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)
theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl
def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws
theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl
def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l
theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl
def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop
theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl
def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits
theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl
def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)
theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl
def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i
theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl
def nthBound (bounds : List (Nat × List Nat × Nat × Nat)) (i : Nat) :
    Option (Nat × List Nat × Nat × Nat) :=
  (List.rec (motive := fun _ => Nat → Option (Nat × List Nat × Nat × Nat))
    (fun _ => none)
    (fun b _ ih k => Nat.rec (some b) (fun m _ => ih m) k) bounds) i
theorem nthBound_mem {bounds : List (Nat × List Nat × Nat × Nat)} {i : Nat} {b : Nat × List Nat × Nat × Nat}
    (h : nthBound bounds i = some b) : b ∈ bounds := by
  induction bounds generalizing i with
  | nil => simp [nthBound] at h
  | cons x xs ih =>
    cases i with
    | zero => cases h; exact List.mem_cons_self
    | succ m => exact List.mem_cons_of_mem _ (ih h)
def forceWP {α : Type} (w : Nat) (k : Nat → α) : α :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem forceWP_eq {α : Type} (w : Nat) (k : Nat → α) : forceWP w k = k w := by
  cases w <;> rfl
def forceCons {α : Type} (l : List Nat) (k : List Nat → α) : α :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem forceCons_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceCons l k = k l := by
  cases l <;> rfl
def forceList {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
  (List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun w _ next k => next (fun rest => k (w :: rest))) ws) k
theorem forceList_eq {α : Type} (ws : List Nat) (k : List Nat → α) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceList ws (fun rest => k (w :: rest)) = _
    rw [ih]
def canonV2 (mask w : Nat) : Nat :=
  forceWP (Nat.land w mask) (fun v =>
    Bool.rec
      (Bool.rec
        (forceWP (Nat.xor mask v) (fun iv => Bool.rec iv v (Nat.blt v iv)))
        0 (Nat.beq v mask))
      0 (Nat.beq v 0))
theorem canonV2_eq (mask w : Nat) : canonV2 mask w = canon mask w := by
  unfold canonV2 canon bsel; dsimp only
  rw [forceWP_eq]
  change Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (forceWP (Nat.xor mask (w &&& mask)) (fun iv => Bool.rec (motive := fun _ => Nat) iv (w &&& mask) (Nat.blt (w &&& mask) iv)))
      0 (Nat.beq (w &&& mask) mask)) 0 (Nat.beq (w &&& mask) 0) = _
  rw [forceWP_eq]
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def HistValid (mask : Nat) (stock : List Nat) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (z, x, y) :: rest =>
    (∃ op < 4, z = binOp mask op x y) ∧
    (x ∈ stock ∨ ∃ a b, (x, a, b) ∈ rest) ∧
    (y ∈ stock ∨ ∃ a b, (y, a, b) ∈ rest) ∧
    HistValid mask stock rest
def WsCovered (stock : List Nat) (hist : List (Nat × Nat × Nat)) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w ∈ stock ∨ ∃ a b, (w, a, b) ∈ hist
theorem getD_mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
theorem childState_valid {mask token : Nat} {stock : List Nat}
    {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (hv : HistValid mask stock st.2.2) (hc : WsCovered stock st.2.2 st.2.1)
    (h : childState mask token st = some ch) :
    HistValid mask stock ch.2.2 ∧ WsCovered stock ch.2.2 ch.2.1 := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at hv hc
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok
      have hab : (token >>> 8) < ((token >>> 4) &&& 15) := by
        cases h1 : Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
        · exfalso; exact hok (Or.inl (Or.inr h1))
        · exact Nat.blt_eq.mp h1
      have hbl : ((token >>> 4) &&& 15) < ws.length := by
        cases h2 : Nat.blt ((token >>> 4) &&& 15) ws.length
        · exfalso; exact hok (Or.inr h2)
        · exact Nat.blt_eq.mp h2
      have hx : ws.getD (token >>> 8) 0 ∈ ws := getD_mem_of_lt (by omega)
      have hy : ws.getD ((token >>> 4) &&& 15) 0 ∈ ws := getD_mem_of_lt hbl
      have hop : ((token >>> 2) &&& 3) < 4 := by
        have := Nat.and_lt_two_pow (token >>> 2) (n := 2) (by omega : 3 < 2 ^ 2)
        simpa using this
      refine ⟨⟨⟨(token >>> 2) &&& 3, hop, rfl⟩, hc _ hx, hc _ hy, hv⟩, ?_⟩
      intro w hw
      rcases insertSorted_mem.mp hw with rfl | hrest
      · exact Or.inr ⟨_, _, List.mem_cons_self⟩
      · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hrest).1).1
        rcases hc w hwm with hst | ⟨a, b, hmem⟩
        · exact Or.inl hst
        · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ hmem⟩
theorem dagTrace_valid {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) :
    HistValid mask stock st.2.2 ∧ WsCovered stock st.2.2 st.2.1 := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s →
      HistValid mask stock s.2.2 ∧ WsCovered stock s.2.2 s.2.1 from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s
        exact ⟨trivial, fun w hw => Or.inl (subsetWords_subset stock _ w hw)⟩
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p =>
        rw [hp] at h
        have ⟨hv, hc⟩ := ih _ _ hp
        exact childState_valid hv hc h
theorem addUniq_mem {w u : Nat} {l : List Nat} : u ∈ addUniq w l ↔ u = w ∨ u ∈ l := by
  unfold addUniq
  cases h : l.contains w
  · simp [List.mem_cons]
  · simp only [ite_true]
    have hw : w ∈ l := List.contains_iff_mem.mp h
    constructor
    · exact Or.inr
    · rintro (rfl | hu); exact hw; exact hu
theorem recipeStart_mem {cut : Nat} {stock ws : List Nat} {u : Nat} :
    u ∈ recipeStart cut stock ws ↔ ∃ w ∈ ws, canon cut w = u ∧ ¬Avail stock u := by
  induction ws with
  | nil => simp [recipeStart]
  | cons w ws ih =>
    change u ∈ (if availB stock (canon cut w) then recipeStart cut stock ws
                else addUniq (canon cut w) (recipeStart cut stock ws)) ↔ _
    cases ha : availB stock (canon cut w)
    · simp only [Bool.false_eq_true, ite_false, addUniq_mem, ih]
      have hna : ¬Avail stock (canon cut w) := fun h => by rw [availB_spec.mpr h] at ha; exact Bool.noConfusion ha
      constructor
      · rintro (rfl | ⟨w', hw', rfl, hnu⟩)
        · exact ⟨w, List.mem_cons_self, rfl, hna⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact Or.inl rfl
        · exact Or.inr ⟨w', hw', rfl, hnu⟩
    · simp only [ite_true, ih]
      have hya : Avail stock (canon cut w) := availB_spec.mp ha
      constructor
      · rintro ⟨w', hw', rfl, hnu⟩; exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd hya hnu
        · exact ⟨w', hw', rfl, hnu⟩
theorem recipeClose_sub {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} {acc : List Nat} :
    ∀ u ∈ acc, u ∈ recipeClose cut stock hist acc := by
  induction hist generalizing acc with
  | nil => intro u hu; exact hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro u hu
    change u ∈ (if acc.contains (canon cut w) then
      let va := canon cut a; let vb := canon cut b
      let acc1 := if availB stock va then acc else addUniq va acc
      let acc2 := if availB stock vb then acc1 else addUniq vb acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist acc)
    split
    · apply ih
      have h1 : u ∈ (if availB stock (canon cut a) then acc else addUniq (canon cut a) acc) := by
        split; exact hu; exact addUniq_mem.mpr (Or.inr hu)
      split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · exact ih u hu
theorem recipeClose_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeClose cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    change (if [].contains (canon cut w) then _ else recipeClose cut stock hist []) = []
    exact ih
theorem recipeClose_mono {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} :
    ∀ {A B : List Nat}, (∀ u ∈ A, u ∈ B) →
      ∀ u ∈ recipeClose cut stock hist A, u ∈ recipeClose cut stock hist B := by
  induction hist with
  | nil => intro A B hAB u hu; exact hAB u hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro A B hAB u hu
    change u ∈ (if A.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then A else addUniq (canon cut a) A
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist A) at hu
    change u ∈ (if B.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then B else addUniq (canon cut a) B
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist B)
    cases hA : A.contains (canon cut w)
    · simp only [hA, Bool.false_eq_true, ite_false] at hu
      cases hB : B.contains (canon cut w)
      · simp only [Bool.false_eq_true, ite_false]; exact ih hAB u hu
      · simp only [ite_true]
        apply ih _ u hu
        intro x hx
        have h1 : x ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
          split; exact hAB x hx; exact addUniq_mem.mpr (Or.inr (hAB x hx))
        split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · have hwB : B.contains (canon cut w) = true := List.contains_iff_mem.mpr (hAB _ (List.contains_iff_mem.mp hA))
      simp only [hA, ite_true] at hu
      simp only [hwB, ite_true]
      apply ih _ u hu
      intro x hx
      have h1 : ∀ y, y ∈ (if availB stock (canon cut a) then A else addUniq (canon cut a) A) →
          y ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
        intro y hy
        cases hca : availB stock (canon cut a)
        · simp only [hca, Bool.false_eq_true, ite_false, addUniq_mem] at hy ⊢
          rcases hy with rfl | hy; exact Or.inl rfl; exact Or.inr (hAB y hy)
        · simp only [hca, ite_true] at hy ⊢; exact hAB y hy
      cases hcb : availB stock (canon cut b)
      · simp only [hcb, Bool.false_eq_true, ite_false, addUniq_mem] at hx ⊢
        rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (h1 x hx)
      · simp only [hcb, ite_true] at hx ⊢; exact h1 x hx
noncomputable def buildFrom (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (z, x, y) :: rest =>
    let vs := buildFrom cut bstock S rest
    let v := canon cut z
    let := Classical.propDecidable
    if v ∈ S ∧ ¬Avail (vs ++ bstock) v ∧ Avail (vs ++ bstock) (canon cut x) ∧ Avail (vs ++ bstock) (canon cut y)
    then vs ++ [v] else vs
theorem buildFrom_builds {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      BuildsBin cut bstock (buildFrom cut bstock S hist)
  | [], _ => trivial
  | (z, x, y) :: rest, ⟨⟨op, hop, hz⟩, _, _, hrest⟩ => by
    unfold buildFrom; dsimp only
    have ih := buildFrom_builds (bstock := bstock) (S := S) sub hrest
    split
    · rename_i hcond
      obtain ⟨_, hna, hax, hay⟩ := hcond
      have hgate : GateBin cut (buildFrom cut bstock S rest ++ bstock) (canon cut z) := by
        have hsub := canon_sub_binOp (op := op) (a := x) (b := y) sub
        rw [← hz] at hsub
        rcases hsub with h0 | hx | hy | ⟨op', hop', heq⟩
        · exact absurd (Or.inl h0) hna
        · exact absurd (hx ▸ hax) hna
        · exact absurd (hy ▸ hay) hna
        · exact ⟨canon cut x, canon cut y, op', hop', hax, hay, heq⟩
      exact builds_append ih ⟨hgate, trivial⟩
    · exact ih
theorem buildFrom_nodup_sub (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    ∀ (hist : List (Nat × Nat × Nat)),
      (buildFrom cut bstock S hist).Nodup ∧ ∀ u ∈ buildFrom cut bstock S hist, u ∈ S
  | [] => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | (z, x, y) :: rest => by
    unfold buildFrom; dsimp only
    obtain ⟨hnd, hsub⟩ := buildFrom_nodup_sub cut bstock S rest
    split
    · rename_i hcond
      obtain ⟨hvS, hna, _, _⟩ := hcond
      have hnm : canon cut z ∉ buildFrom cut bstock S rest := fun hm =>
        hna (Or.inr (List.mem_append_left bstock hm))
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun a ha b hb heq => by
        rw [List.mem_singleton.mp hb] at heq; exact hnm (heq ▸ ha)⟩, ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hsub u hu
      · rw [List.mem_singleton.mp hu]; exact hvS
    · exact ⟨hnd, hsub⟩
theorem buildFrom_mono_avail (cut : Nat) (bstock : List Nat) (S : Finset Nat)
    (r : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) {u : Nat}
    (hu : Avail (buildFrom cut bstock S rest ++ bstock) u) :
    Avail (buildFrom cut bstock S (r :: rest) ++ bstock) u := by
  obtain ⟨z, x, y⟩ := r
  unfold buildFrom; dsimp only
  split
  · exact avail_weaken (fun w hw => by simp only [List.mem_append] at hw ⊢; tauto) hu
  · exact hu
theorem buildFrom_covers {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (hstk : ∀ s ∈ stock, Avail bstock (canon cut s)) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      ∀ (acc : List Nat),
        (∀ u ∈ acc, Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u) →
        (∀ u ∈ recipeClose cut bstock hist acc, u ∈ S) →
        ∀ u ∈ acc, Avail (buildFrom cut bstock S hist ++ bstock) u
  | [], _, acc, hcov, _, u, hu => by
    rcases hcov u hu with ha | ⟨_, _, _, hm, _⟩
    · exact avail_weaken (fun w hw => List.mem_append_right _ hw) ha
    · exact nomatch hm
  | (z, x, y) :: rest, ⟨_, hxc, hyc, hrest⟩, acc, hcov, hS, u, hu => by
    cases hcz : acc.contains (canon cut z)
    · have hnz : canon cut z ∉ acc := fun hm => by rw [List.contains_iff_mem.mpr hm] at hcz; exact Bool.noConfusion hcz
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then _ else recipeClose cut bstock rest acc)
        simp only [hcz, Bool.false_eq_true, ite_false]; exact hv
      have hcov' : ∀ v ∈ acc, Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v := by
        intro v hv
        rcases hcov v hv with ha | ⟨z', x', y', hm, heq⟩
        · exact Or.inl ha
        · rcases List.mem_cons.mp hm with hhead | htail
          · rcases Prod.mk.inj hhead with ⟨rfl, _⟩
            exact absurd (heq ▸ hv) hnz
          · exact Or.inr ⟨z', x', y', htail, heq⟩
      exact buildFrom_mono_avail cut bstock S (z, x, y) rest
        (buildFrom_covers hstk hrest acc hcov' hS' u hu)
    · have hzacc : canon cut z ∈ acc := List.contains_iff_mem.mp hcz
      have hzS : canon cut z ∈ S := hS _ (recipeClose_sub _ hzacc)
      set acc1 := if availB bstock (canon cut x) then acc else addUniq (canon cut x) acc
      set acc2 := if availB bstock (canon cut y) then acc1 else addUniq (canon cut y) acc1
      have hS2 : ∀ v ∈ recipeClose cut bstock rest acc2, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then recipeClose cut bstock rest acc2 else _)
        simp only [hcz, ite_true]; exact hv
      let := Classical.propDecidable
      set acc' := acc2.filter (fun v => decide (Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v))
      have hsub' : ∀ v ∈ acc', v ∈ acc2 := fun v hv => (List.mem_filter.mp hv).1
      have hcov' : ∀ v ∈ acc', Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v :=
        fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc', v ∈ S :=
        fun v hv => hS2 v (recipeClose_mono hsub' v hv)
      have hIH := buildFrom_covers hstk hrest acc' hcov' hS'
      have hacc_sub2 : ∀ v ∈ acc, v ∈ acc2 := by
        intro v hv
        have h1 : v ∈ acc1 := by
          unfold acc1; split; exact hv; exact addUniq_mem.mpr (Or.inr hv)
        unfold acc2; split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
      have hax : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut x) := by
        cases hbx : availB bstock (canon cut x)
        · have hx2 : canon cut x ∈ acc2 := by
            have hx1 : canon cut x ∈ acc1 := by
              unfold acc1; simp only [hbx, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
            unfold acc2; split; exact hx1; exact addUniq_mem.mpr (Or.inr hx1)
          have hpx : Avail bstock (canon cut x) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut x := by
            rcases hxc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk x hs)
            · exact Or.inr ⟨x, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hx2, decide_eq_true hpx⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hbx)
      have hay : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut y) := by
        cases hby : availB bstock (canon cut y)
        · have hy2 : canon cut y ∈ acc2 := by
            unfold acc2; simp only [hby, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
          have hpy : Avail bstock (canon cut y) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut y := by
            rcases hyc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk y hs)
            · exact Or.inr ⟨y, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hy2, decide_eq_true hpy⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hby)
      by_cases huz : u = canon cut z
      · subst huz
        unfold buildFrom; dsimp only
        split
        · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
        · rename_i hneg
          by_cases ha : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut z)
          · exact ha
          · exact absurd ⟨hzS, ha, hax, hay⟩ hneg
      · have hpu : Avail bstock u ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = u := by
          rcases hcov u hu with ha | ⟨z', x', y', hm, heq⟩
          · exact Or.inl ha
          · rcases List.mem_cons.mp hm with hhead | htail
            · rcases Prod.mk.inj hhead with ⟨rfl, _⟩; exact absurd heq.symm huz
            · exact Or.inr ⟨z', x', y', htail, heq⟩
        exact buildFrom_mono_avail cut bstock S (z, x, y) rest
          (hIH u (List.mem_filter.mpr ⟨hacc_sub2 u hu, decide_eq_true hpu⟩))
def flatStartF (cut : Nat) (stock ws : List Nat) : Nat × List Nat :=
  List.rec (0, []) (fun w _ ih =>
    match ih with
    | (fl, acc) =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec
          (Bool.rec
            (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
            (fl, acc) (memN v stock))
          (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
          (Nat.beq v 0))) ws
theorem flatStartF_eq (cut : Nat) (stock ws : List Nat) :
    flatStartF cut stock ws = (flatCount cut ws, recipeStart cut stock ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : flatStartF cut stock (w :: ws) =
      match flatStartF cut stock ws with
      | (fl, acc) =>
        forceWP (canonV2 cut w) (fun v =>
          Bool.rec
            (Bool.rec
              (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
              (fl, acc) (memN v stock))
            (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
            (Nat.beq v 0)) := rfl
    rw [hstep, ih]; dsimp only; rw [forceWP_eq, canonV2_eq, forceWP_eq]
    change Bool.rec
        (Bool.rec
          (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
            (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) (recipeStart cut stock ws)))
          (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) stock))
        (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) (Nat.beq (canon cut w) 0) =
      (bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws),
       if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    simp only [memN_eq, availB, addUniq]
    have haux (b1 b2 b3 : Bool) :
        Bool.rec (Bool.rec (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
          (flatCount cut ws, recipeStart cut stock ws) b3)
          (flatCount cut ws, recipeStart cut stock ws) b2)
          (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) b1 =
        (bsel b1 (flatCount cut ws + 1) (flatCount cut ws),
         if (b1 || b2) = true then recipeStart cut stock ws
         else if b3 = true then recipeStart cut stock ws else canon cut w :: recipeStart cut stock ws) := by
      cases b1 <;> cases b2 <;> cases b3 <;> rfl
    exact haux _ _ _
def recipeCloseV2 (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (next acc)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: acc) acc (memN va acc)) acc (memN va stock)) acc (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    next))))
          (memN v acc))) hist needed
theorem recipeCloseV2_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseV2 cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hstep : recipeCloseV2 cut stock ((w, a, b) :: hist) needed =
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (recipeCloseV2 cut stock hist needed)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: needed) needed (memN va needed)) needed (memN va stock)) needed (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    (recipeCloseV2 cut stock hist)))))
          (memN v needed)) := rfl
    rw [hstep]
    simp only [forceWP_eq, forceCons_eq, canonV2_eq, memN_eq]
    change Bool.rec (recipeCloseV2 cut stock hist needed) _ (needed.contains (canon cut w)) =
      (if needed.contains (canon cut w) then
        let va := canon cut a; let vb := canon cut b
        let acc1 := if availB stock va then needed else addUniq va needed
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        recipeClose cut stock hist acc2
      else recipeClose cut stock hist needed)
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only [ite_true]
      rw [ih]
      congr 1
      have hadd (v : Nat) (l : List Nat) :
          Bool.rec (Bool.rec (Bool.rec (v :: l) l (l.contains v)) l (stock.contains v)) l (Nat.beq v 0) =
          if availB stock v then l else addUniq v l := by
        dsimp only [availB, addUniq]
        have haux (b1 b2 b3 : Bool) :
            Bool.rec (Bool.rec (Bool.rec (v :: l) l b3) l b2) l b1 =
            if (b1 || b2) = true then l else if b3 = true then l else v :: l := by
          cases b1 <;> cases b2 <;> cases b3 <;> rfl
        exact haux _ _ _
      rw [hadd (canon cut a) needed, hadd (canon cut b)]
def boundClosesV2 (fuel : Nat) (ws : List Nat) (hist : List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, bstock, lower, _) := bound
  match flatStartF cut bstock ws with
  | (fl, start0) =>
    forceWP (Nat.sub fuel fl) (fun rem =>
      Bool.rec false
        (match start0 with
         | [] => true
         | s0 :: sr =>
           forceList (s0 :: sr) (fun start =>
             Bool.rec false
               (Nat.blt (Nat.add (lenN (recipeCloseV2 cut bstock hist start)) rem) lower)
               (Nat.blt (Nat.add (lenN start) rem) lower)))
        (Nat.blt rem lower))
theorem boundClosesV2_sound {mask goal : Nat} {stock : List Nat}
    {fuel : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (hg : canon bound.1 goal = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0)
    (hstk : ∀ s ∈ stock, Avail bound.2.1 (canon bound.1 s))
    (hv : HistValid mask stock hist) (hc : WsCovered stock hist ws)
    (nd : ws.Nodup) {k : Nat} (hk : k ≤ fuel)
    (hlive : LiveBin mask goal k ws.toFinset) :
    boundClosesV2 fuel ws hist bound = false := by
  obtain ⟨cut, bstock, lower, bgoal⟩ := bound
  dsimp only at hlow sub hg hnz hstk
  apply Bool.eq_false_iff.mpr
  intro hbc
  unfold boundClosesV2 at hbc; dsimp only at hbc
  rw [flatStartF_eq] at hbc; dsimp only at hbc
  simp only [forceWP_eq] at hbc
  cases h1 : Nat.blt (Nat.sub fuel (flatCount cut ws)) lower
  · rw [h1] at hbc; exact Bool.noConfusion hbc
  · rw [h1] at hbc; dsimp only at hbc
    have hlen_lt : (recipeClose cut bstock hist (recipeStart cut bstock ws)).length + (fuel - flatCount cut ws) < lower := by
      cases hs : recipeStart cut bstock ws with
      | nil =>
        rw [recipeClose_nil]; simp only [List.length_nil, Nat.zero_add]
        exact Nat.blt_eq.mp h1
      | cons s0 sr =>
        rw [hs] at hbc; dsimp only at hbc
        simp only [forceList_eq, recipeCloseV2_eq, lenN_eq] at hbc
        cases h2 : Nat.blt (Nat.add (s0 :: sr).length (Nat.sub fuel (flatCount cut ws))) lower
        · rw [h2] at hbc; exact Bool.noConfusion hbc
        · rw [h2] at hbc; dsimp only at hbc
          exact Nat.blt_eq.mp hbc
    set needed := recipeClose cut bstock hist (recipeStart cut bstock ws)
    set S := needed.toFinset
    set vs := buildFrom cut bstock S hist
    have hvbd : BuildsBin cut bstock vs := buildFrom_builds sub hv
    obtain ⟨hvnd, hvsub⟩ := buildFrom_nodup_sub cut bstock S hist
    have hvlen : vs.length ≤ needed.length := by
      rw [← List.toFinset_card_of_nodup hvnd]
      have hsubf : vs.toFinset ⊆ S := fun u hu => hvsub u (List.mem_toFinset.mp hu)
      exact Nat.le_trans (Finset.card_le_card hsubf) (List.toFinset_card_le needed)
    have hcov_start : ∀ u ∈ recipeStart cut bstock ws,
        Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u := by
      intro u hu
      obtain ⟨w, hww, rfl, hna⟩ := recipeStart_mem.mp hu
      rcases hc w hww with hws | ⟨a, b, hmem⟩
      · exact absurd (hstk w hws) hna
      · exact Or.inr ⟨w, a, b, hmem, rfl⟩
    have hvs_start := buildFrom_covers hstk hv (recipeStart cut bstock ws) hcov_start
      (fun u hu => List.mem_toFinset.mpr hu)
    have hsup : ∀ w ∈ ws.toFinset, Avail (vs ++ bstock) (canon cut w) := by
      intro w hw
      have hww : w ∈ ws := List.mem_toFinset.mp hw
      by_cases ha : Avail bstock (canon cut w)
      · exact avail_weaken (fun u hu => List.mem_append_right _ hu) ha
      · exact hvs_start _ (recipeStart_mem.mpr ⟨w, hww, rfl, ha⟩)
    have hgnf : canon cut goal ≠ 0 := hg.symm ▸ hnz
    obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (vs ++ bstock) hsup
    rw [← flatCount_card cut nd] at hylen
    have hboth := builds_append hvbd hybd
    have hfinal : Avail ((vs ++ ys) ++ bstock) bgoal := by
      rw [← hg]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (vs ++ ys) hboth hfinal
    simp only [List.length_append] at heno
    omega
def edgeAxis (mask goal stride lm : Nat) : Nat :=
  let neg := Nat.xor mask goal
  Nat.land (Nat.lor (Nat.land (Nat.shiftRight goal stride) neg)
    (Nat.land goal (Nat.shiftRight neg stride))) lm
def edgePack (mask goal : Nat) : Nat :=
  Nat.lor (edgeAxis mask goal 1 0x5555555555555555)
    (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 2 0x3333333333333333) 64)
      (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f) 128)
        (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 8 0x00ff00ff00ff00ff) 192)
          (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 16 0x0000ffff0000ffff) 256)
            (Nat.shiftLeft (edgeAxis mask goal 32 0x00000000ffffffff) 320)))))
def sepAxis (stride lm w : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight w stride) w) lm
def sepPack (w : Nat) : Nat :=
  Nat.lor (sepAxis 1 0x5555555555555555 w)
    (Nat.lor (Nat.shiftLeft (sepAxis 2 0x3333333333333333 w) 64)
      (Nat.lor (Nat.shiftLeft (sepAxis 4 0x0f0f0f0f0f0f0f0f w) 128)
        (Nat.lor (Nat.shiftLeft (sepAxis 8 0x00ff00ff00ff00ff w) 192)
          (Nat.lor (Nat.shiftLeft (sepAxis 16 0x0000ffff0000ffff w) 256)
            (Nat.shiftLeft (sepAxis 32 0x00000000ffffffff w) 320)))))
def orSep (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ ih => Nat.lor (sepPack w) ih) ws
theorem edgeAxis_live {mask goal stride lm k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset)
    {n : Nat} (he : (edgeAxis mask goal stride lm).testBit n = true) :
    ∃ w ∈ ws, (sepAxis stride lm w).testBit n = true := by
  unfold edgeAxis at he
  change (((goal >>> stride &&& (mask ^^^ goal)) ||| (goal &&& ((mask ^^^ goal) >>> stride))) &&& lm).testBit n = true at he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Bool.and_eq_true, Bool.or_eq_true] at he
  obtain ⟨hcases, hlm⟩ := he
  have hpm : ∀ j, goal.testBit j = true → mask.testBit j = true := fun j hg => by
    have e := congrArg (fun x => x.testBit j) hgm
    simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
  have hnm : ∀ j, (mask ^^^ goal).testBit j = true → mask.testBit j = true ∧ goal.testBit j = false := fun j hn => by
    rw [Nat.testBit_xor] at hn
    cases hm : mask.testBit j <;> cases hg : goal.testBit j <;> simp_all
  have hsep : ∃ w ∈ ws, w.testBit (stride + n) ≠ w.testBit n := by
    by_contra! hall
    rcases hcases with ⟨hg1, hn0⟩ | ⟨hg0, hn1⟩
    · have h1 := hpm (stride + n) hg1
      have h0 := hnm n hn0
      have eq := liveBin_agrees h1 h0.1 hlive (fun w hw => hall w (List.mem_toFinset.mp hw))
      rw [hg1, h0.2] at eq; exact Bool.noConfusion eq
    · have h0 := hpm n hg0
      have h1 := hnm (stride + n) hn1
      have eq := liveBin_agrees h0 h1.1 hlive (fun w hw => (hall w (List.mem_toFinset.mp hw)).symm)
      rw [hg0, h1.2] at eq; exact Bool.noConfusion eq
  obtain ⟨w, hw, hne⟩ := hsep
  refine ⟨w, hw, ?_⟩
  unfold sepAxis
  change (((w >>> stride) ^^^ w) &&& lm).testBit n = true
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hlm, Bool.and_true]
  cases hb1 : w.testBit (stride + n) <;> cases hb2 : w.testBit n <;> simp_all
theorem orSep_testBit {ws : List Nat} {w j : Nat}
    (hw : w ∈ ws) (hb : (sepPack w).testBit j = true) : (orSep ws).testBit j = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    change (sepPack x ||| orSep xs).testBit j = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | htl
    · exact Or.inl hb
    · exact Or.inr (ih htl)
theorem sepPack_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    Nat.beq (Nat.land (edgePack mask goal) (orSep ws)) (edgePack mask goal) = true := by
  apply Nat.beq_eq.mpr
  apply Nat.eq_of_testBit_eq; intro j
  change ((edgePack mask goal) &&& (orSep ws)).testBit j = (edgePack mask goal).testBit j
  rw [Nat.testBit_and]
  cases he : (edgePack mask goal).testBit j
  · rfl
  · simp only [Bool.true_and]
    have hlane (stride lm shift : Nat)
        (hl : (edgeAxis mask goal stride lm <<< shift).testBit j = true)
        (hs : ∀ w, (sepAxis stride lm w <<< shift).testBit j = true → (sepPack w).testBit j = true) :
        (orSep ws).testBit j = true := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive hl.2
      apply orSep_testBit hw
      apply hs w
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, hsw⟩
    unfold edgePack at he
    change (edgeAxis mask goal 1 0x5555555555555555 |||
      ((edgeAxis mask goal 2 0x3333333333333333 <<< 64) |||
        ((edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f <<< 128) |||
          ((edgeAxis mask goal 8 0x00ff00ff00ff00ff <<< 192) |||
            ((edgeAxis mask goal 16 0x0000ffff0000ffff <<< 256) |||
              (edgeAxis mask goal 32 0x00000000ffffffff <<< 320)))))).testBit j = true at he
    simp only [Nat.testBit_or, Bool.or_eq_true] at he
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive h0
      exact orSep_testBit hw (by
        unfold sepPack
        change (sepAxis 1 0x5555555555555555 w ||| _).testBit j = true
        simp [Nat.testBit_or, hsw])
    · exact hlane 2 0x3333333333333333 64 h1 (fun w hw => by
        unfold sepPack
        change (_ ||| ((sepAxis 2 0x3333333333333333 w <<< 64) ||| _)).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 4 0x0f0f0f0f0f0f0f0f 128 h2 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| ((sepAxis 4 0x0f0f0f0f0f0f0f0f w <<< 128) ||| _))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 8 0x00ff00ff00ff00ff 192 h3 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| ((sepAxis 8 0x00ff00ff00ff00ff w <<< 192) ||| _)))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 16 0x0000ffff0000ffff 256 h4 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| ((sepAxis 16 0x0000ffff0000ffff w <<< 256) ||| _))))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 32 0x00000000ffffffff 320 h5 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| (_ ||| (sepAxis 32 0x00000000ffffffff w <<< 320)))))).testBit j = true
        simp [Nat.testBit_or, hw])
def mapSep (ws : List Nat) : List (Nat × Nat) :=
  List.rec [] (fun w _ ih => (w, sepPack w) :: ih) ws
def forceSepPairs : List Nat → (List (Nat × Nat) → Bool) → Bool
  | [], k => k []
  | w :: ws, k => forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest)))
theorem forceSepPairs_eq (ws : List Nat) (k : List (Nat × Nat) → Bool) :
    forceSepPairs ws k = k (mapSep ws) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest))) = _
    rw [forceW_eq, ih]; rfl
def orSepAll (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Nat.lor p.2 ih) ps
def orSepSkip (x : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 x)) ps
def orSepSkip2 (x y : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 y)) ih (Nat.beq p.1 x)) ps
theorem orSepAll_mapSep (ws : List Nat) : orSepAll (mapSep ws) = orSep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change Nat.lor (sepPack w) (orSepAll (mapSep ws)) = Nat.lor (sepPack w) (orSep ws); rw [ih]
theorem orSepSkip_mapSep (x : Nat) (ws : List Nat) :
    orSepSkip x (mapSep ws) = orSep (dropVal true x ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Nat.lor (sepPack w) (orSepSkip x (mapSep ws))) (orSepSkip x (mapSep ws)) (Nat.beq w x) =
      orSep (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws))
    rw [ih]
    cases Nat.beq w x <;> rfl
theorem dropVal_comm (x y : Nat) (l : List Nat) :
    dropVal true y (dropVal true x l) = dropVal true x (dropVal true y l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    change dropVal true y (bsel (Nat.beq u x) (dropVal true x us) (u :: dropVal true x us)) =
      dropVal true x (bsel (Nat.beq u y) (dropVal true y us) (u :: dropVal true y us))
    cases hux : Nat.beq u x <;> cases huy : Nat.beq u y
    · simp only [bsel_false]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) =
        bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [huy, hux, bsel_false, bsel_false, ih]
    · simp only [bsel_false, bsel_true]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) = _
      rw [huy, bsel_true, ih]
    · simp only [bsel_true, bsel_false]
      change _ = bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [hux, bsel_true, ih]
    · simp only [bsel_true]; exact ih
theorem orSepSkip2_mapSep (x y : Nat) (ws : List Nat) :
    orSepSkip2 x y (mapSep ws) = orSep (dropVal true y (dropVal true x ws)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (Nat.lor (sepPack w) (orSepSkip2 x y (mapSep ws))) (orSepSkip2 x y (mapSep ws)) (Nat.beq w y))
      (orSepSkip2 x y (mapSep ws)) (Nat.beq w x) =
      orSep (dropVal true y (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws)))
    rw [ih]
    cases hx : Nat.beq w x
    · rw [bsel_false]
      change Bool.rec (Nat.lor (sepPack w) (orSep (dropVal true y (dropVal true x ws))))
        (orSep (dropVal true y (dropVal true x ws))) (Nat.beq w y) =
        orSep (bsel (Nat.beq w y) (dropVal true y (dropVal true x ws)) (w :: dropVal true y (dropVal true x ws)))
      cases Nat.beq w y <;> rfl
    · rw [bsel_true]
def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi
theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl
theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h
def checkHintBoundV5 (goal negGoal fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (bounds : List (Nat × List Nat × Nat × Nat)) (cid : Nat) : Bool :=
  match nthBound bounds cid with
  | some b => boundClosesV2 fuel1 ws1 hist1 b
  | none => Bool.rec true false (dagPartF ws1 goal negGoal)
theorem checkHintBoundV5_open {mask goal fuel1 cid : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    checkHintBoundV5 goal (Nat.xor mask goal) fuel1 ws1 hist1 bounds cid = false := by
  unfold checkHintBoundV5
  cases hb : nthBound bounds cid with
  | some b =>
    dsimp only
    have hmem := nthBound_mem hb
    have hg := hgoals b hmem
    exact boundClosesV2_sound (hknown b hmem) (hsub b hmem) hg.1 hg.2 (hstk b hmem) hv hc nd hk hlive
  | none =>
    dsimp only
    have hdp : dagPartF ws1 goal (Nat.xor mask goal) = true := by
      have heq : dagPartF ws1 goal (Nat.xor mask goal) = dagPart ws1 goal (mask ^^^ goal) :=
        dagPartF_eq ws1 goal (mask ^^^ goal)
      rw [heq]; exact dagPart_live hgm hlive
    rw [hdp]
def hintCloseLeafV5 (goal negGoal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (sp : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec (some (cur, h))
    (forceWP (Nat.land h 3) (fun tag =>
      Bool.rec
        (Bool.rec none
          (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
          (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 3 (Nat.land h1 cutMask)) (fun cid =>
            Bool.rec none
              (forceWP (Nat.shiftRight h1 cutBits) (fun h' => some (cur, h')))
              (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
        (Nat.beq tag 3)))
    (Nat.beq (Nat.land ep sp) ep)
theorem hintCloseLeafV5_open {mask goal cutBits cutMask fuel1 : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)} {h : Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    hintCloseLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask bounds fuel1 ws1 hist1 (orSep ws1) cur h = none := by
  unfold hintCloseLeafV5
  rw [sepPack_live hgm hlive]; dsimp only
  rw [forceWP_eq]
  cases Nat.beq (Nat.land h 3) 3
  · dsimp only
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
  · dsimp only
    rw [forceWP_eq, forceWP_eq]
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
def stepLeafV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match cur with
  | (t, dest) :: tl =>
    Bool.rec
      (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) cur h)
      (Bool.rec none
        (match states dest with
         | none => none
         | some saved =>
           Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 (insertSortedF z rest)))
             (Nat.beq saved.1 fuel1))
        (Nat.blt dest count))
      (Nat.beq tok t)
  | [] =>
    hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) [] h
theorem stepLeafV5_ref {mask goal cutBits cutMask count fuel1 z tok h : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    {res : List (Nat × Nat) × Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 (z :: rest))
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (hok : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds states
      fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur h = some res) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (cur := cur) (h := h)
    hgm hknown hsub hgoals hstk hv hc nd hk hlive
  unfold stepLeafV5 at hok
  have hor : Nat.lor (sepPack z) (orSep rest) = orSep (z :: rest) := rfl
  rw [hor] at hok
  cases cur with
  | nil => dsimp only at hok; rw [hcl] at hok; cases hok
  | cons hd tl =>
    obtain ⟨t, dest⟩ := hd
    dsimp only at hok
    cases ht : Nat.beq tok t
    · rw [ht] at hok; dsimp only at hok; rw [hcl] at hok; cases hok
    · rw [ht] at hok; dsimp only at hok
      cases hlt : Nat.blt dest count
      · rw [hlt] at hok; dsimp only at hok; cases hok
      · rw [hlt] at hok; dsimp only at hok
        cases hst : states dest with
        | none => rw [hst] at hok; dsimp only at hok; cases hok
        | some saved =>
          rw [hst] at hok; dsimp only at hok
          cases hf : Nat.beq saved.1 fuel1
          · rw [hf] at hok; dsimp only at hok; cases hok
          · rw [hf] at hok; dsimp only at hok
            cases heq : eqListN saved.2.1 (insertSortedF z rest)
            · rw [heq] at hok; dsimp only at hok; cases hok
            · rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at heq
              exact ⟨dest, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, heq⟩
def checkKeepsV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match (Bool.rec
    (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => none
  | some (c1, h1) =>
    match (Bool.rec
      (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => none
    | some (c2, h2) =>
      match (Bool.rec
        (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => none
      | some (c3, h3) =>
        Bool.rec
          (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3 h3)
          (some (c3, h3)) (Nat.blt fuel (Nat.add n 1))
theorem checkKeepsV5_at {goal negGoal ep cutBits cutMask count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hok : checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur h = some res)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c hh = some r
    | true, false => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c hh = some r
    | false, true => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c hh = some r
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c hh = some r := by
  unfold checkKeepsV5 at hok
  cases hp0 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1
    rw [hp0] at hok; dsimp only at hok
    cases hp1 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2
      rw [hp1] at hok; dsimp only at hok
      cases hp2 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3
        rw [hp2] at hok; dsimp only at hok
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, h, (c1, h1), hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, h2, (c3, h3), hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, h1, (c2, h2), hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at hok; exact Or.inr ⟨c3, h3, res, hok⟩
          · exact Or.inl rfl
def checkOpV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  forceWP (canonV2 mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWP (sepPack z) (fun spZ =>
          checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur h))
        (some (cur, h)) (memN z ws0))
      (some (cur, h)) (Nat.beq z 0))
def check4OpsV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => none
  | some (c1, h1) =>
    match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => none
    | some (c2, h2) =>
      match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => none
      | some (c3, h3) =>
        checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3 h3
theorem check4OpsV5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hop : op < 4)
    (hok : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h = some res) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z (sepPack z)
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c hh = some r := by
  unfold check4OpsV5 at hok
  have extract (rawZ op' : Nat) (c0 : List (Nat × Nat)) (h0 : Nat) (r0 : List (Nat × Nat) × Nat)
      (hz : canon mask rawZ = binOp mask op' x y)
      (hrun : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y rawZ op'
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0 h0 = some r0) :
      binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
        ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n (binOp mask op' x y)
          (sepPack (binOp mask op' x y)) spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB
          ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c hh = some r := by
    unfold checkOpV5 at hrun
    rw [forceWP_eq, canonV2_eq, hz] at hrun
    cases hz0 : Nat.beq (binOp mask op' x y) 0
    · rw [hz0] at hrun; dsimp only at hrun
      cases hm : memN (binOp mask op' x y) ws0
      · rw [hm] at hrun; dsimp only at hrun
        rw [forceWP_eq] at hrun
        exact Or.inr (Or.inr ⟨c0, h0, r0, hrun⟩)
      · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inl (Nat.beq_eq.mp hz0)
  cases hp0 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1; rw [hp0] at hok; dsimp only at hok
    cases hp1 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2; rw [hp1] at hok; dsimp only at hok
      cases hp2 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3; rw [hp2] at hok; dsimp only at hok
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur h (c1, h1) rfl hp0
        · exact extract _ 1 c1 h1 (c2, h2) rfl hp1
        · exact extract _ 2 c2 h2 (c3, h3) rfl hp2
        · exact extract _ 3 c3 h3 res rfl hok
def loopB_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, b, cur, h =>
    forceWP (getDN ws0 b) (fun y =>
      forceList (dropValF true y ws0) (fun wsNoB =>
        forceList (dropValF true y wsNoA) (fun wsNoAB =>
          forceWP (orSepSkip y ps) (fun spNoB =>
            forceWP (orSepSkip2 x y ps) (fun spNoAB =>
              forceWP (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) (fun tokAB =>
                match check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
                | none => none
                | some (cur1, h1) =>
                  loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1 h1))))))
theorem loopB_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (hok : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur h = some res) :
    let y := getDN ws0 b
    ∃ c hh r, check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c hh = some r := by
  induction rem generalizing b0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopB_V5 at hok
    rw [forceWP_eq, forceList_eq, forceList_eq, forceWP_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : b = b0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) hok
def loopA_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, a, cur, h =>
    forceWP (getDN ws0 a) (fun x =>
      forceList (dropValF true x ws0) (fun wsNoA =>
        forceWP (Nat.xor mask x) (fun nx =>
          forceWP (orSepSkip x ps) (fun spNoA =>
            match loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur h with
            | none => none
            | some (cur1, h1) =>
              loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1 h1))))
theorem loopA_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (hok : loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur h = some res) :
    let x := getDN ws0 a
    ∃ c hh r, loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c hh = some r := by
  induction rem generalizing a0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopA_V5 at hok
    rw [forceWP_eq, forceList_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : a = a0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) hok
def dagCheckNodeV5 (mask goal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (nodeHints : Nat → Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      forceWP (lenN ws0) (fun n =>
        Bool.rec
          (Bool.rec
            (Bool.rec false
              (forceW (Nat.xor mask goal) (fun negGoal =>
                forceW (Nat.sub fuel 1) (fun fuel1 =>
                  forceSepPairs ws0 (fun ps =>
                    forceW (orSepAll ps) (fun spAll =>
                      forceW (nodeHints (Nat.add i 1)) (fun h0 =>
                        match loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist n 0 (cursors (Nat.add i 1)) h0 with
                        | none => false
                        | some _ => true))))))
              (Nat.blt n 17))
            true (Nat.beq fuel 0))
          false (memN goal ws0)))
def stepRootV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec
    (match cur with
     | (t, dest) :: tl =>
       Bool.rec
         (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) cur h)
         (Bool.rec none
           (match states dest with
            | none => none
            | some saved =>
              Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 ws)) (Nat.beq saved.1 fuel))
           (Nat.blt dest count))
         (Nat.beq tok t)
     | [] =>
       hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) [] h)
    (some (cur, h)) (Nat.blt (Nat.add fuel 1) (lenN ws))
def loopRootsV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, tok, cur, h =>
    forceList (subsetWordsF stock tok) (fun ws =>
      match stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states ws tok cur h with
      | none => none
      | some (cur1, h1) =>
        loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem (Nat.add tok 1) cur1 h1)
def dagCheckRootsV5 (mask goal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (rootHint : Nat) (stock : List Nat) (fuel : Nat) : Bool :=
  match loopRootsV5 goal (Nat.xor mask goal) ep cutBits cutMask count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur rootHint with
  | none => false
  | some _ => true
theorem loopRootsV5_at {goal negGoal ep cutBits cutMask count fuel : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (hok : loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem t0 cur h = some res) :
    ∃ c hh r, stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock tok) tok c hh = some r := by
  induction rem generalizing t0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV5 at hok
    rw [forceList_eq] at hok
    cases hp : stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock t0) t0 cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : tok = t0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) hok
theorem dagAllNodesV5 {mask goal cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal (edgePack mask goal) cutBits cutMask bounds count
      (dagTrace mask stock fuel forest) cursors nodeHints i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    obtain ⟨hv, hcov⟩ := dagTrace_valid htr
    dsimp only at hv hcov
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV5 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, forceWP_eq, lenN_eq, memN_eq] at hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hchk; exact Bool.noConfusion hchk
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      cases hcg : ws.contains goal
      · rw [hcg] at hchk; dsimp only at hchk
        have hrem0 : Nat.beq rem 0 = false := beq_false_ne hrem_pos
        rw [hrem0] at hchk; dsimp only at hchk
        cases h17 : Nat.blt ws.length 17
        · rw [h17] at hchk; exact Bool.noConfusion hchk
        · rw [h17] at hchk; dsimp only at hchk
          rw [forceW_eq, forceW_eq, forceSepPairs_eq, forceW_eq, forceW_eq] at hchk
          cases hloop : loopA_V5 mask goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
              (dagTrace mask stock fuel forest) rem (Nat.sub rem 1) ws.length (orSepAll (mapSep ws)) ws (mapSep ws) hist
              ws.length 0 (cursors (Nat.add i 1)) (nodeHints (Nat.add i 1)) with
          | none => rw [hloop] at hchk; exact Bool.noConfusion hchk
          | some resA =>
            have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
            have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
            obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
            obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
            have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
            have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
                ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
                  ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
                  ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
                  binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
                  LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                    (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
              by_cases hlt : ia0 < ib0
              · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
                  by simp only [hlt, ite_true]; exact hea0,
                  by simp only [hlt, ite_true]; exact heb0,
                  by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
              · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
                have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                    dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
                  ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
                exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
                  by simp only [hlt, ite_false]; exact heb0,
                  by simp only [hlt, ite_false]; exact hea0,
                  by rw [hea0, heb0, hopEq],
                  by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
            obtain ⟨cA, hA, rA, hB⟩ := loopA_V5_at (a := a) (Nat.zero_le a) (by omega) hloop
            obtain ⟨cB, hB', rB, hO⟩ := loopB_V5_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
            simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
            set x := ws.getD a 0
            set y := ws.getD b 0
            set z := binOp mask op x y
            have hznz : z ≠ 0 := hzeq.symm ▸ hz0
            have hznm : ws.contains z = false := by
              cases h : ws.contains z
              · rfl
              · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
            rcases check4OpsV5_at hop_lt hO with hz' | hcm | ⟨cK, hK', rK, hK⟩
            · exact hznz hz'
            · rw [hznm] at hcm; exact Bool.noConfusion hcm
            · have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
              have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
              have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
              have hzNotW : z ∉ ws := fun hm => by
                have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
              have hdropComm : dropVal true y (dropVal true x ws) = dropVal true x (dropVal true y ws) :=
                dropVal_comm x y ws
              set rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
              have hv' : HistValid mask stock ((z, x, y) :: hist) :=
                ⟨⟨op, hop_lt, rfl⟩, hcov x hxM, hcov y hyM, hv⟩
              have hcov' : WsCovered stock ((z, x, y) :: hist) (z :: rest) := by
                intro w hw
                rcases List.mem_cons.mp hw with rfl | hw'
                · exact Or.inr ⟨x, y, List.mem_cons_self⟩
                · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hw').1).1
                  rcases hcov w hwm with hst | ⟨u, v, hm⟩
                  · exact Or.inl hst
                  · exact Or.inr ⟨u, v, List.mem_cons_of_mem _ hm⟩
              have hnd_u : (z :: rest).Nodup :=
                List.nodup_cons.mpr ⟨fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1,
                  dropVal_nodup (dropVal_nodup nd)⟩
              have hset_u : (z :: rest).toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
                ext w; simp only [rest, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, ← dropVal_toFinset]
              have hlive_u : LiveBin mask goal k' (z :: rest).toFinset := by rwa [hset_u]
              have hset_s : (insertSorted z rest).toFinset = (z :: rest).toFinset := by
                ext w; simp only [List.mem_toFinset, insertSorted_mem, List.mem_cons]
              have hlive_s : LiveBin mask goal k' (insertSorted z rest).toFinset := by rwa [hset_s]
              have hlen' : (insertSorted z rest).length =
                  ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) :=
                list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
              have hcard' : (insertSorted z rest).length ≤ rem := by
                have hnd_s : (insertSorted z rest).Nodup :=
                  insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
                have := liveBin_card_le hlive_s
                rw [List.toFinset_card_of_nodup hnd_s] at this; omega
              have h2len : 2 ≤ ws.length := by
                have hsub2 : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
                  intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
                  · exact List.mem_toFinset.mpr hxM
                  · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hyM
                have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
                have hc := Finset.card_le_card hsub2
                rw [List.toFinset_card_of_nodup nd] at hc; omega
              have hka := checkKeepsV5_at hK keepA keepB
              have finish {tok' hh' : Nat} {c' : List (Nat × Nat)} {rr : List (Nat × Nat) × Nat}
                  (hstep : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
                    (dagTrace mask stock fuel forest) (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c' hh' = some rr) : False := by
                obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                  stepLeafV5_ref hgm hknown hsub hgoals hstk hv' hcov' hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
                exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
              cases keepA <;> cases keepB
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
                · rw [hdropComm] at hst; exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
                · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk
def nodupB : List Nat → Bool
  | [] => true
  | w :: ws => !memN w ws && nodupB ws
theorem nodupB_spec {l : List Nat} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold nodupB at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', memN_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1, ih h.2⟩
theorem kn_nil : KnownBin [] := fun _ h => nomatch h
theorem kn_cons {m : Nat} {s : List Nat} {l g : Nat} {bs : List (Nat × List Nat × Nat × Nat)}
    (h : LowerBin m s g l) (hs : KnownBin bs) : KnownBin ((m, s, l, g) :: bs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h
  · exact hs b hb
def checkSliceMetaV5 (mask goal ep : Nat) (stock : List Nat)
    (bounds : List (Nat × List Nat × Nat × Nat)) : Bool :=
  Nat.beq (Nat.land goal mask) goal &&
  !Nat.beq goal 0 &&
  stock.all (fun w => Nat.beq (canon mask w) w) &&
  nodupB stock &&
  Nat.beq ep (edgePack mask goal) &&
  bounds.all (fun b =>
    Nat.beq (Nat.land mask b.1) b.1 &&
    Nat.beq (canon b.1 goal) b.2.2.2 &&
    !Nat.beq b.2.2.2 0 &&
    stock.all (fun s => availB b.2.1 (canon b.1 s)))
theorem lowerDagV5 {mask goal ep cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hknown : KnownBin bounds)
    (hroots : dagCheckRootsV5 mask goal ep cutBits cutMask count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) (nodeHints 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal ep cutBits cutMask bounds count
      (dagTraceF mask stock fuel forest) cursors nodeHints i = true)
    (hmeta : checkSliceMetaV5 mask goal ep stock bounds = true) :
    LowerBin mask stock goal (fuel + 1) := by
  unfold checkSliceMetaV5 at hmeta
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmeta
  obtain ⟨⟨⟨⟨⟨hgmB, hgnzB⟩, hcs⟩, hndB⟩, hepB⟩, hbdB⟩ := hmeta
  have hgm : Masked mask goal := Nat.beq_eq.mp hgmB
  have hgnz : goal ≠ 0 := fun h => by rw [h] at hgnzB; exact Bool.noConfusion hgnzB
  have snd : stock.Nodup := nodupB_spec hndB
  have hep : ep = edgePack mask goal := Nat.beq_eq.mp hepB
  have hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact Nat.beq_eq.mp h.1.1.1
  have hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Nat.beq_eq.mp h.1.1.2, fun h0 => by rw [h0] at h; exact Bool.noConfusion h.1.2⟩
  have hstkB : ∀ b ∈ bounds, stock.all (fun s => availB b.2.1 (canon b.1 s)) = true := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact h.2
  subst hep
  have hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s) := fun b hb s hs =>
    availB_spec.mp (List.all_eq_true.mp (hstkB b hb) s hs)
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  unfold dagCheckRootsV5 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  cases hrl : loopRootsV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count fuel bounds
      (dagTrace mask stock fuel forest) stock (2 ^ stock.length) 0 (cursors 0) (nodeHints 0) with
  | none => rw [hrl] at hroots; exact Bool.noConfusion hroots
  | some resR =>
    obtain ⟨c, hh, rr, hsr⟩ := loopRootsV5_at (tok := tok) (Nat.zero_le tok) (by omega) hrl
    rw [subsetWordsF_eq] at hsr
    have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
    have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
    have hcard : (subsetWords stock tok).length ≤ fuel + 1 := by
      have := liveBin_card_le hlive'
      rw [List.toFinset_card_of_nodup hnd] at this; omega
    have hnw : Nat.blt (Nat.add fuel 1) (lenN (subsetWords stock tok)) = false := by
      rw [lenN_eq]
      cases h : Nat.blt (Nat.add fuel 1) (subsetWords stock tok).length
      · rfl
      · have hlt' : fuel + 1 < (subsetWords stock tok).length := Nat.blt_eq.mp h
        omega
    have hcov0 : WsCovered stock [] (subsetWords stock tok) :=
      fun w hw => Or.inl (subsetWords_subset stock tok w hw)
    have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (fuel1 := fuel) (hist1 := []) (cur := c) (h := hh)
      hgm hknown hsub hgoals hstk trivial hcov0 hnd (k := k) (by omega) hlive'
    unfold stepRootV5 at hsr
    rw [hnw] at hsr; dsimp only at hsr
    cases c with
    | nil => dsimp only at hsr; rw [hcl] at hsr; cases hsr
    | cons hd tl =>
      obtain ⟨t, dest⟩ := hd
      dsimp only at hsr
      cases ht : Nat.beq tok t
      · rw [ht] at hsr; dsimp only at hsr; rw [hcl] at hsr; cases hsr
      · rw [ht] at hsr; dsimp only at hsr
        cases hltc : Nat.blt dest count
        · rw [hltc] at hsr; dsimp only at hsr; cases hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest dest with
          | none => rw [htr2] at hsr; dsimp only at hsr; cases hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; dsimp only at hsr; cases hsr
            · rw [hf] at hsr; dsimp only at hsr
              cases heq : eqListN saved.2.1 (subsetWords stock tok)
              · rw [heq] at hsr; dsimp only at hsr; cases hsr
              · rw [eqListN_eq, beq_iff_eq] at heq
                exact dagAllNodesV5 hgm hknown hsub hgoals hstk snd hnodes fuel dest saved
                  (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (heq ▸ hlive')
def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)
def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))
def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    forceWP (Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask) (fun code =>
      unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc))
def unpackCursorV5 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      unpackListAux data (Nat.shiftRight entry sizeBits) w wMask tokBits tokMask (Nat.land entry sizeMask) [])
def unpackHintV5 (index data idxW idxMask lenBits lenMask : Nat) : Nat → Nat :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      forceWP (Nat.land entry lenMask) (fun hlen =>
        Bool.rec
          (Nat.land (Nat.shiftRight data (Nat.shiftRight entry lenBits)) (Nat.sub (Nat.shiftLeft 1 hlen) 1))
          0 (Nat.beq hlen 0)))

def decodeHints (table cutsWidth : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, data =>
    forceWP (unpackF table 10 (Nat.land data 31)) (fun entry =>
      forceWP (Nat.land entry 15) (fun clen =>
        forceWP (Nat.shiftRight entry 4) (fun sym =>
          forceWP (Nat.shiftRight data clen) (fun rest =>
            Bool.rec
              (Bool.rec
                (Nat.lor (Nat.lor 3 (Nat.shiftLeft (sym - 3) 2))
                  (Nat.shiftLeft (decodeHints table cutsWidth n rest) (cutsWidth + 2)))
                (Nat.lor sym (Nat.shiftLeft (decodeHints table cutsWidth n rest) 2))
                (Nat.blt sym 3))
              (Nat.lor (Nat.land rest (Nat.sub (Nat.shiftLeft 1 cutsWidth) 1) * 4 + 3)
                (Nat.shiftLeft (decodeHints table cutsWidth n (Nat.shiftRight rest cutsWidth)) (cutsWidth + 2)))
              (Nat.beq sym 63)))))
def unpackCompressedHints (tab cutWidth index data idxW countW bitW bitMask : Nat) : Nat → Nat :=
  fun p =>
    forceWP (unpackF index idxW p) (fun entry =>
      forceWP (Nat.land entry bitMask) (fun bitLen =>
        forceWP (Nat.shiftRight entry bitW) (fun sizes =>
          decodeHints tab cutWidth (Nat.land sizes (Nat.sub (Nat.shiftLeft 1 countW) 1))
            (Nat.land (Nat.shiftRight data (Nat.shiftRight sizes countW))
              (Nat.sub (Nat.shiftLeft 1 bitLen) 1)))))

def m_0 : Nat := 0xc0c00000c0c0000
def s_0 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_0 : Nat := 0x40000040c0000
def ep_0 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_0 : Nat → Nat := fun _ => 0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 m_0 g_0 ep_0 1 1 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 m_0 g_0 ep_0 1 1 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) (nh_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)

def m_1 : Nat := 0x3300330000000000
def s_1 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_1 : Nat := 0x100130000000000
def ep_1 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_1 : Nat → Nat := fun _ => 0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 m_1 g_1 ep_1 1 1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 m_1 g_1 ep_1 1 1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) (nh_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)

def m_2 : Nat := 0xff000000
def s_2 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_2 : Nat := 0x17000000
def ep_2 : Nat := 0x600000000000000120000000000000014000000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_2 : Nat → Nat := fun _ => 0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 m_2 g_2 ep_2 1 1 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 m_2 g_2 ep_2 1 1 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) (nh_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)

def m_3 : Nat := 0xa0a00000a0a0000
def s_3 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_3 : Nat := 0x20000020a0000
def ep_3 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_3 : Nat → Nat := fun _ => 0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 m_3 g_3 ep_3 1 1 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 m_3 g_3 ep_3 1 1 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) (nh_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)

def m_4 : Nat := 0xff00
def s_4 : List Nat := [0x5500, 0x3300, 0xf00]
def g_4 : Nat := 0x1700
def ep_4 : Nat := 0x60000000000000012000000000000001400
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_4 : Nat → Nat := fun _ => 0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 m_4 g_4 ep_4 1 1 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 m_4 g_4 ep_4 1 1 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) (nh_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)

def m_5 : Nat := 0xf0f000000000000
def s_5 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_5 : Nat := 0x107000000000000
def ep_5 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_5 : Nat → Nat := fun _ => 0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 m_5 g_5 ep_5 1 1 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 m_5 g_5 ep_5 1 1 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) (nh_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)

def m_7 : Nat := 0xf000f0000000000
def s_7 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_7 : Nat := 0x100070000000000
def ep_7 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_7 : Nat → Nat := fun _ => 0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 m_7 g_7 ep_7 1 1 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 m_7 g_7 ep_7 1 1 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) (nh_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)

def m_8 : Nat := 0xcccc0000
def s_8 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_8 : Nat := 0x44c0000
def ep_8 : Nat := 0x480000000000000408000000000000000000000000000004400000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_8 : Nat → Nat := fun _ => 0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 m_8 g_8 ep_8 1 1 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 m_8 g_8 ep_8 1 1 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) (nh_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)

def m_9 : Nat := 0x3030303000000000
def s_9 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_9 : Nat := 0x10103000000000
def ep_9 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_9 : Nat → Nat := fun _ => 0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 m_9 g_9 ep_9 1 1 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 m_9 g_9 ep_9 1 1 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) (nh_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)

def m_10 : Nat := 0x5500550000000000
def s_10 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_10 : Nat := 0x100150000000000
def ep_10 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_10 : Nat → Nat := fun _ => 0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 m_10 g_10 ep_10 1 1 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 m_10 g_10 ep_10 1 1 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) (nh_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)

def m_12 : Nat := 0xff0000000000
def s_12 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_12 : Nat := 0x170000000000
def ep_12 : Nat := 0x6000000000000001200000000000000140000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_12 : Nat → Nat := fun _ => 0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) (nh_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0x2222222200000000
def s_13 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_13 : Nat := 0x2022200000000
def ep_13 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_13 : Nat → Nat := fun _ => 0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) (nh_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_18 : Nat := 0x5500000055000000
def s_18 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_18 : Nat := 0x100000015000000
def ep_18 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_18 : Nat → Nat := fun _ => 0
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) (nh_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x3300000033000000
def s_19 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_19 : Nat := 0x100000013000000
def ep_19 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_19 : Nat → Nat := fun _ => 0
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) (nh_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xf0000000f000000
def s_20 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_20 : Nat := 0x100000007000000
def ep_20 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_20 : Nat → Nat := fun _ => 0
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) (nh_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xf0f000000000
def s_21 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_21 : Nat := 0x107000000000
def ep_21 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_21 : Nat → Nat := fun _ => 0
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 1 bds_21 (dagTraceF m_21 s_21 3 f_21) (cur_21 0) (nh_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 1 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xaaaa
def s_22 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_22 : Nat := 0x22a
def ep_22 : Nat := 0x28000000000000020800000000000002200000000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_22 : Nat → Nat := fun _ => 0
def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 1 bds_22 (dagTraceF m_22 s_22 3 f_22) (cur_22 0) (nh_22 0) s_22 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 1 ch_22 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 1 → ch_22 i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xcccc
def s_23 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_23 : Nat := 0x44c
def ep_23 : Nat := 0x48000000000000040800000000000000000000000000000440
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_23 : Nat → Nat := fun _ => 0
def f_23 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 1 (dagTraceF m_23 s_23 3 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 1 bds_23 (dagTraceF m_23 s_23 3 f_23) (cur_23 0) (nh_23 0) s_23 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 1 ch_23 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 1 → ch_23 i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xf0f0
def s_24 : List Nat := [0x5050, 0x3030, 0xf0]
def g_24 : Nat := 0x1070
def ep_24 : Nat := 0x60000000000000000000000000000010200000000000001040
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_24 : Nat → Nat := fun _ => 0
def f_24 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 1 (dagTraceF m_24 s_24 3 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 1 bds_24 (dagTraceF m_24 s_24 3 f_24) (cur_24 0) (nh_24 0) s_24 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 1 ch_24 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 1 → ch_24 i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 4 :=
  lowerDagV5 (kn_nil) rc_24 nc_24 (by decide +kernel)

def m_26 : Nat := 0x3333000000000000
def s_26 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_26 : Nat := 0x113000000000000
def ep_26 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
def cur_26 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_26 : Nat → Nat := fun _ => 0
def f_26 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 1 (dagTraceF m_26 s_26 3 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 1 bds_26 (dagTraceF m_26 s_26 3 f_26) (cur_26 0) (nh_26 0) s_26 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26 : treeBlockF 0 1 ch_26 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 1 → ch_26 i = true := fun _ h1 h2 => treeBlockF_at nb_26 h1 h2
theorem lb_26 : LowerBin m_26 s_26 g_26 4 :=
  lowerDagV5 (kn_nil) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xf000f00000f000f
def s_27 : List Nat := [0x500050000050005, 0x300030000030003, 0xf000f, 0xf000000000f]
def g_27 : Nat := 0x1000700000f000f
def ep_27 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xff00ff0000000000
def s_28 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_28 : Nat := 0x100170000000000
def ep_28 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_12, s_12, 4, g_12), (m_10, s_10, 4, g_10), (m_1, s_1, 4, g_1)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) (nh_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_12 (kn_cons lb_10 (kn_cons lb_1 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_31 : Nat := 0x3333333300000000
def s_31 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_31 : Nat := 0x113133300000000
def ep_31 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_26, s_26, 4, g_26), (m_9, s_9, 4, g_9), (m_13, s_13, 4, g_13)]
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def hc_31_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_31_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_31 : Nat → Nat := fun p => Bool.rec (hc_31_1 (Nat.sub p 32)) (hc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 43 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) (nh_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 ch_31 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 ch_31 = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_26 (kn_cons lb_9 (kn_cons lb_13 (kn_nil))))) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xaa00aa00aa00aa
def s_32 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_32 : Nat := 0x20022000a002a
def ep_32 : Nat := 0x800080000002000000020000000000000000000020000000a000800020022000000200000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_32 : Nat → Nat := fun _ => 0
def f_32 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 1 (dagTraceF m_32 s_32 3 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 1 bds_32 (dagTraceF m_32 s_32 3 f_32) (cur_32 0) (nh_32 0) s_32 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 1 ch_32 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 1 → ch_32 i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 4 :=
  lowerDagV5 (kn_nil) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xaaaaaaaa00000000
def s_33 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_33 : Nat := 0x2022200000000
def ep_33 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_35 : Nat := 0x3030303030303030
def s_35 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_35 : Nat := 0x10103010101030
def ep_35 : Nat := 0x1000000000001020000000200010002000000020000000000000000000000000000000000010100010101000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xaaaa0000aaaa0000
def s_36 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_36 : Nat := 0x20000020a0000
def ep_36 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_39 : Nat := 0xaaaa0000aaaa
def s_39 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_39 : Nat := 0x2220000022a
def ep_39 : Nat := 0x800000000000000000000002000000028000002000000020800000222000002200000000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_22 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0x3300330033003300
def s_40 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_40 : Nat := 0x100130013001300
def ep_40 : Nat := 0x1200000000001200000000000000000000000000010002000200020000000000000000000100100010001000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf000f000f000f00
def s_41 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_41 : Nat := 0x100070007000700
def ep_41 : Nat := 0x600000000000600000000000000000000000000000000000000000001000200020002000100040004000400
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_43 : Nat := 0xffff
def s_43 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_43 : Nat := 0x177f
def ep_43 : Nat := 0x68000000000000060800000000000012200000000000001440
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_24, s_24, 4, g_24), (m_23, s_23, 4, g_23), (m_22, s_22, 4, g_22)]
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_43_1 (Nat.sub p 32)) (cc_43_0 p) (Nat.blt p 32)
def hc_43_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_43_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_43 : Nat → Nat := fun p => Bool.rec (hc_43_1 (Nat.sub p 32)) (hc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 43 bds_43 (dagTraceF m_43 s_43 6 f_43) (cur_43 0) (nh_43 0) s_43 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 ch_43 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 43 ch_43 = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 43 → ch_43 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 43 → ch_43 i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_24 (kn_cons lb_23 (kn_cons lb_22 (kn_nil))))) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xaaaaaaaa
def s_44 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_44 : Nat := 0x20a022a
def ep_44 : Nat := 0x20000000000008002800000000020a020800000000020002200000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_22 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xff000000ff000000
def s_45 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_45 : Nat := 0x100000017000000
def ep_45 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20), (m_2, s_2, 4, g_2), (m_18, s_18, 4, g_18), (m_19, s_19, 4, g_19)]
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_45_1 (Nat.sub p 32)) (cc_45_0 p) (Nat.blt p 32)
def hc_45_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_45_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_45 : Nat → Nat := fun p => Bool.rec (hc_45_1 (Nat.sub p 32)) (hc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 43 bds_45 (dagTraceF m_45 s_45 6 f_45) (cur_45 0) (nh_45 0) s_45 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 ch_45 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 43 ch_45 = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 43 → ch_45 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 43 → ch_45 i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 7 :=
  lowerDagV5 (kn_cons lb_20 (kn_cons lb_2 (kn_cons lb_18 (kn_cons lb_19 (kn_nil))))) rc_45 nc_45 (by decide +kernel)

def m_47 : Nat := 0xf0f00000f0f0000
def s_47 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_47 : Nat := 0x1070000070f0000
def ep_47 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_20, s_20, 4, g_20), (m_0, s_0, 4, g_0), (m_3, s_3, 4, g_3)]
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_47_1 (Nat.sub p 32)) (cc_47_0 p) (Nat.blt p 32)
def hc_47_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_47_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_47 : Nat → Nat := fun p => Bool.rec (hc_47_1 (Nat.sub p 32)) (hc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 43 bds_47 (dagTraceF m_47 s_47 6 f_47) (cur_47 0) (nh_47 0) s_47 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 ch_47 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 43 ch_47 = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 43 → ch_47 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 43 → ch_47 i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_20 (kn_cons lb_0 (kn_cons lb_3 (kn_nil))))) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xa0a0a0a0a0a0a0a
def s_48 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_48 : Nat := 0x20202020a020a
def ep_48 : Nat := 0x208000800000200000000000002000000080008000000000000000000020202020002000000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xaaaaaaaaaaaaaaaa
def s_49 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_49 : Nat := 0x20222020a022a
def ep_49 : Nat := 0x20800080000022000000020000200200008002800020200020a020800020222020002200000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_36, s_36, 5, g_36), (m_48, s_48, 5, g_48), (m_39, s_39, 5, g_39), (m_44, s_44, 5, g_44), (m_32, s_32, 4, g_32), (m_3, s_3, 4, g_3), (m_22, s_22, 4, g_22)]
def cur_49 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b09d27090e318c23071dc07019360580601715c1705c107401003c4d2340d0340c1288a006401 0xca519241ea396a31db498a32283e8350cc51a34e7b42c24e6a42184eb826ab5ea252515e8350845094528b5e7b52725e6a52415e61264944512f41232134294f1943e343d24fb2439a3f5a33394e3142103e0832001f 10 1023 4 15 11 2047 16 65535
def nh_49 : Nat → Nat := unpackHintV5 0x210807a341e50770325b98e6d81db287637298a0761e155ed25584553855303d460c50a1d3b8e4e01d0d5642a150a8041628d463285989e8527a00998a17dd42f60001780000 0x10172025ac05e346c00008c5d2c2e2c16034680017bc1cb82c0b8ba001a340000e07b82e5aeaf2e9e346ad1c397b8fbdef7bdc1a8c3dd9755c25d3d46f518da3872f7182010e1800c631d0000130000001e00fa782aaaa003c0000012f73c11c0e00551ce738e60be6468d1a3400002a80026468d00200000200a18236468d0039070e20c 18 262143 7 127
def f_49 : Nat → Nat × Nat := unpackForestF 0xea390b43db490a4fbc51ba4eb8260a43a35ea2520a3f6452635e84506352625e625261260a33412f49444123094e0942194f21341943083e0832001f 5 11
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 3 7 bds_49 30 (dagTraceF m_49 s_49 7 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 3 7 30 bds_49 (dagTraceF m_49 s_49 7 f_49) (cur_49 0) (nh_49 0) s_49 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49 : treeBlockF 0 30 ch_49 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 30 → ch_49 i = true := fun _ h1 h2 => treeBlockF_at nb_49 h1 h2
theorem lb_49 : LowerBin m_49 s_49 g_49 8 :=
  lowerDagV5 (kn_cons lb_13 (kn_cons lb_36 (kn_cons lb_48 (kn_cons lb_39 (kn_cons lb_44 (kn_cons lb_32 (kn_cons lb_3 (kn_cons lb_22 (kn_nil))))))))) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xff00ff00ff00ff00
def s_50 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_50 : Nat := 0x100170017001700
def ep_50 : Nat := 0x1600000000001600000000000000000000000000010006000600060001001200120012000100140014001400
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 7, g_45)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 7 f_50) (cur_50 0) (nh_50 0) s_50 7 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 7 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 8 :=
  lowerDagV5 (kn_cons lb_45 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xffffffff
def s_51 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_51 : Nat := 0x175f177f
def ep_51 : Nat := 0x20000000000048006800000000060a060800000000120012200000000014501440
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 7 f_51) (cur_51 0) (nh_51 0) s_51 7 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 7 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 8 :=
  lowerDagV5 (kn_cons lb_43 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xffff0000ffff
def s_52 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_52 : Nat := 0x17770000177f
def ep_52 : Nat := 0x800000000000000000000006000000068000006000000060800001222000012200000144400001440
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) (nh_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 7 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV5 (kn_cons lb_43 (kn_nil)) rc_52 nc_52 (by decide +kernel)


def m_132 : Nat := 0xf0ff0f00f0ff0f0
def s_132 : List Nat := [0x505505005055050, 0x303303003033030, 0xf0f00000f0f0, 0xf00f0000f00f0, 0xf0ff0f0]
def g_132 : Nat := 0x1071070070f1070
def huffman_132 : Nat := 0xbf10cbf100bf10cbf100bf10cbf100bf10cbf100bf10cbf100bf10cbf100bf10cbf100bf10cbf1
def fc_132_0 : Nat := 0x0
def ff_132_0 : Nat → Nat × Nat := unpackForestF fc_132_0 1 1
def ci_132_0 : Nat := 0x0
def cv_132_0 : Nat := 0x0
def hi_132_0 : Nat := 0x14
def hv_132_0 : Nat := 0xd
def cur_132_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_132_0 cv_132_0 1 1 1 1 1 1 1 1
def hint_132_0 : Nat → Nat := unpackCompressedHints huffman_132 1 hi_132_0 hv_132_0 5 2 3 7
def fr_132 (p : Nat) : Nat × Nat := ff_132_0 (p - 0)
def cr_132 (p : Nat) : List (Nat × Nat) := cur_132_0 (p - 0)
def hr_132 (p : Nat) : Nat := hint_132_0 (p - 0)
def bds_132 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 7, g_47), (m_0, s_0, 4, g_0), (m_3, s_3, 4, g_3)]
def ep_132 : Nat := 0x608000000000000000000000006006000080060000000000000000001021020020010200104104004001040
def ch_132 : Nat → Bool := dagCheckNodeV5 0xf0ff0f00f0ff0f0 0x1071070070f1070 ep_132 1 1 bds_132 0 (dagTraceF 0xf0ff0f00f0ff0f0 s_132 7 fr_132) cr_132 hr_132
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_132 : dagCheckRootsV5 0xf0ff0f00f0ff0f0 0x1071070070f1070 ep_132 1 1 0 bds_132 (dagTraceF 0xf0ff0f00f0ff0f0 s_132 7 fr_132) (cr_132 0) (hr_132 0) s_132 7 = true := by decide +kernel
theorem nc_132 : ∀ i, 0 ≤ i → i < 0 → ch_132 i = true := fun i _ hi => (Nat.not_lt_zero i hi).elim
theorem lb_132 : LowerBin 0xf0ff0f00f0ff0f0 s_132 0x1071070070f1070 8 :=
  lowerDagV5 (kn_cons lb_47 (kn_cons lb_0 (kn_cons lb_3 (kn_nil)))) rc_132 nc_132 (by decide +kernel)

def m_128 : Nat := 0x33333333cccccccc
def s_128 : List Nat := [0x1111111144444444, 0xcccccccc, 0x30303030c0c0c0c, 0x33003300cc00cc, 0x33330000cccc]
def g_128 : Nat := 0x1131333044c044c
def huffman_128 : Nat := 0xbf10cbf100bf10cbf100bf10cbf100bf10cbf100bf10cbf100bf10cbf100bf10cbf100bf10cbf1
def fc_128_0 : Nat := 0x0
def ff_128_0 : Nat → Nat × Nat := unpackForestF fc_128_0 1 1
def ci_128_0 : Nat := 0x0
def cv_128_0 : Nat := 0x0
def hi_128_0 : Nat := 0x14
def hv_128_0 : Nat := 0xd
def cur_128_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_128_0 cv_128_0 1 1 1 1 1 1 1 1
def hint_128_0 : Nat → Nat := unpackCompressedHints huffman_128 1 hi_128_0 hv_128_0 5 2 3 7
def fr_128 (p : Nat) : Nat × Nat := ff_128_0 (p - 0)
def cr_128 (p : Nat) : List (Nat × Nat) := cur_128_0 (p - 0)
def hr_128 (p : Nat) : Nat := hint_128_0 (p - 0)
def bds_128 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31), (m_1, s_1, 4, g_1), (m_8, s_8, 4, g_8)]
def ep_128 : Nat := 0x1220000000000012002000480048010202000408040800000000000000000110100004400440
def ch_128 : Nat → Bool := dagCheckNodeV5 0x33333333cccccccc 0x1131333044c044c ep_128 1 1 bds_128 0 (dagTraceF 0x33333333cccccccc s_128 7 fr_128) cr_128 hr_128
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_128 : dagCheckRootsV5 0x33333333cccccccc 0x1131333044c044c ep_128 1 1 0 bds_128 (dagTraceF 0x33333333cccccccc s_128 7 fr_128) (cr_128 0) (hr_128 0) s_128 7 = true := by decide +kernel
theorem nc_128 : ∀ i, 0 ≤ i → i < 0 → ch_128 i = true := fun i _ hi => (Nat.not_lt_zero i hi).elim
theorem lb_128 : LowerBin 0x33333333cccccccc s_128 0x1131333044c044c 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_cons lb_1 (kn_cons lb_8 (kn_nil)))) rc_128 nc_128 (by decide +kernel)

def m_102 : Nat := 0x3333333333333333
def s_102 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_102 : Nat := 0x113133313131333
def huffman_102 : Nat := 0xfc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401
def fc_102_0 : Nat := 0x0
def ff_102_0 : Nat → Nat × Nat := unpackForestF fc_102_0 1 1
def ci_102_0 : Nat := 0x0
def cv_102_0 : Nat := 0x0
def hi_102_0 : Nat := 0x3
def hv_102_0 : Nat := 0x0
def cur_102_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_102_0 cv_102_0 1 1 1 1 1 1 1 1
def hint_102_0 : Nat → Nat := unpackCompressedHints huffman_102 1 hi_102_0 hv_102_0 2 1 1 1
def fr_102 (p : Nat) : Nat × Nat := ff_102_0 (p - 0)
def cr_102 (p : Nat) : List (Nat × Nat) := cur_102_0 (p - 0)
def hr_102 (p : Nat) : Nat := hint_102_0 (p - 0)
def bds_102 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31), (m_35, s_35, 5, g_35), (m_40, s_40, 5, g_40)]
def ep_102 : Nat := 0x1200000000001220000000200012002000000020010202000202020000000000000000000110100010101000
def ch_102 : Nat → Bool := dagCheckNodeV5 0x3333333333333333 0x113133313131333 ep_102 1 1 bds_102 0 (dagTraceF 0x3333333333333333 s_102 7 fr_102) cr_102 hr_102
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_102 : dagCheckRootsV5 0x3333333333333333 0x113133313131333 ep_102 1 1 0 bds_102 (dagTraceF 0x3333333333333333 s_102 7 fr_102) (cr_102 0) (hr_102 0) s_102 7 = true := by decide +kernel
theorem nc_102 : ∀ i, 0 ≤ i → i < 0 → ch_102 i = true := fun i _ hi => (Nat.not_lt_zero i hi).elim
theorem lb_102 : LowerBin 0x3333333333333333 s_102 0x113133313131333 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_cons lb_35 (kn_cons lb_40 (kn_nil)))) rc_102 nc_102 (by decide +kernel)

def m_103 : Nat := 0xcccccccccccccccc
def s_103 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_103 : Nat := 0x440444044c044c
def huffman_103 : Nat := 0x434004120042300412007f400412004230041200434004120042300412007f4004120042300412
def fc_103_0 : Nat := 0x64f325dd428a064752620a0c8601f
def ff_103_0 : Nat → Nat × Nat := unpackForestF fc_103_0 3 10
def ci_103_0 : Nat := 0x24489121d3870a8601
def cv_103_0 : Nat := 0x1b505140e4c20a224f792d247190c01f
def hi_103_0 : Nat := 0x2e864550c8a20894400230a5c60008c000ec52c05dd80000
def hv_103_0 : Nat := 0x1cbd5de53b47fd7ffea01f8079
def cur_103_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_103_0 cv_103_0 7 127 3 7 10 1023 14 16383
def hint_103_0 : Nat → Nat := unpackCompressedHints huffman_103 1 hi_103_0 hv_103_0 19 6 6 63
def fr_103 (p : Nat) : Nat × Nat := ff_103_0 (p - 0)
def cr_103 (p : Nat) : List (Nat × Nat) := cur_103_0 (p - 0)
def hr_103 (p : Nat) : Nat := hint_103_0 (p - 0)
def bds_103 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_8, s_8, 4, g_8), (m_23, s_23, 4, g_23)]
def ep_103 : Nat := 0x408000800000400000000000044004000480048000004000408040800000000000000000044044404400440
def ch_103 : Nat → Bool := dagCheckNodeV5 0xcccccccccccccccc 0x440444044c044c ep_103 1 1 bds_103 9 (dagTraceF 0xcccccccccccccccc s_103 6 fr_103) cr_103 hr_103
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_103 : dagCheckRootsV5 0xcccccccccccccccc 0x440444044c044c ep_103 1 1 9 bds_103 (dagTraceF 0xcccccccccccccccc s_103 6 fr_103) (cr_103 0) (hr_103 0) s_103 6 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_103_0 : treeBlockF 0 9 ch_103 = true := by decide +kernel
theorem nc_103 : ∀ i, 0 ≤ i → i < 9 → ch_103 i = true := (fun _ h1 h2 => treeBlockF_at nb_103_0 h1 h2)
theorem lb_103 : LowerBin 0xcccccccccccccccc s_103 0x440444044c044c 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_8 (kn_cons lb_23 (kn_nil)))) rc_103 nc_103 (by decide +kernel)

def m_104 : Nat := 0xf0f0f0f0f0f0f0f
def s_104 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_104 : Nat := 0x1070707070f070f
def huffman_104 : Nat := 0xfc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401
def fc_104_0 : Nat := 0x0
def ff_104_0 : Nat → Nat × Nat := unpackForestF fc_104_0 1 1
def ci_104_0 : Nat := 0x0
def cv_104_0 : Nat := 0x0
def hi_104_0 : Nat := 0x3
def hv_104_0 : Nat := 0x0
def cur_104_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_104_0 cv_104_0 1 1 1 1 1 1 1 1
def hint_104_0 : Nat → Nat := unpackCompressedHints huffman_104 1 hi_104_0 hv_104_0 2 1 1 1
def fr_104 (p : Nat) : Nat × Nat := ff_104_0 (p - 0)
def cr_104 (p : Nat) : List (Nat × Nat) := cur_104_0 (p - 0)
def hr_104 (p : Nat) : Nat := hint_104_0 (p - 0)
def bds_104 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 7, g_47), (m_27, s_27, 5, g_27), (m_41, s_41, 5, g_41)]
def ep_104 : Nat := 0x608000800000600000000000006000000080008000000000000000001020202020002000104040404000400
def ch_104 : Nat → Bool := dagCheckNodeV5 0xf0f0f0f0f0f0f0f 0x1070707070f070f ep_104 1 1 bds_104 0 (dagTraceF 0xf0f0f0f0f0f0f0f s_104 7 fr_104) cr_104 hr_104
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_104 : dagCheckRootsV5 0xf0f0f0f0f0f0f0f 0x1070707070f070f ep_104 1 1 0 bds_104 (dagTraceF 0xf0f0f0f0f0f0f0f s_104 7 fr_104) (cr_104 0) (hr_104 0) s_104 7 = true := by decide +kernel
theorem nc_104 : ∀ i, 0 ≤ i → i < 0 → ch_104 i = true := fun i _ hi => (Nat.not_lt_zero i hi).elim
theorem lb_104 : LowerBin 0xf0f0f0f0f0f0f0f s_104 0x1070707070f070f 8 :=
  lowerDagV5 (kn_cons lb_47 (kn_cons lb_27 (kn_cons lb_41 (kn_nil)))) rc_104 nc_104 (by decide +kernel)

def m_105 : Nat := 0xf0f0f0f0f0f0f0f0
def s_105 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_105 : Nat := 0x50107010501070
def huffman_105 : Nat := 0x84404822008330482200bf40482200833048220084404822008330482200bf4048220083304822
def fc_105_0 : Nat := 0x64f325dd42aa064752624a0c8601f
def ff_105_0 : Nat → Nat × Nat := unpackForestF fc_105_0 3 10
def ci_105_0 : Nat := 0x24489121d3870a8601
def cv_105_0 : Nat := 0x1b505540e4c24a224f792d247190c01f
def hi_105_0 : Nat := 0x214312f8189780423c0001ac51ad60006b0002f0a3402ebc00000
def hv_105_0 : Nat := 0x393caef84f62bfffc03ffc014abffeaa9551
def cur_105_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_105_0 cv_105_0 7 127 3 7 10 1023 14 16383
def hint_105_0 : Nat → Nat := unpackCompressedHints huffman_105 1 hi_105_0 hv_105_0 21 6 7 127
def fr_105 (p : Nat) : Nat × Nat := ff_105_0 (p - 0)
def cr_105 (p : Nat) : List (Nat × Nat) := cur_105_0 (p - 0)
def hr_105 (p : Nat) : Nat := hint_105_0 (p - 0)
def bds_105 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 5, g_35), (m_9, s_9, 4, g_9), (m_21, s_21, 4, g_21), (m_24, s_24, 4, g_24)]
def ep_105 : Nat := 0x1000000000001020000000200050006000400060000000000000000000001020100010200050104010501040
def ch_105 : Nat → Bool := dagCheckNodeV5 0xf0f0f0f0f0f0f0f0 0x50107010501070 ep_105 1 1 bds_105 9 (dagTraceF 0xf0f0f0f0f0f0f0f0 s_105 6 fr_105) cr_105 hr_105
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_105 : dagCheckRootsV5 0xf0f0f0f0f0f0f0f0 0x50107010501070 ep_105 1 1 9 bds_105 (dagTraceF 0xf0f0f0f0f0f0f0f0 s_105 6 fr_105) (cr_105 0) (hr_105 0) s_105 6 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_105_0 : treeBlockF 0 9 ch_105 = true := by decide +kernel
theorem nc_105 : ∀ i, 0 ≤ i → i < 9 → ch_105 i = true := (fun _ h1 h2 => treeBlockF_at nb_105_0 h1 h2)
theorem lb_105 : LowerBin 0xf0f0f0f0f0f0f0f0 s_105 0x50107010501070 7 :=
  lowerDagV5 (kn_cons lb_35 (kn_cons lb_9 (kn_cons lb_21 (kn_cons lb_24 (kn_nil))))) rc_105 nc_105 (by decide +kernel)

def m_109 : Nat := 0xffff0000ffff0000
def s_109 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_109 : Nat := 0x1570000175f0000
def huffman_109 : Nat := 0xfc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401
def fc_109_0 : Nat := 0x0
def ff_109_0 : Nat → Nat × Nat := unpackForestF fc_109_0 1 1
def ci_109_0 : Nat := 0x0
def cv_109_0 : Nat := 0x0
def hi_109_0 : Nat := 0x3
def hv_109_0 : Nat := 0x0
def cur_109_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_109_0 cv_109_0 1 1 1 1 1 1 1 1
def hint_109_0 : Nat → Nat := unpackCompressedHints huffman_109 1 hi_109_0 hv_109_0 2 1 1 1
def fr_109 (p : Nat) : Nat × Nat := ff_109_0 (p - 0)
def cr_109 (p : Nat) : List (Nat × Nat) := cur_109_0 (p - 0)
def hr_109 (p : Nat) : Nat := hint_109_0 (p - 0)
def bds_109 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 7, g_45), (m_47, s_47, 7, g_47), (m_36, s_36, 5, g_36)]
def ep_109 : Nat := 0x160800000000000000000000005600000048000001020000060a000001020000120000000154000014500000
def ch_109 : Nat → Bool := dagCheckNodeV5 0xffff0000ffff0000 0x1570000175f0000 ep_109 1 1 bds_109 0 (dagTraceF 0xffff0000ffff0000 s_109 7 fr_109) cr_109 hr_109
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_109 : dagCheckRootsV5 0xffff0000ffff0000 0x1570000175f0000 ep_109 1 1 0 bds_109 (dagTraceF 0xffff0000ffff0000 s_109 7 fr_109) (cr_109 0) (hr_109 0) s_109 7 = true := by decide +kernel
theorem nc_109 : ∀ i, 0 ≤ i → i < 0 → ch_109 i = true := fun i _ hi => (Nat.not_lt_zero i hi).elim
theorem lb_109 : LowerBin 0xffff0000ffff0000 s_109 0x1570000175f0000 8 :=
  lowerDagV5 (kn_cons lb_45 (kn_cons lb_47 (kn_cons lb_36 (kn_nil)))) rc_109 nc_109 (by decide +kernel)

def m_111 : Nat := 0xffffffff00000000
def s_111 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_111 : Nat := 0x157177700000000
def huffman_111 : Nat := 0xfc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401fc401
def fc_111_0 : Nat := 0x0
def ff_111_0 : Nat → Nat × Nat := unpackForestF fc_111_0 1 1
def ci_111_0 : Nat := 0x0
def cv_111_0 : Nat := 0x0
def hi_111_0 : Nat := 0x3
def hv_111_0 : Nat := 0x0
def cur_111_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_111_0 cv_111_0 1 1 1 1 1 1 1 1
def hint_111_0 : Nat → Nat := unpackCompressedHints huffman_111 1 hi_111_0 hv_111_0 2 1 1 1
def fr_111 (p : Nat) : Nat × Nat := ff_111_0 (p - 0)
def cr_111 (p : Nat) : List (Nat × Nat) := cur_111_0 (p - 0)
def hr_111 (p : Nat) : Nat := hint_111_0 (p - 0)
def bds_111 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28), (m_31, s_31, 7, g_31), (m_33, s_33, 5, g_33)]
def ep_111 : Nat := 0x1620000000000056006000000000010206000000000001021222000000000154144400000000
def ch_111 : Nat → Bool := dagCheckNodeV5 0xffffffff00000000 0x157177700000000 ep_111 1 1 bds_111 0 (dagTraceF 0xffffffff00000000 s_111 7 fr_111) cr_111 hr_111
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_111 : dagCheckRootsV5 0xffffffff00000000 0x157177700000000 ep_111 1 1 0 bds_111 (dagTraceF 0xffffffff00000000 s_111 7 fr_111) (cr_111 0) (hr_111 0) s_111 7 = true := by decide +kernel
theorem nc_111 : ∀ i, 0 ≤ i → i < 0 → ch_111 i = true := fun i _ hi => (Nat.not_lt_zero i hi).elim
theorem lb_111 : LowerBin 0xffffffff00000000 s_111 0x157177700000000 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_cons lb_31 (kn_cons lb_33 (kn_nil)))) rc_111 nc_111 (by decide +kernel)

def huffman_top : Nat := 0xd064fcc021502304c0211095fcc021d42304c020d064fcc021502304c02110a5fcc022142304c02
def fc_top_0 : Nat := 0x348402f5ac05eb180bc6b0178c602f14c05cb500c3430172cc0068e8054af00196a0132cc006548040b300815e0032940185a8030a500604e0030d400c5a80240a00314a0060cc00c13800c2d00206600308400205c0040980003f
def ff_top_0 : Nat → Nat × Nat := unpackForestF fc_top_0 12 11
def ci_top_0 : Nat := 0xd406a03501a80d20e903481a01c23e102f07780ba0dd02e81644b205902c81583ac05602a83540aa051128814017a9bd000f8001
def cv_top_0 : Nat := 0x60bb00c34301ead603b58c0723580dc6301a8a60325a805cb300a95e00e0d401416804cb30089660102bc01a1a80202d00716a00d2940181380240a00516a00829400e19801827002066075ad60e358c1ba358354630658a60c2dbc151b3827b5f04a69e0869a80c52900fa420164740285a8048a900794a00b0d400a16800c2140f45f80f8b700d15df8e29beeb5f7ca6b6f72d5de59a9bc8b4f78b696efed1dca1a1b83a5f6c24b6ad295d4dd29a7fa4f4e749696a91d24521a21a3f42b4767ce8dcf0d199d515f3a52b66f855cde0a99ab14f35429666051ccaca198c13f3062765524dca649993392f25025648249c8c89190c85f20f0b63cc15c778298e584f1b10962a811c4f42188d03f1180761e80dc3bc1985e82f0a605612e09c2201184001f07803600405c0040980003f
def hi_top_0 : Nat := 0xc2730b797a25f562d72c2e958257d60a992f35d4436877a84416214cfda1c69153e4551436f73a0d4cad93db7ddf9740f5bb0d9d6d72596edee62f9391a5580f438ca29636c5284dee7215f95d53d031ade714c145ccc3c4b31601b5c3249b7bb43d0e46145abeefb0749ae0708031b4800066800000000000000000
def hv_top_0 : Nat := (Nat.lor 0xacd20b05009b764dff25dddc82f0f229fe7f1fff3e4fff92cbb65da5524a87771e33779dbbcdcceeee5ddc8cd32964ac5dbb2e9360a4d56b355aad82ab49acd26ff92eeee7bfbffbfffffbc8a7ffcf93ffe40b2e825441740f00f3b70730ee177720164ac5dbb2e803359a4160a07f92eeee43bff83c8a7f87ffcf93ffe6d2b189532976971e33771dbbcdcceeee5ddc8cd0690cbb765db416ccd66b352b0582d99b6ff25dddcf7affefef22ffff9fff3e4fff90ca30669742e8c6cd0f9c78f1e23b8eeeeeeee5dcc160b0566d868699b666934bb65db66937b98aef3777777773fcffffffff3fe7fffffffbffffffc68db416c194ce45f82c159a3505b0d416c1946176e0a4d2edc149a194ba17463ff27f81c7b8e3c78f17725ddc8ee3bbbbbbb9773fe4fff93fcffffffff3fe7fffc632e974ba31f1e3c78f1e2ef3777777779bbcdddc977777260a3360acd20b61a1a66da0a4d2ed976d9a4dfff24bbbbbbb9ffefffffeffffffffe27ffffc9ffffff24fffff907643077770c6305d2e834865db2e976cba74c1a5d3e33e33e9f07f87fffffffffffffffffcfffcf1ff9febffffc7e45fffffffff1fffff8fffc4a8c0ba5d0ba31974e993e1f4fa7c1fe1ffffffffff3fff777318c6318d66b31898c63fe63ffcffffffffff2efffffcfffffffffcde6318c3bbbb831b832ed974bb65d0ba5d2e9741a439f19f127d39834ba7d3e0ffff1f8c3ffc3cffffffffff9fffff8fc8bfffe78ffcff5fffffffe3fffff1fffa1a1974ba5d2e8d21cfa7c34ba7d3ef3ffcff5fffffffe5dff9fff98c6319ddcc6b3598c4c631ff37f8fffffd7fffffff8fffffc7ffffe6f22ffffddd8d2b61bf6c25463bbbb85bdd977773e33e274c9f0faeeecfffff3ffcfffffffffff9fffff997c8bfffe7997fcff32ffffffffdfffffcfffd0d0ed6b58cb6bbbbbbbbb4adddd3bbcfa7c34ba7c67c6eeefffffffffffffffffffffeffe7ffffe3fffff5ffffe3f22fffffffffdfffff8fffc6951a56eeeeeeee7d3e9f0faeeefffffffffffffeffe7fff7777777776eef66eecffdfffffffffffffffdfffffcfffffefc8bfffe0000318c601dddddddc001e1ffffffffffdffe0e6198c6318d66b31898c63fe60f229151151148a5d229148a45229229148a7fc8bfeee7fff83185d97776771dddd77767f9ffffffffffdffe5dd994b1ddddbbbd9bbb3ff7ffe4522a22a22dddddd9149148a453fe45bbb22916eeec18c0ba4db2e963b19fffe0c686864522914ee3bbbbaefbb8f710ff0ffffffffffffffffffefff1cbaee3bbbb8ddedddddcbae6777777777eff706305e97418c633b8eeeeeeee0ff0ffffffffffefff1ddc777771bbbbbbbbbbf7fbfff9148a88a88a45229148a45229229148a7fc8aeeeeeee453090174ba2491dc24977771fe7ffffffffff7ffbbba49246359acc626318ff9849254fff45d49245247fd23232492492bbbb492eeee492bbbbffffffffffffffefff66b359acd4ab37ffd3bbae3ddc7fcda9257776925dddc9257777ffffffffffffffdfff777665b49249ddecddd9ffb4924aafff569248a48ffa49256924bffffc17a41752a4d2ebd49a194ba249771ee2770925dddc7ffff9ffe7fffffffffff7ffbba55cceeee3a55dc777774ee9577777777eff7492b2ed97524979349a4d26b349abffffd25dddc925d77ddc7b8fffffffffaffffffffffffffefff772ebbbbbbbba77b777772eb99ddddddddfbfdd248bab52ead524bbbb924bbbbbffffffffd7ffffff7ffbbbbbbbbbba7777777777eff74925ffe92491491ff4ee8ceeeee452291468634306318c3ffffc2e977c2ed8ec7dc7b89dddc777775df07fff977cba1ffe1e7ffffffffff7ffbb975cceeee3975dc777771bbdbbbbbbbbf7fb8c631d976cbb63b1f777777775df79ffe7ffff8ffeffffffbffddcbaeeeeeeee377b77777777eff7229148a45229148a88a88bffe4524522914ff915dc8a67777718cba5d2e8c7ddc3ee2ef79fffe7ffaffffffbffff3fffe5dddddddddddddddddddfbfdffffffffffffffffffffe7fffffffeff5518c632e974ba5d18c63eeeeeeeeeeee73399cce673399cce6f22f917c8be45f22f917c8be45ff77f7faa98318c553061991918c62a9acd6631898c6e31fff777 (Nat.shiftLeft 0x10d0905ad6d2bddc78cddc6eeeef3734dcbbb90ca650690ed05b2559acd4ac160b666d89b764dff25dddcf7affef22ffffff1fff3e4fff9010c060b5b03c038c1cc3b9372eee400690c019 12288))
def cur_top_0 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_0 cv_top_0 13 8191 6 63 11 2047 23 8388607
def hint_top_0 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_0 hv_top_0 31 7 10 1023
def fc_top_1 : Nat := 0x3e68a07c5100ca3181936f03a2fc0745f00c9b381c47603269e0645980ce35819b430334cc0644d800d29018355020ad605c5700b1aa816154020ac6040dbc0a0bf01417c0206ce04d5d8081af810166021ad6042d4c08533010136
def ff_top_1 : Nat → Nat × Nat := unpackForestF fc_top_1 12 11
def ci_top_1 : Nat := 0x8c42a1108843cde0e9743a1d0e869a7d308a442050072381c0e05b2c144a050281407607
def cv_top_1 : Nat := 0x1fb457c511d97e745f19934711d9ac6b68d0d9a66831adec6378dbdcb676ed3db166644d98355464d9715c5ad556154525f9417c424d13576475ad1353429997d6b5758d536f4ed9d2b5f485990136
def hi_top_1 : Nat := 0xe13ab2d76411d07d1049403424100ecd19c1bf0595977bfe880bed492959a576e7da8963863a0b880d2736787c8d0707edf8bb9db7c6880e1bfb45906fe80001b563452683ab2918011d07575c94555b210125351c1bd16359b943d080dce2d296428cee7f498e38522500809c808789c106f07dc001ba0d
def hv_top_1 : Nat := 0x2cba32e807805dbb2ea34a34bbbbbb8dd7affff1ffff8165d19740620ba04771dc00ff2edd97402d62c01b234bbbbfaffff19fe7afffff00681ab60ec1e038771dc0002d62c6503fc9b7763dc5dddcff3d7ffff7afffffb07884ff5f64db268ec10bbbbffffff123486ac3b5b56daa3b0043ceeeef3733bdad6b196c65b5ac58ca7f936eec78f758bbbbffffff7917d7ffff7afffff46d90b60cbfed52e8cba3541a4326cf59bb7777772c653fcbb765d26d89b6b590b642dad63dc5dddfd7ffff7ffffafffffb5ac1ffe7f831f832ed9949a5db329342e994ba5d0690cca65e26532f138ca0d2e32f1779dddddddc6e8771dddddddddddffffffffcff3fffffffffffffffcba6509b64d56ab49a5d28d33934ba5db25d339231d876bb2c5811a234779b9bf97ff21a1974ba8d1a434688d32a34ca8d3fc9f3fe8d26976cbb64de3dc7867cf71ee2e9eb73bbbbbbbbbbbbbbbbbbb97772ffffffebffffffffbfffffffcff9ffff43432e974686876ee1a5dc5de777777777777777777b16b5ac7ffd89a5db2eddadc6d6b7177777777fffffff5fffffffffe3fffffffffff5ffffffee6526b749a51ae21a12018ecbb65d368cda4b8dddddedddc269941936c90d0ec4db1349a4d36935bb626dbfc934bdbbbbbf8fc8bffffffffff64d7339351a4d28d7f228086003486319e08d28d2e377777b777ffff1fdff8086030630bb604718ee3dbbb800d21801349a1340ff24d4697b777773fcffffff00da80bb61749a1e038771e6f6eee00004d2684d328164adfe7b8bdbbbbb9fe7fffff9343c422b2b7fdf9749a10bbbbbcffffc946d46d2edd976c9a5d269749a010f3bbbbcdccf37b777269349a4d32934ca4d2693426994b256ff3c7b89a5edddddffffffbc8bfffffee8d269d49a195cda30da1231d976cba8f22938dddddedddc269941a43b136c4d26934ea4d3ad89b6ff3dc5edddddffffffffffc9a4d268d196c3465b03328c607ff9fe174bbe176c765d329978994cbc4e32865e1f176ef9dddddddc771dddddddddddffffffffcbbf67f9fffffffffffffffe33296566eb76c328d22fd86344645f2522e9749a5d2684d09a08d11a3cde76fffde4518d1b65db2ed8ecba8d11a65469951a236c34356ff27cfff1ee3c7b8678ba7cf71379dddddddde6ef6eeeeeeeeeee5dcffffffffffffffffffff9fff3ffffe31d976cbb65d1d9749bddc3e2eddf3bbbbbbbb975ddedddddddddc9a1349a4d2684db0d0d136dfffc49a4d26f177b77777777ffffffffffffffffffffffffffffff
def cur_top_1 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_1 cv_top_1 9 511 3 7 11 2047 18 262143
def hint_top_1 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_1 hv_top_1 30 7 10 1023
def fc_top_2 : Nat := 0x55ae60bc9201563982d48c05a6880b49201562982bd710578e20aa9c815538001b67050aec0a11ec142398282580036be0979ec12f39825c7604b490006d3c125a28224530446be088d3c116298221360034d4084d140ca3582014c
def ff_top_2 : Nat → Nat × Nat := unpackForestF fc_top_2 12 11
def ci_top_2 : Nat := 0xa026298260982338c23084a1066181601806012648120445102d8b02489024090204350c01204001
def cv_top_2 : Nat := 0xaea02f248b9232db44b4922c571af1c6fd73bb1cecc53329e2b272aa9c1ca524e9093242a75da947ba31ce3a7aa09612a427094a767b9b9ce64768c9e9ba62969224b458a4da2c539114e3b5f8cd3cc93a884da13456a4da014c
def hi_top_2 : Nat := 0x8284282980b454747f9034497ef824267e04243d7b5880ab7ab824287a10242a7648e8f26eb1d1e6635ac2d65d9159725b6c5c895974647e51b1b9f145dad2f643c45c8541a864873bb1597e340db9e927b6d31626c8203b216d15571c75053e1725055416182c430f31a1ba080199cc074020300115458b0114000000003445
def hv_top_2 : Nat := 0x39e7fff7fde4d2edf7997ec9bfe4d7999ffbc8bdecdf66ab5935cde45eb1343fdff95ac9bc9566a559aad64d1d8cb60cbc7d9becd56b26ffd9cc67f22917fbacbd7f917f8ce4dbfbff246651974ca5d00879ddde6ef3fff092c9589b764d205dddfffffbffbfffc328c19a5d0ba31b343e71e3c788f3771dddde6eeee5dc813e419b61a1a66d99a4d2ed976d9a4d243c25dddddddcfeff3fffffffff8ff9ffffffffffff248d1952a34950ca30bb6655a976d6a194ba17463000903dc78f1e3ffffe65fffffff0f32ff87ffaffffffbfff27fbfc97777777779b9879bb8eeeef3779bbb92ee4ffbffffffffff7914feff3ffbffffffff89ff27fffffffdffad608463b26d93508eefff3af9d7ffe4becd0cbe7af1fdf9ef2f3733bbbcddc73727dffbc8bffffdebff89ffff7fe2ed89b25b77b37edf4df2699cce45ff22f176cac494ef66fd8a6f86733917c8bfc86865d669759a3487c78f9478f17777777771bbbb9772750ea753aa54ea79ffff24ea4d2ed976cea4d252ff25dddddddffffffffffffcff9ffffffffffff434aa18e4a592b25b0492e974690cbb66d5a976ec95e3c4a3c91292e3c7cffff3ffd7ff8fffffcebffffff6fb7ffdfff93fdfe4bbcddddddddc6eef3733bbbbbbbcdddc97727fdfffbffffd7ffffff7917fffffffffff89ff27fffffffdff87626c36ddecdfb7d37c9ae633917c8bfc326d84d869c337cfa6f934ce6722f917f89a4d5656084ba5db2ceefff42fa17ffe1becd0cbe7affbf2e9ef2f3733bbbcdde76e4fbff7917ffffbfbff89ffff7fe1d3474db2ed976c765de3c78f1f365dddddddddddcbb94288542a14ca8510b61a1a42dbcffff924ddff92eeeeeeeffffffffffffffc7fcffffffffffff8c765d5ad974bb63b2ec3426ad61a4d21a951a1a26a5493c78f1e26cf5d93777e7fff9ffebfffffefffcbbffffe85ffffff26f9349feff25de6eeeeeeef377b7777779b99dddddc97727fdfffbfffffbffffffffbfffbc8bfffffe4ff93fffffffeffc6518acd62b34a36d2b189532976925497772eb99dddffc690cbb765db316ccd66b352ac562d99b62cd23b9ffe3f22fffff9e2546254ca136b5b4aa3c8a4eeeeeffe3487662d8eacd3a9d58ac5b336c4dbb269ee23b9ffffffe78652e86532895492a4d9eb376eeeeefff64ac5dbb2e9358a4d42b350a8562b149acd269ee23b9ffffffe783b1958b628d33917c628c18a5d0ba3187fff8316c3434c5b3149a5db2edb149a1ee629c78f1e3cc5e1dc777777777707770bb93fcffffffffff0fff0ff9ffff0ca30329742e8c67194e1f7177877771dddddddddddfffd8b61a1a66d98a4d2ed976d9a4de2cd62f10777770ffff3fffffffffffffffffc3ffc32d95b628dff2cbb60cbb7634860d52eb5497772eb99dddcb194ff2ed89b765db2e936c4db5acadb2b6d6b1b17777f5fffe3fffff5ffffeace6b236c51bfe45f
def cur_top_2 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_2 cv_top_2 10 1023 4 15 11 2047 18 262143
def hint_top_2 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_2 hv_top_2 32 8 10 1023
def fc_top_3 : Nat := 0x7f0880f31ac1f42203cc630790cc0f4d981e42700081b0766aa0ec96000eb583a2520726aa0e496000eb1837b4506f4900071ac1b521035b4506b49000718c19a3b03424206668a0cc92000e298322480628a60c49a000db7830258
def ff_top_3 : Nat → Nat × Nat := unpackForestF fc_top_3 12 11
def ci_top_3 : Nat := 0xcce632390c8626d961b04f6712a94415f2f86ab4184c04ea613083390fc7031180502002
def cv_top_3 : Nat := 0xfe113e844f4d9bf46bf918fd866f21398242eed56734fec9617a423c8eba2525a90b9b559ad3f925856908ea3a8498a936fe0d160a62de920e23a7e98b6a42a2dbf63457a98b5a48368eadb76929eb4242c8dbed367d31db1b7fb2ddf3b45909eb3248348eb2248c714f1268789495242b0a030258
def hi_top_3 : Nat := 0xc842b716c185c9afb7feae62b019b5f9a841b1f6a021aa08981daa01924959758a29de087e16d7057df00c0977d58d877119c1af680ece436229597959f5de0d4d0ed73a4ce80c0946d58d854011c1b13682ce642f398dd22f0c0c0b28ad81982095ca06140ee722134c2430112870890b09b188022ad2380188282800005462
def hv_top_3 : Nat := (Nat.lor 0x777775df004e0007777777701c707777000f22917c645f2adf9148a00452287f87f117c8a45f7f2effbb800038dddd3bb975ddeddc001dc1c01cbbbf39fff733bbb8d0c6343183185db82934bb6f5268652e8318c7ddc7bb89dc777777773fb9fe03bbb8eeeeeeeeeeee0637845304522f845f22f917c8be45f22f917fdffdc9a4d268d0c6343183180eee3b85d2eb85db1d8fbb8f7713b8eeeeebbe777777771dc777777777777f2aff9148bfe452291422f9e45f22fdf917c8be45f7f718c63b2ed976c7632684d269349a0c6343431bbbf777777775df7771eee2eeeeeeeeeeeeeffeeefeeeeeefe45f22f917c8bf645f22917fc8a6ff3297c8be45f7f718c632e9746318fbbbbbbbbbbb9dddddddddddddddfc8a45f2a917c8a45f1917caa45f22917f88be4522fbfd57fdddc77771c6eee9dddddedddcbbbf39fff733890125936c9bc651f5b832f9ebc7ffe65f66fff997d9bf7e7bccddc6eeeef3734dc9f7ef5ffffffde45fe27fffdff8f40cd2e8348671941a5ccde2ef0ecd771ddddc6eeeeeeee097f879fffe0cd26976cbb6cd26f166b359a95e2ef6777777773c7fe7ffffffff8ffffffffffffffffc10d204900194ba0d21976cdab52edd92a71941a5521f592bc52bc78bbc1e65ff0fff5ffe3fffff4affffffdbedfff7fffe7fffc8e95771ddddc6eeeeeeeef6733ba55dddddddfbfdcf1ff9febfffffc7e45fffffffffff1fffff8ffffffffdfc7e4000193d64db2680f838ba01ebc7ffe8df66ffffb37efcf9efff20e3777779b9a6e5ddcfb82ffffffef22ff1fff3fffeffc000034860034b99bc5de00777771bbb35ddddddc0003fffffc6362934bb65db629378b159ac562f10770000ffffffffffffff3ffc0000010c006000d2180b52c0006970040e2ef00007ffafff1800787f807ffdffff9ffff2000eeeee3007303b83ba55dddddddfbfdc003fd7ff8079143fc3ffffc7ffffe3ffffffff7f1976592b049ced2ef137876f9ebfefcbbffeadf56fffbb7d9a7bccdde76eeeeef37313efdfdffdfffffde4527fffdff8568c3ecb1d974e5694de1f176ef872ebb8eeeee5d777777770bbff056d868695b6f3fffc38ab55aad5af1777777773d5bfe7ffffffff977ffffffffffc9bffffffe194605976ec2c765dbbb76a5468689a9500e329c3e2ead6ecbbc4d5af176f10f32ff87ffaffffffbfff2efffffab7fffffc9be4df3fffe472ebb8eeeee5d77b7777772eb99ddddddddddfbfdcf5eff9feb5ffffffff2efffffffff937c8bfffff3ffffffff7f2ef90002c958ba4f070cbbc001ebfefcbbffe8df66ffffb34f9efff20f3b7777779b98bbb9f70effefffffef229fff3fffeffc000163b2e8053787c5dbbe00777777777777000062d868698b6ffffff2e9778b159ac562f10770000ff66ffffffff977fffffcfff00000000b2ed8ecba009501005d00387c5dbbe00800001ffebfffffefffcba001e1fe01e7fffc8003bbbb975dedddc01cc0ee0eeeefdfee001feb5ffffffff2e8079143fc3ffffe7fffffffefe5db58b2c63108ba5d32932932997ffccbecdfff32fb34f0cbffe7af1fdf974997cb975cceeeee5d77771dbbf7bf8fc8bffffe3fff5fe3f1ffffbf8fcf86532964da2570f8bbd6e3cf5e3fbf2efffa37d9bfffecd3e7bffccddc76eeeeef37317773efdebffbfffffbc8a7ffcffffbff21a1d976cbb697f70d2e2eddf3b975dddddddc6eeeeeeeecd19acd66a559a7fffffddffffffa5c59acd66a578bbbbbbbbff8ffffffffffffc7fffffffffffffffe868765db2edda4958d2a592a95b177692ee1a5c5dbbeb2578a578f9fffe7ffaf5ffe3fb7ffdfdfff977c9bffffe95ffffffb7dbcffff9772ebbbbbbbb8ddeddddddcbae677777777777eff7ff1fffffaffffffff1fff8fc8bffffffffffe3ffffffff7f1f19c66a5422f8c3296329c337c56b26ffd8ce6722f917f80000ba31b34038f1e3c401dddddddcbb9000062d868698b662934bb65db629349eeff241dc0003fffffffcff9ff3ffc000000012a2000016a581746303c001dc78f1e20000001e1fe01ffebfffffefffc9feff2400001cc0ee0eeeef3779bbb92ee4ffb8000079143fc3ffbffffffff89ff27fffffffdffb9e7ffe9ffac35de65f56ffb3cdcdfc45fe (Nat.shiftLeft 0x18c0b2edd858ec7776318d0d0c601dc7777775df77771eee23b8eeeeeeeeeeeeeeeeeeee1148be553c8a45f1917cab7e4522f957fc8a45ff229148a45fe22f9148befe5dff77077732838dddd3bb975ddedddc9ae4d7777756bbbbbb9777e73ffee670000b1d8c0000631a1a18cba5d77777700eeeeebbeeee3ddc401dddddddc03fc1dddc03c8a45f1917cab7e4522818c01e45f22ff9fee0000165db1d8c0060200ba00 12288))
def cur_top_3 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_3 cv_top_3 9 511 3 7 11 2047 18 262143
def hint_top_3 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_3 hv_top_3 32 8 10 1023
def fc_top_4 : Nat := 0x988d613119c275a984e2440988c613117c2652204c45300104e12c1902263784a0440898d61241f0226338480440898c611ad74235aa84486608a8cc114d98224270008230872a81035ac214aa040d630812cc105198204af00081f
def ff_top_4 : Nat → Nat × Nat := unpackForestF fc_top_4 12 11
def ci_top_4 : Nat := 0x8c23088611842108058860162581515412348111441103c8f03c0d21d87018460144501404101000
def cv_top_4 : Nat := 0x13ad4e71224ca44a5ad74358e8237cfc6b9e8cf3718e6a2fcc4538e0e92c19250224907c8d0c91613240224735d8d6ab1719a29b34ac6f938d72319e3e31c60668909d0e55214aa4146686ad70958e0cb34095e
def hi_top_4 : Nat := 0xf40ab2b1f3901c1eed11b1a0e3feb645d952aaabd161adfcc592b6f4be9591bfb849c993b03e9203a90db9cc9e1e9ebc96adcddc8c62b693853de1c97cf286137775715f7061a9c567f5be1b610591bc58ddc20a5005be36494989af417dd5f335deb6e82f41c9a7267aae321ec1b5ee1775b1d30fb5a9f007f5a9f00001d5fd
def hv_top_4 : Nat := (Nat.lor 0xffffffff1249ff27eabfffe00000034318d0c6000493764dddd800120049249200557998aaf330c631dddd9248001148a01e45f22fdfd92493c8a45f9914000006200baa8005dddd8000420492492000187018c63bbbb24900008a787917c8bf7f64924fd57c8a45f9914000080001204008c92893649b24924c49724914831859bb2c763026ec0631a1a18c0924812124924924924932a8318c655bb9955e662abccc492117cf22f917efc8bfe4522ff9148a493e45f2283181755bb0b1d8eeec631a1a18c00909249249249249265506318cab7732abccc55799892422f9e45f22fdf917fc8a45ff229149249faaf9148bf3228124ca0464944926926926cd9249a49a49255a4924924c49724914a149a0480d0c634318318049092c9777649249212124924955e662abccc4caa0c631dddd924fdffddff9148a4508be7917c8bf7f64924f9148bf322ddb56d5ddab18318005d85d56eeec9249242424924926deeedecc4caa0c631dddd924fdffddffdd9148a117cf22f917efec9249faaf9148bf3229b24926cd9248109265204649449b249b3649249892e4922900000baa963b180000c63434319349a4924801249248120000318c655bb9955e662abccc49201e45f22fdf91408a450024927eaa79148bf322800005d56c76300180806a8004924920108000c631956ee60187024900f22f917efc8a0114f024927eabe4522fcc8a0000464944926926c9000240801249892e492291ea0c631801bbbbb0bbbbb080100924924ab32acc006318eeeec92422801140f22f917efec9249e4522fcc8b7649249bbbb18c6302eeecdbd6c9b7776492484924924926eeecab32acc6318eeeec927eeefeec8a4508be45f22f917efec9249f22917e645248d0c634318318f5b32934cb6f526865328318c60490909212492492abccc557998995418c632accab3249022917c2291422917c22f917c8be45f2292493e4522fcc8b764dbbbb0632ec9a04d2690268318c649248484924924dddd932a8318c65599566493f777f764522845f3c8be45fbf2292493e4522fcc8a4d2693468631a18c18c0248484d26909b63b1924924848492492557998aaf33132a8318c655bb9924fa17fc8a45ff229148a117cf22f917efc8a4924f9148bf3228c631d9349b64db1d8c9a1349a4d268318d0d0c64924924924924924924ab32acc6318cab7732abccc5579a94927c8be45f22f917ec8be4522ff9148bfe452292493e4522fcc8a318c6318c64924924925599566318c65599566493e45f22f917c8be45f2292493f55f22917e64521248464944924d92492624b9248a4f407fa401ffffe05d2e834865db2e974bb65d2e9d306974e7c673e33e9f063395471a7319caae633b98c63399cce6731fe7fffffffffffffffffffffbfff821a4092002e9741a432ed974ba5db2e974e9839a43e9cf8ce7c67d3e0c672a8e34e633955dcc677318c67319caa67e3398c1ffe650f1fffafffb7dbffffcdbfffffe5dfffbfff3fff3f3e6f3fcfffffffffffffffffffff7f1fffffff8000000c7fffffe0034865db2e974bb65d2e800d2e9cf8ce7c67d3e0071a73180c6007319caa67339803fffc03fc3fffffffcf7fff0004300180034860174b0001a5c012613e9f00038d398c006303b8398ce5533f19cc60000f1fffaff000ff0f00f2efffdfff9fff9f9f37807fff81e787ffffffffbf8ffffffffffc68cb61a7ed8328c2ed974ba5db2e9742e9742e8c65d9cf8ce7c4e993e1f4fa7c063386306338673399cce67339bffcff03fffcffffffffffffff7fffb5ac1ffe7f831f832ed974ba5db2e9742e9741a439cf8ce7c4e9834ba7d3e71bb98cee6318338e9cce673399cdfffffffe7f9fffffffffffffffe868762d6b58fff2e974ba5d1a432ed974ba5db2e9767d3e1a5d39f19cf8cfa7ce6733a3398cee633b993ae673399cdfffffffffffffffffffffffffffffe31974ba5d2e974632ecfa7d3e1f4fa7ce633954ce553398ce633954cfc6731bcffff3fffd7ff977ffefffcfffcfcf9bfffffffffffffffffdfeabffffffe0c60f658ec60ef760318d0d0c60eeeee1dc777775df7771eee23b8eeeeeeeefeeffeeeeeee1148be553c8be45f2adf9148be55f31bfc8a4531bc8be45ff7ff7 (Nat.shiftLeft 0x5d996d5ddab4a86518005d85d56eeefffffefefffffeff83fbfc3ffd7fff7ffdfffddf13764878e3c6f8dd9ff22dbdddbd982a9542a8c655bbbbf7fffff31ee3fffffffff7e453fbfcffeffffffffb2493fe4fd57fffc671c45f00000b1d934011a31934df0007faffffffffe0ff00000aa31954ab76552a954aa55f7ffff000ffeffffffffeffff3fbc8a49ffff00000baad8ec9a009501006500003ffd7fff7ffdffff0007f07f800071e3c6c80121c1fe45002a8c6552add954030e1efffffe63dc4003ffbffffffff803c8a1fe04927fc9faaffffa1a1d977665b2c777776958d2bb4979fdffe7ffafffefffffbfefffffbfbfffbfffbe3c78a3764df1366cff914aa552a954690edecd6f777777efffffe63dc7ffbffffd7fffffdf917ffffffffffec924ff93e3ffff4343b26d936d2f46a351a8db2b91beffeffffffffefffffeffffffef4e954aa552a8d21956ecaa552a954abefffffffdffffebffffffffbffffffbc8a49ffff4343b26d936ed24ac6952c954a996c5dda4bcfefff3ffd7fff7ffdffff7fffff7f7fffff7f71e3c51e367b8f13c95e27fc8a552a954aa348655bb2a955caa62ab954defffffe63dc7ffbffffd7ffffffff7fff7917fffffc924ff93e3ffff18c63f3fbffcfff5fffdfff7fffdc78f1e3c78ff914aa552a954aa31954aa552a957dfffffcc7b8fff7fffff7 12288))
def cur_top_4 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_4 cv_top_4 10 1023 4 15 11 2047 19 524287
def hint_top_4 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_4 hv_top_4 32 8 10 1023
def fc_top_5 : Nat := 0xbf6cc17c9380041785e0640a78de17411029e3585c07c0a78ce16c11029e3185a3610a72cc1641b02c5b305394e0a70cc15cd9829c2705382c0a86be150d6c2a1ab8543530a70480020ac262b5851b4f0a3686144950262b184c46f
def ff_top_5 : Nat → Nat × Nat := unpackForestF fc_top_5 12 11
def ci_top_5 : Nat := 0xa15db741b26c192641725c152541415013148520481114411044110440d40e8300c0300480100000
def cv_top_5 : Nat := 0x61d6bc2ac78319b022f5fb66edad7c958f8a37f046bde8cfb318f5e2fe7453c84cd8897af9275e064ab04974112a8125c07ca90496c112a0125a361b20d962d9ab9b355b5faa6b752d5ea1a9ddc6fb98d76f19ed631d9966b029d5e19ab4275602ca704948d3e8da1d1254
def hi_top_5 : Nat := 0xf119c228eb2d757be535b17edb0ab28bd299d61cc3aebbbbbb85e60aaecebb2ea7b1c9c79cc6b2bb93dd9e3a8c5975e188bcf0e77fc9a23d77a1860a6f35ae1b666dc2325db5aa2e58ecf1325341c96b4b2dd20543d5d1d63dd1c98138f101382fb19a502472b2d023f01c20233024301ce9ad92142eb62f0b8aaa290002b2e2
def hv_top_5 : Nat := (Nat.lor 0xccc557998995418c63bbbb3dc7effecff92422917e0a79148be322fddfdd937e4f917c8b76d5b5776ac60c6001761755bbbbbe26ec90f1c78df1bb36f776f66265506318eeeecf71fbffbbffbb2291422917cca79148be322fddfdd93f3dff27c8be45bb22dddddddddd9148a04522914ca04519151151148b77777777ffe453114ba45722b9148a624800058ec60000318d0d0c64d26dddd9148a01c78f1b201fe000318c655bb9955e662abccc7b88079148be322f936fc8a4502400f9fe7c8be4500000baad8ec60030100d50038f1e3640270000c631956ee6018703dc4003c8a45f1917c9b7e4522801148a1fe04fd57fc9f22f91400008a322a22a229148a4dbbbb229140008a45022807ff914c452e915c8ae452298920c604d26dbd4b18ec6308a452291418d0d0fffc3c71e3c6cf13c48552a8318c655bb2a954aa552a9ee20452281148a45229148b7645229148b64522917ffc8a4522b915c8a5522ff917d7fff8319ffffe194ca0c631f93e4878e3c78f1ffff0aa5506318caa552a954f71ff2281148a045229148a45229148bffe4522915c8ae452a914006318c002280058ec7e7c8071e3c6c954aa552a800c631956ecaa7b8fff8d0c6860c604522d9148a1349b6136c763e27890f1c78f1b2552a954aa154aa0c631956ecaa7b8915ca45229148a004508a452281148a4522916ec8bffe4522915c8ae452a9146318ec9b64db1d8fffffffffd7f917f8f1e3c78d9f27c92a954aa5518c632add957fffcf712284522914228c8a45229148b777645ff22fff9148a45722b914aa45229148a34318d0c60c63d6e0a4d82dbd49a194ca0c631f793fc0e3dc71e3c78955e662abccc4caa0c63195665599ee204f84521148be117c8be45f22f914917cf917c8a4d2693468631a18c18c022916c2291426936c26d8ec7dc4f7121e38f1ee37c4aaf33155e66265506318cab7733dc7d9bfe4522ff9148a453c8bfe7917c8bf7e45245f3e45f228c631d936c9b63b1934269349a4d0631a1a18c8a4522f1e3c78f71be3fe4f7925599566318c655bb9955e662abcd4a7b8f917c8be45f22fd917c8a45ff229ff24917cf917c8a318c65d2e974ba318c7c78f1e3c7898c6318c6318c631f31f22f917c8be45f22f914917cf9bc800000c401755000bbbbb00009c1c78d9b200038e0eeeeeeee5fc800001148a1fe1e4522f8c8bf77f7649e4f9f706302eab76163b1ddd8c6343431801e38f1ee37c7b89ee24771dddddddddddddddcbf908a45f2a9e4522f8c8be55bf22917cabfe4522ff9148a45229245f27cfbddb56d5ddab18318005d85d56eeeef89bb243c71e37c6ecbbbbbbbb8ee3bbbbbbb97f3f7ff77ff76452284522f954f22917c645fbbfbb26fc9f3ee00001755b1d8c0060201aa0071e3c6c804e0007777777701c702fe4003c8a45f1917cab7e4522801148a1fe049e4f9f718c6318c63e3c78f1e3c5dddddddddddcbf9f22917caa45f22917c645f2a917c8a45248be4f9f718c6318c63e3c78f1e3c4ab32acc6318cab32accf71f22917c8be4522f8c8be45f229149faaff93e45f22914229148a4508a322a22a229148a45b22d9148bffe4531148ae45722914c4904348124006532834876b4ac552b764a87f7f87ffafffefffffefefffffefefffbfffe0f1dc571ee27b89e3c7fc8a154aa0d21955caa62ab954c552a954abefffffe63dc4feff3fd7ffffff7917fffffffffff8924ff93e3ffff4681c45f469c4cabde4500000195c0034868d468007fffff07f801ff7ffe003486552a954aa552a954abeffffe001febffffffcfef22ffffff127fffc0010c006000d2181152c00003ffd7fff0007f07f807ffdffff0071440090e0e3c7fc8a003486018702a954aa55f7fffff31ee2001febffc03c8a1fe1fffffc4927fc9f1ffff80000254401755000bbbbb0000000fe0ff00fff5fffdfff7fff600013838f1b367fc8a00018702a8c655bbbbf7fffff31ee200001e450ff0ffeffffffffb2493fe4fd57fffc328c0baadd858ec9b776d54a8d0d1352a007f7f87ffafffefffbfffefffffefefffffefe0f1c78f71be3dc4f713fe450aa550aa31954ab76552ab954c5572a9bdfffffcc7b89fdfe7ff7ffffffff7fffffffff7914924ff93f55ffff (Nat.shiftLeft 0x63b26936c9b63b269349a1349a4d2684db0d0d136c4924924924924924924aa552a954aa31954aa55bb2a954aae553155caaa5249ffffffffffffffffffffff24927ffbffc6318c9249249248492124a24926c924954aa552a954632a954aa552a924924c5c9ffffffffffff27eaa4924ffff7ff8000000d0c63431805ddddddddddd80007f871e366c80155e662abccc318c777767b88001201e45f22fdfd93cf917c8a0000031005d54002eeeec00027071e366c800061c06318eeeecf7100000229143fc3c8a45f1917eefeec9f9eff93e45f2280000001148a04500228c8a88a88a45bbbbbbbbfff22988a5d22b915c8a45312418c08b658ec6045bbb018c6868630bbbb2281e38f1ee37c7bc9ff24995418c632addccaaf33155e663dc422917d5a7917c8be4dbf22917c9be4ff9148a4922f9f22f91418c0baadd858ec7776318d0d0c60078e3c7b8df1ee27b89265506318cab7732abccc557998f7108a45f329e4522f8c8be4dbf22917c9bfe4522ff9148a452293f55ff27c8be450229148a650228c8a88a88a4522936eeec8a45229348a4d229148a4522ab48a45229148bffe453114ba45722b9148a624c149a0452280d0c63431831817765d9765dddff937e4878e3c6f8dd92ab 12288))
def cur_top_5 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_5 cv_top_5 10 1023 4 15 11 2047 19 524287
def hint_top_5 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_5 hv_top_5 32 8 10 1023
def fc_top_6 : Nat := 0xdf4f817d19c371af86e3530da6881b49102fa3186c2540be8be1ac990345b7868b6b0d34f81a2d9c345b1867b440cf48817d14c325a7865a590cb4a21948d0325a185f2660c58cc18adac315b185f25e0bfad617f58c2fe3305fc5e
def ff_top_6 : Nat → Nat × Nat := unpackForestF fc_top_6 12 11
def ci_top_6 : Nat := 0xe2e0e0d2d0bbb8a3a099919089815d584340404032291a181818030000000000
def cv_top_6 : Nat := 0x37d3e60a4cdd6bfb8d4f6da262a6eda4899a9db612a6024cd64c9989d34d3e65a74d56dfa8daf49b3e8b63ca4cda0d13253b67a44cc4b396947291a66b4fc96878f19b19b5e2b63
def hi_top_6 : Nat := 0x89beaa7a8984080e8910181d837179687cedc9a174ee8e006d91c1d764468e53644400006420040963cc0c1563cc00006304243261f42c445bd16589542dc1e9496e9eb045350d0e453400004524040443d440543e5129613689b5f22f59a5cc2ac50d25272114e91fb1a9dc19a93d821531351e0e7595af07d981a70001c9f6
def hv_top_6 : Nat := 0x17665b5776ad2a1946001761755bbbb2492490909249249364924d9b24902499409b492893649366c924dbdddbd982a9542a8c655bbbb2492498b93fffffffff7e453fcffffffff27e7a4924ffff7ff8daa344645f00000b1d934006326924000925124d2492f52005518caa55bb2a954aa552a924b900ffffffff3ffffc9fffefff00000b1d9340001cb61a1a72d89a4d24924009249240900002a8c6552add954aae553155caa624900ffffffff00ff00924fff7ff800005d56c764d004a808032800492492004810000024944926926c90002408012400aa31954ab765500c38124924c5c900ffffffff03cf027eaa4924ffff7ffa1a19f49ea14fa7d9e83192493777652b2494892492492492492492a954aa551a432ab954c5572a9aeeec927fffffffffffffffffffc9249ffefff4343b2eeccb658eeeeed2b1a57692249249249249249212484649449b364926c9249b249b364924aa552a954690edecd6f7777764924931727fffffffffffffffffffc9f192493fffdfff55aab54abb5552acfc8b55b12692d599548be868764db26da46c9289249248c924934924b54954aa552a8d21956ecaa552a954aa492e7fffffffffffffffffc9fffefff4343b26d936d229512a954a9952a5d92492912492492492492492492552a954aa348655bb2a955caa62ab954c493fffffffffffffffffffe4924fff7ffa1a1d936c9b76925634a964aa54cb62eed24492492492492494a9248492119251249a49a49b3649b1b12494a924924954aa552a8d21956ecaa5572a98aae553124924c5c9ffffffffffffffffffff27c64924ffff7ff928686e5b3eddd996cfb77659941dddddab1ab482124925cce6733df9e7fffff93dfe48c64d26b55aaefffffde4a1a1d936c9b6958dca9572a56d632a54cae5b584a89532a54ca5da410924929525cce67339bcf3fffffc9ef248d196c34e5b06518e5b32934cb6e526865328318124242484924924aae553155caa60aa550aa31954aa552a954927ffcff03fffcffffffff24927ffbffed6b01242418c833ad9d49a75b3a934329b41a43249249090924924aae553155caa60aa550690caa552a954927fffffffcff3fffffffc927fffec32c65092cdb65936ed7634876b5ac4d26d95a75b5ac0492492492e673399cdfffffffffe00048166db26dd80658422c580b07500da1249212399cc19cffffff3fc43b218ec5ad6b049369b4690ed7626daed624924924924924924aa552a954690caae553155caa62a954aa55249ffffffffffffffffffffff249ffff10d090134ca31daec9b7626934269941a43b136c4d269352a4d42d89b624924924925cce62a955ccea5ffffffffff27bc04301803181349a5d8003486004d2684d4280484849248670aa55733a94ff3fffffc9efbb26ddddda54328cbb268134813463269249212124924936f76f6154aa154632a954aa552a924ffffffffd9fe7fffffff92493ffdffe868777767dbb1d9349a4d2694921dd93492492492492492a954aa551a43b7bb7b2a954aa55249ffffffffffffffffff24927ffbffc9a4d268d4f6c3485b065180490909a4d2136c764d24924909242492492ab954c5572a982a9542a8c6552add954927ffffffffbecff3fffffffc9249ffefff
def cur_top_6 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_6 cv_top_6 8 255 3 7 11 2047 19 524287
def hint_top_6 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_6 hv_top_6 32 8 10 1023
def fc_top_7 : Nat := 0xff8a41ea99c3eebb07dc7a0fb8b01ea97c3dab587b5630f66d41ecd983d5268008370f02dc1e01983c0160780240010661dc9502fab5873b4f0eb4681ced2c3a52e073b470e76861cad503952a05f5630e34c817d1bc3852205f46b
def ff_top_7 : Nat → Nat × Nat := unpackForestF fc_top_7 12 11
def ci_top_7 : Nat := 0x8d6308c23080e0080200801c4521404c5304c0e5380c2300c02c4b0284a0190600cc300842000800
def cv_top_7 : Nat := 0x835737bc788247281c707fc527ed767e47a7dc587cd6b7c5637bb6a7b3668ad6b885638746a85c528426f7f2677d25f7aa4d020167996e01926790667882c780247725461a4e75a3474a5c7634f7534b7434773b437335472a546124e71a646326e70a44
def hi_top_7 : Nat := 0xb0726e7fac48fd0aa791052ea019b1de95927ea290cd0d318cb9250585c589bd7ea9a5c77709a5e8707979a46ab175726139e25e5c38f94057acf1234d7db68c4631c1d33c0e9a893bbc10143bbc00003b9804093b9800003abc243739ec203434b1714f2e25c9a326868de82069c98718ca85e811e1b1ba073a9aaa0001cdce
def hv_top_7 : Nat := 0x12468ca6d1a3686519ffffe65fffffff0f32ff87ffafffbbbbbbbb2ecbbbbffb000903dc78ff13fe4d9b25572a98aae5530552a85518cabefffffe6bbbb3dc7fffffffcff3fffffffffffeff8ff9ffffb582118fffcebe75fff92fb5432f9ebc77777f6847771f2e6733ff9bfffffffeff8da30da6509bbbbbbff1a43b396c756a9d4eae53ad8db62ec47914b8f173399cce6fffffff3c4343bbbbb4acea1d4ea75369d4f3fffe4ddddddddf1e3e51b365227fc92a954aa551a43bbbb2ab954c5572a98f71ffffffffffffffffffff3fe7fffd0cda8633696369b6c127cffff3ffd7ff8fffffcebffffff6fb5dddda5777777777ff7c78947922525fc4ff9366c954aa552a8d21955caa62ab954defffffe6bbbb3dc7fffffffffffffffffffffffeff8ff9ffff10d0905ddd8d53283487642d8dad56a9b50a85b1b6c6ecf771e377fee673399cdfffff7e7cff80860302daa5d800348600d56a88542806ec878bbff0ce399cc1e453fcfbf3e7fc6a8c2ecbbbb42a150ad5b0d0d356d777777761f38f1b3679cbc154aa154632adddd955caa62ab954c7b89fe7fffffffffffffff9ff3fffe8542b54690b61a42d8328cbb26eec9765dddff93fc0e3dc71e366c955caa62ab954c154aa154632adddd9ee3fe4fff93fcffffffff3fe7fffc63bbbbbbbb428d542b5442d86869ab626eeeecf1e3c78d9bbb3ffe552a954aa5518cab77765572a98aae5531ee3fffffffffffff7fe4fff93fffe7fffc63f3fffcfff5fff77777777ff7ddc3eff3ffe6eeecaa552a954aa31957dfffffcd7777c552af7fffffffffffffffdfd57fffffffc00001800001658ec60001c777775df000038318c655bb2af77700001148a4522917ffc8a45229148a45229148a45229148a34318d0c60c63181ff6137c26936c26d8ec7ddc7bb89dddc777775df155cba62ab974c174aa0c631956ecbbdddc05df84522dd81148be04522f917c8bf7e45f22917f88be4522f9146318ecbb65db1d8fbbbbbbbbaef8c6318c6318d6a5f318c6f22f917c8be45fbf22f917c8be6379ac6318ec9b64db1d8fbbbbbbbbaef9dddddddfdddddddfc8be45f22f917efc8be45f22fbfb8c631d936c9b63b1f777777775df154ba552e8c631956ecbbdddde45f22917c645f22917feefefeabe4522ff117c8a45f22914229148a4508a322a22a22917ffc8a48a4522f114914c4522b915c8a4535dd85004a40049240ca650690d2b69526a56d2a4d0909249249249242a9541a432ab954c5572a98aa552a954924ff3fffffffffffffffc9249ffefff04348124006532834876b4ac552b764a84849249249249248124ca0466c4945126c6c49252a4924926c9248552a834865572a98aae553154aa552a924924c5c93fcffffffffffffffff27c64924ffff7ffd56cdd54ca2b554ab3f22d56cbd665522f800000c92003486000464925ea4926c800d21954aa552a954aa552a924b900ffff3ffffffffc9fffefff000000018c9249001a4372db949ae5b72934009240900249001a432ab954c5572a98aa552a95492403fffc03fc3fffc2493ffdffe00086003000690c08a9600049200481024900002324a24000902004936492400690c030e0552a954aa492493172403fffc0f3c3fffc9f192493fffdffe0000003485b0d4f6c000493764dddd8001200492492005572a98aae553154632adddd92480007f87fffffff84927ffbffc000012a200baa8005dddd800042049249200000004810026d24a24d926c924800061c0aa31956eeec9249262e48001e787fffffff93f3d24927fffbffc568c0d963b26813760adb0d0d2b6c049240909249249249242a9542a8c6552add954aae553155caa62493fcffffffffffffffff249ffff0ca302eab76163b26dddb552a34344d4a801212492492492492049328124a249349349366c924d24d2492ad2492490aa550aa31954ab76552ab954c5572a989249262e49fe7fffffffffffffff93f5524927fffbffd0a4d02406a7b61a42d8328c02484964bbbb249249090924924aae553155caa60aa550aa31956eeec927fffffffefecff3fffffffc9249ffefff
def cur_top_7 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_7 cv_top_7 10 1023 4 15 11 2047 20 1048575
def hint_top_7 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_7 hv_top_7 32 8 10 1023
def fc_top_8 : Nat := 0x11e8d423d19846d1a88d86211b0a40020fc4643300083b1168b022c9543d6b5888c581116b02251484452a87ad6310f46a1eb1a8431b30862350f58a42131a04262907aa6f1078b01ff5cc416b887fc720ff8e0200df8401be080234
def ff_top_8 : Nat → Nat × Nat := unpackForestF fc_top_8 12 11
def ci_top_8 : Nat := 0xa02449024066d90605806015354150541414110034cd0304842008018860108400c4300c0300c003
def cv_top_8 : Nat := 0x9156b905638fc6a8f4669d56b9b5639a36698b5e9726f93a6791a5f8ea358e0628d8525802a8c8668bc588b2557ca4d894528a45889b5888a557c24d7e25f7ba3d87a358026686b6684a6f7fa67862358546884c5282c8083c5882d718137e80b7c80234
def hi_top_8 : Nat := 0xa49da6089c31a61b976d79318fbd6dec88398de18065adf578f595dc71b1b9d16d7cfd0d631e7e985ce1b18f56ed7d7d56c80c09524929204a2e92074341a5bb3be9a1d634bda5cb2d2db1e42591ade71f91b1801bed0ce9143679ee13e8141312c83c48122824280ec4d4d907b5b9c4077c100e0610685b04d44c4f00012135
def hv_top_8 : Nat := 0x4160b051a9ed8699b60ca32ec8a45bbe2284db2c764de72f07ce3c78d92a955dcaa62ab9559a630552a85518caa55bb2a9ee3fffffffffde7f9fffffffe7fcffff8c6cd20acd828cdb0d0d416d64db26d8ec9a49148b6788bc78f1e3fffc4d3678aa552a954aa31954aae553155caa62add954f77154fffffffffff9ff27fffcffff9ffff0000b1d8c003ffffc8be01ddddd77dfffe00318c655bb2afffff777000c0002c3c00e00070aa21a1d936c9b690ffffffffd3bfe45feeeee4bbaefbfffcaa552a954690cab7655ffffeeee2289d22a74fff22a76eed3bfe4522a748a45e4e9153ae4574e8c764db26d8ec9be7fff9fffebffc8bfddc3e26ddf7ff9ff2552a954aa5518caa55bb2afff9bdfff8aa55efffffffffffbfaaffffffffffffff957ffeeec68631a18c18cbfb3fc0bbbb2eeefbb8f7713b8eeeebbbb2ab974c5572e982e95418c63bbbbeeee022917c2291422917c22f917c8bf7f7e45f22f917c8a318c777777777dddddddd7776552e954ba318c77777dddde45f22f917c8bf7f55ffbbf22f917c8be45b2eeecb1dab577fff66eefacd9adedeeec8b67a0bb2d2b04bfc3cffff0bbbbbbbb38ca0d2ebbbb36b5789b4dbc42a9541a43bbbb2ab954c5572a9b8aa55e3fcfffffffffbffffffffffffffff120240cbe7af1fff997dabffe65f6addddfdf1947d6ee3e5cce67ff37fffffffdff021a4092003ccbfe1ffebffc7ffffe6dffffffb7d8bb2d2bbbbbbbbbffb38ca0cda90fac6de26de3fe7ffcdddd8552a834865572a98aae5537bfffff9aeeef8aa55e3fcffffffffffffffffffffbf1ffffffff80005a560001fffffe3185d80000d2ebbbb72b578b95cbc400690eeeecaae553155caa6e2a957803fffffcfff000ffffffff00000fffff1805a43ff26800d2ef6affff93789bc003487effffe552a954abc552af007ffffffffff9e3f22fffffffff9000064f007af1fffa37dabfffed5bbbbfb01f07793ffe6edcce67ff37157fffffffeffbfc0010c00600007ffafff1800787f80005a560161761ff60034b80207f9fff3777600348601870f7fffff35dddf154abc01fffe01e450ff0ffffffffbf1ffffffff8e5185d977761fffe0e5b0d0d396c17777607b9ca71e366cf39782a9542a8c655bbbb2ab954c5572a98f713fcffffffffff0fff0ff9ffff0ca30bbbb2eeefffdcb61a1a6ad82eeeec38ca70faeeedabc5cbc42a9542a8c655bbbb2ab954c5572a9b8aa55e3fffcffffffffff0fff3fffffffed6b07ff9fe0c7e0eed2bbb45d9695994cbc4ca65e271941a5d77765572a98aae5530552a834877777c552af7fffffff9fe7fffffffffffffffa1a1ddddda568d11a65469951a7f93e7fd2bbbbb5c7b8f0cf9eb367adc552a954aa348777765572a98aae5531ee3fffffffffffff7fffffffe7fcffffa1a1dddddda57762d6b58fff4ad3b776bb86975ddddadc6dc4aa552a9546868655bbbb2ab954c5572a9b8aa55efffffffffffffffbffffffffffffffff0000bbbb000072d86869cb60bb0000e3c6cd9ee27fc9002a8c655bbbb2ab954c5572a98f7100ffffff3ffc000ff9ffff00682ecbb0000b58b1940ff49db41e03b8f10ce0caae6731fe7ffdffff800001b4400000001e1fe01ffebffc000b2c2eeeffec0f000771e3fc4ff9366c800061c0aa31957dfffffcd77767b88001e787fffffffffffdff1ff3ffffffebac35e65f56ffb7117facbd7ff117c9199477777ffe12592b5ddd8043c10954aa552ab99cdfffff7fffe35461765ddd813e41ab61a1a6adaeeeeeeec3e71e366c813e12154aa154632adddd955caa62ab954c7b89fe7ffffffffdffffffff9ff3ffff6e0849febed5a085cce6fffffb2463b0ec58b0234469f648d21ab0ed7777776b5ac65b196d6b16329fe93b68021eee26dc5cce61955cce6fffffffbffff
def cur_top_8 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_8 cv_top_8 10 1023 4 15 11 2047 20 1048575
def hint_top_8 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_8 hv_top_8 32 8 10 1023
def fc_top_9 : Nat := 0x13f6cc27c1380042189db5413b4aa2375ac4ddaa09c35e1374aa23758c4d53688db661328cc26491446daf097b6412f6bc2369bc4a2b98964711286fc250df04a63f09435e11b4ce2495d8491bb09235411b4be23d5ac4852a08f563
def ff_top_9 : Nat → Nat × Nat := unpackForestF fc_top_9 12 11
def ci_top_9 : Nat := 0xa49eb781e06cdb06c19258d6049120480e4380e0308b12c0a1280a02444510040100130401000400
def cv_top_9 : Nat := 0xa04669fb66a946fa846ba7467a6463a526ba4263a324ba22438d94ea08669f04e9e3549da55912359c35e90a349cb549ba55902359aa6d8f26592a4f5882a99c6697a6f94267992459836497b5e9638c9647194c7e96d7395b7e9537c8f3749435e9357692b769235490a54
def hi_top_9 : Nat := 0xc235ae44b9e97613b1c5ca09ac912d4da0b6aef7995de5d6992c100c93ad59608aaeb640836da5d07aa9c63172e9adf06b15adf563359df85c65d5b458e8fcdf503aaa2c4ef440514e9818174aa4e4fd42c5c9f842a008093de10930326a9ede2d412d4a27892d6e1ef1d62612eeaf010d5d1d640bd46862078521140001a5e1
def hv_top_9 : Nat := (Nat.lor 0x77917c8bfe97a77d3be45f22917c8be45f22f9148a2748a454e9ffe454ed916d3a452294e9148bc9d2453275c8ae9d3248f407fa401ffffe04db2d21dd9148b763229d0d06973361bc59acde24dbbe0aa550690caae553155caa62add9578aa55e3fcfffff1ffffffffffffff8fffffc7ffe2404964db269e6507ebccbecdfff32fb37ffc8bfc651f5bbcf17339bccfe1fdfde45ffffbfeffffefef04348124004db2d21dd9349b7762687ff9943c7ffebffedf6fffff4affffff917ce32834aa43eb2578a578936efbffcff90aa550690caae553155caa62add957ffcdefffc552af07f87ffff8fffc7e45fffffffbf1fffffffff8fffffc7ffe00000031ffffff805a430229140000697395cbc5cacde24dbbe001a432ab954c5572a98ab7655e2a9578003ffffc6001fe01f7ffffe3fffff1ffff878000c9eb26d934007ebfd9bffe8df66fff917c07c177fe4ff17339bccffc550fefffffef22dff7fffff7fff780021800c00b486004d2685d8000078fffd7f8007f87807917c00697004026ddf7ff9ff2003486018702add957ffcdefffc552af0007ffff8c00f3c03efc7ffffffffe3fffff1fffff87f80d396c34e5b0e5181dd67704db2c764de72f07b9ca71e3c6c955caa62ab954c154aa154632a956ecaa7b8fff9fe07f9fffffffe7fcfffffff8d336c34e5b0651804522d84d2284d26d84db1d935cbc59bc4e329c3e26ddf155caa62ab954c154aa154632a956ecabc552af7ffff9fe007ffff87ffffffffffffff957ffed6b07ff9fe0c7e0ed0c691349a58eecb4867d32f13e9f789c650697136ef8aae553155caa60aa550690cab7655e2a957bfffffffcff3fffffffffffffffd0d0cfa1f61a7d3e9f4ff27cffd936c9b690ed7725ddc78f0cf9eeb771bbb2552a954aa34865572a98aae553156ecaa7b8ffffffffffffffffffff9ff3fffe868762d6b58fffb26d936d0d0ed68645488a9dee1a5d6b71b7126ddf154aa552a8d21955caa62ab954c55bb2af154abdfffffffffffffffffffffffffffffe000034e5b0d396c0004522800058ec9bfe4f71201c78f1b25572a98aae55300154632a956ecaa7b88007f80001fffe7ff9feff3ffdffe00d000016b163e81fe136c1d91152743c0771e219c73398ff3fffffc000012a2000009a5858ec9a0000001fe1e01fffebffc8be078003b8f1e367fc9fe2400030e05518caa55bb2afff9bdffcf71000003cf00fffffefbfefffffff3fdfe7ffbffec35e65fb7c37fbfbc8bd64bffc9fff0906651ab2b5936c9b645b228043c10954aa552ab99cdfffffffffddfde04f900ca30699b61a66d826d977c45bb22916c764d0f804f84f1e3c6c8552a85572a98aae553154632a956ecaa7b89fe7fffffffffffff7fff9feff3ffdfff6e250d0ec7db5ac65b1f6d6b16329ff64db268ec88a93a010f71e2e673399cdfffffde45ffffff248d1952a34950ca32ec9a4dbb2693426d963b26fffffff997ffffc3ffcca1fffebffc8be001207b8f1e367fc9fe24aae553155caa60aa550aa31954ab7655fff37bff9ee3fffffffffde450ff0fffffefbfefffffff3fdfe7ffbffed608463b26d9364becdfff3af9d7ffcf3283f5e45f423bbcf17339bccfffffffde450febfeffffefefff43434a8dca753ab36d6669d4eae5b584a994242284526936c9b64de3c51e45273399cce6fff3c0fff3ffffbfbcea1d52a753a9d44343ff27ffcd936c9b764522ddf116d21f1e3fe4a44f9478d92a954aa552ab954c5572a98690cab76553dc7fffffffffffffbffffffbfffcff7f9ffefff434aa18e4a592b25b049b26d936d21dd9349b77626f9fffe78fffd7ffdbedffffe75ffffff22ff1e251e4894971b3fe4ff12552a954aa34865572a98aae553156ecabffe6f7ff3dc7fffffbfffffbfffffffffbc8bf7fdffffffe7fbfcfff7ff8868480329941a43b4f6c9582c152b3d66da0b6b26d934914917bb8f1ff26f399cce6737157fbc8bffffe7cff800c67804d2692eeefffffdfe02180c001a430082c149eb340026934bb09149140938ff26f0671cce6e2a9fe79f3fe19461d658ec9b0566c160b61a1a82d89a4d26cf71c7b8e3c78d9ff0ff20552a85518caa55bb2a955caa62ab954c7b89fe7ffffffffff9ff24ff9ffff (Nat.shiftLeft 0x868764d26d936c690c64d09a4d269341fa497fa753a9deeeee4bbaefbbb8f7712a974aa5d1a432add974aae5d3155cbaa5eeeef22f917d7a77ec8be4522ff9157fa5e45f22f917c8a86863487ddddc977777154aa3486552af77 12288))
def cur_top_9 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_9 cv_top_9 10 1023 4 15 11 2047 20 1048575
def hint_top_9 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_9 hv_top_9 32 8 10 1023
def fc_top_10 : Nat := 0x15f8f82b2dac5753e0acb6715b6d82b51d0565b18ab4601566f42acd805551b8008471530c827d1bc5442209f46b14f0f827d19c5342209f46314b04827c9ac5241209f26314704827c92c5141209f2431426ba284d544f83309fc66
def ff_top_10 : Nat → Nat × Nat := unpackForestF fc_top_10 12 11
def ci_top_10 : Nat := 0x946508ca3088611751d07418536cd02c8b0284a01cc701846014450104400c430084200800200000
def cv_top_10 : Nat := 0xafc7cad360aea7cadb6cad474b036faf36bae367acb63b167ab0c7aac460abb7aab360d7d6ad636fd4b6bd1b67ceb63cc351caa6fbf267b525db1a3faaa37a1874a9864a8844a787ca1064a004ca6844a5824a4824a3824a2824a1b5da1355
def hi_top_10 : Nat := 0xe9f4080be9f40000e9282c33e9280000e9280000e800304ae0e9b9c6dd88bcd8d69591bdcc8e9682c5fd7da4bfb5b992b5d2a279ada1c20c9f4e9f95974dce008a5ab73d8289e1f4786686897095c1f46352a7515c3dddc551f69e9249a5ce143c86b7483351d24d25328f881fe56153186199e10fc1ae2808b581c30001b22d
def hv_top_10 : Nat := (Nat.lor 0x17c8a0000031005d54002ed2b00009c1c975ddd800061c0690eeeefbbb800008a450ff0ff4bd3be9dfbbfbbf22f917c8be4500002280002753a04500fffbb4eddda76c8a53a4522f274914c9d722ba74c920682c8b765a43022ddd87fa490fc13a9db4e9143b8e4bbaefbbb8f7710ba550690cab765d2ab974c5572e9bbbb822f9ebd3be4dbf22917fd2ff22af22f917c8be450680baadd85a43bbb18d2486300ee392eeebbeeeee3ddc42e9541a432add974aae5d3155cba6eeee08be7fa5e9df4ef936fc8a45ff22917fc8a45f22f917c8be4504e9148a650fff229348a4d4eddd916d3a45229348a4d4e9153a9d22ab48a9d22a753a4529d2291793a48a64eb915d3a6491b49a045228257e97f83402753b65a74bb2d2beee3ddc4ee392ebbbb2ab974c5572e982e9541a43bbbbeeeefbffb5fe9208be7a5e9d4efddfddf917c8be45f22ddb552bb4ac60d0005d85d56d2bbeb37764ee392ebebbbbb7bbb7b305d2a834877777ddddf7ff77ff764522845f3fd2f4efa77eefeefc8be45f22f916ec8a9db4ea76eeed3b69d4e81144e9148a652287ffdd9153b777769db2294e9148bc9d2453275c8ae9d324800002eaa5a430000ff000269353a9db4e9148a01c9775df7771eee200348655bb2e955cba62ab974ddddc01fe97a77d3a7936fc8a4504803c8be45f22f91400002eab690c0060201aa00725dd77c0138000690cab765d00c387777007fa5e9df4ef936fc8a45008a787917c8be45f2280007ff9149a9dbbb4e9140013a9d02280114a748a45e4e922993ae4574e99240d0174ba0d219dc725ddddc19c74e673399cce6022bbb87fa491bcba5d2ed976cba5de3ddddc41dddcc045f3d2f4ea77caa45f22917c8be45f7f37fa5fe640d0174ba0d219dc725ddddc0e5577074e673399cc67e33bb9869246318ba6b3598c62631b8c4008be7fa5e9df4ef9548be4522f917c8bfeffe6ff3117fcc604e9148a650fff229753b645b4e9148a53a4522f27498c633bbb915d3a6318c64e993a9d3188a9d32753a9200001a4300e4bbbbb8001c69cc673399cce60000ff0002e974bb65db2e9778f77771319dddcc600f4bd3a79548be4522f917c8befe604900000000d2180725ddddc000e5571a7319cce6733980060200ba058040e00c007fa5e9df4ef9548be4522f917c8befe600229143fc00003ffc8a5d4ed916d3a452294e9148bc9d2633bbba74c0009d4e8114012486877777695f777725d7776e6733a733dbdb99cc6d0da6d36994da7fa495fda76dddd3a9de3ddddc4ca577773297c8be45f4bd3a9dfbbfbbf22f917dfcdfe92fbffb486877777695f777725d7776e6733a733db955deedcc67e35977665b2c692576eef66eefacd9afc8be45ff4bd3be9dfbbfbbf22f917fdffcdff764522fdffdd9144e9148abd4e9fff769dbbb4ed914a748a45e4e9318c6777722ba74d77769db4ea76ec8a9db4ea7524868765db2eda43eeeee4bbaef9cce671a7319eedd4aa573398da1b4da6d329b4ff52a95294deee9d4eda748afc7bbbb8ddbbbb9afc8be45f4bd3a9df2adf9148be45f22fbf9bfd2ff324343b2ed976d21f777725dd77ce67338d398cef76ea5752b99cc614a631954a186a549294ceee62a531b94a6eefc8be45ff4bd3be9df2adf9148be45f22fbf9bfcc45ff52988a2748a455ea74fff229753b7769d22914a748a45e4e9319dddd3a652a94ca54e993a9d3188a9d52a753a921ea1e00302eeeeec2ed2beeee00e4baeeecaa5d2a97400690eeeefbbb84004503d79f7f7e45f22f917c8b769d4eddda753aaed58cf4302eeeeedeb64db4aeeeefbbbb92ebebbbbbbbb2a974aa5d1a43bbbbeeeefbbbfbb229145e45f5e9dfbfbf22f917c8be454ea753a1fe81f831a06f5b32934cb6f5268653283487ddc7bb89dc725ddddc5573298aaef530652a83486555e9557bdddc09784541148be117d7a77c8be45f22f917c8be45bb26abb563068bb2681349a450269697dddd9dc725ddddddd7776174aa0d21954ba552ef7777dddfdd9148a117cf5e9dfbf5e45f22f917c8a4d26935218d218c1a013a9db08a9d09a4db09b690fbb8f7713b8e4bbaef8aae5d3155cba60ba550690cab765deeeef36ff9148bfe452291422f9ebd3bf7e45f22f917c8be45 (Nat.shiftLeft 0x328aefc3292acfec36a3e93293eccaa45f492bbbb4920ca65124924bfc9f3ffc78a28d9f3dc4ff92552a954aa92577765572a98aae5531ee3ffffffffe9dffffffffffff3fdfe7ffbffc32f9e82ffeeefcfaadfff26936cfbc7cdf12ffe6ffff4efa77bfbd24acbbb12492269349a4d3293524aec9bc78a28ddf713e4954aa552aa495dddd98aa552a954f71fffffffff4effffffffff9feff3ffdfffe7fff8925feacbbbb3feeffffffffffed24924aeeeeffeeffffffed24893c78ff13fe4a28ddf5d926cf154aa552afbfffff9924adeeedecd77767b8ffffffffffffa77d3bfffffffffffe7fbfcfff7fff9fffe2497fafbfffff492eeff3ffe524bb8aa552a957dfffffcc924552a954abc552af7fffffffffffa77d3bfffffe3fffff1fff80000007f800005dda76ed3a9db4ac03bb8f771e4baeeec00aae5d3155cba61a43bbbbeeee0004803d79f7f7e45f22f9 12288))
def cur_top_10 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_10 cv_top_10 10 1023 4 15 11 2047 20 1048575
def hint_top_10 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_10 hv_top_10 32 8 10 1023
def fc_top_11 : Nat := 0x17f6a22aa99c5ae358b5c6a16b8cc2f49105ae318bc46816b6de2ec8d05adb58b9c701734f82d6d9c5c1b60b835c16b6c62d6d3c5b51a0b5b4316b4dc2aa9745933d0b45701648ec2cd5c0591bb0b236c15547e2ad9e855a3d0acb6f
def ff_top_11 : Nat → Nat × Nat := unpackForestF fc_top_11 12 11
def ci_top_11 : Nat := 0xdb6c361b0d86874191c86070180b1582c142a0502633045a01007138184c024100802201
def cv_top_11 : Nat := 0xbe578ca572c6570c4b7fc2373bfb51bd244bc468bb234ba470b9a7cb8b6cb835cb6a34bec6bbe46abdc66bcc63bbb6fbab6bb9367b7b63b734fb6343b5a6eb4570b3570b4e7ab3c76b2b76b236cafb78adb64
def hi_top_11 : Nat := 0xedccf525c9537493594c8e5e37dbdebc4f090837b3363aeeb8302bda2100d4b1c8789f4e24655e90a2c2ed0d44c50982a4a612b9121324943837c53d1cfb81b1ba32fdb1216dd626c95357585545d131376a2b495dd3b42428a40cc0d74510c0c276046508adee0f88a269ae60a0a6a9000b494d8000040580000000
def hv_top_11 : Nat := 0x127ffffccbffffffe1e65ff0492492123fd5994fa65b3e865329f7ffffe924001207bf89ff251478f12ab954c5572a982a954f7fffff3249154aa552a9ee3fffffffe7f9fffffffe9df4effff9feff3ffdffe1d4ea753a9d42923a9d52480469d4ea8db3ed9f412ff72f394aa552a955cce6f3fffffffe241d4ea754924920ca651248cb66526996cca4d03e08a3ce5ee3c42a9544922ab954c5572a98aa552a954f713fcffffffffffffffff3fe7fffcea7532a44a4889075b3a934eb67526865328925fffe4ff003aaa7b811478f12ab954c5572a982a9544922a954aa553dc7fc9fff27f9fffffffe7fcffff807501203c569d7fc003a9d4a481083a865569d4ea8d0fb6025fe7154aa552a8673cff9fe7f802495ddd83979cce6ffff012000011a1d4ea0148975502eeeec03c25fe19c73398ff3cf9ff329949a4d04bfffc9bfe194ca1489755b2c9b64dbb492469f55a7d26934ea7d3a9f49a4d004bffbbb893ef173399cce6f3e7fffffc269344922cb46f399cdfffe097dfff994ca4dd98dff67d492b3a9d6eeeeeed1a194ca1488165d56eeeef8dd92097ff5bdb99cce6fffffbf22f9f3fe16e269343ffaceffffe0092564db268247de7339bfffffc00a440baad936c9a0810846801d43a807d012ff0f0e6730673cf90f229fe7f9d51a755694916651248fb64d3ad9d6eeeeed1bc97fdf1f4aa552a955ccf7e7fffffffd1a753e9349a75f04827fff9d51a754694959f49a4d3ad9d43e994492bbb3e9f51bc97f9f78aa552a955cce6f3fffffffe0000020000eb550003fc2920000492469d4ea8d00004922a954aa552a954aa550000f3fcff3fffffffffe924750ea129248a4959d49a75b26f1e3c8a48ffff1e2552a954aa9245572a98aae553154aa552a9ee3fffffffffe4fff9ffff3fffe7fffd2ff120fa6532dd936cfa4d2687d328924653ea14fa4d26b94fa853e9349a4f1e367acddb99cce6737ff9e7ffff7f7937c0fbe4ddfa77efbfbec9bf7f7f7e197cf567d03eff9349e3e6edffcdf7fffe9df4ef7f784df12482684de387339bfffc9a4dfff42fa17ffe1be197c492f4109349b7fe4db2ceee3e5cce67ff37fffff7917fffd3be9defef4923e87d429f4fa7d124924ac9b64d492fff3fe4f1e28a3764ff93e6c954aa552aa49155caa62ab954c55bb2a9ee3fffffffffffffffffffe7fbfcfff7fff9fffe2497fab269f6c9bff77fffffe4d26a491f4269f4fa4d3fcfbfffffffffe4d26a492491278f1fe27fc9451367aec9bbb2a954aa55f7fffff3249156ecaa5572a98aae5531ee3fffffffffffe9df4effffffffffff9feff3ffdffe97f890196ccb658925776e5b72ddd996cca65bbbbbb32d9349e3c6facd9e73399edcdffe79ffffdfde197ccbe7897abbbffbbbf56ab7ffffffcca65492093bb8f9e387ff3399cdfffe9df4efffff7f7865
def cur_top_11 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_11 cv_top_11 9 511 4 15 11 2047 20 1048575
def hint_top_11 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_11 hv_top_11 31 8 10 1023
def fc_top_12 : Nat := 0x19f6c033c8d4555b18ce2551998dc332d986651a8aab51196ad032cd44555378bfd7218d69e325170635a58c6b4718f69831d150635a18bfd7018ab003155a05fdbf8c2e801856d830d5c0615ae0bfb731808fc300df8601be0c0234
def ff_top_12 : Nat → Nat × Nat := unpackForestF fc_top_12 12 11
def ci_top_12 : Nat := 0xa1c9241198c445cce07032d74b154a85329848a08c8603012c8240200e44620100804004
def cv_top_12 : Nat := 0xb836cd0361cfb60d136cd0b5cb7a6dcf235ce255c0266cdc6ecd366cb26fbfa67ab245cca35cbd68cb351b5a5cc5b7dc4371c9358c7b44c945cc7340c7b4cc7454c336cc9b4fc8b4bc8347c6b43c5d80c5568c1b50c336cc3570c4680c3b6cc2b5cc1c7ec137ec0b7cc0234
def hi_top_12 : Nat := 0xb3e2aab9435ac91e7ac302fca29854c8273d478e676a79d85ee31c2a45c19e4ada9a6c74ba5840cb472789934080d3268000064002034c18101a18300000306000005d70b0d4828e0e18fc818221e10486037e0c11069a14188ce4141419c800003280304458c20310a54183113f0302e207201dc348223180014da4
def hv_top_12 : Nat := 0xf41f77ffe4d26807a37ffffffd2489a4f07793ffe5226f03ff99cce6e2affffa77d3bfde45fffffefffef000000ff4001755ffbbffffff2693524803c003cf0010021007d003fcfff949226ddf004000f7fffff3249156ecaa01870e2a957803fffffffd3be9dffff00f2287f87f8fffffc7ffe09071340389a637ffa77bfbc0000040000135248000049226f1378000c0249154aa552af154abc0001e7ff9e9dffffff1fffff8fffc9a4d26a4924909007ff9fffe04d26f81349a9246532f1329978865e3299449226936eccbc5572a98aae5530552a892455bb2af154abdfffffffe3fb3fcffffffffff1fffff8fffd24ac9b64d4924688d32a34ca8d124924bfc9f3ffc7b8a28f134f9ee26f154aa552aa49156ecaa5572a98aae5531ee3fffffffffffffffffffe7fcffffa495936c9a4d492489a1349a4d268924925fffdc9244d26ddf1349bc49bc4aa552a955248ab655b2a954aae553155caaa5e2a957bffffffffd3bfffffffffffffffe3fffff1fff8000000240000924e5b72935cb6e52680228f713fe4f1e2009245572a98aae553154aa552a9ee201fe7ff8007fff9feff3ffdffe0240004db0120009a650009a4d09a650124bfc3c077771e219c2a955ccea53fcf4efffffff7f7800000001e1fe000002107fa0000fa587dfffffa4901e000effe27fcf928a3c78800061c3dfffffcc924552a954aa7b88001e787fffffffa77d3bfffe7fbfcfff7ff92925ffe12249194cb64db268010f042552a954aae6737ffffa77ffffbfbc9b64db46526d9567e45268559265522f89004f904924920ca65124ac9b64d03e08a204f84f1e2154aa249155caa62ab954c552a954aa7b89fe7ffffa77fffffffffffcff7f9ffeffff26ff936fffc9a1d78b949be65fffb32ddf2749b6affff88bffff7dfc9df32f934cb64dbff26ae4e917c9a4d3299791a4d270424492ffbf087b9cce6fffff4ef7f7928d269349a4d09a13411a2342524aec9b64d2693412269349a4d32934ca4d269342684d32934ca2497f8043ddddc49378b99cc552ab99d4bffffe9dffffffefef
def cur_top_12 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_12 cv_top_12 9 511 3 7 11 2047 20 1048575
def hint_top_12 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_12 hv_top_12 31 8 10 1023
def fc_top_13 : Nat := 0x1b24c637c0906c9258de0241b24863641986e5b30d904e1b2058366d7c6cdad8d9b571b36a6364090004258d8245155ad435b5a06b5328aab6f1aa6d83548d4555b58d324f1a648e34c914692b80d227d1556ce33cdb0679ae0cfb61
def ff_top_13 : Nat → Nat × Nat := unpackForestF fc_top_13 12 11
def ci_top_13 : Nat := 0xd0722c8311c0700b8ae0b82e0b82e0a91dd741946056249120444d4340d034085188240440100000
def cv_top_13 : Nat := 0x482404134df024de02403816dcb6603016db35fdab5bda357d9b53e4c6fe3c6be2c67e1c63e0a6bdfa63dea4bdda4302926dd066dc04edb82cd9024be24dd8245b4a3fb1237bc24dbc568ce350d7568cdb50d6a65bba5dbb26cd5b6cbaa6daba45d5235d424fba24dd3a47d3245b423dba570b9a5cd2d70d227db925db3a3db824db8a5d
def hi_top_13 : Nat := 0xc22dfa30b74abeb9aee5ce19a286b71899edba269169ca218871be3e83ccf9297eed99387889a199720db19f6cc1a9536900e0f0627585a35b55a5c853a5adec4d45c59848f91d1340c6920d394dc1de345d193c294e8ac428c81821283c2023267070731f29d1d219e535510f9e9a92090dbda402c9899102641c190000ac99
def hv_top_13 : Nat := (Nat.lor 0xdeedcc67e35977665b1249249ddecdddf59b35f917c8bebcabfe97dfdf9148bfc45ff77f7f37fdd9148bf7ff768492551ffead25692292e451919dddd3a4ad5a492b492488a924acbb65d492eeee492ebbe73399d2749eedd4aa573398fa1f4fa7d4a9f44a55ffea552bba4927e3ddddc6eeddddd3a5e45f22faf5f7e45f22f917dfcdfe454eff993a92565db2ea49777724975df399cce93a4ef76ea5752b99cc614a631954a24a5492953bb98a94c6e529bbbf22f917d7957fd2fbf22f9148bfc45f77f737f98c4522f9bfd4a642492a8fff45d495a48a4b91464677774e92954a94a9248c94aa54a54454925e8ff012487ada549a95b7a93432994492eee3ddc4ee124bbbb8aae953155dea612a551248aa952aa57bbb808a9df08a4508a45f08bebd7917c8be4522ff117c8a45f229349a4d492492120124241349a826a497771eee2770925d77c5572e98aae5d305d2a892455bb2ef7777b37fc8a45ff229148a7917fcf5ebefc8be4522ff117c8a45f6691524ac9b64d492489a1349a4d26897faf4925dddc925d77dddc7bb8954ba552ea49156ecba5572e98aae5d52f7777917c8be97a5f645f22917fc8a45ff22a77c8a45fe22f9148be454922e974ba5d492eeee492eeee318c65e918c6318c637917c8bebd7917c8be45f22f98de630000021005d54002d2480002702495ddd8000e383bfbbbbbbbbb8000453c3cf5f7f7e45f22fbfb8901755bb0492bbb49249200ee124bbaefbbbb8f7711dc77f7777777777777777708be7af5f7e45ff22917fc8a45f22f917dfdeecfa92492424001761755492beb37764ee124afaeeeddddddddc771dfdddddddddfeffeeffeec8a4508be7af5f7f7e45f22fbfb800005d552480100803e800925d77c0138001dfdddddc071c1dddc03cf5f7e4500229143fc3c8be45f7f7492492eeee492eeee777777f777777777f22f917d7af22f917c8be45f7f7492492eeee492eeee2a955248aa55eeeef22f917d7d57fd2f22f917c8a45fe22f9148be4542491ffe925692292e4519274e9244542407fff802492072b9449272db949ae5b729343dce511479cbdc788552a89245572a98aae553154aa552a9ee27f9fffffe1ffe7fff9ff3fffe2491ffe092480ca651248cb6e526b96cca4d38ca2491978b978f70552a89245572a98aae553154aa552af154abc7fff9fffffe1ffe7fffff8fffffc7ffe0000000900002495dffffff802493978b95cbc6eeec01248aae553155caa6bbbbe2a957803ffcf4eff8007fffff8fffffc7ffe0001fff0dffff42fa1524bd059b3f77fff601c7cddb99ccffe6ffffffff4efa77bfbc00000000f0ff000001083fd05d54002ffeeffffffed248000207f9fff292577760001870f7fffff32495dddf154abc00079e1fffffffe9df4effffff8fffffc7ffe2405dff824924907d82497ff9fe072b44923eab789f4fbc49a7dbb56f0552a89245572a98aae553156ecabc552af1fe7fffffffffffffffffffffff865f3d5ff934bb3d5aadfffffff3299524824e32ff1ff249bc4de7ff3399cdfffe9df4efffff7f787997fc048ff41755bb0fbfffff26a495ddff9f7fffffffffc9a4d49249200e329fe7ffca49134fb77c4d3ef13ef10aa553dfffffcc92455bb2a955caa62ab954dc552af1fe7fffffffa77d3bfffffffffffffe3fffff1fff9e46df9155946f7dd865f12495ddfffa379cce6ffffbfb1200fa4dff04924920bf04920fff3fce328925c78ddddd8552a89245572a98aae5535dddf154abc7f9ffffe9dffffffffbfbffffff1fffff8fffc9a71ffe85f42fffc37c32f8925e821bffbbbe32ff1ff252bb73399ffcc55efffffef22ffffa77d3bdfdf767dfffffbfbfffffbf0f32ff8249249091fe800bb0baafdfffffda495d9bbb27194ff3ffe524aeeeeedeeedecc154aa7bfffff9924aeeef8aa55efffffffffbf229fe7fffffffa77d3bfffffe3fffff1fff8000000240000925fffffe4d26802491f789f4fbc49b77c009245572a98aae553156ecabc552af007f9ffe001fffffe3fffff1fff800007fd803ffffc9a92b007ffffdbadc4dbbe00f7ffff2a954aa552add9578aa55e00fffffff3d3be9dffffff1fffff8ffffc9dffe009244d278123c80399cde9dfeffffffefffef (Nat.shiftLeft 0x2495ddda4977772495dddb99cce9d3da7bb7319f8ccd19acd66a559a24bffd2493bba5c7bbbb8994a677774e94be45f22fa5e97dfdf9148bfc45ff77f7f37f9148a9dfbffb4ea495ddda4977772495dddb99cce9d3db955 12288))
def cur_top_13 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_13 cv_top_13 10 1023 4 15 11 2047 20 1048575
def hint_top_13 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_13 hv_top_13 32 8 10 1023
def fc_top_14 : Nat := 0x1df04800214c775328e636f1db46a398dac7653e8e63671d746a398d8c731378e9b7f1d36e639899c7423b0e83761cc47e39b1e8735bd0e623700109e3941906ca378e40441b28d638c1f06ca338e20441b28c63840906c9358e0024
def ff_top_14 : Nat → Nat × Nat := unpackForestF fc_top_14 12 11
def ci_top_14 : Nat := 0xfb7c3c3e0e170345a0c8e432190b95c2e152a854264b858249207238148a032180482001
def cv_top_14 : Nat := 0xf224bf12438e14ef084ef002cef824eea65e6a45eda35eca7de8a3deba35ea37fe9b73e8c76e8376e747ae6b7aee36fed36bec367eb363eaa6fe9267e7a3fe6237e5064db024e4044da824e307cda024e2044d982405134e1024e0024
def hi_top_14 : Nat := 0xdf759977db990cf7d326961dcee50510c3d28ac5bf511520b4da9a9eafd14542a716962f9ee28a0d9d8844569c0c4c5f912a92b98e80a4aa8a2d05157ee68ad27abd0d0a7828a4a56dca9a9866e581b9605dc9a257ea9a1d50bdb1cb4572a2d33d95d5f732feb2a62c09c9bd22eeaa471b45d5ea1036bec408f5f1d00002b63d
def hv_top_14 : Nat := (Nat.lor 0xffafefffffbbb6aa576958c1a3efc7fffff7f7fffe1ffe30f22f801761755b4afffefeffeecddd938ca0d2efff3e3f3777776f776f660aa550690fffcdefff7777c552af7ffffffffdf914ff3d7d57fffffffffffeffffffffc008be1e3bf001a43ffff18fc63fff2693c097f93fc324de0f33fb99cdc555fdfffffdfffffde45ff000000f22f8005d56d21fff8feffc0065804203cf003c1800d50006977ff9f1f926ddf0040001a43fff37bff956ecaa01870e2a957803d7d57fffffffffffc6079e1fffffffe0000031000000007f878c03c8be000354b01a43fff1fdff81e000ee28ff93fc4f1e200018701a43fff37bff954aa552a9ee200079e1ebfbffffffffffff8ff9ffff268fc7f7e3f32df7f117f87e3f26996ecbc63fefeef22925218d218c1a3c7e3fffff1f8ffffc3ffc61e45fb32b54cb6d50ca650690fffc7f7fe001207b8a3fe4ff13c78955caa62ab954c154aa0d21fff9bdffcaa552a954f71fffffffffef229fe7afeffffffffffffe3fe7fffec9b7f7e78c22fdc343c63f27cf1bbf33ffdafeffff269350d0c7e3fff1f8fffcf1845f0849a4df1dfd967779e2e673799fffffd7f7fffff21a1f9ffe3f3c8bf64d6ad936d21fff8feffe1a135ab0d26831a490c7fffffe31ff8c7fffe49e3c78a3fe4ff126cf5d93776552a954aa3487ffe6f7ff2add954aae553155caa63dc7ffffd7f7ffffffffffff7fffffff9ff3fffe319e308bf77f77f763487fffe31f8c7ffe127779e3c71e67f733997f7ffffdffff9e308be1f77f77e31fdb57cf1be27ccfebfbffffed0d0fcfff1f9e45fb2eeecbb492b1ffffffd8ffeeffffeeeeeed2bfffbfbff24f1e3c51ff27f89bbebb24d9e2a954aa551a43fff37bffdbdddbd9aeeecf71fffff5fdffffffffffffffff7e45fffffb3fe7fffd0d0fcfff1f9e45f1a43fff1fdfff70d2efff3e3f3dc552a954aa3487ffe6f7ff2a954aa55e2a957bffffd7d57fffffffffffc7fffffffe00000001fe000925769249007771eee29257776005572e98aae5d32495dddf7770001153a01e8f4befefc8a45fe22f9148be5d228000021005d54002d2480002702495ddd800061c124aeeefbbb8000229e1ebeabfe97dfdf9148bfc45f22917cba450000000481007ffab495a48a4b914645d4e9d2488a848158924095d824bffd2049241dc24975df7771eee2174aa249156ecba5572e98aae5d37777045f3d7afbf22ff9153bfe454ef917c8be45f228901755bb0492bbb49249200ee124bbaefbbbb8f7710ba551248ab765d2ab974c5572e9bbbb822f9ebeabfe97df917fc8a45ff22917c8a45fe22f9148beb5228248ca1ffe89a92b491351352491f52492292e45191753a749222a3e934120ff497a424024848b42497771eee277092577765572e98aae5d305d2a89257777ddddf7ff69dff229153a117cf4bd2fbfbf22917f88be4522f9748b767d49249212000bb0baaa495f59bbb27709257d77776f776f660ba55124aeeefbbbbeffeeffeec8a4508be7afaaffa5f7f7e4522ff117c8a45f2e9155a49256ad248124650fff5692b491497228c8ba9d3a4911500002490000007f81349a92490024975df7771eee20092455bb2e955cba62ab974ddddc01fe7fafbf2281153a01e4522ff117c8a45f4a91400002eaa9240080401f400492ebbe009c00092455bb2e8061c3bbb803d7d57fd2fbf22801148a1fe1e4522ff117c8a45f5a9140003ffd13525690002408011497228c8ba9d3a49115090174ba2491dc2497777027074e9cce67319f8c09ddc125ffe9174ba5db2ed974bbc7bbbb880eeee9d0117cf5ebc8be45f22f917fdffcdfe454eff993a2405d2e8924770925dddc0e5577074e9cce67319f8ceee92492462e9acd6631898c6e310022f9ebcabfe97917c8be4522ff117fddfdfcdfe631148be6ff318124950fff45d495a48a4b91464677774e923232492324924454000092400925dddc000e93a4e673399cc000001fe05d2e976cbb65d2ef1eeeee26319dddd3a401e8f4bc8be45f22917f88beefee60229153a000000092400925dddc000e55749d273399cce60040200ba058040e00c007af2affa5e45f22f9148bfc45f77f73001148a1fe00001ffe8ba92b491497228c8ceeee9d200048100222a (Nat.shiftLeft 0x18c6300eeeeeeee0018c632a957bbb8003eabe45f22f917c8a45f22f917c8be45001808002c020700600700228008686003f1fff8fc7ffe45f0b367eefc03cf1bb7339bccfffffebfbffffec000006200000000ff0f1807917c2eaa0017695fffdfdff8000401a5dffe7c7e6eeec00030e03487ffe6f7ffbbbbe2a95780003c8a1fe1ebeabffffffffffff7fffffffe78c22ff8efcbb0690ffffc63f18fffc24e32f9e24de26f799fdcce65fdfffffdfffe0d01ffe30f22f85d56ec2d21fff8feffeeec6349218ffffffc63ff18ffffc038ca0d2efff3e3f24d6addf135abc5abc42a9541a43fff37bff956ecaa5572a98aae5537154abc7f9ebeabfffffffffffe3ffffffffffffffff269c21a18fc7ffe3f1fff9e308be10fddfddf1947de78ddb99cde67f2af7f 12288))
def cur_top_14 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_14 cv_top_14 9 511 4 15 11 2047 20 1048575
def hint_top_14 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_14 hv_top_14 32 8 10 1023
def fc_top_15 : Nat := 0x1fc6f83f8d907f5b88fe2351e76863f2d3c7e5a18f3a6d1f18c23e2d847c5a78f9b8c1f34683e2d0c7c5360f3a571ed8f83dadc47b53e0f3a4f1eaae23d4df079d1f8f44701e746e00215c794120efa4b1e30483be90c77c270ef82c
def ff_top_15 : Nat → Nat × Nat := unpackForestF fc_top_15 12 11
def ci_top_15 : Nat := 0x9c27094a0580200711c0701c0701c0689a0555505415048d2048102400f10b420044100040000000
def cv_top_15 : Nat := 0x3fadc5f34ccffb7c7f9b23f29f5f24cefe2357e9a7bf2d0df14ccf6a4e7d1c63e68d1f78c2fb3617d5a7be4d0df14d8f7c7c7b9b8bda9f1ebae2f537c7a2384191860b8b704361819adc08d5e0069efdb437e136be095dec49ef4a3f79d1b9660a9e5048f1824
def hi_top_15 : Nat := 0xc999b1f8c9341c19c3ad4162b7beaefcb345051ead692577a565a601a0fd0d1a9b6d456499745c7e98e02025981c283195b0749b8e2991e2831ea6c37b0dca0474fd35846d198df961ca9ed45ce9053854e1ca02493a92ea419dd1e7375e969030f1759b29d1f1c82082b654197dddc10f869e7e07e1bde90400f0f800010100
def hv_top_15 : Nat := (Nat.lor 0x254b2552a654a85dda4bfcfff9381a5c4dbbeb2578a578fbfffff982a9541a432add954aae553155caa6e2a957800ff0f1fffffffffff8fc8bfffffffe3fffff1fff845228868659947adbd6eee0b67dbbb1dddddab1ab4b9bbfe3eb3c5cce6733d843fffffe1148a21a1d936c9b6958c4a89532a54ca3d52af582dad054ac15eb6b5da5cddff1f71e2e673399cc10ff7917fffffc08a45e228065183505b0d3d6c194ca3d6e0a4d82dbd49a3187b8fffe3c7b8f10aa550aae553155caa62a8c6552a954aa553dc4ff009f3cffffffff9ffff3fffe4435c075b1d53a454ef77777007fdb56dab64dbb0040e3c5cce67339bfffffbc8bfe7811255256c9b7c05995ba4d429350a4522917bbbbb80388a592b7f8040e3c5cce6733a97fffffbc8a1fe7877f7922f96adb56debff76d5b6e8dba4f228f53fc1e453f6268f57a9e122f956b26d9347632d9ebff60cadd21f22845f08007f8000700cca9519952a0037a8dea6532994ca00f57abd5eadd18dba552a954aa00552a954aa5518caa552a954abfffe7fff00043fffffffffffc927c8be45fffff3e421e0d1952a34654afafffff0032d994ca65b32c57efffffc00ca0c607ff13fe7c9008071e3c78955caa62ab954defffffe6002a8c6552a954aa553dc7fffffffffbc8a001e01fffffffe7fbfcfff7ff81148bc45006f5433ffcff923d5ea3d6dea4d7adbd49a34861e1227fc9f28f1e2154aa155caa62ab954c3486552a954aa7b89fe07ff9fffffffffe7fbfcfff7ffa546254ca124d328c764db26845228326d921a1d89b6269349a75269d6c4db7fa3c8a5c78b99cce675287fffff9e7f7f7845e01a550c48705434bcb2564a6512fffffff24865328f582c15ea3487692c96c154aa154aa552a8d21954aa552a954aa552a9fe07fffffffffffffffffffffc8bebffffc60d2a867f9d7fffffffffed60b2564a65024fdfffff86532834876b92c564b764afff13fe7c90f051e4894971e3efffffe60aa550690caae553155caa62a954aa553dc400ff0feffffffffffffffff3fdfe7ffbffec313a453fdaa6db26dd86a9941a43b5ad626936c8542dad6278f1b3d66edcce67339bfcf3ffffc08a45e2280f51834f5b0d3d6c135eb6f53ffcff9363b26878bb27fc9e3c7cd90aa550aae553155caa62a8c6552add954f713fc0fff3fffffffffcff7f9ffefffff22fafffff0ca33efffffc9a134cb6652c764dff42ffffffffff9349a04d32c34ca10d4a8d0d1352a49fe27fc90f1c789b3d764dddfbfffff982a9542a8c6552add954aae553155caa63dc400ff0feffffffffffffffff3fdfe7ffbffc7a8c2deb765ddd81148b760f5b0d0d3d6dfe4f9ff0f1c78d9f3dc4ff92154aa154632adddd955caa62ab954c7b887f87fffffff87ff9fe7fbfcfff7ffff917d7ffff9b4328cffbbffffffffffb0b32dd85ddab5695fbfffffb2ccb765ddd927f89ff243c71e377d7649b3defffffe60aa550aa31956deeedecd77767b8801fe1fdfffffffffffffffe7fbfcfff7ffff917d7ffff833efffffc063ff3ffe4e387dddefffffe60aa550aa31954aa552a9578aa55e003fc3eabffffffffffffffe55fff0000bbbb00eeeebbbb0073399ec7bb7319f8c0000318d0d0c600ee1c7bbbb8994a60000000f22f917eefeefc8be45ff7ff37f9148a45fbffbb0000bbbb00eeeebbbb0073399edcaaef76e633f180002c76ad5dbbbd9bbbeb366b000f2af917c8bf77f77e45f22ffbff9bfeec8a45fbffbb0018080b02c02070060c038e05960058001140000b1d8c03bbbbaef801c667319eedd4a399cc0000318d0d0c6ee001c7bbbb8ddd80000007917c8be55bf22917c8be45f7f37f9148bfe63000058ec601ddddd77c00e33398cef76ea5752b99cc000061a9519294ceee62a531b94a6eec003cabe45f22f956fc8a45f22f917dfcdfe622ffa94c00301005d02c02070060c038e029452800600022800001631d8c60000318d0d0c60007777775df77771eee200318c655bb2e955cba62ab9754bdddc01e45f22fd917c8a45ff22917fc8a45f22f917c8be45000018c6300eeeeeeee00318c6318c6318c600f22f917c8be45f22f917cde6000018c6300eeeeeeee00777777777777000f22f917caa45f22917c8be45f7f7 (Nat.shiftLeft 0x3fffffc7e9d2d0fffffc62b1fffffff9349b6979978cbde65ffff1a5c4dbbe2a954aa55f7ffff1a432add9578aa55effffff1f9140ffffffffff1fffff8ffffcff79fe455fe3bff26fa35ebffffffef50ca652c9b44aef27ffcf0f89bd6e7ff3399cdc5503cfefef22ffffff7fff7ff917d7ffff8c1a3feeffffffc9a4d09b65da4958ffd2bffffffffff6b0 12288))
def cur_top_15 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_15 cv_top_15 10 1023 4 15 11 2047 21 2097151
def hint_top_15 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_15 hv_top_15 32 8 10 1023
def fc_top_16 : Nat := 0x21ead243cd908691f90dc6821b6d04348dc0042f90846b2108ce4209ac8541210824b21304842090c8463310804e0010b641cd0c835228f3c611e78b6414d4c8251a8f3b61207ae23ced6c815b00f3b572018f8402dc0805228f3b4f
def ff_top_16 : Nat → Nat × Nat := unpackForestF fc_top_16 12 11
def ci_top_16 : Nat := 0xb82c2b02c0a8a19842017c5f0749d0705c0689374c121390e0380d11d87018460144501405001400
def cv_top_16 : Nat := 0x21fad30f36487234436da2308b3173598ada7c4ed0e234ab1024f8751fc348dcf30650884c0389a01a4d215049098248463301805a188d70bc6785935c2892e12486059268402741cd0e076d6fba6783522bd68fe0a6a702c6680a2f3ec99dee4bf04a352d01540f5c6056c101c7c809b83f49f5f54cf00a45
def hi_top_16 : Nat := 0xfd81b99af4369a53ee2db182e8d96955e062aa1edb457d47cd8ebb6ec1aab6f9b51ac324adadd5dba14ebf1899d9c1dd8c2aa76c85719dae7cbdbe2d744d8e1c737820356bd9b1e864619dde58aabaee580c20275061b1eb47cdb625434d05203716b70e2fb1b5d924aac6c21cf9c9ec167d799f11fd0d2008028e7f0001c200
def hv_top_16 : Nat := (Nat.lor 0x99cce67319f8c0e61991918c62e9acd6631898c6e310000f0f22f917c8be45f22917f88bfeefefe6ff3188a45f37f98c1e4519151151148a452e916c8b645229149148a45e229318c6777722b98dfffeeeee67ff318c60018c2ecbbbb3b8eeeebbbb0ce399ccf6f6e67305fff80c6343431dddbbbddf1eeeee2652bbbb994a17e1e45f22fdfdf9148bfc45f77f737f81f7ff603185d97776771dddd777619c73399edcaaef76e633f182eecca163b56aedddecdddf59b3587957fc3c8be45fbfbf22917f88bfeefefe6ffbb22917effeefffc8a322a22a22916eeeeeeec8a48a4522f11498c633bbb915cc6bbbbbb22916ec8b777600318176cb1d8cee3bbbbaef8338e33398cf76ea552b99cc06fff018c68686377bbbb22bf1eeeee376eeee6b0de7917c8bf7e45f22f917dfcdfe1fe6018c0bb658ec6771ddddd77c19c7199cc677bb752ba95cce605298c65030d4a8c94a6777315298dca537761e55ff0f22f917efc8be4522ff117ddfdcdfe631148be6ff529bffc8a322a22a229148a5dbbbb229148a48a4522f11498ceeee632954a65298c452298c4552a94ca500b2eeec02ec9a07800318c7777601dddddddddd777600318c6552e954bbdddc177f764522800787917c8a1e79148bfc45f22917cba45063026936cb1d8c3fc9be0318d0d0c64522914ee3bbbbaefbbb8f7710ba5506318cab765d2ab974c5572ea97bbb808be1e45f22fd917c8a45ff229fe1e4522ff117c8a45f2283180318c6771dddddddc15418c632a957bbb83eabfe1e45f22f917c8be4522ff117c8a45f22fff914645445445229148b645b229148a48a4522f114914c45722b914c0134db66d3699541d90c0eeee0ff27cff86536834866db46934db64d0f1c33e7baddc7b8da42a9541a432ab954c5572a98aa552a954f713fcffffffffffffffff3fe7fffc1d90c022a746450fff0da0d21daec4db5dac7034bad6e36e3c6de0aa550690caae553155caa62a954aa55e2a9578ff3fffffc3ffcffffffffffffff3cff4bfffffc7600107fa5fffffffffe454e8203efffffdba0034876b4ab752b764af997cfff9001a5521f592bc52a65e265e32f7bfffff9800690caae553155caa62a954aa55e2a9578003c03ffffffc7e45ffffffffffff1fffff8fffec3432322f865181349b6652c764d0eeee046d8686adfe4f9ff0f1c7b86789a7cf713782a9542a8c6552add954aae553155caa63dc4ff3fffffffffffffffcff9ffff1ba3026936cb1d9349a045229348a04db0d0d136dffe71c3e26ddf1349bc49bc42a9542a8c6552add954aae553155caaa5e2a95783fc3fffffffffc3ffcfffffffff2afff8007f81658eec58d218c6318c7656ab48a9d4e858994b54dad52652e673399cdfe787fff9e7afffff00ffbbffffff2693400b0b1d937feeffffffffffc8a450b56a5468689a9503ccbe7ffc8019787c4d32dd99789a65e2ad32f1f7fffff300154632a956ecaa5572a98aae5537154abc001e01ffffffffffeadf22ffffffff997ffffcabffe5977776950019764d008a001346326dddd8019432f0f89a4de26997aeeec00aa31954aa552a9578aa55efffffff003c00ffff3c3fdebffffe55ffffffffbfbfffffbf22961e5abbb5695f5ffffe6d001807fddffffffd816017777665b37767ccbe7ffc8019432f0faccb77776f776f66f7fffff300154632addddf154abdfffffffff7e45000f00ffffffffff32fffff957ffc08a45bb0068ffffff18cbb12fffffff4ace7a8f57af17aa5788d2ebbbb0aa550aae553155caa61a43bbbbe2a95783fc03ffcffffffffffff1fffff8fffc1a0bbb3e963b08b67a490eec9a73741a5d77764de26f0552a834877776552a954abc552af07f87fffffffff9ffffe3fffff1ffff9157f8fcfaf5fffffff42bd486b54193d7ff68a3c7c8faeeedffcce67301e7f7ffff7f7ff917d7ffff8c1a3feffffffffffeec2eecca163bffbbffffffb2ec4ac695da4bfcfff9381a5d7766ecddddfbfffff982a9541a43b7b35bddddddf154abc007f878ffffffffffffffffffc7ffffe3fff0229146450068ffffffbb09b67fffffa56979cf51eaf5e2f54af11a5c4dbbe0aa550aae553155caa61a432add9578aa55e3fc0fff3fffffffffffc7ffffe3fff (Nat.shiftLeft 0x690b61a42d800090000b1d93402ec0038f10d92ab954c5572a9800aa31954ab76553dc7fffffffc03fffffffff8ff9ffff0000010000001349a176163b2680000001349a0850086a5468689a952480004e0e3c4d9ebb26eec00030e05518caa55bb2a955caa62ab954c7b887f0007ffffffffff7fffffff9ff3fffe000177760000adb0d0d2b6c04800071e3643dc000005518cab77765572a98aae5531ee201fffffffffffffffe7fcffff800005ddd8001346326dd934038f1bbee242400aa31956eeecaa552a954f7100ffffffffffffff3fe7fffc00000da200000000b0bb00bbb56ad2a000016176177764900009c1c78ddf5d926cf000061c0aa31956deeedecd77767b887f0007fffffffffffffdf917ffffecff9ffff00000100000580c600010387ddc00018702a8c6552a954aa55e2a95783eaa001fffffffffffffffffe00005858ec616318d0d0c60007777775df77771eee200318c655bb2e955cba62ab974ddddc00787917c8bf7e45ff229148a45f56ff9148be4522ff117c8a45f5e9143c8a322a22a229148a4d22936eeec8b64522ffffdddd916ffc8a45229148a48a4522f114914c45722b914c0165abbb56300000b00bbbbbeb3776403bbbafaeeeedeeedecc00318c77777ddddf7ff77ff764522801e1e45f22fdfdf9148bfc45f22917cba45bbffbbbbffffbb229143c8a322a22a22916ec8b77777776452452291788a48a622b915c8a60000006318c03bbbbbbb80070733 12288))
def cur_top_16 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_16 cv_top_16 10 1023 4 15 11 2047 21 2097151
def hint_top_16 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_16 hv_top_16 32 8 10 1023
def fc_top_17 : Nat := 0x233ade47c5508ceb591e17c233ace4745508ceb191bc5d2378aa4665988d2b311a4662332bc00248c8c52290d45922f46a434d648b23211624521a69e450dd08a1b211423521a686448d3c8951a11234321a4aa443190885b490d24f
def ff_top_17 : Nat → Nat × Nat := unpackForestF fc_top_17 12 11
def ci_top_17 : Nat := 0x8440600eb74385c0e069341a0c24b2410480359a0d05328140922c140a04212080400400
def cv_top_17 : Nat := 0x11f1548f0be46e592352b91d1548e22ec6f15635acd1a4668feb7c7b5ae3bacf1cd638d8b346657a3148b0fa3f8852fc369162f46b16c6489932c58916254c9153748a5b24489962846b12a34899a7c48d0e228c910b69
def hi_top_17 : Nat := 0xc7ddb9b0bdaa9e8db6c5cdb9ad5eb65aa6a5e1ae9eca85f79a017132940da97d8c4dbdf0868191737f39c1d27791bdea714989926aa1b5aa63c1b5b85d41ada05619a9ca4fe5b18d4c5d04e244428e073e49797e37adc1a7332939212a428a3a25e91d16246468611f412949182db5c511c9b1990d390d2404629a3600011518
def hv_top_17 : Nat := (Nat.lor 0xb8e4bbbf88bdfc45eeee249319df8c49229f24eb602400921222176cba5d2ed974ba174ba249124924848492492e9dd277318c19c74e9cce624927bf88bdfc453b8492eeee249319df8c91b4004815555a4922e85d2e89244924921212492492e9dd27748c60ce3a74e67312492f55289249451248109265205124a28925d24d9249262bd25e88a770925dddc492633bf1892453e48002aa800016b12492005d48ba5db2e974bb65d2e801248120049200e9cc06300399cc4924bd5400e4bbbf88bdfc45eeee249319df8c000aaa006d000ba917402e960004920108124803a730061c1cce624925eaa00006c494480012040097493649249880725c0114f0eeee249319df8c49229f247e85249022e974ba5d0049208010092492430018074e9cce62492777700249777712498cefc64892492024914fd564922e974ba5d492249242492492492e92748c60ce674e9cce62492524bbbb924bbbb8924c677e3125fa8cb632a7ed8329942ed974ba5db2e9742e9742e974ba5d024848490924924818ce18c18ce19cce6733989249efe22f7f114ee3bbbbbbb8924c677e32564ac16b10b0924174ba174ba5d2e924921212492492e92748c60ce3a73399cc4924a491dc7777777712498cefc6b5ac049092d6258bb65d2e976cba5d0ba5d0ba91749249242424924973abb98cee6318338e9cce67312493dfc45efe229dc725ddddc492633bf195acad62d6b5824974ba5d2e97522e976cba5d2ed974ba4924924924924924b99cce8ce633b98cee63399cc4924f777725ddfc45efe4ef77712498cefc62e974ba5d2e974ba5d24924924973399cce67339892497aa909242494492e926c924931eeeeeeeeeeee249319df8c49229f240000000900001a4336d9949a6db329340038643dd6ee3c400690caae553155caa62a954aa553dc403fffffffffffffffff8ff9ffff00000000000690ed7626daed6001d921f5adc6dc78dbc0034865572a98aae553154aa552af154abc01ffffffffffffffffffe3ffffffff0000b1d93400015b61a1a56d80900000e3c789a43dc4de002a8c6552add954aae553155caa63dc403fffffffffffffffcff9ffff00000b1d93400009b61a1a26d8000e1f1349b77c4d26f126f1002a8c6552add954aae553155caaa5e2a957803fffffffffffffffffffffffffc0000063000000480004acfaade27d3ef1001a5d77765572a98aae553000d21ddddf154abdfffffffe01fffffffffffffffe00d00000854287d3e803278bb11443c0faeeec338e6731fc07fffffd800000c40000000176160163b0002cb04ac695da48000200d2ebbb3766eeec00030e034876f66b7bbbbbbe2a95783c6001ffffffff7e45fffffffffffbffffffff1aa16003004004d02d20cbc65e0032834b89b77c552a954aa00e0d21956ecabc552af7fffff87fffffffff8ffffffffc00002ec0000120000b484aa578a54cbc400697136ef8aae553155caa6001a432add9578aa55effffffff000fffffffff1ffffffff803404db000011a6511a6502c9b44a0024e07c4deb70671cce6e2a9fc07ff7fffff7917fc0000062000009a585da4958c00012a00016b025402eed24000100697136efac95e295e200018701a432add954aae553155caa6e2a95783c6001fffffffffe3ffffffffffffffff00434382d9f6eeccb67dbbb001dddddab1ab4802cf173399ccf7e7c87df917ffffeffc06326934b000effe1fdffffc00868764db26da56382a560a95b58ca9532c16d60012a652ed200ee252bc5cce67339bcf90feffffff00001a32d86a0b60082d9949a65b829340063000038f1e3c4aae553155caa6002a8c6552a954aa553dc7ffcff92001fffffffffc7fffcffff8000012000075b3a934eb67526800d2180240001478f12ab954c5572a9800690caa552a954f71ffffffff00ffffffff3fe7fffc00090b26d93400690ec4db1349a4d3a934eb626d811e452eee3c5cce6733a97fffffffffc0000001d81200000000b580ea00490000b01a43b5c962b25bb254000270147922525c78800061c0690caae553155caa62a954aa553dc43f8003ffffffffffffffffff8ff9ffff00000b26dd800690ed6b589a4db2150b6b589eee3c6cf59bb73399cce6fffffffeffff (Nat.shiftLeft 0x8a4012900124902e9742ea45d2ed974ba5db2e974242492492492490ce3a733b98cee63399cc492771c9777f117bf88bdddc492677302aaa4092002e9742ea45d2ed974ba5db2e9742424924924924924338e9ccee633b98ce67312492f550249940d8d8928a24d8d89249b492492e926c9249313 12288))
def cur_top_17 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_17 cv_top_17 9 511 3 7 11 2047 21 2097151
def hint_top_17 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_17 hv_top_17 32 8 10 1023
def fc_top_18 : Nat := 0x251ac64bd1849453312e16c25b8cc4a2978944b312c4662512bc4a206094a2f92945b2528ae4a514c9440a00092b242ade4855ac90ab392634324b4a848558c90a35923b5b2476a648c91090a3192145b24348848514c00493920164
def ff_top_18 : Nat → Nat × Nat := unpackForestF fc_top_18 12 11
def ci_top_18 : Nat := 0x88211842017c5f07c1e1781e0781e0781a44290040100400f1384e0380e0308b12c0b02842808002
def cv_top_18 : Nat := 0x25e8c32e16c96e334b119a558bf2a45b94e2bca514e65adf31d6b986b3cbf58e5d4cd2d25e964b34ae57a5603128814931a1c96952486b723b53919224869124fadf2756b936b3c9558e498d722c639122dc8514e382e920164
def hi_top_18 : Nat := 0xda499de3d39175aecfe0f0ecc879a1dac17985c0b909ae1cb0d9c20ca8a5aa0da37cf14a9e21c9579635d1fb8f6dd1b28999c97584b1013a7ca19a047442aa1868c2b2e05e9ab28a5e181c2057e9b18c4ef2b63e4322b2f442ac1c1d41f8242d3bb1ad92328ab64a2826aa992085ade8149eb6fa0d8991c50799c97c000291e6
def hv_top_18 : Nat := (Nat.lor 0xdb2e974bb65d2e85d2e85d2e974bb3723b81333993333333204b86218ce19cce67339899c957f88a55fe229c550abc55e2af1578f7133b9ad6b018c8318b59162ed974ba5db2e9742e9742ea45d9cc99cc90cc9cca999999732bb98cee6318733b8e9cce67313392aff114abfc4538aa0d2e2af1578f7133b99595ac5ad6b06318ba5d2e974ba9174bb65d2e976cba5d99999cca9977266e4ccccb99cce8ce633b98bb92e67313392af1578697157f88a55fe4e9578abc7b899dcc318c65d2e974ba318c7c78f1e3c78b99cce673399cc4ce48a45229148a45229148a4522914b91499dc800aaa00080002e96092400012608a33332000006303b83a4e9398ce5531239200079e1fffffffe7fc9fff055548124005d2e85d48ba5db2e974bb65d2e8664e654cce64ce64cccc863395472aa7319caaee633b98c63398ce553126724ff3fffffffffffffffcff93ffe91b4004815555a4922e85d2e8924a64a4486629948ccccba7749dd2318319caa3a4e9398ce553129c9ffffffff3fcffffffff3fe4fff8002aa801b4002ea45d00ba58004ca2012613332000e554e630018c0ee0e633954c48e4807fff81e787fff9ff27ffcba5d2e974ba5d2e976666666666665cc672a99caa67319cc672a9893393fffffffffffe7fc9fff2e974ba5d2e974ba5d9999999999997319cce67319cc672e9897aabb9260c63183191918c62e9acd6633bb924abc55e2af1578abc55e3dc4cee63798c4531bcc60015540010000b52c12480000001e60ee00eee9ddd3bbdbbbcc00024c11466665dcc00000e60770777774ef37772492ee4bd54000229e09243e1f3fbbbfb914f71777705554812400652e85d4ac5db36ad4bb765e83cddc1ddd3bbcddddde6f3777779bcdddeddde6199399533399339933332ee61e6ee3bbbbcddddddddde6e6779bbb92497725eaa71541a5c55fe22957f88a55e2af3fbbbfb914f717777497a00240aaaad2492d432974492777774e9ddddd3cc1e6ee0eee9ddd3bbdbbbcd4c94890cc5329199997733bbbbbbbba730f3771ddddd3bcdddc924bb92f555e92f4453862490f87cfeeefee453dc5dddcba4c999c00002c54c00ba958ba8d2e8003bbbbcc1dc0077b777000777779bbbb8f3733bcdddc920034b8abc55e2af1579fddfdddddc001554017a001752b00b52c00001ddd3bbcc001e60ee00eef6eef30099440090984cccbb98001dddde600e60770779bbb92497725eaa0034b80229e055e2af3fbbbfb914f7177770ca6502cbb76165db2edddbb63a4d4ed44d5e800f37707774eef3777b7779bbbbbcde6eeeef3798664cccce66e6673267325dcc3cddc777779bbdbbbbbbcdcceeeeee4925dc972e9c550abc55e2addf157f88a55fe22bfbbbfb914f7177774681333a3499373715400002cbb65d0046a34ba6e6000ee9ddddddde60ee000003bbbbcddedddddddc79b98920055e2af156ef8abc55e7f77f7777700000b2ed976cba011d01005d00001ddd3bbcdddeddde6000f30770000999999b200484c1dcc000eeeef377b777007303b812497725cba0055e2af156ef80229e0feeefee453dc5dddd24acbb65d4acba9248492f509245d4e3cdddc7774eee9ddeddde6eeeee9e6eeeee9d4ccca28ccd94895325dccef3777777774ef6eeeeee9cceeeeee4925dc972e8f87c9243bbe5e88abd27f777f7229ee2eeeeacad65db2eda4e8d46a351b654d1b9bbcdddddddde6eeeef37777779ba95de6eeeeeeef377b7777777779b989255e2af0d2e2addf1578abcfeefeeeeeeacad65db2edda4959756a597ab55ed8bbb4938f37771ddd3bbcdddeddde6eeeef379bbbbbcde73333328ccd99cccc99ad664bb99de6eeeeeeef377b7777779b99dddddc924bb92e5d2af1578697156ef8abfc452aff115fdddfdc8a7b8bbbb974ba5d2eb8f37771ddd3bbcdddeddde7333333333332ee6779bbbbbbbbcdde6eee4925dc97aa9578abc55e2af1578abcfeeefee453dc5dddc000000092522400bb65d2e976cba5d4920002400924924000c60074e9cce624920077f117bf88a925dddc492633bf18005550004000174b0492000084092492400030e0e9d399cc4924bd5400008000120400a24a249749364924988000453c124bbbb8924c677e31248a7c9 (Nat.shiftLeft 0x5ac9fa06318c3bb85d2e85d45d45d2e976cba5db2e8664ca332664cccc818c063246318c8c6318c633bb9c5506971578abc55e2af1ee26f318c6f2a99dcceeeee194ca3dbbbb85d2e85d2e974bae4b9219933333332ee603180c6318c6319ddddddce2a855e2af1578abc7b89bcc631bcaa6000c0005d2e974ba005d48bae5c804ca3333255e2af000d2e2af1578f717770c646316b22c5db2e976cba174ba17522ecc9992199328cccc998a6318c0060c630192318c633bb9578abc71541a5c55e2af1ee26f318c6f2a995959dddddcce5d2e974ba5d48baeeef6f3333328b92e4cccc98318c19248cee63174c6319ddcabc55e1a5ceeee55e2af1ee26f318c6f2a98c633f54b6d2d4fdb0653285 12288))
def cur_top_18 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_18 cv_top_18 10 1023 4 15 11 2047 21 2097151
def hint_top_18 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_18 hv_top_18 32 8 10 1023
def fc_top_19 : Nat := 0x27b6de4f6dac9f53e13db6727b6c64f2d109e5221344532736964ea9649d52893a2342736864d09989b6b3136c6626d6d64dad8c9b5ac93425e269ad64d358c9a5b313424e00125e4cc590946b7932154251ad64c45f0946b3930154
def ff_top_19 : Nat → Nat × Nat := unpackForestF fc_top_19 12 11
def ci_top_19 : Nat := 0xa86a0a46818d63080e0080200789d16c9b06c1b06c1b059560581604cc8b20062180421002208002
def cv_top_19 : Nat := 0x4ec9d27d4f93aa749fdb7cfcdae7c6cf3db639d1334f4d12734ed3ca449d92ccea946744693bb4b9cda1ce359a708cd37b6b9b9b1cdad666bad7355639a5b352f5be95ad749d67a3ab1d191ae838c740c5b9e229ce499a6c4bd3424e998b24aa052642a92a014988be4a6052602a929014
def hi_top_19 : Nat := 0xb2640c15b2640000b1b0242db0b42c3fab616555a46dc1bd9a429e8b95d10d1c95d0000095c00404947040548e9d2975875db5d081a1956f7a91c9c474a53d7b702135216a5181746331c1c85ded0d5159dd150452f5a5ba4b6da9e24601755b4039b172376eb2332f59d60522aebb2b1b09e5e91076baa50981c9bd0002b260
def hv_top_19 : Nat := 0x2aa6d2aed555cc55eaad893493699f8aaacad65db2eda46c928924924d89249749249b4bbbbbbbbbbbbbbbbbb92fddddc9775df7777124f97e77775656b2ed976d22b516a655a9956a5d92492912492492492492492492eeeeeeeeeeeeeeeeeeee4924f777725dd77ddfc45efe22924bf3bbbab2b5976cbb7692565d5a9632ad4cb62eed24492492492492495a92484921b1b12514492e926c936362492b52492497777777777777777777725cba4924bf777725dd77ddfc45efe229249248a7c97e77772524acbb65d565d498a98a9232a36a48465122ea084924971c77777727c8be45f22fae7726d62e974da6d7777ffe725595acbb65db4acbac55ab14cb6b1956a6562dac2d4329956a652ed208492495a92e38eeeeee4f917c8be45f22f39258a8cb632a62d8329942ed9949a5db62934329742e974092121242492492eee3b80eeee3bbbbbbb92493dfc45efe229dc77777777124bf3bbba564ac162092496a194ba176c5db124921212492492eeeeeeee8771dddddddc92495e97a3b8eeeeeeee2497e7777b5ac049092d6258bb67526976cea4d0ca5d0ba9589249242490924925ddddddde6e8771dddddddc9249efe22f7f114ee392eeeee2497e7777b194b19424b2ed85d2ed976cbb77644d4ad6b5ad6b1349b6569d6d6b0124924924bbbbbbbbbb93dde45f4ef917c8bce00048165d2e976cbb65d0b16108b1602c1d402e84924848eeeeee3b84f77917d3a117ce7b5ad6b2ed976ecdd975248da95922ea24924924924925dddddddddddddddddc9249eeeeeeeeebbe5e97a2497e777756b2b58b5ad60925d2e9752b58bb7626976ed624924924924924925dddddddddddddddddddddc9249eeeeee4bbbbf88bdfc9deeee2497e777711f5090134bb65db2e84d32964ad626d89a4d269b49a85b136c4924924924bbbbbbbbbbf917c8be45f22808fa07d000ba4d2ec00b256002693426a140242424924771dddddc22f9e45f229349a4d3ea42d8fa90b60ca7d009212174ba42ed976cba49249212124924bbbbbbbb8ee3bbbbbbb924f7f117bf88a771ddddd77c492eeee7d3ed9749b65d2ed976cba4d09a4d2693426d89a89a89b62492492492492492492eeeeeeeeeeeeeeeeeeeeee493ddddddddd77ddfc45efe22924bbbb974ba5d2e9249249249092424944924d924977777777777725eaa4924bf777777777771249248a7c97e7777000000492492002ed974ba5db2e9752480001dc1146666400090074e9cce6239001ff1147fc454921f0f8f7133b98005550004000174b049200009304519999000003181dc1d2749cc672e9897aabb9200000006301801249248c5d359acc6777248000453c12487c3e3dc4cee63798c45198de630640192400924602e9742ea45d2ed974ba5db2e974332732a666e4bb93333218cf2d1ec9cc67b392ee6312e673133938aa0d2e2aff114abfc452af1578f7133b981555204900174ba17522e976cba5d2ed974ba19939953339933993333218ce651ec9cc67b3b98cee6318ce633974c4bd55dc90318c650359248c6358d6318c631b4c6318c62e9acd6633bb924e2a834b8abfc452aff114abc55e3dc4cee63798c45198de631b6c0630024848482ed974ba5db2e9742e9744927725392198a65233332e9dd177248633cb4749d27319cba6253923fe228ff88a70c4921f0f8f7133b99236800902aaab49245d0ba5d12494c94890cc53291999974ee93ba4630633994749d27319cba625eaaee4a4649249248c60318c6504924923174d66b319ddc92bd25e88a70c4921f0f8f7133b98de63114663798c0000016b24918c005d48ba5db2e974bb65d2e804ca200ee1333200f64e6301200e633974c5c7720034b8abfc452aff114abc55e3dc4cee600055500368005d48ba0174b0009944024c26664001ec9cc6003181dc1cc672e9897aabb9200006b24918c0006301800c5d359acc677724800d2e008a781578abc7b899dcc6f3188a331bcc6
def cur_top_19 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_19 cv_top_19 10 1023 4 15 11 2047 21 2097151
def hint_top_19 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_19 hv_top_19 32 8 10 1023
def fc_top_20 : Nat := 0x29e8ba53d154a68b314dd6629b8cc5345780049994c264268ade52c9509a2b594a27c268ace522d2ca45a1947b5428f4a84d158ca352213446b28b4a850cd7ca19ad94426c2866ae50cd4ca11a21422442688c65049109a22d940264
def ff_top_20 : Nat → Nat × Nat := unpackForestF fc_top_20 12 11
def ci_top_20 : Nat := 0xa0262982609099b64181601625814250140489203ccf0348d0304c0300b12c0741c0431001304001
def cv_top_20 : Nat := 0xa7e2ed3d1569cacd4dc66a9eb7d4b5aea3acf50d63a812f53a59a9a2bd0906b78831b7616d440a74c264a592a4d693a944f938a5ca49a5d22d0e906a947a549a9274de9ba8d48945a54a2136514d7e896b743b57a19a9d0ad126e4dd422449dd3b4da9b28248940264
def hi_top_20 : Nat := 0x9ee199a295d1ae448fd9817e87a5b20d7f1dae2277197601713dc97769d685da6361b19d599e9a7152d1cdb34992aa504948081248c0182243d5793b3dc1c985361a8dea2f69c1ac25229a922520000024fc040924b4101224b4000023d824372320202e1e4171381815c98b103e8df6093dc1c000268e460024000000000409
def hv_top_20 : Nat := 0x1252a9524a5528092493f5592491747b2ea492494e739a9a494eee6e92748c62dcce9d3dba95cce649218c634921dd8c6318ccee652a954afd465b1953f6c194ca03bd85d70ba5db0bb65db2ece73339cc939939ce73bb985db86b0c670ce6733dba95cce62af9948a55f7e914329542a994aa652add974ab32acccee64ac9582d6305849245d0bb6249d2489cc9ce739ce77737493a4630671d3dbdba95cce649206306318c776318c6333b9ad6b02954a83294b5916b45d2ea45d2e85db2d22ece73339cc939934a73bb9b9f5dcc677318c19c74e67b752b99cc55f1914abe322832a8348655bb1954655199dccad656b16b5ac2954aa5b2ed976d175174bb68bae93bce739cd29ce73339ccceee6e6733a3398cee6b77bb7b752b99cc5519546348655f1914abe34e956ec6551954667735976cbb65db2ece739ce739ceee6e673399cc677bb752ba95cce630a53194a194a8c94a6777315298d3529bbb2a954aa552add974ab32acccee652f988a6f5298000000092522400bb6c526976d8a4d49200024009249240001dc1dddddddc249201dfc45efe22a497777124bf3bbb800aaa00080005a9609240001081249248000000120400a24a249f4936492400071c1dddddddc97aa92492e000114f0492eeee24924914f92fceeee1401290012490329742ea562ed9949a5db32934242492492492491dc77777777777777772493b8e4bbbf88bdfc45eeee249777705554812400652e85d4ac5db36ad4bb763284849249249249248124ca06c6c4945126c6c4924ca4924926c9248ee3bbbbbbbbbbbbbbb92f5524925cee392eefe22f7f117bbb892492453e4bf3bbb9d6c048012424442ed9d49a5db3a93432974492249249090924925dddddddd3a1dc7777777724927bf88bdfc453b8492eeee2497e777748ca00240aaaad2492d4329744922492490909249249289249451248124ca05124a28927d24d92497777777774e61dc7777777725eaa4924baf497a229dc24977771249248a7c97e77772e9b4bb64ba6700000b12400ba958ba5d000362492fd24936401dddc77777777725c0392eeeeeeeee249f2fceeee00000016b12492005d4ac5db62934bb6c526801248120049200eeee00ee0eeee124900e4bbbf88bdfc45eeee2497e777700055500328005d4ac02d4b00024900240812480001b1251200048100249b249200eeee038e0eeee4bd549249700e4b80229e1dddc49249229f25f9dddc56ab40d965db2e813760adb2b52b52b6c04924090924924924924771dddddddddddddddc92493b8eeeeebbeefe22f7f114925f9dddc329940b2edd85976cbb776ed8e9353b5134ca004849249249249248124ca04928925d24d24d9b24934934924ab4924924771dddddddddddddddc972e92492e771ddddd77ddfc45efe229249248a7c97e7777aad5522652c9b5573157aaa89f4cfc5500000b2ed97400ba4900024944974924bf4803bbbbbbb8eeeee4b80777775df7777124f97e777700000b2ed97400018b662a62a62d8ba5d24924009249240900007777777700770092480777775df77f117bf88a492fceeee0000165db2ed974023a0200ba0012492480120400000925124ba49b240009020049007777777701c7025cba4924b80777775df00453c092492453e4bf3bbba495976cba8a4750ea753a9b4ea124a44974ba4924924924924924924bbbbbbbbbbbbbbbbbbbb92493dddc925d77ddfc45efe22924bf3bbba495976cba9597524909232a1248ba89249249249249248492144928a24974936494512494492492eeeeeeeeeeeeeeeeeeee4b97492497eeee492ebbe5e88abd224924914f92fceeef55
def cur_top_20 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_20 cv_top_20 10 1023 4 15 11 2047 21 2097151
def hint_top_20 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_20 hv_top_20 32 8 10 1023
def fc_top_21 : Nat := 0x2bf8a055495caf5b4155d6f2bb4a85575acae1b815c27c2abace56b160ad5ac155d632ab6d6556da8aadb31582342ab6c6556d6cab51a155b532ab4dc5549340049b95416429aade54c550a6ab595217c29aace544550a6ab194d25e
def ff_top_21 : Nat → Nat × Nat := unpackForestF fc_top_21 12 11
def ci_top_21 : Nat := 0x95650906408c6308c212842107c9f07c1f07c1e1781e0745d04ac7b1c05214041100130400100000
def cv_top_21 : Nat := 0x2cbcf56557ab263d581182bf8a15eb68aed2a572dc2b84f95b458ad5ac5608d2ad4695e56faeab5d6f59eb4ac759b6bac9b5562d9aaf6c75735bab1a9d569bb03adf8056bbeab3de958ef28d576c52ba937da699ecc4bf5f257aa926d3e5d2a82c953154a90be53c5929c2b951154
def hi_top_21 : Nat := 0xa332966ea1b060609e2d00e19d183c4597c119569640586094e44c579039252b8f00484e8d30707489311d008488dd2a7d6991c875d1bde674c448437114d8ec6d00dd056bac48556714d92661e5854c5b1189b553d97dce4de9b97c44b6a24d3cd1c1f92fd69f3f2879cdd71d06b6dd1589e1df0bfa866404c16dce00016130
def hv_top_21 : Nat := 0x10924249224b8eeee3bbbba74eeeee9dddd3a7774f7776ad2495a493bdcccca5348928cde64bb9366cbbbbbbbbbbbbbbbbbbbbbbbba95d4a5e6ee47c3e5e92f4454927f777f722dddd9ee2e3777700492bbbb062cddddfc8be4501554045d800008d10a8501248dd900ccbb771dc72e5dc22f9e45f2285d994cb6b3bbbd9dc55542417776194ca592b590b636a35ba6d42a16c6db1bb2139ce649b666edddddddcb977f22f917c8be452d6102bbbb46cddddfc8be450bb74eee6532a44bb9148a8da021556d2b48542a492491a194ca2491bb2a6522426aedddddddd399cb977f5e45f22f9142d626cc1de64d7777ff00b256bbbb0bb62cddddddfc8be45015540da0597600592b0023442a14037640332eddc1cc3b8e5cbb845f3c8be4510a8542a150a2151a85469bbb42a14da91b6eeec00bb7762cd8ae5dddddddcabc55ef22f914329942ecbbbb42a150a65b195195196d7777777605c26666cd99b1663b8eeeeeeeeeeeeeeee5dc9c550abc55ebbbb2aff114abfc453dc5dddd0a8532a15216c85485b065329764ddd92ecbbbb777723b8013aa99cc26666cd97725ddc8ee3bbbbbbb977255fe22957f88a71542af157aeeecf717777010a3750a176038ee002150a856ea151a6eec0da22cb10a1942eddc9b9771dc772af157822f88546a15ba90a85492377625e895ab4855646ceeddd4cdae5dddddddc7c3ef22fa46a16c85b215c2ec23bbba151a8546d90b6490a8537761b57a2150b77769246ceeddcdb372eeeeeeee55e2af7917c8a00000000059777600085aa8000ee2151a85469bbb000071dddddc772ee000055e2af5ddd9578abceeef777777768510a216c90aac4ddddd999999ccccd9bbb2eeeeeeeeeeeeeeeee4bbb92eeee4abc55e2af157aeeecabfc452aff114f71777771dddc7774eef77777776ef739ce6ee5ddcddddbbbbbbbbbbbbbbbba95d4aee5d7772a954aa552a954aa557f777f722dddd954aa552ab955dddc000000124a5494aa50007700492009ce6673994929ddcc002ec01d3a7b71cce6001f8c8a3f1915248776318c6333b98005550004000174b049200009304929ddcc0000c60770749d277bb752ba95cce60000300002954a0600494a9252a777315298d3529bbb00008a782490eec6318c66773297cc4537a94c23240192400a552a52980bb65a45dbb77bb2eb939934a739ccce7333bb98671ec9cc677bb7735bdba95cce606550690cabe322957c6452add8caa32a8ccee6055548124005db2d22edd974bb765d2e939939a539ce73339ccceee619c7b27319dcc677319deedd4aea57339814a631940d63594a92325298d63594a652a94c6d3294ca552bbb98a94c69a94ddd832a8348655f1914abe322956ec655195466773297cc4537a94c7db018c00a552a129448493a4ee176c4929ce667399273124a777374ee93bddd8671d2749eedd4aa5733987e3228fc6450631248776318c6333b99236800902aaab49245d0bb624929a29224e629a494eee6e9dd27748c60ce3a4e93bddba95d4ae67324652a52a952494a94aa5030a5318ca6048ca54924a54eee62a531a6a53776bd25e88a0c62490eec6318c66773297cc4537a94c000aaa00005aca552a5298c01691741dc0002694e73999ce667773007b273182ec01deedd4aea51cce6001a432af8c8a55f1914ab7632a8caa333b9800155400da005a45d00ba58004d29804984eee600f64e630061c1deedd4aea5733980000d652a494a600052a940c00eee62a531a6a537760034860114f02add8caa32a8ccee652f988a6f52995959ddddccf65db2eda45d777752bce739cd29bbbbceee6614a6528652a494aee67773294c69a94aa32a8c690ddddcab7632a8caa352f98dea51fa24924087002e8092539ce6009253bb99600601d3a7b71cce618c63004921dd8c6318ccee6
def cur_top_21 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_21 cv_top_21 10 1023 4 15 11 2047 21 2097151
def hint_top_21 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_21 hv_top_21 32 8 10 1023
def fc_top_22 : Nat := 0x2da6b65b4d5cb75ae16dc642db6b85b4d4cb523816ad7e2d56fc5aadf0b551a16a4522aa4ce5a51c0b373b1684702cdaec59b1e8b362c15525f2bfcf457f5e8afe3d160b6f2c78f8582dacb153e160b672c36d85851d0b05b195fc60
def ff_top_22 : Nat → Nat × Nat := unpackForestF fc_top_22 12 11
def ci_top_22 : Nat := 0x88c4213087d371b0d86c361788e4420500793c1e0b8582c160a249209006430148840800
def cv_top_22 : Nat := 0x5b8d42dd6b96e464b6dae5c2d7edf6b76f357b69a9db15fad76fd6b37cb551a5d15fee5ae759478b8a395b31c2d48a569470b42385a39dacfaed6747ab362c58ede2c36c963c7cb09b058a9f2c36d961474b21b7d8cdaec46cf60b63
def hi_top_22 : Nat := 0xb958405772b00002e5600005cac0000b7f8585953b70712a220c1553f41814a3a9011142a1112e566a6bbc04a7aa17e309098ef73033dd283031b54919425eea4aea9f4707a4e594d641789254a287979a63c94d51877c04058ef800001d9810163b30000070616180e0c00001c18000033d0c118314dcd98001918a
def hv_top_22 : Nat := 0x2d7b64e62af58368867e2a8bd5e85d9777604b90b256bbbbbbbb02e1333366c812e123b8eeeeeeeeea5777777772f377271542af157aeeecabfc452aff114f7172abbbbdac6532cd1b624c2123ba7b568219cdddddd4b37f22f914aae4a36d6b58b1604688d094acad6b05ddddddad6b196c65b5ac58b196c651dd5da0086739ce64da65ddddddd4aeeef37f22f917bbc8be9d2ab9252f4dabd46d17abd1ddddccaeeeeeee0e657707774eef777777765d97776ef600120673332f325dc9b365dddddddc771dddddddddddd4aea52f377255fe22957f88a71542af1579fdddfdc8b77767b8b955dddc2ce757489752ba9b8dd591b41d3a74e195c73abd9ec94a65cba777752ba966fefe451b9672c16bbbb9931dddfc8be45b5821b59ddceae757775eb86571d3daeeeded089ce65cbbbbbcdcceeeea5752cdfc8be45f7f22955cda650da6509bbbbbb77b232a5636dacc5b1d4ca753ab158b636d8bb119a294cccbbbbbbb8e4dfc8be45f22f914aaeacad77776959d43a9d4ea6d3a8e5dddc9bbbbbbbb9999728d9b2912ee4bbbbbbbbbbbbbbbbbbbb979bb92af15786975ddd957f88a55fe229ee2e5577775636ab1b4b1b4db6092e3bbb8eee9d3bbd9eceeeee75777777b3daeeeed2bbbbbbbbb77b999928cd22524f325dc9b365dddddddddddddddddddddddd4aea52f377255e2af0d2e2aff114abfc457f777f722dddd9ee2e55777749209032b995c71d3a7776ebb75ddccae65bbbbbb7b9ce64c9972eeeeeeeea5752cdfc8be45f7f228dc1246d0cae3a74e6d76ebd9ecf6a64ccb9777752ba966fefe451b865465420ca89bbb4addd3158a9249232995249232d8bb14d14673332eeeeeee3937f5e45f22f9146e194ca27b4194ba2af06d27db3293699f8aa9257776924194ca3b92e5dd2bb492999945cd9b33992ee4bbbbbbbbbbbbba95dddddddcbcddc8f87c92577763fe228ff88a7b8b8ddddd0922eeed5a495ad6b196c9595a5333294ecd9992e4bbbbbbbbbbbbbbba95dddcbcddc8f87c92488b77763e1f1ee2e37777
def cur_top_22 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_22 cv_top_22 9 511 3 7 11 2047 21 2097151
def hint_top_22 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_22 hv_top_22 31 8 10 1023
def fc_top_23 : Nat := 0x2fd47e5fa8dcbf51a97dc702fb4fa55559cbd62c17ab582f68a45ed140bd52a9555632f346a5551a8bc52a97756e2ee6cc5dc8d4aaa29175c682eb8a45549bcba63416a57f2e68b05ccd60b52b9971d7d2e3ae25a91c8b69af97046c
def ff_top_23 : Nat → Nat × Nat := unpackForestF fc_top_23 12 11
def ci_top_23 : Nat := 0xc0602bb4a9648633188c40dc8e06230172b858a190080359a0a650248cc60290d0441201
def cv_top_23 : Nat := 0xb492edfe8feb947b7f237bf51ad731c2b84997e470bed3eda2976b749b5aa3dad926d6b162f78a57b450be62c5f0d62f54ab5a24db392fd9295eb247b79a35bc52adaa99af0add77b66bad37da899ebf4ab77235bb2345d714aab49972480ba6345b1142db8e171c80b9e2c5ccd62db8b17257db8eb8dc0da2dd6a97046c
def hi_top_23 : Nat := 0x817820227f9470797899d1bf7335355969469a7c62b1bda55c75898f5c0c1c1a5960acab53c155684a9eb249438da5c43b35ae1639a0606534a9853e2c01ea2a24a9a9d61c71c60e15f9c19e11354d3108a6962407f0242d06f8303e06a8141406600c120518405204b41819041028290040e4f4002008080020000000000808
def hv_top_23 : Nat := 0xb451b374832b8e9dd5da492366eeee9d7917c8a09c0bb12480db677077071dd2bb49226bd12495dddcccc8ee3bbbbbbbba95dddddddd3a772ebbb831892577763f19147e3228c631b8ddddec4c085ddceae757775eb86571d3abbbb7b4a6bd49e65dc9bb777779b99dddd4aea59bf917c8befe4518c6e91b400481555ddddd3a777774e0e657707774eee95a492b2ec49277b48a48935e89249dcbbb9bbbb7777777774e61dc77777777777752ba95dcbaeeebd25e88a0c62493fbbbfb916eeec6318dc6eeee000169580003bbbbbdac176000164a77776c59962b166401dddddc777000772ebbb800d21dddd957c6452af8c8a5519546e5577770000077777b005a567726805929bbbbb93664d9803bbbbbbbbbb8ea5752bb975ddc00690dfddfdcaa32a8caa32a8dcaaeeeee49bbb805899dddd85d8e401d4af37777779bbbf917c8a557000b1330074e9ecf677746bbbbbddddbd85a613725ddcddbcdcceeeeeeeea5752bcdddfc8be45f7f22954aa557000555003680000eee9d3bbd9ec000e0ee000169580585d83bd8059298040772eee6eeec01dddc01cc0ee0eeeeeeeea5752bb975ddc00690c0229e0feeefee45bbbb2a8caa372abbbb8c56285d977760eeee0c5b315315316c1777760673629333366ccd8b31dc777777777707770bb938aa1578abd777655fe22957f88a7b8bbbb8653285ddd97776eeec5b195315196c1777761332939dddd996658b323bbb8eeeeeeeeee0eee3b975ddc2a9542a954aa55bbbb2af9548a55f2a914aa552a955caaeeee17613b004eceeea59b9148a37000002c0000b2b480000bbbbb4ed3000071ddc752bbbbbb975ddc0008a05ddd8c6318c631b8dddded6b00eee3bbb85ace16b5da57768bb2d2b3299664ca65990cb332994b59232ceeeeddddddddcbae8771dddddddddcbaeee55f1914abe322832a8348777765519546e5577775656bbbbb4ad1a234ca8d32a347725cbba577776a667333b1733b366769bbbbbbbbbbbbbbbbbbbb977255e2af0d2ebbbb2aff114abfc453dc5dddd595ad77777695dd8b5ad61ddd2bbbbb539dac94eeeeed699b4cbbbbbbbbbbbbbbba95dddddddddcbaeee55195463455432adddd957c6452af8d3a5519546e5577770000bbbb000062d98a98a98b60bb00009999b3667325dc9007777771ddc000bcddc801578abd777655fe22957f88a7b8b955dddc000b200bb2ec00b19400b58b19407757683302739cccc8ee3bba95ddde6e117ceef22fa74aae000006d100000000383b803bba7770002cb0bbbb77b0330009ccccbbcc9772e4d9b200038e0eeeeeeeeeeeea5752979bb900008a781578abcfeeefee45bbbb3dc5caaeeeeeef610b32c5b2f53995ddd29a95ddd4de6a5b2f53995d59ded7333a95ecef65764e9de667257abdbbbb777092c95aeeec0086610bbbbba95ddde6e55e2af7917c8a557b256
def cur_top_23 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_23 cv_top_23 9 511 3 7 11 2047 21 2097151
def hint_top_23 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_23 hv_top_23 32 8 10 1023
def fc_top_24 : Nat := 0x3194ce63b9d8c76bb18ca5f31acf46355e8c652b80093f3172c860f5bcc54aa183d6b3132f860f59cc44aa183d633072cc61d198c1caf1838183088be61116cc222b9844533070280024ecc12341822652aaade603160c052a95556b
def ff_top_24 : Nat → Nat × Nat := unpackForestF fc_top_24 12 11
def ci_top_24 : Nat := 0xd0340c8b20c8302a228098a6090a4088a20809f17c1d2741d0741d074194334b1248541404101000
def cv_top_24 : Nat := 0xc7b3b63b5db1bcf58d57aca6b7e4f5af25acf91d63c8937e3e99f1c4bf8ca57c5cb2616053152a985014c4cbe612053112a9840140440ae1d1981002b85c5fc2a2de1315f088a78b56fc52b5e2559f10ac787966c34af4281ade40c6de85b5182981e0970c03183814af51ed7b1a2f18a182c68bc228608996bc49b5da4cc0a2c594997014ab5d24d
def hi_top_24 : Nat := 0xd49ca4aecfd50532c42e8aeabf4d0d38bc94a4aeb28a9a83aa9981fca489c9849c3a9a14952db1c389fea2cc82d5d5ca78dab27f7231c9aa6922aa4460b1ba1c58e9c9f250e5be014bccf946471d992c40e5a18e3addb18235c1a9473208e0ee2b1d85bb24ddc590205d1d20181a92111095c1e10b75194800768ac00000181d
def hv_top_24 : Nat := (Nat.lor 0xc8be45f22fb8248da39744e9cbae5d733a992e665d5bcddddfc8bee84921249126cbb65d569248ba924e3bb975c74e5d777774e9ddddd3bba77733cccca5348928ce66cbb92f325ddddddddddddd399ddddd3dbcdddddddcbb91f0f97a4bd115248777cfee457f773dc5dddecbb65db2ed975c7772eb8e5d7774eee679ce732eddcdddcb975cbbbbbbbbb975edeaaeeeeeeeeeee552a954aa552a954aa55bb2abfb915fddcaa552a955dddc0000012492480001dc12480273999ce6524aeeec000ca50074e9ec7bb7319e66001f8c8a3f191524aeeec6318cc677198005550004000596092400012609257776000187074e9edeaaef76e633ccc0000001761600924924eef66eee766cd6000114f0492bbbb18c63319dc66bfbb228eefeecb405a480124ac2ecb4aedeeddeec9cc9a539ce667399bbbb0ce3a733b994aee652bdbdb99cc0caa0d21957c6452af8c8b77765519546677302aaa409200bb2d2bbbbbbbbb2732734a739ce667399bbbb0ce3a733b98cee633dbd55deedcc679982eecca176492bbbb5daeeeecdb77776eef66eee766cd60caa0d21957c6452af8c8b77765519546633ba54d7f76451ddfdd9b6c176009212121dd24e91762494e73339cc93989257776e9dd295dcc6528671d3a7b4f76e633ccc3f19147e32283189257776318c6633b8cc91b4004815555a492b2ec49253452449cc53492bbbb74ee93ba4630671d3a7b7aabbddb98cf3325692492495d85dd9941249249ddecdddcecd9ad7a4bd11418c492bbbb18c63319dc66bfbb228eefeec000002d6492bb00b4ac01dc002694e73999ce66eeec01d3980ca500771dedcc6799800690cabe322957c645bbbb2a8caa3319dd2a6000555003680169581658004d29804985ddd803a730018c0ee0f6f5577bb7319e660000bb2495d8005d85803bbd9bbb9d9b35800d2180453c2eeecaa32a8cc6774a9afeec8a3bbfbbbbb7ea32d8ca9fb60ca652dec7702eeecbbbb9ce6673992732739ceeeec0ca570c60c670ce6733dbdb98cf33157cca452afbf48a194aa154ca5532dddd956655998cee6b5ac1768bb2d645aed2bbb45d9695ce73339cc939934a77776e6577319dcc630e6771d399ededcc67998abe322957c64506550690eeeecaa32a8cc6773299595ac5ad6b177777777695dbba56f6a739ce694e73999ce66eeedcce67467319dcc6773295eedeedcc67998aa32a8c690cabe322957c69dbbbb2a8caa3319dcc318c777777777dddddddd7776e673399ccf6f6e6731148a45229148a4522dbdd9148a452298cee453000aaa0008000b2c124800024c124aeeec00030e0e9d38f6e6730001e787fffffffffffffff82aaa409200bb2d2bbbbbbbbb2732734a739ce667399bbbb0ce3a733b98cee633dbdb99cc7f9fffffffffffffffffffffffe91b4004815555a492b2ec49253452449cc53492bbbb74ee93ba4630671d3a74f6e6737fffffff9fe7fffffffffffffff8002aa801b400b4ac0b2c002694c024c2eeec01d39800c6077071edcce600ffff03cf0ffffffffffffbbbbbbbb9ce739ce73bbbb73399cce67b7b7339bfffffffffffffffffffeeeeeeeee739ce739ceeeedcce673399edeaaef76e633ccd65ddd976ad5dbbbd9bbb9d9b35954aa552adddd956655998cee6bfbb22ddfdd800024900003ba4eeee17600009257776c59962b166401ddddddc752bb8003b975ddc0124aeeec7e3228fc64518c6371bbbb800228803bbcd5dddceae7574e9d3ddddbd802532e5dddddddd4aea59bf917c8befe451b800aaa00080000001c1dc01ddd3a7774e0005960924ef6000101249dcbbb9bbbb0001c7077777777777752ba95dcbaeee000114f04927f777f722dddd8c631b8ddddc1d01765a56093b838eeee1777777764dba58da9376777766d6ecc9b4db323b8eeeeeeeeeeeeeeeeeeee0caa0d21dddd957c6452af8c8a5519546eeee24048195c74f67776ebb75ddccae65bbbb7b9af6d3b4de65dc97777777752ba966fe45f22fbf914aae0aaa9024800732bb83bba777b3bbbb9b5dddddecf62ecb4aeeeeeeeeddec9af4b1b529d8db326d99772eee6eeec771dddddddddddddddddddd4aea5772ebbb832a8348655f1914abe322bfbbbfb916eeecaa32a8dcaaeeee668d4e6 (Nat.shiftLeft 0xac8da09d38e5d0bae5d7339293999756f37777f22fbdac10dad65db2e975cbaeee5d72ebbb8e5d0bae9cce844e6e665dddde76f37777f22f917c8beeac6d563696369b6c126cbb65db48bb765d2edd974bae3bb975c72ebbba7772eb975ddddcbae5d7777733cccc94669129299b2ee4bcc97777777779bbbbbbbbbdbcdddddddcbb92af1578697157f88a55fe22956ef9fdc8afeee7b8bbbba490485d2ed976cba39744e9cbae5d7772eb975ddccf39cc98e665d3bbbdbcddddf 12288))
def cur_top_24 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_24 cv_top_24 10 1023 4 15 11 2047 21 2097151
def hint_top_24 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_24 hv_top_24 32 8 10 1023
def fc_top_25 : Nat := 0x33b6e6678df8cf1be19e23433b6a266299ccda3519b4663366d666cd8ccc52e99967a3326ec664db0cc51f80094732c4dc658598cb00c196014001286654994c66b7994255319ad664c9f4c66b3992255319ac66329bcc82bf990573
def ff_top_25 : Nat → Nat × Nat := unpackForestF fc_top_25 12 11
def ci_top_25 : Nat := 0x9425094223755d0741d07419464190641633a0e0344d034085200711c052140320c0210802008002
def cv_top_25 : Nat := 0x19f37ecf5be6788d339af1a1d72d0ab867edcf3b6a39cc6ace23366edaf366c79a67accdbb664db352ad5a7b6bd29b1e8ed47444df9d267cd52ee628fc1302b97a6ecb8b30240972d03196014ca932e34997284ab9327dc792ee4895721aff90573
def hi_top_25 : Nat := 0xc6bc1013c5386861c3904c6abda9217ab41a6e64ad8189a6a6b1a5b4a1390d5e9cd5251995ada5ca9041055b8b94fd2b849db1be7a127ea373ed79896eb5754e65a5e2446038f95b5bd0f11a5331b6284edd0d154662961f4189053635ae8af730a5154226729a8d20bd456d177e96500ed28a2b0d64445b0bac4c6e000292eb
def hv_top_25 : Nat := (Nat.lor 0xce73249b32eeeee9dddddfc8be45eef22f91492eeeee6577777770732bb8249249090ee8bb6bd3e976cfa2f4ba3dbbbbba490004819bcc977251466665dddddddc771dddddddd3cddddcbb91ff1147fc453863fbbbfb9152487c3e3dc5dddc483a9d4ea9249241b4ba249176cda4d2ed9b49a1711466c59cccc8ee3bbbbbbbbbbbbbbb977270c4921ff1147fc451f0f8f7177773a9d4da91292224176cea4d2ed9d49a194ba2493b91dc0999cc45199997725ddc8ee3bbbbbbb97723fe228ff88a70c4921f0f8f7177770da650a44b2ed965db2edda491b4faad3e9349a753e9d4fa4d26824ef39ccccba72e5dddddfc8be45f22f91400a440b2ed976cba08368841b43680750ea017449dc331d39720e61dc77f22f91422f8924750da753684a49225d2ea49176cea4d2ed9b49b33328a48bbbccccbbbbbbbbba7725ddcbbbb9777723e1f2490ff88a3fe228f87c7b8bbbba4ee241f4bb65db2e87d3289246d3ea14fa4d26b14fac53e9349a4ccccd99d9bb7771c7777f22f917c8be4526935ddd0ae857775eb9b432b8924e8212e976ddcbb65939ccb9777777774f3f22f917dfc8a9247d0fa853e9f4fa2492495976cba924eee5dc99999451bb25dc97365dddddddddddddddddddcbb91f0f92487fc451ff114777c7b8bbbbb8eeee2493bab2e9f6cba5d7b777772ea491f4269f4fa4d1dcfaeeeeeeeeee4d26a492491266665e64bb928a26cceec9bbb7777777777774f37777777777772ee47c3e7f777f722a490eef87fc451ff114f71777771dddc4927745d2ebdbbbbba494e6ee5ddca494cbb37777777777774f557777777718c637f777f722a490c6318c631bbbb80000080002e805d48ba000132694e739cc0000ceee6318c6318c0001e0d219546551954655198c6318c63181dd1672d6458bb65d2e976cba5d0ba5d2e9742ea45d9ce6673992739cc9a539ce7301270c6480c670319d399cce67319e662af8c8a55f191419541a432a8caa32a8caa3319dcc86865d2e974ba3487ddddc977777399cce9cce673399cc45229148a4549d7229148a45229148a45319dc8a95958ba5d2e974ba9176739ce694e739cdcce674e673399cce6ffffffffffffffffffff56562e974ba5d2ea45d9ce739a539ce7373398cee93a7aab974ce63398cf3318318c61ddcc5d359acc631318d3314915465518d219546551954655198cee63798c4531bcc6000451b2ed97400bae5d7772eb975ddd3a7338024e665ddddd5bcddddfc8be45f22fb800aaa00080002e9609240000000ee0e5d0074eee9ddcce000101248bb7737772e5d720000e60770777774f6f557777777777700008a782490eec6fee457f7718c63777712024b2ed97472e85d74e5d72ebbb975cbaeee679af6d3b4dcccbcddddede6eeefe45f22f917dc1555204900176cb48bb765d2edd974ba0eee5d072ebbba7772eb975ddddcbae5d7777733935e9636a53b1b664db325dbb9bbb972eb91dc777772ebbbbbbbbbdbd55ddddddddddc19541a432af8c8a55f1914ab7637f722bfbb9546551bbbbd89810d976cba5d72ebbb975cbaeee39744e9cce94d7a91766e665ddddd5bcddddfc8be45f22fb8c691b4004815555a4922e85db1249d3975ddddd3a777707772e83a7774eee6748a48935e89248bb7737772e5d72eeeeeeeee9cc3b8eeeee9edeaaeeeeeeeeeeebd25e88a0c62490eec6fee457f7718c637777000b133b2ed97400bae9cbae5d7772eb975ddcce16985dbb92f32e979bbbbbcdcd6f3777777f22f917c8bee552a8002aa801b400b48ba005d2685d800003975ddd3b8003b8397401cce0164a60100bb7737772e5d7200eeeee5d01c707b7aabbbbbbbbbbb800d2180453c0ab7637f722bfbb9546551bbbb800001b440000174b0b2ed9740000001dc1cba00e5d7774eee670330009ccccccd97725e648000e383bbbbcdede6eeeeeee5dc8000453c0abc55e2addf3fb915fddcf717777b2f5175cbae9cbaf37999e765ea26d975cbae5d72ebcde6e699252f4dabd46d17abd2ecba5dbb2e9742ed965db2eb975cbaeeeee5d72ebbbb83bb9741cbaeee9ddcce001206733333365dc97992eeeeeeeef3730ee3bbbbcdede6eeeeeee5dc957f88a55fe229c550abc55e2addf3fb915fddcf717777 (Nat.shiftLeft 0x9b30848924ef6e10bbbbbaf22f91492e9749a5d2684d09a08d11a3a25248bb765db269749a91349a4d269949a65269349a134ca252a4ee01 12288))
def cur_top_25 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_25 cv_top_25 10 1023 4 15 11 2047 21 2097151
def hint_top_25 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_25 hv_top_25 32 8 10 1023
def fc_top_26 : Nat := 0x35d6d66bc8d0d75b19aba45359aec6b2dd8d65aa1aba3f3572c400253cd54b300094b35348a6635a8d41b61a82353316d6696db0d2dae1a636134b46a662d8cd21b31a42353316a268b5a0d15a8998a6f33bae46775c0d03401a036c
def ff_top_26 : Nat → Nat × Nat := unpackForestF fc_top_26 12 11
def ci_top_26 : Nat := 0xa4281912409024084e105ad605455048d20480f33c0f03c0e1290a024454140500c8210802008002
def cv_top_26 : Nat := 0x1af234d86b56c159b5f6d7aeb63d6ebb6b4ddb596a9bb466dcdb5eded8f6c693b4a6fd8933eb89175847fab962a80994b44ab552cd9ca4dd4d22e688ff516d99ba6dd411ae98d874e6d9a6b5ccd936e968d73c4cda4b66d1537e7699f4846ba3568d15a8e82dc741d01a036c
def hi_top_26 : Nat := 0xb7946863b3052124aadda60aa4a12d8f9f092d6696b1d6168a86af0b857179457e318dd07701adcc706d95a569c9a5a962c1a1c25bedb9b55750fd274cd67e9f46b5b18841017d6d40dc0c093c15293233d292112cb1a5c82571b1d01dd5ade717fdb17614050cfe0c6e79e60908d4d90261b9aa01b4242b0160141500003c58
def hv_top_26 : Nat := 0x240ba5d700b59ddddde7fffe004c4c05976cbb65d09692d026a4d40b161082e8ef698124c72e4771dfc8be4508be154ab3525b35968acac498c8ccc5d2e976e6a4d2edcb49a5d4ad3332eef3b14673332eeeeeee5dc9777777772eeee4abc55e2aff114abfc451a5c55e2af12af7154bbbbbb860d6b5976cba652eb150ac5329349a6542a158a4d2686532964ac4ccccd99d9bb7771c07771ddde6fe45f22f917c8a5572693559597af3577742ba15ddc732867084ba5d72edbd964e6e665dddde6e604f3777779cdfc8be45f22fb955d0a214ca8542a14565648c64a66b2ed975dc97773691766665dc9bb266517365dddddddddddde6eeeeeeeeef32f377255e2af157f88a55fe228d2e2addf1ee2e557777565671dddc733d9756b65d2eda45d7772ebdbbd1426ad68a4d2d6492b59dddddc9a4d7742bbbb92666666517725e649b33bb26eeddddde6e9e6eeeeeeeeeeef37777777779b98bcddc9578abc34b9fdc8afeee55bbe2aff114abfc453dc5caaeeee00000e67002ea45d7777009a5377779ce73000103817400026000d21bbbb954655195465518007954565671dddc733974ba5d4aceeef6ef39d929bbb977332ecddddddd3d55ddddddddddddddddcaa32a8c690dfdc8afeee55195465519546e557777492743b80924176cba5d2ed974ba174ba2494e73339cc939892539ce6063386306338674e9cce6733987e3228fc64506312486318c6318ccee64922e974ba5d4929ce734929ce7373399d3d55dd273399cce642490eee8ba92b491494d1464318c6924318c6318c667732f4455e90900eeee00924818a5d1248bb6c526976d8a4d0ce6c511466c59cccc8ee3bbbbb83bb8eeee5dc9c312487fc451ff1147c3e3dc5dddc4921ddc12490194ba249176d8a4d2ed9b49a4cca2491b6658b3332ecc77771dddddc1ddc7777777706312487e3228fc64518c6318c6377771202eddc12492487b1249ddc77026ad1248faad993e9f664bb7731dc777774eeeeeeeeeeeeeeee0c62490fc6451f8c8a3bb18c631bbbb8ed71d5bb974bb1d5aad7777777769b5248249bb665c97664d9bbbba79bbbbfbf917c8be450732bb8090ee82cbb760f6eeeee5d492bbb773ebbbbbbbbbb9349a9249240135e8ee5ddca49174fb765d9934fb327d991dc777777774e5d77777777777777770631fdddfdc8a9243bb18fc6451f8c8a318c6eeee0000000900002493bbbbb974ba009247d36cc9f4fb325dbb9803b8eee000eeeeeeee009243f19147e3228eec6318c6eeee00000ef600777772ea48ba00e6d7777b4ed32eddcc01ddddddc72eb99dddddddc01fddfdc6318c776318c63777772003a0b772e803a34daeeeeeee6d4922e93309b92eee522ecc1dddd3cddddddfdfc8be45f228c6000000ee8002cbaf6eeeee5d49200700071c0040084017400772eee5248bb773008000eeeeeeee9cbaeeee00e607707777007f777f722a490eec60114f018c637777269349a9249242403bb8ee174bae175248ca6599329966499944922eddcddddddddc771dddddddddddc7e3228fc6450631248776318c637777492b2ed9752491a234ca8d32a344924927725cbbccce6514665d2e67326cdddddddddd3bbbbbbbbbbb97723e1f2490eef87fc451ff114f717777492b2ed97524922684d269349a2494a924eef39a49176ee64d26cc93665ddddddddd3bbbbbbbbbbbbbbbbb8c631a490ec76318fc6451f8c8a318c6eeee000000090000249176d8a4d2edb149a008a33992ee4cccc803b8eee000eeee5dc802490ff88a3fe228f87c7b8bbbb8090176c4800009a4d09a65012952770cc09cccc8ee3a77777708be777917c8a00000000383b800000840ee80003e960f6eeeee92406600137992ee4a28cccc8000e383bbbbbbba79bbbb9772000114f07f777f722a490f87c7b8bbbb92924eee122491757a5db26d9340219842eeeee9dddc7c3ef22f91448025c824924906d2e89245db36934bb66d2685c451025c266664771ddddd3bbbbbbbbbbb977270c4921ff1147fc451f0f8f71777726ddbbbccceeef73732b934bb64db7726ce667
def cur_top_26 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_26 cv_top_26 10 1023 4 15 11 2047 21 2097151
def hint_top_26 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_26 hv_top_26 32 8 10 1023
def fc_top_27 : Nat := 0x37e6f86fc9f0df51f8009573792bc6f2060de40a0009533774da6af198dd1aa1ba2353576d66e0d50dc5ac9b82353576c66dad98db51a9abb4936a8c86d4d24d5d379b1c7e3638f86cd630d8db99b237e3636926ae99cd76b51aed66
def ff_top_27 : Nat → Nat × Nat := unpackForestF fc_top_27 12 11
def ci_top_27 : Nat := 0xc02d38360080200699a059160581334c130448e3380e0290a0280821c4701c061180510140000000
def cv_top_27 : Nat := 0xe02b8efedf37e4f9d1461e862df3f15f9b6c3cd35be59a5f22d0f8e4dbc3257e0d27f0291f7d47f2e92ad5d2f6f6579bf0b6a4053de80c6f2053774dbb0265d6d1fcb64ab756a9afa55dd11aee2d675e4a9b9354d752aee08d76e6cdb526fd8d33eda8d76b8c9b5349d99b8ecd633646fdb447ed9e3e6c11d3656e7b1b49
def hi_top_27 : Nat := 0xc9dd8e06bdd29f03b6c975c2af11bdeeaad0f110a6e100fca0b1998c9961a5d490e5c61f88bdca0a83352d6276eaaf136f4de5e76f1c100c694959755fdeb65b57b1ae0b4fd9adf6477d9e1740a1d5b73cb4fcfb340eaa2a3008e5012855c9ed27e0181d266c405d2634080e20a50964158e9ec60e11a5df061da5fd00011d87
def hv_top_27 : Nat := (Nat.lor 0xabc55e2addf157f88a55fe229ee2e5577777733a7777707b777770ba174baee5ddc9327399766003b83d55dddddddddddddfdddfdc8a154aa154aa552a954aa552a954aa552ab955dddc00000000002e97522e974bb65d2e976cba5d009cd29ce73999ce66739cc01d19cc677319dcc673399cce6001a432af8c8a55f1a74aa32a8caa32a8ccee6000018c6300eeeeeeee0073399cce673398008a45229148a45229148a4522914cee600002e974ba5d009ce739ce7300072a99cc673399cce600ffffffffffffffff00002e974ba5d009ce739ce730007aab99cc673399cce60001005d02c0204c03000552a954ba552e956655999dcc00450f077077009cd139964176d8a4d2edb149a314ba1752b4d8b30ce6c5265199997771dc0771dddddddcbb92aff114abfc4538aa0d2e2af1578f717777777031916316b22c5db32934bb6c5268652e85d4acc59932cc9332964a732ecdddddc77001ddddc1ddddddddddddcabe322957c64506550690caa32a8caa32a8dcaaeeee0ef760590918c9174c3d8ee0eee5a45d26ad15b359956ab666c94cbb7731dc777777777777777772ebb975ddc19542af8c8a55f1914690cab7632a8caa372abbbb8eed0cee5db72ecb256777776995d5aad7770926ed73325d9936609e6eeeef379b99ddde6fe45f7f22f914aae5900eee65073385976ec2d22ebbb975eddeeeed6492b59dddddc9a4d7756bbbb804d7a5929bbb97725d5add97664d5accbb6641dc1d3975dddddddddddcbaeee5d733bbbbbbb975ddc19541a437f722bfbb956ec655f1914abe3229546551b955dddc0000000c60000772e975ddded22e803158b32c59accd929976ee6000000ee00e9dddddddcbaee5d777002af8c8a55f1914690cab7632a8caa372abbbbb838019c1cbb6e0164aceeef35746cd5ddcba4cc127725e64bb3004f3777779bbbbbcdccf3777f22fbf917c8a552a955c000001cce00165db48baeee5d7b7700b160108071c0070002e80164a6eee5dc976ee60100001d3975dddddddddddcba0038e00ee5d777001a437f722bfbb956ec60114f02a8caa372abbbb9349a4d48ba5d4ad61175201ddc770ba5d70bb69174da6599369b6649994b2532eddcddddddddc771dddddddddddcabe322957c64506550690cab7632a8caa377775656b2ed976d22e9b436994da6d36939a494e6ee4b9779999994919974b99cc9b3777777777777777777772ee4abc55e1a5c55bbe2aff114abfc453dc5dddd595acbb65db2ea45db134269349a4d0ba64923295dde73b2532eddcc9a4d9926ccbbbbbbbbbbbbbbbbbbbbbbbbbb95465518d21956ec655f1914abe3229546551bbbb8000018c00005db62934bb6c526801752b3b93399201328cccc8003b800003bbbbbb979bb92aff114abfc45001a5c55e2af1ee2e55777702c80bb6176c00004d2684d36806494aee1981399991dc77777708be7917c8a0000161000000003b8380399c0005a9605d4aceeef6ee06600139945dc9799333320000038e00e9e6eeeeeeeeeeef32f3772000114f01a5cfee457f772af1578f7172abbbb92eee122b2b23231757a5db26d9340219842eeeeeeeef39b9578abde45f22955c0972059094cc918c2f4ba176e6a4d2edcd49a5d4ac1700970999466664771dddddddddddddddde65e6ee4e2a855fe22957f88a34b8abc55e3dc5caaeeee4dbb777732b934bb6e4d9abcde737313664ab2b5976cba5db134da4d26934ca4d369349a4d09a650c9295dc0219ccccbbbbbcdcceeeeefe45f22f917c8a494ad64ad62c8777777732bbbbb83bb9941cce5db5ead4bb6b517a5d0ba959dddeddc00240ce6517725e64ccccbbbbbbbbbcdcc0ee0e9e6eeeeeeeeeeef32f377255fe22957f88a71541a5cfee457f772af1578f7172abbbb9344b4cb2db58946730ca5d0ba958bb72d26976e5a4d2667326517707724ccc8ee3bbbbbb97725dddcbb938aa0d2e2aff114abfc452af1578f71777796cb65a918c94cc5905db32934bb665268652e85d4ad362cc2e4ca33332eeeeeeeef371dc777777772ee4aa55ffe22957f8ca45229c5506971578abc7b8bbbb8653284c4c5976cb2ed976ee5aad56af49a4d9aab55b2d26936c9581ded39ce6665cb979b99dddddfc8be45f22f914aa55 (Nat.shiftLeft 0x1a60ed768fd76bb5fa175db65d2ecbaedb2eddbd976cba135daed76976eeeeeef4526d149a491dc0bbbbbbbbbbbbbbbb9c550abc55e2af1578ab77c55e2af3bbbbb99d3bbbb865328f6eeeee5d0ba65b2e965db2ebba15dddddddddc9a4d026994ca650a2c749aa8a89ab524bbcc9772e48664ccc9b33bb26eec0077079bbbbbbbbbbbbbbbb979bb97f777f7229c550 12288))
def cur_top_27 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_27 cv_top_27 10 1023 4 15 11 2047 21 2097151
def hint_top_27 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_27 hv_top_27 32 8 10 1023
def fc_top_28 : Nat := 0x37d8ae7395ace75a99ce23537d6c26fad6ce5eb81cbb7c39746a6fad2ce49be1c93643936e27248d4df5a19c7b4b38f6866fa9b4e1e309c3b61387696712e30e251a1c3b433874d86fa95ce123e1c237137d49e7055c0df5239bf571
def ff_top_28 : Nat → Nat × Nat := unpackForestF fc_top_28 12 11
def ci_top_28 : Nat := 0xf8f8f1d4d0d0d0d0ada8a8a89a75707054505050505042401d18180a08010000
def cv_top_28 : Nat := 0x73ad4f9ead7c6267e112ff388d799ae1cc37ce413ef1699f9746bc9b71e253372adf3946c9c7a7de2133f248d790697c7b43e1d336fc8fb8a719c4a34e3630f18d878b697c4343e1d3670b1f3846e3c1570
def hi_top_28 : Nat := 0xc9fd0556c9302033c13db1fdb8819e2fab7abb42a57179829df9c9de99250d358f468e788749c1ff7f41b2027ed81c1a78f941786ce2af066839052a621925885a21a5fe548945664fd10d2e4dfc5c754d7420224cb028314a78748e430991dc37e6a6c93005c9f82a89055f1f4e92cf1809d1d10e52966e080935920001ca02
def hv_top_28 : Nat := (Nat.lor 0x652974c04db135135136ceee4c99f665dbb99349b324d991dc777777777707771dddddc2a9542a954aa552add954abe5522957caa452a954aa5577771c74eeeeeed0077bb7777772e93400b0b2ed975deeddddddddddcca50b56bb49a95a89a6501ddae5ddc801966659974cb765d9934cb32ad76cc8003803bbbbbbbbbb975cceeeeeeee5d7777f777f72280154aa552a956ecaa55f2a914abe5522954aa552ab955dddc3202ed976f765d1246d15922ea26ed2d3b4cbb77349207701ddddddddddddddcbaeee0c60c6318eec6924318c6e3777703192012127777770bb63bbbbb974ba9d226fd1fafd997ead665248bb773077007771dddddddddddcbaeee0c60fc6451f8c8a9243bb18c631b8dddddcc9dd5bb975cdafd77777773abf4329b42912e933997291766900e3cdddde6fefe45f22f9146eee67749dddddd090f6eeeee5d0bb62565d492774eeeeeeeeee90248ca09245d4ee5ddc931248bb77349148800ee0e5d7777777777777777772ebbbbfbbbfb91418c4921dd8d7a22af486318dc6eeee063174c0590eeeeef76176c7777774ad2726fd1fafd997ead666c94cbb7731dc07771dddddddddddcbaeee0caa157c6452af8c8a348655bb19546551b955dddddddddcbaea52d175dddddded615975ddddcbb6939966659b995dddec94cbb7737777772eb98077777777772ebbb9546551bfbbfb8d21956ec65519546e55777772f371dcc9ded6ee5d746bf5dddddddfa194ca59368953725ddcced32eced301c79bcdcceeeef3777f7f22f917c8a552a955ddccee93bbbbbdac590f6eeeee5d0bb65da495975dd6aeeeeeeeeef6b02d4b1956a655a85dda49dcbbb9265929976ee765accad6640077072ebbbbbbbbbbb975cceeeeeeee5d7777f777f722832a8348655bb1957c6452af8c8a5519546e5577770c6124acbb65d565d484ed1fa9fa9276a36a4922ea9bb5dcbb3466421777777f22f917c8be83185656b2ed976d2b2e8ed1daed5a9947ebb5faedb59dab596bf6d6bb4a6ed772ece66642179b99dddddfc8be45f22f9140c69980329947ea96da5a9fb61da5d0bb6ed26976dfa4d2e9743398eef3333333331dc025c72eeeeeeee5dddc9c550abfc452aff114abc55e2af1578f71777722b29808ca75b1d4c634e739ce601330ef6edb76bb6d64dbb00409999777779b981dc709bf917c8be45f4e955c88da8db65db982149a8552994b39ce73980592b3b80409999777779b99dc70f22f917c8be4526728da9da5d36a36a7ebba7691cc3f4bcc1cc5ec4d1fafd1c2672acad64d2ed8cb67ebbd832bb485cc19c2000ee00013032994ca65007ebf5fafd2ebb5da5d76bb400bafd2ebf4baed2ebb5dddc777980041dddddddcabc55e002af1578abc55e2af1579dddc925cce6777772e420e195194ca654658eba77777003285db32994bb6655abdbbbbb80174ba03bcc9772e48040266666665dddddddde6e6000700777777772f377255fe22957f88afeeefee45002af1578abc55e3dc5caaeeee0634cc059fa9fa3bb977247e9742edbf49a5db7e934ba958331225dc9728cccc8ee03bb8eeeeeeeeee5e6ee4e2a855fe22957f88a34b8abc55e3dc5caaeeee6d3e86d3284934bb65db2e8a53164ad626d89a4d269d49a75b136cee8cd14a6665dddddc71fc8be45f22f915dcce9ddddec58ca8ca3b9d5ddddddddded60b194ca65024bdbbbbb8652e85d4ac5db36ad4bb765abcc97724330a33489494ccc800ee0f377777777777777772f3772feeefee4538aa0d2e2aff114abfc452af1578f7172abbbb89fa90063240ee4b9771fa5d1248bb6fd26976dfa4d0cc45cce64bb9333320ee0eeee0eee3bbbbb979bb93862490ff88a3fe228f87c7b8b8ddddddccee93bbbbbbbbba0465481d3bbbba11952092f6eeeee7d0ca5d15a4925aa493cc9772433129a4494673332003b83cddddddddddddddddcbcddcbfbbbfb914e18bd25e88a9243e1f1ee2e37777b3b43187776974ba5dbb1749a5dbb2e8ed76964ad6b5ac4d26d90a85b5ac4ccccd99d9bb0771c777779bf917d3be45f22955c0c699807ebf47ea7ed9fa9fb60bafdb2e8eee5dc9b2ed974332ec977266665cd91dc07771dddddddddcbcddc9c550abfc452aff114abc55e2addf1ee2e557777 (Nat.shiftLeft 0x2040165db2e801752b174ba5d2e974ba6d26b754a652bb9b4fa6d26524d2652eeeeee387917c8be45f22d8fa8fa49bc550ca7d02e936cba5976cba139ce608db1f51f559dc972ee19933399f4ccba5cce64d98ee3bbbbbbbbbbbbbbb977271542af1578ab77c55fe22957f88a7b8bbbb87d02e936cba5976cba0 12288))
def cur_top_28 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_28 cv_top_28 8 255 3 7 11 2047 21 2097151
def hint_top_28 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_28 hv_top_28 32 8 10 1023
def fc_top_29 : Nat := 0x3ab6b277ad90ef51a9d5b4b3b96e8772d90ee51a9d5b433b569676c8d0ed5a19d5a553b28c8764da4ead279d7d683af8d075691ceb2b49d63643ab47e00257ce9ab59d35673a7acc74c578004ad9d23433a348a6fb184df62d9d0460
def ff_top_29 : Nat → Nat × Nat := unpackForestF fc_top_29 12 11
def ci_top_29 : Nat := 0xb42d0a8ea0a8291952509424188a208820280200789e0781c24e5304852040897240810981104001
def cv_top_29 : Nat := 0x1df364edd32f7a8d7b64c9ddb74ee9b276a997b946bdb234edda5f6ad0fb38c9d9369ec2b475f1a3adad3d6364f062cf7ed67bc697dc343ed12af6293fae48fd5a3fcbca174e573a7acc0a815ea6b5f5159fa62bd0b06b7042da9414c1404bd2343e82b3732d678d4cfd1a45e011fcbc4ab9e6e3d0460
def hi_top_29 : Nat := 0xd335b189cf5504f8c74e8e02c15d797cbaa9c1adb5d53935aca68a4ca8291d1fa69c6863a119296199e9b5cc937db99b8e85153e859a9a3b7fadb17b7af9692d72f6aa016e510d2967f5b1975e769a6058c17d6d4cc6baff4302b6713d199d7a34c1be162d018df02c3020342489b1ea1ca9b5f810dab6f40a5db59f0002c697
def hv_top_29 : Nat := (Nat.lor 0xd5eccaf57b320164a65dbb9bbbbbbbb8003bbbb975dddddddcabe322957c645001a432add8caa32a8ddddc0b202ed800008d5e88d5e8164da2500124cb4cbb3b4c7980ef3777779b99dc22f9e45f22954aa0000161000005d2c2ed24acba0000b50000b5816a017769200008164a65dbb9d96b32b599072e8003bbbbb975dddddddddddddddc000229e0348655bb1957c6452af8c8a5519546eeee0092565db2eab2ea52d46d492f51b524009175002332e5c83a74e6777777f22f917c8be82d62e974b000ee0f377779ff802b2b5976cbb6959765ab596af6d65ead57b2db58005aaf4bb480273256b32e5c83cddddddfc8be45f22f91400025a97b65ea96d800bb6bd26976e5a4d002e9740000999999997772ee48003bbbbcddddcbbbb92aff114abfc45002af1578abc55e3dc5dddc00000900002ed9d49a5db3a93400ba9580120000a33332eeeeeeee00eeeef377772ee4abfc452aff114006971578abc7b8bbbb80012165db2e80592b589b6269349a75269d6c4db02334529ce6665e6eeeeeeeeefe45f22f917c8a0000005ac09000000005ac07500248000581752b176cdab52edd96a0001260519a44a4a66641e6000eeeeef37777777777772ee4000229e034b8abfc452aff114abc55e3dc5dddc0000000900004922edb749a5db6e9340110ce6001333200eeeeeeeeeeeeeeee5dc802490ff88a3fe228f87c7b8bbbb800000256004922ed8bb6004a732426666401dddddddddddddcbb9004921f0f87c3e3dc5dddc00000000409000000020480920001f4b05692496a924000126094d224a3399990798003bbbbbbbbba733bbbba77772ee4000229e0bd25e88a9243e1f1ee2eeee0000165db2e80592b5ad6b1349b642a16d6b1339ccccd99d9bb7777777777f22fa77c8be45000042a42d90a90b6000240002cbb65d00bb00099990d97777777700777777772ee4abfc452aff11400abc55e2addf1ee2eeee0000020000002e9342ec2cbb65d00000002693410a01458e9355151356a49000093099993667764ddd83cc001ddddde6eeeeeeeeeeee5dc8000453c0abc55e2addf157f88a55fe229ee2eeee00000200000b02e974000204e732ecc1eaa000eeeeeeeeeeeeee000114f02a954aa552a954aa552a954aa5577770010020000ba9174bb65d2e976cba5d009cd29ce73999ce66739cc007074e677318c6736bb98ce673398cf33039ac6b2491918ceeee92464ee6318c62e9acd6631898c69988000348655f1914abe3229546551954655198cee9531bcc453798c20001002b49245d004925345244014d24a739cdd3ba4ee918c00383a74e673398cf3324ee924eeee918c0e919249248c5d359acc631318d331017a4bd114012486318c6318cc677198de6229bcc6109580700124800ba5d2e97524802739ce739ce73049d2318001c01c73399cc67999248006318c6318c6318cc677198b5900ef670318c174ba17522e976cba5d2ed974ba4e64d29ce73339ccce739819c1d19cc67730ee0e673398cf33032a8348655f1914abe34e9546551954655198cee600ba5d0ba5d2e9749cc9ce739ce7307aabb8399cce673398cf333bb98c8c8c63174d66b318c4c634cc400aa154aa552e954ba5599566633b98de6229bcc626976cba4ba672d646502739cc1dc972ee3b4ba1752b176d1a4d2ed934332762e673b4e66732e91dc77777777777777772ee4e2a834b8abfc452aff114abc55e3dc5dddcb59006358c0eee3b4ba1752b58bb7626976ed6265929dad33699997660ee0eeeeee0eee3bbbbbbbbbb832a8348655f1914abe34e95465519546551b955dddc71dd2777777b580040ee93bbbbbbbbb98c0807b77777002ea562ed9b56a5dbb195ccae5ddc8058ca91967632cc994cb326599766000e00eeeeeee65733bbbbbbbbbbb995dddfdddfdc8a00348655f1914abe32295465519546551b955dddc425600c00249276801742ed8bb6492003296b4ec659bb665d9bbbbbbb800e000e0eeeeeefd7774920018c6318c6318c6371bbbbbbbbba74eeeee9cc207007749dddddd008015a4925abdbbbbb9f400ba249232a2922e6572eee400ca232a4919665d9bbbbbbbbba730003803bbbbbbbbb995ddd7a4bd115fdddfdc8a00924318c6318c6e37777 (Nat.shiftLeft 0x1200002e9740001091b5bb326d36cc80249176ee6eeeeeeee00eeeeeeeeeeee3f19147e322802490eec6318c6eeee02405db00000ea750da6d00a44ba4cc33122ecd21e603ba777708be7917c8a00000840000174b04acba9240000000902004922ea0000809245dbb9a48a441cba000eeeeee9ddddddd399dddddddddc000229e09243bb1af4455e90c631bbbb86d0b00b002002e81690659996600bd2c94cbb77377777707777772ebbbbbbbb95465518078348655bb19546551bbbb800005d80000240001690b 12288))
def cur_top_29 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_29 cv_top_29 10 1023 4 15 11 2047 21 2097151
def hint_top_29 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_29 hv_top_29 32 8 10 1023
def fc_top_30 : Nat := 0x3df2f878959cf752a1e25633d78de7af18cf66b71ebc5d3d78aa788998f52b31ea4663c44bc7a15acf42b19e83663c449c79517cf2a2d9e616c3ca8ae79514cf10941e2c5f3c58b678b15cf16299e2124001466784914eae2c9e0235
def ff_top_30 : Nat → Nat × Nat := unpackForestF fc_top_30 12 11
def ci_top_30 : Nat := 0x95e50852108421080600711c0701a2681a0681735c1705c161581244812048120390591402308002
def cv_top_30 : Nat := 0xf89be7c29f3d74c9eaa5cf7cbe7964a3c6249eea54f45277944a3c5249ecd6ef6e37fb518fd88bbebc55f56b37a919bd2ad7e8d63f41b37985b3ce8bfe6c5bf2e2bf9514fc88bfe3c5bf1a2bf8b14fe5adff1d6bf7ab3fb958fd64cde9a5ef3d277924a3c4249d7a55f0922f5a8ffb24bfe0235
def hi_top_30 : Nat := 0xac4ece65a625d98a9ea681e09a590d13956d0d3b94b4382e904d6d1a8a39bd8582fdb5cf7db985517701b5ae700db5bd6af1094766f111006031adb0590195cc5415a13b4d65a9ac4a10f0d543fdb5853ec5a14e3ac0e90136319924302da1812a51b1772595992f2214e0e01c45857415c9ad9f0ef5a9b5082db5b20001b60b
def hv_top_30 : Nat := 0x48ca00240aaa95da49244d2684db1248a249249212124924926cd54a249251449204249948144928a249f492527493a46993989253bb99249249897257a4bd114ee124baef892492453e4f7770002aa800016b1249201695809a4d000024902400924d9aa80134a73799a6f334eee649201c9777f117bf88bd77c493dddc000aaa0065002d2b004d2c0009240210249366aa00006c4944800120400924804d298061c27773249249312e480725c0114f0ebbe24924914f93dddc49955824908654654922654924136c9a4d2684d1049242126739cdccebbbbbbbc8be89465b58ca8ca8ca6546549082490ca6509b64d269342684d09248424ce739b99cddddddde45f229404934213fe052490209a004d012482004024924924e739802494eee6493dddc01e24975df124f777244924901248a32ab2492489a4d09b64d492289249212492492492524929ce734929ddcc9257a5ebbbb924baef8927bbb8928cb632ab06532804d26d84d2684d26d84db26d9340921212424924924cde669bccc4e64e739ceee6493dfc45efe229dddc777775df124f7772564ac16b10b092489a136c495892490909249249492489cc9ce739ddcc9257a5e8ee3bbbbaef8927bbbad6b012424b5896b44d26a44d2684db2d2b12492484849249333ebbccd379ccc62732694e7773249efe22f7f114ee392eebbe249eeee56b2b58b5ad609364db26da26ab5ad589a95ac4924924924924924ce739cd29cde669bccd3bb9924f7777725dddfc45efe4ef5df124f77708fa84809b77776134ca592b589b6269349a6d26a16c4db124924926cd973399ccea5f22f917c8be45011f40fa005934bb002c958009a4d09a850002424d964338e6752845f3c8be45269349a7d485b1f5216c194fa012424bb25dddd92424024909249266f334de662732739ceeeec927bf88bdfc453b8eeeebbbb249eeee3e9f6ec9b77777764d09a4d2693426d89a89a89b6249249249249b24d99ce739ce73bbbb9bccd379a94927bbbbbbbaeeefbf88bdfc45249eeee00155400100005d2c124800021024924800018302491ad4aa524900008a7824975df12498c6318c0aaa9024800bb65a45dbb2e976ecba5d09092492492492490c60c918c6318c6318d6a5529249dc725ddfc45efe22f5df12498c6318c6d0c0921114a5db2e85db124892424249249eeee3b8492ebbe24948da00240aaaad2491742ed89244924921212492492919249231831849235a954a492bd25e88a770925d77c4926318c630002aa801b400b48ba0174b00024900840920019230060c06b52a949240392e008a7875df12498c6318d65db2ed976cba4924924926318c6318c6b52a94927bbbbbbbbaef8924c6318c600155400100004d2c124800021024924800038e0eeeeeeee492000114f0492ebbe2497777055548124004db2d2b5d9349b7762684849249249249248ee3bbbbbbbbbbbbbbb9249dc725ddfc45efe22f5df124bbbba465001205555692489a136c49224924909092492497777777774f31dc777777772495e92f4453b8492ebbe24977770005550032801695802696000492010812400777701c70777724900e4b80229e1d77c492eeef64db26d936c9a492492492eeeeeeeeeeee493ddddddddd77c492eeef64db26d936c9a4924924926cd548492124a24924ce739ce739ceee6492492625c9eeeeeeeeebbe24924914f93dddc0000000480001752b176dba4d2edb749a0013b10ce769cccc803bbbbbbbbbbbbbbb97720034b8abfc452aff114abc55e3dc5dddc00000000002ea562edd89a5dbb5802d64a76b4cda6665d9803bbbbbbbbbbbbbbbbbbbbb800d21957c6452af8d3a55195465519546eeee000165db2e80002b6c7d47d4adb01200001333332e90ce64d9803bbbbcddddddddddddcbb9002af1578ab77c55fe22957f88a7b8bbbb800005976cba00004db135135136c0004cfb32e936ecbb326936649b3200eeeee5d777777777777777777002a954aa552add954abe5522957caa452a954aa557777
def cur_top_30 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_30 cv_top_30 10 1023 4 15 11 2047 21 2097151
def hint_top_30 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_30 hv_top_30 32 8 10 1023
def fc_top_31 : Nat := 0x3feae27fd148fedb91fe4523fb6e07d099cfe6381f9e763f78e07e75d8fce3d1f9b7a3f36b07d097cfa73d1f4d7a3e98f47d3180fa6281f4b7a3e96c07d4d40fa53b1f425700146e7cc990f12b79f22543c4ad67bedf0f7d3e1f0164
def ff_top_31 : Nat → Nat × Nat := unpackForestF fc_top_31 12 11
def ci_top_31 : Nat := 0xd0190b20621a8f50290d20a03402805008cb1823046088310220440881085941302402905002404008010001
def cv_top_31 : Nat := 0x7ff5c5ff4527f914a02d7f8075ce01468801149feb727f6dc1f4a567f31c1fbc707f19d9fb5767eb1e9fa37a7e6d61f52667d4d41f8e7a7e15e9f7c7a7dd181f6c507d8de9f5b607d29da13d6f8495ae1056782d58e0946a81d14a0636a80e9bdfd2677e497df425779e9350d06f3ce19ce605f2aa15dec2747cc991e7128790491f22547a4939e692878e491f0164
def hi_top_31 : Nat := 0xa7442437a388dcefa1f058669bc9918a9166a69990444c488d54c0bc8b208c8d86591932804d31837c7cbcf47691757b6c329e9866b1416062c8f0fa5da1414a56d1c1b4510195744cfcf10146b9959144fc686f40f9090137d2aa4a31f961762c7dc15f250291df1e9db99915069a660f557d6c08f1c199058cf8d90001a563
def hv_top_31 : Nat := 0x3edaec650a349a49f4ca7d09b64dbbb265b32d9bbbb26cca00424a36c849339ce667dddc782c4db196eec4d02513e93624d0ca7d0b32dd97777612484d269349b764d0240924fa4d9024924939939ce7777739ce649332771dddd7777dddc493c7bbb8928ca6d32a3686532801665b26ddddd9605996eec2cbbb56aeeeeeeeeeecb32dd977764900090249249b26c92499bccd379989cc9ce73b7bbb7b35ddd924ccf7f117bf88a771dddd7f777f645bbbb249e3dddc065b3addad08d92492ac8ea092495865b125632d9d6c9251b3649293db9befc8b6b196cb5960b59d4084924847339bc8be45b5821b5aeeceb675491d6c32d9695aceb64dbbbb32d924212559b24973399edcde45f22fdf914db636996c1b6c6d329609bbbbbbbbb232a5636dacadb1d4ca753aab4eb626d82424928a242399cce6737917c8be45f229b4ca1b4ca1217776aeed5a7526934eaad3a936cca49451b24b99cde45f22ab2b5ddddd9576269349a4d36934946ec9a49249289b25124926739ce694eeeee739cc927bbbb92ebbbbeeee249eeee5636ab1d4b1b4eb609365ddd97695a4aed76bbbbb56924aed76bbbbbb4aeeeceb777777649249249289289b26c92499ce739a539bccd3799adeeedecd7776493ddddc9777f117bf88b7f777f645bbbb249eeee49209032d996cb124aeeccb6ddbbb32d994cb665bbbbbbb32d93492484b36492e6733db98cfc8be45fbf229e0491b432d996cb124acdb6ddbb5d8cb69124ca8d8926cd924bdb98cfefc8a7832a32a1065465489bbb4aeed2b55a9249232995249232d8242514492423a73399cc67ebc8be45f229e492bbbb4914688d32a34ca8d1224925224924924944926c924d8ce739a495dddcde669bccc49333dddc9257777dfc45efe22924f1eeee4248bbbb569236b5ac65b256449249aa9289b2493624924ce739a495dddce739924ccf7772495dddf777124f1eeee0ca8ca84195121695abbb47d56a489a4db3e932a28926c934925d398cfd7914f24959776249224d269349a6526a24dd934926aa4a2493649349249339ce6925777739ce649333dddc9257777dddc493c7bbb894acad764db26962c08d11a3bff9221021092351b4ca892cb0b2c495a4aeab768db3e996d2575525dddddffffffd0924249224d97776257692492495a492492577777695da4925692449249251289249364d9249339ce69d24e8c9256f776f66bbbb24999eeee5e92f445492bfbbbfb22dddd924f1eeeeb2eeecbbb56aeeeeeeeeec92493777649b3552eccbb32eccbb3b7bbb7b35ddd99ccf7775fdddfd916eeecf719f177800000009252240009a4d0049200024009249248013799a6f332494eee649201dfc45efe22a4975df124f777000aaa0008000269609240001081249249b3550000200004810028928927d2490000c382494eee6492492625c900008a7824975df1249248a7c9eeee1148025200249204db2d2b5d9349b764d268484924924924924e64d29cde669bccd3bb99249dc725ddfc45efe22f5df124f77702aaa40920026d9695aec9a4dbbb1342424924924924924d9aa8124ca06c6c4945126c6c4924ca4924924939934a73799a6f334eee6492492625c93b8e4bbbf88bdfc45ebbe24924914f93dddc750812444b3addabb269f426d89244ea424994249449f4ce73993989253bb992493dddc770925d77c491493dddc7db01200490911124922693426d892449249212124924ccfaef334de733189cc4929ddcc927bf88bdfc453b8492ebbe249eeee9693124844726bb84db124892424249249e2af7771dc24975df124b8e0eee223bbb84db124892424249249366aa5cb925c9204932814494493e924bbbb9dc24975df1249248a7c9
def cur_top_31 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_31 cv_top_31 11 2047 5 31 11 2047 22 4194303
def hint_top_31 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_31 hv_top_31 32 8 10 1023
def fc_top_32 : Nat := 0x4178b082ed6105d2aa0d23d41b2788344990612120c04f4174a87d158d04eb4a0a255413ac27d11a90452aa07d6e40f6cc7d1149035a69f436a4088f08111a1022292043683e84de80d1a0feebfa024583fbae67f71a1006bf1fdc52
def ff_top_32 : Nat → Nat × Nat := unpackForestF fc_top_32 12 11
def ci_top_32 : Nat := 0xbc2e1b46d0b06a2a828289a2088211625805c57045910314c0300c03008420062180421004001000
def cv_top_32 : Nat := 0x20a4788364920d93c8388f60d12683290a0c04f8271e20fc5883cd620ea5582e951e8a4d8289560ad6982758605a6d804995faa5f7de95e0523539c17cb08578229560856e81ed9a04a6f80099df6a557dc8d606b4d7e897df625739a17cab8578171e20546881314a0436880d1a200c50809161ffb808035f9ff4727f91c1f5234
def hi_top_32 : Nat := 0xf4730aefd445c52ba80020275000000ea000001cbd2020f93e100f6c85b57ec7f5644773163736dd22824564169599dd323ad387110ce500ae83c195de1b74f33b8eca45b7e9640a0c22759754a42db5af6773473a0c58baa390de99f52080484e3bc1415073a0e0f8d1450580d13234617a080a005e96a58000242f
def hv_top_32 : Nat := 0x17695d8002d2b5d93402c51bb269349a4849a48017529dbddbd97665d999cc800d2ebfbbfb26f1378f719f1778002c490b00b5695aec0236c9a00017776236c9a48058a2166c924973399edcc6733e45f22fdf914f71b000b156b2ecb00bbb2eccbb32ec57a2bc5808af78000058ab016005dab576bb05d800001695dddd9764d24801752997665d9dbddbddddd800d2ee46f5fddfdddddcf8bbc000aaa006d002c002ed2b495daec00161760000169580585d812402c51002402eeec9366aa005d4a601870b7bbb7b35ddd99cc800d2e008a785fdddfd916eeecf719f17780b4aeeeeeeecad49256abbb4ad5ab0ddd8da5194d8da4da65366c9945692ea532eccbb3bbbb2eccbb333991a5d6e36f5ddd99795bc7b8cf8bbd6362b55a162040333c1b4b4ac02cb495a92b2b415a10b14400b2156805d4a60177765d99766673234b802eeed5bcade3dc67c5de0ca650bbbb2eeeeeed5b632a56a32d809b3604ca1366c9949a0ad2132e85d9976777765d7998baf3319cc9c653baeeeccbfc4556ff114f719f17782eec3a81400500000160000591480000b21b1440002eeecbb32eccce640002eeec7c3e3dc47c3eb5ac05da2eeec2d6416b5da57768bb2d2b3299493299490994b58a329b364ba6577998baf32e98c17665d2e85d4a77776673295fe22a57f88a72541a5d77767b8cf8bbcacad6bbbbbb4aeec5ad6b177691366d136b146cd9b589b125d997665d4a777765d7998baf3319cca5792bc34baeeeedfc45b7f274f719f1778569f4bbbb26ab49a4d269340d82b4fa7d56d9b0ab43293e9269349355a4093424cba17665d997665d997665d999cc9cad1abc7de26f13795bcade3dc67c5de0ca6502ec2eeeeeed5a4d56936ec26509bb26934956924cba17665d9dddd97665d999cc9c653baeeec9bcade3dc67c5de036800165ddd82155aad56ab42004924d9092ad000002739ceeeee739cc92403bbbaeeefbbb8927bbb80002eeec00015b63ea3ea56d8090000024936424934804e739ddddcde669bccc49201dddd7777dfc45efe22924f77700016401765d80005ac58ca05da24848049b249219c7339822f9e45f4e800005ddd8001349a4d26dd934000924d924d24249009ce73bbbb9ce7324900eeeebbbbeeee249eeee000003688002c000002c2ec02eed5ab00000b0bb0bbbb248120004924d9364924800061c2739cedeeedecd7776492000114f0eeeebfbbbfb22dddd924f77759f6eeec52b19507db0ca16959f4851b3eddda3632a0cb6194562ed651a4265329b4ca6536dddd9bbb32dddd801bb22b4caad32849009249248015692739ce739ceeeee739cc927bbbbbbbaeeefbbb8927bbbad67db1948894acad6b05dddddddb76cddb5ac65b196d6b16329768920109251aa926c4b99cce6737917c8be45f4e996c7db28d21
def cur_top_32 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_32 cv_top_32 10 1023 4 15 11 2047 22 4194303
def hint_top_32 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_32 hv_top_32 31 8 10 1023
def fc_top_33 : Nat := 0x42cad68791c10f13e21e17c42cace8749390e1aa21c25442cac68589990d2b321a46642c4bc8580a10b62fa16c5b42d8ae85c9110b629a160240014768511a10a1b42142653e8ade84b1610952a9f456b4218e08429f5084be1f4567
def ff_top_33 : Nat → Nat × Nat := unpackForestF fc_top_33 12 11
def ci_top_33 : Nat := 0xa0280a02358c212841e3781e0781c2701c0701c0701b15d0f83c0f0384a4280a0154411004001000
def cv_top_33 : Nat := 0x87d1c21ea7c86a9721e17c85e0921d24e85c0921cb548709521682486b59a1a46685c91218c5f86116e17c5785b14e20d6f87f5ae1dd6786f58e1b26686697a1902885809208c508551a208450852da21426582b1e2134587e099612a557a4935fca5d8471c21127d7f09761097c
def hi_top_33 : Nat := 0xb609753bb029b978aa9da963a1a2b63fa0e8402e9c397d2c96bdc15f8f1e95e88875b5aa83817d3d7d7dad8176edb5a47214f9366da9991b677da18b61a1b1775e18f8e25941a5365570e0f44fe989624a3db96b4579693141213916393e99f9319dc9e82c4d3554218a8eb11a35e5d5157121310f75a17f061e92560001b187
def hv_top_33 : Nat := 0x2204db10904849249248493284928926924939892539ce6492492770925dddc49249228c927bbb8eb6024009212225da49245d8924492492121249b2499bccd379989cc492bbbb249efe22f7f114ee124aeeec927bbb9c70777111dddcbb124892424249366aa4925c92e48124ca05125126c925dddcee124aeeec9249248a327caa4a46d001205554aed2492b2ec4922492490909249366aa4925124928a2490249940a24945126c92527493a4699398925777649249317257a4bd114ee124aeeec9249248a327c9eeee00b102c1dffc00002c4900b4acbbbbb0003624924d9009a539ce73bbbb2497201c9777775ddd92493e7bbb80000002d62492402d2b00bb0002490240090920134a73799a6f335ddd92480725ddfc45efe22dddd924f7770002aa801b400b4ac0b2c0009240090206cd549240000d89289000240801b249009a5300c385ddd924924c5c900e4b80229e1777649249245193e4f7771255a8cb632a56d832994bbb2ec0bbbb2eeec0921212424924924cde669bccc4e64e739dddd924f7f117bf88a771dddd7776493dddc9592b05882b4922ecb491249212124924929249234c9cc9ce73bbbb2494923b8eeeebbbb249eeeeb5ac049092d625aed2bbb45d96959249248492124924cde669bccc4e64d29dddd924f7f117bf88a771c975ddd924f7772b595ac5ad6b049bbbbbb4aeeed2bbb44924924924924924ce739cd4d4e73799a6f335ddd924f777725ddfc45efe4edddd924f7770c631dddddddd924924924ce7398c631dddd9249148a45229148a4522dddd9249148a45229148a002aa80020002cb04920000840924848001e787fffffff924800061c124aeeec927fffc15552049005d9695dddddddd84849249249249249fe7fffffffffffffff9248552a85548aa5572a98aae5535ddd924ffffa46d0012055556924acbb12489249242424924927fffffffcff3fffffffc925272aa49d234c2a954492bbbb249ffff00000b12402d2b2eec03fffffffffffc00aa9154aa552a956eeeffffc00155400da005a56059600049200481021201fffe079e1fffe492005548aa01870bbbb249ffffbbbbbbbb249249249ffffffffffff2492a954aa552a954aa55bbbb249ffffbbbbbbbb249249366aa49242490925126c926739ce739ceeeec9249262e4f77777775ddd9249249149f27bbb8100009240000924924048000228d909f49a0000092577765d7998baf3319cc802495ddd8ff88a3fe229ee23e1f0000024924000925764d00451bb2693490900492bbbb2eccbb3339900492bbbb1f0f8f711f0f80009440003ed9340012492b0bbbb0eb64d2400ab36492e6733db98cfc8be45fbf229e0015540010000000585d802492492560000161760924490000808a3767dbb24d9aa800061c124adeeedecd77766732000114f0492bfbbbfb22dddd9ee23e1f05a02ccb765a56095a0b12482ec9b376132963694dd366c9b49a49b49a4932e85d4a777765d7998baf3319cc9c6506975ddd9b7f88a6dfe229ee33e2ef05012065b32d965a56bbb32d936eeed7632dddddd996c9a4932d8d8d9b24973399edcc67e45f22fdf914f02aaa4092002ccb776165da495daeeeecdb7777776bb1665bb2d2bbbbbbbbb2484ca58da51b1b493693777649b355265d0ba94cbaf33175e66b7bbb7b35ddd99cc9c6506975bf88a6dfe22dfdddfd916eeecf719f17781240aaa5996ec492036daec1204249128a413288a46ec946cd54fa4d252249974492bbbb2ebccc5d7998ce64e1892577763fe228ff88a7b88f87d60810a4924923ed93432d89248eb64dbbbb32d9289329564fb6492e6733db9bc8be45fbf22f171c1ddc48777777770b32dd82492493bbb9665bb124892e5c84ca228dd9f6ec9366aaeeee70c492bfbbbfb22dddd9ee291b4004815552bb4924924ac2ccb760924924ad24959665bb1248928948909944523767dbb24d9aaa4e92748d3265d124adeeedecd77766732bd25e88a70c492bfbbbfb22dddd9ee23e1f00005a560001769256b0120001628d90ab49a000005d4a777765d7998baf3319cc800d2ebbbb56ff1155bfc453dc67c5de
def cur_top_33 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_33 cv_top_33 10 1023 4 15 11 2047 22 4194303
def hint_top_33 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_33 hv_top_33 32 8 10 1023
def fc_top_34 : Nat := 0x45f6a488899d1573d22ae76455af48ab5d91563d22ac764556f48aadd91553f22225f44dcf489b5e9146b8226c7644fae089add9135ae22225744b8d088d9ed126342236734468f488d1891109ba2203700147e8849910b2b7a20254
def ff_top_34 : Nat → Nat × Nat := unpackForestF fc_top_34 12 11
def ci_top_34 : Nat := 0xdd3b83706e0dc1b83706e0dc1b82e4dc0b81702d0da0b0360272ce098330250ca09410921009d10010820002
def cv_top_34 : Nat := 0x8d35fe2dd798d15ce33d718cb1fa31c728c4d923035e8bed4a2ee7a8b99da2dd7a8b55da2cc7a8b11da2bb7a8acdda2aa7e8a35c227d708a79ea2957a8a11da2737689ad7225c688931a22567b8919ce23c7a88d18a4756f9155ae42d6790558e40c6a8ff19a3eb6f8f8daa3d3678eed9a3b35f8e8d7a38b578ded4a3526f8bc99e2a25f89895dd596f6fa59dac15f66255e2293743a1bcf486739e17cb18578880dc250178849921882488095218024
def hi_top_34 : Nat := 0xa48686e6a0a8e8f79cfcd8eb9808fd3d91e52d898d40e9298954d8fb8400fd557dc92d8e7a40ece26eba96e2683931a064b4bce1638c4c4a6078c0c55e108c9a5949193253b5756549929e89492c141947f8304d47b814104678405040d91d683a65459d2e3a6f0b21827f2e1bc92d6e167dc1530f3a89d1095db1770002a257
def hv_top_34 : Nat := 0x125194ca832994bbb26936ec9a4d2684d32d994b26d9350a584d329349b77760008509a65429950a08526a42a269240024092492493649b33799a6f33139939ce73bb9cde669bccc493dfc45efe229dc777775df77f117bf88a493dddc58b09048194db6b065329695ad6b5ac8542d89044936249b365cce6f22f915591d40fa653e9d51f50a92483e994b491289241124d9b29399cde45f229d6d6b194db7626936d7760ca652c95aeeec4d26daeed6b1216249b365cce67339bc8be9df22f916d6086d6b3a9349a75bb26994ca7542a1524753a9d4ea4d2686532964ac49d4a0806aa424d9b2e673399cde45f22f917c8a653e865328484d09a1349b6ac9b764d269349a75269d49a120049451b2492697339bc8be45b269b4cb6753addddd86d3284da1410a85b5776492049451b2e6735df917c8a653e8653284d936c9a8526d89b6489aad626d92489aac4db1349a04945126973399ccea5f22f917c8be4526935216d642a56329950a753addda14ea7542dac194ca12109349b64db26a14d8403552125145cce67339bc8be45f22f9140004803ad540489002eecea75bb010b5502ed0a92155a56893188a4556563a963ad824d936c9b695aec9a7526936ceb77626a1426a149a5ac85b2492155ad77769247556ad626d8924924924a24a24926c9366739ce694e6f334de669ddce6f334de66249eeeee4bbbf88bdfc45ebbeefe22f7f114927bbb9248243e934fa6526996ec9b67d269343e934fa6509a249194fa853e9349a653ea16d6b12490849b365cce67339bc8be45f22f914124653e99520fa65124ac7db1f4ca7d42d8944924d9b2e6737917c8a6544d407d56224926cd9355ab56832a0ca89b3e85a44d3ea251449365d39aefd7914ca8b212140849a4d09a134924847339bc8be45269352485485492150654242ab24919512109349b691348425144926dcce674e6f22f917d791524ad6b58fb64ad64db26949226928924944d924924926cce739a494e739ceee6493dddc925ddddd77c493dddc84921249126c9a7db26a57692491349a9247d09a7d3e9344aed249249226d923ea49249124924a25124924926c9366739cd3a49d1924a77739bccd37998927bbb97a4bd11524baefbbf88bdfc45249eeeeb1a7399f5dec8526a149a69bcc304cfa4db1c09a850d333bce65d09ac59a149a8510a4d42934977b2562eddcc0318d39ce739d99d9bb999977777771c9b9578abde45f22955c9a5d629350a4db5ac91350b324b194772ed89b773b9a48c634e739ce766766ee6665dde6eeeef379bbbbcdcabc55ef22fa74aae7d3ed9749b65d2ed976cbae3bbb8eee9ddc97b77724d629349a4d429349a4d429349a4d429349a497731a66666664d99dd92f64bb93776eeeeeeeeeeeef377777777779bccbcddc9578abc55e2af156ef9fdddfdc8a552af7154abdc7b8b955dddc6d51b56c9a4db42936c764df3dabffe7ffafff6a93f7ffe49a85269349a85269349a8518c632693493fe4522f1e3c789b3d764fd93fe4ddd954aa552a954632a956ecabefffffe62a954aa552a954aa553dc7fffffffffffffbffffffffffbf8ff7f9ffefffb26d936c9b64d09a4d09a9134924926cd56ec9bbb9ce732eddcc9af333ccc6733dddc4dbbe26ff117f88a7b8cfb800000009252240002ec12480009002492424804de669bccc925777649201dfc45efe22a495ddd924f777000aaa0008000b2c1248000210249366aa492000000048100289289364920001870492bbbb2492498b92000114f0492bbbb249249228c9f27bbb82802520024921765a577777777612124924924924939934a73799a6f335ddd9249dc725ddfc45efe22dddd924f77702aaa409200bb2d2bbbbbbbbb0909249249249366aa4920493281b1b1251449b1b1249369249364924e64d29cde669bccd77764924931724ee392eefe22f7f116eeec9249248a327c9eeee
def cur_top_34 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_34 cv_top_34 11 2047 5 31 11 2047 22 4194303
def hint_top_34 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_34 hv_top_34 32 8 10 1023
def fc_top_35 : Nat := 0x4448cc8fd5a5111b7a2236a47bae2888d9d1e237a3c4634446cc888d7d1d63322235e472cf48e45b1111aba383664446a48d75a51adba235b5e46b6a48889bd17ebfa2fd7345fae28cd1f517e3f23257145f8e48bed91185b922fb5e
def ff_top_35 : Nat → Nat × Nat := unpackForestF fc_top_35 12 11
def ci_top_35 : Nat := 0x9c25288e20846108416b581604912048102400c4300c0300c01d4611445014041100220802004401
def cv_top_35 : Nat := 0x23f5697a0d91e83668ae97e052358f75c63cc6f8f118e36a5d8c49562b24f89c91dad14f66651ce804f2ca11c260178eb19a3626f8c099e26a558e79ea3916c8e0d9a35a6f8be99df72358dd5a636b748d8d7a35b528aa97a3348c8c92023347d8c95c630c5e8c2dc9f5234
def hi_top_35 : Nat := 0xb9e91d4daf6e829fa75d6a04a1792579933a87908ea0e9268930e95c81b181e0744e77596c19b60d64a59ddd5ea51d805771a1cd4c4a7eca4365c6393c9965b33845051532c97d5f2f40fce22bb8ece222c2a63e2144485f1fc84c5f1a49256019d0101e1634c8e715941c28119cccfe0a8989c50a3810140539094000010d4e
def hv_top_35 : Nat := 0x5dd936ec016b59226a16d6b5925626a16d6b1363ed8a14d936d9bb733989b362cfc8be9d26f2178000004001349a0000485d85936c9a04d2680001349a85269349a8526934920085002582149f49b355bb26eec00030e14599f665dbb99349b399358b3999cc8000453c21bc7de26ddf1349bdc4d42f71ee33e86f0653e8136cb26d9349a4d26d89a89a89b6269349a13284fa49a6c9349a4cca2d667d9976ee64d79989af35299cc9c651abc7de26ddf137f88a4dfe229ee33e5af58fa589a5ac4d429626936c1609a852d6b244d42d8049589a85b5ac493610a5936d9bb733989b342cfc8be9d26f21789a4d269f52150a7d4850ca7d00926d0b764d21349a4d26da1426d936c9a0004d269349a04d269350a4d269350a4d269250b64dd80852854288527d26cd56ec9bbb42bccc8579989994a2ccfb32eddcc9a4d9cc9a859ccce650bfc4542ff114e8690de3ef136ef89a4dee26a17b8f719f43789a4d42ab089a215215248ca920d9349a4d09a2429b10a854214257b342cdcce87c3ef22fa26935216d642a42994ca9209a4d10a850d9349a4d09a1350a6c42a1494288517b342cdcce686f217bc8be45269349a90b642ab06532804d84d21349b6136c9b64d42d92ec026509269b2bd79990af331332939976ee667330dfe22a17f88a7194ee26ddf1ee33ee56563e96429f4fb62c4d26d9349b68526da26ab136ec9a52249a85269349a85269352269352b589b649224a14a14d90a51f4dd927db24d9aadd93777459d16764a767998faf33176ee64d26ce64d42ce667330de86f0d2eb7f114fbfc4526ddf1349bdc4d42f71ee33e86f5ad60b5916b16b22d689a4d489a4d2c9b765a563eab493e9f490994b58a3e9269b27d7998faf331332964a65dbb999cc9f7f88a7dfe229c950697136ef8f719f2579595ac5ad6b16b5ac9b64db44d56b5ab148926d628dd936b249a6cc7671d9d929d9e66b3ccc5dbb999cca5792bc34badfc45b7f2749b77c7b8cf92bc924241350b64db2684d429350a4d42892485b580429350a4d269349250a90a50a6c996cddb99cc4d9a167e45f228f87ceeee924eeef64d26da149aeeee9244d629349a4d429349aeeeeeeee9249244942942972e5144d9aadd937763e1f3bbba490eef863ee18fb8f714249092492b26936d0a4d564a48a492269350a4d269350a4d26a44db2492491349a49429429564a44a429489b355bb26eee8b3a2cd27493a469a49176ee64d26ce64d42ce667323e1f2f497a22a490eef863ee18fb8f711f0fad6b05ac8b58b5916026936c2693426936c26da5632994865328065265329628934d932bccc6579985eccca652c94cbb77333994aff1152bfc4512bc954a834b89b77c7b8cf92bcacad64db26da56b16b5ac5ad6b136c4d8a24d366d65acd6b3b2532eddcecf3359e6a533994af2578697136efadfc45b7f274f719f257800002c9b7600b256b5ad626936c8542dad624924924d9b2e673399cde45f4ef917c8a21442a150a85000801340b26d9340036004d5492424d99ce73009ce739ddcc99927bbb803bbbbaef8927bbb80b200002d62c7d02d609b6136c4a2120124924338e673045f3c8be9d02c809b60016328016b1632816b136c1201b10ce399d4a117cf22fa740000040000004d2685d85936c9a0000850000269342ec010a4d48544d2481200049249249b24d90000c384e739ceee73799a6f33133248000453c3bbbbaefbbf88bdfc45249eeeeb1951f43ed81951350a24693632a36865b032ab589a85026c65092d6329b49b6b26dd832994b226a56b5ad6b589a4db2150a0120484249b365cce67339bc8be9df22f9149a85469249b64d24da65369bbbbbb0da150a85b42a151a00424249b339ce7dddc65b1350a1249f4ca7d269349a4dbbb09a4d32934ca4dbbb249a400084d924934ce739f7771349a42008542a150a6532994ca126d0a4d269269949a4db26d934a14840002492499ce739ce739ce739ddcc927bbbbbbbbbbbbaef8927bbbacfb64956566ed8fb77665b1f6d6b163296b216ec9b64d26936c4a2010924925cce67339bc8be45f22fa74946a5656b591b764db269349a58b5ac65b19402c58cb63296b136c0109b173399ccea5f22f917c8be9d
def cur_top_35 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_35 cv_top_35 10 1023 4 15 11 2047 22 4194303
def hint_top_35 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_35 hv_top_35 32 8 10 1023
def fc_top_36 : Nat := 0x49e8cc93cd992492724c35f4986b69341b1261aba4c353492050926d7d24dada49b574936a692409000521a47b6448f4ca8895bd22daba45b5448b4aa8895ad219be24327d4864f890c5f1112b3a41b544834aa88958d1123524036d
def ff_top_36 : Nat → Nat × Nat := unpackForestF fc_top_36 12 11
def ci_top_36 : Nat := 0xc42f2bc2f0bc2e1b82a4a82a0a82a0991d9741d068da0681a04651044110440b62c0b01945114005
def cv_top_36 : Nat := 0x24fc6693cd9a4d06c938d7e4db5b932d5e4c35392cd7e4ab5b928d5e49b539671be58c6b95919e5546394899a5025e93a93a4b828924091e8e7e920d9247a657a35ba46b57918d522ea6d8a49962da5d9169562513709c05de967d912df24427d90e9f22e25d90c5f1e956e908d5241a558904dc268178b297e4036d8b093e282473a213cb3847
def hi_top_36 : Nat := 0xc395b5b3bc4db5d2b6c9a161af39a9e4abccf0dba4b1b5c79ee5a1739a24e9309579992b8f09a19c88d1b18e83e5993b7ff4e0fc7a85855c74f9b16370ed1d03686e8e2067a01c335fc1c1f85a3d1d614e6e6ef44751c9c741d54d5f3aad95ca3441a19b29de9a9923a1b98f1f29311e166686310e1d821206316dfb0001498c
def hv_top_36 : Nat := (Nat.lor 0x339ce734a739ddce73799a6f352924f777725dd77ddfc45efe22924f777000000c401755000bb4ac00021024849200018701a43bbbb24900008a11408a93a9dbbbb249229148a45229141a02eab761690eeec6349218c009092492492492492730690e77739bccd379989242291422a4ea748b7645229148a45229148a45249229148a45229160a1144e8d0c1a0bbb2c969592484849249339ce64e60d21dddd924ddb552bb4ac60d0005d85d56d2b2492490909249249b7bbb7b31398348777764937645bbbbbb229142291422a4ea76eeec9248a45229148a4500000baada4300180806a8004909240210001a439ddcc030e0492004549d4e916ec8a01142281249148a45229148a8686348649249249339ce6348739ce649245229148a4549d4e9148a45229249148a45229148a0000161005d54002ed2b0000840921248001e787fffffff924800061c0aa9156eeec927fffcb202eab761695aeeed6492b58009092492492492493fcffffffffffffffff2490aa550aa9154ab76552ab954c5572a98927fffeecca95da5762c8002ec2eab6959249248484924924fffffffffdff1fe7fffffff924dbdddbd982a9542aa455bbbb249ffff00000baada5600b008032800490924021000ffffffff03cf0249002aa4552add954030e0493fffeacad64ac492492493fffffffffffe492552a954aa5548aa552a954aa493fffeacad64ac49249251aa9249092424926c924ce739cd29ce739924924c5c9eeeee4bbbbb89249248a4f93dddc00000092492400048024900005d822886c801f5e663ebccc9245dbb999cc800ff88a3fe22a490eef8f711f0f80009440eb7659f49a4d00000bbb01248900289366cb99cce6737917c8be45f22802aa800200000269342ec124800000009a4d03e80249249124000202289b355bb26eec00030e09245dbb9935e663ebccc6732000114f04921ddf0ff88a3fe229ee23e1f1f49b6b136c6d2c8042a480124ac04d32da14b4ad764dd934850a590a5214a16c9bb249a6c9332964a68579990af33176ee6673274341a5c85fe22a17f88a4dbbe3dc67d0de0a02432994cb764db329349a194ca592b5aecca4d26ddddad624996c6c49366cb99cce6734cf917c8be45f2282aaa4092009a65b329695aec9a4dbbb13409a65329942d6492b5ad642d89add26935ba85b589b62484ca58a3624ca49b355bb26eec9994b253b3ccc6d7998bb77326bcccf3319cc9c6506975bf88a65fe22936ef89bfc456aff114f719f71f6c07db00248484849148909a7db428925764a44850a242948a26c93ebccc7d799899944922eddccce647fc451ff114e189243bbe3dc47c3eb04086cfa4d269d6ed1f4cb77692492483e994492251099445124d926cb99cce67319ccf917c8be45f229ee2650ea052122ec9a7db3adda09a7db328925769249209a7d3e9944924892bd99d664cca249176ee64d99f663e1f1c31248777c3e228f88a3e1f38e0eee243bbb84d3ed994492777777770269f4fa65049249224b97213288a26cd56ec9bbb77773862490eef87fc451ff114f7148004815555a4922684d3ed99449248fa92492491349a04d3e9f4ca09249244948948a2426511489b355bb26eed27493a469933289245dbb9935e663ebccc6732bd25e88a70c4921ddf0ff88a3fe229ee23e1f0000005ac9256b005a560240002c5100bb00ddd900b25342bccc857998bb7733399001a5c85fe22a17f88a4dbbe3dc67d0de000b12411b765a349a4d00b256000bbb0090b1024d9b36e673399cc67e45f22f917c8a7800155400000b4ac004d2685d800005ac9256b0001349a08500248058a20100d9aadd937760164a6018702eddcc9af333ccc67320034b80229e04dbbe26ff115abfc453dc67dc194fa0134269349a04d269349b7764d269349a04934813426509f4ddd9349349269349266516b33ecc9b326cc9b326ccce64e328d5e3ef13789bc4de26f1ee33e5af049348194fa1f50a7d4284d269350a5d84d429349a4d26850a04d928527d377764cba17665d997665d997665d999cc9d0d10bc85e86f1f789bc4de3dc67c5debb26dddd8653297604d4282149a8526d936484ca1377777764cba17665d997665d999ccdddddd9c653b89bc85e3dc67c5de (Nat.shiftLeft 0x269349a95ac95ac5900490909a4d2136d2b1249248484924933799a6f33139934a73bb9924f217ff88bdfdc45229dc725dd77c493dddcacad64d26d936ec95ac4d09a4d26934b5924ad6249249249249249249 12288))
def cur_top_36 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_36 cv_top_36 10 1023 4 15 11 2047 22 4194303
def hint_top_36 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_36 hv_top_36 32 8 10 1023
def fc_top_37 : Nat := 0x4bfad096edfd2f2c025e36c4b76e69715c92e2b825c47e4b76a296c99c00523a5a2644928de96491124a35a56b7c4ad4f895c5912b43e2494674ab48892518d295b7a52b634a7adc94ad75295aaa492664a18cc942dad285b1a4925e
def ff_top_37 : Nat → Nat × Nat := unpackForestF fc_top_37 12 11
def ci_top_37 : Nat := 0xe45c83906e2dc1b8370664b0ee41c0304600a1140280500984c3980208400801001c2380320600c018001800
def cv_top_37 : Nat := 0x25fd68970d425ed80978db25d5729735c25c47e7d48d2615689831ca6047097cdfe5db7396ed45f4a369cd5aa7246a9c0dbe6e36b9b0d9e66363990d4661a6f96c99e5025d8988fdf423775c5bdc09676324fd5f13794c9d25a2649380a24b0249449ba592449360a24a82495c5925837c95e9f252a6493e9325687c9320a24a0249429ba55a449300a24982494f5ba54b6f950d8e5335d94ad5651c66944dae50b63
def hi_top_37 : Nat := 0x9a3c50599974243299041c1c9778506396a02436952c585d947c202c8ea92d758526a661804161397ac5c15f733a91e36d25b98563869a685df97d635789c19c5384f9014db5a57443dace773db1d98a363281e031e90d122d190d342c6c382b27f56d1e219dbd961ae1b5af1465ad9f0fad092e0bf510ee05a995930001856a
def hv_top_37 : Nat := 0x2686d419415a36996ec84d9949a6d44a3488da92b21950651134cb64db1134946911b49b632851b60b589a65b592026c9b49b1b1351b6c65259292495d936c9a4d26824ad26ab6d6b1949a65269349a134ca224a4010926cd54924d25cce6733a97c8be45f22f91492008caac924840232a4810924924908ca9049b329f4cb67d0ca6515a4924920009024a251249249266f334de6627313a49d1924a739cc92667bf88bdfc453b85e92f445492eeee249e3dddc849212491255a49249225248928d5499cd3a49d1924a7333991f0f97a4bd1152487c3e3dc47c3e0000000b5800000926ec9b4ac0009002492124804de669bccd34a7777649201dfc45efe22f25d7776493dddc0000161005d54002ed2b0000840924a3552490000200004810026d26c936492400030e134a777764924931724000229e1c975ddd9249249149f27bbb8b20b3765a56026ec2d6492b580924812124924924924939934a73bb9cde669bccc492771c9775df77f117bf88a493dddc5901755bb0b4ad7776b2495ac004849251aa924924924920493281249a49a49b364926926924956924924939934a73bb9cde669bccc4924931724ee392eebbeefe22f7f1149249248a4f93dddc850890a95a56429640492c969594290926509b4924d99ce732732694eeeec93127bbb8ee392ebbbb24927bbb90a4d02412bb4ad62c802484964b4ac924924242492499bccd379989cc9a53bbbb249e42fff117bfb88a453b8e4baeeec927bbba0a71f6ff2c8bbbb2c9695924848492492552a954aa5598552a85548ab7776493e79fffe5907ff964b4ac9242424928d54924f9f24f92409265026d26c9364927fffc2a9542aa455bbbb2492498b9376655695da5776b164001761755b4acd9249249090924a35524924d9249366c9240849329026d26c926cd9249b7bbb7b3139934a777764924931726efeeefeec8bc771c975ddd9249249149f27bbb800002eaa5a560000b580009a4d2492400924a35509240900009a539ddce6f334de6624900e4bbaefbbf88bdfc45249eeee00000baada5600b00803280049251aa9248042000004926926c90002408012402694e777300c38124924c5c900e4bbaef80229e04924924527c9eeee24cb64d092421656b58b1665b32dddd932ddddd849242126739ce73733df7777917ec92cad6b59949a4d32d996cca65b32ddd96124960b194ca124924219ce739cdcce6eeeef22f914d85824923b81600b006eeeec2ed2b080100924849339ce600e4d29dddd924f77700725d7776493dddd76492495776aeed62cac05ddd9b32d936d2b36492490924924924936f76f739ce734a77776493777777ddddc975ddd924f7771242d645ac5ac8b59949a65b2686532964ac049090921249249266f334de662739cc9a539ce73249efe22f7f114ee392eeeee249eeeeb5ac0490912223ad9d49a75b3a934329b4492248480492124924cde669bccc4e62494e739924f7f117bf88a770925dddc493dddd6458ca1259b6cb26ddaed24ad6b589a4db1f4eb6b580928a24924b99cce6737917d3be45f2280000166db26dd8116108b1602c1d403e84942212399cc19cf22fa7422f89592562d6b58249b4da9256bb136d76b124924944944926739cd24a6f334de669ce73249eeee492efe22f7f277bbb8927bbbaec9aaed5d8b22ec9a04d2690269695892490909249249b7bb7b2732694e739cc926eeeeecee392eeeee249eeee
def cur_top_37 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_37 cv_top_37 11 2047 5 31 11 2047 22 4194303
def hint_top_37 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_37 hv_top_37 32 8 10 1023
def fc_top_38 : Nat := 0x4ddcf09badb13751aa5b36b4d9ae09b29f53643e25b3674cdcf099adb1335ae26a6784cd46a9a0975344ae2680264ce48299c4bd3351a25b3634cb4aa9931b9325b325b3514c4af09895a1312342623514b64de96f5a12de3925bc70
def ff_top_38 : Nat → Nat × Nat := unpackForestF fc_top_38 12 11
def ci_top_38 : Nat := 0x984c21b0180401c8d96c361b0d164b2182b258288ec70349a07c381c0e0701c0c0280200
def cv_top_38 : Nat := 0x9bf9e26f36c9449b5f62459ba8d628a3d9b75c26d27d8a08f66c87c9a88d66a6789a20926895c9a49766802699e9066712f9af9e26b36c9aad7250a6d9a68d666a349969566546e992d9a6226f96e99df5a457dc8d663d7898d5a262c68988d465eb71974d465cb51
def hi_top_38 : Nat := 0x9089c9c58b6d3547813a8e8d79e5e5d5754521286f39a18365de9257609569525aa9b17b5579854c543c504f4f2171474f1404034f1400004f1400004d3080794ca420234719b5633ee2b20e3e1844323a015d0631b5de132a399ddf2549753c1f79ad741af9752017211cf60fd699d3099d918e0630dcdb00a5916300002429
def hv_top_38 : Nat := 0x95a9017690244a2902b049249090055a2289f6c49f6c4934fa6d5a49ab44923ebccc7d7998bb77333993862490ff88a3fe228eef8f711f0f832a32a106544da44d0d895b649249136c9249196c12132a289249a49a5d399cce633f5e45f22f914f0232a4810232a41242eab760ad24913524aeed23ea49249244d26a492490013289244946aa4d3e9b24d3e927d2499944e927464922eddcc9af331f5e6633993862f497a22a490eef87fc451ff114f711f0f84654803e935204894520bb417554920490904ca244a28d54db626ec9b376499744922ebccc5d799aeeecce64e189243fe228ff88b77767b88f87c4d0892b569242ab0654242ab2491951210da5764995136a24936e6733a734cf917c8bebc8be79fffffffe08ca907fff88ca90493ffcb42b49256925e7c84ca246d48928d56cd9ffff0aa5513a49d1924aeeec954aa6ecfa924ad5a492b408ca9024924908ca9049002ec2eaaad2495a4959376484ca246d48928d56cdd9b7bbb7b3132e89d24e8c9257776673377f777f7645e3862f497a22a495ddd9ee23e1f04124accb76aec9a7d0040dd03e8884ca0134d9001248cb36eccbb7730033994921f0f8777c007b88f87c000000048000249249244d26802213ed80009a6c802491f5e663ebccc5dbb999cc802490ff88a3fe228eef8f711f0f80000012b00249226a4ac0095ad62436249a6c802749d5a769976ee6673200bd2f43e1f0eef8f711f0f8ca7d401349009a40ccf020002415da489a4d0048db00000924246d89a490045124924d3641d399cce63399f5e45f22f914f714804801004d364d04947671d98f87c309a4741e60200000092000924922693524801200012484ac4d364d004e93a4922eddce68d9802f4bd2490eef87c3e1f0f801000000124002eaa95da49244d26a49002000420010021007d001248928d549a6c801200009d24e8c9245dbb98061c0ce64017a4bd115248777c0114f03dc47c3e049085036006c000004000013514800004424d3640001248bb32eccce6400012487c3e3dc47c3e269349a924924240092124809a4d404d26a49194ca4994ca484ca2289349a6cca4caf33195e6626651248bb77333991997ff88a3fe19148a0f8631248777c7b88f87c92564db2693524922684d269349a244a29248945126934d926d892692b59ad669245dbb9935e6626bcd4a67323e1f2490eef87fc451ff114f711f0f80100750801f4049232994ca6502510926500009240124a739ce739cc9240124bbbbbbbb8927bbb800000009000049236d9949a6db32934000a2126c49240124a6f334de669ce7324900492efe22f7f117bbb8927bbb80000012b002495ad6b000144d8909249240124a739ce739cc9240124bbbbbbbb8927bbb80480009b602400004d2684d3280892904805124924338e6752845f3c8be450001000000204800000010240490000fa582b492492404800128944924924800061c13a49d1924a739cc924000229e0bd25e88a925dddc493dddc9245246500291024994ca7d32994fa9246532994ca01249002652124ce739a494e739ce739924f77724977777777124f777125959244ca8ca8a48946536994da80084a2124946ce73999f7771e11952024912b065368924ad6b58090288124924924da49cc4929ce739ce73249993b8492eeeeeeee249e3dddc8da92269bb
def cur_top_38 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_38 cv_top_38 9 511 3 7 11 2047 22 4194303
def hint_top_38 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_38 hv_top_38 32 8 10 1023
def fc_top_39 : Nat := 0x149e9fc9913a237a7e2444e88d69f15c13e13e27c07c4e88ce9ec8f93d1a227a2444e88c69d09993c2332783664e849c9d04a13a5afa74b5b4e96ae9d48d13a5a9a7412400149696d5a93962ea5b46a4e1ad09c31a138532a5b36f
def ff_top_39 : Nat → Nat × Nat := unpackForestF fc_top_39 12 11
def ci_top_39 : Nat := 0xc02e2b82c2b02c0b02759c2529422388220882028020080200801f16d1382a4a0154501404101000
def cv_top_39 : Nat := 0x9fc992769249f8912761249f55c27ca7c9e2932759249f01f27b23e9d44927ab449e8912749249e319a783669d48d276b5f9d8d6e75b579d2d4e7ec6f9f71ae7bc679e718e792669de93a771289d04926fb699aed8663a6d984996632458a68fdf8a376364fd659379cb1762923f7e08dd8d13f5944de65b509c75a271468994d4270a65
def hi_top_39 : Nat := 0xae95c153a74289d5a199b16a9816a2619325753c8d45b9788795a96c7e4ab6537d84403178e57d287369c15f6bca95e8654db59f60117d4f59e1ad8c5305b5b74f2cf8f64ab1991f4525a1633f45b1783c40f8c13795a52b3494e0c02f518951289d91ad22016da71cf541431749b96b12b569250e95390806ee99ea00018dbb
def hv_top_39 : Nat := 0x480000926ec949200024009092492013799a6f332495ddd9248077f117bf88a9257776493dddc000008401755000b4920000840a355249249000000024080144d926c924800061c124aeeec924924c5d25c900008a782495ddd9249248a7c9eeee12036249013760924924049240909249249249249cc4929ddce6f334de662493b8492ebbeefe22f7f114927bbb8480baadd82495dda492490012146aa49249249249248124ca05124d24d24d9b249349349249f49249249cc4929ddce6f334de6624924931749724ee124baefbbf88bdfc4524924914f93dddc5905904904849249248493286c4926c9249cc9ce73bbbb2492498ba492771dddd7776492493dddc7d26812092492424012424b22491249248485124924cde669bccc4e62495ddd924f7f117bf88a7709257776493dddde79fffe241ffe5912489242428d54924924f927c90249940a26c9364927fffc2a954492bbbb2492493174972a93767d49249256848002ec2eaa92449249212146aa49249249b24926cd9248124ca0513649366c924dbdddbd989cc492bbbb24924931749726efeeefeec8bc770925777649249229f27bbb804004d20effe0000092400909226924000a249a4924802494eee739ce64924b900492ebbeeeee249f3dddc00000924000000901349a492480121249240900004929ddce6f334de6624900492ebbeefe22f7f114927bbb800002eaa9240080401f40028d5492492400902000005124d24d920004810024802494eee601870249249317497240124baef80229e049249229f27bbb8929212012486ed9949a65b6e93432994492024848490924924933799a6f33139892539ce6493dfc45efe229dc2497777124f7775d9352492122ec9a04d2092449248484924924dddd939892539ce6493777777645e3b8492eeee249eeee269349a924924240124242693484d49224924909242492499bccd379989cc4929ddcc927bf88bdfc453b8492ebbe249eeee492b26936c9a9249134269349a4d1249248924924924924924924ce739a494eee73799a6f352924f77724975f5f777f117bf88a493dddc9245d2e974ba9244924924926318c9246318c493dddc925dddc4926318c630000021005d54002d24800021021249200038e0eeeeeeee492000114f0492bbbb24977771202eab760925776924924004849249249249248ee3bbbbbbbbbbbbbbb9249dc24975df77f117bf88a492eeef767d49249212000bb0baaa491249248484924924bbbbbbbb8ee3bbbbbbb924ddf956eefeec8bc7709257776492eeee00000924008489a490077777777777700492ebbeeeee777700000baaa4900201007d00084924801204001dddddddc071c09240124baef80229e0492eeee924924492492492eeeeeeeeeeee493dddc925dddc492eeee92492449251aa9249249092428924d92499ce734929ce73249249312e4f77724977771249248a7c9eeee1248490128a03299449232db749addb329342651144cb603290926651248caf33375e669ccce64e189243fe228ff88a3e1f1ee23e1f24901408a0ca6d2d66edad636b74dadd0994b58d8ca40d826526d24cca5a769b766dd99b666d999cc9c307c3e1f0f87c3e3dc47c3e048124906532892566eb76c132895ac49949249994492b4dbb39ccce64e189243e1f0f87c7b88f87c000000048005809257692490022136d8002cd9004922ebccc5d799aeeecce64012487fc451ff116eeecf711f0f80000012b002b492b4900256b121366c8024917665d9dddd99cc802490f87d77767b88f87c0000021558000124842ab1204d957692b00451249b73399d398cfc8be45f5e453c00000000204800000010240490baa8005a57692495a4900004048da91251aad9b200018704e92746492bbbb339900008a782f497a22a495ddd9ee23e1f052492bb269f6ccb7692492bb49249008a2650ca49a7d366524d3e93e994a491966659976ee64d99f6667329243e1f0eef87c3e3dc47c3e
def cur_top_39 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_39 cv_top_39 10 1023 4 15 11 2047 22 4194303
def hint_top_39 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_39 hv_top_39 32 8 10 1023
def fc_top_40 : Nat := 0x51e6a8a3c8d5401b1a8034b51b6cca00d254633d28c06c50068ea291d1451b4a8a3495004dea135f9426b9284c6450fb18a12dfd43740284b735096e2a155c9425a4a8026750028ea035e9415b6280b7b5036d8a02dcd405a8a80047
def ff_top_40 : Nat → Nat × Nat := unpackForestF fc_top_40 12 11
def ci_top_40 : Nat := 0x8407a57a07a07247207206e26e06e06e06456215e25e05e05c15c05a15a05a05814694604604604414404214203a401d
def cv_top_40 : Nat := 0xa3ed525134ea3c8d6810570a205e8db66a289be84a677e69168ce7aa301b28b474a2ada68a3498d6d062aa3ea1edf686b71a14d6687d8ca1ba0285572a255fa88d72a211928737f8aede686373a16dc684b498bed0682b6ca06db28357aa08dee81373a02d469b56aa6959a9946fa631aa97c67a5919a94b6fa4adae90367a3ad8e8e34ba34d268bb478ded0689a6fa1099e2a23f7e48ddd896f70659e839476384fd661374401bcf6067a0011c9183f1f40dc27817
def hi_top_40 : Nat := 0xa529311f9c8e86279032771787d5b6177fc19e057a2d1d65723da1fc670a7ecd61e17d4a5d35052b597cfcee512ea6144dd8c8d54a9ccccf4435899a43cc101a4248486141b81c2440184c683a2d257b39e4101234a509502a2a869f1e827eea19411d5018d8141a17ac304b17601413162c404d100d458804ca6ed100012d32
def hv_top_40 : Nat := 0x485936c9a00246a5646d80012401349204945144d20e673399cc67e45f22f917c8a78000000092001755b4ad764d26ddd89a0162c0210162c001d40000028d55225244d364020005929d9e6636bccc5dbb98061c0ce64006975bf88bfc4526ddf00453c0f719f72b591d6d63adad63adac49b26d936ec95ad76bb5ddad6b1d4269d4ea6d269629244dddddad63a93a928d55225244d3a9b3a94893aa24db336cec94ed69cec759ccbb77326bccc757998ce664bd25e1a5d6b7758ebdc4dbbe26ff114ebfc453dc67c6de269349a95ac95ac2b2405ad6136c1349b6136d2b1b4ca49b4da484ca58a24d269b36936bccc6d799899b4b2532eddccce64dbfc4536ff114e32834b89b77c7b8cf8dbcacad64db26dd92b589a1349a4d269629244dad626c5126934d948926a256b35acec94cbb77326bccc4d79a94ce662bd15e1a5c4dbbe26ff1149bfc453dc67cb5eb1d4b1d6c75b1d426eec9580b1d49b63a9d6d6b5dddddd96128995148ea4ea4eb65d99766e6735b8ebde45f22ffffab591d6dffff63adad63adadfffffffe49bbbbffffb4aeeeeeeeecea4ea7cf928d552252566c954aa552affff95522a954aa552a954aa552adddd92a954d977762b591d6c912959b1d6d6b1d6d6bbb1349377777777695daeeeeeeed763a93a9b44a44946aa91292b3a9bb25d997676f776f662ea532e976732e97673bbbb339992f497aefeeefeec8bc34bad6eeb1d7baeeecf719f17783a8100b00753a9d4ea0164ac001400424a26aa49339ce60134a739ce6493dddc01c97777713c49eeee000242c9b64d00b256b136c4d26934ea4d3ad89b6024a2892492e673399d4be45f22f917c8a0590136cb5800009a4d09a6d00946d609009249219c733a9422f9e45f2280000016b02400000750000b58120024800058592b5acea75bb0120004924a24a2492400030e134a73799a6f334e7399248000453c392eefe22f7f117bbb89e24f7771365624a492414753a9d51d4fa653e9d51a0042424946739cfbbb89b5ad64916b196c6549136201b4ca6db00425124d8ce739f7775ac42001251d6d63632dac753a9d4ea6532994cb64ac4ea42000124924ce739ce739cd29ce739924f7777777725ddddc493dddd63ea34934da1b50196ec750cb768d24ca5ac7524fa19501949a65b26dd89a75024ca7d0ca650926996d6b5d936ec4d2684964ad626d89a4d269d49a75009a4d024a289210b99cce6752f917c8be45f22a46d249d52b2b5ac9b64db595a4d56a48ca4d369349a4d09a650946d6008492492e673399d4be45f22f917c8a49495ac95ad62c654650ea22c65b59248000ea58ca75329d409366532d86532964ad6b3a9d6ec0012049249449449266f334de662732694e6f334de669ce73249efe22f7f114ee392eefe22f7f117bbb8927bbb95ac8eb671cdaeee12e9ddcd98b6b58eb6b125dcc62e9b4ba6d2ea567b7777736974bb63a974bb6b4ccc9466912e897725253332eeeeeeeef377777777779bcddddcbcddc9578abc34b9fdddfdc8a552af7154abdc55e2af1ee2e557777e1963af1d6c7509ff1a5c01148a45eeeeeeb1d4eb6b26d9351e452e3c4aa552a955cce6fffffff3cefefb117bb88a6dff26d8ea75b77f0450e229b6c8f2c1d4efe22fd8675b1d6c4dd89a4db59d78269941dac972ebbb229148bddddddfe8f22971e2552a954aae6752ff7fffff7f7ffffff7f7a1d90c7e7fff84fafff363adad63adac49ff22914da6d1a43fbfffffb5ac75b1d6d6e3c4a3c913e89ff2525c78954aa552a8d21fbfffff98aa552a954aa552a954aa552a954f71fffffffffeffffffffffefeffff3fdfe7ffbffd5958b5824d92b5aeec4946aa912922673b253b3cccf334e66733dc34badfc45fe22f71ee33ee
def cur_top_40 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_40 cv_top_40 12 4095 5 31 11 2047 22 4194303
def hint_top_40 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_40 hv_top_40 32 8 10 1023
def fc_top_41 : Nat := 0x53f686a704914e01429cb4f539696a72d1d4e5a1a9c0240014a6a015a94d636a805665336d2a011bd402352983715008cea5adbd4b5b1a8046652a8c8a54995401b7a933575266a8a4c8d5401b5a90c7c5214faa429f14843e280367
def ff_top_41 : Nat → Nat × Nat := unpackForestF fc_top_41 12 11
def ci_top_41 : Nat := 0xed3b0ec3b0ec3b0dd29ea06808d630849e3781d1741d04ad20480f33c0f03c069180601806001800
def cv_top_41 : Nat := 0x2a134fa82d2ea0347a7ed0e9e34fa76d2e9d347a72d0eb3c5fac716eaec57ab514eaaa5eaa0972a7a54a9493aa2a4ca88912a1928a7c4929e828a700922ea3fa6b1b62e23f7f08dd8f13f5a24de51c64a66da651c6698c9162da3fa60dc69736fa5ad8e8b25da209562d23f7ec8dd8e93f59e4dc9303f1fa0dc298179439fa95c64a5499694357a4ed5250b4e8b2935fa2458ae8f693235a0815c290179459f69247ca469f69127c8b08f69087c
def hi_top_41 : Nat := 0xc478e0a8c078f100bb299954b6059949b091b95daad9996ea798e0d0a2f1a12a9c6181a495c16da8909d49498b451d568252823d7ba969aa75c1257a69b68703652ce9226020e943596981ae5379b17c4f951cf9470e8e2246401c333e61c1f838ed1d5d2d1e6ef42575c9ea1fed4d62188d95d81185a1c2068e9abe0001b9a3
def hv_top_41 : Nat := (Nat.lor 0x2b60095d552bb4900124924924924807fffffffffffffff9248015522adbd9adeeeeeec927fffc00012baaa49000024925500124924924924807fffffffffffffff92480249156ecaa9d193a4493fffe00000092004ad2492baa80124924924924807ffffffffafeffffffff2490049caa92748d3492bbbb249ffff0000bb492baa80005dda480092492492492403fffffffffffffffc92400aa9154ab76552ab954c5572a98927fffc00000092492403fffffffc92400aa552a954aa552a954927fffc0000000d54924924000100005801002739ce739cc92400c0e001dddddddc49200450f0eeee0b16b5812404d8858329b4b5ad6b5ad609944958d89b58926d24cca5a769da7699b666d999cc9c952dd6eb75b92bc6de3dc67c95e09b10b5ac75120329b43a9d4ea75b58eb6b58275025129247527524cca1d66759da7699b666d999cc9c307c3e1f0f87c3e3dc47c3e4ac9058ea0924194ca58ea75b2251213289225249226652d33ace7333994923860f87c3e1f1ee23e1f00012095d89a4db59d6c0164ad777626936c4d3adad6044fa8a44d3a9349d4da6c59b99d4b6e3af7917c8a0016b00001209005ac0001624800058592b5ad63ad8eb6b001d400880a355489491d49d4800061c2c94ed69cecc59ccdb336ccce64000229e034bad6eeb1d7ba4bc6de3dc67d25e2c8b5ad6b06536964ad6bb136d76b04ca58a36b136926652c94ecf3359e6636ccdb33399392a0d2eb7f116dfc9d4af1b78f719f257ac7d2c7509269b6ec4d26daceb62d62d6b0134b5dd816269d6d6b1349a89f51489268752d33acdccea5b71d7bc8be45b5ac04928ea95896b5ac8ea58002d6b582d6249d6cea753ad9d4329b4b256b5ac75b1d6d63aa25200ea4ea750a355489491d49d49d5e663abccc4cca5929dad39d8eb399b666d999cc9d7f88a75fe229d2506975addd63af74978dbc7b8cfa4bc75b26dad6580ab162ed63ad9d6eeeeeccb67528b0ea1d4ea497665d9b99ee4bc75ef22fddac156b5acea4d269d6cea6532ddd96b160b1d4ea7d283a9d493a87517b33acdcce692f1d7bc8be45b5ac04a2c4b5916b3a934eb64d0ca652c958ea889004ca58a24af5e663abccc4cca5929ce6673325fe229d7f88a71941a5ddc7b8cfb80000090000bbbbbbbb00b4ac0120000a366c975e662ebccc005d4a77776673275fe229d7f88a0034baeeecf719f17780010a9090b6b0000024802409b37776004945136e673399cde45f22f917c8a0000016b024000000016b01d400921755000bb4aeeeeeeeec00020146aa91292b36400030e05d4a65d7998baf335ddd99cc8000453c06975bf88a6dfe22dddd9ee33e2ef134db6b136c7d03addd81656a3a891295884db2ec2ec9a5a5609d43aa25226c51269d4d9d493568757998eaf335929976ee6673272b43aff114ebfc451a5c4dbbe3dc67d25e329943299426c9b64d0d964654ac65b595b644d492b136c121329251449a49a5cce67339bc8be45f22f91789632a3281632994ca0490baadd85a56bb26936eec4dbbbb5924ad6b595b6269d49a4d3aab6d626d802650a35548949134d9269265249994b253b3ccc6d7998bb77326bcccbd7998ce64e32834badfc45fe22936ef89bfc456aff114f719f701d49a752681636a3a89594892ec0bbb2eed2b09d4489b44d9289b3a9bb24cba175e662ebccc5d4a77776673274943aff114ebfc451a5d77767b8cf8bbc4d0890b6b2152b3699525777695dd86d32848437777642650928928d9b2e673399cc6733e45f22f917c8a7b89944289590a90a959636a32895ddda5658da6d328490dd9765a577777765d997664cba17529976662eccd77770de42f1c6506975b8dbd77773e2ef79e7fff9636a329fffffffe16369b4ca0493ffcbb2d2bbbbbbbbbf3e42650a3554894959b3fffe154aa15522a955caa62ab954d77764aa5537695da5762c6d4652eceb77777777776b058da6d32812400bb0baada5777777777764dd9b242650a3554894959bb36f776f66265d0ba94cbaf33175e66bbbb3399bbfbbbfbb22f1c6506975bf88a6dfe22dddd9ee33e2ef0000000120001764d26dd9349b69580001200a48934d9003abccc75799ac94cbb7733399003aff114ebfc451a5c4dbbe3dc67d25e (Nat.shiftLeft 0x92492401dddddddc92403bbbbbbb8925dddc00006318c00924924006318e739cc924008a45229148a45229149248a4522914000002d 12288))
def cur_top_41 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_41 cv_top_41 10 1023 4 15 11 2047 22 4194303
def hint_top_41 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_41 hv_top_41 32 8 10 1023
def fc_top_42 : Nat := 0x55e2d8abc1b14e22baada4655b488a7114d559acaab95c5570b8aacd554e12f2a8b4b5522b8aa4171545a3a9c25c5384a8a97179530ae2a605c54b8aca70939519a7aa395c5470b8a8cd1d4e12629c244538250a7ed3d4fda5a9fb47
def ff_top_42 : Nat → Nat × Nat := unpackForestF fc_top_42 12 11
def ci_top_42 : Nat := 0xe952681408240201007130980c0602890480402010062211008040110080000000000000
def cv_top_42 : Nat := 0x2ab94ca984f2b1678ac2db2b026caac972a5a4cabe5b2a0124abc1b29d024ab891aada44a7e4929c824ab0572ab85cab2d66ab355aa6572a905caa8d2ea8b47a9a572a605ca9d17aa5c56a90572a385ca92d3ea3347
def hi_top_42 : Nat := 0x8fc9d14d8782de1283ed0ce57dc5f18a753ab22370059d4d6d2cf0b66a04f0ca648db55e5dfde5a4586999655590f0b65268f0ca4cb1b16e49c8e8ba4708f0b041819d623ec4f0af3bb8f0c3365db5572f3de5c82985996e26c8f0af23bcf0c31e59b1591b50e8c21860f0bc1500f0d80fc9994e0abd99430539b9610001994e
def hv_top_42 : Nat := 0x7fff807fffa4200035524924924900f3c0f0602004202c02cb00801fffe92577764920062e8395400100000248012b4924aeaa0006aa5124924924924900400084002004202c02cb0080093a49d234d24aeeec92400c5d070004bd25e9117924aeeec924008a30f0eeeeb4aeaa01776002480000bbb490001aa924924b99cd39ce7e45f22f77700005da495d540000bbb00004900000001aa84924924924920134a73bb9cde669bccc49201c9775df77f117bf88a493dddc0001769257550000bbb490001aa9249249249248058b008401342681658162c000001002694e77739bccd3799892400c5d07000e4bbaefbbf88bdfc4524900228c3c3bbb80002ed765ddac0000ac95900124924924924804e739ceee69d193a449201ddddd77cbd1157a4493dddc0000eeee00eeef76580124924924803bbbf7775ddd92480007fff807fffdd960049249249201fffe552a954ab7776492000000958012bbbbb2ed76002492492492490049d24e91a739ce777764920097a4bd222f77775ddd924f7770000000000016b256b5aec4db5dac004924924924924920139a9a9ce73799a6f334e73992480772e5ddddfc45efe4ef777124f77700005daed776b00005dddad600249249249249009ce739ddce6f334de6624900eeeeebbeefe22f7f114927bbb80001dddc01dddeecb00249249249007777eeeebbbb2490000ffff00ffffbb2c0092492492403fffcaa552a956eeec924000002eec01777777776bb00124924924924805dbdddbdd9a739ce777764920177f777f7645eeeeebbbb249eeee0000b580092492402739ce739cc92403bbbbbbb8927bbb80001248009249240124a739cc9240124bbbb8927bbb8000002c9b600244d49589b764d00249249249249009a53b7b35bddce73992480725d7f645bfbbeeee249eeee000077770077774840049249249200eeee925dddc4920001fffe01fffe9080092492492403fffd248aa552a95492400000124009135248489b6002492492492490049d24e91a692539ce64920097a4bd222f2497777124f77700000059349b64d268000136c4d44d44db00004924924924924920139ce739dcee739cde669bcd4a49201dddddd7d7ddddfc45efe22924f777000000589a4d00489a4d4ac4d4900124924924924804d29cde669bccd39ce649201c9777f117bf88bdddc493dddc0000eeee00eeee9080092492492401dddd24bbbb89240003fffc03fffd2100124924924807fffa49154aa552a92480000024801226a49244d26801249249249248024e92748d34929ce73249004bd25e9117924bbbb8927bbb800009a4d00249249009ce739ce7324900eeeeeeee249eeee0000bbbb00249249009ce73bbbb24900eeeebbbb249eeee00002e974ba5d0024924900318c6318c624900eeeeeeee249318c6000000b5ad80257554aed240049249249249200eeeeeeeeeeeeeeee49201c975fd916feeeeeec925dddc00012baaa4900002492d500124924924924803bbbbbbbbbbbbbbb9248024975df2f4455e9124bbbb800000248012b4924aeaa0049249249249200eeeeeeeee9e6eeeeeeee492009795525e9117924aeeec925dddc0002ed24aeaa0001776920024924924924900777777777777777724900e4bbaefbbf88bdfc452497777
def cur_top_42 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_42 cv_top_42 9 511 4 15 11 2047 22 4194303
def hint_top_42 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_42 hv_top_42 32 8 10 1023
def fc_top_43 : Nat := 0x56a2ceaeedf55f6462bbb4f578918af0e315e5be2bc234577686ad41bd5ae38ab5b7156b6daae12315c23e2b838056b69ead91f15b1c62b637c56b686ad419c0052bab42545388beacc9115922f2b22445388b6abd9e1579b62af26c
def ff_top_43 : Nat → Nat × Nat := unpackForestF fc_top_43 12 11
def ci_top_43 : Nat := 0x960cb025032419204902403143841c2020830018004002000f437a03d01e80e836830d9c68020510007043800850400200100002
def cv_top_43 : Nat := 0xaf6d0abec8caf28d2bcb7caf7232bd38caf08d2bf37daf8d3ebbb43ae117ab7342ae5232b8c7cae0e02b747cadae32b637caeb1c6ba371ae6db6b7b4fad6d0cf8a7cd811bf5ec6ba631a75bc67d2518f48461d1b16f43c57cf0dbf39b6b8f8da734367c66d8f17b61c56d6f12b57c3ad3f0a34bc1ad1eca343a1093e5b2478bc8fdfd237b165bebf96770c55db114f67451d8f93f5a64debb06fad419cf80573a413cbf04724e0fc7f0370a805eb2d6ead0952a724ca844929e024acc912b2c5eab29b2b2244a824929d824ab0532a693c
def hi_top_43 : Nat := 0xd88a7a79aef0608b52a202d69ec101ad2804857a500000345a0e11e6c0507db634f5d555b4d5ae7ac98c2cc3cc0c7977038432e5010265880e10c9bc40559248304d21d090b23fc0c0fc57c689f75f44d42dd53f3a58b0eebea946ae074e8941008c04d444e8aeebd9532adf920ab2a6e2f0654942a2fecf8001d151
def hv_top_43 : Nat := 0x427fffddfdf7ff849e6d5e92aaffeccbf77e65bbbb08421ebf33fb99efffbfefc8bfffffdf7dfdfe45bf22f916ccb7f665fb8a8fbbc8beac6532f917bce245f1a562a1de451a562a34a9952bf632f865e3dfe45f22f914924879018cca9518cca95fff32faff0ca30ca6532994ca658afff997effc3299418c0027c240903dc78f1e2552a954aa552a954abffe6f7ff0aa550aa31954aa552a954f71fefefffffffff3fbfcfffffefffffe3fdfe7ffbffc9561d8687d61a493a454ef777771dc7f9b4ca6d8a8ed64dbb0043dddc78954aa552a8caae6737fffff7f7fffff9234a8d2b64d26934cb665e269949b7764522917bbbbb8ee2c95bfc021eeee3c4aa552a954aa55733a97fffffbfbfffffffbedaa122ff36a4aabbffb32ddddff043d6ffe6733dffffffd916efbfa7b67dbbefe22f7fdd996eee2a36ef7f355591951b622f771cf52d538f9148bcac34ad9362a3ffb254ca950cadde28dfe22fff9148bffdc49f5ffffe319952a319952a19467dfffff994ca6532994cb150ca65063ffe000903dc78f1e3efffffe62a954aa552a954aa550aa550aa31954aa552a954f71ffffffffffefe3fcffffffff3fe7fffc92905d8000481aa924bcccf33132739ccce67f88bfc4538eeee3dc67dc0000016b1f40000004aeaa95d80024800092492492492402694e6f334de66bbbb24900e4bbbf88bdfc45bbbb249eeee000000bb004aeaa95da48000d5492492492492402c5804202cb002c002c02cb0080134a76f66b7bbbbbb2490031741c00392ebfb22dfdddddd9248011461e1dddd6248015800000006aa492e6737917c8b62480158006aa49208b084584d2cb2c580b0011ccea50317475a9e45f4e811467a5400004aeaa249000000024809b63a800000124924924924802494eee73799a6f331248024975df77f117bf88a493dddc000095d5524800012490001aa9249249249248020042009a1340b2c042001000100124a77734e8c9d22490031741c00124baef97a22af48924008a30f0eeee10242b00924ab4d54924924800840ad000b2c0892539ce77776492000925dddd7776492001dddc01d6aa000089201649484007500042000b2c009ce73492bbbb00000eeee492bbbb000eeee000000490000005dd8000249095d5400924924924924026757799a6f3998c925777649201c75ffe22f7f71148a9257776493dddc0000eeee00eeee908000d5492492492401c701c2e80801080b00b2c02003bbba495ddd9248011461e550
def cur_top_43 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_43 cv_top_43 13 8191 6 63 11 2047 22 4194303
def hint_top_43 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_43 hv_top_43 31 8 10 1023
def fc_top_44 : Nat := 0x595468b36e3166dc22cdb7459b468b2a4dd659c62cb3845966e8b2c8d16541bab534358c8fab24e31631a5ac6d8c58d718b1d1f16351a2c634356a2deb011c560236ac0371585b00b0ae31615be2c034b581af8b02e31605be2c0343
def ff_top_44 : Nat → Nat × Nat := unpackForestF fc_top_44 12 11
def ci_top_44 : Nat := 0xfc1f83f07e0ec9d83b0760ec1b918fae15c0b0550aa0540a05119c3342604c01803006009192024048061806
def cv_top_44 : Nat := 0x2cf38cb3ae12ce374b368d2ccb8cb30e12cbb74b2c8d305d7ec155cb01c7ebff1caff37fbfadfafc37dbe2df2f7377bb2dd6ec374baadcae7b6db96d9ee2b65b88d922fa3db768eadb237b528dad4235b3e8d2c617fb005ddc4167b344debb87fad61dcf9067b2a0dc2c817b20d06c938cb1c8d2c747cb21632c7b8cb1a8d2c9c7db22d2ec6343b0ed66c1b41b0f602c338cb0adf2c1d7cb04e32c0b7cb151c6c4c6db10dc6c234bb00d0dc3a7c
def hi_top_44 : Nat := 0x909830371e40a0be3621019c6241c2888e898d90fb0608a19214194268202f83903851005131b5b1d233bb1553d3961e03032be81015179c080d2ea424255d480000b81070a1604283fa0567aed353a62dc5dd303288969ac910ac1c20207838384060102476620298e20182b1ae048583400607053c34510002269e
def hv_top_44 : Nat := 0x1e6e633da733cdcde453626974da6d2f62681b4daead64d2eb9b5cdb6b314d3999de7fde4522fdaf22ff39bc8a6c4d1b55aa7ec4d06ab57d5ac9a3f6afb56d672917b88bffc49495ac95ad62c8bbb26936ec9a4d2684db2ed24aeab632dac65b5ac058ca650bbb49000481aad8a24d366c4925e6679989964a65dbb9d9e667998ce67f88bfc45381a5c4dbbeb7f117f88a7b8cfb884777749d4dddc24774bd749cca9273edba5ada41084334ef3774e6777774f39bf917dfc8be86ee64e67328e9751953a5ebce6e67565e995cd37264cf1d2ead426e68e9756a5d329956af65eb865999bb99cce624920e417a655e9957abd8ebbbaf5d3b8653285d2e9957a5d2eaf56aeeebd7b770ca5d0ba5d00097090240ce66666665e6f37777777771e6ee3bbbbcddddde65e6ee4aa55ee2a957b9fdc8afeee71542af1578abc55e3dc5caaeeee4ab5ac654659d8ca92318d39ce7399398ee5d329756b6b26dd80219ce73332eeeef379bbbbbb9578abddde45f4ebcdd1b4244ee8ca92b773ea5ada4f308669dddddfdfc8be45f449f4ca7d8ed934ba4d2ed97664d2e9749b776a53296739ce732732c959dc0219ce73332eeeef379bbbbbb9578abddde45f22a48db379a325379cd4d34a3a5d7748ca9db3799b6c9a8ca8db1a739937e936932e634d5a3b64d2ead4baef6329956a195db328d7999ddcc6779cc92e9ddddcca6532994ca658e865328f6eeeee5d2e994ca5d2e9956a194ba174baef300090339999999977777777779bcc771dddddddcbb97f777f722954abdc552af71c550abc55e2af1578f717777
def cur_top_44 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_44 cv_top_44 11 2047 5 31 11 2047 22 4194303
def hint_top_44 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_44 hv_top_44 31 8 10 1023
def fc_top_45 : Nat := 0x5bc6d8b7a9f16f5362de27e595474b6f1e16e5bc2dbb8c5b76e8b2a8dd6aabf2d547e5aa6d2b54d856a93f2d526c5aa4ccb571796adaf2d5a625ab4c2b549916551b2caa355a08dcb41189681b72d03625a04b2b4094568097ad002f
def ff_top_45 : Nat → Nat × Nat := unpackForestF fc_top_45 12 11
def ci_top_45 : Nat := 0xb42d0aca56906408c63080df1785e0745d0741d0741d0741d0650fa3c0e1380d1340d0340d03400d
def cv_top_45 : Nat := 0x2df27cb7a9b2e1d7eb851fae0b7eb7edb2de27e7d48d2dcc7cb72de2dd478b70e32dbb74b5c992d6a64b568d2d745eb5ad7ad6262b56986dad7eb691fad9b69b64d86d8a7eb609b2d7a66b54992cd925b2c096c716daf21b6d3c6eb4d18ad2b6eb48d8ad1a59b44946c696f71255ed092faf01bcf9857b400bc2d817
def hi_top_45 : Nat := 0xbf60203beb040bbc00e2bac66afaa9e1028a950209a711424a44142d9e6285e9be1028996102897c0a1a96e060e93d18318ba348389114298720c1f8530c1f84a020984102097b13c906c968e8525b3a44b2227340f34a3393227c2f034a32b6163a20948ad1dc102d1b0102c000bdb0
def hv_top_45 : Nat := 0x6aa12aa65328ad26d6b589a4d26936d2baadad632dad62d632d8ca5da44212c5de739cfffbbbaaa650928d2aaaeaa06c486c4daa9360956b26d54b582c8db23493626c4d416b2349b6416b236aa428daa92c4b226dd54028d11b6b5ac8d269349a4d2c008d01dffec6c4daa8006c4d4750936c90a2b4eb63626d6b589a4d26936d2baa86aa58b0effe4dad6b1349a4d26da57552c5802d6b236d6b16b58bb4892ef69cffeddc4a352b246dac8dbb26da349a4d02d6b1951a652c06546994ca234b24a24804909b1449a6cd8b99cce67319ccf917c8be45f229ee24d9591a4d46934fb63ea351a8d18c9491b66d26da349b552d6b2351b1d9c76695e4af124db26a36c8db1b6c6d46a34ba5d46928d47db246daab76589a4d46a356b35ace2bd15e46a351a8d11a1011a8d46a34b0595646c9a8d0011a3166c5983979cbc1626d98aeef3b136ce5fffe24ab595ad62c8b26936c9a4d2684db2d2b05ac8d4696011a8d02cab2364d79a35e64cb2532eddce68d9ff237f8e0697136efb91bd3ee
def cur_top_45 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_45 cv_top_45 10 1023 4 15 11 2047 22 4194303
def hint_top_45 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_45 hv_top_45 28 7 9 511
def fc_top_46 : Nat := 0x5dd8f8bbadf17753e2ed07e5db6f8bb41c9655baacab745d66fcbacdf1655b92e867e5d0afcba11f9746be2e837e5956dab98df1735362e628c5956ceb8d5b971a372e336e5c64fcb8c9c9655b2acab645bcafcb791f96f1bf2e056e
def ff_top_46 : Nat → Nat × Nat := unpackForestF fc_top_46 12 11
def ci_top_46 : Nat := 0xc4310b8ee0b45fe7c1f07c1d26c9b06c1b0685464c530484f3384d1340d0304390c0300c02108002
def cv_top_46 : Nat := 0x2efc7cbbcdf2eea7cbb6df2f6e7ebd99f6f5d7ebd31faf437ebacdf2f3a7ebcc9f6f117ebc05cace935bb81faed072b300d6ebb7ebacdf2e8c7cb80922e8d7cba99fae9d7eba51fae837eb7e8e2d8234b9a9f2e6a6cb9cdf2e628cb5e8d2d7234b5a8d2d6234b955bae4c6eb90dbae3a7eb8c9cadba35b548d2ce135b2e0d6df27cb815badea6e
def hi_top_46 : Nat := 0xbce0201de700002e7030657380000b691019d41b239a127847506218187d5302e357be499a103856cb41c2a6300e1531701009880281ca3ed5014fc1411a7981025338404a8e4505c448101520f080a8fac60667a414193c50606968b53d02a75c500fe1c2a0550e15023850380f010160003c3c
def hv_top_46 : Nat := 0x88b626d54aa951d99a31ad59be95ab5dddab26a5695d56c58ca5da5628d2ee6731ad39ff917c8a45b77194ca65465576958cb76591665b4aec9a654826d96958ca653284ca58a24d364ca6577998caf33298c4cca5929976ee667326532fff114cbfc6522914e32834b89b77c7b8cf8cbd625542122b576ad042e6737917c8a4ab2b5936c9b62c13625ac4db0043552c4d80ad66b59bd8c6b3ba952bc95efb1148b6ff4ed551a4ea234b13558ca2349b6563288d2c402d6b589a4d26936d2baadad646dad62c65bb480205ac6c8d2ef69b167ff6e72f0580abaa9aa85540ca196c6c55ac9b552c65b1608194d89aad626524db2b5899492d644dbaa909aa8196aa163626d6b589a4d26936d2baa816b58cb6b5aed22485ac4cb62ef69cffeddd6b126532d892d59196d65632dac2b26d9949a4db269949a4db4ac65329265265240b1449a6c9966659995e66579d929976ee6673265e32f197f8cbfc34b89b77c7b8cf8cbd626ab19446936cac6511b6205542d62693484077ff
def cur_top_46 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_46 cv_top_46 10 1023 4 15 11 2047 22 4194303
def hint_top_46 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_46 hv_top_46 29 7 10 1023
def fc_top_47 : Nat := 0x5958e4b2adfd655bf2fe3545f9adcbf4d517e6372cab7d5f2acebe495d7c8afaf91575f20bebe415d655be2f798c5ef118b2addd76b3f2ed67d5daafcbd51f176a3f2ed37e5da4fcbb49f578e3e2f1b7c5e34f8bb45f9785be2ed172
def ff_top_47 : Nat → Nat × Nat := unpackForestF fc_top_47 12 11
def ci_top_47 : Nat := 0xedf56d4332cc312a9ea0a82a0a82a0a820a74da34a111440e3380b315841100401004004c1000400
def cv_top_47 : Nat := 0xbf7632fcc8cbd0e12e837cb90dd2e0a38b628d2e8561b8294ac797db025d6bd07dad81d6f546cbf8d52f546cbf4d52fdd6ebf31bae7376bd0d9adc235b3c4d6cc835bef59eeba67bec95dc5167bea57efa1573e819ef985fbe415c2e017bcb1b2f236cbc69b2efc6cbbcdb2eea6cb75a32f5d7cbd31f2ebb8cbd0df2e628cbe0632f788cb731f2f547cbca5f2ef87cbd51f2f217cbbc1f2dce7cb9a9f2f197cbc25c2ee87cbb61c2e6a7cbcb1f2f237cbc69f2f0b7c
def hi_top_47 : Nat := 0xbd240a1459b34e898101d0008139f804093a4204e0ab56a40e060780e0c0efe41839f583073da06117920c2293f15e8fc0b2b9a1165726e44d448c185083070e8ee0a181d6040633c287057061089a06140f41c401dc080c3a0101874000008c185c11800000188218000203
def hv_top_47 : Nat := 0x162595936d556d632d5424dad60924159595abb26d936d5a0086aa01099cdcce6eef22f9155a465b568ca12256aeeeed5a4ad2baa962c65bb4821b12e6735a73f22f916ddc1081a6e679917bc8bfc04902c84ad695d84db2ec9aaed2b4ac100909b1449a6c931e66799ac94cbb773339938fe22ff114697136ef8f719f7589b55b196cc532d565a8db136ab632d9ca65aac151b6576b44daadac8d32d54ca8d9f554aad5432842d29a8d2b45d66ab226dd54aad56aa124a3523589b552aad66a5d2e934bae9566a
def cur_top_47 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_47 cv_top_47 10 1023 4 15 11 2047 22 4194303
def hint_top_47 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_47 hv_top_47 27 7 9 511
def fc_top_48 : Nat := 0x61e6e0c3c9155a9a7b0e356615ae4c2b5c1855bf30ab7c6156e8c2ad398551aab534b60eaf0c1d5c983ab830725d60e2b8c1c1715a9a3b06355595afcb2b5c98123f3043456048f8c091c98163e3023555958fcc015f9802b9300570
def ff_top_48 : Nat → Nat × Nat := unpackForestF fc_top_48 12 11
def ci_top_48 : Nat := 0x94102a003f17e0f49e83d0746e8185300600c0180300600a99411bd2e85c0b81522825009105d08210020004
def cv_top_48 : Nat := 0xc491fb11c7cc451d30b45ec40dcb0fb70c3c916be07fade1dcfa867c38d5ac917db0a5d6ebb7ebacdf1f5234c375cb0d570c32dfb0c37cc2edd30b34ec2a8d6c897fb085ddc5967c275e309572c235c30825dc1e5730705cc111f2fe37cc131fb03c7cc051cafdb7dbd6dd6e9b6db94d9706355b868eadaa36b4e8d2c817db065d70347ec031cb00470b4c8d302b55c10d16f547cc0b1f2fd37cc131fb03c7cc0d1cafcb7dbd2dd6e936db92d9702355b848eada236b4a8d2bd87dadc1d6f547cc055fb00d72c015c2d2234
def hi_top_48 : Nat := 0xf4425a79c1c9a9b381408096d34a4bdcfc2c2ab92834342efadcd5d6f195c1a2f25abd3244b4ea1b935243cd19da87269d9cec9c766c572e8882a8b5996a4533330e655a2944c5e0e131548a8dd21c1b2343fa080f87dc04060ecc2c3b1bd0407236e020306980e110990a8e8116040701e70c11428e3c500000d947
def hv_top_48 : Nat := 0x2559580bbbbbb2c10a8542d8852c49bbbbb46d9f494402136364db99cce67319f917c8be45f229e24a56b256b1645dddddd996eeeec2eecca17777777777765d895d552bb49000481aad8a3764d9366c975e662ebccc4cba17529dbd9adeeeeeecce67f88bfc45381a5d7f645bfbbbbbb3dc67c5de495549495936c9b769246546d48caac8021aaa46c7671d98f87c1404db2eed7761246d1592b20a028934d948a369266d2d3b4cbb77349233993860f87c3bbe4923dc47c3e2524122492495936c9b64dbb24010d54219cdcce61f0fbc8be450251012124924826d9764db5d936c924905004a09451269b24cda1b5e6636bccc9245dbb999cc9c307fc451ff115248777c7b88f87c753a9d52492491b5091764db5d936c136c492369b4ca14228934d936bccc6d799899b44922eddccce647fc451ff114e189243bbe3dc47c3e25249595aeeeec9b64db492b5ad632d8cb6b58b1632d8ca2b48021aadac4d91a5cce6733a97c8be45f22fa74949248d46db26d93404924840753a9d50750946c490084944d28b99cce67319f917c8be45f229e24a4924924245d9349b764d2684db12baaa49249248ca92481246504924001206aa8a24d36522512f333ccc4c4922eddcd3a32748ce647fc451ff114e189243bbe5e88abd23dc47c3e120ea753aa492491762495ddddddd81280d551455aad56d9b24cba249175e662ebccd7776673270c4921ff1147fc45bbbb3dc47c3e24a4924824492bbbb495d56eeec0086aa1097665d9b99cc3e1f7917c8a240128824924917624924aeab7777777604a035545102504d9b24cba249175e662ebccd7776673270c4921ff1147fc45bbbb3dc47c3e24424924007511d4ea751249126eeeec9200425128db99cce6737917c8be45f22925dddddddc771249248487777bbbbbbbb2ec77774920009035572e5146cd91ff1147fc453863bbba495ddd9ee249ffffffff3fc492492123fffeeeeeeeecbb3fffd24800240d57cf9451b364aae553155caa60aa553fffd24aeeec954aa4929248ca92492046548124924848495ddddddd97625692495d5400240d55129128a366c975e662ebccc4cba24e92748d3492bbbb33991ff1147fc4538625e92f488bc92577767b88f87d7626ab2aa93656b26d934fa92b465b1f4ca65b194ca654900435546a36731f0f894959b49b64dbb5aeed6b58cb632dad632d8cb76b5da4010d56d6b2363b38ecd2bc95e26d9194ca65aaa35556d248ca65b48d4693558ca65baaa355555acad755249b64d565636da4accb636994cb632994cb776010d551a8d2eccbb3eeb226994caaaa8d2aeab632996d15546dab136ab6b196c65bb5aed589a904355b5ac8daa928fb656bbb26a44d44d26d89a6526996c4d269949a65bb44d26a4010d549a4d26a356b35ace2bd15e
def cur_top_48 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_48 cv_top_48 11 2047 4 15 11 2047 22 4194303
def hint_top_48 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_48 hv_top_48 31 8 10 1023
def fc_top_49 : Nat := 0x63e6c0c7c9b18f5ba31c16c63a6c0c749b18e5ba31c06c6346aec688dd8d09bb1a03756a6c6c615ad8c6b8b1826756a6c2c595c58b1af31623456a6b6c4d1c58a630b133606264f8c4c1f15a9abb0f47e61e8f8c3d1d1885a2b0f372
def ff_top_49 : Nat → Nat × Nat := unpackForestF fc_top_49 12 11
def ci_top_49 : Nat := 0xd4198b20e40c8180af0d45a81502a02774c098120986300600c0123202400708e01c01901102004008000800
def cv_top_49 : Nat := 0x31fb60c7c9b31eb74c76d831d26cc72dd322e80c8960320484c785b31c06cccf5ff32579cc55cf2ed71c9b1d31045ebff14b24b5fc8cd7b1bb57baad4a8625f97695e31a4d7fa9171b2376ca57d9f957c6a4dce985f30815f1a0370ba05f18d71c655af14466c3f17b18267a1697dfda45c5d5c716b5ec588d314b70c5318715471c50d8313a7cc4c1f2be87dae21d710b45
def hi_top_49 : Nat := 0x84d4040984b0040984580c16843404098410040983ec040983940c1682343c5881543838804434447f24344874761aac6ea125756dfc28296a24e8f661ad9e1e5c45255a57490d3f4f7d89f342229f573c8941663ad4606d343d91a62cf599d2264d99aa1abebae41770d0d3108db9b9095d95cc0908101505e0a4ca00016178
def hv_top_49 : Nat := 0x2ab5526dd56ab55aa936eaa8ca9136c9a4dbb226d567c4db084d36409a04d2eb99e7669bcde64d32f917fac8bdfdfc493e994ca7d0ca652ec9a6526936ccb6134cb6652c9b64dbbbb024ca409a91349a6532800481aa924d36409095ead67332ad67326652732eddcc9af333ccc6732658af71962bdc7194ee26ddf137f88bfc453dc67dc0204016b5aec9b762693402c95ac4db1349a4d32935ba49269348653e994994934ca1073399ccea5f22f917c8be45b136ecad24111955936c9b776164dbbb00b256b2680402420e673399d4be45f22f917c8a1f409a4db2c9b64d268124d204db135135136c4d26934213e926934d90249a124d6a2d667d9976ee64d79989af35299cc9d151abc7de26ddf137f88a4dfe229ee33e5af0005ac0584db5936ec5d91352b5ad6b5ac4d26d95aad24812c6508194da652652e673399cde45f4ef917c8a4565603ad8fb77665b1f6d6b005acadbb26d9949a4d26d8100102c4ca5cce67339bc8be45f22fa742194ca6532805ab49a4d09a652693402c9b64d02693400015a002b55aad56841db376cc01db376ccbb77356cd5b332f197800cbc65e26ddf2b795bd3e76f0432a32994ca8ca01665bb26936ec9a652693400b0b26d9355a6c934ca4d26dddd92485ab49a95a89a650000080194994934ca6cca49a652ad255aad3292657998caf33002f66bd9976ee64d79995af3319cc997f88a65fe22801978cbc4dbbe26ff1155bfc453dc67c65e21952b2b5ac02329d6c75b5ac65b196d6b0058ca5dddddd996eec4001009b13297339a737339bc8be45f22fa74047d02c4dbbb136c4d213632ce65977776007d2ec9a010009a4d26936cca6ec0201949f48102eeec00bb32eccbb32eccce66eeeeec00ca3578fbc4de26f1ee33e2ef001760000850086542a14ca65329b4ca653680042eeecbbb32805ddd97665d9976662eccc005d9976777770de42f1978cbc0065e32f5dddcf8bbdfffffffe0013fffcca8ca6d32a329b400f0bbbbbbbb00bbbbf3e400080194994d9b3fffe5572a98aae55300154aa552adddd92a954dd9949a49377777649604b5776acca8ca6d32a329b400ca0177777777665b02c02eeeeecca4dd9b2400080194994d994dd9b7bbb7b3175e662ebccc005d997677776673377f777f7645e32ff114cbfc450032865e32f5ddd9ee33e2ef13776122b2b2b2b5dddab5776010d54212eccbb37339bbbc8be45026c8164256b256b17625776aeed5abb0d804d84d8a366c932e85d7998baf3317529dddd99cc9cd50fbfc453eff1146975ddd9ee33e2ef1f4fa854ad64ad62c8bb4aed2b3ed9765a567d3eab43658a366c975e662ebccc4cba17529dddd99cc9f7f88a7dfe229cd506975ddd9ee33e2ef5ddd5495656bbbb32d9f6ecca4dbbbb4ac021aada34bb32ece2bd15e2c82eecfa5936c365924ad764d0d9628dd9b3e90d9265d0ba94eeeecbb32eccce64e6a834baeeec9bc4de3dc67c5de
def cur_top_49 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_49 cv_top_49 11 2047 5 31 11 2047 22 4194303
def hint_top_49 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_49 hv_top_49 32 8 10 1023
def fc_top_50 : Nat := 0x65e6accbcd518d2b8b2746165a2b8cb4171965a3b2746064e6dacaa51195422327b5f652268ca40d193dadb27b5764f6a6c9cdb18d23a32568064b6f8c952118d1afb23d7e6478fcc68d798e34031c580641ae0c831c1905be31c484
def ff_top_50 : Nat → Nat × Nat := unpackForestF fc_top_50 12 11
def ci_top_50 : Nat := 0xc024c88a20882027c5d2741d06c9b06c19264190550f63c0f0384c2300c024c90240901c85201400
def cv_top_50 : Nat := 0xc0118330c5acc115b2636dc88d972fb56c8ad572f354a1a9b65ea658c8935ffa45c84d5721b45cb65732d05ccb2d1f25b4ec82d1b2b144caa11329934ca40d32a35fca2d6f28357c9ed4f2e461cb11832bb6dc9cdb32534fc80d1f25b7cc99a0325484c915fb23c7e30a1571f95cc761731f14cc7413321d70c851c320b7cc7a5731c85c
def hi_top_50 : Nat := 0xa3544848d78d5e8303ea7827020981e020980708176da812d63c3e9e633020962a020960f081b60602095fd02095cb10325b904125a704124747b332c6b5ae2a20e2429902092790a2021a1c5f20608141f9040d0b481450910a2306b0c26055061604306120280a1b0090a1f0000209
def hv_top_50 : Nat := 0x1224924aeab7768213a842e6737917c8a65328486532994cb626d89b64d26dd93424b59256bbb49589b63299421aa84210b99cce6737917c8be45f2296329632ddd89b6b04355b1329b194bb32ecedc65eaad56d559f163281b2c4db013606ab626521b24cba17665d997665d999cc9c652dc65e26f1978f719f177ac9b6b5d86c26936c9a10d54364bb32ecc9bc65eaad56ab559f556ab5510b552ad9f556ab55aad885032994b2ad204d81aa99499497665d9932e85d99766673265e32f1c650cbc65e3dc67c5debb32ddddddd865329761b09a4dbb32813606aa6526521b37777764cba17665d997665d999ccdddddd9c650cbc65e26f1978f719f1778b1352b556ab6bb136aa7d3e99559349b64db26d9556c9556d0a4a3ed95ad6b1f6d6b24aeecb1d4b5ac9b64d26d913558021aad8b74ad66b59b99cc95e4af5bc8be9d26936ed0a4d26d92aad936ab559f5daab3eb26d567d55
def cur_top_50 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_50 cv_top_50 10 1023 4 15 11 2047 22 4194303
def hint_top_50 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_50 hv_top_50 28 7 9 511
def fc_top_51 : Nat := 0x6798eacfb1919f5a433cc7367aafccf55f19e62cab536f6776acce95c59d23e33a35e56a6d6cd31f19a638b34c7066eaf8cdd1c19a636b3635d6692f8cd4d759a43e2b5367634afeccad55995aa31a5796636a8c695cd97a2d32f456
def ff_top_51 : Nat → Nat × Nat := unpackForestF fc_top_51 12 11
def ci_top_51 : Nat := 0xf43d0e5390e43549be608ce21881c6701a26098060144501314c121264541405008c200080000000
def cv_top_51 : Nat := 0x318e8ccfd19303350cfad233dd7ecf55f2ebc7ebad1f31857ed0b1ff41c7dcff1d73e473cf31673ab78c06d0a8724f97c91e32a3dafc1f6b98753a813cc4847ceed5b37b54c62d3b27354ced5c73ac7c8c4d933a35ec60d3b16234cdd5f32e370cdd1b72c360cdf5f337470cd85f33507ccd8d773535d8055f33947cce31c738470cdb1b726b60c4e9f33597ccd21f318e8cc0514323b64c90d7318d6ecccd5732b54c0318331b54
def hi_top_51 : Nat := 0xeeb81019dbd0406baf41821f5501826e9185063bdf455132e31d37653c1422c071ba8363b5874e95292c9461e2722803b3300e46597058b0d0f72f1c84915b18e0c8a7a393a541e3835a12195c73f08e0ce5ed657d064525658b70304615f0283c209212d41a66e9b02e4141a02f880b403d070880320c1200001419
def hv_top_51 : Nat := 0x23a936eeaa6d32d9256b32ddd56c91d6aaddb1d5595a566e92acad6b5ad6b24ad6b162c75b1d4bbbbbbbbb568021aadac4d9badd25d99766e67325792bde45f4e926ec9a04d90329b4ca6d0ca652d5dabbb32ddddddd9665bb2eeeeeeec00240d5409b0926cdd92e976732e97673265d2decd6f765d997677776673265ee32f71c652fec8b7f77dd77767b8cf8bbcacca4daa994ca12194ca4d26d936c9a6532d91352b136c653284355329942132995cce67339bc8be45f22f9143606532977768542a16ecca6536934ca4d36813606aa1b2652652ad56ab49974bbbb2eccbb32eccbb3339938ca5ddd9978cbc4de32f1ee33e2ef12ad6b1951f6d632a4aeeccb63edad62c652d632d9b49b665269349b644d560086ab632d8994af66659b99cc95e4af7917d3a49329f4ca65329f4ca194ca5996eec9a652693426d964db26dddd994ca6532935195134ca4d32800481aa994994934d932994ca655ece66532ce64cca2f66bd9976ee64d7998caf3319cc994cbdc6532f71c650cbc65e26ddf137f88a65fe229ee33e32f12524924848bbbbbbbb2ec49200090355451b364ba5d9ccba5d9cc9974492bbbb339918fb863ee3862495ddd9ee23e1f126556b58ca8cb6b58b194495ad632d8cb6b58b194bbbbbbb32ddddddab4010d56c4ca6c4ca4bb32eccbb32ecdcce64af257adc65ef22fa749265b58ca65b58b194bbbbbbbbb32d9765ddd800481aad8994d9b25d2ece65d2ece64cba17665d9dddd99cc9952bdc654af71c652dc65ebbbb3dc67c5de32a10a8492576aed24654ad28b99cde45f2284964acaed2410d9399d7917d5996d048924ad1952576aed2bb328426556f6f669b99d5fdfd917bc8be9dddc2432a495da56109957917d3bbbbbbbb8e125dddcca6536994ca6536865328eeef777777765d97776e5c800481aa994994d9b2eeee552af7154abdc71542af157aeeecf71ffff090ca9257695842654e675ffffffffe7849ffff32994da6532994da194ca7fffdddddddd9765dddf9f2001206aa65265366cffff954aa552a954aa552a8552a8552a954ab77764aa553766526dd9949376aeed5d994ca6d32994ca6d0ca652eeeeeeeeeccb65d97777766500090355329329b366edeeedeecd32e976732e97673265d0bb32eceeeecce66efeeefeec8bc6532f7194cbdc719432f197aeeecf719f1778ca8fa6526ddab2555b5632d543a9d4b4acca65b5ad6acca9194994994cae6737917c8a6532994ca65b5ad764dbb1349a12592b194ca65086aa6532994ca10b99cce6737917c8be45f2295550ea4ca6546532936eecad58aadaed762ab626daeeab64ac75
def cur_top_51 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_51 cv_top_51 10 1023 4 15 11 2047 22 4194303
def hint_top_51 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_51 hv_top_51 31 8 10 1023
def fc_top_52 : Nat := 0x697d08d3adb1a753034e5746972b8d32db1a653034c5746970b8d26d1da4d23b4994769308ead518da4533ab546168e692d1c9115aa2db4446068bae0d10dc5a213e34417c56a8aed0cd619e63fb423586798fad00dc1a00be34007c
def ff_top_52 : Nat → Nat × Nat := unpackForestF fc_top_52 12 11
def ci_top_52 : Nat := 0x8008007c27a17a07a07627416a56a06a06a03d73a12e62e02e02832612602412402401c41c0144140086080080080004
def cv_top_52 : Nat := 0xd3cdb34ea60d395d34d36cd329834c574d3fa132fd80cc0e034d95cd2e17353d74cf8dff3b379cc4dcf2eb71c36d6705351d48d2f51b49d2cd1eeab41a2297660a55d2a91e3423f8068df4a1476404fd72937d2611c9683f20c0dc2f817c62dc746566c5cdaf0d359d2299e602558ce8ff19371d1ed2747244d16d8745d70d1918345371d129f34417cbaf5933dc68d0cd6304b40bad5933d468d08d6303b40a1e9363323dccb5f341370d025f34007c
def hi_top_52 : Nat := 0xc9c0081392f0102724c0204e4540c11c8600813903010271f40204e3a40c11c4e0789b8720e0ab0661a1fdfd0343fac7434cd4ae3a3825dccee0467d0d4f7efb1380cdfa7c016fcc8b0ac7060624c72831c7e5666a4ce2ccba0f6aba971d7030583690c114658141e88b51cff0dd0e0e614d1c1b41c838348000e4e4
def hv_top_52 : Nat := 0x155aad56caab55aad56caab6465b5644dbb5daab3eb2096288582cbd733cd1a6f379d87e45fe445efefe24a5632dac8ca8b195194492024ca42c65329b4ca653686532964ad6bbb000481aad8a2048492bd8ece6658ece64cca5929d9e66799a73339932a57b8ca95ee38ca0d2eb7f117f88bdc7b8cfb88acac92049002b5996d5ac9b7600804841cce67339bc8be45f22fa74b59004d885ad60da592b5ad7626daed6096b14409b049369271d2c94ecf3359e6636ccdb33399392a0d2eb7f116dfc9d4af1b78f719f25788654ac8cb6b5936c9a16b2149a85491949a6d269349a0008b58020134994b99cce6752f917c8be45f2284465b58b196d6000b580000ca00040ca653299402c958ca6532994cb332cc02c94ccb332cd7b35ecccbc65e001a5c65e32f1978cbd3e32f044654ad64ac65b5800406528d8cb6b2491248200cb66532996cca0164ad6b32996ec6500020163294653632932926532994932932932bccc65799802c94ecf33195e665ecd7b3339932ff114cbfc45001a5d6fe22997f88a65e32f1ee33e32f084ac01001249001b4b5ad64652900400201949b4a492400652d3b4cdb336ccce65248007c3e1f0f8f711f0f80b36dac05ad6b244249a65ee2249232a32dd936c9a4d2681665490a4d42dad632934ca4d26934009a6510090040249a4ca5cce6733a97c8be45eef22f91400480000ea01020924248ca00653a9d4ca65329f4ca653e8024919667599966659802492f66bd98f87c3e228f88a009243e1f0f87ceeeeeeee00107049249200777732d994fa65b329f401249cb90002008a2652652eeee3fe228ff88a009243e1f1ee29196c492924912202009249248ca80400ad249196cca7d32d994fa0065124923292914480010046529132932949d24e91a6657998caf33001944925ecd7b333995e92f4451ff1147fc45004921f0f8f711f0f89b7685aaab4fa6db48ca9196eeaa91350b64d489aad09024b5692b49232a569249232ddda56aed24ac210855b99edccebc8bf7e45f412249136ec9a90424db733df917eddddc2449232ddda410996fc8bf7fffe12249196eed2084cb6e67b465561224924aed25665bbb491942132da74e8d3733daf5e88bde45fb
def cur_top_52 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_52 cv_top_52 12 4095 5 31 11 2047 22 4194303
def hint_top_52 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_52 hv_top_52 31 8 10 1023
def fc_top_53 : Nat := 0x6beaf8d7cd255aa35b5c37c6b86e2d70dc1ae0be35c07c56a8ced511b5ad0aa35a0546ae6bed624d1ac41a35735b6ae6aed5cd4daa2363543616aa2b8d54171aa5a3b54360693ae8d4d5f1a9742349b4b693692d415c1a823e350370
def ff_top_53 : Nat → Nat × Nat := unpackForestF fc_top_53 12 11
def ci_top_53 : Nat := 0xe4336cc312bcae1b464988a208820280200789e0781a46098060162544f63c0e1308932407214805
def cv_top_53 : Nat := 0x35fd7ca2119348c5ecc8dc75f349d1c91356570d051f354460d04db740a5dd009766157cd4f1835e37cd76dc75d370cfedb744a7cd725f35c07cd4cd2750b45d6a5535a054d644d358834d66d7f5835bd5ed5f57353d4115b51356d565735505cd52d1f5b46dd5b1b356361d50d8352b4bd3ed1f5357cd4ba1330c80cfb1fb3f37e5cc5174f14cd341334e95cd3217351570d431f350370d385734c05c
def hi_top_53 : Nat := 0xae924b652f689b722ecccc03e2965ec6dd343a0c236565d486caf01f464a723a68f90874401024e7602049c80101b38b8081270e01024db810191b28081235c010245a03d4609d63e5a9388040926c808124c20405c750808d08e9696e1188081220e0508c3801c27016d01650250182202c0507803406090000141a
def hv_top_53 : Nat := 0x24ca8fb6465b5ac9a4d26996cda4d26996d6bbb491949a6d269349a134ca592b5ac010d549a652693295ecccb3733a952bc95ef22f914928ca92b196d62c849232994cb632994da6532994da650ca652c95ad66532dd8ca001206ab628994ca6532932932af673329967326652c94ecf33195e665ecd7b3339932a57b8ca95ee38ca0d2eb7f114cbfc4532f1978f719f197aeeeeeeeecb0929249249242459b2001206aa8a377765d2ece65d2ece64cba24919ccdddd8c7dc31f71c31248f711f0f89492465465b269349a65b329349a4d09a65124aeeec4db1949a65269349a134ca24924010d549a4ca49a4ca57b332cc9b35ecdccea51f0f87c3ef22f914929249248ca848329349a65329349a134ca249000481aaa289349949957b39994cb39933289244d9af66673231f70c7dc70c4921f0f8f711f0f9ddddddddc7092eeee924924243bbb994ca7d32994ca7d0ca651249cb900090355451329329777718fb863ee3862490f87c7b8fffffffff9e127fffd24924848ffff32994fa6532994fa194ca24979f2001206aa8a2652653fffe552a954aa552a954aa154aa249154aa552a92a954a465b246524a4924924654242569249194ca7d32994ca7d0ca651249232800481aaa28994994a4e92748d332af6733299673266512497b35eccce652f497a445e18fb863ee3862490f87c7b88f87cac90504d26dacac10d5428da6bd98f87d55aad56ab3eaad56aa1d6aa5bb3eaad56ab5541d40ca651132902501aa994994af66bd993328bd9af6667323e1f1c307c3e3dc47c3e09a652c4db134ca4d4821aa934994934ca4d9af663e1f556ab6aacf82809a652c4db01280d54289349949332969af664d9af66673270c1f0f87c3e3dc47c3e48ca9050924920ca652d648ca04a03550a265265292491332969af66bd9af66673292491c307c3e1f0f8f711f0faaa4db226d56c8db6b58da65b4ad75525595acda4db269349b6b134da4d26936eed241350a592b5ac010d549a55a56b35acc9ae6752a5792bde45f22ab555136ab3eaacf95aab3e
def cur_top_53 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_53 cv_top_53 10 1023 4 15 11 2047 22 4194303
def hint_top_53 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_53 hv_top_53 31 8 10 1023
def fc_top_54 : Nat := 0x6df6ecdba919b7522361c536da6b2db4d05b2a37b6c3586d48fadad5f1b522cb6a3426ca6deda4dc9b29a7b675726cf6f8d9cd39b29a5b6595c6cb0b8d94d1db0d33363d666c76d6d86979b12b5b624666c349c00296db05acab546f
def ff_top_54 : Nat → Nat × Nat := unpackForestF fc_top_54 12 11
def ci_top_54 : Nat := 0x9e73c243c628a308e103e47c0f09d8b83700d4da8350682c4d883105a896128250446881101f32964100f801
def cv_top_54 : Nat := 0xbd91eb70476dbeddb74477dc6d1b70b44c2c9db6f246dba912b2a3edb11f367b7cbd51f36bb7ddb6d676d341d9f5936b468db0d62f5340dad5f367c7cbd51f36bc7ddab1676a342c8f1fb6745eda4dcb67b7cda15cb3f37ed9cd3b31d72cbd5c36615cd961736cc6fd2318f69b6fc60d8f68b4fd9ad2f65347c2cd0f6456694719b63b6bd8b5af624667a0d9b8256bdff59f7e46bdef19f7ac5fde116f75c57db914f64a66d8c97b61a4ed0d1fb4247cbaedfaeb37cd235fb5fc78d0adff41b7dcdadd733b73d82d6705b41a2493634a3f80a8dec997db125d59093f5d04df56c54
def hi_top_54 : Nat := 0xd1d999818a46e65eccb3b1fd8c42434afd0406f5233835ea46000054481411a89000014e7090ae958101dcf18e0e69d9820272ac3f41e5360808ca6c000092b8688915c3f3ee204322d42c064527dd211ece565e591a62be92b079051354ab431296c414a503cbea71991a1ba297ada6a3b8455dc33d1d0d0001619e
def hv_top_54 : Nat := 0x5a57550b24a24962ed2249242124b99cd39ce7e45f22f77716404db2d2208d32a34ca1764924a4492484921249249204909cc9a539ddce6f334de662493b8e4bbaefbbf88bdfc45249eeee2c809b65da495d542c653285dda480d54902492492492492493624a2493493649b1b1249249204e64d29ceee73799a6f33124924c5c93b8e4bbaefbbf88bdfc4524924914f93dddc4d26dd842855b63ea3e994ca234865560032a32a490247d329f55a40100204ce739b99d77777917d5a4aed6560ea16e934da8da653288d2196c9a006d329b52b32d996eeec2eec02004099ce73733df7777917eecfb611595acfb77665b3eddd805dddddd9355d555a40100925cce6733df917c8be45fb48da2b593558cb60ca146912492b5936c9aaeaa9236a48ca8da920049004024973399ccebc8be45f22fa23bbba495ddd8040f22f9149fffe92577760101cce62248ca8ca9240092495dddab495d54020124b99cc9d3a34fc8be455ebd11782232d8caac0166526996c9a000004009249266f334de66009ce739ce73249efe22f7f11403bbbbbbb8927bbb8425602c00249005ad6b04924008012124a49240139ce739ce649292401dddddddc493dddc00048165936ec5d92b5ad6b1349b6569d6d6b0120424925cce67339bc8be9df22f914b59016b580921b4b256b5d89b6bb582424924921204924e64d29cde669bccd39ce6492771c9777f117bf93bdddc493dddc02040164db2680592b589b6269349a6526a16c4db124924920473399ccea5f22f917c8be452cbbbb00bb26804d0009a4d2693424920042490092eeec02739ce739cc926eeeeec03bbbbbbb8927bbb83e81349b65936c9a04d2693409b626a26a26d8921212492492490902732739ce77739bccd379a94924ee3bbbbaefbbf88bdfc45249eeee000355240924924924944924d920139939ce739ce64924931724ee3bbbbbbb892492453e4f7771292564db269349a91349a4d26dddd89b609a1350a4d428924900435526934926ab55a56b35acdccea51f0fbc8be4524a56025104654924908ca9092329f4ca7d0ca65124ad24924001206aa04a0945224af67332ce64cca27464e92494e6673231f70c7dc70c5e88abd24921f0f8f711f0f8283a9d4ea919432994492b194fa65b1f409406aa144ca653299499493328925699966bd9af66673270c4921f0f87c3e3dc47c3e
def cur_top_54 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_54 cv_top_54 11 2047 4 15 11 2047 22 4194303
def hint_top_54 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_54 hv_top_54 31 8 10 1023
def fc_top_55 : Nat := 0x6c3acedfb1b9bf5a2361c6b6fb4a8df15c5be1be37c07c6c38cedec951b0e2fb79b446f3488de3179bc522361c5b6eccf0dd89b1bb0b637606c6c38aedd2e31ba53a36ec776e46ecdcc991b913b37224e6dd68cdc48f9b75a236fc76
def ff_top_55 : Nat → Nat × Nat := unpackForestF fc_top_55 12 11
def ci_top_55 : Nat := 0x9c4e247208cc6230f57836db0d861b0156a8542853275381a48a391c0c4601b0c0280200
def cv_top_55 : Nat := 0x37f46edfad1363a6edf69537d571df2df1e827cd889337c07cde55bb68a76dec9537a344d9c9db79a44de517b66a76de291366166d9659b77e78d949db7726cdda5b37606cdcc8d37538cdced1370284dd29d36fa44dcc99373264dceddb72a76dc8939f5266dc48fb67b7c
def hi_top_55 : Nat := 0xee91f9d9c7b5d55f417533866807c6bc54241f17545f552c16cca4cf86a62a92fb630503e9d88600e1c1bbe8468667571f9e6d2c6c60963b3b07a75d854642f372f27176551cb94caa68e9a9e241c204044358090b06501a180c4418171798303c2c9090a85520c100818aca30cd8a0d60525a52404a121680002425
def hv_top_55 : Nat := 0x2d626d8100109243628d8d893627d24934d907339899cf917d3a48be40ca0005964db26800582b55aad5684009249269092ad20139ce73bb9ce73992480777775df7777124f77701940002c2c9b64d0b569352b5134ca000040924924924924ab492049251249a49a49b3649269269249b364920004e739ceee73799a6f33124924c5c900eeeeebbeefe22f7f11492492453e4f7770005924936ad12407339bc8be45000bbb2ec4001092490d89289363624d8926cd909cdcce62673e45f4e922f910a0002150a8542800402c0bbbb2852049b492424d99ce73009ce73bbbb24c49eeee00eeeebbbb249eeee00ffff003c002eeec92400204924927c93e48126d24a24d926c903fffc00aa552a956eeec9249262e4965abbb560000160177766c924924800409249249364924d9b249024da49449b249b364816f776f66009ce73bbbb2492498b9377f777f7645e00eeeebbbb24924914f93dddc5901767d3e85ac492497614ac9252242424924092124939934a73799a6f335ddd9249dc725ddfc45efe22dddd924f77716405dd9942ecbb12baaa57692035524092492492492493624a24d9b249364924d926c9009cc9a53b7b35bdddddd924924c5c93b8e4bafec8b7f77777649249229f27bbb811a51b28d25cf963288924924908e6737917c8b652458ca2b243552124d8928a366cd8d89362490733a9499cf917d3a48be44809b622902475368124a44936c492484849249248124273124a77739bccd37998924ee124baefbbf88bdfc45249eeee12026d895d55248124650492406aa481249249249249251251249a49b24a28924a2492013989253bb9a7464e9124924c5c93b8492ebbe5e88abd224924914f93dddc24922acbb2492492ad355249249289249451249b202494e739dddd924924a4977775ddd924924f77701d4ca900909124925d9764924a4501204909024924927326f334de66492bbbb2493b8efe22f7f11524aeeec927bbb87704877772ec777748a035524092492492492e49724a24a24d926c900ee1dddd24aeeec92492453e49fe091fffe5d9fffe91406aa48124924924927c93e49449449b24d9200552a9fffe9257776492493172411952408121245d895a492575503552409249249249249289249451249449449b24d920139893a49d234d24aeeec9249262e49dc25e92f488bc925777649249229f27bbb8aa85828d3626d54b589aa96086c4d89aa81626c4daa8589b550b58355b13493695d540b1769124d89349b1b12499ce732fdddc7d1a8db5ac85b124d3a93490bbff96404db2d2208d468592512493624924d249249cc9a539ddce739cc925c9dc725dd77ddddc493e7bbb95daaab9bc8b550858469
def cur_top_55 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_55 cv_top_55 9 511 3 7 11 2047 22 4194303
def hint_top_55 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_55 hv_top_55 31 8 10 1023
def fc_top_56 : Nat := 0x708696e355a1c692eb8d25c71a2b8e34171c21a3b8c67e7096eae12dd1c25b2b84b64711910e22e11c45ba384a3770946ae1ae11c35ba38493770a708e14dd1c241bb843430014bee0b165c15aa361d6b703488e011c5c01be38017c
def ff_top_56 : Nat → Nat × Nat := unpackForestF fc_top_56 12 11
def ci_top_56 : Nat := 0x8c08c08c08a18817c67c07257206856806806616605c55a15a05a05625605605223ac1341201200c30c00a10a00a0005
def cv_top_56 : Nat := 0xd9855765955e3d5a365265e3a9778e25ce365738d05ce319fb74a65e248d787135e160d6f327ddc09d788a35e1a4d785035dcc99389c88dc11d389384e22dd372a747d499387384e1add385b84e14dd2b2e7ee2edd78b374e2ad978a364c2c99635a3de208df87a35e184df848370c605f93c59e4cd6791b4fe3ed2f8cb47e10d0f64a55a2693e61a478d48fe03a376d253da21476444fd751373aa13cca84725c0fc840370c205f83459e0ad5362a4ee0691381471e02df251a7cd909738017c
def hi_top_56 : Nat := 0xd51372dd98c5145b0d2c291dd1d9522b0fb2a51435a67aa8300c0ece20a49090f2e2d5173312adfa8dccfbec420237cc83030f7409095e8e1a16b8f51d0a71282030e0807075b8e1e20b6cc10146c903842d4f0f10d6b330fb29bd48ea4bb9f9f08345d50cbdb532396147c68240a42083375f52840ecc980002a607
def hv_top_56 : Nat := 0x480001215d80001011455a6525226cd9004922ebccc5d799aeeecce64012487fc451ff116eeecf711f0f80003a9d4003a994480121124bb2c921200145146cd90ce399cc6732117cf22f914f7100000eb55000120000108a40001659bb48400005d99766925777600003e1f2495ddd8f87c00000e380000840eeee0005960eeee9080d54001cb9451b364000229e0eeee92577767b88000079e00002107fff80016587fffa420355000f3e5146cd90000c387fffa495ddd92a95480000000081200000108124000596095a4925755035500048948a25146cd90000c3824e92748d3492bbbb339900008a7825e92f488bc92577767b88f87d552c4d02c134b4aeaa005ac01769125891ed399f6ee0ca16016004004d02d20ca49949032d8a24d364cb332cc01cb2532eddccce64cbc65e00f0697136ef8f719f197800b0105a57550002ed2242c4b99cd69cfc8be45b77000005d80000240001690653292653292001628934d932bccc65799802c94cbb773339932ff114cbfc45001a5c4dbbe3dc67c65eaa86525895525835508194b1aa8580b04d8816404db011a650000b58469940b24a2484806c49a6c4338e67319845f3c8be453c5d368e5d0c0e62e86d702c1a667798daa78c22879146357c0b045e22fff0000161000004d2c2ed24aeaa000000016b0005dda480d54002c51269b362490000c385929976ee767999e66339900008a780d2e26ddf5bf88bfc453dc67dc00000200000b003550002490000c384e73999cc8000453c3bbb8f719f705ac0008b580212486c51269b24d24d249349b4920e67529339f22f914917c802000100400ca0592b194ca653281362124ca492402694e739ce739cc9240392eeeeeeeee249eeee001002000ca0592b5acca65bb19400204924924924ca49249026c6c4945126c6c49251449249364800134a73799a6f334e739924924c5c900e4bbbf88bdfc45eeee24924914f93dddc000924892492480e6737917c8a8048010090042492428a24d24d9249a49a49269248399d4a4ce7bbc8be45245f21d4000080200ea753a9d4012489d481092893e924ce739802494e739924f777002497777124524f777000e000eeee0092449200102492492e49724094494493e926c901dddc0124bbbb892492453e488000400ad2490024914492492400204924924944924a289240944928a249f493648093a49d234c0124a739cc9249262e4af497a228024977771249248a7c9eeee
def cur_top_56 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_56 cv_top_56 12 4095 5 31 11 2047 22 4194303
def hint_top_56 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_56 hv_top_56 31 8 10 1023
def fc_top_57 : Nat := 0x73f068e68d8dcee3d39dc7673b6ece684fdcd09bb9b47a7368ece6cdd9cd01fb9a03772946ae649f5cbdbb39847a72f46ae524ddcb53eb9537672b8f4e548d5ca41b800b437088b2e10d65c923239224570869ee40d91c81a7390235
def ff_top_57 : Nat → Nat × Nat := unpackForestF fc_top_57 12 11
def ci_top_57 : Nat := 0xb67b60b60b60ae4ae0ae0ae0ae0a64a607977807047006a36246205a45a05434c41f71831231201200a40a0081080004
def cv_top_57 : Nat := 0xe831d2d1274de88e3a01344f64b79f8341a20b79ec7ae791db9db76b429db9c47ae6f1db9b376b409dba536fe90dafa3b6ae86d9eec366e7cd8f87a6fdc29aad4267b3e999dc96f72459f9d13fe724dd3d12d4864951406f3f819f9a83fe680dc6802d13209433817e649f6cea75e1c9b6ce265e611eacec76b369db98b76e189fecd277e5e8d796a7db309d785a6db2e99795c7ab311dacb276e58ddb84a7fb2a9df95235ef6dbfbc36aed8d9fb5366e109bf6e26bb2899ead2638de8f7b0a3be988df99a357705bdc8967e5c4dd3c12f48449d1386f3f619f9483719c0bc4c0270ca05e62a5598c9163723fa2a97e042458148d792c64e4317b68a65e4891767265e44d9390b4ed9a99790235
def hi_top_57 : Nat := 0x8add31468a4c202489b41c2688a4344483990d437e90fd427de4202b7d381c2b7c24344577550d347254fd406c1569906bb01819652559a364ac181e5ed1517752f276f85284181b4c89597f4c041821467951633ac276ee345d3d992e0da1942699a1dd207db1871ca114f714e671ef0ef9b17b0b4904ec076514f9000271d9
def hv_top_57 : Nat := 0x236cab2364d0b160842684d08446865011b6b1349b6b012d618b362cc0d31c46b979cbc045e3c468650d3733da7eb98abc1a7332b151a5de6eec562d95346e6385d25cba4b99cd3b4cbb3b4dddccdc979cde6eeeeeef37772af157bc8bee552a955c46b8e9ededd3151a8d62d95346e6e634d1b699766f336da73779bbbbbbcde6efefe452af1578aa550ca117bc8bf69ea559f91422f7195ca8d3ffdfee572d95c8df1e0c9f193e45f22f0f89bd6efff3de4954aa552af99ff8abfddfdfffffffdfffde237cf5f7f7e9ca8d46b96cae46fbc8a45e468f89bdfcd5b73ff98aa552a9578abdffdffffffdfdfeacad64db26da560bb251b5a44d926a26d628d89a4d3649b6b5a73b2532eddcde667998ce67b8697136efbf88bfc453dc67dc4de6e6b58b576b0ad174bb69597403399ddcbae5d0dae6d71c74f6f6e8936972eeeee5d733975dddcbae5d772ebf917c8a552afbf914aaefd2f373241655a36836b8e9ededd124ce67779bce769976769bccda5dc99bbcde6eeeef3733bbcdddfc8be45f7f22954aa5575656b2ed976ed24acbae39b5ddc7774eef6eef6eeeacc5b5ad6b5dda49dcc69cec94cbb773736b977736b4e769cddcbaeeeeeeee5d777772ebbbbbbbbbb975cbaee5d7772a8caa31a432add8dfdddfdc8a552a8c6552a8c65519546e5577773bfbc8b6b16ac6315a26936d2b18045f22fff8fc6357dabe79ebefefd12d53e5cce62a955ffcdffffe3f22f8ffffc7e3ff1f8fdea7fbc8b761655a3686af9ebefefd1248be45fffefee1f137addfcd53fe4b99ccffe6e2af7ff7f7fffff7917fffbfffbd0d0ec9b64dbb492b1f9ed5fff3ffd7ffdfffdfffab396d6b5ad77692ff22917b8697136efbdabe7ffcdaddd6ee2a954aa551a432add957dfffffcc552a954aa552a954abc552af7f8ffffffffc7ffffe3ffffffffff1f8ffc7ffffe3fff5656b26d936ed24aeaa5ac5dda4ac9589b764db1b12e976c9174bb765db3974ce5d3174ba318d21936ec76f1917c64518cba318000000000164ad6bb136d76b005ac51b589b124da402c94ecf3359e6636ccdb33399001a5d6fe22dbf93a95e36f1ee33e4af000005936c9a00004db135135136c00013e926934d9269349269200b599f665dbb9935e6626bcd4a673200d5e3ef136ef89bfc4526ff114f719f2d7800002d6000000480004aeec93e9f4900b146cd92ebccc5d799800ba94eeeecce64fbfc453eff114006975ddd9ee33e2ef016402150a0001761f4fa058925d84a21201b1b26c338e6734c845f3c8be4500000b0800000002ec2c02ec000b2c12baaa576920355000b146ec9b26cd90000c3817529dbd9adeeeeeecce64000229e034bafec8b7f7777767b8cf8bbc00000090000136c0000849224da6d24011449a6c9b5e6636bccc009245dbb999cc8ff88a3fe22802490eef8f711f0f80482ecb1240058ca005ac58ca02b00d540b14690ce399d4a117cf22fa7404809b601d4ea0000907536804a362484804a26944338e673045f3c8be45e200000840000134b04aeaa924000000090200492406aa0008a24d3652251200018704922eddcd3a32748ce64000229e09243bbe5e88abd23dc47c3e
def cur_top_57 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_57 cv_top_57 12 4095 5 31 11 2047 22 4194303
def hint_top_57 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_57 hv_top_57 32 8 10 1023
def fc_top_58 : Nat := 0x74d8feebd631d363dba6c7a75b518e9b1ddd623e3ac37c757b08e9b1cdd55bc3a6b7e74e6e4e9cdc5d39b4ba736174e4fce9c9c9d35bb394a3774b4c8e68dbdd263e39a36b7346d4e889f1d10be3a207c7346cee84db1cfe3a39f934
def ff_top_58 : Nat → Nat × Nat := unpackForestF fc_top_58 12 11
def ci_top_58 : Nat := 0x9c3292144207c8f81f03c26eadc19a321622c4188310620934b7160248444538911202404801802000400000
def cv_top_58 : Nat := 0x3ac374ebd632f6d84ea3212d9a84eab1f370376bdadd779b44e269f6dd275e6051795845bdb1e3abc70b70e33ada8ceb31f3ac37ceaf613a8484bd8d73a9344b64a13aab78de6da2d8274e96992d6264b569d3a9b72ea4dc6b3370ea2da7a8361e9e9fba327ce9c9cb8926ddce9aad7a66b6e996d5264ebf1ffaec7beb91ebad477bb31dbab473ea8dfba6b76e209ff71a7ab6c9ded4a76e5e4d795035e92de3a5a644fe4b46a82de84d93a4c7cb469d37a230e7a5353f12de701346a02dbd914fa0b60e8c9f3a297ce784f53e12de881f39b83d1a40b7a136c
def hi_top_58 : Nat := 0xa27020394120c0f261472844bac181f955068832a80100a52a0609ca080c13914098b51df0e126110a2abc1c8181682d0303103407099fe014223f201c287c10508cde54d6756452761aa8868804d21b9fc9470e174fde78ac17d5a1fa2be8a0f04cb202c881e405e0a190d890f98912613a1e2e4144404c000080a2
def hv_top_58 : Nat := 0x2aa65b5aaa8d2051b6b5ac6d2baa96b196c652ed2b13626924d0093646dad6b1469b162d39b99cd6eef22f916aa554d8abb5550dacb59a578aadad55b5aaa06c49a6c16b1b4d6bc9511b6b1349a236c3bff8582d04d056023400011a234ca059568da011a0488d2d626936d616a19c733996ab512a117cf22f9152a95569600ea06c6aa19411b6aa8589a6546d96a9536aa932865aa926546dac4d5aa56d62d5dac2b44d26da57550092654699432994ca1655a3691a51a4dac4d26dace6732d56ae6732d56be45f22a552be45f22a552aacad64db26dda495d542ec94ad6913764d56b5ad6b5dda489249b58a3626934d926dad6b5ad624d8d96b35acec94cbb7735abcccb5799ad69ced3995ace6b5295e4af0d2e26ddf257f88a95fe22daddd6ee295ee4a99f257811b646dac8d26a349a4d11a01601dffc0b40ac11a00234cb65591b26808db589a4db58338c59b1668d08be3979cbc8d11a236d626936c5551b554688d32a34ca595646c9a8d46d89b134926808d46a351b6b1349b6b5ad62c8d3346cdcce646f237bc8be454696404db2d232994cb6b128dac4d2693649a4d0ca4ca652c51269b36b0196c426652c94cbb77332bccc657998ce64e32834b89b77c65fe22997f88a7b8cf8cbd6b5ac4d269032d8ca8d329951aeffe3bb86532965591b26bba351b6b1349b6b1578abc552a9ffe194ca595646c9bfe8d46dac4d26dac552a954aa552aa351a8d4ad236ed1b76ad1a9001951a6511b65591b26a351a8d46dac4d26dac8d733a34d39a3668d46f917d1a45ee46f2351a8d46a351a5ac4d26a351b5546a351b5546a351a8d46a340046a36d62693411a8d0aaa351a8d0aaa3402cab2364d77770b589a4db59dcabc55e2a95402cab2364dffff0b589a4db5bfcaa552a954aa55
def cur_top_58 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_58 cv_top_58 11 2047 4 15 11 2047 22 4194303
def hint_top_58 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_58 hv_top_58 31 8 10 1023
def fc_top_59 : Nat := 0x168eefb5b9df6373be2657296deef2d99de51ab94b6a76d4feeda9f5dd1c63ba27476d4f6ee5a31db53bbb7b7c76f4f8edce11db539b94b6776b4dae52d99da52f3b43647628fcec75f9d8e3f3b256e7636d8ec49d9ca51dbb0274
def ff_top_59 : Nat → Nat × Nat := unpackForestF fc_top_59 12 11
def ci_top_59 : Nat := 0xb636868ccc5981302514647d0f45e8394720d51a8350664b950ea012f25c0b0924222404800f110e11020004
def cv_top_59 : Nat := 0xbd51b2f546cd9d9dbbf56eefb1bafb36ebacdb370365ed08e3b0236e968d3bd364b9e9d7be265ece8e7aa235ef4d9bbca35eeaa22f3a84b8e993a7a34bce9db70275dd49aae6266eb68dba3234e644d796835ede9d3bab8cdc0a13ba274dbe913b968cb9ce32f3a7cedc9c3b837cede9f3b7384b8cdd3a7344bcca33a9a44eee9ffbb27dee69efb8a77bb29d7b6a73e2e9b77426bb9699ee2a65e9a8d798935e580d6f3343ed69b6ec265e2c976e2255776575ca155454174ff0550d205fb4a5eb7edd3b4364ec69d2eb264bd51f2f547cec95bbb357eecb1fafbb7ebacdf370375ec6db367275ecf1faddb76ec49d9f7244ebd22370474e22dd3b0274
def hi_top_59 : Nat := 0xca003051918060a2fdc809555ea72749b138c31124718f9e6ab6f7bbe8303b6f91ca10dd604071b621012b66414186be0303ad360d119a660201b4800c1368681826caf13179363297f1ef9a1f32c63446458a01008aa61a1b915544fe21683050405060a080402018f2c343714c2126603e9d968030101300001418
def hv_top_59 : Nat := 0xb13558ca8d26d958ca8d012b2b5ad764db269349b695d5402d6b591a6524dda4016b14697339ad362cfc8be45b7397800b000588009a0008b0bb492baa85ac00016bbb490000102c9589b764db5ad6b58016a0061c2c9174bb765db58ba5db314ba5d5a9756a5d004a80114f01a4326dd8ed618ece518d2a34a8cba34a8cb01760016001200026816906532994994ca65200652c9589b764d32b974c6572e9800ca5922e976ecba652e994ba95f19152be322802541a4326dd8d2a34a8cba34a8cb2026d969580ca65329942d6251b589a4d26c9349a132994ca5ac51b1349a6c936d6b1332964a65dbb9995e6632bccc4cb39af49c950697136ef92bfc454aff114a57b92a67c95e2c809b65a56b5ad6b589b60ca652c9589b764db5ac6d62174ca5922e976ecbb672e9ace5d52994babd2e834a834864dbb1dbc645b78d3a951a5465d1a5466c5540996d6b196c582c582684db4aeaa0124cb632dad62c652ed2b589951a5cce6b4e7e45f22dbbaab6b234b136aa583552d635502d552aed554b596a5d4a8cd56d6aadad552d624b58269609756a34adad60bb4ad65ac8b025764d41349b6136ed24aeaa0016b5ac16b5dda4890b25626dd936d6b196d6b2d5cba65ab974c2d4bab55a9648ba5dbb2edac5d2ed8ba5d5a9756a5d4af8c8a95f19144a8d2a950690c9b763b5863b0c6951a5465d1a5476b0196c016b22d62c8026936c2693426d969194ca650994ca652c51269b2657998caf331332964a65dbb999cc997f88a65fe229c650697136ef8f719f197ad6b05da2d65ac8b025613504d26d84db4ac653293299486532964ac4dbb26af5cba632b974c174ca5922e976ecba652eaf4ba65f1914cbe3228332834864dbb199466519746302d6269340bbff8582d04d0560040909624d2001000908165146c924c338664ce4e08be1e245f3626ab194ca4db2b194ca4b589a4d023bff929595ad6bb26d9349a4db4aeab6b5ac6532805ac65b194bb482492497339a739cfc8be45eeee5656b26d936ed24aeab6b5ac65b5aeed244924d8924934924d8d89249212486c92892893649b124ce739cd29ceee739ce739ce6493324931727bbbb92eebbeeeeeeeee249e249229f27bbbac4daa8589aa86d6
def cur_top_59 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_59 cv_top_59 11 2047 4 15 11 2047 22 4194303
def hint_top_59 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_59 hv_top_59 31 8 10 1023
def fc_top_60 : Nat := 0x79827ef3b189e75b53cc13779b6dcf300fde66313cc03779746a002d4de5536bc94667938d4f24914005a7bc826d78c6ccf18d39e35b53c6235001696f14915e02b53c2d6b785accf0c911e16b1bc025d7802b8f00541e002e3c0050
def ff_top_60 : Nat → Nat × Nat := unpackForestF fc_top_60 12 11
def ci_top_60 : Nat := 0xf20f20ee2ee0ec1ec0ea1c1597596092292086670b7006c26066005463eb3e03643603603603412481c41c014414000a
def cv_top_60 : Nat := 0x3cf462f3adabcdb6ef3318bdab5ff64d6fd7357f48d4e8f25f9ea96a69a5799a959b815f69655fcf93ff384dd4292d48c494eb85f33c15fcd03ff300dc6d82d13809436017f6ed7bdb34ea3a97e79a5b99895e55253f2e8d5b795f69455d4192f48a49ceb05f38616cce85729814c6c82f16a0ac4d82711e08c3e01b0d405fcaa6dc44997c9c6ac4519b9226fc3c99d1606f40219fca466f1d17b91a6fdea9af0ea67ace98fc92454561bd000671ae0bc4d027f209b70ba65ef4d9b90a6fde49af0b267aca98df7235f1adab0bb66e409bf0aa6777a5bdcb967f1ed9bc734ee3e9bf7826bc2899eb1a63f188d5de16f72c59d4092f48849f77a69ac498709a4df14917c3244f115af09d6af0f59bc2d63e3a9bf8e26ec2099eb0a62e3657f7695bc1e55eaf953e3457f7615bc1c55eaf153f135ab8ca6fdd69af06a67aba98fc225df06573c1150f02173c0050
def hi_top_60 : Nat := 0xa3c46897474010267d77688cf5a202a99fa425f3218d0ee5238090476379728a128a5b0596b749ea2d3083993add96bf32b9aca95b6a978ad6e42b0ba6054f0703888f96b73d028cae51d4d6d8233c77b6a590e9740a05748e1099bdb91fecb8a23903936c586cacd095ce0d80ee9e1e8161383e0196789600019196
def hv_top_60 : Nat := 0xb2351a734697ebcc8be6d00074ef6f3008ea363a5d3737318268d2ecde6fd07777779bcdcf7f229578abc552a8eddc93a4fa0009518d2a4d37c01ebc9a4f917c8a1c326f000400aa552a957ccffc55feefeffffff3bfffbec349dee191fff78007affbfe004a8c695269bef229143864defe7a83ff98aa552a9578abdffdffffffdfde000005936c9a000164ac4d2693649a4d000249a4d3649a0004e65dbb9bcccf3319cc8077136efbf88bfc453dc67dc00001755b26d934000400004dbb268040002e974bb765d00c38174ba004dbb2680453c0ba5dbb0bb00b5916b1645dd97605d96959f4fa7d0ab55aad2c51bb366cbaf33175e66265d0ba94eeeecce655bfc4556ff114e56834baeeecf719f177aeec2d645ac5ac8b5ab1202eeecb4ad5a7d27d5690ca652c95aeeecbae5d3175cba60ba5d0ba9176eeecba5d2e9755be3229f7c64506650690eeeecca3328cba32e8cb20fa7d3edac4a36b17765da577766ec910a50a852c51bb0bb259b24cba17529975e662ebccd7776673274341a5c85fe22a17f88b77767b8cf8bbcacac7d10a7d4296b128dad7777695dab29124dac51b5ddd9bbb25d997665d4a65d7998baf335ddd99ccf70d2e42ff114fbfc45bbbb3dc67c5de5656b2eeecbbbbbb4aeaa95da4ac95aeecdd9bbbb2e974ba5d2ea45db7b35bdddddd974ba5d2e8c634877f645bfbbbbbb18cba32e8d20481242402401349b61349a136c492369b4da132994ca245144d364caf33195e6626651248bb77333991ff1147fc453862490eef8f711f0f924921201248026dac2693426936c26a49194da4da652194ca249136ec9a6d72e98dae5d305d3289245dbb2e994babd2e8fc6451f8c8a0c62490eec6318c6318c69257776ad2492b16b5ac25692492bbbbb5ac6d625d2e974ba92577765d72e98bae5d52974ba5d2e8c631a495ddd8fc6451f8d3a318c6318c62484136c4923a9b4ea8a49124d2693649a4d0ea4ea7511449a6ca4091099944922eddcceaf331d5e6633993862490eef87fc451ff114f711f0f924ac9b64d49236875369d445248926d89b24d26928a489349a6c9352539a49176ee6757998daf3319cc8f87c9243bbe1ff1147fc453dc47c3e492b26d9352baaa492124849249244dbb26a48a44ba5d4922edd9753a32748ba5d18c634921dd8d7a22af486318c6318c480492480824920bb124aec2eec0ab4d555aad0a28ab55a65b36499744922ebccc5d799aeeecce64e189243fe228ff88b77767b88f87c24909204924177762495d85dd8194ca2491955a55a6537776174ba249175cba62eb974d77765d2e974ba0c62490fc6451f8c8b7776318c6318c61d4ea753a9d44523a9d40492b3777776109d52495a7556dd97665d9b99cc3e1f7917c8a753a99522524448bb26eec976249249112000eb552753a8228d9b25d7998baf33132e8925777667323fe228ff88a70c492bbbb3dc47c3e00ea04001095d974ba31800753aa2901d432a1166ecbb020249075bb2eccbb30ce0f87c117c3a8751249225246eeeeec9bbb29244a491491b37764bb32eccbaf33175e66492bbbb33991f0f87fc451ff11524aeeecf711f0f9dddd249dddeeeeddddd249dddd24aeeec6318ddddd24aeeec6318d24aeeed24a739cd24aeeecc631924aeeecc63186318d24aeeec6318cc631bfffd24bfffeeeeffffd24bfffd24aeeecaa552a957fffd24aeeecaa552a95524aeeed24bbbb924aeeecba5d2e97524aeeefbbb88a452291524aeeec8a45229148a4522915092424924aeeed2b4924aeaa91491492bbbb2e974ba5d49d24e91924aeeecba5d2e9746318d2f497a445492bbbb18c6318c63
def cur_top_60 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_60 cv_top_60 12 4095 5 31 11 2047 22 4194303
def hint_top_60 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_60 hv_top_60 31 7 10 1023
def fc_top_61 : Nat := 0x7bf8c6f749b5ef1a5bde3477ba0d8f74180005abbdc2457976bcf2ed39e61afbd9c6c7b369cf30d6debd363d796c7af0d8f30d5deadaebd604e7ab6b8f4b191e941d3d425c7a78c8f4a0d9e941a3cc3537a08d4f41199e85b43d036e
def ff_top_61 : Nat → Nat × Nat := unpackForestF fc_top_61 12 11
def ci_top_61 : Nat := 0x9eb9e09e08e88e05f85e05645224a44814803c63c03c03c02e72c12c02a12432402402211e21e00c90a10a00a0081004
def cv_top_61 : Nat := 0x7a1597e0c6ff7f18f7ca5ac4e95a91a4fa4493a6d247960908ec84f34811fdeb4bf78d1f7c14bc4c51e9093f9f04ee6c93795a4cfdb56df91187e345bf8515fdf26ddee96f12a57a4093e7ba4b9b091e562438fe8f7dd86cf741810b85b40815cec04f38a12cd184729c10c6f02f16e0ac4f02712208e6aa55f70915a69553421565125f8148d7d9d6ef68da14512d1ba0b7d5b54f691b3d9b4ef46537ce9455124b5241259a99e3d5350f629b3d816cf444f54392df5e1b3d4034f5813bd6b5df56d73d3836f50973d3c649a0593d546499e9914312d48e497d483af4c0dbd28341b80b44e825f431b3d0b68f471abd1466f40dba67266
def hi_top_61 : Nat := 0xafbe4756893a1ae968ec5e23cad0ec851be509e49517f6c0e968d733b5e84af668ed068e52a3ee10160f7c201e3683f3b8d08584c300a220cac8889d21fc649486a0c0a21a800007e834411c7181986e61c1b1b9800006e600001ae8505857a88a00c8404b42e81c1c0a5070a829400000918809c0011523
def hv_top_61 : Nat := 0x3293410a090b642ab06532804d964bb2eeeeeec26509b37764baf33175e66265d0bb32eceeeecccbb325d86ff1150bfc4538ca775ddd9ee33e2ef007fff80083fffffffc10078005a5777777777fffe01636a465b58da6d26d32d8ddddffff8015522a955caa62ab954d7776552a954abfffffffe20000ffff01002b492567800249232a2923fffe008ca92577769395524e918bbfffe009257776552a954abe79fffe07ff9765dddffff85dddffff8552a8552a954ab7776552a954aa0c61765ddd9dc77775ddd85d2e8318c77777dddc1148a1148a4522d97645229148a45229148a4522dddabbb560005d85d56eeeeecddd90bbbbbb7bbb7b305d2e85d2e974bb77765d2e974bb77f777f76450bbbb2e974ba5d0000000240002d2b5a2693522693402d621b5ad6269b20164a67d7998faf33176ee667320034b8fbfc453eff1149b77c7b8cf92bc00000000005a26ab5ad589a95ac016b256b5ac6d624dbb26805ac9176ce5d359cba62edd9763a5d8e97400764876f1916de34e936ec6951a5465d1a5460000585ddd85936c4d44d44db00007d3e996c9b77764d269349349a400ba5d2e976eeecbae5d3175cbaa52e974ba5d006a9f4fad5bbbb26f9348a4df26914cad532b54ba5d2e974011a164db2680246ab236c92269b268247d3e9f49a4d07339a3b38ecd1be45f22a5792bc8d046a03e9f49a4d0aaa3463b210117c0012352489a6c9a00913494ac08d1244d2680040273733a1f0fbc8be86300026934004908d77ff00077774844d364d07741349a03e1f0c6001fffe9089a6c9a1fe8269340aa552a954aa550400902bb491349a0091b649248d269b268246a09a4d04e9d1a7346cd1abd7a22f0f87c31a060091349b55468c634024812349a4d4255546a4318ec34347d91150001648269b26ffff8244d2687f954aa552a954aa001646d9246934d934011a8d26924d4902352469349a0224023b38ecdcce64af257bc8bde454ea6e6709a6d73157ad39a313eb8004763a5d3730074e5d25cce60997660010079cde6eeeeee4dddcabc55ef22fb954aa557
def cur_top_61 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_61 cv_top_61 12 4095 5 31 11 2047 22 4194303
def hint_top_61 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_61 hv_top_61 30 7 10 1023
def fc_top_62 : Nat := 0x7df8aefbc954005afbe5d6b7db2f8f9759df2dafbebd667d748af96d79f5536be5b577d14dcfa20a1f44123e5a3b7cb46ef968d5f2c9bbe583b7cb06e002d6df2522bdd4617c7690f7516df0e303e1b707c32f8f7515defe37be0244
def ff_top_62 : Nat → Nat × Nat := unpackForestF fc_top_62 12 11
def ci_top_62 : Nat := 0xac3483a4012008c1460230118084242020830408204101e88f40684b401a00d001d30e0040c2000c106003001800228100080001
def cv_top_62 : Nat := 0xfc116fefc57a5493e70a473ba13cd6847fc3167ef255a5293e7ea4b9c091e59a433b813ce484b35811ca90431c40bc5d82b14009c4a823fb0d73ed97cfb159b7f26bc5a99feba45faa9b7e9a6e814913e9028fa20937ea6ac5899a9325f9ba95dba15f6a055ced85f35415c38017fb95afed567fb2d7feb35efa8d5fbc352df89af15a67a4a97e7da5b9b895e58a53902936062458f88f7e823bf9e8dfe723573459db995f69e55fe69375184bd249274301ad030673b417ce385b35215ca8053f980efe58371c00bc5c82b13e09c498230fc06c37017f8b59bbd466df49af152679f4967e4a45f8ed23de87cef59c3e2c60f88dc3e197cf781b3e0244
def hi_top_62 : Nat := 0x84bccec5c11f584fded0d76fcf03da192727b5d6935b29de2da1c2faf4c8b1b60c6058cf002ead475fd5e9ce5b4aa19254d5112d4fea692687dd2025151c81b68b973cf8c4f89b0ca3dc0bddceea252927717266a84b791217585079534bee35e17db2150b5d7988e96a670396b537816e1b17506576b4681f93e4c80ae8d9380000f55d
def hv_top_62 : Nat := (Nat.lor 0x4baad964db26ddab6d6249d49a75269349a924009244d569349a4ea4d56ab4b99cc4d9ab67e45f228f87c0ad2012b521241755bb0560921249136eed226d92492489a4d0056ab448a48a491349b76ad269349a4d3a9355a4d2685d5689d24e8c9245dbb2e9349a5d2e9355a5d2ebb4baed2e8318bd25e88a9243bb18c6318c6318c6318c631d8fa595a1259b6cbbb26ddaeed6b244d3adad6b24ac4d3adad602492492499cdcce69ce73f22fa77bbb818c0baadd858ec7776318c6318c6004849249249249249398318c73bb9ce739ce73992484522845229148a45bb229148a45229148a45229249148a45229148a2b4fa05d56ec2c9b64dbbb26ab49a4d269d49a4d002424924924924924ff3fffffffffffffffc9242a9542a954aa552add954aa552a954aa552a954927fffc569f40baadd85936c9b7764d569349a4d3a9349a004956849249a49a49249349349249024d8124a248424d9b024d2492732739ce77739ce739ce732492498b92771ddddd77ddddddddc4924924527c9eeee15a7d02eab76164db2682b6eec15aad3ea3ea56994009bb56d934bbb26ab49a4d26ab49a4d009242ad56ab43293e9269349a4d36ad24d269349a4d269349a492692693568ed99f665dbb9ab5e6656bccc4d26ce64d56ce6673272b46af1f789b77cadfe22ab7f88a4d26f71355bdc7b8cf9dbc194ca04db2c9b64d056ddd82b6c654ad465b013649a04ca124d269b24d269349a4dda4e65dbb9bb5e6656bccc67327194ee26ddf197f88aadfe229ee33ee15a7d02cbb76165db2e83dbb83bba7775e83dbbb97764d569349a4d569349a03b98c4d5a2f667d99749b765d9baf5cbbb9269367326ab6731cbaee3bbbb975ddddcbaeeeeeeeeee5d72ebb975ddc2a9542a954aa552add955fdddfdc8a552a954aa552a954aa552a954aae55777706302eab76163b1ddd8c6318c63180771dddddd77dddddddddc174aa0c631956ecba552a974ba552a974bbdddc1148bead3c8be45f26df9148be4df26ff9148a4522f917c8be45f2285d916c08a322a22a229148a5dff87fff9149148a45e22922988ae45722988a45228ad181755bb0b1d9343effc3ffd7ffb543efffcbbb26ab46318c9a4d03fc8a45395a35787c4d26ddab7bdabe7ffc9349bdc4d56f70552a85518caa55bb2afbfffff98aa552a954aa552a9578aa55e3d5bfe7ffffffff937fffffffffc9be4dffffffff00baadd85936c9b7764d489a00136ec9a4d24d21742e974bb765d26b974ce5d3174ba04dbb26937c8be4d22974ba5ac8ca0194ca653285d9251bbbb2ecb4aeed2bbb413296b128d8dad6b59b24cba17529975e662ebccd77764bb399749c950697257f88a95fe22dddd94af7254cf8bbc5ac80b5ac17765d97695d82565a0b256b5ad636b1bbbb0ba5d0ba8ba8ba5d2eb974c5d72e9aeeecba5d2e9741a541a43b78c8b6f1a76eeed2a34a8cba32e8cb0bb5760045d9340400022eeec02c9589a4d26934da4dbbbb002ea45d2e974ba5d2e974ba5dbbbbbb001a43268c9a3328cca32e8cba32c5695da5776b00082ed2bbbb492bbb58100001601695ddd9b6eeeeeeeccb66eec8058da9196d6369b49b4cb63665bbbbb7bbb7b30017522e975cba62eb974d77765d2e974bb77f777f76451800d21dbc64536f8c8b777665199465d19746212b0160015a480b0040914880194b5ad632daeeed2492462e801742e974ba5dbbbb2e974ba5d4920018318c77776318c6318c65892480405d93402680080bb376400ca2491349a4d269949b7776005d1248ba5d2e974ba5d2e976eeeeeec8a30018924318c6318c6318c6eeeeeeee005838249249003bbb8005802493bbbd996cddd900492b32ddddbbbbddf956eefeec8a300492bbbb18c634aed2492492b105802492492b402004aed2492b000b0049246545246ccb66eec80194465492b32dddda4e92748c5db7bbb7b300174492bbbb2e974ba5d5e92f445bbfbbbfbb228c0062495ddd8c6318c6319f43e88556119442a42a49195241bb2c5768532a429b51450b765d99766e6745d2e8f87de45f485b590b66d3284bb32996cddddd974ba634350a6510a242dac854853699524134ca2150a1bb2cbbb42996cd8a14da85bb2eccbb373398ba5d86f217bc8be45 (Nat.shiftLeft 0x8556485b0005dd9bb26eeec000026cddd9002ebccc5d7998bb32eceeeecce64010bfc4586ff117baeeecf719f177800000401755000bbbbb000081777600018702e974ba5dbbbb2e974ba5d00008a785ddd974ba5d2e8008010000585a56bb269949a4db32ddd89a176b2b6c924ad56b5ddda492b55ab589b6000ca058ca9196d632994994cb624d32dd9949a4d32ab4ab4ca4d201648bb672e98dae5d3176ecba4d72e995ae5d3194ba652e800d21dbc64532f8c8a4dbb1937c64556f8c8a65199465d199460038003bbb80160924eeeeeeee1692492403bbb80249134fb766526934fa7d27d32934bbbb802490eec63f19147e3228c6318800040095da49244d268016092495da49249244db05a47d49249201195149100465492269f6ecca4d269f4fa4fa6526949d24e918ba009245dbb2e935cba63eb974c652e994babd25e88a009243bb18fc6451f8c8a318c6318c6595a8fa05d9f6c2c4d2685d56ec2d135589b764d120bbb489a4d4ad626d9248015aad2c95acad3e93e9f6c49a4dbb569349a4d26ab49aad269342eab4b245db3974c7d72e98bb765d26934ba5d26ab4ba5d76975da5d06ad0690ede3229f7c64526dd8c9a4d18c9aad18daa36a8cba3768c425602c0012489a01602124802d6b58fb626dd935249200b176c5d2edd975da5d76975248006318c776318c6318c632d647d00fa853e9f42d6251b5826d9695ad1349a91349a13296b146d6b589a6eec9376964a67d7998faf33176ee6673272541a5c7dfe229f7f88a4dbbe3dc67c95e2d6405ddac2d6b04db2d1355ad6ac240164ad6b58dac49b764d0baed2c9176ce5d359cba62edd9763a5d8e9741a541a43b78c8b6f1a749b7634a8d2a32e8d2a315a8515a914 12288))
def cur_top_62 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_62 cv_top_62 13 8191 6 63 11 2047 22 4194303
def hint_top_62 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_62 hv_top_62 33 8 10 1023
def fc_top_63 : Nat := 0x7e5696ff8971ff0ae3fe05c7e568eff0d35fe49f3fc34c7f28a8fe44e9fd5263fa4547f226cfe44d1f95a1bf83497e529efdcd45f94a3bf4b5d7e96aafd5171fa5a4bf284f7e66a2fccd35f9423bf22450018a6fc4915f7a2cbefc5b
def ff_top_63 : Nat → Nat × Nat := unpackForestF fc_top_63 12 11
def ci_top_63 : Nat := 0x9e09e09e09078e18e08c18638608608418028006e96e06c16c06a16816806806615e45e05e05a2315075060022020001
def cv_top_63 : Nat := 0x8295e1fdda03ff25c7fd2b8ff8171fac2687402d7f5268ff24f9fe9a6bfc34c7f426cfea931fd22a20d1447f78a8832911fd89d3f99367f22685224b49309287382d0a304afe0d25fb9a8bf53587ea8b8fd8d75fadaabf4b4941846cfced45f99a6c0134f7ff696ff6d1dfc5a1a41a3f43947483a8dd05d1b3f794f7ed28e6484fcbd49b94812d24b24afd013df942389b83f11106e1cc0b4288128398178058bd006d25f9122a4123f43747682c8dcf711999193f3102765e84dca849994712f25f25649449c8e49189b03f11006e1c80bc2841384201f07102e9c4955f8922a65b70
def hi_top_63 : Nat := 0x91c1623c6c9121a2448920ff08d327f08307bf840001f34348ef26307477e8714bbf40001dfa0000ee50a1872c2246b4ce04959fc206abcc91325be8d27a96a048d4721c42a0e0e2b5070000278040b9199162887f1a4d43b01049db1dc28c497a90537a2ed1d8ebc307c35f041d4de0c00074ea
def hv_top_63 : Nat := 0x5ac0005dd88d77ff000b1567777bb2c2d6770b0abc55e2a954002c55bfffeecb0b5bfc2c2a954aa552a95402c02d5a56bb0058ab5a349b7777768db0b5ad1a165bdbd9a65d997665d2edfdfd917b91bc8db0ba016b5d974ba5daaa342cbbb0b5ad1b65d974ba5dbbaaa349a5db2ed8e4db35800162ad64db1dddc2d60bb772af1578aa55000b156b469349a8db00b136bbb46a342d6046dda34b24016b35acdcd373457a2bde45f229749b39da94ab4002c54c02c4b99cc5d5a9756af6e16980040265d9bcddddddde64dddcabc55ef22fb954aa55726976d4b39974975e6ee000e9e60162a6e635bb9756a5d5a85a6f37e84cbaf37777779bce6ee7bf914abc55e2a957efbec8be59aa559f9149bdd6452adf000195c00327c8be458ac57efc07c00100e2a954aa55f33ff157bfbfffffff8efffef26a36c8bdc8d2f533ff354003d7f000caef22916ffe2a8d8a80fbf9ea1c8d7ff3154aa552af157ffffffbfbc0000000b58946d600b256b26d934002d628d802402c94de66799a733399001a5dfc45fe22f71ee33ee00055500002c95802c002c95802000592b0061c000690c0229e0318c6318000000120001695dda57768002d621b5ad6b36400ba94cbaf33175e66bbbb3399001a5c95fe22a57f88b77767b8cf8bbc00000000005da5777695dda00b592b5ad636b1bbbb002ea45d2eb974c5d72e9aeeecba5d2e97400690ede322dbc69dbbbb4a8d2a32e8cba30042a42a42dac009242a142eecdddd801b50addbb2eccbb3733990bd0def22f91401216c0092492152155da4ac2eeca429b402edd398bb32ecfd79147c3e
def cur_top_63 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_63 cv_top_63 12 4095 5 31 11 2047 23 8388607
def hint_top_63 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_63 hv_top_63 29 7 9 511
def fc_top_64 : Nat := 0x81f4aa00317e041a5c0e235810693034976041a3c0b24e81625102c49204125c0824781048b02052e040a3c080470018b701c8d601db0c0536f80b469014d8e01d36c0396c8072c000315df922f4022357e4692fcad3e0022e40034e
def ff_top_64 : Nat → Nat × Nat := unpackForestF fc_top_64 12 11
def ci_top_64 : Nat := 0xf677b03d81dc4ee07607b01d80ec07213901a49d2069034810e68603d19e80f40780b12d490a4022c0f087802c40a30404200004
def cv_top_64 : Nat := 0x41135981f4aa91c8fd1051da13a373e54666524fcc589d9819372a726652e4bc9949592792723f246f8f199c1935b47a6781c46b0349753192a40c24e81725102c491c153534726648b47e84a8dcca09f98093713b07e22c0dc1dc0bbee36b7c66cf03ad2e06da4c0cb47778682e089ada3533a9b25d4e44aaa6293605525c0a24781348a9148fd0fd1da122373e34667525ace84b3c0914b81128e64e4fcc509d9801372a526652a4bc98c9592712723d24641619e0402389d03f11506e1da0bc2941384301f07502ef89199de9b338126b68a4ce87c9260391ac05a344a3acb018dbe029b1b80a5a6894ac9108fd21d1f2112373e246464c4fcbec9bbeda4b7c348ee0052da20a3a4312f43c25684249cf7c91c02d6d80d6c2fb4d6df09abc04a6d6ff4b6d0e95d4d126a42a3f43b4768408dcf7919c0416c8072c075056ce7cab99293f3122765f44dca8c9994992f26125649a49c8ec91a632453d247e83c9160111a97c14511308b00117a005ac3f605d7e60aa1d80b429012bfc3448018b9000d38a489687502d
def hi_top_64 : Nat := 0xd36160fec63e7749bde5b616b5459e28afb51d64a42672e49eb5255c97d1a9b991dda17d88ae8a4c7c868b0a758989bf69ba76f45e3a76e052668ef54e5909034629d60c3e2da5ff3954f93636e86c9b31a4f5512b1591a4283cd0b62450f8fb1fe1511c191999b21285a5a50a39b613064cfcfb04e840590478201c0000e51e
def hv_top_64 : Nat := (Nat.lor 0x32834b89b77c6dfe229b7f88a7b8cf8dbc5901349b65d92b581226a0b092416b582c9589b764d269349a49a4d21756a5922e976ecba4d72e989ae5d52ad4bab52e836e834864dbb1937c64526f8c8b151c5465d1ad462aaa0329d4b256481bb6269250b642dad632dd9b377761632dddac50b632b74ddb99cc5d99767e45f22db8cbc0aaa9005a480124ac4901776269665bb2ed2bb5ddddddddddaec194ca5ac9376d766eecdad642d9bb6b5ddd85d2e85d48bb6f776f662e974ba5d2e974ba5dbbbb2e974ba5d06950690efeeefec8b6b0c766e8c77776951a5465d1974623ea120269b52bb1349b6b42d826994b256bbbb1349b626a16d6b1249249249339ce6e6752f777777917c8a0aaa9024800ba5d0ba9174ba5d2e974ba5d2e97424249249249249243183246318c6318c6318c62493b8e4bbbbbbbbbbbbb8924c6318c6055548124006536964ad6b59bb642dac12124924924924923b8eeeeeeeeeeeeeeee492771c97777777777777124bbbb82aaa409200329b4b256b5acddb216d6092650d8d89249b1b1249249204940421251406c4926c924939934a739ce739ce739ce6492492625c93b8e4bbbbbbbbbbbbb892492453e4f77702aaa4006549000129195584900492194da592b1b6ccadd36d994cb6b59bb66edac132994ca5ad6b146536b5ad6b5ac49b1b1949b49332964a6657998caf335ad39d9bb399b666d999cc9c950697257f88a95fe22daddd632f72578dbc7b8cf92bc5900654900128d80ca652c958cb6dd26b76cca4d0994b58a36b5ac49332964a6657999baf334e6673271941a5c65fe22997f88bdc7b8cfb81555204900174ba17522e974ba5d2e974ba5d2e939939a539ce739ce739ce73986339947b27319ecf677318c673399cce6048c80c24ee0eeee62e9acd6631898c699898c606550690caa5518caa5518caa32a8caa32a8ccee637988a6f318155520074ee00e9ddc4900ee6306d2e85d4acf6eeeee6d2e976c6d2e976d626652d649bb3736b977736b4e766ece66d9976639b5dc77777b3bbbbbbbbbd9eceeeeeeee0caa0d21bfbbbfb914aa5518caa5518caa32a8caa32a8ddddc10d200f5fe01ebffc4901fe45228653683487f7ffffe65b5acddb376d638ca0ec90fbccbe7ffcdaddd632f71978dbc154aa0d21fbfffff98aa552a954aa552a954aa552a9578aa55e3c7fe7ffff8ffffffffffc7e3fffff1ff8fffffc7ffe0aaa9024800b256b5dd82c95ac6c42c95ace67b181834876f1917c64518c6318c4809a4db32892406532994ca0924924912514920994451269349449a49a4d2693499944922eddcd6af332d5e662b59cd6a4e189243bbe1ff1147fc4523ee191f0f84809a4db12492026d89a090212490249136ec9a4d269349a49a4d21756a249176ecba4d72e989ae5d52ad4bab52e83189243b1d8c63f19147e3228c6318c6319f6c9a6d0ea586502908475b3adddddd996d2b3e9f4ea654acd93a97665d9b99ec7c3ef22fd8c67d26934ea8fa65089194ca922925e9d46322914ca1d40a567d26934eb6753e996eecb194408fa7d48ea654912693e9f4eabd99d66e6730f87de45f228c665b01d40094222459d49a75b268653289249209944524495ebccc75799899944929ccce647fc451ff114e189243e1f1e1f118f87ce383bb890eeee0924eeee0924eeee0c62490c6318c631890174ba249139892539ce618c212318c6318c606312486318c6318cc6318c648004815555a492049248a488249249d24e91812497a4bd11418c49218c6318c6318c63001002000124ad7626daed60056492b5ac6d626d369940124acf6359ec6369b4da6d329b57a6d004921f8c8a3f1a746318c6318c6318c0002d2b00005ac9256b01200016289349a424d269349a0164a65dbb9ab5e6656bccc67320034b89b77cadfe22ab7f88a7b8cf8dbc00001764ad60000b5924ad60002c9589a4dbb269349a4d24d26900b245d2e936ecba4d72e989ae5d52ad4bab52e800d219349b76326f8c8a4df19162a38a8cba35a8c002c55802c4dd9351b777777616b0004011a5dd97665d9b99ecba5deef22fd85a342d6056ab4ba5daaa34bbb219c002c5591b768d2693402c95aeed1a16b05dab55aad5acd6b3733991b15e8af7917c8a8d (Nat.shiftLeft 0x555000400016092400010124800030e0924000114f049218c6318c6318c63055548124004d32d9b4bb256b5daed776b5ac091b50584920bbbbb5ac194ca5ac9376d6b59bb66edac4dbb26935ba6d26d3693485d369648bb6b174bb636974ba5dbb2e935cba636b974c6d2e9b4ba0d2a0d21dac31d9ba31936ec64df1914dbe322a54695197466d196404d26d9b4b4ac06d3a9b4da16b2495ad6b13649b60994b149126934d9269349a4d266d2c94cbb77336bccc6d7998ce64e 12288))
def cur_top_64 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_64 cv_top_64 13 8191 6 63 11 2047 23 8388607
def hint_top_64 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_64 hv_top_64 32 8 10 1023
def fc_top_65 : Nat := 0x82346b03ed66081adc10357
def ff_top_65 : Nat → Nat × Nat := unpackForestF fc_top_65 12 11
def ci_top_65 : Nat := 0x4874e1886
def cv_top_65 : Nat := 0x214a4582346a823182085adc1035748f47e8508dcca89f982137
def hi_top_65 : Nat := 0x526d7856c1af8c979bc08b63a79000cf6c
def hv_top_65 : Nat := 0x2490000249249012000008a24d26909349a4d2680249176ee6ad79995af3319cc802490eef87fc451ff114f711f0f8000012492000049249200012489a4dbb269349a4d24d269004922edd9749ae5d3135cbaa55a9756a5d004921dd8c7e3228fc64518c6318c630004913ad9d6cfa4d26805dda491f4fa0091f4eaad3ace6b3733987c3ef22f9140002cfa4d0492569246eeeeeceb6750b3e9f4127b7317665d9fdf9147c3e0000000491489003ad936cea4d4920000114912400eaf334d5e664929ccce64007fc451ff1152487c3e3dc47c3e
def cur_top_65 : Nat → List (Nat × Nat) := unpackCursorV5 ci_top_65 cv_top_65 7 127 3 7 11 2047 23 8388607
def hint_top_65 : Nat → Nat := unpackCompressedHints huffman_top 6 hi_top_65 hv_top_65 27 7 9 511
def fr_top (p : Nat) : Nat × Nat := (Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (ff_top_65 (p - 2080)) (ff_top_64 (p - 2048)) (Nat.blt p 2080))) (ff_top_63 (p - 2016)) (Nat.blt p 2048))) ((Bool.rec (ff_top_62 (p - 1984)) (ff_top_61 (p - 1952)) (Nat.blt p 1984))) (Nat.blt p 2016))) ((Bool.rec ((Bool.rec (ff_top_60 (p - 1920)) (ff_top_59 (p - 1888)) (Nat.blt p 1920))) ((Bool.rec (ff_top_58 (p - 1856)) (ff_top_57 (p - 1824)) (Nat.blt p 1856))) (Nat.blt p 1888))) (Nat.blt p 1952))) ((Bool.rec ((Bool.rec ((Bool.rec (ff_top_56 (p - 1792)) (ff_top_55 (p - 1760)) (Nat.blt p 1792))) ((Bool.rec (ff_top_54 (p - 1728)) (ff_top_53 (p - 1696)) (Nat.blt p 1728))) (Nat.blt p 1760))) ((Bool.rec ((Bool.rec (ff_top_52 (p - 1664)) (ff_top_51 (p - 1632)) (Nat.blt p 1664))) ((Bool.rec (ff_top_50 (p - 1600)) (ff_top_49 (p - 1568)) (Nat.blt p 1600))) (Nat.blt p 1632))) (Nat.blt p 1696))) (Nat.blt p 1824))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (ff_top_48 (p - 1536)) (ff_top_47 (p - 1504)) (Nat.blt p 1536))) ((Bool.rec (ff_top_46 (p - 1472)) (ff_top_45 (p - 1440)) (Nat.blt p 1472))) (Nat.blt p 1504))) ((Bool.rec ((Bool.rec (ff_top_44 (p - 1408)) (ff_top_43 (p - 1376)) (Nat.blt p 1408))) ((Bool.rec (ff_top_42 (p - 1344)) (ff_top_41 (p - 1312)) (Nat.blt p 1344))) (Nat.blt p 1376))) (Nat.blt p 1440))) ((Bool.rec ((Bool.rec ((Bool.rec (ff_top_40 (p - 1280)) (ff_top_39 (p - 1248)) (Nat.blt p 1280))) ((Bool.rec (ff_top_38 (p - 1216)) (ff_top_37 (p - 1184)) (Nat.blt p 1216))) (Nat.blt p 1248))) ((Bool.rec ((Bool.rec (ff_top_36 (p - 1152)) (ff_top_35 (p - 1120)) (Nat.blt p 1152))) ((Bool.rec (ff_top_34 (p - 1088)) (ff_top_33 (p - 1056)) (Nat.blt p 1088))) (Nat.blt p 1120))) (Nat.blt p 1184))) (Nat.blt p 1312))) (Nat.blt p 1568))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (ff_top_32 (p - 1024)) (ff_top_31 (p - 992)) (Nat.blt p 1024))) (ff_top_30 (p - 960)) (Nat.blt p 992))) ((Bool.rec (ff_top_29 (p - 928)) (ff_top_28 (p - 896)) (Nat.blt p 928))) (Nat.blt p 960))) ((Bool.rec ((Bool.rec (ff_top_27 (p - 864)) (ff_top_26 (p - 832)) (Nat.blt p 864))) ((Bool.rec (ff_top_25 (p - 800)) (ff_top_24 (p - 768)) (Nat.blt p 800))) (Nat.blt p 832))) (Nat.blt p 896))) ((Bool.rec ((Bool.rec ((Bool.rec (ff_top_23 (p - 736)) (ff_top_22 (p - 704)) (Nat.blt p 736))) ((Bool.rec (ff_top_21 (p - 672)) (ff_top_20 (p - 640)) (Nat.blt p 672))) (Nat.blt p 704))) ((Bool.rec ((Bool.rec (ff_top_19 (p - 608)) (ff_top_18 (p - 576)) (Nat.blt p 608))) ((Bool.rec (ff_top_17 (p - 544)) (ff_top_16 (p - 512)) (Nat.blt p 544))) (Nat.blt p 576))) (Nat.blt p 640))) (Nat.blt p 768))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (ff_top_15 (p - 480)) (ff_top_14 (p - 448)) (Nat.blt p 480))) ((Bool.rec (ff_top_13 (p - 416)) (ff_top_12 (p - 384)) (Nat.blt p 416))) (Nat.blt p 448))) ((Bool.rec ((Bool.rec (ff_top_11 (p - 352)) (ff_top_10 (p - 320)) (Nat.blt p 352))) ((Bool.rec (ff_top_9 (p - 288)) (ff_top_8 (p - 256)) (Nat.blt p 288))) (Nat.blt p 320))) (Nat.blt p 384))) ((Bool.rec ((Bool.rec ((Bool.rec (ff_top_7 (p - 224)) (ff_top_6 (p - 192)) (Nat.blt p 224))) ((Bool.rec (ff_top_5 (p - 160)) (ff_top_4 (p - 128)) (Nat.blt p 160))) (Nat.blt p 192))) ((Bool.rec ((Bool.rec (ff_top_3 (p - 96)) (ff_top_2 (p - 64)) (Nat.blt p 96))) ((Bool.rec (ff_top_1 (p - 32)) (ff_top_0 (p - 0)) (Nat.blt p 32))) (Nat.blt p 64))) (Nat.blt p 128))) (Nat.blt p 256))) (Nat.blt p 512))) (Nat.blt p 1056))
def cr_top (p : Nat) : List (Nat × Nat) := (Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (cur_top_65 (p - 2080)) (cur_top_64 (p - 2048)) (Nat.blt p 2080))) (cur_top_63 (p - 2016)) (Nat.blt p 2048))) ((Bool.rec (cur_top_62 (p - 1984)) (cur_top_61 (p - 1952)) (Nat.blt p 1984))) (Nat.blt p 2016))) ((Bool.rec ((Bool.rec (cur_top_60 (p - 1920)) (cur_top_59 (p - 1888)) (Nat.blt p 1920))) ((Bool.rec (cur_top_58 (p - 1856)) (cur_top_57 (p - 1824)) (Nat.blt p 1856))) (Nat.blt p 1888))) (Nat.blt p 1952))) ((Bool.rec ((Bool.rec ((Bool.rec (cur_top_56 (p - 1792)) (cur_top_55 (p - 1760)) (Nat.blt p 1792))) ((Bool.rec (cur_top_54 (p - 1728)) (cur_top_53 (p - 1696)) (Nat.blt p 1728))) (Nat.blt p 1760))) ((Bool.rec ((Bool.rec (cur_top_52 (p - 1664)) (cur_top_51 (p - 1632)) (Nat.blt p 1664))) ((Bool.rec (cur_top_50 (p - 1600)) (cur_top_49 (p - 1568)) (Nat.blt p 1600))) (Nat.blt p 1632))) (Nat.blt p 1696))) (Nat.blt p 1824))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (cur_top_48 (p - 1536)) (cur_top_47 (p - 1504)) (Nat.blt p 1536))) ((Bool.rec (cur_top_46 (p - 1472)) (cur_top_45 (p - 1440)) (Nat.blt p 1472))) (Nat.blt p 1504))) ((Bool.rec ((Bool.rec (cur_top_44 (p - 1408)) (cur_top_43 (p - 1376)) (Nat.blt p 1408))) ((Bool.rec (cur_top_42 (p - 1344)) (cur_top_41 (p - 1312)) (Nat.blt p 1344))) (Nat.blt p 1376))) (Nat.blt p 1440))) ((Bool.rec ((Bool.rec ((Bool.rec (cur_top_40 (p - 1280)) (cur_top_39 (p - 1248)) (Nat.blt p 1280))) ((Bool.rec (cur_top_38 (p - 1216)) (cur_top_37 (p - 1184)) (Nat.blt p 1216))) (Nat.blt p 1248))) ((Bool.rec ((Bool.rec (cur_top_36 (p - 1152)) (cur_top_35 (p - 1120)) (Nat.blt p 1152))) ((Bool.rec (cur_top_34 (p - 1088)) (cur_top_33 (p - 1056)) (Nat.blt p 1088))) (Nat.blt p 1120))) (Nat.blt p 1184))) (Nat.blt p 1312))) (Nat.blt p 1568))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (cur_top_32 (p - 1024)) (cur_top_31 (p - 992)) (Nat.blt p 1024))) (cur_top_30 (p - 960)) (Nat.blt p 992))) ((Bool.rec (cur_top_29 (p - 928)) (cur_top_28 (p - 896)) (Nat.blt p 928))) (Nat.blt p 960))) ((Bool.rec ((Bool.rec (cur_top_27 (p - 864)) (cur_top_26 (p - 832)) (Nat.blt p 864))) ((Bool.rec (cur_top_25 (p - 800)) (cur_top_24 (p - 768)) (Nat.blt p 800))) (Nat.blt p 832))) (Nat.blt p 896))) ((Bool.rec ((Bool.rec ((Bool.rec (cur_top_23 (p - 736)) (cur_top_22 (p - 704)) (Nat.blt p 736))) ((Bool.rec (cur_top_21 (p - 672)) (cur_top_20 (p - 640)) (Nat.blt p 672))) (Nat.blt p 704))) ((Bool.rec ((Bool.rec (cur_top_19 (p - 608)) (cur_top_18 (p - 576)) (Nat.blt p 608))) ((Bool.rec (cur_top_17 (p - 544)) (cur_top_16 (p - 512)) (Nat.blt p 544))) (Nat.blt p 576))) (Nat.blt p 640))) (Nat.blt p 768))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (cur_top_15 (p - 480)) (cur_top_14 (p - 448)) (Nat.blt p 480))) ((Bool.rec (cur_top_13 (p - 416)) (cur_top_12 (p - 384)) (Nat.blt p 416))) (Nat.blt p 448))) ((Bool.rec ((Bool.rec (cur_top_11 (p - 352)) (cur_top_10 (p - 320)) (Nat.blt p 352))) ((Bool.rec (cur_top_9 (p - 288)) (cur_top_8 (p - 256)) (Nat.blt p 288))) (Nat.blt p 320))) (Nat.blt p 384))) ((Bool.rec ((Bool.rec ((Bool.rec (cur_top_7 (p - 224)) (cur_top_6 (p - 192)) (Nat.blt p 224))) ((Bool.rec (cur_top_5 (p - 160)) (cur_top_4 (p - 128)) (Nat.blt p 160))) (Nat.blt p 192))) ((Bool.rec ((Bool.rec (cur_top_3 (p - 96)) (cur_top_2 (p - 64)) (Nat.blt p 96))) ((Bool.rec (cur_top_1 (p - 32)) (cur_top_0 (p - 0)) (Nat.blt p 32))) (Nat.blt p 64))) (Nat.blt p 128))) (Nat.blt p 256))) (Nat.blt p 512))) (Nat.blt p 1056))
def hr_top (p : Nat) : Nat := (Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (hint_top_65 (p - 2080)) (hint_top_64 (p - 2048)) (Nat.blt p 2080))) (hint_top_63 (p - 2016)) (Nat.blt p 2048))) ((Bool.rec (hint_top_62 (p - 1984)) (hint_top_61 (p - 1952)) (Nat.blt p 1984))) (Nat.blt p 2016))) ((Bool.rec ((Bool.rec (hint_top_60 (p - 1920)) (hint_top_59 (p - 1888)) (Nat.blt p 1920))) ((Bool.rec (hint_top_58 (p - 1856)) (hint_top_57 (p - 1824)) (Nat.blt p 1856))) (Nat.blt p 1888))) (Nat.blt p 1952))) ((Bool.rec ((Bool.rec ((Bool.rec (hint_top_56 (p - 1792)) (hint_top_55 (p - 1760)) (Nat.blt p 1792))) ((Bool.rec (hint_top_54 (p - 1728)) (hint_top_53 (p - 1696)) (Nat.blt p 1728))) (Nat.blt p 1760))) ((Bool.rec ((Bool.rec (hint_top_52 (p - 1664)) (hint_top_51 (p - 1632)) (Nat.blt p 1664))) ((Bool.rec (hint_top_50 (p - 1600)) (hint_top_49 (p - 1568)) (Nat.blt p 1600))) (Nat.blt p 1632))) (Nat.blt p 1696))) (Nat.blt p 1824))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (hint_top_48 (p - 1536)) (hint_top_47 (p - 1504)) (Nat.blt p 1536))) ((Bool.rec (hint_top_46 (p - 1472)) (hint_top_45 (p - 1440)) (Nat.blt p 1472))) (Nat.blt p 1504))) ((Bool.rec ((Bool.rec (hint_top_44 (p - 1408)) (hint_top_43 (p - 1376)) (Nat.blt p 1408))) ((Bool.rec (hint_top_42 (p - 1344)) (hint_top_41 (p - 1312)) (Nat.blt p 1344))) (Nat.blt p 1376))) (Nat.blt p 1440))) ((Bool.rec ((Bool.rec ((Bool.rec (hint_top_40 (p - 1280)) (hint_top_39 (p - 1248)) (Nat.blt p 1280))) ((Bool.rec (hint_top_38 (p - 1216)) (hint_top_37 (p - 1184)) (Nat.blt p 1216))) (Nat.blt p 1248))) ((Bool.rec ((Bool.rec (hint_top_36 (p - 1152)) (hint_top_35 (p - 1120)) (Nat.blt p 1152))) ((Bool.rec (hint_top_34 (p - 1088)) (hint_top_33 (p - 1056)) (Nat.blt p 1088))) (Nat.blt p 1120))) (Nat.blt p 1184))) (Nat.blt p 1312))) (Nat.blt p 1568))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (hint_top_32 (p - 1024)) (hint_top_31 (p - 992)) (Nat.blt p 1024))) (hint_top_30 (p - 960)) (Nat.blt p 992))) ((Bool.rec (hint_top_29 (p - 928)) (hint_top_28 (p - 896)) (Nat.blt p 928))) (Nat.blt p 960))) ((Bool.rec ((Bool.rec (hint_top_27 (p - 864)) (hint_top_26 (p - 832)) (Nat.blt p 864))) ((Bool.rec (hint_top_25 (p - 800)) (hint_top_24 (p - 768)) (Nat.blt p 800))) (Nat.blt p 832))) (Nat.blt p 896))) ((Bool.rec ((Bool.rec ((Bool.rec (hint_top_23 (p - 736)) (hint_top_22 (p - 704)) (Nat.blt p 736))) ((Bool.rec (hint_top_21 (p - 672)) (hint_top_20 (p - 640)) (Nat.blt p 672))) (Nat.blt p 704))) ((Bool.rec ((Bool.rec (hint_top_19 (p - 608)) (hint_top_18 (p - 576)) (Nat.blt p 608))) ((Bool.rec (hint_top_17 (p - 544)) (hint_top_16 (p - 512)) (Nat.blt p 544))) (Nat.blt p 576))) (Nat.blt p 640))) (Nat.blt p 768))) ((Bool.rec ((Bool.rec ((Bool.rec ((Bool.rec (hint_top_15 (p - 480)) (hint_top_14 (p - 448)) (Nat.blt p 480))) ((Bool.rec (hint_top_13 (p - 416)) (hint_top_12 (p - 384)) (Nat.blt p 416))) (Nat.blt p 448))) ((Bool.rec ((Bool.rec (hint_top_11 (p - 352)) (hint_top_10 (p - 320)) (Nat.blt p 352))) ((Bool.rec (hint_top_9 (p - 288)) (hint_top_8 (p - 256)) (Nat.blt p 288))) (Nat.blt p 320))) (Nat.blt p 384))) ((Bool.rec ((Bool.rec ((Bool.rec (hint_top_7 (p - 224)) (hint_top_6 (p - 192)) (Nat.blt p 224))) ((Bool.rec (hint_top_5 (p - 160)) (hint_top_4 (p - 128)) (Nat.blt p 160))) (Nat.blt p 192))) ((Bool.rec ((Bool.rec (hint_top_3 (p - 96)) (hint_top_2 (p - 64)) (Nat.blt p 96))) ((Bool.rec (hint_top_1 (p - 32)) (hint_top_0 (p - 0)) (Nat.blt p 32))) (Nat.blt p 64))) (Nat.blt p 128))) (Nat.blt p 256))) (Nat.blt p 512))) (Nat.blt p 1056))
def bds_top : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 8, g_49), (m_50, s_50, 8, g_50), (m_102, s_102, 8, g_102), (m_51, s_51, 8, g_51), (m_52, s_52, 8, g_52), (m_104, s_104, 8, g_104), (m_28, s_28, 7, g_28), (m_45, s_45, 7, g_45), (m_31, s_31, 7, g_31), (m_103, s_103, 7, g_103), (m_109, s_109, 8, g_109), (m_111, s_111, 8, g_111), (m_105, s_105, 7, g_105), (m_43, s_43, 7, g_43), (m_47, s_47, 7, g_47), (m_10, s_10, 4, g_10), (m_0, s_0, 4, g_0), (m_40, s_40, 5, g_40), (m_35, s_35, 5, g_35), (m_41, s_41, 5, g_41), (m_32, s_32, 4, g_32), (m_8, s_8, 4, g_8), (m_128, s_128, 8, g_128), (m_132, s_132, 8, g_132), (m_48, s_48, 5, g_48), (m_21, s_21, 4, g_21), (m_18, s_18, 4, g_18), (m_39, s_39, 5, g_39), (m_5, s_5, 4, g_5), (m_9, s_9, 4, g_9), (m_13, s_13, 4, g_13), (m_44, s_44, 5, g_44), (m_3, s_3, 4, g_3), (m_33, s_33, 5, g_33), (m_36, s_36, 5, g_36), (m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7), (m_24, s_24, 4, g_24), (m_23, s_23, 4, g_23), (m_1, s_1, 4, g_1), (m_4, s_4, 4, g_4), (m_19, s_19, 4, g_19), (m_27, s_27, 5, g_27), (m_20, s_20, 4, g_20), (m_26, s_26, 4, g_26)]
def ep_top : Nat := 0x160800080000162000000020005600600048006801020600060a060801021222120012200154144414501440
def ch_top : Nat → Bool := dagCheckNodeV5 0xffffffffffffffff 0x1571777175f177f ep_top 6 63 bds_top 2084 (dagTraceF 0xffffffffffffffff rootStock 11 fr_top) cr_top hr_top
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rc_top : dagCheckRootsV5 0xffffffffffffffff 0x1571777175f177f ep_top 6 63 2084 bds_top (dagTraceF 0xffffffffffffffff rootStock 11 fr_top) (cr_top 0) (hr_top 0) rootStock 11 = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_0 : treeBlockF 0 32 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_32 : treeBlockF 32 64 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_64 : treeBlockF 64 96 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_96 : treeBlockF 96 128 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_128 : treeBlockF 128 160 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_160 : treeBlockF 160 192 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_192 : treeBlockF 192 224 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_224 : treeBlockF 224 256 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_256 : treeBlockF 256 288 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_288 : treeBlockF 288 320 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_320 : treeBlockF 320 352 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_352 : treeBlockF 352 384 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_384 : treeBlockF 384 416 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_416 : treeBlockF 416 448 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_448 : treeBlockF 448 480 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_480 : treeBlockF 480 512 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_512 : treeBlockF 512 544 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_544 : treeBlockF 544 576 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_576 : treeBlockF 576 608 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_608 : treeBlockF 608 640 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_640 : treeBlockF 640 672 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_672 : treeBlockF 672 704 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_704 : treeBlockF 704 736 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_736 : treeBlockF 736 768 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_768 : treeBlockF 768 800 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_800 : treeBlockF 800 832 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_832 : treeBlockF 832 864 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_864 : treeBlockF 864 896 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_896 : treeBlockF 896 928 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_928 : treeBlockF 928 960 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_960 : treeBlockF 960 992 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_992 : treeBlockF 992 1024 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1024 : treeBlockF 1024 1056 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1056 : treeBlockF 1056 1088 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1088 : treeBlockF 1088 1120 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1120 : treeBlockF 1120 1152 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1152 : treeBlockF 1152 1184 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1184 : treeBlockF 1184 1216 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1216 : treeBlockF 1216 1248 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1248 : treeBlockF 1248 1280 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1280 : treeBlockF 1280 1312 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1312 : treeBlockF 1312 1344 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1344 : treeBlockF 1344 1376 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1376 : treeBlockF 1376 1408 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1408 : treeBlockF 1408 1440 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1440 : treeBlockF 1440 1472 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1472 : treeBlockF 1472 1504 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1504 : treeBlockF 1504 1536 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1536 : treeBlockF 1536 1568 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1568 : treeBlockF 1568 1600 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1600 : treeBlockF 1600 1632 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1632 : treeBlockF 1632 1664 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1664 : treeBlockF 1664 1696 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1696 : treeBlockF 1696 1728 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1728 : treeBlockF 1728 1760 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1760 : treeBlockF 1760 1792 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1792 : treeBlockF 1792 1824 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1824 : treeBlockF 1824 1856 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1856 : treeBlockF 1856 1888 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1888 : treeBlockF 1888 1920 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1920 : treeBlockF 1920 1952 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1952 : treeBlockF 1952 1984 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_1984 : treeBlockF 1984 2016 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_2016 : treeBlockF 2016 2048 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_2048 : treeBlockF 2048 2080 ch_top = true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem nb_top_2080 : treeBlockF 2080 2084 ch_top = true := by decide +kernel
theorem nc_top : ∀ i, 0 ≤ i → i < 2084 → ch_top i = true := (block_join (block_join (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_32 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_64 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_96 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_128 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_160 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_192 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_224 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_256 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_288 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_320 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_352 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_384 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_416 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_448 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_480 h1 h2))))) (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_512 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_544 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_576 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_608 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_640 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_672 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_704 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_736 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_768 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_800 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_832 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_864 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_896 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_928 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_960 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_992 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1024 h1 h2))))))) (block_join (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1056 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1088 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1120 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1152 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1184 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1216 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1248 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1280 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1312 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1344 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1376 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1408 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1440 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1472 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1504 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1536 h1 h2))))) (block_join (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1568 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1600 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1632 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1664 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1696 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1728 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1760 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1792 h1 h2)))) (block_join (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1824 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1856 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1888 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1920 h1 h2))) (block_join (block_join (fun _ h1 h2 => treeBlockF_at nb_top_1952 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_1984 h1 h2)) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_2016 h1 h2) (block_join (fun _ h1 h2 => treeBlockF_at nb_top_2048 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_top_2080 h1 h2))))))))
theorem lb_top : LowerBin 0xffffffffffffffff rootStock 0x1571777175f177f 12 :=
  lowerDagV5 (kn_cons lb_49 (kn_cons lb_50 (kn_cons lb_102 (kn_cons lb_51 (kn_cons lb_52 (kn_cons lb_104 (kn_cons lb_28 (kn_cons lb_45 (kn_cons lb_31 (kn_cons lb_103 (kn_cons lb_109 (kn_cons lb_111 (kn_cons lb_105 (kn_cons lb_43 (kn_cons lb_47 (kn_cons lb_10 (kn_cons lb_0 (kn_cons lb_40 (kn_cons lb_35 (kn_cons lb_41 (kn_cons lb_32 (kn_cons lb_8 (kn_cons lb_128 (kn_cons lb_132 (kn_cons lb_48 (kn_cons lb_21 (kn_cons lb_18 (kn_cons lb_39 (kn_cons lb_5 (kn_cons lb_9 (kn_cons lb_13 (kn_cons lb_44 (kn_cons lb_3 (kn_cons lb_33 (kn_cons lb_36 (kn_cons lb_2 (kn_cons lb_7 (kn_cons lb_24 (kn_cons lb_23 (kn_cons lb_1 (kn_cons lb_4 (kn_cons lb_19 (kn_cons lb_27 (kn_cons lb_20 (kn_cons lb_26 (kn_nil)))))))))))))))))))))))))))))))))))))))))))))) rc_top nc_top (by decide +kernel)

-- Thirteen-gate monotone replacement, discovered by target-specific decomposition.
def replacement : List Gate :=
  [⟨.and, [0, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 8]⟩,
   ⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [3, 12]⟩,
   ⟨.or, [1, 4]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.and, [13, 16]⟩,
   ⟨.or, [9, 17]⟩]
theorem replacement_mono : Monotone2 ⟨replacement, 18⟩ := by
  simp [Monotone2, replacement]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem replacement_truth : ∀ x : Fin 6 → Bool, Circuit.eval ⟨replacement, 18⟩ (List.ofFn x) = target x := by
  decide +kernel
end PEqualNP.Outside.L_meta_45458_aux

theorem PEqualNP.Outside.L_meta_45458 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4209568384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4209568384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_45458_aux.table2_from_lowerBin 13
    PEqualNP.Outside.L_meta_45458_aux.lb_top PEqualNP.Outside.L_meta_45458_aux.replacement 18 rfl
    PEqualNP.Outside.L_meta_45458_aux.replacement_mono PEqualNP.Outside.L_meta_45458_aux.replacement_truth
