import PEqualNP.Defs

-- The pair and face checker is adapted from open-goat/pequalnp-proofs PR 54419. The data and circuit below are for this table.

-- The generic text of this file (the kernel-run search and its soundness proof, the cut masks, the hash-split root checks, the circuit bridge) is adapted
-- from the merged PEqualNP.Outside.L_meta_49489 (willakone), which builds on the kernel-run template of the merged L_meta_30723
-- (xyzzyy, pull request 43863, Apache License 2.0); the per-row data (table, pair sample, face bounds, cut masks, root plan, witness) is generated for this table.



/- The live-wire checker and its soundness proof are from odinfree, open-goat/pequalnp-proofs PR 52901. The circuit and all certificate data below were generated for this table. -/

namespace PEqualNP.Outside.L_meta_45452.Free

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

theorem masked_zero (mask : Nat) : Masked mask 0 := by
  unfold Masked; simp

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem masked_xor {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (a ^^^ b) := by
  unfold Masked at ha hb ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_xor] at ea eb ⊢
  cases hm : mask.testBit i <;> simp_all

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

theorem canon_masked (mask w : Nat) : Masked mask (canon mask w) := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0]; exact masked_zero mask
  · rw [h1]; exact masked_land_right mask w
  · rw [h2]; exact masked_xor (masked_self mask) (masked_land_right mask w)

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

def recipeGateBin (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  availB bank ac && availB bank bc &&
    (Nat.beq vc (binOp cut 0 ac bc) || Nat.beq vc (binOp cut 1 ac bc) ||
     Nat.beq vc (binOp cut 2 ac bc) || Nat.beq vc (binOp cut 3 ac bc))

theorem recipeGateBin_spec {cut : Nat} {bank : List Nat} {vc ac bc : Nat}
    (h : recipeGateBin cut bank vc ac bc = true) : GateBin cut bank vc := by
  unfold recipeGateBin at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, availB_spec] at h
  obtain ⟨⟨ha, hb⟩, ((h0 | h1) | h2) | h3⟩ := h
  · exact ⟨ac, bc, 0, by omega, ha, hb, h0⟩
  · exact ⟨ac, bc, 1, by omega, ha, hb, h1⟩
  · exact ⟨ac, bc, 2, by omega, ha, hb, h2⟩
  · exact ⟨ac, bc, 3, by omega, ha, hb, h3⟩

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

def replayRec (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canon cut w
      if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
        v :: next (v :: bank)
      else next bank) hist bank

theorem replayRec_builds (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    BuildsBin cut bank (replayRec cut needed hist bank) := by
  induction hist generalizing bank with
  | nil => trivial
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    change BuildsBin cut bank
      (if needed.contains (canon cut w) && !(availB bank (canon cut w)) &&
          recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) then
        canon cut w :: replayRec cut needed hist (canon cut w :: bank)
      else replayRec cut needed hist bank)
    split
    · rename_i hyes
      exact ⟨recipeGateBin_spec (Bool.and_eq_true_iff.mp hyes).2, ih _⟩
    · exact ih _

def boundCloses (target : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, goal) := bound
  let (fuel, ws, hist) := state
  Nat.beq (canon cut target) goal && !(Nat.beq goal 0) &&
    forceW (fuel - flatCount cut ws) (fun rem =>
      if Nat.blt rem lower then
        forceWs (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length + rem) lower then
            forceWs (recipeClose cut stock hist start) (fun needed =>
              if Nat.blt (needed.length + rem) lower then
                forceWs (replayRec cut needed hist.reverse stock) (fun replay =>
                  Nat.blt (replay.length + rem) lower &&
                    ws.all (fun w => availB (replay ++ stock) (canon cut w)))
              else false)
          else false)
      else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => boundCloses target state b || rest) bounds

def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1

theorem boundCloses_sound {mask goal : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    boundCloses goal state bound = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hlow sub nd hk hlive
  apply Bool.eq_false_iff.mpr
  intro hc
  unfold boundCloses at hc
  simp only [forceW_eq, forceWs_eq, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨hgeq, hgnz⟩, scan⟩ := hc
  have hgnz' : bgoal ≠ 0 := ne_of_beq_false hgnz
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  simp only [Bool.and_eq_true, Nat.blt_eq] at scan
  obtain ⟨hlen, hsrc⟩ := scan
  set replay := replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock
  have hgnf : canon cut goal ≠ 0 := hgeq.symm ▸ hgnz'
  have hsup : ∀ w ∈ ws.toFinset, Avail (replay ++ stock) (canon cut w) := by
    intro w hw
    exact availB_spec.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
  obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (replay ++ stock) hsup
  rw [← flatCount_card cut nd] at hylen
  have hboth := builds_append (replayRec_builds cut _ hist.reverse stock) hybd
  have hfinal : Avail ((replay ++ ys) ++ stock) bgoal := by
    rw [← hgeq]
    exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
  have heno := hlow (replay ++ ys) hboth hfinal
  simp only [List.length_append] at heno
  omega

theorem knownCloses_sound {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    knownCloses goal bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change (boundCloses goal state b || knownCloses goal bs state) = false
    rw [boundCloses_sound (hknown b List.mem_cons_self) (hsub b List.mem_cons_self) nd hk hlive]
    exact ih (fun x hx => hknown x (List.mem_cons_of_mem _ hx)) (fun x hx => hsub x (List.mem_cons_of_mem _ hx))

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

def makeToken (a b op keep : Nat) : Nat := ((a * 16 + b) * 4 + op) * 4 + keep

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

def dagLocal (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Nat.blt (fuel + 1) ws.length ||
    !(dagPart ws goal (mask ^^^ goal)) ||
    knownCloses goal bounds state

theorem dagLocal_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    dagLocal mask goal bounds state = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  dsimp only at nd hk hlive
  unfold dagLocal
  have hcard : ws.length ≤ fuel + 1 := by
    have := liveBin_card_le hlive
    rw [List.toFinset_card_of_nodup nd] at this; omega
  have h1 : Nat.blt (fuel + 1) ws.length = false := by
    cases h : Nat.blt (fuel + 1) ws.length; rfl; have := Nat.blt_eq.mp h; omega
  have h2 : dagPart ws goal (mask ^^^ goal) = true := dagPart_live hgm hlive
  have h3 : knownCloses goal bounds (fuel, ws, hist) = false :=
    knownCloses_sound hknown hsub nd hk hlive
  simp [h1, h2, h3]

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

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Nat.blt dest count &&
      match states dest with
      | none => false
      | some saved => Nat.beq saved.1 state.1 && (saved.2.1 == state.2.1)

def dagCheckChildren (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := ws.length
  !(ws.contains goal) &&
    (Nat.beq fuel 0 ||
      (Nat.blt n 17 &&
        treeBlock 0 n (fun a =>
          let x := ws.getD a 0
          treeBlock (a + 1) n (fun b =>
            let y := ws.getD b 0
            treeBlock 0 4 (fun op =>
              forceW (binOp mask op x y) (fun z =>
                Nat.beq z 0 || ws.contains z ||
                  treeBlock 0 4 (fun keep =>
                    let keepA := Nat.beq (keep &&& 1) 1
                    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
                    let newLen := n - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0)
                    Nat.blt fuel newLen ||
                      forceWs (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))) (fun ws' =>
                        let ch := (fuel - 1, ws', (z, x, y) :: hist)
                        dagLocal mask goal bounds ch || ref (makeToken a b op keep) ch))))))))

def dagCheckNode (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (dagRef count states links (i + 1)) st

def dagCheckRoots (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ stock.length) (fun token =>
    forceWs (subsetWords stock token) (fun ws =>
      let st := (fuel, ws, [])
      dagLocal mask goal bounds st || ref token st))

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

theorem dagAllNodes {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {select : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hsel : ∀ i, ∀ b ∈ select i, b ∈ bounds)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal (select i) count
      (dagTrace mask stock fuel forest) links i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNode at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
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
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm (fun b hb => hknown b (hsel i b hb)) (fun b hb => hsub b (hsel i b hb)) hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · unfold dagRef at href
            split at href
            · contradiction
            · rename_i dest _
              simp only [Bool.and_eq_true, Nat.blt_eq] at href
              obtain ⟨hdest, hst⟩ := href
              cases htr2 : dagTrace mask stock fuel forest dest with
              | none => rw [htr2] at hst; contradiction
              | some saved =>
                rw [htr2] at hst
                simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
                obtain ⟨hfEq, hwEq⟩ := hst
                have hbelow : rem - 1 < cap := by omega
                exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive')

theorem lowerDag {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {select : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true)
    (hsel : ∀ i, ∀ b ∈ select i, b ∈ bounds)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal (select i) count
      (dagTrace mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · unfold dagRef at href
    split at href
    · contradiction
    · rename_i dest _
      simp only [Bool.and_eq_true, Nat.blt_eq] at href
      obtain ⟨hdest, hst⟩ := href
      cases htr : dagTrace mask stock fuel forest dest with
      | none => rw [htr] at hst; contradiction
      | some saved =>
        rw [htr] at hst
        simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
        obtain ⟨hfEq, hwEq⟩ := hst
        exact dagAllNodes hgm hknown hsub snd hsel hnodes fuel dest saved hdest htr hfEq k (by omega) (hwEq ▸ hlive')

def unpack (data width idx : Nat) : Nat :=
  (data >>> (idx * width)) &&& ((1 <<< width) - 1)

def unpackForest (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := pBits + tBits
  let code := unpack data w i
  (code >>> tBits, code &&& ((1 <<< tBits) - 1))

def unpackLinks (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpack index idxW parent
    let sz := entry &&& ((1 <<< sizeBits) - 1)
    let off := entry >>> sizeBits
    let w := tokBits + destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        if Nat.blt lo hi then
          let mid := (lo + hi) / 2
          let code := unpack data w mid
          let key := code &&& ((1 <<< tokBits) - 1)
          if Nat.beq tok key then some (code >>> tokBits)
          else if Nat.blt tok key then next lo mid else next (mid + 1) hi
        else none) steps) off (off + sz)

def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

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

def allN (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun w _ ih => Bool.rec false ih (p w)) l

theorem allN_eq (p : Nat → Bool) (l : List Nat) : allN p l = l.all p := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec false (allN p ws) (p w) = (p w && ws.all p)
    rw [ih]; cases p w <;> rfl

def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l

theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]

def appN (l r : List Nat) : List Nat :=
  List.rec r (fun w _ ih => w :: ih) l

theorem appN_eq (l r : List Nat) : appN l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w ws ih => change w :: appN ws r = w :: (ws ++ r); rw [ih]

def revAccN {α : Type} (l acc : List α) : List α :=
  (List.rec (motive := fun _ => List α → List α) (fun a => a) (fun w _ ih a => ih (w :: a)) l) acc

theorem revAccN_eq {α : Type} (l acc : List α) : revAccN l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    change revAccN ws (w :: acc) = (w :: ws).reverse ++ acc
    rw [ih, List.reverse_cons, List.append_assoc]; rfl

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

def flatCountF (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt =>
    let v := Nat.land w cut
    Bool.rec (Bool.rec cnt (Nat.add cnt 1) (Nat.beq v cut)) (Nat.add cnt 1) (Nat.beq v 0)) ws

theorem flatCountF_eq (cut : Nat) (ws : List Nat) : flatCountF cut ws = flatCount cut ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) cut))
      (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) 0) =
      bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws)
    rw [ih]
    rcases canon_cases cut w with ⟨h0, h1 | h2⟩ | ⟨hne, _⟩
    · have hb : Nat.beq (Nat.land w cut) 0 = true := Nat.beq_eq.mpr h1
      rw [h0, hb, Nat.beq_refl]; rfl
    · have hb : Nat.beq (Nat.land w cut) cut = true := Nat.beq_eq.mpr h2
      rw [h0, hb, Nat.beq_refl]; cases Nat.beq (Nat.land w cut) 0 <;> rfl
    · have h1 : Nat.beq (Nat.land w cut) 0 = false := beq_false_ne (fun e => by
        change w &&& cut = 0 at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      have h2 : Nat.beq (Nat.land w cut) cut = false := beq_false_ne (fun e => by
        change w &&& cut = cut at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      rw [h1, h2, beq_false_ne hne]; rfl

def availBF (bank : List Nat) (w : Nat) : Bool :=
  Bool.rec (memN w bank) true (Nat.beq w 0)

theorem availBF_eq (bank : List Nat) (w : Nat) : availBF bank w = availB bank w := by
  unfold availBF availB; rw [memN_eq]; cases Nat.beq w 0 <;> rfl

def recipeGateBinF (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  Bool.rec false
    (Bool.rec false
      (Bool.rec
        (Bool.rec
          (Bool.rec (Nat.beq vc (binOpF cut 3 ac bc)) true (Nat.beq vc (binOpF cut 2 ac bc)))
          true (Nat.beq vc (binOpF cut 1 ac bc)))
        true (Nat.beq vc (binOpF cut 0 ac bc)))
      (availBF bank bc))
    (availBF bank ac)

theorem recipeGateBinF_eq (cut : Nat) (bank : List Nat) (vc ac bc : Nat) :
    recipeGateBinF cut bank vc ac bc = recipeGateBin cut bank vc ac bc := by
  unfold recipeGateBinF recipeGateBin
  simp only [availBF_eq, binOpF_eq]
  cases availB bank ac <;> cases availB bank bc <;>
    cases Nat.beq vc (binOp cut 0 ac bc) <;> cases Nat.beq vc (binOp cut 1 ac bc) <;>
    cases Nat.beq vc (binOp cut 2 ac bc) <;> cases Nat.beq vc (binOp cut 3 ac bc) <;> rfl

def addUniqF (w : Nat) (l : List Nat) : List Nat :=
  Bool.rec (w :: l) l (memN w l)

theorem addUniqF_eq (w : Nat) (l : List Nat) : addUniqF w l = addUniq w l := by
  unfold addUniqF addUniq; rw [memN_eq]; cases l.contains w <;> rfl

def recipeStartF (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canonF cut w
    Bool.rec (addUniqF v acc) acc (availBF stock v)) ws

theorem recipeStartF_eq (cut : Nat) (stock ws : List Nat) : recipeStartF cut stock ws = recipeStart cut stock ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (addUniqF (canonF cut w) (recipeStartF cut stock ws)) (recipeStartF cut stock ws) (availBF stock (canonF cut w)) =
      (if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    rw [ih, canonF_eq, availBF_eq, addUniqF_eq]; cases availB stock (canon cut w) <;> rfl

def recipeCloseF (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canonF cut w
      Bool.rec (next acc)
        (let va := canonF cut a
         let vb := canonF cut b
         let acc1 := Bool.rec (addUniqF va acc) acc (availBF stock va)
         let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
         next acc2)
        (memN v acc)) hist needed

theorem recipeCloseF_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseF cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : recipeCloseF cut stock ((w, a, b) :: hist) needed =
        Bool.rec (recipeCloseF cut stock hist needed)
          (let va := canonF cut a; let vb := canonF cut b
           let acc1 := Bool.rec (addUniqF va needed) needed (availBF stock va)
           let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
           recipeCloseF cut stock hist acc2)
          (memN (canonF cut w) needed) := rfl
    have hR : recipeClose cut stock ((w, a, b) :: hist) needed =
        (if needed.contains (canon cut w) then
          let va := canon cut a; let vb := canon cut b
          let acc1 := if availB stock va then needed else addUniq va needed
          let acc2 := if availB stock vb then acc1 else addUniq vb acc1
          recipeClose cut stock hist acc2
        else recipeClose cut stock hist needed) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, addUniqF_eq]
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only; rw [ih]
      cases availB stock (canon cut a) <;> cases availB stock (canon cut b) <;> rfl

def replayRecF (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canonF cut w
      Bool.rec (next bank)
        (Bool.rec
          (Bool.rec (next bank) (v :: next (v :: bank))
            (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
          (next bank) (availBF bank v))
        (memN v needed)) hist bank

theorem replayRecF_eq (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    replayRecF cut needed hist bank = replayRec cut needed hist bank := by
  induction hist generalizing bank with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : replayRecF cut needed ((w, a, b) :: hist) bank =
        let v := canonF cut w
        Bool.rec (replayRecF cut needed hist bank)
          (Bool.rec
            (Bool.rec (replayRecF cut needed hist bank) (v :: replayRecF cut needed hist (v :: bank))
              (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
            (replayRecF cut needed hist bank) (availBF bank v))
          (memN v needed) := rfl
    have hR : replayRec cut needed ((w, a, b) :: hist) bank =
        (let v := canon cut w
         if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
           v :: replayRec cut needed hist (v :: bank)
         else replayRec cut needed hist bank) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, recipeGateBinF_eq]
    rw [ih bank, ih (canon cut w :: bank)]
    cases needed.contains (canon cut w) <;> cases availB bank (canon cut w) <;>
      cases recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) <;> rfl

def boundClosesF (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, _) := bound
  let (fuel, ws, hist) := state
  forceW (Nat.sub fuel (flatCountF cut ws)) (fun rem =>
    Bool.rec false
      (forceWs (recipeStartF cut stock ws) (fun start =>
        Bool.rec false
          (forceWs (recipeCloseF cut stock hist start) (fun needed =>
            Bool.rec false
              (forceWs (replayRecF cut needed (revAccN hist []) stock) (fun replay =>
                Bool.rec false
                  (allN (fun w => availBF (appN replay stock) (canonF cut w)) ws)
                  (Nat.blt (Nat.add (lenN replay) rem) lower)))
              (Nat.blt (Nat.add (lenN needed) rem) lower)))
          (Nat.blt (Nat.add (lenN start) rem) lower)))
      (Nat.blt rem lower))

theorem boundClosesF_eq {target : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hg : canon bound.1 target = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0) :
    boundClosesF state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hg hnz
  unfold boundClosesF boundCloses
  simp only [forceW_eq, forceWs_eq, flatCountF_eq, recipeStartF_eq, recipeCloseF_eq,
    replayRecF_eq, revAccN_eq, List.append_nil, lenN_eq, allN_eq, appN_eq, availBF_eq, canonF_eq,
    hg, Nat.beq_refl, beq_false_ne hnz, Bool.not_false, Bool.and_true, Bool.true_and]
  cases Nat.blt (fuel - flatCount cut ws) lower
  · rfl
  · cases Nat.blt ((recipeStart cut stock ws).length + (fuel - flatCount cut ws)) lower
    · rfl
    · cases Nat.blt ((recipeClose cut stock hist (recipeStart cut stock ws)).length + (fuel - flatCount cut ws)) lower
      · rfl
      · cases Nat.blt ((replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock).length + (fuel - flatCount cut ws)) lower <;> rfl

def knownClosesF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => Bool.rec rest true (boundClosesF state b)) bounds

theorem knownClosesF_eq {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    knownClosesF bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change Bool.rec (knownClosesF bs state) true (boundClosesF state b) =
      (boundCloses target state b || knownCloses target bs state)
    have h0 := hgoals b List.mem_cons_self
    rw [boundClosesF_eq h0.1 h0.2, ih (fun x hx => hgoals x (List.mem_cons_of_mem _ hx))]
    cases boundCloses target state b <;> rfl

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

def dagLocalF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Bool.rec
    (Bool.rec true
      (knownClosesF bounds state)
      (dagPartF ws goal (Nat.xor mask goal)))
    true (Nat.blt (Nat.add fuel 1) (lenN ws))

theorem dagLocalF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagLocalF mask goal bounds state = dagLocal mask goal bounds state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagLocalF dagLocal; dsimp only
  rw [lenN_eq, dagPartF_eq, knownClosesF_eq hgoals]
  cases Nat.blt (fuel + 1) ws.length <;> cases dagPart ws goal (mask ^^^ goal) <;> rfl

def dagRefF (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Bool.rec false
      (match states dest with
       | none => false
       | some saved => Bool.rec false (eqListN saved.2.1 state.2.1) (Nat.beq saved.1 state.1))
      (Nat.blt dest count)

theorem dagRefF_eq (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagRefF count states links parent token state = dagRef count states links parent token state := by
  unfold dagRefF dagRef
  cases links parent token with
  | none => rfl
  | some dest =>
    dsimp only
    cases Nat.blt dest count
    · rfl
    · dsimp only
      cases states dest with
      | none => rfl
      | some saved =>
        dsimp only
        rw [eqListN_eq]; cases Nat.beq saved.1 state.1 <;> rfl

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

def dagCheckChildrenF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := lenN ws
  Bool.rec
    (Bool.rec
      (Bool.rec false
        (treeBlockF 0 n (fun a =>
          let x := getDN ws a
          treeBlockF (Nat.add a 1) n (fun b =>
            let y := getDN ws b
            treeBlockF 0 4 (fun op =>
              forceW (binOpF mask op x y) (fun z =>
                Bool.rec
                  (Bool.rec
                    (treeBlockF 0 4 (fun keep =>
                      let keepA := Nat.beq (Nat.land keep 1) 1
                      let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
                      let newLen := Nat.add (Nat.add (Nat.sub n 1) (Bool.rec 0 1 keepA)) (Bool.rec 0 1 keepB)
                      Bool.rec
                        (forceWs (insertSortedF z (dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws))) (fun ws' =>
                          let ch := (Nat.sub fuel 1, ws', (z, x, y) :: hist)
                          let tok := Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep
                          Bool.rec (dagLocalF mask goal bounds ch) true (ref tok ch)))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)

theorem makeTokenF_eq (a b op keep : Nat) :
    Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep =
    makeToken a b op keep := by
  unfold makeToken
  change ((((a <<< 4) + b) <<< 2) + op) <<< 2 + keep = _
  simp only [Nat.shiftLeft_eq]

theorem dagCheckChildrenF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagCheckChildrenF mask goal bounds ref state = dagCheckChildren mask goal bounds ref state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagCheckChildrenF dagCheckChildren; dsimp only
  simp only [lenN_eq, memN_eq, treeBlockF_eq]
  cases ws.contains goal
  · cases Nat.beq fuel 0
    · cases Nat.blt ws.length 17
      · rfl
      · dsimp only
        simp only [Bool.not_false, Bool.true_and, Bool.false_or]
        congr 1; funext a
        simp only [getDN_eq]
        congr 1; funext b
        congr 1; funext op
        simp only [binOpF_eq, forceW_eq]
        cases Nat.beq (binOp mask op (ws.getD a 0) (ws.getD b 0)) 0
        · cases ws.contains (binOp mask op (ws.getD a 0) (ws.getD b 0))
          · dsimp only; simp only [Bool.false_or]
            congr 1; funext keep
            simp only [insertSortedF_eq, dropValF_eq, forceWs_eq, makeTokenF_eq, dagLocalF_eq hgoals]
            cases Nat.beq (keep &&& 1) 1 <;> cases Nat.beq ((keep >>> 1) &&& 1) 1
            all_goals dsimp only
            all_goals simp only [Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false]
            all_goals cases Nat.blt fuel _
            all_goals try rfl
            all_goals cases ref (makeToken a b op keep) _ <;> cases dagLocal mask goal bounds _ <;> rfl
          · rfl
        · rfl
    · rfl
  · rfl

def dagCheckNodeF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (dagRefF count states links (Nat.add i 1)) st

theorem dagCheckNodeF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) :
    dagCheckNodeF mask goal bounds count states links i = dagCheckNode mask goal bounds count states links i := by
  unfold dagCheckNodeF dagCheckNode
  cases states i with
  | none => rfl
  | some st =>
    have href : dagRefF count states links (Nat.add i 1) = dagRef count states links (i + 1) := by
      funext tok s; exact dagRefF_eq count states links (i + 1) tok s
    rw [href]; exact dagCheckChildrenF_eq hgoals _ st

def dagCheckRootsF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlockF 0 (Nat.shiftLeft 1 (lenN stock)) (fun token =>
    forceWs (subsetWordsF stock token) (fun ws =>
      let st := (fuel, ws, [])
      Bool.rec (dagLocalF mask goal bounds st) true (ref token st)))

theorem dagCheckRootsF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) :
    dagCheckRootsF mask goal bounds ref stock fuel = dagCheckRoots mask goal bounds ref stock fuel := by
  unfold dagCheckRootsF dagCheckRoots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow, treeBlockF_eq]
  congr 1; funext tok
  simp only [subsetWordsF_eq, forceWs_eq, dagLocalF_eq hgoals]
  cases ref tok (fuel, subsetWords stock tok, []) <;> cases dagLocal mask goal bounds (fuel, subsetWords stock tok, []) <;> rfl

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksF (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpackF index idxW parent
    let sz := Nat.land entry (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight entry sizeBits
    let w := Nat.add tokBits destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := unpackF data w mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

theorem lowerDagF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {select : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefF count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hsel : ∀ i, ∀ b ∈ select i, b ∈ bounds)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeF mask goal (select i) count
      (dagTraceF mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  have hr : dagCheckRoots mask goal bounds (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true := by
    have href : dagRefF count (dagTrace mask stock fuel forest) links 0 = dagRef count (dagTrace mask stock fuel forest) links 0 := by
      funext t s; exact dagRefF_eq count _ links 0 t s
    rw [href, dagCheckRootsF_eq hgoals] at hroots; exact hroots
  have hn : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal (select i) count (dagTrace mask stock fuel forest) links i = true := by
    intro i h1 h2
    have h := hnodes i h1 h2
    rwa [dagCheckNodeF_eq (bounds := select i) (fun b hb => hgoals b (hsel i b hb))] at h
  exact lowerDag hgm hgnz hcs snd hknown hsub hr hsel hn

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h


def pickCuts {α : Type} : List α → Nat → List α
  | [], _ => []
  | x :: xs, bits =>
    if bits.testBit 0 then x :: pickCuts xs (Nat.shiftRight bits 1)
    else pickCuts xs (Nat.shiftRight bits 1)

theorem pickCuts_mem {α : Type} (xs : List α) (bits : Nat) :
    ∀ b ∈ pickCuts xs bits, b ∈ xs := by
  induction xs generalizing bits with
  | nil => simp [pickCuts]
  | cons x xs ih =>
    intro b hb
    simp only [pickCuts] at hb
    split at hb
    · rcases List.mem_cons.mp hb with hx | ht
      · exact List.mem_cons.mpr (Or.inl hx)
      · exact List.mem_cons_of_mem _ (ih _ b ht)
    · exact List.mem_cons_of_mem _ (ih _ b hb)



def m_0 : Nat := 0x5555000000000000

def s_0 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]

def g_0 : Nat := 0x115000000000000

def bds_0 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_0 : KnownBin bds_0 := by
  intro b hb; simp [bds_0] at hb

theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by
  intro b hb; simp [bds_0] at hb

theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_0] at hb

def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_0 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_0 (j : Nat) := pickCuts bds_0 (unpackF 0x0 1 j)

def node_0 (j : Nat) := dagCheckNodeF m_0 g_0 (select_0 j) 1 (dagTraceF m_0 s_0 3 f_0) l_0 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_0 : dagCheckRootsF m_0 g_0 bds_0 (dagRefF 1 (dagTraceF m_0 s_0 3 f_0) l_0 0) s_0 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_0_0 : treeBlockF 0 1 node_0 = true := by decide +kernel

theorem join_0_0 : ∀ j, 0 ≤ j → j < 1 → node_0 j = true := (fun _ h₁ h₂ => treeBlockF_at block_0_0 h₁ h₂)

theorem nc_0 : ∀ j, 0 ≤ j → j < 1 → node_0 j = true := join_0_0

theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagF (select := select_0) (hsel := fun j => pickCuts_mem bds_0 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0x50505050

def s_1 : List Nat := [0x10101010, 0x500050, 0x5050]

def g_1 : Nat := 0x101050

def bds_1 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_1 : KnownBin bds_1 := by
  intro b hb; simp [bds_1] at hb

theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by
  intro b hb; simp [bds_1] at hb

theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_1] at hb

def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_1 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_1 (j : Nat) := pickCuts bds_1 (unpackF 0x0 1 j)

def node_1 (j : Nat) := dagCheckNodeF m_1 g_1 (select_1 j) 1 (dagTraceF m_1 s_1 3 f_1) l_1 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_1 : dagCheckRootsF m_1 g_1 bds_1 (dagRefF 1 (dagTraceF m_1 s_1 3 f_1) l_1 0) s_1 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_1_0 : treeBlockF 0 1 node_1 = true := by decide +kernel

theorem join_1_0 : ∀ j, 0 ≤ j → j < 1 → node_1 j = true := (fun _ h₁ h₂ => treeBlockF_at block_1_0 h₁ h₂)

theorem nc_1 : ∀ j, 0 ≤ j → j < 1 → node_1 j = true := join_1_0

theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagF (select := select_1) (hsel := fun j => pickCuts_mem bds_1 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0x5050505050505050

def s_2 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]

def g_2 : Nat := 0x10101000101050

def bds_2 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]

theorem kn_2 : KnownBin bds_2 := by
  intro b hb; simp only [bds_2, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1

theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_2, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_2, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_2 : Nat → Nat × Nat := fun _ => (0, 0)

def l_2 : Nat → Nat → Option Nat := fun _ _ => none

def select_2 (j : Nat) := pickCuts bds_2 (unpackF 0x0 1 j)

def node_2 (j : Nat) := dagCheckNodeF m_2 g_2 (select_2 j) 0 (dagTraceF m_2 s_2 4 f_2) l_2 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_2 : dagCheckRootsF m_2 g_2 bds_2 (dagRefF 0 (dagTraceF m_2 s_2 4 f_2) l_2 0) s_2 4 = true := by decide +kernel

theorem nc_2 : ∀ j, 0 ≤ j → j < 0 → node_2 j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_2 : LowerBin m_2 s_2 g_2 5 :=
  lowerDagF (select := select_2) (hsel := fun j => pickCuts_mem bds_2 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0x444400004444

def s_3 : List Nat := [0x40400000404, 0x4400000044, 0x4444]

def g_3 : Nat := 0x400000444

def bds_3 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_3 : KnownBin bds_3 := by
  intro b hb; simp [bds_3] at hb

theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by
  intro b hb; simp [bds_3] at hb

theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_3] at hb

def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_3 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_3 (j : Nat) := pickCuts bds_3 (unpackF 0x0 1 j)

def node_3 (j : Nat) := dagCheckNodeF m_3 g_3 (select_3 j) 1 (dagTraceF m_3 s_3 3 f_3) l_3 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_3 : dagCheckRootsF m_3 g_3 bds_3 (dagRefF 1 (dagTraceF m_3 s_3 3 f_3) l_3 0) s_3 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_3_0 : treeBlockF 0 1 node_3 = true := by decide +kernel

theorem join_3_0 : ∀ j, 0 ≤ j → j < 1 → node_3 j = true := (fun _ h₁ h₂ => treeBlockF_at block_3_0 h₁ h₂)

theorem nc_3 : ∀ j, 0 ≤ j → j < 1 → node_3 j = true := join_3_0

theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagF (select := select_3) (hsel := fun j => pickCuts_mem bds_3 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0x4444444444444444

def s_4 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]

def g_4 : Nat := 0x4000404040444

def bds_4 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]

theorem kn_4 : KnownBin bds_4 := by
  intro b hb; simp only [bds_4, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3

theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_4, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_4, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_4 : Nat → Nat × Nat := fun _ => (0, 0)

def l_4 : Nat → Nat → Option Nat := fun _ _ => none

def select_4 (j : Nat) := pickCuts bds_4 (unpackF 0x0 1 j)

def node_4 (j : Nat) := dagCheckNodeF m_4 g_4 (select_4 j) 0 (dagTraceF m_4 s_4 4 f_4) l_4 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_4 : dagCheckRootsF m_4 g_4 bds_4 (dagRefF 0 (dagTraceF m_4 s_4 4 f_4) l_4 0) s_4 4 = true := by decide +kernel

theorem nc_4 : ∀ j, 0 ≤ j → j < 0 → node_4 j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_4 : LowerBin m_4 s_4 g_4 5 :=
  lowerDagF (select := select_4) (hsel := fun j => pickCuts_mem bds_4 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0x555500005555

def s_5 : List Nat := [0x111100001111, 0x50500000505, 0x5500000055, 0x5555]

def g_5 : Nat := 0x111500001555

def bds_5 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]

theorem kn_5 : KnownBin bds_5 := by
  intro b hb; simp only [bds_5, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3

theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_5, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_5, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_5 : Nat → Nat × Nat := fun _ => (0, 0)

def l_5 : Nat → Nat → Option Nat := fun _ _ => none

def select_5 (j : Nat) := pickCuts bds_5 (unpackF 0x0 1 j)

def node_5 (j : Nat) := dagCheckNodeF m_5 g_5 (select_5 j) 0 (dagTraceF m_5 s_5 4 f_5) l_5 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_5 : dagCheckRootsF m_5 g_5 bds_5 (dagRefF 0 (dagTraceF m_5 s_5 4 f_5) l_5 0) s_5 4 = true := by decide +kernel

theorem nc_5 : ∀ j, 0 ≤ j → j < 0 → node_5 j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_5 : LowerBin m_5 s_5 g_5 5 :=
  lowerDagF (select := select_5) (hsel := fun j => pickCuts_mem bds_5 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x55555555

def s_6 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]

def g_6 : Nat := 0x5151555

def bds_6 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]

theorem kn_6 : KnownBin bds_6 := by
  intro b hb; simp only [bds_6, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1

theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_6, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_6, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_6 : Nat → Nat × Nat := fun _ => (0, 0)

def l_6 : Nat → Nat → Option Nat := fun _ _ => none

def select_6 (j : Nat) := pickCuts bds_6 (unpackF 0x0 1 j)

def node_6 (j : Nat) := dagCheckNodeF m_6 g_6 (select_6 j) 0 (dagTraceF m_6 s_6 4 f_6) l_6 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_6 : dagCheckRootsF m_6 g_6 bds_6 (dagRefF 0 (dagTraceF m_6 s_6 4 f_6) l_6 0) s_6 4 = true := by decide +kernel

theorem nc_6 : ∀ j, 0 ≤ j → j < 0 → node_6 j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_6 : LowerBin m_6 s_6 g_6 5 :=
  lowerDagF (select := select_6) (hsel := fun j => pickCuts_mem bds_6 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0x5500000000005500

def s_7 : List Nat := [0x1100000000001100, 0x500000000000500, 0x5500]

def g_7 : Nat := 0x100000000001500

def bds_7 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_7 : KnownBin bds_7 := by
  intro b hb; simp [bds_7] at hb

theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by
  intro b hb; simp [bds_7] at hb

theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_7] at hb

def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_7 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_7 (j : Nat) := pickCuts bds_7 (unpackF 0x0 1 j)

def node_7 (j : Nat) := dagCheckNodeF m_7 g_7 (select_7 j) 1 (dagTraceF m_7 s_7 3 f_7) l_7 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_7 : dagCheckRootsF m_7 g_7 bds_7 (dagRefF 1 (dagTraceF m_7 s_7 3 f_7) l_7 0) s_7 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_7_0 : treeBlockF 0 1 node_7 = true := by decide +kernel

theorem join_7_0 : ∀ j, 0 ≤ j → j < 1 → node_7 j = true := (fun _ h₁ h₂ => treeBlockF_at block_7_0 h₁ h₂)

theorem nc_7 : ∀ j, 0 ≤ j → j < 1 → node_7 j = true := join_7_0

theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagF (select := select_7) (hsel := fun j => pickCuts_mem bds_7 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x1010101040404040

def s_8 : List Nat := [0x40404040, 0x10001000400040, 0x101000004040]

def g_8 : Nat := 0x10101000000040

def bds_8 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_8 : KnownBin bds_8 := by
  intro b hb; simp [bds_8] at hb

theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by
  intro b hb; simp [bds_8] at hb

theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_8] at hb

def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_8 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_8 (j : Nat) := pickCuts bds_8 (unpackF 0x0 1 j)

def node_8 (j : Nat) := dagCheckNodeF m_8 g_8 (select_8 j) 1 (dagTraceF m_8 s_8 3 f_8) l_8 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_8 : dagCheckRootsF m_8 g_8 bds_8 (dagRefF 1 (dagTraceF m_8 s_8 3 f_8) l_8 0) s_8 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_8_0 : treeBlockF 0 1 node_8 = true := by decide +kernel

theorem join_8_0 : ∀ j, 0 ≤ j → j < 1 → node_8 j = true := (fun _ h₁ h₂ => treeBlockF_at block_8_0 h₁ h₂)

theorem nc_8 : ∀ j, 0 ≤ j → j < 1 → node_8 j = true := join_8_0

theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagF (select := select_8) (hsel := fun j => pickCuts_mem bds_8 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0x404404004044040

def s_9 : List Nat := [0x404000004040, 0x4004000040040, 0x4044040]

def g_9 : Nat := 0x4000004040040

def bds_9 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_9 : KnownBin bds_9 := by
  intro b hb; simp [bds_9] at hb

theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by
  intro b hb; simp [bds_9] at hb

theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_9] at hb

def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_9 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_9 (j : Nat) := pickCuts bds_9 (unpackF 0x0 1 j)

def node_9 (j : Nat) := dagCheckNodeF m_9 g_9 (select_9 j) 1 (dagTraceF m_9 s_9 3 f_9) l_9 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_9 : dagCheckRootsF m_9 g_9 bds_9 (dagRefF 1 (dagTraceF m_9 s_9 3 f_9) l_9 0) s_9 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_9_0 : treeBlockF 0 1 node_9 = true := by decide +kernel

theorem join_9_0 : ∀ j, 0 ≤ j → j < 1 → node_9 j = true := (fun _ h₁ h₂ => treeBlockF_at block_9_0 h₁ h₂)

theorem nc_9 : ∀ j, 0 ≤ j → j < 1 → node_9 j = true := join_9_0

theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagF (select := select_9) (hsel := fun j => pickCuts_mem bds_9 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0x5555555555555555

def s_10 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]

def g_10 : Nat := 0x115111505151555

def bds_10 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_2, s_2, 5, g_2), (m_4, s_4, 5, g_4), (m_5, s_5, 5, g_5), (m_6, s_6, 5, g_6), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9)]

theorem kn_10 : KnownBin bds_10 := by
  intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_2
  · exact lb_4
  · exact lb_5
  · exact lb_6
  · exact lb_7
  · exact lb_8
  · exact lb_9

theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_10 : Nat → Nat × Nat := unpackForestF 0x8a44695c584c525d4a46435d4345415e41523b563a56345a34563356325a3256304e30422a4b2a471a3b1a370b470a4b0a470a3b0a37093a0936084a0846001f 5 11

def l_10 : Nat → Nat → Option Nat := unpackLinksF 0x2d0b42d0b42d0b42c1b02c0b02c0b02c0ac6b0a86a0a82a0a4690a064484d9858ce8308c0288a006401 0xfa34fa44fa44f15ce84ce25d9a55ca4592358b46da46694ad35d9b55cb45b23a8236c15eb952613ab356aa56585aa45a9c5693568a5a8256505a784e70426a4b62475a3b52374b47424b3a47323b2a37213a1936104a0846001f 10 4 11 5 5

def select_10 (j : Nat) := pickCuts bds_10 (unpackF 0x110982010800091119440002011000010001ffbfbf7f7f47df875f1f 8 j)

def node_10 (j : Nat) := dagCheckNodeF m_10 g_10 (select_10 j) 32 (dagTraceF m_10 s_10 7 f_10) l_10 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 32 (dagTraceF m_10 s_10 7 f_10) l_10 0) s_10 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_10_0 : treeBlockF 0 16 node_10 = true := by decide +kernel

theorem join_10_0 : ∀ j, 0 ≤ j → j < 16 → node_10 j = true := (fun _ h₁ h₂ => treeBlockF_at block_10_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_10_16 : treeBlockF 16 32 node_10 = true := by decide +kernel

theorem join_10_16 : ∀ j, 0 ≤ j → j < 32 → node_10 j = true := block_join join_10_0 (fun _ h₁ h₂ => treeBlockF_at block_10_16 h₁ h₂)

theorem nc_10 : ∀ j, 0 ≤ j → j < 32 → node_10 j = true := join_10_16

theorem lb_10 : LowerBin m_10 s_10 g_10 8 :=
  lowerDagF (select := select_10) (hsel := fun j => pickCuts_mem bds_10 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0xc0003000c000300

def s_11 : List Nat := [0x400010004000100, 0x30000000300, 0xc000300]

def g_11 : Nat := 0x10004000300

def bds_11 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_11 : KnownBin bds_11 := by
  intro b hb; simp [bds_11] at hb

theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by
  intro b hb; simp [bds_11] at hb

theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_11] at hb

def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_11 (j : Nat) := pickCuts bds_11 (unpackF 0x0 1 j)

def node_11 (j : Nat) := dagCheckNodeF m_11 g_11 (select_11 j) 1 (dagTraceF m_11 s_11 3 f_11) l_11 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 1 (dagTraceF m_11 s_11 3 f_11) l_11 0) s_11 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_11_0 : treeBlockF 0 1 node_11 = true := by decide +kernel

theorem join_11_0 : ∀ j, 0 ≤ j → j < 1 → node_11 j = true := (fun _ h₁ h₂ => treeBlockF_at block_11_0 h₁ h₂)

theorem nc_11 : ∀ j, 0 ≤ j → j < 1 → node_11 j = true := join_11_0

theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagF (select := select_11) (hsel := fun j => pickCuts_mem bds_11 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0x99009900

def s_12 : List Nat := [0x11001100, 0x9000900, 0x9900]

def g_12 : Nat := 0x1001900

def bds_12 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_12 : KnownBin bds_12 := by
  intro b hb; simp [bds_12] at hb

theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by
  intro b hb; simp [bds_12] at hb

theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_12] at hb

def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_12 (j : Nat) := pickCuts bds_12 (unpackF 0x0 1 j)

def node_12 (j : Nat) := dagCheckNodeF m_12 g_12 (select_12 j) 1 (dagTraceF m_12 s_12 3 f_12) l_12 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 1 (dagTraceF m_12 s_12 3 f_12) l_12 0) s_12 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_12_0 : treeBlockF 0 1 node_12 = true := by decide +kernel

theorem join_12_0 : ∀ j, 0 ≤ j → j < 1 → node_12 j = true := (fun _ h₁ h₂ => treeBlockF_at block_12_0 h₁ h₂)

theorem nc_12 : ∀ j, 0 ≤ j → j < 1 → node_12 j = true := join_12_0

theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagF (select := select_12) (hsel := fun j => pickCuts_mem bds_12 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xa5000000a500

def s_13 : List Nat := [0x50000000500, 0x210000002100, 0xa500]

def g_13 : Nat := 0x10000002500

def bds_13 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp [bds_13] at hb

theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by
  intro b hb; simp [bds_13] at hb

theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_13] at hb

def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_13 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_13 (j : Nat) := pickCuts bds_13 (unpackF 0x0 1 j)

def node_13 (j : Nat) := dagCheckNodeF m_13 g_13 (select_13 j) 1 (dagTraceF m_13 s_13 3 f_13) l_13 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 1 (dagTraceF m_13 s_13 3 f_13) l_13 0) s_13 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_13_0 : treeBlockF 0 1 node_13 = true := by decide +kernel

theorem join_13_0 : ∀ j, 0 ≤ j → j < 1 → node_13 j = true := (fun _ h₁ h₂ => treeBlockF_at block_13_0 h₁ h₂)

theorem nc_13 : ∀ j, 0 ≤ j → j < 1 → node_13 j = true := join_13_0

theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagF (select := select_13) (hsel := fun j => pickCuts_mem bds_13 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xff00ff00ff00ff00

def s_14 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]

def g_14 : Nat := 0x100110005003f00

def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13)]

theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl
  · exact lb_11
  · exact lb_12
  · exact lb_13

theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> decide +kernel

def f_14 : Nat → Nat × Nat := unpackForestF 0x3c38e4a253c3130c4421708541d1c743190c63b18cc54b150c533148c44b110c43b10cc423104c01f 4 10

def l_14 : Nat → Nat → Option Nat := unpackLinksF 0xb85c2e170b85c2e170b0d46a150a85428340a05028140914083e01 0x160e2a94513c9899211222e40547e8eed0db21b23b5c66a52d2a1a1333a46612ca21903b1866208c209801f 9 4 10 5 5

def select_14 (j : Nat) := pickCuts bds_14 (unpackF 0xa0001000007 3 j)

def node_14 (j : Nat) := dagCheckNodeF m_14 g_14 (select_14 j) 23 (dagTraceF m_14 s_14 6 f_14) l_14 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 23 (dagTraceF m_14 s_14 6 f_14) l_14 0) s_14 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_14_0 : treeBlockF 0 16 node_14 = true := by decide +kernel

theorem join_14_0 : ∀ j, 0 ≤ j → j < 16 → node_14 j = true := (fun _ h₁ h₂ => treeBlockF_at block_14_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_14_16 : treeBlockF 16 23 node_14 = true := by decide +kernel

theorem join_14_16 : ∀ j, 0 ≤ j → j < 23 → node_14 j = true := block_join join_14_0 (fun _ h₁ h₂ => treeBlockF_at block_14_16 h₁ h₂)

theorem nc_14 : ∀ j, 0 ≤ j → j < 23 → node_14 j = true := join_14_16

theorem lb_14 : LowerBin m_14 s_14 g_14 7 :=
  lowerDagF (select := select_14) (hsel := fun j => pickCuts_mem bds_14 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x3333000000000000

def s_15 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]

def g_15 : Nat := 0x113000000000000

def bds_15 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp [bds_15] at hb

theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by
  intro b hb; simp [bds_15] at hb

theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_15] at hb

def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_15 (j : Nat) := pickCuts bds_15 (unpackF 0x0 1 j)

def node_15 (j : Nat) := dagCheckNodeF m_15 g_15 (select_15 j) 1 (dagTraceF m_15 s_15 3 f_15) l_15 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 1 (dagTraceF m_15 s_15 3 f_15) l_15 0) s_15 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_15_0 : treeBlockF 0 1 node_15 = true := by decide +kernel

theorem join_15_0 : ∀ j, 0 ≤ j → j < 1 → node_15 j = true := (fun _ h₁ h₂ => treeBlockF_at block_15_0 h₁ h₂)

theorem nc_15 : ∀ j, 0 ≤ j → j < 1 → node_15 j = true := join_15_0

theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagF (select := select_15) (hsel := fun j => pickCuts_mem bds_15 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0x3000300003000300

def s_16 : List Nat := [0x1000100001000100, 0x3000300, 0x300000000300]

def g_16 : Nat := 0x100001000300

def bds_16 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp [bds_16] at hb

theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by
  intro b hb; simp [bds_16] at hb

theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_16] at hb

def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_16 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_16 (j : Nat) := pickCuts bds_16 (unpackF 0x0 1 j)

def node_16 (j : Nat) := dagCheckNodeF m_16 g_16 (select_16 j) 1 (dagTraceF m_16 s_16 3 f_16) l_16 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 1 (dagTraceF m_16 s_16 3 f_16) l_16 0) s_16 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_16_0 : treeBlockF 0 1 node_16 = true := by decide +kernel

theorem join_16_0 : ∀ j, 0 ≤ j → j < 1 → node_16 j = true := (fun _ h₁ h₂ => treeBlockF_at block_16_0 h₁ h₂)

theorem nc_16 : ∀ j, 0 ≤ j → j < 1 → node_16 j = true := join_16_0

theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagF (select := select_16) (hsel := fun j => pickCuts_mem bds_16 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x3333333333333333

def s_17 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]

def g_17 : Nat := 0x113111301133333

def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_16, s_16, 4, g_16)]

theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_15
  · exact lb_16

theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel

theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel

def f_17 : Nat → Nat × Nat := unpackForestF 0xa11225c78d1d34611175c5d4084e1d3c74b1d1c743193c64718fc637111801f 4 10

def l_17 : Nat → Nat → Option Nat := unpackLinksF 0x48241209048241209044621017134564b0582843201 0x2222425c7c68e4d1a22335c5ea0a1393a7a34b3e8e6d0cb2792471c7e28dc223001f 9 4 10 5 5

def select_17 (j : Nat) := pickCuts bds_17 (unpackF 0x40414b427 2 j)

def node_17 (j : Nat) := dagCheckNodeF m_17 g_17 (select_17 j) 18 (dagTraceF m_17 s_17 6 f_17) l_17 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 18 (dagTraceF m_17 s_17 6 f_17) l_17 0) s_17 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_17_0 : treeBlockF 0 16 node_17 = true := by decide +kernel

theorem join_17_0 : ∀ j, 0 ≤ j → j < 16 → node_17 j = true := (fun _ h₁ h₂ => treeBlockF_at block_17_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_17_16 : treeBlockF 16 18 node_17 = true := by decide +kernel

theorem join_17_16 : ∀ j, 0 ≤ j → j < 18 → node_17 j = true := block_join join_17_0 (fun _ h₁ h₂ => treeBlockF_at block_17_16 h₁ h₂)

theorem nc_17 : ∀ j, 0 ≤ j → j < 18 → node_17 j = true := join_17_16

theorem lb_17 : LowerBin m_17 s_17 g_17 7 :=
  lowerDagF (select := select_17) (hsel := fun j => pickCuts_mem bds_17 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xf0f000000000000

def s_18 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]

def g_18 : Nat := 0x107000000000000

def bds_18 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp [bds_18] at hb

theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by
  intro b hb; simp [bds_18] at hb

theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_18] at hb

def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_18 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_18 (j : Nat) := pickCuts bds_18 (unpackF 0x0 1 j)

def node_18 (j : Nat) := dagCheckNodeF m_18 g_18 (select_18 j) 1 (dagTraceF m_18 s_18 3 f_18) l_18 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 1 (dagTraceF m_18 s_18 3 f_18) l_18 0) s_18 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_18_0 : treeBlockF 0 1 node_18 = true := by decide +kernel

theorem join_18_0 : ∀ j, 0 ≤ j → j < 1 → node_18 j = true := (fun _ h₁ h₂ => treeBlockF_at block_18_0 h₁ h₂)

theorem nc_18 : ∀ j, 0 ≤ j → j < 1 → node_18 j = true := join_18_0

theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagF (select := select_18) (hsel := fun j => pickCuts_mem bds_18 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xf0f0f0f0f0f0f0f

def s_19 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]

def g_19 : Nat := 0x107010705070f0f

def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18), (m_11, s_11, 4, g_11)]

theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_18
  · exact lb_11

theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel

theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel

def f_19 : Nat → Nat × Nat := unpackForestF 0xa51225c78d1c34651175c5d4084e1d3c74b1d1c743193c64718fc637151801f 4 10

def l_19 : Nat → Nat → Option Nat := unpackLinksF 0x48241209048241209044621017134564b0582843201 0x22a2425c7c68e0d1aa2335c5ea0a1393a7a34b3e8e6d0cb2792471c7e28dc2a3001f 9 4 10 5 5

def select_19 (j : Nat) := pickCuts bds_19 (unpackF 0x40414b427 2 j)

def node_19 (j : Nat) := dagCheckNodeF m_19 g_19 (select_19 j) 18 (dagTraceF m_19 s_19 6 f_19) l_19 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 18 (dagTraceF m_19 s_19 6 f_19) l_19 0) s_19 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_19_0 : treeBlockF 0 16 node_19 = true := by decide +kernel

theorem join_19_0 : ∀ j, 0 ≤ j → j < 16 → node_19 j = true := (fun _ h₁ h₂ => treeBlockF_at block_19_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_19_16 : treeBlockF 16 18 node_19 = true := by decide +kernel

theorem join_19_16 : ∀ j, 0 ≤ j → j < 18 → node_19 j = true := block_join join_19_0 (fun _ h₁ h₂ => treeBlockF_at block_19_16 h₁ h₂)

theorem nc_19 : ∀ j, 0 ≤ j → j < 18 → node_19 j = true := join_19_16

theorem lb_19 : LowerBin m_19 s_19 g_19 7 :=
  lowerDagF (select := select_19) (hsel := fun j => pickCuts_mem bds_19 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0x444400008888

def s_20 : List Nat := [0x8888, 0x40400000808, 0x4400000088]

def g_20 : Nat := 0x400000888

def bds_20 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp [bds_20] at hb

theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by
  intro b hb; simp [bds_20] at hb

theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_20] at hb

def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_20 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_20 (j : Nat) := pickCuts bds_20 (unpackF 0x0 1 j)

def node_20 (j : Nat) := dagCheckNodeF m_20 g_20 (select_20 j) 1 (dagTraceF m_20 s_20 3 f_20) l_20 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 1 (dagTraceF m_20 s_20 3 f_20) l_20 0) s_20 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_20_0 : treeBlockF 0 1 node_20 = true := by decide +kernel

theorem join_20_0 : ∀ j, 0 ≤ j → j < 1 → node_20 j = true := (fun _ h₁ h₂ => treeBlockF_at block_20_0 h₁ h₂)

theorem nc_20 : ∀ j, 0 ≤ j → j < 1 → node_20 j = true := join_20_0

theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagF (select := select_20) (hsel := fun j => pickCuts_mem bds_20 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xf0f00000000

def s_21 : List Nat := [0x50500000000, 0x30300000000, 0xf00000000]

def g_21 : Nat := 0x10700000000

def bds_21 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp [bds_21] at hb

theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by
  intro b hb; simp [bds_21] at hb

theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_21] at hb

def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_21 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_21 (j : Nat) := pickCuts bds_21 (unpackF 0x0 1 j)

def node_21 (j : Nat) := dagCheckNodeF m_21 g_21 (select_21 j) 1 (dagTraceF m_21 s_21 3 f_21) l_21 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 1 (dagTraceF m_21 s_21 3 f_21) l_21 0) s_21 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_21_0 : treeBlockF 0 1 node_21 = true := by decide +kernel

theorem join_21_0 : ∀ j, 0 ≤ j → j < 1 → node_21 j = true := (fun _ h₁ h₂ => treeBlockF_at block_21_0 h₁ h₂)

theorem nc_21 : ∀ j, 0 ≤ j → j < 1 → node_21 j = true := join_21_0

theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagF (select := select_21) (hsel := fun j => pickCuts_mem bds_21 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xff00000000

def s_22 : List Nat := [0x5500000000, 0x3300000000, 0xf00000000]

def g_22 : Nat := 0x1700000000

def bds_22 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp [bds_22] at hb

theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by
  intro b hb; simp [bds_22] at hb

theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_22] at hb

def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_22 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_22 (j : Nat) := pickCuts bds_22 (unpackF 0x0 1 j)

def node_22 (j : Nat) := dagCheckNodeF m_22 g_22 (select_22 j) 1 (dagTraceF m_22 s_22 3 f_22) l_22 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 1 (dagTraceF m_22 s_22 3 f_22) l_22 0) s_22 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_22_0 : treeBlockF 0 1 node_22 = true := by decide +kernel

theorem join_22_0 : ∀ j, 0 ≤ j → j < 1 → node_22 j = true := (fun _ h₁ h₂ => treeBlockF_at block_22_0 h₁ h₂)

theorem nc_22 : ∀ j, 0 ≤ j → j < 1 → node_22 j = true := join_22_0

theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagF (select := select_22) (hsel := fun j => pickCuts_mem bds_22 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xa0500000a050

def s_23 : List Nat := [0x5000000050, 0x201000002010, 0xa050]

def g_23 : Nat := 0x1000002050

def bds_23 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp [bds_23] at hb

theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by
  intro b hb; simp [bds_23] at hb

theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_23] at hb

def f_23 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_23 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_23 (j : Nat) := pickCuts bds_23 (unpackF 0x0 1 j)

def node_23 (j : Nat) := dagCheckNodeF m_23 g_23 (select_23 j) 1 (dagTraceF m_23 s_23 3 f_23) l_23 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 1 (dagTraceF m_23 s_23 3 f_23) l_23 0) s_23 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_23_0 : treeBlockF 0 1 node_23 = true := by decide +kernel

theorem join_23_0 : ∀ j, 0 ≤ j → j < 1 → node_23 j = true := (fun _ h₁ h₂ => treeBlockF_at block_23_0 h₁ h₂)

theorem nc_23 : ∀ j, 0 ≤ j → j < 1 → node_23 j = true := join_23_0

theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagF (select := select_23) (hsel := fun j => pickCuts_mem bds_23 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xffff0000ffff

def s_24 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]

def g_24 : Nat := 0x111700003fff

def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20), (m_21, s_21, 4, g_21), (m_22, s_22, 4, g_22), (m_5, s_5, 5, g_5), (m_13, s_13, 4, g_13), (m_23, s_23, 4, g_23)]

theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_21
  · exact lb_22
  · exact lb_5
  · exact lb_13
  · exact lb_23

theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_24 : Nat → Nat × Nat := unpackForestF 0x4e0d2506920347c223cd41b088d3505a281c8e0e2707035381a1b144d48c625e2d2f15144a28c495e20af0e578728c335d19a28ad3c568e1b5e0a2f02d3c16860a43051d828cc1286093b04998248c109e084d0422820fc106e001f 6 11

def l_24 : Nat → Nat → Option Nat := unpackLinksF 0xd8360d8351d0731c8711c4310c42f2b4ac1b02c0a8a91a4290a4281a0280a0280a028098a06789d1705a2645815893344910404f107801 0x2a2895034a422520d2806939419420cc9527089335090aa4a11246a11c50502e9e135e4a3123868a8c24e2006af8347a28ba919c4bcda5e6a28b251982bcb95e58af2a51946ba7b4d4da2a4d3d168e835e3e2f1cd3cd68662432d1d948cc9286413b1c998c48c509e204d0c22840fc106e001f 10 4 11 6 5

def select_24 (j : Nat) := pickCuts bds_24 (unpackF 0x104124208100410100020104104007fffffdffffbff3c70cf3ce 6 j)

def node_24 (j : Nat) := dagCheckNodeF m_24 g_24 (select_24 j) 43 (dagTraceF m_24 s_24 7 f_24) l_24 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 43 (dagTraceF m_24 s_24 7 f_24) l_24 0) s_24 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_24_0 : treeBlockF 0 16 node_24 = true := by decide +kernel

theorem join_24_0 : ∀ j, 0 ≤ j → j < 16 → node_24 j = true := (fun _ h₁ h₂ => treeBlockF_at block_24_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_24_16 : treeBlockF 16 32 node_24 = true := by decide +kernel

theorem join_24_16 : ∀ j, 0 ≤ j → j < 32 → node_24 j = true := block_join join_24_0 (fun _ h₁ h₂ => treeBlockF_at block_24_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_24_32 : treeBlockF 32 43 node_24 = true := by decide +kernel

theorem join_24_32 : ∀ j, 0 ≤ j → j < 43 → node_24 j = true := block_join join_24_16 (fun _ h₁ h₂ => treeBlockF_at block_24_32 h₁ h₂)

theorem nc_24 : ∀ j, 0 ≤ j → j < 43 → node_24 j = true := join_24_32

theorem lb_24 : LowerBin m_24 s_24 g_24 8 :=
  lowerDagF (select := select_24) (hsel := fun j => pickCuts_mem bds_24 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0x5050a0a0

def s_25 : List Nat := [0xa0a0, 0x10102020, 0x5000a0]

def g_25 : Nat := 0x1020a0

def bds_25 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp [bds_25] at hb

theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by
  intro b hb; simp [bds_25] at hb

theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_25] at hb

def f_25 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_25 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_25 (j : Nat) := pickCuts bds_25 (unpackF 0x0 1 j)

def node_25 (j : Nat) := dagCheckNodeF m_25 g_25 (select_25 j) 1 (dagTraceF m_25 s_25 3 f_25) l_25 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 1 (dagTraceF m_25 s_25 3 f_25) l_25 0) s_25 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_25_0 : treeBlockF 0 1 node_25 = true := by decide +kernel

theorem join_25_0 : ∀ j, 0 ≤ j → j < 1 → node_25 j = true := (fun _ h₁ h₂ => treeBlockF_at block_25_0 h₁ h₂)

theorem nc_25 : ∀ j, 0 ≤ j → j < 1 → node_25 j = true := join_25_0

theorem lb_25 : LowerBin m_25 s_25 g_25 4 :=
  lowerDagF (select := select_25) (hsel := fun j => pickCuts_mem bds_25 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x33330000

def s_26 : List Nat := [0x11110000, 0x3030000, 0x330000]

def g_26 : Nat := 0x1130000

def bds_26 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp [bds_26] at hb

theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by
  intro b hb; simp [bds_26] at hb

theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_26] at hb

def f_26 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_26 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_26 (j : Nat) := pickCuts bds_26 (unpackF 0x0 1 j)

def node_26 (j : Nat) := dagCheckNodeF m_26 g_26 (select_26 j) 1 (dagTraceF m_26 s_26 3 f_26) l_26 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 1 (dagTraceF m_26 s_26 3 f_26) l_26 0) s_26 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_26_0 : treeBlockF 0 1 node_26 = true := by decide +kernel

theorem join_26_0 : ∀ j, 0 ≤ j → j < 1 → node_26 j = true := (fun _ h₁ h₂ => treeBlockF_at block_26_0 h₁ h₂)

theorem nc_26 : ∀ j, 0 ≤ j → j < 1 → node_26 j = true := join_26_0

theorem lb_26 : LowerBin m_26 s_26 g_26 4 :=
  lowerDagF (select := select_26) (hsel := fun j => pickCuts_mem bds_26 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xff0000

def s_27 : List Nat := [0x550000, 0x330000, 0xf0000]

def g_27 : Nat := 0x170000

def bds_27 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp [bds_27] at hb

theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by
  intro b hb; simp [bds_27] at hb

theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_27] at hb

def f_27 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_27 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_27 (j : Nat) := pickCuts bds_27 (unpackF 0x0 1 j)

def node_27 (j : Nat) := dagCheckNodeF m_27 g_27 (select_27 j) 1 (dagTraceF m_27 s_27 3 f_27) l_27 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 1 (dagTraceF m_27 s_27 3 f_27) l_27 0) s_27 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_27_0 : treeBlockF 0 1 node_27 = true := by decide +kernel

theorem join_27_0 : ∀ j, 0 ≤ j → j < 1 → node_27 j = true := (fun _ h₁ h₂ => treeBlockF_at block_27_0 h₁ h₂)

theorem nc_27 : ∀ j, 0 ≤ j → j < 1 → node_27 j = true := join_27_0

theorem lb_27 : LowerBin m_27 s_27 g_27 4 :=
  lowerDagF (select := select_27) (hsel := fun j => pickCuts_mem bds_27 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0x88448844

def s_28 : List Nat := [0x440044, 0x8040804, 0x8844]

def g_28 : Nat := 0x40844

def bds_28 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp [bds_28] at hb

theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by
  intro b hb; simp [bds_28] at hb

theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_28] at hb

def f_28 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_28 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_28 (j : Nat) := pickCuts bds_28 (unpackF 0x0 1 j)

def node_28 (j : Nat) := dagCheckNodeF m_28 g_28 (select_28 j) 1 (dagTraceF m_28 s_28 3 f_28) l_28 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 1 (dagTraceF m_28 s_28 3 f_28) l_28 0) s_28 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_28_0 : treeBlockF 0 1 node_28 = true := by decide +kernel

theorem join_28_0 : ∀ j, 0 ≤ j → j < 1 → node_28 j = true := (fun _ h₁ h₂ => treeBlockF_at block_28_0 h₁ h₂)

theorem nc_28 : ∀ j, 0 ≤ j → j < 1 → node_28 j = true := join_28_0

theorem lb_28 : LowerBin m_28 s_28 g_28 4 :=
  lowerDagF (select := select_28) (hsel := fun j => pickCuts_mem bds_28 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xffffffff

def s_29 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]

def g_29 : Nat := 0x5173fff

def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 4, g_25), (m_26, s_26, 4, g_26), (m_27, s_27, 4, g_27), (m_6, s_6, 5, g_6), (m_12, s_12, 4, g_12), (m_28, s_28, 4, g_28)]

theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_25
  · exact lb_26
  · exact lb_27
  · exact lb_6
  · exact lb_12
  · exact lb_28

theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_29 : Nat → Nat × Nat := unpackForestF 0x4e8d25049202489a23cd05b068d25061a81e8d4d8a26a4c34941a094d048635e2d2f14d44a26c495e249b1057872bc325d19228a93c548e1a5e09af02d0c149e0a43051f828cc1286093304958248c109e084d0422820bc104e001f 6 11

def l_29 : Nat → Nat → Option Nat := unpackLinksF 0xd8360d8351d0731c8711c06e2b82e0b82c2b02c0a8a91a4281a0280a0280a0280a028098a42799d1705a2609715853344910404f107801 0x2a0495234a41a5209280493a509da24c0926683284190a24a0d244a11b508528c48d540ba784d8628c0931a2a2f9287812ba091c6bcda5e69a8b24d982bcb93658af2a57944ba7a4d4d22a493d148e825e3daf1cd0cd49e62432d1f948cc928641331c958c48c509e204d0c22840bc104e001f 10 4 11 6 5

def select_29 (j : Nat) := pickCuts bds_29 (unpackF 0x208104124100410020100104104007fffffdfffffef3c70cf3ce 6 j)

def node_29 (j : Nat) := dagCheckNodeF m_29 g_29 (select_29 j) 43 (dagTraceF m_29 s_29 7 f_29) l_29 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 43 (dagTraceF m_29 s_29 7 f_29) l_29 0) s_29 7 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_29_0 : treeBlockF 0 16 node_29 = true := by decide +kernel

theorem join_29_0 : ∀ j, 0 ≤ j → j < 16 → node_29 j = true := (fun _ h₁ h₂ => treeBlockF_at block_29_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_29_16 : treeBlockF 16 32 node_29 = true := by decide +kernel

theorem join_29_16 : ∀ j, 0 ≤ j → j < 32 → node_29 j = true := block_join join_29_0 (fun _ h₁ h₂ => treeBlockF_at block_29_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_29_32 : treeBlockF 32 43 node_29 = true := by decide +kernel

theorem join_29_32 : ∀ j, 0 ≤ j → j < 43 → node_29 j = true := block_join join_29_16 (fun _ h₁ h₂ => treeBlockF_at block_29_32 h₁ h₂)

theorem nc_29 : ∀ j, 0 ≤ j → j < 43 → node_29 j = true := join_29_32

theorem lb_29 : LowerBin m_29 s_29 g_29 8 :=
  lowerDagF (select := select_29) (hsel := fun j => pickCuts_mem bds_29 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff000000000000

def s_30 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]

def g_30 : Nat := 0x17000000000000

def bds_30 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp [bds_30] at hb

theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by
  intro b hb; simp [bds_30] at hb

theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_30] at hb

def f_30 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_30 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_30 (j : Nat) := pickCuts bds_30 (unpackF 0x0 1 j)

def node_30 (j : Nat) := dagCheckNodeF m_30 g_30 (select_30 j) 1 (dagTraceF m_30 s_30 3 f_30) l_30 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 1 (dagTraceF m_30 s_30 3 f_30) l_30 0) s_30 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_30_0 : treeBlockF 0 1 node_30 = true := by decide +kernel

theorem join_30_0 : ∀ j, 0 ≤ j → j < 1 → node_30 j = true := (fun _ h₁ h₂ => treeBlockF_at block_30_0 h₁ h₂)

theorem nc_30 : ∀ j, 0 ≤ j → j < 1 → node_30 j = true := join_30_0

theorem lb_30 : LowerBin m_30 s_30 g_30 4 :=
  lowerDagF (select := select_30) (hsel := fun j => pickCuts_mem bds_30 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xffff000000000000

def s_31 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]

def g_31 : Nat := 0x117000000000000

def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_15, s_15, 4, g_15), (m_18, s_18, 4, g_18), (m_30, s_30, 4, g_30)]

theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_15
  · exact lb_18
  · exact lb_30

theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def f_31 : Nat → Nat × Nat := unpackForestF 0x1dd0360c4f408858d901918283c409874a4e149b41327c6064ba116422a9c5508a0c9341248240f88170f421c6235086270c42185c2908519094212642138421083e106418cc29985230866108c209800f 5 10

def l_31 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c2384708e11c2384708e11c230c608c114620c408630c210c1182104200bf17c2f81e8bd0782ec5d0b91720e05c03715f09e0fc1781f01e00b001 0xaa40aa40ab40a418a1409930a1409530a3409c2c994095309a409630903c8c4c81417531892969216041503184294021834172327d3e69325c41382178192411774272426d4e69424c31342164191c1163415e4149323122583e4032542e242253424e3149422d22444e40423c2e1c223a42363231422d32284e2442203e1c321a33153311230c3308230413000f 11 4 10 6 5

def select_31 (j : Nat) := pickCuts bds_31 (unpackF 0x303056000060053080ac009c30409a560201fffffff 4 j)

def node_31 (j : Nat) := dagCheckNodeF m_31 g_31 (select_31 j) 43 (dagTraceF m_31 s_31 6 f_31) l_31 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 43 (dagTraceF m_31 s_31 6 f_31) l_31 0) s_31 6 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_31_0 : treeBlockF 0 16 node_31 = true := by decide +kernel

theorem join_31_0 : ∀ j, 0 ≤ j → j < 16 → node_31 j = true := (fun _ h₁ h₂ => treeBlockF_at block_31_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_31_16 : treeBlockF 16 32 node_31 = true := by decide +kernel

theorem join_31_16 : ∀ j, 0 ≤ j → j < 32 → node_31 j = true := block_join join_31_0 (fun _ h₁ h₂ => treeBlockF_at block_31_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_31_32 : treeBlockF 32 43 node_31 = true := by decide +kernel

theorem join_31_32 : ∀ j, 0 ≤ j → j < 43 → node_31 j = true := block_join join_31_16 (fun _ h₁ h₂ => treeBlockF_at block_31_32 h₁ h₂)

theorem nc_31 : ∀ j, 0 ≤ j → j < 43 → node_31 j = true := join_31_32

theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagF (select := select_31) (hsel := fun j => pickCuts_mem bds_31 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xffffffff00000000

def s_32 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]

def g_32 : Nat := 0x117111700000000

def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31)]

theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_31

theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_32 : Nat → Nat × Nat := fun _ => (0, 0)

def l_32 : Nat → Nat → Option Nat := fun _ _ => none

def select_32 (j : Nat) := pickCuts bds_32 (unpackF 0x0 1 j)

def node_32 (j : Nat) := dagCheckNodeF m_32 g_32 (select_32 j) 0 (dagTraceF m_32 s_32 7 f_32) l_32 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 7 f_32) l_32 0) s_32 7 = true := by decide +kernel

theorem nc_32 : ∀ j, 0 ≤ j → j < 0 → node_32 j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_32 : LowerBin m_32 s_32 g_32 8 :=
  lowerDagF (select := select_32) (hsel := fun j => pickCuts_mem bds_32 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xffff0000ffff0000

def s_33 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]

def g_33 : Nat := 0x117000005170000

def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31)]

theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_31

theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_33 : Nat → Nat × Nat := fun _ => (0, 0)

def l_33 : Nat → Nat → Option Nat := fun _ _ => none

def select_33 (j : Nat) := pickCuts bds_33 (unpackF 0x0 1 j)

def node_33 (j : Nat) := dagCheckNodeF m_33 g_33 (select_33 j) 0 (dagTraceF m_33 s_33 7 f_33) l_33 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 7 f_33) l_33 0) s_33 7 = true := by decide +kernel

theorem nc_33 : ∀ j, 0 ≤ j → j < 0 → node_33 j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_33 : LowerBin m_33 s_33 g_33 8 :=
  lowerDagF (select := select_33) (hsel := fun j => pickCuts_mem bds_33 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x222200008888

def s_34 : List Nat := [0x8888, 0x20200000808, 0x2200000088]

def g_34 : Nat := 0x200000888

def bds_34 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp [bds_34] at hb

theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by
  intro b hb; simp [bds_34] at hb

theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_34] at hb

def f_34 : Nat → Nat × Nat := unpackForestF 0x7 1 3

def l_34 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2

def select_34 (j : Nat) := pickCuts bds_34 (unpackF 0x0 1 j)

def node_34 (j : Nat) := dagCheckNodeF m_34 g_34 (select_34 j) 1 (dagTraceF m_34 s_34 3 f_34) l_34 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 1 (dagTraceF m_34 s_34 3 f_34) l_34 0) s_34 3 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_34_0 : treeBlockF 0 1 node_34 = true := by decide +kernel

theorem join_34_0 : ∀ j, 0 ≤ j → j < 1 → node_34 j = true := (fun _ h₁ h₂ => treeBlockF_at block_34_0 h₁ h₂)

theorem nc_34 : ∀ j, 0 ≤ j → j < 1 → node_34 j = true := join_34_0

theorem lb_34 : LowerBin m_34 s_34 g_34 4 :=
  lowerDagF (select := select_34) (hsel := fun j => pickCuts_mem bds_34 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xaaaa0000aaaa

def s_35 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]

def g_35 : Nat := 0x200002aaa

def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 4, g_34)]

theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_34

theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_35 : Nat → Nat × Nat := unpackForestF 0x2e9c5d34b25164929a24e389c6924f249a42447c98f911ca6394464687d00e9e1d30308860b0c120e401c7038c0422083c106818fc31d86370c6614fc29d85370a6614bc29585270a4610fc21d842f0856109c211841f0836105c209800f 5 10

def l_35 : Nat → Nat → Option Nat := unpackLinksF 0x1a83506a0d41a83506a0d41a83506a0d41a83506a0d41a83506a0d41a83506a0d41a83506a0cc588b00de1b4558aa0d219c528a40c618c118230460806e8dd03a0686b8c1b001 0xc538c134bd28b924b630b744b238ae34a93ca534a130a2449e4c9a44954c91448d208e348b40853c81307c44782c742472406e386a306444603c5c345a3f563b52374e33493f453b41373d33392f352b31272d23283f243b202f1c2b18271423101f0c1b08170413000f 11 5 10 6 6

def select_35 (j : Nat) := pickCuts bds_35 (unpackF 0x67 1 j)

def node_35 (j : Nat) := dagCheckNodeF m_35 g_35 (select_35 j) 50 (dagTraceF m_35 s_35 5 f_35) l_35 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 50 (dagTraceF m_35 s_35 5 f_35) l_35 0) s_35 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_35_0 : treeBlockF 0 16 node_35 = true := by decide +kernel

theorem join_35_0 : ∀ j, 0 ≤ j → j < 16 → node_35 j = true := (fun _ h₁ h₂ => treeBlockF_at block_35_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_35_16 : treeBlockF 16 32 node_35 = true := by decide +kernel

theorem join_35_16 : ∀ j, 0 ≤ j → j < 32 → node_35 j = true := block_join join_35_0 (fun _ h₁ h₂ => treeBlockF_at block_35_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_35_32 : treeBlockF 32 48 node_35 = true := by decide +kernel

theorem join_35_32 : ∀ j, 0 ≤ j → j < 48 → node_35 j = true := block_join join_35_16 (fun _ h₁ h₂ => treeBlockF_at block_35_32 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_35_48 : treeBlockF 48 50 node_35 = true := by decide +kernel

theorem join_35_48 : ∀ j, 0 ≤ j → j < 50 → node_35 j = true := block_join join_35_32 (fun _ h₁ h₂ => treeBlockF_at block_35_48 h₁ h₂)

theorem nc_35 : ∀ j, 0 ≤ j → j < 50 → node_35 j = true := join_35_48

theorem lb_35 : LowerBin m_35 s_35 g_35 6 :=
  lowerDagF (select := select_35) (hsel := fun j => pickCuts_mem bds_35 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xaaaaaaaaaaaaaaaa

def s_36 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]

def g_36 : Nat := 0x2000200022aaa

def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 6, g_35)]

theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_35

theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel

def f_36 : Nat → Nat × Nat := fun _ => (0, 0)

def l_36 : Nat → Nat → Option Nat := fun _ _ => none

def select_36 (j : Nat) := pickCuts bds_36 (unpackF 0x0 1 j)

def node_36 (j : Nat) := dagCheckNodeF m_36 g_36 (select_36 j) 0 (dagTraceF m_36 s_36 6 f_36) l_36 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 0 (dagTraceF m_36 s_36 6 f_36) l_36 0) s_36 6 = true := by decide +kernel

theorem nc_36 : ∀ j, 0 ≤ j → j < 0 → node_36 j = true := fun _ _ h => absurd h (Nat.not_lt_zero _)

theorem lb_36 : LowerBin m_36 s_36 g_36 7 :=
  lowerDagF (select := select_36) (hsel := fun j => pickCuts_mem bds_36 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xff00ff00ff00ff

def s_37 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]

def g_37 : Nat := 0x170017001700ff

def bds_37 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp [bds_37] at hb

theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by
  intro b hb; simp [bds_37] at hb

theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_37] at hb

def f_37 : Nat → Nat × Nat := unpackForestF 0x9d1f47915c2f4b52b4a52749517859148511401f 4 6

def l_37 : Nat → Nat → Option Nat := unpackLinksF 0xa0a0a0a0a0929082807269616060360d01 0xf9394fd354ed364c731cbf6b59b6257759557919348911401f 8 3 6 4 4

def select_37 (j : Nat) := pickCuts bds_37 (unpackF 0x0 1 j)

def node_37 (j : Nat) := dagCheckNodeF m_37 g_37 (select_37 j) 16 (dagTraceF m_37 s_37 5 f_37) l_37 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 16 (dagTraceF m_37 s_37 5 f_37) l_37 0) s_37 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_37_0 : treeBlockF 0 16 node_37 = true := by decide +kernel

theorem join_37_0 : ∀ j, 0 ≤ j → j < 16 → node_37 j = true := (fun _ h₁ h₂ => treeBlockF_at block_37_0 h₁ h₂)

theorem nc_37 : ∀ j, 0 ≤ j → j < 16 → node_37 j = true := join_37_0

theorem lb_37 : LowerBin m_37 s_37 g_37 6 :=
  lowerDagF (select := select_37) (hsel := fun j => pickCuts_mem bds_37 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xf0f0f0f0f0f0f0f0

def s_38 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]

def g_38 : Nat := 0x101010001030f0

def bds_38 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp [bds_38] at hb

theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by
  intro b hb; simp [bds_38] at hb

theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_38] at hb

def f_38 : Nat → Nat × Nat := unpackForestF 0x749e8307a0901f 1 10

def l_38 : Nat → Nat → Option Nat := unpackLinksF 0xa28a28301 0x13497a0a07882401f 6 3 10 3 4

def select_38 (j : Nat) := pickCuts bds_38 (unpackF 0x0 1 j)

def node_38 (j : Nat) := dagCheckNodeF m_38 g_38 (select_38 j) 5 (dagTraceF m_38 s_38 5 f_38) l_38 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 5 (dagTraceF m_38 s_38 5 f_38) l_38 0) s_38 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_38_0 : treeBlockF 0 5 node_38 = true := by decide +kernel

theorem join_38_0 : ∀ j, 0 ≤ j → j < 5 → node_38 j = true := (fun _ h₁ h₂ => treeBlockF_at block_38_0 h₁ h₂)

theorem nc_38 : ∀ j, 0 ≤ j → j < 5 → node_38 j = true := join_38_0

theorem lb_38 : LowerBin m_38 s_38 g_38 6 :=
  lowerDagF (select := select_38) (hsel := fun j => pickCuts_mem bds_38 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xcccccccccccccccc

def s_39 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]

def g_39 : Nat := 0x4000404040ccc

def bds_39 : List (Nat × List Nat × Nat × Nat) := []

theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp [bds_39] at hb

theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by
  intro b hb; simp [bds_39] at hb

theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp [bds_39] at hb

def f_39 : Nat → Nat × Nat := unpackForestF 0x749e830660881f 1 10

def l_39 : Nat → Nat → Option Nat := unpackLinksF 0xa28a28301 0x13497a0a06482201f 6 3 10 3 4

def select_39 (j : Nat) := pickCuts bds_39 (unpackF 0x0 1 j)

def node_39 (j : Nat) := dagCheckNodeF m_39 g_39 (select_39 j) 5 (dagTraceF m_39 s_39 5 f_39) l_39 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 5 (dagTraceF m_39 s_39 5 f_39) l_39 0) s_39 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_39_0 : treeBlockF 0 5 node_39 = true := by decide +kernel

theorem join_39_0 : ∀ j, 0 ≤ j → j < 5 → node_39 j = true := (fun _ h₁ h₂ => treeBlockF_at block_39_0 h₁ h₂)

theorem nc_39 : ∀ j, 0 ≤ j → j < 5 → node_39 j = true := join_39_0

theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagF (select := select_39) (hsel := fun j => pickCuts_mem bds_39 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def g_40 : Nat := 0x117111705173fff

def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 8, g_10), (m_14, s_14, 7, g_14), (m_17, s_17, 7, g_17), (m_19, s_19, 7, g_19), (m_24, s_24, 8, g_24), (m_29, s_29, 8, g_29), (m_32, s_32, 8, g_32), (m_33, s_33, 8, g_33), (m_36, s_36, 7, g_36), (m_37, s_37, 6, g_37), (m_38, s_38, 6, g_38), (m_39, s_39, 6, g_39)]

theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_10
  · exact lb_14
  · exact lb_17
  · exact lb_19
  · exact lb_24
  · exact lb_29
  · exact lb_32
  · exact lb_33
  · exact lb_36
  · exact lb_37
  · exact lb_38
  · exact lb_39

theorem sub_40 : ∀ b ∈ bds_40, fullMask &&& b.1 = b.1 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def f_40 : Nat → Nat × Nat := unpackForestF 0x47b648b6c90a911d1b434c64686a8bb1a14db229354444ca871f909bf1f4643d6c87ad38f2b41db653b6c874d50e92a1cc5e3968872910e1361ba46374886cd54d62b1a369338ca67190c9ab1935431afc631f8c6391846e2f8fc5edc8b93216b442d488591b8aeb41536c2a6b8509909d221336f266c648d9491b211b55236a8455a4873f10e72216fc415b87eb90fb7e1d4c838d50712a0dd6e1a8d03316065ac0ba64164a8295bc52b189b59134aa24d24492288c59114aa20d78411a87a450e69c1c8d436b006a5d0c6de188ec311b862350b8b216d642da785b4b0b68e16d0c2a2f8545b0a8ae1514c292f0524e098de12dbc25b184b4b0969212d1c2237844630849c0edbc1db183b51068de0d18c192f0324e05ade0b58c15b782b5f056bc0ad5c15a90256f04ac6089780eb781d63038a4055bc0ab18125e0249c0317c062980b5f016a602d3c05a580b47016860297c052980a4f014960291c052180a3f01476028dc05198003f 8 11

def l_40 : Nat → Nat → Option Nat := unpackLinksF 0x3741ba0dd06e83741ba0dd06e83741b81db0ed836c1b60da0ed03681b40da06d03643b20d906c83641b20d906c83603b00d806c03601b00d806c03601ae1d706b835c1ae0d706b835c1ae0d706b83583aa1d506a83541aa0d40ea03501a80d406a034c3a60d3069834c1a60d3069834c1a60d20e887441a20d00e7873c19e0ce0e687303942c90e4832418c3c50e207101880c40610b0057e1bd15d0edc7683b215886c035a3a9252928874219f14e8a6c53419814a8e541262911478a3c1164872420e0470017e13f01f04f42790bb89d06e807213809c00dc2683311970cac652227112888673d31b98c0e5a3292129078e3631720990064001 0x4c238986c92ed9259224ac54956d1291924daa49364928d122d9241aa2aa455a474d6955c12d432628a4df0898e0d3147a658e4731a8d63a3f46b7e8c8c91517a2db24534e89ad110d961db24256e866a90a952122f41b4482489029b1f92e3ea4c8048cfe911f9aabec567c6d2eed25cda2bdc657a8c8ecd29d1a43ac5a728acf2d59e1aa3bd7e768fceb1c9d23739c7e726e4e2991b926383446f488dd1b9b6b43425d6c6d8d6d719d36b5264684bcce9b9a5223436f676c6ccd9595b230b5d5e6b8c0db575b2b2355636a8c55a57daf2e35661cfcc19c97dbf2f56e5dae4b8df96d322c25c5a6a8b295162b72bc685249aad16155ac28a4d544c8a49394d2a28a4e52adea358d41aca7a552347e388ec651b8b2334e6929a914891f8da3b1846e2a8cd322ca5a553249e5a92ca92393a434a6bc6297cb12d94a57264a6928d51e2f1ea6f394c6909151da71e26f384c68c8d516b01da6f374c6889750db79d26f364c63a8f5091da0a374046a7f164f9ac9eb4f3c69676d1ce9a19cc5f388b66f15cda299aa5e3449c671bcc9b798b63306965ed24b9a38eb412d8de5918cad271536f296c650d44952e93c6f268c64a978912711d6f22ac642dbc81af8fb5e1e6ae3ad4872b78dd631a4bc335bc62b18bc521349a2d5bc56b18a25e1349c2517c46298835f0f6a61cd3c35a5863470b6861497c25298424f074960c91c15218223f03476048dc05198003f 13 5 11 8 6

def select_40 (j : Nat) := pickCuts bds_40 (unpackF 0x2031033035ff5ff5010ff1000ffa1b4f74026274ff1ff00e0ff90f5076090080ff1061ff509208b19e19109f100ff6270f740f2ff3f7c272ff3ff608f9c0040ff10a1ffa05204725905e25f201050ffa1b0fb80f2f73ffc1b2f73ffa04f6c6ff6ffffffffaffaffffffffbff7ff7ff1fd3ff5fffffffffffffffffbff7ff3fffff8ff4ff1ffcffcffcff3ffafffffbffffffff0ff5ff5ff2ff7ff7ff9ffdff7fffff6fffff3ff7fffffffffff0ff9ff9ff2ffbffbff5ffdfffffbff0ff9ff0ff5ff9ff5ff1ffdff3ff0ffbff1ff3ff9ff7ff1ff3ff5ff0f1 12 j)

def node_40 (j : Nat) := dagCheckNodeF fullMask g_40 (select_40 j) 153 (dagTraceF fullMask rootStock 10 f_40) l_40 j

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem rc_40 : dagCheckRootsF fullMask g_40 bds_40 (dagRefF 153 (dagTraceF fullMask rootStock 10 f_40) l_40 0) rootStock 10 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_0 : treeBlockF 0 16 node_40 = true := by decide +kernel

theorem join_40_0 : ∀ j, 0 ≤ j → j < 16 → node_40 j = true := (fun _ h₁ h₂ => treeBlockF_at block_40_0 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_16 : treeBlockF 16 32 node_40 = true := by decide +kernel

theorem join_40_16 : ∀ j, 0 ≤ j → j < 32 → node_40 j = true := block_join join_40_0 (fun _ h₁ h₂ => treeBlockF_at block_40_16 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_32 : treeBlockF 32 48 node_40 = true := by decide +kernel

theorem join_40_32 : ∀ j, 0 ≤ j → j < 48 → node_40 j = true := block_join join_40_16 (fun _ h₁ h₂ => treeBlockF_at block_40_32 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_48 : treeBlockF 48 64 node_40 = true := by decide +kernel

theorem join_40_48 : ∀ j, 0 ≤ j → j < 64 → node_40 j = true := block_join join_40_32 (fun _ h₁ h₂ => treeBlockF_at block_40_48 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_64 : treeBlockF 64 80 node_40 = true := by decide +kernel

theorem join_40_64 : ∀ j, 0 ≤ j → j < 80 → node_40 j = true := block_join join_40_48 (fun _ h₁ h₂ => treeBlockF_at block_40_64 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_80 : treeBlockF 80 96 node_40 = true := by decide +kernel

theorem join_40_80 : ∀ j, 0 ≤ j → j < 96 → node_40 j = true := block_join join_40_64 (fun _ h₁ h₂ => treeBlockF_at block_40_80 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_96 : treeBlockF 96 112 node_40 = true := by decide +kernel

theorem join_40_96 : ∀ j, 0 ≤ j → j < 112 → node_40 j = true := block_join join_40_80 (fun _ h₁ h₂ => treeBlockF_at block_40_96 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_112 : treeBlockF 112 128 node_40 = true := by decide +kernel

theorem join_40_112 : ∀ j, 0 ≤ j → j < 128 → node_40 j = true := block_join join_40_96 (fun _ h₁ h₂ => treeBlockF_at block_40_112 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_128 : treeBlockF 128 144 node_40 = true := by decide +kernel

theorem join_40_128 : ∀ j, 0 ≤ j → j < 144 → node_40 j = true := block_join join_40_112 (fun _ h₁ h₂ => treeBlockF_at block_40_128 h₁ h₂)

set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
theorem block_40_144 : treeBlockF 144 153 node_40 = true := by decide +kernel

theorem join_40_144 : ∀ j, 0 ≤ j → j < 153 → node_40 j = true := block_join join_40_128 (fun _ h₁ h₂ => treeBlockF_at block_40_144 h₁ h₂)

theorem nc_40 : ∀ j, 0 ≤ j → j < 153 → node_40 j = true := join_40_144

theorem lb_40 : LowerBin fullMask rootStock g_40 11 :=
  lowerDagF (select := select_40) (hsel := fun j => pickCuts_mem bds_40 _) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

theorem target_lower : LowerBin fullMask rootStock (canon fullMask 18368193764639948800) 11 := lb_40
end PEqualNP.Outside.L_meta_45452.Free

namespace PEqualNP.Outside.L_meta_45452
def bigNat_0 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff7ffefffdff) 64) 0xfb6eefffdbb77ffe) 64) 0xdfffb6fffddb7ff7) 64) 0x76db5afffbffebff) 64) 0xefffbffeafffb7ff) 64) 0xd7ffdfff7ffddfff) 64) 0x0)
def bigNat_1 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x8 64) 0x8924a50004001400) 64) 0x1000400150004800) 64) 0x2800200080022000) 64) 0x0)
def bigNat_2 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x20 64) 0x40008001000200) 64) 0x491100024488001) 64) 0x2000490002248000) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x0)
def bigNat_3 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3fff0000 64) 0x38000001dfff87) 64) 0xffe1bfff06c00000) 64) 0x8242843412f210e0) 64) 0x4bc12f0842c423e4) 64) 0x21c08f823e709500) 64) 0x5) 64) 0x6b0ad615aceb5856) 64) 0xb122e2cd8897575c) 64) 0x15b7066db81b2d60) 64) 0x61b1a0003ffe800) 64) 0xfffbffe200037ff) 64) 0xd0001fff7ffdc000) 64) 0xaaaaaaaaaaaaaaaa)
def bigNat_4 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1fff80000000 64) 0x383fff00c000007) 64) 0xffec3fff70c0000c) 64) 0x108088dc21522370) 64) 0x8582572090cc48a4) 64) 0x4ae12304ce312780) 64) 0xa) 64) 0xa5954b7a96352caa) 64) 0x5a4e2d6ac1312a2e) 64) 0x5aabb0b4ddc354b0) 64) 0x70c342fff8000bff) 64) 0xe0003ffe80003000) 64) 0x17ffc0007ffddfff) 64) 0xcccccccccccccccc)
def bigNat_5 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0xfffc00000007ffe 64) 0x18000000e01fffb0) 64) 0x3fff760000c0) 64) 0x2416122448924cb1) 64) 0x32c48a0927409124) 64) 0x9562558914525980) 64) 0x10) 64) 0xd6b9ad235a46b5cd) 64) 0x686441b353a24db6) 64) 0xc34d903aedd81ad7) 64) 0xd8580000000bff) 64) 0xefff8000afff8000) 64) 0x17ffdfff0001dfff) 64) 0xf0f0f0f0f0f0f0f0)
def bigNat_6 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff 64) 0xe000000000007ffe) 64) 0xc003fff6001fffb7) 64) 0xffed800000000155) 64) 0x16a3788de089c2) 64) 0x27089c2a3b8d1dc1) 64) 0x1984661198647e00) 64) 0x1f) 64) 0x18a6314c6298c5f1) 64) 0x8b088e3c5a0471c6) 64) 0xdc71b6c30c406317) 64) 0x76005afffbffe000) 64) 0xafffb7ff) 64) 0xc00000000001dfff) 64) 0xff00ff00ff00ff00)
def bigNat_7 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff 64) 0xefffdfffbfff0000) 64) 0x3fff6edc00000) 64) 0x19d) 64) 0xb6c03c40f100f103) 64) 0xc40f1023dc09ee01) 64) 0xee07b81ee007a000) 64) 0x1c) 64) 0x1f383e707ce0f901) 64) 0xf000083f9bb701f8) 64) 0x807e0203f08903e7) 64) 0x76db000000000000) 64) 0xafffb7ff) 64) 0xd7ffdfff7ffc0000) 64) 0xffff0000ffff0000)
def bigNat_8 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff 64) 0xefffdfffbfff7ffe) 64) 0xdbb8000000000000) 64) 0x1d9) 64) 0xb6d43f80fe00fe03) 64) 0xf80fe003e001f001) 64) 0xf007c01f0007c000) 64) 0x1f) 64) 0xe03fc07f80ff01fe) 64) 0x36eefc000007e00) 64) 0x1f8024fc01127c07) 64) 0x76db5afffbffebff) 64) 0xefffbffe00000000) 64) 0x0) 64) 0xffffffff00000000)
def bigNat_9 : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff7ffefffdff) 64) 0xfb6eefffdbb77ffe) 64) 0xdfffb6fffddb7ff7) 64) 0x76db5afffbffebff) 64) 0xefffbffeafffb7ff) 64) 0xd7ffdfff7ffddfff) 64) 0xfee8eee8fae8c000)
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 454
def AA : Nat := bigNat_0
def HX : Nat := bigNat_1
def HY : Nat := bigNat_2
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
def tstCore (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length
def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (tstCore d l e v F) (Nat.beq (cov d l v) l)
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
def segsX : List (ℕ × ℕ) := [(63, 77), (77, 81), (81, 95), (95, 109), (109, 123), (123, 125), (125, 139), (139, 142), (142, 156), (156, 158), (158, 160), (160, 174), (174, 188), (188, 202), (202, 204), (204, 218), (218, 232), (232, 234), (234, 237), (237, 239), (239, 242), (242, 245), (245, 248), (248, 251), (251, 255), (255, 259)]
def segsY : List (ℕ × ℕ) := [(259, 271), (271, 274), (274, 277), (277, 281), (281, 296), (296, 299), (299, 302), (302, 317), (317, 320), (320, 335), (335, 339), (339, 342), (342, 346), (346, 349), (349, 364), (364, 368), (368, 372), (372, 375), (375, 378), (378, 393), (393, 408), (408, 423), (423, 438), (438, 453)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2, _⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
  rw [← hr]
lemma mid_false {f : ℕ → List W → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch mk (Nat.sub (Nat.sub z x) y) = false
    cases ch mk (Nat.sub (Nat.sub z x) y) <;> simp
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : r.length + t = k + 1) : rect (pos' t) l (wst (pos' t) l r) r [] = false := by
  cases hrect : rect (pos' t) l (wst (pos' t) l r) r [] with
  | false => rfl
  | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := wst (pos' t) l r)] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : pos' 0 = false := by simp [pos']
          rw [hd'] at u1 u2 u3 u4
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : pos' t = true := by simp [pos', htp]
          rw [hd'] at u1 u2 u3 u4
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
lemma hit_ht {k z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y2
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
end sound
lemma hits_true {f : ℕ} {m : List ℕ} (h : hits f m = true) : ∃ e ∈ m, hit f e = true := by
  by_contra hc
  push Not at hc
  rw [hits_false fun e he => by simpa using hc e he] at h; simp at h
lemma app_mem {x y : List ℕ} {e : ℕ} : e ∈ app x y ↔ e ∈ x ∨ e ∈ y := by
  induction x with
  | nil => simp [app]
  | cons a x ih =>
    change e ∈ a :: app x y ↔ _
    simp only [List.mem_cons, ih, or_assoc]
def CmOk (F : W → ℕ) (r : List W) (col : ℕ → ℕ) (c : Cm) : Prop := ∃ κ ≤ 1, (∀ e ∈ c.a, ∃ w ∈ r, F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b, ∃ w ∈ r, F w = e ∧ col w.s = 1 - κ
lemma join_false {F : W → ℕ} {r : List W} {col : ℕ → ℕ} {k : List Cm → Bool} {w : W} (hw1 : col w.s ≤ 1)
    (hh : ∀ w' ∈ r, hit (F w) (F w') = true → col w.s ≠ col w'.s)
    (hk : ∀ cs, (∀ c ∈ cs, CmOk F (w :: r) col c) → k cs = false) : ∀ (cs : List Cm) (S O : List ℕ) (Q : List Cm),
    (∀ c ∈ cs, CmOk F r col c) → (∀ c ∈ Q, CmOk F (w :: r) col c) → (∀ e ∈ S, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = col w.s) →
    (∀ e ∈ O, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = 1 - col w.s) → join k (F w) cs S O Q = false := by
  intro cs
  induction cs with
  | nil =>
    intro S O Q _ hQ hS hO
    refine hk _ fun c hc => ?_
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨col w.s, hw1, hS, hO⟩
    · exact hQ c hc
  | cons c cs ih =>
    intro S O Q hcs hQ hS hO
    have hc := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, CmOk F r col c := fun c' h => hcs c' (by simp [h])
    obtain ⟨κ, hκ, ha, hb⟩ := hc
    have e : join k (F w) (c :: cs) S O Q = bif hits (F w) c.a then (bif hits (F w) c.b then true else join k (F w) cs (app c.b S) (app c.a O) Q)
        else (bif hits (F w) c.b then join k (F w) cs (app c.a S) (app c.b O) Q else join k (F w) cs S O (c :: Q)) := by
      change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs S O (c :: Q)) (join k (F w) cs (app c.a S) (app c.b O) Q) (hits (F w) c.b))
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs (app c.b S) (app c.a O) Q) true (hits (F w) c.b)) (hits (F w) c.a) : Bool) = _
      rw [bR, bR, bR]
    rw [e]
    have hA : hits (F w) c.a = true → κ = 1 - col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := ha x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have hB : hits (F w) c.b = true → κ = col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := hb x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have up : ∀ {κ' : ℕ} {L : List ℕ}, (∀ e ∈ L, ∃ w' ∈ r, F w' = e ∧ col w'.s = κ') → ∀ e ∈ L, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = κ' := by
      intro κ' L h e he
      obtain ⟨w', h1, h2⟩ := h e he
      exact ⟨w', by simp [h1], h2⟩
    cases h1 : hits (F w) c.a with
    | true =>
      have k1 := hA h1
      cases h2 : hits (F w) c.b with
      | true => have k2 := hB h2; omega
      | false =>
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
    | false =>
      cases h2 : hits (F w) c.b with
      | true =>
        have k2 := hB h2
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
      | false =>
        simp only [cond_false]
        refine ih _ _ _ hcs' ?_ hS hO
        intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨κ, hκ, up ha, up hb⟩
        · exact hQ c' hc'
lemma bip_aux {l o : ℕ} {col : ℕ → ℕ} : ∀ (v r : List W) (cs : List Cm), (∀ w ∈ v, col w.s ≤ 1) → (∀ c ∈ cs, CmOk (flag false l o) r col c) →
    (∀ w ∈ v, ∀ w' ∈ r, hit (flag false l o w) (flag false l o w') = true → col w.s ≠ col w'.s) →
    v.Pairwise (fun a b => hit (flag false l o b) (flag false l o a) = true → col b.s ≠ col a.s) → bip l o v cs = false := by
  intro v
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro r cs h1 h2 h3 h4
    rw [List.pairwise_cons] at h4
    change join (bip l o v) (flag false l o w) cs [flag false l o w] [] [] = false
    refine join_false (F := flag false l o) (h1 w (by simp)) (h3 w (by simp)) ?_ cs _ _ _ h2 (by simp) ?_ (by simp)
    · intro cs' hcs'
      refine ih (w :: r) cs' (fun x hx => h1 x (by simp [hx])) hcs' ?_ h4.2
      intro x hx w' hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact h4.1 x hx
      · exact h3 x (by simp [hx]) w' hw'
    · intro e he
      simp only [List.mem_singleton] at he
      exact ⟨w, by simp, he.symm, rfl⟩
lemma anyE_false : ∀ {m : List ℕ}, m.Pairwise (fun p q => hit p q = false) → anyE m = false := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons f t ih =>
    intro h
    rw [List.pairwise_cons] at h
    change (Bool.rec (motive := fun _ => Bool) (anyE t) true (hits f t) : Bool) = false
    rw [bR, hits_false h.1, ih h.2]; rfl
lemma rmF_eq (F : W → ℕ) (f : ℕ) (t : List W) : rmF f (t.map F) = (t.eraseP (fun q => hit f (F q))).map F := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => List ℕ) (F x :: rmF f (t.map F)) (t.map F) (hit f (F x)) : List ℕ) = _
    rw [List.eraseP_cons]
    cases h : hit f (F x)
    · simp [ih]
    · simp
lemma eraseP_not {α : Type} {p : α → Bool} {a : α} : ∀ {t : List α}, t.Nodup → a ∈ t → p a = true → (∀ x ∈ t, p x = true → x = a) → a ∉ t.eraseP p := by
  intro t
  induction t with
  | nil => intro _ h; simp at h
  | cons x t ih =>
    intro hn ha hp hx
    rw [List.nodup_cons] at hn
    rw [List.eraseP_cons]
    cases h : p x
    · have hax : a ≠ x := fun e => by rw [← e, hp] at h; simp at h
      simp only [Bool.false_eq_true, if_false, List.mem_cons, not_or]
      simp only [List.mem_cons] at ha
      exact ⟨hax, ih hn.2 (ha.resolve_left hax) hp fun y hy => hx y (by simp [hy])⟩
    · have := hx x (by simp) h
      subst this
      simpa using hn.1
lemma star_false {F : W → ℕ} {a : W} : ∀ {v : List W}, v.Nodup → star (v.map F) = false →
    ∃ p q : W, [p, q].Sublist v ∧ hit (F p) (F q) = true ∧ p ≠ a ∧ q ≠ a := by
  intro v hn hst
  by_contra hno
  push Not at hno
  have bad : ∀ p q : W, [p, q].Sublist v → hit (F p) (F q) = true → p = a ∨ q = a := by
    intro p q h1 h2
    by_cases h : p = a
    · exact Or.inl h
    · exact Or.inr (hno p q h1 h2 h)
  clear hno
  have key : star (v.map F) = true := by
    clear hst
    induction v with
    | nil => rfl
    | cons w t ih =>
      rw [List.nodup_cons] at hn
      have bt : ∀ p q : W, [p, q].Sublist t → hit (F p) (F q) = true → p = a ∨ q = a := fun p q h => bad p q (h.cons w)
      have e : star ((w :: t).map F) = bif hits (F w) (t.map F) then (bif anyE (t.map F) then (bif hits (F w) (rmF (F w) (t.map F)) then false else
          (bif anyE (rmF (F w) (t.map F)) then false else true)) else true) else star (t.map F) := by
        change (Bool.rec (motive := fun _ => Bool) (star (t.map F)) (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF (F w) (t.map F)))) false (hits (F w) (rmF (F w) (t.map F)))) (anyE (t.map F))) (hits (F w) (t.map F)) : Bool) = _
        rw [bR, bR, bR, bR]
      rw [e]
      have edge : ∀ u : List W, u.Sublist t → a ∉ u → anyE (u.map F) = false := by
        intro u hu ha
        refine anyE_false ?_
        rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
        intro p q hpq
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm : ∀ x ∈ [p, q], x ∈ u := fun x hx => hpq.subset hx
        rcases bt p q (hpq.trans hu) hc with rfl | rfl
        · exact ha (hm p (by simp))
        · exact ha (hm q (by simp))
      cases h1 : hits (F w) (t.map F) with
      | false => rw [cond_false]; exact ih hn.2 bt
      | true =>
        rw [cond_true]
        have part : ∀ q ∈ t, hit (F w) (F q) = true → w = a ∨ q = a := fun q hq h => bad w q ((List.singleton_sublist.2 hq).cons_cons w) h
        by_cases hwa : w = a
        · subst hwa
          rw [edge t (List.Sublist.refl t) hn.1]; rfl
        · have pa : ∀ q ∈ t, hit (F w) (F q) = true → q = a := fun q hq h => (part q hq h).resolve_left hwa
          obtain ⟨x, hx, hhx⟩ := hits_true h1
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          have hqa := pa q hq hhx
          subst hqa
          have hna : q ∉ t.eraseP (fun q => hit (F w) (F q)) := eraseP_not hn.2 hq hhx pa
          rw [rmF_eq, edge _ List.eraseP_sublist hna]
          have : hits (F w) ((t.eraseP (fun q => hit (F w) (F q))).map F) = false := by
            refine hits_false fun e he => ?_
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
            by_contra hc
            rw [Bool.not_eq_false] at hc
            have hyt : y ∈ t := List.eraseP_sublist.subset hy
            exact hna (pa y hyt hc ▸ hy)
          rw [this]
          cases anyE (t.map F) <;> rfl
  rw [key] at hst; simp at hst
lemma flk_eq (l o : ℕ) (v : List W) : ∀ k, flk l o v k = k (v.map (flag false l o)) := by
  induction v with
  | nil => intro k; rfl
  | cons w v ih =>
    intro k
    change flk l o v (fun r => k (flag false l o w :: r)) = _
    rw [ih]; rfl
def NK (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v : List W} {S : Finset ℕ} (h : Rep v S) : v.Nodup := List.Nodup.of_map _ h.1
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q := by
    intro a ha
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 ha
    obtain ⟨p, q, hpq, hh, h1, h2⟩ := star_false (F := flag false l (wst (pos' t) l v)) (a := wa) hs.rep.nodup hst
    have hp : p ∈ v := hpq.subset (by simp)
    have hq : q ∈ v := hpq.subset (by simp)
    have hne : p ≠ q := by
      have := hs.rep.nodup.sublist hpq
      simpa using this
    refine ⟨p.s, q.s, hs.rep.mem.2 ⟨p, hp, rfl⟩, hs.rep.mem.2 ⟨q, hq, rfl⟩, fun e => hne (hs.rep.inj hp hq e), fun e => h1 (hs.rep.inj hp hwa e),
      fun e => h2 (hs.rep.inj hq hwa e), hit_ht X hs hp hq hh⟩
  have he : ∀ t', pos' t = true ∨ t = t' → pos' t = true ∨ t' = 0 := by
    intro t' h
    rcases h with h | h
    · exact Or.inl h
    · subst h
      rcases Nat.eq_zero_or_pos t with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [pos', h])
  have kb : ∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → ∀ U, S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False := by
    rintro d a b S1 k0 rfl hb hl U rfl rfl ha hbU
    have hab := hb.1
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS, Finset.card_insert_of_notMem hbU] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    have hne : (if p = a ∨ p = b then op d a b else p) ≠ (if q = a ∨ q = b then op d a b else q) := by
      simp only [hpa, hqa, false_or]
      have h1' : p = b ∨ p ∈ U := by simp at hp; tauto
      have h2' : q = b ∨ q ∈ U := by simp at hq; tauto
      split_ifs with r s s
      · exact absurd (r.trans s.symm) hpq
      · intro e; exact hf (e ▸ h2'.resolve_left s)
      · intro e; exact hf (e ▸ h1'.resolve_left r)
      · exact hpq
    have k1 := h3 _ m1 _ m2 hne this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
  constructor
  · intro d a b S1 k0 hk' hb hl
    by_contra hc
    obtain ⟨hab, U, e1, e2, hal⟩ := id hb
    have hfS : op d a b ∉ S := fun h => hb.fresh hl (by rw [← hk']; exact hm.2) (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by rw [e1]; simp [h])
    have hs1 := (hb.min hl (by rw [← hk']; exact hm.2)).size.1
    have hcS1 : S1.card = U.card + 1 := by rw [e2, Finset.card_insert_of_notMem hf]
    by_cases ha : a ∈ U
    · by_cases hbU : b ∈ U
      · have : S = U := by rw [e1, Finset.insert_eq_of_mem hbU, Finset.insert_eq_of_mem ha]
        rw [this] at hx; omega
      · exact kb d a b S1 k0 hk' hb hl U e1 e2 ha hbU
    · by_cases hbU : b ∈ U
      · exact kb d b a S1 k0 hk' hb.symm hl U (by rw [e1, Finset.insert_comm]) (by rw [e2, op_comm]) hbU ha
      · have : S.card = U.card + 2 := by
          rw [e1, Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hbU]
        omega
  · rintro a S1 k0 t0 rfl rfl hu hl
    by_contra hc
    obtain ⟨U, rfl, rfl⟩ := id hu
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm.2 (sub_C _ _ (by simp [h]))
    have ha : a ∈ U := by
      by_contra ha
      rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem ha] at hc; omega
    have eS : insert a U = U := Finset.insert_eq_of_mem ha
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have hpos : pos' (t0 + 1) = true := by simp [pos']
    rw [hpos] at hh
    have := ht_un hp hq (fun e => absurd e hpa) (fun e => absurd e hqa) hh
    simp only [hpa, hqa, if_false] at this
    have m1 : p ∈ insert (a ^^^ m) U := by rw [eS] at hp; simp [hp]
    have m2 : q ∈ insert (a ^^^ m) U := by rw [eS] at hq; simp [hq]
    have k1 := h3 _ m1 _ m2 hpq this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
lemma tstCore_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tstCore (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tstCore (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst (pos' t) l v) v star)) false
        (bip l (wst (pos' t) l v) v [])) (Nat.beq (v.length + 1) (k + 1 - t)))
      (Bool.rec (motive := fun _ => Bool) (F 0) false (rect (pos' t) l (wst (pos' t) l v) v [])) (Nat.beq v.length (k + 1 - t)) : Bool) = _
    rw [bR, bR, bR, bR, bR]
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have hr := rect_ok X hs hm hk (by omega)
    exact ⟨0, fun F => by rw [e, h1, hr]; rfl, Or.inl rfl⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | false => exact ⟨0, fun F => by rw [e, h1, h2]; rfl, Or.inl rfl⟩
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      have hbip : bip l (wst (pos' t) l v) v [] = false := by
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (by
          rcases Nat.eq_zero_or_pos t with h | h
          · exact Or.inr h
          · exact Or.inl (by simp [pos', h]))
        refine bip_aux (col := f) v [] [] ?_ (by simp) (by simp) ?_
        · intro w hw
          have := q2 w.s (hs.rep.mem.2 ⟨w, hw, rfl⟩); omega
        · have hnd : v.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hs.rep.1
          refine hnd.imp_of_mem fun {a b} ha hb hab hh => ?_
          exact q3 b.s (hs.rep.mem.2 ⟨b, hb, rfl⟩) a.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (Ne.symm hab) (hit_ht X hs hb ha hh)
      cases h3 : flk l (wst (pos' t) l v) v star with
      | true => exact ⟨0, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inl rfl⟩
      | false => exact ⟨1, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inr ⟨rfl, by omega, nk_ok X hs hm (by omega) h3⟩⟩
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hm.1.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simpa only [tst, hcov] using tstCore_sound X hs hm hk
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk h, hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : L_meta_45452.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : X → X → Bool} {xs : List X} (hp : pairsN h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
lemma opW_r (d : Bool) (a c : W) : (opW d a c).r = 0 := by cases d <;> rfl
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)))) m g (k - s - y) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {m T k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) t S) (hk : k' + 1 ≤ k)
    (hb : Bi R d a b S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK R m T (k' + 1) t S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {m T k k' t : ℕ} {S S1 : Finset ℕ} {a n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' + 1 ≤ k)
    (hb : Un m a S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK R m T (k' + 1) (t + 1) S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_45452.X → L_meta_45452.X → Bool) → List L_meta_45452.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g k t z v y = false) : ∀ k' ≤ k, Min R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False := by
  intro k' hk hm hy
  obtain ⟨hA, hN⟩ := mv_false F l m g k t z v y h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | h
    · exact Or.inl h
    · exact hv w h
  have codU : ∀ {v r : List W} {a : W}, Cod R v → (∀ w ∈ r, w = notW m a ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact hv w h
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have : a.s = c.s := congrArg L_meta_45452.X.s e
        exact hb.1 (by rw [← hax, ← hcy, this])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.r = R a.s := (hcod a ha).resolve_left hc'.1
        have h2 : c.r = R c.s := (hcod c hc).resolve_left hc'.2
        have g1 : a.r ≠ 0 := hc'.1
        have g2 : c.r ≠ 0 := hc'.2
        rw [← hax, ← hcy] at hal
        exact hR _ _ _ (by rw [← h1]; exact g1) (by rw [← h2]; exact g2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨y2, hF3, hy2⟩ := tst_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
end sound
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : a ^^^ m ∉ C m (Q ∪ ((insert a U : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : a ^^^ m ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (a ^^^ m) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
    · exact Or.inl (.un h)
    · have nx : x ≠ a ^^^ m := fun e => hx (e ▸ hfR)
      have ny : y ≠ a ^^^ m := fun e => hy (e ▸ hfR)
      have hmV : a ^^^ m ∈ V := by
        have : a ^^^ m ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase (a ^^^ m))) := by
        ext z
        by_cases hz : z = a ^^^ m
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma Min.Z {m T k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) : Min Z0 m T k t S := ⟨h.1.rel fun d a b _ => al0 d a b, h.2⟩
lemma NK.toR {m T k t : ℕ} {S : Finset ℕ} (h : NK Z0 m T k t S) : NK R m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun d a b _ => al0 d a b)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_45452.X → L_meta_45452.X → Bool) → List L_meta_45452.X → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax, hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := wa.s) (b := wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma or_false' {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  clear X
  cases a <;> simp_all
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine one_sound X hR hR2 ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS, hy1, fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_45452.X.s e))
end sound
def rawP : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8]
def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := bigNat_9
def cutMasks : List ℕ := [(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x5 64) 0x6b0ad615acfffc56) 64) 0xb122e2cd88977ffe) 64) 0x1fff86fffc1b2d60) 64) 0x61b1a10d3ffe843) 64) 0x8fffbffe210b37ff) 64) 0xd0871fff7ffdc254) 64) 0xaaaaaaaaaaaaaaaa), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0xa 64) 0xa5954b7ffe352caa) 64) 0x5a4e2fffc1312a2e) 64) 0x5fffb0fffdc354b0) 64) 0x70c342fff8854bff) 64) 0xe2163ffe82433122) 64) 0x97ffc48c7ffddfff) 64) 0xcccccccccccccccc), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x10 64) 0xd6bfff235a46b5ff) 64) 0xf86441b353a27ffe) 64) 0xc34d90fffdd81ad7) 64) 0xd8584891224bff) 64) 0xefff9228afff8244) 64) 0x97ffdfff2451dfff) 64) 0xf0f0f0f0f0f0f0f0), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffa6314c6298c5ff) 64) 0xfb088fffda047ffe) 64) 0xdfffb6c30c406317) 64) 0x76005afffbffe227) 64) 0x89c2270afffb7ff) 64) 0xc46611984661dfff) 64) 0xff00ff00ff00ff00), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff7ffefffd01) 64) 0xf0000fffdbb701f8) 64) 0x807e0203f08903e7) 64) 0x76db00f103c403c4) 64) 0xf103c40afffb7ff) 64) 0xd7ffdfff7ffc1e80) 64) 0xffff0000ffff0000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff7ffefffdff) 64) 0xfb6eefc000007e00) 64) 0x1f8024fc01127c07) 64) 0x76db5afffbffebff) 64) 0xefffbffe0f8007c0) 64) 0x7c01f007c001f00) 64) 0xffffffff00000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffffffffff14a7ff) 64) 0xffff1ffffff8a8a3) 64) 0xea48f99247e4ffff) 64) 0xfdf6f5ffffb437ff) 64) 0xfed0fb43dfffef70) 64) 0x6ffffdc1f7063fff) 64) 0x5555555555555555), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffffff8569ffffff) 64) 0xfff1f2953fcfffff) 64) 0xe5544f4b223cffff) 64) 0xcfbdfddc8ffff772) 64) 0x3ffff6a37fffcfff) 64) 0xeed47fffecc73b61) 64) 0x3333333333333333), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffc652fffffffe32) 64) 0x979ffffffc7fb249) 64) 0x3fffffc51227fffc) 64) 0xff6fa7fffffff6cd) 64) 0x3b34ffffdb62ffff) 64) 0xedaa76a9fffeb699) 64) 0xf0f0f0f0f0f0f0f), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x20 64) 0xe77ffffffffffe0e) 64) 0x74fff1c3a7ff8e39) 64) 0x238e49fffffffffa) 64) 0xabffa5721dc87fff) 64) 0xffffffff5711cb88) 64) 0xfffffffffffe6e07) 64) 0xff00ff00ff00ff), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x23 64) 0xe0c7c18f831f07ff) 64) 0xfffff7c06448ffff) 64) 0xfffffffffffffff9) 64) 0x8924ffffffffffff) 64) 0xffffffff708fd847) 64) 0xf847e11f847fffff) 64) 0xffff0000ffff), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x20 64) 0x1fc03f807f00fe01) 64) 0xfc911fffffffffff) 64) 0xfffffffffffffff8) 64) 0x9924af01fc07fc07) 64) 0xf01fc07fffffffff) 64) 0xffffffffffffffff) 64) 0xffffffff)]
def exclusions : List ℕ := [(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0xf 64) 0xce9f9d7ffefffcfc) 64) 0xeb6eefffc9b77ffe) 64) 0x4f1cb6d965d879d0) 64) 0x76db58fffbffe3ff) 64) 0xefff8de0a34827ff) 64) 0xc7ffdfff1bc11fff) 64) 0x6666666666666666), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x15 64) 0xbdbfff36f6fffdff) 64) 0xf966e37edbb71aea) 64) 0xdfff965755c337b7) 64) 0x6db525843ffe3ff) 64) 0xe5e43ffe8fffb7ff) 64) 0xc7ffcb687ffc9fff) 64) 0x5a5a5a5a5a5a5a5a), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xfface759cefffdff) 64) 0xfb2aefffda97269a) 64) 0xc9c6b0fffc5b4e77) 64) 0x761b50fffa7c4a64) 64) 0x8fffbffe8fffa4f8) 64) 0x94e11fff7ffc5fff) 64) 0x55aa55aa55aa55aa), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff7ffe0ba157) 64) 0x4122efffdbb07ffe) 64) 0x9fff86fffc9b2e87) 64) 0x74d21ae1d3ffeb87) 64) 0x8fffbffeafffb737) 64) 0x97ffdcde7379dcd4) 64) 0x5555aaaa5555aaaa), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff7ffe1459ff) 64) 0xfb6e0d0d88977ffe) 64) 0x1fffa6fffd1b5167) 64) 0x74d25afffbb3cbff) 64) 0xeecf3b3c2e8b37ff) 64) 0xd7471fff7ffddd54) 64) 0x55555555aaaaaaaa), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1a 64) 0x733fff7ffe7399ff) 64) 0xfa6e6fffd3b37ffe) 64) 0xdfffb08e301b4e67) 64) 0x70db5afff9a701bf) 64) 0xfffbffeafffb366) 64) 0x37e1fff7ffd8df8) 64) 0x3c3c3c3c3c3c3c3c), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffb37a7ffeade9ff) 64) 0xfb4ea3569b357ffe) 64) 0xc6da06fffdc337a7) 64) 0x66c358ae93ffebff) 64) 0xea8a3ffe2fff87ff) 64) 0xd7ffd5147ffd5566) 64) 0x33cc33cc33cc33cc), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff0aeafffdab) 64) 0xaa4e25555b872bd6) 64) 0xdfffb2fffdcb5757) 64) 0x469942fffb414bff) 64) 0xed063ffe2fff97ff) 64) 0xd6939fff68b9dfff) 64) 0x3333cccc3333cccc), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff0516fffdff) 64) 0xfb60efffc131542e) 64) 0x5fffb4fffdd328b7) 64) 0x56995add73ffeb75) 64) 0xcfffb6dc8dc336e2) 64) 0x97ffdb8c7ffddfff) 64) 0x33333333cccccccc), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xffbfff6f38de703c) 64) 0xe36ccfffdba63c70) 64) 0x1fffb6fffdd879c6) 64) 0x76d802fffbffebff) 64) 0xefffb0588c7337ff) 64) 0xd7ffdfff6230d89e) 64) 0xff00ff00ff00ff0), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xff81937ffefffdff) 64) 0xf8644fffd8377ffe) 64) 0xc33392fffdd91935) 64) 0x764b58b992e64bff) 64) 0xefffae68abed37ff) 64) 0xd5ed97b67ffddfff) 64) 0xf0ff0f00f0ff0f0), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1f 64) 0xff866d7ffefffc33) 64) 0x6b0eee7353a27ffe) 64) 0xdccdb4fffdda66d4) 64) 0x764b0afffbffeaca) 64) 0xcb2b3ffeafff8584) 64) 0x97ffdfff5851dfff) 64) 0xf0f0f0ff0f0f0f0), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3 64) 0x7bfff7ffefffdff) 64) 0xfb088603c3b77ffe) 64) 0xdfffb6c0fcc960f3) 64) 0x22db5afffbffe1e3) 64) 0x78c1e30279e13cf) 64) 0x17ffdfff7ffddfff) 64) 0xffff0000ffff00), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0xf8bfff7ffefffc0f 64) 0x886eefffda047ffe) 64) 0xdfffb63f0d521f12) 64) 0x32db0a73e1cf8bff) 64) 0xefffbffeafffb7ff) 64) 0xc3a60e983a61dfff) 64) 0xff00ffff00ff00), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3 64) 0xff07fe0ffc1ff9ff) 64) 0xfb6eefffdbb77ff8) 64) 0x9ffe26fff19b7fe1) 64) 0x10005afffbffebff) 64) 0xefffbffeafffb7ff) 64) 0xd7ffdfff7ffc0180) 64) 0xffffffff0000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffffff90c5218bff) 64) 0xfff33058bfd9828d) 64) 0xffffc9fffe27ffff) 64) 0xcdb7f7cc5f317f31) 64) 0xbcc6ffff5ffffe52) 64) 0xfe53794dfffff935) 64) 0x9999999999999999), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffcc84ffff521264) 64) 0x27bf5ffffcfaffff) 64) 0x290579fffe3cfffc) 64) 0xfd7ebdfffe967e8e) 64) 0xbfffe96bfa69ed34) 64) 0xfd2d7fffd357f4cd) 64) 0xa5a5a5a5a5a5a5a5), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x25 64) 0x8c7fffffff8c6258) 64) 0xc5ff930e2ffcffff) 64) 0x3fffcf514be4fffa) 64) 0xaff6bf62cffff7ff) 64) 0xf64cd933761affff) 64) 0xefffec59b167ec53) 64) 0xaa55aa55aa55aa55), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x26 64) 0x8bcd179a2fffffff) 64) 0xffff150decdfa95b) 64) 0xea36fb91b7edfff9) 64) 0x8f3ff5fffc7037ff) 64) 0xf1c0c7037184ffff) 64) 0xf8c0fffffffe3fff) 64) 0xaaaa5555aaaa5555), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x25 64) 0x74cae995d3fffe57) 64) 0x4db3fffffff8d6a3) 64) 0xf5c8fd6e47f6fff8) 64) 0x9f3fbf112ffffc44) 64) 0x7fffffffdfffe8b0) 64) 0x6fffe2c18b063fff) 64) 0xaaaaaaaa55555555), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffd319a633fffe98) 64) 0xcfd5f3267d6f9867) 64) 0x6619dfffffe4fffc) 64) 0xcfede5941fffffff) 64) 0xf922e48bd921cfff) 64) 0xfffff225c897ffff) 64) 0xc3c3c3c3c3c3c3c3), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x2a 64) 0x42ffffc90bfffea4) 64) 0x2ef9ffffe7cfa417) 64) 0x7ffff9882e7cfffa) 64) 0xfbbde7fffd4d3555) 64) 0x3fffd4d3d552faaa) 64) 0x6ab27fffaaa7ffff) 64) 0xcc33cc33cc33cc33), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x29 64) 0x45528affff2a2bff) 64) 0xfff1ffffe579ffff) 64) 0xe52a4f48d2bdfff9) 64) 0xf9e7fd2d8ffff4b6) 64) 0x3fffcae3f2ccf965) 64) 0x7fffe593ffff25e1) 64) 0xcccc3333cccc3333), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x2a 64) 0xba5574ffff35d2ab) 64) 0xa6df3d553fcfffff) 64) 0xfad46fb7233efff8) 64) 0xf9e7effffc82bfff) 64) 0xf209ffff7fffcfff) 64) 0xe9147fff90c72461) 64) 0xcccccccc33333333), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x30 64) 0x31e063ffffffffff) 64) 0xfc9ff070f67fffff) 64) 0xe0c3d9061e67ffff) 64) 0xab6ffd3a8cea34ea) 64) 0x33a8ffffffffc9cc) 64) 0x69cc6731ffffffff) 64) 0xf00ff00ff00ff00f), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x33 64) 0x367fffacd959b333) 64) 0x679ff67337eab3b1) 64) 0xbfffffc6e2afffff) 64) 0x89fca7fffffff509) 64) 0x3424ffffffffda03) 64) 0x7fffffffa02ea819) 64) 0xf0f00f0ff0f00f0f), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x30 64) 0xc97fffa325464bff) 64) 0xfcf55ffffc7fcc49) 64) 0x3fffff391337ffff) 64) 0x99fcff496d25bfff) 64) 0xffffd257d4e2ffff) 64) 0xea6a69a9fffea999) 64) 0xf0f0f0f00f0f0f0f), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffe1f0c3e187c30f) 64) 0x84fffffffe4c8fc1) 64) 0xa3f04bffffffffff) 64) 0xff24a5831e0c7fff) 64) 0xffffffffffffffff) 64) 0xfc21f087c21e7087) 64) 0xff0000ffff0000ff), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffe60ecc1d983bff) 64) 0xff999e03a7fff039) 64) 0x3c0e6dffffffffff) 64) 0xff24fffffffffe20) 64) 0xf883e20f5891cc48) 64) 0xfffffffffffe7107) 64) 0xff00ff0000ff00ff), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x3f 64) 0xffffffffffffff00) 64) 0xc9118006448ffff) 64) 0xffffffffffffffff) 64) 0xffffaff0ffc3ffc3) 64) 0xff0ffc3f7f0fdf87) 64) 0xff87fe1ff87fffff) 64) 0xffff00000000ffff)]
def kz (Z : ℕ) : ℕ := if Z < 4096 then (List.range 12).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (cutMasks.getD i 0) else x) 0 else exclusions.getD (Z-4096) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawG.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawG) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 35
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c, w.r⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
  have un2 := fun p hp => (hFy _).symm.trans (un p hp).2
  refine one_sound X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc hne har hcr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((a.s + c.s) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : L_meta_45452.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_45452.X.s e)) hpb
end sound
def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def pwr (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E : List (ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
lemma RZ_R (E : List (ℕ × ℕ)) (Z : ℕ) : RR (RZ E Z) := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
lemma RZ_R2 (E : List (ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
lemma rawL_sub {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e ∈ six) {w : ℕ} (hw : w ∈ rawL E) : w ∈ rawG := by
  simp only [rawG, rawL, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hE e he, rfl⟩
theorem imp_of_live {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
theorem imp_of {E Q : List (ℕ × ℕ)} {Z L : ℕ} (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega)
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine Nat.find_min hex (show q < Nat.find hex by omega) (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def row3g0 : List (ℕ × ℕ) := []
def row3g1 : List (ℕ × ℕ) := []
def row3g2 : List (ℕ × ℕ) := []
def row3g3 : List (ℕ × ℕ) := [(145, 4)]
def row3g4 : List (ℕ × ℕ) := []
def row3g5 : List (ℕ × ℕ) := []
def row3g6 : List (ℕ × ℕ) := [(289, 4)]
def row3g7 : List (ℕ × ℕ) := []
def row3g8 : List (ℕ × ℕ) := []
def row3g9 : List (ℕ × ℕ) := []
def row3g10 : List (ℕ × ℕ) := [(1058, 4)]
def row3g11 : List (ℕ × ℕ) := []
def row3g12 : List (ℕ × ℕ) := []
def row3g13 : List (ℕ × ℕ) := [(1064, 4)]
def row3g14 : List (ℕ × ℕ) := []
def row3g15 : List (ℕ × ℕ) := []
def row3g16 : List (ℕ × ℕ) := []
def row3g17 : List (ℕ × ℕ) := [(2068, 4)]
def row3g18 : List (ℕ × ℕ) := []
def row3g19 : List (ℕ × ℕ) := []
def row3g20 : List (ℕ × ℕ) := [(2072, 4)]
def row3g21 : List (ℕ × ℕ) := []
def row3g22 : List (ℕ × ℕ) := []
def row3g23 : List (ℕ × ℕ) := []
def row3g24 : List (ℕ × ℕ) := [(3073, 4)]
def row3g25 : List (ℕ × ℕ) := []
def row3g26 : List (ℕ × ℕ) := []
def row3g27 : List (ℕ × ℕ) := [(3074, 4)]
def row3g28 : List (ℕ × ℕ) := []
def row3g29 : List (ℕ × ℕ) := []
def row3g30 : List (ℕ × ℕ) := []
def row3g31 : List (ℕ × ℕ) := [(3076, 4)]
def row3g32 : List (ℕ × ℕ) := []
def row3g33 : List (ℕ × ℕ) := []
def row3g34 : List (ℕ × ℕ) := [(3080, 4)]
def rt3 : List (ℕ × ℕ) := row3g0 ++ row3g1 ++ row3g2 ++ row3g3 ++ row3g4 ++ row3g5 ++ row3g6 ++ row3g7 ++ row3g8 ++ row3g9 ++ row3g10 ++ row3g11 ++ row3g12 ++ row3g13 ++ row3g14 ++ row3g15 ++ row3g16 ++ row3g17 ++ row3g18 ++ row3g19 ++ row3g20 ++ row3g21 ++ row3g22 ++ row3g23 ++ row3g24 ++ row3g25 ++ row3g26 ++ row3g27 ++ row3g28 ++ row3g29 ++ row3g30 ++ row3g31 ++ row3g32 ++ row3g33 ++ row3g34
def row2g0 : List (ℕ × ℕ) := [(17, 5)]
def row2g1 : List (ℕ × ℕ) := [(20, 5)]
def row2g2 : List (ℕ × ℕ) := [(24, 5), (33, 5)]
def row2g3 : List (ℕ × ℕ) := [(34, 5)]
def row2g4 : List (ℕ × ℕ) := [(40, 5), (80, 6)]
def row2g5 : List (ℕ × ℕ) := [(96, 6)]
def row2g6 : List (ℕ × ℕ) := [(129, 5), (144, 5)]
def row2g7 : List (ℕ × ℕ) := [(257, 5)]
def row2g8 : List (ℕ × ℕ) := [(288, 5), (1025, 5)]
def row2g9 : List (ℕ × ℕ) := [(1028, 5)]
def row2g10 : List (ℕ × ℕ) := [(1056, 5), (2049, 5)]
def row2g11 : List (ℕ × ℕ) := [(2050, 5)]
def row2g12 : List (ℕ × ℕ) := [(2064, 5), (3072, 7)]
def rt2 : List (ℕ × ℕ) := row2g0 ++ row2g1 ++ row2g2 ++ row2g3 ++ row2g4 ++ row2g5 ++ row2g6 ++ row2g7 ++ row2g8 ++ row2g9 ++ row2g10 ++ row2g11 ++ row2g12
def row1g0 : List (ℕ × ℕ) := [(1, 8)]
def row1g1 : List (ℕ × ℕ) := [(2, 7), (4, 7)]
def row1g2 : List (ℕ × ℕ) := [(8, 6)]
def row1g3 : List (ℕ × ℕ) := [(16, 9), (32, 9)]
def row1g4 : List (ℕ × ℕ) := [(64, 7)]
def row1g5 : List (ℕ × ℕ) := [(128, 6), (256, 6)]
def row1g6 : List (ℕ × ℕ) := [(512, 7), (1024, 8)]
def row1g7 : List (ℕ × ℕ) := [(2048, 8)]
def row1g8 : List (ℕ × ℕ) := [(4110, 9), (4114, 10)]
def row1g9 : List (ℕ × ℕ) := [(4115, 10)]
def row1g10 : List (ℕ × ℕ) := [(4118, 9), (4119, 10)]
def row1g11 : List (ℕ × ℕ) := [(4121, 10), (4122, 9)]
def rt1 : List (ℕ × ℕ) := row1g0 ++ row1g1 ++ row1g2 ++ row1g3 ++ row1g4 ++ row1g5 ++ row1g6 ++ row1g7 ++ row1g8 ++ row1g9 ++ row1g10 ++ row1g11
def identifications : List (ℕ × ℕ × ℕ) := [(0,1,0), (0,2,0), (0,3,0), (0,4,0), (0,5,0), (1,2,0), (1,3,0), (1,4,0), (1,5,0), (2,3,0), (2,4,0), (2,5,0), (3,4,0), (3,5,0), (4,5,0), (0,1,1), (0,2,1), (0,3,1), (0,4,1), (0,5,1), (1,2,1), (1,3,1), (1,4,1), (1,5,1), (2,3,1), (2,4,1), (2,5,1), (3,4,1), (3,5,1), (4,5,1)]
def subIdentification (z k : ℕ) : Bool :=
  let (i,j,p) := identifications.getD (z-4096) (0,0,0)
  (k.testBit i && k.testBit (j+6*p)) || (k.testBit (i+6) && k.testBit (j+6*(1-p)))
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => (if Z < 4096 then Nat.beq (Nat.land Z e.1) Z else subIdentification Z e.1) && !Nat.beq Z e.1)
def rt : List (ℕ × ℕ) := (rt1 ++ rt2 ++ rt3).filter (fun e => decide (4 ≤ e.2))
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {E A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp E e.1 e.2) (hb : ∀ e ∈ B, Imp E e.1 e.2) : ∀ e ∈ A ++ B, Imp E e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
lemma imp_ts {E Q : List (ℕ × ℕ)} {L : ℕ} (hE : E = [] ∨ ∃ p ∈ six, E = [p] ∧ Imp [] 0 L) (hp : pOk 0 Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (h : ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 (L - 1) t p.1 p.2 = false) : Imp E 0 L :=
  imp_of hE hp hL hI (Or.inr h)
lemma one {E Q : List (ℕ × ℕ)} {K t : ℕ} (h : chk E Q 0 K t FF 1 = false) : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 K t p.1 p.2 = false :=
  ⟨[(FF, 1)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g0ok : row3g0.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g1ok : row3g1.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g2ok : row3g2.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g3ok : row3g3.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g4ok : row3g4.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g5ok : row3g5.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g6ok : row3g6.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g7ok : row3g7.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g8ok : row3g8.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g9ok : row3g9.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g10ok : row3g10.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g11ok : row3g11.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g12ok : row3g12.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g13ok : row3g13.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g14ok : row3g14.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g15ok : row3g15.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g16ok : row3g16.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g17ok : row3g17.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g18ok : row3g18.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g19ok : row3g19.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g20ok : row3g20.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g21ok : row3g21.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g22ok : row3g22.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g23ok : row3g23.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g24ok : row3g24.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g25ok : row3g25.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g26ok : row3g26.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g27ok : row3g27.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g28ok : row3g28.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g29ok : row3g29.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g30ok : row3g30.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g31ok : row3g31.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g32ok : row3g32.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g33ok : row3g33.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3g34ok : row3g34.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
theorem r3 : rt3.all (fun e => okE [] (pr [] e.1) e) = true := by
  simp only [rt3, List.all_append, Bool.and_true, row3g0ok, row3g1ok, row3g2ok, row3g3ok, row3g4ok, row3g5ok, row3g6ok, row3g7ok, row3g8ok, row3g9ok, row3g10ok, row3g11ok, row3g12ok, row3g13ok, row3g14ok, row3g15ok, row3g16ok, row3g17ok, row3g18ok, row3g19ok, row3g20ok, row3g21ok, row3g22ok, row3g23ok, row3g24ok, row3g25ok, row3g26ok, row3g27ok, row3g28ok, row3g29ok, row3g30ok, row3g31ok, row3g32ok, row3g33ok, row3g34ok]
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll (T := []) r3 (by simp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g0ok : row2g0.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g1ok : row2g1.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g2ok : row2g2.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g3ok : row2g3.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g4ok : row2g4.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g5ok : row2g5.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g6ok : row2g6.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g7ok : row2g7.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g8ok : row2g8.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g9ok : row2g9.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g10ok : row2g10.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g11ok : row2g11.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2g12ok : row2g12.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
theorem r2 : rt2.all (fun e => okE [] (pr rt3 e.1) e) = true := by
  simp only [rt2, List.all_append, Bool.and_true, row2g0ok, row2g1ok, row2g2ok, row2g3ok, row2g4ok, row2g5ok, row2g6ok, row2g7ok, row2g8ok, row2g9ok, row2g10ok, row2g11ok, row2g12ok]
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll r2 i3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g0ok : row1g0.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g1ok : row1g1.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g2ok : row1g2.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g3ok : row1g3.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g4ok : row1g4.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g5ok : row1g5.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g6ok : row1g6.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g7ok : row1g7.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g8ok : row1g8.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g9ok : row1g9.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g10ok : row1g10.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1g11ok : row1g11.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
theorem r1 : rt1.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by
  simp only [rt1, List.all_append, Bool.and_true, row1g0ok, row1g1ok, row1g2ok, row1g3ok, row1g4ok, row1g5ok, row1g6ok, row1g7ok, row1g8ok, row1g9ok, row1g10ok, row1g11ok]
lemma i1 : ∀ e ∈ rt1, Imp [] e.1 e.2 := okAll r1 (apI i2 i3)
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := fun e he => (apI (apI i1 i2) i3) e (List.mem_of_mem_filter he)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_p : pOk 0 rt = true := by decide +kernel
private def preparedStock : List W := [⟨0x7ffefffdfffbfff7ffedbb800000000000000000000000001d9b6d43f80fe00fe03f80fe003e001f001f007c01f0007c000000000000000001fe03fc07f80ff01fe036eefc000007e001f8024fc01127c0776db5afffbffebffefffbffe000000000000000000000000ffffffff00000000, 0x2108000000200040000401084000000000000000000002000000, 0x84210840000021084000000000000000000000000000080000000000000, 0x84210842108021084200040000401084000000000000080000002000000, 0x3⟩, ⟨0x7ffefffdfffbfff00000003fff6edc00000000000000000019db6c03c40f100f103c40f1023dc09ee01ee07b81ee007a000000000000000001c1f383e707ce0f901f000083f9bb701f8807e0203f08903e776db00000000000000000000afffb7ffd7ffdfff7ffc0000ffff0000ffff0000, 0x840000401000000000100020000210800000000000000000100000, 0x84210002100020000210800000000000000000000000004000000000000, 0x84210842100421000210800100020000210800000000004000000100000, 0x3⟩, ⟨0x7ffe000000000007ffec003fff6001fffb7ffed8000000001550016a3788de089c227089c2a3b8d1dc11984661198647e00000000000000001f18a6314c6298c5f18b088e3c5a0471c6dc71b6c30c40631776005afffbffe00000000000afffb7ffc00000000001dfffff00ff00ff00ff00, 0x80000802000000000000000000001000200000000000000000000008000, 0x200000000000, 0x80000802000000000000000000001000200000000000000200000008000, 0x3⟩, ⟨0xfffc00000007ffe18000000e01fffb000003fff760000c02416122448924cb132c48a092740912495625589145259800000000000000010d6b9ad235a46b5cd686441b353a24db6c34d903aedd81ad700d8580000000bffefff8000afff800017ffdfff0001dffff0f0f0f0f0f0f0f0, 0x4000040000000000010000000000000010000000000000000000000400, 0x8000000000042000000000000000000000000010000000000, 0x4000040008000000010042000000000010000000000000010000000400, 0x3⟩, ⟨0x1fff800000000383fff00c000007ffec3fff70c0000c108088dc215223708582572090cc48a44ae12304ce312780000000000000000aa5954b7a96352caa5a4e2d6ac1312a2e5aabb0b4ddc354b070c342fff8000bffe0003ffe8000300017ffc0007ffddfffcccccccccccccccc, 0x200000100000080000000000000080000000000000000000000000020, 0x400000000000108000000000000000000000000800000000, 0x200000100400080000000108000080000000000000000000800000020, 0x3⟩, ⟨0x3fff00000038000001dfff87ffe1bfff06c000008242843412f210e04bc12f0842c423e421c08f823e70950000000000000000056b0ad615aceb5856b122e2cd8897575c15b7066db81b2d60061b1a0003ffe8000fffbffe200037ffd0001fff7ffdc000aaaaaaaaaaaaaaaa, 0x10000008400004000802008000004000800000000000000000000001, 0x420000000000000000000000040000000, 0x10000008400004000802008420004000800000000000000040000001, 0x3⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepare_w : avl (PZ rt) (mz 0) (rawL []) = preparedStock := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepare_l : lz 0 = 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepare_m : mz 0 = 0x7ffefffdfffbfff7ffedbbbfff6eddfffb7ffedbfff76dffdddb6d6bffefffafffbffefffabffedfff5fff7ffdfff77ffc0000000000000001fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfffffffffffffffffff := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepare_g : pL (rt.map fun _ => 16) = 0x842108421084210842108421084210842108421084210842108421084210 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepare_p : pwr [] 0 = 0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepare_b11 : pL (rt.map fun e => 16 + (11 - e.2)) = 0xbdef7bdef7bde96b5ad6b5ad6b56b6b5ad6b4a31946329ce95ad252ad293 := rfl

private noncomputable def prepared11 (t H ph : ℕ) : Bool :=
  anySub (pos t) 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 preparedStock 0 (fun r => startv 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 0x7ffefffdfffbfff7ffedbbbfff6eddfffb7ffedbfff76dffdddb6d6bffefffafffbffefffabffedfff5fff7ffdfff77ffc0000000000000001fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfffffffffffffffffff 0x842108421084210842108421084210842108421084210842108421084210 0xbdef7bdef7bde96b5ad6b5ad6b56b6b5ad6b4a31946329ce95ad252ad293 11 t 0 H ph r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepared_eq11 (t H ph : ℕ) : chk [] rt 0 11 t H ph = prepared11 t H ph := by
  simp only [chk, frc_eq, st_eq]
  unfold prepared11
  rw [prepare_w, prepare_l, prepare_m, prepare_g, prepare_b11, prepare_p]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepare_b12 : pL (rt.map fun e => 16 + (12 - e.2)) = 0xc6318c6318c62b7bdef7bdef7bdad7bdef7bce529ca53a52b6b5673b56b4 := rfl

private noncomputable def prepared12 (t H ph : ℕ) : Bool :=
  anySub (pos t) 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 preparedStock 0 (fun r => startv 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 0x7ffefffdfffbfff7ffedbbbfff6eddfffb7ffedbfff76dffdddb6d6bffefffafffbffefffabffedfff5fff7ffdfff77ffc0000000000000001fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfffffffffffffffffff 0x842108421084210842108421084210842108421084210842108421084210 0xc6318c6318c62b7bdef7bdef7bdad7bdef7bce529ca53a52b6b5673b56b4 12 t 0 H ph r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem prepared_eq12 (t H ph : ℕ) : chk [] rt 0 12 t H ph = prepared12 t H ph := by
  simp only [chk, frc_eq, st_eq]
  unfold prepared12
  rw [prepare_w, prepare_l, prepare_m, prepare_g, prepare_b12, prepare_p]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k11t0ok : chk [] rt 0 11 0 FF 1 = false := by
  rw [prepared_eq11]
  decide +kernel
lemma k11t0 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 11 0 p.1 p.2 = false := one k11t0ok

deriving instance DecidableEq for W
private abbrev FrontKey := Nat × List W
private abbrev FrontSearch := Nat → Nat → Nat → List W → Bool

private def skipProved (f : FrontSearch) (steps : List FrontKey) (depth tokens : Nat) :
    FrontSearch := fun k t z v =>
  if k = depth ∧ t = tokens ∧ (z,v) ∈ steps then false else f k t z v

private theorem skipProved_eq {f : FrontSearch} {steps : List FrontKey} {d u : Nat}
    (h : ∀ s ∈ steps, f d u s.1 s.2 = false) : skipProved f steps d u = f := by
  funext k t z v
  unfold skipProved
  split
  · rename_i hp
    obtain ⟨rfl,rfl,hm⟩ := hp
    exact (h (z,v) hm).symm
  · rfl

private theorem frontBlock {f : FrontSearch} {steps : List FrontKey} {d u : Nat}
    (h : steps.all (fun s => !(f d u s.1 s.2)) = true) :
    ∀ s ∈ steps, f d u s.1 s.2 = false := by
  simpa only [List.all_eq_true, Bool.not_eq_true'] using h

private theorem frontAppend {p : FrontKey → Prop} {xs ys : List FrontKey}
    (a : ∀ s ∈ xs, p s) (b : ∀ s ∈ ys, p s) : ∀ s ∈ xs ++ ys, p s :=
  fun s h => (List.mem_append.mp h).elim (a s) (b s)


private noncomputable def frontTop (ordinary binary : FrontSearch) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv ordinary l m g k t z v y) (Nat.beq ph 1)) true
      (node (binary (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)


private noncomputable def frontStart (ordinary binary : FrontSearch) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => frontTop ordinary binary l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

private noncomputable def frontRoot (ordinary binary : FrontSearch) (H ph : Nat) : Bool :=
  anySub (pos 1) 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 preparedStock 0 (fun r => frontStart ordinary binary 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 0x7ffefffdfffbfff7ffedbbbfff6eddfffb7ffedbfff76dffdddb6d6bffefffafffbffefffabffedfff5fff7ffdfff77ffc0000000000000001fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfffffffffffffffffff 0x842108421084210842108421084210842108421084210842108421084210 0xc6318c6318c62b7bdef7bdef7bdad7bdef7bce529ca53a52b6b5673b56b4 12 1 0 H ph r)

private noncomputable def binaryStep : FrontSearch := look1 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 0x7ffefffdfffbfff7ffedbbbfff6eddfffb7ffedbfff76dffdddb6d6bffefffafffbffefffabffedfff5fff7ffdfff77ffc0000000000000001fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfffffffffffffffffff 0x842108421084210842108421084210842108421084210842108421084210 12 12

private noncomputable def ordinaryStep : FrontSearch := look 0x1fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfff0000000000000000 0x7ffefffdfffbfff7ffedbbbfff6eddfffb7ffedbfff76dffdddb6d6bffefffafffbffefffabffedfff5fff7ffdfff77ffc0000000000000001fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfffffffffffffffffff 0x842108421084210842108421084210842108421084210842108421084210 12


private def frontMask : Nat := 0x7ffefffdfffbfff7ffedbbbfff6eddfffb7ffedbfff76dffdddb6d6bffefffafffbffefffabffedfff5fff7ffdfff77ffc0000000000000001fffbfff7ffefffdfffb6eefffdbb77ffedfffb6fffddb7ff776db5afffbffebffefffbffeafffb7ffd7ffdfff7ffddfffffffffffffffffff



private def frontInput0s : Nat := (preparedStock[0]'(by decide)).s

private def frontInput0a : Nat := (preparedStock[0]'(by decide)).a

private def frontInput0b : Nat := (preparedStock[0]'(by decide)).b


private def frontInput1s : Nat := (preparedStock[1]'(by decide)).s

private def frontInput1a : Nat := (preparedStock[1]'(by decide)).a

private def frontInput1b : Nat := (preparedStock[1]'(by decide)).b


private def frontInput2s : Nat := (preparedStock[2]'(by decide)).s

private def frontInput2a : Nat := (preparedStock[2]'(by decide)).a

private def frontInput2b : Nat := (preparedStock[2]'(by decide)).b

private def frontInput2c : Nat := (preparedStock[2]'(by decide)).c

private def frontInput3s : Nat := (preparedStock[3]'(by decide)).s

private def frontInput3a : Nat := (preparedStock[3]'(by decide)).a

private def frontInput3b : Nat := (preparedStock[3]'(by decide)).b

private def frontInput3c : Nat := (preparedStock[3]'(by decide)).c

private def frontInput4s : Nat := (preparedStock[4]'(by decide)).s

private def frontInput4a : Nat := (preparedStock[4]'(by decide)).a

private def frontInput4b : Nat := (preparedStock[4]'(by decide)).b

private def frontInput4c : Nat := (preparedStock[4]'(by decide)).c

private def frontInput5s : Nat := (preparedStock[5]'(by decide)).s

private def frontInput5a : Nat := (preparedStock[5]'(by decide)).a

private def frontInput5b : Nat := (preparedStock[5]'(by decide)).b

private def frontInput5c : Nat := (preparedStock[5]'(by decide)).c

private def fw0 : W := ⟨frontInput0s, frontInput0a, frontInput0b, ((preparedStock[0]'(by decide)).c : Nat), 3⟩

private def fw1 : W := ⟨frontInput1s, frontInput1a, frontInput1b, ((preparedStock[1]'(by decide)).c : Nat), 3⟩

private def fw2 : W := ⟨frontInput2s, frontInput2a, frontInput2b, frontInput2c, 3⟩

private def fw3 : W := ⟨frontInput3s, frontInput3a, frontInput3b, frontInput3c, 3⟩

private def fw4 : W := ⟨frontInput4s, frontInput4a, frontInput4b, frontInput4c, 3⟩

private def fw5 : W := ⟨frontInput5s, frontInput5a, frontInput5b, frontInput5c, 3⟩

private def fn28 : Nat := frontInput5s &&& frontInput4s

private def fn29 : Nat := frontInput5a + frontInput4a



private def front0_0 : List FrontKey := [(0xad673ad6b39ce759ceb59d6749ce759ceb59ce529ca539ce95a4e52ad251, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨fn28, fn29, 0, fn29, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_0_ok : ∀ s ∈ front0_0, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn31 : Nat := frontInput5s ||| frontInput4s

private def fn32 : Nat := frontInput5b + frontInput4b



private def front0_1 : List FrontKey := [(0xad694ad6b4a4e75a52b5a56939ca55a52b5a4e529ca539ce959ca52ad272, [fw0, fw1, fw2, fw3, (⟨fn31, 0, fn32, fn32, 0⟩ : W), fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_1_ok : ∀ s ∈ front0_1, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn34 : Nat := frontInput5s &&& frontInput3s

private def fn35 : Nat := frontInput5a + frontInput3a



private def front0_2 : List FrontKey := [(0xaceb3aceb59ce75aceb39d2759ce75aceb39ce529ca539ce94ace52aca91, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨fn34, fn35, 0, fn35, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_2_ok : ∀ s ∈ front0_2, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn37 : Nat := frontInput5s ||| frontInput3s

private def fn38 : Nat := frontInput5b + frontInput3b



private def front0_3 : List FrontKey := [(0xad2b4ad2b59d275ad2b4a4e75a4a55ad2b4a4e529ca539ce93aca52ace92, [fw0, fw1, fw2, (⟨fn37, 0, fn38, fn38, 0⟩ : W), fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_3_ok : ∀ s ∈ front0_3, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn40 : Nat := frontInput4s &&& frontInput3s

private def fn41 : Nat := fn35 ^^^ fn29



private def front0_4 : List FrontKey := [(0xace75aceb3a52759d6b3ad294a52959d6b3ace529ca539ce94a5252aca53, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨fn40, fn41, 0, fn41, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_4_ok : ∀ s ∈ front0_4, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn43 : Nat := frontInput4s ||| frontInput3s

private def fn44 : Nat := fn38 ^^^ fn32



private def front0_5 : List FrontKey := [(0xad295ad2b49ce75a56b4ace739d295a56b4ace529ca539ce939d252ace73, [fw0, fw1, fw2, (⟨fn43, 0, fn44, fn44, 0⟩ : W), fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_5_ok : ∀ s ∈ front0_5, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn46 : Nat := frontInput5s &&& frontInput2s

private def fn47 : Nat := frontInput5a + frontInput2a



private def front0_6 : List FrontKey := [(0x9d6b39d6759ce75aceb59d6759ce73ace759ce529ca539ce75ace529d291, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨fn46, fn47, 0, fn47, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_6_ok : ∀ s ∈ front0_6, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn49 : Nat := frontInput5s ||| frontInput2s

private def fn50 : Nat := frontInput5b + frontInput2b



private def front0_7 : List FrontKey := [(0xa56b4a5695a5275ad2b5a5695a4a54ad295a4e529ca539ce55aca52a5292, [fw0, fw1, (⟨fn49, 0, fn50, fn50, 0⟩ : W), fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_7_ok : ∀ s ∈ front0_7, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn52 : Nat := frontInput4s &&& frontInput2s

private def fn53 : Nat := fn47 ^^^ fn29



private def front0_8 : List FrontKey := [(0x9d6759d673ad2759d6b5ad6b4a52939d675ace529ca539ce75a52529d253, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨fn52, fn53, 0, fn53, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_8_ok : ∀ s ∈ front0_8, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn55 : Nat := frontInput4s ||| frontInput2s

private def fn56 : Nat := fn50 ^^^ fn32



private def front0_9 : List FrontKey := [(0xa5695a5694ace75a56b5ad6b39d294a5695ace529ca539ce559d252a5273, [fw0, fw1, (⟨fn55, 0, fn56, fn56, 0⟩ : W), fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_9_ok : ∀ s ∈ front0_9, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn58 : Nat := frontInput3s &&& frontInput2s

private def fn59 : Nat := fn47 ^^^ fn35



private def front0_10 : List FrontKey := [(0x9ceb59ce75a5675ad6b3ad295ad293ad673ace529ca539ce74ad2529ca93, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨fn58, fn59, 0, fn59, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_10_ok : ∀ s ∈ front0_10, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn61 : Nat := frontInput3s ||| frontInput2s

private def fn62 : Nat := fn50 ^^^ fn38



private def front0_11 : List FrontKey := [(0xa52b5a52959d675ad6b4ace75ad294ad694ace529ca539ce53ad252a4e93, [fw0, fw1, (⟨fn61, 0, fn62, fn62, 0⟩ : W), fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_11_ok : ∀ s ∈ front0_11, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn64 : Nat := frontInput5s &&& frontInput1s

private def fn65 : Nat := frontInput5a ||| frontInput1a



private def front0_12 : List FrontKey := [(0xa52939ce949ce53ace949d6739ce55ace739ce529ca539ca95ace50ad291, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨fn64, fn65, 0, fn65, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_12_ok : ∀ s ∈ front0_12, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn67 : Nat := frontInput5s ||| frontInput1s

private def fn68 : Nat := fn29 &&& frontInput1a

private def fn69 : Nat := frontInput5b + frontInput1b




private def front0_13 : List FrontKey := [(0x9ce73a5273a4e34ad2739d694a4a55ad2949ce529ca539c695aca51ad292, [fw0, (⟨fn67, fn68, fn69, (fn69 + fn68 : Nat), 0⟩ : W), fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_13_ok : ∀ s ∈ front0_13, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn72 : Nat := frontInput4s &&& frontInput1s

private def fn73 : Nat := frontInput4a + frontInput1a


private def fn74 : Nat := 0xa52749ce93ace539d694a56b3a52559d6739ce529ca539ca95a5250ad253

private def front0_14 : List FrontKey := [(fn74, [fw0, fw1, fw2, fw3, fw4, (⟨fn72, fn73, 0, fn73, 0⟩ : W), fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_14_ok : ∀ s ∈ front0_14, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn75 : Nat := frontInput4s ||| frontInput1s

private def fn76 : Nat := fn69 ^^^ fn32



private def front0_15 : List FrontKey := [(0x9ce73a5273ace34a56739d6b39d275a5694a4e529ca539c6959d251ad273, [fw0, (⟨fn75, 0, fn76, fn76, 0⟩ : W), fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_15_ok : ∀ s ∈ front0_15, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn78 : Nat := frontInput3s &&& frontInput1s

private def fn79 : Nat := frontInput3a ||| frontInput1a


private def fn80 : Nat := 0xa4e949ce94a4e53ad693a5293ad255ad6739ce529ca539ca94ad250aca93

private def front0_16 : List FrontKey := [(fn80, [fw0, fw1, fw2, fw3, (⟨fn78, fn79, 0, fn79, 0⟩ : W), fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_16_ok : ∀ s ∈ front0_16, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn81 : Nat := frontInput3s ||| frontInput1s

private def fn82 : Nat := fn65 &&& fn41

private def fn83 : Nat := fn69 ^^^ fn38




private def front0_17 : List FrontKey := [(0x9ce73a4e739d234ad6739ce74ad275ad693a4e529ca539c693ad251ace93, [fw0, (⟨fn81, fn82, fn83, (fn83 + fn82 : Nat), 0⟩ : W), fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_17_ok : ∀ s ∈ front0_17, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn86 : Nat := frontInput2s &&& frontInput1s

private def fn87 : Nat := frontInput2a ||| frontInput1a



private def front0_18 : List FrontKey := [(0x9d2949ce74ace53ad694a56b3ad253ad6739ce529ca539ca75ad2509d293, [fw0, fw1, fw2, (⟨fn86, fn87, 0, fn87, 0⟩ : W), fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_18_ok : ∀ s ∈ front0_18, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn89 : Nat := frontInput2s ||| frontInput1s

private def fn90 : Nat := fn65 &&& fn53

private def fn91 : Nat := fn69 ^^^ fn50




private def front0_19 : List FrontKey := [(0x9ce739d273ad234ad6739d6b4ad274ad674a4e529ca539c655ad251a5293, [fw0, (⟨fn89, fn90, fn91, (fn91 + fn90 : Nat), 0⟩ : W), fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_19_ok : ∀ s ∈ front0_19, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn94 : Nat := frontInput5s &&& frontInput0s

private def fn95 : Nat := frontInput5a ||| frontInput0a



private def front0_20 : List FrontKey := [(0xa5293a52739ce54a4e759ce759ca739ceb59ce529ca5394e95ace12ad291, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨fn94, fn95, 0, fn95, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_20_ok : ∀ s ∈ front0_20, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn97 : Nat := frontInput5s ||| frontInput0s

private def fn98 : Nat := fn35 &&& frontInput0a

private def fn99 : Nat := frontInput5b + frontInput0b




private def front0_21 : List FrontKey := [(0x9ce739ce949d2339ce95a5295a4a54a4eb5a4e529ca538ce95aca32ad292, [(⟨fn97, fn98, fn99, (fn99 + fn98 : Nat), 0⟩ : W), fw0, fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_21_ok : ∀ s ∈ front0_21, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn102 : Nat := frontInput4s &&& frontInput0s

private def fn103 : Nat := frontInput4a ||| frontInput0a


private def fn104 : Nat := 0xa5274a52739d2549d275aceb4a4a939ceb5ace529ca5394e95a5212ad253

private def front0_22 : List FrontKey := [(fn104, [fw0, fw1, fw2, fw3, fw4, (⟨fn102, fn103, 0, fn103, 0⟩ : W), fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_22_ok : ∀ s ∈ front0_22, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn105 : Nat := frontInput4s ||| frontInput0s

private def fn106 : Nat := fn41 &&& fn40

private def fn107 : Nat := fn99 ^^^ fn32




private def front0_23 : List FrontKey := [(0x9ce739ce93a4e339ce95ad2b39ce949d2b5ace529ca538ce959d232ad273, [(⟨fn105, fn106, fn107, (fn107 + fn106 : Nat), 0⟩ : W), fw0, fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_23_ok : ∀ s ∈ front0_23, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn110 : Nat := frontInput3s &&& frontInput0s

private def fn111 : Nat := frontInput3a + frontInput0a


private def fn112 : Nat := 0xa4e94a4e739d654a5273ace95aca939ceb3ace529ca5394e94ad212aca93

private def front0_24 : List FrontKey := [(fn112, [fw0, fw1, fw2, fw3, (⟨fn110, fn111, 0, fn111, 0⟩ : W), fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_24_ok : ∀ s ∈ front0_24, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn113 : Nat := frontInput3s ||| frontInput0s

private def fn114 : Nat := fn99 ^^^ fn38



private def front0_25 : List FrontKey := [(0x9ce739ce949d6339ce94ace75ace94a52b4ace529ca538ce93ad232ace93, [(⟨fn113, 0, fn114, fn114, 0⟩ : W), fw0, fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_25_ok : ∀ s ∈ front0_25, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn116 : Nat := frontInput2s &&& frontInput0s

private def fn117 : Nat := frontInput2a ||| frontInput0a


private def fn118 : Nat := 0x9d2949d2739d654a5275aceb5aca939ce75ace529ca5394e75ad2129d293

private def front0_26 : List FrontKey := [(fn118, [fw0, fw1, fw2, (⟨fn116, fn117, 0, fn117, 0⟩ : W), fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_26_ok : ∀ s ∈ front0_26, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn119 : Nat := frontInput2s ||| frontInput0s

private def fn120 : Nat := fn95 &&& fn59

private def fn121 : Nat := fn99 ^^^ fn50




private def front0_27 : List FrontKey := [(0x9ce739ce74a56339ce95ad2b5ace93a5295ace529ca538ce55ad232a5293, [(⟨fn119, fn120, fn121, (fn121 + fn120 : Nat), 0⟩ : W), fw0, fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_27_ok : ∀ s ∈ front0_27, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn124 : Nat := frontInput1s &&& frontInput0s

private def fn125 : Nat := frontInput1a + frontInput0a

private def fn126 : Nat := fn99 &&& fn76




private def front0_28 : List FrontKey := [(0x9ce739ce739ce33a5274a4eb3aca539ce739ce529ca5394a95ad210ad293, [fw0, fw1, (⟨fn124, fn125, fn126, (fn126 + fn125 : Nat), 0⟩ : W), fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_28_ok : ∀ s ∈ front0_28, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn130 : Nat := frontInput1b ||| frontInput0b



private def front0_29 : List FrontKey := [(0x9ce739ce73a52339ce739d2b4ace74a5294a4e529ca538c695ad231ad293, [(⟨(frontInput1s ||| frontInput0s : Nat), 0, fn130, fn130, 0⟩ : W), fw0, fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front0_29_ok : ∀ s ∈ front0_29, binaryStep 11 1 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def checkedFront0 : List FrontKey := front0_0 ++ (front0_1 ++ (front0_2 ++ (front0_3 ++ (front0_4 ++ (front0_5 ++ (front0_6 ++ (front0_7 ++ (front0_8 ++ (front0_9 ++ (front0_10 ++ (front0_11 ++ (front0_12 ++ (front0_13 ++ (front0_14 ++ (front0_15 ++ (front0_16 ++ (front0_17 ++ (front0_18 ++ (front0_19 ++ (front0_20 ++ (front0_21 ++ (front0_22 ++ (front0_23 ++ (front0_24 ++ (front0_25 ++ (front0_26 ++ (front0_27 ++ (front0_28 ++ (front0_29)))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checkedFront0_ok : ∀ s ∈ checkedFront0, binaryStep 11 1 s.1 s.2 = false :=
  frontAppend front0_0_ok (frontAppend front0_1_ok (frontAppend front0_2_ok (frontAppend front0_3_ok (frontAppend front0_4_ok (frontAppend front0_5_ok (frontAppend front0_6_ok (frontAppend front0_7_ok (frontAppend front0_8_ok (frontAppend front0_9_ok (frontAppend front0_10_ok (frontAppend front0_11_ok (frontAppend front0_12_ok (frontAppend front0_13_ok (frontAppend front0_14_ok (frontAppend front0_15_ok (frontAppend front0_16_ok (frontAppend front0_17_ok (frontAppend front0_18_ok (frontAppend front0_19_ok (frontAppend front0_20_ok (frontAppend front0_21_ok (frontAppend front0_22_ok (frontAppend front0_23_ok (frontAppend front0_24_ok (frontAppend front0_25_ok (frontAppend front0_26_ok (frontAppend front0_27_ok (frontAppend front0_28_ok (front0_29_ok)))))))))))))))))))))))))))))


private def fn133 : Nat := fn29 ^^^ frontInput5c

private def fn134 : Nat := fn32 &&& fn29

private def fn135 : Nat := fn134 + fn133

private def fw36 : W := ⟨(frontInput4s - fn28 : Nat), fn133, fn134, fn135, 0⟩

private def fn136 : Nat := 0xad673ad6b39ca759ceb59d674946359ceb59ce529ca539ce95a4652ad251

private def fn137 : Nat := frontMask - frontInput5s

private def fw37 : W := ⟨fn137, frontInput5b, frontInput5a, frontInput5c, 0⟩


private def fn139 : Nat := fn137 + fn28

private def fn140 : Nat := frontInput5a ||| frontInput4b




private def fn143 : Nat := fn133 ^^^ fn41

private def fn144 : Nat := fn38 &&& fn29

private def fn145 : Nat := fn144 + fn143

private def fw39 : W := ⟨(fn137 &&& fn37 : Nat), fn143, fn144, fn145, 0⟩

private def fn146 : Nat := 0xaceb3aceb594e75aceb39d2559c635aceb39ce529ca539ce94ac652aca91

private def front1_0 : List FrontKey := [(fn136, [fw0, fw1, fw2, fw3, fw4, fw36, fw5]), ((fn136 - frontInput5c : Nat), [fw0, fw1, fw37, fw2, fw3, fw4, fw36, fw5]), (0xad692ad6b494a75a4ab59565394a55a4ab594e529ca539ce959ca52ad270, [fw0, fw1, (⟨fn139, 0, fn140, fn140, 0⟩ : W), fw2, fw3, fw4, fw5]), (fn146, [fw0, fw1, fw2, fw3, fw39, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_0_ok : ∀ s ∈ front1_0, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn148 : Nat := fn137 + fn34

private def fn149 : Nat := frontInput5a ||| frontInput3b




private def fn152 : Nat := fn133 ^^^ fn53

private def fw41 : W := ⟨(fn137 &&& fn49 : Nat), fn152, 0, fn152, 0⟩

private def fn153 : Nat := 0x9d6b39d6759ce75aceb59d6759c633ace759ce529ca539ce75ac6529d291


private def front1_4 : List FrontKey := [((fn146 - frontInput5c : Nat), [fw0, fw1, fw37, fw2, fw3, fw39, fw4, fw5]), (0xad2b2ad2b594a75acab494e5594a55acab494e529ca539ce93aca52ace90, [fw0, fw1, (⟨fn148, 0, fn149, fn149, 0⟩ : W), fw2, fw3, fw4, fw5]), (fn153, [fw0, fw1, fw2, fw41, fw3, fw4, fw5]), ((fn153 - frontInput5c : Nat), [fw0, fw1, fw37, fw2, fw41, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_4_ok : ∀ s ∈ front1_4, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn155 : Nat := fn137 + fn46

private def fn156 : Nat := fn47 ^^^ frontInput2c




private def fn159 : Nat := frontInput5b ||| frontInput1a

private def fn160 : Nat := fn91 &&& fn65


private def fw43 : W := ⟨(fn137 &&& fn67 : Nat), fn159, fn160, (fn160 + fn159 : Nat), 0⟩

private def fn162 : Nat := 0xa52929ce949ca53ace94956739c635ace7394e529ca539ca95ac650ad291


private def fn164 : Nat := fn137 + fn64

private def fn165 : Nat := fn65 &&& fn50

private def fn166 : Nat := frontInput5a ||| frontInput1b

private def fn167 : Nat := fn166 + fn165



private def front1_8 : List FrontKey := [(0xa56b2a569594a75acab59565594a54aca9594e529ca539ce55aca52a5290, [fw0, fw1, (⟨fn155, 0, fn156, fn156, 0⟩ : W), fw2, fw3, fw4, fw5]), (fn162, [fw0, fw1, fw43, fw2, fw3, fw4, fw5]), ((fn162 - frontInput5c : Nat), [fw0, fw1, fw37, fw43, fw2, fw3, fw4, fw5]), (0x9ce72a527394a34aca739565494a35aca9494e529ca539c695aca51ad290, [fw0, (⟨fn164, fn165, fn166, fn167, 0⟩ : W), fw1, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_8_ok : ∀ s ∈ front1_8, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn170 : Nat := frontInput5b ||| frontInput0a

private def fn171 : Nat := fn121 &&& fn95


private def fw45 : W := ⟨(fn137 &&& fn97 : Nat), fn170, fn171, (fn171 + fn170 : Nat), 0⟩

private def fn173 : Nat := 0xa5292a527394e54a4a759ce759c6339cab59ce529ca5394e95ac612ad291


private def fn175 : Nat := fn137 + fn94

private def fn176 : Nat := fn46 &&& fn38

private def fn177 : Nat := frontInput5a ||| frontInput0b

private def fn178 : Nat := fn177 + fn176




private def fw47 : W := ⟨(frontMask - fn139 : Nat), fn140, 0, fn140, 0⟩

private def fn181 : Nat := 0xad673ad6b39ca759ceb59d67294e759ceb59ce529ca539ce9594e52ad251

private def front1_12 : List FrontKey := [(fn173, [fw0, fw1, fw45, fw2, fw3, fw4, fw5]), ((fn173 - frontInput5c : Nat), [fw0, fw1, fw37, fw45, fw2, fw3, fw4, fw5]), (0x9ce729ce9494a339ca959525594654a4ab594e529ca538ce95aca32ad290, [(⟨fn175, fn176, fn177, fn178, 0⟩ : W), fw0, fw1, fw2, fw3, fw4, fw5]), (fn181, [fw0, fw1, fw2, fw3, fw4, fw5, fw47])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_12_ok : ∀ s ∈ front1_12, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn182 : Nat := fn139 ^^^ fn31

private def fw48 : W := ⟨fn182, frontInput4b, frontInput4a, frontInput4c, 0⟩



private def fw49 : W := ⟨(fn182 + fn28 : Nat), fn134, fn133, fn135, 0⟩

private def fn185 : Nat := 0xad654ad6b2a4a75952b5a569394a55952b5a4e529ca539ce959ca52ad232



private def fn188 : Nat := fn143 ^^^ fn32

private def fw50 : W := ⟨(fn182 &&& fn43 : Nat), fn188, 0, fn188, 0⟩

private def fn189 : Nat := 0xace75aceb3a4a759d6b3ad292952959d6b3ace529ca539ce9495252aca53

private def front1_16 : List FrontKey := [((fn181 - frontInput4c : Nat), [fw0, fw1, fw48, fw2, fw3, fw4, fw5, fw47]), (fn185, [fw0, fw1, fw49, fw2, fw3, fw4, fw5]), ((fn185 - frontInput4c : Nat), [fw0, fw1, fw49, fw48, fw2, fw3, fw4, fw5]), (fn189, [fw0, fw1, fw2, fw3, fw50, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_16_ok : ∀ s ∈ front1_16, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)



private def fn192 : Nat := fn133 ^^^ fn38

private def fw51 : W := ⟨(fn182 + fn40 : Nat), 0, fn192, fn192, 0⟩

private def fn193 : Nat := 0xad255ad2b29ce75956b4ace739d295956b4ace529ca539ce939d252ace33



private def fn196 : Nat := fn152 ^^^ fn32

private def fw52 : W := ⟨(fn182 &&& fn55 : Nat), fn196, 0, fn196, 0⟩

private def fn197 : Nat := 0x9d6759d673aca759d6b5ad6b2952939d675ace529ca539ce75952529d253

private def front1_20 : List FrontKey := [((fn189 - frontInput4c : Nat), [fw0, fw1, fw48, fw2, fw3, fw50, fw4, fw5]), (fn193, [fw0, fw1, fw51, fw2, fw3, fw4, fw5]), ((fn193 - frontInput4c : Nat), [fw0, fw1, fw51, fw48, fw2, fw3, fw4, fw5]), (fn197, [fw0, fw1, fw2, fw52, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_20_ok : ∀ s ∈ front1_20, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)



private def fn200 : Nat := fn133 ^^^ fn50

private def fw53 : W := ⟨(fn182 + fn52 : Nat), 0, fn200, fn200, 0⟩

private def fn201 : Nat := 0xa5655a5692ace75956b5ad6b39d29495695ace529ca539ce559d252a5233



private def fn204 : Nat := frontInput4b ||| frontInput1a

private def fn205 : Nat := fn74 &&& fn69


private def fw54 : W := ⟨(fn182 &&& fn75 : Nat), fn204, fn205, (fn205 + fn204 : Nat), 0⟩

private def fn207 : Nat := 0xa52549ce92aca539d694a56b2952559d6739ce529ca539ca9595250ad253

private def front1_24 : List FrontKey := [((fn197 - frontInput4c : Nat), [fw0, fw1, fw48, fw2, fw52, fw3, fw4, fw5]), (fn201, [fw0, fw1, fw53, fw2, fw3, fw4, fw5]), ((fn201 - frontInput4c : Nat), [fw0, fw1, fw53, fw48, fw2, fw3, fw4, fw5]), (fn207, [fw0, fw1, fw54, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_24_ok : ∀ s ∈ front1_24, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn209 : Nat := fn182 + fn72

private def fn210 : Nat := fn73 &&& fn44

private def fn211 : Nat := frontInput4a ||| frontInput1b

private def fn212 : Nat := fn211 + fn210

private def fw55 : W := ⟨fn209, fn210, fn211, fn212, 0⟩

private def fn213 : Nat := 0x9ce53a5272aca34956739d6b29d27595694a4e529ca539c6959d251ad233



private def fn216 : Nat := fn188 ^^^ fn111

private def fn217 : Nat := fn104 &&& fn99


private def fw56 : W := ⟨(fn182 &&& fn105 : Nat), fn216, fn217, (fn217 + fn216 : Nat), 0⟩

private def fn219 : Nat := 0xa5254a52729ca5495275aceb294a9394eb5ace529ca5394e9595212ad253

private def front1_28 : List FrontKey := [((fn207 - frontInput4c : Nat), [fw0, fw1, fw48, fw54, fw2, fw3, fw4, fw5]), (fn213, [fw0, fw55, fw1, fw2, fw3, fw4, fw5]), ((fn213 - frontInput4c : Nat), [fw0, fw55, fw1, fw48, fw2, fw3, fw4, fw5]), (fn219, [fw0, fw1, fw56, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_28_ok : ∀ s ∈ front1_28, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn221 : Nat := fn182 + fn102

private def fn222 : Nat := frontInput4a ||| frontInput0b

private def fw57 : W := ⟨fn221, 0, fn222, fn222, 0⟩

private def fn223 : Nat := 0x9ce539ce92a4e3394e95ad2b39ce94952b5ace529ca538ce959d232ad233



private def fw58 : W := ⟨(frontMask - fn148 : Nat), fn149, 0, fn149, 0⟩

private def fn226 : Nat := 0xaceb3aceb594e75aceb39ca559ce75aceb39ce529ca539ce92ace52aca91

private def front1_32 : List FrontKey := [((fn219 - frontInput4c : Nat), [fw0, fw1, fw48, fw56, fw2, fw3, fw4, fw5]), (fn223, [fw57, fw0, fw1, fw2, fw3, fw4, fw5]), ((fn223 - frontInput4c : Nat), [fw57, fw0, fw1, fw48, fw2, fw3, fw4, fw5]), (fn226, [fw0, fw1, fw2, fw3, fw4, fw5, fw58])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_32_ok : ∀ s ∈ front1_32, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn227 : Nat := fn148 ^^^ fn37

private def fw59 : W := ⟨fn227, frontInput3b, frontInput3a, frontInput3c, 0⟩



private def fw60 : W := ⟨(fn227 + fn34 : Nat), fn144, fn143, fn145, 0⟩

private def fn230 : Nat := 0xacab4acab595275ad2b2a4e55a4a55ad2b2a4e529ca539ce93aca52ac692



private def fw61 : W := ⟨(fn227 &&& fn43 : Nat), fn192, 0, fn192, 0⟩

private def fn233 : Nat := 0xace75aceb3952759d6b3aca54a52959d6b3ace529ca539ce92a5252aca53

private def front1_36 : List FrontKey := [((fn226 - frontInput3c : Nat), [fw0, fw1, fw59, fw2, fw3, fw4, fw5, fw58]), (fn230, [fw0, fw1, fw60, fw2, fw3, fw4, fw5]), ((fn230 - frontInput3c : Nat), [fw0, fw1, fw60, fw59, fw2, fw3, fw4, fw5]), (fn233, [fw0, fw1, fw2, fw3, fw4, fw61, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_36_ok : ∀ s ∈ front1_36, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)



private def fw62 : W := ⟨(fn227 + fn40 : Nat), 0, fn188, fn188, 0⟩

private def fn236 : Nat := 0xaca95acab49ce75a56b2ace739d295a56b2ace529ca539ce939d252ac673



private def fn239 : Nat := fn152 ^^^ fn38

private def fw63 : W := ⟨(fn227 &&& fn61 : Nat), fn239, 0, fn239, 0⟩

private def fn240 : Nat := 0x9ceb59ce7595675ad6b3aca55ad293ad673ace529ca539ce72ad2529ca93

private def front1_40 : List FrontKey := [((fn233 - frontInput3c : Nat), [fw0, fw1, fw59, fw2, fw3, fw4, fw61, fw5]), (fn236, [fw0, fw1, fw62, fw2, fw3, fw4, fw5]), ((fn236 - frontInput3c : Nat), [fw0, fw1, fw62, fw59, fw2, fw3, fw4, fw5]), (fn240, [fw0, fw1, fw2, fw63, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_40_ok : ∀ s ∈ front1_40, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)



private def fn243 : Nat := fn143 ^^^ fn50

private def fw64 : W := ⟨(fn227 + fn58 : Nat), 0, fn243, fn243, 0⟩

private def fn244 : Nat := 0xa4ab5a4a959d675ad6b2ace75ad294ad692ace529ca539ce53ad252a4693



private def fn247 : Nat := fn192 ^^^ fn73

private def fn248 : Nat := fn80 &&& fn69


private def fw65 : W := ⟨(fn227 &&& fn81 : Nat), fn247, fn248, (fn248 + fn247 : Nat), 0⟩

private def fn250 : Nat := 0xa4a949ca9494e53ad692a4a53ad255ad6729ce529ca539ca92ad250aca93

private def front1_44 : List FrontKey := [((fn240 - frontInput3c : Nat), [fw0, fw1, fw59, fw2, fw63, fw3, fw4, fw5]), (fn244, [fw0, fw1, fw64, fw2, fw3, fw4, fw5]), ((fn244 - frontInput3c : Nat), [fw0, fw1, fw64, fw59, fw2, fw3, fw4, fw5]), (fn250, [fw0, fw1, fw65, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_44_ok : ∀ s ∈ front1_44, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn252 : Nat := fn227 + fn78

private def fn253 : Nat := frontInput3a ||| frontInput1b

private def fw66 : W := ⟨fn252, 0, fn253, fn253, 0⟩

private def fn254 : Nat := 0x9ca73a4a739d234ad6729ce74ad275ad692a4e529ca539c693ad251ac693



private def fn257 : Nat := frontInput3b ||| frontInput0a

private def fn258 : Nat := fn112 &&& fn99


private def fw67 : W := ⟨(fn227 &&& fn113 : Nat), fn257, fn258, (fn258 + fn257 : Nat), 0⟩

private def fn260 : Nat := 0xa4a94a4a7395654a5273aca55aca939ceb3ace529ca5394e92ad212aca93

private def front1_48 : List FrontKey := [((fn250 - frontInput3c : Nat), [fw0, fw1, fw59, fw65, fw2, fw3, fw4, fw5]), (fn254, [fw0, fw66, fw1, fw2, fw3, fw4, fw5]), ((fn254 - frontInput3c : Nat), [fw0, fw66, fw1, fw59, fw2, fw3, fw4, fw5]), (fn260, [fw0, fw1, fw67, fw2, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_48_ok : ∀ s ∈ front1_48, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn262 : Nat := fn227 + fn110

private def fn263 : Nat := fn103 &&& fn44

private def fn264 : Nat := frontInput3a ||| frontInput0b

private def fn265 : Nat := fn264 + fn263

private def fw68 : W := ⟨fn262, fn263, fn264, fn265, 0⟩

private def fn266 : Nat := 0x9ca739ca94956339ce92aca75ace94a52b2ace529ca538ce93ad232ac693



private def fw69 : W := ⟨(frontMask - fn155 : Nat), fn156, 0, fn156, 0⟩

private def fn269 : Nat := 0x9d6b39d6759ce75aceb59d6759ce73ace759ce529ca539ce35ace529d291

private def front1_52 : List FrontKey := [((fn260 - frontInput3c : Nat), [fw0, fw1, fw59, fw67, fw2, fw3, fw4, fw5]), (fn266, [fw68, fw0, fw1, fw2, fw3, fw4, fw5]), ((fn266 - frontInput3c : Nat), [fw68, fw0, fw1, fw59, fw2, fw3, fw4, fw5]), (fn269, [fw0, fw1, fw2, fw3, fw4, fw5, fw69])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_52_ok : ∀ s ∈ front1_52, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def fn270 : Nat := fn155 ^^^ fn49

private def fw70 : W := ⟨fn270, frontInput2b, frontInput2a, frontInput2c, 0⟩



private def fw71 : W := ⟨(fn270 + fn46 : Nat), 0, fn152, fn152, 0⟩

private def fn273 : Nat := 0x956b495655a5275ad2b5a5695a4a52ad255a4e529ca539ce55aca5295292



private def fw72 : W := ⟨(fn270 &&& fn55 : Nat), fn200, 0, fn200, 0⟩

private def fn276 : Nat := 0x9d6759d673ad2759d6b5ad6b4a52939d675ace529ca539ce35a52529d253

private def front1_56 : List FrontKey := [((fn269 - frontInput2c : Nat), [fw0, fw1, fw2, fw70, fw3, fw4, fw5, fw69]), (fn273, [fw0, fw1, fw2, fw71, fw3, fw4, fw5]), ((fn273 - frontInput2c : Nat), [fw0, fw1, fw2, fw71, fw70, fw3, fw4, fw5]), (fn276, [fw0, fw1, fw2, fw3, fw4, fw72, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_56_ok : ∀ s ∈ front1_56, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)



private def fw73 : W := ⟨(fn270 + fn52 : Nat), 0, fn196, fn196, 0⟩

private def fn279 : Nat := 0x9569595654ace75a56b5ad6b39d292a5655ace529ca539ce559d25295273



private def fw74 : W := ⟨(fn270 &&& fn61 : Nat), fn243, 0, fn243, 0⟩

private def fn282 : Nat := 0x9ceb59ce75a5675ad6b3ad295ad293ad673ace529ca539ce34ad2529ca93

private def front1_60 : List FrontKey := [((fn276 - frontInput2c : Nat), [fw0, fw1, fw2, fw70, fw3, fw4, fw72, fw5]), (fn279, [fw0, fw1, fw2, fw73, fw3, fw4, fw5]), ((fn279 - frontInput2c : Nat), [fw0, fw1, fw2, fw73, fw70, fw3, fw4, fw5]), (fn282, [fw0, fw1, fw2, fw3, fw74, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_60_ok : ∀ s ∈ front1_60, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)



private def fw75 : W := ⟨(fn270 + fn58 : Nat), 0, fn239, fn239, 0⟩

private def fn285 : Nat := 0x952b5952559d675ad6b4ace75ad292ad654ace529ca539ce53ad25294e93



private def fn288 : Nat := fn200 ^^^ fn73

private def fn289 : Nat := fn83 &&& fn46


private def fw76 : W := ⟨(fn270 &&& fn89 : Nat), fn288, fn289, (fn289 + fn288 : Nat), 0⟩

private def fn291 : Nat := 0x9529494e54ace53ad694a56b3ad253ad6539ce529ca539ca35ad2509d293

private def front1_64 : List FrontKey := [((fn282 - frontInput2c : Nat), [fw0, fw1, fw2, fw70, fw3, fw74, fw4, fw5]), (fn285, [fw0, fw1, fw2, fw75, fw3, fw4, fw5]), ((fn285 - frontInput2c : Nat), [fw0, fw1, fw2, fw75, fw70, fw3, fw4, fw5]), (fn291, [fw0, fw1, fw2, fw76, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_64_ok : ∀ s ∈ front1_64, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn293 : Nat := fn270 + fn86

private def fn294 : Nat := frontInput2a ||| frontInput1b

private def fw77 : W := ⟨fn293, 0, fn294, fn294, 0⟩

private def fn295 : Nat := 0x94e7395253ad234ad6739d6b4ad272ad654a4e529ca539c655ad25195293



private def fn298 : Nat := fn216 ^^^ fn56

private def fn299 : Nat := fn118 &&& fn99


private def fw78 : W := ⟨(fn270 &&& fn119 : Nat), fn298, fn299, (fn299 + fn298 : Nat), 0⟩

private def fn301 : Nat := 0x95294952539d654a5275aceb5aca929ce75ace529ca5394e35ad2129d293

private def front1_68 : List FrontKey := [((fn291 - frontInput2c : Nat), [fw0, fw1, fw2, fw70, fw76, fw3, fw4, fw5]), (fn295, [fw0, fw77, fw1, fw2, fw3, fw4, fw5]), ((fn295 - frontInput2c : Nat), [fw0, fw77, fw1, fw2, fw70, fw3, fw4, fw5]), (fn301, [fw0, fw1, fw2, fw78, fw3, fw4, fw5])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_68_ok : ∀ s ∈ front1_68, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn303 : Nat := fn270 + fn116

private def fn304 : Nat := frontInput2a ||| frontInput0b

private def fw79 : W := ⟨fn303, 0, fn304, fn304, 0⟩

private def fn305 : Nat := 0x94e7394e54a56339ce95ad2b5ace92a5255ace529ca538ce55ad23295293





private def front1_72 : List FrontKey := [((fn301 - frontInput2c : Nat), [fw0, fw1, fw2, fw70, fw78, fw3, fw4, fw5]), (fn305, [fw79, fw0, fw1, fw2, fw3, fw4, fw5]), ((fn305 - frontInput2c : Nat), [fw79, fw0, fw1, fw2, fw70, fw3, fw4, fw5]), (0x94a529ce529ca13ace52956739ce35ace7394e529ca539c295ace50ad291, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontMask - fn164 : Nat), fn166, fn165, fn167, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_72_ok : ∀ s ∈ front1_72, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)











private def fn316 : Nat := frontInput1b ||| frontInput0a

private def fn317 : Nat := fn94 &&& fn79




private def front1_76 : List FrontKey := [(0x94a529ce52aca139d652956b2a52559d6739ce529ca539c295a5250ad253, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontMask - fn209 : Nat), fn211, fn210, fn212, 0⟩ : W)]), (0x94a529ca52a4e13ad65295293ad255ad6729ce529ca539c294ad250aca93, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontMask - fn252 : Nat), fn253, 0, fn253, 0⟩ : W)]), (0x94a5294e52ace13ad652956b3ad253ad6539ce529ca539c275ad2509d293, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontMask - fn293 : Nat), fn294, 0, fn294, 0⟩ : W)]), (0x94a5294a529ce12a525294eb3aca539ce739ce529ca5394295ad210ad293, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontInput0s - fn124 : Nat), fn316, fn317, (fn317 + fn316 : Nat), 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_76_ok : ∀ s ∈ front1_76, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)













private def front1_80 : List FrontKey := [(0x94a5294a7394e1294a759ce759c6739cab59ce529ca5384e95ace12ad291, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontMask - fn175 : Nat), fn177, fn176, fn178, 0⟩ : W)]), (0x94a5294a729d21294a75aceb4a4a9394eb5ace529ca5384e95a5212ad253, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontMask - fn221 : Nat), fn222, 0, fn222, 0⟩ : W)]), (0x94a5294a739561294a73aca95aca939ceb3ace529ca5384e94ad212aca93, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontMask - fn262 : Nat), fn264, fn263, fn265, 0⟩ : W)]), (0x94a5294a539d61294a75aceb5aca929ce75ace529ca5384e75ad2129d293, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontMask - fn303 : Nat), fn304, 0, fn304, 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_80_ok : ∀ s ∈ front1_80, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)


private def fn329 : Nat := frontInput1a ||| frontInput0b

private def fn330 : Nat := fn125 &&& fn91




private def front1_84 : List FrontKey := [(0x94a5294a529ce1294a54a4eb3aca539ce739ce529ca5384a95ad210ad293, [fw0, fw1, fw2, fw3, fw4, fw5, (⟨(frontInput1s - fn124 : Nat), fn329, fn330, (fn330 + fn329 : Nat), 0⟩ : W)])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem front1_84_ok : ∀ s ∈ front1_84, ordinaryStep 10 0 s.1 s.2 = false :=
  frontBlock (by decide +kernel)

private def checkedFront1 : List FrontKey := front1_0 ++ (front1_4 ++ (front1_8 ++ (front1_12 ++ (front1_16 ++ (front1_20 ++ (front1_24 ++ (front1_28 ++ (front1_32 ++ (front1_36 ++ (front1_40 ++ (front1_44 ++ (front1_48 ++ (front1_52 ++ (front1_56 ++ (front1_60 ++ (front1_64 ++ (front1_68 ++ (front1_72 ++ (front1_76 ++ (front1_80 ++ (front1_84)))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checkedFront1_ok : ∀ s ∈ checkedFront1, ordinaryStep 10 0 s.1 s.2 = false :=
  frontAppend front1_0_ok (frontAppend front1_4_ok (frontAppend front1_8_ok (frontAppend front1_12_ok (frontAppend front1_16_ok (frontAppend front1_20_ok (frontAppend front1_24_ok (frontAppend front1_28_ok (frontAppend front1_32_ok (frontAppend front1_36_ok (frontAppend front1_40_ok (frontAppend front1_44_ok (frontAppend front1_48_ok (frontAppend front1_52_ok (frontAppend front1_56_ok (frontAppend front1_60_ok (frontAppend front1_64_ok (frontAppend front1_68_ok (frontAppend front1_72_ok (frontAppend front1_76_ok (frontAppend front1_80_ok (front1_84_ok)))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem frontComplete :
    frontRoot (skipProved ordinaryStep checkedFront1 10 0)
      (skipProved binaryStep checkedFront0 11 1) FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k12t1ok : chk [] rt 0 12 1 FF 1 = false := by
  rw [prepared_eq12]
  change frontRoot ordinaryStep binaryStep FF 1 = false
  simpa only [skipProved_eq checkedFront1_ok, skipProved_eq checkedFront0_ok] using frontComplete
lemma k12t1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 1 p.1 p.2 = false :=
  one k12t1ok

private theorem canon_not_wire {m : ℕ} (hm : m &&& Free.fullMask = Free.fullMask) (a : ℕ) :
    Free.canon Free.fullMask (a ^^^ m) = Free.canon Free.fullMask a := by
  have bits : (a ^^^ m) &&& Free.fullMask = Free.fullMask ^^^ (a &&& Free.fullMask) := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := congrArg (fun n : Nat => n.testBit i) hm
    simp only [Nat.testBit_and] at hi
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases ha : a.testBit i <;> cases hb : m.testBit i <;> cases hc : Free.fullMask.testBit i <;> simp_all
  rw [← Free.canon_land Free.fullMask (a ^^^ m), bits, Free.canon_xor_mask, Free.canon_land]

private theorem live_to_binary {m target k t : ℕ} {S : Finset ℕ}
    (hl : Live Z0 m target k t S) (hm : m &&& Free.fullMask = Free.fullMask) :
    ∀ bank : List ℕ, (∀ w ∈ S, Free.Avail bank (Free.canon Free.fullMask w)) →
      ∃ vs : List ℕ, vs.length + t ≤ k ∧ Free.BuildsBin Free.fullMask bank vs ∧
        Free.Avail (vs ++ bank) (Free.canon Free.fullMask target) := by
  induction hl with
  | stop =>
    intro bank hw
    exact ⟨[], by simp, trivial, hw _ (by simp)⟩
  | @un k t a U _ ih =>
    intro bank hw
    have hnext : ∀ w ∈ insert (a ^^^ m) U, Free.Avail bank (Free.canon Free.fullMask w) := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hu
      · rw [canon_not_wire hm]
        exact hw a (Finset.mem_insert_self ..)
      · exact hw w (Finset.mem_insert_of_mem hu)
    obtain ⟨vs, hlen, hb, ht⟩ := ih bank hnext
    exact ⟨vs, by omega, hb, ht⟩
  | @bi k t d a b U _ _ _ ih =>
    intro bank hw
    let w := Free.canon Free.fullMask (op d a b)
    have ha := hw a (Finset.mem_insert_self ..)
    have hb := hw b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have choice : Free.Avail bank w ∨ Free.GateBin Free.fullMask bank w := by
      have hcases : w = 0 ∨ w = Free.canon Free.fullMask a ∨ w = Free.canon Free.fullMask b ∨
          ∃ g < 4, w = Free.binOp Free.fullMask g (Free.canon Free.fullMask a) (Free.canon Free.fullMask b) := by
        cases d
        · exact Free.canon_and_in_binOp Free.fullMask a b
        · exact Free.canon_or_in_binOp Free.fullMask a b
      rcases hcases with h | h | h | ⟨g,hg,h⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (h ▸ ha)
      · exact Or.inl (h ▸ hb)
      · exact Or.inr ⟨_, _, g, hg, ha, hb, h⟩
    have hu : ∀ u ∈ U, Free.Avail bank (Free.canon Free.fullMask u) := by
      intro u h
      exact hw u (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rcases choice with hav | hgate
    · obtain ⟨vs,hlen,hbld,ht⟩ := ih bank (fun x h => by
        rcases Finset.mem_insert.mp h with rfl | hx
        · exact hav
        · exact hu x hx)
      exact ⟨vs, by omega, hbld, ht⟩
    · obtain ⟨vs,hlen,hbld,ht⟩ := ih (w :: bank) (fun x h => by
        rcases Finset.mem_insert.mp h with rfl | hx
        · exact Or.inr List.mem_cons_self
        · exact Free.avail_weaken (fun _ hy => List.mem_cons_of_mem _ hy) (hu x hx))
      refine ⟨w :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbld⟩, ?_⟩
      apply Free.avail_weaken (h := ht)
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto

private theorem count_binary {k t : ℕ} {S : Finset ℕ}
    (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) k t S) : 11 + t ≤ k := by
  have hm : mz 0 &&& Free.fullMask = Free.fullMask := by decide +kernel
  have hv : ∀ w ∈ S, Free.Avail Free.rootStock (Free.canon Free.fullMask w) := by
    intro w hw
    rcases hS hw with ⟨u, hu, rfl⟩ | hc
    · simp only [rawL, List.map_nil, List.append_nil, rawP, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide +kernel)
    · rcases Set.mem_insert_iff.mp hc with rfl | he
      · exact Or.inl (Free.canon_zero _)
      · have heq : w = mz 0 := Set.mem_singleton_iff.mp he
        subst w
        exact Or.inl (by decide +kernel)
  obtain ⟨vs, hlen, hb, ht⟩ := live_to_binary hl hm Free.rootStock hv
  have targetWord : Free.canon Free.fullMask (tz 0) =
      Free.canon Free.fullMask 18368193764639948800 := by decide +kernel
  rw [targetWord] at ht
  have hbinary := Free.target_lower vs hb ht
  omega

lemma iroot : Imp [] 0 12 := by
  intro q hq hs
  obtain ⟨k, hk, t, S, hS, hl⟩ := hs.live
  have hc := count_binary hS hl
  have hzero : t = 0 := by omega
  subst t
  have hmin : ∀ q' < k, ¬ Sol Z0 (mz 0) (tz 0) q' (C (mz 0) (WZ [] 0)) := by
    intro q' hq' hs'
    obtain ⟨k', hk', t', S', hS', hl'⟩ := hs'.live
    have := count_binary hS' hl'
    omega
  exact imp_of_live (L := 12) (Or.inl rfl) root_p (by norm_num) ir
    (by omega) hS hl hmin (Or.inr k11t0)

lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 12 t S) : False := by
  have hmin : ∀ q < 12, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq
  have hbinary := count_binary hS hl
  have htMax : t ≤ 1 := by omega
  apply imp_of_live (L := 13) (Or.inl rfl) root_p (by norm_num) ir (by omega) hS hl hmin
  right
  interval_cases t
  · exact k12t1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol Z0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol Z0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
def f (x : Fin 6 → Bool) : Bool := ((((((((((((x 1 && x 2) && x 3) || ((x 0 && x 1) && x 4)) || ((x 0 && x 2) && x 4)) || ((x 1 && x 2) && x 4)) || ((x 0 && x 3) && x 4)) || ((x 2 && x 3) && x 4)) || ((x 0 && x 1) && x 5)) || ((x 0 && x 2) && x 5)) || ((x 1 && x 2) && x 5)) || ((x 0 && x 3) && x 5)) || ((x 1 && x 3) && x 5))
def EF : ℕ := ((((((((((((rawP.getD 1 0 &&& rawP.getD 2 0) &&& rawP.getD 3 0) ||| ((rawP.getD 0 0 &&& rawP.getD 1 0) &&& rawP.getD 4 0)) ||| ((rawP.getD 0 0 &&& rawP.getD 2 0) &&& rawP.getD 4 0)) ||| ((rawP.getD 1 0 &&& rawP.getD 2 0) &&& rawP.getD 4 0)) ||| ((rawP.getD 0 0 &&& rawP.getD 3 0) &&& rawP.getD 4 0)) ||| ((rawP.getD 2 0 &&& rawP.getD 3 0) &&& rawP.getD 4 0)) ||| ((rawP.getD 0 0 &&& rawP.getD 1 0) &&& rawP.getD 5 0)) ||| ((rawP.getD 0 0 &&& rawP.getD 2 0) &&& rawP.getD 5 0)) ||| ((rawP.getD 1 0 &&& rawP.getD 2 0) &&& rawP.getD 5 0)) ||| ((rawP.getD 0 0 &&& rawP.getD 3 0) &&& rawP.getD 5 0)) ||| ((rawP.getD 1 0 &&& rawP.getD 3 0) &&& rawP.getD 5 0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 6 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 6 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 6 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ g ∈ gs, g.op = GateOp.not) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    Sol Z0 m T (gs.length - 1) S ∨ ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length t S0 := by
  induction gs with
  | nil => intro _ _ _ _ _ _ hnot; simp at hnot
  | cons g gs ih =>
    intro w S hw h0 hm hg hnot hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have hwm_stay : gv m w g ∈ S → ∀ x ∈ w ++ [gv m w g], x ∈ S := fun h x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact hw x hx; exact h
    have hwm_ins : ∀ x ∈ w ++ [gv m w g], x ∈ insert (gv m w g) S := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact Or.inr (hw x hx); exact Or.inl rfl
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.and, i :: j :: _⟩]) (insert (op false (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.not, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | i :: _ =>
        have go := ex_sol m gs (w ++ [gv m w ⟨.not, i :: _⟩]) (insert (w.getD i 0 ^^^ m) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hT
        obtain ⟨k, hk, t, S1, hS1, hl1⟩ := go.live
        by_cases hz : w.getD i 0 ^^^ m ∈ S1
        · have hsub : ((insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m)) : Finset ℕ) : Set ℕ) ⊆ S := by
            intro x hx; simp at hx; rcases hx with rfl | ⟨h1, h2⟩; exact rd i; exact (hS1 h1).resolve_left h2
          have hlu : Live Z0 m T (k + 1) (t + 1) (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨t + 1, by omega, _, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))

theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length t S0 := by
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD o 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) o
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD o false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hnot ⟨o, hout⟩

section sixin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target : (Fin 6 → Bool) → Bool := fun x => Nat.testBit (4276678376 * 2 ^ 32 + 4209557504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem f_target : ∀ x : Fin 6 → Bool, f x = target x := by
  decide +kernel

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [4, 1]⟩, ⟨GateOp.or, [5, 2]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.and, [3, 15]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [8, 17]⟩], 18⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem solve (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = target x := by
  obtain ⟨⟨gates, o⟩, fits, size, computes⟩ := h
  have hsz : Circuit.size ⟨gates, o⟩ = gates.length := rfl
  have hws : witness.size = 13 := rfl
  have hf : ∀ y : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (computes y).trans (f_target y).symm
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 13 ≤ gates.length := by
      by_contra hlt
      rcases bridge_not gates o fits hnot hf with hsol | ⟨t, ht1, S0, hS0, hl0⟩
      · exact iroot (gates.length - 1) (by omega) hsol
      · by_cases hlt2 : gates.length < 12
        · exact iroot gates.length hlt2 (hl0.W hS0)
        · have heq : gates.length = 12 := by omega
          rw [heq] at hl0
          exact iroot_pos ht1 hS0 hl0
    exact ⟨witness, witness_mono, by omega, witness_eval⟩
  · refine ⟨⟨gates, o⟩, fun g hg => ?_, size, computes⟩
    obtain ⟨ho, hl⟩ := fits g hg
    change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at ho
    have hmono : g.op = GateOp.and ∨ g.op = GateOp.or := by
      rcases ho with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hnot ⟨g, hg, h⟩).elim
    exact ⟨hmono, hl⟩

end sixin
end PEqualNP.Outside.L_meta_45452

theorem PEqualNP.Outside.L_meta_45452 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4209557504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4209557504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45452.solve
