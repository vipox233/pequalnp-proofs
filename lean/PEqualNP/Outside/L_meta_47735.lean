import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47735

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
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
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
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm hknown hsub hnd' (k := k') (by omega) hlive'
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
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
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
        exact dagAllNodes hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k (by omega) (hwEq ▸ hlive')

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
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

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

theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel

theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
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
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
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
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefF count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeF mask goal bounds count
      (dagTraceF mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  have hr : dagCheckRoots mask goal bounds (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true := by
    have href : dagRefF count (dagTrace mask stock fuel forest) links 0 = dagRef count (dagTrace mask stock fuel forest) links 0 := by
      funext t s; exact dagRefF_eq count _ links 0 t s
    rw [href, dagCheckRootsF_eq hgoals] at hroots; exact hroots
  have hn : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count (dagTrace mask stock fuel forest) links i = true := by
    intro i h1 h2
    have h := hnodes i h1 h2
    rwa [dagCheckNodeF_eq hgoals] at h
  exact lowerDag hgm hgnz hcs snd hknown hsub hr hn

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def m_0 : Nat := 0xc0c00000c0c0000
def s_0 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_0 : Nat := 0x40000040c0000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_0] at hb
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_0 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsF m_0 g_0 bds_0 (dagRefF 1 (dagTraceF m_0 s_0 3 f_0) l_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0_0 : treeBlockF 0 1 (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) i = true := fun _ h1 h2 => treeBlockF_at nb_0_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0xaa000000aa0000
def s_1 : List Nat := [0x22000000220000, 0xa0000000a0000, 0xaa0000]
def g_1 : Nat := 0x20000002a0000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_1] at hb
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_1 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsF m_1 g_1 bds_1 (dagRefF 1 (dagTraceF m_1 s_1 3 f_1) l_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1_0 : treeBlockF 0 1 (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) i = true := fun _ h1 h2 => treeBlockF_at nb_1_0 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0xc0c0c0c00000000
def s_2 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_2 : Nat := 0x4040c00000000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_2] at hb
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_2 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsF m_2 g_2 bds_2 (dagRefF 1 (dagTraceF m_2 s_2 3 f_2) l_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2_0 : treeBlockF 0 1 (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) i = true := fun _ h1 h2 => treeBlockF_at nb_2_0 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0xaa00aa00000000
def s_3 : List Nat := [0x22002200000000, 0xa000a00000000, 0xaa00000000]
def g_3 : Nat := 0x2002a00000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_3] at hb
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_3 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsF m_3 g_3 bds_3 (dagRefF 1 (dagTraceF m_3 s_3 3 f_3) l_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3_0 : treeBlockF 0 1 (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) i = true := fun _ h1 h2 => treeBlockF_at nb_3_0 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0xaaaa
def s_4 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_4 : Nat := 0x22a
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_4] at hb
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_4 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsF m_4 g_4 bds_4 (dagRefF 1 (dagTraceF m_4 s_4 3 f_4) l_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4_0 : treeBlockF 0 1 (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) i = true := fun _ h1 h2 => treeBlockF_at nb_4_0 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0xcccc
def s_5 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_5 : Nat := 0x44c
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_5 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsF m_5 g_5 bds_5 (dagRefF 1 (dagTraceF m_5 s_5 3 f_5) l_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5_0 : treeBlockF 0 1 (dagCheckNodeF m_5 g_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) l_5) = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_5 g_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) l_5) i = true := fun _ h1 h2 => treeBlockF_at nb_5_0 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0xf0f000000000000
def s_6 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_6 : Nat := 0x107000000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_6] at hb
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_6 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsF m_6 g_6 bds_6 (dagRefF 1 (dagTraceF m_6 s_6 3 f_6) l_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6_0 : treeBlockF 0 1 (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) i = true := fun _ h1 h2 => treeBlockF_at nb_6_0 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0xf0f0
def s_7 : List Nat := [0x5050, 0x3030, 0xf0]
def g_7 : Nat := 0x1070
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_7] at hb
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_7 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsF m_7 g_7 bds_7 (dagRefF 1 (dagTraceF m_7 s_7 3 f_7) l_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7_0 : treeBlockF 0 1 (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) i = true := fun _ h1 h2 => treeBlockF_at nb_7_0 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0xff000000000000
def s_8 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_8 : Nat := 0x17000000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_8 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsF m_8 g_8 bds_8 (dagRefF 1 (dagTraceF m_8 s_8 3 f_8) l_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8_0 : treeBlockF 0 1 (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) i = true := fun _ h1 h2 => treeBlockF_at nb_8_0 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0xff00
def s_9 : List Nat := [0x5500, 0x3300, 0xf00]
def g_9 : Nat := 0x1700
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_9 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsF m_9 g_9 bds_9 (dagRefF 1 (dagTraceF m_9 s_9 3 f_9) l_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9_0 : treeBlockF 0 1 (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) i = true := fun _ h1 h2 => treeBlockF_at nb_9_0 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0x4444444444444444
def s_10 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_10 : Nat := 0x4040404040444
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def f_10 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_10 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 64 (dagTraceF m_10 s_10 5 f_10) l_10 0) s_10 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_0 : treeBlockF 0 32 (dagCheckNodeF m_10 g_10 bds_10 64 (dagTraceF m_10 s_10 5 f_10) l_10) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_1 : treeBlockF 32 64 (dagCheckNodeF m_10 g_10 bds_10 64 (dagTraceF m_10 s_10 5 f_10) l_10) = true := by decide +kernel
theorem nj_10_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_10 g_10 bds_10 64 (dagTraceF m_10 s_10 5 f_10) l_10) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_10_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_10_1 h1 h2)
theorem nc_10 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_10 g_10 bds_10 64 (dagTraceF m_10 s_10 5 f_10) l_10) i = true := nj_10_1
theorem lb_10 : LowerBin m_10 s_10 g_10 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0x2222222222222222
def s_11 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_11 : Nat := 0x2002200220222
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def f_11 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 64 (dagTraceF m_11 s_11 5 f_11) l_11 0) s_11 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 32 (dagCheckNodeF m_11 g_11 bds_11 64 (dagTraceF m_11 s_11 5 f_11) l_11) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_1 : treeBlockF 32 64 (dagCheckNodeF m_11 g_11 bds_11 64 (dagTraceF m_11 s_11 5 f_11) l_11) = true := by decide +kernel
theorem nj_11_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_11 g_11 bds_11 64 (dagTraceF m_11 s_11 5 f_11) l_11) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_11_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_11_1 h1 h2)
theorem nc_11 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_11 g_11 bds_11 64 (dagTraceF m_11 s_11 5 f_11) l_11) i = true := nj_11_1
theorem lb_11 : LowerBin m_11 s_11 g_11 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xa0a0a0a0a0a0a0a
def s_12 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_12 : Nat := 0x2000a000a020a
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def f_12 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 64 (dagTraceF m_12 s_12 5 f_12) l_12 0) s_12 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 32 (dagCheckNodeF m_12 g_12 bds_12 64 (dagTraceF m_12 s_12 5 f_12) l_12) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_1 : treeBlockF 32 64 (dagCheckNodeF m_12 g_12 bds_12 64 (dagTraceF m_12 s_12 5 f_12) l_12) = true := by decide +kernel
theorem nj_12_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_12 g_12 bds_12 64 (dagTraceF m_12 s_12 5 f_12) l_12) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_12_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_12_1 h1 h2)
theorem nc_12 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_12 g_12 bds_12 64 (dagTraceF m_12 s_12 5 f_12) l_12) i = true := nj_12_1
theorem lb_12 : LowerBin m_12 s_12 g_12 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xc0c0c0c0c0c0c0c
def s_13 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_13 : Nat := 0x4040c040c040c
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
def l_13 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 0 (dagTraceF m_13 s_13 4 f_13) l_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_13 g_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) l_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xaa00aa00aa00aa
def s_14 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_14 : Nat := 0x2002a002a002a
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
def l_14 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 0 (dagTraceF m_14 s_14 4 f_14) l_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_14 g_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) l_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xcc00cc00cc00cc
def s_15 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_15 : Nat := 0x4000c000c004c
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def f_15 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 64 (dagTraceF m_15 s_15 5 f_15) l_15 0) s_15 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 32 (dagCheckNodeF m_15 g_15 bds_15 64 (dagTraceF m_15 s_15 5 f_15) l_15) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_1 : treeBlockF 32 64 (dagCheckNodeF m_15 g_15 bds_15 64 (dagTraceF m_15 s_15 5 f_15) l_15) = true := by decide +kernel
theorem nj_15_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_15 g_15 bds_15 64 (dagTraceF m_15 s_15 5 f_15) l_15) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_15_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_15_1 h1 h2)
theorem nc_15 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_15 g_15 bds_15 64 (dagTraceF m_15 s_15 5 f_15) l_15) i = true := nj_15_1
theorem lb_15 : LowerBin m_15 s_15 g_15 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xf000f000f000f00
def s_16 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_16 : Nat := 0x100050005000700
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_16 : KnownBin bds_16 := by intro b hb; simp [bds_16] at hb
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp [bds_16] at hb
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_16] at hb
def f_16 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_16 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 64 (dagTraceF m_16 s_16 5 f_16) l_16 0) s_16 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_0 : treeBlockF 0 32 (dagCheckNodeF m_16 g_16 bds_16 64 (dagTraceF m_16 s_16 5 f_16) l_16) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_1 : treeBlockF 32 64 (dagCheckNodeF m_16 g_16 bds_16 64 (dagTraceF m_16 s_16 5 f_16) l_16) = true := by decide +kernel
theorem nj_16_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_16 g_16 bds_16 64 (dagTraceF m_16 s_16 5 f_16) l_16) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_16_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_16_1 h1 h2)
theorem nc_16 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_16 g_16 bds_16 64 (dagTraceF m_16 s_16 5 f_16) l_16) i = true := nj_16_1
theorem lb_16 : LowerBin m_16 s_16 g_16 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xf000f000f000f0
def s_17 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_17 : Nat := 0x10003000300070
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def f_17 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_17 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 64 (dagTraceF m_17 s_17 5 f_17) l_17 0) s_17 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 32 (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_1 : treeBlockF 32 64 (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) = true := by decide +kernel
theorem nj_17_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_17_1 h1 h2)
theorem nc_17 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) i = true := nj_17_1
theorem lb_17 : LowerBin m_17 s_17 g_17 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xaaaa0000aaaa0000
def s_18 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_18 : Nat := 0x20000002a0000
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
def l_18 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 0 (dagTraceF m_18 s_18 4 f_18) l_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_18 g_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) l_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xaaaa0000aaaa
def s_19 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_19 : Nat := 0x2a0000022a
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
def l_19 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 0 (dagTraceF m_19 s_19 4 f_19) l_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_19 g_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) l_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xcccc0000cccc0000
def s_20 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_20 : Nat := 0x40000040c0000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
def l_20 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 0 (dagTraceF m_20 s_20 4 f_20) l_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_20 g_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) l_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xcccc0000cccc
def s_21 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_21 : Nat := 0x40c0000044c
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
def l_21 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 0 (dagTraceF m_21 s_21 4 f_21) l_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_21 g_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) l_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xf0f00000f0f0000
def s_22 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_22 : Nat := 0x1070000050f0000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
def l_22 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 0 (dagTraceF m_22 s_22 4 f_22) l_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_22 g_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) l_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xf0f00000f0f0
def s_23 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_23 : Nat := 0x103000001070
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
def l_23 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 0 (dagTraceF m_23 s_23 4 f_23) l_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_23 g_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) l_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xff000000ff0000
def s_24 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_24 : Nat := 0x170000003f0000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 4 f_24) l_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xff000000ff00
def s_25 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_25 : Nat := 0x150000001700
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xaaaaaaaa00000000
def s_26 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_26 : Nat := 0x2002a00000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
def l_26 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 0 (dagTraceF m_26 s_26 4 f_26) l_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_26 g_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) l_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xaaaaaaaa
def s_27 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_27 : Nat := 0x2a022a
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def l_27 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xcccccccc00000000
def s_28 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_28 : Nat := 0x4040c00000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xcccccccc
def s_29 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_29 : Nat := 0x40c044c
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
def l_29 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 0 (dagTraceF m_29 s_29 4 f_29) l_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_29 g_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) l_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xf0f0f0f00000000
def s_30 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_30 : Nat := 0x107050f00000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xf0f0f0f0
def s_31 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_31 : Nat := 0x10301070
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
def l_31 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 0 (dagTraceF m_31 s_31 4 f_31) l_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_31 g_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) l_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xff00ff00000000
def s_32 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_32 : Nat := 0x17003f00000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
def l_32 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 4 f_32) l_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_32 g_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) l_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xff00ff00
def s_33 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_33 : Nat := 0x15001700
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
def l_33 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 4 f_33) l_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_33 g_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) l_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xffff000000000000
def s_34 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_34 : Nat := 0x1117000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
def l_34 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 0 (dagTraceF m_34 s_34 4 f_34) l_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_34 g_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) l_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xffff
def s_35 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_35 : Nat := 0x177f
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_5
  · exact lb_7
  · exact lb_9
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_35 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_35 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 43 (dagTraceF m_35 s_35 6 f_35) l_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeF m_35 g_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) l_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 (dagCheckNodeF m_35 g_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) l_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_35 g_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) l_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_35 g_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) l_35) i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xaaaaaaaaaaaaaaaa
def s_36 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_36 : Nat := 0x2002a002a022a
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 6, g_11), (m_12, s_12, 6, g_12), (m_14, s_14, 5, g_14), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_12
  · exact lb_14
  · exact lb_18
  · exact lb_19
  · exact lb_26
  · exact lb_27
  · exact lb_1
  · exact lb_3
  · exact lb_4
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_36 : Nat → Nat × Nat := unpackForestF 0xacb6cacb5c9323fabb4c9323baaa3e93239a814ca8140a804ca804093237a723ca3b44a3a6ca3a5ca3928a3924a3828a382493233a136ca135ca1038a10349313fa00389ea4c9e8189e8149313b931379d13c9ba449b96c9b95c931339936c9935c99138991349303f981389694c9682c968249303b930379503c939449386c9385c9303300b439234900a4f90b4a90b4689c518fd6089a4f89a4e8d24c8d1248d02489a438c24c8992f899278aa4c8982f8982700a4387b5e8823587a5200a3f8634a8634672452852457235e845607235382c5082b4d7235281460813607225f802517225e7da5c7da4c7d9247d8247225375a5d75a4d75a3e75a3d7592a7995c7994c7592678128781247582a7615c7614c76018758267225274a4c7212f721277324c7202f7202700a33712396d3497024e6d2496dc586da6c6da586da546d2330094f6c14e009436b24966b5e6946c6925c6924466a5367a5e67a5266a39669520093f6525e6515e00933644530092f631445f45361b5161b495f15e5fc525fb5e5fb525f14e0092b5e348554535cc515ca4e553525b24f5b24355350594525925e592525534257a4f57a435534056b435503c55b435503000927541444c453533494c25e5235e4c24e50b495093e4c15e4eb5e4eb524e95e4c14e4db434c0184cb434c014009234b239473494a24e4724947c5847a6c47a5847a54472330084f45a6c4582444243449414404e00843432493eb5e4146c4125c412443ea533fa5e3fa523ea393e8520083f3d25c3d0243b2533b15e3b9513b05e008333a4530082f390443545337b5137b493505e35c5235b5e35b523504e0082b343482b45332c5132a4e2b3523124f312432b3502f4522f25e2f2522b3422da4f2da432b3402cb432b13c2bb432b130008272a04422453293492215e2835e2214e26b492683e2205e24b5e24b522485e2204e23b432202c22b432202400823211441e453203491e15e1eb5e1eb521e14e0081f1d0441a4531c3491a05e1ab5e1ab521a04e0081b1924803c531823803b531723803b4314c5114b511494e1493e03a5211c5211b411195e119521193e03a420d3520d3420d15e0f14c0d1520d14e0d95c0d14203a320ba420b94e039520a2520a15e03942072420895c07142078400704e03852042520594c04152048500405e0384200817014530213801b4301124008130001f 9 11
def l_36 : Nat → Nat → Option Nat := unpackLinksF 0x85010a0210241e182c9058209141208241048209040288041000600040008001000200040007e10fc01f803ee17dc0f915f203e027c00f801ed1bd817b00f585eb03d607a06f401e803ce179c0f115e203c027800f001dd1bb817700ed85db03b607606de71bc037426e80dd01b52b6a06c86d711ae035a16b02d395a7034c16980d301a50b4a0659ecb0196032a164c4c98193031c56380c6858d031436280c501871b0e061c0c20d84030046000c0017f0afc15e4abb897512ea05d40b9897302e605c06b8017002dc25b80b7016e02d6358d0b181620ac405880b0856102a4f5480a7114e029825300a6014c029805208a19541127a44f409c9139027204e409a9135026a04cc499812e2a5c04b04941128024e149c09191230246048069001200240047468d0d1a0228645008a01111a220444087890f021e043c0860d0c0218042848501090a1204202809d0101fa43f407d88fb01f223e407c80f619ec03d807b00f319e603c827900f109d473a807310e601c8239007200e401c8038086d94da09b4035886a84d3119e433c06590cb0196032c06390c7018e031446280c0297e12fc05d90bb017412e045a10b4016612cc05790af015e02b065600ac015802a46530ca601406280050009d193a027404d889b0136026c04c0c980130025844b0095092a02502469c8d011242240438887010a2214042808219040208041007f18fe01f823f007d08ec71d803a087400e421c8039007010da31b4035886b00d221a4034806710c8318c22f145e00b4416802b105600ac015802b004e409c0138027004e009c01190230046008c01180228445008a011021f183e007a10e861d0039086c30d801b0034106800cc2180c30006000b8417002d0854307d60f041e003a107020d0801c8001 0xad36cacb5caab4caba48a72349136086b50abb4c7b340aaa3e7b23d7bb4c90a6086250a6a30a994ca9140a884ca8040a723c7b348a6b44a626ca5a5ca5128a4924a4028a3824a0138a2b6ca235c9f948a1838a10349d134a00389fa4c9f0189e8149c9309d13c9ca449c16c9b95c980389ab6c9a35c99938991349784898138950349794c9702c96824948309503c949449406c9385c9025185a41ac23fab23baa239a7a37a323375231a093f9e13b9d9379b1336412f6292b5d927539239883f9603b95837930333a02f3882b33827298232081f1c81b18817028139234984a3284351833509134a90b468fa5d8fd6082b507c2507c34d7f2416994d4184d79a4c76a4c7c35c8026c8e24c8d9248d0248c24c8aa4c9045187b4e83b43823428f24f8ea4e8ca43752426894f8b92f8b1274084f8a02f89827178178823588b5e87a52843518335086b4a8634681a5d85245845607f35c8026c8345082b4d8125d81c60813607ca607cc5d802516e95d4885d7a25c7725c7cb6c7f25c7ea4c7e1247d8247a12477024799247682478828760247a15c7994c7801878928781247715c7694c760187ca5d7c24d7ba3e7b23d7a92a791267782a7582674a4c7324c85c5284b5e83b538235280a5f7fa5e7d253752526d15f7412f739274705f7282f72027168176f241712396e231531227024e6e2426f4586ea6c6e2586da5470b496fa496d23365932529223d8410b81566a4e6c14e3c8430b0256a2516b24967a41521226a46c69a5c67a48692446825e67a526ab5e68a53672396695251922460510a01565a5e6515e4505309825644536216c6095c5f94c631446235161b495fb4160c526035e5fb5262c536115e5f14e5d3605a3505e348593405683c558305d4515ca4e592425ba4f5b2435a45259a5e592525824f57a4356b4355b435dc535c3525ab5058b42573405603c550304f14c541444d8184c814533494e93e5235e5095e513494f3415093e4fb5e4f3524e95e4db434cb4353c5352a5e51a4e5015e4e14e4d0184c014492414b23948231290224a24e482424945848a6c4825847a544ab4949a49472333c03228822089244626c081344485c45824078244494107016452433e94e069264404e42251432493fa41280224246c41a5c3fa48412444025e3fa5242b5e40a533f2393e85227822059243da5c051343b86c3d024048243b951040163ca533c15e039263b05e3a4533806c3685c3584c390443835137b4935b4136c523635e35b5238c533705e3504e3336030350343482f3402c93c2b9303345132a4e2f24231a4f31243304522fa5e2f2522e24f2da432cb432bb4333c533235230b502eb422d3402c13c2b1302504c2a0442382c22824293492483e2835e2685e27349253412683e25b5e253522485e23b4322b4329c532895e2794e2605e2404e2302c220241e94c21144203491eb411f35e1eb5220c531f95e1e14e1a84c1d0441c3491ab411b35e1ab521cc531b85e1a04e020201626013a5019248122400181015a6010a40182380ea301325010240172380d2301645115b510aa421514e121421493e0e9320604213c52133410c2521295e121521193e0d132090520f14c0d95c10b52103420f95e0e9520e14e0d142058400c2420b94e05042088500aa520a15e080520895c0784c0784009242081420704e0594c0485c0485006252051520405e18c5317b5316b4314252112420ca320b15209942068520384201010019240213801b4302c530112492b4391a4f892438723f71a336c94f6b9436613f649336392f5e92b549274b9234684f438433e03f3a8333982f3482b2a827218231d81f1981b03017008130001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 347 (dagTraceF m_36 s_36 8 f_36) l_36 0) s_36 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 64 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_2 : treeBlockF 64 96 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_3 : treeBlockF 96 128 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_4 : treeBlockF 128 160 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_5 : treeBlockF 160 192 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_6 : treeBlockF 192 224 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_7 : treeBlockF 224 256 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_8 : treeBlockF 256 288 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_9 : treeBlockF 288 320 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_10 : treeBlockF 320 347 (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nj_36_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_1 (fun _ h1 h2 => treeBlockF_at nb_36_2 h1 h2)
theorem nj_36_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_2 (fun _ h1 h2 => treeBlockF_at nb_36_3 h1 h2)
theorem nj_36_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_3 (fun _ h1 h2 => treeBlockF_at nb_36_4 h1 h2)
theorem nj_36_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_4 (fun _ h1 h2 => treeBlockF_at nb_36_5 h1 h2)
theorem nj_36_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_5 (fun _ h1 h2 => treeBlockF_at nb_36_6 h1 h2)
theorem nj_36_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_6 (fun _ h1 h2 => treeBlockF_at nb_36_7 h1 h2)
theorem nj_36_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_7 (fun _ h1 h2 => treeBlockF_at nb_36_8 h1 h2)
theorem nj_36_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_8 (fun _ h1 h2 => treeBlockF_at nb_36_9 h1 h2)
theorem nj_36_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_9 (fun _ h1 h2 => treeBlockF_at nb_36_10 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_36 g_36 bds_36 347 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := nj_36_10
theorem lb_36 : LowerBin m_36 s_36 g_36 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0x5555555555555555
def s_37 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_37 : Nat := 0x1115151515151555
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 6, g_10)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
def l_37 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 0 (dagTraceF m_37 s_37 6 f_37) l_37 0) s_37 6 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_37 g_37 bds_37 0 (dagTraceF m_37 s_37 6 f_37) l_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xcccccccccccccccc
def s_38 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_38 : Nat := 0x4040c040c044c
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 6, g_10), (m_15, s_15, 6, g_15), (m_13, s_13, 5, g_13), (m_20, s_20, 5, g_20), (m_21, s_21, 5, g_21), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_5, s_5, 4, g_5)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_10
  · exact lb_15
  · exact lb_13
  · exact lb_20
  · exact lb_21
  · exact lb_28
  · exact lb_29
  · exact lb_0
  · exact lb_2
  · exact lb_5
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_38 : Nat → Nat × Nat := unpackForestF 0xad24900b4fa6a3ba6a39aa25caa124aa024a6a33a935ca693fa6937a7b5ca683fa683700b43a5b4a89c51a4d6089a4f89a4ea1b5ca1a6ca1a4ca1a3c89a4b9ec609e95c9e9509e85c9e85089a479da4c9a3549a26c9a24c9a1289a1249a0289a02489a4397a6c97a4c97828978248992f968289523c95018950148992b899279392c922349216c9214c899238fa6c8fa4c8f9288f9248982f8e9288d13c8d02c8d0248982b898278b82c8a1348a06c8a04c8982300a4388a4687c5287a5e00a3b86a457245e724538534a7245282c5182c5082b4d82b457235281460813607225f803517225e7da5c7da4c7d9247d8247225375a5d75a4e75a4d75a3d7592a7995c7993c7592678128781247582a7615c7613c76018758267225274a5c7212f721277325c7202f7202700a33712396d3497024e6d2496db586da6c6da586da546d2330094f6c13e009436b2530093f6a1346635368a5168a496615e66b5266a5e66a526613e0093b652395c45263a3b63a335c450625606225c5c253603526025e602525c2415ea4f5ea435c2405d9435c04c5ca435c040009375b13454b535a24954a5e592495495e5725e572525715e5493e562435481855243548140093353348532444dc5351b5151b494da5e5035e503524da4e4d9524e25e4e15e4d9420092f4c25e4c15e009234b239473494a24e4724947b5847a6c47a5847a54472330084f45a6c4582444233449314403e00843432530083f420343e35340a5140a493e05e3eb523ea5e3ea523e03e0083b3d239344523ba3b3ba33344503a5603a25c34253383523825e382523424136a4f36a4334240359433414c34a433414000837330342cb53322492c95e312492c85e2f25e2f2522f05e2c83e2e2432c82c2d2432c824008332b3482b24425c5329b5129b4925a5e2835e2835225a4e258522625e2605e258420082f2424c24024222532215e229512205e00823211341e353202491e15e1ea5e1ea521e13e0081f1d0341a3531c2491a05e1aa5e1aa521a03e0081b1924803c531823803b531723803b4314c5114b511494e1493e03a5211452113411115e1213c111521113e03a420d3520d3420d15e0d1520d14e0d95c0d14203a320ba320b93e039520a2520a15e03932072320895c07132078300703e03852042520593c04152048500405e0383200817013530212801a4301124008130001f 9 11
def l_38 : Nat → Nat → Option Nat := unpackLinksF 0x8501090a0f1c16482c10506090c08581010186030406080830101f37be607b8af701ea23d0279c2f381e703ce078c8f181e303c6078c0f181db43b607682ed01da03b407680ed01da03a487480e901d10ba20730ae601ca139407280e38dc60b8c07142e281c5038437080e101c10b8206f0ade01ba137406e80db8db60b6c06d42da81b50364365b8cb01950b2a064c4c981920b1e363c0c60d8c031806300c601872b0e061c0c20d84030046000c0017f0afc15e4abb897702ee05d44b9897302e605c06b8017002dc25b80b7016e02d6358d0b181620ac405880b0856102a4f5480a80950029845300a6014c029805208a19541127a44f409e053c027044e009c01351a6a04d409a81321a5e34bc0960d2c025804a8495012a02486490092012402423484090811f123e047828f011d0a2c74580891112022024400868d0d021a04340850d0a0212142408405013a02040407e90fd01fa03e487c80f901ee23dc07b80f701ea23c0a7800ee11d443a807408e801c8439007200e401c8038086d94da09b4035886a84d3119e433c06704ce0194432806500c7198e031c06380c41982330405f0cbe017c02f045e00bc016c62d805b00b6016632cc05980b1116202c025800af095072a005210a40144228804f8c9f013e027c04e0c9c0136126c04d04933926024c047908f011e022c845808b011222240448089010e2208a40848100fa41f403e047a10ec41d803a087400e421c8039007010da31b4035886b00d221a4034806710c83190030105f08b4516802b105600ac015802b004e409c0138027004e009a11340239847008e011c0238047008e011821f203e007a10e861d0039086c30d801b0034106800cc2180c30006000b8417002d0854307d60f041e003a107020d0801c8001 0xad24986231a5b60853507b3407eb427b23d5393d2b83d79a3876a387b3488026cab25caa924aa024a935ca7b5ca52518824985a4384a41ac23baba39a9a3375231a893fa81375292fa703fa68372a82f188178435283b50a5b4aa4a5da0a55a4d6083350a32587ba50a1b4e7bb4d9da44a335ca2a6ca224ca1a3ca0c6082b407c25c9d240a015c9f9509f05c9e8509da4c7bb5c9d3549ca6c9c24c9b9289b1249a8289a024969289926c98a4c96138980289782493924968289623c9581895014931209392c932349296c9214c8e8289126c90a4c901288f9248e0388e9288b8248e13c8d82c8d0248b0208b82c8b1348a86c8a04ca545182342a424fa3a4ea124b9e24799a43752426b14f6994b619475a9439712f9492b94127919234304f4184b39847328438f02f8c82b8c027898232081f1c81b178170281388a468845287a5e86a45843607eb488026c83b508534a81a5d8445183c508334d82b458125d81c60813607ca607cc5d803516e95d4885d7a25c7725c7cb6c7f25c7ea4c7e1247d8247a12477024799247682478828760247a15c7993c7801878928781247715c7693c760187ca5d7c24e7ba4d7b23d7a92a791267782a7582674a5c7325c8645e85c5384c528235280a5f7fa5e7d253752526d15f7412f739274705f7282f7202716817712396e2316f3427024e6e2425a1426f3586ea6c6e2586da5470b496fa496d233599324c922248310b8154f23e6c13e238330b0256b2536916c6794c6693c6a1346925168a4966a4167b526725e66a5269b536815e6613e62a5165239602316423b63a3362d60613506225c602505d85c5c8506135260a5e602525f24f5ea435d9435ca4364c526345061a535fa415e2405d04c5c0405793c5b13456018550145a2495712e5924957a414e12e5825e57a525715e56243552435ab5359a5e4da3e5895e5693e558185481453b485226c5024c532445235151b49503414e93250b5e503524ea5e4e15e52c535125e4fa4e4f1524d942460510a0154ca5e4c15e45053098254b23948231493424a24e48242320424935848a6c4825847a544ab4949a49472333183223022089244626c081344484c45824078244493107016452332713e069264403e432534106c3f84c3e83c420344125140a493ea413fb523f25e3ea5241b534005e3e03e3aa513d239382313c23b3ba333ad60393503a25c382503595c349503935238a5e382523724f36a433594334a433cc523b45039a5337a41362403514c341402f83c330342e02c2d024322492f02e312492fa412602e3025e2fa522f05e2e2432d24332b533195e2593e3085e2e83e2d82c2c8242bb482a26c2824c2b2442a35129b49283412683228b5e2835226a5e2605e2ac532925e27a4e27052258420592424a4c051342286c2402404824229510401623a532315e039262205e1e93c21134202491ea411f25e1ea5220b531f95e1e13e1a83c1d0341c2491aa411b25e1aa521cb531b85e1a03e1626013a501924811a400202015a6010240182380ea3001810132500fa40172380d2301645115b510aa321514e119421493e0e932060321213c13c52133411295e119521113e0d1320d95c103520fb420c2520f15e0e9520e14e0d14209052058300c2320b93e05032088500aa520a15e080520895c0783c0783009232081320703e0593c0485c0485006252051520405e18c5317b5316b431425210a420ca320b15209932068520383201010019240212801a4302b5301124acb4fa6343892438723b71a336c94f6b9436a93f6593b5b937541334d12f4b9234684f438434283f3d83b338372c0332502f218231d81f1981b03017008130001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 347 (dagTraceF m_38 s_38 8 f_38) l_38 0) s_38 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_0 : treeBlockF 0 32 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_1 : treeBlockF 32 64 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_2 : treeBlockF 64 96 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_3 : treeBlockF 96 128 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_4 : treeBlockF 128 160 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_5 : treeBlockF 160 192 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_6 : treeBlockF 192 224 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_7 : treeBlockF 224 256 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_8 : treeBlockF 256 288 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_9 : treeBlockF 288 320 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_10 : treeBlockF 320 347 (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
theorem nj_38_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_38_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_38_1 h1 h2)
theorem nj_38_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_1 (fun _ h1 h2 => treeBlockF_at nb_38_2 h1 h2)
theorem nj_38_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_2 (fun _ h1 h2 => treeBlockF_at nb_38_3 h1 h2)
theorem nj_38_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_3 (fun _ h1 h2 => treeBlockF_at nb_38_4 h1 h2)
theorem nj_38_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_4 (fun _ h1 h2 => treeBlockF_at nb_38_5 h1 h2)
theorem nj_38_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_5 (fun _ h1 h2 => treeBlockF_at nb_38_6 h1 h2)
theorem nj_38_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_6 (fun _ h1 h2 => treeBlockF_at nb_38_7 h1 h2)
theorem nj_38_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_7 (fun _ h1 h2 => treeBlockF_at nb_38_8 h1 h2)
theorem nj_38_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_8 (fun _ h1 h2 => treeBlockF_at nb_38_9 h1 h2)
theorem nj_38_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_9 (fun _ h1 h2 => treeBlockF_at nb_38_10 h1 h2)
theorem nc_38 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_38 g_38 bds_38 347 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := nj_38_10
theorem lb_38 : LowerBin m_38 s_38 g_38 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0x3333333333333333
def s_39 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_39 : Nat := 0x1113113311331333
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 6, g_11)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
def l_39 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 0 (dagTraceF m_39 s_39 6 f_39) l_39 0) s_39 6 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_39 g_39 bds_39 0 (dagTraceF m_39 s_39 6 f_39) l_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xf0f0f0f0f0f0f0f0
def s_40 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_40 : Nat := 0x1010103010301070
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 6, g_17), (m_23, s_23, 5, g_23), (m_31, s_31, 5, g_31), (m_7, s_7, 4, g_7)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_23
  · exact lb_31
  · exact lb_7
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_40 : Nat → Nat × Nat := unpackForestF 0x500189d2933c0b2742480b4f948bd2917665284a3569747128d3a509cca03901696eed39dda4bba528969d12d262497449228905d1448224113ba50872a0ee57a15283b952772a304d25dca83f9507f0a0ee179ed283d95c7b2a0ee149dc28bc349770a002d1dd1ae3a250548acded71bd28379506f0a0a915551af2a35d5469ca8d35511d3212e64244c80b994903202254470c48e1509d2a13954270bc4a1509b2d2385a270b44d1501d2a03954070aa4a154142a03601686971652e28a594e4b28c9606931a4a63414b0300252d0e2ca1c514329c8a9011420219464325a0250ce52d1fa483f09072578f09e1e018392b472558e4a90093b2b4a456578d40c1595a332a056558bc9e1792c2f03056548ac969581a2b030024cc8a2c914512209c44118881691b4923682440b004258d4591a8a23413871200e1401a08c3407404218815a164902c520402f0983c1305820168402b080520107604548082f0602c020b414140082b0303c060580c07008290102d020580407404198001f 8 11
def l_40 : Nat → Nat → Option Nat := unpackLinksF 0x8982241890222182b20818186060800e0007e8dfa07e81db07605d237199c607181c607105c407101c216ca1b206b0dac06911a406901a026801a00668d9a066819a0649192064818e259d166059816225881620588162056915a056815a056815245481501540150053854645181403500140050013a34e813a04e813434d013404d013404b8cff83f04fa13e04f803e00f803e00f4237acde03780de03780de0360cd8031a4c413100c402f8cbe02f80b832e00b802a9ca812a00a802984a602904a402900a40278c9e027809e023248a122048612180860218086020886cb1b006c01b006c01b006631980549148452014804c313004c0118c46011803870d843600d803410d003210c803200c802c30b002c00b001a900b0001 0x14006278164b45e6c8bb36d6a69acc93566c6a324d1a61a2cf949392833a1244020bab44726a932940cca80505097470604e0181c4dc5e9a8bb23155aa294c356916ab2cd39a9a6a9159492a32a4e4d09894859200a3280e42c18c7a508e4a104541e0284745c8f6b90e57214a84005c7d0a114082289047b4e8e692e8d09c5a0c692e8c245160ba241119c5c872a0f81420a2e42a507f0b8f614209a4b83410a8b900541fc283c45c7d4a0f8571eca83c3496f68323179ae2ec935e6d6bb24d3a45a4b9b426e6832094a21284315e3b2b30854a0ca8c09507e0bc24165e8293c851770a0ead71d1283935c714a0e0541bc28311385e268b80e1581a3282065240d04b99c913302e64044c48e16c1c2a83430478bc4a168142e2385b270b44d0191e2b12855050d9175aa2d39c566e8aadad79b1aeb5b4e6a69ad28e98d1c28959482a2c24e9809caf9385d26c5c4c4a02c8f85159074b00e55c1c2a036050629a061300c181384d69298d054a2ca8c51434a48292940a71d94a4f28c685090c96a701a4b0308c900cca022840498b2911450d2d1ba424729c7252910a3171424325a604910124181483f0907a4f0cc961e018414b45a908f8af1d95a3a2ac72548b496999243503066540c49e1812c2f0306e948b5251b15e342b464558b8a91692d2c0345606090161182c0607048d248da094c59288a23454860a51384e120944c1182c211282d220583407475200e1400a080411647e288d15a0e2843c13840250d8460508434074180a0ba48162900c120501e0982c0a0383056808a10a85e120b42215840290101d0a028180b028280403c070580c07038a90114a0d0bc16168242b028520405a060b0080ece34f93696ecd1d4da1a514b42286704eca8999084b190861e0ec04198001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 161 (dagTraceF m_40 s_40 7 f_40) l_40 0) s_40 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 64 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_2 : treeBlockF 64 96 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_3 : treeBlockF 96 128 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_4 : treeBlockF 128 160 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_5 : treeBlockF 160 161 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nj_40_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join nj_40_1 (fun _ h1 h2 => treeBlockF_at nb_40_2 h1 h2)
theorem nj_40_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join nj_40_2 (fun _ h1 h2 => treeBlockF_at nb_40_3 h1 h2)
theorem nj_40_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join nj_40_3 (fun _ h1 h2 => treeBlockF_at nb_40_4 h1 h2)
theorem nj_40_5 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join nj_40_4 (fun _ h1 h2 => treeBlockF_at nb_40_5 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := nj_40_5
theorem lb_40 : LowerBin m_40 s_40 g_40 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xf0f0f0f0f0f0f0f
def s_41 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_41 : Nat := 0x107050f050f070f
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 6, g_12), (m_16, s_16, 6, g_16), (m_13, s_13, 5, g_13), (m_22, s_22, 5, g_22), (m_30, s_30, 5, g_30), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_16
  · exact lb_13
  · exact lb_22
  · exact lb_30
  · exact lb_0
  · exact lb_2
  · exact lb_6
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_41 : Nat → Nat × Nat := unpackForestF 0x38946a00b4bdd12ff0a557850abba25de05b67025b3810d9ba257dd0afefa9577d0abba15ddedb66e855f740bfbba55ddcaaee8177756d9ba057005a3e34d7f71099b7145dbca66dc1171a6bbb4c6cda5b26d2d53694698d35bd8a366c49b3622d9b1160d88366c41831a6afb035cd66326b24e35d6a9ac934d641c6b4d53590698d353d45a76aa4d355069a8b42d452f6a2577510bb8d345c68afe9c1734b6aba635cd2c2ae34577464d9a3164d18aa68c4d31a2b79fc6ccfdb667ed833f4d99f86ccfc3063455f3d2b99b264cd8a6674553362899b018cdcaa66c0531a2a78d05fcccae660d57316b998155c682ee565b32b0c995854cac1a63416f248d99236cc91b06489b3242d992160c682be441731b2c98d84cc7c2a6361131b0598e054c6c1263414c0148f8c35ec5a2b62cd580147f6ac5bc489ae240d6d58b58736cc38b661c1b2d58af7e45ebf1af5f8d76fc4bd7e15ebf0aedf8573056b97e152c082e604142fc0bd7e05dbf02e5fad72fd2b97e052b562b5f4d3ad56b57bc58bdd365aad5ef26937925ebc8aede4176d56ad74349ba12f5da492ed04974252ba122dd2536e909b74244b552b5aa53ee18ad70b56b8d225c295ae108b6a94db7dae5aa51ed509f6c456b61ab5b4912d84ad6c145b5426dacd72d508e00a37b4c9b00252eb06bf67a45b3c22d60d76cd2d958357ac12fd92d16c908b5825db15b658a5b2c50d958257af9a6d7c93abe2bd5f934afc0a57c54ab048b5c46cae234571182b96815c254ac11bd6017eb36ab59a55acd22d60176b12d958057004a3d5ad7aad4bb46456aad2ed18d5aa68a95336ca99aa54c5b28c4af4fc5aa7e2b53ed5a9f69d50244a7d2b518916998b54cc56a65ab534912994ad46235a5cae52c91e8c0714a14da35a3524d128d28f4734aa39a351c51a8d26b460340049fd131b2892d939b57a152ed0a916852bd39a56a092ed04916732ad3e35a9f1ab4f895a7d2893e1569cc9b4f4d727948f398189d123cea5367526b3a1469cc0a0024ee6e6bd3725d9b8af4dc176578ad35a5d9acaf4aed5a678d933c5499daa4ae95e608b530456981ab4c4912604ad3014e95d1acb097a582bb2c145965a84b48c2592892c12595cab0024de552892946c949364a45b23f6af2835c93d23c7e912494bb24a45928a6c944d6492691f956901ad48c172406ad202569052548291a4128d201448fc9b0024ce3d2bd1da568ecab0024ae386d91c36073e2bb9ed6e3448d1a02573dad4611b2302d91806c73dabc3d17a1e6bd0f35d879ae43cd4a1e4bd14250878af43c576244b9122508782f43c1761e0b90fb5c87cae43c149cf6ace7b4b8652d43295a1904ae7b4a85cae39ed1e0d8b50935c848ae4241720d8ad06b56835a741a53a0d09ae7b4682d28404d16024930123a81d224048da022bd0193480c0a404549cf4ad0013e73cad3f8d61fc4d8fe25473cabbe0d75f0492f823a7c11b3e0579f347af992a7cc933e0511f1288f805d73cab3c8d69ed2b8f23567912b3d4511e42acf213e795253ca919e528cf201473ca53b3159e14a0ecb567652d3b2959d9472ed34476ca03b4911d92ace794673c1fba4d59d268ce925674ca23a4559cf07ae814c73c1b80249dcd06c0084b681afb92915c928ad035d71c36340d5da04bee1b4570ca2b40975bf6d8df96c6fc3634095db869adc24e6e02f3720d1b9028dc05268122b651b1b28d0d94606cda0364951a046ed015f6b5a2b5a955ad48ad015d6ac3634055da78d8d3b6c69cb63404dda16d8d0b68685b0344901a14a8d012700423b3ad799d4babe45666d2eaf8d59968a8cb36c659aa32c1b17c4aec7c5a63e2b31ed598f69cc824463d2b2f8915898b4c4c56625ab314911894acbe23561c2e30c91d7c270c214d5f5233049117d28ebf34a5f9a32fc5197d24abe1340041faf31b1790d8b1b575d52eaea915750bcb19565c92eae4915630acb635a5b1ab2d89596d288b605658c1b2d4d716948eb182c59123aca5356526ab204658c120020ed5e6bcaf25d578aeabc1793f8acada5d56c2f27ed59578d8abc5455daa27e95d508b4a8456541ab2a4911504aca804e4fd1aa991b14c6d8a606c4fcaba90d6148690a403c4fc93a80979402baa0145505a82848c141288a01254fc2b0020dd3d0889d46c4e8b62741b1276ae9c35c4dd23a4e511314ba98a454c8a6a644d531068938564a1ad25c571286ac942564a5252529192928c9404449c1b0020cd250bc9195648c2b0020ad206d8903602b62b95ad6d1c48c8e1252b5ad2311b1182d88c06c2b5aba0d179066bc8335d419ae20cd49064bc87a5c43d2820c579062ba8315c42dae20c549084a0840504182f20c174ad6ac56b4b4052d2029590124a56b4a3fc2e15ad1cf58b47d35c3e8ae1f4170f58ac7ab563d5a71ea534f509c56b463cd281d4d14ea4927523a3bd221d48d8ea0bc758343ac0a1d4148ad4ac72b6c395b01cc900e54a85695738da415a51cad27e6db5636d2d1b6958db4946da4636ca315a4f4d90985693735c1f15a168d36b069a6c34d2a15a15cc56ba62a493151d18a8d8c52bc6523d32895194498c5288641543142e98c910c505a568562e5ad184170b96ac5ca562fca2172158b907c5d24a2e923174518b90285684a2ba2b16c940ae6ac5725a2b92b15c8e4af688581402bd2215c558ad08c008272a8b61541b0896ae5325d2992294c578894ac50b5a285ab142958a127c44a362712e9389149d2884e126224ab1341709948e4494c2412392a5349526a48146245251229189128c48126224a2114d688a6ac4525622ca21145588926c0081f2193610c1b0656ae4125d20922904178652ac3eb5a1f5ab0fa9587d07c329361e12e8f0914792883c0261942b0ec5707548e3284c1b1238e25347126a360461b5250da9186d28c36026194220ccd68666ac3325619ca20cc1586506c0081b185360c25b0610d80dc5717d36036d5c5b4b82d95c16c2e036d1c556ba2aa5d155228aa578550bc0da5613a2d0a49704e8ac273561392689c8d41b48c2135a125ae092570490b821356109a508d1604268c212561089f0840f81b46c1da5d0ed228764d83d2881d9260ec2f036558336b419b560cd2b06c510332ac199460cc1f0364d8284ba142450a09b05c5102824c1405e0a5280544c0292881402606c2b038d681c6ac0e25608ca20385581c28c0f25007c9803c5101c0ac0e03e06c1b00205c190a80aa6c05c2a02a5b0150d80135704cae02491c022480625d0312281a5340d26a060140082b006d68096b801b5600d2b0089280448c0214600c0a0040d8010260001f 10 11
def l_41 : Nat → Nat → Option Nat := unpackLinksF 0x73a039c05cd43e6a0735039595cac0e56072b03930bc902e480724038e11c700e3417180b8c01c600e204710038705bdd7de626f3037885bc40dde16e52b7203b882dc406e2036f09b780dbc06de036e83b740db80ed4236a01b443da206d1036707b380d9c06cb0f6191b0c0d8606c3036085b040d800ebf07581fab04d5806aa0b5501aa02d3c569d074d85a6c0d360697134b81a5c0d2c0e96034b01a541d1a468d034507a280d1406870f4381a1c0d081e7c233c099e00cec1676033a059a8acd20e670b338199c0cc626630331819881cc406620330839648cb206560f2b019580ca61e530329819403c90462493120188c1c4606210b0f078780c3c06142b0a018500c28060f1707818342c1a060d03058582c0c16060b0304078200c1006060b03018180c0c06060301877c52be205f006f8017c00bda1ded02f6817b01bd60de02ef0017800bc005e002ef057780bbc05de02eb1171cfb8a15c502e2037100b860dc302dd916ec0b7215b70adb816d81b6c05b506da816b48b5a05ab0aca2f6500b2415900ac8016400b10458802c30560c3b06058302bc955e40af2057902ba0b5cc1ae6057302b9815cc0ae215623eb1015880ac0155f06ad8954c8aa2155102a8815401a90454802a3054bd7a5e052e06940d4a00a4825220a91014841a3e15152a8a034482a220d1102888143c2a12350902840341c1a0e05060681094080a020d000680013f439fa04fa0e7d013e809f404f70e7a073b479d614eb02709538019bc14de026c0d36009ae0cd312698134819a20cd1026803330499804cb06650331c398e04c702620730439743cba025d012e8097404b12658812c409543ca906538529429345c9a024d01264193204970a4b8124079200490024705234191a048c06450520c78f05c78023b051d028e8046d1e36811a448cc1c6506320319008c804610e2e8917018b8045a0a2c8316408b20459022b07148489c244e0226831340896144b022485104887c1c3e021f010d0a8680434021a010bc585e042d0a16810b408541c2a0215010a028500428021401098284c042602130109808461c114a078503c081e040f02039101c080a1405020281014080a04020e00830040802040101fc12fdc17e623f301f902fc807e013f001f800fc007dc13df3def80f7817bc03de01ef00f6c37b40bda01ec82f6017b003d801ec00f6007a043d001e782f10b7860bc301e084efc277e03be05df00ef8077c03be01dd86ed467680bb305d884ec4076203b101d880ec407600bae09d38ee94274a03a501d202e9007460b9b21cd80e642704bb8201c004df826fc037e01bb10dd806e813710db880dc406ce536701b380d9c06c42b6105b080d8406c2036101af84d40f6a0035001a704d3416922341219f84cfc067c0b3e019b10cd806681334019a00cd0065e2b2f019780cb426580b28119010c257612030805810cc0805fc22fc097e00bec15f212ef297702bb025d60aeb017580ba425c632e3017102b8415c202e0056e08b7005b60ada056d00b5c35ae02d40d6a00b5005a802d10d6706b1c758a12c5015d94ae8157012b801590cac805620aad115680ab015560aab015502a98454c02a5055202a84354202a1014f06a6c35283a94014a00a500528028b254580a2c05083a830540849fc24e85a74013a009cc14e602710938809a874d4026a01350099454ca026501328098054c00260012f0497414ba025c052d0494c74905a480123049102488023d1d1e808e4446c1a35051a028d0046802310d16888b01458022a0914828a404520229011306888443c221e010e828740436121b010c84844841c1a0e010700810a40802040102007fc53fe01fd08fe807f403f419fa00fd007e803f011f800fc007e003ea19f500fa807cc23e601e148ef8477c03be01df00eb9075c03aa11d500ea8075403aa01d20ce88274403a201d100e41271c138621c300e102708038011c000e000700037c11af3cd7806b4235809a810d0106800336299908cc026600330019800cc006600320419000c704638031a098d00c6806340314198904c480620130e098700c38061c030e017f20bf805f812fc017d04b9165c412e2016f08b6845b402d8096c00b6005b002d801690cb18c58812c2095f08af8057c02be015f00af8057812b811551c9f2e4f8027811322898824bc225e012918940249822481124008f0c478023a091d008e0246042300117048b0244c322601130088064400220011000868642832140109048402420020e0903107e0e3e821f400f02877823b421da00e718730239021c410e2006e0c37001b608db006d0235841ac00d5046a0234431a200d1006706338019c00ce006586320319000c7046302318018a08c1105d0e2e8017400ba005a8a2d0115258a90054802a4014828a4005200288214400a2004c9226401320098044c002600130008e284700238011c008e00458622c0116008a0444042200110007f243f801f420fa007d003e021f000ea3875003a801cc20e600720439001c800d6386b0034841a400d2006804340019c10ce006604320417470ba005d002d8416c00b4085a002c8216400b00856082b0013c7088584400210410800801040001c8e0e4006a20320c18820c0106000300016860a440500828001304094104a0025001280088303c201a1000b20001 0x2f948bc4a35c25326a6912f446984a56bdd1b472577862ab5693d9b09aa42177850aace83d5701adf11b3836d984a5ce08b67021b26f2c9359348e52eefc9575248b79a359bcab0c61777d0aa31015dedb64de5715e0c8ad8344852eef09575148b7923518caeeee5555e0ac30816dd5b62bc173874bfc225de012bdf69575048b8ba3dbd91bde28d77f2bfbe15dde8abcda556ac27b351358dc93ef217f760bbba0575742ab380f55a06a8f8271800bed8da30b6c9abb54bbd1a428d33710987e34cdbca6616d1b6b68b3494ddc0a2d144e654262ac84ddb822af40e53c063b034484cae1f41736c8d9b5b64da9aa6d28d3056b97f35cd9e36616d735f6a1b326cd94b66c8583630d9b1060d81ae6ba4d35a069aeb54d59a25dc4d35a6a9aab44bb49a6bf193548a98536cbb1226bc4e35c269ad838d641a6ac4d35506975234ba51a6aed3b54685a9a5ebad1b5d08d3522bb34155aa49ecce4d60a24ba885d5602ab320f55706a79025d24b444e592c12890292484cae69c1734c6b82515c9a5aee9ad56272ada4155a989f4a64c85f0bba585521c0c8300473d2a90a35c1242e6929b3482c9a3954d189a4505721f2b9a246cd0db6684d83414d91395ccf0a86801b33f0c19e95cce89a66e0533a2a9601448109266e552bf28901924cf13257c952024691316cceca6672513380319b014cb83420e191bb08876824cccae1f4173316b82485c565aee64d545f2bb9815541c2b65a1559607c9d8322a80f02c04b220a87e35c128ae65c5b32d0c996054cac1a212171080b994c6cca1b664ed83264d99296cc90b020e173210a19105cc7c1a6380531f0a8dd0443b012638151b908875824c84b2370550ea2688306cc802663c1131d0598d824dc9afedad77686b7b0b57bedaaeb0d4f5068b73a36d3cafe94577452b79f157874aae6a54ebd28b5293fa209dccc4de5126700925cd02fe5e1772a0b7918574142ae3414db708aca83f5e01daac0dd39066748252a40f90a06c5e02e0a013c61af62f15b166ad86564bd6325e0992f88ab86355a90a6cca516bb27b8993565026aaa115b507b89035c322c620db2f74d98796cc383660a542fe0a18185cbf42860ad72132b98105cc0c2e604142fe6b97e95c3e82e61917b0b6bd8535dc252f61057b072bb8315c844aae0854aa327b32135c042f600176ff0b87c855bf0293260f55406b7d34ebe22c5ee9b2eb4a975244ba5225ead26f44bd74244bccaecc6556e427b08135bc82eaa6156db07a7c035bb8925da092ea29b31145b8c96c0e496e909aa9045b68169de096f069377a5ebb1295d6916e84895c145b889ec0c4d69f25b309256c822db20f4ee06ac782d54412c1c5526026971a44b8d2257716ae58ad72356b892b41c5185d09b708451700adbed720e2987a8545401a5b4912da488dac5ab722b5b6d5ad94ac2e94db60a29ea1185b02d6b35c3d42662916f118b586c57bee2b5f2d6af66af78b56b9d2b56e55ee629f7014db78a3c185169e27b2f9356c42bdba13ed709b6a8473d022b1c0f54f06a2d0177fd1b5a64da716c92f1349c5a3586956bc49b682457e89329c136cf08aa68359c5ae59a5b2294c9612547d892578d36ca68b14a46a1c9d4ba4d9fd24a7404db24229500744002aff46cb1db6452972c62d96286c7d4925804d2bf02961b4d9a1a2d8493ab846d6095eaf8a950c4ea5c26cfe1257c8925661345708a7282529c0e87e056b94a92d9449689a572d0262488f9934964925791b2bb8d108c64aea304c6d92b84a8fb9449609a0aa1903b028f8924539aed6ad54e84bb5a255acd22be0498550aca6036ac4b60aa172d16bf6735db31abcdad56cb4bf6425db112bc3a956bd48b5ba37a109d4ae4da3c254fd9277bc9356c17eb20bb580571502aa960dce404e5281d0e80ad280d2ae6bd56a5da8d2ad529169b46b49834aad2ed38956a748b51235a691a5240d2a046909a54a5c14547192a98a95436ca71b254ed529f4894ca34a98b652c0e29106948044955ae51e0d2a048950244a381254916aa38ad51356a85a753e95a8d0690995ca69225349129d8b54e456a6dab53295a972b94b247a50a6d1e5169226b47b54a49a251c4d29069547b46a38a3526d1a9128f46935ab22b554d5aa54af4f245a611ad2a0e28c0690a1449e80c5151b1ec4c9432547ad1a5125b27f2c9411549f89a4f2062770293b0149f4924ea052874baf6255a1922d0a57a7c24d3a0147a8925069767f4ab412457a493428d727d2893e944a01ad4fed5a7e4ad3e1569e9ae4f291de62a93a944794924ec535e628b3a9359dd23ce8519e424d44357a112b3c68da812ad3d9369e00c4e6052716bd3825d8452acd09166346b3795e788934dc174510ab3625d9912acce9161046b3595e780930a00d650261312347709240e8d1da24934c6c846324d1152646c933b54819224c28d1de2c92e15493c983b24926248931244964a24cb16a648ad31b569852b4b055a6029c270357cc9a4b24925a2892d23096da84b25125e4bd2e95d778aacb8515f726b2c1250f81acdb15a6a6ad3325783122cbe8d6572ad271307609334c15c4d08a71027941264aa512506b8f6954952364a69b24f4892916c914b2498552442692835c908aa4945124124927a47924a348049a4b2692513492ca6c845164a26b26a5d9152ac9891649269219449089a48c1724126921a4a9092348251a476b522b569112b480512516af27244920ab47e4da3d2bd1e2568ecab416d51e12891cb6c86db4422d92386c1083448292a3c4591e028917464825b23f25922e4ab0da4a8d5233fc555ee294ef94669016c68094a403a1c8158ca3645cd61fd4d91896c8c03644a172200a10a35c8a0ae448172284a10f8508952e448942206b90f95c1242e45d17a2d6bd1635d8adae422d562a6a514a5e89caf44c575ec274ef13688c2f444176210b824055878291460743802b07c54774aa410d5a1b4b50d25683d22bf05594908aa502d86412c1ed22172b90a35c84cae424172074890ac5a8462b420d5a0f69d032567dcab41c53a0d09a2284576c9a41694207468ee1547689a3e851207488f99448109a4060520a68b04a498211d40c8da052bd011527f0a2be4511eb274ec93668422ba80b44404a5101d0dc0ac004f9fe6b0fea6c7f12a3ea551f4488f99447d51ebb88d5f4254f99267c41e86c0d5d303a1e8157c4a23f4d75e26aafca497e11d3ee8d9f62bcf91447c02e86a155d205a1e02579c0a3da571e6028f51447940a3d4511e7494f3246794a33dcd69ec6acf5a567a4ab3d04f9e4028ee14476d223c2941da288ed940771a23b4911e28acf035677d2d3bc959dd472ec9560d02288411033028e994474ca2348d69d66aca534a755a33a8959d22aca40461081b3a0530420791bc578d9adc66d6a2f6af0eb56871a5c30d2a1668f063468052b3fe569fb2aef795678ca53b0519a00aea384775c1fba20f5cf06e208352800e864054d626ce6836585b228c0d16168cdea556d926b94915a929ae49456a09a9a2099616b8e386c44532378950cd048db34d711a2a22919a529ae19455dc1d28a0d8d404a4201a0c40b1ab1b1c16d888a5c700b637e1b0cc048dd0346e40a37ad355868ade24e6c91b35c5345728ad09256ec2f37014976074a203634c1299209083034180166cd2a28611142068d9b40549221940d141048db46c6d6341f3191b48c0a9b646c92a19c111400682b1640b00a190091a969ad7b456b92ab4a935ad48a2b14669c9b18e098562b8d586c6a6360a3191a86d8d396c0bc22344d502b028150146892006c5102e04814814695b6348da0486c8d1b606852a06a5902d0681401472dafb90d75c66aeaeb557152fb84975be4ae82a556dd22b628ddb02bed615d6a8ab8a8555a626ed01275d01d27e0d92405469027310131020682702cc2134679af33a975934aacca4562d1ab064d19b4bac625565d22b248d58a468c11346411a1f495187050c9c646662a330db18c6c8cbb5463d223128d186270c0934658363005113d6b8bf934641223209117e248ca45a64e2b324d599169cc7a565f49a1f41718a488c52446362d3191598b6acc4a5661c2e30c91d8429abf9456089aafe95182488bf124601a52fed197e28cc1a46604a3afa4959c8accd3566552bb1c9158846ac29385f09a1f81116a058bd46c304b22ec550c0268bc86c5bc322e41516e068b482c59c122cc0516d048b28145dd2e9829557648aba85e5b0132c8050bf048b9a5d5bd2aae4914be04c7e35c5b4222da511706b4b7b565b92b2d81596a6b8b4a472ec2a2ca110ba048b314d2eca2aca4d56748eb20462e4132f0d5d742ac5c1365c42b2d60d968058b1824585af2c0974f94aaac24554d1aabe574512aaaf05e2dc132b8975544aaaba453e11a8a04d55b0bc5a8264e0182a48d0b104877a342bc122b31b0f98c8ac454551b22aed50ee488a8a342cc322881513706057024549222a491141088aac5a5522b2a6d59514ac271355002b2a01394e8d828c64535b607c5114c0d8a5358115aa292d20342a8a403c3289a28249142288a123050da8282511464bca295d2ccaaa88514ce26aa01250bc1aabb1595a6acab2573d122a9e8d54b2ae2694551c93a7e15936060568264e0a627a111386b8610544f2362765b1372889d06c4b4322681512c0689c35c4a82a264111290489ba474c42325009933068990344cca6a545153226a9aa5d4b52aa6891531068958444b8ae2540d12906895a4a4a9232525192f6b496b564b12b250111396ae9b1444c02b24e0d9250bc9215648c2b1e6d50b608890b6c40db41f2d91206c07c3443c92a16e190b50888b4643c5b21a0191164aa81a4a475231be4b51c24a6a85530c25168118800341301646a3622cd60d44d88c96c460362205710b2a07e35c43cae212171104b887a5042dae094571080b884a504202822d179156bc8a35d44dae1f2d55126a488a5e438af21a5750c2b824155428a920e179060ba6083a2cc1b0fe0682502c7bc542c82a1e0d59034b4812563dd229c6514dd25a8092533c2b1eed20ff0b87e35c3ecae1f4170ef4887ec5a3e62b1f0d58f769c772563d8a688a514ce0ac7a84e2c01a1e6940ef468588542bc1a196110ef488650443b01a1d6050f268a78a493c11d1dc8d8e528a7012d110929da178ea0a469845324221800e8ae06c3f01a0900b1ccd50200280f8143992007a490230880f0143a1b61beda0486c873b603952a0784d0220c80e814375ac08ad50e36906d93c0842a0865101c02863044381ab1be968de4ac6ea4a371231b65184324c6285610c9e1b2130d707c6ab58351361a6950cc2a865a44328a21988f4b146a6592a328931900f42306a6301d0b80a990550c648868b5d2ddaa9a0924cf47467236334af192510c70ba110553141685a094bc0286105c2ec0a17e110ba0285f9442f125176918ba28c61b5a305ab180958be0ac5e83e2e40a162510b04885b2502bca2160500b168857a442de2b16ad58b44b459a562c91c95c5582108a8fc57479ada36d69176ae82b56411a5a00d28fe68e7a3463a52b1c855ce228e7093f3689e9b04dc4126a6b05a3482b988158b8094568461f00d036058490a84d03c28d3214e950a24685596c234b213c550992984b9442309a1541b0962684a93422c92150974a34aa53a45298af1284d08a24c49944064ae1244d09d28848934291ad146d58a24ac4e156240a21424f89d2484e94427d2e91a9549e48a4e1262682e13291c922a84a9442449212c5349228a4a93524d251249189128c4ba47250a3120498490b84594422ca211cd688d6ac46256228ab152d5ca54ac5023626cab1305308f288449361282a0ec0f0874d83f96420caa0fc4d0860d8348641e82a0ea13073088340341c81a0e20d0670484225d1fd2a906914820bc38034198130de110170b8370341e4220da0d0806b43fb561f92b0f01586c0883e83e1e4120f25107b4ba34a551e9228f0098762b83aa471b82a0e21106d0483914d1b8a28e24d46f494372461b4a30e691c7008c36026128ae0ce110672883535a1a5ab0d0958660ac42b57204ab0f84d8770ac3a04c1ac220ca0d8634d828a64141220c45b0610d80981017d36090990574a8222340e0b207e55037268128640c02a0480d0120202ea5c1152a09c9105c2b82d85c0d892046090596ba28b551612e8909545748a2b15e0d4930aa1782204c2925c14e2d0a3158506ac27a4d1152289c8d43e2ac1a1260bc2b0420984b6b82515c1242e08d1603d28817044131ad090d584769422b461112b0785584327c168561081f07a4901e0481e9441012e8709543f48a1f1360f0930761781d04c1b1440a42206c510396b41c3560dd2b06a5583428c140560cc1f05c49029048171440a9220544c02b4a0149440c52e84a9543048a179360b4930581782804c11944078220465101f4880f9300812803c510266b412b560912b0445582128c0e8560701f0c115c5e6ae2d3471512b09a9184146c1d1560c89b04e1581b06c0881004cae032150132b80b8540613602c5b0122480a86c0203201e150070680995c0142a01a1100404809247030230060980e02806814038a680a5140d26a0825d0212a81e9140c02803014025ae00a050040280324a015230085180a6b40435601d2b006050146ae0892402c2b0040db88697b9b47c6523e2a8fed446f6914babca3d164fe722772b1378f899c744adce24ee604b67c23af60fd620769f03749819a440acac04e4401f1900d83405c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 906 (dagTraceF m_41 s_41 8 f_41) l_41 0) s_41 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_0 : treeBlockF 0 32 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_1 : treeBlockF 32 64 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_2 : treeBlockF 64 96 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_3 : treeBlockF 96 128 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_4 : treeBlockF 128 160 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_5 : treeBlockF 160 192 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_6 : treeBlockF 192 224 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_7 : treeBlockF 224 256 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_8 : treeBlockF 256 288 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_9 : treeBlockF 288 320 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_10 : treeBlockF 320 352 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_11 : treeBlockF 352 384 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_12 : treeBlockF 384 416 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_13 : treeBlockF 416 448 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_14 : treeBlockF 448 480 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_15 : treeBlockF 480 512 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_16 : treeBlockF 512 544 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_17 : treeBlockF 544 576 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_18 : treeBlockF 576 608 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_19 : treeBlockF 608 640 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_20 : treeBlockF 640 672 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_21 : treeBlockF 672 704 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_22 : treeBlockF 704 736 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_23 : treeBlockF 736 768 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_24 : treeBlockF 768 800 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_25 : treeBlockF 800 832 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_26 : treeBlockF 832 864 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_27 : treeBlockF 864 896 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_28 : treeBlockF 896 906 (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
theorem nj_41_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_41_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_41_1 h1 h2)
theorem nj_41_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_1 (fun _ h1 h2 => treeBlockF_at nb_41_2 h1 h2)
theorem nj_41_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_2 (fun _ h1 h2 => treeBlockF_at nb_41_3 h1 h2)
theorem nj_41_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_3 (fun _ h1 h2 => treeBlockF_at nb_41_4 h1 h2)
theorem nj_41_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_4 (fun _ h1 h2 => treeBlockF_at nb_41_5 h1 h2)
theorem nj_41_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_5 (fun _ h1 h2 => treeBlockF_at nb_41_6 h1 h2)
theorem nj_41_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_6 (fun _ h1 h2 => treeBlockF_at nb_41_7 h1 h2)
theorem nj_41_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_7 (fun _ h1 h2 => treeBlockF_at nb_41_8 h1 h2)
theorem nj_41_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_8 (fun _ h1 h2 => treeBlockF_at nb_41_9 h1 h2)
theorem nj_41_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_9 (fun _ h1 h2 => treeBlockF_at nb_41_10 h1 h2)
theorem nj_41_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_10 (fun _ h1 h2 => treeBlockF_at nb_41_11 h1 h2)
theorem nj_41_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_11 (fun _ h1 h2 => treeBlockF_at nb_41_12 h1 h2)
theorem nj_41_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_12 (fun _ h1 h2 => treeBlockF_at nb_41_13 h1 h2)
theorem nj_41_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_13 (fun _ h1 h2 => treeBlockF_at nb_41_14 h1 h2)
theorem nj_41_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_14 (fun _ h1 h2 => treeBlockF_at nb_41_15 h1 h2)
theorem nj_41_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_15 (fun _ h1 h2 => treeBlockF_at nb_41_16 h1 h2)
theorem nj_41_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_16 (fun _ h1 h2 => treeBlockF_at nb_41_17 h1 h2)
theorem nj_41_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_17 (fun _ h1 h2 => treeBlockF_at nb_41_18 h1 h2)
theorem nj_41_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_18 (fun _ h1 h2 => treeBlockF_at nb_41_19 h1 h2)
theorem nj_41_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_19 (fun _ h1 h2 => treeBlockF_at nb_41_20 h1 h2)
theorem nj_41_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_20 (fun _ h1 h2 => treeBlockF_at nb_41_21 h1 h2)
theorem nj_41_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_21 (fun _ h1 h2 => treeBlockF_at nb_41_22 h1 h2)
theorem nj_41_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_22 (fun _ h1 h2 => treeBlockF_at nb_41_23 h1 h2)
theorem nj_41_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_23 (fun _ h1 h2 => treeBlockF_at nb_41_24 h1 h2)
theorem nj_41_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_24 (fun _ h1 h2 => treeBlockF_at nb_41_25 h1 h2)
theorem nj_41_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_25 (fun _ h1 h2 => treeBlockF_at nb_41_26 h1 h2)
theorem nj_41_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_26 (fun _ h1 h2 => treeBlockF_at nb_41_27 h1 h2)
theorem nj_41_28 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_27 (fun _ h1 h2 => treeBlockF_at nb_41_28 h1 h2)
theorem nc_41 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_41 g_41 bds_41 906 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := nj_41_28
theorem lb_41 : LowerBin m_41 s_41 g_41 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xff00ff00ff00ff00
def s_42 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_42 : Nat := 0x1100150015001700
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 6, g_16), (m_25, s_25, 5, g_25), (m_33, s_33, 5, g_33), (m_9, s_9, 4, g_9)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_25
  · exact lb_33
  · exact lb_9
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_42 : Nat → Nat × Nat := unpackForestF 0x4f9499f09202d3e522f4a45d9b4a128d5a651c4a34e97031284e654164a03901696eed39dda4bba528969d12d262497449228905d1448224113ba50872a0ee57a15283b952772a304d39dca83f9507f0a0ee179ed283d95c7b2a0ee149dc28bc34e770a002d1dc9ae39250722a0e4141522b37b5c6f4a0a915551af2a35d5469ca8d35511d3212e64244c80b994903202254470c48e1509d2a13954270bc4a1509b2d2385a270b44d1501d2a03954070aa4a154142a03601686a28e1441c2794e4f28c0252d24a7249464925a92069240c009433a8bc75148e92d1d15e4227884060e8ad1d1563f03074548e80d1db4e3b68474060049d95c5e2b8a456948acaf1595a314a062540c428159562d2785a4b0b40c159522b25a024cca11c141382609c4c11804259004e2008c400b480161001d010862317846290895a110bc320f064160885a110ac2c0b044290882d1269c24d0844160083b028bc0514808a90105e020b41094020a804050020ac080f010160201c020a40407404198001f 8 11
def l_42 : Nat → Nat → Option Nat := unpackLinksF 0x898226081c204180860207f0dfc07d8df607d05f407c85dac750dd217199c607181c607105c407101c216ca1b206b0dac06911a406901a026801a00668d9a066819a0649192064818e259d1660598166059815e457815e056895a056815a056815245481501540150053854645181403500140050013a34e813a04e813434d013404d013404b8cff83f80fe03e0cf803a9cea03a04e803a00e8035a4d413484d013384ce03380c833200c803184c603180c603088acb2b00ac02a84aa02a80aa02a80aa0290ca402900a40278c9e023248c0230086321807871e007611d807601d80649188460117845c117005c0158c5601580541150054015005020eac3a00e803810e003800e003800e003230c803200c802c30b001a900b0001 0x131179b22eceb5a9c6b324d59b1a8c93469a68b40524f8a0a3939382633e12454208f0390f062ead11c1aa4da50322a010142651c17138040712e06254164ec5e9c8bb23155aa294d356916ab30d39a9a6cb13934263280e42c18c7a50822a0f014239284745c8f6b90e57214a84005c7d0a114082289047b4e8e692e8d09bda0c692e8c245160ba24111945c872a0f814209ae42a507f0b8f614209a739b42088b900541fc283c35c7d4a0f8571eca83c34e7268523179ae2ec935e6d6bb24d3a45a4b8b426e6832094a21284315e412b30854a0ca8c09507e0bc30165e8293c851770a0ead71d12839950720a0e0d71bd28311385e268b80e1581a3282065240d04b99c913302e64044c48e16c1c2a8342e478bc4a168142e2385b270b44d0111e2b12855050d9175aa2d38c566e8aadad79b1aeb5b4e6a69ad28e98d1c2314937282c24e9809caf9385d26c584c474248704159074b00e55c1c2a03603062a48e0b89c288384b4a48a92940a72094a4f28c685092c96991404b4b46c90934a71f14a4c28c585092c96a501a4903078060ec0c171242e290864f0c896210183f03078d38eda123c5e468a48a968ad212215e412b480558f8a91592d3d03474060c89219a50322a062140bc9e1712c2d03071178de291b2522b4946a578d0ad181562c2a4564b4a51c14138040704054870a51384e180944c1182c211001d080804056834a11204e15094461180c211102d21058400744c160902c0402808120681e0c82c080382c0b04da7093421e8bc3b14870ad011421b0bc301685c2b0a8521405a220b0080e840140a4a01254020280303c05058080703e2f074520d2a404528302f0585a070ac06148080ecf34f93696ecd1d4da1a714b48286724eca8999284b1f086200ec04198001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 161 (dagTraceF m_42 s_42 7 f_42) l_42 0) s_42 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 64 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_2 : treeBlockF 64 96 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_3 : treeBlockF 96 128 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_4 : treeBlockF 128 160 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_5 : treeBlockF 160 161 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nj_42_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join nj_42_1 (fun _ h1 h2 => treeBlockF_at nb_42_2 h1 h2)
theorem nj_42_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join nj_42_2 (fun _ h1 h2 => treeBlockF_at nb_42_3 h1 h2)
theorem nj_42_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join nj_42_3 (fun _ h1 h2 => treeBlockF_at nb_42_4 h1 h2)
theorem nj_42_5 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join nj_42_4 (fun _ h1 h2 => treeBlockF_at nb_42_5 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := nj_42_5
theorem lb_42 : LowerBin m_42 s_42 g_42 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xff00ff00ff00ff
def s_43 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_43 : Nat := 0x17003f003f007f
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 6, g_15), (m_17, s_17, 6, g_17), (m_14, s_14, 5, g_14), (m_24, s_24, 5, g_24), (m_32, s_32, 5, g_32), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_8, s_8, 4, g_8)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_17
  · exact lb_14
  · exact lb_24
  · exact lb_32
  · exact lb_1
  · exact lb_3
  · exact lb_8
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_43 : Nat → Nat × Nat := unpackForestF 0x38948a00b4fdd12ff0a557850abba25de06367025b3810d9ba257dd0afefa9577d0abba15ddee366e855f740bfbba55ddcaaee8177758d9ba057005a3ee517b706abb834500527e9ed7f6c28bb6045d3daeed11b3682d9b406cd3dabecd17b4f69bb1b5cd8d3669ed1f5e69daf25ed78aeebc1774f68ba795fd65aaeb2d17590aba795dd5e3669e55f4f0bfa9355d49a2ea45574f0bba846cd3c2b80291f4c6a9a6254b562fe955b2d58b7a2356d1c1e6884d745279a2035b562d67adb33d4d99e96ccf4b067a1b33d0c16ac57cb22f658d7b2c4bd9615ecb0aee58573358b996152cc82e6641432c0bd9605dcb02e65b1732d2b996052b562b654d7322ac99135cc889c64d1532226991038c8e2a6440d2d58a78d349c789a63c0d31a6838d25ec68aee34176d56ad86349c589262c0930c6838625ec31236225371109b86244c3d226185770d4898605db552b5aa53f090b983456c1e2c60c116d529b80a5cc04aa602513012696a94bbeab45f5582fa6b97d25cbe82e5f4142d528f7c14cbc52a5e25b2f528978964bc40c5e4512f10296a943b5427ddc572eb8ad76458baca2daa136e62b973054b98225cc0d2d50976fd68b7eb05bed72df4b96f95cb7ca85aa11edd0996b154b58365b4112d60c96b02cb5c225ac092d508600a37b4a2f5a4976b16ab6825dac5a2d9917acc6bb66345ac52ad92d76c968b58a45afa3257d162be8a95f364af9aa584912be4c960244af92a57c532b146f5e14caed1bd62122b929b59245add26d64516b36a959a54accaa56449eb10880094fabab455c572a168f55a4daad1ad4251aa769553b46a9d235424daa58b152237a840c5448dea10280094ba792ed3c57a9568b4db5da6caf52a916968d14b454a59aa52c9529546e00947a4ca25215a2904b94815c9f5a3d1d1628d46f3ea54a1d26d0e8d68827b44125a1caa4fa51a7e6954204c9f9a34fc91a7f4753fa369fc9b4fc5527d26c009439ec9b0024ee3f8b73ba359dc1ac7f16a752d91fc579c22f4e0976702bd3805d8fe2b4d91b26c8c1364548fd2bc7e93e676b533b5699c1ac7e93663ad13195c98c2e47e91e586b52c356979284bc912584ad2c23e960a74b2552590292c1428fd1ac9e9364f46b2794e94c9a49e49a5027b2812593c0a47e56a476932635091ca2c8e4f6492812414491c92c7e55a3f09f2145690922c848d63f09b2015c8fc238024de3d29d1da468eca30024ae386d91c36073e2bb9ed6e3448d1a02573dad4645b1cf6af1645e8b1aec58d162c2bd1605d73dab39ed2e274b513a5689c12b9ed2a23ad11195c88c2e39ed1e0d8b506c598362c43a5721d0b906c5686dae41b1460d69d06a4e85e2841a53a0d29b09c5884e2841a13a0d09b0684c83a2c41c5320d084e7b4682d28404d5a024b5042448092b4048e60229d0195480c0a404509cf48cfb34a7fca63ecd19f648cfe1347d8a33ec4f9f7474fba367dc9b3ec051cf2b4fa2507b5a2bda925ed474f6a367bca03dc911ed26ce79567ac9f39e529e7690f3a5c79d2239e51dd98b4ecc567652d3b2959d9472ec94e771253b8919dc294ee1467649a3b44d1d909ae794673c1fba4d59d268ce924674c9a3a4519cf07ae814c73c1b80249dcc8bce625d6adaab94975ab68ae345e719aeb8cd15ab4aae1b5d70da2b56915b88c8dc4586e22a370d91b86a8de2446e132374911b84a8dc04c6ad1bb6c131b546ed59486cca6b588d5b149ad61356b5a235a911ad288d61276aca200213da8ad0d405c66da3b4a935a546acd846685a5342d19a148ccd83667e2c33c8dd9b058ce23766c1200212d984bacc05e61da2b2ad75950bcc3a4564234321151906a8c825461d1bb191a18c8b0c604c61c9bb10da1886b0c403c61c9380211d85088c1568608ae3041716f68ec04585fd1bade5517949abca355e89eaf4495790a8b78465c1a52ec5317068cb82465c51d2e28d97126cb80545bc1b00210d6d06c0083b49e2dad28d56926a93c5a59c3624f15d628bcb125d588aeac4179278acaf46c57a302bd151274ae93a4f565ad2b2d595926a93a4d556b42aa571550b893a47529ad294d59504a0a82445292b2948f94a09ca585452c0a2941092746aa445849caba4e53d416b4a0b5650522a828d5412ac9394d4fc2e24e51d396b89cb584e5a82748c139488939274c126a608d53009c9a1344c0132624f53124a9801449c2d250d252d6a0941454a09ea54501292889412549c2b0020dd2509c9194648c230020ad206d8903602b62b95ad6d1c48c8e1252b5ad2341b0ad6ae8a45e451aea28d15142ba8a05e2b5ab15ad2d0f4b487a5643c9295ad290bad08595c42c2e15ad1cf58b47ac593d62c20a571050b87ac5640dae1eb144f569c7aa4e3fa2c1fd140f529c7a94d3d4a61f5160f52847bc503dc201ea138f509a56b463cd281d4d58ea4b4782443a92b1d48e4ea09c758543ac0a1d4108ad48c743582b4ab9c6d70e36a07223038d2215a51cad27e6db4636d2d1b6958db4946da4636cab15a4f4d909856937335a51ac130cd68c66a4634c9a19a118cd07c6723a3391b19c4d8cd0285685a32d28188d14c44926223a3111b18c500c5488621362b42b1840f8ad0945f3482f92e17c910ad08e5745a2ba2b15c968ae4ac572392b8a7166928b348c5994a2cca315c4d0b12885704d2bd1a15c0b4ad08c008272a8ae1541708968e5324d2991a94c5388948c50b4a285a3142918a127c44a3627c2613c8dc892b84aa372689e9344949526c4b23a2591b12c4d89524c44954241269208d49126848126224a3114d288a68c4524622c9a1145188926c0081f2192e10c1706568e4124d2091a9041386528c3eb4a1f5a30fa9187d07c329361eca60f48dc650b838a371d89e8ec4947106c3923a1c91b0e44d87104c328541b1268d88d46d26836026194230ccd286668c3324619c9a0cc1186506c0081b185360c25b0610d80dc57175360ba5b05d0d80db5716d2e036d1c566ba2b3451592e8ac9141b4ac2745a14d2e09d1584e49a27235138a709c1381b48c2135a12dae084d584269423458118a608c1304268c212461089f0840f81b46c1da4d0ed1a8765583d2681d9260ec270365183369419b460cd2306655835268199460cc1f0364d82849a142350a0ab05c4d02824c1404e0a520054480292681402606c23038d281c68c0e246070ab0444d01c28c0f24007c9003c4d01c08c0e03e06c1b00205c190880aa5c05c2202a570150b80134704ca60248dc022480624d0311a81a4f40d24a0601400823006d28098b001b4600d230088e80446c0213600c0a0040d8010260001f 10 11
def l_43 : Nat → Nat → Option Nat := unpackLinksF 0x73a039c05cd43e6a0735039595cac0e56072b03930bc902e480724038e11c700e3417180b8c01c600e204710038705bdd7dee06f6077b01bd02de21ef1037881b9cadce06e7037381b885dc406e1077081b840dbc1ede036f01b741db80ed12f6785b3c0d9c0ece036311b180d8816c20b6101b041d8206b9235c81adc2d40bea0035001a704d360e97134a85a540d261693034885a1cad0e0687034381a181d0c0685073e919ec2cf6067b033c859e40cf20679033b079d80cec06740b3a019d00ce8067403388797d2cbe065c0f2e019700cb806590f2c819640cac1e4e2327019380c9c064c0b260192c1c940e3b3f1d818ec0c7606390b1c818e40c7206390318918c40c600e30031783880fc38261c030d058680c30160e2b068382c2c16060b03038981c0c0c0e060303018180c0a0dfd22fe817e83bf405fa02fb877dc0bee05f40ef6117a04bd005e60af3017902bb455d906eb8575c0bae05d312e9817481ba405d202e9017441b9245c902e3077180b8c05c30ee18170c0b801db822ca496500b260d8d1ac6816244b12058806c3836046b02058006be095e82af4057906bb855d81aec05740aba015cc1ae215672ab3815981aca0d6502b1075880abe1d5f02af8157c0ab81d590ea90f5402aa005462aa3015141a82254102a0034fc1a76253b029d034e41a6c1d330e960f4b00a5805251e92814940a3c3d1d068e8146c2a32150e2e819740c0a0214ff0a7f813e079f004f41278873c019de0cef0277813b039d024e706738139429c80ce402720139009c21cdd126c8936409ae14d50a6a81354099a44cd02658532c099604cb026581308998404c00a5f832dc89681cb4025a012d0095454aa0255012a8094a2ca40651052841942049d124e81274093a049d024d85230f9160c890a448122409100c8802440121438fe347f023f031f028f8047c023d831e428e43c700a38011c008de0c67223381194289cbc4e0226831340896144b022485104887e143f021f810dc886e04350a1a810d408680c34021a010ac98501c280214010a0083c541e020f0107808322c19020b8505c082e0417020a0705008221c11020881044081e140f02078103c081a140d020681034081a040a0dfc24fdc17e623f205f900fc027e003f001f800fc007dc13df3def02f7807b813da09ed00f6417b203d901ec80f6407ac1bd019e782f34279a03cd01e680f3407980bca09e18ef0c07840bc201e100f08077e1bbe05de82ef017760bbb01dd80eec077603bb01dd80ecc876603b205d396e94274a03a501d202e9007460b9b21cd80e642704bb8201c082dec66f6037711bb80dd816ea0b6f19b780db816d4236809b400d9c16ca136405b200d8826c4036105af84d54a6aa035405a982d4c06a01b5001a686d34069a034d01a506d1c36803b3e099f00cd0a6680333059788cbc065c0b2d059488ca406500b27059206c8436343b1a018d00c4c7626031301860ec2c16160309098384bf0b5f802fc017e00bdc55ee02f7017b80bc855ce5ae7017284b8c25c602dc1d6e00b6045aa1ad4056982b4c05a602d00d6608b2c159602c9096402b20059002c8016286b04457a22bd015d84ae4257202b9015890ac4055e12af015780abc055e02a6255300a9025460a9b214c06a6005300298014714a38051c028e01448aa20150c1285054280a0445020281014080a0404fe12703d38009ac54d212690134809a014d0026801301098004bc125e012f0097024b60a571127909381498124c01260092c1496024b01240690864840241051f848fc047e023e051e048d4743cba1e010e828740436121b010c84844841e120f01078081c840e020509028081404080a040102007ec93f019f800fc007e003dc51ee00f7007b803d229e900f38479c03ce01e700f20679003c219e100f08078403c201df08ef8077c03be01dc0cee0077003b411da00e42471c138621c204e100700238001c000e000700037c11af3cd7806a8535401a808d38268c4336419908cc026600330019800cc006600320419000c704634131a018b08c4846240310098800c400620031001850cbf8c5f812f8117c00be005f002f8017b04bc845c872e4017104b8805c402e2016e0cb6825b012d6096a04b5005a802d4016a00b5005a802c4416200b08258402c009552c9f2e4f8027811322898824bc225e012918940249822481124008f0c478023a091c048c86464023201160c8b00458022c01130c8806440021e090f00870242842140109048402420020e0903107e0e3e821f400f02877823b421da00e718730239021c410e2006e0c37001b608da046b8635c01ae00d40c6a0035001a800d10c6706338019a08cd006602320419000c7046302318018a08c1105d0e2e8017400ba005a8a2d4016a00b500580a2bc114858a40052002900148009a284d0026801320899004b8425c012e008e244700238011a088d004680234011a008a0c44042200110007f243f801f420fa007d003e021f000ea3875003a801cc20e600730039021c800d6386b0034841a400d2006804340019c10ce006604320417470ba005d002d8416c00b6005a042c8216400b00856082b0013c7088584400210410800801040001c8e0e4006a20320c18820c0106000300016860a440500828001304094104a0025001280088303c201a1000b20001 0x3654abc4a45ce5326c09131c4699ca56d8d23472577862ab6914da7ca2a42177850aae604d66422f071b3646d99ca5ce08b67021b2712c94f1448e52eefc9575f48b8da359c4ab0c61777d0aa31015dee364e2571620c8cc0444852eef09575e48b8d23518caeeee555620ac30816dd6362c4173874bfc225de012be569577149bb1247d7522e328d77f2bfbe15dde8abcde556d129b4e9458dc93ef217f760bbba0575842ab961359708a8f8271800bee517b716abb8345ce9b26c2d5314469b2356ce9a359a5769c2ab3714ddb4a2b8e175960aab004ddb022ed51b33a6b9b1a6cda4b66d01b3668bdb235cd8d366268d31246988a34d85a76c097b10469af95d9b0aaeb45362e28baf05d5782aea61351608b16964a6ca261e8d26e6bbadb55d69a2e1c8da2d2ac2f85dd642a8bc057578d91695c4503232a1130d468b035dd51aaea6d170c46c2f95dd48aaa281585d02da846c4502e6dcd7f6b6bbb3b57cadaaecad376268faeb45c2d1b6b857f582bbab1578acaad965369a28b35937d542fea21774f0ae8985571426b281155d06e2e017d2a346911534d6a9a6254ca9aa6955b33bac990464c613243c571050b90db58d1c1e206d6345279a4356cedaad5e566922a34c93dd189ab52165840a2c983dd101ae6b1632e8b19dc58ca628684db3414d9a016ccfcb067c1b33d0c19a950cb8286661732d0a19ac5c878ae664173330b999050cba2e65a571050b99dc5eca22ee74d7b394bd9c15ecdcaee6c5721c2ab9a152b1ca6d30517310bd9805dcbc2e2081572c0a4e084d64822e54d732626991834c9a2a63ed53172a991c54c79aa62c55329ac98ec64ca1ae62a9932727192934c901c6440d31f2698f034c4922622913206938eb41c712f62691b104898d95d980aad885369728b05125c682eaa4155be09ac88453c812e2e493160498914d978a2e1e4f60826b8884d54022e1a0f4f006b87a44c3522630d27156838a25ec4d236209130e2bb03955b04a6d2c5165d24b8605d3bc2ab761359008aa7825c10ac42c5525b26902924878ae612173078b02394ca662d61115abe2bd48952858a36065145b09b8304521c0c830046f82890dc5811826608973032a981144c049a42e5720e2997fd68bfab05fad72fc4b90b14cbdca05f6172fa0a17a954be0a65e4052f52892d134810925e45125926901924bdd2a4b0912024697b16cbd0b242a572f303178814ba42c1ec1514d06876824bb8ae20a172ec8b02304c64e2d5db1585b29b759456e02f306148f608d740452a80f02c04add08881c5811ca65d2572e80a973844b981a1f0170f709972568b8eb05c4d72e14b97015cb7ca81ec132dc0816d054b74265ae052da088a60343b0125ae1114b06875824b70aa294510ea2696d86cb64321ea172d80596b024d2e2fe9316f438b59e457cae2b64314f196ad85a56af4afd5a56e952af47953c28a7e0a537002977c947830a2de050e5726b009256dc2fb4e16d8f0aec0853bbc27dd4136e50976f0473d022daa10d4906a748252a40f90a06c5a02e0a013ae4225a717ad24bb63a55b2522d888d6b80896825db152ad98916c346b5b854b091a59d17acd6bb63b55b31a2d828dab608960234b29aed8ad56c968b5fa36a4e2e56a1121e2b960244ad022584912c248959844b012243cd12bc09163c64b1a2c58b152c46c961b54b053257e952be2995d858ac82a578532bb46f5c94dad4a2d68496b749b5aa45acc9356ad52b44a959954ae122d6c516b224f68b55b3da2d96956c848b5ea37ae8245621121b28952818abeb43fc95255488fea34ab8ae550552ab28953934a900c544051fc2495624daa122d568d5fb24d0dc5894c9a552d2aa868d53a46948a354b162a446efc1449409a3ee492a246f279367d89355ad1e4e48cfaa36aa8a354c4daa303150814a7d2ed309562e48b4ba35a78af3e64985808b4e35da61aacd8d169646d4d95e92c9b0ac1168e2a1042447b8924bc912482494cc6887232531152606c94bb5481d3252c9528d2a0f814491c9a3da4926f6ab4eb458ad2ad349169546f461409189b3d8498550aaa383739c13d1c93293289474587fca25255a28d4c948a5ca40ae5065528a28941134a3a2c500512882693f924a351bd0e4da7e24d44954a20aa5124f68026b44125a2d26d069168a46b43954a04aa500552840993f954a051d5008da7f26d42b4aa0da350491a7e2a947b47a312a50c51a7d26cf52369ec9b4e75924d2c939b5598522cd28f67846af29266342ab1c0f67706b39c589d4b64e717a724bb0e2559b122cc08d6712bcf21269c02e8a41565f489261549791a4dd1b2698d10e4649b6304d91525d468f116492caa4309525c488f01249a5ad4d0d5a1846d2b15a928ab3d0494e607b338352a00e88005665ad0f4b5c861264c8572630b8ef924979223bc492492892fa50979223b8552482892d1549640a4c2d6a606ad2ea569711f4aa56a472ad2d94e960a13ce495db2492103d1401a9c6094a703a1f8159440a4a649250029299349449ebf04d65024b2b24d7f922caa8d65429d2912693c0a4924d24c6a124124924a03b85524828926b49788aac965164a27af813591c9287c1544e0a81d8147689231d16a448ac7324d90d22c848d5d924cc6056138234805704e0993cc5b9da2d4e915e6f8ad35a579a927ccc9366248f0624595d1ac9c56a462ad1e12a79893bb04998b0af2284f90426c7e11c4d08a710272940e8740563d29d1e2468eca3416d11f42a91cb6c8a5b4438d92386c117354829223c8591f32a9184647c8b2412d1a304ab14a4a8d5233c6519890aac502d8d012c60d62322d9042348c22f45ed761c6ab1734581d1b45a579e226d1605d1282ac33152066a8f09548a52d45095a1948b0015a7c4ab3d25153c05b138252900e87205625ad10cb487a12e448572230b90a05c83c284371721e2b90e85c86dae42e572130b90bc5083820429162138a107c58838a608c132218b51045987e2c43915a1a8a30cb4e861273fc569f02ad0b14e854a6c2413a1109b0804c11422c1a108a303a1c0157bca241694208488ef1547b8a23ba4d208488ee124810aa4060520a6ad04a5a81d2b40c8e5fd2b4f6956814a7404509e726aed9344e41aba80b44404a5101d0dc0abf2051ff298fc0147f09a3ee051fc268fca3a7e11b3ee4da00694ff3467f5233f6519fa27cfb0147bd1a3e8941ee268f79407792a3dc911e46aaf9b457c924be28e9f046cf69360d82abd64f9e9690f425c79d223be511de268eea34770923be929de48cee94a770a33b40b43504ae981d0f40abb44d1e58b4f245678d2d3c4959e1472f014e76c9a3b21343408ae902d0f01288411033028e993474c9a314d69d66ac9e34a755a33a8919d228cc40561081b3a0530420791bc578d9adc66d6a316af15b568a9a5c4cd2a2268f06346805233ea569ec2acf514a798a3bb0519870ae9c04775c1fba20f5cf06e208352800e864055b3288e6c5e7312eb82955c348adf2356c8a2394975bf4aae32456f51ab62551bc468e445e71daeb82d55c668adda366c0a23748d1c46badfb5570da2b728d9858b8d79444142e374911ae288de2446f12235a511ba48882b446d824383191c08b0dfc546f9b237ad51bb4c8dca546d4ac358551b8098db04c6d51bb66535af28ad71256c526b5e915ad24cd7b446b92235a511b246ad81356b093b96d55c968ae2a5570922b6e8ddb4290d594440c2233e0b1a9ad06a9544d8a21a84d1a80b8d1054694223420d19e058ce02434c1234c935a248ad2a353481320716134068d1b4a689a33429193308ccfc586791b99e11131068670246711ba600d8cd04cd3b474bca31984d9a408cd003667416336091994bac925545922b228d45828acc05e3281332cd75926aaaf3456411b0ac515950bc96036600281e0910c5048a82444a4123271a1048c8c9454549b2322d50ef4c8c82545fc2818e111280686202463a340a51918d8b01f16463026314da04a6c8c4b580d8b23100f1616aacbb4544d2ab289158f46e2a95562c9bb0e49d7e0809383630c1330053185088c0458358223095a17f2c8c195c6082e2ea1517c088ba0346022c2e41117a068b88245fd1baf20d97004cbd8545e82a2f64f57226abd1255f526aea9157c46abc8545cc2a2ec531720a8b88545cd1d2e48d97126cbbb4a5d5a32e8919700a8c0b475f8aa2f01196f06c609365b41b2cb5912e0c8b2b5554d22ab68f56a46aa41555149ead24d4bc04cb2c5859c362cb179644ba8225557922aa48d5632ba291555882f17609951488968545411a2c11b15b8d08246457e302bd1514f4685c8644b02a2009514e4885b82456dad2b4d590046c9e93d5649aa6e1692b0ac5f8252100d06205957ad06035c401262ac571550b85b0245412216a0912a088a8a505412216615129088a605452c0a2a6d69526aca7a565391f2864f45026a9c9254d82d2501594d09ca50422f8129640908303418016516340a5191488b0a094c0bc3209e5502c02858824515ad288d594348a9ea3d5091aa825584f26c5802613ca627e1713a688158140a80a2748c035268170240a40a27ad713c6b022b544eda8272910342a8168340a00a26405134048988144d09a2644f4cf26a989254dd269aa9153646a9a84e4cc132600512a26896b504a492254500b32a8949444b9a49725552c28a9593d31c9aa504942f0aab5c5b5a22d2cd15d618acaea5757127ab09355448e7a2455251aa8e55d4629ea014d4f8a389a5153824e9785a49c2b2480a8bd04e568262040d04e0592509c9214648c231e6d10cb0a890b6c445b4208d91206c08b3543c922176190ca0a88c464324321e2d19184aa88a4a475231d0554df25a8e1252e823230d611a0d8782344622f22ed75046aa8b3453bd1b22a5744a2aa8a05e2e41b203150ee6a85c0544452d2209590148a6e92d43c929ae168c80ac600452000d04c0590dad080b482fd2e2185710b0b87f95c3e8a8207171062b88285c40dae1fc570f80b87fc583fa281f5160472987b84c3e2281ee101098b48445941e2c209159028a280b4e401271fa538fc29a7d94c114a29f2508d50b4638563d8271ea1347f03412816318221e6940f04885a854314221680d0f0488598243b02a1d6050f26ac78a5a3bd2b1dc8e4e326a7012d110929a8168c40ac7684e3a82117c0d4b20683f01a0900b1beda04a6c87435836c9e046190e46881001407c0a1c88c03d248110340780a1ccd70dd6b022b54395a81c69103c268108540740a0865101c02857834381a31be968de4ac6ea4a371231b65584324c5704610c9e1b2130d00286b04c33c0a1a60d0ce028699343411d19e8d8ce26c6bb4a355a31a8918d208c6883e3340a18c8d0cb4a062934318a016a950c54885db55329a2992924c847463a363109b046154c207c603482fd2e17c910b62885a9342d11a166490b64945aa462d0a5166518b105a110252bc0e85c054b128857a342f22d177158ba4b45ca562e11c96e538b22685804d0842295c0b42d04a8fc57479ada36d69196ae89b56449a5a1cd290a68e7a3463a5231ce55ce228e7093f3689e9b04dc4126a6605a30c2b182128bd08e568461f00d0360589f0b82304428d2a14e910a24684f16c270b21565708d2a8491442309a1541709b2a84d15422c92150934a348a53a35264aa14c5388a24c4c15425caa032530962a848934291a5146d18a248c4a954240a31424f89f0984f23725ca21344d0962484d93d25c9a934494984744ba362589b1388dc9926c4a926244921224d09349a46a452491a920498460984593422c9a11cd288d68c46246228a3152d1ca548c50236274ae1285508f28c449361ec2e08e110874b83f95420ca20fc4d07a0d83c0642182e0d21506e088340341dc2a0ec150670484224d1fd229068d4750a84104e198130e8150730a80b84c1c82a0da0d0806943fb461f9230e21506c08c3e83e1eca60f48dc730883b0341c8120ee4f47326a3b1251d11d0e68d87226c3c2371d41b0e20986d048369341bd268d29146e46a3602611ca60ce0d0672683534a1a5a30d09186608c42b47204a30f84d8790b8380541ac230ca0d8634d8292641612a0c45b0610d82fa6c129320ac9505e2d82e86c04c080b6970454a8282441111a0705503f2881b9340942a0601102406809010165ae8a4d545868a2ba5d1292a8ac9143e26c1b1260bc1b046098534b81a924088120a9168528ac28a4d115228a08d44f29c1a126138270420984b6b82445811ca608c1303d26817034131ad094d584969422b46111230785184327c168461081f07a4901e0481e934101268709143f46a1f1560f0930761381d04c1a9340a41a06a4d0396941c3460dd2306c5583428c140460cc1f05c49029048171340a91a0544802b480149340c52684a9143046a179560b4930581382804c111340781a0444d01f4680f9200812003c4d02669412b46091230465582128c0e8460701f0c115c5c6ae2d3471552b09a9184146c1d1460c89b04e1181b06c0881004ca6032110132980b8440612e02c570122480a85c0202a01e110070680994c0142201a0d004048092370301b0060980e028068140389e80a4d40d24a0824d0212281e8d40c028030140262c00a050040280323a0151b0084d80a6940434601d230060501468e0892402c230040db8869fb9b47dbd27e9c91ed446f5814fa80a5d2851e7c2873d13b8f89bc744adce24ed504f66825b0c11d6e086b603b4981ba440acac04e4401f1900d83405c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 906 (dagTraceF m_43 s_43 8 f_43) l_43 0) s_43 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 64 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_2 : treeBlockF 64 96 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_3 : treeBlockF 96 128 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_4 : treeBlockF 128 160 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_5 : treeBlockF 160 192 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_6 : treeBlockF 192 224 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_7 : treeBlockF 224 256 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_8 : treeBlockF 256 288 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_9 : treeBlockF 288 320 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_10 : treeBlockF 320 352 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_11 : treeBlockF 352 384 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_12 : treeBlockF 384 416 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_13 : treeBlockF 416 448 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_14 : treeBlockF 448 480 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_15 : treeBlockF 480 512 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_16 : treeBlockF 512 544 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_17 : treeBlockF 544 576 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_18 : treeBlockF 576 608 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_19 : treeBlockF 608 640 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_20 : treeBlockF 640 672 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_21 : treeBlockF 672 704 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_22 : treeBlockF 704 736 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_23 : treeBlockF 736 768 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_24 : treeBlockF 768 800 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_25 : treeBlockF 800 832 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_26 : treeBlockF 832 864 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_27 : treeBlockF 864 896 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_28 : treeBlockF 896 906 (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nj_43_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_1 (fun _ h1 h2 => treeBlockF_at nb_43_2 h1 h2)
theorem nj_43_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_2 (fun _ h1 h2 => treeBlockF_at nb_43_3 h1 h2)
theorem nj_43_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_3 (fun _ h1 h2 => treeBlockF_at nb_43_4 h1 h2)
theorem nj_43_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_4 (fun _ h1 h2 => treeBlockF_at nb_43_5 h1 h2)
theorem nj_43_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_5 (fun _ h1 h2 => treeBlockF_at nb_43_6 h1 h2)
theorem nj_43_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_6 (fun _ h1 h2 => treeBlockF_at nb_43_7 h1 h2)
theorem nj_43_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_7 (fun _ h1 h2 => treeBlockF_at nb_43_8 h1 h2)
theorem nj_43_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_8 (fun _ h1 h2 => treeBlockF_at nb_43_9 h1 h2)
theorem nj_43_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_9 (fun _ h1 h2 => treeBlockF_at nb_43_10 h1 h2)
theorem nj_43_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_10 (fun _ h1 h2 => treeBlockF_at nb_43_11 h1 h2)
theorem nj_43_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_11 (fun _ h1 h2 => treeBlockF_at nb_43_12 h1 h2)
theorem nj_43_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_12 (fun _ h1 h2 => treeBlockF_at nb_43_13 h1 h2)
theorem nj_43_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_13 (fun _ h1 h2 => treeBlockF_at nb_43_14 h1 h2)
theorem nj_43_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_14 (fun _ h1 h2 => treeBlockF_at nb_43_15 h1 h2)
theorem nj_43_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_15 (fun _ h1 h2 => treeBlockF_at nb_43_16 h1 h2)
theorem nj_43_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_16 (fun _ h1 h2 => treeBlockF_at nb_43_17 h1 h2)
theorem nj_43_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_17 (fun _ h1 h2 => treeBlockF_at nb_43_18 h1 h2)
theorem nj_43_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_18 (fun _ h1 h2 => treeBlockF_at nb_43_19 h1 h2)
theorem nj_43_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_19 (fun _ h1 h2 => treeBlockF_at nb_43_20 h1 h2)
theorem nj_43_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_20 (fun _ h1 h2 => treeBlockF_at nb_43_21 h1 h2)
theorem nj_43_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_21 (fun _ h1 h2 => treeBlockF_at nb_43_22 h1 h2)
theorem nj_43_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_22 (fun _ h1 h2 => treeBlockF_at nb_43_23 h1 h2)
theorem nj_43_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_23 (fun _ h1 h2 => treeBlockF_at nb_43_24 h1 h2)
theorem nj_43_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_24 (fun _ h1 h2 => treeBlockF_at nb_43_25 h1 h2)
theorem nj_43_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_25 (fun _ h1 h2 => treeBlockF_at nb_43_26 h1 h2)
theorem nj_43_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_26 (fun _ h1 h2 => treeBlockF_at nb_43_27 h1 h2)
theorem nj_43_28 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_27 (fun _ h1 h2 => treeBlockF_at nb_43_28 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_43 g_43 bds_43 906 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := nj_43_28
theorem lb_43 : LowerBin m_43 s_43 g_43 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xffff0000ffff0000
def s_44 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_44 : Nat := 0x11170000153f0000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 5, g_18), (m_20, s_20, 5, g_20), (m_22, s_22, 5, g_22), (m_24, s_24, 5, g_24), (m_34, s_34, 5, g_34), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_20
  · exact lb_22
  · exact lb_24
  · exact lb_34
  · exact lb_0
  · exact lb_1
  · exact lb_6
  · exact lb_8
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_44 : Nat → Nat × Nat := unpackForestF 0x342e8b47149624ec491c35d108e5169128215028ac415841b801f 4 11
def l_44 : Nat → Nat → Option Nat := unpackLinksF 0x887a787878786360606052503b0e01 0x685d30ab0d74daa903654a08541a2d1c5620ad8d1ed25d13b9246e11c41b801f 8 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 14 (dagTraceF m_44 s_44 7 f_44) l_44 0) s_44 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 14 (dagCheckNodeF m_44 g_44 bds_44 14 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 14 → (dagCheckNodeF m_44 g_44 bds_44 14 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xffff0000ffff
def s_45 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_45 : Nat := 0x153f0000177f
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_35
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
def l_45 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 0 (dagTraceF m_45 s_45 7 f_45) l_45 0) s_45 7 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_45 g_45 bds_45 0 (dagTraceF m_45 s_45 7 f_45) l_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xffffffff00000000
def s_46 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_46 : Nat := 0x1117153f00000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 5, g_26), (m_28, s_28, 5, g_28), (m_30, s_30, 5, g_30), (m_32, s_32, 5, g_32), (m_34, s_34, 5, g_34), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_28
  · exact lb_30
  · exact lb_32
  · exact lb_34
  · exact lb_2
  · exact lb_3
  · exact lb_6
  · exact lb_8
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_46 : Nat → Nat × Nat := unpackForestF 0x342e8b47149624ec491c35d108e5169128215028ac415841b801f 4 11
def l_46 : Nat → Nat → Option Nat := unpackLinksF 0x887a787878786360606052503b0e01 0x685d30ab0d74daa903654a08541a2d1c5620ad8d1ed25d13b9246e11c41b801f 8 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 14 (dagTraceF m_46 s_46 7 f_46) l_46 0) s_46 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 14 (dagCheckNodeF m_46 g_46 bds_46 14 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 14 → (dagCheckNodeF m_46 g_46 bds_46 14 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xffffffff
def s_47 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_47 : Nat := 0x153f177f
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_35
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
def l_47 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 0 (dagTraceF m_47 s_47 7 f_47) l_47 0) s_47 7 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_47 g_47 bds_47 0 (dagTraceF m_47 s_47 7 f_47) l_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def g_48 : Nat := 0x1117153f153f177f
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 9, g_43), (m_41, s_41, 9, g_41), (m_38, s_38, 9, g_38), (m_36, s_36, 9, g_36), (m_47, s_47, 8, g_47), (m_46, s_46, 8, g_46), (m_45, s_45, 8, g_45), (m_44, s_44, 8, g_44), (m_42, s_42, 8, g_42), (m_40, s_40, 8, g_40), (m_39, s_39, 7, g_39), (m_37, s_37, 7, g_37), (m_35, s_35, 7, g_35), (m_10, s_10, 6, g_10), (m_11, s_11, 6, g_11), (m_12, s_12, 6, g_12), (m_15, s_15, 6, g_15), (m_24, s_24, 5, g_24), (m_13, s_13, 5, g_13), (m_21, s_21, 5, g_21), (m_22, s_22, 5, g_22), (m_23, s_23, 5, g_23), (m_19, s_19, 5, g_19), (m_25, s_25, 5, g_25), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_31, s_31, 5, g_31), (m_32, s_32, 5, g_32), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_18, s_18, 5, g_18), (m_14, s_14, 5, g_14), (m_20, s_20, 5, g_20), (m_8, s_8, 4, g_8), (m_6, s_6, 4, g_6), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1), (m_0, s_0, 4, g_0)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_43
  · exact lb_41
  · exact lb_38
  · exact lb_36
  · exact lb_47
  · exact lb_46
  · exact lb_45
  · exact lb_44
  · exact lb_42
  · exact lb_40
  · exact lb_39
  · exact lb_37
  · exact lb_35
  · exact lb_10
  · exact lb_11
  · exact lb_12
  · exact lb_15
  · exact lb_24
  · exact lb_13
  · exact lb_21
  · exact lb_22
  · exact lb_23
  · exact lb_19
  · exact lb_25
  · exact lb_26
  · exact lb_27
  · exact lb_28
  · exact lb_29
  · exact lb_30
  · exact lb_31
  · exact lb_32
  · exact lb_33
  · exact lb_34
  · exact lb_18
  · exact lb_14
  · exact lb_20
  · exact lb_8
  · exact lb_6
  · exact lb_3
  · exact lb_2
  · exact lb_1
  · exact lb_0
theorem sub_48 : ∀ b ∈ bds_48, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_48 : Nat → Nat × Nat := unpackForestF 0xf7363fbc71f7263f716ff9c71f9b71f7163f706ff7c71f7b71f706300c57f635600b5bf536600b4bf4244f345bf325600a5bf1c6bf1a6600a4be127ee796feea7cee818ee814e796be7967ed16ceca74e7963e786fea17cea02cea024e786be7867e886ce8174e7863e127ce628ce6274e117fe4b8ce4934e1173e328ce3274e107fe1b8ce1834e1073dfd67dfa66dfa5600a33de944dbc5bdbb5bdd134dbb43dc233db9560095bd7c6dda37cd7b4bd7a4bd857dd827cd7a3300957d2c6bd6134d2b6bd5134d2b43d4233d2a66d3233d29660094bcdd6acdb6bd0a6ccda6bcf67acf26ccda33ce233cd96a00947ca37eca37ccbc8cca273caa71ca172c6567c6366c6356c7a66c7a44c626bc6a76c625b0093fc5134bf373bf27ec3a71bf17ec126bc1263c106bc1063bf17cbfa8cbf824bf073bbd67be134bbb6bbd376bbb5bbb966bb95600933b8473ba371b827eb827cb8c71b8172b2567b7466b246bb5c76b5a44b245bb2266b2256b317eb317cb2d67b21420092fb1144ab473ab27eafb71ab17ead36bad363ad06bad063ab17caba8cab824ab073a5d67aa466a5c6ba9144a5c5ba797ea797ca7567a5a4ea5966a595600923a48449dc5b9db5ba30349db43a20249da5ba10249da43a00249da339e2339e1339e1239d8560085b99c6d9c37c99b4b99a4b9a57d9a27c99a330085790c6b9803490b6b9703490b439602490a6b9502490a439402490a339323390966912339113391123908660084b8bd6a8bb6b8ea6c8ba6b8d67a8d26c8ba338c2338b86a008478837e8837c89c8c8827388a718807284567843668435685a6685a448426b84a768425b0083f830347d373820247d2737d17e80271801717d07e7da6b7da637d96b7d9637d07c705677c0347036b7b3767035b79a66798247026b78276780247025b7707475a8c761747588c72e7772a7672a667397c73567728247023371923700667092370056008336cc736eb716ca7e6ca7c6d4716c87266d676bc6666c6b6a4766a24466c5b66a6666a566787e6787c67567668420082f658445fc73648245fa735f97e62b71629715f87e6036b603636016b601635f87c50d675ec6650c6b5d84450c5b5c2665c02450a6b5aa765a82450a5b598745828c589745808c5567755276552665617c55d675502450a435387e5387c535675094e52133508665113350856008234f9444a4734e9344a3734d3714d2714a17e4ab6b4ab634aa6b4aa634a17c3b567494663b46b481443b45b4715445d6b4645b459343b36b4457b443763b35b4317441b8c422744198c3de774097c3db763f96c3db663ea7c3e5673d9343b3433ca333b1663ba333b1560081f3a04434c733903434b7337b7137a713487e3536b353633526b352633487c25d6733c6625c6b3284425c5b318543056b30c5b3003425b6b2ed7b2eb7625b5b2d8742c38c2ca742c08c286772b07c283762a06c283662927c28d672803425b43272332586626233258560081b24a481e47323a381e37322471223711e2721e27020471203711e1721ec711eb711e072125671d4661246b1bc761ba481245b19d6b19b6619a381236b1857b183761235b1738c14e7714b7614b661556714a381234313b431226a12b431225a0081710c7310b73015670fc660146b0145b0e56b0136b0cd7b0cb760135b0bb8c0a6770a3760a3660134308b6308a6301c5707b5601b5b01b4b0645b01a5b04c6b04a6601a4b03a7c02567022660225601a3301124008130003f 9 11
def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x34f5e9e0d117a08f3f167a2cd51990f30165c2c99189cf0b45faebe87763aec05ce5b9076b3ad225948af1d5c12b70d6c1ad815b02b31d641ac815886b00d5e1ab835702ae05563aa835502a90d501a7194e029c05342a6814d029815300a6014b0a96052c0a505452a86250449cdf3982720ce409c81378e6f04d83991131866304c41988131026204be3968b2d025a04b2196412b0e5604aa19541290e4a4492192412482480c9009201228e45048818fcb1f063e047c08f051e023b0c6c58d811b0236046c08d051a02330c5a68b41158a2b045608a07140228045008a01111a220444088050c9e190430186010b86160c2a18313050a0a0412182410482080c06580c1010602040408005000200040008000ff09fd0bee67dc0fa89f503ea07c86f901f203e407c80f619ec03d807a84f19de303c417880f085e103c2077c4ef05dd0bb8174d2e981d20ba407480e78dcf039c17380e609cc039427280e501ca038e36fd0df05be037a16f40de81bd037436d4ada81b5036816d00d88db1036016c00d709ae035826b00d585ab035606ac0d40da0433e167c0cf819e0b3c06780cd8d9b03341654aca0594032806484c901910b1856300c6018c031806284c501890b06660c0c0898102fe25fc0bf817f02f835f00be017c02f805d8cb79d6f02dc15b80b6856d02da05ac4b5816b02d225a40b3896702ca25886b1016202c405842b0055a32b405642ac81580a9e95344a6814c0a9805300a585462a8c05142a281450286250c0a18143028605044a0053a327404e049c0136126c04d809b01331a6604cc0998133025a6498e9301250a4a049029201240244248809101201240047848f011c1232346408c81190230145c28899110222043c487050e021a143408605034a06040448080ff11fe03fc07e88fd01fa03f407e80f829e653cc07888f009dc23b807608ec01d613a447480e901ce239c07288e501c6238067000df09be037826f00dd09b81358c6b00d509aa035026620cc0194232806408c80190031846300c6018c031806094bc297802e845c84b7116e02d445a80b4096422c805900b0116002b845700ac115232a405404a8014e129c05304a5093e627c04f049e013a125504a80902920022ca45808b011222240448089010e221c043808510fa81f023c8c7900f201d483a047400e801c0837846e08d631a82338c6608ca1194032045d38ba017022e005b08a49144228044c20961120623084508862108220843e187a10ec41d0439086a40d401a8032186400c0417842f005c10b8017002c105800ac215802b00503088c0d9c01d0001 0xfba71fa171ba92fb0923f80716f02f650234f01f3981b2401711013fbc71f9971cb14fc4943f78718904f828434e01f3881b2301710813e5a33c4132b0122b8a3e20825caa5e20025fa471f9b71e4343ca24eb823e81843640331f825e2a3381032638226d13e1f1268895e1e926f8471f7b71e1343bf243ab2338814e6c93e1e126fc363fb263e0a33fa96ff9163c993fbe933b792faa923f886ff70638783f7c8336c02f5f0234981f3401b1d81710013b712faa1236b82f5e8234901f3381b1d0170f813f6356f225bd695bd1157b692fa99239885b8f0576b02f5e0234881f3301b1c8170f013b612f6a82f1c017f5366f3a6bde16bd9967b512fa8923a406b9b8676982f5d0234781f3201b1b0170e813f42444681f3101b1a8170e013c813f8603f1a017f3c5bf3256d595bd0157c714fbd9439785b8e0578504f7b8434501f2f81b190170d8134481f2f01b188170d013c693fbd1338483f7b0334401f2e81b180170c813f246bf1a66dd96bd9167c614fbc943a386b9b0678404f7a8434381f2e01b178170c013e697de5171e387de2071ef978ed164efa7cef018ee814ec960ed16ceca74eb078e8864eb17cea82cea024e8060e886ce8174f016fee16bed967ec163eb86fe986be9067e78634281f2d01b170170b813e6a8ce6274e538ce4934e3a8ce3274e238ce1834f0a7ee727ce597fe4173e287fe10734101f2b81b168170b0134001f2a81b160170a8133f01f2981b158170a013e0d67e0266dfa56dc96bd7967d495bce957a286b998679685b8c8573d01f2781b1401709813de944ce266dc166dd134dc2337a0335c823de45bddb5bdcb43cda56db9569585b790435b833d8a33da37cd8d7dd827cd415adac6dd9b4bd924bd7a33d394ad6134d4276d3176d5134d4233d3233788335b023d6c6bd5b6bd4b43d3a66d2966a186b778435a033cfa33d0a6ccfe7acf26cce17ace233d1d6ad136bd026bcea33cd96acba71cbc8cca980caa71ccb7ecc37ccb273ca172a7122c8266c7a44c6a76c9d67c9366c8b56c726bc625ba6922c398cc5134c3a71b392ec0071c2a6bc2263b312ec186bc106359023c028cbf824c4b73c427eb2a3ec317ec097cbf07357833be134bd3765702356823bed67bdb6bbcb5bb223ebc166bb956a086b9485b54833ba28cb8980ba371b8c71bac73b9a7eb927cb8172b2942b7466b6476b5a44b397eb317cb2d67b7d67b6c6bb545bb4a66b4256b2142af98cb1144afb71a813eac071aeb6bae363a793ead86bad06376833ac28cab824b0c73b027ea724eaf17eac97cab07375043aa466a9144a817ea797ca75677483374033aad67a9c6ba8c5ba6a4ea6166a59569f86b9385b72043a48448c1669f066a3034a20249e866a10249e066a00249f2339e9339e123a445ba3b5ba2b43a1a5ba0a439fa338b9569d8569aa339c37c9ad7d9a27c9305a9cc6d9bb4b9b24b99a339284a9803493176920769703496024918769502491076940249323392233919339112398c6b97b6b96b4395a6b94a4393a3392966908668da338ea6c8de7a8d26c8c07a8c2338fd6a8f36b8e26b8ca338b86a89a7189c8c8888088a718ab7e8a37c8927388072530228626685a4484a7687d678736686b568526b8425b528228088c830348008c8202480a71801716802e7f26b7ea637e16b7d963759236782e82b7381a73752338117e6713e7f87e7d07c7c0347b3767a2667982478a76780247387c770747397c7617476a8c7588c730247397c735677567774a767426671876708667282471923709237cd677bb6b7ab5b7926b77a5b722336693e71066700566ea8c6d0806eb716d4716f4736e27e6da7c6c872670426bc666ac766a2446807e6787c675676c5676b46b69c5b6926668a56668426308c658446288c6482463371629715403e61b6b613636096b60163581335383e654736427357a436397e5314e6207e5f87c5ec665d8445ca665c0245b2765a8245607c598745617c589745928c5808c558245617c55d6757e775727656a665207651066550245407e5387c5356752133511335f5675e46b5d45b5ba6b5a25b54a435294e51866508564d98c4f9444d18c4e9344db714d2714c36b4bb634b26b4aa6341a334f4734e373413434c97e4a17c4946644b6b4726b46b7b4814447154461344645b46d6b4593444d7b443763e97c431743ea7c4227442b8c4198c3e1344097c3f96c3ea7c3e56741677403763f3663c9763b9663d9343ca333ba3349d6748c6b47c5b4536b43b5b3d3433c1663b1563808c3a0443788c390343837137a7136b6b3636335a6b352632c23339c7338b732bb433707e3487c33c662f36b31a6b3137b32844318543083430c5b3156b300342f57b2eb762907c2d8742927c2ca742d38c2c08c288342b07c2a06c2927c28d672be772ab7629b662707626066280342723326233345673346b3245b2fb6b2e35b27b43268662585622a8024a48209801f080090102228023a38201801e8800881022c712237120c71203711f4711eb71244732337316b4321a72212701f9721e07208010078101d46618b6b070101c4761ab7b1ba4806810060101ad6b1a36619a3805810050100481018d7b1837604010038101738c152380301002810020101556716e771637615b6613a7a12a6a14a380181013b4312b431dd671cc6b1b45b1936b17b5b143431326a1225a0101009124089241147310b730b34308124079240fc660d36b071240e37b06924061240e56b0592405124049240d57b0cb7604124039240bb8c0312402924021240b6770ab760a366019240936308a630323307b560525b0626b0645b0546b04a6603a7c0356702a6602256084570735b06b4b05a5b0424b01a33105670f46b0ec5b0db6b0c35b09b4301124f6c57f5b5bf4b4bf2a5bf124bdf233db15bd7157d214bcd147c593fbb133b192fa51239d05b990579004b8b0478383f6f8336602f500233a81f2501b11817008130003f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF fullMask g_48 bds_48 (dagRefF 505 (dagTraceF fullMask rootStock 11 f_48) l_48 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_6 : treeBlockF 192 224 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_7 : treeBlockF 224 256 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_8 : treeBlockF 256 288 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_9 : treeBlockF 288 320 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_10 : treeBlockF 320 352 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_11 : treeBlockF 352 384 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_12 : treeBlockF 384 416 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_13 : treeBlockF 416 448 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_14 : treeBlockF 448 480 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_15 : treeBlockF 480 505 (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nj_48_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_1 (fun _ h1 h2 => treeBlockF_at nb_48_2 h1 h2)
theorem nj_48_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_2 (fun _ h1 h2 => treeBlockF_at nb_48_3 h1 h2)
theorem nj_48_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_3 (fun _ h1 h2 => treeBlockF_at nb_48_4 h1 h2)
theorem nj_48_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_4 (fun _ h1 h2 => treeBlockF_at nb_48_5 h1 h2)
theorem nj_48_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_5 (fun _ h1 h2 => treeBlockF_at nb_48_6 h1 h2)
theorem nj_48_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_6 (fun _ h1 h2 => treeBlockF_at nb_48_7 h1 h2)
theorem nj_48_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_7 (fun _ h1 h2 => treeBlockF_at nb_48_8 h1 h2)
theorem nj_48_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_8 (fun _ h1 h2 => treeBlockF_at nb_48_9 h1 h2)
theorem nj_48_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_9 (fun _ h1 h2 => treeBlockF_at nb_48_10 h1 h2)
theorem nj_48_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_10 (fun _ h1 h2 => treeBlockF_at nb_48_11 h1 h2)
theorem nj_48_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_11 (fun _ h1 h2 => treeBlockF_at nb_48_12 h1 h2)
theorem nj_48_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_12 (fun _ h1 h2 => treeBlockF_at nb_48_13 h1 h2)
theorem nj_48_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_13 (fun _ h1 h2 => treeBlockF_at nb_48_14 h1 h2)
theorem nj_48_15 : ∀ i, 0 ≤ i → i < 505 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_14 (fun _ h1 h2 => treeBlockF_at nb_48_15 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 505 → (dagCheckNodeF fullMask g_48 bds_48 505 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := nj_48_15
theorem lb_48 : LowerBin fullMask rootStock g_48 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def wg : List Gate := [⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [3, 1]⟩, ⟨GateOp.and, [3, 0]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.and, [14, 11]⟩, ⟨GateOp.or, [8, 0]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [17, 13]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241856 * 2 ^ 32 + 3938510976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241856 * 2 ^ 32 + 3938510976)) (13 - 1) := by
  rw [show canon fullMask (4008241856 * 2 ^ 32 + 3938510976) = g_48 by decide]
  exact lb_48

end PEqualNP.Outside.L_meta_47735

theorem PEqualNP.Outside.L_meta_47735 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241856 * 2 ^ 32 + 3938510976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241856 * 2 ^ 32 + 3938510976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47735.table2_from_lowerBin (4008241856 * 2 ^ 32 + 3938510976) 13 PEqualNP.Outside.L_meta_47735.root_lb PEqualNP.Outside.L_meta_47735.wg 18 rfl PEqualNP.Outside.L_meta_47735.wfits PEqualNP.Outside.L_meta_47735.weval
