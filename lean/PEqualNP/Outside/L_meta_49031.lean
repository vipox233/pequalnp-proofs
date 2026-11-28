import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49031

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

def m_0 : Nat := 0x4040404040404040
def s_0 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_0 : Nat := 0x4000404040
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

def m_1 : Nat := 0xa0a00000a0a0000
def s_1 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_1 : Nat := 0x20000020a0000
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

def m_2 : Nat := 0xcc000000cc0000
def s_2 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_2 : Nat := 0x40000004c0000
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

def m_3 : Nat := 0x4444444400000000
def s_3 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_3 : Nat := 0x4044400000000
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

def m_4 : Nat := 0xa0a0a0a00000000
def s_4 : List Nat := [0x202020200000000, 0xa000a00000000, 0xa0a00000000]
def g_4 : Nat := 0x2020a00000000
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

def m_5 : Nat := 0xc0c0c0c00000000
def s_5 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_5 : Nat := 0x4040c00000000
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

def m_6 : Nat := 0xcc00cc00000000
def s_6 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_6 : Nat := 0x4004c00000000
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

def m_7 : Nat := 0xf000f0000000000
def s_7 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_7 : Nat := 0x100070000000000
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

def m_8 : Nat := 0xaaaa
def s_8 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_8 : Nat := 0x22a
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

def m_9 : Nat := 0xcccc00000000
def s_9 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_9 : Nat := 0x44c00000000
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

def m_10 : Nat := 0xf0f000000000000
def s_10 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_10 : Nat := 0x107000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_10 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 1 (dagTraceF m_10 s_10 3 f_10) l_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_0 : treeBlockF 0 1 (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) i = true := fun _ h1 h2 => treeBlockF_at nb_10_0 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0xff000000000000
def s_11 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_11 : Nat := 0x17000000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 1 (dagTraceF m_11 s_11 3 f_11) l_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 1 (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) i = true := fun _ h1 h2 => treeBlockF_at nb_11_0 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xff0000000000
def s_12 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_12 : Nat := 0x170000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 1 (dagTraceF m_12 s_12 3 f_12) l_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 1 (dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12) = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12) i = true := fun _ h1 h2 => treeBlockF_at nb_12_0 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0x4444444444444444
def s_13 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_13 : Nat := 0x4044400444444
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

def m_14 : Nat := 0x2222222222222222
def s_14 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_14 : Nat := 0x2020202020222
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def f_14 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_14 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 64 (dagTraceF m_14 s_14 5 f_14) l_14 0) s_14 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_0 : treeBlockF 0 32 (dagCheckNodeF m_14 g_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) l_14) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_1 : treeBlockF 32 64 (dagCheckNodeF m_14 g_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) l_14) = true := by decide +kernel
theorem nj_14_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_14 g_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) l_14) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_14_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_14_1 h1 h2)
theorem nc_14 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_14 g_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) l_14) i = true := nj_14_1
theorem lb_14 : LowerBin m_14 s_14 g_14 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x5050505050505050
def s_15 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_15 : Nat := 0x1010105010505050
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
def l_15 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 0 (dagTraceF m_15 s_15 4 f_15) l_15 0) s_15 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_15 g_15 bds_15 0 (dagTraceF m_15 s_15 4 f_15) l_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xa0a0a0a0a0a0a0a
def s_16 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_16 : Nat := 0x2020a020a020a
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
def l_16 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 0 (dagTraceF m_16 s_16 4 f_16) l_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_16 g_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) l_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xc0c0c0c0c0c0c0c0
def s_17 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_17 : Nat := 0x4000404040
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
def l_17 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 0 (dagTraceF m_17 s_17 4 f_17) l_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_17 g_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) l_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xc0c0c0c0c0c0c0c
def s_18 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_18 : Nat := 0x4040c000c040c
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
def l_18 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 0 (dagTraceF m_18 s_18 4 f_18) l_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_18 g_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) l_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xaa00aa00aa00aa
def s_19 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_19 : Nat := 0x2000a000a002a
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_19 : KnownBin bds_19 := by intro b hb; simp [bds_19] at hb
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp [bds_19] at hb
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_19] at hb
def f_19 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_19 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 64 (dagTraceF m_19 s_19 5 f_19) l_19 0) s_19 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 (dagCheckNodeF m_19 g_19 bds_19 64 (dagTraceF m_19 s_19 5 f_19) l_19) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 64 (dagCheckNodeF m_19 g_19 bds_19 64 (dagTraceF m_19 s_19 5 f_19) l_19) = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_19 g_19 bds_19 64 (dagTraceF m_19 s_19 5 f_19) l_19) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_19 g_19 bds_19 64 (dagTraceF m_19 s_19 5 f_19) l_19) i = true := nj_19_1
theorem lb_19 : LowerBin m_19 s_19 g_19 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xcc00cc00cc00cc
def s_20 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_20 : Nat := 0x4004c004c004c
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
def l_20 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 0 (dagTraceF m_20 s_20 4 f_20) l_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_20 g_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) l_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xf000f000f000f00
def s_21 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_21 : Nat := 0x100070003000700
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
def l_21 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 0 (dagTraceF m_21 s_21 4 f_21) l_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_21 g_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) l_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xf000f000f000f0
def s_22 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_22 : Nat := 0x10005000500070
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by intro b hb; simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_22] at hb
def f_22 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_22 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 64 (dagTraceF m_22 s_22 5 f_22) l_22 0) s_22 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 (dagCheckNodeF m_22 g_22 bds_22 64 (dagTraceF m_22 s_22 5 f_22) l_22) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 64 (dagCheckNodeF m_22 g_22 bds_22 64 (dagTraceF m_22 s_22 5 f_22) l_22) = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_22 g_22 bds_22 64 (dagTraceF m_22 s_22 5 f_22) l_22) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_22 g_22 bds_22 64 (dagTraceF m_22 s_22 5 f_22) l_22) i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xaaaa0000aaaa0000
def s_23 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_23 : Nat := 0x20000020a0000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
def l_23 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 0 (dagTraceF m_23 s_23 4 f_23) l_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_23 g_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) l_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xaaaa0000aaaa
def s_24 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_24 : Nat := 0x20a0000022a
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 4 f_24) l_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xcccc0000cccc0000
def s_25 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_25 : Nat := 0x40000004c0000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xcccc0000cccc
def s_26 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_26 : Nat := 0x44c0000444c
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
def l_26 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 0 (dagTraceF m_26 s_26 4 f_26) l_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_26 g_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) l_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xf0f00000f0f0000
def s_27 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_27 : Nat := 0x1070000030f0000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def l_27 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f00000f0f0
def s_28 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_28 : Nat := 0x105000005070
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def f_28 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_28 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 64 (dagTraceF m_28 s_28 5 f_28) l_28 0) s_28 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 (dagCheckNodeF m_28 g_28 bds_28 64 (dagTraceF m_28 s_28 5 f_28) l_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 64 (dagCheckNodeF m_28 g_28 bds_28 64 (dagTraceF m_28 s_28 5 f_28) l_28) = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_28 g_28 bds_28 64 (dagTraceF m_28 s_28 5 f_28) l_28) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_28 g_28 bds_28 64 (dagTraceF m_28 s_28 5 f_28) l_28) i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xff000000ff0000
def s_29 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_29 : Nat := 0x170000005f0000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
def l_29 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 0 (dagTraceF m_29 s_29 4 f_29) l_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_29 g_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) l_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff000000ff00
def s_30 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_30 : Nat := 0x170000005700
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xaaaaaaaa00000000
def s_31 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_31 : Nat := 0x2020a00000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
def l_31 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 0 (dagTraceF m_31 s_31 4 f_31) l_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_31 g_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) l_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0x5555555500000000
def s_32 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_32 : Nat := 0x1115155500000000
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

def m_33 : Nat := 0xaaaaaaaa
def s_33 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_33 : Nat := 0x20a022a
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
def l_33 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 4 f_33) l_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_33 g_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) l_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xcccccccc00000000
def s_34 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_34 : Nat := 0x4044c00000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6), (m_9, s_9, 4, g_9)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_5
  · exact lb_6
  · exact lb_9
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_34 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_34 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 43 (dagTraceF m_34 s_34 6 f_34) l_34 0) s_34 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 (dagCheckNodeF m_34 g_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 43 (dagCheckNodeF m_34 g_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) l_34) = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_34 g_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) l_34) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_34 g_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) l_34) i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xf0f0f0f00000000
def s_35 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_35 : Nat := 0x107070f00000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7), (m_10, s_10, 4, g_10)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_5
  · exact lb_7
  · exact lb_10
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

def m_36 : Nat := 0xf0f0f0f0
def s_36 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_36 : Nat := 0x10505070
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_36 : KnownBin bds_36 := by intro b hb; simp [bds_36] at hb
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp [bds_36] at hb
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_36] at hb
def f_36 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_36 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 64 (dagTraceF m_36 s_36 5 f_36) l_36 0) s_36 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeF m_36 g_36 bds_36 64 (dagTraceF m_36 s_36 5 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 64 (dagCheckNodeF m_36 g_36 bds_36 64 (dagTraceF m_36 s_36 5 f_36) l_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_36 g_36 bds_36 64 (dagTraceF m_36 s_36 5 f_36) l_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_36 g_36 bds_36 64 (dagTraceF m_36 s_36 5 f_36) l_36) i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xff00ff0000000000
def s_37 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_37 : Nat := 0x1100170000000000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
def l_37 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 0 (dagTraceF m_37 s_37 4 f_37) l_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_37 g_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) l_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xff00ff00000000
def s_38 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_38 : Nat := 0x17005f00000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
def l_38 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 0 (dagTraceF m_38 s_38 4 f_38) l_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_38 g_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) l_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xffff000000000000
def s_39 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_39 : Nat := 0x1117000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
def l_39 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 0 (dagTraceF m_39 s_39 4 f_39) l_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_39 g_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) l_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xffff00000000
def s_40 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_40 : Nat := 0x175f00000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
def l_40 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 0 (dagTraceF m_40 s_40 4 f_40) l_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_40 g_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) l_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xffff
def s_41 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_41 : Nat := 0x577f
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
def l_41 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 0 (dagTraceF m_41 s_41 4 f_41) l_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_41 g_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) l_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xaaaaaaaaaaaaaaaa
def s_42 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_42 : Nat := 0x2020a020a022a
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 6, g_14), (m_19, s_19, 6, g_19), (m_16, s_16, 5, g_16), (m_23, s_23, 5, g_23), (m_24, s_24, 5, g_24), (m_31, s_31, 5, g_31), (m_33, s_33, 5, g_33), (m_1, s_1, 4, g_1), (m_4, s_4, 4, g_4), (m_8, s_8, 4, g_8)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_19
  · exact lb_16
  · exact lb_23
  · exact lb_24
  · exact lb_31
  · exact lb_33
  · exact lb_1
  · exact lb_4
  · exact lb_8
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_42 : Nat → Nat × Nat := unpackForestF 0xad24900b4fa6a3ba6a39aa25caa124aa024a6a33a935ca693fa6937a7b5ca683fa683700b43a5b4a89c51a4d6089a4f89a4ea1b5ca1a6ca1a4ca1a3c89a4b9ec609e95c9e9509e85c9e85089a479da4c9a3549a26c9a24c9a1289a1249a0289a02489a4397a6c97a4c97828978248992f968289523c95018950148992b899279392c922349216c9214c899238fa6c8fa4c8f9288f9248982f8e9288d13c8d02c8d0248982b898278b82c8a1348a06c8a04c8982300a4388a4687c5287a5e00a3b86a457245e724538534a7245282c5182c5082b4d82b457235281460813607225f803517225e7da5c7da4c7d9247d8247225375a5d75a4e75a4d75a3d7592a7995c7993c7592678128781247582a7615c7613c76018758267225274a5c7212f721277325c7202f7202700a33712396d3497024e6d2496db586da6c6da586da546d2330094f6c13e009436b2530093f6a1346635368a5168a496615e66b5266a5e66a526613e0093b652395c45263a3b63a335c450625606225c5c253603526025e602525c2415ea4f5ea435c2405d9435c04c5ca435c040009375b13454b535a24954a5e592495495e5725e572525715e5493e562435481855243548140093353348532444dc5351b5151b494da5e5035e503524da4e4d9524e25e4e15e4d9420092f4c25e4c15e009234b239473494a24e4724947b5847a6c47a5847a54472330084f45a6c4582444233449314403e00843432530083f420343e35340a5140a493e05e3eb523ea5e3ea523e03e0083b3d239344523ba3b3ba33344503a5603a25c34253383523825e382523424136a4f36a4334240359433414c34a433414000837330342cb53322492c95e312492c85e2f25e2f2522f05e2c83e2e2432c82c2d2432c824008332b3482b24425c5329b5129b4925a5e2835e2835225a4e258522625e2605e258420082f2424c24024222532215e229512205e00823211341e353202491e15e1ea5e1ea521e13e0081f1d0341a3531c2491a05e1aa5e1aa521a03e0081b1924803c531823803b531723803b4314c5114b511494e1493e03a5211452113411115e1213c111521113e03a420d3520d3420d15e0d1520d14e0d95c0d14203a320ba320b93e039520a2520a15e03932072320895c07132078300703e03852042520593c04152048500405e0383200817013530212801a4301124008130001f 9 11
def l_42 : Nat → Nat → Option Nat := unpackLinksF 0x8501090a0f1c16482c10506090c08581010186030406080830101f37be607b8af701ea23d0279c2f381e703ce078c8f181e303c6078c0f181db43b607682ed01da03b407680ed01da03a487480e901d10ba20730ae601ca139407280e38dc60b8c07142e281c5038437080e101c10b8206f0ade01ba137406e80db8db60b6c06d42da81b50364365b8cb01950b2a064c4c981920b1e363c0c60d8c031806300c601872b0e061c0c20d84030046000c0017f0afc15e4abb897702ee05d44b9897302e605c06b8017002dc25b80b7016e02d6358d0b181620ac405880b0856102a4f5480a80950029845300a6014c029805208a19541127a44f409e053c027044e009c01351a6a04d409a81321a5e34bc0960d2c025804a8495012a02486490092012402423484090811f123e047828f011d0a2c74580891112022024400868d0d021a04340850d0a0212142408405013a02040407e90fd01fa03e487c80f901ee23dc07b80f701ea23c0a7800ee11d443a807408e801c8439007200e401c8038086d94da09b4035886a84d3119e433c06704ce0194432806500c7198e031c06380c41982330405f0cbe017c02f045e00bc016c62d805b00b6016632cc05980b1116202c025800af095072a005210a40144228804f8c9f013e027c04e0c9c0136126c04d04933926024c047908f011e022c845808b011222240448089010e2208a40848100fa41f403e047a10ec41d803a087400e421c8039007010da31b4035886b00d221a4034806710c83190030105f08b4516802b105600ac015802b004e409c0138027004e009a11340239847008e011c0238047008e011821f203e007a10e861d0039086c30d801b0034106800cc2180c30006000b8417002d0854307d60f041e003a107020d0801c8001 0xad24986231a5b60853507b3407eb427b23d5393d2b83d79a3876a387b3488026cab25caa924aa024a935ca7b5ca52518824985a4384a41ac23baba39a9a3375231a893fa81375292fa703fa68372a82f188178435283b50a5b4aa4a5da0a55a4d6083350a32587ba50a1b4e7bb4d9da44a335ca2a6ca224ca1a3ca0c6082b407c25c9d240a015c9f9509f05c9e8509da4c7bb5c9d3549ca6c9c24c9b9289b1249a8289a024969289926c98a4c96138980289782493924968289623c9581895014931209392c932349296c9214c8e8289126c90a4c901288f9248e0388e9288b8248e13c8d82c8d0248b0208b82c8b1348a86c8a04ca545182342a424fa3a4ea124b9e24799a43752426b14f6994b619475a9439712f9492b94127919234304f4184b39847328438f02f8c82b8c027898232081f1c81b178170281388a468845287a5e86a45843607eb488026c83b508534a81a5d8445183c508334d82b458125d81c60813607ca607cc5d803516e95d4885d7a25c7725c7cb6c7f25c7ea4c7e1247d8247a12477024799247682478828760247a15c7993c7801878928781247715c7693c760187ca5d7c24e7ba4d7b23d7a92a791267782a7582674a5c7325c8645e85c5384c528235280a5f7fa5e7d253752526d15f7412f739274705f7282f7202716817712396e2316f3427024e6e2425a1426f3586ea6c6e2586da5470b496fa496d233599324c922248310b8154f23e6c13e238330b0256b2536916c6794c6693c6a1346925168a4966a4167b526725e66a5269b536815e6613e62a5165239602316423b63a3362d60613506225c602505d85c5c8506135260a5e602525f24f5ea435d9435ca4364c526345061a535fa415e2405d04c5c0405793c5b13456018550145a2495712e5924957a414e12e5825e57a525715e56243552435ab5359a5e4da3e5895e5693e558185481453b485226c5024c532445235151b49503414e93250b5e503524ea5e4e15e52c535125e4fa4e4f1524d942460510a0154ca5e4c15e45053098254b23948231493424a24e48242320424935848a6c4825847a544ab4949a49472333183223022089244626c081344484c45824078244493107016452332713e069264403e432534106c3f84c3e83c420344125140a493ea413fb523f25e3ea5241b534005e3e03e3aa513d239382313c23b3ba333ad60393503a25c382503595c349503935238a5e382523724f36a433594334a433cc523b45039a5337a41362403514c341402f83c330342e02c2d024322492f02e312492fa412602e3025e2fa522f05e2e2432d24332b533195e2593e3085e2e83e2d82c2c8242bb482a26c2824c2b2442a35129b49283412683228b5e2835226a5e2605e2ac532925e27a4e27052258420592424a4c051342286c2402404824229510401623a532315e039262205e1e93c21134202491ea411f25e1ea5220b531f95e1e13e1a83c1d0341c2491aa411b25e1aa521cb531b85e1a03e1626013a501924811a400202015a6010240182380ea3001810132500fa40172380d2301645115b510aa321514e119421493e0e932060321213c13c52133411295e119521113e0d1320d95c103520fb420c2520f15e0e9520e14e0d14209052058300c2320b93e05032088500aa520a15e080520895c0783c0783009232081320703e0593c0485c0485006252051520405e18c5317b5316b431425210a420ca320b15209932068520383201010019240212801a4302b5301124acb4fa6343892438723b71a336c94f6b9436a93f6593b5b937541334d12f4b9234684f438434283f3d83b338372c0332502f218231d81f1981b03017008130001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 347 (dagTraceF m_42 s_42 8 f_42) l_42 0) s_42 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 64 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_2 : treeBlockF 64 96 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_3 : treeBlockF 96 128 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_4 : treeBlockF 128 160 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_5 : treeBlockF 160 192 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_6 : treeBlockF 192 224 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_7 : treeBlockF 224 256 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_8 : treeBlockF 256 288 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_9 : treeBlockF 288 320 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_10 : treeBlockF 320 347 (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nj_42_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_1 (fun _ h1 h2 => treeBlockF_at nb_42_2 h1 h2)
theorem nj_42_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_2 (fun _ h1 h2 => treeBlockF_at nb_42_3 h1 h2)
theorem nj_42_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_3 (fun _ h1 h2 => treeBlockF_at nb_42_4 h1 h2)
theorem nj_42_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_4 (fun _ h1 h2 => treeBlockF_at nb_42_5 h1 h2)
theorem nj_42_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_5 (fun _ h1 h2 => treeBlockF_at nb_42_6 h1 h2)
theorem nj_42_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_6 (fun _ h1 h2 => treeBlockF_at nb_42_7 h1 h2)
theorem nj_42_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_7 (fun _ h1 h2 => treeBlockF_at nb_42_8 h1 h2)
theorem nj_42_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_8 (fun _ h1 h2 => treeBlockF_at nb_42_9 h1 h2)
theorem nj_42_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := block_join nj_42_9 (fun _ h1 h2 => treeBlockF_at nb_42_10 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_42 g_42 bds_42 347 (dagTraceF m_42 s_42 8 f_42) l_42) i = true := nj_42_10
theorem lb_42 : LowerBin m_42 s_42 g_42 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0x5555555555555555
def s_43 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_43 : Nat := 0x1115155511555555
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 5, g_13)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
def l_43 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 0 (dagTraceF m_43 s_43 5 f_43) l_43 0) s_43 5 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_43 g_43 bds_43 0 (dagTraceF m_43 s_43 5 f_43) l_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xcccccccccccccccc
def s_44 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_44 : Nat := 0x4044c004c444c
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 7, g_34), (m_13, s_13, 5, g_13), (m_17, s_17, 5, g_17), (m_18, s_18, 5, g_18), (m_20, s_20, 5, g_20), (m_25, s_25, 5, g_25), (m_26, s_26, 5, g_26), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_34
  · exact lb_13
  · exact lb_17
  · exact lb_18
  · exact lb_20
  · exact lb_25
  · exact lb_26
  · exact lb_0
  · exact lb_2
  · exact lb_3
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_44 : Nat → Nat × Nat := unpackForestF 0x5a7e6239016977e972fd28e192fc32578c0f30c93e2014c32477e942fcae5f950bf0b802d1eb11cd692fad257720f2e41856927b60316c052b491d682fad057624f2c49856827af2415c4d2b411d6034016860293ea51f00a4ba36b946d428cae51950a30b80291e7925cf2479e25f3c49c0521ce0340147f341125a294b353974a32c978051dca4520146e028ce3529c83528d4931c952351d8094f8b0280252e252880947012870c8e4049fc215e01277048e5e6293fd607f4b8f294de9a93d25e7b048f4949e5208093777028024cdba2fb745b726c0e41b1ba2bb7b486f088dd14c0497b145f6b288c516d9db03396c670d8c515d90a232044628a6c457804959745f5f6905d16d6db02da605b0d85d15d59a42b24857460ac110ba29973584e8ba9d165442e274554f0889d144b9a922a4f4549692d41242e22a47464988c0911521973502e6905cd00bda797b4b3d4b87a940f4a817b473a470748d0bda19bb48376885e93cbd2597a472f4865e8fcbd1d97a372f4665c0f004938145f2b2880516c9db01396c270d80515c8ca21203c230880514c092f0f35d1f4a03cd5408af01b4f0369630940602e0c0500368e2a0e0541a01b430329c0613c0c2587b5c0f6a00611c30260604403086060fc0c1d83c58078a0060dc15a002144030660405004918001f 8 11
def l_44 : Nat → Nat → Option Nat := unpackLinksF 0x23c48f023258c822a48a822a08a82262898222286921a086821247fa9fa27e81fa07e81fa07d89f607d81f227c81f207c81f017a8dea07a05e617335be76f05bc06e85ba06e81ba06e81ba06c15ae16b81ac16b019e767819c167019a1660598065858e463818c163018a1628188162018615f917e05f057c05e857a05e817815e017615d817035c017005a116805a016805985603568d5a056055805601580560154255015405409484520148051854605181460500d40050013c24f013254b892e04a0d26148891e245151214405100428d005400100040010003f08fc03e08f043c00f003c00f003b08ec03b00e823810e003800e003800e003800e00368cda03680d623580d603488d203480d203480d203480d202eb0a6a2888a2027889a2260496123148a12280862200c7e11f807e01f047821e007801e007801e007231c807201b886e01b806e01b806e01a886a01a8066219806601980641178c5e017045a1103432700e0001 0x1d497b612b6024e5848f311cba12f6a256bc49ca891b993d69272b84d4a498a5350c60783e573100a6412fc72578a49f0c91b901f67036b605c9c09e525cc94a38494304ae601507125ecc4ad689393123bf0b8e04f5609add03cb90616e062d80a57820b2279624c2b81057920ae269344e6f097dd92bb824f6a48ed017d982bb004f5a08dbc0fb201b5602e4604e6524dea396e25ec64ad549391123ac0695317aa51f53b5ca66a14a57290a85185c974d92093261a5d0a4ba048f2257df8a3cf92f9e24f380d268224bb6c974a33314a61a9cb25e8d2bf2914a41ac483528e4a92294e3d24c6a3b21245160522528c3239842bd00946091cbd23180ac0fad41fd2e3d2507b048fad49f12f3d252818a4fc94de520bb814736c0e41b1c1a437844758bee916dc62bb74536b288d2d81a0b63386c65288c8111b22fb545b668aec714d88af29b6041078a4d817da42003c3e05894d40f41e1f25051480bad8141a82e2605b0d8780f0ec1623b504f4a0768e15d182736059690b092158221c83c4a6a0a21711da427844538baa5165422aa74514a6a0921711d26230244c49e9692d2123a2a433f4b87c940f4a81da383a46870d20dda220b4f4069678d1ce5a19b24f354966891ccd219923f31476608dcbd19b045f5e8b6b515d5629aa3584d6a488d410da4213402e078405b0700a159441b0283e570680a0c85c190b852d80a0b60f15c270d82e050541a1203c150684a5108c220a014130283e94081ae8f3551a4a03217060280b0381506820d703da80684c0c0880a100222c03c50040600ad0010a20e34f1b6962ed1c51a18994e1209e2212c3823858430a07e120ec181b818332c8be5516c9a2b91453214bc3a578080a66b4fcb6977cd1eada1d524fa84974491e7521cda3f95477268de4919c614f8a2971051e1ca1c293f83276f04ddd899b692f612565a49c04918001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 206 (dagTraceF m_44 s_44 8 f_44) l_44 0) s_44 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 64 (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_2 : treeBlockF 64 96 (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_3 : treeBlockF 96 128 (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_4 : treeBlockF 128 160 (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_5 : treeBlockF 160 192 (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_6 : treeBlockF 192 206 (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nj_44_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_1 (fun _ h1 h2 => treeBlockF_at nb_44_2 h1 h2)
theorem nj_44_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_2 (fun _ h1 h2 => treeBlockF_at nb_44_3 h1 h2)
theorem nj_44_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_3 (fun _ h1 h2 => treeBlockF_at nb_44_4 h1 h2)
theorem nj_44_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_4 (fun _ h1 h2 => treeBlockF_at nb_44_5 h1 h2)
theorem nj_44_6 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_5 (fun _ h1 h2 => treeBlockF_at nb_44_6 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_44 g_44 bds_44 206 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := nj_44_6
theorem lb_44 : LowerBin m_44 s_44 g_44 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0x3333333333333333
def s_45 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_45 : Nat := 0x1113131313131333
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 6, g_14)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
def l_45 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 0 (dagTraceF m_45 s_45 6 f_45) l_45 0) s_45 6 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_45 g_45 bds_45 0 (dagTraceF m_45 s_45 6 f_45) l_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xf0f0f0f0f0f0f0f0
def s_46 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_46 : Nat := 0x1010105010505070
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 6, g_22), (m_28, s_28, 6, g_28), (m_36, s_36, 6, g_36), (m_15, s_15, 5, g_15), (m_17, s_17, 5, g_17), (m_0, s_0, 4, g_0)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_22
  · exact lb_28
  · exact lb_36
  · exact lb_15
  · exact lb_17
  · exact lb_0
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_46 : Nat → Nat × Nat := unpackForestF 0x169fe7929f3c14f908e7cc27de6019f209cf920fbc905de4039005a5f8a4a7c5053d4a51ef895f84513be247df02befc2277c08fa94a1dd93eeec0cf52547b425fdc144ed091f6806fb5089da013ea4a87620fbb105dd4851ea817f5c113aa047d501feac2275404fa90a000b47e9894f4c0a790473d092be8491f420afa1047c8238e789f73c06790273cc92fe6491f3206f99027c8138e581f72c0bb90073c882fe4411f2207f91027c8038005a1f1c0678b253c602ee2c1480292f894d9ba24bdd123f0a50785083ba246dd095f0251b81033ba129df4b66fa5537d031ba123dd015ef211b7905dba029dd4366ea15375059ba02300521ea517b7148ba9452dbe366a497f6c293b6049d492f6d4953524a7b2a5dd9522eca4a765053a9252d4895ebf17b5f8a5af95ed7c0cea44a75c2a9ae018d4891ea40af568bdab452d582f6ac0bb52053a9854d4c166a408c01477a8019d3494e9c0bb4d05200a33d2c14e904fb4907da4019004a5e50d4f43471a1938d0c9a650d2f412d99414bca0a3e7a9073d08394146ca09fe6cd4b366959b24acd92366c0a72827d9896ccc4aa6624f33103194133ca00de5a11b2d07d94019ca4366521532909994013004a1dfb17b2528b7ec52c851c6424e3212697eb53bf5a5e3d1b2fd2bf8da49c6c24dfa57b192a97e953c50aee285171427d8a019bf4a95fa4ff0b8bd85c52c2da9616d2b0b4bd85a52c2c14dfa4fb072a98393cc1c0c5fa4cefd03780c5ec062960217b0107d7e819bf82a5fc132fd0260093bbec14df04faf907d7c01900499cb117ef169178a48bcc0c5e2522f12892c45bbadb05d6982eb2d975960bac304b115ee569172a48b94a45ca512e50912c453b85a35c28eae10732c352b662f5bc512d98a56cb5eb65a95b28ead90732c34ab49a95ac8d2d269569246b491eda40a6584a563c5eb3ca258f14acd46963b52b1da558e97ac74a563a3db1c14cb092ac46c162260960afd84142c068b60049960af5769b2bb2995d93caec964b056eb58d95ac60ad5a856a942b50c12c157accae55a992ad2b956954ab4a655a4f2ad0312c153a60af5305769829b4c146a60a2d30512a52894c13da8ca25304b6a029950144a600d530066980314c84ca64225320f2990594c016960a9528d62944b14a048960a7d1c9728e2994713ca3ca651c062582973ec5e9f6294fa57a890313e9529f4a34fa4f67d25b3e81a9f40cd02d3a816853e8189f81e4fc0b27d02d2c14a9e9a44f49225828f3545e9dc1c4d514a756993535a9c1a84e0942702a1380509a9ab4d84f26c259360189a9a74d41065828d3414c9912a4c8532642793212c960a1cb006e5c6a52e34a971294b892a5c0bd2e0469600ccb2132590792c01300491caa4a2550492623394898ca44a64c07d26a329349f49c5124d2652602e00425c3ed4e472712383891c1a43ed2e1f4a721128908144840921f4971f8288fc1243e8ce3d0d90f84b87c23c72906392830f84687c1fc64d4a326951924a8c9234644a61f07d1686c8b42a45a0f22d0590f83387c17c4a94a254951294a894a344a4fa252650f82e88036440152200991002c87c1180210de68bd0e04579a294304e2180710c034799a9bccd2e132510982884c123cc94de6497072548381441c091e64670646c7982fc1292609292f305e81c2a3cc14e020bb010458081f4040b9e60a4f303f7e62f3f3149f96a4fcb4a7e52f3f2949f9252f303e7d42a3ea0f1f5058f303379817bd7179eb8a4f5a527ad253d6579eb2a4f593e7ac993cc0b9e70a8f384c79c163cc08c01076f1254788943c4091da466ef93177c94bb40f9db464ed93e76c993b40b8010668645f74da43a6521d5058e984874c2221916dcd6c0e6a60734b039a1b1cd0c08645771da438e921c7290e384871c2221914dc368ce1a3970c9d218d49bb8bce00446ee29376d79bb6a4dda396ec9d218d29b5498da9286dc2236a0a1b50488625b6c8143640910c4a6d78286bc1221892daa498d51286a8143540910c486d403467da934c0d19f694cfa5e68d2233e9499f494cfa4667c952188c5966a4ce134659a533449196462cb1466589eb2c4b90c2a4c445e64c2231114991268c4352621a531a9118d248c4231620af3105498827ac412e430a530ad81852c08605f60ca8300d1580292c01214302f2f65b17b098bd82c5ec0e21816d758d8bac605d5a82ea981752a0860575cc2e2da5916d0b8b68545b4262da0f16d0588605355918aac179560baab04d558232ac11565242ab04458c222ac0f55605caf84c57c222ac0b556058ad04c568222b40f15604aab84455c122ac0750c0a4a9358549242a45610c09ea615c5302629c1314c078a602c43025a751793a8a49d2314e82f28c0b13a0a49d0464e81ea740b93a05a9fb4e4fda12740b13d0789d0254ec122740750c0949bb484dca421811d238bc9a13848e29264d31236b496b504b52825a5412d0a091b564a41e2520b12903891b4e48ca0a464e5232629223848c90a18119210988e9544742623a0b11d0388604346da02180bd106a48834a4412d220909102bc88152440a5220519100a48804a4301721a1310d058860230041180517d054908294841c1e20a121050880145b3fdb01fe980ff2c07f86c3fc3000515cf96907ca483e4a41f2120f9088014533cd1c1e64e0f5088798383cc1a004d6cf007078034009a99da0e0ed0680134b3a11c1d04e0e807074034009a19c8918e447c7212a009291b9178e10886e4523712f1b8948dc47c6e12a009251b40d0d16a46c034345a51a2978d548868a52345251a2918d1254012323212919c490c84946612432119190518c827c6412d008a9175178c50885d45230c92174948ba4945fa442fc921748c8ba2bc5d1522e89f1744b4022945c03427da916c0d09f6945a12427d291644909f4945624e2bd1a158908ac4745623627d181544809f2bc5323029c9014c5109f2a45223027ca51424e0a12404f94627c968044c89c4c04e1600082f9349409568a4aa492549112c480950440105e240b61200f0900584801c0082d9151b08a8c04536022928114540020ae4405c208b2104170820a84104c2081e1040b0020a633a321fd180ce4c8670bc3385d19c268ce1186708a3b1221dc900ec088670883383e1c8260e41106707a3383c1b8260dc1106706a358441ac1a0ce0b4680883403419c0e8041486369031a5818cac00413c5d2b83004c174260ba0f05d0580104b1262f093148494642c230124990921785507824852124230920f84907a27b4e13da10920f04906a26034124168940d04903a0104a1192408c5200208e17c5e10d1c05f1484169817b5a0f1a80789403c2a01e0500bdab0700f0380581c01c0bda705e9042f47217a310cd1c05e48830470181200bc110041182d098149540a41e0520b029038010430992004c5000207e0db5a06da10369781b4a40da4a06d230365481b2940d85206c250040f8180780c02c00819806d480369401a5200d25006548032940185e030220180f00c0580601c00c290100f0080580401c00c250061180307a0182d00c0e8040c8010260001f 10 11
def l_46 : Nat → Nat → Option Nat := unpackLinksF 0xe609e600e600e546e540e540e486e480e480e3c6e306e300e300e246e240e240e221e220e220e201e165e160e160e0a6e0a0e0a0e081e080e080e061dfc5dfc0dfc0df06df00df00dee1dee0dee0dec1de25dd09dd00dd00dc46dc40dc40dc40dc40dba5dba0dba0dae6dae0dae0dae0dae0da45da40da40d986d980d980d980d980d8e5d76cd760d703d700d6a3d643d640d602d5e1d5e0d5e0d507d4c2d4c0d4c0d3c8d3c0d3a1d3a0d305d2c2d2c0d2c0d1c8d1c0d1a1d1a0d105ceb3cdc7cdc0cce7cce0cca2cca0cca0cbc7cbc0cb82cb80cb80cb80cb80ca88ca42ca40ca40ca40ca40c90ac8e1c8e0c864c822c820c820c820c820c6eac6c1c6c0c644c3b5c3a0c343c340c2e3c283c280c223c220c1c3c163c103c100c100c0e1c007c000bfc2bfa1bfa0bfa0bec7be82be80be80be80be80be80bd88bd80bd61bd60bd60bcc5bc82bc80bc80bb88bb80bb61bb60bac5b873b787b780b6a7b6a0b6a0b681b5a7b543b540b502b500b500b427b420b3e2b3e0b3e0b3e0b3e0b2e8b2a2b2a0b2a0b2a0b2a0b2a0b2a0b2a0b16ab141b140b140b0c4b082b080b080b080b080af4aaf21af20aea4ac15ac00aba3aba0ab43aae3aa07aa00aa00aa00a9e1a9e0a945a921a901a900a8e1a8c1a806a800a800a800a7c2a7c0a6c8a6c0a6c0a6c0a54ca540a540a521a520a520a520a520a36ea360a360a341a340a340a340a1cca1c0a1c0a1a1a1a0a181a180a180a180a180a1809fce9fc09fc09f449f409f219f209e289e019e009e009dc29d449d409d409d409d409d409c679c609c419c409c409c409c409c409b679b609b609b039b009a849a429a409a029a0099c299c099c0998299809980998099809980998098e596f096e096e096e09645960295e195c195c0958294e594c194829480948094429440940293c293a193a093a093a09362936093609303912f9120912090a490a090a090629060904190409040904090408fc48fc08fc08fc08f638f608dec8de08dc18dc08dc08da18d248cc38cc08cc08cc08cc08ca18c818b2b8b208b208ac3871e86e186e086458640864085e385e085e085e085a2854384e38483848084808461838783238320832083018227822081e280c980c080828061806080607f877f427f407f407f407f407f407e487e407e217e207e207d857d427d407d407d407d407d407d407c487c407c217c207c207b857933784778407767776077607741766776037600760075e1750774a374627460742272ea72e072a272a072a071c771c0718271807180718071807088704270407040704070407040704070406f0a6ee16ee06ee06e646e226e206e206e206e206e206e206e206e206cea6cc16cc06cc06c4469b569a06981698068c668c068c0686368606860684167e3678366a766a066a066a06681668065e565c165a165816580656164a664a064a064a064a06462636863606360636061ec61e061e061c161c061c061c061c0600e6000600060005fc25fc05f255f205ee25dc95dc05d825c4a5c405c405c215c205b665b605b225b205ac35aa15a815a425a2159e259e0580f5800580057e157e057a257a057a057a0562c562056205601560055e155e055e055e05583558055805580558053ce53c053c053445340532153205301520851e151e051e051a2512451205120512051205120504750405021502050205020502050204f474f024f004f004ea34ea04e244e014dc24dc04d824d804d804d804d424d404d404d404d404ca54ca04ca04c624a704a604a604a6049c54982496149604922490148654841480247e147e047e047a247a0476247604741474047404702470046a346a04662448f4480448044044400440043c243c043a143a043a043a043a0432443204320432042c342c0428242804280424240cc40c040a140a040a04081400440003fa33fa03fa03f813f613f413f403f403f213f203f203dcb3dc03dc03d6339be38c738c038c038c038a138a0380537e137c137a137a0378136c636c036c036c036c0368235883580358035803542354034a534a0346233493340330231ca31c031c031a131a030e630e030e030e02f6c2f602f602f412f402f402f402f402d8e2d802d422d402ce32cc12ca12c622c412c022c002a2f2a202a202a012a0029c229c029c029c0284c2840284028212820280128002800280027a327a027a027a027a025ee25e025a225a0254325402502250024a324a024a0248124802480230c230022e122c122c022a12262226022412240224022022200202f202020201fa41fa01f811f801f611f601f411e481e211e201e201de21d641d601d601d601d601d601c871c801c611c601c601c601c601c601b871b421b211ae21ae01ae01a831a801a0419e119e019c11982198019801980194219401940194018a518a018a018621860186018221630162016201620158515421540150214e114c11425140113c213a113a013811380138013421340134013211320132012e212831280124212401202102f102010200fa40fa00fa00f620f600f410f400f400f400f400ec40ec00ec00ec00e630e600e220e200e200de20de00de00da20c2c0c200c010c000c000be10b640b600b600b030ae10ac10aa10aa00aa00a810a800a800a800a80092b0920092008c308c008c008c008c008c008c008c008c008c008c008c0084408400840084007e307e007e007e007e0064d029e00330001 0x1b2241dc91ce26507262737b12380420c3a0e5d804685013bd498fa04a6f2242eb831f3c14ba8086f4465e693ebc899212087cc032830117589921048bca07cea032f241720c08bce473e5939bc091f900e5d204682013bbc98f8c4a6ec242e8831f1414b9a087c2289df844f0c95f8248fc0057df02340c09ddc8cbbc27d7613240810f76064ff023dc144ed4227724bfb7246e8023ed80df6804dcf26480922ec81f39a0cbb105c7f822eb822756112eb247d782feb411f5807faa027e2251ef528774547b32a175123ec028f52141cc0467f013ba498f4e4a6e7242e5831e9814b90087a4257d1923e8815f4208cfd02774232e7c9f5ce4c8fc043cf0193e808f384bf9b246e5023e680df3204dc92647d922e5c1f3900cb9605c7d022b9491f280bf93047c901fe4409ee0927a5473d0238c90a4f3a4e7982717212386c24f2a0e790070e30233e0099ee0878e0327a0113d8917180b8f4045c6929e2c149e404f676a9c4a6cd9d246ced3b22293c3141b8c90c3212785082e2821b89205448c3324a591a4ac88a570451aa225ae2031e040c9e2046a325151238dfcb66fc5533a299be81870ca02ac4c2e146316952868a543212b7a08dbc82e3c4112ac07558050ab138ddc366ec15236099ba82ce2125ec892b8748fc2246d18a9e4052ee0263c192be0094ef848e972432505385c25b840c77b057bc029dd011aaa084ef027b7a5db7c98ec44a68c242e0831d6414a940877148b6e931d8494d16485bf063ac02952410edf1b3684c1b445ddb4a4e88506dc243b604992020b7c087686d9b5254da12eece916db263b3129a2090b7a0c765052a2821b692050a8c3628bdb0c52d152961092b602bda2152a1496b780c75f032770119b49450a8e35d2a98714cd700c3765013a261acc5ed62295b28c6492a4fa94ad5c2f49014b5605c770224e80ea520a13a271aa0547f0266a60b3728bdb8452db92fed697b694a7b2252d08a9e3e52ed8263b192bd7894eb648e7c2432305385825b740c75a057aa829d4811a72084ec02675821d400c9d2044ea245a702e3a41169e4a74d052738136e418e960a5b6042dc132d241f36c0cb4a27cda033d200cdae903324719d14cb58985aa903454719c94cce09e6884e34326944130c592a6825b3162918b34ece124e7c906d42450a049cf4209cc046d348152140ce9a9672d2b384959ba46a911ee6c0a5b304272811a949e548933342d999954cc89e662060e426033920b491944054a152950a04acb82365a0f9b30643381d1a40c0ce4a32b0d995054ca4264540f3466a7a134bb451968052f132959f947cf0a36764ff3527d98133a5c9948a14e12096d883338c10e5e06f2c0339401319808da08cb1e2bb8893ea30991c4087040322d811b391964a5171027d4593238010e060645a02366930b31206468e30f2998613cc889c6424d28826165a40c211c61c5331e8d98b960c5e2ee389270c48365122c6c24c86104df0238ba6cc64aa5928cb172bb8b145c549f5104c8de0438a01915008d909028628188c5ec422961ed4b0e69586a5ec312950c8f70b052d802137408cdc4f28649984954c209e60e060dc26024920c122f60714ac74652215279ca560417a430a58083e6c0190920743803024928bfc2a5fc131ef0799345ec9229640d4f1f69763232c74afe3457b182a789952c489fe144fb062673e13290429c2212dae0666d821c140de00066fd026240116b418df60a5ab042d6132be41f3560cafa27cd4833be00cdb6d42df69164a50b41244f0572882a146148bcc0c5ead22f44913a154bc8a45e251272289389449cca24e0512ef6c177260bb4b65d85826f28975860b792459e522dd6b174b48b392c5d09228b2b173948b98a25ca122db69571b46b5d2959892ae24756295dadcaadc20e56b0626c8219840c82c046de2896fc5eb76295b8d7adb6a56aa52b2d255b48ea9629b3d945b641ca900c4d70433001905408dac8d2d76a56ab4ab25255a891ad347b6215dad8aab4e0c6d20524002197c0c828046cf28966a34b422f59d14acc6a565b4ab292f59294ac847b4a94d9e8a2b4a0c6c70522c8219780c826046c56c162260af8b4554582c20a15dc5eaaa2ecf0d36c168b6004990020b48084d6023599549cca2018062be4d95e94caf09e5764b2b98d95c460adda856c942ab2d959150ad430566572aa4d959264ac4ae560552af2995713cab40c4e6512a10314e014a949e5464b2a00314d81468c109aa046a52894d014a8ca2532052a129950144a70265361129a0794c82c0300e55657aaa2bb5494da20a555051aa728b53144a909ed444b5a20626a021a7c0d53c0669d0314c01602c08d2cd62954b149158a1ca252812268289478189b8a24da5128f29936144a492e4d6952912994813ca380c50406275289408189cca25120626e2893f8149b4a24fc0526c2894134ea05a14fe0f27e0580401ca322f51714a8a2bd44152a1ca34d65168627b4292d684189a60868403541819a000c4fa058070233db489e9244d65226728139b449dc1c4ead32736a1392509c4a84e01426e2793692c9b00c4f117a768a53a35a9bdab4d6d3a6469b078499a820c200e5e4062d002134808cd05300803133a54998a64ca4f264258cf940344980064800c09004040985a94c0d2a5f4a52f24a958ad3c650a5d0bd2005283c254b81180303a01928968264b20f2f68bf7845bbaa2bdc914ee06a56c34ab452958c92ac32bf5f95eae8add6855eac2a74b952a4ca7d1a52e7c2953c9479a4a34c650e540b71f05383425bc210d9e062680219880dcb606658026010110300a4ac4a2530992803c934164aa092532632912993490c9c5100c0312823293c9f49a4ca544672883e9301733a5022d2711b04c67018336502492711a84c8d01e4900e247068a283033c984404a22a07867020334984884a2290791402c90c1448409054040cd03033010332500cb260091205ac201000c225059200288fc12016082042a91e86c81024408d3a344931d2418a0a4c72505980446501265ca02c4102366a51ab4a8d1254669196247b191298949099204963078b114c8c03645e1522e0791682c320980d40c22a4a514a4a8a0a544e51a2627d129321a896b2c0c86c0583513c88c36444152210991002c929a9c8cd2e454a720a4b8f919b2a4c8c72451e04b8042547611e3808d1b83f8c41f4580cd550651582f8901743e08c66044ca13231891418175ff07ca50327c8170b6089922646212287022bfc0f949064f882e168113220c1902810d1387f4263f40f2190710c0345141831e501f5270fe04c30c101844c215250f803c7b4164280a2130482a020304983ce4a1ef078c71303009031a0c0bf04108254630a017c4c011240a4040164183d60b20f0510702401c104191b2050c102c5d82924bf490609292f694162c1117a04a052d9038546289917848a050bb0204580c1f28a0ca0205c2a022624a0286101ff8bcff4527f5a93f8d29fb4bcfd25250d1ebf24a5eb2425d8124ac1e286531f70a8fb03c7d4161744c04b060f945e7c6293e0949ef494f715e7b4a93d84f9eb2642592d620190720b04b278f48547a0263ce0b21d8bd0dc5285da9c2cd2e124a708a4b83519b0e4c8b92450585f8202f40c14e010a50003f7e01f3e80cd39064f982f7a8173cc08c48044040147912a3c64a1e0098ee83c76c163c4091e0262ef92976c90810061dd464ee13e76c993c28cdde07ced02e6f5a8382d218a2a0ca1484d42e28a1414a090ea82c75da43ac521310a8ea04874c2225e1112e088968444c0223a2d81d04c0e79607383639a1812c088e024864c2437ed61cb690e5248648ac392521490b0e404871c2237ad29c568ce223968918b3a54990294e193a2dc9130c175770aa8c82e05811380111c18bcdfc526f9af37ad49bc472d0a3166ca931e529bb2745a92255026a701151805c0a8226dc2201a0b1b9498dc12845c1e36c0a1b5048d42302d01034ed01a2480599301f8900280c114058d98286c812016081a646059020695a0342900b12602b9204982a0260c113058d80286bc1200e08009058d6a4c6b09424a15116078d58286a8120fe4c1a80682c1304902234c0d0b02405792068d2215c4c0ad260c71382b09034ed49a5694d225e68929342929a048ccc952630a51564c19f254c005e5ac292901292308c8d83d6709a0fe4c19a248ceb5266da53328c58a294cc14665c9eb2c4b87e244c285d5d42aa220b812044c98446449a31c91058260c69246522f325149906a4c7b4a63118b165798a2a4c493d620970ae4895209a9b84544017022089866c0c29605f8342d2181832a0550205ee2f2d31753569ac1345604a4a2850580242548125cc2a2601100d058bf16c5f4262f80b17b038bcc6c5e2302eed41764c0ba9505a8362e4141730b8b496c5c8b22e2171700a8b784c5b81e2da0b0a8260b28444c0222c00b15c048b183c57c162b609158038538205949094c04963088ad024580262be1115c098ad8445681e01a0b157038ac04455c122d68c4a5244b505e5a42ead013545094b384659822ac81116207ab082e57816aba0b15904a058225580eaa8d6153490a91585402c28811121088a702c4ac2229c1312a08894844540ae2505514f098a683c530162800b1320889f82c2909826011146058958444f4122541114069c9fb424f41e0120b13b038948444ec12295179498a4a423128c9128e179450a4a20464a022a860f54205ca082d4f816278094070449d01d4e1a426e52128090900404c1a22684e132698983504bd2825c5412d0a09583c4a81625207124460510204911c142081358bc99c524c5ad258d592869c8eb4d44ca4a4e505262729293148c90940049210980482c480aa23e1311e0588e81c46da013e4c004060069240249201a520092808cb52461a522e969164848a95e450a92265291228c0212d44429220128042788704c434163b117dd28b6e645771a29b84d49ba694da25b6c529b5c92da9486cf231654a930e5289e244c205f5fc2f2f416d740aeb6053554292a213d4b0969c84a4d823a441191c0868d02f43c1721808c020446f25038924178540c62902205c150280b61210707884a48420a408015106090828440f82207a1103c0881f84440db0204981012c08006c3fc30076110e1290628483f5a41c0960fc490621583eca40b4160fa0907c8443d42201c0f0f74707b138090261e80e0f30686d1302e0181b2900d44605b9402949802c10021078788383c01a0160c0d82605b03035d201a68c0b5280519300d42a02a10020078770383b41a00e0c00a07875a383a89c06815023098748383a01a1bc928e648c72a3e3511919e548c2294599323909513a1748b0aa0f03e050191c2110e28bc7045237d2f1bc948dd47c69a32334a9182528b12646e12a1902688e1141d07c098322a0981b40d0a4260198443601a160480af2406aa442b89815a4c0c027056120365a91aed28d64bc6a25234d251a4918cb2a45f14a2ac981a24a8970bc40052164250641182707a671242a098198490cf4a466a4a32d19178528ca28c6493e294991904b49c0ba450550701f0240c8c508861924301221484c0bf2486345e31229184948c14945f2322f4af178548bb27c519322e8968c61344608a0d83e0441915c8c0b806856a300c42216c0d0ae4605a1242b518144510b224857a342c12715c908ad474562362a8a7150508a427450936258270fe10858074180362a89014e4d0a724054230298a21488c0a2270509202dda916ad28b34a458a4a2ad18152578a52a45194a280a313e4b4950bc3f05215c2505e1182607a4ea60270b01261a07c0c04d2502581012c480908bc3e45d111a6932d149849210a4125c9112a088880a81f8440381e1265b0920784882c2400e11d1b08d8c04636022d281145407d0d8438502202e0f85b0872c84305c2142a108130830784102c1fc980f0110770683fa301d82207e11073078378341c81e0dc0d06c0583481c1dc100ee480782443b0221cc260e41106f098370440381e0d60b068038360441ac1a0d211068068402321f8990fa1787c0ba3d84d150250f41187908a3a8441d01f0e20f4700783683502c190d40b46703a32b481912c0c6560610b0298440b4220c00f0600981d0440e422070110612b81b95417c260bc0f05d0582803c1042209e0f0582602c2300fc220aa0f03a0882834e13da10140f04c0582501c0e4220980d0380882503416e2f0b5148594642b9321582f0a81485308c1b8451481f0a20f44e0782683501c190960b44903a23a48118a406e1202c0801fb4410d1c082d303f6a01f2500f4a80781403a0781c82c0e00e0664c03106019a380c0100628e0302402245e10a29080d683b6ac1bb4e0a5a6840924364821aa390d1188644882f0441684c0281e0585502b0781502c0a40e04e90026280028400391a0148d00e49005240091ad046d08224bc10a520812503e9180547a0f152074a50381481b0940294c0641e0300b00f0880703c034160180700a0780482c0200e02cd48156940a25204d25024548112940805e02c2900e1280608c0283d010168060750a8be8245b3fa2b9f114cf26b677b533b1a59ced0ce34a46da4a3411918e548b92944f13226c2f9281788f0b644857204298cc1486209e2e04b1202508a11c2e08c140430941f8340f81706601032f45a7f8ed2fa868fc7b43e2925ee690f51477a6233d1ca5e4e50efc2777b93395c91c9612e1e086f283b76419a1608c010260001f 16 5 11 10 6
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 978 (dagTraceF m_46 s_46 8 f_46) l_46 0) s_46 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 64 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_2 : treeBlockF 64 96 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_3 : treeBlockF 96 128 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_4 : treeBlockF 128 160 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_5 : treeBlockF 160 192 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_6 : treeBlockF 192 224 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_7 : treeBlockF 224 256 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_8 : treeBlockF 256 288 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_9 : treeBlockF 288 320 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_10 : treeBlockF 320 352 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_11 : treeBlockF 352 384 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_12 : treeBlockF 384 416 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_13 : treeBlockF 416 448 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_14 : treeBlockF 448 480 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_15 : treeBlockF 480 512 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_16 : treeBlockF 512 544 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_17 : treeBlockF 544 576 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_18 : treeBlockF 576 608 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_19 : treeBlockF 608 640 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_20 : treeBlockF 640 672 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_21 : treeBlockF 672 704 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_22 : treeBlockF 704 736 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_23 : treeBlockF 736 768 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_24 : treeBlockF 768 800 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_25 : treeBlockF 800 832 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_26 : treeBlockF 832 864 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_27 : treeBlockF 864 896 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_28 : treeBlockF 896 928 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_29 : treeBlockF 928 960 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_30 : treeBlockF 960 978 (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nj_46_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_1 (fun _ h1 h2 => treeBlockF_at nb_46_2 h1 h2)
theorem nj_46_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_2 (fun _ h1 h2 => treeBlockF_at nb_46_3 h1 h2)
theorem nj_46_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_3 (fun _ h1 h2 => treeBlockF_at nb_46_4 h1 h2)
theorem nj_46_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_4 (fun _ h1 h2 => treeBlockF_at nb_46_5 h1 h2)
theorem nj_46_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_5 (fun _ h1 h2 => treeBlockF_at nb_46_6 h1 h2)
theorem nj_46_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_6 (fun _ h1 h2 => treeBlockF_at nb_46_7 h1 h2)
theorem nj_46_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_7 (fun _ h1 h2 => treeBlockF_at nb_46_8 h1 h2)
theorem nj_46_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_8 (fun _ h1 h2 => treeBlockF_at nb_46_9 h1 h2)
theorem nj_46_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_9 (fun _ h1 h2 => treeBlockF_at nb_46_10 h1 h2)
theorem nj_46_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_10 (fun _ h1 h2 => treeBlockF_at nb_46_11 h1 h2)
theorem nj_46_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_11 (fun _ h1 h2 => treeBlockF_at nb_46_12 h1 h2)
theorem nj_46_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_12 (fun _ h1 h2 => treeBlockF_at nb_46_13 h1 h2)
theorem nj_46_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_13 (fun _ h1 h2 => treeBlockF_at nb_46_14 h1 h2)
theorem nj_46_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_14 (fun _ h1 h2 => treeBlockF_at nb_46_15 h1 h2)
theorem nj_46_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_15 (fun _ h1 h2 => treeBlockF_at nb_46_16 h1 h2)
theorem nj_46_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_16 (fun _ h1 h2 => treeBlockF_at nb_46_17 h1 h2)
theorem nj_46_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_17 (fun _ h1 h2 => treeBlockF_at nb_46_18 h1 h2)
theorem nj_46_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_18 (fun _ h1 h2 => treeBlockF_at nb_46_19 h1 h2)
theorem nj_46_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_19 (fun _ h1 h2 => treeBlockF_at nb_46_20 h1 h2)
theorem nj_46_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_20 (fun _ h1 h2 => treeBlockF_at nb_46_21 h1 h2)
theorem nj_46_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_21 (fun _ h1 h2 => treeBlockF_at nb_46_22 h1 h2)
theorem nj_46_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_22 (fun _ h1 h2 => treeBlockF_at nb_46_23 h1 h2)
theorem nj_46_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_23 (fun _ h1 h2 => treeBlockF_at nb_46_24 h1 h2)
theorem nj_46_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_24 (fun _ h1 h2 => treeBlockF_at nb_46_25 h1 h2)
theorem nj_46_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_25 (fun _ h1 h2 => treeBlockF_at nb_46_26 h1 h2)
theorem nj_46_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_26 (fun _ h1 h2 => treeBlockF_at nb_46_27 h1 h2)
theorem nj_46_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_27 (fun _ h1 h2 => treeBlockF_at nb_46_28 h1 h2)
theorem nj_46_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_28 (fun _ h1 h2 => treeBlockF_at nb_46_29 h1 h2)
theorem nj_46_30 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_29 (fun _ h1 h2 => treeBlockF_at nb_46_30 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_46 g_46 bds_46 978 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := nj_46_30
theorem lb_46 : LowerBin m_46 s_46 g_46 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xf0f0f0f0f0f0f0f
def s_47 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_47 : Nat := 0x107070f030f070f
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

def m_48 : Nat := 0xff00ff00ff00ff00
def s_48 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_48 : Nat := 0x1100170013005700
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 5, g_21), (m_30, s_30, 5, g_30), (m_37, s_37, 5, g_37), (m_7, s_7, 4, g_7), (m_12, s_12, 4, g_12)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_30
  · exact lb_37
  · exact lb_7
  · exact lb_12
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_48 : Nat → Nat × Nat := unpackForestF 0xe0493c405380a4f00450169faf17b5e2eebb56d769db40935d1ceb939d706a02d2ef1a75e349bc4bd7894af128e834ebc4a19a57334a85e15eca4b994942f0a95e151c76937854308ae61150c20b984142f02f5e05dbc0b97a942f4a85e0520168f72d72e5284dc56b66b96c5426e2acdb5e9b6bb36d3a6da6cda3a9b473368e26d1b55a38ab469364ea6c9ccd938a62514c4926c9b51a38a3271360ea78944f1249e0513c0926c1b4d8359b06802d0e609c4c0349549d2a91a549480a4b8d49d1a91a351ec69298d04d1c92a341200a437e8bcfd149f9ad3f25e862510c091f92d3f25683048fc949f894bf0267f494fc090051db645e6c8a4f40d1b1a93625e6c4b4e8941d0a83a05c6c4ace08f1c094380246c4a4dc0d1b11eb612901466c91659228b214e6428cc84f9900b3201401296b51656a28ad14e5e480bc13168a32d13e5b048b44b404a1ac0144e4b4aa92154222715e52278a405138ad271564e2a49c4f8049d9ea523d2bc94050f4ad241503d2ac884f11096220143d2a47a4f8f4969e8163e2847c4e8f40a00933206b440d0881291024a202bc6c05080ad1a140202ac60530c0a218014202a440538b40a1014a2b460405189cae139542702840508800b10a4a2146442508849d100140124638d2475280e3450109e2ed74649c0bb511709c0211c39af0735a132a01cd58411c081380e6a41c178041f8145e028b41094020a80405c028ac0c8e00a2902350020ac040f8041b8001f 8 11
def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x3100c4030e1c382ef0bb06ea1b90ede3b782dc1b702dc0af42ba1ae06b04a996a60a982a22a882a20a6929a0a682905a402900a30a8c0a3028c0a302844a102840a1028409f8e5179402500930a4c0930248292024809202480901240090023848e023808c123008c023008c022848a02280888e220888222088821a486821a0796de407901de37781de072a9ca07205c617181c417101c026aadaa06a81a626905a4069019e367819e067059c066859a065897cd5f017c05f017825e017805e017805e017235c817205c816c35b016a15a8152c5481520540550054014e1528930d4c013004c013004c012a34a812a04a0510c44010c243010c0418d060418100340010004000eca3a08e803a00e613980e413900e403900de33780dc13684da03680d62302cbe12e88b622d04b402d00b212c80b012c00b002c00aa32a80aa02a04a802984a602980a60280ca002800a002800a0026107ce1f007c01e086a71a806a01988660161c5801600580150854015004e313043e70f803e00f803e00f803830e003420d003210c8024700c4001 0xe2029b717ace2eef35add6b3aad5acda8eab46dc68bc69260920c5a397c463c25253ca08604de008b74d12ddaa3b250482a010171c91c2293804069b40937a2f6ec5dd48ab6314b71ab6a355db69d62d37651cbba316a2b2c4547609ca49311407bae0d7412863950768b99c5732ca86285cd06b99a57328a86205cbe0a1a0d3ae5a12445cce2b99a5430c2e63c5ccb4b994943082e5e850c76936cd0714ae62150c30b984142f9285e950080b9a917aca2eeab5eb46bbaad3b51a4dc342b5683a697a152ce9252d14a39e94330af28959c92a59054718a86085ec00bb7e1701c2ade052ba6b972942ddae5b150ac2714e4d2901c5083472479564a2989250024ac471568d28c1c4f834454794e4a298924f024a4471464e0101a50928a02493e0a2781259c5db18b57115ad62ada35eb36bb64d3ac5a6c52497b483608eabd1cd7238ad46cde8c5a4acb0951aa275524e6a09c52936432621e0f6881d4e8369c06b360d1c91c4c9389806922d4a25a54ba4e854952c919dd2148a3d3b2632a4a4d490bb2408e0491c4f239253d232916b4f2d0a4d274124a9248cde90a451ec81292f2431e09a3412392347f068e4921d91e439288604906091b89e3fa4a6e4651717a2a2944b5a6d6851097a152d42256824a4da8f60494961218004cfc091d91a3d034764a0ea541d02e3923c71250e0091b81a3e45e7b8a4f2d49b5a53c25e774b4e6959bd2936a3d3a262d84a49890a29385b058b6509609d35459698a2b49495d253414e51294ce51924a13313e35264b44b5940b320145f4809050178262d824628b2c3145692d2624239464c05393ca52e94643284b84f8bc992d12d45248b005159242294855088a64f1209629014574b482908e1192a15e512b4a05593ca92713e2c264824b520921f8144a02890541189e2292c440287c050f8161f9423e2749894905252595e492b48e5590ca92113e26264824b5000b1e81424028565108c0a1a1542202842050d80a1a1403229862510c00a168142b46052570a0aa1381424494468c888a11093a3b6b474d08e5291c24a372bc6a568ccab179522e29c58528a8a3131422502c4005075280405c0c69a3cd2471a287b41170ac2e118381f0c9380406834d7451ac83b55186a22e1785c2701836132a010170451c08138040681091055af0a35a126ac1ed48382f010460206c1494024a80405c06470080d011a80645e0b8b40f1581629018560209c040fb7da7eb34bbb68f34d0e5125c62437d476d68cd8ca5ac9434d276784cc7c918d84f1608e1a0fc041b8001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF m_48 g_48 bds_48 (dagRefF 228 (dagTraceF m_48 s_48 7 f_48) l_48 0) s_48 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_2 : treeBlockF 64 96 (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_3 : treeBlockF 96 128 (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_4 : treeBlockF 128 160 (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_5 : treeBlockF 160 192 (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_6 : treeBlockF 192 224 (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_7 : treeBlockF 224 228 (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nj_48_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join nj_48_1 (fun _ h1 h2 => treeBlockF_at nb_48_2 h1 h2)
theorem nj_48_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join nj_48_2 (fun _ h1 h2 => treeBlockF_at nb_48_3 h1 h2)
theorem nj_48_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join nj_48_3 (fun _ h1 h2 => treeBlockF_at nb_48_4 h1 h2)
theorem nj_48_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join nj_48_4 (fun _ h1 h2 => treeBlockF_at nb_48_5 h1 h2)
theorem nj_48_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join nj_48_5 (fun _ h1 h2 => treeBlockF_at nb_48_6 h1 h2)
theorem nj_48_7 : ∀ i, 0 ≤ i → i < 228 → (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := block_join nj_48_6 (fun _ h1 h2 => treeBlockF_at nb_48_7 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 228 → (dagCheckNodeF m_48 g_48 bds_48 228 (dagTraceF m_48 s_48 7 f_48) l_48) i = true := nj_48_7
theorem lb_48 : LowerBin m_48 s_48 g_48 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xff00ff00ff00ff
def s_49 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_49 : Nat := 0x17005f005f007f
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 6, g_19), (m_22, s_22, 6, g_22), (m_20, s_20, 5, g_20), (m_29, s_29, 5, g_29), (m_38, s_38, 5, g_38), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6), (m_11, s_11, 4, g_11)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_22
  · exact lb_20
  · exact lb_29
  · exact lb_38
  · exact lb_2
  · exact lb_6
  · exact lb_11
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_49 : Nat → Nat × Nat := unpackForestF 0x38946a00b4bdd12ff0a557850abba25de05b67025b3810d9ba257dd0afefa9577d0abba15ddedb66e855f740bfbba55ddcaaee8177756d9ba057005a3e34d7f71099b7145dbca66dc1171a6bbb4c6cda5b26d2d53694698d35bd8a366c49b3622d9b1160d88366c41831a6afb035cd66326b24e35d6a9ac934d641c6b4d53590698d353d45a76aa4d355069a8b42d452f6a2577510bb8d345c68afe9c1734b6aba635cd2c2ae34577464d9a3164d18aa68c4d31a2b79fc6ccfdb667ed833f4d99f86ccfc3063455f3d2b99b264cd8a6674553362899b018cdcaa66c0531a2a78d05fcccae660d57316b998155c682ee565b32b0c995854cac1a63416f248d99236cc91b06489b3242d992160c682be441731b2c98d84cc7c2a6361131b0598e054c6c1263414c0148f8c35ec5a2b62cd580147f6ac5bc489ae240d6d58b58736cc38b661c1b2d58af7e45ebf1af5f8d76fc4bd7e15ebf0aedf8573056b97e152c082e604142fc0bd7e05dbf02e5fad72fd2b97e052b562b5f4d3ad56b57bc58bdd365aad5ef26937925ebc8aede4176d56ad74349ba12f5da492ed04974252ba122dd2536e909b74244b552b5aa53ee18ad70b56b8d225c295ae108b6a94db7dae5aa51ed509f6c456b61ab5b4912d84ad6c145b5426dacd72d508e00a37b4c9b00252eb06bf67a45b3c22d60d76cd2d958357ac12fd92d16c908b5825db15b658a5b2c50d958257af9a6d7c93abe2bd5f934afc0a57c54ab048b5c46cae234571182b96815c254ac11bd6017eb36ab59a55acd22d60176b12d958057004a3d5ad7aad4bb46456aad2ed18d5aa68a95336ca99aa54c5b28c4af4fc5aa7e2b53ed5a9f69d50244a7d2b518916998b54cc56a65ab534912994ad46235a5cae52c91e8c0714a14da35a3524d128d28f4734aa39a351c51a8d26b460340049fd131b2892d939b57a152ed0a916852bd39a56a092ed04916732ad3e35a9f1ab4f895a7d2893e1569cc9b4f4d727948f398189d123cea5367526b3a1469cc0a0024ee6e6bd3725d9b8af4dc176578ad35a5d9acaf4aed5a678d933c5499daa4ae95e608b530456981ab4c4912604ad3014e95d1acb097a582bb2c145965a84b48c2592892c12595cab0024de552892946c949364a45b23f6af2835c93d23c7e912494bb24a45928a6c944d6492691f956901ad48c172406ad202569052548291a4128d201448fc9b0024ce3d2bd1da568ecab0024ae386d91c36073e2bb9ed6e3448d1a02573dad4611b2302d91806c73dabc3d17a1e6bd0f35d879ae43cd4a1e4bd14250878af43c576244b9122508782f43c1761e0b90fb5c87cae43c149cf6ace7b4b8652d43295a1904ae7b4a85cae39ed1e0d8b50935c848ae4241720d8ad06b56835a741a53a0d09ae7b4682d28404d16024930123a81d224048da022bd0193480c0a404549cf4ad0013e73cad3f8d61fc4d8fe25473cabbe0d75f0492f823a7c11b3e0579f347af992a7cc933e0511f1288f805d73cab3c8d69ed2b8f23567912b3d4511e42acf213e795253ca919e528cf201473ca53b3159e14a0ecb567652d3b2959d9472ed34476ca03b4911d92ace794673c1fba4d59d268ce925674ca23a4559cf07ae814c73c1b80249dcd06c0084b681afb92915c928ad035d71c36340d5da04bee1b4570ca2b40975bf6d8df96c6fc3634095db869adc24e6e02f3720d1b9028dc05268122b651b1b28d0d94606cda0364951a046ed015f6b5a2b5a955ad48ad015d6ac3634055da78d8d3b6c69cb63404dda16d8d0b68685b0344901a14a8d012700423b3ad799d4babe45666d2eaf8d59968a8cb36c659aa32c1b17c4aec7c5a63e2b31ed598f69cc824463d2b2f8915898b4c4c56625ab314911894acbe23561c2e30c91d7c270c214d5f5233049117d28ebf34a5f9a32fc5197d24abe1340041faf31b1790d8b1b575d52eaea915750bcb19565c92eae4915630acb635a5b1ab2d89596d288b605658c1b2d4d716948eb182c59123aca5356526ab204658c120020ed5e6bcaf25d578aeabc1793f8acada5d56c2f27ed59578d8abc5455daa27e95d508b4a8456541ab2a4911504aca804e4fd1aa991b14c6d8a606c4fcaba90d6148690a403c4fc93a80979402baa0145505a82848c141288a01254fc2b0020dd3d0889d46c4e8b62741b1276ae9c35c4dd23a4e511314ba98a454c8a6a644d531068938564a1ad25c571286ac942564a5252529192928c9404449c1b0020cd250bc9195648c2b0020ad206d8903602b62b95ad6d1c48c8e1252b5ad2311b1182d88c06c2b5aba0d179066bc8335d419ae20cd49064bc87a5c43d2820c579062ba8315c42dae20c549084a0840504182f20c174ad6ac56b4b4052d2029590124a56b4a3fc2e15ad1cf58b47d35c3e8ae1f4170f58ac7ab563d5a71ea534f509c56b463cd281d4d14ea4927523a3bd221d48d8ea0bc758343ac0a1d4148ad4ac72b6c395b01cc900e54a85695738da415a51cad27e6db5636d2d1b6958db4946da4636ca315a4f4d90985693735c1f15a168d36b069a6c34d2a15a15cc56ba62a493151d18a8d8c52bc6523d32895194498c5288641543142e98c910c505a568562e5ad184170b96ac5ca562fca2172158b907c5d24a2e923174518b90285684a2ba2b16c940ae6ac5725a2b92b15c8e4af688581402bd2215c558ad08c008272a8b61541b0896ae5325d2992294c578894ac50b5a285ab142958a127c44a362712e9389149d2884e126224ab1341709948e4494c2412392a5349526a48146245251229189128c48126224a2114d688a6ac4525622ca21145588926c0081f2193610c1b0656ae4125d20922904178652ac3eb5a1f5ab0fa9587d07c329361e12e8f0914792883c0261942b0ec5707548e3284c1b1238e25347126a360461b5250da9186d28c36026194220ccd68666ac3325619ca20cc1586506c0081b185360c25b0610d80dc5717d36036d5c5b4b82d95c16c2e036d1c556ba2aa5d155228aa578550bc0da5613a2d0a49704e8ac273561392689c8d41b48c2135a125ae092570490b821356109a508d1604268c212561089f0840f81b46c1da5d0ed228764d83d2881d9260ec2f036558336b419b560cd2b06c510332ac199460cc1f0364d8284ba142450a09b05c5102824c1405e0a5280544c0292881402606c2b038d681c6ac0e25608ca20385581c28c0f25007c9803c5101c0ac0e03e06c1b00205c190a80aa6c05c2a02a5b0150d80135704cae02491c022480625d0312281a5340d26a060140082b006d68096b801b5600d2b0089280448c0214600c0a0040d8010260001f 10 11
def l_49 : Nat → Nat → Option Nat := unpackLinksF 0x73a039c05cd43e6a0735039595cac0e56072b03930bc902e480724038e11c700e3417180b8c01c600e204710038705bdd7de626f3037885bc40dde16e52b7203b882dc406e2036f09b780dbc06de036e83b740db80ed4236a01b443da206d1036707b380d9c06cb0f6191b0c0d8606c3036085b040d800ebf07581fab04d5806aa0b5501aa02d3c569d074d85a6c0d360697134b81a5c0d2c0e96034b01a541d1a468d034507a280d1406870f4381a1c0d081e7c233c099e00cec1676033a059a8acd20e670b338199c0cc626630331819881cc406620330839648cb206560f2b019580ca61e530329819403c90462493120188c1c4606210b0f078780c3c06142b0a018500c28060f1707818342c1a060d03058582c0c16060b0304078200c1006060b03018180c0c06060301877c52be205f006f8017c00bda1ded02f6817b01bd60de02ef0017800bc005e002ef057780bbc05de02eb1171cfb8a15c502e2037100b860dc302dd916ec0b7215b70adb816d81b6c05b506da816b48b5a05ab0aca2f6500b2415900ac8016400b10458802c30560c3b06058302bc955e40af2057902ba0b5cc1ae6057302b9815cc0ae215623eb1015880ac0155f06ad8954c8aa2155102a8815401a90454802a3054bd7a5e052e06940d4a00a4825220a91014841a3e15152a8a034482a220d1102888143c2a12350902840341c1a0e05060681094080a020d000680013f439fa04fa0e7d013e809f404f70e7a073b479d614eb02709538019bc14de026c0d36009ae0cd312698134819a20cd1026803330499804cb06650331c398e04c702620730439743cba025d012e8097404b12658812c409543ca906538529429345c9a024d01264193204970a4b8124079200490024705234191a048c06450520c78f05c78023b051d028e8046d1e36811a448cc1c6506320319008c804610e2e8917018b8045a0a2c8316408b20459022b07148489c244e0226831340896144b022485104887c1c3e021f010d0a8680434021a010bc585e042d0a16810b408541c2a0215010a028500428021401098284c042602130109808461c114a078503c081e040f02039101c080a1405020281014080a04020e00830040802040101fc12fdc17e623f301f902fc807e013f001f800fc007dc13df3def80f7817bc03de01ef00f6c37b40bda01ec82f6017b003d801ec00f6007a043d001e782f10b7860bc301e084efc277e03be05df00ef8077c03be01dd86ed467680bb305d884ec4076203b101d880ec407600bae09d38ee94274a03a501d202e9007460b9b21cd80e642704bb8201c004df826fc037e01bb10dd806e813710db880dc406ce536701b380d9c06c42b6105b080d8406c2036101af84d40f6a0035001a704d3416922341219f84cfc067c0b3e019b10cd806681334019a00cd0065e2b2f019780cb426580b28119010c257612030805810cc0805fc22fc097e00bec15f212ef297702bb025d60aeb017580ba425c632e3017102b8415c202e0056e08b7005b60ada056d00b5c35ae02d40d6a00b5005a802d10d6706b1c758a12c5015d94ae8157012b801590cac805620aad115680ab015560aab015502a98454c02a5055202a84354202a1014f06a6c35283a94014a00a500528028b254580a2c05083a830540849fc24e85a74013a009cc14e602710938809a874d4026a01350099454ca026501328098054c00260012f0497414ba025c052d0494c74905a480123049102488023d1d1e808e4446c1a35051a028d0046802310d16888b01458022a0914828a404520229011306888443c221e010e828740436121b010c84844841c1a0e010700810a40802040102007fc53fe01fd08fe807f403f419fa00fd007e803f011f800fc007e003ea19f500fa807cc23e601e148ef8477c03be01df00eb9075c03aa11d500ea8075403aa01d20ce88274403a201d100e41271c138621c300e102708038011c000e000700037c11af3cd7806b4235809a810d0106800336299908cc026600330019800cc006600320419000c704638031a098d00c6806340314198904c480620130e098700c38061c030e017f20bf805f812fc017d04b9165c412e2016f08b6845b402d8096c00b6005b002d801690cb18c58812c2095f08af8057c02be015f00af8057812b811551c9f2e4f8027811322898824bc225e012918940249822481124008f0c478023a091d008e0246042300117048b0244c322601130088064400220011000868642832140109048402420020e0903107e0e3e821f400f02877823b421da00e718730239021c410e2006e0c37001b608db006d0235841ac00d5046a0234431a200d1006706338019c00ce006586320319000c7046302318018a08c1105d0e2e8017400ba005a8a2d0115258a90054802a4014828a4005200288214400a2004c9226401320098044c002600130008e284700238011c008e00458622c0116008a0444042200110007f243f801f420fa007d003e021f000ea3875003a801cc20e600720439001c800d6386b0034841a400d2006804340019c10ce006604320417470ba005d002d8416c00b4085a002c8216400b00856082b0013c7088584400210410800801040001c8e0e4006a20320c18820c0106000300016860a440500828001304094104a0025001280088303c201a1000b20001 0x2f948bc4a35c25326a6912f446984a56bdd1b472577862ab5693d9b09aa42177850aace83d5701adf11b3836d984a5ce08b67021b26f2c9359348e52eefc9575248b79a359bcab0c61777d0aa31015dedb64de5715e0c8ad8344852eef09575148b7923518caeeee5555e0ac30816dd5b62bc173874bfc225de012bdf69575048b8ba3dbd91bde28d77f2bfbe15dde8abcda556ac27b351358dc93ef217f760bbba0575742ab380f55a06a8f8271800bed8da30b6c9abb54bbd1a428d33710987e34cdbca6616d1b6b68b3494ddc0a2d144e654262ac84ddb822af40e53c063b034484cae1f41736c8d9b5b64da9aa6d28d3056b97f35cd9e36616d735f6a1b326cd94b66c8583630d9b1060d81ae6ba4d35a069aeb54d59a25dc4d35a6a9aab44bb49a6bf193548a98536cbb1226bc4e35c269ad838d641a6ac4d35506975234ba51a6aed3b54685a9a5ebad1b5d08d3522bb34155aa49ecce4d60a24ba885d5602ab320f55706a79025d24b444e592c12890292484cae69c1734c6b82515c9a5aee9ad56272ada4155a989f4a64c85f0bba585521c0c8300473d2a90a35c1242e6929b3482c9a3954d189a4505721f2b9a246cd0db6684d83414d91395ccf0a86801b33f0c19e95cce89a66e0533a2a9601448109266e552bf28901924cf13257c952024691316cceca6672513380319b014cb83420e191bb08876824cccae1f4173316b82485c565aee64d545f2bb9815541c2b65a1559607c9d8322a80f02c04b220a87e35c128ae65c5b32d0c996054cac1a212171080b994c6cca1b664ed83264d99296cc90b020e173210a19105cc7c1a6380531f0a8dd0443b012638151b908875824c84b2370550ea2688306cc802663c1131d0598d824dc9afedad77686b7b0b57bedaaeb0d4f5068b73a36d3cafe94577452b79f157874aae6a54ebd28b5293fa209dccc4de5126700925cd02fe5e1772a0b7918574142ae3414db708aca83f5e01daac0dd39066748252a40f90a06c5e02e0a013c61af62f15b166ad86564bd6325e0992f88ab86355a90a6cca516bb27b8993565026aaa115b507b89035c322c620db2f74d98796cc383660a542fe0a18185cbf42860ad72132b98105cc0c2e604142fe6b97e95c3e82e61917b0b6bd8535dc252f61057b072bb8315c844aae0854aa327b32135c042f600176ff0b87c855bf0293260f55406b7d34ebe22c5ee9b2eb4a975244ba5225ead26f44bd74244bccaecc6556e427b08135bc82eaa6156db07a7c035bb8925da092ea29b31145b8c96c0e496e909aa9045b68169de096f069377a5ebb1295d6916e84895c145b889ec0c4d69f25b309256c822db20f4ee06ac782d54412c1c5526026971a44b8d2257716ae58ad72356b892b41c5185d09b708451700adbed720e2987a8545401a5b4912da488dac5ab722b5b6d5ad94ac2e94db60a29ea1185b02d6b35c3d42662916f118b586c57bee2b5f2d6af66af78b56b9d2b56e55ee629f7014db78a3c185169e27b2f9356c42bdba13ed709b6a8473d022b1c0f54f06a2d0177fd1b5a64da716c92f1349c5a3586956bc49b682457e89329c136cf08aa68359c5ae59a5b2294c9612547d892578d36ca68b14a46a1c9d4ba4d9fd24a7404db24229500744002aff46cb1db6452972c62d96286c7d4925804d2bf02961b4d9a1a2d8493ab846d6095eaf8a950c4ea5c26cfe1257c8925661345708a7282529c0e87e056b94a92d9449689a572d0262488f9934964925791b2bb8d108c64aea304c6d92b84a8fb9449609a0aa1903b028f8924539aed6ad54e84bb5a255acd22be0498550aca6036ac4b60aa172d16bf6735db31abcdad56cb4bf6425db112bc3a956bd48b5ba37a109d4ae4da3c254fd9277bc9356c17eb20bb580571502aa960dce404e5281d0e80ad280d2ae6bd56a5da8d2ad529169b46b49834aad2ed38956a748b51235a691a5240d2a046909a54a5c14547192a98a95436ca71b254ed529f4894ca34a98b652c0e29106948044955ae51e0d2a048950244a381254916aa38ad51356a85a753e95a8d0690995ca69225349129d8b54e456a6dab53295a972b94b247a50a6d1e5169226b47b54a49a251c4d29069547b46a38a3526d1a9128f46935ab22b554d5aa54af4f245a611ad2a0e28c0690a1449e80c5151b1ec4c9432547ad1a5125b27f2c9411549f89a4f2062770293b0149f4924ea052874baf6255a1922d0a57a7c24d3a0147a8925069767f4ab412457a493428d727d2893e944a01ad4fed5a7e4ad3e1569e9ae4f291de62a93a944794924ec535e628b3a9359dd23ce8519e424d44357a112b3c68da812ad3d9369e00c4e6052716bd3825d8452acd09166346b3795e788934dc174510ab3625d9912acce9161046b3595e780930a00d650261312347709240e8d1da24934c6c846324d1152646c933b54819224c28d1de2c92e15493c983b24926248931244964a24cb16a648ad31b569852b4b055a6029c270357cc9a4b24925a2892d23096da84b25125e4bd2e95d778aacb8515f726b2c1250f81acdb15a6a6ad3325783122cbe8d6572ad271307609334c15c4d08a71027941264aa512506b8f6954952364a69b24f4892916c914b2498552442692835c908aa4945124124927a47924a348049a4b2692513492ca6c845164a26b26a5d9152ac9891649269219449089a48c1724126921a4a9092348251a476b522b569112b480512516af27244920ab47e4da3d2bd1e2568ecab416d51e12891cb6c86db4422d92386c1083448292a3c4591e028917464825b23f25922e4ab0da4a8d5233fc555ee294ef94669016c68094a403a1c8158ca3645cd61fd4d91896c8c03644a172200a10a35c8a0ae448172284a10f8508952e448942206b90f95c1242e45d17a2d6bd1635d8adae422d562a6a514a5e89caf44c575ec274ef13688c2f444176210b824055878291460743802b07c54774aa410d5a1b4b50d25683d22bf05594908aa502d86412c1ed22172b90a35c84cae424172074890ac5a8462b420d5a0f69d032567dcab41c53a0d09a2284576c9a41694207468ee1547689a3e851207488f99448109a4060520a68b04a498211d40c8da052bd011527f0a2be4511eb274ec93668422ba80b44404a5101d0dc0ac004f9fe6b0fea6c7f12a3ea551f4488f99447d51ebb88d5f4254f99267c41e86c0d5d303a1e8157c4a23f4d75e26aafca497e11d3ee8d9f62bcf91447c02e86a155d205a1e02579c0a3da571e6028f51447940a3d4511e7494f3246794a33dcd69ec6acf5a567a4ab3d04f9e4028ee14476d223c2941da288ed940771a23b4911e28acf035677d2d3bc959dd472ec9560d02288411033028e994474ca2348d69d66aca534a755a33a8959d22aca40461081b3a0530420791bc578d9adc66d6a2f6af0eb56871a5c30d2a1668f063468052b3fe569fb2aef795678ca53b0519a00aea384775c1fba20f5cf06e208352800e864054d626ce6836585b228c0d16168cdea556d926b94915a929ae49456a09a9a2099616b8e386c44532378950cd048db34d711a2a22919a529ae19455dc1d28a0d8d404a4201a0c40b1ab1b1c16d888a5c700b637e1b0cc048dd0346e40a37ad355868ade24e6c91b35c5345728ad09256ec2f37014976074a203634c1299209083034180166cd2a28611142068d9b40549221940d141048db46c6d6341f3191b48c0a9b646c92a19c111400682b1640b00a190091a969ad7b456b92ab4a935ad48a2b14669c9b18e098562b8d586c6a6360a3191a86d8d396c0bc22344d502b028150146892006c5102e04814814695b6348da0486c8d1b606852a06a5902d0681401472dafb90d75c66aeaeb557152fb84975be4ae82a556dd22b628ddb02bed615d6a8ab8a8555a626ed01275d01d27e0d92405469027310131020682702cc2134679af33a975934aacca4562d1ab064d19b4bac625565d22b248d58a468c11346411a1f495187050c9c646662a330db18c6c8cbb5463d223128d186270c0934658363005113d6b8bf934641223209117e248ca45a64e2b324d599169cc7a565f49a1f41718a488c52446362d3191598b6acc4a5661c2e30c91d8429abf9456089aafe95182488bf124601a52fed197e28cc1a46604a3afa4959c8accd3566552bb1c9158846ac29385f09a1f81116a058bd46c304b22ec550c0268bc86c5bc322e41516e068b482c59c122cc0516d048b28145dd2e9829557648aba85e5b0132c8050bf048b9a5d5bd2aae4914be04c7e35c5b4222da511706b4b7b565b92b2d81596a6b8b4a472ec2a2ca110ba048b314d2eca2aca4d56748eb20462e4132f0d5d742ac5c1365c42b2d60d968058b1824585af2c0974f94aaac24554d1aabe574512aaaf05e2dc132b8975544aaaba453e11a8a04d55b0bc5a8264e0182a48d0b104877a342bc122b31b0f98c8ac454551b22aed50ee488a8a342cc322881513706057024549222a491141088aac5a5522b2a6d59514ac271355002b2a01394e8d828c64535b607c5114c0d8a5358115aa292d20342a8a403c3289a28249142288a123050da8282511464bca295d2ccaaa88514ce26aa01250bc1aabb1595a6acab2573d122a9e8d54b2ae2694551c93a7e15936060568264e0a627a111386b8610544f2362765b1372889d06c4b4322681512c0689c35c4a82a264111290489ba474c42325009933068990344cca6a545153226a9aa5d4b52aa6891531068958444b8ae2540d12906895a4a4a9232525192f6b496b564b12b250111396ae9b1444c02b24e0d9250bc9215648c2b1e6d50b608890b6c40db41f2d91206c07c3443c92a16e190b50888b4643c5b21a0191164aa81a4a475231be4b51c24a6a85530c25168118800341301646a3622cd60d44d88c96c460362205710b2a07e35c43cae212171104b887a5042dae094571080b884a504202822d179156bc8a35d44dae1f2d55126a488a5e438af21a5750c2b824155428a920e179060ba6083a2cc1b0fe0682502c7bc542c82a1e0d59034b4812563dd229c6514dd25a8092533c2b1eed20ff0b87e35c3ecae1f4170ef4887ec5a3e62b1f0d58f769c772563d8a688a514ce0ac7a84e2c01a1e6940ef468588542bc1a196110ef488650443b01a1d6050f268a78a493c11d1dc8d8e528a7012d110929da178ea0a469845324221800e8ae06c3f01a0900b1ccd50200280f8143992007a490230880f0143a1b61beda0486c873b603952a0784d0220c80e814375ac08ad50e36906d93c0842a0865101c02863044381ab1be968de4ac6ea4a371231b65184324c6285610c9e1b2130d707c6ab58351361a6950cc2a865a44328a21988f4b146a6592a328931900f42306a6301d0b80a990550c648868b5d2ddaa9a0924cf47467236334af192510c70ba110553141685a094bc0286105c2ec0a17e110ba0285f9442f125176918ba28c61b5a305ab180958be0ac5e83e2e40a162510b04885b2502bca2160500b168857a442de2b16ad58b44b459a562c91c95c5582108a8fc57479ada36d69176ae82b56411a5a00d28fe68e7a3463a52b1c855ce228e7093f3689e9b04dc4126a6b05a3482b988158b8094568461f00d036058490a84d03c28d3214e950a24685596c234b213c550992984b9442309a1541b0962684a93422c92150974a34aa53a45298af1284d08a24c49944064ae1244d09d28848934291ad146d58a24ac4e156240a21424f89d2484e94427d2e91a9549e48a4e1262682e13291c922a84a9442449212c5349228a4a93524d251249189128c4ba47250a3120498490b84594422ca211cd688d6ac46256228ab152d5ca54ac5023626cab1305308f288449361282a0ec0f0874d83f96420caa0fc4d0860d8348641e82a0ea13073088340341c81a0e20d0670484225d1fd2a906914820bc38034198130de110170b8370341e4220da0d0806b43fb561f92b0f01586c0883e83e1e4120f25107b4ba34a551e9228f0098762b83aa471b82a0e21106d0483914d1b8a28e24d46f494372461b4a30e691c7008c36026128ae0ce110672883535a1a5ab0d0958660ac42b57204ab0f84d8770ac3a04c1ac220ca0d8634d828a64141220c45b0610d80981017d36090990574a8222340e0b207e55037268128640c02a0480d0120202ea5c1152a09c9105c2b82d85c0d892046090596ba28b551612e8909545748a2b15e0d4930aa1782204c2925c14e2d0a3158506ac27a4d1152289c8d43e2ac1a1260bc2b0420984b6b82515c1242e08d1603d28817044131ad090d584769422b461112b0785584327c168561081f07a4901e0481e9441012e8709543f48a1f1360f0930761781d04c1b1440a42206c510396b41c3560dd2b06a5583428c140560cc1f05c49029048171440a9220544c02b4a0149440c52e84a9543048a179360b4930581782804c11944078220465101f4880f9300812803c510266b412b560912b0445582128c0e8560701f0c115c5e6ae2d3471512b09a9184146c1d1560c89b04e1581b06c0881004cae032150132b80b8540613602c5b0122480a86c0203201e150070680995c0142a01a1100404809247030230060980e02806814038a680a5140d26a0825d0212a81e9140c02803014025ae00a050040280324a015230085180a6b40435601d2b006050146ae0892402c2b0040db88697b9b47c6523e2a8fed446f6914babca3d164fe722772b1378f899c744adce24ee604b67c23af60fd620769f03749819a440acac04e4401f1900d83405c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsF m_49 g_49 bds_49 (dagRefF 906 (dagTraceF m_49 s_49 8 f_49) l_49 0) s_49 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 64 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_2 : treeBlockF 64 96 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_3 : treeBlockF 96 128 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_4 : treeBlockF 128 160 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_5 : treeBlockF 160 192 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_6 : treeBlockF 192 224 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_7 : treeBlockF 224 256 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_8 : treeBlockF 256 288 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_9 : treeBlockF 288 320 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_10 : treeBlockF 320 352 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_11 : treeBlockF 352 384 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_12 : treeBlockF 384 416 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_13 : treeBlockF 416 448 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_14 : treeBlockF 448 480 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_15 : treeBlockF 480 512 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_16 : treeBlockF 512 544 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_17 : treeBlockF 544 576 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_18 : treeBlockF 576 608 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_19 : treeBlockF 608 640 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_20 : treeBlockF 640 672 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_21 : treeBlockF 672 704 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_22 : treeBlockF 704 736 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_23 : treeBlockF 736 768 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_24 : treeBlockF 768 800 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_25 : treeBlockF 800 832 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_26 : treeBlockF 832 864 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_27 : treeBlockF 864 896 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_28 : treeBlockF 896 906 (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nj_49_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_1 (fun _ h1 h2 => treeBlockF_at nb_49_2 h1 h2)
theorem nj_49_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_2 (fun _ h1 h2 => treeBlockF_at nb_49_3 h1 h2)
theorem nj_49_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_3 (fun _ h1 h2 => treeBlockF_at nb_49_4 h1 h2)
theorem nj_49_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_4 (fun _ h1 h2 => treeBlockF_at nb_49_5 h1 h2)
theorem nj_49_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_5 (fun _ h1 h2 => treeBlockF_at nb_49_6 h1 h2)
theorem nj_49_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_6 (fun _ h1 h2 => treeBlockF_at nb_49_7 h1 h2)
theorem nj_49_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_7 (fun _ h1 h2 => treeBlockF_at nb_49_8 h1 h2)
theorem nj_49_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_8 (fun _ h1 h2 => treeBlockF_at nb_49_9 h1 h2)
theorem nj_49_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_9 (fun _ h1 h2 => treeBlockF_at nb_49_10 h1 h2)
theorem nj_49_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_10 (fun _ h1 h2 => treeBlockF_at nb_49_11 h1 h2)
theorem nj_49_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_11 (fun _ h1 h2 => treeBlockF_at nb_49_12 h1 h2)
theorem nj_49_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_12 (fun _ h1 h2 => treeBlockF_at nb_49_13 h1 h2)
theorem nj_49_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_13 (fun _ h1 h2 => treeBlockF_at nb_49_14 h1 h2)
theorem nj_49_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_14 (fun _ h1 h2 => treeBlockF_at nb_49_15 h1 h2)
theorem nj_49_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_15 (fun _ h1 h2 => treeBlockF_at nb_49_16 h1 h2)
theorem nj_49_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_16 (fun _ h1 h2 => treeBlockF_at nb_49_17 h1 h2)
theorem nj_49_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_17 (fun _ h1 h2 => treeBlockF_at nb_49_18 h1 h2)
theorem nj_49_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_18 (fun _ h1 h2 => treeBlockF_at nb_49_19 h1 h2)
theorem nj_49_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_19 (fun _ h1 h2 => treeBlockF_at nb_49_20 h1 h2)
theorem nj_49_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_20 (fun _ h1 h2 => treeBlockF_at nb_49_21 h1 h2)
theorem nj_49_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_21 (fun _ h1 h2 => treeBlockF_at nb_49_22 h1 h2)
theorem nj_49_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_22 (fun _ h1 h2 => treeBlockF_at nb_49_23 h1 h2)
theorem nj_49_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_23 (fun _ h1 h2 => treeBlockF_at nb_49_24 h1 h2)
theorem nj_49_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_24 (fun _ h1 h2 => treeBlockF_at nb_49_25 h1 h2)
theorem nj_49_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_25 (fun _ h1 h2 => treeBlockF_at nb_49_26 h1 h2)
theorem nj_49_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_26 (fun _ h1 h2 => treeBlockF_at nb_49_27 h1 h2)
theorem nj_49_28 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_27 (fun _ h1 h2 => treeBlockF_at nb_49_28 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_49 g_49 bds_49 906 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := nj_49_28
theorem lb_49 : LowerBin m_49 s_49 g_49 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xffff0000ffff0000
def s_50 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_50 : Nat := 0x11170000135f0000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 5, g_23), (m_25, s_25, 5, g_25), (m_27, s_27, 5, g_27), (m_29, s_29, 5, g_29), (m_39, s_39, 5, g_39), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_25
  · exact lb_27
  · exact lb_29
  · exact lb_39
  · exact lb_1
  · exact lb_2
  · exact lb_10
  · exact lb_11
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_50 : Nat → Nat × Nat := unpackForestF 0x342e8b471476252c491c35d108e5169128215028ac415841b801f 4 11
def l_50 : Nat → Nat → Option Nat := unpackLinksF 0x887a787878786360606052503b0e01 0x685d30ab0d74daa903654a08541a2d1c5620ad8d1ed1dd14b9246e11c41b801f 8 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsF m_50 g_50 bds_50 (dagRefF 14 (dagTraceF m_50 s_50 7 f_50) l_50 0) s_50 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 14 (dagCheckNodeF m_50 g_50 bds_50 14 (dagTraceF m_50 s_50 7 f_50) l_50) = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 14 → (dagCheckNodeF m_50 g_50 bds_50 14 (dagTraceF m_50 s_50 7 f_50) l_50) i = true := fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2
theorem lb_50 : LowerBin m_50 s_50 g_50 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xffff0000ffff
def s_51 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_51 : Nat := 0x175f0000577f
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 6, g_28), (m_24, s_24, 5, g_24), (m_26, s_26, 5, g_26), (m_30, s_30, 5, g_30), (m_40, s_40, 5, g_40), (m_41, s_41, 5, g_41), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_12, s_12, 4, g_12)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_28
  · exact lb_24
  · exact lb_26
  · exact lb_30
  · exact lb_40
  · exact lb_41
  · exact lb_8
  · exact lb_9
  · exact lb_12
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_51 : Nat → Nat × Nat := unpackForestF 0x145745a3c35d128e516952e145626ac455849b801f 4 11
def l_51 : Nat → Nat → Option Nat := unpackLinksF 0xf18f04b91220c08090581 0x145750aa993586ba8d5489b2a5c68b49158dab1156968ee51c49b801f 7 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsF m_51 g_51 bds_51 (dagRefF 11 (dagTraceF m_51 s_51 7 f_51) l_51 0) s_51 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 11 (dagCheckNodeF m_51 g_51 bds_51 11 (dagTraceF m_51 s_51 7 f_51) l_51) = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_51 g_51 bds_51 11 (dagTraceF m_51 s_51 7 f_51) l_51) i = true := fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xffffffff00000000
def s_52 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_52 : Nat := 0x1117175f00000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 7, g_34)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_34
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
def l_52 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsF m_52 g_52 bds_52 (dagRefF 0 (dagTraceF m_52 s_52 7 f_52) l_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_52 g_52 bds_52 0 (dagTraceF m_52 s_52 7 f_52) l_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xffffffff
def s_53 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_53 : Nat := 0x135f577f
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 6, g_36)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_36
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
def l_53 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsF m_53 g_53 bds_53 (dagRefF 0 (dagTraceF m_53 s_53 6 f_53) l_53 0) s_53 6 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_53 g_53 bds_53 0 (dagTraceF m_53 s_53 6 f_53) l_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_53 sub_53 gl_53 rc_53 nc_53

def g_54 : Nat := 0x1117175f135f577f
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 9, g_49), (m_46, s_46, 9, g_46), (m_44, s_44, 9, g_44), (m_42, s_42, 9, g_42), (m_52, s_52, 8, g_52), (m_51, s_51, 8, g_51), (m_50, s_50, 8, g_50), (m_48, s_48, 8, g_48), (m_47, s_47, 8, g_47), (m_45, s_45, 7, g_45), (m_53, s_53, 7, g_53), (m_35, s_35, 7, g_35), (m_34, s_34, 7, g_34), (m_43, s_43, 6, g_43), (m_19, s_19, 6, g_19), (m_36, s_36, 6, g_36), (m_14, s_14, 6, g_14), (m_28, s_28, 6, g_28), (m_22, s_22, 6, g_22), (m_27, s_27, 5, g_27), (m_40, s_40, 5, g_40), (m_21, s_21, 5, g_21), (m_18, s_18, 5, g_18), (m_23, s_23, 5, g_23), (m_24, s_24, 5, g_24), (m_25, s_25, 5, g_25), (m_26, s_26, 5, g_26), (m_16, s_16, 5, g_16), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_31, s_31, 5, g_31), (m_32, s_32, 5, g_32), (m_33, s_33, 5, g_33), (m_15, s_15, 5, g_15), (m_13, s_13, 5, g_13), (m_41, s_41, 5, g_41), (m_37, s_37, 5, g_37), (m_38, s_38, 5, g_38), (m_39, s_39, 5, g_39), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9), (m_8, s_8, 4, g_8), (m_6, s_6, 4, g_6), (m_4, s_4, 4, g_4), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1), (m_0, s_0, 4, g_0)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_49
  · exact lb_46
  · exact lb_44
  · exact lb_42
  · exact lb_52
  · exact lb_51
  · exact lb_50
  · exact lb_48
  · exact lb_47
  · exact lb_45
  · exact lb_53
  · exact lb_35
  · exact lb_34
  · exact lb_43
  · exact lb_19
  · exact lb_36
  · exact lb_14
  · exact lb_28
  · exact lb_22
  · exact lb_27
  · exact lb_40
  · exact lb_21
  · exact lb_18
  · exact lb_23
  · exact lb_24
  · exact lb_25
  · exact lb_26
  · exact lb_16
  · exact lb_29
  · exact lb_30
  · exact lb_31
  · exact lb_32
  · exact lb_33
  · exact lb_15
  · exact lb_13
  · exact lb_41
  · exact lb_37
  · exact lb_38
  · exact lb_39
  · exact lb_12
  · exact lb_11
  · exact lb_9
  · exact lb_8
  · exact lb_6
  · exact lb_4
  · exact lb_3
  · exact lb_2
  · exact lb_1
  · exact lb_0
theorem sub_54 : ∀ b ∈ bds_54, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_54 : Nat → Nat × Nat := unpackForestF 0x9d36fa30259d263a1b7da18659d16f9fb71a03719f8159d1639e2719e1719d06f9d06d00c579c46d00b579b56a00b4799457992569902500a5b9827c964679626696a6a9602500a4b9427e94a8c9417f92d6792a6692a5600a3b9196c8dc57909348db5b8db4b8f23b8d9568e35b8d8150095b89c6d8c57089b478b27c89a4b89a3b8986d009578897c84467878358436b8434b842668416684b6b8496a840150094b7dd6a82d707db6781e787da6b8067a802767da3b7f23b7d96a7e5667d85d009477bb737c2717b97e785677ab667836b7835b7924b78166781560093b744727623b762337447074d8074a5c742736fd676fc6a6fc5a722666fa6b7057a702767025c6fa5b009376cc7f6e37d6ca7e6ca7c6c97266d676b57d6b27c66c6769e7a69a6c66c5766a6666a56675676726a668250092f6227e6217e6406f640676217c6318c6207f6207d5bd6760d7d6097c5bc675f96c5bc575eb555b9665b9565d1725c5675c16a5b815009235a83458a3f591245902458a330085b4e46f4e46d4e2635627c4e24b4e16f54b5b4e163533735317c4e14b525704e14750d7d50a7c4e12f4ed7f4ed7d4e97c4e123008574436b4c8244426b4b87c442674a1344a0344423f49024442334612f4781446123468134606e441664492f44923440660084b3ed663ea6b3e96b3e9673e92f4097c406763e9233f0133e8660084739b6b39a6b39a6739a3f39a333b12f399663a12f398660083b35c7237a3b37a3335c70365803625c35a73275672746a2745a33a662726b31d7a31a7631a5c2725b2fb6b3025b2f95c2716b2ec70271672d95c2715b2cc60271572ad6a2aa662aa5c2712f28d6a289662895c271232794b270660083724a7e24a7c249732487e1dd671da661da56229341d96b2157d2127c1d9671f2761f1761f1341d95b1e26c1d9570082f1c1241c0241a26b1b07c1a2671a0660082317b7317a7e1797e1797c1456716b661436b159341435b14166141560081f12b6b128660081b11a380cb7310b710ca720ca700f3710c9720e1280d2710d0700c87e02d670bb6602b6b0a3760a23802b5b0935b02a6a02a5a07a6a0284a064720647003567052660326b042760325b0316a02846008170136b01066008130003f 9 11
def l_54 : Nat → Nat → Option Nat := unpackLinksF 0x41428281012202040407f4afd89fb03f417d0cf985f20bda57b02ee41da13a8674c2e699cd0390571c2dc3db8036e16d06da01b30b50b69c2d381a60b48268c2d1819c3b38066c2cd81981b2c26580ca85950326261d8c30586030a16140c20584030805e18bc01770aee05d44ba81740ae615cc0b9817112d095984b301650aca05902b2016402c235840b0056002be15592aa855502a815484a901510aa015400a7854f029455242a48149028e251c0a38145128435042a08141028015000a00140027a34e0a9b8537026c14d809b01312a6204c4097892f025e04b4496812c0a5804b00948d1d623a047028e011c0234246808c851902247448089010f1a1e0438287010d0a181430085850b021033f187e00fb09f603ec07c88f711ec13d047984f301e033c007800ef09de03bc07688ed01d813b007600e821d003a007400e231a6f34c06980d209a4034426880d1019a43302648cc90192031c46380c60986330c06180c1117472e425c80b9017202e405c80b8096c22d805a84ae395c02b805700ac115802b005584ab0154128905008a00140027464e809d0136225c84b049411261244448809009200228c448489011012184430085090a021024200830906020c041808019000200040007d18fa01f0237b46f00de01bc037806b20d601ac035806a08d401a80338c6700ce019c0320c6400c61170e2e005c00b4216802c845900ac315802b005600ac0148829005108a2014022800500096512c02580491090111082200430886010c02088410080110001f0838306e10d441a0434006040c00168c2d005a00b0216002c005420a80148429005010a0012101d383a007400d8801d0001 0xa217d6e92fa09717c94b741479e87d35847a30251901f11017a237d9423b65922a18651881d0f025a0015a0371a0b716ca3e9e07d2503f0e8259f8150d8160d0249ea719e171629232482e0c81662123a3b6fa2a6393a3ba116f9f1637b13b739376c12f619239d86f9d06d43065350372402f1701f0c0176b92f611239c46d97a4b8814b821476a92f601236a12f9b56a9a26b9116b8b9676912f5f1237a93b72137338371681f0b8178795b9a45799a568715b811577a14b719474d05b428573d84b33047990251601f1301b0b017018139827c70937320370a81796a6a97c67972669016b8a9677994b6f9475586731047960251501f098179497d94a8c9527e9417f8014793d679326692a568f96b8a1678695b7f9579196c90934308578e0157f2668f1668f23b8e35b1c832914579035b8fb4b7ea568e9564c05b420573d04b2f0472203f1b8338d8152182f8c5708b27c8cc6d8bb478aa4b8a23b8614a8986d4b04b418473c83b2e0372082f1a8238897c87835850152002f1f82f8536b8496a884678736b86b4b8626685966528672d0471e83f8401581a6980a3b82d7081e7880e7a802767f17a7f23b7e5668356a823678126b7fa3b7e96a518677d85d2c0371d82f7c18c7c2717cb737b97e7ab66791767924b7b5677a36b79b5b78966781567527176a3b762337558074a5c7747275c70742737125b722667157a70a767025c73d677346a72c5a71a6b6fa5b6e28c6e37d6ec7f6da7e6d27c6c972678256bd7d6b27c6a67a69a6c2b03767d676726a4a85a6c5676ac676945768a66682565a06b500674985b410573c04b2a047668256307d6486f640676318c65a7e6517e6397c6287f6207d400755c8156157d6097c5e9645f96c5eb55290375d1725cd675c16a5986a61d67604675f4575e1665d9565886b4e0674885b3f8573b84b280475b8155a83459924590245a23f58a334f9235112f4f1235395b5627c549732784654b5b53b735317c525705157d50a7c4805a3b04a4fd7f4f57d405754e97c4705a3f05657c6f5746d4346556a6355a4b5516f541635294b519475012f4e1234584a3e8463a83a270364c8244b87c481764a934450764a034478664717644876490244687e47814468134812f471234606e4512f449234d36b4c26b4b26749a3f48a334596644066401234097c406763f0763f0134356642a6b4216b419674112f3f9233e8663b1763a0763b12f3a12f3db6b3d26b3ca673c23f3ba333a966071263986636a71068163823b37a330601636d803625c38c723747035a730581632a5b2b92f299230501633a66048160401632d7a3227631a5c3097b27876038163016c3025b30b6b2f95c2ec702d95c2cc602bd6a2b2662aa5c29d6a291662895c2794b3556734c6a3445a3326b3125b2f16b2e1672d15b2c1572a12f2812327066028162627e25a7c251732487e2293421d7d2127c2015a202761f9761f1341e26c2456723a66232562216b209671e95b1d9571c9241c0241b07c1ba6b1aa671a0661937318a7e1817e1797c16b6615934175671636b1535b14966141561336b128660e07c10a8011a380f1800d88c10b710f3710d07c0e1280da710d07011373102720fa700e9720c87e05846050460bb6604856040460ab760927a0a238038560935b0784a0304607a6a06c7206470052660427605d6704a6b03a5b0316a0c5670b36b09b5b08a6a0825a0704a0284601b6b010669cc579bb579ab4798a5b95a4b9223b8d15b891578394b7d1477793b6f1376612f5b1235805b4d8574384b3e0473903b268371d02f198231381f1201b02017008130003f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsF fullMask g_54 bds_54 (dagRefF 328 (dagTraceF fullMask rootStock 11 f_54) l_54 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_6 : treeBlockF 192 224 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_7 : treeBlockF 224 256 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_8 : treeBlockF 256 288 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_9 : treeBlockF 288 320 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_10 : treeBlockF 320 328 (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) = true := by decide +kernel
theorem nj_54_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_54_1 h1 h2)
theorem nj_54_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_1 (fun _ h1 h2 => treeBlockF_at nb_54_2 h1 h2)
theorem nj_54_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_2 (fun _ h1 h2 => treeBlockF_at nb_54_3 h1 h2)
theorem nj_54_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_3 (fun _ h1 h2 => treeBlockF_at nb_54_4 h1 h2)
theorem nj_54_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_4 (fun _ h1 h2 => treeBlockF_at nb_54_5 h1 h2)
theorem nj_54_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_5 (fun _ h1 h2 => treeBlockF_at nb_54_6 h1 h2)
theorem nj_54_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_6 (fun _ h1 h2 => treeBlockF_at nb_54_7 h1 h2)
theorem nj_54_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_7 (fun _ h1 h2 => treeBlockF_at nb_54_8 h1 h2)
theorem nj_54_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_8 (fun _ h1 h2 => treeBlockF_at nb_54_9 h1 h2)
theorem nj_54_10 : ∀ i, 0 ≤ i → i < 328 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := block_join nj_54_9 (fun _ h1 h2 => treeBlockF_at nb_54_10 h1 h2)
theorem nc_54 : ∀ i, 0 ≤ i → i < 328 → (dagCheckNodeF fullMask g_54 bds_54 328 (dagTraceF fullMask rootStock 11 f_54) l_54) i = true := nj_54_10
theorem lb_54 : LowerBin fullMask rootStock g_54 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_54 sub_54 gl_54 rc_54 nc_54

def wg : List Gate := [⟨GateOp.and, [5, 4]⟩, ⟨GateOp.and, [5, 2]⟩, ⟨GateOp.or, [3, 1]⟩, ⟨GateOp.and, [8, 0]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.and, [13, 1]⟩, ⟨GateOp.or, [11, 2]⟩, ⟨GateOp.and, [15, 0]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.and, [12, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241312 * 2 ^ 32 + 3969951872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241312 * 2 ^ 32 + 3969951872)) (13 - 1) := by
  rw [show canon fullMask (4008241312 * 2 ^ 32 + 3969951872) = g_54 by decide]
  exact lb_54

end PEqualNP.Outside.L_meta_49031

theorem PEqualNP.Outside.L_meta_49031 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241312 * 2 ^ 32 + 3969951872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241312 * 2 ^ 32 + 3969951872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49031.table2_from_lowerBin (4008241312 * 2 ^ 32 + 3969951872) 13 PEqualNP.Outside.L_meta_49031.root_lb PEqualNP.Outside.L_meta_49031.wg 18 rfl PEqualNP.Outside.L_meta_49031.wfits PEqualNP.Outside.L_meta_49031.weval
