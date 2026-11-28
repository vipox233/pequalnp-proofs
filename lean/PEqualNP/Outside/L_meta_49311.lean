import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49311

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

theorem knownCloses_of_mem {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)} {b : Nat × List Nat × Nat × Nat}
    (hmem : b ∈ bounds) (hb : boundCloses target state b = true) :
    knownCloses target bounds state = true := by
  induction bounds with
  | nil => cases hmem
  | cons x xs ih =>
    change (boundCloses target state x || knownCloses target xs state) = true
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [hb]; rfl
    · rw [ih htl]; cases boundCloses target state x <;> rfl

theorem treeBlock_mono {lo hi : Nat} {f g : Nat → Bool}
    (hf : treeBlock lo hi f = true)
    (himp : ∀ i, lo ≤ i → i < hi → f i = true → g i = true) :
    treeBlock lo hi g = true := by
  unfold treeBlock at hf ⊢
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      (∀ i, a ≤ i → i < b → f i = true → g i = true) →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then g x else next x m && next m y
          else true) steps) a b = true from
    this (hi - lo + 1) lo hi hf himp
  intro steps
  induction steps with
  | zero => intro a b _ _; rfl
  | succ s ih =>
    intro a b h hfg
    dsimp only at h ⊢
    cases hlt : Nat.blt a b
    · rfl
    · simp only [hlt, ite_true] at h ⊢
      have hab : a < b := Nat.blt_eq.mp hlt
      cases heq : Nat.beq a ((a + b) / 2)
      · simp only [heq, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h ⊢
        exact ⟨ih a ((a + b) / 2) h.1 (fun i h1 h2 => hfg i h1 (by omega)),
               ih ((a + b) / 2) b h.2 (fun i h1 h2 => hfg i (by omega) h2)⟩
      · simp only [heq, ite_true] at h ⊢
        exact hfg a (Nat.le_refl a) hab h

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

def knownClosesTopF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match bounds with
  | [] => false
  | b0 :: rest =>
    Bool.rec
      (match rest with
       | [] => false
       | b1 :: rest1 =>
         Bool.rec
           (match rest1 with
            | [] => false
            | b2 :: _ => boundClosesF state b2)
           true (boundClosesF state b1))
      true (boundClosesF state b0)

theorem knownClosesTopF_imp {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : knownClosesTopF bounds state = true) :
    knownCloses target bounds state = true := by
  cases bounds with
  | nil => exact Bool.noConfusion h
  | cons b0 rest =>
    unfold knownClosesTopF at h; dsimp only at h
    have h0 := hgoals b0 List.mem_cons_self
    cases hb0 : boundClosesF state b0
    · rw [hb0] at h; dsimp only at h
      cases rest with
      | nil => exact Bool.noConfusion h
      | cons b1 rest1 =>
        dsimp only at h
        have h1 := hgoals b1 (List.mem_cons_of_mem _ List.mem_cons_self)
        cases hb1 : boundClosesF state b1
        · rw [hb1] at h; dsimp only at h
          cases rest1 with
          | nil => exact Bool.noConfusion h
          | cons b2 rest2 =>
            dsimp only at h
            have h2 := hgoals b2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            rw [boundClosesF_eq h2.1 h2.2] at h
            exact knownCloses_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) h
        · rw [boundClosesF_eq h1.1 h1.2] at hb1
          exact knownCloses_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) hb1
    · rw [boundClosesF_eq h0.1 h0.2] at hb0
      exact knownCloses_of_mem List.mem_cons_self hb0

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

def forceWC (w : Nat) (k : Nat → Bool × List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem forceWC_eq (w : Nat) (k : Nat → Bool × List (Nat × Nat)) : forceWC w k = k w := by
  cases w <;> rfl

def closeFallbackV4 (mask goal ep : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (st : Nat × List Nat × List (Nat × Nat × Nat)) (sp : Nat) : Bool :=
  Bool.rec true
    (Bool.rec
      (Bool.rec true false (dagPartF st.2.1 goal (Nat.xor mask goal)))
      true (knownClosesTopF bounds st))
    (Nat.beq (Nat.land ep sp) ep)

theorem closeFallbackV4_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (nd : st.2.1.Nodup) {k : Nat} (hk : k ≤ st.1)
    (hlive : LiveBin mask goal k st.2.1.toFinset) :
    closeFallbackV4 mask goal (edgePack mask goal) bounds st (orSep st.2.1) = false := by
  unfold closeFallbackV4
  have hsp : Nat.beq (Nat.land (edgePack mask goal) (orSep st.2.1)) (edgePack mask goal) = true :=
    sepPack_live hgm hlive
  have hkt : knownClosesTopF bounds st = false := by
    cases h : knownClosesTopF bounds st
    · rfl
    · have hk1 := knownClosesTopF_imp hgoals h
      have hk0 := knownCloses_sound hknown hsub nd hk hlive
      rw [hk0] at hk1; exact Bool.noConfusion hk1
  have hdp : dagPartF st.2.1 goal (Nat.xor mask goal) = true := by
    have heq : dagPartF st.2.1 goal (Nat.xor mask goal) = dagPart st.2.1 goal (mask ^^^ goal) :=
      dagPartF_eq st.2.1 goal (mask ^^^ goal)
    rw [heq]; exact dagPart_live hgm hlive
  rw [hsp, hkt, hdp]

def stepLeafV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  match cur with
  | (t, code) :: tl =>
    Bool.rec
      (closeFallbackV4 mask goal ep bounds (fuel1, z :: rest, hist1) (Nat.lor spZ baseSp), cur)
      (Bool.rec
        (match nthBound bounds (Nat.shiftRight code 1) with
         | none => (false, tl)
         | some b => (boundClosesF (fuel1, z :: rest, hist1) b, tl))
        (let dest := Nat.shiftRight code 1
         let ok := Bool.rec false
           (match states dest with
            | none => false
            | some saved => Bool.rec false (eqListN saved.2.1 (insertSortedF z rest)) (Nat.beq saved.1 fuel1))
           (Nat.blt dest count)
         (ok, tl))
        (Nat.beq (Nat.land code 1) 0))
      (Nat.beq tok t)
  | [] =>
    (closeFallbackV4 mask goal ep bounds (fuel1, z :: rest, hist1) (Nat.lor spZ baseSp), [])

theorem stepLeafV4_ref {mask goal count fuel1 z tok : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (h : (stepLeafV4 mask goal (edgePack mask goal) count bounds states fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur).1 = true) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hfb : closeFallbackV4 mask goal (edgePack mask goal) bounds (fuel1, z :: rest, hist1) (Nat.lor (sepPack z) (orSep rest)) = false :=
    closeFallbackV4_open (st := (fuel1, z :: rest, hist1)) hgm hknown hsub hgoals nd hk hlive
  unfold stepLeafV4 at h
  cases cur with
  | nil => dsimp only at h; rw [hfb] at h; exact Bool.noConfusion h
  | cons hd tl =>
    obtain ⟨t, code⟩ := hd
    dsimp only at h
    cases ht : Nat.beq tok t
    · rw [ht] at h; dsimp only at h; rw [hfb] at h; exact Bool.noConfusion h
    · rw [ht] at h; dsimp only at h
      cases hev : Nat.beq (Nat.land code 1) 0
      · rw [hev] at h; dsimp only at h
        cases hb : nthBound bounds (Nat.shiftRight code 1) with
        | none => rw [hb] at h; exact Bool.noConfusion h
        | some b =>
          rw [hb] at h; dsimp only at h
          have hmem := nthBound_mem hb
          have hg := hgoals b hmem
          rw [boundClosesF_eq hg.1 hg.2] at h
          have h0 := boundCloses_sound (state := (fuel1, z :: rest, hist1)) (hknown b hmem) (hsub b hmem) nd hk hlive
          rw [h0] at h; exact Bool.noConfusion h
      · rw [hev] at h; dsimp only at h
        cases hlt : Nat.blt (Nat.shiftRight code 1) count
        · rw [hlt] at h; exact Bool.noConfusion h
        · rw [hlt] at h; dsimp only at h
          cases hst : states (Nat.shiftRight code 1) with
          | none => rw [hst] at h; exact Bool.noConfusion h
          | some saved =>
            rw [hst] at h; dsimp only at h
            cases hf : Nat.beq saved.1 fuel1
            · rw [hf] at h; exact Bool.noConfusion h
            · rw [hf] at h; dsimp only at h
              rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at h
              exact ⟨Nat.shiftRight code 1, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, h⟩

def checkKeepsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  let (ok0, c1) : Bool × List (Nat × Nat) := Bool.rec
    (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur)
    (true, cur) (Nat.blt fuel (Nat.sub n 1))
  Bool.rec (false, c1)
    (let (ok1, c2) : Bool × List (Nat × Nat) := Bool.rec
       (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1)
       (true, c1) (Nat.blt fuel n)
     Bool.rec (false, c2)
       (let (ok2, c3) : Bool × List (Nat × Nat) := Bool.rec
          (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2)
          (true, c2) (Nat.blt fuel n)
        Bool.rec (false, c3)
          (Bool.rec
            (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3)
            (true, c3) (Nat.blt fuel (Nat.add n 1)))
          ok2)
       ok1)
    ok0

theorem checkKeepsV4_at {mask goal ep count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (h : (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur).1 = true)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c).1 = true
    | true, false => Nat.blt fuel n = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c).1 = true
    | false, true => Nat.blt fuel n = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c).1 = true
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c).1 = true := by
  unfold checkKeepsV4 at h
  generalize hp0 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur)
    (true, cur) (Nat.blt fuel (Nat.sub n 1)) : Bool × List (Nat × Nat)) = p0 at h
  obtain ⟨ok0, c1⟩ := p0
  dsimp only at h
  cases ok0
  · exact Bool.noConfusion h
  · dsimp only at h
    generalize hp1 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1)
      (true, c1) (Nat.blt fuel n) : Bool × List (Nat × Nat)) = p1 at h
    obtain ⟨ok1, c2⟩ := p1
    dsimp only at h
    cases ok1
    · exact Bool.noConfusion h
    · dsimp only at h
      generalize hp2 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2)
        (true, c2) (Nat.blt fuel n) : Bool × List (Nat × Nat)) = p2 at h
      obtain ⟨ok2, c3⟩ := p2
      dsimp only at h
      cases ok2
      · exact Bool.noConfusion h
      · dsimp only at h
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, congrArg Prod.fst hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, congrArg Prod.fst hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, congrArg Prod.fst hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at h; exact Or.inr ⟨c3, h⟩
          · exact Or.inl rfl

def checkOpV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  forceWC (canonF mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWC (sepPack z) (fun spZ =>
          checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur))
        (true, cur) (memN z ws0))
      (true, cur) (Nat.beq z 0))

def check4OpsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  let (o0, c1) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur
  Bool.rec (false, c1)
    (let (o1, c2) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1
     Bool.rec (false, c2)
       (let (o2, c3) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2
        Bool.rec (false, c3)
          (checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3) o2) o1) o0

theorem check4OpsV4_at {mask goal ep count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (hop : op < 4)
    (h : (check4OpsV4 mask goal ep count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur).1 = true) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c, (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z (sepPack z) spAll spNoA spNoB spNoAB
        ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c).1 = true := by
  unfold check4OpsV4 at h
  generalize hp0 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur = p0 at h
  obtain ⟨o0, c1⟩ := p0; dsimp only at h
  cases o0
  · exact Bool.noConfusion h
  · dsimp only at h
    generalize hp1 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 = p1 at h
    obtain ⟨o1, c2⟩ := p1; dsimp only at h
    cases o1
    · exact Bool.noConfusion h
    · dsimp only at h
      generalize hp2 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 = p2 at h
      obtain ⟨o2, c3⟩ := p2; dsimp only at h
      cases o2
      · exact Bool.noConfusion h
      · dsimp only at h
        have extract (rawZ op' : Nat) (c0 : List (Nat × Nat))
            (hz : canon mask rawZ = binOp mask op' x y)
            (hok : (checkOpV4 mask goal ep count bounds states fuel fuel1 n x y rawZ op' spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0).1 = true) :
            binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
              ∃ c, (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n (binOp mask op' x y) (sepPack (binOp mask op' x y))
                spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c).1 = true := by
          unfold checkOpV4 at hok
          rw [forceWC_eq, canonF_eq, hz] at hok
          cases h0 : Nat.beq (binOp mask op' x y) 0
          · rw [h0] at hok; dsimp only at hok
            cases hm : memN (binOp mask op' x y) ws0
            · rw [hm] at hok; dsimp only at hok
              rw [forceWC_eq] at hok
              exact Or.inr (Or.inr ⟨c0, hok⟩)
            · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
          · exact Or.inl (Nat.beq_eq.mp h0)
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur rfl (congrArg Prod.fst hp0)
        · exact extract _ 1 c1 rfl (congrArg Prod.fst hp1)
        · exact extract _ 2 c2 rfl (congrArg Prod.fst hp2)
        · exact extract _ 3 c3 rfl h

def loopB_V4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, b, cur =>
    let y := getDN ws0 b
    let wsNoB := dropValF true y ws0
    let wsNoAB := dropValF true y wsNoA
    forceWC (orSepSkip y ps) (fun spNoB =>
      forceWC (orSepSkip2 x y ps) (fun spNoAB =>
        let tokAB := Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2
        let (ok, cur1) := check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur
        Bool.rec (false, cur1) (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1) ok))

theorem loopB_V4_at {mask goal ep count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b : Nat} {cur : List (Nat × Nat)}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (h : (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur).1 = true) :
    let y := getDN ws0 b
    ∃ c, (check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c).1 = true := by
  induction rem generalizing b0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopB_V4 at h; dsimp only at h
    rw [forceWC_eq, forceWC_eq] at h
    cases hp : check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : b = b0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) h

def loopA_V4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, a, cur =>
    let x := getDN ws0 a
    let wsNoA := dropValF true x ws0
    forceWC (Nat.xor mask x) (fun nx =>
      forceWC (orSepSkip x ps) (fun spNoA =>
        let (ok, cur1) := loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur
        Bool.rec (false, cur1) (loopA_V4 mask goal ep count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1) ok))

theorem loopA_V4_at {mask goal ep count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a : Nat} {cur : List (Nat × Nat)}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (h : (loopA_V4 mask goal ep count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur).1 = true) :
    let x := getDN ws0 a
    ∃ c, (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c).1 = true := by
  induction rem generalizing a0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopA_V4 at h; dsimp only at h
    rw [forceWC_eq, forceWC_eq] at h
    cases hp : loopB_V4 mask goal ep count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : a = a0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) h

def dagCheckNodeV4 (mask goal ep : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      let n := lenN ws0
      Bool.rec
        (Bool.rec
          (Bool.rec false
            (forceSepPairs ws0 (fun ps =>
              forceW (orSepAll ps) (fun spAll =>
                (loopA_V4 mask goal ep count bounds states fuel (Nat.sub fuel 1) n spAll ws0 ps hist n 0 (cursors (Nat.add i 1))).1)))
            (Nat.blt n 17))
          true (Nat.beq fuel 0))
        false (memN goal ws0))

def stepRootV4 (mask goal ep count fuel : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  Bool.rec
    (match cur with
     | (t, code) :: tl =>
       Bool.rec
         (closeFallbackV4 mask goal ep bounds (fuel, ws, []) (orSep ws), cur)
         (Bool.rec
           (match nthBound bounds (Nat.shiftRight code 1) with
            | none => (false, tl)
            | some b => (boundClosesF (fuel, ws, []) b, tl))
           (let dest := Nat.shiftRight code 1
            let ok := Bool.rec false
              (match states dest with
               | none => false
               | some saved => Bool.rec false (eqListN saved.2.1 ws) (Nat.beq saved.1 fuel))
              (Nat.blt dest count)
            (ok, tl))
           (Nat.beq (Nat.land code 1) 0))
         (Nat.beq tok t)
     | [] =>
       (closeFallbackV4 mask goal ep bounds (fuel, ws, []) (orSep ws), []))
    (true, cur) (Nat.blt (Nat.add fuel 1) (lenN ws))

def loopRootsV4 (mask goal ep count fuel : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, tok, cur =>
    let ws := subsetWordsF stock tok
    let (ok, cur1) := stepRootV4 mask goal ep count fuel bounds states ws tok cur
    Bool.rec (false, cur1) (loopRootsV4 mask goal ep count fuel bounds states stock rem (Nat.add tok 1) cur1) ok

def dagCheckRootsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (stock : List Nat) (fuel : Nat) : Bool :=
  (loopRootsV4 mask goal ep count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur).1

theorem loopRootsV4_at {mask goal ep count fuel : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok : Nat} {cur : List (Nat × Nat)}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (h : (loopRootsV4 mask goal ep count fuel bounds states stock rem t0 cur).1 = true) :
    ∃ c, (stepRootV4 mask goal ep count fuel bounds states (subsetWordsF stock tok) tok c).1 = true := by
  induction rem generalizing t0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV4 at h; dsimp only at h
    cases hp : stepRootV4 mask goal ep count fuel bounds states (subsetWordsF stock t0) t0 cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : tok = t0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) h

theorem dagAllNodesV4 {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV4 mask goal (edgePack mask goal) bounds count
      (dagTrace mask stock fuel forest) cursors i = true) :
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
    unfold dagCheckNodeV4 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, lenN_eq, memN_eq] at hchk
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
          rw [forceSepPairs_eq, forceW_eq] at hchk
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
          obtain ⟨cA, hB⟩ := loopA_V4_at (a := a) (Nat.zero_le a) (by omega) hchk
          obtain ⟨cB, hO⟩ := loopB_V4_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
          simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
          set x := ws.getD a 0
          set y := ws.getD b 0
          set z := binOp mask op x y
          have hznz : z ≠ 0 := hzeq.symm ▸ hz0
          have hznm : ws.contains z = false := by
            cases h : ws.contains z
            · rfl
            · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
          rcases check4OpsV4_at hop_lt hO with hz' | hcm | ⟨cK, hK⟩
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
            have hka := checkKeepsV4_at hK keepA keepB
            have finish {tok' : Nat} {c' : List (Nat × Nat)}
                (hstep : (stepLeafV4 mask goal (edgePack mask goal) count bounds (dagTrace mask stock fuel forest)
                  (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c').1 = true) : False := by
              obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                stepLeafV4_ref hgm hknown hsub hgoals hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
              exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
            cases keepA <;> cases keepB
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
              · rw [hdropComm] at hst
                exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
              · exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
              · exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
              · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk

theorem lowerDagV4 {mask goal ep fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hep : ep = edgePack mask goal)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsV4 mask goal ep count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV4 mask goal ep bounds count
      (dagTraceF mask stock fuel forest) cursors i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  subst hep
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
  unfold dagCheckRootsV4 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  obtain ⟨c, hsr⟩ := loopRootsV4_at (tok := tok) (Nat.zero_le tok) (by omega) hroots
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
  have hfb := closeFallbackV4_open (st := (fuel, subsetWords stock tok, [])) hgm hknown hsub hgoals hnd (k := k) (by omega) hlive'
  unfold stepRootV4 at hsr
  rw [hnw] at hsr; dsimp only at hsr
  cases c with
  | nil => dsimp only at hsr; rw [hfb] at hsr; exact Bool.noConfusion hsr
  | cons hd tl =>
    obtain ⟨t, code⟩ := hd
    dsimp only at hsr
    cases ht : Nat.beq tok t
    · rw [ht] at hsr; dsimp only at hsr; rw [hfb] at hsr; exact Bool.noConfusion hsr
    · rw [ht] at hsr; dsimp only at hsr
      cases hev : Nat.beq (Nat.land code 1) 0
      · rw [hev] at hsr; dsimp only at hsr
        cases hb : nthBound bounds (Nat.shiftRight code 1) with
        | none => rw [hb] at hsr; exact Bool.noConfusion hsr
        | some b =>
          rw [hb] at hsr; dsimp only at hsr
          have hmem := nthBound_mem hb
          have hg := hgoals b hmem
          rw [boundClosesF_eq hg.1 hg.2] at hsr
          have h0 := boundCloses_sound (state := (fuel, subsetWords stock tok, [])) (hknown b hmem) (hsub b hmem) hnd (k := k) (by omega) hlive'
          rw [h0] at hsr; exact Bool.noConfusion hsr
      · rw [hev] at hsr; dsimp only at hsr
        cases hltc : Nat.blt (Nat.shiftRight code 1) count
        · rw [hltc] at hsr; exact Bool.noConfusion hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest (Nat.shiftRight code 1) with
          | none => rw [htr2] at hsr; exact Bool.noConfusion hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; exact Bool.noConfusion hsr
            · rw [hf] at hsr; dsimp only at hsr
              rw [eqListN_eq, beq_iff_eq] at hsr
              exact dagAllNodesV4 hgm hknown hsub hgoals snd hnodes fuel (Nat.shiftRight code 1) saved
                (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (hsr ▸ hlive')

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    let code := Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask
    unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc)

def unpackCursorV4 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    let entry := Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask
    let sz := Nat.land entry sizeMask
    let off := Nat.shiftRight entry sizeBits
    unpackListAux data off w wMask tokBits tokMask sz []

def m_0 : Nat := 0xf000f0000000000
def s_0 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_0 : Nat := 0x100070000000000
def ep_0 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
theorem epk_0 : ep_0 = edgePack m_0 g_0 := by decide +kernel
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_0] at hb
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV4 m_0 g_0 ep_0 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 (dagCheckNodeV4 m_0 g_0 ep_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0) = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_0 g_0 ep_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0) i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_0 kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0xf000f000000000
def s_1 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_1 : Nat := 0x10007000000000
def ep_1 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
theorem epk_1 : ep_1 = edgePack m_1 g_1 := by decide +kernel
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_1] at hb
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV4 m_1 g_1 ep_1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 (dagCheckNodeV4 m_1 g_1 ep_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1) = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_1 g_1 ep_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1) i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_1 kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0x3300330000000000
def s_2 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_2 : Nat := 0x100130000000000
def ep_2 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
theorem epk_2 : ep_2 = edgePack m_2 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_2] at hb
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV4 m_2 g_2 ep_2 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 (dagCheckNodeV4 m_2 g_2 ep_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2) = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_2 g_2 ep_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2) i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_2 kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0x5500550000000000
def s_3 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_3 : Nat := 0x100150000000000
def ep_3 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
theorem epk_3 : ep_3 = edgePack m_3 g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_3] at hb
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV4 m_3 g_3 ep_3 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 (dagCheckNodeV4 m_3 g_3 ep_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3) = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_3 g_3 ep_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3) i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_3 kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0xff000000
def s_4 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_4 : Nat := 0x17000000
def ep_4 : Nat := 0x600000000000000120000000000000014000000
theorem epk_4 : ep_4 = edgePack m_4 g_4 := by decide +kernel
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_4] at hb
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV4 m_4 g_4 ep_4 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 (dagCheckNodeV4 m_4 g_4 ep_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4) = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_4 g_4 ep_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4) i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_4 kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0x2222222200000000
def s_5 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_5 : Nat := 0x2022200000000
def ep_5 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
theorem epk_5 : ep_5 = edgePack m_5 g_5 := by decide +kernel
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV4 m_5 g_5 ep_5 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 (dagCheckNodeV4 m_5 g_5 ep_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5) = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_5 g_5 ep_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5) i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_5 kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x4444444400000000
def s_6 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_6 : Nat := 0x4044400000000
def ep_6 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
theorem epk_6 : ep_6 = edgePack m_6 g_6 := by decide +kernel
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_6] at hb
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV4 m_6 g_6 ep_6 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 (dagCheckNodeV4 m_6 g_6 ep_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6) = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_6 g_6 ep_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6) i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_6 kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0x5050505000000000
def s_7 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_7 : Nat := 0x10105000000000
def ep_7 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
theorem epk_7 : ep_7 = edgePack m_7 g_7 := by decide +kernel
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_7] at hb
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV4 m_7 g_7 ep_7 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 (dagCheckNodeV4 m_7 g_7 ep_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7) = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_7 g_7 ep_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7) i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_7 kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x3030303000000000
def s_8 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_8 : Nat := 0x10103000000000
def ep_8 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
theorem epk_8 : ep_8 = edgePack m_8 g_8 := by decide +kernel
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV4 m_8 g_8 ep_8 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 (dagCheckNodeV4 m_8 g_8 ep_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8) = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_8 g_8 ep_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8) i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_8 kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0xa000a000a000a00
def s_9 : List Nat := [0x200020002000200, 0xa0000000a00, 0xa000a00]
def g_9 : Nat := 0x20002000a00
def ep_9 : Nat := 0x200080000000200000008000000000000000000000000000000000000000200020000000000000000000000
theorem epk_9 : ep_9 = edgePack m_9 g_9 := by decide +kernel
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV4 m_9 g_9 ep_9 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9) = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9) i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_9 kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0xc000c000c000c00
def s_10 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_10 : Nat := 0x40004000c00
def ep_10 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
theorem epk_10 : ep_10 = edgePack m_10 g_10 := by decide +kernel
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV4 m_10 g_10 ep_10 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 (dagCheckNodeV4 m_10 g_10 ep_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10) = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_10 g_10 ep_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10) i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_10 kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0x3333000000000000
def s_11 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_11 : Nat := 0x113000000000000
def ep_11 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
theorem epk_11 : ep_11 = edgePack m_11 g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV4 m_11 g_11 ep_11 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 (dagCheckNodeV4 m_11 g_11 ep_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11) = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_11 g_11 ep_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11) i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_11 kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0x5555000000000000
def s_12 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_12 : Nat := 0x115000000000000
def ep_12 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
theorem epk_12 : ep_12 = edgePack m_12 g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV4 m_12 g_12 ep_12 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 (dagCheckNodeV4 m_12 g_12 ep_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12) = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_12 g_12 ep_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12) i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_12 kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xff000000000000
def s_13 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_13 : Nat := 0x17000000000000
def ep_13 : Nat := 0x600000000000000120000000000000014000000000000
theorem epk_13 : ep_13 = edgePack m_13 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_13 : KnownBin bds_13 := by intro b hb; simp [bds_13] at hb
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp [bds_13] at hb
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_13] at hb
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV4 m_13 g_13 ep_13 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 (dagCheckNodeV4 m_13 g_13 ep_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13) = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_13 g_13 ep_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13) i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_13 kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xc000c000c000c0
def s_14 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_14 : Nat := 0x40004000c0
def ep_14 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
theorem epk_14 : ep_14 = edgePack m_14 g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14) = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14) i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xf0f000000000000
def s_15 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_15 : Nat := 0x107000000000000
def ep_15 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
theorem epk_15 : ep_15 = edgePack m_15 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15) = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15) i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0x5500000055000000
def s_16 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_16 : Nat := 0x100000015000000
def ep_16 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
theorem epk_16 : ep_16 = edgePack m_16 g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_16 : KnownBin bds_16 := by intro b hb; simp [bds_16] at hb
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp [bds_16] at hb
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_16] at hb
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 (dagCheckNodeV4 m_16 g_16 ep_16 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16) = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_16 g_16 ep_16 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16) i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x3300000033000000
def s_17 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_17 : Nat := 0x100000013000000
def ep_17 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
theorem epk_17 : ep_17 = edgePack m_17 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17) = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17) i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xf0000000f000000
def s_18 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_18 : Nat := 0x100000007000000
def ep_18 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
theorem epk_18 : ep_18 = edgePack m_18 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18) = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18) i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xf0f000000000
def s_19 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_19 : Nat := 0x107000000000
def ep_19 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
theorem epk_19 : ep_19 = edgePack m_19 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_19 : KnownBin bds_19 := by intro b hb; simp [bds_19] at hb
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp [bds_19] at hb
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_19] at hb
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19) = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19) i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xff0000000000
def s_20 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_20 : Nat := 0x170000000000
def ep_20 : Nat := 0x6000000000000001200000000000000140000000000
theorem epk_20 : ep_20 = edgePack m_20 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_20 : KnownBin bds_20 := by intro b hb; simp [bds_20] at hb
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp [bds_20] at hb
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_20] at hb
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20) = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20) i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0x4444000044440000
def s_21 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_21 : Nat := 0x4000004440000
def ep_21 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
theorem epk_21 : ep_21 = edgePack m_21 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_21 : KnownBin bds_21 := by intro b hb; simp [bds_21] at hb
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp [bds_21] at hb
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_21] at hb
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 1 bds_21 (dagTraceF m_21 s_21 3 f_21) (cur_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 1 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21) = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21) i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0x5050000050500000
def s_22 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_22 : Nat := 0x10000010500000
def ep_22 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by intro b hb; simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_22] at hb
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 1 bds_22 (dagTraceF m_22 s_22 3 f_22) (cur_22 0) s_22 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 1 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22) = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22) i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0x2222888822228888
def s_23 : List Nat := [0x888800008888, 0x202080802020808, 0x22008800220088, 0x22228888]
def g_23 : Nat := 0x2000002020888
def ep_23 : Nat := 0x200088800000000000000000002000000000080000200000202080000000000000000000000000000000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV4 0xcc61 0x92e52200f 4 15 2 3 9 511 12 4095
def f_23 : Nat → Nat × Nat := unpackForestF 0x32ec880f 1 9
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 3 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 3 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 3 (dagTraceF m_23 s_23 4 f_23) cur_23) = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 3 (dagTraceF m_23 s_23 4 f_23) cur_23) i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xa0aa0a00a0aa0a0
def s_24 : List Nat := [0x202202002022020, 0xa0a00000a0a0, 0xa00a0000a00a0, 0xa0aa0a0]
def g_24 : Nat := 0x20020020200a0
def ep_24 : Nat := 0x2000080000000000000000000020020000000a0000000000000000000020020020200000000000000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_24 : KnownBin bds_24 := by intro b hb; simp [bds_24] at hb
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp [bds_24] at hb
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_24] at hb
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV4 0xcc61 0x99510f 4 15 2 3 5 31 8 255
def f_24 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 3 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) s_24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 3 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 3 (dagTraceF m_24 s_24 4 f_24) cur_24) = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 3 (dagTraceF m_24 s_24 4 f_24) cur_24) i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xff00ff0000000000
def s_25 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_25 : Nat := 0x100170000000000
def ep_25 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_20, s_20, 4, g_20), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_20
  · exact lb_3
  · exact lb_2
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xffff000000000000
def s_26 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_26 : Nat := 0x117000000000000
def ep_26 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_13, s_13, 4, g_13), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_13
  · exact lb_12
  · exact lb_11
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 43 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) s_26 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 43 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26) = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26) i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xffff00000000
def s_27 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_27 : Nat := 0x177700000000
def ep_27 : Nat := 0x6000000000000006000000000000001222000000000000144400000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f0f0f000000000
def s_28 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_28 : Nat := 0x10107000000000
def ep_28 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_19, s_19, 4, g_19), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_19
  · exact lb_7
  · exact lb_8
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28) = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28) i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xcccccccc00000000
def s_29 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_29 : Nat := 0x4044400000000
def ep_29 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0x3333333300000000
def s_30 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_30 : Nat := 0x113133300000000
def ep_30 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_11, s_11, 4, g_11), (m_8, s_8, 4, g_8), (m_5, s_5, 4, g_5)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_11
  · exact lb_8
  · exact lb_5
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 43 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 43 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xaa00aa00aa00aa
def s_31 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_31 : Nat := 0x20022000200aa
def ep_31 : Nat := 0x8800000020000000a80000000000000000000200000002000000020022000200000000000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_31 : KnownBin bds_31 := by intro b hb; simp [bds_31] at hb
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp [bds_31] at hb
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_31] at hb
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_31 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 1 bds_31 (dagTraceF m_31 s_31 3 f_31) (cur_31 0) s_31 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 1 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 1 (dagTraceF m_31 s_31 3 f_31) cur_31) = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 1 (dagTraceF m_31 s_31 3 f_31) cur_31) i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xaaaaaaaa00000000
def s_32 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_32 : Nat := 0x2022200000000
def ep_32 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0x5555555500000000
def s_33 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_33 : Nat := 0x115155500000000
def ep_33 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_12, s_12, 4, g_12), (m_7, s_7, 4, g_7), (m_6, s_6, 4, g_6)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_12
  · exact lb_7
  · exact lb_6
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xc0c0c0c0c0c0c0c0
def s_34 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_34 : Nat := 0x40004000c0
def ep_34 : Nat := 0x400080000000400000008000000040004000c0000000000000000000000000000000000000004000400000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0x5555000055550000
def s_35 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_35 : Nat := 0x115000015550000
def ep_35 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_16, s_16, 4, g_16), (m_22, s_22, 4, g_22), (m_21, s_21, 4, g_21)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_16
  · exact lb_22
  · exact lb_21
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 43 bds_35 (dagTraceF m_35 s_35 6 f_35) (cur_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xf0f00000f0f0
def s_36 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_36 : Nat := 0x1070000010f0
def ep_36 : Nat := 0x80000000000000000000000060000000e0000000000000000000001020000010000000104000001000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xcccc0000cccc0000
def s_37 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_37 : Nat := 0x4000004440000
def ep_37 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_21
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xaa00aa00aa00aa00
def s_38 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_38 : Nat := 0x20002000a00
def ep_38 : Nat := 0x2000800000002000000080000000000000000000000020002000a0000000200020000000000000000000000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xcc00cc00cc00cc00
def s_39 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_39 : Nat := 0x40004000c00
def ep_39 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xf000f000f000f00
def s_40 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_40 : Nat := 0x100070007000f00
def ep_40 : Nat := 0x600080000000600000008000000000000000000000000000000000001000200020000000100040004000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_18, s_18, 4, g_18), (m_10, s_10, 4, g_10), (m_9, s_9, 4, g_9)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_18
  · exact lb_10
  · exact lb_9
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_40_1 (Nat.sub p 32)) (cc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 43 bds_40 (dagTraceF m_40 s_40 6 f_40) (cur_40 0) s_40 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 43 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xcc00cc00cc00cc
def s_41 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_41 : Nat := 0x40044004400cc
def ep_41 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xffff0000
def s_42 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_42 : Nat := 0x17570000
def ep_42 : Nat := 0x400000000000000602000000000000120200000000000014540000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xff00ff00
def s_43 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_43 : Nat := 0x17001f00
def ep_43 : Nat := 0x80000000000000000000000000006000e0000000000120010000000000014001000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xaaaaaaaa
def s_44 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_44 : Nat := 0x2020aaa
def ep_44 : Nat := 0x8a800000000000000a00000000002020a0000000000020200000000000000000000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_44 : KnownBin bds_44 := by intro b hb; simp [bds_44] at hb
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp [bds_44] at hb
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_44] at hb
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_44 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 1 bds_44 (dagTraceF m_44 s_44 3 f_44) (cur_44 0) s_44 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 1 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1 (dagTraceF m_44 s_44 3 f_44) cur_44) = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1 (dagTraceF m_44 s_44 3 f_44) cur_44) i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xff000000ff000000
def s_45 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_45 : Nat := 0x100000017000000
def ep_45 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18), (m_4, s_4, 4, g_4), (m_16, s_16, 4, g_16), (m_17, s_17, 4, g_17)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_4
  · exact lb_16
  · exact lb_17
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_45_1 (Nat.sub p 32)) (cc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 43 bds_45 (dagTraceF m_45 s_45 6 f_45) (cur_45 0) s_45 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 43 (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45) = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45) i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xff000000ff0000
def s_46 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_46 : Nat := 0x17000000570000
def ep_46 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xf0f00000f0f0000
def s_47 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_47 : Nat := 0x107000007070000
def ep_47 : Nat := 0x600000000000000000000000006000000000000000000000000000001020000020200000104000004040000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0x4444444444444444
def s_48 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_48 : Nat := 0x4044404440444
def ep_48 : Nat := 0x440000000000440000000000004004000400040000404000400040000000000000000000000000000000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xa0a0a0a0a0a0a0a
def s_49 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_49 : Nat := 0x2020202020a0a
def ep_49 : Nat := 0x200080800000200000008080002000000000000000000000000000000020202020200000000000000000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xc0c0c0c0c0c0c0c
def s_50 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_50 : Nat := 0x4040404040c0c
def ep_50 : Nat := 0x400080800000400000008080004000000000000000000000000000000000000000000000004040404040000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xaaaaaaaaaaaaaaaa
def s_51 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_51 : Nat := 0x2022202020aaa
def ep_51 : Nat := 0x200088800000220000008a800020020000000a00002020002020a0000020222020200000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 5, g_32), (m_44, s_44, 4, g_44), (m_38, s_38, 5, g_38), (m_5, s_5, 4, g_5), (m_31, s_31, 4, g_31), (m_49, s_49, 5, g_49), (m_24, s_24, 5, g_24), (m_9, s_9, 4, g_9), (m_23, s_23, 5, g_23)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_44
  · exact lb_38
  · exact lb_5
  · exact lb_31
  · exact lb_49
  · exact lb_24
  · exact lb_9
  · exact lb_23
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_51_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x832d0409e0a3b827700ee01d22b4976882d10176b2e425c80b901663265a4c8081610009b143600690cb0895c12b8043508600c911804213c0300001 0xb1782c5d12d347b4916d144b410a9682a590e9582a510e9182a450a8e84a361253601497c5144941124a429210613418450a8e04a340f1788c5d16d35d34916d155341129342a49129142a410e56839590e55889510e51839450e17438550613418451651190140ed259341225343945060443c596d1448a5d0e9683a560e954395e22575a14e1652859461a508293e124e849360a4c8392e0e4b4181d0e068881606055801406111635e0ed683b5654d485b4e1ad347a4d169144a3d0a8e44a350a8c4594a1652459461a5045936164d4292e0a488183d060d43944444d05b4e44d08693d164d4292e124885c5e4d1486a4d169285a46169142a3e0a8c9215e0e56839561a548594e1a534293e1a4f4293c124e849361a4d501340a4c8592e164b4181d060544b5e0ad484b4e0ad082a3e0a8f44a350a8c8e15e0e568395612548794e125285946125082936124d4292e0a4b4283d120d4181d06054182412d783b5a0ed58c35212d385b4a12d187b420a9284a46128f82a3d0a4f8293d0a4b849290a4882921060f41835129302a40061303b5e06d683b5606d481a3d0a8e44a35068c4193d284e49135064c41856061181836060b8181e060901b5e0ed681b560ed481b4e16d281b461ed082a4a12918713d064e41935184c449290a4841856060f8182e06078395e06568395606548414e06528594606508293e064e84936064c8185e0613818360609818160a4f04934069783a5a069583a52069385a4a069182242068f84a3a068d82a3206158182e060785b4f0ed2c3b4784d0de24f0a92c3a470a90c7a3f0a8ec5a370a8cdc14f0e52c39475c50d413f164ec59373c4cc292f344acb1270a48c384f0e11c803f160dc282f1409c301f0405c001f 15 32767 6 63 11 2047 18 262143
def cc_51_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x46078a17020002 0x5b500ed004a3c0a8c0183c171743c5a0f1583c550ed785b5d0ed383b4d0a9642a511e9345a45128f42a39128d42a310e565b151165253141544f63139884d469310e1743855060f418350e930184c 11 2047 5 31 11 2047 18 262143
def cur_51 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_51_1 (Nat.sub p 32)) (cc_51_0 p) (Nat.blt p 32)
def f_51 : Nat → Nat × Nat := unpackForestF 0x889cc44d41686f9497ca28293dd692094f6228b05399682c01404a1aad7956a4093f4229205791684813404999c578125663520493924e4926a083f189e8c4c4104e214e040f84908102e001f 6 11
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 36 bds_51 (dagTraceF m_51 s_51 7 f_51) (cur_51 0) s_51 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 36 (dagTraceF m_51 s_51 7 f_51) cur_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 36 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 36 (dagTraceF m_51 s_51 7 f_51) cur_51) = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 36 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 36 (dagTraceF m_51 s_51 7 f_51) cur_51) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 36 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 36 (dagTraceF m_51 s_51 7 f_51) cur_51) i = true := nj_51_1
theorem lb_51 : LowerBin m_51 s_51 g_51 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0x5555555555555555
def s_52 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_52 : Nat := 0x115155515551555
def ep_52 : Nat := 0x1440000000001440000000000014004000400040010404000400040001101000100010000000000000000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_35
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 7 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0x3333333333333333
def s_53 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_53 : Nat := 0x113133313131333
def ep_53 : Nat := 0x1200000000001220000000200012002000000020010202000202020000000000000000000110100010101000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 7, g_30)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_30
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) s_53 7 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 7 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xcccccccccccccccc
def s_54 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_54 : Nat := 0x4044404440ccc
def ep_54 : Nat := 0x4400888000004400000088800040040004000c00004040004000c0000000000000000000004044404440000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_37, s_37, 5, g_37), (m_29, s_29, 5, g_29), (m_48, s_48, 5, g_48), (m_39, s_39, 5, g_39), (m_41, s_41, 5, g_41), (m_34, s_34, 5, g_34), (m_50, s_50, 5, g_50), (m_6, s_6, 4, g_6), (m_21, s_21, 4, g_21)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_37
  · exact lb_29
  · exact lb_48
  · exact lb_39
  · exact lb_41
  · exact lb_34
  · exact lb_50
  · exact lb_6
  · exact lb_21
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV4 0x851060001 0x1f2f165a2cacf949727364a6c8cb908f1f263a4c6c78c8aab0d2e18b4515860cb74f2e965d1d7a1a64f2c96591cf21a63f3c7698dcf19c54f2a8eb4fda9b9d2f4a4ef13c62594471886b0fc61db437186670bc615a4271846306c40b801f 12 4095 6 63 10 1023 15 32767
def f_54 : Nat → Nat × Nat := unpackForestF 0xddf 1 5
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 2 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) s_54 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 2 (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 2 (dagTraceF m_54 s_54 7 f_54) cur_54) = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 2 → (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 2 (dagTraceF m_54 s_54 7 f_54) cur_54) i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xf0f0f0f0f0f0f0f
def s_55 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_55 : Nat := 0x107070707070f0f
def ep_55 : Nat := 0x600080800000600000008080006000000000000000000000000000001020202020200000104040404040000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_40
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) s_55 7 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 7 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def g_56 : Nat := 0x117177717571fff
def ep_56 : Nat := 0x1640088800001660000008a800160060004000e00106060006020e0001121222120210000114144414541000
theorem epk_56 : ep_56 = edgePack fullMask g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 7, g_26), (m_25, s_25, 7, g_25), (m_55, s_55, 8, g_55), (m_28, s_28, 7, g_28), (m_53, s_53, 8, g_53), (m_54, s_54, 8, g_54), (m_52, s_52, 8, g_52), (m_51, s_51, 8, g_51), (m_35, s_35, 7, g_35), (m_40, s_40, 7, g_40), (m_41, s_41, 5, g_41), (m_36, s_36, 5, g_36), (m_45, s_45, 7, g_45), (m_33, s_33, 7, g_33), (m_30, s_30, 7, g_30), (m_43, s_43, 5, g_43), (m_14, s_14, 4, g_14), (m_46, s_46, 5, g_46), (m_29, s_29, 5, g_29), (m_16, s_16, 4, g_16), (m_22, s_22, 4, g_22), (m_27, s_27, 5, g_27), (m_13, s_13, 4, g_13), (m_17, s_17, 4, g_17), (m_44, s_44, 4, g_44), (m_37, s_37, 5, g_37), (m_39, s_39, 5, g_39), (m_6, s_6, 4, g_6), (m_42, s_42, 5, g_42), (m_4, s_4, 4, g_4), (m_32, s_32, 5, g_32), (m_11, s_11, 4, g_11), (m_47, s_47, 5, g_47)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_25
  · exact lb_55
  · exact lb_28
  · exact lb_53
  · exact lb_54
  · exact lb_52
  · exact lb_51
  · exact lb_35
  · exact lb_40
  · exact lb_41
  · exact lb_36
  · exact lb_45
  · exact lb_33
  · exact lb_30
  · exact lb_43
  · exact lb_14
  · exact lb_46
  · exact lb_29
  · exact lb_16
  · exact lb_22
  · exact lb_27
  · exact lb_13
  · exact lb_17
  · exact lb_44
  · exact lb_37
  · exact lb_39
  · exact lb_6
  · exact lb_42
  · exact lb_4
  · exact lb_32
  · exact lb_11
  · exact lb_47
theorem sub_56 : ∀ b ∈ bds_56, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8e10a21ad8389dfa2876111c1ad6b4a599285dd1174065a45952ad53a21392b48cb100463b0a0d52e2ead4b7072968ca1882408c8d0621c30762215704402b0ba8c1ea0002f00001 0x9cfe05e7b0273b8179cc05afe07d7e016bd80b5e805aee06d76016b980b5c805ade03d6e016b680b1fc058f602c770163980b1ac078d402c690163380b198058c602c610162b80b158058aa09b7f00dbd822ddc036e605b6f00db5812d9c036c602b5f015ae806d6c036b202b5704daa806d4c036a202b4f00da580ad1c0368607a7e0353b0169b8094cc02a5e0152e00a958404a802a4e015230068f81346c0d9760443b012198050ac1f05400eb78075b80f8de06c6b0363381f18c178be04c5d05e2d817164178ae04c5505e298171440f6de03b6b035b380ed8c136be02b5d01dad80ed64136ae02b5501da980ed441369e03b4b04da380ed0c034d601a6700d3180695c034aa01a4f00d2580691c0348601a3f00d1d8068dc034660b95e05c2f0075bc0f8de06c6b0363381f18c178be0bc5b05e2b82f14c0f6de03b6b035b380ed8c136be03b5b04dab80ed4c1369e03b4b04da380ed0c034d601a6700d3180695c0349e01a4b00d2380690c0347e01a3b00d1b8068cc0f2dc0795e00c9301a198170bc0904600eb781f1bc0d8d606c6703e3183b17c098ba0fc5b0762b8131541f8a607b6f01db581ad9c076c609b5f01dad826d5c076a609b4f01da5826d1c0768601a6b00d3380698c034ae01a4f00d2580691c0348601a3f00d1d8068dc034660796e03caf0064980d0cc0f85e00f3f8079f803cfa07d7f036bd81b5dc0fae607d6f026b681f5ac0bad207d67026b281f58c0bac207c7f01e3d81b1dc078e607c6f0163680f1ac078d207c670163280f18c078c209c5f01e2d82715c078a601b7b00dbd006de4036ee06b7600db9806dc4036ce06b6600db2806d7c036b601b5700da9806d3c0369601b4700da181e9f80d4ec07a6e03d3601e9983a4c805a5e0252b00e9380548c01a3e00d1b01a5d80f2cc1c1640343b01e198360c808056026b78175ac09ace05d6305e3781f1b8118d606c6a0463381b198178c607c6200e2f807178136de03b6b045b380ed8c0b6be03b5b025ab80ed4c1369e02b4d01da580ed241368e02b4501da180ed04034de01a6b00d3380698c034b601a5700d2980691c0348a01a3f00d1d8068dc034660b94e05c270135bc0bad604d6702eb182f1bc118d606c6a0463381b198178c601c5f04db780edac116ce03b6302daf80ed6c096ae03b5304da780ed2c1368e03b4300d378069ac034ce01a6300d2d80695c034a601a4700d1f8068ec0346e01a3302caf0165380324c088660242b02e13809ade05d6b026b381758c1f8de08c6b0363502319c0d8cc0fc6300e2f826dbc076d608b6701db1816d7c076b604b5701da9826d3c0769609b4701da18069bc034d601a6700d3180696c034ae01a5300d238068fc0347601a3700d198165780b29c0192606c3303e13809cfe05e7b0273b8179cc0bafe07d7e02ebd8175e80baee06d7602eb98175c803ade01d6e00eb68271fc078f608c7701e398171bc078d604c6701e3181717c058ba03c5b01e2c81715c058aa03c5301e28806dfc036f601b7700db9806dac036d401b6900db3812d98036c601b6100dab812d58036aa01b4f00da5806d1c0368607a7e0353b0169b8094cc05a5e02d2e016958324a803a4e015230068f80346c0d97602cab060550110ec0486602c2b05c150174980aa4400d1e02a8d0172980f84c036c401f60009af005d70016b60555a005ac805d6001e3400b190036d011b6402d3602e990314b802a5400d1e02a8d0172c81215c07c320621701dade08d6b046b386358c178de07c6e0463581b1a8118ce06c6605e3181f188178be05c5e05e2d813168178ae04c5605e29817148056de02b6b015b380ad8c056be02b5b015ab80ad4c0369e01b4d00d378069ac034ce01a6300d2f80696c034ae01a5300d278069340347e01a3b00d1982e5181708c0bc5808e2a00ed60056a801a5808d2a0165701f0a80ed6f046b582359c24ac60bc6f0463581b1a8118ce06c6605e3182f17c178b60bc5705e2980adbc056d602b67015b180ad7c056b602b57015a9806d3c034de01a6b00d3380698c034be01a5b00d2b80694c0349e01a3f00d1d8068cc0f2dc0595e014a300a4d80324c088660302b02e1181dade08d6b046b386358c1f8de08c6b0363502319c0d8cc0fc6307e2f83b16c098b40ec570262b03f14c056de02b6b015b380ad8c056be02b5b015ab80ad4c0369e01a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d1f8068ec034660796e02caf00a5180526c0192606c3303e1181dcfe08e7b0473b8519cc05afe02d7e016bd81b5e805aee02d76016b981f5c805ade02d6e016b58135a805ace02d66016b1817588058fe02c7b0163b80b1cc058de02c6b0163380b18c038be01c5e00e2e806dfc036f601b7700db9806dbc036d601b6700db1806d7c056bc01b5d00da780ad380369601b4900da1806d080368207a7e0353b0169b8094cc02a5e0992e00a958054a802a4e015230068f80347801a360691a0365d8052bc1115c0443b014198050bc1005c0473c81f9c407af203d7103e3f01f1f40f8f806c7a0363b0231d4118e80ac6e0563502b198158c403c5e04e2d027158078a401b7d00dba806d68156ac07a7e03d3e8169b8094d404a6602d3100e978054b402a5601d2901a9380d49a06a4c00d1f006538150cc0a84e056b78235ac11ace0ad630163780b1ac058ce02c630162f80b16c058ae02c53015b780adac056ce02b63015af80ad6c056ae02b5300da7806d380369a0aa6f0453582299c154c60aa5f0552d82a95c154a602a4f0152700a8fc0547c02a3b0151c80a8cc0546403a3101d1800a5380325c0a8560142702a0b81dade08d6b046b382b58c138de03c6b0463380f18c138be03c5b04e2b80f14c156de07b6e045b581ada8116ce06b66071b181ed88156be05b5e055ad812d68156ae04b56055a9816d480769e03b4e04da580ad281368e02b4601da180ed08034de01a6b00d3380698c034be01a5b00d2b80694c0349e01a4b00d2500691c1a48c01a4300c9f0101581907c06c6a02633013178098b20bc520262884b14007cfc02e7d036bd0135d805ada02d6a026b48535a005acc04d65026b200b584058da04c690263280b184076f402b79015bb00adc4056cc02b65015af00ed48054da01a6904d32806984092bc0494e04c9301a1d8050cc0b0640242f01b1a8098cc04c5e0262c82f148098a211c5000c0b0079f803cfa06d7a026bb0135b40fad404d6909eb401359809aca04d64026b08131b4098d204c650263080adb4076d202b6501db08069e8034f206a7600d3881a998034ca04a5e00d290125780929c019260343b01e198120c80485e035b501ad98092bc0192606c3304a0f80dad404d66035b501ad98096bc0bb5d08dae012d54096a40485e024270060580dcf404e760163f01b1e8058ec07c72016370131a8058d204c6801633013188058c2074600162f013168058ac04c5200da7006d340549c01a4d0151f0068e40346401a31024b70125780324c0a92406c3b0121b80509c0604c026b78135ac09ace04d63026378131ac098ce04c6304db780edac116ce03b63025af80ed6c096ae03b53025a780ed2c0968e03b43055378229ac114ce0aa630252f812978094b604a590252b81294c094a40aa5102d2801293c0949c04a4b0252481291c0948604a42055208169000747e09a3b04d1b80e8cc032de0196b00cb380658c032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9d0064dc1526c0193300c170135bc09ad606d6a026b381359809ac604c6f0263581319c098c60a36f01db5822d9c076c604b5f01dad812d5c076a604b4f01da5812d1c076860826f00d3582299c034c604a5f00d2d81295c034a604a4f00d2581291c0348603a3f00d1d8148dc034660495e024a70104981b0cc0485e076b78235ac11ace2556310a3780f1ac118ce03c630f22f80f16c1d8ae03c530d1b7806dac116ce01b630b1af806d6c1d6ae01b5301da7806d2c1e68e01b4303d3701a9980b4bc04a5601d2700a9180347c0c23606cb3022198060ac08d6f046b582359c11ac603c6f01e3580f19c078c603c5f01e2d80f15c078a601b6f00db5806d9c036c601b5f00dad806d5c036a601b4f00da5806d1c036860786e03433016178090ac0384e014230060f80306dea45ff422df9915fb88a7d735fea9adf50d5f9e6a7ca34fe29a5f0cd1f7c687b225fd892deac95f544a79d24fce125e4891f1e4878a23fbf91dda08debe4675015fa30adc9855e2e2a70214f808a5bcc51de0286dd13f6e09db444dd9c266c812f61095ab849d562469b05f4d02da4415d1c0a68204f4082599811cca0864e03f2681d91c0dc880664002f1f8158b809c5a0462a01f1480d80805c020260003f 18 262143 7 127 11 2047 21 2097151
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xd9c99a09332a175ff55af7094c52a898f4b45f90e5b178a60ea0bb8656d0a0da001a1132f15154a98a14812d15a1c3e3f64276488d616983292b65045d1075168c3271365015d1015168002a 0x135bc5d6b1359c1d63131bc4c6e071ac1c6a0719c1c660718c1c621717c5c5e0716c1c5a0715c1c560714c1c521edbc3b6b1ad9c3b6316d7c3b5b12d5c3b5326d3c2b4d0ed2c3b4926d1c2b450ed0c3b41069bc1a6b0699c1a630697c1a5b0695c1a530693caa4e069341a3f068ec1a3a068dcaa36068cc796f1a59c595f1255ca94f2e534a9472a514393f264dc192f0649c186f0619c185f0615c184f2a138184d060fc1837060bc1827135bc5d6b1359c1d63131bc1c6b0719c1c631717c1c5b0715c1c531edbc3b6b1ad9c3b6316d7c3b5b12d5c3b5326d3c2b4d0ed2c9b470ad143b43069bc7a6e069ac1a670698c1a620697c5a5e0696c1a570694c1a520693c5a4e0691c1a43069081a3f068ec1a3a068dc2a36068cc796f1a59c595f1255ca94f2a51c393f264dc192f064b419272a494186f0619c185f06168185712158184f2a138184706108183f060dc182f060b8182d135f85d6e0b1743c590b1543c511edf81b7a1add81b7216db81b6a12d981b622ad781b5d2ad701b5a06d641b582ad581b552ad501b5206d441b500ed381b4a0ad181b42069741a59069541a5106928aa461e5f8596e165789946064d8a934064984866060f8182e135bc5d6b1359c1d63131bc1c670718c5c5f0715c1c531edbc3b6b1ad9c3b6316d7c3b5b12d5c3b5326d3c3b4b26d1c3b43069bc7a6e069ac1a670698c1a620697c5a5e0696c1a570694c1a520693c5a4e0692c1a490691c1a43069081a41069001a3f068ec1a3a068dc2a36068cc196f065ac19670658c195f0656c19570654c194f2a538194b0652419470650c194206504193f064ec193a064dca936064cc786f1a19c585f1215cf84f3e11c383f260dc182f060b418272a094181f0605c4e7f139f45e7b179e84e771b9d84e75135fc4d7e135f45d6f175b85d6d1f1fc3c7b1b1dc3c73171bc3c6b1319c3c631717c2c5d0f16c3c591715c2c550f14c3c5106dfc7b7e06dec1b7a06ddc6b7606dcc1b7206dbc5b6e06dac1b6a06d9c4b6606d8c1b6206d7c5b5e06d745b5c06d6c1b5a06d641b5806d5c5b5606d57e35406d4c1b5206d441b5006d3c3b4e06d2c1b4a06d1c2b4606d0c1b42069fc1a7b069dc1a73069bc1a6b0699c1a630697c1a5d0696c1a5a069641a580695c5a5606957d2540694c1a510693c1a4b069281a472a9181a431e5fc6977165bc49671657c595d1655fc1550e53c9947064fc193d064dca935064bc1927061fc1877061bc186a0619c48660617c185d061681857161581855ec150184f0611c183f060f8183d060bc182e06088ed6f2b5acdd672b58c2c6f0b1ac2c670b18c2c5f0b16c2c570b14c2b6f0adac2b670ad8c2b5f0ad6c2b570ad4c1b4f06d381b4d069bc1a6b0699c1a630697c1a5b0695c1a530693c2a4e0691c1a43069081a3f0a8f81a3b068e41a37068cc1a32068c41a30e05bcd9672a57ce9570a53c29470a4fc393d0a4dc2935064bc192d0649cd125061bc18670617c185a0615f20560613c284e0611c1842060fc1837060bc182e060b44d6d175a44d65175842c6d0b1a42c650b1842b6d0ada42b650ad841b4e06d341a6d069a41a65069842a4e0a8f81a39068c81a31068c069761a598294ec4158284e060b87d7f1b5ec6d771f5cc7d6f135b47d6b175a47d67135947d63175847c7f0f1ec6c770f1cc7c6f0b1b43c6b0f1a47c670b1943c630f1849c5f0f16c9c570f14c1b7f1edf81b7b06de81b771add81b7306dc81b6f1edb81b6d1edb01b6b06da81b6906da01b671ed981b6522d901b6306d881b6106d801b5f16d781b5b06d681b5712d581b5306d481b4f0ed381b4b06d281b470ad181b4306d081a7f069ec1a77069cc1a6f069b41a6b069a41a67069941a63069841a5f0696c1a570694c1a4f0692c1a4a0691f82460690c69761a59b0056060f8182e2b5bc7d6e235ac6d6a2359c6d662b58c7d62131bc5c6b1319c5c630717c1c5d26dbc3b6b22d9c3b6326d7c2b5d0ed6c3b5926d5c2b550ed4c3b5116d3c3b4b12d1c3b43069bc1a6b0699c1a630697caa5e069741a4f0692c1a43068fc1a3b068dc1a332a178ad6f235ac8d672b58c4c6f171ac4c671718c1c5f26dbc3b6b22d9c3b6326d7c2b5d0ed6c9b570ad543b5316d3c3b4b12d1c3b43069bc1a6b0699c1a630697c5a5e0693c5a4e0692c1a43069081a3f068ec1a37068cca85e12118182e135bc5d6b1359c5d633f1bc8c6b2319cfc6326dbc3b6b22d9c3b6316d7c3b5b12d5c3b5326d3c3b4b26d1c3b43069bc1a6b0699c1a630697c5a5e0696c1a570694c1a520693c5a4e0692c1a490691c1a43069081a41069001a3f068ec1a37068cc196f065ac19670658c195f0656c19570654c194f2a538194b0652419470650c194206504193f064ec193a064dca936064cc4e7f179ec4e77179cc5d7f1f5f85d7b175e85d771b5d85d73175c89c7f0f1ec8c770f1cc5c6f0f1ac4c670f18c5c5f0b1743c5b0f1645c570b1543c530f1441b7f1edf81b7b06de81b771add81b7306dc81b6f16db81b6b06da81b6712d981b6306d881b5f16d781b5d16d701b5b06d681b5906d601b5716d581b55d8d501b5306d481b5106d401b4f0ed381b4b06d281b470ad181b4306d081a7f069ec1a77069cc1a6f069ac1a670698c1a5f069741a5b069681a59069601a57169581a55d49501a53069441a4f0692c1a4a0691caa460690c49661255848661615b4054060f8182e135bc4d6b1359c4d63131bc4c6b1319c4c630adbc2b6b0ad9c2b630ad7c2b5e0ad6c2b590ad5c2b5312d482b510ad3c2b4b0ad1c2b430a9bc2a6b0a99c2a630a97c2a5b0a95c2a530a93c2a4b0a91c2a43068fc1a3e068f4196f065ac19670658c195f0656c19590655c195306544194f0652c19490651c194306504193f064dc1933064bc192b064a419270648c1921c41bcd8671217c48571213c48470a0fc28370a0bc382d0a09c28250607c181d0605ca815135b44d69135944d61131b44c69131944c610adb43b690ad943b61069b41a69069941a61129781a59069481a51069404a4e069241a4206904196d065a4196506584495e06564195206544193ac44d868761a198485e135bc4d6b1359c4d63131bc4c6b1319c4c6326dbc3b6b26d9c3b6312d7c3b5b12d5c3b5312d3c3b4b12d1c3b43069bc1a6b0699c1a630697c4a5e0696c1a590695c1a53069481a51069401a4f129381a4b069241a470690c1a42069041a3f068ec1a37068cc196f065ac19670658c195f12578195b0656419570654c195206544194f0652c19470650c193f064ec193a064df2136064cf006f3619c485f1215c484f1211c383f260dc182f060b4182710094181f0605ced6f375acdd67e958c9c6f0f1ac9c670f18c9c5f0f16c9c570f14c1b6f1edb81b6b06da81b671ad981b6306d881b5f16d781b5b06d681b5712d581b5306d481b4f0ed381b4b06d281b470ad181b4306d081a6f069ac1a670698c1a5f0696c1a570694c1a4f0692c1a4a0691f92460690f716f3659f315f3a55c394f2651c193f064f41937304d4192f0649c186f0619c185f061681857bc158184f0611c183f060f8183d060bc182e06088dd6f375acdd673758c3c6f0f1ac3c670f18c3c5f0f16c3c570f14c1b6f06dac1b6706d8c1b5f06d6c1b5706d4c1b4f06d2c1b4706d0c19361e1b868661617848560e1382846060f84d6f175ac4d671758c8c6f1f1b88c6b1b1a88c671b1988c631f1883c5f0f1782b6f0adac2b670ad8c2b5b0ad5c2b530ad1c2b45229bc1a6b2299c1a631697c1a5b1295c1a532693c9a4d0692c1a492691c9a450690c1a410a8fc1a3b0a8dc1a33139fc5e7b139dc5e730b5fc7d7e0b5ec2d7a0b5dc6d760b5cc2d720b5bc3d6e0b5b42c7f0b1ec2c770b1cc2c6b0f1a82c690b19c2c660b18c2c610b15c2c560b1548b7f06dec8b7706dcc5b6f06dac4b6706d8c2b5f0ad741b5b06d642b5726d541b5306d442b4f06d2c2b4706d0c8a761e5f86976165b849660a578295c0a55ac1540a5382946064f89936235bc8d6b2359c8d63231bc3c6b2319c3c63ad17c3c5b3b15c3c5322dbc1b6b22d9c1b6332d7c1b5b32d5c1b530ed3c1b4b32d1c1b4322998796e1a598595e12558394e0a518193e324d8dd6f235ac8d673758c3c6f0f1ac3c670f18c3c5f0f16c3c570f14c1b6f06dac1b6706d8c1b5f06d6c1b5706d4c1b4f06d2c1b4706d0c89663a558786e1a198585e12158384e0a118183e060d84d6f175ac4d67131bc4c6e1717c5c5e1edbc3b6b1ad9c3b6316d7c3b5b12d5c3b532ed3c2b4d0ed2c3b492ed1c2b450ed0c3b411e9bc1a6b1a99c1a631697c1a5b1295c1a532e93caa4d0692c1a492e91caa450690c1a410e8fc1a3b2e8dc1a332e538b84e135bc5d6b1359c4c6f1717c7b6f0edac6b670ed8c5b5f0ed6c4b570ed4cbb4f0ed2cbb470ed0c7a6f069ac6a670698c5a5f0696c4a570694cba4f0692cba470690c3a3f068ecba37068cc796e16578594e0a4d8a9261a19848562e1384d6f175ac4d67131bc5c5f1edbc3b6b1ad9c3b6316d7c3b5b12d5c3b533ed3c3b4b3ed1c3b431e9bc1a6b1a99c1a631697c1a5b1295c1a533e93c1a4b3e91c1a430e8fc1a3b3e8dc1a331e5b8595e1653829362a49868663e1384e7f139f45e7b179e84e771b9d84e75135fc4d7e135f45d6f175b85d6d1f1fc3c7b1b1dc3c73171bc3c6b1319c3c631717c2c5d0f16c3c591715c2c550f14c3c511edfc1b7b1addc1b7316dbc1b6b12d9c1b6316d7c5b5d06d6c1b5916d5d6b5506d4c1b510ed3c1b4b50d1c1b431e9f86a76169b84a66169785a5c1695a82540e9382a46068f8aa361a5d859569c5506876121985856981503d6f0f5b87c6f1b1ac6c671f18cbc5f13174bc5b17164bc5713154bc53171442b6b0ad9c2b630ad5c2b550ad3c2b4b0ad1c2b431e9bc1a6b1a99c1a632697c9a5d0696c1a592695c9a550694c1a512693c1a4b2691c1a430a8fc1a3b0a8dc1a332e578b85e0f5bc7c6f1b1ac6c671f18cbc5f2f16cbc572f14c2b6b0ad9c2b630ad5c2b4f0ad2c2b470ad0c7a6f069ac6a670698c9a5f0696c9a570694c9a4f0692c9a470690c2a3f068ec2a37068cc796e0a57829361a198b85e2c1183d6f1f1bc6c6b1b19c7c633b17c4c5d3f16cec5713154fc530adac2b670ad8c2b570ad3c2b4b0ad1c2b431e9bc1a6b1a99c1a632697c1a5b2695c1a532693c1a4b2691c1a430a8fc1a3b0a8dc1a331e5b8295e0a4d868663e1782e7f0f9f82e7d1f5fc6d7b1b5dc7d730b5bc2d6d0b5ac5d690b59c4d650b58c2d610b1ec3c7a0b1e42c770b1d82c730b1c42c670b1982c650b17c2c5b0b15c2c531edfc1b7b1addc1b730adbc2b6d06dac1b690ad9c9b6506d8c1b6126d7c1b5b26d5c1b530ad3c1b4b0ad1c1b431e9f86a760a9b82a6c0a99a4264169784a560a9382a46068f89a361a5d829668c59068760a19a2064281584d6f175ac4d671758cbc6f1f1b88c6b1b1a88c671b198bc631f1883c5f0f1782b6f0adac2b670ad8c2b5b0ad5c2b530ad1c2b45269bc1a6b2299c1a631697c1a5b1295c1a532693c9a4d0692c1a492691c9a450690c1a410a8fc1a3b0a8dc1a332e538b84e135bc5d6b1359c5d633f1bc8c6b1b1a88c671b198fc630f17c2b6f0adac2b670ad8c2b5b0ad5c2b530ad1c9a6f069ac8a670698c5a5f0696c4a570694c9a4f0692c9a470690c2a3f068ec2a37068cc796e16578294e0a4d8992636198f84e 19 524287 8 255 11 2047 18 262143
def cc_56_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xf085bcd93b950670327d4eb99f0af102e5ef31b805f654aeb29853233a0a5b3789e4ea0c39647e290f4481d315b53535a7009dd710dae1d3483763068c60c09113b461d4a21adfc10a500021 0xed6f11ad62359c56b18bc6f0f8dc231ac363508c670d8cc2f18c3e310ac5f0b8bc2f16c262d0bc57098ac2b14c2e2902b6f076d60ad9c1db182b5f076b60ad5c1da981b4f0369a069bc0d3581a67034c60697c0d2d81a57034a60693c0d2681a3f03476068cc54a3019261dade2b5ac6eb38ad63158de1f1b86e3586c6a158ce1b1987e3187c62158be17178562d84c5a158ae13158562985c52056de0edac15b383b63056be0ed6c15ab83b530369e06d340da381b4503686069bc0d3581a67034c60697c0d2d81a57034a60693c1d2701a4d0347e0e8f80d1d81a3703466068cad8b78d967152be3a55c7ca7de14d1528f485141c9f829370325e064b40c93d1125030de0619c0c2f818570309e061340c23818450307e060dc0c178182d0304e060943ebe05d7811ae8175c03dbe03b78116e80edc02dae03b582f6a80ed4026b685d6909aca175843e3f06c7a0d8ec1f1c83e3707c6d0f8d81f1a8463488c680f8cc23194463207c620f8c21f1802e2f04c5a098ac1714815b683b69056ca0ed840da681a6d034d2069940d3083a4e0349a0e8f80d19069760d2cc1f5fc36bd86d770fae61f5bc26b687d6b0bad21f59c26b287d630bac20b1fc1e3d82c77078e60b1bc163683c6b078d20b19c163283c63078c20b17c1e2d82c57078a60edfc3dbf03b7b076f40eddc35bb03b73076e40edbc3db703b6d0f6d80edac1db503b69076d00ed9c3db303b65116c80ed8c1db103b61076c00ed7c2daf03b5b076b40ed5c25ab03b53076a41e9fc0d3d86a77034e61e9bc3d3681a6b034d21e99c453281a63034c37097c0d2d8ea57034a60e93c0d2582a47034860e8fc1d1e81a3b034720e8ded91a81a33034621a5d834b3028460506c2f5bc3eb708d6b0dad42359c36b30bd630fac4131bc2e3584c670b8c60f17c1e2e82b6f076d60ad9c1db182b5f056ba0ad3c1da583b43214de069ac453381a63174be2a9740d2d81a59174ae2a9540d2981a510b49e0692c252381a430747e068ec151b81a3309cfe179ec273b85e730bafe1f5f82ebd85d7a0baee1b5d82eb985d72058fe0f1ec163b83c73058de0f1ac163383c63058be0b1741e2d83c59058ae0b1541e2983c51076fe1edf81dbd83b7a076ee1add81db983b72076de16db81db583b6a076ce12d981db183b62076be16d781dae85b5c076b60ed681dac83b58076ae16d581daad9354076a60ed481da883b50214fe069ec453b81a730b4de069ac253381a630b4be169740d2d81a590b4ae429540d2981a510749e0692c152381a430747e0e8f40d1d81a390746e2a8d40d1981a31092cc1255814230283609cfa179e8373b04e7509afc135f42eb705d6d0f8fc1b1e8363b07c720b8dc131a8263305c620b8bc171742e2e05c5a298b2531602e2b0bc55178a8171482e2885c50056ba0ed681dac83b580b6ac0ad5415aa03b510b4ba06964852a81a511549a06924552281a410b2ac2e5501ca70393e2124c079f80f3e84d6d0bad2135942eb087c7e0d8f41b1d83e3907c6e0f8da1f1b03e3514c69278d01f1985e328bc640f8c41f1843e3005c5e098b4131582e2902b6d076d20ad941db081a7a034f21a9d80d3886a66034ca429380d268aa4c03492069140d2101a41034800e5381c9f019260fafc175e836bb05d7203adc075b43e3f06c7a0d8ec1f1c82e3704c6a098cc171882e2f05c5d0b8b817168a62c94c580b8ac2f1545e2a05c520b8a21714015ae83b59056aa0ed440d3501a69094cc06984252b01a550349a069240d2281a410729c0e4f80c930ad6f11ad62359c56b182c6f078d60b19c1e3182c5f078b60b15c1e298ab6f0f6dc22dac35b508b670d6cc2ad8c3db10ab5f0b6bc2ad6c25ad0ab57096ac2ad4c2da901b4f0369c069bc553701a6b034ce0698c0d3101a5f034b60695c0d2981a4b034940691c152301a430346e2a8d80d1a8ed6f11ad62359ebab18bc6f0f8dc231ac363508c670d8cc5318c3e310bc5f0b8bc3b16c262d0bc57098ac5314c2e2902b6f076d60ad9c1db182b5f076b60ad5c1da9d626f034d62299c0d31d525f034b63a95c0d2994a4fa849a0692c0d248ba47a448a0690c0d2083a3f034760a8dc0d198394e0727d4049856b788d6b11ace2b58c563787c6e118d61b1a8463386c66158c61f188562f85c5e158b613168562b84c56158a61714815b783b6b056ce0ed8c15af83b5b056ae0ed4c15a782b4d034de069ac0d3381a63034be0696c0d2b81a530349e2a9380d2681a3f03476068cc54a70ad6f11ad62359c56b18ac6f118d62319c56318ac5f158b62b15c562982b6f076d60ad9c1db182b5f076b60ad5c1da981b4f0369a2a9bc453588a67154c62a97c552d8aa57154a60e93c1d2703a3f0747c0a8ec1d1983a321529c064b876b788d6b11ace4358c5e3788c6b118ce2f18c5e2f8bc5b178ae2f14c15b783b6b056ce0ed8c15af83b5b056ae0ed4c5d3788a6b114ce2e98c5d2f8ba5b174ae2e94c1d2783a4e03496069240d2381a4303484069040d2003a3f0747c0a8ec0d1b83a3307464065bc0cb581967032c60657c0cad81957032a60653c5ca70194b032920651c0ca18194203282064fc0c9d8193a0326e0a4d80c998ee7f11cf6239dc873982d7f07af60b5dc1eb982d6f07ad60b59c1eb183c7f0f8fc0f1ec1e3d03c770d8ec0f1cc1e3903c6f0b8dc0f1ac1e3503c67098cc0f18c1e310bb7f0f6fc22dec35bd08b770d6ec2edcc3db90bb6f0b6dc2edac25b50bb67096cc2ed8c2db103b5f076bc0ad6c15ad02b57056ac0ed4c1da903b4f0769c0ed341da603b4b076942ed2465a403b470768c2ad1691a203b43076840ed041da001a7f034f6069dc0d3981a6f034d60699c0d3181a5f034b6069680d2b82a56034a60693c0d2681a4b03494069240d2401a470748c06916892201a43034820e51a80a20193e0325c0a15814230ed6f1bad63759f1ab182c6f078d60b19c1e3182c5f078b60b15c1e2983b6f0f6dc0edac1db503b670d6cc0ed8c1db103b5f0b6bc0ed6c1dad03b57096ac0ed4c1da96126f034d63699c0d31df25f034b63a95c0d2983a4f034960a91c0d2183a3f0747a068ec0d1c83a37ba46a068cc0d18da16f1b2cf6057c74ab8394f0528e0e4fc1c9e83937a626a064be78938386f070ce0e17c1c2b8284a0508e0a118141b828360506a060bc0c138dd6f1bad63759c6eb182c6f058d60b19c163182c5f058b60b15c162981b6f036d606d9c0db181b5f036b606d5c0da981b4f0369606d1c0da18294e0f0dc1a1982c2f048560508c060f80c1b04d7e0badc0b1f81e3d02c76078e40b1b81e3502c66078c40b178162e82c5c078b40b1641e2c02c56058aa0b1501e2902c51078a00ad7415ac82b55056a2269740d2c89a55034a20e9340d2482a45034821e5f82cb70595e0528c0a510149b099260509c0a0f826b785d6b09ace0b58c263783c67078c61717c1e2b83c53056de0adb815b582b67056c60ed8815af82b5e056b60ad5c15a983b520569e0ad3815a582b490568e0ad0c1da102b41076800a9bc153582a67054c60a97c152d82a57054a60a93c152702a4b054920a91c152183a42054821e5bc0cb586967032c61657c0cad84957032a62653c0ca589947032860a4fc1c9e8193b0526e0a4d40c998292f032560a49c0c918786f0d0ce1617c242b8f84f1f08e0a0fc1c1e828370506a0a0bc14138181f1302e139fc273e85e7b0bcf4139dc373b04e7509afe135f826be85d6f0badc175b4163f82c7e058f60f1e8163b82c76058e60f1c8163782c6e058d60f1a8163382c66058c60f188162f82c5e058ba0b170162d83c5a058b20f160162b82c56058aa0b150162983c52058a20f14015bf82b7b056ee0adcc15b782b6b056ce0ad8c15af82b5d056b60ed6815ac83b58056ae0ad5815aa82b54056a60ad443d3f81a7b0d4ee069cc2d3781a6b094ce0698c2d2f85a5d034b6069642d2b89a55034a606944152783a4d0349606924152382a450348606904151f81a3b0546e068cc3cbf869770b2de1259c2caf8595d0b2af3055414a78394d0528e0a514149f829370325e2649c1c3f83877070de0e19c1c2f8385d070b40e15c2c2b03855960a80a13c14270384d0507e0a0f814190182f0304e1f5fc36bd86d770fae61f5bc26b687d6b0bad21f59c26b287d630bac20b1fc163f02c7b078f40b1dc163b02c73078e40b1bc163702c6d058d80b1ac1e3502c69078d00b19c163302c65058c80b18c1e3102c61078c00b17c162f02c5b078b40b15c162b02c53078a40adfc15bd82b77056e60adbc15b682b6b056d20ad9c15b282b63056c20ad7c15ad82b57056a61e9fc0d3d86a77034e61e9bc3d3681a6b034d21e99c453281a63034c22697c0d2d89a57034a60a93c1d2681a4b034920a91c152281a43034820a8fc0d1d82a37034661a5d834b30284e0507c139fc2f3d84e770bce6175fc3ebf05d7b0baf4175dc36bb05d730bae40b1fc163f02c7b078f40b1dc163b02c73078e40b1bc163702c6b078d40b19c163302c63078c40b17c162f02c5d058b80b16c1e2d02c59078b00b15c162b02c55058a80b14c1e2902c51078a00adfc15bd82b77056e60adbc15b582b67056c60ad7c15ae82b5b056b20ad5c15aa82b53056a2269fc0d3d88a77034e6169bc0d3584a67034c61697c2d2e81a5b034b21695c4d2a81a53034a20a93c1d2681a4b034920a91c152281a43034820a8fc0d1d82a37034661259824ab0284e0507c3b5bc6eb58dd6794ac60b1bc163702c6b078d40b19c163302c63078c40b17c162f02c5b078b40b15c162b02c53078a40adbc15b582b67056c60ad7c15ad82b57056a6269bc0d3589a67034c62697c0d2d89a57034a60a93c1d2681a4b034920a91c152281a43034820a8fc0d1d82a3703467245bc6cb3c815f1d2ae0a53c1ca6829470528a0a4fc149b8192f1324e0e1bc1c338385f070ae0a13c14270384d0507e0a0f814190182f0304e3717c6e2d8dc571b8a60ad7c1dad82b57076a60ad3c1da582b47076860697c0d2d81a57034a60693c0d2581a4703486068fc0d1d81a37034663717c6e2d8dc571b8a60ad7c1dad82b57076a60ad3c1da582b47076860697c0d2d81a57034a60693c0d2581a4703486068fc0d1d81a3703466375bc6eb58dd671bac60b1bc1e3582c67078c60b17c1e2d82c57078a606dbc0db581b67036c606d7c0dad81b57036a606d3c0da581b47036860a5183c37068660b0bc121581c270183e8c078060da281a04d6f0bad61359c0eb184c6f038d60719c0e3185c5f038b60715c0e2987b6f076d61ad9c1db185b5f076b612d5c1da989b4f0569a0ed2c4da382b4507686069bc3d3701a6b034ce0698c0d3101a5f0b4bc0696c0d2b81a53034a40693c952701a4d0347e068ec0d1d01a370546c068cc3cb7869670b2be1255c64a78a9470727e264dc0c978192d0324e324940c3781867030be0615c0c27818470307e060dc0c13818260304a135bc2eb584d6703ac6131bc263701c6b038d40719c0e3301c63038c41717c2e2f01c5b038b40715c0e2b01c53038a41edbc1db586b67076c616d7c1dad84b57076a626d3c15a683b4b0769226d1c15a283b4307682069bc0d3581a67034c60697c0d2d81a57034a60693c0d2681a470348a0690c0d1f81a3b03474068dc4d1b01a330f2de1a59c2caf849571929e2e53464a38b9450727e264dc0c9781927030de0619c0c2f818570309e061340c23818450307e060dc0c178182a0304e06098273f84e7d0bcf6179e8273b86e7609cea135fc26bf04d7d0bade175b82eb687c7f078f61b1dc1e3985c6f078d61319c1e3185c5f058ba0f16c1e2c85c57058aa0f14c1e2881b7f036f606ddc0db981b6f036d606d9c0db181b5f036ba06d6c0dad01b59036b006d5c2dab01b55866a806d4c0da881b4f0369606d280da389b4603686069fc3d3f01a7b034f4069dc353b01a73034e4069bc2d3701a6b034d40699c253301a63034c40697c2d2f01a5d0b4b80696c0d2d01a59034b00695c2d2b01a55844a80694c0d2901a51034a00693c1d2701a4b034940691c152301a43034841e5fc34bb8596f092ce1657c2cae85957192aa0e53c4ca38193f0326e064bc0c96819271924a061fc0c3b8186f030ce0617c0c2e81857030aa0613c0c238183a0306e060d80c13818260304a3b5bc6eb58dd6782ac6271bc1e3589c67078c62717c1e2d89c57078a606dbc0db581b67036c606d7c0dad81b57036a606d3c0da581b4a0368e26d180da181a6f0f4dc069ac0d3501a670d4cc0698c0d3101a5f0b4bc0696c0d2d01a57094ac0694c0d2901a4f0749c0692c0d2501a470548c0690c0d210c96f192ce3257c64ab8394f1328e064fc0c9b8192f0325a0649c64928186f030ce0617c0c2b8184f0308e060e80c1b818360304e060980c128dd6f1bad63759c6eb183c6f078d60f19c1e3183c5f078b60f15c1e2981b6f036d606d9c0db181b5f036b606d5c0da981b4f0369606d1c0da18e9560327c1e1b834330585e090ac0e138142301836 19 524287 8 255 11 2047 19 524287
def cc_56_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x87481823517fa2977981732477052d6b74e662556352d5b184588295790f51a5f4ef2b4c42b4982c46b2d42c3f3f9333ce2b36f5f3422d3251d2c4612784c258202094f18c7d13f4d0c6790794d00079 0x2e7f03e7e02e7d04d7f04d7e04d7b06d7a04d7704d7604d7307d7202d6f02d6e02d6d02d6c02d6b02d6a04d698056802d6702d6604d6504d6402d6302d6202d6102d6004c7f04c7b04c7704c7302c6f02c6d02c6b04c6902c6704c6502c6302c6102b7b03b7a02b7902b7702b7602b7302b7102b6702b6602b6502b5f02b5e02b5d02b5c02b5b02b5902b5702b5502b5303b5202b5103b5002b4f02b4b02b4702b4307a7f01a7b06a7701a7302a6f02a6d01a6b01a6902a6709a6501a6301a6104a5f09a5d01a5b01a5904a5704a5501a5301a5104a4f01a4b04a4701a4302a3f01a3b02a3701a330797f069770296f0296d029677f1650495f7115d04957049550494f049470293f029370192f099270387f038770286f0286d02867038650385f0485e0385d0384f0484e038420283f028370182f0382a01827098260381a0a01604d6f01d6b04d6704d6301c6f01c6e01c6b01c6a04c6704c6601c6301c6204c5f04c5e01c5701c5301c5207b6f03b6b06b6703b6304b5f03b5b04b5703b5309b4f02b4d03b4b03b4909b4702b4503b4303b4101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330796f069670495f049571294f0b94d129470b9450393f099370192f019270186f018670185f018570184f0184d01847018450183f018370182f0182a01827018260181a1381601e7e04d7e06d7a04d7607d7204d6e04d6d04d6c0bd6a04d690bd6804d6604d6504d6411d6204d6111d6004c6d04c6904c6504c6102b6d03b6902b6503b6102b5d03b5902b5503b5101a6501a5d01a5901a5501a510797e0796e019260485e0484e018260901401e7f01e7e01e7d04d7f04d7e04d7b06d7a04d7704d7604d7307d7204d6f04d6e04d6d04d6c04d6b07d6a04d697d56804d6704d6604d6504d6404d6307d6204d6107d6004c7f04c7b04c7704c7304c6f04c6d04c6b04c6904c6704c6504c6304c6107b7f03b7b06b7703b7307b6f02b6d03b6b03b6907b6702b6503b6303b6104b5f02b5d03b5b03b5904b5702b5503b5303b5104b4f03b4b04b4703b4301a7b01a7a01a7901a7706a7601a7301a7101a6706a6601a6501a5f04a5e01a5d7a25c01a5b01a5901a5701a5501a5301a5201a5101a5001a4f01a4b01a4701a4301a3f01a3b01a3701a330797f069770796f0796d079677c1650495f7015d04957049550494f049470393f099370192f019270187f018770186f0186d01867018650185f0485e0185d0184f0484e018420183f018370182f0182a01827018260181a0801601d6f01d6e01d6d04c6f04c6b04c6704c6304c5f04c5d04c5b04c5704c5504c5307b6f07b6d06b6b06b6a06b6706b660ab6504b6304b5f04b5d06b5b06b5a04b5704b5604b5504b5404b5301b4f01b4701b4307a6f03a6b06a6703a6307a5f03a5b07a5703a5304a4f03a4b04a4703a4309a3f03a3b09a3703a330796f069670795f079570494f049470a93f0a9370392f099270186f018670185f0185d01857018550184f018470183f018370182f0182704d6f04d6b04d6704d630bc6f07c6e08c6b06c6a08c6706c660bc6307c6201c5f01c5e09b6f03b6b08b6703b6304b5f03b5b04b5703b5309b4f02b4d03b4b03b4909b4702b4503b4303b4101a6f01a6b01a6701a6301a5b01a5701a5301a4701a4501a3f01a3b01a3701a330a94e0192604d6f04d6b04d6704d630fc6f07c6e0ac6b06c6a0dc6706c660ac6307c6201c5f01c5e01c5701c5301c5209b6f03b6b09b6703b6304b5f03b5b04b5703b5309b4f02b4d03b4b03b4909b4702b4503b4303b4101a6f7a26e01a6b01a6701a6301a6201a5f01a5b01a5a01a5704a5601a5301a4704a4601a4501a3f01a3b01a3701a337416f0d9670495f049570a94f6914d0f947791450393f099370192f019270186f018670185f018570184f0184d01847018450183f018370182f0182d018270182504d6f04d6b04d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5701c5312b6f07b6e0db6b06b6a0db6706b6612b6307b6202b5f02b5e01b5701b5301b5202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a311b96f0d9670495f049570294f029471293f0b93d129370b9350192f019270186f018670185f0485e01857018520184f018470183f0183d01837018350182f0182d0182a0182701826018250181a0701604e7e06e7a04e7607e7207c7e06c7a06c7607c7204c6e11c6d11c6c04c6a04c6904c6804c6604c6504c6404c620bc610bc6004c5e04c5a04c5604c5202b6d02b6902b6502b6101b4d01a6d01a6901a6501a6101a4d1597e0496e0b96c0495e0294602936019260486e0485e018260601404e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7302c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b04c6a02c6904c6802c6702c6602c6502c6402c6304c6202c617746002c5f02c5e02c5b04c5a02c5702c5602c5304c5202b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5301b4f01b4e01b4d01a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a317317f0d9770496f6e16d04967049650495f049570294f7614d02947029450293f0393d02937029350192f0192d01927681250187f018770186f0486e0186d0185f0485e018520184f0184d01847018450183f018370182f0182d0182a018270182601825320240181a0501604d6d04d6904d6504d6107c7e06c7a06c7607c7207c6e07c6d07c6c07c6a08c6908c6807c6608c6508c6407c6207c6107c6001c5e02b6d03b6902b6503b6102b4d03b4902b4503b4107a7e01a7201a6d01a6901a6501a6101a5a04a5604a4601a45069760696604e7c08e7804e7407e7002c7c08c7802c7407c7002c6c04c6802c641bc600b96c1594c3102404d7f04d7e04d7b06d7a04d7704d7604d7307d7204d6f04d6e04d6d04d6c04d6b07d6a04d6908d6804d6704d6604d6504d6404d6307d6204d6107d6004c7f04c7b04c7704c7304c6f04c6d04c6b04c6904c6704c6504c6304c6107b7f03b7b06b7703b7307b6f02b6d03b6b03b6907b6702b6503b6303b6104b5f02b5d03b5b03b5904b5702b5503b5303b5104b4f03b4b04b4703b4307a7f01a7b06a7701a7307a6f07a6d01a6b01a6907a6708a6501a6301a6104a5f7425d01a5b01a5904a5704a5501a5301a5104a4f01a4b04a4701a4303a3f01a3b7323701a3306976069660495e6d15c0485e0484e3002603e7e02e7d02d6d04d6904d6502d6107c7e06c7a06c7607c7202c6e02c6d02c6c02c6a0bc690bc6802c660bc6514c6402c6202c6102c6003b7a02b7902b7602b7102b6602b6502b4d02b4902b4502b4102a6d01a6909a6501a6109a4d01a4909a4501a410797e049560494601e7e01e7d04d6d04d6904d6504d6107c7e06c7a06c7607c7207c6e07c6d07c6c07c6a0bc690bc6807c6617c6513c6407c6207c6107c6002b6d03b6902b6503b6102b4d03b4902b4503b4101a7a01a7906a7601a7106a6601a6501a4d01a4901a4501a410797e04956049460ad6f07d6e08d6b06d6a08d6706d660ad6307d6204c6f04c6b04c6704c6301c5f01c5d09b6f03b6b08b6703b6309b5f02b5d03b5b03b5909b5702b5503b5303b5104b4f03b4b04b4703b4301a6f01a6b01a6701a6301a5f0aa5e01a5d01a4f01a4b01a4301a3f01a3b01a3701a3307d7e06d7a06d7607d7202c7e06c7a02c7607c7202c6e04c6a02c6604c6202c5e02c5d02c5c0bc5a02c5917c5802c5602c5502c540bc5202c510bc5002b5d02b5902b5502b5101b4e01b4d01a5d01a5901a5501a5102a4e01a4d02a3e01a3901a3201a310b97e04966049560294e0b94c04c6f04c6b04c6704c6304c5f04c5d04c5b04c5704c5504c5307b6f07b6d06b6b06b6a06b6706b6608b6504b6304b5f04b5d06b5b06b5a04b5704b5604b5504b5404b5307a6f03a6b06a6703a6307a5f03a5b07a5703a5304a4f03a4b04a4703a430ba3f03a3b0ba3703a330796f0196b06967019630795f0195b07957019530494f0194b04947019430b93f0193b0b937019330392f0192b0b9270192304d6f04d6b04d6704d6317c6f07c6e08c6b06c6a08c6706c660bc6307c627136f03b6b08b6703b6304b5f03b5b04b5703b530bb4f02b4d03b4b03b490bb4702b4503b4303b417026f01a6b08a6701a6304a5f01a5b04a5701a530ba4f6924d01a4b01a4917a476f24501a4301a4103a3f01a3b6e23701a336d16e049560494604d6f04d6b04d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5712b6f07b6e08b6b06b6a08b6706b6612b6307b6202b5f02b5e02b4f02b4e09a6f01a6b08a6701a6304a5f01a5b04a5701a5302a4f01a4b02a4701a4309a3f09a3d01a3b01a3909a3709a3501a3301a3104e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7302c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b04c6a02c6904c6802c6702c6602c6502c6402c6304c6202c616b46002c5f02c5e02c5b04c5a02c5702c5602c5304c5202b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5309a7f01a7b08a7701a7304a6f09a6d01a6b01a6904a6704a6501a6301a6104a5f01a5b04a5701a5302a4f09a4d01a4b01a4902a4702a4501a4301a4102a3f03a3d01a3b02a3702a3501a330294e0293e0486e0485e0982604d6f04d6b04d6704d630ac6f07c6e08c6b06c6a08c6706c660ac6307c6204c5f04c5e09b6f03b6b08b6703b6304b5f03b5b04b5703b5309b4f02b4d03b4b03b4909b4702b4503b4303b4101a6f01a6b01a6701a6301a5b01a5701a5301a470aa4601a4501a3f01a3b01a3701a330a94604e7e06e7a04e7607e7202c6d02c6902c6502c6102b6d02b6902b6502b6101b4e01b4d0aa6d04a6904a650aa6102a4e02a3e02a3902a3203a310294e0192e0486e0485e0a8260a82404e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7309c7f03c7b08c7703c7304c6f02c6d03c6b03c6904c6702c6503c6303c6104c5f03c5b04c5703c530ab7f07b7e08b7b06b7a08b7706b760cb7307b7204b6f04b6e0ab6d6936c04b6b04b6a04b6904b6804b6704b6604b6504b6404b6304b620cb610cb6004b5f04b5e04b5b04b5a04b5704b5604b5304b5203b4f03b4e09b4b02b4a09b4702b4603b4303b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4a01a476824601a430193e0192e0486e0485e0a836040340182604d6f04d6e04d6b06d6a04d6704d6604d6307d6204c6f04c6b04c6704c637e36f03b6b0db6703b6304b5f02b5d03b5b03b5904b5702b5503b5303b5104b4f03b4b04b4703b437b26f01a6b0da6701a6304a5f7825d01a5b01a5904a5704a5501a5301a5104a4f01a4b04a4701a4303a3f01a3b7523701a337216f0d9670495f6c15d04957049550494f049470393f6a1370192f671270d86f0d8670485f0485e0585d0484f0484e048420383f038370182f0e82a018272f0260e81a0301604d6f05d6b04d6705d6303c6f03c6b03c6703c6303c5f03c5b03c5703c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b43049560786e068660585e0384e028460183e0183604d6f05d6b04d6703d6304c6f04c6e03c6b03c6a03c6703c6603c6303c6205c5f05c5e03c5b03c5a03c5703c5603c5303c5202b6f03b6b02b6703b6302b5f03b5b02b5703b5302b4f02b4d02b4702b4503b4307a6f01a6b06a6701a6305a5f01a5b04a5701a5310a4f0aa4d01a4b01a4910a470aa4501a4301a4103a3f01a3b02a3701a330796f069670595f049571094f0b94d109470b9450393f029370192f109270386f038670385f038570384f0284d02847028450383f0283a02837028360182f0182704e7f04e7d05e7b05e7a04e7706e7604e7504d7f04d7e04d7d05d6f05d6e05d6d02c7f03c7b02c7703c7302c6f03c6b02c6703c6302c5f02c5d03c5b03c5a03c5903c5802c5705c5602c5502c5403c5303c5103b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f05b6e03b6b03b6a03b6704b6603b6303b6203b5f05b5e03b5d05b5c03b5b03b5a03b5903b5803b5705b5603b556435403b5303b5203b5103b5007a7f01a7b06a7701a7305a6f01a6b04a6701a6305a5f05a5d01a5b01a5905a5710a5501a5301a5103a4f01a4b02a4701a4303a3f03a3d01a3b01a3903a370aa3501a3301a310797f069770596f049670595f0595d059570b9550394f029470393f0393d03937571350192f109270387f038770386f038670385f0385d03857038550284a02847028460283702836028350182f0182703d6f03d6d01d6b01d6901d6701d6501d6301d610ec6f04c6d10c6b05c690ec6704c6510c6305c6107c5f06c5b06c5707c5302b6f02b6d01b6701b6501b6302b5f03b5b01b5703b5302b4f03b4b02b4703b4301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a331096f0b96d109670b9650795f069571094f0e9470393f029370192f019270186f0186d01867018650185f018570184f018470183f018370182f0182701e7f01e7e01e7d07d7f06d7b06d7707d7307d6f04d6d07d6b05d6907d6704d6507d6305d6102c7f03c7b02c7703c7302c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5303b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f07b6e03b6d07b6c03b6b03b6a03b6903b6803b6707b6603b656236403b6303b6203b6103b6003b5f05b5e03b5b03b5a03b5704b5603b5303b5201a7b01a7a01a7901a7706a7601a7301a7101a6706a6601a6501a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310797f069770796f0796d079670b9651095f0e9570394f029470393f0393d03937561350192f019270187f018770186f0186d01867018650185f018570184a01847028460183702836018350182f0182710d6f07d6e0dd6b06d6a0dd6706d6610d6307d6204c6f05c6b04c6705c6303c5f03c5d01c5b01c5901c5701c5501c5301c5102b6f03b6b02b6703b6302b5f02b5d01b5701b5501b5302b4f03b4b01b4703b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a331796f0d9671095f0b95d109570b9550594f049470393f029370192f019270186f018670185f0185d01857018550184f018470183f018370182f0182704e7f05e7b04e7705e7305d7f07d7e05d7b05d7a05d7706d7605d7305d7201d6f01d6e01d6d02c7f03c7b02c7703c7302c6f03c6b02c6703c6302c5f02c5d03c5b03c5902c5702c5503c5303c5103b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f05b6e03b6b03b6a03b6704b6603b6303b6203b5f05b5e03b5d05b5c03b5b03b5a03b5903b5803b5705b5603b556035403b5303b5203b5103b5001a7f01a7b01a7701a7301a6b01a6a01a6901a6704a6601a6301a6101a5704a5601a5501a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a315c17f0d9770596f049670595f0595d059570b9550394f029470393f0393d03937551350192f019270187f018770186f018670185f0185d01857018550184a01847028460183702836018350182f01827 20 1048575 8 255 11 2047 20 1048575
def cc_56_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x8cd608b11c8535e80b487eb2079a5171b7f6cd4e67e4f637475b87f565534e48149a4a482184691944722420273a77938027307792dc2b28953207821f90e19d5c13f5e0e15e09948078210294f00029 0x7d7f06d7b06d7707d7307d6f04d6d07d6b05d6907d6704d6507d6305d6102c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b07c6a02c690dc6802c6702c6602c6502c6402c6307c6202c6107c6002c5f02c5e02c5b04c5a02c5702c5602c5305c5202b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5307a7f01a7b06a7701a7307a6f07a6d01a6b01a6907a6709a6501a6301a6109a5f01a5b09a5701a5302a4f09a4d01a4b01a4902a4702a4501a4301a4102a3f03a3d01a3b02a3702a3501a330294e0293e06876068660284e9f04c04d6d05d6904d6505d6102c6d02c6902c6502c6102b6d02b6902b6502b6101b4e01b4d07a6d0ca690aa6507a6102a4e02a3e02a3902a3203a310294e0192e06876068660284e07d7f06d7b06d7707d7307d6f04d6d07d6b05d6907d6704d6507d6305d6107c7f03c7b06c7703c7307c6f02c6d03c6b03c6907c6702c6503c6303c6109c5f03c5b09c5703c5307b7f07b7e06b7b06b7a06b7706b7607b7307b7207b6f07b6e07b6d07b6c07b6b07b6a0cb690cb6807b6707b660ab650db6407b6307b6207b6107b600cb5f05b5e0cb5b04b5a0cb5704b560cb5305b5203b4f03b4e09b4b02b4a09b4702b4603b4303b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4a01a479d24601a430193e0192e068760686607c6f06c6b06c6707c6307c5f04c5d07c5b05c5907c5704c5507c5305c5107b6f03b6b06b6703b6307b5f02b5d03b5b03b5907b5702b5503b5303b51a834f03b4b0eb4703b4307a6f01a6b06a6701a6307a5f07a5d01a5b01a5907a570da5501a5301a51a624f01a4b0ea4701a4303a3f01a3ba323701a330796f069670795f0795d079570d955a014f0e9470393f9e1370192f9c1270686a06867068660685706856068550d84f0d8470383f038370182f0182706d6f06d6b06d6706d6303c6f03c6b03c6703c6303c5f03c5b03c5703c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b430696e068660585e048560384e028460183e0183602d6f02d6e02d6702d6302d6203c6f05c6b04c6705c6303c5f03c5d03c5b03c5904c5704c5503c5303c5102b6f02b6b02b6702b6302b5f02b5d02b5b02b5902b5702b5502b5302b5102b4f02b4b02b4702b4306a6f01a6b06a6701a6309a5f09a5d01a5b01a5909a5709a5501a5301a5105a4f01a4b04a4701a4302a3f01a3b02a3701a330696f069670895f0895d08957089550594f049470293f029370192f089270386f0686e02867038620385f0385d02857028550384f038470283f028370182f018270381a0881604d7f04d7d05d7b05d7904d7704d7505d7305d7104d6f05d6b04d6705d6302c7f06c7e02c7d9947c02c7b02c7a02c7902c7802c7706c7602c7506c7402c7302c7202c7102c7002c6f06c6e02c6b02c6a02c6706c6602c6302c6202c5f03c5e02c5d02b7f02b7e02b7d02b7c02b7b02b7902b7702b7502b7303b7202b7103b7002b6f02b6b02b6702b6302b5b03b5a02b5902b5702b5602b5302b5102b4702b4602b4506a7f09a7d01a7b01a7906a7706a7501a7301a7106a6f01a6b06a6701a6305a5f01a5b04a5701a5302a4f02a4d01a4b01a4902a4709a4501a4301a4102a3f01a3b02a3701a330697f0897d06977069750696f069670595f049570294f0294d02947089450293f029370192f089270387f0687e0387d0386f0686e038620385f038570284f0284d02847038450283f028370182f018270381a0881601d6f01d6e01d6701d6301d6206c6f06c6b06c6706c630ac5f04c5d0ac5b05c590ac5704c550ac5305c5106b6f03b6b06b6703b6309b5f02b5d03b5b03b5909b5702b5503b5303b5109b4f03b4b09b4703b4301a6f01a6b01a6a01a6706a6601a6301a5706a5601a5501a4f9524e01a4b01a4701a4301a4201a3f01a3b01a3701a330696f069670895f0895d08957089550894f089470393f089370192f019270186f018670185f0185d01857018550184f018470183f018370182f0182d018270182505d6f05d6e01d6701d6301d6201c6f05c6b04c6705c6301c5f01c5d01c5b01c5904c5704c5501c5301c5106b6f03b6b06b6703b6309b5f02b5d03b5b03b5909b5702b5503b5303b5105b4f03b4b04b4703b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330696f069670895f0895d08957089550594f049470393f089370192f019270186f018670185f0185d01857018550184f018470183f018370182f018270181a0881601d6f01d6701d6304c6f05c6b04c6705c6304c5f04c5d05c5b05c5a04c570ac5604c5505c5305b6f05b6b05b6a05b6706b6605b6304b5f04b5d05b5b05b5a05b5706b5604b5504b5405b5301b4f01b4e01b4d06a6f03a6b06a6703a6309a5f03a5b09a5703a5305a4f03a4b04a4703a4305a3f03a3b05a3703a330696f069670895f089570594f049470593f059370392f089270186f018670185f018570184f018470183f0183d01837018350182f0182704d7f04d7d05d7b05d7904d7704d7505d7305d7104d6f05d6b04d6705d6305c7f06c7e05c7d9647c05c7b05c7a05c7905c7805c7706c7605c7506c7405c7305c7205c7105c7005c6f06c6e05c6b05c6a05c6706c6605c6305c6201c5f01c5e01c5d06b7f02b7d03b7b03b7906b7702b7503b7303b7106b6f03b6b06b6703b6305b5f03b5b04b5703b5305b4f02b4d03b4b03b4905b4702b4503b4303b4101a7f06a7e01a7d9527c01a7b01a7901a7701a7501a7301a7201a7101a7001a6f01a6b01a6701a6301a5b01a5a01a5901a5704a5601a5301a5101a4704a4601a4501a3f01a3b01a3701a330697f0897d06977069750696f069670595f049570594f0594d05947089450393f089370192f019270187f0687e0187d0186f0686e018620185f018570184f0184d01847018450183f018370182f018270181a0881606d6f06d6b06d6706d6302c6f02c6b02c6701c6302c5f02c5b02c5702c5302b6f02b6e01b6701b6301b621eb5f05b5e0eb5b04b5a0eb5704b561eb5305b5202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310696f069670895f089570294f029470893f0893d08937089350192f019270186f0686e01867018620185f018570184f018470183f0183d01837018350182f0182d01827018250181a0881606d7f04d7d06d7b05d7906d7704d7506d7305d7106d6f06d6b06d6706d6302c7f02c7e02c7d02c7c02c7b06c7a02c7906c7802c7702c7602c7502c7402c7306c7202c719347002c6f02c6e02c6b06c6a02c6702c6602c6306c6202c5f02c5e02c5b04c5a02c5702c5602c5305c5202b7f02b7d02b7b02b7902b7702b7502b7302b7102b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4e01b4d01a7f01a7d01a7b01a7901a7701a7501a7301a7101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a310697f0897d06977069750696f069670895f089570294f0894d02947029450293f0393d02937029350192f0192d01927089250187f0687e0187d0186f0686e018620185f018570184f0184d01847018450183f018370182f0182d01827018250181a0881606c6f04c6d06c6b05c6906c6704c6506c6305c6106c5f06c5b06c5706c5306b6f02b6d03b6b03b6906b6702b6503b6303b6106b5f03b5b06b5703b539834f03b4b0eb4703b4306a6f9726d01a6b01a6906a6706a6501a6301a6106a5f01a5b06a5701a539424f01a4b0ea4701a4303a3f01a3b9223701a330696f0896d06967069650695f069570894f089470393f089370192f089270686f0686e0786d0685f0685e068520d84f0d8470383f038370182f018270881a0881607c5f06c5b06c5707c5303b5f03b5b03b5703b5303b4f03b4b03b4703b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a3307c5f06c5b06c5707c5303b5f03b5b03b5703b5303b4f03b4b03b4703b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330685607d6f06d6b06d6707d6303c6f03c6b03c6703c6303c5f03c5b03c5703c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b43069660786e0585e048560384e028460183e018369002c8f02403e7e04d6d05d6904d6505d6107c7e05c7a06c7605c720ec6e05c6d0ec6c05c6a05c6905c680bc6605c650bc6405c6205c6105c6002b6502b4d02b4902b4502b4109a6d01a6909a6501a6105a4d01a4909a4501a410797e0296e02936048560484602e7f03e7e02e7d04d7f05d7b04d7705d7302d6f02d6d02d6b05d6902d6704d6502d6302d6105c7f07c7e05c7b05c7a05c7706c7605c7305c7202c6f02c6e02c6d02c6c02c6b02c6a05c6905c6802c6702c6605c650ec6402c6302c6202c6102c6002b7b03b7a02b7902b7702b7602b7302b7102b6702b6602b6502b5f02b5b02b5702b5302b4f02b4d02b4b02b4902b4702b4502b4302b4107a7f01a7b06a7701a7302a6f02a6d01a6b01a6902a6709a6501a6301a6105a5f01a5b04a5701a5305a4f05a4d01a4b01a4905a4709a4501a4301a4102a3f01a3b02a3701a330797f069770296f0296d029678d1650595f049570594f0594d059470e9450293f029370192f099270387f038770286f0286d02867038650385a03857048560384704846038450283f028370182f0182701e7e04d6d05d6904d6505d6107c7e05c7a06c7605c720ec6e05c6d0ec6c05c6a05c6905c680bc6605c650bc6405c6205c6105c6002b6d03b6902b6503b6102b4d03b4902b4503b4101a6501a4d01a4901a4501a410797e0796e01926048560484601e7f01e7e01e7d04d7f05d7b04d7705d7304d6f04d6d05d6b05d6904d6704d6505d6305d6105c7f07c7e05c7b05c7a05c7706c7605c7305c7205c6f07c6e05c6d07c6c05c6b05c6a05c6905c6805c6707c6605c650ec6405c6305c6205c6105c6007b7f03b7b06b7703b7307b6f02b6d03b6b03b6907b6702b6503b6303b6105b5f03b5b04b5703b5305b4f02b4d03b4b03b4905b4702b4503b4303b4101a7b01a7a01a7901a7706a7601a7301a7101a6706a6601a6501a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330797f069770796f0796d079678b1650595f049570594f0594d059470e9450393f099370192f019270187f018770186f0186d01867018650185a01857048560184704846018450183f018370182f0182707d7e05d7a06d7605d7207c7e06c7a06c7607c7205c6e04c6a04c6605c6205c5e05c5d05c5c05c5a0bc590bc5805c560ec550ec5405c5205c5105c5002b5d02b5902b5502b5101b4d01a5d01a5901a5501a5101a4d1597e0596e0595e0595c029460293601926048660485604d6f05d6b04d6705d6305c6f07c6e05c6b05c6705c6305c620fb6f0db6b0db670fb6305b5f05b5d04b5b04b5a04b5704b560eb5502b5302b4f02b4d04b4b04b4a02b4702b4602b4502b4402b4302a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f02a4d02a4b02a4702a4502a4301a3f01a3701a330196f0196b01967019630195f0195b01957019530194f0194d0194b0194701945019430193f01937019330192f0192b01927019231886f0d8670585f048570584f0584d058470e8450f83f0f8370282f028270181f0181704e7f05e7b04e7705e7305d7f07d7e05d7b05d7a05d7706d7605d7305d7202c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6b04c6a02c6702c6602c6305c6202c5f02c5e02c5d02c5c02c5b05c5a02c590ec5802c5702c5602c5502c5402c5305c5202c5105c5002b7f02b7b02b7702b7302b6f02b6b02b6702b6302b5f02b5d02b5b02b5902b5702b5502b5302b5101b4f01b4e01b4d01a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a318617f0d9770596f049670595f0595d059570e9550294f8914d02947029450293f0393d02937029350192f0192d019270a9250187f018770186a01867048660185704856018550184f0284e0184d8804c0184701845018420183f018370182f0182d018270182507d7c05d7808d7405d7002c7c08c7802c7407c7002c5c0ec5802c5405c501594c1884c04d7f05d7b04d7705d7304d6f04d6d05d6b05d6904d6704d6505d6305d6105c7f07c7e05c7b05c7a05c7706c7605c7305c7205c6f07c6e05c6d07c6c05c6b05c6a05c6905c6805c6707c6605c6508c6405c6305c6205c6105c6007b7f03b7b06b7703b7307b6f02b6d03b6b03b6907b6702b6503b6303b6105b5f03b5b04b5703b5305b4f02b4d03b4b03b4905b4702b4503b4303b4107a7f01a7b06a7701a7307a6f07a6d01a6b01a6907a6708a6501a6301a6105a5f01a5b04a5701a5305a4f05a4d01a4b01a4905a470ea4501a4301a4103a3f01a3b8623701a330697606966048560484604e7f05e7b04e7705e7305d7f07d7e05d7b05d7a05d7706d7605d7305d7202c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6b04c6a02c6702c6602c6305c6202c5f02c5e02c5d02c5c02c5b05c5a02c590ec5802c5702c5602c5502c5402c5305c5202c5105c5002b7f02b7b02b7702b7302b6f02b6b02b6702b6302b5f02b5d02b5b02b5902b5702b5502b5302b5109a7f01a7b08a7701a7305a6f01a6b04a6701a6305a5f05a5d01a5b01a5905a5709a5501a5301a5102a4f09a4d01a4b01a4902a4702a4501a4301a4102a3f03a3d01a3b02a3702a3501a330294e0293e048660485604e7f05e7b04e7705e7305d7f07d7e05d7b05d7a05d7706d7605d7305d7209c7f03c7b08c7703c7305c6f03c6b04c6703c6305c5f02c5d03c5b03c5905c5702c5503c5303c510ab7f07b7e08b7b06b7a08b7706b760ab7307b7205b6f05b6e04b6b04b6a04b6704b6605b6305b6205b5f05b5e05b5d05b5c05b5b05b5a0ab590cb5805b5705b560ab550eb5405b5305b5205b5105b5003b4f03b4e09b4b02b4a09b4702b4603b4303b4201a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4a01a470aa4601a430193e0192e048660485604d6f05d6b04d6705d6305c6f07c6e05c6b05c6a05c6706c6605c6305c628c36f03b6b0db6703b6305b5f03b5b04b5703b5305b4f02b4d03b4b03b4905b4702b4503b4303b418a26f01a6b0da6701a6305a5f01a5b04a5701a5305a4f05a4d01a4b01a4905a470ea4501a4301a4103a3f01a3b8723701a338516f0d9670595f049570594f0594d059470e9450393f841370192f831270d86f0d8670485a04857048560484704846048450383f038370182f0182704d6f04d6b04d6704d6303c6f03c6b03c6703c6303c5f03c5b03c5703c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b430495e019360786e06866048560384e028460183e0183604d6f03d6b04d6704d6303c6f03c6e03c6b03c6a04c6704c6603c6303c6202c5f02c5e02c5702c5302c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4f02b4d02b4b02b4902b4702b4502b4302b4107a6f01a6b06a6701a6304a5f01a5b04a5701a5309a4f09a4d01a4b01a4909a4709a4501a4301a4102a3f01a3b02a3701a330796f069670495f049571294f0b94d129470b9450293f029370192f099270386f038670385f028570384f0384d02847028450283f028370182f018270381a1481603e7e04d7e06d7a04d7607d7204d6e04d6d04d6c0bd6a04d690bd6804d6604d6504d6415d6204d6112d6004c6d04c6904c6504c6102b6502b5d02b5902b5502b5109a6d01a6909a6501a6109a5d01a5904a5501a510797e0296e029360485e0484e098260b014 20 1048575 8 255 11 2047 20 1048575
def cc_56_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9354a8e05585e828144a7ca4a775556f3826a94a65f4a5e07f5964a54c4a4f7554758244b2a404473ba4a3a21838a1836822341272ee532727c249291d0791a52b152530d0820a92709b0e03f5c0003f 0x4d6f05d6b04d6705d6304c6f01c6b06c6707c6305c5f01c5b04c5705c5307b6f06b6b06b6707b6305b5f04b5b04b5705b5309b4f02b4d0ab4b09b4702b450ab4307a6f07a6e06a6b06a6707a6307a6205a5f05a5e04a5b04a5705a5305a5205a4f05a4e05a4705a4305a420aa3f09a3b02a3a09a3702a360aa330796f069670595f049570894f0a94e05947089420893f089370192f0192e0192d0786f068670585f048570a84f0a8471083f098370a82f0c82d0a8270a82504d6f05d6b04d6705d6304c6f06c6707c6305c5f04c5705c5307b6f06b6b06b6707b6305b5f04b5b04b5705b5309b4f0bb4b09b470bb4307a6f07a6e06a6b06a6707a6307a6205a5f05a5e04a5b04a5705a5305a5205a4f05a4e01a4b01a4905a4705a4305a4201a4101a400aa3f09a3b02a3a09a3702a360aa330796f0196b06967019630595f0195b04957019530a94f0a94e0194b0194905947019430b942019410993f0193b0b93a099370a936019330786f068670585f048570b84f0b8470b83f098370a82f0c82d0a8270a8250181f0181704e7f04e7d05e7b05e7a04e7706e7604e7504d7f04d7e04d7d05d6f05d6e05d6d07c7f06c7b06c7707c7305c6f04c6b04c6705c6305c5f02c5d05c5b03c5905c5702c5505c5303c5107b7f07b7e06b7b06b7a06b7706b7607b7307b7205b6f05b6e04b6b04b6a04b6704b6605b6305b6205b5f05b5e05b5d05b5c05b5b05b5a0ab590cb5805b5705b560ab55bf35405b5305b5205b5105b500ab4f03b4e09b4b02b4a09b4702b460ab4303b4207a7f01a7b06a7701a7305a6f01a6b04a6701a6305a5f05a5d01a5b05a5a01a5901a5805a5705a560aa55be25401a5301a5109a4f01a4b0ca4a09a470aa4601a430797f069770596f049670595f0595d0595a059570595608955bd1540894f089470193f0193e0193d0192f0192e019220787f068770586f048670585f0585d058571d8551084f098470a83f0c83d0a8370a8350182f0182707d6f06d6b06d6707d6302c6f03c6b02c6703c6302c5f03c5b02c5703c5302b6f02b6e06b6b06b6a06b6706b6607b6302b620ab5f05b5e0ab5b04b5a0ab5704b560ab5305b5203b4f03b4e02b4b02b4a02b4702b4603b4303b4207a6f01a6b06a6701a6309a5f01a5b09a5701a5303a4f01a4b02a4701a4309a3f0aa3e09a3d0796f069670895f089570394f029470893f0a93e0893d0192f039270386f038670385f038570384f028470383f0383d03837038350182f0182707d6f06d6b06d6707d6302c6f03c6b02c6703c6302c5f03c5b02c5703c5302b6f01b6b06b6707b630ab5f0ab5b0ab570ab5303b4f01b4b01b4a02b4701b4603b4307a6f07a6e06a6b06a6707a6307a620aa5f0aa5b04a5a0aa5704a560aa5303a4f03a4e02a4b02a4703a4303a4203a3f03a3e03a3703a3303a320796f069670895f089570394f029470893f0a93e03937089320192f0192e0192d0386f038670385f038570384f028470383f038370382f0382d038270382507d6f06d6b06d6707d6302c6f03c6b02c6703c6302c5f03c5b02c5703c5302b6f06b6707b630bb5f0bb5b0bb570bb5303b4f02b4703b4307a6f07a6e06a6b06a6707a6307a620ba5f0ba5b04a5a0ba5704a560ba5303a4f03a4e02a4b02a4703a4303a4203a3f03a3e01a3b01a3903a3703a3303a3201a3101a300796f0196b06967019630995f0195b09957019530394f0194b0294a0294702946019430993f0b93e0193b01939039370193309932019310386f038670385f038570384f028470383f038370382f0382d03827038250181f0181707e7f06e7b06e7707e7302d7f02d7d03d7b03d7a02d7706d7602d7502d6f03d6b02d6703d6302c7f02c7e02c7d03c6f05c6e03c6b03c6a03c6704c6603c6303c6203c5f03c5e03c5d07b7f07b7e06b7b06b7a06b7706b7607b7307b720bb6f05b6e0bb6b04b6a0bb6704b660bb6305b6203b5f03b5e02b5b02b5a02b5702b5603b5303b5203b4f03b4e03b4d03b4c03b4b03b4a0bb490cb4803b4703b460ab45bb34403b4303b4203b4103b4007a7f01a7b06a7701a7309a6f01a6b09a6701a6303a5f01a5b02a5a02a5702a5601a5303a4f03a4d01a4b03a4a01a4901a4803a4703a4609a45ba24401a4301a410797f069770896f089670395f029570394f0394d0394a039470394608945b91440193f0193e0193d0192f0192e019220387f038770386f038670385f028570384f0384d03847038450383f0383d03837038350182f0182704d6f04d6b04d6704d6302c6f03c6b02c6703c6302c5f03c5b02c5703c530ab6f07b6e08b6b06b6a08b6706b660ab6307b6204b5f04b5e04b5b02b5a02b5702b5604b5304b5203b4f03b4e02b4b02b4a02b4702b4603b4303b4209a6f01a6b08a6701a6304a5f01a5b04a5701a5303a4f01a4b02a4701a4309a3f0aa3e09a3d0896f089670495f049570394f029470a93f0a93e0b93d0192f039270386f038670385f038570384f028470383f0383d03837038350182f0182704d6f04d6b04d6704d6302c6f03c6b02c6703c6302c5f03c5b02c5703c530ab6f08b6b08b670ab6304b5f04b5b02b5701b5303b4f01b4b01b4a02b4701b4603b430aa6f07a6e08a6b08a670aa6307a6204a5f04a5b04a5a04a5704a5604a5303a4f03a4e02a4b02a4703a4303a4203a3f03a3e03a3703a3303a320896f089670495f049570394f029470a93f0a93e039370a9320192f0192e0192d0386f038670385f038570384f028470383f038370382f0382d038270382504e7f04e7b04e7704e7302d7f03d7b02d7703d7302d6f04d6e02d6d02d6702d6503d6303d6203c7f07c7e03c7b03c7a03c7706c7603c7303c7202c6702c6602c6503c5f03c5e03c5d0ab7f07b7e08b7b06b7a08b7706b760bb7307b7204b6f04b6e04b6b04b6a04b6704b6604b6304b6203b5f03b5e02b5b02b5a02b5702b5603b5303b5203b4f03b4e03b4d03b4c03b4b03b4a0bb490cb4803b4703b460ab45b734403b4303b4203b4103b4009a7f01a7b08a7701a7304a6f01a6b04a6701a6303a5f01a5b02a5a02a5702a5601a5303a4f03a4d01a4b03a4a01a4901a4803a4703a4609a45b624401a4301a410897f089770496f049670395f029570394f0394d039470b9450193f0193e0193d0192f0192e019220387f038770386f038670385f028570384f0384d03847038450383f0383d03837038350182f0182704d6f05d6b04d6705d6302c6f03c6b02c6703c6302c5f03c5b02c5703c530ab6f07b6e08b6b06b6a08b6706b660ab6307b6202b5f02b5e04b5b04b5a04b5704b5605b5302b5203b4f03b4e02b4b02b4a02b4702b4603b4303b4209a6f01a6b08a6701a6305a5f01a5b04a5701a5303a4f01a4b02a4701a4309a3f0aa3e09a3d0896f089670595f049570394f029470a93f0a93e0b93d0192f039270386f038670385f038570384f028470383f0383d03837038350182f0182704d6f05d6b04d6705d6302c6f03c6b02c6703c6302c5f03c5b02c5703c530ab6f08b6b08b670ab6302b5f01b5b04b5705b5303b4f01b4b01b4a02b4701b4603b430aa6f08a6b06a6a08a6706a660aa6305a5f05a5e04a5b04a5705a5305a5203a4f03a4e02a4b02a4703a4303a4203a3f03a3e03a3703a3303a320896f089670595f049570394f029470a93f0a93e039370a9320192f0192e0192d0386f038670385f038570384f028470383f038370382f0382d038270382504d6f05d6b04d6705d6302c6f03c6b02c6703c6302c5f03c5b02c5703c530bb6f08b6b08b670bb6302b5f04b5705b5303b4f02b4703b430aa6f08a6b06a6a08a6706a660aa6305a5f05a5e04a5b04a5705a5305a5203a4f03a4e02a4b02a4703a4303a4203a3f03a3e01a3b01a3903a3703a3303a3201a3101a300996f0196b08967019630595f0195b04957019530394f0194b0294a0294702946019430993f0a93e0193b01939039370193309932019310386f038670385f038570384f028470383f038370382f0382d03827038250181f0181704e7f05e7b04e7705e7302d7f03d7b02d7703d7302d6f02d6d03d6b03d6a02d6704d6602d6503c7f07c7e03c7b03c7a03c7706c7603c7303c7202c6f02c6e02c6d03c5f03c5e03c5d0ab7f07b7e08b7b06b7a08b7706b760ab7307b7205b6f05b6e04b6b04b6a04b6704b6605b6305b6203b5f03b5e02b5b02b5a02b5702b5603b5303b5203b4f03b4e03b4d03b4c03b4b03b4a0ab490cb4803b4703b460ab45b434403b4303b4203b4103b4009a7f01a7b08a7701a7305a6f01a6b04a6701a6303a5f01a5b02a5a02a5702a5601a5303a4f03a4d01a4b03a4a01a4901a4803a4703a4609a45b324401a4301a410897f089770596f049670395f029570394f0394d0394a03947039460b945b21440193f0193e0193d0192f0192e019220387f038770386f038670385f028570384f0384d03847038450383f0383d03837038350182f0182705e7e04e7d06d7a04d7904d7604d7104d6604d6502c6d02c6902c6502c6102c5902c5102b6d02b6902b6502b6101b4e01b4d04a6d0aa690aa6504a6102a4e02a4202a3e02a3902a320aa310496d089650294e029420893d029350192e0192d0486d0e8650c82d0a825b056f08d6b08d670ad6302c6f02c6b02c6702c6302c5f02c5b02c5702c5302b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4e01b4d0aa6f08a6b08a670ca630aa5f0aa5b0aa570aa5302a4f02a4e02a4702a4302a4202a3f02a3e02a3b02a3902a3702a3302a320ca310896f089670a95f0b9570294f0294e02947029420293f0c93d02937029350192f0192e0192d9d06f088670a85f680570284f028470283f028370c82f0c82d0a8270d025c056f08d6b08d67bc56309c6f08c6b08c67b846309c5fb545b09c57b14530cb6f07b6e08b6b06b6a08b6706b660cb6307b620cb5f05b5e0cb5b04b5a0cb5704b560cb5305b520cb4f03b4e09b4b02b4a09b4702b460cb4303b420ca6f01a6b08a6701a630ca5f01a5b0ca5701a5309a4f01a4b0ca4a09a47af24601a430896f089670c95f0c9570c94f099470193f0193e0193d0192f0192e019229c06f088678305f670574f04f098470c83f0c83d0c8370c0350182f0182708c5f08c5b08c5708c5303b5f03b5b03b5703b5303b4f03b4b03b4703b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a3308c5f08c5b08c5708c5302b5f02b5b02b5702b5302b4f02b4b02b4702b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a3308d6f08d6b08d6708d6308c6f08c6b08c6708c6309c5f09c5b09c5709c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a360796e069660595e049560394ead14c02946ac1440193e04d6d05d6904d6505d6107c7e06c7a06c7607c7207c6e07c6d07c6c07c6a0dc690dc6807c660bc650bc6407c6207c6107c6003c5e02b6d02b6902b6502b6102b4507a6d01a6909a6501a6109a4d01a4909a4501a410595e0294e02936068760686604c6f05c6b04c6705c6304c5f05c5b05c5904c5705c5305c5102b6f06b6b06b6a0db6906b6706b6607b6307b6102b5f02b5b02b5a02b5902b5806b5706b5602b5302b5103b4f03b4703b4302a6f02a6b02a6702a6302a5f02a5d02a5b02a5702a5502a5302a4f02a4b02a4702a4302a3f02a3b02a370796f0196b06967019630795f0795d0195b0795709955019530594f0194b04947019430993f0193b09937019330292f0192b02927019230786f068670785f0785d078570d8550584f048470f83f0f8370282f028270181f0981704d7f05d7b04d7705d7304d6f04d6d05d6b05d6904d6704d6505d6305d6102c7f07c7e02c7b02c7a02c7706c7602c7302c7202c6f07c6e02c6d07c6c02c6b02c6a02c6902c6802c6707c6602c650dc6402c6302c6202c6102c6002c5f03c5e02c5d02b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5b03b5a02b5902b5702b5602b5302b5102b4702b4602b4507a7f01a7b06a7701a7307a6f07a6d01a6b01a6907a6709a6501a6301a6105a5f01a5b04a5701a5302a4f02a4d01a4b01a4902a4709a4501a4301a4102a3f01a3b02a3701a330797f069770796f0796d079670d9650595f049570294f0294d02947aa1450293f029370192f099270387a03877068760386706866038650385f038570284f0284d0284a028470284603845a90440283f028370182f0182704d6d05d6904d6505d6107c7e06c7a06c7607c7207c6e07c6d07c6c07c6a0dc690dc6807c660bc650bc6407c6207c6107c6001c5e02b6d03b6902b6503b6102b4d03b4902b4503b4101a6d01a6901a6501a6101a450595e0594e0192606876068661184e0f84c04d7f05d7b04d7705d7304d6f04d6d05d6b05d6904d6704d6505d6305d6105c7f07c7e05c7b05c7a05c7706c7605c7305c7205c6f07c6e05c6d07c6c05c6b05c6a05c6905c6805c6707c6605c650dc6405c6305c6205c6105c6001c5f01c5e01c5d07b7f03b7b06b7703b7307b6f02b6d03b6b03b6907b6702b6503b6303b6105b5f03b5b04b5703b5305b4f02b4d03b4b03b4905b4702b4503b4303b4101a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5b01a5a01a5901a5704a5601a5301a5101a4704a4601a4501a3f01a3b01a3701a330797f069770796f0796d079670d9650595f049570594f0594d05947a71450393f099370192f019270187a01877068760186706866018650185f018570184f0184d01847018450183f018370182f0182704d6d05d6904d6505d6107c7e06c7a06c7607c7207c6e07c6d07c6c07c6a0bc690bc6807c660dc650dc6407c6207c6107c6005c5e04c5a04c5605c5202b6d02b6902b6502b6101b4d01a6d01a6901a6501a6101a4d0797e0796e0796c1595e029460293601926068760686607c6f06c6b06c6707c6307c5f07c5b05c5907c5707c5305c5107b6f07b6d06b6b06b6a06b6706b660db6502b6302b5f02b5d06b5b06b5a02b5702b5602b5502b5402b530fb4f0eb4b0eb470fb4302a6f02a6b02a6702a6302a5f02a5d02a5b02a5702a5502a5302a4f02a4b02a4702a4301a3f01a3701a330196f0196b01967019630195f0195d0195b0195701955019530194f0194b01947019430193f01937019330192f0192b01927019230786f068670785f0785d078570d8551c84f0e8470f83f0f8370282f028270181f0181707d7f06d7b06d7707d7307d6f04d6d07d6b05d6907d6704d6507d6305d6102c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b07c6a02c690dc6802c6702c6602c6502c6402c6307c6202c6107c6002c5f02c5e02c5b04c5a02c5702c5602c5305c5202b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5301b4f01b4e01b4d01a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a310797f069770796f0796d079670d965a115f0e9570294fa514d02947029450293f0393d02937029350192f0192d019279d1250187a01877068760186706866018650185f018570184f0284e0184da404c0184701845018420183f018370182f0182d018270182507d7e06d7a06d7607d7207d6e07d6d07d6c07d6a0dd690dd6807d660ad650ad6407d6207d6107d6004c6d05c6904c6505c6101c5d02b6d03b6902b6503b6102b5d03b5902b5503b5101a6d01a6901a6501a6105a5e01a5d05a4e01a42068760686607d7c05d780dd7405d7002c7c0dc7802c7407c7002c5c1fc5802c5405c501594c1c84c04d7f05d7b04d7705d7304d6f04d6d05d6b05d6904d6704d6505d6305d6105c7f07c7e05c7b05c7a05c7706c7605c7305c7205c6f07c6e05c6d07c6c05c6b05c6a05c6905c6805c6707c6605c650dc6405c6305c6205c6105c6007b7f03b7b06b7703b7307b6f02b6d03b6b03b6907b6702b6503b6303b6105b5f03b5b04b5703b5305b4f02b4d03b4b03b4905b4702b4503b4303b4107a7f01a7b06a7701a7307a6f07a6d01a6b01a6907a670aa6501a6301a6105a5f01a5b04a5701a5305a4f05a4d01a4b01a4905a47a224501a4301a4103a3f01a3ba123701a330495604946068760686607c6f06c6b06c6707c6307c5f07c5b07c5707c5307b6f07b6d06b6b06b6a06b6706b6608b6502b6302b5f02b5d06b5b06b5a02b5702b5602b5502b5402b530fb4f0eb4b0eb470fb4302a6f02a6b02a6702a6302a5f02a5d02a5b02a5702a5502a5302a4f02a4b02a4702a430796f0196b06967019630795f0195b07957019530994f0194b09947019430993f0193b09937019330292f0192b0292701923 20 1048575 8 255 11 2047 20 1048575
def cc_56_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x8b0668664a846207f94d77a7f72b4f6d4576a72d621865bb6655368522314ef334a54a48d1847518453224064d38b7b345462f4512757f22b4a2002b1c33d19b281702b1313f111200c74a04c7b0004c 0x4e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7302c7f03c7b02c7703c7302c6f04c6e02c6d02c6c03c6b03c6902c6702c6503c6303c6203c6103c6002c5f03c5b02c5703c5303b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f04b6e02b6d02b6c03b6b03b6a03b6903b6802b6702b6602b6502b6403b6303b6203b6103b6003b5f04b5e03b5d05b5c03b5b03b5a03b5704b5603b5504b5403b5303b5208a7f08a7b08a7708a7304a6f0ca6d04a6b01a6904a6704a6504a6301a6104a5f04a5b04a5704a5303a4f03a4d02a4b02a470ca4503a4303a3f03a3d03a3b01a3903a370ca3503a3301a310496e0495e0294602936ee56f08d6b08d67ec56302c6f03c6b02c6703c6302c5f03c5b02c5703c5303b6f07b6e03b6b03b6a03b6706b6603b6303b6203b5f05b5e03b5b03b5a03b5704b5603b5303b52ea26f08a6b08a6709a63e825f09a5be525709a5303a4f03a4d02a4b02a47e324503a4303a3f03a3d03a3b01a3903a37e023503a3301a310896f08967df15fde1570294a02947029460293702936029350992f0c9270386f038670385f038570384f028470383f0383d03837038350382f0382708d6f08d6b08d6708d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5308b6f08b6b08b6708b6309b5f09b5b09b5709b5302b4f02b4b02b4702b4302a4e0796e069660595e04956029460193e0993602d6f04d6b04d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5302b6f02b6e02b6b02b6a02b6702b6605b6305b6202b5f02b5e04b5b04b5a02b5702b5602b5302b5202b4f02b4e02b4702b4302b4207a6f06a6b06a6707a6304a5f04a5b04a5704a5302a4f02a4b02a4702a4309a3f09a3d09a3b01a3909a3709a3509a3301a310796f069670495f049570294f029470393f0393d04937039350892f089270786f068670485f048570284f028470e83f0e83d0e8370e8350982f0982704e7f05e7e04e7d04d7b06d7a04d7904d7704d7604d7304d7104d6704d6604d6502c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b04c6a02c69db46802c6702c6602c6502c6402c6304c6202c6104c6002c5f02c5e02c5b04c5a02c5904c5802c5702c5602c5304c5202c5105c5002b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5307a7f06a7b06a7707a7304a6f04a6d04a6b01a6904a6709a6504a6301a6104a5f04a5b04a5704a5302a4f09a4d02a4b01a4902a4702a4502a4301a4102a3f09a3d02a3b02a3702a3502a330797f069770496f0496d04967089650495f049570294f0294e0394d0293f0293e029320892f089270787f068770486f0486d048670e8650485f048570284f0e84d02847028450283f028370982f0982704d6f05d6b04d6702d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5302b6f02b6e02b6b02b6a02b6702b6604b6304b6202b5f02b5e02b5b02b5a02b5702b5605b5305b5202b4f02b4e02b4702b4302b4207a6f06a6b06a6707a6305a5f04a5b04a5705a5302a4f09a4d02a4b02a4702a4502a4309a3f09a3d09a3b01a3909a3709a3509a3301a310796f069670595f049570294f029470393f0393d05937039350892f089270786f068670585f048570284f028471483f0f83d148370f8350982f0982704d6f05d6b04d6702d6304c6f06c6707c6305c5f04c5705c5302b6f02b6e02b6b02b6702b6307b6202b5f02b5e02b5b02b5902b5702b5305b5202b5102b4f02b4e02b4b02b4902b4702b4305b4202b4103b4002a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f02a4e02a4b02a4902a4702a430ba4202a410796f0696b06967079630595f0495b04957059530994f0994b09947099430293f0993d0293b0293702935029330292f0992d0292b0292702925029230786f068670585f048570b84f0b8470283f1583d02837028350282f028270981f0981704d7e05d6e02c7e06c7a02c7607c7202c6e04c6a02c6605c6202c5e02c5d02c5c0fc5a02c590fc5802c5602c5502c5412c5202c5112c5002b5d02b5902b5502b5109a5d01a5909a5501a5109a4d01a4902a4501a4103a3d02a350294e0293e0787e0586e0585e0284602844028360982604e7f04e7d05e7b05e7a04e7706e7604e7504d7f04d7e04d7d05d6f05d6e05d6d02c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6b04c6a02c6904c6802c6702c6602c6305c6202c6105c6002c5f02c5e02c5d02c5c02c5b05c5a02c59d945802c5702c5602c5502c5402c5305c5202c5105c5002b7f02b7b02b7702b7302b6f02b6b02b6702b6302b5f02b5d02b5b05b5a02b5903b5802b5702b5602b5502b5402b5302b5107a7f06a7b06a7707a7305a6f04a6b04a6705a6305a5f05a5d05a5b01a5905a5709a5505a5301a5102a4f09a4d02a4b01a4902a4702a4502a4301a4102a3f09a3d02a3b02a3702a3502a330797f069770596f049670595f0595d0595a059570595608955d81540294f0294e0394d0293f0293e029320892f089270787f068770586f048670585f0585d05857d70550284fd304d02847028450283f028370982f0982704e7f05e7b04e7705e7305d7f07d7e05d7b05d7a05d7706d7605d7305d7202c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6b04c6a02c6904c6802c6702c6602c6305c6202c6105c6002c5f02c5e02c5d02c5c02c5b04c5a02c5903c5802c5702c5602c5502c5402c5303c5202c5103c5002b7f02b7b02b7702b7302b6f02b6b02b6702b6302b5f02b5d02b5b05b5a02b5903b5802b5702b5602b5502b5402b5302b5108a7f08a7b08a7708a7305a6f04a6b04a6705a6305a5f05a5d05a5b01a5905a5709a5505a5301a5102a4f09a4d02a4b01a4902a4702a4502a4301a4102a3f09a3d02a3b02a3702a3502a3304966049560294e0293e04e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7302c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b03c6a02c6903c6802c6702c6602c6502c6402c6304c6202c6103c6002c5f02c5e02c5b04c5a02c5904c5802c5702c5602c5304c5202c5105c5002b7f02b7b02b7702b7302b6f02b6e02b6d02b6c02b6b02b6902b6702b6502b6304b6202b6103b6002b5f02b5b02b5702b5308a7f08a7b08a7708a7304a6f09a6d04a6b01a6904a6704a6504a6301a6104a5f04a5b04a5704a5302a4f09a4d02a4b01a4902a4702a4502a4301a4102a3f09a3d02a3b02a3702a3502a33089760496e0495e0294e0293e0992604e7d05e7a06e7604e7504d7e04d7d05d6e05d6d07c7e06c7a06c7607c7205c6e04c6a04c6605c6205c5e05c5d05c5c05c5a0fc590fc5805c5614c5515c5405c5205c5105c5002b5d03b5a02b5903b5802b5602b5502b5402b5105a5d01a5909a5501a5109a4d01a4909a4501a4105956159540787e02846028360ed6f08d6b08d67d356314c6f07c6e08c6b06c6a08c6706c660fc6307c6215c5f05c5e0ec5b04c5a0ec5704c560fc5305c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5309a6f01a6b08a6701a6309a5f01a5b09a5701a5309a4f09a4d01a4b01a4909a4709a4501a4301a4102a3f01a3b02a3701a339f06e0284602836da56f08d6b08d67d656302c6f02c6e02c6b06c6a02c6702c6602c6307c6202c5f02c5e02c5b04c5a02c5702c5602c5305c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5309a6f08a6b08a6709a6309a5f09a5b09a5709a5302a4f09a4d02a4b01a4902a4702a4502a4301a4102a3f09a3d02a3b02a3702a3502a330896f08967d515fd41570294f0294e0394d0293f0293e029320992f099279e06f088678405f6a0570284fd204d02847028450283f028370982f0982708c5f08c5b08c5708c5302b5f03b5b02b5703b5302b4f03b4b02b4703b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a3308c5f08c5b08c5708c5302b5f03b5b02b5703b5302b4f03b4b02b4703b4308a5f08a5b08a5708a530ca4f0ca4b0ca470ca4303a3f02a3b02a3703a3308d6f08d6b08d6708d6302c6f03c6b02c6703c6302c5f03c5b02c5703c5308b6f08b6b08b6708b630cb5f09b5b0cb5709b5303b4f02b4b02b4703b4302a460796e069660595e049560394e0193ed013c0c936cf13405d6f05d6e01d6b01d6a01d6701d6601d6301d6201c6f04c6b04c6704c6301c5f01c5d01c5b01c5904c5704c5501c5301c5107b6f06b6b06b6707b6309b5f02b5d09b5b03b5909b5702b5509b5303b5104b4f04b4b04b4704b4301a6f01a6b01a6701a6301a5f01a5d01a5701a5501a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330796f069670495f0495d08957089550494f049470893f089370192f019270186f018670185f0185d01857018550184f018470183f018370182f0182704e7f05e7e04e7d04d7b06d7a04d7904d7704d7604d7304d7104d6704d6604d6507c7f06c7b06c7707c7304c6f02c6d04c6b03c6904c6702c6504c6303c6104c5f04c5b04c5704c5301b7f01b7b01b7701b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4b01b4a01b4709b4601b4301a7f07a7e01a7b01a7a01a7706a7601a7301a7201a6f04a6e01a6d04a6c01a6b01a6a01a6901a6801a6704a6601a65cd26401a6301a6201a6101a6001a5f04a5e01a5b01a5a01a5704a5601a5301a5201a4f03a4e01a4b01a4a01a4702a4601a4301a420797f069770496f0496d04967089650495f049570894f089470193a01937019360192701926089250187f018770186f0186d01867018650185f018570184f018470183f018370182f0182d018270182504d6f05d6b04d6701d6304c6f01c6b01c6701c6305c5f01c5b01c5701c5307b6f06b6b06b6707b6305b5f04b5b04b5705b5309b4f02b4d09b4b09b4702b4509b4301a6f07a6e01a6b01a6701a6301a6201a5f05a5e01a5b01a5701a5301a5201a4f11a4e01a4d01a3f01a3b01a3a01a3702a3601a330796f069670595f049570594f089470893f089370192701926089250186f018670185f018570184f018470183f018370182f0182d018270182504d6f05d6b04d6701d6304c6f04c6e01c6b01c6a01c6701c6601c6301c6205c5f05c5e01c5b01c5a01c5701c5601c5301c5207b6f06b6b06b6707b6305b5f04b5b04b5705b5309b4f02b4d09b4b03b4909b4702b4509b4303b4101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4701a4501a4301a3f01a3b01a3a01a3709a3601a330796f069670595f049570594f0594d08947089450893f089370192f0192a01927019260186f018670185f018570184f0184d01847018450183f018370182f0182704e7f04e7d05e7b05e7a04e7706e7604e7504d7f04d7e04d7d05d6f05d6e05d6d07c7f06c7b06c7707c7305c6f04c6b04c6705c6305c5f02c5d05c5b03c5905c5702c5505c5303c5101b7f01b7b01b7701b7301b6f01b6b01b6701b6301b5f01b5d01b5b01b5a01b5901b5801b5705b5601b55cb35401b5301b5101b4f01b4b01b4a01b4709b4601b4301a7f07a7e01a7b01a7a01a7706a7601a7301a7201a6f05a6e01a6b01a6a01a6704a6601a6301a6201a5f05a5e01a5d05a5c01a5b01a5a01a5901a5801a5705a5601a55ca25401a5301a5201a5101a5001a4f03a4e01a4b01a4a01a4702a4601a4301a420797f069770596f049670595f0595d05957089550894f089470193a01937019360192701926089250187f018770186f018670185f0185d01857018550184f018470183f018370182f0182d0182701825cc56f08d6b08d67c956309c6f08c6b08c6709c6309c5f09c5b09c5709c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4a01b4709b4601b4301a6f07a6e01a6b01a6a01a6706a6601a6301a6201a5f05a5e01a5b01a5a01a5704a5601a5301a5201a4f03a4e01a4b01a4a01a4702a4601a4301a420896f089670c95f0c9570994f099470193a019370193601927019260c9250186f018670185f018570184f018470183f018370182f0182d018270182504d6f04d6b04d6704d6302c6f03c6b02c6703c6302c5f02c5703c5308b6f07b6e08b6b06b6a08b6706b6608b6307b6202b5702b5603b4f03b4e08a6f01a6b08a6701a6304a5f01a5b04a5701a5303a4f01a4b02a4701a4303a3f03a3d01a3b01a3909a3709a3501a3301a3104e7f04e7b04e7704e7302d7f03d7b02d7703d7302d6f04d6e02d6d02d6702d6503d6303d6203c7f07c7e03c7b03c7a03c7706c7603c7303c7202c6702c6602c6503c5f03c5e03c5d08b7f01b7b08b7701b7304b6f01b6b04b6701b6303b5f01b5b02b5701b5303b4f03b4d01b4b01b4903b4709b4501b4301b4101a3e0797e069760496e049660395e029560394e0394c03946c71440993604d6f05d6b04d6705d6302c6f03c6b02c6703c6302c5f03c5b02c5708b6f08b6b08b6708b6302b5f03b4f08a6f01a6b08a6701a6305a5f01a5b04a5701a5303a4f01a4b02a4701a4303a3f01a3b01a3909a3701a3301a31069660595e0394e1493e0992604d6f05d6b04d6705d6302c6f03c6b02c6703c6302c5f03c5b02c5708b6f07b6e08b6b06b6a08b6706b6608b6307b6202b5f02b5e03b4f03b4e08a6f01a6b08a6701a6305a5f01a5b04a5701a5303a4f01a4b02a4701a4303a3f03a3d01a3b01a3909a3709a3501a3301a3104e7f05e7b04e7705e7302d7f03d7b02d7703d7302d6f02d6d03d6b03d6a02d6704d6602d6503c7f07c7e03c7b03c7a03c7706c7603c7303c7202c6f02c6e02c6d03c5f03c5e03c5d08b7f01b7b08b7701b7305b6f01b6b04b6701b6303b5f01b5b02b5701b5303b4f03b4d01b4b01b4903b4709b4501b4301b4103a46c524401a3e0797e069760596e049660395e029560394e0394c03946c41440993608d6f08d6b08d6708d6308c6f08c6b08c6708c6309c5fc645b09c57c345308b6f01b6b08b6701b630cb5f01b5b0cb5701b5309b4f01b4b09b4701b4301a3e0796e069660595e049560394e029460c93605d6f05d6e06d6b06d6a06d6706d6607d6305d6204c6f04c6b04c6704c6304c5f04c5d04c5b04c5904c5704c5504c5304c5107b6f06b6b06b6707b6309b5f02b5d0ab5b03b5909b5702b550ab5303b5104b4f04b4b04b4704b4307a6f01a6b06a6701a630aa5f0aa5e0aa5d04a4f01a4b04a4701a4309a3f01a3b09a3701a330796f069670895f0a95e0895d0494f049470893f089370192f049270786f068670a85f0e85d0a8570a8550484f048470b83f098370182f0182704e7f05e7e04e7d04d7b06d7a04d7904d7704d7604d7304d7104d6704d6604d6507c7f06c7b06c7707c7304c6f02c6d04c6b03c6904c6702c6504c6303c6104c5f04c5b04c5704c5307b7f07b7e06b7b06b7a06b7706b7607b7307b7204b6f04b6e04b6d04b6c04b6b04b6a0cb690cb6804b6704b660ab65c136404b6304b6204b6104b6004b5f04b5e04b5b04b5a04b5704b5604b5304b520ab4f03b4e09b4b02b4a09b4702b460cb4303b4207a7f01a7b06a7701a7304a6f04a6d01a6b01a6904a670aa6501a6301a6104a5f01a5b04a5701a5309a4f01a4b0ca4a09a47b024601a430797f069770496f0496d04967089650495f049570894f089470193f0193e0193d0192f0192e019220787f068770486f0486d048670e8650485f048570e84f098470c83f0c83d0a8370e8350182f0182704d6f05d6b04d6705d6304c6f04c6e06c6b06c6a06c6706c6607c6304c6205c5f05c5e04c5b04c5a04c5704c5605c5305c5207b6f06b6b06b6707b6305b5f04b5b04b5705b5309b4f02b4d0ab4b03b4909b4702b450ab4303b4107a6f01a6b06a6701a6305a5f01a5b04a5701a530aa4f0aa4e0aa4d09a3f01a3b0ba3a09a370aa3601a330796f069670595f049570894f0a94e0894d0893f089370192f059270786f068670585f048570a84f0f84d0a8470a8450b83f098370182f01827 20 1048575 8 255 11 2047 20 1048575
def cc_56_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xa2e4d9f03e99b55917848ca4d84d7d806477b84e73d7b6ea5366b7f6234860b185f3185d1225844d5097b4b8514397f3ea4f36f7b3204f2a57b2564f205511877e15f2811c430e6360b5310674e00067 0x4d6f04d6b04d6704d6304c6f02c6e04c6b04c6a04c6704c6602c6302c6203c5f03c5e03c5703c5303c5202b6f03b6b02b6703b6302b5f03b5b02b5703b5302b4f02b4d03b4b03b4902b4702b4503b4303b4107a6f06a6b06a6707a6304a5f04a5b04a5704a530ba4f0aa4d09a4b01a490ba470aa4509a4301a4103a3f02a3b02a3703a330796f069670495f039570594f0594d03947039450393f029370892f089270386f038670385f038570384f0384d03847038450383f028370382f0382704e7e06e7a04e7607e7202c6d03c6902c6503c6102b7e01b7a01b7602b7204b6e0ab6d0ab6c04b6a04b6904b6804b6604b6504b6404b620ab6119b6004b5e04b5a04b5604b5203b4e01b4a01b4603b4207a7e07a7209a6d04a6a01a6901a6804a6604a6504a6401a6104a5a04a5603a4e03a4203a3e03a3d0496e0596d0495e049520893d089350892d089250386d038650383d038350382d0382504d6f04d6e04d6b04d6704d6307d6204c6f04c6b04c6704c6302b6f03b6b02b6703b6302b5f04b5e03b5b03b5902b5703b5303b5203b5102b4f03b4b02b4703b4302a6f06a6707a6304a5f04a5e03a5b03a5903a5703a5303a5203a5103a5004a4f04a4e04a4b04a4903a4704a4304a420ba4103a3f02a3703a330796f0696b06967079630495f1095d0495b0495704955049530494f0494b04947049430393f0293b02937039330b92f0992b0b927099230386f038670385f0385d03857038550384f038470383f028370382f038270381f0381704e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7302c7f02c7d03c7b03c7a02c7706c7602c7502c6f04c6e02c6d02c6c03c6b03c6902c6702c6503c6303c6203c6103c6002c5f03c5b02c5703c5302b7f02b7e02b7d03b6f04b6e03b6dfe36c03b6b03b6a03b6903b6803b6704b6603b6504b6403b6303b6203b6103b6003b5f04b5e03b5d05b5c03b5b03b5a03b5704b5603b5504b5403b5303b5203b4f03b4e03b4d07a7f06a7b06a7707a7304a6f10a6d04a6b01a6904a6704a6504a6301a6104a5f04a5b04a5704a5303a4f02a4b02a4703a4303a3f03a3d03a3b01a3903a37fd23503a3301a310797f069770496f0496e0596d0495f0495e049520394f029470393f0393d0393a039370393608935fc1340892f089270387f038770386f0386d03867038650385f038570384f028470383f0383d03837038350382f0382704d6f04d6b04d6704d6304c6f01c6e04c6b04c6a04c6704c6601c6301c6204c5f04c5e04c5704c5304c5207b6f06b6b06b6707b6304b5f04b5b04b5704b5309b4f02b4d10b4b03b4909b4702b4510b4303b4104a6f01a6b06a6701a6304a5f01a5b04a5701a5306a4f06a4d01a4b01a4904a4704a4501a4301a4109a3f01a3b09a3701a330796f069670495f049570594f0594d07947059450893f089370192f089270786f068670485f048570e84f0e84d0e8470e8450e83f098370182f0182701e7f01e7e01e7d04d7f04d7e04d7b06d7a04d7704d7604d7307d7204d6f04d6e04d6d04d6c04d6b07d6a04d69fa56804d6704d6604d6504d6404d6307d6204d6107d6004c7f04c7b04c7704c7304c6f04c6d04c6b04c6904c6704c6504c6304c6107b7f06b7b06b7707b7307b6f02b6d07b6b03b6907b6702b6507b6303b6104b5f02b5d04b5b03b5904b5702b5504b5303b5104b4f04b4b04b4704b4301a7b06a7a01a7906a7706a7601a7301a7106a6706a6606a6504a5f04a5e0aa5df825c01a5b01a5904a5704a5501a5304a5201a5101a5004a4f01a4b04a4701a4309a3f01a3b09a3701a330797f069770796f0796d07967089650495f0495e0595d0494f0494e049420893f089370192f089270787f068770786f0786d078670e8650485f0e85d04857048550484f048470e83f098370182f0182701d6f01d6e01d6d04c6f04c6b04c6704c6304c5f04c5d04c5b04c5704c5504c5307b6f07b6d06b6b06b6a06b6706b6608b6504b6304b5f04b5d06b5b06b5a04b5704b5604b5504b5404b5301b4f04b4704b4307a6f06a6b06a6707a6307a5f07a5b07a5707a5304a4f04a4b04a4704a4309a3f0aa3b09a370aa330796f069670795f0795d07957089550494f049470593f089370892f089270786f068670785f078570484f048470a83f0a8370e82f0982704d6f04d6b04d6704d6317c6f07c6e08c6b06c6a08c6706c660ac6307c6201c5f01c5e04c5704c5301c5209b6f08b6b08b6710b6304b5f04b5b04b5704b5309b4f02b4d10b4b03b4909b4702b450ab4303b410aa6ff826e01a6b08a6701a630ca6204a5f01a5b04a5a04a5704a5601a5304a4704a4604a4509a3f01a3b09a3701a330896f089670495f049570594f0594d0c947059450c93f099370192f0c92d0a9270c9250e86f088670485f048570a84f0e84d0e8470e8450e83f098370182f0182704e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7302c7f03c7b02c7703c7302c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5303b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f04b6e03b6d09b6c03b6b03b6a03b6903b6803b6704b6603b6504b6403b6303b6203b6103b6003b5f04b5e03b5b03b5a03b5704b5603b5303b5201b4f01b4e01b4d09a7f01a7b08a7701a7304a6f09a6d01a6b01a6904a6704a6501a6301a6104a5f01a5b04a5701a5301a4b02a4a01a4902a4702a4601a4301a4102a3702a3602a350897f089770496f0496e0596d0495f0495e049520394f0394d02947099450393f0393d03937099350192f099270387f038770386f0386d03867038650385f038570384f028470383f0383d03837038350182f0182704d6f04d6b04d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5319b6f07b6e08b6b06b6a08b6706b6619b6307b6202b5f02b5e02b5702b5302b5202b4f02b4e01b4b01b4a02b4701b4602b4302b4209a6f01a6b08a6701a6304a5f01a5b04a5701a5302a4f01a4b02a4701a4303a3f03a3d01a3b01a3904a3703a3501a3301a310896f089670495f0495e02957049520294f0c94d02947029450593f0593d02937029350192f0992d099270b9250e86f088670485f048570284f028470e83f0e83d0e8370e8350182f0182704e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7302c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b04c6a02c6904c6802c6702c6602c6502c6402c6304c6202c61f546002c5f02c5e02c5b04c5a02c5702c5602c5304c5202b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5301b4f01b4e01b4d09a7f01a7b08a7701a7304a6f09a6d01a6b01a6904a6704a6501a6301a6104a5f01a5b04a5701a5302a4f02a4e03a4d02a3f02a3e01a3b01a3901a3302a3201a310897f089770496f0496e0596d0495f0495e049520294f0b94d02947029450293f0c93d02937029350192f0992d099270b9250e87f088770486f0e86d04867048650485f048570284f0e84d02847028450283f028370182f0982d018270e82504d6f04d6e04d6b06d6a04d6704d6604d6307d6204c6f04c6b04c6704c63ff36f08b6b08b67fb36304b5f02b5d04b5b03b5904b5702b5504b5303b5104b4f04b4b04b4704b43f926f08a6b08a670ca6304a5ff725d04a5b01a5904a5704a5504a5301a5104a4f04a4b04a4704a43f623f0ca3bf42370ca330896f089670495f0495e0595d0494f0494e04942de13fd41370c92f0c9270e86f088670485f0e85d04857048550484f048470e83f0e8370c82f0e82704c5f05c5b04c5705c5303b5f03b5b03b5703b5303b4f03b4b03b4703b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a3304c5f05c5b04c5705c5308b5f08b5b08b5708b5305b4f04b4b04b4705b4308a5f08a5b08a5708a5305a4f04a4b04a4705a430ca3f0ca3b0ca370ca3304d6f05d6b04d6705d6308c6f08c6b08c6708c6305c5f04c5b04c5705c5308b6f08b6b08b6708b6305b5f04b5b04b5705b530cb4f0cb4b0cb470cb4304a560796e069660595e0394e029460193e0c936f2018f101405d6f05d6e03d6b03d6a03d6703d6603d6303d6203c6f04c6b04c6704c6303c5f03c5d03c5b03c5904c5704c5503c5303c5102b6f03b6b02b6703b6302b5f02b5d02b5702b5503b5302b4f03b4b02b4703b4307a6f06a6b06a6707a6310a5f0aa5d09a5b01a5910a570aa5509a5301a5104a4f04a4b04a4704a4303a3f02a3b02a3703a330796f069670495f0295d02957029550494f049470393f029370892f089270386f038670385f0385d03857038550384f038470383f028370382f0382704e7f05e7e04e7d04d7b06d7a04d7904d7704d7604d7304d7104d6704d6604d6502c7f03c7b02c7703c7302c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5303b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f04b6e03b6d04b6c03b6b03b6a03b6903b6803b6704b6603b65ef36403b6303b6203b6103b6003b5f04b5e03b5b03b5a03b5704b5603b5303b5207a7f06a7b06a7707a7304a6f04a6d04a6b01a6904a6710a6504a6301a6104a5f04a5b04a5704a5303a4f03a4d02a4b02a47e424503a4303a3f03a3d03a3b01a3903a37e223503a3301a310797f069770496f0496d04967089650495f049570294a02947029460293702936029350892f089270387f038770386f0386d03867038650385f038570384f028470383f0383d03837038350382f0382704d6f05d6b04d6703d6304c6f04c6e03c6b03c6a03c6703c6603c6303c6205c5f05c5e03c5b03c5a03c5703c5603c5303c5202b6f03b6b02b6703b6302b5f03b5b02b5703b5302b4f02b4d02b4702b4503b4307a6f06a6b06a6707a6305a5f04a5b04a5705a5310a4f0aa4d09a4b01a4910a470aa4509a4301a4103a3f03a3d02a3b02a3710a3503a330796f069670595f049570594f0294d02947029450393f0293a02937029360892f089270386f038670385f038570384f0384d03847038450383f028370382f0382704e7f04e7d05e7b05e7a04e7706e7604e7504d7f04d7e04d7d05d6f05d6e05d6d02c7f03c7b02c7703c7302c6f03c6b02c6703c6302c5f02c5d03c5b03c5a03c5903c5802c5705c5602c5502c5403c5303c5103b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f05b6e03b6b03b6a03b6704b6603b6303b6203b5f05b5e03b5d05b5c03b5b03b5a03b5903b5803b5705b5603b55ed35403b5303b5203b5103b5007a7f06a7b06a7707a7305a6f04a6b04a6705a6305a5f05a5d05a5b01a5905a5710a5505a5301a5103a4f03a4d02a4b02a4710a4503a4303a3f03a3d03a3b01a3903a370aa3503a3301a310797f069770596f049670595f0595d05957089550294a02947029460293702936029350892f089270387f038770386f038670385f0385d03857038550384f028470383f0383d03837038350382f0382703d6f03d6d01d6b01d6903d6703d6503d6301d6110c6f04c6d10c6b05c6910c6704c6510c6305c6107c5f06c5b06c5707c5302b6f02b6d02b6702b6503b6302b5f03b5b02b5703b5302b4f03b4b02b4703b4303a6f03a6d01a6b01a6906a6706a6501a6301a6103a5f01a5b06a5701a5309a4f01a4b09a4701a4303a3f03a3d01a3b02a3709a3501a330796f0296d02967029650795f069570894f089470393f029370192f089270386f0386d03867038650385f038570384f038470383f028370182f0182701e7f01e7e01e7d07d7f06d7b06d7707d7307d6f04d6d07d6b05d6907d6704d6507d6305d6102c7f03c7b02c7703c7302c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5303b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f07b6e03b6d07b6c03b6b03b6a03b6903b6803b6707b6603b65eb36403b6303b6203b6103b6003b5f05b5e03b5b03b5a03b5704b5603b5303b5201a7b06a7a01a7906a7706a7601a7301a7106a6706a6606a6509a5f01a5b09a5701a5303a4f03a4d01a4b02a4709a4501a4303a3f03a3d01a3b01a3903a3709a3501a3301a310797f069770796f0796d07967089650895f089570294a02947029460293702936029350192f089270387f038770386f0386d03867038650385f038570384f028470383f0383d03837038350182f0182710d6f07d6e08d6b06d6a08d6706d6610d6307d6204c6f05c6b04c6705c6303c5f03c5d01c5b01c5903c5703c5503c5301c5102b6f03b6b02b6703b6302b5f02b5d02b5702b5503b5302b4f03b4b02b4703b4309a6f01a6b08a6701a6303a5f03a5d01a5b01a5904a5704a5501a5301a5103a4f01a4b04a4701a4303a3f03a3d01a3b02a3709a3501a330896f089670595f0295d02957029550594f049470393f029370192f099270386f038670385f0385d03857038550384f038470383f028370182f0182704e7f05e7b04e7705e7305d7f07d7e05d7b05d7a05d7706d7605d7305d7201d6f01d6e01d6d02c7f03c7b02c7703c7302c6f03c6b02c6703c6302c5f02c5d03c5b03c5902c5702c5503c5303c5103b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f05b6e03b6b03b6a03b6704b6603b6303b6203b5f05b5e03b5d05b5c03b5b03b5a03b5903b5803b5705b5603b55e935403b5303b5203b5103b5009a7f01a7b08a7701a7301a6b04a6a01a6904a6704a6601a6301a6104a5704a5604a5503a4f03a4d01a4b02a4709a4501a4303a3f03a3d01a3b01a3903a3709a3501a3301a310897f089770596f049670595f0595d059570b9550294a02947029460293702936029350192f099270387f038770386f038670385f0385d03857038550384f028470383f0383d03837038350182f0182704d6f04d6b04d6704d6310c6f07c6e08c6b06c6a08c6706c6610c6307c6203c5f03c5e01c5b01c5a03c5701c5603c5303c5202b6f03b6b02b6703b6302b5f03b5b02b5703b5302b4f02b4d03b4b02b4702b4509a6f01a6b08a6701a6304a5f01a5b03a5701a5305a4f05a4d01a4b01a4903a4703a4501a4301a4103a3f03a3d01a3b02a3709a3501a330896f089670495f049570294f0294d04947029450393f029370192f099270386f038670385f038570384f0384d03847038450383f028370182f018270bd6f08d6b08d670bd6304c6f04c6b04c6704c6301c5f04c5704c5302b6f03b6b02b6703b6302b5f02b5d03b5b03b5a02b5709b5602b5503b5302b4f03b4b02b4703b4303a6f03a6b03a6703a6302a5f02a5d03a5b03a5a03a5704a5602a5502a5403a5303a4f03a4b03a4a03a4704a4603a430996f0196b08967019630595f09957019530494f0194b03947019430393f0393d0193b0293709935019330392f0392d0192b0392709925019230386f038670385f038570384f038470383f028370382f038270181f0181704e7f04e7e04e7b06e7a04e7704e7604e7307e7204d7f04d7b04d7704d7301d6f01d6e01d6d02c7f03c7b02c7703c7302c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5303b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f04b6e03b6de736c03b6b03b6a03b6903b6803b6704b6603b6504b6403b6303b6203b6103b6003b5f04b5e03b5b03b5a03b5704b5603b5303b5209a7f01a7b08a7701a7304a6f04a6e05a6d04a5f04a5e01a5b01a5901a5304a5201a5103a4f03a4d01a4b02a4709a4501a4303a3f03a3d01a3b01a3903a3709a3501a3301a310897f089770496f0496e0b96de616c0496704965049620495f049570294a02947029460293702936029350192f099270387f038770386f0386d03867038650385f038570384f028470383f0383d03837038350182f0182705e7e04e7d06d7a04d7904d7604d7104d6604d6502c6d02c6902c6502c6102c5902c5103b6d03b6903b6503b6102b4e03b4d04a6d01a6909a6501a6102a4e03a4d03a3e01a3903a3201a310496d0896502936029350892d089250386d038650382d03825e456f08d6b08d6710d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5303b6f03b6b03b6703b6303b5f03b5b03b5703b5302b4f02b4e03b4d09a6f01a6b08a6701a6309a5f01a5b09a5701a5302a4f02a4e03a4d03a3f03a3e01a3b01a3903a3701a3303a3201a310896f089670c95f0c9570294f029470293702936029350192f0992d099270c9250386f038670385f038570284f028470383f038370182f0382d018270382505e7e04e7d06d7a04d7904d7604d7104d6604d6507c7e06c7a06c7607c7204c6e04c6d04c6c04c6a0ac691bc6804c660ac650ac6404c6204c6104c6004c5e04c5a04c5604c5202b6d03b6902b6503b6101b4d01b4504a6d01a6909a6501a6103a4e03a4d03a3e03a320496d089650294d029450892d089250386d038650384d038450382d0382507d7e07d7d07d7c06d7a06d7608d7508d740ad6e0ad6a0ad660ad6201c5d02c5503c5107b7e07b7d05b6e04b6a04b6605b6206b5e06b5d06b5c03b4e01b4a01b4603b4207a7d08a7503a5e03a5d03a4e03a4203a3d01a3903a3501a310895d029550793d089350892d089250385d038550383d038350382d03825e256f08d6b08d670ad630ac6f07c6e08c6b06c6a08c6706c66e146307c620ac5f05c5e0ac5b04c5a0ac5704c560ac5305c5202b6f03b6b02b6703b6302b5f03b5b02b5703b5301b4f01b4d02b4701b4503b4309a6f01a6b08a6701a6309a5f01a5b09a5701a5303a4f03a4e03a4d03a3f03a3e01a3b02a3701a3303a320896f089670a95f0c9570994f0294d02947029450393f029370192f0992d099270c9250386f038670385f038570384f0384d03847038450383f028370182f0382d018270382504e7f05e7b04e7705e7305d7f07d7e05d7b05d7a05d7706d7605d7305d7202c7f03c7b02c7703c7302c6f03c6b02c6703c6302c5f02c5d03c5b03c5a03c5903c5802c5705c5602c5502c5403c5303c5103b7f07b7e03b7b03b7a03b7706b7603b7303b7203b6f05b6e03b6d05b6c03b6b03b6a03b6704b6603b6504b6403b6303b6202b5f02b5e02b5d02b5c03b5b03b5a03b5903b5803b5704b5602b5502b5403b5303b5203b5103b5008a7f08a7b08a7708a7305a6f04a6b04a6705a6305a5f05a5d05a5b01a5905a570ca5505a5301a5103a4f03a4d02a4b02a470ca4503a4303a3f03a3d03a3b01a3903a370aa3503a3301a31049660495602946029360992e 20 1048575 8 255 11 2047 20 1048575
def cc_56_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x8213f809187d7327a532773327413272819706226b94d69227619795ca4f54d7d5004d4d927460794312f3e34e3687b315532c2532972b215821ea2b1bf2b1932c1652e132330ea480ca2007d4d0007d 0x273f8179ec09cee05e73016bf80f5ec05aee03d73016b780b5b407ad603d6a016b381359805aca03c7f03e3f00f1ec078f403c770363b00f1cc078e402c6f0163700b1b4078be03c5e01e2e81edfc0d6f606b7703db9816dbc096d604b6702db180ed7c056b602b5701da980ed3c0769a03b4b00da480ed1c1968a03b4300da081a9d80f2fc0596e024b300e578052ac0394e01ca600e51a3e2880193e0549b00e0623202807c5f0362d81b15c0f8a603b5f01dad80ed5c076a603b4f01da580ed1c0768601a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1d8068dc0346604d6f02eb581359c0bac602c6f03e3700b1ac058d402c670363300b18c058c402c5f01e2f00b174056de02b6b015b380ad8c056b604b5a015ac80ad5c056ac02b53015a880ad1c0568c02b4503d3781a9ac0d4ce07a6302d2f81296c094ae05a530152780a9340549601a49015238269140548601a410151f80a8ec0546e02a33034b30135bc09ad604d67026b180b1bc078d602c6701e3180b17c098bc02c5d0162b80b154078a603c5201db781edb8076d603b6a01db381ad98076c603b62015ab80ad58056aa03b4f01da700ed340f4de06a6b0353381e98c094be04a5b0252b81294c0749e02a4b0152380e90c0747e03a3d01d1d8068e40746e0ca3501d198068c40d2cc02d6f016b700b5ac0dad402d67016b300b58c0fac404c6f0263581319c098c602c5f0162f00f174056de02b6b015b380ad8c056be02b5e015ae80ad3c0569c02b4b015a480ad0c0968402b4103d3781a9ac0d4ce07a630152f826974054b601a590152b80a954054a601a510252781292c0948e04a430151f80a8ec0546e02a33034b30135bc0bad604d6702eb180b1bc078d602c6701e3180b17c058ba03c5b01e2d00b15c098ac02c5501db781edb8076d603b6a01db381ad98076c603b62015af80ad78056ba03b4f01da700ed340f4de06a6b0353381e98c0b4be04a5b0252b81694c0749e02a4b0152380e90c0747e03a3d01d1d8068e40746e0ca3501d198068c40d2cc07c5f0362d81b15c0f8a607b5f035ad81ad5c0f6a71c34f8d9a5c68d1e3268607a5f0352d81a95c0f4a60ca4f0652583291c194860ca3f0651d8328dc194660695603eb781b5ac0dace07d6303e3781b1ac0d8ce07c639222fc8916e408af1e45303db781adac0d6ce07b63065af832d6c196ae0cb53065a7832d2c1968e0cb430353301e5b80b2bc0495601ca700a5180327c0c9368e80c4600500bade05d6d01eb580f5a40bace05d6502eb180f584058de02c6d0163380b194058c604c5f02e2d81315c0b8a602b6f015b680adac056d202b67015b280ad8c056c202b5f015ad80ad5c056a602b4f015a580ad1c0568609a6f04d368269ac034d209a6704d3282698c034c207a5f0352d81a95c0f4a605a4f0252581291c0b48602a3f0151d80a8dc054660296f014b681259c092ca0795f034ab80a53c0928e0293f0149b8224bc1124e1486f07c3685219c1f0ca0785f0342b81613c0908e0283f0141b8260bc1304e03e7e026b68175a409aca05d6103e3f0171e80d8ec05c720a6370171b42f8d805c6a02e348171a01f8cc05c6507e320171880b8c205c60015b280ad340569202b45015a08269b4034d209a6500d308169340349209a4500d208125580928c0787e0143700a0d805cfe03e7e0173e8135fc0baf604d7702eb980b5bc05ada02d6b02eb480b59c09aca02d63016b08171fc0f8fc05c7b02e3d0171dc0d8ec05c7302e3900b1bc058dc02c6d0163600b1ac058d405c6902e3400b19c058cc05c658b23200b18c058c402c610163000adec0d6f402b79015bb80add8056e602b71015b380ad98056ca02b5f015ad80ad5c056a602b4f015a680ad2c0569202b47015a280ad0c0568207a7f0353d81a9dc0f4e602a6f0153680a9ac034d202a6704d3280a98c034c205a5f0252d81295c0b4a605a4f02d2681692c0349205a4704d2281690c0348202a3f0151d80a8dc054660797f034bb80a5bc052da02967044b2812568092ae04956024a38125180928a0293f0149b8224bc1124e0787f0343b80a1bc050da028678a83281617c090ae0584f02c2681611e0e08a0283f0141b8260bc1304e02d6f016b70175ac0bad405d6702eb301758c05ac404c6f02e3581319c0b8c603c5f01e2e80f15c078aa03c53015b780edac056ce03b63015af80ad74076b603b59015ab80ad54076a603b51015a780ed2c0568e03b4303d3781a9ac0d4ce07a6305d2f82a974134b601a5905d2b82a954134a601a5102d2781292c0948e05a4301d1f80a8ec0546e03a3303cb781a59c072be0395d024ab8125540729e0494a024a38125180727e029370449782249c070de0386701c2f80e174070ae0385501c2780e11c0707e0283701c1780e09c09cfe05e7b0273b8179cc0bafe07d7e02ebd8175e80baee06d7602eb98175c8058fe02c7d01e3d80f1e8058ee06c760163a80b1bc078d602c6701e3180b17c058ba03c5b01e2c80b15c058aa03c5301e2880adfc056fc02b7d01db7816db8076da05b6c01db580eda8076ce04b6601db2812d90076c603b6201daf816d78076ba05b5c01dad80ed68076b203b5801dab816d58076ab1335401da980ed48076a203b5001da780ed380769a07a7f0353d81a9dc0f4e605a6f0253581299c0b4c605a5f02d2e81696c034b205a570852a81694c034a203a4f0152580a91c0748603a3f01d1e80e8ec0347203a370551a80e8cc034620797f034bb8125a8092ce04966024ab812558092aa0394f014a380e4fc0727a039370449a8224bc1124e0387f01c3b80e1bc070ce0385f01c2e80e15c070aa0384f0142380e0fc0707a0383701c1a80e0bc0704e05d6f02eb68075ac03ad205d6702eb281758c03ac204c6f0263681319c098ca05c630262f81716c098ae05c5304db780adb4156d603b6904db380ad94156c603b6103daf81ad6c0d6ae07b5302da7812d2c0968e05b4302d378169b4034d601a690353381a994034c601a6102d2f80696c0d4ae01a5302d2780692c0948e01a4304d1f8068ec1346e01a3303cb78125b4092ce0496503caf81a55c0b29e049470449f8224dc0325e089270543782a1b4150ce0f86503c2f81a15c0b09e048470841f8260dc0305e0182700f3f0135b40bad204d6502eb081f1f80b8f406c7602e3904f1b80b8da16c6c02e350171a40b8d00fc6602e3283f1900b8c405c6102e3000adb4076d202b6501db080ad340769202b4501da08069940349a01a4900d22806904092ac0494603c3f01e1b80304c01e7f00f3f0079f409afe05d7b026bb8175cc09ade04d6d02eb58175a409ace04d6502eb18175840b8fe07c7e02e3d8171e80b8ee06c7602e398171c80b8de07c6e02e3681f1b00b8d605c6a02e348171a00b8ce07c6602e32c451900b8c605c6202e308171800f6fe06b7b035bb81edcc0f6de02b6d03db580eda40f6ce02b6503db180ed840b6be04b5b025ab816d4c0b69e02b4d02da580ed240b68e02b4502da180ed04034f606a7a00d3c81a9dc0d4ec01a7300d3881a99c0d4cc06a6502d2f80696c094ae01a5302d278169340349601a4902d2382a9140348601a4104d1f8068ec1346e01a3303cbf81a5dc0f2de0796d03cb3822594092b404957024ab01251c0928c049450449f8224dc0325e0892703c3f81a1dc0f0de0786d03c33c401940b0be0485702c278161340b08f060450841f8260dc0305e0182707eb781f5b811ad606d6a046b381b5981fac607d62026378171ac098ce05c6300e2f807174136de03b6b045b380ed8c136be02b5d01dad80ed64136ae02b5501da980ed440b69e03b4b025a380ed0c034de01a6b00d3380698c034be01a5d00d2780692c0348601a3f00d1d8068dc034660a8560242303e0f80304c0ad6f03eb70235ac0dad408d67036b306b58c0fac404c6f02e3581319c0b8c601c5f00e2e81315c038aa05c5304db7822dac116ce10b6304daf80ad74156b603b5904dab80ad54216a603b5102da7812d2c0968e05b43055378069ac114ce01a6302d2f8169780b4ba05a4f02d2700692c0948e01a4302d210268fc0347609a3700d198225bc112ce0c95f024ae81255c092aa0594f024a38324fc1326e0192f0649682a49c1924aa206f0443385a17e1c0ba0a8571b02a81613c0908e1083f04c1b8060bc1905a018271a8128139fc0bcf604e7702f398175fc0fafc05d7b02ebd0175dc0daec05d7302eb900b1fc078f602c7701e3980b1bc078d602c6701e3180b17c058ba03c5b01e2c80b15c058aa03c5301e2880edfc0f6fc03b7b01dbd00eddc0d6ec03b7301db900edbc0b6dc03b6b01db500ed9c096cc03b6301db100ed7c0b6bc03b5d02dae00ed6c076b403b5901dac00ed5c0b6ac03b5504daa00ed4c076a403b5101da8006d3c0369c01b4d04d3f8069ec114ee01a7302d378069ac094ce01a6302d2f816974034b601a5902d2b826954034a601a5100d2580a9280349202a470152300690c0348202a370151b00a8d4112fe08977024b501259c092cc04957024ab0125540729e0394d014a38265140727e0393d01c9b8264d40325e0992701c3f80e1dc070de0386701c2f80e174070ae0385501c2780a11c0707e0383d01c1b80e0d40305e01827026b78175ac09ace05d630163780b1ac058ce02c630162f80b16c058ae02c53055b781edb8116d606b6a045b381ad98156c607b62015af80ad6c056b402b57015ab00ad3c0569c01b4b00da500ad1c0368c02b43015a10269bc034d608a6700d3181697c034b604a5700d2980a93c0349602a4700d2180e8fc0747a01a3b00d1c8168dc0746a01a3300d188225bc112ce0295f024ab80a53c1929a02947014a28124fc0927a029370149a8064bc1325a099270549287e1bc110ce0585f0242b80a13c0508e0a83f07c1e82a0dc1506a0182f04c1680609c1504a04d6f02eb581359c0bac605c6f03e370171ac0b8ce05c6302e3102edbc116d608b6705db1816d7c0b6ba04b5b025ad012d5c096ac0bb55015a980ad3c0569a04b4b025a500ad1c0568c02b45015a200ad0c054de02a6b0153380a98c054be02a5b0152b80a94c0549e02a4d0152580a91c0548a02a4300d1f80a8dc054660996f00cb582259c032c60595f00cad81255c032a60594f02ca680652c0b28e0994500ca180e4fc1326e01933014978064ac0524e019230ac3782219c0b0be0485702c278161340b08e1584505c1f82e0dc0505e0282700c0f80605c0fafc05d7a036bb0175c80f8fc06c7a0363b01f1c80b8dc04c6a026330171880b8bc05c5d02e2e0171681f8b20fc5802e2b05b1542d8a805c5202e28817140056ba02b59015aa80ad440369a01a5d00d2c806954034a201a4d024b3012558390fc0586e02c2f0161700508c0283600c130139fc0bcf604e7702f398175fc0fafc05d7b02ebd0175dc0daec05d7302eb900b1fc058fc02c7b0363d00b1dc058ec02c7303e3900b1bc058dc02c6b0263500b19c058cc02c6302e3100b17c058bc02c5d0162e00b16c0b8b402c5985a2c00b15c058ac02c550162a00b14c0b8a402c5102e2800adfc056f602b77015b980adbc056d602b67015b180ad7c056ba02b5b015ac80ad5c056aa02b53015a8806d3c0369c01b4d04d3f8069ec114ee01a7302d378069ac094ce01a6302d2f816974034b601a5902d2b826954034a601a510152780a9380749a02a3f0151f0068ec0347201a33015190068c4112fe08977024b501259c092cc04957024ab0125540529e0294e05ca6c285300528e02945014a100a4fc1927a029370149a8064bc1325a0992705492a841fc110ee0586f0243381617c0b0ba058578202a80a13e1209a028470142280a0fc0506e0182f04c1680609c1504a03e7e0173e80b5b40bad204d65016b081f1f80d8f406c7603e3900b1b8058da02c6c0163504b1a4258d002c6607e3283f190058c402c610163000ede8056f202b76015b880ad98056ca02b4d015a480ad140568202a6d00d34826994034c209a4d00d24826914034820585e02c2702609803cfc01e7d026b68175a409aca05d6103e3f01b1e80d8ec07c7203e3701f1b40f8d807c6a07e3484b1a00f8cc0fc6507e3201f1880f8c207c60015b680eda4056ca03b61015a680ed240568a03b4100d3d0069e40d4ec01a71035330069940349a01a4900d228069040b0bc0584e00c130135bc0bad604d6702eb182b1bc0f8dc08c6b0363502319c0d8cc0ac6303e3101717c0b8bc09b6f01db5822d9c076c605b5f01dad812d5c076a609b4f015a680ed2c0769209b47015a280ed0c0768201a6f00d3580699c034c601a5b00d2b80694c0348e0aa4600d228068fc0347601a3700d1981f5f80daf406d7603eb900b1f80d8f402c7603e3900b1b8098d402c6602e3100b178058ba02c5c07e2d00b1641f8b002c560162a80b1501f8a402c510962800ad74056b202b55015a8806d380369a01a5d00d2c806954034a202a4e00d2680a8f80347201a3200d1880a5382b2980586e02c2f0060981504804d6f02eb581359c0bac60fc6f03e370231ac0d8d408c670363304b18c0f8c50736f01db5822d9c076c605b5f01dad812d5c076a612b4f015a680ed2c076920fb47015a280ed0c076830626f00d3582299c034c605a5f00d2d81295c034a60fa4f8292680692c034920fa471b12280690c0348203a3f00d1dc108dc034660585e02c270d009809ade05d6b026b381758c0b8de07c6e02e358171a80b8ce06c6602e3181718a286de08b6b045b3c48d8c0b6be04b5b025ab816d4c0b69e02b4d02da580ed240b68e02b4502da180ed061e4de08a6b0453383298c0b4be04a5b0252b81694c0b49e05a4d02d258069240b48f0d24502d218069061847e0ca3b8411b8328cc112de08967024ad01255c092ac04947024a3012515be27ed51370649783249d400de0886702c2f81215c0b09e0584d02c23c0c114b007e48037064178cc09c09ade04d6b026b381358c118de08c6b0463382318c098be04c5b0262b81314c116de08b6b045b3822d8c096be04b5b025ab812d4c1969e0cb4b065a3832d0c094bc0796e034b30125580729c0294600c9f0324d809ade04d6b026b381358c098de03c6e026358131a8098ce04c6601e3180f188058be02c5e0162b80b14c058a402b6f015b580ad9c056c602b5f015ad80ad5c056a602b4f015a680ad2c0569202b47015a280ad0c0568207a6f0353581a99c0f4c604a5f0252d81295c094a609a4f04d2682692c0349209a4704d2282690c0348202a3f0151d80a8dc054660796f034b381257c052ae0594f02ca680a51c0528a0293f0149b8224bc1124e0786f0343381217c090ae0e84f0742683a11c1d08a0283f0141b8260bc1304e02e7f01f3f00b9f409afe04d7e026bd81b5e809aee04d76026b981f5c805ade02d6e016b680b5b005ad602d6a026b4c015a005ace02d66026b281359005ac602d62016b080b580098fe04c7b0263b8131cc058de02c6d016358131a4058ce04c650163180b184056f606b7a015bc80addc056ec02b73015b880ad9c056cc02b65015af80ad78056ba02b5c015ad80ad64056ae02b55015a9812d48056a203b50015a780ad2c0568e02b4303d3f81a9ec0d4ee07a730153780a9b4054d601a6901533826994054c601a610252f826974094b601a590252b812954094a601a510252781292c0948e04a430151f80a8ec0546e02a3303cbf81a5dc052de0296d014b3822594092be0495e02cae81253c0929c049420149f80a4dc1125e0892703c3f81a1dc050de0286d0143383a194090be0e85d0242b8121540909e048470141f80a0dc1305e09827 20 1048575 8 255 11 2047 21 2097151
def cc_56_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xdc89fa910325acdc18aadea54813e6aa5c567f80e9ee31ed9fa6abe8157606ae8055b81ab70055816ab00155012aa0055004a782922ac9c4812f494534b486208df2d13c821ccac182180030 0xf5bc07adc03d6701eb180f588098de05c6b0263381718c098be04c5d02e2d80b164098ae04c550162980b144056de03b6b015b380ed8c056be02b5d01dad80ed64056ae02b5501da980ed440569e03b4b015a380ed0c0d4de06a6b0353381a98c174be0aa5d04d2d806964174ae0aa5504d298069440b49e04a4b0252381690c0747e02a3b0151b80e8cc0d2de0396703caf81e574072ae0395502ca781251c0727e029370449782249c070de0386701c2f80e174070ae0385501c2780e11c0707e0283701c1780e09c0703a03815026be8175e409aea05d710163e80f1e4058ea03c71035bf02adf4156f806b7a035bc81ade00d6ec06b75035ba01adc8236e21ab70035b701ada80d6cc06b62015af006d68036ac02b5201da7006d280368c03b4204d3e81a9e8034f201a780353b01a9d40d4e801a710353501a9980b4bc05a5201d2700e9080747c03a3d034bf01e5f40d2dc069620449e8224d41125a0892501c3e80e1d40707a0383501c1680e0940703a038150263781b1b80b8d605c690263381718c0b8c405c610262f81716c098ae05c53015b781adb8076d603b69015b380ed8c076c403b61015af80ed6c056ae03b53015a780ed2c0568e03b430353781a9b8074d603a6901d3380e98c074c403a6101d3001a97c0d4bc06a5b0352c80e95c0d4a606a5205d2880a93c0948e05a4301d1f80a8dc074660696f054b681a5ac0d2ce06965034b181a57c0d2b606957034a981653c092960494702ca180e4fc052760293701c9982e4bc132560b92704c9180e1bc070da0386701c3280e17c070ae0384f01c2380e0fc0506e0382f01c1680e09c0704a0381f01c0b8135fc0dafc04d7d026be0175ec0baf204d77026ba8175cc0bae405d7102eb80135bc0bad604d6702eb180b1fc0d8fc02c7d0163e00f1ec078f202c770163a80f1cc078e403c7101e3800b1bc078d602c6701e3180b17c058ba03c5b01e2d00b15c098ac02c5501dbf81adf8076fb3e37c01dbd80ede8076f203b7801dbb81add8076ea06b7401db980edc8076e203b7001db781adb8076da07b6c01db580eda8076ce06b6601db281ad90076c603b62015af80ad78056ba03b4f01da700ed340d4fe0aa7d0353d8069e40d4ee06a75035398069c40d4de06a6b0353381a98c0b4be04a5b0252b81694c0749e02a4b0152380e90c0747e03a3d01d1d8068e40746f3d23501d198068c40d2fe0697e03cbe81a5bc0d2dc0696202caf81255c0729e0294701c9f80e4f4072740393701c9b0224d6782680892f0449380e1fc070fa0387701c3a80e1bc070ce0385f01c2b80e13c0508e0383f01c1e80e0dc0706a0382f01c1380e0740702a01d6f00eb701b59c0dac601d620363781b1ac0d8ce06c630562f813174158b605c590562b813154158a605c51035b781adac0d6ce06b6304daf80ad74216b603b5904dab80ad54156a603b5104da7842d2c1368e0ab43035378069ac0d4d406a670353300698c0d4ae06a560352a82a93e7049c01a4b0552380690c1948409a3f9a11f0068ec1346e01a330651901a5bc0d2ce0795f03cae82255c0f2aa0894f044a38224fc1126e0192f0449682249c1124a0686f0343382a17c1b0ba0d85706c2a82a13c1b08e0d83f04c1b8060bc1905a0182706c128175bc0badc05d6702eb1817588098de05c6b0263381718c098be04c5d02e2d807164098ae04c5500e298071440d6de06b6b035b381ad8c136be02b5d0bdad80ed64136ae02b550bda980ed440b69e04b4b025a3816d0c0d4de01a6b0353380698c094be04a5d00d2d8069640d4ae04a5500d298069440b49e01a4b0252380690c1347e01a3b04d1b8068cc0d2de0596703caf81e5740b2ae0595502ca781251c1127e0893700c9782249c0d0de0686706c2f8361741b0ae0d85502c2781211c1b07e0983700c1780609c1103a0d81500eb781b59c0dac604c6f02e3581319c0b8c604c5f0262e81716c0b8b404c570562b0131540b8a605b6f02db5816da80b6ce06b6602db1812d7c096ba05b5b02dad016d5c0d6ac04b55025aa016d4c0369e01b4e00da681a9bc0d4d606a670353182697c154b609a570552981693c0949604a4702d218168fc0b47603a3902d1b8168cc074620696f02cb381e57c112ae0594f024a38164fc0b27a059370449a8224bc1124e0686f0343382a17c150ae0584f024238160fc0b07a0583706c1a8360bc1304e04d7f026be8175ec0baf204d77026ba8175cc0bae204d6f02eb581359c0bac605c7f0363f0171f6728f805c7b02e3d0171e40b8f005c770363b0171d40d8e805c7302e390171c40b8e005c6f036370171ac0b8d405c670363301718c0b8c401c5f00e2f0071740d6fe02b7d035bd80ede40d6ee02b75035b980edc40d6de06b6b035b381ad8c0b6be04b5b025ab816d4c0b69e02b4d02da580ed240b68e02b4502da180ed040d4fe06a7e0553ece09f0034f601a790353b81a9d4034e606a7200d388069c00d4de01a6b0353380698c034b604a5a00d2c81295c094ac01a5300d2881291c0948c04a4504d1f8068ec1346e01a33034bf81a5f80f2fa0696f034b701a5880b2be0495702ca78165340b28e089450449f8224dc0325e089270343f8361f40d0ee068750343781a19c0b0be0485702c278161340b08e0d84506c1f8260dc0305e018270440e83605409ade04d6b026b381358c098de04c6e0263381318c098c404c5f0262f00716c038b404c5700e2b01314c098a406b6f035b581ad9c0d6c604b5f025ad812d5c096a609b4f015a686ad2c0769209b47015a286ad0c0768206a6f00d3581a99c034c604a5f0252f00696c094ae01a530252901693c0b49a01a4b00d2481a91c0b48a01a4300d208268fc0347609a3700d1981a5bc092ce0495f024ab81e53c0f29a04947024a28224fc1126e0192f0449381a1bc0d0ce0485f0242b83613c1b09a0d84706c228360fc1306e0182f00c138135fc09afc04d7d026be0135ec0daf404d79036bc0135dc09aec04d75026ba0135cc0dae404d719b2b80135bc09adc04d6b036b501359c09acc04d63036b10131fc098fa04c7b0263c8131dc098ea04c73026388131bc098d604c670263180717c038bc01c5d035bf80adf40d6f603b79035bb80add40d6e603b71035b781adac0d6ce06b63025af80ad74096b603b59025ab80ad54096a603b51025a7812d2c0968e04b430353f82a9f4034f601a790353b81a9d4034e601a71035378069ac0d4ce01a630252f8129780b4ba04a4f0252700692c0349201a43025210069041347e01a3b04d1b8068cc0d2fe0697e03cbe81a5bc0d2dc06962024af822574092ae04955024a781251c1127e0893700c9782249c0d0fe0d87d0343b81a1d40d0de068670242f836174090ae048550242781211c1b07e0983700c1780609c1103a0d81500eb781b59c0dac606c6f0363581b19c0d8c60ac5f0562d82b15c158a602b6f01db580ad9c076c602b5f015ae80ed6c076b402b5704dab00ad54076a602b4f01da580ad1c0768603a6f01d3580e9a8074ce06a6601d3180a97c054ba03a5b01d2d00e95c0d4ac02a550152a00e94c0749e05a4e01d2580e91c0748603a4200d1f8068f80347a0696f01cb381e57c112ae0894f044a380e4fc0727a029370449a80e4bc0725a039270449280e1bc070ce0385f01c2b80e13c0708e0383f0141b80e0bc0705a0382701c1281b5fc09afa06d7b02ebc81b5dc09aea06d7302eb881b5bc0dad606d67036b180b1fc058fa03c7b01e3c80b1dc058ea03c7301e3880b1bc078d602c6701e3180b17c078b602c5701e2980edfc0d6fc03b7d04dbe00edec076f403b7901dbc00eddc0d6ec03b75035ba00edcc076e403b7101db800edbc0d6dc03b6b01db500ed9c0d6cc03b6301db100ed7c0b6bc03b5b01dad00ed5c096ac03b5301da9006d3c0369c01b4d0353f81a9f8134fb3427c00d3d8069e40d4ee06a7500d3981a9c8034e201a70035378069ac0d4ce01a6304d2f80696c134ae01a5300d2580a9280349202a470152300690c0348202a370151b00a8d40d2fe0697e03cbe81a5bc0d2dc06962044af82255c0729e0394d014a38225140727e0393d01c9b8224d40325e0892701c3f80e1f4070ee0387501c3780e19c070be0385701c2780a11c0707e0383d01c1b80e0d40305e0182701c0e80e056626d005b60025aa4b4d52628d804c6402da601b9e005ce002c6c01e30016db0096b12c35008d36006980172d92f06c969ae4ac0d00b6b92b35402e364b11900f6f803b5c00daa012d300347003a3403c9a4a80d00dade06d6b036b381b58c058de02c6b0163380b18c058be02c5b0162b80b14c056de02b6e015b380ad8c056c53235f02daf4c0d6c096b52e357025ab4a4d4c0b6a402b4f015a7006d2c0369402b4700da300ad0c0568406a6f00d3581a99c034c609a5f00d2d82695c034a602a4f0152700692c0548e01a430152100e8fc0747a01a3b00d1c81a8dc0746a01a3300d1881a5bc0d2dc02967034b102257c112ae0294f044a680a51c0528a0793f03c9e80a4dc0526a0192f0449682249c1124a0686f0343383617c1b0ae0284f014238360fc1b07a0d83706c1a8060bc1305a0182706c128220741b02a06d7f026be81b5ec0baf206d77026ba81b5cc0bae206d6f036b581b59c0dac602c7f0163f00b1f4058f802c7b0363d00b1e40d8f002c770163b00b1d4058e802c730363900b1c6508e002c6f0163700b1ac0d8d402c670163300b18c0d8c402c5f0162f00b16c098b402c570162b00b14c0b8a402b7f015be80adec056f202b77015ba80adcc056e202b6f015b580ad9c056c602b5f015ad80ad5c056a601b4f00da7006d340d4fe09a7d00d3d8069e40d4ee06a7500d398069c40d4de01a6b0353380698c134be01a5b04d2b80694c0549e02a4e01d2680a8fc0547c01a3b00d1c8068cc0546401a31034bf81a5f80f2fa0696f034b701a588112be08957014a78225340528e029450149f8224f40526e0293500c978224b41124e089250343f8361f40d0ee068750343781a19c1b0be0d857014278361340508e028450141f80a0dc0305e0982d00c138360941103a0d815036378131b40d8d605c69036338131940d8c605c610362f81b16c0d8ae06c53035b780adb40d6d603b69035b380ad940d6c603b61035af81ad6c0d6ae06b53a21a7d04d2e7e68f3b34303537ce89b40d4d601a690353381a9940d4c601a610352f81a96c0d4ae06a539b92783292e6a48e0ca439991f8328ee4e46e0ca33034b781a5b80f2da0695f034af01a5481129e089470449f8224dc1125e08927034378361b40d0ce068650342f81a15c1b09e0d84706c1f8360dc1905e0d8270440e83605409ade05d6b026b381758c0f8de07c6e0163580b1a8058ce02c660163180b188078be03c5e015b780adac056ce02b63015ad812d68056ae02b56015a980ad1c0568a07a6f0353581a99c0f4c605a5f0252d81295c0b4a609a4f04d2682692c0349209a4704d2282690c0348202a3f0151d80a8dc0546604e7f02f3d8139dc0bce602d7f03ebf00b5ec05af402d77036bb00b5cc05ae402d6f01eb700b5b4058fe02c7b0163b80b1cc058d604c6a0163480b19c058cc02c630163080b15c058ac02c5503dbf81adec0d6ee07b7302db7812dac096ce05b63015af80ad74056b601b59015ab826d54056a601b51015a780ad2c0568e02b430353b01e5f80b2dc0596c024b3012590052bc0295c014ab4945500529c0294600c9f0264d8070311c014026b78135ac09ace04d630163780f1ac058ce03c630162f80b174058ae02c5501e2981edbc0f6dc03b6b01db500ed9c076cc03b6301db100ad5c056ac03b4f01da701e9bc0d4d606a6703d3181297c094b604a570252980e93c0549602a4701d218328fc1547a09a3b00d1c8328dc1546a09a3300d188139fc09cf604e770273980b5fc07af602d7701eb980b5bc09adc02d6d016b380b59407ac603d6201e3f81f1f8078f603c7a01e3b81b1d8078e603c720163380b198058ca03c5f01e2f00f1740f6fe06b7b035bb81edcc096de04b6b025b3812d8c076be02b5b015ab80ed4c0769e03b4d01da5806d240768e0cb4501da1806d040d4ec0797e024b7012598072bc0395c014ab00a5500729c0394c01ca348c5100327c0c93601c0c46c05005ade02d6e016b580b5a805ace02d6603eb181f588098de04c6b0263381318c078be03c5d015b780adac056ce02b63015af80ad740569e02b4b015a181e9bc0d4d606a6703d3182697c134ba09a5b00d2c82695c134aa09a5300d2881293c0949604a470252180a8fc0547602a370151980b9fc05cfc02e7b0373d00b9dc05cec02e7303f390135fc09af604d77026b980b5bc05adc03d6d0163f80b1ec058ee02c730163780b1b8058da02c5f0162f00b16c058b202c530262900b1440f6fe06b7b035bb81edcc056de09b6d015b5806da4056ce02b65015b1806d84096be04b5b025ab812d4c0569e02b4b015a380ad0c0d4ec0797e014b74845b0052cc02964024af016570092ac04954014a700e5300528c0294400c9f0264d8070311a014026b78175ac09ace05d630163780f1ac058ce03c630162f80b174078b603c5a0162b813158058aa07b6f03db700edac076d403b6701db300ed8c076c402b5f015af00ed3c0769c07a6f0353581a99c0f4c605a5f0252d81295c0b4a603a4f0152580a91c074860ca3f0551e8268ec034720ca370551a8268cc0346206966 19 524287 8 255 11 2047 21 2097151
def cc_56_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x9d22b9597991b3e8a279829797eb3e76e7d747276ce79655795da7b5875355c2b4da82492484672b42a3d3ff2b3c23d3972b35a3d332283072b2c83f2a8202594f1da7f18b4f14b400cc7f07b510007b 0x4d6d02eb48135940bac207c7e0363d01b1d80f8e407c6e03e3681f1b00f8d408c690463401f198118ca08c6403e3101f1840f8c003c5e015b680ada4056ca02b61015a281e9b4034d208a6500d308269340349209a4500d2081a5d80d2cc0787e03c3701e1b00b0bc0284e0141b02609809afe05d7b026bb8175cc09ade04d6d02eb58175a409ace04d6502eb1817584058fe07c7e0163d80b1e8058ee06c760163980b1c8058de07c6e0163681f1b0058d602c6a0163480b1a0058ce07c6601632823190058c602c620163080b180058be03c5e0162e80adfc056f602b77015b980adbc056da02b6b015b480ad9c056ca02b63015b080ad6c096b402b59015ab80ad58056a602b51015a380ad180568a07a7f0353d81a9dc0f4e607a6f03d3681e9ac034d207a670453281e98c034c205a5f0252d81295c0b4a602a4f0152680a92c0349202a4704d2280a90c0348202a3f0151d80a8dc054660697a034bb81a5d80d2ce06966034b281657c092ae0294f014a680a51c1128a0293f0149b8224bc1124e0787f0343b81e1bc0f0da078670443281617c090ae0284f0142680a11ebc08a0283f0141b8260bc1304e04d6d026b481359409ac202c6d01e3480b194078c207b7e035bd01add80f6e407b6e03db681edb00f6d408b69045b401ed98116ca08b6403db101ed840f6c001b5e015ad00ad58036a403b4e00da5006d180768407a7e03d3901e9b80f4da07a6c00d348229940f4c401a6100d30012968094ac03a4e01d2100e8f80747a0697a034bb01a5980d2ca0893d0449a8224b41124a0386d01c3280e0f40706a0382d01c128135fc09af604d77026b98135bc09ada04d6b026b481359c09aca04d63026b080b1fc078f602c7701e3980b1bc058da03c6b01e3480b19c058ca03c6301e3080b17c098bc02c5d0162b80b154078a603c5201dbf81edf8076f603b7a01dbb81add8076e603b7201db781edb8076da07b6c01db580eda8076d203b6801db381ed98076ca08b6401db180ed88076c203b60015ab80ad58056aa03b4f01da700ed340f4fe06a7b0353b81e9cc0f4de07a6d03d358069a40f4ce08a6503d31806984094be04a5b0252b81294c0749e02a4b0152380e90c0747e03a3d01d1d8068e40746f5c23501d198068c40d2f406977034bb01a59c0d2cc06965024af81255c0729e0294701c9f80e4f40726e089350449782249c070fe0387701c3780e1b4070ce0386501c2f80e15c0709e0284701c1f80e0f40706e0383501c1780e09c05afe02d7e016bd81b5e805aee02d76016b981f5c805ade02d6e016b680b5b005ad607d6a016b48235a005ace02d66016b280b59005ac607d62016b081f580098fe04c7b0263b8131cc098de04c6d026358131a4098ce04c6502631813184058be02c5e01e2e80adfc056f602b77015b980adbc056da02b6b015b480ad9c056ca02b63015b080ad7c056bc02b5d015a780ad380569602b49015a1812d080568207a7f0353d81a9dc0f4e607a6f03d3681e9ac034d207a670453281e98c034c202a5f04d2e80a96c034b202a570152a80a94c034a204a4f0252581291c0948602a3f0151d80a8dc054660697a034bb81a5d80d2ce06966034b280a57c112ba02957014aa81253c0928e0293f0149b8224bc1124e0787f0343b81e1bc0f0da078670443280a17c1d0ba028570142a81213c0908e0283f0141b8260bc1304e04d6d02eb48135940bac202c6d01e3480b194078c207b7e035bd01add80f6e407b6e03db681edb00f6d408b69045b401ed98116ca08b6403db101ed840f6c002b5e00dad006d58056a403b4e00da5006d180768406a7a0353b01e9b40f4d401a6900d3401e998114ca08a6400d308169780b4a403a4e01d2100e8f80747a0697a034bb01a5980d2ca0893d0449a8224b41124a0386d01c3280e0f40706a0382d01c128135fc0baf604d7702eb98135bc09ada05d6b02eb481359c09aca05d6302eb080b1fc078f602c7701e3980b1bc058da03c6b01e3480b19c058ca03c6301e3080b17c058ba03c5b01e2d00b15c098ac02c5501dbf81edf8076fa07b7c01dbd80ede8076ee06b7601dba81add0076e603b7201db781edb8076da07b6c01db580eda8076d203b6801db381ed98076ca08b6401db180ed88076c203b60015af80ad78056ba03b4f01da700ed340f4fe06a7b0353b81e9cc0f4de07a6d03d358069a40f4ce08a6503d318069840b4be04a5b0252b81694c0749e02a4b0152380e90c0747e03a3d01d1d8068e40746f5923501d198068c40d2f406977034bb01a59c0d2cc0696502caf81255c0729e0294701c9f80e4f40726e089350449782249c070fe0387701c3780e1b4070ce0386501c2f80e15c0709e0284701c1f80e0f40706e0383501c1780e09c09ada05d69026b28175840f8fc06c7a0363b01f1c80f8dc07c6d03e3601f1a8118d208c6803e33023194118c807c6203e3081f180038bc02b6d01db480ad94076c202b4d01da480ad140768201a6d00d34806994034c201a45034bb01a5980b0bc0584e00c130135fc0baf604d7702eb98135bc09ada05d6b02eb481359c09aca05d6302eb08171fc0f8fc05c7b02e3d0171dc0d8ec05c7302e390171bc0f8dc05c6d03e360171ac0b8d405c6902e3401719c0f8cc05c650463201718c0b8c405c6102e3000717c038bc01c5d03dbf81adec0d6ee07b7303db780adb40f6d603b6903db380ad940f6c603b6102daf812d6c096ae05b5302da780ad340b69603b4902da380ad140b68603b4103d3f8069ec0d4ee01a7303d3781e9b4034d601a6903d33822994034c601a6100d2d812968034b204a570252b00694c034a204a47025230129141347e01a3b04d1b8068cc0d2f406977034bb01a59c0d2cc0696502caf81255c0b29e0594d02ca38225141127e0893700c9782249c0f0fe0687703c3781e1b40f0ce0886502c2f81215c0b09e0584d02c23d5c114b807e0983700c1780609c09afe04d7e026bd81b5e809aee04d76026b981f5c809ade04d6e026b68135b009ad607d6a026b48235a009ace04d66026b281359009ac607d62026b081f580098fe04c7b0263b8131cc098de04c6d026358131a4098ce04c6502631813184038be01c5e00e2e81edfc0d6f606b7703db981edbc056da07b6b01db481ed9c056ca07b6301db0812d7c056ba04b5b01dac812d5c056aa04b5301da8812d3c0969604b47025a181e9fc034f606a7700d3981e9bc0f4da01a6b00d3481e99c114ca01a6300d3081297c094bc05a5d025278129380349601a4900d218129080348209a3f00d1d8268dc034660697a034bb81a5d80d2ce06966034b281257c112ba04957024aa81253c0928e0893f0449b8064bc1124e0787f0343b81e1bc0f0da078670443281217c1d0ba048570242a81213c0908e0e83f04c1b8060bc0304e07d7f036bd81b5dc0fae607d6f026b681f5ac0bad207d67026b281f58c0bac202c7f01e3d80b1dc078e602c6f0163680f1ac078d202c670163280f18c078c202c5f01e2d80b15c078a603b7f03dbf00edec076f403b77035bb00edcc076e403b6f03db700edb40f6d803b6b01db500eda4076d003b6703db300ed94116c803b6301db100ed84076c003b5f02daf00ed6c076b403b57025ab00ed4c076a401b4f00da7006d340f4fe01a7b0353b8069cc0f4de07a6d00d358069a40f4ce08a6500d31806984134be01a5b04d2b80694c0349602a4a00d2480a91c0548c01a4300d2080a8dc0546c02a35034bd01a5dc0d2ec06967034b301a594112be0895701ca780e5340528e0894501c9f80e4f40726e0893500c9782249c070fe0387701c3780e1b4070ce0386501c2f80e15c0709e0284701c1f80e0f40706e0383500c1780609c0f8de06c6b0363381f18c0f8be07c5b02e2c81f15c0f8a605c5103db781edb40d6d606b6a035b381ad98116ca02b63015af80ad740d6b606b5a015ab80ad58056aa02b54015a982ed3c176960bb4705da180a9bc054d602a670153180a97c054ba02a5b0152b80a954054a602a4f0152580a91c0548601a3f0151b80a8cc0f2de0196b034b380658c0f2be0795d00cad81e55c112aa0195304ca780652c1328e0194301c9f8224dc032660292f00c9580a49c032460786f0343381e17c0f0ba078570442a85613c2b08e0b83f05c1b80a0bc0504e0181f00c0b8135b40bad204d6502eb081f1f80d8f406c7603e3901f1b80f8da07c6c03e350231a4118d007c66046328231900f8c407c6103e30017178098b404c5602e2900adb4056d202b65015b0806d34034da01a6900d328069840349a06976034b301e1f80f0dc0786c0c42f00a1180506c0182603ebf81b5ec0daee07d7303eb78135b40fad605d6903eb38135940fac605d610163f80b1f8058f606c7a0163b80b1d8058e607c720163780b1b8058da02c6c0163581f1a8058d208c680163380b198058ca02c640163181f188058c207c600162f80b178058b604c5a0162b80b158058a605c52015bf80adec056ee02b73015b780adb4056d602b69015b380ad94056c602b61015af80ad6c056ae02b5300da7806d380369a07a7f00d3d81a9dc034e607a6f03d368069ac034d207a670453280698c034c209a5f00d2d82695c034a602a4f0152700e9340547e02a3e00d1d8068e40346602a3200d1881a5e80d2ee06976034b381a5980d2ca0895f044ab80a53c0529c0894da98a600a51c0528a029420149f8224f40526e0293500c978224b41124e0892503c3f81a1dc0f0de0786d03c338221950c0be7305701427d481340508e028450141f80a0dc0305e0982d00c138e00940f8de06c6b0363381f18c0f8be04c5d03e2d8171640f8ae04c5503e298171440f6de06b6b035b381ed8c0f6be02b5d03dad80ed640f6ae02b5503da980ed46ba69f5b34bad1a3d60d0c0f4de06a6b0353381e98c0f4be07a5d03d2d8069640f4ae08a5503d29806946ac49e0ca4baa92383290ea847e0ca3ba891b8328cc0d2d406967034b301a55c0d2ac06955044a782251c1127e089370449782249c0f0de0686703c2f81e1740f0ae08855428279c811cb407e49037064178dc09c09ade05d6b026b381758c058de02c6e0163580b1a80d8ce06c660163180b188078be03c5e015b780adac056ce02b63015ad80ad5c056a602b47015a281a9bc0d4d606a670353181697c094b604a5702d2982693c1349a09a4b00d2482691c1348a09a4300d2080a8fc0547602a37015198139fc0bcf604e7702f3980b5fc0dafc02d7b016bd00b5dc0daec02d73016b900b5bc07adc02d6d0163f80b1ec058ee02c73016358131a8058d202c670163300b18c058c202c570162b00b1540d6fe06b7b035bb81adcc0b6de04b6b025b3816d8c056be02b5d015ad806d64056ae09b55015a9806d440569e02b4b015a380ad0c0d4fc0697602cb7012598052bc0295c014ab53c5500529c0294600c9f0264d809ade04d6b026b381358c058de03c6b0163380f18c058be02c5701e2980edbc076dc03b6b01db501ad9c0d6cc03b6301db100ad5c056ac03b4f01da701a9bc0d4d606a670353181297c094b604a570252980e93c0549602a4701d218328fc1547a09a3b00d1c8328dc1546a09a3300d188139fc09cf604e770273980b5fc07af602d7701eb980b5bc09adc02d6d016b380b59407ac603d6201e3f81b1f8078f603c7a01e3b81b1d8078e603c720163380b198058ca03c5f01e2f00f1740d6fe06b7b035bb81adcc096de04b6b025b3812d8c076be02b5b015ab80ed4c0769e03b4d01da5806d240768e0cb4501da1806d040d4fc06976024b7012598072bc0295601ca700e5300728d4d14400c9f0324d805ade02d6e036b581b5a805ace02d66016b180b588098de04c6b0263381318c078be03c5d015b780adac056ce02b63015af80ad740569e02b4b015a181a9bc0d4d606a670353182697c134ba09a5b00d2c82695c134aa09a5300d2881293c0949604a470252180a8fc0547602a370151980b9fc05cfc02e7b0373d00b9dc05cec02e73037390135fc09af604d77026b980b5bc05adc03d6d0163f80b1ec058ee02c730163780b1b8058da02c5f0162f00b16c058b202c530262900b1440d6fe06b7b035bb81adcc056de09b6d015b5806da4056ce02b65015b1806d84096be04b5b025ab812d4c0569e02b4b015a380ad0c0d4fc06976014b752c5b0052cc02964024af0125580529c0294600c9f0264d809ade05d6b026b381758c058de03c6b0163380f18c058be03c5b0162b81adbc0d6dc03b6b035b381ad8c0d6c402b5f01da781a9bc0d4d606a670353181697c094b604a5702d2980e93c0549602a4701d218328fc134760ba3704d1981a5980b2bc0394e0a49f02a49809ade05d6b026b381758c058de03c6b0163380f18c058be03c5b0162b80edbc076dc03b6b01db501ad9c0d6cc03b6301db100ad7c056bc03b4f01da701a9bc0d4d606a670353181697c094b604a5702d2980e93c0549602a4701d218328fc1547a09a3b00d1c8328dc1546a09a3300d188139fc0bcf604e7702f3980b5fc07af602d7701eb980b5bc05ada03d6b01eb500b59c09acc02d6501e3f81b1f8078f603c7a01e3b81b1d8078e603c720163780b1b8058da03c5f01e2f00f1740d6fe06b7b035bb81adcc0b6de04b6b025b3816d8c076be02b5b015ab80ed4c0769e03b4d01da5806d240768e0cb4501da1806d040d4fc03a46a492201a5d80b2dc0496601caf00a5580729c0394c01ca35205100327c0a936036b781b5ac0dace06d630363781b1ac0d8ce06c63a722fd3116e948af47453035b781adac0d6ce06b63065af832d6c196ae0cb53065a7832d2c1968e0cb430353701a5980b2bc0495601ca700a5180327c0c936016b780b5b805ace02d63016b10131bc0b8d604c6702e3181317c098ba05c5b01e2c81315c098aa03c5301e2880adbc056d602b67015b180ad7c056ba02b5b015ac80ad5c056aa02b53015a880ad3c0569602b49015a380ad0c0568206a6f0353581a99c0d4c609a5f04d2e82696c034b209a5704d2a82694c034a205a4f0252581291c0b48602a3f0151d80a8dc054660696f014b381e57c0f2ba02957014aa81653c0928e0293f0149b8224bc1124e0686f0343383617c1b0ba0d85706c2a81613c0908e0283f0141b8260bc1304e04d7f026be8175ec0baf204d77026ba8175cc0bae204d6f02eb581359c0bac602c7f0363f00b1f68a8f802c7b0163d00b1e4058f002c770363b00b1d40d8e802c730163900b1c4058e002c6f0363700b1ac058d402c670363300b18c058c402c5f01e2f00b174056fe02b7e015be80adf0056f602b79015bb80add4056e606b72015b880edc0056de02b6b015b380ad8c056b604b5a015ac80ad5c056ac02b53015a880ad1c0568c02b450353f8269f40d4f601a790353b81a9d40d4e601a710353781a9ac0d4ce06a6302d2f81296c094ae05a530152780a9340549601a49015238269140548601a410151f80a8ec0546e02a33034bf81a5f80f2fa0696f034b701a5880b2be04957014a780a5340528e089450149f80a4dc1125e089270343f8361f40d0ee068750343781a19c0b0be048570142780a1340508e0d8450141f80a0dc1305e098270440e83605407ade03d6e01eb380f58c07ac404c6f0263581319c098c602c5f0162e81316c098b204c570162a81314c098a202b6f01db580ad9c076c602b5f015ae80ed6c076b202b57015aa80ed4c076a202b4f025a700ed2c0568e03b4301da101a9bc0d4d606a670353182e97c154ba09a5b00d2c82e95c154aa09a5300d2881293c0949604a470252180e8fc0547602a3701d1981a5bc072ce0795f03cae80e55c072aa0494f024a380e4fc0526e0892f0449380e1bc070ce0385f01c2e80e15c070aa0384f01c2380e0fc0506e0382f01c138135f409af204d75026b880b1f4078f202c7501e3881adf8156fa0ab7c035bd01ade40d6f006b76035ba81add00d6e411b710bdb801adb80d6d406b66035b1006d78056b402b5600da900ed380369401b4601da101a9f8134fa0aa7c00d3c81a9d40d4e401a7100d3801a9b80d4c404a5a0252b00e9380748403a3e01d1e81a5f80f2fa0696e034b10224f41126a0892d0449280e1f4070ea0383d01c1a80e0b40704a0381d01c0a8135fc09afc04d7d026be0135ec09af204d77026ba8135cc0dae404d7102eb80135bc09ad604d67026b180b1fc058fa03c7b01e3c80b1dc058ea03c7301e3880b1bc078d602c6701e3180b17c098bc02c5d0162b80b154078a603c5201dbf81adf8076fb4337c01dbd80ede8076f203b7801dbb81add8076ea06b7401db980edc8076e203b7001db781adb8076d603b6a01db381ad98076c603b62015ab80ad58056aa03b4f01da700ed340d4fe10a7d0353d8069e40d4ee06a75035398069c40d4de06a6b0353381a98c094be04a5b0252b81294c0749e02a4b0152380e90c0747e03a3d01d1d8068e40746f4223501d198068c40d2fe0697e03cbe81a5bc0d2dc06962024af81255c0729e0294701c9f80e4f40726e089350449782249c070fe0387d01c3b80e1d4070de0386701c2f80e15c0709e0284701c1f80e0f40706e0383501c1780e09c0703a03815026b78135ac09ace04d630163780b1b8058ce02c630163101317c098bc03c5b01e2d01315c078ac04c530262900adbc056d602b67015b180ad7c056bc02b5b015ac80ad5c056a604b52015a880ad3c0569a02b4b015a480ad1c0568a02b43015a081a9bc0d4d606a670353181297c094b604a570252982693c1349a09a4b00d2482691c1348a09a4300d2080a8fc0547602a370151981a5bc052ce0495f024ab81e53c0f29a02947014a280a4fc0526e0892f0449381a1bc0d0ce0485f0242b83613c1b09a0d84706c2280a0fc0506e0982f04c1380b5fc05afc02d7d016be00b5ec0daf402d79036bc00b5dc05aec02d75016ba00b5cc0dae402d71a02b800b5bc05adc02d6b036b500b59c05acc02d63036b10131fc098fa04c7b0263c8131dc098ea04c73026388131bc098d604c670263180b17c058bc03c5d015bf80adf4056f602b79015bb80add4056e602b71015b780adac056ce02b63015af80ad78056ba02b4f015a700ad2c0569202b43025a100ad040d4fe09a7d0353d8069e40d4ee06a75035398069c40d4de06a6b0353381a98c054be09a5d0152d806964054ae02a55015298069440949e04a4b0252381290c0547e02a3b0151b80a8cc0d2fe0697e03cbe81a5bc0d2dc06962014af822574052ae02955024a781251c0527e029370449782249c0d0fe0d87d0343b81a1d40d0de068670142f836174050ae028550242781211c0507e0283704c1782609c1103a0d815 20 1048575 8 255 11 2047 21 2097151
def cc_56_11 : Nat → List (Nat × Nat) := unpackCursorV4 0xc326abf33fb53a0ae96aa49a09dd6c977668d3a48656e7f66f7a94d761486b5ac6783d633456072c5b4535ad075684555f095332c4e0534796740f6a3759a30b6a2719a2056c1679e0f7700619600061 0x16b78135ac09ad204d67026b1813584058de02c6b0163380b18c058be02c5b0162b80b14c056de02b6e015b580ada8056ce02b6602db1816d88056be02b5e025ad812d68056ae02b56015a980ad480569e02b4e00da5806d280568e01b46015a180ad080f4de01a6b0353380698c094be01a5b0252b80694c0549e01a4b0152380690c0747e03a3d00d1d8068e40946e03a3500d198068c40f2de0696b034b381e58c092be0495b024ab81254c0529e0294b014a380a50c3727e0b93d0449d86e4dc1726a0893300c978224ac1324e0192303c378061ac0d0ce018630242f80616c090ae018530142780612c0508e018430741f83a0f4030760e8370741a8060cc0305e0182b00c1380608c1103e0181b0740b80604c0bcfc05e72026b6813594058fc06c7a0163b01f1c8058dc02c6d0163602f1a8058d20bc680163300b194058c80bc620163085f180058bc04c5a0162b013148056da02b69015b280ad840369c01b4d04d368069a4134ca01a610152700e9340547c01a39015190068c40f2fc07972024b70125b4092b404956014a70225341729802945014a10224f40526a0892d0449283a1b4170ca0e84d014228260b41d04a0881d05c0a8139fc0bcfc04e7d026bd81b5e809af204d77026bb0135cc09ae204d67026b3013594058fe02c7e0163d81b1e8058ee02c760163981f1c8058de02c6e0163680b1b0058d604c6a01634df91a0058ce02c660163280b190058c604c6201630813180058be02c5e0162d813168058b204c580162b80b158058a604c5201628817140056fe02b7b015bb80adcc056de02b6d015b580ada4056ce02b65015b180ad84056be02b5b015ab80ad4c0369e01b4e00da681e9fc034f606a7700d398129bc094da01a6b00d3481299c134ca01a6300d3081297c034b604a5700d2980a93c0549c03a4d0151f80a8f80347601a3900d1980a8c8034620797f034bd81a5dc0f2e60496f024b68125ac092cf7d165024b181257c092b604957024a980a53ee229a0294b014a380a514052860293f7209e80a4ec0526e02935014998064bc1325a0892b04c93ac0494032460787f00c3d81a1dc030e60486f024368061ac090ce0e86500c3181217c030b60485700c2980a13c1d09a0184b0142380a114030860283f00c1d80a0dc030660182f04c168060ac0304e0e82500c1182207c030360e81700c098135bc0dadc02d6b026b381758c0bac402c6f0163580b19c058c602c5f0162d80b15c058a602b6f015b7012dac096d402b67015b300ad8c056c402b5f015af00ad6c056b402b57015ab016d4c0b6a402b4f015a7006d2c0369402b4700da300ad0c0568406a6f00d3581a99c034c605a5f00d2d81295c034a602a4f00d2580a91c0348603a3f01d1e8068ec0347205a3701d1a8068cc034620696f034b581a59c0d2c60595f024ad81255c0b2a60294f014a580a51c052860893f0449e8224ec1126e08935044998064bc112560892700c9181a1bc030d60686700c3181617c030b60485700c2980a13c030960284700c2182a0fc1b07a0183b0541b82a0d4030660182f00c1580609c030460881f00c0d82205c0302604e7f0373f0139f409cee04e7502f398179c809aee04d76026ba8175bc0badc05d6d0163f80b1f8058f606c7a0163c81b1e0058ee02c760163981b1c8058e207c700163780b1b8058d604c6a0163380b198058c605c620162f80b178058ba02c5c0162d817168058b37b4580162b80b158058aa02c5401629817148058a205c50015bf80adec056ee02b73015b780adac056ce02b63015af80ad74056b602b59015ab80ad54056a602b5100da7806d380369a06a7f00d3d81a9dc034e605a6f00d3581299c034c605a5f02d2e80696c034b205a5704d2a80694c034a202a4f0152700e9340547e02a3e00d1d8068e40346602a3200d1881a5fc0d2f606977034b98165bc092d60496702cb181657c0b2ba0595b02cab8225540b2a60294f044a680a52c0528e02945014a180a4fc1127a0293b0149b80a4d4052660192f044968224ac1124e0892500c9181a1fc030f60687700c398161bc030d60486700c3181617c0b0ba0185b02c2b836154030a60284f06c2680612c0508e0284500c2180a0fc030760283700c198060bc1305a0182b00c1382a094030460881f00c0d82205c0302604d6f026b70135ac09ad202d67026b181b58809ac202c6f0163580b19c058c602c5f0162d80b15c058a602b6f015b7016dac0b6d402b67015b300ad8c056c402b5f015af012d6c096b402b57015ab00ad4c056a402b4f015a7006d2c0369402b4700da300ad0c0568406a6f00d3581a99c034c604a5f00d2d81295c034a602a4f00d2580a91c0348603a3f01d1e8068ec0347204a3701d1a8068cc034620696f034b581a59c0d2c60495f024ad81255c092a60294f014a580a51c052860893f0449e8224ec1126e08935044998064bc112560892700c9181a1bc030d60686700c3181217c030b60485700c2980a13c030960284700c218360fc1b07a0183b06c1b8360d4030660182f00c1580609c030460881f00c0d82205c0302605d6f00eb581b59c0dac604c6f00e3581319c098c604c5f0262d80b15c098a602b6f015b5812da8056d203b68015b380ad98056c602b61015af80ad6c0d6b402b57015ab00ad4c0569e02b4b025a500ad1c0568c02b430153780a9ac154d402a690153380a998054c602a610152f80a96c054ae02a530152780a92c0548e02a4300d1f8068f80347a0896f044b68225ac112ce08965044b181a57c0d2b606957034a981253c0929604947024a180a4fc05276029370149980a4bc1125a0292b0149380a494052460a86f054368061ac150ce0d86500c3181a17c030b60685700c2981213c030960484700c2180a0fc030760283700c1980a0bc030560282700c1182207c030360881700c098139fc09cfc05e7d026bf8135f809afa04d6f026b70135ac09ad204d63036b1013584058fe02c7e0163e80b1f0058f604c7a0163c8131e0058ee02c760163a80b1d0058e604c7201638de51c0058de02c6e0163581b1a8058ce02c660163181b188058be02c5e0162d813168058ae02c5601629813148056fe02b7e015be80adf0056f602b79015bb80add4056e604b72015b880edc0056de02b6b015b380ad8c056be02b5b015ab80ad4c0369e01b4e00da68129fc094fc09a7dbc13e0069ec034f204a770253a8069cc094e401a7100d3801a9bc034d606a6700d3181297c034b604a5700d2980a93c0549c03a4d0151f80a8f80347601a3900d1980a8c8034620497f044be8125ec092ee04975024b981a5bc0d2d606967034b181257c092b604957024a980a53c1129a0294b014a380a514052860293f0449e80a4ec0526e02935014998064bc1125a0892b04493822494032460487f06c3e8061ec090ee0487500c3981a1bc030d60686700c3181217c030b60485700c2980a13c1b09a0184b0142380a114030860283f00c1d80a0dc030660182f04c168060ac0304e0d82500c1182207c030360881700c098135bc0bad604d67016b180b1bc058d602c670163180b17c058b602c570162980adbc056dc02b6b015b500ad9c056cc04b63025b100ad7c056bc02b5b015ad00ad5c056ac05b5302da900ad3c0569c01b4b00da500ad1c0368c02b43015a101e9bc034d606a6700d3181697c034b604a5700d2980a93c0349602a4700d2180e8fc0747a01a3b00d1c8168dc0746a01a3300d1881e5bc0d2d60696703cb181657c092b60495702ca980a53c2129a0294b014a380a514052860a93f05c9e8224ec1526e0a935044998064bc1325a0892b04c9382a494032460786f00c3581a19c030c60585f00c2d81215c030a60284f00c2580a11c030860a83f07c1e8060ec1506e0a83500c198060bc1305a0182b00c1382a094030460881f00c0d85405c0302604d6f02eb581359c05ac604c6f00e3581b19c0f8c605c5f00e2d81315c0b8a602b6f015b700adac056d202b67015b181ed88056c202b5f015af00ad6c056b202b57015a9816d48056a205b50015a780ad380569602b49015a380ad0c0b68402b4101da000a9bc054d602a670153180a97c054b602a570152980a93c0549c02a4b0152480a91c054860aa42015208068fc0347c01a3d03cb781a5ac0d2ce0796302caf81256c092ae05953054a782e534112960a947054a282250c0527e1193d0149d80a4dc0526a02933014978424b405256029270149280a48c0f0de0186b0343380618c0b0be0185b0242b80614c1509e1684d00c2582a11c1508a018430141f85a0f403076028370141a8060cc0505e0182b0141380608c1103e0181b08c0b80604c09afc04d7202eb7017588058fc06c7a0163b01f1c8058dc04c6a01633017188058bc02c5d0162e02f168058b20bc580162b00b154058a80bc5201628867140056ba0bb5a015ac80ed60056ac02b55015aa00ad440369c01b4d04d2e826968034b201a580552b026954154a801a510152700e9340547c01a39015190068c40f2fc0797202cb70165880b2bc0595d044a680a5280528c02945014a20224f405274029360149a80a4d01125a0892a04c93022494152480f85d05c2adb41340508a0982d054128220741702a04d7e00eb90175b803ac402c7e0363d00b1d80f8e402c6e0263500b1980b8c402c5e0162e80b1701f8b402c5907e2c00b158058aa02c5407e2900b144258a002b5d015ac80ad54056a201b4e00da6806974034b401a5900d2c02a958034aa0aa5400d2880a9380349a02a3e00d1c8068c8034620b95d05caa8765340528a0393d0149a8064b41524a0787e00c390161b8030c40585e00c2e806134030940284600c2280a110030740283600c168060a80304c01825054120060681f02c04e7f0273e8179ec0bcf404e770373b0139d409afe04d7e026be8175bc0badc05d6d0163f80b1f8058f606c7a0163c81b1e0058ee02c760163981f1c8058e207c700163780b1b8058d604c6a016348131a0058ce02c6601631817188058c205c600162f80b178058ba02c5c0162d817168058b3764580162b80b158058aa02c5401629817148058a205c50015bf80adec056ee02b73015b780adac056ce02b63015af80ad74056b605b5a015ac80ed60056ae02b56015aa80ad50056a602b5100da7806d380369a07a7f00d3d81a9dc034e605a6f00d3581299c034c605a5f02d2e80696c0b4b401a5900d2c01695c0b4ac09a55ba92a00694c034a202a4f0152700e9340547e02a3e00d1d8068e40346602a3200d1881e5fc0d2f60697703cb98165bc092d60496702cb181657c0b2ba0595b02cabdd05540b2a60294fb80a680a52c0528e02945014a180a4fc2127a0293b0149b80a4d4052660192f04c968224ac1324e0a92500c9181e1fc030f60687700c398161bc030d60486700c3181617c0b0ba0185b02c2bdcc154030a60284fb602680612c0508e0284500c2180a0fc030760283700c198060bc1305a0182b00c1382a094030460881f00c0d85005c0302605e7e0273e81b5e809af204d76026b881359809aca07c7e0363d01b1d80f8e404c6e026368131b0098d40bc6905e34013198238ca11c6402631013184098c004c5e0262d013158098a402b6d015b480ad94056c201b4d00da28129b4034d209a6500d3080e9340748a0797e03cb90125b4092d404966044b282e590092bc04952014a300a514052740293604495026498090da0e8650742683a1141103a0e8150273e8179e80dcec04e75026bf0135f40badc05d6d03e3f01b1e80d8ec07c7202e370131a8098cc05c6202e2f0171740b8b805c5a05e2c82f1600b8ac11c5508e2a0171480b8a205c50015ae816d68056b203b58015ab00ad54056a802b5100da6806d140b4ba05a5a00d2c8069600b4ac09a5508d2a0069440749a03a4503cbf01e5c80b2dc0596202caf0165740b2b80895502ca900a5180528a0293a0149b0224a81324c0585d0ec2a8621343108a0881d0900a83b5bc11ad608d670c6b183f1bc0f8dc08c6b0363502319c0d8cc0fc6303e3103f17c0b8bc0ec5b0262d03b15c098ac0fc5302e2900adbc056d602b67015b180ad7c056b602b57015a9806d3c0369a01a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d268068fc0347601a3305c275c55bc11ad608d67b82b18471bc0f8dc08c6b0363502319c0d8cc0bc6303e3104717c0b8bc0bc5b0262d04715c098ac0bc5302e2900adbc056d602b67015b180ad7c056b602b57015a9806d3c0369a02b4700da280ad0c134de01a6b0453380698c134be01a5b04d2b80694c0749e03a4d04d2380e9140348602a3f00d1d80a8dc034660896fa98b702259c192c40b95f850af02e55c192a402947014a300a5140527e0293a0149b80a4d80325e0992a04c938264994a0de088674482f9d815c1709e1304d08c23dbc1140507e0283700c1780609c1903a110150b62e02f160178a80fc5005ca203e1701702804e7d02f3d01b9d809cea04d7e026be8175b80bada07c7e0363d01b1d80f8e405c6e026350131980b8c405c5e02e2e8171700b8b40fc5907e2c0171582d8aa16c5402e290171440b8a002b5d01dad00ad64076b002b56015aa80ad50056a201b4d00da2806974034b401a5900d2c016958034aa16a5400d288069340348a0595db68aa862536d628a0787e00c390161b8030c40585e00c2e816170030aa0185201423006114030740283600c15006098030341881602e2e073160178a805c5001dac00ad50034b011a5405caa03b5bc11ad608d67b5ab182f1bc0f8dc08c6b0363502319c0d8cc0bc6303e3102f17c0b8bc0bc5b0262d02f15c098ac0bc5302e2900adbc056d602b67015b180ad7c056b602b57015a980ad3c0569a01a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d268068fc0347601a3305ca703b5bc1bad60dd67b62b185b1bc0f8dc0dc6b0363503719c0d8cc0fc6303e3105b17c0b8bc0ec5b0262d03b15c098ac0fc5302e2900adbc056d602b67015b180ad7c056b602b57015a9806d3c0369a01b4700da2806d0c034de01a6b00d3380698c034be01a5b00d2b80694c0349e01a4d00d238069140348601a3f00d1d8068dc034675216f06cb3c2457c1d2ae0f94f098a685a51ed428a0293f0149b8064bc0324e0186f5203700619c030c40185f4402f00615c030a401847014230061140307e0183a00c1b80a0d80305e0182a00c138060980303410016be2b7de95aeeeacf725630163780b1b8058d606c6a0163380b198058c607c620162f80b178058b604c5a0162b80b158058a605c52015b780adac056ce02b63015af80ad6c056ae02b5300da7806d380369a09a6f00d3582699c034c609a5f00d2d82695c034a602a4f0152700e9340547e02a3e00d1d8068e40346602a3200d18d445bc192d727167064b1c2057c192b6f4157064a980a53edc29a0294b014a380a514052860293f7189e80a4ec0526e02935014998064bc1325a0992b04c93abc49403246a306f00c35a4819c030c68705f00c2d9d415c030a60284fb482680612c0508e0284500c2180a0fc030760283700c198060bc1305a0182b00c138e4094030460c81f00c0d83c05c0302605d6f02eb70075ac03ad401d6700eb300758c03ac401c6f0263581b1a8098ce04c660263180717c038ba01c5b00e2c81315c098aa01c5300e2880adbc076d602b6701db180ad7c056ba03b5b01dac80ad5c056aa03b5301da880ad3c0769602b4701da18069bc034d601a6700d3180697c034ba01a5b00d2c80695c034aa01a5300d2880693c0349601a4700d218068fc0347601a3700d1981e5bc0d2d60696703cb183257c172ba0895b064ab82e554112a60494f024a581251c092860393f0149d80a4dc072660192f00c9580649c032460186f00c3580619c030c60185f00c2e80616c030ae0185500c2980613c030960184700c218060fc030760183700c198060bc030560182700c1180607c030360181700c098139fc0bcfc04e7d026bd81b5e809af204d77026bb0135cc09ae204d67026b3013594058fe03c7b0163b80f1cc058de02c6d01e3580f1a4058ce02c6501e3180f184058be03c5b0162b80f14c036fe01b7b00dbb806dcc036de01b6d00db5806da4036ce01b6500db1806d84036be01b5b00dab806d4c0369e01b4d00da5806d280368e02b4600da28069fc0f4fc01a7d03d3e0069ec034f401a770353b0069d40d4e801a7300d390069bc094dc01a6d025360069ac034d401a6900d3400699c094cc01a65b393200698c034c401a6100d3000697c094bc01a5b00d2d00695c094ac01a5300d2900693c0749c01a4d00d1f8068f80347a0797f034bd81a5dc0f2e60496f024b68125ac092ce0b965024b181257c092b604957024a980e53c052960294701ca18064fc032760193700c998064bc0325a0192b00c93832494032460187f00c3d8061dc030e60186f00c368061ac030ce0186500c3180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc0305a0182b00c13806094030460181f00c0d80605c0302604d6f026b68075ac09ace04d6502eb18071bc038dc01c6b00e3501319c098cc01c6300e3101717c0b8bc01c5b00e2d00715c038ac01c5300e2900adbc076d602b6701db180ad7c076b602b5701da980ad3c0569a03b4b01da480ad1c0568a03b4301da08069bc034d601a6700d3180697c034b601a5700d2980693c0349a01a4b00d2480691c0348a01a4300d208068fc0347601a3700d1981a5bc0d2d606967034b181657c092b60495702ca982253c1129a0894b044a3822514112860393f0149d80a4dc072660192f00c9580649c032460186f00c3580619c030c60185f00c2d80615c030a60184f00c2680612c0308e0184500c218060fc030760183700c198060bc030560182700c1180607c030360181700c098139fc0dcfc04e7d0273b8139d40bce605e72026bb8135d809aea05d6f02eb70175b4058fe03c7b0163b80f1cc058de03c6b0163380f18c058be02c5d01e2d80f164058ae02c5501e2980f144036fe01b7b00dbb806dcc036de01b6b00db3806d8c036be01b5d00dad806d64036ae01b5500da9806d440369e01b4d00da5806d280368e02b4600da28069fc0d4fc01a7b00d3d0069dc0d4ec01a7300d390069bc0b4dc01a6d02d360069ac034d401a6702533006994094c801a6300d3100697c0b4bc01a5d02d2e00696c034b401a5900d2c00695c0b4ac01a55b292a00694c034a401a5100d2800693c0749c01a4d00d1f8068f80347a0697f034bd81a5dc0d2e60596f024b581259c0b2c60595f02cae81656c0b2ae0895502ca980e53c052960294701ca18064fc032760193700c998064bc0325a0192b00c93822494032460187f00c3d8061dc030e60186f00c3580619c030c60185f00c2e80616c030ae0185500c2980613c030960184700c218060fc030760183700c198060bc0305a0182b00c13806094030460181f00c0d80605c0302605d6f02eb68075ac03ad201d6700eb280758c03ac204c6f026368071ac038d201c6700e3280718c038c204c5f0262d80715c098a602b6f015b680edac076d202b67015b280ed8c076c202b5f01dad80ad5c076a602b4f01da580ad1c0768601a6f00d368069ac034d201a6700d3280698c034c201a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1e8068ec0347401a370151b0068d4034660896f044b68225ac112ce08965044b181a57c0d2b606957034a981253c0929604947024a180e4fc052760293701c998064bc032560192700c918061bc030da0186b00c33806194030c60185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660182f00c1580609c030460181f00c0d80605c0302604e7f0273f0179f409afe04d7e026be8135bc09adc04d6b026b481358c0dac404d610163f80b1f4078f603c790163b80b1d4078e603c710163780f1ac058ce03c630162f80f16c058ae03c5300dbf806df4036f601b7900dbb806dd4036e601b7100db7806dac036ce01b6300daf806d6c036ae01b5300da7806d340369601b4a00da380ad180368a01a7f0253f0069f6c64f801a7b00d3d0069e4034f001a770253b0069d4094e801a7300d390069c4034e001a6f035370069b40f4d801a6b00d3500699c0d4cc01a650353200698c034c401a5f0252f0069740b4b801a5b00d2d00695c094ac01a550252a00694c034a401a4f01d270069340347e01a3e00d1e8125fc112fa0497b024bb8125d4092e60696f034b581a59c0d2c60495f024ad81255c092a60394f014a580a51c072860193f00c9d8064dc032660192f00c968064ac0324e0892500c918061fc030fa0187b00c3b8061d4030e60186f00c3580619c030c60185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660182f00c168060ac0304e0182500c1180607c030360181700c098135bc09ada05d6b02eb501359c0dacc04d6500eb18131bc098dc01c6b00e3500719c038cc01c6300e3101717c0b8bc01c5b00e2d00715c038ac01c5300e2900adbc076d602b6701db180ad7c076b602b5701da980ad3c0569a03b4b01da480ad1c0568a03b4301da08069bc034d601a6700d3180697c034b601a5700d2980693c0349a01a4b00d2480691c0348a01a4300d208068fc0347a01a3b00d1d0068dc0546c01a3500d1981e5bc0d2d60696703cb181657c092b60495702ca983253c1729a0894b064a382e514112860393f0149d80a4dc072660192f00c9580649c032460186f00c3580619c030c60185f00c2d80615c030a60184f00c2680612c0308e0184500c218060fc030760183700c198060bc030560182700c1180607c030360181700c098139fc09cfa05e7b02f3d0139dc0dcec04e75026bf8135f809afa05d6f02eb70175b4058fe03c7b0163b80f1cc058de03c6b0163380f18c058be02c5d01e2d80f164058ae02c5501e2980f144036fe01b7b00dbb806dcc036de01b6b00db3806d8c036be01b5d00dad806d64036ae01b5500da9806d440369e01b4d00da5806d280368e02b4600da28069fc0f4fc01a7b00d3d0069dc0d4ec01a7300d390069bc0b4dc01a6b00d3500699c094cc01a6300d3100697c0b4bc01a5d02d2e00696c034b401a5900d2c00695c0b4ac01a55b092a00694c034a401a5100d2800693c0749c01a4d00d1f8068f80347a0797f034bd81a5dc0f2e60596f024b581259c0b2c60595f02cae81656c0b2ae0b95502ca980e53c052960294701ca18064fc032760193700c998064bc0325a0192b00c93832494032460187f00c3d8061dc030e60186f00c3580619c030c60185f00c2e80616c030ae0185500c2980613c030960184700c218060fc030760183700c198060bc0305a0182b00c13806094030460181f00c0d80605c030276656fb22b5d8959ec0ac602c6f01e3580b19c078c602c5f01e2d80b15c078a601b6f00db5806d9c036c601b5f00dad806d5c036a601b4f00da6806d2c0369401b47015a3006d14034de07a6e00d358069a8034ce06a6600d31806988034be05a5e00d2d806968034ae04a5600d298069480349e03a4e00d268068fc0347c01a3d064b78325ac192ce0c963064af83256c192ae0c95301ca780a52c0528e0394300c9f8064ec0326e0193300c978064b403256019270649280648c030de0186b00c3380618c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c1580609c0304a0182300c0f80606c0302e01813 20 1048575 8 255 11 2047 21 2097151
def cc_56_12 : Nat → List (Nat × Nat) := unpackCursorV4 0xe234fdc261d6161cf76ac5d9abf568b8f66b523dab0a2a129e96da591e4f8bd618a5188693c8046576c986d4986389c59c9c539634d1684379a3cf683359a2d95c26f6a1d19e171601036e0659e00065 0x9ade05d6b026b381758c1f8de07c6e06e3581b1a81b8ce06c660963181f188038be01c5e00e2b80714c038a409b6f01db5826d9c076c605b5f01dad812d5c076a609b4f015a680ed2c0769209b47015a280ed0c0768201a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d2680692c0348e01a4500d1f8068ec0346e01a33ab8b783659c0b2be04957094a7e7c5341f28e1914501c9f8264dc0325e0192700c3780619c030be0585e00c2b8061480309e0584e00c268060fc0306e0182f00c1500609c0304c0181a0b80b0135bc0bad604d6702eb18171bc0f8dc05c6b02e3501719c0d8cc05c6302e3100717c038bc01c5d04db7e9cdac136cfa436302daf812d6c096ae05b5302da780ad340b69603b4902da380ad140b68603b41d19378069af444ce01a6300d2d812968034b204a570252b00694c034a204a47025230129141347e01a3b04d1b8068ceac2de0c96b9b8b383258c0b2be0495b024ab81654c0b29e0594d02ca581651f4028a059437409f8264ec1326e0c93300c978324ac1924e01923530378061ad280ce0186302c2f80616c090ae0185302c278161340309605847cf02280610cbe07e0183b04c1b8060cc0305e0182b00c1380608c1903e0181b0b00b80604c09ade04d6b026b381358c138de09c6b04e3382718c098be04c5b0262b81314c036de01b6b00db3806d8c036be04b5e00dae806d5c036aa01b5300da9006d3c0369601b4700da18069bc0f4dc01a6b00d3500699c0d4cc01a6300d3100695c094ac01a5500d2780e9380349601a4a00d2380a9180348601a4200d1f8068f80347a0c96f064b583259c192c60495f024ad81255c092a60994f04ca582651c132860193f00c9d8064dc032660192f00c968064ac0324e0c92500c918061bc030d60186700c3180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc0305a0182b00c13806094030460181f00c0d80605c0302604d6f026b581359c09ac604c6f0263700b1ac058d404c670163301318c098c403c5f01e2f00716c038b403c5700e2b00f14c078a402b6f01db580ad9c076c602b5f01dad80ad5c076a602b4f015a680ed2c0769202b47015a280ed0c0768206a6f00d3581a99c034c604a5f0252f00696c074ae01a530252901693c0b49a01a4b00d2480e91c0748a01a4300d2080e8fc0347602a3700d1981a5bc0d2d606967034b181257c092b604957024a982253c1129a0894b044a3822514112860393f0149d80a4dc072660192f0449582249c032460386f00c3580e19c030c60385f00c2d80e15c030a60384f01c2680612c0708e0384500c2180e0fc030760283700c198060bc030560182700c1180e07c030360381700c098139fc09cfc04e7b0373d0139e40dcf004e770273b0139cc0dce404e7103f380135fc09af604d77026b98075bc03adc01d6d0163f81b1f8058fa02c770163a80f1cc078e402c6f0163680f1ac078d202c670163280f18c078c202c5f01e2d80b15c078a602b77015bb00add4076de04b6e01db6e6cdb0076d603b6a01db480eda0076ce04b6601db2812d90076c603b6201db080ed80076be04b5e01dad80ed68076ae04b5601da980ed480769e03b4e01da681a9fc034f606a7700d398129bc094dc05a6d0252f812978034b601a5900d29812948034a203a4f00d2580a91c0348603a3f01d1e8068ec0347203a3704d1a8068cc034620697f034bd81a5dc0d2e60496f044b68125ac092ce04965024b181257c092b604957024a980e53c052960294701ca180e4fc0727a0393b01c9b8224d4072660192f0449582249c032460387f00c3d80e1dc030e60386f01c368061ac070ce0386500c3180e17c030b60385700c2980e13c030960284700c2180e0fc0707a0183b01c1b80e0d4030660182f00c1580609c030460381f00c0d80e05c0302604d6f026b581359c09ac604c6f016370131ac098d404c670263300b18c058c403c5f01e2f00716c038b403c5700e2b00f14c078a402b6f01db580ad9c076c602b5f01dad80ad5c076a602b4f015a680ed2c0769202b47015a280ed0c0768207a6f00d3581a99c034c604a5f00d2d80e95c034a605a4f02d2680692c0349203a4701d2280690c0348203a3f00d1d80a8dc034660796f034b581a59c0f2c60495f024ad81255c092a61094f05ca682252c2128e0b945044a180e4fc052760293701c998064bc112560992700c9180e1bc030d60386700c3180e17c030b60385700c2980e13c0709a0184b01c2380e114030860383f00c1d80a0dc030660182f00c1580609c030460381f00c0d80e05c0302604d6f026b70135ac09ad204d67026b181f58809ac204c6f0263581319c098c601c5f00e2f007174056de03b6b015b380ed8c056be03b5b01dac80ad5c076a603b51015a780ed2c0568e03b43015378069ac0d4ce07a630252f812978074b603a5901d2b80e94c074a403a5101d2801293c0949c04a4b0252480e91c0948604a420552080e8fc0347602a3701d1981e5bc0d2d60696703cb181257c172ba0495b024ab812554092a60494f024a581251c092860393f0149d80a4dc072660a92f0449582a49c112460386f00c3580e19c030c60385f01c2e80616c070ae0385500c2980e13c030960384700c2180e0fc030760283700c1980e0bc030560382700c1180e07c030360381700c098139f80dcf404e7603f390075b803ada02c6d01e3480b194078c202b7e015b9012db8176da0bb6c025b5012da4096d004b66025b2812d90096c414b610a5b0012d78096b404b56025a900ed380768404a6e02d36812978034b204a5200d288268f40347209a3500d1881e5f80f2e40896d024b5012598092ca04964024ad0125580729c0394201c9f00e4f4112540992601c3680e1940707a0383501c0e80e05409cfe04e7e0273d81b9e809cf206e780273b8139d809ce607e720273881f9c009afe04d7b026bb8135cc03ade01d6e00eb680b1fc058fa03c7b01e3d00b1dc0d8ec02c750163780b1b4078d603c690163380b194078c603c610162f80f16c058ae03c53015bf80adf8056fa03b6f025b700edb7326d803b6b01db500eda4076d003b67025b300ed94096c803b6301db100ed84076c003b5f025af00ed740b6b803b5b01dad00ed5c096ac03b55025aa00ed4c076a403b4f01da700ed340f4fe01a7b0353b8069cc094de04a6e02d3681297c094bc01a5b00d2c80694c094a401a5101d2780692c0548e01a4301d1f80e8f40347603a3a00d1c8068e00746e03a3604d1ae608d00346601a3103cbf81a5ec0d2ee07973024b782e5b4092d604967024b281258c092be0495b024ab81254c0729e0294b014a380e50c0727e0393d01c9d80e4df2e26a0393300c978224ac1324e0192301c3f8061ec070ee0187301c3780e1b4030d60386701c3280618c070be0185b01c2b80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e0181300f3f8079f803cfa04d7f026bf0135ec0daf404d79036bc0135dc09aec04d7303eb90135c40fae004d6f026b70135b409ad804d6b036b50135a40bad004d67026b301359409ac804d6302eb10135840bac004c7f0263d8131dc098e604c6f026368131ac0f8d404c6902e3401319c098cc04c650263201318c098c201c5f00e2f0071740f6fe06b7b035bb81edcc0f6de02b6d03db580eda40f6ce02b6503db180ed84096be02b5d025ad80ed64096ae02b55025a980ed440969e04b4b025a3812d0c034f601a7a00d3c8069dc0d4ec01a7300d3880699c0d4cc01a6500d2f812978034ba01a4f0252700692c0349201a4300d210069040347e01a3b00d1b8068cc0f2fe0697b034bb81e5cc0f2de0796d03cb581e59c192ca07963024af832574092b604957024aa81254c0929e0494b024a381250c1327e0893b04c9b8224cc0325e0192b00c9380648c030fe0187b00c3b8061cc030de0186d00c3580619c030ca0186300c2f806174030b60185700c2a80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182b00c1380608c0303e0181b00c0b80604c03cfe01e7e00f3e8135fc09afc04d7d026be0135ec0baf404d7902ebc0135dc09aec04d75026ba0135cc0dae404d7102eb80135bc09adc04d6b036b50135a40dad004d67026b301358c0dac404d6103eb00131fc098fc04c7d0263e0131ec098f204c770263a8131cc0d8e404c7102e380131bc098d604c670263180717c038bc01c5d035bf80adf40d6f603b79035bb80add40d6e603b71035b781adac0d6ce06b63025af80ad74096b603b59025ab80ad54096a603b51025a7812d2c0968e04b4300d3f81a9f8034fa01a6f035370069ac034d201a6300d31006984034be04a5e00d2e80693c0949c01a4b00d2480690c0348401a4100d200068fc0347601a3a00d1b8268d8034660697f044be81a5ec0d2ee06975034b981a5bc0d2d606967034b181257c112ba0495b024ab812554092a60494f024a581251c092860893f0449d8224dc112660192f00c968064ac0324e0892500c918061fc030fa0187b00c3b8061d4030e60186f00c3580619c030c60185f00c2e80616c030ae0185500c2980613c030960184700c218060fc030760183700c198060bc0305a0182b00c13806094030460181f00c0d80605c0302611d6f03eb70235ac0dad408d67036b302f58c0fac404c6f0263581319c098c601c5f00e2e81315c038aa04c5304db7822dac116ce0bb6304daf80ad74176b603b5904dab80ad54176a603b51025a7812d2c0968e04b43065378069ac114ce01a6302d2f816974194ae05a5500d2981293c0349604a4700d218268fc0347609a3700d198225bc112ce04957024ab0125540929e0494a024a38125181727ee613e04c9b8324c80325e0c92a05c938324981d0de0886705c2f83a1741d0ae0e8550242781211c1707e0983700c1780609c09ade04d6e026b581b5a809ace04d66026b181f588098de04c6b0263381318c038be01c5e00e2e826dbf346d609b67cb1b1812d7c056ba04b5b01dac812d5c056aa04b5301da8812d3c0969604b47025a1e549bc034d79426700d3181297c094bc05a5d025278129380349601a4900d218129080348209a3f00d1d8268dc034675516f064b5cd459c192c60495fc98ae81256c092ae04955024a981253c0929604947024a1b944fc1327609937064998064bc192560c92700c9183a1bc030d60e86700c3181217c1d0ba0185b0242b812154030a60484f00c2581211c030860e83f00c1d8260dc030660182f00c1580609c030460c81f00c0d83a05c0302604c5f02e2d81315c0b8a603b5f01dad80ed5c076a603b4f01da580ed1c0768601a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1d8068dc0346604c5f02e2d81315c0b8a609b5f04dad826d5c136a605b4f025a5812d1c0b68601a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1d8068dc034660195f00cad80655c032a60194f00ca580651c032860193f00c9d8064dc032660192f00c9580649c032460c85f0642d83215c190a60584f0242581211c0b0860983f04c1d8260dc130660182f00c1580609c030460181f00c0d80605c0302604d6f02eb581359c0bac609c6f04e3582719c138c605c5f0262d81315c0b8a601b6f00db5806d9c036c601b5f00dae806d6c036b401b57025ab006d540369e01b4b00da3806d0c034de07a6e00d358069a8034ce06a6600d31806988034be05a5e00d2e80693c0749c01a4b00d2500691c0548c01a4300d210068fc0347c01a3d064b78325ac192ce0c96302caf81256c092ae0595304ca782652c1328e0994300c9f8064ec0326e0193300c978064b403256019270649280648c030de0186b00c3380618c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c158060ab220500182700c13006097200480182300c0f80606c0302e018130273f8179f809cfa04d7b036bd0135e409aee04d76026b98135c409ace04d66026b280b1fc078f602c7701e3980b1bc058da03c6b01e3480b19c058ca03c6301e3080b17c078b602c5701e2980edfc0f6fc03b7b01dbd00eddc0d6ec03b7301db900edbc096dc03b6d025b600edac076d403b6901db400ed9c096cc03b6504db200ed8c076c403b6101db000ed7c096bc03b5b01dad00ed5c096ac03b5301da9006d3c0369c01b4d03d3f8069ec0d4ee01a73025378129b4034d601a6902533826994034c601a610252f80696c094ae01a5300d2580a9280349202a470152300690c0348202a370151b00a8d40f2fe0697b034bb81e5cc092de0496d024b581259c172ca04963024af81256c092ae0495301ca780e534052960294704ca280e50c0727e0393d01c9d80e4dc1326a0393300c978224ac1324e0192301c3f8061ec070ee0187301c3780e1b4030d60386701c3280618c070be0185b01c2b80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e018130273f81b9f809cfa04e770273a8179cc0bce404d77026bb0135d40bade05d6e02eb680b1fc078f602c7701e3980b1bc078d602c6701e3180b17c058ba03c5b01e2c80b15c058aa03c5301e2880edfc0d6fc03b7b01dbd00eddc0d6ec03b7301db900edbc0b6dc03b6b01db500ed9c096cc03b6301db100ed7c0b6bc03b5d02dae00ed6c076b403b5901dac00ed5c0b6ac03b5504daa00ed4c076a403b5101da8006d3c0369c01b4d0353f8069ec0d4ee01a7302d378069ac094ce01a6302d2f816974034b601a5902d2b826954034a601a5100d2580a9280349202a470152300690c0348202a370151b00a8d40d2fe0697b034bb81a5cc0b2de0496b024b381658c0b2be0595d02cad81655c112aa0595301ca780e5340529602947044a280e50c0727e0393d01c9d80e4dc1126a0393300c978224ac1124e0192301c3f8061ec070ee0187301c378061ac070ce0186301c2f80e174030b60385701c2a80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e018130273f8139f80bcfa04d7f026bf0135f409ade04d6e026b58135a409ac606d62026b080b1fc098fc02c7d0163e00f1ec078f202c770163a80f1cc078e403c7101e3800b1bc078d602c6701e3180b17c078b602c5701e2980edfc096fc03b7d04dbe00edec076f403b7901dbc00eddc096ec03b75025ba00edcc076e403b7101db800edbc0d6dc03b6b01db500ed9c0d6cc03b6301db100ed7c096bc03b5b01dad00ed5c096ac03b5301da9006d3c0369c01b4d0253f8269f4034f601a790253b8129d4034e601a71035378069ac0d4ce01a630252f80696c094ae01a5300d2580a9280349202a470152300690c0348202a370151b00a8d4092fe0897d024bd8125dc092ea04973034b781a5ac0d2ce06963024af81256c092ae0495301ca780e5340529602947044a280e50c0727e0393d01c9d80e4dc1126a0393300c978224ac1124e0192301c3f80e1f4030f60387701c3a8061cc070de0186b01c3380618c070be0185b01c2b80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e018130273f8139f40bcf605e7a0273b81b9d809cea04d7f026bf0135f40bade05d6e02eb680b1fc078f602c7701e3980b1bc078d602c6701e3180b17c058ba03c5b01e2d00f164078b002c5702e2b00b154058a803c5301e2880edfc0f6fc03b7b01dbd00eddc0d6ec03b7301db900edbc0b6dc03b6b01db500ed9c096cc03b6301db100ed7c0b6bc03b5d02dae00ed6c076b403b5901dac00ed5c0b6ac03b5504daa00ed4c076a403b5101da8006d3c0369c01b4d03d3f8069ec0d4ee01a7302d378069ac094ce01a6302d2f816974034b601a5902d2b826954034a601a5100d2580a9280349202a470152300690c0348202a370151b00a8d40f2fe0697b034bb81e5cc0b2de0496b024b381658c0b2be0595d02cad81655c172aa0595301ca780e534052960294704ca280e50c0727e0393d01c9d80e4dc1326a0393300c978224ac1324e0192301c3f8061ec070ee0187301c378061ac070ce0186301c2f80e174030b60385701c2a80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e01813c72b7e355af18acf8b5630163780f1ac058ce03c630162f80f16c058ae03c5301db781edb8076d603b6a01db381ad98076c603b6201daf816d78076b603b5a01dab812d58076a603b5200da7806d380369a09a6f00d3582699c034c609a5f00d2d82695c034a601a4b015250069240548e02a4600d218069040546e02a360151ad505bc192d733167064b1c3057c192b6f6157064a980e53c0729a0294b014a3826514072860393f01c9e80e4ec0726e0993501c998064bc132560992700c9180e1bc030d60386700c3180e17c030b60385700c2980e13c030960284700c2180e0fc0707a0183b01c1b80e0d4030660182f00c1580609c030460381f00c0d80e05c0302605d6f02eb70075ac03ad401d6700eb300758c03ac401c6f0263581319c098c601c5f00e2e80716c038b204c570262a80714c038a202b6f015b580ad9c056c602b5f015ae80ad6c056b202b57015aa80ad4c056a202b4f015a580ad1c0568601a6f00d3580699c034c601a5f00d2e80696c034b201a5700d2a80694c034a201a4f00d2580691c0348601a3f00d1d8068dc034660796f034b581a59c0f2c60c95f05cae82256c192ae0b955044a981253c0929604947024a180a4fc0527602937014998064bc032560192700c918061bc030d60186700c3180617c030ba0185b00c2b806154030a60184f00c2580611c030860183f00c1d8060dc030660182f00c1580609c030460181f00c0d80605c0302604e7f02f3f0139f409af606d7a026bc8135dc09aec04d73026b881359c09acc04d650163f80b1ec058ee02c730163780b1b4058d602c690163380b194058c602c610162f80b16c058ae02c5300dbf806dec036ee01b7300db7806db4036d601b6900db3806d94036c601b6100daf806d6c036ae01b5300da780ad380369a01b4700da2806d0c0368401a7f03d3f0069ec034f401a770353b0069cc034e401a6f025370069b4094d801a6b00d350069a4034d001a6702533006997124c801a6300d31006984034c001a5f0252f00696c034b401a570252b00694c034a401a47015230069140347e01a3e00d1e81e5fc0d2f60697703cb98125bc092da0496b024b3832594092c60495f024ad81255c092a60294f014a580a51c052860193f00c9e8064ec0326e0c93500c998064bc0325a0192b00c93832494032460187f00c3d8061dc030e60186f00c368061ac030ce0186500c3180617c030b60185700c2980613c030960184700c218060fc0307a0183b00c1b8060d4030660182f00c168060ac0304e0182500c1180607c030360181700c098135bc03ad604d6702eb18071bc038dc01c6b00e3501319c098cc01c6300e3101717c0b8bc01c5b00e2d00715c038ac01c5300e2900adbc056d602b67015b180ad7c056b602b57015a980ad3c0569a02b4b015a480ad1c0568a02b43015a08069bc034d601a6700d3180697c034b601a5700d2980693c0349a01a4b00d2480691c0348a01a4300d208068fc0347601a3700d1981a5bc0d2d606967034b181657c092b60495702ca982253c1129a0894b044a3822514112860293f0149d80a4dc052660192f00c9580649c032460186f00c3580619c030c60185f00c2d80615c030a60184f00c2680612c0308e0184500c218060fc030760183700c198060bc030560182700c1180607c030360181700c098139fc0dcfc04e7d0273b8139d40bce605e72026bb8135d809aea05d6f02eb70175b4058fe02c7b0163b80b1cc058de02c6b0163380b18c058be02c5d0162d80b164058ae02c550162980b144036fe01b7b00dbb806dcc036de01b6b00db3806d8c036be01b5d00dad806d64036ae01b5500da9806d440369e02b4e00da6806d1c0368a01b4300da10069fc0d4fc01a7b00d3d0069dc0d4ec01a7300d390069bc0b4dc01a6b00d3500699c094cc01a6300d3100697c0b4bc01a5d02d2e00696c034b401a5900d2c00695c0b4ac01a55c392a00694c034a401a5100d2800691c0548c01a4500d1f8068f80347a0697f034bd81a5dc0d2e60596f024b581259c0b2c60595f02cae81656c0b2ae0895502ca980a53c0529602947014a18064fc0327a0193b00c9b8224d4032660192f00c968064ac0324e0892500c918061fc030f60187700c398061bc030d60186700c3180617c030ba0185b00c2b806154030a60184f00c2580611c030860183f00c1e8060ec0306e0183500c198060bc0305a0182b00c13806094030460181f00c0d80605c0302605d6f00eb580759c03ac604c6f00e3580719c038c604c5f0262d80715c098a602b6f015b580ada4056ce02b63015b080ad7c056b602b57015a980ad3c0569602b47015a180699c214cc01a6500d2f80696c034b401a570352b00694c0349e01a4b00d2500691c0948c01a4300d1b80a8d80346a0896f044b68225ac112ce08965044b181a57c0d2b606957034a981253c0929604947024a180a4fc0527602937014998064bc032560192700c918061bc030da0186b00c33806194030c60185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660182f00c1580609c030460181f00c0d80605c0302605d6f02eb68075ac03ad201d6700eb280758c03ac204c6f026368071ac038d201c6700e3280718c038c204c5f0262d80715c098a602b6f015b680adac056d202b67015b280ad8c056c202b5f015ad80ad5c056a602b4f015a580ad1c0568601a6f00d368069ac034d201a6700d3280698c034c201a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1e8068ec0346e01a3500d198225bc112da0896b044b3822594112c60695f034ad81a55c0d2a60494f024a581251c092860293f0149d80a4dc052660192f00c9580649c032460186f00c368061ac030ce0186500c3180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc030560182700c1180607c030360181700c098139fc09cfc05e7d026bf8135f809afa04d6f026b70135ac09ad204d63036b1013584058fe02c7d0163d80b1e4058ee02c750163980b1c4058de02c6b0163380b18c058be02c5b0162b80b14c036fe04b7e00dbee14df0036f601b7900dbb806dd4036e601b7200db8806dc0036de01b6b00db3806d8c036be01b5b00dab806d4c0369e02b4e00da6806d1c0368a01b4300da10069fc094fc01a7dc213e0069ec034f401a7900d3c0069dc094ec01a750253a0069cc034e401a7100d380069bc0d4dc01a6b00d3500699c0d4cc01a6300d3100697c094bc01a5b00d2d00695c094ac01a5300d2900691c0548c01a4500d1f8068f80347a0497f044be8125ec092ee04975024b981a5bc0d2d606967034b181257c092b604957024a980a53c0529602947014a18064fc0327a0193b00c9b8224d4032660192f00c968064ac0324e0892500c918061fc030fa0187b00c3b8061d4030e60186f00c3580619c030c60185f00c2d80615c030a60184f00c2580611c030860183f00c1e8060ec0306e0183500c198060bc0305a0182b00c13806094030460181f00c0d80605c0302604d6f02eb581359c03ac604c6f00e3580719c038c605c5f00e2d80715c038a602b6f015b580ad9c056c602b5f015ad80ad5c056a602b4f015a580ad240568e02b43015a08069bc0f4dc01a6b00d3380698c034c401a5f02d2f00696c034ae01a5300d2900693c2149c01a4d00d1b80a8d80346a0796f034b581a59c0f2c60595f024ad81255c0b2a60c94f05ca682252c1528e0b945044a180a4fc0527602937014998064bc0325a0192b00c93832494032460186f00c3580619c030c60185f00c2d80615c030a60184f00c2680612c0308e0184500c218060fc030760183700c198060bc0305a0182b00c13806094030460181f00c0d80605c0302604d6f02eb581359c03ac604c6f026370071ac038d401c6700e3300718c038c405c5f02e2f00716c038b401c5700e2b00714c038a402b6f015b580ad9c056c602b5f015ad80ad5c056a602b4f015a680ad2c0569202b47015a280ad0c0568201a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d2680692c0349201a4700d2280690c0348201a3f00d1e8068ec0346e01a3500d1981e5bc0d2d60696703cb181657c092b60495702ca983253c1729a0894b064a382e514112860293f0149d80a4dc052660192f00c968064ac0324e0c92500c918061bc030d60186700c3180617c030b60185700c2980613c0309a0184b00c23806114030860183f00c1d8060dc030660182f00c168060ac0304e0182500c1180607c030360181700c098139fc09cfa05e7b02f3d0139dc0dcec04e75026bf8135f809afa05d6f02eb70175b4058fe02c7b0163b80b1cc058de02c6b0163380b18c058be02c5d0162d80b164058ae02c550162980b144036fe01b7b00dbb806dcc036de01b6b00db3806d8c036be01b5d00dad806d68036b201b5800dab816d58036ab8235400da9806d440369e02b4e00da6806d1c0368a01b4300da10069fc0f4fc01a7b00d3d0069dc0d4ec01a7300d390069bc0b4dc01a6b00d3500699c094cc01a6300d3100697c0b4bc01a5d02d2e00696c034b401a5900d2c00695c0b4ac01a55c092a00694c034a401a5100d2800691c0548c01a4500d1f8068f80347a0797f034bd81a5dc0f2e60596f024b581259c0b2c60595f02cae81656c0b2ae0c95502ca980a53c0529602947014a18064fc0327a0193b00c9b8324d4032660192f00c968064ac0324e0c92500c918061fc030f60187700c398061bc030d60186700c3180617c030ba0185b00c2b806154030a60184f00c2580611c030860183f00c1e8060ec0306e0183500c198060bc0305a0182b00c13806094030460181f00c0d80605c030278856fc32b5e0d59f00ac602c6f0163580b19c058c602c5f0162d80b15c058a601b6f00db5806d9c036c601b5f00dad806d5c036a601b4f015a7006d340368e01b4500da1806d08034de07a6e00d358069a8034ce06a6600d31806988034be05a5e00d2d806968034ae04a5600d298069480348e02a4600d228068fc0347c01a3d064b78325ac192ce0c963064af83256c192ae0c953014a780a52c0528e0294300c9f8064f403276019370649a8064cc0325e0192d00c9580649c1924a0192300c378061ac030ce0186300c2f80616c030ae0185300c2780612c0308e0184300c1f8060f4030760183700c1a8060cc0305e0182d00c1580609c0304a0182300c0f80606c0302e01813 20 1048575 8 255 11 2047 21 2097151
def cc_56_13 : Nat → List (Nat × Nat) := unpackCursorV4 0xc5f61bf768b9364b5f34ac59aa5b6aa1a419809a9542c9054f8d92c88a4f829617c86175e6a6c49a65c685f666554a24f3614926142a683c66432c9a2c26a2853d1eb9a147a40a99e07b2e02c4f0002c 0x26b78175ac09ace05d630163780f1ac058ce03c630162f80b174078b603c5a0162b813158058aa03b6f03db700edac076d403b67035b300ed8c076c402b5f015af00ad740769e03b4e01da6edc9bc134d7ac26704d3181697c094b604a5702d2980e93c0549602a4701d2180e8fc0747a03a3b00d1c80e8df8246a03a3300d18d605be8e2d73b1678f0b181657c092b60495702ca980e53c052960294701ca180e4fc0727a0393b01c9befc4d4072660992f61895ac449c132460386f01c3580e19c070c60385f01c2d80e15c070a60384f0142580a11c070860383f01c1e80e0ec0706e0383501c1980e0bc070560382701c1180e07c070360381701c0980f5bc07ada01d6b00eb480f59c07aca03d6300eb08131bc058da04c6b0263480b19c058ca04c630263081317c098b604c570262980adbc056da03b6b01db480ad9c056ca03b6301db080ad7c076b602b5701da980ad3c0769602b4701da180e9bc074da01a6b00d3481a99c0d4ca01a6300d3080e97c034b606a5700d2981293c0349604a4700d2180e8fc0347602a3700d198425bc172da0896b084b382e594112c60795f034ad81a55c0f2a60494f024a581251c092860393f0149d80a4dc072660192f0449582649c032460386f01c368061ac070ce0386500c3180e17c030b60385700c2980e13c030960384700c2180e0fc030760283700c198060bc030560182700c1180e07c030360381700c098075bc03adc01d6d026378131ac098ce04c630262f813174098b604c570262a81314c056de03b6b015b380ed8c056be03b5b01dac80ad5c076a603b51015a780ed2c0568e03b4301d3781a9ac0d4d40aa690353381a9980f4c607a6101d2f80e96c074b403a5901d2c01a95c0d4ac03a5301d2881293c0949602a4700d2180e8fc0347602a3701d1981e5bc0d2d60696703cb181e57c0f2ba0795b03cab82e5540f2a60494f024a581251c092860393f0149d80a4dc072660a92f0449582a49c112460386f00c3580e19c030c60385f01c2e80616c070ae0385500c2980e13c030960384700c2180e0fc030760283700c1980e0bc030560382700c1180e07c030360381700c098079f803cfa04d6d026b481359409ac202c6d01e3480b194078c207b7e035bd01add80f6e407b6e03db681edb00f6d414b6909db401ed98176ca0bb6403db101ed840f6c002b5a015ab00ed380768406a7a00d3c81a9d8034e206a66035328268f40347209a3500d1881e5b4112ca0495a024ab00e538072840393e01c9e80e1b4070ca0383d01c1a8079fc03cfc01e7d026bf8135ec09aee04d73026b78135b409ad604d69026b381359409ac604d610163f80f1ec058ee03c730163780b1b4078d603c690163380b194078c603c610162f813178058ba02c570162a80f14c078a403b7f03dbf00edec076f403b77035bb00edcc076e403b6f03db700edb40f6d803b6b01db500eda4076d003b6703db300ed977a6c803b6301db100ed84076c002b57015ab00ad540769e03b4e01da68069ec0d4f401a790353b81a9d8034e601a710353381a9980d4ca04a5f00d2d81295c034a603a4f00d2580a91c0348603a3f01d1e8068ec0747401a3900d1c00e8dc0746c09a35de11a0068cc034620797f034bd81a5dc0f2e60796f03cb681e5ac0f2ce0b96503cb181257c092b604957024a980e53c052960294701ca180e4fc0727a0393b01c9beec4d4072660192f0449582649c032460387f00c3d80e1dc030e60386f01c368061ac070ce0386500c3180e17c030b60385700c2980e13c030960284700c2180e0fc0707a0183b01c1b80e0d4030660182f00c1580609c030460381f00c0d80e05c0302603d6f01eb68075ac03ad203d6701eb280f58c03ac204c6f0263680b1ac058d204c670263281718c058c204c5f02e2d81315c0b8a602b6f015b680edac076d202b67015b280ed8c076c202b5f01dad80ad5c076a602b4f01da580ad1c0768603a6f01d368069ac034d206a670353280698c034c203a5f00d2d81a9680d4ae06a5600d2981693c0349604a4700d2180e8fc0347602a3700d1982a5bc152da0896b054b382e594112c60795f034ad81a55c0f2a60594f024a581251c0b2860393f0149d80a4dc072660192f0449582649c032460386f01c368061ac070ce0386500c3180e17c030b60385700c2980e13c030960384700c2180e0fc030760283700c198060bc030560182700c1180e07c030360381700c098079f803cfa04d6d02eb48135940bac202c6d01e3480b194078c207b7e035bd01add80f6e407b6e03db681edb00f6d414b6909db401ed98176ca0bb6403db101ed840f6c002b5e015a900ed380768406a7a00d3c81a9d8034e206a660353282a8f81347a0aa3c00d1c8268d41346401a3100d1801a5e80d2ec0796d03cb501e598112ca0b96402caf0165480729c0394201c9f00e4f4112540992601c3680e1940707a0383501c0e80e05403cfe01e7e00f3e8135fc0baf604d7702eb98135bc09ada05d6b02eb481359c09aca05d6302eb080b1fc078f602c7701e3980b1bc058da03c6b01e3480b19c058ca03c6301e3080b17c058ba03c5b01e2d00b15c098ac02c5501dbf81edf8076fa07b7c01dbd80ede8076ee06b7601dba81add0076e603b7201db781edb8076da07b6c01db580eda8076d203b6801db381ed98076cbb936401db180ed88076c203b60015af80ad78056ba03b4f01da700ed34034f606a7a00d3c81a9dc0d4ec01a7300d3881a99c0d4cc06a6502d2f80696c094ae01a5301d2780692c0548e01a4301d1f80e8f40347601a3901d1b8268d40346601a3103cbf81a5ec0d2ee0797303cb781e5b40f2d60796705cb281e58c0b2be0495b024ab81654c0729e0294b014a380e50c0727e0393d01c9d80e4df7026a0393300c978224ac1324e0192301c3f8061ec070ee0187301c3780e1b4030d60386701c3280618c070be0185b01c2b80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e0181300eb78075b80f8de06c6b0363381f18c1d8be04c5d07e2d8171641d8ae04c5507e298171440f6de03b6b035b380ed8c136be02b5d01dad80ed64136ae02b5501da980ed441369e03b4b04da380ed0c034d601a6700d3180695c034aa01a4f00d2580691c0348601a3f00d1d8068dc034660b85600eb78075b80dace07d6300eb101f1bc0d8d606c6703e3184717c098ba0bc5b02e2c82f15c098aa11c5302e2881edbc0d6d606b6703db1826d7c056ba0bb5b01dac826d5c056aa0bb5301da8826d3c1769609b4705da181e9bc034d606a6700d3182297c0d4ba01a5b0352b81a9541949e01a4b0652380690c1347e01a3b04d1b8068cc0f2de0796e034b381e5880f2be0795e03cae82253c1128e0893f0449b8064bc11254089270649301e1bc0d0ce1185fdb02e82e15c3a0aa8b04f3e02382e0fc1306e0182f00c138220743802a07d6f03eb701f1bc0d8d606c6703e3182f17c098ba0bc5b02e2c82f15c098aa0bc5302e2881edbc076d606b6701db1826d7c056ba03b5b01dac826d5c056aa03b5301da8826d3c0769609b4701da18069ac034ce01a6300d2b8069540349e01a4b00d2380690c0347e01a3b00d1b8068cc172ac01d6f00eb700759c03ac601d6203e3781b1ac0d8ce07c630762f8131741f8b605c590762b8131542d8a605c5103db780edac0d6ce03b6304daf80ad74076b603b5904dab80ad54076a603b5104da780ed2c1368e03b4300d378069ac034ce01a6300d2f806974034b601a5700d2a80693c0349601a4700d218068fc0347601a3700d1981e5bc0d2ce1395fda0ae83e55c3a2ab1014f074a380e4fc1326e0192f00c938061bc0f0dc0186700c3100617c0f0bc0185d00c2780611c0307e0183700c178060a80304e0182600c0d06c05803ade01d6e00eb681f1bc0d8d606c6703e3181f17c098ba07c5b02e2c81f15c098aa07c5302e2881edbc0d6d606b6703db181ed7c056ba07b5b01dac81ed5c056aa07b5301da8826d3f7469609b47db9a18069ac0d4d401a690353381a998034c601a610352b81a9580d4aba324f00d25e5491c0348609a3f00d1d8268dc034660796f034b581a59c0f2c60795f03cae81e56c0f2afb515503ca9c3c53c11296f9147044a1ba84fc1127609937044998064bc112560c92700c9181e1bc030d60686700c3181e17c0f0ba0185b03c2becc154030a68a04f00c259ec11c030866103f00c1d8260dc030660182f00c1580609c030460881f00c0d86805c0302606d6f036b581b59c0dac606c6f0363581b19c0d8c609c5f04e2d82715c138a601b6f035b7006db4036ce01b6500db1806d88036be01b5b00dab806d4c0369e01b4b00da3806d0c034ce06a6600d3280697c0b4bc01a5b00d2d00695c094ac01a5300d2900693c0749c01a4b00d2500691c0548c01a4300d210068fc0347c01a3d034b781a5ac0d2ce06963044af82256c112ae08953044a782252c1128e0894300c9f8064ec0326e0193300c978064b403256019270449280648c030de0186b00c3380618c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c1580609c0304a0182300c0f80606c0302e0181301eb780f5b803ad601d6a01eb380759807ac603d62026378131ac098ce04c630162f80b174098b604c590262b80b154098a604c51015b780edac056ce03b63015af80ad74076b603b59015ab80ad54076a603b51015a780ed2c0568e03b430353781a9b8034d603a6700d3181a9880f4be07a5d00d2d806964074ae03a5500d298069440949e01a4b0252380690c0747e01a3b0151b8068cc0d2de0696b034b381a58c112be0895d044ad82255c112aa08953024a781252c0928e0494301c9f80a4ec0526e0393300c978224ac1124e0192301c378061ac070ce0186301c2f80e174030b60385701c2a80614c0709e0184b01c2380610c0707e0183b0141b8060cc0305e0182b00c1380608c0703e0181b01c0b80604c03cfe01e7e00f3e8135fc09afc04d7d026be0135ec09af204d77026ba8135cc0dae404d7102eb80135bc09ad604d67026b180b1fc058fa03c7b01e3c80b1dc058ea03c7301e3880b1bc078d602c6701e3180b17c098bc02c5d0162b80b154078a603c5201dbf81adf8076fbb037c01dbd80ede8076f203b7801dbb81add8076ea06b7401db980edc8076e203b7001db781adb8076d603b6a01db381ad98076c603b62015ab80ad58056aa03b4f01da700ed340d4fe06a7e03d3e81a9bc0d4dc01a6b00d3480698c0d4c401a610252f80696c094ae01a5301d2780692c0548e01a4301d1f80e8f40347601a3901d1b8268d40346601a31034bf8225f40d2f606977034ba81a5cc0d2de0696b034b381a58c092be0495b024ab81254c0729e0294b014a380e50c0727e0393d01c9d80e4dc1126a0393300c978224ac1124e0192301c3f80e1f4030f60387701c3a8061cc070de0186b01c3380618c070be0185b01c2b80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e0181301eb780f5b803ad601d6a01eb380759807ac603d62026378171ac098ce05c630262f8131740b8b602c590262b813154058a602c51015b780edac056ce03b63015af80ad74076b603b59015ab80ad54076a603b51015a780ed2c0568e03b43035378069ac074ce01a6303d2f81e974034b601a5901d2b80e954034a601a5102d2780692c0948e01a4301d1f8068ec0546e01a33034b781a5ac0d2ce06963044af822574112b608957044aa82254c0b29e0494b024a381650c0727e0293b0149b80e4cc0325e0892b0449380648c070de0186b01c3380618c070be0385d00c2d80e15c070aa0185301c2780612c0708e0184301c1f8060ec0506e0183300c178060ac0304e0182301c0f80606c0702e0181300eb78075b803ada04c6f036370171ac0b8d204c6702e318171880b8c204c5f02e2d81315c0b8a602b6f01db580eda4056ce03b6301db080ad7c076b602b5701da980ad3c0769602b4701da181a9bc0d4dc03a6b01d3480e99c074c603a6201d3080e9800d4be06a5e0352d81a964074ae06a530352902a9440549e01a4b0252381690c0747e01a3b0151b80e8cc0d2de0896d034b581a59c0d2ca06963034af81a56c0d2ae0695302ca781252c0928e0594301c9f80a4ec0526e03933044978224ac1124e0892301c3780e1b4030d60386701c3280618c070be0185b01c2b80614c0709e0184b01c2380610c0707e0183b0141b8060cc0705e0182b01c1380608c0703e0181b01c0b80604c03cfe01e7e00f3e8135fc0dafc04d7d026be0175ec0baf204d77026ba8175cc0bae405d7102eb80135bc0bad604d6702eb180b1fc058fa03c7b01e3c80b1dc058ea03c7301e3880b1bc078d602c6701e3180b17c058ba03c5b01e2d00b15c098ac02c5501dbf81adf8076fbae37c01dbd80ede8076f203b7801dbb81add8076ea06b7401db980edc8076e203b7001db781adb8076da07b6c01db580eda8076ce06b6601db281ad90076c603b62015af80ad78056ba03b4f01da700ed340d4fe06a7e03d3e81a9bc0d4dc01a6b00d3480698c0d4c401a6102d2f80696c094ae01a5301d2780692c0548e01a4301d1f80e8f40347603a3a00d1c8068e00746e03a3604d1aeb48d00346601a31034bf8225f40d2f606977034ba81a5cc0d2de0696b034b381a58c0b2be0495b024ab81654c0729e0294b014a380e50c0727e0393d01c9d80e4dc1126a0393300c978224ac1124e0192301c3f80e1f4030f60387701c3a8061cc070de0186b01c3380618c070be0185b01c2b80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e0181300eb78075b803ada06c6f0263681b1ac0b8d206c670263281b18c0b8c206c5f0362d81b15c0d8a606b6f015b681adac076d206b67015b281ad8c076c206b5f035ad81ad5c0d6a609b4fd79a5826d1f5868606a6f0353701e9b40d4be06a5e00d2d806964034a606a5200d28e8893c034979424700d218268fc0347609a3700d1981a5bc112da0696b034b381a5940d2c60695f034ad81a55c0d2a60894f044a582251c112860893f0449d8224dc112660192f0449582249c032460686f06c368061ac0d0ce0686500c3181a17c030b60685700c2983613c030960d84700c218360fc030760983700c198060bc030560182700c1182207c030360881700c0981f5bc0dad606d6703eb181f1bc0d8d606c6703e3182717c138b609c5704e29806dbc036da01b6b00db5006d9c0d6cc01b6500daf806d6c036ae01b5300da7806d2c0368e01b4300d3781e9b8034da01a5f02d2f00696c034b401a570252b00694c034a401a4f01d2700692c0349401a470152300690c0348401a3f00d1f0068f40f2de0696b034b381e58c192be0895b064ab82254c1329e0894b04ca382250c0327e0193b00c9b8064cc0325e0192d00c9580649c1924a0192300c378061ac030ce0186300c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e0183300c178060b4030560182700c1280608c0303e0181b00c0b80604c0bade05d6e02eb580b5a805ace02d6602eb1817588098de05c6b0263381718c078be03c5d00e2d807164078ae03c5501e29807144056de03b6b015b380ed8c056be02b5d01dad80ed64056ae02b5501da980ed440569e03b4b015a380ed0c0d4de01a6b0353380698c074be03a5d00d2d806964094ae04a5500d298069440749e01a4b0252380690c0747e01a3b0151b8068cc0d2de0696b034b381a58c112be0895d044ad82255c112aa0895302ca781252c0928e0594301c9f80a4ec0526e0393300c978224ac1124e0192301c378061ac070ce0186301c2f80e174030b60385701c2a80614c0709e0184b01c2380610c0707e0183b0141b8060cc0305e0182b00c1380608c0703e0181b01c0b80604c09ade05d6b026b381758c0b8de05c6b02e3501719c0d8cc05c6300e2f807178038ba02b6f01db580ad9c076c602b5f01dad80ad5c076a602b4f01da580ed240568e03b4301da081a9bc0d4d602a6700d3180e97c094b604a5a0552c81295c094ac05a5302d2880e93c0749603a4a01d2480e9200948e04a4601d2180e9040747e01a3b0151b80e8cc0d2de0696b034b381a58c0b2be0495b024ab81654c0b29e0594d02ca581651c1128a0594301c9f80a4ec0526e03933044978224ac1124e0892301c378061ac070ce0186301c2f80616c070ae0185301c2780e134030960384701c2280610c0707e0183b0141b8060cc0705e0182b01c1380608c0703e0181b01c0b80604c09cfe05e7b0273b8179cc0bafe06d7e02ebd8175e80baee06d7602eb98175c803ade01d6e00eb680b1fc0d8fc02c7d0163b80b1d4078e603c720163780f1ac058ce03c630162f80b174078b603c590162b80b154078a603c51015bb80add8056ea03b6f02db700edac076d403b67025b300ed8c076c403b5f02daf00ed740b6b803b5b01dad00ed64076b003b5702dab00ed57526a803b5301da900ed44076a003b4f01da700ed340d4fe01a7b0353b8069cc034d604a6a00d3481299c094cc01a6300d3081295c094ac04a5501d2780692c0548e01a4301d1f80e8f40347603a3a00d1c8068e00746e03a3604d1aea08d00346601a31034bf81a5ec0d2ee0697302cb78125ac092ce0596302caf8165740b2b605957044aa81654c0729e0294b014a380e50c0727e0393d01c9d80e4dc1126a0393300c978224ac1124e0192301c3f8061ec070ee0187301c378061ac070ce0186301c2f80e174030b60385701c2a80614c0709e0184b0142380610c0707e0383d00c1d80e0dc0706a0183300c178060ac0304e0182301c0f80606c0702e01813016b780b5b80bad605d6a02eb38175980bac602d62026378171ac098ce05c6301e2f80f174038b601c5901e2b80f154078a601c51015b780edac056ce03b63015af80ad74076b603b59015ab80ad54076a603b51015a780ed2c0568e03b4303d378069ac0d4ce01a6301d2f80e974034b601a590252b812954034a601a5101d2780692c0949404a470252300690c0747e01a3b0151b8068cc0f2de0696b034b381e58c212be0b95d044ad84255c172aa0895302ca781252c0928e0594301c9f80a4ec0526e0393300c978224ac1324e0192301c378061ac070ce0186301c2f80e174030b60385701c2a80614c0709e0184b01c2380610c0707e0183b0141b8060cc0305e0182b00c1380608c0703e0181b01c0b80604c0fafc05d7a036bb0175c803adc01d6d0162e80f164058aa03c51015bf00adc80b6dc04b6a025b3016d880b6bc05b5d02dae016d68296b214b5802dab02ed54176a805b5202da8816d400769c03b42025350069a4094cc01a610252b0129541347a01a3904d1a8068c40f2fc07972024b50125980b2ba0595a02cab022554172a80394e01ca100e4f80727a0892a04c9300e174070aa0383d01c1a80e0740702a04e7f02f3d8139dc0bce605d7f03ebf0175ec0baf405d77036bb0175cc0bae401d6f00eb70075b4058fe02c7d01e3d80f1e8058ee06c760163a80b1bc078d602c6701e3180b17c058ba03c5b01e2c80b15c058aa03c5301e2880adfc056fc02b7d01db7816db8076da05b6c01db580eda8076ce04b6601db2812d90076c603b6201daf816d78076ba05b5c01dad80ed68076b203b5801dab816d58076aba635401da980ed48076a203b5001da780ed380769a07a7f00d3d81a9dc034e601a6b025350069a4094ce04a6600d31806984094ae04a560252a80e93c0349602a4700d2180e8fc0747a01a3b00d1c80e8dc1346a01a3300d1881e5fc0d2f60697703cb98165bc092d60496702cb181657c0b2ba0595b02cab82e5540b2a60394f014a580a51c072860393f01c9e80e4ec0726fa513501c998064bc112560992700c9180e1fc030f60387700c3980e1bc030d60386700c3180e17c070ba0185b01c2b80e154030a60384f00c2580a11c030860383f01c1e8060ec0706e0383500c198060bc030560182700c1180e07c030360381700c098079fc03cfc01e7d026bf8175ec09aee05d73026b78135b40bad605d6a02eb48175a009ace07d66026b28135900bac605d6102e3f81f1f80b8fa07c7c02e3d8171e80b8ee06c7602e3a81b1d00b8e605c72026378131b8098da04c6c02e358171a80b8d205c6802e3381b198098ca04c6402e318171880b8c205c6000e2f807178038ba07b7f035bd81addc0f6e607b6f015b681edac076d207b67015b281ed8c076c205b5f025ad812d5c0b6a605b4f015a6816d2c0769205b47015a2816d0c0768201a7b00d3d0069e4034ee06a7600d398069c4034ce06a6600d3280696c034b401a5900d2b812958034a601a5100d238129180348a01a3f00d1d8068e80346e09a3600d1981e5fc0d2f60697703cb981e5bc0f2da0796b03cb38325940f2c60595f024ad81255c0b2a60594f02ca681652c0b28e0c94502ca18264fc1127609937044998064bc032560892900c9380648c032420187f00c3d8061dc030e60186f00c368061ac030ce0186500c3180617c030b60185700c2980613c0309a0184b00c23806114030860183f00c1d8060dc030660182f00c158060a40304e0182300c1080607c030360181700c098079fc03cfc01e7d026bf81b5f809afa04d7c02ebd8175e409aee04d7502eb98175c80bae205d70026b78175ac09ace05d6302e3f81b1f8098fa04c7c02e3d8171e80b8f205c780263b8131d8098ea04c7402e398171c80b8e205c7002e3781b1b80b8da07c6c02e358171a80b8ce06c6602e3281b1900b8c605c6200e2f807178038ba06b7f015be81adec076f206b77015ba81adcc076e206b6f035b581ad9c0d6c605b5f025ad812d5c0b6a605b4f015a6816d2c0769205b47015a2816d0c0768201a7f0353f0069f4034de06a6e00d358069a4034c601a6200d3080696c034b401a5900d2b812958034a601a5100d238129180348a01a3f00d1d8068dc034660697f044be81a5ec0d2ee06975034b981a5bc0d2d606967034b181657c092b60495702ca981653c0b29a0594b02ca38225140b2860893f0449d8224dc112660192f00c9580649c032460187f00c3e8061ec030ee0187500c398061bc030d60186700c3180617c030b60185700c2980613c0309a0184b00c23806114030860183f00c1d8060dc030660182f00c1580609c030460181f00c0d80605c0302604d6f02eb581359c0bac60fc6f03e370231ac0d8d408c670363303f18c0f8c401c5f00e2f026dbc076d608b6701db1816d7c076b604b5701da9826d3c0569a03b4b01da4826d1c0568a03b4301da08069bc034d601a6700d3180696c034ae01a5300d238069140347e01a3b00d1b8068cc1f0dc0485605c230135bc0bad604d6702eb182f1bc0f8dc08c6b0363502319c0d8cc11c6303e3100717c038bc04c5702e29807148136de08b6b045b382ed8c0b6be04b5b025ab816d4c1369e02b4d05da580ed241368e02b4505da180ed04194de01a6b0453380698c0b4be01a5b0252b80694c1949e04a4d00d2581291c0948a09a3f00d1d8268dc034660896f044b381657c0b2bc0495702ca901653c0b29c0594d05c9f8264dc0325e0c92a05c938324994e0de0886702c2f81215c2309fa104d05c238641141707e0983700c1780609c1903a18015026b78175ac09ace05d6305e3781f1b8118d606c6a0463381b198178c607c6202e2f817178136de03b6b045b380ed8c0b6be03b5b025ab80ed4c1369e02b4d01da580ed241368e02b4501da180ed04034de01a6b00d3380698c034b601a5700d2980691c0348a01a3f00d1d8068dc034660b946 20 1048575 8 255 11 2047 21 2097151
def cc_56_14 : Nat → List (Nat × Nat) := unpackCursorV4 0xa06593674e54b0c922e8d59f152b216a7bfce178cdae5785b2b0b3e4e60fdab911d5d69a8a614e858937351bd620e533bbc26d348bf3695ac72689a40f846e278abe11099c139b414e480053 0x9ade05d6b026b381f1bc0f8dc05c5f02e2f01edbc076d606b6701db1816d7c076b604b5701da982ed3c0569a03b4b01da482ed1c0568a03b4301da081e9bc034d606a6700d3181697c034b604a5700d2982e93c1549a01a4b00d2482e91c1548a01a4300d2080e8fc034760ba3700d1982e51809ade05d6b026b381758c098de04c6e0363381f18c098c405c5f02e2f01315c0b8a605c5203db780edac0d6ce03b6302daf80ed6c096ae03b53095a780ad340769603b4907da380ad140768603b4103d378069ac0d4ce01a6302d2f80696c094ae01a5307d27f7c9340349601a4907d238f89140348601a4101d1f8068eee646e01a3303cb781a59c0b2be04957094a7f785341f28e2814501c9fb5c4dc0325e1d92703c3781e1b80d0ce0786202c2f816178090ae0585202c278161380b09a0383f06c1d00e0dc9606c0182f06c1500609c7604c0d81a1300b0135bc09ada05d6b02eb501359c0dacc04d65026378131b8098da05c5f02e2f0171740f6de06b6b035b381ed8c0b6be04b5b025ab816d4c0b69e02b4d02da580ed240b68e02b4502da180ed040f4de06a6b0353381e98c0b4be04a5b0252b81694c0b49e05a4d02d258069240b48fe324502d218069071647f8023bb911bd808cc0f2de0696b034b381e58c0b2be0495b024ab81654c0b29e0594d02ca581651fc028a059437609f8224edac26e08933648978224ad7824e0892303c3781a1ac0d0ce0786302c2f81216c090ae0585302c278161340b09605847ee82281610cc607e0d83b2501b8360cc8205e0d82b1d01383608c1103e0d81b1280b82204c07ade03d6e03e3781b1ac0d8ce07c630762f8131741f8b605c590762b8131541f8a605c51015b580ad9c056c602b57015aa80ad3c0569602b47015a181e9bc034d606a6700d3182697c134ba01a5b00d2c82695c134aa01a5300d2882693c0349609a4700d2180a8fc0347602a3700d1982e1580507c0982601eb780f5b80dace07d6301eb101f1bc0d8d606c6703e3188317c098ba0bc5b02e2c82f15c098aa20c5302e2880adbc056d602b67015b180ad7c056ba02b5b015ab80ad540569e02b4b015a380ad0c0f4de06a6b0353381e98c134be09a5d04d2d806964134ae09a5504d298069441349e09a4b04d2382690c0547e02a3b0151b80a8cc0f2de0796e034b381e588052be0295e014ae82253c1128e0293f0149d00a4dc0526c0892f0449381e1bc0d0ce1585fed82e82e15c480aa8d04f3f82380a0fc0506e0982f04c138220744602a07d6f03eb701f1bc0d8d606c6703e3182f17c098ba0bc5b02e2c82f15c098aa0bc5302e2880adac056ce02b63015ab80ad540569e02b4b015a380ad0c0f4de01a6b0353380698c134be09a5d00d2d806964134ae09a5500d298069441349e01a4b04d2380690c0547e01a3b0151b8068cc172ac03d6f01eb700f59c07ac603d6203e3781b1ac0d8ce07c630762f8131741f8b605c590762b8131543d8a605c51015b780adac056ce02b63015af80ad74056b602b57015aa80ad3c0569602b47015a181e9bc034d606a6700d3182697c134ba01a5b00d2c82695c134aa01a5300d2882693c0349609a4700d2180a8fc0347602a3700d1981e5bc0d2ce1495fec8ae83e55c482ab1514f074a380a4fc0526e0192f04c9380e1bc0f0dc0386701c3100a17c050bc0285d01c2780e11c0507e0283a0141b80a0d80305e0182701c0d08805805ade03d6e016b681f1bc0d8d606c6703e3180b17c058ba02c5b02e2c80b15c098aa02c530162880adac0d6d402b69015b380ad98056c602b61015ab80ad58056aa02b4f015a580ad1c0568607a6f0353581a99c0f4c602a5f0152e80a96c034b202a5704d2a80a94c034a209a4f04d2582691c1348602a3f0151d80a8dc054660796f034b581a59c0f2c60295f014ae80a56c052afda155014a9c5053c11296ff147044a180a4fc0527602937014998264bc11256099270449181e1bc070d60686701c3180a17c050ba0285b0142bf60154050a68c04f01c259f811c070860283f0141d80a0dc050660982f01c1582609c070460881f01c0d88405c0702606d6f036b581b59c0dac602c6f01e3580b19c078c602c5f01e2d80b15c078a606b6f00db701adac056d402b67015b3006d8c036c40ab5f02daf02ad6c096b40ab57025ab02ad4c0b6a403b4f01da7006d2c0369402b4700da300ed0c0768406a6f00d3581a9a80d4ce06a6600d3182697f504bc01a5b04d2b80694c134a403a4f01d2700692c0548e01a4301d2100e8fc0747c03a3d034b781a5ac0d2ce06963044af82256c112ae0895301ca780a52c0528e039430449f8224f411276089370449a8224cc0325e0892d0449582249c1124a0192301c378061ac070ce0186301c2f80616c070ae0185301c2780612c0508e0184301c1f80e0f4030760383701c1a8060cc0305e0382d00c1580609c0704a0182301c0f80606c0702e01813036b781b5ac0dace06d630163781b1b8058da02c670163280f18c078c402c5f01e2d80b15c078a602b67015b300ad94076be05b5e01dad80ed68076ae04b5601da980ed480769e03b4e01da681a9bc0d4d606a6703531e9c97c134b79a25704d2980e93c0549602a4701d2180e8fc0747a03a3b00d1c80e8dfac46a03a3300d1881a5bc0d2d606967034b182257c112b608957044a980e53c052960294701ca180e4fc0727a0393b01c9b8224d4072660892f0449582249c112460386f01c3580e19c070c60385f01c2d80e15c070a60384f0142580a11c070860383f01c1e80e0ec0706e0383501c1980e0bc070560382701c1180e07c070360381701c0980b5bc05adc03d6d016378131b4058d602c690163380b194058c605c610362f81b16c0d8ae06c53015b780adb8056da02b5f015af00ad6c056b202b53035a900ad440569e02b4b015a380ad0c054de09a6d015358069a4054ce02a65015318069840d4be06a5b0352b81a94c1349e09a4b04d2382690c0547e02a3b0151b80a8cc052de0896d014b580a59c052ca02963034af81a56c0d2ae06953044a782252c1128e089430149f80a4ec0526e02933044978224ac1124e08923014378361b4050d6028670143280a18c0d0be0385b0342b80e14c1b09e0384b06c2380e10c0507e0283b0141b80a0cc1305e0382b04c1380e08c1103e0381b0440b80e04c0fade06d6b036b381f58c058de03c6b0163380f18c058be03c5b0162b80f14c0f6de07b6e00db5806da80d6ce01b6603db181ed88156be05b5e05dad812d68176ae04b56055a9816d480769e03b4e00da5806d280568e01b4601da180ed080f4de01a6b0353380698c134be01a5b04d2b80694c0749e01a4b0152380690c0747e03a3d01d1b80e8d4034660796f034b382257c112ae0394f014a38224dc1526c0893500c978224a81124e0992601c3780e19c070be0385701c2780a11c0707e0383d01c1b80e0d40305e0182703eb781b5ac0dace07d630163780f1ac058ce03c630162f80f16c058ae03c53015b780adb8036d601b6a035b3806d980f6c602b62055af816d78156b604b5a055ab812d58156a605b5201da780ed380369601b4a015a3806d180768603b4203d3781e9b8034d606a6700d3181e988134be01a5b04d2d02695f304ac01a5301d2780e9380349602a4700d2180e9080747e03a3e01d1e81e5bc0d2d60696703cb182a57c112b6fd157044a980e53c052960294701ca18464ffa627a0893b0549baec4d4112660192f04c968224ac1324eba12500c9180e1bc030d60386700c3180e17c030b60385700c2980e13c030960284700c2180e0fc0707a0183b01c1b80e0d4030660182f01c168060ac0304e0382500c1180e07c030360381700c0981f5bc0dad606d6703eb180b1bc078d602c6701e3180b17c078b602c5701e2981edbc0f6dc06b6703db181ed88156be05b5e055ad812d68156ae04b56055a9816d480769e03b4e015a380ed0c0768407a6f00d3581a99c034c609a5f00d2d82695c034a603a4f00d2580a91c0348609a370551b0268d40f2de06967044af82255c0729e0294701c9f80e4f40726e0393500c978224b41124e0892501c3780e19c070be0385701c2780a11c0707e0383d01c1b80e0d40305e0182703eb781b5ac0dace07d630163780f1ac058ce03c630162f80f16c058ae03c53015b780adb80d6ce07b63015b102ed7c0b6bc14b5b025ad02ed5c096ac14b5302da900ed3c0769c02b4701da180ed080f4de06a6b0353381e98f4a4be09a5bcb92b82694c0749e02a4b0152380e90c2947fd123d04d1d8068e41746ebb23504d198068c40f2de0796e034b381e588112be0895a044abbf05580729e0394e014a380e5080727e0393e01c9e8224bc11254089275c89300e1bc070ce0385f01c2b80e13c0508e0383f01c1e80e0dc0706a0382f01c1380e0740702a07d6f036b581b59c0fac602c6f0163680f1ac078d402c670363300b194058be03c5b0162b80f14c056de02b6e015b680ed7c0b6bc03b5b01dad00ed5c096ac03b5301da900ed3c0769c03b4d03d3781a9ac0d4ce07a63d212f82696f2c4ae09a5301d2780a92c0548e03a4301d1f80e8f40747601a3901d1bf488d40746601a3103cb781a5ac0d2ce07963890af82256df62ae0895301ca780a52c0528e0394301c9f80e4f40727603937e809a80e4cc1325e0892b5c09382248c070de0386b01c3380e18c070be0385b01c2b80e14c0709e0284b0142380e10c0707e0383d01c1d80e0dc0706a0383301c1780e0ac0704e0382301c0f80e06c0702e03813026b78175ac09ace05d6307e3781f1b8118d606c6a0463381b1981f8c607c6201e2f80f178056de02b6b015b380ad8c056b602b57015a980ad1c0568a09a6f00d3582299c034c605a5f00d2d81295c034a609a4f04d2680692c0349209a4704d2280690c0348202a3f00d1d80a8dc034660b846026b78175ac09ace05d6305e3781f1b8118d606c6a0463381b198338c607c6201e2f80f178098ae05c5301e2900adbc056d602b67015b180ad7c056b602b57015a980ad3c0569a02b4b015a380ad14134de08a6b0453382698c0b4be04a5b0252b81694c1349e09a4d04d258069241348e09a4504d218069040547e02a3b0151b80a8cc112de0896702caf816578092ae05952014a780a5380529a0293f0149d00a4dc0526c0992f04c93aa81bc110ce0585f0242b85613f9c09a0b8471002280a0fc0506e0982f04c138135bc0bad604d6702eb182f1bc0f8dc08c6b0363502319c0d8cc0bc6303e3101717c0b8bc02b6f015b580ad9c056c602b5b015ab80ad4c0568e02b4504d378069ac114ce01a6302d2f80696c094ae01a5304d278269340349601a4904d238269140348601a410151f8068ec0546e01a3305ca30135bc0bad604d6702eb183f1bc0f8dc0dc6b0363503719c0d8cc12c6303e3100f17c078bc03c5701e2980f148056de02b6b015b380ad8c056be02b5b015ab80ad4c0569e02b4d015a580ad1c0568a09a6f00d3582699c034c605a5f00d2d81295c034a609a4f04d2680692c0349209a4704d2280690c0348202a3f00d1d80a8dc034675e16f06cb381657c092ae1294fe60a683e51c4028a0293f0149b8064bc1324e0386f5483700e19c070c40385f02c2f00e15c070a40284f0142700a1340507e0283a0141b80a0d80305e0382a00c13826098070341f016026b78175ac09ace05d630163781f1b8058d602c6a0163381b198058c602c620162f80f178058ba02b6f015b580ad9c056c602b5b025ad00ad64056ae02b56015a980ad440568e02b46015a28269bc134d609a6704d3181697c094b604a5702d2980a93c0549a02a4b00d2480a91c1348a02a4300d2080a8fc0547602a3701519d745be9c2d744167920b181657c092b60495702ca980a53c0529a0294b014a3f34514052860293f0149d80a4dc052660992f04c9582649c13246a806f01c35a6019c070c60585f01c2d81215c070a60284f0142680a12c0508fcb0450142180a0fc0507602837014198260bc070560982701c118ac07c070361e01701c098135bc09ad604d67026b180b1bc078d602c6701e3180b17c078b602c5701e2982edbc0f6dc08b6b035b5022d9c0d6cc0bb6303db1012d7c036bc04b5b025ad012d5c096ac01b5300da900ed3c0769c01b4b00da500ad1c0368c03b4301da10269bc034d608a6700d3181297c034b604a5700d2980e93c0349602a4700d2180e8fc0747a03a3701d1a8068cc112de08967024af812578092ae0495201ca780a51c1526e0a9360549a8064bc132540992704c9300e1bc070ce0385f01c2b80e13c0508e0383f01c1e80e0dc0706a0182f00c1380e0740702a04d6f026b581359c09ac602c6f01e3580b19c078c602c5f01e2d80b15c078a60ab6f03db705edac0d6d40ab67035b305ed8c0f6c404b5f00daf012d6c056b402b57015ab006d4c036a403b4f01da7006d2c0369402b4700da300ed0c0768409a6fde1370069ac134ce01a6304d3101297c034b604a5a0252b812958034a603a4f01d2700692c0548e01a4301d2100e8fc0747c03a3dae0b78325ae842ce0c963024af81256c092ae0495301ca780a52c0528e0394308c9ff244f4152760a9375b89a8324cc0325e0992d04c9582649d6c24a0192301c378061ac070ce0186301c2f80616c070ae0185301c2780612c0508e0184301c1f80e0f4030760383701c1a8060cc0305e0382d00c1580609c0704a0182301c0f80606c0702e01813026b78135ac09ace04d630163780f1ac058ce03c630162f80f16c058ae03c53055b781edb8116d606b6a045b381ad98156c607b62025af812d6c096b404b57025ab00ed3c0769c02b4701da180ed08134de01a6b0453380698c094be01a5b0252b80694c0749e01a4b0152380690c1346e0aa3604d1a8225bc112ce0495f024ab80e53c0528e0393f01c9e80e4dc0726a0192f04c9682649c1524a0386f01c3380e17c070ae0384f0142380e0fc0707a0383701c1a8060bc0304e04d6f026b581359c09ac602c6f01e3580b19c078c602c5f01e2d80b15c078a60bb6f03db7022dac0d6d408b67035b3052d8c0f6c404b5f025ad80ad68056ae02b5601da780ed380568e03b4301da16ec9bc114d608a6704d3181297c094b604a570252980e93c0549602a4701d218528ff8e47a09a3b00d1c82e8dd6e46a09a3300d188225bc112ce0495f024ad01255c092ac0394f01ca700a51c072840393f01c9f00e4f41325e0b92701c3780e19c070be0385701c2780a11c0707e0383d01c1b80e0d40705e03827026b78135ac09ace04d630163780f1ac058ce03c630162f813178058ba02c570162a80f14c078a403b6f03db700edac076d403b67035b300ed8c076c402b57015ab00ad540769e03b4e01da6ee89bc134d7af26704d3181297c094b604a570252980e93c0549602a4701d2180e8fc0747a03a3b00d1c80e8df9046a03a3300d18d6c5be982d741167910b181257c092b604957024a980e53c052960294701ca180e4fc0727a0393b01c9bf184d4072660992f63095ad449c132460386f01c3580e19c070c60385f01c2d80e15c070a60384f0142580a11c070860383f01c1e80e0ec0706e0383501c1980e0bc070560382701c1180e07c070360381701c0985f5bc0fadc08d6b036b502359c0dacc0bd6303eb10131bc098d604c670263180f17c078ba04c5701e2a81314c056de02b6b015b380ad8c056be02b5d015ab80ad54056a602b4f015a580ad1c0568609a6f0453582299c134c609a5f04d2e82696c034b209a5704d2a82694c034a204a4f0252581291c0948602a3f0151d80a8dc054660896f044b380a55c052ac02955024a78125280928e049460149f80a4e80526e0293604c978264b81324e099220743782219c170be0e85d0742b83a1540909e048470141f80a0dc1305e09827016b780b5b805ad606d6a016b380b59805ac607d62026378131ac098ce04c630162f80b178078ba02b6f015b580ad9c056c602b5f015af00ad740569e02b4e015a580ad240568604b42015a08269bc134d609a6704d3180a97c134ba02a5b00d2c80a95c054aa02a5300d2881293c0949604a470252180a8fc0547602a3701519d685be942d73f167900b180a57f882ba0295b014ab80a554052a60494f024a581251c092860293f0149d80a4dc052660992f04c9582649c132460e86f01c3583a19c070c60285f0742e80a16c050ae028550142981213c070960484701c2180a0fc0507602837014198260bc070560982701c1183a07c070360e81701c098135bc0bad604d6702eb180b1bc078d602c6701e3180b17c078b602c5701e2982edbc0f6dc08b6b035b5022d9c0d6cc0bb6303db1016d7c0b6bc01b5b00dad012d5c036ac05b5302da900ed3c0769c01b4b00da500ad1c0368c03b4301da10269bc034d608a6700d3181697c034b604a5700d2980e93c0349602a4700d2180e8fc0747a03a3701d1a8068cc112de0896702caf81255c0729e029470549b82a4d81526a0192f04c9502649c1324c0386f01c3380e17c070ae0384f0142380e0fc0707a0383701c1a8060bc0304e04d6f02eb581359c0bac602c6f01e3580b19c078c602c5f01e2d80b15c078a60ab6f03db706adac0d6d40ab67035b306ad8c0f6c402b5f015af006d6c036b404b5700dab016d4c056a403b4f01da7006d2c0369402b4700da300ed0c0768409a6f00d358269a8134cfad26600d3181697c0b4bc01a5b0252b80694c0b4a403a4f01d2700692c0548e01a4301d2100e8fc0747c03a3dac8b78325ae7a2ce0c96302caf81256c092ae0595301ca780a52c0528e0394308c9ff084f4152760a9375a09a8324cc0325e0992d04c9582649d6624a0192301c378061ac070ce0186301c2f80616c070ae0185301c2780612c0508e0184301c1f80e0f4030760383701c1a8060cc0305e0382d00c1580609c0704a0182301c0f80606c0702e01813026b78175ac09ace05d630163780f1ac058ce03c630162f80f16c058ae03c53055b781edb8116d606b6a045b381ad98156c607b6202daf816d78096ae05b5302da900ed3c0769c02b4701da180ed08134de0aa6e00d3582299c034c609a6202d2f80696c094ae01a5301d2780692c0548e01a4304d1b82a8d81346a0896f044b381657c092ae0394f014a380e4fc0727a0393701c9a8064bc1325a099270549280e1bc070ce0385f01c2b80e13c0508e0383f01c1e80e0dc0706a0182f00c138135bc0bad604d6702eb180b1bc078d602c6701e3180b17c078b602c5701e2982edbc0f6dc08b6b035b5022d9c0d6cc14b6303db100ad7c056bc04b5702da980ad480769e03b4e015a380ed0c07685b826f0453582299c134c605a5f0252d81295c0b4a603a4f0152580a91c0748614a3fe011e8268ec034720ba375a11a8268cc034620896fa48b502259e782cc0595f02caf01255c0b2a40394f01ca700a51c072840393f01c9f00e4f41325ec512a05c93ac8498070de0386701c2f80e15c0709e0284701c1f80e0f40706e0383501c1780e09c0703a03815 19 524287 7 127 11 2047 21 2097151
def cc_56_15 : Nat → List (Nat × Nat) := unpackCursorV4 0xa2d3a57e78c92e0acf76985a6e75d9853fed43d84e6522f54886ed18d1c4d2c08f4c0047 0x3eb781f5b803ad601d6a036b38075980fac607d62026378131ac098ce04c630262f813174098b601c590262b813154038a601c5103db781adac0d6ce07b6304daf80ad74176b603b5904dab80ad54176a603b51025a7812d2c0968e04b4303d378069ac0d4ce01a630252f812974094ae04a5500d2981293c0349604a4700d218268fc0347609a3700d1981e5bc0d2ce08957054ab0225540929e049470449f8224dc0325e0892a0449382a4980f0de0686705c2f82e174170ae0e8550242781211c1707e0983700c1780609c0bade05d6e00eb58075a80dace01d6603eb1817588098de04c6b0263381318c098be04c5d0262d807164098ae04c5500e298071440f6de06b6b035b381ed8c136be02b5d055ad80ed64136ae02b55085a980ed440969e04b4b025a3812d0c0f4de07a6e00d3581a99c034c607a620252f812978094ba04a4f00d258129280948e04a4600d218268fc0347609a3700d1981e5bc0d2d60696703cb184657fdc2ba0895b054abb04554112a60494f024a581251c092861093f0449d8264dc112660192f0449582a49c032460786f00c3581a19c030c60e85f0742e80616c150ae0e85500c2981213c030960484700c2183a0fc030760983700c198060bc030560182700c1182207c030360e81700c0981f5bc0fadc06d6703eb181f588098de04c6b0263381318c098be04c5d0262d81315c098aa07b6f035b581ad9c0f6c609b5f015ae82ad6c076b209b57015aa82ad4c076a204b4f025a5812d1c0968607a6f00d3581a99c034c60aa570552b02a9540949e04a4e00d2581291c0348604a4204d1f8068ec1346e01a3303cb781a59c092be0495d024ab8125540929e049470449f8224dc0325e0892d044938224940f0de068670542f82a174150ae0e8550242781211c1707e0983700c178320b40304e0a82502eb78175b80dace07d6302eb10131bc098d604c670263181317c098ba04c5b0262b8131540f6de06b6b035b381ed8c176be02b5d05dad80ed64176ae02b5505da980ed440969e04b4b025a3812d0c0f4de06a6b0353381e98c2f4bfec25d05d2d806964174aec1255065298069440949e04a4b0252381290c1747e0ca3bbe91b82e8cc0f2de0796e034b381e588092be0495e024ae81253c0929404947024a30224fc1126e0892f0449381e1bc0d0ce0e85f0742e82e15c1d0aa0484f0242382e0fc1d06e0c82f074138220741d02a04d6f02eb70135b4098d606c6a0263481319c098cc04c630263081315c098ac04c5503db781adac0d6ce07b63025af80ad74096b603b59025ab80ad54096a603b51025a7812d2c0968e04b4303d3781a9ac0d4ce07a630252f812974094b601a590252bfb4954094a601a510252781292c0948e04a43c711fe208eef846f6623303cb781a5ac0d2ce07963024af812574092b604957f58aa81254c0929e0494b024a381250ddc27e0893b6d09b8224cd9825e0892b6009382248c0f0de0686b0343381e18c090be0485d0242d81215c1d0aa048530242781212c0908e048430741f8360ec1d06e0d833074178360ac1d04e0d8230440f83606c1d02e08813026b78175ac09ace05d63036378071b80d8d604c6a02633813198038c601c6202e2f817178038b601c5a0262b8071580b8a605c52035b781adac0d6ce06b6302daf812d6c096ae05b5304da780ad341569603b4904da380ad142168603b41035378069ac0d4d406a670353300698c0b4be05a5e00d2d81295c034a605a5202d278169380b49a09a3f00d1d8268dc034660696f034b581a59c0d2c60595f024ad81255c0b2a60894f044a682252c1128e08945044a18224fc1127608937044998064bc112560892700c9181a1bc030d60686700c3181617c030b60485700c2983613c1b09a0184b05423836114030860d83f00c1d8260dc030660182f00c1580609c030460881f00c0d82205c0302604d6f036b70135b409ace04d6502eb1817588098ce04c660263281717c0b8bc05c5d035b781adac0d6ce06b6302daf812d6c096ae05b5302da780ad340b69603b4902da380ad140b68603b410353781a9ac0d4ce06a6302d2f81296c094ae05a5302d278169340b49601a4902d23fa49140b48601a41c691fe188eef446f64233034b781a5ac0d2ce0696302caf81256c092ae0595302ca78165340b29605947044a281650c1127e0893b0449b8224cc1125e0892b0449382248c0d0de0686b0343381a18c0b0be0485b0242b81614c0b09e0584d02c2581611c1b08a0584306c1f8360ec1b06e0d83306c178360ac1b04e0d8230440f82206c1102e0881302eb78175b403ad601d69036b38175940dac601d61026378131b4038d601c6902633813194098c601c610262f81316c098ae04c5304db780adb4216d603b6904db380ad94156c603b61035af81ad6c0d6ae06b53025a7812d2c0968e04b4302533812998094ca06a5f00d2d81a9680d4ae06a5600d2981293c0349604a4a025238129180348609a3f00d1de148e81346f7823600d198225bc112da0896b044b3822594112c60695f034ad81a55c0d2a60494f024a581251c092860893f0449d8224dc112660192f044958224a41124e019230449082a1bc1b0da0186b06c33836194030c60685f00c2d81a15c030a60484f00c2581211c030860d83f00c1d8260dc030660182f00c158360a40304e0182306c1082207c030360881700c098135bc09adc05d6d026378131b8098da04c5f0262f01316c098b204c5303629013144096de02b6d025b580eda4096ce02b65025b180ed840d6be06b5b035ab81ad4c0969e04b4b025a3812d0c094dfe726d025358069a4094ce04a65025318069840d4be06a5b0352b81a94c0949e04a4b0252381290f1847f8323bbb91bd888cc092de0896d024b581259c092ca04963034af81a56c0d2ae06953024a781252c0928e049430449f8224ec1126e08933044978224ac1124e08923024378361b4090d6048670243281218c0d0be0685b0342b81a14c0909e0484b0242381210c1b07e0d83b06c1b8360cc1b05e0d82b06c1383608c1103e0881b0440b82204c09ade05d6b026b381758c0f8de07c6e00e358071a80d8ce01c6603e3181f1880b8be05c5e00e2d807168098ae01c5602e298171480f6de06b6b035b381ed8c0b6be04b5b025ab816d4c1369e02b4d05da580ed241368e02b4505da180ed040f4de01a6b0353380698c0b4be01a5b0252b80694c0b49e05a4d02d238169140348609a3f00d1d82e8e81346e0ba3600d1981e5bc0d2ce0595f024ab82251c1528c089450449f82e4f81126e0893200c978224a81124e0a92603c3781a19c0b0be0485705c2782e1341708e0f84505c1f8260dc0305e01827026b78175ac09ace01d6303e3781f1b8038d601c6a00e33807198038c601c6202e2f817178038b601c5a00e2b807158038a601c5203db780edac0d6ce03b6302daf80ed6c096ae03b5304da780ad340769603b4904da380ad140768603b4100d378069ac034ce01a6300d2f80696c034ae01a5300d278069340348e01a4500d218068fc0347601a3a00d1b85a8d8034660796f034b381657c092ae0f94f05ca683e51c1728a0393f04c9b8064bc0324e0186f00c3380617c030ae01847054230061140307e0f83e00c1b8060c80305e0182a00c1380609809ade05d6b026b381758c098de04c6e00e358071a80d8ce01c6603e318131880b8be05c5e00e2d807168098ae01c5602e298171480f6de06b6b035b381ed8c0b6be04b5b025ab816d4c1369e02b4d055a580ed241368e02b45085a180ed040f4de07a6e00d3581a99c034c607a6202d2f816978034b604a5700d298169480b49e05a4e02d268268fc034778223a04d1bdd48d8034660796f034b581a59c0f2c60595f024ad81255c0b2a61194ff28a682252c1528ebf145044a18424fc1127609937044998064bd9625a0892b05493af8494032460786f00c3581a19c030c60585f00c2d81215c030a61684ff202680612c1508e3e04500c218420fc030760983700c198060bc8605a0182b00c138f4094030460881f00c0d85a05c0302604d6f02eb581359c0bac607c6f03e3701b19c0f8c607c6202e2f817178098ae05c5302e2901edbc0d6d606b6703db1816d7c096b604b5702da9826d3c0569a0ab4b01da4826d1c0568a0ab4301da081e9bc034d606a6700d3181697c034b604a5700d2982a91c1548c0aa4504d1f8068ec1346e01a3303cb781a59c0b2be0495702ca78165340b28e059450449f8224dc0325e0892d044938224940f0de0686702c2f81215c1509e0a84d0542383e1141707e0983700c1780609c09ade05d6b026b381f1bc0f8dc05c5f02e2f01edbc076d606b6701db1816d7c076b604b5701da983ed3c0569a03b4b01da483ed1c0568a03b4301da081e9bc034d606a6700d3181697c034b604a5700d2983e93c1549a01a4b00d2483e91c1548a01a4300d2080e8fc034760fa3700d1982e11809ade05d6b026b381758c098de04c6e0363381f18c098c405c5f02e2f01315c0b8a605c5203db781adac0d6ce07b6302daf812d6c096ae05b5305da780ad341769603b4905da380ad141768603b4103d3781a9ac0d4ce07a6302d2f81296c094ae05a530cd27f889341749601a4905d23afc9141948601a4105d1f8328eee846e0ba3303cb781e5b80d2ce0796202caf816578092ae0595202ca78165380b29a0893f0449d0224ddb026c0892f0449502249d7a24c0786f0343381617c090ae1584ff082682e11c5008a0b83f2601b8320bc7804e0881d1380a8135bc0bad604d6700eb181f1bc0f8dc01c6700e318071880b8be05c5e00e2b80714c038a407b6f01db581ad9c076c605b5f01dad812d5c076a609b4f015a680ed2c0769209b47015a280ed0c0768201a6f00d3580699c034c601a5f00d2d80695c034a601a47055230069140347e01a3b00d1b8068cc0f2de0696702caf81255c1529e0a94d054a382e5140727e0993700c9780649c030de0186700c2f80615c0309e0184d00c238061140307e0183700c178060b40304e01825 18 262143 7 127 11 2047 21 2097151
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_56_15 (Nat.sub p 480)) (cc_56_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (cc_56_13 (Nat.sub p 416)) (cc_56_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 448)) (Bool.rec (Bool.rec (cc_56_11 (Nat.sub p 352)) (cc_56_10 (Nat.sub p 320)) (Nat.blt p 352)) (Bool.rec (cc_56_9 (Nat.sub p 288)) (cc_56_8 (Nat.sub p 256)) (Nat.blt p 288)) (Nat.blt p 320)) (Nat.blt p 384)) (Bool.rec (Bool.rec (Bool.rec (cc_56_7 (Nat.sub p 224)) (cc_56_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_56_5 (Nat.sub p 160)) (cc_56_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_56_3 (Nat.sub p 96)) (cc_56_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_56_1 (Nat.sub p 32)) (cc_56_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 256)
def f_56 : Nat → Nat × Nat := unpackForestF 0xf715df5a55f625df595500c5ff4a4500c5bf3a6d00c57f214df204deea45f0a4df084dee945ef24def14dee84500c53ed85dec155ec95dec05500b5feb23500b5b00b57e993de8235e8a3de813500b53e704de5945e614de584500b4fe493de3235e3a3de313500b4be215d00b47e113ddfa35e023ddf93500b43ddb64dda34dd935d9b4bdc364dc135d9b43db05dd9955da15dd985500a5f00a5bd837cd634bd6b7cd6a34d634300a5700a53d4354d4234cf36bd2b54d2935cf363cf26fcf267d084dcf145cf94dcf04500a4f00a4bcdb6cc9b6bcbb6ccba34cb935c9b63c9a6fc9a67c995d00a47c8028c802400a43c5d6fc5d6bc5d67c5d6300a3fc4a64c056fc3a54c056bc237cc227cc0567c0b54c0a54c056300a3bbec68be965b4d6fbdc58b4d6bbc470bc27cb4d67b9c58b9a54b9955b9855b4d63b7d6fb7d63b7845b494db6955b5563b5d63b5145b484d00a37b3a64b056fb2a54b056bb1a7cb0567b0a54b056300a33af045a8b4fae235a8b4ba8b47aca35a8b43ab845a8a4fa8a47a8a3fa914ca904da8a370095fa7954a3c5fa6944a3c5ba596ca3c57a4244a4144a3c530095ba2c7c93b4fa137ca123593b4ba057093b479e37c9e2359e13493b4393a6d9c47c9c27c93a4f9b57093a479a27c93a3f94b5f98c6c94b5b9786c94b5796b5c9546495b549503494b539447093a3700957929548c45f919448c45b9096c8c4578f9448c4538c0188cb4f8cb4b8cb478cb438c014009538ac648a86581b6f89b5481b63884648806581a6f8705d81a4581a3f84c588494c8484d81a378236f8226f8224d82237818450094f0094b805687a36f7e36c7e2357e1347a3637d5687a26f7c26e7a25d7a23f7ac607a2370094778818788140094377b646f56f76b546f56375b646f26f74b546f25f7336c7316c6f2577256f6f24570d6f70c636f2356f15f6f1570093f0093b6dc686956f6bc586b9546b855695636915f6915769d636904d009376793c679340093366a6464d6f653546525464d630092f6394461c5b622446214461c530092b60b6457d6f5eb545ea545e95457d635cb445ca445c94457c635b3445b24457c5b59344592445914457c535856f57a46009275614c561440092354945548444e34f539454e24f5214d5204c4e23750a4550a374e14f4f84c4e1374ea464e1270085f0085b4cc7c4934f4926d4ac7c4aa7c4924f49c7049237008574782c47824008534696541b6f4596541a6f4414d4404c41a37432374196f41937419270084f0084b3fd683f96533b6f3e5683e16533a6f3ca6e3c94533a5d3b4603b14d33a3739a5d39a373396f36b6f36a6f36a4536a373696e3395d35c60339373436c342463392700847008433235427d633136427a6f3035427a5f2f14d27a352da5f2da352796f2cb542795f2a5632a26f2a25f2a24d27935283442824428144279270083f0083b2595525854245632416f2415f008372283c2283400833213542125420d630082f0082b1db541da541d9551d85417d6317a461c2461796f1a3541a2541a0541795f18136189361806f1785600827008231615415c5f0081f0081b13254131541305401d6311264111641106401c6f0fa540f85401c5f0da640d9640d86401b6f0ba540b9540b85401b5f0ad68086730825c095630815c0805c01b4706b6306a4601a36058640236f048640226f034600304c02237021260185600817008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 fullMask g_56 ep_56 495 bds_56 (dagTraceF fullMask rootStock 11 f_56) (cur_56 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_9 : treeBlockF 288 320 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_10 : treeBlockF 320 352 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_11 : treeBlockF 352 384 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_12 : treeBlockF 384 416 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_13 : treeBlockF 416 448 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_14 : treeBlockF 448 480 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_15 : treeBlockF 480 495 (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nj_56_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_1 (fun _ h1 h2 => treeBlockF_at nb_56_2 h1 h2)
theorem nj_56_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_2 (fun _ h1 h2 => treeBlockF_at nb_56_3 h1 h2)
theorem nj_56_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_3 (fun _ h1 h2 => treeBlockF_at nb_56_4 h1 h2)
theorem nj_56_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_4 (fun _ h1 h2 => treeBlockF_at nb_56_5 h1 h2)
theorem nj_56_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_5 (fun _ h1 h2 => treeBlockF_at nb_56_6 h1 h2)
theorem nj_56_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_6 (fun _ h1 h2 => treeBlockF_at nb_56_7 h1 h2)
theorem nj_56_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_7 (fun _ h1 h2 => treeBlockF_at nb_56_8 h1 h2)
theorem nj_56_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_8 (fun _ h1 h2 => treeBlockF_at nb_56_9 h1 h2)
theorem nj_56_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_9 (fun _ h1 h2 => treeBlockF_at nb_56_10 h1 h2)
theorem nj_56_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_10 (fun _ h1 h2 => treeBlockF_at nb_56_11 h1 h2)
theorem nj_56_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_11 (fun _ h1 h2 => treeBlockF_at nb_56_12 h1 h2)
theorem nj_56_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_12 (fun _ h1 h2 => treeBlockF_at nb_56_13 h1 h2)
theorem nj_56_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_13 (fun _ h1 h2 => treeBlockF_at nb_56_14 h1 h2)
theorem nj_56_15 : ∀ i, 0 ≤ i → i < 495 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := block_join nj_56_14 (fun _ h1 h2 => treeBlockF_at nb_56_15 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 495 → (dagCheckNodeV4 fullMask g_56 ep_56 bds_56 495 (dagTraceF fullMask rootStock 11 f_56) cur_56) i = true := nj_56_15
theorem lb_56 : LowerBin fullMask rootStock g_56 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def wg : List Gate := [⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3903381504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3903381504)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3903381504) = g_56 by decide]
  exact lb_56

end PEqualNP.Outside.L_meta_49311

theorem PEqualNP.Outside.L_meta_49311 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3903381504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3903381504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49311.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3903381504) 13 PEqualNP.Outside.L_meta_49311.root_lb PEqualNP.Outside.L_meta_49311.wg 18 rfl PEqualNP.Outside.L_meta_49311.wfits PEqualNP.Outside.L_meta_49311.weval
