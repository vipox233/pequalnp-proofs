import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49229

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

def m_0 : Nat := 0x4444000044440000
def s_0 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_0 : Nat := 0x4000004440000
def ep_0 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_1 : Nat := 0xff000000000000
def s_1 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_1 : Nat := 0x17000000000000
def ep_1 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_2 : Nat := 0xff0000000000
def s_2 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_2 : Nat := 0x170000000000
def ep_2 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_3 : Nat := 0xc000c000c000c0
def s_3 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_3 : Nat := 0x40004000c0
def ep_3 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_4 : Nat := 0x5500550000000000
def s_4 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_4 : Nat := 0x100150000000000
def ep_4 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_5 : Nat := 0x3300330000000000
def s_5 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_5 : Nat := 0x100130000000000
def ep_5 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_6 : Nat := 0xf000f0000000000
def s_6 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_6 : Nat := 0x100070000000000
def ep_6 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_7 : Nat := 0x4444444400000000
def s_7 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_7 : Nat := 0x4044400000000
def ep_7 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_8 : Nat := 0x4040404040404040
def s_8 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_8 : Nat := 0x4000404040
def ep_8 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x5050505000000000
def s_9 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_9 : Nat := 0x10105000000000
def ep_9 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_10 : Nat := 0x22222222
def s_10 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_10 : Nat := 0x20222
def ep_10 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
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

def m_11 : Nat := 0xa0a0a0a
def s_11 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_11 : Nat := 0x2020a
def ep_11 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
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

def m_12 : Nat := 0xc0c0c0c0
def s_12 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_12 : Nat := 0x4040c0
def ep_12 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
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

def m_13 : Nat := 0x5500000055000000
def s_13 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_13 : Nat := 0x100000015000000
def ep_13 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_14 : Nat := 0xc0c00000c0c0
def s_14 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_14 : Nat := 0x40000040c0
def ep_14 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_15 : Nat := 0x5050000050500000
def s_15 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_15 : Nat := 0x10000010500000
def ep_15 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_16 : Nat := 0x4400440044004400
def s_16 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_16 : Nat := 0x40004004400
def ep_16 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_17 : Nat := 0xf0f000000000000
def s_17 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_17 : Nat := 0x107000000000000
def ep_17 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_18 : Nat := 0x5555000000000000
def s_18 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_18 : Nat := 0x115000000000000
def ep_18 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_19 : Nat := 0x3333000000000000
def s_19 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_19 : Nat := 0x113000000000000
def ep_19 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_20 : Nat := 0x5000500050005000
def s_20 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_20 : Nat := 0x100010005000
def ep_20 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
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

def m_21 : Nat := 0xff00ff0000000000
def s_21 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_21 : Nat := 0x100170000000000
def ep_21 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_21 : ep_21 = edgePack m_21 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_2
  · exact lb_4
  · exact lb_5
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_21_1 (Nat.sub p 32)) (cc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 43 bds_21 (dagTraceF m_21 s_21 6 f_21) (cur_21 0) s_21 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 43 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21) = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21) i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xffff000000000000
def s_22 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_22 : Nat := 0x117000000000000
def ep_22 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17), (m_1, s_1, 4, g_1), (m_18, s_18, 4, g_18), (m_19, s_19, 4, g_19)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_1
  · exact lb_18
  · exact lb_19
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_22_1 (Nat.sub p 32)) (cc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 43 bds_22 (dagTraceF m_22 s_22 6 f_22) (cur_22 0) s_22 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 43 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22) = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22) i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xffff00000000
def s_23 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_23 : Nat := 0x175700000000
def ep_23 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xf0f0f0f000000000
def s_24 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_24 : Nat := 0x10105000000000
def ep_24 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_24 g_24 ep_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xf0f0f0f00000000
def s_25 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_25 : Nat := 0x107070700000000
def ep_25 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_25 g_25 ep_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xcccccccc00000000
def s_26 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_26 : Nat := 0x4044400000000
def ep_26 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x3333333300000000
def s_27 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_27 : Nat := 0x113131300000000
def ep_27 : Nat := 0x1200000000000012000000000000010202020000000000000000000000000110101000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0x5050505050505050
def s_28 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_28 : Nat := 0x10105010505050
def ep_28 : Nat := 0x1040400000001040000040000010004000400000000000000000000000101000100000000000000000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_15, s_15, 4, g_15), (m_20, s_20, 4, g_20), (m_8, s_8, 4, g_8)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_15
  · exact lb_20
  · exact lb_8
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_29 : Nat := 0x5555555500000000
def s_29 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_29 : Nat := 0x115155500000000
def ep_29 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_18, s_18, 4, g_18), (m_9, s_9, 4, g_9), (m_7, s_7, 4, g_7)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_18
  · exact lb_9
  · exact lb_7
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0x666600006666
def s_30 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_30 : Nat := 0x64600004666
def ep_30 : Nat := 0x402000000000000000000000004000000020000006020000020000000000000000000000000000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31243048c4f080a193c202928f611ab92a524c80a8413000f 7 127 3 7 10 1023 15 32767
def f_30 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 10 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 10 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 10 (dagTraceF m_30 s_30 4 f_30) cur_30) = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 10 (dagTraceF m_30 s_30 4 f_30) cur_30) i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x66006600660066
def s_31 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_31 : Nat := 0x6004600460066
def ep_31 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_31 : KnownBin bds_31 := by intro b hb; simp [bds_31] at hb
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp [bds_31] at hb
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_31] at hb
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31243048c4f080a193c202928f611ab92a524c80a8413000f 7 127 3 7 10 1023 15 32767
def f_31 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 10 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 10 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 10 (dagTraceF m_31 s_31 4 f_31) cur_31) = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 10 (dagTraceF m_31 s_31 4 f_31) cur_31) i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0x3030303030303030
def s_32 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_32 : Nat := 0x10101010101030
def ep_32 : Nat := 0x1000002000001000000000200010000000000020000000000000000000000000000000000010101010101000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_32 : KnownBin bds_32 := by intro b hb; simp [bds_32] at hb
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp [bds_32] at hb
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_32] at hb
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_32_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 64 bds_32 (dagTraceF m_32 s_32 5 f_32) (cur_32 0) s_32 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) cur_32) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 64 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) cur_32) = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) cur_32) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) cur_32) i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xc0c0c0c0c0c0c0c0
def s_33 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_33 : Nat := 0x40004040c0
def ep_33 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_12, s_12, 4, g_12), (m_8, s_8, 4, g_8), (m_3, s_3, 4, g_3)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_12
  · exact lb_8
  · exact lb_3
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_34 : Nat := 0xcccc0000cccc
def s_34 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_34 : Nat := 0x444000044cc
def ep_34 : Nat := 0x408800000000000000000000004000000088000004000000000000000000000000000000044400004400
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

def m_35 : Nat := 0x3333000033330000
def s_35 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_35 : Nat := 0x113000011130000
def ep_35 : Nat := 0x1000000000000000000000000012000000020000010200000002000000000000000000000110000011100000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x5555000055550000
def s_36 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_36 : Nat := 0x115000015550000
def ep_36 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_18, s_18, 4, g_18), (m_15, s_15, 4, g_15), (m_0, s_0, 4, g_0)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_18
  · exact lb_15
  · exact lb_0
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_36_1 (Nat.sub p 32)) (cc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 43 bds_36 (dagTraceF m_36 s_36 6 f_36) (cur_36 0) s_36 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 43 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0x5500550055005500
def s_37 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_37 : Nat := 0x100150015005500
def ep_37 : Nat := 0x1400400000001400000040000000000000000000010004000400000001001000100000000000000000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_13, s_13, 4, g_13), (m_20, s_20, 4, g_20), (m_16, s_16, 4, g_16)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_13
  · exact lb_20
  · exact lb_16
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_37_1 (Nat.sub p 32)) (cc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 43 bds_37 (dagTraceF m_37 s_37 6 f_37) (cur_37 0) s_37 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 43 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) i = true := nj_37_1
theorem lb_37 : LowerBin m_37 s_37 g_37 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xff000000ff00
def s_38 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_38 : Nat := 0x170000005700
def ep_38 : Nat := 0x400000000000000000000000000000000000000006000000020000001200000002000000140000005400
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x1050000050f0
def ep_39 : Nat := 0x40a0000000000000000000000040000000a0000000000000000000001000000000000000105000005000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcccc0000cccc0000
def s_40 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_40 : Nat := 0x4000004440000
def ep_40 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0x3300330033003300
def s_41 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_41 : Nat := 0x100130011001300
def ep_41 : Nat := 0x1000000000001200000002000000000000000000010002000000020000000000000000000100100011001000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xcc00cc00cc00cc00
def s_42 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_42 : Nat := 0x40004004400
def ep_42 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000040004004400
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf000f000f000f000
def s_43 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_43 : Nat := 0x100010005000
def ep_43 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000100010005000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_20
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xf000f000f000f00
def s_44 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_44 : Nat := 0x100070005000700
def ep_44 : Nat := 0x400000000000600000002000000000000000000000000000000000001000200000002000100040005000400
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0x33333333
def s_45 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_45 : Nat := 0x11131333
def ep_45 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xcc00cc00cc00cc
def s_46 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_46 : Nat := 0x40044004400cc
def ep_46 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xff00ff00
def s_47 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_47 : Nat := 0x15005700
def ep_47 : Nat := 0x42000000000000000000000000000400020000000000100002000000000015005400
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_47 : KnownBin bds_47 := by intro b hb; simp [bds_47] at hb
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp [bds_47] at hb
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_47] at hb
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_47_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 64 bds_47 (dagTraceF m_47 s_47 5 f_47) (cur_47 0) s_47 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 64 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47) i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xf0f0f0f0
def s_48 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_48 : Nat := 0x105050f0
def ep_48 : Nat := 0x40a000000000004000a0000000000000000000000000100000000000000010505000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xf0f0f0f
def s_49 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_49 : Nat := 0x507070f
def ep_49 : Nat := 0x2080000000000020008000000000000000000000000000202000000000005040400
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xcccccccc
def s_50 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_50 : Nat := 0x44444cc
def ep_50 : Nat := 0x40880000000000400088000000000400000000000000000000000000000004444400
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xaaaaaaaa
def s_51 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_51 : Nat := 0x202aa
def ep_51 : Nat := 0x2a800000000000200a8000000000002020000000000000202000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xff000000ff000000
def s_52 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_52 : Nat := 0x100000015000000
def ep_52 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000100000015000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xff000000ff0000
def s_53 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_53 : Nat := 0x17000000570000
def ep_53 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xf000f000f000f0
def s_54 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_54 : Nat := 0x100050005000f0
def ep_54 : Nat := 0x4000a000000040000000a00000000000000000000000000000000000100000000000000010005000500000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xf0f00000f0f00000
def s_55 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_55 : Nat := 0x10000010500000
def ep_55 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xf0f00000f0f0000
def s_56 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_56 : Nat := 0x107000005070000
def ep_56 : Nat := 0x400000000000000000000000006000000020000000000000000000001020000000200000104000005040000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 0 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) s_56 4 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_56 g_56 ep_56 bds_56 0 (dagTraceF m_56 s_56 4 f_56) cur_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0x5050a0a05050a0a
def s_57 : List Nat := [0xa0a00000a0a, 0x101020201010202, 0x5000a0005000a, 0x5050a0a]
def g_57 : Nat := 0x10502020505020a
def ep_57 : Nat := 0x400000800000000000000000004000000000008000000000000000001000202000002000000000000000000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_57 : KnownBin bds_57 := by intro b hb; simp [bds_57] at hb
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp [bds_57] at hb
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_57] at hb
def cur_57 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58952244890e8701 0x39283048e8d081a1924205128ea11b313a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_57 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 10 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) s_57 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57 : treeBlockF 0 10 (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 10 (dagTraceF m_57 s_57 4 f_57) cur_57) = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 10 (dagTraceF m_57 s_57 4 f_57) cur_57) i = true := fun _ h1 h2 => treeBlockF_at nb_57 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0x5500aa005500aa
def s_58 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_58 : Nat := 0x150002005500aa
def ep_58 : Nat := 0x4000a800000000000000000000000000000000000400020000000000100002000000000000000000000000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_58 : KnownBin bds_58 := by intro b hb; simp [bds_58] at hb
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp [bds_58] at hb
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_58] at hb
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x324438cd0ce2343492f61abad54a4744a80f 7 127 3 7 6 63 11 2047
def f_58 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 10 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) s_58 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 10 (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 10 (dagTraceF m_58 s_58 4 f_58) cur_58) = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 10 (dagTraceF m_58 s_58 4 f_58) cur_58) i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0x1111222211112222
def s_59 : List Nat := [0x222200002222, 0x101020201010202, 0x11002200110022, 0x11112222]
def g_59 : Nat := 0x111020211110222
def ep_59 : Nat := 0x1000002000000000000000000010000000000020010002020000020000000000000000000000000000000000
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_59 : KnownBin bds_59 := by intro b hb; simp [bds_59] at hb
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp [bds_59] at hb
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_59] at hb
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58952244890e8701 0x39283048e8d081a1924205128ea11b313a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_59 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 10 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) s_59 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 10 (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 10 (dagTraceF m_59 s_59 4 f_59) cur_59) = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 10 (dagTraceF m_59 s_59 4 f_59) cur_59) i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0x4444444444444444
def s_60 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_60 : Nat := 0x4044404444444
def ep_60 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_7, s_7, 4, g_7), (m_16, s_16, 4, g_16), (m_8, s_8, 4, g_8)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_7
  · exact lb_16
  · exact lb_8
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_60_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_60_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_60 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_60_1 (Nat.sub p 32)) (cc_60_0 p) (Nat.blt p 32)
def f_60 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 43 bds_60 (dagTraceF m_60 s_60 6 f_60) (cur_60 0) s_60 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 32 (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 43 (dagTraceF m_60 s_60 6 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_1 : treeBlockF 32 43 (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 43 (dagTraceF m_60 s_60 6 f_60) cur_60) = true := by decide +kernel
theorem nj_60_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 43 (dagTraceF m_60 s_60 6 f_60) cur_60) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_60_1 h1 h2)
theorem nc_60 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 43 (dagTraceF m_60 s_60 6 f_60) cur_60) i = true := nj_60_1
theorem lb_60 : LowerBin m_60 s_60 g_60 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0x55550000aaaa
def s_61 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_61 : Nat := 0x1555000002aa
def ep_61 : Nat := 0x40000000a8000004000000020000001000000002000000000000000000
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_61 : KnownBin bds_61 := by intro b hb; simp [bds_61] at hb
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp [bds_61] at hb
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_61] at hb
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x192440619343061134349253d84d5d2d549481a105800f 7 127 3 7 9 511 14 16383
def f_61 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV4 m_61 g_61 ep_61 10 bds_61 (dagTraceF m_61 s_61 4 f_61) (cur_61 0) s_61 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 10 (dagCheckNodeV4 m_61 g_61 ep_61 bds_61 10 (dagTraceF m_61 s_61 4 f_61) cur_61) = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_61 g_61 ep_61 bds_61 10 (dagTraceF m_61 s_61 4 f_61) cur_61) i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_61 kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0x55005500aa00aa
def s_62 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_62 : Nat := 0x150055000200aa
def ep_62 : Nat := 0x40000000a80000000000000000000400000002000000100000000200000000000000000000
theorem epk_62 : ep_62 = edgePack m_62 g_62 := by decide +kernel
def bds_62 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_62 : KnownBin bds_62 := by intro b hb; simp [bds_62] at hb
theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by intro b hb; simp [bds_62] at hb
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_62] at hb
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x192440619343061134349253d84d5d2d549481a105800f 7 127 3 7 9 511 14 16383
def f_62 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV4 m_62 g_62 ep_62 10 bds_62 (dagTraceF m_62 s_62 4 f_62) (cur_62 0) s_62 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 10 (dagCheckNodeV4 m_62 g_62 ep_62 bds_62 10 (dagTraceF m_62 s_62 4 f_62) cur_62) = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_62 g_62 ep_62 bds_62 10 (dagTraceF m_62 s_62 4 f_62) cur_62) i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_62 kn_62 sub_62 gl_62 rc_62 nc_62

def m_63 : Nat := 0x2222222222222222
def s_63 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_63 : Nat := 0x2020200020222
def ep_63 : Nat := 0x2000000200000002200002000000020020000202020002020000000000000000000000000000000000
theorem epk_63 : ep_63 = edgePack m_63 g_63 := by decide +kernel
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV4 m_63 g_63 ep_63 0 bds_63 (dagTraceF m_63 s_63 4 f_63) (cur_63 0) s_63 4 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_63 g_63 ep_63 bds_63 0 (dagTraceF m_63 s_63 4 f_63) cur_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_63 kn_63 sub_63 gl_63 rc_63 nc_63

def m_64 : Nat := 0xa0a0a0a0a0a0a0a
def s_64 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_64 : Nat := 0x202020002020a
def ep_64 : Nat := 0x800000200000002080002000000020008000000000000000000020202000202000000000000000000
theorem epk_64 : ep_64 = edgePack m_64 g_64 := by decide +kernel
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_64 : ∀ b ∈ bds_64, m_64 &&& b.1 = b.1 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV4 m_64 g_64 ep_64 0 bds_64 (dagTraceF m_64 s_64 4 f_64) (cur_64 0) s_64 4 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_64 g_64 ep_64 bds_64 0 (dagTraceF m_64 s_64 4 f_64) cur_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_64 kn_64 sub_64 gl_64 rc_64 nc_64

def m_65 : Nat := 0x5a5a00005a5a
def s_65 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_65 : Nat := 0x12520000525a
def ep_65 : Nat := 0x400800000000000000000000004000000008000000000000000000001202000002000000000000000000
theorem epk_65 : ep_65 = edgePack m_65 g_65 := by decide +kernel
def bds_65 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_65 : KnownBin bds_65 := by intro b hb; simp [bds_65] at hb
theorem sub_65 : ∀ b ∈ bds_65, m_65 &&& b.1 = b.1 := by intro b hb; simp [bds_65] at hb
theorem gl_65 : ∀ b ∈ bds_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_65] at hb
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_65 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV4 m_65 g_65 ep_65 10 bds_65 (dagTraceF m_65 s_65 4 f_65) (cur_65 0) s_65 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 10 (dagCheckNodeV4 m_65 g_65 ep_65 bds_65 10 (dagTraceF m_65 s_65 4 f_65) cur_65) = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_65 g_65 ep_65 bds_65 10 (dagTraceF m_65 s_65 4 f_65) cur_65) i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_65 kn_65 sub_65 gl_65 rc_65 nc_65

def m_66 : Nat := 0x5a005a005a005a
def s_66 : List Nat := [0xa000a000a000a, 0x12001200120012, 0x5a0000005a, 0x5a005a]
def g_66 : Nat := 0x1200520052005a
def ep_66 : Nat := 0x40000800000040000000080000000000000000000000000000000000120002000200000000000000000000
theorem epk_66 : ep_66 = edgePack m_66 g_66 := by decide +kernel
def bds_66 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_66 : KnownBin bds_66 := by intro b hb; simp [bds_66] at hb
theorem sub_66 : ∀ b ∈ bds_66, m_66 &&& b.1 = b.1 := by intro b hb; simp [bds_66] at hb
theorem gl_66 : ∀ b ∈ bds_66, canon b.1 g_66 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_66] at hb
def cur_66 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_66 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV4 m_66 g_66 ep_66 10 bds_66 (dagTraceF m_66 s_66 4 f_66) (cur_66 0) s_66 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66 : treeBlockF 0 10 (dagCheckNodeV4 m_66 g_66 ep_66 bds_66 10 (dagTraceF m_66 s_66 4 f_66) cur_66) = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_66 g_66 ep_66 bds_66 10 (dagTraceF m_66 s_66 4 f_66) cur_66) i = true := fun _ h1 h2 => treeBlockF_at nb_66 h1 h2
theorem lb_66 : LowerBin m_66 s_66 g_66 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_66 kn_66 sub_66 gl_66 rc_66 nc_66

def m_67 : Nat := 0xc0c0c0c0c0c0c0c
def s_67 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_67 : Nat := 0x404040404040c
def ep_67 : Nat := 0x400000800000400000000080004000000000008000000000000000000000000000000000004040404040400
theorem epk_67 : ep_67 = edgePack m_67 g_67 := by decide +kernel
def bds_67 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_67 : KnownBin bds_67 := by intro b hb; simp [bds_67] at hb
theorem sub_67 : ∀ b ∈ bds_67, m_67 &&& b.1 = b.1 := by intro b hb; simp [bds_67] at hb
theorem gl_67 : ∀ b ∈ bds_67, canon b.1 g_67 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_67] at hb
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_67_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_67 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_67_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_67_0 p) (Nat.blt p 32)
def f_67 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV4 m_67 g_67 ep_67 64 bds_67 (dagTraceF m_67 s_67 5 f_67) (cur_67 0) s_67 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 32 (dagCheckNodeV4 m_67 g_67 ep_67 bds_67 64 (dagTraceF m_67 s_67 5 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_1 : treeBlockF 32 64 (dagCheckNodeV4 m_67 g_67 ep_67 bds_67 64 (dagTraceF m_67 s_67 5 f_67) cur_67) = true := by decide +kernel
theorem nj_67_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_67 g_67 ep_67 bds_67 64 (dagTraceF m_67 s_67 5 f_67) cur_67) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_67_1 h1 h2)
theorem nc_67 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_67 g_67 ep_67 bds_67 64 (dagTraceF m_67 s_67 5 f_67) cur_67) i = true := nj_67_1
theorem lb_67 : LowerBin m_67 s_67 g_67 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_67 kn_67 sub_67 gl_67 rc_67 nc_67

def m_68 : Nat := 0x55aa000055aa
def s_68 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_68 : Nat := 0x1502000055aa
def ep_68 : Nat := 0x40a800000000000000000000000000000000000004020000000000001002000000000000000000000000
theorem epk_68 : ep_68 = edgePack m_68 g_68 := by decide +kernel
def bds_68 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_68 : KnownBin bds_68 := by intro b hb; simp [bds_68] at hb
theorem sub_68 : ∀ b ∈ bds_68, m_68 &&& b.1 = b.1 := by intro b hb; simp [bds_68] at hb
theorem gl_68 : ∀ b ∈ bds_68, canon b.1 g_68 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_68] at hb
def cur_68 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x324438cd0ce2343492f61abad54a4744a80f 7 127 3 7 6 63 11 2047
def f_68 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV4 m_68 g_68 ep_68 10 bds_68 (dagTraceF m_68 s_68 4 f_68) (cur_68 0) s_68 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68 : treeBlockF 0 10 (dagCheckNodeV4 m_68 g_68 ep_68 bds_68 10 (dagTraceF m_68 s_68 4 f_68) cur_68) = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_68 g_68 ep_68 bds_68 10 (dagTraceF m_68 s_68 4 f_68) cur_68) i = true := fun _ h1 h2 => treeBlockF_at nb_68 h1 h2
theorem lb_68 : LowerBin m_68 s_68 g_68 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_68 kn_68 sub_68 gl_68 rc_68 nc_68

def m_69 : Nat := 0x5555555555555555
def s_69 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_69 : Nat := 0x115155515555555
def ep_69 : Nat := 0x1440400000001440000040000014004000400000010404000400000001101000100000000000000000000000
theorem epk_69 : ep_69 = edgePack m_69 g_69 := by decide +kernel
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29), (m_36, s_36, 7, g_36), (m_28, s_28, 7, g_28), (m_37, s_37, 7, g_37)]
theorem kn_69 : KnownBin bds_69 := by
  intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_29
  · exact lb_36
  · exact lb_28
  · exact lb_37
theorem sub_69 : ∀ b ∈ bds_69, m_69 &&& b.1 = b.1 := by intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_69 : ∀ b ∈ bds_69, canon b.1 g_69 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_69 : Nat → List (Nat × Nat) := unpackCursorV4 0xe001 0x174fba5dd1ee87e4ff25f91fc8763fb1dd8dec66d4f6a5b51da86d3f69db4dda66d2f695b49da4601f 10 1023 5 31 10 1023 13 8191
def f_69 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV4 m_69 g_69 ep_69 1 bds_69 (dagTraceF m_69 s_69 8 f_69) (cur_69 0) s_69 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69 : treeBlockF 0 1 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 1 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 1 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := fun _ h1 h2 => treeBlockF_at nb_69 h1 h2
theorem lb_69 : LowerBin m_69 s_69 g_69 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_69 kn_69 sub_69 gl_69 rc_69 nc_69

def m_70 : Nat := 0xff00ff00ff00ff00
def s_70 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_70 : Nat := 0x100170015005700
def ep_70 : Nat := 0x1400400000001600000042000000000000000000010006000400020001001200100002000100140015005400
theorem epk_70 : ep_70 = edgePack m_70 g_70 := by decide +kernel
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21), (m_37, s_37, 7, g_37), (m_43, s_43, 5, g_43), (m_41, s_41, 5, g_41), (m_44, s_44, 5, g_44), (m_42, s_42, 5, g_42), (m_38, s_38, 5, g_38), (m_52, s_52, 5, g_52), (m_47, s_47, 6, g_47)]
theorem kn_70 : KnownBin bds_70 := by
  intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_37
  · exact lb_43
  · exact lb_41
  · exact lb_44
  · exact lb_42
  · exact lb_38
  · exact lb_52
  · exact lb_47
theorem sub_70 : ∀ b ∈ bds_70, m_70 &&& b.1 = b.1 := by intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_70 : ∀ b ∈ bds_70, canon b.1 g_70 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_70 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf49ff493338c5b7e39713464345773509b4279357428741bb314db06b900590001 0x1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b522b4f2b4e2b4d1a5f1a5e1a5b1a571a531a522a4b3a4a2a493a473a462a432a413a373a363a35195f195b19571953594f394b39475943493f493d493b79394937693549334931292f492b49272923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b532b4f3b4e2b4d2b472b452b432b421a5f1a5e1a5b1a5a1a571a561a531a522a473a462a452a3f2a3e2a3d195f195b19571953394f394b39473943293f293b29372933292f292d292b79292927692529232921185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b532b4f2b4e2b4d1a5f1a5b1a571a533a4f3a4e4a4d3a3f3a3e2a3b2a392a333a322a31c230195f195b19571953394f694d394b39493947394539437941393f393b39373933292f492b49272923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a432a3f3a3e2a3d194f194b19471943393f393b39373933292f292b29272923184e28261c5f1c5e1c5b1c571c531c521b5f1b5e1b5b1b571b531b522b4f2b4d2b4b2b4a2b473b462b45c3441a5f1a5e1a5b1a5a1a571a561a531a522a4f4a4e2a4d2a3f2a3e2a3d195f195b19571953594f394b39475943293f293b29372933292f292d292b79292927692529232921185e282688241c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b525b4f5b4e5b4d1a5f1a5b1a571a535a4f3a4b3a475a435a3f4a3d5a3b2a395a374a355a332a31195f195e195b195719531952394b394a69493947394659435941393739363935692f692b69276923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b533b4f3b4b3b473b431a5f1a5b1a571a533a4f3a4e6a4d3a473a453a433a426a3f7a3b6a377a33195f195e195b195a1957195619531952394739463945393f293e393b393a3937493639332932392f592e392d185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b533b4f3b4e3b4d1a5f1a5b1a571a533a4f4a4d3a4b2a493a473a453a432a413a3f3a3b3a373a33195f195b19571953394f394e594d393f393e393b39393933393269317130692f692b69276923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a433a3f3a3b3a373a33194f194b19471943393f393e593d592f592b59275923184e58161c5f1c5e1c5b1c571c531c521b5f1b5b1b571b535b4f3b4b3b475b431a5f1a5e1a5b1a571a531a525a4f5a4d3a4b3a4a3a473a466a4572446a3f7a3b6a377a33195f195e195b195a1957195619531952594f594e594d593f293e593b493a5937493659332932392f392e392d185e581688141c5f1c5b1c571c531b5f1b5b1b571b532b4f2b4b2b472b431a5f1a5e1a5b1a5a1a571a561a531a522a4f5a4e2a4b2a4a2a473a462a432a422a3f2a3e2a3d195f195e195b195719531952694f694b69476943293b293a69392937293629332931292729264925185e1c5f1c5b1c571c531b5f1b5e1b5b1b571b531b524b4f2b4b4b472b431a5f1a5b1a571a536a4f7a4b6a477a432a3f2a3e6a3d4a374a352a332a32195f195e195b195a1957195619531952494f594e494b394a4947394649434942493749364935292f292e292d185e1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b524b4f4b4e4b4b3b4a4b473b464b435b421a5f1a5b1a571a534a4f2a4b4a472a434a3f4a3e4a3d195f195b19571953694f694b69476943293f293e293d292f292e492b49292923292269212120185e1b4f1b4b1b471b431a4f1a4e1a4b1a471a431a424a3f4a3b4a374a33194f194b19471943293f293b29372933292f492e292d184e28161c5f1c5b1c571c531b5f1b5e1b5b1b571b531b522b4f2b4b2b472b431a5f1a5e1a5b1a571a531a526a4f7a4b6a477a432a3f2a3d2a3b2a3a2a372a366a352234195f195e195b195a1957195619531952294f594e294b294a2947394629432942293f293e293d292f492e292d185e281688141b4f1b4b1b471b431a4f1a4b1a471a43f23fe23bd237b233194f194b19471943a13f913b81376133512f412b31271123184e001f 16 65535 6 63 11 2047 16 65535
def f_70 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV4 m_70 g_70 ep_70 16 bds_70 (dagTraceF m_70 s_70 8 f_70) (cur_70 0) s_70 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70 : treeBlockF 0 16 (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 16 (dagTraceF m_70 s_70 8 f_70) cur_70) = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 16 (dagTraceF m_70 s_70 8 f_70) cur_70) i = true := fun _ h1 h2 => treeBlockF_at nb_70 h1 h2
theorem lb_70 : LowerBin m_70 s_70 g_70 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_70 kn_70 sub_70 gl_70 rc_70 nc_70

def m_71 : Nat := 0xf0f0f0f0f0f0f0f0
def s_71 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_71 : Nat := 0x101050105050f0
def ep_71 : Nat := 0x104040a000001040000040a000100040004000a0000000000000000000101000100000000010105010505000
theorem epk_71 : ep_71 = edgePack m_71 g_71 := by decide +kernel
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 5, g_24), (m_33, s_33, 7, g_33), (m_54, s_54, 5, g_54), (m_48, s_48, 5, g_48), (m_28, s_28, 7, g_28), (m_9, s_9, 4, g_9), (m_43, s_43, 5, g_43), (m_39, s_39, 5, g_39), (m_55, s_55, 5, g_55), (m_32, s_32, 6, g_32)]
theorem kn_71 : KnownBin bds_71 := by
  intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_24
  · exact lb_33
  · exact lb_54
  · exact lb_48
  · exact lb_28
  · exact lb_9
  · exact lb_43
  · exact lb_39
  · exact lb_55
  · exact lb_32
theorem sub_71 : ∀ b ∈ bds_71, m_71 &&& b.1 = b.1 := by intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_71 : ∀ b ∈ bds_71, canon b.1 g_71 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_71 : Nat → List (Nat × Nat) := unpackCursorV4 0x187cbb125cf52a4d5afdd26ee032e91587e9d9d44d41a700af48383f14ce856a001540001 0x1c5f4c5e1c5b1c571c531c522b5f4b5b2b574b531b4f1b4b1b471b434a5f4a5e4a5b4a5a4a574a564a534a521a4f1a4e1a4b1a4a1a471a461a431a426a3f6a3e6a3d495f495e495b495749534952194f194b19471943293b293a79392937293669336931292729262925485f485b48574853184f184b18471843683f283b28376833682f382d682b682738256823781f781b781778131c5f4c5e1c5b1c571c531c522b5f2b5e2b5b2b572b534b521b4f1b4b1b471b434a5f4a5b4a574a531a4f1a4b1a471a432a3f2a3e7a3d2a372a352a332a32295f495e295b295a2957495629532952194f194e194b194a1947194619431942293729362935292f692e292d485f485b48574853184f184b18471843283f283b28372833882f782b78278823281f281d281b2817381528131c5f4c5e1c5b1c571c531c522b5f2b5e2b5b4b5a2b572b562b534b521b4f1b4e1b4b1b4a1b471b461b431b422a5f2a5b2a572a531a4f1a4b1a471a432a3f2a3e2a3d495f495b49574953194f194b19471943293f293e693d292f292e292b2929292329227921c120485f485b48574853184f184b18471843283f383d283b283728352833282f282b28272823781f781b781778131b4f4b4e1b4b1b471b431b422a4f2a4e2a4b2a472a434a421a3f1a3b1a371a33494f494b49474943193f193d193b193769351933292f292e692d484f484b48474843183f183b18371833282f282b28272823681f681b681768131c5f4c5e1c5b1c571c531c522b5f4b5e4b5b2b574b534b521b4f1b4b1b471b434a5f4a5e4a5b4a574a534a521a4f1a4b1a471a436a3f6a3d2a3b2a3a2a372a367a35c234495f495e495b495a4957495649534952194f194e194d194c194b194a194719466945994419431942693f693e693d292f292e292d485f485b48574853184f184b18471843683f283b28376833882f782b78278823681f381d681b6817381568131c5f4c5e1c5b1c571c531c522b5f4b5b2b574b531b4f1b4b1b471b433a5f4a5e3a5b3a5a3a574a563a533a521a4f1a4e1a4b1a4a1a471a461a431a42495f495b49574953194f194b19471943693f293b29376933392f392d392b89293927792539233921385f385e38574852184f1847283a28372836282728262825381f38171c5f4c5e1c5b1c571c531c522b5f2b5e2b5b2b572b534b521b4f1b4b1b471b434a5f4a5b4a574a531a4f1a4b1a471a432a3f2a3b2a372a33293e485e4856184e18462836882e78261c5f4c5e1c5b1c571c531c522b5f2b5e2b5b4b5a2b572b562b534b521b4f1b4e1b4b1b4a1b471b461b431b422a5f2a5b2a572a531a4f1a4b1a471a43495f495b49574953194f194b19471943293f793d293b29392937293529338931292f292b29272923385f3857184f1847283f283e383d282f282e28227020381f38171b4f4b4e1b4b1b471b431b422a4f2a4e2a4b2a472a434a421a3f1a3b1a371a33494f494b49474943193f193b19371933292f292b29272923282e1c5f4c5e1c5b1c571c531c522b5f4b5e4b5b2b574b534b521b4f1b4b1b471b434a5f4a5b4a574a531a4f1a4b1a471a436a3f2a3b2a376a33495e29367134485e4856184e184c18469844383e882e78261c5f4c5e1c5b1c571c531c524b5f4b5b4b574b531b4f1b4b1b471b434a5f4a5b4a574a531a4f1a4b1a471a437a3f8a3b7a378a33395f495e395b395a3957495639533952194f194e194b194a1947194619431942393f693e393b293a3937293639333932385f385e38574852184f1847383f3837782a382738263817381638151c5f4c5e1c5b1c571c531c524b5f4b5b4b574b531b4f1b4b1b471b434a5f4a5e4a5b4a574a534a521a4f1a4b1a471a437a3f7a3b7a377a33792e485e4856184e1846683e283638261c5f4c5e1c5b1c571c531c524b5f4b5b4b574b531b4f1b4b1b471b433a5f3a5e3a5b4a5a3a573a563a534a521a4f1a4e1a4b1a4a1a471a461a431a423a3f3a3e3a3b2a3a3a372a363a336a32495f495b49574953194f194b19471943793f793b79377933385f3857184f1847383f3837382f382e382d381f381e781220101b4f4b4e1b4b1b471b431b424a4f4a4b4a474a431a3f1a3b1a371a33394f394e394b394739434942193f193b19371933392f392b39273923381e1c5f4c5e1c5b1c571c531c524b5f4b5b4b574b531b4f1b4b1b471b434a5f4a5e4a5b4a574a534a521a4f1a4b1a471a437a3f8a3b7a378a33495e79262124485e4856184e184c18469844683e2836382e1b4f4b4e1b4b1b471b431b424a4f4a4b4a474a431a3f1a3b1a371a33494f494b49474943193f193b19371933f12fe12bd127b123484f484b48474843183f183b18371833a02f902b80276023501f401b30171013001f 17 131071 7 127 11 2047 16 65535
def f_71 : Nat → Nat × Nat := unpackForestF 0x14bc52b149f234148c42f10ac42774d0423107c41b105c924104c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV4 m_71 g_71 ep_71 16 bds_71 (dagTraceF m_71 s_71 8 f_71) (cur_71 0) s_71 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71 : treeBlockF 0 16 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 16 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
theorem nc_71 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 16 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := fun _ h1 h2 => treeBlockF_at nb_71 h1 h2
theorem lb_71 : LowerBin m_71 s_71 g_71 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_71 kn_71 sub_71 gl_71 rc_71 nc_71

def m_72 : Nat := 0x3333333333333333
def s_72 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_72 : Nat := 0x113131311131333
def ep_72 : Nat := 0x1000002000001200000002200012000000020020010202020002020000000000000000000110101011101000
theorem epk_72 : ep_72 = edgePack m_72 g_72 := by decide +kernel
def bds_72 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 6, g_32), (m_41, s_41, 5, g_41), (m_27, s_27, 5, g_27), (m_35, s_35, 5, g_35), (m_45, s_45, 5, g_45), (m_63, s_63, 5, g_63), (m_59, s_59, 5, g_59), (m_5, s_5, 4, g_5), (m_10, s_10, 4, g_10)]
theorem kn_72 : KnownBin bds_72 := by
  intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_41
  · exact lb_27
  · exact lb_35
  · exact lb_45
  · exact lb_63
  · exact lb_59
  · exact lb_5
  · exact lb_10
theorem sub_72 : ∀ b ∈ bds_72, m_72 &&& b.1 = b.1 := by intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_72 : ∀ b ∈ bds_72, canon b.1 g_72 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_72 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007187006a3643339038001 0x1c5e1c5d5a5e1a5d5a4e1a491a421a41815d395969553951192d3125885e485d485c28594855785228512850182d48253c5e3c5d625d1a596a551a51595e395d594e394939423941392a2126685e485d485c28594855685228512850381d48153a50395028501a50195028505b5e435a6b565b521a5a32563a3e1a3d395a2156193e193d192e3929192219211920483d28394835283128291821281928115a4f1a4b72471a43594f394b51473943192f392b11271923484f284b48472843182f282b48271823381f281b48172813001f 12 4095 5 31 11 2047 16 65535
def f_72 : Nat → Nat × Nat := unpackForestF 0x215d191da5d151cb5a2958956149c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV4 m_72 g_72 ep_72 9 bds_72 (dagTraceF m_72 s_72 7 f_72) (cur_72 0) s_72 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72 : treeBlockF 0 9 (dagCheckNodeV4 m_72 g_72 ep_72 bds_72 9 (dagTraceF m_72 s_72 7 f_72) cur_72) = true := by decide +kernel
theorem nc_72 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_72 g_72 ep_72 bds_72 9 (dagTraceF m_72 s_72 7 f_72) cur_72) i = true := fun _ h1 h2 => treeBlockF_at nb_72 h1 h2
theorem lb_72 : LowerBin m_72 s_72 g_72 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_72 kn_72 sub_72 gl_72 rc_72 nc_72

def m_73 : Nat := 0xcccccccccccccccc
def s_73 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_73 : Nat := 0x40444044444cc
def ep_73 : Nat := 0x440408800000440000040880004004000400088000404000400000000000000000000000004044404444400
theorem epk_73 : ep_73 = edgePack m_73 g_73 := by decide +kernel
def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 5, g_26), (m_33, s_33, 7, g_33), (m_40, s_40, 5, g_40), (m_46, s_46, 5, g_46), (m_7, s_7, 4, g_7), (m_60, s_60, 7, g_60), (m_42, s_42, 5, g_42), (m_34, s_34, 5, g_34), (m_50, s_50, 5, g_50), (m_67, s_67, 6, g_67)]
theorem kn_73 : KnownBin bds_73 := by
  intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_33
  · exact lb_40
  · exact lb_46
  · exact lb_7
  · exact lb_60
  · exact lb_42
  · exact lb_34
  · exact lb_50
  · exact lb_67
theorem sub_73 : ∀ b ∈ bds_73, m_73 &&& b.1 = b.1 := by intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_73 : ∀ b ∈ bds_73, canon b.1 g_73 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_73 : Nat → List (Nat × Nat) := unpackCursorV4 0x187cbb125cf52a4d5afdd26ee032e91587e9d9d44d41a700af48383f14ce856a001540001 0x1c5f5c5e1c5b1c571c531c523b5f5b5b3b575b531b4f1b4b1b471b435a5f5a5e5a5b4a5a5a574a565a535a521a4f1a4e1a4b1a4a1a471a461a431a422a3f2a3e2a3d595f595e295b595729535952194f194b19471943293b393a29393937393629332931392739263925585f585b58575853184f184b18471843683f383b38376833682f682d682b682788256823281f781b781728131c5f5c5e1c5b1c571c531c523b5f3b5e3b5b3b573b535b521b4f1b4b1b471b432a5f2a5b2a572a531a4f1a4b1a471a432a3f3a3e2a3d2a372a352a332a32295f595e295b295a2957495629532952194f194e194b194a1947194619431942293739362935292f292e292d585f585b58575853184f184b18471843383f383b38373833282f282b28272823281f281d281b2817881528131c5f5c5e1c5b1c571c531c523b5f3b5e3b5b4b5a3b573b563b535b521b4f1b4e1b4b1b4a1b471b461b431b423a5f3a5b3a573a531a4f1a4b1a471a432a3f2a3e2a3d595f295b59572953194f194b19471943393f393e693d392f392e292b2929292339222921c120585f585b58575853184f184b18471843383f883d383b383738353833382f382b38273823281f781b781728131b4f5b4e1b4b1b471b431b423a4f3a4e3a4b3a473a435a421a3f1a3b1a371a33294f294b29472943193f193d193b193729351933292f392e292d584f584b58475843183f183b18371833382f382b38273823281f281b281728131c5f5c5e1c5b1c571c531c523b5f5b5e5b5b3b575b535b521b4f1b4b1b471b432a5f5a5e2a5b2a572a532a521a4f1a4b1a471a432a3f2a3d2a3b2a3a2a373a362a35c234295f595e295b295a2957495629532952194f194e194d194c194b194a194719462945994419431942293f693e293d292f292e292d585f585b58575853184f184b18471843683f383b38376833282f282b28272823281f281d281b2817881528131c5f5c5e1c5b1c571c531c523b5f4b5b3b575b531b4f1b4b1b471b435a5f5a5e4a5b4a5a4a574a565a535a521a4f1a4e1a4b1a4a1a471a461a431a42595f495b49575953194f194b19471943693f393b39376933692f692d692b29296927792569232921485f585e48575852184f1847383a38373836382738263825881f88171c5f4c5e1c5b1c571c531c523b5f3b5e3b5b3b573b534b521b4f1b4b1b471b434a5f4a5b4a574a531a4f1a4b1a471a433a3f3a3b3a373a33393e485e4856184e18463836282e78261c5f5c5e1c5b1c571c531c523b5f3b5e3b5b4b5a3b573b563b535b521b4f1b4e1b4b1b4a1b471b461b431b423a5f3a5b3a573a531a4f1a4b1a471a43595f495b49575953194f194b19471943393f793d393b29393937393539332931392f392b39273923485f4857184f1847383f383e683d382f382e38227020881f88171b4f4b4e1b4b1b471b431b423a4f3a4e3a4b3a473a434a421a3f1a3b1a371a33494f494b49474943193f193b19371933392f392b39273923382e1c5f4c5e1c5b1c571c531c523b5f4b5e4b5b3b574b534b521b4f1b4b1b471b434a5f4a5b4a574a531a4f1a4b1a471a436a3f3a3b3a376a33495e39367134485e4856184e184c18469844683e282e78261c5f5c5e1c5b1c571c531c525b5f4b5b4b575b531b4f1b4b1b471b432a5f2a5b2a572a531a4f1a4b1a471a432a3f2a3b2a372a33295f595e295b295a2957495629532952194f194e194b194a1947194619431942293f693e293b293a2937393629332932485f585e48575852184f1847883f8837282a282728262817281678151c5f4c5e1c5b1c571c531c524b5f4b5b4b574b531b4f1b4b1b471b434a5f4a5e2a5b4a572a534a521a4f1a4b1a471a437a3f2a3b7a372a33292e485e4856184e1846683e383678261c5f5c5e1c5b1c571c531c525b5f4b5b4b575b531b4f1b4b1b471b435a5f5a5e4a5b4a5a4a574a565a535a521a4f1a4e1a4b1a4a1a471a461a431a427a3f6a3e7a3b3a3a7a373a367a336a32595f295b49572953194f194b19471943793f293b79372933485f4857184f1847883f8837282f282e282d281f281e281220101b4f4b4e1b4b1b471b431b424a4f4a4b4a474a431a3f1a3b1a371a33494f494e494b494749434942193f193b19371933792f792b79277923781e1c5f4c5e1c5b1c571c531c524b5f4b5b4b574b531b4f1b4b1b471b432a5f4a5e2a5b2a572a532a521a4f1a4b1a471a432a3f2a3b2a372a33495e29262124485e4856184e184c18469844683e3836282e1b4f5b4e1b4b1b471b431b425a4f5a4b5a475a431a3f1a3b1a371a33594f594b59475943193f193b19371933f12fe12bd127b123584f584b58475843183f183b18371833a02f902b80276023501f401b30171013001f 17 131071 7 127 11 2047 16 65535
def f_73 : Nat → Nat × Nat := unpackForestF 0x14bc52b149f234148c42f10ac42774d0423107c41b105c924104c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsV4 m_73 g_73 ep_73 16 bds_73 (dagTraceF m_73 s_73 8 f_73) (cur_73 0) s_73 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73 : treeBlockF 0 16 (dagCheckNodeV4 m_73 g_73 ep_73 bds_73 16 (dagTraceF m_73 s_73 8 f_73) cur_73) = true := by decide +kernel
theorem nc_73 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_73 g_73 ep_73 bds_73 16 (dagTraceF m_73 s_73 8 f_73) cur_73) i = true := fun _ h1 h2 => treeBlockF_at nb_73 h1 h2
theorem lb_73 : LowerBin m_73 s_73 g_73 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_73 kn_73 sub_73 gl_73 rc_73 nc_73

def m_74 : Nat := 0xff00ff00ff00ff
def s_74 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_74 : Nat := 0x170057005700ff
def ep_74 : Nat := 0x4000a800000040000000a80000000000000000000600020002000000120002000200000014005400540000
theorem epk_74 : ep_74 = edgePack m_74 g_74 := by decide +kernel
def bds_74 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_62, s_62, 5, g_62), (m_58, s_58, 5, g_58), (m_66, s_66, 5, g_66), (m_31, s_31, 5, g_31)]
theorem kn_74 : KnownBin bds_74 := by
  intro b hb; simp only [bds_74, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_3
  · exact lb_62
  · exact lb_58
  · exact lb_66
  · exact lb_31
theorem sub_74 : ∀ b ∈ bds_74, m_74 &&& b.1 = b.1 := by intro b hb; simp only [bds_74, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_74 : ∀ b ∈ bds_74, canon b.1 g_74 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_74, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_74_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xee0e64e41e21c30c20be2be0ba2a6aa60a60a608ae8a08a08a08a08248017e15f05e05e05e05e0564541521330038001 0x6930f922019243c04806d400d282135e406b40ed58e9a901b4e0369406d180da101a5a384ac069380d211b1560328c064f80c971925c034a05cd700da81034d0369260d140da08824d03492589140d20828560508c50d740dac82b55036a24c9740d2c82a55034a20a57890ae0285e0509c280d8101301a381c468344d00c1a01a50036a0411787a2d02c56188a406d6859ab01a4d03492069140d2081a3903462281580c270183e0304c069303122051240304806d400d280835e0e6b40ad5821a901b4e0369406d180da101a5a064ac069380d21020560308c060f80c174034f03696f0d1c0da1b724f03496cc91c0d2181a3f03476068dc0d19ae14f5428e064fd109b8192f3424e5413c88238183f1206e060bc08138001f 12 4095 5 31 11 2047 19 524287
def cc_74_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8004001938c80630b1818829d44e0270138065c3201808c005c224512009004801670b005802c016009104422010080000000000 0x71781c5d16d781b5d16d381b4906d081b41169781a5dfc9701a59069541a52069441a50069341a45068f41a35f85743955064f64135f41742855060f4b035ec133914c071781c5d06d741b5506d341b4906d141b41069681a59129581a51129181a45068f81a3284537a145201378045071781c5d12d781b5dd8d701b5906d541b5206d441b5006d341b45129781a5d129381a49069081a41068e81a36d45743955064b5c125d01742855060b43025c89701a50c0d701b50a4d341b49c4d141b41849341a49bc9141a410e5583946b4d741b590ed541b51b09741a590e9541a510e578394e8c4d9b1260e17ab05c068e27234064d26034069401b50a517a845a0f15a545206d6a4356069341a49069141a41068e41a318c558194e064f81926 13 8191 5 31 11 2047 18 262143
def cc_74_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xb02a1a828105000 0x220264214c038bc071740dad01b590b6ac06d442da301b45034ba069540d2681a490348a069040d1c81a315229b0c5148026c1045 10 1023 5 31 11 2047 19 524287
def cur_74 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_74_2 (Nat.sub p 64)) (cc_74_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_74_0 p) (Nat.blt p 32)
def f_74 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
set_option maxHeartbeats 0 in
theorem rc_74 : dagCheckRootsV4 m_74 g_74 ep_74 69 bds_74 (dagTraceF m_74 s_74 7 f_74) (cur_74 0) s_74 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_0 : treeBlockF 0 32 (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 69 (dagTraceF m_74 s_74 7 f_74) cur_74) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_1 : treeBlockF 32 64 (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 69 (dagTraceF m_74 s_74 7 f_74) cur_74) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_2 : treeBlockF 64 69 (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 69 (dagTraceF m_74 s_74 7 f_74) cur_74) = true := by decide +kernel
theorem nj_74_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 69 (dagTraceF m_74 s_74 7 f_74) cur_74) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_74_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_74_1 h1 h2)
theorem nj_74_2 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 69 (dagTraceF m_74 s_74 7 f_74) cur_74) i = true := block_join nj_74_1 (fun _ h1 h2 => treeBlockF_at nb_74_2 h1 h2)
theorem nc_74 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 69 (dagTraceF m_74 s_74 7 f_74) cur_74) i = true := nj_74_2
theorem lb_74 : LowerBin m_74 s_74 g_74 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_74 kn_74 sub_74 gl_74 rc_74 nc_74

def m_75 : Nat := 0xf0f0f0f0f0f0f0f
def s_75 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_75 : Nat := 0x10707070507070f
def ep_75 : Nat := 0x400000800000600000002080006000000020008000000000000000001020202000202000104040405040400
theorem epk_75 : ep_75 = edgePack m_75 g_75 := by decide +kernel
def bds_75 : List (Nat × List Nat × Nat × Nat) := [(m_67, s_67, 6, g_67), (m_56, s_56, 5, g_56), (m_25, s_25, 5, g_25), (m_44, s_44, 5, g_44), (m_49, s_49, 5, g_49), (m_64, s_64, 5, g_64), (m_57, s_57, 5, g_57), (m_6, s_6, 4, g_6), (m_11, s_11, 4, g_11)]
theorem kn_75 : KnownBin bds_75 := by
  intro b hb; simp only [bds_75, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_67
  · exact lb_56
  · exact lb_25
  · exact lb_44
  · exact lb_49
  · exact lb_64
  · exact lb_57
  · exact lb_6
  · exact lb_11
theorem sub_75 : ∀ b ∈ bds_75, m_75 &&& b.1 = b.1 := by intro b hb; simp only [bds_75, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_75 : ∀ b ∈ bds_75, canon b.1 g_75 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_75, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_75 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007187006a3643339038001 0x3c5e3c5d5a5e3a5d5a4e3a493a423a41815d195969551951392d3125885e485d485c28594855785228512850382d48251c5e1c5d625d3a596a553a51595e195d594e194919421941192a2126685e485d485c28594855685228512850181d48151a50195028503a50395028505b5e435a6b565b523a5a32561a3e1a3d195a2156393e193d392e1929192219211920483d28394835283128292821281918115a4f3a4b72473a43594f194b51471943392f192b11271923484f284b48472843382f282b48272823181f281b48171813001f 12 4095 5 31 11 2047 16 65535
def f_75 : Nat → Nat × Nat := unpackForestF 0x215d191da5d151cb5a2958956149c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_75 : dagCheckRootsV4 m_75 g_75 ep_75 9 bds_75 (dagTraceF m_75 s_75 7 f_75) (cur_75 0) s_75 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75 : treeBlockF 0 9 (dagCheckNodeV4 m_75 g_75 ep_75 bds_75 9 (dagTraceF m_75 s_75 7 f_75) cur_75) = true := by decide +kernel
theorem nc_75 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_75 g_75 ep_75 bds_75 9 (dagTraceF m_75 s_75 7 f_75) cur_75) i = true := fun _ h1 h2 => treeBlockF_at nb_75 h1 h2
theorem lb_75 : LowerBin m_75 s_75 g_75 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_75 kn_75 sub_75 gl_75 rc_75 nc_75

def m_76 : Nat := 0xffff0000ffff
def s_76 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_76 : Nat := 0x1757000057ff
def ep_76 : Nat := 0x40a8000000000000000000000040000000a8000006020000020000001202000002000000145400005400
theorem epk_76 : ep_76 = edgePack m_76 g_76 := by decide +kernel
def bds_76 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_14, s_14, 4, g_14), (m_61, s_61, 5, g_61), (m_65, s_65, 5, g_65), (m_30, s_30, 5, g_30), (m_68, s_68, 5, g_68)]
theorem kn_76 : KnownBin bds_76 := by
  intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_14
  · exact lb_61
  · exact lb_65
  · exact lb_30
  · exact lb_68
theorem sub_76 : ∀ b ∈ bds_76, m_76 &&& b.1 = b.1 := by intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_76 : ∀ b ∈ bds_76, canon b.1 g_76 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_76_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xee0e64e41e21c30c20be2be0ba2a6aa60a60a608ae8a08a08a08a08248017e15f05e05e05e05e0564541521330038001 0x6930f922019243c04806d400d282135e406b40ed58e9a901b4e0369406d180da101a5a384ac069380d211b1560328c064f80c971925c034a05cd700da81034d0369260d140da08824d03492589140d20828560508c50d740dac82b55036a24c9740d2c82a55034a20a57890ae0285e0509c280d8101301a381c468344d00c1a01a50036a0411787a2d02c56188a406d6859ab01a4d03492069140d2081a3903462281580c270183e0304c069303122051240304806d400d280835e0e6b40ad5821a901b4e0369406d180da101a5a064ac069380d21020560308c060f80c174034f03696f0d1c0da1b724f03496cc91c0d2181a3f03476068dc0d19ae14f5428e064fd109b8192f3424e5413c88238183f1206e060bc08138001f 12 4095 5 31 11 2047 19 524287
def cc_76_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8004001938c80630b1818829d44e0270138065c3201808c005c224512009004801670b005802c016009104422010080000000000 0x71781c5d12d781b5d12d381b4906d081b41129781a5dfc9701a59069541a52069441a50069341a45068f41a35f85744955064f64135f41742855060f4b035ec133914c071781c5d06d741b5506d341b4906d141b41069681a590e9581a510e9181a45068f81a3284537a145201378045071781c5d0ed781b5dd8d701b5906d541b5206d441b5006d341b450e9781a5d0e9381a49069081a41068e81a36d45743955064b5c125d01742855060b43025c89701a50c0d701b50a4d341b49c4d141b41849341a49bc9141a41165585946b4d741b5912d541b51b09741a590e9541a5116578594e8c4d9b1261617ab05c068e27234064d26034069401b50a517a845a1315a545206d6a4356069341a49069141a41068e41a318c558194e064f81926 13 8191 5 31 11 2047 18 262143
def cc_76_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xb02a1a828105000 0x220264214c038bc071740dad01b59096ac06d4425a301b45034ba069540d2681a490348a069040d1c81a315229b0c5148026c1045 10 1023 5 31 11 2047 19 524287
def cur_76 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_76_2 (Nat.sub p 64)) (cc_76_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_76_0 p) (Nat.blt p 32)
def f_76 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
set_option maxHeartbeats 0 in
theorem rc_76 : dagCheckRootsV4 m_76 g_76 ep_76 69 bds_76 (dagTraceF m_76 s_76 7 f_76) (cur_76 0) s_76 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_76_0 : treeBlockF 0 32 (dagCheckNodeV4 m_76 g_76 ep_76 bds_76 69 (dagTraceF m_76 s_76 7 f_76) cur_76) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_76_1 : treeBlockF 32 64 (dagCheckNodeV4 m_76 g_76 ep_76 bds_76 69 (dagTraceF m_76 s_76 7 f_76) cur_76) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_76_2 : treeBlockF 64 69 (dagCheckNodeV4 m_76 g_76 ep_76 bds_76 69 (dagTraceF m_76 s_76 7 f_76) cur_76) = true := by decide +kernel
theorem nj_76_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_76 g_76 ep_76 bds_76 69 (dagTraceF m_76 s_76 7 f_76) cur_76) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_76_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_76_1 h1 h2)
theorem nj_76_2 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_76 g_76 ep_76 bds_76 69 (dagTraceF m_76 s_76 7 f_76) cur_76) i = true := block_join nj_76_1 (fun _ h1 h2 => treeBlockF_at nb_76_2 h1 h2)
theorem nc_76 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_76 g_76 ep_76 bds_76 69 (dagTraceF m_76 s_76 7 f_76) cur_76) i = true := nj_76_2
theorem lb_76 : LowerBin m_76 s_76 g_76 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_76 kn_76 sub_76 gl_76 rc_76 nc_76

def g_77 : Nat := 0x1171757155757ff
def ep_77 : Nat := 0x144040a800001640000042a800160040004200a8010606020402020001121202100202000114145415545400
theorem epk_77 : ep_77 = edgePack fullMask g_77 := by decide +kernel
def bds_77 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_74, s_74, 8, g_74), (m_75, s_75, 8, g_75), (m_76, s_76, 8, g_76), (m_72, s_72, 8, g_72), (m_69, s_69, 9, g_69), (m_70, s_70, 9, g_70), (m_71, s_71, 9, g_71), (m_73, s_73, 9, g_73), (m_51, s_51, 5, g_51), (m_29, s_29, 7, g_29), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10), (m_47, s_47, 6, g_47), (m_36, s_36, 7, g_36), (m_21, s_21, 7, g_21), (m_13, s_13, 4, g_13), (m_33, s_33, 7, g_33), (m_60, s_60, 7, g_60), (m_28, s_28, 7, g_28), (m_16, s_16, 4, g_16), (m_20, s_20, 4, g_20), (m_37, s_37, 7, g_37)]
theorem kn_77 : KnownBin bds_77 := by
  intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_22
  · exact lb_74
  · exact lb_75
  · exact lb_76
  · exact lb_72
  · exact lb_69
  · exact lb_70
  · exact lb_71
  · exact lb_73
  · exact lb_51
  · exact lb_29
  · exact lb_11
  · exact lb_10
  · exact lb_47
  · exact lb_36
  · exact lb_21
  · exact lb_13
  · exact lb_33
  · exact lb_60
  · exact lb_28
  · exact lb_16
  · exact lb_20
  · exact lb_37
theorem sub_77 : ∀ b ∈ bds_77, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_77 : ∀ b ∈ bds_77, canon b.1 g_77 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_77_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x7b0baf0ea5cea6b784a6b27cd248185fdace7b522f498d711aae2075c3c69070efcd6d618dc02ef5855f00a3909283e230403e2fc6c9f8ba3e1377a1f4f42f5e84ea005e7e07a84005e00001 0x2267f05e7b05e7708e7302d7f02d7e02d7b05d7a02d7702d7602d732057202d6f02d6e02d6b04d6a02d6702d6602d6308d6202c7f02c7b02c7702c7302c6f02c6b02c6702c6301b7f01b7e01b7b05b7a01b7701b7601b7309b7201b6f01b6e01b6b04b6a01b6701b6601b6308b6201b5f01b5e01b5d01b5c01b5b02b5a01b5902b5801b5701b5601b5501b5401b5302b5201b511f35001b4f01b4e01b4b02b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a430193e0192e0d8660285e0284e04d6f04d6b04d6704d6302c6f02c6b02c6702c6302c5f02c5e02c5b02c5702c5304c5202b6f02b6b02b6702b6302b5f02b5b02b5702b530aa6f05a6b05a6706a6304a5f04a5b04a5704a5302a4f02a4b02a4702a4302a3f02a3b02a3702a33048560284e0283e04d6f04d6b04d6704d6304c6f04c6b04c6704c6302b6f02b6b02b6702b6302b5f02b5e02b5b02b5902b5702b5304b5202b5107b5002b4f02b4e02b4b02b4902b4702b4304b4202b4102a6f02a6b02a6702a6302a5f02a5e02a5b02a5902a5702a5304a5202a5102a4f02a4b02a4702a430996f0596b05967069630495f0495b04957049530494f0494b04947049430293f0293b02937029330292f0292b02927029230986f058670485f048570484f048470283f028370282f028270681f0d8172d56f05d6b05d6708d6302c6f02c6e02c6b05c6a02c6702c6602c632946202c5f02c5e02c5b04c5a02c5702c5602c5308c5202b6f02b6b02b6702b6302b5f02b5b02b5702b532826f05a6b05a6706a6308a5f06a5b2625706a5302a4f01a4d02a4b02a4902a4701a4502a4306a4102a3f02a3b02a3702a332516f059670895f231570294f0394d02947029450293f029370692f1e1270a86f058670885f1d05a0d8571c0560284f0284e0784d0283f0283e028320682f0d82702e7f02e7e02e7b05e7a02e7702e7602e730ae7204d7f04d7b04d7704d7302d6f02d6e04d6d02c7f02c7b02c7702c7302c6f02c6e02c6d02c5f02c5e02c5b02c5902c5304c5202c5107c5001b7f01b7b01b7701b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4b01b4701b430193e0a87e058760286e0d86c02866028640485e048560284e02846018360ad6f05d6b05d6708d630ac6f05c6b05c6707c6308c5f07c5b1a45707c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b430193e0a86e058660885e048560784e028460183604e7f05e7e04e7d04d7b05d7a04d7904d7704d7604d7304d7104d6704d6604d6505c7f05c7b05c7705c7304c6f02c6d04c6b07c6904c6702c6504c6304c6104c5f04c5b04c5904c5704c5307c5101b7f01b7e01b7b05b7a01b7701b7601b7305b7201b6f01b6e01b6d01b6c01b6b04b6a01b690fb6801b6701b6601b6501b6401b6304b6201b6104b6001b5f01b5e01b5b04b5a01b5701b5601b5304b5201b4f01b4e01b4b02b4a01b4701b4601b4307b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430597f059770496f0396d04967039650495f049570794f0b9470193f0393d01937019350192f019270587f058770486f0486d04867098650485f048570784f098470183f0183e0683d0182f0182e0182202e7f05e7e02e7d05d7f05d7b05d7705d7302d6f02d6d02d6b08d6902d6704d6502d6302d6102c7b05c7a02c7902c7702c7602c7302c7102c6702c6602c6502c5f02c5e02c5b02c5702c5307c5201b7f01b7e01b7b05b7a01b7701b7601b7305b7201b6f01b6e01b6d01b6c01b6b02b6a01b690fb6801b6701b6601b6501b6401b6302b6201b6102b6001b5f01b5e01b5b04b5a01b5701b5601b5308b5201b4f01b4e01b4b02b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430597f059770296f0296d02967039650895f0c9570294f029470193f0393d01937019350192f019270587f058770286f0286d02867098650885f098570284f028470183f0183e0683d0182f0182e0182202e7f02e7e02e7b05e7a02e7702e7602e7309e7204d7f04d7b04d7704d7302d6f02d6e04d6d02c7f02c7b02c7702c7302c6f02c6e02c6d02c5f02c5e02c5b02c5902c5304c5202c5107c5001b7f01b7e01b7b05b7a01b7701b7601b730bb7201b6f01b6e01b6d01b6c01b6b02b6a01b6902b6801b6701b6601b6501b6401b6302b6201b610fb6001b5f01b5e01b5b04b5a01b5701b5601b5304b5201b4f01b4e01b4b02b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430b97f059770296f0396d02967029650495f049570294f029470193f0393d01937019350192f019270a87f058770286f0986d02867028650485f048570284f028470183f0183e0683d0182f0182e0182205d7f05d7b05d7705d7303d6f03d6d03d6b08d6903d6704d6503d6303d6105c7f05c7b05c7705c7303c6f02c6d03c6b07c6903c6702c6503c6303c6108c5f07c5b0bc5707c5301b7f01b7e01b7b05b7a01b7701b7601b7305b7201b6f01b6e01b6d01b6c01b6b03b6a01b690eb6801b6701b6601b6501b6401b6303b6201b6103b6001b5f01b5e01b5b04b5a01b5701b5601b5308b5201b4f01b4e01b4b02b4a01b4701b4601b4307b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4303976039660183e0182e03e7f03e7e03e7b05e7a03e7703e7603e7309e7204d7f04d7b04d7704d730cc7f05c7b05c7707c7303c6f02c6d03c6b03c6903c6702c6503c6307c6104c5f04c5b04c5704c5301b7f01b7e01b7b05b7a01b7701b7601b730cb7201b6f01b6e01b6d01b6c01b6b03b6a01b6903b6801b6701b6601b6501b6401b6303b6201b610fb6001b5f01b5e01b5b04b5a01b5701b5601b5304b5201b4f01b4e01b4b02b4a01b4701b4601b4307b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430396e0395e0183e0182e0be7f05e7b05e7708e7302d7f02d7e02d7b05d7a02d7702d7602d7309d7202d6f02d6e02d6b04d6a02d6702d6602d6308d6202c7f02c7b02c7702c7302c6f02c6b02c6702c6301b7f01b7e01b7b05b7a01b7701b7601b730bb7201b6f01b6e01b6b04b6a01b6701b6601b6308b6201b5f01b5e01b5d01b5c01b5b02b5a01b5902b5801b5701b5601b5501b5401b5302b5201b510fb5001b4f01b4e01b4b02b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a430295e0294e0183e0182e1856f05d6b05d6708d631746f05c6b05c6707c6308c5f07c5b1645707c5301b6f01b6e01b6b05b6a01b6701b6601b630fb6201b5f01b5e01b5b04b5a01b5701b5601b5308b5201b4f01b4e01b4b02b4a01b4701b4601b4307b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a431516f059670895f141570794f131470193f0393d01937019350192f019270a86f058670885f0d8570784f0d8470183f0183e0683d0182f0182e0182202e7f02e7e02e7b05e7a02e7702e7602e7309e7204d7f04d7b04d7704d7302d6f02d6e04d6d02c7f02c7b02c7702c7302c6f02c6e02c6d02c5f02c5e02c5b02c5902c5304c5202c5107c500bb7f05b7b05b7706b7302b6f01b6d02b6b02b6902b6701b6502b6306b6104b5f04b5b04b5704b5302b4f02b4b02b4702b430b97e059760296e1196c02966029640495e049560294e029460693e019360b87e0cd6f09d6e05d6b05d6a05d6705d660cd6309d6204c6f04c6b04c6704c6304c5f04c5d0cb6f05b6b05b6707b630cb5f02b5d07b5b07b590cb5702b5507b5307b5104b4f04b4b04b4704b4301a6f01a6b01a6701a6301a5f01a5d01a4f01a4b01a4301a3f01a3b01a3701a330c86e01e7f01e7e01e7b05e7a01e7701e7601e7309e7204d7f04d7b04d7704d7301d6f01d6e04d6d0cc7f05c7b05c7707c7301c6f02c6d01c6b01c6901c6701c6501c6307c6104c5f04c5b04c5704c5301b7f01b7b01b7701b7301b6f01b6e01b6d01b5f01b5e01b5b01b5901b5304b5201b5101b4f01b4b01b4701b430c97e059760196e1016c01966019640495e049560794e029460193e0693c01936019340c87e0bd6f05d6b05d6708d630bc6f09c6e05c6b05c6a05c6705c660bc6309c6208c5f08c5e0bc5b04c5a0bc5704c5608c5308c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4f02b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a3f01a3b01a330b86e0be7f05e7b05e7708e7301d7f01d7e01d7b05d7a01d7701d7601d7309d7201d6f01d6e01d6b04d6a01d6701d6601d6308d6202c7f02c7b02c7702c7302c6f02c6b02c6702c6301c5f01c5e02c5d01b7f01b7b01b7701b7301b6f01b6b01b6701b6301b5f01b5e01b5d01b4f01b4e01b4b01b4901b4302b4201b410b97e059760896e049660195e0e15c01956019540294e029460193e0693c01936019340b87e0ed6f05d6b05d6708d630ec6f05c6b05c6707c6308c5f07c5b1145707c530eb6f05b6b05b6706b6308b5f06b5b0f35706b5307b4f06b4b0d34706b430e96e059660895e049560794e029460693e019360e86e02e7f02e7e02e7b05e7a02e7702e7602e730ae7204d7f04d7b04d7704d7302d6f02d6e04d6d02c7f02c7b02c7702c7302c6f02c6e02c6d02c5f02c5e02c5b02c5902c5304c5202c5107c500ab7f05b7b05b7706b7302b6f01b6d02b6b02b6902b6701b6502b6306b6104b5f04b5b04b5704b5302b4f02b4b02b4702b430a87e058760286e1186c02866028640485e048560284e028460683e018360ad6f05d6b05d6708d630ac6f05c6b05c6707c6308c5f07c5b0b45707c530ab6f05b6b05b6706b6308b5f06b5b0fb5706b5307b4f06b4b0fb4706b430a86e058660885e048560784e028460683e0183604e7f05e7e04e7d04d7b05d7a04d7904d7704d7604d7304d7104d6704d6604d6505c7f05c7b05c7705c7304c6f02c6d04c6b07c6904c6702c6504c6304c6104c5f04c5b04c5904c5704c5307c5105b7f05b7b05b7705b7304b6f01b6d04b6b06b6904b6701b6504b6304b6104b5f04b5b04b5704b5307b4f06b4b0bb4706b4303a7e03a7603a6e03a6c03a6603a6403a5e03a5603a4e02a4603a3e01a3602e7f05e7e02e7d05d7f05d7b05d7705d7302d6f02d6d02d6b08d6902d6704d6502d6302d6102c7b05c7a02c7902c7702c7602c7302c7102c6702c6602c6502c5f02c5e02c5b02c5702c5307c5205b7f05b7b05b7705b7302b6f01b6d02b6b06b6902b6701b6502b6302b6108b5f06b5b0cb5706b5302b4f02b4b02b4702b4303a7e03a7602a6e02a6c02a6603a6403a5e03a5602a4e02a4603a3e01a3602e7f02e7e02e7b05e7a02e7702e7602e7309e7204d7f04d7b04d7704d7302d6f02d6e04d6d02c7f02c7b02c7702c7302c6f02c6e02c6d02c5f02c5e02c5b02c5902c5304c5202c5107c500bb7f05b7b05b7706b7302b6f01b6d02b6b02b6902b6701b6502b6306b6104b5f04b5b04b5704b5302b4f02b4b02b4702b4303a7e03a7602a6e03a6c02a6602a6403a5e03a5602a4e02a4603a3e01a3601e7f05e7e01e7d05d7f05d7b05d7705d7301d6f01d6d01d6b08d6901d6704d6501d6301d6105c7f05c7b05c7705c7301c6f01c6d01c6b07c6901c6702c6501c6301c6108c5f07c5b0bc5707c5301b7b05b7a01b7901b7701b7601b7301b7101b6701b6601b6501b5f01b5b01b5701b5301b4f01b4b01b4701b4303a7e03a7601a6e01a6c01a6603a6403a5e03a5603a4e02a4601a3e01a3601e7f01e7e01e7b05e7a01e7701e7601e7309e7204d7f04d7b04d7704d7301d6f01d6e04d6d0cc7f05c7b05c7707c7301c6f02c6d01c6b01c6901c6701c6501c6307c6104c5f04c5b04c5704c5301b7f01b7b01b7701b7301b6f01b6e01b6d01b5f01b5e01b5b01b5901b5304b5201b5101b4f01b4b01b4701b4303a7e03a7601a6e03a6c01a6601a6403a5e03a5603a4e02a4601a3e01a360be7f05e7b05e7708e7301d7f01d7e01d7b05d7a01d7701d7601d7309d7201d6f01d6e01d6b04d6a01d6701d6601d6308d6202c7f02c7b02c7702c7302c6f02c6b02c6702c6301c5f01c5e02c5d01b7f01b7b01b7701b7301b6f01b6b01b6701b6301b5f01b5e01b5d01b4f01b4e01b4b01b4901b4302b4201b4103a7e03a7603a6e03a6601a5e03a5c01a5601a5402a4e02a4601a3e01a360956f05d6b05d6708d630846f05c6b05c6707c6308c5f07c5b0745707c530636f05b6b05b6706b6308b5f06b5b0535706b5307b4f06b4b0434706b4303a6e03a6603a5e03a5603a4e02a4603a3e01a3602e7f02e7e02e7b05e7a02e7702e7602e730ae7204d7f04d7b04d7704d7302d6f02d6e04d6d02c7f02c7b02c7702c7302c6f02c6e02c6d02c5f02c5e02c5b02c5902c5304c5202c5107c500ab7f05b7b05b7706b7302b6f01b6d02b6b02b6902b6701b6502b6306b6104b5f04b5b04b5704b5302b4f02b4b02b4702b430a97e0a87e058760286e1186c02866028640485e048560284e028460683e018360ad6f05d6b05d6708d630ac6f05c6b05c6707c6308c5f07c5b0245707c530ab6f05b6b05b6706b6308b5f06b5b0fb5706b5307b4f06b4b0fb4706b430a96e0a86e058660885e048560784e028460683e018368945f05c5b05c5708c538835f05b5b05b5707b5308b4f07b4b8734707b438525f05a5b05a5706a5308a4f06a4b7f24706a4307a3f06a3b7923706a337515f0595b059576f1530894f6c14b63147089430793f6013b57137079330692f5512b4e127069234405f0585b05857420530884f4104b30047088430783f2e03b1b037078330682f1902b12027068230c01f0a01b03017010130003f 19 524287 7 127 11 2047 20 1048575
def cc_77_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8251f7d94c758816d97f68a4f60f7b5b05f5842c5275d524034f3314e3104b82b45b5d4114a3e8293c721346813103630b052ec1f2a04c2217f1d24f1577b0f85f0cc2c06f5d05f1005c0302b310002b 0x9cfa139d41ebf03d6e098fc131f4263702b5d076b20ad543da889b4d0f6922ed143da081a5d074b206954352889a4d0d492fc91435208397e072bc0e5381ca6039360724c0e1784c2e04d6f09ada135ac26b384d6509ac6131bc263704c6d098be13178262b84c53098a416dbc2db585b670b6c612d7c25ad84b57096a626d3c15a687b4b0f6922ed1c15a287b430f682169bc2d3585a670b4c61297c252d84a57094a62693c0d2686a4b0d4930091c0d2286a430d4821e8fc351d8ba370d466165bc2cb38495f092ae2653c1ca6be1470728a1e4fc5c9b8692f6824e161bc5436858670b0ca1217c242b8884f1109a1611c2c228783f1306e1a0bc4c1382e7f0bcfc0b9f426bf84d7e09af6175e826bb84d7609ae6175c816b782d6e05ada0b5b016b582d6a09ad24f5a016b382d6609aca1359016b182d6205ac20b580263f84c7b098ee131cc163782c6d058d6131a4163384c65058c60b18415bd85b7a056f20addc15bb02b73056e20ad9c15b302b65056be0ad7815ae82b5c056b60ad6415ab82b55056a612d4815a887b500569e0ad3815a582b470568612d082d3f85a7b0b4ee169cc153781a6d054d61a9a4153381a65054c60a984252f81a5d094b612964252b81a55094a61a944252784a4b0948e1290c151f82a3b0546e0a8cc2cbf85977052de0a5b414b383965092be0e57424ab839550929e1251c149f829370d25ecc49c2c3f85877050de0a1b4143389865090be12178442e8484f0909c12108141f8283a0506e0a0d834178982703cfe179f80f3e84d7f09afc135ec2ebd04d7709aec135cc2eb901d6f03adc075b40eb601d6b03ad4135a4b6b401d6703acc1359426b201d6303ac4075840eb004c7f098f6131dc263981c6f038da071ac263481c67098ca0718c0e3085b7f0b6f616ddc2db981b6f036da06dac3db481b67056ca06d8c0db084b5f056ba12d6c25ac84b57056aa12d4c3da884b4f0969612d1c25a181a7b0b4f4069e40d3b81a76034e6069c40d3381a66034ca0697c0d2f01a5d034b80696c0d2c81a57034aa0694c252901a510d4a00693c0d2581a4703486068fc0d1d81a3703466165fc2cbb8196f032da0659c1cb28495f072ba1255c1caa8494f0928e1e4fc5c9b8192f0324e161fc2c3b8186f030da0619c4c328485f090bc2217424278484e090841e0fc541d098371306c060bc0c1384d6f09ad61359c26b182c6f058d60b19c163182c5f058b60b15c16298bb6f136dc16dac2db505b670b6cc2ed8c4db101b5f036bc06d5c0da981b520569e0ad3815a582b4a0568e0ad1815a182b42034de069ac0d3381a63034be0696c0d2b81a530349e0692c0d2381a430347e068f40d1d81a390346e068d40d1981a31172de1659c24af849570529e0a51c5c9f8393d1726e0e4d40c9781927150de1619c242f818570509e0a1281423828461107e220f40c1b818350305e0609c273f84e7e09cf6179e8273b84e7609ce62f9c826bf84d7b09aee135cc0e3f81c7e038f6171e80e3b81c76038e6271c80e3781c6e038da071b00e3584c6a038d2131a00e3381c66038ca071900e3184c62038c2e91800e2f81c5e038b6131680e2b81c56038a61314815bf82b7b056ee0adcc15b782b6d056d60ada415b382b65056c60ad8415af82b5b056ae0ad4c0da781b4e0569a069fc0d3d81a77034e6069bc0d3681a6b034d20699c0d3281a63034c20697c0d2d81a57034a60693c0d2701a4d0347e068f80d1d81a39034660a8c80d188b97f0b2ee125bc1cb684967072ca1257c24ab8194f0729a0651c0ca28293f0526e064bc0c938a87f0b0ee121bc24370886d090be1217824290184f1309a0611c0c228283f050740a0dc141b0182f0304e135fc26bf04d7b0baf4135dc26bb04d730bae40f5bc1eb703d6d07ad80f5ac1eb504d691dad00f59c1eb304d6509ac80f58c1eb103d6107ac0131fc263d84c77098e60f1bc1e3683c6b098d20f19c263283c63078c216dfc2dbd85b770b6e60edbc15b683b6b0f6d20ed9c15b283b63076c212d7c15ae84b5b096b212d5c15aa84b530f6a212d3c25a584b4709686169fc2d3d85a770b4e60e9bc0d3683a6b0d4d20e99c0d3283a63074c21297c0d2e84a5b094b21295c0d2a84a530d4a21293c252584a47094861e8fc351d8ba370d4660e5d81cb30395e072b81217824270983609ade135ac26b384d63058de0b1ac163382c63058be0b16c162b8bb6f136dc16dac2db505b670b6cc2ed8c4db102b5f056bc0ad3c15a70ba6f0b4d61699c353184a5f094b61295c252982a4f054960a91c15218ba3f0347a1a8ec351c8ba370346a1a8cc35188284609cfe139f8273d85e7a09cee139d827398be7209afe135ec26bb84d73058fe0b1f8163d85c7a058ee0b1d8163989c72058de0b1b8163682c6c058d6131a8163484c68058ce0b198163282c64058c6131881630b7460058be0b178162d84c5a058ae0b158162984c52056fe0adec15bb82b73056de0adb415b582b69056ce0ad9415b182b61056be0ad6c15ab82b53174fe169ec2d3b86a73094de069b4253584a69094ce06994253186a61094be1296c252b84a530549e06934152582a490548e06914152186a410547e0a8ec151b82a330529c0a4f824370485e0506c069e0253801a5409cfa139d426bf04d7d09adc0b1743e2c82c550f8a206df82dbd01b790b6f006dd82db901b71136e006db825b501b66096c406d780dae81b5c6a6b406d6485ac01b56036aa06d504da901b51136a006d3815a501b460f68406974352d01a590d4b0069580d2a81a54034a20e5581caa0193e0325c0b9f09f3c04e7405ce00b1b03e3001b7c276f006dd015b801b6c096d006d9085b002b480f680135bc26b584d6709ac6431bc2e3585c670f8c61317c262d84c57098a606dbc0db581b67036c606d7c0dad81b570369e06d2c0da381b43214de269b82d3585a6a0b4ce16998853189a62034be069783d2787a4e214960a928852382a460f4861e9080d1f81a3e09cfe139f8273d85e7a09cee139d82739b467209afe135ec26bb84d73668fe171ec2e3b87c73098de0b1b4263584c69098ce0b194263187c61098be1316c262b84c53036fe06df80dbd85b7a036ee06dd80db989b72036de06db80db681b6c036d612da80db484b68036ce06d980db281b64036c612d880db0b2360036be06d780dad84b5a036ae06d580da984b520369e06d380da582b4a0368e06d180da187b42034fe069ec0d3b81a73034de069b40d3581a69034ce069940d3181a61034be0696c0d2b81a530349e0692c0d2381a430327c064b824370485e1b08c135bc26b704d6b0bad41359c26b304d637aac4131bc263584c67098c6f0dbc2db585b670f6c612d7c15ae84b5b096b212d5c15aa84b530f6a212d3c25a584b4709686ec9bc2d3585a670d4c61297c0d2e84a5b094b21295c0d2a84a530d4a21293c252584a47094861e8fc351db92370d466e05bc2cb38495f072ba1255c1caa8494f0928e1e4fdb09b8692f6224e2a1bc2c338485f090bc2217424278484e090841e0fd781d0d8373806c1a0bc6c1384d6f09ad61359c26b184c6f098d61319c263182b6f056d60ad9c15b182b5f056b60ad6415ab82b53056a20ad3c15a582b47056862a9bc2d3585a670d4c61297c252d84a57094a61293c252584a47094860a8fc151d82a37054661217824270283615ade175ac2eb388d63058de0b1ac163382c63058be0b16c162b82c53156de16dac2db386b63116be1ad6c7dab86b530569e0ad2c15a382b435e2ac0a538543705866110bc1215814230683e0306c139fc2f3f04e7d09af6175e826bc84d7709aec135cc26b884d6709acc13594163f82c7e058f6171e8163b82c76058e6171c8163782c6e058da0b1b0163584c6a058d24b1a0163382c66058ca0b190163184c62058c213180162f82c5e058b613168162c84c58058ae0b158162984c52058a22314015bf82b7b056ee0adcc15b782b6d056d60ada415b382b65056c60ad8415af82b5b056b20ad5c15a982b510b4fe169ec2d3b85a73094de069b4253586a69094ce06994253184a61094be1296c252b84a530549e06934152582a490548e06914152186a410547e0a8ec151b82a330b2fe165dc24b78396d092ce0e59424af849570529e0e53414a3829450527e0a4dc3497a21270b0fe161dc24378486d090ce26194242f8485a090ae1215814278284e0f09a0a0fc141f028320d05e2609c16be82d75038fc171e80e3b02c72038dc131a80e3308c62038bc0b1680e2b02c52056fc0adf445b709b6a196cc22d8815af02b56056a406d3835a686b4c034fc169c8353501a660349c069340d1f01a3d03478068e4351901a310d4600e5340ca28993d5626a1a4b40c928987d0b0ea061384c268984c0308a061083c1e8583507698068f035180394c032480b5f416ba82c7e078dc131a81e3308c62058bc0adf815be88b6e136d432d9845b102b5e0349a0e9240d2286a411347a1a8e5591a86a31072fc0e5981ca70393e072780e4981c270984c0bade175ac2eb385d63058de0b1b4163582c67058ca0b18c162f82c5b058ae0b14c15b782b6e056da22d7c45af09b5b096b432d5c25ab08b53116a40ad3c15a702b47056860ad082d3785a6b0b4ce1698c452f86a5b194ae1a94c152782a4b0548e0a90c4d1f81a3d0d4761a8e5611b81a350d4661a8c42cb785967112be3255c14a7829471327e0e4f5509b839350d25e8049c2c378a86d0b0ce16194442f898570509e0a11c3c1f8783d0b06e160d434178982703cfe179f80f3e85d7f0baf6175dc2eb981d6f03ada075ac46b481d6709aca0758c0eb082c7f058fc0b1ec2e3d02c77058ec0b1cc2e3901c6f038dc071b40e3601c6b038d40b1a4b63401c67038cc0b194163201c63038c4071840e3002c5f058bc0b16c262d02c57058ac0b14c462902b7f056f60addc15b981b6f036da06dac15b481b67056ca06d8c0db082b5f056b60ad5c15a981a7b0b4f4069e40d3b81a76034e6069c40d3381a66034ca0697c0d2d81a57034a60693c0d2701a4d034980692c0d2481a470348a0690c152101a410d480068fc0d1d81a3703466165fc2cbb8196f032da0659c1cb28895f192ae0a53c1ca6829470528a0a4fc149b8192f0324e161fc2c3b8186f030da0619c4c328885f150b42615c4c2b0284f0509c1e134141f8283e05064060bc0c1384d6f09ad61359c26b182c6f058d60b19c163182c5f058b60b15c16298cb6f136dc16dac2db505b670b6cc32d8c4db102b5f056bc12d6c25ad02b57056ac0ad4c15a901b4f0369c06d1c0da181b42034de069ac0d3381a63034be0696c0d2b81a530349e0692c0d2381a430347e068f40d1d81a390346e068d40d1981a31192de1659c24af849570529e0a51c649f8393d1926e0e4d40c9781927150de1619c242f8485a090ae121581427818470f07e1e0f40c1b818350305e0609c0f3f81e7e03cf6179e80f3b81e7603ce6279c826bf84d7b09aee135cc0eb781d6e09ada0b1fc163f02c7b0b8f40b1dc163b02c73198e4071bc0e3702c6d058d8071ac0e3501c69038d00719c0e3301c65038c80718c0e3102c614e8c00b17c162f02c5b098b40b15c162b02c53098a40adfc15bd82b77056e606dbc15b681b6b036d206d9c0db281b63056c20ad7c15ad82b57056a6069fc0d3d81a77034e6069bc0d3701a6d034be069780d2d81a59034a6129480d2881a4f0349a0692c0d2481a470348a0690c0d2081a3f03476068dc0d198c97f0b2ee065bc1cb681967032ca1257c24ab8294f0729a0a51c14a28293f0526e064bc0c938a87f0b0ee061bc4c3681867030ca1217c242d04857090ac0a13c14270784d0507e0a0f814190182f0304e175fc2ebd85d770bae60f5bc1eb683d6b11ad20f59c26b283d6307ac20b1fc163f02c7b0b8f40b1dc163b02c730b8e40b1bc163702c6d058d80b1ac1e3502c691d8d00b19c163302c65058c80b18c1e3102c61078c00b17c162f02c5b098b40b15c162b02c53118a40adfc15bd82b77056e60adbc15b682b6b056d20ad9c15b282b63056c20ad7c15ad82b57056a6169fc2d3d85a770b4e60e9bc0d3683a6b0d4d20e99c0d3283a63074c22297c352d8ca570d4a60a93c0d2682a4b054920a91c0d2282a430d4820a8fc151d82a37054660e5d81cb30294e072982615814270283e09ade135ac26b384d63058de0b1ac163382c63058be0b16c162b8cb6f136dc16dac2db505b670b6cc32d8c4db102b5f056bc0ad3c15a70ca6f0b4d61699c353184a5f094b61295c252982a4f054960a91c15218ca3f0347a1a8ec351c8ca370346a1a8cc35188485607cfe0f9f81f3d85e7a07cee0f9d81f3989e7209afe135ec26bb84d73058fe0b1f8163d85c7a058ee0b1d816398cc72058de0b1b8163682c6c058d60f1a8163483c68058ce0b198163282c64058c60f1881630a4460058be0b178162d84c5a058ae0b158162984c52056fe0adec15bb82b73056de0adb415b582b69056ce0ad9415b182b61056be0ad6c15ab82b53194fe169ec2d3b86a73074de069b41d3583a69074ce069941d3186a61094be1296c252b84a530549e06934152582a490548e06914152186a410547e0a8ec151b82a33072dc0e578242b0284e0507c0b5f096bc02d7409ae0135a046b001b7c256f006dd025b804b68116c006d7015ac01b54216a0069e0153801a4405afa0b5d4163f02c7d118dc131a8263308c62058bc06df82dbd01b790b6f006dd82db901b71136e006db825b501b66116c406d7815ad01b56056a406d380da681b4c4269406d2485a401b460368a06d104da101b411368006934352501a490d490069180d2281a44034820e5181ca20193e0325c435bc2eb585d6711ac60b1bc163582c67058c60b17c162d82c57058a606dbc0db581b67036c606d7c0dad81b57036a606d3c0da581b47214de269b82d3585a6a0b4ce16998853189a62114be22978852d84a5a214ae12958452988a520349e069380d1f81a3e 20 1048575 8 255 11 2047 19 524287
def cc_77_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x8d4338884c80b7d7be4d745797192c6e63369e486603e640205c080540804c57b4794c44d2c41a333d1493537e2d380253802450e1e65f1d80e1795f16b0e10c5f0c04c07d4305c2103b210053600005 0xb5f416ba81c7e0b8f4071d8163901c6e098d407198463101c5e058b407158162902b7e056fa22db84db50cb66116c40ad7815ab02b520369c1ad3435a601a7e0b4e41a9a80d3301a4e0349a068f80d1e81a3c034721a8c80d1886a30072fa0e5d41ca6819450727a0e4d44c26818451307a260d43416818250bade175ac2eb385d63058de0b1b4163582c67058ca0b18c162f82c5b058ae0b14c15b782b6e056da22d7c45af09b5b096b432d5c25ab08b53116a40ad3c15a702b47056860ad082d3785a6b0b4ce1698c452f86a5b194ae1a94c152782a4b0548e0a90c4d1f81a3d0d4761a8e6f11b81a350d4661a8c41cb78396d072ce0e5941caf839570529e0a51c1c9f8393d0726e0e4d41c97839270b0de1619c442f898570509e0a11c4c1f8d83d1306e360d434178982703cfe179f80f3e85d7f0baf6175dc2eb981d6f03ada075ac46b481d6709aca0758c0eb082c7f058fc0b1ec2e3d02c77058ec0b1cc2e3901c6f038dc071b40e3601c6b038d40b1a4b63401c67038cc0b194163201c63038c4071840e3002c5f058bc0b16c262d02c57058ac0b14c462902b7f056f60addc15b981b6f036da06dac15b481b67056ca06d8c0db082b5f056b60ad5c15a981a7b0b4f4069e40d3b81a76034e6069c40d3381a66034ca0697c0d2d81a57034a60693c0d2701a4d034980692c0d2481a470348a0690c152101a410d480068fc0d1d81a37034660e5fc1cbb8196f032da0659c1cb28395f072ae0a53c14a70394d0527e0a4f814990192f0324e161fc2c3b8186f030da0619c5c328885f170ae0a13c4c26828470508a0a0fc141b8182f0304e135bc26b584d6709ac60b1bc163582c67058c60b17c162d82c57058a652dbc4db705b6b0b6d416d9c2db314b63136c40ad7c15af04b5b096b40ad5c15ab02b53056a406d3c0da701b470368606d080d3781a6b034ce0698c0d2f81a5b034ae0694c0d2781a4b0348e0690c0d1f81a3d03476068e40d1b81a3503466068c41cb783967072be0e55c14a7819470727e0e4f40c9b819350325e0649ca43785867090be1215c1427828472907e260f4a41b898350305e0609c0f3f81e7e03cf6179e80f3b81e7603ce62f9c826bf84d7b09aee135cc0eb781d6e09ada0b1fc163f02c7b0b8f40b1dc163b02c73198e4071bc0e3702c6d058d8071ac0e3501c69038d00719c0e3301c65038c80718c0e3102c61b68c00b17c162f02c5b098b40b15c162b02c53098a40adfc15bd82b77056e606dbc15b681b6b036d206d9c0db281b63056c20ad7c15ad82b57056a6069fc0d3d81a77034e6069bc0d3701a6d034be069780d2d81a59034a6129480d2881a4f0349a0692c0d2481a470348a0690c0d2081a3f03476068dc0d198397f072ee065bc1cb681967032ca0e57c1cab8294f0529c0e534149f8293e05264064bc0c93c807f0b0ee061bc5c3681867030ca1217c242b8284f1909a0a11c14228283f0506e060bc0c1385d6f0badc275b42e3785c6b0b8ce1718c4e2f84c5d118b6231644e2b84c55118a62314415b582b67056c60ad5c15aa82b4f056960ad1c15a185a6f0b4d61699c2d3189a5f034ba1a96c352c89a57034aa1a94c352888a4f0d4963291c352182a3f054760a8dc151989d6f0bad61759c46b189c6fb28dc171ac2e3505c670b8cc2718c6e3108c5f118bc2716c262d0cc57098ac2314c462902b6f056d60ad9c15b182b5f056b60ad5c15a989a6f0b4d61699c353188a5f0d4b63295c352989a4f0349a1a92c35248da470348a1a90c352082a3f054760a8dc15198d86e0508c0a0dafab785d6b0bace2358c163782c6e058d6171a8163382c66058c775188162f82c5e058b613168162b82c56058a62314815b782b6b056ce0ad8c15af82b5b056ae0ad4ee13785a6b0b4ce1a98c452f86a5bb44ae1a94c152781a4d054960a924152381a45054861a904151f82a3b0546e0a8cc1cb783967072be0e55c14a78294e0729a0a4fc149f029320725e0e49e383785867110bed815c1427d804d0508e0a114141f828370d05e4c09c173f82e7e05cf6179e8173b82e7605ce63b9c826bf84d7b09aee135cc16b782d6e09ada0b1fc163d82c77058e60b1bc163702c6d058be0b178162d82c59058a613148162887c50036fe06dec0dbb81b73036de06db40db581b69036ce06d940db181b61036be06d6c0dab81b530369e06d2c0da381b430347c2e5f82cbb0296e232d80a59814b20495e092ac0a53814a3019361dade175ac2eb388d631d8de171ac2e3387c63118be1f16eb22b87c53036de06dac0db381b63036be06d6c0dab81b530369e06d2c0da381b430347c3a5b82cb30895e092ac1e53814a30193609cfe179f8273e84d7b0baf4135e426bb84d7609ae6135c426b384d6609aca171fc2e3d85c770b8e6131bc163684c6b0f8d21319c163284c63098c21317c262d84c59098ae1314c3e2881b7f036fc06dec2dbd01b77036ec06dcc2db901b6f036dc06db40db601b6b096d406da495b401b67036cc06d940db201b63096c406d8425b001b5f036bc06d6c25ad01b59096b006d5c0dab01b53096a406d4445a801b4f0369c06d2c15a501b470368c06d0c3da101a7f034f6069dc0d3981a6f034da069ac0d3481a67034ca0698c0d3081a5f034b60695c0d2981a4f034960691c0d218397f072ee0e5bc1cb683967072ca0e57c1cab8394f0728e064fc0c9f0393d0325e064b80c91069200b0fe161dc24378486d090ce36194242f848570f09e8811c0c1f8983d0306e060d40c178182705cfe179f8173e85d7f0baf6175dc2eb982d6f05ada0b5ac46b482d6709aca0b58c16b082c7b0b8f40b1e4163b82c76058e60b1c4163382c66058ca0b17c162f02c5b058ae0b14c3e2901b7f036fc06dec2dbd01b77036ec06dcc2db901b6f036dc06db40db601b6b056d406da49db401b67036cc06d940db201b63056c406d8415b001b5f036bc06d6c25ad01b57036ac06d4c45a901b4f0369c06d2c15a501b490569006d1c0da301b430568406d043da001a7f034f6069dc0d3981a6f034da069ac0d3481a67034ca0698c0d3081a5f034b60695c0d2981a4f034960691c0d218397f072ee0a5bc14b682967072ca0e57c1cab8294f0528e064fc0c9f0393d0325e064b80c91069200b0fe161dc14378286d050ce36194442fb30570509e0a11c0c1f8983d0306e060d40c178182705cfe0b9f8173d85e7a05cee0b9d8173991e7209afe135ec26bb84d7305ade0b5b826b682c7f058f60b1dc163982c6f058dc0b1b4162f82c5e058b60b164162984c52058a21f1400dbf81b7e036f616de80dbb81b76036e62edc80db781b6e036da06db00db582b6a036d20ada00db381b66036ca06d900db182b62036c246d800daf81b5e036b612d680dab81b56036a612d480da781b4e036960ad280da381b46036860ad080d3f81a7b034ee069cc0d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034ae0694c0d2781a4b0348e0690c1cbf83977052de0e5b414b382965072be0e55c14a7829470327e064f81c9e8192f0325c0648834904607f0b0ee0a1bc6c3682867050ca1217c242b8284f0508e060fc5c1e818370306a060bc0c1385d6f0bad61759c2eb185c6f0b8d61719c2e3188c5f0f8b62f15c3e2981b6f036da06dac0db381b65036c606d7c0dad81b57036a606d3c0da581b4703686069bc0d3701a6d114be229784d2d84a5a194ae12958452988a520f49e1e9384d2582a4a1748e0a9183d2187a420347e068f80d1b81a33034640e5bc1cb683967072ca0e57c1cab8394f0728e064fc0c9b8392f0725a0e49c1c928586f0b0ce2217c4c2b8784f1308e060fc0c1b8982f1b05a2609c6c1285d6f0badc275b42e3785c6b0b8ce1718c4e2f84c5d118b6231644e2b84c55118a6231442db785b6b0b6ce16d8c4daf82b5d0f6b61ed644dab82b550f6a61ed4445a787b4b1768e1ed0c0d3581a67034c60695c0d2a81a4f034960691c0d2181a3f03476068dc0d1989d6f0bad61759c46b189c6f0b8d61719c3e3188c5f0f8b62f15c3e2989b6fa06dc16dac2db505b670b6cc26d8c6db108b5f116bc26d6c25ad0cb57096ac22d4c45a907b4f0f69c26d2c15a50bb470568c1ed0c3da101a6f034d60699c0d3181a5f034b60695c0d2981a4f034960691c0d218d86e0306c0609aa2b785d6b0bace2358e9a3785c6b0b8ce1f18c462f87c5ba48ae1f14c0db781b6e036d616da80db381b66036c744d880daf81b5e036b612d680dab81b56036a622d480da781b4e036960ad280da381b46036861ed080d3781a6b034ce0698c0d2f81a5b034ae0694c0d2781a4b0348e0690c1cb783967072be0e55c1ca7839470327e064f81c9e8192f0325c0648834904506f0b0ce2217d882b8784f3c08e060fe781e818370306a060bc0c1382d7f05afc0b5ec2ebd02d7705aec0b5cc2eb902d6f05adc0b5b416b602d6b15ad40b5a456b402d6705acc0b59416b202d6313ac40b5846eb004c7f098f6131dc263984c6f098da131ac263484c67098ca1318c263082c5f058bc1317415bf82b7b056ee0adcc15b782b6d056d60ada415b382b65056c60ad8415af82b5e056ba0ad3c15a702b4b056920ad0c25a102b410f680169fc2d3d85a770b4e62a9bc0d3686a6b0d4d22a99c0d3286a630d4c20a97c0d2e82a5b054b20a95c0d2a82a530d4a21293c252584a47094860a8fc151d82a3705466165fc2cbb8a96f072da2a59c1cb28295f072ba0a55c14aa8494f0928e0a4fc149b8692f8c24e161e82c3b858760b0ce161982c328285f130ba0a15c142a8484f0908e0a0fc141b8682f0d05c2a09c34110b81e15024075fc0ebf01d7b0baf4075dc0ebb01d730bae4075bc0eb701d6d03ad8075ac56b501d6915ad00759c0eb301d6503ac80758c4eb101d611bac0131fc263d84c77098e6131bc263684c6b098d21319c263284c63098c20717c0e2f04c5d0b6fe16dec2dbb85b73156de0adb43db587b69156ce0ad943db187b61036be0ad740dad81b59036ae06d540da987b510969e12d2c25a384b43034fe069ec0d3b81a73034de069b40d3581a69034ce069940d3181a61034be069780d2e81a4f0349c0692c0d2481a4309484069040d1f81a3b0346e068cc2cbf85977152de0e5b454b383965032be0e5740cab819550929e1251c3c9fc81370325e0649c2c3d058770b0ec1619c2c3305865030be061784c2e8d85c030ae061540c290484f0908e1e0fc541b8182f0305c0609c0c110c81e15024175fc2ebd85d770bae62b5bc26b688d6b11ad22b59c26b288d6311ac2071fc0e3f01c7b0b8f4071dc0e3b01c730b8e4071bc0e3701c6d038d8071ac563501c69158d00719c0e3301c65038c80718c4e3101c611b8c00717c0e2f01c5b098b40715c0e2b01c53118a40adfc15bd82b77056e60adbc15b682b6b056d20ad9c15b282b63056c20ad7c15ad82b57056a606d3c0da702b4d034fe069ec0d3b81a73034de069b40d3581a69034ce069940d3181a61034be0696c0d2b81a530349e069380d2681a3f0347c068ec0d1c81a3305464068c42cbf85977152de0e5b454b383965112bf2855c0ca78394d0328e06514149f829370325e0649c2c3d058770b0ec1619c2c3305865110be2a15c0c278184e1309a361300c2381845030840a0fc141b8182f0305c0609c0c110b81e150240f9f0573c03e7417ce0071f0563c01c74198e0071b01e3401c642b8c02e1b0642603d7f07afc0f5ec2ebd03d7707aec0f5cc2eb903d6f07adc0f5b41eb603d6b15ad40f5a456b403d6707acc0f5941eb203d6313ac40f5846eb004c7f098f6131dc263984c6f098da131ac263484c67098ca1318c263085b7f0b6f616ddc2db98ab6f056da1edac3db48ab67056ca1ed8c3db083b5f056ba0ed6c1dac83b57056aa0ed4c3da884b4f0969612d1c25a185a7f0b4f6169dc2d398aa6f034da1a9ac35348aa67034ca1a98c353083a5f034ba0e96c1d2c83a57034aa0e94c352884a4f094961291c252187a3f0d477288dc35198395e0729c161d82c330385e1b0b81a0b80f3e0ae7803ce82f9c0163e0ac78058e8331c0163601c68038c8531805c360c84c0bafe175ec2ebb85d7315ade135b446b588d6915ace1359446b188d61058fe0b1f8163d85c7a058ee0b1d8163985c72058de0b1b8163682c6c058d62b1a816348ac68058ce0b198163282c64058c62718816308dc60058be0b178162d84c5a058ae0b158162988c52056fe0adec15bb82b73056de0adb415b582b69056ce0ad9415b182b61056be0ad6c15ab82b530b4fe169ec2d3b85a73154de069b4353586a69154ce06994353186a61114be1a96e412b86a530549e06934152582a490548e06914152186a410547e0a8ec151b82a330529c0a4f82c3b058660509c36130341702e7c15cf00b9d06f3807c50036f82ade00dba0bb70036d80ada00db210b6017078175fc2ebd85d770bae62b5bc26b688d6b11ad22b59c26b288d6311ac2171fc2e3d85c770b8e62b1bc163687c6b0f8d22b19c163287c630f8c22317c3e2dc64570f8a606dfc0dbf01b7b0b6f406ddc0dbb01b730b6e406dbc0db701b6d036d806dac55b501b69156d006d9c0db301b65036c806d8c4db101b611b6c006d7c0daf01b5b096b406d5c0dab01b53116a406d3c0da701b4b0569406d1c0da301b430f684069fc0d3d81a77034e6069bc0d3681a6b034d20699c0d3281a63034c20697c0d2d81a57034a60693c0d2581a4703486064f80c97058760b0cc060f86c1e0182e0b8de171ac2e3385c63158be13174462d88c59158ae13154462988c510b6de16dac2db385b63156be0ad743dad87b59156ae0ad543da987b511169e1ed2e69a387b430b4de169ac2d3385a63154be06974352d86a59154ae06954352986a511149e1a92e612386a430f47e1a8ee591b86a330b2de1659c54af8395d152ae0e55444a7c91470f27f1c4dc3497c51270b0d41619c2c33058570b0ac1615444278a8470f07e2a0dc34178682e1504e1a088740f0a81205cfe0b9f8173d85e7a05cee0b9d8173985e7209afe135ec26bb84d7305ade0b5b826b682c7f058f60b1dc163982c6f058dc0b1b4162f82c5e058b60b164162984c52058a21f1402dbf85b7b0b6ee16dcc15b781b6d056d60ada415b381b65056c61ad8425af84b5b096ae12d4c15a782b4b0568e0ad0c2cbb0693e0b0fc0a1b88c3602866050c812178442e04856090a80a1383c2602846050881a0f80c1b05d6f0bad61759c2eb185c6f0b8d61719c2e3188c5f0f8b70d15c3e2985b6f0b6d616d9c2db188b5f0d6b63ed5c35a987b4f0d6963ed1c35a1859660d27c161b8442f048560f09c0a118341f0183609ade135ac26b384d63158de171ac2e3387c63098be1316c262b84c53156de16dac2db386b63096be12d6c25ab84b530f69e1ad2c7da386b43092bc74518543705866090ac1e13814230683e0306c139f4273a81d7e0baf4075d826b901d6e09ad40759826b104c7e098fa131b8263304c62038bc1b174362e02b5d036b206d543da889b4d0f6922ed143da081a7e0b4e4069780d2e81a4e0349a069300d2486a42034821a900351d01a36072ba065544ca6bf1450d25a064944c3e85875030bc261744c2e01855030a4221342c2283c5c034981a9001cae01924 20 1048575 8 255 11 2047 19 524287
def cc_77_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x9039c8d13286a67823477d44f773616f97a67d7c6017c5b9485774254c2b509434de2b49b4347b204502b4113f3f1203be333724c2f37f2767d2294d1b0791842c15133109480de2b09f3f07f200007f 0x139fc2f3f04e7d09af6175e826bc84d7709aec135cc26b884d6709acc135940e3f81c7e038f6171e80e3b81c76038e6171c80e3781c6e038da071b00e3584c6a038d24b1a00e3381c66038ca071900e3184c62038c2131800e2f81c5e038b6131680e2c84c58038ae071580e2984c52038a22314015bf82b7b056ee0adcc15b782b6d056d60ada415b382b65056c60ad8415af82b5b056b20ad5c15a982b510369e06d3815a681a7f034f6069dc0d3981a6f034da069ac0d3481a67034ca0698c0d3081a5f034b60695c0d2981a4f0349c069340d1f81a3e03476068e40d1982a3203462165fc2cbd859770b2e6125bc1cb68496b092ce0e59424b18495f092b61255c24a98194f0729a0652c0ca381945032860a4fc149d8293705266064bc0c958192703246161fc2c3d858770b0e6121bc24368486b090ce2e19424318485f090b61215c24298184f1309a0612c0c2381845030860a0fc141d8283705066060bc0c1581827030462e07c540d8b817150260b5f416ba81c7e038ec071c81e3704c6a078cc23188162f02c5a058ac0b1480dbf01b7d116dc26da865b308b62056bc0ad6815ab02b52034fa069d40d2681a490348a069040d1e81a390346a068c41cbf05972192d40e5981ca70394d0727c0e4f41c9e0993213260261341c228983d1306a260741c0a85d6f0bad61759c2eb182c6f058da0b1ac163382c65058c60b17c162d82c57058a606dbc0db701b6d116be22d784dad84b5a196ae12d5845a988b520569e0ad3815a582b4a0568e0ad1815a182b42034de069b40d3581a67034ca0698c0d2f81a5b034ae0694c0d2781a4b0348e0690c0d1f81a3d03476068e40d1b81a3503466068c42cb78596b0b2ce1658c44af8c95b192ae2254c14a78294b0528e0a50c4c9f8393d1d277f44dc1c9a899330325e064ac0c93819230b0de161ac2c3385863110be2a16c4c2b888530509e0a12c1423828431307e360f44c1d898371b06a260cc0c178182b0304e0608c4c0f8a81b1302e2a04c2eb785d6e13ada171bc2e3585c670b8c62717c262e88c5b118b22715c262a88c53118a20adbc15b582b67056c60ad7c15ae82b5b056ae0ad5415a782b4b0568e0ad0c0d3781a6b034ce0698c0d2f81a5d034b60695c0d2a81a4f034960691c0d2181a3f03476068dc0d198596f0b2ce2657c1cae89957072aa2253c64a38293f0526e064bc0c938586f130da1619c2c328185f030ba0615c0c2a8884f1308e0a0fc141b8182f0304e275bc2eb585d6711ac6271bfda3705c6b0b8d41719c2e3309c631b8c42317c462f09c5b098b43315c262b08c53118a40adbc15b582b67056c60ad7c15ad82b57056a60ad3c15a682b470568a0ad0c0d3781a6b034ce0698c0d2f81a5b034ae0694c0d2781a4d0348e069140d2181a3f03476068dc0d198996f0b2ce2257c64ab8994f0729a3651c1ca28293f0526e064bc0c938986f1b0dc1619c7c310885f130ae0611c0c23018450507e0a0e8141b828360305e060a80c1381826fcade175ac2eb388d63038de071b80e3585c6a038ce071980e31fc462038be071780e2d84c5a038ae071580e2988c52056de0adac15b382b63056be0ad6c15ab82b530369e06d3815a681a6f034d60699c0d3181a5f034b60695c0d2981a4f0349c069340d1f81a3e03476068e40d1982a3203463d85bc2cb585967e02c62257f68ade6157112a60653c1ca68194b0328e065140ca18293f052760a4dc14998192f032560649c0c91cb06f0b0d61619c7c318885f1f0b6e415c44298184ff409a0612c0c2381845030860a0fc141d8283705066060bc0c1581827030463407c7c0d840171f0260b5fc16bf02d7b0baf40b5dc16bb02d730bae40b5bc16b702d6d05ad80b5ac1eb502d691dad00b59c16b302d6505ac80b58c1eb102d6107ac0131fc263d84c77098e60f1bc1e3683c6b098d20f19c263283c63078c20b17c162f04c5d056fe0adec15bb82b73056de0adb415b582b69056ce0ad9415b182b61056be0ad7815ae82b4f0569c0ad2c15a482b43096840ad043da005a7f0b4f6169dc2d3983a6f034da0e9ac353483a67034ca0e98c1d3082a5f034ba0a96c152c82a57034aa0a94c352884a4f094961291c252182a3f054760a8dc15198597a072ee0e5d81cb383966072ca0a57c1cae82957052aa0e53c1ca38293f0526e0e4bc1c938587f0b0ee0e1bc1c3683867170ca0a17c4c2e82857050aa1213c24238283f0506e1a0bc5c1381d7f03afc075ec2ebd01d7703aec075cc2eb901d6f03adc075b40eb601d6b07ad4075a476b401d6703acc075940eb201d6307ac4075841eb004c7f098f6131dc263983c6f078da0f1ac263483c67098ca0f18c1e3081c5f038bc131742dbf85b7b0b6ee16dcc1db782b6d076d61eda41db382b65076c60ed840daf82b5d036b606d640dab81b55036a61ed4425a784b4b0968e12d0c0d3f81a7b034ee069cc0d3781a6d034d6069a40d3381a65034c6069840d2f81a5e034ba0693c0d2701a4b034920690c252101a410347e068ec0d1b81a330b2f40e5dc1cbb03967072cc0e5940caf8195e072ba0e5700cab81955032a40e53c1ca38393f0726e064bc0c938587f0b0ee0e1bc1c3683867190ca0617c4c2e81857030aa1213c24238783f1906e060bc0c1385d7f0baf6175dc2eb983d6f07ada0f5ac46b483d6709aca0f58c1eb081c7f038fc071ec2e3d01c77038ec071cc2e3901c6f038dc071b40e3601c6b078d4071a4763401c67038cc071940e3201c63078c4071841e3001c5f038bc0716c262d01c57038ac0714c462902b7f056f60addc15b982b6f056da0adac15b482b67056ca0ad8c15b082b5f056b60ad5c15a981b4f0369c0ad340d3f81a7b034ee069cc0d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034ae0694c0d2781a4e0349a068fc0d1f01a3b03472068cc151901a310b2f40e5dc1cbb03967072cc0e5941caf839570329e065381ca68394c0328e065140ca10293f0526e064bc0c938587f0b0ee0e1bc1c3683867170ca2217c5c2b8184f1309a0611c0c228283f0506e060bc0c1385c6f0b8d61719c2e3183c5f078ba0f16c462c83c57098aa0f14c1e2885b6f0b6d616d9c2db183b5f056ba0ed6c3dac83b57056aa0ed4c1da888b4f0f697e0d1c3da185a6f0b4d61699c2d3183a5f034ba0e96c352c83a57034aa0e94c1d2888a4f0d497dc91c352187a3f0d477d88dc35198596a072ce0e5981cab83956072aa0e53c1ca38393f0726e0e4bc1c938586f0b0ce0e17c1c2e838571d0aa2213dc0238783f4a06e1a0bca81382e7f05cfc0b9ec2f3d02e7705cec0b9cc2f3904d7f09af6135dc26b982d6f05adc135b4163f82c7b058ee0b1cc163782c6e058da0b17c162f02c5b058b20b14c262902c510f8a016dfc2dbd85b770b6e60adbc0db682b6b056d20ad9c0db282b630d6c212d7c25ad84b57096a60ad3c15a582b4705686169d81cbf0296e232d80a59814b20495e112b81255824aa0294e0f2980a51814a20693e0326c075bc0eb701d6b03ad40759c0eb303d6307ac4131bc263584c67098c61317c262e85b6f0b6d616d9c2db18cb5f056ba1ed6c3dac8cb57056aa1ed4c3da884b4f0969612d1c25a181a6f034d60699c0d3181a5f034ba0693c0d2581a430347e068ec0d1b81a3303cfe079f80f3d85e7a03cee079d80f3985e7209afe135ec26bb84d7303ade075b826b685c7f0b8f6171dc2e3981c6f058da071ac0e3481c67038ca0718c3e3084c5f098b61315c262981b7f036f606ddc0db981b6f036dc06db40daf81b5e036b606d640da984b52036a206d3c0da581b4703686169d80d3703a6c072fc065bb98b601966032c81257844ae04956092a81e53814a30193e0d278064d80c9a05d6f0bad61759c2eb181c6f038dc071ac0e3501c67038cc0f18c1e3108c5f118bc2f16c262d0bc57098ac2314c462902b6f056d60ad9c15b182b5f056b60ad5c15a982b4f0569a069bc0d3581a67034c60697c0d2d81a57034a60693c0d2681a3f03476068cc2f3f85e7b0bcee179cc0ebf81d7e03af6175e80ebb81d7603ae6175c80eb781d6e03ad6135a80eb381d6603ac623588163f82c7b058ee0b1cc163782c6b058ce0b18c0e2f81c5e058ba06dfc0dbd81b77036e606dbc0db581b67036c606d7c0daf01b5d0369e06d380da581b49036860ad080da085a76034bc0e9701cbf0896e092cc0657b88ae01956032a80a5383ca60294605288064f8349e0193603268175bc2eb585d670bac6171bc2e3585c670b8c62317c3e2df44570f8a616dbc2db585b670b6c622d7c35adf23570d6a61ed3c35a5f03470d686169981cb70895e092ac1e53814a30693e0326c135bc26b584d6709ac63b1bc4e3705c6b0b8d41719c2e330ec63138c40717c0e2f03c5b078b40715c0e2b01c53038a40adbc15b582b67056c60ad7c15ad82b57056a60ad3c15a681a6f034d60699c0d3181a5f034b60695c0d2981a4f0349a068fc0d1d81a3309cfe139ec273b84e7303afe075f80ebd85d7a03aee075d80eb98cd7203ade075b80eb584d6a03ace075980eb184d62058fe0b1ec163b82c73058de0b1ac163382c63038be07178162e81b7f036f606ddc0db981b6f036d606d9c0db181b5f036bc06d740da781b4e0369606d240da182b4203682129b85cbf05976072cc0657b70ae01956032a80a5383ca60294605288064f80c9b04d6f09ad61359c26b18ec6f0b8d61719c3e3184c5f098b61315c26298eb6f0b6d616d9c35b184b5f096b612d5c25a987b4f0d697b4d1c35a184a5e1d2dc165981cab0794e0528c1a4f80c9b04e7d09cea075f82ebd01d7607ae4075b826b501d6609ac40f1f81e3e84c6e098cc131880e2f06c5d0d8b80ad740dac81b550f6a226d343da48bb450f682069f82d3901a5e034ba069380d2681a4c034921a9080d2086a400d474068d81cbe83975072ba065541ca683945130ba061544c26898450d05a0609426b784d6d09ad61359c26b284d63078de0f1b81e3684c5f098bc1315c262984c520b6de16dac2db385b63096be12d6c25ab84b531369e0ad343da587b491768e0ad143da187b410b4de169ac2d3385a63094be1296c252b84a531349e06934352586a49d648e06914352186a410f47e1a8ec5d1b86a33072de0e5b41cb383965072be0e55c1ca78394d0728e0e5141c9f839370725e0e49c2c3785867090be1215c4c278d84d1308e361143c1f898370d05e2609c173f85e7e05cfa0f5fc1ebf03d7b0baf40f5dc1ebb03d730bae40b5bc16b702d6d05ad80b5ac16b503d6927ad00b59c16b303d6507ac80b58c16b102d6105ac0131fc263d84c77098e60b1bc163682c6b098d20b19c263282c63058c20adec2dbd02b79056ee0add815b982b71056ce0ad9815b282b5f056bc0ad7415ae02b5b056b20ad5c15aa82b53076a40ad443da802b4f0569c0ad2c15a382b4309684169fc2d3d85a770b4e60a9bc0d3682a6b0d4d20a99c0d3282a63054c20e97c0d2e83a5b074b20e95c0d2a83a530d4a21293c252584a47094860a8fc151d82a37054660e5fc1cbb8296f052da0a59c1cb28395f072bc0e5741ca78394e092840a4fc149b8392f0724e161fc2c3b8286f050da0a19c64328385f130ba0e15c1c2a8484f0908e0a0fc141b8682f1904e079fc2f3f01e7d07afe0f5f81ebd85d7a07aee0f5d81eb985d7203ade075b80eb681d6c03ad6075a81eb496d6803ace075981eb283d6403ac6075880eb081d60098fe131ec263b84c73038de071b40e3584c69038ce131940e3181c610b6fe16dec2dbb85b73036de06db40db587b69036ce0ad940db181b61076be0ad741dad83b59076ae0ad541da987b510969e12d2c25a384b43034f6169e80d3c81a77034ec069cc0d3881a67034cc069940d2f81a5e034ba069700d2d81a59034ae069540d2983a52034a21a9400d2781a4b0348e0690c0d1f81a3b0346e068cc1cbf83977032de065b40cb383965072be0e5781cae8394f0729c125081c9f839370325e0649c2c3f85877030de061b40c338c865070be261741c2b838550909e1211c3c1f8c8370305e0609c26b784d6b09ace1358c163782c6b058ce0b18c162f82c5b058ae0b14cadb789b6e0b6d616da82db385b662b6c626d880daf81b5e036ae06d4c0da902b4f0569c0ad2c15a502b470568c0ad0c15a101a6f034d60699c0d3181a5f034b60695c0d2981a4f034960691c0d2181a3f0347a068ec0d1c81a370346a068cc0d188396f072ce0e57c0cab8294f0528e0e4fc1c9e819370326a064bc0c939586f0b0ce1217c242b8284f0508e560fc4c1e958371306a060bc0c1383e7f07cfc0f9ec2f3d03e7707cec0f9cc5f3904d7f09af6135dc26b981c7f038fc071ec2e3d01c77038ec071cc663901c6f038dc071b40e3601c6b078d4071a41e3401c67038cc071940e3201c63078c4071873a3001c5f038bc0716c262d01c57038ac0714c262902b7f056f60addc15b982b6f056da0adac15b482b67056ca0ad8c15b082b5f056b60ad5c15a981b4f0369c0ad340d3f81a7b034ee069cc0d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034ae0694c0d2781a4e0349a068fc0d1f01a3b03472068cc151901a31072fe0e5dc1cb78396e072da0e57c1caf049520329e0e5340ca3819450527e0a4dc0c9781927940fe161dc1c378b86d070ce0e194242f848570309e321340c23818450507e0a0dc0c17818270bade175b84eb684c6b098ce1318c262b84c550b6de16dac2db385b63136be0ad743dad87b59136ae0ad543da987b510969e12d2c25a384b430b4de169ac2d3385a63134be06974352d86a59134ae06954352986a510949e1292c252384a430f47e1a8ec5d1b86a3313adf955b82eb585d6a0bace175984eb18dd62098de131ac263384c63136de16dac2db387b63136be0ad743dad87b59176ae0ad543da987b510969e12d2c25a384b43134de169ac2d3386a63134be06974352d86a591b4ae06954352986a510949e1292c252384a430f47e1a8ec5d1b86a331b0dc0e158242303d6f07adc0f5ac2eb503d6707acc0f58f52b104c6f098d61319c2631e936f0b6d616d9c3db183b5f056ba0ed6c1dac83b57056aa0ed4c3da884b4f0969612d1c25a1e826f0b4d61699c353183a5f034ba0e96c1d2c83a57034aa0e94c352884a4f094961291c252187a3f0d477988dc35198396f072ce0e57c1caf0395d0729e0e53824a10393f0726e0e4bc1c93c906f0b0ce0e17f202e83857070aa1213c24238783f4606e1a0bca0138ed6f13adc175ac2eb505d670bacc3b58c4eb104c6f098d61319c263184c5f098ba0adbc15b582b67056c60ad7c15ae81b5b036b206d5c0daa81b53036a20ad3c15a582b4705686069bc0d3581a67034c60697c0d2e81a4f034960690c0d1f81a3b0346e068cc0f3f81e7e03cf6179e80f3b81e7603ce62f9c826bf84d7b09aee135cc0eb781d6e09ada0b1fc163d82c77058e6071bc163681c6b038d20719c0e3281c63058c20b17c162d82c57058a606dfc0dbd81b77036e606dbc0db701b6d036be06d780dad81b59036a612d480da881b4f0369606d1c0da182a4e192fc165d80cb76216c032cc0659024af0895c092ac1255014a30193e0326c3b5bc2eb585d6711ac60b1bc163582c67058c60b17c162d82c57058a63adbc2db585b670d6c622d7c35ade13570d6a60ad3c15a582b47056860a93874b705966112bc1255814a30693e0326c139fc2f3f04e7d09af6175e826bc84d7709aec135cc26b884d6709acc13594163f82c7e058f6171e8163b82c76058e6171c8163782c6e058da0b1b0163584c6a058d24b1a0163382c66058ca0b190163184c62058c213180162f82c5e058b613168162c84c58058ae0b158162984c52058a22314015bf82b7b056ee0adcc15b782b6d056d60ada415b382b65056c60ad8415af82b5b056b20ad5c15a982b510b4fe169ec2d3b85a73094de069b4253586a69094ce06994253184a61094be1296c252b84a530549e06934152582a490548e06914152186a410547e0a8ec151b82a33072fe0e5dc1cb78396d072ce0e5941caf839570529e0a5381ca68293f0527c0a4c81c97839270b0fe161dc24378486d090ce2e194242f848570509e261341423828450507e0a0dc34178b827 20 1048575 8 255 11 2047 19 524287
def cc_77_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xfa58dc331b246251b2e8b184fd19193671ef382c11c30a780061 0x4d6f05d6e04d6d04c6b05c6a04c6904c6704c6604c6304c6104c5704c5604c5505b6f05b6b05b6705b6304b5f02b5d04b5b07b5904b5702b5504b5304b5104b4f04b4b04b4904b4704b4307b4105a6f05a6b05a6705a6304a5f01a5d04a5b06a5904a5701a5504a5304a5104a4f04a4b04a4704a4307a3f06a3b7e23706a330596f0596b05967059630495f0395d0495b0495703955049530494f0494b04947049430793f0e93b5f137079330692f0e92b54127069230586f0586b05867058630485f0485d0485b0485712855048530484f0484b04847048430783f0a83b2d037078330682f0a82b18027068230e81f0a81b090170a81302d6f05d6e02d6d05c6f05c6b05c6705c6302c5f02c5d02c5b08c5902c5704c5502c5302c5102b6b05b6a02b6902b6702b6602b6302b6102b5702b5602b5502b4f02b4e02b4b02b4702b4307b4205a6f05a6b05a6705a6302a5f01a5d02a5b06a5902a5701a5502a5302a5108a4f06a4b8224706a4302a3f02a3b02a3702a330596f0596b05967059630295f0295d0295b0295703955029530894f0e94b69147089430293f0293b02937029330692f0e92b53127069230586f0586b05867058630285f0285d0285b0285713855028530884f0a84b3c047088430283f0283b02837028330682f0a82b17027068230e81f0a81b080170a81302d6f02d6e02d6b05d6a02d6702d6602d6311d6204c6f04c6b04c6704c6302c5f02c5e04c5d02b6f02b6b02b6702b6302b5f02b5e02b5d02b4f02b4e02b4b02b4902b4304b4202b4107b408626f05a6b05a6706a6302a5f01a5d02a5b02a5902a5701a5502a5306a5104a4f04a4b04a4704a4302a3f02a3b02a3702a337816f0596b05967741630295f0395d0295b0295702955029530494f0494b04947049430293f0293b02937029330692f5612b52127069234d06f0586b05867430630285f1185d0285b0285702855028530484f0484b04847048430283f0283b02837028330682f1a02b16027068231101f0b01b070170201301e7f05e7e01e7d02d7f02d7e02d7b05d7a02d7702d7602d7305d7201d6f01d6e01d6d01d6c01d6b01d6a02d6911d6801d6701d6602d6502d6401d6301d6201d6101d6004c7f04c7b04c7704c7301c6f01c6d01c6b04c6901c6704c6501c6301c6102c5f02c5e04c5d02b7f02b7b02b7702b7301b6f01b6d01b6b02b6901b6702b6501b6301b6102b5f02b5e02b5d02b4f02b4e02b4b02b4902b4304b4202b4107b4001a7b05a7a01a7901a7701a7601a7301a7101a6701a6601a6501a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330597f0597b05977059730196f0196d0196b0196703965019630295f0395d0295b0295702955029530494f0494b04947049430293f0293b02937029330192f0192b01927019230587f0587b05877058730186f0186d0186b018670b865018630285f0985d0285b0285702855028530484f0484b04847048430283f0283b02837028330182f0182b01827018230b81f0a81b0b8170a81301d6f05d6e01d6d05c6f05c6b05c6705c6301c5f01c5d01c5b08c5901c5704c5501c5301c5105b6f05b6b05b6705b6301b5f01b5d01b5b07b5901b5702b5501b5301b5108b4f07b4b8634707b4301a6b05a6a01a6901a6701a6601a6301a6101a5701a5601a5501a4f01a4b01a4701a4301a3f01a3b01a3701a330596f0596b05967059630195f0195d0195b0195703955019530894f0e94b68147089430793f0e93b5c137079330192f0192b01927019230586f0586b05867058630185f0185d0185b0185716855018530884f0a84b3b047088430783f0a83b28037078330182f0182b01827018230e81f0a81b060170a81304e7d04e7501d7e01d7601d7203d6e04d6a03d6604d6201c7e01c7d04c6e04c6a04c6604c6202b5d03b5902b5507b5109b4d07b490bb4507b4101a7d01a7501a5d01a5901a5501a5101a4d01a4901a4501a410397e059720395e0395d0394e0394d0394c09942099400b93a039360985d038550984d098450981d0381504d6f04d6d04d6b04d6704d6504d6301c6f01c6e01c6d04c5f04c5e04c5b04c5a04c5704c5604c5304c5205b6f05b6b05b6705b6304b5f04b5b04b5704b5309b4f02b4d07b4b07b490bb4702b4507b4307b4101a6f01a6d01a6b01a6701a6501a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330596f0596b05967059630495f0495b04957049530994f0394d0e94b8414703945099430793f0b93b0b937079330192f0192b01927019230586f0586b05867058630485f0485b04857048530984f0d84d0984b098470d845098430783f0a83b09837078330182f0182b01827018230981f0a81b098170a81302e7f05e7e02e7d01d7f01d7e01d7b05d7a01d7701d7601d7305d7201d6f01d6e01d6d01d6c01d6b02d6a01d6913d6801d6701d6601d6501d6401d6302d6201d6102d6004c7f04c7b04c7704c7302c6f02c6d02c6b04c6902c6704c6502c6302c6101c5f01c5e04c5d02b7b05b7a02b7902b7702b7602b7302b7102b6702b6602b6501b5f01b5e02b5d02b5c01b5b01b5901b5701b5501b5301b5202b5107b5002b4f02b4e02b4b02b4702b4304b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5e01a5d01a4f01a4e01a4b01a4901a4304a4201a4101a3f01a3b01a3701a330597f0597b05977059730296f0296d0296b0296703965029630195f0395d0195b0195701955019530494f0494b04947049430293f0293b02937029330192f0192b01927019230587f0587b05877058730286f0286d0286b028670c865028630185f0985d0185b0185701855018530484f0484b04847048430283f0283b02837028330182f0182b01827018230c81f0a81b0c8170a81305d6f05d6e09d6d04c6f04c6b04c6704c6304c5f04c5d04c5b04c5704c5505b6f05b6b05b6705b6309b5f02b5d07b5b07b5909b5702b5507b5307b5104b4f04b4b04b4704b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5701a5501a4f01a4b01a4701a4301a3f01a3b01a3701a330596f059670995f0395d09957039550494f049470793f0b9370192f019270586f0986d05867058650185f0185d01857018550484f048470783f098370182f0182709d6f8156e05d6b05d6a05d6705d6609d630dd6204c6f04c6b04c6704c6304c5f04c5d04c5704c5504c5309b6f05b6b05b6707b6309b5f02b5d07b5b07b590bb5702b5507b5307b5104b4f04b4b04b4704b4301a6f01a6b01a6701a6301a5f01a5d01a5701a5501a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330996f059670995f0395d0d957039550494f049470793f0b9370192f019270986f0d86e058670f8620185701856018550484f0484a04847048460783f098370182f0182a018270182601d6f01d6e01d6b05d6a01d6701d6601d638356204c6f04c6b04c6704c6301c5f01c5e04c5d8236f05b6b05b6707b6301b5f02b5d01b5b01b5901b5701b5501b5307b5104b4f04b4b04b4704b4301a6f01a6b01a6701a6301a5f01a5e01a5d01a4f01a4e01a4b01a4901a4304a4201a4101a3f01a3b01a3701a337716f0596b05967721630195f0395d0195b0195701955019530494f0494b04947049430793f6113b5a137079330192f0192b01927019234c06f0586b058670f8630185f8005d0185b0185701855018530484f0484b04847048430783f0f83b26037078330182f0182b01827018230f01f0f81b050170f813 19 524287 8 255 11 2047 20 1048575
def cur_77 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_77_4 (Nat.sub p 128)) (cc_77_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_77_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_77_1 (Nat.sub p 32)) (cc_77_0 p) (Nat.blt p 32)) (Nat.blt p 64)
def f_77 : Nat → Nat × Nat := unpackForestF 0x62f80b5f0168f0cd1c052fc214780ac500dbe06b74005d0148ef55bdf49bbd4627b8dcf4134051bbb3477648eec8dc04afb8457732d8e0d5dc4ae38347012a6dc571b5a38094b6b48ec958991b7b226f678c0c88dd96b73205d0128ec45b185ab8093b58adebc8dd62312c26f5b8c0b095d66372c04d0126ead15c0495a7d6f4f8de9f15d3db12836e4f07a0249d15a3a2a474546e948dd14a3a42574526e8d15d14938085f438ae0214c04259f2473f48a7c51cc6b118b6f314de75180c51b9896f378c0624dcd5ad19672328fe64d80c493808472f2ac020ec72b7952372b46a544dc72310e26f278c03895c70b7924601c2ae3f9fc85a50fd721f6a03849c702d0e0560106e3515c041589d6f138de2715c4cb7899571328e0209c362b8816c0d6ae1c57035a38081f0b8ae0206c12b78246f048ae08dbc11ab823470102e0515c04098003f 8 11
set_option maxHeartbeats 0 in
theorem rc_77 : dagCheckRootsV4 fullMask g_77 ep_77 138 bds_77 (dagTraceF fullMask rootStock 11 f_77) (cur_77 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_77_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_77_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_77_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_77_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_77_4 : treeBlockF 128 138 (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) = true := by decide +kernel
theorem nj_77_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_77_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_77_1 h1 h2)
theorem nj_77_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) i = true := block_join nj_77_1 (fun _ h1 h2 => treeBlockF_at nb_77_2 h1 h2)
theorem nj_77_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) i = true := block_join nj_77_2 (fun _ h1 h2 => treeBlockF_at nb_77_3 h1 h2)
theorem nj_77_4 : ∀ i, 0 ≤ i → i < 138 → (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) i = true := block_join nj_77_3 (fun _ h1 h2 => treeBlockF_at nb_77_4 h1 h2)
theorem nc_77 : ∀ i, 0 ≤ i → i < 138 → (dagCheckNodeV4 fullMask g_77 ep_77 bds_77 138 (dagTraceF fullMask rootStock 11 f_77) cur_77) i = true := nj_77_4
theorem lb_77 : LowerBin fullMask rootStock g_77 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_77 kn_77 sub_77 gl_77 rc_77 nc_77

def wg : List Gate := [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3936921600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3936921600)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3936921600) = g_77 by decide]
  exact lb_77

end PEqualNP.Outside.L_meta_49229

theorem PEqualNP.Outside.L_meta_49229 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3936921600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3936921600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49229.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3936921600) 13 PEqualNP.Outside.L_meta_49229.root_lb PEqualNP.Outside.L_meta_49229.wg 18 rfl PEqualNP.Outside.L_meta_49229.wfits PEqualNP.Outside.L_meta_49229.weval
