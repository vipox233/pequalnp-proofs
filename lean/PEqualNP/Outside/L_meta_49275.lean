import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49275

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

def m_0 : Nat := 0xcccc00000000
def s_0 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_0 : Nat := 0x44c00000000
def ep_0 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
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

def m_2 : Nat := 0x4444444400000000
def s_2 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_2 : Nat := 0x4044400000000
def ep_2 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_3 : Nat := 0xf0000000f000000
def s_3 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_3 : Nat := 0x100000007000000
def ep_3 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_5 : Nat := 0xf000f0000000000
def s_5 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_5 : Nat := 0x100070000000000
def ep_5 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_6 : Nat := 0xcccc0000
def s_6 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_6 : Nat := 0x44c0000
def ep_6 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_7 : Nat := 0xc0c0c0c00000000
def s_7 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_7 : Nat := 0x4040c00000000
def ep_7 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
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

def m_8 : Nat := 0xaa00aa00000000
def s_8 : List Nat := [0x22002200000000, 0xa000a00000000, 0xaa00000000]
def g_8 : Nat := 0x2002a00000000
def ep_8 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000000000
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

def m_9 : Nat := 0xa0a0a0a00000000
def s_9 : List Nat := [0x202020200000000, 0xa000a00000000, 0xa0a00000000]
def g_9 : Nat := 0x2020a00000000
def ep_9 : Nat := 0x208000000000002000800000000000000000000000000020200000000000000000000000000
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

def m_10 : Nat := 0xcc00cc00000000
def s_10 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_10 : Nat := 0x4004c00000000
def ep_10 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
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

def m_11 : Nat := 0x2222222200000000
def s_11 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_11 : Nat := 0x2022200000000
def ep_11 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_12 : Nat := 0xaaaa00000000
def s_12 : List Nat := [0x222200000000, 0xa0a00000000, 0xaa00000000]
def g_12 : Nat := 0x22a00000000
def ep_12 : Nat := 0x2800000000000002080000000000000220000000000000000000000000
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

def m_13 : Nat := 0xc000c000c000c00
def s_13 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_13 : Nat := 0x40004000c00
def ep_13 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_14 : Nat := 0xa000a000a000a00
def s_14 : List Nat := [0x200020002000200, 0xa0000000a00, 0xa000a00]
def g_14 : Nat := 0x20002000a00
def ep_14 : Nat := 0x200080000000200000008000000000000000000000000000000000000000200020000000000000000000000
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

def m_15 : Nat := 0xaa000000aa00
def s_15 : List Nat := [0x220000002200, 0xa0000000a00, 0xaa00]
def g_15 : Nat := 0x20000002a00
def ep_15 : Nat := 0x280000000000000000000000000000000000000002000000080000000200000020000000000000000000
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

def m_16 : Nat := 0x808080808080808
def s_16 : List Nat := [0x8000800080008, 0x80800000808, 0x8080808]
def g_16 : Nat := 0x800080808
def ep_16 : Nat := 0x8080000000008000008000000000800080000000000000000000000000000000000000000000000000000
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

def m_17 : Nat := 0xff000000000000
def s_17 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_17 : Nat := 0x17000000000000
def ep_17 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_18 : Nat := 0x2200220022002200
def s_18 : List Nat := [0x200020002000200, 0x220000002200, 0x22002200]
def g_18 : Nat := 0x20002002200
def ep_18 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000000000000000000000
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

def m_19 : Nat := 0xf0f000000000000
def s_19 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_19 : Nat := 0x107000000000000
def ep_19 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_20 : Nat := 0xf0f000000000
def s_20 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_20 : Nat := 0x107000000000
def ep_20 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_21 : Nat := 0xaa00aa00
def s_21 : List Nat := [0x22002200, 0xa000a00, 0xaa00]
def g_21 : Nat := 0x2002a00
def ep_21 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000
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

def m_22 : Nat := 0xff0000000000
def s_22 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_22 : Nat := 0x170000000000
def ep_22 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_23 : Nat := 0x4444000044440000
def s_23 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_23 : Nat := 0x4000004440000
def ep_23 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_23 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 1 bds_23 (dagTraceF m_23 s_23 3 f_23) (cur_23 0) s_23 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 1 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) cur_23) = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) cur_23) i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xa0a00000a0a0000
def s_24 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_24 : Nat := 0x20000020a0000
def ep_24 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_24 : KnownBin bds_24 := by intro b hb; simp [bds_24] at hb
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp [bds_24] at hb
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_24] at hb
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_24 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 1 bds_24 (dagTraceF m_24 s_24 3 f_24) (cur_24 0) s_24 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 1 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) cur_24) = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) cur_24) i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xc0c00000c0c0000
def s_25 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_25 : Nat := 0x40000040c0000
def ep_25 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_25 : KnownBin bds_25 := by intro b hb; simp [bds_25] at hb
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp [bds_25] at hb
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_25] at hb
def cur_25 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_25 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 1 bds_25 (dagTraceF m_25 s_25 3 f_25) (cur_25 0) s_25 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25 : treeBlockF 0 1 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 1 (dagTraceF m_25 s_25 3 f_25) cur_25) = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 1 (dagTraceF m_25 s_25 3 f_25) cur_25) i = true := fun _ h1 h2 => treeBlockF_at nb_25 h1 h2
theorem lb_25 : LowerBin m_25 s_25 g_25 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xcc000000cc0000
def s_26 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_26 : Nat := 0x40000004c0000
def ep_26 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_26 : KnownBin bds_26 := by intro b hb; simp [bds_26] at hb
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp [bds_26] at hb
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_26] at hb
def cur_26 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_26 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 1 bds_26 (dagTraceF m_26 s_26 3 f_26) (cur_26 0) s_26 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26 : treeBlockF 0 1 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 1 (dagTraceF m_26 s_26 3 f_26) cur_26) = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 1 (dagTraceF m_26 s_26 3 f_26) cur_26) i = true := fun _ h1 h2 => treeBlockF_at nb_26 h1 h2
theorem lb_26 : LowerBin m_26 s_26 g_26 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xcccc3333
def s_27 : List Nat := [0x44441111, 0x3333, 0xc0c0303, 0xcc0033]
def g_27 : Nat := 0x44c3333
def ep_27 : Nat := 0x480000000000000408000000000000000000000000000004400000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xa0aa0a00a0aa0a0
def s_28 : List Nat := [0x202202002022020, 0xa0a00000a0a0, 0xa00a0000a00a0, 0xa0aa0a0]
def g_28 : Nat := 0x20020020a2020
def ep_28 : Nat := 0x208200000000000000000000002002000080000000000000000000000020020020020200000000000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 4, g_24)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_24
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xffff00000000
def s_29 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_29 : Nat := 0x177f00000000
def ep_29 : Nat := 0x6800000000000006080000000000001220000000000000144000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20), (m_22, s_22, 4, g_22), (m_0, s_0, 4, g_0), (m_12, s_12, 4, g_12)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_22
  · exact lb_0
  · exact lb_12
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

def m_30 : Nat := 0x6060606060606060
def s_30 : List Nat := [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060]
def g_30 : Nat := 0x6000402060
def ep_30 : Nat := 0x40200000000060000020200000006000400040000000000000000000000000000000000000000000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV4 0xcc61 0x4e5620f 4 15 2 3 6 63 9 511
def f_30 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 3 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 3 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 3 (dagTraceF m_30 s_30 4 f_30) cur_30) = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 3 (dagTraceF m_30 s_30 4 f_30) cur_30) i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xff00ff0000000000
def s_31 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_31 : Nat := 0x1100170000000000
def ep_31 : Nat := 0x600000000000000000000000000000006000000000011001200000000001100140000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xff00ff00000000
def s_32 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_32 : Nat := 0x17007f00000000
def ep_32 : Nat := 0x68000000000000000000000000000600080000000000120020000000000014004000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_17, s_17, 4, g_17), (m_10, s_10, 4, g_10), (m_8, s_8, 4, g_8)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_17
  · exact lb_10
  · exact lb_8
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xf0f0f0f000000000
def s_33 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_33 : Nat := 0x1010107000000000
def ep_33 : Nat := 0x60000000000000006000000000000000000000000010101020000000001010104000000000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xf0f0f0f00000000
def s_34 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_34 : Nat := 0x107070f00000000
def ep_34 : Nat := 0x608000000000006000800000000000000000000000001020200000000000104040000000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_19, s_19, 4, g_19), (m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_19
  · exact lb_7
  · exact lb_9
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_34_1 (Nat.sub p 32)) (cc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 43 bds_34 (dagTraceF m_34 s_34 6 f_34) (cur_34 0) s_34 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 43 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xcccccccc00000000
def s_35 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_35 : Nat := 0x4044c00000000
def ep_35 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_10
  · exact lb_0
  · exact lb_2
  · exact lb_7
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_36 : Nat := 0xcc00cc00cc00cc
def s_36 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_36 : Nat := 0x4004c004c004c
def ep_36 : Nat := 0x48000000000048000000000000000000000000000400080008000800000000000000000004004000400040
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xaaaaaaaa00000000
def s_37 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_37 : Nat := 0x2022a00000000
def ep_37 : Nat := 0x228000000000002002800000000000202080000000000020220000000000000000000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_12
  · exact lb_11
  · exact lb_9
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_37_1 (Nat.sub p 32)) (cc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_38 : Nat := 0xcccc0000cccc0000
def s_38 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_38 : Nat := 0x40000044c0000
def ep_38 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 4, g_26), (m_6, s_6, 4, g_6), (m_23, s_23, 4, g_23), (m_25, s_25, 4, g_25)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_6
  · exact lb_23
  · exact lb_25
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_38_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_38_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_38 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_38_1 (Nat.sub p 32)) (cc_38_0 p) (Nat.blt p 32)
def f_38 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 43 bds_38 (dagTraceF m_38 s_38 6 f_38) (cur_38 0) s_38 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_0 : treeBlockF 0 32 (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_1 : treeBlockF 32 43 (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38) = true := by decide +kernel
theorem nj_38_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_38_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_38_1 h1 h2)
theorem nc_38 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38) i = true := nj_38_1
theorem lb_38 : LowerBin m_38 s_38 g_38 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xaaaa0000aaaa0000
def s_39 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_39 : Nat := 0x20000020a0000
def ep_39 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 4, g_24)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_24
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xaa00aa00aa00aa00
def s_40 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_40 : Nat := 0x20002002a00
def ep_40 : Nat := 0x200280000000200000028000000000000000000000002000200080000000200020020000000000000000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_21, s_21, 4, g_21), (m_18, s_18, 4, g_18), (m_14, s_14, 4, g_14)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_21
  · exact lb_18
  · exact lb_14
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_40_1 (Nat.sub p 32)) (cc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_41 : Nat := 0xff000000ff00
def s_41 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_41 : Nat := 0x170000003f00
def ep_41 : Nat := 0x2800000000000000000000000000000000000000060000000c0000001200000030000000140000000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xf0f00000f0f0
def s_42 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_42 : Nat := 0x107000003070
def ep_42 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_20
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf0f00000f0f0000
def s_43 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_43 : Nat := 0x1070000070f0000
def ep_43 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_19, s_19, 4, g_19), (m_25, s_25, 4, g_25), (m_24, s_24, 4, g_24)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_19
  · exact lb_25
  · exact lb_24
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_43_1 (Nat.sub p 32)) (cc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 43 bds_43 (dagTraceF m_43 s_43 6 f_43) (cur_43 0) s_43 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 43 (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43) = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43) i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xcccc0000cccc
def s_44 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_44 : Nat := 0x44c00000c4c
def ep_44 : Nat := 0x800000000000000000000000048000000400000040800000c0800000000000000000000044000000040
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xaaaa0000aaaa
def s_45 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_45 : Nat := 0x22a00002a2a
def ep_45 : Nat := 0x280000000000000000000000002800000000000002080000080800000220000020200000000000000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0x3300330033003300
def s_46 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_46 : Nat := 0x1100130013003300
def ep_46 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000001100100010000000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xcc00cc00cc00cc00
def s_47 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_47 : Nat := 0x40004000c00
def ep_47 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xf000f000f000f00
def s_48 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_48 : Nat := 0x100070007000f00
def ep_48 : Nat := 0x600080000000600000008000000000000000000000000000000000001000200020000000100040004000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5), (m_13, s_13, 4, g_13), (m_14, s_14, 4, g_14)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_5
  · exact lb_13
  · exact lb_14
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_48_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_48 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_48_1 (Nat.sub p 32)) (cc_48_0 p) (Nat.blt p 32)
def f_48 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 43 bds_48 (dagTraceF m_48 s_48 6 f_48) (cur_48 0) s_48 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 43 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48) i = true := nj_48_1
theorem lb_48 : LowerBin m_48 s_48 g_48 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0x5555555500000000
def s_49 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_49 : Nat := 0x1115155500000000
def ep_49 : Nat := 0x440000000000004004000000000000404000000000011101000000000000000000000000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xffff0000
def s_50 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_50 : Nat := 0x175f0000
def ep_50 : Nat := 0x48000000000000060a000000000000120000000000000014500000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xff00ff00
def s_51 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_51 : Nat := 0x17003f00
def ep_51 : Nat := 0x280000000000000000000000000006000c0000000000120030000000000014000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xaaaaaaaa
def s_52 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_52 : Nat := 0x20a2a2a
def ep_52 : Nat := 0x2820000000000008000000000000020a080800000000020020200000000000000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_21
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xf000f000f000f0
def s_53 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_53 : Nat := 0x10007000500070
def ep_53 : Nat := 0x40000000000060000000200000000000000000000000000000000000100020000000200010004000500040
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

def m_54 : Nat := 0x8888888888888888
def s_54 : List Nat := [0x808080808080808, 0x88008800880088, 0x888800008888, 0x88888888]
def g_54 : Nat := 0x800080808
def ep_54 : Nat := 0x8080000000008000008000000000800080000000000080008080800000000000000000000000000000000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xc0c0c0c0c0c0c0c
def s_55 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_55 : Nat := 0x4040c040c0c0c
def ep_55 : Nat := 0x408080000000408000008000004000800080000000000000000000000000000000000000004040004000000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_25, s_25, 4, g_25), (m_13, s_13, 4, g_13), (m_16, s_16, 4, g_16)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_25
  · exact lb_13
  · exact lb_16
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_55_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_55 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_55_1 (Nat.sub p 32)) (cc_55_0 p) (Nat.blt p 32)
def f_55 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 43 bds_55 (dagTraceF m_55 s_55 6 f_55) (cur_55 0) s_55 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 43 (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55) = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55) i = true := nj_55_1
theorem lb_55 : LowerBin m_55 s_55 g_55 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xa0a0a0a0a0a0a0a
def s_56 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_56 : Nat := 0x2020a020a0a0a
def ep_56 : Nat := 0x208080000000208000008000002000800080000000000000000000000020200020000000000000000000000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_24, s_24, 4, g_24), (m_14, s_14, 4, g_14), (m_16, s_16, 4, g_16)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_24
  · exact lb_14
  · exact lb_16
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_56_1 (Nat.sub p 32)) (cc_56_0 p) (Nat.blt p 32)
def f_56 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 43 bds_56 (dagTraceF m_56 s_56 6 f_56) (cur_56 0) s_56 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 43 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) i = true := nj_56_1
theorem lb_56 : LowerBin m_56 s_56 g_56 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0x3333333333333333
def s_57 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_57 : Nat := 0x1113133313133333
def ep_57 : Nat := 0x200200000000220000020200002002000000000000202000202000000000000000000001110100010100000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 5, g_46)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_46
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 0 bds_57 (dagTraceF m_57 s_57 5 f_57) (cur_57 0) s_57 5 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_57 g_57 ep_57 bds_57 0 (dagTraceF m_57 s_57 5 f_57) cur_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0xff00ff00ff00ff00
def s_58 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_58 : Nat := 0x1100170017003f00
def ep_58 : Nat := 0x6002800000006000000280000000000000000000000060006000c0011001200120030001100140014000000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_48, s_48, 7, g_48)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_48
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 0 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) s_58 7 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_58 g_58 ep_58 bds_58 0 (dagTraceF m_58 s_58 7 f_58) cur_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xf0f0f0f0f0f0f0f
def s_59 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_59 : Nat := 0x107070f070f0f0f
def ep_59 : Nat := 0x608080000000608000008000006000800080000000000000000000001020200020000000104040004000000
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43), (m_48, s_48, 7, g_48), (m_55, s_55, 7, g_55), (m_56, s_56, 7, g_56)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_43
  · exact lb_48
  · exact lb_55
  · exact lb_56
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV4 0xe001 0x174fba5dd1ee86e4f725b91dc86e3f71db8ddc67c4fe25f11f88743fa1dd0de866c2f615b09d84601f 10 1023 5 31 10 1023 13 8191
def f_59 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 1 bds_59 (dagTraceF m_59 s_59 8 f_59) (cur_59 0) s_59 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 1 (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 1 (dagTraceF m_59 s_59 8 f_59) cur_59) = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 1 (dagTraceF m_59 s_59 8 f_59) cur_59) i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0xff00ff00ff00ff
def s_60 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_60 : Nat := 0x17007f005f007f
def ep_60 : Nat := 0x4800000000006800000020000000000000000000060008000a000800120020000000200014004000500040
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_32
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 0 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) s_60 7 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_60 g_60 ep_60 bds_60 0 (dagTraceF m_60 s_60 7 f_60) cur_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0xffff0000ffff
def s_61 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_61 : Nat := 0x177f00003f7f
def ep_61 : Nat := 0x2800000000000000000000000068000000400000060800000c0800001220000030200000144000000040
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_29
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV4 m_61 g_61 ep_61 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_61 g_61 ep_61 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_61 kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0xffff0000ffff0000
def s_62 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_62 : Nat := 0x11170000175f0000
def ep_62 : Nat := 0x64800000000000000000000000600000048000000060000060a000011120000120000001114000014500000
theorem epk_62 : ep_62 = edgePack m_62 g_62 := by decide +kernel
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43)]
theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_43
theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV4 m_62 g_62 ep_62 0 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) s_62 7 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_62 g_62 ep_62 bds_62 0 (dagTraceF m_62 s_62 7 f_62) cur_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_62 kn_62 sub_62 gl_62 rc_62 nc_62

def g_63 : Nat := 0x1117177f175f3f7f
def ep_63 : Nat := 0x64828000000066800002820000600680048004000060608060a0c0811121220120030201114144014500040
theorem epk_63 : ep_63 = edgePack fullMask g_63 := by decide +kernel
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35), (m_60, s_60, 8, g_60), (m_59, s_59, 9, g_59), (m_62, s_62, 8, g_62), (m_37, s_37, 7, g_37), (m_61, s_61, 8, g_61), (m_38, s_38, 7, g_38), (m_23, s_23, 4, g_23), (m_58, s_58, 8, g_58), (m_40, s_40, 7, g_40), (m_34, s_34, 7, g_34), (m_29, s_29, 7, g_29), (m_57, s_57, 6, g_57), (m_42, s_42, 5, g_42), (m_32, s_32, 7, g_32), (m_55, s_55, 7, g_55), (m_56, s_56, 7, g_56), (m_48, s_48, 7, g_48), (m_43, s_43, 7, g_43), (m_46, s_46, 5, g_46), (m_30, s_30, 5, g_30), (m_54, s_54, 5, g_54), (m_18, s_18, 4, g_18), (m_52, s_52, 5, g_52), (m_53, s_53, 5, g_53), (m_16, s_16, 4, g_16), (m_47, s_47, 5, g_47), (m_51, s_51, 5, g_51), (m_31, s_31, 5, g_31), (m_44, s_44, 5, g_44), (m_50, s_50, 5, g_50), (m_45, s_45, 5, g_45), (m_28, s_28, 5, g_28), (m_36, s_36, 5, g_36), (m_49, s_49, 5, g_49), (m_39, s_39, 5, g_39), (m_33, s_33, 5, g_33)]
theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_35
  · exact lb_60
  · exact lb_59
  · exact lb_62
  · exact lb_37
  · exact lb_61
  · exact lb_38
  · exact lb_23
  · exact lb_58
  · exact lb_40
  · exact lb_34
  · exact lb_29
  · exact lb_57
  · exact lb_42
  · exact lb_32
  · exact lb_55
  · exact lb_56
  · exact lb_48
  · exact lb_43
  · exact lb_46
  · exact lb_30
  · exact lb_54
  · exact lb_18
  · exact lb_52
  · exact lb_53
  · exact lb_16
  · exact lb_47
  · exact lb_51
  · exact lb_31
  · exact lb_44
  · exact lb_50
  · exact lb_45
  · exact lb_28
  · exact lb_36
  · exact lb_49
  · exact lb_39
  · exact lb_33
theorem sub_63 : ∀ b ∈ bds_63, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xcb4b7172cc04b2e636b32cea6cca150e84029a6d641518aab6290389a16171f7febdd8ce6d915a1a960af95953512a52b33456aced5132d10aac12054c55d70bb381ea0002f00001 0xb1bc098d602c6702631812dbc096d604b67025b183ad3c0569602b4704da18129bc094ce03a6302d2780a92c0548e03a4302d1f80e8ec0b46e03a33024b38125980f2ca0795503ca7836538052960294a014a380a5180f2860794203c9f8224f80f2760193a03c9b8064d80f2660793201c9780e4b809ade07d6e026b680adbc056da07b6b03db480ad9c056ca07b6306db080ad7c096b602b57025a981e9bc034da07a6b03d3481e99c034ca07a630453081297c094b604a570252983a8fc0547602a3704d198125bc092da0495f01cad80e54c0b27e0293b0149b80e4cc0b25e0392b02c9380e48c058de02c6b0163380b18c096de04b6e06db581eda81b6ce07b66025b1812d880569e02b4e065a68129bc234d60ea670253180a93c0549602a47015218368fc0347a0da3b0451c8368dc0346a0da33045188125bc072d60596701cb180a52c0528e0294302c9b8164d40b25e0392b02c9380e48c058de1f46b0163381318c096de13b6b075b3812d8c1d69e02b4b015a384ed0c094de03a6b0353501699c0b4cc03a6302d2a81693c0549602a4701d218168fc0747605a3701d198125bc092dc0c96b0f0b505a59c3a2cc04963024b10165543b29e1c14e014a580a5280528e02946064a18505082727e0893e0649d8064e81d26e01936064998224c8180cc05036026bf0135b8058fc02c7d0163e00b1e4058ea14c72016388371c0036fa08b7900dba822dc40569209b4102d3e80e9e40b4ea03a7102d2680a914292fc1497d0acbe01e5e81b2f20797803cbb0525d40f2e81497206cb88365c0092dc0496d024b60125a8092cc1496503cb2012588292aa0c954014a70165341127c0193a00c9b0224c80525c04d6f04eb38071bc118d601c670263182316c038ae04b6f045b5822d9c096c608b5b045ab80ad3c0569c02b4d0253780e9ac0b4ce03a6301d2d81695c0b49e01a4b00d2380e90c0b47e05a3d01d1d8228e80b46e05a3602d1a8168d0074660496f04cb582659c092c60d95b06cab82253c1129a0194b00ca500651c0328c0d94502ca18164fc0b27a0193b00c9d0164dc0326c0593500c9a0164cc0525e02927014918121bc090ce0884f00c238220fc1107a0883a0441b8220d81506a0382f0141380e07c0502e04d6f026b380b1bc058d602c670163180b16c058ae04b6f025b5812d9c096c607b5b03dab80ad3c0569602b47015a18129bc074d604a6701d3180e96c0b4ae02a4f0152580a91c0548605a3f01d1d8168dc0746604967024b301e5940f2b60795a03cab81e5580529e0294e03ca681e4fc1127c0793b00c9d01e4dc0326c0793303c9900e4bc0725c0492701c9180e488090de048670142780a11c0907e0483701c1780a09c0703e0381d0240b80e054092d80c95406f3f0139f42eafa14d75026b6853594058fa02c790163a80b1c4058d202c6100dbe822de4036ea08b71025b683ad940569209b410253e80a9e4054ea02a7102d2680a914092fc0497d024be0125b8092d40d96903cb4012588092c20496006cad0485580529c0594d04c9f0364e81d26c099320149700a498052440487d0143a8121340508a0381d0140a8135bc0fadc04d6d03e3781f1b40f8ce07c650262f813174098ae07c55015b780adb4056d602b69015b380ad94056c602b61015af80ad6c056b202b57015a980ad440569602b4703d378069b40f4d607a6903d338069940f4c608a610252f812974094b604a5703d2a81294c0f49607a470151f80a8ec0546e02a33024b78125b4052d602969014b380a594052c602961024af80e56c092ae0395301ca581651c0527e0293b0149b80a4cc0b25e0392b02c9380e48c090de0486d0143380a194090be048570141f80a0dc0905e0482701c0f80a05c058de02c6b0163380b18c096de11b6b075b3812d8c0569e02b4b015a380ad0c094de03a6b02d3380e98c0549e02a4b015238168fc0747605a3701d198125bc092dc0c96b03cb503259c0f2cc04963024b10325540529e0294e064a68324fc1127c0c93b00c9d0324dc0326c0c9330449900e4bc0725c0497c03cba01256009af807d68026b00331f0298c804e7e09b3d0539d809ce414d7606eb700b1a4058b201b6d045b4806d94116c20eb55015a4836d04054d205a4d015228125f81b2f412176024b9036564192b00294e02ca68464f81b2740e93606c9900a4b809ade04d6e066b581f5a819ace07d66026b1813588198cc0cc5e015b780adac056ce02b63015ad80ad640569204a6f08d3583a99c094c60ca5f00d2e83296c114b20ca5700d2a83294c114a20ca450151f80a8ec0546e02a33024b780e5ac0b2ce03963014ad80a5640527e0293b0149b8164bc072560592701c918135bc34ace02c6f0163580b19c058c602c5b0162b812dbc236d60eb67025b1846d6c1d6ae02b4f015a580ad240568e02b430c9a08129bc074d605a6701d3180e96c0b4ae02a4f02d2680a92c0548e02a45015218168fc0747605a3701d198125bc092dc0d96b0c0b505859c2a2cc04963024b103656c282b411157080ab00a53c0529c0594d08c9f8224f81b2760193a0749b8064d81b266089320149780a4b80524e02923014910121bc090ce0284f0542680a11c0508a0a83f0541b80e0bc0504e0381f01c0e80a05c0502a04d6f026b380b1bc098d602c670263181b16c058ae04b6f025b5812d9c096c606b5b035ab83ad3c0569602b4704da18129bc094dc04a6b0253381298c094c405a5b0352d01695c0b4ac05a4f0152580a91c0b48605a3f02d1d8168dc0b46603967024b300e594072b60395701ca780a52c0528e0394301c9f80e4ec0726e0393301c978124b80725a0486f0243501219c090cc0484f014238120fc09074048370201b00e0bc0705c0382d01c0f80e0780702e038120263500b198058aa04b7e025bd012dd8096e404b6e025b5012d98096c402b5500d3e8069d40347a08a3900d1a8228c4092fc03979024b900e5c4072e00496e02cb4812588092c20593d02c9c8164d40b2620487e01c3c8121c8070e20486a024330160f4070720583501c1880adbc096d602b67025b180ad7c096b602b57025a98129bc034da04a6b02533806994094c604a5f0252d81295c094a60ea3f0151d80a8dc134660496f01cb581259c072c60495f01cad812568092ae0495601ca98165140b27e0293b0149b80e4cc0b25e0392b02c9380e48c090de0486e01c3581219c090c6048620242f812178090b604857024298121480b08a1683f0141d80a0dc190660982f0641583a09c1304604c6f0263381317c098ae02b6f025b580ad9c096c602b5f025ad80ad5c096a60d34b015a38129bc034da04a6b02533806994094c604a5f0252d81295c094a609a4b0752383a8fc0547602a3704d198125bc092dc0396b01cb481259c092c60496201cb080e580092be0495e024ad816564092ae04953024a90125440b2960c14a02ca38165180b27e0293b0149b8164cc0b25e0592b02c9381648c090de0486e01c3580e1a4090ce038630243100e184090be0385b0242d01215c090ac0385301c2581611c0b07e0283b0141b80e0cc0b05e0382b02c1380e08c09afc04d6e0163e8371e4058ea0dc7100dbe806de4036ea01b71025b5006d98034fa01a7900d3a8069c40b2fa0597902cba8165c40327c0193900c9900e4c4072600192e00c948064880b2420892002c3e80e1e40b0ea03871024350121980307c0183900c1900e0c40706002d7e016be80b5d409ae40dd6a016b300b1d8058ea0dc6a0863300b178098ba04b7a00dbb006d340369201b4500da08269a8034cc01a4d00d24806914034821696a02cb30165340b2920594502ca08064f8032720193201c9880e4c00325c0192900c91016484112400487a0243b016134070920584501c208060f8030720183201c1880e0c01baf402d76016b28131f81b8f40fc760263900b1940f6f401b7600da6806d240368a01b4100d268069240348a01a4102ca68165240b28a0594100c9f0064e4032640393101c980064b8032520192202c908224800d0f40587602c2680e1240b08a0384100c1f0060e4030640383101c180135bc09ace02c6f0263580b19c098c607c5b0162b806dbc036da01b6b00db3806d94036c601b5b03dad006d5c036ac01b4f00da5806d1c0368601a6700d330069940f4b607a5703d2780a92c0548e07a4300d1f8068dc034660496f024b581259c092c60595b03cad01655c0b2ac0594f014a580a51c0b2860193f00c9d8064dc032660592f02c958164a40b24e0592302c908121bc070d60486a02433812198070c60385b02c2b81613c050960284701c218060fc030760183700c198160bc0b05c0382b01c1481609c070460782201c1080e080058de09c6b0163381318c036de01b6b03db5006d9c036cc01b6300da7806d2c0368e01b43025378229ac114ce04a6300d2a82293c0549602a47045218125bc0b2d605967024b181653c052960294702ca18064fc0327c0193b00c9b8064cc032640592f02c970164ac0b2520592702c918224880b242089200243780e1ac0d0d40586702c3300e18c0b09e0284b0142380e10c0307e0183e00c1d8060dc030660183202c1780e0ac0d0540582702c1300e08c058de16c6b0163381318c036de01b6b03db5006d9c036cc01b6300da7806d2c0368e01b4300d378069ac034ce01a6300d2780692c0348e01a43024b780e5ac0d2d40596702cb300e58c0b2aa0594f014a580a51c072860193f00c9d8064dc032660192f00c9580649c032460486f0643584e19c090c60585509c2780a12c0508e0c84300c1f8060f8030760183700c198060c80305e0182e00c158060a40304e0182300c110320841104004d6f026b380b1bc098d602c670263181b16c058ae01b6f00db5812da8036ce01b6600db1806d6c036ae01b4f00da5806d1c0368601a6f00d3580699c034c601a5b0352d00695c034ac01a4f00d2580691c034860496f024b581259c092c60595b034ad01655c0b2ac0594f014a580a51c0b2860193f00c9d8064e40326e0193301c988064bc032560192900c9380648c0b242038670243300e194070b60385701c2780a12c0508e0384300c1f8060f8030760183900c1b8060cc030640383101c180060bc0705a0182b00c13806094030460381f0240f00e07409ade0a567016378251ac058ce04c630422d80b15c036de01b6b039b5006d9c036cc01b6300dad806d5c0369e01b4b00da3806d0c034de01a6b00d3380698c034b60625a00d2b8069580349e01a4b00d2380690c092de0596b02cb381258c0b2b60515a02cab8165580b29e0294b014a381650c0327e0193e00c9d8064e40326e0193300c9900e4c4072600192f00c970064ac032520192700c918064880b242089200243780e1ac080d40586702c3300e18c070b60585702c2780a12c0508e0384300c1f8060f8030760183900c1b8060cc030640383101c180060bc030560182700c118135bc62ace02c6f1823580b19c098c62f45b0162b812dbc566d60eb67025b18a0d6c1d6ae0eb4f015a580ad1c4868604a6f025370169ac404d405a6702d3301298c094c405a5b0d92d01695c0b4ac05a4f02d2700a92c0549402a470152301690c1e48405a3f02d1f0168ec0347405a3700d1b0168cc114640496f01cb58385a80b2ce0596601cb180e56c0b2ae0594f014a580a51c072860593f01c9d8164dc072660486f05c3501219c160cc0a84f0142382e0fc170740b8370181b00e0bc0705c0382d01c0f80e0780702402c6f0263580b19c098c604b6f025b5812d9c096c60ab4f015a580ad1c1568603a6f01d3580e99c074c603a4f0152580a91c0748603a3f01d1d80e8dc0746603926024370121981509c028460441f0060d80705d5845fab22dd1115e788a602b5f9d9ad80ad5e726a602b4f9a1a580ad1e646873025f9592dc9c95e4a4a72324f90925c5491e244871023f0151d80a8de164670915f838adbe055dea2a6eb14f6f0a5b4851d8e286c213f0149d80a4dd76266b912f5b895a7049d302469405f4982da2815d0e0a68304f410259d011ce20866803f0141d80a0dcce0666502f320158e409c700463601f1a80d80805c020260003f 18 262143 7 127 11 2047 21 2097151
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x88c5c7fe8e7e41a7be267942a7464e726206a97d65f4a63d2263904629105fb2e59b6051a814b86248d2b43c513e25a35e843332b2f043287692582f207511ab5c11d8e0f4290c72d07a4d02e4c0002e 0x9ade1b59c163782c6b058ce0b18c162d82c57036de06dac3db501b67036cc06d8c0dad86b5a036ae06d580da781b4e0369606d240da381b430568406d040d3781a6b034ce0698c0d2d86a5a034ae069580d2781a4b0348e0690c1cb78396b072ce0e58c1cad839570529e0a52c14a3819430327e064f80c9d819390326e064cc0c990393107260064bc0c958192703246121bcbc3597867090c61a16c342d068570d0ac0a13c1423828430307e060f80c1d818390306e060cc0c190383107060060bc0c170182b030520609c0c1181822230420a07c140b8281309cfe1b9dc16bf82d7b05aee0b5cc16b582d67038fe071f80e3d87c7a038ee071d80e3984c72038d61b1a80e3381c66038be071780e2d82c5a038b20b1600e2b81c56038a60b1480e28c1450036fe06dec0dbb81b73036d61ada80db381b66036be06d6c0dab81b53074fe0e9ec1d3b83a73074d60e99c152f83a5d054b60a968152b82a56054aa0693c0d2703a4d0b4980692c0d2481a470348a0690c0d2103a4107480068fc0d1d81a37034660e5fc24bf0397b072f40e5de00bb03973072e40e5ac1cb5039670d2cc0a57c14af0395d0329e065381ca6bf14c03296065280ca4819480328e065180ca28194403286065081ca0839400327e064f81c9e8893c03276064e80c9b819360326a064d00c99819320525e0a4b814968487f090ee1a1a834330285f050ae0613c0c270884d0307e060f80c190382f070540e09c1c130381f0703a0e0681c0b838161502af8050163f02c7d058ea131c815bb02b750569c12d34253d01a76034d2069640d1e81a390346a068c40cb48193d03272064d40c98858650b07a0e0e42c1a83831056de12dac15b384b63034de069b40d3381a65034c6068fc0d1d81a37034660659c0cb3019650f27e0a4ec149b879330325e121bc243584867090c6161543c1f8283b0506e1a0cc0c178182b0304e0608c3c0f8681b0f02e1a04c15b7bc36b056ce12d8c0d3781a6b764d40699c0d3301a63034b2069240d1f81a3b0346e068cc0cb78196b032ce0658c0cac8193f03276064dc0c998486f0d0d62e19c2431858551707e0a0ec141b868330305e060ac0c13818230303e0606c0c0b8181309adf8159c1637df46b058ce1318ef22d82c57036de06db80db5da36a036ce06d980db184b62036b754d680dab81b560369e06d380da582b4a0368e06d180da1ca342034de069ac0d3381a63034b7249680d2b81a560349e0692c0d2381a43092df185ac5cb384963842b62e55c5ca78294b0528ef450c0c9f8593d03276064e40c9b81935032660e4c40c978192b0324e0648c2437848671d0b4e81585427828470307e060f8441e8182f0305c060885c0f8e81a1702e0c058163784c6b058ce1318c0db784b6b036ce12d8c0da782b4b0368e22d0c253784a6b094ce1298c552782a4b0548e2a90c451f81a3b0346e228cc0c9b0486e090cc2a13814230883e0705c16098273f84e7705afe135ec16bb84d730dad60b59c0e3f84c7e038fa071dc0e3a84c73098e41b1ac363501c670d8cc0717c162d81c57118a606ddc0dbb01b750d6d61ada835b386b660f6be46d7815ad82b5a056ae0ad583da987b520969e12d3825a683a7f074f60e9e81d3b84a76074e60e9ac1d3383a5f054b60a95c1d2983a4f034960691c1d2183a3f0747a0e8ec1d1c83a370746a0e8cc1d188397f092fc0e5ec1cbd03977092ec0e5cc1cb90396b072d40e59c34b30395f172bc0a56c14ad02957052ac0e54c1ca90394f1129c0652c0ca5019470328c0e50c1ca10393f0f27c0e4f4449e0393b072740e4e41c9c039370f26c0e4d45c9a03933072640e4c41c980487f090ee1217c142b8484f0308e120fc241e848370906a0e0a81c13838260702e0e058240a84d6f0dace0b1bc963582c67098c61b16c162b84b6f6e6d63ad9c25b186b5b0d6ae3ad3c15a582b47256860e9bc1d3583a6a074ce2e9981d3183a5b074ae0e93c152582a47074860e8fc1d1d83a37074660e5bc24b70396b072d40e59c5cb303963072c40e56c1cad039570d2ac0e53c5ca70294b052940a51c14a303943072840e4fc449f0393b032740e4dc0c9b0393307264121bc24338a84f0508e2e0fc5c1b8382a0704e0e0981c0b838160b02a0b1bc263582c67098c612dbc25b584b67096c62ad3c15a582b4715686129bc1d3584a67074c61693c152582a4707486168fc1d1d85a370746612598749b0392e090dc121985427028461107c060d82c130297c052f0165d014b807d8805b080b2302d4607a880b50856a00152c14a500b498d09202d2214a400729016510bc2202c6f098d60b19c263184b6f096d612d9c25b18eb4f056960ad1c4da184a6f074d6129a8253384a660b49e0a92c152383a430b47e0e8ec2d1b83a33092de125b8aca78d94e052960a52814a3829462b286365084c9f8893e1d276064e8749b8193613266224c81c978392e090cc135f826b702c7f058fa1f1ec6e3c82c77058eacd1cc6e3882c6f098d60b19c26318eb7f036fa1edec45bc87b77036ea26dcc45b884b6f096d612d9c25b18eb4f056960ad1c4da185a7f0b4fc169f42d3e05a7b0f4f4169e4f13c05a770b4ec169d42d3a05a732b4e4169c5913804a6f094dc129ac253504a67094cc1298c253105a4f0b49c0a92c152502a470548c1690cd12105a3f0b47c168ec0d1d05a370346c168cc45190597f0b2fa0e5ec1cbc859770b2ea0e5cc1cb88496f072d6125a824b384966072c61653c14a58294707286164fc1c9d859370726612198501b0382e0703c139fc273b82d7f05afc0b5f416bb82d7505ae6135c816b58dd6a05ace0b598163b82c76058ea1f1ac6e3507c67218cc0b17c162f04c5d096fe12dec25bb84b73136d63ad9c15af82b5b056ae0ad4c3da781b4d1369622d246da381b450f68622d04253f84a7e094f6129e8253b84a76094e6129c82d359f26a0b4ce16998152f82a5e054b60a968152b82a56054a60a9482d2785a4e0b49a169302d258da4a0b492429202d2385a460b48a169102d2187a420b482609002d1f85a3e0b476068e82d1b81a360b466228c824bf8397b092f4125dc24bb03973072d61659c14af8295b052ae0a54c2ca78594d072960e5242ca385945072860e5042c9f8393b0b26e0e4cc243f8487a090ee121d8142f828570909e121342423848450907e120e8241b890360705e0e0b81c168381f0703c0e04816bf82d7b1baf40b5dc16bb02d7305aca131fc263f0dc7b1b8f4371dc7e3b04c73098e40b19425bf91b7b1d6ee12dcc15af82b5b056ae0ad4c6da781b4d1b69622d246da381b451b68622d04253f84a7e0b4f68c9e82d3b85a76094e6129c8152f82a5e054b60a968152b82a56054a60a9482d2785a4e0b49a169302d258da4a0b4923e9202d2385a460b48a169102d218ca420b482509002d1f85a3e0b476068e82d1b81a360b466228c824bf8397b0d2f4165dc2cbb03973052be0a56c14ab829530b29e165341ca5839490b28e165141ca1839410b27e0e4ec2c9b839331a0ec200d81c170381e03cec135d83eb702c6d1b8d20b1943e3084b69116b2129f8253d04a76094e4169b82d3685a6c0f4d4169a4653405a660b4ca169903d3105a610f4c016938152502a4623484168f80d1d01a3611464125e824bb0596d072d2165941cb0848760306c0e0b81c0f04d6f09ace0b1bc263582c67098c64716c162b81b6f096d606d9c25b188b5b036ae06d3c15a581b4711686129bc1d3584a6a094ce129981d3183a5b0b4ae1693c152582a4707486168fc0d1d81a3707466125bc24b70196b032d41259c0cb304963092c46e56c64ad1b957192ac4653c6ca70294b052940a51c14a3119431b284124fc249f0193b03274064dc0c9b04933092640e4bc1c9704927072460e48824378486a090ce121982427828470907e060dc1c17848270703e0e074240b8381509ade1359c163784c6b058ce1318c8e2d82c57036de12dac0db384b63116b622d680dab8eb560369e0ad2c0da388b43094de129ac0d3501a67034cc5e96cbd2b91a4f054960a91c8d2184a3f0346e128cc24b78496b092d41259c24b3049630b2b64e5682cab859560b29e1653814a5829470b286465082c9f8593e03276064dc2c99889320b25e164b81c95839290b24e1648c44910392107240121bc1c358486a090ce121981c318385b0b0ae1613c14258284707086160fc0c1d8183707066160bc2c170382b070521609c1c1197822070420e080273f84e7705afe135ec16bb84d7323ad60b59c0e3f84c7e038fa071dc0e3a84c73098e4231ac463501c671d8cc0717c162d81c57118a606ddc0dbb01b750f6d622da83db3ae366116be36d7815ad82b5a056ae0ad583da988b520969e12d3825a684a7f094fc129ec253d04a77094ec129cc253905a6b274d41699c2d3305a5f0b4bc0a96c152d02a57054ac1694c8d2905a4f0b49c0692c0d2501a470348c1690c452105a3f0b47c168f42d1e05a3b11474168e5691c05a370b46c168d42d1a05a330f464168c445180497f072f6125e824bb84976072e60e5ac2cb38595f052b60a55c1ca98594f032960651c1ca18593f0b27a0e4ec1c9c859370b26a0e4cc1c988487f090f4121dc243b0485f050ae1213c0c25018470308c120fc241e8483a0906e220d8241aac0340705e0e0b81c168381f0703c0e048163789c6b058ce1318c0db788b6b036ce12d8c0da782b4b0368e22d0c253783a6b0b4ce0e98c2d2782a4b0548e0e90c2d1f81a3707466125bc24b70996b0f2d42659c3cb304963092c44653c6ca70294b052940a51c14a3119431b284064dc0c9b0392f0725c0b1bc4e3582c67098c606dbc45b581b67096c606d3c15a581b4711686129bc4d3587a6a134ce1e998253191a4f054960a91c8d218496f0b2d61659c24b18594f052960a51c2ca18593f0b27c064ec0c9b8593311264164bc2c970392b072521649c2c9186922072420e48024378386b0d0d41619c2c33038630b09e0a12c1423838430b07e060ec0c1b838330b05e160b81c15838290b04e0e08c34110382105afe275ec16bb84d73038fe231ec463d01c77138ec131cc0e3281c5f058b60715c462984b7f096fc22dec45bd08b77136ec12dcc25b901b65116be36d7815ad82b5a056ae0ad5845a988b52094fe129f82d3d89a7a0b4ee169d8253984a720b4be16978152d82a5a054ae0a9582d2991a520b49e169380d2581a4a0348e069182d2188a420b47e168f82d1e85a3c0b476228e82d1caa2380b46e168d82d1a85a340b466228c82d1888a30092fe0e5ec34bd059770b2ec0e5cc2caf8295b052ae0e54c2ca78194b0328e0e50c2c9f8593d072761a4e81c9c839380b26e164d82c9a85934072660e4c44c3b018460c088220d9481a0382e0703c139f83f3d07e7609ce4275d846b701c69058b20ada445ac84a7e134f4169d8253905a6e0b4da169b0653505a69194d0169982d3285a64354c416984d53005a550b4a80a938152502a4605484168f80d1d01a36114641a5e82cbb0596d072d2165941cb085955130ec060d81c170381e09ade2759c163782c6b058ce0b18c162d82c57036de22dac0db384b63116b606d5c0da782b4b0368e0ad0c253783a6b134d41699c2d3303a63074b61695c152782a4b0548e0a90c2d1f81a3b0346e0e8cc24b78496e132d61e5a84cb387966092c6125886cad8c95a1b2ae3255814a78194e052960a52814a3829460328606508149f8293e03276064e80c9b81936052660a4c81c978392e0b24e0e48c1c910486f130d41219c4c330284f0508e220fc0c1b8382f0504e0e07c1c0e888170702a135bc4eb382c6f058d60b19c163182c5b058ae06dbc45b581b67096c622d6c0dab81b4f0569606d1c15a184a6f134d61e9a84d3387a66094c65e96cbd2b81a4f0548e0a90c151f81a3705466125bc2cb58996a0b2ce1659824b18595b272b41655c2cab0294f0529c0a52c14a482947052860a5082ca08593f0b27c064ec2c9c819370b266224c82c98889300b25e164b81c95839290b24e1648c44910392107240121bc1c358986a0b0ce161981c318385b0b0ae0a13c14258284705086160fc0c1d8183707066160bc2c170382b070521609c1c119282207042139fc4f3b82d7f05af60b5dc16b982d6b05ace071fc463d81c77098e6231ac0e3381c5f038ba0b16c162d01c57058ac0715425bf84b7e116f622de845bb89b76096e612dc845b588b6a116ce9cd980daf81b5e036ba0ad3c15a702b4d094fe129f82d3d89a7a0b4ee169d8253984a720b4d64e9a82d3385a66054be0a978152d82a5a054b20a960152b82a56054a60a9482d28992500b49e169380d2581a4a0b492069200d2381a460b486229082d2088a400b47e168f82d1e85a3c0b476228e82d1ca62380b46e168d82d1a85a340b466228c82d1888a30092fe0e5ec4cbd059770b2ec0e5cc1cb585967052be0a56c14ab829530b29e0652c0ca3839430b27e164f41c9d8893a072720e4e02c9b859360b26a164d01c9983931090fe261e8243b89876050be0a15c44278184a0308e06118441f8883d11074220dc441b0a8354a0680e0bc1c170382d0703e0e0781c0904d7a05aec0b594263f04c7a098ec131c8163281b4d1169206d1445a084a7d0b4ea169341d2485a4507482125d82cba8295e052b40a55814a90c94e0f29a325303ca5079490f290365183ca28f9440f2841e5043ca00893e03274064d83c990392e09ace13598263307c5e056de12dac15b384b63056be0ad743dad8cb59056ae0ad543da987b51094de129ac253384a630f4be069743d2d88a590f4ae069543d2987a511d47e0a8ec151b89a33092de1259c1cb18395b072b2164fc149d8293707266164bc1c958592707246135bc26b382c6f058d6131a8163382c66058c60b16c162b82b6f056dc12dac25b502b67056cc0ad8c15b10db5b196b436d5c65ab02b4f0569c1ed34253784a6b094ce1298c4d2d8ea570549e0a92c152382a431b47e068f44d1d88a391b46e068d44d1988a31092de0e5ac24b383963072b61655c14a78294b0528e0a50c249f8493d072760e4e42c9b85935072660e4c42c978392b0b24e0e48c2437848670509e0a11c241f8483d0906e120d42417848270703e0a05c26b784d67058de131ac163384c63468b60b15c25b784b6b096ce12d8c4dad8eb571d69e0ad2c15a389b43094de129b41d3584a670b4ca0e98c1d2d85a570b49e0a92c152383a430b47e0e8ec2d1b83a33092ce125982cb28795b3c2b41e55d10ab1794f4229c0a52c14a5029470528c1e50cc0a10993f1127c1e4ec0c9d0e9370326c1e4cc44990392f0725c1249c1c9183922090de121b42433848650909e0a11c241f848370705e1209c1c0f8381d0902e0e05416bf02d7d05aea135c8163b02c75058bc131740da688b490368a1ed04253d04a760b4ca169341d2485a4507482125f824bd04976092e41659414af0295a052ac0a5483ca70794d0f2981e52864a48c9480f28c4251484a2079420f2821e500449f0193a0326c224c8243b16836 20 1048575 8 255 11 2047 19 524287
def cc_63_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xdb0bfab8ab4096e344dbc4a56e0aac596d5f2ca6659404ca6719c8b4391205150d601a8bd62d7a606f3815d78fb802f6649cc20a95ca7a66533b7166cca0c415942461c2c22553028a200051 0xb5fc16bd98d7a05aee0b5d816b982d65098fe131f87e3d98c7a1f8ee3f1d8263984c72058ca06dfc0dbf01b7bba6f406ddc0dbb01b73096e406d7c0daf01b5b056b406d5c0dab01b53056a406d3c0da701b4d0369806d2c7da501b491f69006d1c0da301b450368806d0c65a101b419e680069fc0d3d81a77034e60697c0d2d81a57034a60693c0d2681a4b034920691c0d2281a4303482125fc34bd8b977092e60a57c14ad82957052a62e53c2ca68694b072922e51c2ca28694307282064fc2c9e8193b03272064dc0c9a8193307262064bc0c958192703246060f80c170801609af40b5d816b284c7e098f4131d8263902c65036fa06dd40da681b490368a06d040d3b01a75054bc0a968152b02a521949c1e934652607a4a0f4921e9207d2307a451f4881e9083d2087a400347c165341ca48594507282164b41c9485925072421e0580eb381d66098cc1f17815b784b6b056ce12d8c15af82b5d0f6b632d6415ab82b550f6a61ed440d3781a67034c60696c0d2c81a3f03476068dc0d198496f092d61259c24b18795f0b2ba1a56c1cac879570b2aa1a54c1ca88793f052760a4dc34998192f032560649c0c9184d6f09ace0b1bc163584c6a058ce0b1980e3182c5b058ae0adbc15b701b6b036d406d9c0db301b63036c436d6c65ad0db57196ac0ad3c15a707b4d034de069ac0d3381a63034b60695c0d2781a4b0348e0690c0d1f81a3d03476068e40d1b81a3503466068c424b78496b092ce1258c3cad879570529e0a52c14a3829431727e164f43c9d839391726e164d43c99839310325e064ac0c9381923090de1219c1427828470907e120f4241b848350305e0609c240f8481709ade1359c163784c6b058ce1318eea2d82c57036de06db40db581b67036ca06d8c0dad89b5a036ae06d580da781b4b0368e06d0c0d3381a66034ca1e96ec12d07a57b84ac5e93ed92702a4b054940a91c152307a43a6484068fc0d1f01a3703466068c824b78496b092ce1258c3cad879571729e0a52c14a3879430327e064ec0c9b819330f25e164b43c95839290f24e164943c9183921090de121b4243384865090b4ec1582427828470307e060dc24178482d0904e12094240f8481a0902e1c05816bf02d7d05aea135c8163b02c75058bc131740db281b4d0369206d140da084a7e094f4129d8253901a65054bc0a968152b02a520f49c5a9343d2610a4a1949232920852310a45214881e908652087a400b29a0e5242ca2839410b25a0e4a42c9283921058de131ac163384c63036de06d9c0db181b4f0369606d1c0da184a67094cc1e9943d2a87a4f1b49c0a92c152502a470548c1e90c3d2101a3f0347c125bc24b584967092c61e53c14a5829470d286064fc0c9d81937032661e4bc2c968692b072521e49c2c928692307242135bc3eb704d6d056de0adb43db587b69056ce0ad943db18db61056be12d6c15ab84b53034de069b40d2f81a5b034a6068fc0d1d81a37034661e5bc2cb68696b072d21e59c2cb286963072c21257c24ad84957092a61e4fc149d829370d266064bc0c9581927032460b1bc163582c67058c612dbc25b70db6b0f6d436d9c3db304b63096c40ad3c15a70cb4d034de069ac0d3381a63034960691c0d2181a370346a125bc34b58b967092c60a53c14a582947052862e4fc2c9e8693b072722e4dc2c9a8693307262064bc0c9581927032460b1beca3582c67098c606dbc0db581b67036c606d540da781b4b0368e06d0c253784a6e194d7609a8b533d7266094c6129880d2aa1a4fac49c0a92c152502a470548c3290e79210496f0d2d62e59c24b18b94f052960a51c34a18193f03276064dc0c998b92f0b25a1a4ac1c948b9270b24a1a48c1c9084d7e09adc0b1f8163e82c7c058f20b1d4a63902c711b8e006df40dbc81b75036e206d340da294a7e294fa569f03d3d0da790f4f01e9d8a53a87a74294e4369c46d3804a6e094da129b0253504a66294ca1e990253114a55194a8069380d2681a3e0b2fa0e5e42cba83971052921a5042c96839290b24a0e48426b784d67058de071ac163382c63058b60b15c0db781b6b036ce06d8c0dad81b570369e06d2c0da381b43094ce129983d3287a5b0f4b41e95c3d2b02a4f0549c1e9340d1f81a3e0346e068cc0d190496f092d61259c24b18795b0f2ae0a53c14a58294705286064fc0c9d81937032661e4bc2c968792b072521e49c2c928792307242121bc24338284f0508e060fc0c1b8482f0905a1209c24128481f0902e129b0652a0de7e09cfb495f4a6ba84d6d29aca0b1f40e3c81c75038e20b1a4163081b7d036f206dd40db881b4d0368a129f8253e84a7c094dc129a86d3487a68094c41298425300da5a9a4ac069380d2681a3e0346c068c82cbe839790b2ea0e5c424b68b96505292365045c96879291724a1e484243e828750909a0a11424168282509ade1f5b826b687c6f0f8da1f19c3e3284c5f098ba1315c3e2a82b6f056da06dac0db481b67036ca06d8c0db082b5f056b60ad640dab82b53056a20ad2c15a381a6f034da069ac0d3481a67034ca0698c0d3081a5f034b60695c0d2981a4b0348e068fc0d1d81a37034661e5bc2cb68796b072d21e59c2cb287963072c21257c24ae8495b092ae1e55424a98794b0f28e0a4fc149d8293705266064bc0c958192703246121bc243682867050ca1217c242b8283f0506e060bc0c138481f0902e0b1bc163582c67058c606dbc0db581b67036c606d3c0da581b47094de129b8653587a6a194ce1e998253184a62194aa0a93c15270ca4d0347e068f824b78696b172ce1258c14a78294b0528e0a50c0c9f8193b0326e064cc5c978592d0d2560e4a45c93859250d2460e484253e07a74094b0135f03eb404d60198f853190273f4e67a29cec139c8a6bb0dd6e038d20b1640db481b4d0368a129f86d3d4d276094e436964652c01a4e0349a068f82cb6839690b2ca0e5845caa829490d2822e4b434948b9250d242135bc26b70cd6b0fad43359c3eb304d6309ac433198662f02b6f056d60ad9c15b181b5b036b20ad240d3781a6b034ce0698c0d2d81a590347e068ec0d1b8496f0d2d62e59c24b18b95f0b2ba1a56c1cac8b9570b2aa1a54c1ca88b9450527e0a4ec149b829330325e064ac0c938192309adf5159c163782c6b058ce0b18c162d82c57036de06dac0db381b63036b606d5c0da781b4d0369606d1c0da281b43094de129b86d35d326aa24cf40998253184a621b4b73c96a612bcb2560349e069380d2681a3f0347c068dc0d1981a32092de4a5ac5cb384963252b62e55c14a78294b052920a51c14a1c11410327e064ec0c9b819331725e164b46c95839291724e164946c9183921090de1219c14278a84d0508e0a1140c1f818371105e220b41413828251503e2a05c163789c6b058ce1318c0db781b6b136d406d9c0db301b630369e06d2c0da381b43094de229ac453384a63034aa2293c152582a4711486125bc34b589967092c62e53c14a5829470d286064fc0c9d8193703266224bc3495889270d246060f844170601609ade1359c163784c6b058ce1318c362d82c57036de06dac0db381b63036b606d5c0da781b4b0368e06d0c0d3781a6e094d6129a80d3381a66034c606988352d86a5a0d4ae1a95895278da4e054960a928152382a4625486369080d1f81a3e0346e068cc0d190396f032d60e59c1cb18395b072ae0e53c14a58294707286064fc0c9d8193703266064bc0c968192b032520649c0c928392307242121bc24338484f0508e060fc0c1b8482f0905a0e09c1c128381f0703a0e05c240a84d6f09ace0b1bc263582c67098c61b16c162b81b6f036d612da80db381b66036c606d6c0dab81b4f0369606d1c0da181a6f034d60699c0d3181a5b0d4b40695c0d2b01a4f034960691c0d218396f032d60e59c1cb18395b072ae0e53c14a58294707286064fc0c9d819390326e064cc1c988192f032560649c0c918486f090d61219c342d8685a0d0ae1a15894278284b0508e4a10c0c1f8183e03076060e40c1b81833030640e0c41c180182f0305c060ac0c148182703046060884c108381f0702e0e04c273f84e7705afe135ec16bb84d730dad60b59c0e3f81c7e038f6131e80e3b81c76038e6131c80e3586c6a038ce071980e2f81c5e038b60b1680e2b81c56038a64b1480dbf81b7b036ee06dcc0db586b6a036ce06d980daf81b5b036ae06d4c1d3f84a7e074fa0e9dc1d3a83a73074e40e9ac1d3503a670d4cc0e97c152d82a57074a60693c1d2681a4b034920691c0d2281a4307482068fc0d1d81a37034660e5dc24bb03975072d60e5a81cb386966072be4a57814ad8295a052ae0a5581ca9839520329e065381ca6c814c03296065280ca4819480328e065180ca28194403286065081ca0839400327e064f81c9e8893c03276064e80c9b819360326a064d00c99819320725e0e4b81c968487f090ee121a834330485f050ae0613c0c270484d0307e060f80c190382f0705a0e0a81c13838260904a100901c0f8381d070340e05c1c0b048158e0280f9f81f3e82c7d258f20b1d4963881b7e036fa06df03dbd01b790f6f006dd80dba81b742d6e406dc4b5b801b6e096d406d9825b101b4e0569406d1895a101a7d034f2069d40d388397d072d20e5841c9e819390326a0e4c40c1f0182e0702c0b1bc963582c67098c606dbc0db581b67036c606d3c0da581b4703686129bc25371ca6b0f4d47299c3d3304a63094c44a93c6d2702a4b054940a91c152312a431b484068fc0d1f0396f072d60e59c1cb18394f052960a51c1ca18193b0326e064cc0c9381925058de4b1ac163384c63036de06dac3db501b67036cc06d8c0da781b4e0369606d1c0da192b42034de069ac0d3381a630349e0692c0d2381a43072de0e5ac1cb503967172cc0e58c1ca78294b0528e0e50c0c9f8193b03272064dc0c99839310325e064ac0c9381923090de5e1acbc33848632509e0a12c1423928430307e060f80c1d818390306e060cc0c190383107060060bc0c170182b030520609c0c11818222f0422208016bf92d7b05aee135cc0e3f81c7e038f61f1e80e3b81c76038e6131c80e2f81c5e038b60b1680e2b81c56038a64b1480dbf81b7b036ee06dcc0daf81b5b036ae06d4c1d3f83a7b074f40e9dc5d3b03a73074ca0e97c152d82a57074a60693c1d2681a4b034920691c0d2281a4307482068fc0d1d81a37034660e5fc24bf0397b072f40e5de28bb03973072e40e5941caf9295e052b60a56814ab82956072a60e5480ca78194e0729b105300ca58194a03292065200ca3819460328a065100ca181942072820e5000c9f8193e03276064e80c9b8193603266064c80c270183e0704c0e05a180a04d6f0dace071bc0e3581c67038c60716c0e2b84b6f1b6d636d9c25b186b5b0d6ae06d3c0da381b43074de0e9ac1d3383a63074b60e95c0d2781a4b0348e0690c1d1f83a3d074760e8e81d1b8ba360746a068cc1cb78396b072ce0e58c1cad839570329e0e5340ca58194a0328e065180ca281944032860e4fc1c9e8193b03274064dc0c9b0193503268064cc14978292e0525a121bc24338184f0308e220fc141b8382f0704e0e07c1c0e8381a0702e0e058540a83e7e07cfa1b5f436ba84d6d0daca0b1f4163c82c75058e20b1a4163081b7e036fa06df03dbd01b790f6f006dd80dba81b74416e406dc4e5b801b6e036da06db025b501b66036ca06d9025b106b5a036ac06d3815a501b4605684069f40d3c81a75034e2069b40d3286a5a034ac0e5f414bc82975052e20e5a41cb08393d03272064d41c988487d090ea121b424328485a0d0ac060f8241e8182e030440e0681c0b04d6f0dace0b1bc163582c67058c60b16c162b81b6f036d606d9c0db181b5b0d6b406d5c0dab01b4f0369606d1c0da184a6f094dc629ac3d3518a670f4cc1298c253106a5b0d4b41a95c352b01a4f0349c0692c0d2501a470348c0a90c152101a3f0347c068dc0d1981a32072de0e5ac1cb383963072b60e55c14a78294b0528e0650c0c9f8193b0326e064cc0c978192d03256064a40c9381925052460a4842437848670d0b41a1581427828470307e060dc44178882d0704e0e0941c0f83817 19 524287 8 255 11 2047 19 524287
def cc_63_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xca265848fef2175bc28af683534ba9214cfb2997087238aa3611454188783106889f696bae3f6a0bcc88b96ea2aae2f5005c938c903241e620310bc4f9288e909190421220378ac40ae80081 0x4c6e02b6f02b6d07b6b6b36902b6702b65813638036102b5f04b5b02b5704b530ea6f01a6d07a6b08a6907a6701a6509a6308a6104a5f04a5b04a5704a530ea3f02a3b02a3709a330796f0596d0696b03969079670596506963039610495f0495b04957049530b93f0293b02937069330992f0692b0b927069237f06e04e7e04e7602c7f02c7e02c7d02c7702c7502c7304c7202c6902c6502b7702b7602b7507b696b36810b6510b6402b4f02b4e04b4d04a7f04a7b04a7704a7308a6901a6502a4f02a4b02a4702a4307a3f01a3d09a3b08a390ea3701a3507a3308a310497f0497b049770497303969059650294f0294b02947029430793f0593d0693b03939079370593506933039310992f0692b0b92706923048763c02601d6701d660cc5e02b6f04b6b02b6704b6302b5f02b5d0cb5b0cb5902b5702b550cb530db5101a6f01a6704a6304a5b04a5901a3f02a3b01a3708a330496f0496b04967049630b95f0595d0695b039590b9570595506953039510b93f0293b02937069330892f0192b0192706923048660785e04d6602b6f04b6b02b6704b6311b5901a6f01a6704a6308a5901a3f02a3b01a3708a33019670196607959139491193f0293b02937119330492f0486f0486b0486704863058550b83f0283b02837068330882f0182b01827068230b81f0681b0b8170681304e7e04e7602c7f04c7b02c7704c7311c6902c6501b7f04b7e01b7d01b7701b7504b7304b7208b6901b6501b4f02b4b01b4708b4301a7701a7601a7507a6908a6808a657c26408a4f11a4e02a4b02a4a02a4702a4607a4308a4204a3f04a3e04a3d0497f0497b049770497303969059650b94f0294b02947069430893f0193b01937069330792f0592d0692b03929079270592506923039210487601836088267b02404d6f04d6e09d6b07d6a09d6707d6604d6304d620cc5e02b6f02b6b02b6702b6301b5b01b5901a6f08a6b01a6704a6302a5b02a5901a3f02a3b01a370496f0696b09967049630b95f0595d0695b039590b9570595506953039510293f0293b02937029330892f0192b0192706923098660c85e04d6f09d6b09d6704d6309c6608c5e02b6f02b6b02b6702b6301b5b02b4901a6f08a6b01a6704a6302a5b08a4901a3f02a3b01a370496f0696b09967049630b95f0695b0b95706953059450293f0293b02937029330892f0192b0192706923098660c85e0182609d6602b6f02b6b02b6702b6302b5901a6f08a6b01a6704a6308a5901a3f02a3b01a370496f0996b0796a09967079660496308959139490193f0292f0486f0686b0986704863058550283f0283b02837028330882f0182b01827068230b81f0681b0b8170681304e7e09e7602c7f02c7b02c7702c7302c6902c6501b7f08b7b01b7704b7308b6901b6501b4f01b4d02b4b02b4a01b4702b4601b4504a7f04a7e08a7b08a7a08a7709a7604a7304a7208a6908a6808a657926408a557825401a4f01a4e01a4d02a3f02a3e02a3d0497f0697b099770497303969059650294f0294b02947029430893f0193b01937069330892f0592d0692b03929089270592506923039210987601836088267702404c6e04c5e04b6e02a6f04a6b02a6704a6302a5f04a5b02a5704a530496f0196d0496b0496701965049630495f0495b04957049530e92f0292b02927099230486f0486b04867048630485f0485b0485704853058450b82f0282b02827068230981f0681b0b8170681304d6e7e56602b6f7d36b02b6704b636935902b5504a6f7a26b0ea6704a6308a5901a550ea3f02a3b02a37762330496f0696b0b9670496303959059550b93f0293b02937069330b92f0692b0b92706923750663a02602b5f04b5b02b5704b5304a5f04a5b04a5704a5308a3f02a3b02a3708a330495f0495b04957049530693f0293b02937069330692f0692b069270692302b5f04b5b02b5704b5301a5f01a5b01a5701a5301a3f01a3b01a3701a330495f0495b04957049530693f0293b02937069330192f0192b019270192302c6f04c6b02c6704c6304b6f04b6b04b6704b630ab4f02b4b02b470ab4304a6f04a6b04a6704a6306a4f02a4b02a4706a4306a3f06a3b06a3706a330486e048660a84e028460883e7303c01836720340382e0582602c6f02c6b02c6704b6f04b6e02b4f02b4e0db4d04a6f04a6b04a6704a6302a4f02a4b02a4702a430da3f01a3d09a3b08a390da3701a3509a3308a310496f0496b04967049630294f0294b02947029430b93f0593d0693b039390b9370593506933039310992f0692b0b927069230d83602b6f02b6d02b6b17b6a02b6702b6602b6502b6302b5f02b5b02b5702b5302a6f02a6d0aa6b07a6a02a6702a6602a6502a6402a6304a5f04a5b04a5a04a5704a5604a530e96f0996b0e967099630495f0495b04957049530293f0293b02937029330a92f0992b0a927099230b86f0686b0b867068630485f0485b04857048530283f0283b02837028330a82f0682b0a827068230981f0681b0b8170681304d7e04d6e02c7f02c7d02c7b02c7902c7702c7502c7302c7102c6f02c6b02c6702c630ab7f0ab7e0ab7d0ab7c0ab7b07b7a0ab796b3780ab7707b760ab750ab740ab7315b720ab717037004b6f04b6e04b6b04b6a04b6704b6604b6304b620ea7f01a7d09a7b08a790ea7701a7509a7308a7104a6f04a6b04a6704a6302a4f02a4b02a4702a430aa3f01a3d09a3b08a390aa3701a3509a3308a310b97f0597d0697b039790b9770597506973039710496f0496b04967049630294f0294b02947029430a93f0593d0693b039390a9370593506933039310992f0692b0b927069231987e6f07c028460283604d6704d6604c6607c5e02b6f02b6702b6302b5b02b5902b4904a6f04a6b04a6704a6307a5f01a5d07a5b08a5907a5701a5507a5307a5102a3f02a3b02a3702a330496f0496b04967049630795f0595d0695b03959079570595506953039510293f0293b02937029330792f0692b079270692304d6f04d6702c6f02c6b02c6702c6302c5b02c5704b6704b660ab6507b5b6b35a07b576d35602b4f02b4e04b4d04a6f04a6b04a6704a6309a5b0ea5702a4f02a4b02a4702a4307a3f01a3d09a3b08a390ea3701a3507a3308a310496f0496b04967049630795b079570294f0294b02947029430793f0593d0793b03939079370593507933039310992f0792b0b927079230486f028670284f028470483710836048350482f048270481f0481702c6f02c6702c6304b6704b6607b6507b5502b4f02b4e07b4d04a6f04a6b04a6704a6302a4f02a4b02a4702a4307a3f01a3d07a3b08a3907a3701a3507a3307a310496f0496b04967049630294f0294b02947029430793f0593d0693b03939079370593506933039310792f0692b07927069230783604d6f07d6e04d6d02b6f02b6d02b5f02b5b02b5902b5302b5107a6f01a6d07a6b07a6907a6701a6507a6308a6104a5f04a5b04a5704a5302a3f02a3b02a3702a330796f0596d0696b03969079670596506963039610495f0495b04957049530293f0293b02937029330792f0692b079270692302c6f02c6b02c6702c6304b6f04b6e0cb6b6b36a16b676a36604b6304b620ab5504a6f11a6b0ea6704a6302a4f02a4b02a4702a430ca3f01a3d11a3b08a390ea3701a350ca3308a310496f0696b0b967049630294f0294b02947029430b93f0593d0693b039390b9370593506933039310b92f0692b0b927069230f83604d6f6e56702c6f02c6b02c6702c6302c5b02c5704b6f04b6e0ab6b6c36a0ab670ab6604b6304b620ab5b6935a0ab570ab5604a6f11a6b0ea6704a6311a5b0ea5702a4f02a4b02a4702a430aa3f01a3d0aa3b08a390aa3701a350aa3308a310496f1296b0b967049631295b0b9570294f0294b02947029430a93f0593d0a93b039390a937059350a933039310b92f0e92b0b927119230486f048670284a02847028460283702836028350a82f0a8270a81f0a81702c6f02c6b02c6702c6304b6f04b6b04b6704b6302b4f02b4b02b4702b4304a6f04a6b04a6704a6302a4f02a4b02a4702a430ba3f0ba3b0ba370ba33029460486e048660284e0883e018360382e0582602d7f09d7b02d7704d7301c7f08c7b01c7704c7301c5f02c5b01c5708c5304b7f04b7e08b7b07b7a08b7707b7604b7304b7208b5f0eb5e02b5b02b5a02b5702b5608b5308b5203a7f03a7b03a7a03a7709a7603a7303a6503a5f02a5b02a5703a5303a4f01a4b01a4703a4303a3f03a3d03a3b03a3903a3703a3503a3303a310397f0497e0397b0397a03977099760397303972039650395f1195e0295b0295a029570295603953039520394f0894e0194b0194a019470194603943039420393f0893e0393d0893c0393b0393a03939039380393708936039350e93403933039320393103930018460183604d6f09d6702c6f09c6b02c6704c6311c5b02c5701b6f08b6b01b6704b6308b5b08b5a01b570eb5601b4f02b4b01b4708b4304a6f04a6e08a6b08a6a08a6709a6604a6304a6208a5b08a5a08a570ea5608a4f0ea4e02a4b02a4a02a4702a4608a4308a420496f0996b09967049636615b0b9570b94f0294b02947119430893f0193b01937089330892f0592d0892b03929089270592508923039210486f048670a84f028470183a01837018360182701826018250b81f0b81702c6f04c6b02c6704c6301b6f01b6b01b6701b6301b4f01b4b01b4701b4304a6f04a6b04a6704a630aa4f02a4b02a470aa4301a3f01a3b01a3701a330193e0b9260486e048660a84e02846018360382e0582601a7c01a7801a7402a7013d8802d8402c8c01b8c07b8801b8415b8002b5814b5001b4c6334801b4414b4008a4801a441784402c6f04c6b02c6704c6301b6f01b6b01b6701b4f01b4b01b4701b4301a6f01a6e15a4f0da4e02a4b02a4a02a4702a4615a430da4201a3f01a3e0496f0496b04967049630b94f0294b02947069430193f0193b01937019330b92f0592d0692b039290b92705925069230392104d7e04d6e02c7f02c7d13c7b18c7902c7702c756247318c7102c6f04c6b02c6704c6301b7f01b7e01b7d01b7c01b7b07b7a01b795837801b7701b7601b7501b7401b7315b7201b716137001b6f01b6e01b6b04b6a01b6701b6601b6304b6201b4f01b4e01b4b02b4a01b4701b4601b435434201a7f01a7d01a7b01a7901a7701a7501a7301a7101a6f01a6b01a6701a6301a4f01a4b01a4701a430b97f0597d0697b039790b9770597506973039710496f0496b04967049630b94f0294b02947069430193f0593d0193b01939019370193501933039310192f0192b01927019230183e0182e0a01604e7f04e7702d7f02d7e02d7d02d7702d7502d7304d7202d6b18d6a02d6702d6602c7702c7602c7510c6b18c6a10c6710c6602c5f02c5e04c5d01b7f01b7e01b7b04b7a01b7701b7601b7304b7201b6b5936a01b6701b6601b5f01b5e01b5b02b5a01b5701b5601b5302b5201b4f01b4e01b4d01b4c01b4b10b4a01b4910b4801b4701b4601b4501b4401b4307b4201b415334001a7f01a7b01a7701a7301a6b09a6a01a6701a6601a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a410497f0497b04977049731296b0b9670295f0295b02957029530b94f0594d1094b039490b9470594510943039410193f0593d0193b01939019370193501933039310192f0192b01927019230487f048770486a3c0660285f028570484f0484d04847048450183f0183e0483d0182f0182e018220481f0481a0481709016 19 524287 8 255 11 2047 20 1048575
def cc_63_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x7b35274a696e9616d1186745d6383c5d3655a0335742c512624ca484a92144a5f41d2d3d8453776132b4c2df4c28a55206841ba4c1a21818919167221373010c2b0cd3f0ad2008b22065260333200033 0x9d6f04d6e0cd6b07d6a0cd6707d6609d6304d6206c6f06c6a06c670cc6606c5f0cc5e06c5d02b6f02b6b02b6702b6301b5b01b5901b5701b5301b5102b4b02b4901b4702b4101a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4b01a4701a3f01a3b01a3701a330596f0396b05967039630595f0595d0295b02959029570295502953029510394b059470293f0293b02937029330192f0192b01927019230986f0b8670b85f0b85d0b8570b8550684d0b8450283f028370182f018270381f0581709d6f06d6ba756706d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4701b4501b4309a6f04a6e0da6ba626aa4267a326609a6304a6206a5f0da5ba225a9f2579e25606a5301a4f01a4e01a4d01a3f01a3e01a3b01a3a01a3701a3601a3301a320596f0396b05967039630595f0395b05957039530294f0594d0294b0294702945029430193f0193b01937019330592f0592d0292b02929029270292502923029210986f0a86b0b867098630685f0a85b0b857068530284f0284b0284902847028430b8410183f0183b01837018330b82f0b82d0a82b0b8270b8250a8230381f0581b058170381309d6f06d6bb356706d6302c6fb246b02c6709c6302c5fb145b02c5706c5301b6f01b6e01b6bad36a01b6701b6601b6304b6201b5f01b5ba835a01b5701b5601b5301b4f01b4e01b4b02b4a01b4701b4601b439d34201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3e01a3d0596f0396b05967039630595f0395b05957039530594f0294b02947039430193f0193e0593d0192f0192e0192b019290192301922039210986f0b86b0b867098630685f0b85b0b857068530b84f0284b028470b8430183f0b83d0183b0183701835018330182f0182b01827018230381f0581b058170381302b5f04b5b02b5704b5301a5f04a5b01a5704a5301a3f02a3b01a3708a330395f0395b03957039530393f0293b02937039330392f0192b019270392304d6f06d6702c6f09c6b02c6704c6306c5b02c5701b6f08b6b01b6704b6306b5b01b5701b4f02b4b01b4708b4303a6f03a6b03a6703a6303a5b03a5703a4f02a4b02a4703a4303a3f01a3b01a3703a330496f0496e0996b0996a099670996604963049620695b0695a06957069561194f1194e0294b0294a029470294611943119420593f0593e0193708933059320192f0192e0392703923019220486f0986e0986a0486709866098620685e0685a06856068520a84f1184e0284a02847028460b8420883f0883e0183a0183701836088320382f0382e0382a0382703826038220381f0381e0381d06c5f06c5b06c5706c5302b5f09b5b02b5709b5302b4f06b4b02b4706b4301a5f08a5b01a5708a5301a4f06a4b01a4706a4301a3f02a3b01a3708a330395f0395b03957039530394f0394b03947039430393f0293b02937039330392f0192b01927039230985f0985b09857098530684f0684b06847068431183f0283b02837118330582f0182b01827088230181f0381b038170381306d6f06d6b06d6706d6302c6f09c6b02c6709c6302c5f06c5b02c5706c5301b6f08b6b01b6708b6301b5f06b5b01b5706b5301b4f02b4b01b4708b4303a6f03a6b03a6703a6303a5f03a5b03a5703a5303a4f02a4b02a4703a4303a3f03a3d01a3b01a3a01a3701a3603a350396f0496e0396b0396a039670996603963039620395f0395b0395a0395706956039530394f1194e0294b0294a029470294603943039420393f0593e0393d0192f0192e0192d0986f0986b09867098630685f0685b06857068531184f0284b028470b8430883f0183b01837088330382f0382b03827038230381f0381d0381b0381a9b01803817038169a015990140381304c6e04c5e02b6f02b6d0cb6b10b6902b6702b6510b6310b6102b5f04b5b02b5704b5309a6f01a6d09a6b08a6909a6701a6509a6308a6104a5f04a5b04a5704a5309a3f02a3b02a3709a330b96f0596d0696b039690b9670596506963039610495f0495b04957049530b93f0293b02937069330992f0692b09927069230485603d6f03d6d02b6f02b6d10b6b0db6902b6702b6510b630db6102b5f04b5b02b5704b5309a6f01a6d09a6b08a6909a6701a6509a6308a6104a5f04a5b04a5704a5309a3f02a3b02a3709a330396f0396d0395f0395b039530393f0293b02937039330392f0392b03927039230485602c7f04c7b02c7704c7302c6f02c6d04c6b10c6902c6702c6504c6304c6104b7f04b7b04b7704b7304b6f01b6d04b6b08b6904b6701b6504b6304b6109b4f02b4b02b4709b4303a7f03a7b03a7a03a7704a7603a7303a6f03a6d03a6b03a6a03a6903a6803a6704a6603a6505a6403a6303a6103a5503a4f02a4b02a4703a4303a3f03a3b03a3703a330397f0497e0397b0397a039770497603973039720396f0496e0396d0496c0396b0396a03969039680396704966039659616403963039620396103960039550394f1094e0294b0294a029470294603943039420393f0893e0393b0193a03937019360393303932048760486604c6f04c6704c5f04c5d04c579745502b6f04b6b02b6704b6302b5f02b5d04b5b10b5902b5702b5504b5304b5110b4b02b4704a6f04a6b04a6704a6304a5f01a5d04a5b08a5904a5701a5504a5304a5109a4b09a4709a3f02a3b02a3709a330496f0496b04967049630495f0495d0495b03959049570595504953039519514b0b9470b93f0293b02937109330992f0992b09927099230486a04867048660485704856048550483f028370482f048270481f0481702c6f04c6b02c6704c6304b6f04b6b04b6704b630ab4f02b4b02b4709b4304a6f04a6b04a6704a630aa4f02a4b02a470aa4309a3f0ba3b0ba3709a330496e0b926048660a84e028460883e018360382e0582602c7f02c7d02c7b02c7902c7702c7502c7302c7102c6f02c6b04c6a02c6702c6602c6302c5504b7f04b7e04b7d04b7c04b7b04b7a0cb796b37804b7704b760fb750fb7404b7304b7204b7104b7004b6f04b6e04b6b04b6a04b6704b6604b6304b6202b5504a7f01a7d04a7b08a7904a7701a7504a7304a7104a6f04a6b04a6704a6302a4f02a4b02a4702a430ea3f01a3d09a3b08a390ea3701a3509a3308a310497f0497d0497b03979049770597504973039710496f0496b04967049630294f0294b02947029430b93f0593d0693b039390b9370593506933039310992f0692b0b927069230487e0486e0d01604d6f07d6e04d6d02b6f02b6d07b6b07b6902b6702b6507b630db6102b5f04b5b02b5704b5307a6f01a6d07a6b07a6907a6701a6507a6308a6104a5f04a5b04a5704a530ea3f02a3b02a3709a330396f0396d0395f0395b039530393f0293b02937039330392f0392b03927039230786e02b6f04b6b07b6902b6704b6304b6102b5f04b5b02b5704b5304a6f01a6d04a6b04a6701a6504a6304a5f04a5b04a5704a530ea3f02a3b02a3709a330396f0396b039690396703963039610395f0395b0395a0395704956039530393f0293b02937039330392f0392b03927039230486f0486e0386b0386903867038630386203861038600485f0485e0485b07859038570485304852048511283f0283b02837128330982f0e82b0e8270982302c7f02c7d04c7b07c7902c7702c7504c7304c7102c6f04c6b02c6704c6304b7f01b7d04b7b07b7904b7701b7504b7304b7104b6f04b6b04b6704b630eb4f02b4b02b4709b4303a7f03a7d03a7b03a7903a7703a7503a7303a7103a6f03a6b03a6a03a6704a6603a6303a5503a4f02a4b02a4703a4303a3f03a3b03a3703a330397f0497e0397d0497c0397b0397a039790397803977049760397591174039730397203971039700396f0496e0396b0396a03967049660396303962039550394f1294e0294b0294a029470294603943039420393f0893e0393b0193a039370193603933039320487e0486e03826038169001404d6f07d6e04d6d06c6f06c6d06c6706c6504c5f04c5702b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5302b4b02b4707a6f01a6d07a6b07a6907a6701a6507a6308a6104a5f04a5b04a5704a5306a4b06a4702a3f02a3b02a3702a330396f0396d0296b02969029670296502963029610395f0395b03957039530394b039470293f0293b02937029330392f0392b03927039230486f0786e0486d0485f028570484a068460283f028370482f048270381f0381703d6f03d6e03d6703d6303d6206c6f06c6704c5f04c5d04c5706c5502b6f02b6b02b6702b6302b5f02b5b02b5902b5702b5302b5102b4b02b4707a6f07a6b07a6707a6304a5f01a5d04a5b04a5701a5504a5306a4b06a4702a3f02a3b02a3702a330396f0296b02967029630395f0395b039590395703953039510394b039470293f0293b02937029330392f0392b03927039230486f0786e03867048620485f0485e0485d0484a068460283f028370482f048270381f0381a038170381604c6f04c6d04c6706c6504c5f04c5702b6f02b6b02b6902b6702b6302b6102b5f02b5b02b5702b5302b4b02b4704a6f01a6d04a6b04a6701a6504a6304a5f04a5b04a5704a5306a4b06a4702a3f02a3b02a3702a330396f0396b039690396703963039610395f0395b03957039530394b039470293f0293b02937029330392f0392b03927039230486f0486e0386b0386903867038630386203861038600485f0485e0485b07859038570485304852048510684b0684a06847068460283f02837028330982f0e82b0e827098230281f028170281304d7f04d7d04d7706d7504d6f04d6702c7f02c7d02c7b02c7902c7702c7502c7302c7102c6f02c6b02c6702c6302c5b02c5704b7f01b7d04b7b07b7904b7701b7504b7304b7104b6f04b6b04b6704b6306b5b06b5702b4f02b4b02b4702b4303a7f03a7d03a7b03a7903a7703a7503a7303a7103a6f03a6b03a6703a6303a5b03a5702a4f03a4d02a4b02a4a02a4702a4602a4503a3f03a3b03a3703a330397f0497e0397d0497c0397b0397a03979039780397704976039758e174039730397203971039700396f0496e0396d0496c0396b0396a0396704966039658d16403963039620395b0395a03957069560294f0294e0394d0393f0893e0393b0193a039370193603933039320292f0292e0292d0487f0487e0487d0486f0486e048620485a068560284f028470483f048370382f0382a03827038260381f0381d0381a0381703816048158c01404c6f04c6d04c677e46504c5f04c5702b6f02b6d04b6b6c36902b6702b6504b6304b6102b5f04b5b02b5704b539234b02b4704a6f01a6d04a6b08a6904a6701a6504a6304a6104a5f04a5b04a5704a5309a4b0ea470ea3f02a3b02a3709a330496f0496d0496b03969049670596504963039610495f0495b04957049538f14b0b9470b93f0293b029378b1330992f0e92b0b927099230486f0486e0486d0485f0485e048520484a750460483f028370482f048270481f0481a048170b01602b5f04b5b02b5704b5304a5f04a5b04a5704a5309a3f02a3b02a3709a330395f0395b03957039530393f0293b02937039330392f0392b039270392302b5f04b5b02b5704b5304a5f04a5b04a5704a5309a3f02a3b02a3709a330495f0495b04957049530593f0293b02937059330592f0592b05927059230485602c6f04c6b02c6704c6304b6f04b6b04b6704b6309b4f02b4b02b4709b4304a6f04a6b04a6704a630aa4f02a4b02a470aa4309a3f09a3b09a3709a33049660486e0a84e028460883e018360382e8902c058268802402b6f02b6d07b6b0fb6902b6702b650fb630fb6102b5f04b5b02b5704b530ea6f01a6d07a6b08a6907a6701a6509a6308a6104a5f04a5b04a5704a530ea3f02a3b02a3709a330696f0596d0696b03969069670596506963039610495f0495b04957049530693f0293b02937069330692f0692b069270692301d6701d6602b6f04b6b02b6704b6302b5f02b5d07b5b0db5902b5702b5507b5307b5101a6f01a6704a6304a5b04a5901a3f02a3b01a3708a330496f0496b04967049630695f0595d0695b03959069570595506953039510693f0293b02937069330692f0192b019270692304d7e04d7602c7f04c7b02c7704c730fc5902c5501b7f04b7e01b7d01b7701b7504b7304b7208b5908b5801b5501b5401b4f02b4b01b4708b4301a7701a7601a7507a5908a5807a558525407a4f0fa4e02a4b02a4a02a4702a4607a4307a4204a3f04a3e04a3d0497f0497b049770497303959059550694f0294b02947069430693f0193b01937069330692f0592d0692b039290692705925069230392104c6e8646602b6f0fb6b02b6704b630fb4902b4504a6f8426b0ea6704a6308a4901a450ea3f02a3b02a370fa330496f0696b069670496303949059450693f0293b02937069330692f0692b069270692302c6f04c6b02c6704c6304b6f04b6b04b6704b630ab4f02b4b02b470ab4304a6f04a6b04a6704a630aa4f02a4b02a4706a430ba3f06a3b0ba3706a33049660e9360486e048660a84e028460883e018360382e0582604d7e02c7d07c7a02c7907c7802c7602c7502c7404c6a02c6602b7e02b7d02b7c02b6e02b4e07b4d0ea7d07a7907a7509a7102a4909a4101a3d08a3901a3508a310797d06979079750697102949069410593d0393905935039310787e1987c02c6f02c6b04c6a02c6702c6602b6f02b6e02b4f02b4e07b4d04a6f04a6b04a6704a6302a4f02a4b02a4902a4702a4309a410da3f01a3d09a3b08a390da3701a3509a3308a310496f0496b04967049630294f0294b029490294702943069410b93f0593d0693b039390b9370593506933039310992f0692b0b9270692304b6e02a6f07a6b07a6902a6707a6319a6102a5f14a5b02a5714a5302a4f04a4b02a4704a430796f0796b07967079630e95f0995b0e957099530494f0494b04947049430e92f0292b02927099230786f0686b07867068630785f0685b07857068530484f0484b04847048430782f0282b02827068230781f0681b0781706813 20 1048575 8 255 11 2047 20 1048575
def cc_63_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x8dd6d89449841537e0617914f730616c7696666166204651116044d58b794f3984787b442363f44e38f65328672f2362a84a2614721a471cd4d18e3f1305e12b050f13a0886903e4a039050320700032 0x3d6f03d6e03d6d06c6f06c6d06c6b06c6706c6506c6304c5f06c5d06c5b06c5706c5504c5302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5902b5702b5302b5102b4f02b4b02b4702b4323a6f01a6d07a6b08a6907a6701a6509a6308a6104a5f10a5d07a5b07a57c025504a5306a4f06a4b06a4706a4302a3f02a3b02a3702a330396f0396d0296b02969029670296502963029610395f0395b039590295703953039510394f0394b03947039430293f0293b02937029330392f0392b03927039232286fbf06d0486b078678e065048630485f1085d0485b048578d055048530684f0484b06847048430283f0283b02837028330982f0482b40027048230381f0381b038170381304d6f04d6702c6f02c6b02c6702c6302c5b02c5704b6f04b6b04b6704b6306b5b06b5702b4f02b4b02b4702b4303a6f03a6b03a6703a6303a5b03a5702a4f02a4b02a4702a4303a3f03a3b03a3703a330496704966079650695b0695a06957069560294f0294e0294702943029420793f0893e0793b0193a079370193607933079320392f0392e0392703923039220486f0486d04867048650485a068560284f028470483f048370382f028270381f0381d038170381504d6f06d6702c6f02c6b02c6702c6302c5b02c5704b6f11b6b0eb6704b6306b5b06b5702b4f02b4b02b4702b4303a6f03a6b03a6703a6303a5b03a5702a4f02a4b02a4702a4303a3f03a3b03a3703a330496f0496e1796bbd16a179678e16604963049620695b0695a06957069560294f0294e0294702943029421193f0893e0e93b0193a0e9370193611933089320292f0292e0292702923029220486f0a86a048678c0660685a068560284f0284e02847028420a83f0a83a0a8373e0360382f0382e02827038220381f0381e0381d06d6f06d6b06d6706d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5310b6f11b6bc136710b6306b5f06b5b06b5706b5302b4f02b4b02b4702b4303a6f03a6b03a6703a6303a5f03a5b03a5703a5302a4f03a4d02a4b02a4a02a4702a4602a4503a3f03a3b03a3703a330396f0496e0396b0396a03967be16603963039620395f0395b0395a0395706956039530294f0294e0394d0393f0893e0393b0193a039370193603933039320292f0292e0292d1086f0a86b8b0670a8630685f0685b06857068530284f0284b02847028431183f0a83b3d0370a8330382f0382b03827038230381f0381d0381b03817bc0150381309d6f04d6e09d6b09d6a09d6709d6609d6304d6206c6f06c6705c5f05c5e05c5d02b6f09b6b02b6709b6302b5f02b5d0cb5b11b5902b5702b5511b5311b5106b4b02b4701a6f08a6b01a6708a6303a5b03a5901a5706a5303a5106a4b08a4901a4706a4101a3f02a3b01a3708a330596f0396b05967039630595f0195d0395b01957019550594d0394b05947059450593f0293b02937039330592f0192b01927039230986f098670b85f0b85d0b8570b8550684d0b8450b83f028370882f018270381f0581709d6f06d6b09d6706d6302c6f09c6b02c6709c6302c5f11c5b02c5706c5301b6f08b6b01b6708b6301b5f08b5b01b5706b5301b4f02b4b01b4708b4305a6f04a6e05a6b05a6a05a6709a6605a6304a6205a5f05a5b05a5a05a57ba25605a5305a4f11a4e02a4b02a4a02a4702a4605a4305a4203a3f03a3e03a3d0596f0396b05967039630595f0395b05957039530594f0294b02947039430193b0193a03939019370193603933039310192701926019250986f0986b09867098630685f0b85b0b857068530b84f0284b028470b8430883f0183b01837088330582f0582d0582b058270b825058230381f0581b058170381301d6f01d6e01d6d06c6f06c6d06c6b06c6706c6506c6304c5f06c5b06c5704c5302b6f02b6d07b6b12b6902b6702b6512b6312b6102b5f07b5b02b5704b5302b4f06b4b02b4706b4301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5d01a5b01a5701a5501a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330396f0396d0396b03969039670396503963039610395f0395b039590395703953039510394f0394b03947039430393f0293b02937039330192f0192b01927019230e86f0e86d0486b078670e865048630485f0985d0485b048570e855048530684f0484b06847048430e83f0283b02837048330182f0182b01827018230381f0381b038170381306d6f06d6b06d6706d6302c6f12c6b02c6709c6302c5f06c5b02c5706c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4303a6f03a6b03a6703a6303a5f03a5b03a5703a5303a4f02a4b02a4703a4301a3f01a3e03a3d01a3701a3501a3301a320196f0496e0196b0196a01967b816601963019620195f0195b0195a0195706956019530194f1294e0194b0194a019470294601943019420193701936019350192f0392e0192d0986f0b86b0e867098630685f0685b06857068530e84f0284b028470b8430183f0183b01837018330382f0382b03827038230181f0181d0181b018170e8150181301a7c01a7801a7402a7007d8802d8402c8c01b8c07b8801b8415b8002b5814b5001b4cb634801b4414b4008a4801a44039480594404d6f01d6702c6f07c6b02c6704c6306c5b02c5701b6f01b6b01b6701b6301b5b01b5701b4f01b4b01b4701b4301a6f01a6e01a6701a6301a6204a5b04a5a01a5701a5615a4f0da4e02a4b02a4a02a4702a4615a430da4201a3f01a3e01a3b01a3a01a3701a3601a3301a320496f0396b05967039630395b059570594f0294b02947039430193f0193b01937019330592f0592d0392b03929059270592503923039210486f048670b84f028470183f018370b82f0b82d0b8270b8250381f0581704d7f04d7e04d7d04d6f04d6e04d6202c7f02c7d07c7b0dc7902c7702c75b54730dc7102c6f07c6b02c6704c6306c5b02c5701b7f01b7e01b7d01b7c01b7b07b7a01b79ab37801b7701b7601b7501b7401b7315b7201b71b437001b6f01b6e01b6b07b6a01b6701b6601b6304b6201b5b06b5a01b5701b5601b4f01b4e01b4b02b4a01b4701b4601b43a734201a7f01a7d01a7b01a7901a7701a7501a7301a7101a6f01a6b01a6701a6301a5b01a5701a4f01a4b01a4701a4301a3f01a3e01a3d0597f0597d0397b03979059770597503973039710496f0396b05967039630395b059570594f0294b02947039430193f0193e0593d0192f0192e0192b019290192301922039210b87f0b87d078770b8750486f048670b84f028470183f0b83d01837018350182f018270381f0581704e7f06e7b07e7704e7302d7f02d7e02d7d02d7702d7502d7304d7202d6f02d6b0dd6a02d6702d6602d6302c7702c7602c7506c6f07c6b0dc6a07c6710c6606c6302c5f02c5e04c5d01b7f01b7e01b7b07b7a01b7701b7601b7304b7201b6f01b6bac36a01b6701b6601b6301b5f01b5e01b5b02b5a01b5701b5601b5302b5201b4f01b4e01b4d01b4c01b4b0db4a01b4910b4801b4701b4601b4501b4401b4307b4201b41a634001a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3e01a3d0497f0397b05977039730596f0396b05967039630295f0295b02957029530594f0594d0394b03949059470594503943039410193f0193e0593d0192f0192e0192b019290192301922039210487f0487b04877048730686f0486b0b867048630285f0285b02857028530784f0b84d0484b0b8470b845048430183f0b83d0183b0183701835018330182f0182b01827018230381f0481b058170381306e7f06e7702d7f02d7b0dd7a02d7702d7602d7302d6d02d6702d6509c7f04c7e0dc7b0dc7a0dc770fc7609c7304c7202c6702c6602c6501b7f01b7e01b7bb037a01b7701b7601b7304b7201b6b06b6a01b6701b6601b5f01b5e01b5b02b5a01b5701b5601b5302b5201b4f01b4e01b4d01b4c01b4b0db4a01b490fb4801b4701b4601b4501b4401b430cb4201b41a234001a7f01a7b01a7701a7301a6b01a6701a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3e01a3d0597f0397b05977039730396b059670295f0295b02957029530594f0594d0394b03949059470594503943039410193f0193e0593d0192f0192e0192b019290192301922039210987f0b8770285f028570b84f0b84d0b8470b8450183f0b83d01837018350182f018270381f0581707d7a02d7602d6d02d6504c7e07c7a07c7604c7202c6602c6501b7d01b7501b4d01b4901b4501b4101a7601a7506a6a06a6602a5e02a5a02a5602a520ca4e07a4d0ca4c07a4a07a4907a480da4607a450fa4407a4207a4107a4001a3e01a3a01a3601a320597d059750594d0394905945039410592d0392905925039210b84d0b8450782d0b82501d6f01d6b01d6a01d6701d6601c6f06c6a06c6707c6606c5f07c5e06c5d02b6f07b6b02b6704b6302b5f02b5d07b5b0cb5902b5702b5507b5307b5106b4b02b4701a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4b01a4701a3f01a3b01a3701a330496f0396b05967039630595f0595d0395b03959059570595503953039510394b059470593f0293b02937039330192f0192b01927019230486f048670785f0785d078570b8550b83f028370182f018270381f0581704d6f06d6b07d6704d6302c6f02c6b07c6a02c6702c6601c6302c5f02c5b02c5702c5302b6f02b6e01b6b01b6a01b6701b6601b6301b6206b5f0db5b0cb5a0db570cb5606b5302b4f02b4e07b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310496f0396b05967039630595f0395b05957039530294f0294b02947029430593f0593d0393b03939059370593503933039310192f0192b01927019230486f0486b04867048630685f0485b0b857048530284f0284b02847028430b83f0b83d0483b0b8370b835048330182f0182b01827018230381f0481b058170381304d6f06d6b07d6704d6302c6f07c6b02c6704c6302c5fb045b02c5706c5301b6f01b6d01b6b01b6701b6501b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6701a6601a6506a5f07a5bab25a07a57af25606a531fa4fae24e02a4b02a4a02a4702a4607a43a624201a3f01a3e01a3b01a3a01a3701a3601a3301a320496f0596d0396b0596705965039630595f0395b05957039530594f0294b02947039430193f0193b01937019330592f0592d0392b03929059270592503923039210486f0486b04867048630685f0485b0b857048530b84f0284b02847048430183f0183b01837018330782f0b82d0482b0b8270b825048230381f0481b058170381302d7e02d7d02d7504d7206d6a02d6602c7602c7506c6a06c6602c5e04c5d01b6d01b6501b4d01b4901b4501b4104a7e07a7a07a7604a7201a6601a6502a5e02a5a02a5602a5207a4e07a4d07a4c07a4a0ca490ca4807a4610a4510a4407a4207a4107a4001a3a01a360596d059650594d0394905945039410592d059250784d0b8450b82d0b82504d6f01d6702c6f07c6b02c6704c6306c5b02c5701b6f01b6b01b6701b6301b5b01b5701b4f01b4b01b4701b4307a6707a6607a6506a5706a5607a5507a4f0da4e02a4b02a4a02a4702a4607a4307a4201a3f01a3e01a3b01a3a01a3701a3601a3301a320496f0396b05967039630395b059570594f0294b02947039430193f0193b01937019330592f0592d0392b03929059270592503923039210486f048670b84f028470183f018370782f0782d078270b8250381f0581707d6f07d6e07d6d01c6f01c6d01c6701c6504c5f06c5d06c5706c5502b6f02b6d07b6b07b6902b6702b6507b630db6102b5f07b5b02b5704b5306b4b02b4701a6f01a6d01a6701a6501a6301a5f01a5b01a5701a5301a4b01a4701a3f01a3b01a3701a330596f0596d0596705965039630495f0395b05957039530394b059470593f0293b02937039330192f0192b01927019230786f0b86d07867078650485f048570b83f028370182f018270381f0581706d6f06d6702c6f02c6b02c6702c6302c5b06c5a02c5702c5609b6f04b6e0db6b07b6a0db6707b6609b6304b6201b5b01b5a01b5701b5602b4f02b4e0cb4d01a6f01a6b01a6701a6301a5b01a5701a4f01a4b01a4701a4301a3f01a3d01a3b01a3701a350596f0396b05967039630395b059570294f0294b02947029430593f0593d0393b05937059350192f0192b01927019230986f0b8670284f028470b83f0b83d0b8370b8350182f018270381f0581706d6f06d6702c6fac46b02c6709c6306c5b02c5701b6f01b6b01b6701b6301b5d01b5b01b5701b5501b4f01b4b01b4701b4309a6f04a6e0ca6bab26a16a67aa26609a6304a6201a5701a5601a551da4fa924e02a4b02a4a02a4702a460ca43a224201a3b01a3a01a3701a3601a330596f0396b05967039630595d0395b05957059550594f0294b02947039430193f0193b01937019330592f0592d0592705925039230986f0b8670b84f028470183f018370b82f0b82d0b8270b8250381f0581704d7e04d7d04d6e04d6202c7e02c7d02c7c02c7902c7514c7202c710dc7001b7d01b7901b7501b7101b4d01b4514a7e14a7d15a7c07a7a0da7907a7807a7614a7507a7414a720da710da7004a6e09a6d04a6c07a6a07a6614a6507a6404a6206a5d06a5a06a5614a550ca5401a4e01a4d01a3e01a3a01a3601a320597d0397905975039710594d029450592d0292902925029210b87d0b8750b82d0b82504d6f06d6b07d6704d6302c6f01c6b02c6702c6302c5f02c5b02c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4307a6707a6607a6506a5f07a5b07a5a07a5707a5606a5302a4f02a4e07a4d01a3f01a3e01a3b01a3a01a3701a3601a3301a320496f0396b05967039630595f0395b05957039530294f0294b02947029430193f0193b01937019330592f0592d0392b03929059270592503923039210486f0486b04867048630685f0485b07857048530284f0284b02847028430183f0183b01837018330782f0782d0482b078270b825048230381f0481b058170381304a6c06a6406a6006a5c0ca540de7e09e7da557d14d7509d6d14d6502c7d01c7901c7501c7102c6902c6101b7d01b7901b7501b7101b4d01b4504a7e04a7d04a7c04a6e07a6a0da6907a6804a6209a6109a6006a5e0da5aa025606a5201a4e01a4d01a3e01a3a01a3601a320597d0297902975029710594d029450592d0292902925029210b87d0b8750986d0b86502849048410b82d048290b8250482107d6f07d6e07d6d07c6f07c6d06c6b07c6707c6506c6304c5f07c5d06c5b07c5707c5504c5302b6f02b6d01b6b01b6901b6701b6501b6301b6102b5f02b5b02b5901b5702b5302b5102b4f02b4b02b4702b4301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330596f0596d0296b02969029670296502963029610495f0395b05957039530594f0394b05947039430293f0293b02937029330192f0192b01927019230786f0b86d0486b0786707865048630485f0985d0485b0485707855048530684f0484b07847048430283f0283b02837028330182f0182b01827018230381f0481b058170381306d6f06d6702c6f02c6b02c6702c6301c5b02c5701b6f01b6b01b6701b6301b5b01b5701b4f01b4b01b4701b4309a6f04a6e0ca6b07a6a0ca6707a6609a6304a6206a5706a560ca5502a4f02a4e0ca4d01a3f01a3e01a3b01a3a01a3701a3601a3301a320596f0396b05967039630395b059570294f0294b02947029430193f0193b01937019330592f0592d0392b03929059270592503923039210986f0b8670284f028470183f018370b82f0b82d0b8270b8250381f0581709a7c07a7404a5806a5406a5004d7c06d7406d7007d6804d600cc7c14c6404e7ea167a14e7604e7206d7a14d760dd6e06d6d01c6901c6501c6102c5902c5101b6d01b6901b6501b6101b4d01b4509a7e0da7aa027609a7206a5a0da590ca5806a5106a5001a4e01a4d01a3e01a3a01a3601a320596d0296902965029610594d029450592d0292902925029210b86d0b8650685d0b8550b82d0b825 20 1048575 8 255 11 2047 20 1048575
def cc_63_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xaf84aa7b7da24579a2829237f8a67d8297d7d257750826d57b680555fe825b44a5872d5483f51b2d4dc3f49b4146b3042e3d4032b3d72c3a136381203047d26c98236361b581154610b4a004e660004e 0x6d6f06d6702c6f12c6b02c6712c6306c5b02c57e936fe736be6367e436306b5b06b5712b4f02b4b02b4712b4303a6f03a6b03a6a03a67e326603a6303a5d03a5703a5503a4f02a4b02a4703a4303a3f03a3b03a3703a330396f0496e0396b0396a03967e116603963039620395705956039550394f1294e0294b0294a029470294603943039420393f0893e0393b0193a039370193603933039329506f8f0671284f028476603f420370382f038270381f0381d03817df01504e7f04e7e05e7b06e7a05e7705e7604e7304e7204d7f06d7703d6f03d6e03d6d02c7f02c7e02c7d02c7702c7502c7304c7202c6f02c6d02c6b02c6902c6702c6502c6302c6102c5b06c5a02c5702c5602b7702b7602b7505b6f05b6e06b6d06b6c05b6b05b6a05b6905b6805b6705b6605b6505b6405b6305b6206b6106b6006b5b06b5a06b5706b5602b4f02b4e04b4d04a7f07a7b07a7704a7305a6f01a6d05a6b05a6905a6701a6505a6306a6106a5b06a5702a4f02a4b02a4702a4307a3f01a3d07a3b08a3907a3701a3507a3307a310497f0397b0697a0597705976039730395b03959039510294f0294b02947029430593f0593d0393b03939059370593503933039310592f0392b05927039230487f048770586f0686d05867058650284f028470783f0783d078370b8350982f0b8270381f0581702d6f02d6702d6304c6f04c6e04c6b04c6704c6304c6204c5f04c5e03c5b03c5904c5704c5304c5203c5103c5002b6f02b6b04b6a02b6702b6602b6302b5b02b5702b5302b4f02b4b02b4902b4702b4302b4104a6f04a6b04a6704a6309a5f09a5b09a5709a5305a4f01a4d05a4b05a4701a4505a4302a3f02a3b02a3702a330496f0396b0496a0496704966039630595f0595e0395b03959049570395306952039510293f0293b02937029330592f0392b05927039230486f048670485f048570484f0484d04847048450283f028370482f048270381f0481704e7f04e7e04e7b04e7a04e7704e7604e7304e7204d7f04d7703d6f03d6e03d6d02c7f02c7d02c7b04c7a02c7702c7602c7502c6f02c6d02c6b02c6902c6702c6502c6302c6102c5b02c5702b7f02b7e02b7d04b6f05b6e04b6d06b6c04b6b04b6a04b6904b6804b6705b6604b6505b6404b6304b6204b6104b6004b5d04b5b04b5a04b5706b5604b55dc35402b4f02b4e04b4d04a7f04a7b04a7704a7305a6f01a6d05a6b05a6905a6701a6505a6306a6106a5b06a5702a4f02a4b02a4702a4304a3f01a3d04a3b08a3904a3701a3504a3304a310497f0397b0497a0497704976039730395b03959039510294f0294b02947029430493f0493d0393b0493a03939039380493704936059350593403933039310592f0392b05927039230487f048770486f0486d04867048650284f028470483f0483d04837048350482f048270381f0481701e7f04e7e01e7d04d7f04d7e04d7b04d7a04d7704d7604d7304d7201d6f01d6e01d6d01d6c01d6b01d6a05d6906d6801d6701d6605d6505d6401d6301d6201d6101d6004c7f04c7701c6f01c6d01c6706c6503c5f03c5e03c5d02b7f04b7b02b7704b7301b6f01b6d01b6b0db6901b6702b6501b6301b6102b5f02b5d05b5b05b5902b5702b5505b5306b5106b4b02b4701a7b04a7a01a7901a7701a7601a7301a7101a6701a6601a6501a5f01a5d01a5b01a5901a5701a5501a5301a5101a4b01a4701a3f01a3b01a3701a330497f0397b0497a0497704976039730196f0196d0196b0196a03969039680196701966059650596401963019610394b03949039410593f0293b02937039330192f0192b01927019230487f048770186f0186d01867048650485f0485d04857048550483f028370182f018270381f0481704e7f04e7e05e7b06e7a05e7705e7604e7304e7204d7f06d7703d6f03d6e03d6d02c7f07c7b02c7704c7302c6f02c6d05c6b05c6902c6702c6505c6306c6106c5b02c5701b7f04b7e01b7d01b7701b7504b7304b7201b6f01b6d05b6b05b6901b6701b6505b6306b6106b5b06b5a01b5706b5601b4f02b4b01b4708b4301a7701a7601a7505a6f05a6e06a6d06a6c05a6b05a6a05a6905a6805a6705a6605a6505a6405a6305a6206a6106a6006a5b06a5a06a5706a5607a4f0da4e02a4b02a4a02a4702a4607a4307a4204a3f04a3e04a3d0497f0397b0697a0597705976039730395b03959039510594f0294b02947039430593f0193b01937039330592f0592d0392b03929059270592503923039210487f048770586f0686d05867058650b84f028470883f018370782f0782d078270b8250381f0581701e7f01e7e07e7d01d7f01d7e05d7d05d7c01d7b01d7a01d7901d7801d7701d7601d7501d7401d7301d7205d7106d7004d6f04d6e05d6b06d6a05d6705d6604d6304d6201c7f06c7d01c7701c7504c6f06c6703c5f03c5e03c5d01b7f02b7d01b7b01b7901b7701b7501b7309b7102b6f07b6b02b6704b6302b5f02b5d05b5b05b5902b5702b5505b5306b5106b4b02b4701a7f01a7e01a7d01a6f01a6e01a6b01a6901a6304a6201a6101a5f01a5d01a5b01a5901a5701a5501a5301a5101a4b06a4a01a4701a4601a3f01a3b01a3701a330197f0597d0197b01979019770197501973039710496f0396b0696a0596705966039630394b03949039410593f0293b02937039330192f0192b01927019230187f0987d01877018750486f048670585f0685d05857058550b83f028370182f018270381f0581701d6f04d6704d6304c6f04c6e04c6b04c6704c6304c6204c5f04c5e03c5b03c5904c5704c5304c5203c5103c5002b6f04b6b02b6704b6302b5f0cb5b02b570cb5302b4f02b4d05b4b02b4702b4505b4301a6f04a6b04a6a01a6704a6604a6307a5b01a5706a5301a4f05a4b05a4901a4705a4306a4101a3f02a3b01a3708a330496f0396b0496a0496704966039630595f0595e0395b03959049570395306952039510593f0293b02937039330592f0192b01927039230486f048670485f048570484f0484d04847048450483f028370482f018270381f0481704e7f04e7e04e7b04e7a04e7704e7604e7304e7204d7f04d7703d6f03d6e03d6d02c7f04c7b02c7704c7302c6f02c6d05c6b05c6902c6702c6505c6306c6106c5b02c5701b7f01b7d04b7b04b7a01b7704b7601b7501b6f01b6d05b6b05b6901b6701b6505b6306b6106b5b01b5701b4f02b4b01b4708b4301a7f01a7e01a7d04a6f05a6e04a6d06a6c04a6b04a6a04a6904a6804a6705a6604a6505a6404a6304a6204a6104a6004a5d04a5b04a5a04a5706a5604a55d725404a4f0da4e02a4b02a4a02a4702a4604a4304a4204a3f07a3e04a3d0497f0397b0497a0497704976039730395b03959039510594f0294b02947039430593f0193b01937039330492f0492d0392b0492a03929039280492704926059250592403923039210487f048770486f0486d04867048650484f028470483f018370482f0482d04827048250381f0481705e7f04e7e05e7b06e7a05e7705e7605e7304e7206d7f06d7703d6f03d6e03d6d02c7f02c7b02c7702c7302c6f02c6d02c6b02c6902c6702c6502c6302c6102c5b02c5701b7f04b7e01b7b01b7a01b7707b7601b7301b7201b6f05b6e01b6d06b6c01b6b01b6a01b6901b6801b6705b6601b6505b6401b6301b6201b6101b6001b5b01b5a01b5706b5601b4f02b4e01b4d01a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5b01a5701a4b02a4a01a4901a4701a4601a4301a4101a3701a3601a350597f0397b0697a0597705976039730395b03959039510294f0294b02947029430193f0193d0193b03939019370593501933019310192f0192b01927019230987f0b8770586f0686d05867058650284f028470183f0183d018370b8350182f018270381f0581709d6f09d6b09d6709d6305c6f05c6b06c6a05c6705c6605c6305c5f05c5e03c5b03c5905c5705c5306c5203c5103c5002b6f02b6b02b6702b6301b5b02b5702b5302b4f02b4b02b4902b4702b4302b4101a6f08a6b01a6708a6302a5b01a5702a5301a4f05a4b05a4901a4705a4306a4101a3f02a3b01a3702a330596f0396b0696a0596705966039630595f0595e0395b03959059570395306952039510293f0293b02937029330592f0192b01927039230986f098670b85f0b8570584f0684d05847058450283f028370882f018270381f0581705e7f04e7e05e7b06e7a05e7705e7605e7304e7206d7f06d7703d6f03d6e03d6d02c7f02c7b02c7702c7302c6f02c6d02c6b02c6902c6702c6502c6302c6102c5b02c5701b7f08b7b01b7708b7301b6f01b6d05b6b05b6901b6701b6505b6306b6106b5b01b5701b4f01b4d02b4b02b4a01b4702b4601b4508a7f04a7e08a7b07a7a08a7707a7608a7304a7205a6f05a6e06a6d06a6c05a6b05a6a05a6905a6805a6705a6605a6505a6405a6305a6206a6106a6006a5d06a5b06a5a06a5706a5608a55d425401a4f01a4e01a4d02a3f02a3e02a3d0597f0397b0697a0597705976039730395b03959039510294f0294b02947029430593f0193b01937039330592f0592d0392b0692a03929039280592705926059250592403923039210987f098770586f0686d05867058650284f028470883f018370882f0882d088270b8250381f0581705d6f04d6e05d6b06d6a05d6705d6605d6304d6206c6f06c6703c5f03c5e03c5d02b6fdd36b02b67db36302b5f02b5d05b5b05b5902b5702b5505b5306b5106b4b02b47da26fd926bd8267d626305a5f01a5d05a5b05a5905a5701a5505a5306a5106a4b06a47d523f02a3b02a37d32330596f0396b0696a0596705966039630394b03949039410593f0293b02937039330592f0392b05927039230b86f0b8670585f0685d05857058550b83f028370b82f0b8270381f0581704d6f04d6e02b6f04b6b02b6704b6302b5f02b5d0fb5b0db5902b5702b550fb530db5101a6b04a6a01a6701a6601a6301a5701a5501a3f01a3b01a3701a330396f0396b03967039630195f0195d0395b03959019570195501953019510393f0293b02937039330192f0192b019270192301e7f04e7e01e7d02c7f04c7b02c7704c7301c6f01c6d01c6b0fc6901c6702c6501c6301c6101b7b04b7a01b7901b7701b7601b7301b7101b6701b6601b6501b4f01b4b01b4701b4303a7f03a7b03a7703a7301a6f01a6d01a6b03a6901a6703a6501a6301a6103a5503a4f02a4b02a4703a4301a3f01a3b01a3701a330497e0497c04976ca1740196e0196c01966d11640f94e029460193e019360392e02c6f07c6b02c6704c6301b6f01b6d01b6701b6504b6301b4f02b4b01b4708b4301a6701a6607a4f0da4e02a4b02a4a02a4702a4607a4307a4204a3f04a3e0396f0396b03967039630394f0294b02947039430393f0193b01937039330392f0392d0392b039290392703925039230392102d7f07d7b02d7704d7301c7f04c7e01c7d01c7701c7504c7304c7201c5f02c5b01c5708c5301b7701b7601b7507b5f0fb5e02b5b02b5a02b5702b5607b5307b5204b4f04b4e04b4d03a7f03a7b03a7703a7303a6503a5f02a5b02a5703a5303a4f01a4b01a4703a4303a3f03a3d03a3b03a3903a3703a3503a3303a310497e079760f95e029560894e0894c01946019440793e0893c07936cf1340392e01e7f01e7e07e7d01c7f02c7d01c7b01c7901c7701c7501c7309c7102c6f07c6b02c6704c6301b7f01b7e01b7d01b6f01b6e01b6b01b6901b6304b6201b6101b4f01b4b01b4701b4301a7f03a7d01a7b01a7901a7701a7501a7303a7103a6f03a6b03a6703a6303a5503a4f02a4b02a4703a4301a3f01a3b01a3701a330197e0997c01976019740496e0496c07966c91640f94e029460193e0893c01936019340392e02c6f04c6b02c6704c6301b6f01b6d04b6b04b6a01b6704b6601b6501b4f02b4b01b4708b4301a6f01a6e0fa4f0da4e02a4b02a4a02a4702a460fa430da4207a3f07a3e0396f0396b0396703963039550394f0294b02947039430393f0193b01937039330392f0392d0392b039290392703925039230392102d7f04d7b02d7704d7301c7f01c7d04c7b04c7a01c7704c7601c7501c5f02c5b01c5708c5301b7f01b7e01b7d04b5f0fb5e02b5b02b5a02b5702b5604b5304b5204b4f07b4e04b4d03a7f03a7b03a7703a7303a6503a5f02a5b02a5703a5303a4f01a4b01a4703a4303a3f03a3d03a3b03a3903a3703a3503a3303a310497e049760f95e029560894e019460493e0493c04936cc1340392e01d6f15d6e01d6d02b6f07b6b02b670fb6301b5f01b5d01b5b01b5702b5501b5301a6b01a6901a6701a6301a6101a5701a5601a5501a3f01a3b01a3701a330396f0396b03967039630195f0195b039590195701953019510393f0293b02937039330192f0192b019270192301d6f01d6e01b6f02b6d01b6b01b6701b6501b6302b5f07b5b02b5707b5301a6f01a6e01a6d01a5f01a5e01a5b01a5901a5307a5201a5101a3f01a3b01a3701a330196f0196b019690196701963039610395f0395b03957039530393f0293b02937039330192f0192b019270192302b6f02b6d07b6b0fb6902b6702b650fb630fb6102b5f02b5d07b5b02b5702b5504b5315a6f01a6d07a6b08a6907a6701a6509a6308a6104a5fca25d07a5b07a57c925504a530fa3f02a3b02a3709a330396f0396d0396b03969039670396503963039610395f0395b039590395703953039510393f0293b02937039330392f0392b039270392302c6f0fc6b02c670fc63d036fce36bcd367cb3630fb4f02b4b02b470fb4303a6f03a6b03a6703a6303a5503a4f02a4b02a4703a4303a3f03a3b03a3703a330496ec81660f94e029460893e019360392e04d7f04d7e04d7d04d6f04d6e04d6202c7f02c7d02c7b02c7902c7702c7502c7302c7102c6f02c6b02c6702c6302c5b02c5705b7f12b7e05b7d12b7c05b7b05b7a05b7905b7805b7707b7605b7512b7405b7305b7205b7105b7004b6f04b6e05b6b05b6a05b6707b6604b6304b6205b5b05b5a05b5706b5602b4f02b4e03b4d19a7f01a7d07a7b08a7907a7701a7509a7308a7104a6f07a6b07a6704a6306a5b06a5702a4f02a4b02a4702a4305a3f01a3d05a3b08a3905a3701a3505a3305a310597f0597e0597d0597c0397b039790597705975039730697203971039700496f0396b05967039630395b059570294b0294a02949029470294602943039410293702936029350592f0392b05927039230b87f0b87d078770b8750486f048670284f028470583f0583d058370b8350982f0b8270381f0581701e7f01e7e08e7d01d7f09d7d01d7b01d7701d7501d7304d6f06d6b07d6704d6301c7f02c7d01c7b01c7901c7701c7501c7302c7102c6f02c6b02c6702c6302c5f02c5b02c5702c5301b7f01b7e05b7d09b7c01b7b01b7a01b7901b7801b7701b7601b7501b7401b7301b7205b7105b7004b6f04b6e05b6b05b6a05b6707b6604b6304b6205b5f05b5b05b5a05b5712b5605b5302b4f02b4e03b4d01a7f01a7e01a7d01a6f01a6e01a6b01a6901a6304a6201a6101a5f01a5b09a5a01a5701a5601a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310197f0597d0197b01979019770197501973039710496f0396b05967039630595f0395b05957039530294b0294a02949029470294602943039410293702936029350192f0192b01927019230187f0987d0187b0187701875018730486f0486b04867048630685f0485b0b857048530284f0284b02847028430583f0583d0483b058370b835048330182f0182b01827018230381f0481b058170381306e7d06e7501d7601d7506d6a06d6602c7902c7102c5d02c5902c5502c5104b7e05b7a07b7604b7205b6a06b6607b5e05b5d07b5c05b5a05b5905b5807b5605b5512b5405b5205b5105b5002b4e03b4d01a7d01a7501a5901a5101a3d01a3901a3501a310595d0395905955039510294a02949029460394102936029350785d0b8550583d0b83501e7f01e7e01e7bc467a01e7701e7601e7304e7206d7f06d7701d6f01d6e06d6d02c7f02c7b02c7702c7301c6f02c6d01c6b01c6901c6701c6501c6302c6102c5b02c5705b7f04b7e05b7b05b7a05b7712b7605b7304b7201b6f01b6e05b6d12b6c01b6b01b6a01b6901b6801b6701b6601b6501b6401b6301b6205b6105b6005b5b05b5a05b5706b5602b4f02b4e03b4d01a7f01a7b11a7a01a7701a7601a7301a5b01a5901a5101a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310597f0397b05977039730196f0196e0596d0596c0196b019690196701965019630196203961039600395b059570294b0294a02949029470294602943039410293702936029350192f0192b01927019230987f0b8770186f0b86d01867018650284f028470583f0583d058370b8350182f0b82d01827018250381f0581710d6f06d6bc656706d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5305b6f04b6e05b6b05b6a05b6712b6605b6304b6205b5f05b5b05b5a05b5712b5605b5302b4f02b4e03b4d10a6f11a6bc526710a6306a5f11a5bc325706a5302a4f02a4b02a4702a4305a3f01a3d05a3b08a3905a3701a3505a3305a310596f0396b05967039630595f0395b05957039530294b0294a02949029470294602943039410293702936029350592f0392b05927039230b86f0a86b0b8670a8630685f0a85b0b857068530284f0284b02847028430583f0583d0583b058370b835058330b82f0a82b0b8270a8230381f0581b058170381301e7f01e7e07e7d01d7f06d7d01d7b01d7701d7501d7304d6f06d6b06d6704d6301c7f02c7d01c7b01c7901c7701c7501c7302c7102c6f02c6b02c6702c6302c5f02c5b02c5702c5301b7f01b7e01b7d01b6f01b6e01b6b01b6901b6304b6201b6101b5f01b5b06b5a01b5701b5601b5301b4f01b4b01b4701b4301a7f03a7d01a7b01a7901a7701a7501a7303a7103a6f03a6b03a6703a6303a5f03a5b03a5703a5302a4f03a4d02a4b02a4a02a4702a4602a4501a3f01a3b01a3701a330197f0197e0397d0997c0197b0197a019790197801977019760197501974019730197203971039700396f0496e0396d0496c0396b0396a039670796603965c016403963039620395f0395b0395a0395706956039530294f0294e0394d0193f0193e0393d0893c0193b0193a0193701936019350193401933019320292f0292e0292d0187f0987d0187b0187701875018730486f0486b04867048630685f0485b06857048530284f0284b02847028430183f0183b01837018330382f0382b03827038230381f0381d0381b038170e8150381301d6f01d6e01d6b01d6901d6701d6301d6203d6103d6001c6f06c6d01c6b01c6701c6501c6306c5f06c5b06c5706c5301b6f01b6b01b6901b6701b6302b6102b5f02b5b02b5702b5302b4f02b4b02b4702b4301a6f01a6e01a6d01a5f01a5e01a5b01a5901a5701a5307a5201a5101a4f01a4b06a4a01a4701a4601a4301a3f01a3b01a3701a330196f0196b019690196701963039610395f0295b02957029530394f0394b03947039430293f0293b02937019330192f0192b01927019230186f0986d0186b0186701865018630785f0485b07857048530684f0484b06847048430283f0283b02837028330182f0182b01827018230381f0381b038170381303d6f03d6d03d6703d6503d6306c6f06c6d06c6706c6504c5f04c5702b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5302b4b02b470ea6f01a6d09a6b08a690ea6701a6509a6308a6104a5f04a5b04a5704a5306a4b06a4702a3f02a3b02a3702a330396f0396d0396b03969039670396503963039610395f0395b02957039530394b039470293f0293b02937029330392f0392b03927039230486707866048650385f0485a04857048560283f028370482f048270381f03817 20 1048575 8 255 11 2047 20 1048575
def cc_63_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x9434c8c182870517ef817b93671b9e6b66569e186603e5fb655c93259c2d55f3d5342b4f53f4b63f48c2a45f2d4203f400203b34d3347f2e3512667d1e97d19a4f11b7f0dc3f0af2d0634c0372c00037 0x135bc0dace02c6f0163581f1a8058ce02c660163180b16c058ae04b6f025b700edac076d406b6701db3012d8c096c406b57035ab032d540569e02b4e03da68129bc0f4d607a670253181a96c0d4ae02a4f0152580a91c054860ca3f00d1e8268ec114720ca3700d1a8268cc114620496f01cb580a59c072c60395b02cab80a53c0529602947014a18124fc0927a0393b01c9c8164dc0926a0393301c988164bc072560592701c918121bc090ce0284f0142382e0fc1707a0b83705c1a8260bc1704e0381f02c0b80f9fc07cfc03e7d02ebf8175f80dafaff57c02ebb8175d40bae404d6f036b380b1fc058fa02c7b0163c80b1dc058ea02c730163880b1bc058d607c6a0163380b198058c602c5d0162b80b1540b6fe05b7e06dbe83edf00b6f605b7a02dbc816de00b6ee05b7602dba816dd00b6e605b72065b8bf8dc0096de04b6e03db581eda80f6ce07b66025b1812d88056ae02b56015aa8169fc034fa05a7b02d3c8169dc034ea05a73045388129bc0f4d607a670253181a96c0d4ae02a4f0152580a91c054860da3f00d1e8268ec114720da3700d1a8268cc114620497f024bf0125f4092de0496e01cb580e5a4072c60496201cb080e56c0d2b40595702cab00a53c0529602947014a18164fc0b27a0393b01c9c8164dc0b26a0393301c988164bc072560592701c918161fc170fa0587702c3a8121bc090ce0284f0142382e0fc1707a0b83705c1a8260bc1704e0381f0340e81605c0b02a04d6f036b38071bc038dc03c6b01e3500719c038cc01c6300e3101b16c0d8b405c5702e2b00adbc0f6d602b67025b181ad6c056ae02b4f015a686ad2c1b69202b47015a286ad0c1b68201a6f00d3581e9a8034ce01a6600d3180696c034ae01a4b00d2480691c0348601a4100d1f8068ec0346e01a33024b780e5ac032ce0396301cad81a5680b2ae05956024a7812534032960194900ca3806514032860194102c9f80a4ec0526e0393300c978064ac0324e019230243781219c1709e0b84d05c2382e1141707e0283700c1780609c0703e0581701f3f80f9f807cfa01d7f00ebf0075f403af801d7b02ebd0075e40baf001d7700ebb0075d403ae801d7302eb90075c5f8ae001d6f00eb70075ac0fad401d6700eb300758c09ac405c7f0363e8171dc0b8ea04c6f0363380717c038bc06c5d015bf80adf40b6f605b79015bb80add40b6e618b71015b781edac056ce04b6300daf80ad74036b601b5900dab806d54036a60db51035a580ad1c034fe01a7d00d3d8069e4034ee01a7500d398069c4034de01a6b03d3500699c034cc01a6300d258069240348201a3f00d1d8068dc034660497f024bf0125f4092de0496e01cb580e5a4072c60496201cb080657c0b2ba0195b00cac80655c032aa0195301ca880e52c0d2940594702ca30164fc052760293701c998064bc032560192700c918161fc170fa0587702c3a8121bc090ce0185f05c2e80615c030aa0b83f0141b8060bc1305a0182700c1280e07c0d03a0581702c0a80f9e807cec06d7a04ebb0175980baca02c6d0163480b194058c202c5901628812df8036f407b7600db9032db8036da0cb6c00db5006da4036d007b6600db281ed90036c401b6100db0006d680d6ac02b4e00da68069b4034d201a6500d3080a9280349201a4600d208068d80346a0496d024b28165740b2aa0193d01c9c8164d4032620b86d05c328060f41706a03e7f01f3f00f9f40bafefa57d02ebd8175dc0baea05d73026b781b5ac13ace04d630163f80b1f4058f602c790163b80b1d4058e602c710163780b1ac058ce02c630162f80b16c058ae02c5300dbf816df8036fa11b7c00dbd806de8036f201b7800dbb816dd8036ea05b7400db9806dc8036e201b7000db7812db8036d601b6a00db381ed98036c601b6200daf806d6c036b401b5708dab006d4c0369e02b4e00da68069fc034fc01a7d00d3e0069ec034f201a7700d3a8069cc0b4e401a71045380069bc034d601a6700d3180697c034b601a5700d2980692c0549401a4900d238069180348601a4100d1b8068d80346a0497f024bf0125f4092de0496e01cb580e5a4072c60496201cb081657c072b61295a02cab816558072a60294f014a580a51c052860193f00c9e8064ec072720193702c9a8064cc032620192f00c9580649c032460587f05c3e8121ec0b0ee05875024398121bc090d6048670243181a17c090b60b8570242980a13c0509602847014218060fc0307a0183b00c1b82e0d4030660182f00c1580609c030460381f05c0e81206c0b02e0581501c0980f5bc07adc03d6d02e37c151b40b8d605c6702e3281718c098be06c5b81a2b81314c056de02b6d02db5816da4056ce02b6502db1c00d84056be10b5b015ab812d4c0569efd34b015a381ad0c0b4de01a6d02d358169a40b4ce01a6502d31822984094be09a5b04d2b81294c0d49e09a4b7d92381a90df247e02a3b0151b8268cc092de0496e024b681257c092bc0395b01cac80e54c092a40395102ca780e52dc62940594702ca300e50c0b27e0293b0149b80e4cc0b25e0392b02c9380e48c0b0de0b86d0243581619c0b0ca048630242f81216c090ae048530342781212c1708e0484305c1f80a0ec0506e0483304c178120ac1704e0482301c0f82e074090360581702c0a80e04c056be04b5b015ab812d4c094be04a5b0252b81294c1347e02a3b0151b8268cc072be0395b01cab80e54c0727e0293b0149b80e4cc0725e0392b01c9380e48c098be04c5b0262b81314c056be04b5b015ab812d4c0569e06b4b015a381ad0c094be04a5b0252b81294c0d49e06a4b0352381a90c1347e02a3b0151b8268cc072be0395b01cad00e55c092ac0395301ca780e52c0728e0394301c9f80a4ec0526e0393301c9780e4ac0724e039230242f81216c090ae048530242781212c0908e048430241f80a0ec0506e04833024178120ac0904e0482301c0f80e06c0702e03813026b78135ac09ace04d63016378131ac058ce04c630162f81b16c058ae06c53025b7812dac096ce04b63035af81ad6c0d6ae06b5304da780ad2c0568e09b4301d3780e9b4074d603a6a01d33812998074ca03a5f01d2d80e95c074a603a4f0152580a91c0748603a3f01d1d80e8dc074660396f024b700e5b4072be0395b01cad00e55c0d2ac0395301ca7842538052960294a014a380a518072860394201c9f8224f8072760193a01c9b8064d8072660393201c9780e4b80725a0486f0243581219c090c60485f0242d81215c090a60484f0142580a11c090860483f0241d8120dc090660382f01c1580e09c070460381f01c0e80e06c07034f701801c0b80e0580902af601401c0980adbc056da07b6b07db480ad9c056ca0fb6307db080ad7c0f6b602b57025a98569bc034da07a6b0453481e99c034ca09a630453081297c0f4b607a570252983e8fc0547602a3704d198165bc0b2da0396b01cb481659c0b2ca0396301cb081257c0b2ba0395b02cab816554072a60593f0149d80a4dc072660592f01c9581649c0724604d6b026b480adbc056da0fb6b06db480ad9c056ca0fb6306db080ad7c096b602b57025a980699c034ca01a5b0252d00695c034ac01a5300d1f8068ec0346e01a3300cb78065b4032d60196902cb3816594032c601961024af80e56c092ae0395302c9f80a4ec0526e0393300c978064ac0324e0192300f3f8139f803cfa04c7e0263b0071b8038d801c6679a3200adfc096f602b77025b9806dbc036da01b6b06db4806d9c056ca01b6300db083ed240568a01a7b0253d0069e4034ee01a7600d398069c4034ce01a6600d328069240348a01a3f00d1d8068dc034660497f01cbd8125dc072e60196f00cb68065ac072d20196702cb280658c032c20395902ca28164fc052760293701c998064bc032560192700c9180759c03acc02b6f03db580ad9c096c602b5f015ae81ed6c1b6b202b57015aa81ed4c0f6a201a6f00d3381298c094b604a5900d1f80a8ec0346e08a33024b780e5ac0b2ce0396302caf816574072b60395902cab816554072a60395102c9f80a4ec0526e0393302c978064ac0324e03923026bf01f5d8058fe07c7b0163b8131cc1f8b202c5500dbf812df8036fa01b7700dba812dcc096e408b59045ac006d54036a801b4f015a5806d1c1168601a7700d3b0069d40f4b208a5803d2abc49500f49e0da4e0152580a9280548e02a4603d2181e9080947e04a3e0251e8125fc072f60597701cb980e5a40b2aa0594f014a580a51c072860593f00c9d8064dc072660592f02c9680e4ac072520592702c9280e48c0724201e7f00f3f01f9f4038fc09c7c00e3b0071d0098dc07c6600dbf80adf4036f601b7900dbb806dd4036e609b71015b781edac056ce04b6307da480ad14034fe01a7e00d3e8069bc034dc01a6b00d3480698c094c401a6100d248229200348a01a4400d1f8068ec0346e01a3300cbf8165f4032f60197900cbb8065d4032e603971024b780e5ac0b2ce0396301cac8165140b27e0293b0149b80e4cc0325e0192b00c9380648c03ade04c6e0ae2f00adbc096d602b67025b180ad7c196b602b5707da980ad14034de04a6b0253500699c094cc07a5b045248068fc0547601a37045198125bc072d60496701cb181257c072b60395902cab80e54c072a20594502c9f80a4ec0526e0393302c978064ac0324e0392300eb78075b8056de04b6b015b3812d8c056be02b5d07dad836d64056ae02b5507da9836d44034de04a6b0253500699c094cc07a5b03d2c8068fc0547601a37045198125bc072d60496701cb181257c092ba0395b01cac81655c0b2aa0395301ca88164fc052760293701c998164bc032560192701c918135f809aec02c7f0263d80b1dc098e60fc590162a806dfc036fa04b7b025bd006ddc096ec01b75045ac806d540369e02b4b00da3822d0c034fe01a7e00d3e812995dc4c804a590252c012955da4a804a4f06d2700a92c0549402a470152301290c0948404a3f03d1f0128f4092fe0397b024bb80e5cc072d20595502ca780a52c0528e0394302c9f8064ec0326e03933024978124b40725603929024938164940724603921026373d1198056de0fb6b015b383ed8c1f69202b4579137bc09adde4ceec263045248069141f47e02a3b0151b83e8cc0b2de0396b02cb380e58c072b20594502c9f80a4ec0526e0393302c9780e4ac0b24e03923026b78135b807ad603d6a01eb380f59807ac603d620263781319c038be01c5d02e2b817154056de04b6b015b3812d8c056be02b5d085ad836d64056ae02b55085a9836d440d69602b4700d378069ac034ce01a6300d2f806974034b601a5900d2b806954034a601a5100d2580691c0347e01a3b00d1b8068cc072de0396b01cb380e58c032be0195d00cab806554032a60194b01ca380e4fc052760293701c998064bc032560192700c918121bc090ce0485f0242e81215c090aa0483f0141b8060bc0304e0381f01c0b8079fc09cfc01e7d026bf8135dc03ade01d6d00eb381b594058fe04c7b0163b8131cc038de01c6d00e358431a4038ce02c6500e318071840d8b602c5700dbd812de8036f201b7700dbb006dcc036e201b6700db3006d94036b601b5700da7806d2c0368e01b4301d3f80e9ec074f403a770253b00e9cc034de01a6d00d358069a8074d203a6800d33806998074ca05a6400d31806984074ba03a5701d2a80e93c0549602a4701d218068fc0347601a3700d1980e5fc092fc0397b01cbd00e5dc092ec0397301cb90065bc032dc0196d00cb60065ac032d40396901cb400659c032cc03965750b200658c032c40196100cb000e55c0b2ac0395501ca7842538052960294a014a380a518072860394200c9f8064f8032760193a00c9b8064d803266019320243f8121dc030de0186d00c338121940909e0284700c1f8060dc0705e0382701c0f80e0740702e04815026b781b59c058de07c6b0163381318c0d8b602c5700db780edac036ce04b63035ad81ad68036ae06b5600da780ad2c0368e08b4301d3780e9b8074d601a6a00d33806998074c603a620352d8169680b4ae05a5603d278369380549602a4a0152380a9180f48607a420251f8128f80347601a3a00d1b8068d80746603a3201cb780e5ac072d40396703cb300e58c072b60395701ca780a52c0528e0394301c9f8064ec0326e0393301c9780e4b40724e0392501c918121bc090ce1184f014238220fc0306e0782f03c1681e09c2f04a0381f01c0b8139fc0dcee02d7f03ebd80b5dc09ae606d6b016b38071fc098fc01c7d00e3b8071d4098e604c720363581b1a8038ce06c6600e2f80b16c038ae08c5300dbb806dd8036ea06b6b035b501ad9c0d6cc07b5f08daf00ad6c056b402b57015ab01ed4c0f6a404b4f025a7012d34074fe03a7b01d3d00e9dc0f4ec03a7301d3680e99c074ca03a5f0152d80a95c074a603a4f00d2580691c0748603a3f01d1e80e8ec0747203a3701d1a80e8cc074620397f024bf00e5ec072f40397703cbb00e5cc072e40396702cb300e594072be1195e014ad80a568052ae0295601ca980e5480729e0894e00ca58065280328e0194601ca180e5080727e0793e01c9e8224f0072760393a01c9c80e4e00726e0793601c9aba04d0072660393201c9880e4c0090fe0487708c2f80a15c1109e0184703c1f81e0f40f06e1e83501c1780e09c0703e0381d01c0b86e05403cfe01e7e03f3e8075fc0dafa01d7700eba8135bc0dace01c7f0163e8071ec038f201c7700e3a8071cc138e202c6f03e3580b19c098c606c5b0162b806dfc036fc01b7d00db7806db8036d601b6900db1812d88036c201b5b035ad006d5c036ac01b4f00da5806d1c0368601a7f01d3e8069ec034f201a7700d3a8069cc074e203a6f01d3580e9a8074ce07a6601d3180e974074ae03a5501d2780a92c0548e03a4300d1f8068ec0346e01a3300cbf8065f8072fa0997c00cbd8065e8032f20197800cbb8065d8032ea0197400cb98065c8072e20397001cb78125b8072d60396a01cb381e598072c60396201cab816558072aa0394f094a700a52c0529402947014a300e50c072840193f00c9f0064ec032740193700c9b0064cc032640187f04c3e8061dc030ea0486f0243383a13c0508e0183f00c1b80e0bc0704e0381f01c0e80e05c1d02a04d6f026b380b1bc098d602c670263181b16c058ae01b6f025b5806d9c076c606b5b00dab806d3c0569601b47045a18069bc034dc03a6b01d3500e99c074cc03a6300d3101296c094b405a5702d2b04293c1b49c02a4b0152500a91c0548c10a4306d2101e8fc0f47c01a3b00d1d0068dc0346c03a3301d1900e5bc072d60396701cb180e574072b60395701caa80e53c052960294701ca180e4fc032760193701c9980e4bc0725a0392701c9280e48c090de048670242780a11c0907e01837024178120b40904e0482501c0f80e05c09cfe04e77016bf8135ec05aee04d73036b580b59c038fe01c7d0263d8131e8038ee04c7600e3a81b1ac038ce01c5f0162d80715c118a601b7f00dbf006df4096d604b6a025b381ad98096be10b5e015ad80ad68056ae02b56025a9812d480969e07b4e025a680e9fc074f603a7a01d3b8129d8074e603a6d01d3380e994074be02a5b0152b80e94c0749e01a4b00d2380e90c0747e03a3d01d1d80e8e80747203a3801d1b8128d80746a05a3401d1980e8c4072fe0497e01cbd80e5e8072ee0497601cb980e5c8072ce0596601cb280e57c212bc0295b014ad00a55c052ac0395301ca900e53c1129c0194b00ca500651c0328c0394301ca100e4fc0927c0393d0249e00e4ec072740393901c9c00e4dc0926c039357289a00e4cc072640393101c980121fc090ee0485f0142b81213c0308e0483f0241e8120dc0906a0382f01c1380e07c0703a038170240a80f5bc07adc03d6d02e3781719c098be06c57015b7816dac056ce05b63015af81ed6c056ae04b53035a580ad1c0b4de05a6b02d3381698c094be07a5b03d2b81294c0d49606a470951f80a8ec0546e09a3301cb78165b8072da0395f024af00e56c072ae0395301ca900e51c0b28c0394501c9f80a4ec0526e0393301c9780e4ac0724e0392302c3781619c090be0485705c1f80a0dc1305e0b82701c0f80e0740702e0b81501eb780f5b4056de02b6d095b5836da4056ce02b65095b1836d84056be04b5b015ab812d4c1d4de01a6d04d358229a41d4ce01a6504d31822984094be04a5b0252b81294c1d47e02a3b0151b8268cc072de0396d01caf80e56c072a60393f0149d80a4dc072660392f01c9580e49c07246078660242b00f5bc07adc03d6d036378171b40b8ce05c650262f81b1740d8ae06c55015b780adb40f6d612b69015b380ad94256c612b61015af81ed6c056ae04b53035a580ad1c2d4de01a6d03d358229a40f4ce01a6504d31822984094be07a5b03d2b81294c0d49606a470951f80a8ec0546e09a3301cb780e5b4072ce0396501cb180e57c072b60395901cab80e54c072a20394b01ca380e4fc052760293701c9980e4bc072560392701c9185a1bdc40da078674883281217c090ae1283f0141b8260bc8a04e0381f01c0b80b1bc098d602c6702631812dbc096d604b67025b183ad3c0569602b4704da180e9bc074ce03a6301d2780a92c0548e03a4301d1f80e8ec0746e03a33024b38125980f2ca0794f06ca700a52c0529402947014a301e50c0f2840793f0449f01e4ec032740793700c9b01e4cc0f2640392f01c9700b1bc258d602c6702631812dbc376d60eb67025b183ad3c0569602b47095a180e9bc074d603a6a01d3382e998074c603a4f0152580a91c0748603a3f01d1d80e8dc074660496f024b705e5adc02d417967488b301258c092c41294f094a700a52c0529402947014a304a50c252841793f0449f03a4ec032740e93700c9b06e4cc11264900660942710c0d80705c0381e 20 1048575 8 255 11 2047 21 2097151
def cc_63_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x96b2a903688ba49837837f2457bf3376c537204c6e13f6954c67d1866518643225c67d565615392c4e6534b92d46653405613b64f355613064f2a16525a4720b4f1c24913e8410c320b8540516700051 0x4d6e00e338071940f8aa02b6f03db581eda4056ce07b6307db080ad3c0f69602b4703da18069bc034dc01a6d00d33806994034c607a6200d258068fc0347601a3700d1981a5bc0d2d606967034b181a53c0d29606947034a181a4fc0527602937034998064bc032560192700c918075fc03afc01d7d00ebe0075ec0faf401d79046bc0075dc03aec01d7500eba0075cc09ae401d71026b80075bc03adc01d6b03eb50075a63cad001d6700eb300758c09ac401d61026b00131f8098dc01c5e015bf80adf40f6f60cb79015bb80add4196e60fb71015b781edac056ce04b6300daf80ad74036b601b5900dab806d54036a60fb51015a28069fc034fc01a7d00d3e0069ec034f201a7700d3a8069cc134e401a71045380069bc034d607a6a00d33806998034c601a4900d1f8068ec0346e01a33034bf8165f40d2f603979034bb8165d40d2e603971024b781a5ac0d2ce0496300caf816574032b60195900cab806554032a603951034a281a4fc0527602937034998064bc032560192700c9181f5ac0face02c6b03e3500b19c058cc02c5f0162e80b16c0f8b402c570162b00b154038a607b6b03db501ed9c0f6cc02b5f015ae806d6c036b401b5700dab006d54036a801b53015a780ad380969a01a6b00d3380696c034ae01a5300d2780692c0348e01a4300d1f8068f40347601a3700d1a8068cc0d2d60696703caf81a56c0f2ae06953014a780a52c0528e0294303c9f81a4ec0f26e0693300c978064ac0324e0192303c2f81e15c0509e0284703c1f81e0dc0305e018270340f81e05c03cfe01e7e00f3d81f9e803cf31c67800f3b8079d803ce604e7200f388139c009afe07d7700eb78075b811ada02c7f0163f00b1f4058ee02c75016398131c8038de02c6d00e358071a4038ce01c6500e3180b184058b60fc5a0162b80b158056ee02b76015ba806dbc036dc10b6d085b6006dac036d401b6900db4006d9c036cc01b6500db2006d8c036c407b618d1b001ed6c196b407b57065ab00ad3c0569c04b4d00d3f8069ec0f4f401a7700d3b0069cc034b601a5900d2880693c0349601a4700d218068fc0347a01a3b00d1c8068dc0346a01a3300d188125fc0d2f607977024b98065bc0b2da0196b00cb480659c032ca0196301cb081a56c0d2ae0294f014a580a51c052860793f02c9e81a4ec072720793702c9a81a4cc072620192f00c9580649c032460487f0243b8061bc1d0da0186700c3280a13c0508e0783f0741e83a0dc1d06a0182f04c1680609c0304a0681f0740b8135bc0face02c6f00e3580b19c058c602c5b03e2d00b15c058ac07b6703db301ed940f6b607b5a03dab81ed580569e02b4e03da68069bc034d601a6700d3180696c034ae01a4f00d2580691c0348601a3b00d1c8068dc0346601a31024b781a5ac0f2ce04963034ad81a55c0529e0294b014a380a50c0f27e0593d0349d80e4e40f26e059350349980e4c40325e0192b00c9380648c090de048670142780a11c0f07e0783d03c1b83a0d40305e018270340f81e05c1bcfc09e7d04ebe80b5d4058fa01c7900e3a8071c4058d202c6106e2d00b158096fc04b7d025be012db80f6d40db6903db4012d88136c209b60045ad00ad580369c01b4d00d3e8069e4034ea01a7100d268069140347201a3500d188165f4072f20597501cb88265b41b2ca0d93d0349c8364d40d2620e87d0743a8261b41d0ca0d83d0741a81f5bc0fadc07d6d03e3781f1b4058ce02c650262f81f15c056de02b6d00db5806da4036ce01b6500db1806d84056be02b5b015ac806d5c056a602b51015a581ed280568e02b4600d378069b4034d601a6900d33806994034c601a6100d2f80696c034ae01a5300d2580691c0347e01a3b00d1b8068cc0f2de0596d034b580e5a40f2ce05965034b180e584092be0795d034ad81e55c0f2aa04953034a581a51c0527e0293b0149b80a4cc0325e0192b00c9380648c0f0de0e86d03c3381e194090be0985d0242b81e1540507e0283700c1780609c0d03e0781704eb783f59c058de02c6b0163380b18c058b60fc5a0162b80b158136de04b6e06db5c68daa326cf1836604db1812d88116b608b5a015ab80ad580369e01b4e00da68069bc034d601a6700d3180696c034ae01a4f00d2680692c0348e01a4500d218068ec0347201a3700d198068c4132de0696b06cb381a58c0d2b606957014a780a52c0528e0294306c9f8164f40d2760393906c9b8164d40d2660393100c978064ac0324e0192304c3783a19c0509e0284706c1f83a0f41d06e0e83500c1780609c0d03e0d81700eb78075b803ad601d6700eb1813588098de07c6700e2f807178118ba02b6f03db580ad9c096c601b5f00dad806d5c036a60fb4b015a380699c034cc01a6500d2f806978114ba07a4b03d238228fc0547602a3703d198125bc0d2d607967024b180657c032b60195700ca981a52c0d28e1193f0149d80a4dc0d2660792f0349581e49c0d2460486f0243380617c030ae0e83f0141b81e0bc1105a088270741281a07c1d02e01d6f00eb70075ae3ead401d6700eb300758c09ac409c6f8ea3380717c038bc08c5d015b7c6cdac056ce09b6300daf80ad74036b601b5900dab806d54036a71735107da580ad1c034de01a6b8b13500699c034cc01a6300d258069240348201a3f00d1d8068dc034660996f034b5bec59c0d2c60195f02cae80656c032b20195700caa80654c072a20694b034a3b0c4fc0527602937034998064bc032560192700c918261bc1d0ce0185f0742e80615c030aa0e83f0141b8060bc1d05a0182700c1281a07c1d02e02b5f025ad80ad5c096a601a5f0252d80695c094a601a3f0151d8068dc114660495f024ad81255c092a60693f0149d80a4dc0d2660692f00c9580649c0d24602b5f04dad80ad5c136a601a5f0452d80695c114a601a3f0151d8068dc114660685f0342d81a15c0d0a60683f0141d80a0dc0d0660682f00c1580609c0d04602c6f04e3580b19c138c601b6f045b5806d9c116c601b5500da780ad2c0368e08b43025370269981f49c02a460451f01a5bc0d2d606967034b181a53c0529602947034a181a4fc03276019370349980e4a40b24b14028898120135fc09afc04d7d026b78135b809ac402c7f0163e80b1ec058f202c770163a80b1cc058e202c6f0163580b19c058c602c5b0162b806dfc236fc01b7d08dbe006dec036f401b7900dbc006ddc0f6ec01b7508dba006dcc036e401b7100db8006dbc096dc01b6b00db5006d9c0f6cc01b6300db1006d6c036b401b57065ab006d3c0569c01b4d00d3f8069f8034fa01a7c00d3d8069e4034ee01a7500d398269c8034e208a7000d378069ac034ce01a6300d2d80695c0349602a4a00d2480691c0348c01a4300d208068dc0346c01a350ccbf8165f40d2f60397909cbb8165d40d2e603971024b781a5ac132ce04963034ad81a55c0529e0294b014a380a50c0327e0193d00c9d80e4e40326e0593500c998064c40325e0192b00c9380648c1d0fe0e87d0743b83a1d4090de048670142780a11c0307e0183d00c1b83a0d40305e018270340f83a05c13ade0fd6b88ab382758c058de02c6b0163380b18c058be02c5b0162b80b14c036de04b6e00db5806da8036ce11b6600db1806d88036be01b5b00dad006d5c236ac01b5300da780ad380369a01a6f00d3580699c034c601a5f00d2d80695c034a601a4b015250069240348e01a4600d218069040346e01a3600d1a8265bc252d6f916704cb183e57c252b6d515707ca980a53c0529602947014a18064fc0327a0193b01c9c8064dc0b26a0193300c988064bc032560192700c918261bc150d60e86704c3183a17c150b60e8570542980a13c0509602847014218060fc0307a0183b00c1b83a0d4030660182f00c1580609c030460e81f0540d83a05c1502604d6f026b70275ac0fad409d6703eb301358c09ac402b6f015b580ad9c056c602b5b015ac8069bc114d601a670253182296c114b201a3f0151d8068dc092de0696b04cb381258c172be0595d034ad80e564172ae05955034a980e5440527e0293b0149b80a4cc1125e0192b00c9381a48c190ac09d6f026b70275ac13ad409d6704eb302758c09ac409c6f04e3502719c138cc08c5f0462f023174056de02b6b015b380ad8c036b601b59015ab80ad4c036a202b4b015a480ad1c0568201a6f0453580699c114c602a5b0152c80695c054a602a51045258229240348e08a4100d1f80a8ec0346e02a3304cb781a5ac132ce069630d4af8165740d2b603959064ab8165540d2a60395107ca681a52c0d28ed41450149f80a4ec0526e02933044978064ac0324e0692304c3782619c350bf0f05d0642b9e41541f09a780450141f80a0dc1105e018270340f89c05c058de02c6b0163380b18c036de08b6b00db3812d8c0369e02b4b00da38129bc094dc09a6b03d3502699c0f4cc04a63025310329540549e02a4e0451f8228f8092de0696b04cb381258c0529e0294b014a380a50c1127e0193b00c9b81a4cc1725e0592d0349580e4a41724e059250349180e484130cc04d6f04eb380b1bc058d602c670163180b16c058ae01b6f045b5806d9c096c608b5b00dab806d3c0569601b47015a18129bc094dc09a6b04d3502699c134cc04a630253107296e1a4b417a573c92b00693c0349c02a47015218069080547e02a3e00d1b80a8cc054640496f04cb582659c092c61295b05cab80a53c0529602947014a18224fc03276019370449982e4bc0b25a1292b01c9482e49c0b24a1292301c908121bc130d40486704c3302a168ee0ac0284f0142700a11c050840883f0441f0060dc110640882f044170220b41503e0a81a0540b89405813ade09d6b04eb382758c058de02c6b0163380b18c058be02c5b0162b80b14c036de08b6b00db3822d8c036be08b5b00dab822d4c0369e01b4d015a580ad280368e02b4600da28229bc094dc08a6b0453502299c134cc08a630253102297c114b608a5a0452bc38958114a601a4f00d270069340547e02a3e0151e8265bc132d60996704cb183e57c252b6d315707ca980a53c0529602947014a18224fc0327601937044998224bc0b25a0892b01c9482249c0b24a0892301c908261bc130d60986704c3183e17c150b6760570542980a13c0509602847014218220fc0307601837044198220bc1105a0882b04413c30094110461281f0540d89005c1502603d6b01eb481359c09ac603d61026378131b8098da04c5f0262f01315c098a402b6f015b681edac216d202b67015b2842d8c216c202b5f025ad80ad5c096a606b4b015a38269bc034da07a6b0453481e99c034ca09a630453081297c094b604a570252981a92c0d48e09a3f0151d80a8dc134660596f02cb680e5ac0b2ce05965024af80e56c092b404957024ab00e54c0b29a0394b02ca38165140b27e0293b0149b80e4cc0b25e0392b02c9380e48c090de0486d02433812194090be048570241f80a0dc0905e0482701c0f81205c07ade03d6e01eb68131bc098d604c670263181317c098ba04c5b0262bc29154098a602b6f025b580ad9c096c602b5f015ae812d6c216b202b57015aa812d4c096a202b4f085a580ad1c0d68604a6f0253581299c094c604a5f00d2e81296c114b204a5700d2a81294c094a206a4f04d2582691c0d48609a3f0151d80a8dc134660396b024b500e5a4092ce0496601cb180e584092ae0495602caa81653c072960594701ca18164fc052760293701c998164bc072560592701c918121bc090d6048670243181217c090ba0485b0242b812154090a60484f0242581211c090860483f0141d80a0dc090660482f0241581209c090460381f0240d81205c0702604d6f026b380b1bc098d602c670263181b16c058ae04b6f025b5812d9c096c606b5b035ab83ad3c0569602b4704da180e9bc074d603a6701d3180e96c074ae03a4f0152580a91c0748603a3f01d1d80e8dc074660496f024b58125a8092ce04966034ad81a5680d2ae06956094a784a538052960294a014a380a518252861294204c9f8224f81d2760193a0749b8064d8132660893201c9780e4b80724e0392301c910121bc090d4048670243301213c0508e0483f0241d0120dc8e06c0382f01c1700e09c070440381f01c0f00e07409ade06d6b036b381358c058de10c6b0163381318c058be06c5b0162b81b14c096de09b6b04db3812d8c0d6be06b5b035ab81ad4c2569e02b4b015a3826d0c074de04a6e01d3680e99c074ca03a6301d3100e97c074b603a5a01d2b81a958074a603a4f0152580a91c0748603a3f01d1d80e8dc074660396702cb300e594072be0395b01cad00e55c0d2ac0395301ca784a538052960294a014a380a518072860394201c9f8224f8072760193a01c9b8064d8072660393201c9780e4b80725a0486f0243581219c090c60685f0242d81a15c090a61284f0142580a11c090860983f0241d9180dc090660382f01c1680e0ac0704e0e02501c1180e07c0703a0381b01c0bc200540702604d6f036b380b1bc058d602c670163180b16c0d8b402c570162b012dbc0d6d606b6a03db381ed980b6b605b5a015ab80ad580569e02b4e03da68129bc0f4d607a670253181a96c0d4ae02a4f0152580a91c0548607a3f00d1e81e8ec1147207a3700d1a81e8cc0f4620496f01cb580a59c072c60395b02cab80a53c0529602947014a18164fc0b27a0393b02c9b8164d40b25e0392b02c9380e48c090de048670142780a11c0f07e0783d03c1b82e0d41305e0b82701c0f81605c07ad603d6a036b380f59809ac604c6f0363501b19e088cc05c5702e2b017154056de07b6b015b3812d8c056be02b5d03dadc18d64056ae02b55065a9bf8d440d696ff349015a381ad04094de07a6b03d3381298c194be01a5d03d2d8229640f4ae01a5504d298229440d49606a477d11f80a8ec0546e09a33024b780e5ac0b2ce03963024af8125740b2ae0495501ca9816534072960594702ca28164fc052760293701c998164bc072560592701c918121bc090ce0b85f05c2e81e15c170aa0b83f0141b8260bc1704e0381f02c0b80f1ac0b8ce05c650263180f16c098ae06c550262980adbc0f6d607b69015b381ed8c1b6c202b5f025ad80ad5c096a602b4f03da580ad1c0f68607a6f03d3581e99c0f4c604a5f0252d81295c094a607a4f03d2581e91c0f48609a3f0151d80a8dc134660596f02cb70165b4072d60596702cb280e58c0d2c40495f01cad81255c072a60494f024a380e50c0b27e0293b0149b80e4cc0b25e0392b02c9380e48c090de048670242f81215c0909e048470241f80a0dc0905e0482701c0f81205c07cf603e7a01f3c80f9e00bcee05e7602f3a8179d00bce603e7101eb780f5b807ada04c7f0263f0131f40b8de05c6e03636c111b00b8ce05c6502e3101317c098bc04c52015bf80adf40f6f607b79015bb80add40f6e60db71015b780adb40b6d605b69015b380ad940b6c610b61015af80ad74096b602b57015aa812d4c0d69602b4703d3f8069f40f4f607a7903d3b8069d40f4e608a7102d378069b40b4d605a6902d338069940b4c608a610252f812974094b604a5703d2a81294c0d49606a4704d1f80a8ec0546e09a3302cbf8165f80b2fa0597c01cbd80e5e40b2ee0597501cb981a5c8072e203970024b78125b8092da0495f024af00e56c072b203953024a900e544072960694a02ca38165180b27e0293b0149b80e4cc0b25e0392b02c9380e48c090fe0487d0243b8121d4090de0486d02433812194090be0485d0242b8121540907e028370241781209c0703e0481d0240b81205405cfc06e7a0173b00b9c81badc06d6d03e3d00b1d8058d202c650163080b164058a202b7e01dbd00add8056e406b5a06dac832d600d6a206b50015a7016d34034da08a6900d328229840d4ba18a5506d1e8268e43146a09a3102cb680a5a4052ca0296102ca680a5140927a029390149a80a4c4170da0b8650342e82e1541707a0b835016b780b5b80dad606d6a016b380b59805ac602d620263781b19c0d8be0cc5e0362e80adbc056d607b6a015b380ad98056c602b5b015ac80ad5c056a602b51015a580ad240568e02b410253781e9ac0f4ce04a630652f806974134b608a590652b806954134a608a510352681a92c0d48e0ca450151f80a8ec0546e02a33024b780e5ac052ce0396302caf816574052b602959014ab80a554052a60295101ca581651c0527e0293b0149b80a4cc0b25e0392b02c9380e48c090de0486705c2f82e174170ae0b8550342682e1140507e0283704c1782e09c0703e05817026b781b5ac21ace04d630163780b1ac218d402c670163300b18c058be02c5b0162b80b14c056de02b6e01db580eda8056ce02b66015b180ad880d6be0db5b7f1ad408d5e026ac06b53015a780ad380b69a04a6f04d3582699c094c606a5f04d2d86295c0d4a602a4f0152580a91c054860da3f00d1e8268ec1147218a3700d1a8268cc114620496f01cb580a59c072c60595f01cad81655c072a60294f02ca680a52c0528e02945014a18124fc0927a0293b0149c80a4dc0526a02933014988164bc072560592701c918121bc090d6048670243181a17c090b60b8570242980a13c05096028470142182e0fc1707a0483b05c1b82e0d4090660982f0241582e09c090460381f0240d81605c0702603d6b036b381358c058de02c6b03e3500b19c058cc02c630162f80b174058b607c5a0162b80b158058aa02c53025b781edac0f6d407b6703db3012d8c056be02b5d02dad816d68056ae02b56015aa80ad50056a604a6f03d3581e99c094c60ca5f03d2d81e95c134a602a4f0152580a91c054860ca3f04d1d8328dc134660496f01cb580a59c072c60495f02cab80e54c0529e0294b014a380a50c0b27e0593d01c9d8164dc0b26a0393302c9780e4ac0b24e039230243781219c170be078570142780a11c1707e0b83704c1782e09c0703e05817 20 1048575 8 255 11 2047 21 2097151
def cc_63_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x8653109a6209543e16376daae1985b261b48396625cc3b1574e52ceb657d40a5d3d3370a50ac4549a84eb4f4aa9b7e32f2fa58cb0a160911631cdaa2d9844e9908d200e7661373013a68004e 0x2b5f025ad80ad5c096a604a5f0252d81295c094a609a3f0151d80a8dc134660495f024ad81255c092a60693f0149d80a4dc0d2660692f0349581a49c0d24602a5f0252d80a95c094a60495f024ad81255c092a60992f0149580a49c132460485f0242d81215c090a60682f0141580a09c0d0460681f0340d81a05c0d02604d660263700adbc096d602b67025b183ed268669002b45015a20129bc094d604a67025318229268449001a45a09220268fc0547602a3704d198125bc092d604967024b180e52680290059459f8a201a4fc05276029370349981a4bc0d2560692703491cf81227a08804d6f07eb584359c09ac602c6f0163700b1b4058ce02c6501631813188058be02c5b9c22d00b15c058ac02c53015b380ad98056ca0fb5f085adcd4d68216ae10b5607da980ad3c0569c04b4d025378269ac134ce04a6307d2f82696e364ae09a530152780a92c0548e02a430851f8068f41347608a390851b8068d41346608a31024b78425ac212ce0496307caf84a56dba2ae0f953014a780a52c0528e029430849f8164f421276039390849b8164d4212660393104c9784a4ad6424e09923024378121ac090ce0486307c2f81216cfa0ae048530142780a12c0508e028430841f9b00f409076108370841a8120cc1305e0482b2f81381208c2503e0481b1800b81204c05ade02d6e016b380b58c05ac404c6f0263700b19c098c404c5f0262f013174056de02b6b025b500ad9c056cc02b63015ad80ad64056ae02b53015a880ad2c0569202b47015a08129bc094d604a670253182697c034ba09a5b0452c82695c034aa09a53045288269341349609a4704d2280a8fc0547602a37015198125bc092d604967024b185657c0b2ba0695b01cac83255c0b2aa0695301ca883e5340d296069476e0a280a4fc0527602937014998264bc0d25609927034918121bc090ce0485f0242e81215c090aa0484d0242280a0fc0506e0482f0241381207c0902e04d6f026b581359c09ac602c6f0163680b1ac098d402c670163300b194058be02c5b0162b80b14c056de02b6e015b6812d7c096b604b5a025abce8d58096a602b4f015a7012d34094de04a6b0253381298c134be09a5b04d2b82694c0549e02a4b0152380a90c0947e01a3d0251d8228e40946e01a35025198128c4092de0496b024b381258c1f2be1295b6d8ab83e54c0529e0294b014a380a50c0927e0493d0249d80e4e40926e059350249980e4c41325e0992b04c9382648c090de0486b0243381218c090be0485b0242b81214c0509e0284b0142380a10c0907e0483d0241d8120dc0906a04833024178120ac0904e048230240f81206c0902e04813026b781f59c098de04c6e07e3681f1ac0f8ce0fc6502631813188058ae02c560162a80ad9c056cc02b6507dae81ed6c0f6ae10b55025a7812d341b68e04b4503da18129bc0f4d607a670253182696c1f4ae0da4f04d2583e91c1348607a3f04d1d8428dc0f4660496f034b581e59c092c60695b034ab83653c0d2960d947034a181e4fc0d27607937034998264bc0d2560d927034918121bc090ce0d84f07c2381e0fc2106e0982f0c41381a07c1b02e04d6f016b381f19c0f8cc07c6503e2b81f1580f8aa02b6f015b380ad8c096b602b57015a380ad14094de07a6b03d3381298c0f4b607a5703d2781e92c0f48e07a4306d1f8268ec1b46e09a33024b781a5ac0f2ce04963034ad81a55c0f29e0694b03ca381a50c0f27e0693b03c9b81a4cc0f25e0692b03c9381a48c090de0486703c2781e11c1b07e0d83704c1784e09c0d03e078170163780b19c058c604b67025b300ad3c0569c04a6f0253581299c094c602a4f0152580a91c054860ea3f00d1e8268ec114720ea3700d1a8268cc114620496f024b581259c092c60294f014a580a51c052860b93f02c9e81a4ec072720b93702c9a81a4cc072620992f0349582e49c0d246048660142701e0f809ade02d670163780b1ac058ce02c630162d80b15c0f6ce0fb6607db281ed5c1f6ac10b55015a780ad3a6e69a04a6f03d3581e99c094c609a5b0652b80a93c0549602a470152181e8fc0347a09a3b0451c84e8dc0346a07a33045188125bc0d2d607967024b181a56c0d2ae0294f014a580a51c052860793f02c9e81a4ec072720793702c9a81a4cc072620992f0349583649c0d2460486f0243380a13c0508e0783f3581e8660de6c06a0982f0c41381a07c1b02e0fd6f07eb380b1bc058d73846a0163380b198058c602c5d0162b80b1541f6de04b6e07db5cd4da81f6ce0fb6607db1812d88056ae02b56015aa8429bc234d72a2670853183e96c1f4ae02a4f0152580a91c054860fa3f00d1e83e8ec114720fa3700d1a83e8cc114621096f034b5bf459c0d2c60695b034ab80a53c0529602947014a183e4fc0b27a0693b01c9c83e4dc0b26a0693301c988464bc0d256b1127034918421bd240ce0284f0142383e0fcd207a0f83707c1a8460bcbc04e0681f1780b80adbc056da02b6b015b480ad9c056ca02b63015b080ad7c056b602b59015ab80ad4c056a215a6f00d3681e9ac114d207a6700d3282698c114c204a5f0852e81e96c0f4af292550252980a8fc0547602a370151981a5bc0b2da0696b01cb481a59c0b2ca0696301cb081257c0d2ba0695b034ab81a554092a60293f0149d80a4dc052660692f0349581a49c0d24602c6f0163580b19c058c602c55025b74ccd980569c10a6f08d35ca099c214c602a4f0152580a91c0548608a3900d1a81a5bc0d2d606967034b180a53c0529602947014a180e4e40b26a0692f0349581a49c0d24604d6b026b481359c09ac604d6100e378071b8038da04c5f0262f01315c098a402b6f015b6832dac216d202b67015b2842d8c216c202b5f025ad80ad5c096a60cb4b015a38069bc034da01a6b00d33806994034be01a5b0252d00695c034ac01a5300d2680692c0348e01a4500d1f8068ec0346e01a330acb78165b40d2d603969064b38165940d2c603961024af81256c092ae04953034a581a51c2127e0293b0149b81a4cc0325e0192b00c9380648c090de0486d02433812194090be048570241f80a0dc0305e018270240f81205c03ade04d6e00eb68131bc098d604c670263180717c038ba01c5b00e2bcc5154038a602b6f025b580ad9c096c601b5f00dae806d6c216b201b57015aa806d4c036a202b4f085a580ad1c2168601a6b025350069a4034ce01a6600d31806984034ae01a5600d2a80693c0349601a4700d218068fc0347601a3700d198125bc092d604967024b180657c032ba0195b01cac80655c0b2aa0195300ca8bc853dd2296da147680a18424fc0527602937084998064bc032560192700c918121bc090d6048670243180617c030ba0185b00c2b812154030a60484f0242581211c090860483f0141d80a0dc090660182f00c1580609c030460481f0240d81205c0902604d67026b300adbc096d602b67025b180ad7c056ba07b5b06dac80ad5c056aa07b5303da88069bc034ce04a630252d8129640347e02a3b00d1b8228cc092de0496b024b381258c0f2be0595d034ad80e5640f2ae05955034a980e5440f27e0293b0149b81a4cc0f25e0192b00c9381a48c0f0ac04d6f03eb58075a803ace01d66026378271a80f8ce09c6603e2f823178118ba02b6f03db580ad9c096c602b5f015ae832d6c236b202b57015aa81ed4c236a20cb4b015a38069bc0f4d601a670253181296c094b201a5703d298129441149608a4900d238229040347e02a3b00d1b8228cc092de0696b03cb381258c0f2be0595d034ad80e5640f2ae05955034a980e5440d2960694708c9f80a4ec0526e06933044978064ac0324e069230243781219c0f0bf2f05d0642b9f01542307e028370441780609c0d03e2e017016378131ac058ce04c6300db7806d9c096c601b4f015a5806d1c1168604a67025330329541949e0da4e0152580a9280548e02a46065218329081147e08a3e024b78125ac092ce0496305ca780a52c0528e069430449f8064ec0326e0693305c978164b40d2560392905c938164940d24603921024330135bc09ace02c6f0263580b19c098c611c5b0162b806dbc096d601b67025b1822d6c116b401b57075ab006d3c0569601b47045a18129bc094d601a6a00d33806998394b72d25a0bd2b9f09582349e11a4e0152580a9280548e02a4608d218469080947e04a3e00d1b8128cc094640496f024b581259c092c61e95b05cab82e53c052960294708ca18224fc03276019370449982e4bc0b25a1792b01c9482e49c0b24a1c92301c908121bc090d40486702433012168f60ac0484f08c2700a11c090840483f0441f0060dc090640482f044170120b40903e0481a0240b8b005809ade09d6b04eb381358c058de09c6b0163381318c058be11c5b0162b84714c036de04b6e00db6806d9c036ca04b63025b1006d7c116b608b5a00dabc58d58116a601b4f015a5806d1c1168601a6700d33006994114be08a5b0452d02295e5c4ac08a53045278469380549602a4a0152380a9181148608a420251f8128f80947a0496f04cb582659c092c6f015f738adb6455d9c2a61194f014a580a51c232860893f00c9d8064dc112660892f02c968224ac072520892702c9282248c072420486f0243581219c090c68405f0242d9e815c090a61184f0142580a11c090860883f00c1d8060dc090660882f044168120ac1104f2c025024118dc07c090362b017024098079fc03cfc08e7d00ebf8275f403aee01d75026b781f59c038fe02c7d00e3d8071e4038ee01c7500e3980b1c4058de02c6b03e3500b19c058cc02c630162e80b15c058aa01b7f00dbf026df4136f801b7b00dbd006de4036f001b7700dbb006dd4036e801b7300db9026dc4136e004b6f025b701edac0f6d407b6703db3012d8c096c402b57015ab00ad54034fe01a7e00d3e8069bc034dc01a6b00d3480698c094c401a6100d2d826968034ae01a5600d2780692c0348e01a4300d1f8068f40347601a3900d1b8068d40346601a3100cbf8165f4032f60197900cbb8065d4032e603971024b781a5ac0f2ce04963034ad81a55c0529e0294b014a380a50c1f27e0593d0349d80e4e41f26e059350349980e4c40325e0192b00c9380648c030fe0987d00c3b8061d4090de048670142780a11c1d07e0e83d0741b83a0d40305e018270340f83a05c03ad601d69015b780adac056ce02b6300daf806d6c036b201b5700da980ad44034de01a6e00d358069a4034c607a6200d3080697c034bc01a5d00d1f8068ec0346e01a33034b781a5ac0d2ce0696300caf816574032b60195700caa80654c0527e0293b0149b80a4cc0325e0192b00c9380648c03cfe01e7e03f3e8071fc058fa01c7b00e3c8071dc038ea01c730163880b1bc058d602c670163180b154036fc09b7c00dbb006dd0096dc04b6c03db34a4d900569c01a7f00d3f0069f4034de01a6e00d358069a4034c604a6200d3080693c0349601a4700d218068e41147001a3500d1a0065fc0b2fa0197b00cbc8065dc032ea0197301cb88125bc0d2d606967024b180a53c0529602947014a180e4e40b26a0192f00c9580649c0324601d6f00eb70235b4038de09c6d00e3580719c038ca01c630262f82716c138ae04c5300db780adb4036d601b6900db3806d94036c609b61015af826d6c056ae04b53015a7ca8d2c0568f2834300d378069b8034da01a5f00d2f00696c034b201a53025290069440349e01a4b04d2500691c0348c01a4300d1f8068ec0346e01a3300cb78165b4032d60196900cb3806594032c603961024af82656c132ae04953778a7b9852db028ecd1436289f80a4ec0526ec113300c978064ac0324e0192300c378261b4030d60186700c3280618c090be0485b0242b81214c1d09e0484b0742381210c1d07e0283b0141b8120cc0305e0182b00c1380608c1d03e0481b0740b81204c03ade01d6e026b381358c03ac404c6f0263701319c098c404c5f0262f013174056de04b6b015b3812d8c056be02b5d065ad842d64056ae02b55085a9842d440569a0cb4b015a380ad14034de04a6b0253500699c094cc04a630452d822964034ae08a530452882292c1149201a47045208068fc0547601a37045198125bc092d604967024b185657c0b2ba0695b01cac83255c0b2aa0695301ca8bb85340d296069476b8a28424fc0527602937034998224bc0325601927034918121bc090ce0485f0242e81215c090aa0484d024228120fc0506e0482f00c1381207c0902e04d6f026b581359c09ac602c6f0263580b19c098c602c5f0862d80b15c218a601b6f00db6812dac096d401b67025b3006d94036be08b5b00dab822d4c0369e02b4b00da3822d0c034de01a6e00d3681297c094b604a5a0252bc98958094a604a4f0852700a92c0549402a470152301290c0948404a3f0451f0128f4092de0496b024b381258dd82bee415b6b0abb2c54c2129e0294b014a384250c1127e0193b00c9b8224cc0925e0492d0249580e4a40924e059250249180e484090de0486b0243381218c090be0485b0242b81214c0909e0284b0142381210c0907e0183b00c1b8120cc0905e0482d0241581209c0904a048230240f81206c0902e04813015b780adb40f6d60fb69015b380ad941f6c60fb61015af81ed6c056ae04b5300d378069b4034d601a6900d33806994034c601a6100d2f806974034b601a5700d2a80694c0347e01a3b00d1b8068cc0d2de0596d034b580e5a40d2ce05965034b180e584092be0695b034ab81254c0d27e0293b0149b81a4cc0325e0192b00c9380648c098dd24466015b783edac056ce09b6307da480ad14034de01a6b00d3380698c034b201a4500d1f8068ec0346e01a33034b781a5ac0d2ce0696301ca48165140d27e0293b0149b81a4cc0325e0192b00c9380648c058de09c6b0163381318c036de08b6b00db3812d8c0369e02b4b00da3822d0c094de04a6e04d358269a8134ce09a66025318129882349e11a4e0152580a9280548e02a4608d21846908092de0696b04cb381258c1729e0294b014a381a50c1127e0193b00c9b81a4cc1725e0592d0349580e4a41724e059250349180e4841107c0882e1480b0275bc13ace02c6f04e3580b19c138c60fc5b0162b806dbc116d608b6a00db3826d98116c601b5d00dab806d540369e02b4b00da3822d0c114de04a6e045358229a8114ce09a6604531812988034ae01a5600d2a82293c2349c02a4b0152500a91c0548c08a43045210265bc0d2d609967034b181a56c0d2ae1194f014a580a51c0d2860893f00c9d8064dc0d2660892f02c9681a4ac072520892702c9281a48c072420986f04c3384613c0508e0883f0441e8060dc9206a0882f0441682209e4404a0681f1400b8135bc0face02c6f0163581f1a8058ce02c6600e3180b16c058ae02b6f015b7006dac036d401b6700db3006d8c036c409b5b04dad036d5c196ac02b4f015a701ed34034de01a6b00d3380698c034b601a5700d2780692c0348e01a4300d1f8068f40347601a3900d1b8068d40346601a31024b781a5ac0f2ce04963034ad81a55c0529e0294b014a380a50c1b27e0593d0349d80e4e41b26e059350349980e4c40325e0192b00c9380648c090de048670142780a11c1b07e0d83d06c1b83a0d40305e018270340f83605c09ade09d6d03eb3c79594038ce01c6600e3281f16c118b407c570462b00adbc0f6d71c369015b3812d8c136c20fb5b015ab80ad3c0569a16b4b901a480ad1c0568a07b438d1a08069bc034da01a6b00d33806994034c601a5b00d2b80692c0349201a4700d218069040347e01a3b00d1b8068cc092de0696b03cb381258c0d2b60695703ca78165340d2960394903ca38165140d286039416209f80a4ec0526e0693300c978064ac0324e019230243781219c0f09e0e84d0742383a1141d07e0283700c1780609c0d03e0e817 19 524287 7 127 11 2047 21 2097151
def cc_63_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xc1f22eeb2b7a82a86da60825f7291ebe21cc79fd1c7c0645b557744dd0100ed3653cc32c2a6cc962721e74604f0f1203018090601818030600018 0x131a8098ce04c660262b81315aae8aa02b6f025b580ad9c096c602b5f015ae812d6c216b202b57015aa812d4c096a20fb4b015a38129bc094d604a670253181297c034ba04a5b0452c81295c034aa04a530252882692c1348e09a3f0151d80a8dc134660496f024b581259c092c60495f024ae81256c072b20495702caa81254c072a20694b034a38424fc0527602937034998264bc0d25609927034918121bc090ce0485f0242e81215c090aa0483f0141b8120bc0904e0481f0240b8131b8098bc02b6f015b681edac1f6d202b67015b283ed8c1f6c202b5f025ad80ad5c096a609a6f00d3681e9ac114d207a6700d3282698c114c204a5f0252d81295c094a609a3f0151d80a8dc134660696f02cb681a5ac072d20696702cb281a58c072c20495f024ad81255c092a60693f0149d80a4dc0d2660692f0349581a49c0d24604d6eaba3300adbc1f6d602b67025b183ed240568a04a6f04d3582699c094c608a4900d2283e8fc0547602a3704d198125bc0d2d606967024b180e5240b28a0693f0149d80a4dc0d2660692f0349581a49c0d24604d7f026bf0135f409ade04d6e026b100b1fc058fc02c7d0163e00b1dc058ea02c7303e3900b1c66e8e002c6f0163580b19c058c602c5b0162b80addc056ec02b75015ba01ed9c0f6cc07b6507db201ed5c0f6ac07b55085aa00ad3c0569c07b4d03d3f84e9f40f4f607a7903d3b81e9d40f4e609a710253781e9ac0f4ce04a6303d2d81e95c0549e02a4b0152380a90c0f47e01a3d03d1d8228e40f46e01a3503d1981e8c40f2fe0797d034bd81a5e40f2ee07975034b981a5c4092de0696b03cb381258c0d2b606957014a780a52c0528e0294303c9f8164f40d2760393903c9b8164d40d2660393103c9781a4ac0f24e0692303c3f8661f40f0ee078750243781219c0509e0284703c1f81e0f40f06e1983504c1784e09c0d03e07817026bf0135b8058fa02c790163a80adf8056fa02b7c015b700ad381d4fa09a790753a8269c40347a08a3900d1a8228c4172fa0697905cba81a5c40b27a0393902c9a80e4c42b0fc1587c014270520f82f04c17816026bf8135f809afa04d6f026b7013588058fe02c7d0163d81f1e8058f3374780163b80b1d8058ea02c740163780b1ac0f8d402c670163300b18c058b60cc5a0162b80b158056fe02b7e015be80adf0056de02b6e015b380ad8c056c404b5b025ad00ad5c056ac02b4f015a701ed34274fe15a7d03d3d8269e40f4ee18a7504d398269c4094de07a6b03d3381298c134b60ca570152780a92c0548e02a430a51f8068f41347608a390ad1b8068d41346608a3103cbf8365f40d2f60697903cbb8365d40d2e606971024b781a5ac0f2ce04963034ad81a55c0529e0294b014a380a50c2927e0593d0349d80e4e42b26e059350349980e4c41325e0692b5a89381a48c2b0fe1587d03c3bd181d4090de048670142780a11c2907e1583d0ac1bd500d41305e620270340f8cc05c058de02c6b0163380adbc056dc02b4f015a70129bc094d604a670253180a93c0549602a470152183a8fc0347a09a3b0451c83a8dc0346a09a33045188125bc092d604967024b180a53c0529602947014a182e4fc0b27a0693b01c9c82e4dc0b26a0693301c988264bc0d2560b9270349180a1381b07c1782606c0b0135bc05ace02c6f016358431a8058ce02c660163180b16c1f8b402c570162b00adbc056dc02b67015b180ad88096b604b5a015ab80ad580569e02b4e9b9a68129bc134d609a670253182696c1f4ae02a4f0152580a91c054860da3f00d1e8268ec1147218a3700d1a8268cc114620496f034b583659c092c60695b034ab80a53c0529602947014a18364fc0b27a0693b01c9c8364dc0b26a0693301c988264bc0d2560d927034918121bc090ce0284f014238360fce007a24837a901a8260bc3104e0681f06c0b8079fc11cfc01e7d0473e0075ac09ad201d6700eb1807584098fe04c7e0263e8071bc038da01c670263281317c098bc04c52015bf80adf40f6f613b79015bb80add4276e615b7100db7806db4036d613b6900db380ad94036c601b61015af81ed6c056ae04b53065a580ad1c034f607a7a00d3c8269e0034ee01a7600d3a8069d0034e601a7100d33806998034ca01a5f00d2d81e968034ae01a5600d2980692c1349401a4700d230068fc0347c01a3b00d1b8068cc134640797f0acbe81a5ec0d2f20797709cba81a5cc0d2e20196f00cb68065ac072d20196702cb280658c032c20495f034ad81e55c092a60694b034a38664fc0527602937034998064bc032560192700c9183a1fc1d0fa078770743a8061bc030da018670743281217c090ae0e83f0141b8060bc0304e0681f0740b8135f809afa04d6e026b100b1f40f8f402c7903e3c00b1d8058ea02c740163881f1a8058cc07c5a0162b00adf8056fa02b7c03dbd01ede40f6f002b76015ba80add0056e402b71015b800adb80f6d402b66015b101ed68056ac01b4e00da68069f8034fa01a7c00d3c8069d40f4e401a7104d380069340348a01a3d00d1c8068d4034620797d034bc81e5d40d2e202949034a08164f4072720593501c9883a1f40f0ea0e83d0741a8079fc03cfc07e7d0473e0075fc03afc07d7d8f2be0071fc038fc07c7d04e3e0131bc098dc04c6d0262f813178098a401b7f015be806dec036f201b7700dba806dce9e6e202b6f015b681edac0f6d202b67015b281ed8c316c202b5f03dad80ad5c096a607b4b015a38069fc034fc01a7d00d378069b8034da01a6c00d358069a4034c607a6200d30826980034be01a5b00d2b80694c0349601a4700d1f8068ec0346e01a3300cbf8165f4032f60197900cbb8065d4032e60397103cb781e5b40d2d60696903cb381e5940d2c606961024af81a56c0f2ae04953034a581a51c0f27e0293b0149b81a4cc0325e0192b00c9380648c030fe0e87d00c3b8061d40f0de0e86d03c3381e194090be048570741f80a0dc0305e018270340f81e05c07cfe03e7e01f3e80f9f007ad603d6902eb381358c09ac204c7f0263f0131f4098de04c6d02e33813194098be04c5e0262900adfc056fa07b7b03dbc80addc056ea07b7306db880adbc056da05b6b03db480ad9c056ca05b6302db080ad7c0f6b602b57025a981ad2c0568e07a7f0ad3e81e9ec0f4f207a7703d3a81e9cc134e205a6f00d368169ac0f4d205a6700d3281698c0b4c204a5f03d2d81e95c094a606a4b035238668fc0547602a3704d1980e5ec0d2f403979034bc0165dc0b2ec0597502cba00e5cc072e20596702cb3016594092be0395b034ad01655c0b2ac0395301ca581a5280b28e0594602c9f8164f8052760293701c9981a4c80b25e0392b02c9380e48c0f0fe0b87d03c3b81e1d40b0de0586d02c3381e194090be0485705c1f80a0dc1305e0b82701c0f81605c09afc04d7d026b7013588058fa07c7a0163c81f1e0058ec02c750163a00b1c40f8d402c660362d00b158056fc02b7d015be00ede8076f203b78015bb00add4056e802b72015b880adc0056dc06b6a015b300ad880d6b402b56015a7016d34274fa07a7903d3a8269c40549209a4100d1e8228e40346a08a3102cbf0165f40b2f803979014ba81a5c8072e20697002ca680a5140b27a029390149a80a4c4170fa0787505c1e82e0d407cfe03e7e01f3e80f9f00bafe05d7e036be81b5f00b8fe05c7e0363ec111f0098de04c6e0263681317c098bc04c52015bf80adf40b6f605b79015bb80add40b6e74c371015b780adb40f6d607b69015b380ad940f6c60db61015af81ed6c056ae04b53035a580ad1c0b4fe01a7d02d3d8169e40b4ee01a7502d398229c40f4de13a6d03d3581e9a40f4ce07a6503d31826984094be07a5b03d2b81294c0d49606a4709d1f80a8ec0546e09a3302cbf8165f80b2fa0596f02cb70165b40b2d80396b01cb480e58c0d2c403961034b001257c072b60595701ca980e52c0b28e0593f0149d80a4dc072660592f01c9581649c072460587f05c3e8161dc0b0ea0786f05c3681e19c0f0ca0485f0242b82e0fc0506e0982f05c1380e07c0b02e04c7e0262f00adfc056fa07b7b0cdbc80addc056ea15b730adb880adbc056da15b6b0cdb480ad9c056ca15b630adb080ad7c096b602b57025a983a9fc1d4fa07a7b04d3c81e9dc1d4ea09a7304d3883a9bc034da09a6b0453483a99c034ca09a630453081297c094b604a570252983a8fc0547602a3704d1981e5fc172fa0697b034bc81e5dc172ea06973034b882e5bc0b2da0696b01cb482e59c0b2ca0696301cb081257c092b604957024a982e4fc0527602937034998264bc0d2560b9270349181e1d8fe0e8078660242b0660f8058de02c6701631812d9c096cc02b4f015a7036d34094de04a6b0253381298c0549e02a4b0152380a90c1b47e01a3d04d1d8228e41b46e01a3504d198228c4092de0496b024b381258c0529e0294b014a380a50c1727e0593d0349d80e4e41726e059350349980e4c41325e0692b05c9381a48c056de02b6d0cdb5d24da4056ce02b650adb19c0d84056be04b5b015ab812d4c1d4de01a6d04d358229a41d4ce01a6504d31822984094be04a5b0252b81294c1d47e02a3b0151b8268cc172de0596d034b580e5a4172ce05965034b180e584092be0495b024ab81254c1727e0293b0149b81a4cc1325e0692b05c9381a48cfe0cc048563781f0135f809adc02c7d03e3d00b1e40f8f002c760163a80b1d0098d402c66015bf00adf4056f802b6e015a701ed341d4fa07a7903d3a8269c40549209a4100d1e8228e40346a08a3103cbe81a5e40f2ea06971014a481a5040b27a0393902c9a80e4c40f0fc1987c026bf00b1f4058f202c750263500b1980f6fc0ab7d055be00adb80569c07b4d00d3e81e9e4034ea08a7100d1e8228e40346a08a3102cbe80e5e40b2ea0397102c9e80e4e40b26a0393103c3f0131f8098f804c6e0262f00adfc056fa07b7b03dbc80addc056ea07b73a39b880adbc056da07b6b03db480ad9c056ca07b63a31b080ad7c096b602b57025a981e9fc034fa07a7b03d3c81e9dc034ea07a730453881e9bc1d4da07a6b03d3481e99c0f4ca07a6304d3081297c094b604a570252983a8fc0547602a3704d1981e5fc0b2fa0697b01cbc81e5dc0b2ea0697301cb881e5bc0f2da0696b034b481e59c0f2ca06963034b081257c092b604957024a981e4fc05276029370349981e4bc0d256079270349181e1f80f0dc7f06c026378131b8098da04c5f0262f013148056de02b6daa9b5cd4da4056ce02b65a99b1d44d84056be10b5b015ab812d4c1f69602b47a81378069b4134d608a69a7133806994134c608a610252f82696c134ae04a5304d25c7491e2247e02a3b0151b8268ce9a2de0596d034b580e5a6962ce05965034b180e584092be0695b818ab81254c0d296069476309f80a4ec0526e0693304c9781a4ad6624e06923a5037d201b68a0ce7e0650242f81215cdc07e0283704c1798009c0d03e31017025af812d6c056ae04b530252f81296c094ae04a5304d1f8268ec1346e09a33024af81256c092ae049530349f81a4ec0d26e069330349781a4ac0d24e06923015af812d6c056ae04b530252f81296c094ae04a530451f80a8ec0546e08a33024af81256c092ae049530349f80a4ec0526e069330349781a4ac0d24e0692300daf806d6c036ae01b530152f81296c054ae04a5300d1f8068ec0346e01a33024af81256c092ae0495300c9f8064ec0326e019330349780a4ac0524e06923015af812d6c056ae04b530252f81296c094ae04a5304d1f80a8ec0546e09a3301caf80e56c072ae0395301c9f80a4ec0526e0393301c9780e4ac0724e03923025af812d6c096ae04b530152f81296c054ae04a530151f8168ec0546e05a33024af81256c092ae0495302c9f8164ec0b26e0593304c9780a4ac0524e09923 18 262143 7 127 11 2047 21 2097151
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_63_10 (Nat.sub p 320)) (cc_63_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_63_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (cc_63_7 (Nat.sub p 224)) (cc_63_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_63_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (cc_63_4 (Nat.sub p 128)) (cc_63_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_63_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_63_1 (Nat.sub p 32)) (cc_63_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)
def f_63 : Nat → Nat × Nat := unpackForestF 0xc5fabc6600c5ba2b6baa035a2b63a9035a2b61a2a6fa7b71a2a67a296fa6371a2967a286fa4b69a286da3371a3361a286700c579eb489ea489ea449e9489e9449e8489e84400c5300b5b9d35600b539ac6a9b34d9b0359ab6a00b4b99b6600b4398c5500a5f9785d9625696a5a9602500a5b9434b94b649434300a579325600a539246600a4f9102500a4b903498b56a8f5688b4678e6788b36b8c36a8c3678c3668b3518b26a00a47898288982400a4388d6700a3f8785d8625686a5a8602500a33854550095f840150095b833597cc6d8246c7cc5780b5780b567cb617f57c7f3707cb4b7e5707ca477d57d7ca3f009577b0187b014009537646679c647626f78a547626b7626776a6476a54762630094f751646fb6f741346fb6b6fb67729346fb636fa667106d6f9667016a6f8150094b69b6b6e35469b6369a6f69a6b69a676ba5469a6369a3f6a25469a3300947689646436f679346436b64367661346436364a5d64a55641660094361d6761a676267a61a570093f5e3675fa555f86d5e1665e96a5e015009335d2560092f5c1660092b5b3485a4735a3704ed674ec6b4ec5b5745b572565724e4eb6a54c6b54a6a54a6654a4e4eb5a4f5674f26a52d7d4f2674f2664f25a5067a502764f2574f2564eb42009274c8184c8154c814009234ac554b1644a94b0085f0085b45b4b48174480144594b46174461644601445933008574402c44024008534246642a544226b0084f0084b3fb633fb613f86e3ad663ab6b3da643d8243aa6b3ba643ba543b8243aa333a866008473903c390340084337b703787c34d6736b5634b6a3536a3536634b5a0083f008333315b0082f0082b31b4830c7330b701d5671d46b1d45b2dc5b2da562da4e1d36a2b46b2b26a2b2662b24e1d35a25d6725a6a2957d25a6725a6625a5a26e7a26a7625a5725a561d3421d25a2394c238141d16b219762194c218141d15b1f4501f1761f14c1f0141d1431db6b1da6a1d05600827008231bb6b0081f0081b1a248194731927001d6701c6b01c5b16366162381603401b6b14a381483401b5b12b6612a381283401b4310c5b109561094e01a6a0e46b0e16a0e1660e14e01a5a08567083410816a0bd7d08167081660815a0967a09176081570815601a420196a0634b0614a01866025670246b0245b0236a0225a0215a0206a0183600817008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV4 fullMask g_63 ep_63 345 bds_63 (dagTraceF fullMask rootStock 11 f_63) (cur_63 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_9 : treeBlockF 288 320 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_10 : treeBlockF 320 345 (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) = true := by decide +kernel
theorem nj_63_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_63_1 h1 h2)
theorem nj_63_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_1 (fun _ h1 h2 => treeBlockF_at nb_63_2 h1 h2)
theorem nj_63_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_2 (fun _ h1 h2 => treeBlockF_at nb_63_3 h1 h2)
theorem nj_63_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_3 (fun _ h1 h2 => treeBlockF_at nb_63_4 h1 h2)
theorem nj_63_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_4 (fun _ h1 h2 => treeBlockF_at nb_63_5 h1 h2)
theorem nj_63_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_5 (fun _ h1 h2 => treeBlockF_at nb_63_6 h1 h2)
theorem nj_63_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_6 (fun _ h1 h2 => treeBlockF_at nb_63_7 h1 h2)
theorem nj_63_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_7 (fun _ h1 h2 => treeBlockF_at nb_63_8 h1 h2)
theorem nj_63_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_8 (fun _ h1 h2 => treeBlockF_at nb_63_9 h1 h2)
theorem nj_63_10 : ∀ i, 0 ≤ i → i < 345 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := block_join nj_63_9 (fun _ h1 h2 => treeBlockF_at nb_63_10 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 345 → (dagCheckNodeV4 fullMask g_63 ep_63 bds_63 345 (dagTraceF fullMask rootStock 11 f_63) cur_63) i = true := nj_63_10
theorem lb_63 : LowerBin fullMask rootStock g_63 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_63 kn_63 sub_63 gl_63 rc_63 nc_63

def wg : List Gate := [⟨GateOp.and, [3, 5]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241280 * 2 ^ 32 + 3902849152)) (13 - 1) := by
  rw [show canon fullMask (4008241280 * 2 ^ 32 + 3902849152) = g_63 by decide]
  exact lb_63

end PEqualNP.Outside.L_meta_49275

theorem PEqualNP.Outside.L_meta_49275 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241280 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49275.table2_from_lowerBin (4008241280 * 2 ^ 32 + 3902849152) 13 PEqualNP.Outside.L_meta_49275.root_lb PEqualNP.Outside.L_meta_49275.wg 18 rfl PEqualNP.Outside.L_meta_49275.wfits PEqualNP.Outside.L_meta_49275.weval
