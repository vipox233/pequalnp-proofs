import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49181

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

def m_0 : Nat := 0x3300000033000000
def s_0 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_0 : Nat := 0x100000013000000
def ep_0 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_1 : Nat := 0x5050505000000000
def s_1 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_1 : Nat := 0x10105000000000
def ep_1 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_2 : Nat := 0x3030303000000000
def s_2 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_2 : Nat := 0x10103000000000
def ep_2 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_3 : Nat := 0xf000f000000000
def s_3 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_3 : Nat := 0x10007000000000
def ep_3 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_7 : Nat := 0xf0f00000
def s_7 : List Nat := [0x50500000, 0x30300000, 0xf00000]
def g_7 : Nat := 0x10700000
def ep_7 : Nat := 0x600000000000000000000000000000102000000000000010400000
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

def m_8 : Nat := 0xff000000
def s_8 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_8 : Nat := 0x17000000
def ep_8 : Nat := 0x600000000000000120000000000000014000000
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

def m_9 : Nat := 0x2222222200000000
def s_9 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_9 : Nat := 0x2022200000000
def ep_9 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_10 : Nat := 0x4444444400000000
def s_10 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_10 : Nat := 0x4044400000000
def ep_10 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_11 : Nat := 0xa000a000a000a00
def s_11 : List Nat := [0x200020002000200, 0xa0000000a00, 0xa000a00]
def g_11 : Nat := 0x20002000a00
def ep_11 : Nat := 0x200080000000200000008000000000000000000000000000000000000000200020000000000000000000000
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

def m_12 : Nat := 0xc000c000c000c00
def s_12 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_12 : Nat := 0x40004000c00
def ep_12 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_13 : Nat := 0x3333000000000000
def s_13 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_13 : Nat := 0x113000000000000
def ep_13 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_14 : Nat := 0x5555000000000000
def s_14 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_14 : Nat := 0x115000000000000
def ep_14 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_15 : Nat := 0xff000000000000
def s_15 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_15 : Nat := 0x17000000000000
def ep_15 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_16 : Nat := 0xa000a000a000a0
def s_16 : List Nat := [0x20002000200020, 0xa0000000a0, 0xa000a0]
def g_16 : Nat := 0x20002000a0
def ep_16 : Nat := 0x20008000000020000000800000000000000000000000000000000000000020002000000000000000000000
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

def m_17 : Nat := 0xc000c000c000c0
def s_17 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_17 : Nat := 0x40004000c0
def ep_17 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_18 : Nat := 0xf0f000000000000
def s_18 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_18 : Nat := 0x107000000000000
def ep_18 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_19 : Nat := 0xf0000000f00000
def s_19 : List Nat := [0x50000000500000, 0x30000000300000, 0xf00000]
def g_19 : Nat := 0x10000000700000
def ep_19 : Nat := 0x60000000000000000000000000000000000000000000000000000000100000002000000010000000400000
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

def m_20 : Nat := 0x5500000055000000
def s_20 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_20 : Nat := 0x100000015000000
def ep_20 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_21 : Nat := 0xf0000000f000000
def s_21 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_21 : Nat := 0x100000007000000
def ep_21 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_22 : Nat := 0xf0f000000000
def s_22 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_22 : Nat := 0x107000000000
def ep_22 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_23 : Nat := 0xff0000000000
def s_23 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_23 : Nat := 0x170000000000
def ep_23 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_24 : Nat := 0x2222000022220000
def s_24 : List Nat := [0x202000002020000, 0x22000000220000, 0x22220000]
def g_24 : Nat := 0x2000002220000
def ep_24 : Nat := 0x220000000000000000000000002000000200000000200000200000000000000000000000000000000000000
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

def m_25 : Nat := 0x4444000044440000
def s_25 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_25 : Nat := 0x4000004440000
def ep_25 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_26 : Nat := 0x5050000050500000
def s_26 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_26 : Nat := 0x10000010500000
def ep_26 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_27 : Nat := 0x3030000030300000
def s_27 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_27 : Nat := 0x10000010300000
def ep_27 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_27 : KnownBin bds_27 := by intro b hb; simp [bds_27] at hb
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp [bds_27] at hb
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_27] at hb
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_27 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 1 bds_27 (dagTraceF m_27 s_27 3 f_27) (cur_27 0) s_27 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 1 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 1 (dagTraceF m_27 s_27 3 f_27) cur_27) = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 1 (dagTraceF m_27 s_27 3 f_27) cur_27) i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xffff00
def s_28 : List Nat := [0x555500, 0x333300, 0xf0f00, 0xff00]
def g_28 : Nat := 0x771f00
def ep_28 : Nat := 0xe0000000000002210000000000000441000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf01e0391f20e03b87706c1d81b0350ea0d4179ae0dc0b43682c0ce59c128a504a08c518230460844d981d001 0x3c4f0e93026060912c04480c0242a0d0b93a2c4d8a12a26498901e04074292c080601818044a0784c1c110683c180d0382408070383406070203406090503d120d4402d0c094281e040766a3f988ee5a37868ce113f824ee0137764cdd12f724adc1276648d703f560ed40374e0cd102f3e0ace0273608cd01f3206c88192005c581302044000f 11 2047 5 31 10 1023 18 262143
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xd8d8d8bcb8b8b8b8b8b8b89c989898987c78715b585843404040404024201903 0x7e4f3e269e818f00a6e5336289a818d00a648e314698138bc9a300617251683cb01a545329280b01899264a91242511924540c284a210990044 8 255 3 7 10 1023 17 131071
def cc_28_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x14284974e1c3160a54050000000 0x948c241248c0a242348c8d25344924a239248a0a22024 7 127 3 7 10 1023 18 262143
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_28_2 (Nat.sub p 64)) (cc_28_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xc7e063b031bc4d12225122348892468d2205110240319814fc0a760537789e3c4d1e030f0140299814bc0a56052768a634511a030d0140291af8e17c68bd385e9a010fd6078b034021da95314a8004370219a39311c888d284692010bd0098804402159d4f0ea60042702118107c08366024249d124d8a868492a2493120780832041718260c110607830340209820f4106a082d0e1a02094103c0c340612020740822000f 7 10
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 78 bds_28 (dagTraceF m_28 s_28 5 f_28) (cur_28 0) s_28 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 78 (dagTraceF m_28 s_28 5 f_28) cur_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 64 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 78 (dagTraceF m_28 s_28 5 f_28) cur_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_2 : treeBlockF 64 78 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 78 (dagTraceF m_28 s_28 5 f_28) cur_28) = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 78 (dagTraceF m_28 s_28 5 f_28) cur_28) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nj_28_2 : ∀ i, 0 ≤ i → i < 78 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 78 (dagTraceF m_28 s_28 5 f_28) cur_28) i = true := block_join nj_28_1 (fun _ h1 h2 => treeBlockF_at nb_28_2 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 78 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 78 (dagTraceF m_28 s_28 5 f_28) cur_28) i = true := nj_28_2
theorem lb_28 : LowerBin m_28 s_28 g_28 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xff00ff0000000000
def s_29 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_29 : Nat := 0x100170000000000
def ep_29 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_23, s_23, 4, g_23), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_23
  · exact lb_4
  · exact lb_5
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_30 : Nat := 0xffff000000000000
def s_30 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_30 : Nat := 0x117000000000000
def ep_30 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18), (m_15, s_15, 4, g_15), (m_14, s_14, 4, g_14), (m_13, s_13, 4, g_13)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_15
  · exact lb_14
  · exact lb_13
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_31 : Nat := 0xffff00000000
def s_31 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_31 : Nat := 0x177700000000
def ep_31 : Nat := 0x6000000000000006000000000000001222000000000000144400000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_22
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
def g_32 : Nat := 0x17007700000000
def ep_32 : Nat := 0x60000000000000000000000000000600000000000000120022000000000014004400000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xf0f0f0f000000000
def s_33 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_33 : Nat := 0x10107000000000
def ep_33 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_22, s_22, 4, g_22), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_22
  · exact lb_1
  · exact lb_2
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

def m_34 : Nat := 0xcccccccc00000000
def s_34 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_34 : Nat := 0x4044400000000
def ep_34 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0x3333333300000000
def s_35 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_35 : Nat := 0x113133300000000
def ep_35 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_13, s_13, 4, g_13), (m_2, s_2, 4, g_2), (m_9, s_9, 4, g_9)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_13
  · exact lb_2
  · exact lb_9
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
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

def m_36 : Nat := 0xaa00aa00aa00aa
def s_36 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_36 : Nat := 0x20022002200aa
def ep_36 : Nat := 0x20008800000020000000880000000000000000000200000000000000020022002200000000000000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
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
def g_37 : Nat := 0x2022200000000
def ep_37 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0x5555555500000000
def s_38 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_38 : Nat := 0x115155500000000
def ep_38 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_14, s_14, 4, g_14), (m_1, s_1, 4, g_1), (m_10, s_10, 4, g_10)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_14
  · exact lb_1
  · exact lb_10
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_38_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_38_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_38 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_38_1 (Nat.sub p 32)) (cc_38_0 p) (Nat.blt p 32)
def f_38 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_39 : Nat := 0xc0c0c0c0c0c0c0c0
def s_39 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_39 : Nat := 0x40004000c0
def ep_39 : Nat := 0x400080000000400000008000000040004000c0000000000000000000000000000000000000004000400000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0x3333000033330000
def s_40 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_40 : Nat := 0x113000013330000
def ep_40 : Nat := 0x1220000000000000000000000012000000200000010200000200000000000000000000000110000010000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_13, s_13, 4, g_13), (m_27, s_27, 4, g_27), (m_24, s_24, 4, g_24)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_13
  · exact lb_27
  · exact lb_24
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
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

def m_41 : Nat := 0xaaaa0000aaaa0000
def s_41 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_41 : Nat := 0x2000002220000
def ep_41 : Nat := 0x220000000000000000000000002000000200000000200000200000000020000022200000000000000000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 4, g_24)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_24
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0x5555000055550000
def s_42 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_42 : Nat := 0x115000015550000
def ep_42 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_20, s_20, 4, g_20), (m_26, s_26, 4, g_26), (m_25, s_25, 4, g_25)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_20
  · exact lb_26
  · exact lb_25
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_42_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_42_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_42 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_42_1 (Nat.sub p 32)) (cc_42_0 p) (Nat.blt p 32)
def f_42 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 43 bds_42 (dagTraceF m_42 s_42 6 f_42) (cur_42 0) s_42 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 43 (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42) = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 43 (dagTraceF m_42 s_42 6 f_42) cur_42) i = true := nj_42_1
theorem lb_42 : LowerBin m_42 s_42 g_42 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf0f00000f0f0
def s_43 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_43 : Nat := 0x1070000010f0
def ep_43 : Nat := 0x80000000000000000000000060000000e0000000000000000000001020000010000000104000001000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_22
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xcccc0000cccc0000
def s_44 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_44 : Nat := 0x4000004440000
def ep_44 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 4, g_25)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_25
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xaa00aa00aa00aa00
def s_45 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_45 : Nat := 0x20002000a00
def ep_45 : Nat := 0x2000800000002000000080000000000000000000000020002000a0000000200020000000000000000000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xcc00cc00cc00cc00
def s_46 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_46 : Nat := 0x40004000c00
def ep_46 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xf000f000f000f00
def s_47 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_47 : Nat := 0x100070007000f00
def ep_47 : Nat := 0x600080000000600000008000000000000000000000000000000000001000200020000000100040004000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_21, s_21, 4, g_21), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_21
  · exact lb_12
  · exact lb_11
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_47_1 (Nat.sub p 32)) (cc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 43 bds_47 (dagTraceF m_47 s_47 6 f_47) (cur_47 0) s_47 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 43 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xcc00cc00cc00cc
def s_48 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_48 : Nat := 0x40044004400cc
def ep_48 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xffff0000
def s_49 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_49 : Nat := 0x17770000
def ep_49 : Nat := 0x600000000000000600000000000000122200000000000014440000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xff00ff00
def s_50 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_50 : Nat := 0x17001f00
def ep_50 : Nat := 0x80000000000000000000000000006000e0000000000120010000000000014001000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xa0a0a0a0a0a0a0a0
def s_51 : List Nat := [0x2020202020202020, 0xa000a000a000a0, 0xa0a00000a0a0, 0xa0a0a0a0]
def g_51 : Nat := 0x20002000a0
def ep_51 : Nat := 0x200080000000200000008000000020002000a0000000000000000000000020002000000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
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
def g_52 : Nat := 0x100000017000000
def ep_52 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21), (m_8, s_8, 4, g_8), (m_20, s_20, 4, g_20), (m_0, s_0, 4, g_0)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_8
  · exact lb_20
  · exact lb_0
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_52_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_52_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_52 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_52_1 (Nat.sub p 32)) (cc_52_0 p) (Nat.blt p 32)
def f_52 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 43 bds_52 (dagTraceF m_52 s_52 6 f_52) (cur_52 0) s_52 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : treeBlockF 0 32 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_1 : treeBlockF 32 43 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52) = true := by decide +kernel
theorem nj_52_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_52_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_52_1 h1 h2)
theorem nc_52 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52) i = true := nj_52_1
theorem lb_52 : LowerBin m_52 s_52 g_52 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xf000f000f000f0
def s_53 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_53 : Nat := 0x100070007000f0
def ep_53 : Nat := 0x60008000000060000000800000000000000000000000000000000000100020002000000010004000400000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_19, s_19, 4, g_19), (m_17, s_17, 4, g_17), (m_16, s_16, 4, g_16)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_19
  · exact lb_17
  · exact lb_16
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_53_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_53_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_53 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_53_1 (Nat.sub p 32)) (cc_53_0 p) (Nat.blt p 32)
def f_53 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 43 bds_53 (dagTraceF m_53 s_53 6 f_53) (cur_53 0) s_53 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 32 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 43 (dagTraceF m_53 s_53 6 f_53) cur_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_1 : treeBlockF 32 43 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 43 (dagTraceF m_53 s_53 6 f_53) cur_53) = true := by decide +kernel
theorem nj_53_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 43 (dagTraceF m_53 s_53 6 f_53) cur_53) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_53_1 h1 h2)
theorem nc_53 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 43 (dagTraceF m_53 s_53 6 f_53) cur_53) i = true := nj_53_1
theorem lb_53 : LowerBin m_53 s_53 g_53 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xf0f00000f0f00000
def s_54 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_54 : Nat := 0x10000010700000
def ep_54 : Nat := 0x1060000000000000000000000010000000600000000000000000000000100000102000000010000010400000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19), (m_7, s_7, 4, g_7), (m_26, s_26, 4, g_26), (m_27, s_27, 4, g_27)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_7
  · exact lb_26
  · exact lb_27
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_54_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_54_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_54 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_54_1 (Nat.sub p 32)) (cc_54_0 p) (Nat.blt p 32)
def f_54 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 43 bds_54 (dagTraceF m_54 s_54 6 f_54) (cur_54 0) s_54 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 32 (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 43 (dagTraceF m_54 s_54 6 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_1 : treeBlockF 32 43 (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 43 (dagTraceF m_54 s_54 6 f_54) cur_54) = true := by decide +kernel
theorem nj_54_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 43 (dagTraceF m_54 s_54 6 f_54) cur_54) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_54_1 h1 h2)
theorem nc_54 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 43 (dagTraceF m_54 s_54 6 f_54) cur_54) i = true := nj_54_1
theorem lb_54 : LowerBin m_54 s_54 g_54 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xf0f00000f0f0000
def s_55 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_55 : Nat := 0x107000007070000
def ep_55 : Nat := 0x600000000000000000000000006000000000000000000000000000001020000020200000104000004040000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0x4444444444444444
def s_56 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_56 : Nat := 0x4044404440444
def ep_56 : Nat := 0x440000000000440000000000004004000400040000404000400040000000000000000000000000000000000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 0 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) s_56 4 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_56 g_56 ep_56 bds_56 0 (dagTraceF m_56 s_56 4 f_56) cur_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0x2222222222222222
def s_57 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_57 : Nat := 0x2022202220222
def ep_57 : Nat := 0x220000000000220000000000002002000200020000202000200020000000000000000000000000000000000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_57 g_57 ep_57 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0xa0a0a0a0a0a0a0a
def s_58 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_58 : Nat := 0x2020202020a0a
def ep_58 : Nat := 0x200080800000200000008080002000000000000000000000000000000020202020200000000000000000000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_58 g_58 ep_58 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xc0c0c0c0c0c0c0c
def s_59 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_59 : Nat := 0x4040404040c0c
def ep_59 : Nat := 0x400080800000400000008080004000000000000000000000000000000000000000000000004040404040000
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 0 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) s_59 4 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_59 g_59 ep_59 bds_59 0 (dagTraceF m_59 s_59 4 f_59) cur_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0xaaaaaaaaaaaaaaaa
def s_60 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_60 : Nat := 0x2022202220aaa
def ep_60 : Nat := 0x2200888000002200000088800020020002000a00002020002000a0000020222022200000000000000000000
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_41, s_41, 5, g_41), (m_37, s_37, 5, g_37), (m_57, s_57, 5, g_57), (m_45, s_45, 5, g_45), (m_36, s_36, 5, g_36), (m_51, s_51, 5, g_51), (m_58, s_58, 5, g_58), (m_24, s_24, 4, g_24), (m_9, s_9, 4, g_9)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_41
  · exact lb_37
  · exact lb_57
  · exact lb_45
  · exact lb_36
  · exact lb_51
  · exact lb_58
  · exact lb_24
  · exact lb_9
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV4 0x851060001 0x1f2f165a2cacf949727364a6c8cb908f1f263a4c6c78c8aab0d2e18b4515860cb74f2e965d1d7a1a64f2c96591cf21a63f3c7698dcf19bd4f2a8eb4fda9b9d2f4a4f113c62594471886b0fc61db437186670bc615a4271846306c40b801f 12 4095 6 63 10 1023 15 32767
def f_60 : Nat → Nat × Nat := unpackForestF 0xddf 1 5
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 2 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) s_60 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 2 (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 2 (dagTraceF m_60 s_60 7 f_60) cur_60) = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 2 → (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 2 (dagTraceF m_60 s_60 7 f_60) cur_60) i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0x5555555555555555
def s_61 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_61 : Nat := 0x115155515551555
def ep_61 : Nat := 0x1440000000001440000000000014004000400040010404000400040001101000100010000000000000000000
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_42, s_42, 7, g_42)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_42
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV4 m_61 g_61 ep_61 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_61 g_61 ep_61 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_61 kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0x3333333333333333
def s_62 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_62 : Nat := 0x113133313331333
def ep_62 : Nat := 0x1220000000001220000000000012002000200020010202000200020000000000000000000110100010001000
theorem epk_62 : ep_62 = edgePack m_62 g_62 := by decide +kernel
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40)]
theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_40
theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV4 m_62 g_62 ep_62 0 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) s_62 7 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_62 g_62 ep_62 bds_62 0 (dagTraceF m_62 s_62 7 f_62) cur_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_62 kn_62 sub_62 gl_62 rc_62 nc_62

def m_63 : Nat := 0xcccccccccccccccc
def s_63 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_63 : Nat := 0x4044404440ccc
def ep_63 : Nat := 0x4400888000004400000088800040040004000c00004040004000c0000000000000000000004044404440000
theorem epk_63 : ep_63 = edgePack m_63 g_63 := by decide +kernel
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_44, s_44, 5, g_44), (m_34, s_34, 5, g_34), (m_56, s_56, 5, g_56), (m_46, s_46, 5, g_46), (m_48, s_48, 5, g_48), (m_39, s_39, 5, g_39), (m_59, s_59, 5, g_59), (m_10, s_10, 4, g_10), (m_25, s_25, 4, g_25)]
theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_44
  · exact lb_34
  · exact lb_56
  · exact lb_46
  · exact lb_48
  · exact lb_39
  · exact lb_59
  · exact lb_10
  · exact lb_25
theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV4 0x851060001 0x1f2f165a2cacf949727364a6c8cb908f1f263a4c6c78c8aab0d2e18b4515860cb74f2e965d1d7a1a64f2c96591cf21a63f3c7698dcf19c54f2a8eb4fda9b9d2f4a4ef13c62594471886b0fc61db437186670bc615a4271846306c40b801f 12 4095 6 63 10 1023 15 32767
def f_63 : Nat → Nat × Nat := unpackForestF 0xddf 1 5
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV4 m_63 g_63 ep_63 2 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 2 (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 2 (dagTraceF m_63 s_63 7 f_63) cur_63) = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 2 → (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 2 (dagTraceF m_63 s_63 7 f_63) cur_63) i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_63 kn_63 sub_63 gl_63 rc_63 nc_63

def m_64 : Nat := 0xff00ff00ff00ff
def s_64 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_64 : Nat := 0x170077007700ff
def ep_64 : Nat := 0x60008800000060000000880000000000000000000600000000000000120022002200000014004400440000
theorem epk_64 : ep_64 = edgePack m_64 g_64 := by decide +kernel
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_53, s_53, 7, g_53)]
theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_53
theorem sub_64 : ∀ b ∈ bds_64, m_64 &&& b.1 = b.1 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV4 m_64 g_64 ep_64 0 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) s_64 7 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_64 g_64 ep_64 bds_64 0 (dagTraceF m_64 s_64 7 f_64) cur_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_64 kn_64 sub_64 gl_64 rc_64 nc_64

def m_65 : Nat := 0xf0f0f0f0f0f0f0f
def s_65 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_65 : Nat := 0x107070707070f0f
def ep_65 : Nat := 0x600080800000600000008080006000000000000000000000000000001020202020200000104040404040000
theorem epk_65 : ep_65 = edgePack m_65 g_65 := by decide +kernel
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 7, g_47)]
theorem kn_65 : KnownBin bds_65 := by
  intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_47
theorem sub_65 : ∀ b ∈ bds_65, m_65 &&& b.1 = b.1 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_65 : ∀ b ∈ bds_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV4 m_65 g_65 ep_65 0 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) s_65 7 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_65 g_65 ep_65 bds_65 0 (dagTraceF m_65 s_65 7 f_65) cur_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_65 kn_65 sub_65 gl_65 rc_65 nc_65

def m_66 : Nat := 0xffffffff
def s_66 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_66 : Nat := 0x17771fff
def ep_66 : Nat := 0x88800000000006000e00000000006000e0000000000122210000000000014441000
theorem epk_66 : ep_66 = edgePack m_66 g_66 := by decide +kernel
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 6, g_28)]
theorem kn_66 : KnownBin bds_66 := by
  intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_28
theorem sub_66 : ∀ b ∈ bds_66, m_66 &&& b.1 = b.1 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_66 : ∀ b ∈ bds_66, canon b.1 g_66 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_66 : Nat → List (Nat × Nat) := fun _ => []
def f_66 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV4 m_66 g_66 ep_66 0 bds_66 (dagTraceF m_66 s_66 5 f_66) (cur_66 0) s_66 5 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_66 g_66 ep_66 bds_66 0 (dagTraceF m_66 s_66 5 f_66) cur_66 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_66 : LowerBin m_66 s_66 g_66 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_66 kn_66 sub_66 gl_66 rc_66 nc_66

def g_67 : Nat := 0x117177717771fff
def ep_67 : Nat := 0x16600888000016600000088800160060006000e00106060006000e0001121222122210000114144414441000
theorem epk_67 : ep_67 = edgePack fullMask g_67 := by decide +kernel
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33), (m_30, s_30, 7, g_30), (m_64, s_64, 8, g_64), (m_62, s_62, 8, g_62), (m_63, s_63, 8, g_63), (m_29, s_29, 7, g_29), (m_61, s_61, 8, g_61), (m_60, s_60, 8, g_60), (m_42, s_42, 7, g_42), (m_40, s_40, 7, g_40), (m_65, s_65, 8, g_65), (m_47, s_47, 7, g_47), (m_35, s_35, 7, g_35), (m_43, s_43, 5, g_43), (m_52, s_52, 7, g_52), (m_38, s_38, 7, g_38), (m_66, s_66, 6, g_66), (m_53, s_53, 7, g_53), (m_54, s_54, 7, g_54), (m_32, s_32, 5, g_32), (m_55, s_55, 5, g_55), (m_49, s_49, 5, g_49), (m_50, s_50, 5, g_50), (m_31, s_31, 5, g_31), (m_15, s_15, 4, g_15), (m_34, s_34, 5, g_34), (m_28, s_28, 6, g_28), (m_44, s_44, 5, g_44), (m_48, s_48, 5, g_48), (m_37, s_37, 5, g_37), (m_41, s_41, 5, g_41)]
theorem kn_67 : KnownBin bds_67 := by
  intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_33
  · exact lb_30
  · exact lb_64
  · exact lb_62
  · exact lb_63
  · exact lb_29
  · exact lb_61
  · exact lb_60
  · exact lb_42
  · exact lb_40
  · exact lb_65
  · exact lb_47
  · exact lb_35
  · exact lb_43
  · exact lb_52
  · exact lb_38
  · exact lb_66
  · exact lb_53
  · exact lb_54
  · exact lb_32
  · exact lb_55
  · exact lb_49
  · exact lb_50
  · exact lb_31
  · exact lb_15
  · exact lb_34
  · exact lb_28
  · exact lb_44
  · exact lb_48
  · exact lb_37
  · exact lb_41
theorem sub_67 : ∀ b ∈ bds_67, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_67 : ∀ b ∈ bds_67, canon b.1 g_67 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x7a85871e8a6f12d6c62b68046618685eb2d5c02b57a46512684c84a47c4c4265639d893534a3074c2b1562288921e0a2011d1f9081cc2d1c309193301870c13b4c0ca710795105e1b03d210013c00001 0x1eb78135ac07ace01d6301e3780719c038c604c5f00e2b80714c0f6de06b67025af80ed5c2169e10b4703d378169ac0d4ce05a630252f80e96c074ae04a530852781692c2148e05a4302d1d85a8dc032de0796e00cb580659c032c60196200caf812578032b60195700ca98065480329e0494e00ca58065240328e0194300ca1006504032800193b00c9d0064dc1526c0192f00c958064a80324e0292600c918061bc030d60186a00c3381a198030c60185f00c2d806168030ae0385600c2980613c2109c0184b00c2480611c030860184200c20806100030760183700c178060ac0304e0182301f3f80f9f409cf604e7a01f3b81b9d807cea08e7401ebf80f5f807afa04d6f026b70135b40f8fe06c770263780f19c098be04c5d0262b82b1540f6fe05b7b035bb816dcc096de03b6b01db3812d8c096be02b5d025ad816d64096ae02b55025a9812d440b6960b34700d3f81e9f8034f601a7a00d3b81a9d8034e601a7200d378129b8034d601a6a00d3380e998034c601a6200d2f812978034ba04a5c00d2d806968034b201a5800d2b812958034aa2025400d29806948034a201a5000d258069280348e0aa4600d1f8168f80347601a3a00d1b80a8d80346601a3200cbf8065ec032f401977034bb0065cc032de0196b00cb500659c072cc0196300caf806574032b60195a00cac806560032ae0495600caa87c550032a60195100ca580651c0327e0193b00c9b8064cc030fe0187a00c3b81a1d8030de0186a00c3380e198030be0185d00c2d00615c090ac018550f02a0060fc0306e0182f00c170060b40303e0181e00c0902204003ad601d6a03e3781b1ac0d8ce07c6304e2f80f1741b8b604c5904e2b80f1541b8a604c5103d378169ac0d4ce05a6305d2f80a9740b4b605a5905d2b80a9540b4a605a5105d2781692c1348e05a4300cb78065ac032c60195f06caf0065740329e0194b00ca380650c0325e0192b00c9380648c1b0bc01d6b00eb501f1bc0d8d606c6703e3182717c078ba0dc5b04e2b80f1541b8a607a6f02d3581a99c0b4c60ba5f02d2d82e95c0b4a60ba4f02d2582691c0b4860196f03cb70065ac032c60196200caf81e5780329e0194b00ca380650c0325e0192b00c9380648c0d0cc0d85e04c230060780f8de06c6b0363381f18c138be03c5d0862d82715c078aa10c5303d378169ac0d4ce05a6305d2f81696c174ae05a5305d2781692c1348e05a4300cb781e5b8032d60196700cb1806588032be0795e00cad806564032ae0195300ca9006544032a00194f00ca580651c032860192f00c9580649c032460186f00c358061a8030ce0686600c3180617c210bc0185b00c2c80615c030a60185200c288061400309e0184b00c2500611c1908c0184300c178060ac0304e0182303ebf81b5ec0daee07d7303eb780f5b40fad604d6903eb380f5940fac604d610363b01b1980f6fe05b7b035bb816dcc0f6de02b6d02db5816da40f6ce02b6502db1816d84176be05b5b04dab816d4c034fe07a7e00d3d8069e8034ee06a7600d398069c8034de07a6e00d3681e9b0034d601a6a00d348069a0034ce07a6600d32870990034c601a6200d30806980034be04a5e00d2d806968034ae03a5600d298069480347e05a3e00d1d8068e80346e02a3600d198068c8032fe0197b00cbd0065dc0d2ec0197300cb78065b4032d60196a00cb48065a0032ce0796600cb286c590032c60196100caf80656c032b401957064ab00654c0327e0193b00c9b8064cc0d0ec078660d0320261580305c0181e01eb78135ac07ace04d6306e3781f1b8118d606c6a0463381b1981b8c607c6200e2d807168174de05a6b0453381698c094be03a5b01d2b81294c1749e02a4d02d258169241748e02a4502d21816904032de0196b00cb380658c032be0195b00ca980653c1b29c0194d00c978064ac0324e0192306c2700f5bc09ad603d67026b18371bc118d606c6a0463381b1981b8c601c5b00e2d02e9bc0b4d608a6702d3181297c074b603a570252982e93c0b4960ba4702d218065bc032d60196700cb180657c092bc0195b00ca98065480329e0494e00c978064ac0324e019230443300e1581b09c0181e01eb78135ac07ace04d63086378231ac0d8d408c670363304318c174de05a6b0453381698c094be03a5b01d2b81294c1749e05a4b05d2381690c032de0196b00cb380658c032be0495e00cad80655c032a60195200ca7812538032960194900ca380650c032840194100ca00064bc032560192700c918061bc030d60186a00c3383e198030c60185f00c2d806168030ae0385600c2980613c2109c0184b00c2480611c030860184200c208061000305e0182b00c1380608c07cfe04e7b01f3b8139cc09afe07d7e026bd8135e809aee06d76026b98135c8078cc03c5605dbf816dec116ee05b73025b780edac076ce04b63025af80ad74096b605b59025ab80ad54096a604b5100d3f81e9f8034f601a7a00d3b81a9d8034e601a7200d378129b8034d601a6a00d3380e998034c601a6200d2f812978034ba04a5c00d2d806968034b201a5800d2b812958034aa1825400d29806948034a201a5000d1f8168f80347601a3a00d1b80a8d80346601a3200cbf8065ec032f40197707cbb0065cc032de0196b00cb500659c072cc0196300caf806574032b60195a00cac806560032ae0495600caa85c550032a60195100c9f8064ec0326e019330443b00e198090ac1605400c170060780bade05d6e00eb58075a803ace01d6600eb18075880f8de06c6b0363381f18c138be03c5d06e2d813164138ae03c5506e298131440f6de06b6705daf82ad74176ae0ab5505da7826d1c034de02a6b0153380a98c034be01a5d00d2d806964054ae02a5500d298069440549e02a4b0152380a90c0547602a3700cb78065ac032ce0196300caf836578032ba0194f00ca580651c032860193b00c9b8064bc032560192700c918061bc030ce0185f06c2f0061740309e0184700c1780609c0303e0181702eb78075ac03ad401d6700eb300758c0f8de06c6b0363381f18c138be03c5d06e2d82715c078aa0dc5303db781ad9c176be0bb5705da7826d1c034de02a6b0153380a98c034be01a5b0152b80694c0549e02a4b0152380a90c0547602a3700cb781e5b8032d60196700cb1806588032be0295e00cab80654c032a40194f00ca580651c032860193b00c9b8064bc032560192a00c9380a498032460186f00c3500619c0d0cc0185f06c2f00615c030a40184f00c2500611c1308c0182f00c1380607c0303c0181d02eb780759c03ac607c6f0363581b19c0f8c609c5f01e2e84316c138ae03c550862981edbc0d6ce0bb5f05dab82ed3c1368e01a6f0153580a99c054c601a5f00d2d80a95c0549e02a4b0152380a90c0547602a3700cb781e5b8032d60196700cb1806588032be0295e00cad806564032ae0195300ca9006544032a00194f00ca580651c032860193b00c9b8064bc032560192a00c9380a498032460186f00c358061a8030ce0686600c3180617c210bc0185b00c2c80615c030a60185200c288061400309e0184b00c2500611c1908c0184300c1d8060dc0305e0182b00c1380608c05cfe05e7e0173e81f5fc0daf606d7703eb980b5bc05ada02d6b026b480b59c07aca02d63016b081f1fc0d8ee02c6f0163680b19c158ca0bc5f04e2b80adec0b6f402b79015bb80add8056e602b71015b380ad98056ca02b5f015ad80ad5c056a602b4b015a38069fc0f4fc01a7b00d3d0069dc0d4ec01a7300d390069bc054dc01a6d015360069ac034d401a6900d3400699c054cc01a650a13200698c034c401a6100d3000697c094bc01a5b00d2d00695c074ac01a5300d2900692c0349401a47055230068fc0547c01a3b00d1d0068dc0546c01a3300d190065fc032f60197a00cbb81a5d8032e60196f00cb68065ac032d40196900cb400659c052cc01965098b200658c032c20195f00cad806568032ae0c95600ca980652c0328e0193f00c9d8064dc032660187f00c3d0061dc0d0ec0186f00c368061a8030ce0286600c32848190030be0185a00c2b8261580307e0183700c178060b80305a0181f00c0f0060480b02003d6f026b580f59c09ac60dc6f03e370231ac0d8d408c670363303718c0f8c404c5f0262f00716c038b401c5700e2b00714c038a40bb6f045b3812d7c076ae0bb4f055a682ed1c1568a02a6f0153580a99c054c601a5f0152d80a95c054a601a4f00d2680692c0349202a470152280690c0348202a3b0151b8065bc032d60196700cb180657c032b60195700ca980653c1b29c0194d00c9d8064dc0325e0192b00c9380648c030de0186700c2f80615c0309e0d84e00c268060bc0304e0181f00c0b80f5bc09ad603d67026b18371bc118d606c6a0463381b1981b8c604c5f00e2d807168038ae01c5600e2982edbc116ce04b5f01dab82ed3c1768e02a6f0153580a99c054c601a5f0152d80a95c054a601a4f00d2580a91c0348602a3b0151b8065bc032d60196700cb180657c092bc0195b00cab80654c032a40194f014a700651c032860194200c9d8064dc0325e0192b00c9500649c0524c0192300c378061a8030ce0886600c2f806168030ae0385600c278361380308e0184200c1780609c0303e0181e00c0e80f5bc09ad603d67026b18431bc118d606c6a0463381b198218c604c5f00e2b80714c176de08b67025af80ed5c1769e0bb470153780a9ac054ce02a6300d2f80a96c054ae02a5300d2780692c0548e02a3b0151b8065bc032d60196700cb180657c092bc0195b00cab80654c032a40194f014a700652c032920194700ca1806508032820194000c9d8064dc0325e0192b00c9500649c0524c0192300c378061ac030d40186707c3300618c030be0185b00c2d00615c070ac0185300c27842138030960184900c2380610c030840184100c200060ec0306e0182f00c1580609c0304603e7f0273d80f9dc09ce602d7f03ebf00b5ec05af402d77036bb00b5cc05ae402d6f026b700b5b4178fe08c770263780f19c058be02c5d0162b82b154056fe02b7b015bb80adcc056d603b6a015b480ad9c056cc02b63015b080ad5c056ac02b55015a580ad1c034fe07a7e00d3d8069e8034ee06a7600d398069c8034de04a6e00d358069a8034ce03a6600d31806988034be02a5e00d2e80a970034b601a5a00d2c806960034ae02a5600d2a840950034a601a5200d288069400349601a4a00d2382a9180347e02a3e00d1d8068e80346e02a3600d198068c8032fe0197b00cbd0065dc1f2ec0197300cb78065ac032d40196701cb300658c032be0195d00cad806568032b20195800cab80a558032aa0f15400ca9806544032960194700c9f8064ec0326e0193300c3f8061e8030ee0887600c378061a8030ce0386600c2f806174030b4018570142b0061541c0a80183f00c1b8060bc0305c0182d00c0f80607803024058100552a036930034900da4400d200168f0054680d94c00ca004213011f0806d8803ec000f5e009ae002d6c062b400b59009ac00ac6402db400ad90094d801a6806d32006980144b801a580152a0069401548805a3c0151a0065a01b2c80815c00ca805a1900c0b808e740262e037160318a804c50055aa016960054a809d6f046b582359c14ac60dc6f03e370231ac0d8d408c670363303718c0f8c40dc5f0262f02716c078b409c5701e2b03714c098a402a6f0153580a99c054c602a5f0152d80a95c054a601a4b00d248065bc032d60196700cb180657c032b60195700ca980651c1b28c0194500c9580649c032460d8460473a037160298a80ab5402d2c00a950092b8019500b42a0275bc11ad608d67042b18371bc118d606c6a0463381b1981b8c60dc5f04e2d80f168138ae03c5606e2980a9bc054d602a670153180a97c054b602a570152980692c032de0796e00cb580659c032c60196200caf812578032b60195700ca98065480328e0294600c958064a80324e0292600c91822198130ac0d84600c0f0239d0218b013c54055aa016960054a80495c00ca8006520030b00d85400c240275bc11ad608d67032b18431bc118d606c6a0463381b198218c610c5f04e2d80f168138ae03c560862980a9bc054d602a670153180a97c054b602a57015298065bc0f2dc0196b00cb380658c032c40195f024af00656c032ae0195300ca900653c032960194a00ca48065200328e0294600ca18065040325e0192b00c9500649c0524c0192300c378061ac030d40186707c3300618c030be0185b00c2d00615c190ac0185300c2780612c030940184900c2400611c2108c0184300c208060bc030560182700c118279fc11cf608e7705b3980b5fc05afc02d7b036bd00b5dc05aec02d7303eb900b5bc05adc02d6b01eb500b59c05acc02d63026b100b178056fe02b7b015bb80adcc056de02b6b015b380ad8c0569201a7f03d3f0069ec034f401a770353b0069cc034e401a6f025370069ac034d401a6701d3300698c034c401a5f0152f006974124b801a5b00d2d006964034b001a570152b006954054a801a5300d29006944034a001a45055220068fc0547c01a3d02d1e0068ec0347401a370151b0068d40546801a3300d190065fc032f60197a00cbb83e5d8032e60196f00cb58065a8032ce0c96600cb180657c052bc0195d038ae00656c032b20195700caa80654c032a40195100ca80065140327e0193d00c9d8064dc0326a019330443b026198050bc0505c00c1700607813ade08d6b046b387558c328de08c670aa2f82715c226de05b6b045b3816d8c1a6be05b5b04dab816d4c0b6960434700d3781e9b8034d601a6a00d3381a998034c601a6200d2f812978034b601a5a00d2b80e958034a601a5200d258069280348e0aa4600d1f8168f80347601a3a00d1b80a8d80346601a3200cb78065ac032d40196707cb300658c032be0195b00cad00655c192ac0195300ca580651c0327e0193b00c9b8064cc030de0186a00c33822198030be0185a00c2b8261580307e0183700c178060b80305a0181f00c0f0060480402008c5f0462d82315c118a605a5f02d2d81695c0b4a605a4f02d2581691c0b4860195f00cad80655c032a60194f00ca580651c032860192f00c9580649c032460685601c2300607811ade08d6b046b382358c0b6de05b6b02db3816d8c0b6be05b5b02dab816d4c034de01a6b00d3380698c034be01a5b00d2b80694c0347e01a3b00d1b8068cc0324c0212403c3701a198090bc0385602c1f00a0d80305d0445f81a2dc0915df88a6f735f7b1adbd4d5de86a6ef34f771a5bb4d1dd8686e725f7312db9495dc84a6df24f6f125b7491db8486d623f6811dae88dd4c4669e15f4e8ada5855d262a68b14f450a5a0c51d002867d13f3e09d9e04dcea2667212f388959b849cd62465f05f2f02d95c15ca80a64804f2382590011c7a0863a03f1c81d8cc0dc600662d02f1601589809c460462201f1080d80c05c020260003f 20 1048575 8 255 11 2047 21 2097151
def cc_67_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe7433c608b76166ab41d14439a8832391e1f28bb887678fab01f53f21a4e3143c62769149c5183900f4929d9103724063aaaa6a0d0fbd9a47b2b49450860950c108221789826888282500050 0x3c5f1316c3c571314c5a5f1696c5a571694c4a4f0e92c3a471290c195f0656c19570654c194f0652c19470650c192f064ac19270648c38460f5bc4d6b0f59c4d6316dbc5b6b16d9c5b6312d7c3b5b0ed5c4b53069bc1a6b0699c1a630697c1a5b0695c1a53068fc1a3b068dc1a330e558786e1a198485e160f82836060bbf02c0609be0240f5bc4d6b0f59c3c6f0f1b84c5f131787a6f169ac6a671698c4a5f0e96c3a571294d1a4f0a9345a4b169251a470a9145a43169051a351e5bc196b1a59c19631257c195b0e55c19534a53cd94d0652c19494a51cd9450650c1941164bc192b4649c19230f9fc3e7d139ec4e7a0f9dc6e760f9d4ce740f5fc3d7e0f5f44d6f135b84d6d13158ac541edf86b7612db83b6612d784b5c12d5bc3541e9fc5a7b1a9dc5a73129bc3a6b0e99c4a631297c2a5d1296c5a591295c2a551294c4a51469145a390a8d4797f065ec6977065cc496f065ac39670658c495f12574195b0656449573655419530654419394a4d4592f064ad19270648ccd6f3f5accd67ed58c7b6e1ad984b5e0ed591a6f169acfa671698d1a5f1696cca571694d1a45168e42a354a5bc196b3e59c19634a57c195b3255c1953064e52935164bc192b4649c1923335bccd6b3359ccd6316dbc5b6b16d9c5b6316d7c5b5b16d5c5b53069bc1a6b0699c1a630697c1a5b0695c1a53068fc1a3b068dc1a331e1b86866121783856160f82836060b818260f5f81d7a075d81d72135b81d6a075981d621f1f86c76131b83c662b178ac5c2b158ac540a9745a590a9545a51169242a452a8d4797e065c8496e06588495e0657419490652019452a510192a2e4983d6f135ac3d670f1bc4c5f1edb84b5e12d38aa4e1e5bc596b1a59c59631257c395b0e55c49532e53c594b2e51c59430a4d4a9251e1bc186b1a19c18631217c185b0e15c18534213c184b4211c18432a0d4581f0606cb8170604c3e7f0f9f44e7b139e83e771b9d83e75339d03d7f0f5f83d7d135bc4d6e135b47c7e1b1d84c6e0f1984c5e131704c562b1504b562ad507a7f169ec6a77169cc4a6f0e9ac3a671298c4a5f0a9744a5b169644a570a9544a53129445a490a914aa351e5fc197b1a5dc1973125bc196b0e59c19631257c495d0656c19591255f81550654c195106524a945164bc192b2e49c19231215b7054079fc1e7e079f47d7f1b5ec6d771f5cc7d6f0f5b47d6b135a47d670f5947d63135847c7e1b1d87c6e1f1b07c66231904c5e0f1587a7f169ec6a77169cc7a6f0a9b45a6b169a47a670a9945a6316984ba5f1696c9a571694c5a490a914aa35065ec197a065e419771a5d81973065c419671a59819650657c195b0655c1953065241945064bc192b0649c19230f9fc4e7b0f9dc4e73135fc7d7e135ec4d7a135dc6d76135cc4d72075bc1d6e075b47c7e1b1d84c6e0f1984c5e131704c5627150ba7f169ec8a77169cc4a6f0e9ac3a671298c4a5f0a9744a5b169644a570a9544a53129445a490a914aa35065fc197b065dc1973065ac196a065a419670e59819630658419570e5581955065241945064bc192b0649c1923335bcfd6b3359f65631f1b86c66131783c562e9bc5a6b2e99c5a632e97c5a5b2e95c5a53169242a452a8d7516f065acf9670658f415f0656cc9570654c19492a514592f064acb9270648ccc5f3316ccc573314c5a5f1696c5a571694c5a4f1692c5a471690c195f0656c19570654c194f0652c19470650c192f064ac19270648ccc5f3316ccc573314c2a5f0a96c2a570a94c2a4f0a92c2a470a90c195f0656c19570654c194f0652c19470650c192f064ac19270648ccd6f335accd673358c5b6f16dac5b6716d8c5b5f16d6c5b5716d4c1a6f069ac1a670698c1a5f0696c1a570694c1a3f068ec1a37068cc786e1a198485e0e158583ec80f02836c40d0182e060983d6f135ac3d671358c3c6f0f1b85c6b171a85c67171985c630f1884c5f131783c5b0f1683c570f1584c53131487b6f1ad9c4b5f0ed5cbb4f2ad34bb472ad142a6f169ac2a671698c2a5f0e96c2a571294c2a4f0a9342a470a9144a43168ec5a3a0a8dcba361e5bc196b1a59c19631257c195b0e55c19533a53cd94d0652c19493a51cd9450650c1941064ecb937164bc192b0a49c1923161bc58671217c38571213c284d0a11c2845120bc282a0a09c28260607c18170f9fc3e7d139ec4e7a0f9dc6e760f9d4ce740f5fc3d7e0f5f44d6f135b84d6d1f1fc6c77131bc3c671317c4c5d1315cac550adfc5b7b0addc5b730adbc3b6b0ad9c4b630ad7c2b5d12d6c4b5a16d645b580ad5c4b560ad542b5412d4c4b5116d2c5b4a0ad1cbb46169fc7a7e169ec5a7a169dc6a76169cc5a72129bc4a6e0e9ac3a6a0e99c3a661298c4a621297c4a5e129744a5c1296c4a5a169645a581295c4a5616956f2541294c4a52129444a501692c5a4a1691caa461e5fc197b1a5dc1973125bc196b0e59c19631257c495d0656c19591255ce9550654c19510652cb947164fc193b0a4dc1933164bc592d064ac19291649ce9250648c1921161fc5877121bc38671217c485d1215c58550a0e828370a0d828270a09828250607c1817335bcfd6b3359ee5632f1bcbc672f17cbc570adbc5b6b0ad9c5b630ad7c5b5b0ad5c5b5316d2c5b4a0ad1cbb46169bc7a6e169ac5a6a1699c6a661698c5a621697c4a5e1696c3a5a1695c3a561694c4a521692c5a4a1691caa463a5bc196b3a59c19633a57c195b3255c19530652cb947164fc193b0a4dc1933164bc592d064ac19291649ce9250648c1921161bc58671617c58570a0e828370a0d828270a09828250607c1817335bccd6b3359ccd630adbc2b6b0ad9c2b630ad7c2b5b0ad5c2b53069bc1a6b0699c1a630697c1a5b0695c1a53068fc1a3b068dc1a330a4f8786e1a198485e0e1582836060b818260f5f81d7a075d81d72135b81d6a075981d622b174ac550adf85b7a0add85b720adb83b6a0ad984b620ad782b5d0ad705b5a0ad645b580ad582b550ad505b520ad445b5016d282b460a9742a590a9542a51169282a461e5f81972125b8196212578195d06528b946064f4193a064e419380a4d819350a4d01931064a829260617418550a0f8183d0a0b818220607418150f5bc4d6b0f59c2d630f1bc5c671718c4c5f0f15c4c531edbc6b6712d7c3b572ed3cbb470a9bc2a6e0a9ac2a670a98c5a620a97c2a5e0a96c2a570a94c4a520a93c2a4e0a92c2a490a91c2a43129082a41129002a3b168e82a370a8d8296f0a5ac29670a58c295f0a56c29570a54c294f0a538294b0a52429470a50c59420a504293b164e829370a4d8786f061ac68670618c485f0616c38570614d084f0612d08470610c183b2e0dc282f160b4182b0a09c28250608c281f0606c28170604c3e7f0f9f44e7b139e83e771b9d83e75339d03d7f0f5f83d7d135bc4d6e135b47c7f1b1dc4c6f0f19c4c5f131744c572b1542b7f0adf82b7b16de82b770add82b7316dc82b6f0adb82b6b0eda82b670ad982b6312d882b5f0ad782b5d0ad702b5b12d682b5916d602b570ad582b550ad502b5312d482b5112d402b4b16d282b470ad182a7f0a9ec2a770a9cc2a6f0a9ac2a670a98c2a5f0a9742a5b129682a59169602a570a9582a550a9502a530a9442a4b169282a470a918797f065ec6977065cc496f065ac39670658c495f12574195b065644957ac554195306544194b2e51c293f164f4193b064e429370a4d41933064c4292f064ac29270648c587f161dc486f0e19c485f12174485a1215c485616156a0540a0fc283e160f4282f0a0b828220607c1817079fc1e7e079f47d7f1b5ec6d771f5cc7d6f0f5b47d6b135a47d670f5947d63135847c7f1b1dc7c6f1f1b47c6723194bc5f2715c2b7f0adf82b7b16de82b770add82b7316dc82b6f0adb82b6d0adb02b6b16da82b6916da02b670ad982b650ad902b6316d882b6116d802b5f0ad782b5b0ed682b570ad582b5312d482b4b16d282b470ad182a7f0a9ec2a770a9cc2a6f0a9b42a6b0a9a42a670a9942a630a9842a5f0a96c2a570a94c2a4b169282a470a918197b065e81979065dc6976065cc19710659c696606594195f0656c19570654c194b0651c193f064f4193b064e41937064d41933064c4192f064ac19270648c187f061dc186f061b4186706194185f0615c183f0a0f8183d060bc282e06088181f0605c3e7f139ec3e77139cc4d7f1f5f84d7b135e84d771b5d84d73135c81d6f075b81d6d2f1fc8c77131bc3c671317c4c5d1315c9c550adfc2b7e0adec5b7a0addc2b760adcc5b720adbc2b6e0adac3b6a0ad9c2b660ad8c4b620ad7c2b5e0ad742b5c0ad6c4b5a0ad645b580ad5c2b560ad542b540ad4c4b520ad444b500ad2c5b4a0ad1c2b460a9fc2a7b0a9dc2a730a9bc2a6b0a99c2a630a97c2a5d0a96c2a590a95c2a550a94c2a510a92c5a4a0a91c2a46065fc197b065dc1973065ac196a065a419670e59819630658419570e55819550652c1947064fc193d064ec1939064dc1935064cc1931064bc192b0649c1923061fc1877061bc18670617c185d0615c1855060fc283e060f4182f0a0b818220607c1817335bcfd6b3359e95632f1bcbc672f17cbc570adbc2b6e0adac5b6a0ad9c2b660ad8c5b620ad7c2b5e0ad6c3b5a0ad5c2b560ad4c4b520ad2c5b4a0ad1c2b460a9bc2a6b0a99c2a630a97c2a5b0a95c2a530a92c5a4a0a91c2a46a05bc196b3e59c19639c57c195b3255c19530652cb9470a4fc593d064ec19390a4dc2935064cc19310a4bc192b0a49c1923161bc58671617c58570a0fc283e160f4282f0a0b828220607c18173317ccc5b3315ccc530a97c5a5b0a95c5a530a93c5a4b0a91c5a430657c195b0655c19530653c194b0651c1943064bc192b0649c19233317ccc5b3315ccc530a97c5a5b0a95c5a530a93c5a4b0a91c5a430657c195b0655c19530653c194b0651c1943064bc192b0649c1923335bccd6b3359ccd630adbc5b6b0ad9c5b630ad7c5b5b0ad5c5b53069bc1a6b0699c1a630697c1a5b0695c1a53068fc1a3b068dc1a330a4d8786e1a198485e0e15a504c90110583e060b81826235bc8d6b2359c8d63231bc8c672717c9c5722dbc5b6b22d9c5b6326d7c5b5b26d5c5b5316d2ceb47069bc1a6b069a81a67229981a630697c1a5b069681a57269581a530692c1a47068fc1a3b068dc1a33065bc796e065ac196a0659c69660658c19620657c495e0656c195a0655c39560654c19520652c194a0651ca946064fc593e064ec193a064dc2936064cc1932061bc18670617c1857060fc1837060a81827060981817060581815275bc8d6b2359ccd6316dbc5b6b16d9c5b6316d7c5b5b16d5c5b53069bc1a6b0699c1a630697c1a5b0695c1a53068fc1a3b068dc1a33225989956064b8786e1a198485e0e158583e0a0d818260f5bc4d6b0f59c1d630f1bc3c6e071ac1c6a0719c1c660718c1c621317c4c5e0716c1c5a0715c1c560714c1c521edbc6b6712d7c3b5736d3cab4d36d1cab451e9bc5a6b1a99c5a631297c3a5b0e95c4a533693c2a4d1692c5a493691c2a451690c5a41168ecda37065bc196b0659c19630657c195b0655c19530653cd94e06534193b064dc192f064ac19270648c186f0619c185f0615c184f36138184d060bc18270607c18170f5bc4d6b0f59c1d630f1bc1c6b071a81c67071981c631317c1c5b071681c57071581c531edbc6b6712d7c3b5736d3cdb471e9bc5a6b1a99c5a631297c3a5b0e95c4a533693c5a4b3691c5a43168ecda37065bc796e065ac19670658c19620657c495e0656c19570654c19520653c494e0651c194306508193b064e819372a4d8192f064ac192a0649c29260648c186f061a818671a198185f0616818570e158184f36138184706108182f0609c181f06078181d 19 524287 8 255 11 2047 18 262143
def cc_67_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x899430dab203afbdfcf740fee26b5acf0334ca65130c706585912f7a7593b8abad9393ca5aaf472868238500879c4f932cba563ec9a641242121c5837b7c5ba7877ff0c25a0c580062500018 0x36b786d6b0dace1b58c2db785b6b0b6ce16d8c2daf85b5b0b6ae16d4c0d3781a6b034ce0698c0d2f81a5b034ae0694c0d1f81a3b0346e068cc34b7019260d0cc121781c2b0583e0506c060b80c1304d6f09adc131ac1e3384c63078ae0f154353785a6b0d4ce1698c5d2f82a5d0b4b6169645d2b82a550b4a616944252783a4b0748e1290c34b78196b0d2ce0658c44af8895d032b60656444ab88955032a60654424a78194b0728e0650c2c978192b1124e0648c440b03d7f07afa135ec26bc83d7707aea135cc26b883d6f09ad60f59c26b184c7f0d8fc131f6ea3e04c7b098f4131e4263c04c770d8ec131d4363a04c73098e4131c4263804c6f0d8dc131ac263504c670d8cc1318c263106b7e156f80ed581da306a7f054fa169ec2d3c86a77054ea169cc2d3886a6f0b4d61a99c2d3184a5f074b60e95c252984a4f0549a1292c2d2484a470548a1290c25208697f112fa065ec0cbc869770d2ea065cc0cb88696f032d61a59c0cb18495f032b60e55c0ca98494f0929a0652c0ca4849471128a0650c0ca08592f032562249c0c918687e0d0dc2205816b782d6e05ace0b58c16b103c6f098d60f19c263183c5f078ba1316c262c83c57078aa1314c262886b6f0d6ce2ed7c55ae8bb57156aa12d3c1da382a6f054d60a99c153182a5f054ba0a96c152c82a57054aa0a94c152882a4f054960a91c152182a3b0546e1a5bc0cb586967032c62257c44ae8195b032b22255c44aa81953032a21253c0ca58394703286064ec449b8292f032560a49c0c918586f050ce1617c2c2e82857050aa1213c1c238282f0504e0607c2c0d018171102c0f5fc1ebe84d7b09af20f5dc1eba84d7309ae20f5bc26b583d6709ac60b1fc363f02c7db68f80b1ec163d02c79058f00b1dc363b02c750d8e80b1cc163902c71058e00b1bc363702c6b058d40b19c363302c63058c40b17c262f02c5d0d6fe2adf435bb86b750d6de1ad9c25af83b570569e0ad3415a38ab45054fe0a9f8153e82a7c054f60a9e4153b82a75054e6169c8153885a70054de0a9ac153382a63054b60e968152c82a57054ac0a94c152882a470548c0a914151d82a370d2fe225f40cbd819790d2ee1a5d40cb9819710d2de065ac34b381963092be0656c1cab819530529e0a5340ca5819490528e225140ca18194103276224dc14978192b0524e0648c2c3f8687e0b0fa161bc343705862090be0e15c14278284d0508e161141417828270303e160680c0b888160dade1b5ac36b386d63056de0adb8edaf84b5e196b60ed6865ab83b563b6a612d48153782a6b054ce0a97c152d82a57054a60a8ec151c8696f032d61a59c0cb18895f032b62255c0ca98893f1127a064ec0c9c889371126a064cc0c988292f032560a49c0c918686e1102c1b5fc1ebe86d7b09af21b5dc1eba86d7309ae21b5bc36b586d670dac60b1fc163f02c7d058f80b1ec363d02c790d8f00b1dc163b02c75058e80b1cc363902c71b28e00b1bc163702c6b0d8d40b19c163302c630d8c40b17c162f02c5b078b40b15c162b02c53098a40ad38153f82a7d054f60a9e4153b82a75054e60a9c4153782a6b054ce0a98c152f82a5b054ae0a94c151c8697f112fa065ec0cbc869770d2ea065cc0cb88696f032d61a59c0cb18895f032b62255c0ca98294f1129a0652c0ca4829470528a0650c0ca0889350525e164b40c95829270524a0648c343f0686e1102c1b1bc1e3686c6b098d21b19c1e3286c63098c21b17c362d86c570d8a61adbc55b686b670d6ca1ad7c35abdc34f1968e1a9bc153685a6b0b4d21a99c153285a630b4c21a97c2d2d86a570b4a76893c2d258ca470b486168eec11b8696f112da065ac0cb4869670d2ca0658c0cb08695f032b61a55c0ca98894f032962251c0ca18193b1126e164bc0c9588927032461a1bc34370786d0d0be1a17834290c84f1908e160bc2c138181f110340605c440b07c5f0d8b61b15c3e2985a5f0b4b61695c2d2985a4f0b4961691c2d218195f032b60655c0ca98194f032960651c0ca18192f032560649c0c9187c5f0d8b61b15c3e2985a5f0b4b61695c2d2985a4f0b4961691c2d218195f032b60655c0ca98194f032960651c0ca18192f032560649c0c91868560fade1b5ac36b387d630b6de16dac2db385b630b6be16d6c2dab85b53034de069ac0d3381a63034be0696c0d2b81a530347e068ec0d1b81a330d2cc1e1b8242f038560b07c0a0d80c175602c0304d540900f3d03d6d09ad20f59426b087c7e098f41b1d826390cc6e098da331b0263504c69098d03319826328cc64098c413184263002a6d0b4d20a9942d3082a4d0b4920a91425208797e032e41e5b80cb68194d03292065140ca0838560708c0f5fc26bd83d7709ae60f5bc1eb684d6b09ad20f59c1eb284d6309ac2131fc3e3f04c7b098f4131dc363b04c73098e4131bc3e3704c6d0f8d8131ac263504c69098d01319c3e3304c65198c81318c263104c61098c01add835b307a7f0b4f61a9dc2d3987a6f054da169ac2d3487a67054ca1698c2d3084a5f074b60e95c252984a4f0549a1292c2d2484a470548a1290c25208797f032f61a5dc0cb98796f0f2da065ac0cb487967a62ca0658c0cb08495f032b60e55c0ca98494f0929a0652c0ca4849471928a0650c0ca08592f032562e49c0c91838560708c179f80f3d01e7603ce40f5b426b483d6509ac21f1f8263d06c76098e4331b826368cc6c098d4131a426340cc66098ca33190263104c61098c02adb455b284b4d1568a069b40d3482a65034c20a934152482a45054821e5f80cb90296e032da065340ca48194503282064a814930186d030ca061681c2b038460308a060740c0a82e7f0bcfc0b9f41ebf84d7b07aee135cc16b782d6d05ad6135a416b383d6505ac60b584263f87c7e098f6131e8263b86c76098e6131c8163782c6e058da0b1b0163582c6a098d2131a0163382c66098ca33190163182c62058c20b1803dbf86b77056de0adb415b38ab65096be0ed5c25a784b4d0968e2ad14153d85a7a054f20a9dc153b02a73054e20a99c153302a65054be0a96c152b82a530549e0a934152582a490548e0a914152182a41054760a8dc3cbf8197b0d2ee065cc14b78296d032d6065a414b3d1165032c60658424af8195b072ae0654c24a78494d032960652424a38c94503286065040c9d8b9370525e064ac1493819230b0fe161dc14378286d050ce161941c2d03857070ac0e11c1c23038450505e0a09c0c0f818170fafc135e836bb04d720f8fc1b1e8363b07c72098dc0f1a81e3304c62098bc13174262e04c5a198b233160262b0cc55198a813148262884c50054ba0a964152a82a51034925e5f80cb90496e032c4125780cae8495c032b2065540ca901951032a00a5180ca28192a0524c0e1981c2b03d6f09ad60f59c26b184c6f0f8dc131ac263384c63098c442dbc7db58fb67216c612d7c25ae83b5b076b40ed5c1dab0cb55056a60ad3c15a683b4b076940ad1c15a302b45056880ad0c14b78296b052ce0a58c14af8295b052ae0a54c14a78294d052960a51c14a2829432b0de061ac7c3381863090be0616c1c2b818530909e121340c25848471908a0610c841f8183b2106e060cc140f8181b0502e0604c1f3f84e7b07cee139cc26bf87d7e09af6135e826bb86d7609ae6135c8163f82c7e058f61b1e8163b82c76058e61f1c8163782c6e058d60f1a8163382c66058c613188162f82c5e058ba0b170162d84c5a058b233160162b82c56058aa0b150162984c52058a21314015a702a7f054f60a9dc153982a6f054d60a99c153182a5f054ba0a96c152c82a57054aa0a94c152882a39982fe065ec7cbb81973092de065ac1cb381963092be125740cad81959092ae325540ca9819510529f3c5340ca5819490528e0a5140ca1819411526a0a4bc2c968192b0524e0a4940c9183866070ac0a13a702607d7c09af0235d026b802c7c118f00b1d03e3802c5c198b00b15026281794c03280561300f3f81e7e03cfa0f5fc26bd83d7709ae60f5bc1eb684d6b09ad20f59c1eb284d6309ac2131fc3e3f04c7b098f4131dc363b04c73098e4131bc3e3704c6d0f8d8131ac263504c69098d01319c3e3304c65118c81318c263104c61098c01edfc35bb87b6f0f6da1ed9c45b284b5f076ae12d3c25a684b471568a1e9fc2d3d86a770b4e61e9bc153685a6b0b4d21e99c153285a630b4c21297c1d2d83a57094a61293c152684a4b0b4921291c152284a4309482168ee611b8197b032f4065e40cbb86976032e6065c40cb386966032ca0657c0cad81957032a60653c0ca68194b032920651c0ca28194303282064ec0c9b8192f032560649c0c918187f030ee061bc0c3681867030ca061680c2b838560308e0e1180c228182f0304e0607c0c0b83e7f09cf60f9dc273984d7f0fafc135ec26bd04d770daec135cc26b90ac7f0f8fc231ec363d08c770d8ec2b1cc3e3904c6f098dc0f1ac1e3503c67078cc1318c263104c5f098bc13174262e04c5b098b42b164662c04c57098ac2b154562a04c53098a413144262801b4e174fe169ec453b85a73094de0e9ac1d3384a63094be0a974252d85a59094ae0a954252984a511549e0a9342d2585a491548e0a9142d2185a411546a065fc0cbd81977032e6065bc0cb581967032c60657c0cae8195b032b20655c0caa81953032a2064e40c978192b0324e0648c1c330385607cfe139ec1f3b84e7309afe1f5f826bd84d7a09aee1b5d826b984d72178fe231dc263783c67098be13174262b8ac55056fe0adf815bd86b7a056ee0add815b987b72056de0adb815b583b6a056ce0ad9815b184b62056be0ad7815ae82b5c056b612d6815ac8cb58056ae0ad5815aa82b54056a612d4815a884b50056962ad2815a382b46054fe0a9ec153b82a73054de0a9ac153382a63054be0a974152d82a59054ae0a954152982a510549616928152382a460347e068f80d1e8197f032f6065dc0cb98196f032d60659c0cb18195f032ba0656c0cac81957032aa0654c0ca88194b0328e064fc149f0193d0325e0a4b80c958192903246064880c908187f030ee061a80c3383866030ae0e1580c2a8183f0307a060dc0c1a8182f0304e0607c0c0b83d6f09ad60f59c26b184c6f0f8dc131ac263504c670d8cc1318c26315236f1f6ce12d7c1dab84b4f0969a12d1c55a2d026f0b4d63e99c2d3184a5f074b60e95c252984a4f0549a1292c2d2484a470548a1290c252085a3b9a46f2c5bc0cb58f967032c61257c0cad83957032a61253c24a68194b032921251c64a28194303282064ee509b8592f032572449c0c918c86f190ce0e1681c2b838560708e0e1181c228582f0b04e0607c0c0b83d6f07ad60f59c1eb185b6f0b6d616d9c2db183b5f076b60ed5c1da981a6f034d60699c0d3181a5f034b60695c0d2981a3f03476068dc0d198395e0324c1e1b83433038560b07c0a0d80c170182607ade0f59c1eb183c67078cc0f17c1e2f07a6f0b4d61a99c2d3183a5f074b60e95c1d298ba4f0549a1692c2d248ba470548a1690c2d208796f032d61a59c0cb18395f032b60e55c0ca98994f1329a0652c0ca4899471328a0650c0ca08592f032562649c0c918981607afe0f5f81ebd86d7a07aee0f5d81eb987d7207ade0f5b81eb683d6c07ad61f5a81eb4c656807ace0f5981eb283d6407ac61f5881eb087d60078fe0f1ec1e3b83c73078de0f1b41e3583c69078ce0f1941e3183c610d6ec1ad981daf0ab5c0f4fe169ec353b85a730f4de0a9b42d3585a690f4ce0a9942d3185a61074be0a9741d2d83a59074ae0a9541d2985a510749e0e92c1d2383a430f2fe065ec34bb819730f2de1e5b40cb5819690f2ce265940cb181961072be265740cad81959072ae0e5540ca9819510729e0652c1ca3819430b25e064ac4c9381923070bc0e1384c0b03d6f07ad60f59c1eb183c6f078dc0f1ac1e3503c67078cc1718c2e3102c5f058bc0b15c162982c520f6de1ad9c1daf83b571769e2ad345da38ab45054de0a9ac153382a63054be0a96c152b82a530549e0a934152582a490548e0a914152182a41054760a8dc3cb78196b0d2ce0658c1caf8195b072ae0654c4ca78994d03296065244ca38994503286065040c9d899370525e064ac1493819230b0de1619c1c2f828570909e121341423828450505e0a09c0c0f8581a0302e26058173f85e7e05cfa0f5fc1ebf03d7b0daf40f5dc1ebb03d730fae40b5bc16b702d6d05ad80b5ac16b503d6988ad00b59c16b303d6507ac80b58c16b102d6105ac00f1fc1e3d83c77078e60b1bc163682c6b078d20b19c1e3282c63058c21edfc35bb82b6f056da0ad9c55b283b5f156ba0ed5c1daa83b4f0768e0a9ec2d3d02a79054ee0a9d8153982a71054ce0a998153282a5f054bc0a974152e02a5b054b20a95c152a82a53074a40a9442d2802a4f054960a91c152182a3b0546e1e5fc0cbd86977032e60a5bc14b68196b032d20a59c4cb281963032c20e57c4cae8195b032b20e55c1caa81953032a20e53c0ca58394703286064ec4c9b8292f032560a49c0c918587f0b0ee0a1bc1436828670b0ca0e17c1c2f0485d0709e0e1381c210282f0504e0607c2c0d018171302c0f5bc1eb583d6707ac666dbc3db70fb6b0d6d43ed9c35b319b630f6c40ad7c15af02a6f054d60a99c153182a5f054b60a95c151d82a39132de065ac4cb381963072be0656c1cab819531327e264f40c9d819391326e264d40c99819310525e064ac149381923070bc260581f3f83e7e07cf61b9e81f3b83e7607ce61f9c81ebf83d7b07aee0f5cc163f82c7e058f61b1e8163b82c76058e61f1c8163782c6e058da0b1b0163583c6a058d20f1a0163382c66058ca0b190163183c62058c309180162f82c5e058b60f168162b82c56058a60f14815a702a7f054f60a9dc153982a6f054da0a9ac153482a67054ca0a98c153082a5f054b60a95c152982a39132fe065ec4cbb81973072de265b40cb581969072ce0e5940cb181961072be0656c1cab819530529e265340ca5819490528e0a5140ca1819411326a0a4bc2c968192b0524e0a4940c918386e070bc260581eb783d6e07ad61b5a81eb383d6607ac61f5881e3783c6b078ce0f18e29b78fb67076be2ad741dab83b550769e0ed1e193785a6b1f4ce1698c1d2f82a5d074b60e9641d2b82a55074a6169441d2783a4b0748e0e90c2d1dc1237132de065ac4cb381963072be265740cad81959072ae0e5540ca9819510729e0652c1ca38194303276264dc2c978192b1324e0648c64378c867070be0e178242e8384f0709c0e1082c17858270303e260680c0b89816078be1316c1e2b84c530b4be1696c2d2b85a530949e0e92c1d2384a43032be0656c0cab819530329e0652c0ca3819430325e064ac0c9381923 19 524287 7 127 11 2047 19 524287
def cc_67_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x99e4197d21935488eb4a8bf2c83c837f24a7da187c11979f227336c6969d633635d26156c664cba146863450184123e3ad653862732a5c2f43627b7924c2f209431a8611990f120790c35d0487b00048 0xf9fc1f3e84e7b09cf40f9dc373b03e7511ce80f5fc1ebf03d7d09ade135b826b684c56158a81edf835bb04b6e076cc12d7825ae04b56fe6a81e9fc353d86a770f4e6129bc1d3583a67094c61297c152e84a5b0b4b21295c152a84a53094a2469142d1c82a350f2fe065ec34bb81973092de065ac1cb381963092be125740cad81959092ae225540ca98195103292224d444978192b1124e0648c4eb788d6b11acff958c3db706b66096bc0ed588d3788a6b114ce2e98c8d2f89a5b134ae2e94c8d2285a390546a225bc0cb588967032c62657c0cad89957032a606524549a8b92f032563a49c0c9188d6f11ad62359c46b188c6f118ce2717c4e2b88b6f116d622d9c45b189b5f136b626d5c4da98ab4b1568e069bc0d3581a67034c60697c0d2d81a57034a6069340d2381a450347e068ec0d1b81a33032de1e5b80cb58196a032ce1a5980cb181962032be125780cad8195a032ae0e5580ca9819520328e2a5180ca28193f0b27c064ec0c9d019370526c064cc0c990186f030ce0617c0c2b8183f0306e060bc0c138181f0303a0605c0c0a83d6f09ad60f59c26b183c6f038d61b19c3e3184c5f038b60f15c262987b6f0f6dc1adac35b387b630f6c412d7c25af03b5b076ae12d4c25a904b4f0969c12d1c25a184b420f4de1a99c252f83a571549e2a93825238da420347e068f80d1e8796f0d2d61a59c3cb18495f072b60e55c24a98b94f172962e51c5ca18a93f0527a2a4ec549b82935152662e4b454958a9271524a1e1bc34338485f070ae3613c6c238a83f2507a2a0dc541a8b81f1702e0f5f826b707c7e0d8f41b1d83e3904c6e078d40f19826310ac5e158ba2b170862d0ac59218b02b158562a8ac54258a42b144962801b4e054ba16964152a85a510549a16924152285a411546a065740cac81955032a2064e43c3f0486e090bc2a11854220b8260302c0f9fc1f3e84e7b09cf40f9dc373b03e7511ce80f5fc1ebf03d7d09ade135b826b687c7f0f8fc1b1ec363d06c770d8ec1f1cc3e3904c6f098dc0f1ac1e3503c67078cc1318c263104c5f098bc13174262e04c5b098b42b164962c04c57098ac2b154562a04c53098a413144262807b7f0d6ee12dbc1db384b5f096ba12d6825ab84b56156aa2ad500da781b4e0369a1e9fc353d86a770f4e6129bc1d3583a67094c61297c152e84a5b0b4b21295c152a84a53094a22a93c15268aa4b0b4922a91c15228aa430b4822e8f4551d8aa371546a1e5fc0cbd86977032e6125bc0cb583967032c61257c24ae8195b092b4065640cac04957092ac22557d8aa01953032a2064ec0c9c819311125e064ac4493819230f0fe1a1dc243783867090be12174242bfa0551509e4a13454238a8451705e2e09c0c0f8181713ade235ac46b3f9563158de1f1b8463586c6a118ce1b198563187c62158be131784e2d83c5a138ae0f158562984c52156de22d9c55af89b570369e06d380da68ba6f114d62299c5d318ba5f134b62695c5d298aa4f0549a2a92c2d248aa470548a2a90c2d208ba3d154762a8dc551a8896f032d62259c0cb18995f032b62655c0ca98193b03272064c45c978192b1724e0648f083788867940be2615c54279284d1508e2a1145c178b8270303e0605c462f88c5b118ae2314c2d2f85a5b0b4ae1694c2d2785a4b0b48e1690c0caf8195b032ae0654c0ca78194b0328e0650c0c978192b0324e0648c462f88c5b118ae2314c152f82a5b054ae0a94c152782a4b0548e0a90c0caf8195b032ae0654c0ca78194b0328e0650c0c9a8192f032560649c0c9188d6f11ad62359c46b188b6f116d622d9c45b189b5f136b626d5c4da981a6f034d60699c0d3181a5f034b60695c0d2981a450347e068ec0d1b81a330f2dc1a59824af039560b27ddc4f0149b761340325c0f5bc26b583d6709ac60f1bc1e3705c6b0b8d41719c2e3305c63078c41317c262f03c5b078b40f15c1e2b04c53098a41edbc35b586b670f6c612d7c1dad83b57096a62ed3c55a68bb4b1768e2ad145da182a6f0b4d60a99c2d3182a5f074b60a95c252982a4f0549a0692c0d2482a470548a1290c0d2082a3f0b476168e8151b8ba360b4661e5bc0cb586967032c61257c0cad83957032a61253c14a68194b032920a51c14a28194303282224fc0c9d8893703266124bc0c958292a0524e0a4980c918586f030d61619c0c318485f030b60e15c0c298584f0b09a0612c2c238584503086160fc0c1d8583703066160bc0c1582827030460607c0c0d81817030260f9fc1f3e84e7b09cf40f9dc373b03e7511ce80f5fc1ebf03d7d09ade135b826b687c7f0d8f61b1dc3e3984c6f078d60f19c263184c5f098ba1316c262b8ac55098a60adfc2dbd82b770b6e60adbc1db582b67096c60ad7c15ae84b5b096b416d642dac02b57096ac0ad5415aa04b53096a20ad3c2da585b4a0568e2ed182da185a7f0f4fc169ec2d3d05a770d4ec169cc2d3904a6f094dc0e9ac1d3503a67074cc1298c253104a5f094bc12974252e04a5b094b4169642d2c04a57094ac16957a12a04a53094a412944252805a4f0b496169282d238aa460b486068fc0d1f01a3d0f2fe065ec34bb81973092de065ac1cb381963092be125740cad81959092ae225540ca9819511129e0652c44a381943032760a4e80c9c829370526c064cc0c98829270524c0a4942c3f8187b0b0ee061cc24378186b070ce0618c242f8485d030b61215c2c2a818530b09e0612c2c23818430b07e060ec141b818330b05e160b40c15858270b04a0608c0c0f8181b0302e0604c4eb788d6b11acfcd58c5e3788c6b118ce2f18c5e2f89c5b138ae2f14c15b785b6b056ce16d8c15af85b5b056ae16d4c15a785b4b0b6940ad1c5da305b430b4de1e9b82d3585a6a0b4ce1a9982d3185a620b4be129782d2d83a5a0b4ae0e9582d2984a520b49e1692c2d2505a471548c1690c0d1f81a3e0347a225bc0cb588967032c62657c0cad89957032a62e53c0ca58b94703286064ec149d019390526e0a4d80c99819310524e0a49814928586f030d61619c0c318585f030b61615c0c298584f030961611c0c218583f030760a0dc0c198582f0b05a060ac2c1385825030460607c0c0d8181703026235bc46b588d6711ac6231bc463588c67118c62717c4e2d89c57138a60adbc15b582b67056c60ad7c15ad82b57056a60ad3c15a582b4705686069bc0d3581a67034c60697c0d2d81a57034a60693c0d2581a4703486068fc151f01a3d0346e068d40d1981a32032de1e5b80cb58196a032ce1a5980cb181962032be125780cad8195a032ae0e5580ca9819520329e0652c0ca5019471528c0650c0c9b829360326a064bc0c970192d030de061ac0c3381863030be0616c0c2b818530309e0612c0c23818430307e060ec0c1b818330305e060ac0c13818230303e060740c0d818170302a0604c1eb784d6b07ace0b58c1e3781c6b0d8ce1f18c262f81c5b078ae1314c3db786b6b0d6ce1ed8c25af83b5b076ae12d4c5da78db4b1768e36d0c153782a6e054d60a99c153187a62054be0a978152d82a57054a612948152782a4e054960a924152382a43094840a904252002a3f054762a8e8151b82a36054660a5bc14b582967052c60a57c14ad82957052a60a53c14a70294b052920a51c14a18d942052820a4fc149d8d93a0526e0a4d814998192f0325c064b43c378186b0d0ce0618c242f8185b070ae0614c6c278184b1b08e0610c6c1f8183b1706e060cc14178e82d030560a09c1412818230503e0606c140b8181307cfe0f9f4273d84e7a07cee1b9d81f3a88e7407afe0f5f81ebe84d6f09adc135b43e3f86c7b0d8ee1f1cc263783c6b078ce1318c262f84c5d098b61315c562a84c53056fe0adf815bd86b7a056ee0add815b987b72056de0adb815b583b6a056ce0ad9815b184b62056be0ad7815ae82b5c056b612d6815ac8eb58056ae0ad5815aa82b54056a612d4815a884b500569e0ad2c55a502b470568c0ad0c153f82a7b054ee0a9cc153782a6b054ce0a98c152f82a5d054b612968152c85a58054ae0a958152a82a54054a60a944152782a4b1d4940a91c152302a430347e068f80d1e8797f032f61a5dc0cb98496f032d60e59c0cb18495f092ba0656c24ad01959032b01255c24ab08955e02a80654c0ca88894f032962251c0ca18293f0527c164f414978292e03256064a40c9182922032421e1fc0c3d86877030e6121bc0c3583867030c61217c242e8185b090ae6a1540c299184f030962e11c0c218283f1d07a060ec141b82835030660a0bc0c1582827030460607c0c0d8181703026275bc46b588d67deac62f1bc463588c67238c62f17c4e2d89c57238a60adbc15b702b6b0d6d40ad9c15b302b630f6c40ad7c15af02b5b076b40ad5c15ab02b53096a40ad3c15a58ab4a0568e0ad1815a182a6f054d60a99c153182a5f054b60a95c152982a4f054963a928152382a4605486068fc0d1f01a3d112de065ac44b381963132be0656c4cab819531d29e0652c5ca3819430527e0a4f82c9e8292f0525c064ac0c9481923052440648700378186b110ce0618e482f8185b130ae0614c8c278184b1708e0610c141f8e83d030760a0dc141a818330505e060ac1413818230303e0606c0c0b81813118be2316c462b88c53054be1696c152b85a530549e1692c152385a43032be0656c0cab819530329e0652c0ca3819430325e064ac0c9381923118be2316c462b88c53116be22d6c45ab88b531369e26d2c4da389b43054be1696c152b85a530549e1692c152385a430547e168ec151b85a33032be0656c0cab819530329e0652c0ca3819430327e064ec0c9b819330325e064b40c95819270324a0648c0c2f8185b030ae0614c0c278184b0308e0610c0c1f8183b0306e060cc0c178182b0304e0608c0c0f8181b0302e0604c46b788d6b11ace2358c463788c6b118ce2318c4e2f89c5b138ae2714c15b785b6b056ce16d8c15af85b5b056ae16d4c15a785b4b0568e16d0c0d3781a6b034ce0698c0d2f81a5b034ae0694c0d2781a4b0348e0690c0d1f81a3d03476068e80d1b82a360346a065bc3cb70196b032d40659c34b301963032c40657c24af0195b032b40655c1cab01953032a40653c0ca6ed14c03296065280ca38a9460328bb05100ca18193f0b27c064f40c978192e0325a061bc0c3581867030c60617c0c2d81857030a60613c0c258184703086060fc0c1d8183703066060bc0c1581827030460607c0c0e8181b0302e060540c0983d6d09ad20f59426b087c7e0d8f41b1d83e3907c6e0f8da1f1b03e350fc691f8d01f1986e328dc640f8c41f1843e3001c5a054da169a4153285a610549a16924152285a41032da065a40cb281961092bc0654824a70194d0d0ec1a1981ebf84d7b07aee135cc1eb783d6d09ad6135a41eb383d6509ac613584263f87c7e098f6131e8263b86c76098e6131c8263787c6e098da1f1b0263584c6a098d2131a0263387c66098ca3f190263184c62098c2131801dab03b460f4fe169ec353b85a730f4de0a9b42d3585a690f4ce0a9942d3185a61094be0e96c1d2b84a530949e0a934252585a490948e0a914252184a410f2fe065ec34bb819730f2de1e5b40cb5819690f2ce3e5940cb181961092be0656c1cab819530929e125340ca5819490928fa85140ca1819410b25e064ac5c93819230d0ec1a1981eb684d6907aca135843e3f06c7a0d8ec1f1c83e3707c6d0f8d81f1a87e348fc680f8cc371946e3207c620f8c21f180262f01c5a038ac071483db68ab651569a2ad14153682a69054ca0a9840d2681a490548a069040cb681969032ca0658424af019520529c065340c9502926030f41a1d83433018650309a061140c0e8181507afe135ec1ebb84d7307ade0f5b426b584d6907ace0f59426b184d61058fe1f1f8163d82c7a058ee1b1d8163982c72058de1f1b8163687c6c058d60b1a8163482c68058ce1f19816328fc64058c60b188163082c60058be13178162e87b7f0d6ee1edbc3db687b67156ca12d7c1dab82b4f0569a0ad1c55a282a7f054f60a9dc153982a6f054da0a9ac153482a67054ca0a98c153082a5b074b40a964152b82a56054a60a944152382a460548a0a8ec151b8797f032f61a5dc0cb98796f0f2da065ac0cb4879671f2ca0658c0cb08495f032b60e55c0ca98294f0529a0652c0ca482947d028a0650c0ca08193b1726e0a4bc0c958292703246161e82c3b868760b0ce1a1982c328485f070ae0a13c1426828470b08a0a0bc14138181f0302e0f5b426b483d6509ac21f1f8363d06c760f8e41f1b83e3687c6c0f8d4371a46e3407c661f8ca3f1903e3107c610f8c0131781e2d03c56098a40a9b4153482a65054c2069243cbf019720f2dc065b43cb601969032ca065880cb0819602f2bc0654814a301945032540a498343b068660f8de1b1ac363387c630f8be1f16c262c87c570f8a6131443db787b6d0d6d61ada835b386b661f6ca0ad8c15af82b5d0d6b61ad6815ab82b56056aa0ad5015a990b4f1969632d1c85a18296f052d60a59c14b18295f052ba0a56c14ab82955052a60a53c14a582947052861e1bc0c3586867030c61e17c3c2e8185b0f0ae3e1540c299584f030963211c0c219083f03076420dc0c198281f030360a05c0c0987d7f0daf61b5dc3eb987d6f07ada1f5ac26b487d6707aca1f58c26b082c7f058fc0b1ec363d02c77058ec0b1cc3e3902c6f058dc0b1b4163602c6b0f8d40b1a47e3402c67058cc0b194163202c630f8c40b1843e3002c5f058bc0b16c1e2d02c57058ac0b14c262902b4e054fe0a9ec153b82a73054de0a9b4153582a69054ce0a994153182a61054be0a96c152b82a53054721e5fc0cbd86977032e61e5bc3cb68196b032d21e59c7cb281963032c38c57c0cad8c957032a60a53f30a68194b032920a51c14a281943032822a4d414978592d032560a49c1492819230d0ec1a19814276504c0faf8135e04eba04d70058f83f1e0163a07c70058b827160162a04c502f29806500ac2603d7f09af60f5dc26b983d6f07ada135ac26b483d6707aca1358c26b084c7f0f8fc131ec263d04c770d8ec131cc263904c6f0f8dc131b43e3604c6b098d4131a4263404c670f8cc131944e3204c63098c413184263001c5f038bc071743dbf86b770f6de1edb43db38ab65096be0ed5c25a784b4d0968e26d143d3f85a7b0d4ee169cc3d3782a6d0b4d6169a43d3382a650b4c616984252f83a5b074ae1294c252782a4d0949616924252382a4509486129042d1de3237032fe065ec0cbb81973032de065b40cb581969032ce065940cb181961032b6065680cac81957072ac0654c0ca8819470728c065140c9d819370325e064ac0c9381923030f4061dc343b018670d0cc061940c2f818570309e061340c23818450305e0609c0c0f818170fafe1b5ec36bb87d730fade0f5b43eb584d690face0f5943eb184d610f8fe1f1f8363d86c7a0d8ee1b1d83e3987c720f8de1f1b83e3687c6c0f8d61f1a856348fc680f8ce1f19856328ac640f8c61f1883e3087c60158be131784e2d83c5a138ae0f158562984c520369c1e9fc2d3d86a770b4e61e9bc153685a6b0b4d21e99c153285a630b4c22e97c2d2d89a570b4a62a93c152685a4b0b4922a91c152285a430b4822a8d40cbf8197b032ee065cc0cb78196d032d6065a40cb381965032c6065840caf8195b032ae0654c0c9c8192f032560649c0c91868760d0cc1f5fc36bd86d770fae61f5bc1eb687d6b09ad21f59c1eb287d6309ac21f1fc363b87c6f0f8da1f19c56328bc5f138ae0adfc15bf02b7b0d6f40addc15bb02b730f6e40adbc15b702b6d056d80adac3db502b691d6d00ad9c15b302b65056c80ad8c3db102b610f6c00ad7c15af02b5b076b40ad5c15ab02b53096a40ad2c55a502b470568c0a9fc153d82a77054e60a9bc153682a6b054d20a99c153282a63054c20a97c152d82a57054a60a92c2d2502a470548c068fc0d1f01a3d032fe065ec0cbb81973032de065b40cb581969032ce065940cb181961032be0656c0cab81953032960651c0c9f8293e0327a064bc14970192b032520648c0c9101921030f4061dc343b018670d0cc061940c2f818570307e060f40c1b818350305e0609c0c0f818170f8de1b1ac363387c630f8be0f1743e2d84c590f8ae0f1543e2984c510f6de1ad9c3daf87b5d0f6ae2ad5749a78cb470f4de169ac353385a630f4be0a9742d2d85a590f4ae0a9542d2985a51ce49e1692c652385a430b477908dc3cb78196b0d2ce0658c3caf8795d032b6065643cab8f955032a60654710a78194b1928e0650c0c9de11370b25e064af0093819230d0d41a19c3433068570d0ac1a15464278c8470b05e1609c0c0f81817 20 1048575 8 255 11 2047 19 524287
def cc_67_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xb5761af463aa54fa277e9bd6a9219c8cc55848847e5637cd1878f3e72a656ff2b68679650365ba9656f4b5402f4ba86459613f6633a74f3297e2bf6a2239c1ce5514a840e7630cf180913e02c650002c 0x1d6f01d6e01d6d07c6f06c6b06c6707c6307c5f03c5d07c5b04c5907c5703c5507c5304c5107b6f06b6b06b6707b6307b5f07b5d07b5b07b5708b5507b53a434f09b4b09b4712b4307a6f06a6b06a6707a6307a5f02a5d07a5b05a5907a5702a5507a5305a51a224f09a4b09a470ea4312a3f0ea3b9f2370ea330196b0696a01969069670696601963019610695706956069550894f0194b08947019430893f0193b08937019330892f0192b08927019230786f0186b06867018630785f0785d0185b0785708855018534b04f0184b09847018431283f0183b35037018330e82f0182b28027018230181f0181b018170181306d6f06d6b06d6706d6306c6f06c6b06c6706c6309c5f09c5b09c5709c5306b6f06b6b06b6706b6309b5f09b5b09b5709b530eb4f0eb4b0eb470eb4301a6f06a6e01a6d01a6701a6501a6301a6201a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330196706966019650195f0495e0195b0195a019570395601953019520194f0194b0194a019470a946019430193f0593e0193b0193a019370293601933019320192f0192e0192d0186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b0182701825018230181f0181d0181b01817018150181304d6f04d6e01d6b01d6a04d6701d6604d6304d6203c6f04c6b03c6704c6303c5f03c5d04c5b03c5703c5506b6f06b6703b5f03b5d06b5703b5504b4f03b4706a6f06a6b06a6706a630ba5f02a5d0ba5b05a590ba5702a550ba5305a5104a4f03a4b03a4704a430aa3b0aa370696f0196b04967019630795f0795d0195b01959049570495501953019510494f0194b03947019430193b089370892f0192b08927019230686f068670f85f0f85d0f8570f8550484f038470b82f0b8270181f0881d018170f81501e7f01e7e01e7d03d7f03d7d04d7b04d7903d7703d7504d7304d7103d6f04d6b03d6704d6304c7f06c7e04c7d9c47c04c7b04c7a04c7904c7804c7706c7604c7506c7404c7304c7204c7104c7004c6f06c6e04c6b04c6a04c6706c6604c6304c6206b7f06b7e0ab7d0ab7c06b7706b7506b7206b6f06b6703b5a03b5703b5603b4703b4603b4506a7f02a7d06a7b05a7906a7702a7506a7305a7106a6f06a6b06a6706a6304a5f03a5b03a5704a5304a4f02a4d04a4b05a4904a4702a4504a4304a410aa3b0aa370697f0697e0797d0696f0696e0196b019690196306962019610495f0195b03957019530494f0494d0194b01949049470894501943019410193b089370892f0192b08927019230687f0f87d06877068750686f068670485f038570484f0484d048470f8450b82f0b8270181f0881d018170f81502d6f02d6e01d6b01d6a02d6701d6602d6302d6203c6f04c6b03c6704c6303c5f03c5d04c5b04c5903c5703c5504c5304c5106b6f06b6b06b6706b630bb5f0ab5d11b5b0bb570ab5511b5304b4f03b4b03b4704b4302a6f02a6b02a6702a6302a5f02a5d02a5b02a5902a5702a5502a5302a5102a4f02a4b02a4702a4302a3f02a3b02a3702a330696f0196b02967019630795f0795d0195b01959029570295501953019510494f0194b03947019430893f0193b08937019330292f0192b02927019230686f0186b06867018630f85f0f85d0185b0f8570f855018530484f0184b03847018430f83f0183b0b837018330282f0182b02827018230181f0881d0181b018170f8150181301e7f01e7e01e7d03d7f03d7d04d7b04d7903d7703d7504d7304d7103d6f04d6b03d6704d6302c7f06c7e02c7d9a47c02c7b02c7a02c7902c7802c7706c7602c7506c7402c7302c7202c7102c7002c6f06c6e02c6b02c6a02c6706c6602c6302c6202c5f04c5e02c5d06b7f0ab7d06b7b06b7706b7506b7306b6f06b6b06b6706b6304b5f03b5b03b5704b5302b4f02b4d02b4b02b470ab4502b4302a7f02a7e02a7d02a7c02a7b02a7902a7702a7502a7306a7202a7105a7002a6f02a6b02a6702a6302a5b03a5a02a5902a5702a5602a5302a5102a4702a4602a4502a3f02a3b02a3702a330697f0697e0797d0696f0696e0196b019690196306962019610495f0195b03957019530294f0294d0194b01949029470894501943019410893f0193b08937019330292f0192b02927019230687f0f87d0187b0687706875018730686f0186b06867018630485f0185b03857018530284f0284d0184b028470f845018430f83f0183b0b837018330282f0182b02827018230181f0881d0181b018170f8150181306d6f06d6b06d6706d6306c6f06c670ac5f09c5702b6f02b6e01b6b01b6a02b6701b6602b6302b621eb5f04b5e09b5b03b5a09b5703b561eb5304b5205b4b05b4a06b4705b4602a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4b02a4702a3b02a3902a3702a3302a310696f0696e0196b0296701963069620895f0195b08957019530894d0194b08947089450793f0793d0193b01939029370293501933019310292f0892d0192b0292702925019230686f068670f85f098570f83f0f83d0f8370f8350282f028270181f0881d018170f81501e7f01e7e01e7d06d7f03d7d06d7b04d7906d7703d7506d7304d7106d6f06d6b06d6706d6302c7f02c7e02c7d02c7c02c7b06c7a02c7906c7802c7702c7602c7502c7402c7306c7202c719847002c6f02c6e02c6b06c6a02c6702c6602c6306c6202c5f02c5e02c5b03c5a02c5702c5602c5304c5206b7f0ab7d06b7706b7506b6f06b670ab5f09b5702b4f02b4e05b4d02a7f02a7d02a7b02a7902a7702a7502a7302a7102a6f02a6b02a6702a6302a5f02a5b02a5702a5302a3b02a3902a310ea300697f0697e0797d0696f0696e0196b019690196306962019610895f0195b08957019530294f0894d0194b01949029470294501943019410893d0193b08937089350292f0892d0192b0292702925019230687f0f87d06877068750686f068670f85f098570284f0f84d02847028450f83d0a8350282f0b82d02827028250181f0881d018170f81501d6f01d6e01d6d06c6f03c6d06c6b04c6906c6703c6506c6304c6106c5f06c5b06c5706c5306b6f0ab6d06b6b06b6706b6506b6306b5f06b5b06b5706b539b34f09b4b09b4712b4306a6f02a6d06a6b05a6906a6702a6506a6305a6106a5f06a5b06a5706a539924f09a4b09a470ea4312a3f0ea3b972370ea330696f0696e0796d0695f0695e0195b019590195306952019510894f0194b08947019430893f0193b08937019330892f0192b08927019230686f0f86d0186b0686706865018630685f0185b06857018530f84f0184b09847018430f83f0183b0f837018330e82f0182b0f827018230181f0881d0181b018170f8150181307c5f06c5b06c5707c5305a5f05a5b05a5705a5305a4f05a4b05a4705a430195f0195b01957019530194f0194b01947019430192f0192b019270192307c5f06c5b06c5707c5307b5f06b5b06b5707b5309b4f09b4b09b4709b4307a5f06a5b06a5707a5309a4f09a4b09a4709a430ea3f0ea3b0ea370ea330195f0195b0195a0195706956019530194f0194b01947019430193f0193b01937019330192f0192b01927019230185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181307d6f06d6b06d6707d6307c6f06c6b06c6707c6309c5f09c5b09c5709c5307b6f06b6b06b6707b6309b5f09b5b09b5709b530eb4f0eb4b0eb470eb4301a6f01a6d01a6b01a6a01a6706a6601a6501a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0796e0196d0195f0495e0195b0195a019570395601953019520194f0194b0194a019470a946019430193f0593e0193b0193a019370293601933019320192f0192e0192d0186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181d0181b0181a95018018170181601815940140181303d6d04d6903d6504d6107c7e04c7a06c7604c7209c6e04c6d09c6c04c6a04c6904c6809c6604c6509c6404c6204c6104c6001c5e01c5d02a6d05a6902a6505a6102a4d05a4902a4504a410196d0196901965019610195a01959039560195103946019450787e0786e0181603d7f04d7b03d7704d7303d6f03d6d04d6b04d6903d6703d6504d6304d6104c7f07c7e04c7b04c7a04c7706c7604c7304c7204c6f07c6e04c6d07c6c04c6b04c6a04c6904c6804c6707c6604c6509c6404c6304c6204c6104c6001c5f01c5e01c5d06b7a06b7706b7606b6706b6606b6504b5f03b5704b4f04b4d04b4709b4507a7f06a7b06a7707a7307a6f02a6d07a6b05a6907a6702a6507a6305a6104a5f03a5b03a5704a5304a4f02a4d04a4b05a4904a4702a4504a4304a410aa3b0aa370797f0197b06977019730796f0796d0196b01969079670896501963019610195b0395a01959039570395601953019510394703946039450193b089370892f0192b08927019230787f068770786f0786d07867920650485f038570484f0484d04847098450b82f0b8270181f0181705e7e01e7203d6d04d6903d6504d6107c7e04c7a06c7604c7209c6e04c6d09c6c04c6a04c6904c6809c6604c6509c6404c6204c6104c6001c5e01c5d0ab6d0ab6504b4d09b4501a6d02a6502a4d02a4902a4502a410196d0196901965019610195a01959039560195103946019450787e018720286e0186d0184d018450182a028260181a0181602e7f05e7e02e7d03d7f04d7b03d7704d7302d6f02d6d02d6b04d6902d6703d6502d6302d6104c7f07c7e04c7b04c7a04c7706c7604c7304c7202c6f02c6e02c6d02c6c02c6b02c6a04c6904c6802c6702c6604c6509c6402c6302c6202c6102c6001c5f01c5e01c5d07b7f06b7b06b7707b7302b6f02b6d02b6b02b670ab6502b6304b5f03b5b03b5704b5304b4f04b4d04b4b04b4709b4504b4302a7b06a7a02a7902a7702a7602a7302a7102a6702a6602a6502a5f02a5b02a5702a5302a4f02a4d02a4b02a4902a4702a4502a4302a4102a3f02a3b02a3702a330797f0197b06977019730296f0296d0196b01969029670896501963019610195b0395a01959039570395601953019510394703946039450893f0193b08937019330292f0192b02927019230787f0187b06877018730286f0286d0186b0286790065018630485f0185b03857018530484f0484d0184b0484709845018431183f0183b0b837018330282f0182b02827018230181f0181b018170181303d6f04d6b03d6704d6304c6f07c6e04c6b04c6704c6304c6201c5f01c5e01c5d0db6f08b6b08b670db6304b5f04b5d03b5b03b5a03b5703b5609b5502b5302b4f02b4d03b4b03b4a02b4702b4602b4502b4402b430aa6f08a6704a5f03a5704a4f04a4d04a4709a4505a3f09a370296f0296b02967029630295f0295b02957029530294f0294d0294b0294702945029430193b02937029330292b029271786f088670485f038570484f0484d04847098450d83f0d8370281f0281707d7e04d7a06d7604d7201d6e01d6d07c7e06c7a06c7607c7204c6e03c6a03c6604c6204c5e04c5d04c5c04c5a09c5909c5804c5609c5509c5404c5204c5104c5002a5d02a5902a5502a510196a01969039660196103956019550194d0194901945019411587e0486e0485e0485c02846028260181603e7f04e7b03e7704e7304d7f07d7e04d7b04d7a04d7706d7604d7304d7201d6f01d6e01d6d02c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6b03c6a02c6702c6602c6304c6202c5f02c5e02c5d02c5c02c5b04c5a02c5909c5802c5702c5602c5502c5402c5304c5202c5104c500ab7f08b7704b6f03b6704b5f04b5d04b5709b5502b4f02b4e05b4d02a7f02a7b02a7702a7302a6f02a6b02a6702a6302a5f02a5d02a5b02a5902a5702a5502a5302a5102a3b02a3902a310ea300897f0197b08977019730196b0396a01969039670396601963019610395703956039550294f0294e0994d8e14c0194b019490294702945019430294201941019400993d0193b09937099350292f0992d0192b0292702925019236307f088770486f038670485f0485d04857098550284f8d04d02847028451183d0a8350282f0b82d02827028250181f0181703d6f04d6b03d6704d6304c6f07c6e04c6b04c6a04c6706c6604c6304c6201c5f01c5e01c5d9136f08b6b08b6712b6304b5f03b5b03b5704b5304b4f04b4d04b4b04b4709b4504b438f26f08a6b08a670ea6304a5f03a5b03a5704a5304a4f02a4d04a4b05a4904a4702a4504a4304a4112a3f0ea3b8c2370ea330896f0196b08967019630195b0395a01959039570395601953019510394703946039450993f0193b09937019330992f0192b09927019236206f0186b08867018630485f0185b03857018530484f0484d0184b0484709845018431283f0183b34037018330e82f0182b27027018230181f0181b018170181303d6f03d6b03d6703d6308c6f08c6b08c6708c6303c5f03c5b03c5703c5308b6f08b6b08b6708b6303b5f03b5b03b5703b530eb4f0eb4b0eb470eb4301a6f01a6b01a6701a6301a5f03a5e01a5d01a5701a5501a5301a5201a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0796e0196b0196a019670696601963019620195703956019550194f0194b0194a019470a946019430193f0593e0193b0193a019370293601933019320192f0192e0192d0186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b0182701825018230181f0181d0181b01817018150181303d6f03d6b03d6703d6303c6f03c6b03c6a03c6703c6603c5f03c5e01c5b01c5a03c5701c5603c5303c5203b6f06b6703b5f03b5706b4f06b4d03b4703b4507a6f06a6b06a6707a6303a5f03a5b03a5703a530ba4f02a4d0ba4b05a490ba4702a450ba4305a410aa3b0aa370796f0196b06967019630395f0195b03957019530494f0494d0194b01949079470494501943019410193b089370892f0192b08927019230786f068670385f038570c84f0c84d0c8470c8450b82f0b8270181f0881d018170c81503d7f03d7e03d7b06d7a03d7703d7603d7307d7203d6f03d6e03d6d03d6c03d6b07d6a03d698956803d6703d6603d6503d6403d6307d6203d6107d6003c7f03c7b03c7703c7303c6f03c6d03c6b03c6903c6703c6503c6303c6101c5f01c5e01c5d06b7a06b7706b7606b6706b6606b6503b5f03b5e0ab5d0ab5c03b5703b5503b5203b4f03b4707a7f06a7b06a7707a7307a6f02a6d07a6b05a6907a6702a6507a6305a6103a5f02a5d03a5b03a5903a5702a5503a5305a5103a4f03a4b03a4703a430aa3b0aa370797f0197b06977019730796f0796d0196b01969079670896501963019610395f0395e0495d0394f0394e0194b019490194303942019410193b089370892f0192b08927019230787f068770786f0786d078670c8650385f0c85d03857038550384f038470b82f0b8270181f0881d018170c81503d6f03d6b03d6703d6303c6f03c6e03c6b03c6a03c6703c6605c6305c6202c5f02c5e01c5b01c5a02c5701c5602c5302c5207b6f06b6b06b6707b6303b5f03b5b03b5703b530bb4f0ab4d11b4b0bb470ab4511b4302a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f02a4d02a4b02a4902a4702a4502a4302a4102a3f02a3b02a3702a330796f0196b06967019630395f0195b02957019530494f0494d0194b01949029470294501943019410893f0193b08937019330292f0192b02927019230786f0186b06867018630385f0185b03857018530c84f0c84d0184b0c8470c845018430c83f0183b0b837018330282f0182b02827018230181f0881d0181b018170c8150181302e7f05e7e02e7d03d7f03d7e03d7b06d7a03d7703d7603d7307d7202d6f02d6e02d6d02d6c02d6b02d6a03d698756802d6702d6603d6503d6402d6302d6202d6102d6003c7f03c7b03c7703c7302c6f02c6d02c6b03c6902c6703c6502c6302c6101c5f01c5e01c5d07b7f06b7b06b7707b7302b6f02b6d02b6b02b670ab6502b6303b5f0ab5d03b5b03b5703b5503b5303b4f03b4b03b4703b4302a7b06a7a02a7902a7702a7602a7302a7102a6702a6602a6502a5f02a5e02a5d02a5c02a5b02a5902a5702a5502a5303a5202a5105a5002a4f02a4b02a4702a4302a3f02a3b02a3702a330797f0197b06977019730296f0296d0196b01969029670896501963019610395f0395e0495d0394f0394e0194b019490194303942019410893f0193b08937019330292f0192b02927019230787f0187b06877018730286f0286d0186b028670c865018630385f0c85d0185b0385703855018530384f0184b03847018430c83f0183b0b837018330282f0182b02827018230181f0881d0181b018170c8150181303d6f03d6b03d6703d630ac6f08c6703c5f03c571bb6f07b6e08b6b06b6a08b6706b661bb6307b6202b5f02b5e01b5b01b5a02b5701b5602b5302b5205b4b05b4a03b4703b4602a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4b02a4702a3b02a3902a3702a3302a310896f0196b08967019630395f0395e0195b0295701953039520994d0194b09947099450493f0493d0193b01939029370293501933019310292f0992d0192b0292702925019230c86f088670385f038570c83f0c83d0c8370c8350282f028270181f0981d018170c81503e7f03e7e03e7b06e7a03e7703e7603e7307e7203d7f03d7b03d7703d7301d6f01d6e01d6d02c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b03c6a02c6903c6802c6702c6602c6502c6402c6303c6202c618546002c5f02c5e02c5b03c5a02c5702c5602c5303c520ab7f08b7703b6f0ab6d03b6703b6503b5f03b5702b4f02b4e05b4d02a7f02a7b02a7702a7302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f02a5b02a5702a5302a3b02a3902a310ea300897f0197b08977019730396f0396e0496d0395f0395e0195b019590195303952019510294f0994d0194b01949029470294501943019410993d0193b09937099350292f0992d0192b0292702925019230c87f088770386f0c86d03867038650385f038570284f0c84d02847028450c83d0a8350282f0b82d02827028250181f0981d018170c81503d6f03d6e03d6b06d6a03d6703d6603d6307d6203c6f03c6b03c6703c6301c5f01c5e01c5d8836f08b6b08b6712b6303b5f0ab5d03b5b03b5703b5503b5303b4f03b4b03b4703b438626f08a6b08a670ea6303a5f02a5d03a5b03a5903a5702a5503a5305a5103a4f03a4b03a4703a4312a3f0ea3b842370ea330896f0196b08967019630395f0395e0495d0394f0394e0194b019490194303942019410993f0193b09937019330992f0192b09927019230c86f0186b08867018630385f0c85d0185b0385703855018530384f0184b03847018430c83f0183b0c837018330c82f0182b0c827018230181f0981d0181b018170c8150181303c5f04c5b03c5704c5305a5f05a5b05a5705a5304a4f03a4b03a4704a430195f0195b01957019530194f0194b01947019430192f0192b019270192303c5f04c5b03c5704c5308b5f08b5b08b5708b5304b4f03b4b03b4704b4308a5f08a5b08a5708a5304a4f03a4b03a4704a430ea3f0ea3b0ea370ea330195f0195b01957019530194f0194b0194a0194703946019430193f0193b01937019330192f0192b01927019230185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181303d6f04d6b03d6704d6308c6f08c6b08c6708c6304c5f03c5b03c5704c5308b6f08b6b08b6708b6304b5f03b5b03b5704b530eb4f0eb4b0eb470eb4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5a01a5703a5601a5501a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0796e0196b0196a019670696601963019620195f0495e0195d0194f0194b0194a019470a946019430193f0593e0193b0193a019370293601933019320192f0192e0192d0186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181d0181b0181a82018018170181601815810140181303d6f04d6b03d6703c6f03c6e04c5f04c5e07a6f06a6b06a6707a6304a5f03a5b03a5704a5311a4f02a4d0ba4b05a4911a4702a450ba4305a4111a350796f0196b06967019630495f0195b03957019530494f0494d0194b01949089470894501943019410892f0192b0892701923 20 1048575 8 255 11 2047 20 1048575
def cc_67_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xd7e6dad42b449665435c06a3758b6cb205692da52813f0b65ca1c97228fe31134ca071fbd9357486adfc95a49b32b1e62630b94b9559d2911a4e042914ace63c996362012c2d52c431780086 0x3e7d04e7a06e7603e750ce7403d7e03d7d04d6e04d6d07c7e06c7a06c7607c7204c6e03c6a03c6604c6204c5e04c5d04c5c04c5a10c5910c5804c5613c5513c5404c5204c5104c5004b560ab5402a5d04a5a02a5905a5802a5602a5502a5402a510495d01959bf155019510a14d01949bd145019410787e0486e0485e0485c02846028260601608e7404c5c15c580dc5404c500ab5405a5802a54019580d95409d6f08d6b08d67bd5630dc6f07c6e08c6b06c6a08c6706c660dc6307c620dc5f04c5e09c5b03c5a09c5703c560dc5304c5202a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f02a4d0196f0196b01967019630195f0195b01957019530194f0d94e0194d0192f0192b019230cd6f0fd6b0cd67be56313c6f07c6e0fc6b06c6a0fc6706c6610c6307c6213c5f04c5e0cc5b03c5a0cc5703c5610c5304c5202a6f02a6b02a6702a6302a5f02a5b02a5702a53a016f0196b0f967019638d15f0195b0c957019531094f0914d0194b0194913947bc14501943019410292f0192b02927019236506e4e05e028460282605016ce56fcc56bca567c456302c6f02c6e02c6b06c6a02c6702c6602c6307c6202c5f02c5e02c5b03c5a02c5702c5602c5304c520ab6f0ab670ab5f0ab5702b4f02b4e05b4d02a6f02a6b02a6702a6302a5f02a5b02a5702a5302a3b02a3902a31a72309f16f0e96b971670e9638c15f0e95b841570e9530294fc014d0294b01949029470294502943019411193d0a93b0a9370a9350292f0b92d0292b0292702925029236406f580674d05f410570284fbb04d02847028451183d0a8350282f0b82d02827028250e81f0401704d6f04d6e03c6b06c6a03c6703c6603c6303c5703c5502a6f05a6b02a6705a6302a5f02a5d05a5b05a5902a5702a5503a5303a5102a4f03a4b02a4703a430796f0696b06967079630995f0995d0895b01959099570995508953019510394f0394b03947039430592f0292b029270592303e7f04e7e03e7d03d7b06d7a03d7903d7703d7603d7303d7103d6703d6603d6502b7f05b7b02b7705b7302b6f02b6d03b6b05b6902b6702b6503b6303b6102b5f03b5b02b5703b5302b45af34407a7e07a7c06a7606a7403a6e03a6c03a66b926403a5e03a5605a3e0797f0697b06977079730396f0396d0396b01969039670996503963019610395f0395b03957039530593f0293b0293705933019290992503d6f03d6d03d6703d6504d6303c6703c6604c5f04c5e02a6f05a6b02a6705a6302a5f03a5b02a5704a5302a4f02a4d05a4b05a4902a4702a4504a4304a410696f0696b06967069630495f0395b03957049530894f0894d0894b01949089470894508943019410592f0292b029270592303e7f06e7e03e7d03e7703e7504e7304e7203d7703d7603d7504d6f04d6e04d6d02b7f05b7b02b7705b7302b6f03b6b02b6704b6302b5f02b5d04b5b05b5902b5702b5504b5304b5102b45ae34406a7e06a7604a6e04a6c03a6603a6404a5e04a5c04a56b725405a3e0697f0697b06977069730496f0396b03967049630495f0495d0495b01959049570895504953019510593f0293b0293705933019290892504d6f04d6d03c6f03c6d03c5f03c5b03c5302a6f02a6d03a6b03a6902a6702a6505a6305a6102a5f05a5b02a5705a5302a4f03a4b02a4703a4302a35ad2340896f0896d0896b01969089670896508963019610695f0695b06957069530394f0394b03947039430592f0292b029270592303e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6306d6203d61b356002b7f02b7d03b7b03b7902b7702b7503b7305b7102b6f05b6b02b6705b6302b5f03b5b02b5703b5302b45ac34403a7eb527c03a7603a7406a6e07a6c06a6606a6403a5e04a5c03a5603a5405a3e0397f0897d0397b01979039770397503973019710696f0696b06967069630395f0395b03957039530593f0293b0293705933019290892503d6f03d6e04d6d02b6f03b6b02b6703b6302b5f04b5b02b5704b5302b45ab34403a6e03a6604a5e04a5c04a56b225405a3e0396f0396b03967039630495f0495b04957049530593f0293b0293705933019290892503c5f03c5e02a5f03a5b02a5703a5302a4f05a4b02a4704a4302a35aa2340395f0395b03957039530894f0894b08947089430592f0292b029270592303d6f03d6d04d6b04d6a03d6706d6603d65b256403c6f03c6e04c5f04c5e02a6f05a6b02a6705a6302a5f03a5b02a5704a5302a4f02a4d05a4b05a4902a4702a4504a4304a4102a35a92340796f0696b06967079630495f0395b03957049530e94f0d94d0894b019490e9470d94508943019410592f0292b029270592303e7f03e7d04e7b04e7a03e7706e7603e75b367403d7f03d7e03d7d04d6f04d6e04d6d02b7f05b7b02b7705b7302b6f03b6b02b6704b6302b5f02b5d04b5b05b5902b5702b5504b5304b5102b45a834407a7e06a7604a6e03a6604a5e04a5c04a56b125405a3e0797f0697b06977079730496f0396b03967049630495f0495d0495b01959049570d95504953019510593f0293b0293705933019290e92503d6f04d6e03d6d03c6b06c6a03c6903c6703c6603c6303c6103c5703c5603c5502b6f02b6b02b6702b6302b5f02b5d02b5b02b5902b5702b5502b5302b5102b4f02b4b02b4902b4702b4302b4102a3e0796f0696b06967079630395f0395d0395b01959039570995503953019510394f0394b03947039430293f0293b02937029330992503d6f06d6e03d6d03d6703d6504d6304d6203c6703c6603c6504c5f04c5e04c5d02b6f02b6b02b6902b6702b6302b6102b5f02b5b02b5702b5302b4f02b4d02b4b02b4902b4702b4502b4302b4102a3e0696f0696b06967069630495f0395b03957049530494f0494d0494b01949049470894504943019410293f0293b02937029330892504c5f03b5f03b4f03b4b03b4302a5f02a5b02a5902a5702a5302a5102a4f02a4b02a4702a4302a3f02a3b02a3702a330895f0895d0895b0895708955089530694f0694b06947069430393f0393b03937039330292f0292b029270292303d6f03d6e04d6d03c6f03c6e03c6d03c5f03c5e03c5b03c5903c5306c5203c51ab45002b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5302b4f02b4b02b4702b4303a6ead26c02a3e0396f0896d0396b01969039670396503963019610695f0695b06957069530394f0394b03947039430293f0293b02937029330892503c5f03c5e04c5d02b5f02b5b02b5902b5702b5302b5102b4f02b4b02b4702b4303a5e04a46aa24402a3e0395f0395b03957039530494f0494b04947049430293f0293b02937029330892503b4f03b4e02a4f02a4b02a4902a4702a4302a4102a3f02a3b02a3702a330394f0394b03947039430893f0893b08937089330292f0292b029270292303c5f03c5d04c5b04c5a03c5706c5603c55aa45403b5f04b4f02a5f02a5b02a5902a5702a5302a5102a4f02a4b02a4902a4702a4302a4102a3f02a3b02a3902a3702a3302a310795f0695b06957079530494f0394b03947049430e93f0d93d0893b0e9370d935089330292f0292b029270292303d6f03d6d04d6b04d6a03d6706d6603d65ab56403c6f03c6e03c6d04c5f04c5e04c5d02b6f02b6b02b6902b6702b6302b6102b5f02b5b02b5902b5702b5302b5102b4f02b4d02b4b02b4902b4702b4502b4302b4104a46a924402a3e0796f0696b06967079630495f0395b03957049530494f0494d0494b01949049470d94504943019410293f0293b02937029330e925af45fae45bac457a845302b5f02b5b02b5702b5302b4f02b4b02b4702b4302a3e0e95f0e95b0e9570e9530e94f0e94b0e9470e9430293f0293b02937029330e925b856fb656bb4567b056302b6f05b6b02b6705b6302b5f05b5b02b5705b5302b45a734407a6e06a6604a5e03a5605a3e0e96f0e96b0e9670e9630e95f0e95b0e9570e9530593f0293b0293705933019290e92501e7e01e7d03d6d04d6903d6504d6107c7e06c7a06c7607c7207c6e07c6d07c6c07c6a08c6908c6807c6608c6508c6407c6207c6107c6002a6d05a6902a6505a6102a4d05a4902a4505a410197a01979069760197106966019650194d0194901945019410485e0484e0181601e7f01e7e01e7d03d7f04d7b03d7704d7303d6f03d6d04d6b04d6903d6703d6504d6304d6104c7f07c7e04c7b04c7a04c7706c7604c7304c7204c6f07c6e04c6d07c6c04c6b04c6a04c6904c6804c6707c6604c6508c6404c6304c6204c6104c6007b7f06b7707b6f07b6d07b6708b6503b5a03b5703b5603b4703b4603b4507a7f06a7b06a7707a7307a6f02a6d07a6b05a6907a6702a6507a6305a6104a5f03a5b03a5704a5304a4f02a4d04a4b05a4904a4702a4504a4304a410aa3b0aa370197b0697a01979069770697601973019710696706966069650495f0195b03957019530494f0494d0194b01949049470894501943019410193b089370892f0192b08927019230787f068770786f0786d07867088650485f038570484f0484d04847a50450b82f0b8270181f0181701e7e01e7d03d6d04d6903d6504d6107c7e06c7a06c7607c7207c6e07c6d07c6c07c6a08c6908c6807c6608c6508c6407c6207c6107c6004c5e01c5207b6d08b650ab4d0ab4502a6d02a6902a6502a6101a4d02a450197a01979069760197106966019650194d0194901945019410186d018650485e018520284e0184d0182a028260181a0181601e7f01e7e01e7d03d7f04d7b03d7704d7303d6f03d6d04d6b04d6903d6703d6504d6304d6102c7f07c7e02c7b02c7a02c7706c7602c7302c7202c6f07c6e02c6d07c6c02c6b02c6a02c6902c6802c6707c6602c6508c6402c6302c6202c6102c6002c5f04c5e02c5d07b7f06b7b06b7707b7307b6f07b6d07b6b07b6708b6507b6304b5f03b5b03b5704b5302b4f02b4d02b4b02b470ab4502b4302a7f02a7b02a7702a7302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5b03a5a02a5902a5702a5602a5302a5102a4702a4602a4502a3f02a3b02a3702a330197b0697a01979069770697601973019710696706966069650495f0195b03957019530294f0294d0194b01949029470894501943019410893f0193b08937019330292f0192b02927019230787f0187b06877018730786f0786d0186b0786708865018630485f0185b03857018530284f0284d0184b02847a3045018431183f0183b0b837018330282f0182b02827018230181f0181b018170181301d6f01d6e01d6d07c6f06c6b06c6707c6307c5f07c5b04c5907c5707c5304c5107b6f07b6d06b6b06b6a06b6706b6608b6502b6302b5f02b5d06b5b06b5a02b5702b5602b5502b5402b530db4f09b4b09b470db4307a6f06a6707a5f07a5d07a5708a550aa4f09a4705a3f08a370296f0296b02967029630295f0295d0295b0295702955029530294f0294b02947029430193b02937029330292b029270786f068670785f0785d07857088551784f098470d83f0d8370281f0281701e7e01e7d03d6d04d6903d6504d6107c7e06c7a06c7607c7207c6e07c6d07c6c07c6a08c6908c6807c6608c6508c6407c6207c6107c6004c5e03c5a03c5604c5202a6d02a6902a6502a610197a01979069760197106966019650194d0194901945019410787e0786e0786c1585e02846028260181601e7f01e7e01e7d07d7f06d7b06d7707d7307d6f03d6d07d6b04d6907d6703d6507d6304d6102c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b07c6a02c6908c6802c6702c6602c6502c6402c6307c6202c6107c6002c5f02c5e02c5b03c5a02c5702c5602c5304c5207b7f06b7707b6f07b6d07b6708b650ab5f09b5702b4f02b4e05b4d02a7f02a7b02a7702a7302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f02a5b02a5702a5302a3b02a3902a310ea300197b0697a01979069770697601973019710696706966069650895f0195b08957019530294f0294e0894da114c0194b019490294702945019430294201941019400893d0193b08937089350292f0892d0192b0292702925019230787f068770786f0786d07867088654c05f098570284fa004d02847028451183d0a8350282f0b82d02827028250181f01817 19 524287 8 255 11 2047 20 1048575
def cc_67_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9ee6198d6192c618ee3e8b03e86f4184d2280c417eb2176e7d6f17d66f826204f59e825524c5034f47d8642e4f3a886356522cc8a29f2d2435c1ee5519e50168360d692090460870905a2d0085200008 0x3d6f03d6b03d6703d630bc6f0bc6b0bc670bc6303c5f03c5b03c5703c5302b6f05b6b02b6705b6302b5f03b5e02b5d02b5702b5503b5303b5202b4f05b4b02b4705b4303a6f07a6e03a6b03a6a03a6706a6603a6303a6202a5702a5602a5503a4f03a4b03a4a03a470aa4603a4303a3f04a3e03a3d0996f0996b09967099630395f0395b03957039530994f0994b09947099430593f0293b02937059330392f0392d0392b01929039270992503923019210586f0586b05867058630385f0385b03857038530584f0584b05847058430583f0283b02837058330382f0382d0382b0382705825038230581f0581b058170581302d6f02d6e02d6b06d6a02d6702d6602d6307d6203c6f03c6b03c6703c6302c5f02c5e03c5d0bb6f11b6b0bb6711b6302b5f0ab5d02b5b02b5702b5502b5303b4f03b4b03b4703b4302a6f02a6b02a6702a6302a5f02a5e02a5d02a4f02a4e02a4b02a4902a4303a4202a4102a3f02a3b02a3702a330996f0996b09967099630295f0995d0295b01959029570295502953019510394f0394b03947039430993f0993b09937099330292f0292b02927029230c86f0586b0c867058630285f0c85d0285b0285702855028530384f0384b03847038430c83f0583b0b837058330282f0282b02827028230981f0581b098170581303d6f04d6b03d6704d630bc6f0bc6b0bc670bc6304c5f03c5b03c5704c5302b6f05b6b02b6705b6302b5f02b5d03b5b03b5a02b5703b5602b5502b4f05b4b02b4705b4304a6f07a6e04a6b04a6a04a6706a6604a6304a6202a5f02a5e02a5d04a4f04a4b04a4a04a470aa4604a4303a3f03a3e03a3d0e96f0996b0e967099630495f0395b03957049530b94f0994b0b947099430593f0293b02937059330492f0492d0492b01929049270e92504923019210586f0586b05867058630485f0385b03857048530584f0584b05847058430583f0283b02837058330482f0482d0482b0482705825048230581f0581b058170581303e7f04e7e03e7d03d7b06d7a03d7903d7703d7603d7303d7103d6703d6603d6507b7e06b7603b6e03b6c03b660bb6403b5e03b5602a7f02a7b02a7702a7302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f02a5b02a5702a5302a4902a350797f0697b06977079730396f0396d0396b01969039670996503963019610395f0395b03957039530994501939099350292f0292b029270292303e7f06e7e03e7d03e7703e7504e7304e7203d7703d7603d7504d6f04d6e04d6d06b7e06b7604b6e03b6604b5e04b5c04b560bb5402a7f02a7b02a7702a7302a6f02a6b02a6702a6302a5f02a5d02a5b02a5902a5702a5502a5302a5102a4902a350697f0697b06977069730496f0396b03967049630495f0495d0495b01959049570895504953019510894501939089350292f0292b029270292303e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6306d6203d61d856003c7e0ac7c03b7e0bb7c03b7603b7406b6e06b6603b5e03b5602a7f02a7d02a7b02a7902a7702a7502a7302a7102a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4902a350397f0897d0397b01979039770397503973019710696f0696b06967069630395f0395b03957039530894501939089350292f0292b029270292303d6f03d6e04d6d03c6e04c5603b6e03b6604b5e04b5602a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4902a350396f0396b03967039630495f0495b04957049530894501939089350292f0292b029270292303e7f03e7d04e7b04e7a03e7706e7603e75d867403d7f03d7e03d7d04d6f04d6e04d6d04c560ac5407b7e06b7604b6e03b6604b5e04b5c04b560bb5402a7f02a7b02a7702a7302a6f02a6b02a6702a6302a5f02a5d02a5b02a5902a5702a5502a5302a5102a4902a350797f0697b06977079730496f0396b03967049630495f0495d0495b01959049570d95504953019510b945019390b9350292f0292b0292702923db56fda56bd9567d756307b6e06b6604b5e03b5602a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4902a351296f0e96b129670e9631295f0e95b129570e9530b945019390b9350292f0292b029270292303e7f04e7e03e7d03d7b06d7a03d7903d7703d7603d7303d7103d6703d6603d6507c7f06c7703c6f03c6d03c670ac6503c5f03c5702b7f05b7b02b7705b7302b6f02b6d03b6b05b6902b6702b6503b6303b6102b5f03b5b02b5703b5302b4d02b4702b4505a7f07a7e05a7b05a7a05a7706a7605a7305a7203a6f03a6e03a6d03a6c03a6b03a6a05a6905a6803a6703a6605a6511a6403a6303a6203a6103a6003a5f03a5e03a5b03a5a03a5703a5603a5303a5202a4702a4602a450797f0697b06977079730396f0396d0396b01969039670996503963019610395f0395b03957039530894b099470593f0593d0293b0293709935059330592f0592d0592b01929059270992505923019210587f058770386f0386d03867058650385f038570583f0583d02837058350582f0582d05827058250581f0581703e7f06e7e03e7d03e7703e7504e7304e7203d7703d7603d7504d6f04d6e04d6d06c7f06c7704c6f03c6704c5f04c5d04c570ac5502b7f05b7b02b7705b7302b6f03b6b02b6704b6302b5f02b5d04b5b05b5902b5702b5504b5304b5102b4d02b4702b4505a7f06a7e05a7b05a7a05a7706a7605a7305a7204a6f04a6e03a6b03a6a03a6703a6604a6304a6204a5f04a5e04a5d04a5c04a5b04a5a05a5905a5804a5704a5605a5511a5404a5304a5204a5104a5002a4702a4602a450697f0697b06977069730496f0396b03967049630495f0495d0495b01959049570895504953019510894b089470593f0593d0293b0293708935059330592f0592d0592b01929059270892505923019210587f058770486f038670485f0485d04857058550583f0583d02837058350582f0582d05827058250581f0581703e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6306d6203d61d256003c7f0ac7d03c7703c7506c6f06c6703c5f03c5702b7f03b7e02b7d02b7c03b7b03b7902b7702b7503b7303b7205b7105b7002b6f05b6b02b6705b6302b5f03b5b02b5703b5302b4d02b4702b4503a7f03a7e05a7d11a7c03a7b03a7a03a7903a7803a7703a7603a7503a7403a7303a7205a7105a7005a6f06a6e05a6b05a6a05a6706a6605a6305a6203a5f03a5e03a5b03a5a03a5703a5603a5303a5202a4702a4602a450397f0897d0397b01979039770397503973019710696f0696b06967069630395f0395b03957039530894b089470593f0593d0293b0293708935059330592f0592d0592b01929059270892505923019210387f0587d03877038750586f058670385f038570583f0583d02837058350582f0582d05827058250581f0581703d6f03d6e04d6d03c6f03c6704c5f04c5702b6f03b6e03b6b02b6703b6303b6202b5f04b5b04b5a02b5704b5604b5302b4d02b4702b4503a6f03a6e03a6b03a6a03a6703a6603a6303a6204a5f04a5e04a5b04a5a04a5704a5604a5304a5202a4702a4602a450396f0396b03967039630495f0495b04957049530894b089470593f0593d0293b0293708935059330592f0592d0592b01929059270892505923019210386f038670485f048570583f0583d02837058350582f0582d05827058250581f0581703e7f03e7d04e7b04e7a03e7706e7603e75d267403d7f03d7e03d7d04d6f04d6e04d6d07c7f06c7704c6f03c6704c5f04c5d04c570ac5502b7f05b7b02b7705b7302b6f03b6b02b6704b6302b5f02b5d04b5b04b5a05b5905b5802b5704b5602b5502b5404b5304b5102b4d02b4702b4505a7f07a7e05a7b05a7a05a7706a7605a7305a7204a6f04a6e03a6b03a6a03a6703a6604a6304a6204a5f04a5e04a5d04a5c04a5b04a5a05a5905a5804a5704a5605a5511a5404a5304a5204a5104a5002a4702a4602a450797f0697b06977079730496f0396b03967049630495f0495d0495b01959049570e95504953019510894b0a9470593f0593d0293b029370e935059330592f0592d0592b01929059270e92505923019210587f058770486f038670485f0485d04857058550583f0583d02837058350582f0582d05827058250581f05817d556fd456bd3567d15630ac6f0ac670ac5f0ac5702b6f05b6b02b6705b6302b5f05b5b02b5705b5302b4d02b4702b4505a6f07a6e05a6b05a6a05a6706a6605a6305a6205a5f04a5e05a5b03a5a05a5703a5605a5304a5202a4702a4602a450e96f0e96b0e9670e9630e95f0e95b0e9570e9530a94b0a9470593f0593d0293b029370e935059330592f0592d0592b01929059270e92505923019210586f058670585f058570583f0583d02837058350582f0582d05827058250581f0581702d6f03d6b03d6903d6703d6303d6107c6f06c6703c5f03c5702b6f02b6e02b6b02b6a02b6702b6604b6304b6202b5f02b5e03b5b03b5a02b5702b5602b5302b5205b4b05b4a03b4703b4602a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4b02a4702a3b02a3902a3702a3302a310796f0696b06967079630395f0395b03957039530894b099470993f0993d0893b01939099370993508933019310292f0292b02927029230786f068670385f038570c83f0c83d0c8370c8350282f028270881f0981703e7f04e7e03e7d03d7b06d7a03d7903d7703d7603d7303d7103d6703d6603d6502c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b03c6a02c69cf46802c6702c6602c6502c6402c6303c6202c6103c6002c5f02c5e02c5b03c5a02c5903c5802c5702c5602c5303c5202c5104c5007b7f06b7703b6f03b6d03b670ab6503b5f03b5702b4f02b4e05b4d02a7f02a7b02a7702a7302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f02a5b02a5702a5302a3b02a3902a31af2300797f0697b06977079730396f0396d0396b01969039670996503963019610395f0395b03957039530294f0994d0294b01949029470294502943019410993d0893b09937099350292f0992d0292b0292702925029230787f068770386f0386d038670c8650385f038570284f0c84d02847028450c83d0a8350282f0b82d02827028250881f0981703d6f06d6e02d6b03d6704d6304d6206c6f06c6704c5f03c5702b6f02b6e03b6b03b6a02b6702b6602b6302b6202b5f02b5e02b5b02b5a02b5702b5604b5304b5205b4b05b4a04b4704b4602a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4b02a4702a3b02a3902a3702a3302a310696f0696b06967069630495f0395b03957049530894b089470893f0893d0893b01939089370893508933019310292f0292b02927029230686f068670485f038570f83f0f83d0f8370f8350282f028270881f0881703e7f06e7e03e7d03e7703e7504e7304e7203d7703d7603d7504d6f04d6e04d6d02c7f02c7e02c7b06c7a02c7906c7802c7702c7602c7306c7202c7107c7002c6f02c6e02c6b03c6a02c6702c6602c6304c6202c5f02c5e02c5d02c5c02c5b04c5a02c59cd45802c5702c5602c5502c5402c5304c5202c5104c5006b7f06b7704b6f03b6704b5f04b5d04b570ab5502b4f02b4e05b4d02a7f02a7b02a7702a7302a6f02a6b02a6702a6302a5f02a5d02a5b02a5902a5702a5502a5302a5102a3b02a3902a31ae2300697f0697b06977069730496f0396b03967049630495f0495d0495b01959049570895504953019510294f0894d0294b01949029470294502943019410893d0893b08937089350292f0892d0292b0292702925029230687f068770486f038670485f0485d048570f8550284f0f84d02847028450f83d0a8350282f0b82d02827028250881f0881703d6f03d6e03d6b03d6902d6703d6306d6203d61c956006c6f06c6703c5f03c5702b6f02b6e04b6b04b6a02b6702b6602b6302b6202b5f02b5e03b5b03b5a02b5702b5602b5302b5205b4b05b4a03b4703b4602a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4b02a4702a3b02a3902a3702a3302a310696f0696b06967069630395f0395b03957039530894b089470893f0893d0893b01939089370893508933019310292f0292b02927029230686f068670385f038570c83f0c83d0c8370c8350282f028270881f0881703e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6306d6203d61c856002c7f02c7e02c7d02c7c02c7b03c7a02c7903c7802c7702c7602c7502c7402c7303c7202c71cb47002c6f02c6e02c6b06c6a02c6702c6602c6306c6202c5f02c5e02c5b03c5a02c5702c5602c5303c5203b7f03b7e0ab7d0ab7c03b7703b7503b7206b6f06b6703b5f03b5702b4f02b4e05b4d02a7f02a7e02a7d02a7c02a7b02a7902a7702a7502a7303a7202a7105a7002a6f02a6b02a6702a6302a5f02a5b02a5702a5302a3b02a3902a31ac2300397f0897d0397b01979039770397503973019710696f0696b06967069630395f0395b03957039530294f0894d0294b01949029470294502943019410893d0893b08937089350292f0892d0292b0292702925029230387f0c87d03877038750686f068670385f038570284f0c84d02847028450c83d0a8350282f0b82d02827028250881f0881704c5f04c5a04c5704c5602b5f04b5b04b5a02b5702b5602b5305b4b03b4702a5f02a5b04a5a02a5702a5602a5302a4b02a4702a3b02a3702a330495f0495b04957049530894b089470893f0893b08937089330292f0292b02927029230485f048570c83f0c8370282f028270881f0881703d6f03d6e04d6d02c6f02c6e02c6b03c6a02c6903c6802c6702c6602c6303c6202c61c946002c5f02c5e02c5b04c5a02c5702c5602c5304c5203b6f03b6e03b6703b6204b5f04b5a04b5704b5602b4f02b4e05b4d02a6f02a6e02a6b02a6702a6303a6202a5f02a5b04a5a02a5702a5602a5302a3b02a3902a31ab2300396f0396b03967039630495f0495b04957049530294f0894d0294b01949029470294502943019410893d0893b08937089350292f0892d0292b0292702925029230386f038670485f048570284f0c84d02847028450c83d0a8350282f0b82d02827028250881f0881703d6f04d6b03d6702d6307c6f06c6704c5f03c5702b6f02b6e02b6b02b6a02b6702b6603b6303b6202b5f02b5e02b5b02b5a02b5702b5604b5304b5205b4b05b4a04b4704b4602a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4b02a4702a3b02a3902a3702a3302a310796f0696b06967079630495f0395b03957049531194d0894b0a9470a9451c93f0d93d0893b019391c9370d93508933019310292f0b92d0292b0292702925029230786f068670485f038571184d0a8451c83f1083d1c837108350282f0b82d02827028250881f0c01703d7e01d7a01d7603d7204d6e01d6a01d6604d6202c7e06c7a02c7607c7202c6e03c6a02c6604c6202c5e02c5d02c5c0dc5a02c590dc5802c5602c5502c540dc5202c511bc500ab5d0db5a0ab560ab550ab5402b4e05b4d02a5d0ba5a02a5905a5802a5602a5502a5402a5102a3902a310da300797e079720496e049620495e0495d0894d0294a0194901948029460294502944019410893d0893a0a936089350a9340892d0292a0292602925029241685d0d855bf04d028450d83d0a8350b82d028250881d0d81503d7e04d6e02c7e06c7a02c7607c7202c6e03c6a02c6604c6202c5e02c5d02c5c10c5a02c5910c5802c5602c5502c5416c5202c5119c500ab560ab5402b4e02a5d05a5a02a5905a5802a5602a5502a5402a5102a390d95d019590d955019511a94d0194902945019410a9350592d029250787e0486e0485e02846028440a83402826028241681603e7f03e7d04e7b04e7a03e7706e7603e75c867403d7f03d7e03d7d04d6f04d6e04d6d02c7f02c7e02c7b06c7a02c7906c7802c7702c7602c7307c7202c7107c7002c6f02c6e02c6b03c6a02c6903c6802c6702c6602c6304c6202c6104c6002c5f02c5e02c5d02c5c02c5b04c5a02c59c745802c5702c5602c5502c5402c5304c5202c5104c5007b7f06b7704b6f03b6704b5f04b5d04b5a04b5704b560ab550ab5402b4f02b4e05b4d02a7f02a7b02a7702a7302a6f02a6b02a6702a6302a5f02a5d02a5b04a5a02a5905a5802a5702a5602a5502a5402a5302a5102a3b02a3902a31a82300797f0697b06977079730496f0396b03967049630495f0495d0495b0195904957c615504953019510294fc314d0294b01949029470294502943019411193d0893b0a9370a9350292f0b92d0292b0292702925029230787f068770486f038670485f0485d04857c50550284fbe04d02847028451183d0a8350282f0b82d02827028250881f0b01703e7d04e7a06e7603e7508e7403d7e03d7d04d6e04d6d07c7e06c7a06c7607c7204c6e03c6a03c6604c6204c5e04c5d04c5c04c5a0dc590dc5804c5614c5514c5404c5204c5104c5004b5d04b5a04b560ab550ab5405b4d05b4502a5d04a5a02a5905a5802a5602a5502a5402a5101a4901a410797e079720496e049620495e0495d0495c019590895504952019510195002946029450893a0a9360292a029260485d1a8550a04dc20450881d0801508e7404c5c17c5810c5404c500ab5405a5802a541085409d6f08d6b08d67c256310c6f07c6e08c6b06c6a08c6706c6610c6307c6210c5f04c5e09c5b03c5a09c5703c5610c5304c5202a6f02a6b02a6702a6302a5f02a5b02a5702a5301a4b01a490196f0196b01967019630195f0195b019570195301947019450192b01927019230d84e0181609d6f08d6b08d67c356314c6f07c6e08c6b06c6a08c6706c660dc6307c6214c5f04c5e09c5b03c5a09c5703c560dc5304c520ab6f08b670ab5f09b5705b4f05b4d0ab4705b4502a6f02a6b02a6702a6302a5f02a5b02a5702a5301a4b01a4902a4702a4301a4102a3b02a370896fa116e0196b08967019630e9620995f8e15e0195b09957019530e9520294702946029450193b0a93a0a9370a9360292f0192b0292a0292702926019236606f088674f05f098570d84f0904d14847c10450282f028270181f0e81d018170701513c5c0dc580dc5410c50019480d9441085c0d814 20 1048575 8 255 11 2047 20 1048575
def cc_67_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x8888f06b4df4f13d32d7589ce58b1be59b58c869140c93218a502fe2d5ae9cb04b153d9a83c84e74093f211fd0218ce3c8d27031ccca7968e1270c241f846bb08b04e0f7d21611c186780061 0xf5bc09ad603d6700eb181f1bc0f8dc01c6700e31807188098be04c5e00e2b80714c038a407b6f035b3812d7c076ae0db4f055a6836d1c1568a07a6f02d3581a99c0b4c604a5f01d2d80e95c094a60da4f0152681692c0b4920da470152281690c0b48205a3b06d1b8065bc032d60196700cb180657c032b60195700ca980651c1b28c0194500c9d8064dc0325e0192b00c9380648c030de0186700c2f80615c0309e0184d00c238061140305e0182700c0f8060740302e0181501eb78135ac07ace04d6301e3780f1b80d8ce07c6301e3101317c098bc03c57026298131480f6de06b67025af80ed5c3369e0ab4d085a382ad140f4de05a6b0353381698c094be03a5b01d2b81294c2d49e02a4d02d258169242148e02a4502d218169040b476c523703cb78065ac0d2ce01963024af80656c072ae019530aca7bf85340329601949084a3880514032860194100c9d9e84dc0b25e0192b0d49380648c0f0de0786e0343381e188090be0485e01c2b8121480909e0484e024268320e86e06c0582f0641501609c5404c0181f0640d00605c3c02c03d6f01eb68135ac09ad403d67036b300f59602ac803c6f01e3700f1b4098be04c5e0262e81edbc0d6d606b6703db1812d7c076b603b57025a9812d3c0969a04b4b025a382ad140968607a6f0353581a99c0f4c604a5f01d2d80e95c094a604a4f0152681292c0b49204a470152281290c09482d723f6891db108dd604660796f034b581a59c0f2c60495f01cad80e55c092a60494f024a681252c03292049477f8a281250c032827e13f0449d9e44dc112667312f044959bc49c112460786f0343581a19c0f0c60485f01c2d80e15c090a60484f0242681212c0908efd045024218ec0fc1907636037064198b80bc19056290270641182207c190361d017044098075ac03ad407c6f0363581b19c0f8c609c5f01e2e84316c098b209c5701e2a84314c098a207a6f02d3581a99c0b4c60ba5f0152e81696c0b4b20ba570152a81694c0b4a20ba4f02d2582691c0b4860196f00cb580658c032be0195d00ca780652c0328e0194300c978064ac0324e0192306c2b00605803ad601d6a036b38075980fac607c6f0363581b19c0f8c609c5f01e2e83716c098b209c5701e2a85314c098a207b6f035b3822d7c0d6ba06b57035aa82ad3c1368e07a6f0353581a99c0f4c60ba5f0152e82e96c0b4b20ba570152a82e94c0b4a20ba4f04d2582691c174860aa3b0551b81e5bc0f2dc0196b034b380658c0f2c40795f03caf01e5741129e0194b044a380650c032760893a0449b82a4d81125e0192b0449380648c0f0de068670a42fbec1741b0ae1c0552982782611c1705e0b82700c0f8220740302e1b01503eb781f5b80f8de06c6b0363381f18c138be03c5d06e2d813164138ae03c5506e298131440f4de05a6b0353381698c174be02a5d02d2d816964174ae02a5502d298169441749e05a4b04d2381690c032d60196700cb180655c1b2ac0195500ca780652c0328e0194300c978064ac0324e0192303e3781b1ac0d8ce07c630662f80f174218b604c590662b80f1543b8a604c5103d378169ac0d4ce05a6305d2f80a9740b4b605a5905d2b80a9540b4a605a5105d2781692c1748e05a4303cb78065ac0d2ce019630acafbe4574032b601959084ab870554032a601951490a780652c1928e0194302c978064ac1724e0192303c3701e1783402c07c6f0363581b19c0f8c607c5f01e2e81f16c098b207c5701e2a81f14c098a206b6a035b381ad980d6ae06b56035aa82ad3c1568e07a6f0353581a99c0f4c607a5f0152e81e96c0b4b207a570152a81e94c0b4a20ba4f05d2582e91c174860aa3b0551b81e5bc0d2d60696703cb181e57c0f2ba0795b00cac81e55df42aa0795300ca8a4453c1129688147044a18224ec1526e0b92f0449582e49c112460786f0343381e17c0f0ba078577c02a94813c8a08e0b82f05c1382207c3202e06d6f036b581b59c0dac606c6e035b3012d78076ac06a6f0353581a99c0d4c611a5f05d2d84695c174a605a390151a81a5bc0d2d606967034b182257c112b608957044a98064e41126a0892f0449582249c1124606c6f01e3681b1ac098d206c6701e3281b18c098c206c5f0362d81b15c0d8a606b6f035b701edb40d6be06b5e035a902ad3c1568e06a6f0153681a9ac0b4d206a670153281a98c0b4c206a5f0352d81a95c0d4a60ba4f05d2582e91c174860aa3b0551b81a5bc112da0696b00cb481a59c0d2ca0696300cb081a57c0d2b606957034a982253c1129608947044a18224ec1126e0892f0449582249c112460686f07c3681a19c0d0ca0685f0342b83e13c1f08e0b82f05c1382207c1102e07d6f036b581b59c0fac606c6603db7012d78076ac07a6f0353581a99c0f4c611a5f05d2d84695c174a605a390151a81e5bc0d2d60696703cb184a57c112b612957044a98064e42526a0b92f0449584649c1124603d6f026b580f59c09ac610c6f03e370231ac0d8d408c670363304318c0f8c401c5b00e2d02e9bc0b4d608a6702d3181297c074b603a570252982e93c0549a05a4b02d2482e91c0548a05a4302d208065bc032d60196700cb180657c032b60195300ca78065340325e0192b00c9380648c1b08c0181601eb78135ac07ace04d6306e3781f1b8118d606c6a0463381b198298c607c6200e2d807168078ae01c560262982adbc116ce04b5f01dab826d3c0769a03b4701da282e9bc114d608a6705d3181297c074b603a570252982e93c0549a0ba4b02d2482e91c0548a0ba4302d2082a8ec1546e0896f00cb582259c032c60495f024af00656c072ae01953024a901253c0929c0494d00c9d8264e81326e0a93604c978064ac1324e019233503782219c090be038570a427bcc1341b08e1804505c1782e09c0303e0981d00c0b85c05407ade04d6b01eb381358c1b8de07c6e0463581b1a8118ce06c6606e3181f188098be04c5e05d378169ac114ce05a630252f80e96c074ae04a5305d2780a9340b49605a4905d2380a9140b48605a4100cb78065ac032ce0196300cad80655c032a60194706ca30065140325e0192b00c9380648c07ade04d6b01eb381358c218de07c6e07e3581b1a81f8ce06c660ce3181f188174de05a6b05d3381698c094be03a5b01d2b81294c1749e02a4d02d258169241748e02a4502d218169054a2de0196b07cb380658c092be0195b01cab80654c2b29ef114d00ca58065242128e1814500ca18065040b25e0192b05c9380648c090bc0484e0b00b00f5bc09ad603d67026b18131bc0f8dc04c6b0263501319c0d8cc04c630263102adbc156ce03b5a01dab80ed580768e03b4601da282e9bc174d60ba6705d3181297c074b603a570252981293c0549a04a4b02d2481291c0548a04a430252082a8ec1546ea416f04cb5a6c59c132c60495f01cad80e55c092a60494f024a681252c0329204947790a281250c032820993b0549b82e4bc132560b92704c919a41bcb80ce0485f01c2b81213c0909a048477802282e0bc1704e0981f0a80b80f5bc07ad603d6701eb180f1780f6dc06b6601dab0469bc174d611a6705d3180e97c074b603a5701d298168e40546a0996f04cb582659c132c60395f01cad80e55c072a60193904c9a8264bc132560992704c9180f5bc07adc03d6b036b500f59c07acc03d6303eb100f1bc078d603c6701e3182adbc156ce03b5f01daf012d740769e03b4e01da102e9bc174d60ba6705d3180e97c054ba03a5b01d2c80e95c054aa03a5302d2880e93c0749603a4701d2182a8ec1546e0996f04cb582659c132c60395f04cae80e56c032b20395701caa80e54c032a20394f01ca580e51c072860993b04c9b8264bc132560992704c918321bc190ce0385f0642e80e15c070aa0384f01c2382e0bc1704e0981f04c0b80f5bc09ad603d67026b180f1580f6dc06b66025af0469bc174d611a6705d3181297c074b603a57025298168e40546a1296f04cb584a59c132c60495f01cad80e55c092a6019390949a82e4bc132561192704c918175bc0badc01d6b00eb500759c03acc01d6300eb101f1bc0d8d606c6703e3182717c078ba10c5b0262c82715c078aa10c530262881edbc0d6ce0bb5f055ae82ed5c156aa0bb4f04da38069bc054d602a670153180697c034ba01a5b00d2c80a95c054aa01a5300d2880a93c0549602a470152180a8ec0546e0196f00cb580659c032c60195f00cae80655c032aa0195300ca780652c0328e0194300c9d8064dc0325e0192b00c9380648c030de0186700c2b836158030aa0184f00c238060bc0304e0181f00c0d00605c0302c05d6f02eb70075ac03ad406d6700eb301f58c0bac407c6f0363581b19c0f8c609c5f01e2e83716c098b209c5701e2a86314c098a207b6f035b581ad9c0f6c60bb5f055ae836d6c176ae0ab5506da982ed3c1369609b4706da180a9bc054d602a670153180a97c054ba02a5b00d2c80a95c054aa01a5300d2880a93c0549602a470152180a8fc0547602a370151981e5bc0f2dc0196b034b380658c0f2c40295f014af00a5741129e0194b044a380650c1127e0193b0449b8064cc0525e0192b0149500a49c0524c0192303c378061ac0d0ce018630bc2fbac174030b60d8570a02a80614ca209e0184b04c2380610c1b07e0183b05c1b8060cc0505e0182b0141380608c0303e0881d00c0d80605c2602a0181303eb781f5b803ace01d6300eb101f1bc0d8d606c6703e3182717c078ba0dc5b0262c82715c078aa0dc530262881edbc0d6ce0bb5f055ae82ed5c156aa0bb4f04da38069bc054d602a670153180697c034ba01a5b0152b80a9540549e02a4b0152380a90c0547602a3700cb78065ac032ce0196300cab836558032aa0194f00ca580651c032860193b00c9b8064bc032560192700c918061bc030ce0185f00c2e80615c030aa0184f00c238060bc0304e0181f00c0e80605c0302a05d6f02eb701759c0bac605d6203e3781b1ac0d8ce07c630662f80f174218b604c590662b80f154278a604c5103db781ad9c176be0ab5d05dab82ad541769e0bb470153780a9ac054ce02a630152f80a974054b602a570152a80a93c0549602a470152180a8ec0546e0796f00cb581a59c032c61395f748ae80656c032b2109570a0aa80654c032a29014f00ca583251c032860193b05c9b80a4bc032560292700c918161bc0f0dc0586702c3100a17c050bc0285d02c2781611c0505e0282a0141380a0980303e0581a00c0b84805805ade05d6e016b681f1bc0d8d606c6703e3180b17c058ba02c5b0262c80b15c078aa02c530162881edbc0d6d606b6703db180ad7c056ba02b5b015ab82ad54056a60bb4f08da582ed1c2368602a6b0353500a9a4054ce02a660153180a984054ae02a560152a80a93c0549602a470152180a8fc0547602a370151981e5bc0d2d60696703cb180a57c052ba0295b00cac80a55dd42aa0295300ca8a3c53c1129686147044a18464fc112760b9370449980a4bc05256029270149181e1bc0b0d60686702c3180a17c050ba0285b0142bba0154050a65004f02c2590c11c0b0861183f02c1d82e0dc0b0660282f0141580a09c050460881f02c0d84405c0b02606d6f036b581b59c0dac606c6f0363581b19c0d8c60bc5f05e2d82f15c178a602b6f035b700adb4056ce02b6502db1816d88056be05b5b015ab816d4c0569e05b4b015a3816d0c054ce02a660153281697c094bc05a5b01d2d01695c074ac05a530252901693c0b49605a4a02d2382a9180b48605a3f02d1f0168f40d2de0696b034b381a58c112be0895b044ab82254c1129e0894b044a382250c0b27e0293b0149b8164cc0b25e0592d02c958064a40b24e0892502c918064840b0de0586b02c3381618c0b0be0585b02c2b81614c0b09e0584b02c2381610c0b07e0283b0141b8160cc0b05e0582d02c1581609c0b04a0582302c0f81606c0b02e05813016b780b5b80bada02c6f01e3680b1ac058d202c670163280b18c098c206c5f0362d81b15c0d8a602b6f055b680adac056ce02b65015b181ad7c0d6b606b57035a982ed3c236960bb4708da180a9bc054dc02a6d0152f80a978054b602a590152981a948054a202a4f0152580a91c0548602a3f0151d80a8dc054660296f044b680a5ac032d202967014b280a58c032c20695f034ad81a55c0d2a60894f044a582251c112860893f0449d8224dc112660292f0149580a49c052460286f07c3680a1ac050ce028650143181a17c0b0b60685702c2983e13c0b0960f84702c2183e0fc0b0760b83702c1980a0bc05056028270141182207c0b0360881702c0981f5bc0dad606d6703eb181f1bc0d8d606c6703e3182f17c178b60bc5705e2980adbc056da05b6b02db500ad9c0d6cc02b65015af816d6c056ae05b53015a7816d2c0568e05b430153780a9b8054da05a5f0252f01696c074b405a5701d2b01694c094a405a4f02d258169280b48e0aa4602d218168fc0b47c05a3d03cb781a5ac0d2ce07963074af82256c1d2ae0895305ca782252c1728e0894302c9f80a4ec0526e0593302c978164b40b2560192902c9383a4940b2460192102c378161ac0b0ce0586302c2f81616c0b0ae0585302c2781612c0b08e0584302c1f80a0ec0506e0583302c178160b40b0560582702c1281608c0b03e0581b02c0b81604c07ade04d6b01eb381358c218de07c6e0463581b1a8118ce06c660863181f188098be04c5e00e2d807168038ae01c5600e29807148176de08b67025af80ed5c1769e0ab4d05da382ad14054de02a6b0153380a98c034be02a5b0152b80a94c0349e01a4d00d258069240548e02a4500d218069040547602a3700cb78065ac032ce0196300caf80656c032ae0195300ca78065340328e0194500ca18064ec0326e0192f00c9580649c032460186f00c3380617c030ae0184706c230061140305e0182700c0f8060680302e0181601eb78135ac07ace04d6306e3781f1b8118d606c6a0463381b198318c607c620262f813178038b601c5a01e2b807158098a604c5205db7822dac116ce0db63025af80ed6c076ae04b5305da782ad341b6960bb47055a2836d0c054de02a6b0153380a98c054be02a5b0152b80a94c0549e02a4d015258069240548e02a4500d218069040547e02a3b0151b80a8cc112de0196b044b380658c092be0495e00cad80e55c032a604952014a780a5380529a0993f00c9d8264dc032660292f00c9580a4a80524e0292600c919a01bc030d60886700c3181217c030b60385700c2985e13dc609a0184b06c23840114030860d83f00c1d82e0dc030660282f00c1580a09c030460181f04c0e80606c0302e0f01500c0980f5bc09ad603d67026b18371bc0f8dc08c6b0363502319c0d8cc0dc6303e3101317c098bc01c5700e29807148176de08b67025af80ed5c1769e0ab4d05da382ad14054de02a6b0153380a98c034be02a5b0152b80a94c0349e01a4d00d2580a91c0548a02a3b0151b8065bc032d60196700cb180657c032b60195700ca980651c1b28c0194500c9d8064dc0325e0192b00c9380648c030de0186700c2f80615c0309e0184d00c238061140305e0182700c0f8060740302e0181501eb78135ac07ace04d630863781f1b81f8d606c6a07e3381b198278c607c620262f813178078ae04c530262902edbc176ce04b5f01dab82ed3c1569a0bb47055a280a9bc054d602a670153180a97c054b602a570152980a93c0549a02a4b0152380a9140547602a37518b78065ac1f2ce01963024af80656c072ae0195309ca7b845340329601949084a3840514032860194100c9d82e4dc0525e0192b0149380648c0b0de058670242f812178070ae048520142780a1380509a0282f0141500a09c0504c0181f02c0d00605c1c02c03d6f026b580f59c09ac602c6f03e3700b1ac058d402c670363300b18c058c402c5f0262f00b174176de11b6b05db3846d8c096be03b5b01dab812d4c0569e02b4d015a580ad1c1568a02b430153780a9ac054ce02a630152d80e968054b202a570152b00a94c054a202a470152300a9140547e02a3b0151b80a8cd442de0996b4c8b382658c092be0395b01cab81254c0529e0294d014a58065240528ee2145014a18065042327e0993b05c9b8264cc0525e0292b0149380a48cce0de0586b2d03381618c090be0385b01c2b81214c0509e0284d0142580a11dc008a0284308c1f8160ec1706e058330141780a0ac0504e0282304c0f81606c1a02e05813 19 524287 7 127 11 2047 21 2097151
def cc_67_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x1b9c2ac613db1176ec6d9c006d 0x7ade04d6e01eb680f1ac0d8d403c6901e3380f198078c603c6101e2b80f158078aa07b6f035b581ad9c0f6c603b5f01dae80ed6c076ae0ab5501da980ed3c0769603b4701da181e9bc0d4d606a6703d3180e97c054ba03a5b02d2c80e95c054aa03a5301d2880e93c0749603a4701d21b6c8fdaa476ce2375c11981e5bc0d2d60696703cb180e57c072ba0395b00cac80e55c132aa0395300ca880e53c072960394701ca18264fc1127609937044998264bc11256099270449181e1bc0d0d60686703c3180e17c070ba0385b01c2b832154070a60384f01c2580e11c070860c83f0641d8320dc190660c82f0641583209c190460881f04c0d82605c1102603d6f036b700f5b407ace03d65026b1813588078ce03c6601e3281317c098bc04c5d035b781adac0d6ce06b63025af80ed6c076ae04b53025a7812d340969604b47055a2812d0c0d4de06a6b0353381a98c094be03a5b01d2b81294c0949e02a4d025258169240948e02a4502521812905b447ed423b6611bad88cc0d2de0696b034b381a58c092be0395b01cab81254c0929e0494d024a58065240928e08945024a18065041127e0893b0449b8224cc1125e0892b0449382248c0d0de0686b0343381a18c090be0385b01c2b81214c0909e0484d0242581211c1f08a0484307c1f8320ec1f06e0c83307c178320ac1f04e0c8230440f82206c1102e0881301eb780f5b809ada03c6f01e3700f1b4078be03c5e01e2d80f164078a606c5201e28c05140076de0ab6d01db580ed9c076ca03b63035af81ad6c0d6ae06b5301da780ed2c0768e03b4301d3780a9b4074d603a6901d3380a994074c605a610352f81a96c0d4ae06a5301d2780e92c0748e03a436c91fb4c8ed9446eb423301cb78225b4072d60196901cb380e594072c601961034af81a56c0d2ae0695301ca780e52c0728e039430449f8224ec1126e08933044978224ac1124e0892301c378321b4070d60386701c3280e18c0d0be0685b0342b81a14c0709e0384b01c2380e10c1907e0c83b0641b8320cc1905e0c82b0641383208c1103e0881b0440b82204c078be03c5e0262e80ed7c076b603b5701da9812d3c0969604b47025a180e97c074b603a5701d2981293c0949604a4702521b608fda4476c82375991980e57c072b60395701ca981253c0929604947024a18224fc1127608937044998224bc11256089270449180e17c070b60385701c2981213c0909604847024218320fc190760c837064198320bc190560c8270641182207c11036088170440980f5bc09ad603d6700eb181f1bc0f8dc01c6b00e3500719c038cc01c6300e3101317c098bc01c5b00e2d00715c038ac01c5300e2901edbc0d6ce04b5f01dab842d3c1569a10b47055a281e9bc0b4d606a6702d3181297c074b603a570252984293c0549a05a4b02d2484291c0548a05a4302d208168ec2d46e0196f00cb580659c032c60195f00cad80655c032a60194f00ca680651c0328a0194300c9d8064dc0325e0192b00c9380648c030de0186700c2f80615c0308e0d84600c228060bc0304e0181f00c0d00605c0302c03d6f026b580f59c09ac603c6f01e370071ac038d406c6700e3301f18c078c404c5f0262f00716c038b403c5700e2b01314c098a407b6f035b581ad9c0f6c604b5f01dad80ed5c096a60db4f055a6836d2c1b68e0ab4506da181e9bc0d4d606a6703d3181297c074b603a570252986e93c0549a0da4b02d2483691c0548a0ea4302d208368fc1d476c623706d1981e5bc0f2dc0196b034b380658c0f2c40495f024af00656c072ae01953024a901253c0929c0494d0449f8064ec11274089373d89b0064cc1125e0192b0449502249ce024c0192303c378061ac0d0ce018630242f80616c070ae018530bc27c00134030960d8471002280610c1b07e0183b1c01b8060cc1d05e0182b1581380608c0303e0881d00c0d80605c3e02a01813 17 131071 7 127 11 2047 21 2097151
def cur_67 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_67_8 (Nat.sub p 256)) (cc_67_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_67_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_67_5 (Nat.sub p 160)) (cc_67_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_67_3 (Nat.sub p 96)) (cc_67_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_67_1 (Nat.sub p 32)) (cc_67_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)
def f_67 : Nat → Nat × Nat := unpackForestF 0xc5f00c5b00c577ed648004d7e9457f14d7e84500c537d85d7c1557c95d7c05500b5f00b5b00b5700b537984d781457894d7804500b4f00b4b00b4700b437585d741557495d7405500a5f00a5b00a5700a537184d701457094d7004500a4f00a4b00a4700a436bd6f6bd6b6bd676c6746bd6300a3f68d6f68d6b68d676967468d6300a3b67c685dd6f66c585dd6b65c705dd6764c6062e7462c5862955628555dd6360d6361563608455d94d5f9555e5635ed635e1455d84d00a375ca6453d6f5ba5453d6b5aa7c53d6758e745956458a5453d635445f5445b56a6c5445754d645545454a445445353b4400a33528454fb4f518454fa4f5014c5004d4fa370095f0095b4e47c4bb4f4d47c4ba4f4c4704ba37009574a0184a01400953490654636f480654626f4694c4684d462370094f0094b44d684236f43d684226f42c6042237009474081840814009433fb543f5630093f0093b3d1543d0553cd63009373b13c3b134009333a25439d630092f0092b3815437d63009273614c3614400923351453034f341453024f3294d3284c3023731a373014f30137301270085f0085b2ec7c2c34f2dc7c2c24f2cc702c237008572a82c2a824008532996524b6f2896524a6f2714d2704c24a37262372496f24937249270084f0084b2356820b6f2256820a6f2146020a37008471f02c1f024008431e3541dd630083f0083b1b9551b8541a5631a16f1a15f008371883c188340083317a54175630082f0082b151551505413d631396f1395f008271204c12044008230081f0081b0f2540f1540f054025630d2640d1640d0640246f0b2540b1540b0540245f0926409164090640236f0725407154070540235f0656802e730556302a5c045630295c035630285c023470081701124008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV4 fullMask g_67 ep_67 261 bds_67 (dagTraceF fullMask rootStock 11 f_67) (cur_67 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_8 : treeBlockF 256 261 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
theorem nj_67_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_67_1 h1 h2)
theorem nj_67_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_1 (fun _ h1 h2 => treeBlockF_at nb_67_2 h1 h2)
theorem nj_67_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_2 (fun _ h1 h2 => treeBlockF_at nb_67_3 h1 h2)
theorem nj_67_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_3 (fun _ h1 h2 => treeBlockF_at nb_67_4 h1 h2)
theorem nj_67_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_4 (fun _ h1 h2 => treeBlockF_at nb_67_5 h1 h2)
theorem nj_67_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_5 (fun _ h1 h2 => treeBlockF_at nb_67_6 h1 h2)
theorem nj_67_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_6 (fun _ h1 h2 => treeBlockF_at nb_67_7 h1 h2)
theorem nj_67_8 : ∀ i, 0 ≤ i → i < 261 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_7 (fun _ h1 h2 => treeBlockF_at nb_67_8 h1 h2)
theorem nc_67 : ∀ i, 0 ≤ i → i < 261 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 261 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := nj_67_8
theorem lb_67 : LowerBin fullMask rootStock g_67 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_67 kn_67 sub_67 gl_67 rc_67 nc_67

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3901284352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3901284352)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3901284352) = g_67 by decide]
  exact lb_67

end PEqualNP.Outside.L_meta_49181

theorem PEqualNP.Outside.L_meta_49181 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3901284352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3901284352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49181.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3901284352) 13 PEqualNP.Outside.L_meta_49181.root_lb PEqualNP.Outside.L_meta_49181.wg 18 rfl PEqualNP.Outside.L_meta_49181.wfits PEqualNP.Outside.L_meta_49181.weval
