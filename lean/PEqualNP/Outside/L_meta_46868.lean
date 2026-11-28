import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46868

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

def m_0 : Nat := 0x404040404040404
def s_0 : List Nat := [0x4000400040004, 0x40400000404, 0x4040404]
def g_0 : Nat := 0x400040404
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

def m_1 : Nat := 0x44004400440044
def s_1 : List Nat := [0x4000400040004, 0x4400000044, 0x440044]
def g_1 : Nat := 0x400040044
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

def m_2 : Nat := 0x444400004444
def s_2 : List Nat := [0x40400000404, 0x4400000044, 0x4444]
def g_2 : Nat := 0x400000444
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

def m_3 : Nat := 0x44444444
def s_3 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_3 : Nat := 0x40444
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

def m_4 : Nat := 0x4444444444444444
def s_4 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_4 : Nat := 0x400040444
def bds_4 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
theorem kn_4 : KnownBin bds_4 := by
  intro b hb; simp only [bds_4, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_1
  · exact lb_2
  · exact lb_3
theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by intro b hb; simp only [bds_4, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_4, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_4 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_4 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsF m_4 g_4 bds_4 (dagRefF 43 (dagTraceF m_4 s_4 6 f_4) l_4 0) s_4 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4_0 : treeBlockF 0 32 (dagCheckNodeF m_4 g_4 bds_4 43 (dagTraceF m_4 s_4 6 f_4) l_4) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4_1 : treeBlockF 32 43 (dagCheckNodeF m_4 g_4 bds_4 43 (dagTraceF m_4 s_4 6 f_4) l_4) = true := by decide +kernel
theorem nj_4_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_4 g_4 bds_4 43 (dagTraceF m_4 s_4 6 f_4) l_4) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_4_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_4_1 h1 h2)
theorem nc_4 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_4 g_4 bds_4 43 (dagTraceF m_4 s_4 6 f_4) l_4) i = true := nj_4_1
theorem lb_4 : LowerBin m_4 s_4 g_4 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0x5050505050505050
def s_5 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_5 : Nat := 0x10101010101050
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def f_5 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_5 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsF m_5 g_5 bds_5 (dagRefF 64 (dagTraceF m_5 s_5 5 f_5) l_5 0) s_5 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5_0 : treeBlockF 0 32 (dagCheckNodeF m_5 g_5 bds_5 64 (dagTraceF m_5 s_5 5 f_5) l_5) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5_1 : treeBlockF 32 64 (dagCheckNodeF m_5 g_5 bds_5 64 (dagTraceF m_5 s_5 5 f_5) l_5) = true := by decide +kernel
theorem nj_5_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_5 g_5 bds_5 64 (dagTraceF m_5 s_5 5 f_5) l_5) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_5_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_5_1 h1 h2)
theorem nc_5 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_5 g_5 bds_5 64 (dagTraceF m_5 s_5 5 f_5) l_5) i = true := nj_5_1
theorem lb_5 : LowerBin m_5 s_5 g_5 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x505050505050505
def s_6 : List Nat := [0x101010101010101, 0x5000500050005, 0x50500000505, 0x5050505]
def g_6 : Nat := 0x101010501050505
def bds_6 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_6 : KnownBin bds_6 := by
  intro b hb; simp only [bds_6, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by intro b hb; simp only [bds_6, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_6, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_6 : Nat → Nat × Nat := fun _ => (0, 0)
def l_6 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsF m_6 g_6 bds_6 (dagRefF 0 (dagTraceF m_6 s_6 4 f_6) l_6 0) s_6 4 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_6 g_6 bds_6 0 (dagTraceF m_6 s_6 4 f_6) l_6 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_6 : LowerBin m_6 s_6 g_6 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0xc0c0c0c0c0c0c0c
def s_7 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_7 : Nat := 0x400040404
def bds_7 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_7 : KnownBin bds_7 := by
  intro b hb; simp only [bds_7, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by intro b hb; simp only [bds_7, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_7, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_7 : Nat → Nat × Nat := fun _ => (0, 0)
def l_7 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsF m_7 g_7 bds_7 (dagRefF 0 (dagTraceF m_7 s_7 4 f_7) l_7 0) s_7 4 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_7 g_7 bds_7 0 (dagTraceF m_7 s_7 4 f_7) l_7 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_7 : LowerBin m_7 s_7 g_7 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x5500550055005500
def s_8 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_8 : Nat := 0x100110011001500
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def f_8 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_8 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsF m_8 g_8 bds_8 (dagRefF 64 (dagTraceF m_8 s_8 5 f_8) l_8 0) s_8 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8_0 : treeBlockF 0 32 (dagCheckNodeF m_8 g_8 bds_8 64 (dagTraceF m_8 s_8 5 f_8) l_8) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8_1 : treeBlockF 32 64 (dagCheckNodeF m_8 g_8 bds_8 64 (dagTraceF m_8 s_8 5 f_8) l_8) = true := by decide +kernel
theorem nj_8_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_8 g_8 bds_8 64 (dagTraceF m_8 s_8 5 f_8) l_8) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_8_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_8_1 h1 h2)
theorem nc_8 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_8 g_8 bds_8 64 (dagTraceF m_8 s_8 5 f_8) l_8) i = true := nj_8_1
theorem lb_8 : LowerBin m_8 s_8 g_8 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0x55005500550055
def s_9 : List Nat := [0x11001100110011, 0x5000500050005, 0x5500000055, 0x550055]
def g_9 : Nat := 0x11001500150055
def bds_9 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_9 : KnownBin bds_9 := by
  intro b hb; simp only [bds_9, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by intro b hb; simp only [bds_9, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_9, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_9 : Nat → Nat × Nat := fun _ => (0, 0)
def l_9 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsF m_9 g_9 bds_9 (dagRefF 0 (dagTraceF m_9 s_9 4 f_9) l_9 0) s_9 4 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_9 g_9 bds_9 0 (dagTraceF m_9 s_9 4 f_9) l_9 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_9 : LowerBin m_9 s_9 g_9 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0xcc00cc00cc00cc
def s_10 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_10 : Nat := 0x400040044
def bds_10 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_10 : KnownBin bds_10 := by
  intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_10, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_10 : Nat → Nat × Nat := fun _ => (0, 0)
def l_10 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 0 (dagTraceF m_10 s_10 4 f_10) l_10 0) s_10 4 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_10 g_10 bds_10 0 (dagTraceF m_10 s_10 4 f_10) l_10 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_10 : LowerBin m_10 s_10 g_10 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0xf000f000f000f
def s_11 : List Nat := [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f]
def g_11 : Nat := 0x1000500050007
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def f_11 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
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

def m_12 : Nat := 0x5555000055550000
def s_12 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_12 : Nat := 0x111000011150000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def f_12 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
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

def m_13 : Nat := 0x555500005555
def s_13 : List Nat := [0x111100001111, 0x50500000505, 0x5500000055, 0x5555]
def g_13 : Nat := 0x111500001555
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
def l_13 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 0 (dagTraceF m_13 s_13 4 f_13) l_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_13 g_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) l_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xcccc0000cccc
def s_14 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_14 : Nat := 0x400000444
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
def l_14 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 0 (dagTraceF m_14 s_14 4 f_14) l_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_14 g_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) l_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xf0f00000f0f
def s_15 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_15 : Nat := 0x10500000507
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def f_15 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
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

def m_16 : Nat := 0xff000000ff
def s_16 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_16 : Nat := 0x1500000057
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

def m_17 : Nat := 0x5555555500000000
def s_17 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_17 : Nat := 0x111111500000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def f_17 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_17 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
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

def m_18 : Nat := 0x55555555
def s_18 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_18 : Nat := 0x11151555
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
def l_18 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 0 (dagTraceF m_18 s_18 4 f_18) l_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_18 g_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) l_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xcccccccc
def s_19 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_19 : Nat := 0x40444
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
def l_19 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 0 (dagTraceF m_19 s_19 4 f_19) l_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_19 g_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) l_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xf0f0f0f
def s_20 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_20 : Nat := 0x1050507
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_20 : KnownBin bds_20 := by intro b hb; simp [bds_20] at hb
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp [bds_20] at hb
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_20] at hb
def f_20 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_20 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 64 (dagTraceF m_20 s_20 5 f_20) l_20 0) s_20 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_0 : treeBlockF 0 32 (dagCheckNodeF m_20 g_20 bds_20 64 (dagTraceF m_20 s_20 5 f_20) l_20) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_1 : treeBlockF 32 64 (dagCheckNodeF m_20 g_20 bds_20 64 (dagTraceF m_20 s_20 5 f_20) l_20) = true := by decide +kernel
theorem nj_20_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_20 g_20 bds_20 64 (dagTraceF m_20 s_20 5 f_20) l_20) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_20_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_20_1 h1 h2)
theorem nc_20 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_20 g_20 bds_20 64 (dagTraceF m_20 s_20 5 f_20) l_20) i = true := nj_20_1
theorem lb_20 : LowerBin m_20 s_20 g_20 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xff00ff
def s_21 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_21 : Nat := 0x150057
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_21 : KnownBin bds_21 := by intro b hb; simp [bds_21] at hb
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp [bds_21] at hb
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_21] at hb
def f_21 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_21 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 64 (dagTraceF m_21 s_21 5 f_21) l_21 0) s_21 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 (dagCheckNodeF m_21 g_21 bds_21 64 (dagTraceF m_21 s_21 5 f_21) l_21) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 64 (dagCheckNodeF m_21 g_21 bds_21 64 (dagTraceF m_21 s_21 5 f_21) l_21) = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_21 g_21 bds_21 64 (dagTraceF m_21 s_21 5 f_21) l_21) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_21 g_21 bds_21 64 (dagTraceF m_21 s_21 5 f_21) l_21) i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xffff
def s_22 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_22 : Nat := 0x1557
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

def m_23 : Nat := 0x5555555555555555
def s_23 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_23 : Nat := 0x111111511151555
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 7, g_4), (m_5, s_5, 6, g_5), (m_8, s_8, 6, g_8), (m_12, s_12, 6, g_12), (m_17, s_17, 6, g_17), (m_6, s_6, 5, g_6), (m_9, s_9, 5, g_9), (m_13, s_13, 5, g_13), (m_18, s_18, 5, g_18)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_5
  · exact lb_8
  · exact lb_12
  · exact lb_17
  · exact lb_6
  · exact lb_9
  · exact lb_13
  · exact lb_18
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_23 : Nat → Nat × Nat := unpackForestF 0x63714dc5279d4212710ddb50551c4273940b47105c01f 4 10
def l_23 : Nat → Nat → Option Nat := unpackLinksF 0x3cf1d3a30d9b1464c882e4701 0x205d427811e750849db50551ce502d1f237b4de92770dd027105c01f 7 3 10 4 4
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 13 (dagTraceF m_23 s_23 8 f_23) l_23 0) s_23 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 13 (dagCheckNodeF m_23 g_23 bds_23 13 (dagTraceF m_23 s_23 8 f_23) l_23) = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 13 → (dagCheckNodeF m_23 g_23 bds_23 13 (dagTraceF m_23 s_23 8 f_23) l_23) i = true := fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xcccccccccccccccc
def s_24 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_24 : Nat := 0x400040444
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 7, g_4)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 7 f_24) l_24 0) s_24 7 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 7 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0x3333333333333333
def s_25 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_25 : Nat := 0x111111111111113
def bds_25 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_25 : KnownBin bds_25 := by intro b hb; simp [bds_25] at hb
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp [bds_25] at hb
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_25] at hb
def f_25 : Nat → Nat × Nat := unpackForestF 0xa3a49348e53291ca052384ca470814749168e8a4d20a4ca414814821329042051d145a3a0934769328ed2051d94ca3b281474114005a7d11c5ea238bb446d5a88da7518928a312494620a28c412511a39a2346b4564f28ac9a515818a2b0294464e688c9ad1283ca2506944a0b289412511839a2306a002d2e7fda74ffb499ff4bd3fe9767fd2e4ffa529ff4a3434d3a7fd2850b95ca172a13fe57a7fcaecff95ca124b94249427fca94ff951a0f69d3fe542828ae505150a0a0b94141427fc2f4ff85d9ff0b940697280d2850195ca032a13fe14a7fc28d0034e9ff0a0002d1e7e9ae4fd2509fa2a13f41427262b4fc35c9c98ab392d7a725aece4b4e9c969b3928ea7251cce4a389c946d3928d67a9a54f59409eb0813d4d1a7251a4f3a389e74693924ea7249cce49389e22513c44927249b4e49359dc6953ba502774204ee3469c92693ae8e275d1a4eb9389d72693920ea7241cce48389d02513a0492740144e80249c906d3920d6729a54e59409cb081394d1a7241a000b439b669338657270ca84e185c9c30a136cd166d8a4cdeb4c9bd68137a1326f4204db1459b609336ed326dda04db94c9b728136c11400527ccfb5e99f6bb33e95a6b89c4d71349ae07135c0d267d274cfa4699f47d34e53269ca24d38189a702933e4a667c92cd084c9a10893420b2684124cf82999f04a00292e5e9af4bd35d97a6b92f4d4a5e9a8ccc23697a6a132c9425e9274bd2499924b93249425e8af4bd15d97a2b931ad72635a84bd15297a2a331493a5e8a84c2a5c9854a130a172614284bd05e97a0bb2f41725f9ae4bf35097e2b92fc5425e8294bd05197b49d2f414000523cbab509754b92ea5425d4284a1b569734b9286d5650d2f4a1a5d94349d28693650d264a1a4694348b2d25025a4204b3a4696746528691250d1f4b224494347b2c2932585224a192a9432532864a2570a64ae14494324d286496559254aba409570812ac91a50c924a8a4c9514892a24a2544924a182a9430532860a2528a64a514494a03129405250c134a182594449528a902514204a224694304800290e4322d49f25093e2a127c1424322b48635e9382712704d24e01c49c03490c6b5218d5a4c89c4991349320712640d2431a948625e92d48925a4924b41248625290c2752184e649927493a3492704924c90a4309c48613690c26b23ed2a480a049004091f68d2184d24709c48e13490c0752180e64592748ba3491724922c90a4301c4898289130492180da4301ac86b4a90e28121c102435a348603400147f18b17a41da248394490708918b14a315ad4813509022a1204142315ab47f9388ff07118ad3a3f0a247e0448c569b18a97a3d89447b1248f60511ec0923152d462a568f02511e04923c0144780248c54a518a91a3151f46292a8c52531cad3a3a11a4740348e56851cc0d23951ec629288c524d18a4963712546fa408df0811b891a3741446e23e8c52491b24a23649246282a8c50531a2d3a3511a46a1348d16851a44d23451ec628288ce03119c052314134628258c6495192902324204632468c705118c8fa31412000a3b89a8bd13516a2f1ae45e25c8bc2b91785422f02e45e05089a8ad16e4e22dc9a45b8388b706913514a2d5a644d35a8b06a11609422c0a845805089a6ad15c9322692d454b508a94a11525422a42844d2568a625114c0a22691f4519288a30511348e62802445004489a29b134506270a444e14489a09b1341040051bc4c2448508bd128d12250a244a0448508a5124912141af44734488e26911c0d2141a944624c85068d114932141a2c3db4e88626910c0d21eda14419288830510f68fa2009a44003487b47b0fc0d21ec9ec3e13487b07b0a0d121412f43c3448504b50dad421b52843a24086d4690da5721c51a43695086d0b90dc8d21b4284282568664990cc8f2198944331248660510cc0921412942824e8622890c411214126c2823e85d6890ba4d21741a42823d8586890b48d21600c42c0148502530a0496149a242a2348520590a409214014c2802500146707ad261292e42525084a0b90941420f5a2c1ea498446b9088d421102e42205083d48b07a1260f9a641f34083e49907c9020f42280094f8264bd04c976098ab41aa3883546906a0e20d41a41314e82628d05e9320bd2241782882f04904c4fa0989b41312e8280990501120a01e41403482603304c054004a5c0035e8006bb000d72001a940035181f26d000d420712e40e2508004bd0009760012e40bb5c8176a100094a00128c0a1268004a1022942044a840014e80029301697202d2840595c80b2a100017a0002ec0005c8046b9008d420112e4022508000a5000146004a740005000128eff6d41fed283fd95c7fb0a0f90959fe4ae3e42557c82bcf90575f20a73e414d7c8298f90519f20a2bf79407ef080fda519fb4993e41447c827cfd2531fa4a23e413d7c8278f904d9f90a63f21447c826afc2901f84203ef9467df244f904d1f20973ed9447db268f904b5f58a63eb1447d6278fac4d1f200d3e40197c8030f9e131f3c223e783c7cf068f90059f200abe494a7ca480f94501f24a33e4014001286f09169f0d283e19507c30a0f09159e11af3dea387bd468f7a0e1ef41a3c235a7846acf6e8e1edd1a3db8387b7068f08d49ed0943da028784492f08905e111d3c22397af24cf088e1e111b3d623078446af48929ea0a03d40407a448cf4a4a1e94143d223e784468f444a1e10af3cd23879f250f34511e74943cd12479b250f34051e10a93cba38797468f080e9e101cbc894e792268f24491e44a13c203878e250f1c491e101b3c2035785694f12501e24203c2b46787030f0a4e5e1498bc203400127ee61179dfda23bfa4477f088e61149df1223be04473069ae60d15cc12d3bb3507764a0eec141cc12b3b9a38773070e60939dc1a23b804473049ae60579da89e3b513476a030ed4051cc0ad398156764278ec84d1d900c3b20147302a4e60519d85a239813e73027aeacd39d709a3ae034756684eb24d1d641a3ab23d757068eac4f5cc09e39813673026ae96529d3d203a794074f080e96519d34143a593e74b244e604d1cc0973a393c747268e60069cc00cb9e34e742468e844d1cf1a13a013473c47ae788d5cf51a39e13d730030e720f1ce41a39801673002ae62529cd12039a14073128ce644a1cc49f398014001276e01179c022d393b5c7274b8e4e941c9cae39385c7270a0e01159c891c391234722070e440d1c022939034c7006b4e36d41c6d2838d95071b0a0e00d59c601c38c03470049ae00905c509438a028700472e24931c0118b8814c7002b4e16d41c2d2838595070b0a0e00559c209438402870027ce0a4f1c140c380139702490e04911c0026b8004100126edfc511ac62f37d3446fa488df4111ac62937ba446f7088d62d35bd4a6358b456f3288d62979bbd22377a346ef048d62949bb4a6358a466eb298d62915b71a7373a346e7068db8d09b941a36e23d6e2250dc40a1b709f36fa346df068db84f5b751a36e03d6b1488d62579b652235895a6ce6a0d9c971b39283671506d2480da4501b389a36705c6cf268d9c141ac4ab36394c6c7278d8e4d1b1c963638186c7028d62549ac4a7361b446c3088d62535af8a23601346be050d7c091ac49f3589366b125cd70911ae11a35c0246b125ad66911ad49a35983c6b3068d62065ac40a8009336596b4d58d41ab0a83560506596acd524e1aa41c32cb4e659684cb2979a89263512446a2050d440919652d32ca5669c498d38911a701434e0246594a4cb293996526b4c136659498d2a0a1a541232ca4a693460cb291996522b4424a68d480d1a501a342034424668a250d140a1a211f344232659488d0a0a1a141232ca42683278cb25799ed2634013c67b288cfc4f19ec9a33e13c67b028cb25499d52633c13c675268cec4f19d40a32c94a672460ce44f1964a3337a4c66f488cb20a996414b3314e66a268cd4491998a1334124666274ccc4d99641433194c663288cb209996412b2d24a65e480cbc1019692332e02865a47ccb48c99641200092f5ef6bcca8d119511a32a0345ef6a4ca28d19441a2f7b4a5ef68cbde96992da8325a5064b0a0bde9599211c3240385ef49cc8cd117bd21321a4c643050bde8f9901a23200345ef47abde5798e8a631d14463a030c740517bcad2f7956634298c685118d00c31a0145ef2a4c649117bca72f794d62449cc588d18b092316024624484c524918a41231223a62446cc4a8d18941231212d5ef298c420618840a2f794a61f260bde5197bca2b0894a619480c3250186420308946616250c2c0a18449f308932612278c24061844972f794460e030c1c0517bca12f79365ef25cc12531824a22f781a5ef032bfc9398111a3021245fe484c044917f91d2ff2365ff468bfc4b57bc0c2fd84c5fb088bde0597bc0aaf814a5f6480bec5017c0a32fa1285f027cbe04c97c49e2f812e5ef0280024ad6b9af2d735a5e66b8bccd417992e2f315c5e60b8bcc1416b9ab2f0a4c5e1488bc20a1784122d73525dc468bb84d17701c2ee0345ae69cbb20a1764122d734a5ae68cb5cd097551e2d725a5d06a0ba0941740a82e80505ae4acb988e17309c2e60385ae49cb92d117251e2d72425c7278b5c569709a82e12505c22a0b841416b8ab2dea385bd280b7a4e16f41c2d714e5b9688b729316e49e2d71425b6298b6c0616b8972d994c5b3030b5c4a56c1a62d83445ae07ab5c0c400493ad61445466bcb50d116a11a2d40345466a4b4a8d16941a2a334a5a3298a8cd19684a22a325e59d488b3a8d1674122a3252599688b328d1664122a324a596470b2c531519232ca13c54646cb244f15191aac124e58e468b1c091609212c6024582474b048d96209e2c401858225cb0a8d1614122c112d583468b040b55191a2a315e57f468a8c5695d1ae2ba3505744a0ae85415e1202bc140574248ae81715d4922ba0505462acada5315b4a22b693c56d258ada0615b40a2a3152565470aca4e15a4942b2924567248aca0e15941a2a314e560278ac04b15800c2b0014546294a8c519569a22ad24455b468ab48d1518a12aba4c557488a8c4f9551a22aa03454627aaa2531544a22a312e54d488a9a8d1534122a312d548468a94491520262a4044546032a8c05400491a99b495404b8a80941500ae2a015053368aa669254e9ae29d35053a2b8a745414cd22a999495346b8a68d414d12e29a25053328a00213d470af28e15d51c0aca568e14ad1a29593852b268a3813947023292a4c525488a4a4a14949228e03e51c06ca3e53147ca228f93c51f268a380b94701328e01e0010969ead793d5aea7ab5c4f56a49ead454541b27ab505124b8a249413d52f27aa5d4f54b8a1ad71435a827aa524f54a2a140993d528282a5c5054a0a0a571414a827a95e4f52ba9ea5713f9ae27f3504fe4b89fc9413d4a927a9514fb02c9ea5413dd2827b9504f70a09ea1393d4248008474f06a09e09413c0a827805c4bc2ac9dc1712f0aaa5e05e4bc0ba9781392f026a5e04c4bc08c978115390a02720404e208c9c40c92f02225e03e4de0989bc1112f01ea5e03c4bc06c9b21313642225e0354d64809ac1013502326a0224bc0689780b9338262670444ce07899c0d12f016a5e02c4bc04c98e13131c2226383c4c7068978095311202621404c208c9840492f01225e01e4bd08897a0d12f41225e01d0010868d71692dd2825b9504b70a08d71591adaf258a384b14689624e12c49a235b5a46b6ac9568e12ad1a2559384ab2688d6d492a09425402846b4928d69051ad1d235a394a304c8d68e11ad1b25023046b46a930929270a024e04049848c9324a12641424c23e46b468926d1124c9e24a2344930308d6525245a223594148e47091c8d11ac9d23593948b02c8d64e12209424412446b26c90c4c11ac9aa3da4a4822809041011ed2323f92c47f0308f68f91f40c23d92947b2428d64d11e09423c02846b0bc8d88e11b09c2399284730508d81111c09423802846c0488da4a11b41423601446b0a40020fd02a2f2333444664888cc51102a29231a44463288814d35029a2a2fb4445f28881493502922a0515a4596a08b2941164a82051564564708ac4e1028a7229b444534888145350282f22683c44d06889a0b11341220505a40a0ac88e0f111c1a22382c4470488141490282322234440a07c8140f50d9a721f93443f06886cd090f09a21e03443647a8740d10d89ea1b13543726886c0f50281e20503640a06a8561290bd2021794042f0808561190b41421583e42b0448140d10a52220502e42607884c0d102816a0cb4e4224688440d1065a121003441947a8328d50711a20e03441927a8348d10641ea0502c40a04c82a0f10541a20502540c094820901040a020804040c08c81c4a10301f20601240a0488140780041d9eac5e3d58b4802d710052e200a504012b88025410042e1eac563fc4707f88d0ff09c1fe1343d58a47f4d30f55ad1fab503f54a07ea540fd4281eab563f22707e44d0f55269eaa413ee2507dc0a0f551c9f624c3d54627d28e0fa51a1ea94d3d52827ca4f0f940c1ea9393e32987aa4c4f84261ea85a3dc6a07b8940f70a81ee0503d50ac7b24a0f64141ea83e3d60787ac0b0f541c8008373d3088703178f3da21e7a443cf288703148f31221e614438169a794130e05a29e3b443c7288702934f14261c0a453c3088702578efca21df9343bf248702548ef4261c09463bb098702514eb1a71dba343b7268758d08ed49a1d623d3b34687584f4ec0941d80283ac07c75a8d0eb49a1d603d381288702178ea4a21c085a39e6a073c970e79281cf15c39e2a073c140e7d201cf94039f08073c0d0e042b1cb84c39707872e0d0e5c161cb824397038702148e04271c9b44393488702134e38941c712438f03071c110e041f1c08363882787104d0e24161c404438105c702098e040f1c1144382268704490e040e80083331a6b46f8d40df0a81be05031a6ac6f24e0de41c18d34e31a684634978dc9261b92443722506e4490c692d18d25636c4986d8910db0941b612431a4a4634938c69269b403631a4986ca4a0d949218d24a363460634918c69229ac24a35d4806ba500d74201ac24635a2506b40a0d611f1ac23231a4886aa4a0d549218d24234f6886a48d0d3ca61a823434f0306344e4d35a218d13134a498694910c689518d12934702c6344a0d10a61a214431a24c684480c689299b94a33e48067c100cdca319e02833727c66e4c8ce09e19c01833725c634490cd09e19a01831a0bc650930ca09419793c32f030650110cb09e1960183280686524f0ca40c19401431a0a463e930c7c9419193c32303063e0d0c809e19001831f028634128c6d1818d93c31b03063411800417950b5e31568862a8d0c549a150b523124686244d0a85a5150b4630e68861c4d0a851e950a352a12b4610d40c21281841502a12ac60a8e0c149c15094e303688542508c01261801282a127c5fad10bf51a15093d2a10bc5ee130bdc2217b82c2f7048542168a842b17884c2f10885e20b0bc4121508522ef488542138a842696ea4e2e94685d2490ba41216ea422e62485cc090b751d16ea362e24685c4090b749696e9252de4685bc490b741695084c2da0585b4090a842516c0302a108c542114b28251692402d22805a4100b28231679282cf0505940f8b281916593c2cb0305940b8a842216382c2c7048542108a841b1622342a105c582130b042215082d2b449c57a8d0af41215a2422bb0485688e8ad11b15ba342b70485684b4ad51a15a02d2a1058542098ac0261580442a104a546128aad201559402ab080546118aa0941540282a307c5460c8a949e15182e2a3024542090a840f00082b25b6bc4b6d68a61ae14c3502984b8530570a60a814c05c25b6ac526930a4d221499282932484b6d48a391a14713828e26851c0d096da714592828b2484b6d2896da312db422874784b6968a09a81412502822a050414096d2b13f23827e2704fc0e096d2713db4427b4784b69089e12613c24425b27a4b64c49d0a613a01825b2524e44f096c9093803c25b0b44d6d409ad2813595026b0a04b61589991c1331402662704cc0e096c271313442624984c40f096c2112f94c25f0304b60b89702612e02c25b05200209c964220f735e2556884aa8d09549a0f73522524684a44d07b9a512804c1ee68c49ad109349a0f723d24b0783dc8d4924220f715e24528848a4d0914920f71522416884824d0904920f714a23e47047c1307b8a311e03c1ee26c4740f07b89a91524e23646846c4908a92111a12422a4744548d88c51a11512d22e27845c0608a817115a3422b2484540b47b89a0f705e2272683dc168871ae10e35021c4a0438570870a810e05021d48043a5008742010e0241ee0ac42a1308542210a83c21505842a0908540e0f705220d47041a4e08349a10683820e25041c0a0834120f704e2080784100b08201210401c1ee0943dc118809a21011442034684044d07b8210ffa4c1ff4883dc0f87f1a20fe2341ee07a3ee5307dca20fc03c1f70683dc0b87b8130f984c1f30883dc0787bca20f79341ef2483dc074004118b8a5a1e96a03d29407a4280b8a561e64703cc0e05c5270b8a421e24983c40a05c51f0b8a321712bc3b653076ca20ed93c1db2682e25685c4ab0ea94c1d52883aa4f07549a0b895217129c2e25347441b0b894c1ce27839c4d05c4a50e613017128c2e25146f4a50e32401c628038c1006f4a30e19281c305037a4f86f4990df93c1bf03037a4b86f4910b89441ba2783744d05c4a10b893e1b629836c5105c49e8da0261712783625306c4a20b893a1af2402e24d86b0a60d614417126a33c52869d200d39401a708033c518690940d202819e27c33c4c86809e0d001819e25c33c4885c49a0cd94c19b2882e24c86601e0cc02c1710bc3185306309e0c983c1930583181106401e0c802c18c06831a0f0634160c60241710a430653060c9e0c383c1870583060d06101e0c202c1830482e21285fc980bf83c17f0582e21185d8a60bb13c17a0782f40b05d8220bb83c1770582ec0905c41d0b91201720982e40b05c41b00081f0e04bc2d89105b11a0b61240e04a42d28d05a49207024a0e048c2ca9105949207023a0e046c1c056857da80afa5015f2a01c05585711c0ae1380e029c2b4910380a10aba4c1572501c04f85551a0701321522982a44f0380970a7a4414f4681c04b43802f0a484c1490882920f05241a07005a0e00ac28613050c220a183c1430681c0148504a207004e0e009a25e5384ec9a09d92413b02825e5084e09209c01412f27425e4d84d09a09a01412f25425e4984c09a09812412f03a1c01304b01e0960340e00942540c038023070045118094248900490a009204011808c2424a04841408c03e11806423a4f04740c08c02e1180442320f04641608c01e0e008822a0f04541a0700421132681c00f8440260880440e007a1fe53842c9a08592410b0281fe508420920840140ff2741fe4d84109a0820140ff2541fe4984009a0801240ff03a1c00f03f02607e0440e00741f40803801b07b84c0f70881c00d4398250792400f22801e4100398230779280ef0501cc0f83981907593c0eb0301cc0b83981107383c0e70581cc0783801a07184c0e30881c00c83801307001e0010361129782252d06bb5c0d76a01ae97035d2806b95c0d70b8112958348a60691440d22781a44d022529066a380cd46819a4d03341a044a4e0ca2781944d022525044a4608948418693030d220619240c30481128f8300a60601440894741128d82251905e12c0892b416ed402dd2805b9500b70a01125582cd1c0599380b30701125382c12205812c0892841589302b09405602808927c1528d02a4960449320a7058112168289a80512500a22a01441402242b04ea3809d27013a1002741c04484e099488132530264160448420944981284a02501804a02808907c1208d02409e04802c08906411a1302341e04481e08a0981140f02240c80081708708800497820d22041a340832480049482011a0401240024940fc1300092303da4407b2480048e81e41e0012360770880045781cca20399340732480045481bd2203793406f2480045281b09c03604c00228c0d08d01a0a20341240022740ca4a01941e0011360630580044981841600112505029c0ba4d01749202814205b2480a04e81409b02c1340502540a04981501e02a02c05003c0a24d01449202801d0022480041781349200105a0426b8084d401092e0212500422a008414010d200219400430800840500082b01d84c03b0880760f00ec1a01d82c03b0380041480cd1c019a340332700660e00d09401a0280330280041380b81e01703402e05805c070008250010460284880505100a49a014124002084040930081220101280200500424f00840c01001400207c03613006c2200d82c01b0380040e80081b00aa3401526802c490054920010320102980205100409e00813400205c01a9100351a00102d0080980101100201e00403400203c00651000c9a0019240030280040740040980001f 12 11
def l_25 : Nat → Nat → Option Nat := unpackLinksF 0x54240a848150902a12054240a820b50402a08054100a8201504029fe2d3fc0a7f814ff029fe053fc0a7d0b4e06a9be0d3781a6c0d4d21a9a4053480a69014d20299a2d3340a66814cd0299a053340a640b4c802990053200a64014c8029862d30c0a54b54a5129480d27c5a4f8149f02932352583a4b0148e2291c052380a448b48902912052240a44814831a9001d2000a3c11478028f0051e00a3c01473168e6051cc0a3981473028e6051cc0a368d46a0e8d4051888a1e4d43c028721d0d83a198742c1e858050ac1a158142a06854050984a108b421028420506c6a0c0741802830050600a0a8740d2281a050340a040b40802810050200a04014021a7fe1cffc09ff813ff027f81cfd089fa013f4027e804fd009f78b3ef027de04fbc09f7813ef027de04fa469f3073e6027cc04f9809f1873db2276b34ed409da813b50276a04ed409d80b3b00276004ec009d8013b0027562ceac09d5813ab0275604eac09d30b38c6a7160ce2819c20d3840270804e1009c20137f166fe04de469bc81379026f204de409ba0b374026e804dd009ba01374026de2cdbc09aab5350166a004d4009a50d3470e68e04cfc899f8133b126740cce8099d013351666a04cd4099a813350265e34cb03996013242264804c900992013240263e2cc7c098f8131f0263e04c7c098f813191a62c1cc580987112e89a5ca1cb940971072df0e5b03cb60096b832d7025ac0cb5809688b2d10259c1cb206964012c80258a1cb14095e912bd0257a04ae4495c812b9025682cad0095a012b40256804ab86955872ab0255604aac0954072a02254004a800950012a0025362ca6c094d8129b0253604a6c094d812951a5241ca480949012920251e1ca1c8930cd25e0e4b814968292c052521a4a20c944092881251024a20493059258324b024960492c092581246164861c904291f8523d0a46e348cc49180723002460048c00916872252244224878390f0121e0243c0486c390991213024260483c49060720c0241804830090487201224020480408fe891fa0e3f4047e808fd011f70e3de4471e88e2071c20a380146f828dc0d1b50e366146c428d7851a91a34e1469428d00b19e0a3381465c58cb031960232c0465808cb01191163200c64008c801190023200462c58c5031890630a2460838c10118202304045fc38bf8117d0a2ea445c448b70716e022dc045b808b58716b022d21458488b081161022ba2456838ad0115a022b40455c38ab811550a29a4453408a6811491228c1c51808a301146022861c50c08a085139222234444018880111002220044400888011100222004428688501109062120442018808f101021fe143fc087f810ff021fe043ec487d810f90a1f2043e4087c810f9021ea243d4087a810f1121e2043c40876890ed021d80c39c5873810e7021cc0c3845870810c086180042f8285f010be0217c042e8485d010b80a170042e0085c010b412168042cc1859810b206164042c80859010af0e15e042bc0856850ad0215a042ac2855810a90a1520429c284c9d0990213204260184c010980213004254384a81095021280c250084a01093061183c23008460108c02118042300846010861a1042420808410107e120f4241e8083d0107a020ec241d0283a01073060e6041b858370106c0a0d8041ac183581066160cc041161822810450208a04114082281040160800410008200104002080040ec581d8103b02076040ec081d8103616038d406c180d030141a02804050080a010140201e2c03c08078100f0201e0403c08050b00a02008340100802010040200803ffc57ff80fe569fc02bf8007f000fda19fae1bf5c07e790fcf01f9e03f2857e500fca01f9403f2807e20cfc10df8203ee487dc80fb901f6a23ed017da00fb401f6803ed007d78afaf01f5e03ebc07d780faf01f5e03ea467d306fa601f3c43de267ba86f720dee403dbc37b40ef6801ece0bd9c07b302f6601ec22bd8407af06f5819eb003d6007aa86f5501e9a43d3407a680f4d01e902bd2007a286f4501e8a03cfc679f80f3f01e781bcf0079a10f3401e6803cd0079808f3001e6003cc0079800f2b15e5603cac079580f2b01e5603cac07928cf220de4403c88079100f1f0de2e43bc6677706eec09dd413ba027710cee105dc203b84077080ee101db82bb6c176d80edb01db603b6c076b0aed409da413b34576488ec511d841bb08075d10eb611d6c03acc375980eb301d6603ac0375800eb001d5c13a98875300ea30dd401ba80074f04e9e01d3813a70074d04e9419d2803a50074808e8d0dd1a03a34074680e8a0dd0443a08074100e7e11cf61b9ec073d80e7b01cf01b9e0073b04e7601cdc4391a872186e4109c7e138f4271b8ce3509c66138b8571508e270dc4a1388c271084e1b19c321385c27090ae1009c1c13824570402e0801c1003820070400e0315c040b808070100e0201c04037f456fe02dfc01bf21b7d446fa80df501bea037c836f900df201be0137c006f704de621bc61b77c46ef80ddf01bbe0377c06ee06ddc01bb41376806e910dd105ba20374406e688dca0db940372806e500dc70db8e0371426e280dc501b86136ec86dd80dbb01b6e236d036da00db401b68036c436d880daf09b4e435fe86bf02d7e01afc035f806bf00d7e01afc035f806bc0cd7801aee0b5dc06bb02d6f1dade035b426b680d6d01ada035b406b488d6901ad00b58c56b180d6301ac60357c46af80d5b11ab60356426ac80d5901ab20356406aa88d5501aaa0354446a880d5101a9a2353406a602d4715a8e0349a169300d2409a4803490069200d2011a4003480068e08d1c01a3023460068b04d1601a2c03458068908d1201a220b444068802d1001a2003440068686d0d01a161342c068580d0909a1203424068384d0701a0a133dce67b80cf7019ec0b3d8067b00cf5059ea033d4067a80cf20d9e4033c8067882cea1d9d4033a8067500cea019d4033a806720cce0119c003380066e08cda099b403364166c80cd4159a803340466800cd0019a003330466504cca019920b32406620acc4019470b280364f04c9c0993413250664904c90099162b21c464302c860190c03218064300c81159000b200064000c8001900031ec563c06c74118e8031b0863600c6c018d0231a0063286c61118c203184063080c61018bc1b178062f00c5c098b803150862a00c54018a023140062686c4a0d89403120262400c460988c03110261f0cc3c09878030e8261d00c38098662b0cc061980c2f1185e030bc061588c280d850030a0061400c250d84a0308c261180c1b218360306c060b88c140d82803050060a00c110d8220303c260780c07217bf42f7035ed04bd8097ac12f4065e704bcc0978e2af0c45e006bbe0977812ee825da0cbb20976012eac55d580ba71174a12e8c25cf0ab9c0973412e5455ca02b940172802e5005ca00b8f1571c0ae3805c700b8e0171c02e2455c480b860d70422e0805c100b820170402dfc35bf80b7f016fa12df405be80b7d016f612dcc85b980b73016de22dbc05b606b68116d002da005b400b68016ca1ad9405b280b63096c602d8c05b180b61096b242d6405ac80b55116a80ad4c15a980b530169e22d3035a600b4c0169802d2435a480b470968e02d1c05a284b3d2167a02cf4059c88b360d66c02cd8059b00b330d66602cc4259880b310165e12c9c857fd0afe055fc02bf8057f00afe015fc02bf8057f00af8195f002bdc157b80af6055de3abbc057780aef015de02bac457580aea055ca2ab88357100ae2015c012b80057000ae0015c002b70456e00adc015b802b60456b82ad7015a622b4c056884ad1015a202b44056880acd1159a02b34056680acd0159222b20156400ac80158822b10056200ac01158002b00055e08abc015760aad8555b00a958552a02a4c254980a930152602a3c454780a8f0151622a2c054388a870150a12a14054280a850150222a04054080a81014fa229f4053e80a79114f2029e0153c00a77054ee029dc053b80a740d4e8029c8253882a71014e2029bc253780a6f014da129b4053584a5d394ba02974052e02a5c014b60a96c052d80a5b014b602960352c00a58014ae0a940752800a50014a002940052800a500149432928052500a4a0149012920052382a47014842a908052100a4201484028f8451f00a3d054780a8f0051d82a380d470028e0051a08a3401468028c0451800a3001458228b0051600a2c0145022898251300a250544a028805510009ff853fe027fc04ff809ff013fe027e854fd009fa013f4027e804fd009f5153ea027d404fa809f5013ea027c054eb349d5053a80a73864e7009ce0139c0273804e48a9c9013920272404e4809c9013882a71004e2009c4013880271004df8a9bf013723267da4cd0a99a013340265064c886991013124262404c480984153080261004c200984012fc325ec34bd80973212e6025cc04b980973012dc2a5b804b70096e012dc025b804b700968192ca1a59404ae9095d012ba0257404ac8895805265324bc3496069290d25202488749100921052420248014900091b152360246034890c912012240243c3487809072120e0241c04838090215204023fc347f808ff011f2323e4047c808f60d1ec023b88477008ee011dc023b80477008e9151d2023983473008e6011cc0239804700c8e0011c002374346e808d5211aa02354046a808d5011a2222ae6454068a60914812288244e0c89b051360226c044d8089b0112c2a254144a808950112a0225404480a88e091181221c54418887f110f81a1f0043a10870110e0021b434368086d010da021a834350086a010d012180842f0485c090b802168242a8a855010a22214404288084d110941a12804211084201084020f8441f0083b0d076020ec041d808380d070020e0041b0483601068120d004161082c01058020a43413068230d0460208c041084821010420207c240f8081f0103a1205c63f7d07ec0cfd411fa023f3047e018fbc11f7023eb8a7d310fa211f3c23e50a7c610f8619f0423df847bd08f6e31ed423d9847ae14f5811ea823d28a7a404f4801e9003d2007a400f3e29e7813cf0079e00f3c01e7803cc8a79804f3001e5433c88879100f2201e4403c70678e00f1c01e3023c60078a08f1401e2803c40478020efa19de443bc8077900ef201de403bb0677600ee811dd003b61076c00ed219da403b48076510eca01d9403b2807620cec401d8023b00076000ec001d7823af0075c08ea841d4433a88075100e9a21d3403a68074d00e9a01d2833a50074808e9001d00839f82717a0e2c09c58038b0071600e2c01c58038b0071600e2031c4003878270f00e1c09c1c73838070508e0a01c1403828070500e0221c040380026fb14df601bec037d806f710dee01bcc4379806f204dda29bb40376806ed00dd221ba40372886e500dc611b8c0371806e300dc601b7c436f806df00db621b6c036d806d710d6d09ad8035a046b400d6801ad00358086b000d6001ab04356006a810d5001aa00352086a400d4021a80034f0469e00d3c01a78034d0869a00d3209a64034c0269800d3001a60034a8669500d2611a4c03488469100d2201a3c23478068f00d1a119fce33f8067f00cfc099f8033f0067d04cfa019f0133e0067c00cf8019f0033c866721cce4019c803390067200ce4019c803360c66810cd0019a003320866304cc60198c03308465c14cb80196c132d8065b00cb211950532a0065010ca00194003280064c10c57098a033130462408c4411870630d0461808c262983c43070260e00c1c0183803070060914c100982003040060800c100180c5300065fc10bf8017d082fa005f400be0217c002f6865e910bd2017a402f4805e900bcc1979802f3005e408bc80177082ee005dc00bb02175822eb005d408ba80174822e68a5cd00b922172402e4805c510b841970802dd105ba00b74016d842db005b30cb66016cc02d9805b00cb60016b822d7005ae00b5c016b022d2105a400b480168432cf0659b0cb360166c02cc8459900b320165c22cb8059700b2a1163c62c68458b08b160162c02c48458900b120161c22c10a58200b040160802bf08556a0aa61954422a78454d08a8e3151422a18453e14a74214e0229b0453114a5a214a832940452608a4811478628e0451a08a2a2945402888850f08a1a11420528304504089fe293f8127f004fe009fc013f8027c8a4f8049f0013e0027c004f8009e6293cc0278064ec109d8013b00276004ec009d2193a40274804e7089ce0139c0273804e5089ca013940272804e3089b64136c026d804d7109ae013503268084d0009a0013400268004cd0c99a013340265844cb009960132c0264844c12098201304025e884bc04978012e4325c804b90096a212d4025a804b500964192c80258044b000960012c00257044ae00958112908250864a10094201274424e8049d0093a01274024d0649a0093401260224c004980092c1125802471048d048cb41190123200464008c801190023200464008c801178622f0045d048ba01170122a8e455008aa01154022a80451108a20114012258a4480c890011200223044460088c01118022300442108840110802210043e1087a090f4021c8843900870090cc52198043300866010bc42178042b10856010a422148042900852010a40212884250084a01094021280421108400908002100041c1083801070020c08418008300105041f9c23f3007e210fc401f8803f1007da20fb401f6803e9107d200f9441f2803e5007c220f8401ee883dd007b610f6c01ed803db007ae20f5c01eb803d7007a620f4c01e9803cf1079e00f3811e7003cd0479a00f3401e6803ca0c79400f2021e3823c70078a10f1401e2803c30878600f0c01e0843b33876600ecc01d9023b20076208ec401d8803b00476000ec001d8003b00075a18e9871d3003a60074c00e9801d3003a60074030e8001cf8239f0073e00e7c01cf8039d0873028e6001cc003980073000e5041ca003930472408e4801c88238e0c71c00e3801c50838a0071400e1841c2823850070a00e0c21bf0a37e006fc00df801bd0837a006f400de801bb08355846a418d4021a70434c0868c30d1021a10433d1467220cdc219a843301465820cac11958032b0065600cac01930a3250464a00c940192803250064028c74318c883190062240c4401888030d1061a00c283183083060060c00c180183003030c60600c0c0180843010060200c04017f842ff005ee40bdc017b802f3105e018bc00178002ec105d800b908172002e4005c020b80016e862dd005ba00b64416c802d9005b200b64016b062d6005ac00b50216a002d4005a800b482169002ca2059400b280163082c60058c00b0c3160062bd0c57a00af4015d842bb0057600ae4215c802b90056e10ac46157842ad0855a00ab40155842ab0055600aa421520a2a40054800a9001500829e0853810a70014e0029a0853400a68014c042931452600a4c01498028f104cf40990313104260084bc10960612b042540849e2892c41248424708484288f8411d862390846e108d421178c22d08456108985113002221044010878210c8a2190042a2084c21088420c144141082021018a2020440400808010100202003fa287f010fe001fc003f8007f000fb8a1f7003e8187c040f8001f0003e0007c000f6861ed003da007ac20f5801eb003d6007a420f4801e9003d20079c20ef901df003be0076c40ed801d80c3a82075000ea001d4003a80074430e8801d10039e1073c00e7801cf0039a1073400e6801cd003961070c80e1801c30037e206fc00de061bc00378006e040dc001b800370006e000da861b50036a006cc20d9801b300366006c420d8801b100362006bc20d3901a70034e0068c40d1801a00c3400068000ce0819c003380067000ce001990c3320066400cb841970032e0065c00ca841950032a0065400c98418b203160062c00c3881860430a0857680ae0215c002b80057000ae0015c002b80057000ab0c156002aa0855400aa0214d1c29a0053400a68014d002922052400a402143142801850000a0001400028000500009e0813c00276084d850998613300266004c420988013100262004c400968812d0025a004b400948812804250004904092001240024800480408f8211f002362046c008c841190023200464008c801151022a00454008a801150022220440108800110002182043000860010c00218004204083821070020e0040c408180103001fe203fc007f800fb101b508368006c040d8001b000360006a080d4001a8003404068000cc10198003300064080c800188203100061040c20018400308005f080be0017c002f8005d080ba00174002d8405b000b60016c002c84059000b20015c202b80056820ad00158082b00056000ac00152182a40053840a60414c002902051820a300146002842050800a10013e10244e04880091001200824000478208f0011c0823800470008e0011c002380045860841c108002100042000840010800210003f0c07d040fa001f4003e8007d000fa001ec203b0a076000ec001d8003b00072100e4001c4103802070000de081b030358206b000d6001ac00358006b000d210190503200064000c800190003008060000be08178102f0005d040b418168002d0005a000b400158402b00056000a420148002900052000a40013840270004e0009c0013800250802984003400001 0x460b4ca4a2994925029202652384072c69948893290d2052104ca4108080cd328f92651ea40a3c2994765028d62f4fac5da386b546ed66885ab4fab51a2168d46cd1630d26d25a49a4648b1de9064291cc4ba3172e29b48a526900a2bb1941782272dfa4c502026d1f849a3a08a88c1051a41c9e90319fd6893f0d523012e43aa507292b8da85410042e1d105086a4711588d1b249c3871343970707be0d21ad2651a128a332494640a28c41236614ca2e27945a4d28b00c51581439c0994500f289c1a51302ca2504947117a8de2ed104559f38a546cd5a881aad1ab4e9f369b2829362d122c9ba3da3047345e8d61dd18be314d71f28af784f68a89cd149356d8262974134fe422a5803da240734460d4ea018801b5ca1a4a141e54280028001b5c8758b943057284ca850685ca060a1434d723012e50b95ca122a1418172814284a034c8b2689166912869a74fe34294047b2ce8d5f149eb8e9354b907a7ee0d5b522e50c15ca172a141617281028507b5ca134b9424941ca4ae50505ca030a0f88931c712238f144a0f69d3f6d0a4fd1ec58a357c427afda4d52e01e9fb0353a28b941a572830a850585ca0a0a1400d728192e502a50a042b94065410042e25b94c3f52887f0112801a74fd34293e47b1608d5f0c9eb8d9354b707a9c40d68822f4fa45da216bd3ecd76885a75103499f96853eed0687d2f50f25da1d4b91ea9662ed2ad0e252a1b4a34329424f51ec57a35a162bd42a576850ae3b49597262ab42254a840a8d071507c227ae344d68242f50405da070b88981650002ad01052a010a33fe1412d81e9fa0358744693bc4d27301a4f62346d32693960d27ad1a4ee9343a10693fad727f1284f52349fb2a13b84d27e8284e50349f86b8006d5000da24f6a349df26939a0d22b11a4f41389e32693b40e274c1a4f6a4c86a4793ce4a2788924ec8289d20490ecd024252444b2408744813d85027ac204f6b4a9ea68d2128e666118bc09396fc2628d00e4f4418cf42389e7468e1c4d27601c4e88349df498d928f278c944f11249d70513a0091b5da03c01486fb280da6902778a04ee8409df6953b8d19e011cc0fa3190827312a4c519c1c9e80319da4713b28d27609c4eb9343df06939a930e5d1e4e99289d22493a20a2740121d3b4046609079e100e85204e61409cb08139ad2a729a323323951546320e4e625098bbf8396fa0633eb1767ce2d4fcc569f78ab3ecd7a7d5aecfa34e9f369b20c92624d20c98a3d9f24753e28e67c11c4f7a369ee46b3d28d219518bbf1496f9282f6c4f67989d4f29399e42713c24da7809aced9346c62628ca124f3820a5503d9d60753aa0e67501c4e78369ce06b3920d0e5818c6025c9c62b938a5427102e4e18509c069937ed017a5264df04c9bd081374d326e5a014da4c9b829936e5026ae2f4b845d8c369b38ed26709a2c98b419b44b53669666552b4b825199548d3649164c11f448a325ed29b3825266f0a2b19941657252b56484a7c26cdd8499b608a5e0104c601492c0219774892e6952305ae43b3505e82b8af4540a602e11005086a4713624e26c09a4d78389ae0690d69322cd222b79285c424842a0a09b4124d514c9a9288ae04f26a00c4d38149a40993461108601e4d102c9a1049368d7a6cdaecca3559636a520ad2a2b5a34d92569944ab35a93a3d5254d62468774853568fa58d1eb5793d5d426ad424b669894cd292557e2426fe0f4a181a9b882d9a005333e09489810c3b35c9932b931c5426202e4c08508c16b932c972648ae4c69509870b930014241124455a448ac46932c93a5e12148223a99846cd5c4b574c929bf02d28504a006d72659284c515097b0a00069715ea2e4c9a5c9924a130c1725fc284c735c98d6a13149717a0ae4c285c97e0a0d5a8f17451a2e913498a49d2ec90a40d1d4552366ad25afbe494df4169418252208b931097261d284c305c9850a1302d72601a84bda5c97f2b92fc540a602e1be13c2822685080d25ed274baa429024751528d9ab096ae812537c05a9a80966522f4b2c5d99d6bd338d7666dae49bb598bb6ab334d4a665a8ccbb509954bd2e2976655274ca2499744852e49064051d4542369912bd32057663cae31c9595e52ab31854a62ca8cc49506ab25ab9e4966102f4c185d9820b85ec164a5c2acbe85297c0a32f4140dec169408258744692b0492518124b523457824928a0925a51a4ab92421e0492f0d425dd2e4b42349762a12ac4925d4284a20249734b80069522cd224b112895d2492a80a25341243aa4092f4791208c21ad264b223c9612512b849254c144a60248744812d45025a4204b224a96848d25e8fa59d1932b1295aa24262e0a495c10cb22440034692b249251c124b124c961488b88492548144a582495d2992b85125649e2b792c9510312940515ed1832a9385a92612b09015e0a04ab8409594952ac91a4b91f447a32655253028484c581492b0219544992a6912548944a892426d04929a532530a24a393c2152592960625280a111a303150704aa0c25192010f14094508128e92a51123496a3e88e46462a4a542890b2a0295a80432e0d7658dad4ba3569726ab258d3a235a14b8a5e9704bb2de93a5b926cb6a4c8ef4952d891a5ad22cb32448654852ca8fa58d1eb299395a7262d364b6580954af92995e2512b649a56892caa92456c2426280e4950189b582d95005529e0a6538144a482694804b28609085010c35b449222892201124849a48783468026921c0d24809a1980348986b92809424fca848f93493e0a121a0d21ada443b34c93b2712744d24e41c49c0348c04b91588d24d49c49a1349330712640d2301224949289190512504a2460143a81289170508604a249c14497a448ae46924c4e24b89248b03892d04914e8d17789a48e838914068d548f17351a2e7134928468ea049249c12494a4e9264852008ea29d1b35512d74b24a6f40b49fc12c31a4c56a4792380a244c122ac34077d290df0501a0120490940920081244d2a47da33bea396984631fa4e618c98a320393cd06314c8d24749c48e13428e0686f24f09f89a14003491846922e4910c01248ca4e9164851fe8ea2991b35492d5cc24a6f20b50ac12c3124c2104792280a244c12100340463090798100cc12048794090e081220d2a435a3231a393684631f84e618898bbe0396f706328316a4f62b49e35e9376b526cd5a4c5a9476b4e86169b26097a4b12947f24a8fb49314a91a18520c52a368ee46aef6525bd8a0aed93d92b2752544e64949c49213692326b23c4d183498b5412d5cb24a8c4124f2c2094683d91b0752340e64541c48903691106b2180d0b18189bc02d27d04b1829123a89446b0288e92511aa0a186c9e46a0182d42791d0062425a245aa449082891ce4a241c2246982886a4691c24d232c1a4701248ca048f3a4923241246f924471049208d422492e4819508de249204142320122b49248c70491ba49083c124462349002711b84923fc1c4630246132791a4060b309e47301888a4891fa5123949447e0448d10510d49221d51e47c9288f82491ee0a23d812460b5c8b34891e64a23c8924788288f00490be8c217da24522445c02491b40a233c123daa4c715488aa25123a51a30d9348e8068c264d23981a47534e8e76851ca8f62911abda93d61426a9520f4fbc1ac2f13c5622591b20623380a2b5a30652270b4c4c2381203ce9408df080ad24a237414470a4a8de48d1b88fa179193291297af2426260a494c10c51a448da2511b24909a41225414c3ee2883e61123551a46a1342d40691a44d0b301a46b34e8d36851a28f628d1abda13d71426a9500f4b341ac2e93c20825919e0623380a109a303120704a40c2329202389408c908041e4a231c14465a4a8c848d18c8fa175191891294a3242ca20a569410c8545e9068a520ad6a405ab47f34e8fb69b144d16171a147d25e8f54b51e895a3bd294772468a248b1da8fa1711ebd994d71328aca04e569098b4a12d8ec2551d64a6390944719268e224b1b649157c90a5384d3ed08a6220e4944189b202d8d80551ae0a6340144668268cc04b18a09081c10c442308c16b91809722fcae45f1508bd0b917814221c984431308b368910a9022b11a45d1388b92691700e22dc1a45ab4c878461166d422c9284589508b00a115c9321e1184563508ab4a11545422a428001a4c85f47914e4a229814001a4c85f4791484a228c1443f120557688bbe9121f5184508488a00890f84807fda2148a4487b46113a522270a2461c5e8c28b517715a2da2945a35a8af6ad144d3a181a6c56a5a8a84ad14a93a19126c52a3e8a24731168ca22518c3d23089f29ac4052575ca2c4f14177a272de84c593c94ad112189b09a5b2124a2422c4d0414610727920c4c4014927821888699130912259a243b244895289128112221a64492448906890ea8d223c9a44703488c4991149321d11a4439348860691084a220c14440934880068c4c8d21f81a16fa3487c269110d3a215a143c24a87348d1048fa1fd1ec3e93d5ca26b0b64a557490c3d83d27c06b0aa0a481410c3c3448744810e25021b820438a3486e4690ecd421d528439a348722b90e05421bc2e43685086b4990d48f21a4944341248670510cc0915a89c2ef13421007051c0d217da2001a448632890c4111588942e01242080504d209217da2001a3485e2690ba0d18989e42d01885a4690b6d11548a62b193c8590310b0050b7c1e42a02c8544690aad107d02610583c8530590a409225e2f449c528916bd11ad4a185a6c2e34a88b68d112d161e9a243ca5e8774b50d895a1952943224e86149b0c08fa1711ebd914d71128ad4e4f57209ab4212d8572530ac49556490a5304d3eb08a6ee0f49e81a9aa02d8510530a009480410c26a5c84c4a0e5257212c2e4250508476b908cd417a0ae42285c8440a1082d32101a041fa4c83e4801b05320b22f3fb45d72e69b09cd26125a2bdb3415ed49b09092610d22b4da4183b2b5074566040ab3fb15181028d072515e849f37913268225cb4048837826c2104983d08a2841045bc0c8430117fc288ff2551cb1ae36bb505e94b8af694035c2e02305083847106e8d1b249c41b0388350690649320c5222b792883005105e091b30a638f144570278ba44d00ec0c05181482b0990541120a41e41403403c05907697a0e92ec07a557da4a4ef2929c3d2332723a5c646d07255a03caac1a14e769295066519b60a141713e63927505a4d95f89941612e7da25a3d80b42ec128ed01d82703304c05413008b6bb5c81d4b90309420382e40385072c6b903897205d2840915c80d0b900c141de0a438694470e269024539ff8a13bc13a81f26cc9a4a9714930f581d0ba02aaf6d720752e40e25080c0b900a142061ae40bb505e94b902257202c2e40205064c270b864d17109240894e7fd284eee4e9c309b32612a81424c3d40742e40a801b5c8124a10225420042800195c0468b901c9720352840615c80b2a100ed72019a8402a5c8044a100257035c2e0f492c0b7248170092004a73fd942776274e164d992c952e11261e903a98405603e2f3eec5d8246bd046d76089ae3de3597266ab042d4a081a8c0f35081b4bd0349760652e350a595e54ab02c94a05528c09a508102bcfee576040a74079497fa284ff0505dd49d38513664a254b8249a0282f40485d8080b82901643582ac018528020a30001407a00e85b0156d3268fc4491f2c0a3f8134578248f94051fbc9a3f0924043028ffcd41ff5283fe15c7ee268fc0491fec283e48147f92b8006551c78a23f513c7e5268fb2061f480a36a14079e278de24c1b30a63f493c7e4268fb84b1f600c3e88146d3480fe0501fbc203ee14a7ee28cf3c4f9fb49933f92e59f2442dc06421408bf514c7e9288ba44d1f5c0c3e801457a260cfa4b1678903f294c7e4288ae04f1f6c963eb0187cf028fc49015e0a03f08407db294fc0519e709f37813267d25cfbe4885b40c8420117dc288fb64d000c923e60147d9298fb0511f5c9e3eb1340a3028fa4131f44223e803c7cf068f980b00ec0e02392016c050106081f2d203e5140043080f98529f24a33cd13e6ef264cf64b9674910b60194fb022fec975f692d3fd2567f84aaf32939bb92133d23e59c464fee579fd8aebfa94e7f429afe6531d8ca53f91467f128afd8511b18a13f593e7e827afce4f18cc9d3f31367e326afbc4d15b0993ee92e7da25a2d60a4208108ea01d7d5034fa8065f4c0c3e70167cd02af900500e808b663447aa488f161118b91a3c50347a9468f120d1ea11a0ca0346fe6b8f8a941e9d1a3e21507c30a0f100d1b31a436bb4c7c0470f7e8d1ef81c3de8347292b8f748e1ee51a3871347b8070f6e0d1e991a3c38347a54682f60d1e91a237aa447b5250f0c111ed0143d6344552488b7e4d1e14222efa34709268f300e1e3c1a3249385be268b80491e88a73d0142774274e124d9924953d79261e703a16a0555ad2636223c797050f1c091549a03d22387ac460c5c901ea4a03d40407a6250f4a0a1ea9253d3a467a447cc4e8c9dc494b62121460052790085ca5223d1128794050f3e4d1e74923cd81479f250f260a1e74943c902879b2508200a1e811c3cf144710268f38491e441c3cd014798470f2e8d1c209a0668341e62581664902d0123c9934792248820051e50a73c8942773274e104d9920952de9261e603a818055b0d2601b23c78f250f1c49004da022f8483c7080328901e28a03c484017b278f0e061e2da53c434645f4723a28c5e189cbc2931770072d860c5f1a2d3e14567c16bcf78d69eedab3db35274969cd84d35ecd24bd92415db47af628e9ec11cbd72387ad46cf568d5e8d1a3422317a12bcf32549dc8a53b794970728cd84505c1c9b3b1135647254b78499178249e30410cc07af2c0e9e541cbc803878d06cf180d5e101a08a0311e503a164055cb0a23af13c744030d1e4f1d0c0c3ae92c74203024c0f1d70163c0b44780488e40511d6c9e3bf844741030eb44b1d000c08f03c759058efa911c48a23ac13c77c088e7e06166d182ab94c761278e7c061d491a364924736048ea2491cd40a3a8124734028e9e4911b40a3bc3507774a0de6571d38923bb050733028ad2491cc80a3a6924034028ee88e1bb49a3a6124773070e620518989e39e81811a078eae0b1dc5a2375944756278ee0111cf00c36494876d278ed84d1b50963b581876a028e58d71c78a23b393c766268eca061d900a35d130758698ec2d1155d223831445ce268e90061ce80a347a3475d268eb80d1d689a3ac834626468eae0d1d79a73adb4275847ad108d5d589eb8313549507a7cc0d55a89833b92c59a240ac64f1ae4963a3818739028ea2901d40a03a7840569250e9a0a1d48a53a714674c27cd724c99dc973a592216a032102045ae922382944748278e8e4d027c0a24994c3e5288014111d0d1a3a1134126068e804d04781a39ea3411a068e88d39d05a139fa3d73e46ae784f5c149aa4983d11f06ae740f1ce41a35c02c02e03806e4805a414040020735480e685011b420399128034050e6c529ccca339893e6b8264cea4b9664910b481948b022f05179dfa293bdb4d77a68aef2969dd52b3b924e76f49ae08915add2133a23e598464edc579da4ad3b41567632a4ec4519c10a2bb013e75f27aeaa4f18809d3aa13675326ae944d157c993a492e6b725a924134f90228b402907f04239a075d180d3a281973b030e70059cdc0ab9801402d022dd24c1cb1ae395a5c72a4a0e52571ca02e3938506e8260dce0c1c79a2392a38724468dcc501c389a391838722068e40d31b649838f35071d4a0e38541c6c28372830551688dc85017789a38c838718068aa293165c9838a928714050b94d11c492633993c55c240e20531b649838735070d4a0e18541c2c28001a4c6ba478e124a1c201400194c706278d744b1c140c36e920012688e06921c09220671446dc260e5d179cb62d3934567218a4e3ed69c69ab38234e6bb69ae2e935a5124aeba45716482e268e5c4518b8795a70a2ace0e539b14a6b8393e704272dd84c9ba898b6d93067125cb2a489c04268958490c808ae001051741c9e20311670320fa045ba52637f1446fc688df6911b5ca237d0446f8488b748d1560a237b8445bb488c8c8e1bd4a62ae9306e9698de6511bc5223782346d4248dde091bb4a637594c6e8468da64d1b9c1a3099346e5068dc64a1b88143702346df068dba8d04c49a374b4e6e6684dc88f56ed1ab6c94a6d128cdc24f9b789eb6092e55c244db80f42c41ab5b01902b022db2911b489a369a406d2280d9e101b3c9a36bb506d64b8daa941b50a83689346d00b8d9c141b30a636593c6ca268d924b1b200c36381456b470bbe8d00d81c0668346c4688d7491000ca2361844613278d80061b009a2ac24c6c1288ac44a1afc1435f024563278b9c4d00b80c04f8146ba488d728d000c9235c024131078d6a0b1ad49a35b24400b098d680f1acc1a01782c6fd8bcdf3149bd9a6b7a3456f24bcddc949b0926b5ba4a6ec48cdd4915b6d22322a3a5b846cdb4579b60ad3669566c62a4d8a539b08a6b5e93e60d274d784d95649935d92e6b725a920134f88228f202d0af04a372075ac80cb58815027022d20d115c11a33003468f468cbe091a391a32f02468d468320091ab9a82d625c68c468d5a541ab02832e82468b468cb8091a291a0c3824689488b468d1aa89c35483865b048d26d1158d1a33994465a068ae0921a952635224457b478d460a1a88122f415c69f498d3c9117109234e82869c048cf25219c8a22ef134557488b6e4919c01433202468329cd025099e49d34c136644254b6e49878c0e857015557488b80491a581434a824563480d128f1a4d182ac24c555478cde0a198c12347a4068e280d1a101a2c94345028690494d18919a251f344232641252aaa484c3c14927021558498ad68f1a18143428245e8288d064f19b00c34013467e248cf8051a009e33581867e278cd40619f09e155818681498cfe5119f49a2e3924669050cf60519e09233b014678278cd00619d89e154018679498cee4d16e492333828675028ce68c1778a633913c666030ce09319bd222db1240c30483c44b02b09205682466b268cd4490aac0a3341242a8028cd85399a4a133393a66626cc864a96d8930f101d2a302acc853198ca22aa13c0232580228c0c381c12683065f480320501978200c392865c050cc09299752332da3e65a46461c4a46d090b20029554042d5ed69aadab35434e6a7684d4c979a852d35025669b4a4d34939a6526b4ba4c694494d24919a4522b43a44684484c168f954d1eb4115e67a2a4ce85299c4a332113a63f272b6a4d954c98ada92660c24a61a0e49301886102d66e054cda0a59941433102666104acb2090388108f081d0ab02abd25118bc9e30301862e278c0a0618b49e30201862c0781e60b1959a232aa3462b298baa4d19501a30181862a278c040618a41e07802c652468c505317249a328834601030c8c8c177ca631913c600030c389115bc922fc02461b268bee0518689a2fb014619268652051935a83262505a12b8c304d192c282fa814617268be80518589a190014649470c2a5116589a3240385f3028c8cd1187d222b11245f2048c264d17c40a309134021028c88931844a22ca124643050be00518989e2ff8186250781ce0b1905a231214c592268c800d17f80c2b794863d298c785115e89631d81863a028bd29718dca631b1445d2268c6a0618d00a314248632488bbe8d1544a22da13460a030bf80518b91a31692462c048c544918a412313234625048c5e9398ad2131423a62746cc484b56d0929a882d27504aaa25117389a311018621028ac45018549e30f930552298a9e4b18240c2fd81461b480c345018642030b928616050c264f18480c30e14a61828cc2a4f98509930892e54f2442cc0641f008aa914c56a258c1e0618380a2a712054e468c14531824a22d993409602869e4f09d09a004034605468c084903cc123011240f0048bfe8d039c1230324e603484c028e98011b2ff12d5b324a69e0b43a412afe04c5fb088a9a0b006c0e0121201650500f60817dd202fb140329080be84a0c80142f893c021030bf05297d4a32f993e5f2264be04b9534910b2819347022caed7994da932834a64f68cc9c9699292b323a4e645484c848f98fd1ead923554c464c7c5798e4ad31c1566332a4c625398c0a6b1194c620294c3c519874a2b0814460d284c184d96c89ab0592e54c25a69c0f49cc1a8b202907a0423600758200d3038195fd030bf40597e40aaf781401a022b204817adae2f53505e94b8bd057179c2e2f305058f240b1c081791262f1a445d2468b1a4c1710922f10285e1048bbe8d17789a2ee8385dc068b180817391a2c59305c0248bb40a1764122e52305bb260b144817551e2bf9205d36a0ba4941744a82e80505ce470b745017349c2e603855b240b94d117251e2df94c55a240b8e4f15fc902e2b505c44a0b86541708282e02385bf280b7c4e16f41c2ad9205bb688b749316e49e2ad1205b72980064f1538962db0185b42980064f1538962d9818583240b62d316c1a20082340c4268b044817b5af2f635a5e56acbc0d4976da72ec34a5d768cbacd097512d2e7a565cb49cb909096c91f2a823d5c62b4b825596f0a72dc1425b527caac4f56d4972d9129593244b22485604902d783d0fb07217c0d56b81898602924a0422c60641e008ac824c5ac288b54d116a51a2bd9345a8068b2e9116991a2b59345a5068b1491166d1c2d194c55d260b20931684a22cfa4459e468af4491674122cdb4459a468ad4491664122c5244597470b2c531570982ca13c592278b1e8d15e0922c7024569248b1809156c902c493c588030b0c8d1614122c1a34100248b20939635212c5a3a58a46cafe5295dca32b413e55a264b0e4b961096ac102d0aa04aa9606406008abfa34579248af29015e0a02ba840575248afad715f1a82bda5057a2a0aee4915d82e2ba050572298ae25115c09e2b792c56e030ada0515a4942b3828567248ad68e15a89c2b4124566070aca0d158c9e2b112c561030ac005156d1a2ada3455b468abad11571222ad234558498aae91008c14061824555688a9c8d000c9a2aa034552298aa251006c0c04b01454f488a9c8d000c922a682454a0782000b1528922a5a34549098a901100241e00e02c5ab6bcb4ed49691a52d13465a04bcb38949661252caa4655347aa988e964d1b2c8a35581468b005795f8ad2b995656c2a4ac853957ca52af146559284aac4f954c9eaa812e54c25a6980f49c41a8f002d0a804a33407551c0caa3015014022a86971509282a095c5402a08021714f5ae29e35053b2b8a74540a602e29bb5c5366a0a6a9714d12806b85c51c8bc9d7175021a6aa234953f68a954d04a7d26a9f24953948a6d6904378a6a9c14953328a3a85054c42d2980594f60ac9d61453d82329784547707c7840c8ccc1712402219703c0ec0493c0222770544066b874ed40a6d2e111a500d82b808e5414b91c296a3452c270a564d0e5c1c29424c527488a4c4a14949210a828522298a425114809e28f93403b030738130fe02210c03c2840680780b02e01229895e5302ba9ea5552f0a922e14a3e028c6164e89bc9b0b112a0a624ca5e1593d42aa9504e44c094a52118ea02129203e2f6074a460d88981928f02e148054a3a0981301128e01e4bc03a74ed7144d2e2872505082b8a02541019ae28925c50d4a0a0e571400a827c85c45b0907bc110f7c1a27c84e4f30848b60e94541b18502a26e04c2c20682940b111b5c5134b8a24941418ae27f95050e6b8a1ad40a6d2e28295c4fe2a09f0170c241c13603426d0489f01393c82122d03a3dd06c6120a9428130b001a0a402c08ed714212e283a505062b8a0a541405ae2803504ff4b89fc940360ae27b85c15f05014409028c0a27b84e4f10848b20e8f701b18402a26b04c2be0693ec0b001b5c4f94a09f05413dc2800185c4f58bc981175469af28cb5d5186b8960d65001aaa8bb525166a2a28d414452f28825d50f4b86e2964a5d2aa8625250b4a2a12941410af28195d5022b83b4564358aaa7e9524fc2a29f45413d82f27605d4f609c9ea1253bc212768414580747b60d8c1c1513502615e034142058e841a26b8244c50289ca0d0878122620144e40689ac09010c0a279b504f24a09e25413c02e2718344d50489860513b82e0018543f80889be0f13681a26882c4ca0487441011c81e1e083039c0989bc0f13641a26802c4c904897e070e85202729404e408097e12938c2323903e4e206465c0b891c110c901e0750249be131378221420344cf0589900908801819582c2460409b41313642210c03c4ce05898e0912f80e26ba4021e2809ac1012f82526a84646f07c7800c8cac1726a02218f03c0e8049344262680444cf07899c0d02e01202302018c0380e6041328262648444c807898e0d00f01625e81c4c548098850010c2025e84a4c308c8d80f8efc1919402e2450443180793080925f8444be06897a09000c0a27595d4bc2b49de5593b4aaa3594e3be28464e4f8910990c592e0722449d81793ac2ea7504e4e909a9d0131118252738464e608a9c2110e582127003e4dd07a9b80f0bc01d26d8364d806a9a60d08501926902e4cd05a9980b0508152658264c604a9820900e81126001e4bc03a738d11279222421442eb4689064d12751a09e93449c4689044d0f4dae25ca5049b4689705412049a25b85039c69074ed312d11c259a344b22709624d10042e2572384ad4689584e12ac9a1ef83449a46826a4d12651a23e9344986887949111f0a22549284a8050940d107d12223d9442680685228d123c9c2449343da06860c0e099c1a13482447909c8ec10915c1d1ed0363060549460985740d0500162134987288f1238942441241f46809308e128118175a4049d2809381012689424c82849e4949369192611f172232496252922485150149ca0212e3278928060b8d1a2401344944688fe4d1259a223f2443c528892a4f124c0c248b4448648801651027812247a3848e46819c4d0f641a0ae02809d04813e0511e02723a8424560747b20d8c141513302615c0349160580dd261c9a3c48925091049002da023f13848626027a90120ca02410404802588fe0604d49e23e8184844949029191f91f09b23247c2528f648514c149c98214014888f24a11e01423a0344710488dc0511cc1a23802446d0288e84a11cc142389284700508dc4a11b41423b2384752708e4110f841a23782446c0289751692da2b25ab5e4b06b495ed592a9a920534e39269a94e92529920946a3d4a54749488e52891c250a3649f46a92e8d0d5118a491494902821984f52349d24613948a27090e4d92149aa3d1341b92628ee1791ac2922a84a4520927b0118e48209ec03644506a6080a8994130ad81a09c02c80c1111041e21202c35f0788460b07201e22002c43f0588440711a1a2233a444662887f41110f81e21082c1c007887a0b10f01621001c4644888c6510fb02221d83c41f0584864c07fc2622203c41e0586a40f10741621d02c41c0388c0d1117ca21f18444390788360b01c49000904c4380788520b10c89a2099243970288620910480a21802441102885e0910400a22db5045a4a08b2540f0c2e21702440f02841e0910380a2168240340288ae8e11589c1de83442c04881a050b7c1e20d02c13107886e0b1151a2229a443bb08886c0f1064161cb84845007889e0d1138162268243a203880cd70fe02222503c4490688900b111c121c203043b698888d107fd221eb84428006884e0b1058121afa3444026887e0d10f49a21e0343524688740d0b7d1a21b93444169c87cd090ed1e9ac23543927a8704d50d81e9eb8352100606440b09081010583c42605882a090e0c0e218a4043028085e10083c9421682843209485c1190b01f1c183232205c8560886180f03801241b498852910048a21eb04442707884c0d02d012211a341c82688440d07009a21003441d4688380d10691a09893442469c842d0907d1ea0f23541b27a3824d50641e9eb0350360403060701bc0820b03c41506805e0b0e080e2092404112808201010389401a02841309481e1190341f1c103231f05c48208860c0f2060123842888d31791962923134d46168a8bc93517522a2e15a4582ac8aa539148a69ea94538128463c4f8900990c112e06e2448a21791302d2258564460a488a118f5422a2183e44207a86a0f0b641d21a03643306a8540d081c1921402e42505a8300b04ac1520b82641404a8160900b41120501e38103a7720c1019ae202a5c4044a0806571008a820085c3b806076e0c0fe1a21ffa383fe4687fa4e0ff09a1db0403df0687f4d30ea4181fc3503f74a07ec540fd4281da8301f36887e64e0fc89a1da04028e0683e6930fbc9411f8303ee0504f8d10fb12618e83c204040766080029a21f52383e94687641003341a00514c3e62780da080f940c058a443e32983020b00a8081f084c3a90607bed40f79281ee9503dc0a0006930e111e1ed1283d9050006130f5c1e1eb02c38403881117901e2d2004563fb8a47f2d68fd1ab1eab4e38569a7e2934d9124944a453f04827da8e4fad189f414d1cd292190514f9ca09f21393e22627c0168f6c2b1ec04e39509a7b00f8f541c9de0323ba0627560c0c681711e82217e03c0d6048ee4a61e98443d16887a0910f3ca21d38443cd48879851098c9a1000442642886064e0f28261028303c868878e5102689200984409b2882b44a0f14260158203b9698786110f04a21e01343bf248744050ef4261dd84c3b846876e4d0e841a1da9342cc0687668d04681a1d89283b005075c8d0eb49a1dcb4e3b66847688f49911a9d913d09b26a752128e78231d783e3ac07a71c0b8810111c401e02a024752510e801a1cf8343a1480740500e7c201d3b503a64b874a940e90ae1d19503a20a073c0d0e70261cd83c39a0687320b0e60121cb81c2134705228d00dc9c067134394688726910e10a200184438f0685984f0e3c0c10024c391250720490e38221040283890682340f0e241600994c38b2787144d0e202201701820b0785000d00bc1605a0243842887064d0e08920018143d28bc79d148f2da69e4b453c649a788914f08af1df15239229a702528ef0a31dd1453ab2886044e89849b0ac92a09824c754178ea02d1ce8563960a472a138e48269c683e2c60747180d8804191c382e11405470c09809c111c281e38103a6c0d108611a1a013435f46867e490d791a08612435d46867c490df9a812ca5c35c4686fa540cf4921be05035b468212490d691a19e1243594884a08d0de89c19d9243790706c6d1082d1a19d13431d088430920dd5261ba2442234786e64a0dc89214c05c36f4986dc910db4941b612426d04864c120c70221470341ff4886964a0d149213002433509c664108c981d1b40363010544c00985600d04b8161ff4886cc4a0d949213482420b4806b28f0d8d1810024c1fd4786944a0d10921afa4035e2806ba100d6c941ad0283604946b8918d651f1ac23235325269a484bf8148fe8212004984268f0d58941aa9243522786a0060d491a19c924350468670490d4da219ba343512984964d0d3c0c1a6b443424680124d0254121a5a4c34a48818849097c120ab82809404812c050cd0271988423250746360d8c001512f82615703468e058d14a61a21440242783f84b00251819b92834224067e900430a019f0401092506780a0ce49e19c01834029467a518cec9f19d13233725c204488bf40c8fe01129828866a4f0cd00c19803432d048654050cbc1a1960243290286604f0cbc0c19693c32c0306544f0ca40c19924c33125065c110cac1a138024328028648090c840a1918243200286484f0c8c0c19093c32003064c930c949419103426204863e050c751814714c31c278636060dfdad1bdb5637869c6eed08dd92f1b8a5a3704ac6d6948da9271b4a4d3674986c8928d89231b0a453574886a8908a851f0fda3d34e2726984c4308969a492a34825268c4a0d0c931a0925336248334484ccc2f19385231e094634118bfc1d17e03925e06c3f60c497813162825156034126058a6c2217603c2bf0585d60f0af81617503c1a80585d20f0af40e18bb4431646862a4d0ba0261438342bc0585ce0f06941617303c2bb0386268d0c489a17284c27b0685740b0c0c9814884c2ef0785720b0b8c1e15c02c2e207856e070c3da21871342e10984e40d0ad8160351202e00980200f0b101616a9442ae24842a050b501a1568142d3068558050b481a15581430a6a0612940c20a812485c2d1068554050b401a1548142cf068550050c191c1829382ce08847c0d0a9c0a181b442d828854c4908200a1660342a50285960d00840a180a4c3002505941108f0121520142df07856a0b0b781e08002c2fe6885fa8d0b742611d0342b405842a120be82617c8442f80585ee0908800e14da5c2f40985e6110a101a17902c2f10485ca920bbd22148a341f30884ba0d0b08161588242eb4685d4490ba4121739242e60485c68d0b881216fa342de2485d8938ba121172a3a2e446c5c24b4b809296e82d25d04a3e6110a001a16d82c2da048410100b381e16c0301f40985820b0ac0120f881c2d44805a6500b48201681282cf0505984f0b2c0c16a84a2d108c59c0f8b341916502e1f10442f20781a4090fa04c2c805858e0908400e0f80202b64785888d00409a16104c2c10884b80d02b41215f2341a824857a0906949215d8242b846856e090ad51a0801242bf49c578908ae91d15ca362b625a33c494ad01692e0250230402ec0701a00815884c2b00880380b07bc0e156a402ac280556100aa4941540282a5278042060ab8251550462a707c54c0c8a90170f782217603c5460487c09a18c35e3146a4622d28c41a3186a3d30c46a616568c1cab18214e3022845fe4f8bf09e92d9351ee2642ea4b819c9117d85e2f60b45ea158bc02917704e2ed09a5b8130b642516b8462d608a592110b182116283625b06a5860b8b001695982c0fb054564098abc1295102401a0445420787b80e91c02029d6b8538d40a6d2e14d15c2992a05301708dc1011b02029649852a910a111a14a12829324846a0c09b412148a3429027051e4d0a381a11a0202804685184a0a2c921198302690484f88c09901811902028747844e080a15a81422502832a0504140a011c13f9382630804fc0e080c1013e34427b4784d0130808101188202794984f09100211a1180300c30484ea5300209e0330202740301548d09c89e0ba02c0170204e00f089c1013735026d4a04d85409ac28134a382682804ce4e09981c1018202646884c69309881e1010202602980064f07c09612f81825d0980060f0970160f801c29f6bc53cd68a5dab14935228d69c514d28a25a31443422864b45029589f52713d24225b47c3e48f49dc9e8d81390be26a4ec4c49cc9493892126f0b44d41589942713084225e07c3fc0f49781712d82923b0444720848a4100b881e0640244705309642212bb442564684aa4d088c1a129a3423f2884a44d084c1a1191442432704a01308141812734424d2681224900441a0491341552504960f00601011c24c24908848e5109189a122924220028486d109089a1209242100284649108fd1c11f04c2040604780f08e81e11ba3423624843c0908d0921078242030404628d039c1211793c22e0304588d08ac9211c24e2354844668e88c91b11812d09224a44e1288702310683e20206445a0b88a8168fb81e01702444e4d087c1210e82421f48043c50087420112b5c2246a0446940888ae1109502200a04380908682610c84421807842e0b08581210a81c20e04841e4a083814109a382122704224d08401c10682420b0784140b08241210401c2032684068d080d1a102b442042884044d0801260ffa440242501884907f5a20fe2341f02680060d07e0120fc03c0e70583f45307e4a200893c1f70680360607d0260f984401c05815a0907c4a20f81341ef248006050961af12a35225169449ed189311e9252352482bc488548900a511e9461fb27a3dc4e88ec9b11c9352292682a84a823c9311405e2260b44361588502910604e20709440c118804210ff03e1fb07a3ec0b8388150fa8260140443e40787b80e8e4a441aa4680784907209a0d49241c72683504907189a0d39241eb6a03d494021cae0e29341a62483d21407109a0d29241c326834849079d1c0e114407e2683464907981c0e62441a246805e490604220e01341a124837e4d0680920f1a4c1be28833e4d01e4920f10281bd48835e8d0070920ba03403c2903bc530774a20ee13c1db26808e4b035c2e0ec14c1d72883ac4f07549a05181418a0903001103341a0091441b727835a4d02380a0cc84e1960843140e87441b0be82a17304c2a60682380b0091441cf27839c4d027c0a0179401c22783984c004ca60db13c1ac26801c4b0721200e39401c60803884a070c140e013c1bf030392528714a30e113e1c126437c4b86f4910a801900e0220265306ec9e0dd1340372582f80e05c81a0618241b729836c5100409a04681419809c32a1086241d0bf83617c0543680985480d0468161b22983625100409a04b01401c26033e4b06bc900d694c1ac2880224f0034960d4a401a828034e100694940d20281a12783400606a8a50d31461a327c3444c867c970cf12214f03201a044670a60cd9440112780484b035c220cc83c1980583280d0644120c70141930683200906340a0ca03c1930583220f0640160c703c18d05832c5306549e0c904418f06831809029c0a0c402418502830e0906100a0c403c18705830a0f0610160c514c18927830c0d060c1204c81418126019a1306001e0bf82c17b0682f00505e81a0bb81417b0782f40b05e01e0bb82c17d2982f84f05e4220bb0240900282e84805cc2606183c1720583d89687a12b0f2a4e1e44843c28f8781190ef95e1da2b43b2558750a90e994e1d229a3a0530734a50e59461ca28a3785106e4a10dc13e1b527a3664f06c09d0d71361ab26a33a4d06689907012e00c25a32e17862c290c104a17e08c2ea0e85c41b0a882a14e052118098030108460160e102a1b01104f81e08702c13d07821a0b04f01e08602c13b0782160b05b9220b6a3416c2482741304281e05e0241390782120b04e01e08402c16a4682d24904dc2608383c0b00482b44c0338260a083c10605826a0f04141609a03c1040582cc9105949209984c1030781520905549009904c0c40782260b049ca207a93403b02824c0d03d0120928340f30482480d03c8120b0b501604a02be5401dc2e0918340f10482440d03c0120908340ef0482ba8e05709c09004406c0681dc090569220951440ed26805c0504781a07602411d0681d6090561260ab92811c0881d40d0194120aaa3411b2881f44d006c0a08d0340e80482320d039c120a994c1522782301103981a0318141310782020b04c01e08002c15048829e8d04bc2607f83c061048076120530260a584414a0782920d01180e06c15c14609828a1105101e0a18340b804826e520504a206713400a0882220f03e01a04582413d2682784904ec0a09c92413802826a4d04d00a09893413024827c5384e8a109b93a13626c2664a84c89309781d08b02a0141104b41e0960340b404805c1004801e09503000b0982200f03dc1a00301c12648024a5004902009112812105023c4f04740c08d03c11905824e12848c2309003e11f0642380b846c1108c01e0060240161304581e08a8340360382064e044c9a0621241110982201100201a04502410d26821849042c0a08492410802820a4d04100a08093410024821c538428a108393a10626c2064a84089307f81d08a02a1fa1303f0220040340ad0480360c03a81607d0200f80981ee1100241e00281c0f44801e65003c8200781280ef0501d84f03ac0c07403c0e70581ea1283c42307703e0ed0641d40b83a41107301e0050241c813038c2200483c023038008040010920b7a5e16b4a42d092859d230b223a16346c2c4568578ab0ad94e1592842ac4f8550990a892e14e25a112494008910a685e1480b428e158508290a004e13f09a25c1304ac2509484612808a22e1104502108903e10f07a1fc0f03ec1d07c8360f606a1ca0d03881907082608904a1c00780080e82f8100dc6b81b6d403692e06ca500d82b81ae1701780802e8100d52981a851034c9e0691340b82480b808028c0a0682380cf46819c4d03341a02d8100cb2781944d02d09202d02009f0281624c026c1802c8100c649818a91031092061824058020182530300a205692405704012c0502a8900490200560201784b01340805d3500b94a01705402dc2805aa380b42701341002cc1c0148100b14881604b0278260140100ae49815a4a0244180560280160201548d02a49604a83c01502014e0b013408052b500a44a01465402882805023809f27013c1002741c01481009b4881345302641601401009749812c4a02541804a0280160201248d02449e04802c01502011c1302341e00182c0040381161302281e00182c0040381bc9783752d06b2560d14a4198938325250642460c74841848f82fd1d05f2360bd4641765682d8ab05914e0af2841564f82a09904492e00725a14c1682842b04e04e0980841260f823c1904602e00f05a1180782240c83101206002209e04017ca60438440854881088d020c920238240814680da5102009201b8240592880e24e01f82601583007c4880cc4d01ec920120240562680d44a01e41e00c02005f2980ee1101d4a203a13407324808c0501c52203813406f24806c050164a203693806c0980540c01a91a0349440682480460501589a03312806507802e08018c1603082c05e2680ba49010c0a02d9240340280520801609a0108140160200aa0f0150160291340512480be538170a102d13a05926c0ae4a81589302684a04208c0660f80a01901002e0150440a60781400e82692404502808805011520022140043080096d70129a8024a5c0484a008e5401182802101404009807e1100f81e01e83403c0580760700d40a01a9280340500728e00e11a01b9380360700660500c41e01803402f05805c0700a49a0149340292680569100a8a20141240220280444f00840c01324c0254880484a008c1401001401e09803a1100701600d81c01624802c4900589200c23401726802a49004ca60091440112780204d003922006a3400424800609002c260050440090780100d0018a20029340042480060502192f04125207f4940fa9181e91d03c2360762bc0e45481b8a50359460672740c84d80309680112a06224c0c049413c9202705e04c0b40821580e82901904e02d09405811809c2100f83e01a0740320d80501900782e00c05a00e0780080ed1cb4fa226973fcd1e721a1cdaa4f99e4972f291e50921c85a3f8c44771328de13d19c1e14f825296ffe51df1ca1bc193f72f276dfe4ddac099b2c12f5ee256b5a49d51491a9904f51b0969e811d2ec21a3503f4090767a80dce001998c82f2a00564b409c7b4118b801f0df03611005c0040980001f 19 6 11 12 7
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 2636 (dagTraceF m_25 s_25 7 f_25) l_25 0) s_25 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 64 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_2 : treeBlockF 64 96 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_3 : treeBlockF 96 128 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_4 : treeBlockF 128 160 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_5 : treeBlockF 160 192 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_6 : treeBlockF 192 224 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_7 : treeBlockF 224 256 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_8 : treeBlockF 256 288 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_9 : treeBlockF 288 320 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_10 : treeBlockF 320 352 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_11 : treeBlockF 352 384 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_12 : treeBlockF 384 416 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_13 : treeBlockF 416 448 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_14 : treeBlockF 448 480 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_15 : treeBlockF 480 512 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_16 : treeBlockF 512 544 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_17 : treeBlockF 544 576 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_18 : treeBlockF 576 608 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_19 : treeBlockF 608 640 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_20 : treeBlockF 640 672 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_21 : treeBlockF 672 704 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_22 : treeBlockF 704 736 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_23 : treeBlockF 736 768 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_24 : treeBlockF 768 800 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_25 : treeBlockF 800 832 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_26 : treeBlockF 832 864 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_27 : treeBlockF 864 896 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_28 : treeBlockF 896 928 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_29 : treeBlockF 928 960 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_30 : treeBlockF 960 992 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_31 : treeBlockF 992 1024 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_32 : treeBlockF 1024 1056 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_33 : treeBlockF 1056 1088 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_34 : treeBlockF 1088 1120 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_35 : treeBlockF 1120 1152 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_36 : treeBlockF 1152 1184 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_37 : treeBlockF 1184 1216 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_38 : treeBlockF 1216 1248 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_39 : treeBlockF 1248 1280 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_40 : treeBlockF 1280 1312 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_41 : treeBlockF 1312 1344 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_42 : treeBlockF 1344 1376 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_43 : treeBlockF 1376 1408 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_44 : treeBlockF 1408 1440 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_45 : treeBlockF 1440 1472 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_46 : treeBlockF 1472 1504 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_47 : treeBlockF 1504 1536 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_48 : treeBlockF 1536 1568 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_49 : treeBlockF 1568 1600 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_50 : treeBlockF 1600 1632 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_51 : treeBlockF 1632 1664 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_52 : treeBlockF 1664 1696 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_53 : treeBlockF 1696 1728 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_54 : treeBlockF 1728 1760 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_55 : treeBlockF 1760 1792 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_56 : treeBlockF 1792 1824 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_57 : treeBlockF 1824 1856 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_58 : treeBlockF 1856 1888 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_59 : treeBlockF 1888 1920 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_60 : treeBlockF 1920 1952 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_61 : treeBlockF 1952 1984 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_62 : treeBlockF 1984 2016 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_63 : treeBlockF 2016 2048 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_64 : treeBlockF 2048 2080 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_65 : treeBlockF 2080 2112 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_66 : treeBlockF 2112 2144 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_67 : treeBlockF 2144 2176 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_68 : treeBlockF 2176 2208 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_69 : treeBlockF 2208 2240 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_70 : treeBlockF 2240 2272 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_71 : treeBlockF 2272 2304 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_72 : treeBlockF 2304 2336 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_73 : treeBlockF 2336 2368 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_74 : treeBlockF 2368 2400 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_75 : treeBlockF 2400 2432 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_76 : treeBlockF 2432 2464 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_77 : treeBlockF 2464 2496 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_78 : treeBlockF 2496 2528 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_79 : treeBlockF 2528 2560 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_80 : treeBlockF 2560 2592 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_81 : treeBlockF 2592 2624 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_82 : treeBlockF 2624 2636 (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nj_25_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_1 (fun _ h1 h2 => treeBlockF_at nb_25_2 h1 h2)
theorem nj_25_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_2 (fun _ h1 h2 => treeBlockF_at nb_25_3 h1 h2)
theorem nj_25_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_3 (fun _ h1 h2 => treeBlockF_at nb_25_4 h1 h2)
theorem nj_25_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_4 (fun _ h1 h2 => treeBlockF_at nb_25_5 h1 h2)
theorem nj_25_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_5 (fun _ h1 h2 => treeBlockF_at nb_25_6 h1 h2)
theorem nj_25_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_6 (fun _ h1 h2 => treeBlockF_at nb_25_7 h1 h2)
theorem nj_25_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_7 (fun _ h1 h2 => treeBlockF_at nb_25_8 h1 h2)
theorem nj_25_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_8 (fun _ h1 h2 => treeBlockF_at nb_25_9 h1 h2)
theorem nj_25_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_9 (fun _ h1 h2 => treeBlockF_at nb_25_10 h1 h2)
theorem nj_25_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_10 (fun _ h1 h2 => treeBlockF_at nb_25_11 h1 h2)
theorem nj_25_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_11 (fun _ h1 h2 => treeBlockF_at nb_25_12 h1 h2)
theorem nj_25_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_12 (fun _ h1 h2 => treeBlockF_at nb_25_13 h1 h2)
theorem nj_25_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_13 (fun _ h1 h2 => treeBlockF_at nb_25_14 h1 h2)
theorem nj_25_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_14 (fun _ h1 h2 => treeBlockF_at nb_25_15 h1 h2)
theorem nj_25_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_15 (fun _ h1 h2 => treeBlockF_at nb_25_16 h1 h2)
theorem nj_25_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_16 (fun _ h1 h2 => treeBlockF_at nb_25_17 h1 h2)
theorem nj_25_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_17 (fun _ h1 h2 => treeBlockF_at nb_25_18 h1 h2)
theorem nj_25_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_18 (fun _ h1 h2 => treeBlockF_at nb_25_19 h1 h2)
theorem nj_25_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_19 (fun _ h1 h2 => treeBlockF_at nb_25_20 h1 h2)
theorem nj_25_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_20 (fun _ h1 h2 => treeBlockF_at nb_25_21 h1 h2)
theorem nj_25_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_21 (fun _ h1 h2 => treeBlockF_at nb_25_22 h1 h2)
theorem nj_25_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_22 (fun _ h1 h2 => treeBlockF_at nb_25_23 h1 h2)
theorem nj_25_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_23 (fun _ h1 h2 => treeBlockF_at nb_25_24 h1 h2)
theorem nj_25_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_24 (fun _ h1 h2 => treeBlockF_at nb_25_25 h1 h2)
theorem nj_25_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_25 (fun _ h1 h2 => treeBlockF_at nb_25_26 h1 h2)
theorem nj_25_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_26 (fun _ h1 h2 => treeBlockF_at nb_25_27 h1 h2)
theorem nj_25_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_27 (fun _ h1 h2 => treeBlockF_at nb_25_28 h1 h2)
theorem nj_25_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_28 (fun _ h1 h2 => treeBlockF_at nb_25_29 h1 h2)
theorem nj_25_30 : ∀ i, 0 ≤ i → i < 992 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_29 (fun _ h1 h2 => treeBlockF_at nb_25_30 h1 h2)
theorem nj_25_31 : ∀ i, 0 ≤ i → i < 1024 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_30 (fun _ h1 h2 => treeBlockF_at nb_25_31 h1 h2)
theorem nj_25_32 : ∀ i, 0 ≤ i → i < 1056 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_31 (fun _ h1 h2 => treeBlockF_at nb_25_32 h1 h2)
theorem nj_25_33 : ∀ i, 0 ≤ i → i < 1088 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_32 (fun _ h1 h2 => treeBlockF_at nb_25_33 h1 h2)
theorem nj_25_34 : ∀ i, 0 ≤ i → i < 1120 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_33 (fun _ h1 h2 => treeBlockF_at nb_25_34 h1 h2)
theorem nj_25_35 : ∀ i, 0 ≤ i → i < 1152 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_34 (fun _ h1 h2 => treeBlockF_at nb_25_35 h1 h2)
theorem nj_25_36 : ∀ i, 0 ≤ i → i < 1184 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_35 (fun _ h1 h2 => treeBlockF_at nb_25_36 h1 h2)
theorem nj_25_37 : ∀ i, 0 ≤ i → i < 1216 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_36 (fun _ h1 h2 => treeBlockF_at nb_25_37 h1 h2)
theorem nj_25_38 : ∀ i, 0 ≤ i → i < 1248 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_37 (fun _ h1 h2 => treeBlockF_at nb_25_38 h1 h2)
theorem nj_25_39 : ∀ i, 0 ≤ i → i < 1280 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_38 (fun _ h1 h2 => treeBlockF_at nb_25_39 h1 h2)
theorem nj_25_40 : ∀ i, 0 ≤ i → i < 1312 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_39 (fun _ h1 h2 => treeBlockF_at nb_25_40 h1 h2)
theorem nj_25_41 : ∀ i, 0 ≤ i → i < 1344 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_40 (fun _ h1 h2 => treeBlockF_at nb_25_41 h1 h2)
theorem nj_25_42 : ∀ i, 0 ≤ i → i < 1376 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_41 (fun _ h1 h2 => treeBlockF_at nb_25_42 h1 h2)
theorem nj_25_43 : ∀ i, 0 ≤ i → i < 1408 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_42 (fun _ h1 h2 => treeBlockF_at nb_25_43 h1 h2)
theorem nj_25_44 : ∀ i, 0 ≤ i → i < 1440 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_43 (fun _ h1 h2 => treeBlockF_at nb_25_44 h1 h2)
theorem nj_25_45 : ∀ i, 0 ≤ i → i < 1472 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_44 (fun _ h1 h2 => treeBlockF_at nb_25_45 h1 h2)
theorem nj_25_46 : ∀ i, 0 ≤ i → i < 1504 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_45 (fun _ h1 h2 => treeBlockF_at nb_25_46 h1 h2)
theorem nj_25_47 : ∀ i, 0 ≤ i → i < 1536 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_46 (fun _ h1 h2 => treeBlockF_at nb_25_47 h1 h2)
theorem nj_25_48 : ∀ i, 0 ≤ i → i < 1568 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_47 (fun _ h1 h2 => treeBlockF_at nb_25_48 h1 h2)
theorem nj_25_49 : ∀ i, 0 ≤ i → i < 1600 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_48 (fun _ h1 h2 => treeBlockF_at nb_25_49 h1 h2)
theorem nj_25_50 : ∀ i, 0 ≤ i → i < 1632 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_49 (fun _ h1 h2 => treeBlockF_at nb_25_50 h1 h2)
theorem nj_25_51 : ∀ i, 0 ≤ i → i < 1664 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_50 (fun _ h1 h2 => treeBlockF_at nb_25_51 h1 h2)
theorem nj_25_52 : ∀ i, 0 ≤ i → i < 1696 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_51 (fun _ h1 h2 => treeBlockF_at nb_25_52 h1 h2)
theorem nj_25_53 : ∀ i, 0 ≤ i → i < 1728 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_52 (fun _ h1 h2 => treeBlockF_at nb_25_53 h1 h2)
theorem nj_25_54 : ∀ i, 0 ≤ i → i < 1760 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_53 (fun _ h1 h2 => treeBlockF_at nb_25_54 h1 h2)
theorem nj_25_55 : ∀ i, 0 ≤ i → i < 1792 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_54 (fun _ h1 h2 => treeBlockF_at nb_25_55 h1 h2)
theorem nj_25_56 : ∀ i, 0 ≤ i → i < 1824 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_55 (fun _ h1 h2 => treeBlockF_at nb_25_56 h1 h2)
theorem nj_25_57 : ∀ i, 0 ≤ i → i < 1856 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_56 (fun _ h1 h2 => treeBlockF_at nb_25_57 h1 h2)
theorem nj_25_58 : ∀ i, 0 ≤ i → i < 1888 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_57 (fun _ h1 h2 => treeBlockF_at nb_25_58 h1 h2)
theorem nj_25_59 : ∀ i, 0 ≤ i → i < 1920 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_58 (fun _ h1 h2 => treeBlockF_at nb_25_59 h1 h2)
theorem nj_25_60 : ∀ i, 0 ≤ i → i < 1952 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_59 (fun _ h1 h2 => treeBlockF_at nb_25_60 h1 h2)
theorem nj_25_61 : ∀ i, 0 ≤ i → i < 1984 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_60 (fun _ h1 h2 => treeBlockF_at nb_25_61 h1 h2)
theorem nj_25_62 : ∀ i, 0 ≤ i → i < 2016 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_61 (fun _ h1 h2 => treeBlockF_at nb_25_62 h1 h2)
theorem nj_25_63 : ∀ i, 0 ≤ i → i < 2048 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_62 (fun _ h1 h2 => treeBlockF_at nb_25_63 h1 h2)
theorem nj_25_64 : ∀ i, 0 ≤ i → i < 2080 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_63 (fun _ h1 h2 => treeBlockF_at nb_25_64 h1 h2)
theorem nj_25_65 : ∀ i, 0 ≤ i → i < 2112 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_64 (fun _ h1 h2 => treeBlockF_at nb_25_65 h1 h2)
theorem nj_25_66 : ∀ i, 0 ≤ i → i < 2144 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_65 (fun _ h1 h2 => treeBlockF_at nb_25_66 h1 h2)
theorem nj_25_67 : ∀ i, 0 ≤ i → i < 2176 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_66 (fun _ h1 h2 => treeBlockF_at nb_25_67 h1 h2)
theorem nj_25_68 : ∀ i, 0 ≤ i → i < 2208 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_67 (fun _ h1 h2 => treeBlockF_at nb_25_68 h1 h2)
theorem nj_25_69 : ∀ i, 0 ≤ i → i < 2240 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_68 (fun _ h1 h2 => treeBlockF_at nb_25_69 h1 h2)
theorem nj_25_70 : ∀ i, 0 ≤ i → i < 2272 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_69 (fun _ h1 h2 => treeBlockF_at nb_25_70 h1 h2)
theorem nj_25_71 : ∀ i, 0 ≤ i → i < 2304 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_70 (fun _ h1 h2 => treeBlockF_at nb_25_71 h1 h2)
theorem nj_25_72 : ∀ i, 0 ≤ i → i < 2336 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_71 (fun _ h1 h2 => treeBlockF_at nb_25_72 h1 h2)
theorem nj_25_73 : ∀ i, 0 ≤ i → i < 2368 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_72 (fun _ h1 h2 => treeBlockF_at nb_25_73 h1 h2)
theorem nj_25_74 : ∀ i, 0 ≤ i → i < 2400 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_73 (fun _ h1 h2 => treeBlockF_at nb_25_74 h1 h2)
theorem nj_25_75 : ∀ i, 0 ≤ i → i < 2432 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_74 (fun _ h1 h2 => treeBlockF_at nb_25_75 h1 h2)
theorem nj_25_76 : ∀ i, 0 ≤ i → i < 2464 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_75 (fun _ h1 h2 => treeBlockF_at nb_25_76 h1 h2)
theorem nj_25_77 : ∀ i, 0 ≤ i → i < 2496 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_76 (fun _ h1 h2 => treeBlockF_at nb_25_77 h1 h2)
theorem nj_25_78 : ∀ i, 0 ≤ i → i < 2528 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_77 (fun _ h1 h2 => treeBlockF_at nb_25_78 h1 h2)
theorem nj_25_79 : ∀ i, 0 ≤ i → i < 2560 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_78 (fun _ h1 h2 => treeBlockF_at nb_25_79 h1 h2)
theorem nj_25_80 : ∀ i, 0 ≤ i → i < 2592 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_79 (fun _ h1 h2 => treeBlockF_at nb_25_80 h1 h2)
theorem nj_25_81 : ∀ i, 0 ≤ i → i < 2624 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_80 (fun _ h1 h2 => treeBlockF_at nb_25_81 h1 h2)
theorem nj_25_82 : ∀ i, 0 ≤ i → i < 2636 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := block_join nj_25_81 (fun _ h1 h2 => treeBlockF_at nb_25_82 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 2636 → (dagCheckNodeF m_25 g_25 bds_25 2636 (dagTraceF m_25 s_25 7 f_25) l_25) i = true := nj_25_82
theorem lb_25 : LowerBin m_25 s_25 g_25 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xf0f0f0f0f0f0f0f0
def s_26 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_26 : Nat := 0x10101010101050
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 6, g_5)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
def l_26 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 0 (dagTraceF m_26 s_26 6 f_26) l_26 0) s_26 6 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_26 g_26 bds_26 0 (dagTraceF m_26 s_26 6 f_26) l_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xf0f0f0f0f0f0f0f
def s_27 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_27 : Nat := 0x101010501050507
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 6, g_11), (m_15, s_15, 6, g_15), (m_20, s_20, 6, g_20), (m_6, s_6, 5, g_6), (m_7, s_7, 5, g_7), (m_0, s_0, 4, g_0)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_15
  · exact lb_20
  · exact lb_6
  · exact lb_7
  · exact lb_0
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_27 : Nat → Nat × Nat := unpackForestF 0x169fe7929f3c14f908e7cc27de6019f209cf920fbc905de4039005a5f8a4a7c5053d4a51ef895f84513be247df02befc2277c08fa94a1dd93eeec0cf52547b425fdc144ed091f6806fb5089da013ea4a87620fbb105dd4851ea817f5c113aa047d501feac2275404fa90a000b47e9894f4c0a790473d092be8491f420afa1047c8238e789f73c06790273cc92fe6491f3206f99027c8138e581f72c0bb90073c882fe4411f2207f91027c8038005a1f1c0678b253c602ee2c1480292f894d9ba24bdd123f0a50785083ba246dd095f0251b81033ba129df4b66fa5537d031ba123dd015ef211b7905dba029dd4366ea15375059ba02300521ea517b7148ba9452dbe366a497f6c293b6049d492f6d4953524a7b2a5dd9522eca4a765053a9252d4895ebf17b5f8a5af95ed7c0cea44a75c2a9ae018d4891ea40af568bdab452d582f6ac0bb52053a9854d4c166a408c01477a8019d3494e9c0bb4d05200a33d2c14e904fb4907da4019004a5e50d4f43471a1938d0c9a650d2f412d99414bca0a3e7a9073d08394146ca09fe6cd4b366959b24acd92366c0a72827d9896ccc4aa6624f33103194133ca00de5a11b2d07d94019ca4366521532909994013004a1dfb17b2528b7ec52c851c6424e3212697eb53bf5a5e3d1b2fd2bf8da49c6c24dfa57b192a97e953c50aee285171427d8a019bf4a95fa4ff0b8bd85c52c2da9616d2b0b4bd85a52c2c14dfa4fb072a98393cc1c0c5fa4cefd03780c5ec062960217b0107d7e819bf82a5fc132fd0260093bbec14df04faf907d7c01900499cb117ef169178a48bcc0c5e2522f12892c45bbadb05d6982eb2d975960bac304b115ee569172a48b94a45ca512e50912c453b85a35c28eae10732c352b662f5bc512d98a56cb5eb65a95b28ead90732c34ab49a95ac8d2d269569246b491eda40a6584a563c5eb3ca258f14acd46963b52b1da558e97ac74a563a3db1c14cb092ac46c162260960afd84142c068b60049960af5769b2bb2995d93caec964b056eb58d95ac60ad5a856a942b50c12c157accae55a992ad2b956954ab4a655a4f2ad0312c153a60af5305769829b4c146a60a2d30512a52894c13da8ca25304b6a029950144a600d530066980314c84ca64225320f2990594c016960a9528d62944b14a048960a7d1c9728e2994713ca3ca651c062582973ec5e9f6294fa57a890313e9529f4a34fa4f67d25b3e81a9f40cd02d3a816853e8189f81e4fc0b27d02d2c14a9e9a44f49225828f3545e9dc1c4d514a756993535a9c1a84e0942702a1380509a9ab4d84f26c259360189a9a74d41065828d3414c9912a4c8532642793212c960a1cb006e5c6a52e34a971294b892a5c0bd2e0469600ccb2132590792c01300491caa4a2550492623394898ca44a64c07d26a329349f49c5124d2652602e00425c3ed4e472712383891c1a43ed2e1f4a721128908144840921f4971f8288fc1243e8ce3d0d90f84b87c23c72906392830f84687c1fc64d4a326951924a8c9234644a61f07d1686c8b42a45a0f22d0590f83387c17c4a94a254951294a894a344a4fa252650f82e88036440152200991002c87c1180210de68bd0e04579a294304e2180710c034799a9bccd2e132510982884c123cc94de6497072548381441c091e64670646c7982fc1292609292f305e81c2a3cc14e020bb010458081f4040b9e60a4f303f7e62f3f3149f96a4fcb4a7e52f3f2949f9252f303e7d42a3ea0f1f5058f303379817bd7179eb8a4f5a527ad253d6579eb2a4f593e7ac993cc0b9e70a8f384c79c163cc08c01076f1254788943c4091da466ef93177c94bb40f9db464ed93e76c993b40b8010668645f74da43a6521d5058e984874c2221916dcd6c0e6a60734b039a1b1cd0c08645771da438e921c7290e384871c2221914dc368ce1a3970c9d218d49bb8bce00446ee29376d79bb6a4dda396ec9d218d29b5498da9286dc2236a0a1b50488625b6c8143640910c4a6d78286bc1221892daa498d51286a8143540910c486d403467da934c0d19f694cfa5e68d2233e9499f494cfa4667c952188c5966a4ce134659a533449196462cb1466589eb2c4b90c2a4c445e64c2231114991268c4352621a531a9118d248c4231620af3105498827ac412e430a530ad81852c08605f60ca8300d1580292c01214302f2f65b17b098bd82c5ec0e21816d758d8bac605d5a82ea981752a0860575cc2e2da5916d0b8b68545b4262da0f16d0588605355918aac179560baab04d558232ac11565242ab04458c222ac0f55605caf84c57c222ac0b556058ad04c568222b40f15604aab84455c122ac0750c0a4a9358549242a45610c09ea615c5302629c1314c078a602c43025a751793a8a49d2314e82f28c0b13a0a49d0464e81ea740b93a05a9fb4e4fda12740b13d0789d0254ec122740750c0949bb484dca421811d238bc9a13848e29264d31236b496b504b52825a5412d0a091b564a41e2520b12903891b4e48ca0a464e5232629223848c90a18119210988e9544742623a0b11d0388604346da02180bd106a48834a4412d220909102bc88152440a5220519100a48804a4301721a1310d058860230041180517d054908294841c1e20a121050880145b3fdb01fe980ff2c07f86c3fc3000515cf96907ca483e4a41f2120f9088014533cd1c1e64e0f5088798383cc1a004d6cf007078034009a99da0e0ed0680134b3a11c1d04e0e807074034009a19c8918e447c7212a009291b9178e10886e4523712f1b8948dc47c6e12a009251b40d0d16a46c034345a51a2978d548868a52345251a2918d1254012323212919c490c84946612432119190518c827c6412d008a9175178c50885d45230c92174948ba4945fa442fc921748c8ba2bc5d1522e89f1744b4022945c03427da916c0d09f6945a12427d291644909f4945624e2bd1a158908ac4745623627d181544809f2bc5323029c9014c5109f2a45223027ca51424e0a12404f94627c968044c89c4c04e1600082f9349409568a4aa492549112c480950440105e240b61200f0900584801c0082d9151b08a8c04536022928114540020ae4405c208b2104170820a84104c2081e1040b0020a633a321fd180ce4c8670bc3385d19c268ce1186708a3b1221dc900ec088670883383e1c8260e41106707a3383c1b8260dc1106706a358441ac1a0ce0b4680883403419c0e8041486369031a5818cac00413c5d2b83004c174260ba0f05d0580104b1262f093148494642c230124990921785507824852124230920f84907a27b4e13da10920f04906a26034124168940d04903a0104a1192408c5200208e17c5e10d1c05f1484169817b5a0f1a80789403c2a01e0500bdab0700f0380581c01c0bda705e9042f47217a310cd1c05e48830470181200bc110041182d098149540a41e0520b029038010430992004c5000207e0db5a06da10369781b4a40da4a06d230365481b2940d85206c250040f8180780c02c00819806d480369401a5200d25006548032940185e030220180f00c0580601c00c290100f0080580401c00c250061180307a0182d00c0e8040c8010260001f 10 11
def l_27 : Nat → Nat → Option Nat := unpackLinksF 0xe609e600e600e546e540e540e486e480e480e3c6e306e300e300e246e240e240e221e220e220e201e165e160e160e0a6e0a0e0a0e081e080e080e061dfc5dfc0dfc0df06df00df00dee1dee0dee0dec1de25dd09dd00dd00dc46dc40dc40dc40dc40dba5dba0dba0dae6dae0dae0dae0dae0da45da40da40d986d980d980d980d980d8e5d76cd760d703d700d6a3d643d640d602d5e1d5e0d5e0d507d4c2d4c0d4c0d3c8d3c0d3a1d3a0d305d2c2d2c0d2c0d1c8d1c0d1a1d1a0d105ceb3cdc7cdc0cce7cce0cca2cca0cca0cbc7cbc0cb82cb80cb80cb80cb80ca88ca42ca40ca40ca40ca40c90ac8e1c8e0c864c822c820c820c820c820c6eac6c1c6c0c644c3b5c3a0c343c340c2e3c283c280c223c220c1c3c163c103c100c100c0e1c007c000bfc2bfa1bfa0bfa0bec7be82be80be80be80be80be80bd88bd80bd61bd60bd60bcc5bc82bc80bc80bb88bb80bb61bb60bac5b873b787b780b6a7b6a0b6a0b681b5a7b543b540b502b500b500b427b420b3e2b3e0b3e0b3e0b3e0b2e8b2a2b2a0b2a0b2a0b2a0b2a0b2a0b2a0b16ab141b140b140b0c4b082b080b080b080b080af4aaf21af20aea4ac15ac00aba3aba0ab43aae3aa07aa00aa00aa00a9e1a9e0a945a921a901a900a8e1a8c1a806a800a800a800a7c2a7c0a6c8a6c0a6c0a6c0a54ca540a540a521a520a520a520a520a36ea360a360a341a340a340a340a1cca1c0a1c0a1a1a1a0a181a180a180a180a180a1809fce9fc09fc09f449f409f219f209e289e019e009e009dc29d449d409d409d409d409d409c679c609c419c409c409c409c409c409b679b609b609b039b009a849a429a409a029a0099c299c099c0998299809980998099809980998098e596f096e096e096e09645960295e195c195c0958294e594c194829480948094429440940293c293a193a093a093a09362936093609303912f9120912090a490a090a090629060904190409040904090408fc48fc08fc08fc08f638f608dec8de08dc18dc08dc08da18d248cc38cc08cc08cc08cc08ca18c818b2b8b208b208ac3871e86e186e086458640864085e385e085e085e085a2854384e38483848084808461838783238320832083018227822081e280c980c080828061806080607f877f427f407f407f407f407f407e487e407e217e207e207d857d427d407d407d407d407d407d407c487c407c217c207c207b857933784778407767776077607741766776037600760075e1750774a374627460742272ea72e072a272a072a071c771c0718271807180718071807088704270407040704070407040704070406f0a6ee16ee06ee06e646e226e206e206e206e206e206e206e206e206cea6cc16cc06cc06c4469b569a06981698068c668c068c0686368606860684167e3678366a766a066a066a06681668065e565c165a165816580656164a664a064a064a064a06462636863606360636061ec61e061e061c161c061c061c061c0600e6000600060005fc25fc05f255f205ee25dc95dc05d825c4a5c405c405c215c205b665b605b225b205ac35aa15a815a425a2159e259e0580f5800580057e157e057a257a057a057a0562c562056205601560055e155e055e055e05583558055805580558053ce53c053c053445340532153205301520851e151e051e051a2512451205120512051205120504750405021502050205020502050204f474f024f004f004ea34ea04e244e014dc24dc04d824d804d804d804d424d404d404d404d404ca54ca04ca04c624a704a604a604a6049c54982496149604922490148654841480247e147e047e047a247a0476247604741474047404702470046a346a04662448f4480448044044400440043c243c043a143a043a043a043a0432443204320432042c342c0428242804280424240cc40c040a140a040a04081400440003fa33fa03fa03f813f613f413f403f403f213f203f203dcb3dc03dc03d6339be38c738c038c038c038a138a0380537e137c137a137a0378136c636c036c036c036c0368235883580358035803542354034a534a0346233493340330231ca31c031c031a131a030e630e030e030e02f6c2f602f602f412f402f402f402f402d8e2d802d422d402ce32cc12ca12c622c412c022c002a2f2a202a202a012a0029c229c029c029c0284c2840284028212820280128002800280027a327a027a027a027a025ee25e025a225a0254325402502250024a324a024a0248124802480230c230022e122c122c022a12262226022412240224022022200202f202020201fa41fa01f811f801f611f601f411e481e211e201e201de21d641d601d601d601d601d601c871c801c611c601c601c601c601c601b871b421b211ae21ae01ae01a831a801a0419e119e019c11982198019801980194219401940194018a518a018a018621860186018221630162016201620158515421540150214e114c11425140113c213a113a013811380138013421340134013211320132012e212831280124212401202102f102010200fa40fa00fa00f620f600f410f400f400f400f400ec40ec00ec00ec00e630e600e220e200e200de20de00de00da20c2c0c200c010c000c000be10b640b600b600b030ae10ac10aa10aa00aa00a810a800a800a800a80092b0920092008c308c008c008c008c008c008c008c008c008c008c008c0084408400840084007e307e007e007e007e0064d029e00330001 0x1b2241dc91ce26507262737b12380420c3a0e5d804685013bd498fa04a6f2242eb831f3c14ba8086f4465e693ebc899212087cc032830117589921048bca07cea032f241720c08bce473e5939bc091f900e5d204682013bbc98f8c4a6ec242e8831f1414b9a087c2289df844f0c95f8248fc0057df02340c09ddc8cbbc27d7613240810f76064ff023dc144ed4227724bfb7246e8023ed80df6804dcf26480922ec81f39a0cbb105c7f822eb822756112eb247d782feb411f5807faa027e2251ef528774547b32a175123ec028f52141cc0467f013ba498f4e4a6e7242e5831e9814b90087a4257d1923e8815f4208cfd02774232e7c9f5ce4c8fc043cf0193e808f384bf9b246e5023e680df3204dc92647d922e5c1f3900cb9605c7d022b9491f280bf93047c901fe4409ee0927a5473d0238c90a4f3a4e7982717212386c24f2a0e790070e30233e0099ee0878e0327a0113d8917180b8f4045c6929e2c149e404f676a9c4a6cd9d246ced3b22293c3141b8c90c3212785082e2821b89205448c3324a591a4ac88a570451aa225ae2031e040c9e2046a325151238dfcb66fc5533a299be81870ca02ac4c2e146316952868a543212b7a08dbc82e3c4112ac07558050ab138ddc366ec15236099ba82ce2125ec892b8748fc2246d18a9e4052ee0263c192be0094ef848e972432505385c25b840c77b057bc029dd011aaa084ef027b7a5db7c98ec44a68c242e0831d6414a940877148b6e931d8494d16485bf063ac02952410edf1b3684c1b445ddb4a4e88506dc243b604992020b7c087686d9b5254da12eece916db263b3129a2090b7a0c765052a2821b692050a8c3628bdb0c52d152961092b602bda2152a1496b780c75f032770119b49450a8e35d2a98714cd700c3765013a261acc5ed62295b28c6492a4fa94ad5c2f49014b5605c770224e80ea520a13a271aa0547f0266a60b3728bdb8452db92fed697b694a7b2252d08a9e3e52ed8263b192bd7894eb648e7c2432305385825b740c75a057aa829d4811a72084ec02675821d400c9d2044ea245a702e3a41169e4a74d052738136e418e960a5b6042dc132d241f36c0cb4a27cda033d200cdae903324719d14cb58985aa903454719c94cce09e6884e34326944130c592a6825b3162918b34ece124e7c906d42450a049cf4209cc046d348152140ce9a9672d2b384959ba46a911ee6c0a5b304272811a949e548933342d999954cc89e662060e426033920b491944054a152950a04acb82365a0f9b30643381d1a40c0ce4a32b0d995054ca4264540f3466a7a134bb451968052f132959f947cf0a36764ff3527d98133a5c9948a14e12096d883338c10e5e06f2c0339401319808da08cb1e2bb8893ea30991c4087040322d811b391964a5171027d4593238010e060645a02366930b31206468e30f2998613cc889c6424d28826165a40c211c61c5331e8d98b960c5e2ee389270c48365122c6c24c86104df0238ba6cc64aa5928cb172bb8b145c549f5104c8de0438a01915008d909028628188c5ec422961ed4b0e69586a5ec312950c8f70b052d802137408cdc4f28649984954c209e60e060dc26024920c122f60714ac74652215279ca560417a430a58083e6c0190920743803024928bfc2a5fc131ef0799345ec9229640d4f1f69763232c74afe3457b182a789952c489fe144fb062673e13290429c2212dae0666d821c140de00066fd026240116b418df60a5ab042d6132be41f3560cafa27cd4833be00cdb6d42df69164a50b41244f0572882a146148bcc0c5ead22f44913a154bc8a45e251272289389449cca24e0512ef6c177260bb4b65d85826f28975860b792459e522dd6b174b48b392c5d09228b2b173948b98a25ca122db69571b46b5d2959892ae24756295dadcaadc20e56b0626c8219840c82c046de2896fc5eb76295b8d7adb6a56aa52b2d255b48ea9629b3d945b641ca900c4d70433001905408dac8d2d76a56ab4ab25255a891ad347b6215dad8aab4e0c6d20524002197c0c828046cf28966a34b422f59d14acc6a565b4ab292f59294ac847b4a94d9e8a2b4a0c6c70522c8219780c826046c56c162260af8b4554582c20a15dc5eaaa2ecf0d36c168b6004990020b48084d6023599549cca2018062be4d95e94caf09e5764b2b98d95c460adda856c942ab2d959150ad430566572aa4d959264ac4ae560552af2995713cab40c4e6512a10314e014a949e5464b2a00314d81468c109aa046a52894d014a8ca2532052a129950144a70265361129a0794c82c0300e55657aaa2bb5494da20a555051aa728b53144a909ed444b5a20626a021a7c0d53c0669d0314c01602c08d2cd62954b149158a1ca252812268289478189b8a24da5128f29936144a492e4d6952912994813ca380c50406275289408189cca25120626e2893f8149b4a24fc0526c2894134ea05a14fe0f27e0580401ca322f51714a8a2bd44152a1ca34d65168627b4292d684189a60868403541819a000c4fa058070233db489e9244d65226728139b449dc1c4ead32736a1392509c4a84e01426e2793692c9b00c4f117a768a53a35a9bdab4d6d3a6469b078499a820c200e5e4062d002134808cd05300803133a54998a64ca4f264258cf940344980064800c09004040985a94c0d2a5f4a52f24a958ad3c650a5d0bd2005283c254b81180303a01928968264b20f2f68bf7845bbaa2bdc914ee06a56c34ab452958c92ac32bf5f95eae8add6855eac2a74b952a4ca7d1a52e7c2953c9479a4a34c650e540b71f05383425bc210d9e062680219880dcb606658026010110300a4ac4a2530992803c934164aa092532632912993490c9c5100c0312823293c9f49a4ca544672883e9301733a5022d2711b04c67018336502492711a84c8d01e4900e247068a283033c984404a22a07867020334984884a2290791402c90c1448409054040cd03033010332500cb260091205ac201000c225059200288fc12016082042a91e86c81024408d3a344931d2418a0a4c72505980446501265ca02c4102366a51ab4a8d1254669196247b191298949099204963078b114c8c03645e1522e0791682c320980d40c22a4a514a4a8a0a544e51a2627d129321a896b2c0c86c0583513c88c36444152210991002c929a9c8cd2e454a720a4b8f919b2a4c8c72451e04b8042547611e3808d1b83f8c41f4580cd550651582f8901743e08c66044ca13231891418175ff07ca50327c8170b6089922646212287022bfc0f949064f882e168113220c1902810d1387f4263f40f2190710c0345141831e501f5270fe04c30c101844c215250f803c7b4164280a2130482a020304983ce4a1ef078c71303009031a0c0bf04108254630a017c4c011240a4040164183d60b20f0510702401c104191b2050c102c5d82924bf490609292f694162c1117a04a052d9038546289917848a050bb0204580c1f28a0ca0205c2a022624a0286101ff8bcff4527f5a93f8d29fb4bcfd25250d1ebf24a5eb2425d8124ac1e286531f70a8fb03c7d4161744c04b060f945e7c6293e0949ef494f715e7b4a93d84f9eb2642592d620190720b04b278f48547a0263ce0b21d8bd0dc5285da9c2cd2e124a708a4b83519b0e4c8b92450585f8202f40c14e010a50003f7e01f3e80cd39064f982f7a8173cc08c48044040147912a3c64a1e0098ee83c76c163c4091e0262ef92976c90810061dd464ee13e76c993c28cdde07ced02e6f5a8382d218a2a0ca1484d42e28a1414a090ea82c75da43ac521310a8ea04874c2225e1112e088968444c0223a2d81d04c0e79607383639a1812c088e024864c2437ed61cb690e5248648ac392521490b0e404871c2237ad29c568ce223968918b3a54990294e193a2dc9130c175770aa8c82e05811380111c18bcdfc526f9af37ad49bc472d0a3166ca931e529bb2745a92255026a701151805c0a8226dc2201a0b1b9498dc12845c1e36c0a1b5048d42302d01034ed01a2480599301f8900280c114058d98286c812016081a646059020695a0342900b12602b9204982a0260c113058d80286bc1200e08009058d6a4c6b09424a15116078d58286a8120fe4c1a80682c1304902234c0d0b02405792068d2215c4c0ad260c71382b09034ed49a5694d225e68929342929a048ccc952630a51564c19f254c005e5ac292901292308c8d83d6709a0fe4c19a248ceb5266da53328c58a294cc14665c9eb2c4b87e244c285d5d42aa220b812044c98446449a31c91058260c69246522f325149906a4c7b4a63118b165798a2a4c493d620970ae4895209a9b84544017022089866c0c29605f8342d2181832a0550205ee2f2d31753569ac1345604a4a2850580242548125cc2a2601100d058bf16c5f4262f80b17b038bcc6c5e2302eed41764c0ba9505a8362e4141730b8b496c5c8b22e2171700a8b784c5b81e2da0b0a8260b28444c0222c00b15c048b183c57c162b609158038538205949094c04963088ad024580262be1115c098ad8445681e01a0b157038ac04455c122d68c4a5244b505e5a42ead013545094b384659822ac81116207ab082e57816aba0b15904a058225580eaa8d6153490a91585402c28811121088a702c4ac2229c1312a08894844540ae2505514f098a683c530162800b1320889f82c2909826011146058958444f4122541114069c9fb424f41e0120b13b038948444ec12295179498a4a423128c9128e179450a4a20464a022a860f54205ca082d4f816278094070449d01d4e1a426e52128090900404c1a22684e132698983504bd2825c5412d0a09583c4a81625207124460510204911c142081358bc99c524c5ad258d592869c8eb4d44ca4a4e505262729293148c90940049210980482c480aa23e1311e0588e81c46da013e4c004060069240249201a520092808cb52461a522e969164848a95e450a92265291228c0212d44429220128042788704c434163b117dd28b6e645771a29b84d49ba694da25b6c529b5c92da9486cf231654a930e5289e244c205f5fc2f2f416d740aeb6053554292a213d4b0969c84a4d823a441191c0868d02f43c1721808c020446f25038924178540c62902205c150280b61210707884a48420a408015106090828440f82207a1103c0881f84440db0204981012c08006c3fc30076110e1290628483f5a41c0960fc490621583eca40b4160fa0907c8443d42201c0f0f74707b138090261e80e0f30686d1302e0181b2900d44605b9402949802c10021078788383c01a0160c0d82605b03035d201a68c0b5280519300d42a02a10020078770383b41a00e0c00a07875a383a89c06815023098748383a01a1bc928e648c72a3e3511919e548c2294599323909513a1748b0aa0f03e050191c2110e28bc7045237d2f1bc948dd47c69a32334a9182528b12646e12a1902688e1141d07c098322a0981b40d0a4260198443601a160480af2406aa442b89815a4c0c027056120365a91aed28d64bc6a25234d251a4918cb2a45f14a2ac981a24a8970bc40052164250641182707a671242a098198490cf4a466a4a32d19178528ca28c6493e294991904b49c0ba450550701f0240c8c508861924301221484c0bf2486345e31229184948c14945f2322f4af178548bb27c519322e8968c61344608a0d83e0441915c8c0b806856a300c42216c0d0ae4605a1242b518144510b224857a342c12715c908ad474562362a8a7150508a427450936258270fe10858074180362a89014e4d0a724054230298a21488c0a2270509202dda916ad28b34a458a4a2ad18152578a52a45194a280a313e4b4950bc3f05215c2505e1182607a4ea60270b01261a07c0c04d2502581012c480908bc3e45d111a6932d149849210a4125c9112a088880a81f8440381e1265b0920784882c2400e11d1b08d8c04636022d281145407d0d8438502202e0f85b0872c84305c2142a108130830784102c1fc980f0110770683fa301d82207e11073078378341c81e0dc0d06c0583481c1dc100ee480782443b0221cc260e41106f098370440381e0d60b068038360441ac1a0d211068068402321f8990fa1787c0ba3d84d150250f41187908a3a8441d01f0e20f4700783683502c190d40b46703a32b481912c0c6560610b0298440b4220c00f0600981d0440e422070110612b81b95417c260bc0f05d0582803c1042209e0f0582602c2300fc220aa0f03a0882834e13da10140f04c0582501c0e4220980d0380882503416e2f0b5148594642b9321582f0a81485308c1b8451481f0a20f44e0782683501c190960b44903a23a48118a406e1202c0801fb4410d1c082d303f6a01f2500f4a80781403a0781c82c0e00e0664c03106019a380c0100628e0302402245e10a29080d683b6ac1bb4e0a5a6840924364821aa390d1188644882f0441684c0281e0585502b0781502c0a40e04e90026280028400391a0148d00e49005240091ad046d08224bc10a520812503e9180547a0f152074a50381481b0940294c0641e0300b00f0880703c034160180700a0780482c0200e02cd48156940a25204d25024548112940805e02c2900e1280608c0283d010168060750a8be8245b3fa2b9f114cf26b677b533b1a59ced0ce34a46da4a3411918e548b92944f13226c2f9281788f0b644857204298cc1486209e2e04b1202508a11c2e08c140430941f8340f81706601032f45a7f8ed2fa868fc7b43e2925ee690f51477a6233d1ca5e4e50efc2777b93395c91c9612e1e086f283b76419a1608c010260001f 16 5 11 10 6
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 978 (dagTraceF m_27 s_27 8 f_27) l_27 0) s_27 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 64 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_2 : treeBlockF 64 96 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_3 : treeBlockF 96 128 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_4 : treeBlockF 128 160 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_5 : treeBlockF 160 192 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_6 : treeBlockF 192 224 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_7 : treeBlockF 224 256 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_8 : treeBlockF 256 288 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_9 : treeBlockF 288 320 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_10 : treeBlockF 320 352 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_11 : treeBlockF 352 384 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_12 : treeBlockF 384 416 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_13 : treeBlockF 416 448 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_14 : treeBlockF 448 480 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_15 : treeBlockF 480 512 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_16 : treeBlockF 512 544 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_17 : treeBlockF 544 576 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_18 : treeBlockF 576 608 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_19 : treeBlockF 608 640 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_20 : treeBlockF 640 672 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_21 : treeBlockF 672 704 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_22 : treeBlockF 704 736 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_23 : treeBlockF 736 768 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_24 : treeBlockF 768 800 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_25 : treeBlockF 800 832 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_26 : treeBlockF 832 864 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_27 : treeBlockF 864 896 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_28 : treeBlockF 896 928 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_29 : treeBlockF 928 960 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_30 : treeBlockF 960 978 (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nj_27_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_1 (fun _ h1 h2 => treeBlockF_at nb_27_2 h1 h2)
theorem nj_27_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_2 (fun _ h1 h2 => treeBlockF_at nb_27_3 h1 h2)
theorem nj_27_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_3 (fun _ h1 h2 => treeBlockF_at nb_27_4 h1 h2)
theorem nj_27_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_4 (fun _ h1 h2 => treeBlockF_at nb_27_5 h1 h2)
theorem nj_27_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_5 (fun _ h1 h2 => treeBlockF_at nb_27_6 h1 h2)
theorem nj_27_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_6 (fun _ h1 h2 => treeBlockF_at nb_27_7 h1 h2)
theorem nj_27_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_7 (fun _ h1 h2 => treeBlockF_at nb_27_8 h1 h2)
theorem nj_27_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_8 (fun _ h1 h2 => treeBlockF_at nb_27_9 h1 h2)
theorem nj_27_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_9 (fun _ h1 h2 => treeBlockF_at nb_27_10 h1 h2)
theorem nj_27_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_10 (fun _ h1 h2 => treeBlockF_at nb_27_11 h1 h2)
theorem nj_27_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_11 (fun _ h1 h2 => treeBlockF_at nb_27_12 h1 h2)
theorem nj_27_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_12 (fun _ h1 h2 => treeBlockF_at nb_27_13 h1 h2)
theorem nj_27_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_13 (fun _ h1 h2 => treeBlockF_at nb_27_14 h1 h2)
theorem nj_27_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_14 (fun _ h1 h2 => treeBlockF_at nb_27_15 h1 h2)
theorem nj_27_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_15 (fun _ h1 h2 => treeBlockF_at nb_27_16 h1 h2)
theorem nj_27_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_16 (fun _ h1 h2 => treeBlockF_at nb_27_17 h1 h2)
theorem nj_27_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_17 (fun _ h1 h2 => treeBlockF_at nb_27_18 h1 h2)
theorem nj_27_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_18 (fun _ h1 h2 => treeBlockF_at nb_27_19 h1 h2)
theorem nj_27_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_19 (fun _ h1 h2 => treeBlockF_at nb_27_20 h1 h2)
theorem nj_27_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_20 (fun _ h1 h2 => treeBlockF_at nb_27_21 h1 h2)
theorem nj_27_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_21 (fun _ h1 h2 => treeBlockF_at nb_27_22 h1 h2)
theorem nj_27_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_22 (fun _ h1 h2 => treeBlockF_at nb_27_23 h1 h2)
theorem nj_27_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_23 (fun _ h1 h2 => treeBlockF_at nb_27_24 h1 h2)
theorem nj_27_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_24 (fun _ h1 h2 => treeBlockF_at nb_27_25 h1 h2)
theorem nj_27_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_25 (fun _ h1 h2 => treeBlockF_at nb_27_26 h1 h2)
theorem nj_27_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_26 (fun _ h1 h2 => treeBlockF_at nb_27_27 h1 h2)
theorem nj_27_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_27 (fun _ h1 h2 => treeBlockF_at nb_27_28 h1 h2)
theorem nj_27_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_28 (fun _ h1 h2 => treeBlockF_at nb_27_29 h1 h2)
theorem nj_27_30 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := block_join nj_27_29 (fun _ h1 h2 => treeBlockF_at nb_27_30 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_27 g_27 bds_27 978 (dagTraceF m_27 s_27 8 f_27) l_27) i = true := nj_27_30
theorem lb_27 : LowerBin m_27 s_27 g_27 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xff00ff00ff00ff00
def s_28 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_28 : Nat := 0x100110011001500
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 6, g_8)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 6 f_28) l_28 0) s_28 6 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 6 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xff00ff00ff00ff
def s_29 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_29 : Nat := 0x11001500150057
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 6, g_11), (m_16, s_16, 6, g_16), (m_21, s_21, 6, g_21), (m_9, s_9, 5, g_9), (m_10, s_10, 5, g_10), (m_1, s_1, 4, g_1)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_16
  · exact lb_21
  · exact lb_9
  · exact lb_10
  · exact lb_1
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_29 : Nat → Nat × Nat := unpackForestF 0x169fe7929f3c14f908e7cc27de6019f209cf920fbc905de4039005a5f8a4a7c5053d4a51ef895f84513be247df02befc2277c08fa94a1dd93eeec0cf52547b425fdc144ed091f6806fb5089da013ea4a87620fbb105dd4851ea817f5c113aa047d501feac2275404fa90a000b47e9894f4c0a790473d092be8491f420afa1047c8238e789f73c06790273cc92fe6491f3206f99027c8138e581f72c0bb90073c882fe4411f2207f91027c8038005a1f1c0678b253c602ee2c1480292f894d9ba24bdd123f0a50785083ba246dd095f0251b81033ba129df4b66fa5537d031ba123dd015ef211b7905dba029dd4366ea15375059ba02300521ea517b7148ba9452dbe366a497f6c293b6049d492f6d4953524a7b2a5dd9522eca4a765053a9252d4895ebf17b5f8a5af95ed7c0cea44a75c2a9ae018d4891ea40af568bdab452d582f6ac0bb52053a9854d4c166a408c01477a8019d3494e9c0bb4d05200a33d2c14e904fb4907da4019004a5e50d4f43471a1938d0c9a650d2f412d99414bca0a3e7a9073d08394146ca09fe6cd4b366959b24acd92366c0a72827d9896ccc4aa6624f33103194133ca00de5a11b2d07d94019ca4366521532909994013004a1dfb17b2528b7ec52c851c6424e3212697eb53bf5a5e3d1b2fd2bf8da49c6c24dfa57b192a97e953c50aee285171427d8a019bf4a95fa4ff0b8bd85c52c2da9616d2b0b4bd85a52c2c14dfa4fb072a98393cc1c0c5fa4cefd03780c5ec062960217b0107d7e819bf82a5fc132fd0260093bbec14df04faf907d7c01900499cb117ef169178a48bcc0c5e2522f12892c45bbadb05d6982eb2d975960bac304b115ee569172a48b94a45ca512e50912c453b85a35c28eae10732c352b662f5bc512d98a56cb5eb65a95b28ead90732c34ab49a95ac8d2d269569246b491eda40a6584a563c5eb3ca258f14acd46963b52b1da558e97ac74a563a3db1c14cb092ac46c162260960afd84142c068b60049960af5769b2bb2995d93caec964b056eb58d95ac60ad5a856a942b50c12c157accae55a992ad2b956954ab4a655a4f2ad0312c153a60af5305769829b4c146a60a2d30512a52894c13da8ca25304b6a029950144a600d530066980314c84ca64225320f2990594c016960a9528d62944b14a048960a7d1c9728e2994713ca3ca651c062582973ec5e9f6294fa57a890313e9529f4a34fa4f67d25b3e81a9f40cd02d3a816853e8189f81e4fc0b27d02d2c14a9e9a44f49225828f3545e9dc1c4d514a756993535a9c1a84e0942702a1380509a9ab4d84f26c259360189a9a74d41065828d3414c9912a4c8532642793212c960a1cb006e5c6a52e34a971294b892a5c0bd2e0469600ccb2132590792c01300491caa4a2550492623394898ca44a64c07d26a329349f49c5124d2652602e00425c3ed4e472712383891c1a43ed2e1f4a721128908144840921f4971f8288fc1243e8ce3d0d90f84b87c23c72906392830f84687c1fc64d4a326951924a8c9234644a61f07d1686c8b42a45a0f22d0590f83387c17c4a94a254951294a894a344a4fa252650f82e88036440152200991002c87c1180210de68bd0e04579a294304e2180710c034799a9bccd2e132510982884c123cc94de6497072548381441c091e64670646c7982fc1292609292f305e81c2a3cc14e020bb010458081f4040b9e60a4f303f7e62f3f3149f96a4fcb4a7e52f3f2949f9252f303e7d42a3ea0f1f5058f303379817bd7179eb8a4f5a527ad253d6579eb2a4f593e7ac993cc0b9e70a8f384c79c163cc08c01076f1254788943c4091da466ef93177c94bb40f9db464ed93e76c993b40b8010668645f74da43a6521d5058e984874c2221916dcd6c0e6a60734b039a1b1cd0c08645771da438e921c7290e384871c2221914dc368ce1a3970c9d218d49bb8bce00446ee29376d79bb6a4dda396ec9d218d29b5498da9286dc2236a0a1b50488625b6c8143640910c4a6d78286bc1221892daa498d51286a8143540910c486d403467da934c0d19f694cfa5e68d2233e9499f494cfa4667c952188c5966a4ce134659a533449196462cb1466589eb2c4b90c2a4c445e64c2231114991268c4352621a531a9118d248c4231620af3105498827ac412e430a530ad81852c08605f60ca8300d1580292c01214302f2f65b17b098bd82c5ec0e21816d758d8bac605d5a82ea981752a0860575cc2e2da5916d0b8b68545b4262da0f16d0588605355918aac179560baab04d558232ac11565242ab04458c222ac0f55605caf84c57c222ac0b556058ad04c568222b40f15604aab84455c122ac0750c0a4a9358549242a45610c09ea615c5302629c1314c078a602c43025a751793a8a49d2314e82f28c0b13a0a49d0464e81ea740b93a05a9fb4e4fda12740b13d0789d0254ec122740750c0949bb484dca421811d238bc9a13848e29264d31236b496b504b52825a5412d0a091b564a41e2520b12903891b4e48ca0a464e5232629223848c90a18119210988e9544742623a0b11d0388604346da02180bd106a48834a4412d220909102bc88152440a5220519100a48804a4301721a1310d058860230041180517d054908294841c1e20a121050880145b3fdb01fe980ff2c07f86c3fc3000515cf96907ca483e4a41f2120f9088014533cd1c1e64e0f5088798383cc1a004d6cf007078034009a99da0e0ed0680134b3a11c1d04e0e807074034009a19c8918e447c7212a009291b9178e10886e4523712f1b8948dc47c6e12a009251b40d0d16a46c034345a51a2978d548868a52345251a2918d1254012323212919c490c84946612432119190518c827c6412d008a9175178c50885d45230c92174948ba4945fa442fc921748c8ba2bc5d1522e89f1744b4022945c03427da916c0d09f6945a12427d291644909f4945624e2bd1a158908ac4745623627d181544809f2bc5323029c9014c5109f2a45223027ca51424e0a12404f94627c968044c89c4c04e1600082f9349409568a4aa492549112c480950440105e240b61200f0900584801c0082d9151b08a8c04536022928114540020ae4405c208b2104170820a84104c2081e1040b0020a633a321fd180ce4c8670bc3385d19c268ce1186708a3b1221dc900ec088670883383e1c8260e41106707a3383c1b8260dc1106706a358441ac1a0ce0b4680883403419c0e8041486369031a5818cac00413c5d2b83004c174260ba0f05d0580104b1262f093148494642c230124990921785507824852124230920f84907a27b4e13da10920f04906a26034124168940d04903a0104a1192408c5200208e17c5e10d1c05f1484169817b5a0f1a80789403c2a01e0500bdab0700f0380581c01c0bda705e9042f47217a310cd1c05e48830470181200bc110041182d098149540a41e0520b029038010430992004c5000207e0db5a06da10369781b4a40da4a06d230365481b2940d85206c250040f8180780c02c00819806d480369401a5200d25006548032940185e030220180f00c0580601c00c290100f0080580401c00c250061180307a0182d00c0e8040c8010260001f 10 11
def l_29 : Nat → Nat → Option Nat := unpackLinksF 0xe609e600e600e546e540e540e486e480e480e3c6e306e300e300e246e240e240e221e220e220e201e165e160e160e0a6e0a0e0a0e081e080e080e061dfc5dfc0dfc0df06df00df00dee1dee0dee0dec1de25dd09dd00dd00dc46dc40dc40dc40dc40dba5dba0dba0dae6dae0dae0dae0dae0da45da40da40d986d980d980d980d980d8e5d76cd760d703d700d6a3d643d640d602d5e1d5e0d5e0d507d4c2d4c0d4c0d3c8d3c0d3a1d3a0d305d2c2d2c0d2c0d1c8d1c0d1a1d1a0d105ceb3cdc7cdc0cce7cce0cca2cca0cca0cbc7cbc0cb82cb80cb80cb80cb80ca88ca42ca40ca40ca40ca40c90ac8e1c8e0c864c822c820c820c820c820c6eac6c1c6c0c644c3b5c3a0c343c340c2e3c283c280c223c220c1c3c163c103c100c100c0e1c007c000bfc2bfa1bfa0bfa0bec7be82be80be80be80be80be80bd88bd80bd61bd60bd60bcc5bc82bc80bc80bb88bb80bb61bb60bac5b873b787b780b6a7b6a0b6a0b681b5a7b543b540b502b500b500b427b420b3e2b3e0b3e0b3e0b3e0b2e8b2a2b2a0b2a0b2a0b2a0b2a0b2a0b2a0b16ab141b140b140b0c4b082b080b080b080b080af4aaf21af20aea4ac15ac00aba3aba0ab43aae3aa07aa00aa00aa00a9e1a9e0a945a921a901a900a8e1a8c1a806a800a800a800a7c2a7c0a6c8a6c0a6c0a6c0a54ca540a540a521a520a520a520a520a36ea360a360a341a340a340a340a1cca1c0a1c0a1a1a1a0a181a180a180a180a180a1809fce9fc09fc09f449f409f219f209e289e019e009e009dc29d449d409d409d409d409d409c679c609c419c409c409c409c409c409b679b609b609b039b009a849a429a409a029a0099c299c099c0998299809980998099809980998098e596f096e096e096e09645960295e195c195c0958294e594c194829480948094429440940293c293a193a093a093a09362936093609303912f9120912090a490a090a090629060904190409040904090408fc48fc08fc08fc08f638f608dec8de08dc18dc08dc08da18d248cc38cc08cc08cc08cc08ca18c818b2b8b208b208ac3871e86e186e086458640864085e385e085e085e085a2854384e38483848084808461838783238320832083018227822081e280c980c080828061806080607f877f427f407f407f407f407f407e487e407e217e207e207d857d427d407d407d407d407d407d407c487c407c217c207c207b857933784778407767776077607741766776037600760075e1750774a374627460742272ea72e072a272a072a071c771c0718271807180718071807088704270407040704070407040704070406f0a6ee16ee06ee06e646e226e206e206e206e206e206e206e206e206cea6cc16cc06cc06c4469b569a06981698068c668c068c0686368606860684167e3678366a766a066a066a06681668065e565c165a165816580656164a664a064a064a064a06462636863606360636061ec61e061e061c161c061c061c061c0600e6000600060005fc25fc05f255f205ee25dc95dc05d825c4a5c405c405c215c205b665b605b225b205ac35aa15a815a425a2159e259e0580f5800580057e157e057a257a057a057a0562c562056205601560055e155e055e055e05583558055805580558053ce53c053c053445340532153205301520851e151e051e051a2512451205120512051205120504750405021502050205020502050204f474f024f004f004ea34ea04e244e014dc24dc04d824d804d804d804d424d404d404d404d404ca54ca04ca04c624a704a604a604a6049c54982496149604922490148654841480247e147e047e047a247a0476247604741474047404702470046a346a04662448f4480448044044400440043c243c043a143a043a043a043a0432443204320432042c342c0428242804280424240cc40c040a140a040a04081400440003fa33fa03fa03f813f613f413f403f403f213f203f203dcb3dc03dc03d6339be38c738c038c038c038a138a0380537e137c137a137a0378136c636c036c036c036c0368235883580358035803542354034a534a0346233493340330231ca31c031c031a131a030e630e030e030e02f6c2f602f602f412f402f402f402f402d8e2d802d422d402ce32cc12ca12c622c412c022c002a2f2a202a202a012a0029c229c029c029c0284c2840284028212820280128002800280027a327a027a027a027a025ee25e025a225a0254325402502250024a324a024a0248124802480230c230022e122c122c022a12262226022412240224022022200202f202020201fa41fa01f811f801f611f601f411e481e211e201e201de21d641d601d601d601d601d601c871c801c611c601c601c601c601c601b871b421b211ae21ae01ae01a831a801a0419e119e019c11982198019801980194219401940194018a518a018a018621860186018221630162016201620158515421540150214e114c11425140113c213a113a013811380138013421340134013211320132012e212831280124212401202102f102010200fa40fa00fa00f620f600f410f400f400f400f400ec40ec00ec00ec00e630e600e220e200e200de20de00de00da20c2c0c200c010c000c000be10b640b600b600b030ae10ac10aa10aa00aa00a810a800a800a800a80092b0920092008c308c008c008c008c008c008c008c008c008c008c008c0084408400840084007e307e007e007e007e0064d029e00330001 0x1b2241dc91ce26507262737b12380420c3a0e5d804685013bd498fa04a6f2242eb831f3c14ba8086f4465e693ebc899212087cc032830117589921048bca07cea032f241720c08bce473e5939bc091f900e5d204682013bbc98f8c4a6ec242e8831f1414b9a087c2289df844f0c95f8248fc0057df02340c09ddc8cbbc27d7613240810f76064ff023dc144ed4227724bfb7246e8023ed80df6804dcf26480922ec81f39a0cbb105c7f822eb822756112eb247d782feb411f5807faa027e2251ef528774547b32a175123ec028f52141cc0467f013ba498f4e4a6e7242e5831e9814b90087a4257d1923e8815f4208cfd02774232e7c9f5ce4c8fc043cf0193e808f384bf9b246e5023e680df3204dc92647d922e5c1f3900cb9605c7d022b9491f280bf93047c901fe4409ee0927a5473d0238c90a4f3a4e7982717212386c24f2a0e790070e30233e0099ee0878e0327a0113d8917180b8f4045c6929e2c149e404f676a9c4a6cd9d246ced3b22293c3141b8c90c3212785082e2821b89205448c3324a591a4ac88a570451aa225ae2031e040c9e2046a325151238dfcb66fc5533a299be81870ca02ac4c2e146316952868a543212b7a08dbc82e3c4112ac07558050ab138ddc366ec15236099ba82ce2125ec892b8748fc2246d18a9e4052ee0263c192be0094ef848e972432505385c25b840c77b057bc029dd011aaa084ef027b7a5db7c98ec44a68c242e0831d6414a940877148b6e931d8494d16485bf063ac02952410edf1b3684c1b445ddb4a4e88506dc243b604992020b7c087686d9b5254da12eece916db263b3129a2090b7a0c765052a2821b692050a8c3628bdb0c52d152961092b602bda2152a1496b780c75f032770119b49450a8e35d2a98714cd700c3765013a261acc5ed62295b28c6492a4fa94ad5c2f49014b5605c770224e80ea520a13a271aa0547f0266a60b3728bdb8452db92fed697b694a7b2252d08a9e3e52ed8263b192bd7894eb648e7c2432305385825b740c75a057aa829d4811a72084ec02675821d400c9d2044ea245a702e3a41169e4a74d052738136e418e960a5b6042dc132d241f36c0cb4a27cda033d200cdae903324719d14cb58985aa903454719c94cce09e6884e34326944130c592a6825b3162918b34ece124e7c906d42450a049cf4209cc046d348152140ce9a9672d2b384959ba46a911ee6c0a5b304272811a949e548933342d999954cc89e662060e426033920b491944054a152950a04acb82365a0f9b30643381d1a40c0ce4a32b0d995054ca4264540f3466a7a134bb451968052f132959f947cf0a36764ff3527d98133a5c9948a14e12096d883338c10e5e06f2c0339401319808da08cb1e2bb8893ea30991c4087040322d811b391964a5171027d4593238010e060645a02366930b31206468e30f2998613cc889c6424d28826165a40c211c61c5331e8d98b960c5e2ee389270c48365122c6c24c86104df0238ba6cc64aa5928cb172bb8b145c549f5104c8de0438a01915008d909028628188c5ec422961ed4b0e69586a5ec312950c8f70b052d802137408cdc4f28649984954c209e60e060dc26024920c122f60714ac74652215279ca560417a430a58083e6c0190920743803024928bfc2a5fc131ef0799345ec9229640d4f1f69763232c74afe3457b182a789952c489fe144fb062673e13290429c2212dae0666d821c140de00066fd026240116b418df60a5ab042d6132be41f3560cafa27cd4833be00cdb6d42df69164a50b41244f0572882a146148bcc0c5ead22f44913a154bc8a45e251272289389449cca24e0512ef6c177260bb4b65d85826f28975860b792459e522dd6b174b48b392c5d09228b2b173948b98a25ca122db69571b46b5d2959892ae24756295dadcaadc20e56b0626c8219840c82c046de2896fc5eb76295b8d7adb6a56aa52b2d255b48ea9629b3d945b641ca900c4d70433001905408dac8d2d76a56ab4ab25255a891ad347b6215dad8aab4e0c6d20524002197c0c828046cf28966a34b422f59d14acc6a565b4ab292f59294ac847b4a94d9e8a2b4a0c6c70522c8219780c826046c56c162260af8b4554582c20a15dc5eaaa2ecf0d36c168b6004990020b48084d6023599549cca2018062be4d95e94caf09e5764b2b98d95c460adda856c942ab2d959150ad430566572aa4d959264ac4ae560552af2995713cab40c4e6512a10314e014a949e5464b2a00314d81468c109aa046a52894d014a8ca2532052a129950144a70265361129a0794c82c0300e55657aaa2bb5494da20a555051aa728b53144a909ed444b5a20626a021a7c0d53c0669d0314c01602c08d2cd62954b149158a1ca252812268289478189b8a24da5128f29936144a492e4d6952912994813ca380c50406275289408189cca25120626e2893f8149b4a24fc0526c2894134ea05a14fe0f27e0580401ca322f51714a8a2bd44152a1ca34d65168627b4292d684189a60868403541819a000c4fa058070233db489e9244d65226728139b449dc1c4ead32736a1392509c4a84e01426e2793692c9b00c4f117a768a53a35a9bdab4d6d3a6469b078499a820c200e5e4062d002134808cd05300803133a54998a64ca4f264258cf940344980064800c09004040985a94c0d2a5f4a52f24a958ad3c650a5d0bd2005283c254b81180303a01928968264b20f2f68bf7845bbaa2bdc914ee06a56c34ab452958c92ac32bf5f95eae8add6855eac2a74b952a4ca7d1a52e7c2953c9479a4a34c650e540b71f05383425bc210d9e062680219880dcb606658026010110300a4ac4a2530992803c934164aa092532632912993490c9c5100c0312823293c9f49a4ca544672883e9301733a5022d2711b04c67018336502492711a84c8d01e4900e247068a283033c984404a22a07867020334984884a2290791402c90c1448409054040cd03033010332500cb260091205ac201000c225059200288fc12016082042a91e86c81024408d3a344931d2418a0a4c72505980446501265ca02c4102366a51ab4a8d1254669196247b191298949099204963078b114c8c03645e1522e0791682c320980d40c22a4a514a4a8a0a544e51a2627d129321a896b2c0c86c0583513c88c36444152210991002c929a9c8cd2e454a720a4b8f919b2a4c8c72451e04b8042547611e3808d1b83f8c41f4580cd550651582f8901743e08c66044ca13231891418175ff07ca50327c8170b6089922646212287022bfc0f949064f882e168113220c1902810d1387f4263f40f2190710c0345141831e501f5270fe04c30c101844c215250f803c7b4164280a2130482a020304983ce4a1ef078c71303009031a0c0bf04108254630a017c4c011240a4040164183d60b20f0510702401c104191b2050c102c5d82924bf490609292f694162c1117a04a052d9038546289917848a050bb0204580c1f28a0ca0205c2a022624a0286101ff8bcff4527f5a93f8d29fb4bcfd25250d1ebf24a5eb2425d8124ac1e286531f70a8fb03c7d4161744c04b060f945e7c6293e0949ef494f715e7b4a93d84f9eb2642592d620190720b04b278f48547a0263ce0b21d8bd0dc5285da9c2cd2e124a708a4b83519b0e4c8b92450585f8202f40c14e010a50003f7e01f3e80cd39064f982f7a8173cc08c48044040147912a3c64a1e0098ee83c76c163c4091e0262ef92976c90810061dd464ee13e76c993c28cdde07ced02e6f5a8382d218a2a0ca1484d42e28a1414a090ea82c75da43ac521310a8ea04874c2225e1112e088968444c0223a2d81d04c0e79607383639a1812c088e024864c2437ed61cb690e5248648ac392521490b0e404871c2237ad29c568ce223968918b3a54990294e193a2dc9130c175770aa8c82e05811380111c18bcdfc526f9af37ad49bc472d0a3166ca931e529bb2745a92255026a701151805c0a8226dc2201a0b1b9498dc12845c1e36c0a1b5048d42302d01034ed01a2480599301f8900280c114058d98286c812016081a646059020695a0342900b12602b9204982a0260c113058d80286bc1200e08009058d6a4c6b09424a15116078d58286a8120fe4c1a80682c1304902234c0d0b02405792068d2215c4c0ad260c71382b09034ed49a5694d225e68929342929a048ccc952630a51564c19f254c005e5ac292901292308c8d83d6709a0fe4c19a248ceb5266da53328c58a294cc14665c9eb2c4b87e244c285d5d42aa220b812044c98446449a31c91058260c69246522f325149906a4c7b4a63118b165798a2a4c493d620970ae4895209a9b84544017022089866c0c29605f8342d2181832a0550205ee2f2d31753569ac1345604a4a2850580242548125cc2a2601100d058bf16c5f4262f80b17b038bcc6c5e2302eed41764c0ba9505a8362e4141730b8b496c5c8b22e2171700a8b784c5b81e2da0b0a8260b28444c0222c00b15c048b183c57c162b609158038538205949094c04963088ad024580262be1115c098ad8445681e01a0b157038ac04455c122d68c4a5244b505e5a42ead013545094b384659822ac81116207ab082e57816aba0b15904a058225580eaa8d6153490a91585402c28811121088a702c4ac2229c1312a08894844540ae2505514f098a683c530162800b1320889f82c2909826011146058958444f4122541114069c9fb424f41e0120b13b038948444ec12295179498a4a423128c9128e179450a4a20464a022a860f54205ca082d4f816278094070449d01d4e1a426e52128090900404c1a22684e132698983504bd2825c5412d0a09583c4a81625207124460510204911c142081358bc99c524c5ad258d592869c8eb4d44ca4a4e505262729293148c90940049210980482c480aa23e1311e0588e81c46da013e4c004060069240249201a520092808cb52461a522e969164848a95e450a92265291228c0212d44429220128042788704c434163b117dd28b6e645771a29b84d49ba694da25b6c529b5c92da9486cf231654a930e5289e244c205f5fc2f2f416d740aeb6053554292a213d4b0969c84a4d823a441191c0868d02f43c1721808c020446f25038924178540c62902205c150280b61210707884a48420a408015106090828440f82207a1103c0881f84440db0204981012c08006c3fc30076110e1290628483f5a41c0960fc490621583eca40b4160fa0907c8443d42201c0f0f74707b138090261e80e0f30686d1302e0181b2900d44605b9402949802c10021078788383c01a0160c0d82605b03035d201a68c0b5280519300d42a02a10020078770383b41a00e0c00a07875a383a89c06815023098748383a01a1bc928e648c72a3e3511919e548c2294599323909513a1748b0aa0f03e050191c2110e28bc7045237d2f1bc948dd47c69a32334a9182528b12646e12a1902688e1141d07c098322a0981b40d0a4260198443601a160480af2406aa442b89815a4c0c027056120365a91aed28d64bc6a25234d251a4918cb2a45f14a2ac981a24a8970bc40052164250641182707a671242a098198490cf4a466a4a32d19178528ca28c6493e294991904b49c0ba450550701f0240c8c508861924301221484c0bf2486345e31229184948c14945f2322f4af178548bb27c519322e8968c61344608a0d83e0441915c8c0b806856a300c42216c0d0ae4605a1242b518144510b224857a342c12715c908ad474562362a8a7150508a427450936258270fe10858074180362a89014e4d0a724054230298a21488c0a2270509202dda916ad28b34a458a4a2ad18152578a52a45194a280a313e4b4950bc3f05215c2505e1182607a4ea60270b01261a07c0c04d2502581012c480908bc3e45d111a6932d149849210a4125c9112a088880a81f8440381e1265b0920784882c2400e11d1b08d8c04636022d281145407d0d8438502202e0f85b0872c84305c2142a108130830784102c1fc980f0110770683fa301d82207e11073078378341c81e0dc0d06c0583481c1dc100ee480782443b0221cc260e41106f098370440381e0d60b068038360441ac1a0d211068068402321f8990fa1787c0ba3d84d150250f41187908a3a8441d01f0e20f4700783683502c190d40b46703a32b481912c0c6560610b0298440b4220c00f0600981d0440e422070110612b81b95417c260bc0f05d0582803c1042209e0f0582602c2300fc220aa0f03a0882834e13da10140f04c0582501c0e4220980d0380882503416e2f0b5148594642b9321582f0a81485308c1b8451481f0a20f44e0782683501c190960b44903a23a48118a406e1202c0801fb4410d1c082d303f6a01f2500f4a80781403a0781c82c0e00e0664c03106019a380c0100628e0302402245e10a29080d683b6ac1bb4e0a5a6840924364821aa390d1188644882f0441684c0281e0585502b0781502c0a40e04e90026280028400391a0148d00e49005240091ad046d08224bc10a520812503e9180547a0f152074a50381481b0940294c0641e0300b00f0880703c034160180700a0780482c0200e02cd48156940a25204d25024548112940805e02c2900e1280608c0283d010168060750a8be8245b3fa2b9f114cf26b677b533b1a59ced0ce34a46da4a3411918e548b92944f13226c2f9281788f0b644857204298cc1486209e2e04b1202508a11c2e08c140430941f8340f81706601032f45a7f8ed2fa868fc7b43e2925ee690f51477a6233d1ca5e4e50efc2777b93395c91c9612e1e086f283b76419a1608c010260001f 16 5 11 10 6
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 978 (dagTraceF m_29 s_29 8 f_29) l_29 0) s_29 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 64 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_2 : treeBlockF 64 96 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_3 : treeBlockF 96 128 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_4 : treeBlockF 128 160 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_5 : treeBlockF 160 192 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_6 : treeBlockF 192 224 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_7 : treeBlockF 224 256 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_8 : treeBlockF 256 288 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_9 : treeBlockF 288 320 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_10 : treeBlockF 320 352 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_11 : treeBlockF 352 384 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_12 : treeBlockF 384 416 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_13 : treeBlockF 416 448 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_14 : treeBlockF 448 480 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_15 : treeBlockF 480 512 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_16 : treeBlockF 512 544 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_17 : treeBlockF 544 576 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_18 : treeBlockF 576 608 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_19 : treeBlockF 608 640 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_20 : treeBlockF 640 672 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_21 : treeBlockF 672 704 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_22 : treeBlockF 704 736 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_23 : treeBlockF 736 768 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_24 : treeBlockF 768 800 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_25 : treeBlockF 800 832 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_26 : treeBlockF 832 864 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_27 : treeBlockF 864 896 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_28 : treeBlockF 896 928 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_29 : treeBlockF 928 960 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_30 : treeBlockF 960 978 (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nj_29_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_1 (fun _ h1 h2 => treeBlockF_at nb_29_2 h1 h2)
theorem nj_29_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_2 (fun _ h1 h2 => treeBlockF_at nb_29_3 h1 h2)
theorem nj_29_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_3 (fun _ h1 h2 => treeBlockF_at nb_29_4 h1 h2)
theorem nj_29_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_4 (fun _ h1 h2 => treeBlockF_at nb_29_5 h1 h2)
theorem nj_29_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_5 (fun _ h1 h2 => treeBlockF_at nb_29_6 h1 h2)
theorem nj_29_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_6 (fun _ h1 h2 => treeBlockF_at nb_29_7 h1 h2)
theorem nj_29_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_7 (fun _ h1 h2 => treeBlockF_at nb_29_8 h1 h2)
theorem nj_29_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_8 (fun _ h1 h2 => treeBlockF_at nb_29_9 h1 h2)
theorem nj_29_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_9 (fun _ h1 h2 => treeBlockF_at nb_29_10 h1 h2)
theorem nj_29_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_10 (fun _ h1 h2 => treeBlockF_at nb_29_11 h1 h2)
theorem nj_29_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_11 (fun _ h1 h2 => treeBlockF_at nb_29_12 h1 h2)
theorem nj_29_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_12 (fun _ h1 h2 => treeBlockF_at nb_29_13 h1 h2)
theorem nj_29_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_13 (fun _ h1 h2 => treeBlockF_at nb_29_14 h1 h2)
theorem nj_29_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_14 (fun _ h1 h2 => treeBlockF_at nb_29_15 h1 h2)
theorem nj_29_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_15 (fun _ h1 h2 => treeBlockF_at nb_29_16 h1 h2)
theorem nj_29_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_16 (fun _ h1 h2 => treeBlockF_at nb_29_17 h1 h2)
theorem nj_29_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_17 (fun _ h1 h2 => treeBlockF_at nb_29_18 h1 h2)
theorem nj_29_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_18 (fun _ h1 h2 => treeBlockF_at nb_29_19 h1 h2)
theorem nj_29_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_19 (fun _ h1 h2 => treeBlockF_at nb_29_20 h1 h2)
theorem nj_29_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_20 (fun _ h1 h2 => treeBlockF_at nb_29_21 h1 h2)
theorem nj_29_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_21 (fun _ h1 h2 => treeBlockF_at nb_29_22 h1 h2)
theorem nj_29_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_22 (fun _ h1 h2 => treeBlockF_at nb_29_23 h1 h2)
theorem nj_29_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_23 (fun _ h1 h2 => treeBlockF_at nb_29_24 h1 h2)
theorem nj_29_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_24 (fun _ h1 h2 => treeBlockF_at nb_29_25 h1 h2)
theorem nj_29_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_25 (fun _ h1 h2 => treeBlockF_at nb_29_26 h1 h2)
theorem nj_29_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_26 (fun _ h1 h2 => treeBlockF_at nb_29_27 h1 h2)
theorem nj_29_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_27 (fun _ h1 h2 => treeBlockF_at nb_29_28 h1 h2)
theorem nj_29_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_28 (fun _ h1 h2 => treeBlockF_at nb_29_29 h1 h2)
theorem nj_29_30 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := block_join nj_29_29 (fun _ h1 h2 => treeBlockF_at nb_29_30 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_29 g_29 bds_29 978 (dagTraceF m_29 s_29 8 f_29) l_29) i = true := nj_29_30
theorem lb_29 : LowerBin m_29 s_29 g_29 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xffff0000ffff0000
def s_30 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_30 : Nat := 0x111000011150000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 6, g_12)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 6 f_30) l_30 0) s_30 6 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 6 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xffff0000ffff
def s_31 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_31 : Nat := 0x111500001557
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 6, g_15), (m_16, s_16, 6, g_16), (m_22, s_22, 6, g_22), (m_13, s_13, 5, g_13), (m_14, s_14, 5, g_14), (m_2, s_2, 4, g_2)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_16
  · exact lb_22
  · exact lb_13
  · exact lb_14
  · exact lb_2
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_31 : Nat → Nat × Nat := unpackForestF 0x169fe7929f3c14f908e7cc27de6019f209cf920fbc905de4039005a5f8a4a7c5053d4a51ef895f84513be247df02befc2277c08fa94a1dd93eeec0cf52547b425fdc144ed091f6806fb5089da013ea4a87620fbb105dd4851ea817f5c113aa047d501feac2275404fa90a000b47e9894f4c0a790473d092be8491f420afa1047c8238e789f73c06790273cc92fe6491f3206f99027c8138e581f72c0bb90073c882fe4411f2207f91027c8038005a1f1c0678b253c602ee2c1480292f894d9ba24bdd123f0a50785083ba246dd095f0251b81033ba129df4b66fa5537d031ba123dd015ef211b7905dba029dd4366ea15375059ba02300521ea517b7148ba9452dbe366a497f6c293b6049d492f6d4953524a7b2a5dd9522eca4a765053a9252d4895ebf17b5f8a5af95ed7c0cea44a75c2a9ae018d4891ea40af568bdab452d582f6ac0bb52053a9854d4c166a408c01477a8019d3494e9c0bb4d05200a33d2c14e904fb4907da4019004a5e50d4f43471a1938d0c9a650d2f412d99414bca0a3e7a9073d08394146ca09fe6cd4b366959b24acd92366c0a72827d9896ccc4aa6624f33103194133ca00de5a11b2d07d94019ca4366521532909994013004a1dfb17b2528b7ec52c851c6424e3212697eb53bf5a5e3d1b2fd2bf8da49c6c24dfa57b192a97e953c50aee285171427d8a019bf4a95fa4ff0b8bd85c52c2da9616d2b0b4bd85a52c2c14dfa4fb072a98393cc1c0c5fa4cefd03780c5ec062960217b0107d7e819bf82a5fc132fd0260093bbec14df04faf907d7c01900499cb117ef169178a48bcc0c5e2522f12892c45bbadb05d6982eb2d975960bac304b115ee569172a48b94a45ca512e50912c453b85a35c28eae10732c352b662f5bc512d98a56cb5eb65a95b28ead90732c34ab49a95ac8d2d269569246b491eda40a6584a563c5eb3ca258f14acd46963b52b1da558e97ac74a563a3db1c14cb092ac46c162260960afd84142c068b60049960af5769b2bb2995d93caec964b056eb58d95ac60ad5a856a942b50c12c157accae55a992ad2b956954ab4a655a4f2ad0312c153a60af5305769829b4c146a60a2d30512a52894c13da8ca25304b6a029950144a600d530066980314c84ca64225320f2990594c016960a9528d62944b14a048960a7d1c9728e2994713ca3ca651c062582973ec5e9f6294fa57a890313e9529f4a34fa4f67d25b3e81a9f40cd02d3a816853e8189f81e4fc0b27d02d2c14a9e9a44f49225828f3545e9dc1c4d514a756993535a9c1a84e0942702a1380509a9ab4d84f26c259360189a9a74d41065828d3414c9912a4c8532642793212c960a1cb006e5c6a52e34a971294b892a5c0bd2e0469600ccb2132590792c01300491caa4a2550492623394898ca44a64c07d26a329349f49c5124d2652602e00425c3ed4e472712383891c1a43ed2e1f4a721128908144840921f4971f8288fc1243e8ce3d0d90f84b87c23c72906392830f84687c1fc64d4a326951924a8c9234644a61f07d1686c8b42a45a0f22d0590f83387c17c4a94a254951294a894a344a4fa252650f82e88036440152200991002c87c1180210de68bd0e04579a294304e2180710c034799a9bccd2e132510982884c123cc94de6497072548381441c091e64670646c7982fc1292609292f305e81c2a3cc14e020bb010458081f4040b9e60a4f303f7e62f3f3149f96a4fcb4a7e52f3f2949f9252f303e7d42a3ea0f1f5058f303379817bd7179eb8a4f5a527ad253d6579eb2a4f593e7ac993cc0b9e70a8f384c79c163cc08c01076f1254788943c4091da466ef93177c94bb40f9db464ed93e76c993b40b8010668645f74da43a6521d5058e984874c2221916dcd6c0e6a60734b039a1b1cd0c08645771da438e921c7290e384871c2221914dc368ce1a3970c9d218d49bb8bce00446ee29376d79bb6a4dda396ec9d218d29b5498da9286dc2236a0a1b50488625b6c8143640910c4a6d78286bc1221892daa498d51286a8143540910c486d403467da934c0d19f694cfa5e68d2233e9499f494cfa4667c952188c5966a4ce134659a533449196462cb1466589eb2c4b90c2a4c445e64c2231114991268c4352621a531a9118d248c4231620af3105498827ac412e430a530ad81852c08605f60ca8300d1580292c01214302f2f65b17b098bd82c5ec0e21816d758d8bac605d5a82ea981752a0860575cc2e2da5916d0b8b68545b4262da0f16d0588605355918aac179560baab04d558232ac11565242ab04458c222ac0f55605caf84c57c222ac0b556058ad04c568222b40f15604aab84455c122ac0750c0a4a9358549242a45610c09ea615c5302629c1314c078a602c43025a751793a8a49d2314e82f28c0b13a0a49d0464e81ea740b93a05a9fb4e4fda12740b13d0789d0254ec122740750c0949bb484dca421811d238bc9a13848e29264d31236b496b504b52825a5412d0a091b564a41e2520b12903891b4e48ca0a464e5232629223848c90a18119210988e9544742623a0b11d0388604346da02180bd106a48834a4412d220909102bc88152440a5220519100a48804a4301721a1310d058860230041180517d054908294841c1e20a121050880145b3fdb01fe980ff2c07f86c3fc3000515cf96907ca483e4a41f2120f9088014533cd1c1e64e0f5088798383cc1a004d6cf007078034009a99da0e0ed0680134b3a11c1d04e0e807074034009a19c8918e447c7212a009291b9178e10886e4523712f1b8948dc47c6e12a009251b40d0d16a46c034345a51a2978d548868a52345251a2918d1254012323212919c490c84946612432119190518c827c6412d008a9175178c50885d45230c92174948ba4945fa442fc921748c8ba2bc5d1522e89f1744b4022945c03427da916c0d09f6945a12427d291644909f4945624e2bd1a158908ac4745623627d181544809f2bc5323029c9014c5109f2a45223027ca51424e0a12404f94627c968044c89c4c04e1600082f9349409568a4aa492549112c480950440105e240b61200f0900584801c0082d9151b08a8c04536022928114540020ae4405c208b2104170820a84104c2081e1040b0020a633a321fd180ce4c8670bc3385d19c268ce1186708a3b1221dc900ec088670883383e1c8260e41106707a3383c1b8260dc1106706a358441ac1a0ce0b4680883403419c0e8041486369031a5818cac00413c5d2b83004c174260ba0f05d0580104b1262f093148494642c230124990921785507824852124230920f84907a27b4e13da10920f04906a26034124168940d04903a0104a1192408c5200208e17c5e10d1c05f1484169817b5a0f1a80789403c2a01e0500bdab0700f0380581c01c0bda705e9042f47217a310cd1c05e48830470181200bc110041182d098149540a41e0520b029038010430992004c5000207e0db5a06da10369781b4a40da4a06d230365481b2940d85206c250040f8180780c02c00819806d480369401a5200d25006548032940185e030220180f00c0580601c00c290100f0080580401c00c250061180307a0182d00c0e8040c8010260001f 10 11
def l_31 : Nat → Nat → Option Nat := unpackLinksF 0xe609e600e600e546e540e540e486e480e480e3c6e306e300e300e246e240e240e221e220e220e201e165e160e160e0a6e0a0e0a0e081e080e080e061dfc5dfc0dfc0df06df00df00dee1dee0dee0dec1de25dd09dd00dd00dc46dc40dc40dc40dc40dba5dba0dba0dae6dae0dae0dae0dae0da45da40da40d986d980d980d980d980d8e5d76cd760d703d700d6a3d643d640d602d5e1d5e0d5e0d507d4c2d4c0d4c0d3c8d3c0d3a1d3a0d305d2c2d2c0d2c0d1c8d1c0d1a1d1a0d105ceb3cdc7cdc0cce7cce0cca2cca0cca0cbc7cbc0cb82cb80cb80cb80cb80ca88ca42ca40ca40ca40ca40c90ac8e1c8e0c864c822c820c820c820c820c6eac6c1c6c0c644c3b5c3a0c343c340c2e3c283c280c223c220c1c3c163c103c100c100c0e1c007c000bfc2bfa1bfa0bfa0bec7be82be80be80be80be80be80bd88bd80bd61bd60bd60bcc5bc82bc80bc80bb88bb80bb61bb60bac5b873b787b780b6a7b6a0b6a0b681b5a7b543b540b502b500b500b427b420b3e2b3e0b3e0b3e0b3e0b2e8b2a2b2a0b2a0b2a0b2a0b2a0b2a0b2a0b16ab141b140b140b0c4b082b080b080b080b080af4aaf21af20aea4ac15ac00aba3aba0ab43aae3aa07aa00aa00aa00a9e1a9e0a945a921a901a900a8e1a8c1a806a800a800a800a7c2a7c0a6c8a6c0a6c0a6c0a54ca540a540a521a520a520a520a520a36ea360a360a341a340a340a340a1cca1c0a1c0a1a1a1a0a181a180a180a180a180a1809fce9fc09fc09f449f409f219f209e289e019e009e009dc29d449d409d409d409d409d409c679c609c419c409c409c409c409c409b679b609b609b039b009a849a429a409a029a0099c299c099c0998299809980998099809980998098e596f096e096e096e09645960295e195c195c0958294e594c194829480948094429440940293c293a193a093a093a09362936093609303912f9120912090a490a090a090629060904190409040904090408fc48fc08fc08fc08f638f608dec8de08dc18dc08dc08da18d248cc38cc08cc08cc08cc08ca18c818b2b8b208b208ac3871e86e186e086458640864085e385e085e085e085a2854384e38483848084808461838783238320832083018227822081e280c980c080828061806080607f877f427f407f407f407f407f407e487e407e217e207e207d857d427d407d407d407d407d407d407c487c407c217c207c207b857933784778407767776077607741766776037600760075e1750774a374627460742272ea72e072a272a072a071c771c0718271807180718071807088704270407040704070407040704070406f0a6ee16ee06ee06e646e226e206e206e206e206e206e206e206e206cea6cc16cc06cc06c4469b569a06981698068c668c068c0686368606860684167e3678366a766a066a066a06681668065e565c165a165816580656164a664a064a064a064a06462636863606360636061ec61e061e061c161c061c061c061c0600e6000600060005fc25fc05f255f205ee25dc95dc05d825c4a5c405c405c215c205b665b605b225b205ac35aa15a815a425a2159e259e0580f5800580057e157e057a257a057a057a0562c562056205601560055e155e055e055e05583558055805580558053ce53c053c053445340532153205301520851e151e051e051a2512451205120512051205120504750405021502050205020502050204f474f024f004f004ea34ea04e244e014dc24dc04d824d804d804d804d424d404d404d404d404ca54ca04ca04c624a704a604a604a6049c54982496149604922490148654841480247e147e047e047a247a0476247604741474047404702470046a346a04662448f4480448044044400440043c243c043a143a043a043a043a0432443204320432042c342c0428242804280424240cc40c040a140a040a04081400440003fa33fa03fa03f813f613f413f403f403f213f203f203dcb3dc03dc03d6339be38c738c038c038c038a138a0380537e137c137a137a0378136c636c036c036c036c0368235883580358035803542354034a534a0346233493340330231ca31c031c031a131a030e630e030e030e02f6c2f602f602f412f402f402f402f402d8e2d802d422d402ce32cc12ca12c622c412c022c002a2f2a202a202a012a0029c229c029c029c0284c2840284028212820280128002800280027a327a027a027a027a025ee25e025a225a0254325402502250024a324a024a0248124802480230c230022e122c122c022a12262226022412240224022022200202f202020201fa41fa01f811f801f611f601f411e481e211e201e201de21d641d601d601d601d601d601c871c801c611c601c601c601c601c601b871b421b211ae21ae01ae01a831a801a0419e119e019c11982198019801980194219401940194018a518a018a018621860186018221630162016201620158515421540150214e114c11425140113c213a113a013811380138013421340134013211320132012e212831280124212401202102f102010200fa40fa00fa00f620f600f410f400f400f400f400ec40ec00ec00ec00e630e600e220e200e200de20de00de00da20c2c0c200c010c000c000be10b640b600b600b030ae10ac10aa10aa00aa00a810a800a800a800a80092b0920092008c308c008c008c008c008c008c008c008c008c008c008c0084408400840084007e307e007e007e007e0064d029e00330001 0x1b2241dc91ce26507262737b12380420c3a0e5d804685013bd498fa04a6f2242eb831f3c14ba8086f4465e693ebc899212087cc032830117589921048bca07cea032f241720c08bce473e5939bc091f900e5d204682013bbc98f8c4a6ec242e8831f1414b9a087c2289df844f0c95f8248fc0057df02340c09ddc8cbbc27d7613240810f76064ff023dc144ed4227724bfb7246e8023ed80df6804dcf26480922ec81f39a0cbb105c7f822eb822756112eb247d782feb411f5807faa027e2251ef528774547b32a175123ec028f52141cc0467f013ba498f4e4a6e7242e5831e9814b90087a4257d1923e8815f4208cfd02774232e7c9f5ce4c8fc043cf0193e808f384bf9b246e5023e680df3204dc92647d922e5c1f3900cb9605c7d022b9491f280bf93047c901fe4409ee0927a5473d0238c90a4f3a4e7982717212386c24f2a0e790070e30233e0099ee0878e0327a0113d8917180b8f4045c6929e2c149e404f676a9c4a6cd9d246ced3b22293c3141b8c90c3212785082e2821b89205448c3324a591a4ac88a570451aa225ae2031e040c9e2046a325151238dfcb66fc5533a299be81870ca02ac4c2e146316952868a543212b7a08dbc82e3c4112ac07558050ab138ddc366ec15236099ba82ce2125ec892b8748fc2246d18a9e4052ee0263c192be0094ef848e972432505385c25b840c77b057bc029dd011aaa084ef027b7a5db7c98ec44a68c242e0831d6414a940877148b6e931d8494d16485bf063ac02952410edf1b3684c1b445ddb4a4e88506dc243b604992020b7c087686d9b5254da12eece916db263b3129a2090b7a0c765052a2821b692050a8c3628bdb0c52d152961092b602bda2152a1496b780c75f032770119b49450a8e35d2a98714cd700c3765013a261acc5ed62295b28c6492a4fa94ad5c2f49014b5605c770224e80ea520a13a271aa0547f0266a60b3728bdb8452db92fed697b694a7b2252d08a9e3e52ed8263b192bd7894eb648e7c2432305385825b740c75a057aa829d4811a72084ec02675821d400c9d2044ea245a702e3a41169e4a74d052738136e418e960a5b6042dc132d241f36c0cb4a27cda033d200cdae903324719d14cb58985aa903454719c94cce09e6884e34326944130c592a6825b3162918b34ece124e7c906d42450a049cf4209cc046d348152140ce9a9672d2b384959ba46a911ee6c0a5b304272811a949e548933342d999954cc89e662060e426033920b491944054a152950a04acb82365a0f9b30643381d1a40c0ce4a32b0d995054ca4264540f3466a7a134bb451968052f132959f947cf0a36764ff3527d98133a5c9948a14e12096d883338c10e5e06f2c0339401319808da08cb1e2bb8893ea30991c4087040322d811b391964a5171027d4593238010e060645a02366930b31206468e30f2998613cc889c6424d28826165a40c211c61c5331e8d98b960c5e2ee389270c48365122c6c24c86104df0238ba6cc64aa5928cb172bb8b145c549f5104c8de0438a01915008d909028628188c5ec422961ed4b0e69586a5ec312950c8f70b052d802137408cdc4f28649984954c209e60e060dc26024920c122f60714ac74652215279ca560417a430a58083e6c0190920743803024928bfc2a5fc131ef0799345ec9229640d4f1f69763232c74afe3457b182a789952c489fe144fb062673e13290429c2212dae0666d821c140de00066fd026240116b418df60a5ab042d6132be41f3560cafa27cd4833be00cdb6d42df69164a50b41244f0572882a146148bcc0c5ead22f44913a154bc8a45e251272289389449cca24e0512ef6c177260bb4b65d85826f28975860b792459e522dd6b174b48b392c5d09228b2b173948b98a25ca122db69571b46b5d2959892ae24756295dadcaadc20e56b0626c8219840c82c046de2896fc5eb76295b8d7adb6a56aa52b2d255b48ea9629b3d945b641ca900c4d70433001905408dac8d2d76a56ab4ab25255a891ad347b6215dad8aab4e0c6d20524002197c0c828046cf28966a34b422f59d14acc6a565b4ab292f59294ac847b4a94d9e8a2b4a0c6c70522c8219780c826046c56c162260af8b4554582c20a15dc5eaaa2ecf0d36c168b6004990020b48084d6023599549cca2018062be4d95e94caf09e5764b2b98d95c460adda856c942ab2d959150ad430566572aa4d959264ac4ae560552af2995713cab40c4e6512a10314e014a949e5464b2a00314d81468c109aa046a52894d014a8ca2532052a129950144a70265361129a0794c82c0300e55657aaa2bb5494da20a555051aa728b53144a909ed444b5a20626a021a7c0d53c0669d0314c01602c08d2cd62954b149158a1ca252812268289478189b8a24da5128f29936144a492e4d6952912994813ca380c50406275289408189cca25120626e2893f8149b4a24fc0526c2894134ea05a14fe0f27e0580401ca322f51714a8a2bd44152a1ca34d65168627b4292d684189a60868403541819a000c4fa058070233db489e9244d65226728139b449dc1c4ead32736a1392509c4a84e01426e2793692c9b00c4f117a768a53a35a9bdab4d6d3a6469b078499a820c200e5e4062d002134808cd05300803133a54998a64ca4f264258cf940344980064800c09004040985a94c0d2a5f4a52f24a958ad3c650a5d0bd2005283c254b81180303a01928968264b20f2f68bf7845bbaa2bdc914ee06a56c34ab452958c92ac32bf5f95eae8add6855eac2a74b952a4ca7d1a52e7c2953c9479a4a34c650e540b71f05383425bc210d9e062680219880dcb606658026010110300a4ac4a2530992803c934164aa092532632912993490c9c5100c0312823293c9f49a4ca544672883e9301733a5022d2711b04c67018336502492711a84c8d01e4900e247068a283033c984404a22a07867020334984884a2290791402c90c1448409054040cd03033010332500cb260091205ac201000c225059200288fc12016082042a91e86c81024408d3a344931d2418a0a4c72505980446501265ca02c4102366a51ab4a8d1254669196247b191298949099204963078b114c8c03645e1522e0791682c320980d40c22a4a514a4a8a0a544e51a2627d129321a896b2c0c86c0583513c88c36444152210991002c929a9c8cd2e454a720a4b8f919b2a4c8c72451e04b8042547611e3808d1b83f8c41f4580cd550651582f8901743e08c66044ca13231891418175ff07ca50327c8170b6089922646212287022bfc0f949064f882e168113220c1902810d1387f4263f40f2190710c0345141831e501f5270fe04c30c101844c215250f803c7b4164280a2130482a020304983ce4a1ef078c71303009031a0c0bf04108254630a017c4c011240a4040164183d60b20f0510702401c104191b2050c102c5d82924bf490609292f694162c1117a04a052d9038546289917848a050bb0204580c1f28a0ca0205c2a022624a0286101ff8bcff4527f5a93f8d29fb4bcfd25250d1ebf24a5eb2425d8124ac1e286531f70a8fb03c7d4161744c04b060f945e7c6293e0949ef494f715e7b4a93d84f9eb2642592d620190720b04b278f48547a0263ce0b21d8bd0dc5285da9c2cd2e124a708a4b83519b0e4c8b92450585f8202f40c14e010a50003f7e01f3e80cd39064f982f7a8173cc08c48044040147912a3c64a1e0098ee83c76c163c4091e0262ef92976c90810061dd464ee13e76c993c28cdde07ced02e6f5a8382d218a2a0ca1484d42e28a1414a090ea82c75da43ac521310a8ea04874c2225e1112e088968444c0223a2d81d04c0e79607383639a1812c088e024864c2437ed61cb690e5248648ac392521490b0e404871c2237ad29c568ce223968918b3a54990294e193a2dc9130c175770aa8c82e05811380111c18bcdfc526f9af37ad49bc472d0a3166ca931e529bb2745a92255026a701151805c0a8226dc2201a0b1b9498dc12845c1e36c0a1b5048d42302d01034ed01a2480599301f8900280c114058d98286c812016081a646059020695a0342900b12602b9204982a0260c113058d80286bc1200e08009058d6a4c6b09424a15116078d58286a8120fe4c1a80682c1304902234c0d0b02405792068d2215c4c0ad260c71382b09034ed49a5694d225e68929342929a048ccc952630a51564c19f254c005e5ac292901292308c8d83d6709a0fe4c19a248ceb5266da53328c58a294cc14665c9eb2c4b87e244c285d5d42aa220b812044c98446449a31c91058260c69246522f325149906a4c7b4a63118b165798a2a4c493d620970ae4895209a9b84544017022089866c0c29605f8342d2181832a0550205ee2f2d31753569ac1345604a4a2850580242548125cc2a2601100d058bf16c5f4262f80b17b038bcc6c5e2302eed41764c0ba9505a8362e4141730b8b496c5c8b22e2171700a8b784c5b81e2da0b0a8260b28444c0222c00b15c048b183c57c162b609158038538205949094c04963088ad024580262be1115c098ad8445681e01a0b157038ac04455c122d68c4a5244b505e5a42ead013545094b384659822ac81116207ab082e57816aba0b15904a058225580eaa8d6153490a91585402c28811121088a702c4ac2229c1312a08894844540ae2505514f098a683c530162800b1320889f82c2909826011146058958444f4122541114069c9fb424f41e0120b13b038948444ec12295179498a4a423128c9128e179450a4a20464a022a860f54205ca082d4f816278094070449d01d4e1a426e52128090900404c1a22684e132698983504bd2825c5412d0a09583c4a81625207124460510204911c142081358bc99c524c5ad258d592869c8eb4d44ca4a4e505262729293148c90940049210980482c480aa23e1311e0588e81c46da013e4c004060069240249201a520092808cb52461a522e969164848a95e450a92265291228c0212d44429220128042788704c434163b117dd28b6e645771a29b84d49ba694da25b6c529b5c92da9486cf231654a930e5289e244c205f5fc2f2f416d740aeb6053554292a213d4b0969c84a4d823a441191c0868d02f43c1721808c020446f25038924178540c62902205c150280b61210707884a48420a408015106090828440f82207a1103c0881f84440db0204981012c08006c3fc30076110e1290628483f5a41c0960fc490621583eca40b4160fa0907c8443d42201c0f0f74707b138090261e80e0f30686d1302e0181b2900d44605b9402949802c10021078788383c01a0160c0d82605b03035d201a68c0b5280519300d42a02a10020078770383b41a00e0c00a07875a383a89c06815023098748383a01a1bc928e648c72a3e3511919e548c2294599323909513a1748b0aa0f03e050191c2110e28bc7045237d2f1bc948dd47c69a32334a9182528b12646e12a1902688e1141d07c098322a0981b40d0a4260198443601a160480af2406aa442b89815a4c0c027056120365a91aed28d64bc6a25234d251a4918cb2a45f14a2ac981a24a8970bc40052164250641182707a671242a098198490cf4a466a4a32d19178528ca28c6493e294991904b49c0ba450550701f0240c8c508861924301221484c0bf2486345e31229184948c14945f2322f4af178548bb27c519322e8968c61344608a0d83e0441915c8c0b806856a300c42216c0d0ae4605a1242b518144510b224857a342c12715c908ad474562362a8a7150508a427450936258270fe10858074180362a89014e4d0a724054230298a21488c0a2270509202dda916ad28b34a458a4a2ad18152578a52a45194a280a313e4b4950bc3f05215c2505e1182607a4ea60270b01261a07c0c04d2502581012c480908bc3e45d111a6932d149849210a4125c9112a088880a81f8440381e1265b0920784882c2400e11d1b08d8c04636022d281145407d0d8438502202e0f85b0872c84305c2142a108130830784102c1fc980f0110770683fa301d82207e11073078378341c81e0dc0d06c0583481c1dc100ee480782443b0221cc260e41106f098370440381e0d60b068038360441ac1a0d211068068402321f8990fa1787c0ba3d84d150250f41187908a3a8441d01f0e20f4700783683502c190d40b46703a32b481912c0c6560610b0298440b4220c00f0600981d0440e422070110612b81b95417c260bc0f05d0582803c1042209e0f0582602c2300fc220aa0f03a0882834e13da10140f04c0582501c0e4220980d0380882503416e2f0b5148594642b9321582f0a81485308c1b8451481f0a20f44e0782683501c190960b44903a23a48118a406e1202c0801fb4410d1c082d303f6a01f2500f4a80781403a0781c82c0e00e0664c03106019a380c0100628e0302402245e10a29080d683b6ac1bb4e0a5a6840924364821aa390d1188644882f0441684c0281e0585502b0781502c0a40e04e90026280028400391a0148d00e49005240091ad046d08224bc10a520812503e9180547a0f152074a50381481b0940294c0641e0300b00f0880703c034160180700a0780482c0200e02cd48156940a25204d25024548112940805e02c2900e1280608c0283d010168060750a8be8245b3fa2b9f114cf26b677b533b1a59ced0ce34a46da4a3411918e548b92944f13226c2f9281788f0b644857204298cc1486209e2e04b1202508a11c2e08c140430941f8340f81706601032f45a7f8ed2fa868fc7b43e2925ee690f51477a6233d1ca5e4e50efc2777b93395c91c9612e1e086f283b76419a1608c010260001f 16 5 11 10 6
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 978 (dagTraceF m_31 s_31 8 f_31) l_31 0) s_31 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 64 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_2 : treeBlockF 64 96 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_3 : treeBlockF 96 128 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_4 : treeBlockF 128 160 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_5 : treeBlockF 160 192 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_6 : treeBlockF 192 224 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_7 : treeBlockF 224 256 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_8 : treeBlockF 256 288 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_9 : treeBlockF 288 320 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_10 : treeBlockF 320 352 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_11 : treeBlockF 352 384 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_12 : treeBlockF 384 416 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_13 : treeBlockF 416 448 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_14 : treeBlockF 448 480 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_15 : treeBlockF 480 512 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_16 : treeBlockF 512 544 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_17 : treeBlockF 544 576 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_18 : treeBlockF 576 608 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_19 : treeBlockF 608 640 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_20 : treeBlockF 640 672 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_21 : treeBlockF 672 704 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_22 : treeBlockF 704 736 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_23 : treeBlockF 736 768 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_24 : treeBlockF 768 800 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_25 : treeBlockF 800 832 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_26 : treeBlockF 832 864 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_27 : treeBlockF 864 896 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_28 : treeBlockF 896 928 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_29 : treeBlockF 928 960 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_30 : treeBlockF 960 978 (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nj_31_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_1 (fun _ h1 h2 => treeBlockF_at nb_31_2 h1 h2)
theorem nj_31_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_2 (fun _ h1 h2 => treeBlockF_at nb_31_3 h1 h2)
theorem nj_31_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_3 (fun _ h1 h2 => treeBlockF_at nb_31_4 h1 h2)
theorem nj_31_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_4 (fun _ h1 h2 => treeBlockF_at nb_31_5 h1 h2)
theorem nj_31_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_5 (fun _ h1 h2 => treeBlockF_at nb_31_6 h1 h2)
theorem nj_31_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_6 (fun _ h1 h2 => treeBlockF_at nb_31_7 h1 h2)
theorem nj_31_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_7 (fun _ h1 h2 => treeBlockF_at nb_31_8 h1 h2)
theorem nj_31_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_8 (fun _ h1 h2 => treeBlockF_at nb_31_9 h1 h2)
theorem nj_31_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_9 (fun _ h1 h2 => treeBlockF_at nb_31_10 h1 h2)
theorem nj_31_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_10 (fun _ h1 h2 => treeBlockF_at nb_31_11 h1 h2)
theorem nj_31_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_11 (fun _ h1 h2 => treeBlockF_at nb_31_12 h1 h2)
theorem nj_31_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_12 (fun _ h1 h2 => treeBlockF_at nb_31_13 h1 h2)
theorem nj_31_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_13 (fun _ h1 h2 => treeBlockF_at nb_31_14 h1 h2)
theorem nj_31_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_14 (fun _ h1 h2 => treeBlockF_at nb_31_15 h1 h2)
theorem nj_31_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_15 (fun _ h1 h2 => treeBlockF_at nb_31_16 h1 h2)
theorem nj_31_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_16 (fun _ h1 h2 => treeBlockF_at nb_31_17 h1 h2)
theorem nj_31_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_17 (fun _ h1 h2 => treeBlockF_at nb_31_18 h1 h2)
theorem nj_31_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_18 (fun _ h1 h2 => treeBlockF_at nb_31_19 h1 h2)
theorem nj_31_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_19 (fun _ h1 h2 => treeBlockF_at nb_31_20 h1 h2)
theorem nj_31_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_20 (fun _ h1 h2 => treeBlockF_at nb_31_21 h1 h2)
theorem nj_31_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_21 (fun _ h1 h2 => treeBlockF_at nb_31_22 h1 h2)
theorem nj_31_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_22 (fun _ h1 h2 => treeBlockF_at nb_31_23 h1 h2)
theorem nj_31_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_23 (fun _ h1 h2 => treeBlockF_at nb_31_24 h1 h2)
theorem nj_31_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_24 (fun _ h1 h2 => treeBlockF_at nb_31_25 h1 h2)
theorem nj_31_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_25 (fun _ h1 h2 => treeBlockF_at nb_31_26 h1 h2)
theorem nj_31_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_26 (fun _ h1 h2 => treeBlockF_at nb_31_27 h1 h2)
theorem nj_31_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_27 (fun _ h1 h2 => treeBlockF_at nb_31_28 h1 h2)
theorem nj_31_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_28 (fun _ h1 h2 => treeBlockF_at nb_31_29 h1 h2)
theorem nj_31_30 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := block_join nj_31_29 (fun _ h1 h2 => treeBlockF_at nb_31_30 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_31 g_31 bds_31 978 (dagTraceF m_31 s_31 8 f_31) l_31) i = true := nj_31_30
theorem lb_31 : LowerBin m_31 s_31 g_31 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xffffffff00000000
def s_32 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_32 : Nat := 0x111111500000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 6, g_17)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
def l_32 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 6 f_32) l_32 0) s_32 6 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_32 g_32 bds_32 0 (dagTraceF m_32 s_32 6 f_32) l_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xffffffff
def s_33 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_33 : Nat := 0x11151557
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 6, g_20), (m_21, s_21, 6, g_21), (m_22, s_22, 6, g_22), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_3, s_3, 4, g_3)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_21
  · exact lb_22
  · exact lb_18
  · exact lb_19
  · exact lb_3
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_33 : Nat → Nat × Nat := unpackForestF 0x169fe7929f3c14f908e7cc27de6019f209cf920fbc905de4039005a5f8a4a7c5053d4a51ef895f84513be247df02befc2277c08fa94a1dd93eeec0cf52547b425fdc144ed091f6806fb5089da013ea4a87620fbb105dd4851ea817f5c113aa047d501feac2275404fa90a000b47e9894f4c0a790473d092be8491f420afa1047c8238e789f73c06790273cc92fe6491f3206f99027c8138e581f72c0bb90073c882fe4411f2207f91027c8038005a1f1c0678b253c602ee2c1480292f894d9ba24bdd123f0a50785083ba246dd095f0251b81033ba129df4b66fa5537d031ba123dd015ef211b7905dba029dd4366ea15375059ba02300521ea517b7148ba9452dbe366a497f6c293b6049d492f6d4953524a7b2a5dd9522eca4a765053a9252d4895ebf17b5f8a5af95ed7c0cea44a75c2a9ae018d4891ea40af568bdab452d582f6ac0bb52053a9854d4c166a408c01477a8019d3494e9c0bb4d05200a33d2c14e904fb4907da4019004a5e50d4f43471a1938d0c9a650d2f412d99414bca0a3e7a9073d08394146ca09fe6cd4b366959b24acd92366c0a72827d9896ccc4aa6624f33103194133ca00de5a11b2d07d94019ca4366521532909994013004a1dfb17b2528b7ec52c851c6424e3212697eb53bf5a5e3d1b2fd2bf8da49c6c24dfa57b192a97e953c50aee285171427d8a019bf4a95fa4ff0b8bd85c52c2da9616d2b0b4bd85a52c2c14dfa4fb072a98393cc1c0c5fa4cefd03780c5ec062960217b0107d7e819bf82a5fc132fd0260093bbec14df04faf907d7c01900499cb117ef169178a48bcc0c5e2522f12892c45bbadb05d6982eb2d975960bac304b115ee569172a48b94a45ca512e50912c453b85a35c28eae10732c352b662f5bc512d98a56cb5eb65a95b28ead90732c34ab49a95ac8d2d269569246b491eda40a6584a563c5eb3ca258f14acd46963b52b1da558e97ac74a563a3db1c14cb092ac46c162260960afd84142c068b60049960af5769b2bb2995d93caec964b056eb58d95ac60ad5a856a942b50c12c157accae55a992ad2b956954ab4a655a4f2ad0312c153a60af5305769829b4c146a60a2d30512a52894c13da8ca25304b6a029950144a600d530066980314c84ca64225320f2990594c016960a9528d62944b14a048960a7d1c9728e2994713ca3ca651c062582973ec5e9f6294fa57a890313e9529f4a34fa4f67d25b3e81a9f40cd02d3a816853e8189f81e4fc0b27d02d2c14a9e9a44f49225828f3545e9dc1c4d514a756993535a9c1a84e0942702a1380509a9ab4d84f26c259360189a9a74d41065828d3414c9912a4c8532642793212c960a1cb006e5c6a52e34a971294b892a5c0bd2e0469600ccb2132590792c01300491caa4a2550492623394898ca44a64c07d26a329349f49c5124d2652602e00425c3ed4e472712383891c1a43ed2e1f4a721128908144840921f4971f8288fc1243e8ce3d0d90f84b87c23c72906392830f84687c1fc64d4a326951924a8c9234644a61f07d1686c8b42a45a0f22d0590f83387c17c4a94a254951294a894a344a4fa252650f82e88036440152200991002c87c1180210de68bd0e04579a294304e2180710c034799a9bccd2e132510982884c123cc94de6497072548381441c091e64670646c7982fc1292609292f305e81c2a3cc14e020bb010458081f4040b9e60a4f303f7e62f3f3149f96a4fcb4a7e52f3f2949f9252f303e7d42a3ea0f1f5058f303379817bd7179eb8a4f5a527ad253d6579eb2a4f593e7ac993cc0b9e70a8f384c79c163cc08c01076f1254788943c4091da466ef93177c94bb40f9db464ed93e76c993b40b8010668645f74da43a6521d5058e984874c2221916dcd6c0e6a60734b039a1b1cd0c08645771da438e921c7290e384871c2221914dc368ce1a3970c9d218d49bb8bce00446ee29376d79bb6a4dda396ec9d218d29b5498da9286dc2236a0a1b50488625b6c8143640910c4a6d78286bc1221892daa498d51286a8143540910c486d403467da934c0d19f694cfa5e68d2233e9499f494cfa4667c952188c5966a4ce134659a533449196462cb1466589eb2c4b90c2a4c445e64c2231114991268c4352621a531a9118d248c4231620af3105498827ac412e430a530ad81852c08605f60ca8300d1580292c01214302f2f65b17b098bd82c5ec0e21816d758d8bac605d5a82ea981752a0860575cc2e2da5916d0b8b68545b4262da0f16d0588605355918aac179560baab04d558232ac11565242ab04458c222ac0f55605caf84c57c222ac0b556058ad04c568222b40f15604aab84455c122ac0750c0a4a9358549242a45610c09ea615c5302629c1314c078a602c43025a751793a8a49d2314e82f28c0b13a0a49d0464e81ea740b93a05a9fb4e4fda12740b13d0789d0254ec122740750c0949bb484dca421811d238bc9a13848e29264d31236b496b504b52825a5412d0a091b564a41e2520b12903891b4e48ca0a464e5232629223848c90a18119210988e9544742623a0b11d0388604346da02180bd106a48834a4412d220909102bc88152440a5220519100a48804a4301721a1310d058860230041180517d054908294841c1e20a121050880145b3fdb01fe980ff2c07f86c3fc3000515cf96907ca483e4a41f2120f9088014533cd1c1e64e0f5088798383cc1a004d6cf007078034009a99da0e0ed0680134b3a11c1d04e0e807074034009a19c8918e447c7212a009291b9178e10886e4523712f1b8948dc47c6e12a009251b40d0d16a46c034345a51a2978d548868a52345251a2918d1254012323212919c490c84946612432119190518c827c6412d008a9175178c50885d45230c92174948ba4945fa442fc921748c8ba2bc5d1522e89f1744b4022945c03427da916c0d09f6945a12427d291644909f4945624e2bd1a158908ac4745623627d181544809f2bc5323029c9014c5109f2a45223027ca51424e0a12404f94627c968044c89c4c04e1600082f9349409568a4aa492549112c480950440105e240b61200f0900584801c0082d9151b08a8c04536022928114540020ae4405c208b2104170820a84104c2081e1040b0020a633a321fd180ce4c8670bc3385d19c268ce1186708a3b1221dc900ec088670883383e1c8260e41106707a3383c1b8260dc1106706a358441ac1a0ce0b4680883403419c0e8041486369031a5818cac00413c5d2b83004c174260ba0f05d0580104b1262f093148494642c230124990921785507824852124230920f84907a27b4e13da10920f04906a26034124168940d04903a0104a1192408c5200208e17c5e10d1c05f1484169817b5a0f1a80789403c2a01e0500bdab0700f0380581c01c0bda705e9042f47217a310cd1c05e48830470181200bc110041182d098149540a41e0520b029038010430992004c5000207e0db5a06da10369781b4a40da4a06d230365481b2940d85206c250040f8180780c02c00819806d480369401a5200d25006548032940185e030220180f00c0580601c00c290100f0080580401c00c250061180307a0182d00c0e8040c8010260001f 10 11
def l_33 : Nat → Nat → Option Nat := unpackLinksF 0xe609e600e600e546e540e540e486e480e480e3c6e306e300e300e246e240e240e221e220e220e201e165e160e160e0a6e0a0e0a0e081e080e080e061dfc5dfc0dfc0df06df00df00dee1dee0dee0dec1de25dd09dd00dd00dc46dc40dc40dc40dc40dba5dba0dba0dae6dae0dae0dae0dae0da45da40da40d986d980d980d980d980d8e5d76cd760d703d700d6a3d643d640d602d5e1d5e0d5e0d507d4c2d4c0d4c0d3c8d3c0d3a1d3a0d305d2c2d2c0d2c0d1c8d1c0d1a1d1a0d105ceb3cdc7cdc0cce7cce0cca2cca0cca0cbc7cbc0cb82cb80cb80cb80cb80ca88ca42ca40ca40ca40ca40c90ac8e1c8e0c864c822c820c820c820c820c6eac6c1c6c0c644c3b5c3a0c343c340c2e3c283c280c223c220c1c3c163c103c100c100c0e1c007c000bfc2bfa1bfa0bfa0bec7be82be80be80be80be80be80bd88bd80bd61bd60bd60bcc5bc82bc80bc80bb88bb80bb61bb60bac5b873b787b780b6a7b6a0b6a0b681b5a7b543b540b502b500b500b427b420b3e2b3e0b3e0b3e0b3e0b2e8b2a2b2a0b2a0b2a0b2a0b2a0b2a0b2a0b16ab141b140b140b0c4b082b080b080b080b080af4aaf21af20aea4ac15ac00aba3aba0ab43aae3aa07aa00aa00aa00a9e1a9e0a945a921a901a900a8e1a8c1a806a800a800a800a7c2a7c0a6c8a6c0a6c0a6c0a54ca540a540a521a520a520a520a520a36ea360a360a341a340a340a340a1cca1c0a1c0a1a1a1a0a181a180a180a180a180a1809fce9fc09fc09f449f409f219f209e289e019e009e009dc29d449d409d409d409d409d409c679c609c419c409c409c409c409c409b679b609b609b039b009a849a429a409a029a0099c299c099c0998299809980998099809980998098e596f096e096e096e09645960295e195c195c0958294e594c194829480948094429440940293c293a193a093a093a09362936093609303912f9120912090a490a090a090629060904190409040904090408fc48fc08fc08fc08f638f608dec8de08dc18dc08dc08da18d248cc38cc08cc08cc08cc08ca18c818b2b8b208b208ac3871e86e186e086458640864085e385e085e085e085a2854384e38483848084808461838783238320832083018227822081e280c980c080828061806080607f877f427f407f407f407f407f407e487e407e217e207e207d857d427d407d407d407d407d407d407c487c407c217c207c207b857933784778407767776077607741766776037600760075e1750774a374627460742272ea72e072a272a072a071c771c0718271807180718071807088704270407040704070407040704070406f0a6ee16ee06ee06e646e226e206e206e206e206e206e206e206e206cea6cc16cc06cc06c4469b569a06981698068c668c068c0686368606860684167e3678366a766a066a066a06681668065e565c165a165816580656164a664a064a064a064a06462636863606360636061ec61e061e061c161c061c061c061c0600e6000600060005fc25fc05f255f205ee25dc95dc05d825c4a5c405c405c215c205b665b605b225b205ac35aa15a815a425a2159e259e0580f5800580057e157e057a257a057a057a0562c562056205601560055e155e055e055e05583558055805580558053ce53c053c053445340532153205301520851e151e051e051a2512451205120512051205120504750405021502050205020502050204f474f024f004f004ea34ea04e244e014dc24dc04d824d804d804d804d424d404d404d404d404ca54ca04ca04c624a704a604a604a6049c54982496149604922490148654841480247e147e047e047a247a0476247604741474047404702470046a346a04662448f4480448044044400440043c243c043a143a043a043a043a0432443204320432042c342c0428242804280424240cc40c040a140a040a04081400440003fa33fa03fa03f813f613f413f403f403f213f203f203dcb3dc03dc03d6339be38c738c038c038c038a138a0380537e137c137a137a0378136c636c036c036c036c0368235883580358035803542354034a534a0346233493340330231ca31c031c031a131a030e630e030e030e02f6c2f602f602f412f402f402f402f402d8e2d802d422d402ce32cc12ca12c622c412c022c002a2f2a202a202a012a0029c229c029c029c0284c2840284028212820280128002800280027a327a027a027a027a025ee25e025a225a0254325402502250024a324a024a0248124802480230c230022e122c122c022a12262226022412240224022022200202f202020201fa41fa01f811f801f611f601f411e481e211e201e201de21d641d601d601d601d601d601c871c801c611c601c601c601c601c601b871b421b211ae21ae01ae01a831a801a0419e119e019c11982198019801980194219401940194018a518a018a018621860186018221630162016201620158515421540150214e114c11425140113c213a113a013811380138013421340134013211320132012e212831280124212401202102f102010200fa40fa00fa00f620f600f410f400f400f400f400ec40ec00ec00ec00e630e600e220e200e200de20de00de00da20c2c0c200c010c000c000be10b640b600b600b030ae10ac10aa10aa00aa00a810a800a800a800a80092b0920092008c308c008c008c008c008c008c008c008c008c008c008c0084408400840084007e307e007e007e007e0064d029e00330001 0x1b2241dc91ce26507262737b12380420c3a0e5d804685013bd498fa04a6f2242eb831f3c14ba8086f4465e693ebc899212087cc032830117589921048bca07cea032f241720c08bce473e5939bc091f900e5d204682013bbc98f8c4a6ec242e8831f1414b9a087c2289df844f0c95f8248fc0057df02340c09ddc8cbbc27d7613240810f76064ff023dc144ed4227724bfb7246e8023ed80df6804dcf26480922ec81f39a0cbb105c7f822eb822756112eb247d782feb411f5807faa027e2251ef528774547b32a175123ec028f52141cc0467f013ba498f4e4a6e7242e5831e9814b90087a4257d1923e8815f4208cfd02774232e7c9f5ce4c8fc043cf0193e808f384bf9b246e5023e680df3204dc92647d922e5c1f3900cb9605c7d022b9491f280bf93047c901fe4409ee0927a5473d0238c90a4f3a4e7982717212386c24f2a0e790070e30233e0099ee0878e0327a0113d8917180b8f4045c6929e2c149e404f676a9c4a6cd9d246ced3b22293c3141b8c90c3212785082e2821b89205448c3324a591a4ac88a570451aa225ae2031e040c9e2046a325151238dfcb66fc5533a299be81870ca02ac4c2e146316952868a543212b7a08dbc82e3c4112ac07558050ab138ddc366ec15236099ba82ce2125ec892b8748fc2246d18a9e4052ee0263c192be0094ef848e972432505385c25b840c77b057bc029dd011aaa084ef027b7a5db7c98ec44a68c242e0831d6414a940877148b6e931d8494d16485bf063ac02952410edf1b3684c1b445ddb4a4e88506dc243b604992020b7c087686d9b5254da12eece916db263b3129a2090b7a0c765052a2821b692050a8c3628bdb0c52d152961092b602bda2152a1496b780c75f032770119b49450a8e35d2a98714cd700c3765013a261acc5ed62295b28c6492a4fa94ad5c2f49014b5605c770224e80ea520a13a271aa0547f0266a60b3728bdb8452db92fed697b694a7b2252d08a9e3e52ed8263b192bd7894eb648e7c2432305385825b740c75a057aa829d4811a72084ec02675821d400c9d2044ea245a702e3a41169e4a74d052738136e418e960a5b6042dc132d241f36c0cb4a27cda033d200cdae903324719d14cb58985aa903454719c94cce09e6884e34326944130c592a6825b3162918b34ece124e7c906d42450a049cf4209cc046d348152140ce9a9672d2b384959ba46a911ee6c0a5b304272811a949e548933342d999954cc89e662060e426033920b491944054a152950a04acb82365a0f9b30643381d1a40c0ce4a32b0d995054ca4264540f3466a7a134bb451968052f132959f947cf0a36764ff3527d98133a5c9948a14e12096d883338c10e5e06f2c0339401319808da08cb1e2bb8893ea30991c4087040322d811b391964a5171027d4593238010e060645a02366930b31206468e30f2998613cc889c6424d28826165a40c211c61c5331e8d98b960c5e2ee389270c48365122c6c24c86104df0238ba6cc64aa5928cb172bb8b145c549f5104c8de0438a01915008d909028628188c5ec422961ed4b0e69586a5ec312950c8f70b052d802137408cdc4f28649984954c209e60e060dc26024920c122f60714ac74652215279ca560417a430a58083e6c0190920743803024928bfc2a5fc131ef0799345ec9229640d4f1f69763232c74afe3457b182a789952c489fe144fb062673e13290429c2212dae0666d821c140de00066fd026240116b418df60a5ab042d6132be41f3560cafa27cd4833be00cdb6d42df69164a50b41244f0572882a146148bcc0c5ead22f44913a154bc8a45e251272289389449cca24e0512ef6c177260bb4b65d85826f28975860b792459e522dd6b174b48b392c5d09228b2b173948b98a25ca122db69571b46b5d2959892ae24756295dadcaadc20e56b0626c8219840c82c046de2896fc5eb76295b8d7adb6a56aa52b2d255b48ea9629b3d945b641ca900c4d70433001905408dac8d2d76a56ab4ab25255a891ad347b6215dad8aab4e0c6d20524002197c0c828046cf28966a34b422f59d14acc6a565b4ab292f59294ac847b4a94d9e8a2b4a0c6c70522c8219780c826046c56c162260af8b4554582c20a15dc5eaaa2ecf0d36c168b6004990020b48084d6023599549cca2018062be4d95e94caf09e5764b2b98d95c460adda856c942ab2d959150ad430566572aa4d959264ac4ae560552af2995713cab40c4e6512a10314e014a949e5464b2a00314d81468c109aa046a52894d014a8ca2532052a129950144a70265361129a0794c82c0300e55657aaa2bb5494da20a555051aa728b53144a909ed444b5a20626a021a7c0d53c0669d0314c01602c08d2cd62954b149158a1ca252812268289478189b8a24da5128f29936144a492e4d6952912994813ca380c50406275289408189cca25120626e2893f8149b4a24fc0526c2894134ea05a14fe0f27e0580401ca322f51714a8a2bd44152a1ca34d65168627b4292d684189a60868403541819a000c4fa058070233db489e9244d65226728139b449dc1c4ead32736a1392509c4a84e01426e2793692c9b00c4f117a768a53a35a9bdab4d6d3a6469b078499a820c200e5e4062d002134808cd05300803133a54998a64ca4f264258cf940344980064800c09004040985a94c0d2a5f4a52f24a958ad3c650a5d0bd2005283c254b81180303a01928968264b20f2f68bf7845bbaa2bdc914ee06a56c34ab452958c92ac32bf5f95eae8add6855eac2a74b952a4ca7d1a52e7c2953c9479a4a34c650e540b71f05383425bc210d9e062680219880dcb606658026010110300a4ac4a2530992803c934164aa092532632912993490c9c5100c0312823293c9f49a4ca544672883e9301733a5022d2711b04c67018336502492711a84c8d01e4900e247068a283033c984404a22a07867020334984884a2290791402c90c1448409054040cd03033010332500cb260091205ac201000c225059200288fc12016082042a91e86c81024408d3a344931d2418a0a4c72505980446501265ca02c4102366a51ab4a8d1254669196247b191298949099204963078b114c8c03645e1522e0791682c320980d40c22a4a514a4a8a0a544e51a2627d129321a896b2c0c86c0583513c88c36444152210991002c929a9c8cd2e454a720a4b8f919b2a4c8c72451e04b8042547611e3808d1b83f8c41f4580cd550651582f8901743e08c66044ca13231891418175ff07ca50327c8170b6089922646212287022bfc0f949064f882e168113220c1902810d1387f4263f40f2190710c0345141831e501f5270fe04c30c101844c215250f803c7b4164280a2130482a020304983ce4a1ef078c71303009031a0c0bf04108254630a017c4c011240a4040164183d60b20f0510702401c104191b2050c102c5d82924bf490609292f694162c1117a04a052d9038546289917848a050bb0204580c1f28a0ca0205c2a022624a0286101ff8bcff4527f5a93f8d29fb4bcfd25250d1ebf24a5eb2425d8124ac1e286531f70a8fb03c7d4161744c04b060f945e7c6293e0949ef494f715e7b4a93d84f9eb2642592d620190720b04b278f48547a0263ce0b21d8bd0dc5285da9c2cd2e124a708a4b83519b0e4c8b92450585f8202f40c14e010a50003f7e01f3e80cd39064f982f7a8173cc08c48044040147912a3c64a1e0098ee83c76c163c4091e0262ef92976c90810061dd464ee13e76c993c28cdde07ced02e6f5a8382d218a2a0ca1484d42e28a1414a090ea82c75da43ac521310a8ea04874c2225e1112e088968444c0223a2d81d04c0e79607383639a1812c088e024864c2437ed61cb690e5248648ac392521490b0e404871c2237ad29c568ce223968918b3a54990294e193a2dc9130c175770aa8c82e05811380111c18bcdfc526f9af37ad49bc472d0a3166ca931e529bb2745a92255026a701151805c0a8226dc2201a0b1b9498dc12845c1e36c0a1b5048d42302d01034ed01a2480599301f8900280c114058d98286c812016081a646059020695a0342900b12602b9204982a0260c113058d80286bc1200e08009058d6a4c6b09424a15116078d58286a8120fe4c1a80682c1304902234c0d0b02405792068d2215c4c0ad260c71382b09034ed49a5694d225e68929342929a048ccc952630a51564c19f254c005e5ac292901292308c8d83d6709a0fe4c19a248ceb5266da53328c58a294cc14665c9eb2c4b87e244c285d5d42aa220b812044c98446449a31c91058260c69246522f325149906a4c7b4a63118b165798a2a4c493d620970ae4895209a9b84544017022089866c0c29605f8342d2181832a0550205ee2f2d31753569ac1345604a4a2850580242548125cc2a2601100d058bf16c5f4262f80b17b038bcc6c5e2302eed41764c0ba9505a8362e4141730b8b496c5c8b22e2171700a8b784c5b81e2da0b0a8260b28444c0222c00b15c048b183c57c162b609158038538205949094c04963088ad024580262be1115c098ad8445681e01a0b157038ac04455c122d68c4a5244b505e5a42ead013545094b384659822ac81116207ab082e57816aba0b15904a058225580eaa8d6153490a91585402c28811121088a702c4ac2229c1312a08894844540ae2505514f098a683c530162800b1320889f82c2909826011146058958444f4122541114069c9fb424f41e0120b13b038948444ec12295179498a4a423128c9128e179450a4a20464a022a860f54205ca082d4f816278094070449d01d4e1a426e52128090900404c1a22684e132698983504bd2825c5412d0a09583c4a81625207124460510204911c142081358bc99c524c5ad258d592869c8eb4d44ca4a4e505262729293148c90940049210980482c480aa23e1311e0588e81c46da013e4c004060069240249201a520092808cb52461a522e969164848a95e450a92265291228c0212d44429220128042788704c434163b117dd28b6e645771a29b84d49ba694da25b6c529b5c92da9486cf231654a930e5289e244c205f5fc2f2f416d740aeb6053554292a213d4b0969c84a4d823a441191c0868d02f43c1721808c020446f25038924178540c62902205c150280b61210707884a48420a408015106090828440f82207a1103c0881f84440db0204981012c08006c3fc30076110e1290628483f5a41c0960fc490621583eca40b4160fa0907c8443d42201c0f0f74707b138090261e80e0f30686d1302e0181b2900d44605b9402949802c10021078788383c01a0160c0d82605b03035d201a68c0b5280519300d42a02a10020078770383b41a00e0c00a07875a383a89c06815023098748383a01a1bc928e648c72a3e3511919e548c2294599323909513a1748b0aa0f03e050191c2110e28bc7045237d2f1bc948dd47c69a32334a9182528b12646e12a1902688e1141d07c098322a0981b40d0a4260198443601a160480af2406aa442b89815a4c0c027056120365a91aed28d64bc6a25234d251a4918cb2a45f14a2ac981a24a8970bc40052164250641182707a671242a098198490cf4a466a4a32d19178528ca28c6493e294991904b49c0ba450550701f0240c8c508861924301221484c0bf2486345e31229184948c14945f2322f4af178548bb27c519322e8968c61344608a0d83e0441915c8c0b806856a300c42216c0d0ae4605a1242b518144510b224857a342c12715c908ad474562362a8a7150508a427450936258270fe10858074180362a89014e4d0a724054230298a21488c0a2270509202dda916ad28b34a458a4a2ad18152578a52a45194a280a313e4b4950bc3f05215c2505e1182607a4ea60270b01261a07c0c04d2502581012c480908bc3e45d111a6932d149849210a4125c9112a088880a81f8440381e1265b0920784882c2400e11d1b08d8c04636022d281145407d0d8438502202e0f85b0872c84305c2142a108130830784102c1fc980f0110770683fa301d82207e11073078378341c81e0dc0d06c0583481c1dc100ee480782443b0221cc260e41106f098370440381e0d60b068038360441ac1a0d211068068402321f8990fa1787c0ba3d84d150250f41187908a3a8441d01f0e20f4700783683502c190d40b46703a32b481912c0c6560610b0298440b4220c00f0600981d0440e422070110612b81b95417c260bc0f05d0582803c1042209e0f0582602c2300fc220aa0f03a0882834e13da10140f04c0582501c0e4220980d0380882503416e2f0b5148594642b9321582f0a81485308c1b8451481f0a20f44e0782683501c190960b44903a23a48118a406e1202c0801fb4410d1c082d303f6a01f2500f4a80781403a0781c82c0e00e0664c03106019a380c0100628e0302402245e10a29080d683b6ac1bb4e0a5a6840924364821aa390d1188644882f0441684c0281e0585502b0781502c0a40e04e90026280028400391a0148d00e49005240091ad046d08224bc10a520812503e9180547a0f152074a50381481b0940294c0641e0300b00f0880703c034160180700a0780482c0200e02cd48156940a25204d25024548112940805e02c2900e1280608c0283d010168060750a8be8245b3fa2b9f114cf26b677b533b1a59ced0ce34a46da4a3411918e548b92944f13226c2f9281788f0b644857204298cc1486209e2e04b1202508a11c2e08c140430941f8340f81706601032f45a7f8ed2fa868fc7b43e2925ee690f51477a6233d1ca5e4e50efc2777b93395c91c9612e1e086f283b76419a1608c010260001f 16 5 11 10 6
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 978 (dagTraceF m_33 s_33 8 f_33) l_33 0) s_33 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 64 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_2 : treeBlockF 64 96 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_3 : treeBlockF 96 128 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_4 : treeBlockF 128 160 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_5 : treeBlockF 160 192 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_6 : treeBlockF 192 224 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_7 : treeBlockF 224 256 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_8 : treeBlockF 256 288 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_9 : treeBlockF 288 320 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_10 : treeBlockF 320 352 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_11 : treeBlockF 352 384 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_12 : treeBlockF 384 416 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_13 : treeBlockF 416 448 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_14 : treeBlockF 448 480 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_15 : treeBlockF 480 512 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_16 : treeBlockF 512 544 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_17 : treeBlockF 544 576 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_18 : treeBlockF 576 608 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_19 : treeBlockF 608 640 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_20 : treeBlockF 640 672 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_21 : treeBlockF 672 704 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_22 : treeBlockF 704 736 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_23 : treeBlockF 736 768 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_24 : treeBlockF 768 800 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_25 : treeBlockF 800 832 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_26 : treeBlockF 832 864 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_27 : treeBlockF 864 896 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_28 : treeBlockF 896 928 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_29 : treeBlockF 928 960 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_30 : treeBlockF 960 978 (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nj_33_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_1 (fun _ h1 h2 => treeBlockF_at nb_33_2 h1 h2)
theorem nj_33_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_2 (fun _ h1 h2 => treeBlockF_at nb_33_3 h1 h2)
theorem nj_33_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_3 (fun _ h1 h2 => treeBlockF_at nb_33_4 h1 h2)
theorem nj_33_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_4 (fun _ h1 h2 => treeBlockF_at nb_33_5 h1 h2)
theorem nj_33_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_5 (fun _ h1 h2 => treeBlockF_at nb_33_6 h1 h2)
theorem nj_33_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_6 (fun _ h1 h2 => treeBlockF_at nb_33_7 h1 h2)
theorem nj_33_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_7 (fun _ h1 h2 => treeBlockF_at nb_33_8 h1 h2)
theorem nj_33_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_8 (fun _ h1 h2 => treeBlockF_at nb_33_9 h1 h2)
theorem nj_33_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_9 (fun _ h1 h2 => treeBlockF_at nb_33_10 h1 h2)
theorem nj_33_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_10 (fun _ h1 h2 => treeBlockF_at nb_33_11 h1 h2)
theorem nj_33_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_11 (fun _ h1 h2 => treeBlockF_at nb_33_12 h1 h2)
theorem nj_33_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_12 (fun _ h1 h2 => treeBlockF_at nb_33_13 h1 h2)
theorem nj_33_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_13 (fun _ h1 h2 => treeBlockF_at nb_33_14 h1 h2)
theorem nj_33_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_14 (fun _ h1 h2 => treeBlockF_at nb_33_15 h1 h2)
theorem nj_33_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_15 (fun _ h1 h2 => treeBlockF_at nb_33_16 h1 h2)
theorem nj_33_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_16 (fun _ h1 h2 => treeBlockF_at nb_33_17 h1 h2)
theorem nj_33_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_17 (fun _ h1 h2 => treeBlockF_at nb_33_18 h1 h2)
theorem nj_33_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_18 (fun _ h1 h2 => treeBlockF_at nb_33_19 h1 h2)
theorem nj_33_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_19 (fun _ h1 h2 => treeBlockF_at nb_33_20 h1 h2)
theorem nj_33_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_20 (fun _ h1 h2 => treeBlockF_at nb_33_21 h1 h2)
theorem nj_33_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_21 (fun _ h1 h2 => treeBlockF_at nb_33_22 h1 h2)
theorem nj_33_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_22 (fun _ h1 h2 => treeBlockF_at nb_33_23 h1 h2)
theorem nj_33_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_23 (fun _ h1 h2 => treeBlockF_at nb_33_24 h1 h2)
theorem nj_33_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_24 (fun _ h1 h2 => treeBlockF_at nb_33_25 h1 h2)
theorem nj_33_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_25 (fun _ h1 h2 => treeBlockF_at nb_33_26 h1 h2)
theorem nj_33_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_26 (fun _ h1 h2 => treeBlockF_at nb_33_27 h1 h2)
theorem nj_33_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_27 (fun _ h1 h2 => treeBlockF_at nb_33_28 h1 h2)
theorem nj_33_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_28 (fun _ h1 h2 => treeBlockF_at nb_33_29 h1 h2)
theorem nj_33_30 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := block_join nj_33_29 (fun _ h1 h2 => treeBlockF_at nb_33_30 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_33 g_33 bds_33 978 (dagTraceF m_33 s_33 8 f_33) l_33) i = true := nj_33_30
theorem lb_33 : LowerBin m_33 s_33 g_33 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def g_34 : Nat := 0x111111511151557
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 9, g_33), (m_31, s_31, 9, g_31), (m_29, s_29, 9, g_29), (m_27, s_27, 9, g_27), (m_23, s_23, 9, g_23), (m_25, s_25, 8, g_25), (m_24, s_24, 8, g_24), (m_32, s_32, 7, g_32), (m_30, s_30, 7, g_30), (m_28, s_28, 7, g_28), (m_26, s_26, 7, g_26), (m_4, s_4, 7, g_4), (m_17, s_17, 6, g_17), (m_15, s_15, 6, g_15), (m_16, s_16, 6, g_16), (m_12, s_12, 6, g_12), (m_20, s_20, 6, g_20), (m_21, s_21, 6, g_21), (m_22, s_22, 6, g_22), (m_11, s_11, 6, g_11), (m_8, s_8, 6, g_8), (m_5, s_5, 6, g_5), (m_13, s_13, 5, g_13), (m_14, s_14, 5, g_14), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_10, s_10, 5, g_10), (m_9, s_9, 5, g_9), (m_7, s_7, 5, g_7), (m_6, s_6, 5, g_6), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1), (m_0, s_0, 4, g_0)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_33
  · exact lb_31
  · exact lb_29
  · exact lb_27
  · exact lb_23
  · exact lb_25
  · exact lb_24
  · exact lb_32
  · exact lb_30
  · exact lb_28
  · exact lb_26
  · exact lb_4
  · exact lb_17
  · exact lb_15
  · exact lb_16
  · exact lb_12
  · exact lb_20
  · exact lb_21
  · exact lb_22
  · exact lb_11
  · exact lb_8
  · exact lb_5
  · exact lb_13
  · exact lb_14
  · exact lb_18
  · exact lb_19
  · exact lb_10
  · exact lb_9
  · exact lb_7
  · exact lb_6
  · exact lb_3
  · exact lb_2
  · exact lb_1
  · exact lb_0
theorem sub_34 : ∀ b ∈ bds_34, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_34 : Nat → Nat × Nat := unpackForestF 0xc5fe8b49e8a49e8949e884900c53e4b57e4a3be4a39e493be4939e483be483900b53e1d62e1b6ee1a39e1939e183900b4bdfa39df939df83900b43dea44d9c5bd9a57d9a4fd9a4ed992bdbc5bd9929d982bda45bd982900a53d4d62d7244d7149d7049d4c63d4a6ed4a4ed4929d482900a4bd2a4ed2929d282900a43cd56fd0959d0859cd563cd462cd362cd26ecd262cd129cd02900a33cc144c345bcb134c335bc3343c9b43c3157c314fc825bc314ec313fc6c5bc313ec5c53c301bc3c5bc3b5bc3b43c301900953b7d62c0b49c0944c0849b7c63beb5ebe934be839b7b63bb672bb572bb472bb37ebb372bb039b7b43ba233b796eb794eb793eb8343b78190094bb6824b6039b3b43b394eb393eb4343b381900943a5d6fb1b59b1859a5d63a5c62af367af03baf039a5b63ace72acd72acb7eac839a5b5bab839a5b53aab5ba5a62a9a4ba596ea8b5ba5962a593ea635ba6834a6353a5819009339756fa3c59a385997563a1c67a184ba1849974639fe729fc7e9f8499745b9e849974539dc5b973629cc5b972629bb4b9716e9ac5b971629714e9714297c5b9804497c539701900923960448445b950348435b8434392c5393343928248425b918449146b84243900548fd6b842338db438da438da33840578ca338404f8aa5b8a95b8a9238404e89a538403f87c5b8795b879438403e86c538402f84c5b84b5b84b438402e008536a56281b4981a49818446a4637fb5e7fa397f8346a3637c6727c5727c4727c37e7c3727c2396a343794537925e7924e79b43790246a26374e7274d727704474c7374b7274a7e74a7274a4e6a2436fe72730546fd736fc726fb726fa7e6fa726fa5e6fa526a2336da336d9336d9236a06e6c9236a04e6b9436a03e6ab436a02e0084b6902468a3961343678346724e612436604464a5e6502464a5261233639236104e629436103e61b436102e008434356f5f3595f25943563434625cb675ca3b5ca39433635a6725a5725a37e5a2394335b5923943353582445646b562675624f5624e4326352e7252d725424452c7352a7e52a4e4325b51a4e432534de7f4de734dd724dc724db724da7e4da72432334bb5b4ba5b4ba334316249a4b4994b499234306e47b5b47a5b47a33430624595b46134459534303e43b5b4413443b534302e008332356f4145941259235633f4673f24b3f249234633d6723d47e3d2492345b3c249234533b45b233623a2543856b382673825f3825e2326334e7236a5434d7334c7234a7e34a5e2325b33a5e232532fe7f2fe732fd722fc722fb722fa7e2fa72232432dc5b2da5b2da43231622bb4b2b94b2b9332306e29c5b29a5b29a43230622795b28144279532304e25a5b2602425a532304223c5b2414423c532302e008230156f2145921359015631f4671f34b1f349014631d6721d47e1d3490145b1c349014531b3541956b193671935f1935e013631667217b54165731637e1635e0135b1535e0135311e7f11e7311d7211c7211b7e11b72013430fc5b0fb5b0fb43012620dc5b0db5b0db43011620bb4b0ba4b0ba330106e09c5b09b5b09b430106207a5b0824407a530104e05b5b0603405b530104203c5b0424403c530103e01c5b0204401c5301032008130003f 9 11
def l_34 : Nat → Nat → Option Nat := unpackLinksF 0x1d39ba41f423e787cd8f8d77143e243c30f850f043e043bf0f6b9ed03d947b207630ec41d5d7ab07550ea81d38da6874546843d0439f0f3d0e7a0ce879c8739066c3c8e7900f1f0e3e0c7c18ba3141e261c4838887065e0a1c1038186fd35f81bf017e02f72de83bc47770eeb1dd22b9c56b46d50d9a8b3036222be357c0aec75d06ba056e3ad835b02b31d660ac835902b205640abc74e4e991d320a6034c029045200a3c3478287450e0a1c1438287050e0a1c13eaa7d04f439e433c067804ee19b1736026b0cd0399c333066604ca197cd2f065e04bc0964b2b0e5604ac09581281a5004a009401280246548c090c72182401c8008f471e823a1c7028e011c02370c6a2892311862304460878b0f021e043c0860d0c021804300839507020b1c16082070402051c0a080870101ff1bfa27ec4fd81fb03f417e04f3c5e60bbc87742eaa1cf339c17380e685c5438a07102df19be037a16dccdb81b7036e06d06da01b30b6606cc0d981b01b6006bc2d781af035e06b06d601ab0b5606ac0d581a81b2b36486c90192032216250c48189031016010c00180030006000c0018002eca5d42ba817502ea05d02b6216c02d805b00b5856b02d605ac0b5816152c205840b0056002c005800b0016002c005594ab015602ac054c6a981520aa405442a881500a8ab5140a205411a82050029e8d3d027814f009d85381a7004dc29b81360a6c04d4297992e0a5c04b809495261a4c04980930120324004800900120022ca4580898d1302241448089011202186430086010c0216142c0858101520203f867f00fe01fc03f807f00fe01fc03d147a00f401e803c467880f101e203b867700ee01dc03ac67580eb01d413a047400e801ce139446a44d309a6034c06714ce019c033806418c80190032005f28be017632ec05c0cb8016e12dc05b80b7016262c405880b0096002c005800a6514c028c65180a30146028c05180a30146026544c80990132025864b0096012c024c6498093012602406480090011e1234446808d01181228445008a0112121c43b447508ea01d4038147000e001c0035186a00d401a8030286000ba317402e045c00b8017002b185600ac015422a80550096a12c0240c48009001200240048009000f941f003e007c00ec61d803b007600e061c0038007000d461a8035006a00c86190032006210bc417802f005c10b0416002c005610a441480290050109840ac401a0001 0xd1a33b2933a4923600334202322013a41234182321813b21435f84321013d13435f04341033d0b43b1a43a3a33e3b59ea349d8a59e9a49d0233c2159e9149b1133a312383059e88495e8334082320813a292340023200131f813c195b8285b1f0133f833d7b5b8205b3f033a2233d735bc0a5ba1a33e7b57d6a5bcfa41e723be6a39ce231c015bb0941e613be5939a8131a11238105b5e041e503be4839470313e8231e813a09233e0231e013a01233d8231d8131d0133d0339fa33e3d62e336ede263e2a39cb963e21399f12395863e18393c8231c8131c0133c0339ea33e0a39e01399e123df8393b8231b8131b013dea449d931db9299a9213b031da0292a8211a813b01435d8431a01319813bf95b8085b190135d053dbc5b8005b5c843afa53da45bbea5baf243de45bcf342dda57dd24fdca4ece242be15bae9439d131dc12bdb1299a1217f05b5c0433a831da82bd98292902118813ae1435b8431801317813d8244ad951d7949a89415b051d70494884117013ad1335a83316813160135a043aca43d8d62d6c63d626ed5a4eca963ac143d51299486359843d4829158131501359043aba43d3a4eab143d312958843d28291481314013bd969d11597e869d085913813bd15b7e05b13013bc95b7d85b12813bc14b7d04b12013bb95b7c85b118137c05b68853bb25bb6253d1d6fd0563cfc62cf362cea6ece262ca163ba95bb5953cd92999121940637b85b68053cd02925021110133a0239ca32cc144c693e9a9323983310821c48190a81158043aaa52c815ea8952cb1345785310021c40190a011c99677b06b0f821c581bc381909811c9b43570433903338833c825b7a85b3802356853c6c5b7a05b56043c5c53c4c5bc435bc3b43cbc5bcab5bca343aa2429c232c9157c894fc794ea8142c713fc613e9a1327885b55843378330f021c501bc301909011bdb43550433703336823bd351c1b49bbb41c114454851c0849480413603354043bcc52bfb5ebbb52bf1345385335841be8392a031bde72bd572bcc72bc37ebbb72ba17e93873bb03926831b8019ba23353033350233482352843b8343c2562c0463be363bab43b996eb914eb893e920635204334033b7819b6824b603925831b40193382351843b4343b5b43b514eb493e5104333033b381932833ae369b235978069b185932033adb5b7785b31833b03677686b31041af83baf03929831ae672add72ad37eaaa72a997ea897291073ac839a701906811ab839a601905811aab5b7605b30833a9a4b7584b30023a8b5b7505b2f8337485b67053a6834a735ba6353b2d6fb1563b0c62aeb63ac35bab353aa262a916ea8162a793e99132908637405b668532f033a58190501150843a0c69a445973869a385950043a2c677286b4f851a204ba184947841a0e72a047e9db729ca729b97e9a9728f8739f84998819028119e84997819018119dc5b7205b4f0439cc5b7185b4e8439bb4b7104b4e0339ac5b7085b4d8437005b658536f85b648539804498c5b97c53a4d6fa3563a14639f45b9e4539d3629c2629b16e9a1629994e991428f0636f05b640534d0439701901011901238fa332e9320e922960448883e2a8328582e0a82291943912534c9520e1228b85e48852950348502e0a02293a6b0d9228e8678682f8482e09822930249334393c534c1522e1428b05e480528804e2a04292824918449146b2d9428e0678984f8784e29842900548fd6b4b9528d8678c85f8a85e478528eb438e2438da338ca338ba5b8b15b8a92389a5388c5b8815b8794386c5385c5b8535b84b4395c5b94b5b943439225b90a438f2334b1422d1320d1228d0578c04f8a04e470428903f8703e290328602f8402e090227eb437824373a33731237e35182b497cb4177a51822497524172a3381844771437dc5280b5e7cb5276a53722418023970a317f8347ee727e5727dc727d37e7cb727b2737c2396fa316e87e6a82e7982479b437b4537635271b427aa5e752527a24e70a4279024770447867277d7276c737637275a7e7527274a4e6fa426e07e6b84e7305473e7272d737247271b727127e70a727025e6fa526d87e6c85e6ea336e1336d9236c9236b9436ab4383562814637f3637bb4378a63742436f2336d06e6c04e6b03e6a02e6902468a3964a316182e678346724e64a426284e660446502465a5e64a526385e639236294361b436834366a43642336304e6203e6102e50a335bb695fb59552695f259502335b35b54a5b4fa335db6753a6b4f2415d23b5ca394da315be725b5725ab7e57a735a2394c9724a87e488724482e06822592394382e058225824457c6b4eb425726756a4f5624e4da42542445567254d7253c735327e52a4e4c1724a07e480724684e2684251a4e4584e2584250e7f506734fd724f4724eb724e27e4da724b9724987e478724cb5b4c25b4ba334aa4b4a14b4992348b5b4825b47a33461344695b459534413444b5b43b536056f5ed635e4625c36359b5b58b5355a635225b512534d2334b1624906e470624503e250324302e0502232a433e46941c59372694125932243404673626b31a513fa4b3f2492fa413e6723dc7e3b37239a733d2492e9722c87e2a8722482e028223c2492382e018223b45b35a5b312433a25439d6b30b523926738a5f3825e2fa5236a54376723657335c723527e34a5e2e1722c07e2a0722885e2685233a5e2785e2585232e7f3267331d723147230b723027e2fa722d9722b87e298722ec5b2e25b2da432cb4b2c14b2b9332ac5b2a25b29a43281442895b279532602426a5b25a532414424c5b23c534256f40d633ec633cc5b3bc533ab6237a633425b332532f2432d1622b06e290622704e250422302e01022143431e46921c59183692135913b43204671736b133511fb4b1f34911b411e6721dc7e1ab731d34910a720e9720c87e0a8720483e028321c3490383e018321b3541ad6b12c521a36719b5f1935e11b5217b54186721757316b7e1635e102720e1720c07e0a0720885e068521535e0785e058521467f13e731357212c721237e11b720fa720d9720b87e0987210c5b1035b0fb430ec5b0e35b0db430cb4b0c24b0ba330ac5b0a35b09b430824408a5b07a530603406b5b05b530424404c5b03c530204402c5b01c532256f20d631ec631cc5b1bc5318b6315b5b14b53113430f2620d1620b06e090620704e050420303e01032eac5fe8453e4353e134bdf343d9253d424bd2243cca33c2953b714bb3143a513396923838536984b608434283322823008130003f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF fullMask g_34 bds_34 (dagRefF 470 (dagTraceF fullMask rootStock 11 f_34) l_34 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_6 : treeBlockF 192 224 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_7 : treeBlockF 224 256 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_8 : treeBlockF 256 288 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_9 : treeBlockF 288 320 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_10 : treeBlockF 320 352 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_11 : treeBlockF 352 384 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_12 : treeBlockF 384 416 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_13 : treeBlockF 416 448 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_14 : treeBlockF 448 470 (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nj_34_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_1 (fun _ h1 h2 => treeBlockF_at nb_34_2 h1 h2)
theorem nj_34_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_2 (fun _ h1 h2 => treeBlockF_at nb_34_3 h1 h2)
theorem nj_34_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_3 (fun _ h1 h2 => treeBlockF_at nb_34_4 h1 h2)
theorem nj_34_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_4 (fun _ h1 h2 => treeBlockF_at nb_34_5 h1 h2)
theorem nj_34_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_5 (fun _ h1 h2 => treeBlockF_at nb_34_6 h1 h2)
theorem nj_34_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_6 (fun _ h1 h2 => treeBlockF_at nb_34_7 h1 h2)
theorem nj_34_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_7 (fun _ h1 h2 => treeBlockF_at nb_34_8 h1 h2)
theorem nj_34_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_8 (fun _ h1 h2 => treeBlockF_at nb_34_9 h1 h2)
theorem nj_34_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_9 (fun _ h1 h2 => treeBlockF_at nb_34_10 h1 h2)
theorem nj_34_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_10 (fun _ h1 h2 => treeBlockF_at nb_34_11 h1 h2)
theorem nj_34_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_11 (fun _ h1 h2 => treeBlockF_at nb_34_12 h1 h2)
theorem nj_34_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_12 (fun _ h1 h2 => treeBlockF_at nb_34_13 h1 h2)
theorem nj_34_14 : ∀ i, 0 ≤ i → i < 470 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := block_join nj_34_13 (fun _ h1 h2 => treeBlockF_at nb_34_14 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 470 → (dagCheckNodeF fullMask g_34 bds_34 470 (dagTraceF fullMask rootStock 11 f_34) l_34) i = true := nj_34_14
theorem lb_34 : LowerBin fullMask rootStock g_34 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def wg : List Gate := [⟨GateOp.and, [3, 2]⟩, ⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [10, 1]⟩, ⟨GateOp.and, [11, 0]⟩, ⟨GateOp.and, [8, 1]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.and, [9, 1]⟩, ⟨GateOp.or, [7, 15]⟩, ⟨GateOp.and, [16, 14]⟩, ⟨GateOp.or, [17, 12]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4277071594 * 2 ^ 32 + 4008372904)) (13 - 1) := by
  rw [show canon fullMask (4277071594 * 2 ^ 32 + 4008372904) = g_34 by decide]
  exact lb_34

end PEqualNP.Outside.L_meta_46868

theorem PEqualNP.Outside.L_meta_46868 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_46868.table2_from_lowerBin (4277071594 * 2 ^ 32 + 4008372904) 13 PEqualNP.Outside.L_meta_46868.root_lb PEqualNP.Outside.L_meta_46868.wg 18 rfl PEqualNP.Outside.L_meta_46868.wfits PEqualNP.Outside.L_meta_46868.weval
