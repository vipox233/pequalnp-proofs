import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49487

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

theorem certBlock {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ i, lo ≤ i → i < hi → f i = true :=
  fun _ hi₁ hi₂ => treeBlockF_at h hi₁ hi₂

theorem joinChecks {lo mid hi : Nat} {f : Nat → Bool}
    (left : ∀ i, lo ≤ i → i < mid → f i = true)
    (right : ∀ i, mid ≤ i → i < hi → f i = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := by
  intro i h₁ h₂
  by_cases hl : i < mid
  · exact left i h₁ hl
  · exact right i (Nat.le_of_not_gt hl) h₂

def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_1 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
def m_1 : Nat := 0x808080808080808
def s_1 : List Nat := [0x8000800080008, 0x80800000808, 0x8080808]
def g_1 : Nat := 0x800080808
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by
  intro b hb
  simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_1] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsF m_1 g_1 bds_1 (dagRefF 1 (dagTraceF m_1 s_1 3 f_1) l_1 0) s_1 3 = true := by decide +kernel
def node_1 : Nat → Bool := dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1_0 : treeBlockF 0 1 node_1 = true := by decide +kernel
theorem nc_1 : ∀ j, 0 ≤ j → j < 1 → node_1 j = true :=
  (certBlock nb_1_0)
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0x2020202020202020
def s_2 : List Nat := [0x20002000200020, 0x202000002020, 0x20202020]
def g_2 : Nat := 0x2000202020
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by
  intro b hb
  simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_2] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsF m_2 g_2 bds_2 (dagRefF 1 (dagTraceF m_2 s_2 3 f_1) l_1 0) s_2 3 = true := by decide +kernel
def node_2 : Nat → Bool := dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2_0 : treeBlockF 0 1 node_2 = true := by decide +kernel
theorem nc_2 : ∀ j, 0 ≤ j → j < 1 → node_2 j = true :=
  (certBlock nb_2_0)
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0x4040404040404040
def s_3 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_3 : Nat := 0x4000404040
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by
  intro b hb
  simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_3] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsF m_3 g_3 bds_3 (dagRefF 1 (dagTraceF m_3 s_3 3 f_1) l_1 0) s_3 3 = true := by decide +kernel
def node_3 : Nat → Bool := dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_3_0 : treeBlockF 0 1 node_3 = true := by decide +kernel
theorem nc_3 : ∀ j, 0 ≤ j → j < 1 → node_3 j = true :=
  (certBlock nb_3_0)
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_3 sub_3 gl_3 rc_3 nc_3

def m_7 : Nat := 0x88008800880088
def s_7 : List Nat := [0x8000800080008, 0x8800000088, 0x880088]
def g_7 : Nat := 0x800080088
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by
  intro b hb
  simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_7] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsF m_7 g_7 bds_7 (dagRefF 1 (dagTraceF m_7 s_7 3 f_1) l_1 0) s_7 3 = true := by decide +kernel
def node_7 : Nat → Bool := dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_7_0 : treeBlockF 0 1 node_7 = true := by decide +kernel
theorem nc_7 : ∀ j, 0 ≤ j → j < 1 → node_7 j = true :=
  (certBlock nb_7_0)
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_7 sub_7 gl_7 rc_7 nc_7

def m_11 : Nat := 0x888800008888
def s_11 : List Nat := [0x80800000808, 0x8800000088, 0x8888]
def g_11 : Nat := 0x800000888
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by
  intro b hb
  simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_11] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 1 (dagTraceF m_11 s_11 3 f_1) l_1 0) s_11 3 = true := by decide +kernel
def node_11 : Nat → Bool := dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 1 node_11 = true := by decide +kernel
theorem nc_11 : ∀ j, 0 ≤ j → j < 1 → node_11 j = true :=
  (certBlock nb_11_0)
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_16 : Nat := 0x88888888
def s_16 : List Nat := [0x8080808, 0x880088, 0x8888]
def g_16 : Nat := 0x80888
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_16 : KnownBin bds_16 := by
  intro b hb
  simp [bds_16] at hb
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_16] at hb
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_16] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 1 (dagTraceF m_16 s_16 3 f_1) l_1 0) s_16 3 = true := by decide +kernel
def node_16 : Nat → Bool := dagCheckNodeF m_16 g_16 bds_16 1 (dagTraceF m_16 s_16 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_16_0 : treeBlockF 0 1 node_16 = true := by decide +kernel
theorem nc_16 : ∀ j, 0 ≤ j → j < 1 → node_16 j = true :=
  (certBlock nb_16_0)
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_22 : Nat := 0xa000a000a000a0
def s_22 : List Nat := [0x20002000200020, 0xa0000000a0, 0xa000a0]
def g_22 : Nat := 0x20002000a0
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by
  intro b hb
  simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_22] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 1 (dagTraceF m_22 s_22 3 f_1) l_1 0) s_22 3 = true := by decide +kernel
def node_22 : Nat → Bool := dagCheckNodeF m_22 g_22 bds_22 1 (dagTraceF m_22 s_22 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 1 node_22 = true := by decide +kernel
theorem nc_22 : ∀ j, 0 ≤ j → j < 1 → node_22 j = true :=
  (certBlock nb_22_0)
theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_26 : Nat := 0xa0a00000a0a0
def s_26 : List Nat := [0x202000002020, 0xa0000000a0, 0xa0a0]
def g_26 : Nat := 0x20000020a0
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_26 : KnownBin bds_26 := by
  intro b hb
  simp [bds_26] at hb
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_26] at hb
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_26] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 1 (dagTraceF m_26 s_26 3 f_1) l_1 0) s_26 3 = true := by decide +kernel
def node_26 : Nat → Bool := dagCheckNodeF m_26 g_26 bds_26 1 (dagTraceF m_26 s_26 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 1 node_26 = true := by decide +kernel
theorem nc_26 : ∀ j, 0 ≤ j → j < 1 → node_26 j = true :=
  (certBlock nb_26_0)
theorem lb_26 : LowerBin m_26 s_26 g_26 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_31 : Nat := 0xa0a0a0a0
def s_31 : List Nat := [0x20202020, 0xa000a0, 0xa0a0]
def g_31 : Nat := 0x2020a0
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_31 : KnownBin bds_31 := by
  intro b hb
  simp [bds_31] at hb
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_31] at hb
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_31] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 1 (dagTraceF m_31 s_31 3 f_1) l_1 0) s_31 3 = true := by decide +kernel
def node_31 : Nat → Bool := dagCheckNodeF m_31 g_31 bds_31 1 (dagTraceF m_31 s_31 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 1 node_31 = true := by decide +kernel
theorem nc_31 : ∀ j, 0 ≤ j → j < 1 → node_31 j = true :=
  (certBlock nb_31_0)
theorem lb_31 : LowerBin m_31 s_31 g_31 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_39 : Nat := 0xaa000000aa0000
def s_39 : List Nat := [0x22000000220000, 0xa0000000a0000, 0xaa0000]
def g_39 : Nat := 0x20000002a0000
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_39 : KnownBin bds_39 := by
  intro b hb
  simp [bds_39] at hb
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_39] at hb
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_39] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 1 (dagTraceF m_39 s_39 3 f_1) l_1 0) s_39 3 = true := by decide +kernel
def node_39 : Nat → Bool := dagCheckNodeF m_39 g_39 bds_39 1 (dagTraceF m_39 s_39 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 1 node_39 = true := by decide +kernel
theorem nc_39 : ∀ j, 0 ≤ j → j < 1 → node_39 j = true :=
  (certBlock nb_39_0)
theorem lb_39 : LowerBin m_39 s_39 g_39 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_44 : Nat := 0xaa00aa00000000
def s_44 : List Nat := [0x22002200000000, 0xa000a00000000, 0xaa00000000]
def g_44 : Nat := 0x2002a00000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_44 : KnownBin bds_44 := by
  intro b hb
  simp [bds_44] at hb
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_44] at hb
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_44] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 1 (dagTraceF m_44 s_44 3 f_1) l_1 0) s_44 3 = true := by decide +kernel
def node_44 : Nat → Bool := dagCheckNodeF m_44 g_44 bds_44 1 (dagTraceF m_44 s_44 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 1 node_44 = true := by decide +kernel
theorem nc_44 : ∀ j, 0 ≤ j → j < 1 → node_44 j = true :=
  (certBlock nb_44_0)
theorem lb_44 : LowerBin m_44 s_44 g_44 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_53 : Nat := 0xc000c000c000c0
def s_53 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_53 : Nat := 0x40004000c0
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_53 : KnownBin bds_53 := by
  intro b hb
  simp [bds_53] at hb
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_53] at hb
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_53] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsF m_53 g_53 bds_53 (dagRefF 1 (dagTraceF m_53 s_53 3 f_1) l_1 0) s_53 3 = true := by decide +kernel
def node_53 : Nat → Bool := dagCheckNodeF m_53 g_53 bds_53 1 (dagTraceF m_53 s_53 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 1 node_53 = true := by decide +kernel
theorem nc_53 : ∀ j, 0 ≤ j → j < 1 → node_53 j = true :=
  (certBlock nb_53_0)
theorem lb_53 : LowerBin m_53 s_53 g_53 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_53 sub_53 gl_53 rc_53 nc_53

def m_61 : Nat := 0xc0c00000c0c0
def s_61 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_61 : Nat := 0x40000040c0
def bds_61 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_61 : KnownBin bds_61 := by
  intro b hb
  simp [bds_61] at hb
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_61] at hb
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_61] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsF m_61 g_61 bds_61 (dagRefF 1 (dagTraceF m_61 s_61 3 f_1) l_1 0) s_61 3 = true := by decide +kernel
def node_61 : Nat → Bool := dagCheckNodeF m_61 g_61 bds_61 1 (dagTraceF m_61 s_61 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_61_0 : treeBlockF 0 1 node_61 = true := by decide +kernel
theorem nc_61 : ∀ j, 0 ≤ j → j < 1 → node_61 j = true :=
  (certBlock nb_61_0)
theorem lb_61 : LowerBin m_61 s_61 g_61 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_61 sub_61 gl_61 rc_61 nc_61

def m_68 : Nat := 0xc0c0c0c0
def s_68 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_68 : Nat := 0x4040c0
def bds_68 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_68 : KnownBin bds_68 := by
  intro b hb
  simp [bds_68] at hb
theorem sub_68 : ∀ b ∈ bds_68, m_68 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_68] at hb
theorem gl_68 : ∀ b ∈ bds_68, canon b.1 g_68 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_68] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsF m_68 g_68 bds_68 (dagRefF 1 (dagTraceF m_68 s_68 3 f_1) l_1 0) s_68 3 = true := by decide +kernel
def node_68 : Nat → Bool := dagCheckNodeF m_68 g_68 bds_68 1 (dagTraceF m_68 s_68 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_68_0 : treeBlockF 0 1 node_68 = true := by decide +kernel
theorem nc_68 : ∀ j, 0 ≤ j → j < 1 → node_68 j = true :=
  (certBlock nb_68_0)
theorem lb_68 : LowerBin m_68 s_68 g_68 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_68 sub_68 gl_68 rc_68 nc_68

def m_73 : Nat := 0xcc000000cc00
def s_73 : List Nat := [0x440000004400, 0xc0000000c00, 0xcc00]
def g_73 : Nat := 0x40000004c00
def bds_73 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_73 : KnownBin bds_73 := by
  intro b hb
  simp [bds_73] at hb
theorem sub_73 : ∀ b ∈ bds_73, m_73 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_73] at hb
theorem gl_73 : ∀ b ∈ bds_73, canon b.1 g_73 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_73] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsF m_73 g_73 bds_73 (dagRefF 1 (dagTraceF m_73 s_73 3 f_1) l_1 0) s_73 3 = true := by decide +kernel
def node_73 : Nat → Bool := dagCheckNodeF m_73 g_73 bds_73 1 (dagTraceF m_73 s_73 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_73_0 : treeBlockF 0 1 node_73 = true := by decide +kernel
theorem nc_73 : ∀ j, 0 ≤ j → j < 1 → node_73 j = true :=
  (certBlock nb_73_0)
theorem lb_73 : LowerBin m_73 s_73 g_73 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_73 sub_73 gl_73 rc_73 nc_73

def m_75 : Nat := 0xcc000000cc0000
def s_75 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_75 : Nat := 0x40000004c0000
def bds_75 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_75 : KnownBin bds_75 := by
  intro b hb
  simp [bds_75] at hb
theorem sub_75 : ∀ b ∈ bds_75, m_75 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_75] at hb
theorem gl_75 : ∀ b ∈ bds_75, canon b.1 g_75 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_75] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_75 : dagCheckRootsF m_75 g_75 bds_75 (dagRefF 1 (dagTraceF m_75 s_75 3 f_1) l_1 0) s_75 3 = true := by decide +kernel
def node_75 : Nat → Bool := dagCheckNodeF m_75 g_75 bds_75 1 (dagTraceF m_75 s_75 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_75_0 : treeBlockF 0 1 node_75 = true := by decide +kernel
theorem nc_75 : ∀ j, 0 ≤ j → j < 1 → node_75 j = true :=
  (certBlock nb_75_0)
theorem lb_75 : LowerBin m_75 s_75 g_75 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_75 sub_75 gl_75 rc_75 nc_75

def m_77 : Nat := 0xcc00cc00
def s_77 : List Nat := [0x44004400, 0xc000c00, 0xcc00]
def g_77 : Nat := 0x4004c00
def bds_77 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_77 : KnownBin bds_77 := by
  intro b hb
  simp [bds_77] at hb
theorem sub_77 : ∀ b ∈ bds_77, m_77 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_77] at hb
theorem gl_77 : ∀ b ∈ bds_77, canon b.1 g_77 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_77] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_77 : dagCheckRootsF m_77 g_77 bds_77 (dagRefF 1 (dagTraceF m_77 s_77 3 f_1) l_1 0) s_77 3 = true := by decide +kernel
def node_77 : Nat → Bool := dagCheckNodeF m_77 g_77 bds_77 1 (dagTraceF m_77 s_77 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_77_0 : treeBlockF 0 1 node_77 = true := by decide +kernel
theorem nc_77 : ∀ j, 0 ≤ j → j < 1 → node_77 j = true :=
  (certBlock nb_77_0)
theorem lb_77 : LowerBin m_77 s_77 g_77 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_77 sub_77 gl_77 rc_77 nc_77

def m_79 : Nat := 0xcc00cc00000000
def s_79 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_79 : Nat := 0x4004c00000000
def bds_79 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_79 : KnownBin bds_79 := by
  intro b hb
  simp [bds_79] at hb
theorem sub_79 : ∀ b ∈ bds_79, m_79 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_79] at hb
theorem gl_79 : ∀ b ∈ bds_79, canon b.1 g_79 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_79] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_79 : dagCheckRootsF m_79 g_79 bds_79 (dagRefF 1 (dagTraceF m_79 s_79 3 f_1) l_1 0) s_79 3 = true := by decide +kernel
def node_79 : Nat → Bool := dagCheckNodeF m_79 g_79 bds_79 1 (dagTraceF m_79 s_79 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_79_0 : treeBlockF 0 1 node_79 = true := by decide +kernel
theorem nc_79 : ∀ j, 0 ≤ j → j < 1 → node_79 j = true :=
  (certBlock nb_79_0)
theorem lb_79 : LowerBin m_79 s_79 g_79 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_79 sub_79 gl_79 rc_79 nc_79

def m_81 : Nat := 0xcccc0000
def s_81 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_81 : Nat := 0x44c0000
def bds_81 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_81 : KnownBin bds_81 := by
  intro b hb
  simp [bds_81] at hb
theorem sub_81 : ∀ b ∈ bds_81, m_81 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_81] at hb
theorem gl_81 : ∀ b ∈ bds_81, canon b.1 g_81 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_81] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_81 : dagCheckRootsF m_81 g_81 bds_81 (dagRefF 1 (dagTraceF m_81 s_81 3 f_1) l_1 0) s_81 3 = true := by decide +kernel
def node_81 : Nat → Bool := dagCheckNodeF m_81 g_81 bds_81 1 (dagTraceF m_81 s_81 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_81_0 : treeBlockF 0 1 node_81 = true := by decide +kernel
theorem nc_81 : ∀ j, 0 ≤ j → j < 1 → node_81 j = true :=
  (certBlock nb_81_0)
theorem lb_81 : LowerBin m_81 s_81 g_81 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_81 sub_81 gl_81 rc_81 nc_81

def m_82 : Nat := 0xcccc00000000
def s_82 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_82 : Nat := 0x44c00000000
def bds_82 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_82 : KnownBin bds_82 := by
  intro b hb
  simp [bds_82] at hb
theorem sub_82 : ∀ b ∈ bds_82, m_82 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_82] at hb
theorem gl_82 : ∀ b ∈ bds_82, canon b.1 g_82 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_82] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_82 : dagCheckRootsF m_82 g_82 bds_82 (dagRefF 1 (dagTraceF m_82 s_82 3 f_1) l_1 0) s_82 3 = true := by decide +kernel
def node_82 : Nat → Bool := dagCheckNodeF m_82 g_82 bds_82 1 (dagTraceF m_82 s_82 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_82_0 : treeBlockF 0 1 node_82 = true := by decide +kernel
theorem nc_82 : ∀ j, 0 ≤ j → j < 1 → node_82 j = true :=
  (certBlock nb_82_0)
theorem lb_82 : LowerBin m_82 s_82 g_82 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_82 sub_82 gl_82 rc_82 nc_82

def m_85 : Nat := 0xf0000000f000
def s_85 : List Nat := [0x500000005000, 0x300000003000, 0xf000]
def g_85 : Nat := 0x100000007000
def bds_85 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_85 : KnownBin bds_85 := by
  intro b hb
  simp [bds_85] at hb
theorem sub_85 : ∀ b ∈ bds_85, m_85 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_85] at hb
theorem gl_85 : ∀ b ∈ bds_85, canon b.1 g_85 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_85] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_85 : dagCheckRootsF m_85 g_85 bds_85 (dagRefF 1 (dagTraceF m_85 s_85 3 f_1) l_1 0) s_85 3 = true := by decide +kernel
def node_85 : Nat → Bool := dagCheckNodeF m_85 g_85 bds_85 1 (dagTraceF m_85 s_85 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_85_0 : treeBlockF 0 1 node_85 = true := by decide +kernel
theorem nc_85 : ∀ j, 0 ≤ j → j < 1 → node_85 j = true :=
  (certBlock nb_85_0)
theorem lb_85 : LowerBin m_85 s_85 g_85 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_85 sub_85 gl_85 rc_85 nc_85

def m_87 : Nat := 0xf0000000f00000
def s_87 : List Nat := [0x50000000500000, 0x30000000300000, 0xf00000]
def g_87 : Nat := 0x10000000700000
def bds_87 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_87 : KnownBin bds_87 := by
  intro b hb
  simp [bds_87] at hb
theorem sub_87 : ∀ b ∈ bds_87, m_87 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_87] at hb
theorem gl_87 : ∀ b ∈ bds_87, canon b.1 g_87 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_87] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_87 : dagCheckRootsF m_87 g_87 bds_87 (dagRefF 1 (dagTraceF m_87 s_87 3 f_1) l_1 0) s_87 3 = true := by decide +kernel
def node_87 : Nat → Bool := dagCheckNodeF m_87 g_87 bds_87 1 (dagTraceF m_87 s_87 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_87_0 : treeBlockF 0 1 node_87 = true := by decide +kernel
theorem nc_87 : ∀ j, 0 ≤ j → j < 1 → node_87 j = true :=
  (certBlock nb_87_0)
theorem lb_87 : LowerBin m_87 s_87 g_87 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_87 sub_87 gl_87 rc_87 nc_87

def m_89 : Nat := 0xf000f000
def s_89 : List Nat := [0x50005000, 0x30003000, 0xf000]
def g_89 : Nat := 0x10007000
def bds_89 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_89 : KnownBin bds_89 := by
  intro b hb
  simp [bds_89] at hb
theorem sub_89 : ∀ b ∈ bds_89, m_89 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_89] at hb
theorem gl_89 : ∀ b ∈ bds_89, canon b.1 g_89 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_89] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_89 : dagCheckRootsF m_89 g_89 bds_89 (dagRefF 1 (dagTraceF m_89 s_89 3 f_1) l_1 0) s_89 3 = true := by decide +kernel
def node_89 : Nat → Bool := dagCheckNodeF m_89 g_89 bds_89 1 (dagTraceF m_89 s_89 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_89_0 : treeBlockF 0 1 node_89 = true := by decide +kernel
theorem nc_89 : ∀ j, 0 ≤ j → j < 1 → node_89 j = true :=
  (certBlock nb_89_0)
theorem lb_89 : LowerBin m_89 s_89 g_89 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_89 sub_89 gl_89 rc_89 nc_89

def m_91 : Nat := 0xf000f000000000
def s_91 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_91 : Nat := 0x10007000000000
def bds_91 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_91 : KnownBin bds_91 := by
  intro b hb
  simp [bds_91] at hb
theorem sub_91 : ∀ b ∈ bds_91, m_91 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_91] at hb
theorem gl_91 : ∀ b ∈ bds_91, canon b.1 g_91 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_91] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_91 : dagCheckRootsF m_91 g_91 bds_91 (dagRefF 1 (dagTraceF m_91 s_91 3 f_1) l_1 0) s_91 3 = true := by decide +kernel
def node_91 : Nat → Bool := dagCheckNodeF m_91 g_91 bds_91 1 (dagTraceF m_91 s_91 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_91_0 : treeBlockF 0 1 node_91 = true := by decide +kernel
theorem nc_91 : ∀ j, 0 ≤ j → j < 1 → node_91 j = true :=
  (certBlock nb_91_0)
theorem lb_91 : LowerBin m_91 s_91 g_91 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_91 sub_91 gl_91 rc_91 nc_91

def m_93 : Nat := 0xf0f00000
def s_93 : List Nat := [0x50500000, 0x30300000, 0xf00000]
def g_93 : Nat := 0x10700000
def bds_93 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_93 : KnownBin bds_93 := by
  intro b hb
  simp [bds_93] at hb
theorem sub_93 : ∀ b ∈ bds_93, m_93 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_93] at hb
theorem gl_93 : ∀ b ∈ bds_93, canon b.1 g_93 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_93] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_93 : dagCheckRootsF m_93 g_93 bds_93 (dagRefF 1 (dagTraceF m_93 s_93 3 f_1) l_1 0) s_93 3 = true := by decide +kernel
def node_93 : Nat → Bool := dagCheckNodeF m_93 g_93 bds_93 1 (dagTraceF m_93 s_93 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_93_0 : treeBlockF 0 1 node_93 = true := by decide +kernel
theorem nc_93 : ∀ j, 0 ≤ j → j < 1 → node_93 j = true :=
  (certBlock nb_93_0)
theorem lb_93 : LowerBin m_93 s_93 g_93 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_93 sub_93 gl_93 rc_93 nc_93

def m_94 : Nat := 0xf0f000000000
def s_94 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_94 : Nat := 0x107000000000
def bds_94 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_94 : KnownBin bds_94 := by
  intro b hb
  simp [bds_94] at hb
theorem sub_94 : ∀ b ∈ bds_94, m_94 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_94] at hb
theorem gl_94 : ∀ b ∈ bds_94, canon b.1 g_94 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_94] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_94 : dagCheckRootsF m_94 g_94 bds_94 (dagRefF 1 (dagTraceF m_94 s_94 3 f_1) l_1 0) s_94 3 = true := by decide +kernel
def node_94 : Nat → Bool := dagCheckNodeF m_94 g_94 bds_94 1 (dagTraceF m_94 s_94 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_94_0 : treeBlockF 0 1 node_94 = true := by decide +kernel
theorem nc_94 : ∀ j, 0 ≤ j → j < 1 → node_94 j = true :=
  (certBlock nb_94_0)
theorem lb_94 : LowerBin m_94 s_94 g_94 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_94 sub_94 gl_94 rc_94 nc_94

def m_101 : Nat := 0xff000000000000
def s_101 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_101 : Nat := 0x17000000000000
def bds_101 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_101 : KnownBin bds_101 := by
  intro b hb
  simp [bds_101] at hb
theorem sub_101 : ∀ b ∈ bds_101, m_101 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_101] at hb
theorem gl_101 : ∀ b ∈ bds_101, canon b.1 g_101 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_101] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_101 : dagCheckRootsF m_101 g_101 bds_101 (dagRefF 1 (dagTraceF m_101 s_101 3 f_1) l_1 0) s_101 3 = true := by decide +kernel
def node_101 : Nat → Bool := dagCheckNodeF m_101 g_101 bds_101 1 (dagTraceF m_101 s_101 3 f_1) l_1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_101_0 : treeBlockF 0 1 node_101 = true := by decide +kernel
theorem nc_101 : ∀ j, 0 ≤ j → j < 1 → node_101 j = true :=
  (certBlock nb_101_0)
theorem lb_101 : LowerBin m_101 s_101 g_101 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_101 sub_101 gl_101 rc_101 nc_101

def f_104 : Nat → Nat × Nat := fun _ => (0, 0)
def l_104 : Nat → Nat → Option Nat := fun _ _ => none
def m_104 : Nat := 0x4444444444444444
def s_104 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_104 : Nat := 0x404044404444444
def bds_104 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_104 : KnownBin bds_104 := by
  intro b hb
  simp only [bds_104, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_3
theorem sub_104 : ∀ b ∈ bds_104, m_104 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_104, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_104 : ∀ b ∈ bds_104, canon b.1 g_104 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_104, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_104 : dagCheckRootsF m_104 g_104 bds_104 (dagRefF 0 (dagTraceF m_104 s_104 4 f_104) l_104 0) s_104 4 = true := by decide +kernel
def node_104 : Nat → Bool := dagCheckNodeF m_104 g_104 bds_104 0 (dagTraceF m_104 s_104 4 f_104) l_104
theorem nc_104 : ∀ j, 0 ≤ j → j < 0 → node_104 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_104 : LowerBin m_104 s_104 g_104 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_104 sub_104 gl_104 rc_104 nc_104

def f_105 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_105 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
def m_105 : Nat := 0x8888888888888888
def s_105 : List Nat := [0x808080808080808, 0x88008800880088, 0x888800008888, 0x88888888]
def g_105 : Nat := 0x800080888
def bds_105 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_16, s_16, 4, g_16), (m_1, s_1, 4, g_1), (m_7, s_7, 4, g_7)]
theorem kn_105 : KnownBin bds_105 := by
  intro b hb
  simp only [bds_105, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_16
  · exact lb_1
  · exact lb_7
theorem sub_105 : ∀ b ∈ bds_105, m_105 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_105, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_105 : ∀ b ∈ bds_105, canon b.1 g_105 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_105, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_105 : dagCheckRootsF m_105 g_105 bds_105 (dagRefF 43 (dagTraceF m_105 s_105 6 f_105) l_105 0) s_105 6 = true := by decide +kernel
def node_105 : Nat → Bool := dagCheckNodeF m_105 g_105 bds_105 43 (dagTraceF m_105 s_105 6 f_105) l_105
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_105_0 : treeBlockF 0 32 node_105 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_105_1 : treeBlockF 32 43 node_105 = true := by decide +kernel
theorem nc_105 : ∀ j, 0 ≤ j → j < 43 → node_105 j = true :=
  (joinChecks (certBlock nb_105_0) (certBlock nb_105_1))
theorem lb_105 : LowerBin m_105 s_105 g_105 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_105 sub_105 gl_105 rc_105 nc_105

def f_107 : Nat → Nat × Nat := fun _ => (0, 0)
def l_107 : Nat → Nat → Option Nat := fun _ _ => none
def m_107 : Nat := 0x5050505050505050
def s_107 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_107 : Nat := 0x1010105010505050
def bds_107 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_107 : KnownBin bds_107 := by
  intro b hb
  simp only [bds_107, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_3
theorem sub_107 : ∀ b ∈ bds_107, m_107 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_107, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_107 : ∀ b ∈ bds_107, canon b.1 g_107 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_107, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_107 : dagCheckRootsF m_107 g_107 bds_107 (dagRefF 0 (dagTraceF m_107 s_107 4 f_107) l_107 0) s_107 4 = true := by decide +kernel
def node_107 : Nat → Bool := dagCheckNodeF m_107 g_107 bds_107 0 (dagTraceF m_107 s_107 4 f_107) l_107
theorem nc_107 : ∀ j, 0 ≤ j → j < 0 → node_107 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_107 : LowerBin m_107 s_107 g_107 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_107 sub_107 gl_107 rc_107 nc_107

def m_108 : Nat := 0xa0a0a0a0a0a0a0a0
def s_108 : List Nat := [0x2020202020202020, 0xa000a000a000a0, 0xa0a00000a0a0, 0xa0a0a0a0]
def g_108 : Nat := 0x20002020a0
def bds_108 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 4, g_26), (m_31, s_31, 4, g_31), (m_2, s_2, 4, g_2), (m_22, s_22, 4, g_22)]
theorem kn_108 : KnownBin bds_108 := by
  intro b hb
  simp only [bds_108, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_31
  · exact lb_2
  · exact lb_22
theorem sub_108 : ∀ b ∈ bds_108, m_108 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_108, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_108 : ∀ b ∈ bds_108, canon b.1 g_108 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_108, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_108 : dagCheckRootsF m_108 g_108 bds_108 (dagRefF 43 (dagTraceF m_108 s_108 6 f_105) l_105 0) s_108 6 = true := by decide +kernel
def node_108 : Nat → Bool := dagCheckNodeF m_108 g_108 bds_108 43 (dagTraceF m_108 s_108 6 f_105) l_105
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_108_0 : treeBlockF 0 32 node_108 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_108_1 : treeBlockF 32 43 node_108 = true := by decide +kernel
theorem nc_108 : ∀ j, 0 ≤ j → j < 43 → node_108 j = true :=
  (joinChecks (certBlock nb_108_0) (certBlock nb_108_1))
theorem lb_108 : LowerBin m_108 s_108 g_108 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_108 sub_108 gl_108 rc_108 nc_108

def f_110 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_110 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
def m_110 : Nat := 0xaa00aa00aa00aa
def s_110 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_110 : Nat := 0x2002a002a00aa
def bds_110 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 4, g_39), (m_44, s_44, 4, g_44), (m_22, s_22, 4, g_22), (m_7, s_7, 4, g_7)]
theorem kn_110 : KnownBin bds_110 := by
  intro b hb
  simp only [bds_110, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_39
  · exact lb_44
  · exact lb_22
  · exact lb_7
theorem sub_110 : ∀ b ∈ bds_110, m_110 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_110, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_110 : ∀ b ∈ bds_110, canon b.1 g_110 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_110, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_110 : dagCheckRootsF m_110 g_110 bds_110 (dagRefF 43 (dagTraceF m_110 s_110 6 f_110) l_110 0) s_110 6 = true := by decide +kernel
def node_110 : Nat → Bool := dagCheckNodeF m_110 g_110 bds_110 43 (dagTraceF m_110 s_110 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_110_0 : treeBlockF 0 32 node_110 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_110_1 : treeBlockF 32 43 node_110 = true := by decide +kernel
theorem nc_110 : ∀ j, 0 ≤ j → j < 43 → node_110 j = true :=
  (joinChecks (certBlock nb_110_0) (certBlock nb_110_1))
theorem lb_110 : LowerBin m_110 s_110 g_110 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_110 sub_110 gl_110 rc_110 nc_110

def f_114 : Nat → Nat × Nat := fun _ => (0, 0)
def l_114 : Nat → Nat → Option Nat := fun _ _ => none
def m_114 : Nat := 0xaaaa0000aaaa
def s_114 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_114 : Nat := 0x2a00002aaa
def bds_114 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_114 : KnownBin bds_114 := by
  intro b hb
  simp only [bds_114, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_11
theorem sub_114 : ∀ b ∈ bds_114, m_114 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_114, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_114 : ∀ b ∈ bds_114, canon b.1 g_114 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_114, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_114 : dagCheckRootsF m_114 g_114 bds_114 (dagRefF 0 (dagTraceF m_114 s_114 4 f_114) l_114 0) s_114 4 = true := by decide +kernel
def node_114 : Nat → Bool := dagCheckNodeF m_114 g_114 bds_114 0 (dagTraceF m_114 s_114 4 f_114) l_114
theorem nc_114 : ∀ j, 0 ≤ j → j < 0 → node_114 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_114 : LowerBin m_114 s_114 g_114 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_114 sub_114 gl_114 rc_114 nc_114

def f_116 : Nat → Nat × Nat := fun _ => (0, 0)
def l_116 : Nat → Nat → Option Nat := fun _ _ => none
def m_116 : Nat := 0xaaaa0000aaaa0000
def s_116 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_116 : Nat := 0x20000002a0000
def bds_116 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 4, g_39)]
theorem kn_116 : KnownBin bds_116 := by
  intro b hb
  simp only [bds_116, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_39
theorem sub_116 : ∀ b ∈ bds_116, m_116 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_116, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_116 : ∀ b ∈ bds_116, canon b.1 g_116 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_116, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_116 : dagCheckRootsF m_116 g_116 bds_116 (dagRefF 0 (dagTraceF m_116 s_116 4 f_116) l_116 0) s_116 4 = true := by decide +kernel
def node_116 : Nat → Bool := dagCheckNodeF m_116 g_116 bds_116 0 (dagTraceF m_116 s_116 4 f_116) l_116
theorem nc_116 : ∀ j, 0 ≤ j → j < 0 → node_116 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_116 : LowerBin m_116 s_116 g_116 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_116 sub_116 gl_116 rc_116 nc_116

def f_118 : Nat → Nat × Nat := fun _ => (0, 0)
def l_118 : Nat → Nat → Option Nat := fun _ _ => none
def m_118 : Nat := 0xaaaaaaaa
def s_118 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_118 : Nat := 0x2a2aaa
def bds_118 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_118 : KnownBin bds_118 := by
  intro b hb
  simp only [bds_118, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_16
theorem sub_118 : ∀ b ∈ bds_118, m_118 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_118, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_118 : ∀ b ∈ bds_118, canon b.1 g_118 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_118, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_118 : dagCheckRootsF m_118 g_118 bds_118 (dagRefF 0 (dagTraceF m_118 s_118 4 f_118) l_118 0) s_118 4 = true := by decide +kernel
def node_118 : Nat → Bool := dagCheckNodeF m_118 g_118 bds_118 0 (dagTraceF m_118 s_118 4 f_118) l_118
theorem nc_118 : ∀ j, 0 ≤ j → j < 0 → node_118 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_118 : LowerBin m_118 s_118 g_118 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_118 sub_118 gl_118 rc_118 nc_118

def f_122 : Nat → Nat × Nat := fun _ => (0, 0)
def l_122 : Nat → Nat → Option Nat := fun _ _ => none
def m_122 : Nat := 0xc0c0c0c0c0c0c0c
def s_122 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_122 : Nat := 0x404040c040c0c0c
def bds_122 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_122 : KnownBin bds_122 := by
  intro b hb
  simp only [bds_122, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_1
theorem sub_122 : ∀ b ∈ bds_122, m_122 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_122, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_122 : ∀ b ∈ bds_122, canon b.1 g_122 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_122, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_122 : dagCheckRootsF m_122 g_122 bds_122 (dagRefF 0 (dagTraceF m_122 s_122 4 f_122) l_122 0) s_122 4 = true := by decide +kernel
def node_122 : Nat → Bool := dagCheckNodeF m_122 g_122 bds_122 0 (dagTraceF m_122 s_122 4 f_122) l_122
theorem nc_122 : ∀ j, 0 ≤ j → j < 0 → node_122 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_122 : LowerBin m_122 s_122 g_122 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_122 sub_122 gl_122 rc_122 nc_122

def f_123 : Nat → Nat × Nat := fun _ => (0, 0)
def l_123 : Nat → Nat → Option Nat := fun _ _ => none
def m_123 : Nat := 0x3030303030303030
def s_123 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_123 : Nat := 0x1010103010303030
def bds_123 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_123 : KnownBin bds_123 := by
  intro b hb
  simp only [bds_123, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_2
theorem sub_123 : ∀ b ∈ bds_123, m_123 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_123, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_123 : ∀ b ∈ bds_123, canon b.1 g_123 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_123, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_123 : dagCheckRootsF m_123 g_123 bds_123 (dagRefF 0 (dagTraceF m_123 s_123 4 f_123) l_123 0) s_123 4 = true := by decide +kernel
def node_123 : Nat → Bool := dagCheckNodeF m_123 g_123 bds_123 0 (dagTraceF m_123 s_123 4 f_123) l_123
theorem nc_123 : ∀ j, 0 ≤ j → j < 0 → node_123 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_123 : LowerBin m_123 s_123 g_123 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_123 sub_123 gl_123 rc_123 nc_123

def m_124 : Nat := 0xc0c0c0c0c0c0c0c0
def s_124 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_124 : Nat := 0x40004040c0
def bds_124 : List (Nat × List Nat × Nat × Nat) := [(m_61, s_61, 4, g_61), (m_68, s_68, 4, g_68), (m_3, s_3, 4, g_3), (m_53, s_53, 4, g_53)]
theorem kn_124 : KnownBin bds_124 := by
  intro b hb
  simp only [bds_124, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_61
  · exact lb_68
  · exact lb_3
  · exact lb_53
theorem sub_124 : ∀ b ∈ bds_124, m_124 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_124, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_124 : ∀ b ∈ bds_124, canon b.1 g_124 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_124, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_124 : dagCheckRootsF m_124 g_124 bds_124 (dagRefF 43 (dagTraceF m_124 s_124 6 f_105) l_105 0) s_124 6 = true := by decide +kernel
def node_124 : Nat → Bool := dagCheckNodeF m_124 g_124 bds_124 43 (dagTraceF m_124 s_124 6 f_105) l_105
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_124_0 : treeBlockF 0 32 node_124 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_124_1 : treeBlockF 32 43 node_124 = true := by decide +kernel
theorem nc_124 : ∀ j, 0 ≤ j → j < 43 → node_124 j = true :=
  (joinChecks (certBlock nb_124_0) (certBlock nb_124_1))
theorem lb_124 : LowerBin m_124 s_124 g_124 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_124 sub_124 gl_124 rc_124 nc_124

def m_126 : Nat := 0xcc00cc00cc00cc
def s_126 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_126 : Nat := 0x4004c004c00cc
def bds_126 : List (Nat × List Nat × Nat × Nat) := [(m_75, s_75, 4, g_75), (m_79, s_79, 4, g_79), (m_53, s_53, 4, g_53), (m_7, s_7, 4, g_7)]
theorem kn_126 : KnownBin bds_126 := by
  intro b hb
  simp only [bds_126, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_75
  · exact lb_79
  · exact lb_53
  · exact lb_7
theorem sub_126 : ∀ b ∈ bds_126, m_126 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_126, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_126 : ∀ b ∈ bds_126, canon b.1 g_126 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_126, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_126 : dagCheckRootsF m_126 g_126 bds_126 (dagRefF 43 (dagTraceF m_126 s_126 6 f_110) l_110 0) s_126 6 = true := by decide +kernel
def node_126 : Nat → Bool := dagCheckNodeF m_126 g_126 bds_126 43 (dagTraceF m_126 s_126 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_126_0 : treeBlockF 0 32 node_126 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_126_1 : treeBlockF 32 43 node_126 = true := by decide +kernel
theorem nc_126 : ∀ j, 0 ≤ j → j < 43 → node_126 j = true :=
  (joinChecks (certBlock nb_126_0) (certBlock nb_126_1))
theorem lb_126 : LowerBin m_126 s_126 g_126 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_126 sub_126 gl_126 rc_126 nc_126

def f_127 : Nat → Nat × Nat := fun _ => (0, 0)
def l_127 : Nat → Nat → Option Nat := fun _ _ => none
def m_127 : Nat := 0xcc00cc00cc00cc00
def s_127 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_127 : Nat := 0x400040004004c00
def bds_127 : List (Nat × List Nat × Nat × Nat) := [(m_73, s_73, 4, g_73)]
theorem kn_127 : KnownBin bds_127 := by
  intro b hb
  simp only [bds_127, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_73
theorem sub_127 : ∀ b ∈ bds_127, m_127 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_127, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_127 : ∀ b ∈ bds_127, canon b.1 g_127 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_127, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_127 : dagCheckRootsF m_127 g_127 bds_127 (dagRefF 0 (dagTraceF m_127 s_127 4 f_127) l_127 0) s_127 4 = true := by decide +kernel
def node_127 : Nat → Bool := dagCheckNodeF m_127 g_127 bds_127 0 (dagTraceF m_127 s_127 4 f_127) l_127
theorem nc_127 : ∀ j, 0 ≤ j → j < 0 → node_127 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_127 : LowerBin m_127 s_127 g_127 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_127 sub_127 gl_127 rc_127 nc_127

def m_128 : Nat := 0xcccc0000cccc
def s_128 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_128 : Nat := 0x44c00004ccc
def bds_128 : List (Nat × List Nat × Nat × Nat) := [(m_73, s_73, 4, g_73), (m_82, s_82, 4, g_82), (m_61, s_61, 4, g_61), (m_11, s_11, 4, g_11)]
theorem kn_128 : KnownBin bds_128 := by
  intro b hb
  simp only [bds_128, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_73
  · exact lb_82
  · exact lb_61
  · exact lb_11
theorem sub_128 : ∀ b ∈ bds_128, m_128 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_128, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_128 : ∀ b ∈ bds_128, canon b.1 g_128 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_128, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_128 : dagCheckRootsF m_128 g_128 bds_128 (dagRefF 43 (dagTraceF m_128 s_128 6 f_110) l_110 0) s_128 6 = true := by decide +kernel
def node_128 : Nat → Bool := dagCheckNodeF m_128 g_128 bds_128 43 (dagTraceF m_128 s_128 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_128_0 : treeBlockF 0 32 node_128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_128_1 : treeBlockF 32 43 node_128 = true := by decide +kernel
theorem nc_128 : ∀ j, 0 ≤ j → j < 43 → node_128 j = true :=
  (joinChecks (certBlock nb_128_0) (certBlock nb_128_1))
theorem lb_128 : LowerBin m_128 s_128 g_128 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_128 sub_128 gl_128 rc_128 nc_128

def f_130 : Nat → Nat × Nat := fun _ => (0, 0)
def l_130 : Nat → Nat → Option Nat := fun _ _ => none
def m_130 : Nat := 0xcccc0000cccc0000
def s_130 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_130 : Nat := 0x4040000044c0000
def bds_130 : List (Nat × List Nat × Nat × Nat) := [(m_75, s_75, 4, g_75)]
theorem kn_130 : KnownBin bds_130 := by
  intro b hb
  simp only [bds_130, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_75
theorem sub_130 : ∀ b ∈ bds_130, m_130 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_130, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_130 : ∀ b ∈ bds_130, canon b.1 g_130 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_130, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_130 : dagCheckRootsF m_130 g_130 bds_130 (dagRefF 0 (dagTraceF m_130 s_130 4 f_130) l_130 0) s_130 4 = true := by decide +kernel
def node_130 : Nat → Bool := dagCheckNodeF m_130 g_130 bds_130 0 (dagTraceF m_130 s_130 4 f_130) l_130
theorem nc_130 : ∀ j, 0 ≤ j → j < 0 → node_130 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_130 : LowerBin m_130 s_130 g_130 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_130 sub_130 gl_130 rc_130 nc_130

def m_131 : Nat := 0xcccccccc
def s_131 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_131 : Nat := 0x44c4ccc
def bds_131 : List (Nat × List Nat × Nat × Nat) := [(m_77, s_77, 4, g_77), (m_81, s_81, 4, g_81), (m_68, s_68, 4, g_68), (m_16, s_16, 4, g_16)]
theorem kn_131 : KnownBin bds_131 := by
  intro b hb
  simp only [bds_131, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_77
  · exact lb_81
  · exact lb_68
  · exact lb_16
theorem sub_131 : ∀ b ∈ bds_131, m_131 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_131, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_131 : ∀ b ∈ bds_131, canon b.1 g_131 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_131, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_131 : dagCheckRootsF m_131 g_131 bds_131 (dagRefF 43 (dagTraceF m_131 s_131 6 f_110) l_110 0) s_131 6 = true := by decide +kernel
def node_131 : Nat → Bool := dagCheckNodeF m_131 g_131 bds_131 43 (dagTraceF m_131 s_131 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_131_0 : treeBlockF 0 32 node_131 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_131_1 : treeBlockF 32 43 node_131 = true := by decide +kernel
theorem nc_131 : ∀ j, 0 ≤ j → j < 43 → node_131 j = true :=
  (joinChecks (certBlock nb_131_0) (certBlock nb_131_1))
theorem lb_131 : LowerBin m_131 s_131 g_131 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_131 sub_131 gl_131 rc_131 nc_131

def f_133 : Nat → Nat × Nat := fun _ => (0, 0)
def l_133 : Nat → Nat → Option Nat := fun _ _ => none
def m_133 : Nat := 0xcccccccc00000000
def s_133 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_133 : Nat := 0x404044c00000000
def bds_133 : List (Nat × List Nat × Nat × Nat) := [(m_79, s_79, 4, g_79)]
theorem kn_133 : KnownBin bds_133 := by
  intro b hb
  simp only [bds_133, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_79
theorem sub_133 : ∀ b ∈ bds_133, m_133 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_133, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_133 : ∀ b ∈ bds_133, canon b.1 g_133 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_133, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_133 : dagCheckRootsF m_133 g_133 bds_133 (dagRefF 0 (dagTraceF m_133 s_133 4 f_133) l_133 0) s_133 4 = true := by decide +kernel
def node_133 : Nat → Bool := dagCheckNodeF m_133 g_133 bds_133 0 (dagTraceF m_133 s_133 4 f_133) l_133
theorem nc_133 : ∀ j, 0 ≤ j → j < 0 → node_133 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_133 : LowerBin m_133 s_133 g_133 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_133 sub_133 gl_133 rc_133 nc_133

def m_135 : Nat := 0xf000f000f000f0
def s_135 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_135 : Nat := 0x100070007000f0
def bds_135 : List (Nat × List Nat × Nat × Nat) := [(m_87, s_87, 4, g_87), (m_91, s_91, 4, g_91), (m_53, s_53, 4, g_53), (m_22, s_22, 4, g_22)]
theorem kn_135 : KnownBin bds_135 := by
  intro b hb
  simp only [bds_135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_87
  · exact lb_91
  · exact lb_53
  · exact lb_22
theorem sub_135 : ∀ b ∈ bds_135, m_135 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_135 : ∀ b ∈ bds_135, canon b.1 g_135 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_135, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_135 : dagCheckRootsF m_135 g_135 bds_135 (dagRefF 43 (dagTraceF m_135 s_135 6 f_110) l_110 0) s_135 6 = true := by decide +kernel
def node_135 : Nat → Bool := dagCheckNodeF m_135 g_135 bds_135 43 (dagTraceF m_135 s_135 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_135_0 : treeBlockF 0 32 node_135 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_135_1 : treeBlockF 32 43 node_135 = true := by decide +kernel
theorem nc_135 : ∀ j, 0 ≤ j → j < 43 → node_135 j = true :=
  (joinChecks (certBlock nb_135_0) (certBlock nb_135_1))
theorem lb_135 : LowerBin m_135 s_135 g_135 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_135 sub_135 gl_135 rc_135 nc_135

def f_136 : Nat → Nat × Nat := fun _ => (0, 0)
def l_136 : Nat → Nat → Option Nat := fun _ _ => none
def m_136 : Nat := 0xf000f000f000f000
def s_136 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_136 : Nat := 0x1000100010007000
def bds_136 : List (Nat × List Nat × Nat × Nat) := [(m_85, s_85, 4, g_85)]
theorem kn_136 : KnownBin bds_136 := by
  intro b hb
  simp only [bds_136, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_85
theorem sub_136 : ∀ b ∈ bds_136, m_136 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_136, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_136 : ∀ b ∈ bds_136, canon b.1 g_136 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_136, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_136 : dagCheckRootsF m_136 g_136 bds_136 (dagRefF 0 (dagTraceF m_136 s_136 4 f_136) l_136 0) s_136 4 = true := by decide +kernel
def node_136 : Nat → Bool := dagCheckNodeF m_136 g_136 bds_136 0 (dagTraceF m_136 s_136 4 f_136) l_136
theorem nc_136 : ∀ j, 0 ≤ j → j < 0 → node_136 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_136 : LowerBin m_136 s_136 g_136 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_136 sub_136 gl_136 rc_136 nc_136

def m_137 : Nat := 0xf0f00000f0f0
def s_137 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_137 : Nat := 0x1070000070f0
def bds_137 : List (Nat × List Nat × Nat × Nat) := [(m_85, s_85, 4, g_85), (m_94, s_94, 4, g_94), (m_61, s_61, 4, g_61), (m_26, s_26, 4, g_26)]
theorem kn_137 : KnownBin bds_137 := by
  intro b hb
  simp only [bds_137, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_85
  · exact lb_94
  · exact lb_61
  · exact lb_26
theorem sub_137 : ∀ b ∈ bds_137, m_137 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_137, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_137 : ∀ b ∈ bds_137, canon b.1 g_137 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_137, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_137 : dagCheckRootsF m_137 g_137 bds_137 (dagRefF 43 (dagTraceF m_137 s_137 6 f_110) l_110 0) s_137 6 = true := by decide +kernel
def node_137 : Nat → Bool := dagCheckNodeF m_137 g_137 bds_137 43 (dagTraceF m_137 s_137 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_137_0 : treeBlockF 0 32 node_137 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_137_1 : treeBlockF 32 43 node_137 = true := by decide +kernel
theorem nc_137 : ∀ j, 0 ≤ j → j < 43 → node_137 j = true :=
  (joinChecks (certBlock nb_137_0) (certBlock nb_137_1))
theorem lb_137 : LowerBin m_137 s_137 g_137 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_137 sub_137 gl_137 rc_137 nc_137

def f_139 : Nat → Nat × Nat := fun _ => (0, 0)
def l_139 : Nat → Nat → Option Nat := fun _ _ => none
def m_139 : Nat := 0xf0f00000f0f00000
def s_139 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_139 : Nat := 0x1010000010700000
def bds_139 : List (Nat × List Nat × Nat × Nat) := [(m_87, s_87, 4, g_87)]
theorem kn_139 : KnownBin bds_139 := by
  intro b hb
  simp only [bds_139, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_87
theorem sub_139 : ∀ b ∈ bds_139, m_139 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_139, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_139 : ∀ b ∈ bds_139, canon b.1 g_139 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_139, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_139 : dagCheckRootsF m_139 g_139 bds_139 (dagRefF 0 (dagTraceF m_139 s_139 4 f_139) l_139 0) s_139 4 = true := by decide +kernel
def node_139 : Nat → Bool := dagCheckNodeF m_139 g_139 bds_139 0 (dagTraceF m_139 s_139 4 f_139) l_139
theorem nc_139 : ∀ j, 0 ≤ j → j < 0 → node_139 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_139 : LowerBin m_139 s_139 g_139 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_139 sub_139 gl_139 rc_139 nc_139

def m_140 : Nat := 0xf0f0f0f0
def s_140 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_140 : Nat := 0x107070f0
def bds_140 : List (Nat × List Nat × Nat × Nat) := [(m_89, s_89, 4, g_89), (m_93, s_93, 4, g_93), (m_68, s_68, 4, g_68), (m_31, s_31, 4, g_31)]
theorem kn_140 : KnownBin bds_140 := by
  intro b hb
  simp only [bds_140, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_89
  · exact lb_93
  · exact lb_68
  · exact lb_31
theorem sub_140 : ∀ b ∈ bds_140, m_140 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_140, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_140 : ∀ b ∈ bds_140, canon b.1 g_140 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_140, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_140 : dagCheckRootsF m_140 g_140 bds_140 (dagRefF 43 (dagTraceF m_140 s_140 6 f_110) l_110 0) s_140 6 = true := by decide +kernel
def node_140 : Nat → Bool := dagCheckNodeF m_140 g_140 bds_140 43 (dagTraceF m_140 s_140 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_140_0 : treeBlockF 0 32 node_140 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_140_1 : treeBlockF 32 43 node_140 = true := by decide +kernel
theorem nc_140 : ∀ j, 0 ≤ j → j < 43 → node_140 j = true :=
  (joinChecks (certBlock nb_140_0) (certBlock nb_140_1))
theorem lb_140 : LowerBin m_140 s_140 g_140 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_140 sub_140 gl_140 rc_140 nc_140

def f_142 : Nat → Nat × Nat := fun _ => (0, 0)
def l_142 : Nat → Nat → Option Nat := fun _ _ => none
def m_142 : Nat := 0xf0f0f0f000000000
def s_142 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_142 : Nat := 0x1010107000000000
def bds_142 : List (Nat × List Nat × Nat × Nat) := [(m_91, s_91, 4, g_91)]
theorem kn_142 : KnownBin bds_142 := by
  intro b hb
  simp only [bds_142, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_91
theorem sub_142 : ∀ b ∈ bds_142, m_142 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_142, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_142 : ∀ b ∈ bds_142, canon b.1 g_142 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_142, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_142 : dagCheckRootsF m_142 g_142 bds_142 (dagRefF 0 (dagTraceF m_142 s_142 4 f_142) l_142 0) s_142 4 = true := by decide +kernel
def node_142 : Nat → Bool := dagCheckNodeF m_142 g_142 bds_142 0 (dagTraceF m_142 s_142 4 f_142) l_142
theorem nc_142 : ∀ j, 0 ≤ j → j < 0 → node_142 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_142 : LowerBin m_142 s_142 g_142 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_142 sub_142 gl_142 rc_142 nc_142

def m_145 : Nat := 0xff000000ff0000
def s_145 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_145 : Nat := 0x170000007f0000
def bds_145 : List (Nat × List Nat × Nat × Nat) := [(m_87, s_87, 4, g_87), (m_101, s_101, 4, g_101), (m_75, s_75, 4, g_75), (m_39, s_39, 4, g_39)]
theorem kn_145 : KnownBin bds_145 := by
  intro b hb
  simp only [bds_145, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_87
  · exact lb_101
  · exact lb_75
  · exact lb_39
theorem sub_145 : ∀ b ∈ bds_145, m_145 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_145, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_145 : ∀ b ∈ bds_145, canon b.1 g_145 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_145, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_145 : dagCheckRootsF m_145 g_145 bds_145 (dagRefF 43 (dagTraceF m_145 s_145 6 f_110) l_110 0) s_145 6 = true := by decide +kernel
def node_145 : Nat → Bool := dagCheckNodeF m_145 g_145 bds_145 43 (dagTraceF m_145 s_145 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_145_0 : treeBlockF 0 32 node_145 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_145_1 : treeBlockF 32 43 node_145 = true := by decide +kernel
theorem nc_145 : ∀ j, 0 ≤ j → j < 43 → node_145 j = true :=
  (joinChecks (certBlock nb_145_0) (certBlock nb_145_1))
theorem lb_145 : LowerBin m_145 s_145 g_145 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_145 sub_145 gl_145 rc_145 nc_145

def m_148 : Nat := 0xff00ff00000000
def s_148 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_148 : Nat := 0x17007f00000000
def bds_148 : List (Nat × List Nat × Nat × Nat) := [(m_91, s_91, 4, g_91), (m_101, s_101, 4, g_101), (m_79, s_79, 4, g_79), (m_44, s_44, 4, g_44)]
theorem kn_148 : KnownBin bds_148 := by
  intro b hb
  simp only [bds_148, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_91
  · exact lb_101
  · exact lb_79
  · exact lb_44
theorem sub_148 : ∀ b ∈ bds_148, m_148 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_148, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_148 : ∀ b ∈ bds_148, canon b.1 g_148 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_148, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_148 : dagCheckRootsF m_148 g_148 bds_148 (dagRefF 43 (dagTraceF m_148 s_148 6 f_110) l_110 0) s_148 6 = true := by decide +kernel
def node_148 : Nat → Bool := dagCheckNodeF m_148 g_148 bds_148 43 (dagTraceF m_148 s_148 6 f_110) l_110
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_148_0 : treeBlockF 0 32 node_148 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_148_1 : treeBlockF 32 43 node_148 = true := by decide +kernel
theorem nc_148 : ∀ j, 0 ≤ j → j < 43 → node_148 j = true :=
  (joinChecks (certBlock nb_148_0) (certBlock nb_148_1))
theorem lb_148 : LowerBin m_148 s_148 g_148 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_148 sub_148 gl_148 rc_148 nc_148

def f_153 : Nat → Nat × Nat := fun _ => (0, 0)
def l_153 : Nat → Nat → Option Nat := fun _ _ => none
def m_153 : Nat := 0x5555555555555555
def s_153 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_153 : Nat := 0x1515155515555555
def bds_153 : List (Nat × List Nat × Nat × Nat) := [(m_104, s_104, 5, g_104)]
theorem kn_153 : KnownBin bds_153 := by
  intro b hb
  simp only [bds_153, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_104
theorem sub_153 : ∀ b ∈ bds_153, m_153 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_153, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_153 : ∀ b ∈ bds_153, canon b.1 g_153 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_153, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_153 : dagCheckRootsF m_153 g_153 bds_153 (dagRefF 0 (dagTraceF m_153 s_153 5 f_153) l_153 0) s_153 5 = true := by decide +kernel
def node_153 : Nat → Bool := dagCheckNodeF m_153 g_153 bds_153 0 (dagTraceF m_153 s_153 5 f_153) l_153
theorem nc_153 : ∀ j, 0 ≤ j → j < 0 → node_153 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_153 : LowerBin m_153 s_153 g_153 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_153 sub_153 gl_153 rc_153 nc_153

def f_156 : Nat → Nat × Nat := unpackForestF 0xcf929cf829c9253c9251cd361cd13ecd019c9153c9151ca361ca261ca03eca02ec9053c905100b47c7951c7851c1247c1246c5356c5156c5019c112bc1129c2356c2239c2056c202ec102bc102900a4bb835ab825abe961be861b8257b8256bc366bc166bc019b812bb8129b9366b9239b9066b902eb802bb802900a3bb493ab4936b4935b4934b5024b4839aab4bb3351b3051aa947aa946b1934afb5aafb56af956af839aa93faa93eaca56aca4eac856ac84eaa81bab834ab34baa8190094ba713aa7136a7135a7134a7824a70399c35b9c25a9c15aa4b61a48619c1579c156a3134a136aa1366a1166a10399c13f9c13e9e2669e24e9e0669e04e9c01b9d0349cb5b9c0190093b96b629ab6096a629696e9696d9696c9801896962970249686189c578995a9446d944559406189957899568994a8ed6a9116c910608ed668ec668fb548e9668e85189947899468ba668ba568b8668b8568981b8a86c8a457898190092388824862398603a8603686035860346fb4b8503482a4e8282a8282682825828246fa4b818247da5a8085c7da567d92a7d82a7d8267d8257d8246fa337c3517c2516f8477b15c7a9236f8467983477b5a77b5677a39778566f83f769347614b6f83e7502471a5a71a5671a4e7302471a42718567184e6f82f709347034b6f82e0084b6e8246c2396c03a6c0366c0356c0345235b6b03468a4e6882a6882668825688245225b6782463a6a6686c63a666392a6382a63826638256382452233621246202461a335215a60824602335205a5eb615ea61520575d96c5d123520565c0345a36a5a3665a2395a0665203f591345895b5203e578245426a542665424e5582454242540665404e5202f5313452b5b5202e0083b4cb62508244ca614fb604c9624c86e4c86d4c86c4d02c4c8622d4574b85c492564902a4902649025490242d25b480244336a470244326a4606c432664302a430264302543a5a430242d24b41a6c4186c414572d231400243fa4b2d05a3dc6d3dc553da612d0573c96c3c13b2d0563b0243aa5b2d04a3656a38a603886c36566364663625136b54360662d0473515c3495b2d0462f36a2f35a328242f26a2f266310242f25a2f2562f0662f0562d02f2e16c2dc572d02e008232c03427b6127a622aa60279622786e2786d2786c2803c27862014572685c243562403a2403624035240340135b230341e46a220341e36a2106c1e3661e03a1e0361e0351eb5a1e0340134b1ca6c1c86c1c457012321a96c1a86c17c5718a5c1895c1885c1834717a3001132168341634b0105a1446d1445514361010571326c12a3b01056118341135b0104a0cd6a0f3600f06c0cd660cc660cb510d3540c866010470ba5c0b25b0104605c6a05c5a0903405b6a05b660783405b5a05b5605866058560103f04a6c044570103e0306c01c57018540184401032008130001f 9 11
def l_156 : Nat → Nat → Option Nat := unpackLinksF 0xac02b00aa22a71a986a60a9829e8a7469c1a6c69b0a6c2938a48686ca182860a01a7f19fc27f09fc27969e067809e027809e027269c4664d98c66219882620971a5b196c25b096c25569506540950254095024e6934640d8fc63f08fc23f08fc23e18d663508d422f68b862e08b462d08b422d089da26189822608982260881a20087c61e184761018402100840210083c6069814604181020407f99fd17f41fc17f01fc07f01f667d45f507d41f507d41ef67bc1ee17b45e0d77c5df07785de07781dc27701da27681d9172bdc917241c817201c177005bf16fc1bf06fc1bd26f05bc06ec5bb06d1db316cc1b306cc1b306ae1ab06a85a9166f99b066859916641990664190964018f163858e063818e06165850610584060c5830608582060818115dad7605d817065c016f15b856e05b456d05b416d059d9670598565159416415901640590163158c163057595d057055b153b54e053454c153014c0530143950c1421504541050414104e253804dc53704d853604d453504d413414a6d2904a4127249852604945241490124047991e047451c147011b146c11b046c1156454114144c513044851204481120444511044410b642c10a14244fcd3ec4fb03e84fa03e44f903e40f723dc0f5239bce603944e413900e4038c4d8b3600d623580d513540d4134c4d3034c0d303484c7b3184c51308cc023000bf12f84be02f44bd02d9cb602d44b412d00b312c84b202c80b202c08af12bc0af02b84a7729c0a612944a502940a502904a402900a3128c0a3028c09b826c09a126448be22c08a122448902204880220086221808421d7c7501d047311cc07301c8467b19c06521940641190063118846201880620184456b1544541144c4f213844d1128c4a012804a011cc461110844010c4421108041110403a70e803910e043800dc43610d803600d803420cc43300cc03210adc2b00a842910a402900a402810a0028009c427009c027007e01f007841d107401c107001c0064c0be0068001 0xce1619b131d012997921cb86151031cf8294c8212b8139aa40ce3619a232cd93e97932cb0612b021cd01927811500334f9402a930cbb61cb2614f1322a122ca83e4c832ca02e2782296a33bfa59cf253cea51a5959cc953cc151961235f859c9853c90514c02327013a9959c8151c61296d859c7851c382926013c6356a995ac5956c3039c5019258116e04bc3b56c32396d85ac2856c202e25822a724bc034abfa4ac7247c6a46a694bc492bc4129959216b84bc182bc10293f021238132281321813b7169bf161bd12987869be861ba82920813bd366b716abc966ba039bc019200118805bbab66ba2398786ab9866b902e20022b4a5bc035abfa5abe257bda56b415bbb92bbb129929218585bb882bb80293a0211d813b1934b5024b113db713ab6936b6135b5934b48393a831ab01916011b1359b3b51b013e6a059b3051ae0194b023b1934b135ab0b56b0156af8394a831ad8196a84bae256ada4e6a05aad056ac84e4a842ab834ab34bb434ba624aa594ab2947b2146af13fae93e959326804b48833ac01baa81915811a3134a7824a293da993aa9136a8935a8134a70393f8319c819110114783346833a2b69a5361a193e84069a48619f81945823a3134a2b6aa2366a1966a1039450319f0198485b9fa669f24e8406a9e8669e04e450429d0349cb5ba6b5ba625aa595aa4157a3956a093fa013e929328205b428339d81b9c019108119aa609ab60420211d0119196c98018970249b3629a2629996e9916d9896c909659796294955901456006996861410311c0218a019028116704b8f9449546d90c6594c558f1467f069940618d0196603b8105b9196c910608f9548fb549256a90d66904668f166650598e8518c8198005b8d2668ca567f96a6595a7f06a8c0666505a8b8568a86c8a457964579595a93957931569294a8e1478d9467d05b6304b408311b8218b01b8981901011888247983488239812317903d8783a8703686835860347002e16022850347502484a4e812427604e3f8427482d8402a838268302582824818248085c730246204a8125a802566195a7f92a6005a7a8567282d7f02a7e8267e0257d824793597cb5174a597c2517783e7202e7b15c7a923798347935a78b567823972a31778567182e769347614b750247302474a5a7425673a4e72a42720567184e709347034b85b4b8224b7d2336114a5f84a7b8477a0467703f7583e3f0327102f6f82e158226e8245c0346e239672315b83d6d83a6d0366c8356c0345282e110226b034578246aa4e672425884e3a8425702d6a02a698266902568824678246686c558246285a6726a662666196a6592a6006a5d0665502d6502a648266402563824629246202461a3360824602335bb695f361572695ea615a03e5482e5d96c5d1235c0345bb6a5b3665aa39552315a0665402e591345895b57824558245726a56a665624e55242548665404e5313452b5b6bb5b6825b632336115a5f85a5e0575c8565983f5803e3a0325382f5202e108224f960508244fb60419211b0123886c4d02c5136246a6950261412314f1621a1224e86e4e06d4d86c380654c8623e055378452d82e028224b85c328244824a47b5a46a5a4b2563a85a348563383d3202d4a82a4a02649825490244383448024470244606c3102443a5a47b6a46a6a45a663f86a3c0663303d3082d4502a44826440254302419920190204226c181304186c4145717930400243fa4b368443ec6d384653e455322693da61360462f82e3c96c3c13b3b0243aa5b392603886c3685436b5439d6a3856637c6630a5937251360662f02e3515c3495b328243102433b6a3335a3226a31a6630a5a302562f8662f0562e16c2dc574c45748a5b42a4b40a31171223f05a3d0573b8563a04a35847340462e82f2d02e010222c0342a9602aa601c9221a8220f06c2803c21b692bb612b2621c2322a1621a1322986e2906d2886c0e86527862148550e0450403e028322685c090342334a22c5a21b5a263561105a0b0560a04d0883d2583a2503624835240341e84423034220342106c078341eb5a22c6a21b6a20b661606a128660984d0703d2003a1f8361f0351e03419920188201d26c181301c86c1c457179301912018920182301b16c1a86c19a5c1915c1885c183471a45717a30168341634b0d0441546d0ec6514c5508b69143610c8460603e1326c12a3b118341135b0fb600f06c0d0540d3541056a0ed660e466073590db510c8660583e0ba5c0b25b09034078340a46a09c5a08b6a083660735a06b56060660585604a6c044570306c02c5702054018442745723b5b1db4b1ba32171321585a13857120561084a0c0470a8460503f0383e01032c8b47c0a4bb7a3baa14b9b93b891236f04b5183b2c823008130001f 14 4 11 9 5
def m_156 : Nat := 0xcccccccccccccccc
def s_156 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_156 : Nat := 0x404044c044c4ccc
def bds_156 : List (Nat × List Nat × Nat × Nat) := [(m_128, s_128, 7, g_128), (m_131, s_131, 7, g_131), (m_127, s_127, 5, g_127), (m_126, s_126, 7, g_126), (m_124, s_124, 7, g_124), (m_105, s_105, 7, g_105), (m_122, s_122, 5, g_122), (m_104, s_104, 5, g_104), (m_133, s_133, 5, g_133), (m_130, s_130, 5, g_130)]
theorem kn_156 : KnownBin bds_156 := by
  intro b hb
  simp only [bds_156, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_128
  · exact lb_131
  · exact lb_127
  · exact lb_126
  · exact lb_124
  · exact lb_105
  · exact lb_122
  · exact lb_104
  · exact lb_133
  · exact lb_130
theorem sub_156 : ∀ b ∈ bds_156, m_156 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_156, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_156 : ∀ b ∈ bds_156, canon b.1 g_156 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_156, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_156 : dagCheckRootsF m_156 g_156 bds_156 (dagRefF 417 (dagTraceF m_156 s_156 9 f_156) l_156 0) s_156 9 = true := by decide +kernel
def node_156 : Nat → Bool := dagCheckNodeF m_156 g_156 bds_156 417 (dagTraceF m_156 s_156 9 f_156) l_156
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_0 : treeBlockF 0 32 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_1 : treeBlockF 32 64 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_2 : treeBlockF 64 96 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_3 : treeBlockF 96 128 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_4 : treeBlockF 128 160 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_5 : treeBlockF 160 192 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_6 : treeBlockF 192 224 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_7 : treeBlockF 224 256 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_8 : treeBlockF 256 288 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_9 : treeBlockF 288 320 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_10 : treeBlockF 320 352 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_11 : treeBlockF 352 384 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_12 : treeBlockF 384 416 node_156 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_156_13 : treeBlockF 416 417 node_156 = true := by decide +kernel
theorem nc_156 : ∀ j, 0 ≤ j → j < 417 → node_156 j = true :=
  (joinChecks (joinChecks (joinChecks (certBlock nb_156_0) (joinChecks (certBlock nb_156_1) (certBlock nb_156_2))) (joinChecks (joinChecks (certBlock nb_156_3) (certBlock nb_156_4)) (joinChecks (certBlock nb_156_5) (certBlock nb_156_6)))) (joinChecks (joinChecks (certBlock nb_156_7) (joinChecks (certBlock nb_156_8) (certBlock nb_156_9))) (joinChecks (joinChecks (certBlock nb_156_10) (certBlock nb_156_11)) (joinChecks (certBlock nb_156_12) (certBlock nb_156_13)))))
theorem lb_156 : LowerBin m_156 s_156 g_156 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_156 sub_156 gl_156 rc_156 nc_156

def m_158 : Nat := 0xf0f0f0f0f0f0f0f0
def s_158 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_158 : Nat := 0x10101070107070f0
def bds_158 : List (Nat × List Nat × Nat × Nat) := [(m_137, s_137, 7, g_137), (m_140, s_140, 7, g_140), (m_136, s_136, 5, g_136), (m_135, s_135, 7, g_135), (m_124, s_124, 7, g_124), (m_108, s_108, 7, g_108), (m_123, s_123, 5, g_123), (m_107, s_107, 5, g_107), (m_142, s_142, 5, g_142), (m_139, s_139, 5, g_139)]
theorem kn_158 : KnownBin bds_158 := by
  intro b hb
  simp only [bds_158, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_137
  · exact lb_140
  · exact lb_136
  · exact lb_135
  · exact lb_124
  · exact lb_108
  · exact lb_123
  · exact lb_107
  · exact lb_142
  · exact lb_139
theorem sub_158 : ∀ b ∈ bds_158, m_158 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_158, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_158 : ∀ b ∈ bds_158, canon b.1 g_158 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_158, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_158 : dagCheckRootsF m_158 g_158 bds_158 (dagRefF 417 (dagTraceF m_158 s_158 9 f_156) l_156 0) s_158 9 = true := by decide +kernel
def node_158 : Nat → Bool := dagCheckNodeF m_158 g_158 bds_158 417 (dagTraceF m_158 s_158 9 f_156) l_156
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_0 : treeBlockF 0 32 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_1 : treeBlockF 32 64 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_2 : treeBlockF 64 96 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_3 : treeBlockF 96 128 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_4 : treeBlockF 128 160 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_5 : treeBlockF 160 192 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_6 : treeBlockF 192 224 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_7 : treeBlockF 224 256 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_8 : treeBlockF 256 288 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_9 : treeBlockF 288 320 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_10 : treeBlockF 320 352 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_11 : treeBlockF 352 384 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_12 : treeBlockF 384 416 node_158 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_158_13 : treeBlockF 416 417 node_158 = true := by decide +kernel
theorem nc_158 : ∀ j, 0 ≤ j → j < 417 → node_158 j = true :=
  (joinChecks (joinChecks (joinChecks (certBlock nb_158_0) (joinChecks (certBlock nb_158_1) (certBlock nb_158_2))) (joinChecks (joinChecks (certBlock nb_158_3) (certBlock nb_158_4)) (joinChecks (certBlock nb_158_5) (certBlock nb_158_6)))) (joinChecks (joinChecks (certBlock nb_158_7) (joinChecks (certBlock nb_158_8) (certBlock nb_158_9))) (joinChecks (joinChecks (certBlock nb_158_10) (certBlock nb_158_11)) (joinChecks (certBlock nb_158_12) (certBlock nb_158_13)))))
theorem lb_158 : LowerBin m_158 s_158 g_158 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_158 sub_158 gl_158 rc_158 nc_158

def f_160 : Nat → Nat × Nat := fun _ => (0, 0)
def l_160 : Nat → Nat → Option Nat := fun _ _ => none
def m_160 : Nat := 0xff00ff00ff00ff00
def s_160 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_160 : Nat := 0x1500150015007f00
def bds_160 : List (Nat × List Nat × Nat × Nat) := [(m_127, s_127, 5, g_127)]
theorem kn_160 : KnownBin bds_160 := by
  intro b hb
  simp only [bds_160, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_127
theorem sub_160 : ∀ b ∈ bds_160, m_160 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_160, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_160 : ∀ b ∈ bds_160, canon b.1 g_160 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_160, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_160 : dagCheckRootsF m_160 g_160 bds_160 (dagRefF 0 (dagTraceF m_160 s_160 5 f_160) l_160 0) s_160 5 = true := by decide +kernel
def node_160 : Nat → Bool := dagCheckNodeF m_160 g_160 bds_160 0 (dagTraceF m_160 s_160 5 f_160) l_160
theorem nc_160 : ∀ j, 0 ≤ j → j < 0 → node_160 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_160 : LowerBin m_160 s_160 g_160 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_160 sub_160 gl_160 rc_160 nc_160

def f_161 : Nat → Nat × Nat := fun _ => (0, 0)
def l_161 : Nat → Nat → Option Nat := fun _ _ => none
def m_161 : Nat := 0xffff0000ffff
def s_161 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_161 : Nat := 0x157f00007fff
def bds_161 : List (Nat × List Nat × Nat × Nat) := [(m_128, s_128, 7, g_128)]
theorem kn_161 : KnownBin bds_161 := by
  intro b hb
  simp only [bds_161, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_128
theorem sub_161 : ∀ b ∈ bds_161, m_161 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_161, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_161 : ∀ b ∈ bds_161, canon b.1 g_161 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_161, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_161 : dagCheckRootsF m_161 g_161 bds_161 (dagRefF 0 (dagTraceF m_161 s_161 7 f_161) l_161 0) s_161 7 = true := by decide +kernel
def node_161 : Nat → Bool := dagCheckNodeF m_161 g_161 bds_161 0 (dagTraceF m_161 s_161 7 f_161) l_161
theorem nc_161 : ∀ j, 0 ≤ j → j < 0 → node_161 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_161 : LowerBin m_161 s_161 g_161 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_161 sub_161 gl_161 rc_161 nc_161

def f_162 : Nat → Nat × Nat := fun _ => (0, 0)
def l_162 : Nat → Nat → Option Nat := fun _ _ => none
def m_162 : Nat := 0xffff0000ffff0000
def s_162 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_162 : Nat := 0x15170000157f0000
def bds_162 : List (Nat × List Nat × Nat × Nat) := [(m_145, s_145, 7, g_145)]
theorem kn_162 : KnownBin bds_162 := by
  intro b hb
  simp only [bds_162, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_145
theorem sub_162 : ∀ b ∈ bds_162, m_162 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_162, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_162 : ∀ b ∈ bds_162, canon b.1 g_162 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_162, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_162 : dagCheckRootsF m_162 g_162 bds_162 (dagRefF 0 (dagTraceF m_162 s_162 7 f_162) l_162 0) s_162 7 = true := by decide +kernel
def node_162 : Nat → Bool := dagCheckNodeF m_162 g_162 bds_162 0 (dagTraceF m_162 s_162 7 f_162) l_162
theorem nc_162 : ∀ j, 0 ≤ j → j < 0 → node_162 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_162 : LowerBin m_162 s_162 g_162 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_162 sub_162 gl_162 rc_162 nc_162

def f_163 : Nat → Nat × Nat := fun _ => (0, 0)
def l_163 : Nat → Nat → Option Nat := fun _ _ => none
def m_163 : Nat := 0xffffffff
def s_163 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_163 : Nat := 0x157f7fff
def bds_163 : List (Nat × List Nat × Nat × Nat) := [(m_131, s_131, 7, g_131)]
theorem kn_163 : KnownBin bds_163 := by
  intro b hb
  simp only [bds_163, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_131
theorem sub_163 : ∀ b ∈ bds_163, m_163 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_163, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_163 : ∀ b ∈ bds_163, canon b.1 g_163 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_163, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_163 : dagCheckRootsF m_163 g_163 bds_163 (dagRefF 0 (dagTraceF m_163 s_163 7 f_163) l_163 0) s_163 7 = true := by decide +kernel
def node_163 : Nat → Bool := dagCheckNodeF m_163 g_163 bds_163 0 (dagTraceF m_163 s_163 7 f_163) l_163
theorem nc_163 : ∀ j, 0 ≤ j → j < 0 → node_163 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_163 : LowerBin m_163 s_163 g_163 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_163 sub_163 gl_163 rc_163 nc_163

def f_164 : Nat → Nat × Nat := fun _ => (0, 0)
def l_164 : Nat → Nat → Option Nat := fun _ _ => none
def m_164 : Nat := 0xffffffff00000000
def s_164 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_164 : Nat := 0x1517157f00000000
def bds_164 : List (Nat × List Nat × Nat × Nat) := [(m_148, s_148, 7, g_148)]
theorem kn_164 : KnownBin bds_164 := by
  intro b hb
  simp only [bds_164, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_148
theorem sub_164 : ∀ b ∈ bds_164, m_164 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_164, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_164 : ∀ b ∈ bds_164, canon b.1 g_164 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_164, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_164 : dagCheckRootsF m_164 g_164 bds_164 (dagRefF 0 (dagTraceF m_164 s_164 7 f_164) l_164 0) s_164 7 = true := by decide +kernel
def node_164 : Nat → Bool := dagCheckNodeF m_164 g_164 bds_164 0 (dagTraceF m_164 s_164 7 f_164) l_164
theorem nc_164 : ∀ j, 0 ≤ j → j < 0 → node_164 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_164 : LowerBin m_164 s_164 g_164 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_164 sub_164 gl_164 rc_164 nc_164

def f_165 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def l_165 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
def m_165 : Nat := 0xff00ff00ff00ff
def s_165 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_165 : Nat := 0x17007f007f00ff
def bds_165 : List (Nat × List Nat × Nat × Nat) := [(m_145, s_145, 7, g_145), (m_135, s_135, 7, g_135), (m_126, s_126, 7, g_126), (m_110, s_110, 7, g_110)]
theorem kn_165 : KnownBin bds_165 := by
  intro b hb
  simp only [bds_165, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_145
  · exact lb_135
  · exact lb_126
  · exact lb_110
theorem sub_165 : ∀ b ∈ bds_165, m_165 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_165, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_165 : ∀ b ∈ bds_165, canon b.1 g_165 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_165, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_165 : dagCheckRootsF m_165 g_165 bds_165 (dagRefF 1 (dagTraceF m_165 s_165 8 f_165) l_165 0) s_165 8 = true := by decide +kernel
def node_165 : Nat → Bool := dagCheckNodeF m_165 g_165 bds_165 1 (dagTraceF m_165 s_165 8 f_165) l_165
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_165_0 : treeBlockF 0 1 node_165 = true := by decide +kernel
theorem nc_165 : ∀ j, 0 ≤ j → j < 1 → node_165 j = true :=
  (certBlock nb_165_0)
theorem lb_165 : LowerBin m_165 s_165 g_165 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_165 sub_165 gl_165 rc_165 nc_165

def f_166 : Nat → Nat × Nat := unpackForestF 0x10fa1b42f4910981f 2 9
def l_166 : Nat → Nat → Option Nat := unpackLinksF 0x38e31c29301 0x410524a1f81b61721301f 6 3 9 3 4
def m_166 : Nat := 0xaaaaaaaaaaaaaaaa
def s_166 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_166 : Nat := 0x2002a002a2aaa
def bds_166 : List (Nat × List Nat × Nat × Nat) := [(m_114, s_114, 5, g_114), (m_116, s_116, 5, g_116), (m_110, s_110, 7, g_110), (m_108, s_108, 7, g_108), (m_105, s_105, 7, g_105), (m_118, s_118, 5, g_118)]
theorem kn_166 : KnownBin bds_166 := by
  intro b hb
  simp only [bds_166, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_114
  · exact lb_116
  · exact lb_110
  · exact lb_108
  · exact lb_105
  · exact lb_118
theorem sub_166 : ∀ b ∈ bds_166, m_166 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_166, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_166 : ∀ b ∈ bds_166, canon b.1 g_166 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_166, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_166 : dagCheckRootsF m_166 g_166 bds_166 (dagRefF 6 (dagTraceF m_166 s_166 8 f_166) l_166 0) s_166 8 = true := by decide +kernel
def node_166 : Nat → Bool := dagCheckNodeF m_166 g_166 bds_166 6 (dagTraceF m_166 s_166 8 f_166) l_166
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_166_0 : treeBlockF 0 6 node_166 = true := by decide +kernel
theorem nc_166 : ∀ j, 0 ≤ j → j < 6 → node_166 j = true :=
  (certBlock nb_166_0)
theorem lb_166 : LowerBin m_166 s_166 g_166 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_166 sub_166 gl_166 rc_166 nc_166

def f_167 : Nat → Nat × Nat := unpackForestF 0x29674a5931ad2fa38f1ad2b6b49e741f9d06e74179d04e712c998d2657499531ad23949d2524c944e651356b0be223d91092223b8f09222398d13222378b0f22235888c6213c6b0ae1a3c7a4b6114c7a4ae093c7a4a603407a49dfa307a495ed747b4f1e9216b09de0246c8e5d83c6c8d5c41f7106dc4177104dc02c6c4d1b9256c1d1b04c6b08c065b680ada027674f8055b640ad9027639840557601bd80635f998052f5c1bd70635b5980523590d14e3f570914e33544ad5127530f8045b504ad41274a9853a7c4a4bd2d7c4b59129230115d1d6f4758d0a66454d1096b439f10967010bd0024399acf87c3999ce96f3a58ce955391980423364d8d9342ddacce6333984b5662f9a8be672f998b53e2d0c8041f2a0d8a83421dac86322698c9a61211988a6a2299c8a66210f8041b1e8e87a3815dac6d3f1b4f8566a16da8596a1659c5966158c80417120d8483402dac0a3e024f82e5b0c96831570b48809240898c2261021980f6a039a80e6703998083e0104c003f 8 10
def l_167 : Nat → Nat → Option Nat := unpackLinksF 0xe60e60e15e01d97d27d20d20d20d20ce4cd1cc1cc0c75c70c70c61c51c05bf1bf0be1be0bd1bd0bc1bc0bb1ba1b91b27b20b11b10b01b00af1af0ae1ae0ad1ad0ad0ab2a47a40a31a30a12a10a10a10a109d49c19c09b19b09658ac8a08a08828538508508328038008007e27a47a07a07737347307217207117107106f26c36c06c06a26a06916906906726436406406226206116106015c45c05b15b05925905905905635245205204f34f04f04c34c04c04c04934904544504504234204204203f33f03f03f03c33843803803353303303032f12f02e12e02952542502502052002001f11f01f01d21b21b01b01831801801801801440e601d001 0xa69d2964ca34e24839850d67124a38f2543d900ee3839830de0435770c66d20940b6302b8a0a5fc277d095d421a007e7c1b9e05e74139c4b1f0259b8d269749953224397a0d5d934788f25e74969325539944d620387b0d244248f092344c8b0f21824700924a3d908ee3a398c8de2a35898c6213c868f2114c824f203407e8c1f1747b4f2152d834ae05297f49df5257a485bc2078091b874760f1d01f7306dc8177104dc02c6e495de39758d5bd346d1d1b04ca44be892ba149e6123930be1c2b7909dac233507ca41b1d05c4413690ada027674f9103f3f0cd942b6409d8e61420bcf423611bd80635f999606b4d19c40115d1bd70634b1556d66561ad2867280a5643457091552b5449d623f568cd4c3e514ad41274e9f1317c4b5913e614d4bd2923485bd1d63454d10e7c46999116b4259c3c1240090f87c3a190f16f3b58ce9553f9acf6672d4b8e466314f0dd36364d0c6693498cce61319a8c2672f998d76b32598b93e2d0c8903c2b0d8a834249a49e6326984926a2399c8a6629daca23225198843e199007e3a1e8e062300e040713f1b4f861320d080302019da8616a1759c59660b080776b1a9a856320a040392406130143c130d848340d4c0365a0c55c3a5b0b48816690998c226106da8166a0499c0e6611dac423e0f4f8292407198083e6a96d995b6255d792f5a48d485b4915d042f3808cb01f2006c50170104c003f 12 4 10 8 5
def m_167 : Nat := 0xffffffffffffffff
def s_167 : List Nat := [0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def g_167 : Nat := 0x1517157f157f7fff
def bds_167 : List (Nat × List Nat × Nat × Nat) := [(m_161, s_161, 8, g_161), (m_162, s_162, 8, g_162), (m_165, s_165, 9, g_165), (m_156, s_156, 10, g_156), (m_164, s_164, 8, g_164), (m_158, s_158, 10, g_158), (m_166, s_166, 9, g_166), (m_163, s_163, 8, g_163), (m_153, s_153, 6, g_153), (m_160, s_160, 6, g_160)]
theorem kn_167 : KnownBin bds_167 := by
  intro b hb
  simp only [bds_167, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_161
  · exact lb_162
  · exact lb_165
  · exact lb_156
  · exact lb_164
  · exact lb_158
  · exact lb_166
  · exact lb_163
  · exact lb_153
  · exact lb_160
theorem sub_167 : ∀ b ∈ bds_167, m_167 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_167, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_167 : ∀ b ∈ bds_167, canon b.1 g_167 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_167, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_167 : dagCheckRootsF m_167 g_167 bds_167 (dagRefF 167 (dagTraceF m_167 s_167 11 f_167) l_167 0) s_167 11 = true := by decide +kernel
def node_167 : Nat → Bool := dagCheckNodeF m_167 g_167 bds_167 167 (dagTraceF m_167 s_167 11 f_167) l_167
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_0 : treeBlockF 0 32 node_167 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_1 : treeBlockF 32 64 node_167 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_2 : treeBlockF 64 96 node_167 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_3 : treeBlockF 96 128 node_167 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_4 : treeBlockF 128 160 node_167 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_167_5 : treeBlockF 160 167 node_167 = true := by decide +kernel
theorem nc_167 : ∀ j, 0 ≤ j → j < 167 → node_167 j = true :=
  (joinChecks (joinChecks (certBlock nb_167_0) (joinChecks (certBlock nb_167_1) (certBlock nb_167_2))) (joinChecks (certBlock nb_167_3) (joinChecks (certBlock nb_167_4) (certBlock nb_167_5))))
theorem lb_167 : LowerBin m_167 s_167 g_167 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_167 sub_167 gl_167 rc_167 nc_167

def wg : List Gate :=
  [⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.and, [3, 8]⟩,
    ⟨GateOp.and, [7, 9]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.and, [10, 11]⟩,
    ⟨GateOp.and, [16, 17]⟩]

theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) =
    Nat.testBit (3941132928 * 2 ^ 32 + 3934289920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

theorem root_lb : LowerBin fullMask rootStock (canon fullMask (3941132928 * 2 ^ 32 + 3934289920)) (13 - 1) := by
  exact lb_167

end PEqualNP.Outside.L_meta_49487

theorem PEqualNP.Outside.L_meta_49487 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132928 * 2 ^ 32 + 3934289920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132928 * 2 ^ 32 + 3934289920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_49487.table2_from_lowerBin
    (3941132928 * 2 ^ 32 + 3934289920) 13 PEqualNP.Outside.L_meta_49487.root_lb
    PEqualNP.Outside.L_meta_49487.wg 18 rfl
    PEqualNP.Outside.L_meta_49487.wfits PEqualNP.Outside.L_meta_49487.weval
