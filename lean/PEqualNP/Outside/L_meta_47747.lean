import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47747

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

def m_0 : Nat := 0x202020202020202
def s_0 : List Nat := [0x2000200020002, 0x20200000202, 0x2020202]
def g_0 : Nat := 0x200020202
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

def m_1 : Nat := 0x22002200220022
def s_1 : List Nat := [0x2000200020002, 0x2200000022, 0x220022]
def g_1 : Nat := 0x200020022
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

def m_2 : Nat := 0xa000a000a000a
def s_2 : List Nat := [0x2000200020002, 0xa0000000a, 0xa000a]
def g_2 : Nat := 0x20002000a
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

def m_3 : Nat := 0xc000c000c000c00
def s_3 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_3 : Nat := 0x40004000c00
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

def m_4 : Nat := 0x4444000044440000
def s_4 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_4 : Nat := 0x4000004440000
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

def m_5 : Nat := 0x222200002222
def s_5 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_5 : Nat := 0x200000222
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

def m_6 : Nat := 0xaa000000aa
def s_6 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_6 : Nat := 0x20000002a
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

def m_7 : Nat := 0x4444444400000000
def s_7 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_7 : Nat := 0x4044400000000
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

def m_8 : Nat := 0x22222222
def s_8 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_8 : Nat := 0x20222
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

def m_9 : Nat := 0xaa00aa
def s_9 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_9 : Nat := 0x2002a
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

def m_10 : Nat := 0xf0f0
def s_10 : List Nat := [0x5050, 0x3030, 0xf0]
def g_10 : Nat := 0x1070
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

def m_11 : Nat := 0x4444444444444444
def s_11 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_11 : Nat := 0x4044404440444
def bds_11 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_11 : KnownBin bds_11 := by
  intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_11, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_11 : Nat → Nat × Nat := fun _ => (0, 0)
def l_11 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 0 (dagTraceF m_11 s_11 4 f_11) l_11 0) s_11 4 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_11 g_11 bds_11 0 (dagTraceF m_11 s_11 4 f_11) l_11 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_11 : LowerBin m_11 s_11 g_11 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0x2222222222222222
def s_12 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_12 : Nat := 0x200020222
def bds_12 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_8, s_8, 4, g_8)]
theorem kn_12 : KnownBin bds_12 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_1
  · exact lb_5
  · exact lb_8
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_12 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 43 (dagTraceF m_12 s_12 6 f_12) l_12 0) s_12 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 32 (dagCheckNodeF m_12 g_12 bds_12 43 (dagTraceF m_12 s_12 6 f_12) l_12) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_1 : treeBlockF 32 43 (dagCheckNodeF m_12 g_12 bds_12 43 (dagTraceF m_12 s_12 6 f_12) l_12) = true := by decide +kernel
theorem nj_12_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_12 g_12 bds_12 43 (dagTraceF m_12 s_12 6 f_12) l_12) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_12_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_12_1 h1 h2)
theorem nc_12 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_12 g_12 bds_12 43 (dagTraceF m_12 s_12 6 f_12) l_12) i = true := nj_12_1
theorem lb_12 : LowerBin m_12 s_12 g_12 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xa0a0a0a0a0a0a0a
def s_13 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_13 : Nat := 0x200020a0a
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

def m_14 : Nat := 0xc0c0c0c0c0c0c0c
def s_14 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_14 : Nat := 0x4040404040c0c
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
def l_14 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 0 (dagTraceF m_14 s_14 4 f_14) l_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_14 g_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) l_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x303030303030303
def s_15 : List Nat := [0x101010101010101, 0x3000300030003, 0x30300000303, 0x3030303]
def g_15 : Nat := 0x101010301030303
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

def m_16 : Nat := 0xaa00aa00aa00aa
def s_16 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_16 : Nat := 0x20002002a
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6), (m_9, s_9, 4, g_9)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_2
  · exact lb_6
  · exact lb_9
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_16 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_16 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 43 (dagTraceF m_16 s_16 6 f_16) l_16 0) s_16 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_0 : treeBlockF 0 32 (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_1 : treeBlockF 32 43 (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) = true := by decide +kernel
theorem nj_16_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_16_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_16_1 h1 h2)
theorem nc_16 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_16 g_16 bds_16 43 (dagTraceF m_16 s_16 6 f_16) l_16) i = true := nj_16_1
theorem lb_16 : LowerBin m_16 s_16 g_16 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xcc00cc00cc00cc00
def s_17 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_17 : Nat := 0x40004000c00
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
def l_17 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 0 (dagTraceF m_17 s_17 4 f_17) l_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_17 g_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) l_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xcc00cc00cc00cc
def s_18 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_18 : Nat := 0x400440044004c
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def f_18 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_18 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 64 (dagTraceF m_18 s_18 5 f_18) l_18 0) s_18 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_0 : treeBlockF 0 32 (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_1 : treeBlockF 32 64 (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) = true := by decide +kernel
theorem nj_18_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_18_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_18_1 h1 h2)
theorem nc_18 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_18 g_18 bds_18 64 (dagTraceF m_18 s_18 5 f_18) l_18) i = true := nj_18_1
theorem lb_18 : LowerBin m_18 s_18 g_18 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0x33003300330033
def s_19 : List Nat := [0x11001100110011, 0x3000300030003, 0x3300000033, 0x330033]
def g_19 : Nat := 0x11001300130033
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
def l_19 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 0 (dagTraceF m_19 s_19 4 f_19) l_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_19 g_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) l_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xf000f000f000f00
def s_20 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_20 : Nat := 0x100050005000f00
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
def l_20 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 0 (dagTraceF m_20 s_20 4 f_20) l_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_20 g_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) l_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xf000f000f000f0
def s_21 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_21 : Nat := 0x10005000500070
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

def m_22 : Nat := 0xf000f000f000f
def s_22 : List Nat := [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f]
def g_22 : Nat := 0x500070007000f
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
def l_22 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 0 (dagTraceF m_22 s_22 4 f_22) l_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_22 g_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) l_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0x5555000055550000
def s_23 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_23 : Nat := 0x1115000015550000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
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
def g_24 : Nat := 0x200000a2a
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
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
def g_25 : Nat := 0x4000004440000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x333300003333
def s_26 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_26 : Nat := 0x111300001333
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
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
def g_27 : Nat := 0x105000005070000
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_27 : KnownBin bds_27 := by intro b hb; simp [bds_27] at hb
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp [bds_27] at hb
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_27] at hb
def f_27 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_27 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 64 (dagTraceF m_27 s_27 5 f_27) l_27 0) s_27 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 (dagCheckNodeF m_27 g_27 bds_27 64 (dagTraceF m_27 s_27 5 f_27) l_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 64 (dagCheckNodeF m_27 g_27 bds_27 64 (dagTraceF m_27 s_27 5 f_27) l_27) = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_27 g_27 bds_27 64 (dagTraceF m_27 s_27 5 f_27) l_27) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_27 g_27 bds_27 64 (dagTraceF m_27 s_27 5 f_27) l_27) i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f00000f0f0
def s_28 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_28 : Nat := 0x105000001070
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xff000000ff0000
def s_29 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_29 : Nat := 0x15000000570000
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_29 : KnownBin bds_29 := by intro b hb; simp [bds_29] at hb
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp [bds_29] at hb
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_29] at hb
def f_29 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_29 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 64 (dagTraceF m_29 s_29 5 f_29) l_29 0) s_29 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 (dagCheckNodeF m_29 g_29 bds_29 64 (dagTraceF m_29 s_29 5 f_29) l_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 64 (dagCheckNodeF m_29 g_29 bds_29 64 (dagTraceF m_29 s_29 5 f_29) l_29) = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_29 g_29 bds_29 64 (dagTraceF m_29 s_29 5 f_29) l_29) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_29 g_29 bds_29 64 (dagTraceF m_29 s_29 5 f_29) l_29) i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff000000ff
def s_30 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_30 : Nat := 0x570000007f
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x5555555500000000
def s_31 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_31 : Nat := 0x1115155500000000
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

def m_32 : Nat := 0xaaaaaaaa
def s_32 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_32 : Nat := 0x20a2a
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
def l_32 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 4 f_32) l_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_32 g_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) l_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xcccccccc00000000
def s_33 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_33 : Nat := 0x4044400000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
def l_33 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 4 f_33) l_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_33 g_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) l_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x33333333
def s_34 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_34 : Nat := 0x11131333
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
def l_34 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 0 (dagTraceF m_34 s_34 4 f_34) l_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_34 g_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) l_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xf0f0f0f00000000
def s_35 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_35 : Nat := 0x105050700000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_35 : KnownBin bds_35 := by intro b hb; simp [bds_35] at hb
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp [bds_35] at hb
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_35] at hb
def f_35 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_35 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 64 (dagTraceF m_35 s_35 5 f_35) l_35 0) s_35 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeF m_35 g_35 bds_35 64 (dagTraceF m_35 s_35 5 f_35) l_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 64 (dagCheckNodeF m_35 g_35 bds_35 64 (dagTraceF m_35 s_35 5 f_35) l_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_35 g_35 bds_35 64 (dagTraceF m_35 s_35 5 f_35) l_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_35 g_35 bds_35 64 (dagTraceF m_35 s_35 5 f_35) l_35) i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xf0f0f0f0
def s_36 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_36 : Nat := 0x10501070
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
def l_36 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 0 (dagTraceF m_36 s_36 4 f_36) l_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_36 g_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) l_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xff00ff00000000
def s_37 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_37 : Nat := 0x15005700000000
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_37 : KnownBin bds_37 := by intro b hb; simp [bds_37] at hb
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp [bds_37] at hb
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_37] at hb
def f_37 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_37 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 64 (dagTraceF m_37 s_37 5 f_37) l_37 0) s_37 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 (dagCheckNodeF m_37 g_37 bds_37 64 (dagTraceF m_37 s_37 5 f_37) l_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 64 (dagCheckNodeF m_37 g_37 bds_37 64 (dagTraceF m_37 s_37 5 f_37) l_37) = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_37 g_37 bds_37 64 (dagTraceF m_37 s_37 5 f_37) l_37) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_37 g_37 bds_37 64 (dagTraceF m_37 s_37 5 f_37) l_37) i = true := nj_37_1
theorem lb_37 : LowerBin m_37 s_37 g_37 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xff00ff
def s_38 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_38 : Nat := 0x57007f
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
def l_38 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 0 (dagTraceF m_38 s_38 4 f_38) l_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_38 g_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) l_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xffff00000000
def s_39 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_39 : Nat := 0x155700000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_39 : KnownBin bds_39 := by intro b hb; simp [bds_39] at hb
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp [bds_39] at hb
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_39] at hb
def f_39 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_39 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 64 (dagTraceF m_39 s_39 5 f_39) l_39 0) s_39 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 (dagCheckNodeF m_39 g_39 bds_39 64 (dagTraceF m_39 s_39 5 f_39) l_39) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 64 (dagCheckNodeF m_39 g_39 bds_39 64 (dagTraceF m_39 s_39 5 f_39) l_39) = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_39 g_39 bds_39 64 (dagTraceF m_39 s_39 5 f_39) l_39) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_39 g_39 bds_39 64 (dagTraceF m_39 s_39 5 f_39) l_39) i = true := nj_39_1
theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xffff0000
def s_40 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_40 : Nat := 0x15570000
def bds_40 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_40 : KnownBin bds_40 := by intro b hb; simp [bds_40] at hb
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp [bds_40] at hb
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_40] at hb
def f_40 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_40 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 64 (dagTraceF m_40 s_40 5 f_40) l_40 0) s_40 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeF m_40 g_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 64 (dagCheckNodeF m_40 g_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) l_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_40 g_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) l_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_40 g_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) l_40) i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xffff
def s_41 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_41 : Nat := 0x1f7f
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
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
def g_42 : Nat := 0x200020a2a
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 7, g_12)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
def l_42 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 0 (dagTraceF m_42 s_42 7 f_42) l_42 0) s_42 7 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_42 g_42 bds_42 0 (dagTraceF m_42 s_42 7 f_42) l_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xcccccccccccccccc
def s_43 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_43 : Nat := 0x4044404440c4c
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 6, g_18), (m_11, s_11, 5, g_11), (m_14, s_14, 5, g_14), (m_17, s_17, 5, g_17), (m_25, s_25, 5, g_25), (m_33, s_33, 5, g_33), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4), (m_7, s_7, 4, g_7)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_11
  · exact lb_14
  · exact lb_17
  · exact lb_25
  · exact lb_33
  · exact lb_3
  · exact lb_4
  · exact lb_7
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_43 : Nat → Nat × Nat := unpackForestF 0x25109b2714593ca6c9c1140169f25b4e92d1c002d2e454a12295c914a848a172450a000b478f09fc784de4107b1e1358f01fc780de3d27b1e035005a1c7293e3948600a4e8dd1e00292e3505b191258cc96c640940148713349899a1c564fe2b26f1583f8ac1bc4cd062907b1312789c9ec4c09c014851194588c22c3897a204a51002d87092c3a94a1d25b0e0250051dc341321728b0c14c85c22c1c97a1504909a5284c16c1c4961124907a5283c96c1c0940146705a5c82c924108ee094b904233004a7c0c4d20069701a3480c9a400d0e0029d0013c004a5bd2d71e96a2fd23b7ec923f48cde96a0f4a507da303ec9b1e9476f8c607c5363e4d41f1248f4a337b895bdc48de90b8f523b7ac923d48cde90a0009477991a3cc4d1cc696f2134731a1bc40d5cc29cefa3b77d19b98061dd284e601576c9239a8edcd466e683f7341dbab141d5480e6837749a03a48c1d0288e803c73419b9a0bdcd046e6014004a1b5714dab6bee3b5171c22b56d79c5268d5b53705aeb824d9c106ad5b526ad2f356949bd4bad595e6dc9b36e055b8072dc0316dc0a356549ab07eda14c6ac1db560ddaf6a4d7a5e6bd293560d5ad078d61446ac198024fda7030d381569c0a0024eda506ad04526812f343179a14bcd004d0049bb385399c278ce01500499b34115974bccc25265c128024bd9502a009236492e32409186476c825c61919b1ad718d068c313f62a283141318626ec3a5c61c1230c4bc0109ec20345f9a5b024d181068bf3435f8272fc0f001096b3b5c59da8af08ed79048bc23359da82ce941748c0ba26c59d1dadf1816f4d8b83505bc122ce8cd6c256b612359cae2d08ed69048b423359ca800211d64268b20344e1a5ac40d138686af94457c2227093d5bac0ad95c56c2e27091d58268ac0344e11faac4d53809ca9a3b54d19a700b14c49ca6242530a729c4c14c28ca613e4e013294091394769ca3351c1a2724fd39276a1450509202841313926e9fb404fd1827a9113d2789c9334ec122724bd392469c02400421a1114d086be99b514cca2a10d7931068843534b5aea5a4d52d06c843524212f210949082be9314c498a224c051082a68414f420a1a440d10827e9024c4209da104dd158bc8ac524552f22a949152bc8c014454a922a4f9152648413544ca6222911110288413343d2ea101790906c848164281ca140c509028840520041fa080b10404c820240041da044d4f38a479a5e3ccaf9f7580fb2b87e0303ec0a1e654cf46bc7a3523d12f1e8578f50287a1523cca68020dcf128874a4f3bc921d290ce909c7483c3a8a71d4508e904c0083339ca29b8978dc2be7193438c0a1b854cdd6bc6eb52374af1bc050dd2a46e125004179b4098010466ba3435c9a190d2cd42686a034321a19a44d8c849c6414e3392219c570c809e65a5c32ca619011cc94686403f0040f98a4d0c50685ab4b3091a1840d0b5686601442d52797c570b548e5e1342d51f9740d8b529c5b94d2dca296a138b504c0081b2c12c160950b02a85805409e2f956920ab488559442ac2204f14c276bc5223829d201488d0a42685203409da99449209c8a24e23a27da01388d89c26c4e03609da912e8e0974684b93425c1a04ed2c934704a25024d1a04ed0c274be4834909d2f11d180274a642c51215a89128d88906c42b50214ae90c9408529c13a5209d278f4d787a6a43d25e1fdae0f49487a26c3d1351e81b0f40d42749c3bb5c1dc9e04e92c74ac03a35009d238e1140706803814c1b9aa0dc530274862dc5e1a9220d41105b8a43414416daf0cb140652682db5216da48b6d045b2bc3035016ca90b65345b27a2e35016c9a84e9082747e13a33155280ac500550881394f12d2f0969484b2bc2825012ca90965244b2822583a12c1b04e538484802405c09ca388a5384525c1394210c1a04e4fc3f4a0201300fca204e13c334bc19a520ccaf074940332a4199490cca0866138330841983a0cc1b04e1382f4b817a400bcae04e11c2a29c151420a8270540b8270841413409c1f80205c250680134b0851a0424d0210680134307c120128ec1b2500e14006c920128cc190680493f0249d829140144800a04c0249b822d001146007a4403c9e0124cc0d0480492f024918140f80903c011240101c8080c4040520202100c0a004138010260001f 10 11
def l_43 : Nat → Nat → Option Nat := unpackLinksF 0x4360219870cc08601c2b1615810ac08501c280214010a00850042802118b080383c141e020c8b0583828141402078b004e802040101fc90fe407f00bf801fa86fd407e41bef0df780fbc07de03ef01f780fbc07d42bea01f386f9c07c81bdc21ee00f7007b023d801ec00f4087a003d001e410ee4f77203b805dc00edc176623b301d902ec8075443aa01d482ea4074243923dc900e480720139001c782e1c870e038605c300e180708138401c200e004700037e09bf00df806fa0b7b09bd80dec06f6037711bb02dd806ec037409b78adbc06de036d09b680db406d80b6a09b110d8416c2035d11ae80d6836b4035809ac00d6006ac135505a78cd3c069c0b4e01a682d3016960b4a05a308d18068c034409a200d0436800b40019b92cb4a6561329099480ca4064a2325019184c8c06460323018f88c7036321b19018b84c5c062e0317018b80c5426241b0e118682c28360e1b07018380c1c05f662fb017d02bd845bebadf016f80b7c05b81adc016c86b6015b002d8016792b1c85881ac4016008ae8657402b8095c00ac8655832ac015582aac055602a9095480aa0155002a8015208a90054802a2095100a8805401298214c00a5c152e0297014a84a54052a0291114880a3c251e028f014702a302518028c014600a20450e0a87014380a1425002a800140009f824fc027e013e829ec24e642720539009b844dc026b0d35029a804cc226601328299404c2226005300097434ba025b092d8096c04b21259012c0295c14ae0255092a02938649c024d05268093404980a4b0525029241492024511228091404861243012006900047e0a3f011b128b0a45412280914008a00448222401110488804440222010f0886c34301a14110a0085004260a0f11058881c440e02031101027fc33f819fc00fe007f003f801fc00fe007ec13f601fb00f7987bc03dc09ee00f5087a803d011e800f4007a003d001e608f186731739801cc00e600724339201c60ce28270c238601c300e180704237a21bd00de806f4037a01bd00de026cc935641ab00d38869c034621a00cd0006800340019c10cb0c6580328119208c900644131c198e00c700638031c018d04c38c6046302018004c00060002fc117e00bf005f022f8017a08bb085d802ec017210b9005c802de196f00b70259882cc016600b20459002c8016208b10057842bc015b0cad8056812b4015808ac0056002a8215010a4105200290014800a40050c5284094200a082500126e49331099804cc026409320099004b4525a012a0c95004a802520928049382470b238011c008e00470022c3115048a02448221c210d04868042052100106088300418020c010600800c400020000ff047b903c851e208f10078803c401e008ef0477803b811dc00e428718238c01bc28dc086d0434c71a408d1046880334419808c6186300318018c00c30c6180308118400c2005f862fc017e00bf005f802f8117810bc005e002ec115680a80c5382298114c00a5045106288014208a1005080280114000a0005000280012c5096004b0024841240092004708238011a088c04460022c1110188800438221c010e0086044300218010c008600430021800f8507c003e001f000f02078003c001e000f00074103a001cc10aaf05404290414410a008500026081300096084b00258012810901048002382114208808430421800fc407e003f001e840f400722039001c020e0007000360816140b00058002c0016000a0404e08231000c40001 0x25109a590452c40ac9e534b228a580169322f47497a5028b270452bc0bc98d3a304a125a3892528490572472a12305c91428390db22e4c0e11448b5303844f1c529ce113e9041e95a0d4ac02a9a36c8b13025a1122b4c09683c8f49e95a4d53109c9683e2ac0b47297a2f4a515250728a7c864fdc027b211379009aa6c13e3f07e9603d8f81bc780d4aa02f1bb4e8e927c7290dbf25ed19274ac17a0009ca902f1ba3c8d41694c094a502b1992d2989294805a3424b1902528c0bc5c4fe2d26f1603f8ac1b94205e2907a4f0352740ac4e4f49e26a4e0168c1a4c5ed0e2a682df13f8a093a540fe2604e4d817830a6c485159309b118458312f44294a0b2bcf395288016932094d803a4c01564d2f43c94a1d25a4c9256482f2ca148c60344b8168892f41457e052b6fa957794a9c3e495910bec185b5cc2bac614e1c04a6b01f3100d92c05c240270d04c860a64125361928ac804d85c22c2a092094bd0a252810ad3e255a1305a4982530c0c84604611248c825e8412941e4b49324ac105a5bc2b1a8078220250b25e820afc0456df02aef195384892b1e17d800b6b705758429c1c094d303e6081b2480b84004e0c4b9059248252e380d060a477042336f09f11e1352907e7f83739417c0c4d20446901934815a5c04d0e0129d0013c7dd24be8905fb248fe23b7e919bef181f64d8f786c7b0303e4491f26a0f58507d2303e69b1f1248f706c7a8303de4adee246f59247b11dbd48cdfe6b8feb517e5a83f0941f5476f82337b42e3d2141db028f3a347989a3c0061da028f213477c0c3b20512807af10357811dbbe8ccfc088dd24e4a0a73ba5092609c7d84638c1f3b649118268dca4c74c203a40c1d68a0eaa403d4a63a20c1d3680e92306e1263a2511d00786f1247691dbb28cdb727cec03f75c1dba80ddcf066e702f73411bcad2de3686db24e784a724a13cfa08e7103f7780c3b8055cc028e446c7149a386d81bd2d8e1c5d721a8b1c135c708ae1c6c7149a386d75c226c4083d7041a9000b5b004a298151f81eb5e0d45202adea5d14426b720e5b8062dd9366e80ab6e050576b88b1346d0240f6111ad068da14c130920f41107b078d603012c0a31cd79b16a4d825e6bd2931a179600a49104e3c4210f60f83107a6001a1540b35a0f1ac2885c05c0c4261d6091ca8a6e4b5f719af388d4dc06a4dfa5e6f929378579b62a4c605f57829a4813cf0086da83f1e41eb660edb206ed70356ac199a2074bf0362a0171280ab52061a802ad381457428b160f5a506ad083d68a2f317149a14bc1894d1f0a2b141795c0a45f01a1200b349149a34bccf14d6242fab414da009a5e81b11c0b8620f47a06a230150c4a70ee5091109c77842678a733a4f12309e7704311012b380558809acd0456212f330949870bcac8522f00d086059994bcc305f55c29b2e094bb036210176540ab2697192048c825c639ae102d40512b8c683462e28314131884b8c38244b1a0b228ed8f4664794d6309fb124dd8625e8703e6101a3044d181068c1b4b601a1afe1397e078baa495c920af20917a476bc2335d6302e89b16d2d8b51605c0122e0d41690a0b94605c5362d85b1682c0b78245b495ad848d69048b523b5a119af8d717b6a2bbb505d9282e68ed6e466b595c59ca829405165268b20345501629209162068a982c5201228e05160288a884c57c2229e09142028aed60570ae2b61714d0489d8145649a2b00d14c048a893d5589aaa88ed53466a724451c1a29c4c1420989d824545272a09094f29ca69465309f2181394a048a383442c262805013f260a245050d2027c4c142098a03404fd1827c9113d2788504c4ec122928ed48466a313f5149da824dd3c2669d12f4e491a120f963696b0b4357927ab491d5747e8414e554272a40b14b04c9c0244d2362620d12f6c08786c4be2ea68d451d29a999454be362620d12f6ba4093d4b89aa5a0d88025a8d9250f40b0fc4f51a26a1e016475ae102d41192681d85c4609a22e91128298939444980a062d0116288910340d80a22a910312981a8244440a082d71202903e9444881a2264d1204983e1440d0120fa4f112260198144600a23b1791c8a48da5e46929232579172a43e94e0c4a6a2c4f9152646781d0fc0aa26531124886715c0c4a62220510f4ba1d84d42c1ca140c50d06c860164240a26d14d356be9935e4c1a9a58d492b4bc952524a4afa4a54d2429e919434849f8f24f51f2768f1374509aa204cd0e0bc840523340f9720683e02e190164181620a099040487f1513e09ea044d4f727a7c4503d8a61ea530fc0607f5603d12e1fa570fb0287a8143e5af1f0d48f74bc7b15e3d0a90620f47a06a6601d0bc0aa03149004bc7f95f3e8a99e6534ed09a6501f0b80b9e25102d2481884c3ac120584d0ef248750341dc120624f47c26a158160c5270ee908eb29c751423c1279dc90c2924c7684e3b01e1d2098e129a739453852e1be490de2486ea343909a1c6050de02870b5e381a91be578dd2a46481d0a00a9cc978e52be711533709299007c2702e6d0263611a1ae4d0d52686a0343489b08c054ce09a658450c41e8f40d4cf4886715c0c4a6056050cc4b83d15c32ca61928d0d669669b43345271a0538cd09e650473201f96a054c62686283430d1a1840d0c02885c05c0c42608c090be2b83e05c2dc261784d0ba06c158162e0a696e5143127a3e1350c5270ee9084629c1584e311a5982d0cbf49e5ea472ed1f972538b609c5a8262cd2c1649506c480589542c02a144d406b28035140285b0118980694a040a4c2b92415a9105f480561442ac221008f8674642993e0f41f14e9008b4c0542382991a14a4d0a406833250289240c09009f68045150224a81431448e4a2442501f9270c8908a04744f236148a713a4d83c09c4e03618d281348e0994684c13425c1a03c0401d0400e01025128036040624a04aa3824d1a034040874c043c5d241a4902d045127c1d83e23a3010edb05049c45236218a70c05083a09c44836219281191448b6a24435013d2710e5748529c2f9420e4270f09605e4a01f944154220300407f4a03fb5c1011e0ac930826bc40b521dda70bcd34804bc3f2521f49b0f84d47b06c3d0351c0a20f0d704e4b83b93c0e02e02e080724a00b0101c52002a04075ac03a3500c52e0de9002f2b82405c04c0802408011040394501c5a00e05301004007810179ae0ded504d4b83714c0dc2e01c080666a035a441a8220d0510668a0301501949a0c0d40404882b044171a80d9178698a433b5e191a90c6d24626822ba4d125228c25785f2a41894e178a68ba4f45b26a2084d0c0228504d0430680601002c100ac110562802ba500c5260aa110502a02825014d2f0a4948512bc27952138a489a5043609c168421301d0960d8314b824a40118ae0901704629c2292e0d427058108430682024410098082940314981f9440e8a80749403d4bc1e2520ecaf072548382921b9410d82706a10834074198360c52e0609002f2b81585c0b4a70585082b09c1502e0a09a15f17caa8a654b5e28da9936d4896696493432452f91e9788d4a64225220d278f29387649639a471b5218b49085947e2c233150a78945384728e221421089f87c13c3209c170470a42104e0fc080200f8140789204a0d01b2480d92408d1a0444d01a2481083407c120385001d2500d9240641a00e13005028091400449802d140154800813005026024d00114600824403c9e00c13004038068240281f0080c81e4760d2330609f82e4ec1326e071330309781648c0307c0481e01c1c80c0c4050520202100c0a048d2c20686041240082749ad3e4a697223478eda1c7093a3649718a43895214368ee0d4670394f7fca5bd051dcb286d513f6989db3e4dd9b266cb12f65091b0a13d7d096b30474dc21a0e0fd03076790373a0199b60bcd90466381f2d00d84c05c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 594 (dagTraceF m_43 s_43 8 f_43) l_43 0) s_43 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 64 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_2 : treeBlockF 64 96 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_3 : treeBlockF 96 128 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_4 : treeBlockF 128 160 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_5 : treeBlockF 160 192 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_6 : treeBlockF 192 224 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_7 : treeBlockF 224 256 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_8 : treeBlockF 256 288 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_9 : treeBlockF 288 320 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_10 : treeBlockF 320 352 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_11 : treeBlockF 352 384 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_12 : treeBlockF 384 416 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_13 : treeBlockF 416 448 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_14 : treeBlockF 448 480 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_15 : treeBlockF 480 512 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_16 : treeBlockF 512 544 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_17 : treeBlockF 544 576 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_18 : treeBlockF 576 594 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nj_43_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_1 (fun _ h1 h2 => treeBlockF_at nb_43_2 h1 h2)
theorem nj_43_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_2 (fun _ h1 h2 => treeBlockF_at nb_43_3 h1 h2)
theorem nj_43_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_3 (fun _ h1 h2 => treeBlockF_at nb_43_4 h1 h2)
theorem nj_43_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_4 (fun _ h1 h2 => treeBlockF_at nb_43_5 h1 h2)
theorem nj_43_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_5 (fun _ h1 h2 => treeBlockF_at nb_43_6 h1 h2)
theorem nj_43_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_6 (fun _ h1 h2 => treeBlockF_at nb_43_7 h1 h2)
theorem nj_43_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_7 (fun _ h1 h2 => treeBlockF_at nb_43_8 h1 h2)
theorem nj_43_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_8 (fun _ h1 h2 => treeBlockF_at nb_43_9 h1 h2)
theorem nj_43_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_9 (fun _ h1 h2 => treeBlockF_at nb_43_10 h1 h2)
theorem nj_43_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_10 (fun _ h1 h2 => treeBlockF_at nb_43_11 h1 h2)
theorem nj_43_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_11 (fun _ h1 h2 => treeBlockF_at nb_43_12 h1 h2)
theorem nj_43_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_12 (fun _ h1 h2 => treeBlockF_at nb_43_13 h1 h2)
theorem nj_43_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_13 (fun _ h1 h2 => treeBlockF_at nb_43_14 h1 h2)
theorem nj_43_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_14 (fun _ h1 h2 => treeBlockF_at nb_43_15 h1 h2)
theorem nj_43_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_15 (fun _ h1 h2 => treeBlockF_at nb_43_16 h1 h2)
theorem nj_43_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_16 (fun _ h1 h2 => treeBlockF_at nb_43_17 h1 h2)
theorem nj_43_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_17 (fun _ h1 h2 => treeBlockF_at nb_43_18 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := nj_43_18
theorem lb_43 : LowerBin m_43 s_43 g_43 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0x3333333333333333
def s_44 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_44 : Nat := 0x1111111311131333
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 7, g_12)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
def l_44 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 0 (dagTraceF m_44 s_44 7 f_44) l_44 0) s_44 7 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_44 g_44 bds_44 0 (dagTraceF m_44 s_44 7 f_44) l_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xf0f0f0f0f0f0f0f0
def s_45 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_45 : Nat := 0x1010105010501070
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 6, g_21), (m_28, s_28, 5, g_28), (m_36, s_36, 5, g_36), (m_10, s_10, 4, g_10)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_28
  · exact lb_36
  · exact lb_10
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_45 : Nat → Nat × Nat := unpackForestF 0x4f9499f09202d3e522f4a45d9b4a128d5a651c4a34e97031284e654164a03901696eed39dda4bba528969d12d262497449228905d1448224113ba50872a0ee57a15283b952772a304d39dca83f9507f0a0ee179ed283d95c7b2a0ee149dc28bc34e770a002d1dc9ae39250722a0e4141522b37b5c6f4a0a915551af2a35d5469ca8d35511d3212e64244c80b994903202254470c48e1509d2a13954270bc4a1509b2d2385a270b44d1501d2a03954070aa4a154142a03601686a28e1441c2794e4f28c0252d24a7249464925a92069240c009433a8bc75148e92d1d15e4227884060e8ad1d1563f03074548e80d1db4e3b68474060049d95c5e2b8a456948acaf1595a314a062540c428159562d2785a4b0b40c159522b25a024cca11c141382609c4c11804259004e2008c400b480161001d010862317846290895a110bc320f064160885a110ac2c0b044290882d1269c24d0844160083b028bc0514808a90105e020b41094020a804050020ac080f010160201c020a40407404198001f 8 11
def l_45 : Nat → Nat → Option Nat := unpackLinksF 0x898226081c204180860207f0dfc07d8df607d05f407c85dac750dd217199c607181c607105c407101c216ca1b206b0dac06911a406901a026801a00668d9a066819a0649192064818e259d1660598166059815e457815e056895a056815a056815245481501540150053854645181403500140050013a34e813a04e813434d013404d013404b8cff83f80fe03e0cf803a9cea03a04e803a00e8035a4d413484d013384ce03380c833200c803184c603180c603088acb2b00ac02a84aa02a80aa02a80aa0290ca402900a40278c9e023248c0230086321807871e007611d807601d80649188460117845c117005c0158c5601580541150054015005020eac3a00e803810e003800e003800e003230c803200c802c30b001a900b0001 0x131179b22eceb5a9c6b324d59b1a8c93469a68b40524f8a0a3939382633e12454208f0390f062ead11c1aa4da50322a010142651c17138040712e06254164ec5e9c8bb23155aa294d356916ab30d39a9a6cb13934263280e42c18c7a50822a0f014239284745c8f6b90e57214a84005c7d0a114082289047b4e8e692e8d09bda0c692e8c245160ba24111945c872a0f814209ae42a507f0b8f614209a739b42088b900541fc283c35c7d4a0f8571eca83c34e7268523179ae2ec935e6d6bb24d3a45a4b8b426e6832094a21284315e412b30854a0ca8c09507e0bc30165e8293c851770a0ead71d12839950720a0e0d71bd28311385e268b80e1581a3282065240d04b99c913302e64044c48e16c1c2a8342e478bc4a168142e2385b270b44d0111e2b12855050d9175aa2d38c566e8aadad79b1aeb5b4e6a69ad28e98d1c2314937282c24e9809caf9385d26c584c474248704159074b00e55c1c2a03603062a48e0b89c288384b4a48a92940a72094a4f28c685092c96991404b4b46c90934a71f14a4c28c585092c96a501a4903078060ec0c171242e290864f0c896210183f03078d38eda123c5e468a48a968ad212215e412b480558f8a91592d3d03474060c89219a50322a062140bc9e1712c2d03071178de291b2522b4946a578d0ad181562c2a4564b4a51c14138040704054870a51384e180944c1182c211001d080804056834a11204e15094461180c211102d21058400744c160902c0402808120681e0c82c080382c0b04da7093421e8bc3b14870ad011421b0bc301685c2b0a8521405a220b0080e840140a4a01254020280303c05058080703e2f074520d2a404528302f0585a070ac06148080ecf34f93696ecd1d4da1a714b48286724eca8999284b1f086200ec04198001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 161 (dagTraceF m_45 s_45 7 f_45) l_45 0) s_45 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 64 (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_2 : treeBlockF 64 96 (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_3 : treeBlockF 96 128 (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_4 : treeBlockF 128 160 (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_5 : treeBlockF 160 161 (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nj_45_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) i = true := block_join nj_45_1 (fun _ h1 h2 => treeBlockF_at nb_45_2 h1 h2)
theorem nj_45_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) i = true := block_join nj_45_2 (fun _ h1 h2 => treeBlockF_at nb_45_3 h1 h2)
theorem nj_45_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) i = true := block_join nj_45_3 (fun _ h1 h2 => treeBlockF_at nb_45_4 h1 h2)
theorem nj_45_5 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) i = true := block_join nj_45_4 (fun _ h1 h2 => treeBlockF_at nb_45_5 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_45 g_45 bds_45 161 (dagTraceF m_45 s_45 7 f_45) l_45) i = true := nj_45_5
theorem lb_45 : LowerBin m_45 s_45 g_45 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xf0f0f0f0f0f0f0f
def s_46 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_46 : Nat := 0x105050705070f0f
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 6, g_27), (m_35, s_35, 6, g_35), (m_13, s_13, 5, g_13), (m_14, s_14, 5, g_14), (m_15, s_15, 5, g_15), (m_20, s_20, 5, g_20), (m_22, s_22, 5, g_22), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_27
  · exact lb_35
  · exact lb_13
  · exact lb_14
  · exact lb_15
  · exact lb_20
  · exact lb_22
  · exact lb_0
  · exact lb_2
  · exact lb_3
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_46 : Nat → Nat × Nat := unpackForestF 0xad04dab945ac14dab84500b4f00b4ba7a5ca7a50a9055a795da8155a785d00b47a1238a1234a583da1135a402fa4027a1134a313da1035a182fa1827a103400b43a004d9e9459f14d9e84500a4f00a4b9ab5c9ab509c0559a95d9b1559a85d00a479424c942449882d941259701f97017941249612d940259481f948179402400a439303d919359213d9183500a3f9082d8f1258f92d8f02500a3b00a37893448c95d8c85d892568b25a8b02d8912589a5a8992d8902500a33880450094f873547eb5b7eb5385a547ea5b7ea538226c8385c8226482254821247ea337e85f7e85d7f46c7f3607f2607e857009477d85d7ac567c85d7ab567b4567b35a7a8350093f798257823178a317804d009377705d743567605d7425674b5674a5a740250092f7302571a42722427183d0092770c5e6f9556f9450084f6eb545d35b5d3536d2545d25b5d25369a6c6b15c69a6469a54698245d2335d15f5d15d66c6c66b6066a605d15765c5e5d14d6415c6406c5d1476294e6285e5d1456036c603646016c600345d13f5da6c5da645d96c5d8245d12f008475c15d564565b15d5635659b6c5986c561575614556c5a56c5656b5656956561350083f551254fa31542414f94d4f93d5035050240519405015c509305003c4f927008374e95d48b564d95d48a564c26c4c06c48957489354935a493564925649156489250082f47925422424535045240459304505c421474334243a30431464213d4212d008273fa583fa543f9543f8540145f0145b3cb6c3cb603ca6c3ca60014573934839344392483924439144390440145336a5836a5436954368540135f0135b33c6c33c6033a6c33a60013573035c3035430238302343013430034013532ea482ea440134f2d2382d2340134b01347294542b344292382923429134290340134327954278540125f26b6c0125b259560125a2246c224602236c223602216c2206c012571ac5e1ab5e1ab521f25c1f2501aa5e1e35c1aa521ca501c9501a95e1b2501b1501a85e012561995c16b641695c169541694c169441693c01253143481434414144140440124f1334411b5c1194c119440124b1015c1005c012470f14c0eb54012430c35c0c3540c1340c0340123f0b34409b4c0995c099540123b0814c0804c012370713c06b440123304949049410485e0115601949019410185e018460184401056008170001f 9 11
def l_46 : Nat → Nat → Option Nat := unpackLinksF 0x8501088e11041c382c70506090c1018201028e05040437ecefd05f90bf207d86fb01f603e827d00f88df103e207bc4f41de803ca37940f10ddf1bbc17742ee05dc03b237640eb0dcf3b9c17342e681ca1b9407280e409c8038a37140e281c3137876f00dd09ba037026d46da81b3136606c44d70dac135616ac0d581a5334a06940cea19d033a06550c52d8a031026200c38587030e06182c30186030c06142c28185030245f86bd117a02f215e02b995647ac805884b1016012c005800ae11572aae05506a98551129a45340a5894b029225240a481452280550009e8d3c0a7424d889b01350a6a04cc49981320a6404c80988531026204c40980530026004b08948d25224a0490291851e2a3c047428e811d0234346808d01171a2e045c08b81170226444c08981130226043c8803d0001fc23f807e08fc01f803e087c00f801f003e007c00f421de53bc0760ceb09d223a407480e711ce039827300e509c2437486e80db11b6036446c80d901aa435406a80d501aa035406890cc2998032466480c7118e031826110c10982030025f08be017442e805d00ba017402d885b00b6016c02d805b00b2216402c805900b2016402c805618ac015802b005600a8215002a005400a80150029085200a40148029005200a4013c627804f009c1138027004d08990930126004b8497012e025c04914920124023884684892112021c4438087010e021c043808700fe81fc03e887a18f401e803c087800ea31d403a807310e601cc038886940d201a0234006800d001a0034006040c0017c22f805f00b4516802c085800b0015462a805500a43148028845008a0013c227804f00945128024084800900114622804500843108020844008800100020003b287600ec01d803b007600d8a0d7001c8001 0xad04d4084540015ac14d409453f816ac945ab8453f0173e8173e0173d8173d05da90555c03d3d15da81557d93daa25ca9a50a895d7d13da785d5b83d3c0173b8173b017a583d3a03539815a482fa4027a313d3a13539016a202fa1827a6a38a6234a5135a3934a2835a103438817a004d37845370159f14d37945368169f9459e845360173581735017348173405d9c0554e82d3415d9b1557712d9d35c9cb509b95d7692d9a85d4e02d3301732817320179882d31025308159781f970179612d31125300169501f9481799a4c99244981259692495825940242f8179303d2e8359213d2e93592935918352e0179082d2d0258f92d2d125901258f0252c8178da302c0172b8178d15d83155829458c85d6a8556a0458ba5a832568215655045478358b02d2a025298158a25a6aa5679945731358992d2a12569856290168db448c2568195779145729358a925690575484547035890252881765055880458735485a548385c8426c8326482a54821241a86462844048141a856640465983e4c02e1b85c1b05c8046c7fb607f2606496c1a85c86b5b863538525b84a5381a338105f8085d7e8571a0557004d63847620455903f4b82f040157d85d7b8357c85d610557bc567b35a61356600567d4567c3565f857530457a8357884d46035798254583478a3145026792317804d5883d448277705d750257605d5e8557535674a5a5ea565d85676b5675a565d0574203574025520457203d7302550844722425004672a424f8477183d4b02d70c5e701556f9456eb546d2546b15c6ba6c6aa646a254698241c1646315402814649561c1466093e5e12e1d15c1c95c67c6c6736066a601c15c6406c65c5e6495c6406c020146314e6285e0181461b6c613646096c600345f26c5ea645e16c5d8246e35b6db536ca5b6c253692336895f6815d661571a1556514d63947621455f93f5d12f010165c15d571355b15d579555a36c57b64569345986c5845a57c5657356569565bc565ab565915758945561355414d52135551255193454241511265194c5083c519405093052b50522405115c5003c54a315394d5313d4f9274e95d499254d95d4a1554ca6c4a264491244c06c4ab5a4a35649a56491564e3564d2564b9574b13548925461454413d479254393c4584c4593046b50462404313c4505c4394443a30443424314647242449474293d4212d4125840a54401543f8543e36c3db603d26c3ca603bb483b3443aa483a24439944390443825837a5437154368543546c34c603426c33a6032b5c3235431a383123430934300342f2482ea442da382d2342bb402b2382b3442bc542aa382a234299342903426a6825a5428154278541995426b6c2136405a6403864259562115524c6c2446023b6c2336021258192502296c2206c1fa5c1e2501f25c1d15c1b85c1fa5c1f2501e35c1c95c1b05c1d2501c9501ba501b1502145e16c5d20b5e203521ea5e1da521c15e1a85e1995c19364052641895c181541794c171441693c030641323815b481534412a581494414044133440f14412b5c1214c119440ea401095c1005c0f14c0eb540b2380db5c0d3540aa480c9340c0340b344071340ab4c0a15c0995406a300894c0804c0713c06b4405949051410485e020460184403949031410285e02046018443f45f3ec5b3c45738c533635f35b5b333572fb532e34f2cb4b2c34728b432725f2625b2525a21a571a2561625313a4f1124b0fa470e2430ba3f0923b07a37062330415601056ab34faab4ba7347a0b439e24f9da4b9a24793a439123f8ea3b8e23788a338794f7e1477a13f779377392f711276f04f5c8475583f4f0374802f41827008170001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 347 (dagTraceF m_46 s_46 8 f_46) l_46 0) s_46 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 64 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_2 : treeBlockF 64 96 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_3 : treeBlockF 96 128 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_4 : treeBlockF 128 160 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_5 : treeBlockF 160 192 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_6 : treeBlockF 192 224 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_7 : treeBlockF 224 256 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_8 : treeBlockF 256 288 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_9 : treeBlockF 288 320 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_10 : treeBlockF 320 347 (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nj_46_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_1 (fun _ h1 h2 => treeBlockF_at nb_46_2 h1 h2)
theorem nj_46_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_2 (fun _ h1 h2 => treeBlockF_at nb_46_3 h1 h2)
theorem nj_46_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_3 (fun _ h1 h2 => treeBlockF_at nb_46_4 h1 h2)
theorem nj_46_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_4 (fun _ h1 h2 => treeBlockF_at nb_46_5 h1 h2)
theorem nj_46_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_5 (fun _ h1 h2 => treeBlockF_at nb_46_6 h1 h2)
theorem nj_46_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_6 (fun _ h1 h2 => treeBlockF_at nb_46_7 h1 h2)
theorem nj_46_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_7 (fun _ h1 h2 => treeBlockF_at nb_46_8 h1 h2)
theorem nj_46_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_8 (fun _ h1 h2 => treeBlockF_at nb_46_9 h1 h2)
theorem nj_46_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := block_join nj_46_9 (fun _ h1 h2 => treeBlockF_at nb_46_10 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_46 g_46 bds_46 347 (dagTraceF m_46 s_46 8 f_46) l_46) i = true := nj_46_10
theorem lb_46 : LowerBin m_46 s_46 g_46 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xff00ff00ff00ff00
def s_47 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_47 : Nat := 0x1100150015001f00
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 5, g_17), (m_20, s_20, 5, g_20)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl
  · exact lb_17
  · exact lb_20
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide +kernel
def f_47 : Nat → Nat × Nat := unpackForestF 0x74e0a9fe5102a5e75ccca191732280547a8316082a0a0543089f2110225b75c6ca0d571aa804474858a4812120443083e106cb1804171a402490209801f 5 10
def l_47 : Nat → Nat → Option Nat := unpackLinksF 0x8c2308c2218822088220791e0781d16c9b06c1a1681a0681a059160581514c9304c121409003c4e107401 0x7944735c6e50685c645058205c1854144844435c3e50395c355029202c2c24240c20163008100d200924834e7d4f754b614751434c4f444b304720431c1f181b10170413001f 10 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 33 (dagTraceF m_47 s_47 6 f_47) l_47 0) s_47 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeF m_47 g_47 bds_47 33 (dagTraceF m_47 s_47 6 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 33 (dagCheckNodeF m_47 g_47 bds_47 33 (dagTraceF m_47 s_47 6 f_47) l_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 33 → (dagCheckNodeF m_47 g_47 bds_47 33 (dagTraceF m_47 s_47 6 f_47) l_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 33 → (dagCheckNodeF m_47 g_47 bds_47 33 (dagTraceF m_47 s_47 6 f_47) l_47) i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xff00ff00ff00ff
def s_48 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_48 : Nat := 0x1500570057007f
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 7, g_16), (m_18, s_18, 6, g_18), (m_21, s_21, 6, g_21), (m_29, s_29, 6, g_29), (m_37, s_37, 6, g_37), (m_19, s_19, 5, g_19), (m_22, s_22, 5, g_22), (m_30, s_30, 5, g_30), (m_38, s_38, 5, g_38)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_18
  · exact lb_21
  · exact lb_29
  · exact lb_37
  · exact lb_19
  · exact lb_22
  · exact lb_30
  · exact lb_38
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_48 : Nat → Nat × Nat := unpackForestF 0x63714dc5279d4212710ddb50551c4273940b47105c01f 4 10
def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x3cf1d3a30d9b1464c882e4701 0x205d427811e750849db50551ce502d1f237b4de92770dd027105c01f 7 3 10 4 4
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF m_48 g_48 bds_48 (dagRefF 13 (dagTraceF m_48 s_48 8 f_48) l_48 0) s_48 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 13 (dagCheckNodeF m_48 g_48 bds_48 13 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 13 → (dagCheckNodeF m_48 g_48 bds_48 13 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xffff0000ffff0000
def s_49 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_49 : Nat := 0x1115000015570000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 6, g_27), (m_29, s_29, 6, g_29), (m_40, s_40, 6, g_40), (m_23, s_23, 5, g_23), (m_25, s_25, 5, g_25), (m_4, s_4, 4, g_4)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_27
  · exact lb_29
  · exact lb_40
  · exact lb_23
  · exact lb_25
  · exact lb_4
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_49 : Nat → Nat × Nat := unpackForestF 0x169fe7929f3c14f908e7cc27de6019f209cf920fbc905de4039005a5f8a4a7c5053d4a51ef895f84513be247df02befc2277c08fa94a1dd93eeec0cf52547b425fdc144ed091f6806fb5089da013ea4a87620fbb105dd4851ea817f5c113aa047d501feac2275404fa90a000b47e9894f4c0a790473d092be8491f420afa1047c8238e789f73c06790273cc92fe6491f3206f99027c8138e581f72c0bb90073c882fe4411f2207f91027c8038005a1f1c0678b253c602ee2c1480292f894d9ba24bdd123f0a50785083ba246dd095f0251b81033ba129df4b66fa5537d031ba123dd015ef211b7905dba029dd4366ea15375059ba02300521ea517b7148ba9452dbe366a497f6c293b6049d492f6d4953524a7b2a5dd9522eca4a765053a9252d4895ebf17b5f8a5af95ed7c0cea44a75c2a9ae018d4891ea40af568bdab452d582f6ac0bb52053a9854d4c166a408c01477a8019d3494e9c0bb4d05200a33d2c14e904fb4907da4019004a5e50d4f43471a1938d0c9a650d2f412d99414bca0a3e7a9073d08394146ca09fe6cd4b366959b24acd92366c0a72827d9896ccc4aa6624f33103194133ca00de5a11b2d07d94019ca4366521532909994013004a1dfb17b2528b7ec52c851c6424e3212697eb53bf5a5e3d1b2fd2bf8da49c6c24dfa57b192a97e953c50aee285171427d8a019bf4a95fa4ff0b8bd85c52c2da9616d2b0b4bd85a52c2c14dfa4fb072a98393cc1c0c5fa4cefd03780c5ec062960217b0107d7e819bf82a5fc132fd0260093bbec14df04faf907d7c01900499cb117ef169178a48bcc0c5e2522f12892c45bbadb05d6982eb2d975960bac304b115ee569172a48b94a45ca512e50912c453b85a35c28eae10732c352b662f5bc512d98a56cb5eb65a95b28ead90732c34ab49a95ac8d2d269569246b491eda40a6584a563c5eb3ca258f14acd46963b52b1da558e97ac74a563a3db1c14cb092ac46c162260960afd84142c068b60049960af5769b2bb2995d93caec964b056eb58d95ac60ad5a856a942b50c12c157accae55a992ad2b956954ab4a655a4f2ad0312c153a60af5305769829b4c146a60a2d30512a52894c13da8ca25304b6a029950144a600d530066980314c84ca64225320f2990594c016960a9528d62944b14a048960a7d1c9728e2994713ca3ca651c062582973ec5e9f6294fa57a890313e9529f4a34fa4f67d25b3e81a9f40cd02d3a816853e8189f81e4fc0b27d02d2c14a9e9a44f49225828f3545e9dc1c4d514a756993535a9c1a84e0942702a1380509a9ab4d84f26c259360189a9a74d41065828d3414c9912a4c8532642793212c960a1cb006e5c6a52e34a971294b892a5c0bd2e0469600ccb2132590792c01300491caa4a2550492623394898ca44a64c07d26a329349f49c5124d2652602e00425c3ed4e472712383891c1a43ed2e1f4a721128908144840921f4971f8288fc1243e8ce3d0d90f84b87c23c72906392830f84687c1fc64d4a326951924a8c9234644a61f07d1686c8b42a45a0f22d0590f83387c17c4a94a254951294a894a344a4fa252650f82e88036440152200991002c87c1180210de68bd0e04579a294304e2180710c034799a9bccd2e132510982884c123cc94de6497072548381441c091e64670646c7982fc1292609292f305e81c2a3cc14e020bb010458081f4040b9e60a4f303f7e62f3f3149f96a4fcb4a7e52f3f2949f9252f303e7d42a3ea0f1f5058f303379817bd7179eb8a4f5a527ad253d6579eb2a4f593e7ac993cc0b9e70a8f384c79c163cc08c01076f1254788943c4091da466ef93177c94bb40f9db464ed93e76c993b40b8010668645f74da43a6521d5058e984874c2221916dcd6c0e6a60734b039a1b1cd0c08645771da438e921c7290e384871c2221914dc368ce1a3970c9d218d49bb8bce00446ee29376d79bb6a4dda396ec9d218d29b5498da9286dc2236a0a1b50488625b6c8143640910c4a6d78286bc1221892daa498d51286a8143540910c486d403467da934c0d19f694cfa5e68d2233e9499f494cfa4667c952188c5966a4ce134659a533449196462cb1466589eb2c4b90c2a4c445e64c2231114991268c4352621a531a9118d248c4231620af3105498827ac412e430a530ad81852c08605f60ca8300d1580292c01214302f2f65b17b098bd82c5ec0e21816d758d8bac605d5a82ea981752a0860575cc2e2da5916d0b8b68545b4262da0f16d0588605355918aac179560baab04d558232ac11565242ab04458c222ac0f55605caf84c57c222ac0b556058ad04c568222b40f15604aab84455c122ac0750c0a4a9358549242a45610c09ea615c5302629c1314c078a602c43025a751793a8a49d2314e82f28c0b13a0a49d0464e81ea740b93a05a9fb4e4fda12740b13d0789d0254ec122740750c0949bb484dca421811d238bc9a13848e29264d31236b496b504b52825a5412d0a091b564a41e2520b12903891b4e48ca0a464e5232629223848c90a18119210988e9544742623a0b11d0388604346da02180bd106a48834a4412d220909102bc88152440a5220519100a48804a4301721a1310d058860230041180517d054908294841c1e20a121050880145b3fdb01fe980ff2c07f86c3fc3000515cf96907ca483e4a41f2120f9088014533cd1c1e64e0f5088798383cc1a004d6cf007078034009a99da0e0ed0680134b3a11c1d04e0e807074034009a19c8918e447c7212a009291b9178e10886e4523712f1b8948dc47c6e12a009251b40d0d16a46c034345a51a2978d548868a52345251a2918d1254012323212919c490c84946612432119190518c827c6412d008a9175178c50885d45230c92174948ba4945fa442fc921748c8ba2bc5d1522e89f1744b4022945c03427da916c0d09f6945a12427d291644909f4945624e2bd1a158908ac4745623627d181544809f2bc5323029c9014c5109f2a45223027ca51424e0a12404f94627c968044c89c4c04e1600082f9349409568a4aa492549112c480950440105e240b61200f0900584801c0082d9151b08a8c04536022928114540020ae4405c208b2104170820a84104c2081e1040b0020a633a321fd180ce4c8670bc3385d19c268ce1186708a3b1221dc900ec088670883383e1c8260e41106707a3383c1b8260dc1106706a358441ac1a0ce0b4680883403419c0e8041486369031a5818cac00413c5d2b83004c174260ba0f05d0580104b1262f093148494642c230124990921785507824852124230920f84907a27b4e13da10920f04906a26034124168940d04903a0104a1192408c5200208e17c5e10d1c05f1484169817b5a0f1a80789403c2a01e0500bdab0700f0380581c01c0bda705e9042f47217a310cd1c05e48830470181200bc110041182d098149540a41e0520b029038010430992004c5000207e0db5a06da10369781b4a40da4a06d230365481b2940d85206c250040f8180780c02c00819806d480369401a5200d25006548032940185e030220180f00c0580601c00c290100f0080580401c00c250061180307a0182d00c0e8040c8010260001f 10 11
def l_49 : Nat → Nat → Option Nat := unpackLinksF 0xe609e600e600e546e540e540e486e480e480e3c6e306e300e300e246e240e240e221e220e220e201e165e160e160e0a6e0a0e0a0e081e080e080e061dfc5dfc0dfc0df06df00df00dee1dee0dee0dec1de25dd09dd00dd00dc46dc40dc40dc40dc40dba5dba0dba0dae6dae0dae0dae0dae0da45da40da40d986d980d980d980d980d8e5d76cd760d703d700d6a3d643d640d602d5e1d5e0d5e0d507d4c2d4c0d4c0d3c8d3c0d3a1d3a0d305d2c2d2c0d2c0d1c8d1c0d1a1d1a0d105ceb3cdc7cdc0cce7cce0cca2cca0cca0cbc7cbc0cb82cb80cb80cb80cb80ca88ca42ca40ca40ca40ca40c90ac8e1c8e0c864c822c820c820c820c820c6eac6c1c6c0c644c3b5c3a0c343c340c2e3c283c280c223c220c1c3c163c103c100c100c0e1c007c000bfc2bfa1bfa0bfa0bec7be82be80be80be80be80be80bd88bd80bd61bd60bd60bcc5bc82bc80bc80bb88bb80bb61bb60bac5b873b787b780b6a7b6a0b6a0b681b5a7b543b540b502b500b500b427b420b3e2b3e0b3e0b3e0b3e0b2e8b2a2b2a0b2a0b2a0b2a0b2a0b2a0b2a0b16ab141b140b140b0c4b082b080b080b080b080af4aaf21af20aea4ac15ac00aba3aba0ab43aae3aa07aa00aa00aa00a9e1a9e0a945a921a901a900a8e1a8c1a806a800a800a800a7c2a7c0a6c8a6c0a6c0a6c0a54ca540a540a521a520a520a520a520a36ea360a360a341a340a340a340a1cca1c0a1c0a1a1a1a0a181a180a180a180a180a1809fce9fc09fc09f449f409f219f209e289e019e009e009dc29d449d409d409d409d409d409c679c609c419c409c409c409c409c409b679b609b609b039b009a849a429a409a029a0099c299c099c0998299809980998099809980998098e596f096e096e096e09645960295e195c195c0958294e594c194829480948094429440940293c293a193a093a093a09362936093609303912f9120912090a490a090a090629060904190409040904090408fc48fc08fc08fc08f638f608dec8de08dc18dc08dc08da18d248cc38cc08cc08cc08cc08ca18c818b2b8b208b208ac3871e86e186e086458640864085e385e085e085e085a2854384e38483848084808461838783238320832083018227822081e280c980c080828061806080607f877f427f407f407f407f407f407e487e407e217e207e207d857d427d407d407d407d407d407d407c487c407c217c207c207b857933784778407767776077607741766776037600760075e1750774a374627460742272ea72e072a272a072a071c771c0718271807180718071807088704270407040704070407040704070406f0a6ee16ee06ee06e646e226e206e206e206e206e206e206e206e206cea6cc16cc06cc06c4469b569a06981698068c668c068c0686368606860684167e3678366a766a066a066a06681668065e565c165a165816580656164a664a064a064a064a06462636863606360636061ec61e061e061c161c061c061c061c0600e6000600060005fc25fc05f255f205ee25dc95dc05d825c4a5c405c405c215c205b665b605b225b205ac35aa15a815a425a2159e259e0580f5800580057e157e057a257a057a057a0562c562056205601560055e155e055e055e05583558055805580558053ce53c053c053445340532153205301520851e151e051e051a2512451205120512051205120504750405021502050205020502050204f474f024f004f004ea34ea04e244e014dc24dc04d824d804d804d804d424d404d404d404d404ca54ca04ca04c624a704a604a604a6049c54982496149604922490148654841480247e147e047e047a247a0476247604741474047404702470046a346a04662448f4480448044044400440043c243c043a143a043a043a043a0432443204320432042c342c0428242804280424240cc40c040a140a040a04081400440003fa33fa03fa03f813f613f413f403f403f213f203f203dcb3dc03dc03d6339be38c738c038c038c038a138a0380537e137c137a137a0378136c636c036c036c036c0368235883580358035803542354034a534a0346233493340330231ca31c031c031a131a030e630e030e030e02f6c2f602f602f412f402f402f402f402d8e2d802d422d402ce32cc12ca12c622c412c022c002a2f2a202a202a012a0029c229c029c029c0284c2840284028212820280128002800280027a327a027a027a027a025ee25e025a225a0254325402502250024a324a024a0248124802480230c230022e122c122c022a12262226022412240224022022200202f202020201fa41fa01f811f801f611f601f411e481e211e201e201de21d641d601d601d601d601d601c871c801c611c601c601c601c601c601b871b421b211ae21ae01ae01a831a801a0419e119e019c11982198019801980194219401940194018a518a018a018621860186018221630162016201620158515421540150214e114c11425140113c213a113a013811380138013421340134013211320132012e212831280124212401202102f102010200fa40fa00fa00f620f600f410f400f400f400f400ec40ec00ec00ec00e630e600e220e200e200de20de00de00da20c2c0c200c010c000c000be10b640b600b600b030ae10ac10aa10aa00aa00a810a800a800a800a80092b0920092008c308c008c008c008c008c008c008c008c008c008c008c0084408400840084007e307e007e007e007e0064d029e00330001 0x1b2241dc91ce26507262737b12380420c3a0e5d804685013bd498fa04a6f2242eb831f3c14ba8086f4465e693ebc899212087cc032830117589921048bca07cea032f241720c08bce473e5939bc091f900e5d204682013bbc98f8c4a6ec242e8831f1414b9a087c2289df844f0c95f8248fc0057df02340c09ddc8cbbc27d7613240810f76064ff023dc144ed4227724bfb7246e8023ed80df6804dcf26480922ec81f39a0cbb105c7f822eb822756112eb247d782feb411f5807faa027e2251ef528774547b32a175123ec028f52141cc0467f013ba498f4e4a6e7242e5831e9814b90087a4257d1923e8815f4208cfd02774232e7c9f5ce4c8fc043cf0193e808f384bf9b246e5023e680df3204dc92647d922e5c1f3900cb9605c7d022b9491f280bf93047c901fe4409ee0927a5473d0238c90a4f3a4e7982717212386c24f2a0e790070e30233e0099ee0878e0327a0113d8917180b8f4045c6929e2c149e404f676a9c4a6cd9d246ced3b22293c3141b8c90c3212785082e2821b89205448c3324a591a4ac88a570451aa225ae2031e040c9e2046a325151238dfcb66fc5533a299be81870ca02ac4c2e146316952868a543212b7a08dbc82e3c4112ac07558050ab138ddc366ec15236099ba82ce2125ec892b8748fc2246d18a9e4052ee0263c192be0094ef848e972432505385c25b840c77b057bc029dd011aaa084ef027b7a5db7c98ec44a68c242e0831d6414a940877148b6e931d8494d16485bf063ac02952410edf1b3684c1b445ddb4a4e88506dc243b604992020b7c087686d9b5254da12eece916db263b3129a2090b7a0c765052a2821b692050a8c3628bdb0c52d152961092b602bda2152a1496b780c75f032770119b49450a8e35d2a98714cd700c3765013a261acc5ed62295b28c6492a4fa94ad5c2f49014b5605c770224e80ea520a13a271aa0547f0266a60b3728bdb8452db92fed697b694a7b2252d08a9e3e52ed8263b192bd7894eb648e7c2432305385825b740c75a057aa829d4811a72084ec02675821d400c9d2044ea245a702e3a41169e4a74d052738136e418e960a5b6042dc132d241f36c0cb4a27cda033d200cdae903324719d14cb58985aa903454719c94cce09e6884e34326944130c592a6825b3162918b34ece124e7c906d42450a049cf4209cc046d348152140ce9a9672d2b384959ba46a911ee6c0a5b304272811a949e548933342d999954cc89e662060e426033920b491944054a152950a04acb82365a0f9b30643381d1a40c0ce4a32b0d995054ca4264540f3466a7a134bb451968052f132959f947cf0a36764ff3527d98133a5c9948a14e12096d883338c10e5e06f2c0339401319808da08cb1e2bb8893ea30991c4087040322d811b391964a5171027d4593238010e060645a02366930b31206468e30f2998613cc889c6424d28826165a40c211c61c5331e8d98b960c5e2ee389270c48365122c6c24c86104df0238ba6cc64aa5928cb172bb8b145c549f5104c8de0438a01915008d909028628188c5ec422961ed4b0e69586a5ec312950c8f70b052d802137408cdc4f28649984954c209e60e060dc26024920c122f60714ac74652215279ca560417a430a58083e6c0190920743803024928bfc2a5fc131ef0799345ec9229640d4f1f69763232c74afe3457b182a789952c489fe144fb062673e13290429c2212dae0666d821c140de00066fd026240116b418df60a5ab042d6132be41f3560cafa27cd4833be00cdb6d42df69164a50b41244f0572882a146148bcc0c5ead22f44913a154bc8a45e251272289389449cca24e0512ef6c177260bb4b65d85826f28975860b792459e522dd6b174b48b392c5d09228b2b173948b98a25ca122db69571b46b5d2959892ae24756295dadcaadc20e56b0626c8219840c82c046de2896fc5eb76295b8d7adb6a56aa52b2d255b48ea9629b3d945b641ca900c4d70433001905408dac8d2d76a56ab4ab25255a891ad347b6215dad8aab4e0c6d20524002197c0c828046cf28966a34b422f59d14acc6a565b4ab292f59294ac847b4a94d9e8a2b4a0c6c70522c8219780c826046c56c162260af8b4554582c20a15dc5eaaa2ecf0d36c168b6004990020b48084d6023599549cca2018062be4d95e94caf09e5764b2b98d95c460adda856c942ab2d959150ad430566572aa4d959264ac4ae560552af2995713cab40c4e6512a10314e014a949e5464b2a00314d81468c109aa046a52894d014a8ca2532052a129950144a70265361129a0794c82c0300e55657aaa2bb5494da20a555051aa728b53144a909ed444b5a20626a021a7c0d53c0669d0314c01602c08d2cd62954b149158a1ca252812268289478189b8a24da5128f29936144a492e4d6952912994813ca380c50406275289408189cca25120626e2893f8149b4a24fc0526c2894134ea05a14fe0f27e0580401ca322f51714a8a2bd44152a1ca34d65168627b4292d684189a60868403541819a000c4fa058070233db489e9244d65226728139b449dc1c4ead32736a1392509c4a84e01426e2793692c9b00c4f117a768a53a35a9bdab4d6d3a6469b078499a820c200e5e4062d002134808cd05300803133a54998a64ca4f264258cf940344980064800c09004040985a94c0d2a5f4a52f24a958ad3c650a5d0bd2005283c254b81180303a01928968264b20f2f68bf7845bbaa2bdc914ee06a56c34ab452958c92ac32bf5f95eae8add6855eac2a74b952a4ca7d1a52e7c2953c9479a4a34c650e540b71f05383425bc210d9e062680219880dcb606658026010110300a4ac4a2530992803c934164aa092532632912993490c9c5100c0312823293c9f49a4ca544672883e9301733a5022d2711b04c67018336502492711a84c8d01e4900e247068a283033c984404a22a07867020334984884a2290791402c90c1448409054040cd03033010332500cb260091205ac201000c225059200288fc12016082042a91e86c81024408d3a344931d2418a0a4c72505980446501265ca02c4102366a51ab4a8d1254669196247b191298949099204963078b114c8c03645e1522e0791682c320980d40c22a4a514a4a8a0a544e51a2627d129321a896b2c0c86c0583513c88c36444152210991002c929a9c8cd2e454a720a4b8f919b2a4c8c72451e04b8042547611e3808d1b83f8c41f4580cd550651582f8901743e08c66044ca13231891418175ff07ca50327c8170b6089922646212287022bfc0f949064f882e168113220c1902810d1387f4263f40f2190710c0345141831e501f5270fe04c30c101844c215250f803c7b4164280a2130482a020304983ce4a1ef078c71303009031a0c0bf04108254630a017c4c011240a4040164183d60b20f0510702401c104191b2050c102c5d82924bf490609292f694162c1117a04a052d9038546289917848a050bb0204580c1f28a0ca0205c2a022624a0286101ff8bcff4527f5a93f8d29fb4bcfd25250d1ebf24a5eb2425d8124ac1e286531f70a8fb03c7d4161744c04b060f945e7c6293e0949ef494f715e7b4a93d84f9eb2642592d620190720b04b278f48547a0263ce0b21d8bd0dc5285da9c2cd2e124a708a4b83519b0e4c8b92450585f8202f40c14e010a50003f7e01f3e80cd39064f982f7a8173cc08c48044040147912a3c64a1e0098ee83c76c163c4091e0262ef92976c90810061dd464ee13e76c993c28cdde07ced02e6f5a8382d218a2a0ca1484d42e28a1414a090ea82c75da43ac521310a8ea04874c2225e1112e088968444c0223a2d81d04c0e79607383639a1812c088e024864c2437ed61cb690e5248648ac392521490b0e404871c2237ad29c568ce223968918b3a54990294e193a2dc9130c175770aa8c82e05811380111c18bcdfc526f9af37ad49bc472d0a3166ca931e529bb2745a92255026a701151805c0a8226dc2201a0b1b9498dc12845c1e36c0a1b5048d42302d01034ed01a2480599301f8900280c114058d98286c812016081a646059020695a0342900b12602b9204982a0260c113058d80286bc1200e08009058d6a4c6b09424a15116078d58286a8120fe4c1a80682c1304902234c0d0b02405792068d2215c4c0ad260c71382b09034ed49a5694d225e68929342929a048ccc952630a51564c19f254c005e5ac292901292308c8d83d6709a0fe4c19a248ceb5266da53328c58a294cc14665c9eb2c4b87e244c285d5d42aa220b812044c98446449a31c91058260c69246522f325149906a4c7b4a63118b165798a2a4c493d620970ae4895209a9b84544017022089866c0c29605f8342d2181832a0550205ee2f2d31753569ac1345604a4a2850580242548125cc2a2601100d058bf16c5f4262f80b17b038bcc6c5e2302eed41764c0ba9505a8362e4141730b8b496c5c8b22e2171700a8b784c5b81e2da0b0a8260b28444c0222c00b15c048b183c57c162b609158038538205949094c04963088ad024580262be1115c098ad8445681e01a0b157038ac04455c122d68c4a5244b505e5a42ead013545094b384659822ac81116207ab082e57816aba0b15904a058225580eaa8d6153490a91585402c28811121088a702c4ac2229c1312a08894844540ae2505514f098a683c530162800b1320889f82c2909826011146058958444f4122541114069c9fb424f41e0120b13b038948444ec12295179498a4a423128c9128e179450a4a20464a022a860f54205ca082d4f816278094070449d01d4e1a426e52128090900404c1a22684e132698983504bd2825c5412d0a09583c4a81625207124460510204911c142081358bc99c524c5ad258d592869c8eb4d44ca4a4e505262729293148c90940049210980482c480aa23e1311e0588e81c46da013e4c004060069240249201a520092808cb52461a522e969164848a95e450a92265291228c0212d44429220128042788704c434163b117dd28b6e645771a29b84d49ba694da25b6c529b5c92da9486cf231654a930e5289e244c205f5fc2f2f416d740aeb6053554292a213d4b0969c84a4d823a441191c0868d02f43c1721808c020446f25038924178540c62902205c150280b61210707884a48420a408015106090828440f82207a1103c0881f84440db0204981012c08006c3fc30076110e1290628483f5a41c0960fc490621583eca40b4160fa0907c8443d42201c0f0f74707b138090261e80e0f30686d1302e0181b2900d44605b9402949802c10021078788383c01a0160c0d82605b03035d201a68c0b5280519300d42a02a10020078770383b41a00e0c00a07875a383a89c06815023098748383a01a1bc928e648c72a3e3511919e548c2294599323909513a1748b0aa0f03e050191c2110e28bc7045237d2f1bc948dd47c69a32334a9182528b12646e12a1902688e1141d07c098322a0981b40d0a4260198443601a160480af2406aa442b89815a4c0c027056120365a91aed28d64bc6a25234d251a4918cb2a45f14a2ac981a24a8970bc40052164250641182707a671242a098198490cf4a466a4a32d19178528ca28c6493e294991904b49c0ba450550701f0240c8c508861924301221484c0bf2486345e31229184948c14945f2322f4af178548bb27c519322e8968c61344608a0d83e0441915c8c0b806856a300c42216c0d0ae4605a1242b518144510b224857a342c12715c908ad474562362a8a7150508a427450936258270fe10858074180362a89014e4d0a724054230298a21488c0a2270509202dda916ad28b34a458a4a2ad18152578a52a45194a280a313e4b4950bc3f05215c2505e1182607a4ea60270b01261a07c0c04d2502581012c480908bc3e45d111a6932d149849210a4125c9112a088880a81f8440381e1265b0920784882c2400e11d1b08d8c04636022d281145407d0d8438502202e0f85b0872c84305c2142a108130830784102c1fc980f0110770683fa301d82207e11073078378341c81e0dc0d06c0583481c1dc100ee480782443b0221cc260e41106f098370440381e0d60b068038360441ac1a0d211068068402321f8990fa1787c0ba3d84d150250f41187908a3a8441d01f0e20f4700783683502c190d40b46703a32b481912c0c6560610b0298440b4220c00f0600981d0440e422070110612b81b95417c260bc0f05d0582803c1042209e0f0582602c2300fc220aa0f03a0882834e13da10140f04c0582501c0e4220980d0380882503416e2f0b5148594642b9321582f0a81485308c1b8451481f0a20f44e0782683501c190960b44903a23a48118a406e1202c0801fb4410d1c082d303f6a01f2500f4a80781403a0781c82c0e00e0664c03106019a380c0100628e0302402245e10a29080d683b6ac1bb4e0a5a6840924364821aa390d1188644882f0441684c0281e0585502b0781502c0a40e04e90026280028400391a0148d00e49005240091ad046d08224bc10a520812503e9180547a0f152074a50381481b0940294c0641e0300b00f0880703c034160180700a0780482c0200e02cd48156940a25204d25024548112940805e02c2900e1280608c0283d010168060750a8be8245b3fa2b9f114cf26b677b533b1a59ced0ce34a46da4a3411918e548b92944f13226c2f9281788f0b644857204298cc1486209e2e04b1202508a11c2e08c140430941f8340f81706601032f45a7f8ed2fa868fc7b43e2925ee690f51477a6233d1ca5e4e50efc2777b93395c91c9612e1e086f283b76419a1608c010260001f 16 5 11 10 6
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsF m_49 g_49 bds_49 (dagRefF 978 (dagTraceF m_49 s_49 8 f_49) l_49 0) s_49 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 64 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_2 : treeBlockF 64 96 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_3 : treeBlockF 96 128 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_4 : treeBlockF 128 160 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_5 : treeBlockF 160 192 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_6 : treeBlockF 192 224 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_7 : treeBlockF 224 256 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_8 : treeBlockF 256 288 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_9 : treeBlockF 288 320 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_10 : treeBlockF 320 352 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_11 : treeBlockF 352 384 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_12 : treeBlockF 384 416 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_13 : treeBlockF 416 448 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_14 : treeBlockF 448 480 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_15 : treeBlockF 480 512 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_16 : treeBlockF 512 544 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_17 : treeBlockF 544 576 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_18 : treeBlockF 576 608 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_19 : treeBlockF 608 640 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_20 : treeBlockF 640 672 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_21 : treeBlockF 672 704 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_22 : treeBlockF 704 736 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_23 : treeBlockF 736 768 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_24 : treeBlockF 768 800 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_25 : treeBlockF 800 832 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_26 : treeBlockF 832 864 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_27 : treeBlockF 864 896 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_28 : treeBlockF 896 928 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_29 : treeBlockF 928 960 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_30 : treeBlockF 960 978 (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nj_49_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_1 (fun _ h1 h2 => treeBlockF_at nb_49_2 h1 h2)
theorem nj_49_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_2 (fun _ h1 h2 => treeBlockF_at nb_49_3 h1 h2)
theorem nj_49_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_3 (fun _ h1 h2 => treeBlockF_at nb_49_4 h1 h2)
theorem nj_49_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_4 (fun _ h1 h2 => treeBlockF_at nb_49_5 h1 h2)
theorem nj_49_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_5 (fun _ h1 h2 => treeBlockF_at nb_49_6 h1 h2)
theorem nj_49_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_6 (fun _ h1 h2 => treeBlockF_at nb_49_7 h1 h2)
theorem nj_49_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_7 (fun _ h1 h2 => treeBlockF_at nb_49_8 h1 h2)
theorem nj_49_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_8 (fun _ h1 h2 => treeBlockF_at nb_49_9 h1 h2)
theorem nj_49_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_9 (fun _ h1 h2 => treeBlockF_at nb_49_10 h1 h2)
theorem nj_49_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_10 (fun _ h1 h2 => treeBlockF_at nb_49_11 h1 h2)
theorem nj_49_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_11 (fun _ h1 h2 => treeBlockF_at nb_49_12 h1 h2)
theorem nj_49_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_12 (fun _ h1 h2 => treeBlockF_at nb_49_13 h1 h2)
theorem nj_49_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_13 (fun _ h1 h2 => treeBlockF_at nb_49_14 h1 h2)
theorem nj_49_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_14 (fun _ h1 h2 => treeBlockF_at nb_49_15 h1 h2)
theorem nj_49_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_15 (fun _ h1 h2 => treeBlockF_at nb_49_16 h1 h2)
theorem nj_49_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_16 (fun _ h1 h2 => treeBlockF_at nb_49_17 h1 h2)
theorem nj_49_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_17 (fun _ h1 h2 => treeBlockF_at nb_49_18 h1 h2)
theorem nj_49_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_18 (fun _ h1 h2 => treeBlockF_at nb_49_19 h1 h2)
theorem nj_49_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_19 (fun _ h1 h2 => treeBlockF_at nb_49_20 h1 h2)
theorem nj_49_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_20 (fun _ h1 h2 => treeBlockF_at nb_49_21 h1 h2)
theorem nj_49_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_21 (fun _ h1 h2 => treeBlockF_at nb_49_22 h1 h2)
theorem nj_49_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_22 (fun _ h1 h2 => treeBlockF_at nb_49_23 h1 h2)
theorem nj_49_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_23 (fun _ h1 h2 => treeBlockF_at nb_49_24 h1 h2)
theorem nj_49_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_24 (fun _ h1 h2 => treeBlockF_at nb_49_25 h1 h2)
theorem nj_49_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_25 (fun _ h1 h2 => treeBlockF_at nb_49_26 h1 h2)
theorem nj_49_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_26 (fun _ h1 h2 => treeBlockF_at nb_49_27 h1 h2)
theorem nj_49_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_27 (fun _ h1 h2 => treeBlockF_at nb_49_28 h1 h2)
theorem nj_49_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_28 (fun _ h1 h2 => treeBlockF_at nb_49_29 h1 h2)
theorem nj_49_30 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_29 (fun _ h1 h2 => treeBlockF_at nb_49_30 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_49 g_49 bds_49 978 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := nj_49_30
theorem lb_49 : LowerBin m_49 s_49 g_49 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xffff0000ffff
def s_50 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_50 : Nat := 0x155700001f7f
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 6, g_39), (m_24, s_24, 5, g_24), (m_26, s_26, 5, g_26), (m_28, s_28, 5, g_28), (m_30, s_30, 5, g_30), (m_41, s_41, 5, g_41), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6), (m_10, s_10, 4, g_10)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_39
  · exact lb_24
  · exact lb_26
  · exact lb_28
  · exact lb_30
  · exact lb_41
  · exact lb_5
  · exact lb_6
  · exact lb_10
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_50 : Nat → Nat × Nat := unpackForestF 0x25048b28044005a7802d2e4d2b31e25d8f0ae4944da3c2a31e92f8f495c8c0f23d24f2023490c9248055241249200148f491c7a07e3d02f1e150005a3c648e23246b1b02f8dda046c09e32469191388c89a4640d0016871804400527c5495a2d2731524e8aca74544a40149710b5b885a9c4c4e6216a31095b884a9c4453a212a200a4786d264369121b2510d92486c1200290dfe8b50a35d850a8c2a4b61524b0a1507fa2b3fcd6e1069b081397f9ad41d161fe6af05c5e82ca8bfcd5a088c1043547f92bbfc4fe05498ff13b80cab3fc4e5fe26f0013c7fd223fc4cc0147efd1297e8943f449001476fb9417dc260028ddf52a2f8a567c5273e4559f125200a337b922bdc1100129ef5a487aca43ced3de8470f413879da180252dc76b8f223571da8bae8fdd7476f004c75d1bbb4d11dd468ed25476d1a3b4091d7466eb83f75c1bb8ed41d5692e3a5d73e3039edb1cf6c0e835073c9c38e8fdcd688e446072136390951c96a0e412871d1980251dbd298de9446f49e37a4d9bf05ee01306fc13b7a4d1bd028009436ec9c36a93db9250daa436d91f36c8c9b546a0093f6cca3360d35b026cd812e0049db5c9340126ed4b5c6a51c3524e1a9268ae35b69230348981a42d8d2160571abab8d3da0494d0246571a6b3c5355c68ace35c571a1b308f59946acc13d571222b856d9469aca136570ad2b855d8e8bcc725d63922b1c8f55c2acc4c5c629a6314931894a8ae13f61ca6308d5184498c213c5709dafad7180698c024c5f52a2fc5117d098ae1375c5ad2e2d59714b4bbb505dca82e29597149cb8a425c41f2e415171064ae1365bca62c4d516c488b613c589222d091169268b4134588b22c44f163488b213458c9a2c40515c266b014c57daa2b807d5d6a8ae01700499ab093958498ac24400497a2716d534c0a996c54cb022715d136ae89b4f44da3a26969496a2a5a3a52d1b292d41492ba89a5651c9aa269391349689a434f9a6a7cd153e2b49f1564f89ea7c4d5134849e13c44cada725393925a8995a4dd2c22655d338bc99b514cd22a26559314a08994f49e2d25c541278ac93b5a49dab24e9352748a9394949ca0a26539234b89194448c9e22652d214808994747ca62389511c2888e13c44ca1a28569142ac8a14d45ca62284d5152688a12d44ca10024ad0568487b5043ca420a93d0b6a085b4042ca820a91d0749a83a4541c9ea0a50905078009273ae2da048d1004c08016c3ae2b9fc910eb4967e2443ad219f2d44f968a759563c22d1ec540f08ac7835a3c1ab1e0524f0282781393aca71d8908ec29c761423ac9700248c0109e6c24b361239cc4e4d847e72129361199c0d34e107870136360999b8908dc29c6e142360959b4538d82466c046004251ac4e4cc6a26a14e330a899b180cd4c06696c33c9a19a580cd2a866133004239940a4a54865293d2949b98692cc34866184b30c2194a4d4c10525292f2fc1f14a10cac6a45e05c2b1229588f4ac2a45605e2dc12158148ac08a58a322c4a69624b4b1064560442b52815a910ad2885602629411954110a62645303e29c2214c0c8a50360084628ca8928d58942b64fc6027db612855c9429e4a1432552d134d40954ac4aa4e2552112a568952ac4a1390041f9245040106e482541622f8b116c8b4d84596c22cb00b115c8668843244218a410c510588a641b5120ca88b09587c8b4401501f22b0f8d687c6ac3e139161270f4950582be2c15b1d6360eb180754d82c1571c0ae0e05507028838134160a98dc9105829e35b5c1ac9a0b052c694b82c14718dae0cc930634a83194418c9a0b050c594b4303501652b0b2938594842c95a164ab0b2538592842c129004178acd60158be0ac5b145b00a25b0512c00ac57131a40989104c29026144056298944e04749c2414c11c9482ad683e8bc21b4410ca207d1483e4b4201500f92b07c4a4156841e358054af82a56c378d81bc600ddb002a55c322b8191540c8a60644d0152a617b500bda402a53c2d2980a94b0a9a8054d001528e12a5409ca204a530252680a9430592f042910214680b2520592502c918162b40e350058ab02c538174880c13405caa02c50815262008270122d822980112d8024570112580890c0d6a2021560162d014540058ac02b5a015ab00a524052820214e0040f8049080102e0001f 10 11
def l_50 : Nat → Nat → Option Nat := unpackLinksF 0x436021b010c84854442a021405098284a0c1f1a0f03074183a041a0e0c05060082e0c17020b0304848220c11020412ff8a7fc03fc09fe00ff007f60bf909fb84fd427ea03ed21f680fa837d403ea01f386f9c07c81bdf15ee06f6827b403d515e906f4027a003cb15de9cef4077a03bd01de80ef407702bb609db00ed8076c03b601da04ec4375e13af01d780eac475603a909d480ea4074a23a501d280e8c273e239e05cd86e6c071e638c0dc600e2c170e23705db800dc006e0036d0db488da406c6336301b006d7436ba035425a610d300698034811a400d200688234401a200d0826744338099b82cc466600b2f059780cb03654132a019482ca406500b24119182c8c06344b1a018c04c5c162e0317018b80c5816242312018804c4006200310018782c2c460252ff097e84bf405f612fb017d80be815f012f8017810bc005d822ec017486ba405d202e5116e90b7405b612d7116988b2c85940ac6116300b18058c02c601608ab00157e0abe055f00ad495641ab2015900aa0a55002a4115200a804538229c014d04a40a51e0a8f014780a2855101288014382a1c050c0a7e213f009f804fc027c093b8a9dc04ec0a75053a029bc54de026f0137809ac44d6026a05320c99004c60a6301318098c04c01a5f052f8097c04be025e0527209380494224809240091044860a430121029002480023f051f808f8147812351d1a808d014621a31011802849e424021201090083c3416220a050500828040c22040900087f043f411fa00fd007e803f011f800fa867d403e611ef10f6067b003d801ec00f5827ac03d601e128f08077c23be01df00ed8876c03b211d900ec8076403aa21d500e90674803a401d104e88074403a201d100e880740138861c304e18070c037e21bf00de066f0037609ba04dd006d8436c01b504da026d0036411b200d88269ca320b98c10c6006300310218800c4006200308218400c2006100300218000bd0c5e022f0017608bb005c842e4016f0cb7805ac42d6016b00b4065a002d0016704b38059c02ce016700b38057892bc015e00af0056c32a6415204a90054802a4014f0ca780538129c014e00a6825244292014900a480518328c014504a2804f4827a013a0c9d004dc326e0137009b804dc026c093600988a4b8325c012b0c95804ac0256012b0095804ac024c292600918648c0240191f048f804703236091a048d0046802320919008c804640232011900898c44c02260113008806414b20a0104048200410020609000c7c103e001ec10f40879823cc01e018ef0477023b801dc00ed0476803b401da00ed00738c38461c200e004700037c11ba10dd006e8037011b020d8006c0036001b000d4106a0035001a020d000680033c119e00cf00678031c818e00c6046204310018608c3005f882fc017e00bf005f802ec417600b9085c802e4016e10b6045a042d0016800b30459802cc015a30ad0056802b0115800ac0056002b0015800ac005210254f12a00930849022480124009200478623c011c088e0046822205110008704438021811042082004100208010010800040001fc10fe0077203b801d420e80874003a001d000e218710038021c000de086a1435001a800d0106800330419800ca0861102f8417c00bc085e002d0816800b4005a002c0416000ae0857002b8015810ac0055042a8015010a4104a201d9e0e420700838001a860d0106608330018840c4006200300418000c00060003000150c090604800230400c40001 0x25148b2804423c178aa09e1949b07a3d64c98aac4ad032464702f1501382607e4d2b2a99512300f8a405d022410bb4d5551d2028c9532752513604816c2cd312e2990aa4c9109048c0f2432892081490c9248249244469211543d8a64800500a2990a23d92097c8e4ae4524f1f92322c178a209e3e03f1e8179312ec268f64b2b9249518f0a82a44acff2464502f1401382007c8905a270258dda04700be3604e4382f1341390c07c4c02f1d2388e51ac6a8d234271199348c81a10a0bc4b04f172453202a460111ac283169396a898b5690a2b29cd51428b92b458939a8287151293a02d423182086a8630548463418a1521169b04a4d69ca0c4c4e5a42629ca604ccaa188151394d061854699212788ea2229cd21424e496c50d6e0f6b313b53895a8c0e8fe242b69c15988ca9c42545a3266a892b39c2518e118c20890fa4c8792243a4a21c2490d82483a2ab2a4c61625b0a925861aec2e546142a106464825ae418d561169b0813946898c1d1620c6b10645e82122bd65660b2a304c60821aa220d70ec698dba34814a44004d1a14a102a4c451203d8969cf4acdda4e611212388e90f46cf595a80cab1d84b91425a7305a3042b1e0d31a02a0ff9308009e228921ff4889515c5d49a43316a138ad0935b83dad41ad5e0a6ad03a577a8adb9c55dba29ed9149688a1b3e5060627f0213b8089cc024ddfe2668993154095a1c49ce50b4600567f094bf64a1fa24891a3a42d1b1d84e90d26cf9a4d7e0a0b3a4c54f256851277dc263d0565f52a2e5145670a09e04e4ec262f4a5a7212b37293966484f415a7c8ab1da538ec2847205a7d12b3e6939e72b6e39576e0a7b3650df12527185a7bd22bdc1107905e1d8277b12432a541eb2908d1407a51c3d04e1ea69ef3b435391d326509382745084f1e01f8740dc7705e1c827735203a6935cc482e8a3d7911aa9a4a8a009ae81385309c3bc8c14b250f004c775223b6091dd468eda34779a23b8951c9250ed0242689c3c48fde1476efa3776519a944a9d807eeb8371d81787009dd5692e8b41740a43a0d41d38c0e936c745b039e4e1cd688e4928725a8399181cb4d8e5254720943cad71e36a2eb3507512eb9c8fdc7466a412a2781f8e80bc3604e3982f0d4138e40bc3404e3882d0c812b804c1c105edf827714a6388511c3278e11366f89a0de0fc3106ede8146722e1d8d21b7488dd9386d9a21da911b9250763493b5a0b6e8f9b6464d834e6e927b7090db546aa312a274278da0bc2e04ed9946670971d84e4f0262921293f890b38d34ee4747613a4349b364d35454767ea336c49b3604b86a07e1603703c17b34501ae49acb9301a01785209dac6b8d5a385e4a23544e1a9268bc1345dc9a178111a78c0d3260694b62345a17a2c8d216063caa2ec4d0bb0a8c22483b0a02ea4d1a1494d024650d1d2128d9952b4c71566309eb044d4e20b45d056671a6a848e90846ccf14d671ae2cc8e174288761386049eb144d58b25ac01256051eb328d59a47acc13d62497b0c4ad7f24eb71231941785009d5f03eae8176453232ad3541474c89554689d3284d9912b05a8542cc2a164111918bcc825d5e92ab1e9158e47aa012a334229601118b698c524c6322e3129513f490c29484349a30e5316c2688a934619aa30a931164889395c6109e302d3180498b69205f81e2fc511826b8bfa544f91c22c4e16b260be84c2b8222f0d41772a0568444549c2e41517b6b4bd3565e52d2ec9597549cba2424591f1d88f51d2527e1213802d1581597307cb88321901684a0956d468b51545bca62ca05169288b20145b5222d05516c278b18145a4922d24d16a488b4134590922c84d165488b19345b9aa2d6911672c87895c5989e1d84b162028b014c57daa00a57097278aeb546a1adb46d5da269ecfb4d675a2b36d0d97488a223b4f51d20c8d8fb466cb15b64cad32455d8d2acc413f60c9da264e97c26eb8136584999be168cc0ae55856270278c40fc2406e0702f5780fab805d5a49caca4c561222829012f2b89614c468a025c931554c0aa16c54cb025a5313c4c09995450d282389212a2b87614048d28284900ec2a09494c4dd2aa825094c474a5a36535a8a94d41492ba7734e51c9aa50971242887713c3b09624e9711d288761202a822286d354268a98a4d48522a82569402ac9f93d4f89a9bc168a90ac9aa644f09e26a5553a29c8d1424e496a6e961352b09ac5e4b1aca68d453348a98a50494ac2305412e2a08b9344be2d25b1592c6b495b563b1a7230d352a49a94a454a0a4a4e504dd0b45405647ca224a971242889193c3b096242900ed2b88f14047ca622e531184b88f254474a22384f0a70888b93445ca622a4b1152688d15a464ab1da5391829a869364589a9e04b91425a6e05a2982b2ad16d528aea8b57541a7a9ed1d4e4b4a42565192728a92d444869ea424ecada70569362ae991564c0a7a4c539222969014746ca1a26508db0b452856441a6a18d14ec47486a36441a81d8d01092a087948435a8218d010b2a08414042526a10914ee47a8393d445a121c93d0a48e75a3d418a120a0f0f72b87a14c4091a1ec531014c08016c3e4aa1ea530fe4887915c3c0921f8910f12b87713c3b0961e8d64fa6a27cb453d8a81ef168f58ac7a35a3cdab1e4524f1282781393b0989b4168ee4847694e3b0a120716cff8ae7ea4b3ed219f0558ef29c7592e3642d1b0110e228273139370989c84a4e10787134d3791d1b84e8e026c6f242374a71b8508da29c7424b39d239ca8fce34666f93336c959b248cd808c691413589c99c4c4d14846a14e338a119e4d0d28c068a60340b619c580cd2a86ab5134ca89984ccbd062650292d81098c92cc54866204b30c2197608cba06260829298109724c8bf07c5b0322d022178170ae0a8568242c822162110b70485a2322cca695c514b225a588322a80d15e940ae488569442f5a9176914ba47a5c9522a495170178b60a45a8452c02214c0a8ac04c5504429c221524c8a807c53032325219904f4c726e611353009797c10cab0465281b258ac9465449b4904b148268a41411809f6d84c938260a412e9209a6a04da5a2652b130938974844b15a254ab144d58a12b64f157274a793850c94272491412412a1029707e4984024c235360fe9308c2d845960225a211091087290431441f9ac908d445c2b241951200a81031687f8ac3f35a1f5ab0d8524672823e139164988f4950614702e138180940ef1b0768c03aa6c17c940e6570722a8389441c09a0dc9105e2503635c1ac9a0cc500694b832940199260ced70654a82ea38190a20b24e063268303501852d0be9585e49c2ea42170ad0b65585a29c2c94223e2f91d16c8a8ae42c532092b0f6938792be3c15b1d0ab8de54c6d29e3514b1a0a38c450c582522b358115a0082d00536c02916c144b0088900434802135013da409c9104d290261441289c0905304949c20a4211c9483a4844468821944100a808b178428a420a5a0fd2b0605342a28a1f12905890878d60232600e9400e636071180376c01113008490040900352b81a1540cca60644d0306a017b4807d2005a5301924015b500a9a00505001e2601393c0649804e510284a81314c058a004a4d02248810a3406498038d40182880c1340652202e550234bc1025207d2503c9181d2b40d956068a702c508558be2a45b1422b89714c466b41eb420ecaf87456c362ae189530b8a785852c2928e1214305498816570082980524c049300225b0092980325c0152e010d640d6a20515002e2d013158086b403b56018a480a504138b60845703d2581c90c0c2ac0214e0092149ed3e4e6971db478c5a1c5e93e294971024786921bfa8fdf9476fb2377c119bda53de6296e31476f0a1b684fdaf276d693756c99aae4bd12256821273a8919d213cd709465847290231260fc9106e2b82f0501380607c0102e0001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsF m_50 g_50 bds_50 (dagRefF 594 (dagTraceF m_50 s_50 8 f_50) l_50 0) s_50 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 64 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_2 : treeBlockF 64 96 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_3 : treeBlockF 96 128 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_4 : treeBlockF 128 160 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_5 : treeBlockF 160 192 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_6 : treeBlockF 192 224 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_7 : treeBlockF 224 256 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_8 : treeBlockF 256 288 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_9 : treeBlockF 288 320 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_10 : treeBlockF 320 352 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_11 : treeBlockF 352 384 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_12 : treeBlockF 384 416 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_13 : treeBlockF 416 448 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_14 : treeBlockF 448 480 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_15 : treeBlockF 480 512 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_16 : treeBlockF 512 544 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_17 : treeBlockF 544 576 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_18 : treeBlockF 576 594 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nj_50_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_1 (fun _ h1 h2 => treeBlockF_at nb_50_2 h1 h2)
theorem nj_50_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_2 (fun _ h1 h2 => treeBlockF_at nb_50_3 h1 h2)
theorem nj_50_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_3 (fun _ h1 h2 => treeBlockF_at nb_50_4 h1 h2)
theorem nj_50_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_4 (fun _ h1 h2 => treeBlockF_at nb_50_5 h1 h2)
theorem nj_50_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_5 (fun _ h1 h2 => treeBlockF_at nb_50_6 h1 h2)
theorem nj_50_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_6 (fun _ h1 h2 => treeBlockF_at nb_50_7 h1 h2)
theorem nj_50_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_7 (fun _ h1 h2 => treeBlockF_at nb_50_8 h1 h2)
theorem nj_50_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_8 (fun _ h1 h2 => treeBlockF_at nb_50_9 h1 h2)
theorem nj_50_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_9 (fun _ h1 h2 => treeBlockF_at nb_50_10 h1 h2)
theorem nj_50_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_10 (fun _ h1 h2 => treeBlockF_at nb_50_11 h1 h2)
theorem nj_50_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_11 (fun _ h1 h2 => treeBlockF_at nb_50_12 h1 h2)
theorem nj_50_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_12 (fun _ h1 h2 => treeBlockF_at nb_50_13 h1 h2)
theorem nj_50_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_13 (fun _ h1 h2 => treeBlockF_at nb_50_14 h1 h2)
theorem nj_50_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_14 (fun _ h1 h2 => treeBlockF_at nb_50_15 h1 h2)
theorem nj_50_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_15 (fun _ h1 h2 => treeBlockF_at nb_50_16 h1 h2)
theorem nj_50_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_16 (fun _ h1 h2 => treeBlockF_at nb_50_17 h1 h2)
theorem nj_50_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_17 (fun _ h1 h2 => treeBlockF_at nb_50_18 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := nj_50_18
theorem lb_50 : LowerBin m_50 s_50 g_50 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xffffffff00000000
def s_51 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_51 : Nat := 0x1115155700000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 6, g_35), (m_37, s_37, 6, g_37), (m_39, s_39, 6, g_39), (m_31, s_31, 5, g_31), (m_33, s_33, 5, g_33), (m_7, s_7, 4, g_7)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_35
  · exact lb_37
  · exact lb_39
  · exact lb_31
  · exact lb_33
  · exact lb_7
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_51 : Nat → Nat × Nat := unpackForestF 0x169fe7929f3c14f908e7cc27de6019f209cf920fbc905de4039005a5f8a4a7c5053d4a51ef895f84513be247df02befc2277c08fa94a1dd93eeec0cf52547b425fdc144ed091f6806fb5089da013ea4a87620fbb105dd4851ea817f5c113aa047d501feac2275404fa90a000b47e9894f4c0a790473d092be8491f420afa1047c8238e789f73c06790273cc92fe6491f3206f99027c8138e581f72c0bb90073c882fe4411f2207f91027c8038005a1f1c0678b253c602ee2c1480292f894d9ba24bdd123f0a50785083ba246dd095f0251b81033ba129df4b66fa5537d031ba123dd015ef211b7905dba029dd4366ea15375059ba02300521ea517b7148ba9452dbe366a497f6c293b6049d492f6d4953524a7b2a5dd9522eca4a765053a9252d4895ebf17b5f8a5af95ed7c0cea44a75c2a9ae018d4891ea40af568bdab452d582f6ac0bb52053a9854d4c166a408c01477a8019d3494e9c0bb4d05200a33d2c14e904fb4907da4019004a5e50d4f43471a1938d0c9a650d2f412d99414bca0a3e7a9073d08394146ca09fe6cd4b366959b24acd92366c0a72827d9896ccc4aa6624f33103194133ca00de5a11b2d07d94019ca4366521532909994013004a1dfb17b2528b7ec52c851c6424e3212697eb53bf5a5e3d1b2fd2bf8da49c6c24dfa57b192a97e953c50aee285171427d8a019bf4a95fa4ff0b8bd85c52c2da9616d2b0b4bd85a52c2c14dfa4fb072a98393cc1c0c5fa4cefd03780c5ec062960217b0107d7e819bf82a5fc132fd0260093bbec14df04faf907d7c01900499cb117ef169178a48bcc0c5e2522f12892c45bbadb05d6982eb2d975960bac304b115ee569172a48b94a45ca512e50912c453b85a35c28eae10732c352b662f5bc512d98a56cb5eb65a95b28ead90732c34ab49a95ac8d2d269569246b491eda40a6584a563c5eb3ca258f14acd46963b52b1da558e97ac74a563a3db1c14cb092ac46c162260960afd84142c068b60049960af5769b2bb2995d93caec964b056eb58d95ac60ad5a856a942b50c12c157accae55a992ad2b956954ab4a655a4f2ad0312c153a60af5305769829b4c146a60a2d30512a52894c13da8ca25304b6a029950144a600d530066980314c84ca64225320f2990594c016960a9528d62944b14a048960a7d1c9728e2994713ca3ca651c062582973ec5e9f6294fa57a890313e9529f4a34fa4f67d25b3e81a9f40cd02d3a816853e8189f81e4fc0b27d02d2c14a9e9a44f49225828f3545e9dc1c4d514a756993535a9c1a84e0942702a1380509a9ab4d84f26c259360189a9a74d41065828d3414c9912a4c8532642793212c960a1cb006e5c6a52e34a971294b892a5c0bd2e0469600ccb2132590792c01300491caa4a2550492623394898ca44a64c07d26a329349f49c5124d2652602e00425c3ed4e472712383891c1a43ed2e1f4a721128908144840921f4971f8288fc1243e8ce3d0d90f84b87c23c72906392830f84687c1fc64d4a326951924a8c9234644a61f07d1686c8b42a45a0f22d0590f83387c17c4a94a254951294a894a344a4fa252650f82e88036440152200991002c87c1180210de68bd0e04579a294304e2180710c034799a9bccd2e132510982884c123cc94de6497072548381441c091e64670646c7982fc1292609292f305e81c2a3cc14e020bb010458081f4040b9e60a4f303f7e62f3f3149f96a4fcb4a7e52f3f2949f9252f303e7d42a3ea0f1f5058f303379817bd7179eb8a4f5a527ad253d6579eb2a4f593e7ac993cc0b9e70a8f384c79c163cc08c01076f1254788943c4091da466ef93177c94bb40f9db464ed93e76c993b40b8010668645f74da43a6521d5058e984874c2221916dcd6c0e6a60734b039a1b1cd0c08645771da438e921c7290e384871c2221914dc368ce1a3970c9d218d49bb8bce00446ee29376d79bb6a4dda396ec9d218d29b5498da9286dc2236a0a1b50488625b6c8143640910c4a6d78286bc1221892daa498d51286a8143540910c486d403467da934c0d19f694cfa5e68d2233e9499f494cfa4667c952188c5966a4ce134659a533449196462cb1466589eb2c4b90c2a4c445e64c2231114991268c4352621a531a9118d248c4231620af3105498827ac412e430a530ad81852c08605f60ca8300d1580292c01214302f2f65b17b098bd82c5ec0e21816d758d8bac605d5a82ea981752a0860575cc2e2da5916d0b8b68545b4262da0f16d0588605355918aac179560baab04d558232ac11565242ab04458c222ac0f55605caf84c57c222ac0b556058ad04c568222b40f15604aab84455c122ac0750c0a4a9358549242a45610c09ea615c5302629c1314c078a602c43025a751793a8a49d2314e82f28c0b13a0a49d0464e81ea740b93a05a9fb4e4fda12740b13d0789d0254ec122740750c0949bb484dca421811d238bc9a13848e29264d31236b496b504b52825a5412d0a091b564a41e2520b12903891b4e48ca0a464e5232629223848c90a18119210988e9544742623a0b11d0388604346da02180bd106a48834a4412d220909102bc88152440a5220519100a48804a4301721a1310d058860230041180517d054908294841c1e20a121050880145b3fdb01fe980ff2c07f86c3fc3000515cf96907ca483e4a41f2120f9088014533cd1c1e64e0f5088798383cc1a004d6cf007078034009a99da0e0ed0680134b3a11c1d04e0e807074034009a19c8918e447c7212a009291b9178e10886e4523712f1b8948dc47c6e12a009251b40d0d16a46c034345a51a2978d548868a52345251a2918d1254012323212919c490c84946612432119190518c827c6412d008a9175178c50885d45230c92174948ba4945fa442fc921748c8ba2bc5d1522e89f1744b4022945c03427da916c0d09f6945a12427d291644909f4945624e2bd1a158908ac4745623627d181544809f2bc5323029c9014c5109f2a45223027ca51424e0a12404f94627c968044c89c4c04e1600082f9349409568a4aa492549112c480950440105e240b61200f0900584801c0082d9151b08a8c04536022928114540020ae4405c208b2104170820a84104c2081e1040b0020a633a321fd180ce4c8670bc3385d19c268ce1186708a3b1221dc900ec088670883383e1c8260e41106707a3383c1b8260dc1106706a358441ac1a0ce0b4680883403419c0e8041486369031a5818cac00413c5d2b83004c174260ba0f05d0580104b1262f093148494642c230124990921785507824852124230920f84907a27b4e13da10920f04906a26034124168940d04903a0104a1192408c5200208e17c5e10d1c05f1484169817b5a0f1a80789403c2a01e0500bdab0700f0380581c01c0bda705e9042f47217a310cd1c05e48830470181200bc110041182d098149540a41e0520b029038010430992004c5000207e0db5a06da10369781b4a40da4a06d230365481b2940d85206c250040f8180780c02c00819806d480369401a5200d25006548032940185e030220180f00c0580601c00c290100f0080580401c00c250061180307a0182d00c0e8040c8010260001f 10 11
def l_51 : Nat → Nat → Option Nat := unpackLinksF 0xe609e600e600e546e540e540e486e480e480e3c6e306e300e300e246e240e240e221e220e220e201e165e160e160e0a6e0a0e0a0e081e080e080e061dfc5dfc0dfc0df06df00df00dee1dee0dee0dec1de25dd09dd00dd00dc46dc40dc40dc40dc40dba5dba0dba0dae6dae0dae0dae0dae0da45da40da40d986d980d980d980d980d8e5d76cd760d703d700d6a3d643d640d602d5e1d5e0d5e0d507d4c2d4c0d4c0d3c8d3c0d3a1d3a0d305d2c2d2c0d2c0d1c8d1c0d1a1d1a0d105ceb3cdc7cdc0cce7cce0cca2cca0cca0cbc7cbc0cb82cb80cb80cb80cb80ca88ca42ca40ca40ca40ca40c90ac8e1c8e0c864c822c820c820c820c820c6eac6c1c6c0c644c3b5c3a0c343c340c2e3c283c280c223c220c1c3c163c103c100c100c0e1c007c000bfc2bfa1bfa0bfa0bec7be82be80be80be80be80be80bd88bd80bd61bd60bd60bcc5bc82bc80bc80bb88bb80bb61bb60bac5b873b787b780b6a7b6a0b6a0b681b5a7b543b540b502b500b500b427b420b3e2b3e0b3e0b3e0b3e0b2e8b2a2b2a0b2a0b2a0b2a0b2a0b2a0b2a0b16ab141b140b140b0c4b082b080b080b080b080af4aaf21af20aea4ac15ac00aba3aba0ab43aae3aa07aa00aa00aa00a9e1a9e0a945a921a901a900a8e1a8c1a806a800a800a800a7c2a7c0a6c8a6c0a6c0a6c0a54ca540a540a521a520a520a520a520a36ea360a360a341a340a340a340a1cca1c0a1c0a1a1a1a0a181a180a180a180a180a1809fce9fc09fc09f449f409f219f209e289e019e009e009dc29d449d409d409d409d409d409c679c609c419c409c409c409c409c409b679b609b609b039b009a849a429a409a029a0099c299c099c0998299809980998099809980998098e596f096e096e096e09645960295e195c195c0958294e594c194829480948094429440940293c293a193a093a093a09362936093609303912f9120912090a490a090a090629060904190409040904090408fc48fc08fc08fc08f638f608dec8de08dc18dc08dc08da18d248cc38cc08cc08cc08cc08ca18c818b2b8b208b208ac3871e86e186e086458640864085e385e085e085e085a2854384e38483848084808461838783238320832083018227822081e280c980c080828061806080607f877f427f407f407f407f407f407e487e407e217e207e207d857d427d407d407d407d407d407d407c487c407c217c207c207b857933784778407767776077607741766776037600760075e1750774a374627460742272ea72e072a272a072a071c771c0718271807180718071807088704270407040704070407040704070406f0a6ee16ee06ee06e646e226e206e206e206e206e206e206e206e206cea6cc16cc06cc06c4469b569a06981698068c668c068c0686368606860684167e3678366a766a066a066a06681668065e565c165a165816580656164a664a064a064a064a06462636863606360636061ec61e061e061c161c061c061c061c0600e6000600060005fc25fc05f255f205ee25dc95dc05d825c4a5c405c405c215c205b665b605b225b205ac35aa15a815a425a2159e259e0580f5800580057e157e057a257a057a057a0562c562056205601560055e155e055e055e05583558055805580558053ce53c053c053445340532153205301520851e151e051e051a2512451205120512051205120504750405021502050205020502050204f474f024f004f004ea34ea04e244e014dc24dc04d824d804d804d804d424d404d404d404d404ca54ca04ca04c624a704a604a604a6049c54982496149604922490148654841480247e147e047e047a247a0476247604741474047404702470046a346a04662448f4480448044044400440043c243c043a143a043a043a043a0432443204320432042c342c0428242804280424240cc40c040a140a040a04081400440003fa33fa03fa03f813f613f413f403f403f213f203f203dcb3dc03dc03d6339be38c738c038c038c038a138a0380537e137c137a137a0378136c636c036c036c036c0368235883580358035803542354034a534a0346233493340330231ca31c031c031a131a030e630e030e030e02f6c2f602f602f412f402f402f402f402d8e2d802d422d402ce32cc12ca12c622c412c022c002a2f2a202a202a012a0029c229c029c029c0284c2840284028212820280128002800280027a327a027a027a027a025ee25e025a225a0254325402502250024a324a024a0248124802480230c230022e122c122c022a12262226022412240224022022200202f202020201fa41fa01f811f801f611f601f411e481e211e201e201de21d641d601d601d601d601d601c871c801c611c601c601c601c601c601b871b421b211ae21ae01ae01a831a801a0419e119e019c11982198019801980194219401940194018a518a018a018621860186018221630162016201620158515421540150214e114c11425140113c213a113a013811380138013421340134013211320132012e212831280124212401202102f102010200fa40fa00fa00f620f600f410f400f400f400f400ec40ec00ec00ec00e630e600e220e200e200de20de00de00da20c2c0c200c010c000c000be10b640b600b600b030ae10ac10aa10aa00aa00a810a800a800a800a80092b0920092008c308c008c008c008c008c008c008c008c008c008c008c0084408400840084007e307e007e007e007e0064d029e00330001 0x1b2241dc91ce26507262737b12380420c3a0e5d804685013bd498fa04a6f2242eb831f3c14ba8086f4465e693ebc899212087cc032830117589921048bca07cea032f241720c08bce473e5939bc091f900e5d204682013bbc98f8c4a6ec242e8831f1414b9a087c2289df844f0c95f8248fc0057df02340c09ddc8cbbc27d7613240810f76064ff023dc144ed4227724bfb7246e8023ed80df6804dcf26480922ec81f39a0cbb105c7f822eb822756112eb247d782feb411f5807faa027e2251ef528774547b32a175123ec028f52141cc0467f013ba498f4e4a6e7242e5831e9814b90087a4257d1923e8815f4208cfd02774232e7c9f5ce4c8fc043cf0193e808f384bf9b246e5023e680df3204dc92647d922e5c1f3900cb9605c7d022b9491f280bf93047c901fe4409ee0927a5473d0238c90a4f3a4e7982717212386c24f2a0e790070e30233e0099ee0878e0327a0113d8917180b8f4045c6929e2c149e404f676a9c4a6cd9d246ced3b22293c3141b8c90c3212785082e2821b89205448c3324a591a4ac88a570451aa225ae2031e040c9e2046a325151238dfcb66fc5533a299be81870ca02ac4c2e146316952868a543212b7a08dbc82e3c4112ac07558050ab138ddc366ec15236099ba82ce2125ec892b8748fc2246d18a9e4052ee0263c192be0094ef848e972432505385c25b840c77b057bc029dd011aaa084ef027b7a5db7c98ec44a68c242e0831d6414a940877148b6e931d8494d16485bf063ac02952410edf1b3684c1b445ddb4a4e88506dc243b604992020b7c087686d9b5254da12eece916db263b3129a2090b7a0c765052a2821b692050a8c3628bdb0c52d152961092b602bda2152a1496b780c75f032770119b49450a8e35d2a98714cd700c3765013a261acc5ed62295b28c6492a4fa94ad5c2f49014b5605c770224e80ea520a13a271aa0547f0266a60b3728bdb8452db92fed697b694a7b2252d08a9e3e52ed8263b192bd7894eb648e7c2432305385825b740c75a057aa829d4811a72084ec02675821d400c9d2044ea245a702e3a41169e4a74d052738136e418e960a5b6042dc132d241f36c0cb4a27cda033d200cdae903324719d14cb58985aa903454719c94cce09e6884e34326944130c592a6825b3162918b34ece124e7c906d42450a049cf4209cc046d348152140ce9a9672d2b384959ba46a911ee6c0a5b304272811a949e548933342d999954cc89e662060e426033920b491944054a152950a04acb82365a0f9b30643381d1a40c0ce4a32b0d995054ca4264540f3466a7a134bb451968052f132959f947cf0a36764ff3527d98133a5c9948a14e12096d883338c10e5e06f2c0339401319808da08cb1e2bb8893ea30991c4087040322d811b391964a5171027d4593238010e060645a02366930b31206468e30f2998613cc889c6424d28826165a40c211c61c5331e8d98b960c5e2ee389270c48365122c6c24c86104df0238ba6cc64aa5928cb172bb8b145c549f5104c8de0438a01915008d909028628188c5ec422961ed4b0e69586a5ec312950c8f70b052d802137408cdc4f28649984954c209e60e060dc26024920c122f60714ac74652215279ca560417a430a58083e6c0190920743803024928bfc2a5fc131ef0799345ec9229640d4f1f69763232c74afe3457b182a789952c489fe144fb062673e13290429c2212dae0666d821c140de00066fd026240116b418df60a5ab042d6132be41f3560cafa27cd4833be00cdb6d42df69164a50b41244f0572882a146148bcc0c5ead22f44913a154bc8a45e251272289389449cca24e0512ef6c177260bb4b65d85826f28975860b792459e522dd6b174b48b392c5d09228b2b173948b98a25ca122db69571b46b5d2959892ae24756295dadcaadc20e56b0626c8219840c82c046de2896fc5eb76295b8d7adb6a56aa52b2d255b48ea9629b3d945b641ca900c4d70433001905408dac8d2d76a56ab4ab25255a891ad347b6215dad8aab4e0c6d20524002197c0c828046cf28966a34b422f59d14acc6a565b4ab292f59294ac847b4a94d9e8a2b4a0c6c70522c8219780c826046c56c162260af8b4554582c20a15dc5eaaa2ecf0d36c168b6004990020b48084d6023599549cca2018062be4d95e94caf09e5764b2b98d95c460adda856c942ab2d959150ad430566572aa4d959264ac4ae560552af2995713cab40c4e6512a10314e014a949e5464b2a00314d81468c109aa046a52894d014a8ca2532052a129950144a70265361129a0794c82c0300e55657aaa2bb5494da20a555051aa728b53144a909ed444b5a20626a021a7c0d53c0669d0314c01602c08d2cd62954b149158a1ca252812268289478189b8a24da5128f29936144a492e4d6952912994813ca380c50406275289408189cca25120626e2893f8149b4a24fc0526c2894134ea05a14fe0f27e0580401ca322f51714a8a2bd44152a1ca34d65168627b4292d684189a60868403541819a000c4fa058070233db489e9244d65226728139b449dc1c4ead32736a1392509c4a84e01426e2793692c9b00c4f117a768a53a35a9bdab4d6d3a6469b078499a820c200e5e4062d002134808cd05300803133a54998a64ca4f264258cf940344980064800c09004040985a94c0d2a5f4a52f24a958ad3c650a5d0bd2005283c254b81180303a01928968264b20f2f68bf7845bbaa2bdc914ee06a56c34ab452958c92ac32bf5f95eae8add6855eac2a74b952a4ca7d1a52e7c2953c9479a4a34c650e540b71f05383425bc210d9e062680219880dcb606658026010110300a4ac4a2530992803c934164aa092532632912993490c9c5100c0312823293c9f49a4ca544672883e9301733a5022d2711b04c67018336502492711a84c8d01e4900e247068a283033c984404a22a07867020334984884a2290791402c90c1448409054040cd03033010332500cb260091205ac201000c225059200288fc12016082042a91e86c81024408d3a344931d2418a0a4c72505980446501265ca02c4102366a51ab4a8d1254669196247b191298949099204963078b114c8c03645e1522e0791682c320980d40c22a4a514a4a8a0a544e51a2627d129321a896b2c0c86c0583513c88c36444152210991002c929a9c8cd2e454a720a4b8f919b2a4c8c72451e04b8042547611e3808d1b83f8c41f4580cd550651582f8901743e08c66044ca13231891418175ff07ca50327c8170b6089922646212287022bfc0f949064f882e168113220c1902810d1387f4263f40f2190710c0345141831e501f5270fe04c30c101844c215250f803c7b4164280a2130482a020304983ce4a1ef078c71303009031a0c0bf04108254630a017c4c011240a4040164183d60b20f0510702401c104191b2050c102c5d82924bf490609292f694162c1117a04a052d9038546289917848a050bb0204580c1f28a0ca0205c2a022624a0286101ff8bcff4527f5a93f8d29fb4bcfd25250d1ebf24a5eb2425d8124ac1e286531f70a8fb03c7d4161744c04b060f945e7c6293e0949ef494f715e7b4a93d84f9eb2642592d620190720b04b278f48547a0263ce0b21d8bd0dc5285da9c2cd2e124a708a4b83519b0e4c8b92450585f8202f40c14e010a50003f7e01f3e80cd39064f982f7a8173cc08c48044040147912a3c64a1e0098ee83c76c163c4091e0262ef92976c90810061dd464ee13e76c993c28cdde07ced02e6f5a8382d218a2a0ca1484d42e28a1414a090ea82c75da43ac521310a8ea04874c2225e1112e088968444c0223a2d81d04c0e79607383639a1812c088e024864c2437ed61cb690e5248648ac392521490b0e404871c2237ad29c568ce223968918b3a54990294e193a2dc9130c175770aa8c82e05811380111c18bcdfc526f9af37ad49bc472d0a3166ca931e529bb2745a92255026a701151805c0a8226dc2201a0b1b9498dc12845c1e36c0a1b5048d42302d01034ed01a2480599301f8900280c114058d98286c812016081a646059020695a0342900b12602b9204982a0260c113058d80286bc1200e08009058d6a4c6b09424a15116078d58286a8120fe4c1a80682c1304902234c0d0b02405792068d2215c4c0ad260c71382b09034ed49a5694d225e68929342929a048ccc952630a51564c19f254c005e5ac292901292308c8d83d6709a0fe4c19a248ceb5266da53328c58a294cc14665c9eb2c4b87e244c285d5d42aa220b812044c98446449a31c91058260c69246522f325149906a4c7b4a63118b165798a2a4c493d620970ae4895209a9b84544017022089866c0c29605f8342d2181832a0550205ee2f2d31753569ac1345604a4a2850580242548125cc2a2601100d058bf16c5f4262f80b17b038bcc6c5e2302eed41764c0ba9505a8362e4141730b8b496c5c8b22e2171700a8b784c5b81e2da0b0a8260b28444c0222c00b15c048b183c57c162b609158038538205949094c04963088ad024580262be1115c098ad8445681e01a0b157038ac04455c122d68c4a5244b505e5a42ead013545094b384659822ac81116207ab082e57816aba0b15904a058225580eaa8d6153490a91585402c28811121088a702c4ac2229c1312a08894844540ae2505514f098a683c530162800b1320889f82c2909826011146058958444f4122541114069c9fb424f41e0120b13b038948444ec12295179498a4a423128c9128e179450a4a20464a022a860f54205ca082d4f816278094070449d01d4e1a426e52128090900404c1a22684e132698983504bd2825c5412d0a09583c4a81625207124460510204911c142081358bc99c524c5ad258d592869c8eb4d44ca4a4e505262729293148c90940049210980482c480aa23e1311e0588e81c46da013e4c004060069240249201a520092808cb52461a522e969164848a95e450a92265291228c0212d44429220128042788704c434163b117dd28b6e645771a29b84d49ba694da25b6c529b5c92da9486cf231654a930e5289e244c205f5fc2f2f416d740aeb6053554292a213d4b0969c84a4d823a441191c0868d02f43c1721808c020446f25038924178540c62902205c150280b61210707884a48420a408015106090828440f82207a1103c0881f84440db0204981012c08006c3fc30076110e1290628483f5a41c0960fc490621583eca40b4160fa0907c8443d42201c0f0f74707b138090261e80e0f30686d1302e0181b2900d44605b9402949802c10021078788383c01a0160c0d82605b03035d201a68c0b5280519300d42a02a10020078770383b41a00e0c00a07875a383a89c06815023098748383a01a1bc928e648c72a3e3511919e548c2294599323909513a1748b0aa0f03e050191c2110e28bc7045237d2f1bc948dd47c69a32334a9182528b12646e12a1902688e1141d07c098322a0981b40d0a4260198443601a160480af2406aa442b89815a4c0c027056120365a91aed28d64bc6a25234d251a4918cb2a45f14a2ac981a24a8970bc40052164250641182707a671242a098198490cf4a466a4a32d19178528ca28c6493e294991904b49c0ba450550701f0240c8c508861924301221484c0bf2486345e31229184948c14945f2322f4af178548bb27c519322e8968c61344608a0d83e0441915c8c0b806856a300c42216c0d0ae4605a1242b518144510b224857a342c12715c908ad474562362a8a7150508a427450936258270fe10858074180362a89014e4d0a724054230298a21488c0a2270509202dda916ad28b34a458a4a2ad18152578a52a45194a280a313e4b4950bc3f05215c2505e1182607a4ea60270b01261a07c0c04d2502581012c480908bc3e45d111a6932d149849210a4125c9112a088880a81f8440381e1265b0920784882c2400e11d1b08d8c04636022d281145407d0d8438502202e0f85b0872c84305c2142a108130830784102c1fc980f0110770683fa301d82207e11073078378341c81e0dc0d06c0583481c1dc100ee480782443b0221cc260e41106f098370440381e0d60b068038360441ac1a0d211068068402321f8990fa1787c0ba3d84d150250f41187908a3a8441d01f0e20f4700783683502c190d40b46703a32b481912c0c6560610b0298440b4220c00f0600981d0440e422070110612b81b95417c260bc0f05d0582803c1042209e0f0582602c2300fc220aa0f03a0882834e13da10140f04c0582501c0e4220980d0380882503416e2f0b5148594642b9321582f0a81485308c1b8451481f0a20f44e0782683501c190960b44903a23a48118a406e1202c0801fb4410d1c082d303f6a01f2500f4a80781403a0781c82c0e00e0664c03106019a380c0100628e0302402245e10a29080d683b6ac1bb4e0a5a6840924364821aa390d1188644882f0441684c0281e0585502b0781502c0a40e04e90026280028400391a0148d00e49005240091ad046d08224bc10a520812503e9180547a0f152074a50381481b0940294c0641e0300b00f0880703c034160180700a0780482c0200e02cd48156940a25204d25024548112940805e02c2900e1280608c0283d010168060750a8be8245b3fa2b9f114cf26b677b533b1a59ced0ce34a46da4a3411918e548b92944f13226c2f9281788f0b644857204298cc1486209e2e04b1202508a11c2e08c140430941f8340f81706601032f45a7f8ed2fa868fc7b43e2925ee690f51477a6233d1ca5e4e50efc2777b93395c91c9612e1e086f283b76419a1608c010260001f 16 5 11 10 6
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsF m_51 g_51 bds_51 (dagRefF 978 (dagTraceF m_51 s_51 8 f_51) l_51 0) s_51 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 64 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_2 : treeBlockF 64 96 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_3 : treeBlockF 96 128 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_4 : treeBlockF 128 160 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_5 : treeBlockF 160 192 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_6 : treeBlockF 192 224 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_7 : treeBlockF 224 256 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_8 : treeBlockF 256 288 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_9 : treeBlockF 288 320 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_10 : treeBlockF 320 352 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_11 : treeBlockF 352 384 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_12 : treeBlockF 384 416 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_13 : treeBlockF 416 448 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_14 : treeBlockF 448 480 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_15 : treeBlockF 480 512 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_16 : treeBlockF 512 544 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_17 : treeBlockF 544 576 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_18 : treeBlockF 576 608 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_19 : treeBlockF 608 640 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_20 : treeBlockF 640 672 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_21 : treeBlockF 672 704 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_22 : treeBlockF 704 736 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_23 : treeBlockF 736 768 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_24 : treeBlockF 768 800 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_25 : treeBlockF 800 832 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_26 : treeBlockF 832 864 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_27 : treeBlockF 864 896 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_28 : treeBlockF 896 928 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_29 : treeBlockF 928 960 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_30 : treeBlockF 960 978 (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nj_51_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_1 (fun _ h1 h2 => treeBlockF_at nb_51_2 h1 h2)
theorem nj_51_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_2 (fun _ h1 h2 => treeBlockF_at nb_51_3 h1 h2)
theorem nj_51_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_3 (fun _ h1 h2 => treeBlockF_at nb_51_4 h1 h2)
theorem nj_51_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_4 (fun _ h1 h2 => treeBlockF_at nb_51_5 h1 h2)
theorem nj_51_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_5 (fun _ h1 h2 => treeBlockF_at nb_51_6 h1 h2)
theorem nj_51_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_6 (fun _ h1 h2 => treeBlockF_at nb_51_7 h1 h2)
theorem nj_51_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_7 (fun _ h1 h2 => treeBlockF_at nb_51_8 h1 h2)
theorem nj_51_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_8 (fun _ h1 h2 => treeBlockF_at nb_51_9 h1 h2)
theorem nj_51_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_9 (fun _ h1 h2 => treeBlockF_at nb_51_10 h1 h2)
theorem nj_51_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_10 (fun _ h1 h2 => treeBlockF_at nb_51_11 h1 h2)
theorem nj_51_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_11 (fun _ h1 h2 => treeBlockF_at nb_51_12 h1 h2)
theorem nj_51_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_12 (fun _ h1 h2 => treeBlockF_at nb_51_13 h1 h2)
theorem nj_51_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_13 (fun _ h1 h2 => treeBlockF_at nb_51_14 h1 h2)
theorem nj_51_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_14 (fun _ h1 h2 => treeBlockF_at nb_51_15 h1 h2)
theorem nj_51_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_15 (fun _ h1 h2 => treeBlockF_at nb_51_16 h1 h2)
theorem nj_51_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_16 (fun _ h1 h2 => treeBlockF_at nb_51_17 h1 h2)
theorem nj_51_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_17 (fun _ h1 h2 => treeBlockF_at nb_51_18 h1 h2)
theorem nj_51_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_18 (fun _ h1 h2 => treeBlockF_at nb_51_19 h1 h2)
theorem nj_51_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_19 (fun _ h1 h2 => treeBlockF_at nb_51_20 h1 h2)
theorem nj_51_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_20 (fun _ h1 h2 => treeBlockF_at nb_51_21 h1 h2)
theorem nj_51_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_21 (fun _ h1 h2 => treeBlockF_at nb_51_22 h1 h2)
theorem nj_51_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_22 (fun _ h1 h2 => treeBlockF_at nb_51_23 h1 h2)
theorem nj_51_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_23 (fun _ h1 h2 => treeBlockF_at nb_51_24 h1 h2)
theorem nj_51_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_24 (fun _ h1 h2 => treeBlockF_at nb_51_25 h1 h2)
theorem nj_51_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_25 (fun _ h1 h2 => treeBlockF_at nb_51_26 h1 h2)
theorem nj_51_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_26 (fun _ h1 h2 => treeBlockF_at nb_51_27 h1 h2)
theorem nj_51_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_27 (fun _ h1 h2 => treeBlockF_at nb_51_28 h1 h2)
theorem nj_51_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_28 (fun _ h1 h2 => treeBlockF_at nb_51_29 h1 h2)
theorem nj_51_30 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := block_join nj_51_29 (fun _ h1 h2 => treeBlockF_at nb_51_30 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 978 → (dagCheckNodeF m_51 g_51 bds_51 978 (dagTraceF m_51 s_51 8 f_51) l_51) i = true := nj_51_30
theorem lb_51 : LowerBin m_51 s_51 g_51 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xffffffff
def s_52 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_52 : Nat := 0x15571f7f
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 6, g_40), (m_32, s_32, 5, g_32), (m_34, s_34, 5, g_34), (m_36, s_36, 5, g_36), (m_38, s_38, 5, g_38), (m_41, s_41, 5, g_41), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_40
  · exact lb_32
  · exact lb_34
  · exact lb_36
  · exact lb_38
  · exact lb_41
  · exact lb_8
  · exact lb_9
  · exact lb_10
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_52 : Nat → Nat × Nat := unpackForestF 0x25048b28044005a7802d2e4d2b31e25d8f0ae4944da3c2a31e92f8f495c8c0f23d24f2023490c9248055241249200148f491c7a07e3d02f1e150005a3c648e23246b1b02f8dda046c09e32469191388c89a4640d0016871804400527c5495a2d2731524e8aca74544a40149710b5b885a9c4c4e6216a31095b884a9c4453a212a200a4786d264369121b2510d92486c1200290dfe8b50a35d850a8c2a4b61524b0a1507fa2b3fcd6e1069b081397f9ad41d161fe6af05c5e82ca8bfcd5a088c1043547f92bbfc4fe05498ff13b80cab3fc4e5fe26f0013c7fd223fc4cc0147efd1297e8943f449001476fb9417dc260028ddf52a2f8a567c5273e4559f125200a337b922bdc1100129ef5a487aca43ced3de8470f413879da180252dc76b8f223571da8bae8fdd7476f004c75d1bbb4d11dd468ed25476d1a3b4091d7466eb83f75c1bb8ed41d5692e3a5d73e3039edb1cf6c0e835073c9c38e8fdcd688e446072136390951c96a0e412871d1980251dbd298de9446f49e37a4d9bf05ee01306fc13b7a4d1bd028009436ec9c36a93db9250daa436d91f36c8c9b546a0093f6cca3360d35b026cd812e0049db5c9340126ed4b5c6a51c3524e1a9268ae35b69230348981a42d8d2160571abab8d3da0494d0246571a6b3c5355c68ace35c571a1b308f59946acc13d571222b856d9469aca136570ad2b855d8e8bcc725d63922b1c8f55c2acc4c5c629a6314931894a8ae13f61ca6308d5184498c213c5709dafad7180698c024c5f52a2fc5117d098ae1375c5ad2e2d59714b4bbb505dca82e29597149cb8a425c41f2e415171064ae1365bca62c4d516c488b613c589222d091169268b4134588b22c44f163488b213458c9a2c40515c266b014c57daa2b807d5d6a8ae01700499ab093958498ac24400497a2716d534c0a996c54cb022715d136ae89b4f44da3a26969496a2a5a3a52d1b292d41492ba89a5651c9aa269391349689a434f9a6a7cd153e2b49f1564f89ea7c4d5134849e13c44cada725393925a8995a4dd2c22655d338bc99b514cd22a26559314a08994f49e2d25c541278ac93b5a49dab24e9352748a9394949ca0a26539234b89194448c9e22652d214808994747ca62389511c2888e13c44ca1a28569142ac8a14d45ca62284d5152688a12d44ca10024ad0568487b5043ca420a93d0b6a085b4042ca820a91d0749a83a4541c9ea0a50905078009273ae2da048d1004c08016c3ae2b9fc910eb4967e2443ad219f2d44f968a759563c22d1ec540f08ac7835a3c1ab1e0524f0282781393aca71d8908ec29c761423ac9700248c0109e6c24b361239cc4e4d847e72129361199c0d34e107870136360999b8908dc29c6e142360959b4538d82466c046004251ac4e4cc6a26a14e330a899b180cd4c06696c33c9a19a580cd2a866133004239940a4a54865293d2949b98692cc34866184b30c2194a4d4c10525292f2fc1f14a10cac6a45e05c2b1229588f4ac2a45605e2dc12158148ac08a58a322c4a69624b4b1064560442b52815a910ad2885602629411954110a62645303e29c2214c0c8a50360084628ca8928d58942b64fc6027db612855c9429e4a1432552d134d40954ac4aa4e2552112a568952ac4a1390041f9245040106e482541622f8b116c8b4d84596c22cb00b115c8668843244218a410c510588a641b5120ca88b09587c8b4401501f22b0f8d687c6ac3e139161270f4950582be2c15b1d6360eb180754d82c1571c0ae0e05507028838134160a98dc9105829e35b5c1ac9a0b052c694b82c14718dae0cc930634a83194418c9a0b050c594b4303501652b0b2938594842c95a164ab0b2538592842c129004178acd60158be0ac5b145b00a25b0512c00ac57131a40989104c29026144056298944e04749c2414c11c9482ad683e8bc21b4410ca207d1483e4b4201500f92b07c4a4156841e358054af82a56c378d81bc600ddb002a55c322b8191540c8a60644d0152a617b500bda402a53c2d2980a94b0a9a8054d001528e12a5409ca204a530252680a9430592f042910214680b2520592502c918162b40e350058ab02c538174880c13405caa02c50815262008270122d822980112d8024570112580890c0d6a2021560162d014540058ac02b5a015ab00a524052820214e0040f8049080102e0001f 10 11
def l_52 : Nat → Nat → Option Nat := unpackLinksF 0x436021b010c84854442a021405098284a0c1f1a0f03074183a041a0e0c05060082e0c17020b0304848220c11020412ff8a7fc03fc09fe00ff007f60bf909fb84fd427ea03ed21f680fa837d403ea01f386f9c07c81bdf15ee06f6827b403d515e906f4027a003cb15de9cef4077a03bd01de80ef407702bb609db00ed8076c03b601da04ec4375e13af01d780eac475603a909d480ea4074a23a501d280e8c273e239e05cd86e6c071e638c0dc600e2c170e23705db800dc006e0036d0db488da406c6336301b006d7436ba035425a610d300698034811a400d200688234401a200d0826744338099b82cc466600b2f059780cb03654132a019482ca406500b24119182c8c06344b1a018c04c5c162e0317018b80c5816242312018804c4006200310018782c2c460252ff097e84bf405f612fb017d80be815f012f8017810bc005d822ec017486ba405d202e5116e90b7405b612d7116988b2c85940ac6116300b18058c02c601608ab00157e0abe055f00ad495641ab2015900aa0a55002a4115200a804538229c014d04a40a51e0a8f014780a2855101288014382a1c050c0a7e213f009f804fc027c093b8a9dc04ec0a75053a029bc54de026f0137809ac44d6026a05320c99004c60a6301318098c04c01a5f052f8097c04be025e0527209380494224809240091044860a430121029002480023f051f808f8147812351d1a808d014621a31011802849e424021201090083c3416220a050500828040c22040900087f043f411fa00fd007e803f011f800fa867d403e611ef10f6067b003d801ec00f5827ac03d601e128f08077c23be01df00ed8876c03b211d900ec8076403aa21d500e90674803a401d104e88074403a201d100e880740138861c304e18070c037e21bf00de066f0037609ba04dd006d8436c01b504da026d0036411b200d88269ca320b98c10c6006300310218800c4006200308218400c2006100300218000bd0c5e022f0017608bb005c842e4016f0cb7805ac42d6016b00b4065a002d0016704b38059c02ce016700b38057892bc015e00af0056c32a6415204a90054802a4014f0ca780538129c014e00a6825244292014900a480518328c014504a2804f4827a013a0c9d004dc326e0137009b804dc026c093600988a4b8325c012b0c95804ac0256012b0095804ac024c292600918648c0240191f048f804703236091a048d0046802320919008c804640232011900898c44c02260113008806414b20a0104048200410020609000c7c103e001ec10f40879823cc01e018ef0477023b801dc00ed0476803b401da00ed00738c38461c200e004700037c11ba10dd006e8037011b020d8006c0036001b000d4106a0035001a020d000680033c119e00cf00678031c818e00c6046204310018608c3005f882fc017e00bf005f802ec417600b9085c802e4016e10b6045a042d0016800b30459802cc015a30ad0056802b0115800ac0056002b0015800ac005210254f12a00930849022480124009200478623c011c088e0046822205110008704438021811042082004100208010010800040001fc10fe0077203b801d420e80874003a001d000e218710038021c000de086a1435001a800d0106800330419800ca0861102f8417c00bc085e002d0816800b4005a002c0416000ae0857002b8015810ac0055042a8015010a4104a201d9e0e420700838001a860d0106608330018840c4006200300418000c00060003000150c090604800230400c40001 0x25148b2804423c178aa09e1949b07a3d64c98aac4ad032464702f1501382607e4d2b2a99512300f8a405d022410bb4d5551d2028c9532752513604816c2cd312e2990aa4c9109048c0f2432892081490c9248249244469211543d8a64800500a2990a23d92097c8e4ae4524f1f92322c178a209e3e03f1e8179312ec268f64b2b9249518f0a82a44acff2464502f1401382007c8905a270258dda04700be3604e4382f1341390c07c4c02f1d2388e51ac6a8d234271199348c81a10a0bc4b04f172453202a460111ac283169396a898b5690a2b29cd51428b92b458939a8287151293a02d423182086a8630548463418a1521169b04a4d69ca0c4c4e5a42629ca604ccaa188151394d061854699212788ea2229cd21424e496c50d6e0f6b313b53895a8c0e8fe242b69c15988ca9c42545a3266a892b39c2518e118c20890fa4c8792243a4a21c2490d82483a2ab2a4c61625b0a925861aec2e546142a106464825ae418d561169b0813946898c1d1620c6b10645e82122bd65660b2a304c60821aa220d70ec698dba34814a44004d1a14a102a4c451203d8969cf4acdda4e611212388e90f46cf595a80cab1d84b91425a7305a3042b1e0d31a02a0ff9308009e228921ff4889515c5d49a43316a138ad0935b83dad41ad5e0a6ad03a577a8adb9c55dba29ed9149688a1b3e5060627f0213b8089cc024ddfe2668993154095a1c49ce50b4600567f094bf64a1fa24891a3a42d1b1d84e90d26cf9a4d7e0a0b3a4c54f256851277dc263d0565f52a2e5145670a09e04e4ec262f4a5a7212b37293966484f415a7c8ab1da538ec2847205a7d12b3e6939e72b6e39576e0a7b3650df12527185a7bd22bdc1107905e1d8277b12432a541eb2908d1407a51c3d04e1ea69ef3b435391d326509382745084f1e01f8740dc7705e1c827735203a6935cc482e8a3d7911aa9a4a8a009ae81385309c3bc8c14b250f004c775223b6091dd468eda34779a23b8951c9250ed0242689c3c48fde1476efa3776519a944a9d807eeb8371d81787009dd5692e8b41740a43a0d41d38c0e936c745b039e4e1cd688e4928725a8399181cb4d8e5254720943cad71e36a2eb3507512eb9c8fdc7466a412a2781f8e80bc3604e3982f0d4138e40bc3404e3882d0c812b804c1c105edf827714a6388511c3278e11366f89a0de0fc3106ede8146722e1d8d21b7488dd9386d9a21da911b9250763493b5a0b6e8f9b6464d834e6e927b7090db546aa312a274278da0bc2e04ed9946670971d84e4f0262921293f890b38d34ee4747613a4349b364d35454767ea336c49b3604b86a07e1603703c17b34501ae49acb9301a01785209dac6b8d5a385e4a23544e1a9268bc1345dc9a178111a78c0d3260694b62345a17a2c8d216063caa2ec4d0bb0a8c22483b0a02ea4d1a1494d024650d1d2128d9952b4c71566309eb044d4e20b45d056671a6a848e90846ccf14d671ae2cc8e174288761386049eb144d58b25ac01256051eb328d59a47acc13d62497b0c4ad7f24eb71231941785009d5f03eae8176453232ad3541474c89554689d3284d9912b05a8542cc2a164111918bcc825d5e92ab1e9158e47aa012a334229601118b698c524c6322e3129513f490c29484349a30e5316c2688a934619aa30a931164889395c6109e302d3180498b69205f81e2fc511826b8bfa544f91c22c4e16b260be84c2b8222f0d41772a0568444549c2e41517b6b4bd3565e52d2ec9597549cba2424591f1d88f51d2527e1213802d1581597307cb88321901684a0956d468b51545bca62ca05169288b20145b5222d05516c278b18145a4922d24d16a488b4134590922c84d165488b19345b9aa2d6911672c87895c5989e1d84b162028b014c57daa00a57097278aeb546a1adb46d5da269ecfb4d675a2b36d0d97488a223b4f51d20c8d8fb466cb15b64cad32455d8d2acc413f60c9da264e97c26eb8136584999be168cc0ae55856270278c40fc2406e0702f5780fab805d5a49caca4c561222829012f2b89614c468a025c931554c0aa16c54cb025a5313c4c09995450d282389212a2b87614048d28284900ec2a09494c4dd2aa825094c474a5a36535a8a94d41492ba7734e51c9aa50971242887713c3b09624e9711d288761202a822286d354268a98a4d48522a82569402ac9f93d4f89a9bc168a90ac9aa644f09e26a5553a29c8d1424e496a6e961352b09ac5e4b1aca68d453348a98a50494ac2305412e2a08b9344be2d25b1592c6b495b563b1a7230d352a49a94a454a0a4a4e504dd0b45405647ca224a971242889193c3b096242900ed2b88f14047ca622e531184b88f254474a22384f0a70888b93445ca622a4b1152688d15a464ab1da5391829a869364589a9e04b91425a6e05a2982b2ad16d528aea8b57541a7a9ed1d4e4b4a42565192728a92d444869ea424ecada70569362ae991564c0a7a4c539222969014746ca1a26508db0b452856441a6a18d14ec47486a36441a81d8d01092a087948435a8218d010b2a08414042526a10914ee47a8393d445a121c93d0a48e75a3d418a120a0f0f72b87a14c4091a1ec531014c08016c3e4aa1ea530fe4887915c3c0921f8910f12b87713c3b0961e8d64fa6a27cb453d8a81ef168f58ac7a35a3cdab1e4524f1282781393b0989b4168ee4847694e3b0a120716cff8ae7ea4b3ed219f0558ef29c7592e3642d1b0110e228273139370989c84a4e10787134d3791d1b84e8e026c6f242374a71b8508da29c7424b39d239ca8fce34666f93336c959b248cd808c691413589c99c4c4d14846a14e338a119e4d0d28c068a60340b619c580cd2a86ab5134ca89984ccbd062650292d81098c92cc54866204b30c2197608cba06260829298109724c8bf07c5b0322d022178170ae0a8568242c822162110b70485a2322cca695c514b225a588322a80d15e940ae488569442f5a9176914ba47a5c9522a495170178b60a45a8452c02214c0a8ac04c5504429c221524c8a807c53032325219904f4c726e611353009797c10cab0465281b258ac9465449b4904b148268a41411809f6d84c938260a412e9209a6a04da5a2652b130938974844b15a254ab144d58a12b64f157274a793850c94272491412412a1029707e4984024c235360fe9308c2d845960225a211091087290431441f9ac908d445c2b241951200a81031687f8ac3f35a1f5ab0d8524672823e139164988f4950614702e138180940ef1b0768c03aa6c17c940e6570722a8389441c09a0dc9105e2503635c1ac9a0cc500694b832940199260ced70654a82ea38190a20b24e063268303501852d0be9585e49c2ea42170ad0b65585a29c2c94223e2f91d16c8a8ae42c532092b0f6938792be3c15b1d0ab8de54c6d29e3514b1a0a38c450c582522b358115a0082d00536c02916c144b0088900434802135013da409c9104d290261441289c0905304949c20a4211c9483a4844468821944100a808b178428a420a5a0fd2b0605342a28a1f12905890878d60232600e9400e636071180376c01113008490040900352b81a1540cca60644d0306a017b4807d2005a5301924015b500a9a00505001e2601393c0649804e510284a81314c058a004a4d02248810a3406498038d40182880c1340652202e550234bc1025207d2503c9181d2b40d956068a702c508558be2a45b1422b89714c466b41eb420ecaf87456c362ae189530b8a785852c2928e1214305498816570082980524c049300225b0092980325c0152e010d640d6a20515002e2d013158086b403b56018a480a504138b60845703d2581c90c0c2ac0214e0092149ed3e4e6971db478c5a1c5e93e294971024786921bfa8fdf9476fb2377c119bda53de6296e31476f0a1b684fdaf276d693756c99aae4bd12256821273a8919d213cd709465847290231260fc9106e2b82f0501380607c0102e0001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsF m_52 g_52 bds_52 (dagRefF 594 (dagTraceF m_52 s_52 8 f_52) l_52 0) s_52 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : treeBlockF 0 32 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_1 : treeBlockF 32 64 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_2 : treeBlockF 64 96 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_3 : treeBlockF 96 128 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_4 : treeBlockF 128 160 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_5 : treeBlockF 160 192 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_6 : treeBlockF 192 224 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_7 : treeBlockF 224 256 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_8 : treeBlockF 256 288 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_9 : treeBlockF 288 320 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_10 : treeBlockF 320 352 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_11 : treeBlockF 352 384 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_12 : treeBlockF 384 416 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_13 : treeBlockF 416 448 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_14 : treeBlockF 448 480 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_15 : treeBlockF 480 512 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_16 : treeBlockF 512 544 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_17 : treeBlockF 544 576 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_18 : treeBlockF 576 594 (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
theorem nj_52_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_52_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_52_1 h1 h2)
theorem nj_52_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_1 (fun _ h1 h2 => treeBlockF_at nb_52_2 h1 h2)
theorem nj_52_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_2 (fun _ h1 h2 => treeBlockF_at nb_52_3 h1 h2)
theorem nj_52_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_3 (fun _ h1 h2 => treeBlockF_at nb_52_4 h1 h2)
theorem nj_52_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_4 (fun _ h1 h2 => treeBlockF_at nb_52_5 h1 h2)
theorem nj_52_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_5 (fun _ h1 h2 => treeBlockF_at nb_52_6 h1 h2)
theorem nj_52_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_6 (fun _ h1 h2 => treeBlockF_at nb_52_7 h1 h2)
theorem nj_52_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_7 (fun _ h1 h2 => treeBlockF_at nb_52_8 h1 h2)
theorem nj_52_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_8 (fun _ h1 h2 => treeBlockF_at nb_52_9 h1 h2)
theorem nj_52_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_9 (fun _ h1 h2 => treeBlockF_at nb_52_10 h1 h2)
theorem nj_52_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_10 (fun _ h1 h2 => treeBlockF_at nb_52_11 h1 h2)
theorem nj_52_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_11 (fun _ h1 h2 => treeBlockF_at nb_52_12 h1 h2)
theorem nj_52_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_12 (fun _ h1 h2 => treeBlockF_at nb_52_13 h1 h2)
theorem nj_52_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_13 (fun _ h1 h2 => treeBlockF_at nb_52_14 h1 h2)
theorem nj_52_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_14 (fun _ h1 h2 => treeBlockF_at nb_52_15 h1 h2)
theorem nj_52_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_15 (fun _ h1 h2 => treeBlockF_at nb_52_16 h1 h2)
theorem nj_52_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_16 (fun _ h1 h2 => treeBlockF_at nb_52_17 h1 h2)
theorem nj_52_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_17 (fun _ h1 h2 => treeBlockF_at nb_52_18 h1 h2)
theorem nc_52 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_52 g_52 bds_52 594 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := nj_52_18
theorem lb_52 : LowerBin m_52 s_52 g_52 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_52 sub_52 gl_52 rc_52 nc_52

def g_53 : Nat := 0x1115155715571f7f
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 9, g_51), (m_50, s_50, 9, g_50), (m_49, s_49, 9, g_49), (m_48, s_48, 9, g_48), (m_46, s_46, 9, g_46), (m_43, s_43, 9, g_43), (m_52, s_52, 9, g_52), (m_45, s_45, 8, g_45), (m_44, s_44, 8, g_44), (m_42, s_42, 8, g_42), (m_47, s_47, 7, g_47), (m_16, s_16, 7, g_16), (m_12, s_12, 7, g_12)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_51
  · exact lb_50
  · exact lb_49
  · exact lb_48
  · exact lb_46
  · exact lb_43
  · exact lb_52
  · exact lb_45
  · exact lb_44
  · exact lb_42
  · exact lb_47
  · exact lb_16
  · exact lb_12
theorem sub_53 : ∀ b ∈ bds_53, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_53 : Nat → Nat × Nat := unpackForestF 0x62ff261f47fc98062be23916b62d4e51c8b4b14b6294c525a27c2ace4998519803f 4 11
def l_53 : Nat → Nat → Option Nat := unpackLinksF 0x4c2613090bcde0e170381a2d068341a0c1602883201 0x7a3f826172601a3362394a39227c1d6712668c5f6c575b5b5353434b3a5b32532a4b0a33003f 9 4 11 5 5
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsF fullMask g_53 bds_53 (dagRefF 18 (dagTraceF fullMask rootStock 11 f_53) l_53 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 18 (dagCheckNodeF fullMask g_53 bds_53 18 (dagTraceF fullMask rootStock 11 f_53) l_53) = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 18 → (dagCheckNodeF fullMask g_53 bds_53 18 (dagTraceF fullMask rootStock 11 f_53) l_53) i = true := fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2
theorem lb_53 : LowerBin fullMask rootStock g_53 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_53 sub_53 gl_53 rc_53 nc_53

def wg : List Gate := [⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [1, 0]⟩, ⟨GateOp.and, [7, 0]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [10, 2]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.and, [12, 1]⟩, ⟨GateOp.or, [13, 9]⟩, ⟨GateOp.and, [12, 0]⟩, ⟨GateOp.or, [10, 2]⟩, ⟨GateOp.and, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008372904 * 2 ^ 32 + 3936936064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008372904 * 2 ^ 32 + 3936936064)) (13 - 1) := by
  rw [show canon fullMask (4008372904 * 2 ^ 32 + 3936936064) = g_53 by decide]
  exact lb_53

end PEqualNP.Outside.L_meta_47747

theorem PEqualNP.Outside.L_meta_47747 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372904 * 2 ^ 32 + 3936936064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372904 * 2 ^ 32 + 3936936064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47747.table2_from_lowerBin (4008372904 * 2 ^ 32 + 3936936064) 13 PEqualNP.Outside.L_meta_47747.root_lb PEqualNP.Outside.L_meta_47747.wg 18 rfl PEqualNP.Outside.L_meta_47747.wfits PEqualNP.Outside.L_meta_47747.weval
