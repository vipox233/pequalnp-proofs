import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49393

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

def m_1 : Nat := 0x5500550000000000
def s_1 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_1 : Nat := 0x100150000000000
def ep_1 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_2 : Nat := 0x3300000033000000
def s_2 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_2 : Nat := 0x100000013000000
def ep_2 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_3 : Nat := 0x3300330000000000
def s_3 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_3 : Nat := 0x100130000000000
def ep_3 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_4 : Nat := 0x5050505000000000
def s_4 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_4 : Nat := 0x10105000000000
def ep_4 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_5 : Nat := 0x4444444400000000
def s_5 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_5 : Nat := 0x4044400000000
def ep_5 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_6 : Nat := 0x5000500050005000
def s_6 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_6 : Nat := 0x100010005000
def ep_6 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
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

def m_7 : Nat := 0x3333000000000000
def s_7 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_7 : Nat := 0x113000000000000
def ep_7 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_8 : Nat := 0x5555000000000000
def s_8 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_8 : Nat := 0x115000000000000
def ep_8 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_9 : Nat := 0xc0c00000c0c0
def s_9 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_9 : Nat := 0x40000040c0
def ep_9 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_10 : Nat := 0x4040404040404040
def s_10 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_10 : Nat := 0x4000404040
def ep_10 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_11 : Nat := 0xff000000000000
def s_11 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_11 : Nat := 0x17000000000000
def ep_11 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_12 : Nat := 0xc000c000c000c0
def s_12 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_12 : Nat := 0x40004000c0
def ep_12 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_13 : Nat := 0xf0f000000000000
def s_13 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_13 : Nat := 0x107000000000000
def ep_13 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_14 : Nat := 0xc0c0c0c
def s_14 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_14 : Nat := 0x4040c
def ep_14 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
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

def m_15 : Nat := 0xc0c0c0c0
def s_15 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_15 : Nat := 0x4040c0
def ep_15 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
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

def m_16 : Nat := 0xff0000000000
def s_16 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_16 : Nat := 0x170000000000
def ep_16 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_17 : Nat := 0x5050000050500000
def s_17 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_17 : Nat := 0x10000010500000
def ep_17 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_18 : Nat := 0x30c030c030c030c
def s_18 : List Nat := [0x104010401040104, 0xc000c000c000c, 0x30c0000030c, 0x30c030c]
def g_18 : Nat := 0x10403040304030c
def ep_18 : Nat := 0x200000800000200000000080000000000000000000000000000000000000000000000000104000400040000
theorem epk_18 : ep_18 = edgePack m_18 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_18 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 10 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 10 (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 10 (dagTraceF m_18 s_18 4 f_18) cur_18) = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 10 (dagTraceF m_18 s_18 4 f_18) cur_18) i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xff00ff0000000000
def s_19 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_19 : Nat := 0x100170000000000
def ep_19 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_19 : ep_19 = edgePack m_19 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_16, s_16, 4, g_16), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_16
  · exact lb_1
  · exact lb_3
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_19_1 (Nat.sub p 32)) (cc_19_0 p) (Nat.blt p 32)
def f_19 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 43 bds_19 (dagTraceF m_19 s_19 6 f_19) (cur_19 0) s_19 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 43 (dagTraceF m_19 s_19 6 f_19) cur_19) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 43 (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 43 (dagTraceF m_19 s_19 6 f_19) cur_19) = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 43 (dagTraceF m_19 s_19 6 f_19) cur_19) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 43 (dagTraceF m_19 s_19 6 f_19) cur_19) i = true := nj_19_1
theorem lb_19 : LowerBin m_19 s_19 g_19 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xffff000000000000
def s_20 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_20 : Nat := 0x117000000000000
def ep_20 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_20 : ep_20 = edgePack m_20 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_11, s_11, 4, g_11), (m_8, s_8, 4, g_8), (m_7, s_7, 4, g_7)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_11
  · exact lb_8
  · exact lb_7
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_20_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_20_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_20 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_20_1 (Nat.sub p 32)) (cc_20_0 p) (Nat.blt p 32)
def f_20 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 43 bds_20 (dagTraceF m_20 s_20 6 f_20) (cur_20 0) s_20 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_0 : treeBlockF 0 32 (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) cur_20) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_1 : treeBlockF 32 43 (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) cur_20) = true := by decide +kernel
theorem nj_20_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) cur_20) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_20_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_20_1 h1 h2)
theorem nc_20 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 43 (dagTraceF m_20 s_20 6 f_20) cur_20) i = true := nj_20_1
theorem lb_20 : LowerBin m_20 s_20 g_20 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xffff00000000
def s_21 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_21 : Nat := 0x175700000000
def ep_21 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
theorem epk_21 : ep_21 = edgePack m_21 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_21 g_21 ep_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xff00ff00000000
def s_22 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_22 : Nat := 0x17005700000000
def ep_22 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_22 g_22 ep_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xf0f0f0f000000000
def s_23 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_23 : Nat := 0x10105000000000
def ep_23 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0x5050505050505050
def s_24 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_24 : Nat := 0x10105010505050
def ep_24 : Nat := 0x1040400000001040000040000010004000400000000000000000000000101000100000000000000000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_17, s_17, 4, g_17), (m_6, s_6, 4, g_6), (m_10, s_10, 4, g_10)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_17
  · exact lb_6
  · exact lb_10
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_24_1 (Nat.sub p 32)) (cc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 43 bds_24 (dagTraceF m_24 s_24 6 f_24) (cur_24 0) s_24 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_0 : treeBlockF 0 32 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_1 : treeBlockF 32 43 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) = true := by decide +kernel
theorem nj_24_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_24_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_24_1 h1 h2)
theorem nc_24 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) i = true := nj_24_1
theorem lb_24 : LowerBin m_24 s_24 g_24 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0x5555555500000000
def s_25 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_25 : Nat := 0x115155500000000
def ep_25 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_8, s_8, 4, g_8), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_8
  · exact lb_4
  · exact lb_5
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_26 : Nat := 0x666600006666
def s_26 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_26 : Nat := 0x64600004666
def ep_26 : Nat := 0x402000000000000000000000004000000020000006020000020000000000000000000000000000000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_26 : KnownBin bds_26 := by intro b hb; simp [bds_26] at hb
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp [bds_26] at hb
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_26] at hb
def cur_26 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31243048c4f080a193c202928f611ab92a524c80a8413000f 7 127 3 7 10 1023 15 32767
def f_26 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 10 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26 : treeBlockF 0 10 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 10 (dagTraceF m_26 s_26 4 f_26) cur_26) = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 10 (dagTraceF m_26 s_26 4 f_26) cur_26) i = true := fun _ h1 h2 => treeBlockF_at nb_26 h1 h2
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x66006600660066
def s_27 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_27 : Nat := 0x6004600460066
def ep_27 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_27 : KnownBin bds_27 := by intro b hb; simp [bds_27] at hb
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp [bds_27] at hb
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_27] at hb
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31243048c4f080a193c202928f611ab92a524c80a8413000f 7 127 3 7 10 1023 15 32767
def f_27 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 10 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 10 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 10 (dagTraceF m_27 s_27 4 f_27) cur_27) = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 10 (dagTraceF m_27 s_27 4 f_27) cur_27) i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0x3030303030303030
def s_28 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_28 : Nat := 0x10101010101030
def ep_28 : Nat := 0x1000002000001000000000200010000000000020000000000000000000000000000000000010101010101000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_28_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 64 bds_28 (dagTraceF m_28 s_28 5 f_28) (cur_28 0) s_28 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 64 (dagTraceF m_28 s_28 5 f_28) cur_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 64 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 64 (dagTraceF m_28 s_28 5 f_28) cur_28) = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 64 (dagTraceF m_28 s_28 5 f_28) cur_28) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 64 (dagTraceF m_28 s_28 5 f_28) cur_28) i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xc0c0c0c0c0c0c0c0
def s_29 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_29 : Nat := 0x40004040c0
def ep_29 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_15, s_15, 4, g_15), (m_10, s_10, 4, g_10), (m_12, s_12, 4, g_12)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_15
  · exact lb_10
  · exact lb_12
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

def m_30 : Nat := 0x5555000055550000
def s_30 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_30 : Nat := 0x115000011550000
def ep_30 : Nat := 0x1040000000000000000000000014000000440000010400000000000001100000110000000000000000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_30 g_30 ep_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xf0f00000f0f0
def s_31 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_31 : Nat := 0x1050000050f0
def ep_31 : Nat := 0x40a0000000000000000000000040000000a0000000000000000000001000000000000000105000005000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xf000f000f000f000
def s_32 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_32 : Nat := 0x100010005000
def ep_32 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000100010005000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xf000f000f000f00
def s_33 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_33 : Nat := 0x100070003000700
def ep_33 : Nat := 0x200000000000600000004000000000000000000000000000000000001000200030002000100040000000400
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xffff0000
def s_34 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_34 : Nat := 0x13570000
def ep_34 : Nat := 0x440000000000000202000000000000130200000000000010540000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_34 : KnownBin bds_34 := by intro b hb; simp [bds_34] at hb
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp [bds_34] at hb
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_34] at hb
def cur_34 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_34 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 1 bds_34 (dagTraceF m_34 s_34 3 f_34) (cur_34 0) s_34 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34 : treeBlockF 0 1 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 1 (dagTraceF m_34 s_34 3 f_34) cur_34) = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 1 (dagTraceF m_34 s_34 3 f_34) cur_34) i = true := fun _ h1 h2 => treeBlockF_at nb_34 h1 h2
theorem lb_34 : LowerBin m_34 s_34 g_34 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xff00ff00
def s_35 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_35 : Nat := 0x13005700
def ep_35 : Nat := 0x44000000000000000000000000000200020000000000130002000000000010005400
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_35 : KnownBin bds_35 := by intro b hb; simp [bds_35] at hb
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp [bds_35] at hb
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_35] at hb
def cur_35 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_35 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 1 bds_35 (dagTraceF m_35 s_35 3 f_35) (cur_35 0) s_35 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35 : treeBlockF 0 1 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 1 (dagTraceF m_35 s_35 3 f_35) cur_35) = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 1 (dagTraceF m_35 s_35 3 f_35) cur_35) i = true := fun _ h1 h2 => treeBlockF_at nb_35 h1 h2
theorem lb_35 : LowerBin m_35 s_35 g_35 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xf0f0f0f0
def s_36 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_36 : Nat := 0x105050f0
def ep_36 : Nat := 0x40a000000000004000a0000000000000000000000000100000000000000010505000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xf0f0f0f
def s_37 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_37 : Nat := 0x307070f
def ep_37 : Nat := 0x4080000000000040008000000000000000000000000030202000000000000040400
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xf000f000f000f0
def s_38 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_38 : Nat := 0x100050005000f0
def ep_38 : Nat := 0x4000a000000040000000a00000000000000000000000000000000000100000000000000010005000500000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xf0f00000f0f00000
def s_39 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_39 : Nat := 0x10000010500000
def ep_39 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
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

def m_40 : Nat := 0x5500aa005500aa
def s_40 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_40 : Nat := 0x150002005500aa
def ep_40 : Nat := 0x4000a800000000000000000000000000000000000400020000000000100002000000000000000000000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_40 : KnownBin bds_40 := by intro b hb; simp [bds_40] at hb
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp [bds_40] at hb
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_40] at hb
def cur_40 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x324438cd0ce2343492f61abad54a4744a80f 7 127 3 7 6 63 11 2047
def f_40 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 10 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40 : treeBlockF 0 10 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 10 (dagTraceF m_40 s_40 4 f_40) cur_40) = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 10 (dagTraceF m_40 s_40 4 f_40) cur_40) i = true := fun _ h1 h2 => treeBlockF_at nb_40 h1 h2
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0x4444444444444444
def s_41 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_41 : Nat := 0x4044400444444
def ep_41 : Nat := 0x40400000000440000044000004004000440000000404000000000000000000000000000000000000000000
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

def m_42 : Nat := 0x55550000aaaa
def s_42 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_42 : Nat := 0x1555000002aa
def ep_42 : Nat := 0x40000000a8000004000000020000001000000002000000000000000000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_42 : KnownBin bds_42 := by intro b hb; simp [bds_42] at hb
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp [bds_42] at hb
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_42] at hb
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x192440619343061134349253d84d5d2d549481a105800f 7 127 3 7 9 511 14 16383
def f_42 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 10 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 10 (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 10 (dagTraceF m_42 s_42 4 f_42) cur_42) = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 10 (dagTraceF m_42 s_42 4 f_42) cur_42) i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0x55005500aa00aa
def s_43 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_43 : Nat := 0x150055000200aa
def ep_43 : Nat := 0x40000000a80000000000000000000400000002000000100000000200000000000000000000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_43 : KnownBin bds_43 := by intro b hb; simp [bds_43] at hb
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp [bds_43] at hb
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_43] at hb
def cur_43 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x192440619343061134349253d84d5d2d549481a105800f 7 127 3 7 9 511 14 16383
def f_43 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 10 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43 : treeBlockF 0 10 (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 10 (dagTraceF m_43 s_43 4 f_43) cur_43) = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 10 (dagTraceF m_43 s_43 4 f_43) cur_43) i = true := fun _ h1 h2 => treeBlockF_at nb_43 h1 h2
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0x2222222222222222
def s_44 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_44 : Nat := 0x2020202020222
def ep_44 : Nat := 0x200002000000200000000200002000000000020000202020202020000000000000000000000000000000000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_44 : KnownBin bds_44 := by intro b hb; simp [bds_44] at hb
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp [bds_44] at hb
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_44] at hb
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_44_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 64 bds_44 (dagTraceF m_44 s_44 5 f_44) (cur_44 0) s_44 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 64 (dagTraceF m_44 s_44 5 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 64 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 64 (dagTraceF m_44 s_44 5 f_44) cur_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 64 (dagTraceF m_44 s_44 5 f_44) cur_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 64 (dagTraceF m_44 s_44 5 f_44) cur_44) i = true := nj_44_1
theorem lb_44 : LowerBin m_44 s_44 g_44 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xa0a0a0a0a0a0a0a
def s_45 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_45 : Nat := 0x202020202020a
def ep_45 : Nat := 0x200000800000200000000080002000000000008000000000000000000020202020202000000000000000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_45 : KnownBin bds_45 := by intro b hb; simp [bds_45] at hb
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp [bds_45] at hb
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_45] at hb
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_45_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 64 bds_45 (dagTraceF m_45 s_45 5 f_45) (cur_45 0) s_45 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 64 (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45) = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45) i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0x5a5a00005a5a
def s_46 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_46 : Nat := 0x12520000525a
def ep_46 : Nat := 0x400800000000000000000000004000000008000000000000000000001202000002000000000000000000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_46 : KnownBin bds_46 := by intro b hb; simp [bds_46] at hb
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp [bds_46] at hb
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_46] at hb
def cur_46 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_46 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 10 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46 : treeBlockF 0 10 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 10 (dagTraceF m_46 s_46 4 f_46) cur_46) = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 10 (dagTraceF m_46 s_46 4 f_46) cur_46) i = true := fun _ h1 h2 => treeBlockF_at nb_46 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0x5a5a00005a5a0000
def s_47 : List Nat := [0xa0a00000a0a0000, 0x1212000012120000, 0x5a0000005a0000, 0x5a5a0000]
def g_47 : Nat := 0x12000012520000
def ep_47 : Nat := 0x1240000000000000000000000012000000400000000000000000000000120000120200000000000000000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0x5a005a005a005a
def s_48 : List Nat := [0xa000a000a000a, 0x12001200120012, 0x5a0000005a, 0x5a005a]
def g_48 : Nat := 0x1200520052005a
def ep_48 : Nat := 0x40000800000040000000080000000000000000000000000000000000120002000200000000000000000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_48 : KnownBin bds_48 := by intro b hb; simp [bds_48] at hb
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp [bds_48] at hb
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_48] at hb
def cur_48 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_48 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 10 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48 : treeBlockF 0 10 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 10 (dagTraceF m_48 s_48 4 f_48) cur_48) = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 10 (dagTraceF m_48 s_48 4 f_48) cur_48) i = true := fun _ h1 h2 => treeBlockF_at nb_48 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0x55aa000055aa
def s_49 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_49 : Nat := 0x1502000055aa
def ep_49 : Nat := 0x40a800000000000000000000000000000000000004020000000000001002000000000000000000000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_49 : KnownBin bds_49 := by intro b hb; simp [bds_49] at hb
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp [bds_49] at hb
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_49] at hb
def cur_49 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x324438cd0ce2343492f61abad54a4744a80f 7 127 3 7 6 63 11 2047
def f_49 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 10 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49 : treeBlockF 0 10 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 10 (dagTraceF m_49 s_49 4 f_49) cur_49) = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 10 (dagTraceF m_49 s_49 4 f_49) cur_49) i = true := fun _ h1 h2 => treeBlockF_at nb_49 h1 h2
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xf0f0f0f0f0f0f0f0
def s_50 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_50 : Nat := 0x101050105050f0
def ep_50 : Nat := 0x104040a000001040000040a000100040004000a0000000000000000000101000100000000010105010505000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 5, g_23), (m_29, s_29, 7, g_29), (m_38, s_38, 5, g_38), (m_24, s_24, 7, g_24), (m_36, s_36, 5, g_36), (m_32, s_32, 5, g_32), (m_31, s_31, 5, g_31), (m_39, s_39, 5, g_39), (m_28, s_28, 6, g_28)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_29
  · exact lb_38
  · exact lb_24
  · exact lb_36
  · exact lb_32
  · exact lb_31
  · exact lb_39
  · exact lb_28
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_50 : Nat → List (Nat × Nat) := unpackCursorV4 0x187cbb125cf52a4d5afdd26ee032e91587e9d9d44d41a700af48383f14ce856a001540001 0x1c5f3c5e1c5b1c571c531c522b5f3b5b2b573b531b4f1b4b1b471b433a5f3a5e3a5b3a5a3a573a563a533a521a4f1a4e1a4b1a4a1a471a461a431a425a3f5a3e5a3d395f395e395b395739533952194f194b19471943293b293a69392937293659335931292729262925385f385b38573853184f184b18471843583f283b28375833582f482d582b582748255823681f681b681768131c5f3c5e1c5b1c571c531c522b5f2b5e2b5b2b572b533b521b4f1b4b1b471b433a5f3a5b3a573a531a4f1a4b1a471a432a3f2a3e6a3d2a372a352a332a32295f395e295b295a2957395629532952194f194e194b194a1947194619431942293729362935292f592e292d385f385b38573853184f184b18471843283f283b28372833782f682b68277823281f281d281b2817481528131c5f3c5e1c5b1c571c531c522b5f2b5e2b5b3b5a2b572b562b533b521b4f1b4e1b4b1b4a1b471b461b431b422a5f2a5b2a572a531a4f1a4b1a471a432a3f2a3e2a3d395f395b39573953194f194b19471943293f293e593d292f292e292b2929292329226921c120385f385b38573853184f184b18471843283f483d283b283728352833282f282b28272823681f681b681768131b4f3b4e1b4b1b471b431b422a4f2a4e2a4b2a472a433a421a3f1a3b1a371a33394f394b39473943193f193d193b193759351933292f292e592d384f384b38473843183f183b18371833282f282b28272823581f581b581758131c5f3c5e1c5b1c571c531c522b5f3b5e3b5b2b573b533b521b4f1b4b1b471b433a5f3a5e3a5b3a573a533a521a4f1a4b1a471a435a3f5a3d2a3b2a3a2a372a366a35c234395f395e395b395a3957395639533952194f194e194d194c194b194a194719465945894419431942593f593e593d292f292e292d385f385b38573853184f184b18471843583f283b28375833782f682b68277823581f481d581b5817481558131c5f3c5e1c5b1c571c531c522b5f3b5b2b573b531b4f1b4b1b471b433a5f3a5e3a5b3a5a3a573a563a533a521a4f1a4e1a4b1a4a1a471a461a431a42395f395b39573953194f194b19471943593f293b29375933492f492d492b79294927692549234921385f385e38573852184f1847283a28372836282728262825481f48171c5f3c5e1c5b1c571c531c522b5f2b5e2b5b2b572b533b521b4f1b4b1b471b433a5f3a5b3a573a531a4f1a4b1a471a432a3f2a3b2a372a33293e385e3856184e18462836782e68261c5f3c5e1c5b1c571c531c522b5f2b5e2b5b3b5a2b572b562b533b521b4f1b4e1b4b1b4a1b471b461b431b422a5f2a5b2a572a531a4f1a4b1a471a43395f395b39573953194f194b19471943293f693d293b29392937293529337931292f292b29272923385f3857184f1847283f283e483d282f282e28227020481f48171b4f3b4e1b4b1b471b431b422a4f2a4e2a4b2a472a433a421a3f1a3b1a371a33394f394b39473943193f193b19371933292f292b29272923282e1c5f3c5e1c5b1c571c531c522b5f3b5e3b5b2b573b533b521b4f1b4b1b471b433a5f3a5b3a573a531a4f1a4b1a471a435a3f2a3b2a375a33395e29367134385e3856184e184c18468844483e782e68261c5f3c5e1c5b1c571c531c523b5f3b5b3b573b531b4f1b4b1b471b433a5f3a5b3a573a531a4f1a4b1a471a436a3f7a3b6a377a33395f395e395b395a3957395639533952194f194e194b194a1947194619431942493f593e493b293a4937293649334932385f385e38573852184f1847483f4837682a482748264817481648151c5f3c5e1c5b1c571c531c523b5f3b5b3b573b531b4f1b4b1b471b433a5f3a5e3a5b3a573a533a521a4f1a4b1a471a436a3f6a3b6a376a33692e385e3856184e1846583e283648261c5f3c5e1c5b1c571c531c523b5f3b5b3b573b531b4f1b4b1b471b433a5f3a5e3a5b3a5a3a573a563a533a521a4f1a4e1a4b1a4a1a471a461a431a424a3f4a3e4a3b2a3a4a372a364a335a32395f395b39573953194f194b19471943693f693b69376933385f3857184f1847483f4837482f482e482d481f481e681220101b4f3b4e1b4b1b471b431b423a4f3a4b3a473a431a3f1a3b1a371a33394f394e394b394739433942193f193b19371933492f492b49274923481e1c5f3c5e1c5b1c571c531c523b5f3b5b3b573b531b4f1b4b1b471b433a5f3a5e3a5b3a573a533a521a4f1a4b1a471a436a3f7a3b6a377a33395e69262124385e3856184e184c18468844583e2836482e1b4f3b4e1b4b1b471b431b423a4f3a4b3a473a431a3f1a3b1a371a33394f394b39473943193f193b19371933f12fe12bd127b123384f384b38473843183f183b18371833a02f902b80276023501f401b30171013001f 17 131071 7 127 11 2047 16 65535
def f_50 : Nat → Nat × Nat := unpackForestF 0x14bc52b149f234148c42f10ac42774d0423107c41b105c924104c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 16 bds_50 (dagTraceF m_50 s_50 8 f_50) (cur_50 0) s_50 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50 : treeBlockF 0 16 (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 16 (dagTraceF m_50 s_50 8 f_50) cur_50) = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 16 (dagTraceF m_50 s_50 8 f_50) cur_50) i = true := fun _ h1 h2 => treeBlockF_at nb_50 h1 h2
theorem lb_50 : LowerBin m_50 s_50 g_50 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xff00ff00ff00ff
def s_51 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_51 : Nat := 0x170057005700ff
def ep_51 : Nat := 0x4000a800000040000000a80000000000000000000600020002000000120002000200000014005400540000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_12, s_12, 4, g_12), (m_43, s_43, 5, g_43), (m_40, s_40, 5, g_40), (m_48, s_48, 5, g_48), (m_27, s_27, 5, g_27)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_12
  · exact lb_43
  · exact lb_40
  · exact lb_48
  · exact lb_27
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_51_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xee0e64e41e21c30c20be2be0ba2a6aa60a60a608ae8a08a08a08a08248017e15f05e05e05e05e0564541521330038001 0x6930f922019243c04806d400d282135e406b40ed58e9a901b4e0369406d180da101a5a384ac069380d211b1560328c064f80c971925c034a05cd700da81034d0369260d140da08824d03492589140d20828560508c50d740dac82b55036a24c9740d2c82a55034a20a57890ae0285e0509c280d8101301a381c468344d00c1a01a50036a0411787a2d02c56188a406d6859ab01a4d03492069140d2081a3903462281580c270183e0304c069303122051240304806d400d280835e0e6b40ad5821a901b4e0369406d180da101a5a064ac069380d21020560308c060f80c174034f03696f0d1c0da1b724f03496cc91c0d2181a3f03476068dc0d19ae14f5428e064fd109b8192f3424e5413c88238183f1206e060bc08138001f 12 4095 5 31 11 2047 19 524287
def cc_51_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8004001938c80630b1818829d44e0270138065c3201808c005c224512009004801670b005802c016009104422010080000000000 0x71781c5d16d781b5d16d381b4906d081b41169781a5dfc9701a59069541a52069441a50069341a45068f41a35f85743955064f64135f41742855060f4b035ec133914c071781c5d06d741b5506d341b4906d141b41069681a59129581a51129181a45068f81a3284537a145201378045071781c5d12d781b5dd8d701b5906d541b5206d441b5006d341b45129781a5d129381a49069081a41068e81a36d45743955064b5c125d01742855060b43025c89701a50c0d701b50a4d341b49c4d141b41849341a49bc9141a410e5583946b4d741b590ed541b51b09741a590e9541a510e578394e8c4d9b1260e17ab05c068e27234064d26034069401b50a517a845a0f15a545206d6a4356069341a49069141a41068e41a318c558194e064f81926 13 8191 5 31 11 2047 18 262143
def cc_51_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xb02a1a828105000 0x220264214c038bc071740dad01b590b6ac06d442da301b45034ba069540d2681a490348a069040d1c81a315229b0c5148026c1045 10 1023 5 31 11 2047 19 524287
def cur_51 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_51_2 (Nat.sub p 64)) (cc_51_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_51_0 p) (Nat.blt p 32)
def f_51 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 69 bds_51 (dagTraceF m_51 s_51 7 f_51) (cur_51 0) s_51 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 69 (dagTraceF m_51 s_51 7 f_51) cur_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 64 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 69 (dagTraceF m_51 s_51 7 f_51) cur_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_2 : treeBlockF 64 69 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 69 (dagTraceF m_51 s_51 7 f_51) cur_51) = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 69 (dagTraceF m_51 s_51 7 f_51) cur_51) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nj_51_2 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 69 (dagTraceF m_51 s_51 7 f_51) cur_51) i = true := block_join nj_51_1 (fun _ h1 h2 => treeBlockF_at nb_51_2 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 69 (dagTraceF m_51 s_51 7 f_51) cur_51) i = true := nj_51_2
theorem lb_51 : LowerBin m_51 s_51 g_51 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xffffffff
def s_52 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_52 : Nat := 0x135757ff
def ep_52 : Nat := 0x44a800000000004400a8000000000202020000000000130202000000000010545400
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_37, s_37, 5, g_37), (m_14, s_14, 4, g_14), (m_34, s_34, 4, g_34), (m_35, s_35, 4, g_35), (m_36, s_36, 5, g_36)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_37
  · exact lb_14
  · exact lb_34
  · exact lb_35
  · exact lb_36
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV4 0x421840f89e0bc0704d841d001 0x992305c51426486571d505040f4f3d2cf473d0e64a38cb94f752e947750cd3f34ecd3734ce04f512d047510cc3f30ecc3730cdc1f506c817504c01f 11 2047 5 31 10 1023 14 16383
def f_52 : Nat → Nat × Nat := unpackForestF 0x34fc5c34724f75c24721701f 3 9
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 8 bds_52 (dagTraceF m_52 s_52 6 f_52) (cur_52 0) s_52 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 8 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 8 (dagTraceF m_52 s_52 6 f_52) cur_52) = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 8 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 8 (dagTraceF m_52 s_52 6 f_52) cur_52) i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xffff0000ffff
def s_53 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_53 : Nat := 0x1757000057ff
def ep_53 : Nat := 0x40a8000000000000000000000040000000a8000006020000020000001202000002000000145400005400
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_9, s_9, 4, g_9), (m_42, s_42, 5, g_42), (m_46, s_46, 5, g_46), (m_26, s_26, 5, g_26), (m_49, s_49, 5, g_49)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_9
  · exact lb_42
  · exact lb_46
  · exact lb_26
  · exact lb_49
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_53_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xee0e64e41e21c30c20be2be0ba2a6aa60a60a608ae8a08a08a08a08248017e15f05e05e05e05e0564541521330038001 0x6930f922019243c04806d400d282135e406b40ed58e9a901b4e0369406d180da101a5a384ac069380d211b1560328c064f80c971925c034a05cd700da81034d0369260d140da08824d03492589140d20828560508c50d740dac82b55036a24c9740d2c82a55034a20a57890ae0285e0509c280d8101301a381c468344d00c1a01a50036a0411787a2d02c56188a406d6859ab01a4d03492069140d2081a3903462281580c270183e0304c069303122051240304806d400d280835e0e6b40ad5821a901b4e0369406d180da101a5a064ac069380d21020560308c060f80c174034f03696f0d1c0da1b724f03496cc91c0d2181a3f03476068dc0d19ae14f5428e064fd109b8192f3424e5413c88238183f1206e060bc08138001f 12 4095 5 31 11 2047 19 524287
def cc_53_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8004001938c80630b1818829d44e0270138065c3201808c005c224512009004801670b005802c016009104422010080000000000 0x71781c5d12d781b5d12d381b4906d081b41129781a5dfc9701a59069541a52069441a50069341a45068f41a35f85744955064f64135f41742855060f4b035ec133914c071781c5d06d741b5506d341b4906d141b41069681a590e9581a510e9181a45068f81a3284537a145201378045071781c5d0ed781b5dd8d701b5906d541b5206d441b5006d341b450e9781a5d0e9381a49069081a41068e81a36d45743955064b5c125d01742855060b43025c89701a50c0d701b50a4d341b49c4d141b41849341a49bc9141a41165585946b4d741b5912d541b51b09741a590e9541a5116578594e8c4d9b1261617ab05c068e27234064d26034069401b50a517a845a1315a545206d6a4356069341a49069141a41068e41a318c558194e064f81926 13 8191 5 31 11 2047 18 262143
def cc_53_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xb02a1a828105000 0x220264214c038bc071740dad01b59096ac06d4425a301b45034ba069540d2681a490348a069040d1c81a315229b0c5148026c1045 10 1023 5 31 11 2047 19 524287
def cur_53 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_53_2 (Nat.sub p 64)) (cc_53_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_53_0 p) (Nat.blt p 32)
def f_53 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 69 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) s_53 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 32 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_1 : treeBlockF 32 64 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_2 : treeBlockF 64 69 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) = true := by decide +kernel
theorem nj_53_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_53_1 h1 h2)
theorem nj_53_2 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) i = true := block_join nj_53_1 (fun _ h1 h2 => treeBlockF_at nb_53_2 h1 h2)
theorem nc_53 : ∀ i, 0 ≤ i → i < 69 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 69 (dagTraceF m_53 s_53 7 f_53) cur_53) i = true := nj_53_2
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def g_54 : Nat := 0x1171757135757ff
def ep_54 : Nat := 0x124040a800001640000044a800160040004400a8010606020202020001121202130202000114145410545400
theorem epk_54 : ep_54 = edgePack fullMask g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 7, g_20), (m_51, s_51, 8, g_51), (m_50, s_50, 9, g_50), (m_53, s_53, 8, g_53), (m_45, s_45, 6, g_45), (m_19, s_19, 7, g_19), (m_29, s_29, 7, g_29), (m_25, s_25, 7, g_25), (m_28, s_28, 6, g_28), (m_24, s_24, 7, g_24), (m_44, s_44, 6, g_44), (m_52, s_52, 7, g_52), (m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7), (m_37, s_37, 5, g_37), (m_33, s_33, 5, g_33), (m_23, s_23, 5, g_23), (m_14, s_14, 4, g_14), (m_21, s_21, 5, g_21), (m_22, s_22, 5, g_22), (m_3, s_3, 4, g_3), (m_46, s_46, 5, g_46), (m_18, s_18, 5, g_18), (m_39, s_39, 5, g_39), (m_41, s_41, 5, g_41), (m_47, s_47, 5, g_47), (m_30, s_30, 5, g_30), (m_32, s_32, 5, g_32), (m_42, s_42, 5, g_42), (m_43, s_43, 5, g_43)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_51
  · exact lb_50
  · exact lb_53
  · exact lb_45
  · exact lb_19
  · exact lb_29
  · exact lb_25
  · exact lb_28
  · exact lb_24
  · exact lb_44
  · exact lb_52
  · exact lb_2
  · exact lb_7
  · exact lb_37
  · exact lb_33
  · exact lb_23
  · exact lb_14
  · exact lb_21
  · exact lb_22
  · exact lb_3
  · exact lb_46
  · exact lb_18
  · exact lb_39
  · exact lb_41
  · exact lb_47
  · exact lb_30
  · exact lb_32
  · exact lb_42
  · exact lb_43
theorem sub_54 : ∀ b ∈ bds_54, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_54_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xbf0fee430b30c2b72aa7cc28f209bb06503d8e0c21e3483881eebf7350dadbf676817e3f57ef5413d4c87911c140288e23d34880b3bd28e808341192f449b60bad81ea0002f00001 0x139fc0dcf607e77027398075fc03afc01d7b03ebd0075dc03aec01d73102b90075bc03adc01d6b066b500759c03acc01d63036b100b1fc058f602c770163980b1bc058d602c670163180717c038bc02c5d00dbf806dec036ee01b7300db7806dac036ce01b6300daf806d78036ba01b4f00da7006d2c0369201b43015a1006d04092fc07976034b7022598032bc1f15c00cab0065500529c0294600c9f0164f00326c01934026378131ac098ce04c630262f813174098b606c590262b823154098a604c51025b780adac096ce02b63025af812d74056b602b59025ab812d54056a602b51025a780ad2c0968e02b43025378129ac094ce04a630252f806974094b605a590252b806954094a604a510552781692c1548e05a430151f8128ec0946e02a33046b78135b80fad607d6a03eb381f59811ac604d620463781b1ac0f8ce06c63045b780adac0f6ce02b63045af812d74056b602b59045ab812d54056a602b51035a780ad2c0d68e02b43055378169ac0f4ce05a630452f8069740b4b605a590452b8069540b4a605a510352781692c1148e05a430151f8168ec1146e02a3300f3f0139e803cec04e7200eb70175b4098fc04c7a0263b0131c8038dc04c6d026360071a8038d201c6800e33007194038c801c620263085f180098bc06c5a0262b01b148056da01b6900db280ad84034dc01a6d00d2f0069640b4a401a5100d268069240348a01a4100c3702e1b009ade04d6b026b381358c098de04c6e026358131a8098ce04c6602631813188098be04c5e0262d823168098ae04c560262981b148056de02b6b015b380ad8c056be02b5b015ab80ad4c094de04a6b0253381298c0d4be05a5b0d92b81694c0949e01a4d025258129240948e01a45025218169040547e02a3b0151b80a8cc5cade07d6b03eb38b158c568de02c6b03e3380b18c528be02c5b1422b80b14c4c6de05b6b03db3816d8c486be05b5b109ab816d4c0569e05b4b0f1a380ad0c3a2dc07966034af0705580529c1a14602c9f0064d809cfe06e7b0373b8139cc09afe07d7e026bd81b5e809aee07d76026b981b5c805ade02d6e016b680b1fc0f8fc02c7b0163b80b1cc058e402c6b0163500b1a4058ce06c660163180b184058ae06c560162a812dfc0b6f605b77025b9816dbc0b6d605b6702db1812d7c036ba05b5b02dac816d5c036aa04b5302da880ad3c0569602b47015a18121f80f0ec0686e03433012178090b8068560442a00a1380509802846024220160f80306c04e7f03f3f0139ec0dcf404e7703f3b0139cc0dce404d7f036bd81b5dc09ae602d6f016b700b5b4058fe02c7b0163b80b1cc058de06c6e0163680b17c0d8bc02c5b0162c80b14c058a402c51025bf816dec0b6ee04b7302db7806db4096d605b69025b3806d940b6c605b6102daf816d6c0b6ae05b53015a780ad2c0568e02b430243f01e1d80d0dc0686c024330121900d0bc068560142700a1180b07c0183603eb78135b80fad607d6a03eb381f5980fac604d6203e3781b1ac0f8ce06c6303db780adac0f6ce02b63045af812d74056b602b59045ab812d54056a602b51035a780ad2c0d68e02b4302d378169ac0b4ce05a6302d2f8069740b4b605a5902d2b8069540b4a605a5102d2781692c0b48e05a430151f8168ec0b46e02a33026b78135ac09ace04d63026378131b8098d604c6a02633813198098c604c620262f813178098b608c5a0262b813158098a606c52015b780adac056d402b67025b300ad8c056be04b5e015ad80ad5c056a602b52025378129ac094ce04a6302d2f81696c0b4ae05a53025278069340949604a49025238069140948605a410151f80a8ec0546e02a3303eb781f5ac0face07d6303e3780b1ac0f8ce02c630c22f80b16c2e8ae02c5302db7816dac0b6ce05b6302daf816d6c0b6ae05b53015a7816d2c0b68e02b4303c3701e1980d0bc16056014270541180b07c018360273f81b9f80dcfa06d7b03ebd01b5e40faee07d76026b981b5c40face07d6603eb28131fc058f604c77016398131bc1b8da02c6b0163481319c1d8ca02c630163081317c058b602c590262b80b14c058a204b7f02dbd81eddc096e604b6f00db6816dac0b6d20cb6700db2812d8c0b6c206b5f02dad822d5c0b6a602b4f025a5812d1c0568603a7e01d3b00e9b8074d803a6601d3200e978074ac02a4e01d2300e8f80346c04e7f0373e81b9ec0dcf406e7703f3b01b9d409afe07d7e036be81b5bc0dadc06d6d0263f80b1ec098ee02c730263780b1ac058d204c670163180b184098be06c5d0162d80b164098ae06c550162980b144096fe05b7b03dbb812dcc0d6de05b6b035b3816d8c096be01b5d02dad816d640d6ae01b55025a9816d440569e04b4b025a380ad0c074fc03a7601d3700e998074bc03a5c01d2b00e9500549c03a4601d1f0068d8072ac039540342b02e15005cfe02e7e0173e8135fc0daf607d77026b98135bc1bada06d6b036b482759c13aca04d63036b080b1ec058f402c790163b81f1d8058e602c710163381f198058ca02c5f0762f00b16c058ae02c5301629012dfc0b6f607b77025b9812dbc036da05b6b02db4826d9c036ca04b6302db081ad7c0b6b60ab5702da980ad3c0569602b47015a180e9f8074ec03a6e01d3600e998074c803a5e01d2b00a9380548c03a3e00d1b0139f809cfa06d79026b880b5b405ad206d65016b080b1f4058ea02c6d0163480b194058c202c5901628806db40b6d201b65025b080e9f8074ec03a6e01d3600e998074c803a5e01d2b00a9380548c03a3e00d1b0139fc0dcf606e77027398135fc20afc04d7b036bd0135dc0faec04d73036b900b5bc05adc02d6d0163f83b1f8058f602c770163980b1c8058d602c6a0163480b19c0d8cc02c630163080b15c0d8ac02c55025bf816dec0f6ee04b73035b7816dac0d6ce05b63025af806d740b6b605b59035ab806d54096a605b51015a780ad2c0568e02b4301d3f00e9d8074dc03a6601d2f00e970074ac03a540152700a9180747c01a360273f8379f809cf606e7a0273b81f9d809ce606e72026bf81b5ec0daee04d73016b780b5b805ada02c7f0163d80b1dc058e602c6f0363700b1b4058be06c5e0162d80b164058a602c5201628812dfc0b6f607b77025b981adbc036da04b6b02db4812d9c036ca05b6302db081ad7c0b6b606b5702da980ad3c0569602b47015a180e9f8074ec03a6e01d3600e998074c803a5e01d2b00a9380548c03a3e00d1b0079fc0bcfc01e7d026bf81f5ec0faee04d7300eb78075b403ad606d6900eb383759403ac601d610263f80b1ec098ee02c7300e378071b4038d602c6900e3383b194038c601c610262f80b16c098ae02c5300dbd816de8036f201b7700dbb006dcc036e201b6700db3006d94036be01b5b00dab806d4c0369e01b4b00da3806d0c074fc03a7600d370069b0034cc03a6401d2f00e9580549c03a4600d1f0068d803cfc01e7d036bc8135c409ada05d69036b2813584098da02c690263280b184036fa01b7500db6806da4036ca01b6101d3f00e9d8074dc03a6c01d3300e990074bc03a560152700e9180347c01a360373f81b9ec0dcee06e7300ebf8315f803af601d7a00ebb81f5d803ae601d7200eb78175b803ada06c7f0163d81b1dc058e606c6f0163581b19c058c601c5f00e2e80716c058b201c570362a80714c038a201b7f00dbd806ddc036e601b6b02db5006da4036ce01b6600db1806d84036ae01b5600daa806d3c0369601b4700da180e9f8074ec03a6e01d33006978034b801a5601d2a00a9380748c01a3e00d1b006558072a80185605c2a0139f40fcea01d7e00ebe81b5b809ad405d66026b1013174058b204c5501628806df4036ea01b5d00dac806d54036a203a7e01d3b00e9b8074cc03a5e01d2e00e958074a802a4e01d230068f80346c0395601caa012158170a801e7f00f3f0079ec0fcf401e7700f3b0079cc14ce408d7f036bd81f5dc0dae601d6f00eb70175b4158fe02c7b03e3b80b1cc038de0ec6d00e358071a4038ce01c6500e3180b1840d8be02c5b0362b80b14c036fe01b7b00dbb806dcc036de01b6e00db6806d7c036bc01b5b00dac806d4c0b6a401b5100da7806d2c0368e01b4301d3f00e9d8034dc03a6c00d33006990074bc03a560152700e9180347c01a36016be80b5d4038fc01c7d036370131a8118cc04c620162f00b168058ac02c5200dbe806dd40369a01b4900da2806d04074fc03a7601d3700e998054bc02a5601d2700e9300748c03a4400d1f0068d80908c0b8440273f81b9ec0fcee04e7300ebf8075f803af607d7a00ebb8075d803ae60857200eb78075b803ad60dd6a00eb380759803ac606d620163f80b1ec058ee02c730163780b1ac058ce02c6300e2f807178058ba01b7f00dbd806ddc036e601b6f00db5806d9c036c601b5f00daf006d740369e01b4e00da5806d240368602b4200da080e9f8074ec03a6e01d33006978074b801a5600d2a00a9380548c01a3e00d1b04d5bc0fad607d67092b18451bc058d607c670163183d17c058b60e45701629834dbc0b6d607b6702db182cd7c0b6b60935702da980ad3c0b69607347015a180e9b8074cc03a5e01d2b00a9380748c03a3e00d1b0139fc0dcf606e77027398135fc0fafc04d7b036bd0135dc0faec04d73036b900b5bc05adc02d6d0163f81f1f8058f602c770163980b1c8058d602c6a0163480b19c0d8cc02c630163080b15c0d8ac02c55025bf816dec0b6ee04b7302db7816dac0b6ce05b63025af806d740b6b605b5902dab806d54096a605b51015a780ad2c0568e02b430243f01e1d80d0dc068660242f0121700d0ac088540142700a1300508c0484402c1f0060d809cfe07e7e0273d81b9e809cee07e760273981b9c809afe06d7b036bb8135cc05ade02d6e016b680b1fc058f602c770163980b1bc0d8dc02c6d0162f81b178058b602c590162980b148058a204b7f02dbd816ddc096e605b6f00db6812dac0b6d204b6700db2816d8c0b6c205b5f02dad816d5c0b6a602b4f015a580ad1c056860487e03c3b01a1b80d0d8048660243201a1780d0ac0284e014230160f80306c07d6f026b701f5ac0fad407d6703eb301f58c09ac407c6f0363581f1a80f8ce07c660363181edbc056d607b67015b1822d7c096ba02b5b015ac822d5c096aa02b53015a881ad3c0569602b49035a380ad0c0568205a6f02d3581699c0b4c605a5f00d2e81696c0b4b205a5700d2a81694c0b4a205a4f02d2681692c0b48e05a4502d2180a8fc0b47605a37015198135bc09ad604d67026b18131bc098dc04c6b0263501319c098cc04c630263101317c098bc04c5b0462d01315c098ac04c530362900adbc056d602b6a015b3812d98056c602b5f025af00ad6c056ae02b53015a90129bc094d604a670253181697c0b4b605a5702d2981293c0349a04a4b0252481291c0348a04a4302d2080a8fc0547a02a3b0151b8128d40546607d6f03eb581f59c0fac607c6f0163581f19c058c60545f0162d81115c058a605b6f02db5816d9c0b6c605b5f02dad816d5c0b6a602b4f02da5816d1c056860786e03c3301a178060ac0284e010230160f80306db945fdc22ded915f668a7b235f015adea8d5c056a7a634f015a5e90d1c05687a025fcf12de7095f324a79624fc8925e2491f0e48602a3fc211de008dc054677715fb60add8855eb42a74d14fa00a5cb851e482860293f8e89dc504dc052670012f75095b4049d58246a805f5302da6015d260a68a04f430259e011cee0860283f3a81d97c0dc050664802f218158d409c600461901f0a00d81805c020260003f 18 262143 7 127 11 2047 21 2097151
def cc_54_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe51f757f9ca7731627b958acbb3a7772872d96572354885305f63d76cd9c0366c0819aab5ecfd65ab5150525bf45680f63f35ef4c22b28afc8c2d1b2fc5ba2118ac25c105680002b 0x4e7f0dcf61b9dc273984d7f7eafc135ec36bd04d770faec135cc36b902d6f05adc0b5b4163f8ec7e058f60b1dc163982c72058d60b1a8163482c670d8cc0b18c163082c570d8ac0b1540dbf81b7e036f616de80dbb81b76036e612dc80db781b6e036d616da80db381b66036c616d880daf81b5e036ba06d700dad85b5a036b216d600dab81b56036aa06d500da984b52036a212d400da781b4e036960ad280da381b46036860ad080d3f81a7b034ee069cc0d3781a6b034ce0698c0d2f81a5d034b6069640d2b81a55034a6069440d2781a4b0348e0690c24bf879770d2de1a59c24af8395d0d2ae0e55414a7829470327e0e4f40c9b819350325e0649c243f858770b0de1619c242f8585d0b0ae1615414278284d0508e161140c1f8183e0b07a060bc0c170182209cfe3b9f8273d86e7a09cee1f9d8273986e7209afe1b5ec36bb84d7305ade0b5b816b682c7f058f60b1dc163982c6f0d8dc0b1b4162f86c5e058b60b164162982c52058a206dfc0dbf01b7b0b6f406ddc0dbb01b73096e406dbc0db701b6d036d806dac25b501b69096d006d9c0db301b65036c806d8c2db101b610b6c006d7c0daf01b5b0b6b406d5c0dab01b530b6a406d3c0da701b4b0569406d1c0da301b4305684069fc0d3d81a77034e6069bc0d3681a6b034d20699c0d3281a63034c20697c0d2d81a57034a60693c0d2581a4703486125fc3cbb8696f072da1259c1cb28695f0d2ae0a53c14a38193f0727a064dc0c9a8192f0324e121fc2c3b8586f0b0da1219c2c328585f0b0ae0a13c14238183f0307c160f40c178182e03044135fc3ebd87d7709ae60f5bc1eb683d6b0dad20f59ca6b283d6307ac2131fc163d84c77058e60f1bc1e3682c6b058d20f19c763282c63058c21317c162d84c57058a606dfc0dbf01b7b0b6f406ddc0dbb01b73096e406dbc0db701b6d036d806dac1db501b690b6d006d9c0db301b65036c806d8c1db101b61076c006d7c0daf01b5b0b6b406d5c0dab01b530b6a406d3c0da701b4b0969406d1c0da301b4305684069fc0d3d81a77034e6069bc0d3681a6b034d20699c0d3281a63034c20697c0d2d81a57034a60693c0d2581a47034860e5d81cb30183e0305c0f9f81f3e86d7909ae21b594263682c69098ca0b1840dbf04b7a036ec12dc80db701b6d036d812da80db485b68036cc06d940db204b62036c212d800daf05b5a036ac16d480da704b4a0368c0ad080d3681a69034ca069840c1f0182e0dcfe1b9ec373b86e7307afeed5f81ebd83d7a07aee1f5d81eb983d720d8fe0b1ec363b82c730d8de0b1ac363382c63078be0f174162d82c59078ae1b154162982c51036fe06df80dbd85b7a036ee06dd80db985b72036de06db80db585b6a036ce06d980db185b62036be06d780dae81b5c036b60ed680dac85b58036ae06d580daa81b54036a60ed480da883b500369e06d380da585b4a0368e06d180da182b42034fe069ec0d3b81a73034de069ac0d3381a63034be069740d2d83a5a034b2169600d2b81a56034aa069500d2981a510349e0692c0d2381a43072cc0e5581c2b0b8540307c060b8273e87e7507afc0f5f436b704c5d058b213154162881b7e096f406de42dbc01b76096e406dc425b801b6e0b6d406d982db101b5e036ba06d7025ad01b590b6b006d580daa81b54096a406d4425a801b4e0969406d1815a101a79034e206974252d01a590b4b0069580d2a81a54034a2121585c2a0183e0305c0f9fc1f3f03e7b0fcf40f9dc1f3b03e7372ce4235fc36bd87d770dae62b1fc163d87c77058e60f1bc763682c6b058d20f19c1e3282c63058c21b17c162d86c57058a606dfc0dbf01b7b0b6f406ddc0dbb01b730b6e406dbc0db701b6d036d806dac1db501b69076d006d9c0db301b65036c806d8c1db101b610b6c006d7c0daf01b5b0b6b406d5c0dab01b530b6a406d3c0da701b4b0b69406d1c0da301b4305684069fc0d3d81a77034e6069bc0d3681a6b034d20699c0d3281a63034c20697c0d2d81a57034a60693c0d2581a47034860e5b81caf0183e0305c0b5f416ba83c7e078fa1b1b8263508c66098c40b1780dbf04b7a036f216de00dbb04b72036e212dc00db705b6a036cc16d880daf02b5a036ac0ad480da701b4d0369812d280da485b480368c06d140da204b420368212d000d2681a490348a0690424230b8440307c060b8273f86e7b0fcee139cc1ebf83d7e07af61f5e81ebb83d7607ae6dd5c81eb783d6e07ad6475a81eb383d6607ac61b588163f82c7b058ee0b1cc163782c6b058ce0b18c0dbf81b7e036f616de80dbb81b76036e612dc80db781b6e036d616da80db381b66036c616d880daf81b5e036ba06d700dad83b5a036b20ed600dab81b56036aa06d500da983b52036a216d400da781b4e036960ad280da381b46036860ad080d3f81a7b034ee069cc0d3781a6b034ce0698c0d2f81a5d034b6069640d2b81a55034a6069440d2781a4b0348e0690c14af0294e0307c060ba12b787d6b0facf0558e023782c6b0f8ce0b18df22f82c5b7a8ae0b14c0db781b6e036d616da80db381b66036c616d880daf81b5e036b616d680dab81b56036a616d480da781b4e0369616d280da381b46036860ad080d3781a6b034ce0698c0d2f81a5b034ae0694c0d2781a4b0348e0690de0b787967742bee055c14a7b61470327e0e4f40c9b819350325e0649c2c37858670b0be1615c1427858470307e060f82c1e8182f0305c06088273f86e7b0dcee139cc26bf87d7e09af61b5e826bb87d7609ae61b5c816b782d6e05ada0b1fc3e3f02c7b058ee0b1cc163902c6b058d40b1a4163386c66058c60b184162b86c56058aa06dfc2dbd81b77096e606dbc2db581b670b6c606d7c0dae85b5b0b6b206d5c0daa84b530b6a206d3c15a581b4705686064d8243f078760d0dc1a198242f0485c0d0ac2215014270284c0508c121102c1f04e7f0fcfc139ec373d04e770fcec139cc373904d7f0daf61b5dc26b982d6f05adc0b5b4163f82c7b058ee0b1cc163786c6e058da0b17c362f02c5b058b20b14c162902c51036fe16dec0dbb84b73036de06db425b585b69036ce06d942db185b61036be16d6c0dab85b530369e0ad2c0da382b430326c121f83c3b0686e0d0d81219824320685e0d0ac0a13814230583e0fade135b83eb587d6a0face1f5983eb184d620f8de1b1ac3e3507c670f8cc1b18c3db782b6b0f6ce0ad8c45af84b5d056b60ad6445ab84b55056a60ad4435a782b4b056921ad1c15a182b41034de169ac0d3385a63034be069742d2d85a59034ae069542d2985a510349e1692c2d2481a470b486169040d1f85a3b0346e0a8cc26b784d6b09ace1358c263784c6e098d6131a8263384c66098c613188262f84c5e098b623168262b84c56098a61b14815b782b6b056d40ad9c25b302b63056be12d7815ad82b57056a60ad480d3784a6b034ce1298c0d2f85a5b034ae1694c0d2781a4d09496129240d2381a45054860a9040d1f82a3b09472068dc151982a310fade1f5ac3eb387d630f8de0b1ac3e3382c63688be0b16d9a2b82c53036de16dac0db385b63036be16d6c0dab85b530369e16d2c0da382b430326c1e1b83c330685e640ac0a13988230583e09ade135b8363587c67098c61f15c3e2a84b6f056d612d9c15b184b5f096ba0ad6c15ac84b57096aa0ad4c15a884b4f0569612d1c15a184a6f0b4d61e99c25318ca5f034ba1696c2d2c8ca57034aa1694c2d2886a4f0b4962291c2d2182a3f09476128dc151984e7f0dcfc1b9f436bd87d7a0daf21f5dc3ebb04d730dae21f59c3eb307d65098fe0b1ec263b82c73098de331b4163582c69098ce3b194163182c61098be0b16c162c84c57058a60b14425bf85b7b0f6ee12dcc25b781b6d0b6d616da465b381b65096c616d8435af85b5b116ae16d4c15a784b4b0968e0ad0c24bf07976092dc125b064b32f1640d2bc2255814a7049460b27c064d826b786d6b0dace131bc263706c5f0d8bc12dbc15b584b67056c612d7c15ad84b57056a612d3c25a682b4b0569212d1c25a282b4305682129bc2d3587a67094c61a97c2d2d86a570b4a64693c0d2685a4b0b4924691c0d2285a430b4820a8fc251d84a3705466139fc373e86e7b0dcf41b9dc3f3b06e7509afe1f5f836be86d6f0dadc1b5b4263f82c7b098ee0b1cc263782c6b058d21319c163182c61098be1b174162d82c59098ae1b154162982c51096fe16dec3dbb84b730d6de16dac35b385b63096be06d742dad85b590d6ae06d5425a985b510569e12d2c25a382b430d4ac0e95024bf079760d2dc1a59824af0495c0d2acb455014a7049460b27c064d8173f82e7e05cfa135fc36bd87d7709ae6135bc66b686d6b0dad22759c4eb284d630dac20b1ec163d02c79058ee1f1d8163982c71058ce1f198163282c5f1d8bc0b16c162b82c53058a412dfc2dbd87b77096e612dbc0db685b6b0b6d226d9c0db284b630b6c21ad7c2dad8ab570b6a60ad3c15a582b4705686125f83cbb0496e092d8265984cb20695e112ac0a53814a30593e0326c139f8273e86d7909ae20b5b416b486d6505ac20b1f4163a82c6d058d20b194163082c59058a206db42db481b65096c2125f824bb0496e092d81259894b20695e0d2ac0a53814a30593e0326c139fc373d86e7709ce6135fd52bf04d7b0daf4135dc3ebb04d730dae40b5bc16b702d6d058fe3b1f8163d82c77058e60b1c8163582c6a058d20b19c363302c63058c20b15c362b02c55096fe16dec3dbb84b730d6de16dac35b385b63096be06d742dad85b590d6ae06d5425a985b510569e0ad2c15a382b43092fc1e5d834b706966092bc1257034ab089540529c0a5182c9f0193609cfe339f8273d86e7a09cee1f9d8273986e7209afe1b5ec36bb84d7305ade0b5b816b682c7f058f60b1dc163982c6f0d8dc0b1b4162f86c5e058b60b164162982c52058a212dfc2dbd87b77096e61adbc0db684b6b0b6d212d9c0db285b630b6c21ad7c2dad86b570b6a60ad3c15a582b4705686125f83cbb0696e0d2d81259824b20695e0d2ac0a53814a30593e0326c135bc26b704c6f0f8d61f19c26318ac5f118ba4b16c362c8ac57118aa4b14c362884b6f056d612d9c15b184b5f096ba0ad6c15ac84b57096aa0ad4c15a884b4f0569612d1c15a181a6b034ce0698c0d2b81a550349e0692c0d2381a430347e068ec0d1b81a3303cfe179f80f3e84d7f0faf61f5dc26b981d6f03ada075ac36b481d6719aca0758c0eb084c7f058f6131dc163981c6f038da071ac163481c671d8ca0718c0e3084c5f058b61315c162981b7b0b6f406de40dbb81b76036e606dc40db381b66036ca06d7c0dad81b57036a606d3c0da581b4703686125f83cbb0196e032d80659938b20695e152ac0a53824a30193e0b278064d80c9a06d6f0dad61b59c36b18cc6f098dc1f1ac3e3507c670f8cc3318c263105c5f0b8bc1adbc15b586b67056c61ad7c15ad86b57056a61ad3c25a682b4b056921ad1c25a282b4305682069bc0d3581a67034c60696c2d2d01a57034ac0694c0d2381a450347e068ec0d1b81a330dcfe1b9ec373b86e7303afe335f80ebd81d7a03aee1f5d80eb981d7203ade175b80eb686c7f058f61b1dc163986c6f058d61b19c163181c5f038ba0716c162c81c570d8aa0714c0e2881b7f036f606ddc0db981b6b0b6d406da40db381b66036c606d840dab81b56036aa06d3c0da581b4703686069581d2a0a97e0f2ec1a5b834b30195e032b80655928aa0294e0d28c064f80c9b04e7d0fcea075f80ebe86d6e09ad41759826b104c5d058b213154162881b7d036ea06d740dac81b55036a2129581d2a0497e092ec1a5b844b30495e092b81255894aa0294e0928c064f82c9e01936032682b5bc26b707d6b0fad41f59c3eb30ad6309ac4231bc363587c670d8c61717c2e2e8ab6f056d61ed9c15b18cb5f096ba0ad6c15ac8cb57096aa0ad4c15a886b4f056961ad1c15a181a6f034d60699c0d3181a5f034ba0693c0d2581a430347e068ec0d1b81a3303cfe079f80f3d87e7a03cee079d80f39a367211afe1b5ec3ebb86d7303ade075b82eb68ac7f058f61f1dc163981c6f1d8da071ac0e3481c67038ca0718c163086c5f058b61b15c162981b7f036f606ddc0db981b6f036dc06db40daf81b5e036b606d640da985b52036a206d3c0da581b47036862a5f83cbb0196e442d8065980cb20695e112ac0a538d8a30193e0b278064d80c9a0186e170d80b5f416ba81c7e038fa1b1b8263508c66098c40b178162d02c56058a406df40dba81b4d0369206d140da08497e092ec1a5b844b30295e052ac1253824a60494625288064f82c9e0193603268135bc36b587d6709ac6131bc263707c6b0f8d41f19c3e3304c63098c41b17c362f0cc5b118b43315c462b06c530d8a40adbc15b582b67056c60ad7c15ad82b57056a60ad3c15a681a6f034d60699c0d3181a5f034b60695c0d2981a4f0349a068fc0d1d81a33 18 262143 7 127 11 2047 19 524287
def cc_54_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x97b4d9007b8b14f8327f7b77b781367047d68b7963f4c5f34c5a74c57c2b51e5e4f12d491604622f4372b40e293ae603852935a2b2fc5e2b448273412363d204321ce361ae201337b0b1820367b00036 0x9ade135b82eb585d6a0bace1759826b184d62098de1b1ac3e3384c630b8be171742e2d85c590f8ae1f1542e2985c51096de0adac25b382b63096be12d7415ad82b59096ae12d5415a982b510969e0ad2c25a382b43034de169ac0d3384a63034be069740d2b81a550b4a60693c2d2581a470b486068fc251d81a3705466125bc3cb38c95f072ba3255c1caa8694f1128e0a4fc249b8592f0324e121bc2c338585f030ba0615c0c2a8584f0b08e0a0fc241b8582f0304e139fc373f06e7d0daf61f5e836bc87d770faec135cc36b887d670facc1f594263f82c7b098ee0b1cc26378cc6d058d60b1a426338ec65058c60b184262f82c5b058b21315c162982c51036fe16dec0dbb84b73036de06db42db585b69036ce06d9425b185b61036be16d6c0dab85b530369e12d2c0da382b43094fe129f82d3d85a7a0b4ee1e9d8253984a72094de129b82d3684a6c0b4d6169a82d3485a680b4ce329982d32de264094c6129882d3084a600b4be1a9782d2d85a5a0b4ae229582d2985a520549e0a938252584a4a0948e12918152182a42092fe1e5dc24b78396d192ce0e59434af889570529e1251c2c9f819370b25e0e4b42c9383925090fe161dc24378586d0b0ce161942c2f858570509e1211c0c1d018370306c0609c0c130182509ade1b5ac36b384d63098de131b82e3585c6a0b8ce17198263184c620d8be1b1782e2d85c5a0b8ae171582e2985c52096de0adac25b382b63096be0ad6c25ab82b530969e12d3415a582b490968e12d1415a182b41034de169ac0d3384a63034be1696c0d2b85a530349e069340d2381a450b486068fc251d81a3705466125bc3cb38695f0d2ae4653c1ca6919470728a0a4fc249b8592f0324e121bc2c338585f0b0ae1613c0c26818470308a0a0fc241b8582f030540609c0c1304e7f0dcfa1b9ec373d06e770fcec1b9d426bf87d7e0dafa1b5bc36b706d6d098fe0b1ec263b82c73098de0b1ac163484c67058c60b184262f86c5d058b60b164262b86c55058a60b1440dbf85b7b036ee12dcc0db785b6b036ce16d8c0daf81b5d0b6b616d682dac85b58036ae1ad580daa81b54096a616d440da784b4b0368e0ad0c253f84a7e0b4f6169e82d3b87a76094e6129c82d3786a6e0b4d6169a82d3386a660b4c616988252f84a5e0b4ba129702d2d85a5a0b4b2169602d2b86a560b4ab70950252984a520b4a212940152782a4e0949612928252384a46054860a90824bf879770d2de1a59c24af8395d0d2ae0e55414a7849470b27e064dc2c978392d0b24e0e494243f858770b0de1619c242f8585d0b0ae1615414278484703074060dc0c1b018270304c06094173f82e7e05cfa135fc36bd87d7709ae6135bc66b686d6b0dad22759c4eb284d630dac20b1ec163d02c79058ee1f1d8163982c71058ce1f198163282c5f1d8bc0b16c162b82c53058a406dfc2dbd81b77096e606dbc0db685b6b0b6d206d9c0db284b630b6c206d7c2dad81b570b6a606d3c15a581b4705686129fc253f05a7b0b4f4169dc3d3b04a73094e4129bc253705a6d094d8169ac2d3505a690b4d01699c4d3305a65134c81298c253105a61094c01697c352f05a5b0b4b41695c452b05a530b4a40a93c152702a4b054940a91c152302a4305484125fc3cbb8496f072da2659c1cb28695f152ae0a53c14a38593f0326e164bc1c96859270724a121fc2c3b8486f0b0da1619c2c328585f0b0ae0a13c14238183a0306e060d80c13818260304a139f8273e86d7909ae20b5b416b486d6505ac20b1f4163a82c6d058d20b194163082c59058a206db42db481b65096c2129f8253d04a76094e4129b8253684a6c094d4169a42d3404a660b4ca4e990253104a61094c01a9782d2d06a560b4a40a938152502a46054840e5b41cb28392d0724a121b42c328183a0306c060980c1284e7f0dcf61b9dc273984d7fb2afc135ec36bd04d770faec135cc36b902d6f05adc0b5b4163f8ec7e058f60b1dc163982c72058d60b1a8163482c670d8cc0b18c163082c570d8ac0b1540dbf85b7b036ee12dcc0db785b6b036ce16d8c0daf81b5d0b6b616d640dab81b55096a616d440da782b4b0368e0ad0c253f84a7e0b4f6169e82d3b87a76094e6129c82d3786a6e0b4d6169a82d3386a660b4c616988252f84a5e0b4ba129702d2d85a5a0b4b2169602d2b86a560b4aa22950252984a520b4a212940152782a4e054960a928152382a46054860a90824bf879770d2de1a59c24af8395d0d2ae0e55414a7829470b27e064dc2c978392d0b24e0e494243f858770b0de1619c242f8585d0b0ae1615414278284d0508e161140c1d018370306c0609c0c130182509cfe339f8273d86e7a09cee1f9d8273986e7209afe1b5ec36bb84d7305ade0b5b816b682c7f058f60b1dc163982c6f0d8dc0b1b4162f86c5e058b60b164162982c52058a206dfc2dbd81b77096e606dbc0db684b6b0b6d206d9c0db285b630b6c206d7c2dad81b570b6a606d3c15a581b4705686129fc253f05a7b0b4f4169dc3d3b04a73094e4169bc353705a6d0d4d8129ac253505a69094d01299c253305a65094c81698c2d3105a610b4c01697c352f05a5b0b4b41695c352b05a530b4a40a93c152702a4b054940a91c152302a4305484125fc3cbb8696f072da1259c1cb28695f0d2ae0a53c14a38593f0326e164bc1c96859270724a121fc2c3b8586f0b0da1219c2c328585f0b0ae0a13c14238183a0306e060d80c13818260304a135bc26b704d6d098de131ac263384c63098be13174262d86c59098ae23154262984c51096de0adac25b382b63096be12d7415ad82b59096ae12d5415a982b510969e0ad2c25a382b43034de129ac2d3481a67094c6129840d2f81a5d094b60695c0d2a81a4f0b4960691c2d2181a3f09476068dc15198496f092ce1257c1cae84957072aa2a53c54a38293f0926e164bc0c938486f090da1219c2c328185f030ba1215c0c2a8584f0b08e0a0fc241b8582f0304e235bc26b707d6b0fad41f59c3eb308d6309ac4231bc363587c670d8c61717c2e2f05c5d116de0adac3db382b63116be12d7415ad82b59116ae12d5415a982b510d69e0ad2c35a382b43034de169ac0d3385a63034be069740d2b81a550b4a60693c2d2585a490348e1690c2d2081a3f0b476068dc15198a96f0f2ce2257c1cae88957072aa1a53c44a38293f1126e164bc0c938586f0b0ce1617c0c2e81857030aa1613c2c26858470b08a0a0fc2c1b8582f0304e135bc26b584d6709ac6131bc263704c6b098d41319c263304c63098c41317c262f04c5b118b41315c262b04c530d8a40adbc15b582b67056c60ad7c15ad82b57056a60ad3c25a702b4d034de129ac0d3384a63034be1696c0d2b85a530349e069340d2381a4505486068fc151d84a390346e0a8cc15188496f092ce1a57e68ab8494f0729a1251c1ca28293f0526e164bc0c938486f090ce1617c2c2b8284f0309a0611c0c228283f0507a0a0dc241a8282f0304e175bc2eb68ac6f118da4f1ac36348ac67118ca4f18c363084c5f0f8b61f15c262984b6f096da0adac15b484b67096ca0ad8c15b084b5f056b612d5c15a984b4f0569612d1c15a181a6f034da0697c2d2d84a530349e1692c0d2385a430347e128ec0d1b82a3309afe1f5ec3ebb84d7307ade0f5b41eb586d6907ace335941eb183d61098fe0b1ec263b82c73078de0f1b4163582c69078ce3b194163182c61098be0b16c262b82c53036fe16dec0dbb84b73036de06db41db585b69036ce06d941db183b61036be16d6c0dab85b530369e12d2c0da382b43094fe129f82d3d85a7a0b4ee1e9d8253984a72074de0e9b81d3683a6c074d60e9a82d3485a68074ce0e9982d32d3264074c60e9881d3083a600b4be1a9782d2d85a5a0b4ae2a9582d2985a520549e0a938252584a4a0948e12918152182a42072ec0e5981c93039240306c0609866b784d6e0fad61f5a83eb387d6619ac613588363786c6b0d8ce1b18c2e2f85c5d0d6de0adac35b382b630d6be12d7415ad82b590d6ae12d5415a982b510d69e0ad2c35a382b43034de169ac0d3385a63034be069740d2785a4b0b486068fc2d1d81a37054660e5180c1306e7f0dcf61b9dc373983d7f19afc0f5ec1ebd03d770faec0f5cc1eb906c7f058f61b1dc163986c6f058d61b19c163183c5f078ba0b16c162c83c570d8aa0b14c162881b7f0b6f606ddc2db981b6f0b6d606d9c2db181b5f036ba0ed6c1dad05b590b6b006d5c1dab01b55036a80ed4c1da881b4f0b69606d1c15a185a7f154fc169ec2d3d05a770f4ec169cc2d3905a6f0d4dc169ac2d3505a670d4cc1698c2d3103a5f074bc0e9741d2e03a5b074b4169642d2c03a57074ac16956892a03a53074a40e9441d2802a4f0549c1692c2d2505a470d48c0a90c152103966072ac060d80c1304e7d0fcea0f5f81ebe86d6e098ba0b164262a82c510b6f212dc40dae84b5a0b6b216d6025ab01b55036a812d44253f04a7a094ec129c8353705a6a114cc16988252f04a5d094b8129682d2c85a58094ac169549d2a04a52094a212940152704a4a0948c0a9081c93039240306c0609846b786d6b0face1b58c563784c6e0f8d61f1a83e3387c66158c6131882e2f85c5e156de0adac3db382b630d6be0ad6c35ab82b531969e12d3415a582b491968e12d1415a182b41034de169ac0d3385a630b4b60695c2d2981a470348a068fc2d1d81a37054660f9f8273d03e7609ce4131f8263d04c76098e40f1b8263684c6c078d40f1a41e3403c66078ca0f1901e3104c61378c013178362d04c560d8a40adb415b482b65056c212d3815a681a6d074d2069942d3081a4d094720a8c41cb70395e070dc2e1b01f3f83e7e07cf61f9e81f3b83e7607ce73d9c846bf86d7b0faee1b5cc563f82c7b0f8ee0b1cc1e378ec6d058d60b1a41e3383c65058c60b184362f82c5b0d8ae0b14c0dbf85b7b036ee16dcc0db781b6d076d60eda40db381b65076c616d840daf85b5b036ae16d4c0da785b4b0368e0ad0c2d3f8aa7e0b4f6169e82d3b87a760b4e6169c81d3783a6e0b4db389b01d3583a6a074d20e9a01d3383a66074ca0e9901d3183a620b4c2169802d2f86a5e0b4b6169682d2b88a560b4a616948152782a4e0b496169282d23cd246054860a9081cb70395e0724c0e4901c370b86c0306c0609816be82d75078fc0f1f4363704c6a118cc13188162f01b4d0b69206d1425a084a7e094f4129d8253906a6e0b4d4229982d3102a5e054b40a958152904a4e0949a12930252505a490b490129182d2293a44094841290425200392607248060d80c1304d6f0dad61f59c26b182c6f058d60b19c163182c5f058b60b15c162984b6f096dc1edac3db507b670f6cc12d8c25b106b5f0d6bc32d6c45ad0cb57116ac1ad4c35a902b4f0569c069bc2d3581a67094c60697c2d2d81a570b4a60a92c0d2382a430346e068d4273f86e7b0fcee139cc1ebf83d7e07af61f5e81ebb83d7607ae72d5c81eb783d6e07ad6335a81eb383d6607ac61b588163f82c7b058ee0b1cc163782c6b058ce0b18c0dbf85b7b036ee12dcc0db785b6b036ce16d8c0daf81b5d076b60ed640dab81b55076a616d440da782b4b0368e0ad0c253f84a7e0b4f6169e82d3b87a76094e6129c82d3786a6e0b4d6169a82d3388a660b4c6169881d2f83a5e0b4bb289701d2d83a5a074b20e9601d2b83a56074aa0e9501d2983a520b4a216940152782a4e054960a928152382a46054860a90814af0294e0724c0e4900c1b01826baade1f5ac3eb3db563b48de0b1ac3e3382c63b08be0b16eba2b82c53036de16dac0db385b63036be16d6c0dab85b530369e16d2c0da382b430b4df589b82d3585a6a0b4ce1e9982d3185a620b4be1a9782d2d85a5a0b4af549582d2985a520549e0a9382d2585a4a0b48f50918152182a42a42de1e59e80afcc1570529f2451c2c9f819370b25e0e4b42c93839250b0de1619c2c2f858570509e1611c0c1d018370306c0609c0c130182509cfe1b9ec373b84e7309afe1f5f826bd86d7a09aee1f5d826b986d7205ade0b5b816b682c7f0f8fc0b1ec163b82c73058e40b1ac163502c69058ce1b198163182c61058ae1b158162a81b7f036f606ddc0db981b6f036d606d9c0db181b5f036ba06d6c0dac81b57036aa06d4c0da881b4f0369606d1c0da18193e090fc1e1d8343706866090bc12170342b088540509c0a1301423048440306c139fc3f3f04e7b0dcf4139dc3f3b04e730dce4135fc36bd86d7709ae60b5bc16b702d6d058fe0b1ec163b82c73058de1b1b8163682c5f0d8bc0b16c162c82c53058a40b1440dbf81b7b036ee06dcc0db781b6d036d606da40db381b65036c606d840daf81b5b036ae06d4c0da781b4b0368e06d0c0c9f0487e0f0ec1a1b8343604866090c81a178342b0284e0508c060d83eb784d6e0fad61f5a83eb387d660fac6135883e3786c6b0f8ce1b18c3db782b6b0f6ce0ad8c45af84b5d056b60ad6445ab84b55056a60ad4435a782b4b0d68e0ad0c0d3781a6b034ce0698c0d2f81a5d034b6069640d2b81a55034a6069440d2781a4d034960691c0d2281a430347e068ec0d1b81a3309ade135ac26b384d63098de131b8263584c6a098ce13198263184c62098be13178262d88c5a098ae13158262986c52056de0adac15b502b67096cc0ad8c15af84b5e056b60ad5c15a982b52034de069ac0d3381a63034be0696c0d2b81a530349e069340d2581a490348e069140d2181a410347e068f40d1d81a370346a068cc3eb787d6b0face1f58c3e3782c6b0f8ce0b18e3a2f82c5b8c8ae0b14c0db781b6b036ce06d8c0daf81b5b036ae06d4c0da781b4b0368e06d0c0c9f0786e0f0cc1a17a282b0284e8808c060d8273f86e7e0dcfa1b5ec3ebd06d790faee1f5d826b986d710face1f5983eb284c7f058f6131dc163984c6f1d8da0b1ac163484c671d8ca0b18c163084c5f058b60b164262b82c53058a206dfc0dbf01b7b0b6f406ddc0dbb01b73096e406dbc0db701b6d036d806dac2db501b690b6d006d9c0db301b65036c806d8c25b101b61096c006d7c0daf01b5b0b6b406d5c0dab01b530b6a406d3c0da701b4b0969406d1c0da301b4305684069fc0d3d81a77034e6069bc0d3681a6b034d20699c0d3281a63034c20697c0d2d81a57034a60693c0d2581a4703486125fc3cbb8496f072da3259c1cb28695f112ae0a53c24a38193f0727a064dc0c9a8192f0324e121fc2c3b8486f0b0da1619c2c328585f0b0ae0a13c24238183f0307c160f40c178182e03044139fc373e86e7b0dcf41b9dc3f3b06e7509afe1f5f836be86d6f0dadc1b5b4263f82c7b098ee0b1cc263782c6b058d21319c163182c61098be1b174162d82c59098ae1b154162982c51036fe06df80dbd85b7a036ee06dd80db984b72036de06db80db585b6a036ce06d980db185b62036be06d780dae81b5c036b616d680dac85b58036ae06d580daa81b54036a612d480da884b500369e06d380da584b4a0368e06d180da182b42034fe069ec0d3b81a73034de069ac0d3381a63034be069740d2d85a5a034b2169600d2b81a56034aa069500d2981a510349e0692c0d2381a43092fe1e5dc34b786967092be0e57434ab839550529e1251c0c9f8393d0326e064d40c9781927090fe161dc2c3785867090be161742c2d058570d0ac161545c2a0284f0908e060fc0c1f0583d0305e060b80c1102e7f05cfc0b9f426bf86d7b0faee135cc26b78ed6d0dad61b5a44eb389d6509ac61b584163d82c7a058f20b1dc3e3b02c73058e20b19c3e3302c65058be3b178162d82c57058a60b1480dbf81b7e036f616de80dbb81b76036e612dc80db781b6e036da06db00db585b6a036d216da00db381b66036ca06d900db184b62036c212d800daf81b5e036b616d680dab81b56036a616d480da781b4e036960ad280da381b46036860ad080d3f81a7b034ee069cc0d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034ae0694c0d2781a4b0348e0690c24bf87977092de0e5b44cb3839650d2be2a55c14a7829470327e0e4f40c9b819350325e0649c243f85877090de161b42c33858650b0be1615c1427828470307e060f82c1e8182f0305c06088273f04e7d0daf2135c416b682d690daca0b584163e82c75058da0b1a4163282c61058b20b1440dbf04b7a036ec12dc80db701b6d036d812da80db485b68036cc06d940db204b62036c212d800daf05b5a036ac16d480da702b4a0368c0ad080d3681a69034ca069841cb6839650727a064d42436858650307c160f40c1701822 20 1048575 8 255 11 2047 19 524287
def cc_54_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xf9057db1739d98f0e2ddc459a19731f2461e20bd06d71c86be25d255794efd1554a0723bc5496f09abca193c3d24d2b47a207599cea809c80d2e8a8520b0879c9000f1b8482bcb427308004e 0x4d6f06d6b06d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5704b6f04b6e07b6b07b6a07b6707b6604b6304b6203b5f03b5e02b4f02b4e04a6f05a6b07a6704a6306a5f05a5b06a5705a5302a4f02a4b02a4702a430ea3f01a3d05a3b05a390ea3701a3505a3305a3104e7f04e7e07e7b07e7a07e7707e7604e7304e7204d7f06d7b06d7704d7303c7f03c7e03c7b07c7a03c7703c7603c730ac7203c6f03c6e03c6d03c6c03c6b08c6a03c6908c6803c6703c6603c6503c6403c6308c6203c617e46003c5f03c5e03c5b06c5a03c5703c5603c5306c5202b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5304a7f05a7b07a7704a7308a6f01a6d05a6b05a6908a6701a6505a6305a6106a5f05a5b06a5705a5303a4f01a4d03a4b03a4903a4701a4503a4305a4102a3f02a3b02a3702a330294e0293e0686e0685e04e7d07e7504d7e04d7d06d6e04c5d02c5904c5502c5101b7e04b7a01b7907b7801b7604b7201b7104b7001b6e08b6a01b6606b6201b5e01b5d01b5c04b5a01b590cb5801b5601b5501b5404b5201b5104b5001b4e04b4a01b4602b4201a5d04a5a01a5905a5801a5601a5501a5401a5103956039540193e0192e04d7e04d7a04d7604d7202d6e04c7e02c7202c6a04c6604c5602c5501b7e04b7a01b7604b7201b6e06b6a01b6606b6201b5e01b5d01b5c04b5a01b5908b5801b5601b5501b5404b5201b5104b5001b4e02b4a01b4904b4801b4602b4201b4102b4001a5d01a5901a5501a510193e0192e08d6f06d6b07d6706d630ac6f02c6b07c6702c6306c5f02c5b06c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b4f01b4b01b4701b430aa6f04a6e07a6b07a6a07a6707a660aa6304a6201a5f01a5e02a4f02a4e0ca4b04a4a0ca4704a4602a4302a4201a3f01a3e0685e08e7f0ce7e07e7b07e7a07e7707e760ae737c67208d7f06d7b07d7706d730ac7f02c7b07c7702c7308c6f7b46d02c6b02c6908c670cc6502c6302c6106c5f02c5b06c5702c5301b7f01b7e01b7b07b7a01b7701b7601b730ab7201b6f01b6e01b6d01b6c01b6b08b6a01b6908b6801b6701b6601b6501b6401b630cb6201b617a36001b5f01b5e01b5b08b5a01b5701b5601b5306b5201b4f01b4e01b4b0cb4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430193e0192e0686e0685e08d6f8556e07d6b07d6a07d6707d660ad638456208c6f06c6b07c6706c630ab6f02b6b07b6702b6308b5f8335d02b5b02b5908b577035502b5302b5106b4f02b4b06b4702b430aa6f05a6b07a6705a638225f01a5d05a5b05a5908a5701a5505a5305a5106a4f05a4b08a4705a4302a3f05a3b8023702a330a96f079677f15f0395d08957039550694f089470293f7d1370592f791270786f078670685f0685e0685d0684f0684e068420283f0b8370582f0582706d6f06d6b06d6706d6306c6f02c6b06c6702c6306c5f02c5b06c5702c5305b6f05b6b05b6705b6305b5f05b5b05b5705b5302b4f05b4b05b4702b43069560786e078660685e0284e068460583e0183604d6f04d6e07d6b07d6a07d6707d6604d6304d6204c6f04c6e06c6b06c6704c6304c6202b6f02b6b02b6702b6302b5f02b5d02b5b02b5902b5702b5502b5302b5102b4f02b4d02b4b02b4702b4502b4304a6f05a6b05a6704a6305a5f01a5d05a5b05a5905a5701a5505a5305a5105a4f05a4d05a4b05a4705a4505a4302a3f02a3b02a3702a3304d6f06d6b07d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5304b6f05b6b05b6704b6305b5f05b5b05b5705b5302b4f02b4b02b4702b43079660294e0786e078660685e76056028460583e0183604d6f04d6e04d6d04c6f04c6b04c6704c6304c5f04c5d04c5b06c5904c5708c5504c5304c5102b6f02b6b02b6a02b6704b6602b6302b5704b5602b5502b4f04b4e02b4b02b4702b4302b4204a6f04a6b04a6704a6304a5f01a5d04a5b05a5904a5701a5504a5304a5106a4f05a4b0aa4705a4302a3f02a3b02a3702a330496f049670495f0395d04957039550694f0a9470293f029370592f651270286f0486a04867048660485704856078550684f078470283f028370582f0582704d6f04d6b04d6704d6302c6f02c6d02c6b02c6a02c6704c6602c6502c6302c5f04c5e02c5b02c5702c5302c5204b6f04b6e04b6d04b5f06b5e04b5b04b5a04b5708b5604b5304b5202b4f02b4e02b4d02b4704b4502b4302b4204a6f04a6b04a6704a6306a5f05a5b0aa5705a5302a4f02a4b02a4702a4304a3f01a3d04a3b05a3904a3701a3504a3304a310496f049670695f0a9570294f029470493f0393d04937039350592f641270486f0486d0486a0486704866078650685f078570284f028470283f0283d0483a028370283602835028340582f0582704e7f04e7e04e7b04e7704e7304e7204d7f04d7e04d7b04d7a04d7704d7604d7304d7204d6f04d6e04d6d04d6c04d6704d6604d6504d6404d6306d6202c7f02c7b02c7a02c7704c7602c7302c6f04c6e02c6d04c6c02c6b02c6702c6502c6302c6204b7f04b7e04b7b04b7a04b7704b7604b7304b7204b6704b6604b6504b5f04b5e06b5d06b5c02b4f02b4e02b4d02b4c02b4704b4502b4302b4204a7f04a7b04a7704a7306a6f05a6b06a6705a6304a5f10a5d04a5b04a5904a5704a5504a5305a5102a4f02a4b02a4702a4308a3f01a3d05a3b05a3908a3701a3505a3305a310497f049770696f069670495f1095d04957049550294f029470893f0393d08937039350592f631270487f0487a04877048760686f0686d06867088650285f0285e0285d0284f0284e028420283f0283d02837028350582f0582704d6f04d6e06d6b06d6704d6304d6202c6f02c6b02c6702c6302c5f06c5e02c5d02c5b02c5702c5502c5302c5204b6f04b6e07b6b07b6a07b6707b6604b6304b6204b5704b5604b5502b4f02b4e02b4d02b4708b4502b4302b4204a6f05a6b07a6704a6306a5f05a5b06a5705a5302a4f02a4b02a4702a4308a3f01a3d05a3b05a3908a3701a3505a3305a310496f079670695f069570294f029470893f0393d08937039350592f0c9270486f078670685f0685d06857088550284f028470283f0283d02837028350582f0582704d6f04d6e04d6b04d6a04d6704d6604d6304d6204c6f04c6b04c6704c6304c5f04c5e06c5d02b6f02b6b02b6702b6302b5f04b5e02b5d02b4f04b4e02b4b02b4702b4302b4204a6f04a6b04a6704a6304a5f01a5d04a5b04a5904a5701a5504a5305a5106a4f05a4b06a4705a4302a3f02a3b02a3702a330496f049670495f0395d04957039550694f069470293f029370592f0c9270486f048670485f0485e0685d0684f028470283f028370582f0582704d6f04d6b04d6704d6304c6f04c6b04c6a04c6704c6604c6302c5f02c5e02c5d04b6f04b6e04b6b04b6704b6304b6204b5f04b5b06b5a04b5904b5704b5604b5304b5104b4f04b4b04b4a04b4704b4604a6f04a6b04a6704a6306a5f05a5b06a5705a5304a4f04a4b04a4704a4304a3f04a3b04a3704a330496f049670695f069570494f049470493f049370592f621270486f0486a04867048660685f068570484f0484a04847048460283f0283e0283d0582f0582704d6f06d6b06d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5304b6f04b6e07b6b07b6a07b6707b6604b6304b6204b5f04b5e05b5b05b5a05b5705b5605b5304b5201b4f01b4e01b4701b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310496f079670695f069570294f029471093f0393d10937039350192f019270486f058670585f058570284f018470283f0283d01837018350182f0182701e7f01e7e01e7b07e7a01e7701e7601e7304e7204d7f06d7b06d7704d7301d6f01d6e05d6d04c7f0ac7e04c7b07c7a04c7707c7604c730ac7201c6f01c6e04c6d04c6c01c6b01c6a01c6901c6801c6701c6601c6501c6401c6301c6210c616e46004c5f06c5e06c5b06c5a04c5706c5606c5306c5202b7f02b7b02b7a02b7707b7602b7301b6f01b6e02b6d04b6c01b6b01b6901b6701b6501b6301b6202b6102b6002b5f06b5e02b5b02b5702b5302b5201a7f01a7b01a7701a7301a6f01a6e01a6d01a5f01a5e01a5b01a5901a5305a5201a5101a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330497f079770196f0396d01967019650695f069576714f0394d04947039450293f029370192f019270487f0587a05877098760186f0186e0586d0b86c0186701865018620585f058570284f0284e0284d0283f0283e028320182f0182704e7f04e7b04e7704e7304d7f04d7e04d7b04d7a04d7704d7604d7304d7204d6f04d6e04d6b10d6a04d6704d6604d6306d6202c7f02c7b02c7a02c7704c7602c7302c6f04c6e02c6b02c6702c6302c6201b7f04b7e01b7b01b7a01b7704b7601b7301b7201b6f06b6e01b6b01b6a01b6708b6601b6301b6201b5f04b5e01b5d05b5c01b4f02b4e01b4701b4301b4201a7f01a7e01a7b01a7701a7304a7201a6f01a6b01a6701a6301a5b04a5a01a5904a5801a5701a5601a5501a5401a5301a5101a4f01a4b02a4a01a4701a4601a4301a3701a3601a350497f049770696f6a1670495f1095d04957049550294f029470193f0193d01937039350192f019270487f0487a04877048760586f058670285f0285e0285d0284f0284e028420183f0183d01837028350182f0582d018270182504d6f06d6b06d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5704b6f04b6e07b6b07b6a07b6707b6604b6304b6204b5f04b5e02b4f02b4e04a6f05a6b07a6704a6306a5f05a5b06a5705a5302a4f02a4b02a4702a4310a3f01a3d05a3b05a3910a3701a3505a3305a3104d7c03d7803d7410d7004c7c02c700fb7c01b7803b7401b7005b5c01a7c05a7004a5801a540b87c03e7f03e7e03e7b07e7a03e7703e7603e7304e7204d7f06d7b06d7704d7304c7f0ac7e04c7b07c7a04c7707c7604c730ac7203c6f03c6e04c6d04c6c03c6b03c6a03c6903c6803c6703c6603c6503c6403c6303c6210c616b46004c5f06c5e06c5b06c5a04c5706c5606c5306c5202b7f02b7b02b7a02b7707b7602b7302b6f03b6e02b6d04b6c02b6b02b6902b6702b6502b6302b6202b6102b6002b5f06b5e02b5b02b5702b5302b5204a7f05a7b07a7704a7303a6f01a6d03a6b03a6903a6701a6503a6305a6106a5f05a5b06a5705a536a24f01a4d04a4b05a4904a4701a4505a4305a4102a3f02a3b02a3702a330396e0395e098760386e0b86c0284e0283e01c5404d7c01d7801d7410d7004c7c02c706837c01b7801b7403b700397c039540b87c04e7f04e7b04e7704e7304d7f04d7e04d7b04d7a04d7704d7604d7304d7204d6f04d6e04d6b10d6a04d6704d6604d6306d6202c7f02c7b02c7a02c7704c7602c7302c6f04c6e02c6b02c6702c6302c6203b7f04b7e03b7b03b7a03b7704b7603b7303b7203b6f06b6e03b6b03b6a03b6708b6603b6303b6204a7f04a7b04a7704a7306a6f05a6b6726705a6304a5f10a5d04a5b04a5904a5704a5504a5305a5102a4f02a4b02a4702a4303a3f01a3d03a3b05a3903a3701a3503a3303a310397e03956039540294603936048760285e0284e04e7e04e7d04d6d06d6908d6504d6102c7a04c7604c6602c6504c5e02c5201b7e04b7a01b7604b7201b6e01b6d01b6c04b6a01b690cb6801b6601b6501b6404b6201b6104b6001b5e08b5a01b5606b5201b4e02b4a01b4602b4201a6d01a6901a6501a610193e0192e048760486602d7d02d7a04d7602d7504d6e02d6204c7e04c7d06c6e04c6a08c6604c6202c5e02c5d01b7e04b7a01b7907b7801b7604b7201b7104b7001b6e08b6a01b6606b6201b5e02b5a01b5602b5201b4e01b4d01b4c04b4a01b490cb4801b4601b4501b4404b4201b4104b4001a4d04a4a01a4905a4801a4601a4501a4401a4103946039440193e0192e04876028460284404e7c04e7404d7c06c6c02c5c08b7806b7001b6c04b6801b640cb6001b4c11b4801b4408b4004d7a04d7602d6e02d6d04c7e04c7206c6a04c6904c6604c6104c5601b7e04b7a01b7604b7201b6e06b6a01b6606b6201b5e04b5a01b5604b5201b4e04b4a01b4904b4801b4604b4201b410cb400193e0192e04876048560284e04d6f06d6b07d6704d6302c6f02c6b02c6702c6302c5f0cc5e02c5b02c5702c5302c5201b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4704a6f04a6e07a6b07a6a07a6707a6604a6304a6206a5f06a5e0ca5b08a5a0ca5708a5606a5306a5201a4f01a4e01a3f01a3e04e7f06e7b07e7704e7304d7f6557e04d7b07d7a04d7707d7604d736457204d6f06d6e6356b0cd6a04d670cd6606d6306d6202c7f02c7b02c7a02c7707c7602c7302c6f6246e02c6b02c6702c6302c6201b7f01b7e01b7b07b7a01b7701b7601b7304b7201b6f01b6e01b6b08b6a01b6701b6601b6306b6201b5f01b5e01b5d01b5c01b5b04b5a01b5904b5801b5701b5601b5501b5401b5310b5201b516135001b4f01b4e01b4b02b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a430193e0192e098760285e0284e04d6f06d6b07d6704d6304c6f7446e04c6b07c6a04c6707c6604c637346204c5f06c5e7245b7145a04c577045606c5306c5202b6f02b6b02b6a02b6707b6602b6302b5f6f35e02b5b02b5702b5302b5204a6f05a6b07a6704a6306a5f05a5b6d25705a536c24f01a4d04a4b05a4904a4701a4505a4305a4102a3f02a3b02a3702a330496f079670695f691576614f0394d04947039450293f029370592f601270486f0986a07867098660685f0b8570284f0284e0284d0283f0283e028320582f05827 19 524287 8 255 11 2047 20 1048575
def cc_54_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x7f0befda0defd73b15d73756da98da2a532b346197abc4dd724cad3a255b98a1d35257ca352b40eb87ce9cef159ac64310905bcc8a89e14518268444471475e60c4ce115e81913413fc8004f 0x6d7f06d7d06d7b06d7906d7706d7506d7306d7106d6f06d6b06d6706d6303c7f07c7e03c7d9f47c03c7b03c7a03c7903c7803c7707c7603c7507c7403c7303c7203c7103c7003c6f04c6e03c6b03c6a03c6707c6603c6303c6206b7f06b7d02b7b02b7906b7706b7502b7302b7106b6f02b6b06b6702b6306b5f02b5b06b5702b5303b4f03b4d02b4b02b4903b4704b4502b4302b4107a7f01a7d05a7b05a7907a7701a7505a7305a7107a6f05a6b07a6705a6306a5f05a5b06a5705a5303a4f01a4d03a4b05a4903a4701a4503a4303a4102a3f05a3b06a3702a330397e0397c03956039460787e0786e0683605c5c05a5801a5407d6f06d6b07d6703c6f03c6e06c5f06c5e07b6f02b6b07b6702b6306b5f02b5b06b5702b5309b4f04b4d02b4b02b4909b4704b4502b4302b4107a6f05a6b07a6705a6306a5f05a5b08a5705a539d24f01a4d05a4b05a491ca4701a4505a4305a4102a3f05a3b09a3702a330395e0786e0983603d7f03d7e03d7d03d7c03d7b07d7a03d7907d7803d7703d7603d7503d7403d7307d7203d719c57003d6f03d6e03d6b07d6a03d6703d6603d6304d6207c7f08c7d06c7b06c7907c7707c7506c7306c7107c6f06c6b07c6706c6307b7f09b7d02b7b02b7907b7707b7502b7302b7107b6f02b6b07b6702b6303b5f04b5d02b5b02b5903b5703b5502b5302b5106b4f02b4b06b4702b4307a7f01a7d05a7b05a7907a7701a7505a7305a7107a6f05a6b07a6705a6303a5f01a5d03a5b03a5903a5701a5503a5305a5106a4f05a4b08a4705a4302a3f05a3b09a3702a330395e0394e0787e0786e0983607d6f07d6b07d6707d6307c6f02c6b07c6702c6309c5f02c5b09c5702c5301b6f01b6b01b6701b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6e0ca5f06a5e0ca5b08a5a0ca5708a560ca5306a5202a4f02a4e09a4b04a4a09a4704a4602a4302a4201a3f01a3e07d7f0cd7d07d7b06d7907d7707d7507d7306d7107d6f07d6b07d6707d6307c7f09c7d02c7b02c7907c7707c7502c7302c7107c6f02c6b07c6702c6309c5f02c5b09c5702c5301b7f01b7e01b7d01b7c01b7b07b7a01b7907b7801b7701b7601b7501b7401b7307b7201b719a37001b6f01b6e01b6b07b6a01b6701b6601b6304b6201b5f01b5e01b5b0ab5a01b5701b5601b5306b5201b4f01b4e01b4b04b4a01b4701b4601b4302b4201a7f01a7e01a7d01a7c01a7b01a7901a7701a7501a7305a7201a7105a7001a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a430397e0397c0193e0192e0787e0786e0984607c6fa546d07c6b06c6907c6707c6507c6306c6107c5f07c5b07c5707c5307b6f09b6d02b6b02b6907b6707b6502b6302b6107b5f02b5b07b5702b5309b4f02b4b09b4702b4307a6f01a6d05a6b05a6907a6701a6505a6305a6107a5f05a5b07a5705a53a324f05a4ba024705a4302a3f05a3b09a3702a330796f0396d07967039650795f079579e14f9b1470293f099370592f991270786f0786e0786d0785f0785e078520784f078470283f0783a07837098360582f0582704d6f04d6e06d6b06d6a07d6706d6604d6304d6204c6f04c6e06c6b07c6704c6304c6204b6f02b6b04b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4b04b4702b4304a6f05a6b05a6704a6305a5f01a5d05a5b05a5905a5701a5505a5305a5105a4f05a4d05a4b05a4705a4505a4302a3f04a3b04a3702a3304d6f04d6b04d6704d6304c6f04c6e02c6b02c6a02c6702c6602c6302c6204c5f04c5e04c5b08c5a04c5704c5604c5306c5202b6f04b6e02b6b02b6a02b6704b6602b6302b6202b5f04b5e02b5b02b5a02b5704b5602b5302b5204a6f04a6b04a6704a6305a5f05a5b05a5705a5304a4f01a4d04a4b04a4904a4701a4504a4305a4102a3f02a3d02a3b04a3902a3704a3502a3302a310486604d6f04d6e04d6b04d6704d6304d6204c6f04c6e02c6b04c6704c6304c6204c5f04c5d04c5b06c5a04c5704c5604c5504c5404b6f04b6e02b6b02b6a04b6702b6604b6304b6204b5f04b5e04b5d04b4f04b4e06b4d04a6f04a6b04a6704a6305a5f05a5b05a5705a5304a4f04a4b04a4704a4305a3f01a3d05a3b05a3905a3701a3505a3305a310486604c5f07c5b07c5704c5304b5f02b5b04b5704b5304b4f0ab4b04b479534304a5f05a5b05a5704a5305a4f05a4b05a4705a4305a3f04a3b04a3705a330785604d6f07d6b07d6704d6304c6f02c6b04c6702c6304c5f02c5b04c5702c5304b6f05b6b05b6704b6305b5f05b5b05b5705b5302b4f04b4b04b4702b43079660786e0685e970560284e0284c96046940440583e0183604d6f04d6e04d6d04c6f04c6b06c6904c6704c6304c6104c5f04c5d04c5b04c5706c5504b6f02b6b04b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4b04b4702b4304a6f04a6b04a6704a6304a5f01a5d04a5b05a5904a5701a5504a5304a5106a4f05a4b06a4705a4302a3f04a3b04a3702a330496f049670495f0395d04957039550694f069470293f049370592f8d1270486f0486d04867078650485f0485d04857078550684f068470283f048370582f0582706d6f06d6d04d6b04d6905d6705d6504d6304d6101c6f01c6d01c6701c6501c6304c5f06c5b05c5704c5304b6f04b6d02b6b02b6904b6704b6502b6302b6104b5f02b5b04b5702b5304b4f02b4b04b4702b4301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330d96f0396d0d967039650495f079570694f069470293f049370192f019270186f0186d05867058650485f058570184f058470283f048370182f0182701e7f05e7e01e7d04d7f06d7b06d7704d7301d6f01d6d01d6b06d6901d6706d6501d6301d6104c7f04c7e06c7b06c7a06c7707c7604c7304c7201c6f01c6e01c6d01c6c01c6b01c6a06c6906c6801c6701c6606c659146401c6301c6201c6101c6004b7f02b7b04b7702b7301b6f01b6d01b6b02b6901b6706b6501b6301b6104b5f02b5b04b5702b5304b4f04b4d02b4b02b4904b4704b4502b4302b4101a7b05a7a01a7901a7701a7601a7301a7101a6701a6601a6501a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330497f079770196f0196d01967039650695f069570694f0394d06947039450293f049370192f019270487f058770186f0186d01867058650585a05857068560584706846058450283f048370182f0182706d6f06d6d03c6f03c6d04c5f06c5b04c5304b6f04b6d02b6b02b6904b6704b6502b6302b6104b5f02b5b04b5702b5304b4f02b4b04b4702b430da6f01a6d05a6b05a690da6701a6505a6305a6104a5f05a5b07a5704a5306a4f05a4b06a4705a4302a3f04a3b04a3702a3304d7f06d7b06d7704d7303d6f03d6d03d6b06d6903d6706d6503d6303d6104c7f04c7e06c7b06c7a06c7707c7604c7304c7203c6f03c6e03c6d03c6c03c6b03c6a06c6906c6803c6703c6606c658f46403c6303c6203c6103c6004b7f02b7b04b7702b7303b6f03b6d02b6b02b6903b6706b6502b6302b6104b5f02b5b04b5702b5304b4f04b4d02b4b02b4904b4704b4502b4302b4104a7f05a7b07a7704a7303a6f01a6d03a6b05a6903a6701a6503a6303a6106a5f05a5b06a5705a5306a4f01a4d05a4b05a4906a4701a4505a4305a4102a3f04a3b04a3702a330397603966068560684604e7e04e7d06d7904d7106d6504c6d02c6904c6502c6101b7e04b7a01b7604b7201b6e01b6d01b6c04b6a01b690cb6801b6601b6501b6404b6201b6104b6001b5e06b5a01b5606b5201b4e04b4a01b4602b4201a6d01a6901a6501a610193e0192e06d6f06d6b06d6706d6306c6f02c6b06c6702c6306c5f02c5b06c5702c5301b6f01b6b01b6701b6301b5f01b5701b5301b4f01b4b01b4701b430ca6f04a6e07a6b07a6a07a6707a660ca6304a6201a5701a5602a4f02a4e06a4b04a4a06a4704a4602a4302a4201a3f01a3e06e7f06e7b06e7706e7306d7f8d57e06d7b06d7a06d7707d7606d7306d7206c7f02c7b06c7702c7306c6f02c6b06c6702c6306c5f06c5d02c5b02c5906c5706c5502c5302c5101b7f01b7e01b7b07b7a01b7701b7601b730ab7201b6f01b6e01b6b06b6a01b6701b6601b6306b6201b5f01b5e01b5d01b5c01b5b06b5a01b598c35801b5701b5601b5501b5401b5306b5201b5106b5001b4f01b4e01b4b06b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b05a5a01a5905a5801a5701a5601a5501a5401a5301a5101a4f01a4b01a4701a4303956039540193e0192e06866068560183e0b83c06d6f06d6b06d6706d6306c6f9246e06c6b06c6a06c6707c6606c6306c6206b6f02b6b06b6702b6306b5f02b5b06b5702b5306b4f06b4d02b4b02b4906b4706b4502b4302b419026f05a6b07a6705a6306a5f05a5b06a5705a5306a4f01a4d05a4b05a4906a4701a4505a4305a4102a3f05a3b06a3702a338e16f079670695f069570694f0394d06947039450293f069370592f8b1270786f078670685a06857068560684706846890450283f068370582f0582707d6f04d6e07d6b07d6a07d6707d6607d6304d6206c6f06c6b06c6706c6306b6f02b6b06b6702b6306b5f04b5d02b5b02b5906b5704b5502b5302b5106b4f02b4b06b4702b4305a6f05a6b05a6705a6305a5f01a5d05a5b05a5905a5701a5505a5305a5105a4f05a4b05a4705a4302a3f05a3b05a3702a330685e0684e04d6f04d6b04d6704d6304c6f04c6e04c6b04c6a04c6704c6604c6304c6202c5f02c5e02c5b02c5a04c5704c5602c5302c5202b6f04b6e02b6b02b6a02b6704b6602b6302b6202b5f04b5e02b5b02b5a02b5704b5602b5302b5204a6f04a6b04a6704a6305a5f05a5b05a5705a5304a4f01a4d04a4b04a4904a4701a4504a4305a4102a3f02a3d02a3b04a3902a3704a3502a3302a3104c5f06c5b07c5704c5304b5f04b5b04b5704b5304b4f08b4b04b4702b4304a5f05a5b05a5704a5305a4f05a4b05a4705a4305a3f04a3b04a3705a3307d6f06d6b07d6706d6307c6f02c6b07c6702c6306c5f02c5b06c5702c5305b6f05b6b05b6705b6305b5f05b5b05b5705b5302b4f05b4b05b4702b430695e0786e07866890560284e0284c88046870440583e0183604d6f04d6e04d6d04c6f04c6b04c6704c6304c5704c5607c5504b6f02b6b04b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4b04b4702b4304a6f04a6b04a6704a6304a5f01a5d04a5b05a5904a5701a5504a5304a5106a4f05a4b08a4705a4302a3f04a3b04a3702a330496f049670495f0395d04957039550694f089470293f049370592f0c9270486f048670485704856078550684f078470283f048370582f0582704d6f04d6d04d6b04d6707d6504d6304c6f04c6e04c6d04c5f06c5e04c5704c5304c5204b6f02b6b04b6702b6304b5f02b5b04b5702b5304b4f04b4d02b4b02b4904b4704b4502b4302b4104a6f04a6b04a6704a6306a5f05a5b08a5705a5304a4f01a4d04a4b05a4904a4701a4504a4304a4102a3f04a3b04a3702a330496f049670695f089570494f0394d04947039450293f049370592f7c1270486f0486d04867078650685f078570484f0484d04847068450283f048370582f0582704d6f04d6b04d6704d6304c6f04c6e04c6b04c6a04c6704c6604c6304c6202c5f02c5e02c5702c5302c5202b6f04b6e02b6b02b6702b6302b6202b5f02b5b02b5a02b5704b5602b5302b4704b4602b4504a6f04a6b04a6704a6306a5f05a5b06a5705a5304a4f01a4d04a4b05a4904a4701a4504a4304a4102a3f02a3b02a3702a330496f049670695f069570494f0394d04947039450293f029370592f7b1270486f048670685f028570484f0484d02847028450283f0283d02837048350582f0582708e7f08e7e07e7b07e7a07e7707e7608e730ae7208d7f06d7b07d7706d7301c7f0ac7e01c7b01c7a01c7707c7601c7301c7201c6f05c6e01c6d05c6c01c5f05c5e01c5701c5301c5208b7f02b7b07b7702b7308b6f08b6d02b6b02b6908b6708b6502b6302b6106b5f02b5b06b5702b5301b4f01b4d01b4b02b4901b4708b4501b4301b4101a7f01a7e01a7b01a7701a7305a7201a6b05a6a01a6905a6801a6701a6601a6501a6401a6301a6101a5f01a5b05a5a01a5701a5601a5301a4701a4601a4501a3f01a3b01a3701a330a97f079770896f0c96d08967089650695f089570194f0194d01947039450293f089370192f019270587f058770586f0686e0586d0585f0685e058520184f0184d01847058450283f058370182f0582d018270182504d6f06d6b06d6704d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5304b6f04b6e07b6b07b6a07b6707b6604b6304b6201b5f01b5e01b5701b5301b5202b4f02b4e02b4b02b4a02b4702b4602b4302b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310496f079670695f069570294f029470e93f0393d0e937039350192f019270486f058670585f018570284f028470583f0583d01837018350182f0182704e7f04e7e07e7b07e7a07e7707e7604e7304e7204d7f06d7b06d7704d7301c7f01c7e01c7b07c7a01c7701c7601c730ac7201c6f01c6e01c6d01c6c01c6b08c6a01c6908c6801c6701c6601c6501c6401c6308c6201c618146001c5f01c5e01c5b06c5a01c5701c5601c5306c5202b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5301b4f01b4e02b4d01a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4e01a4d01a3f01a3e01a3b01a3901a3302a3201a310497f079770896f0396d08967039650695f069570194f0394d01947019450293f029370192f019270487f058770586f0686e0586d0585f0685e058520184f0584d01847018450283f028370182f0182708e7f08e7e07e7b07e7a07e7707e7608e730ae7208d7f06d7b07d7706d7303c7f0ac7e03c7b03c7a03c7707c7603c7303c7208b7f02b7b07b7702b7308b6f08b6d02b6b02b6908b6708b6502b6302b6106b5f02b5b06b5702b5303b4f03b4d02b4b02b4903b4708b4502b4302b410aa7f05a7b07a7705a7308a6f0ca6d05a6b05a6908a6708a6505a6305a6106a5f05a5b08a5705a5303a4f01a4d03a4b05a4903a4701a4503a4303a4102a3f05a3b08a3702a330397e039660396403956039460686e0685e 19 524287 7 127 11 2047 20 1048575
def cc_54_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xd76d35198d1467283ac4ea6f7b8b76d2d198b106eb897a6eea91159d8da5d329426637b2872da01b67c485b4f961b7158dc4d3211ab442884e34e2f3347d7f1f2045353057ec002b 0x6d6f07d6e06d6d06d6706d6506d6306d6206c6707c6606c6506c5f06c5e06c5d06b6f02b6b06b6702b6306b5f02b5b06b5702b5306b4f06b4d02b4b02b4906b4706b4502b4302b4101a6f01a6b01a6901a6701a6301a6101a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330192e04c5f02c5b04c5704c5304b5f02b5b08b5704b5304b4f06b4b04b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330192e07c5f06c5b06c5906c5306c5107b5f02b5b07b5702b5306b4f02b4b06b4702b4301a5f06a5b01a5701a5301a4f08a4b01a4701a4302a3f09a3b09a3702a3306d6f06d6e06d6d07c6f07c6e0cc6d07c5f07c5e06c5b06c5906c5307c5206c5107b6f07b6e09b6dbd36c02b6b02b6907b6707b6502b6307b6202b6102b6007b5f02b5b07b5702b5306b4f02b4b06b4702b4301a6f01a6e01a6d01a6c01a6b01a6901a6701a6501a6307a6201a61bc26001a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330192e04c5f06c5b06c5a06c5707c5604b5f06b4f04a5f02a5b04a5702a5304a4f02a4b02a4904a4702a4302a4104a3f02a3b04a3702a330195f0195b019590195701953019510194f0194b01947019430193f0193b019390193701933019310192f0192b019270192304d6f06d6d06d6b06d6a06d6707d6606d6504c6f0cc6e06c6d06c5f06c5e06c5d04b6f02b6b04b6702b6304b5f02b5b02b5904b5702b5302b5104b4f06b4d02b4b02b4904b4706b4502b4302b4101a6f01a6b01a6901a6701a6301a6101a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a3306946ba1440192e02d6f02d6e02d6d04c6f06c6b07c6704c6304c5f0cc5d06c5b06c5909c5709c5504c5306c5102b6b02b6a02b6902b6707b6602b6302b6102b5707b5602b5502b4f0fb4e02b4b02b4702b4302b4201a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330192e04c5f02c5b02c5702c5302b5f02b5b02b5302b4f02b4b02b4702b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330192e04c5f02c5b02c5702c5302b5f07b5e02b5b02b5302b5202b4f02b4b02b4702b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a33069460192e04c5f06c5b07c5704c5302b5f02b5b02b5302b4f02b4b02b4702b4301a5f02a5b01a5701a5306a4f0ca4b0ca4706a4301a3f02a3b01a3701a3302d6f02d6e02d6d07c6f07c6e0cc6db746c04c6b06c6904c6707c6506c6307c6206c61b646004c5f06c5b07c5704c5302b6f07b6e02b6d02b5f07b5e02b5b02b5902b5302b5202b5102b4f02b4b02b4702b4301a6f01a6e01a6d01a6c01a6b01a6901a6701a6501a6307a6201a61b526001a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330192e04d6e04d6d06c6904c6102c5d02c5906c5502c5102b6d02b6502b5d02b5902b5502b5102b4902b4101a5d01a5901a5501a510192e04d6f06d6b06d6704d6304c6fb346e04c6b06c6a04c6707c6604c6306c6202c5f02c5e02c5d02b6f0fb6e02b6b02b6702b6302b6202b5b02b5a02b5902b5706b5602b5302b5102b4706b4602b4501a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3901a3701a3301a310192e04d6f0cd6e04d6b06d6a04d6707d6604d6306d6204c6f06c6b06c6704c6302c5f02c5e02c5d02b6f02b6b02b6702b6302b5f06b5e02b5d02b4f06b4e02b4b02b4902b4302b4202b4101a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330192ebf45fbe45bbb457b9453b835f02b5bb435702b53b234f02b4bb134702b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330192e04c6f04c6b04c6704c6304c5f04c5d04c5b06c5904c5708c5504c5304c5104b6f02b6b04b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4b04b4702b4301a6f04a6b05a6901a6704a6304a6101a5f01a5d04a5b03a5901a5701a5503a5303a5101a4f05a4b01a4705a4301a3f04a3b01a3702a3308d6f04d6e08d6b07d6a08d6707d6608d6304d6208c6f06c6b0ac6a08c6708c6606c6308b6f02b6b08b6702b6308b5f04b5d02b5b02b5908b5704b5502b5302b5106b4f02b4b02b4906b4702b4302b4101a6f05a6b01a6705a6301a5f01a5d03a5b03a5901a5701a5505a5303a5101a4f05a4b05a4901a4705a4305a4101a3f05a3b01a3702a3304d6f04d6b04d6704d6304c6f04c6e04c6b04c6a04c6704c6604c6304c6204c5f04c5e04c5b08c5a04c5704c5604c5306c5202b6f02b6b02b6a02b6704b6602b6302b5f04b5e02b5b02b5702b5302b5201a6f04a6b01a6704a6301a5f05a5b01a5705a5301a4f01a4d03a4b03a4901a4701a4502a4302a4101a3f02a3b04a3901a3702a3302a31ce56fcd56bca567c8563c746f02c6bc346702c63c145f02c5bc045702c5301b6f05b6b01b6705b6301b5f05b5b01b5705b5301b4f05b4b01b4702b4301a36b0234af16e079660695eae1560294ead1460393e04d7f06d7b06d7704d7304d6f06d6d06d6b06d6906d6706d6504d6306d6101c7f04c7e01c7b01c7a01c7707c7601c7301c7201c6f04c6e01c6d04c6c01c6b01c6a01c6901c6801c6707c6601c6507c6401c6301c6201c6101c6001c5f05c5e01c5d04b7f02b7b04b7702b7304b6f06b6d02b6b02b6904b6706b6502b6302b6104b5f02b5b04b5702b5301b4f01b4d01b4b02b4901b4704b4501b4301b4101a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5b05a5a01a5901a5701a5601a5301a5101a4701a4601a4501a3f01a3b01a3701a330497f079770496f0396d07967039650695f069570194f0194d01947039450293f049370192f019270587a05877078760586707866058650585f058570184f0184d01847058450283f048370182f0182704d7f06d7b06d7704d7304d6f06d6d06d6b06d6906d6706d6504d6306d6103c7f04c7e03c7b03c7a03c7707c7603c7303c7203c6f04c6e03c6d04c6c03c6b03c6a03c6903c6803c6707c6603c6507c6403c6303c6203c6103c6004b7f02b7b04b7702b7304b6f06b6d02b6b02b6904b6706b6502b6302b6104b5f02b5b04b5702b5303b4f03b4d02b4b02b4903b4704b4502b4302b4104a7f05a7b07a7704a7304a6f01a6d05a6b05a6907a6701a6504a6305a6106a5f05a5b06a5705a5303a4f01a4d03a4b05a4903a4701a4503a4303a4102a3f04a3b04a3702a330395603946078760786604d7f07d7b07d7704d7304d6f0cd6d07d6b06d6907d6707d6504d6306d6104c7f02c7b04c7702c7304c6f6546d02c6b02c6904c6707c6502c6302c6104c5f02c5b04c5702c5301b7f01b7e01b7b07b7a01b7701b7601b7304b7201b6f01b6e01b6d01b6c01b6b07b6a01b6907b6801b6701b6601b6501b6401b6304b6201b6104b6001b5f01b5e01b5b0ab5a01b5701b5601b5306b5201b4f01b4e01b4b04b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430193e0192e078760786604c6f07c6b07c6704c6304c5f8545d07c5b06c5907c5707c5504c5306c5104b6f02b6b04b6702b6304b5f7435d02b5b02b5904b5707b5502b5302b5104b4f02b4b04b4702b4304a6f05a6b07a6704a6304a5f01a5d05a5b05a5907a5701a5504a5305a51ab24f05a4b0aa4705a4302a3f04a3b04a3702a330496f079670495f0395d0795703955aa14f0a9470293f049370592fa91270786a07867078660785707856078550784f078470283f048370582f0582707d6f04d6e07d6b07d6a07d6707d6606d6304d6207c6f06c6b07c6a07c6707c6606c6307b6f02b6b07b6702b6308b5f04b5d02b5b02b5908b5704b5502b5302b5106b4f02b4b02b4906b4702b4302b4105a6f05a6b05a6705a6305a5f01a5d05a5b05a5905a5701a5505a5305a5105a4f05a4b05a4705a4302a3f05a3b05a3702a3307d6f07d6b07d6707d6307c6f02c6b07c6702c6309c5f02c5b09c5702c5305b6f05b6b05b6705b6305b5f05b5b05b5705b5302b4f05b4b05b4702b430796e09946078660685ea70560284e098460583e0183606d6f04d6e07d6707d6304d6207c6f06c6b07c6a07c6707c6606c6307c5707c5607c5507b6f02b6b07b6702b6308b5f04b5d02b5b02b5908b5704b5502b5302b5106b4f02b4b02b4906b4702b4302b4107a6f05a6b07a6705a6308a5f01a5d05a5b05a5908a5701a5505a5305a5106a4f05a4b08a4705a4302a3f05a3b08a3702a330796f079670895f0395d08957039550694f089470293f089370592f0c9270786f078670785f0485d07857078550684f0784d07847078450283f078370582f0582701d6f01d6e01d6701d6301d6205c6f06c6b06c6706c6305c5f05c5d05c5b05c5906c5706c5505c5305c5106b6f02b6b06b6702b6306b5f04b5d02b5b02b5906b5704b5502b5302b5106b4f02b4b06b4702b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330796f079670c95f0395d0c957039550694f069470293f069370192f019270586f018670585f0485d01857018550584f058470283f058370182f0182706d7f06d7d06d7b06d7906d7706d7506d7306d7106d6f06d6b06d6706d6301c7f07c7e01c7da447c01c7b01c7a01c7901c7801c7707c7601c7507c7401c7301c7201c7101c7001c6f04c6e01c6b01c6a01c6707c6601c6301c6201c5f05c5e01c5d06b7f06b7d02b7b02b7906b7706b7502b7302b7106b6f02b6b06b6702b6306b5f02b5b06b5702b5301b4f01b4d01b4b02b4901b4704b4501b4301b4101a7f01a7e01a7d01a7c01a7b01a7901a7701a7501a7305a7201a7105a7001a6f01a6b01a6701a6301a5b05a5a01a5901a5701a5601a5301a5101a4701a4601a4501a3f01a3b01a3701a330797f0397d07977039750796f079670695f069570194f0194d01947039450293f069370192f019270587f0787e0587d0586f0786e058620585f058570184f0184d01847058450283f0583a05837068360182f018270395407d6f06d6b07d6705d6301c6f01c6e01c6701c6301c6206c5f06c5e05c5b05c5a05c5705c5605c5305c5207b6f02b6b07b6702b6306b5f02b5b06b5702b5309b4f04b4d02b4b02b4909b4704b4502b4302b4101a6f01a6b01a6701a6301a5f01a5e01a5b01a5701a5305a5201a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330796f079670695f08957a214f0394d1d947039450293f099370192f019270586f0786e01867058620585f058570584f0484d01847018450283f0583a05837098360182f0182701d7f01d7e01d7d01d7c01d7b07d7a01d7907d7801d7701d7601d7501d7401d7307d7201d71a157001d6f01d6e01d6b07d6a01d6701d6601d6304d6207c7f08c7d06c7b06c7907c7707c7506c7306c7107c6f06c6b07c6706c6301c5f01c5e05c5d07b7f09b7d02b7b02b7907b7707b7502b7302b7107b6f02b6b07b6702b6301b5f04b5d01b5b01b5901b5701b5501b5302b5106b4f02b4b06b4702b4301a7f01a7d01a7b01a7901a7701a7501a7301a7101a6f01a6b01a6701a6301a5f01a5e01a5d01a4f01a4e01a4b01a4901a4305a4201a4101a3f01a3b01a3701a330797f0397d07977039750796f079670195f0395d01957019550694f089470293f099370192f019270587f0787e0587d0586f0786e058620185f0585d01857018550584f058470283f0583a05837098360182f0182703d6f03d6e06c6b06c6706c6306c5706c5506b6f02b6b06b6702b6306b5f04b5d02b5b02b5906b5704b5502b5302b5106b4f02b4b06b4702b4307a6f05a6b07a6705a630ca5f01a5d05a5b05a590ca5701a5505a5305a5106a4f05a4b06a4705a4302a3f05a3b06a3702a33 18 262143 7 127 11 2047 20 1048575
def cc_54_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x7d97c7904973f516ef5066f806383760a2e5e327561824e77a4994e44d4c3ff4e3cc33383493542f314402d4402b4202892b23f4a20e311ce4018e4016e2014a2411f2b0d54a0b421072420343e00034 0x2e7f02e7e02e7d04d7f06d7b07d7704d7304d6f0cd6d06d6b06d6909d6709d6504d6306d6102c7b02c7a02c7902c7707c7602c7302c7102c6707c6602c6502c5fd845e02c5b02c5702c5302c5201b7f01b7e01b7b07b7a01b7701b7601b7304b7201b6f01b6e01b6d01b6c01b6b09b6a01b6909b6801b6701b6601b6501b6401b6304b6201b6104b6001b5f01b5e01b5b08b5a01b5701b5601b5306b5201b4f01b4e01b4b02b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430397f039770396f0396d03967039650395f039570294f029470193f0193e0393d0192f0192e01922b81200487f078770486f6506d09867098650685f0a8570284f028470183f0e83d01837018350182f0182704d6f02d6b02d6702d6302c6f02c6b01c6702c6302c5f02c5b02c5702c5301b6f01b6e01b6b07b6a01b6701b6601b6304b6201b5f01b5e01b5b0cb5a01b5701b5601b5308b5201b4f01b4e01b4b02b4a01b4701b4601b4302b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a430396f039670395f039570294f029470193f0193e0393d0192f0192e01922b71200486f078670785f078570284f028470183f0783d01837018350182f0182704d6f02d6b02d6702d6302c6f07c6e02c6b01c6702c6302c6202c5f02c5b02c5702c5301b6f01b6e01b6b07b6a01b6701b6601b6304b6201b5f01b5e01b5b06b5a01b5701b5601b5306b5201b4f01b4e01b4b02b4a01b4701b4601b4302b4201a6f01a6b01a6701a6301a5f01a5b06a5a01a5701a5601a5301a4f01a4b01a4701a430396f039670395f0695a03957039560294f029470193f0193e0393d0192f0192e01922b61200486f078670685f068570284f0284d02847078450183f0783d01837018350182f0182704d6f06d6b07d6704d6302c6f02c6b01c6702c6302c5f02c5b02c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6e02a6b02a6a01a6701a6601a6301a6206a5f06a5e0ca5b08a5a0ca5708a5606a5306a5201a4f01a4e02a4b02a4a01a4701a4601a4301a4201a3f01a3e01a3701a3301a320396f039670395f039570294f029470193f0193e0193701932b51300392f0392d03927039250486f078670685f078570284f028470183f018370782f0782d078270782502e7f02e7e02e7d07d7f07d7e0cd7ddd57c04d7b06d7904d7707d7506d7307d7206d71dc57004d6f06d6b07d6704d6302c7f07c7e02c7d02c6f07c6e02c6b02c6902c6302c6202c6102c5f02c5b02c5702c5301b7f01b7e01b7d01b7c01b7b04b7a01b7904b7801b7701b7601b7501b7401b7307b7201b71db37001b6f01b6e01b6b07b6a01b6701b6601b6304b6201b5f01b5e01b5b08b5a01b5701b5601b5306b5201b4f01b4e01b4b02b4a01b4701b4601b4302b4201a7f01a7d01a7b01a7901a7701a7501a7301a7101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a430397f0397d03977039750396f039670395f039570294f029470193f0193e0393d0192f0192e01922b41200787f0787d04877078750486f078670685f078570284f0284d02847078450183f0783d01837018350182f0182704e7e04e7d06d7904d7102d6d02d6906d6502d6102c7d02c7502c6d02c6902c6502c6102c5902c5101b7e04b7a01b7604b7201b6e01b6d01b6c04b6a01b690cb6801b6601b6501b6404b6201b6104b6001b5e06b5a01b5606b5201b4e02b4a01b4602b4201a6d01a6901a6501a610396d039650193e0393d0192e01922b31200486d0b8650e83d0183502e7e02e7d04d6d04d6a04d6606d6504c7d04c7a04c7604c7504c6d04c6a04c6604c6507c6402c5e02c5d01b7e04b7a01b7604b7201b6e04b6a01b6909b6801b6604b6201b6104b6001b5e06b5a01b5606b5201b4e04b4a01b4604b420193e0393d0192e019220f9200486d098650e83d0183504d7e07d7a07d7604d7202d6e02c5501b7e07b7a01b7604b7201b6e06b6a01b6606b6201b5e01b5d01b5c08b5a01b5908b5801b5601b5501b5408b5201b510cb5001b4e02b4a01b4602b4201a5d01a5901a5501a510193e0192e0686e0485e0284604e7f06e7b06e7704e7304d7fd957e04d7b06d7a04d7707d7604d7306d7202d6f02d6e02d6d02c7fd847e02c7b02c7702c7302c7202c6b02c6a02c6902c6706c6602c6302c6102c5706c5602c5501b7f01b7e01b7b07b7a01b7701b7601b7304b7201b6f01b6e01b6b06b6a01b6701b6601b6306b6201b5f01b5e01b5d01b5c01b5b06b5a01b5908b5801b5701b5601b5501b5401b5304b5201b5104b5001b4f01b4e01b4b02b4a01b4904b4801b4701b4601b4302b4201b4102b4001a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a430397f039770396f039670395f0395d03957039550294f029470193f0193e0393d0192f0192e01922b21200487f098770686f068670485f0685d06857d70550284f0284d02847620450183f0e83d01837018350182f0182704e7f0ce7e04e7b06e7a04e7707e7604e7306e7204d7f06d7b06d7704d7302d6f02d6e02d6d02c7f02c7b02c7702c7302c6f06c6e02c6d02c5f06c5e02c5b02c5902c5302c5202c5101b7f01b7e01b7b07b7a01b7701b7601b7304b7201b6f01b6e01b6d01b6c01b6b04b6a01b6904b6801b6701b6601b6501b6401b6306b6201b6106b6001b5f01b5e01b5b06b5a01b5701b5601b5306b5201b4f01b4e01b4b02b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430397f039770396f0396d03967039650395f039570294f029470193f0193e0393d0192f0192e01922b11200487f098770686f0686d048670c8650685f068570284f028470183f0c83d01837018350182f0182704d6f04d6b0ad6904d6704d6304d6104c6f02c6b04c6702c6304c5f02c5b04c5702c5301b6f01b6d01b6b01b6701b6501b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6e01a6d04a5f06a5e04a5b04a5a04a5708a5604a5304a5202a4f02a4e04a4b04a4a04a4704a4602a4302a4201a3f01a3e01a3701a3301a320396f0396d03967039650395f039570294f039470193f019370392f0392d03927039250486f048670a85f0a8570284f048470183f018370482f0482d048270b82508d6f06d6b08d6706d6308c6f02c6b08c6702c6306c5f02c5b06c5702c5301b6f01b6b01b6701b6301b5f01b5d01b5b01b5701b5501b5301b4f01b4b01b4701b4308a6f04a6e08a6b07a6a08a6707a6608a6304a6201a5701a5601a5502a4f02a4e08a4b04a4a08a4704a4602a4302a4201a3f01a3e01a3701a3301a320396f039670395f0395d03957039550294f039470193f019370392f0392d03927039250a86f0a8670685f088570284f088470183f018370882f0882d088270b82504d6f04d6b04d6704d6302c6f02c6b02c6702c6302c5f04c5e02c5b02c5702c5302c5201b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4701b4501b4304a6f04a6e04a6b04a6a04a6704a6604a6304a6204a5f06a5e04a5b04a5a04a5708a5604a5304a5201a4701a4601a4501a3f01a3e01a3701a3301a320396f039670395f039570294f0294d02947039450193f019370392f0392d02927029250486f048670685f0c8570284f028470183f018370482f0482d048270b8250cd6f07d6b07d6711d630ec6f02c6b07c6702c630ec5f02c5b0cc5702c530bb6f04b6e07b6b07b6a07b6707b660bb6304b620bb5f06b5e0bb5b08b5a0bb5708b560bb5306b5202b4f02b4e0bb4b04b4a0bb4704b4602b4302b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a430b85e0183601826e656fe556be2567df563de46f02c6bda46702c63d645f02c5bd545702c5301b6f01b6e01b6b07b6a01b6701b6601b63d436201b5f01b5e01b5bd335a01b5701b5601b5306b5201b4f01b4e01b4bd234a01b4701b4601b4302b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a430396f039670395f039570294f039470193f0193e0393d0192f0192e01922b0120a906f990678b05f790570284f600470183fd103d01837018350182f0182704d6f04d6e06c6b07c6a07c6707c6604c6307c5707c5504b6f02b6b04b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4b02b4904b4702b4302b4101a6f05a6b01a6704a6301a5f01a5d03a5b03a5901a5701a5505a5303a5101a4f05a4b01a4705a4301a3f04a3b01a3702a3304e7f06e7e06e7d06d7b07d7a06d7907d7707d7604d7306d7107d6707d6607d6504c7f02c7b04c7702c7304c6f0cc6d02c6b02c6904c670fc6502c6302c6104c5f02c5b02c5904c5702c5302c5101b7f05b7b01b7704b7301b6f01b6d05b6b05b6901b6701b6504b6305b6101b5f05b5b01b5705b5301b4f04b4b01b4702b4301a36bf2340497e079760496e0496c0c966cf1640695e089560294e049460393e06e7f07e7e06e7d06e7706e7506e7306e7206d7707d7606d7506d6f06d6e06d6d06c7f02c7b06c7702c7306c6f02c6b06c6702c6306c5f06c5d02c5b02c5906c5706c5502c5302c5101b7f05b7b01b7705b7301b6f05b6b01b6705b6301b5f01b5d05b5b05b5901b5701b5505b5305b5101b4f05b4b01b4702b4301a36be2340497e079760696e0696c069660a9640695e0695c069560a9540294e049460393e04d6f02d6b04d6704d6304c6f02c6b08c6704c6304c5f06c5b04c5301b6f05b6b01b6704b6301b5f05b5b01b5704b5301b4f05b4b01b4705b4301a36bd2340496e089660495e079560694e089460393e06d6f06d6d08c6f04c6d07c5f06c5b06c5309b6f04b6d02b6b02b6909b6704b6502b6302b6107b5f02b5b07b5702b5306b4f02b4b06b4702b4301a6f01a6d05a6b03a6901a6701a6503a6303a6101a5f05a5b01a5705a5301a4f05a4b01a4705a4301a3f05a3b01a3702a3306e7f06e7e06e7d07d7f07d7e0cd7d07d6f07d6e06d6b06d6906d6307d6206d6107c7f07c7e09c7dcc47c02c7b02c7907c7707c7502c7307c7202c7102c7007c6f02c6b07c6702c6306c5f02c5b06c5702c5301b7f07b7e01b7d01b7c05b7b05b7901b7701b7505b7305b7205b7105b7001b6f05b6b01b6705b6301b5f05b5b01b5705b5301b4f05b4b01b4702b4307a7e03a7c01a36bb2340797ecb17c07976079740496e079660695e0695c08956089540294e049460393e04d6f06d6b06d6a06d6707d6604c6f04c6e06c5f06c5e04b6f02b6b04b6702b6304b5f02b5b02b5904b5702b5302b5104b4f04b4d02b4b02b4904b4704b4502b4302b4101a6f05a6b01a6704a6301a5f05a5b01a5705a5301a4f01a4d03a4b03a4901a4701a4505a4303a4101a3f04a3b01a3702a3301926ba12404e7f06e7d06e7b06e7a06e7707e7606e7504d7f0cd7e06d7d06d6f06d6e06d6d04c7f02c7b04c7702c7304c6f02c6b02c6904c6702c6302c6104c5f06c5d02c5b02c5904c5706c5502c5302c5101b7f05b7b01b7704b7301b6f05b6b01b6705b6301b5f01b5d05b5b05b5901b5701b5504b5305b5101b4f04b4b01b4702b4301a36b92340497e079760696e069660495e0495c06956c91540294e049460393e02e7f02e7e02e7d04d7f06d7b07d7704d7304d6f0cd6d06d6b06d6909d6709d6504d6306d6102c7b02c7a02c7902c7707c7602c7302c7102c6707c6602c6502c5f0fc5e02c5b02c5702c5302c5201b7f05b7b01b7704b7301b6f01b6d05b6b05b6901b6701b6504b6305b6101b5f05b5b01b5705b5301b4f02b4b01b4702b4301a36b82340497e079760496e0496c09966099640695e089560294e029460393e04d6f02d6b02d6702d6302c6f02c6b02c6302c5f02c5b02c5702c5301b6f05b6b01b6704b6301b5f05b5b01b5705b5301b4f02b4b01b4702b4301a36b72340496e079660895e0c9560294e029460393e04d6f02d6b02d6702d6302c6f07c6e02c6b02c6302c6202c5f02c5b02c5702c5301b6f05b6b01b6704b6301b5f05b5b01b5705b5301b4f02b4b01b4702b4301a36b62340496e079660695e069560294e0294c02946049440393e02d6f02d6d0fc6f08c6d06c6b06c690fc6708c6506c6306c6104c5f06c5b07c5704c5302b6f02b6d02b5f02b5b02b5302b4f02b4b02b4702b4301a6f01a6d05a6b03a6901a6701a6503a6303a6101a5f05a5b01a5704a5301a4f05a4b01a4705a4301a3f02a3b01a3702a3302e7f02e7e02e7d07d7f07d7e0cd7dc657c04d7b06d7904d7707d7506d7307d7206d71c557004d6f06d6b07d6704d6302c7f07c7e02c7d02c6f07c6e02c6b02c6902c6302c6202c6102c5f02c5b02c5702c5301b7f07b7e01b7d01b7c04b7b05b7901b7701b7505b7305b7205b7105b7001b6f05b6b01b6704b6301b5f05b5b01b5705b5301b4f02b4b01b4702b4307a7e03a7c01a36b42340797ec417c04976049740496e079660695e089560294e0294c02946049440393e04e7e04e7d06d7904d7102d6d02d6906d6502d6102c7d02c7502c6d02c6902c6502c6102c5902c5101b6d05b6901b6504b6101a36b32340497e049760496e0496c04966189640695e069560294e029460393e04e7f06e7b06e7704e7304d7fc257e04d7b06d7a04d7707d7604d7306d7202d6f02d6e02d6d02c7f0fc7e02c7b02c7702c7302c7202c6b02c6a02c6902c6706c6602c6302c6102c5706c5602c5501b7f05b7b01b7704b7301b6f05b6b01b6705b6301b5f01b5d05b5b05b5901b5701b5504b5305b5101b4f02b4b01b4702b4301a36b22340497e079760696e069660495e0495c06956089540294e0294c02946049440393e04e7f0ce7e04e7b06e7a04e7707e7604e7306e7204d7f06d7b06d7704d7302d6f02d6e02d6d02c7f02c7b02c7702c7302c6f06c6e02c6d02c5f06c5e02c5b02c5902c5302c5202c5101b7f05b7b01b7704b7301b6f01b6d04b6b05b6901b6701b6505b6305b6101b5f05b5b01b5705b5301b4f02b4b01b4702b4301a36b12340497e079760696e0696c04966049640695e069560294e029460393e04d6f06d6e06d6d06c6b07c6a06c6907c6707c6604c6306c6107c5707c5607c5504b6f02b6b04b6702b6304b5f0cb5d02b5b02b5904b570fb5502b5302b5104b4f02b4b02b4904b4702b4302b4101a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330192e 20 1048575 8 255 11 2047 20 1048575
def cc_54_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xf4e57da0ff959ef0c1fdc059a6d173815e2f41be07f7447ed7915832ca7c8b47882818dcc43f90e7b154ca11993f1327a240e4501a127b123052cf8861f8e7a497d521fefc2c934439580087 0x4d6f04d6e06c6b07c6704c6307c5707c5504b6f02b6b04b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4b04b4702b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a3304e7f06e7e06e7d06d7b07d7a06d7907d7707d7604d7306d7107d6707d6607d6504c7f02c7b04c7702c7304c6f0cc6d02c6b02c6904c67ff46502c6302c6104c5f02c5b02c5904c5702c5302c5101b7f01b7b01b7701b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4b01b4701b4301a3e0497e079760496e0496c0c966fe1640695e089560294e049460193606e7f07e7e06e7d06e7706e7506e7306e7206d7707d7606d7506d6f06d6e06d6d06c7f02c7b06c7702c7306c6f02c6b06c6702c6306c5f06c5d02c5b02c5906c5706c5502c5302c5101b7f01b7b01b7701b7301b6f01b6b01b6701b6301b5f01b5d01b5b01b5901b5701b5501b5301b5101b4f01b4b01b4701b4301a3e0497e079760696e069660695e0695c069560a9540294e049460193604d6f02d6b04d6704d6304c6f02c6b08c6704c6304c5f06c5b04c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a3e0496e089660495e079560694e089460193606d6f06d6d08c6f04c6d07c5f06c5b06c5309b6f04b6d02b6b02b6909b6704b6502b6302b6107b5f02b5b07b5702b5306b4f02b4b06b4702b4301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330192e06e7f06e7e06e7d07d7f07d7e0cd7d07d6f07d6e06d6b06d6906d6307d6206d6107c7f07c7e09c7dfb47c02c7b02c7907c7707c7502c7307c7202c7102c7007c6f02c6b07c6702c6306c5f02c5b06c5702c5301b7f01b7e01b7d01b7c01b7b01b7901b7701b7501b7307b7201b7105b7001b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a3e0797efa17c07976079740496e079660695e089560294e049460193604d6f06d6b06d6704c6f04c6e06c5f06c5e04b6f02b6b04b6702b6304b5f02b5b04b5702b5304b4f04b4d02b4b02b4904b4704b4502b4302b4101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a3304e7f06e7d06e7b06e7a06e7707e7606e7504d7f0cd7e06d7d06d6f06d6e06d6d04c7f02c7b04c7702c7304c6f02c6b02c6904c6702c6302c6104c5f06c5d02c5b02c5904c5706c5502c5302c5101b7f01b7b01b7701b7301b6f01b6b01b6701b6301b5f01b5d01b5b01b5901b5701b5501b5301b5101b4f01b4b01b4701b4306a5603a5401a3e0497e079760696e069660495e0495c06956f81540294e049460193602e7f02e7e02e7d04d7f06d7b07d7704d7304d6f0cd6d06d6b06d6909d6709d6504d6306d6102c7b02c7a02c7902c7707c7602c7302c7102c6707c6602c6502c5ff045e02c5b02c5702c5302c5201b7f01b7b01b7701b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4b01b4701b4301a3e0497e079760496e0496c09966099640695e089560294e029460193604d6f02d6b02d6702d6302c6f02c6b02c6302c5f02c5b02c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a3e0496e079660895e0c9560294e029460193604d6f02d6b02d6702d6302c6f07c6e02c6b02c6302c6202c5f02c5b02c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4306a5601a3e0496e079660695e069560294e029460193602d6f02d6d1ac6f08c6d06c6b06c6919c6708c6506c6306c6104c5f06c5b07c5704c5302b6f02b6d02b5f02b5b02b5302b4f02b4b02b4702b4301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330192e02e7f02e7e02e7d07d7f07d7e0cd7df557c04d7b06d7904d7707d7506d7307d7206d71f457004d6f06d6b07d6704d6302c7f07c7e02c7d02c6f07c6e02c6b02c6902c6302c6202c6102c5f02c5b02c5702c5301b7f01b7e01b7d01b7c01b7b01b7901b7701b7501b7307b7201b7105b7001b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a3e0797ef317c04976049740496e079660695e089560294e029460193604e7e04e7d06d7904d7102d6d02d6906d6502d6102c7d02c7502c6d02c6902c6502c6102c5902c5101b6d01b6901b6501b6101a3e0497e049760496e0496c04966189640695e069560294e029460193602e7e02e7d04d6d04d6a04d6606d6504c7d04c7a04c7604c7504c6d04c6a04c6604c6507c6402c5e02c5d01a3e0497e049760496e049660695e069560494e049460193604e7f06e7b06e7704e7304d7ff157e04d7b06d7a04d7707d7604d7306d7202d6f02d6e02d6d02c7ff047e02c7b02c7702c7302c7202c6b02c6a02c6902c6706c6602c6302c6102c5706c5602c5501b7f01b7b01b7701b7301b6f01b6b01b6701b6301b5f01b5d01b5b01b5901b5701b5501b5301b5101b4f01b4b01b4701b4301a3e0497e079760696e069660495e0495c06956089540294e029460193604e7f0ce7e04e7b06e7a04e7707e7604e7306e7204d7f06d7b06d7704d7302d6f02d6e02d6d02c7f02c7b02c7702c7302c6f06c6e02c6d02c5f06c5e02c5b02c5902c5302c5202c5101b7f01b7b01b7701b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4b01b4701b4301a3e0497e079760696e0696c04966049640695e069560294e029460193604c6f04c6b04c6704c6304c5f04c5d04c5b06c5904c5708c5504c5304c5104b6f02b6b04b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4b04b4702b4301a6f01a6d01a6b01a6701a6501a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a3308d6f04d6e08d6b07d6a08d6707d6608d6304d6208c6f06c6b08c6706c6308b6f02b6b08b6702b6308b5f04b5d02b5b02b5908b5704b5502b5302b5106b4f02b4b06b4702b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4d01a4b01a4701a4501a4301a3f01a3b01a3701a3304d6f04d6b04d6704d6304c6f04c6e04c6b04c6a04c6704c6604c6304c6204c5f04c5e04c5b08c5a04c5704c5604c5306c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a33fd56ffc56bf9567f7563f646f02c6bf246702c63ef45f02c5bee45702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a3eed16e079660695eec1560294eeb1460193604e7e02e7a02e7602e7202d6e02d6d02d6c02d6904d6502d6202d6104c7e02c7204c6e02c6d02c5a02c5904c5602c5101b7e04b7a01b7604b7201b6e01b6d01b6c04b6a01b6904b6801b6601b6501b6404b6201b6108b6001b5e06b5a01b5606b5201b4e02b4a01b4904b4801b4602b4201b4102b4001a6d01a6901a6501a610396d039650193e0393d0192e019220f9200886d048650284d048450c83d0183501d6f06d6b06d6907d6704d6306d6104c6f02c6b04c6702c6304c5f02c5b04c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6e01a6b01a6a01a6701a6604a6304a6201a5f01a5e07a5b07a5a01a5701a5601a5301a5202a4f02a4e04a4b04a4a04a4704a4602a4302a4201a3f01a3e01a3701a3301a320396f039670395f039570294f039470193f019370392f0392d03927039250486f078670685f088570284f048470183f018370c82f0b82d0c8270b82504e7e07d6504c6d02c6904c6502c6101b7e07b7a01b7604b7201b6e01b6d01b6c0bb6a01b690bb6801b6601b6501b640bb6201b610cb6001b5e08b5a01b5606b5201b4e04b4a01b4602b4201a6e01a6d01a6c01a6901a6505a6201a6105a600396e0396c0193e0192e0487e0486e08856048460183e0b83c04e7f06e7e06e7d06d7b07d7a06d7907d7707d7604d7306d7107d6707d6607d6504c7f02c7b04c7702c7304c6f0cc6d02c6b02c6904c67e946502c6302c6104c5f02c5b02c5904c5702c5302c5101b7f01b7e01b7b07b7a01b7701b7601b7304b7201b6f01b6e01b6d01b6c01b6b0cb6a01b69e836801b6701b6601b6501b6401b6304b6201b6104b6001b5f01b5e01b5b08b5a01b5701b5601b5306b5201b4f01b4e01b4b04b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a430397f039770396f0396d03967039650395f039570294f039470193f0193e0393d0192f0192e01922bf1200487f078770486f0c86d0c867e70650685f088570284f048470183f0c83d01837018350182f0182706e7f07e7e06e7d06e7706e7506e7306e7206d7707d7606d7506d6f06d6e06d6d06c7f02c7b06c7702c7306c6f02c6b06c6702c6306c5f06c5d02c5b02c5906c5706c5502c5302c5101b7f01b7e01b7b07b7a01b7907b7801b7701b7601b7304b7201b710ab7001b6f01b6e01b6b06b6a01b6701b6601b6306b6201b5f01b5e01b5d01b5c01b5b06b5a01b590ab5801b5701b5601b5501b5401b5306b5201b5106b5001b4f01b4e01b4b04b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a430397f039770396f039670395f0395d03957039550294f039470193f0193e0393d0192f0192e01922be1200787f078770686f068670685f0685d06857078550284f068470183f0783d01837018350182f0182704d6f02d6b04d6704d6304c6f02c6b08c6704c6304c5f06c5b01c5704c5301b6f01b6e01b6b08b6a01b6701b6601b6304b6201b5f01b5e01b5b07b5a01b5701b5601b5304b5201b4f01b4e01b4b08b4a01b4701b4601b4306b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a430396f039670395f039570394f039470193f0193e0393d0192f0192e01922bd1200486f078670485f078570684f078470183f0783d01837018350182f0182707d6f06d6b06d6901d6706d6306d6107c6f02c6b07c6702c6306c5f02c5b06c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6e06a6b06a6a01a6701a6601a6301a6201a5f01a5e08a5b04a5a01a5701a5601a5301a5202a4f02a4e09a4b04a4a09a4704a4602a4302a4201a3f01a3e01a3701a3301a320396f039670395f039570294f039470193f0193e0193701932bc1300392f0392d03927039250786f078670685f078570284f078470183f018370782f0782d078270782506e7f06e7e06e7d07d7f07d7e0cd7d07d6f07d6e06d6b06d6906d6307d6206d6107c7f07c7e09c7de447c02c7b02c7907c7707c7502c7307c7202c7102c7007c6f02c6b07c6702c6306c5f02c5b06c5702c5301b7f01b7e01b7d01b7c01b7b07b7a01b7907b7801b7701b7601b7501b7401b7307b7201b71e337001b6f01b6e01b6b07b6a01b6701b6601b6304b6201b5f01b5e01b5b08b5a01b5701b5601b5306b5201b4f01b4e01b4b04b4a01b4701b4601b4302b4201a7f01a7d01a7b01a7901a7701a7501a7301a7101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a430397f0397d03977039750396f039670395f039570294f039470193f0193e0393d0192f0192e01922bb1200787f0787d07877078750786f078670685f078570284f078470183f0783d01837018350182f0182704d6f06d6b06d6701d6304c6f02c6b04c6702c6304c5f02c5b04c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6e01a6b01a6a01a6701a6604a6304a6201a5f01a5e01a5b01a5a01a5701a5606a5306a5202a4f02a4e04a4b04a4a04a4704a4602a4302a4201a3f01a3e01a3701a3301a320396f039670395f039570294f039470193f019370392f0392d03927039250486f078670685f068570284f048470183f018370c82f0b82d0c8270b82504d7e06d6e04c5d02c5904c5502c5101b7e07b7a01b7604b7201b6e06b6a01b6606b6201b5e01b5d01b5c0bb5a01b590bb5801b5601b5501b540bb5201b510cb5001b4e04b4a01b4602b4201a5d01a5901a5501a510193e0192e0487e0686e0485e0484601836018340182604e7f06e7d06e7b06e7a06e7707e7606e7504d7f0cd7e06d7d06d6f06d6e06d6d04c7f02c7b04c7702c7304c6f02c6b02c6904c6702c6302c6104c5f06c5d02c5b02c5904c5706c5502c5302c5101b7f01b7e01b7b07b7a01b7907b7801b7701b7601b7304b7201b7104b7001b6f01b6e01b6b06b6a01b6701b6601b6306b6201b5f01b5e01b5d01b5c01b5b06b5a01b59e135801b5701b5601b5501b5401b5304b5201b5104b5001b4f01b4e01b4b04b4a01b4701b4601b4302b4201a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b06a5a01a5905a5801a5701a5601a5501a5401a5301a5101a4f01a4b01a4701a430397f039770396f039670395f0395d0695a039570395603955039540294f039470193f0193e0393d0192f0192e01922b91200487f078770686f068670485f0685d06857e00550284f048470183f1183d01837018350182f01827 19 524287 8 255 11 2047 20 1048575
def cc_54_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xa7136a5120a054c9b74e96a4d8ed7d8a04d827797fa2d7c73377f487324d6b77b63e795f6485a94d529804da4f45b7f3e07b3984834a4e2fd4d27b82245361c87d14f791034c0b74c06b4c0234800023 0x135bc09adc08d6b03eb502359c0facc04d63026b10131bc098dc06c6b0363381318c098c402b6f015b580ad9c056c602b5f015ae80ad6c056b202b57015aa80ad4c056a202b4f015a680ad2c0568e02b45015a18129bc134d609a670253182297c034ba08a5b02d2c82295c034aa08a5302d2881a93c0d49a06a4b035238229140d48602a3f0151d80a8dc0546604d6f036b582759c09ac602c6f0163580b19c058c602c5f0162d80b15c058a604b6f04db5826d9c096c606b5f911adc80d5c0d6a602b4f015a580ad1c0568602a4e8f8b701e5980d2bd1e156014a30164f80326c04d6f026b581359c09ac602c6f0163680b1ac058ce02c650163180b17c058b602c570162980edbc076dc03b6d025af81ad78096b604b5a025ab822d58096a604b52015a780ad380568e02b43015a10129bc094d604a670253181a97c154b60aa570352980a93c0549602a47015218128fc0347a04a3b02d1c8128dc0346a04a330251880e5bc072da0396701cb280e57c072ae0294f014a380a4fc0527a029370149a80e4bc0724e0486f0243381a17c150ae0284f014238120fc0907a0483705c1a92c0bc6e04e04d6f026b701b5ac0dace04d63026b100b1bc058d602c670163180b17c058ba02c5b0162b80b154058a604b6f025b7022dac0f6d408b6703db3012d8c096c403b5701dab00ed540569e02b4e015a380ad0c0568404a6f04d3582699c094c606a5f0352d81a95c0d4a602a4f0152580a91c0548608a3f00d1e8228ec0b47208a3700d1a8228cc0b4620396f01cb380e57c072ba0395701caa80a53c0528e0293f0149e80a4dc0526a0392f01c938121bc130ce0685f0342b80a13c0508e0883f0441e8220dc1706a0c82f08c138135bc0dad606d67026b180b1bc058d602c670163180b17c058b602c5701629812dbc096dc09b6b03db5026d9c0f6cc04b63025b100ed7c076bc01b5b00dad00ed5c036ac03b5301da900ad3c0569c02b47015a180ad08034de05a6b00d3381298c034be02a5b00d2b81694c0349e02a4b00d2380a90c0347e01a3d01d1d80e8e40346e01a3502d198168c4072de0396701caf80e55c0529e029470149f80a4f40526e0293501c9780649c090de0586702c2f81615c0509e0284702c1f8160f40b06e0583502c1780609c09cfe06e7b0373b8139cc07afe03d7e01ebd81f5e807aee03d7601eb982b5c807ade03d6e01eb581b5a807ace03d6601eb181b588058fe02c7b0163b80b1cc058de02c6b0163380b18c036fe05b7b00dbb812dcc036de06b6e00db6806d9c036ca05b6302db1006d7c036ba03b5b01dac806d5c036aa03b5302da8806d3c0569601b47015a18129fc094fc05a7b02d3d0169dc0f4ec04a730253900699c034cc01a6501d2f80e9780b4bb1a25c01d2d80e968074b203a5801d2b80e958074aa03a5401d2980e9480b4a205a500152780a9380549a02a4c0152580a9280548e02a4602d228129100548602a4202d1f8168f80b47a0397f01cbb80e5bc072ce0295f014af00a5740529e0294e014a100e4fc0326e0392f01c9680e49c0724a0487f02c3b8161bc0b0ce0385f02c2e80e15c070aa0284f014238160fc0306e0582f02c1681609c0b04a04d6f036b581b59c09ac602c6f0163580b19c058c602c5f0162d80b15c058a604b6f025b7026dac0f6d409b6703db3012d8c096c403b5f01daf016d6c0b6b403b5701dab00ed4c076a401b4f00da7006d1c0368601b4200d378069ac034ce01a6300d2f80696c034ae01a5300d2780692c0348e01a4300d1f8068f40347601a3900d1b8068d40346601a3101cb780e59c072be03957014a780651c0527e0293d00c9b8064d40325e019270243782619c0d0be068570142780a11c2307e0b83d08c1b82e0d40305e0182700f3f8079f803cf607e7a00f3b8079d803ce604e72026bf81b5ec0daee04d7300eb78075b80bada03c7f01e3f00f1ec0f8f403c7701e3b00f1cc158e401c6f00e3700f1b4078d801c6b00e350071a4038d001c6700e33007194038c801c6300e3100f186308c003c5f01e2f00f16c0d8b403c5701e2b00f14c0d8a402b7f015bd80addc056e601b6f015b6806dac036d201b6700db2806d8c056c202b5f015ad80ad5c056a601a7f00d3d8069dc034e601a6f00d370069b4034be01a5e00d2d806964034a606a5200d2880693c0349a01a4b00d2480691c0348a01a4300d208068fc0347601a3700d1980e5fc072ee0196f01cb680659c032ca0395f01cab80a53c0529c0294d0149f80a4f8052640192f00c938121fc130ee0186f0743680619c030ca0685f0342b80e13e2c09a0384701c2280a0fc0506e0182f00c138079f80fcf401e76027390075b80bada04c7e03e3d01f1d8098e401c6e05e3684b1b0038d401c6900e34007198038ca01c6400e3102f184178c006c5e0362d01b1580d8a402b6d00db4806d94056c201a6e00d36806978034b205a5200d288069340349201a4500d208121f8030dc0b86c01c2300a0d809ade06d6b03eb381358c098de04c6e03e3581f1a80f8ce07c66026318131880d8be06c5e05e2d823168178ae08c560362981b148056de02b6b015b380ad8c056be02b5b015ab80ad4c094de05a6b03d3381298c0d4be05a5b8b12b81694c1749e01a4d02d258169241748e01a4502d218169040547e02a3b0151b80a8cc090dc038460141b0135bc0dad609d67026b180f1bc078dc03c6b03e3500f19c078cc03c638e23100f17c078bc03c5b8da2d00f15c078ac03c530362900adbc056d602b67015b180ad7c056b602b57015a98129bc134d609a670253181a97e324b7172570352980e93c0349a03a4b01d2480e91c0348a03a4302d2080a8fc0547602a370151980e5bc072ce0395f01cab80a53c0529c0294d0149f80a4f8052640392f01c938121bc130ce0685f3e82b80e13e2a09a0384701c2280a0fc0506e4902f1b0138135bc09adc03d6b01eb500f59c07acc03d6301eb100f1bc0d8d607c670263180f17c078ba03c5b01e2c81f15c0f8aa03c5301e28812dbc056d604b67015b1812d7c096ba02b5b015ac812d5c096aa02b53015a8812d3c0569604b47015a18069bc0b4d601a670253180697c034ba01a5700d2a81694c0349e05a4b00d2381690c0347e04a3b00d1b80a8cc072de0396701caf806574032ae0195501ca780e51c0527e0393701c9780649c090de0586702c2f8161740b0ae0585502c2781611c0507e0483702c1780609c09cfe06e7e0373e81b5ec0faf406d7903ebb81f5d809ae606d7103eb381f5980faca04c7f0163d8131dc058e604c6f0663680b1ac058d204c6707e3280b18c058c204c5f0162d80b164098ae02c5301628806dfc0b6f601b77025b9806dbc036da05b6b02db4806d9c036ca04b6302db0806d7c0b6b601b5702da9806d3c0969601b47015a180e9fc094fc03a7b01d3d00e9dc0f4ec03a7301d3900e9bc094dc03a6d0253600e9ac074d403a6901d3400e99c194cc03a658993200e98c074c403a6101d3000e97c0d4bc03a5b01d2d00e95c114ac03a5301d2900a93c0549c03a4b01d2500e91c0948c02a430152100e5fc072ee0396f01cb680e59c072ca0395f01cab80a53c0728e0193a00c9b8064d80324e0192600c928121fc0b0ee0486f02c3681619c0b0ca0585f02c2b80a13c0908e0583f00c1b80e0bc0705a0382702c1281b9fc0fcfc06e7d0373b81b9d40dce606e72036bb81f5d80daea06d6f036b701b5b40d8fe02c7b0363b80b1cc0d8de02c6b0363380b18c0d8be06c5d0162d80b1640d8ae06c550162980b144036fe05b7b00dbb816dcc036de05b6b00db3816d8c036be01b5d02dad816d64036ae01b5502da9816d440369e05b4b00da380ad0c074fe04a7e01d3d80e9e8074ee07a7601d3980e9c8074de06a6e01d3580e9a8074ce06a6601d3180e988074be06a5e01d2e81a970074b603a5a01d2c80e960074ae06a5601d2a82a950074a603a5201d2880e9400549e02a4e01d2580e9280748e04a460152180a908072fe0397701cb780e59c072be0395d01cab80e5540529e0394700c9d0064dc0326c0192700c930064940b0fe0587702c3781619c0b0be0585d02c2b8161540509e0584702c1f8060dc0705e0382d01c1381609409ade02d6b026b381358c098de02c6b0463381318c098be06c5b01e2b81314c036de05b6b00db3812d8c036be05b5b00dab812d4c0369e05b4b00da3816d0c074de04a6e01d3580e9a8074ce08a6601d3180e988074be04a5e01d2d80e968074ae07a5601d2980e9480749e06a4e01d2580e9280748e08a4601d2180e908072de0396701caf80e55c0729e0394700c9d0064dc0326c0192700c93006494090de058670242f81615c0b09e0584702c1f8060dc0705e0382d01c138160940dade06d6d01eb580f5a407ace03d6501eb180f584118de04c6d01e3580f1a4078ce03c6501e3180f1840f8be06c5b01e2b81b14c136de04b6d015b580ada4136ce04b65015b180ad840f6be02b5b03dab80ad4c0d69e02b4b035a380ad0c034de01a6d02d3580699c034ca01a5f02d2d80695c0b4a601a4f02d2580691c0b48601a3f02d1d8068dc054660196f00cb680e59c032ca0395f01cab80e53c0728e0293f01c9b80e4bc0324e0586f02c3681619c0b0ca0585f02c2b81613c0b08e0283f02c1b8160bc0304e06e7f0373f01b9f40fafe07d7e066be81f5bc0fadc06d6b036b481b58c0fac406d6103e3f81f1f8138fb1047c0163d80b1e40f8ee07c750163981f1c8058e202c7003e3780b1ac0f8ce02c630362f80b16c0d8ae02c5300dbf806df40b6f605b7900dbb806dd40b6e605b7100db7816dac036ce05b6300daf816d6c036ae05b5300da7816d2c0368e02b4301d3f81e9f8074fb0f27c01d3d80e9e8074f203a7801d3b81e9d8074ea07a7401d3980e9c8074e203a7001d378129b8074d603a6a01d3381e998074c603a6201d2f81a978074b603a5a01d2b822958074a603a520152780a9380749603a4a01d238129180548602a4201cbf80e5f8072fa0397c01cbb80e5d40f2e40396f01cb380e57c072ae0294f01ca38064e80326e0193600c938064980324a0587f02c3e8161dc0b0ea0586f02c3381617c0b0ae0284f02c238160fc0306e0382f01c1680e09c0b04a04d6f036b581b59c07ac604c6f0263700f1ac078d403c6701e3300f18c078c406c5f0362f00f16c078b403c5701e2b00f14c078a404b6f015b5812d9c056c604b5f015ad812d5c056a604b4f025a680ad2c0569204b47025a280ad0c0568201a6f02d3580699c094c601a5f02d2d80695c0b4a601a4f00d2680691c0348a05a4300d1f8128ec0346e02a3301cb780e59c072be0395701ca78065340328e019450149f80e4dc0725e0192a00c93806498090de0586702c2f81615c0b09e0584d02c238161140507e0483702c1780609c09cfe06e7d0373d81b9e80dcee07e760373a8135fc19afc06d7d036b781b5b80dada04c7f0163d8131dc058e604c6f0163580b1a4098ce02c630163081317c0d8ba02c5b0162c81315c0d8aa02c5301628806dfc0b6f601b77025b9806dbc0b6d601b6702db1806d7c036ba05b5b02dad016d640b6b001b57035ab006d54036a804b5302da8806d3c0969601b47015a180e9fc094fc03a7b01d3d00e9dc0f4ec03a7301d3900e9bc0d4dc03a6b01d3500e99c0d4cc03a6301d3100e97c094bc03a5d0252e00e96c074b403a5901d2c00e95c0d4ac03a558692a00e94c074a403a5101d2800a93c0549c03a4b01d2500e91c0948c02a430152100e5fc072ee0396f01cb380e57c072ba0395701caa80a53c0728e0193a00c9b8064d80324e0192600c928121fc0b0ee0586f02c3381217c0b0ba0585702c2a80a13c0908e0583f00c1b80e0bc0705a0382702c1280b9fc05cfc02e7d026bf81b5ec0faee04d73026b78335b40dad606d6904eb382759409ac606d610163d80b1e8058f202c7703e3b00b1cc058e202c6703e3300b194058be0fc5e0162d80b15c058a602c5200dbf816dec036ee04b7300db7806db40b6d605b6900db3806d94096c605b6100daf816d6c036ae05b5300da780ad2c0368e02b4301d3f8129f8074f603a7a01d3b81e9d8074e603a7201d378129b8074da04a6c01d3580e9a8074d203a6801d33826998074ca09a6401d3180e988074c203a6001d2f81a978074b603a5a01d2b822958074a603a520152780a9380549602a4a0152380a9180548602a4201cbf80e5dc072de0396d01cb380e594072be03957014a780a51c032740193700c9b00649c0324c019250243f8161dc090de0586d02c338161940b0be058570142780a11c0b07e0183701c1780e0b40704e05825026b780b5ac05ace02d630163780b1ac058ce02c630162f80b16c058ae02c5300db7816dac036ce04b6300daf816d6c036ae05b5300da780ad2c0368e02b4301d378129b8074d603a6a01d3381e998074c603a6201d2f822978074b603a5a01d2b832958074a603a520152780a9380549602a4a0152380a9180548602a4201cb780e59c072be03957014a780a51c032740193700c9b00649c0324c019250243781619c0b0be058570142780a11c0b07e0183701c1780e0b40704e05825026b780b5ac05ace02d630163781f1b8058d602c670163180b188058be02c5b0162b80b14c036de05b6b00db3812d8c036be05b5b02dad006d5c0d6ac05b5300da780ad2c0368e02b4301d378129b8074d603a6a01d3381e998074c603a6201d2f81a978074b603a5a01d2b81a958074a603a520152780a9380549602a4a0152380a9180548602a4201cb780e59c072be03957014a780a51c032740193700c9b00649c0324c019250243781619c0b0be058570142780a1340508e0584502c1f8060dc0705e0382d01c1381609405ade02d6d01eb580f5a405ace02d65016b180b5841f8de08c6d0363581b1a41f8ce08c650363181b184098be06c5b03e2b81314c056de02b6d015b580ada4056ce02b65015b180ad84056be02b5b015ab80ad4c0569e02b4b015a380ad0c034de01a6d02d3580699c034ca01a5f02d2d80695c094a601a4f02d2580691c0b48601a3f0151d8068dc054660196f00cb680e59c032ca0395f01cab80e53c0728e0293f0149b80a4bc0324e0586f02c3681619c0b0ca0485f02c2b81613c0b08e0283f0141b8160bc0304e02e7f0173f00b9f40fafe07d7e066bec295f009af606d79026bb81f5d40dae607d72036b8c255c009ade06d6b03eb381358c058fe07c7e0163e80b1bc0f8dc02c6b0163480b18c058c402c610162f80b16c058ae02c5300dbf806df4096f605b7900dbb806dd40b6e605b7100db7816dac036ce04b6300daf816d6c036ae05b5300da780ad2c0368e02b4301d3f81e9f8074fb0827c01d3d80e9e8074f203a7801d3b8129d8074ea04a7401d3980e9c8074e203a7001d378129b8074d603a6a01d3381e998074c603a6201d2f81a978074b603a5a01d2b822958074a603a520152780a9380549602a4a0152380a9180548602a4201cbf80e5f8072fa0397c01cbb80e5d40f2e40396f01cb380e57c072ae0294f014a38064e80326e0193600c938064980324a0587f02c3e8121dc0b0ea0486f02c3381617c0b0ae0284f0142680a11c0b08a0583f00c1b80e0bc0705a0382702c128139f809cfa06d79026b880b5b405ad206d65016b080b1f4058ea02c6d0163480b194058c202c5901628806db40b6d201b65025b08129f8074f404a7601d390129b8074da04a6c01d3500e9a4074d004a6601d32862990074c403a6101d3001a978074b406a5601d2900a9380549402a460152100e5b4072ca0193a00c9b0064980324a0486d02c3280e0b40b04a04e7f0373d81b9dc09ce604d7f832bf0135ec0daf404d7703ebb0135cc0dae402d6f016b700b5b4058fe0fc7e0163d80b1dc058e602c720163580b1a8058d202c670363300b18c058c202c570362b00b154036fe05b7b00dbb812dcc036de05b6b00db3816d8c036be01b5d02dad816d64036ae01b55025a9816d440369e02b4b00da380ad0c074fe04a7e01d3d80e9e8074ee07a7601d3980e9c8074de06a6e01d3580e9a8074ce06a6601d3180e988074be04a5e01d2e812970074b603a5a01d2c80e960074ae06a5601d2a822950074a603a5201d2880e9400549e02a4e0152580a9280548e02a460152180a908072fe0397701cb780e59c072be0395d01cab80e5540529e0294700c9d0064dc0326c0192700c93006494090fe0587702c3781619c090be0585d02c2b8161540509e0284d014238161140b07e0183701c1780e0b40704e058250273f8339f809cf606e7a0273b81f9d809ce606e72026bf81b5ec0daee04d73016b780b5b805ada02c7f0163d80b1dc058e602c6f0363700b1b4058be06c5e0162d80b164058a602c5201628806dfc0b6f601b77025b9806dbc036da04b6b02db4806d9c036ca05b6302db0806d7c0b6b601b5702da9806d3c0569601b47015a180e9fc094fc03a7b01d3d00e9dc0f4ec03a7301d3900e9bc0d4dc03a6d0353600e9ac074d403a6901d3400e99c094cc03a650253200e98c074c403a6101d3000e97c0d4bc03a5b01d2d00e95c0d4ac03a5301d2900a93c0549c02a4b0152500a91c0548c02a430152100e5fc072ee0396f01cb680e59c072ca0395f01cab80a53c0528e0193a00c9b8064d80324e0192600c928121fc0b0ee0586f02c3681219c0b0ca0585f02c2b80a13c0508e0583f00c1b80e0bc0705a0382702c1280f5bc07adc03d6d026378131ac098ce04c630262f813174098b606c590262b823154098a604c51025b780adac096ce02b63025af812d74056b602b59025ab812d54056a602b51025a780ad2c0968e02b4300d378129ac0b4d201a6702531812984034be01a5d0252d80695c034aa01a4f02d2580691c0b48601a3f0251d8068dc054660396f01cb680e59c072ca0195f00cae80e55c032aa0394f01ca380a4fc0726e0392f00c938121bc090ce0485f0242e81215c0b0aa0584f02c2380a0fc0906e0582f00c138235bc09adc08d6b03eb502359c0facc08d63026b10231bc0d8d608c670363180f17c078bc03c5d045b780adac116ce02b63045af812d74056b602b59045ab812d54056a602b51035a780ad2c0d68e02b4300d378169ac034ce05a6300d2f806974034ae01a5502d2980693c0b49605a4900d2381690c0b48201a3f02d1d8068dc054660396f01cb380e57c032ba0195700caa80e53c0729a0394701ca280a4fc0726e0392f00c938161bc0b0ce0585f02c2e81615c0b0aa0584f02c2380a0fc0b06e0582f00c138135bc09ad604d67026b18131bc098dc04c6b0263501319c098cc04c630263101317c098bc04c5b0462d01315c098ac04c530362900adbc056d602b67015b180ad7c056b602b57015a980ad3c0769c02b4d00d378129ac034ce04a6300d2f81696c034ae05a5300d278069340348e01a45015218068fc0547604a3900d1b80a8cc054620396f01cb380e57c072ae0294f00ca680651c0328a0293f0149e80a4dc0726a0292f00c938121bc090ce0585f02c2b81213c0b09a048470242280a0fc0506e0582f00c13c495be22ad70e567862b1c2d1bc058d70746701631c1517c058b70445701629806dbc0b6d601b6702db1806d7c0b6b601b5702da9806d3c0b69601b47015a180e9be064dc03a6b01d3500e99c0f4cc03a6301d3100e97c0d4bc03a5b01d2d00e95e044ac03a5301d2900a93c0549c03a4b01d2500e91e0248c02a430152100e5bc072ce0395f01cab80a53c0728e0193a00c9b8064d80324e0192600c928161bc0b0ce0585f02c2b80a13c0b08e0583f00c1b80e0bc0705a0382702c128139f805cf402e760173900b5b805ada02d6c016b481359405ac402d610263f00b1c8098dc02c6d0162d00b164098ac02c5100db6806da4036ca01b6100d1f0125f8092ec0496e044b6012598092c80695e034ab00a5380528c01936 20 1048575 8 255 11 2047 21 2097151
def cc_54_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x84804841077ee5376f7f71d526de3f68f4f6127d5bf53546794f94d478814294f3ff2a3867935135309482dc2d29f3d2742b2353f20a2b1c94119b2e15e3d12a3410a200dd2d0a03d0752b0324300032 0x36b00171702b4b001a54036b0016d602b6a801a5c015260129100724804d6f036b581b59c09ac603c6f01e3700b1ac058d402c670163300b18c058c404c5f0262f01b15c0d8a604c5203628813140056de07b6e015b580ad9c056c602b62015af80ad6c056ae02b53015a780ad340569602b49015a380ad140568602b410253781e9ac0f4ce04a630352f81a96c0d4ae06a539f1278069342b49605a490ad238069167a48605a410151f80a8ec0546e02a3301cb780e59c072be0295701ca780e5340728e039450149f80a4dc0725e039270243781e19c0d0be0685703c2781e1340f08e078450141f80a0f40506e0783503c1781e09c05cfe02e7e0173e80f5fc07afc03d7d01ebe00f5ec09af403d79026bc00f5dc07aec03d7501eba00f5cc0fae403d719e2b800f5bc07adc03d6b03eb500f59c07acc03d63026b101b1fc0f8fc06c7d0463e0131ec0d8f204c770363a81b1cc0d8e406c71036380131bc0d8d606c670263180adfc0f6fc02b7d015b781edb8056d602b69015b180ad88056c202b5f015ae80ad6c056b202b57015aa80ad4c056a202b4f015a580ad1c0568607a7f00d3e8129ec0b4f204a7700d3a81e9cc0b4e204a6f03d3581e99c094c603a5f00d2e80e96c074b203a5700d2a80e94c0b4a206a4f0352581a91c0d48602a3f0151d80a8dc054660397f01cbe80e5dc072ea0396f01cb380e57c072bc0395d01ca780e5380d2840293f0149b80e4bc0724e0787f03c3e8121dc0f0ea0486f03c3380e17c0f0ba0385701c2a81a13c0d08e0283f0141e80a0dc0f06a0782f03c138135bc09ad604d67026b18131bc098dc04c6b0263501319c098cc04c630263100b17c058bc02c570162980b148056de04b6e015b580ad9c056c602b62015af80ad6c056b402b57025ab00ad4c0568e03b46015a28129bc094d604a670253181a97c0d4b606a570352981293c0349a04a4b02d2481291c0348a04a430252080a8fc0547604a390151b80a8cc054620396f01cb380e57c052ae0394f01ca680a51c0528a0293f0149e80a4dc0726a0392f01c938121bc090ce0685f0342b81213c0909a048470442280a0fc0507a028370241a83a0bc1d04e04d6f026b381358c098de02c6b0263380b18c098be02c5b0262b80b14c036de05b6b00db3816d8c036be01b5d01dad806d5c036aa04b5300da7812d2c0368e02b4302d378169ac0b4d405a670453301698c094ae04a5602d2a80a93c0949604a47015218128fc0947c04a3d01cb780e59c072be03957014a780e51c0727e0193701c9780e4b40724e0392502c3781619c090be048570142781211c0b07e0183702c1781609c0fade06d6b03eb381b58c078de03c6e00e358071a8078ce01c6601e3180f1880b8be05c5e02e2b81714c0b8a407b6f015b581ed9c056c606b5f015ad81ad5c056a609b4f025a680ad2c0569209b47025a280ad0c0568201a6f03d3700e9ac034ce05a6302d3100697c0b4b601a5702d2980693c0349a03a4b01d2480691c0348a05a43025208068fc0b47601a370151980e5bc072ce0395f01cab80e53c0729a0394701ca280a4fc0726e0392f00c938161bc0b0ce0585f02c2b81613c0b09a0584702c2280a0fc0b06e0582f00c1380f9fc07cfc03e7b03f3d00f9e40fcf003e7701f3b00f9cc09ce403e719cb3801f5fc0daf607d77036b981f1fc058f607c770163980f1bc098da02c6b0163480f19c078ca02c630163081b17c058b606c5701629806dfc0f6fc01b7d00dbb806dd40b6e605b7200db7806db4076d603b6900db3806d94076c605b6100daf816d6c036ae05b5300da7816d2c0368e02b4300d3b8069d8034ea03a6f01d370169b6704d803a6b01d3500e9a4074d003a6701d3300e994074c803a6301d310169840b4c005a5f0352f01696c0b4b405a570452b01694c0b4a402a4f0152701692c0b49405a4704d2300a90c0548405a3f02d1f0168f4072fe0397701cb780e5b8072da0395f01caf01a5480529e0394701c9f8064dc0725e0392d01c9380e4940b0fe0587701c378161b4070ce0386502c2f81615c0509e0584702c1f8060dc0b05e0582d02c138160940fade06d6b03eb381b58c078de03c6e02e358171a8078ce03c6601e3180f188038be01c5e00e2b80714c038a407b6f015b581ed9c056c606b5f015ad81ad5c056a609b4f025a680ad2c0569209b47025a280ad0c0568201a6f00d370069ac034d201a6700d3181e988034c201a5f00d2d80695c034a601a4f00d2680692c0349201a4700d2280690c0348201a3f00d1d8068dc034660396f01cb380e57c072bc01957034a900e53c0729a0194700ca280a4fc0726e0192f00c9381e1bc0f0ce0685f03c2b81e13c0f09a0784703c2280a0fc0f06e0182f00c138079fc03cfc05e7d00ebf8075f807afa03d7c00ebd8075e803af201d7800ebb8075d803aea01d7400eb98075c807ae33657001eb780f5b807ad607d6a01eb380f59807ac604d6200e3f8231f4038f601c7900e3b8071d4038e606c7103e3781b1ac0f8ce06c6300dbf826df4036f601b7900dbb806dd4036e602b7103db780adac0f6ce02b6301daf812d74056b602b5901dab80ed54056a602b51035a780ad2c0d68e02b4300d3f8069f8034fa01a6f00d370069ac034d201a6303d31006984034be01a5d00d2d806964034ae01a5500d298069440349e01a4b00d2380690c0347e01a3b00d1b8068cc032fe0397d00cbb8065d4072de0396701caf80e578072ba0394f01ca701a5080527e0393700c9780649c030fe0787d00c3b8061d40f0de0786701c2f81e174070ae038550342781e11c0507e0783700c1780609c09ade06d6b036b381358c098de04c6e04e3581f1a8138ce07c6602631813188098be04c5e02e2b81714c098a402b6f015b580ad9c056c602b5f015ad80ad5c056a601b4f00da680ad2c0569202b4700da280ad0c0568201a6f02d3580699c094c601a5f02d2d80695c0b4a601a4f00d2680a92c0549201a4700d2280a90c0548201a3f0151d8068dc054660396f01cb380e57c052ae0394f01ca680e51c0728a0293f0149b80e4bc0324e0486f02c3381617c0b0ae0584f02c2681611c0b08a0283f0141b8160bc0304e03e7f01f3f00f9ec0fcf403e7701f3b00f9cc09ce404d7f036bd81b5dc09ae602c7f0163d80b1dc058e602c6f01e3700b1b4098d802c6b0163480b19c058ca02c630163100b184058c002c5f0162d80b15c058a601b7f02dbd806ddc096e601b6f00db680edac076d201b6700db280ed8c0b6c201b5f02dad806d5c0b6a601b4f015a7006d340368e01b45015a180ad08094fe0aa7e0253d8169e8094ee07a76025398169c8074de03a6e02d36cd09b0074d603a6a01d3480e9a0074ce03a6601d3280e990074c603a62025308129800b4be06a5e02d2e81a970094b605a5a02d2b81a9580b4aa08a54025298169480348e01a4600d2280a8fc0547c02a3d01cbf80e5dc072de0396e01cb680e57c072bc06952014a780a51c0727e0193701c9780e4b40724e039250243f8161dc070de0586d01c3380e1940b0be058570142780a11c0b07e01837024178160b40b04e05825026b781b5ac0dace04d630163780b1ac058ce02c630162f80b16c058ae02c53025b7812db8136d607b6a04db381ed98096c604b6200daf806d78036ae01b5300da900ad3c0569c02b4b015a500ad1c0568c02b43015a10069bc034d601a6700d3180697c034b601a5700d2980693c0349601a4900d2380690c0348201a3f00d1e8068ec0347201a3700d1a8068cc034620396f01cb380e57c032ae0294f014a380e4fc0727a0193700c9a8064bc0324e0486f04c3381a17c0d0ae0284f014238460fc1707a1183705c1a8060bc0304e03e7e03f3d00f9d809ce404c7e03e3d01f1d8098e403c6e05e3684f1b0078d403c6901e3400f198078ca03c6401e3102f184178c006c5e0362d01b1580d8a402b6d015b480ad94056c202b4d00d368069a4034ca01a6100d2680e5b8072bc0487e01c3702e1b00308c0283600c1300f9fc07cfc03e7b03f3d00f9dc07cec03e73027390135fc0daf606d77026b98071fc038fc01c7b03e3d0071dc038ec01c73056390071bc038dc01c6d00e360071ac078d401c6901e3400719c038cc01c6500e3200718c078c401c619923000717c038bc01c5b0362d00715c038ac01c530362900adfc056f602b77015b980adbc056da02b6b015b480ad9c056ca02b63015b080ad7c056b602b57015a9806d3c0369c02b4d00d3f8069ec034ee01a7300d378069b4034d601a6900d33806994034c601a6100d2f80696c034ae01a5300d278069380349a01a3f00d1f0068ec0347201a33015190068c4072fe0397701cb780e5b8072da0395f01caf01a5480329e0394d00ca38065140527e0293700c9780649c090fe0987701c3783a1b4070ce038650342f81a15c0309f3104d00c238061140507e0283700c1780609c15ade04d6e03eb581f5a80face07d66056b1813588118de06c6b03e3381b18c156de02b6b03db380ad8c176be04b5d015ad80ad64176ae04b55015a980ad440d69e02b4b035a380ad0c154de05a6b03d3381698c174be01a5d02d2d816964174ae01a5502d298169440d49e05a4b0452381690c0547e05a3b0751b80a8cc150dc038560442302e0d81705c03d6f01eb700f5ac0fad403d6701eb300f58e7eac408c6f0363582319c0d8c60ab6f015b5cecd9c056c603b5f9d1ae80ad6c056b203b5701daa80ad4c056a206b4f015a581ad1c056860aa6f9b935cd499c154c603a5f00d2e80e96c074b203a5700d2a80e94c0b4a206a4f0452582291c0d48602a3f9991dcc08dc054660396f01cb380e57c072bc0395d01ca780e5380d2840293f01c9b80e4bc0724e0a86f4d83380e17e5e0ba0385701c2a81a13c1108e0283f3481b9300bc7004e04d6f026b70131bc0d8d606c670263180717c038ba03c5b01e2c80715c038aa01c5300e28812dbc056d604b67015b1812d7c096ba02b5b015ac812d5c096aa02b53015a8812d3c0569604b47015a18069ac0f4d401a6700d3300698c034ae01a5500d2780692c0348e01a4300d1f8068ec0346e01a3300f3f8179f803cfa04d7f036bd81b5dc09ae601d6f00eb68075ac0dad201d67036b280758c03ac204c7f0163d8131dc058e601c6f00e368071ac058d201c670363280718c038c204c5f0162d81315c058a601b7b03dbd006de4036ee01b7600db9806dc4036ce01b6600db2806d7c036b601b5700da9806d3c0369601b4700da181a958092fc0797600cb70065b0032cd2d16401caf00a5380928c0193e00c9b01b5bc0dad606d67036b181b1bc058d606c670163181b17c058b606c5701629806dbc036ce05b6300daf816d6c036ae05b5300da7816d2c0368e02b4300d33806998074be03a5e02d2d8169680b4ae05a5602d2980e9480549e02a4e035258129280d48e04a460152180a9080b47e04a3e0373f81b9ec0dcee06e73036bf80b5ec0daee02d73036b780b5ac0dace02d6300e3f81f1f8038fa01c7700e3a8171cc0b8e401c6f02e3580719c0b8c601c5f02e2d80715c058a601b7700dbb006dd40b6de06b6e02db5816da80b6ce06b6602db1816d88056be02b5e02dad816d680b6ae06b56015a980ad480b69e05b4e02da681a998092fc0797601cb700a578092ac0594e02ca6006518032880593e02c9e0164da5626805d6f02eb68071bc038da01c6b00e3480719c038ca03c6301e3081b17c0d8b606c570362981adbc096da02b6b015b481ad9c096ca02b63015b081ad7c056b606b57015a981ad3c0569606b47015a18069bc034da01a5f00d2d80694c0349e01a4b00d2380690c0347e01a3b00d1b8068cc03cfe01e7e02f3e8075fc0dafa01d7b00ebc8075dc03aea01d73036b881b5bc0dad606d67036b18071fc0d8fa01c7b00e3c8071dc038ea01c730163881b1bc058d606c670163181b17c058b606c5701629806dfc036fc01b7d00db7806db8036d601b6900db181ed88036c201b5f00dad806d5c036a601b4f00da5806d1c0368601a7e01d3e01a958032fd2917c00cbb0065d0092dc0796601caf00a5380928c0193e02c9e0064d80326804d6f036b581b59c09ac604c6f0163581319c058c604c5f0162d81315c058a601b6f02db5816da8036ce07b6600daf816d6c036ae05b5300da7812d2c0368e02b4300d378069b8074be03a5e0252d8129680b4ae04a5602d2980e9480549e02a4e025258129280948e04a460152180a9080b47e05a3e034ab0139fc0dcf606e77027398135fc05af604d77016b98135bc05ad604d67016b18071fc038fa05c7b02e3d0071dc0f8ec01c7500e378171ac038ce05c6300e2f81316c038ae02c5300dbf806df8036fa05b6f035b7012dac0b6d405b67035b3012d8c0b6c402b5f015af012d6c0b6b404b57035ab00ad4c056a405b4f02da7016d340d4cc0497e03cbb00e5b8052bc0495602ca70065180927c0493c02c9b49c4d0098de04c6b0363481319c098c604c610262f813174098b603c590262b81b154078a603c51025b7812db4056d604b67025b280ad8c096be04b5d015ad80ad64096ae04b55015a980ad440969e02b4b025a380ad0c094de04a6b0253381298c094be01a5d0252d816964094ae01a55025298129440d49e06a4b0352381a90c0547e04a3b0251b80a8cc0dade06d6b036b381b58c0d8de02c6b0363380b18c0d8be02c5b0362b80b14e586df2a36b941b3c98d8c0d6be06b5b035ab81ad4c0569e06b4b035a380ad0c0d4ad2516e03cb300e5780529c0694602c9f0064d809ade06d6b036b381358c058de02c6b0163380b18c058be02c5b0162b80b14c036de05b6b00db3812d8c036be01b5d00dab806d540b6a601b4f015a5806d1c0568604a6f025370269ac0f4d409a6703d3301298c094c401a5700d2b00a93c0549c02a4b0152500a91c0548c02a43015210168fc0b47c04e7f0373d81b9dc09ce602d7f016bd80b5dc05ae602d6f016b580b59c05ac601c7f02e3d8071dc098e601c6f036370071b4038ce01c6502e31817188038be02c5b00e2b80b14c096fe04b7e02dbd816de80b6ee07b76025b9812dc8036ce01b6600db280ad7c056bc02b5b015ad00ad5c056ac02b53015a9016d3c0b69c05b4d0152f02a5f80f2ec0696e034b300a5580b29c0194602c9f0164f00b26d23134026b78135b813ad607d6a04eb381f59809ac604d620263781b1ac0d8ce04c6302e2f817174056de02b6b015b380ad8c056be02b5d00dad806d64036ae01b5500da9806d440569e02b4b015a380ad0c034de01a6b00d3380698c034be01a5d00d2780692c0348601a3f00d1d8068dc0346601e7f00f3f0079ec0fcf401e7700f3b0079cc09ce404d7f036bd81b5dc09ae601d6f00eb70175b4058fe02c7b0163b80b1cc038de01c6e016368131b0038d601c6900e33807194038c601c620163080b180058be02c5b0162b80b14c036fe01b7b00dbb806dcc036de01b6e00db6806d7c036bc01b5b00dac806d4c0d6a401b5100da7806d2c0368e01b430152702a5f80f2ec0196e908b6006598032c80695e034ae01a558112a80294600c9f0064d8098de04c6b0263381318c098be04c5d0262d81b164098ae08c5502629813144056de02b6d015b580ad9c056ca02b63015af80ad74056b602b59015ab80ad54056a602b51015a780ad2c0568e02b43025378129ac094ce04a630252f806974094b605a590252b806954094a604a510352782a92c1548e06a430151f80a8ec0546e02a33 20 1048575 8 255 11 2047 21 2097151
def cc_54_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x7fe7afa6ade75b3b3b674740df731aba6b1af95e89aadfe548a6a537c462888273ce5be9b3af334665d920af1813dc125056426f479d60d53d17d5a280f4455586b3f0a4640dcd813900004e 0x139fc0dcf606e77027398135fc05af604d77016b98135bc05ad604d67016b18071fc0b8f601c77026398071bc038da05c6b02e3500719c0d8cc01c6500e2f81316c038ae02c53025bf812df80b6f605b7a02dbb81edd8096e604b7200db7806db8036da02b5f015af012d6c096b404b57025ab00ad4c056a405b4f02da7016d340f4ec0397e034b701a598052bc0695602ca70065180b27c0593c02c9b57c4d007ade06d6b036b381358c038de04c6e00e3580719c038c601c6200e2f823178038ba04b6f015b5812d9c056c604b5f015ad812d5c056a601b4f00da6806d2c0368e04b4500da18069bc034d601a6700d3180696c034b201a5700d298069440348e01a4600d228068fc0347601a3700d1980f5bc07adc06d6b036b501f59c0dacc04d6301eb10131bc098dc06c6b03e3381318c098c404b6f015b5812d9c056c604b5f025ae80ad6c056b204b57025aa80ad4c056a204b4f025a680ad2c0968e04b45015a18129bc0f4d607a670253182297c034ba08a5b02d2c82295c034aa08a5302d2881a93eba49a08a4b045238229140d48602a3f0251d8128dc0546604d6f026b581359c09ac603c6f01e3700b1ac058d402c670163300b18c058c404c5f0262f01316c118b404c570262b01314c0d8a402b6f025b700adac056ce02b63015b100ad7c056b602b5a015ab812d58056a604a6f0253581299c094c606a5f0552d82a95c0d4a604a4f00d2681292c0949204a4700d2281290c0b48202a3f0151e80a8ec0546e04a35015198135bc0fad607d67026b18131bc058d604c670163181317c058b604c5701629812dbc0f6d607b67025b1d80d7c156b60ab57af1a980ad3c0969604b47015a181e998072dc0695eae0ab00a53ab628c0593e00c9b00f5bc07adc03d6d026378131ac0d8d204c6702631813184098be04c5d0262d81315c0d8aa04b6f015b5812d9c056c604b5f025ae80ad6c056b204b57025aa80ad4c056a204b4f015a5812d1c0568604a6f0253581299c094c604a5f00d2e81296c0b4b204a5700d2a81294c094a206a4f0352581a91c0d48602a3f0251d8128dc054660396f01cb680e59c072ca0395f01cae80e55c072aa0394f01ca380a4fc0726e0392f01c938121bc090ce0485f0242e81215c170aa0684f0342380a0fc0906e0c82f1d81380f5bc07ada04d6b026b480f59c07aca03d6301eb08071bc038da01c6700e3280718c098be06c5b0362b81314c096de04b6d015b580ada4096ce04b65015b180ad84096be02b5b025ab80ad4c0969e02b4b025a380ad0c034de01a6d00d358069a4034ce01a6500d31806984034be01a5b00d2b80694c0349e01a4b00d2380690c0347e01a3b00d1b8068cc032de0196d01cb380e594072be0395700ca780e51c0527e0393700c9780649c190de0b86d0643382e194090be078570342781a11c0507e0483700c1780609c03cfe05e7e00f3e8135fc0daf606d77026b98075bc03ada01d6b036b480759c0daca01d6300eb080f1fc098fc03c7b01e3d00f1dc0f8ec03c7301e390071bc038dc01c6d00e360071ac038d403c6901e3400719c038cc03c65ac23200718c038c401c6100e30012dfc056f604b77015b9806dbc036da01b6b015b4806d9c0d6ca01b6300db0812d7c056b604b57015a980ed3c0769a02b4b015a480ed1c0968a02b43015a08069ec0f4f401a7900d3b8069d8034e601a7100d33806998034ca01a5f00d2d80695c034a601a4f00d2680692c0349201a4700d2280690c0348201a3f00d1d8068dc034660397f01cbb8065bc032da0196701cb281a568072ae0395601ca380e5180728a0293f01c9b8064bc0324e0487f03c3b8061bc030da0186708c3281a17c0d0ae0384f01c2680e11e9e08a0283f0241b8060bc0304e03d6f01eb700f5ac03ad401d6700eb300f58c07ac406c6f0363581b19c0d8c605c5f02e2e81715c0b8aa05c53035b780adac0d6ce02b63035af812d74056b602b59035ab812d54056a602b51035a780ad2c0d68e02b4300d3780e9ac034ce05a6300d2f8069740b4b604a5900d2b806954074a603a5100d2781692c0348e05a4300d1f8168ec0346e02a3301cb780e59c072be0395d01cab80e5540729e039470149f80e4dc0725e0192702c3781619c0b0be0585d02c2b8161540b09e058470141f8160dc0b05e018270373f81b9ec0dcee06e7301ebf8135f807af603d7a01ebb81f5d807ae603d720363f80b1ec0d8ee02c730363780b1ac0d8ce02c6301e2f80f174058b602c5901e2b813154058a602c5100dbf81edf8036fa01b7700dba816dcc0b6e401b6f02db5806d9c0b6c601b5f00dae80ed6c0b6b201b5700daa80ed4c076a201b4f02da5806d1c0568601a7700d3b0069d40b4de06a6e02d358169a80b4ce06a6602d31816988074be03a5e01d2e80e970074b603a5a02d2c816960074ae03a5602d2ad58950074a603a5201d2880e9400549e02a4e02d258169280b48e06a460152180a9080b47e05a3e02d1e80e5fc072ee0696a01cb380e598072ae0395601caa80a53c0728e0393f00c9b80e4bc0725a0392701c928161fc0b0ee0586f02c3380e17c070ba0385702c2a80a13c0b08e0583f00c1b8160bc0b05a0582702c1280f5bc07adc05d6b02eb500f59c07acc03d6301eb101b1bc0d8d606c670363180717c038ba01c5b00e2b8071540d6de02b6b035b380ad8c0d6be04b5d015ad80ad640d6ae04b55015a980ad440d69e02b4b035a380ad0c034de01a6b00d3380698c034be01a5d00d2d806964034ae01a5500d298069440349e01a4b00d2380690c0347e01a3b00d1b8068cc072de0396701caf80e574032ae0195500ca780e51c0527e0393700c9780649c0f0de0786703c2f81e1740f0ae078550342781a11c0507e0683700c1780609c03cfe01e7e02f3e8075fc0dafa01d7b00ebc8075dc03aea01d73036b881b5bc0dad606d67036b18071fc038fc03c7daa23e0071ec038f401c7900e3c0071dc038ec01c7500e3a0071cc038e403c7101e3800f1bc098dc03c6b01e3500f19c0f8cc03c6301e31006dfc0d6fa01b7b00dbc806ddc036ea01b73015b881adbc056d606b67015b181ad7c056b606b57015a980ed3c0769a02b4b015a480ed1c0968a02b43015a08069fc034fc01a7d00d378069b8034d601a6900d3181e988034c201a5f00d2d80695c034a601a4f00d2680692c0349201a4700d2280690c0348201a3f00d1d8068dc034660197f00cbf00e5f4072f80197700cba8065c8072de03967034ad00e55c072ac0394701ca300e5140527e0393700c9780649c030fe0787d00c3b8061d40f0de078670342f81a15c0709e0384d01c2381e1140507e0683700c1780609c03ade06d6b036b381358c078de04c6e01e3580f19c078c603c6201e2f823178078ba04b6f015b5812d9c056c604b5f015ad812d5c056a603b4f01da680ad2c0768e04b45015a18069bc0b4d601a6701d3180697c0b4b601a5702d2980693c0749605a4900d2380e90c0748201a3f0251d8068dc054660396f01cb380e57c072ae0394701ca300e5140527e0393701c9780649c090de0586702c2f81615c0709e0384d01c238161140507e0483702c1780609c03ade01d6e01eb580f5a807ace03d6601eb1807588098de06c6b0363381318c098be04c5d02e2b8131540b8a604b6f015b5812d9c056c604b5f025ae80ad6c056b204b57025aa80ad4c056a204b4f015a5812d1c0568601a6f02d3580699c074c601a5f00d2e81696c0b4b201a5700d2a80e94c074a201a4f02d2580691c0b48601a3f0251d8068dc054660396f01cb380e57c072ba0395701caa80e53c0d2940394701ca300a4fc0726e0392f00c938121bc0b0ce0585f02c2e81615c0b0aa0584f02c2380a0fc0906e0582f00c138139fc0dcf606e770273980f5fc09afc03d7b01ebd00f5dc0faec03d7301eb90131fc058f604c77016398131bc058d604c670163180f17c078ba02c5b0162c80f15c098aa02c5301628806dfc036fa05b7b02dbd006ddc0f6ec01b7500db7816dac036ce05b6300daf806d74076b605b5900dab806d54076a603b5100da7812d2c0368e02b4300d3f8069f8034fa05a6f035370169b40d4d804a6b02d3501699c0d4cc05a65a913201298c0b4c403a5f01d2f00e974074b803a5b01d2d012964094b003a5701d2b016956a24a803a5301d2900e944074a002a4f0152701292c0b49404a470352300a90c0548405a3f02d1f0168f4072fe03977034b500e59c072cc0395701cab00e5540529e0394701c9f8064dc0725e0392d01c9380e494090fe0587702c3781619c070be0385d01c2b8161540509e0484702c1f8060dc0905e0582d02c138160940bcfc01e7d00eb681b5a40daca01d610263f01f1e80f8ec04c7200e370071b4038d801c6a05e3484b1a0038cc0bc6505e32007188038c201c6000db680ada40d6ca01b61025a680ad240968a02b4102d3d0069e4034ec01a7100d330069940349c01a4d00d260069240348a05a4200d208169000d0bc0384e00c1301b5bc0dad606d67036b182f1bc098dc07c6b03e3501f19c0f8cc0bc630263101adbc056d606b67015b181ad7c056b606b57015a981ad3c0969a02b4b015a481ad1c0968a02b43015a0d3c9bc0b4d607a6702d3181a97c0b4b606a5702d2982e93c0349a05a4b02d2482e91c0348a05a4302d2080a8fc0b47606a370151981a1780709c0b826036b781b5ac0dace06d6301e37d651b8078d603c6a01e3381f198078c603c62035b780adac0d6ce02b63035af80ad6c0d6ae02b5301da780ed340569602b4901da381ad140568602b41ab937d549aea64cf502630352f81a96c0d4ae06a5301d278069340749605a4901d238069140748603a410151f81a8ec0d46e02a3301cb780e59c0d2b40395701cab00e51c0728c039450149f80e4dc0725e0392755037a7819c0d0be0685701c2780e1340708f4e0450141f81a0dca005e3a027016b780b5b4078de03c6e01e368131ac098d206c6701e3281b18c0d8c404c610263001317c0d8b606c570262980adbc056da02b5f03daf00ad6c056a602b52015a780ad2c0568e02b430d5378069b4334d605a690cd33806994354c605a610252f81e96c0f4ae04a530352781a92c0d48e06a430151f80a8ec0546e02a330173f80b9f805cfa06d7f03ebf01b5f411af804d7b036bc8135dc0daea06d73036b901b5c40dae004d6f036b581b59c09ac602c7f03e3f00b1f4058de07c6e0163580b1a4058c602c620163080b17c058b602c570162981edfc036fa04b7b02dbc812ddc036ea07b7302db8812dbc0f6d607b67025b181ad7c0d6b606b57035a980ad3c0569602b47015a181a9780f2fd4c17c024bb0125d0092dc0796601cab00a5380528c0593e00c9b01f5bc0dad607d67036b181f1bc058d607c670163181b17c058b606c5701629806dbc036ce05b6300daf816d6c036ae05b5300da7816d2c0368e02b4300d338069980b4be05a5e02d2d80e968074ae03a5602d298169480549e02a4e04d258129281348e04a460152180a9080b47e04a3e03f3f81b9ec0fcee06e7303ebf80b5ec0faee02d73036b780b5ac0dace02d6300e3f81f1f8038fa01c7700e3a8171cc0b8e401c6f02e3580719c0b8c601c5f02e2d80715c058a601b7700dbb006dd40b6de06b6e02db5816da80b6ce08b6602db1816d88056be02b5e02dad816d680b6ae09b56015a980ad480b69e05b4e02da681a9b8092fc0797601cb300a578092ac0594e00ca30164f80b27805936a509a0175bc0bada03c6f01e368071ac038d201c6700e3280718c038c207c5f0362d81f15c0d8a609b6f025b680adac056d209b67025b280ad8c056c207b5f015ad81ed5c056a606b4f015a581ad1c0568601a6f00d3680697c034b601a5300d2780692c0348e01a4300d1f8068ec0346e01a33034a70079fc03cfc05e7d00ebf8235f403af601d7900ebb8075d403ae606d7103eb781b5ac0face06d6300e3f8271f4038f601c7900e3b8071d4038e602c7103e3780b1ac0f8ce02c630362f80b16c0d8ae02c5300dbf806df8036fa01b6f00db7006dac036d201b6303db1006d84036be01b5b00dab806d4c0369e01b4b00da3806d0c0d4bc0197ea40be0065d8032e80496e03cb300e5580529c0494600c9f0064d809ade06d6b036b381358c058de02c6b0163380b18c058be02c5b0162b80b14c036de05b6b00db3812d8c036be05b5b00dab816d4c0369e01b4d00da3806d140568604a6f025370269ac0f4d409a6703d3301298c094c405a5f0252f01696c074b403a5701d2b01294c094a401a4700d2300a8fc0547c04e7f0373d81b9dc09ce602d7f016bd80b5dc05ae602d6f016b580b59c05ac601c7f02e3d8071dc098e601c6f02e3580719c0b8c601c5f0162f007174038ae01c550162980b148096fe0ab7e025bd816de8096ee07b76025b9816dc80b6de06b6e025b5816da80b6ce06b66025b1816d88036ae01b5600daa80ad3c0569c02b4d035370125f80f2ec03966014af00a5580b29c019460249f0124f00b26d46134026b781b5ac0dace04d63026378131b8138d607c6a04e3381f198098c604c6200e2f807178078b603c5a00e2b807158038a601c52015b780adac056ce02b63015af80ad6c056ae02b53015a780ad34034de01a6b00d3380698c034be01a5b00d2b80694c0349e01a4d00d1f8068ec0346604e7f0373d81b9dc09ce601d7f00ebf0075ec0faf401d7700ebb0075cc15ae401d6f00eb70075ac0dad401d6700eb300758c0dac402c7f0163d80b1dc058e602c6f0163580b19c058c601c5f00e2f00b174036fe01b7b00dbb806dcc036de01b6b00db3806d8c036be01b5e00dae806d3c0369c01b4b00da4806d0c0568401b41035370125f80f2ec0396600caf510570032ac01954014a700a5300528c0494400c9f0064d8098de04c6d0263581319c118ca04c6301e2f80f174098b606c590262b80f154098a604c51025b780adac096ce02b63025af812d74056b602b59025ab812d54056a602b51025a780ad2c0968e02b43025378129ac094ce04a630252f806974094b605a590252b806954094a604a510352782292c1148e06a430151f8128ec0946e02a33026b78135ac09ace04d63026378131b8098d604c6a02633813198098c604c620162f80b178058b602c5a01e2b80f158058a602c52015b7812db8056d602b67015b180ad88056be02b5b015ad00ad5c096ac02b53025378129ac094ce04a630352f81a96c0d4ae06a53025278069340949604a49025238069140948605a410151f80a8f40547602a370251a80a8cc11ade06d6b046b381b58c158de02c6ba5a3380b18c0d8be02c5b0362b80b14c156df4936ba39b382ad8c0d6be08b5b045ab81ad4c0569f4534ba19a380ad0c0d4bd4216e03cb300e5580529d4114602c9f0064d809ade04d6d026b581359c11aca04d6301e3780f1b8078da04c5f0362f01315c098a604c52025b780adac096ce02b63025af80ad6c096ae02b53025a7812d340569602b49025a3812d140568602b41025378129ae724d204a67025318129840d4be08a5b0452b81a94c0949e01a4d025258169240948e01a45025218129040547e04a3b0251b80a8cc072de0396d01cb380e594072be0395701ca780e5340728e039450149f80e4dc0725e039270243781219c0d0be08857024278121340908e0b8450141f8120dc9e05e39027 19 524287 7 127 11 2047 21 2097151
def cc_54_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x8a24e8554d82c297b3797644f6eb796b833670486452b6083d5dd2b5a03d5861a55a2c519414ee2b4af3f47b3445b2040d4e3c04d3437d2f44f27b7922a511b1791644d0e48009c4806f2d0303f00030 0x16b780b5b405ace02d65016b18131bc118da04c6b0263481319c098ca04c630363081317c098b604c570262980adbc076dc02b6d015af812d78056b602b57015a980ad480569e02b4b015a380ad0c094de01a6d025358129a4094ce01a6502531816984094be04a5b0252b81294c0d49e0aa4b0552381a90c0547e02a3b0151b80a8cc052de0296d01cb380e594052be0395701ca780e51c0527e0293d0149b80e4d40725e039270243782e1b4090ce048650242f81215c0d09e0a8470141f80a0f40506e048350741783a09c03ade01d6d00eb380759403ac603c6f01e368171ac0b8d203c6701e3280f18c078c204c5f0362d81b15c098a604b6f025b680adac056d204b67025b280ad8c056c204b5f015ad812d5c056a604b4f015a5812d1c0568601a6f00d368069ac034d201a6700d3280698c034c201a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1d8068dc034660196f00cb680e59c072ca0195f01cab80e53c0728e0293f01c9b8064bc0324e0c86f05c3683219c170ca0485f03c2b81a13c0d08e0283f0241b8060bc0304e03d6d036b481b59407ac204c7e03e3d01f1d8098e403c6e01e3680f1b0078d40bc6909e3400f198178ca0bc6401e3100f184078c005c5e01db680ada40d6ca02b61025a680ad240968a02b4100d368069a4034ca01a6100d2280e5d8072cc0394e01ca601a1780309c01826026bf81b5ec0daee04d7301eb780f5b407ad606d6901eb381b59407ac603d6100e3f8131f8038f601c7a00e3b81f1d8038e601c7200e3780f1b8038da03c6c00e358071a8038d201c6800e3380f198038cb7d46400e31807188038c201c6000e2f817178038ba04b7f015bd812ddc056e603b6f01db680adac056d203b67035b280ad8c056c204b5f015ad812d5c056a601b4f00da6806d2c0569201b47025a2806d0c0368201a7f00d3d8069dc034e601a6f00d368069ac034d201a6700d3280698c034c201a5b0352d006964034ae01a5600d298069440348e01a4600d228068fc0347601a3700d1981e5e8072ee0397601cb380e598072ca0395f01cab80653c0329a0194701ca280a4fc0726e0192f00c938121fc0f0ee0386f01c3680e19c230ca0685f0342b80613c0309a01847be02280a0fc0906e0182f00c138175bc0bada05d6702eb281358c078de03c6d00e358071a4078ce03c6501e31807184098be06c5b0362b81314c096de04b6d015b580ada4096ce04b65015b180ad84096be02b5b025ab80ad4c0969e02b4b025a380ad0c034de01a6d02d358169a4034ce01a6501d3180e984034be05a5b00d2b81294c0349e05a4b00d2380e90c0347e04a3b00d1b80a8cc072de0396d01cb380e594072be0795a01cab80e5580729e039470149f80e4dc0725e0192702c378161b40b0ce058650242f81615c0b09e058470141f8120dc0b05e01827026bf81b5ec0daee04d7301eb780f5b407ad606d6901eb381b59407ac603d610263f80b1ec098ee02c7301e3780f1b4058d602c6901e3381b194058c602c610262f80b16c098ae02c5300dbf816dec036ee04b7300db7806db4076d605b6900db3806d94076c603b6100daf806d740b6b605b5a00dab81ad58036aa01b4f025a5806d1c0568604a7f0253f0169ec0b4f405a7703d3b0129cc094e403a6f01d3700e9b4074d803a6b01d350169a40b4d003a6701d33016996f44c803a6301d3100e984074c001a5f00d2f0069740549e02a4e025258129280948e04a460152180a9080b47e05a3e02d1e81e5e8072ee0397601cb380e598072ca0395f01cab80a53c0728e0393f00c9b80e4bc0725a0392701c928121fc0b0ee0386f01c3680e19c0b0ca0585f02c2b80a13c0908e0583f00c1b8160bc0b05a0582702c128131bc0f8d607c670263182b17c118ba0bc5b0362c82b15c118aa0bc5303628812dbc056d604b67015b1812d7c096ba02b5b015ac812d5c096aa02b53015a8812d3c0569604b47015a18129bc0b4d607a670253182e97c034ba05a5b02d2c82e95c034aa05a5302d2884693c0b4960aa4702d2180a8fc0947604a37015198121b8070bc048360263781f1ac0f8ce04c6301e2f80f174078b606c5901e2bdfd154078a603c51025b780adac096ce02b6301daf80ed74056b602b5901dabdf8d54056a602b51025a780ad2c0968e02b430253781e9ac0f4ce04a6301d2f806974074b605a5901d2b806954074a603a51bd92782a92c1548f792430151f8128ec0946e02a3303cb500e59c072cc0395701cab00e5540729e039470149f80e4dc0725e039270243781e19c070be0385d01c2bde01551c09e0a8470141f8120dca405e3c027036b781b5ac0dace06d6300e378071b8038d601c6a01e3380f198038c601c6202e2f8171780d6de02b6b035b380ad8c0d6be02b5b035ab80ad4c0d69e04b4d015a580ad240d68e04b45015a180ad04034de01a6b00d3380698c034b601a5700d2980691c0348a01a3f00d1d8068dc0346606e7f0373d81b9dc0dce601d7f026bf0075ec03af401d7703ebb0075cc03ae401d6f02eb70075b40d8fe02c7b0363b80b1cc0d8de02c6b0363380b18c038be01c5d00e2d80b164038ae04c5500e29807144036fe01b7b00dbb806dcc036d606b6a00db4806d9c036cc01b6300db0806d5c036ac01b5500da7806d2c0368e01b4303d3f00e5d80d2dc0696600caf006570032ad76154014a701a5180327c0193603eb781b5ac0face06d6303e3780b1ac0f8ce02c630362f80b16c0d8ae02c5300db7816dac036ce05b6300daf806d5c0b6a601b4f02da5806d1c0568605a6f025370169ac074d403a6701d3301698c094c401a5700d2b00a93c0549c09a4b0252502691c0948c02a43015210168fc0b47c07e7f0373d81f9dc0dce607d7f016bd81f5dc05ae606d6f016b581b59c05ac601c7f02e3d8071dc0b8e601c6f036370071b4038ce01c6502e31817188038be05c5b00e2b80b14c0b6fe04b7e02dbd816de80b6ee07b7602db9812dc8036ce01b6600db280ad7c056bc05b5b025ad016d5c096ac02b53015a9016d3c0b69c05b4d03d3f00e5d80d2dc08966014af0265580b29c0194602c9f0164f00b26d74134026b78135ac09ace04d630263780b1ac098ce02c630262f80b16c098ae02c5300db7806dac036c601b5f00dad806d5c036a601b4f00da5806d1c0368608966024ab0064d803ade01d6e01eb580f5a803ace01d6600eb18075880f8de06c6b03e3381b18c0b8be05c5d03db780adac0f6ce02b6304daf812d74056b602b5904dab812d54056a602b51035a780ad2c0d68e02b4300d378069ac034ce01a6300d2f8069740349e01a4b00d218068fc0347601a3700d1981e5b803cfe01e7e00f3d81f9e803cf207e7800f3b8079d803ce604e7200f38dc99c00fafe06d7b03ebb81b5cc03ade01d6e02eb681f1fc058f607c77016398071bc098da01c6b00e3480719c038ca01c630163081b17c058b606c5701629806dfc036f601b7700db9806dbc036dc01b6d00daf806d78036b601b5900da981ad48036a201b4f00da5806d1c0368607a7e01cbb0065bae22d80196600cb201a578112ac0294e04ca30064f80326c06d6f036b581b59c0dac606c6f0163581b19c058c606c5f0162d81b15c058a601b6f02db5806d9c0b6c601b5f02dad806d5c0369e05b4b00da380ad0c0b4de04a6e02d3580e9a8074ce03a6602d31812988034be01a5e0152780a9380d49604a4a035238129180548602a4202d1f8168f80dcfe06e7b0373b81b9cc0dafe02d7b036bb80b5cc0dade02d6b036b380b58c038fe05c7b00e3b8171cc038de01c6d02e358171a8038ce06c6600e3280717c0b8b601c5701629816dfc096fc05b7b02dbd016ddc0f6ec05b73025b9006dbc036dc01b6d015af80ad780b6b604b5a02dab812d58056a602b5202da7816d380b69a07a7e02d1b00e8d0072ec0696e034b300a5780d2ac0594e00ca30164f80b27805936b789a01f5bc09adc07d6b01eb500f59c07acc06d63026b101f1bc0d8d607c6a03e3381f1980d8c607b6f015b581ed9c056c608b5f025ae80ad6c056b208b57025aa80ad4c056a206b4f015a580ad240d68e02b43015a081e9bc0f4d607a6703d3182297c034ba08a5b02d2c82295c034aa08a5302d2881a93c1149608a470352180a8fc1147608a370151981f5bc0fad607d6703eb181f1bc058d607c670163182717c058b609c570162981edbc0f6d607b6703db1dd4d7ee66b770357b71a980ad3c1369609b47015a181e9b8072cc0695eb68ab00a5381328c0593e00c9b01b5bc09adc07d6703eb18135880f8de06c6b03e3501f19c0f8cc06c6301e2b80f158078aa07b6f015b581ed9c056c608b5f025ae80ad6c056b208b57025aa80ad4c056a206b4f015a580ad240d68e02b43015a081e9bc0f4d607a6703d3182297c034ba08a5b02d2c82295c034aa08a5302d2881a93c1149608a470352180a8fc1147608a370151980e5bc072ce0395f01cae80e55c072aa0394f01ca680e51c0728a0293f01c9b80e4bc0724e0786f03c3381e17c0f0ba0785703c2a81a13c0f08e0283f03c1b81e0bc0f04e01d6f00eb700759c03ac601d620363781b1ac0d8ce06c6301e2f80f174078b603c5901e2b80f1540b8a605c51035b780adac0d6ce02b63035af812d74056b602b59035ab812d54056a602b51035a780ad2c0d68e02b4300d378069ac034ce01a6300d2f806974034b601a5900d2b806954034a601a5100d2780692c0348e01a4300d1f8068ec0346e01a3301cb780659c072be0395d00cab8065540729e039470149f80e4dc0325e0192703c3781e19c0f0be0785d03c2b81e1540d09e068470141f81a0dc0305e0182701ebf81b5f407af603d7901ebb80f5d407ae606d71036b781b5ac0dace06d6300e3f80f1f8038fb6a47c00e3d8071e8038f201c7800e3b80f1d8038ea03c7400e398071c8038e201c7000e378131b8038d601c6a00e3381f198038c601c6200e2f817178038ba03b7f035be80adec056f203b7701dba80adcc056e206b6f015b581ad9c056c606b5f015ad81ad5c056a601b4f00da6806d2c0569201b47025a2806d0c0368201a7f00d3f0069f4034f801a7b00d3c8069dc034ea01a7301d390069c40b4e001a6f00d3580699c034c601a5b0352d006964034ae01a5600d298069440348e01a4600d228068fc0347601a3700d1980e5fc072fc0397d01cb780e5b80f2c40395f01cab80653c0329a0194701ca280a4fc0726e0192f00c9380e1fc0f0fa0387701c3a81e1bc0f0ce0685f0342b80613c0309a0184703c2280a0fc0d06e0182f00c138175bc09adc05d6702eb18135880f8de06c6b03e3381b18c038be01c5d01e2d80f164078ae01c5501e2980f1440f6de02b6b03db380ad8c136be04b5d015ad80ad64136ae04b55015a980ad440d69e02b4b035a380ad0c034de05a6b00d3381698c034be01a5d01d2d80e964034ae01a5502d298169440349e06a4e01d2580691c0b48605a4200d1f8168ec0346e02a3301cb780e59c072be0395d01cab80e5540729e039470149f80e4dc0725e0192702c3781619c0b0be0585d02c2b8161540b09e058470141f8160dc0b05e0182701ebf8235f407af603d7901ebb80f5d407ae606d7103eb781b5ac0face06d6301e3f8271f4058f602c7901e3b80f1d4058e602c7103e3780b1ac0f8ce02c630362f80b16c0d8ae02c5300dbf806df4076f603b7900dbb806dd4076e605b7100db7816dac036ce05b6300daf81ad78036ba01b5700daa816d4c0b6a401b4f02da5806d1c0568603a7f01d3f0169f6d04f803a7b01d3d00e9e4074f003a7701d3b00e9d4074e803a7301d390169c40b4e005a6f025370169ac0b4d405a6703d3301698c094c401a5700d2b0069540549e02a4e02d258129280b48e04a460152180a9080b47e05a3e02d1e80e5fc072fc0397d01cb780e5b80f2c40395f01cab80a53c0728e0393f00c9b80e4bc0725a0392701c9280e1fc0b0fa0387701c3a8161bc0b0ce0585f02c2b80a13c0b08e0583f00c1b8160bc0b05a0582702c1281f5bc0dad607d67036b18071bc038dc01c6700e31807188078be03c5e02e2d817168078ae03c5601e2980f1480f6de02b6b03db380ad8c0d6be02b5b035ab80ad4c1369e04b4d015a580ad241368e04b45015a180ad04034de01a6b00d3380698c034be01a5e00d2d80695c034a606a5200d278069340349601a4900d238069140348601a4100d1f8068ec0346e01a3301cb780e5b8032ce0796201caf80e55c0729e0394d00ca38065140527e0393700c9780649c0f0de078670342f81e15c0f09e0784d03c2381e1140507e0783700c1780609c03afe01d7e00ebe8075f003af603d7a00ebc80f5e003aee01d7600eba8075d003ae603d7200eb8d995c003ade01d6e00eb581f5a803ace01d6600eb1813588078fe08c7d01e3d80f1e4078ee03c7501e3981b1c40f8de06c6b03e3381b18c038be01c5e02e2e80edfc136fa02b7b015bc80eddc076ea02b73015b881edbc056d607b67015b1806d7c096ba01b5b00dac806d5c036aa01b53015a881ad3c0569606b47015a18069fc034fa01a7b00d3c8069dc034ea01a7300d388069bc034d601a6700d3180697c034bc01a5d00d278069380349601a4900d2181a9080348201a3f00d1d8068dc034660397f01cbf00e5f4072de0396e03cb100657c072ba0195700caa80e53c0728e0293f01c9b8064bc0324e0387f03c3e80e1dc070ea0786f03c3380617c0f0ba0185700c2a81a13c0f08e0283f03c1b8060bc0304e05d6f026b701759c0bac604d620363781b1ac0d8ce06c6301e2f80f174078b601c5901e2b80f154038a601c51035b780adac0d6ce02b63035af812d74056b602b59035ab812d54056a602b51035a780ad2c0d68e02b4300d378169ac034ce05a6300d2f806974074b603a5900d2b8069540b4a605a5100d2781692c0348e03a4300d1f8168ec0346e02a3301cb780e59c072be0395d01cab80e5540729e039470149f80e4dc0725e0192702c3781619c0b0be0585d02c2b8161540b09e058470141f8160dc0b05e0182701ebf81b5f407af603d7901ebb80f5d407ae606d71036b781b5ac0dace06d6301e3f81b1f4058f602c7901e3b80f1d4058e602c710363780b1ac0d8ce02c630362f80b16c0d8ae02c5300dbf80edf8036fa01b7c01dbd80ede4036ee01b7501db980edc80b6e205b7000db7816dac036ce05b6300daf806d740b6b605b5a00dab81ad58036aa01b4f02da5806d1c0568603a7f01d3f0169f6c84f803a7b01d3d00e9e4074f003a7701d3b00e9d4074e803a7301d390169c40b4e005a6f025370169ac0b4d405a6703d3301698c094c401a5f00d2f0069740549e02a4e02d258129280b48e04a460152180a9080b47e05a3e02d1e80e5fc072fc0397d01cb780e5b80f2c40395f01cab80a53c0728e0393f00c9b80e4bc0725a0592a01c9380e4980724a0392401c3f8161f4070ee0387502c3781619c0b0be058570142781611c0b07e0183702c178160b40b04e0582501e37dad1b4078d603c6901e3380f194078c606c6103e2f81f16c0f8ae07c5301db7826db4056d602b6901db380ed94056c602b6103daf80ad6c0f6ae02b5304da780ad2c1368e02b4301d378069b4074d603a6901d33806994074c605a6103d2f81e96c0f4ae07a53b4927d9c92eca48f632430151f8268ec1346e02a3301cb780e5b8072da0395f01caf01e5480729e039470149f80e4dc0725e0392701c3781e1b4070ce0386503c2f81e15c0f09e078470141f81e0dc0f05e07827026b781b5ac0dace04d6301e3780f1b8038d601c6a00e33807198038c601c6202e2f817178096de02b6b025b380ad8c096be02b5b025ab80ad4c0969e04b4d015a580ad240968e04b45015a180ad04034de01a6b00d3380698c034b606a5a00d2b806958034a601a4700d228068fc0347601a3700d198139fc0dcf606e77027398075fc09afc01d7b00ebd0075dc0faec01d7300eb90075bc0badc01d6d0263f80b1ec098ee02c730263780b1ac098ce02c6300e2f807174038b602c5900e2b813154038a601c5100dbf806dec036ee01b7300db581ada8036d201b6700db3006d8c036c201b5700dab006d540369e01b4b00da3806d0c0f4ec0397e034b701a5b00d2cd5d16400caf006570032ad61154014a701a5180327c01936026b781b5ac0dace04d630263780b1ac098ce02c630262f80b16c098ae02c5300db7816dac036ce04b6300daf806d740b6b605b5a00dab81ad58036aa01b4f025a5806d1c0568603a6f01d370169ac0b4d405a6702d3301298c074c401a5f00d2f00a93c0549c04a4b0252501291c0948c02a43015210168fc0b47c07966 20 1048575 8 255 11 2047 21 2097151
def cc_54_12 : Nat → List (Nat × Nat) := unpackCursorV4 0xbca61b6169b0061a936da266d9c56195e6790f4f8ae6183d717a19c73a676cd6d66c6160369600035f907588714ec9c47f6d42c533cb61362693016129a6722d6d1cc61165670fc690ad4f04c610004c 0x1f5bc0fad607d6703eb181f1bc058d607c670163182717c058b609c5701629806dbc0f6dc01b6d00db3806d940b6c605b6200daf816d6c036ae05b5300da7816d2c0368e02b4300d33806998034ca05a5f0352f01696c0b4b405a57cf92b01694c0b4a402a4f0152701692c0b49405a4704d2300a90c0548405a3f02d1f0168f40f2de0796b03cb381e58eaa2bf4915b9b8abca854c0529e0994b04ca380a50c0b27e0193b00c9b8164cc0b25e0392d02c9581649c0724a0592302c378161ac0b0ce0586302c2f81616c0b0ae058530142781612c0b08e0284302c1f8060ec0306e0583302c178160b40b0560582702c1281608c0b03e0581b02c0b81604c0dade04d6e02eb58175a80face05d6603eb18135880f8de06c6b03e3501f19c0f8cc06c6300e2b807158038aa07b6f015b581ed9c056c608b5f025ae80ad6c056b208b57025aa80ad4c056a206b4f015a580ad240d68e02b43015a08069bc034d601a6700d3180697c034ba01a5b00d2c80695c034aa01a5300d2880693c0349a01a4b00d238069140348601a3f00d1d8068dc034660796f03cb581e59c0f2c60895f01cae82256c112ae03955044a981a53c1129608947034a180a4fc1127608937014998064bc032560192700c9181e1bc0b0d60786702c3181e17c0f0ba0585b03c2b81e1540b0a60684f02c2581e11c0b0860283f02c1d81e0dc050660182f00c1580609c030460781f02c0d81e05c0b02601d6f00eb70175b4038df9d46d00e358071a4038ce01c6500e3181b1840f8be07c5b03e2b81f14c036de09b6d00db5806da4036ce01b6500db180ad840f6be02b5b03dab80ad4c1369e02b4b04da380ad0c034de01a6e00d3680697c034bc01a5b00d2c80694c0f4a401a5100d2780692c0348e01a4300d1f8068ec0346e01a3300cb780e5b4032d60196700cb280658c0f2be0795b03cab81e54ea629f4714b9a8a3ca050c0527e0993b04c9b80a4cc0325e0192b00c9380648c030de0786d00c3580619c030ca0186303c2f81616c0f0ae0585303c2781612c0f08e058430141f8160ec0f06e0283300c178060ac0304e0182303c0f81606c0f02e0581300eb78075b80dad606d6a03eb381b59809ac601d62026378131b80d8d607c6702631813188098be04c5e0262e812dbc056d604b67015b1812d7c096ba02b5b015ac812d5c096aa02b53015a8812d3c0969a02b4b025a3812d140568601a6f02d3580699c094c601a5f00d2e81696c0b4b201a5700d2a81694c0b4a201a4f02d258169240348e05a4302d208068fc0947601a37015198125bc0f2d607967024b182257c072ba0895b044ab80e554112a60694fa90a682252c1128e08945034a180a4fc0927604937014998164bc032560192702c918121bc0b0d6058670243181617c0b0ba0585b02c2b8161540b0a60584f02c2681612c0b08e0584502c2180a0fc0907604837014198160bc030560182702c1181607c0b0360581702c098135bc09ad604d67026b18071bc038dc02c6b0163500b19c058cc02c6300e3101317c098bc04c5b0462d01315c098ac04c530362900adbc096dc02b6b015b380ad8c056c402b5f015ad80ad68056ae04b56015a980ad3c0969c02b4d00d378129ac034ce02a6300d2f81696c034ae05a5300d278069340949604a4900d238069140548602a4100d1f80a8ec0947201a370151980a8c4092de0496b024b381258c0d2be0a95b054ab81a54c0929e0394d024a581251c0728a049430149f80a4f405276029370249a80a4cc0b25e0192b00c9381648c090de0486b0243381218c0b0be0585b02c2b81614c0909e0584d0242581211c0908a048430141f80a0f405076028370241a80a0cc0b05e0182b00c1381608c0b03e0581b02c0b81604c09ade07d6b03eb381358c098de02c6b0263380b18c098be02c5b0262b80b14c036de01b6d02db5816da8036ce07b6600db2806d7c0b6b601b5702da9806d3c0969601b47015a18069bc034dc01a6d02d2f81a978094b605a5a02d2be6c958094a605a520152780a9380949605a4a02523e689180548602a4202d1f8168f80b47a0496f03cb581e59c092c75015f054ad82a55e4c2a60294f024a581251c052860593f00c9d8064dc0b2660492f01c968164ac0b24e03925024918121bc0b0d6058670243181617c0b0b60585702c2980a13c0909604847014218160fc030760183702c198120bc0b05a0582b02c13816094090460581f02c0d81605c0b02601d6f00eb70075b4098de04c6b0363481319c098c604c610262f813174098b605c590262b81b154098a604c51025b780adac096ce02b63025af812d74056b602b59025ab812d54056a602b51025a780ad2c0968e02b4300d378069b4034d601a6700d3280698c034be01a5d00d2d806964034ae01a5500d298069440349e01a4b00d2380690c0347e01a3b00d1b8068cc092de0496b024b381258c092be0395d024ad81255c072aa04953034a781a52c0d28e069430149f8124ec0926e0293300c978064ac0324e01923024378121ac090ce048630242f812174090b60485705c2a81214c0d09e0584b0342381610c0507e0483b0241b80a0cc0305e0182b00c1380608c1903e0581b0600b81604c0dade06d6b036b381b58c178de04c6e03e3581f1a80f8ce07c6605e318131880b8be05c5e02e2b81714c0b8a406b6f015b581ad9c056c606b5f015ad81ad5c056a606b4f025a680ad2c0569206b47025a280ad0c0568201a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d2680692c0348e01a4500d1f8068ec0346e01a33be0b781e59c0d2be0695705ca780e5341728e039450149f81a4dc0325e0192702c3781619c0b0be0685e02c2b8161480309e0184e00c2680a0fc0b06e0182f00c1500609c0304c0581a05c0b01b5bc0dad606d67036b18071bf308dc01c6b00e3500719c0f8cc01c6300e3100717c0b8bc01c5d035b780adac0d6ce02b63035af80ad6c0d6ae02b5300da7806d340369602b4900da381ad140368601b4100d378069ac034ce01a6300d2d81a968034b201a5700d2b00694c034a201a4700d230069140347e01a3b00d1b8068cef62df7516bb48b3d8058c0d2be0695b034ab81a54c0329e0194d00ca580651c0728a019430149f81a4ec0d26e0293300c978064ac0324e01923558378161ad460ce058630342f81616c0d0ae0585300c278061340309601847cb82280610c0507e0583b0341b80a0cc0305e0182b00c1380608c4803e0581b0580b81604c05ade02d6d026b58135a405ace02d65016b180b584038de01c6e00e368131ac098d206c6700e3281b18c0d8c404c610263001317c0d8b606c570262980adbc056da02b6b015b480ad9c056ca02b63015b080ad7c0f6bc02b5b015ab80ad4c056a402b4f015a580ad1c0568601a6f00d368169ac0b4d201a6700d3281698c0b4c201a5f02d2d80695c094a601a4f00d2680a92c0348e01a4502d218068fc0547601a370151983e5bc072da0f96b07cb380e5941f2c60495f03cad81e55c092a60694f034a581a51c0d2860293f0149d80a4dc052660592f00c9580649c0b2460586f02c368161ac0b0ce0586502c3181217c0b0b6058570242981613c0b0960584702c2180a0fc0507a0283b0141b8160d4050660582f00c1580609c0b0460581f02c0d81605c0b02602e7f0173f00b9f40dafe07d7e036be8235f009af606d79026bb81b5d40dae606d72036b881b5c009ade06d6b036b381358c058fe07c7e0163e80b1bc0f8dc02c6b0163480b18c058c402c610162f80b16c058ae02c5300dbf806df4096f605b7900dbb806dd40b6e605b7100db7816dac036ce04b6300daf81ad78036ba01b5700daa816d4c0b6a401b4f015a5806d1c0568605a7f03d3f0169f72a4f804a7b0253d0169e4094f004a770253b0169d4094e805a7302d390169c40b4e004a6f025370169ac0b4d405a6703d3301298c094c401a5700d2b0069540549e02a4e0152580a9280548e02a460152180a9080b47e05a3e02d1e81e5fc072fa0497b024bb80e5d40f2e60496f03cb581e59c092c60695f034ad81a55c0d2a60294f014a580a51c052860593f00c9d8064dc0b2660592f01c968164ac0b24e0392502c918161fc0b0fa0487b0243b8161d40b0e60486f02c3581619c090c60585f02c2d81615c0b0a60284f0142680a12c0508e05845014218160fc030760183702c198160bc0b05a0582b02c138160940b0460581f02c0d81605c0b02604d6f026b70135b4098de04c6d0263581319c118ca04c6300e2f807174098b606c590262b807154098a604c51025b780adac096ce02b63025af812d74056b602b59025ab812d54056a602b51025a780ad2c0968e02b4300d378129ac0b4d201a6702531812984034be01a5d0252d816964034ae01a55025298129440349e05a4b00d2381690c0347e04a3b00d1b80a8cc092de0496b024b381258c092be0395d024ad81255c072aa04953034a782252c1128e069430149f8124ec0926e0293302c978064ac0324e05923024378121ac090ce048630242f812174090b60485702c2a81214c0b09e0584b02c2381610c0507e0483b0241b80a0cc0b05e0182b00c1381608c0b03e0581b02c0b81604c09ade04d6b026b381358c098de04c6e026358131a8098ce04c6602631813188058be02c5e0162d807168038ae01c560162980b148056de04b6e015b580ad9c056c602b62015af80ad6c056b402b57025ab00ad4c0569e04b4e015a68069bc094d601a670253180697c054b601a5702d2980693c0349a04a4b0252480691c0348a02a43015208068fc0547604a3900d1b80a8cc054620496f024b581259c092c60695f034ad81a55c0d2a60494f01ca681252c0928e03945024a180a4fc0527a0293b0149b8124d4052660592f00c9580649c0b2460486f0243581219c090c60585f02c2d81615c0b0a60484f02c2681212c0908e048450242180a0fc0507a0283b0141b8120d4050660582f00c1580609c0b0460581f02c0d81605c0b02608d6f036b582359c0dac60ac6f01635e5119c058c606c5f0162d81b15c058a601b6f02db5806d9c0b6c601b5f035af006d74036ae01b5502da9816d480369e05b4b00da380ad0c0b4df9326e02d358169a80b4ce07a6602d31816988034ae01a5600d2a80a93c0549c05a4b02d2501691f2448c02a43015210168fc0b47c05a3d054b7dcc5aece2ce0a963034af82256c112ae06953014a7c8852e3228e0294302c9f8064ec0326e0593302c9780e4b40b2560592701c9281648c0b0de0586b02c3381618c0b0be0585b02c2b81614c0509e0584b02c2380a10c0b07e0183b00c1b8160cc0b05e0582d02c1581609c0b04a0582302c0f81606c0b02e05813026b78135b409ad604d67046b281358c038de01c6e00e3681317c0d8bc04c5b0262d01315c0b8ac04c5302629012dbc056d604b67015b1812d7c056b604b57015a9812d3c0969a02b4b015a4812d1c0968a02b43015a08069bc034da01a6b00d33806994034c601a5f00d2d80695c034a601a4f00d2680692c0349201a4700d2280690c0348201a3f00d1d8068dc034660496f024b5dc85a4092ce04963024b081a57c112b608957034a981253c0729a0494b024a380e514092860293f0249d8124dc052660192f00c9580649c032460486f0243581219c090c60685f02c2d82215c0b0a60484f0242681212c0908e0b8450242180a0fc0907604837014198060bc030560182700c1188c07c0b0360a01702c0981b5802d2b003954036b005a950072b80294c024a20164f00326804d6f036b581b59c09ac601c6f00e3700b1ac058d401c6700e3300718c038c404c5f0262f01716c0b8b405c590362b8171580d8a604c5203628813140056de07b6e015b5806d9c056c602b62015af80ad6c056ae02b53015a780ad340369601b4900da3806d140368601b4100d378069ac034ce01a6300d2f80696c034b201a5700d298069440349e01a4d00d258069240348e01a4500d218069040347e01a3b00d1b8068cc092de0796b03cb381258c0d2be0695b034ab81a54f1e29e0394d0b4a585a51c0728b8e1430149f80a4ec0526e0293300c978064ac0324e01923024378161ac0f0ce048630342f81616c0d0ae0585303c2781e1340b0960784703c2281610c0507e0283d0141d80a0dc0f06a0283300c178060ac0304e0182303c0f81606c0f02e058130173f80b9f805cfa01d7f00ebf0075f403af801d7b026bd0075e409af001d7700ebb0075d403ae801d7303eb90075c71aae001d6f00eb70075ac0fad401d6700eb300758c09ac406c7f03e3f01b1f4118f804c7b0363c8131dc0d8ea06c730363901b1c40d8e004c6f0363581b19c098c601c5f00e2f017174056fe07b7e015be80adbc0f6dc02b6b015b480ad8c056c402b6100daf80ad74036b601b5900dab806d54036a602b51015a780ad2c0568e02b4300d3f8069f4034f601a7900d3b8069d4034e601a7100d378069ac034ce01a6300d2f806978034ba01a4f00d2700692c0349201a43035210069040347e01a3b00d1b8068cc0f2fe0397d024bd8125dc072ea07973024b781e5ac0f2ce0496300caf80e574032b60195700caa80654c0d29e0694b034a381a50c0527e0293b0149b80a4cc0325e0192b00c9380648c0f0fe0787d0243d8121dc0f0ea05873024378161ac0f0ce0486300c2f81e174030b60185700c2a80614c0d09e0584b0342381610c0507e0283d0141d80a0dc0f06a0283300c178060ac0304e0182303c0f81606c0f02e05813026b78135ac09ace04d63026378131b8098d604c6a02633813198098c604c620162f80b178098b604c5a0162b80b158058a602c52015b7812db8056d602b67015b180ad88056be02b5b015ad00ad5c096ac02b5300da3806d180368a01a6f00d3580699c034c601a5f00d2d80695c034a601a4f00d2680692c0349201a4700d2280690c0348201a3f00d1e8068ec0346e01a3500d198125bc092d604967024b181a57c0d2b606957034a981253c0729a0494b024a380e514092860293f0149d8124e40526e02933014988064bc032560192700c918121bc090d6048670243181a17c0b0b60685702c2981213c0909a0484b02423822114090860283f0141e80a0ec0506e04835014198060bc030560182700c1183a07c0b0360e81702c0982b5bc09adc07d6b03eb501f59c0facc0ad63026b10231bc0d8d607c670363181717c0b8ba05c5702e2a81714c156de02b6b03db380ad8c176be04b5d015ad80ad64176ae04b55015a980ad440d69e02b4b035a380ad0c034de01a6b00d3380698c034be01a5d00d2b806954034a601a4f00d2580691c0348601a3f00d1d8068dc034660a96f03cb382e57c072ba0b95701caa81a53c1128e0293f0749b8064bc0324e0586f0543701619c0b0c40185700c2b0061540b09e0584a02c238221180507e0583a02c1b82e0d80305e0182a00c138060981703c0581200eb78075b803ad607d6a00eb380759803ac7905620463781b1ac118ce06c6300e2f8071780b8ba0ab6f015b5e30d9c056c601b5fc59ae806d6c036b201b5700daa806d4c056a206b4f015a581ad1c0568601a6f00d3580699c034c601a5f00d2f0069740349e01a4e00d258069240348606a4200d208068fc0347601a3700d1982a5bee02d765167054b180657c072ba0195b00cab806554032a60694f044a582251c0d2860293f9009dc5c4dc052660192f00c9580649c032460a86f02c35a8019c0b0c60185fc502e80616c030ae0185500c2981a13c0b0960884702c2180a0fc0b0766d037014198060bc030560182700c1188407c0b0360901702c098135bc09adc04d6d026378131ac0d8d204c6702631813184098be04c5d0262d807164098ae06c5500e29807144096de04b6d015b5812d9c096ca02b63025af812d74056b602b59025ab812d54056a602b51025a780ad2c0968e02b4300d378129ac0b4d201a6702531812984034be01a5d0252d816964034ae01a55025298129440349e05a4b00d2381690c0347e04a3b00d1b80a8cc092de0496b024b381258c092be0395d024ad81255c072aa04953034a781a52c0d28e069430149f8124ec0926e0293302c978064ac0324e05923024378121ac090ce048630242f812174090b60485702c2a81214c0b09e0584b02c2381610c0507e0483b0241b80a0cc0b05e0182b00c1381608c0b03e0581b02c0b81604c0dade06d6b036b381b58c0d8de02c6b0363380b18c0d8be02c5b0362b80b14c036de05b6b00db3816d8c036be01b5d02dad816d68036ae06b5600daa806d3c0b69601b47015a18169bf104dc05a6b02d3501699c0f4cc05a6302d3100697c034bc01a5d0152780a9380b49605a4a02d2381a9180548602a4202d1f8168f80b47b7916fb70b5d8c59ebc2c60695f034ad81a55c0d2a60294f034a581a51c052860593f00c9d8064dc0b2660592f01c968164ac0b24e0392502c918161bc0b0d60586702c3181617c0b0b60585702c2980a13c0b09605847014218160fc030760183702c198160bc0b05a0582b02c138160940b0460581f02c0d81605c0b02604d6f026b70135b4098de04c6b0263381318c098be04c5d0262d81b164098ae08c5502629813144056de02b6d015b580ad9c056ca02b6300daf806d74056b602b59015ab806d54056a602b51015a780ad2c0568e02b4300d378129ac0b4d201a6702531812984034be01a5d0152d80a964034ae01a550152980a9440349e05a4b00d2381690c0347e02a3b00d1b80a8cc092de0496b024b381258c092be0395d024ad81255c072aa04953034a782a52c1528e069430149f80a4ec0526e0293302c978064ac0324e05923024378121ac090ce048630242f812174090b60485702c2a81214c0b09e0584b02c2381610c0507e0283b0141b80a0cc0b05e0182b00c1381608c0b03e0581b02c0b81604c09ade04d6e046b581f5a811ace07d66026b1813588098de04c6e0363581b19c098c604c620262f813178098ba02b6f015b580ad9c056c602b5f00dae80ad6c056b201b5700daa80ad4c056a202b4f015a680ad2c0568e02b45015a18069bc0b4d601a670253180697c034ba02a5b0152c80695c034aa02a530152880693c0b49605a4900d2381690c0b48201a3f0151d8068dc054660496f04cb582659c092c60895f01cae82256c112ae03955044a981a53c0d29a0694b034a38225140d2860293f0149d80a4dc052660592f00c9580649c0b2460486f02c3581619c090c60585f02c2e81616c0b0ae0585502c2981613c0b09a0584b02c238161140b0860283f0141d80a0dc050660582f00c1580609c0b0460581f02c0d81605c0b02604d6f036b582759c09ac602c6f0163580b19c058c602c5f0162d80b15c058a601b6f02db5806d9c096c601b5f02dad806d5c0b6a601b4f015a7006d340368e01b45015a180ad08094df8626e025358169a8094ce07a66025318169880b4be06a5e0252d8169680b4af85256025298169480348e01a4600d2280a8fc0547c02a3d024b78265ac132ce04963034afd1456e662ae06953014a780a52c0528e0294302c9f8064ec0326e059330249780e4b40b2560592701c9281248c090de0586b02c3381218c0b0be0585b02c2b81614c0509e0284b0142380a10c0b07e0183b00c1b8160cc0905e0582d02c1581609c0b04a0482302c0f81606c0b02e05813026b78135ac09ace04d630163780b1b4058d602c670163280b18c058be02c5b0162b80b14c036de01b6e00db6812d7c0d6bc04b5b025ad012d5c116ac04b53025a900ad3c0569c02b4b015a500ad1c0568c02b43015a10069bc034da01a6b00d33806994034c601a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1e8068ec0347201a3700d1a8068cc034620496f024b581259c092c60695f054ad82a55c0d2a60294f014a580a51c052860493f01c9e8124ec0926e03935024998064bc032560192700c918121bc090d6048670243181a17c0b0b60a85702c2980a13c0509602847014218120fc0907a0483b0241b82e0d4090660182f00c1580609c030462001f02c0d82005c0b02604d6f026b701b5ac0dace04d63026b100b1bc058d602c670163180b17c058ba02c5b0162b80b154058a604b6f025b7022dac0f6d408b6703db3012d8c096c401b5700dab006d540569e02b4e015a580ad280568e02b46015a180ad08034de01a6b00d3380698c034be01a5d00d2d80695c034aa01a5300d2780692c0348e01a4300d1f8068f40347601a3900d1b8068d40346601a31024b78265ac132ce04963034af81a56c0d2ae06953014a780a52c0528e029430449f80e4f4112760893701c9a8224cc0325e0192b00c9380648c090de0586b04c3381218c0d0be0585b0342b81614c0509e0284b0142380a10c1107e0883d02c1d8220dc1706a0583300c178060ac0304e018230640f81606c1b02e05813026b781b5ac0face04d63026378131b80f8d607c6a03e3381f198098c604c620362f81b178178b608c5a05e2b8231580d8a606c52015b780adac056ce02b63015af80ad6c056ae02b53015a780ad340568e02b45015a18069bc034d601a6700d3180697c034b601a5700d2980693c0349a01a4700d2280690c0347e01a3b00d1b8068cc092de07967034afcc455c1729e0394d05ca380e5140527e0293700c9780649c090de0486e02c338121880b0be0585700c238061180308a0283f0141d00a0dc0506c0182f00c1500609c0304c04d6f036b582759c09ac601c6f00e370071ac0f8d401c6700e3300718f068c401c5f00e2f00716f048b401c5700e2b00714c0d8a402b6f015b580ad9c056c602b5f015ad80ad5c056a601b4f00da700ad34034de01a6b00d3380698c034be01a5b00d2b80694c0349e01a4e00d268068fc0347c01a3b00d1c8068cc0546401a31024b78265ac132ce04963034afd0c56e602ae0695300ca780e534032960194700ca280650c0527e0293b0149b80a4cc0325e0192b00c9380648c090de0586b04c3381218c0d0be0585b4002b81614c0309f8104d00c2580611c0308a018430141f80a0ec0506e0283300c178060ac0304e018230f00f81606c0e02e05813036b781b5b40face06d65026b180f1bc078dc03c6d0262f8131780d8b607c5702629813148096de04b6d015b580ada4096ce04b65015b180ad84096be02b5b025ab80ad4c0969e02b4b025a380ad0c114de01a6d045358169a4114ce01a6504531816984094be07a5b03d2b81294c0d49e08a4b0452381a90c0547e04a3b0251b80a8cc072de0396d01cb380e594072be0395701ca780e5340728e039450149f80e4dc0725e039270443782e1b4110ce088650242f81e15c0d09e088470141f8120dc1905e14827 20 1048575 8 255 11 2047 21 2097151
def cc_54_13 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0198ac041a4c749d6769874f924638c3618873c822657bf6376c53709636a66362f775ce6156d6154e1f506484ca3c48a40423673ba693596130c4d2a76524a5d1e96118267119690ca4f0696100069 0x1e7f00f3f0079ec09cf401e7700f3b0079cc09ce404d7f026bf0135f403ade01d6e026b68175b0098f604c7a0363c8131dc098ec04c73026388071bc0f8da01c6b00e3480719c038ca01c6302e3081315c098ac07c55025bf80adec096ee02b7300db7812db4036d601b6900db3806d94036c602b61025af812d74056b602b59025ab812d54056a602b51025a780ad2c0569204b47015a180ad04034fe01a7e00d3d8069dc034e604a7200d378069b8034da01a5f00d2f006974034b801a5b00d2c80694c094a401a510252800693c0349608a4a00d238069180348601a3f00d1d8068dc034660497f024bd8125dc092e60196f01cb68065ac032ce0196500cb181257c092ba0495b064ac81255c192aa04953024a881a53c1129608947034a180a4fc0927604937014998064bc032560192700c918121fc090f604877024398061bc190da0186b00c33806194030c60485f0242e81216c0b0b2048570a42a81214c090a20684f02c2582211c0b0860283f0241d8120dc050660182f00c1580609c030460c81f02c0d83205c0b02604e7f0273f0139f409af604d7a036bc8135dc09aec04d73026b881359c09acc07d650263f80b1ec098ee02c73026378131b4058d602c6902633813194058c602c610262f80b16c058b204c570162980b144096fe04b7b025bb812dcc096de04b6d025b5832da4096ce0cb65025b1812d840d6be08b5b045ab81ad4c0569e04b4b025a380ad0c094fc04a6e02536022958092fc0397601cb300e590072bc07956014a70125180b27c0193601f3f80f9f807cee03e7601f398139c809afe04d7e026be8131ec098f406c790263b8131d8098e604c7101e3781f1b4078d603c6901e3380f194098ae04c5603e2a812dfc056f604b77015b980edbc096da02b6b015b480ed9c076ca02b63015b0812d7c096ba02b5b015ac812d5c096aa02b53015a8812d3c0569602b49025a380ad0c0568204a7f0253d8129dc094e603a6f00d3680e9ac074d203a6700d3280e98c0b4c204a5f0252e81296c194b204a570652a81294c094a206a4f0452582291c0d48602a3f0251d8128dc054660397f01cbf00e5dc092e40396f01cb700e5b4072be0395e01cae80e570092a40495001ca78225280728e039460149f80e4dc0725e039270243f8121dc070de0c86d01c3380e194090be0485d0242b8361540d09e088470141f8120dc1905e0c8270273f8139f809cee04e76027398139c809afe04d7e026be8131ec098f406c790263b8131d8098e604c7103e3781f1b40d8d606c6903e3381f194098ae04c5603e2a812dfc056f604b77015b9812dbc096da02b6b015b4812d9c096ca02b63015b0812d7c096ba02b5b015ac812d5c096aa02b53015a8812d3c0569602b49025a380ad0c0568204a7f0253d8129dc094e60da6f00d368169ac0b4d20ba6700d3281698c0b4c204a5f0252e81296c0b4b204a570a52a81294c094a206a4f02d2582291c0b48602a3f0251d8128dc054660497f024bb8365bc072da0b96701cb281257c092ba0495706caa81a53c1128e0293f0249b8164bc1924e0487f0243f0121dc090e40486f024370121b4090be0485e0242e812170090a4048500342781e1280f08e088460141f8120e80906e0483602c1781609c09ade04d6e03eb381358c09ac404c6f0363581f19c098c607c5f03e2e81b16c0f8ae07c55025b780adac096ce02b63025af812d74056b602b59025ab812d54056a602b51025a780ad2c0968e02b43025378169ac0f4ce04a6305d2f8069740b4b605a5905d2b8069540b4a605a510352781692c1148e05a430151f8128ec0946e02a33024b781e59c172be0395d05cab80e5540d29e089470149f8124dc0b25ee7127024378121b80f0ce048620242f812178090ba0684f03c2501e11c1108c0283f0241d0120dc0906c0582f02c138135bc0dadc06d6d0363581f1a80d8d207c6703e3301318c0d8c207c5703e2b01f154096de02b6b025b380ad8c096bfa535d015ad80ad64096afc0355015a980ad440969e02b4b015a4812d1c0568602b410253781e9ac0f4ce04a630252f8069777e4b605a59df12b806954094a605a510352782292c1148e06a430151f8128ec0946e02a33024b781e5ac0f2ce04963024af80e5777a2b7bc15701caa81254c0d29e0894b044a381a50c0527e0493b0249b80a4ce2425efd12b73093b3848c090de0786b03c3381218c090be8505d03c2deec15f740aa048530342781e12c1108e068430141f8120ec0906e028332e81781e0ac8404e078231700f81e06c2602e07813036b781f5b80dada06d67036b281b58c0dac406c6703e3301b1940d8be06c5e0362e81adbc056d606b67015b181ad7c056b606b57015a981ad3c0d69a02b4b015a481ad1c0d68a02b43015a081e9bc0f4d607a6703d3181a97c0d4b606a570352981a93c0349a06a4b02d2481a91c0348a06a4302d2080a8fc0d47606a370151981e5bc0f2d60796703cb181a57c0d2b606957034a981a53c0729a0694b034a380e5140d2860293f0349d81a4dc052671112f7e095b9449d9a2460786f03c3581e19c0f0c60685f0342d81a15c0d0a60684f0342681a12c0d08e078450342180a0fc0d076068370141981e0bc0f0560782703c1181e07c0f0360781703c0981317c058b604c5702629812d7c056b608b57025a9812d3c0d69607b47025a181297c114b608a570252981293c0f49607a470252181a8fc1147608a370351981257c112b608957024a981253c0f29607947024a181a4fc112760893703499c404bdf6256e41276609181217c0f0b6078570242981213c0f096078470242181a0fc0f076078370341981e0bc0f0560782703c1181e07c0f0360781703c0981b5bc0dadc06d6d03e3781f1bb6a8da07c5f03e2f01b16c0d8b206c5303e2901b1440f6de07b6e04db6edcdb0056d602b6903db381ed94056c607b62015b080ad800f6be02b5b03dab80ad4c0d69e02b4b035a380ad0c0f4de01a6d03d358169a40f4ce01a6503d318169840f4be07a5b03d2b81e94c0d49e08a4b0452381a90c0547e09a3b04d1b80a8cc0f2de0396d03cb581e59c072ca0796303caf81e56c0f2ae07953034a782252c1128e069430149f8264ec1326e0293387097be44adc424eca12303c3781e1b40f0d60786703c3281e18c0f0be0785b03c2b81e14c0d09e0784b03c2381a10c0507e0783b03c1b80a0cc0f05e0782b03c1381e08c0f03e0781b03c0b81e04c09ade04d6e026b68131ac098d406c6902633813198098c604c610262b8131580d8aa04b6f015b5812d9c056c604b5f025ae80ad6c056b204b57025aa80ad4c056a204b4f015a580ad240968e02b43015a08129bc094d604a670253181297c034ba04a5b02d2c81295c034aa04a530252881a93c0d49606a470352180a8fc0947604a37015198125bc092d604967024b181257c072ba0495b024ab80e554092a60694f034a581a51c0d2860293f0249d8124dc052660c92f0649583249c192460486f0243581219c090c60485f0242e81216c090ae078550242981a13c0d096068470342180a0fc09076048370141981e0bc0f0560782703c1181e07c0f0360781703c098135bc0dad606d67026b18131bc098dc07c67026318131880d8be06c5e0362b81b14c0d8a404b6f015b5812d9c056c604b5f015ad812d5c056a604b4f025a680ad2c0569204b47025a280ad0c0568204a6f02d3581e99c094c606a5f02d2d81a95c0b4a60ba4f00d2681692c0b4920ba4700d2281690c0b48202a3f0251d8128dc054660496f03cb381a57c0d2ae0b94f01ca682e51c0728a0293f0249b8164bdc024e0486f0243701e19c090c40685f0342f01a15c0d0a40484f024270121340507e0483a0241b8120d80b05e0782a02c1382e0980f0340b816026b781b5b40dad606d6a036b381f5980daca04c6fdaa3701b1b40d8be06c5e0362e812dbc056d604b67015b1812d7c056b602b59025ab80ad4c056a204b4f035a680ad2c0569204b47035a280ad0c0568204a6f03d3581e99c094c606a5f0352d81a95c0d4a604a4f00d2681a92c0b49206a4700d2281290c0b48202a3f0251d8128dc054660496f03cb581e59c092c60695f034ad81a55c0d2a60494f01ca681a52c0d28e03945024a180a4fc092760493701499c304bdee256df127640918121bc0f0d6078670243181a17c0d0b6068570342981213c0d09a0684b03423ed0114090860283f0241d8120dc050665b02f03c1590409c0f0462c01f03c0d84805c0f02602d6f016b700b5b4098de06c6b03e3381318c098bfa545d0362d81b164138ae09c550262981b144056d602b6a015b480ad9c0f6cc02b63015b080ad5c0f6ac02b55015a7ea0d380569602b47015a180ad08094de07a6b03d3381298c094be01a5d04d2d816964134ae01a55025298169440d49e0aa4b0552381a90c0547e02a3b0151b80a8cc092de0796b03cb381258c092be0395d04cad82655c072aa04953034a782a52c1528e069430149f80a4ec0526e0293385897bd84adbc24ec71230243781e1ac0f0ce048630242f9d01740f0b60985704c2a81214c0d09e0784b0542381a10c0507e0283b0141b80a0ccb405e0782b2001381e08c5603e0781b0880b81e04c09ade04d6e016b580b5a805ace02d66016b180b588058de02c6e0363581b1a80d8ce07c6602631813188098ae04c560262a80adbc056d602b67015b180ad7c056ba02b5b015ac80ad5c056aa02b53015a880ad3c0569a02b4b015a480ad1c0568a02b43015a08129bc0f4d607a670253182297c034ba08a5b02d2c82295c034aa08a5302d2881a93c0d49a06a4b0452481a91c1148a06a430352080a8fc0547602a37015198125bc0f2d607967024b182257c072ba0895b044ab80e554112a60694f034a681a52c1129206947044a281a50c0d2820293f0149d80a4dc052660c92f0649583249c192460486f03c3581e19c090c60785f03c2e81e16c0f0ae0785503c2981a13c0d09a0684b03c2481a11c0f08a068430342080a0fc05076028370141981e0bc0f0560782703c1181e07c0f0360781703c098135bc05ad602d67016b180b1bc058d602c670163180b17c058b602c5701629806dbc0b6d601b67025b1806d7c116bc01b5d00dab806d540b6a605b5200da780ad2c0368e02b43025378129b80b4d605a6a02d3381e998094c604a6200d2b806958034aa02a4f0152700a92c0549402a470152300a90c0548405a3f02d1f0168f4092de0796b03cb381258c112be0895b044ab82254c0529e0294b014a380a50c0b27e0193b00c9b8164cc0b25e0392d02c9581649c0724a05923024378161ac0b0ce0486302c2f81616c0b0ae058530142780a12c0508e0284302c1f8060ec0306e0583302c178160b40b0560582702c1281608c0b03e0581b02c0b81604c03ade01d6e00eb581f5a803ace01d6600eb1813588098de02c6b0163380b18c038be01c5e02e2e80adbc056d601b67015b1806d7c056ba01b5b00dac806d5c036aa01b53015a880ad3c0569602b47015a18069bc034d601a6700d3180697c034bc01a5d00d278069380349601a4900d218229080348201a3f00d1d8068dc034660496f03cb581e59c092c60195f01cae80656c032ae0195500ca982253c1129608947044a180a4fc0527602937014998064bc032560192700c918121bc0b0d6078670243180617c0f0ba0185b00c2b806154030a60784f02c2581e11c0b0860283f0141d80a0dc050660182f00c1580609c030460781f02c0d81e05c0b02604d6f016b580b59c05ac602c6f0163580b18c058be02c5b0162b80b14c096de07b6b03db3812d8c116be08b5b045ab822d4c0569e02b4b015a380ad0c114bc0496e03cb300e5580529c0294602c9f0064d807ade03d6e01eb581f5a807ace03d6601eb1813588098de02c6b0163380b18c056de02b6b015b380ad8c056be02b5d015ad80ad64056ae02b55015a980ad440569e02b4b015a380ad0c094de07a6b03d3381298c074be01a5d01d2d80e964074ae01a5501d298169441149e08a4b0452382290c0547e02a3b0151b80a8cc072de0396701caf80e578072ba0394f01ca70225080527e0293701c9780e49c090de0786701c2f81e174070ae0385503c2781e11c0507e0283703c1781e09c098be02c5b0162b80b14c056be02b5b015ab80ad4c0569e02b4b015a380ad0c094be07a5b03d2b81294c1149fb024bd792382290c0547e02a3b0151b80a8cc092be0795b03cab81254c1129fae14bd68a382250c0527e0293b0149b80a4ce1425ef512b6e893b1848c090be0785b03c2b81214c0f09e0784b03c2381e10c0507e0283b0141b80a0cc0f05e0782b03c1381e08c0f03e0781b03c0b81e04c098be02c5b0162b80b14c056be07b5e015ad80ad5c056a602b52015a780ad2c0568e02b430252f81e96c0f4ae04a530352781a92c0d48e06a430151f80a8ec0546e02a33024af81e56c0f2ae04953034a781a52c0d28e069430149f80a4ec0526e0293384897bd04adb824ec51230242f81e16c0f0ae048530342781a12c0d08e068430141f80a0f4050760283703c1a80a0cc0f05e0782b03c1381e08c0f03e0781b03c0b81e04c05ade02d6e016b681f1bc0f8ddb146dd62360131ac0d8d204c6703e3281b18c0f8c406c61d5a3001317c0d8b607c570262980adbc0f6dc02b6d015af81ed78056b602b59015a980ad48056a202b4f015a580ad1c0568607a6f00d368129ac0b4d204a6700d3281e98c0b4c204a5f03d2d81e95c094a606a4fca125e3091c0d48602a3f0151d80a8dc054660796f01cb68125ac092ce0396503cb181257c0f2b607957024a981a53e962973b147034a180a4fc052760293701499c1c4bde4256da1276189181e1bc0f0da0486b0243381e1940f0c60485f03c2d81e15c090a60684f03c2581e11c0d0860283f0141e80a0ec0506e078350141981e0bc0f0560782703c1181e07c0f0360781703c098135bc09adc04d6d016378131ac0d8d204c6702631813184058be02c5d0162d80b164098ae06c550162980b144056de02b6d015b580ad9c056ca02b63015af80ad74056b602b59015ab80ad54056a602b51015a780ad2c0569202b47015a180ad04094de04a6b0253381298c094be01a5d0252d816964094ae01a55025298129440d49e06a4b0352381a90c0547e02a3b0151b80a8cc092de0496b024b381258c092be0395d024ad81255c072aa04953034a781a52c0d28e069430149f80a4ec0526e0293383097bc44adb224ec2123024378121ac090ce048630242f812174090b60485705c2a81214c0d09e0684b0342381a10c0507e0283b0141b80a0ccb205e0782b1f81381e08c5403e0781b0800b81e04c05ade02d6e016b68131bc098d604c670263181317c098ba04c5b0262d01315c098ac06c5502629812dbc096da04b6b025b5012d9c096cc04b65025b1812d7c096ba04b5b025ad012d5c096ac04b5503daa012d4c0569e02b4e015a68129bc094d604a670253181297c094b604a570252981a93c0d49606a47035218128fc0947604a37025198125bc092d604967024b181257c092b604957024a981a53c0d29606947034a18124fc09276049370249983e4bde0256d812707c918121bc090d6048670243181217c090ba0485b0242b826154090a60684f0342581a11c0d0860483f0241d8120dc090660e82f03c1583a09c0f0460e81f03c0d83a05c0f02604d6f036b581b59c09ac604c6f0263701f1ac0f8d407c6703e3301318c098c402c5f0162f00b15c058a602c52015b780adac056ce02b63015af80ad6c056ae02b53015a780ad340569602b47015a28129bc0b4d607a670253181a97c0b4b606a5702d2982293c0349a05a4b02d2482291c0348a05a4302d2080a8fc0547602a37015198125bc0f2ce0695f034ab82253c0729a0894701ca280a4fc0526e0592f6b8938121bc0f0ce0685f0342f00a15c0d0a40484f024270121340507e0283a0141b80a0d80b05e05827026b781b5ac0dace04d6302637ea51b8098d606c6a0263381f198098c606c620162f80b178058ba02b6fd41b700adac056ce02b63015b100ad6c056b402b59015ab81ad58056a602b51015a381ad180568a04a6f04d3582699c094c606a5f0352d81a95c0d4a604a4f00d2681a92c0b49206a4700d2281290c0b48202a3f0151d80a8dc054660496f04cb582659c092c60695f034ad81a55c0d2a60494f01ca681a52c0d28e03945024a180a4fc052760293701499c144bdde256d6127608918121bc130d6098670243181a17c0d0b6068570342981213c0d09a0684b03423e9c114090860283f0141e80a0ec0506e6f035014199600bc8e0563e0271a0118a407c300360f017028098135bc09adc04d6d016378131ac098ce04c630262b8131580d8aa02b6f015b580ad9c056c602b57025ab00ad540569e04b4e015a580ad240568e02b43015a100ad04094de04a6b0253381298c094be01a5d0252d816964094ae01a55025298129440d49e06a4b0352381a90c0547e02a3b0151b80a8cc092de0496b024b381258c092be0395d024ad81255c072aa04953034a781a52c0d28e069430149f80a4ec0526e02933064978324ac1924e0c923024378121ac090ce048630242f812174090b60485705c2a81214c0d09e0684b0342381a10c0507e0283b0141b80a0cc1905e0782b0741381e08c1903e0781b06c0b81e04c09adfa556e026b581b5a809ace07d66026b181b588098de06c6b0363381318c058be02c5e0162e80adbc056d602b67015b180ad7c0d6bc02b5d015a781ad380569602b49015a180ad080568204a6f04d3582699c094c606a5f00d2e81296c0b4b204a5700d2a81a94c0b4a206a4f0352581a91c0d48602a3f0151d80a8dc054660496f04cb582659c092c60695f01cae81256c092ae03955034a981a53c0d29606947034a180a4fc052760293701499c104bddc256d5127600918121bc130d6098670243181a17c0d0ba0485b0242b9c01540d0a60684f0342581a11c0d0860283f0141d80a0dc050665702f230158f409c660462801f0b80d83805c0802606d6f036b68135ac09ad207d67036b281358c09ac201c6f00e370071b4098be04c5e0362d81f15c098a604c52025b7812db4056d602b69025b3812d94056c602b61025af80ad6c096ae02b53025a780ad2c0968e02b4300d378069b4034d601a6900d33806994034c601a6100d2f80696c034ae01a5300d278069340349601a4700d2280690c0347e01a3b00d1b8068cc112de0396d044b582259c072ca08963024af81e56c0f2ae04953034a782252c1128e069430149f8124ec0926e0293300c978064ac0324e019230443782e1b40b0d6088670443281618c090be0585b03c2b81214c0d09e0584b0442381610c0507e0483b0241b80a0cc0305e0182b00c1380608c1903e0581b06c0b81604c05ade02d6d026b58135a405ace02d65016b180b584098de08c6d026358131a4098ce04c650263181b184098be04c5b0262b81314c036de01b6e00db680ad7c096bc02b5b015ab80ad4c056a402b4f015a580ad1c0568601a6f00d368069ac034d201a6700d3280698c034c201a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1e8068ec0346e01a3500d198125bc072da0496b024b380e594092c60495f024ad81255c092a60694f054a582a51c0d2860293f0149d80a4dc052660192f00c9580649c032460486f05c368121ac090ce048650243181217c090b6048570242981a13c0b0960a84702c2180a0fc0507a0283b0141b8120d4050660182f00c1580609c030460e81f02c0d83a05c0b02604d6f026b701759c09ac604d620263781f1ac0f8ce04c630562f823174178b606c590562b823154178a606c51025b780adac096ce02b63025af812d74056b602b59025ab812d54056a602b51025a780ad2c0968e02b4300d378069ac034ce01a6300d2f806974034b601a5700d2a80693c0349601a4700d218068fc0347601a3700d198125bc0f2ce0b95f01cae82e55c072aa1194f054a380a4fc0926e0192f00c938121bc090dc058670243100617c030bc0185d02c2781611c0507e0483a0241b8120d80305e0182a00c1380609803ade05d6e00eb68131bc0f8d607c670263180717c038ba01c5b0362c80715f468aa01c5300e28812dbc056d604b67015b1806d7c036ba01b5b015ac806d5f446aa01b5300da8812d3c0569604b47015a18069ac0f4d401a6900d33806998034c601a6100d2b806958034aa01a4f00d2580691c0348601a3f00d1d8068dc034660496f03cb581e59c092c60195f00cae80656c032ae0395500ca9d5c53c152960a947960a180a4fc0927604937014998064bc032560192700c918121bc0b0d6078670243180617c030ba0185b00c2be84154030a69004f02c2582a11c0b0860283f0241d8120dc050660182f00c1580609c030462601f02c0d83405c0b02607d6f026b701f5ac03ad401d6700eb301b58c09ac407c6f0363581f1a80f8ce07c660363181717c0b8bc05c5d03db780adac0f6ce02b63045af812d74056b602b59045ab812d54056a602b51035a780ad2c0569206b47015a180ad04034de05a6b00d3381698c034be01a5d02d2d812964034ae01a5502d298169440349e05a4b02d2480691c0b48605a4100d1f8168ec0346e02a3303cb781e5ac0f2ce07963044af80e574112b60895701caa82254c0d29e0894b044a381a50c0527e0893b0449b80a4cc0b25e0192b00c9381648c0b0de0586b02c3381618c0b0be0585d02c2d81615c0b0aa0585302c2781612c0b08e058430141f8160ec0b06e0283302c178060ac0304e0582302c0f81606c0b02e05813 20 1048575 8 255 11 2047 21 2097151
def cc_54_14 : Nat → List (Nat × Nat) := unpackCursorV4 0x130dc0098 0x4d6f04d6e02d6b02d6a02d6702d6602d6302d6202c6f04c6b04c6704c6302c5f02c5e02c5d02c5c02c5b02c5904c5704c5502c5302c5202c5102b6f04b6e02b6b02b6702b6302b6202b5f04b5e02b5d02b4f02b4b02b4a02b4902b4704b4602b4302b4104a6f04a6b04a6704a6304a5f01a5d04a5b04a5904a5701a5504a5305a5106a4f06a4b06a4706a4302a3f02a3b02a3702a330496f0496b04967049630495f0395d0495b0495703955049530694f0694b06947069430293f0293b02937029330f92fff12be91270f9230486f0486b04867048630485f0885d0485b0485704855048530684f0684b06847068430283f0283d0283b0283704835028330e82f0782b0e827078230e81f0781b0e8170781304e7f04e7e04e7d04d7b04d7a06d7904d7704d7604d7304d7104d6704d6607d6504c7f02c7b04c7702c7304c6f04c6d02c6b02c6904c6704c6502c6302c6104c5f02c5b02c5904c5702c5302c5101b7f04b7e04b7b01b7704b7304b7201b6f04b6e01b6d04b6c01b6701b6504b6304b6204b6104b6001b5f05b5b05b5a01b5708b5605b5301b4f04b4b01b4702b4304a7f04a7e04a7b04a7a01a7701a7604a7304a7201a6701a6601a6501a6401a5f01a5e05a5b05a5a05a5707a5605a5305a5202a4f02a4e04a4b04a4a04a4704a4602a4302a4204a3f04a3e04a3d0497f0497b04977049730496f0496d0496b0c969049670c96504963049610695f0895b08957069530294f0494b04947029430593f0193b01937059330592f0392d0592b0592703925059230487f0487b04877048730486f0486d0486b05869048670586504863048610585f0585b05857058530284f0484b04847028430583f0183b01837058330582f0582d0582b0582705825058230581f0581b0581705813 17 131071 8 255 11 2047 20 1048575
def cur_54 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_54_14 (Nat.sub p 448)) (cc_54_13 (Nat.sub p 416)) (Nat.blt p 448)) (Bool.rec (cc_54_12 (Nat.sub p 384)) (cc_54_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 416)) (Bool.rec (Bool.rec (cc_54_10 (Nat.sub p 320)) (cc_54_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (cc_54_8 (Nat.sub p 256)) (cc_54_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 288)) (Nat.blt p 352)) (Bool.rec (Bool.rec (Bool.rec (cc_54_6 (Nat.sub p 192)) (cc_54_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_54_4 (Nat.sub p 128)) (cc_54_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_54_2 (Nat.sub p 64)) (cc_54_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_54_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def f_54 : Nat → Nat × Nat := unpackForestF 0xdd355dd25bdd257dd15bdd157dd057dd05500c5f00c5bdbb6c00c57da46eda04500c5300b5fd5c6dd6a4bd6a47d694bd6947d5c6cd5c6000b57d3c6ed3b6ed384500b4fd2d6e00b47d0c55d0b55d085500a5fcfa5600a5bcec6d00a57cd256cd24600a53cbc6ecb84500a4fcaa7cc9467c926ec924600a4bc5562c714fc7143c6d70c5367c535dc505d00a47c426e00a43c2a6ec2a5600a3bc0c62c0c5ac084d00a37bc455bc355be464be045bc24fbd264bc243bc0550095fbb154b6b5fba134b6b5bb8e70b896cb6b57b7934b6b53b69560095bb1c6db547cb1a4fb427cb1a4bb3570b1a47b227cb1a4300957b0954adb5faf934adb53aea4dad956ad94600953a746eac464a726fab254a726baa47ca7267a8a64a8a54a7263a7a6fa70450094fa617ca0c67a5134a0b6ba417ca0b67a3134a0b4ba215ca0b47a096ea09460094b97d629ea4f9ea439e57097b6797b5d9c6709c26c97a6b9b57097a679a26c97a3b98c609884d97a379785d009479696492b6f9593492b6b9497c92b679393492b639296e00943919348f35b9096c8f3578f16e8f1560093b8ac628ac5a8d25c8aa5b8c4608aa578b2578a84d0093789a6480d6f80d6b87c7c87a7c80d6786a5480d6380c6f8457c845708427c80c678357e80c5f80c5780a6e80a5680a460092f7f4657f16475d6f75d6b7d47c7d17c75d677c15475d6375c6f79d7c79d707997c75c677857e7847e75c5f75c577596e75956759460092b73c6573b687386568d6f68d6b71c7c71b7068d67703587005568d6368c6f6dd7c6dd706db7068c676bd7e6bc7e6b85568c5f68c5768b6268b5a68b4a6883d009276796456d6f56d6b65c7c6597c56d676495456d6356c6f6257c625706217c56c676157e56c5f56c5758c5f58c5b5e36c5e26058c575d14458c5358b5f5ac6c5ac605aa6058b5759c6e58b4f58b4756a345696e56956569460092354a4f5494f549270085f538560085b4cc6d5247c4ca4f5114f50d704ca474fc7c4c94f4ea4f4e5704c9474d3704c927008574a0564a0464ab434a0440085345c6e48c6445a6f47c644596f4657e46358459270084f4385643846438440084b3cd6e3cd623cb5d3ca5f40c603ca373c95f3f4603c9373d6723d46d3d3603c92700847008433b0560083b3046e304623045b3045a304563035e37460302573024f354603524f301573437c33a673014f30d7e30d7230d6b30c6e30b5030127008372f26424d6f2e25424d6324c6f2cd7e24c5f24c5724a6e24a5624a4629a642496f28a542495f26e7226a6c26a4624957255722525c249470082f2245f2245722056220460082b1b56f1b5631b46f1fd7e1b45f1b4571b16f1dd7e1b15f1ce721b1571bd721b1470082718c5f18c57188561884600823179640d56f169540d5630d46f1557e0d45f0d457139640d36f129540d35f116721116c0d3570fd720f95c0d3470d16e0d1560da570d1460081f0ac5f0ac570a8560a8460081b03d6f03d6303c6f0857e03c5f03c5703b6f0657e03b5f0567203b570457203b47008170145f014570105601046008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 fullMask g_54 ep_54 449 bds_54 (dagTraceF fullMask rootStock 11 f_54) (cur_54 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_9 : treeBlockF 288 320 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_10 : treeBlockF 320 352 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_11 : treeBlockF 352 384 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_12 : treeBlockF 384 416 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_13 : treeBlockF 416 448 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_14 : treeBlockF 448 449 (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) = true := by decide +kernel
theorem nj_54_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_54_1 h1 h2)
theorem nj_54_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_1 (fun _ h1 h2 => treeBlockF_at nb_54_2 h1 h2)
theorem nj_54_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_2 (fun _ h1 h2 => treeBlockF_at nb_54_3 h1 h2)
theorem nj_54_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_3 (fun _ h1 h2 => treeBlockF_at nb_54_4 h1 h2)
theorem nj_54_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_4 (fun _ h1 h2 => treeBlockF_at nb_54_5 h1 h2)
theorem nj_54_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_5 (fun _ h1 h2 => treeBlockF_at nb_54_6 h1 h2)
theorem nj_54_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_6 (fun _ h1 h2 => treeBlockF_at nb_54_7 h1 h2)
theorem nj_54_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_7 (fun _ h1 h2 => treeBlockF_at nb_54_8 h1 h2)
theorem nj_54_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_8 (fun _ h1 h2 => treeBlockF_at nb_54_9 h1 h2)
theorem nj_54_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_9 (fun _ h1 h2 => treeBlockF_at nb_54_10 h1 h2)
theorem nj_54_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_10 (fun _ h1 h2 => treeBlockF_at nb_54_11 h1 h2)
theorem nj_54_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_11 (fun _ h1 h2 => treeBlockF_at nb_54_12 h1 h2)
theorem nj_54_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_12 (fun _ h1 h2 => treeBlockF_at nb_54_13 h1 h2)
theorem nj_54_14 : ∀ i, 0 ≤ i → i < 449 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := block_join nj_54_13 (fun _ h1 h2 => treeBlockF_at nb_54_14 h1 h2)
theorem nc_54 : ∀ i, 0 ≤ i → i < 449 → (dagCheckNodeV4 fullMask g_54 ep_54 bds_54 449 (dagTraceF fullMask rootStock 11 f_54) cur_54) i = true := nj_54_14
theorem lb_54 : LowerBin fullMask rootStock g_54 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def wg : List Gate := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3970476032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3970476032)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3970476032) = g_54 by decide]
  exact lb_54

end PEqualNP.Outside.L_meta_49393

theorem PEqualNP.Outside.L_meta_49393 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3970476032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3970476032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49393.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3970476032) 13 PEqualNP.Outside.L_meta_49393.root_lb PEqualNP.Outside.L_meta_49393.wg 18 rfl PEqualNP.Outside.L_meta_49393.wfits PEqualNP.Outside.L_meta_49393.weval
