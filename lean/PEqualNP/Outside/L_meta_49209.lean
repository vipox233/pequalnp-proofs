import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49209

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

def m_0 : Nat := 0xcccc0000
def s_0 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_0 : Nat := 0x44c0000
def ep_0 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_2 : Nat := 0x5500550000000000
def s_2 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_2 : Nat := 0x100150000000000
def ep_2 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_4 : Nat := 0x3300330000000000
def s_4 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_4 : Nat := 0x100130000000000
def ep_4 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_6 : Nat := 0xf0f000000000000
def s_6 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_6 : Nat := 0x107000000000000
def ep_6 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_7 : Nat := 0xa000a000a000a00
def s_7 : List Nat := [0x200020002000200, 0xa0000000a00, 0xa000a00]
def g_7 : Nat := 0x20002000a00
def ep_7 : Nat := 0x200080000000200000008000000000000000000000000000000000000000200020000000000000000000000
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

def m_8 : Nat := 0x2222222200000000
def s_8 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_8 : Nat := 0x2022200000000
def ep_8 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x4444444400000000
def s_9 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_9 : Nat := 0x4044400000000
def ep_9 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_10 : Nat := 0x3030303000000000
def s_10 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_10 : Nat := 0x10103000000000
def ep_10 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_11 : Nat := 0x5050505000000000
def s_11 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_11 : Nat := 0x10105000000000
def ep_11 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_12 : Nat := 0xff000000000000
def s_12 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_12 : Nat := 0x17000000000000
def ep_12 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_13 : Nat := 0x4040404040404040
def s_13 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_13 : Nat := 0x4000404040
def ep_13 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_14 : Nat := 0xcc000000cc0000
def s_14 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_14 : Nat := 0x40000004c0000
def ep_14 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
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

def m_15 : Nat := 0xc0c00000c0c0
def s_15 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_15 : Nat := 0x40000040c0
def ep_15 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_16 : Nat := 0xf0000000f000000
def s_16 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_16 : Nat := 0x100000007000000
def ep_16 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_17 : Nat := 0xcc000000cc00
def s_17 : List Nat := [0x440000004400, 0xc0000000c00, 0xcc00]
def g_17 : Nat := 0x40000004c00
def ep_17 : Nat := 0x480000000000000000000000000000000000000004000000080000000000000000000000040000004000
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

def m_18 : Nat := 0xff0000000000
def s_18 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_18 : Nat := 0x170000000000
def ep_18 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_19 : Nat := 0x4444000044440000
def s_19 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_19 : Nat := 0x4000004440000
def ep_19 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_20 : Nat := 0xa0a00000a0a0000
def s_20 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_20 : Nat := 0x20000020a0000
def ep_20 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_21 : Nat := 0xc0c00000c0c0000
def s_21 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_21 : Nat := 0x40000040c0000
def ep_21 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_22 : Nat := 0xc000c000c000c00
def s_22 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_22 : Nat := 0x40004000c00
def ep_22 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_23 : Nat := 0xcc00cc00
def s_23 : List Nat := [0x44004400, 0xc000c00, 0xcc00]
def g_23 : Nat := 0x4004c00
def ep_23 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000
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

def m_24 : Nat := 0x4400440044004400
def s_24 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_24 : Nat := 0x40004004400
def ep_24 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_25 : Nat := 0x3333000000000000
def s_25 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_25 : Nat := 0x113000000000000
def ep_25 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_26 : Nat := 0xf0f000000000
def s_26 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_26 : Nat := 0x107000000000
def ep_26 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_27 : Nat := 0x88888888
def s_27 : List Nat := [0x8080808, 0x880088, 0x8888]
def g_27 : Nat := 0x80888
def ep_27 : Nat := 0x8800000000000080080000000000008080000000000000000000000000000000000
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

def m_28 : Nat := 0x5555000000000000
def s_28 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_28 : Nat := 0x115000000000000
def ep_28 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_28 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 1 bds_28 (dagTraceF m_28 s_28 3 f_28) (cur_28 0) s_28 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 1 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 1 (dagTraceF m_28 s_28 3 f_28) cur_28) = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 1 (dagTraceF m_28 s_28 3 f_28) cur_28) i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xc0c0c0c0
def s_29 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_29 : Nat := 0x4040c0
def ep_29 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_29 : KnownBin bds_29 := by intro b hb; simp [bds_29] at hb
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp [bds_29] at hb
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_29] at hb
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_29 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 1 bds_29 (dagTraceF m_29 s_29 3 f_29) (cur_29 0) s_29 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 1 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 1 (dagTraceF m_29 s_29 3 f_29) cur_29) = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 1 (dagTraceF m_29 s_29 3 f_29) cur_29) i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff00ff0000000000
def s_30 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_30 : Nat := 0x100170000000000
def ep_30 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_18, s_18, 4, g_18), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_18
  · exact lb_2
  · exact lb_4
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

def m_31 : Nat := 0xffff000000000000
def s_31 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_31 : Nat := 0x117000000000000
def ep_31 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_12, s_12, 4, g_12), (m_28, s_28, 4, g_28), (m_25, s_25, 4, g_25)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_12
  · exact lb_28
  · exact lb_25
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 43 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xffff00000000
def s_32 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_32 : Nat := 0x177700000000
def ep_32 : Nat := 0x6000000000000006000000000000001222000000000000144400000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
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
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_26, s_26, 4, g_26), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_26
  · exact lb_11
  · exact lb_10
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

def m_34 : Nat := 0xf0f0f0f00000000
def s_34 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_34 : Nat := 0x107070700000000
def ep_34 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xcccccccc00000000
def s_35 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_35 : Nat := 0x4044400000000
def ep_35 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x3333333300000000
def s_36 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_36 : Nat := 0x113133300000000
def ep_36 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_25, s_25, 4, g_25), (m_10, s_10, 4, g_10), (m_8, s_8, 4, g_8)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_25
  · exact lb_10
  · exact lb_8
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

def m_37 : Nat := 0xaaaaaaaa00000000
def s_37 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_37 : Nat := 0x2022200000000
def ep_37 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
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
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_28, s_28, 4, g_28), (m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_28
  · exact lb_11
  · exact lb_9
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
def g_39 : Nat := 0x40004040c0
def ep_39 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_29, s_29, 4, g_29), (m_13, s_13, 4, g_13), (m_3, s_3, 4, g_3)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_29
  · exact lb_13
  · exact lb_3
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_39_1 (Nat.sub p 32)) (cc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 43 bds_39 (dagTraceF m_39 s_39 6 f_39) (cur_39 0) s_39 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 43 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) i = true := nj_39_1
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcccc0000cccc
def s_40 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_40 : Nat := 0x44400004ccc
def ep_40 : Nat := 0x488800000000000000000000004000000080000004000000080000000000000000000000044400004000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xaaaa0000aaaa0000
def s_41 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_41 : Nat := 0x20000020a0000
def ep_41 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_20
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xff000000ff00
def s_42 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_42 : Nat := 0x170000005f00
def ep_42 : Nat := 0x4800000000000000000000000000000000000000060000000a0000001200000000000000140000005000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf0f00000f0f0
def s_43 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_43 : Nat := 0x1070000050f0
def ep_43 : Nat := 0x4080000000000000000000000060000000a0000000000000000000001020000000000000104000005000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
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
def g_44 : Nat := 0x40000044c0000
def ep_44 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_0, s_0, 4, g_0), (m_19, s_19, 4, g_19), (m_21, s_21, 4, g_21)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_0
  · exact lb_19
  · exact lb_21
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_44_1 (Nat.sub p 32)) (cc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 43 bds_44 (dagTraceF m_44 s_44 6 f_44) (cur_44 0) s_44 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 43 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) i = true := nj_44_1
theorem lb_44 : LowerBin m_44 s_44 g_44 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xaa00aa00aa00aa00
def s_45 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_45 : Nat := 0x20002000a00
def ep_45 : Nat := 0x2000800000002000000080000000000000000000000020002000a0000000200020000000000000000000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
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
def g_46 : Nat := 0x40004004c00
def ep_46 : Nat := 0x400480000000400000048000000000000000000000004000400080000000000000000000000040004004000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17), (m_23, s_23, 4, g_23), (m_24, s_24, 4, g_24), (m_22, s_22, 4, g_22)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_23
  · exact lb_24
  · exact lb_22
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_46_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_46_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_46 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_46_1 (Nat.sub p 32)) (cc_46_0 p) (Nat.blt p 32)
def f_46 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 43 bds_46 (dagTraceF m_46 s_46 6 f_46) (cur_46 0) s_46 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 43 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46) = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46) i = true := nj_46_1
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xf000f000f000f00
def s_47 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_47 : Nat := 0x100070007000f00
def ep_47 : Nat := 0x600080000000600000008000000000000000000000000000000000001000200020000000100040004000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_16, s_16, 4, g_16), (m_22, s_22, 4, g_22), (m_7, s_7, 4, g_7)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_16
  · exact lb_22
  · exact lb_7
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

def m_48 : Nat := 0xffff0000
def s_48 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_48 : Nat := 0x75f0000
def ep_48 : Nat := 0x58000000000000070a000000000000020000000000000004500000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xff00ff00
def s_49 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_49 : Nat := 0x7005f00
def ep_49 : Nat := 0x580000000000000000000000000007000a0000000000020000000000000004005000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_23
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
def g_50 : Nat := 0x44c4ccc
def ep_50 : Nat := 0x48800000000000480080000000000408080000000000000000000000000004404000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_23, s_23, 4, g_23), (m_29, s_29, 4, g_29), (m_27, s_27, 4, g_27)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_23
  · exact lb_29
  · exact lb_27
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_50_1 (Nat.sub p 32)) (cc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 43 bds_50 (dagTraceF m_50 s_50 6 f_50) (cur_50 0) s_50 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 43 (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50) = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50) i = true := nj_50_1
theorem lb_50 : LowerBin m_50 s_50 g_50 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xaaaaaaaa
def s_51 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_51 : Nat := 0x20a0aaa
def ep_51 : Nat := 0x8a000000000000800a000000000020a0a0000000000020000000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 4, g_27)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_27
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
def g_52 : Nat := 0x100000007000000
def ep_52 : Nat := 0x600000000000000000000000000000000000000010000000700000001000000020000000100000004000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
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
def g_53 : Nat := 0x170000005f0000
def ep_53 : Nat := 0x4800000000000000000000000000000000000000060000000a000000120000000000000014000000500000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
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
def g_54 : Nat := 0x100070005000f0
def ep_54 : Nat := 0x40008000000060000000a00000000000000000000000000000000000100020000000000010004000500000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xf0f00000f0f0000
def s_55 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_55 : Nat := 0x1070000070f0000
def ep_55 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_16, s_16, 4, g_16), (m_21, s_21, 4, g_21), (m_20, s_20, 4, g_20)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_16
  · exact lb_21
  · exact lb_20
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

def m_56 : Nat := 0x4444444444444444
def s_56 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_56 : Nat := 0x4044404444444
def ep_56 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_19, s_19, 4, g_19), (m_24, s_24, 4, g_24), (m_13, s_13, 4, g_13)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_9
  · exact lb_19
  · exact lb_24
  · exact lb_13
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

def m_57 : Nat := 0x8888888888888888
def s_57 : List Nat := [0x808080808080808, 0x88008800880088, 0x888800008888, 0x88888888]
def g_57 : Nat := 0x80888
def ep_57 : Nat := 0x8088800000000000008800000000000080080000000000008080000000000000000000000000000000000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 4, g_27)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_27
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_57 g_57 ep_57 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0x2222222222222222
def s_58 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_58 : Nat := 0x2022202020222
def ep_58 : Nat := 0x200000000000220000000200002002000000020000202000202020000000000000000000000000000000000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_58 g_58 ep_58 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xa0a0a0a0a0a0a0a
def s_59 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_59 : Nat := 0x20202020a0a0a
def ep_59 : Nat := 0x208080800000200000008000002000000080000000000000000000000020202020000000000000000000000
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
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
def g_60 : Nat := 0x20222020a0aaa
def ep_60 : Nat := 0x208088800000220000008a000020020000800a000020200020a0a0000020222020000000000000000000000
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_41, s_41, 5, g_41), (m_51, s_51, 5, g_51), (m_37, s_37, 5, g_37), (m_45, s_45, 5, g_45), (m_59, s_59, 5, g_59), (m_57, s_57, 5, g_57), (m_58, s_58, 5, g_58), (m_20, s_20, 4, g_20), (m_7, s_7, 4, g_7)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_41
  · exact lb_51
  · exact lb_37
  · exact lb_45
  · exact lb_59
  · exact lb_57
  · exact lb_58
  · exact lb_20
  · exact lb_7
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV4 0x851060001 0x17af375a6eacbd49fa7274a4e8cfd08f2526464a8c74f8e970c3d287230d4a18a74f6e969d1d7a1ae4f3c96d91cf21c63f3c7698dcf19ad4f6a8ef4fd29b9d2f124e313ca258c47288630fca1d8c37286630bca158c272846506c60b801f 12 4095 6 63 10 1023 15 32767
def f_60 : Nat → Nat × Nat := unpackForestF 0xc9c1f 1 9
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 2 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) s_60 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 2 (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 2 (dagTraceF m_60 s_60 7 f_60) cur_60) = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 2 → (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 2 (dagTraceF m_60 s_60 7 f_60) cur_60) i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0xf0f0f0f0f0f0f0f0
def s_61 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_61 : Nat := 0x101070005050f0
def ep_61 : Nat := 0x40408000001060000050a000100060005000a0000000000000000000101020000000000010104000505000
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 7, g_39)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_39
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
def g_62 : Nat := 0x113133303131333
def ep_62 : Nat := 0x200000000001220000010200012002000100020010202000302020000000000000000000110100000101000
theorem epk_62 : ep_62 = edgePack m_62 g_62 := by decide +kernel
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 7, g_36)]
theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_36
theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV4 m_62 g_62 ep_62 0 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) s_62 7 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_62 g_62 ep_62 bds_62 0 (dagTraceF m_62 s_62 7 f_62) cur_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_62 kn_62 sub_62 gl_62 rc_62 nc_62

def m_63 : Nat := 0xff00ff00ff00ff
def s_63 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_63 : Nat := 0x170077005f00ff
def ep_63 : Nat := 0x48008800000060000000a0000000000000000000060000000a000000120022000000000014004400500000
theorem epk_63 : ep_63 = edgePack m_63 g_63 := by decide +kernel
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 5, g_54)]
theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_54
theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV4 m_63 g_63 ep_63 0 bds_63 (dagTraceF m_63 s_63 5 f_63) (cur_63 0) s_63 5 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_63 g_63 ep_63 bds_63 0 (dagTraceF m_63 s_63 5 f_63) cur_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_63 kn_63 sub_63 gl_63 rc_63 nc_63

def m_64 : Nat := 0xf0f0f0f0f0f0f0f
def s_64 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_64 : Nat := 0x1070707070f0f0f
def ep_64 : Nat := 0x608080800000600000008000006000000080000000000000000000001020202020000000104040404000000
theorem epk_64 : ep_64 = edgePack m_64 g_64 := by decide +kernel
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 7, g_47)]
theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_47
theorem sub_64 : ∀ b ∈ bds_64, m_64 &&& b.1 = b.1 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV4 m_64 g_64 ep_64 0 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) s_64 7 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_64 g_64 ep_64 bds_64 0 (dagTraceF m_64 s_64 7 f_64) cur_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_64 kn_64 sub_64 gl_64 rc_64 nc_64

def m_65 : Nat := 0xffffffff
def s_65 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_65 : Nat := 0x75f5fff
def ep_65 : Nat := 0x58a000000000005800a000000000070a0a0000000000020000000000000004505000
theorem epk_65 : ep_65 = edgePack m_65 g_65 := by decide +kernel
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 7, g_50)]
theorem kn_65 : KnownBin bds_65 := by
  intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_50
theorem sub_65 : ∀ b ∈ bds_65, m_65 &&& b.1 = b.1 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_65 : ∀ b ∈ bds_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV4 m_65 g_65 ep_65 0 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) s_65 7 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_65 g_65 ep_65 bds_65 0 (dagTraceF m_65 s_65 7 f_65) cur_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_65 kn_65 sub_65 gl_65 rc_65 nc_65

def m_66 : Nat := 0xffff0000ffff
def s_66 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_66 : Nat := 0x177700005fff
def ep_66 : Nat := 0x4888000000000000000000000060000000a00000060000000a0000001222000000000000144400005000
theorem epk_66 : ep_66 = edgePack m_66 g_66 := by decide +kernel
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 5, g_32)]
theorem kn_66 : KnownBin bds_66 := by
  intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_32
theorem sub_66 : ∀ b ∈ bds_66, m_66 &&& b.1 = b.1 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_66 : ∀ b ∈ bds_66, canon b.1 g_66 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_66 : Nat → List (Nat × Nat) := fun _ => []
def f_66 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV4 m_66 g_66 ep_66 0 bds_66 (dagTraceF m_66 s_66 5 f_66) (cur_66 0) s_66 5 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_66 g_66 ep_66 bds_66 0 (dagTraceF m_66 s_66 5 f_66) cur_66 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_66 : LowerBin m_66 s_66 g_66 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_66 kn_66 sub_66 gl_66 rc_66 nc_66

def g_67 : Nat := 0x1171777075f5fff
def ep_67 : Nat := 0x648488800001660000058a000160060005800a001060600070a0a0001121222020000000114144404505000
theorem epk_67 : ep_67 = edgePack fullMask g_67 := by decide +kernel
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 7, g_38), (m_30, s_30, 7, g_30), (m_31, s_31, 7, g_31), (m_64, s_64, 8, g_64), (m_62, s_62, 8, g_62), (m_61, s_61, 8, g_61), (m_55, s_55, 7, g_55), (m_50, s_50, 7, g_50), (m_60, s_60, 8, g_60), (m_63, s_63, 6, g_63), (m_65, s_65, 8, g_65), (m_47, s_47, 7, g_47), (m_46, s_46, 7, g_46), (m_66, s_66, 6, g_66), (m_33, s_33, 7, g_33), (m_44, s_44, 7, g_44), (m_43, s_43, 5, g_43), (m_52, s_52, 5, g_52), (m_56, s_56, 7, g_56), (m_42, s_42, 5, g_42), (m_39, s_39, 7, g_39), (m_40, s_40, 5, g_40), (m_54, s_54, 5, g_54), (m_49, s_49, 5, g_49), (m_35, s_35, 5, g_35), (m_53, s_53, 5, g_53), (m_36, s_36, 7, g_36), (m_48, s_48, 5, g_48), (m_51, s_51, 5, g_51), (m_16, s_16, 4, g_16), (m_58, s_58, 5, g_58)]
theorem kn_67 : KnownBin bds_67 := by
  intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_38
  · exact lb_30
  · exact lb_31
  · exact lb_64
  · exact lb_62
  · exact lb_61
  · exact lb_55
  · exact lb_50
  · exact lb_60
  · exact lb_63
  · exact lb_65
  · exact lb_47
  · exact lb_46
  · exact lb_66
  · exact lb_33
  · exact lb_44
  · exact lb_43
  · exact lb_52
  · exact lb_56
  · exact lb_42
  · exact lb_39
  · exact lb_40
  · exact lb_54
  · exact lb_49
  · exact lb_35
  · exact lb_53
  · exact lb_36
  · exact lb_48
  · exact lb_51
  · exact lb_16
  · exact lb_58
theorem sub_67 : ∀ b ∈ bds_67, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_67 : ∀ b ∈ bds_67, canon b.1 g_67 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xdbc91a39431f285b38bad295544629c0cd162299c912b4864115c265c7b09ce4121b790b125d59094ac0614b8ca7522494567b970d0271584826e42369744825078180be320f488009e00001 0xfade07d6304e378231b8138c608c6203e2f81f1780f8b604c5a03e2b8131580f8a607c5201db7816d8c076be05b5b01dab816d4c0769e03b4d00da3806d140368601a6f00d3180697c034b601a5700d2980693c1349c01a4d00d1f8068ec0346e01a33014b780a58c052be0295b014ab80a54c0529e0994e014a680a4fc0527601937014998064bc032560192700c9180617c030b40185703c2b00613c0d09c0184d01c2600611c0308a0184200c1f8060dc0305e0182700c0f80605c0fade07d6304e3782718c0f8be07c5b03e2b81f14c076de05b6301daf816d6c076ae05b5300da7806d340368e01b4500da18269bc134c607a5f03d2d81e95c0f4a605a4f02d2700a92c0549202a470152180a9080548202a4002d1f8168f80747602a3702d198168c8052de02963014af80a56c052ae02953014a78265380529602949014a380a50c0528402941014a000a4fc052760293a0149b80e4d8052660192f00c970064b4030be0185a00c2b81e1580309e0184700c1f8060dc0305e0782e00c1680609c0304a0182200c0f80605c0fade07d6306e3783718c0f8be07c5b03e2b81f14c076de05b6301daf816d6c076ae05b53015a780ad340368e01b4500da18369bc1b4c607a5f03d2d81e95c0f4a605a4f02d2700692c0349201a4700d218069080348201a4002d1f8168f80747601a3702d198168c8032de0196300caf80656c032ae0195300ca7836538032960194900ca380650c032840194100ca00064fc032760193a00c9b80e4d8032660192f014970064b4030be0185a00c2b81e1580309e0184700c1f8060dc0305e0782e00c1680609c0304a0182200c0f80605c0fcfe07e7301ebf8175cc07ade05d6b01eb381758c0b8fe08c7e02e398171c80b8de07c6e02e358131a80b8ce04c6602e31817188216fe08b7e085b9822dc80f6de07b6e03db5812da80f6ce04b6603db181ed880b6be05b5e01dad80ed68076ae03b5602da9816d480b69e05b4e02da6816d300b69605b4a085a487cd200b68e05b4604da2878d100b68605b4202da0816d00034fe01a7300d378069ac034ce01a6300d2f80696c034b401a5701d2b00694c0349e01a4d00d258069280349201a4800d238169180348a1d24400d218069040347e02a3e00d1e80a5fc052e60296f014b580a59c052c60295f014ad80a568052ae03956014a980a53c0529a0294b014a500a524052900294702ca300a5143828802943014a08064fc0327c0193d00c978064b8032560292900c91806488032420192000c378061a8030ce0786600c2d00615c070ac0184701c230061140307e0783e00c1e81e0f00306e0183500c190060bc0304e0181f00c0b81f5bc0fac603c6f02e3180f17c0b8b603c5702e29816dbc116dc05b6302db1016d7c0f6bc05b5b025ad016d5c096ac05b5302da90a09bc034c607a5f00d2d81e95c034a605a4f00d2580e91c0348605a3f02d1e8068ec0347205a371311a8068cc034622316f014b181e57c052b607957014a981653c0529603947014a18164fc0b27a0293b0149c8164dc4026a02933014988064bc052561b12700c9181e17c0f0b40785703c2b00e1280708e0384601c1b80e0d80706a0182f00c1380a07c0502e03b4f01da580ed1c0768601a4f00d2580691c0348601a3f00d1d8068dc034660294f014a580a51c052860293f0149d80a4dc052660192f00c9580649c0324603b4f01da580ed1c0768601a4f00d2580691c0348601a3f00d1d8068dc034660294f014a580a51c052860293f0149d80a4dc052660192f00c9580649c032460383e01e2f80f16c078ae03c5300daf806d6c036ae01b5300da7806d2c0368e01b430152f80a96c054ae02a530152780a92c0548e02a4300d1f8068ec0346e01a3301ca701e178320b8048560c02a00e1180307c018360141700a0980fade07d6301e3780f1b8078c608c6201e2f80f178078b604c5a01e2b80f158078a607c5201db780ed8c076be03b5b01dab80ed4c174de01a6303d2f80696c0f4ae01a5301d2782e9340349601a4901d2380e9140348601a4101d1f8068ec0746e01a33034b780a58c0d2be0295b034ab80a54c0729e0694d014a580a5240728e03945014a180a5040727e0293b01c9b80a4cc0325e0292b0349380648c0f0be0785701c2780e1380b09a0383f01c1f00e0c80305e018270140f80a05c078be05c5b01e2b81714c036be01b5b00dab806d4c0369e01b4b00da3806d0c054be02a5b0152b80a94c0549e02a4b0152380a90c0347e01a3b00d1b8068cc292ac0394603c2f0121580b09c0183e00c1b00a0b80504c07c6f0263681f1ac0f8d207c670263281f18c0f8c206b6f01db682edac0b6d206b6701db282ed8c0b6c206b4f03da581ad1c0f68601a6f00d3680693c0349601a4700d218068fc0347601a3700d1980658c032c20294f014a580a51c052860293f0149d80a4dc052660192f00c9380648c05cfa07d6f026b681f5ac0fad207d67026b281f58c0fac206c6f01e368231ac0b8d206c6701e3282318c0b8c206c5f03e2d81b15c0f8a601b6f00db6806dac036d201b6700db2806d8c036c201b5f00dad806d5c036a601b4f00da5806d1c0368601a6f045370069b4114d801a6b00d350069a4034d001a6704533006994284c801a6300d31006984034c001a5f03d2f00696c034b401a570252b00694c034a401a4f02d2700692c0349401a4701d2300690c0348402971014af80a56c052ae02953014a780a52c0528e0294300c9f8064ec0326e0193300c978064b4032560292900c9380a494032460192100c1b0060980fade07d630363782f18c0d8be07c5b0362b81f14c1b6de08b6e08db1822d880f6be07b5e03dad812d680f6ae04b5603da981ed481769e05b4e035a580ed280d68e03b4605da1816d08034de01a6300d2f80696c034ae01a5300d2780692c0348e01a4300d1f8068f40346e01a3500d1980a5bc052c60295f014ad80a55c052a60294f014a580a5280528e0b946014a18064fc0327c0193d00c978064b8032560192700c91806488030be0185700c2780611c0307e0183d00c1b8060d40305e0182700c0f8060740302e0181503eb781f58c178de0bc6303e2f81f16c0f8ae07c5300db7806d8c036be01b5b00dab806d4c0369e01b4b00da3806d0c034de08a6e00d31806988034be07a5e00d2d806968034ae04a5600d298069480349e05a4e00d258069280348e03a4600d21806908262de0296303caf80a56c0f2ae0295305ca780a52c1728e0294300c9f8064ec0326e0193300c978064b4032560292900c93848494032460192100c2f80615c0309e0184700c1d0060dc0306c0182700c130060940303e0181703e2f83b16c178ae07c5300daf806d6c036ae01b5300da7806d2c0368e01b430152f80a96c054ae02a530152780a92c0548e02a4300d1f8068ec0346e01a330d4ab0064f80f0bc0485602c2700e1180306c0282e0141300b9f40fade04d6d03eb581f5a40face04d6503eb181f5840d8de03c6d046358171a40d8ce03c65046318171840d8be07c5b0362b81f14c036de07b6e00db681edb0036d601b6a00db4806da0036ce07b6600db281ed90036c601b6200db0806d80036be07b5e00dad806d68036ae04b5600da9806d480369e05b4e00da5806d280368e03b4600da1806d08034de01a6d00d358069a4034ce01a6500d31806984034be01a5b00d2b80694c0349e01a4b00d2380690c052e20295f014ad80a55c052a60294f014a580a51c052860193f00c9e8064ec05272019370149a8064cc032620192f00c9580649c032460785600c1f0060b80fade07d6305e3783b18c0f8be07c5b03e2b81f14c036de07b6e00db1806d88036be07b5e00dad806d68036ae04b5600da9806d480369e05b4e00da5806d280368e03b4600da1806d08034de01a6300d2f80696c034ae01a5300d2780692c0348e01a43078b780a58c0f2be0295b03cab80a54c1d29e0294b05ca380a50c0327e0193d00c9d80a4e40326e0793500c998064c40325e0192b00c9380648c030be0185a00c2b81e1580309e0184700c1f8060f80307a0182f00c170060880303e0181703da781ed2c0f68e07b4300d2780692c0348e01a4300d1f8068ec0346e01a33014a780a52c0528e029430149f80a4ec0526e0293300c978064ac0324e01923025a7812d2c0968e04b4300d2780692c0348e01a4300d1f8068ec0346e01a33014a780a52c0528e029430149f80a4ec0526e0293300c978064ac0324e0192300c1301f17c178b60bc5703e29806d7c036b601b5700da9806d3c0369601b4700da180a97c054b602a570152980a93c0549602a47015218068fc0347601a3700d198064d80f0bc0d05c0242b0301500b09c0384600c1f00a0b80504c07c5f0262e81f16c0f8b207c570262a81f14c0f8a206b5f01dae81ad6c0b6b206b5701daa81ad4c0b6a206b4f035a581ad1c0d68601a5300d2880693c0349601a4700d218068fc0347601a3700d1980a57c052ba0294f014a580a51c052860293f0149d80a4dc052660192b00c9380648c03cfa07d6f026b681f5ac0fad207d67026b281f58c0fac206c6f01e3681b1ac0b8d206c6701e3281b18c0b8c206c5f0362d81b15c0d8a601b7100daf806d6c036ae01b5300da7806d2c0368e01b430153780a9b4054d602a690153380a994054c602a610152f80a96c054ae02a530152780a92c0548e02a4300d1f8068ec0346e01a33014b78225b8052da0896c014b580a5a8052d202968014b3822598052ca0a164014b180a588052c202960014af81e578052b60295a014ab812558052a602952014a7816538052960294a014a380e518052860294200c9f8064f8032760193a00c9b8064d803266019320141300a0580fade07d630363781b18c0d8be06c5b0362b81b14c136de08b6e08db1822d880f6be07b5e03dad812d680f6ae04b5603da981ed480d69e05b4e035a580ed280d68e03b46035a1816d08034de01a6300d2f80696c034ae01a5300d2780692c0349401a470352300690c0347e02a3e00d1e80a5bc052c60295f014ad80a55c052a60294f014a580a51c052860193f00c9e8064dc0326a0193300c978064ac052520192700c91806484030be0185700c2780611c0307e0183d00c1b8060d40305e0182d00c138060940303e0181703eb781f58c0d8de06c630362f81b16c0d8ae06c53049b7806d8c0f6be01b5b03dab806d4c0d69e01b4b035a3806d0c054de02a630152f80a96c054ae02a530152780a92c0548e02a4300d1f80a8ec0546e01a33014b78225b8052c602962014af81e578052b60295a014ab812558052a602952014a7816538052960294a014a380e518052860294200c9f8064f8052760293a0149b8204d803266019320142f80a15c0509e0284700c1f8060dc05054028270141300a05c0502c028150362f83b16c0d8ae07c5300daf806d6c036ae01b5300da7806d2c0368e01b430152f80a96c054ae02a530152780a92c0548e02a4300d1f8068ec0346e01a330d4ab00a4b80f0bc0485602c2700e1180307c01836014130079f40fade04d6d03eb581f5a40face04d6503eb181f5840d8de03c6d046358171a40d8ce03c65046318171840d8be07c5b0362b81f14c036e201b5f00dad806d5c036a601b4f00da5806d1c0368602a6f03d3700a9b40f4d802a6b0153500a9a4054d002a6703d3300a9940f4c802a630153100a984054c002a5f03d2f00a96c054b402a570252b00a94c054a402a4f02d2700a92c0549402a4701d2300a90c0548401a3f00d1f0068ec0347401a3700d1b0068cc034640296f014b680a5ac052d202967014b280a58c052c20295f014ad80a55c052a60294f014a580a51c052860193f00c9d8064dc03266078560141700a0780fade07d630363783b18c0d8be07c5b0362b81f14c0a6de01b6303daf806d6c0f6ae01b53075a7806d2c0d68e01b430153781e9b8054c602a620152f81e978054b602a5a0152b812958054a602a52015278169380549602a4a0152380e9180548602a4200d1f8068f80547602a3a0151b81e8d80346601a32014b780a58c052be0295b014ab80a54c0529e0294b014a380a50c0327e0293b0149b8064cc050be0285a0142b81e1580509e0284700c1f8060dc0505e0282e0141680a07c0503c02812035a781ad2c0d68e06b4300d2780692c0348e01a4300d1f8068ec0346e01a33014a780a52c0528e029430149f80a4ec0526e0293300c978064ac0324e01923025a7812d2c0968e04b4300d2780692c0348e01a4300d1f8068ec0346e01a33014a780a52c0528e029430149f80a4ec0526e0293300c978064ac0324e019230140b01b17c0d8b606c5703629806d7c036b601b5700da9806d3c0369601b4700da180a97c054b602a570152980a93c0549602a47015218068fc0347601a3700d1980a4980f0bc0305c0242b0081500b09c0384600c1f0060d80505d2345f9122dc7515e348a71935f8a1adc4cd5e1c6a70b34f821a5c0cd1e04686fc25f7d12dbe095dec4a6f524f79925bc891dde486ee23f7691dba48ddc0466d315f688adb2055d8c2a6c514f608a5afc51d78286b813f5b89dacc4dd442669d12f4b8959b849cb82465805f2b82d92c15c900a64704f230258b011c540861a03f0b81d8580dc2a0661102f0801583809c160460701f0300d81005c020260003f 19 524287 8 255 11 2047 21 2097151
def cc_67_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x87a4e82951796937682e7323670b2769c6f675276284d5ff295b14e560514cd934cb024ba11477434195e3859432e573121c2f1212c52c2685d2194f1c95019d2c1732a1165d0ec2a09d4f04d500004d 0x9ade1358cbe3788c6e138c6231880e2f81c5e038ae0714c0e290bb6f1d6c612d7c25ad84b57096a626d3c1da68eb4b0b6922ed1c1da289b430b682069be013701a63034c40697c0d2d81a5a034ae129580d2981a470948c069140d1f81a3b0346e068cdc8b782963092be0a56c24ab829531329ebc53414a5829492f28efc51414a1829411d27e0a4ec5c9b829330325e064ac0c9381923030be0615c0c278184d0308e061140c1f818370305e060b40c13818250303e0605c26b784d63078de0f18c1e2f83c5b078ae0714cc5b788b6e316c622d881daf83b5e036ae06d4c0da903b4f0769c06d2c0da501b470368c06d0c0da101a6f034c60697c0d2e81a5b034ae069540d2981a4f034960691c0d2181a3f0347a068ec0d1c81a370346a068cc0d188696f052c61257c14ad84957052a60e53c14a583947052861a4fc349e8293b052721a4dc349a8293305262064bc0c9581927032460617c0c2b8184f0308e060fc0c1e818370306a060bc0c15018270304c0607c0c0b84e7f09cfc139cc473904d7f09ae60f1fc1e3f03c73118e40f1bc1e3703c6d078d80f1ac263503c69098d00f19c1e3303c65078c80f18c263103c617a8c00f17c1e2f03c5b098b40f164262c03c57078ac0f14c262903c510f8a00edfc1db983b6f076da0edac1db483b67076ca0ed8c1db083b5f076b60ed641dab83b53076a206d3c0da701b4d034fe069cc0d3781a6d034d6069a40d3381a65034c6069840d2f81a5d034b60695c0d2a81a530349e0e9380d2681a3f0747c068ec0d1c81a3303464068c434bf82973092de1a5b414b582969092ce1259414b182961092be1a57414ad84957092aa0a54c1ca78694d052960a5241ca383945052860a5041c9f8693d052760e4dc1c9a829330325e064b40c95819270d24a0648c0c3d07876030de121b80c368185f090bc061480c280184f0709c061343c26018470308a061080c1f8383e0306e060c80c178182a0304e060980c0f8181a0302e1a058262f84c5e096be12d6c25ab84b530d69e0ed3475a585b490d68e0ed1475a185b41094be0696c252b81a533149e269340d2581a493148e269140d2181a411d47e068ec351b81a33052be0a57414ad82957052aa0a52c14a48293f052760a4dc14998192f052560a49c0c918281609afc135f426be09d7a09af2275e026bb04d7509ae84f5c826b893d70098fa1f1e8263c87c78098ec131d4263a04c71076fa16de41dba85b71076ba12d641daa85b51096921ed04453f01a7d034ba069640d2a81a510349a069140cb88295d052b20a55414a88294d0528a064b41492878760f0e81217824270783e0304c0a058173e84d6d09ad21359426b088c6e118da231b0463509c69138d023198be3297c64118c423184463001c5e076da16da41db285b610769a16d241da285b41034da069a40d3281a61034b412958252301a45052e20a53414a482945052820b9f426b784d6e09ada135b026b588d6a09ad2ed5a026b384d6609aca1359026b188d6209ac223580263784c6d098d61f1a8263487c68098ce13198263284c64098c61318435b783b6d116d616da435b383b65116c616d8425af83b5d096b612d6425ab83b55096a616d4425a784b4b0969212d1c25a187b41114de229b40d3581a69114cee89940d3181a61094bee49740d2d81a59094ae129540d2981a510949e1e9340d2584a470948a0690c751f81a3b0d46e068cc14b88295f092bc0a575a8ae0295b052b20a55c14aa82953052a40a54414a80294f0529a0a52c14a382945052860a4fc149d8293705266064bc149582927032461e1983c320485e0909c1e0f83c130281603cfa135b426b484d6509ac2231b8463688c6c118d4371a46e3408c66278ca6f190463108c61118c00b1781db685b69076ca16d841da685b490768a16d040d3881a4d03492069140d208296d052d20a59414b08295a092ac1251814a289d6f11adc2758c46b104c6f098c60717c0e2e82c5b058b20715c0e2a81c53038a21adbc75b186b5f076ba26d6c2dac86b57076aa26d4c2da884b4f0969612d1c25a181a6f034c60697c4d2f01a5d0349e0692c0d2381a430347e068ec0d1b81a33052de0a58c0caf8195d032b60656414ab82955032a6065440ca78294b0528e0a50c149f8293b0526e0a4cc0c978192d032560649c149281923030be061740c2b818550309e0611c0c1f818370305e0609c0c0f8181705ada1317c262e84c5b0f8b41315c262b04c55116da12d7c25ae82b4f0d4be2296c352b88a530949e1292c252384a430d47e368ec351b8da33112be0656c44ab819530929e0652c24a3819431b27e064ec6c9b819331d25e064ac3493819230f0ac135bc26b19bc6f118dc3718c463102c5f058bc0b15c162982c520d6de3ad8c25af84b5b096ae12d4c35a783b4d1d69616d2435a383b451b68616d05b93781a63094be0696c252b81a531b49ebc9340d2581a492748ed89140d2181a411d47e068ec351b81a33052ded45b814b182962052be0a56c14ad02957092ac0a54c14a3849460528a0a4fc149d8293705266064bc149582927032460a17c142b8284f0509a0a11c14228283f0506e060bc0c138281f0503a0a05c140a84d6f09ac60f1bc1e3183c5f078b60f15c162998b6f116dc62d8c45b103b5f076bc0ad5c15a982b520769e0ed3815a582b4a0568e0ad1815a182b42174de0698c252f81a5b094ae0694c1d2781a4b0748e0690c5d1f89a3d03476068e45d1b89a3503466068c414b782963052be0a57414ad82957052aa0a54c14a78294b0528e0a50c149f8293d052760a4e4149b82935052660a4c40c978292b0524e0648c142f828570509e0a11c141f8283d0506e0a0d40c17818270503e0a068140b8281609cfe139f8273988e7209afe135cc1e3f83c7e078e6231c81e3783c6e078da0f1b01e3584c6a078d2131a01e3383c66078ca0f1901e3184c62078c2cd1801e2f83c5e078b6131681e2c84c58078ae0f1581e2984c52078a21f1401dbf83b73076de0edb41db583b69076ce0ed941db183b61076be0ed6c1dac83b57076a60ed4415a782b4e0569a2e9fc0d3984a6f174da069ac0d3484a67094ca0698c0d3084a5f0f4ba0696c252b84a55034a60e93c5d2681a4b034920e91c1d2281a43034820e8fc5d1e81a3b0746e0e8d40d198297f052e60a5bc14b68296b052d20a59c14b282963052c20a57c14ae8295b052ae0a55414a98294f0729c0a534149f8393e052760a4e414998293205262064bc14958292a0524e2e4980c918287a0f0ec0a1bc24370286d050be121781429028500509e0e13814268784c0508e0a11414210283f0707c0a0dc14190182f050540609c3c130281f050340a05c140b04b540324023e00464609c7c098f0131d08e3807c6c098c8c49f0253c04a74114e01e9b02532019300f0881e09026b784d63138de231b84e3188c62098be131780e2b81c53038a41adbc75b184b5f096b612d5c25a986b4f0769a26d2c2da486b470768a26d0c2da081a6f034c60697c0d2d81a57034a60691c4d2301a450347e068ec0d1b81a33052de0a58c0caf8295b052ae0a54c14a3899460528a0a4fc149d8293705266064bc0c9581927032460617c0c2b8184f0309a0611c0c228183f0306e060bc0c138181f0302e135bc26b186c6f1d8c61317c262d84c59098ae1314c3e2881b6f036c606d7c0dae81b5b036ae06d540da981b4f0369606d1c0da191a6f114dc4698c453104a5f094bc1e9740d2b81a55034a606948752785a4e0d4960e928352383a461d486169080d1f81a3e03476068e80d1b81a3603466068c814b782963052be0a57414ad82957052aa0654c14a78294b0528e0a50c0c9f8193b0326e064cc0c978192d052560a4a40c938192503246064840c2f818570309e1e1380c23818420307e060e80c1b818360305e060b40c15018270f04c060943c120181f030340605c140b04e7f09cfc139cc473904d7f09ae61b1fc763984c6f078da131ac263484c67078ca1318c2e3084c5f098b613164262b84c530f8a256dfc45bf30373116e412dbc25b709b6d5e6d812dac25b504b69096d012d9c25b304b65096c812d8c25b111b615c6c012d7c25af07b5d0f6b812d6c25ad04b57096ac12d5425aa04b53096a43ad3c2da706b4b076941ad1c1da30eb430b684069fc0d3981a6f034da069ac0d3481a67034ca0698c0d3081a5f034ba0696c0d2b81a55034a60693c0d2581a4a0348e1a9180d2181a3f0547c068f414bf82973052de0a5b414b582969052ce0a59414b182961052be0a57414ad82957052aa0a54c14a78294b052940a51c5ca3029430327e064f80c9e8192f0325c064ac14948192303244064840c900187a0f0ec061bc24370186d030be121780c29018500309e1e1380c23818420307e060f40c1d018370f06c060d43c1a0182f030540609c0c130181f030340605c140b04d6f09adc1358c46b104c6f098c710dbc75b184b5f076ba12d6c25ac84b57076aa12d4c2da884b4f0969612d2425a384b430f683049bc0d3184a5f7c4ba0696c0d2c84a57094aa0694c0d2884a4f0f49a0692c252384a45034863a8fc0d1dbc23703466e05bc14b18495f682ba0a56c14ac84957092aa0a54c14a88494f0f29a0a52c24a384945052863a4fc149db213705266064bc1495ad127032464a1a83c330485f090bc1e17424278484e09084ac1003c1f8783e0f06e520c80c179a82a0304e1e098140f9a81a0502e1e05825a784b4b0968e12d0c0d2781a4b0348e0690c0d1f81a3b0346e068cc14a78294b0528e0a50c149f8293b0526e0a4cc0c978192b0324e0648c24270583e0304c0a0583e2f84c5b098ae1f14c0daf81b5b036ae06d4c0da781b4b0368e06d0c152f82a5b054ae0a94c152782a4b0548e0a90c0d1f81a3b0346e068cc24ab2b1540f0bc161381c230183e0306c0a0b8141307c6f098da1f1ac3e3487c67098ca1f18c3e3083b6f076da0ed3c2da583b470b6860698c0d3081a4f034960691c0d2181a3f0346e068ccb4b78d96d052d60a5a4b4b38d965052c60a5843ca78294b0f28e0a50c2c9f8293b0726e0a4cc0c978192b0324e0648c3c2301e7d0fade135b43eb587d690face135943eb187d61078de0f1b42e3585c69078ce0f1942e3185c61078be1716c1e2b85c530b6de22db82db688b6c0b6d616da82db485b680b6ce22d982db2a93640b6c616d882db085b600b6be1ed782dad84b5a0b6ae12d582da985b52034e20697c0d2d81a57034a60693c0d2581a4703486068fc0d1e81a3b03472068dc0d1a81a3303462225bc44b68296b052d22259c84b282963052c21e57c14ad87957052a61653c14a58394705286164fc2c9e8293b05272164dd109a8293305262064bc0c9581927032461e1581c23038360fade1f58c6e3788c6e1b8c6231883e2f87c5e0f8b6131683e2b84c560f8a61f1481db785b63076be16d6c1dab85b530369e06d3415a582b490368e06d140da181b41034de0698c0d2f81a5b034ae0694c0d2781a4d03496069240d2381a4503486069040d1f81a3b0346e068cc14b782963052be0a56c14ab829530528e2651814a28193f052760a4dc14998192f03256064a80c9381926032460617c0c2d018570f0ac0613c0c26818470308a060fc0c1b8182f0304e0607c0c0b87d6f0fac6271bc463717c63118c41f17c3e2f07c5b098b41f15c262b07c530f8a40edbc2db183b5f0b6b60ed5c2da981b4f0369a06d1c0da281b43034de0698c0d2f81a5b034ae0694c0d2785a4e0349a068fc2d1f01a3b0346e068cc0d192416f052c61e57c14ad87957052a65e53d38a68294b052922651cf0a28294305282164fc149d8393705266064bc0c968192b0324e744940c918185f030b40615c3c2b0184f0309a0611c0c228183f0306e060bc0c16818270304a0607c0c0b87c6f098da1f1ac3e3487c67098ca1f18c3e3083b6f076da0ed3c2da583b470b686429bc4d3681a6b034d24299c4d3281a63034c21e93c0d2587a4703486168fc0d1d83a37034660a58c14b08294f052960a51c14a18293f0526e0a4cc0c978292b0524e0648c3c2302e7d09ada1f5a426b287d61118dc231b4463608c6a2f8d25f1a0463309c65138c823188463088c600f8bc13168262b07c52076da16da41db285b610369a069b40d3481a65034c2169380d2685a3e034640a5c414a6829490528a0a5040c96829250f0ac0b9f43eb784d6d0fad61f5a43eb384d650fac61f5841e3783c6d0b8d6171a41e3383c650b8c6171841e2f85c5b078ae1714c2db788b6e0b6da22db02db585b6a0b6d216da02db388b660b6ca94d902db185b620b6c216d802daf87b5e0b6b612d682dab84b560b6a616d48453788a6d034d6069a4453396a65034c6069843d2f81a5b0f4ae0694c2d2781a4b0748e0690c2d1f85a3d03476068e42d1ba423503466068c414b88295f052b60a55c14a98294f052960a51c14a18293f0527a0a4ec149c829370526a0a4cc14988192f052560a49c0c91878560708c0e0d80f3e84d6d0fad2135943eb088c6e118da231b0463513c69378d0231986e328dc64118c423184463007c5e098b4131583e2903b6d0b6d20ed942db082b4d034e2069340d2481a45034820a5b414b482965052c21653814a68593e05264064a80c93078560fade1f58c1e3785c63078be1716c1e2b85c53136de22db84db188b620f6be1ed783dad84b5a0f6ae12d583da987b520369e06d3815a582b4a0368e06d180da181b42034de0698c0d2f81a5b034ae0694c0d2781a4b0348e0690c0d1b89a360346a0a5bc14b18295f052b60a55c14a98294f052960651c14a18293f0527a064ec0c9c819370326a064cc0c988192f0325a064ac0c9382925032460617c0c2d018570f0ac0613c0c238183f0307a060dc0c1a8182f0304e0607c0c0b87d6f0fac6371bc46371bc63118c41f17c3e2f07c5b098b41f15c262b07c530f8a40edbc2db183b5f0b6b60ed5c2da982b4f0569a0ad1c15a282b43444de0698c3d2f81a5b0f4ae0694c9d27a124d03496069246d239e24503486069042d1f81a3b0746e068cc14b782963052be0a56c14ab829530529e1653814a68293f0b27c0a4ec149b8293305264064bc14958292a0524e704980c918285f050b40a15c3c2b0284f0509a0a11c14228283f0506e060bc0c138281f0503a0a05c140a87d6f0fac60f1bc2e3183c5f0b8b60f15c2e2981b6f036c606d7c0dad81b57036a606d3c0da581b4703686429bc453710a63114c41e97c3d2f07a5b094b41e95c252b07a530f4a40693c0d2581a4a0748e0e9180d1f81a3e03476068e80d1b81a3603466068c814b782963052be0a56c14ab829530529e0652c14a3829430327e064ec0c9b819330325e064b41495829290324e064940c9181921030be0615c0c27818470307e060dc0c178182d0304e060940c0f81817 20 1048575 8 255 11 2047 19 524287
def cc_67_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xd66a33941c199ae4c3b0d0ea242a488281a19a8be50b38eab219c2808bde8b374ab1b1c266ab9852b58f0d532151c613b184a889034e3c68cdc2b293bc8dae1cad83b6f09aa4004d 0x32d3c65a58cb47196860e93c1d2583a47074860e8fc1d1d83a37074678c53f10a5e1147be286324fc649d8c937192660e4bc1c9583927072460613c0c258184703086060fc0c1d8183703066060bc0c1581827030460607c0c0d81817030263317c662d8cc57198a60ed7c1dad83b57076a60ed3c1da583b47076860697c0d2d81a57034a60693c0d2581a4703486068fc0d1d81a37034660a57c14ad82957052a60a53c14a582947052860a4fc149d8293705266064bc0c968192b032540649c0c9302925bc2480648c0c2f8185b030ae0614c0c278184b0308e0610c0c1f8183b0306e060cc0c178182b0304e0608c0c0f8181b0302e0604c66b78cd6b19ace3358c363786c6b0d8ce1b18c362f86c5b0d8ae1b14c0db781b6b036ce06d8c0daf81b5b036ae06d4c0da781b4b0368e06d0c153782a6b054ce0a98c152f82a5b054ae0a94c152782a4b0548e0a90c0d1f81a3d03476068e80d1b81a360546b948d00cb78896e032d60659c0cb181962032be1e5780cad8195a032ae125580ca9819520329e165380ca6e414c03296065280ca3839460328b745100ca1819420327e064f80c9e8192f0525c064b40c378186b030ce0618c0c2f8185b030ae0614c0c278184b0308e0610c0c1f8183b0306e060cc0c178182b0304e0608c0c0f8181d030360605c0c0a8181309ada1f5841e3683c6c078c21f1801e2f83c5e078b6131681e2b83c56078a61f1481db683b61076be0ed6c1dab83b530369e06d380da681a6d034c20697c0d2d81a57034a60693c1d2701a4d0347e0e8f80d1d81a3903466068c80d188696d052c21a57c14ad86957052a60e53c34a68294b052920e51c1ca282943052820e4fc349e8293b0726e0e4d414998192f0325a064ac0c9386925032460e1383c2604d6d0fac20f1b41e3603c610f8c00f17c1e2f03c5b098b40f15c1e2b03c530f8a40edb41db083b5f076b60ed5c1da982b4f0569c0ad343d3681a610f4be0696c3d2b81a530749e2e9340d2581a490748e0e9140d2181a410747e2e8f40d1d83a370746a068cc14b682961052be0a56c14ab829530529e0e53814a68293f0727c0a4ec149c82933052640a4c40c978292b052540a49c5c93019230709c1e13026b687d61078da17184362f87c5b0d8ae1f14c3db687b6c0f6c21ed803daf87b5e0f6b612d683dab84b560f6a61ed4875a785b4e0d6960ed2835a383b461d68616d080d3681a61034be0696c0d2b81a530349e0692c0d2501a470d48c0690c0d1f82a3e0347a0a5b414b08295f052b60a55c14a98294f052960a52814a38b94605286064fc0c9f0193d0325e064b80c958292903246064880c9081920098ba1f1441dae85b510f69e1ed2c3da387b430f4ba069443d2781a4b0f48e0690c751f81a3bb646e068cc3cae829510f29e0a52c3ca3829431d27e0a4eed09b829330325e0a4aec893819230f8be3b16c762b87c53036be06d6c0dab81b530369e06d2c0da381b43054be0a96c152b82a530549e0a92c152382a430347e068ec0d1b81a33252ac1e178242b0584e0708c060f80c1b0282e0504c1f17c262e87c5b0f8b21f15c262a87c530f8a21ad7c1dae8db5b0b6b21ad5c1daa8db530b6a21ad3c3da586b470f6860694c0d2881a4f034960691c0d2181a3f03476068dc0d198295f132bc0a57414a78294b0528e0a50c149f8293b0526e0a4cc0c958192a0324e064980c91878460f8be131743e2d87c590f8ae131543e2987c51136be0ed7475ad85b59176ae0ed544da985b510f69e1ed2c3da387b430349e1e9380d2581a4703486069080d1f81a3b0346e068cc4cafce15d052b60a564bcabd6155052a60a5443ca78294b0f28e0a50c749f8293b1726e0a4cc0c978192b0324e0648c3c2303c5f078b60f15c1e2987b5f0f6bc1ed6c25ad07b57096ac1ed4c3da901b4b036940697c0d2d81a57034a60693c0d2581a430347e068f434af8295b0d2ae0a54c1ca78294b0728e0a50c349f8693d052760a4e4349b86935052660a4c40c978192b0324e0648c3c2b04d7d0fae20f1f41e3e03c71a88e00f17c1e2f03c5b098b40f15c1e2b03c530f8a40edf41db883b5f076b60ed5c1da981b4f0369c06d340d3e81a71034be0696c0d2b81a530349e0e9380d2681a3f0747c068ec0d1c81a3303464068c434be829710d2be0a56c34ab829530729e1a53414a5829490728e0e51414a1829410727e1a4f4149d839370726a0a4cc0c978192d032560649c3492819230f0ac1f1bc263687c6b0f8d21f19c263287c630f8c21adbc1db689b6b0b6d21ad9c1db289b630b6c21ad3c3da586b470f686069bc4d3701a6d0349e0692c0d2381a430347e068ec0d1b81a33032c60658414a78294b0528e0a50c149f8293b0526e0a4cc0c978192d0324e0a4940c91878460f8be131743e2d87c590f8ae131543e2987c510d6be0ed7475ad85b590d6ae0ed546da985b510d69e1ed2c35a387b431b4bf389740d2d81a59274af489540d2981a510f49e0692c3d2381a431d47e068ec351b81a330529e1e53814a582947052860a508149f8293b0526e0a4cc0c978292b0524e0648c3c2303c5f078b60f15c1e2987b5f0f6bc1ed6c25ad07b57096ac1ed4c3da902b4b056941e97c0d2d87a57034a60e93c0d2583a47034862e8fc4d1e81a3b034722e8dc4d1a81a33034620a57c14ad82957052a60a53c14a5829430527e0a4f40c978292b0524e0648c3c2b04d7d0fae20f1f41e3e03c71a08e00f17c1e2f03c5b098b40f15c1e2b03c530f8a40edf41db883b5f076b60ed5c1da982b4f0569c0ad345d3e81a710f4be0696c3d2b81a530749e2e9340d2581a490748e0e9140d2181a410747e2e8f40d1d83a370746a068cc14be82971052be0a56c14ab829530529e0e53814a68293f0727c0a4ec149c82933052640a4c40c978292b052540a49c5c93019230f0ac1f17c262e87c5b0f8b21f15c262a87c530f8a21ad7c1dae89b5b0b6b21ad5c1daa89b530b6a21ad3c3da586b470f6860695c4d2b01a550349e0692c0d2381a430347e068ec0d1b81a33052ae2655814aa8294f052960a51c14a18293f052760a4dc14998192f032560648c3c2306c5f0f8b61b15c3e2981b5f036b606d5c0da981b4f0369606d1c0da187a5f0f4bc1e96c252d07a57094ac1e94c3d290ea4f0b49c1a92c1d2506a470748c3a90c2d2101a3b034740a57c14ad82957052a60a53c14a58294705286064fc0c9d819330325e064b426be87d71078fa171c4362f87c5b0d8ae1f14c4dbece37c236e334dc03daf87b5e0f6b612d683dab84b560f6a61ed4875a785b4e0d6960ed2835a383b461d68616d080d3e81a71034be0696c0d2b81a530349e0692c0d2501a470d48c0690c0d1f82a3e0347a0a5f414b88295f052b60a55c14a98294f052960a52814a38b94605286064fc0c9f0193d0325e064b80c958292903246064880c90819200f0ac131b43e3083b6d0b6c21ed3c3da587b470f687549b40d3087a4f034961e91c0d218ea3f034774c8dc0d19d116d052c21e53c14a587947052863a4fc149dcf13705266064bc1495cc127032461e1183da787b4b0f68e1ed0c0d2781a4b0348e0690c0d1f81a3b0346e068cc14a78294b0528e0a50c149f8293b0526e0a4cc0c978192b0324e0648c25a784b4b0968e12d0c0d2781a4b0348e0690c0d1f81a3b0346e068cc14a78294b0528e0a50c149f8293b0526e0a4cc0c978192b0324e0648c3e2f8ec5b1d8ae1f14c0daf81b5b036ae06d4c0da781b4b0368e06d0c152f82a5b054ae0a94c152782a4b0548e0a90c0d1f81a3b0346e068cc3c2f4a05c090ad241502c27038460307c060d814170282609ade1f58c3e3788c6e0f8c61f18895b78eb630f6be12d6c75ac84b570f6a61ed443da783b4d0f69616d243da383b450f68616d04653781a630f4be1e9740d2d84a57194aa0694c3d2787a4d03496069243d238ca450348606904651f81a3b1946e068cc7cb7829630f2be1e57414ad849571f2aa0a54c3ca78794d052960a5243ca38f945052860a504749f8293b1f26e0a4cc0c978292b1924e0648c242d04857090ac1211c2423048450f07e1e0dc0c17818270503e0a05c262f84c5b098ae1314c0daf81b5b036ae06d4c0da781b4b0368e06d0c152f82a5b054ae0a94c152782a4b0548e0a90c0d1f81a3b0346e068cc24af0794e0326c0a498242b0584e0708c060f80c1b0282e0504c0f17c1e2f03b5f076b60ed5c1da583b49094be0696c252b81a531749e269340d2581a491748e269140d2181a410747e068ec1d1b81a33092be0a56c24ab829530d29e1a53414a5829490d28e1a51414a1829410727e0a4ec1c9b829330325e0a4ac34938192307cfa0f5bc1eb703d6d07ad80f5ac1eb504d698aad00f59c1eb304d6509ac80f58c1eb103d6107ac00f1bc1e3683c6b078d4131a43e3403c67078cc13194263203c63078c20edc41daf83b5e076ba0ed701dad83b59076ae0ed541da984b52076a216d401da783b4b076920ed1c1da183b41074de0e9b40d3581a69074ce2e9940d3181a61094be2e9740d2d81a59094ae129540d2981a510949e1e9340d2584a470948a0690c1d1f81a3b0746e068cc1cb78396d052d60a5a41cb386965052c60a58424af8695d052b60a56424ab84955052a60a54424a78694d052961251c24a2829430727e0a4ec1c9b829330325e0a4ac349381923070cc1e190242f0484e0707c1e098340b04c5f098bc12d7c25ad84b57096a62ed3c1da68eb4b0b6922ed1c1da28eb430b6820697c0d2e81a5b034ae069540d2581a490347e068ec0d1b81a33092be0a56c24ab829533129e3653414a5829493128e3651414a1829411d27e0a4ec5c9b829330325e064ac0c93819230304c135b826b684d6c1bad4135a46eb404d6609aca13590aeb104d6131ac0131b43e3504c690f8d013198263284c64098c20edb42db483b650b6c20ed7425ac83b550b6a212d243da081a61034ba069640d2a81a510349a0691444b70296d052ba0a56414aa829510529a0a5140c95019260f0cc1e190242f0484e0f07c06098140b01e7d09ade135b826b684d6c09ad6235a826b4c356809ace1359826b284d6409ac62358826b088d60098de131b4263587c6a098d21f1a0263384c66098ca13190263184c61116de0edb445b585b69116ce0ed9445b185b61096be0ed7425ad84b59096ae0ed5425a985b510969e12d2c25a484b47096861ed040d3881a5f094bc06976012e01a5b034b20695c0d2a81a53034a4069440d2801a4f0349a0692c0d2381a4503486068fc0d1d81a3703466225bc44b68296b052d22259e10b282963052c21257db8ae8295b052b21255c24aa82953052a21253c3ca68294b0928e1251414a18e93f052762e4dc14998192f032560649c0c91878660f0c81217824270783e0304c1e0580eb684c5f098ba1316c3e2d04c57098ac1315445b684b5f096ba06d3c452f88a5b114ae2294c252784a4b0948e1290c4d1f89a3b1346e268cc44af8295b112ae0a54c24a78294b0928e0a50c4c9f8293b1326e0a4cc74978292b1724e0a48c3c2b04d6f09ac6371bc46370dc63118c40717c0e2f02c5b058b40715c0e2b01c53038a41adbc75b184b5f096b612d5c25a986b4f0769a36d2c2da486b470768a36d0c2da081a6f034c60697c0d2d81a57034a60693c0d2681a4b034920691c0d2281a4303482068fc0d1d81a37034660a5bc14b18295f052b60655c14a98294f1329c0a534149f8293b0526e0a4cc0c978192b032540649c0c9301923030be0615c0c278184d0308e061140c1f818370305e0609c0c0f81817 18 262143 7 127 11 2047 19 524287
def cc_67_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x9482f8cf798329d7a1917128f66da5624495a57f5753052d484e4494657f435303ed48374793037129d662702d2264a200261e7191c2251a51d154511173d0d74009b3c0693205613043130350e00035 0x5c6106c5f10c5b06c570cc5309b6d09b5f01b5b09b5701b5309b4f01b4b06b4a06b4706b4601b4308a6d7f26c08a5f08a5b08a5708a5308a4f06a4b06a4708a4302a3b0d96d0c95f0295b0d957029530694f0294b0b94a069470b946029430193f0193e0293b02939019330193202931681300192f08e7f08e7306d7f10d7908d7308d7106d6f10d6b06d670cd6308c7f08c7e08c7d08c7c09c757e47409c6f0cc6e11c6b11c6a09c671ec660cc630cc6209c5f1dc5e06c5b06c5a06c5706c5610c5311c5208b7f08b7d09b7501b7309b6f01b6b09b6701b6309b5f01b5b06b5a06b5706b5601b5302b4f02b4e02b4d08a7f08a7e08a7d08a6f07a6e08a6b04a6a08a6704a6608a6307a6208a5f05a5e06a5b03a5a06a5703a5608a5305a5202a3b02a3a08a3702a3601a3301a320897f0897d0d975029730c96f0296b0d967029630695f0295b0b95a069570b956029530194f0194e0194d0193f0193e0293b02939019330193202931671300192f0192d089270192502923029210c86f300671085f068571184f1184d098471c8450183f018370882f0782d08827078250281f0281704e7f04e7b04e7704e7306d7f10d7b06d7710d7304d6f04d6b04d6904d6704d630cd6109c7f15c7e11c7b11c7a09c7712c7611c7311c7204c6f04c6e09c6d0cc6c04c6704c6604c6504c6404c6304c6209c5f14c5e06c5b06c5a06c5706c5610c5311c5209b7f01b7b09b7701b7304b6f09b6d01b6b04b6704b6501b6309b5f01b5b06b5a06b5706b5601b5302b4f02b4e02b4d04a7f08a7e04a7b04a7704a7304a7204a6704a6604a6504a5f05a5e04a5b03a5a04a5703a5604a5304a5204a4f07a4e04a4d07a4c01a3f01a3e02a3b02a3a04a3702a3601a3301a320d97f0297b0d977029730496f0c96d0296b0496704965029630695f0295b0b95a069570b956029530194f0194e0194d0193f0193e0293b029390193301932029310c9300192f0192d0292b02929049270192502923029210787f0187b07877018730486f0186b04867018630785f0185b06857018530784f0784d0184b01849078470784501843018410183f0183b01837018330482f0482d0182b0482707825018230281f0181b028170181304e7f04e7e04e7b04e7704e7308e7204d7f04d7b04d7704d7304d6f04d6e04d6d06c7f10c7b06c7710c7304c6f03c6d04c6b04c6904c6703c6504c6305c6104c5f04c5b04c5704c5309b7f09b7e09b7b12b7a09b7709b7609b731eb7204b6f04b6e07b6d07b6c04b5f04b5e04b5b04b5a04b5904b5804b5304b5209b510cb5009b4f09b4e06b4b06b4a06b4706b4609b4310b4209a7f01a7b09a7701a7304a6f04a6e09a6d0fa6c04a5f01a5b04a5701a5309a4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0d97f0297b0d977029730496f0496e0c96d0c96c0495f0295b04957029530694f0294b0b94a069470b946029430193f0193e0193d0192f0192e0292b029290192301922029210c9200787f0187b07877018730486f0786d0186b0486704865018630485f0c85d0185b0485704855018530784f0184b06847018430783f0783d0183b01839078370783501833018310182f0182b01827018230281f0181b028170181314e7f0ce7b14e770ce7303d7f05d7b03d7705d7303d6f05d6b03d6705d6305c7f08c7e05c7b05c7705c7305c7205c6f07c6e05c6b04c6a05c6704c6605c6305c6205c5f05c5e05c5d09b7f09b7e09b7b1db7a09b7709b7609b731db7209b6f09b6e09b6b14b6a09b6709b6609b630cb6203b5b03b5a06b5906b5803b5703b5605b5305b5205b5105b5003b4703b4603b4503b4409a7f01a7b09a7701a7309a6f01a6b09a6701a6305a5f01a5b03a5a03a5703a5601a5305a4705a4606a4506a4402a3f02a3e02a3d0697f0297b06977029730696f0296b06967029630595f0295b0395a0395703956029530594705946069450b9440193f0193e0193d0192f0192e0292b02929019230192202921069200e87f0187b0e877018730c86f0186b0e867018630585f0185b03857018530584f0584d0184b0584707845018430983f0e83d0183b01839098370983501833018310182f0182b01827018230281f0181b028170181314e7f0ce7b14e770ce7303d7f05d7b03d7705d7303d6f05d6b03d6705d6309c7f10c7e10c7b11c7a09c7710c7610c7311c7209c6f0cc6e10c6b11c6a09c6710c660cc630cc6205c5f05c5e05c5d05c5c03c5b03c5a03c5703c5606c5506c5409b7f01b7b09b7701b7309b6f01b6b09b6701b6305b5f05b5d01b5b03b5a03b5703b5606b5506b5401b5302b4f02b4e02b4d05a7f08a7e05a7b05a7705a7305a7205a6f07a6e05a6b04a6a05a6704a6605a6305a6205a5f05a5e05a5d03a4f03a4e03a4d03a4c01a3f01a3e03a3d01a3c02a3b02a3a05a3702a3605a3502a3401a3301a320697f0297b06977029730696f0296b06967029630595f0595d0295b0395a0395703956069550b954029530194f0194e0194d0193f0193e0293b02939019330193202931069300192f0192d0292b0392a02929029280592705926019250192402923029210e87f0187b0e877018730c86f0186b0e867018630585f0185b03857018530e84f0e84d0184b01849098470e84501843018410183f0183b01837018330582f0582d0182b0582707825018230281f0181b028170181301d6f01d6308c6f08c630cc5f0cc5b0cc570cc5306b6f08b6306b5f03b5d0bb5b06b5703b550bb5306b4f0bb4b06b470bb4308a6f08a6e09a6908a6308a6208a6108a6008a5f08a5e01a5b01a5901a5309a4f09a4b09a4709a4309a3f06a3b06a3709a330196f019630195f0995e0195b01959019530195201951019500194f0194b01947019430193f0193b0193a0193706936019330192f0292e0192d0185f018570184f018470183f018370182f018270181f0181701e7f01e7e01e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6106c7f08c7306c6f03c6d08c6b05c6906c6703c6508c6305c6106c5f0bc5b06c570bc5308b7f08b7e09b7908b7308b7208b7108b7008b6f08b6e08b6d08b6c08b6b02b6902b6302b6202b6102b6009b5f07b5e09b5b04b5a09b5704b5609b5307b5209b4f05b4e06b4b03b4a06b4703b4609b4305b4201a7901a7301a7101a5f01a5b01a5701a5301a4f01a4b01a4a01a4706a4601a4301a3f02a3e01a3d0897f029730896f0896d0296b0896a029690296808967089660d9657816402963029610c95f0295b0c957029530694f0294b0b94a069470b946029430193f0193e0193d0192f0192e0192b02929019230192201921019200186f0186d01867018650185f018570184f018470183f0183d01837018350182f018270181f018170cc6f0cc6b0cc670cc6306b6f03b6d0bb6b06b6703b650bb6306b4f0bb4b06b470bb4301a6301a6109a5109a4f09a4b09a4709a4309a3f05a3e06a3b06a3709a3305a320196b0196a0196901968019670996601963019610194f0194b01947019430193f0193b0193a0193706936019330192f0292e0192d04d7d07d7103c7d05c7106c5f0bc5b06c570bc5308b7d08b7c02b7102b7009b6108b6009b5f07b5e09b5b04b5a09b5704b5609b5307b5209b4f05b4e06b4b03b4a06b4703b4609b4305b4201a7d01a6101a5f01a5b01a5a01a5709a5601a5301a4f01a4b01a4a01a4706a4601a4301a3f02a3e01a3d0d97d7617c02971029700c95f0295b0c957029530694f0294b0b94a069470b946029430193f0193e0193d0192f0192e0192b029290192301922019210192002d6b02d6309c6f09c6b09c6709c6308c5f08c5306b6f03b6d06b6b06b6703b6506b6306b5f06b5306b4f06b4b06b4706b4308a6f08a6e02a6b01a6901a6308a5f08a5e09a5908a5308a5208a5108a5009a4f09a4b09a4709a4306a3f06a3b06a3706a330296f0996e0296b01969019630196201961019600295f029530294f0294b02947029430293f0293b0293a0293706936029330192f0192e0192d0286f028670284f028470283f028370282f028270281f0281702e7f02e7e02e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6106c7f06c7306c6f03c6d06c6b05c6906c6703c6506c6305c6106c5f06c5b06c5706c5308b7f08b7e0db7908b7308b7208b7108b7008b6f08b6e08b6d08b6c08b6b01b6901b6301b6201b6101b600cb5f07b5e0db5b04b5a0db5704b560cb5307b5206b4f05b4e06b4b03b4a06b4703b4606b4305b4208a7f01a7308a6f08a6d01a6b08a6a01a6901a6808a6708a6609a657426401a6301a610ca5f01a5b0ca5701a5306a4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0297902973029710295f0295b02957029530294f0294b0294a0294706946029430193f0193e0193d0192f0192e0292b02929019230192202921029200286f0286d02867028650285f028570284f028470283f0283d02837028350182f018270281f0281709c5f09c5b09c5709c5306b5f03b5d06b5b06b5703b5506b5306b4f06b4b06b4706b4309a6102a5301a5109a4f09a4b09a4709a4306a3f05a3e06a3b06a3706a3305a320195b0195a0195901958029570995602953019510294f0294b02947029430293f0293b0293a0293706936029330192f0192e0192d04d7d07d7103c7d05c7106c5f06c5b06c5706c5308b7d08b7c01b7101b700db6108b600cb5f07b5e0db5b04b5a0db5704b560cb5307b5206b4f05b4e06b4b03b4a06b4703b4606b4305b4209a7d7227c01a7101a700ca5f01a5b0ca5701a5306a4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0297d029610295f0295b0295a029570d956029530294f0294b0294a0294706946029430193f0193e0193d0192f0192e0292b029290192301922029210292007e7f07e7306d7f0ed7306d6f07d6b06d6707d6309c7f1cc7e11c7311c7207c6f07c6e07c6b07c6a07c6707c6607c6307c6209c5f0ec5e06c5b06c5a06c5706c560ec530ec5207b7f08b7e07b7307b7207b6f07b6e07b6b04b6a07b6704b6607b6307b6207b5f05b5e06b5b03b5a06b5703b5607b5305b5201a7f01a7301a6f01a6b01a6701a6301a5f01a5b01a5a01a5706a5601a5301a4f02a4e01a4d01a3f01a3d01a3701a3501a3301a310297f029730296f0296b02967029630295f0295b0295a029570b956029530194f0194e0194d0193f0193d019370193501933019310192f0192e0192b02929019230192201921019200186f018670185f0785e01857018520184a01848018470784601845078440183707836018350182f0182a01827018260181f0181a018170281607e7f07e7306d7f0ed7306d6f07d6b06d6707d6307c7f07c7e07c7308c7207c6f07c6e07c6b04c6a07c6704c6607c6307c6207c5f05c5e06c5b03c5a06c5703c5607c5305c5209b7f09b7e09b731cb7207b6f07b6e07b6b07b6a07b6707b6607b6307b6209b5f09b5e06b5b06b5a06b5706b5609b530eb5201a7f01a7301a6f01a6b01a6701a6301a5f01a5b01a5a01a5706a5601a5301a4f02a4e01a4d02a4c01a3f02a3e01a3d0297f029730296f0296b02967029630295f0295b0295a029570b956029530194f0194e0194d0194c0193f0193e0193d0192f0192e0192b02929019230192201921019200186f0186a01867078660185f018570184f0784e0184d0183f0783e0183d0783c01832018300182f018270181f018179656f0cd6b935670cd6306c6f8e46b06c678946306c5f8445b06c570cc538336f08b6e8136b803677d36308b620cb5f07b5e7c35b04b5a7b35704b560cb5307b527a34f05b4e06b4b03b4a06b4703b467934305b427726f01a6b7526701a630ca5f01a5b0ca5701a530ba4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d7316f0296b71167029630c95f0295b0f957029530694f0294b0b94a069470b946029430193f0193e0193d0192f0192e0292b02929019230192202921651205906f0186b4c067018630c85f0185b2d057018531b04f0184b06847018437003f0783d0183b6f03707835018330182f0182b01827018230281f0181b028170181308c5f01c5308b5f08b530cb4f0cb4b0cb470cb4306a5f06a5306a4f03a4d06a4b06a4703a4506a4306a3f06a3b06a3706a330195f0995908953089510194f0194b0194901943019410993f0993b09937099330692f0692b06927069230184f018470183f018370182f018270181f0181708d6f08d6e08d6d08c6f08c6308c5f04c5d08c5b07c5908c5704c5508c5307c5106b6f06b6306b5f03b5d06b5b05b5906b5703b5506b5305b5106b4f06b4b06b4706b4309a6908a6308a6109a4f09a4b09a4709a4306a3f06a3e06a3b06a3706a3306a320196f019630195708956019556d1540194f0194b01947019430193f0193d0193b0193a01937039360193563134019330192f0992e0192d0185f0185d01857018550184f018470183f018370182f018270181f0181706c6106c5f06c5b06c5706c5309b6d09b5f0cb5b09b570cb5306b4f06b4b06b4706b4307a5e04a5605a4e03a4608a3e0196d0195f0195b01957019530194f0194d0194b0194a01947039460194562144019430193f1193e0193d01929019250cb5f0cb5b0cb570cb5306a5f03a5d06a5b06a5703a5506a5306a3f06a3b06a3706a330195301951099410993f0993b09937099330692f0692b069270692304c6d07c6103b6d05b6106b4f06b4b06b4706b4308a6d09a516825009a4f09a4b09a4709a4306a3f06a3b06a3706a330196d6a16c0194f0194b01947019430193f0193d0193b0193a01937039360193561134019330192f0992e0192d05b5106b4f06b4b06b4706b4308a5d08a4f08a4b08a4708a4306a3f06a3b06a3706a330195d0194f0194b01947019430193f0193d0193b0193a01937039360193560134019330192f08d6f08d6306c6f06c6906c6306c6106c5f06c5b06c5706c5308b6f08b6d09b656836409b5f0cb5b09b570cb5306b4f06b4e06b4b06b4706b4306b4208a6f08a6e08a6d08a5f07a5e08a5b04a5a08a5704a5608a5307a5206a4f05a4e06a4b03a4a06a4703a4606a4305a420196f0196d01965019630195f0195b01957019530194f0194d0194b0194a0194703946019455f144019430193f1193e0193d0192f0192d019270192501923019210185f018570184f018470183f018370182f0182d01827018250181f018170cc5f0cc5b0cc570cc5306b5f06b5b06b5706b5306b4f06b4b06b4706b4309a5f11a5b09a5711a5309a4f0ca4b09a470ca4306a3f06a3b06a3706a331395f1195b13957119530c94f0c94b0c9470c9430693f0693b0393a0693703936069330192f0192e0192d0185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b01817018130cc5f0cc5b0cc570cc5306b5f06b5b06b5706b5306b4f06b4b06b4706b436c25f6b25b69257672530ca4f0ca4b0ca470ca4306a3f06a3b06a3706a330195f0195b01957019530194f0194b01947019430193f0193d0193b0193a0193703936019355e134019330192f6612e0192d0185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b01817018130cc5f0cc5b0cc570cc5305b5f05b5b05b5705b5305b4f05b4b05b4705b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330295f0295b02957029530294f0294b02947029430293f0293b02937029330192f0192b01927019230185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181308c5f08c5e08c5d08b5f08b5308b4f04b4d08b4b07b4908b4704b4508b4307b4103a5f03a5303a4f03a4d03a4b03a4903a4703a4503a4303a4103a3f03a3b03a3703a330995908953089510993f0993b09937099330392f0392e0392b0392703923039220184f0184d01847018450183f018370182f018270181f0181703b5103b4f03b4b03b4703b4309a5d09a4f0ca4b09a470ca4303a3f03a3b03a3703a330794e049460393e039360892e04b5d07b5103a5d03a5103a3f03a3b03a3703a330895d09941601400993f0993b09937099330392f0392b039270392303a4103a3f03a3b03a3703a330894d0893f0893b08937089330392f0392b039270392308c5f08c5303b5f03b5903b5303b5103b4f03b4b03b4703b4308a5f08a5d09a556025409a4f0ca4b09a470ca4303a3f03a3e03a3b03a3703a3303a320895f0895e0895d0894f0794e0894b0494a089470494608943079420393f0393e0393b0393a039370393603933039320184f018470183f018370182f018270181f0181d0181701815 20 1048575 8 255 11 2047 20 1048575
def cc_67_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x9b944956639173f8997e86e2b82a447c466761636e37e6b62d68b2b6494261e2b5f02e5c03059030548484fb4d4b5464625340f533868931e682bb63252691e969140a90d16f0a829063450214200021 0x4d7d07d7103c7d05c7106c5f06c5b06c5706c5301b7d9f37c01b7101b7001b5f01b5b01b5701b5301b4f01b4b01b4a01b4706b4601b4301a7d08a7c01a7101a7001a6d08a6c01a5f07a5e01a5b01a5a01a5704a5601a5301a5201a4f05a4e01a4b01a4a01a4703a4601a4301a4201a3f01a3e01a3d0297d02961029600295f0295b02957029530294f0294b02947029430193b0193a02939019370193601933019310192701926029250cd6f0cd6b0cd670cd6306c6f0bc6b06c670bc6306c5f0bc5b06c570bc5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4a01b4706b4601b4301a6f08a6e01a6b01a6701a6301a6201a5f07a5e01a5b01a5a01a5704a5601a5301a5201a4f05a4e01a4b01a4a01a4703a4601a4301a4201a3f01a3e01a3da016f0296b9e167029630c95f0295b0c957029530694f0294b06947029430193b0193a02939019370193601933019310192701926981250186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b0182701825018230181f0181b018170181301d6f01d6308c6f08c630cc5f0cc5b0cc570cc5306b6f06b6306b5f03b5d06b5b06b5703b5506b5306b4f06b4b06b4706b4301a6f01a6301a5f01a5b01a5901a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330296f0896e02963029620295f1395e0295d0294f0294b02947029430293f0293b02937029330192701926029250185f018570184f018470183f018370182f018270181f0181701e7f01e7e01e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6106c7f06c7306c6f03c6d06c6b05c6906c6703c6506c6305c6106c5f06c5b06c5706c5301b7901b7301b7101b5f01b5b01b5701b5301b4f06b4e01b4b01b4701b4301b4202a7f02a7302a6f02a6d02a6b02a6a02a6902a6802a6708a6602a659c26402a6302a6102a5f02a5b02a5702a5302a4f02a4b02a4a02a4706a4602a4301a3f01a3e01a3d01a3702a3501a3301a320297f0897e0297d0897c0297502973029720296f0896e0296d0896c0296702965029630296202961029600295f0795e0295b0295a029570495602953029520294f0594e0294b0294a029470394602943029420193701936029350192f0192e0192d0186f0186d01867018650185f018570184f018470183f018370182f018270181f0181d01817018150cc6f0cc6b0cc670cc6306b6f03b6d06b6b06b6703b6506b6306b4f06b4b06b4706b4301a6f01a6b01a6901a6301a6101a4f01a4b01a4701a4301a3f01a3b01a3701a330296713966029650294f0294b02947029430293f0593e0293b02937029330293201927019260292504d7d07d7103c7d05c7106c5f06c5b06c5706c5301b7d01b6101b6001b5f01b5b01b5701b5301b4f01b4b01b4701b4302a7d9a27c02a7102a7002a5f02a5b02a5702a5302a4f02a4b02a4a02a4706a4602a4301a3f01a3e01a3d01a3702a3501a3301a320297d0897c02971029700296d0896c0295f0795e0295b0295a029570495602953029520294f0594e0294b0294a029470394602943029420193701936029350192f0192e0192d0cd6f0cd6b0cd670cd6306c6f06c6b06c6706c6306c5f06c5b06c5706c5309b6f08b6e11b6b09b6711b6308b6209b5f07b5e0cb5b04b5a09b5704b560cb5307b5206b4f05b4e06b4b03b4a06b4703b4606b4305b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4a01a4706a4601a4301a3f02a3e01a3d0296f0296b02967029630295f0295b02957029530294f0294b0294a0294706946029430193f0193e0193d0192f0192e0192b02929019230192201921019200186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183d0183b0183701835018330182f0182b01827018230181f0181b01817018130fd6f0cd6b0fd670cd6306c6f06c6b06c6706c6306c5f06c5b06c5706c539b36f01b6b9936701b630cb5f01b5b0cb5701b5306b4f01b4b06b4701b4302a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f02a4b02a4a02a4706a4602a4301a3f01a3e02a3d02a3702a3501a3301a320296f0896e0296b0296702963029620295f0795e0295b0295a029570495602953029520294f0594e0294b0294a029470394602943029420293798136029350192f0192e0192d0286f0186b02867018630285f0185b02857018530284f0184b02847018430183f0183b01837018330282f0182b02827018230281f0281d0181b02817028150181304e7f07e7e04e7d04d7904d7304d7106c7f08c7304c6f03c6d04c6b05c6904c6703c6504c6304c6104c5f04c5b04c5704c5308b7f08b7e08b7308b7204b6f04b6e04b6d04b6c04b6b04b6a11b6912b6804b6704b6609b6512b6404b6304b6204b6104b6004b5f04b5e04b5b04b5a04b5704b5604b5304b5214b4f05b4e06b4b03b4a06b4703b4614b4305b4208a7f01a7304a6f04a6d01a6b01a6904a6709a6501a6301a6104a5f01a5b04a5701a530ba4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0897f029730496f0496d0296b02969049670d96502963029610495f0295b04957029530694f0294b0b94a069470b946029430193f0193e0193d0192f0192e0292b029290192301922029210c9200486f0486d04867078650485f048570784f068470783f0783d07837078350182f018270281f0281704c6f04c6d04c6b04c6904c6704c6504c6304c6106b6f03b6d09b6b05b6906b6703b6509b6305b6104b4f04b4b04b4704b4309a6709a6609a6504a4f01a4b04a4701a4309a3f01a3b06a3701a3309967099660d9650494f0294b04947029430693f0293b06937029330192f0292b0192304c5f04c5b04c5704c5304b5f01b5b04b5701b530bb4f01b4b06b4701b4304a5f04a5e04a5b04a5a04a5704a5604a5304a5211a4f05a4e06a4b03a4a06a4703a4611a4305a4202a3b02a3a0495f0295b04957029530694f0294b06947029430193f0293b019330192f0192d04d7d04d6103c7d05c7104c5f04c5b04c5704c5309b7d9537c11b719437004b5f04b5e04b5b04b5a04b5704b5604b5304b5214b4f05b4e06b4b03b4a06b4703b4614b4305b4209a7d01a7104a5f01a5b04a5701a530ba4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0d97d029710495f0295b04957029530694f0294b0b94a069470b946029430193f0193e0193d0192f0192e0292b029290192301922029210c92003c5f05c5b03c5705c530bb5f01b5b0bb5701b5305b4f01b4b03b4701b430ca5f07a5e10a5b04a5a10a5704a560ca5307a5205a4f05a4e03a4b03a4a03a4703a4605a4305a4202a3b02a3a0695f0295b06957029530594f0294b03947029430193f0293b019330192f0192d03c5f05c5b03c5705c5309b6109b5f07b5e09b5b04b5a09b5704b5609b5307b5205b4f05b4e03b4b03b4a03b4703b4605b4305b4209a5f01a5b09a5701a5305a4f01a4b03a4701a4309a3f09a3e09a3d0695f0295b06957029530594f0294b03947029430693f0993e0693d0192f0292b0192303c5f05c5b03c5705c5309b5f09b5b09b5709b5305b4f01b4b01b4a03b4701b4605b4309a6109a5f09a5b09a5709a5305a4f05a4e03a4b03a4705a4305a4202a3b02a390695f0295b06957029530594f0294b0394a0394703946029430693f0993e0293b02939029330693202931029300192f0192e0192d03c5f05c5b03c5705c530cb5f0db5b0db570cb5305b4f02b4b02b4a03b4702b4605b430da610ca5f0da5b0da570ca5305a4f05a4e03a4b03a4705a4305a4201a3b01a390b95f0195b0b957019530594f0194b0394a0394703946019430b93f0d93e0193b01939019330b93201931019300292f0292e0292d03d7d03d6f05d6b03d6705d6307c6e04c6605c5e10b7108b700cb6f07b6e10b6b04b6a10b6704b660cb6307b6205b5f05b5e03b5b03b5a03b5703b5605b5305b5210b499234809b45913440ba6f01a6b0ba6701a6305a5f01a5b03a5a03a5703a5601a5301a4901a4809a459024402a3f02a3e02a3d0696f0296b06967029630595f0295b0395a0395703956029530294902948069458f1440193f0193e0193d0192f0192e0292b029290192301922029210692008d6f08d6303c6f05c6303c5f05c5b03c5705c5308b6f01b630bb5f01b5b0bb5701b5305b4f01b4b03b4701b4306a6f03a6e03a6303a620ca5f07a5e10a5b04a5a10a5704a560ca5307a5205a4f03a4b03a4a03a4703a4601a3f01a3e02a3b02a3a05a3702a3601a3301a320696f029630695f0295b06957029530594f0294b03947029430193f0293b05937019330192f0192d0292b02929059270192502923029210c85f0e8570584f038470183f018370e82f0782d0e827078250281f0281708d6f08d6303c6f05c6303c5f05c5b03c5705c5303b6f03b6e09b6906b6303b6206b6103b6009b5f07b5e09b5b04b5a09b5704b5609b5307b5203b4b03b4a03b4703b4605b4308a6f01a6309a5f01a5b09a5701a5305a4f01a4b03a4701a4309a3f09a3e09a3d0696f029630695f0295b06957029530594f0294b03947029430693f0993e0693d0192f0292b05927019230c85f0e8570584f038470983f0783d09837078350182f018270281f0281708d6f08d6303c6f05c6303c5f05c5b03c5705c5303b6f06b6309b5f09b5b09b5709b5301b4b01b4a03b4701b4605b4308a6f08a6e09a6908a6308a6208a6108a6009a5f09a5b04a5a09a5704a5609a5305a4f05a4e03a4b03a4705a4305a4205a3f05a3e02a3b02a3905a3705a3305a3202a3102a300696f029630695f0295b06957029530594f0294b0394a0394703946029430693f0993e0293b0293905937029330693202931029300192f0192e0192d0c85f0e8570584f038470983f098370982f0782d09827078250281f0281708d6f08d6303c6f05c6303c5f05c5b03c5705c5303b6f06b630cb5f0db5b0db570cb5302b4b02b4a03b4702b4605b4308a6f08a6e0da6908a6308a6208a6108a600ca5f0da5b04a5a0da5704a560ca5305a4f05a4e03a4b03a4705a4305a4205a3f05a3e01a3b01a3905a3705a3305a3201a3101a300896f019630b95f0195b0b957019530594f0194b0394a0394703946019430b93f0d93e0193b0193905937019330b93201931019300292f0292e0292d0c85f0e8570584f038470d83f0d8370d82f0782d0d827078250181f0181708e7f08e7303d7f03d7d03d7503d6f05d6b03d6705d6303c7f03c7e03c7d05c6f07c6e05c6b04c6a05c6704c6605c6305c6208b7f08b7e10b7908b7308b7208b7108b700cb6f07b6e10b6b04b6a10b6704b660cb6307b6205b5f05b5e03b5b03b5a03b5703b5605b5305b5205b4f05b4e05b4d05b4c05b4b05b4a10b498d34805b4705b4609b458c34405b4305b4205b4105b4008a7f01a730ba6f01a6b0ba6701a6305a5f01a5b03a5a03a5703a5601a5305a4f05a4d01a4b05a4a01a4901a4805a4705a4609a458b24401a4301a4102a3f02a3e02a3d0697f029730696f0296b06967029630595f0295b0395a0395703956029530594f0594d0294b0594a02949029480594705946069458a14402943029410193f0193e0193d0192f0192e0292b02929019230192202921069200c86f0e8670585f038570584f0584d05847078450e83f0783d0e837078350182f018270281f0281704d6f04d6b04d6704d6303c6f05c6b03c6705c6303c5f04c5b03c5704c530bb6f01b6b0bb6701b6304b5f01b5b04b5701b5305b4f01b4b03b4701b4310a6f08a6e10a6b10a6710a6308a6204a5f04a5e03a5b03a5a04a5703a5604a5304a5205a4f05a4e03a4b03a4a03a4703a4605a4305a4201a3f01a3e02a3b02a3a04a3702a3601a3301a320696f0296b06967029630495f0295b04957029530594f0294b03947029430193f0293b04937019330192f0192d0292b02929049270192502923029210786f0186b07867018630485f0185b04857018530584f0184b03847018430183f0183b01837018330782f0782d0182b0782707825018230281f0181b028170181304d6f04d6b04d6704d6303c6f05c6b03c6705c6303c5f04c5b03c5704c5309b6f08b6e09b6b09b6709b6308b6204b5f04b5e04b5b03b5a04b5903b5803b5703b5604b5304b5209b5105b4f05b4e03b4b03b4a03b4703b4605b4305b4209a6f01a6b09a6701a6304a5f01a5b04a5701a5305a4f01a4b03a4701a4309a3f09a3e09a3d0696f0296b06967029630495f0295b04957029530594f0294b03947029430693f0993e0693d0192f0292b04927019230786f0186b07867018630485f0c85d0185b0485704855018530584f0184b03847018430783f0783d0183b0783707835018330182f0182b01827018230281f0181b028170181304d6f04d6b04d6704d6303c6f05c6b03c6705c6303c5f04c5b03c5704c5309b6f09b6b09b6709b6304b5f04b5b03b5701b5305b4f01b4b01b4a03b4701b4605b4309a6f09a6b09a6709a6304a5f04a5b04a5a04a5904a5704a5604a5309a5105a4f05a4e03a4b03a4705a4305a4204a3f04a3e02a3b02a3904a3704a3304a3202a3102a300696f0296b06967029630495f0295b04957029530594f0294b0394a0394703946029430693f0993e0293b0293904937029330693202931029300192f0192e0192d0786f0186b07867018630485f0c85d0185b0485704855018530584f0184b03847018430783f0183b07837018330782f0182b07827018230281f0181b028170181304d6f04d6b04d6704d6303c6f05c6b03c6705c6303c5f04c5b03c5704c530db6f0db6b0db670db6304b5f04b5b03b5702b5305b4f02b4b02b4a03b4702b4605b430da6f0da6b0da670da6304a5f04a5b04a5a04a5904a5704a5604a530ca5105a4f05a4e03a4b03a4705a4305a4204a3f04a3e01a3b01a3904a3704a3304a3201a3101a300b96f0196b0b967019630495f0195b04957019530594f0194b0394a0394703946019430b93f0d93e0193b0193904937019330b93201931019300292f0292e0292d0786f0186b07867018630485f0c85d0185b0485704855018530584f0184b03847018430783f0183b07837018330782f0182b07827018230181f0181b018170181304e7f04e7b04e7704e7303d7f05d7b03d7705d7303d6f04d6e03d6d03d6703d6504d6304d6204c7f08c7e04c7b04c7704c7304c7203c6703c6603c6504c5f05c5e04c5d10b7f08b7e10b7b10b7710b7308b7204b6f04b6e04b6b04b6a04b6904b6804b6704b6604b6304b620cb6107b6005b5f05b5e03b5b03b5a03b5703b5605b5305b5204b4f04b4e04b4d04b4c04b4b04b4a10b498834804b4704b4609b458734404b4304b4204b4104b400ba7f01a7b0ba7701a7304a6f01a6b04a6701a6305a5f01a5b03a5a03a5703a5601a5304a4f04a4d01a4b04a4a01a4901a4804a4704a4609a458624401a4301a4102a3f02a3e02a3d0697f0297b06977029730496f0296b04967029630595f0295b0395a0395703956029530494f0494d0294b0494a02949029480494704946069458514402943029410193f0193e0193d0192f0192e0292b02929019230192202921069200787f0187b07877018730486f0c86d0186b0486704865018630585f0185b03857018530484f0484d0184b0484707845018430783f0783d0183b0783707835018330182f0182b01827018230281f0181b028170181308e7f08e7e08e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6106c7f08c7306c6f03c6d08c6b05c6906c6703c6508c6305c6106c5f10c5b06c570cc5309b798237808b7308b7208b7108b7009b5f09b5e09b5b15b5a09b5709b5609b530cb5209b4f09b4e06b4b06b4a06b4706b4609b4310b4208a7f01a7308a6708a6609a657426409a5f01a5b09a5701a5309a4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0897f0297308967089660d965781640c95f0295b0d957029530694f0294b0b94a069470b946029430193f0193e0193d0192f0192e0292b029290192301922029216c1200886f0786d08867078650c85f158571084f068470983f1c83d09837098350182f018270281f0281708d6f08d6b08d6708d6306c6f08c6b05c6906c6708c6305c6106c5f10c5b06c570cc5308b6708b6609b6509b5f01b5b09b5701b5309b4f01b4b06b4701b4308a667f26408967089660d9650c95f0295b0d957029530694f0294b06947029430193f0293b0193310d7106d6f10d6b06d670cd6309c7d8247c09c6f0cc6e11c6b11c6a09c6712c660cc630cc6209c5f1dc5e06c5b06c5a06c5706c5610c5311c5209b7d09b6f01b6b09b6701b6309b5f01b5b06b5a06b5706b5601b5302b4f02b4e02b4d07a6e04a6605a5e03a5608a4e08a4c01a3e02a360d97d0c96f0296b0d967029630695f0295b0b95a069570b956029530194f0194e0194d0193f0193e0293b029390193301932029316b130029290192504d7d07d7103c7d05c7106c5f10c5b06c570cc5308b7d08b7c09b617e36009b5f09b5e09b5b12b5a09b5709b5609b530cb5209b4f09b4e06b4b06b4a06b4706b4609b4310b4209a7d7227c09a5f01a5b09a5701a5309a4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0d97d7617c0c95f0295b0d957029530694f0294b0b94a069470b946029430193f0193e0193d0192f0192e0292b029290192301922029216912012c5f0cc5b12c570cc5306b5f10b5b06b5710b5306b4f10b4b06b470cb4308a5709a4f01a4b09a4701a4309a3f01a3b06a3701a33089570c94f0294b0d947029430693f0293b06937029330192f0292b01923 20 1048575 8 255 11 2047 20 1048575
def cc_67_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x8e2188a43e83f657c47b7982c757416f46369163610815e52b5a44153f654f04f4737d4472c4192e3d64339a3c3475331f282a47b2584c2352321c191f6261da1c18d4d14d400e8650a93f02b7e0002b 0x6b4f04b4b04b4706b4301a4f01a4b01a4701a4301a3f01a3b01a3701a330294f0294b02947029430293f0293b02937029330192f0192b019270192304c5f07c5b04c5707c5306b5f06b5b06b5706b5306b4f04b4b04b4706b430ca5f0ca5b0ca570ca5307a4f04a4b04a4707a4306a3f06a3b06a3706a330295f0295b02957029530294f0294d0294b0294702945029430293f0293b02937029330292f0292b02927029230285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281b028170281304d6f07d6b04d6707d6306c6f06c6b06c6706c6306c5f04c5b04c5706c530cb6f0cb6b0cb670cb6307b5f04b5b04b5707b5306b4f06b4b06b4706b4302a6f02a6b02a6702a6302a5f02a5d02a5b02a5a02a5704a5602a5502a4f02a4b02a4702a4302a3f02a3b02a3702a330296f0896e0296b0296702963029620295f0795e0295d0294f0594e0294b0294a029470394602943029420293f0193e0293b0293a029370c93602933019320292f0292e0292d0286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281d0281b0281abe018028170281602815bd0140281301e7f01e7e01e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6103c7f05c7303c6f03c6d05c6b05c6903c6703c6505c6305c6103c5f05c5b03c5705c5305b7f06b7e05b7305b7205b6f06b6e05b6d06b6c05b6b05b6a05b6905b6805b6706b6605b6506b6405b6305b6205b6105b6005b5f06b5e05b5b04b5a05b5704b5605b5305b5202b4f02b4e02b4d01a7901a7301a710ba5f01a5b0ba5701a5305a4f05a4d01a4b03a4706a4501a4305a3f05a3d01a3b01a3905a3706a3501a3301a310697f029730696f0696d0296b02969069670696502963029610695f0295b06957029530294b0394a02949039470394602943029410393703936039350192f0292b06927019230886f0786d08867078650c85f0e8570584f038470583f0583d05837068350182f018270281f028170dc6f0cc6b0dc670cc6303b6f03b6d05b6b05b6a03b6706b6603b6503b4f05b4b03b4705b4303a6f03a6d05a4f05a4b05a4705a4302a3f02a3e02a3d0896f0196b06967019630b94f0194b0b947019430593f0593d0193b0393706935019330592f0592d0192b05927069250192304d7d07d7103c7d05c7103c5f05c5b03c5705c5305b7d06b7c05b7105b7005b5f06b5e05b5b04b5a05b5704b5605b5305b5202b4f02b4e02b4d08a7d01a610ba5f01a5b0ba5701a5305a4f05a4d01a4b03a4706a4501a4305a3f05a3d01a3b01a3905a3706a3501a3301a310697dba17c02971029700695f0295b06957029530294b0394a02949039470394602943029410393703936039350192f0292b069270192314d6f0fd6b14d670fd6303c6f05c6b03c6705c6303c5f05c5b03c5705c5305b6f06b6e05b6b05b6705b6305b6205b5f06b5e05b5b04b5a05b5704b5605b5305b5202b4f02b4e02b4dbb26f0ba6bb92670ba630fa5f0ba5b14a570ba5305a4f05a4d03a4b03a4706a4505a4305a3f05a3d05a3b01a3905a3706a3505a3301a310696f0296b06967029630695f0295b06957029530294b0394a02949039470394602943029410393703936039350692f0292b06927029230e86f0286b0e867028630e85f0285b0e857028530584f0284b03847028430583f0583d0283b0583706835028330b82f0282b0e827028230281f0281b02817028130fd6f0fd6b0fd670fd6303c6f03c6b03c6703c6303c5f03c5b03c5703c530bb6f0bb6b0bb670bb630bb5f0bb5b0bb570bb5303b4f03b4b03b4703b4302a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f03a4e02a4d02a4702a4502a4302a4202a3f02a3b02a3a02a370ba3602a330296f0896e0296b0296702963029620295f0795e0295b0295a029570495602953029520294703946029450293f0193e0293b0293a029370b93602933019320292f0292e0292d0286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281d0281b02817028150281304e7f07e7e04e7d04d7904d7304d7103c7f03c7e03c7308c7203c6f03c6e03c6d03c6c03c6b04c6a03c6912c6803c6703c6603c6503c6403c6304c6203c6104c6003c5f03c5e03c5b04c5a03c5904c5803c5703c5603c5304c5203c5107c5003b7f03b7303b6f03b6d03b6b03b6903b6703b6503b6303b6103b5f03b5b03b5703b5302b4f02b4e02b4d08a7f08a7304a6f04a6d04a6b01a6904a670ba6504a6301a6104a5f04a5b04a5704a5303a4f0ba4d03a4b01a4903a4703a4503a4301a4103a3f0ba3d03a3b03a3703a3503a330697f029730496f0496d0296b02969049670696502963029610495f0295b04957029530394f0394e0594d0393f0393e0293b029390293303932029310692f0292b0692a069270b926029230486f0486d04867078650485f048570384f0784d03847038450383f038370782f078270281f0281703c5f03c5b03c5703c5303b5f03b5e04b5b04b5a03b5703b5603b5303b5202b4b02b4a04a5f04a5b04a5704a5303a4f03a4b03a4703a430ba3f09a3d0ba3b01a390ba3709a350ba3301a310495f0295b04957029530394f0294b029430593f0593d0692f0292b069270292304d7d04d6103c7d03c7c03c71b547003c5f03c5e03c5b04c5a03c5703c5603c5304c5203b7d03b7103b5f03b5b03b5703b5302b4f02b4e02b4d0ba7d01a7104a5f04a5b04a5704a5303a4f0ba4d03a4b01a4903a4703a4503a4301a4103a3f0ba3d03a3b03a3703a3503a330697d029710495f0295b04957029530394f0394e0594d0393f0393e0293b029390293303932029310692f0292b0692a069270b92602923b656f0fd6bb45670fd6303c6f03c6e03c6b03c6703c6308c6203c5f03c5e03c5b04c5a03c5703c5603c5307c5203b6f03b6b03b6703b6303b5f03b5b03b5703b5302b4f02b4e02b4d0ba6f0ba6b0ba670ba630ba5f0ba5b0ba570ba5303a4f0ba4d03a4b01a4903a4703a4503a4301a4103a3f0ba3d03a3b03a3703a3503a330696f0296b06967029630695f0295b06957029530394f0394e0594d0393f0393e0293b029390293303932029310692f0292b0692a069270b926029235a06f0286b4f067028630f85f0285b32057028530384f0784d0284b0384703845028430383f0283b03837028330b82f0282b0b827028230281f0281b028170281301d6f01d6e02d6301d6208c6f08c630fc5f04c5d0cc5b07c590fc5704c550cc5307c5103b6f05b6303b5f03b5d05b5b05b5903b5703b5505b5305b5103b4f05b4b03b4705b4302a6f01a6302a5f01a5b02a5a01a5901a5801a5301a510ba4f01a4b0ba4701a4305a3f01a3b03a3701a330296f029630295f0295d0295b02959029570295502953029510294f0294b02947029430293f0293b02937029330192f0292b02927019230285f0285d02857028550284f028470283f028370182f018270281f0281701e7f01e7e01e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6103c7f05c7303c6f03c6d05c6b05c6903c6703c6505c6305c6103c5f05c5b03c5705c5301b7901b7301b710bb5f01b5b0bb5701b5305b4f01b4b03b4701b4302a7f02a7302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f02a5b02a5702a5302a4f02a4d02a4b02a4a02a4703a4602a4501a3f02a3b02a3701a330297f0897e02973029720296f0896e0296d0896c0296b0296a0296902968029670896602965b2164029630296202961029600295f0795e0295b0295a029570495602953029520294f0594e0294d0193f0193e0293d0193c0293b0293a029370993602935ac13401933019320292f0292e0292d0286f0286d02867028650285f028570284f028470183f018370282f028270281f0281d02817028150dc6f0cc6b0fc670cc6303b6f03b6d03b6703b6505b6303b4f05b4b03b4705b4308a6f01a6b02a6701a630ba4f01a4b0ba4701a4305a3f01a3b03a3701a330296710966029650294f0294b02947029430293f0593e0293d0192f0292d0292b0292a029270992602925a7124019230fc6f04c6d0cc6b07c690fc6704c650cc6307c6105b6305b6103b4f05b4b03b4705b4308a6f08a6e08a6d01a6b01a6902a6702a6501a6302a6201a6101a600ba4f01a4b0ba4701a4305a3f01a3b03a3701a3302963029610294f0294b02947029430293f0293b029370192f0292b029270192304d7d07d7103c7d05c7103c5f05c5b03c5705c5308b7d01b610bb5f01b5b0bb5701b5305b4f01b4b03b4701b4302a7db027c02a7102a7002a5f02a5b02a5702a5302a4f02a4d02a4b02a4a02a4703a4602a4501a3f02a3b02a3701a330297daf17c02971029700295f0795e0295b0295a029570495602953029520294f0594e0294d0193f0193e0293d0193c0293b0293a029370993602935ab13401933019320292f0292e0292d0cc5f0cc5b0cc570cc5303b5f05b5b03b5705b5303b4f05b4b03b4705b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330295f0295b02957029530294f0294b02947029430293f0293b02937029330192f0192b01927019230185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181301d6f01d6e01d6d08c6f08c6308c5f04c5d08c5b07c5908c5704c5508c5307c5103b6f05b6303b5f03b5d05b5b05b5903b5703b5505b5305b5103b4f05b4b03b4705b4302a6f09a6908a6308a6102a5f02a5d02a5b02a5902a5302a5109a4f09a4b09a4709a4305a3f01a3b03a3705a330296f029630295f0295d0295b02959029570295502953029510294f0294b02947029430293f0293d0293b0293a029370393602935029330192f0292b02927029230285f0285d02857028550284f028470283f028370282f028270281f0281704c6d07c6103b6d05b6103b4f05b4b03b4705b4308a6d02a6102a6009a5108a5009a4f09a4b09a4709a4305a3f01a3b03a3705a330296da716c02961029600294f0294b02947029430293f0293d0293b0293a0293703936029350192f0292b02927029230fd6f0cd6b0fd670cd6303c6f05c6b03c6705c6303c5f05c5b03c5705c5309b6f08b6e11b6b09b6711b6308b6209b5f07b5e0fb5b04b5a09b5704b560cb5307b5205b4f05b4e01b4b01b4a03b4701b4605b4305b4209a6fac26e01a6b0ba6a09a67ab26601a630ba6209a5f0fa5e01a5b0ba5a09a570fa5601a530ba5205a4f05a4e01a4b03a4a03a4703a4601a4305a4202a3f02a3e02a3d0296f0296b02967029630295f0295b02957029530294f0294d0294b0294a029470394602945029430193f0193d0293b02939029370193502933029310192f0292d0292b02929029270292501923029210286f0186b02867018630285f0185b02857018530284f0184b02847018430283f0283d0183b0283702835018330182f0282d0182b02829018270282501823028210281f0181b028170181308d6f08d6e08d6d08c6f08c6308c5f04c5d08c5b07c5908c5704c5508c5307c5103b6f05b6303b5f03b5d05b5b05b5903b5703b5505b5305b5103b4f05b4b03b4705b4309a6908a6308a6109a4f09a4b09a4709a4305a3f03a3b03a3705a330296f029630295f0295d0295b02959029570295502953029510294f0294b02947029430293f0293d0293b0293a029370393602935029330292f0292b02927029230285f0285d02857028550284f028470283f028370282f028270281f0281703c5f05c5b03c5705c5309b6d09b5f0fb5b09b570fb5305b4f03b4b03b4705b4307a5e04a5605a4e03a4608a3e0295f0295b02957029530294f0294d0294b0294a0294703946029450293f0293b029370293302929029250db5f0fb5b0fb570db5303a5f03a5d03a5703a5505a5303a3f05a3b03a3705a330895f0295b02957029530993f0993b09937099330592f0392b039270592304c6d07c6103b6d05b6103b4f05b4b03b4705b4308a6d09a51a525009a4f09a4b09a4709a4305a3f03a3b03a3705a330296da716c02961029600294f0294b02947029430293f0293d0293b0293a0293703936029350292f0292b029270292303b4f05b4b03b4705b4308a5d08a4f08a4b08a4708a4305a3f03a3b03a3705a330294f0294b02947029430293f0293d0293b0293a0293703936029350292f0292b029270292308d6f08d6303c6f05c6303c5f05c5b03c5705c5308b6f08b6d09b65a536409b5f0fb5b09b570fb5305b4f03b4b03b4705b4308a6f08a6e08a6d08a5f07a5e08a5b04a5a08a5704a5608a5307a5205a4f05a4e03a4b01a4a03a4703a4605a4305a420296f029630295f0295b02957029530294f0294d0294b0294a029470394602945029430293f0293b02937029330292f0192d0292b02929029270292502923029210285f028570284f028470283f028370282f0282d02827028250281f028170fc5f0fc5b0fc570fc5303b5f05b5b03b5705b5303b4f05b4b03b4705b43a925fa825ba6257a42530fa4f0fa4b0fa470fa4305a3f03a3b03a3705a330295f0295b02957029530294f0294b02947029430293f0293d0293b0293a029370393602935029330292f0292b02927029230285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281b02817028130fd6f0fd6b0fd670fd6303c6f05c6b03c6705c6303c5f05c5b03c5705c53b136f0bb6bae3670bb630fb5f0bb5b0fb570bb5305b4f03b4b03b4705b4302a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f02a4d02a4b02a4a02a4703a4602a4502a3f02a3b02a3702a330296f0896e0296b0296702963029620295f0795e0295b0295a029570495602953029520294f0594e0294d0293f0193e0293dad13c0293b0293a02937aa13602935a313402933019320292f0292e0292d0286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281d0281b02817028150281302d6b01d630cc6f09c6b09c670cc6308c5f08c5306b6f03b6d06b6b06b6703b6506b6306b5f06b5306b4f06b4b06b4706b4301a6f13a6e01a6d01a5f08a5e01a5301a5201a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0196b0196901963019610195f029530294f0294b02947029430293f0293b02937029330192701926029250186f018670184f018470183f018370182f018270181f0181702e7f02e7e02e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6106c7f06c7306c6f03c6d06c6b05c6906c6703c6506c6305c6106c5f06c5b06c5706c5301b7f01b7301b6f01b6d01b6b01b6a01b6901b6801b6708b6601b65a136401b6301b6101b5f01b5b01b5701b5301b4f01b4b01b4a01b4706b4601b4301a7f08a7e01a7d08a7c01a7501a7301a7201a6f08a6e01a6d08a6c01a6701a6501a6301a6201a6101a6001a5f07a5e01a5b01a5a01a5704a5601a5301a5201a4f05a4e01a4b01a4a01a4703a4601a4301a4201a3f01a3e01a3d0297902973029710295f0295b02957029530294f0694e0294b0294702943029420193b0193a02939019370193601933019310192701926029250186f0186d01867018650185f018570184f018470183f018370182f0182d01827018250181f0181709c5f0cc5b0cc5709c5306b5f03b5d06b5b06b5703b5506b5306b4f06b4b06b4706b4301a5713a5601a5501a4f01a4b01a4701a4301a3f05a3e01a3b01a3701a3301a320295f0195b0195901953019510294f0294b02947029430293f0293b0293702933019270192602925 20 1048575 8 255 11 2047 20 1048575
def cc_67_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9802d290e2337dc40cc8349af77e5d03db62fb6769ec474d69beaaf4852a68a1481359a2552c4698287ab103d71fb193ce507170cdad018cd22d1904dd8c88668d47913fd21bd8418fd80063 0x2b6e02b6201b5e04b5a04b5601b5205b4e01b4a01b4605b4204a3d01a3904a3501a3102939029310692d069250c85d048550783d0783502e7e02e7d04d6d04d6904d6504d6103c6d05c6903c6505c6108b7e08b7208b6e08b6d08b6c08b6a19b69de36808b6609b6509b6408b6208b6108b6001b5e03b5a03b5601b5205b4e01b4a01b4605b4208a6d01a6909a6501a6104a5a04a5605a4e05a4204a3e04a3d02979029710693d0293906935029310692d069250786d078650c85d048550783d0783502e7f02e7e02e7d04d7f04d7304d6f04d6d04d6b04d6904d6704d6504d6304d6103c7f05c7303c6f03c6d05c6b05c6903c6703c6505c6305c6103c5f04c5e03c5d03c5703c5504c5304c5204b7f08b7e04b7304b7204b6f08b6e04b6d08b6c04b6b04b6a04b6904b6804b6708b6604b65df36404b6304b6204b6104b6003b5703b5603b5504b4f05b4e04b4d08a7f08a7308a6f08a6d08a6b01a6908a6716a6508a6301a6104a5f04a5b04a5704a5305a4f03a4b03a4705a4304a3f04a3d04a3b01a3904a37dd23504a3301a310297902973029710495f0295b04957029530594f0294b03947029430493f0493d0293b02939049370693502933029310692f0292b06927029230786f0786d07867078650485f0e85d04857048550584f038470483f0483d04837078350782f078270281f0281702d6b02d6908d6302d6113c6f04c6d09c6b07c6909c6704c650cc6307c6108c5f08c5306b6f03b6d09b6b05b6906b6703b6513b6305b6106b5f08b5306b4f16b4b06b470cb4308a6f08a6e08a6d08a5f08a5e01a5308a5209a4f01a4b09a4701a4309a3f01a3b06a3701a331396f0296b0196901963019610895f029530c94f0294b0f947029430693f0293b06937029330192fa112d0292b0992774125019231386f0786d09867078650c84f3a0471683f068370182f018270281f0281702d6b02d6901d6301d6104c6f04c6d04c6b04c6904c6704c6504c6304c6104c5f04c5306b6f03b6d0bb6b05b6906b6703b650bb6305b6106b5f08b5304b4f04b4b04b4704b4301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0196b0196901963019610195f029530494f0294b04947029430693f0293b06937029330192f0192b01927019230186f0186d01867018650184f018470183f018370182f018270181f0181702e7f02e7e02e7d04d7f04d7304d6f04d6d04d6b04d6904d6704d6504d6304d6106c7f08c7306c6f03c6d08c6b05c6906c6703c6508c6305c6104c5f04c5b04c5704c5301b7f01b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f04b5e01b5d01b5701b5501b5301b5201b4f01b4b01b4701b4301a7f08a7e01a7301a7201a6f08a6e01a6d08a6c01a6b01a6a01a6901a6801a6708a6601a65da26401a6301a6201a6101a6001a5704a5601a5501a4f05a4e01a4b01a4a01a4703a4601a4301a4201a3f01a3e01a3d0297902973029710495f0295b04957029530694f0294b06947029430193f0193b01937019330192f0192d0192b02929019270d92501923019210186f0186d01867018650185f018570184f018470183f018370182f0182d01827018250181f0181702e7f02e7e02e7d04d7f04d7e04d7308d7204d6f04d6e04d6d04d6c04d6b08d6a04d690cd6804d6704d6604d6504d6404d6308d6204d6108d6004c7f04c7304c6f04c6d04c6b04c6904c6704c6504c6304c6101c5f01c5e01c5d06b7f08b7306b6f03b6d08b6b05b6906b6703b6508b6305b6104b5f03b5d04b5b04b5904b5703b5504b5305b5104b4f04b4b04b4704b4308a7f01a7308a6f08a6d01a6b01a6908a6709a6501a6301a6104a5f04a5e07a5d04a4f04a4e01a4b01a4901a4304a4201a410ba3f01a3b06a3701a330297902973029710495f0c95d0295b02959049570495502953029510494f0294b04947029430693f0293b06937029330192f0292b0c927019230786f0786d07867078650485f0785d04857048550484f0c84d04847048450783f068370182f018270281f0281702e7f02e7e02e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6103c7f05c7303c6f03c6d05c6b05c6903c6703c6505c6305c6103c5f05c5b03c5705c5305b7f08b7e05b7305b7205b6f08b6e05b6d08b6c05b6b05b6a05b6905b6805b6708b6605b650bb6405b6305b6205b6105b6005b5f07b5e05b5b04b5a05b5704b5605b5305b5201b4f01b4e01b4d08a7f01a7308a6f08a6d01a6b01a6908a6709a6501a6301a610ba5f01a5b0ba5701a5301a4b03a4a01a4903a4703a4601a4301a4103a3703a3603a350297902973029710695f0295b06957029530594f0594d0294b0394706945029430593f0593d0293b02939059370693502933029310192f0292b06927019230886f0786d08867078650c85f0e8570584f038470583f0583d05837078350182f018270281f0281702d6b02d6901d6301d610cc6f04c6d0cc6b07c690cc6704c650cc6307c6108c5f08c5303b6f03b6d05b6b05b6903b6703b6505b6305b6103b5f05b5303b4f05b4b03b4705b4301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0196b0196a019690196801963019610195f029530694f0294b06947029430593f0293b03937029330192f0192b01927019230186f0186d01867018650184f018470183f018370182f018270181f0181702d6f02d6e02d6d08c6f08c6308c5f04c5d08c5b07c5908c5704c5508c5307c5103b6f05b6303b5f03b5d05b5b05b5903b5703b5505b5305b5103b4f05b4b03b4705b4301a6f01a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3d01a3b01a3a01a3703a3601a3501a330196f0d96908963089610195f0195d0195b0195901953019510c94f0c94b0c9470c9430593f0293b03937059330192f0192b01927019230185f0185d01857018550184f018470183f018370182f018270181f0181702e7f02e7e02e7d08d7f08d7308d6f04d6d08d6b07d6908d6704d6508d6307d6103c7f05c7303c6f03c6d05c6b05c6903c6703c6505c6305c6103c5f05c5b03c5705c5301b7f01b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4d01b4b01b4a01b4703b4601b4501a7f08a7e01a7301a7201a6f08a6e01a6d08a6c01a6b01a6a01a6901a6801a6708a6601a65d626401a6301a6201a6101a6001a5f07a5e01a5b01a5a01a5704a5601a5301a5201a4f05a4e01a4d01a3f01a3e01a3d0297902973029710695f0295b06957029530594f0294b03947029430193f0193b01937019330192f0192d0192b0192a0292902928019270192606925d512401923019210186f0186d01867018650185f018570184f018470183f018370182f0182d01827018250181f0181702d6f02d6e02d6d08c6f08c6308c5f04c5d08c5b07c5908c5704c5508c5307c5106b6f08b6306b5f03b5d08b5b05b5906b5703b5508b5305b5106b4fdc34b06b470fb4308a6f08a6308a5f08a5d08a5b01a5908a57db25508a5301a510fa4fd924bd82470fa43d723f06a3b06a37d42330296902963029610f94f0294b0f947029430693f0293b0693702933a012f0292b73127029230885f0785d08857078550f84f380472303f068371302f0f0270281f0281706c5f06c5b06c5706c5309b5f07b5e0fb5b04b5a09b5704b560cb5307b5206b4f05b4e06b4b03b4a06b4703b4606b4305b4209a5f01a5b09a5701a5306a4f01a4b06a4a06a4706a4601a430295f0295b02957029530294f0294b02947029430193f0193d0293b02939029370193502933029310192f0292b0292902927019230292106c5f06c5b06c5706c530fb5f0fb5b0fb570fb5306b4f06b4b06b4706b4302a6d02a5f02a5b02a5702a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330795e049560594e039460193ed21360292e09c5f04c5d0cc5b07c5912c5704c5509c5307c5106b5f03b5d13b5b05b5906b5703b5509b5305b5106b4f12b4b06b470cb4309a4f01a4b09a4701a4309a3fcf23e01a3b06a3701a33cd2320895f0895d0195b01959139570895502953019510c94f0294b0f947029430693f0293b06937029330192f9f12d0292b09927721250192309c5f09c5b09c5709c5303b5f03b5d05b5b05b5a03b5706b5603b5503b4f05b4b03b4705b4303a5f03a5d05a4f05a4b05a4705a4301a3f01a3e01a3d0695f0195b06957029530694f0294b06947029430593f0593d0293b0393706935029330592f0592d0292b05927069250292304d7d07d7103c7d05c7103c5f05c5b03c5705c5305b7d0bb7c05b7105b7005b5f07b5e05b5b04b5a05b5704b5605b5305b5201b4f01b4e01b4d09a7dcf27c01a7101a700ba5f01a5b0ba5701a5301a4b03a4a01a4903a4703a4601a4301a4103a3703a3603a350697d029610695f0295b06957029530594f0594d0294b0394706945029430593f0593d0293b02939059370693502933029310192f0292b069270192309c5f0cc5b0cc5709c5303b5f03b5d03b5703b5505b5303b4f05b4b03b4705b4301a5713a5601a5501a4f01a4b01a4701a4301a3f05a3e01a3d0695f0195b01957019530694f0294b06947029430593f0293b03937029330192f0192d0192b0192a019270192606925cb124019230cc5f04c5d0cc5b07c590cc5704c550cc5307c5105b5305b5103b4f05b4b03b4705b4301a5301a5101a4f01a4b01a4701a4301a3f01a3b01a370695f0895e0695d0195b019590195701955019530195201951019500694f0294b06947029430593f0293b03937029330192f0192b019270192309b4f0cb4b0cb4709b4303a4f03a4d03a4703a4505a4303a3f05a3b03a3705a330694f0194b01947019430c93f0c93b0c9370c9330592f0292b039270592304c6d07c6103b6d05b6103b4f05b4b03b4705b4301a6dcb26c01a6101a6001a4f01a4b01a4701a4301a3f01a3d01a3b01a3a01a3703a3601a350896d01961019600d951089500c94f0c94b0c9470c9430593f0293b03937059330192f0192b019270192304d7d07d7103c7d05c7103c5f05c5b03c5705c5301b7dcd37c01b7101b7001b5f01b5b01b5701b5301b4f01b4d01b4b01b4a01b4703b4601b4501a7dcc27c01a7101a7001a5f07a5e01a5b01a5a01a5704a5601a5301a5201a4f05a4e01a4d01a3f01a3e01a3d0697d029610695f0295b06957029530594f0294b03947029430193f0193b01937019330192f0192d0192b0192a0292902928019270192606925ca124019230192104c6d07c6103b6d05b6106b4f12b4b06b470fb43d026d01a610fa4f12a4b12a470fa43ce23f06a3b06a37c92330896d029510f94f0294b0f947029430693f0293b06937029339e12f0292b711270292308d6f08d6306c6f06c6306c5f06c5b06c5706c5308b6f08b6e08b6308b6209b5f07b5e0fb5b04b5a09b5704b560cb5307b5206b4f05b4e06b4b03b4a06b4703b4606b4305b4208a6f08a6e01a6308a6209a5f01a5b0fa5a09a570fa5601a5306a4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0296f029630295f0295b02957029530294f0294b02947029430193f0193d0293701935029330192f0292b029290292701923029210285f028570284f028470283f0283d02837028350182f0282d01827028250281f0281708d6f08d6306c6f06c6306c5f06c5b06c5706c5308b6f08b630fb5f0fb5b0fb570fb5306b4f06b4b06b4706b4302a6f02a6d02a6502a5f02a5b02a5702a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330296f0896e0296d0295f0795e0295b0295a029570495602953029520294f0594e0294b0294a029470394602943029420293f0193e0293b0293a02937c713602933019320285f028570284f028470283f028370282f028270281f0281d028170281504d6f07d6b04d6707d6307c6f08c6e07c6b07c6707c6307c6202c5f02c5e02c5d06b6f12b6b06b6712b6306b5f04b5b04b5707b5306b4f03b4d07b4b05b4906b4703b4507b4305b410ca6f0ca6b0ca670ca6307a5f04a5b04a5707a5307a4f07a4d07a4b01a4907a470ca4507a4301a410ca3f06a3b06a370ca330f96f0296b0f967029630295b0495a02959049570495602953029510494704946049450693f0293b06937029330c92f0292b0c927029230786f0286b07867028630785f0785d0285b0485707855028530784f0784d0284b0784707845028430783f0283b06837028330782f0282b07827028230281f0281b028170281301d6f01d6e02d6301d6204c6f04c6304c5f04c5d04c5b04c5904c5704c5504c5304c5106b6f06b6306b5f03b5d06b5b05b5906b5703b5506b5305b5104b4f04b4b04b4704b4302a6f01a6302a5f01a5b01a5901a5301a5104a4f01a4b04a4701a4306a3f01a3b06a3701a330296f029630295f0295d0295b02959029570295502953029510294f0294b02947029430293f0293b02937029330192f0292b02927019230285f0285d02857028550284f028470283f028370182f018270281f0281701e7f01e7e01e7d04d7f04d7304d6f04d6d04d6b04d6904d6704d6504d6304d6106c7f06c7306c6f03c6d06c6b05c6906c6703c6506c6305c6104c5f04c5b04c5704c5301b7901b7301b7104b5f01b5b04b5701b5306b4f01b4b06b4701b4302a7f02a7302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f04a5e02a5d02a5702a5502a5302a5202a4f02a4b02a4702a4301a3f02a3b02a3701a330297f0897e02973029720296f0896e0296d0896c0296b0296a0296902968029670896602965c4164029630296202961029600295704956029550294f0594e0294b0294a029470394602943029420193f0193e0293b0293a029370993601933019320292f0292e0292d0286f0286d02867028650285f028570284f028470183f018370282f028270281f0281d028170281504d6f04d6b04d6704d6306c6f06c6b06c6706c6304c5f04c5b04c5704c5309b6f08b6e11b6b09b6711b6308b6204b5f01b5e04b5b04b5a04b5704b5601b5301b5206b4f05b4e06b4b03b4a06b4703b4606b4305b4209a6f01a6b09a6701a6304a5f01a5b04a5a04a5704a5601a5306a4f01a4b06a4a06a4706a4601a4302a3f02a3e02a3d0296f0296b02967029630295f0295b02957029530294f0294b02947029430193f0193d0293b02939029370193502933029310192f0292b029290292701923029210286f0186b02867018630285f0185b02857018530284f0184b02847018430283f0283d0183b0283702835018330182f0182b01827018230281f0181b028170181304d6f04d6b04d6704d6306c6f06c6b06c6706c6304c5f04c5b04c5704c53c336f0cb6b12b670cb6304b5f04b5b04b5704b5306b4f06b4b06b4706b4302a6f02a6b02a6702a6302a5f04a5e02a5d02a5702a5502a5302a5202a4f02a4b02a4702a4302a3f02a3b02a3702a330296f0896e0296b0296702963029620295704956029550294f0594e0294b0294a029470394602943029420293f0193e0293b0293a02937c213602933019320292f0292e0292d0286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281d0281b02817028150281301e7f01e7e01e7d04d7f04d7e04d7308d7204d6f04d6e04d6d04d6c04d6b08d6a04d690fd6804d6704d6604d6504d6404d6308d6204d6108d6004c7f04c7304c6f04c6d04c6b04c6904c6704c6504c6304c6102c5f02c5e02c5d06b7f08b7306b6f03b6d08b6b05b6906b6703b6508b6305b6104b5f03b5d04b5b04b5904b5703b5504b5305b5104b4f04b4b04b4704b4301a7901a7301a7104a5f09a5d01a5b01a5904a5704a5501a5301a5104a4f01a4b04a4701a430ba3f01a3b06a3701a330897f029730896f0896d0296b02969089670d96502963029610495f0495e0795d0494f0494e0294b029490294304942029410693f0293b06937029330192f0292b0c927019230786f0786d07867078650485f0785d04857048550484f0c84d04847048450783f068370182f018270281f0281704d6f04d6e04d6b04d6704d6308d6204c6f04c6b04c6704c6302c5f02c5e02c5d06b6f12b6b06b6714b6304b5f03b5d04b5b04b5904b5703b5504b5305b5104b4f04b4b04b4704b43c026f0ca6b12a670ca6304a5f0fa5d04a5b01a5904a5704a5504a5301a5104a4f04a4b04a4704a4314a3f06a3b06a370ca330f96f0296b0f967029630495f0495e0795d0494f0494e0294b029490294304942029410693f0293b06937029330c92f0292b0f927029230786f0286b07867028630485f0785d0285b0485704855028530484f0f84d0284b0484704845028430783f0283b06837028330782f0282b07827028230281f0281b0281702813 19 524287 7 127 11 2047 20 1048575
def cc_67_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x8e27b8964c84e4881a347fa207c6347a6207545270c486a963640695df6157c63564185263e4c16545e633fb6337a8134f2b30e412a96526d3c1f27b1a64c1832315d261411c0f44d0b44004f650004f 0x1e7f00f3f0079f409afe04d73026b78135b409ad604d69026b381359409ac604d6101e3f8171cc078de03c6d02e358171a4078ce03c6502e31817184078be04c5e01e2e80f15c078aa04c5302629012dfc116fc04b73025b9012dbc116dc04b6d045b6012dac096d404b69025b4012d9c116cc04b65809b2012d8c096c404b61025b000ed5c076ac03b55025a7816d380969a01a7900d398069c4094be01a5b0252b80694c0b49e01a4b01d2380690c0947e04a3d00d1d8068e40946e09a3500d198068c4112fe06973044b78225b40d2d602969044b38425940d2c602961024af81256c092ae0495302ca780e52c0728e059430249f8124f409276029390249bbfc4d4092660293100c9781a4ac1724e0192303c3781e1b40f0ce078650242f832174090ae0485502c2780e11c0907e0483d0241b81e0d40305e018270340f81e05c03ade01d6e046b1807588118de08c630ae2f813174198b607c5906e2b813154198a607c51035b7822d8c0d6be03b5d06dad816d640d6ae03b55085a9816d440d69e10b4b035a3832d0c114de01a6309d2f80696c034b201a5300d2883293c034960ca4700d2182e8fc0347606a3700d198225bc112dc02963044b102257c112bc0895d064a780a52c1b28e029430349f80a4ec0d26e0293300c9780a4ad382540d9273c09300648c330be0785d06c2b81e1541909e420470841f81a0dc0305e018270140f80a05c03ade01d6e00eb68231bc118c608c5f0262e82316c0f8b208c570262a82314c0f8a208b6f045b1822d7c076ba08b5b02dac822d5c076aa08b5302da882ed3dfc6960bb47065a18069a4034c601a610652780692c1948e01a4305d1f8068ec1746e01a33044b782258c112be0895d044ad80a564112aefd155044a980a5441929ec314b600a383250d7627e0b93b05c9bac44cc0325e9b12b3b89380648c110be0785d0442b81e1541909e410471401f82e0dc0305e018270480f81405c0d8be0bc5b0362b82f14c036be01b5b00dab806d4c0369e01b4b00da3806d0c194be07a5e0652d812968194ae04a560652981e9481749e05a4e0352580e9280d48e03a4605d218169080347e01a3e00d1d8068e80346e01a3600d198068c8192be0295b064ab80a54c0d29e0294b05ca501a51c1728c0294300c9f8064f8032760193700c998064c8178be0bc5b05e2b82f14c036da01b5f00dad806d5c036a601b4f00da5806d1c0368607a5e0252b0169380748c01a3e064af83256c192ae0c95305ca782e52c1728e0b94300c9f8064ec0326e0193301494bec4941b8de04c6d0663581f1a4258ce04c650663181f1840d6de03b6d085b5816da40d6ce03b6506db1816d840d69e10b4b035a3832d0c114de08a6d00d358069a4274ce08a6500d318069841949e01a4b0652380690c1747e01a3b0351b8068cc1929e0294b06ca380a50c0d27eba13e0149d81a4dc05266b013200c9780a4ad342540d9273b09300648c098da07c6101db6816d841769e12b4b05da3832d0c114da01a510652780692c1948e01a4305d1f8068ec1746e01a337c8b680a5841929e1294b094a383250d7227e0b93b05c9bab84cc0325e9912b3a89380648c11ade08d630363782318c0d8be0bc5b0362b82f14c036de01b6300daf806d6c036ae01b5300da7806d2c0368e01b43045378229b8114c608a620652f81e978194b604a5a0652b812958194a607a5205d278169380d49603a4a0352380e9181748605a4200d1d8068e80346e01a3600d198225bc112dc02963044b103257c052b60c95a064ab832558052a60694f014a582e5280d28e0b946014a18064fc0327c0193b00c9b8064cc032640192f00c970064b4030be0185700c2780611c0307e0183700c178060b40304e0182500c0f8060740302e01815046b782358c118de08c6305e2f82f16c178ae0bc5300db7806db4036ca01b5f00dad806d5c036a601b4f00da5806d1c0368601a6f045370069b4034be07a5e00d2d806968034ae04a5600d298069480349e05a4e00d258069280348e03a4600d21806908112de08963064af83256c192ae0c95305ca782e52c1728e0b94300c9f8064ec0326e0193300c978064b4032560292900c93bdc494032460192100c2f80615c0309e0184700c1f8060dc0305e0182d00c138060940303e01817026b781f5ac09ace07d6303e378231b80f8d607c6703e3181f188038be01c5e00e2e82edbc256d60bb67095b181ed7c096b604b5703da981ed3c0769a07b4b02da481ed1c0768a07b4302da08329bc034d60ca6700d3180696c094b401a590252b812958034a601a51025238129180948a0ba3f00d1d82e8dc034660f96f07cb583e59c1f2c60795f024ad81255c0f2a60794f03ca681e52c052920794707ca281e50c052820f93f05c9d82e4dc1f2660192f0649583249c032460786f00c3581e19c030c60785f03c2e80616c090ae0785500c2981e13c0f09a0184b03c2381e114030860783f00c1d81e0dc030660182f00c1580609c030460781f00c0d81e05c0302604d6f026b581359c09ac606c6f05e3581b19c178c604c5f0262d81315c098a601b6f00db5806d9c036c601b5f00dad806d5c036a601b4f00da5806d1c036860da6f045370469ac1b4ce11a630453101297c054bc04a5b0252d01295c094ac02a530152902e93c0b49c06a4b01d2501a91c0748c0ba4302d210068fc0347c01a3b00d1d0068dc0346c01a3300d190365bc052d60d967014b181257c052b60495a024ab812558052a60694f014a582e5280d28e0b946014a18064fc0327c0193b00c9b8064cc032640192f00c970064b4030de0186b00c3380618c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c1580609c0304a0182300c0f80606c0302e01813026b78135ac09ace04d6305e3782f1ac178ce0bc630262f81316c098ae04c5300db7806dac036ce01b6300daf812d78036ba01b5700daa806d4c036a401b4f00da5806d1c0368601a6f045370069ac034ce01a6300d3100695c094ac01a5500d278169380349601a4a00d2380e9180348601a4200d1f8068f80347ad916f07cb584a59c1f2c60495f024ad81255c092a60b94f05ca582e51c172860193f00c9d8064dc032660192f00c968064ac05252019277a09280648c032420186f00c3580619c030c60185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660182f00c168060ac0304e0182500c1180607c030360181700c098135bc09adc04d6b026b381358c11ac404c6f0263581319c098c601c5f00e2f007174176de12b6b05db3852d8c096be03b5d025ad812d64096ae03b55025a9816d440969e04b4b025a3812d0c194de01a6b0653380698c094be04a5e03d2e81293c0949c01a4b00d2480690c0948401a4105d1f8068ec1746e01a336c0b783e5ac252ce0f963024af832574092b602959024ab812554092a602951024a781252c0928e049430a49f82e4ec1726e0f93300c978324ac1924e0192303c378061ac0f0ce018630242f81e174030b6048570242a80614c0909e0c84d00c2581211c0908a0184303c1f8060ec0f06e0183300c178060ac0304e0182303c0f80606c0f02e0181303da7812d2c0968e07b4300d2780692c0348e01a4300d1f8068ec0346e01a33014a780a52c0528e029430149f80a4ec0526e0293300c978064ac0324e019230262f81f16c098ae07c5305daf82ed6c176ae0bb5303da7812d2c0968e07b4300d2f80696c034ae01a5300d278069340349601a4700d2280690c0347e01a3b00d1b8068cc032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9b8064cc0325e0192b00c9380648c1f0be0f85b07c2b83e14c0f09e0484b0242381e10c1707e0b83b05c1b82e0cc0305e0182b00c1380608c0303e0181b00c0b80604c09ade07d6b026b381f58c178de0bc6b05e3382f18c0f8be04c5b0262b81f14c036de01b6b00db3806d8c036be01b5d00dad806d68036ae04b5600daa806d3c0369601b4700da18069bc114dc01a6b00d3380698c034c401a5f03d2f0069740349e05a4e00d258069280348e03a4600d218069080347e01a3e00d1e83e5bc1f2d60f96707cb181e57c092b60495703ca982e53c172960b94705ca18064fc032760193700c998064bc0325a0192b0149480649c1f24a0192300c908061bc030d60186700c3180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc0305a0182b00c153c40a00304e0182600c12bc0090030460181f00c0d80605c0302614d6f066b585359c19ac603c6f02e3580f19c0b8c603c5f02e2d80f15c0b8a605b6f045b7016dac0b6ce05b6302db1016d7c0f6bc05b5b025ad016d5c096ac05b5302da9006d3c0369c01b4d05d378069ac174ce01a6305d2f80696c174ae01a5300d2580e9280349203a4701d2300690c0348203a3701d1b00e8d5ae2de0696b670b381a58c192be0695b0a4ab81a54c0b29e0594d01ca580e51c1728a0594302c9f8164f40b2760293902c9b82e4d40b2660293100c9781a4ac1724e01923074378061ac1d0ce018630642f80616c1d0ae0185302c2780612c0708e0184302c1f8160f4030760583703c1a8060cc0305e0182b00c1380608c0d03e0181b0740b80604c19ade0cd6b066b383358c078de03c6b01e3380f18c078be03c5b01e2b80f14c036de01b6b00db3806d8c036be01b5b00dab806d4c0369e03b4e00da6806d1c0368a01b4300da10069bc114dc01a6b00d3380698c034c401a5f03d2f00696c034b401a570252b00694c034a401a4701d230069140347e01a3e00d1e81a5bc0d2d606967034b181a57c0d2b606957034a980e53c072960394701ca18064fc0327a0193b00c9b81a4d4032660192f00c968064ac05252019270349280648c032420186f00c3580619c030c60185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660182f00c168060ac0304e0182500c1180607c030360181700c098139fc0fcfc04e7d026bc8135cc09ae203c7f01e3f00f1cc118e403c6f01e3700f1b4078d803c6b0263500f1a4258d003c6701e3300f194078c803c630263100f184098c003c5f01e2f00f16c098b403c590262c00f15c078ac03c530262900f1440f8a003b7f01db980edbc076da03b6b01db480ed9c076ca03b6301db080ed7c076b603b5701da9806d3c0369c01b4d0453f8069cc094de04a6d00d358069a4094ce09a6500d31806984094be01a5b0252b80694c0749e03a4e02d2680e8fc0747c01a3b00d1c8068cc0746401a31034bf81a5cc092de0496d024b580a5a4092ce06965024b180a584092be0495b024ab81254c0729e0694d01ca580a5240728e0394501ca180a5040727e0693d01c9d80e4dc0726a0393300c9781a4b40d256069270349280648c090de0486d0243381e194090be0485701c2781e1340708e0384501c1f80e0dc0305e018270340f81a05c078be03c5b01e2b80f14c076be03b5e025ad812d68076ae03b5601da980ed480369601b4a0252f80696c094ae01a5301d2780692c0348605a3f02d1e81257c092b604957024a980e53c072960394701ca181a4fc0d27a0693b0149c81a4dc0d26a06933014988064bc0d2560692700c918135f409ac203c7d01e3e00f1c5d68e003c5f01e2f00f16c098b403c5701e2b00f14c098a403b7d01db880ed7c076b603b5701da9806d3c0369c01b4d04d3e8069c4094be01a5b0252b80694c0749e03a4e02d2680e8fc0747c01a3b00d1c8068cc0746401a31034be80a5c4092be0495b024ab81254c0729e0694d01ca580a5240728e0394501ca180a5040727e0693d01c9d80e4dc0726a0393300c9781a4b40d256069270349280648dd8ade0cd6b752b383358c078de03c6e01e3580f19c078c608c6201e2f80f178078b604c5a01e2b80f158078a607c5201db780edac076ce03b6301daf80ed6c076ae03b5300da7806d380369a0ba6f00d3582e99c034c60ba5f00d2d82e95c034a603a4f01d270169340747e03a3e00d1d8068e40346603a3200d1881a5bc0d2d606967034b181a57c0d2b606957034a980e53c0d29a0394b014a480e51c0728a03943014a080e4fc0d27a0393b01c9b80e4d4072660192f0349681a4ac0d24e0692500c9196c1bc030d65306700c3183217c030b63c05700c2980e13c0f09a0184b01c2380e114030860383f00c1d80e0dc030660182f00c1580609c030460681f00c0d81a05c030260cc5f0662d83315c198a603b5f02dad80ed5c0b6a603b4f02da580ed1c0b68601a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1d8068dc034660295f014ad80a55c052a60294f014a580a51c052860293f0149d80a4dc052660192f00c9580649c032460185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660182f00c1580609c030460181f00c0d80605c030260cd6f066b583359c19ac603c6f02e3580f19c0b8c603c5f02e2d80f15c0b8a601b6f00db5806d9c036c601b5f00dad806d5c036a601b4f00da6806d2c0369401b4701da3006d14036860da6f045370469ac1b4ce11a630453103297c0f4bc0ca5b0252d03295c094ac0ca5303d2901693c0b49c02a4b0152500e91c0548c05a4302d210068fc0347c01a3b00d1d0068dc0346c01a3300d1901a5bdaa2dc0296b034b501a59d942cc02963034b101a57c192bc0295b034ad01a55c192ac02953034a901653c0b29c0294b01ca500e51c0728c0294302ca10064fc0327c0193b00c9d0064dc0326c0193300c990064bc0325c0192d00c378061ac030ce0186300c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e0183300c178060b4030560182700c1280608c0303e0181d00c0d8060640302e0181500c0980604411ade08d6e046b68231bc118c608c5f0262e82316c0f8b208c570262a82314c0f8a203b6f02db180ed7c076ba05b5b02dac80ed5c076aa05b5302da880ed3c0b69603b4702da18069bc034c601a5f00d2e80696c034b201a5700d2a80694c034a201a4f00d2580691c0348601a3f00d1e8068ec0347401a3701d1b0068d4034660d969044b18225841929e0c94b064a383250c0b27e0393b01c9b8164cc0325e0192b00c9380648c030be0185d00c2b8061540309e0184700c1f8060dc0305e0182700c0f80605c078be05c5b01e2b81714c036be01b5b00dab806d4c0369e01b4d00da5806d280368e03b4600da28369b4194be0ca5b0652b83294c0b49e03a4b01d2381690c0347e01a3b00d1b8068cc0f2bc0495602ca700e5180327c01936044970131b40f8c203b6d02db080ed3c0b69603b4702da18069b5964d801a6100d3000693c0349601a4700d218068fc0347a01a3b00d1d0068dc0746c01a35044b6836545c62a00c94f064a583251c192860593f01c9d80e4dc0b2660192f00c9580649c0324603b4f02da580ed1c0b68601a4f00d2580691c0348601a3f00d1e8068ec0347401a3701d1b0068d4112ba0894f044a582251c112860593f01c9d80e4dc0b2660192f00c9580649c0324608d6f046b180f1bc0b8c603c5f02e2d80f15c0b8a601b6f00db1806d7c036b601b5700da9806d3c0369a01b4b00da5006d1c0768c01b4500da18229bc114da0da657193203297c194b60ca570652981693c0749603a4702d218068fc0347601a3700d198225bc112dc0896d044af81e578112b60495a044ab812558112a60795202ca7816538072960294a01ca380e5180b2860594200c9f8064f8032760193a00c9b8064d8032660193200c2f80615c0309e0184700c1f8060dc0305e0182700c0f8060740302e018150662f83316c198ae0cc5301daf816d6c076ae05b5301da7816d2c0768e05b4300d2f80696c034ae01a5300d2780692c0348e01a4300d1f8068f40347601a3a00d1b80e8d80346a01a33730afb9456dc82aee2153064a783252c1928e0c94302c9f80e4ec0726e0593300c978064ac0324e0192300c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e0183300c178060ac0304e0182300c0f80606c0302e01813066b78335ac19ace0cd6301e378171ac078ce05c6301e2f81716c078ae05c5300db7806dac036ce01b6300daf806d6c036ae01b5300da7806d340369601b4a00da380ed180368a01a6f045370069ac034ce01a6300d3100697c0f4bc01a5b00d2d00695c094ac01a5300d2900693c0b49c01a4d00d1f8068f80347ad416f034b5b2459c0d2c60c95f034ad83255c0d2a60594f01ca580e51c0b2860193f00c9d8064dc032660192f00c968064ac03254029297409400649c0324ce71257089200648c032420186f00c3580619c030c60185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660182f00c168060ac0304e0182500c1180607c030360181700c0980b5ac05ad204d63016b08131bc078da04c6b0263480f19c078ca04c630263081317c098a603b6f01db6816dac0b6d203b6701db2816d8c0b6c203b5f02da980ed3c0969603b47025a18429bc134da0ba6b00d3484299c134ca0ba6300d3082297c114a604a4f0252581291c0948605a3f01d1d80e8dc0b4660496f014b580a5a4052c602961024af80a54c0929e0294b024a380a50c0b27e0293b01c9b80a4cc0d25e0292b0349380a48c0f0de0786d03c3381e1940909e0e84d024238121140b07e0383703c1781e09c0503e02817 20 1048575 8 255 11 2047 21 2097151
def cc_67_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x80d64fda81f54c3d2b075998e2321b8d7357b46815cc9ad18b50306a05c09aadd494866a67d2487908de610c5f1e66539a646679cb23594b3222fce389ac58718806109dc609d3c0e0b00038 0x131bc098da02c6b0163481319c098ca04c630163081adbc076da10b6b02db481ad9c076ca0db6302db0812d3c0969604b47025a18369bd2a4da0ca6b00d3484e99e3e4ca0ca6300d3081293c0949604a47025218428fc0d47606a370651981253c052960494a024a3812518052860693f0149d81a4dc052660c92f0149583649c0524604c6d0262880edb40b6c204b4f025a5812d1c096872026d00d3081293c0949604a47025218528fc19476ea23706519c785b4052c20494f024a581251c092861493f07c9dad04dc1f2660c92f07c95a4c49c1924607b4f025a5812d1c0f68601a4f00d2580691c0348601a3f00d1d8068dc034660294f014a580a51c052860293f0149d80a4dc052660192f00c9580649c0324604c5f03e29812d7c0f6a604b4703da182297c114a607a4f0252581291c0f48607a3f03d1d81e8dc0f4660895f044a981e53c092960494703ca181e4fc0f2760793703c998324bc192560c9270649182217c110a60784f0242581211c0f0860783f03c1d81e0dc0f0660f82f07c1583e09c1f0460c81f0640d83205c1902604d6f026b6813594098de04c6e02636822dbc116c607b5f025ad812d5c0f6a607b4f01da681ed2c0b69207b4701da281ed0c0b68208a6f0453181e97c094b604a5703d2981e93c0f49a07a4b00d2481e91c1948a07a4300d208328fc194760ca37065198225bc112c60795f024ad81255c0f2a60794f03ca681e52c052920794707ca281e50c052820f93f07c9d83e4dc1f2660c92f0649583249c192460785f0242b81e13c0f09a0784a8e02401e11c0f08c078458d82201e0fc0f06e0782f03c1381e07c0f02e03d6f02eb700f5b4118de08c6301e2f80f174078b607c5901e2b813154078a603c5101db480ed8c076c203b4f01da580ed1c0768608a6f0453180e97c074ba03a5b00d2c80e95c174aa03a5300d2882e93c174960ba4705d2180e8fc0747603a3701d1981a5bc0d2c60395f01cae80e56c052b203957034aa80e54c052a20694f034a581a51c0d2860393f01c9d80e4dc072660692f0349581a49c0d2460385f01c2e80e15c0f0aa1284f2202380e0fc0706e0b82f05c1381a07c0d02e03c5f02e2d80f15c0b8a60cb5f03daf036d6c096b40db57025ab032d4c0f6a405b4f02da7006d2c0369403b4700da3016d0c0b68409a5f00d2d82695c034a605a4f00d2580e91c0348601a3b00d1c81a57c052b606957014a981653c0529603947014a181a4dc1326c069350149581a4a80d24e0992600c9180f17c0b8b603c5702e29826d7c0f6bc12b5b025ad026d5c096ac0cb5303da9016d3c0b69c01b4b00da500ed1c0368c05b4302da102697c034b609a5700d2981693c0b49c01a4b01d2380690c0b4840c95f034ad84a55c0d2a60594f01ca580e51c0b2861993f8c09e81a4ec05272099374889a81a4cc052620192f05c9681a4ac1324e9012500c9180f17c0b8b603c5702e29826d7c0f6bc09b5b025ad026d5c096ac09b5303da9016d3c0b69c02b4b015a500ed1c0568c05b4302da102697c034b609a5700d2981693c0349603a4700d218268dc1346c09a35034af80a56c0d2ae0295302ca780a52c0728e0294300c9d8064e40325e0692d0349381a4940324603c5f02e2d80f15c0b8a60db5f03daf04ad6c096b40db57025ab03ed4c0f6a405b4f02da700ad2c0569403b47015a3016d0c0b6840fa5f05d2d84a95c174a605a4f01d2580e91c0b48613a3f8b11e82e8ec034720da374891a82e8cc034620695f014ad81a55c052a60594f02ca700a52c0728e0294302ca101a4bc052560692a03493a3c4980524603c6d01e2f81716c078ae05c5303daf012d580b69c12a5f05d2d84a95c174a605a4f01d2580e91c0b48601a398b91a84a57c0d2b612957034a981653c072960394702ca180a4e62a26a0b92f03495a3849c0d24604c6d03e3080edb4076a203b4f01da580ed1c076860ba6d00d3082e93c174960ba4705d2180e8fc0747603a3701d1981a5b4052c20694f034a581a51c0d2860393f01c9d80e4dc072660692f0349581a49c0d24608d6f046b180f1bc0b8c603c5f02e2d80f15c0b8a606b6f035b701ad8c0d6c40cb5f03daf036d6c096b40db57025ab032d4c0f6a405b4f02da7006d2c0369403b4700da3016d0c0b68408a6f00d3182697c034b609a5700d2981693c0349603a4700d218168fc0b47a01a3b00d1c8168dc0b46a01a3300d1881a5bc052c60695f014ad81a55c052a60594f014a580e51c052860693704c9b01a4d40325e0292b0349501a49c1324c019230642f83a15c0b09e0384706c1f81e0f41b06e0783500c1780609c0503e02817046b782358c078de05c6301e2f81716c078ae05c5301db780edb8116c603b6204daf81ed78296b604b5a04dab812d58196a607b5200da5806d280768e01b4602da18229bc114dc01a630453102697c034b60ba5a04d2b852958034a605a4f02d2700692c0748e01a4302d210168fc0b47c05a3d044b781a58c192be0695b0a4ab81a54c0b29e0394b01ca381650c3327f1213d0349d80a4e41326e8c1350349980a4c40325e0b92d0349582649d1624a019230642f83a15c0b09e038470741f81e0f41306e0783500c1782e0b40304e0e8250340f83a05c11ade08d6301e3781718c078be05c5b01e2b81714c116de08b6e035b181ad88136be07b5e04dad812d68136ae04b5604da981ed480b69e05b4e015a580ad280768e02b4602da1816d080d4de01a6304d2f80696c134ae01a5302d2780692c0748e01a4304d1b8268d81346a0696f014b181a57c052b606957014a981653c0529603947014a18164fc0b27a0193b00c9c8164dc0b26a0293300c988064bc0d25a0292b0349381a494032460c85f0742b81613c0708e0983f03c1e8260dc0f06a0182f00c1380a07c0502e08d6f046b180f1bc0b8c603c5f02e2d80f15c0b8a603b6f01db701ad8c076c40db5f03daf052d6c096b40db57025ab03ed4c0f6a402b4b015a500ed1c0568c05b430453782298c1f4be0ba5b0a52b82e94c0b49e03a4b01d2381690c2747f1023d05d1d8068e41b46e8c23505d198068c40d2de0896e014b181a5880d2be0295b034ad01a55c292ac0295302ca78165380529603947014a18165080b27e0593e02c9e81a4bc052560692a03493a28498052460e85f0742b81613c0708e0e83f03c1e8360dc0f06a0b82f0741380a07c0d03a028170740a8235bc11ac603c6f01e3680f194078be05c5b01e2b81714c076de03b6e01db6816d7c0f6bc05b5b025ad016d5c096ac05b5302da90229bc114c612a5f05d2d85295c174a605a4f01d2580e91c0b48605a3f02d1e8168ec0347205a378891a8168cc034620896f034b184a57c0d2b614957034a981653c072960394702ca18164fc0b27a0593b0149c8164de1e26a059330149882e4bc0d256891270349183a17c1d0ae0584f01c238160fc0b07a0583703c1a82e0bc1d04e0681f0740b80ed3c0769603b4701da180693c0349601a4700d218068fc0347601a3700d1980a53c0529602947014a180a4fc0527602937014998064bc032560192700c9181317c0f8b604c5703e2981ed7c0f6b607b5703da9816d3c0969604b4703da180e97c074b603a5701d2980e93c0749603a4901d2380e90c0748203a3f01d1d80e8dc074660b95f05cad82e55c172a60794f024a581251c0f2860793f03c9d81e4dc0f2660392f01c9580e49c072460685f0342d81a15c0d0a60684f0242581211c0d0860683f0341d81a0dc0d0660382f01c1580e09c070460681f0340d81a05c0d02604d6f03eb581359c0fac603c6f0463700f1ac078ce03c6301e3100f17c0b8bc03c5d01db780edac076ce03b6301dad812d68076b203b5701dab00ed4c076a203b4701da300ed14174de0ba6b05d3382e98c0f4be04a5b0252b81e94c0749e03a4d01d258069240748e0ba4501d218069040747e03a3b01d1b80e8cc0d2de0696b034b381a58c0d2be0495b024ab81a54c0729e0394d01ca580a5240728e0694501ca180a5040727e0393b01c9b80e4cc0d25e0692b0349381a48c0f0de0786b03c3381e18c0f0be0485b0242b81e14c0709e0384d01c2580e12a1a0900384701c2301e116180880384301c1f80e0ec0706e0383303c1781e0ac0f04e078230340f81a06c0d02e068130463f0231f4118f809c7504e3a0131b8098d403c6600e31017178038b403c5602e29022df8116fa01b6e025b5012d98036c405b5e00dad006d580b6a408a7d04d3a8129a8094cc05a5e02d290129380949a04a3d0251a8068c43329a0694904ca281a5041127a029390849a80a4c41725a09925064368121940f09a0784503c1e81e0d409ade04d6b026b381358c078de05c6b01e3381718c078be04c5b01e2b81314c1b6de08b6e06db5836d9c1b6c608b62025af806d78096b604b5a025ab812d58036a601b5202da7816d380369601b4a01da3806d180b68605b4204d378069ac134ce01a630252f80696c094ae01a5302d2780692c0748e01a430251f8128f40347601a390251b8128d40346601a31034b780a5ac0d2ce02963024af80a56c092ae0295302ca780a52c0728e029430349b8264d80d26a0192f0149581a4a80d24e0992600c9181e1bc030d60786700c3181217c190ba0185b0242b812154030a60584f00c2580e11c030860783f03c1e8060ec0f06e0783500c198060bc030560182700c1180a07c030360281700c098135bc09ad604d67026b180f1bc0b8d603c6702e3180f17c098b603c5702629826dbc116dc12b6b04db3c28d8c116c404b5f00daf012d6c076b403b5701dab006d4c036a405b4f02da7006d2c0369403b4700da3016d0c0b68409a6f00d3582699c034c604a5f00d2d812968094ae04a5600d2981693c0b49c01a4b01d2380690c0b48404a3f0251f0128f5ba2de0696b094b381a58c092be0495b024ab81254c0b29e0394b01ca381650c3327f0913d0349d80a4e41326e871350349980a4c40325e0b92d0349582649d0c24a0192303c378061ac0f0ce018630242f832174030b6048570242a80614c0b09e0184b01c2380610c0f07e0783d00c1d81e0dc0f06a0183300c178060ac0304e018230340f80606c0f02e018130463f0231f4118f80dc7506e3a0131b8098d403c6601631017178058b403c5602e29022df8116fa02b6e025b5012d98056c405b5e015ad00ad580b6a413a4d05d248369141748208a3d00d1c84e8d4034620697d034ba8125a8092cc0595e02ca90125380929a0493d0249a80a4c40d2540d926074368121940f09a0784503c1e81e0d409ade04d6b026b381358c078de05c6b01e3381718c078be04c5b01e2b81314c136de08b6e04db5826d9c136c608b62025af80ad78096b604b5a025ab812d58056a602b5202da7816d380569602b4a01da380ad180b68605b4204d378069ac134ce01a630252f80696c094ae01a5302d2780692c0748e01a4304d1b8268d81346a0696f014b581a59c052c60495f014ad81255c052a60594f014a580e51c052860493f0249e8064ec03272049370249a80a4cc032620192f0349680a4ac0d24e0692500c9181e1bc030d60786700c3181217c190ba0185b0242b812154030a60584f00c2580e11c030860783f03c1e8060ec0f06e0783500c198060bc030560182700c1180a07c030360281700c098135bc09ad604d67026b180f1bc0b8d603c6702e3180f17c098b603c5702629836dbc116dc12b6b06db3c1cd8c116c404b5f015af012d6c076b403b5701dab00ad4c056a405b4f02da700ad2c0569403b47015a3016d0c0b684ff26f05d3584a99c174c604a5f0252d81295c094a605a4f01d2580e91c0b48613a3f8311e82e8ec034720da374391a82e8cc034620696f014b581a59c052c60495f014ad812568092ae04956014a981653c0b29c0294b01ca380a50c0b2840493f0249f0124f40d25e0292b0349501a49d0a24c0292303c3780a1ac0f0ce028630242f83a174050b6048570242a80a14c0b09e0284b01c2380a10c0f07e0783d0141d81e0dc0f06a0283303c1780a0ac0f04e028230140f80a06c0502e02813026b78135ac09ace04d6301e378171ac078ce05c6301e2f813178078ba03c5701e2a81314c098a404b6f045b7012dac096ce04b63025b100ed5c076ac03b55025a7816d380969afe26f05d3584a99c174c604a5f0252d81295c094a605a4f01d2580e91c0b48604a3f0251e8128ec0347204a378411a8128cc03462dc16f034b584a59c0d2c60495f024ad81255c092a60594f01ca580e51c0b2860493f0249e8124ec05272049378289a8124cc052620b92f03495a1049c0d2460786f0743581e19c1d0c60485f0742e81216c090ae048550242981613c070960384702c218120fc0907a0483b0241b81e0d4090660782f0741581e09c170460681f0740d81e05c0d02603d6f01eb700f5ac07ace03d63046b10131bc098d604c670263180f17c078bc04c5d01db780edac076ce03b6301daf80ed78076ba03b4f01da700ed2c0769203b43025a100ed04174de0ba6b05d3382e98c074be0ba5d01d2d806964074ae03a5501d298069440949e04a4b0252381290c0747e03a3b01d1b80e8cc0d2de0696b034b381a58c072be0695d01cad80a564072ae0395501ca980a5440929e0494b024a381250c0727e0393b01c9b80e4cc0d25e0692b0349381a48c0f0de0e86b03c3383a18c070be0785d01c2d80e15c070aa038530242781212c0908e0484301c1f80e0ec0706e0383303c1782e0ac0f04e0b8230340f81a06c0d02e06813026b781f5ac09ace07d6301e378171ac078ce05c6301e2f80f174098b604c5a01e2b813158078aa05b6f045b7016dac0b6ce05b6302db100ed7c076bc03b5d025a7812d380969a0ca6f05d3583299c174c607a5f0252d81295c0f4a605a4f01d2580e91c0b48605a3f02d1e8168ec0347205a370651a8168cc034620f96f034b583e59c0d2c60795f024ad81255c0d2a60594f01ca580e51c0b2860593f02c9e8164ec052720593707c9a8164cc052620b92f0349583249c0d2460786f03c3581e19c0f0c60785f03c2e81216c090ae0785503c2981613c070960384702c218160fc0b07a0583b02c1b81e0d40b0660782f03c1581e09c0f0460681f03c0d81e05c0d02601d6b00eb481358c03ac204c6f01e368131ac098d203c6701e3281318c098c204c5f0262980edbc076da05b6b02db480ed9c076ca05b6302db080ed7c0b6a603b4f025a580ed1c0968604a6f00d358069a4034c601a610252f80694c0949e01a4b0252380690c0b47e01a3b01d1b8068cc2d2de0d96d034b580a5a42d2ce0d965034b180a584112be06953024a781252c0928e0494302c9f80e4ec0726e0593300c9781a4ac1724e0192303c3781e1b40f0ce07865024278321340908e0484502c1f80e0dc0305e018270340f81e05c036dc01b62015af012d68096ac02b5202da700ad280568c05b4200d1c8068c40927a029390249a80a4c40d2540b9260642e8121540f07a0783500f3f0079f409ada04d69026b2813584078da05c6901e32817184116fc08b72045b7022db4116d808b6a09db4c00da0116cc0db6506db2022d88116c208b60015af00ed68076ac02b5202da700ad280568c05b4200d3c8069c41347a01a3904d1a8068c40d2da02969034b280a584092b40495602ca70165080927c0493d0349502e4980f0da078650642e8121540f07a07835 19 524287 7 127 11 2047 21 2097151
def cc_67_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x57488e40c0b8b99002e 0x9ade07d6e026b68131a4098c604c61045b7822d8c096be03b5d025ad816d64096ae03b55025a9812d440969e04b4b025a3812d0c114de08a630252f812974094b601a590252b84a954094a601a510252781292c0948e04a430a51f8328edd846e0ca33044b782258c092be0495d024ad80a564092ae12955024a980a5440929e0494b024a381250c2927e0f93b5b09b83e4cc1925e0f92b4b09383248c090be0485d0242b81e1540909e0484703c1f81e0dc0f05e0782703c0f81e05c09ada07c5e03daf812d6c096ae07b5302da480ed140f4be04a5b0252b81e94c034920ca450651f8328ec1946e0ca3303caf81256c092ae07953014a483e5141f27e0f93b07c9b83e4cc1925e0c92b0649383248c098de04c6d00e358071a4098ce04c65026318071840d6de03b6d06db5816da40d6ce03b6506db1816d840969e04b4b025a3812d0c034c601a610252780692c0948e01a4304d1f8068ec0d46e01a3304cb78265b8132da0494f014a581251c052860693f0149d81a4dc052660292b04c9502649c1324c01923026378131b4038d601c6902633813194098c601c6104db780edb4296d605b6905db380ed94136c605b61025a7812d2c0968e04b430252780692c0949404a470252300690c1347e01a3b04d1b8068cc132de9516d07cb580a5a4332cf2116504cb180a5840929e0494b024a381250c2927e0b93b05c9b83e4cc0325e0992b04c9380648c098de04c6d0163580b1a4098ce04c650263180b1840d6de03b6d04db5816da40d6ce03b6504db1816d840969e04b4b025a3812d0c134de09a6e04d3681293c0349604a4700d218268fc0347606a3700d1980658c032c20494f014a581251c052860693f0149d81a4dc052660192f0649682649c1324a01923 15 32767 7 127 11 2047 21 2097151
def cur_67 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_67_9 (Nat.sub p 288)) (cc_67_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_67_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_67_6 (Nat.sub p 192)) (cc_67_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_67_4 (Nat.sub p 128)) (cc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_67_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_67_1 (Nat.sub p 32)) (cc_67_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)
def f_67 : Nat → Nat × Nat := unpackForestF 0xc5f00c5b909658f26d8fa658f16d00c578d8488d84400c5300b5f8c13d8aa358b23d8a93500b5b00b578913d87a358823d8793500b53860488604400b4f84b638493d82a35833638323d8293500b4b00b4700b437fb64803687f9357eb4b7e95500a5f7d92500a5b7c96d00a577b92500a5300a4f7a12500a4b00a47780287802400a4300a3f00a3b7556f75c707556700a3770928709257115f7115b7115771a64711537092400a336eb646f3686ea356a34b6a2556d2646a24b6a2476a23f6aa646a9246a2330095f691360095b64a6d67a7c64a3f6537c6527c65a6c6512464a330095763936009530094f621646136f611360094b6026f009475e8185e814009435ca6f5d17c5ca670093f0093b5a56f5ac705a567009375916451b6f57a7c5797c51b675193c55a6e55a66519365225f5225b5396c5225752b6452253519340093350b644f16f4fb7c4f1670092f4e2644c36f4d27c4c3674c1360092b37d6f4a37c4a37037d6747b4847b4447a444794437c6b4534845344452444514437c6342b4842b4442a444294437c5b37b6f4147c37b6b37b673fa6c3f47437b6337b5b37b5737b4f37b433c16437a6f3b17c37a673a2643796f3927c379673783f3783700927369543325f3325b3516c3325734364332533312e2ea342e94c2f94f2f94b2f947302542f9432f1242e944009232ca372c9372c9270085f0085b2b1552626d2a47026237292552616d284702613726b7c26b7026127008572485c24854008530084f0084b22d6816b6f215682116516a6f1fa6e1f94516a5d1ec6016a371cd681ca651ca5d1696f1aa6f1aa451a96e1695d19c601693718a7c173731736c173601692700847159540084314b640da6f1394d0da3512364122350d96f10a6f10a4d0d9350e3480e3440e2440e1440d9270083f0c05c0c0540083b00837008330a2640916f091250082f0082b0796f008270605c0605400823051640436f041360081f0081b02b6f008170105c01054008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV4 fullMask g_67 ep_67 292 bds_67 (dagTraceF fullMask rootStock 11 f_67) (cur_67 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_9 : treeBlockF 288 292 (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) = true := by decide +kernel
theorem nj_67_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_67_1 h1 h2)
theorem nj_67_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_1 (fun _ h1 h2 => treeBlockF_at nb_67_2 h1 h2)
theorem nj_67_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_2 (fun _ h1 h2 => treeBlockF_at nb_67_3 h1 h2)
theorem nj_67_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_3 (fun _ h1 h2 => treeBlockF_at nb_67_4 h1 h2)
theorem nj_67_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_4 (fun _ h1 h2 => treeBlockF_at nb_67_5 h1 h2)
theorem nj_67_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_5 (fun _ h1 h2 => treeBlockF_at nb_67_6 h1 h2)
theorem nj_67_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_6 (fun _ h1 h2 => treeBlockF_at nb_67_7 h1 h2)
theorem nj_67_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_7 (fun _ h1 h2 => treeBlockF_at nb_67_8 h1 h2)
theorem nj_67_9 : ∀ i, 0 ≤ i → i < 292 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := block_join nj_67_8 (fun _ h1 h2 => treeBlockF_at nb_67_9 h1 h2)
theorem nc_67 : ∀ i, 0 ≤ i → i < 292 → (dagCheckNodeV4 fullMask g_67 ep_67 bds_67 292 (dagTraceF fullMask rootStock 11 f_67) cur_67) i = true := nj_67_9
theorem lb_67 : LowerBin fullMask rootStock g_67 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_67 kn_67 sub_67 gl_67 rc_67 nc_67

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4171276288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 4171276288)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 4171276288) = g_67 by decide]
  exact lb_67

end PEqualNP.Outside.L_meta_49209

theorem PEqualNP.Outside.L_meta_49209 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 4171276288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4171276288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49209.table2_from_lowerBin (4276676744 * 2 ^ 32 + 4171276288) 13 PEqualNP.Outside.L_meta_49209.root_lb PEqualNP.Outside.L_meta_49209.wg 18 rfl PEqualNP.Outside.L_meta_49209.wfits PEqualNP.Outside.L_meta_49209.weval
