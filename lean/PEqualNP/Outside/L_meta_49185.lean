import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49185

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

def m_7 : Nat := 0xcccc0000
def s_7 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_7 : Nat := 0x44c0000
def ep_7 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_11 : Nat := 0x3000300030003000
def s_11 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_11 : Nat := 0x100010003000
def ep_11 : Nat := 0x1000200000001000000020000000000000000000000000000000000000000000000000000000100010000000
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

def m_12 : Nat := 0x3333000000000000
def s_12 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_12 : Nat := 0x113000000000000
def ep_12 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_13 : Nat := 0x5555000000000000
def s_13 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_13 : Nat := 0x115000000000000
def ep_13 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_14 : Nat := 0xa0a00000a0a0
def s_14 : List Nat := [0x202000002020, 0xa0000000a0, 0xa0a0]
def g_14 : Nat := 0x20000020a0
def ep_14 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000
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

def m_15 : Nat := 0xc000c000c000c0
def s_15 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_15 : Nat := 0x40004000c0
def ep_15 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_16 : Nat := 0xf0f000000000000
def s_16 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_16 : Nat := 0x107000000000000
def ep_16 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_17 : Nat := 0x2200220022002200
def s_17 : List Nat := [0x200020002000200, 0x220000002200, 0x22002200]
def g_17 : Nat := 0x20002002200
def ep_17 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000000000000000000000
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

def m_18 : Nat := 0x5500000055000000
def s_18 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_18 : Nat := 0x100000015000000
def ep_18 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_19 : Nat := 0xf0000000f000000
def s_19 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_19 : Nat := 0x100000007000000
def ep_19 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_21 : Nat := 0xff0000000000
def s_21 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_21 : Nat := 0x170000000000
def ep_21 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_22 : Nat := 0x4444000044440000
def s_22 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_22 : Nat := 0x4000004440000
def ep_22 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_23 : Nat := 0xa0a00000a0a0000
def s_23 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_23 : Nat := 0x20000020a0000
def ep_23 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_24 : Nat := 0xc0c00000c0c0000
def s_24 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_24 : Nat := 0x40000040c0000
def ep_24 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_25 : Nat := 0x5050000050500000
def s_25 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_25 : Nat := 0x10000010500000
def ep_25 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_27 : Nat := 0xff00ff0000000000
def s_27 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_27 : Nat := 0x100170000000000
def ep_27 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_21, s_21, 4, g_21), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_21
  · exact lb_4
  · exact lb_5
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 43 bds_27 (dagTraceF m_27 s_27 6 f_27) (cur_27 0) s_27 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 43 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f0f0f000000000
def s_28 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_28 : Nat := 0x10107000000000
def ep_28 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_20, s_20, 4, g_20), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_20
  · exact lb_1
  · exact lb_2
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

def m_29 : Nat := 0xf0f0f0f00000000
def s_29 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_29 : Nat := 0x107070700000000
def ep_29 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
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
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_12, s_12, 4, g_12), (m_2, s_2, 4, g_2), (m_9, s_9, 4, g_9)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_12
  · exact lb_2
  · exact lb_9
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

def m_31 : Nat := 0xaaaaaaaa00000000
def s_31 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_31 : Nat := 0x2022200000000
def ep_31 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
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

def m_32 : Nat := 0x5555555500000000
def s_32 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_32 : Nat := 0x115155500000000
def ep_32 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_13, s_13, 4, g_13), (m_1, s_1, 4, g_1), (m_10, s_10, 4, g_10)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_13
  · exact lb_1
  · exact lb_10
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

def m_33 : Nat := 0xaaaa0000aaaa0000
def s_33 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_33 : Nat := 0x20000020a0000
def ep_33 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_23
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x5555000055550000
def s_34 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_34 : Nat := 0x115000015550000
def ep_34 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_18, s_18, 4, g_18), (m_25, s_25, 4, g_25), (m_22, s_22, 4, g_22)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_18
  · exact lb_25
  · exact lb_22
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
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

def m_35 : Nat := 0x5500550055005500
def s_35 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_35 : Nat := 0x100150015001500
def ep_35 : Nat := 0x1400000000001400000000000000000000000000010004000400040001001000100010000000000000000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xf0f00000f0f0
def s_36 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_36 : Nat := 0x1070000030f0
def ep_36 : Nat := 0x2080000000000000000000000060000000c0000000000000000000001020000030000000104000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
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
def g_37 : Nat := 0x40000044c0000
def ep_37 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 4, g_26), (m_7, s_7, 4, g_7), (m_22, s_22, 4, g_22), (m_24, s_24, 4, g_24)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_7
  · exact lb_22
  · exact lb_24
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

def m_38 : Nat := 0xaaaa0000aaaa
def s_38 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_38 : Nat := 0x222000022aa
def ep_38 : Nat := 0x208800000000000000000000002000000088000002000000000000000222000022000000000000000000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xaa00aa00aa00aa00
def s_39 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_39 : Nat := 0x20002002200
def ep_39 : Nat := 0x200200000000200000020000000000000000000000002000200000000000200020022000000000000000000
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

def m_40 : Nat := 0x3300330033003300
def s_40 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_40 : Nat := 0x100130013003300
def ep_40 : Nat := 0x1200200000001200000020000000000000000000010002000200000000000000000000000100100010000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_5, s_5, 4, g_5), (m_11, s_11, 4, g_11), (m_17, s_17, 4, g_17)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_5
  · exact lb_11
  · exact lb_17
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

def m_41 : Nat := 0xf000f000f000f000
def s_41 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_41 : Nat := 0x100010003000
def ep_41 : Nat := 0x1000200000001000000020000000000000000000000000000000000000001000100030000000100010000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xf000f000f000f00
def s_42 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_42 : Nat := 0x100070007000700
def ep_42 : Nat := 0x600000000000600000000000000000000000000000000000000000001000200020002000100040004000400
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xcc00cc00cc00cc
def s_43 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_43 : Nat := 0x40044004c00cc
def ep_43 : Nat := 0x48008800000040000000800000000000000000000400000008000000000000000000000004004400400000
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

def m_44 : Nat := 0xff00ff00
def s_44 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_44 : Nat := 0x17003700
def ep_44 : Nat := 0x20000000000000000000000000000600040000000000120032000000000014000400
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xcccccccc
def s_45 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_45 : Nat := 0x44c04cc
def ep_45 : Nat := 0x8000000000004800c8000000000408040000000000000000000000000004400400
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

def m_46 : Nat := 0xa0a0a0a0a0a0a0a0
def s_46 : List Nat := [0x2020202020202020, 0xa000a000a000a0, 0xa0a00000a0a0, 0xa0a0a0a0]
def g_46 : Nat := 0x20000020a0
def ep_46 : Nat := 0x208000000020000020a00000002000000080000000000000000000000020000020000000000000000000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xff000000ff000000
def s_47 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_47 : Nat := 0x100000017000000
def ep_47 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19), (m_8, s_8, 4, g_8), (m_18, s_18, 4, g_18), (m_0, s_0, 4, g_0)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_8
  · exact lb_18
  · exact lb_0
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_47_1 (Nat.sub p 32)) (cc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_48 : Nat := 0xf0f00000f0f00000
def s_48 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_48 : Nat := 0x10000010500000
def ep_48 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 4, g_25)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_25
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xf0f00000f0f0000
def s_49 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_49 : Nat := 0x1070000070f0000
def ep_49 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_19, s_19, 4, g_19), (m_24, s_24, 4, g_24), (m_23, s_23, 4, g_23)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_19
  · exact lb_24
  · exact lb_23
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_49_1 (Nat.sub p 32)) (cc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 43 bds_49 (dagTraceF m_49 s_49 6 f_49) (cur_49 0) s_49 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 43 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0x2222222222222222
def s_50 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_50 : Nat := 0x2022202022222
def ep_50 : Nat := 0x200200000000220000020200002002000000000000202000202000000000000000000000000000000000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xa0a0a0a0a0a0a0a
def s_51 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_51 : Nat := 0x20202020a020a
def ep_51 : Nat := 0x208000800000200000000000002000000080008000000000000000000020202020002000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_23
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xaaaaaaaaaaaaaaaa
def s_52 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_52 : Nat := 0x20222020a22aa
def ep_52 : Nat := 0x208208800000220000020a0000200200008008800020200020a000000020222020022000000000000000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 5, g_39), (m_33, s_33, 5, g_33), (m_38, s_38, 5, g_38), (m_31, s_31, 5, g_31), (m_50, s_50, 5, g_50), (m_46, s_46, 5, g_46), (m_51, s_51, 5, g_51), (m_9, s_9, 4, g_9), (m_17, s_17, 4, g_17)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_39
  · exact lb_33
  · exact lb_38
  · exact lb_31
  · exact lb_50
  · exact lb_46
  · exact lb_51
  · exact lb_9
  · exact lb_17
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV4 0x851060001 0x1faf275a4eacfd497a7374a6e8cbd0932b1e3e2a7a34e4a9a8d3138b49158e14b74f4e969d1d7a1c64f4c8eb8fdb1b954f1a96551c6a1953f1a7654dc6998d2b2a4ef13ce25a4473886b0fce1db437386670ac4138c1f2836505c609801f 12 4095 6 63 10 1023 15 32767
def f_52 : Nat → Nat × Nat := unpackForestF 0x339f 1 6
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 2 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) s_52 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 2 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 2 (dagTraceF m_52 s_52 7 f_52) cur_52) = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 2 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 2 (dagTraceF m_52 s_52 7 f_52) cur_52) i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xf0f0f0f0f0f0f0f0
def s_53 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_53 : Nat := 0x101070105030f0
def ep_53 : Nat := 0x1040208000001060000020a000100060004000c0000000000000000000101020100030000010104010500000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_28
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) s_53 7 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 7 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0x3333333333333333
def s_54 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_54 : Nat := 0x113133313133333
def ep_54 : Nat := 0x1200200000001220000020200012002000000000010202000202000000000000000000000110100010100000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_40
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) s_54 7 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 7 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xff00ff00ff00ff
def s_55 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_55 : Nat := 0x170077005f00ff
def ep_55 : Nat := 0x48008800000060000000a0000000000000000000060000000a000000120022000000000014004400500000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 5, g_43)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_43
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 5 f_55) (cur_55 0) s_55 5 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 5 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xf0f0f0f0f0f0f0f
def s_56 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_56 : Nat := 0x1070707070f070f
def ep_56 : Nat := 0x608000800000600000000000006000000080008000000000000000001020202020002000104040404000400
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 7, g_49)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_49
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 0 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) s_56 7 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_56 g_56 ep_56 bds_56 0 (dagTraceF m_56 s_56 7 f_56) cur_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def g_57 : Nat := 0x1171777175f37ff
def ep_57 : Nat := 0x1648208800001660000020a000160060004800c801060600060a040001121222120032000114144414500400
theorem epk_57 : ep_57 = edgePack fullMask g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 7, g_34), (m_27, s_27, 7, g_27), (m_56, s_56, 8, g_56), (m_53, s_53, 8, g_53), (m_54, s_54, 8, g_54), (m_30, s_30, 7, g_30), (m_37, s_37, 7, g_37), (m_49, s_49, 7, g_49), (m_28, s_28, 7, g_28), (m_38, s_38, 5, g_38), (m_47, s_47, 7, g_47), (m_32, s_32, 7, g_32), (m_40, s_40, 7, g_40), (m_52, s_52, 8, g_52), (m_55, s_55, 6, g_55), (m_44, s_44, 5, g_44), (m_3, s_3, 4, g_3), (m_43, s_43, 5, g_43), (m_15, s_15, 4, g_15), (m_48, s_48, 5, g_48), (m_31, s_31, 5, g_31), (m_45, s_45, 5, g_45), (m_36, s_36, 5, g_36), (m_35, s_35, 5, g_35), (m_42, s_42, 5, g_42), (m_33, s_33, 5, g_33), (m_41, s_41, 5, g_41), (m_29, s_29, 5, g_29)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_34
  · exact lb_27
  · exact lb_56
  · exact lb_53
  · exact lb_54
  · exact lb_30
  · exact lb_37
  · exact lb_49
  · exact lb_28
  · exact lb_38
  · exact lb_47
  · exact lb_32
  · exact lb_40
  · exact lb_52
  · exact lb_55
  · exact lb_44
  · exact lb_3
  · exact lb_43
  · exact lb_15
  · exact lb_48
  · exact lb_31
  · exact lb_45
  · exact lb_36
  · exact lb_35
  · exact lb_42
  · exact lb_33
  · exact lb_41
  · exact lb_29
theorem sub_57 : ∀ b ∈ bds_57, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x82a437a48673f657033c6c34065e6563d2160a335c2485972b56a2d529415022749f6344f5042b243d9523b32633d762ef4e27e712433b1fc471d12b1963b1494d0fb4e0a95205d4c03d200013c00001 0x5d6f036b180b1bc058c602c5f0162d80b15c058a60eb6f04db703ad8c136c406b5f035af016d6c096b405b57025ab01ad4c0d6a401b4f00da7006d1c0368601b4200d3780698c034be01a5b00d2b80694c0349e01a4b00d2380690c0346e0ea3600d1a81a57c0b2ae0294f00ca380e4fc0727a0193700c9a8064bc0324e0186f00c3180617c030b60185700c2980613c030960184700c218060dc1d06c0183500c178060ac0304e0182300c0d80605c0bcfe06e73016bf80b5f805ae60dd72016b780b5b805ad604d6a016b380b59805ac606d620163f80b1cc058de02c6b0163380b18c036fe09b7e00db9806dc8036de06b6e00db5806da8036ce04b6600db1806d88036be02b5e00dae878d70036b601b5a00dac806d60036ae02b5600daa80ad50036a601b5200da8806d400369e02b4e00da5806d280368e02b4600da1806d08034fe01a7300d378069ac034d401a6702d3300698c034be01a5d00d2d806964034ae01a5500d298069440349e01a4d00d2580691c0348a01a4300d1f8068f80347a0696f02cb380a57c052bc0395d014a780a538052840193f00c9e8064e80326e0193603c9a8104d00325e0192a00c93806498030fe0187300c378061ac030d4018670643300618c030be0185d00c2d806164030ae0185500c298061440309e0184b00c2380610c0307e0183e00c1e8060bc0305c0182b00c1480608c030440182100c0e80606c0302e0181502eb782f5ac0bace2a563142378231ac178ce08c631222f81716c0b8ae08c5300db7836db8036d601b6700db1806d88036be06b5e00dad806d68036ae04b5600da9806d480369e03b4e00da5806d280368e02b4600da1806d08034de01a6b00d3380698c034be01a5b00d2d00695c0b4ac01a5300d2780692c0348e01a4300d1f8068f80347a2316f054b582e59c152c61f15f02cad81655c152a60894f054a587451c112860193f00c9e8064ec0326e0813500c998064bc032560192700c918061bc030d60186700c3180617c030b60185a00c2b832158030a60184f00c2580611c030860183f00c1f0060f40305e0182e00c158060a4030460182200c1080607c030360181700c0981717c0b8b605c5702e29822d7c116b608b57045a9816d3c0b69605b4702da180697c034b601a5700d2980693c0349601a4700d218068fc0347601a3700d1981a57c0d2b606957034a981653c0b2960594702ca181a4fc0d27606937034998064bc032560192700c9180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc030560182700c1180607c030360181700c0981317c098b604c5702629822d7c116b608b57045a9812d3c0969604b47025a180697c034b601a5700d2980693c0349601a4700d218068fc0347601a3700d1982a57c152b60a957054a981253c0929604947024a18224fc1127608937044998064bc032560192700c9180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc0305a0182b00c1500609c0304c0182500c1180607c030360181700c098175bc0bad605d6702eb18231bc118d608c670463181717c0b8b605c5702e29806dbc036d601b6700db1806d7c036b601b5700da9806d3c0369601b4700da182a9bc154d60aa670553181697c0b4b605a5702d2982293c1149608a47045218068fc0347601a3700d198065bc032d60196700cb180657c032b60195700ca980653c032960194700ca18064fc0327a0193b00c9d0064dc0326c0193500c978064ac0324e0192300c3782e1b8030d60186700c31806188030be0585e00c2e86c170030b60185a00c2b812158030aa1a05400c298061480309e0384e00c258061280308e0284600c218061080307e0183e00c1e8060bc030560182a00c1382a098030460181f00c0f0060740d8be05c5b02e2b81b14c0d6be01b5b02dab806d4c0f69e01b4b03da3806d0c0f48c0695e024ab00e5380528c0193e0549b01617c030b60585700c2981e13c030960784700c218060fc030760183700c198060a42e02a05c5f02e2d81715c0b8a601b5f00dad806d5c036a601b4f00da5806d1c0368605a5f02d2f01696c094b405a570252b01694c0b4a407a4f01d2701e92c0549407a470152301e90c0748401a3f00d1f0068ec0347401a3700d1b0068cc034640794600c9700617c030b60185700c2980613c030960184700c218060fc030760183700c198060640bade05d6303e3782318c0b8be05c5b02e2b81714c036de01b6300daf806d6c036ae01b5300da7806d2c0368e01b4302d2f81695c0f49e07a4700d1f8068dc032de0196300caf80656c032ae0195300ca780652c0328e0194300c9f8064ec0326e0193300c9680649c0324a0186f05c3700618c030c40185f02c2f00616c030b4018570242b00614c030a40184f01c2700612c03094018470142300610c030840183f00c1f0060ec030740183700c1b0060cc03064018270b8130060940d8be05c5b02e2b81b14c036be01b5b00dab806d4c0369e01b4b00da3806d0c0d2be0695e02cad8125680b2ae04956034a981a5481129e0394e03ca580a5280f28e02946044a180e5080327e0193e00c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e0181b00c0c81717c098ba06c5b0362c81715c098aa06c530362881ed7c056ba08b5b01dac81ed5c056aa08b5301da881ad3c0b69605b47035a180694c034a201a4f00d2580691c0348601a3f00d1d8068dc034660995e00c2f826178030ba0184f00c2580611c030860183f00c1d8060dc030660182b00c1380608c0b8be06c5b02e2b81b14c0f6be02b5d045ad81ed5c056aa08b53035a7816d2c0b68e06b4300d2780692c0348e01a4300d1f8068ec0346e01a3304caf826578032b60195900cab80654c032a40195100ca801a53c0b29605947034a18224fc0f27607937044998064bc032560192a00c93806498032460185f04c2f00616c030b20185700c29806148030a20184f00c2580611c030860183f00c1d8060dc030660182f00c1580609c0304605c5f0362d81715c0d8a607b5f045ad81ed5c116a606b4f02da5816d1c0d68601a5300d2780692c0348e01a4300d1f8068ec0346e01a3304caf8265780d29e0594b02ca381a50c1127e0793b03c9b8224cc032560192a00c93806498032460985e04c1b00607803cfa05d6f026b681b5ac0dad205d67026b281b58c0dac207c6f016368231ac078d207c670163282318c078c206c5f02e2d81715c0d8a601b7100daf806d6c036ae01b5300da7806d2c0368e01b4304d378269b8134da0da6c04d358269a8134d21526804d33826998134ca1426404d31826988134c20da600352f81a9780b4b604a5a02d2b8129580d4a606a520452780e9380f49602a4a03d2380a9181148603a4200d1f8068f80347601a3a00d1b8068d80346601a3204cb304c5901328c0192e00c378061b4030d60186a00c348061a0030ce0986600c32848190030c60186100c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e0183300c0c8279f40bade04d6d036b581b5a40bace04d65036b181b5840f8de02c6d0463580f1a40f8ce02c650463180f1840d8be05c5b02e2b81b14c136de09b6d00db5806da4136ce0fb6500db1806d840d6be01b5b02dab806d4c1169e01b4b03da3806d0c134e20da700352f81a9780b4b605a5a02d2b8169580d4a606a52045278229380f49607a4a03d2381e9181148608a4200d1f8068f8134760fa3a04d1b8268d80346601a3204cb302e5901328c0192e02c2f80616c0b0ae018530442780612c0f08e0184300c1f8060ec0306e0183300c0c81b1b8098d404c660363100f178058b402c5601e29006da80b6cc01b5a03dab026d380369a06a6e02d350169980d4c408a5e03d2d01e958114a401a4e00d268069300347c01a3a04d1c83a8e00346401a3100d180265580325c0184d00c0c81b5bc0bad605d67036b181b1bc038d605c6700e3182317c038b607c5700e29826df41b6f806b6f035b7016dac0b6d405b6702db301ad8c0d6c408b5f045af01ed6c0f6b407b5703dab022d4c116a401b4f00da7026d2c1a69409b4704da3006d0c036840ba7404d2b0068f8132fa0696f034b70165ac092d405967024b301a58c0d2c40895f01caf01e56c052b407957014ab02254c072a40194f00ca702652c1329409947078a300650c032840992500c920261f40b0de0186b02c3380618c110be0185b03c2b80614c0309e0184b00c2380610c0305209b5604d3e8269f00d4dc04a6a0253301a988074bc02a5a0152b00e9480348c09a4504cbe81a5b8092d404966034b100e578052b40295601ca90065380329a0194c00ca30265141d2880194200c9a8064d0032540192900c940061f40309a0184500c148179fc0dce607d7f046b981b5bc0bad605d67036b18071fc038e601c6f00e3580719c038c601c5f00e2d80715c038a609b7f07dbf026dcc1a6e406b6f035b7016dac0b6d405b6702db301ad8c0d6c408b5f045af01ed6c0f6b407b5703dab022d4c116a401b4f00da7006d340369801b4700da3026d141268801b4300da102a9e8174ec06a6f02d3381e97c154b407a570312b00693c0349a01a4704d228068fc0347c01a3d04cbf8265f8132e609972034b781a5b80b2d60496a02cb38125980d2c606962044af80e5780f2b60295a03cab80a558112a60395200ca38065181328a0193f00c9f0064f4032780192b00c9500649c0324c0187f00c398061bc030d60186700c3180617c030b60185700c2980613c0309a0184b00c23806114030860182b00c14806084030360181900c0b80604c0302205d6f036b181f1bc118c606c5f02e2d81715c0d8a601b6f00db1806d7c036b601b5700da9806d3c0369601b4700da181a97c0b4ae07a4f0552501e91c0a48c01a3f00d1e8068dc1546a0f96f06cb703a58c1b2c40695f034af01656c092b405957024ab01a54c0d2a40894f01ca701e52c0529407947014a302250c072840193700c9b0244d4032560192a00c93806498030de0186300c2f80616c030ae0185300c2780612c0308e0184300c1f8060f4030760183700c1a8060cc030560182700c0d8060640302e0181300c088179fc0dce607d7f046b981b5bc0bad605d67036b18271fc138fc09c7304e3901b1bc0d8dc05c6b0263501719c098cc06c630363102317c078bc07c5b0162d01f15c058ac08c5301e29006dfc036e601b6f00db5806d9c036c601b5f00dad806d5c036a601b4f04da7006d34134fe09a7e04d398269c80d4de06a6e02d358169a80b4ce05a660353181a988114be08a5e03d2d81e9680f4ae07a56045298229480349e01a4e00d268069300347e01a3e00d1d8068e8134720923800d198068c80346201a3004cbd0265d80d2de0596703caf82a5680f2ae0995600ca78065380329a0194c00c9f8064dc0325e0192e00c968061fc030e60186f00c3580619c030c60185f00c2d80615c030a60184f04c27006134150980183f00c1d8060dc030660181b00c0c8060440bade06d6303e3782318c0d8be05c5b02e2b81b14c136de09b63035af816d6c0b6ae06b53045a781ed2c0f68e08b430352f81695c0f49e0aa4a03d238269180347e01a3e00d1e8265bc132c60695f02cad81655c0d2a60894f03ca581e51c112860193f00c9e8064ac0324e0186f00c3180617c030b60185700c2980613c030960184700c218060fc1307c0183d00c1580609c030360181700c098175bc0dac607c6f0463181b17c0b8b605c5703629826dbc1b6dc09b6306db101ad7c0d6bc05b5b025ad016d5c096ac06b53035a9022d3c0769c07b4b015a501ed1c0568c08b4301da10069bc034c601a5f00d2d80695c034a601a4f00d2580691c0348601a3f0491f0068f40d2be0595703ca782a5280f28e0414600c9f8064f80327a0192f00c938061bc030c60185f00c2d80615c030a60184f00c2580611c030860183f0541f0060f40305e0182b00c1380608c03036018170162f80b16c058ae02c53035af806d6c0b6ae01b53015a7806d2c0568e01b430352f81696c0b4ae06a530152780a9380549602a470152180a9080347e0aa3b0551d02a8dc1546c01a33014a30224b80b0be0185b02c2b80614c0509e0184b0142380610c0307e0183b00c1b8060cc0303201b4d00da28269f8134e406a6e02d350169980d4c402a5e00d2d006964034ac01a5200d288069400549c02a4a0152480a9200348c02a42045208229000347c01a3d00d1b0268d41346801a3204cbf0265c80d2dc0496a024b301a588052bc0195a00cab0065480529c0294a014a480a5200328c02942044a080e5000326c0993500c970064b4050bc0185900c290061440307a0183500c0c8060440bade06d630163780b18c058be02c5b0162b80b14c056de02b63015af80ad6c056ae02b5300d3780698c034be01a5b00d2b80694c0349e01a4b00d2380690c0347e01a3d00d1d8068dc0346a01a3304cb782658c0d2be0595b02cab81a54c0529e0294e00ca580651c03286019420149f80a4f8052760293900c9b80a4cc052640893101c9800649c0324c0992500c3780618c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c1580609c0304a0182300c0d80605c0302605d6f036b180b1bc058c602c5f0162d80b15c058a602b6f015b180ad7c056b602b57015a98269bc134c606a5f02d2d81695c0d4a602a4f0152700692c0349201a4700d218069080348201a400151f80a8f80547602a3900d1b80a8cc0546408a3101d180065bc032c60195f00cad80655c032a60194f00ca580651c032860193f00c9e8064ec0326e0193500c998064bc1325c0192d00c3780618c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0982e00c1680607c030360181700c098175bc0dac602c6f0163180b17c058b602c570162980adbc056c602b5f015ad80ad5c056a609a6f00d3181a97c034b605a5700d2980a93c0349602a4700d2180a8fc1147a01a3b0151b80a8d4034660996f04cb181a57c0b2b605957034a980a53c0529c0194b00ca480a51c052860294200ca08065000527e0293e0149d80a4e40526e02933014990224c4072600192f030958144a81324e0412600c918221bc030c60585f00c2d81615c030a60284f0142700612c030920284700c2180a108030820283f00c1d80a0dc030660182f00c1580609c0304605d6f036b181f1bc118c606c5f02e2d81715c0d8a61136f00db181ad7c036b605b5700da9822d3c0369607b4700da18409bc1b4dc0e26306d3101a97c0d4bc05a5b0252d01695c094ac06a530352902293c0749c07a4b0152501e91c0548c08a4301d210068fc0347c0c23b0591d0288dc1046c01a3300d1902e5a8172cc0695f02cab81e53c0e29407947018a30064fc1526e0192f00c970064b4170de0186302c2f80616c0b0ae018530442780612c0f08e0184300c1f8060ec0306e0183300c0d8060640302205c5f02e2d81715c0b8a601b5f00dad806d5c036a601b4f00da5806d1c036860195f00cad80655c032a60194f00ca580651c032860193f00c9d8064dc032660192502c2f0121580709c0284600c1f0060d80303d3b45f9ca2dce115e668a72e35f961adca8d5e4a6a72034f8f1a5c74d1e366871125f8812dc2895e124a70424f7d125bb891dbe486d723f6b11db308dd92466c315f610adae455d6a2a6a614f528a5a8851d402869b13f4c89da284dd122668512f418959f449cf42466f05f3702d99415cc20a65c04f2d02594811c9e0863d03f1e01d8dc0dc660663002f1701587009c320461801f0b00d80805c020260003f 20 1048575 8 255 11 2047 21 2097151
def cc_57_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb8482b2361ac261a774b9f68197d798e5988846186c1880f5d7d33c76e657214d6a67b643635f05358d6354a434fb4f4ac4f427853e4433677d3095e2a5642416419fa215e4111b430d04b0854b00085 0x2f3f86e7305afe0f5cc16b783d6b05ace0f58c1e3f89c7e078e60f1c81e3786c6e078d60f1a81e3384c66078c60f1880e2f81c5e038ba2adfc6dbf0ab73156e41adbc35b705b6b096d416d9c25b306b630d6c40ed7c1daf02b5b056b40ad5c15ab03b53076a40ed3c1da703b4d076980ed2c1da50ab49156900ed1c1da309b45826880ed0c1da103b4107680069fc0d3981a6f034d60699c0d3181a5f034b60695c0d2981a4f0349a0692c0d2501a49034900691c1d2301a45804880690c0d208696f0b2ce0e57c14ad02957052ac0e53c1ca68394a0728e0e5183ca2bf1440327e064f80c9e8192f0325c064880c3f81873030de061ac0c3381863030b6061680c2c81857050ac0614c0c28818470508c061140c1f8183d03076060e40c1b8183503066060c40c178182b0304e0608c0c0d818170bade2f5ac2eb3cd563058de0f1ac163383c63058be0f16c162b83c53076de36db81db583b67076c60ed881daf86b5e076b60ed681dab84b56076a60ed480da781b4e0369b2c9bc0d358ba67034c72897c0d2d85a57034a60e93c0d2582a47034860e8fc1d1e81a3b034720e8de411a81a3303463185bc3cb58b9670f2c71057c2cad859570f2a60e53c14a582947072860e4fc1c9e8393b0726f084d41c998192f0f256f849c0c918886f030d62219c0c318585f030b61615c0c298184b05094061241423828460308606104141b828360506a060bc0c1581827030461e07c0c0d8881703026175bc2eb585d670bac60b1bc163582c67058c60b17c162d82c57058a606dbc0db581b67036c606d7c0dad81b57036a606d3c0da581b47036861e9bc3d3587a670f4c61697c2d2d85a570b4a60a93c152582a4705486068fc0d1d81a3703466065bc0cb581967032c60657c0cad81957032a60653c14a70194d0328e065140ca1819420327e064ec0c9b819330325e064ac0c9381923030de2e1b80c3581867030c6061880c2f8585e030b6061680c2b84856030a6061480c23828460308a060fc0c1f0183b03074060dc0c1b0183303064060bc0c158182a0304e1e0980c118181f0303c0607426b782d63098de1718c0e2d84c570b8a60adbc15b702b63116c40ad7c15af02b5b056ae0ad4c2da902b4f0569c0ad2c15a482b47056861ad0815a083b40054de0a98c152f82a5b054ae0a94c152782a4e054960a924152382a43114840a9040d1f81a3e0347a2e5bc0cb18595f032b61255c0ca98f94f032963e51c0ca18293f1127a064ec149b82935032660a4bc0c9582927032461617c242b8684f0d08e0a0fc341e828370506a0a0bc14138181f0d02e139fc273e84e7509afe135f826be82c7f058fc0b1cc463902c6f058dc0b1ac263502c67058cc0b18c2e3102c5f058bc0b174162e02c5b0d8b40b164462c02c57058ac0b154162a02c530d8a40b144362802b7f056e60adbc15b582b67056c60ad7c15ae82b5b0d6b40ad641dac02b57056ac0ad5415aa02b53056a206d3c0da701b4d174fe069cc2d3781a6b094ce0698c352f86a5d034b606964352b90a55034a606944152788a4d0349606924152382a450348606904151f81a3b0546e068cc2cb7849670d2be1a57434ab869550529e1a53414a3829450527e0a4dc0c97869270b0fe061cc2c378186b090ce0618c2c2f8585d030b6161680c2c818580b0ae1a1582c2abb054030a60614414278284e0709a0a0fc141f0183b03072060cc1419018310305e060ac0c1381823030361605c0f3f81e7e03cfa175fc5eb985d6f09ada375ac36b485d6709aca3758c36b082c7f058fc0b1cc463902c6f058dc0b1b4163602c6b118d40b1a4463402c67058cc0b194163202c63118c40b184463002c5f058bc0b16c262d02c57058ac0b14c362902b7f056e60adbc15b682b6b056d20ad9c15b282b63056c20ad7c15ad82b57056a606d3c0da701b4d034f2069cc0d3881a5f034b60695c0d2981a4f0349a0692c0d2481a470348a0690c0d2081a3f03476068dc0d198796f0f2da1e59c3cb28795f0b2ae0a53c3ca6829470528a0a4fc149b8192f0324e061fc0c398186f030da061ac0c3481867030ca0618c0c308185f030b60615c0c298184f0509c061340c1f8283e03076060e40c198183203062060bc0c1581827030460606c0c0b84e7f0bcf6139dc2f3986d7f19afc1b5ec36bb86d730dae4075bc0eb701d6d058fe0b1f8163d82c77058e6231c8163782c6e058d6131a8163382c66058c617188162f82c5e058ba0b170162d86c5a058b223160162b82c56058aa0b150162986c52058a21b14015bf82b7b056ee0adcc15b782b6b056ce0ad8c15af82b5d056b60ad6415ab82b55056a60ad440da781b4e0369a069fc0d3d81a77034e6069ac0d3501a69034ce129980d3181a61034ae129580d2a81a4f0349a0692c0d2481a470348a0690c0d2081a3f03476068dc0d198697f0d2f61a5dc34b98596f092d61259c2cb18695f0d2ba1a56c34ab869550d2a60a53c34a68294b0528e0a51414a18293f052760a4dc14998192f032560649c0c918187f030f6061dc0c398186f030da061ac0c3381865030c60617c0c2e8185b030b20615c0c2a81853030a20613c14270184d0307e0a0f80c1d8183903066060c80c188182f030560609c0c118181f030360605c0c0985d6f17ad61759dd2b182c6f058dc0b1ac163382c63118c40b17c162f02c5b098b40b15c162b02c530d8a40adbc15b582b67056c60ad7c15ad82b57056a606d3c0da701b4d724de069ac5d3381a63704be0696c2d2b81a530549e229340d2581a490548e0a9140d2181a410547e068ec151b81a330f2de1e5ac3cb3879630f2be1656c2cab879530529e1e53414a5829470528a0a50c149f8293b0526e0a4cc0c978792b0f24e0648c44378186b110ce0618c2c2f8185b0b0ae0614c14278284e0709a0a0fc141f0183b03072060cc1419018310305e060ac0c13818230f03e0606c3c0b818130569e0ed2c15a383b430349e0692c0d2381a430347e068ec0d1b81a330309e0612c0c23818430307e060ec0c1b818330305e060ac0c13818230bade1758c163783c63058be0f16c162b83c53036de06d8c0daf81b5b036ae06d4c0da781b4b0368e06d0c4d378ba6e134c62e9882d2f85a5e0b4b6129682d2b84a560b4a6169481d2783a4e0548e0e90c1d2101a3f0347c068ec0d1d01a370346c068cc0d190b96e0f2d42e5983cb10595f0b2bc165682cab859560b2a40e53c1ca70294a0528e0a5181ca10193f0327c064e80c9b8193603264064bc0c970192d030de0618c0c2f8185b030ae0614c0c278184b0308e0610c0c1f8183b0306e060cc0c15818290304e0608c0c108181d03036060640c0b81815030221717c2e2d85c570b8a60ad7c1dad82b57076a60ad3c1da582b47076860697c0d2d81a57034a60693c0d2581a4703486068fc0d1d81a37034662e57c5cad8b957172a61653c2ca5859470b2860e4fc149d8293707266064bc0c9581927032460617c0c2d81857030a60613c0c258184703086060fc0c1d8183703066060bc0c1581827030460607c0c0d8181703026175bc2eb585d670bac60b1bc1e3582c67078c60b17c1e2d82c57078a606dbc0db581b67036c606d7c0dad81b57036a606d3c0da581b47036862e9bc3d358ba670f4c61697c2d2d85a570b4a60e93c152582a4707486068fc0d1d81a3703466065bc0cb581967032c60657c0cad81957032a60653c0ca68194b032940651c14a3019450327e064ec0c9b819330325e064ac0c9381923030de2e1b80c3581867030c6061880c2f8585e030b6061680c2b84856030a6061480c278384e0309a060fc0c1f0183b03074060dc0c1b0183303064060bc0c16b602c03056060a80c13b50260304ad00900c118181f0303c060741eb783d6e03ac6075882e378bc630b8be13174662d86c590b8ae13154662986c51036de0ad8c0daf81b5b036b206d4c0da882b4f056960ad1c15a181a6f034c60697c0d2e81a5b034b20695c0d2a81a53034a20693c0d2581a4703486068fc0d1d81a37034661e57c3cae879570f2aa1e53c2ca38293f0526e064bc0c938186f030c60617c0c2e8185b030b20615c0c2a81853030a20613c0c258184703086060fc0c1d8183703066060bc0c1581827030460606c0c0b82e7f07cfc0b9f42ebf8bd7305ade0b5b416b586d6905ace1359416b182d61058f20b1cc163882c5f058b60b15c162981b7f036e606dbc0db681b6b036d206d9c0db281b63036c206d7c0dad81b5a036ae16d580da981b4f0369606d1c0da181a7f134fc069cc0d3901a6f054dc069b4153601a6b034d4069a40d3401a67054cc06995913201a63034c4069840d3001a5f0d4bc0696c0d2d01a57094ac0694c0d2901a4f0549c0692c0d2501a470548c0690c0d2101a3f0347c068f414b78296d052ce1e5943caf859570529e0a51c0c9f819370325e064b40c9387925030fe061cc0c378186d030d6061a40c3381865030c6061840c2f8185b030ae0614c0c278184b0308e0610c0c1d8183a03072060dc0c1b01833030620609c0c1301825030360605c2eb78bd6b0bace3358d8a3788c6b178ce2318c662f85c5b0b8ae2314c0db781b6b036ce06d8c0daf81b5b036b406d5c2dab01b530369e06d2c0da381b43034de369b80d3581a67034c6069880d2f86a5e034b6069680d2b84a56034a6069480d2783a4e03496069280d2382a4603486069080d1f81a3e0347a2a5bc54b58a967152c62a57c2cad85957152a62253c54a58a94711286064fc0c9d8193703266064bc0c968192b0324e2a4940c918186f030d60619c0c318185f030b60615c0c298184f030960611c0c218183b03074060e40c1b8183603066060c40c13818260304a0607c0c0d8181703026175bc2eb187c6f118c61717c2e2d85c570b8a606dbc0db181b5f036b606d5c0da981b4f0369606d1c0da189a6f174dc2698c5d3105a5f0b4bc1696c252d05a57094ac1694c2d2908a4f0749c1e92c152507a470548c2290c1d2101a3f03476068e80d1b81a36152d42e5982caf8595e0b2ae165483ca78894a0f28e225180c9f8193a0326e064d80c978192e0325a061bc0c318185f030b60615c0c298184f030960611c0c218183f03076060dc0c198182b030520609c0c118182103036060640c0b818110bade175ac2eb385d63118de231ac463388c630b8be1716c2e2b85c53036de06dac0db381b63036be06d6c0dab81b530369e06d2c0da381b43174de2a9ac5d338aa630b4be1696c2d2b85a531149e2292c452388a430347e068ec0d1b81a33032de065ac0cb381963032be0656c0cad019570b2ac0654c0ca78194b0328e0650c0c9f8193e0327a064dc0c9a8193303264064bc0c958192703246061bc5c370186b030ce0618c0c310185f0b0bc0616c0c2d01857090ac0614c0c290184f0709c0612c0c25018470508c0610c0c21018370306c060d40c178182b030540609d7813018230303e060780c0e84d6f03ac6131bc263701c63038c40716c0e2d01c57038ac0714c5db788b630b6be12d6c25ab85b531d69e0ad3445a583b491d68e0ad1445a183b41034de0698c0d2f81a5b034ae0694c0d278ea4e0349a068fc0d1d81a37034661657c24ab8694f0d29a1a51c34a28693f0d26e064bc0c938186f030c60617c0c2d81857030a60613c74270184d0307e060ec0c1b818330305e060ac0c1381823030360605c26b781d63098de0718c0e2d81c5a038ae071580e298bb6f116c616d7c25ad84b570b6a63ad3c45a58eb4711686069bc4d3701a63034c40697c2d2f01a5b034ae0694c0d2901a4f0d49c0692c0d2481a4703486069080d2081a400347e068ec0d1d01a370546c068cc2caf849570d29e1a51c349f869370325e064b40c9386925030de0618c0c2f8185b030b40615c242b018530309e3a1380c25818490308e0610c0c21018410307e060ec0c1b818330305e060b80c168181b0302e135bc0eb184c6f038c60716c0e2d01c57038ac0714c5db788b630b6be12d6c25ab85b531f69e22d2c7da388b43034de269b80d3181a62034be169780d2d81a57034a6069480d2786a4e03496069240d2381a4303484069040d2001a3f03476068e80d1b82a3603466065bc0cb18195f032b6065680cab84956032a60653c7ca70194b032920651c0ca18194203282064fc0c9d8193703266064bc0c970192d0b0be1215c3427868470d07e1a0dc0c178182d0304e1a0940c0f8181709cfe139f4273a84d7f09afc135f45e3f88c730b8de131ac263385c630d8be0b174362d83c590d8ae0b154362983c51036fe26df80db981b72036de16db80db581b6a036ce12d980db181b62036be1ad780dae86b5c036b606d680dac81b58036ae1ad580daaad354036a606d480da881b500369e0ed380da581b4a0368e0ad180da181b42034fe069cc0d3781a6b034d40699c253301a63034be069740d2d81a5a034b2069600d2b86a56034aab09500d2981a510349e0692c0d2381a430347e068f80d1e8596f092ce1a57c34ae869570d2aa1a53c34a38193f0327a064dc349a8192f0324e061fc0c398186f030d6061a80c3384866030c60617c0c2e8185b030b4061640c2c018570d0ac06155582a01853030a20613c0c258184703086060fc0c1f0183d0305e060b80c158182903046060880c108181b0302e0f5bc1eb701d6303ac4171bc5e3185c5f098ba3b16c362c85c57098aa3b14c362881b6f056c606d7c0dad81b59036a606d4415a782b4b0568e0ad0c0d3781a63034be3a9780d2e81a4f034960691c0d2181a3f03476068dc0d198795f0f2ba1e55c3caa8794f0b28e0a4fc149b8192f0324e061bc0c318185f1d0bc061740c278184b0308e0610c0c1f8183b0306e060cc0c178182b0304e0608c0c0d8181705cfe0f9f8173e85d7f17ae60b5bc16b682d6b0dad20b59c26b282d6305ac20b1e4163982c71058be0b16c162b82c53036fe26df80db981b72036de0adb80db682b6c036d606da80db481b68036ce0ad980db2a9364036c606d880db081b60036be1ad780dad81b5a036ae12d580da981b520369e0ad380da581b4a0368e0ad180da181b42034fe069cc0d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034b40695c2d2b01a530349e0692c0d2381a430347e068f80d1e8296f052da0a59c3cb28795f0b2ae0a53c14a38193f0327a064dc3c9a8192f0324e061fc0c398186f030da061ac0c3481867030ca0618c0c308185f030b6061680c2b8c856030a60613c0c258184703086060fc0c1f0183d0305e060b80c158182903046060880c108181b0302e135bc2eb584d670bac63b1bc4e370bc6b178ce3b18c4e3103c5f078bc0716c0e2d01c57038ac0714c0e2902b6f056d60ad9c15b181b5f056b60ad5c15a981b4f0369a06d2c0da482b470568a06d0c0da081a6f034d60699c0d3181a5f034b60695c0d2981a4f1d49c069340d1f81a3b0346e068cc34b78696b0d2ce1a58c2caf8495b092ae1654c34a78694d0d2961a51c34a2869430527e0a4ec149b829330325e064ac0c9381923030de061ac0c3381863030be0616c0c2b818530309e3a1380c268183f03076060dc0c198182f030560609c0c118181f030360605c0c0984d6f0bad61359c2eb18ec6f178d62f19c763183c5f038b6071680e2b81c56038a60adbc15b582b67056c606d7c15ad82b57056a606d3c0da582b4703686069bc0d3581a67034c60697c2d2f01a5b034ae0694c0d2901a4f0549c0692c0d2481a4703486069080d2081a400347e068ec0d1d01a370546c068cc34b78696b0d2ce1a58c2caf8495b092ae1654c34a78694b0d28e1a50c149f8293b0526e0a4cc0c978192b0324e0648c0c378186b030ce0618c0c2f8185b030b40615c242b018530309e3a1380c25818490308e0610c0c21018410307e060ec0c1b818330305e060b80c168181f030360605c0c0984d6f0bad61359c2eb18fc6f178d62f19c7e3183c5f038b6071680e2b81c56038a60adbc15b582b67056c606d7c15ad82b57056a606d3c0da582b4703686069bc0d3581a67034c60697c2d2f01a5b034ae0694c0d2901a4f0549c0692c0d2481a4703486069080d2081a400347e068ec0d1d01a370546c068cc0cb78196b032ce0658c0caf8195b032b40655c24ab019530329e3e5380ca5819490328e0650c0ca1019410327e064ec0c9b819330325e064b80c968686f0d0d61a19c34318585f090b61215c2c298684f0d0961a11c34218283f050760a0dc14198182f030560609c0c118181f030360605c0c0984e7f0bcf6139dc2f3982d7f1bafc0b5ec16bb82d7305ae40b5bc1eb702d6d058fe0b1ec163b82c73058d6131a8163482c67058cc0b18c163082c57058ac0b1540dbf8db7e036f606ddc0db981b72036de16db80db581b6a036ce12d980db181b62036be0ad780dae82b5c036b606d680dac81b58036ae0ad580daaa7354036a606d480da881b500369e0ad380da581b4a0368e0ad180da181b42034fe069ec0d3b81a73034de069ac0d3501a67094cc0698c0d2f81a5d034b6069680d2c81a58034ae0a9580d2aa6254034a6069440d2781a4b0348e0690c0d1f81a3e0347a1a5fc34bd869770d2e6165bc24b5849670b2c60a57c14ae8295b052ae1a55414a98294f052960a51c14a18193f0327a064ec0c9b8693503266064bc0c958192703246061fc0c3d81877030e6061bc0c358186a030ce121980c318185f030ba0616c0c2d01859030b00615c142b018554a0a80614c0c288184f030960611c0c218183f0307c060f40c178182e03056060a40c1181822030420607c0c0d8181703026135b436b082c6d078c21b17c2e2d85c570d8a606db46db601b61036c006d7c35af01b5b036b406d5c25ab01b53036a406d3c1da701b4b0369406d1c15a301b4303684069b40d3081a5f034b6069680d2b85a56034a60693c0d2581a4703486068fc0d1f01a3d030da061840c2f8185b030b40615c642b018530309e0612c0c23818430307e060f80c1e8182f0305c060ac0c1481823030440608476b789d6e1dac627588263785c63038be071740e2b81c55038a61edbc45b187b5f056ba22d6c1dac87b57056aa22d4c1da885b4f0969612d1c2da181a6f034c60697c752f01a5d0349e0692c0d2381a430347e068ec0d1b81a33032be0657424ab849550329e1251c349f869370325e0649c0c3781863030be3a1780c2e8184f030960611c0c218183f03076060dc0c198182f030560609c0c118181b0302e3b5bc76b184c6f0b8c60717c0e2e81c57038aa0714c3db788b630f6be22d6c3dab88b530b69e12d2c25a385b43034de0698c0d2f86a5e034b6069640d2b81a53034a4069440d2801a4f0b49c0692c0d2381a4303484068fc0d1d81a37034660657c24ab8194f0928e1a4fc349b8192f0325a0649c34928186f030c60617c742f0185b030b20615c0c2981852030a20613c0c258184a0308e121180c218183f03076060dc0c198182f0305c060b40c0d8181709ade1758c7e378fc63038b6071680e2b81c56038a61edbc45b185b5f096b612d5c2da987b4f116961ed1c45a181a6f034c60697c2d2f01a5b034ae0694c0d2901a4f0d49c0692c0d2481a4703486069080d2081a400347e068ec0d1b81a33032de0658c0caf8195b032b40655c24ab019530329e3e5380ca5819490328e0650c0ca1019410327e064ec0c9b819330325e064b80c968185f090ae0613c24238683f0d06e060bc0c16818270d04a0607c0c0b84e7f0bce61b5fc6ebf06d730dae41f1fc463985c6f098d61319c2e3186c5f058ba1b16c1e2c86c57058aa1b14c1e2881b7f136fc06dcc0db901b6f0b6dc06dac0db501b67096cc06d8c0db101b5f0d6bc06d7435ae01b5b036b406d640dac01b570d6ac06d5511aa01b53036a406d440da801b4f0769c06d2c0da501b470568c06d0c0da101a7f034e6069bc0d3581a6a034ce129980d3181a5f034ba0696c0d2d01a59034b00695c352b01a55424a80694c0d2881a4f034960691c0d2181a3f0347c068f424b504967092cc1255c24ab049550d29e1a51c0c9f8193d0326e1a4d40c9781927030fe061cc0c378186b030d40619c243301863030be061740c2d8185a030b2061600c2b86856030aa801500c29818510309e0612c0c23818430307e060f80c1e8182f0305c060ac0c148182303044060840c0d81817 20 1048575 8 255 11 2047 19 524287
def cc_57_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf62a319e9ce6397b53918638cb4d84a81807437e2257934f7444f6c18365c656203c5e04057b6552c4f4af7d4624d3e979351982ff52296692781e23b3d1ee4d1757912e470df4f0954a04f460004f 0x4d6f0bad61359c2eb185c6f0b8d61719c2e3181c5f038bc071747db78bb6b176ce3ed8c2daf86b5d096b612d6825ab84b560b6aa0ad4c15a782b4d0969612d2815a382b460568a0ad1015a182a6f054d60a99c153182a5f054b60a95c152982a4f0549a0a92c152382a4505486068fc0d1d81a3703466065bc0cb581967032c60657c0cae8195b032ae065540ca98194f0329a0652c0ca38194503286064fc0c9d8193703266064bc0c9581927032461a1bc3435868670d0c61617c242d848570b0a61613c2c25858470b0861a0fc341d868370d0660a0bc141582827050460607c0c0d8181703026139fc2f3d84e770bce6175fc2ebf05d7b0baee175cc36b901d6f03adc075b4163f82c7e058f60b1dc16398dc72058de0b1b8163584c6a058ce0b198163185c62058be0b178162e82c5c058b617168162c85c58058ae0b158162a82c54058a617148162886c50056fe0adec15bb82b73056de0adac15b382b63056be0ad7415ad82b59056ae0ad5415a982b510369e06d380da681a7f034f6069dc0d3981a6f034da069ac0d3381a65034c60697c0d2e81a5b034b20695c0d2a81a53034a20693c152701a4d0347e0a8f80d1d81a3903466068c80d188697f0d2f61a5dc34b98596f092d61259c2cb18595f0d2ba1656c2cab859550b2a60a53c34a68294b0528e0a51414a18293f0d27a0a4ec149b8293505266064bc0c958192703246061fc0c3d81877030e6061ac0c3501869030ce121980c3181861030ae121580c2a8184f0509c06136f0260184b030920611c0c228184303084061040c200183f03076060dc0c198182f030560609c0c118181f030360605c0c0984d6f0bad61359c2eb185c6f0b8dc171ac2e3385c630d8c40717c0e2f01c5dc06de22dac5db388b630b6be12d6c25ab85b530b69e0ad342da583b490b68e0ad142da183b41be4de069ac5d3381a630b4be1a9740d2d84a570b4aa0694c2d2786a4d03496069242d2385a450348606904451f81a3bba46e068cc34b78696b0d2ce1a58c2caf8495b092ae1654c2ca78694d0b2961651c2ca2859430d27e1a4ec349b869330325e1a4ac3493819230b0de061ac2c3381863030b6121680c2c84857090ac0614c0c28848470908c121142c1f8183b0b06e060cc0c178182b0304e0608c2c0f8181b0b02e0604c26b784d630f8de2318c262f84c5b098ae1314c0db781b63036be06d6c0dab81b530369e06d2c0da381b43134de2e9b84d318ba62094be1296c252d04a57094ac2293c1d2707a4b054941e91c152308a4307484068fc0d1f01a3b03474068dc0d1b01a33034641a5a85cb30495f092b41255c24ab0694f0d2941a51c44a30193f0327c064dc0c990192f0325c064b40c3781863030be0616c0c2b818530309e0612c0c23818430307e060ec0c1b8183303056060a40c1381823030420606c0c0c8181703022135bc26b584d6709ac6231bc463588c67118c61317c262d84c57098a606dbc0db581b67036c606d7c0dad81b57036a606d3c0da581b47036862e9bc35358ba670d4c61297c252d84a57094a62293c352588a470d486068fc0d1d81a3703466065bc0cb581967032c60657c24af0195d032ae065540ca9819520329e0652c0ca3819430327e064ec0c9d019370326c064cc0c978192b0324e0648c0c378b86e030d60619c0c3181862030ae121580c2a8184f0709c0612c0c25018470508c0610c0c210183f0307c060ec0c1d018370306c060cc0c190182f03056060a80c13db026030460607c0c0f0181d09ade1358c263783c6e078c60f188162f82c5e038b607168162b81c56058a60b14815b782b63056be0ad6c15ab82b53056960ad2415a382b43056822e9bc0d3184a5f034b61295c0d298ca4f1949a0692c0d248ca471948a0690c0d2082a3f034760a8dc0d198495f092ae1e53c3ca6879470f28a0a4fc149b8192f0f24e161bc0c318485f030b60a15c0c298584f0b09a0612c0c24828470508a0610c0c208283f030760a0dc0c198182f030560609c0c118181b0b02e0b9fc1f3f02e7d09afe135f826b989d7205ade0b5b816b682d6c05ad60b5a826b4d956805ace0b59826b284d6405ac60b58816b082d60098fe131cc163782c6d058d6131a4163384c65058c60b1840e2f81c5e038ba0ade415b982b71056be0ad7815ae82b5c056b60ad6415ab82b55056a612d4815a883b500569e0ad2c15a382b43174fe069cc153782a6d034d6069a415338ca65034c606984252f8ca5d034b606964252b84a55034a60694425278ca4d034961291c252281a430547e068ec151b81a33052de0a5b414b387965092be1e57424ab849550929e1251c149f829370325e1e49c2c3f81873050de0a1b40c3581869050ce161940c3181861090be121782c2e8484f0909c0612c0c24818430908406104141f8183b0506e060cc0c178182b0b0540609c641301823030361605c26b684d6c09ac237580263684c61038be071780e2e82b6d076c212d7c15ae84b5b076b212d5c15aa84b53076a212d3c25a584b4709686329b40d3084a5f194ba0696c0d2c84a57094aa0694c0d2884a4f0d49a0692c252384a4503486228fc0d1d87a37034661257ab0ae0586d030c21217c242f0585d0909e121380c258184903086121080c208583f03076160dc0c198182f03056160a80c138c82603046131744db684b5d036961293c252584a47094861e8fc451d87a37114661253c0ca58494703286264fc0c9d8993703266224bc0c9587927032461617424278184b03086160fc2c178182b0b04e0608c0c0f8181b0302e0604c26b784d63138de371b84e318dc62038b607168262b81c56098a61edbc45b184b5f096b612d5c25a987b4f0569a22d2c1da487b470568a22d0c1da089a6f034c61297c0d2d84a57034a62693c652681a4b034923291c652281a4303482228fc0d1d87a3703467585b834b10495f092b41255c24ab049470928c12514349f869370325e1a49c2c3781863090be0616c242b818530b09e161342c238584503086160fc0c1d8583703066060bc0c158182703046160740c0d858170b02a135bc26b182c6f058c60b17c162d82c57058a64edbc4db713b63136c40ad7c15af01b5b036b40ad5c0dab02b53056a40ad3c15a702b47056860ad08653781a63094be0696c252b81a530549e0692c152381a431947e328f40d1d81a391946e328d40d1981a31092be1255c14a7829470727e0e4f4249b839350325e1a49c2c3781863090be0616c142b818530509e0612c1423818430b07e160f40c1d818390506e0a0d40c19818310305e060ac0c13818230b03a0606c2c0b8581509cfe139f8273989e7209afe135cc0eb781d6e03ada0b1fc163f02c731b8e40b1bc163702c6d058d80b1ac263502c69098d00b19c163302c65058c80b18c263102c61a88c00b17c162f02c5b098b40b15c162b02c53098a40adfc15b982b6f056da0adac15b482b67056ca0ad8c15b082b5f056b60ad5c15a98ca7f034e6129bc653681a6b034d21299c253281a63034c21297c352e81a5b094ae129540d2982a4f1949a0692c0d2482a470548a0690c0d2082a3f1147a068ec151b82a3503466125bc34b684967092ca1257c24ab8294f0529c0e534149f8293e05264064bc3495069271924c161fc0c398486f090dc161b4242f8485e030b6061640c2984852030a20a13c2c268184b030920a11c142281843030820a0fc0c1d8283703066060bc0c158582a0304e320980c118581d030361605c2c0a84d6f09adc135ac26b384d631bac4131bc263584c67098c60717c0e2f01c5db06de22dac5db388b63096be0ad7425ad83b59096ae0ad5425a983b510969e12d2c25a384b43194de069ac5d3381a63094be329740d2d81a59094ae129540d2981a510949e329340d2584a470948a0690c451f81a3b1946e068ceb8b78696b172ce1a58c24afd515d092b61255c24aa849530929e1252c24a3849431127e1a4ee989b869330325e1a4ac6493819230b0de061ac2c3381863090be121782c2e8484f0909c0612c0c248184309084061042c1f8183b0b06e060cc0c178182b0b0540609c6413018230b03e0606c2c0b81813098be1716c262b85c53116be22d6c45ab88b530b69e12d2c25a385b43034be0696c0d2b81a530349e0692c0d2381a430347e068ec0d1b81a330d2be1a56c34ab869530b29e1252c24a3859430d27e1a4ec349b869330325e064ac0c9381923030be0616c0c2b818530309e0612c0c23818430307e060ec0c1b818330305e060ac0c13818230303e0606c0c0b81813098be1716c262b85c53116be22d6c45ab88b530b69e12d2c25a385b43034be0696c0d2b81a530349e0692c0d2381a430347e068ec0d1b81a330d2be1a56c34ab869530b29e1252c24a3859430d27e1a4ec349b869330325e064ac0c9381923030be0616c0c2b818530309e061340c258184a0308e121180c22818430307e060ec0c1b818330305e060ac0c13818230303e0606c0c0b8181309ade175ac26b385d63118de231ac463388c630b8be1316c262b85c53036de06dac0db381b63036be06d6c0dab81b530369e06d2c0da381b430d4de1a9ac353386a630b4be1296c252b85a530d49e1a92c352386a430347e068ec0d1b81a33032de065ac0cb381963032be065740cad8195a032ae125580caa8194f032960651c0ca18193f03276064dc0c998192f032560649c0c918186f170dc061ac0c3381863030c40617c2c2f0185d0309e0e1380c258184a0308e0a1180c21818420307e060f80c1ed103c03076060e80c1b818360306b400d00c19818320305e060ac0c15018270d04c0608c0c0f8181e0303a135bc1eb184c6f098dc0f18c1e3103c5b078b40f15c1e2b03c53056de0ed8c15af83b5b056ae0ed4c15a782b4d0369606d2415a382b450768606d045d3781a630b4be0696c252b81a532549e3a9340d2581a492548e3a9140d2181a410747e068ec151b81a330b2be1255c34a78694d0d28e1a5141c9f829370325e1a49c2c37818630b0be0616c242b818530b09e0a1340c25818490508e0a1140c21818410707e060ec141d028370506c060cc0c178182b0304e0608c0c0d8581709cfe139f4273a84d7f09afc135f4163f83c73058de0f1ac163383c63058be0b1741e2d83c5a078b20f160162b86c56058aa0b1501e2983c51076fe26df81db983b72076de16db81db583b6a076ce12d981db183b62076be1ad781dae86b5c076b60ed681dac83b58076ae1ad581daace354076a60ed481da883b500369e06d380da68ba7f034e6169bc0d3584a67034c61a97c352e81a5b034b21a95c852a81a53034a20e93c0d2582a47034860e8fc1d1e81a3b034720e8dc8d1a81a3303462165bc24b38695f0d2ba1a55c34aa8394f0528e0e4fc1c9e839370d26a064bc34938587f030e6161bc0c3584867030c61617c2c2e8185b030b21615c2c2a81853030a20612c1425018490508e0a1180c21818410506e0a0d8141a8182f030560609c0c118181b0b02e075ac0eb481d6303ac2171bc263690c6b0d8d21719c263290c630d8c21717c5e2982b6f056da06dac0db481b67036ca06d8c0db082b5f076a60ad3c1da582b4707686069bc0d3581a69034c6069840d2f81a530349e0692c0d2381a430347e068ec0d1b81a33212de265b484b3899652529e1651c1c9f829370325e0649c0c378186d030d6061a40c3381865030c6061840c2f818530309e0612c0c23818430307e060ec0c1b818330305e060ac0c1381823030360605c0f3f81e7e03cfa175fc5eb985d6f09ada375ac36b485d6709aca3758c36b082c7f078e60b1bc163683c6b078d20b19c163283c63078c20b17c1e2d82c57078a60edfc4dbf03b73076e40edbc4db703b6d1b6d80edac1db503b69076d00ed9c6db303b65986c80ed8c1db103b61076c00ed7c35af03b5b076b40ed5c25ab03b53076a406d3c0da701b4d034f2069cc0d3881a5f034b60695c0d2981a4f034960691c0d2181a3f0347a068ec0d1c81a370346a068cc0d188d96f1b2da3659cb4b29295f0b2ae0e53c14a38393f0727a0e4dc4c9a8192f0324e061fc0c398186f030da061ac0c3481867030ca0618c0c308185f030b60615c0c298184b03094061240c238284603086061040c1b828360306a060bc0c1581827030460606c0c0b84e7f0bcf6139dc2f3986d7f19afc1b5ec36bb86d730dae4075bc0eb701d6d058fe0f1ec163b83c73058de0f1ac163383c63058be0b1741e2d83c59058ae0b1541e2983c51076fe36df81dbd83b77076e60edc81db785b6e076d60eda81db384b66076c60ed881daf86b5e076ba1ad701dad83b5a076b20ed601dab86b56076aa32d501da983b52076a20ed400da781b4e0369a069fc0d3d81a77034e6069ac0d3501a69034ce129980d3181a61034ae129580d2a81a4f034960691c0d2181a3f0347a068ec0d1c81a370346a068cc0d188697f0d2f61a5dc34b98596f092d61259c2cb18695f0d2ba1a56c34ab869550d2a60e53c14a582947072860e4fc1c9e8393b0726e1a4d41c998192f032560649c0c918187f030f6061dc0c398186f030da061ac0c3381865030c60617c0c2e8185b030b20615c0c2a81853030a20612c0c25018490308e0a1180c21818410306e0a0d80c1a8182f030560609c0c118181f030360605c0c0985d6f0dac6271bc4e3709c63138c41b17c362f05c5b098b41715c262b06c530d8a40adbc1db182b5f076b60ad5c1da981b4f0369a0ed2c1da481b470368a06d0c0da081a6f034c60697c0d2d81a57034a60693c0d2681a470348a0690c0d1f81a3b0346e068cc34af8995e0b2ae1e5483ca3899460f28a064fc149d029370526c064bc0c95019270324c061bc0c318185f030b60615c0c298184f0309a0612c0c24818470308a0610c0c208183f03076060dc0c198182f030560609c0c118181b0302e175bc5eb585d6723ac63b1bc6e370bc6b178ce3f18c6e310ec5f0d8bc1716c262d05c57098ac3f14c362902b6f076d60ad9c1db182b5f076b60ad5c1da981b4f0369a06d2c0da481b470368a06d0c0da081a6f034d60699c0d3181a5f034b60695c0d2981a4f0749c069340d1f83a3e03476068dc0d1981a328e2de1e5ac5cb387963232be1656c2cab879531f29f245343ca58e9478228a1e50c1c9f8293b0526e0e4cc0c978192d032560649e009281923030de061ac0c3381863030be0616c0c2b818530309e061340c25818490308e061140c21818410307e060ec0c1b818330305e060b40c15818270304a0608c0c0f8181b0302e0604c26b686d611b8da271b06e3089c600d8bc13168262b06c52056da0ed840da681b490368a06d040d3681a610749c069341d1f01a32030da061840c26818490308a061040c168182509ada1b584163683c61058be0f16c162b83c53076da36db01db083b60076be1ad781dad83b5a076ae12d581da983b520369e06d380da68da6d034c21a97c0d2d85a57034a60e93c0d2582a47034860e8fc1d1e81a3b034720e8de391a81a3303462221b40c308585f030b61615c0c298184b05094061241423828460308606104141b828360506a060bc0c1581827030464b5bc4eb712d6313ac4131bc2e3183c5f078ba0f15c1e2a83c53056de0ed8c15af82b5d036b606d6415ab82b55076a606d4415a783b4b0568e0ed0c953781a63254be3a9740d2d81a59254ae3a9540d2981a510b49e0692c252381a430747e068ec151b81a33072be0e57424ab849550729e1251c1c9f829370325e1a49c2c37818630b0be0a1740c2d81859050ae0a1540c29818510b09e0612c2423818430707e060ec141b818330305e060ac0c1381823030361605c273f85e730dafe375f836b986d72058fe0f1cc163783c6b058ce0f18c162f82c5d078b60f164162b82c55078a60f1441dbf89b7e076e60edc81db785b6e076d60eda81db384b66076c60ed881daf86b5e076ba1ad701dad83b5a076b20ed601dab86b56076ab14d501da983b52076a20ed400da781b4e0369a4a9fc0d3985a6f034d61299c0d3186a5f0d4ba0696c0d2c86a57214aa0694c0d2883a4f034960a91c0d2183a3f0747a068ec0d1c83a372346a068cc0d188496a092ce1259824ab84956092aa0e53c14a38393f0727a0e4dc349a8192f0d24e161fc0c398586f030d61219c0c318585f0b0ba0616c0c2c858570b0aa0614c0c288184b05094061241423828460308606104141b828360506a060bc0c1581827030460606c2c0b85d6f0dac60b1bc1e3182c5f078b60b15c1e2989b6f136dc26d8c4db106b5f0d6bc16d6c25ad05b57096ac1ad4c35a901b4f0369c06d1c0da181b42034de0698c0d2f81a5b034ae0694c0d2781a4b0348e0690c0d1b89a360346a1a57c2cab8394f0328e0e4fc1c9e819370326a064bc0c96819270f24a061bc0c318185f030b60615c0c298184f030960611c0c218183f0307a060ec0c1b818350305e060ac0c1381823030360605c2eb786d63138de371b84e318dc620d8be1b1782e2d84c5a0b8ae13158362986c52056de0ed8c15af83b5b056ae0ed4c0da581b490568e0ed0c0da089a6f034c61a97c0d2d85a57034a64e93e192681a4b034922691e092281a43034820e8fc0d1d82a37034661a57c2cab8394f0729c0e5341c9f8393e0526e0e4c80c978792a0f24efc4984437818630b0be0616c2c2b818530f09e0a1340c25828470508a0e0fc0c1d8283703066060bc0c1581827030461e0740c0d878171102a175bc36b189c6f138dc2718c4e3106c5f0d8bc1716c262d05c57098ac1b14c362902b6f076c60ad7c1dad82b57076a60ad3c15a681b4b0369206d1c0da281b4303682069bc0d3181a5f034b60695c0d2981a4f1349c069340d1f81a3b0346e068cc34af859570f29e265383ca68393f0326e064bc0c938186f030c60617c0c2d81857030a60613c0c268184b030920611c0c228184303082060fc0c1d8183703066060bc0c1581827030460606c0c0b85d6f0dac63b1bc763186c5f0b8b61715c362982b6f076c60ad7c1dad82b57076a606d3c0da581b47036862a9bc553186a5f0b4b61695c352983a4f0749c0e91c1d2183a420747e0e8f8151d82a37074660e8c834af859570f29e3a5381ca3879420727e0a4e8149b829360325e064b80c968186f030c60617c0c2d81857030a60613c0c258184703086060fc0c1d8183703066060bc0c168182b0304e060940c118181b0302e175bc36b189c6f138c61b17c2e2d85c570d8a60adbc1db182b5f076b60ad5c1da981b4b0368e06d0c4d3789a630d4be1696c2d2b86a530749e0e9380d2581a490348e0690c0d2101a41034800e8fc1d1f02a3b0346e0e8cc1d190196f032c60657c0cad81957032a60653c4ca70194b032920651c0ca18194203282064fc0c9d8193703266061bc0c318185f030b60615c0c298184f030960611c0c1f8183b0306e060cc0c178182d030560609c0c12818230303e0606c0c0b81813 20 1048575 8 255 11 2047 19 524287
def cc_57_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x7b3a2ed329d44c39c1971644dc0d999fcaf67b571f6a90a53b2e262a749f4c87790f7ae9cb4837640696accad01763f2b868518b092e09102b1e37a386806acc0b939142601ed301efd8007b 0x13ade1b58c163782c63058be0b16c162b82c53056de0ad8c15af82b5b056ae0ad4c4d3789a630d4be2a96c4d2b86a530549e0a9380d2581a490548e0a90c152101a41034800a8fc151f02a3b054720a8dc151982a3215462265bc0cb18695f032b62a55c0ca98294f0529c0652c0ca482947032860a5080ca08293f1527a064ec149b8293503266261bc0c318685f030b63215c0c298284f030960a11c0c218283f030760a0dc0c198a82f1505a060ac4c1384025030460607c0c0d8181703026335bc36b187c6ffe8c61b17c662d87c570d8a62adbc6db70ab63156c41ad7c35af0ab5b096b42ad5c25ab06b530d6a42ad3c1da707b4b056941ed1c15a30ab43076842a9bc0d3186a5f034b62a95c0d298aa4f034961e91c0d218695f0d2ae1e53c54a507947fc28c064fc0c9f0193d0325e064b80c917006f030c61a17c0c2d8c857030a6f813c0c2587847030862a0fc541e8183b030722a0dc401a8183303062060bc0c1581827030460606c540b83b4f076960ed1c1da181a4f034960691c0d2181a3f03476068dc0d198184f030960611c0c218183f03076060dc0c198182f030560609c0c1182b4f056960ad1c15a181a4f034960691c0d2181a3f03476068dc0d19819260309e0612c0c23818430307e060ec0c1b818330305e060ac0c13818230d8be1b16c362b86c53036be06d6c0dab81b530369e06d2c0da381b430346c1a57824ab0394ef82980a51bd8a20193e030be0616c0c2b818530309e0612c0c23818430307e060ec0c1b8183303032060540f3f01e7d09ada175a426b285d61138fc271c84e370dc6d138d82f1a85e348bc68178cc2f1945e3209c621b8c2271801e2f01c5a038ac0714815b682b69056ca0ad840da681b490568a06d040d3681a69034ca069842d2f01a520549c069340d1d02a360d2da1a59434a686945030f2061c40c26818490308a061040c168182503cfe079f80f3e84d7f0bae6135bc26b685d6b0bad21359c26b285d630bac20b1fc4e3f02c73058e40b1bc4e3702c6d1b8d80b1ac163502c69058d00b19c5e3302c65178c80b18c163102c61058c00b17c1e2f02c5d056fe0adcc15b782b6d056d60ada415b382b65056c60ad8415ad84b5a056b20ad5c15ab02b53056a20ad1c15a302b45174fe069cc5d378da6d034d6069a45d338ba65034c6069842d2f81a5b094ae0694c152782a4d03496069241523f92450348606904151f81a3b0546e068cc34b78696d0d2ce1a5942caf849570529e0a53414a3869450527e0a4dc0c9786927030f2061cc0c388585f030b61215c0c298284f0509a0612c0c24828470b08a0610c0c208283f030760a0dc0c198182f030560609c0c118181b0b02e079fc0f3f01e7d09afe175cc26b784d6d0bad6175a426b384d650bac617584363f89c7e0d8e61b1c8363789c6e0d8da331b0363586c6a0d8d21b1a036338bc660d8ca2f190363186c620d8c21b1800e2f81c5e038ba2edfc45b98bb6f056da22dac1db48bb67056ca22d8c1db085b5f096b612d5c2da986b4f0569a1ad2c1da486b470568a1ad0c1da081a7f034e6069bc0d3681a6b034d20699c0d3281a63034c20696c0d2d01a59034ae129580d2981a510348e129180d2281a3f03476068dc0d198696f0d2da1a59c34b28595f092ae1a53c34a6869470d28a1a4fc349b8192f0324e061e40c3981871030be061740c2d81857030aa0614c0c278184d03096061240c238184503086061040c1f8183b0306e060cc0c178182b0304e0608c0c0d8181703cfe079f80f3e85d7f17ae6175bc26b68bd6b0dad21759c26b28bd630dac20b1fc163f02c73138e40b1bc163702c6d058d80b1ac5e3502c69178d00b19c163302c65058c80b18c4e3102c611b8c00b17c162f02c5b098b40b15c162b02c530d8a40adfc15b982b6f056da0adac15b482b67056ca0ad8c15b082b5f056b60ad5c15a981b4f0369c06d340d3f81a73034de069b40d3581a69034ce069940d3181a61034be0696c0d2b81a530349e0a9380d2681a3f0547c068ec0d1c81a3303464068c43cb78796d0f2ce1e5943caf859570529e1e53414a3829450527e1e4f4149b829350325e0649c0c3c81873030e20617c0c2d81857030a60613c0c268184b030920611c0c228184303082060fc0c1d8183703066060bc0c1581827030460606c0c0b81e7d13adc275b44eb609d6a17ad22f5a04eb30bd6517ac8275884eb089d60098da171a4263285c61038ba0adb41db482b65076c20ad741dac82b55076a2069b40d3481a65034c21a9780d2e85a4e03484061c40c2e81859030aa061440c168182503cfa135bc26b685d6b0bad21359c26b285d630bac21b1bc4e3706c6d1b8d81b1ac363506c690d8d01b19c4e3306c65178c81b18c363106c610d8c01edbc15b688b6b076d21ed9c15b288b63076c216d7c25ad84b570b6a61ad3c15a686b4b076921ad1c15a286b4307682269bc4d3681a6b034d22699c5d3281a63034c21697c0d2d84a57034a61a93c352681a4b034921a91fa92281a4303482228fc0d1d87a37034661255824a3018710b0be0616c242b818530b09e161340c25818490b08e161140c21818410b07e060ec2c1b818330305e060ac0c138182303cfa135b436b484d650dac20b1b4163482c65058c226db84db689b6c136d42eda45db409b66176ca2ed904db109b61136c01ad7825ad04b560d6a406d380d3681a69034ca069840d2502a460546c068d40c388183d03072060d40c1881d6d0b8be1b16c2e2b86c53136da0ad7c15ae86b4f0b69616d1c35a182a5f054ba0a96c152b82a550549e0a92c152382a43034762657c0cad89957032a61a53c0ca585947032863e4fc0c9d8f937032660a4bc0c958292703246079f42eb784d6d0dad61b5a42eb384d650dac61b584163782c6e058da0b1b0163589c6a058d22f1a0163382c66058ca0b190163189c62058c237180162f82c5e058b613168162b82c56058a61b14815b782b6d056d60ada415b382b65056c60ad8415af82b5b056ae0ad4c4d3789a6d034d6069a44d338ba65034c606984352f81a5b0b4ae0694c1527f324d0349606924152382a450348606904151f88a3d034760a8dc151a81a330529c0a4f84c93018710b0be0616c2c2b818530509e0a1384426f204c0309606124142382845030860a1080c20818400507e060ec141b818330305e060ac0c13818231102a079f42eb784d6d0dad61b5a42eb384d650dac61b5843e3782c6d118d60f1a43e3382c65118c60f184362f85c5b0b8ae1b14c4db789b6e136da36db04db589b6a136d22ada04db389b66136ca2ed904db189b62136c22ad8035af86b5e0b6b612d682dab84b560d6a61ad4845a783b4e0f6960ad283da382b46116860ed080d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034ae0694c0d2781a4b0348e0690c4ca30193e0325c061c40c2f8185b030ae0614c0c278184b0308e0610c0c1f8183d03076060e40c1b8183503066060c40c178182b0304e0608c0eb781d6e03ada171bc5e3185c5f098ba2f16c362c85c57098aa2f14c36288bb6f116c62ed7c15ae88b5b076b22ed5c15aa88b53076a3e0d3c2da585b47116862e9bc0d318ba5f1b4ba0696c0d2c8ba57174aa0694c0d28f724f034961691c0d2188a3f03477d88dc0d198b95f1b2ba2e55c5caaf414f0b28e224ff889b8192fe024e061a40c31818610b09e0612c2c23818431107e060ec441b818330305e060ac0c1381823030362e05c2e2f85c5b0b8ae1714c0daf81b5b036ae06d4c0da781b4b0368e06d0c0cb68195f032b60655c0ca98194f032960651c0ca18193f03276064dc0c998585e090ac0e13814230183e0306c060781e2983c51056be0ad7415a582b47056865297c752e81a5b034b25295c752a81a53034a21693c0d2584a47034860a8fc0d1d82a37034661617c2c2e8185b030b20a15c142a81853030a21613c0c2584847030860a0fc0c1d8283703066060bc0c158182703046135f42eb88ec7d1d8f8431c4a63803c5e038b4071580e2902b7d056e206d340da482b4503682069f40d3885a5e034a40a9380d2681a3a0546c061f40c308184d03092061140c208182d0304a135f42eb882c7dda8f80b1c4163802c5f078bc0b17415be82b7c056e20edc015ad84b5a056b20ad5c15ab02b53056a20ad1c15a302b45234fa069c42d2f81a5b094ae0694c152782a4d03496069241523ec2450348606904151f81a3b0546e068cc2c3e818610b0be0616c242b818530509e0a1340c25818490508e161140c21818410507e060ec141b818330305e060ac0c13818230b8be131747e2d86c590b8ae13154762986c511d6be0ad7445ad83b591f6ae0ad5445a983b512369e16d2c2da388b430349fa49380d2581a4703486069080d1f81a3b0346e068cc0c2f8185d030b6061640c2b81855030a6061440c278184b0308e0610c0c1f8183b0306e060cc0c178182d030560609c0c1281823098be131742e2d86c5a098ae17158262a84b5f096ba06d3c0da701b4d1d4be2296c752b88a530b49e1292c252385a430d47e1a8ec351b86a33030be0616c0c2b818530309e061340c25818470308a0610c0c1f8183d03076060dc0c1a818330305e060ac0c138182309afa175c4363e8cc7c0d8e21b1c00e2f81c5e038ba0adf41db885b5f096b612d5c2da986b4f0569a1ad2c1da486b470568a1ad0c1da081a7dd24f8069c40d3801a5b034b4069640d2b84a56034a6069440d2384a460348a068fc0d1d81a3703466061f40c308185f030ba0616c0c2b81855030a60613c0c268184b030920611c0c228184303082060fc0c1d8183703066060bc0c1581827030460b17c162d82c57058a652d7c35af05b5b096b416d5c25ab14b530d6a406d2c0da501a5f034b60695c0d2981a4f034960690c0d1f81a3d030be0616c0c2b818530309e0612c0c23818430307e060f40c1d818390306e060d40c19818310305e060ac0c138182309afa1b5c4163e82c7c058e39d1c0162f82c5e058b613168162b82c56058a61b14815be82b71056be0ad6c15ab82b530369e06d380da681a7d034e20697c0d2d81a57034a60693c152701a4d0347e0a8f80d1d81a3903466068c80d188187d030c20617c0c2d81857030a60613c0c268184b030920611c0c228184303082060fc0c1d8183703066060bc0c158182703046131b4363082b6d076c3acd3c2da585b4711687a89b40d30e824f034961691c0d2188a3f03477988dc0d198b86d030a21613c0c258584703086220fc0c1d8883703066060bc0c15818270304616d3c2da585b470b6860693c0d2581a4703486068fc0d1d81a37034660613c0c258184703086060fc0c1d8183703066060bc0c1581827030461717c2e2d85c570b8a606d7c0dad81b57036a606d3c0da581b47036861697c2d2f05a5b094b41695c252b05a530b4a42293c1d2707a4b054941e91c152308a4307484068fc0d1f01a3b03474068dc0d1b01a3303464165782cab0894e1128c064f80c9b0192e030be0616c0c2b818530309e0612c0c23818430307e060ec0c1b8183303032060542e2f85c53116be22d4c2da785b4b0b68e16d0c0d2f81a530349e0692c0d2381a430347e068ec0d1b81a33172be2e54c2ca78594b0b28e1650c449f8893b1126e224cc0c978192b0324e0648c0c2f818530309e0612c0c23818430307e060ec0c1b818330305e060ac0c13818230302e0604c2eb785d63118de2318c2e2f85c5b0b8ae1714c0db781b63036be06d6c0dab81b530369e06d2c0da381b430b4be1695c452788a470347e068dc0cb78196d032ca0657c0cad81957032a60653c0ca58194703286064fc0c9d8193703266064ac0c938186f170dc061b40c2f8585e030b6061680c2b84856030a6061480c278384e03096061280c238284603086061080c1f8183e03076060e80c1b8183603066060c80c16e402c03056060a80c13e30260304b88090173f83e7e05cfa135fc2eb982d6f05ada0b5ac2eb482d6709aca0b58c16b085c7f0b8fc171cc363902c6f058dc0b1b4163602c6b058d4171a4363402c67058cc171942e3202c63058c40b184163001c5f038bc0717415bc82b73056e20ad7c15ad82b57056a60ad3c15a682b4b056920ad1c15a282b43056822e9fc0d3982a6f054da069ac0d3482a67234ca0698c0d3085a5f0d4ba0696c252b85a55034a61693c352681a4b034921691c2d2281a43034820a8fc0d1d82a37034660a5bc14b6829670d2ca1657c24ab8594f0d29a1651c2ca28293f0526e064bc34938587f030e60a1bc14368186b030d20a19c2c3281863030c20616c242d01859090ae121580c29818510908e1211824228283f030760a0dc0c198182f030560609c0c118181b0b02e079fc0f3f01e7d09afe175cc26b784d6d0bad6175a426b384d650bac6175842e3f85c7e0b8e61b1c82e3785c6e0b8da171b02e3586c6a0b8d21b1a02e3385c660b8ca171902e3186c620b8c21b1800e2f81c5e038ba2edfc45b98db6f056da22dac1db48db67056ca22d8c1db085b5f096b612d5c2da985b4f0569a16d2c1da485b470568a16d0c1da081a79034e6069c40d2f81a5d034b60695c0d2a81a530349e069340d2581a490348e069140d2181a410347e068ec0d1b81a330d2de1a5b434b3869650b2be1255c2ca78694d0b28e16514349f869370325e0649c0c3f81873030de061b40c3581869030ce061940c3181861030b6061680c2c81857090ac0614c0c28818470908c061140c1f8183b0306e060cc0c178182b0304e0608c0c0d81817 19 524287 7 127 11 2047 19 524287
def cc_57_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x8245e7cf5574d827034a6d1326af226832c61f645f02f5c42c5606450b5548883462264154d3c74e3844335d273104d2c24e2744e2542022a2a1fe2c19e601564811f370fe210d12d0a62b0634300063 0x1e7d09d6f04d6d06d6b06d6909d6704d6506d6306d6102c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5303b6f07b6e03b6d07b6c03b6b03b6a03b6903b6803b6707b6603b6507b6403b6303b6203b6103b6003b5f06b5e03b5b03b5a03b5704b5603b5303b5201a7106a5f01a5b0aa5701a5303a4f03a4d01a4b02a4707a4501a4303a3f03a3d01a3b01a3903a3707a3501a3301a3102946029360886f0886d0186b01869088670886501863018610685f0185b08857018530384f0184b02847018430383f0383d0183b01839038370783501833018310182f0182b018270182309d6f09d6304c6f04c6301c5f04c5704c5302b6f03b6302b5f02b5d03b5b03b5a02b5707b5602b5503b5302b4f03b4b02b4703b4303a6f07a6e03a6303a6202a5f02a5d03a5b03a5a03a5704a5602a5502a5403a5303a4f03a4b03a4a03a4704a4603a430996f019630695f06957019530494f0194b03947019430393f0393d0193b0293707935019330392f0392d0192b0392707925019230586f018630585f0185b05857018530484f0184b04847018430383f0183b02837018330382f0382d0182b0382705825018230181f0181b018170181304e7f04e7e04e7309e7204d7f04d7301d6f01d6e01d6d02c7f03c7302c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5303b7f07b7e03b7303b7203b6f04b6e03b6d07b6c03b6b03b6a03b6903b6803b6704b6603b6504b6403b6303b6203b6103b6003b5f04b5e03b5b03b5a03b5704b5603b5303b520aa7f01a7304a6f04a6e06a6d04a5f04a5e01a5b01a5901a5304a5201a5103a4f03a4d01a4b02a4707a4501a4303a3f03a3d01a3b01a3903a3707a3501a3301a310496f0496e0696d9d16c0496704965049620495f049570294a02947029460293702936029350192f069270587f018730486f0586d0186b01869048670486501863018610485f0585d0185b0485704855018530384f0184b02847018430383f0383d0183b01839038370583501833018310182f0582d0182b0182705825018230181b058179f56f06d6302c6f03c6302c5f03c5b02c5703c5303b6f07b6e03b6303b6203b5f06b5e03b5b03b5a03b5704b5603b5303b529e26f0aa6306a5f0aa5b9c25706a5303a4f03a4d02a4b02a4707a4503a4303a3f03a3d03a3b01a3903a3707a3503a3301a310695f069570294a02947029460293702936029350792f079270886f088630685f0885b08857068530384f0284b02847038430383f0383d0383b01839038370783503833018310882f0882b08827088230781b0781702c5f02c5b02c5702c5306b5f01b5b05b5701b5302b4f01b4b02b4701b430695f0695e0595b0495a059570495606953069520294f0194e0294b0294a029470294601943019420193f0193e0a93b0a93a0a9370a93601933019320585f0185b05857018530284f0184b0284a0284702846018430183f0183b018370183302c5f02c5b02c5702c5306b5f06b5b06b5706b5302b4f02b4b02b4702b4302a4e0aa360695e04956029460193e0a9360685f0685b06857068530284f0284b02847028430a83f0883b0a8370883307025018199a01502c5f02c5b02c5702b5f02b5e02b4f02b4e04a5f04a5b04a5704a5302a4f02a4b02a4702a4309a3f0ca3d09a3b01a3909a3709a3509a3301a310485f0485b04857048530284f0284b02847028430583f0583d0583b01839058370583505833018310582f0582b05827058230581504e7d04d7102c6f02c6e02c6d02c6c02c6b04c6a02c699846802c6702c6602c6502c6402c6304c6202c6104c6002c5f02c5e02c5b04c5a02c5904c5802c5702c5602c5304c5202c5106c5002b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5304a6f04a6d04a6b01a6904a670ca6504a6301a6104a5f04a5b04a5704a5302a4f0ca4d02a4b01a4902a4702a4502a4301a4102a3f0ca3d02a3b02a3702a3502a330294e0293e099260486f0486d0486b01869048670586504863018610485f0485b04857048530284f0584d0284b01849028470284502843018410283f0283b02837028330582f0582b05827058230581502c5f02c5b02c5702c5306b5f06b5e09b5b04b5a09b5704b5606b5306b5202b4f02b4e06a5f01a5b0aa5701a5302a4f0aa4d01a4b02a4702a4501a3b01a39099260685f0185b0c857018530284f0184b02847018430983f0f83d0183b01839098370983501833018310182f0182b01827018230981504d6d06d6904d6506d6102c6e02c6d02c6c0fc6a02c690fc6802c6602c6502c6410c6202c6110c6002c5e04c5a02c5606c5202b6d02b6902b6502b6101a6101a4d01a4901a4501a4101a3d01a350294e0293e019260986e0186d0184d0184901845018410182a01826018150981401e7d09d6f04d6d06d6b06d6909d6704d6506d6306d6102c6f02c6e02c6d02c6c02c6b09c6a02c699646802c6702c6602c6502c6402c6309c6202c610dc6002c5f02c5e02c5b04c5a02c5702c5602c5306c5202b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5301a7106a5f01a5b0aa5701a5302a4f02a4e0aa4d9124c01a4b01a4902a4702a4501a4302a4201a4101a4002a3f0aa3d01a3b02a3702a3501a330294e0293e099260986f0986d0186b01869098679506501863018610685f0185b0c857018530284f8d04d0184b01849028470284501843018410283f0183b02837018330182f0182b01827018230981504d6f04d6302c6f02c6302c5f02c5b02c5702c5313b6f09b6e13b6309b6202b5f02b5e01b5b01b5a02b5701b5602b5302b5202b4f02b4e02b4702b4302b420aa6f01a6304a5f01a5b02a5701a5302a4f0aa4d01a4b02a4702a4501a4306a3f06a3d01a3b01a3902a3702a3501a3301a310495f049570294f0294e02947029420393f0393d04937039350192f0692a069270a9260586f018630485f0185b04857018530284f0184b02847018430583f0583d0183b01839058370583501833018310182f0182b01827018230581d0181b058170581504e7f04e7e04e7309e7204d7f04d7301d6f01d6e01d6d02c7f02c7e02c730dc7202c6f02c6e02c6d02c6c02c6b04c6a02c6904c6802c6702c6602c6502c6402c6304c6202c619346002c5f02c5e02c5b04c5a02c5702c5602c5304c5202b7f02b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b530aa7f01a7304a6f04a6e06a6d04a5f04a5e01a5b01a5901a5304a5201a5102a4f0aa4d01a4b01a4902a4702a4501a4301a4102a3f0aa3d01a3b02a3702a3501a330496f0696d04967049650495f049570294f0294e0394d0293f0293e029320192f0692a069270a9260587f018730486f0586d0186b01869048670486501863018610485f0585d0185b0485704855018530284f0584d0184b01849028470284501843018410283f0183b02837018330182f0582d0182b0182705825018230581d0181b058170581501d6d09c5f06c5b09c5706c5302b5f02b5d02b5b02b5702b5502b4f02b4b02b4702b4309a6d02a5f02a5d06a4f0ca4b0ca4706a4301a3f0985f0185b09857018530684f0184b0c847018430283f0183b02837018330e82f0182b0e8270182305d6f06d6302c6f02c6302c5f02c5b02c5702c530fb6f09b6e0fb6309b6206b5f06b5e05b5b04b5a05b5704b5606b5306b5201b4f01b4e02b4b02b4a01b4701b4601b4301b4201a6f01a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310695f059570294f019470793f0793d01937019350192f019270186f018630185f0185b01857018530184f0184b01847018430183f0e83e0183d0182f0182b0182a0182701826018230181b018170cd6f06d6302c6f02c6302c5f02c5b02c5702c5318b6f0db6e0eb630db6206b5f06b5e0cb5b04b5a0cb5704b5606b5306b5201b4f01b4e02b4702b4301b420aa6f9126e01a630aa6206a5f01a5b0aa5701a5302a4f01a4b02a4a02a4702a4601a4302a3702a3602a350695f069570294f029470393f0393d07937039350192f0792d07927079257306f018630685f0185b0c857018530284f0184b02847018430e83f1e03d0183b01839108379003501833018310182f0182b01827018230181b078170cd6f06d6302c6f02c6302c5f02c5b02c5702c5303b6f03b6303b5f03b5b03b5703b5302b4f02b4e03b4d0aa6f01a6306a5f01a5b0aa5701a5302a4f01a4b01a4902a4701a4301a4102a3702a3602a350695f069570294f0294e0394d0393f0393e03937039320192f0792a079270a9260886f018630685f0185b08857018530284f0184b02847018430383f0183b03837018330182f0182b01827018230781d0181b078170881501e7d04d6d06d6904d6506d6109c6e09c6d09c6c09c6a0fc690fc6809c660fc6517c6409c6209c6109c6006c5e04c5a04c5606c5202b6d02b6902b6502b6101b4901a7101a4d01a4901a4501a410186d01869018650186102846018450183a0283605d6f06d630ec6f09c6e0ec6309c6206c5f06c5e05c5b04c5a05c5704c5606c5306c5202b6f02b6302b5f02b5b02b5702b5302b4f02b4d01b4b01b4901b4701b4501b4301b4101a6f01a6301a5f01a5b01a5701a5301a4f0ea4e01a4d01a3f01a3b01a3701a330695f059570794f0794d01947019450293f019370192f019270186f018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182d0182b0182701825018230181b0181705d6f06d631bc6f0dc6e0fc630dc6206c5f06c5e05c5b04c5a05c5704c5606c5306c5202b6f02b6302b5f02b5b02b5702b5301b4b01b4902b4702b4301b418d26f01a6306a5f01a5b05a5701a530fa4f1e24d01a4b01a490fa478c24501a4301a4102a3f01a3b02a3701a330695f059570394f0394d07947039450293f029370192f079270886f7206e01863088620585f0185b05857018530284702846028450283f0183b0283a0283702836018330182f0182b01827018230181b0781a07817078169756f06d6302c6f02c6e02c630dc6202c5f02c5e02c5b04c5a02c5702c5602c5306c5202b6f02b6302b5f02b5b02b5702b539426f0aa6306a5f0aa5b9225706a5302a4f8f24d02a4b01a4902a4702a4502a4301a4102a3f8e23d02a3b02a3702a3502a330695f069570294f0294e0394d0293f0293e029320792f0792a079277e1267106f088630685f0885b53057068530284f8b04d0284b01849028470284502843018410283f0283b02837028330a82f0882b1d027088230781d0781b078170301502c5f03c5b02c5703c5306b5f06b5b06b5706b5303b4f02b4b02b4703b4302a460695e049560394e0193e0a9360685f0685b06857068530384f0284b02847038430883f0883b0883708833018190881502c5f03c5b02c5703c5306b5f0cb5b0cb5706b5301b4b01a5f01a5b01a5a01a5704a5601a5301a4f03a4e01a4b01a4301a4201a3f13a3e01a3d019260185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b01827018250182302c5f03c5b02c5703c5306b5f06b5e09b5b04b5a09b5704b5606b5306b5201b4b01b4a01a5f01a5b01a5701a5301a4f01a4b01a4301a3f01a3d019260185f0185b01857018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b018270182302d7d02d6f03d6b02d6703d6302c7d03c6f06c6e03c6b03c6a03c6704c6603c6303c6201b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4a01b4901b4801b4703b4601b458834401b4301b4101a6f06a6e01a6b01a6a01a6704a6601a6301a6201a5f03a5e01a5b01a5a01a5702a5601a5301a5201a4f03a4e01a4d03a4c01a4b01a4a01a4901a4801a4703a4601a458724401a4301a4201a4101a4001936019260186f0186b01867018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182d0182b01829018270182501823018210cd6f06d6307c6f8646306c5f0cc5b07c5706c5301b6f01b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f0da6e01a6301a6201a5f06a5e01a5b01a5a01a5704a5601a5301a5201a4f03a4e01a4b01a4a01a4702a4601a4301a420695f069570794f079470193a019370193601927019260a9250186f018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b01829018270182501823018210181b0181706c5f05c5b05c5706c5301b5f01b5b01b5701b5301b4f01b4b01b4701b4307a460695f0695e0595b0495a059570495606953069520794f0394e0794b0294a079470294607943039420193f0193e0193b0193a019370193601933019320185f0685e0185b0185701853018520184f0184b0184a0184707846018430183f0183b0183a01837018360183306c5f06c5b06c5706c5306b5f01b5b06b5701b5307b4f01b4b07b4701b4307a4601a3e0695e049560394e029460a9360685f0185b06857018530784f0184b07847018430183f0183b0183701833018198401502c5f03c5b02c5703c5306b5f06b5e09b5b04b5a09b5704b5606b5306b5202b4b02b4a06a5f01a5b0aa5701a5303a4f01a4b01a4309a3f09a3e0aa3d0993e0685f0185b08857018530384f0184b02847018430883f0883d0183b01839088370883501833018310182f0182b018270182302c5f03c5b02c5703c5306b5f0cb5b0cb5706b5301b4b06a5f09a5b04a5a09a5704a5606a5303a4f03a4e02a4b03a4303a4203a3f03a3e029460993e0192e0685f0185b08857018530384f0184b02847018430883f0183b08837018330882f0882d0182b08827088250182302c5f03c5b02c5703c5306b5f09b5b09b5706b5306a5f09a5b04a5a09a5704a5606a5303a4f03a4e02a4b02a4703a4303a4203a3f03a3e01a3b01a3903a3703a3303a3201a3101a300695f0195b0a957019530394f0194b02947019430993f0993e0193b01939039370193309932019310685f0185b08857018530384f0184b02847018430883f0183b08837018330882f0882d0182b0882708825018230181f0181b018170181302d7d02d6f03d6b02d6703d6302c7d03c6f06c6e03c6b03c6a03c6704c6603c6303c6206b6f06b6e09b6b04b6a09b6704b6606b6306b6203b5f03b5e02b5b02b5a02b5702b5603b5303b5203b4f03b4e03b4d03b4c03b4b03b4a09b490ab4803b4703b4609b458234403b4303b4203b4103b4006a6f01a6b0aa6701a6303a5f01a5b02a5701a5303a4f03a4d01a4b03a4a01a4901a4803a4703a460aa458124401a4301a410295603946801440193e0192e0686f0186b08867018630385f0185b02857018530384f0384d0184b01849038470884501843018410883f0883d0183b01839088370883501833018310182f0182b0182701823 20 1048575 8 255 11 2047 20 1048575
def cc_57_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xe20b36742d44b33d28c75030ca1c0262e2bcb5a62c5a2abeb27fe09a8ae3c5c8b676074d78139b8cf5eded760a59a7d52294af3504ce38320d0a02bd0c7e62169203f360bc80005e 0x1c5b01c5a04b5f04b5b04b5704b5307b4f02b4d19b4b03b4907b4702b4519b4303b4104a5f01a5b01a5306a4f06a4d0aa3f01a3b07a3701a330485f0185b04857018530584f0584d0184b01849058470584501843018410583f0183b05837018330182f0182b01827018230581504d7d04d7c04d71be57004c7d04c7101c5f01c5e01c5d02b7d03b7104b5f02b5d04b5b03b5904b5702b5504b5303b5104b4f04b4b04b4704b430aa7d01a7104a5f04a5e06a5d04a4f04a4e01a4b01a4901a4304a4201a410aa3f01a3b07a3701a330587d018710485f0585d0185b01859048570485501853018510484f0584d0184b0484704845018430583f0183b05837018330182f0582d0182b018270582501823058150cc5f04c5d06c5b06c590cc5704c5506c5306c5101b5301b5102b4f03b4b02b4703b4302a5f02a5d06a4f01a4b0aa4701a4301a3b02a3701a330885f0885d0185b01859088570885501853018510684f0184b08847018430383f0183b02837018330182f0182b0182701823088150cc5f06c5b0cc5706c5302b5f02b5d03b5b03b5a02b5707b5602b5502b4f03b4b02b4703b4302a5f02a5d03a4f03a4b03a4703a4301a3f01a3e01a3d0885f0185b08857018530684f0184b08847018430383f0183b02837018330382f0182b038270182304d7d06d7102c7d03c7102c5f03c5b02c5703c5303b7dbc37c03b7103b7003b5f06b5e03b5b03b5a03b5704b5603b5303b5201b4f01b4e01b4d0aa7dbb27c01a7101a7006a5f01a5b0aa5701a5301a4b02a4a01a4902a4702a4601a4301a4102a3702a3602a350887d018710685f0185b08857018530384f0184b02847018430383f0383d0183b01839038370883501833018310182f0182b01827018230881504c6d06c6102b6d03b6106b4fc034b07b4706b43bf26d01a6106a4f0aa4bbd24706a43ba23f07a3b07a370aa330b86d018610684f0b84b0b847068430b83f0783b078370b8330a82f0b82b0b8270a8230b81505b4f05b4b05b4705b4301a4f01a4b01a4701a4301a3f01a3b01a3701a330184f0184b01847018430183f0183b01837018330182f0182b018270182306c5f05c5b05c5706c5306b5f01b5b05b5701b5307b4f01b4b07b4701b430695f0695e0595b0495a059570495606953069520794f0394e0794b0294a079470294607943039420193f0193e0a93b0a93a0a9370a93601933019320585f0685e0185b0685a058570685601853068520784f0784e0184b0784a078470784601843078420183f0a83e0183b0a83a018370a836018330a83206b4f06b4b06b4706b4306a4f06a4b06a4706a4307a3f07a3b07a3707a330684f0684b06847068430783f0783b07837078330a82f0a82b0a8270a82306c5f06c5b06c5706c5306b5f06b5b06b5706b5307b4f07b4b07b4707b430695e049560394e029460193e0a9360685f0685b06857068530784f0784b07847078430a83f0a83b0a8370a83301819b8018b7015b601403c5f03c5d02b5f02b5d02b4f03b4b03b4309a5f09a5d09a5b01a5909a570ea5509a5301a5106a4f04a4b04a4706a4303a3f02a3b02a3703a33049460885f0885d0585b01859088570885505853018510584f0484b04847058430383f0283b02837038330882f0582b088270582302c7d02c6f03c6b02c6703c6302c5f02c5d03c5b03c5902c5702c5503c5303c5102b7d03b6f06b6e03b6d06b6c03b6b03b6a03b6704b6603b6504b6403b6303b6203b5f06b5e03b5d06b5c03b5b03b5a03b5903b5803b5706b5603b55b435403b5303b5203b5103b5006a6f04a6b04a6706a6306a5f06a5d06a5b01a5906a5710a5506a5301a5103a4f02a4b02a4703a4303a3f03a3d03a3b01a3903a3711a3503a3301a3104966049560586f0486b04867058630685f0685d0585b01859068570885505853018510384f0284b02847038430383f0383d0383b01839038370883503833018310882f0582b088270582304c6f04c6d07b6f02b6d09b6b03b6907b6702b6509b6303b6106b4f04b4b04b4706b4301a6301a6106a4f04a4701a430aa3f01a3b07a3701a330986f0986d0186b01869098670f86501863018610584f0184b04847018431283f0183b07837018330182f0182b018270182301e7d04d6f04d6d06d6b06d6904d6704d6506d6306d6106c6f09c6e06c6d0dc6c06c6b06c6a06c6906c6806c6709c6606c65b246406c6306c6206c6106c6007b6f02b6d09b6b03b6907b6702b6509b6303b6106b5f04b5b04b5706b5306b4f02b4d06b4b03b4906b4702b4506b4303b4101a7106a5f01a5b04a5701a5306a4f06a4d01a4b01a4906a470aa4501a4301a410aa3f01a3b07a3701a3304956049460986f0986d0186b01869098671586501863018610585f0185b04857018530684f0684d0184b0184906847a904501843018411283f0183b07837018330182f0182b018270182309e7d09e7c01d6d09c7d01c5a07b6d0eb6907b6510b6102b4d03b4902b4503b4109a7d06a6e06a6d06a5e06a5206a4d1086d018690e865018610984d0184910845018410a82d0e8250fd6f09d6e0fd6309d6204c6f05c6301c5f01c5d05c5b05c5901c5701c5501c5301c5107b6f08b6307b5f02b5d08b5b03b5907b5702b5508b5303b5105b4f04b4b04b4705b4301a6f01a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330195f0195d05957059550194f049470693f069370192f019270186f01863018570e856018550184f0184b01847018430183f0183b01837018330182f0182b0182a0182701826018230181b018170ed6f0dd6eb05630dd6204c6f06c6301c5f01c5d04c5701c5506c5307b6f10b6307b5f02b5d0eb5b03b5907b5702b5510b5303b5106b4f04b4b04b4706b430aa6f01a6306a5f06a5e06a5d06a4f06a4e01a4b04a4701a4306a420aa3f01a3b07a3701a330695f0495d04957049550694f049470693f069370192f0692d06927069257506f018631085faf05d0185b018590e8572205501853018510584f0184b04847018431083f0183b07837018330182f0a82d0182b0182721025018230181b0681711d6f09d6e11d6309d6204c6f06c6303c5f03c5d03c5703c5503c5302b6f03b6302b5f02b5d01b5b01b5902b5702b5503b5301b5102b4f03b4b02b4703b430aa6f01a6306a5f02a5d01a5b01a5902a5702a5501a5301a5106a4f01a4b04a4701a4303a3f01a3b02a3701a330395f0395d04957049550394f049470393f0393d02937069350192f069270886f018630885f0885d0185b01859088570885501853018510584f0184b04847018430383f0183b02837018330182f0182b01827018230181b0681704e7f06e7306d7f0dd7e06d7306d7202c7f03c7302c6f03c6b02c6703c6302c5f02c5d03c5b03c5902c5702c5503c5303c5103b7f09b7e03b7303b7203b6f06b6e03b6b03b6a03b6704b6603b6303b6203b5f06b5e03b5d06b5c03b5b03b5a03b5903b5803b5706b5603b55ad35403b5303b5203b5103b5001b4f01b4e01b4d0aa7f01a7306a6f01a6b04a6701a6306a5f06a5d01a5b01a5906a570aa5501a5301a5101a4b02a4a01a4902a4702a4601a4301a4102a3702a3602a350496a04967049660495704956049550394f0394d02947069450393f0393d03937069350192f069270887f018730586f0186b04867018630685f0685d0185b01859068570885501853018510384f0184b02847018430383f0383d0183b01839038370883501833018310182f0182b01827018230181b0681707a4d07a450f94d0f9450585e058520684e0584d0581a0f81609d7d09d7c01d6a09c7d01c6a07b5d08b5907b5508b5102b4d03b4902b4503b410fa5d01a590fa5501a5109a4d01a490fa4501a4109946ab1440587d0586e058620685e0585d0584d0582a0f82601e7d04d6d05d6904d6505d6109c6e09c6d09c6c09c6a0fc6917c6809c660fc650fc6409c6209c6109c6001c5a02b6d03b6902b6503b6102b4d03b4902b4503b4101a7101a4d01a4901a4501a410186d0186901865018610585e018520684e0184d0182a0182604d6f05d630ec6f09c6e0ec6309c6205c5f05c5e01c5b01c5a01c5701c5601c5301c5207b6f08b6305b5f04b5b04b5705b5307b4f02b4d08b4b03b4907b4702b4508b4303b4101a6f01a6301a5f01a5b01a5701a5301a470ea4601a4501a3f01a3b01a3701a330195f049570194f0194d06947069450693f069370192f019270186f018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182d0182b0182701825018230181b0181704d6f05d630fc6f0dc6eaa4630dc6201c5b01c5a04c5701c5605c5307b6f08b6305b5f04b5b04b5705b5307b4f02b4d08b4b03b4907b4702b4508b4303b41a926f01a6305a5f01a5b04a5701a530fa4fa824d01a4b01a490fa472224501a4301a4108a3f01a3b07a3701a330595f049570594f0494d04947049450693f069370192f069270586f018630585f0585e0185b0485701853058520584f0684e0584d0583f0183b05837018330182f0182b0582a0182720026018230181b0581a058170681604d6f06d6306c6f0dc6e06c6306c6207b6fb336306b5f04b5b04b5706b5306b4f02b4d06b4b03b4906b4702b4506b4303b41b126f0aa6306a5f04a5b04a5706a5306a4f06a4d06a4b01a4906a47ae24506a4301a41ac23f07a3b07a370aa330495a04957049560494704946049450693f069370692f069277406f058630585f0485b04857058530684f0684d0584b0184906847a704505843018414403f0583b07837058330a82f0582b1f027058230581b0681704c5f04c5b04c5704c5304b5f04b5b04b5704b5307b4f07b4b07b4707b4304a5e049560394e029460193e0a9360485f0485b04857048530584f0584b05847058430583f0583b0583705833018190581502b5f03b5b03b5902b5703b5303b5102b4f03b4b02b4703b4304a5f04a5e03a5b03a5903a5703a5303a5203a5103a5004a4f04a4e04a4b04a4903a4704a4304a4206a410495f0695d0495b0495704955049530494f0494b04947049430393f0293b02937039330992f0992b09927099230485f0585d0485b0485704855048530484f0484b04847048430383f0283b02837038330582f0582b05827058230581f0581b058170581302c7d02c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5302b7d03b6f04b6e03b6d06b6c03b6b03b6a03b6903b6803b6704b6603b6504b6403b6303b6203b6103b6003b5f04b5e03b5d06b5c03b5b03b5a03b5704b5603b5504b5403b5303b5204a6f06a6d04a6b01a6904a6704a6504a6301a6104a5f04a5b04a5704a5303a4f02a4b02a4703a4303a3f03a3d03a3b01a3903a370ca3503a3301a310496e0495e03936a41340486f0586d0486b01869048670486504863018610485f0485b04857048530384f0284b02847038430383f0383d0383b01839038370583503833018310582f0582b058270582304d6f04d6e04d6306d6204c6f04c6307b6fa336304b5f02b5d04b5b03b5904b5702b5504b5303b5104b4f04b4b04b4704b430ca6f0aa6304a5f06a5d04a5b01a5904a5704a5504a5301a5104a4f04a4b04a4704a430ca3f07a3b07a370aa330495f0495e0695d0494f0494e049420693f069370692f069270586f058630485f0585d0485b01859048570485504853018510484f0484b04847048430583f0583b05837058330582f0582b05827058230581b0581705c5f04c5b04c5705c5305b5f01b5b04b5701b5307b4f01b4b07b4701b430595f0595e0195b0195a049570195605953059520794f0394e0794b0294a079470294607943039420193f0193e0a93b0a93a0a9370a93601933019320585f0585e0185b0485701853058520584f0184b0584a0584707846018430183f0183b0583a018370a8360183306c5f04c5b04c5706c5306b5f04b5b04b5706b5307b4f07b4b07b4707b4304a560695e0394e029460193e0a9360585f0485b04857058530784f0584b07847058430a83f0583b0a8370583301819a101504e7d04d7102c6f02c6d03c6b03c6902c6702c6503c6303c6102c5f03c5b02c5703c5303b6f04b6e03b6d04b6c03b6b03b6a03b6903b6803b6704b6603b6507b6403b6303b6203b6103b6003b5f04b5e03b5b03b5a03b5704b5603b5303b5204a6f04a6d04a6b01a6904a670ca6504a6301a6104a5f04a5b04a5704a5303a4f03a4d02a4b02a4707a4503a4303a3f03a3d03a3b01a3903a3707a3503a3301a3102946029360486f0486d0486b01869048670586504863018610485f0485b04857048530384f0284b02847038430383f0383d0383b01839038370583503833018310582f0582b0582705823 18 262143 7 127 11 2047 20 1048575
def cc_57_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x8e02b8a33d852517d37f7577c716416c74f66463603615d82b5993f54a4f4fb4f4bb40435863b97c3734630a692a76328f182513e1ec651c5271863f15f2711c430df3d0bf2009e210722c0324000032 0x6c5f06c5e03c5b03c5a03c5703c5603c5303c5202b5f03b5b02b5703b5301b4b01b4906a5f01a5b04a5701a5302a4702a4501a3b02a3701a330585f0185b04857018530884f0884d0184b01849088470884501843018410383f0183b02837018330182f0182b018270182304e7d06d6e02c6f03c6b02c6703c6303c5902c5503b6f06b6e03b6b03b6a03b6704b6603b6303b6203b5903b5803b55de35401b4f01b4e01b4d06a6f01a6b04a6701a6301a590ca5501a4b02a4a01a4902a4702a4601a4301a4102a3702a3602a350586f0186b048670186301859088550384f0184b02847018430383f0383d0183b01839038370883501833018310182f0182b018270182304d6f03d6304c6f04c6e03c6303c6203c5b03c5a03c5703c5603c5302b6f03b6302b5f03b5b02b5703b5302b4f02b4d01b4b01b4902b4702b4503b4301b410ca6f01a6306a5f01a5b04a5701a5306a4f02a4d01a4b01a4902a4702a4501a4301a4103a3f01a3b02a3a02a3702a3601a330695f049570694f0694d06947069450393f0393d02937069350192f069270886f018630585f0185b04857018530884f0884d0184b01849088470884501843018410383f0183b02837018330182f0182b01827018230181b0681704e7f04e7d04e7504d7f04d7e04d7d02c7f03c7302c6f03c6b02c6703c6302c5f02c5d03c5b03c5a03c5903c5802c5706c5602c5502c5403c5303c5103b7f09b7e03b7303b7203b6f06b6e03b6b03b6a03b6704b6603b6303b6203b5f06b5e03b5d06b5c03b5b03b5a03b5903b5803b5706b5603b55dc35403b5303b5203b5103b5001b4f01b4e01b4d0ca7f01a7306a6f01a6b04a6701a6306a5f06a5d01a5b01a5906a570ca5501a5301a5101a4b02a4a01a4902a4702a4601a4301a4102a3702a3602a350696f049670695f0695d06957069550394f0394d02947069450393f0393d03937069350192f069270887f018730586f0186b04867018630685f0685d0185b01859068570885501853018510384f0184b02847018430383f0383d0183b01839038370883501833018310182f0182b01827018230181b0681701e7f01e7e01e7d0cd7f0cd730cd6f04d6d0cd6b06d690cd6704d650cd6306d6102c7f03c7302c6f02c6d03c6b03c6a03c6903c6802c670dc6602c6502c6403c6303c6102c5f03c5b02c5703c5303b7f09b7e03b7d0db7c03b7503b7303b7202b6f02b6e02b6d02b6c03b6702b6503b6303b6203b6103b6003b5f06b5e03b5b03b5a03b5704b5603b5303b5201b4f01b4e01b4d01a7901a7301a7101a5f01a5b01a5701a5301a4b01a4a01a4901a4702a4601a4301a4101a3702a3601a350a96f0a96d0a9670a9650a95f0a9570394f0394d029470a9450393f0393d03937099350192f019270187f018730186f0186d0186b01869018670186501863018610185f0185b01857018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181704d7d06d7102c7d02c7c03c7103c7002c5f03c5b02c5703c5302b7d02b7c03b7103b7003b6d0db6c03b5f06b5e03b5b03b5a03b5704b5603b5303b5201b4f01b4e01b4d01a7d01a6101a5f01a5b01a5701a5301a4b01a4a01a4901a4702a4601a4301a4101a3702a3601a350187d018710185f0185b01857018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b018270182309d6f06d6302c6f03c6302c5f03c5b02c5703c5309b6f0db6e09b630db6206b5f06b5e0cb5b04b5a09b5704b5606b5306b5201b4f01b4e02b4703b4301b4209a6f01a6306a5f01a5b0aa5701a5303a4f01a4b02a4701a4307a3f02a3d01a3b02a3702a350695f069570394f0394e02947039420393f0393e0393d0192f0792a079270a9260886f018630685f0185b08857018530384f0184b02847018430883f0883d0183b01839088370883501833018310182f0182b01827018230781d0181b07817088150cd6fdd56b0cd67db56302c6f03c6b02c6703c6302c5f03c5b02c5703c5303b6f0db6e03b6b03b6703b6303b6203b5f06b5e03b5b03b5a03b5704b5603b5303b5201b4f01b4e01b4dda26f01a6bd926701a630ca5f01a5b0ca5701a5301a4b02a4a01a4902a4702a4601a4301a4102a3702a3602a35c416f0796bba16707963ac15f0795b0c957079530394f0394d0294b029478e145039430393f0393d0393b03937d8135039330192f0792b0a927019230886f0186b08867018630885f0185b08857018530384f0184b02847018430383f0383d0183b01839038370883501833018310182f0182b01827018230781f0181b08817018130cd6f0cd6b0cd670cd6302c6f02c6b02c6702c6302c5f02c5b02c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f02b4e01b4d01b4701b4501b4301b4201a6f0da6e01a6b01a6701a6301a6201a5f06a5e01a5b01a5a01a5704a5601a5301a5201a4702a4601a4501a3f01a3e01a3d0796f0796b07967079630795f0795b07957079530294f0294b02947029430193f0193b01937019330192f0192d0192b0192707925019230186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b01829018270182501823018210181f0181b018170181302c5f02c5b02c5702c5302b5f02b5e02b5b02b5a02b5702b5606b5306b5201b4b01b4a06a5f01a5b04a5701a5302a4f01a4b01a4303a3f03a3d0585f0185b04857018530284f0184b02847018430b83f0b83d0183b018390b8370b83501833018310182f0182b018270182304e7d06d6e02c710dc7002c6f02c6e02c6b04c6a02c6702c6602c6306c6202c59d545802c5502c5402b6f02b6b02b6702b6302b5902b5501b4f01b4e01b4d06a6f01a6b04a6701a6301a590ca5502a4f02a4e03a4d02a3f02a3e01a3b01a3901a3302a3201a310586f0186b0486701863018590b8550284f0b84d0184b01849028470284501843018410283f0183b02837018330182f0182b018270182304d6f02d6302c6f02c6302c5f02c5b02c5702c5302b6f02b6e04b6304b6202b5f02b5b02b5a02b5702b5602b4f02b4e01b4b01b4a02b4701b4602b4302b420ca6f01a6306a5f01a5b04a5701a5302a4f01a4b02a4701a4303a3f03a3d01a3b01a3906a3703a3501a3301a310695f049570294f0694d02947029450693f0693d06937069350192f069270b86f018630585f0185b04857018530284f0184b02847018431183f0f83d0183b01839118370f83501833018310182f0182b01827018230181b0681704d6f02d6304c6f0cc6301c5b04c5706c5302b6f02b6e02b6902b6309b6202b6102b5f02b5e02b5b02b5702b5306b5202b4f02b4e02b4b02b4902b4702b4306b4202b4103b4002a6f02a6302a5f02a5b02a5702a5302a4f02a4e02a4b02a4902a4702a430ea4202a4101a3f01a3e01a3d0695f049570694f069470293f0693d02937029350292f0692d02927029250b86f018630585f0185b04857018530e84f0184b0e847018430283f1083d0183b0283702835018330282f0182b02827018230181b0681704d7e01d7201d6a01d6602c7e09c7202c6e04c6a02c6605c6202c5e02c5d02c5c0fc5a02c590fc5802c5602c5502c540fc5202c5114c5002b5d02b5902b5502b5101b4e01b4d01a5d01a5901a5501a5102a4e01a4d02a3e01a3901a3201a310695d069550694d029450693d029350b87e018720586e018620685e0185d0184d0184a0184901848028460184502844018410183a028360182a018260181a0681604e7f04e7d04e7504d7f04d7e04d7d02c7f02c7e02c7902c7309c7202c710dc7002c6f02c6e02c6b04c6a02c6702c6602c6306c6202c5f02c5e02c5d02c5c02c5b06c5a02c59d345802c5702c5602c5502c5402c5306c5202c5106c5002b7f02b7302b6f02b6b02b6702b6302b5f02b5d02b5b06b5a02b5903b5802b5702b5602b5502b5402b5302b5101b4f01b4e01b4d0ca7f01a7306a6f01a6b04a6701a6306a5f06a5d01a5b06a5a01a5901a5806a5706a560ca55d225401a5301a5102a4f02a4e03a4d02a3f02a3e01a3b01a3901a3302a3201a310696f049670695f0695d06957069550294f0694d02947029450293f0693d02937029350192f069270b87f018730586f0186b04867018630685f0685d0185b0185906857d105501853018510284f1584d0184b01849028470284501843018410283f0183b02837018330182f0182b01827018230181b0681701e7f01e7e01e7d0cd7f0cd730cd6f04d6d0cd6b06d690cd6704d650cd6306d6102c7f02c7e02c7902c7309c7202c710dc7002c6f02c6e02c6d02c6c02c6b02c6902c6303c6202c6103c6002c5f02c5e02c5b04c5a02c5702c5602c5306c5202b7f02b7302b6f02b6d02b6b0db6a02b6903b6802b6702b6602b6502b6402b6302b6102b5f02b5b02b5702b5301b4f01b4e01b4d01a7901a7301a7101a5f01a5b01a5701a5301a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a310796f0796d07967079650795f079570294f0794d02947029450293f0793d02937029350192f019270187f018730186f0186d0186b01869018670186501863018610185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b01827018230181b0181704d7d06d7102c7d02c7c02c7103c7002c610dc6002c5f02c5e02c5b04c5a02c5702c5602c5306c5202b7d02b7c02b7103b7002b5f02b5b02b5702b5301b4f01b4e01b4d01a7d01a6101a5f01a5b01a5a01a570ca5601a5301a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a3101a300187d018710185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182d0182b01827018250182305d6f0bd6b05d6715d6310c6f0dc6e0bc6b0bc670fc630dc6210c5f06c5e05c5b04c5a05c5704c560fc5306c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4d01b4b01b4901b4701b4501b4301b4101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330796f0796b07967079630795f0595b05957079530794f0794d0794b0794707945079430293f0293b02937029330192f0192b01927019230186f0186b01867018630185f5e05e0185b0185701853018520184702846018450183f0183b0183a0183702836018330182f0182b0182a0182701826018230181f0181b01817018130cd6fd456b0cd67d056302c6f02c6e02c6b02c6702c630dc6202c5f02c5e02c5b04c5a02c5702c5602c5306c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4e01b4dcf26f01a6bce26701a630ca5f01a5b0ca5701a5302a4f02a4e03a4d02a3f02a3e01a3b01a3901a3302a3201a310796f0796b07967079630795f0795b07957079530294f0794d0294b0294702945029430293f0793d0293b0293702935029330192f0792b07927019237606f0186b66067018635d05f0185b0c857018530284fcd04d0184b01849028470284501843018410283f0183b02837018330182f0182b01827018230781f0181b078170181302b4f03b4b02b4703b4301a4f01a4b01a4701a4301a3f01a3b01a3701a330184f0184b01847018430183f0183b01837018330182f0182b01827018230cc5f0cc5b0cc570cc5302b5f03b5b02b5703b5302b4f03b4b02b4703b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3701a3501a330a95f0a95b0a9570a9530a94f0a94b0a9470a9430393f0293b02937039330192f0192b01927019230185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b01817018130cd6f0cd6b0cd670cd6302c6f03c6b02c6703c6302c5f03c5b02c5703c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4a01b4702b4601b4501a6f0da6e01a6b01a6701a6301a6201a5f06a5e01a5b01a5a01a5704a5601a5301a5201a4f03a4e01a4d01a3f01a3e01a3d0a96f0796b0a967079630a95f0795b0a957079530394f0294b02947039430193f0193b01937019330192f0192d0192b0192acb12801927019260a925ca124019230186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b01829018270182501823018210181f0181b018170181304c5d03b5102b4f02b4703b4309a6103a5102a4703a3f0995d0494f0494b04947049430393f0293b02937039330992f0992b09927099230585d0484f0484b04847048430383f0283b02837038330582f0582b05827058230581f0581b058170581304d6d04d6102c6d03c6102c5f04c5e02c5d02c5702c5503c5303c5203b6d0db6c03b6103b6002b5702b5602b5503b4f03b4e03b4d0ca6d01a6104a5f04a5b04a5704a5303a4f02a4b02a4703a4303a3f03a3d03a3b01a3903a370ca3503a3301a3103936c81340586d018610485f0485b04857048530384f0284b02847038430383f0383d0383b01839038370583503833018310582f0582b058270582309c6d04c5d04b5d01b4f03a5107a4f09a4b07a4709a4304a3f04a3b04a3704a330995d0694f0493f0193b019330a92f0192b07927019230585d0584f0184b05847018430483f0183b04837018330582f0182b05827018230181f0181b018170181304d6d04d6c04d610dd6004c6d04c6101c5f01c5e01c5d02b6d03b6104b5f02b5d04b5b03b5904b5702b5504b5303b5104b4f04b4b04b4704b430aa6d01a6104a5f04a5e06a5d04a4f04a4e01a4b01a4901a4304a4201a410aa3f01a3b07a3701a330495ec615c0586d018610485f0585d0185b01859048570485501853018510484f0584d0184b0484704845018430583f0183b05837018330182f0582d0182b01827058250182304d6d06d6102c6d03c6102c5f03c5b02c5703c5303b6d0db6c03b6103b6003b5f06b5e03b5b03b5a03b5704b5603b5303b5201b4f01b4e01b4d0aa6d01a6106a5f01a5b0aa5701a5301a4b02a4a01a4902a4702a4601a4301a4102a3702a3602a350886d018610685f0185b08857018530384f0184b02847018430383f0383d0183b01839038370883501833018310182f0182b018270182304c5d06c5102b5d03b5106b4fc734b07b4706b430da5d01a5106a4f0aa4bc524706a43c423f07a3b07a370aa330d85d018510684f0b84b57047068434603f0783b078370b8330a82f0b82b230270a82306c5f06c5b06c5706c5306b5f06b5b06b5706b5307b4f07b4b07b4707b430695e049560394e029460193e0a9360685f0685b06857068530784f0784b07847078430a83f0a83b0a8370a8330b825018190b81502c5f02c5d03b5303b5102b4f02b4703b430ca5f0ca5d0aa5b01a590ca570ca550aa5301a5104a4f04a4b04a4704a4303a3f02a3b02a3703a330585f0585d0585b01859058570585505853018510484f0484b04847048430383f0283b02837038330582f0582b05827058230581504d7d04d7c04d7106d7002c7d03c7102c5f04c5e02c5d02c5702c5503c5303c5203b7dc137c03b7103b7002b5702b5602b5503b4f03b4e03b4d0ca7d01a7104a5f04a5b04a5704a5303a4f02a4b02a4703a4303a3f03a3d03a3b01a3903a370ca3503a3301a310587d018710485f0485b04857048530384f0284b02847038430383f0383d0383b01839038370583503833018310582f0582b0582705823058150cc5f04c5d06c5b06c590cc5704c5506c5306c5107b5f02b5d10b5b03b5907b5702b550eb5303b5106b4f0cb4b07b4706b4306a4f01a4b0aa4701a430aa3fbb23e01a3b07a3701a330aa320b85f0b85d0185b018590b8570b85501853018510684f0184b0b847018430b83f0183b07837018330182f0182b0182701823 20 1048575 8 255 11 2047 20 1048575
def cc_57_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x97e3f939458e8518697f806637b74f7368170b2b6c84369c2c65b4160a515b654583334f78c4a45343f653f24d372803462c301452d62b28f4723c531bf7d1833c1374c114230f1230a54c0654000065 0x4d7d026b880b1f4058c202c5f0162d80b15c058a601b7d00db8806d7c096bc01b5d00dab806d54036a601b5200da7806d2c0368e01b4300d3ebfc9f0034e201a7000d2b812958034aa01a4f0152700692c0349401a470152300690c0348401a3f00d1f0068f4030fa0187100c2f80616c030ae0185300c2780612c0308e0184300c1f8060f4030760183700c1a8060cc0305e0182d00c158060a40304e0182500c1180608409ade04d630163780718c058be03c5b0162b80f14c056de01b63025af812d78076b604b57025a9812d480369601b4700da18069bc134dc01a6300d3100695c094ac01a5500d2780e9380349601a4700d218069080347e11a3e00d1e81257c092ae0394f014a382a4fc1526e0192f00c9680649c1324a0186f00c3180617c030b60185700c2980613c030960184700c218060fc0307a0183b00c1b8060d4030660182f00c168060ac0304e0182500c1180606c0302e04d6f026b180b1bc038c602c5f01e2d80b15c078a602b6f015b7006d8c036c403b5f01daf00ed6c076b404b57025ab00ed4c076a401b4b00da5006d1c0368c01b4300d3780698c034be01a5d00d2d80695c034aa01a5300d2780692c0348e01a4300d1f8068f40347601a3900d1b8068d40346601a31024af81255c0729e029470549f8264f41526e0993500c9780649c030de0186300c2f80616c030ae0185300c2780612c0308e0184300c1f8060f4030760183900c1b8060d4030660183100c178060b4030560182700c1280608c03036018170273f8139cc05afe02d7d016ba80b5bc07ad602d6701eb180b1fc058fc02c7d01e378131b8078d603c6a01e33813198078c603c6200dbf806dcc036de04b6e00db6806d9c036ca01b6300db1006d7c036b601b5700da9806d3c0369a01b4b00da5006d240369001b4701da3006d15fa68801b4300da08069fc134fc01a7300d3900699c094cc01a6500d2f80e978034b601a5a00d2b80a958034a601a5200d2780e9380349a03a4c00d258069280349201a4800d2380e9180348afc24400d218069080348201a4000d1f8068f80347a0496f024b380e57c052ae0394f01ca680e51c1528a0193f00c9b8064bc0325a0192704c928061fc030e60186f00c3580619c030c60185f00c2d80615c030a60184f00c2680612c030920184700c2280610c030820183f00c1e8060ec0306e0183500c198060bc0305a0182b00c1480609c0304a0182300c1080606c0302e04d6f026b581359c09ac70246f80235bf919df68c604c5f0262d81315c098a601b6f00db5806d9c036c601b5f025af006d74036ae01b5500da9806d480369e01b4b00da3806d0c034de0da6e00d3580699c034c601a6200d2b812958034aa01a4f01d2700692c0349401a470152300690c0348401a3f00d1f0068f4152de0696b054b381a58c092be0495b024ab81254c1529e0694b054a381a50c0327e0193b00c9b8064cc0325e0192d00c9580649c1524a0192300c378061ac030ce0186300c2f80616c030ae0185300c2780612c0308e0184300c1f8060f4030760183700c1a8060cc0305e0182d00c158060a40304e0182500c118060840303e0181b00c0b80604c09ade04d630263780f1b8078c603c620162f80b178038b601c5a0162b807158058a602c52015b780ada4056c602b61015af80ad6c056ae02b53015a580ad240568e02b43015a08329bc034c604a5f00d2d80a95c034a606a4f0352680692c0349202a470152280690c0348202a3f00d1d80a8dc034660495f024ab81e53c0f29a0794703ca280a4fc0526e0192f03c938161bc030c60485f00c2d81215c030a60584f02c2680612c030920584702c2280610c030820283f00c1d80a0dc030660182f00c1580609c030460181b02c0b80b9fc07cfc02e7d026bf8135f809ae609d72016b780b5b805ada02d6c016b580b5a809ad2f9568016b380b59809aca04d64016b180b58805ac202d600263f8131cc058de02c6d016358131a4058ce04c650163180b184038be01c5e00e2e80ade4056e602b71015af80ad78056ba02b5c015ad80ad64056ae02b55015a9812d48056a203b50015a780ad2c0568e02b430653f8069cc054de02a6d00d358069a4054ce0ca6500d31806984094be04a5e0352e81293c0949c01a4b00d2480690c0948401a410151f8068ec0546e01a33014b780a5b4052ce07965024af81e574092ae04955024a781251c0527e0293700c9781e49c0b0fe018730143780a1b4030d60186901433816194030c6018610242f816174030b6018590242b812154030a6018510242781613403096048470242280610c0507e0183b0141b8060cc0305e0582d00c1580609c0b04a0182300c0d81605c038b601c5a015af80ed6c056ae03b53015a780ad340769603b49015a380ad140768603b410252f80696c034a606a4f0352680e8fc0347602a3700d1981217c030b60485700c2981613c0b09a0184b00c2481611c0b08a0184300c2080e0fc030760283700c198060bc030560182700c118139c41bce001d6f00eb70075b4058fa02c6f0163680f1ac078d202c670163280f18c078c202c5f01e2d80b15c078a604b6e7b9b6012d98096c804b5e025ab00ed38094de04a6e0353681297c094bc01a5b00d2c80694c094a401a5101d2780692c0548e01a4300d1c8328d4090de0586d00c358061a4090ce0486500c31806184090be0585d00c2d81215c090aa0185301c2780612c0508e0184300c1c8160d40305e0582d00c1580609c0b04a0182300e2d807168056c202b5f015ad80ad5c056a602b4f015a680ad2c0569202b47015a280ad0c0568204a5f00d2d80694c0d49e06a4d0151f8068ec0546e01a330242f80616c090ae0185302c27816134030960184902c2381611403086018410141f8060ec0506e0183300c178060ac0304e01823026be8135f009ae2f55700263e8131c4038be01c5e00e2e80adf4056c202b5f015ae80ad6c056b202b57015aa80ad4c056a202b4f015a580ad1c056860ca7d00d3881297c094bc06a5d025278129380349601a4900d218129080348202a3f00d1d80a8dc034660587d00c3881217c0b0ba0185b00c2c81215c090aa0185300c2881213c0b09a0184b02423812114030860283f00c1d80a0dc030660182f02c168060ac0304e0582500c118135bc09ac604c6f0163700b18c058c403c5f01e2f00716c038b403c5700e2b00f14c078a402b6f01db180ad7c076b602b5701da980ad3c0569a03b4b015a380ad14194de01a630252f80696c074ae01a530352781a9340349601a4901d2380e9140348601a4101d1f8068ec0546e01a33024af81255c2129e0994d084a38265140727e0293700c9782a49c0b0de018630242f816174030b6048570242a80614c0b09e0584d00c258061240b08e0584500c218061040707e0183b0141b8060cc0305e0582d00c1580609c0b04a0182300c0d81605c09ade04d6e026b481358c13ac404d610263781318c038be01c5e00e2e80adbc076c602b5f025af00ed6c076b202b5701da980ed48076a203b50015a780ed2c0568e03b430153783298c094be04a5e01d2d80e964074ae03a5301d2900e944074a004a4f0252701292c0949203a47025218129081d48201a3b0151b80e8cc092be0995d024ab8125540929e0494701c9f80a4dc1d25e0e92702c3780618c090be0585d00c2d81215c090aa018530242781613403096048470242280610c0707e0183b0141b8060cc0b05e0582d00c1581609c0b04a0182300c0d81605c03adc01d6d0163680f1a4058ca03c61025b7026db4136d804b6a025b4812da0096cc04b65025b2012d88276c213b60025af012d68096ac04b520253701a9b4094bc01a59025290069441547a01a390551a8068c4092cc04964024ab00e5380727c0a92602c368061a4090ca0186102c2e8121540b07a0183902c1a8060c40b05a0582502c0a8139fc09cfc04e79027398279c809ce20de70026bf8135cc03ade01d6e00eb680b1fc058fa02c75016378131b8058da02c6c01e3580f1a4058ce02c6501e3180f188078c203c600162f80f16c058ae03c53015bf80adf8056fa03b6f025b700edb5e66d803b6b01db500eda4076d003b67025b300ed94096c803b6301db100ed84076c003b5f025af00ed740d6b803b5b01dad00ed5c096ac03b55025aa00ed4c076a40ca7f00d398129bc094dc06a6d0252f812978034b601a5900d29812948034a203a4f00d2580a91c0348603a3f01d1e8068ec0747401a3900d1c00e8dc0746c0ca357911a0068cc034620496f04cb681259c092ca0495f024ab80e53c0528e0393f01c9e80e4dde226a0192f054938161fc030e60486f02c368061ac030d2048670243280618c030c20485f02c2e80616c090ae0485500c2980e13c030960284700c2180e0fc0707a0183b00c1c80e0dc0b06a0183300c188060bc0b05a0182b00c13816094030460181b02c0b8275bc1badc09d6306eb10131bc098c601c5f00e2e81315c038aa04c5303db7826d8c0f6be02b5d0b5ad80ed640f6ae02b5504da980ed440969e04b4b025a3812d0c134de01a630352f81a9740d4ae06a5500d2981293c0349604a4700d2182a8fc0347607a3700d19b185b80d2c404957024ab0125540929e0494a024a38125180d27e9d13e0349b81a4c80325e0692a0349382a4980b0de0186302c2f816174030b60185902c2b816154030a6018510242780612c0908e0184302c1f8060ec0b06e0183300c178060ac0304e0182302c0e80606c0b02e05815026b78135b809ad604d67026b1837588098de04c6b0263381318c038be01c5e00e2ebe0dbdec6d6f4367781b1812d7c056ba04b5b01dac812d5c056aa04b5301da8812d3c0969604b47025a18329bc034d60ca6700d3181297c094bc06a5d025278129380349601a4900d21812908034820ca3f00d1d8328dc03466c516f034b5af459c0d2c60495f778ae81256c092ae04955024a981253c0929604947024a1a704fc0d27692137034998064bc0d2560a92700c918161bc030d60586700c3181217c0b0ba0185b00c2c81215c090aa0185300c2881213c0b09a0184b02423812114030860583f00c1d8160dc030660182f02c168060ac0304e0582500c1181607c030360581700c0980f5bc07adc01d6300eb10131bc0d8c602c5f0162e81b16c0d8b202c570162a80b14c058a201b6f015b1806d7c036b601b5900da9806d440569e02b4b015a380ad0c034de01a6300d2f806974034b601a5900d2b806954034a601a5100d2780692c0348e01a4300d1f8068ec0346e01a33034af81a5740d2ae06955034a781251c0527e0293700c9780649c030de0186300c2f806174030b60185900c2b806154030a60185100c2780612c0308e0184300c1f8060ec0306e0183300c178060ac0304e0182300c0d80605c05cfe03e7e0173e8135fc0dae602d6f016b680b5ac0dad202d67026b280b58c05ac202c790163980b1c4058be02c5b0162b80b14c036fe01b7300db7806db4036d601b6900db3806d94036c601b6100daf806d74036b601b5a00dab812d58036aa01b4f00da5806d1c0368601a7f04d3f0069f41b4f801a7500d398069c8034de02a6e00d3680a9b0034d601a6a00d348069a0034ce02a6600d32bb4990034c601a6200d30806980034be06a5e00d2e80693c0549c01a4b00d2500691c0548c01a4300d210068fc0347c01a3d014b780a5b4052ce06965034af81255c0529e0294700c9f8064dc0325e0192d00c9381a494030fe0187300c378061b4030d60186900c33806194030c60186100c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e0183300c178060b4030560182a00c148220a00304e0182600c12b90090030460182100c0d80605c058da02c5f01e2d80b15c078a606b5f035af00ed3c0769c01b4b00da5006d1c0368c01b4300da100697c034b601a5700d2780692c0348e01a4300d1d8068e4030be0185b00c2b80614c0309e0184b00c2380610c0307e0183d00c1d8060e40306e0183500c198060c40305e0182b00c1380608c05afa02d6f01eb580b59c07ac606c6e0263300f178036de01b6d00db5806da8036ce04b6600db2806d7c036b601b5700da9806d240368a01a6f035370069b4034be03a5e00d2e80e970034b601a5a00d2b80a958034aa02a5400d298069480349201a4800d22bac9100347e01a3e00d1e8061bc030d60186700c3180617c030b60185700c298061240308a0183f00c1d8060dc030660182f00c168060ac03054018290441400609c0304c018257181200608c0304206c630363080adbc056da01b6b00db4806d9c036ca01b6300db080ad3c0569602b47015a180698c034c201a4f00d2580691c0347e01a3b00d1b8068cc030de0186d00c358061a4030ce0186500c318061840309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182b00c1380608c09afa06d710163e80b184058be02c5b0162b80b14c036fa01b7100daf806d74036b601b5a00dab812d58036aa01b4f00da5806d1c0368601a7d7493e0069c4034e001a6d06d3600697c0d4bc01a5d00d2780a9380349a03a4c00d258069280348e02a4600d2280a9100348601a4200d1f8068f80347a0187d00c3880617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc0305a0182b00c150060a4110500182700c13006095c40480182300c108135bc0dac602c6f0163680b194038c602c5f01e2d80b15c078a602b6f015b7006d8c036c406b5f035af00ed6c076b403b5701dab00ed4c076a401b4b00da5006d1c0368c01b4300d3780698c034be01a5d00d2d806968034ae04a5600d2a80694c0349e01a4b00d2380690c0347e01a3d00d1d8068e40346e01a3500d198068c40d2be0495701ca780a51c0d27e0693d0349b81a4d40325e0192700c3780618c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183d00c1d8060e40306e0183500c198060c40305e0182b00c1380608c03036018170273f81b9cc05afe02d7d016ba80b5bc07ad602d6701eb180b1fc058fc02c7d01e3781b1b8078d603c6a01e33813198078c603c6200dbf806dcc036de01b6d00db5806da8036ce04b6600db2806d7c036b601b5700da9806d3c0369a01b4b00da4806d1c0368a01b4300da08069fc134fc01a7300d390069bc0d4dc01a6d00d2f80e978034b601a5a00d2b80a958034a601a5200d2780e9380349a03a4c00d258069280349201a4800d2380e9180348ae724400d218069080348201a4000d1f8068f80347a0696f024b380e57c052ae0394f01ca680e51c0d28a0193f00c9b8064bc0325a01927034928061fc030e60186f00c3580619c030c60185f00c2d80615c030a60184f00c2680612c030920184700c2280610c030820183f00c1d8060dc030660182f00c168060ac03054018290441400609c0304c018257081200608c030420181b00c0b81317c0b8b604c5702e29822d7c116b608b57045a9816d3c0969604b4702da180697c034b601a5700d2980693c0349601a4700d218068fc0347601a3700d1981a57c0d2b606957034a981653c092960494702ca181a4fc0d27606937034998064bc032560192700c9180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc030560182700c1180607c030360181700c0980b5bc07adc02d6d0263781b18c058be02c5d0162d81b164058ae04c550162980b144056d202b63015b080ad3c0569602b47015a18069bc034c601a5f00d2e80696c034b201a5700d2a80694c034a201a4f00d2680692c0349401a47025230069140348601a3f00d1d8068dc034660196f00cb180657c032ba0195b00cac80655c032aa0195300ca880653c032960194700ca18064fc032760193700c998064bc032560192700c9180a17c050ba028570342a81a13c0908e0283f0141b8060bc0304e0181f00c0b80b1b4058be03c5b0162b80f14c0d6bc04b5601da700697c034ba01a5b00d2d00695c094ac01a5500d2780692c0348e01a4300d1c8068d4032be0195b00cab80654c0329e0194b00ca380650c032720193500c978064ac0324e019230263681b184056da02b51015a780ad2c0568e02b4300d368069840349e01a4d00d258069280348e04a4600d228068fc0347601a3700d198065b4032c20194f00ca580651c032860193f00c9d8064dc032660192f00c9580649c0324604d6f036b180b1bc058da02c650162f80f16c058ae03c53015b780adb8056da03b5f035af00ed6c076b403b57025ab00ed4c076a401a6f00d3180697c034ba01a5b00d2d00695c094ac01a5500d2980693c0349601a4700d218068fc0347a01a3b00d1c8068dc0346a01a3300d188065bc032c60195f00cad80655c032a60194f00ca580651c032860193f00c9e8064ec032720193700c9a8064cc032620192f00c9580649c032460685f0242b80e13c0508e0383f01c1e80e0dc0d06a0182f00c1380607c0302e04c5f0362d81315c0d8a6e435f719adb88d5dc26a606b4f025a5812d1c0d68601a5f00d2d80695c034a601a4f00d2680692c0349401a47025230069140348601a3f00d1d8068dc034660195f00cad80655c032a60194f00ca580651c032860193f00c9d8064dc032660192f00c9580649c032460685f0342d81a15c0d0a60684f0242581211c0d0860683f0341d81a0dc0d0660182f00c1580609c030460181f00c0d80605c0302604d6f036b581359c0dac6ec46f75235ba119dcc8c606c5f0262d81315c0d8a601b6f00db5806d9c036c601b5f00dae806d6c036b401b57025ab006d540369e01b4b00da3806d0c034de0da6e00d3580699c034c601a6200d2f81a978034ba01a4f01d2700692c0349401a470152300690c0348401a3f00d1f0068f40d2de0696b034b381a58c0d2be0495b024ab81a54c0d29e0694b034a381a50c0327e0193b00c9b8064cc0325e0192d00c9580649c0d24a0192300c378061ac030ce0186300c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e0183300c178060b4030560182a00c14b940a00304e0182600c12b80090030460182100c0f80606c0302e01813 20 1048575 8 255 11 2047 21 2097151
def cc_57_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x8cdc30d985fff6bcf617519ae36d9a8bcb2acd5d9f8b5ab15e99aa6ad4ff9c96f2125d02362b42d7e804acf94e9d0453804067120af7d93f3f23f7e381fc57718884d095f60d4ac0adf8002b 0x9ade04d6b026b381358c058de03c6b0163380f18c058be04c5e0162e80b15c058aa03c5301e2900edbc1b6dc03b6b01db380ed8c076c402b57015ab00ad540769e03b4e01da68329bc194d60ca670653181297c094b604a570252980e93c0549602a4701d2180e8fc0747a03a3b00d1c80e8dc1946a03a3300d18b1c5bc0d2d6c0167034b181257c092b604957024a980e53c052960294701ca180e4fc0727a0393b01c9bc7c4d4072660c92f0349583249c0d2460586f02c3581619c0b0c60485f0242d81215c090a60384f0142580a11c070860383f01c1e80e0ec030720383702c1a80e0cc030620582f02c1581609c0b0460581f02c0d81605c0b02602d6f016b700b5ac05ace02d6306eb10131bc098d604c670263180b17c058bc03c5d015b780adac056ce02b63015af80ad78056ba02b4f015a700ad2c0569202b43025a100ad04194de0ca6b0653383298c054be0ca5d0152d806964054ae02a55015298069440949e04a4b0252381290c0547e02a3b0151b80a8cc0f2de0696b03cb381a58c052be0795d014ad80a55c052aa02953024a781252c0928e049430149f80a4ec0526e0293303c9781a4ac0f24e0692302c378161ac0b0ce058630142f816174050b6018590142b80a154050a6018510242781212c0908e048430141f80a0ec0506e0283302c178160ac0b04e0582302c0f81606c0b02e05813026b781b5ac09ace06d630163780f1ac058ce03c630162f80f16c058ae03c53075b7836db8356d60eb670d5b1836d88056be02b5e00dad806d68096ae01b56035a980ad480769e03b4e00da5806d280568e01b4601da180ed08194de01a6b0653503299e184cc01a630352f81a978034b604a5700d2981a9480749e03a4e00d2580a91c0348603a4201d1f80e8f80747a0696f034b581a59c0d2c60695f024ad81255c0d2a60394f014a580a51c072860693f0349e81a4ec0d26e06935034998064bc0d25a0692b0349381a494032460886f00c3582219c030c60585f00c2d81215c030a60384f00c2580a11c030860883f0441e8060ec03072088370441a8060cc030620182f044168060ac0304e0882500c1181a07c030360681700c098135bc0dad604d67036b180b1bc078d602c6701e3180b17c058ba03c5b01e2d00b15c098ac02c5501db7836db8076d603b6701db180ed88056be02b5e015ae80ed3c0769c03b4d8b1378329ae164ce0ca630352f81296c094ae06a5301d2780a92c0548e03a4301d1f80e8f40747601a3901d1bc708d40746601a31034b781a5ac0d2ce06963034af81256c092ae0695301ca780a52c0528e0394301c9f80e4f407276039370349a80e4cc0d25e0692b0349381a48c110de0586b0443381618c0b0be0485b0242b81614c0709e0284b0142380e10c0707e0383d01c1d8060e40706e0883501c198060c41105e0582b0441381608c0d03e0581b0340b81604c03ad601d69016b1807584098de04c6d01e3580f1a4098ce04c650363180f184098be06c53015b780adb4056d602b69015b380ad94056c602b61015af80ad4c0569e02b4b015a380ad0c054de01a6b00d3480698c034c202a5f00d2981a93c0349604a4700d2180a8fc0347602a3700d1981a5bc0d2da06967034b281a53c0928e0293f0149b8064bc0d24e1186f07c368061ac030d21186707c3280618c030c20b85f00c2981613c030960484700c2180a0fc030760283700c198060bc030560182700c1180606c0d02e01e7e00f3e8135b40bad204d6502eb08271f8138e409c6e06e368271b01b8d40fc690be340371981f8ca0fc6404e31037184138c003c5e00e2d007158038a402b6d015b480ad94056c201b4d00da480ad140368201a7900d388069340349201a4500d2081a5b40d2ca0694d034a28061b4030d20186500c30816178030a40284e00c268060e80506c0182a00c130079fc03cfc01e7d026bf81b5cc09ade04d6d036b581b5a409ace04d65036b181b584058fe09c7e0163980b1c8058de09c6e016368371b0058d602c6a0163480b1a0058ce0dc6601632c69190058c602c620163080b180058be03c5e0162e80adfc056e602b6f015b680adac056d202b67015b280ad8c056c202b5b025ad00ad64056ae02b56015a980ad440568e02b46015a28069e4034e601a710352f80696c094ae01a530152780a9340349601a49015238329140348601a410151f8068ec0546e01a33034b781a5b40d2ce06965034af81255c0529e0294d014a381a5140527e0293700c9781a49c170fe0187306c378361b4030d60186906c33856194030c60186102c2f80616c090ae018530142780a134030960184901423c6411403086018410141f8060ec0506e0183300c178060ac0304e0182300c0d81a05c03ad601d6901eb1807584098de04c6d0163580b1a4098ce04c650363180b184098be06c53015b780adb4076d603b69015b380ad94076c603b61015af80ed4c0569e03b4b015a380ed0c074de01a6b00d3480698c034c203a5f00d2981a93c0349604a4700d2180e8fc0347602a3700d1981a5bc0d2da06967034b281a53c0928e0393f0149b8064bc0d24e0886f044368061ac030d2088670443280618c030c20885f00c2981613c030960484700c2180e0fc030760283700c198060bc030560182700c1180606c0d02e01e7f00f3f0079f409afe06d73026b78135b40dad606d69026b38135940dac606d610163f80f1cc058de02c6d01e3580f1a4058ce02c6501e3180f184058be02c5d01e2d80f168058ae04c560162a80edfc136fc03b7d06dbe00edd4076e603b7201db7826db8076da0db6c01db580eda8076d203b6801db3836d98076cb1736401db180ed88076c203b60015af80ad78056ba03b4f01da700ed34034f201a7300d3881a97c034b604a5700d2980e93c0349602a4700d2180e8fc0747a01a3b00d1c80e8dc1946a01a3300d1881a5bc0d2da06967034b281a57c092ae0394f014a380e4fc0727a039370349a8064bc0d24e0887f00c398221bc110da0186b00c3482219c110ca0186300c3081617c030b60485700c2980e13c030960284700c2180e0fc0707a0183b00c1c80e0dc1106a0183300c188060bc030560182700c1180606c0d02e05c5f0262e81b16c0d8b205c570262a81b14c0d8a207b5f015ae822d6c076b207b57015aa822d4c076a206b4f02da5816d1c0d68601a5700d2a80693c0349601a4700d218068fc0347601a3700d1980615c130ac0185500c2780612c0308e0184300c1f8060ec0306e0183300c178060ac030460cc5f0262e81b16c0d8b209c570262a81b14c0d8a207b5f015ae826d6c076b207b57015aa85ad4c076a206b4f065a581ed1c0d68606a4f00d2582a91c034860aa3f00d1d81e8dc034660d95e0549306617e2a0ba0185b00c2c82615c280aa0185300c2881a13c030960c84700c2185a0fc030760783700c198060bc030560182700c1184c0540b8be04c5d0362d81b1640b8ae04c550362981b1440f6be02b5d045ad80ed640f6ae02b55045a980ed440d69e05b4b02da381ad0c034a601a5100d2780692c0348e01a4300d1f8068ec0346e01a3304cab00617c030ba0184f00c2580611c030860183f00c1d8060dc030660182b00c1380608c0302a01d6f00eb700758c03ac405c6f05e3181717c098ba0fc5b0362c81715c098aa10c530362882edbc116c610b5f015ae822d6c076b20fb57015aa822d4c076a215b4f02da5816d1c1168601a6f00d3180697c034b601a5900d298069440349e01a4b00d2380690c0347e01a3b00d1b8068cc212bf1315d07cab8505542b29e059470449fa544dc0325e0192700c3782e1b8030c60186200c2f836178030ba0184f00c2580611c030860183f00c1d8060dc030660182f00c158060a80304e0182600c1180606c03034018170900b0075bc03adc01d6d0663783718c198be04c5d06e2d81b164198ae04c5506e2981b1441b6de0db6306daf80ad741b6b603b5906dab80ad541b6a603b518c1a7832d2c1968f1634300d3480698c034c20ca4f00d2583291c03486da23f00d1db3c8dc034660d95f06cae83655e282aab114f064a3a784fd2826e0192f0549382e1bc030c60d85f06c2e80616c030b20d8578902a80614c030a25f04f00c2583211c030864b03f00c1d8e40dc030660182f00c1580609c030460181b0880b83317c198b60cc5706629806db4036be01b5b00dab806d4c0369e01b4b00da3806d0c0d4bc04a5601d2700a9180347c0185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660182900c1280f14c078a202b5f015ae80ad2c0568e02b430652f826974034b601a590152b80a954034a601a510352780692c0948e01a430151f8068ec0546e01a3305c2f82e174030b60185905c2b82e154030a60185102c2780612c0908e018430141f8060ec0506e0183300c178060ac0304e01823026be81b5c4058fb0f47c0163880b1c0058be03c5e0162e80adf4056f802b7101db800ad6c096b402b59015ab80ad58056a602b51015a380ad180568a0ca7d00d3081a97c034b604a5700d2980a93c0549a01a4b00d2480a91c1948a01a4300d2080a8fc0347602a3700d1982e1f4030e20585f00c2d81215c030a60284f0142680612c030920284705c2280610c030820283f00c1d80a0dc030660182f00c1580609c0304602c530162880ed4c076a202b4f01da580ad1c194be09a5d00d2d806964074ae03a5500d298069440d49e01a4b0252380690c0747e01a3b0151b8068cc110be0885d00c2d806164110ae0885500c298061440b09e0184b0242380610c0707e0183b0141b8060cc0305e0182b00c1380608c0d8c203b61015a780ed2c0568e03a6101d3003a9440549e01a4b0252381a90c0747e01a3b0151b80e8cc110da0584f00c2581211c030860383f00c1d80a0dc030660882f00c1582209c0304604d7d036b880b1f4058f803c7101e3800b17c058ba03c5b01e2d00b15c098ac02c5501dbec34df0076e203b7001db6836db0056be02b5e015ae80ed3c0769c03b4d0653e8069840d4be01a5b0252b80694c0749e01a4b0152380690c0747e03a3d00d1d80e8e80347201a3801d1b80e8d81946b0c23400d198068c4110fa0187102c2f80616c090ae0185301c2780612c0508e0184301c1f80e0f4030760183901c1b8220d4030660183100c178060ac0304e018230263681b184056da03b61871a7832d2c1968f0b34306d368069441949e01a4b0652380690db247e01a3b6711b8068cc170da0186105c2780612c1708e0184305c1f8060ec1706e0183300c178060ac0304e01823066b783358c1b8de0dc630662f83316c198ae0cc5300db7806db4036ca01b5f00dad806d5c036a601b4f00da5806d1c0368601a6f06d370069b4034be06a5e00d2d806968034ae04a5600d298069480349e03a4e00d258069280348e02a4600d21806908152be0a957054a782a51c0327e0193700c978064b40324e0a92500c3780618c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c158060a40304e0182500c1180608403036018170173f80f9f805cfa04d7f036b980b5bc05ada02d6b036b480b59c09aca02d63016b081b1fc138fc06c730363900b1bc058dc02c6d0163600b1ac058d406c690363400b19c058cc06c650663200b18c058c402c610163000717c038bc01c5d015bc80adcc056e202b5f015ad80ad5c056a602b4f015a680ad2c0569202b47015a280ad0c056820ca7f00d3980a9bc054da01a6b00d3480a99c194ca01a6300d3080696c094b401a590252b812958034a601a51025238129180948a02a3f00d1d80a8dc034660296f014b680a59c0d2ca0695f024ab81a53c0d29a06947034a280a4fc0526e0192f0349382e1fc030e60286f014368061ac030d2028670ac3280618c030c20585f0342e80616c090ae0c85500c2981a13c0d09a0184b00c2481a11c1908a0184300c2080a0fc030760283700c198060bc030560182700c1180606c0d02e01d6f00eb70075b4058fa02c6f01e3580b19c078c602c5f0162e80f16c078b202c570162a80f14c078a206b6e025b301ad780d6b806b56065aa00ed38034d604a6a00d3481299c094cc01a6300d3081295c094ac04a5501d2780692c0548e01a4300d1c8328d40b0de0686d00c3581219c110ca018630342f81a174030b6018590342b822154030a60185101c2780612c0508e0184300c1c8220d40305e0182b00c1380608c09afa06d710363e8331f00d8e206c7000e2f807178038ba02b7d015b080ad7c056b602b57015a980ad3c0569a02b4b015a480ad1c0568a02b43015a08329f4034e201a5b0252d006964094ae04a5600d298069440948e04a460252280a8fc0347602a3700d1982e1f4030e20585f0342e80616c090ae0b85500c2981a13c0d09a0184b00c2481a11c1708a0184300c2080a0fc030760283700c198060bc030560182700c118139fc0dce606d7f04ebf01b5cc0dae401d6f00eb70075b4058fe02c7d0163a80b1bc078d602c6701e3180b17c058ba03c5b01e2c80b15c058aa03c5301e2880adfc056fc02b7d01db781adb8076da06b6c01db580eda8076ce04b6601db2812d90076c603b6201daf81ad78076ba06b5c01dad80ed68076b203b5801dab81ad58076aa0cb5401da980ed48076a203b500653f8069cc034d604a6a00d3481299c094cc01a6300d3081295c094ac04a5501d2780692c0548e01a4301d1f80e8f40347601a3901d1b8328d40346601a31034b781259c0d2be0695d034ab81a5540729e0294701c9f80e4f40726e0693500c9781a49c110fe0187302c3781a1b4030d6048670443280618c0d0be0685d00c2d8061640d0ae0885500c298061440709e0184b0142380610c0707e0383d00c1d8060e40706e0883500c198060c40305e0182b00c1380608c0303606817026b781b5ac09ace06d63036378331b80d8d606c670363181b188038be01c5e00e2ec20dbe0e6d706367829b181ad7c096b604b57035a981ad3c0569a06b4b01da481ad1c0568a06b4301da08329bc034d60ca6700d3180696c094b401a590252b812958034a601a51025238129180948a0ca3f00d1d8328dc034660696f034b581a59c0d2c60695f024ad81255c0d2a60694f034a681a52c0d28e06945034a181a4fc0d27606937034998064bc0d2560692700c919dc1bc030d66806700c3181617c0d0ba0185b0242b832154030a60684f0342680612c03092068470642280610c030824a03f00c1d8e00dc030660182f00c1580609c030460681f00c0d81a05c0302603d6f01eb700758c03ac404c6f0263180b17c058ba02c5b0162c81315c098aa02c5301628806dbc056c601b5f00dad806d64036a601b51015a780ad2c0568e02b4300d3780698c034be01a5d00d2d806964034ae01a5500d298069440349e01a4b00d2380690c0347e01a3b00d1b8068cc0f2be0795d03cab81e5540929e049470149f80a4dc0325e0192700c3780618c030be0185d00c2d806164030ae0185500c298061440309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182b00c1380608c03036018170173f80f9f805cfa04d7f026b980b5bc05ada02d6b026b480b59c09aca02d63016b080b1e4058e602c710162f80b16c058ae02c5300dbf806dcc036de01b6d00db5806da4036ce01b6500db1806d84036be04b5e00dae806d5c036aa01b5300da9006d3c0369601b4700da18069fc134fc01a7300d390069bc054dc01a6d015360069ac034d401a6900d3400699c054cc01a658193200698c034c401a6100d3000695c094ac01a5500d2780a9380349601a4a00d2380a9180348601a4200d1f8068f80347a0296f014b680a59c0f2ca0495f024ab80a53c0528e0193f00c9b8064bc0325a0192703c928061fc030e60186f00c368061ac030d20186700c3280618c030c20185f00c2d80615c030a60184f00c2580611c030860183f00c1e8060ec0306e0183500c198060bc0305a0182b00c1480609c0304a0182300c1080606c0302e02c5f01e2d80b15c078a604b57025ab00ed3c0769c01b4b00da5006d1c0368c01b4300da100697c034ae01a5300d2780692c0348e01a4300d1d8068e4030be0185b00c2b80614c0309e0184b00c2380610c0307e0183d00c1d8060e40306e0183500c198060c40305e0182b00c1380608c05afa02d6f01eb580b59c07ac604c6e0263300f178036de04b6e00db6806d9c036ca01b6300db1006d7c036b601b5700da9806d240368a01a6702533006994034be03a5e00d2d806968034ae02a5600d298069480349201a4800d22c049100347e01a3e00d1e8061bc030d60186700c3180617c030b60185700c298061240308a0183f00c1e8060ec0306e0183500c198060bc0305a0182b00c1480609c0304a0182300c108131bc098da02b6f015b6806dac036d201b6700db2806d8c036c202b4f015a580ad1c0568601a6300d3080693c0348e01a4300d1f8068ec0346e01a3300c378061b4030d60186900c33806194030c60186100c2780612c0308e0184300c1f8060ec0306e0183300c178060ac0304e01823 19 524287 7 127 11 2047 21 2097151
def cc_57_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x1f7d9bcbc876368e8681c8d036b4d684a4c6f3579692cec85509aa09312de6a34ce421907dec8f3d01ceb237d4069eb8bf69168ac29c6a4a9207af48c16911dca169a414f080053 0xf6be02b5d04dad80ed640f6ae02b550b5a980ed440969e04b4b025a3812d0c194be0ca5d04d2d806964134ae0ca55055298069440949e04a4b0252381290c1947e07a3b03d1b82a8cc092bc0494602c2f8161740b0b60185902c2b8161540b0a6018510242781212c0908e0484302c1f8160ec0b06e0583302c178160ac0b04e0582302c0a8135bc0dadc04d6d0263481318c098c20db6f06db1812d7c056ba04b5b01dac812d5c056aa04b5301da8812d3c0969604b47025a18329bc194c604a5f0252e81296c034b204a570652a81294c034a204a4f0252581291c094860ca3f0651d8328dc194660495f024ae81255e782aa0494f024a3a7c4fd2e26e0c92f064938161bc0b0c60485f0242e81216c030b20485702c2a81214c030a20484f0242581211c090860583f02c1d8160dc0b0660582f02c1581609c0b0460581b02c0b81b17c0d8bc01c5b00e2d01315c038ac06c530362901ad7c096b604b57035a9842d3c0569a0eb4b01da483ad1c0568a10b4301da081a97c0d4bc01a5b0252b80694c0d4a40ca3f00d1d8328dc034660585f00c2d81215c030a60b84f05c2680612c030920b84705c2280610c030820b83f00c1d82e0dc030660182f05c168060ac0304e0b82500c118135b40d8bc06b5f025ad812d5c0d6a603b49015a281a97c094b604a57035298069267448add23f0651db508dc194660585f0242d81215c0b0a60184905c2282e0fc0b0760b83702c1982e0bc0b0560b82702c118131b4098a202b6d01db0812d3c0969604b47025a18329b4034c204a4f0252581291c094860ca3f0651d8328dc194660586d00c3081213c0909604847024218160fc0b0760583702c198160bc0b0560582702c118135bc03ac605c6f02e3700718c038c405c5f02e2f00716c038b401c5700e2b00714c038a40bb6f045b1816d7c096b604b5702da983ed3c0569a08b4b01da483ed1c0568a08b4301da08069bc034c601a5f00d2d80695c034a601a4f00d2680692c0349201a4700d2280690c0348201a3f00d1d8068dc034660595f024ab81a53c0d29a06947034a281a4fc0d26e0192f00c938061bc030c60185f00c2d80615c030a601847074230061140307e0183b00c1b8060cc0305e0182b00c1500609c0304c0182300c0d80605c09ade06d63026378131b8198c604c6200e2d807168098ae01c5603629836dbc1b6c606b5f025ad812d5c0d6a610b4f015a683ad2c076920eb47015a2842d0c076820ca6f06d3700698c194c406a5f0352f00696c094ae01a530352901a93c0d49c06a4d0651f8068ec194740ca376911b0068cc0d2be04957034a781a5340d28e069450349f81a4dc0325e0692d0349381a494170de0186302c2f80616c090ae0185308427cdc1340309601849074238b411403086018410841f8060ec2106e0183300c178320b403056018271601280608c0303606817026b780758c178de09c6e00e318071880b8be05c5e00e2d807168038ae01c5600e29807148176de08b6302daf812d6c096ae05b53075a780ad341169603b49075a380ad141168603b4100d3780698c034be01a5b00d2b80694c0348e0ea4600d228068fc0347601a3700d1981657c092ae0694f034a681a51c0d28a0693f0349b8064bc0324e0186f00c3180617c030b60185700c2980613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc0305a0182b00c13806094030460181b00c0b8135bc0bac604c6f0263701718c098c401c5b00e2d01315c038ac05c5305db7822d8c0b6be04b5b025ab816d4c2969e02b4d045a580ed241f68e02b45045a180ed04174de01a6302d2f80696c094ae01a5307d27cd49340349601a4907d238b49140348601a410451f8068eda246e01a3302caf81255c0d29e0694d034a381a5140d27e0693700c9781a49c0b0de0b86e00c318161880b0be0585e00c2d81215c030a60585202c2781a1380b09a0583f00c1d8160e80b06e3b03600c198060bc030560582a00c138ac098030460181b02c0d01605c0d02c04d6f026b6813594098de04c6e02636836dbc1b6c606b5f025ad812d5c0d6a606b4f015a681ad2c0769206b47015a281ad0c076820da6f0653181a97c094b604a570352981a93c0d49a06a4b00d2481a91e6c48a06a4300d20b6c8fc19476d02370651981a57c092ae0694f034a681a51c0d28a0693f0349b81a4bc0d24e0b86f02c3181617c090b60485702c2981a13c0d09a0584b00c2481a11e6808a0584300c209340fc0b0763a03702c198320bc0b0562a02702c1181606c0d02e08d6f046b700758c03ac405c6f05e3181717c098ba0fc5b0362c81715c098aa0fc5303628806dbc056c601b5f00dae806d6c036b202b57015aa806d4c036a202b4f015a580ad1c0568601a6f00d3180697c034ba01a5b00d2c80695c034aa01a5300d2880693c0349601a4700d218068fc0347601a3700d1981e57c0f2ba0795703caa81e53c0b28e0293f0149b8064bc0324e0186f00c3180615c1d0ac0185500c2780612c0308e0184300c1f8060ec0306e0183300c178060ac030540182700c1300608c030360181701eb780f5b81bac603d620663783718c198be04c5d0762d81b164198ae04c5508e2981b144056de02b63015af80ad6c036b201b5300da880ad3c0569602b47015a18369bc1b4dc01a6306d3100a97c054bc02a5d0652780692c1948e01a430151f8068ec0547402a370151b0068cc0f2be0795d03cab81e5540f29e079470149f80a4dc0325e0792705c3780618c210bf3205d00c2d8061641d0ae2905500c298061442309e0184b0642380610c0507e0183b0141b8060cc0305e0182b00c1380608c030360781705eb78275b803ac601d6202e3782f18c0b8be04c5d0762d81b1640b8ae04c550762981b144036de02b6300daf806d74036b601b59015ab80ad54036a601b51015a780ad2c0568e02b4300d3780698c034ae0ea5600d2a80693c0349601a4700d218068fc0347601a3700d1981e57c0f2ba0795703caa81e53c0b28e0293f0149b8064bc0324e0186f00c3180617c030ba0185b00c2c80615c030aa0185300c2880613c030960184700c218060fc030760183700c198060bc0305a0182b00c13806094030460181b00c0b80f5bc07adc08d6301eb10171bc178c605c5f0262e83f16c0d8b205c570262a85314c0d8a202b6f015b180ad7c056b601b5900da9806d440569e02b4b015a380ad0c174de01a6307d2fcc0974034b601a5907d2b8a4954034a601a510ad2780692c0b48e01a430151f8068ec0546e01a3303caf81e5740f2ae0795503ca781651c0527e0293700c9781e49c110de0b86e00c31822188050be0285e0142e81613c030960584700c2180a0fc030760283a0141b80a0d8030660182f00c1580609c030460181b03c0d01e05c0f02c02d6f01eb700b5b41b8de0dc630162f80b174058b606c590162b813154058a602c51015b480ad8c056c202b4f015a580ad1c056860da6f06d3180a97c054ba02a5b00d2c80a95e624aa02a5300d28c2093e04496f82477612180a8fc0547602a370151980a57c052ba0295703caa81e53c0f28e0293f0149b81e4bc0f24e0b86f0443180a17c050ba0285b00c2c80a15e5e0aa0285300c2898013c11096580470442180a0fc0507602837014198c40bc11056280270441181e06c0f02e02c5f01e2d80b15c078a60eb5f035af032d6c096b40cb57025ab046d4c0d6a403b4f01da7006d2c0369402b4700da300ed0c076840ca5f00d2d83295c034a603a4f01d2700692c0548e01a4301d2102217c030b60885700c2980e13c030960284700c218220fc1107a0183b00c1c8220dc1106a0183300c188060bc030560182700c1180b1b4058be03c5b0162b80f14c0d6bc04b5601da741c97e004b6f62577512980e93c0549602a4701d218068e65a46a0885f0442d82215c110a60384f0142580a11c07086018390441a8220bc1105608827044118331bc098da11c6b0363483319c098ca0ec630363080adbc056da01b6b00db480ad9c056ca02b6300db080ad3c0569602b47015a183293c034960ca4700d2180a8fc0347602a3a0151b80a8d8034660b86f05c368061ac030d20b86705c3280618c030c20b84f00c2582e11c030860283f00c1d80a0dc030660182f00c1580609c0304604c6d0363080adb4056a202b4f015a580ad1c056872b26d00d30c1893dfc496f42477412180a8fc0547602a370151982e1b4030c20b84f0442582e11c110860283f0141d80a0dc050660b82f0441582e09c1104602c5f01e2d80b15c078a606b5f035af026d6c096b409b57025ab01ad4c0d6a401b4b00da501a97c034b60aa5700d2980e93c0349601a4301d1f80e8f4132bc0993604c9301a17c030b60885700c2980e13c030960284700c218220fc1107a0183b00c1c8220dc1106a0183300c188060bc030560182700c118335bc1bac602c6f01e3180b17c078b602c5701e2980adbc056dc0db63015b103ad7c0d6bc0cb5b025ad032d5c096ac11b53035a9006d2c0369402b4700da300ed0c1b4de0da6e00d31836988194be01a5b7e92d03295de44ac01a5301d2780e9380349602a4700d2180e9080747e03a3e01d1e84657c192ae0394f014a386a4fe5227a0e9374109a8064bd1025a0a927408928221bc030c60885f00c2d82215c030a60384f00c2580a11c030860883f0441e8060ec03072088370441a8060cc030620182f044168060ac0304e0882500c1180606c1102e02c5f01e2d80b15c078a606b5f035af032d6c096b40cb57025ab01ad4c0d6a403b4f01da701a97c034b60aa5700d2980692c0548e01a4304d1b8268d81346a0685f00c2d82215c030a60384f00c2580a11c030860883f0441e8060ec03072088370441a8060cc030620182f00c1580609c0304602c5f01e2d80b15c078a606b5f035af04ed6c096b409b57025ab01ad4c0d6a406a5f0552dbc495c0d4a603a4f0152580a91c0748613a3f9391e8268ec0347209a374111a82a8cc03462a415601ca700e4f90024c0685f0442d82215c0d0a60384f0142580a11c070860883f0441e8220ec03072088370441a8220cc030620882f0441582209c110460881506eb783758c058de02c6d0163280b17c078b602c5701e2980adbc056dc02b6d01daf81ad78076b603b5a01dab812d58076a603b5206d3783698e0a4befb25b7812bb9894c0749e02a4b0152380e90c0747e03a3d01d1d8068e40746f2823501d198068c5662bea315701ca780a51c0727e0393d01c9bc984d50c25e7f1270443782218c110be0885b0442b82214c0709e0284b0142380e10c0707e0383d01c1d8060e40706e0883501c198060c41105e0882b0441382208c1103608817026b78175ac09ace05d6307e378271b8178d60bc6707e318271880b8be05c5e00e2d807168038ae01c5600e29807148056de02b6b015b380ad8c036be02b5b015ab80ad4c0369e01b4d00da5806d240568e02b4500da1806d04034de01a6b00d3380698c034be01a5b00d2b80694c0349e01a4d00d258069240348e01a4500d218069040347e01a3b00d1b8068cc0d2de0696b034b381a58c0b2be0495b024ab81654c0d29e0694d034a581a51c0d28a069430149f80a4ec0526e0293300c978064ac0324e0192300c378061ac030ce0186300c2f80616c030ae0185300c2383a1180308a0183f0141f0060ec0306e0183300c190060bc030560182a00c13806098030460181f00c0d8060680302e0681600c098135bc0dad604d67036b183b1bc1b8dc18c6b0763386318c1b8c403c5f01e2f00716c038b404c5700e2b01b14c078a402b6f015b580ad9c056c602b5f015ad80ad5c056a602b4f015a680ad2c0369202b47015a2806d0c036820ca6f00d3583299c034c606a5f0352f00696c094ae01a530352900a93c0549c02a4d0151f8068ec0547402a370151b0068cc0d2de0696b034b381a58c0d2be0495b024ab81a54c0d29e0694d034a581a51c0d28a069430149f80a4ec0526e0293300c9781a4ac0d24e019233c8378061acd80ce0186302c2f80616c090ae0185308427c9013403096018490742389c11403086018410141f8060ec0506e0183300c178320b403056018271301280608c0d03e0181b0340b80604c09ade05d6b026b381758c1d8de09c6e05e3582f19c1d8c609c6202e2f817178038b601c5a00e2b807158038a601c52015b780adac056ce02b6300daf80ad6c056ae02b5300da7806d340369601b49015a380ad140368601b4100d378069ac034ce01a6300d2f80696c034ae01a5300d2383a9180348a01a3f00d1d8068dc034660696f034b581a59c0d2c60595f024ad81255c0b2a60694f034a681a52c0d28e06945034a180a4fc0527602937014998064bc032560192700c918061bc030d60186700c3180617c030b60185700c2980613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc0305a0182b00c13806094030460181f00c0d80605c0302604d6f02eb581359c0bac60fc6f06e3702f1ac178ce1bc6306e3100f17c078bc01c5b00e2d01315c038ac05c5301e2900adbc056d602b67015b180ad7c056b602b57015a980ad3c0569a02b4b00da480ad1c0568a01b4300da0c649bc034d60ba6700d3181697c034b604a5700d2983e93e4449a01a4b00d2483e91c4e48a01a4300d2080a8fc0347602a3700d1981a5bc0d2d606967034b181657c092b60495702ca981a53c0d29a0694b034a381a5140d2860293f0149d80a4dc052660192f0349581a49c032460586f00c3581619c030c60585f02c2f00616c090ae0185302c2900a13c0509c0284d0141f8060ec05074028370141b0060cc0305e0182b02c1500609c4a04c0182302c0f80606c0b02e01813026b781b5ac09ace06d63016378371b8058d602c670163180b188058be03c5e0162e80adbc056d602b67015b180ad6c096b402b59015ab80ad58056a602b51015a380ad180568b1826f06535c3899c194c606a5f0252d81295c0d4a602a4f0152680a92c0349202a479192280a90c0348202a3f0151d80a8dc054660696f034b581a59c0d2c60695f024ad81255c0d2a60294f014a680a52c0528e06945014a180a4fc05276029370149981a4bc0d25606927034919e01bc0b0d66b06702c3181617c090b60485702c2980a13c0509a0284b00c2480a11e4208a0284300c2080a0fc0507602837014198320bc0b0562402702c1181a07c0b0360681702c098135bc09ac602c6f01e3180b17c078b602c5701e29826dbc1b6dc09b6306db1012d7c096b602b5a015ab80ad580769e03b4e015a380ed0c0768409a6f04d3181297c094b604a570252980e93c0549602a4701d218328fc1947a09a3b00d1c8268dc1946a0aa3300d18b205b80d2c40495f024ad01255c092ac0394f01ca700a51c072840393f01c9f00e4f40d25e0692a034938324980b0de058630242f81216c090ae0485301c2780a12c0508e0384302c1f8160f40b0760183902c1b8160d40b0660183102c178160ac0b04e0582302c0e81606c0b02e05815 19 524287 7 127 11 2047 21 2097151
def cur_57 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_57_9 (Nat.sub p 288)) (cc_57_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_57_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_57_6 (Nat.sub p 192)) (cc_57_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_57_4 (Nat.sub p 128)) (cc_57_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_57_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_57_1 (Nat.sub p 32)) (cc_57_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)
def f_57 : Nat → Nat × Nat := unpackForestF 0x9e15500c5f9d24500c5b00c579b84d9a2459aa4d9a04500c539905d97a559825d9785500b5f96a3500b5b95a6d00b579493d9323593a3d9313500b539204d90a459124d9084500b4f8f93500b4b00b478e23500b438cc648c8458934f8bb64893438a85d891558995d8905500a5f00a5b87c7c85b4f8637c8623485b4300a5700a5382b6f82b6b82b6782b6300a4f81a647dc6f80a447dc6b7fa7c7dc677e3447e2447dc6300a4b7cd6877b6f7bb6c77b6b7ad7077b6778b6c78a347893577b637795d00a4776a647046f75a447046b74a7c7046773a44704637002870b5f70b5b70b5770b537002400a436f3546c56b6e3546c5636c26f6c2676c13500a3f00a3b6ac5866d6b68c5868a546885566d6366a6f66a676684d00a37651286512400a33641346234b6315c622476223f0095f0095b60b7c5d34b5d26d5f5705d2475db7c5da7c5d23f009575b0185b0155b014009535a35453b635946453a6f57d635785d53a4556b5453a3f55944544635426f5424d538450094f0094b5213451b630094750815009434e56f4e26f4e96c4e2570093f4d0150093b4c46845d6f4ac684a86545a6f49c6045a574826e4803545a4d45a3d4626f462454584d009370093343b4443a44434630092f420150092b4034440244401443f4633f146009273d94c3d944009233ca453834f3824f382373aa453814f3924d3904c38137381270085f0085b3647c362453334f3326d34a7c3324f33c7033237008573102c3102631024008532eb6f2ea6f2f04c2ea370084f2d8260084b2cd6829b6f2996f2b16e2995d2a46029937008472803c2803400843273541f563263641f26f1f25f2494d1f23523a351f16f22b541f15f21a4d1f1351fb441fa441f9441f1270083f0083b1d8541c5631c26f1c25f008371a02c1a0261a024008331926418c6f0082f178260082b15b5415a54158540ed6314b640ec6f12b5412a54128540ec5f0e96f1035410254100540e95f0f35c0e947008270d05c0d054008230081f0b8260081b0926809264091640906401b6f01a6f0794601a6306b7201a3b01a3a01a3704a3e01a360194a0212b0212a021260194600817008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 fullMask g_57 ep_57 317 bds_57 (dagTraceF fullMask rootStock 11 f_57) (cur_57 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_9 : treeBlockF 288 317 (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nj_57_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join nj_57_1 (fun _ h1 h2 => treeBlockF_at nb_57_2 h1 h2)
theorem nj_57_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join nj_57_2 (fun _ h1 h2 => treeBlockF_at nb_57_3 h1 h2)
theorem nj_57_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join nj_57_3 (fun _ h1 h2 => treeBlockF_at nb_57_4 h1 h2)
theorem nj_57_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join nj_57_4 (fun _ h1 h2 => treeBlockF_at nb_57_5 h1 h2)
theorem nj_57_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join nj_57_5 (fun _ h1 h2 => treeBlockF_at nb_57_6 h1 h2)
theorem nj_57_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join nj_57_6 (fun _ h1 h2 => treeBlockF_at nb_57_7 h1 h2)
theorem nj_57_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join nj_57_7 (fun _ h1 h2 => treeBlockF_at nb_57_8 h1 h2)
theorem nj_57_9 : ∀ i, 0 ≤ i → i < 317 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := block_join nj_57_8 (fun _ h1 h2 => treeBlockF_at nb_57_9 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 317 → (dagCheckNodeV4 fullMask g_57 ep_57 bds_57 317 (dagTraceF fullMask rootStock 11 f_57) cur_57) i = true := nj_57_9
theorem lb_57 : LowerBin fullMask rootStock g_57 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3902851072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3902851072)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3902851072) = g_57 by decide]
  exact lb_57

end PEqualNP.Outside.L_meta_49185

theorem PEqualNP.Outside.L_meta_49185 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3902851072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3902851072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49185.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3902851072) 13 PEqualNP.Outside.L_meta_49185.root_lb PEqualNP.Outside.L_meta_49185.wg 18 rfl PEqualNP.Outside.L_meta_49185.wfits PEqualNP.Outside.L_meta_49185.weval
