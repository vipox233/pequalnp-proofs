import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48025

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
theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp
theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]
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
def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1
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
def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l
theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]
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
def forceWP {α : Type} (w : Nat) (k : Nat → α) : α :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem forceWP_eq {α : Type} (w : Nat) (k : Nat → α) : forceWP w k = k w := by
  cases w <;> rfl
def forceCons {α : Type} (l : List Nat) (k : List Nat → α) : α :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem forceCons_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceCons l k = k l := by
  cases l <;> rfl
def forceList {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
  (List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun w _ next k => next (fun rest => k (w :: rest))) ws) k
theorem forceList_eq {α : Type} (ws : List Nat) (k : List Nat → α) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceList ws (fun rest => k (w :: rest)) = _
    rw [ih]
def canonV2 (mask w : Nat) : Nat :=
  forceWP (Nat.land w mask) (fun v =>
    Bool.rec
      (Bool.rec
        (forceWP (Nat.xor mask v) (fun iv => Bool.rec iv v (Nat.blt v iv)))
        0 (Nat.beq v mask))
      0 (Nat.beq v 0))
theorem canonV2_eq (mask w : Nat) : canonV2 mask w = canon mask w := by
  unfold canonV2 canon bsel; dsimp only
  rw [forceWP_eq]
  change Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (forceWP (Nat.xor mask (w &&& mask)) (fun iv => Bool.rec (motive := fun _ => Nat) iv (w &&& mask) (Nat.blt (w &&& mask) iv)))
      0 (Nat.beq (w &&& mask) mask)) 0 (Nat.beq (w &&& mask) 0) = _
  rw [forceWP_eq]
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def HistValid (mask : Nat) (stock : List Nat) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (z, x, y) :: rest =>
    (∃ op < 4, z = binOp mask op x y) ∧
    (x ∈ stock ∨ ∃ a b, (x, a, b) ∈ rest) ∧
    (y ∈ stock ∨ ∃ a b, (y, a, b) ∈ rest) ∧
    HistValid mask stock rest
def WsCovered (stock : List Nat) (hist : List (Nat × Nat × Nat)) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w ∈ stock ∨ ∃ a b, (w, a, b) ∈ hist
theorem getD_mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
theorem childState_valid {mask token : Nat} {stock : List Nat}
    {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (hv : HistValid mask stock st.2.2) (hc : WsCovered stock st.2.2 st.2.1)
    (h : childState mask token st = some ch) :
    HistValid mask stock ch.2.2 ∧ WsCovered stock ch.2.2 ch.2.1 := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at hv hc
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok
      have hab : (token >>> 8) < ((token >>> 4) &&& 15) := by
        cases h1 : Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
        · exfalso; exact hok (Or.inl (Or.inr h1))
        · exact Nat.blt_eq.mp h1
      have hbl : ((token >>> 4) &&& 15) < ws.length := by
        cases h2 : Nat.blt ((token >>> 4) &&& 15) ws.length
        · exfalso; exact hok (Or.inr h2)
        · exact Nat.blt_eq.mp h2
      have hx : ws.getD (token >>> 8) 0 ∈ ws := getD_mem_of_lt (by omega)
      have hy : ws.getD ((token >>> 4) &&& 15) 0 ∈ ws := getD_mem_of_lt hbl
      have hop : ((token >>> 2) &&& 3) < 4 := by
        have := Nat.and_lt_two_pow (token >>> 2) (n := 2) (by omega : 3 < 2 ^ 2)
        simpa using this
      refine ⟨⟨⟨(token >>> 2) &&& 3, hop, rfl⟩, hc _ hx, hc _ hy, hv⟩, ?_⟩
      intro w hw
      rcases insertSorted_mem.mp hw with rfl | hrest
      · exact Or.inr ⟨_, _, List.mem_cons_self⟩
      · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hrest).1).1
        rcases hc w hwm with hst | ⟨a, b, hmem⟩
        · exact Or.inl hst
        · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ hmem⟩
theorem dagTrace_valid {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) :
    HistValid mask stock st.2.2 ∧ WsCovered stock st.2.2 st.2.1 := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s →
      HistValid mask stock s.2.2 ∧ WsCovered stock s.2.2 s.2.1 from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s
        exact ⟨trivial, fun w hw => Or.inl (subsetWords_subset stock _ w hw)⟩
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p =>
        rw [hp] at h
        have ⟨hv, hc⟩ := ih _ _ hp
        exact childState_valid hv hc h
theorem addUniq_mem {w u : Nat} {l : List Nat} : u ∈ addUniq w l ↔ u = w ∨ u ∈ l := by
  unfold addUniq
  cases h : l.contains w
  · simp [List.mem_cons]
  · simp only [ite_true]
    have hw : w ∈ l := List.contains_iff_mem.mp h
    constructor
    · exact Or.inr
    · rintro (rfl | hu); exact hw; exact hu
theorem recipeStart_mem {cut : Nat} {stock ws : List Nat} {u : Nat} :
    u ∈ recipeStart cut stock ws ↔ ∃ w ∈ ws, canon cut w = u ∧ ¬Avail stock u := by
  induction ws with
  | nil => simp [recipeStart]
  | cons w ws ih =>
    change u ∈ (if availB stock (canon cut w) then recipeStart cut stock ws
                else addUniq (canon cut w) (recipeStart cut stock ws)) ↔ _
    cases ha : availB stock (canon cut w)
    · simp only [Bool.false_eq_true, ite_false, addUniq_mem, ih]
      have hna : ¬Avail stock (canon cut w) := fun h => by rw [availB_spec.mpr h] at ha; exact Bool.noConfusion ha
      constructor
      · rintro (rfl | ⟨w', hw', rfl, hnu⟩)
        · exact ⟨w, List.mem_cons_self, rfl, hna⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact Or.inl rfl
        · exact Or.inr ⟨w', hw', rfl, hnu⟩
    · simp only [ite_true, ih]
      have hya : Avail stock (canon cut w) := availB_spec.mp ha
      constructor
      · rintro ⟨w', hw', rfl, hnu⟩; exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd hya hnu
        · exact ⟨w', hw', rfl, hnu⟩
theorem recipeClose_sub {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} {acc : List Nat} :
    ∀ u ∈ acc, u ∈ recipeClose cut stock hist acc := by
  induction hist generalizing acc with
  | nil => intro u hu; exact hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro u hu
    change u ∈ (if acc.contains (canon cut w) then
      let va := canon cut a; let vb := canon cut b
      let acc1 := if availB stock va then acc else addUniq va acc
      let acc2 := if availB stock vb then acc1 else addUniq vb acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist acc)
    split
    · apply ih
      have h1 : u ∈ (if availB stock (canon cut a) then acc else addUniq (canon cut a) acc) := by
        split; exact hu; exact addUniq_mem.mpr (Or.inr hu)
      split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · exact ih u hu
theorem recipeClose_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeClose cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    change (if [].contains (canon cut w) then _ else recipeClose cut stock hist []) = []
    exact ih
theorem recipeClose_mono {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} :
    ∀ {A B : List Nat}, (∀ u ∈ A, u ∈ B) →
      ∀ u ∈ recipeClose cut stock hist A, u ∈ recipeClose cut stock hist B := by
  induction hist with
  | nil => intro A B hAB u hu; exact hAB u hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro A B hAB u hu
    change u ∈ (if A.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then A else addUniq (canon cut a) A
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist A) at hu
    change u ∈ (if B.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then B else addUniq (canon cut a) B
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist B)
    cases hA : A.contains (canon cut w)
    · simp only [hA, Bool.false_eq_true, ite_false] at hu
      cases hB : B.contains (canon cut w)
      · simp only [Bool.false_eq_true, ite_false]; exact ih hAB u hu
      · simp only [ite_true]
        apply ih _ u hu
        intro x hx
        have h1 : x ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
          split; exact hAB x hx; exact addUniq_mem.mpr (Or.inr (hAB x hx))
        split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · have hwB : B.contains (canon cut w) = true := List.contains_iff_mem.mpr (hAB _ (List.contains_iff_mem.mp hA))
      simp only [hA, ite_true] at hu
      simp only [hwB, ite_true]
      apply ih _ u hu
      intro x hx
      have h1 : ∀ y, y ∈ (if availB stock (canon cut a) then A else addUniq (canon cut a) A) →
          y ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
        intro y hy
        cases hca : availB stock (canon cut a)
        · simp only [hca, Bool.false_eq_true, ite_false, addUniq_mem] at hy ⊢
          rcases hy with rfl | hy; exact Or.inl rfl; exact Or.inr (hAB y hy)
        · simp only [hca, ite_true] at hy ⊢; exact hAB y hy
      cases hcb : availB stock (canon cut b)
      · simp only [hcb, Bool.false_eq_true, ite_false, addUniq_mem] at hx ⊢
        rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (h1 x hx)
      · simp only [hcb, ite_true] at hx ⊢; exact h1 x hx
noncomputable def buildFrom (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (z, x, y) :: rest =>
    let vs := buildFrom cut bstock S rest
    let v := canon cut z
    let := Classical.propDecidable
    if v ∈ S ∧ ¬Avail (vs ++ bstock) v ∧ Avail (vs ++ bstock) (canon cut x) ∧ Avail (vs ++ bstock) (canon cut y)
    then vs ++ [v] else vs
theorem buildFrom_builds {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      BuildsBin cut bstock (buildFrom cut bstock S hist)
  | [], _ => trivial
  | (z, x, y) :: rest, ⟨⟨op, hop, hz⟩, _, _, hrest⟩ => by
    unfold buildFrom; dsimp only
    have ih := buildFrom_builds (bstock := bstock) (S := S) sub hrest
    split
    · rename_i hcond
      obtain ⟨_, hna, hax, hay⟩ := hcond
      have hgate : GateBin cut (buildFrom cut bstock S rest ++ bstock) (canon cut z) := by
        have hsub := canon_sub_binOp (op := op) (a := x) (b := y) sub
        rw [← hz] at hsub
        rcases hsub with h0 | hx | hy | ⟨op', hop', heq⟩
        · exact absurd (Or.inl h0) hna
        · exact absurd (hx ▸ hax) hna
        · exact absurd (hy ▸ hay) hna
        · exact ⟨canon cut x, canon cut y, op', hop', hax, hay, heq⟩
      exact builds_append ih ⟨hgate, trivial⟩
    · exact ih
theorem buildFrom_nodup_sub (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    ∀ (hist : List (Nat × Nat × Nat)),
      (buildFrom cut bstock S hist).Nodup ∧ ∀ u ∈ buildFrom cut bstock S hist, u ∈ S
  | [] => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | (z, x, y) :: rest => by
    unfold buildFrom; dsimp only
    obtain ⟨hnd, hsub⟩ := buildFrom_nodup_sub cut bstock S rest
    split
    · rename_i hcond
      obtain ⟨hvS, hna, _, _⟩ := hcond
      have hnm : canon cut z ∉ buildFrom cut bstock S rest := fun hm =>
        hna (Or.inr (List.mem_append_left bstock hm))
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun a ha b hb heq => by
        rw [List.mem_singleton.mp hb] at heq; exact hnm (heq ▸ ha)⟩, ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hsub u hu
      · rw [List.mem_singleton.mp hu]; exact hvS
    · exact ⟨hnd, hsub⟩
theorem buildFrom_mono_avail (cut : Nat) (bstock : List Nat) (S : Finset Nat)
    (r : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) {u : Nat}
    (hu : Avail (buildFrom cut bstock S rest ++ bstock) u) :
    Avail (buildFrom cut bstock S (r :: rest) ++ bstock) u := by
  obtain ⟨z, x, y⟩ := r
  unfold buildFrom; dsimp only
  split
  · exact avail_weaken (fun w hw => by simp only [List.mem_append] at hw ⊢; tauto) hu
  · exact hu
theorem buildFrom_covers {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (hstk : ∀ s ∈ stock, Avail bstock (canon cut s)) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      ∀ (acc : List Nat),
        (∀ u ∈ acc, Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u) →
        (∀ u ∈ recipeClose cut bstock hist acc, u ∈ S) →
        ∀ u ∈ acc, Avail (buildFrom cut bstock S hist ++ bstock) u
  | [], _, acc, hcov, _, u, hu => by
    rcases hcov u hu with ha | ⟨_, _, _, hm, _⟩
    · exact avail_weaken (fun w hw => List.mem_append_right _ hw) ha
    · exact nomatch hm
  | (z, x, y) :: rest, ⟨_, hxc, hyc, hrest⟩, acc, hcov, hS, u, hu => by
    cases hcz : acc.contains (canon cut z)
    · have hnz : canon cut z ∉ acc := fun hm => by rw [List.contains_iff_mem.mpr hm] at hcz; exact Bool.noConfusion hcz
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then _ else recipeClose cut bstock rest acc)
        simp only [hcz, Bool.false_eq_true, ite_false]; exact hv
      have hcov' : ∀ v ∈ acc, Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v := by
        intro v hv
        rcases hcov v hv with ha | ⟨z', x', y', hm, heq⟩
        · exact Or.inl ha
        · rcases List.mem_cons.mp hm with hhead | htail
          · rcases Prod.mk.inj hhead with ⟨rfl, _⟩
            exact absurd (heq ▸ hv) hnz
          · exact Or.inr ⟨z', x', y', htail, heq⟩
      exact buildFrom_mono_avail cut bstock S (z, x, y) rest
        (buildFrom_covers hstk hrest acc hcov' hS' u hu)
    · have hzacc : canon cut z ∈ acc := List.contains_iff_mem.mp hcz
      have hzS : canon cut z ∈ S := hS _ (recipeClose_sub _ hzacc)
      set acc1 := if availB bstock (canon cut x) then acc else addUniq (canon cut x) acc
      set acc2 := if availB bstock (canon cut y) then acc1 else addUniq (canon cut y) acc1
      have hS2 : ∀ v ∈ recipeClose cut bstock rest acc2, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then recipeClose cut bstock rest acc2 else _)
        simp only [hcz, ite_true]; exact hv
      let := Classical.propDecidable
      set acc' := acc2.filter (fun v => decide (Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v))
      have hsub' : ∀ v ∈ acc', v ∈ acc2 := fun v hv => (List.mem_filter.mp hv).1
      have hcov' : ∀ v ∈ acc', Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v :=
        fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc', v ∈ S :=
        fun v hv => hS2 v (recipeClose_mono hsub' v hv)
      have hIH := buildFrom_covers hstk hrest acc' hcov' hS'
      have hacc_sub2 : ∀ v ∈ acc, v ∈ acc2 := by
        intro v hv
        have h1 : v ∈ acc1 := by
          unfold acc1; split; exact hv; exact addUniq_mem.mpr (Or.inr hv)
        unfold acc2; split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
      have hax : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut x) := by
        cases hbx : availB bstock (canon cut x)
        · have hx2 : canon cut x ∈ acc2 := by
            have hx1 : canon cut x ∈ acc1 := by
              unfold acc1; simp only [hbx, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
            unfold acc2; split; exact hx1; exact addUniq_mem.mpr (Or.inr hx1)
          have hpx : Avail bstock (canon cut x) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut x := by
            rcases hxc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk x hs)
            · exact Or.inr ⟨x, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hx2, decide_eq_true hpx⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hbx)
      have hay : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut y) := by
        cases hby : availB bstock (canon cut y)
        · have hy2 : canon cut y ∈ acc2 := by
            unfold acc2; simp only [hby, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
          have hpy : Avail bstock (canon cut y) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut y := by
            rcases hyc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk y hs)
            · exact Or.inr ⟨y, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hy2, decide_eq_true hpy⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hby)
      by_cases huz : u = canon cut z
      · subst huz
        unfold buildFrom; dsimp only
        split
        · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
        · rename_i hneg
          by_cases ha : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut z)
          · exact ha
          · exact absurd ⟨hzS, ha, hax, hay⟩ hneg
      · have hpu : Avail bstock u ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = u := by
          rcases hcov u hu with ha | ⟨z', x', y', hm, heq⟩
          · exact Or.inl ha
          · rcases List.mem_cons.mp hm with hhead | htail
            · rcases Prod.mk.inj hhead with ⟨rfl, _⟩; exact absurd heq.symm huz
            · exact Or.inr ⟨z', x', y', htail, heq⟩
        exact buildFrom_mono_avail cut bstock S (z, x, y) rest
          (hIH u (List.mem_filter.mpr ⟨hacc_sub2 u hu, decide_eq_true hpu⟩))
def flatStartF (cut : Nat) (stock ws : List Nat) : Nat × List Nat :=
  List.rec (0, []) (fun w _ ih =>
    match ih with
    | (fl, acc) =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec
          (Bool.rec
            (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
            (fl, acc) (memN v stock))
          (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
          (Nat.beq v 0))) ws
theorem flatStartF_eq (cut : Nat) (stock ws : List Nat) :
    flatStartF cut stock ws = (flatCount cut ws, recipeStart cut stock ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : flatStartF cut stock (w :: ws) =
      match flatStartF cut stock ws with
      | (fl, acc) =>
        forceWP (canonV2 cut w) (fun v =>
          Bool.rec
            (Bool.rec
              (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
              (fl, acc) (memN v stock))
            (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
            (Nat.beq v 0)) := rfl
    rw [hstep, ih]; dsimp only; rw [forceWP_eq, canonV2_eq, forceWP_eq]
    change Bool.rec
        (Bool.rec
          (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
            (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) (recipeStart cut stock ws)))
          (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) stock))
        (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) (Nat.beq (canon cut w) 0) =
      (bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws),
       if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    simp only [memN_eq, availB, addUniq]
    have haux (b1 b2 b3 : Bool) :
        Bool.rec (Bool.rec (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
          (flatCount cut ws, recipeStart cut stock ws) b3)
          (flatCount cut ws, recipeStart cut stock ws) b2)
          (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) b1 =
        (bsel b1 (flatCount cut ws + 1) (flatCount cut ws),
         if (b1 || b2) = true then recipeStart cut stock ws
         else if b3 = true then recipeStart cut stock ws else canon cut w :: recipeStart cut stock ws) := by
      cases b1 <;> cases b2 <;> cases b3 <;> rfl
    exact haux _ _ _
def recipeCloseV2 (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (next acc)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: acc) acc (memN va acc)) acc (memN va stock)) acc (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    next))))
          (memN v acc))) hist needed
theorem recipeCloseV2_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseV2 cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hstep : recipeCloseV2 cut stock ((w, a, b) :: hist) needed =
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (recipeCloseV2 cut stock hist needed)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: needed) needed (memN va needed)) needed (memN va stock)) needed (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    (recipeCloseV2 cut stock hist)))))
          (memN v needed)) := rfl
    rw [hstep]
    simp only [forceWP_eq, forceCons_eq, canonV2_eq, memN_eq]
    change Bool.rec (recipeCloseV2 cut stock hist needed) _ (needed.contains (canon cut w)) =
      (if needed.contains (canon cut w) then
        let va := canon cut a; let vb := canon cut b
        let acc1 := if availB stock va then needed else addUniq va needed
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        recipeClose cut stock hist acc2
      else recipeClose cut stock hist needed)
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only [ite_true]
      rw [ih]
      congr 1
      have hadd (v : Nat) (l : List Nat) :
          Bool.rec (Bool.rec (Bool.rec (v :: l) l (l.contains v)) l (stock.contains v)) l (Nat.beq v 0) =
          if availB stock v then l else addUniq v l := by
        dsimp only [availB, addUniq]
        have haux (b1 b2 b3 : Bool) :
            Bool.rec (Bool.rec (Bool.rec (v :: l) l b3) l b2) l b1 =
            if (b1 || b2) = true then l else if b3 = true then l else v :: l := by
          cases b1 <;> cases b2 <;> cases b3 <;> rfl
        exact haux _ _ _
      rw [hadd (canon cut a) needed, hadd (canon cut b)]
def boundClosesV2 (fuel : Nat) (ws : List Nat) (hist : List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, bstock, lower, _) := bound
  match flatStartF cut bstock ws with
  | (fl, start0) =>
    forceWP (Nat.sub fuel fl) (fun rem =>
      Bool.rec false
        (match start0 with
         | [] => true
         | s0 :: sr =>
           forceList (s0 :: sr) (fun start =>
             Bool.rec false
               (Nat.blt (Nat.add (lenN (recipeCloseV2 cut bstock hist start)) rem) lower)
               (Nat.blt (Nat.add (lenN start) rem) lower)))
        (Nat.blt rem lower))
theorem boundClosesV2_sound {mask goal : Nat} {stock : List Nat}
    {fuel : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (hg : canon bound.1 goal = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0)
    (hstk : ∀ s ∈ stock, Avail bound.2.1 (canon bound.1 s))
    (hv : HistValid mask stock hist) (hc : WsCovered stock hist ws)
    (nd : ws.Nodup) {k : Nat} (hk : k ≤ fuel)
    (hlive : LiveBin mask goal k ws.toFinset) :
    boundClosesV2 fuel ws hist bound = false := by
  obtain ⟨cut, bstock, lower, bgoal⟩ := bound
  dsimp only at hlow sub hg hnz hstk
  apply Bool.eq_false_iff.mpr
  intro hbc
  unfold boundClosesV2 at hbc; dsimp only at hbc
  rw [flatStartF_eq] at hbc; dsimp only at hbc
  simp only [forceWP_eq] at hbc
  cases h1 : Nat.blt (Nat.sub fuel (flatCount cut ws)) lower
  · rw [h1] at hbc; exact Bool.noConfusion hbc
  · rw [h1] at hbc; dsimp only at hbc
    have hlen_lt : (recipeClose cut bstock hist (recipeStart cut bstock ws)).length + (fuel - flatCount cut ws) < lower := by
      cases hs : recipeStart cut bstock ws with
      | nil =>
        rw [recipeClose_nil]; simp only [List.length_nil, Nat.zero_add]
        exact Nat.blt_eq.mp h1
      | cons s0 sr =>
        rw [hs] at hbc; dsimp only at hbc
        simp only [forceList_eq, recipeCloseV2_eq, lenN_eq] at hbc
        cases h2 : Nat.blt (Nat.add (s0 :: sr).length (Nat.sub fuel (flatCount cut ws))) lower
        · rw [h2] at hbc; exact Bool.noConfusion hbc
        · rw [h2] at hbc; dsimp only at hbc
          exact Nat.blt_eq.mp hbc
    set needed := recipeClose cut bstock hist (recipeStart cut bstock ws)
    set S := needed.toFinset
    set vs := buildFrom cut bstock S hist
    have hvbd : BuildsBin cut bstock vs := buildFrom_builds sub hv
    obtain ⟨hvnd, hvsub⟩ := buildFrom_nodup_sub cut bstock S hist
    have hvlen : vs.length ≤ needed.length := by
      rw [← List.toFinset_card_of_nodup hvnd]
      have hsubf : vs.toFinset ⊆ S := fun u hu => hvsub u (List.mem_toFinset.mp hu)
      exact Nat.le_trans (Finset.card_le_card hsubf) (List.toFinset_card_le needed)
    have hcov_start : ∀ u ∈ recipeStart cut bstock ws,
        Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u := by
      intro u hu
      obtain ⟨w, hww, rfl, hna⟩ := recipeStart_mem.mp hu
      rcases hc w hww with hws | ⟨a, b, hmem⟩
      · exact absurd (hstk w hws) hna
      · exact Or.inr ⟨w, a, b, hmem, rfl⟩
    have hvs_start := buildFrom_covers hstk hv (recipeStart cut bstock ws) hcov_start
      (fun u hu => List.mem_toFinset.mpr hu)
    have hsup : ∀ w ∈ ws.toFinset, Avail (vs ++ bstock) (canon cut w) := by
      intro w hw
      have hww : w ∈ ws := List.mem_toFinset.mp hw
      by_cases ha : Avail bstock (canon cut w)
      · exact avail_weaken (fun u hu => List.mem_append_right _ hu) ha
      · exact hvs_start _ (recipeStart_mem.mpr ⟨w, hww, rfl, ha⟩)
    have hgnf : canon cut goal ≠ 0 := hg.symm ▸ hnz
    obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (vs ++ bstock) hsup
    rw [← flatCount_card cut nd] at hylen
    have hboth := builds_append hvbd hybd
    have hfinal : Avail ((vs ++ ys) ++ bstock) bgoal := by
      rw [← hg]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (vs ++ ys) hboth hfinal
    simp only [List.length_append] at heno
    omega
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
def checkHintBoundV5 (goal negGoal fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (bounds : List (Nat × List Nat × Nat × Nat)) (cid : Nat) : Bool :=
  match nthBound bounds cid with
  | some b => boundClosesV2 fuel1 ws1 hist1 b
  | none => Bool.rec true false (dagPartF ws1 goal negGoal)
theorem checkHintBoundV5_open {mask goal fuel1 cid : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    checkHintBoundV5 goal (Nat.xor mask goal) fuel1 ws1 hist1 bounds cid = false := by
  unfold checkHintBoundV5
  cases hb : nthBound bounds cid with
  | some b =>
    dsimp only
    have hmem := nthBound_mem hb
    have hg := hgoals b hmem
    exact boundClosesV2_sound (hknown b hmem) (hsub b hmem) hg.1 hg.2 (hstk b hmem) hv hc nd hk hlive
  | none =>
    dsimp only
    have hdp : dagPartF ws1 goal (Nat.xor mask goal) = true := by
      have heq : dagPartF ws1 goal (Nat.xor mask goal) = dagPart ws1 goal (mask ^^^ goal) :=
        dagPartF_eq ws1 goal (mask ^^^ goal)
      rw [heq]; exact dagPart_live hgm hlive
    rw [hdp]
def hintCloseLeafV5 (goal negGoal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (sp : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec (some (cur, h))
    (forceWP (Nat.land h 3) (fun tag =>
      Bool.rec
        (Bool.rec none
          (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
          (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 3 (Nat.land h1 cutMask)) (fun cid =>
            Bool.rec none
              (forceWP (Nat.shiftRight h1 cutBits) (fun h' => some (cur, h')))
              (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
        (Nat.beq tag 3)))
    (Nat.beq (Nat.land ep sp) ep)
theorem hintCloseLeafV5_open {mask goal cutBits cutMask fuel1 : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)} {h : Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    hintCloseLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask bounds fuel1 ws1 hist1 (orSep ws1) cur h = none := by
  unfold hintCloseLeafV5
  rw [sepPack_live hgm hlive]; dsimp only
  rw [forceWP_eq]
  cases Nat.beq (Nat.land h 3) 3
  · dsimp only
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
  · dsimp only
    rw [forceWP_eq, forceWP_eq]
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
def stepLeafV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match cur with
  | (t, dest) :: tl =>
    Bool.rec
      (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) cur h)
      (Bool.rec none
        (match states dest with
         | none => none
         | some saved =>
           Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 (insertSortedF z rest)))
             (Nat.beq saved.1 fuel1))
        (Nat.blt dest count))
      (Nat.beq tok t)
  | [] =>
    hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) [] h
theorem stepLeafV5_ref {mask goal cutBits cutMask count fuel1 z tok h : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    {res : List (Nat × Nat) × Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 (z :: rest))
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (hok : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds states
      fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur h = some res) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (cur := cur) (h := h)
    hgm hknown hsub hgoals hstk hv hc nd hk hlive
  unfold stepLeafV5 at hok
  have hor : Nat.lor (sepPack z) (orSep rest) = orSep (z :: rest) := rfl
  rw [hor] at hok
  cases cur with
  | nil => dsimp only at hok; rw [hcl] at hok; cases hok
  | cons hd tl =>
    obtain ⟨t, dest⟩ := hd
    dsimp only at hok
    cases ht : Nat.beq tok t
    · rw [ht] at hok; dsimp only at hok; rw [hcl] at hok; cases hok
    · rw [ht] at hok; dsimp only at hok
      cases hlt : Nat.blt dest count
      · rw [hlt] at hok; dsimp only at hok; cases hok
      · rw [hlt] at hok; dsimp only at hok
        cases hst : states dest with
        | none => rw [hst] at hok; dsimp only at hok; cases hok
        | some saved =>
          rw [hst] at hok; dsimp only at hok
          cases hf : Nat.beq saved.1 fuel1
          · rw [hf] at hok; dsimp only at hok; cases hok
          · rw [hf] at hok; dsimp only at hok
            cases heq : eqListN saved.2.1 (insertSortedF z rest)
            · rw [heq] at hok; dsimp only at hok; cases hok
            · rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at heq
              exact ⟨dest, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, heq⟩
def checkKeepsV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match (Bool.rec
    (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => none
  | some (c1, h1) =>
    match (Bool.rec
      (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => none
    | some (c2, h2) =>
      match (Bool.rec
        (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => none
      | some (c3, h3) =>
        Bool.rec
          (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3 h3)
          (some (c3, h3)) (Nat.blt fuel (Nat.add n 1))
theorem checkKeepsV5_at {goal negGoal ep cutBits cutMask count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hok : checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur h = some res)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c hh = some r
    | true, false => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c hh = some r
    | false, true => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c hh = some r
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c hh = some r := by
  unfold checkKeepsV5 at hok
  cases hp0 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1
    rw [hp0] at hok; dsimp only at hok
    cases hp1 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2
      rw [hp1] at hok; dsimp only at hok
      cases hp2 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3
        rw [hp2] at hok; dsimp only at hok
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, h, (c1, h1), hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, h2, (c3, h3), hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, h1, (c2, h2), hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at hok; exact Or.inr ⟨c3, h3, res, hok⟩
          · exact Or.inl rfl
def checkOpV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  forceWP (canonV2 mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWP (sepPack z) (fun spZ =>
          checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur h))
        (some (cur, h)) (memN z ws0))
      (some (cur, h)) (Nat.beq z 0))
def check4OpsV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => none
  | some (c1, h1) =>
    match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => none
    | some (c2, h2) =>
      match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => none
      | some (c3, h3) =>
        checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3 h3
theorem check4OpsV5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hop : op < 4)
    (hok : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h = some res) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z (sepPack z)
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c hh = some r := by
  unfold check4OpsV5 at hok
  have extract (rawZ op' : Nat) (c0 : List (Nat × Nat)) (h0 : Nat) (r0 : List (Nat × Nat) × Nat)
      (hz : canon mask rawZ = binOp mask op' x y)
      (hrun : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y rawZ op'
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0 h0 = some r0) :
      binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
        ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n (binOp mask op' x y)
          (sepPack (binOp mask op' x y)) spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB
          ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c hh = some r := by
    unfold checkOpV5 at hrun
    rw [forceWP_eq, canonV2_eq, hz] at hrun
    cases hz0 : Nat.beq (binOp mask op' x y) 0
    · rw [hz0] at hrun; dsimp only at hrun
      cases hm : memN (binOp mask op' x y) ws0
      · rw [hm] at hrun; dsimp only at hrun
        rw [forceWP_eq] at hrun
        exact Or.inr (Or.inr ⟨c0, h0, r0, hrun⟩)
      · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inl (Nat.beq_eq.mp hz0)
  cases hp0 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1; rw [hp0] at hok; dsimp only at hok
    cases hp1 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2; rw [hp1] at hok; dsimp only at hok
      cases hp2 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3; rw [hp2] at hok; dsimp only at hok
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur h (c1, h1) rfl hp0
        · exact extract _ 1 c1 h1 (c2, h2) rfl hp1
        · exact extract _ 2 c2 h2 (c3, h3) rfl hp2
        · exact extract _ 3 c3 h3 res rfl hok
def loopB_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, b, cur, h =>
    forceWP (getDN ws0 b) (fun y =>
      forceList (dropValF true y ws0) (fun wsNoB =>
        forceList (dropValF true y wsNoA) (fun wsNoAB =>
          forceWP (orSepSkip y ps) (fun spNoB =>
            forceWP (orSepSkip2 x y ps) (fun spNoAB =>
              forceWP (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) (fun tokAB =>
                match check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
                | none => none
                | some (cur1, h1) =>
                  loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1 h1))))))
theorem loopB_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (hok : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur h = some res) :
    let y := getDN ws0 b
    ∃ c hh r, check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c hh = some r := by
  induction rem generalizing b0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopB_V5 at hok
    rw [forceWP_eq, forceList_eq, forceList_eq, forceWP_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : b = b0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) hok
def loopA_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, a, cur, h =>
    forceWP (getDN ws0 a) (fun x =>
      forceList (dropValF true x ws0) (fun wsNoA =>
        forceWP (Nat.xor mask x) (fun nx =>
          forceWP (orSepSkip x ps) (fun spNoA =>
            match loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur h with
            | none => none
            | some (cur1, h1) =>
              loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1 h1))))
theorem loopA_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (hok : loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur h = some res) :
    let x := getDN ws0 a
    ∃ c hh r, loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c hh = some r := by
  induction rem generalizing a0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopA_V5 at hok
    rw [forceWP_eq, forceList_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : a = a0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) hok
def dagCheckNodeV5 (mask goal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (nodeHints : Nat → Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      forceWP (lenN ws0) (fun n =>
        Bool.rec
          (Bool.rec
            (Bool.rec false
              (forceW (Nat.xor mask goal) (fun negGoal =>
                forceW (Nat.sub fuel 1) (fun fuel1 =>
                  forceSepPairs ws0 (fun ps =>
                    forceW (orSepAll ps) (fun spAll =>
                      forceW (nodeHints (Nat.add i 1)) (fun h0 =>
                        match loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist n 0 (cursors (Nat.add i 1)) h0 with
                        | none => false
                        | some _ => true))))))
              (Nat.blt n 17))
            true (Nat.beq fuel 0))
          false (memN goal ws0)))
def stepRootV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec
    (match cur with
     | (t, dest) :: tl =>
       Bool.rec
         (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) cur h)
         (Bool.rec none
           (match states dest with
            | none => none
            | some saved =>
              Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 ws)) (Nat.beq saved.1 fuel))
           (Nat.blt dest count))
         (Nat.beq tok t)
     | [] =>
       hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) [] h)
    (some (cur, h)) (Nat.blt (Nat.add fuel 1) (lenN ws))
def loopRootsV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, tok, cur, h =>
    forceList (subsetWordsF stock tok) (fun ws =>
      match stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states ws tok cur h with
      | none => none
      | some (cur1, h1) =>
        loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem (Nat.add tok 1) cur1 h1)
def dagCheckRootsV5 (mask goal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (rootHint : Nat) (stock : List Nat) (fuel : Nat) : Bool :=
  match loopRootsV5 goal (Nat.xor mask goal) ep cutBits cutMask count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur rootHint with
  | none => false
  | some _ => true
theorem loopRootsV5_at {goal negGoal ep cutBits cutMask count fuel : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (hok : loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem t0 cur h = some res) :
    ∃ c hh r, stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock tok) tok c hh = some r := by
  induction rem generalizing t0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV5 at hok
    rw [forceList_eq] at hok
    cases hp : stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock t0) t0 cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : tok = t0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) hok
theorem dagAllNodesV5 {mask goal cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal (edgePack mask goal) cutBits cutMask bounds count
      (dagTrace mask stock fuel forest) cursors nodeHints i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    obtain ⟨hv, hcov⟩ := dagTrace_valid htr
    dsimp only at hv hcov
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV5 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, forceWP_eq, lenN_eq, memN_eq] at hchk
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
          rw [forceW_eq, forceW_eq, forceSepPairs_eq, forceW_eq, forceW_eq] at hchk
          cases hloop : loopA_V5 mask goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
              (dagTrace mask stock fuel forest) rem (Nat.sub rem 1) ws.length (orSepAll (mapSep ws)) ws (mapSep ws) hist
              ws.length 0 (cursors (Nat.add i 1)) (nodeHints (Nat.add i 1)) with
          | none => rw [hloop] at hchk; exact Bool.noConfusion hchk
          | some resA =>
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
            obtain ⟨cA, hA, rA, hB⟩ := loopA_V5_at (a := a) (Nat.zero_le a) (by omega) hloop
            obtain ⟨cB, hB', rB, hO⟩ := loopB_V5_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
            simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
            set x := ws.getD a 0
            set y := ws.getD b 0
            set z := binOp mask op x y
            have hznz : z ≠ 0 := hzeq.symm ▸ hz0
            have hznm : ws.contains z = false := by
              cases h : ws.contains z
              · rfl
              · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
            rcases check4OpsV5_at hop_lt hO with hz' | hcm | ⟨cK, hK', rK, hK⟩
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
              have hv' : HistValid mask stock ((z, x, y) :: hist) :=
                ⟨⟨op, hop_lt, rfl⟩, hcov x hxM, hcov y hyM, hv⟩
              have hcov' : WsCovered stock ((z, x, y) :: hist) (z :: rest) := by
                intro w hw
                rcases List.mem_cons.mp hw with rfl | hw'
                · exact Or.inr ⟨x, y, List.mem_cons_self⟩
                · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hw').1).1
                  rcases hcov w hwm with hst | ⟨u, v, hm⟩
                  · exact Or.inl hst
                  · exact Or.inr ⟨u, v, List.mem_cons_of_mem _ hm⟩
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
              have hka := checkKeepsV5_at hK keepA keepB
              have finish {tok' hh' : Nat} {c' : List (Nat × Nat)} {rr : List (Nat × Nat) × Nat}
                  (hstep : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
                    (dagTrace mask stock fuel forest) (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c' hh' = some rr) : False := by
                obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                  stepLeafV5_ref hgm hknown hsub hgoals hstk hv' hcov' hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
                exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
              cases keepA <;> cases keepB
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
                · rw [hdropComm] at hst; exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
                · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk
def nodupB : List Nat → Bool
  | [] => true
  | w :: ws => !memN w ws && nodupB ws
theorem nodupB_spec {l : List Nat} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold nodupB at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', memN_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1, ih h.2⟩
theorem kn_nil : KnownBin [] := fun _ h => nomatch h
theorem kn_cons {m : Nat} {s : List Nat} {l g : Nat} {bs : List (Nat × List Nat × Nat × Nat)}
    (h : LowerBin m s g l) (hs : KnownBin bs) : KnownBin ((m, s, l, g) :: bs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h
  · exact hs b hb
def checkSliceMetaV5 (mask goal ep : Nat) (stock : List Nat)
    (bounds : List (Nat × List Nat × Nat × Nat)) : Bool :=
  Nat.beq (Nat.land goal mask) goal &&
  !Nat.beq goal 0 &&
  stock.all (fun w => Nat.beq (canon mask w) w) &&
  nodupB stock &&
  Nat.beq ep (edgePack mask goal) &&
  bounds.all (fun b =>
    Nat.beq (Nat.land mask b.1) b.1 &&
    Nat.beq (canon b.1 goal) b.2.2.2 &&
    !Nat.beq b.2.2.2 0 &&
    stock.all (fun s => availB b.2.1 (canon b.1 s)))
theorem lowerDagV5 {mask goal ep cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hknown : KnownBin bounds)
    (hroots : dagCheckRootsV5 mask goal ep cutBits cutMask count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) (nodeHints 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal ep cutBits cutMask bounds count
      (dagTraceF mask stock fuel forest) cursors nodeHints i = true)
    (hmeta : checkSliceMetaV5 mask goal ep stock bounds = true) :
    LowerBin mask stock goal (fuel + 1) := by
  unfold checkSliceMetaV5 at hmeta
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmeta
  obtain ⟨⟨⟨⟨⟨hgmB, hgnzB⟩, hcs⟩, hndB⟩, hepB⟩, hbdB⟩ := hmeta
  have hgm : Masked mask goal := Nat.beq_eq.mp hgmB
  have hgnz : goal ≠ 0 := fun h => by rw [h] at hgnzB; exact Bool.noConfusion hgnzB
  have snd : stock.Nodup := nodupB_spec hndB
  have hep : ep = edgePack mask goal := Nat.beq_eq.mp hepB
  have hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact Nat.beq_eq.mp h.1.1.1
  have hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Nat.beq_eq.mp h.1.1.2, fun h0 => by rw [h0] at h; exact Bool.noConfusion h.1.2⟩
  have hstkB : ∀ b ∈ bounds, stock.all (fun s => availB b.2.1 (canon b.1 s)) = true := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact h.2
  subst hep
  have hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s) := fun b hb s hs =>
    availB_spec.mp (List.all_eq_true.mp (hstkB b hb) s hs)
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
  unfold dagCheckRootsV5 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  cases hrl : loopRootsV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count fuel bounds
      (dagTrace mask stock fuel forest) stock (2 ^ stock.length) 0 (cursors 0) (nodeHints 0) with
  | none => rw [hrl] at hroots; exact Bool.noConfusion hroots
  | some resR =>
    obtain ⟨c, hh, rr, hsr⟩ := loopRootsV5_at (tok := tok) (Nat.zero_le tok) (by omega) hrl
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
    have hcov0 : WsCovered stock [] (subsetWords stock tok) :=
      fun w hw => Or.inl (subsetWords_subset stock tok w hw)
    have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (fuel1 := fuel) (hist1 := []) (cur := c) (h := hh)
      hgm hknown hsub hgoals hstk trivial hcov0 hnd (k := k) (by omega) hlive'
    unfold stepRootV5 at hsr
    rw [hnw] at hsr; dsimp only at hsr
    cases c with
    | nil => dsimp only at hsr; rw [hcl] at hsr; cases hsr
    | cons hd tl =>
      obtain ⟨t, dest⟩ := hd
      dsimp only at hsr
      cases ht : Nat.beq tok t
      · rw [ht] at hsr; dsimp only at hsr; rw [hcl] at hsr; cases hsr
      · rw [ht] at hsr; dsimp only at hsr
        cases hltc : Nat.blt dest count
        · rw [hltc] at hsr; dsimp only at hsr; cases hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest dest with
          | none => rw [htr2] at hsr; dsimp only at hsr; cases hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; dsimp only at hsr; cases hsr
            · rw [hf] at hsr; dsimp only at hsr
              cases heq : eqListN saved.2.1 (subsetWords stock tok)
              · rw [heq] at hsr; dsimp only at hsr; cases hsr
              · rw [eqListN_eq, beq_iff_eq] at heq
                exact dagAllNodesV5 hgm hknown hsub hgoals hstk snd hnodes fuel dest saved
                  (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (heq ▸ hlive')
def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)
def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))
def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    forceWP (Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask) (fun code =>
      unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc))
def unpackCursorV5 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      unpackListAux data (Nat.shiftRight entry sizeBits) w wMask tokBits tokMask (Nat.land entry sizeMask) [])
def unpackHintV5 (index data idxW idxMask lenBits lenMask : Nat) : Nat → Nat :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      forceWP (Nat.land entry lenMask) (fun hlen =>
        Bool.rec
          (Nat.land (Nat.shiftRight data (Nat.shiftRight entry lenBits)) (Nat.sub (Nat.shiftLeft 1 hlen) 1))
          0 (Nat.beq hlen 0)))

def m_0 : Nat := 0xf000f0
def s_0 : List Nat := [0x500050, 0x300030, 0xf0]
def g_0 : Nat := 0x100070
def ep_0 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_0 : Nat → Nat := fun _ => 0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 m_0 g_0 ep_0 1 1 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 m_0 g_0 ep_0 1 1 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) (nh_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)

def m_1 : Nat := 0x5500550000000000
def s_1 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_1 : Nat := 0x100150000000000
def ep_1 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_1 : Nat → Nat := fun _ => 0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 m_1 g_1 ep_1 1 1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 m_1 g_1 ep_1 1 1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) (nh_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)

def m_2 : Nat := 0xf0f0000
def s_2 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_2 : Nat := 0x1070000
def ep_2 : Nat := 0x60000000000000000000000000000010200000000000001040000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_2 : Nat → Nat := fun _ => 0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 m_2 g_2 ep_2 1 1 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 m_2 g_2 ep_2 1 1 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) (nh_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)

def m_3 : Nat := 0xff0000
def s_3 : List Nat := [0x550000, 0x330000, 0xf0000]
def g_3 : Nat := 0x170000
def ep_3 : Nat := 0x6000000000000001200000000000000140000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_3 : Nat → Nat := fun _ => 0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 m_3 g_3 ep_3 1 1 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 m_3 g_3 ep_3 1 1 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) (nh_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)

def m_4 : Nat := 0x4444444400000000
def s_4 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_4 : Nat := 0x4044400000000
def ep_4 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_4 : Nat → Nat := fun _ => 0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 m_4 g_4 ep_4 1 1 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 m_4 g_4 ep_4 1 1 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) (nh_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)

def m_5 : Nat := 0x5050505000000000
def s_5 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_5 : Nat := 0x10105000000000
def ep_5 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_5 : Nat → Nat := fun _ => 0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 m_5 g_5 ep_5 1 1 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 m_5 g_5 ep_5 1 1 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) (nh_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)

def m_6 : Nat := 0xf000f000
def s_6 : List Nat := [0x50005000, 0x30003000, 0xf000]
def g_6 : Nat := 0x10007000
def ep_6 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_6 : Nat → Nat := fun _ => 0
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_6 : Nat → Bool := dagCheckNodeV5 m_6 g_6 ep_6 1 1 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV5 m_6 g_6 ep_6 1 1 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) (nh_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)

def m_7 : Nat := 0x5000500050005000
def s_7 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_7 : Nat := 0x100010005000
def ep_7 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_7 : Nat → Nat := fun _ => 0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 m_7 g_7 ep_7 1 1 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 m_7 g_7 ep_7 1 1 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) (nh_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)

def m_8 : Nat := 0x3000300030003000
def s_8 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_8 : Nat := 0x100010003000
def ep_8 : Nat := 0x1000200000001000000020000000000000000000000000000000000000000000000000000000100010000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_8 : Nat → Nat := fun _ => 0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 m_8 g_8 ep_8 1 1 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 m_8 g_8 ep_8 1 1 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) (nh_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)

def m_9 : Nat := 0x3333000000000000
def s_9 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_9 : Nat := 0x113000000000000
def ep_9 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_9 : Nat → Nat := fun _ => 0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 m_9 g_9 ep_9 1 1 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 m_9 g_9 ep_9 1 1 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) (nh_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)

def m_10 : Nat := 0x5555000000000000
def s_10 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_10 : Nat := 0x115000000000000
def ep_10 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_10 : Nat → Nat := fun _ => 0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 m_10 g_10 ep_10 1 1 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 m_10 g_10 ep_10 1 1 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) (nh_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)

def m_11 : Nat := 0xaa000000aa
def s_11 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_11 : Nat := 0x20000002a
def ep_11 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_11 : Nat → Nat := fun _ => 0
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_11 : Nat → Bool := dagCheckNodeV5 m_11 g_11 ep_11 1 1 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV5 m_11 g_11 ep_11 1 1 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) (nh_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 ch_11 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → ch_11 i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV5 (kn_nil) rc_11 nc_11 (by decide +kernel)

def m_12 : Nat := 0xff000000000000
def s_12 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_12 : Nat := 0x17000000000000
def ep_12 : Nat := 0x600000000000000120000000000000014000000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_12 : Nat → Nat := fun _ => 0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) (nh_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0xcc00cc
def s_13 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_13 : Nat := 0x4004c
def ep_13 : Nat := 0x480000000000000000000000000004000800000000000000000000000000040040
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_13 : Nat → Nat := fun _ => 0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) (nh_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0xf0f000000000000
def s_14 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_14 : Nat := 0x107000000000000
def ep_14 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_14 : Nat → Nat := fun _ => 0
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) (nh_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0xaa00aa
def s_15 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_15 : Nat := 0x2002a
def ep_15 : Nat := 0x280000000000000000000000000002000800000000000200200000000000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_15 : Nat → Nat := fun _ => 0
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) (nh_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xcc000000cc00
def s_16 : List Nat := [0x440000004400, 0xc0000000c00, 0xcc00]
def g_16 : Nat := 0x40000004c00
def ep_16 : Nat := 0x480000000000000000000000000000000000000004000000080000000000000000000000040000004000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_16 : Nat → Nat := fun _ => 0
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) (nh_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xf0000000f000
def s_17 : List Nat := [0x500000005000, 0x300000003000, 0xf000]
def g_17 : Nat := 0x100000007000
def ep_17 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_17 : Nat → Nat := fun _ => 0
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) (nh_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xf0f0f0f0000
def s_18 : List Nat := [0x50505050000, 0x30303030000, 0xf000f0000, 0xf0f0000]
def g_18 : Nat := 0x50701070000
def ep_18 : Nat := 0x200060000000000000000000000000002010200000000050401040000
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def nh_18 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xf0f000000000f0f
def s_19 : List Nat := [0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f]
def g_19 : Nat := 0x107000000000f0f
def ep_19 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def nh_19 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xcccc0000cccc00
def s_20 : List Nat := [0x44440000444400, 0xc0c00000c0c00, 0xcc000000cc00, 0xcccc00]
def g_20 : Nat := 0x4040000044c00
def ep_20 : Nat := 0x480000000000000000000000000000000000000404000004080000000000000000000004040000044000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def nh_20 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff00ff0000000000
def s_21 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_21 : Nat := 0x100150000000000
def ep_21 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xffff000000000000
def s_22 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_22 : Nat := 0x117000000000000
def ep_22 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_12, s_12, 4, g_12), (m_10, s_10, 4, g_10), (m_9, s_9, 4, g_9)]
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_22_1 (Nat.sub p 32)) (cc_22_0 p) (Nat.blt p 32)
def hc_22_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_22_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_22 : Nat → Nat := fun p => Bool.rec (hc_22_1 (Nat.sub p 32)) (hc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 43 bds_22 (dagTraceF m_22 s_22 6 f_22) (cur_22 0) (nh_22 0) s_22 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 ch_22 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 43 ch_22 = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 7 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_12 (kn_cons lb_10 (kn_cons lb_9 (kn_nil))))) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xffff00000000
def s_23 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_23 : Nat := 0x155700000000
def ep_23 : Nat := 0x4200000000000004020000000000001002000000000000155400000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_23_0 p) (Nat.blt p 32)
def hc_23_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_23_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_23_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_23 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_23_2 (Nat.sub p 64)) (hc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 64 (dagTraceF m_23 s_23 5 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 64 bds_23 (dagTraceF m_23 s_23 5 f_23) (cur_23 0) (nh_23 0) s_23 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 ch_23 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 64 ch_23 = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 64 → ch_23 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 64 → ch_23 i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 6 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xff00ff00000000
def s_24 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_24 : Nat := 0x17005700000000
def ep_24 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f0f0f000000000
def s_25 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_25 : Nat := 0x10105000000000
def ep_25 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xf0f0f0f00000000
def s_26 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_26 : Nat := 0x107050700000000
def ep_26 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xcccccccc00000000
def s_27 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_27 : Nat := 0x4044400000000
def ep_27 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x3333333300000000
def s_28 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_28 : Nat := 0x113111300000000
def ep_28 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def nh_28 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x5050505050505050
def s_29 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_29 : Nat := 0x10105010105050
def ep_29 : Nat := 0x1000400000001040000040400010004000000000000000000000000000101000101000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x1212121212121212
def s_30 : List Nat := [0x202020202020202, 0x12001200120012, 0x121200001212, 0x12121212]
def g_30 : Nat := 0x12101210121212
def ep_30 : Nat := 0x1000020000001000000002000012000200020000000000000000000000000000000000000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_30 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_30 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 10 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 10 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 10 ch_30 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 10 → ch_30 i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x5555555500000000
def s_31 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_31 : Nat := 0x115155500000000
def ep_31 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_10, s_10, 4, g_10), (m_5, s_5, 4, g_5), (m_4, s_4, 4, g_4)]
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def hc_31_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_31_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_31 : Nat → Nat := fun p => Bool.rec (hc_31_1 (Nat.sub p 32)) (hc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 43 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) (nh_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 ch_31 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 ch_31 = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_10 (kn_cons lb_5 (kn_cons lb_4 (kn_nil))))) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x3030303030303030
def s_32 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_32 : Nat := 0x10101010103030
def ep_32 : Nat := 0x1000202000001000000020200010000000000000000000000000000000000000000000000010101010100000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xcccc0000cccc
def s_33 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_33 : Nat := 0x44400004c4c
def ep_33 : Nat := 0x480800000000000000000000004000000000000004000000080800000000000000000000044400004040
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x3333000033330000
def s_34 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_34 : Nat := 0x113000011130000
def ep_34 : Nat := 0x1000000000000000000000000012000000020000010200000002000000000000000000000110000011100000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x5555000055550000
def s_35 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_35 : Nat := 0x115000011150000
def ep_35 : Nat := 0x1000000000000000000000000014000000040000010400000004000001100000111000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x5500550055005500
def s_36 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_36 : Nat := 0x100150011005500
def ep_36 : Nat := 0x1000400000001400000044000000000000000000010004000000000001001000110000000000000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xff000000ff00
def s_37 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_37 : Nat := 0x150000007f00
def ep_37 : Nat := 0x6a0000000000000000000000000000000000000004000000080000001000000020000000150000004000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xff000000ff
def s_38 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_38 : Nat := 0x570000007f
def ep_38 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x105000007070
def ep_39 : Nat := 0x602000000000000000000000004000000000000000000000000000001000000020200000105000004040
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xaaaa0000aaaa
def s_40 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_40 : Nat := 0x200002a2a
def ep_40 : Nat := 0x2a2800000000000000000000000200000000000000020000080800000002000020200000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x3300330033003300
def s_41 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_41 : Nat := 0x100110011003300
def ep_41 : Nat := 0x1000220000001000000022000000000000000000010000000000000000000000000000000100110011000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xcc00cc00cc00cc00
def s_42 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_42 : Nat := 0x40000004c00
def ep_42 : Nat := 0x48000000040000004c000000000000000000000004000000080000000000000000000000040000004000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xf000f000f000f000
def s_43 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_43 : Nat := 0x100010007000
def ep_43 : Nat := 0x1000600000001000000060000000000000000000000000000000000000001000100020000000100010004000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8)]
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_43_1 (Nat.sub p 32)) (cc_43_0 p) (Nat.blt p 32)
def hc_43_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_43_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_43 : Nat → Nat := fun p => Bool.rec (hc_43_1 (Nat.sub p 32)) (hc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 43 bds_43 (dagTraceF m_43 s_43 6 f_43) (cur_43 0) (nh_43 0) s_43 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 ch_43 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 43 ch_43 = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 43 → ch_43 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 43 → ch_43 i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 7 :=
  lowerDagV5 (kn_cons lb_17 (kn_cons lb_6 (kn_cons lb_7 (kn_cons lb_8 (kn_nil))))) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xf000f000f000f00
def s_44 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_44 : Nat := 0x100050001000f00
def ep_44 : Nat := 0xa000000040000000e000000000000000000000000000000000001000000010000000100050001000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_44 : Nat → Nat := fun _ => 0
def f_44 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_44 : Nat → Bool := dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 1 (dagTraceF m_44 s_44 3 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 1 bds_44 (dagTraceF m_44 s_44 3 f_44) (cur_44 0) (nh_44 0) s_44 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 1 ch_44 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 1 → ch_44 i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 4 :=
  lowerDagV5 (kn_nil) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xcc00cc00cc00cc
def s_45 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_45 : Nat := 0x400440004004c
def ep_45 : Nat := 0x800000040000000480000000000000000000400000004000800000000000000000004004400040040
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff00ff
def s_46 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_46 : Nat := 0x17007f
def ep_46 : Nat := 0x680000000000000000000000000006000800000000001200200000000000140040
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_3, s_3, 4, g_3), (m_13, s_13, 4, g_13), (m_15, s_15, 4, g_15)]
def cc_46_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_46_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_46 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_46_1 (Nat.sub p 32)) (cc_46_0 p) (Nat.blt p 32)
def hc_46_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_46_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_46 : Nat → Nat := fun p => Bool.rec (hc_46_1 (Nat.sub p 32)) (hc_46_0 p) (Nat.blt p 32)
def f_46 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 43 bds_46 (dagTraceF m_46 s_46 6 f_46) (cur_46 0) (nh_46 0) s_46 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 ch_46 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 43 ch_46 = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 43 → ch_46 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 43 → ch_46 i = true := nj_46_1
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_3 (kn_cons lb_13 (kn_cons lb_15 (kn_nil))))) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xf0f0f0f
def s_47 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_47 : Nat := 0x1070f0f
def ep_47 : Nat := 0xe080000000000060000000000000000000000000000010200000000000001040000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xcccccccc
def s_48 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_48 : Nat := 0x44c4c
def ep_48 : Nat := 0x4c480000000000040000000000000004080800000000000000000000000000044040
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xaaaaaaaa
def s_49 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_49 : Nat := 0x22a2a
def ep_49 : Nat := 0x2a280000000000020000000000000002080800000000000220200000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xf000f000f000f0
def s_50 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_50 : Nat := 0x10005000100070
def ep_50 : Nat := 0x2000000040000000600000000000000000000000000000000000100000001000200010005000100040
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x5500aa005500aa00
def s_51 : List Nat := [0xaa000000aa00, 0x1100220011002200, 0x5000a0005000a00, 0x5500aa00]
def g_51 : Nat := 0x100000011002a00
def ep_51 : Nat := 0x10002a0000000000000000000000000000000000010000000000080001000000110020000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14b99100f 4 15 2 3 9 511 11 2047
def nh_51 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_51 : Nat → Nat × Nat := unpackForestF 0x32ec880f 1 9
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 3 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 3 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 3 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 3 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x1111222211112222
def s_52 : List Nat := [0x222200002222, 0x101020201010202, 0x11002200110022, 0x11112222]
def g_52 : Nat := 0x111000211112222
def ep_52 : Nat := 0x1000222000000000000000000010000200000000010000020000000000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x1a4471b4371343927d8d5ed5949d1540f 7 127 3 7 6 63 10 1023
def nh_52 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_52 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 10 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 10 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 10 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 10 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x4444444444444444
def s_53 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_53 : Nat := 0x4044400044444
def ep_53 : Nat := 0x400000000440000044400004004000040000000404000004000000000000000000000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x1111111122222222
def s_54 : List Nat := [0x22222222, 0x101010102020202, 0x11001100220022, 0x111100002222]
def g_54 : Nat := 0x111111100022222
def ep_54 : Nat := 0x1000000022200010000000020000010000000002000000000000000000000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0xd2440c34d0c309343924cf626af2d592906842c00f 7 127 3 7 9 511 13 8191
def nh_54 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 10 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 10 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 10 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x5a5a00005a5a
def s_55 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_55 : Nat := 0x105200005a5a
def ep_55 : Nat := 0x4a0800000000000000000000004200000000000000000000000000001002000000000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1ec351f4250f42b27d8d5ad5951d1540f 7 127 3 7 6 63 10 1023
def nh_55 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_55 : Nat → Nat × Nat := unpackForestF 0xfa75fa1b4ca5d5a2b0aa0f 3 6
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 10 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 10 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 10 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 10 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xc0c0c0c0c0c0c0c
def s_56 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_56 : Nat := 0x4040400040c0c
def ep_56 : Nat := 0x8080000040000000c080004000000040000000000000000000000000000000000000004040400040000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_56 : Nat → Nat := fun _ => 0
def f_56 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 1 (dagTraceF m_56 s_56 3 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 1 bds_56 (dagTraceF m_56 s_56 3 f_56) (cur_56 0) (nh_56 0) s_56 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 1 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 1 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 4 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x1122112211221122
def s_57 : List Nat := [0x22002200220022, 0x102010201020102, 0x112200001122, 0x11221122]
def g_57 : Nat := 0x102110211021122
def ep_57 : Nat := 0x1000002000001000000000200000000000000000010200020002000000000000000000000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
def cur_57 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_57 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_57 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 10 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 10 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57 : treeBlockF 0 10 ch_57 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 10 → ch_57 i = true := fun _ h1 h2 => treeBlockF_at nb_57 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x5555555555555555
def s_58 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_58 : Nat := 0x115155511155555
def ep_58 : Nat := 0x1000400000001440000044400014004000040000010404000004000001101000111000000000000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x3333333333333333
def s_59 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_59 : Nat := 0x113111311133333
def ep_59 : Nat := 0x1000222000001000000022200012000200020000010200020002000000000000000000000110111011100000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_8, s_8, 4, g_8), (m_54, s_54, 5, g_54), (m_52, s_52, 5, g_52), (m_57, s_57, 5, g_57), (m_30, s_30, 5, g_30)]
def cc_59_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b2ac2b099660946509060480200801b56c1b06c1b06499064145501405014048920480d507001 0xfa443c0910b5e40d68eb5238958d95632970bb5c20d34c34510934b24528d749a5d2457050360409872341a4d0845e1f168645216d5850560c910292410d783b5a08d481a560415a034f78d1dba4f6691d714f5451d11373449ca84f2211c48370209c001f 10 1023 4 15 11 2047 18 262143
def cc_59_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441dae870b81b2bc5c2e1709548225108132180c0601e8e070381c0a85028028000000 0x3f4b9f15d909afa174b06bd84ce4a642537a28a404de022ecd7352bae125d02e8609724b9835ca5a6e2d16149b7a45b5aed8976326cd926ac2e4e8d260694c5ea22d4b14a46ad1956 9 511 3 7 11 2047 17 131071
def cc_59_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc29a21100 0x884c854c534d8745204d8245 6 63 3 7 9 511 16 65535
def cur_59 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_59_2 (Nat.sub p 64)) (cc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_59_0 p) (Nat.blt p 32)
def hc_59_0 : Nat → Nat := unpackHintV5 0xed09ca437c66c8cbb797602e815d00b90546b28c05180a3010cea180430084090411e883a0c6e18a2e944028804f089a111481f8c391838e801c0000 0x3fd3d13fdff0d555005103c000141540003e20019660000880f00fff13d3df7fc905550001103c43ffd0f53fdff2555400001440f055550410041000 15 32767 6 63
def hc_59_1 : Nat → Nat := unpackHintV5 0xd000d000af42af00ae02ae00ad029530950095009500744274007302730072025a305a005a005a00384438003800360434042c10260c200c023c020002000004 0x5b6d5fb555550c484155557dd754015d5555d757d4312150550f30c000004d4d30c0f0300000fff1f43df7fc341554440f10000f 16 65535 7 127
def hc_59_2 : Nat → Nat := unpackHintV5 0xd00c82c80c02030000 0x55fb6d555500 12 4095 6 63
def nh_59 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_59_2 (Nat.sub p 64)) (hc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_59_0 p) (Nat.blt p 32)
def f_59 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 2 3 bds_59 69 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 2 3 69 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 32 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_1 : treeBlockF 32 64 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_2 : treeBlockF 64 69 ch_59 = true := by decide +kernel
theorem nj_59_1 : ∀ i, 0 ≤ i → i < 64 → ch_59 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_59_1 h1 h2)
theorem nj_59_2 : ∀ i, 0 ≤ i → i < 69 → ch_59 i = true := block_join nj_59_1 (fun _ h1 h2 => treeBlockF_at nb_59_2 h1 h2)
theorem nc_59 : ∀ i, 0 ≤ i → i < 69 → ch_59 i = true := nj_59_2
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_8 (kn_cons lb_54 (kn_cons lb_52 (kn_cons lb_57 (kn_cons lb_30 (kn_nil))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xcccccccccccccccc
def s_60 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_60 : Nat := 0x4044400044c4c
def ep_60 : Nat := 0x48080000044000004c480004004000040000000404000004080800000000000000000004044400044040
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_33, s_33, 5, g_33), (m_42, s_42, 5, g_42), (m_45, s_45, 5, g_45), (m_48, s_48, 5, g_48), (m_56, s_56, 4, g_56), (m_16, s_16, 4, g_16), (m_13, s_13, 4, g_13)]
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b0a0e80a02177c9f0785e0691a0681a05cd705856054550505405014035cd0340c1288a006401 0xe9497931281eb15199497141d9394131d036181e912b61235a50b4515242a94e41429c52935e895e5a5069445c507c5e7452635e5252495e4152393520342b4f1b43e34fcb43c24eba42a143813b3133101e0812001f 10 1023 4 15 11 2047 16 65535
def nh_60 : Nat → Nat := unpackHintV5 0x20d077a325e5077861dbcca62d8d58665443951004a54126854901520873df48f5053bc30ef003a828e28f36844d68733e38cc07285589e8527a00998a17dd42f60001780000 0x10c585c5800e1cab5800072e2c0b8b001c3850000e01000c631802346a0000004c00002aa001ebd7b300000040f00bdd0027a05d15ae18e040002f70eb7d2dd582d618e56a70e5ef72e3bdeefbdc1d0c3de7d2ad6e0b3e18c72b53872f7380e613c70e415555381ce739e18e000000070e00055550000000100610e1c82a36003872061c4 18 262143 7 127
def f_60 : Nat → Nat × Nat := unpackForestF 0xe9490b4fd139d0360b430a4e0a42ac51a94e09438c528b5e895e093b3c5e3c5269443b5e5c503a52395e3952393509331b4f20341b43081e0812001f 5 11
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 3 7 bds_60 30 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 3 7 30 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 30 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 30 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_33 (kn_cons lb_42 (kn_cons lb_45 (kn_cons lb_48 (kn_cons lb_56 (kn_cons lb_16 (kn_cons lb_13 (kn_nil))))))))) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xff00ff00ff00ff
def s_61 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_61 : Nat := 0x1700570017007f
def ep_61 : Nat := 0x2800000040000000680000000000000000000600020006000800120002001200200014005400140040
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 7, g_46)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_46 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xf0f0f0f0f0f0f0f
def s_62 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_62 : Nat := 0x107050701070f0f
def ep_62 : Nat := 0xa080000040000000e080006000200060000000000000000000001020002010200000104050401040000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 5, g_26), (m_2, s_2, 4, g_2), (m_44, s_44, 4, g_44), (m_56, s_56, 4, g_56)]
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0x4080e5c3862c0681 0xd2e3d73e9f747927a91cc6e01f 7 127 3 7 10 1023 13 8191
def nh_62 : Nat → Nat := unpackHintV5 0x3287ca03005b21ec80a61a8820144000 0xe3ee2fcdd3a5555550040000100 14 16383 7 127
def f_62 : Nat → Nat × Nat := unpackForestF 0x3a7e970e8e64f7ae191cc6e01f 3 10
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 8 (dagTraceF m_62 s_62 6 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 8 bds_62 (dagTraceF m_62 s_62 6 f_62) (cur_62 0) (nh_62 0) s_62 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 8 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 8 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 7 :=
  lowerDagV5 (kn_cons lb_26 (kn_cons lb_2 (kn_cons lb_44 (kn_cons lb_56 (kn_nil))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xffffffff00000000
def s_63 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_63 : Nat := 0x117155700000000
def ep_63 : Nat := 0x1440000000000016004200000000010604020000000001121002000000000114155400000000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_31, s_31, 7, g_31), (m_21, s_21, 5, g_21), (m_28, s_28, 5, g_28), (m_24, s_24, 5, g_24), (m_27, s_27, 5, g_27), (m_25, s_25, 5, g_25), (m_26, s_26, 5, g_26), (m_23, s_23, 6, g_23)]
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3230cd11d30791092028d3e3fe8ef637b8ce93f94ee13764cd52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_63 : Nat → Nat := unpackHintV5 0xab9f09c9f08e2e785f83762fd687db5d0b74fed24906e3cfc12f4db23db716bd20fd6e03cc10003c00000 0xaaaaaab5ad554637ec635ac631aaac635aceb9675cf9cde2000000000000aaaaa31bf6318c6aaaa318c6b1aa8c631bdef78c638671c2000000000000aaaaaa318d546358c6318c6f5519c70c6386318df39bc400000000000155554635ed546318d6b5ac40000016002aaaaaad6318c6f55555ad6318d55631adef7bd675cb3ae1000000000165c001555556a5558c6b39cef3cce7555876c63a18c678f08000000000002aaaa8c631aac3b75554aaab0e9f54eaa1000000000000555555a9547318c631bc6318d546338c750e3c784000000000001555546318d561dbaa10000000085555558c6b555aa87552aaac7a7d53aa84000000000008b82aaabdef7aaaa9d6719c673d4aaa78f4fb673d1ce71000000000000555559be6f55aa9f6ea955565d43a8f542000000000000aaaaaa739c6719d6ab37cdf52a9e3c739ce7a9f08000000000002aaaa9ce73aad547b62000000010aaaaaf7bdeaab55553e55559750ea3d50800000000001170555555100000000 20 1048575 8 255
def f_63 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 16 (dagTraceF m_63 s_63 8 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 16 bds_63 (dagTraceF m_63 s_63 8 f_63) (cur_63 0) (nh_63 0) s_63 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 16 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 16 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 9 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_31 (kn_cons lb_21 (kn_cons lb_28 (kn_cons lb_24 (kn_cons lb_27 (kn_cons lb_25 (kn_cons lb_26 (kn_cons lb_23 (kn_nil)))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xffff0000ffff0000
def s_64 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_64 : Nat := 0x117000011170000
def ep_64 : Nat := 0x1000000000000000000000000016000000060000010600000006000001120000111200000114000011140000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22)]
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def nh_64 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 1 1 0 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_64 g_64 ep_64 1 1 bds_64 0 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_22 (kn_nil)) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xffff0000ffff
def s_65 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_65 : Nat := 0x155700007f7f
def ep_65 : Nat := 0x6a2800000000000000000000004200000000000004020000080800001002000020200000155400004040
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 6, g_23), (m_39, s_39, 5, g_39), (m_37, s_37, 5, g_37), (m_33, s_33, 5, g_33), (m_38, s_38, 5, g_38), (m_40, s_40, 5, g_40), (m_55, s_55, 5, g_55), (m_16, s_16, 4, g_16), (m_11, s_11, 4, g_11)]
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x10974d1ab35d246c9168dab1256768ea91c51b801f 6 63 2 3 11 2047 15 32767
def nh_65 : Nat → Nat := unpackHintV5 0xdf00a378a300706670006a8b62113658006c0000 0x6358d6318f6bd1dce78f3a19c0000146f1ad5abb5e73c77d270000076c3d8e5bd635468d54f1ea90000058c6b51a9e3c38f31d000000000 16 65535 7 127
def f_65 : Nat → Nat × Nat := unpackForestF 0x425d168ecd74523945a26ac495851b801f 4 11
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 3 7 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 3 7 9 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 9 ch_65 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 9 → ch_65 i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_39 (kn_cons lb_37 (kn_cons lb_33 (kn_cons lb_38 (kn_cons lb_40 (kn_cons lb_55 (kn_cons lb_16 (kn_cons lb_11 (kn_nil)))))))))) rc_65 nc_65 (by decide +kernel)

def g_66 : Nat := 0x117155711177f7f
def ep_66 : Nat := 0x10006a280000144000006e680016004200060000010604020006080801121002111220200114155411144040
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43), (m_64, s_64, 8, g_64), (m_63, s_63, 9, g_63), (m_60, s_60, 8, g_60), (m_65, s_65, 8, g_65), (m_46, s_46, 7, g_46), (m_58, s_58, 8, g_58), (m_40, s_40, 5, g_40), (m_62, s_62, 7, g_62), (m_59, s_59, 8, g_59), (m_22, s_22, 7, g_22), (m_11, s_11, 4, g_11), (m_31, s_31, 7, g_31), (m_35, s_35, 5, g_35), (m_2, s_2, 4, g_2), (m_47, s_47, 5, g_47), (m_36, s_36, 5, g_36), (m_49, s_49, 5, g_49), (m_16, s_16, 4, g_16), (m_29, s_29, 5, g_29), (m_32, s_32, 5, g_32), (m_53, s_53, 5, g_53), (m_23, s_23, 6, g_23), (m_21, s_21, 5, g_21), (m_56, s_56, 4, g_56), (m_50, s_50, 5, g_50), (m_6, s_6, 4, g_6), (m_34, s_34, 5, g_34), (m_57, s_57, 5, g_57), (m_39, s_39, 5, g_39), (m_55, s_55, 5, g_55), (m_8, s_8, 4, g_8), (m_25, s_25, 5, g_25), (m_45, s_45, 5, g_45), (m_54, s_54, 5, g_54), (m_51, s_51, 5, g_51)]
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xbe0df0291b441a00d0028013c19c0cd066033009804c0260120490048024011437653b01d80ec07603b01d80ec076033200e4001 0x7da808f5bc45ac621c6f1062f87f15c356c418b4a0b1210505bc242be10157078a383a4b40e28c0694604cbf0245f8112fc0817e04da7824d2c1168e0834303ab781b58c0c8c40dd6f06ab18331bc188c60bc5f05a2d82b15c148a60796e02ca30135bc08ac603c6f01a3180b17c048b601c5700a29e9517f488b7a2457d0a29e70d7f376b79a357ca9a9e50d3f2669792347c89a1e2a97f144b786257c1929dfa93efb49779247bbd21dc88feda4776aa37b1119d2c57e7b2b72b157888a9bf853dd6296cd1475bca1aba4fd482769813749099a2a4bcfe256621272e89196217c910ae4104f1c0238c60fc5506e2482f0701381407c0102e0003f 13 8191 6 63 11 2047 21 2097151
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x844060100793c1d2e870ad960b05821900803c9e09c48241206630180c036180c0600600 0x1f255f136f69b3748dba66f62ff515ed685ca5fe12bec91f4adf9d63c937545be62bf1157bd2a615beeac76b62a4b7ca57e12af5b68a9a55290a76b1334a952146d8226950a42 9 511 3 7 11 2047 17 131071
def cc_66_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x84421f4f878bc1d2e870ad960a95428540a04ca61229044978b043200ac5021100482002 0x2f35fbad5edc68b3162bc60c35befd63b918ad16fb057eb157a899292549e9926a54969b29d6fa358e826e9c5be615f9455e436868d2982428cd619b4a5c90a23687adca135874dca0360 9 511 3 7 11 2047 18 262143
def cc_66_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xf8f1f0e2e0e0cbc8c8bab8b1b0a977706968685a585851504948411610090801 0x3f568f31b3e36cf51bbcb62ec5bfbd68ecd77a36ce5183fd62fadbfdb63f0d77a96fe64ff8937ded936c54d8d534b64ced532b6cdd5bf5d63d4dbb416fcc57f2157c51a30458 8 255 3 7 11 2047 18 262143
def cc_66_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2348c23084a1080600789e0745d07051b44110405003c4f0348d0340b22c0a12809109c2008002 0x142d3e81a5cfb479e687391f26dbeccb4398ae12edf655be49c70b06db5cd3eb1a5d5347a7687445b274b04d14f9628f284fe489bc7c648d6a91758a20b7c4c648868b0cd52122c4846e8e6df18d8e29a2c396f8527f064de05a5c0347 10 1023 4 15 11 2047 19 524287
def cc_66_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8862084610715c0701c0701c0701c07014844d1038ce02ccb020c802004410040100400100000000 0x17e5f2f4aa6156fc0ad77d59ef2b1dd96eb969f70d2edda3db343b529f6851ecc9fd9137a96853653e5ca3d7c7ca62f9425c2b5be5297ca02e1575c290be4f970a98f950df28cbe4f170a647f4a8ee911bd1a33 10 1023 4 15 11 2047 19 524287
def cc_66_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0a8098a60982429024081200801e2781e06cdb06c1b060d174411044110440c50a8200441000400 0x359b96fb60dd4ab9e91f4532ed255d84dbae9b3552ee7245d58cba91574a36e8c5dcd48d9f9e73a3366a66dcad3b7587662feb457d34bfa095f3123e556fc9ad79159f1eb1e326efbadff15afceb3f7d63ed8dfd319f9e2fef457cb6c58ad2b0cb260954 10 1023 4 15 11 2047 19 524287
def cc_66_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x86a10841e3781e0691a0681a0609535414150104400f13c0f0348c1300a2244811c4611805110404 0x89d6f88d6b87d6786d6385c6f84c6783c5f82c578196e7f9467ec657e3686534a7d4556e3707cb5864b4a7b24b7aa477bc7d7a3706434a7935078c556db707835863b4a773687625b75a53753706cb727435872a787126472b7c70a607126c70b747326f7226b71a6770263 10 1023 4 15 11 2047 20 1048575
def cc_66_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe2e0d2d0d0d0d0d0b47f786a6861605250494841403938313022201918181803 0x8fa7c8c0248ea548b8248d45f8cc5b8c4578bc539156f9056b8f5678e5638da6e0e8358b0248a16481146891548817c8094687154861648517c841548217e8316c823478156f80d6780462 8 255 3 7 11 2047 20 1048575
def cc_66_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x98251942509421484201801f17c1e1781d13f8f0384e0344d0340d028ca024490114400882000800 0x9f3559ed699e5619db5f9d3579c4689b4709a45899460a356fa256ba0d679fd639cc629ba6f9aa6799a5f98a575906f490674185f388570f027979649695495c7c9537c9497c939549756f9656b94567935639296e91a648d02490a548c824 10 1023 4 15 11 2047 20 1048575
def cc_66_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x951ba6c1a168191641905c9705856054550505405012248120409001e47018460108401002208002 0xb1c5fb145bb0c57afc53b6d6fb5d6bb4567b2d63b236e5986f4a0674285f39857af034ae164ad154ac37cab97caa954a9964a897ca7d7ea7154a6672a596cadd6facd6bab567aa563a936fa8367a6b5fa5357a496ea3c689ec70a2c58a1c70a127c9e470a0458 10 1023 4 15 11 2047 20 1048575
def cc_66_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4690a42459024088a208821184201801f1694ce300a2280822008014c4110013040100401004001 0xb9144bf47ebeb7ebc97eb8954be134bd23bbca33b9230ba470b936ebbc62bb36abaa6fb9a67b8a31cc46fcb46bc9467c7c63c6b6fc5b6bc4b67c3363c1b4fc034bbfb47bdb43bc16eb8146b7364b1834b6354b1034b537cb4a7cb0834b0034b3c54b3354af834b0344 10 1023 4 15 11 2047 20 1048575
def cc_66_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc1706e054456aa8140a80484901202403c6780f01a234050ca0121240388700e0144280500620c018001800 0xcf160d025fcfa5bcea57ce253e8d62e7b6fe5b6be3b67e1363dfb5ddda6fdc26bda267d7a63d6a3fd523bd4a37d0a335a06f4b067cd85c3203f2b0372502f10027cc964bb154cb944cab7cca370c997cc8944c8044bf342c7164ba946c6134c517cb9946c4134c3834c2c7ec2144c137ebd17ec0934 11 2047 5 31 11 2047 20 1048575
def cc_66_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8d8d1b4b0b0a2a0a0a08b888888816b68616060525050494140323029050000 0xd2a30df568deb65de35dd2232dd670dca6cdbd70db37ddab5dd8950d9e70d926cd8024d736cd6672d5a6cd4254d2b6ed2b5cd1a5cd1a6ed3e72d346cd237ed126c10835 8 255 3 7 11 2047 20 1048575
def cc_66_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4341c4f10c4310c42e383a00802007896858142501314c103401003c4b42c0b02c0a11545014005 0xef36ef047eefb7eee934ed462eca6fec267fd46ffc46bfa467f8c63f7b6ff6b6bf5b67f4363f2b4ff134bf0b47ee343ed96eeb946ea252e9a50e6b69e3361eab4be9347dd269d9a61d623bd3a33e8568d005ce7356e6e70e636ccf86ccf05ce5570e4a7ce4270ce85ce2250e3670e046ce2b6cce06ce1834e0c6ee0362de26fdaa67d3231 10 1023 4 15 11 2047 20 1048575
def cc_66_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xb014114a2804c298120a40480900f19e03c0688d0143280484900e21c0380510a01401883006004408000800 0x802bf3fedf9fe4a8128358863743edbe1d6d70cb67859b1c28d16104df0726b82933c0e98e0547f0123b8051bbfa8ccb50de4d0671981f8b00dc4c05e120277ecb23f2511f76f8fb3707d4be3e6511f2088f03427c0b23b2519ee268f617c760a33d44d1e9068f3c7e798a23c8df9e3268ef134 11 2047 5 31 11 2047 21 2097151
def cc_66_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a9a8a8a893909082806b6868684c48414040402b28281a1811101002000000 0x21e6a90e47c86d3e4349c2186a90b834856b14229be0b4cf09c64849b2c22d15ff46507a548363e418df60b68b04a548201240cd5204afd01a54 8 255 3 7 11 2047 21 2097151
def cc_66_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xb83702e0563a8350290ce29c128a5048190118630460844f89f03e07c0f05e03c0780f01e02c80e608810001 0x47e4d23dce11e16c894a34724d2396dd1d47e8e09a448552362891a1348c09a460dba2f4af18c7e8b89a4540d22cadf15d638a5b1450d6a274df1325f8952bc488f655adf2a56394e37ca318e4f8bf26c5b92a2bc9114e446df21363901afc7cd6e3b6af1bb538d5a7c66d2e3268f16b4388ca34088ee0046710464 11 2047 5 31 11 2047 21 2097151
def cc_66_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xac2b0a4a90a4290a42545f961545505052248102400e2380d128ca024490240810d4300842000800 0x4bd1f25d4f92da3f9691dcb28de584673d36d9e1a7cecd2e7268f37b439ad27cd292e6648f322439891fcc08ee5f46f2e23395c3645851a2b28d150448a4aa4a4112476ff281548a0aa49c512464df26670915bfc965b2492892316c91e2fc8b15e3a6a518b4289ca34860d2412a913146 10 1023 4 15 11 2047 21 2097151
def cc_66_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x982519418d511404892040900400e2308c030093240902406318051140500c830084200441000400 0x27e2694a45fa4a2dd1f15e8d8a745b5fa25add0cd5e846a74134fa01a5cfed1e7d6873e1469c5a14da93e6748f2f2319e63e4b61f2776f92d07c9d527ce891e73ae12c87c9c63e4e0df2580f93747c9b5becd8d166a4f93457099dbecca9f2636f930a7c 10 1023 4 15 11 2047 21 2097151
def cc_66_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8148690501a01402804a3332600b0960282500a0102200384700c1180284500a00c41802084004208000800 0x29e6c94e264a65bf5309902906b6146fb0231d7edbebd6c75cb55adda7d6ad2eb368f58b43ab537d5698ea749f52a4ba8923d3e90e9d47f4da3ba691bd2e8cc8709e3a8471a01f8b40dc4e05e14027a54aa52651291ce14816ca38a25185528a26944670a1cb650a4d28328940934 11 2047 5 31 11 2047 21 2097151
def cc_66_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8cac8c8c89e98919089887a78717070704d48414040402b2821202012101002 0x575192be0695e45faee29d74d4ab04bf54a4fa8d23d71192b66c95a568ab93fd64d92b06cb57b55ab9a3d4290a9946556024aaa32552d96a868b53264a92b4546d96a16fd50264 8 255 3 7 11 2047 21 2097151
def cc_66_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x92324240c6273ae41c8390720b7168294520a41392704a48c901a004007c4bc1702e04d02784004408001000 0x2df4f96ea54790a5b0450ee2adf7056bb7ab3db958edb4dd4d96fa00b5cc059e332c70115f788adb5455d802a76cd6fb62b5daf59ed6ac74d16f9fcb5cbe59e322c70095f784adb5255d7f2a765b7eb1d3e5a89903006b69454b452a59e9f2c64d96526e0bc12d92dfacd4a817035b29225971bec98c74c96f8c4b1bfe53de0296d21475f8a1d8f1b6c68caef94b5f4a1da75bed0ad767567b32b1d90dbac54dd4b96f9f4b5cb859e2d2c6fe95f770adb4255d7b2a616035af1b2d86d56bb6cb60b45 11 2047 4 15 11 2047 21 2097151
def cc_66_23 : Nat → List (Nat × Nat) := unpackCursorV5 0xfc34bd02f5bc2b4ac2a1a8291a42817a9c2701665815154141501314c130448f20b4200441000400 0x60b1bb036df80b67bfda2dfc98aa72df4596b9acb3c8058d4d27699937bf13754a5be892d7349678f8b1df4d1e882d31e9615309ddf15a2f6ae17a46ebe6b15eedbef56cf79b5da88b7d0c5ae662cf1d9635289da624dea12df1d163bc5b75e09ba9f2df4216b990b3c6e58eee6c976354ba9be5d1152e76a8f394b614a1ddb5beebad774d67b9ab1dcadba9d2df4116b988b3c6a58e052bef295b6b4abb0654ee34c970a54 10 1023 4 15 11 2047 21 2097151
def cc_66_24 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e38e08e08e08458408028007a35b05244e24e04c14c04c04824613493213013003002080ca0a10a0081080061060003 0x31b6cb8fb45b251963917f1b8a75795f848a7b7a51f198c923973c5eb455c5fe452e79046fc7a31e3adbf1a6ab8c34fc59a3de290ac84655696f910b1c2053def296dd947634a1aa44ed3726f0715f7b4adb7055d8b2a70614f6d8a3e251f31029f87943c3ab8626db71169f86b47828a7bd652db428ec49435409da6a4df0904984024c262fe1114eac0bf2185382027bd212db008ec3843c2eb7e1558efe6bd5596f908b1c0e57de82b6d7957618a9e0e0914f27782464c0a3e60158aa82df36167 12 4095 5 31 11 2047 21 2097151
def cc_66_25 : Nat → List (Nat × Nat) := unpackCursorV5 0xfe0fe0fe0fe0fc1fc0cd8c44bc4b449eb9e09a298194294094094092182866e6604ae4a038934218e180069060003000 0x6761b3418dfa0463cfe2de7d15f1d4df9ea57c0d27dee91ebf2df29963cf0ade7455e1f29efd14b73ca3b3050d0b25676927ce42b91c13c7d08e218270640f80e05e1d2befc15b72cabb2c54e1b27efb93b7249bb2a4ce1a29efb14b720a3b2850f2f6db9b26ccd53060293ef548f0c94f7d0a5b8e51d922868492b3a493e671932e06996834cc62a6580d32d6899745fcb229d7c17e520a70b84f7c825b8611d900879956fcc2b1e5edbabd2df28963858afbe256dc22aec79532302f8f615f2b0680c01f0180be531bb184df88a67adcb7d285ae782cf2796341c959ce49cb90de570671041382e07c0502f93b6ead4b7d245ae762cf269632e03795819c1603e02017a44b4c9858725ac58b26fc3533d665be8f2d739167928b1a0a4acde24e5b86f2a83387e09c1503e01817c8db75625be8d2d737967920b196c1bca70ce0a01f0080be38d97216ab65a32 12 4095 5 31 11 2047 21 2097151
def cc_66_26 : Nat → List (Nat × Nat) := unpackCursorV5 0xba48998426ad6625e45e040f327019000000000 0xccf62c866fb0d6f3f527d076fccb63d2f55c826fc2e63bb63fb8a3bb6637b4e33b096f955635b53f56d3b519374b9334892f44d2b3ed27309231b83f1843714c2f11c2706c1f02417b4a313e927d2745bae3fb823bb6237b42335ad3f5653b511374b1334812f4452b3e127301234ad313dd275a52f5612b509274a923d1f6dd1a6cd1660ba63fb7a3bb5e37b3a335a13f5593b505374a1334792f43d2b3cd272f923cc762c7e6fba23db056f59d3d3c5271b43dd036fcc363d0f45c7a6fc2a63b9a3fb723bb5a37b3233b016f951635953f5513b4fd37499334712f4352b3bd272f1231ac3f17c371442f114270681f02017 12 4095 5 31 10 1023 20 1048575
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_66_26 (Nat.sub p 832)) (cc_66_25 (Nat.sub p 800)) (Nat.blt p 832)) (Bool.rec (cc_66_24 (Nat.sub p 768)) (cc_66_23 (Nat.sub p 736)) (Nat.blt p 768)) (Nat.blt p 800)) (Bool.rec (Bool.rec (cc_66_22 (Nat.sub p 704)) (cc_66_21 (Nat.sub p 672)) (Nat.blt p 704)) (cc_66_20 (Nat.sub p 640)) (Nat.blt p 672)) (Nat.blt p 736)) (Bool.rec (Bool.rec (Bool.rec (cc_66_19 (Nat.sub p 608)) (cc_66_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (cc_66_17 (Nat.sub p 544)) (cc_66_16 (Nat.sub p 512)) (Nat.blt p 544)) (Nat.blt p 576)) (Bool.rec (Bool.rec (cc_66_15 (Nat.sub p 480)) (cc_66_14 (Nat.sub p 448)) (Nat.blt p 480)) (cc_66_13 (Nat.sub p 416)) (Nat.blt p 448)) (Nat.blt p 512)) (Nat.blt p 640)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_66_12 (Nat.sub p 384)) (cc_66_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_66_10 (Nat.sub p 320)) (cc_66_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_66_8 (Nat.sub p 256)) (cc_66_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_66_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_66_5 (Nat.sub p 160)) (cc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_66_2 (Nat.sub p 64)) (cc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 416)
def hc_66_0 : Nat → Nat := unpackHintV5 0xee0af0e93934e211cad6eacacb72dec1c26cbab1c4b12264aa31bca0a26499b1bc94c13c9180d08c41508900d081f9c27c696476717e70418c6a497e64d15e562baa46cbd83a4b2031ca20254b201d0212108320083a120051fa000014000000 0x8c8c8c8c1c1c1c3c1c1c1c8c1c0c1c6c1c1c1c0c000040b0b0b0f0b0b0b130b030b1b0b0b0b0307070b0b070707070707070707070b0000000001c0b0000000201d0741d074001021c1c1d41c1d4001caa0baaa0782eaaa800002021d6948c9c9c8c00002c2c2c2c2c2c2c2c0000000000b01d0741d074025075007aa0baa8000028016949c9c27002c2c2c3c2c2c2c2c0c2c6c2c2c2c0c02c2c2c02c0b02c0b00b02a1f271f1f1f07c0b070b42c1c2d02c2c2caa0baa8a000a0a1e0baa030303030f03870f0f03030f0f0f130f0f13131b1b06cbc4c031b1b030b0b0b0b0b0b0b02c2c2c030b0b030b0b0b0b55555555555544d50f544d1b5546d4f5540d51b54551150b4560baaaaa82e0ba80eaaa82eaa0b968755580c0c0c0c0c3c0e1c0c6c0c0c0c0c4c3c3c4c0c0c0c0c0c0c0c032f0302c2c2c2c0c0c0c0c0c0c0c030b0302c2c2c2d55555550341d5555513543d503540d50340d550353d551544542d1582eaa03aa80e03aaaaaa0baa82e5a1d556004c3c3c4c4c6cbc0cbc6c4c0c0f21c3c3c03c3c3c5c1702c0b02c2c02c2c02c0b00155555554505113543d51345d552f53d5503546d4151700542c1582eaa0b82eaaaa0baa2a0b0a82c5a1d556130f0f130003c870009c00c01b000000000000155540004400113543d503546d40000001414f000000560baa82ea800002820b00005a1d55603030303033b0303030f0303005c1700321c0c0c00c0c6c2c0b00c0300c0c00c2c001555555545051543d503540d50340d550353d54151700542c1582eaa03aa80e03aaaa2a0b0a82c5a1d5561b031b030000c87000ec00f006c000000000001555400044001543d503546d40000001414f000000560baa80ea800002820b00005a1d556171b1b0f170f1b3b1b031b03005c1700c0c0c0c0c00321c2c0b02c2c02c2c00c0b001555555545051543d51b53d551745d5503546d4151700542c1582eaa0b82eaaaa03aa2a0b0a82c5a1d55603030303000000c870ec00f000c000000000001555400044001543d503540d40000001414f000000560baa80ea800002820b00005a1d55650303030313030f031303130303032b032b03030301705c0321c0c031b0b02c0302c55555aaaaa951b031b03000321c04c0f04c1300ac2b006c0000055514aaa2895130f0f131317132b1b2b1b1717131b131b031b0301705c03030300c870b02c0b02c55555aaa0b82eaa95030303030000321c4c0f04c1300ac2b000c0000055514aaa289544c3c3c4c4c6cac0cac6c4c0c4c3c3c4c4c5cac2b171302c2c2c2c2c2c2c0b0b0b02c2c2c2c2c2c2c2d5555555555556aaaaaaaaaaaa96540c0c3c0e1c3c0c3c3c4c3c3c4c4c5c4c6c5d2c5c5c5c4c5c4c0c6c5c0c5c17142c0b02c0b154456a82e0ba2280c0c3c0e1c6c0c0c0c4c3c3c4c0c0c0c0c0c0c0c0c5d7c0c5c5c0c0c0c0c0c00c5c5c50302c0b02c550341d115aa88a130f0f13131303c5c1705c13131313031313131b130305500b02c0b02c000b0b00b0b0555514054514aaaa28aa082e0285527271717170f170f171703171b171717031705c1705c542c0b02c0b02c2c02c2c0015554151454452aaaaa280aa0a1549c9c9c9c2c2c2c2c2c2c2c2c2c2c2c2d55555555543d503546d51544542d1582eaa0baaaa0baa82e5a1d556030303030f03870f0f03030f0f0f130f0f1313131304cbc4c031b1b030b0b0b0b0b0b0b02c2c2c030b0b030b0b0b0b0707070f07070713070707070713071f070707070713071b0303071b070703030701c7c1c1c1c0701c2c1c1c1c0741d07075070750341d0741d0741daaaaaaaaaaaaa955a5a1c0c0c0c0c0c3c0e1c0c4c0c0c0c0c4c3c3c4c0c0c0c0c0c0c0c032f0302c2c2c2c0c0c0c0c0c0c0c030b0302c2c2c2c1c1c1c3c1c1c1c4c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1c7c0c0c1c1c0c0c0c0c1c071f07070701c070b07070701d0740d0340c0d0350303070750741d0741daaaaaaaaa0382eaaaa955a5a1c0130f0f1313131303131b130303c870f0f00f0f0f1705c0b02c0b0b00b0b00b02c000707070f07070713070707070713071f07070707071307170703071b0707070300717070700070b070700741d07075070750741d107041caaaaaaaaa8a0a155a5a1c4c3c3c4c000f21c0013003006c0000000000000707070f070707130703071b070707030000000071f007070000000741d0741d000101c002aaaaa0000a082c00155a5a1c0c0c0c0c0c4c0c0c0c3c0c0c01705c00c870303003031b0b02c0300c03030030b0000707070f0707071f0303030303030303030303030303071f030307070303030300717070700070b070700741d0340d0303503075107041caaaaaaaaa8a0a155a5a1c6c0c6c0c000321c0013003c01b0000000000000707070f0707071f0303071b070703030000000071f007070000000741d0341d000101c002aaaaa00022000556968717131b0f170f1b131b031b03005c1700c0c0c0c0c00321c2c0b02c2c02c2c00c0b0001c1c1c3c1c1c1c7c1c1c1c1c1c5c1c5c1c1c1c1c1c6c1c7c0c0c1c6c1c1c0c0c01c5c1c1c001c2c1c1c01d0741c1d41c1d40d07441c1072aaaaaaaaa2828556968703030303000000c8704c00f000c0000000000001c1c1c3c1c1c1c7c0c0c0c0c0c0c0c0c00000001c7c01c1c0000001d0740d034000407000aaaaa80008800155a5a1c9c9c9c9c2c2c2c2c2c2c2c2c2c2c2c2c1c1c1c3c1c1c1c7c1c0c1c6c1c1c1c0c1c071f07070701c070b07070701d0741d0741d0741d076aaaaaaaaa5569687aaaaa 24 16777215 10 1023
def hc_66_1 : Nat → Nat := unpackHintV5 0xb99812b4215eb3702cb1e064ab699ea5418a9ed19c9e003498f9429119f88ae18e8459a27dc9a47729a873190470e88c6cb90c66e17661e93e5ab9cc54b18250e0f4433b6a3c09cc36197c32a0de257b4a1da9f417699012f11e05cb4a000172 0x38704c0c3c0c021c0c0300000c0b002c2c0c0c0c0c0c0c0c0c4c4c0d1c0c0c0c00000d0741d07682e87aa28002e0b0b17870b80b0b0f0b00c000001d076a82e130f1b0f0f131b1300300c08700b02c0000b0b1b171313171b171b1313031b1b03000bc5c000741d0741da0ba1c2e0baa8a000b84c0c2c0c3c0c0c0c0c2f02c2c0c0b02d4c2c2c0c4c4c0c0c0c0c0c4c6c13570a00c4c0d0744c4c4c4e82e87aa282e0b82e0b030b0b131313132f06c0b0b0b0b0b02c6c02d4c2c2c0c0c0c0c4c4c4c0c4c4c130a01d0744c4c4c4c4c4e82e87aa282e0b82e03006c0c5c0530b000c6c6c0c4c0bc4c00b02c0000530b0b5713130004c4c0000741d04c4c4c4c4e82e87202a000b84c3c3c4c4c0f002c2c0b0b02c0b00b002c2c2c0c4c6c6c4c0c04c5c5c02a804c3c3c4c4c7c4c7c1f1300b0b04c1c4d1307136aa0ba1eaa28280aa0b0a82ea80c0c3c0e1c3c0c3c3c5c00000870130f0f131317131717171b174b13171303171b0302c0280741d0741d82ea82e0b88002e03030f03871b03030317000000c0b021c04c3c3c4c0c0c0c0c0c0c0c0c5c5c0c5d6c0c0c0c0b00a00d0741d0760baa0382e2000b84c4c4c4c3c3c4c4c4c4c0c4c6c4c0c000000000000000000004c3c3c4c4c1c4d13071344c4c4c4c0000a82e00082e0aa000082ea89c9c1700000000021c0017170f170f171717031717171b170300b0002807c9c7c7c7c00005c1c5d1707176a82eaa00800000082ea80c0c3c0e1c3c0c3c3c002c4c2c2c2c2c2c2c000002c0741d01e0baa0b82e080b80c0c3c0e1c02c4c2c0c2c0c01c1e0ba00b80c0c3c0e1c6c0c0c0c002c4c2c0c0c2c2c0c0000c002c0341d01e0baa0382e080b84c3c3c4c00002c2c2d4c4d4c4c0014c5c00000000004c3c3c4c4c7c4c7c004c4c4c4c02aa0ba1caa000a000020baa272700000b0b0b0b0b0b0b0b0b0000000000b07c9c7c7c7c002c2c2c2c001caa0baa800008082ea88c3c3c8c8c0f0bc2f02c0b02c0b0002d0b0b0b0b52303231b231b230302317231700aa090741d07441c01d070701c1d41c1d6aaa8a0a02a29a541c0c6c0c5c00000870130f0f1307070707171707172b07070703171b0302c0280f61c1d07070741d82ea81e0b88019a507031b03000b13070b0b0700000b03d870741c1c1c2c0782ea81e0b8219a548c3c3c8c1c1c1c0c1c6c1c0c8c0f01c1c01cbc0bc2f02c2c2c3c2c2c2c4c1c1c1c1c1c1c2c1c1c2c2c1c1c1c1c2c0c2c6c2c2c2c0c02c2c2c02c0b01c1c01c2c02c0b00b02a43d87070750707070741d10701c1c1c1d41c1d0b501d07072a82eaaa81e0baaa2800282875a9680c0c0c0c8c2300c0302c0b00c030008c4c8c3c8c3c8c4c0d03030303502317231700aa00741d903441c01d070701c1d41c1d6aaa8a0a02a29a48c0c3c0d45c00000870130f0f130303030303030303171703175b03030302c0280361c0d03070741d82ea80e0b880148c0c3c0d4002c4c0c2c2c0c00002c0361c0d030701e0baa0382e0850303030303230303030f0303548c2300c0300c0c00cbc02c2c2c3c2c2c2c4c0c0c0c0c0c0c0c0c0c0c0c0c0c0c2c0c0c2c2c0c0c0c0c02c2c2c02c0b00c0300c0c00c2c00b02a0741d40d870303503030710701c1d41c1d40741c1caa0baaaaaa0382e8a000a0a1d6946c0c6c0c8c2300c1b02c0b00c0b00b014c8c4c8c3c8c3c8c4c0c0d42d030302317231700aa00741d036441c01d070700c0d41c0d6a82eaa280a002a2a96941c3c1c8d45c0705c00000870130f0f1307175b07070707070707171703171b0302c02803030340d870741d82c1e0baa880141c3c1c8d41c2f0002c4c1c2c2c1c1c1c2d4c00002c03030340d87001c1e0b0782eaa0850707070f070707231b031b03548c2301cbc01c1c00c1b02c2c2c3c2c2c2c4c1c1c2c2c1c1c1c1c1c1c1c1c1c1c2c0c0c2c6c2c2c0c0c02c2c2c02c0b01c2c01c1c00c0b00b02a0741d0303030303540d8710701c1d41c1d40741c1caa0ba0782eaaaaa8a000a0a1d6948c8c8c8c00000000008c4c8c3c8c3c8c4c8c0c8c6c8c6c8c0c000000001d0741d07400001c0500aaaa00000a0068 24 16777215 10 1023
def hc_66_2 : Nat → Nat := unpackHintV5 0x839cbd40545e9f26410f241bc726dad377a6f1a20674c9b1d45e659d2d507895fb2b4a7322a50d0b2262a8f925a2ec8da14c42ad091ffa570efd40072795c34f9111966458baf4104eb3b2233d070dd2f3062930024932e0f34c5049cbf8189314000312 0x13030b030f03030313170305c0b0b0313130303030303131b280302c0b02c03130341d13131313a0ba1ea8a0b82e0b82c0c2c2c4c4c4c4c4c5c5c1702c2c0c0c0c0c4c4c4c0c4c4ca02c0b02c0b01d0744c4c4c4c4c4e82e87aa282e0b82e130f0f13131703c5c1705c0b0b0b03131b1b13030aa00b02c0b02c000b0b00b0b0130f0f13131f131f05c4c13071344c1c4d02c2caa82e87aa8a02a82c28a20baa270f0f271703c1705c0b42c2c2c2d4ac0cac6cac6cac0c2a802c0b02c0b0002c2c02c2c241d0741d10701c1d41c1d441caaaa280a8a2869549c3c3c9c1c1c1c0c1c6c1c0c2c2c2c3c2c2c2c4c1c1c1c1c1c1c2c1c1c2c2c1c1c1c1c2c0c2c6c2c2c2c0c5c0f01c1c01c5c05c172a0b02c07070070b00b02c0b0b00b0b00043d87070750707070741d070707075070742d441c1072a82eaaa81e0baaa0028287285a9680c0c0c0c5c1700c0315c4c9c3c9c3d8c4c0d0303030350aa00b02c0300c000b0b00b0b00741d903441c07075070751072aaa8a02a28a1a40c0c0c0c0cec0c0c0c3c0c0d50b0b0b0f0b0b0b1303030303030303030303030303030b03030b0b030303031705c0300c0303003170a82c0b00c0300c0c00c2c02c2c02c2c0001d0750361c0c0d40c0c1c1c1d41c1d441c1072a82eaaaaa80e0ba0028287285a51b031b031705c0305c7713270f270f7713030350b40c0c2a802c0b00c0b0002c2c02c2c01d0740d910700c0d41c0d441caa0baa82800a8aa285a50707070f0707073b1b031b03542c2c2c3c2c2c2c4c1c1c2c2c1c1c1c1c1c1c1c1c1c1c2c0c0c2c6c2c2c0c0c5c1701c5c01c1c00c172a0b02c070b0070700302c0b0b00b0b0000741d0303030303540d870707507075107041caa0ba0782eaaaaa800a0a1ca16949c9c2c2c2c3c2c2c2c2c0c2c6c2c2c2c0c5c1705c172a0b02c0b02c0b0b00b0b0001f271f1f1f0b070b42c1c2d05c5c02c2caa0baa800a0a1ca20baa030300000c3c0c003c3c00000000000000000008c3c3c7c8c1c7d23071f40c6c6c0c0002aaaaaaa800002a80c0c0c0c3c0e1c3c3c0c0c3c3c3c000000000000000000013003c01306c001b00003006c000000230f0f1f1b071b46c1c6d031b1b0300000b004070aaaaaaaa000a1c002aa03030306c4c0000c0c0000000000000000000008c3c3c7c0c0c0c0c8c1c7d23071f400002caaaaaaaa00000aa03030303030f0387031b0303030300000000000000000c0b000004c00f000c003000c030000c000000008c3c3c7c0c0c0c0c0c0c0d030703400002c0101c2aaaaaaa800287000aa80130f0f13131b3703371b130300000000000000000000130f0f1313071344c1c4d131f131f0000aaaaaaaaa0000aa05002b1b2b032b1b2b03230f0f23000000000000000000000707010741d07400001caaaaaaaa0000069548c3c3c8c1c1c1c0c1c6c1c0c000000000000000000013003c00701c000700003006c00000043d87070750707070741d000007001401c1c2aaaaaaa8002870009a988c4c9c3c9c3c8c4c0c0c0c0c14000000000000000000001d074001c1c040c0c0d0000072aaaaaaa800001a40c0c0c0c0cec0c0c0c3c0c0d5000000000000000000004c00f000c003000c030000c000000001d0750361c0c0d40c0c1c00001c0101c2aaaaaaa8002870009a46c0c6c0c8c4c9c3c9c3c8c4c140000000000000000000001d0740d103030000000072aaaa0baaaa800001a41c1c1c3c1c1c1cec6c0c6c0d5000000000000000000004c00f001c0001c070000c01b00000001d0740c0c0c0c0d50361c00001c005007070aa81e0baaaaaa000a1c00269272700000000000000f000c01b00000007c9c7c7c7c00002c0101c2aaa800287000aaa030f032303c0306c0b02c0302c000b030b0b0b0b030303030f0f0b0b030302317231700aa0230f0f1f031b1b0307c8c02c2c23071f48c1c7daaaa28280a8a82ea80c0c0c0c3c0e1c3c3c0c0c3c3c3c8c0f06c6c06cbc00c1b02c2c2c3c2c2c2c4c2c2c2c2c2c6c2c2c2c2c2c2c4c2c6c0c0c2c6c2c6c2c2c0c0c2c0c02c2c2c02c0b02c2c02c2c00c0b00b02a230f0f1f1b071b46c1c6d031b1b0307c8c0b070b42c1c2d08c2c2c2caa0baaaa0b82eaa8a000a0a1e0baa03030388c0f00c0302c0b00c030002c2c2c2c2c2c6c4c0c0c0c0c0c0c0c0c08c5c8c5c02a808c3c3c7c0c0c0c0c1f230230b0b0b08c1c7d23071f6aaa8a0a02a2aa80c0c0c0c0c3c0e1c0c6c0c0c0c0c8c0f00c0300c0c00cbc02c2c2c3c2c2c2c4c0c0c0c0c2c6c0c0c0c0c0c0c0c0c0c0c0c0c2c0c0c2c2c0c0c0c0c02c2c2c02c0b00c0300c0c03003030b0b002c0a88c3c3c7c0c0c0c0c0c0c0d03070341f2302c1c2d0b070b4230b0b0b2a82eaaaaa80e0ba28002828782ea88c3c3c8c0000000000002c2c08c0c8c6c8c6c8c0c000000008c3c3c7c8c7c8c7c00008c1c7d23071f62aa800002802a80230f0f23171b2303231b1703021c0f003c000b0b0b0f0b0b0b130b0b0b0b0b230b0b0b0b0b0b130b170b030b1b0b0b0b03000b170000000002c0b000000208c3c3c7c5c1c7d23071748c7c8c7c002c1c2d0b070b4002caa0baaaa0b82eaa800002021e0baa0303030300000000002f13270f270f2f130003030000000002f1f271f0303030300000b0bc1c7d2f071f6aa2800002802a80c0c0c0c0c8c0c0c0c3c0c0c000021c03000c0b0b0b0f0b0b0b03030303030303030303030303030b03030b0b030303030000000000000c0b000020bc7c9c7c0c0c0c0c0c0c0d0307034002c1c2d0b070b4002caa0baaaaaa800002021e0baa1b031b0300000000002f13270f270f2f130303000000000002f1f271f031b1b0300002f071f4bc1c7daaa800000a0082ea85c6c6c3c5c3c6c8c6c0c6c0c00000c00c00870b0b0b0f0b0b0b0b0b0b0b0b170b170b0b0b0b0b1b0b03030b1b0b0b030300000002c0b00000000020bc7c9c7c6c1c5d17071b40c6c6c0c002c1c2d0b070b4002caa0ba0b82eaaaaa800002021e0baa 25 33554431 10 1023
def hc_66_3 : Nat → Nat := unpackHintV5 0xf769e0e9e362e3b98adaca3cd2e9f8cda152c619e2bd8226b7c170a92ba6a391669b620c94c1a888ab067fe2327a795a720a1c6d313667c95a5f2a285961725459424c4a044701523f39f23a014e31b2142d910825720816eba20ef1fe0003bc 0x6c0c3c0c2c0b0b0b0b00303aaa80f00c1703c3c02c2c02c0b00c0b02c2c02c2c0009c3c3c7c0c6c6c0cbc1c7d2f071f4171700b0b2aaaaaaa8a0a2a800b0b0b0f0b0b0b130b0b0b0b0b2f0b0b0b0b0b0b130b171b030f03171b03031b1b0303a80f21c3c3c03c3c3c2c2c5c5c02c2c0b00305c0b02c0b0b00b0b00b0b00b0b00302c00270f0f1f17071f4bc1c5d0b070b42c1c2d031b1b0305c5c02c2caaaaaa80e80eaa872828aa1b030f030b0b0b0b0b0b27130a00000000000000000000270f0f1f031b1b033b071f4ec1c7d0000aa80e2a03800000002a82c2c2c3c2c2c2c4c6c0c3c0ea0003c8702c00000009c02c0002c0b0000c01b000000000000000009c3c3c7c2c1c2d0b070b40c6c6c0c000407000aa80e80eaa870000a082c002a84c4c4c4c0c3c0c4c4c0c131b0131303c5c0b0b00b0b081702c0b02c2c02c2c00c0b0004c3c3c4c4c1c4d13071340c4c4c0c131300b0b2aaa820b82a8a0a2a86c0c3c0c2c3c3c3c3c5c80170006c05c00000000270f0f1f031b1b03171717170000aaa28000082c00aa1b031b0317170f170f17170aa8171705c81b171702c2c2c2c0b00c0b02c2c02c2c0007c9c7c0c6c6c0c5c1c5d1707174171700b0b2aaaa82a0aa0a2a86c0c3c0c2d0b0b0b0b50303aaa270f0f27031b1b032b172b0ac5cac0b0b0b0b030b0b030b0b0b02c2c2c0b0b0b0b90740d0741c1d41c1d41d0741d076aa03aaaaaaaaaa69507031b03130f0f1307070707171707172b0707072817270705c1b170b0b0702c0b02c0f61c1d07070741daa88aa542c2c2c3c2c2c2c4c1c1c1c1c1c1c2c1c1c2c2c1c1c1c1c6c0c3c0c1c1c0c0c1c6c0c0ea270f0f2707070701cbc1c0b0b02c2c2c031b1b030b0b0b0b07070701c2c1c0b0b0b02c2c2c030b0b030b0b0b0b43d8707075070707070707075070742d40d0741d0741d076aaaaaa03a03aaa1eaaa9a986c0c6c0cbc4c9c3c9c3cbc4c28000000000000000000001d0740d0741c1d41c1d40002aa038a80e00000000690b0b0b0f0b0b0b131b031b03a8000000002f003c00b0000b02c0003006c00000000000000000741d07075070750341d061c0001c02aa03a03aaa1c0002820b000691b031b031705c0305c2f13270f270f2f130303aaa050b402c0b00c0b0002c2c02c2c01d0740d07460141c51072aa03aa28aaaa28690b0b0b0f0b0b0b131b031b03a81c1c1c3c1c1c1cec1c1c1c1c1c2c1c2c1c1c1c1c1c2c1c0c0c1c6c1c1c0c0c5c1702c5c02c2c00c17150b02c0b0b00b0b00302c070b007070000741d07075070750341d00141871072aa03a03aaa1eaaa8a0a1a42c2c2c3c2c2c2c6c0c6c0ea27270b0b02c2c2c031b1b030b0b0b0b0b0b0b02c2c2c030b0b030b0b0b0b1f271f0b070b42c1c2d031b1b031f1f0b0b0b0baa80e80eaa87aaaaaa030300000c3c0c003c3c00000000000000000009c3c3c7cec1c7d3b071f40c6c6c0c0002aaaaaaa800002a80c0c0c0c3c0e1c3c3c0c0c3c3c3c0000000013003c01306c001b00003006c0000000000000000270f0f1f1b071b46c1c6d031b1b03000101c002aaaaaaa8287000802a80c0c0c17000c004c00030005c000000000270f0f1f03030303171717170007002aaaaaa8200aa03030306c4c0000c0c0000000000000000000009c3c3c7c0c0c0c0cec1c7d3b071f40002aaaaaaa800002a80c0c0c0c0c3c0e1c0c6c0c0c0c0c0000000030013003c003000c00300c0003000000000000000000270f0f1f0303030303030340c1c0d000101c002aaaaaaa8287000802a80130f0f13131b4303431b13030000000000000000000130f0f1313071344c1c4d131f131f0000aaaaaaaaa0000aa05002b1b2b032b1b2b03270f0f27000000000000000000000707010741d0740002aaaaaaa800001a55270f0f2707070703071b07030000000004c00f001c070001c0000c01b000000000000000010f61c1c1d41c1c1c1d0740001401c1c002aaaaaaa8287000801a998c4c9c3c9c3d8c4c0c0c0c0c14000000000000000000001d074001c1c040c0c0d0000aaaaaaaa000006903030303033b0303030f0303540000000013003c003000c00300c00030000000000000000000741d40d8703035030307000101c002aaaaaaa8287000801a46c0c6c0d1c4c9c3c9c3d1c4c14000000000000000000001d0740d103030000000aaaa82eaaaa00000690707070f0707073b1b031b03540000000013003c0070000701c0003006c00000000000000000741d0303030303540d870000500707000aa81e0baaaaaa0a1c002006927270000000f000c01b00000000000007c9c7c7c7c000407000aaaa0a1c00200aa80c3c0c5c0f00c1702c0c2c2c2c2c0c0c0c0c3c3c2c2c0c0c2a802c0b00c0b0002c2c02c2c09c3c3c7c0c6c6c0c17170ec1c7d3b071f40b0b2aaa8a02a28a20baa030303030f03870f0f03030f0f0f0b0b0b0f0b0b0b130b0b0b0b0b1b0b0b0b0b0b0b130b1b03030b1b0b1b0b0b03030b031703c17170171700305ca82c0b02c2c02c2c00c0b02c2c02c2c0009c3c3c7c6c1c6d1b071b40c6c6c0c2c1c2d0b070b4171700b0b2a82eaaa82e0baaa00282872882ea80c0c0e1703c0300c0b0b0b0b0b0b1b1303030303030303030aa00b02c0300c000b0b00b0b0270f0f1f0303030305c5c3b071f4ec1c7d02c2caaaa280a8a28aa03030303030f0387031b030303030b0b0b0f0b0b0b13030303030b1b0303030303030303030303030b03030b0b030303031703c0300c030300c00c0c5c5c2a0b02c0300c03030030b00b0b00b0b000270f0f1f0303030303030340c1c0d0b070b42c1c2d05c5c02c2caa0baaaaaa0382e800a0a1ca20baa 24 16777215 10 1023
def hc_66_4 : Nat → Nat := unpackHintV5 0x8250914022419ee34b8f1297c7129db38640c1b024c0d169aa6121e52f0c61166f45cac49cc4fbd9a259891919c4c08561e03c0da91c72650d1c47460da022ca4f2143687095e2f43bf3c01b1cb70b7e8404f033c1aa33808d91e03803b0123274000246 0xc0c0c0c00000321c0f003c00300000000000055550001100082e2aa800002820b0000550f0f0f0f0f0f0f0f0b0b0b0b0b0b0b0b0b0b0b0b5555555582eaaaaa82eaa0b9540c0eaa80c0c0c0c0c0c0d030350f0f0f0f2f174b0bc5d2c030303030b0b0b0b0b0b0b02c2c2c030303030b0b0b0b0741d0707075070742d640c0c0d0741d0741d82eaaaaaaaaa82eaa0b9a4a00c0c0c0c3c0c3c0c5c0c5c0c0c0c5c0d0c0c0c0d43c3c2c2c0c0c0c1702c0b00c0b02c2c1d0740d870340c1e22aaaa030303030303030303030303030b0303030303030b030b03030303030f0303030f0303542c2c0b0b0b03c3c3c3c0c0c0c0c0c0c0c032f0302c2c2c0b0b0b02c2c2c2c0c0c0c0c0c0c0c030b0302c2c2c2c1c1c1c1d41c1d0b50741d40d87030350303070741d0741d82e82eaa87aaaaaaaa0baa82e690bc0d170ba0b0f030f030707aaa030350b40c0c3c3c3c3c0c6c6c0cbc5dfc2f1702c2c2c2c0c2c2c0c2c2c2c0b0b0b02c2c2c2c1d0740c0d9030303035070342d41d0741d0760baaaa82eaaaaaa0baa82e6928070f070f07070717074307070717071717031b0350f0f0b0b07171701c1c00c0c2c0b02c0702c2c1d0740c0c0d0361e201e0baaaaa07070707070b070b07070707070b070707070f0707070f0b1b03030b0b03030f030f03542c2c0b0b0b03c3c3c3c1cbc1c07070700c6c6c0c2c2c2c0b0b0b02c2c2c2c1c2c1c07070700c2c2c0c2c2c2c2c1c1c1c1d41c1d0b50741d0303030303540d870741d0741d82e82eaa8781e0baaaaaaaa0baa82e690a000f0f0f0f2f1b2f032f1b2f030000000000000000000741d0707075070742d41d074000020b8a82e0000aa00000069a82c6c2c0c2c2c2c0c3c3c3c3c000000000b0000b02c000f003c003006c0000000000000000070707075070742d41d0741d074187000070082e82eaa87aa00000a082c0001a43c3c3c3c3c0f05c1701c1eaa8bc0cbc6cbc6cbc0c142d00b02c0b02c000b0b00b0b00741d0741d0600141c42d441c82eaaa8a82caaaa2a0b1a6a0b1b0b030b0b0b030f0f0f0f07070707070b070b07070707070b070707070f0707070f0703071b070707030b1700b0b00f03c1705c542c2c02c2c02c0b02c0b01c2c01c1c0001c1c1c1d41c1d0b50741d0741d001418710720ba0baaa1eaaaaa8a82c2a0b1a6a0b1b0b030b0b0b030f0f0f0f0b0b02c2c2c0f0f0f0f0b0b0b02c2c2c0b0b0b0b0b0b0b0b0b0b0b0b0b0b070b42c1c2c2d0f0f0f0f1f1f1f1f0b0b0b0b82e82eaa87aaaa0baa82eaa03030380c0c0c0c0ea80c0e84c3c3c4c4c5d2c4b171300c0c0c0c2c2c2c2c2c2c2c0b0b0b00c0c0c0c2c2c2c2c4c3c3c4c4c1c4d13071340c0c0c0c4c7c4c7c2c2c2c2eaaaaaaaaaaaaa0baa0303003030300c0eaa80c0c0c0c0c0c03c3c203c0300c0b0b00b0b00b02c0300c002f071f4bc1c7d270f0f1f0303030305c5c02c2caaaaaaaa2828aa000c0c0c0c0c0c0c0c0c0c0c0c0c4c0c0c0c3c0c0c0c4c0c5c0c0c0c0c0cbc0c0c0c0c0ea03c870f0f00f0f0f0300c03030031700b02c0b0b00b0b00300c03030030b000270f0f1f17071f4bc1c5d0303030303030340c1c0d05c5c02c2caaaaaaaa1e03a80e282882ea89c4c0c0c0c0c0c0c0c0c0c0c28000000000000000000009c3c3c7cec1c7d3b071f40c0c0c0c0002a80020b80a80e000082ea80c0c0c0c0c4c0c0c0c3c0c0ea0003c8700000009c00c003000c030000c0000000000000000009c3c3c7c0c0c0c0c0c0c0d0307034000407000aaaa1e03a80e0000a082c0020baa03030303131313030300300c0c4c4c0f1700c803030030300b02c0300c0b0b00b0b000130f0f130303030313071344c1c4d04c4c02c2caaaaaa082e0282882ea85c5c5c3c5c3c5c0c0c0c0c2a285c1700c0c0c0c0c8030b02c0b0b00b0b00300c001f271f17071745c1c5d0303030305c5c02c2caaa8a0aa2a82882ea80c0d40c0c0d0303aaa030303032b172b0ac5cac270f0f27030303030b0b0b02c2c2c0b0b0b0b030303030b0b0b0b030350707590740d0341d0741d076aaaaaaaaaaa9a544c3c3c4c1c1c1c1c5cac1c5c5c1c1c1c0c0c0c0c881c1700c0c0c0c1c0b02c0b03d870741c1c1d076a81e0ba2299a540c0c0c0c0c0c0c0c0c0c0c0c0c4c0c0c0c3c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c0c0ea270f0f2707070701cbc1c0303030303030300c0c0b0b0b0b07070701c2c1c0303030303030300c2c0c0b0b0b0b43d87070750707070340d030340d40c0c1c1d41d0741d076aaaaa0782eaa8780ea03aaaa96a5a2f13270f270f2f13030303030a000000000000000000000741d03035070750340d00000aa00082e02a03800016940c0c0c0c0c4c0c0c0c3c0c0ea000000000bc00f000c003000c030000c0000000000000000001d0740d0340c0d40c1d41870000700aaaa1e03a80e0000a082c0016940c0c0c0c5c1700c030bc4c9c3c9c3cbc4ea80c0e8140d00b02c0300c000b0b00b0b00741d0340d1805031441caaaa28aaaa28690303030303130303030f0303a81c1c1c3c1c1c1cec0c0c0c0c0c0c0c0c0c0c0c0c0c0c1c0c0c1c1c0c0c0c0c5c1700c0300c0c00c5c150b02c0300c03030030b0070b007070000741d0340d030340d40c0c1c1d4005061c41caaaa1e03a80e81e0baaaa28285a503030303030303030f0303a89c9c0c0c0c0c0c0c0c030302c2c2c2c0c0c0c0c0c0c0c030b0302c2c2c2c7c9c7c0c0c0c0c0c0c0d03070347c7c2c2c2c2eaaa8780ea03aaaaa0baa131b0b0b03a84c1304c002c0f00c1b04c17000001313131304c41caaa28131b0b02c2c0c6c6c0c2c2c0ea004c4c4c4c4c4c4c1304c2c0b02c0b01d0744c4c4c4c4c4eaaaa84c6c0c3c6e0b0b0b0303aaa130f0f13031b1b03131705c4c0b0b0b0b030b0b030b0b0b02c2c2c0b0b0b0b130f0f13031b130313071344c1c4d131f131f0b0b0b0baaaaaaaaaaaaaaa 25 33554431 10 1023
def hc_66_5 : Nat → Nat := unpackHintV5 0x82c5104010549f0c3f0f3294e77a47c3878d69b22468cb5b6e61451a2cf2ec14a17609caa1848099321d08d0fef3e477c1ee34d5c318ec5f8b424d051aa1a21fdb60f9c5887122f02ec27413a0f008a44b03623c016612c08c49b02c66700d024c0001a0 0xc0c0c3c3c6c3c3c0c0c0c3c0e1c000000000f02c000000000155555554000018703c0003c0f0003c00f000c03006c1b000000040b0ba0b0ba0b82e0382e0000550202c00c0c0c0c3c13130000303000000000000000000000555555550000061c0b82e0380e0b0ba0b0ba00005503030303030f0387031b03030303000000000000000000555555550000061c13003c003000c00300c000300000000102e0b80e0380c0e80c2e8000154080b0004c3c3c4c4c6cac0cac6c4c0c000000000000000000155555555400002e0b82c2e82c2e82e0b8000154000000000155540000187000f000c01b000000040b82e0b82e0000550202c2a03030303030303030303030303130303030f0303030b030b03030303030b032703030303005c0f02c2c02c5c00321c0c0c00c0c6c2c0b02c2c02c2c00c0300c0c00c2c0009c3c3c7c2c1c2d0b070b40c0c0c0c0c0c0d0307034171700b0b2a8782ea0baaaaaa8a0a20baaa86c0c3c0c2c2c0c0c2c6c0c0c0000000321c0013003c00b02c000b09c001b0000000000000000270f0f1f0b070b42c1c2d031b1b03000101c002a8782ea0baa8000880020baaa85c4c3c3c3c3c6c4c2c2c2c2c2c2c6c9c2c2c5c5c2c2c2c2c6c0c3c0c2c2c0c0c2c6c0c0c01703c0b0b00b1700303030303000c870b02c0b0b00b0b00b0b00b0b00302c00270f0f1f0b070b42c1c2d1b071745c1c6d031b1b0305c5c02c2caa1e0ba82e82e0baaaaaa282882eaaa0303030303030303030303030000000000c8704c00f002c0b0002c270000c00000000000000009c3c3c7c2c1c2d0b070b40c0c0c0c000407000aa1e0ba82eaa0002200082eaaa03030303030303030303030303130303030f0303030b030b03030303030b032703030303544c3c3c4c2c2c2c0b270b00c0c0c0c0c0c0c032f0302c2c2c2c2c2c2c0b0b0b00c0c0c0c0c0c0c030b0302c2c2c2c1d0741c1d41c1d50361c0c0d40c0c1c1d0741d076a8782ea0baaaaaa0382eaaaa9696a0707070f0707071307070707070b072707070707070b070b13030f030b0b03030b1b0303544c3c3c4c2c2c2c0b270b01cbc1c07070700c6c6c0c2c2c2c2c2c2c2c0b0b0b01c2c1c07070700c2c2c0c2c2c2c2c1d0741c1d41c1d40c0c0c0c0d50361c1d0741d076a8782ea0ba0782eaaaaaaaaa9696a130f0f130b0b0b030b1b0b030000000004c00f002c0b0002c270000c01b000000000000000001d0741c1d41c1d41d0741870000700aa1e0ba82eaa0000a082c001696a130f0f130b0b0b030b1b0b030707070f0707071307070707070b072707070707070b070b0703071b070707031303c0b0b00b1701705c542c0b02c2c02c2c02c0b01c2c01c1c0001d0741c1d41c1d41d074005061c41caa1e0ba82eaa81e0baaaa28285a5a89c3c3c9c2c2c2c0c2c6c2c0c9c3c3c9c2c2c2c0b270b02c2c2c2c2c2c2c0b0b0b02c2c2c2c2c2c2c2c9c3c3c7c2c1c2d0b070b47c7c7c7c2c2c2c2ea8782ea0baaaaaaa0baa0aa80f0f0f0f17171703171b170380f0f0f02c2c2c5c5c1702c0b02c2c02c2c02c0b002c02c3c3c3c3c5c1c5d17071747c7c171700b0b2aa82a2a8aa0a2a80c0eaa80c0c0c0c0c0c0c030300f03c171700b0b0800c02c0b02c2c02c2c00c030003c3c3c3cbc1c7d2f071f40c0c0c0c171700b0b2aaaaaaa8a82c28aaa80c0c0c0c0c0c0c0c0c0c0c0c0c2c0c0c0c0c0c0c2c0c2c0c0c0c0c0c3c0c0c0c3c0c0c00b0b171700b0b02c03c0f00321c0c0c00c0c6c2c2c02c2c02c0b00c0300c0c00c2c0002c2c1c2d0b070b0b43c3c3c3c0c0c0c0c0c0c0d0307034171700b0b20ba0baaa1eaaaaa8a82c2a0b2a828003c0c3c0c6c5c0c0c2c2c0c0c000000030000000000000f0f0f0f43071f50c1c7d031b1b030000a2a000aa0000aaa82c2c6c6c0c0c2c2c0c2c0c0c3c0c3c0c0000000321c000b0000b02c000f003c01b00000000000000000b0b070b42c1c2c2d0f0f0f0f031b1b03000101c0020ba0baaa1ea800002820b0000aa0f030f030f0faaa030300b00c0c3c0f00c0c200c87030300b0300b02c0302c0b0b00b0b0000f0f0f0f031b1b032f071f4bc1c7d05c5c02c2c82eaaaaaaa8a82c2a0b2aaa0b0b17170b0b0b0b0b0b0b0b0b0b1b0f0f0f0f0f0f0f0f0b1b03030b0b03030f030f03002c5c02c2c03c0f00c0c0c0c0c00321c2c2c02c2c02c0b02c2c02c2c00c0b0002c2c1c2d0b070b0b43c3c3c3c6c1c5d17071b40c6c6c0c171700b0b20ba0baaa1eaaaaa8a82c2a0b2a8800c0c0c0c0c5c0e1c0c0c0c0c0c003c05c00c0000000000f0f0f0f17171717030303030000a280aa00800aa0a000303030303030303030303030000000000000000000f0f0f0f43071f50c1c7d030303030000a2a000aa00000aaa80c2c0c6c0c0c0c0c0c0c0c0c0c0c0c0c0b0000000000321c0b0000b02c000f003c00300000000000000000b0b070b42c1c2c2d0f0f0f0f03030303000101c0020ba0baaa1ea800002820b0000aa07a80c0c0c0c0c0c0c0c0c3c0c0c0c3c0c0c0c1c0c0c0c1c0c0c00f03c0701c00c870303003031b0b02c0701c0300c03030030b000aaaaaaaaaa282807a83c0c3c0c1c0c1c0c00000321c000f003c007001c01b00000000000000a2aaaa0002200007a83c3c3c3c3c3c3c3c1c1c1c1c1c1c1c1c3c0c3c0c1c0c1c0c00f03c0701c0303030303000c870b02c0701c0b0b00b0b00302c00aaaaaaaaaa282807a80c0c0c0c0c0c0c0c0000000321c0f003c007001c00300000000000000a2aaaa0002200007a83c3c3c3c1c1c1c1c3c3c3c3c1c1c1c1c2c2c2c2c1c1c1c1c2c2c2c2c2c2c2c2eaaaaaaaaa80c0c0c0c0c3c0c0c0c3c0c0c00f03c00c870303003031b0b02c0300c03030030b000555555555141482eaaaaaaa8a82c2a0b1543c0c3c0c000321c000f003c01b000000000000555500401100082e2aa800002820b0000550f0f0f0f0f0f0f0f0f030f03003c0f00c0c0c0c0c00321c2c0b02c2c02c2c00c0b001555555554550520baaaaaaaa2a0b0a82c55 25 33554431 10 1023
def hc_66_6 : Nat → Nat := unpackHintV5 0x879ad885f8687f71a276ca2a76a80870c9787068186ed06668b18867e83267482861198c60b81860581859e19e59981258b03a57a0445391044c29da45f18e3fb98e3931a23241bc2c418025c99e1f01b219f9421219f80d513205220c000148 0x5c4c6c3c5c3c6c4c6c0c6c0c00000c00c00870707070f070707070707070717071707070707071b070303071b0707030300000000000000101d0741c1d41c1d40d07400001021c2e0b82c2e82c2e80e0b8001c2e81c1e8002c60740c0c2c2e1c2c3c0c0c0c0c1c1c0c0c0c0c0300c0300c0300c0c030b0000c0c0c0c0c0c0c0c13042c0340d030340c1d107040c10740e0380e03882c20b02e0b981d0303030300c0300c0300c030300c0c0c2e1c0003030303030313870303030303030307070304c4c10b00d0340c0d0303030787441c103041d0380e0380e20b082c0b82e60740c0c0c4c0c3c0c021c0c0300000c0b01c1c0c0c0c0c0c6c0c0c0c0c0c4c4c0d1c0c0c0c00001c1c0d074400e0b82e0b81c1c5c1c1c3c1c03000000741d0b82e130f1b0f0f131b13030300300c08700007071b171313171b171b131303031b1b1b1b030005c0007070741d100b82e0b82e138713131b15c3c4c05c05c4c0c0c0c0c1c0c0c0c3c0c0c0c0c0c0c0c02c2c0c0b01c1c0c4c4c0c0c0c0c0c4c6c1357042c07070341d10740e0b82e0b80c005c0c4c0c1c0c0c0c1c1c1c1c4c0c4c0c4c4c4c1b06c2c2c2c2c2c0b1b007070303030313131303131304c10b01c1c1d07441d0b82e0b82e0b21c4c0e1c4c4d5c6c078703006c0c5c1b01307000c6c6c0c4c04c00b02c0007075713130004c4c000070710100b82e0b82e130f0f131303c00b0b02c2c0b02c0007070703131b1b130301317170050b401c1d070741d07441c1070141c50b82e0b82e20b082c0b0ba0b0ba60740c0c3c0e1c3c0c3c3c4c001305c0300004c3c3c4c4c4c4c4c5c5c4c5d2c4c4c4c0c5c6c0c07000741d01c002e0b80b0b82e0f038703030f0303030f00c000305c0000f0f0f0f0303030303030303171703175b03030301c000d07407000382e02c2e0b80c0c3c4c3c0c3c0e1c3c170003c0302c0b00003c5d6c3c3c3c3c3c3c3c5c5c3c3c3c3c0c5c6c0c07000741d01c002e0b80b0b82e03030f0387130303031300c0300c00000302c0130f0f130303030303030303171703175b03030301c000c0d40c1c1d01c000e0b80b0b82e131313130f0f1313131303131b130300000000000000000001074001c1c01d07400002e0b82c2e82c2e82e0b8000181d05c001700000000017170f170f171717031717171b170300700000741d0741d000700000002e0b82e0b8002c000b0ba0b0ba6074001c1c1c3c1c1c1c1c0c1c6c1c1c1c0c01c1c1c02c0b02c0b00150741d0741d1070005061c2e0b82e0b882c070ba0707a02e0b0b181d030300000c3c3c3c0c003c3c00000000000000000015555555400002e0b82c2e82c2e80e0b80001540c0c0c0c3c0e1c3c3c0c0c3c3c3c00000000000000000155555554000018704c00f004c1b0006c0000c01b000000040b82e0b0ba0b0ba0382e0000550202c00c0303000f0f003030000000000000000000005555555500000b82e0380e0b0ba0b0ba000055030f038703030303030f03030303000000000000000000555555550000061c0f003c00300c00306c00300c000300000000102e0b80e0380c0e80c2e8000154080b003030001b130000f0300c000000000f02c00000000055555555000040b0ba0b0ba0b82e0382e000055 24 16777215 10 1023
def hc_66_7 : Nat → Nat := unpackHintV5 0xb3b918adf970a5921a97ab7a92296089c21a7bfb727669647610167580246c7a425eab745c589456a96c4e421a3f2bc63919842d4af42ce01a2c40282621881a52f414418408430008001008000007c01006a04806a00006a00005c836000172 0x2c0b02c0b00155545018750550f540d51b5054107400b82e0b82e20b082c555642d40c000f04c13017070f0713070707170717070707170747031b070300717000b02c0040741d010870b82e0b81e02c1c0c0c3c0c0c4c0f00c1b02c0b00c0b0001c0c1c1c1c1c0c0c0c0c3c3c1c1c0c0c04c5c4c4c0142d00741d0341d107041c0507142e0b80e0b882c20b02c2e82c2e981d030303030f03870f0f03030f0f0f1303c131301300306c0707070f0707071307070707071307070707070713071b0303071b071b070703030703007070700b02c0b0b00b0b00302c00541d0741c1d41c1d40d07441c00141870b82e0b0ba0b0ba0382e20b01c2e81c1e80b82c2c607403c03000f0300c070f070f03030303070707170717070707170743007170000040741d010870b82e0b81e02c0c3c0c0c0c0c3c0f00c0302c0b00c030001c1c3c3c1c1c1c1c0c0c0c0c0c0c0c0c0fc5cfc5c0140d00741d0340d107040c0503142e0b80e03882c20b02c2e82c2e981d030f038703030303030f030303030f03c0300c030300300707070f070f0707070f070303030303030303030303030303070303070703030303007070700b02c0300c03030030b000541d0740d0340c0d40c1d441c00141870b82e0380e0303a030ba20b01c2e81c1e80b82c2c60740c013003c03c17070707170743070707170717070f070f031b070300717000040741d4010870b82e80b81e02e1c170870b017000f0f030307030f03870f03c0306c0b02c0302c00070703030703070703031313070703030171700542d00f01d0740d07441c141c4141c50b82e0382e20b00b82c2c0b0ba0b0ba60740c0c0c3c3c4c3c3c0c0c0c3c0e1c3c03c3c03c0f00c1b01c1c1c1c1c3c1c3c1c1c1c1c1c3c1c1c1c1c3c1c1c1c3c0c0c1c6c1c1c0c0c01c1c1c02c2c2c2c02c2c0f00b02c0302c00541c1d41c1d41d0740d07441c00141870b0ba0b0ba0b82e0382e20b01c2e81c1e80b82c2c60744c03004c00300000c0c0001d0400b02c2e0b84c003004c0300c070f07130303030307070717071707070717070001c1c00040741d01c0421c2e0b80b0b81e02c0c0c0c0c4c0f00c0302c0b00c030001c1c1c1c1c1c4c4c0c0c0c0c0c0c0c0c04c5c4c4c0140d00741d0340d107040c0503142e0b80e03882c02e0b0b02c2e82c2e981d03030303030f03870313030303031303c0300c030300300707070f070f070707130703030303071b030303030303030303030303070303070703030303007070700b02c0300c030300c00c0c2c2c00150741d0340d030340d40c0c1c1d441c00141870b82e0380e0303a030ba20b01c2e81c1e80b82c2c60744c3c3c4c0000000000001c1c04c0c4c6c4c4c4c0c000000001c0741d074000014002e0b82e0b800002c0b0ba0b0ba60740130f0f1313131303131b1303021c0f003c000707070f070707130707070707130707070707071307170703071b070707030007170000000000000101d0741c1d41c1d41d07400001021c2e0b82c2e82c2e82e0b8001c2e81c1e8002c6075bc6c03036f0131b40f0f0f0f03c00000000001c1c001bc0c6dbc6c0c0000010000741c0741d0004005000b82e0b82e00000b02c2e82c2e981d003c6c3c0c3c3c3c0c3c3c3c3c0f00f0021c001c1c1c1c1c3c1c3c1c1c1c1c1c3c1c1c1c1c3c1c1c1c3c1c0c1c6c1c1c1c0c00000b02c0000000000407075070750741d0741d0000040870b0ba0b0ba0b82e0b82e00070ba0707a000b181d0303030300000000003f133f0f3f0f3f130003030000000000741d0300d000005000b82e0380e00000b02c2e82c2e981d0303030303130303030f0303000008700c00301c1c1c3c1c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1c0c0c1c1c0c0c0c0c001c5c00000000000302c00040741d0340d03035030750000040870b82e0380e0303a030ba00070ba0707a000b181d130f0f131b031702c130f0742e130300310f482c6c0c6c0c000300000000130f0f130303000000000000741d0341c0004005000b82e0382e00000b02c2e82c2e981d 24 16777215 10 1023
def hc_66_8 : Nat → Nat := unpackHintV5 0xd3a258cdc976c46a58be2990b739bcb049bca909d0a1c9d09eb8c49a292493b19e8a126883999e79da707309b46902826279a2586a845329504b31fe45b1603d6a1237f15e2faa122a695021ba2c1ce93415f1be10b94e0b316205c15c000170 0x303030f0f130f0f0303030f03870000000003c0b000000000003c0003c0f0003c00f000c01b00000001c1d41c1d41d0740d07400187000070b0ba0b0ba0b82e0382e000027002802c181d03030304c4c0000c0c0000000000000000000001d0740d0340c0d41c1d4000002e0b80e0382c2e82c2e800008c60740c0c0c0c0c3c0e1c0c4c0c0c0c0c0000000000000000302c00013003c003000c00300c0003000000000741d0340d030350307500061c0001c2e0b80e0380c0e80c2e800008c00a00b060740130f0f13131b3703371b13030000000000000000000070741c1d07075070750741d00000b82e0b0ba0b0ba0b82e000060740c0c0c0c3c0e1c3c3c0c0c3c3c3c0000000000000000002c2c2c2c2c2c2c2c2c2c2c2c0c2c2c0c00001d0741c1d41c1d40d07400001d0740c3c0e1c0c0c0c0c0c3c0c0c0c0c0000000000000000002c2c2c2c0c0c0c0c0c0c0c2c0c2c0c0c00001d0740d0340c0d40c1d400001d0740c0c0c3c3c4c3c3c0c0c0c3c0e1c000000000b02c00000000002c2c2c2c2c2c2c2c2c2c2c2c0c2c2c0c00001c1d41c1d41d0740d07400001d0740c0c0c0c0c3c0e1c0c4c0c0c0c0c0000000000000000302c0002c2c2c2c0c0c0c0c0c0c0c2c0c2c0c0c00001d0740d0340c0d40c1d400001d07400000000002c2c2c2c2c2c2c2c00001d0741d07400001d0740000000000003c003006c0000000741d0741d00061c0001c2e0b82e0b8000000a00b060740c0d555030f03550f0f51303c23170231700306c0b02c0b070070700302c005550545514140b82e0b0ba0b0ba0382e20b082c55030303030f03870f0f03030f0f0f1303c131b01b2f00306c0b02c0b0b00b0b00302c005555555514061d4113543d51346d551b55503546d415041d002e0b82c2e82c2e80e0b882c20b155590b50340c0d543c3d40c0d5543c0f00c030ac5c0ac5c02c0b00c0300c0c01c1c0015555415050502e0b80e0382c2e82c2e882c20b1540c3c0e1c0c0c0c0c0c3c0c0c0c0c3c0f00c0300c0c00cbc02c0b00c0300c0c00c2c00155555554501875043d50f540d503540d035540d55054fc107400b82e0380e0303a030ba20b082c555642d40c0d5546c4d5543c0d032b1702b1700f03c0306c07070700b0703c02c0b00c0b00151415554505502c2e82c2e82e0b80e0b882c20b1540c0c0c3c3c6c3c3c0c0c0c3c0e1c3cbc03c3c03c0f00c1b02c2c2c2c02c2c0f00b02c0302c005555555514061d410f5550f43d550f543d503546d415041d002c2e82c2e82e0b80e0b882c20b155590b503030344c4d5540c0d5544c0f00c0308c5c08c5c02c0b00c0300c0c01c1c00155554150505502e0b80e0382c2e82c2e882c20b1540c0c0c0c0c3c0e1c0c6c0c0c0c0c4c0f00c0300c0c00cbc02c0b00c0300c0c00c2c00155555550341d4501875044d50f540d503540d035540d55054fc107400b82e0380e0303a030ba20b082c555642d414004c3c3c4c8c6c8c0c8c6c8c0c0000000000000000014540015400002e0b82c2e82c2e82e0b80001540130f0f13131b2303231b1303021c0f003c0000000000005555555500021c4113543d51345d552355503546d400001002e0b82c2e82c2e82e0b8000155590b505002b1b2b032b1b2b030f0f0f0f0000000001c000000000000501555000040b0ba0b0ba0b82e0b82e000055003c6c3c0c3c3c3c0c3c3c3c3c0f00f0021c000b02c000000000155555554000871043d5543d0f5543d50f540d51b500000400b0ba0b0ba0b82e0b82e0000555642d40c0c0c0cbc4cbc3cbc3cbc4c140000000c0000000000000055515000000040b82e0380e0b0ba0b0ba0000550303030303230303030f0303000008700c003000000000015555555400087104fd50f540d03540d1b540d035540d5500000400b82e0380e0303a030ba0000555642d4bc4cbc3cbc3cbc4c6c0c6c0c14000000000000000000015401405400002e0b82c2e82c2e80e0b80001545c6c6c3c5c3c6c8c6c0c6c0c00000c00c00870002c0b000000005555555500021c41543d51b5551745d550340d51b46d400011700400b82e0b0ba0b0ba0382e0000555642d544c3c3c4c4c5c4cac6cac6c5c5c4c6c4c6c0c6c0c0000c03021c0002c0b001411542e0b82e0b95130f0f13131b2b032b1b13031303c131702b1703f00b0b02c2c070700b0700b02c0055554505514140b82e0b0ba0b0ba0b82e20b082c5503030f03870f030f0f130f0f131317131b174b171717131713031b17030005d000001540102e0b82e0b80c0c3c6c3c0c3c0e1c3c5c5c3c3c3c3c3c3c3c5d6c3c3c3c3c0c6c5c0c001740b02c00000550040b82e0b82e130f0f130000013131313031313131b1303000000000000005455000500000b82e0b82e000b0ba0b0ba00553f3f1717170f170f171703171b17171703000017040000000000055550000040000b82e0b82e0b0ba0b0ba000055 24 16777215 10 1023
def hc_66_9 : Nat → Nat := unpackHintV5 0xdc6050d5b9aacd122ac6a19cbfc9b6b801f2b1f184a612f89ff188949ad68e8984826b087c498870f2d66ae98265e1425e01f8593932510a0c4ca11a47a93e42e1323a023834b9522cd9f827615e2380f81de16814d2440f3168062244000188 0x303170f0303030307070303030300c030300c5c030303030303030310f00c0300c030004c2300d0340c0d0307440c107441c0380e0380e21704e27888c60740c0c0c0c0300c0c030303178700c0c0c0c0c0c4e1c0c0c0c0c0c0c0c1c1c0c44c0300c0300c001304c0340d030340c0c0c1e1d103041d10700e0380e03885c1384e223181d1303030303070303030f030303030313170305c07070313130303030303131b11700c8c0c0b04c2301c1c0d07441d0382e138ee07030303070707071303130313131313171705c07070303030313131303131311706c2c8c0b1b0231b1308c07070741d10742e0b84e3b84c3c3c4c4c5c0f1705c1701c1c1c0c4c6c6c4c0c145d01303c2308c00130b0230b0070741c1d0741d1070141c510704e0f8ee3b885c130ba3b0ba223181d130f0f13000000070701303131b1313130300000002c000000001c0741d074001400002e0b82e0b8002c2e82c2e80181d004c3c3c4c2c2c2c0c2c6c2c0c1c1c1c3c1c1c1c4c1c1c1c1c1c2c1c1c1c1c1c1c2c1c2c1c0c1c6c1c1c1c0c000000004021c0b002c02c000702c00000001d0741c1d41c1d41d074001021c002e0b82c2e82c2e82e0b81c2e81c1e8000181d0f0f0f0f000007070002303231b231b2303000002c00000000001d0701d0741001400002e0b82e0b8002c2e82c2e80181d002c6c2c0c2c2c2c0c3c3c3c3c1c1c1c1c1c2c1c2c1c1c1c1c1c2c1c1c1c1c3c1c1c1c3c1c0c1c6c1c1c1c0c00000000402c02c00870000000007075070750741d0741d0004087000b0ba0b0ba0b82e0b82e070ba0707a000060740c0c0c0c00008c4c8c3c8c3c8c4c000c0c000000b00000000000741d0300d000500000b82e0380e000b0ba0b0ba0060740c0c0c0c0c4c0c0c0c3c0c0c00707070f070707230303030303030303030303030303070303070703030303000000000c170100b00021c03000c01c0b0000000741d0340d03035030750004087000b82e0380e0303a030ba070ba0707a000060746c0c6c0c00008c4c8c3c8c3c8c4c0c0c00000000003000000000741d0341c0400500000b82e0382e000b0ba0b0ba0060742c2c2c3c2c2c2c4c6c0c6c0c00707070f0707072307070707070b070b07070707070b070303071b07070303000000001000030030021c0000001d0741c1d41c1d40d074001021c002e0b82c2e82c2e80e0b81c2e81c1e8000181d0707070f0707070703071b070707031705c1705c54001c2c01c1c0001d0741d074005061c41caa070ba0707a2170860740c0c000030f0f0f03000f0f00000000000000000005555555500001383e1f0ba1f0ba0386e000055030303030f03870f0f03030f0f0f0000000000000000005555555500061c0013003c01306c001b00003006c000000104e0f84c2e86c2e80e1b8000154080b00300c0c003c3c00c0c0000000000000000000015555555400003e0f80e0387c2e87c2e80001540c3c0e1c0c0c0c0c0c3c0c0c0c0c00000000000000000155555554001870003c00f000c03000c1b000c030000c0000000040f83e0380e0303a030ba0000550202c00c017003c0c0300000045d87555555400170003c001b00041785e0f83e0386e005508003002c00f0300c0000015555540018702c00b003c00f000c01b00040b82e0b82e0382e00550202c00c0c0006c4c0003c0c030000000000000000005555555500001f0ba1f0ba0f83e0386e0000550303030f0f1b0f0f0303030f038703c0000000003c000000000043d075555555500061c000f0000f03c000f003c00300c01b06c000000103c2e83c2e83e0f80e1b8000154080b0030303030f04c4c0000c0c00000000000000000000155555554001870004e0f80e0387c2e87c2e80001540c0c0c0c0c3c0e1c0c6c0c0c0c0c00000000000000000155555554001870004c00f000c003000c030000c0000000041383e0380e0303a030ba0000550202c00130f0f13131b2b032b1b130300000000000000000005555555550000131f83c7e130ba1f0ba1f87e0000550000000000555500061c00003c003006c000000107e1f87e1f8000154080b0030300000c3c0c003c3c00000000000000000001d0741c1d41c1d40d07400002e0b82c2e82c2e80e0b8000181d030303030f03870f0f03030f0f0f00000000000000000004c00f004c1b0004c0000c01b00000001d0741c1d41c1d40d07400187000070b82e0b0ba0b0ba0382e000023002802c181d0300c0c003c3c00c0c0000000000000000000001d0740d0340c0d41c1d400002e0b80e0382c2e82c2e8000181d030f038703030303030f0303030300000000000000000003c00f000c003000c030000c000000001d0740d0340c0d40c1d400187000070b82e0380e0303a030ba000027002802c181d030300013130000f0300c000000000f02c00000000007075070750741d0341d000400b0ba0b0ba0b82e0382e000027181d 24 16777215 10 1023
def hc_66_10 : Nat → Nat := unpackHintV5 0xf960c4f55902eee19ee52270dea99ed4ea70ced186c849a2bdda9cb751a2ad4284a801509f9a1a9a315a91ea128e58e488b96880ba007c69147729506eca1867b1c66331205aca1a4ce37a447a1a36b3722daa4224f22e17436c0f1a0a0003c6 0xb0b0b0b0b0b0b0b00000000000741d0741d000741d000000000f000c01b00000000000001d0741d0741870000700aa0000a00b00060740c0d555030f03550f0f51303c17070070700305c1303c230b0230b00306c005550545514141383e1f0ba1f0ba0386e217087c55030303030f03870f0f03030f0f0f1303c13170171700305c1303c130b01b0b00306c0055555555061d405113543d51346d551b55503546d5074150b0004e0f84c2e86c2e80e1b885c21f155590b50340c0d543c3d40c0d5543c0f00c0300c0c01c1c03c0f00c030ac2c0ac2c0015555415050503e0f80e0387c2e87c2e885c21f1540c3c0e1c0c0c0c0c0c3c0c0c0c0c3c0f00c0300c0c00c5c03c0f00c0300c0c00c2c00155555554187501443d50f540d503540d035540d5541d0542c000f83e0380e0303a030ba217087c555642d40c0b0b0b02c0c3c0d030b02c0f03c0305c555555061d410b542d50f543d503546d507400b82e0b82e0382e20b155590b503035551b135550f0340c1c1c03c1c03c0f00c170ac2c0ac2c03c0f00c1b00151415554140507c2e87c2e83e0f80e1b885c21f1540c0c0c3c3c6c3c3c0c0c0c3c0e1c3c3c5c5c03c3c0f00f03c0305c0f0f0b00f0b03c03c0f00c1b00155555554187501443d5543d0f5543d50f540d51b541d0542c000f0ba0f0ba0f83e0386e217087c555642d40c0c0d131355503035551303c0300c03030070701303c0300c230b0230b00055555054154141383e0380e1f0ba1f0ba217087c5503030303030f0387031b030303031303c0300c03030031701303c0300c03030030b000555555540d075061d405113543d503540d50340d5503555074150b0004e0f80e0380c0e80c2e885c21f155590b50500130f0f13371b3703371b37030000000000000000005150005500000b82e0b0ba0b0ba0b82e000055004c3c3c4c2c2c2c0c2c6c2c0c0000000008702c00b00b0000055555555021c400113543d50b42d550b55503546d41000042c000b82e0b0ba0b0ba0b82e0000555642d41400ac6cac0cac6cac0c3c3c3c3c0000000000000b0000000050155500000b0ba0b0ba0b82e0b82e000055002c6c2c0c2c2c2c0c3c3c3c3c0b05c000000000b00b0021c000155555554087100042d5542d0b5543d50f540d51b504000000b0ba0b0ba0b82e0b82e0000555642d40c0c0c0c00c000005508741343d1344d51352d50340d10000b82e60b40c0c0c0c8c4d5c3dac3c8c4c1400000000000b000003000000155454000010002e0b80e0382c2e82c2e80001540c0c0c0c0c0c0c0c3c0c0c00000000002c0008700c00300155555554087100048d50f540d503540d035540d5504000000b82e0380e0303a030ba0000555642d44c6c2c2c0c0000030015544d07421d04d0f40d1b44d13544d6b5440042c00b82e60b48c4cfc3cfc3c8c4c6c0c6c0c14000000000000000000015401405400002e0b82c2e82c2e80e0b80001542c2c2c3c2c2c2c6c0c6c0c00002c170000000000c00c00870055555555021c400123543d50b5550b42d5503546d41000042c000b82e0b0ba0b0ba0382e0000555642d55130f0f13131b2b032b1b1303131703c5c07070170701705c1303c130b0230b02308c0055554505514141383e130ba1f0ba1f87e217087c551705c1705c00005555061d4051543d503546d5074150b0007e1f87e1f885c21f155590b50703030f03031303c0305c070307070707030303030f0f070703030513404c0f00c1b0004c2c04c2c01d0740d07441c05071441c1383e0386e21704c2e84c2e888c60740c0c0c0c3c0e1c3c3c0c0c3c3c3c1c1c1c3c1c1c1c4c1c1c1c1c1c4c1c1c1c1c1c1c4c1c6c0c0c1c6c1c6c1c1c0c0c1c0c4c0f04c4c04c5c00c17151303c130b0130b00306c070b007070000741d07075070750341d001418710704e0f84c2e84c2e80e1b81c2e81c1e885c223181d030f030303030f03c0300c07070f0f0707070703030303030303030503403c0f00c030008c2c08c2c01d0740d03440c05031441c0f83e0380e21709c2e89c2e888c60740c3c0e1c0c0c0c0c0c3c0c0c0c0c1c1c1c3c1c3c1c1c1c3c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1c0c0c1c1c0c0c0c0c3c0f00c0300c0c00c5c150f03c0300c03030030b0070b007070000741d0340d0303503075001418710703e0f80e0380c0e80c2e81c2e81c1e885c223181d0f0f030307030f03870f03c0305c07070303070307070303131307070303050f403c0f00c1b0008c2c08c2c01d0740d074141c18705071441c0f83e0386e21709c2e89c2e888c60740c0b0b0b02c0c3c0c1c0c1c1c1c2c1c1c1c2c1c1c1c3c1c1c1c3c0c0c1c6c1c1c0c0c2c0b03c0f00c17150741d0741d0341d00141870b82e0b82e0382e070ba0707a20b181d0303030f0f130f0f0303030f038707070707070f070f07070707070f070707070f0707070f0303071b070703030f1700f0f00f03c0305c543c3c2c03c2c0f00f03c0306c070b0070700007075070750741d0341d001418710703c2e83c2e83e0f80e1b81c2e81c1e885c223181d030303031303c0300c070707070707131303030303030303030503404c0f00c030004c2c04c2c01d0740d03440c05031441c1383e0380e21704c2e84c2e888c60740c0c0c0c0c3c0e1c0c4c0c0c0c0c1c1c1c3c1c3c1c1c1c4c1c0c0c0c0c1c6c0c0c0c0c0c0c0c0c0c0c0c0c1c0c0c1c1c0c0c0c0c4c0f00c0300c0c030030317170544c0f00c0300c0c00c2c01c2c01c1c0001d0740d0340c0d035030307075001418710704e0f80e0380c0e80c2e81c2e81c1e885c223181d 24 16777215 10 1023
def hc_66_11 : Nat → Nat := unpackHintV5 0xbb70beb76902b1a970aa91c6a6a8faa1d136990a329169e88ca93086c17a8540607f81707e504c79314871e1d46cb14c6711685e2a3a5889684fa23a49f16c44017c3a82603569462fb96c26a2462061901971bc1281bc0b41d00721080001c8 0xf0b00c050361c4d0f42d0b42d3740d00100142c2d82d00303030303030000005550361c4d1343d0f44d13544d37540d000050b82e60b40c0c0c0c0000000000fc4cfc3cfc3cfc4c0c0c0000000000155540c000005000b82e0380e00001f02c2e82c2e9540c0c0c0c0000000000021c003c003000c000155550361c00000441543d503400010000042c00014100542e0b80e03800007c0202c155590b55030303030303000008701303c1304c0230ac00300c00555140b0b0b82e20b140c0c0c0c0c0c004c1302c0000871304c0f03c1304c0230ac00300c00555140b0b0b82e07c82c540c0c0c0c0c0c0c0c0c0c0c0c0c0c4c3c3c4c4c5cac2b171300c0c0c0c4c3c3c4c4c2c8c230b1300c0c0c0c8c8d55555555555544c7e0f1f84c2e87c2e80e0387e1f87e1f9540c0c0c0c4c4c0f0f0f178700c0304c4c4c0c0c00c030300f55501303c0300c00130b0130b05555140545141383e0380e21704c2e13a13130b0ba21f1540c0c0c0c3c3d0f0f0f03000f0030005c000000000555410040000f83e0380e1785e000b0015400c0c0c0c4c3c3c4c2c2c2c2c5cdc2c5c5c2c2c2c0c003c002c1700c40870b02c0302c0b00001544102e0b82e0b80b03c3c00300002c004100b82e00b031b03030303030b17170b0b0b0b0b0b0b170f0f0f0f03002c170000f03102c0b021c001544102e0b82e0b80b00b1703c2c0305c0b0b0303030317171717030000000005c870003c00c001700555410000400b82e0380e0b82e001f0002c55030303031717170f170f17030300300c0c5c171700c0c0300d500300c170b0170b0017055550545151141f87e0380e170ba170ba07e1717087c55030303030303030303030303555540d875555550f540d4551150b4547e1f80e0387e1f87e1f955590b5030300000c3c0c003c3c00000000000000000001d0741c1d41c1d40d07400004e0f84c2e84c2e80e1b8000181d030303030f03870f0f03030f0f0f0000000004c00f004c1b0004c0000c01b000000000000000001d0741c1d41c1d40d07418700007001383e130ba130ba0386e0000a00b00060740c0303000f0f003030000000000000000000000741d0340d030350707500000f83e0380e270ba270ba000060740c3c0e1c0c0c0c0c0c3c0c0c0c0c000000000f003c003000c00300c00030000000000000000000741d0340d0303503075061c0001c003e0f80e0380c0e80c2e80002802c00181d030300013130000f0300c0000000000000000001c1d41c1d41d0740d074100009c2e89c2e83e0f80e1b8000181d03002c00f0300c0000000b002c00f003c003006c000741d0741d0341d061c0001c2e0b82e0b80e0b80002802c2c181d0303030f0f130f0f0303030f03870000000003c0003c0f0003c00f000c01b0000f0000000000000001c1c1c1d41c1d0f50741d0341d061c0001c003c2e83c2e83e0f80e1b80002802c00181d03030304c00300130000c001700000000001d0740d0340d41d401c004e0f80e0385e1780002c0060740c0c0c131300003030000000000000000000000741d0340d0303507075000001383e0380e130ba130ba000060740c0c0c0c0c3c0e1c0c4c0c0c0c0c0000000030013003c003000c00300c00030000000000000000000741d0340d0303503075061c0001c004e0f80e0380c0e80c2e80002802c00181d004c3c3c4c4c6d0c0d0c6c4c0c00000000000000000001c1d070741c1d41c1d41d07400004e0f84c2e8bc2e8be2f8000181d030303030f03870f0f03030f0f0f000000000b0b0b0b0b0b0b0b0b0b0b0b030b0b03000000000000000741d07075070750341d000741d00030f038703030303030f03030303000000000b0b0b0b030303030303030b030b0303000000000000000741d0340d0303503075000741d000303030f0f130f0f0303030f0387000000000b0b0b0b0b0b0b0b0b0b0b0b030b0b030002c0b00000000000007075070750741d0341d000741d0003030304c003002c2c2c2c0c0c0c0c2e0b0b000000000741d0340d0341d0741d0003030303030f0387031303030303000000000c00b0b0b0b030303030303030b030b0303000000000000000741d0340d0303503075000741d00 24 16777215 10 1023
def hc_66_12 : Nat → Nat := unpackHintV5 0xcd38d2c42246be796ab89978b111e2aa29baa0826a9ba13894b1bc8e998689e12e8339aa784abc72e9586e09386719bc5fb1da55ca7a50e93849d9c44331aa38f2903359662e693c2741ca23c8de1e116e16d1d01348e20dc96006f9b40001be 0xb0b0b0b0f030f0360b03000000000000000741d0341d0344000000b0b0b0b0b0b0b0b0b0b0b0b0f1b03030f0f03030f030f0360b030f0f130f0f003c870b02c0305c0b0b0b0b00b0b03c0b02c0b02c0302c0007075070750741d0341d0341d107041c0b0b0b0b13030f0360b030003c87000004c02c0b002c4f000c01b0000000000000001d0740d0740d1000101c0002c2c2c2c6c0c6c0d82c0c2c2c2c2c0c6c6c0c2c2c2c2c2c2c2c2c0c2c2c0c2c2c2c2c1d0740d0740d0741d0741d0741c1c1c3c1c1c1c6c0c6c0d5070701c1c1c031b1b03070b0701c1c1c031b1b030741d0303030303540d870741d0741da07070ba070781e80e1baa981d055403030303030303030303030340f0f0f1403c3c00c0304c0f08c2c08c2c00c030015555555450504e0f87c2e87c2e80e03885c21f154003030303030303030303030303c870f0f00f0f0f0300c1303c130b0230b00300c005555555540d87141444d50f544d17554bd5540d0545c0150b0544e0f84c2e87c2e80e03885c21f155590b5030303030000550f0f50303000000000000000005554000500000f83e0380e001f0ba1f0ba00550303030303c87000003c00c003000000000000155550361c000440010f543d50340001000050400000150f83e0380e000202c00155590b500b0b03030303030303030b02c0f100c0315555550361c510b542d50f543d503415170542e0b82e0b80e03882c555642d40c0c0c0c000000000155550361c00010f543d503400011700000543e0f80e038000155590b5054503030303030303030303030317130500f100c030ac2c0ac2c03c0f00c030015555555450507c2e87c2e83e0f80e03885c21f1540030f031b0303030303030303030303030f0f2f0f0f003c870300c0f0f0b00f0b03c0f03c0300c0043d075555555540d87141443d5543d0f5543d50f540d04545d1700542c150f0ba0f0ba0f83e0380e217087c555642d40c0c0c0c003c001313555030300000000000000000555540d870001400004e0f80e038007c2e87c2e801540c0c0c0c00002e0b0b030303030000000000555540d8700550044d50f540d000042d50b50000540c0c0c0c000f21c002f003000c000000000000555540d870001100044d50f540d000000050400000151383e0380e0000a00b000555642d415500c0c0c0c0c0c0c0c0c0c0c0c4c0f0dc5c0dc5c00c03103c2c2c500b0b0030300c0302c0375555555514140b82e0b0ba0b0ba0380e20b082c55000c0c0c0c0c0c0c0c0c0c0c0c4c0f02c2c02cbc00c0300f21c2c2c02c2c2c0c0c0300c0b01555555550361c505113543d50b42d550b5550341500542c150b82e0b0ba0b0ba0380e20b082c555642d40c0c0c0c0000000001542c2d40c0c000000000015550000014002e0b80e03800002c2e82c2e9540c0c0c0c00000f21c0000000b003000c000000555540d870000011043d50f540d0000000042c00014100542e0b80e0380000080b0555642d415140c0c0c0c0c0c0c0c0c0c0c0cac5c0ac5c03c0f00c0302c2c1402c40300c005555555514140b0ba0b0ba0b82e0380e20b082c55000c2c0c6c0c0c0c0c0c0c0c0c0c0c0c0c2cbc02c2c03c0f00c0302c2c2c2c2c00f21c0c03001555555550361c50510b5550b42d550f543d503415004542d0b0542c2e82c2e82e0b80e03882c20b155590b5030303030000000f003000000b0b555030300000000000555540d870000014002e0b80e03800002c2e82c2e9540c0c0c0c000000000002e0b0b030303030000555540d8700005544d50f540d0000000042d50b5540c0c0c0c0000000f21c030000002c00c003000000155550361c0000044113543d5034000000000014100542e0b80e038000002802c155590b50030303030000005550361c4d0f44d13544d43540d000050b82e60b40c0c0c0c00008c4dec3dec3c8c4c0c0c00000000000000000155550001400002e0b80e038002c2e82c2e8002c55030303030000000f000c0030000b0000021c000555540d870001100048d50f540d00000005040000010b0542e0b80e03800080b0000b155590b500303030300000005550361c4d0f44d13544d37540d000050b82e60b40c0c0c0c00000000000bc4cbc3cbc3cbc4c0c0c000000000015550000014002e0b80e03800002c2e82c2e9540c0c0c0c0000000008700000f000c0030000555540d8700000110550f540d000045c000000014100542e0b80e0380000080b0555642d40c0c0c0c0b002c003000c00000000000000087555540d870110000048d50f540d0005042c000000000150b82e0380e0202c0000155590b5 24 16777215 10 1023
def hc_66_13 : Nat → Nat := unpackHintV5 0xcfaa1ec9419ac32188b4cb96b0a908aab17ea13260988a2a9279848ce1667f536479f95673b1927058d66929cc5e82aa5879824e6a8449893843a9783a5a54311a502e28bc29413a23d15c22f0381e61241db02c17d9760e1272055a2e000156 0x13030f030701c1c1c1c00c0d42d03031303c0306c13170131300700b00302c0b0b00707002c0370741d0341d0303507035107041c0b82e0382e0b0ba0b0ba20b082c6074001c1c1c5c1c5c1c1c1c5c1d6c1c3c1c4c6c0c5c0d42c1301c170002c0b000008700741d03030340d870b82e070b0b81c1e80b00b031b03130f0f130b0b0b0b17170b17370b0b0b10130002c1701707021c2c0b00c000b02c000741d0300070b82e0b82e001c1c1c3c1c1c1c4c1c1c1c1c1c2c1c1c1c1c1c1c2c1c2c4c0c3c0c2c2c0c0c2c6c0c0d51303c0b0b00b0070070700306c03c870b0b00b0b0b07070b0b0070701c00c0c0b00c0b001d0741c1d41c1d40c0c0c0c0d50361c41c10702e0b82c2e82c2e81c1c2c2e81c1e07a0382e20b082c60740d0f0300000000000001b0230000003440d0740000001c0382e0b82e00000060743c0c3c0c1c1c2c2c1c1c1c1c1400000000000f00000000000741d03440c0c00000002e0b80e0b82c2e82c2e8000181d0707070f070f0707070f070f030f0354000000000f21c00000000000b0070000701c0003006c0000000741d0303030303540d8700000101c02e0b81c1c2c2e81c1e07a0382e00000202c181d0f030f03070700701c1c0c0d42d03030f03c0306c23170231700b0b00703c870302c0b0b007070000741d0350750303507035107041c0b82e0382e0b0ba0b0ba20b082c6074001c3c1c3c1c1c1c5c1d0c1c1c1c5c1c5c5c0c6c0d40f0b01c1700017000000741d03030340d8740b82e070b0b81c1ea006c0c2c0c2c5d1c2c2c2c2c2c2c2c5c5c3c3c3c3c402c170003c05c1c0b02c0870000741d0300070b82e0b82e001c1c1c1c1c2c1c2c1c1c1c1c1c2c1c1c1c1c3c1c1c1c3c2c6c0c0c2c2c0c0c3c0c3c0d50b00b0b00f03c070070700306c0b0b0b0b0b003c87070b0070700302c0007075070750741d0303030303540d87107041c0b0ba0b0ba0b82e07070b0ba070781e80e0b882c20b181d0344c0c000003000004c870000001b06c0001c070000003440d07400000001e1c0382e0b82e000000060744c0c3c0c1c1c1c1c1c1c2c2c140000000000000000000001d0740d1030300000000b82e0382e0b130b0ba0b0b84e8000181d13030f03000000000001383c4c0d0b0300000741d034400000d0741c1c1c3c1c1c1c4c4c0c3c0d500000000000000000000b82c2c1c1c2c2c1c1c1c1c1c1c2c0c2c2c0c00001d0740c0c0c0c0d50361c00001d0741c1c1c3c1c3c1c1c1c4c1c4c0c3c0d5000000000003c8701c0b000000c000000b0070000701c000300c01b06c0000000741d0303030303540d8700000050070700b82e07070b0ba070781e80e0b8000002802c181d1b031b032313230f230f231305000000000002c000000000001d0740d1030300000000b82e0382e0b0ba0b0ba000060741c1c1c3c1c1c1c8c6c0c6c0d50000000004c00f001c0001c070000c03006c1b0000b0001c0b000000021c0000741d0303030303540d87000101c0002e0b81c1c2c2e81c1e07a0382e000202c0002c60746c6c1c1c0d40c0000008c0b021c04c1303c0f00c1b04c13008c5b00001c1c0d03441c0b82e20b06c0c6c0c8c4cfc3cfc3c8c4c140000000000000000000001d0740d1030300000000b82e0382e0b0ba0b0ba000060741c1c1c3c1c1c1c6c0c6c0d50001c1700000000000000021c0013003c0070000701c0003006c00001d0740c0c0c0c0d50361c0000040700b82e07070b0ba070781e80e0b80000080b060741c1c1c3c1c1c1c8c6c0c6c0d502c00b001c0b0001c070000c00b0000000000000000000000021c1d0740c0c0c0c0d50361c0407000000b82e07070b0ba070781e80e0b8080b0000060746c6c1c0000c6c6c0c0004c0871300000870741d0b82e08c6c6c1c1c0d40c0004c004c0b000021c4c00f000c1b04c13008c00001c1c0d03441c0b82e08c82c1b031b031717171710000001721c0004c00006c05c001d0740d1030000001c0b82e0382e0b82e002f00181d0170b0b05c0b0b0070f0713070b0737070b070b500700003c2c0700003000c0c0d0361c02c2c1c2c2e0707a00f0f0b07001b031b0323133f0f3f0f2313050000000000000000000001d0740d1030300000000b82e0382e0b0ba0b0ba000060741c1c1c3c1c1c1c6c0c6c0d50001c0000000000702c0000000008704c00f001c0001c070000c01b00000741d0303030303540d8700000050070700b82e07070b0ba070781e80e0b800000202c181d002c2c2c2c2c2c2c2c2c2c2c2c4c0c3c0c4c4c0c0c4c6c0c0d82c0c0f21c3c3c03c3c3c2c0b00c1702c0b02c2c02c2c02c0b00c0b0001d0741c1d41c1d40d0740d07441c10702c2c2c2c3c0c3c0d82c0c0f21c0000000f00b002c003006c000000000000000741d0341d0344000407000 24 16777215 10 1023
def hc_66_14 : Nat → Nat := unpackHintV5 0xd1783acbc96cc4a9c8bbe232b4f9baafc14eaa914ca3c1b49e914c9a112099a81a97708e90e9a2873a6c7f020e70eb867028306c290066317e5cd25853ca424a924e443996364b7c3129482af18e27a8d22089c8165a8c0de21e084966000212 0xf0f42c002c2c6c0c6c0c000000000003f133f0f3f0f3f130007070000000005545000005000b82e0382e00001f02c2e82c2e9546c0c6c0c0000000000021c003c003006c0001550361d54000001410704fd50f541d000000000005040150b82e0382e00001f0080b0555642d55131b030f1b03070703031b070303130f0f1313172b0ac5c4c031b1b03130f0f13130b2308c2c4c031b1b03233f233f55555555555551383e130ba1f0ba0386e1f87e1f87e551303030f0303131303c5c0305c1313130304c4c4c6c015404c0f00c1b0004c2c04c2c15554501514504e0f80e1b885c130ba130ba21f15402c0c6c0c4c3c3c4c2c2c2c2c5cdc2c5c5c2c2c2c01c0005d021c2c0b00c0b02c000551040b82e0b82e00b1b1b030b0b03030b17170b0b0b0b0b0b0b17470f0f0f0f0070001740b02c08700551040b82e0b82e1b031b031717170f170f170305c1c1c1c05c1700c1b17171500306c170b0170b00055550545151141f87e0386e170ba170ba217087c551b031b03031b1b03031b1b035540d87555555550f541d4551150b4547e1f80e1b87e1f87e1f955590b5131b07070346c0c4c004c130007003c00306c1305c00000001c1c0d07441c138ee0ec82c001302c4c6c1c1c0d1b03000000007070341d138be131b07001c1c1c1c0c6c6c0c1c1c0d1b03004c1304c4c4c4c4c4c1304c08c2c8c0b04c2308c8c1c1c1d0740d0742e0b84e2f8ecec4c6c0c3c6c0c1c1c1c0c0d46d0303130f0f13031b1b03131705c4c130f0f13031b1b03130b2308c2c4c2323070741c1d0341d03035070350741d0741d1383e0386e130ba3b0ba3b8ee3b88e60744c0c3c0c1c070707070030351340c0c1c03c00c1703c3c01c1c04c0f00c1b04c2c04c2c0001d0740d0740c0d41c0d441c10704e0f80e1b84c2e84c2e885c223181d001c1c1c3c1c1c1c4c1c1c1c1c1c4c1c1c1c1c1c1c4c1c5c4c0c3c0c4c4c0c0c4c6c0c0d503c870f0f00f0f0f070717170070701c00c1704c0f04c2c04c2c01c2c01c1c00c1b0001d0741c1d41c1d40c0c0c0c0d50361c41c10704e0f84c2e84c2e81c1c2e81c1e07a0386e217088c60746c3c00001c1c0d0f0300000001b00000000000003440d07400001c000386e1389e00000060743c0c3c0c1c1c3c3c1c1c1c1c14000f0000000000000000000741d03440c0c00000003e0f80e1b89c2e89c2e8000181d0707070f070f0707070f070f030f03540f21c000000000f0070000701c0003006c00000000000000000741d0303030303540d87000101c0003e0f81c1c2e81c1e07a0386e000202c00181d0f030f03070700701c1c0c0d43d03030f0f00703c870305c13130070700f03c0306c230b0230b0000741d030350740d870303507035107041c0f83e0386e270ba270ba217088c607402c2c1c1c1c2c1c1c1c2c1c1c1c3c1c1c1c3c2c0c2c0c3c0c3c0d50b02c0f01c07170070700305c0741d0741d0303030303540d8710702e0b82e0b81c1c2c2e81c1e07a0382e20b181d0707070f0707070f0f030f03540000000000000000001d0740c0c0c0c0d50361c000003e0f81c1c2e81c1e07a0386e00006074007070707070f070f07070707070f070707070f0707070f0f1b03030f0f03030f030f03543c3c4c3c3c00f21c1c5c01c1c00c1703c3c2c03c2c0f03c0f01c2c01c1c00c1b0001c1d41c1d41d0740c0c0c0c0d50361c41c10703c2e83c2e83e0f81c1c2e81c1e07a0386e217088c60740d1303000004c870001b06c0001c070000000000003440d074000001e1c000386e1384e000000060744c0c3c0c1c1c1c1c1c1c4c4c14000000000000000000001d0740d1030300000001383e0386e13130b0ba130b84e8000181d13030f0300001383c4c0d0b0300000000000741d0344000d074001c1c1c3c1c1c1c4c4c0c3c0d5000000000b82c2c1c1c2c2c1c1c1c1c1c1c2c0c2c2c0c000000000000001d0740c0c0c0c0d50361c001d074001c1c1c3c1c3c1c1c1c4c1c4c0c3c0d50003c8701c00000004c01c0001c070000c03006c1b000000000000000001d0740c0c0c0c0d50361c0001401c1c0004e0f81c1c2e81c1e07a0386e0000a00b00060744c4c4c4c0c3c0c4c4c0c131b0131303c5c07070070700305c1303c130b0130b00306c000741d07074070700341d107041c1383e130b84e84c4c2c2e80e1b885c223181d13030f03070f0f17870f0f13131004c001b01700000000001d0740d10300001c001383e0386e1785e0000060746c0c6c0c5c5c3c5c3c5c5c145d0305c5c1700c1b171701c1c1c00c1b05c2c05c2c005c01d0740d0740c0c01c0d00741c1c1070be2f80e1b85c2e85c2e885c22f181d 24 16777215 10 1023
def hc_66_15 : Nat → Nat := unpackHintV5 0xc63184bd8a2ab649d0afa1aaa5fa6aa119389a41b69429868f992488c9b47e629a79713c7491386d69ca66c1aa5ca28857994250c1b649d9ba3fd2823ae13c35b94a2e21e62aa8de24c9781dc1c21a00f014915c0da1bc0671cc03b8ae0000ee 0x23133f0f3f0f23130303030305000000000000000000000741d00070701030303400002e0b82c2e82c2e80e038000181d03030303030303030f030354000000000000000000021c13003c003000c00300c00030000001d0750361c0c0d40c0c1c0000040700b82e0380e0303a030ba00000080b060740c0c0c0c0c0c0c0c3c0c0d50303030303030300c0c0303030303030300c2c0c0741d40d87030350303070741d0741da0380e0303a030baaa607415504c0c3c0c6c1c0c0c1c1c0c0d03c500f0f00305c1303c230b0230b00306c005555555514141383e1f0ba1f0ba0386e217087c55004c0c3c0c4c6c0c0c6c6c0c0c0f21c3c3c03c3c3c0c1704c0f04c2c08c2c00c1b0015555550361d54505113543d51345d552f555074151700542c151383e130ba1f0ba0386e217087c555642d43c0c3c0c0001543c3d4001c1c0000000000000015514001400003e0f80e1b8007c2e87c2e801543c0c3c0c0f21c00000f003006c0000000000005540d87550001100043d50f541d000000050400000150f83e0386e000202c00155590b500b0b0b030b030f030f030b02c0f100c17155550361d54510b542d50f543d507415170542e0b82e0b80e0b882c555642d43c0c3c0c0000000001550361d54000010f543d50740000000150f83e0386e0000555642d415141c1c0c0c3c1c0c0c3c0c3c0c5c4c1403c40305c2b0b02b0b00f03c0306c0055555540d5450507c2e87c2e83e0f80e1b885c21f15400f0f1b1b03030f0f030f03030f030f030f0f2f0f0f003c870305c0f0f0b00f0b03c0f03c0306c0055555540d8755141443d5543d0f5543d50f541d0545c0150b0543c2e83c2e83e0f80e1b885c21f155590b513030f030000131355500070700000000000000055515000500001383e0386e001f0ba1f0ba005513030f0300000b82c2c0c2c2c0c0000000001550361d5401540113543d507400010b542d40001513030f030003c87000bc00c01b0000000000001550361d540001410700044d50f541d000000050400000151383e0386e0000a00b000555642d415504c0c3c0c2c1c0c0c1c1c0c0c4c0f0dc5c0dc5c00c1b102c500b0b00302c005555555514140b82e0b0ba0b0ba0382e20b082c55004c0c3c0c2c2c0c0c2c6c0c0c4c0f02c2c02cbc00c1b00f21c2c2c02c2c2c0c0c0b00c0b015555550361d54505113543d50b42d550b55507415004542d0b0542e0b82c2e82c2e80e0b882c20b155590b50f030f03000003c000001542c2d4001c1c0000000015514000014002e0b80e0b800002c2e82c2e9543c0c3c0c00000f21c0000000b003006c0000005540d87550000011043d50f541d000000000005040150b82e0382e00000202c155590b50545070703030b0703030f030f032b1702b1700f03c0306c0b0b0500b0b103c0c0b0015555555450502c2e82c2e82e0b80e0b882c20b15400b0b1b1b03030b0b030b03030f030f030b2f00b0b00f03c0306c0b0b0b0b0b003c870302c0055555540d8755141442d5542d0b5543d50f541d0540150b0542c2e82c2e82e0b80e0b882c20b155590b513030f0300000000000b0b55500070700000000055515000005000b82e0382e00000b0ba0b0ba5513030f03000000000000b82c2c0c2c2c0c0001550361d5400015513543d5074000000010b042d50b5544c0c3c0c0000000f21c030000002c00c01b0000001550361d540000014107044d50f541d0000000042c00014100542e0b80e0b8000002802c155590b5013031b03000000550361d44d0f44d13544d3f541d000050b82e60b46c0c6c0c00008c4cfc3cfc3c8c4c001c1c000000b0000000000055515000500000b82e0382e000b0ba0b0ba000b1546c0c6c0c0000003c003006c0002c00000870001550361d540004400123543d5074000000141000000542e0b80e0b800080b0000b155590b5013031b030000000550361d44d0f44d13544d37541d000010b142e0b982d1b031b0300000000002f132f0f2f0f2f130007070000000005545000005000b82e0382e00000b0ba0b0ba551b031b0300000000021c00003c003006c0001550361d54000004413f543d5074000000010b00005040150b82e0382e00000202c155590b51b031b0302c00b000c00b00000000000000021d550361d540440000123543d5074001410b000000000042c150b82e0382e0202c0000155590b50003c2c03000d87501343d0b42d0740000450b0b60b404c6c4c0c6c0c000001540d8751343d1344d5134dd5074000142e0b982d 24 16777215 10 1023
def hc_66_16 : Nat → Nat := unpackHintV5 0xecf174e43a2edc020ed33234cd3180bf2384b91184b251b0a93248a11208990a0290a21a8af16c85596677d362720174694a2e61120e5b696a56095848e34a42a98e3bd9b43282562cb174235a561f390819697410d22607fa360339300000ce 0x30303030f0f03030303030305000000000000000000000741d0007070103400003e0f89c2e89c2e80e038000181d03030303030f0303030f0303540f21c000000000f003000c00300c00030000000000000000000741d40d8703035030307000101c0003e0f80e0380c0e80c2e800080b00060740c0c00c03030303030303030340c0d43c0304c4c00c0c00c0303c0f08c2c08c2c00c030001d0741c1d41c1d40d40d441c10703e0f89c2e89c2e80e03885c223181d00b0b0303030303030303030b0303030b0303030f0303030f0303542c0b03c0300c0300c0c00c5c01d0741d0750361c0c0d40c0c1c41c0b82e0b82e0380e0303a030ba20b181d03030303030f0303030f0303540000000000000000001d0750361c0c0d40c0c1c00003e0f80e0380c0e80c2e8000181d000c0c0c0c0c0c0c0c0c0c0c0c0c3c0c0c0c0c0c0c3c0c3c0c0c0c0c0c3c0c0c0c3c0c0d50f0f130f0f003c870300c03030031700f0f0b00f0b03c0f03c0300c03030030b000070707075070743d41d0750361c0c0d40c0c1c41c10703c2e83c2e83e0f80e0380c0e80c2e885c223181d13130303030303030303030305000000000000000000000741d00070701030303400004e0f84c2e84c2e80e038000181d0303030303130303030f030354000000002e0b0b030303030303030b030b0303000000000000000741d40d8703035030307000741d000303030303130303030f030354000f21c0000001300300c00306c00300c00030000000000000000000741d40d8703035030307000101c0004e0f80e0380c0e80c2e80002802c00181d03030303131313030300300c0c4c4c0f1700c0300c0c00c0c04c0f00c0304c2c04c2c0001d41d40d0341c1d01c1c041c10704e0f80e0384c2e84c2e885c223181d1717170f170f1703030303050300d1705c030303030300c030170b0170b00300c000741d07074070700340d01d0707041c2f8be170ba170ba0380e21708bc60740c0c00c0c0c0303503030340c0c0c0c4c4c04c5c04c0f00c0300c0c02c2c00c0b00c0c0300c001c1d41c1d41d0740d03441c10702c2e82c2e82e0b80e03882c20b181d000303030317035b03030317031703030313030f0350b04c000b02c000021c01d0740d870340c1c2e0b80e0b80b0130f0f130b0b0b0b17370b17170b0b0b0303030310000300c0870b02c0b02c0003001d07401c01c2e0b82e0b8003030303030303030303030303130303030f0303030b030b03030303030b0303030303544c0f02c2c02c00c0300c0c00c00f21c2c2c02c2c2c0c0c0300c0c0c00c2c00b001d0741c1d41c1d50361c0c0d40c0c1c41c10702e0b82c2e82c2e80e0380c0e80c2e882c20b181d030303030b0b03030303030305000000000000000000000741d0007070103400002e0b82c2e82c2e80e038000181d03030303030f0303030f030354000000000f21c00000000000b003000c00300c0003000000000741d40d870303503030700000101c02e0b80e0380c0e80c2e80000080b060740c0c00c03030303030303030340c0d43c0f08c5c08c5c00c0302c0302c2c00c0c00c030001d0741c1d41c1d40d40d441c10702e0b82c2e82c2e80e03882c20b181d00030303030f030f03170317030303170343030303503c2c00c000c170000001d0740d870340c1d02e0b80e0ba002c5c5c2c2c2c2c2c2c2c5dac3c3c3c3c0c0c0c0c402c170000c0302c0b021c001d07401c01c2e0b82e0b80030303030303030303030303030b0303030303030b030b03030303030f0303030f0303542c02c2c03c0f00c0300c0c00c02c2c2c2c2c00f21c0c0300c0c00c2c0001c1d41c1d41d0750361c0c0d40c0c1c41c10702c2e82c2e82e0b80e0380c0e80c2e882c20b181d0b0b0303030303030303030305000000000000000000c00001d074001c1c040c0c0d00000b82e0b0ba0b0ba0380e000060740c0c0c0c0c4c0c0c0c3c0c0d500000000000000000000b82c2c0c0c0c0c0c0c0c2c0c2c0c0c00001d0750361c0c0d40c0c1c00001d0740c0c0c0c0c4c0c0c0c3c0c0d5000000000003c8700c0000000000b00300c00306c00300c0003000000000741d40d870303503030700000101c02e0b80e0380c0e80c2e8000002802c181d2313230f230f23130303030305000000000000000000000741d0007070103400002e0b82c2e82c2e80e038000181d0303030303230303030f0303540000000013003c00300c00306c00300c0003000002c0000000008700001d0750361c0c0d40c0c1c0004070000b82e0380e0303a030ba000202c0002c60740c0c0c0c0d034000021c04c0f04c13008c4b000c030001c1c1d07441c0b82e20b08c4cfc3cfc3c8c4c0c0c0c0c14000000000000000000001d074001c1c040d00000b82e0b0ba0b0ba0380e000060740c0c0c0c0c0c0c0c3c0c0d50000000000000000021c0013003c003000c00300c00030000001d0750361c0c0d40c0c1c0000040700b82e0380e0303a030ba00000202c181d0303030303230303030f0303540b002c003000c00300c000302c000000000000000000000000870741d40d87030350303070101c000002e0b80e0380c0e80c2e8080b0000060740c0c0c0c0d034004c0000871304c0f03c1304c02312c00300c0007070741d10702e0b82320b004c0c3c0c2c0c2c0d40000f0b00c0000361c0d03070b0b0382e 24 16777215 10 1023
def hc_66_17 : Nat → Nat := unpackHintV5 0xb771c8b1a972ab01aaa082a09dc8ae9cc04297495e9059bc8a89748339d47db9607699c86f21de6c58b26b284c6a403a64497e5d31c65669b24ed9e44ac9044531664071303b414c3569763009582b113e2421bc1f812815927c0d6a0a00035a 0x1b030f0300000000c87000004c00f002c000001550f61d540000044107503546d4000000010b00005040150b82e0382e00000202c1655590b50304c0c0c1b04c1300c0c4030302c00555544d8745051551b61d5542d07450550b61c540e0b82e0b882c20b1655542c1c2c2c2c2c1c1c6c0c3c0c15148c0f08c5c08c5c00c1b02c0b00c0c1400c4005555555514140b82e0b0ba0b0ba0382e20b082c550b0b0b0f0b0f0b0b0b130b1b030f03008c0f02cbc02c2c00c1b02c0b00c0c0c0c0c00321c01550f61d55555450510750b5550b42d550340d51b46d415004542d0b0542e0b82c2e82c2e80e0b882c20b1655590b50030303c2c030143d8742c1d07000d034000045960b400c0c000d043d0b9030303030000000000321c000707000030355500000000550f154000014002e0b80e03800002c2e82c2e96540c0c0c0c0000000000c870004c00f000c000001550f61d540000044107503540d4000000000014100542e0b80e0380000080b05955642d48c3c3c8c00001c1c0008c0c8c6c8c6c8c0c00000b000000000005455000500000b82e0b82e000b0ba0b0ba000b1548c3c3c8c000013003c003006c0002c00000870001550f61d540004400107503546d40001000050400000150b82e0b82e000202c0002c5955642d48c3c3c8c000000000001c1c000bc0cbc6cbc6cbc0c000000015154000014002e0b82e0b800002c2e82c2e9548c3c3c8c000000000870004c00f000c01b00005543d87550000011041d40d51b50000000042c00014100542e0b82e0b80000080b05955642d48c3c3c8c0b002c003002c000000000000000875543d87550110000041d40d51b50005042c000001170000042c150b82e0b82e0202c00001655590b50003c2c030143d8742c1d07000d1b40000450b0b960b400000c0c10f42c2c2e43c1c2c87031b3f230f0f230000000000008701c1c000fc0e0c6c6cfc0c00000001543c55000005000b82e0b82e00001f02c2e82c2e96548c3c3c8c0000000000021c13003c003006c0001550f61d540000044107503546d4000000000014100542e0b82e0b800007c0202c1655590b503030f03870f030f0f0700707070713174b131717131313031b17030f0f13131305c4c06c5d42c0b02c0b08c5d544542e0b82e0b87c5c0c0c3c0e1c3c0c0c0c1c0071307030303030303030317470317170303030f03c87030303030031717140c0b02c0b08c5d540d0744540e0b82e0b87c5c3c3c3c3c1c0171717170b82c2c2c2c2c2c2e0b0b0000000061d61c551042d54003c3e1c3c3e1c1e1c021e1c1717171703c001b01700000000018758715440100003e0f87e1f85e1780002c00551b030f0307000c0d17030304c00170170000000001515440100007e0f80e1b85e178002c005500b031b0307001c1c1c0000031b17030f02c0b0001740870b02c0b02c0b00002c1504102e0b82e0b80b13030f03007000c0c0c0c0c0c0c0c5dcc0c5c5c0c0c0c5c00c000c17102c0870300c0b02c000551040382e0b82e02c2c3c2c4c01c00b17170b0b0b0b0b0b0b173f031b1703170002c0b01740300c087000551040b82e0b82e02c8c3c3c8c1c01717171704c00006c05c02c00000000545510040000b82e0b82e0b82e000b0002c550f0f070700f05c1c5c0c5c6c5c5c5c0c5c5c0f05c17171503c0170b0170b0005c55550545151141f83e1f87e170ba170ba07e1717087c550f0f0f0f0f0f5543d8755555541d40d51b54551150b4547e0f87e1f87e1f87e1f9655590b503030303030303030303030340c0d44c3c3c4c4c5d2c4b171300c0c0c0c4c3c3c4c4c2c8c230b1300c0c0c0c8c8c1c1d070741c1d41c1d40d0341d0741d0744e0f84c2e8ec2e80e038ee3b8ee23981d0303003030300c0d40c0c0d03030303030300f0f00303c0300c130b0130b01303c0300c0007075070750741d0340d107041c130ba130ba1383e0380e217088c6074003030303030303030303030303130303030f0303031303170303030303130303030303540f21c3c3c03c3c3c0c0300c0c00c5c04c0f04c2c04c2c00c0300c0c00c2c0001d0741c1d41c1d50361c0c0d40c0c1c41c10704e0f84c2e84c2e80e0380c0e80c2e885c223181d 24 16777215 10 1023
def hc_66_18 : Nat → Nat := unpackHintV5 0xdd3964d76974cd428ac48a2ebf3156b67a2eb12156ab4178a2da1a96bb088a1b287fea8c7ac9487319ec6c31ba624a7a5d593c5659c050d1624a49a23f7ab43a095c3321ba3100883038322da8a4239a841e49541642020f19ca04f28a00013c 0x403c3c3c3c5c5c5c5c0f0005c8700000003c05c00c00007441c00741d00000702e0b82e0b82e0b8009c00607414003c3c3c3cdc6cdc0cdc6cdc0c0000000000000000001d107070000741d00000b82e0b0ba0b0ba0b82e000060755071b0703070707030f0f0f0f01c0000000001c0b000003c00000008701c0001c070003c00f000c01b00000707070707543d870741d000000500707007070b0ba070781e82e0b82e0b800009c0202c181d60b0b0303030303030303030b0303030b0303030f0303030f0303002c0b03c0f00321c0c0c00c0c6c2c0b02c0b00c0300c0c00c2c0001d0741d0340d0340c0d40c1d441c107182c2c2c0c2c0c3c0c3c0c00000321c000b002c00f003c01b000000000000000741d07440d07400040700060b0b0b0b0b0b0b0b0b0b0f0f0f0f0f0f0f0f0b030b030f030f03002c0b03c0f00c0c0c0c0c00321c2c0b02c0b02c2c02c2c00c0b0001d0741d0741c1d41c1d40d07441c107182c2c0c0c0c0c0c0c0c0c0000000321c0b002c00f003c003000000000000000741d07440d03400040700060b0b0b0b0b0b0f0f0f0f0b0b0b0b0f0f0f0f0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0741d0741d0741d0741d0741d541c6c1c0c1c1c1c0c3c3c3c3c1c1c07070703c3c3c3c1c2c1c07070703c3c3c3c1c1c1c1c1d50f61c1d0741d0741d0741c1c2e81c1e07a0f83e2789e2789e2789e60740c0c0c0c3c0e1c3c3c0c0c3c3c3c3c3c3c3c4c4c4c132f1300c6c6c0c3c3c3c3c4c2c4c130b1300c6c6c0c8c8c8c8d550f61d5551341d55555550750741d550340d550340d51b46d51544542d150f83e130ba130ba0386e1f87e1f87e5955642d40c0c0c0c0c3c0c3c0c3c0c0c0c0c3c3c3c3c3c4c0c0c0c0c0c0c0c032f0303c3c3c3c3c4c0c0c0c0c0c0c0c030b0308c8c8c8d550f61d555550341d555550750340d50346d50340d550341d551544542d150f83e0380e0303a030ba1f87e1f87e5955642d400f0f0f0f13131303131b130303c870f0f00f0f0f1705c0f03c130b0130b02308c005543d8755544d07555141441d41d0700445540d51b504545d1700542c150f83e130ba130ba1f87e217087c5955642d43c3c3c3c00002e0b0b0b0b0b0b00000000005543d87550042d540107503546d40001042d50b50000543c3c3c3c3c4c000f21c000f003006c0000000000005543d875500005041c00107503546d4000100005041c00000150f83e1f87e0000a00b0005955642d40c0c0c0c1c1c0c0c0c0c0c0c15505c0f100c0c0c50171707303c0300c2f0b02f0b0005555555514141f83e0380e1f0ba1f0ba217087c550303030303130303030f0303005c0f00321c0c0c00c0c6c0f00c0300c0c00c2c001550f61d55555450510750340d50346d50340d5503554151700542c151f83e0380e0303a030ba217087c5955642d46c0c3c0c000001c1c001546c5d4000000000000015154001400007e0f80e1b8007c2e87c2e801546c0c3c0c000321c0013003c01b0000000000005543d87550001100041d40d51b500004000141000000547e0f80e1b800080b0005955642d40c130303100c1300c1b04c1300155551361d14145546d875551341d1545d8705150386e1384e217087c595551b070f0f0f0f07071b030f0305451703c030305003100f0bc2c0bc2c00c1b0015555555450507e0f87c2e87c2e80e1b885c21f1545c4c3c3c6c3c3c3c6c4c6c6c0c3c0c01703c0303030303000c8703c1b0b0170b00306c005543d8746d07555555141441d46d5545d175540d03546d1b504545d1700542c151f83e1b0ba170ba0386e217087c5955642d40c0c0c0c00000321c0707000030355500000000000000550f154001400007e0f80e038007c2e87c2e8016540c0c0c0c00000321c13003c0030000000000005543d87550001100041d40d5035000000050400000151f83e0380e000202c001655590b50b033703878702e1d0707000c6c0d7340b0b372f07870b03c4c2cdc5c2e1e1c2c8741c1d07011740c6c1702c00f0f0f0f0b0b0b030b1b0b030f03c0b0b00b2f0003c870b0b00b0b0b0b0b02c02c05543d8755542d07555141441d41d0700445540d51b505401150b42c150b82e0b0ba0b0ba0b82e20b082c5955642d43c3c3c3c000000000002e0b0b0b0b0b0b00005543d8755000042d5507503546d4000000010b042d50b5543c3c3c3c3c4c0000000f21c230000002c00c01b0000001550f61d540000014107041d40d51b50000000042c0001410700542e0b82e0b8000002802c1655590b503030303070703030303030305542303c0300c23170231700b0b02c2340303031402c2c0015555555450502e0b80e0382c2e82c2e882c20b1540c0c0c0c0c4c0c0c0c3c0c0c02303c0300c03030032f00b0b02c2300c870303003030b005543d87555555141441d40d03540d1b540d035540d550540150b0542e0b80e0380c0e80c2e882c20b1655590b51b030f03000000000000707000550b0b5000000005455000005000b82e0382e00000b0ba0b0ba55 24 16777215 10 1023
def hc_66_19 : Nat → Nat := unpackHintV5 0xf56166edc9e6e699cce14954d8e21ad0aa0ec29386bc997eb31a60b2a81cb2002aa93a329b8b6c960162903174864a7a7e120e78517072119063db8e5de17e5442684b9a2a46016638536c32817428329422517818927012b17809425c000250 0x3c3c3c3c0000000000001c1c04c0c4c6c4c4c4c0c000000011554000014002e0b82e0b800007c0b0ba0b0ba550f0f0f0f000003c00000008703c00f000c01b000043d8755550000005041c107503546d4000000010b00005040150b82e0b82e00001f0080b0555642d43c3c3c3c3c0f07070701303171b131717030f03c3c3c1705c543c0f08c2305c2c04c2c00155541514544503e0f87e1f85c2e84c2e885c21f1543c3c3c3c3c3c3c3c3c3c3c3d0f61d5555555507503546d51544542d150f83e1f87e1f87e1f87e555642d4143d0f03c3c3c3c5c5c5c0c5c6c5c0c3c0f0f0f01c1c1c5c5c1703c0f05c2c05c2c0005c01d0741c1c01c1d01d0740741c1c10703e0f85c2e85c2e89e27885c227181d030350340c0c0c0c0c0c0c0c0c030300f03c17170070700300300f03c3f0b03f0b00300c000740d07075030350340d107041c0f83e270ba270ba0380e217089c60755030303030303030303030303030703030303030307030703030303030f0303030f0303001c1c5c5c01c1c0700f03c00c870303003031b070b0070700f03c0300c03030030b0000707070707543d870340d0303503075107041c07070ba070781e83e0f80e0380c0e80c2e885c227181d05000f030f031b1703030707030300000000c0000000000001d107070000341d00000f83e270ba270ba0386e00006075507071b1b03030707030703030f030f0300000000c870001c0001c070003c00f006c00000000000000001c1c1c1c1d50f61c0d07400040700007070ba070781e83e0f80e1b800080b00060748702e1c0871702c870f030f030f0f50f43c3c0c0c01c03030f03c030300700c8703030070300f03c0306c0b00b000070750743d870341d0707507075107041c0f83e0386e270ba270ba217089c6075507071717070707070707070707071b0f0f0f0f0f0f0f0f071b0303070703030f030f03001c5c01c1c03c0f00c0c0c0c0c00321c1c2c01c1c03c0f06c2c05c2c00c1b0001c1c1c1c1d50f61c1c1d41c1d40d07441c10701c1c2e81c1e07a0f83e1b0ba170ba0386e217089c6074400c0c0c0c0c5c0e1c0c0c0c0c0c003c05c00c00000000007441c00340d00070003e0f85e1780e038000181d050003030303030303030303030300000000000000000007441c1c0000d03400003e0f89c2e89c2e80e038000181d540c1c0c6c0c0c0c0c0c0c0c0c0c0c0c0c070000000000321c070000701c000f003c00300000000000000000707070707543d870340d000050070700007070ba070781e83e0f80e03800080b00060740c0d40d03030303030303030300c0c03c0f08c5c08c5c00c0302c0b02c2c01c1c00c00c0001d0341c1d40c0d40d03441c10702e0b82c2e82c2e80e03882c20b181d10030303030f030f03170317030303170343030303003c1c030000c1702c000870300c007000d074070b82e0382e507171707070707070707175b0f0f0f0f03030303000705c000f00c030000001c1c1d0f61c1d07407070b0b81c1e82e0b80b540c0c0c0c0c0c0c0c0c0c0c0c0c1c0c0c0c0c0c0c1c0c1c0c0c0c0c0c3c0c0c0c3c0c0c0070070700f03c0300c0303003007070b0b0070701c02c2c0b03c0321c0c0c00c0c2c001c1c1c1c1d50f61c0d0340c0d40c1d441c10701c1c2c2e81c1e07a0b82e0380e0303a030ba20b082c607414003c0c3c0c2c2c0c0c1c1c0c0c0000000000000003000007441c1c0000d07400002e0b82c2e82c2e80e0b8000181d541c1c6c6c0c0c1c1c0c1c0c0c3c0c3c0c000000000000000321c0000070000701c000f003c00b0000000707070707543d870341d00000101c01c1c2c2e81c1e07a0b82e0382e00000202c181d0f030f030b0b50b42c2c0c0c01c03030f03c0306c23170231700b02c030300700c870303007030000750750341d0707507075107041c0b82e0382e0b0ba0b0ba20b082c6074402c3c2c3c2c2c2c5c2cfc2c2c2c5c2c5c5c0c6c0c00f0702c170000c000300c087007001d074070b82e0b82e541c1c2c2c1c1c1c1c1c1c1c1c1c1c2c2c2c2c3c2c2c2c3c1c6c0c0c1c1c0c0c3c0c3c0c0070070700f03c0b3f00b0b00306c070b0070700b02c0303030303000c87000707070707543d8707075070750341d107041c07070b0ba070781e82e0b82c2e82c2e80e0b882c20b181d050003030303030303030303030300000000000000000007441c1c0000d03400002e0b82c2e82c2e80e038000181d540c1c0c6c0c0c0c0c0c0c0c0c0c0c0c0c000000000702c00000f000000c870001c0001c070003c00f000c0000001c1c1c1c1d50f61c0d034000001401c1c01c1c2c2e81c1e07a0b82e0380e00000202c181d05000f0f0f0f231b2303231b2303000000000000000000007441c1c0001d07400002e0b82c2e82c2e82e0b8000181d541c6c1c0c1c1c1c0c3c3c3c3c00000000070000701c000f003c003006c0001c0b000002c000008700001c1c1c1c1d50f61c1d07400040700007070b0ba070781e82e0b82e0b800080b0000b181d05000f0f0f0f371b3703371b3703000000000000000000007441c1c0001d07400002e0b82c2e82c2e82e0b8000181d541c6c1c0c1c1c1c0c3c3c3c3c0705c00000000000000000870001c0001c070003c00f000c01b00000707070707543d870741d00000101c01c1c2c2e81c1e07a0b82e0b82e00000202c181d541c6c1c0c1c1c1c0c3c3c3c3c0702c000701c000b002c003002c00000000000000000000000870707070707543d870741d0101c000001c1c2c2e81c1e07a0b82e0b82e0202c0000181d 24 16777215 10 1023
def hc_66_20 : Nat → Nat := unpackHintV5 0xd6317ecd1a46c74974be8232b59a3ab220deabd992a302369c51ac95a9aa8c026a8721388049b67bc12274f1b46aea826609385ef9c45851aa4e32884929424251b63d893236a1ba2c9a8227b9382049dc1ab1661351d80dd16006f9b60001be 0x14008c6c8c0c8c6c8c0c8c3c3c8c0000000000000b000000000707010741d07400002c2e82c2e82e0b82e0b8000181d548c3c3c8c1c1c1c0c1c6c1c0c0000000013003c00701c000700003006c0002c0000000008700010f61c1c1d41c1c1c1d0740004070000b82e0707a070ba0b82e000202c0002c681d81400ac6cac0cac6cac0c8c3c3c8c000000000000000000001c1c041d0741d00000b0ba0b0ba0b82e0b82e000060755230f0f2307070703071b07030000000000000000021c0013003c00701c000700003006c00010f61c1c1d41c1c1c1d0740000040700b82e0707a070ba0b82e00000202c1a076548c3c3c8c1c1c1c0c1c6c1c0c0b002c00701c000702c0003002c000000000000000000000008743d87070750707070741d0101c000002e0b81c1e81c2e82e0b8080b00000681d940401c0c6c0c0000f00070ac0b00c00f61c1d07070b070782e0b0ba05002b1b2b032b1b2b03230f0f230000000000000ac000000001c1c043c1c1d0741d00000b0ba0b0ba0b82e0b82e0000681d95230f0f2307070703071b0703000000000000000000008704c00f001c070001c0000c01b000043d87070750707070741d00000101c02e0b81c1e81c2e82e0b800000202c1a076543c3c1c1c1c0c1c6c1c0c3c3c1c1c1c070703c3c1c1c1c070b0710f61c1c1d41c1c1c1d0741d0741d0749e0f81c1e81c2eaaa9a07603030303030303030707030305540f03c4031404c4c03c0f00c0304c2c04c2c0015555555450503e0f80e0384c2e84c2e885c21f1540c0c0c0c0c3c0c0c0c3c0c0c00f03c00c870303003031b0f03c0300c03030030b00043d8755555555141441d40d503540d035540d550545c0150b0543e0f80e0380c0e80c2e885c21f155590b50f030f03000000070705513135000000000000004555000500000f83e0386e00130ba130ba00550f030f030000c870003c00f006c0000000000010f61d55540004400107503546d4000000141000000543e0f80e1b800080b000555642d40c0f0303100c0f00c1b04c13001555545051544d44d151305150386e1384e217087c55550f0f07070f070f0f0f030f0305450f03c030305003103c0f04c2c04c2c00c1b0010f5555555514140f83e130ba130ba0386e217087c550f0f0f0f0f0f0f0f0f0f1b0f030f03003c0f00c0c0c0c0c00321c3c0f06c2c05c2c00c1b0010f61d5555555450510751b5551745d5503546d4151700542c150f83e1b0ba170ba0386e217087c555642d40c0c0c0c0000001c1c00c0d554000000000000011554001400003e0f80e038004c2e84c2e801540c0c0c0c00000321c0f003c00300000000000043d87555500005041c00107503540d4000000141000000543e0f80e03800080b000555642d40c0c0c0c0c0c0c0c1c1c0c0c15503c0f00c0304c5c04c4c02c0b100c500b0b0005555555514140b82e0380e0b0ba0b0ba20b082c5503030303030f0303030f0303003c0f00c0300c0c00cbc02c2c0b03c0321c0c0c00c0c2c010f61d55555554505107503540d50340d55035541523004542d0b0542e0b80e0380c0e80c2e882c20b155590b50f030f0300000000c0000001c1c1542c2d4000000011554000014002e0b80e0b800002c2e82c2e9543c0c3c0c0000000321c00000f003c00b00000043d8755550000011041d40d51b5000000000005040150b82e0382e00000202c155590b50303c0c0c1b04c1300c0c4030302c005555514145513513450542c540e0b82e0b882c20b155542c2c1c1c2c1c2c2c3c0c3c0c15143c0f04c4c04c5c00c1b02c0b00c0c1400c0c403005555555514140b82e0b0ba0b0ba0382e20b082c550b0b0b0f0b0f0b0b0b0f0b0f030f03003c0f02cbc02c2c00c1b02c0b00c0c0c0c0c00321c010f61d5555555450510750b5550b42d5503546d4152300542c150b82e0b0ba0b0ba0382e20b082c555642d40c0c0c0c0000000000001c1c00c0d554000000011554000014002e0b80e03800002c2e82c2e9540c0c0c0c00000f000000c870003c00f000c0000010f61d55540000014107041d40d50350000000042c00014100542e0b80e0380000080b0555642d43c3c3c3c0000001c1c04c0c4c6c4c4c4c0c000000000000011554001400002e0b82e0b8002c2e82c2e8002c550f0f0f0f000003c00f000c01b0000b0000021c00043d8755550001100041d40d51b500000005040000010b0542e0b82e0b800080b0000b155590b50f0f0f0f0000000000000070701303131b13131303000000004555000005000b82e0b82e00000b0ba0b0ba550f0f0f0f00000000021c000f003c003006c00010f61d55540000044107503546d4000000000014100542e0b82e0b80000080b0555642d43c3c3c3c0b002c003002c0000000000000008743d8755550110000041d40d51b50005042c000000000150b82e0b82e0202c0000155590b5 24 16777215 10 1023
def hc_66_21 : Nat → Nat := unpackHintV5 0xf229c4e8f24ee3097adcb994d7495ccfa1eac77a0aba035eb43174ab6a32a3320e9573708f5188868a328229187d59347b38886dfb5066e9c45d5a6454f21a4fb94e49d17a3c5b5e3689742dc232258a0e1fd96c1283560f18da08d192000234 0x150f0f0f0f07070703071b07030000000000b82c2c1c1c1c2c1c2c1c1c2c2c2c2c000000000000010f61c1c1d41c1c1c1d074001c1d0742c0150f0f0f0f07070703071b07030003c8700001c00003c01c0700110000c01b000000000000000010f61c1c1d41c1c1c1d0740001401c1c0003e0f81c1e81c2e89e2780002802c001a0761117134b545c4c5c4c4c4c0c0c6c0c5c0c3c0e1c3c0c3c3c1c1c3c3c4c1702c0b02c0b01c0701d0741c1c2e0b82e0b8440c0c0c0c0c0c3c0e1c5c0d1d51703170303030f03030307070f0f0305c0b02c0302c0701c0303503070741c1c2e0b80e0b818721c8705c5c5c5c3c3c3c3c1700f0000000000001c1870761c1d074001c001785e0f83e2789e000006074143c1745c6c5c0c5c5c5c0c3c3c1c1c1c5c5c0f05c1705c2c05c2c00f00001c1d01c1c01d0741d0740741c1c10705c2e85c2e89e0f8be2f885c22f181d0303503030340c0c00c0c0c0303030307070171701703c0300c2b0b02b0b02b03c0300c0003035070750341d0340d107041c2b0ba2b0ba2783e0380e21708bc6075503030303030303030303030303130303030f0303030703070303030303070303030303005c0f01c1c01c5c00321c0c0c00c0c6cfc0f01c1c01c2c00c0300c0c00c2c0010f61c1c1d41c1c1c0d0340c0d40c1d441c10709e0f81c1e81c2e80e0380c0e80c2e885c22f1a0760500070703031b1703031b030f03000000000000000000000707010740d0740000ac2e8ac2e89e0f80e1b8000181d546c0c3c0c1c1c0c0c1c6c0c0c0000000321c0013003c00701c00070001b000000000000000043d87070750707070341d000101c0009e0f81c1e81c2e80e1b800080b000681d86c0c3c0c6d0f0f0f0f5030300700c0c5c0f00c0700c0c01c0c0ac0f00c1b0ac2c0ac2c0001d41d40d0741c1d41c1d441c10709e0f80e1b8ac2e8ac2e885c22f181d545c4c3c3c3c3c6c4c1c1c1c1c1c1c6c1c1c5c5c1c1c1c1c6c0c3c0c1c1c0c0c1c6c0c0c01703c07070071700303030303000c8703c07070070b01b0b0170b00306c0043d8707075070707070707075070746d40d07441c10709e0f81c1e81c2e86c2e85c2e80e1b885c22f1a0760500030303030303030303030303000000000000000000000707010f070740d0340000ac2e8ac2e89e0f80e0380001a076540c0c0c0c0c0c0c0c0c0c0c0c000000000321c13003c00701c000700003000000000000000043d87070750707070340d000101c0009e0f81c1e81c2e80e03800080b000681d84005400006c0c5c0c2c0c6c0c1c0f0002c0b00021c2c0b02c0007041d01c2e0b82e0b8005c1cac000051b03170307031b030b03c000b02c000021c041d0f61c1d07070b82e0782e02e8401cac5c1c2cdc5c2e1e1c0b0b21d0707550001541d0070707070f0f0f0f07070703071b07030b0b0b030b1b0b030f03c070700700b0b00b03f003c870b0b0070701c01c1c2c2c02c2c2c2c2c0b00b010f61c1c1d41c1c1c1c1d0b50707070750741d107041c0b82e0707a070ba0b0ba0b0ba0b82e20b082c681d950f0f0f0f07070703071b070300000000000000000000b82c2c1c1c1c2c1c2c1c1c2c2c2c2c00010f61c1c1d41c1c1c1d07400001c1d0742d50f0f0f0f07070703071b0703000000000003c8700001c0b008c000000b00701c00440003006c00000043d87070750707070741d00000050070700b82e0707a070ba0b82e000000a00b0681d80c0d40c0c0d0303003030300c0c0c0c8c5c08c5c08c0f00c0301c1c02c2c02c2c0b08c0c030000c0d41c1d40d0740d03441c10702c2e82c2e82e0b80e03882c20b181d100303030317036b03030317031703030313030f0300705c00000b021c0c03001c0341d01c2e0b80e0b944c3c3c4c1c1c1c1c5cac1c5c5c1c1c1c0c0c0c0c005c0701c000300c000000f61c1d07070741d01c1e0b82e0b80ba540c0c0c0c0c0c0c0c0c0c0c0c0c4c0c0c0c3c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c0c0c02303c070700700300c030300300b0b02c2307070070b000c870303003030b0043d87070750707070340d0303503075107041c0b82e0707a070ba0380e0303a030ba20b082c681d814001c1c0c0c2c2c0c0c6c0c3c0c000000000000000000001c1c041d0341d00000b0ba0b0ba0b82e0382e0000607551b030f0307070303071b03030000000000000000c87000004c00f001c070001c0002c0000010f61c1c1d41c1c1c0d0740000040700b82e0707a070ba0382e00000202c1a0761b030f030b42c2c2c2d40c0c01c03032303c0306c23170231700b02c0301c0303007030000750750341d0707507075107041c0b82e0382e0b0ba0b0ba20b082c6074402c2c2c5c2c5c2c2c2c5c2cfc2c3c2c4c6c0c5c0c01c1702c170002c0b0000c03021c01c0741d01c2e0b82e0b950b0b0b0f0b0b0b130707070707070b07070b0b070707071b030f0307070303071b0303008c0f01c1c01c02cfc02c2c00c1b02c0b01c1c01c2c00c0c0c0c0c00321c010f61c1c1d41c1c1c1c1d41c1d40d07441c10702e0b81c1e81c2e82c2e82c2e80e0b882c20b1a07650100303030303030003c001c2b02c03003d870741c1c2c1c1e0ba814000c0c0c0c0c0c0c0c0c0c0c0c0000000000002b000000000707010f070740d03400002c2e82c2e82e0b80e0380001a076540c0c0c0c0c0c0c0c0c0c0c0c000000000000000000c870004c00f001c070001c0000c0000010f61c1c1d41c1c1c0d0340000040700b82e0707a070ba0380e00000202c1a076 24 16777215 10 1023
def hc_66_22 : Nat → Nat := unpackHintV5 0xefe93974c865b7f24e5b281a2d5587d65e099b08a4cd70827aae0947550040a8d435933326e93a0bf468c68a0a054cf721bc70f95334e073980e4c4b890fc5ab0332b9039149027098418845e8c71fb8678ede1fc6a519424e2090ed4738368804000368 0x303030f0f1b0f0f0303030f03870000000003c0b00000000021c000f0000f03c000f003c003006c00003c1c3d0f070f43c3c3c3c0c6c6c0c0000040700b0ba0b0ba0b82e0382e00000202c02e0b80c0c0c1b1300003030000000000000000000000230f0f230303030323073f48c1cfd00000b82e0380e0b0ba0b0ba00000b82e03030303030f0387031b0303030300000000000000000c0b0021c0013003c003000c00300c00030000008c3c3c8c0c0c0c0c0c0c0d03070340000040700b82e0380e0303a030ba00000202c02e0b80130f0f13131b3703371b1303000000000000000000000130f0f1313071344c1c4d131300000b82e0b0ba0b0ba0b82e00000b82e00000000021c00003c003006c00000000040700b82e0b82e00000202c02e0b80c0c0c0c3c0e1c3c3c0c0c3c3c3c0b002c00b02c000b02c0003002c0000000000000000000000087230f0f231b071b46c1c6d031b1b030101c000002e0b82c2e82c2e80e0b8080b000000b82e030f038703030303030f0303030302c00b000c003000c030000c0b00000000000000000000000021c3c3c3c3c0c0c0c0c0c0c0d03070340407000000b82e0380e0303a030ba0202c000002e0b80c0c0c3c3c6c3c3c0c0c0c3c0e1c0b02c000b02c000b002c003002c000000000002c0b0000000000000870f070f43c1c3d0f0f0f0f031b1b030101c000002c2e82c2e82e0b80e0b8080b000000b82e03030303030f0387031b0303030302c00b000c003000c030000c0b00000000000c1700000000000302c0000021c8c3c3c8c0c0c0c0c0c0c0d03070340407000000b82e0380e0303a030ba0202c000002e0b80b002c003002c000000000000000870101c000002e0b82e0b8080b000000b82e030300000c3c3c3c0c003c3c0000000004b0000000000230f0f2323074748c1d1d031b1b0300000b82e0b0ba0b0ba0382e00000b82e030303030f03870f0f03030f0f0f000000000000000000008704c003c0f004c1b0006c0000c01b0000230f0f231b071b46c1c6d031b1b0300000101c02e0b82c2e82c2e80e0b800000202c02e0b80c030300f00c003c0000001721c000f0030005c003c3c3c3c0c0c0c0c5c5c5c5c00002e0b80e0382e0b8009c000b82e030300c0c0c003c3c00c0c0000000000000000000003c3c3c3c0c0c0c0cdc1cdd370737400002e0b80e0382c2e82c2e800002e0b80c3c0e1c0c0c0c0c0c3c0c0c0c0c000000003000f000000000c0b000021c0f003c00300c00306c00300c00030000003c3c3c3c0c0c0c0c0c0c0d03070340000040700b82e0380e0303a030ba0000270080b00b82e03030001b130000f0300c000000000f02c00003c0000000dc1cdd37073743c3c3c3c0c6c6c0c00002c2e82c2e82e0b80e0b800009c0b82e0303030f0f1b0f0f0303030f03870000000003c0b000003c00000008703c0003c0f0003c003c0f000c03006c1b00000f070f43c1c3d0f0f0f0f031b1b0300000101c02c2e82c2e82e0b80e0b800009c0202c02e0b80c0c0c0c0c3c0e1c1b130000303000000000000000000000008708c3c3c8c0c0c0c0c8c1cfd23073f400002e0b80e0382c2e82c2e800000b82e03030303030f0387031b03030303000000000000000000008704c00f000c003000c030000c00000230f0f230303030303030340c1c0d00000101c02e0b80e0380c0e80c2e800000202c02e0b800c0c0c00f03870f030b0b0f0f000000f03c2c001312c03001d0742c2c2e0b800c0c3c0e1c0c2c000c000b0b003030f0387030b0f030b000c0c0000f0b00c0003000341d0b0b0382e003c3c2c2c2c2c0000000003c02c00c0000f0f0b0b0b0b00000b82e0b0b82c2e0b82e00000b82e0303000003130387131303030f0f0f000000000000000013131313131313130313130300000b82e0b82e0382e00000b82e0f0f370f0f131313030300c4c0e1c00000000f00000000003c3c3c3c4c4c4c4c0c6c4c0c00002e0b82e0b80e0b800002e0b80130f0f13131b3703371b130300000000000000000000130f0f1313071344c1c4d131300000b82e0b0ba0b0ba0b82e00000b82e00000000000087000f000c01b000000000101c02e0b82e0b800000202c02e0b940c00c0c0c0c1c5cac1c5c5c1c1c1c1c0c6c0c3c0f03c3c1c1704c4c6c5c1c0b02c0b03d870741c1c1d0744c3c1e0b82e0ba9503030303030303550740d07070707030f03870f0f030307070307030307071b1b03030f0f0f0f0f0f0f07070701c1c13131304c4c031b1b030f0f0f0f07070701c2c1c130b1304c2c4c031b1b032323232343d8707075070707070744d41c1c1c1d40d0741d0741d0743c4e0f0f81c1e81c2e84c2e84c2e80e1b89e2788e239a0765030303030f00f07070707172b071717070707030030f0f07070705c1c00c0c0c0c1c0b02c0b08c5c3d870741c1c1d0741c1c1e0b82e0b89c5e9503030303030f03870303030303030307031b0303030f0303070307550340d030303030303030f0f0f0f07070701c1c0303030303030300c0c0f0f0f0f07070701c2c1c0303030303030300c2c0c2323232343d87070750707070340d030340d40c0c1c1d41d0741d0743e0f81c1e81c2e80e0380c0e80c2e89e2788e239a076540005507401c1c1c1c3c3c3c3c1c1c1c0c1c6c1c0c4c4c4c0c4c6c4c0c0f21c3c3c01c1c0700707171700f0f0f1705c0f03c07070070b0130b0130b02308c0043d8707075070707070744d41c1c1c1d41d07441c10703c4e0f0f81c1e81c2e84c2e84c2e89e27885c2231a076 25 33554431 11 2047
def hc_66_23 : Nat → Nat := unpackHintV5 0xe73978dfa1e6d891c4d3a93acf1126c5ea4abfa192b3a300ad01a8a0b3149a69929379bc8c01de8671647f79be7a893c74199c6a02866369a65952865239c64822864221803b79aa3132922ab99e26810e20399216c25e10699606a2720001a8 0xc0c0c0c0c0c0c0c3c0c0000000002c00030030008c3c3c8c0c0c0c0c0c0c0c0c00002e0b80e0380e038000002e0b80c0c0c0c0c0c0c0c3c0c0c000300c030300300b0b02c00c870303003030b000303030303030340c1c0d002c2c0b82e0380e0303a030ba20b082c0b82e004c6c0c3c6c0c2c2c0c0c6c2c0c0c000000000000000030000130f0f1313071344c1c4d031b130300000b82e0b0ba0b0ba0382e00000b82e1b031b0300000000c870000000f002c0000000c6c6c0c0000040700b82e0382e00000202c02e0b84c6c2c003002c2c0c0004c1304c130000302c0b000004c4c1d0744c4c4c4c130b82e0b82e131b030f1b030b0b0b030301b00c0c4c0f00c1b04c5c05c02c2c0b0b00c0c0b00c0c0c02c0c0004c3c3c4c0c6c4c0c4c1c4d13071341300b0b02e0b80e0b82c2e82c2e882c20b02e0b86c0f03000b0b00303000000000000000000000230f0f23031b1b0323072348c1c8d00000b82e0382e0b0ba0b0ba00000b82e002c2c2c3c2c2c2c4c2c2c2c2c2c8c2c2c2c2c2c2c4c2c5c6c0c3c0c5c6c0c0c6c6c0c0c0021c0f003c00000000000000c00c008700230f0f2317072348c1c5d0b070b42c1c2d031b1b0300000b82e0b0ba0b0ba0b0ba0b0ba0382e00000b82e0f030f02c2c0000c0c0000000000000030000c0000000f0f0f0f031b1b0323073f48c1cfd00000b82e0382e0b0ba0b0ba00000b82e002c2c2c2c2c3c2c3c2c2c2c2c2c3c2c2c2c2c3c2c2c2c3c3c6c0c0c3c3c0c0c3c0c3c0c003c03c008700000002c0b00000000c00c0087000f070f43c1c3d0f0f0f0f0b070b42c1c2d031b1b0300000b0ba0b0ba0b82e0b0ba0b0ba0382e00000b82e13131300c3c0c004c6c000000000000000000004c3c3c4c4c1c4d13071340c4c4c0c00002e0b82c2e82c2e80e0b800002e0b86c0c6c0c5c5c3c5c3c5c5c000000005c02c000000000003f2f3f2f031b1b0317071745c1c5d01700002e0b80e0b82c2e82c2e800002e0b82c2c2c3c2c2c2c6c0c6c0c000b00b0b00306c0b02c0303030303000c87000b070b42c1c2d031b1b03002c2c0b82e0b0ba0b0ba0382e20b082c0b82e000c0c0c0c0c0c0c0c0c0c000000003c02c00c0000f0f0b0b0b0b0303030300000b82e0b82e0380e00000b82e000c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000000000004c3c3c4c4c1c4d13071340c0c0c0c00002e0b82c2e82c2e80e03800002e0b80c0c0c0c0000000000c8700000f000c0000000c0c0c0c0000040700b82e0380e00000202c02e0b80c0c000030f03000f0f00000000002c00000000008c3c3c8c8c1c8d23072340c6c6c0c00002e0b82c2e82c2e80e0b800002e0b80c0c0c0c3c0e1c3c3c0c0c3c3c3c0000000013003c01306c001b0000300c01b06c0002c0000000008700008c3c3c8c6c1c6d1b071b40c6c6c0c0004070000b82e0b0ba0b0ba0382e000202c0002c0b82e030f00c0c0c003c3c00c0c00000000000000000000003c3c3c3c0c0c0c0c8c1d0d230743400002e0b80e0382c2e82c2e800002e0b80c3c0e1c0c0c0c0c0c3c0c0c0c0c000000000f003c003000c00300c0003000002c00000000302c008700003c3c3c3c0c0c0c0c0c0c0d03070340004070000b82e0380e0303a030ba000202c0002c0b82e03030001b130000f0f0300c3c000000000b000000b000000023074348c1d0d0f0f0f0f031b1b0300000b0ba0b0ba0b82e0382e00000b02e0b80c0c0c3c3c6c3c3c0c0c0c3c0e1c000000000f0000f03c000f003c003006c0002c0b000002c000008700003c1c3d0f070f43c3c3c3c0c6c6c0c0004070000b0ba0b0ba0b82e0382e000202c0002c0b82e03030305c00300130000c001700b0000000008c3c3c8c0c0c0c0c5c5c5c5c001c000b82e0380e0b82e000b0002c0b82e03030306c4c0000c0c000000000000b00000000000230f0f230303030323072348c1c8d00000b82e0380e0b0ba0b0ba00000b02e0b80c0c0c0c0c3c0e1c0c6c0c0c0c0c0000000030013003c00300c00306c00300c0003000002c0000000008700008c3c3c8c0c0c0c0c0c0c0d03070340004070000b82e0380e0303a030ba000202c0002c0b82e004c3c3c4c4c6d0c0d0c6c4c0c000000000000000000004c3c3c4c4c1c4d13071344c4c00002e0b82c2e82c2e82e0b800002e0b80000003c003006c0002c000008700000004070000b82e0b82e000202c0002c0b82e030300000c3c0c003c3c00000000000000000008c3c3c8c8c1d2d23074b40c6c6c0c00002e0b82c2e82c2e80e0b800002e0b80c0c0c0c3c0e1c3c3c0c0c3c3c3c00000000000000000870004c00f004c1b0006c0000c01b0000230f0f231b071b46c1c6d031b1b0300000101c02e0b82c2e82c2e80e0b80000080b00b82e0300c0c003c3c00c0c00000000000000000000003c3c3c3c0c0c0c0cdc1cdd370737400002e0b80e0382c2e82c2e800002e0b80c3c0e1c0c0c0c0c0c3c0c0c0c0c00000000305c0000000000870003c00f000c003000c030000c000000f0f0f0f0303030303030340c1c0d00000101c02e0b80e0380c0e80c2e80000080b00b82e03030001b130000f0300c000000000f02c00000000003707374dc1cdd0f0f0f0f031b1b0300000b0ba0b0ba0b82e0382e00000b82e 24 16777215 10 1023
def hc_66_24 : Nat → Nat := unpackHintV5 0xed4bc8e192eedca13cd76150d079baca099cbda31ab75992ab1312a3d9ce9ed14297c9c29131a684b32084681283f81c7dc98c70fb346961e65edaa25412b24c69ea4471fe4158c63ca12e339a422d299c20b31e19c1bc0d4b1e0701920001c0 0x3030303030f0387030303030303030b031b0303030f03030b030b000300c030303030303030f03c0b0b00b00300c0303003003c870b0b00b0b0b030300c03030300c00c0c2c2c00b003c3c3c3c2c1c2d0b070b40c0c0c0c0c0c0d0307034131300b0b02e0b82c2e82c2e80e0380c0e80c2e882c20b02e0b8000000000003c4c3c3c3c3c2c2c2c0c2c6c2c0c4c4c4c0c4c6c4c0c08703c00000b05c00f00008702c00b00000b02c00b000000f0f0f0f0b070b42c1c2d13071344c1c4d1313131300000b82e0b0ba0b0ba0b0ba0b0ba0b82e00000b82e0017134b000000c0c0317030f03870f030f0f0b03c000b02c000021c01d0741d0742e0b82e0b80b0003030300c0c3c0e1c5c0d1c00000f0303030b03c000b02c00000c0b021c01d0740d0742e0b80e0b80b0000171b1703171717030f0f02c05c00000b02c0000000021c0017071745c1c5d0f0f2f2f2f00000b0ba0b0ba0b82e0b82e000b0002e0b80c0c0000c0c0000c0c030000000000000000c0000dc1cdd3707374dc3c3cdc0c0c0c0c00002c2e82c2e82e0b80e03800002e0b8003030303030303030303030303130303030f0303030b030b03030303030b03030303030000000008700c003008702c00b0030000000c0b00003f0f0f0b070b42c1c2d0303030303030340c1c0d00000b82e0b0ba0b0ba0380e0303a030ba00000b82e1b03c0c003c3c00c0c000000000000000000000dc3c3cdc0c6c6c0cdc1cdd370737400002e0b80e0b82c2e82c2e800002e0b8017130f0f0f0f1b130b0b0b0b0b0b1b0b0b17170b0b0b0b1b030f030b0b03030b1b030300000000030030021c08702c00b00b02c000003000000f0f0b070b42c1c2d1b071745c1c6d031b1b0300000b82e0b0ba0b0ba0b0ba0b0ba0382e00000b82e003c3c2c2c2c0c2c6c2c0c0f02c2c02c000f21c2c2c02c2c2c2c2c0b00b003c3c2c1c2d0b070b400b0b02e0b82c2e82c2e82e0b882c20b02e0b83c3c3c3c00000f21c0000000b003006c0000000f0f0f0f00000101c02e0b82e0b80000080b00b82e00000f0f0f0f17171703171b1703000f00b0005c000000000000f0f0f0f17071745c1c5d2f2f01700002e0b82c2e82c2e82e0b8200002e0b80c0c0000303030003030000000000300b00000000000f0f0f0f3f07474fc1d1d0303030300000b82e0b0ba0b0ba0380e00000b82e000c2c0c6c0c0c0c0c0c0c0c0c0c0c0c0c0c2c0c0c0c0c0c0c2c0c2c0c0c0c0c0c3c0c0c0c3c0c0c0000000021c03000c02c02c0087000000000b070b42c1c2d0f0f0f0f0303030303030340c1c0d00000b0ba0b0ba0b82e0380e0303a030ba00000b82e59c1d670702c3c0c3c0f0f00003030000000000002c00000000003c3c3c3c0c6c6c0c1d9d6707400002e0b80e0b82c2e82c2e800002e0b800b0b17170b0b0b0b0b0b0b0b0b0b1b0f0f0f0f0f0f0f0f0b0b1b1b03030b0b030b03030f030f03000b05c000000030030021c0b00b0021c000000002c1c2d0b070b43c3c3c3c6c1c5d17071b40c6c6c0c00002c2e82c2e82e0b82c2e82c2e80e0b800002e0b800b1b0b030b0b0b030f0f0f0f0b00b0b00f03c00b0b0b0b0b003c870b02c000b070b42c1c2d0f0f0f0f002c2c0b0ba0b0ba0b82e0b82e20b082c0b82e030303030f03870f0f03030f0f0f000000000003c8700004c0b000c000000b00b02c000300c000300c01b06c0000000f0f0f0f13071344c1c4d0313130300000101c02e0b82c2e82c2e80e0b8000002802c02e0b80c0c0c0c0c3c0e1c0c3c0c0c0c0c00000000000f21c030000000c0b000002c00c03000c1b000c030000c0b000000003c3c3c3c3c4c0c0c0c0c0c0c0d03070340000040700b82e0380e0303a030ba000000a00b00b82e030303030f03870f0f03030f0f0f00000000000000000000b82c2c2c2c2c2c2c2c2c2c0c2c2c0c00003c3c3c3c4c1c4d13071340c4c4c0c00002c2c2c2c0c0c0c0c0c3c0e1c0c3c0c0c0c0c0000000000000000302c00002e0b0b030303030303030b030b030300000f0f0f0f0303030303030340c1c0d00000b0b0b0b0f0f000000000000b82c2c2c2c2c2c00003c3c00002c2c2c2c3c3c0000000f21c0000002c00c01b00000003c3c0000040700b82e0b82e000000a00b00b82e03030303030303030303030300c0c04c0f04c5c12c5c00c0302c2c0b0b02c2c02c2c00c030004c3c3c4c4c1c4d13071340c0c0c0c1300b0b02e0b82c2e82c2e80e03882c20b02e0b80c0c0000c0c0000c0c0300000000000002c0000008c1c8d23072348c3c3c8c0c0c0c0c00002c2e82c2e82e0b80e03800002e0b8003030303030303030303030303130303030f03030313031703030303032303030303030008703c00f0000000305c00b000000021c03000c00230f0f2317072348c1c5d0303030303030340c1c0d00000b82e0b0ba0b0ba0380e0303a030ba00000b82e030300000c0c0c000c0c00f0000000002c000b00000000c000f0f0f0f23074b48c1d2d0303030300000b82e0b0ba0b0ba0380e00000b82e000c0c0c0c0c0c0c0c0c0c0c0c0c3c0c0c0c0c0c0c3c0c3c0c0c0c0c0c3c0c0c0c3c0c0c003c03c008700000002c0b000002c0008700c0030003c1c3d0f070f43c3c3c3c0c0c0c0c0c0c0d030703400002c2e82c2e82e0b80e0380c0e80c2e800002e0b80c0c0c13131303030000000000000000000000130f0f130303030313071344c1c4d00000b82e0380e0b0ba0b0ba00000b82e1717170f170f1703030303000005c000300300000000000002f2f17071745c1c5d0303030300170002e0b82c2e82c2e80e038002c000b82e 24 16777215 10 1023
def hc_66_25 : Nat → Nat := unpackHintV5 0xe4337cd94abacfaa68c73a1cba6b34ae7afca8c16ea3b9429eb1429ba0c493c9f68dc980839a8c7cf9a8728a9c6bb1b66419e65f51325789f25480c2508100475a4a4061be3979ba35111a2bea4a24f1be1df9be19911a15012405a3d8000168 0x30300f0f1300c0c0c0c01313131313030f031313131717030303130317170f00f0f003c870f0f00f0f0f031705c5c1b0b01b0b01303c13170174300306c0013071b44c1c6d130f0f131317134313431317031b130305c4c08c4c1b0ba1b0ba1383e1317a1743a0386e217088c2f84e000000004c3c3c4c2c6c2c0c2c2c2c0c4c5c5d0c5d0c4c5c08703c000000f0000b0002c02c0b00000000130f0f130b070b42c1c2d13171323132313171323132300000b82e0b0ba0b0ba0b0ba0b0ba0b82e00000b02e0b80130f0f13131313431343131303c870f0f00f0f0f1705c1303c13130132302308c0044d551345d55554544c144541c10741d03544d4150f00542c151383e1313a131fa1f87e217087c555642d42d0b0b01682c2c2c2c4c3c3c4c2c2c2c2c4c4c4cfc4d0c4c4c0f21c3c3c02c0b03c3c3c5c1702c0b02c0b02c2c02c2c02c0b0001d0741d0741c1d41c1d41d07441c1070141c1c1c01544c3c3c4c1c6c1c0c1c1c1c0c4c4c4cfc4d0c4c4c0f21c3c3c01c3c01c1c03c3c3c5c1704c0f01c2c01c1c04c4c04c8c08c230001c1d0744c1c1c1c1c1c1c1d51345c1d07445c1c1c10704e0f81c1c2e81c1e07a1313a132fa2f8be217088c60742aa00aa130f0f130b1b0b030b0b0b03131717431743131703c870f0f0a00b0b00f0f0f1705c0b02c0b0b00b0b00b0b00b0b00b02c00130f0f130b070b42c1c2d1317131f132f1317131f131f05c4c02c2c82eaa0ba0b82eaaaa8a82c2a0b2a800f0f171b031b170303c870f0f00f0f0f1705c03c170b00b00000f0f170741c5d05c5c02783e170ba0baa21708a0f0f0f0f03c87000003c00c01b00000000000003c3c3c3c0004070000f83e2789e000202c0009e27802c2c2c2c2c2c3c3c3c3c2c0b03c0f05c1702c2c2c2c3c3c3c3c171702e0b82e0b82e0b882c0b82e0f0f0f0f00000000000f0f0f0f00000f83e2789e00002789e003c6c3c0c3c3c3c0c3c3c3c3c3c3c3c3c00f21c5c1703c3c2c03c2c0f03c0f00003c1c3d0f070f43c3c3c3c1717003c2e83c2e83e0f89e27885c22709e2780e1c021e1c00e1c3c0e1c03c03c05c001b0000000003c3c3c3c4c4c4c4c0c4c4c0c00003e0f85e1780e1b8000004e1380c0c0c0c3c0e1c3c3c0c0c3c3c3c000f21c0001300000f01305c000300c000300c01b06c00000000000000000f0f0f0f13071344c1c4d03131303000101c0003e0f84c2e84c2e80e1b80002802c0004e1380e1c0c0e1c0f8700878700c003c00c001700000000003c3e1c3c3e1c0c0c0c0c4c4c4c4c001c000f83e0380e1785e0000b0004e1380c0c0c0c0c3c0e1c0c3c0c0c0c0c000f21c0000003000f00300c00306c00300c000306c000000000000000000f0f0f0f0f130303030303030340c1c0d000101c0003e0f80e0380c0e80c2e80002802c0004e13800f0f0f0f13171703171b1303021c0f003c0000000000000f0f0f0f13071344c1c4d132f132f00000f83e130ba170ba2789e00002784e030303030f03870f0f03030f0f0f000000000b82c2c2c2c2c2c2c2c2c2c0c2c2c0c000000000000003c3c3c3c4c1c4d13071340c4c4c0c002c2c2c2c000c0c0c0f000c00b82c2c0c0c0c0c2e0b0b000000000f0f0f0f03030303131313130b0b0b0b0003030303030f0387030f03030303000000000c00b82c2c0c0c0c0c0c0c0c2c0c2c0c0c000000000000003c3c3c3c0c0c0c0c0c0c0d0307034002c2c2c2c003c3c00002e0b0b0b0b0b0b00000000000f0f000b0b0b0b000f0f0003c8700000c01b00000000000003c3c0004070002783ea0000a00b000a03030303030303030303030300c0c04c5c0f1704c5c05c5c00c0304c0f04c2c08c2c00c030004c3c3c4c4c1c4d13071340c0c0c0c17130231304e0f84c2e8ec2e80e03885c2230ee1380c0c0c0c0c0c0c0c3c0c0c01705c00c870303003031b00300c03030030b0000303030303030340c1c0d05c5c0a0380e0303a030ba21708a004c6c0c3c6c0c4c5c0c0c6c6c0c0c00000000000000000004c3c3c4c4c1c4d13071340c6c4c0c00004e0f84c2e8ec2e80e1b80000ee1386c0c6c0c000321c00003c01b000000000000031b1b03000101c00280e1b800080b000a131b030f1b03131717030301b00c0c4c5c0f1700c1700c0c05c0c04c0f00c1b04c2c08c2c0004c3c3c4c0c6c4c0c4c1c4d130713417130231304e0f80e1b84c2e8ec2e885c2230ee1385c6c6c3c5c3c6c6c0c6c0c01705c0303030303000c8701b0b0170b00306c001b071745c1c6d031b1b0305c5c0a1b0ba170ba0386e21708a000c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000000000004c3c3c4c4c1c4d13071340c0c0c0c00004e0f84c2e8ec2e80e0380000ee1380c0c0c0c00000321c003c00300000000000003030303000101c00280e03800080b000a003000c0c0c000000c6c0c03c0f0004c05c21c2c0b02c0b0000c00741d0741d0b82e0b82e000c0c0c0c0c0c0c002c0302c2c2c2c0c3c0e1c3c3c0c0c2c2c0c2c0c0c2c2c6c6c0c0c3c3c3c3c4c0f0f02c2c02c04c4c04c00c1b00f21c2c2c02c2c2c2c2c1300b0b0b0b0030302c0302c00f0f0f0f0b070b42c1c2d13071344c1c4d0313130304c4c02c2c0b82e0b0ba0b0ba0b0ba0b0ba0382e20b082c0b82e0030303030303c00b0b0b000000c00f02c0b0000c03021c2c0b00c0b02c0000b00741d0741d04c2e0b82e0b80b 24 16777215 10 1023
def hc_66_26 : Nat → Nat := unpackHintV5 0x73c230d803e18b0942cc1285032549443091a4391e893033f2485863e073cf406f9e000037c 0x30300f05c0c6c0c3c0c5c3c0c0f0f0171703c1717170306c5c5c03c170b0170b00306c000f0f2f17071745c1c5d031b1b0305c5c0bc2783e170ba170ba0386e21708bc2f8be030303030f03870f0f03030f0f0f0f0f1b1b1b06c6c031b1b030f0f1b0b1b06c2c6c031b1b030f0f1b071b46c1c6d031b1b032783e1b0ba1b0ba0386eaaa030303030f03c3c3c3c00c0c00c03030f03c3c3c030300c030303030f03c0300c170b0170b001700f0f0f0f0303030317071745c1c5d05c5c0bc0f83e0380e170ba170ba217089c2789e030f038703030303030f030303030f0f0f0f0303030303030300c0c0f0f0f0f0303030303030300c2c0c0f0f0f0f0303030303030340c1c0d0f83e0380e0303a030ba2789e2789e2789e030300f030f05c5c05c6c0c0f030f030f0f0f0f03c3c3c0306c5c5c170b0170b00f03c0306c0017071745c1c5d0f0f0f0f031b1b0305c5c5c0bc170ba170ba0f83e0386e285c889c2789e030b0b0b0b030b030f030f030b0b0b0b0f0f0f0f031b1b030b0b0b0b0f0f0f0f031b1b030b82e0b82e0382e0b82e0b82e0f030f0300000000000f0f0f0f031b1b0300000f83e0386e00002789e0303030f0f1b0f0f0303030f03870f0f03c3c3c0f0f0f0f031b1b030f0f0b0f03c2c3c3c0f0f0f0f031b1b030f070f43c1c3d0f0f0f0f031b1b030f0ba0f0ba0f83e0386e2789e2789e2789e03030303171700f05c6c0c0c00c0303171703c030300c0303030303c0300c170b0170b0005c0f0f2f0303030317071745c1c5d05c5c5c0bc2783e0380e170ba170ba2171708bc2f8be03030303030f0387031b030303030f0f0303030303030300c0c0f0f0303030303030300c2c0c0f0f0303030303030340c1c0d2783e0380e0303a030baaaa000c0c0c0c0c0c0c004c0304c4c4c5c0c3c0e1c3c3c0c0c4c4c0c4c0c0c4c4c6c6c0c0c3c3c3c0f21c3c3c03c3c3c4c4c1301313171700305c0f1303c3c130b0130b0130b0130b00306c000f0f0f0f13071344c1c4d13071344c1c4d0313130304c4c04c4c0f83e130ba130ba130ba130ba0386e217088c1384e000c0c0c0c0c3c0e1c0c0c0c0c0c0c0c4c0c6c0c0c0c3c0c0c4c0c5c000c0300c0c0c0c0c0c0c0f21c3c3c03c3c3c0c0300c0c0300303171700f03c130b0130b00300c03030030b0000f0f0f0f13071344c1c4d0303030303030340c1c0d04c4c04c4c0f83e130ba130ba0380e0303a030ba217088c1384e000c4c0c0c0c0c0c4c0c5c0c0c0c0c0c0c0c0303030f00317031b03030303c870f0f00f0f0f030300c5c03030030f01303c13170174300300c03030030b000130f0f1313171343133f13170303030303030340c1c0d05c4c08c4c1383e1317a1743a0380e0303a030ba217088c2f84e 23 8388607 10 1023
def nh_66 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_66_26 (Nat.sub p 832)) (hc_66_25 (Nat.sub p 800)) (Nat.blt p 832)) (Bool.rec (hc_66_24 (Nat.sub p 768)) (hc_66_23 (Nat.sub p 736)) (Nat.blt p 768)) (Nat.blt p 800)) (Bool.rec (Bool.rec (hc_66_22 (Nat.sub p 704)) (hc_66_21 (Nat.sub p 672)) (Nat.blt p 704)) (hc_66_20 (Nat.sub p 640)) (Nat.blt p 672)) (Nat.blt p 736)) (Bool.rec (Bool.rec (Bool.rec (hc_66_19 (Nat.sub p 608)) (hc_66_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (hc_66_17 (Nat.sub p 544)) (hc_66_16 (Nat.sub p 512)) (Nat.blt p 544)) (Nat.blt p 576)) (Bool.rec (Bool.rec (hc_66_15 (Nat.sub p 480)) (hc_66_14 (Nat.sub p 448)) (Nat.blt p 480)) (hc_66_13 (Nat.sub p 416)) (Nat.blt p 448)) (Nat.blt p 512)) (Nat.blt p 640)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_66_12 (Nat.sub p 384)) (hc_66_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_66_10 (Nat.sub p 320)) (hc_66_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_66_8 (Nat.sub p 256)) (hc_66_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_66_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_66_5 (Nat.sub p 160)) (hc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_66_2 (Nat.sub p 64)) (hc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 416)
def f_66 : Nat → Nat × Nat := unpackForestF 0xd2daa80317f4968a00c5bd15b6e8a9b3454c000c57d0da280314f398df9cc63ce62de7315f394af9c95bcec3667255f390ae00b5f005ade6a9b3354c000b57cce326575bf318a995d63cadb765917f2d68996453cac1a002d4f298dc00b4fc9db7002d2f25ac400b47c8db7002d0f216ab8b46fc7da2e2d18f166df8dc5fc6e29e2cd57198c98b34fc5eb462cd1c014be00a5bc35b6e251f30d69f8794fc3ca1e1d5c30d68e00a57c1eb7e0f58f088bf84453c1c1200294efe8dd82464bf9b7e051f2fe6cf80562bf9a2dfc9880149f7e26e00525df4d1ef3ac57c568bcdb7ded5c2f36cf7a46ebcdae80291ef06dd7826e00521ddcd92e5adf76354b96b5dd4df2e5acf73c54b9daa5cb58ee56dc00a3fb8d325b75bee14a96dd6bb7d3e5b759edd4a96dd63b6d370028eed6adf6b56bb5ab3dad58c0146f6a264b16b7da3152d14a962d6bb3d3e58b59ecd4a962d63b2637d94912c98c762b6eb1a36d8d196c54dc00a33b0daad2f1bec168b4bc63a5db7d7c0d2976c75d45faea29d74d4a976ab5c464a5da7d6cd92976975a568a5da3d64d929768757365ab9aad5cd1e974df56024a5d31d51192a86cb54345a5d27d4c9929749751d68a8db2d2e91ea06fd50264a5d21d3cd929747f4e264a5d1dd2e8de986fd4c264a5d1980257e952a93e45fa4ca24f916e90ce14816c9f22bd1c5127c8a7461549f1afd144d27c6b743e70a1cb64f8d5e852693e353a0ca24f8d3e812693e34b9f1a3cfc4d27c6873e146004adcaedb6798f92bb4f9ddbe4aed2e7449f3a2479ceb84aed1e708f93837c95da1cd91f26c6fb3634595d27cd49f25749733d7099dbecae91e654f92ba4398dbe4ae8fe614f92ba3b95d1bcbb1f25d4f92ba339611fcb08ee5846f2c23395c3600255e23adf11d6388e37ca4112238c72815488e2fc9c512238b725e7092cb644715e4928911c539162fc8c5b2458af11b6f90c1a446d8e412a911b5f8fc9a446d6e3cce11e16c88dabc711fa396dd1c13488da9c6c5122369f1a13488da5c46d1e2e8fd17b6e8bd2bc5c4d2236871256f892b1c540d2246c51235a89137c4897e244af1223d88ca300254dfd8dd104647f5b7c3cd51fd6d70d47c8693e4349c1fd6cf0bb5485c1a3fad8e15ac4feb4584632422d961168afea6f83d2a3fa9ae0b8f905b7d82da2bfa99e084a9040247f531c0cd51fd47f01d7e80d2a3fa8edfd46eff57e7f9bf3fc951fd4660094f7ecb23af1bdf9288ebc6b7d5be3eadc1f52f8ebc677c8a23e4111d78c6f816475db7bdc4d1d76d6f617c75db3bd24d1e9068ebb6379a3f3cc511d769ef1b7e78c9a3aed2dd768eeec7e775bf3bcdb9dd268ebb4375cb73b1189d84deec26775ca300252dd2696e9a5274d283a4d1d9bac4e856866db7b9cd59ccce0e636c66db5b915c1c84f8e427066db3b879c1c36d8e225070c1a336d8dc08dce036266daeb795a1bc6cade35d66d37b739c1b94d8cda6b6d6b836adf5b56bacda676c3383609b1b12a0d802466d31b5cdb19b47ed5e726ad363368ed9b46ed425468b393451b1a56b8d137e68d373449b19b466ce25f6712db3c5819c4aece25366c2e00251d992c8b846f65ca22e11ad936f8c9b7064cbe2e119d90288c80445c231b1c591706dec61345c1b5b145f1706cec393461c1a2e0d8d848fcc21445c1a7b02df981268b834b5c1a3af91f97c6fcbe1345c1a1af28ed79466b816e5c6312e2da9714deba4705c533ae4db971462b8146004a1adcd915eadeb635457ab5ad2df1694f8af56759a2a2ccd515eac6af36e57e2fabf16d5f8aeb034457e29abc0d00127eae164526b7ab455149ad6abb7c55cbe29359d552a8a4d6354cb2292dbd512f8a4b6753abf29c551496bea5e7252cb6292d5d492dc0093b51e342635bd458b098d6b50a382849f131acea04584c6b1a7cd553aad29d5614e9afa74d5d318c49c4684c537a6d1c1314ce9a4584c52fa65181314ae009374bcb224b5bd2d2a892d6b4a63e252df1292f892d6749caa24b58d252dc0093348d3222d5bd214a88b56b47d3e22d59d1d4a88b5634593722f17d178b68bc5745e29a2c0900125e8a1643feb7a24550ffad68817c3feb3a1c550ffac6861643fe37a145f0ff8ce841543fe2fa0c5b0ff8ae823473fcb72015bd00ace804623fca30024acfc8ca7e368316b79f3154f96b062d6b3d23e9ea92cf548e7a370316b39e4d40f08aa78358316b19dcda0c58de75a5b3ad299d4dc0c58ce743583162f9c09bce56f87026b381339c49b0e16e87026337db018b15cdd4aa66569332b09b4954cc8be6ba6d35d3619915cd48ca6a4553312f9a31b4d18ba662573373c99b198cd4cc66247315b118d5bcc6ad66356731ab198c9b8c56940092730cb21775bcc12a85dd6b2fcbe17759cbd2a85dd632ecb700248cb269e5934b2c9a3964d0cb229e591472c89f9644dc010be4936d2be3e124d3cad6f84934b2aeb8124d1ca88f85437c249a19468fca347651a3728d199245b09e69e4f34b279a393cd0c922c04dc7c26dbe92453c996864bd7025dbe92451c956f84913f24e381244dc010ae41c6e23e32106dbc8d6a841b6322eb1106d14888c84434520cb790cd508327e4245820c9b80213c80696403471c6b10fd5a0716de3e36c1c5b18f31b8796c438b5d1dab40ecd74712de3a36c1c49f8e51807126e008471bdb20c95bc6c8a836354192b18c8db8696c83216f19daa0c857c656d8321570041f8c51a056ade3045815ab18bad7c5d6ae2b46216e340ac5bc598b02b15f15e300ac55c0106e2a26412ab78a49504aac62526e13d320945bc4d4a82515f12d3609455c0105e24368076b788cd601dac62236807637884d601d8be203600762b87c954368be1da6d0ed3606d15c364be1b2570dd3306c91c1d6c41956f0cab18649b81d69416d6f0bd2a05b58c2d6c40ea420a5b4052d28294840e96f095ac04ad28254840e95f085b0042d28214840e95707da803a51c1d25a0082702eb781758c0b8de05c6302e2f81716c0b8ae05c53041a7820d2c1068e0834302cb70195bc0cac60646202ca300207c02ade0156300a3780518c028be0145b00a2b80514c0102e0003f 10 11
def ch_66 : Nat → Bool := dagCheckNodeV5 fullMask g_66 ep_66 6 63 bds_66 844 (dagTraceF fullMask rootStock 11 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 fullMask g_66 ep_66 6 63 844 bds_66 (dagTraceF fullMask rootStock 11 f_66) (cur_66 0) (nh_66 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 64 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_2 : treeBlockF 64 96 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_3 : treeBlockF 96 128 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_4 : treeBlockF 128 160 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_5 : treeBlockF 160 192 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_6 : treeBlockF 192 224 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_7 : treeBlockF 224 256 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_8 : treeBlockF 256 288 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_9 : treeBlockF 288 320 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_10 : treeBlockF 320 352 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_11 : treeBlockF 352 384 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_12 : treeBlockF 384 416 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_13 : treeBlockF 416 448 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_14 : treeBlockF 448 480 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_15 : treeBlockF 480 512 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_16 : treeBlockF 512 544 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_17 : treeBlockF 544 576 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_18 : treeBlockF 576 608 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_19 : treeBlockF 608 640 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_20 : treeBlockF 640 672 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_21 : treeBlockF 672 704 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_22 : treeBlockF 704 736 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_23 : treeBlockF 736 768 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_24 : treeBlockF 768 800 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_25 : treeBlockF 800 832 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_26 : treeBlockF 832 844 ch_66 = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 64 → ch_66 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nj_66_2 : ∀ i, 0 ≤ i → i < 96 → ch_66 i = true := block_join nj_66_1 (fun _ h1 h2 => treeBlockF_at nb_66_2 h1 h2)
theorem nj_66_3 : ∀ i, 0 ≤ i → i < 128 → ch_66 i = true := block_join nj_66_2 (fun _ h1 h2 => treeBlockF_at nb_66_3 h1 h2)
theorem nj_66_4 : ∀ i, 0 ≤ i → i < 160 → ch_66 i = true := block_join nj_66_3 (fun _ h1 h2 => treeBlockF_at nb_66_4 h1 h2)
theorem nj_66_5 : ∀ i, 0 ≤ i → i < 192 → ch_66 i = true := block_join nj_66_4 (fun _ h1 h2 => treeBlockF_at nb_66_5 h1 h2)
theorem nj_66_6 : ∀ i, 0 ≤ i → i < 224 → ch_66 i = true := block_join nj_66_5 (fun _ h1 h2 => treeBlockF_at nb_66_6 h1 h2)
theorem nj_66_7 : ∀ i, 0 ≤ i → i < 256 → ch_66 i = true := block_join nj_66_6 (fun _ h1 h2 => treeBlockF_at nb_66_7 h1 h2)
theorem nj_66_8 : ∀ i, 0 ≤ i → i < 288 → ch_66 i = true := block_join nj_66_7 (fun _ h1 h2 => treeBlockF_at nb_66_8 h1 h2)
theorem nj_66_9 : ∀ i, 0 ≤ i → i < 320 → ch_66 i = true := block_join nj_66_8 (fun _ h1 h2 => treeBlockF_at nb_66_9 h1 h2)
theorem nj_66_10 : ∀ i, 0 ≤ i → i < 352 → ch_66 i = true := block_join nj_66_9 (fun _ h1 h2 => treeBlockF_at nb_66_10 h1 h2)
theorem nj_66_11 : ∀ i, 0 ≤ i → i < 384 → ch_66 i = true := block_join nj_66_10 (fun _ h1 h2 => treeBlockF_at nb_66_11 h1 h2)
theorem nj_66_12 : ∀ i, 0 ≤ i → i < 416 → ch_66 i = true := block_join nj_66_11 (fun _ h1 h2 => treeBlockF_at nb_66_12 h1 h2)
theorem nj_66_13 : ∀ i, 0 ≤ i → i < 448 → ch_66 i = true := block_join nj_66_12 (fun _ h1 h2 => treeBlockF_at nb_66_13 h1 h2)
theorem nj_66_14 : ∀ i, 0 ≤ i → i < 480 → ch_66 i = true := block_join nj_66_13 (fun _ h1 h2 => treeBlockF_at nb_66_14 h1 h2)
theorem nj_66_15 : ∀ i, 0 ≤ i → i < 512 → ch_66 i = true := block_join nj_66_14 (fun _ h1 h2 => treeBlockF_at nb_66_15 h1 h2)
theorem nj_66_16 : ∀ i, 0 ≤ i → i < 544 → ch_66 i = true := block_join nj_66_15 (fun _ h1 h2 => treeBlockF_at nb_66_16 h1 h2)
theorem nj_66_17 : ∀ i, 0 ≤ i → i < 576 → ch_66 i = true := block_join nj_66_16 (fun _ h1 h2 => treeBlockF_at nb_66_17 h1 h2)
theorem nj_66_18 : ∀ i, 0 ≤ i → i < 608 → ch_66 i = true := block_join nj_66_17 (fun _ h1 h2 => treeBlockF_at nb_66_18 h1 h2)
theorem nj_66_19 : ∀ i, 0 ≤ i → i < 640 → ch_66 i = true := block_join nj_66_18 (fun _ h1 h2 => treeBlockF_at nb_66_19 h1 h2)
theorem nj_66_20 : ∀ i, 0 ≤ i → i < 672 → ch_66 i = true := block_join nj_66_19 (fun _ h1 h2 => treeBlockF_at nb_66_20 h1 h2)
theorem nj_66_21 : ∀ i, 0 ≤ i → i < 704 → ch_66 i = true := block_join nj_66_20 (fun _ h1 h2 => treeBlockF_at nb_66_21 h1 h2)
theorem nj_66_22 : ∀ i, 0 ≤ i → i < 736 → ch_66 i = true := block_join nj_66_21 (fun _ h1 h2 => treeBlockF_at nb_66_22 h1 h2)
theorem nj_66_23 : ∀ i, 0 ≤ i → i < 768 → ch_66 i = true := block_join nj_66_22 (fun _ h1 h2 => treeBlockF_at nb_66_23 h1 h2)
theorem nj_66_24 : ∀ i, 0 ≤ i → i < 800 → ch_66 i = true := block_join nj_66_23 (fun _ h1 h2 => treeBlockF_at nb_66_24 h1 h2)
theorem nj_66_25 : ∀ i, 0 ≤ i → i < 832 → ch_66 i = true := block_join nj_66_24 (fun _ h1 h2 => treeBlockF_at nb_66_25 h1 h2)
theorem nj_66_26 : ∀ i, 0 ≤ i → i < 844 → ch_66 i = true := block_join nj_66_25 (fun _ h1 h2 => treeBlockF_at nb_66_26 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 844 → ch_66 i = true := nj_66_26
theorem lb_66 : LowerBin fullMask rootStock g_66 12 :=
  lowerDagV5 (kn_cons lb_43 (kn_cons lb_64 (kn_cons lb_63 (kn_cons lb_60 (kn_cons lb_65 (kn_cons lb_46 (kn_cons lb_58 (kn_cons lb_40 (kn_cons lb_62 (kn_cons lb_59 (kn_cons lb_22 (kn_cons lb_11 (kn_cons lb_31 (kn_cons lb_35 (kn_cons lb_2 (kn_cons lb_47 (kn_cons lb_36 (kn_cons lb_49 (kn_cons lb_16 (kn_cons lb_29 (kn_cons lb_32 (kn_cons lb_53 (kn_cons lb_23 (kn_cons lb_21 (kn_cons lb_56 (kn_cons lb_50 (kn_cons lb_6 (kn_cons lb_34 (kn_cons lb_57 (kn_cons lb_39 (kn_cons lb_55 (kn_cons lb_8 (kn_cons lb_25 (kn_cons lb_45 (kn_cons lb_54 (kn_cons lb_51 (kn_nil))))))))))))))))))))))))))))))))))))) rc_66 nc_66 (by decide +kernel)

def wg : List Gate := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.and, [8, 13]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4008214656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677288 * 2 ^ 32 + 4008214656)) (13 - 1) := by
  rw [show canon fullMask (4276677288 * 2 ^ 32 + 4008214656) = g_66 by decide]
  exact lb_66

end PEqualNP.Outside.L_meta_48025

theorem PEqualNP.Outside.L_meta_48025 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 4008214656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4008214656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48025.table2_from_lowerBin (4276677288 * 2 ^ 32 + 4008214656) 13 PEqualNP.Outside.L_meta_48025.root_lb PEqualNP.Outside.L_meta_48025.wg 18 rfl PEqualNP.Outside.L_meta_48025.wfits PEqualNP.Outside.L_meta_48025.weval
