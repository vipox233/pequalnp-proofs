import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48013

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

def m_0 : Nat := 0x4444444400000000
def s_0 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_0 : Nat := 0x4044400000000
def ep_0 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_1 : Nat := 0xff0000
def s_1 : List Nat := [0x550000, 0x330000, 0xf0000]
def g_1 : Nat := 0x170000
def ep_1 : Nat := 0x6000000000000001200000000000000140000
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

def m_2 : Nat := 0x5500550000000000
def s_2 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_2 : Nat := 0x100150000000000
def ep_2 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_3 : Nat := 0x5050505000000000
def s_3 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_3 : Nat := 0x10105000000000
def ep_3 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_4 : Nat := 0xf000f000
def s_4 : List Nat := [0x50005000, 0x30003000, 0xf000]
def g_4 : Nat := 0x10007000
def ep_4 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000
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

def m_5 : Nat := 0x5000500050005000
def s_5 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_5 : Nat := 0x100010005000
def ep_5 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
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

def m_6 : Nat := 0x3000300030003000
def s_6 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_6 : Nat := 0x100010003000
def ep_6 : Nat := 0x1000200000001000000020000000000000000000000000000000000000000000000000000000100010000000
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

def m_7 : Nat := 0x3333000000000000
def s_7 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_7 : Nat := 0x113000000000000
def ep_7 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_8 : Nat := 0x5555000000000000
def s_8 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_8 : Nat := 0x115000000000000
def ep_8 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_9 : Nat := 0xa0a00000a0a
def s_9 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_9 : Nat := 0x20000020a
def ep_9 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000000000000000
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

def m_10 : Nat := 0xc0c00000c0c0
def s_10 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_10 : Nat := 0x40000040c0
def ep_10 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_11 : Nat := 0xff000000000000
def s_11 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_11 : Nat := 0x17000000000000
def ep_11 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_12 : Nat := 0xf0f000000000000
def s_12 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_12 : Nat := 0x107000000000000
def ep_12 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_13 : Nat := 0x3300000033000000
def s_13 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_13 : Nat := 0x100000013000000
def ep_13 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_14 : Nat := 0xc0c0c0c
def s_14 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_14 : Nat := 0x4040c
def ep_14 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
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

def m_15 : Nat := 0xf0000000f000
def s_15 : List Nat := [0x500000005000, 0x300000003000, 0xf000]
def g_15 : Nat := 0x100000007000
def ep_15 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000
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

def m_16 : Nat := 0xff0000000000ff
def s_16 : List Nat := [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff]
def g_16 : Nat := 0x170000000000ff
def ep_16 : Nat := 0x600000000000000120000000000000014000000000000
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def nh_16 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0x3300003333000033
def s_17 : List Nat := [0x1100001111000011, 0x300000303000003, 0x3300000033, 0x33000033]
def g_17 : Nat := 0x100001313000033
def ep_17 : Nat := 0x1200002000000000000000000000000000000000010000020200000000000000000000000100001010000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cc_17_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8428408027657417407217207016846616606416406215a45a05a05625605415025005004c24c04a1462460270032001 0x106901fd00269201c24094681d53038a205124030680b0d0329205c240d280184c02c200283402848134d0221a0513009240100c0081203424058280b0c018980283403868050500a1001920020482a938532509a4611c84228f8431d07a360dc64155181e9b0092e0709409118101d00c36010337c8fee91ddb6379fc67384fe549bc752f81a4efb0fde61db88375a066a70bd30159e427200462b06c020b8000f 12 4095 5 31 10 1023 19 524287
def cc_17_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9866094650942508ca308c221791e0781e0709c0701b15d09e24090240901c870148050000000000 0xe030c020d8242c14d834e144dc3cd4346824b8341414b824c134bc4cb4445024fd4af946f53af1360925ec4ee84ae446d042cc3ec83ac436b0320825a24c9e40653434346244953c913469243044 10 1023 4 15 10 1023 16 65535
def cc_17_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xf01e0382700dc3a0f21640c81886d25a0b0350aa0521a4140632c41881102203a5740d89b0341642b0c0b000 0xc04cbe3cbc24ba1c88248b34b4449624ac340a14ac24b134ae4caa442824a634a03c9c34a0249c24a3349e4c9a44963c841c0a24962d842a94269225902488340a1488240a248b3486448424b33d833aef36eb35e534e24ede4ddc4cd24ace46ca45c244b842b63eb23da82d582aa42698258e248c1e821d 11 2047 5 31 9 511 16 65535
def cc_17_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a09438c48a18815b75a05435404e34e04e036c3603222a42a02622412402211c31c01a11620a60a00a00a0005000000 0x112307f4c1f920849020a3080501f534454b1141c97d3a5b4a94d1a4b429192a2e467a8f91a3d8a4f47935894b6192585129f0467b0f96c3d7b0b9e82977089d42172080f01a030599044780f1281463111d83c49091c03d6d0e9a036660d58834740b9cc2d58074c01a53059441548051103450051c1346c1115c2c4f09110346b05110246b091b5346c111a82468091581c4e051993460131683c550b1342443071682d430a99026630958824 12 4095 5 31 10 1023 18 262143
def cc_17_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe01b8741e61cc1791d93a0740e81c0b4254aa0530a60444880f11642c0504a01021842844088008410001000 0x9e0d27d44900d2742445081153460131b04414092994aa551a913ea34f5e935414c8f52a0849a884ea112a80469c10a6c367a0d4c82a9a09a641e41076554c8f8d20c348ed12423493492084484091b4207f0d23d247e09110348d05242408e8c230407d0d0c020880d01414870c010146d081fa347f4920c14444d20414 11 2047 5 31 10 1023 18 262143
def cc_17_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8818808808807e57e07a27817617034564214013e13e03e03a23a03813233203203200f20c10a1081061041040040002 0x2c34be0f6d83abd0daf035bb0d1fc240b051fc340b0d2e144b70d2d824d9536d54ae051b7945db513684ed9137603ed60f7543c9c0eb4c36d10d730345c0cb1c2d340ab1426bf096e824b907ad41d5f8d2ba305f8e2b5247e092b634aed12b12484092cf4ab2d1ac64eb092abe46ab90a663e598f6a93da94d4892da8496903aa30e5ec36590c5ec269b09574149f0c1e024760d174387f0927814 12 4095 5 31 10 1023 18 262143
def cc_17_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4f50d429ca42639824281200801f1749765856058160454f23c0f0384a4280911c8701846014405 0xdf26670d2f049ba3edc1eeb8b67c55a826d212e68932c3a701ac60b62056ec297144d01a5f091fc498614d7a2480d328598424d422648730429a544d0262f8f320598024b70e3f8d3407b6e3acf1b670d7346992240b0a648d32e89943cc81a0d0931889862cc112618d304698944be26610f300696c1c 10 1023 4 15 9 511 17 131071
def cc_17_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xba0ba0ba09729419219018e18e08e08646326205e25455215204e24e04a24244204014003c2382361341077060003000 0x3d34e6ce9b029360322a5e3d80472ff8d55718bf94d7ea8a2a4f5f89abe84a7c892e4119b220b90367c06ae10d1be222e0302e850b8510be1e240340d048fa539f2a6b8d455aa84a64e90a9b0fd2a0724cf8119c622bdc3e50874f60d8d2190e82a7a84cf40796a0ebba3440848edd10d9223c52440068840913e183b9243f0487f091d80a1b34076c60eb100fa120e030738480b051cc20028145c478b8071c7a72e74d7949ab09252922bc24177c7aea8d5d2a6899457427ae54d5c8273684d7207ce30e5c019378316d860a50a8f8130f81a0482ce11319e122f414 12 4095 5 31 10 1023 19 524287
def cc_17_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xf417baf05e0bc1782d15a0ac5316604c090510a10c20803001f0be0782d11a0340680c093287008208400800 0x4a74a9468d2793a4d254964690485084da10932a83d4486a220b63e14c7825160431a132322044e348786912d121ca2441248b85116092169244c24894610a4d2171a43c14868290b482212043a30862810a4d110120441443a68104920c26414440a0491cd3a37a5463468ae851492a2323425468427d084ba0e1e8c8390f06b040c55216a18250782a60d115d181824c 11 2047 5 31 10 1023 19 524287
def cc_17_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xe41c0780700e01c02a7540a8140a32c608c1089f13e07c0f81d1305220400708e01c0380510a014020402000 0x492309f49b3d916391ecf2399dc6b208c65ea34bd367f09ae8114541ece8399c86a340c6651a4342498e890c4d220924d8289a8490b49264124c63085248e70d02e0a399440b2492d0f2581a068249bc9b269263122cd24199c7b308d65ea74bd3e84a4d2e13474248984595882fd0f5ca1a85415924610b492441248a349268910492461448424 11 2047 5 31 10 1023 19 524287
def cc_17_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf05b97706c1d43a0740680d01796d15a0b4160682500a0130a604a1941205e33c0742e05b0b606c0d8162816 0x2a40c52814af6895a532b29e54418a48295cd12171a42e34ad47b598eab11b55e35ab46952490fc1254a34aa689534a2a29221024a60314a052991a52a34a6e8945532889e1752ca5831490528fa21fa343f469458f6891d50e36a146b418d2c9a6d874ab5e8d69d16cda25964eb249b638fac31ec812dafa555d49ab692d55245585b500aa9e14d3828a404d46096801217021 11 2047 5 31 10 1023 19 524287
def cc_17_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xd81d80b52b21b01ae1a64a60a41a408127e17c17c07c07826e54174003a33a03433403401cc1c01631601220c3082004 0x1804cbc69d64d36f7255ea49b9c8d64906e71b5e6359f29b33516389edfd358109aef1152e1edf839be86a9c0c6d91a5aa44b146162d12209217428420485f0f2f7a75eb4db968b61d0af3235ca45bc47d618f6529ec51359325b77495661ea44355805b760a6ea129a421b1479628f1d81a2342475a888c4d0d82224034b784972d3ac7a6dce4eb2c9b738fae51cdae32b4c63668c2e2a6c61459ea7b304d65096c4525b809aa11252822db8418087aea0d56416a2c25b64995849286125aa4caba4942092d11f59e3d9225b604aabc9357125ab248ae0b6a81553426a384b41092c5a256924a28490b490fc1258b44aca4944092169253024b068910492a61452c24 12 4095 5 31 10 1023 19 524287
def cur_17 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec ([]) (cc_17_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_17_10 (Nat.sub p 320)) (cc_17_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_17_8 (Nat.sub p 256)) (cc_17_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_17_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_17_5 (Nat.sub p 160)) (cc_17_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_17_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_17_2 (Nat.sub p 64)) (cc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_17_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_17_0 : Nat → Nat := unpackHintV5 0xa00a8009e0a50a9402500920a480900a18a8602180840a1008209e0a7219c807009c006c1188a5c197005a09680561130a46189a00290002 0x15540554155510115440454114440501145144545 14 16383 6 63
def hc_17_1 : Nat → Nat := unpackHintV5 0xa22a60a8e29f907c09c0c6e09b806e01b806e017905c0940c4e093804e013804e00aa4280870c1c007001a08680180838a0c0800c0000000 0x5555455555515555555155555554114415555551555 14 16383 6 63
def hc_17_2 : Nat → Nat := unpackHintV5 0x90024008a19f0e7c01d867409d007401d007401c827009b826e01b806e01b806c09b006a09a0260212183a38d843600d803600c060a9800a 0x155551554555555555555554555555051554 14 16383 6 63
def hc_17_3 : Nat → Nat := unpackHintV5 0xaa0148327084b0c9018ecd1c84368a6910c8297862c0c4c308841082200434306410c80190032005e18a4610901e0c38106040a080c2000600000000 0x5555555455545555455155555555555555555555555555555555555555551555555555555555555555555 15 32767 6 63
def hc_17_4 : Nat → Nat := unpackHintV5 0xd603580d01b010be0ae0686c9e8c665198054494824828f0c3c00f003a08e803808a10260870a1c00682102810c040010002080800008000 0x55555455555555455515555555554555551555555555554515555 14 16383 6 63
def hc_17_5 : Nat → Nat := unpackHintV5 0xa8014e0a981510896311e3a34246808d011419dd3388c6b18c8397862b105408a80150028864c14921920117b2291846307460b8c101c14300880004 0x555555555555554555555051555555555555555555445551555555455155555555555555555555555555 15 32767 6 63
def hc_17_6 : Nat → Nat := unpackHintV5 0xdc568331195989e74c1a2210848023461718990463211108074832411402b0102080040020010006102080840400200100080002 0x1555555555555555554555555555555555555555555555555555555554 13 8191 5 31
def hc_17_7 : Nat → Nat := unpackHintV5 0xbc15721ae014fb2991926322c8420e7c20f609e032fb25528a8093c5248c4900900920023823f207c08e451c8038046628b46138c0d6812201050008 0x555155554551555555555555555555555545555555545551555555545555555555551451555155154555555555555555 15 32767 6 63
def hc_17_8 : Nat → Nat := unpackHintV5 0xd832d24b20a98ca602980a40a900a20a60a921a480900a18a8602180840a100820a0807e11d0a6e1988c62018025628da02a3078c1038010 0x555055051155555545551114015541555454111440155555555555555 14 16383 6 63
def hc_17_9 : Nat → Nat := unpackHintV5 0x89150829f083b0c6e20d031592280c50009e09285238647008c090451f0638187000dc1190a22403a2860508100f0412302010400080010002000010 0x15555455555554555550051155555554555111505555150144044545555455555555455 15 32767 6 63
def hc_17_10 : Nat → Nat := unpackHintV5 0xde0b702da0b602d803600d60b502cc22d18b012c00b002c00ac127108461f867e01f807e01f807a11b8c5e417805e015884e20f902660026 0x45555555555555555555555555555555555555555555555555541155 14 16383 6 63
def hc_17_11 : Nat → Nat := unpackHintV5 0xd91da242e19590cac1948428435002991d2241e19390c6c18d60984a30025b1482d0f441c0a34105e28a46118c17302038343030e040802180010000 0x5555555555554551555555555555554555555555555555455155455455555555515515455555555555555555555555555555555515555545 15 32767 6 63
def hc_17_12 : Nat → Nat := unpackHintV5 0x2 0x1 4 15 2 3
def nh_17 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_17_12 (Nat.sub p 384)) (hc_17_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_17_10 (Nat.sub p 320)) (hc_17_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_17_8 (Nat.sub p 256)) (hc_17_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_17_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_17_5 (Nat.sub p 160)) (hc_17_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_17_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_17_2 (Nat.sub p 64)) (hc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_17_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_17 : Nat → Nat × Nat := unpackForestF 0xbea6b7d0e6fa1a8063fbae9d75d36eb235d63ebaa4b750a6ea128063bb747d6e8e6dca6db84db78496e104031bdb24ca068d6a93281a2d9e3eb3c7b40d1281275024da047d62d12811ed8344a02555ed12809357344a024b568f6ad1d55a36ab46b568d2809254744a8a51528d2a2925002aa0053400a293a253234a48314a8d2920a50026a3e8940096831ed063aa0c6d418d6831a5002400c67399367322ce6399cc6b390e6721a8053f95c9b350a26a124ae4195c7b3209263184ae3595a7d2b136581e4b03495882014de3da547b468f49d1e92a3d234874490851228d2421247a428f0531e0940297c134e82695191323220413468b0511609209a14124a89849128c2092342a40878290a8c21a0a4294085a410a4d208a34112e8207b051320a224103100a4efc935f922bf2397e46afc535f8a2bf1350087ef4539e8a6bd0467a07cf40d9e8133d01e00876e3935e29238e4171c7aee491d7183b01475880e38d5c6a6b8d3d73848e6101c69ab8c3e71872010ddc2262d5466f898b5515b81f3703d5aa88b51396a26ad43e6ba88b50f56a1e350445a86cd25116a1ab343d6686ccd0d59a1a2d43464288c80f1921a320345a85ac61116a133014461868c00f1821a300345a84abb0f5761b2ec355d868b50916a0f2d9445b068b60916a0e8043354694a8d1951272a24a5448cacd115b1a2b12454484a84f5509aaa1250085e9952932a32653e4ca7a991393225264464ea889e0d13a12264424c86c99099320f0042b3d69c7ad292aa61eb4649a487ad08f5252324047a488c8c11a0a230403d48c7a4f4f496a2034438607a494f4251f640418287d8c1020a1f5403f2607e480fa9a1e8463d05c7a0a402139e03c20a6c760f0829a9cc2e3985a414d082271c1342089a41130d49a1a844358486a09082251a0242088c664d08222988263104a6209082221744c2e8785d090ba0e104422087c5a110821e955342a89856090aa221042d29868410989a9a14024268984e0909a22104252405a480989012920242084841078849a110242108842090820e80423162942c518589d0b1361609c2c12858230d5441a878360d06a1a0b0421607c2c0e8581b0b534168982e0905a220b0320083602938052509e4c13c8002918489e0913401484028f8051d07f480fe80028d838a60714401464165003292059300b8481610004a30413009a6810480221a040300126c021281a1202930058600a0d004230083a03868044800a10010240106c02064020b8000f 9 10
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 384 (dagTraceF m_17 s_17 6 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 384 bds_17 (dagTraceF m_17 s_17 6 f_17) (cur_17 0) (nh_17 0) s_17 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 32 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_1 : treeBlockF 32 64 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_2 : treeBlockF 64 96 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_3 : treeBlockF 96 128 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_4 : treeBlockF 128 160 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_5 : treeBlockF 160 192 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_6 : treeBlockF 192 224 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_7 : treeBlockF 224 256 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_8 : treeBlockF 256 288 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_9 : treeBlockF 288 320 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_10 : treeBlockF 320 352 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_11 : treeBlockF 352 384 ch_17 = true := by decide +kernel
theorem nj_17_1 : ∀ i, 0 ≤ i → i < 64 → ch_17 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_17_1 h1 h2)
theorem nj_17_2 : ∀ i, 0 ≤ i → i < 96 → ch_17 i = true := block_join nj_17_1 (fun _ h1 h2 => treeBlockF_at nb_17_2 h1 h2)
theorem nj_17_3 : ∀ i, 0 ≤ i → i < 128 → ch_17 i = true := block_join nj_17_2 (fun _ h1 h2 => treeBlockF_at nb_17_3 h1 h2)
theorem nj_17_4 : ∀ i, 0 ≤ i → i < 160 → ch_17 i = true := block_join nj_17_3 (fun _ h1 h2 => treeBlockF_at nb_17_4 h1 h2)
theorem nj_17_5 : ∀ i, 0 ≤ i → i < 192 → ch_17 i = true := block_join nj_17_4 (fun _ h1 h2 => treeBlockF_at nb_17_5 h1 h2)
theorem nj_17_6 : ∀ i, 0 ≤ i → i < 224 → ch_17 i = true := block_join nj_17_5 (fun _ h1 h2 => treeBlockF_at nb_17_6 h1 h2)
theorem nj_17_7 : ∀ i, 0 ≤ i → i < 256 → ch_17 i = true := block_join nj_17_6 (fun _ h1 h2 => treeBlockF_at nb_17_7 h1 h2)
theorem nj_17_8 : ∀ i, 0 ≤ i → i < 288 → ch_17 i = true := block_join nj_17_7 (fun _ h1 h2 => treeBlockF_at nb_17_8 h1 h2)
theorem nj_17_9 : ∀ i, 0 ≤ i → i < 320 → ch_17 i = true := block_join nj_17_8 (fun _ h1 h2 => treeBlockF_at nb_17_9 h1 h2)
theorem nj_17_10 : ∀ i, 0 ≤ i → i < 352 → ch_17 i = true := block_join nj_17_9 (fun _ h1 h2 => treeBlockF_at nb_17_10 h1 h2)
theorem nj_17_11 : ∀ i, 0 ≤ i → i < 384 → ch_17 i = true := block_join nj_17_10 (fun _ h1 h2 => treeBlockF_at nb_17_11 h1 h2)
theorem nc_17 : ∀ i, 0 ≤ i → i < 384 → ch_17 i = true := nj_17_11
theorem lb_17 : LowerBin m_17 s_17 g_17 7 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xff00ff0000000000
def s_18 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_18 : Nat := 0x100150000000000
def ep_18 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_18 : Nat → List (Nat × Nat) := fun _ => []
def nh_18 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 0 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 0 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xffff000000000000
def s_19 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_19 : Nat := 0x117000000000000
def ep_19 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11), (m_8, s_8, 4, g_8), (m_7, s_7, 4, g_7)]
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_19_1 (Nat.sub p 32)) (cc_19_0 p) (Nat.blt p 32)
def hc_19_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_19_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_19 : Nat → Nat := fun p => Bool.rec (hc_19_1 (Nat.sub p 32)) (hc_19_0 p) (Nat.blt p 32)
def f_19 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 43 (dagTraceF m_19 s_19 6 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 43 bds_19 (dagTraceF m_19 s_19 6 f_19) (cur_19 0) (nh_19 0) s_19 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 43 ch_19 = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 43 → ch_19 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 43 → ch_19 i = true := nj_19_1
theorem lb_19 : LowerBin m_19 s_19 g_19 7 :=
  lowerDagV5 (kn_cons lb_12 (kn_cons lb_11 (kn_cons lb_8 (kn_cons lb_7 (kn_nil))))) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xffff00000000
def s_20 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_20 : Nat := 0x155700000000
def ep_20 : Nat := 0x4200000000000004020000000000001002000000000000155400000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cc_20_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_20_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_20 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_20_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_20_0 p) (Nat.blt p 32)
def hc_20_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_20_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_20_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_20 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_20_2 (Nat.sub p 64)) (hc_20_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_20_0 p) (Nat.blt p 32)
def f_20 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 64 (dagTraceF m_20 s_20 5 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 64 bds_20 (dagTraceF m_20 s_20 5 f_20) (cur_20 0) (nh_20 0) s_20 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_0 : treeBlockF 0 32 ch_20 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_1 : treeBlockF 32 64 ch_20 = true := by decide +kernel
theorem nj_20_1 : ∀ i, 0 ≤ i → i < 64 → ch_20 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_20_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_20_1 h1 h2)
theorem nc_20 : ∀ i, 0 ≤ i → i < 64 → ch_20 i = true := nj_20_1
theorem lb_20 : LowerBin m_20 s_20 g_20 6 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff00ff00000000
def s_21 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_21 : Nat := 0x17005700000000
def ep_21 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xf0f0f0f000000000
def s_22 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_22 : Nat := 0x10105000000000
def ep_22 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xf0f0f0f00000000
def s_23 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_23 : Nat := 0x107050700000000
def ep_23 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xcccccccc00000000
def s_24 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_24 : Nat := 0x4044400000000
def ep_24 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x3333333300000000
def s_25 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_25 : Nat := 0x113111300000000
def ep_25 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0x5050505050505050
def s_26 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_26 : Nat := 0x10105010105050
def ep_26 : Nat := 0x1000400000001040000040400010004000000000000000000000000000101000101000000000000000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x5555555500000000
def s_27 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_27 : Nat := 0x115155500000000
def ep_27 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_8, s_8, 4, g_8), (m_3, s_3, 4, g_3), (m_0, s_0, 4, g_0)]
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def hc_27_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_27_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_27 : Nat → Nat := fun p => Bool.rec (hc_27_1 (Nat.sub p 32)) (hc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 43 bds_27 (dagTraceF m_27 s_27 6 f_27) (cur_27 0) (nh_27 0) s_27 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 ch_27 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 43 ch_27 = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 43 → ch_27 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 43 → ch_27 i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_8 (kn_cons lb_3 (kn_cons lb_0 (kn_nil))))) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x666600006666
def s_28 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_28 : Nat := 0x44600006666
def ep_28 : Nat := 0x622000000000000000000000004200000000000004020000000000000000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1a4351bc250fc2927d8d5ed5951d1540f 7 127 3 7 6 63 10 1023
def nh_28 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_28 : Nat → Nat × Nat := unpackForestF 0xfa7536ef0ca5d5e290aa0f 3 6
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 10 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 10 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 10 ch_28 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 10 → ch_28 i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x6600660066006600
def s_29 : List Nat := [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600]
def g_29 : Nat := 0x40002006600
def ep_29 : Nat := 0x200620000000400000064000000000000000000000004000200000000000000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa3963100f 4 15 2 3 10 1023 12 4095
def nh_29 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_29 : Nat → Nat × Nat := unpackForestF 0x18e71880f 1 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 3 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 3 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 3 ch_29 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 3 → ch_29 i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x3030303030303030
def s_30 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_30 : Nat := 0x10101010103030
def ep_30 : Nat := 0x1000202000001000000020200010000000000000000000000000000000000000000000000010101010100000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xc0c0c0c0c0c0c0c0
def s_31 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_31 : Nat := 0x40000040c0
def ep_31 : Nat := 0x408000000040000040c00000004000000080000000000000000000000000000000000000004000004000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xcccc0000cccc
def s_32 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_32 : Nat := 0x444000044cc
def ep_32 : Nat := 0x408800000000000000000000004000000088000004000000000000000000000000000000044400004400
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xff000000ff00
def s_33 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_33 : Nat := 0x150000007700
def ep_33 : Nat := 0x620000000000000000000000000000000000000004000000000000001000000022000000150000004400
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xf0f00000f0f0
def s_34 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_34 : Nat := 0x1050000070f0
def ep_34 : Nat := 0x60a000000000000000000000004000000080000000000000000000001000000020000000105000004000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xf0f00000f0f
def s_35 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_35 : Nat := 0x5070000070f
def ep_35 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000050400000400
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xaaaa0000aaaa
def s_36 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_36 : Nat := 0x2000022aa
def ep_36 : Nat := 0x22a800000000000000000000000200000088000000020000000000000002000022000000000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xf000f000f000f000
def s_37 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_37 : Nat := 0x100010007000
def ep_37 : Nat := 0x1000600000001000000060000000000000000000000000000000000000001000100020000000100010004000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_37_1 (Nat.sub p 32)) (cc_37_0 p) (Nat.blt p 32)
def hc_37_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_37_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_37 : Nat → Nat := fun p => Bool.rec (hc_37_1 (Nat.sub p 32)) (hc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_37 : Nat → Bool := dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 43 bds_37 (dagTraceF m_37 s_37 6 f_37) (cur_37 0) (nh_37 0) s_37 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 ch_37 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 43 ch_37 = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 43 → ch_37 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 43 → ch_37 i = true := nj_37_1
theorem lb_37 : LowerBin m_37 s_37 g_37 7 :=
  lowerDagV5 (kn_cons lb_15 (kn_cons lb_4 (kn_cons lb_5 (kn_cons lb_6 (kn_nil))))) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xf000f000f000f00
def s_38 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_38 : Nat := 0x100050003000700
def ep_38 : Nat := 0x200020000000400000004000000000000000000000000000000000001000000030002000100050000000400
def bds_38 : List (Nat × List Nat × Nat × Nat) := []
def cur_38 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_38 : Nat → Nat := fun _ => 0
def f_38 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_38 : Nat → Bool := dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 1 (dagTraceF m_38 s_38 3 f_38) cur_38 nh_38
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 1 bds_38 (dagTraceF m_38 s_38 3 f_38) (cur_38 0) (nh_38 0) s_38 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38 : treeBlockF 0 1 ch_38 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 1 → ch_38 i = true := fun _ h1 h2 => treeBlockF_at nb_38 h1 h2
theorem lb_38 : LowerBin m_38 s_38 g_38 4 :=
  lowerDagV5 (kn_nil) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xcc00cc00cc00cc
def s_39 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_39 : Nat := 0x40044000400cc
def ep_39 : Nat := 0x8800000040000000c80000000000000000000400000004000000000000000000000004004400040000
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
def cur_39 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_39 : Nat → Nat := fun _ => 0
def f_39 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_39 : Nat → Bool := dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 1 (dagTraceF m_39 s_39 3 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 1 bds_39 (dagTraceF m_39 s_39 3 f_39) (cur_39 0) (nh_39 0) s_39 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39 : treeBlockF 0 1 ch_39 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 1 → ch_39 i = true := fun _ h1 h2 => treeBlockF_at nb_39 h1 h2
theorem lb_39 : LowerBin m_39 s_39 g_39 4 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xffff0000
def s_40 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_40 : Nat := 0x13170000
def ep_40 : Nat := 0x40000000000000206000000000000131200000000000010140000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xff00ff00
def s_41 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_41 : Nat := 0x13007700
def ep_41 : Nat := 0x64000000000000000000000000000200000000000000130022000000000010004400
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xff00ff
def s_42 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_42 : Nat := 0x1700ff
def ep_42 : Nat := 0xe80000000000000000000000000006000000000000001200000000000000140000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xf0f0f0f0
def s_43 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_43 : Nat := 0x101070f0
def ep_43 : Nat := 0x60e00000000000000080000000000000000000000000101020000000000010104000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xf0f0f0f
def s_44 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_44 : Nat := 0x307070f
def ep_44 : Nat := 0x4080000000000040008000000000000000000000000030202000000000000040400
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xcccccccc
def s_45 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_45 : Nat := 0x444cc
def ep_45 : Nat := 0x44c80000000000040088000000000004000000000000000000000000000000044400
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xaaaaaaaa
def s_46 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_46 : Nat := 0x20222aa
def ep_46 : Nat := 0x20a80000000000000088000000000202000000000000020222000000000000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
def cur_46 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_46 : Nat → Nat := fun _ => 0
def f_46 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 1 (dagTraceF m_46 s_46 3 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 1 bds_46 (dagTraceF m_46 s_46 3 f_46) (cur_46 0) (nh_46 0) s_46 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46 : treeBlockF 0 1 ch_46 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 1 → ch_46 i = true := fun _ h1 h2 => treeBlockF_at nb_46 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 4 :=
  lowerDagV5 (kn_nil) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff000000ff000000
def s_47 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_47 : Nat := 0x100000013000000
def ep_47 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xff000000ff0000
def s_48 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_48 : Nat := 0x17000000170000
def ep_48 : Nat := 0x600000006000000120000001200000014000000140000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x4 0x0 6 63 3 7
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 3 f_48) (cur_48 0) (nh_48 0) s_48 3 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 3 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 4 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf000f000f000f0
def s_49 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_49 : Nat := 0x100050001000f0
def ep_49 : Nat := 0xa000000040000000e00000000000000000000000000000000000100000001000000010005000100000
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
def cur_49 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_49 : Nat → Nat := fun _ => 0
def f_49 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 1 (dagTraceF m_49 s_49 3 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 1 bds_49 (dagTraceF m_49 s_49 3 f_49) (cur_49 0) (nh_49 0) s_49 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49 : treeBlockF 0 1 ch_49 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 1 → ch_49 i = true := fun _ h1 h2 => treeBlockF_at nb_49 h1 h2
theorem lb_49 : LowerBin m_49 s_49 g_49 4 :=
  lowerDagV5 (kn_nil) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xf0f00000f0f0000
def s_50 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_50 : Nat := 0x107000003070000
def ep_50 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x5050a0a05050a0a0
def s_51 : List Nat := [0xa0a00000a0a0, 0x1010202010102020, 0x5000a0005000a0, 0x5050a0a0]
def g_51 : Nat := 0x100000101020a0
def ep_51 : Nat := 0x100020a000000000000000000010000000000080000000000000000000100000101020000000000000000000
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

def m_52 : Nat := 0x4444444444444444
def s_52 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_52 : Nat := 0x4044400044444
def ep_52 : Nat := 0x400000000440000044400004004000040000000404000004000000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x2222222222222222
def s_53 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_53 : Nat := 0x2000202022222
def ep_53 : Nat := 0x200222000000000000020200002000200000000000200020202000000000000000000000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_53 : Nat → Nat := fun _ => 0
def f_53 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 1 (dagTraceF m_53 s_53 3 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 1 bds_53 (dagTraceF m_53 s_53 3 f_53) (cur_53 0) (nh_53 0) s_53 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 1 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 1 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 4 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xa0a0a0a0a0a0a0a
def s_54 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_54 : Nat := 0x200020202020a
def ep_54 : Nat := 0x200020800000000000000080002000200000008000000000000000000020002020202000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xc0c0c0c0c0c0c0c
def s_55 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_55 : Nat := 0x404040004040c
def ep_55 : Nat := 0x800000400000004080004000000040008000000000000000000000000000000000004040400040400
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x55aa000055aa
def s_56 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_56 : Nat := 0x1502000055aa
def ep_56 : Nat := 0x40a800000000000000000000000000000000000004020000000000001002000000000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x1a4471b4371343927d8d5ed5949d1540f 7 127 3 7 6 63 10 1023
def nh_56 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_56 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 10 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 10 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 10 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 10 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xff00ff00ff00ff00
def s_57 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_57 : Nat := 0x100150013007700
def ep_57 : Nat := 0x1200620000001400000064000000000000000000010004000200000001001000130022000100150010004400
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_2, s_2, 4, g_2), (m_41, s_41, 5, g_41), (m_37, s_37, 7, g_37), (m_33, s_33, 5, g_33), (m_38, s_38, 4, g_38), (m_29, s_29, 5, g_29), (m_15, s_15, 4, g_15), (m_4, s_4, 4, g_4)]
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xf81aa6e3dc0b81702d0da0b03412804e19c1306604c094328240c80847082103e27c0f81d1343680c841c001 0xa91d93a332627e4a4ec889b901331f25e3c48c5c1f1ca4f374966691cbd218b14e2b09c3a0d065aa0b8241b8a634d7860af8b05214068251483caf0684e094c00c9402d2404c510829c0d14814af05453074a408908081a51b4fa169736d1e61a1ca94f932972251e40a1c793f8d277004ddd499b604f600967411c70218a83f13076220dc40198701f0c0360605c04098001f 11 2047 5 31 11 2047 19 524287
def cc_57_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa028098a155e9525413244910440c5300b12c083200801c45214050140320c0300c0300481000400 0x7cd41ea5087182136c825b1f95c784d2fb5cbcd46bb50ac972a95ca8542893f9a4ee2137764cd705c4c0d1284470091685c480d1b5606ad71a05c581311034640f18a444011180245b141714d58515492850491245046901093c 10 1023 4 15 11 2047 18 262143
def cc_57_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x7e3e1f0f8753a1b4bc4e26130984c2291088441cce06230148a049241043a0a040201001 0x2994da05264945865065450b6932015cb24d2e93fb84eed137b04ce912f9e4ae39278448e9c60a49b284609edb2716c95142425c95142324c90d423350991825c5092d823a6c8a932015c7c4d20350 9 511 3 7 11 2047 18 262143
def cc_57_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a50942508ca308c2306a5374c1304c13044910440f22d0b02c0a1280a0280731c0701485001400 0x3785d7e157e028f6093ea4bf490fc94edc13f204b7811d8843f00bfb823fe97bf15eec4d3685fc416dd8575e14f9460e2933796cdc4d3a13fe64ef8137da4cf5024d15833b5ccc1732244c60935a4fd292f2a47c490f084e 10 1023 4 15 11 2047 18 262143
def cc_57_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0340d02f5bc2f0a96a0a8264982519424190204801b56c1745c1705c152541323d0b42c0b006801 0xa04b93e57278a84e85c9c0a12e57e689b8d84f9906e1405e5da9cb3497f264300fe509a49351740bed616d442b9c8538e2bce617da42da6857370a6e4175a02ca5855360a29514221261685c86069140fe241dc383785066e213d9c25a284735087191622e294245083498e017d942da2057330a70413204203c924 10 1023 4 15 11 2047 19 524287
def cc_57_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x3440 0x28a2f5134e 3 7 1 1 11 2047 19 524287
def cur_57 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_57_5 (Nat.sub p 160)) (cc_57_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_57_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_57_2 (Nat.sub p 64)) (cc_57_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_57_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_57_0 : Nat → Nat := unpackHintV5 0x9c305971528b8b98991f85445854008342082c0880923750b96fc54652aa60250561a14a2bf462403bda537d402d2ab2d2002b0222a20e2a20025949248112480020246156ac0fe58050ae0005000000 0x5aaaaad6aab5aaaaaaaaaaaaaa318c6aa318c6aaaed55555555445468d51aa8a9d15dbd5576ccbc446318ce1c51153d6c3b6c555550951a024ab4a8d46301d43874200504701831950760a048e906000550000000055000550000155000000005507600aa0020200030600c0000010000118c631800280ed5404000006a306000c00000000000154200077320028aaa301a2000c18aaaa00ed5468282aaab28d51a82a70000006318c00155410006a30000000000400000180300154002641d8004aa2318c68000200022aa301a88800c18aa82aa0ed41555500546a8d5903694f0edbdec9467581e318c628aa227dbb0182bc86318c02000041a8c603a55a802a8750ce2000c18aaac0cc800a0ec015400400000154001540001540040000015400154001d88080000030600c000418c6318c6318c6318c63 20 1048575 8 255
def hc_57_1 : Nat → Nat := unpackHintV5 0x99c02620593c4e262958f0d471c51c01272043c61000f3b44cc42931000ba0a298508c1a2141c85001f81c403e0dc2437000dc0032050b4142409090001f0503c400f00014280005 0x6c59cd8339b111ed95515155546aaa31aa8c631a9d1545518c6355555daaaacaaef61c11ef6c30e26f60c3ed73163d88f7b904187daf635ef63d8c437b550546318ce1c511db6f7b6dabdced7b 18 262143 8 255
def hc_57_2 : Nat → Nat := unpackHintV5 0xba715c816df0b6f80b3c859e02bf212be87df0307d133a0960749c2a088cff0a7d053c449a678b738521329001284094003f951fc00ce603e521495068780e4c07000007 0x2a8a28c6318c6319c38aaa88dbda3dced1b2aaa8c631aa8c631aaaaaaacaaaaaaaef75aaaef75aaaaaaaaaaaa9ce73aa8c6318c631aaaaaaaa802a800000002a802a801bd821c6737bded760ce6c4d8ac7b360339b47b96ebdc9359cd888319cdee77b46db5dc58dd9b 17 131071 7 127
def hc_57_3 : Nat → Nat := unpackHintV5 0x84071050320a004140081e0b01c220102bfd05756a4bd6d971892cd1658c0eb0415520ea9d075300a9fc64ea559b81c370006a040d18299e0532a125e86cb70616e0029c4041524285a80050 0x18c6300099d83d806d600b5800000000000b580000c631800000006c000100018300600000318c600024025bdee136c6f6890f7b937bdb083daaaa8a8caacaac318c6aac8a8318c6aed5556555555dece087dec4decd88f7b90761f63db071145146318ce1c551146aaaa318c6aa318c6aed5555546aaaaa22a3546a8a9d1500550000000055005500 19 524287 8 255
def hc_57_4 : Nat → Nat := unpackHintV5 0xb3454ae450a90549e2ae9ce149bd118ecd18ca22888427a2e674e546a4aa654505aaaa4ebbf434b73f14333fb22ef502905f28b0528605286002731327300260131f56b195601395c0e950026c300026 0x55000000005500550055000055550000000000001550000000055005500040001360300018d54000000000000010005540154036007362b20a26c0546a3180c6318c6318c100079c0e03062a88af9651a34436f00361c7800718c630000990040381ce3518c6318c6318c0626d4150e00c18c62a9e53ca08d1a29c401540040000015401540000154004d8000000800000c1803000550055000110400106318c681b000155001411146aa8d5460353a809b0018315555550554500006a3000013600000303800000c01800aa0034682000900000807006318c00180030e0006c0000000200118c6300000018c630000073200318c6000006c00006002000300600000c63180009000002a800000002aaa80000000c6318c631800000399dec19cdec187000018c6300000001800318c6000135cd60000000000b9cd601540000318c754000000000000aa00000000aa00aa0002000000318c60300018c0000000036003020004006318c00004e000c4 20 1048575 8 255
def hc_57_5 : Nat → Nat := unpackHintV5 0x18fab53904a0ae141400050 0x4d8000351803060000000000000aa024000234680086c046318c0005544d8280aaa301aa346a82000a09c060c5541555555145500000000005555000000000000550000550055 18 262143 8 255
def nh_57 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_57_5 (Nat.sub p 160)) (hc_57_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_57_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_57_2 (Nat.sub p 64)) (hc_57_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_57_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_57 : Nat → Nat × Nat := unpackForestF 0x169f44d3805a5ce25c9c2b938542702e4e0500168f324de641b80b43966a72cd2404a7ca1340129724d4404a3809430127f1c578049dc0c58818a50a0fe141dc424c8506f0c0d21419c0c508149902132042000937764bcec579dd25bd8287b048ee90ddca73b82f77046ec4d00499b693f6d276e3181c526369376e2d8dc4d1b4998084f6149ed40918525b3560666b8cc1718523b1a4463048c290d84270084b3b6b876d45609fac13b5b498b04dd649a2c1333b6a076970ecae1d950528c0a49b0ec9fa74604e6d89c5b0ec9da2c60458a09514115b024350454d88cd4115261d9373c8c078db0f0b6203503c2b87ad40f5281e1343b2660211c75279c0241d49669580d1ae1a05c1d48e640f0c122180241d48658534b628161451d09c3c8eca094141241e4663c4fc789d91c50234803c4dc849e0f1331e25e3c48c741a00843168a62cd7865aa0b15f170482c148041f8a0340107625148041b808330f2bc0207c34270081b0b4900914c22288414e044a40b14814af022420102e040d004098001f 8 11
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 3 7 bds_57 164 (dagTraceF m_57 s_57 8 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 3 7 164 bds_57 (dagTraceF m_57 s_57 8 f_57) (cur_57 0) (nh_57 0) s_57 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 64 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_2 : treeBlockF 64 96 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_3 : treeBlockF 96 128 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_4 : treeBlockF 128 160 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_5 : treeBlockF 160 164 ch_57 = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 64 → ch_57 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nj_57_2 : ∀ i, 0 ≤ i → i < 96 → ch_57 i = true := block_join nj_57_1 (fun _ h1 h2 => treeBlockF_at nb_57_2 h1 h2)
theorem nj_57_3 : ∀ i, 0 ≤ i → i < 128 → ch_57 i = true := block_join nj_57_2 (fun _ h1 h2 => treeBlockF_at nb_57_3 h1 h2)
theorem nj_57_4 : ∀ i, 0 ≤ i → i < 160 → ch_57 i = true := block_join nj_57_3 (fun _ h1 h2 => treeBlockF_at nb_57_4 h1 h2)
theorem nj_57_5 : ∀ i, 0 ≤ i → i < 164 → ch_57 i = true := block_join nj_57_4 (fun _ h1 h2 => treeBlockF_at nb_57_5 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 164 → ch_57 i = true := nj_57_5
theorem lb_57 : LowerBin m_57 s_57 g_57 9 :=
  lowerDagV5 (kn_cons lb_13 (kn_cons lb_2 (kn_cons lb_41 (kn_cons lb_37 (kn_cons lb_33 (kn_cons lb_38 (kn_cons lb_29 (kn_cons lb_15 (kn_cons lb_4 (kn_nil)))))))))) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xf0f0f0f0f0f0f0f0
def s_58 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_58 : Nat := 0x101050101070f0
def ep_58 : Nat := 0x100060a000001040000060e00010004000000080000000000000000000101000101020000010105010104000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_37, s_37, 7, g_37), (m_34, s_34, 5, g_34), (m_43, s_43, 5, g_43), (m_30, s_30, 5, g_30), (m_26, s_26, 5, g_26), (m_22, s_22, 5, g_22), (m_3, s_3, 4, g_3), (m_31, s_31, 5, g_31), (m_10, s_10, 4, g_10), (m_49, s_49, 4, g_49), (m_51, s_51, 5, g_51), (m_6, s_6, 4, g_6), (m_5, s_5, 4, g_5)]
def cc_58_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc3a8ae3dc0b43682c0d80a85502a04e39c13825144388108610401801002003e16c8d81a0b40642c801c001 0x1f8a04092879231c24f374966691cbd218392e210683a0b86daf0c82e152a22e4e456b009250142b82494844af0b452132a620504381a06154080681717c29298495e070a40a0d00d295134fa06973cd1e75a1ce14f9a2972851e40a1c713f8d277004ddd499b604f600967411c70218d03f180761e0dc34198301f040360405c04098001f 11 2047 5 31 11 2047 19 524287
def cc_58_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82e0b0a75769d06c9925c9705c12548111440e3380e0380e0380e0308c02c4b02c0b02480900000 0x7c941e95086db21260825b1f95c784d2fb5cbcd42ea5cb8572d951a8542813f9a4ee2137764cdc844580d15844400f150343e0b1b5606ad71a05c500d0f02c640f18a444c1118024551414a404e4f1214c46511723b5a8cd613f564ed41374c4cd292f4448c401e 10 1023 4 15 11 2047 18 262143
def cc_58_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c3f1f0dc6c361b0ca642e938984c2610680401c8e06230164a250281083a18050201001 0x2912f9e4ae49278648e8a4e9c92a2a468490a3c50b0932015cac4d2d13fb24eeb937aa4ce9b6ca49b289609edb2726094972395094d4231508f142324c991825c50929b2424c8a582015c7a4d20150 9 511 3 7 11 2047 18 262143
def cc_58_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a5094250942328c2306a5374c1304c13044910440f22d0b0284a0280a0280731c0701485001400 0x3785d7e157d828f4093eb4ef892fca43dc13f204b7811d8843f00bfb823ff17bf15eec4d3685fc416dd8575e14f9460e2933796cdc4d3a13fe64ef8137da4cf5844d15833b5ccc1732244c6093524fd292f2a47c490f082e 10 1023 4 15 11 2047 18 262143
def cc_58_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0700bc6f0b86e0b82e0b82e0a5690a4290916407d5b46c1745c1705c152541323d0b42c0b006801 0x4f9519b8bd364ba65ae4c350974b92c172542849c5f9228e2611c2817c88178f6bce817da82da8057380a6e617da42da6857370a6e4175a02ca5855360a3109311ca0430341f059140fe241dc383785066e213d9c25a404735087191622e294245083498e017d942da2057330a70413204203e934 10 1023 4 15 11 2047 19 524287
def cc_58_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x28308040 0x24d53a3525fd310b07e8634 6 63 3 7 10 1023 18 262143
def cur_58 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_58_5 (Nat.sub p 160)) (cc_58_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_58_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_58_2 (Nat.sub p 64)) (cc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_58_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_58_0 : Nat → Nat := unpackHintV5 0xdc8066b617314a357f458b1c6f5541d25ea5d2f4009262a48b042458011c8328d00a4680021e0b0f5cca6de682ca52965000ac83052e1b26f1413382092c383ce6419b260971b44045a150590104c00004000000 0xacb3cf964c30d3002cb2cb47473c71cf00003c71cf00a1c787ab8b8b008b8b2ea2d32c32c32cb00002c0b2d2d2cb1c71e8f4c32c32c015d5eaaaa3c33c34ea87a8b80000000173cf5d30c34e65e6802aa0eaeaaa00aa970cf0c33c71cf69000c30c32cb4b4b0c30c30cf00003cf3cf0c30c3008b8b83aba0c3008b8b0cf0c30c70c3a8000030d0d0c30cb0c30e830c30c000f57eaaaabad87ada7d30eb2e0ebab5c30c071df430d00a83a99a87a830c30e83000000005cf3e6a60c30c300aaaaaa0eac02a833cf0cf3cf3cf3e00f3cf3d30c34d75d75e2e2e0e00c25cb8b2c33cf0cf3c0000f3cf3d30c34c022e2e830e0eac025cb8b2cb3cb1cb1cb2ea00002c0b5cb4b4b2c30c3ac3a4c32e3ebadf1cb8b1eacba834c34c00f7d2d2e99aa1cba1cba932c02d62cf3d700004f55d5c02a87a93a83a00008baaaaa970005ab5a54f3cf3cf3cf3d75d75d5554122e2e2e2c2c1454f3cf3c0001553d54022e2e2e2c016ad553d51d54d50d400010552d3d70554c30d30055a56aea973cf5c000151d5543553000055550056aaa8016555ab3cf3cf00004f3d3cf5757008f2e2cb972e2cb000a55ab2cf2c72c72cb2d32c32c32cb0000a9500000000 21 2097151 9 511
def hc_58_1 : Nat → Nat := unpackHintV5 0xcc81b3200c606ae23684b421200798b1be286887190125f8494836520013c0c4a051062240018fa063b038e60639800e00631868c6002e830ac0e2b000ac00298180c9a000300000 0xac34db6b0d31ae931cacba87a0eaa931c71c720000000029a9a1c71c700aaaa1eaea8002aabacb930d2d2bac432d70eb4c34aeb6e35b2b472bae2d4b4c31adbac6ebacac4cb2eb6eb2eaeb1dbae2eb6eb2cacf1c73e01b6cf1c73db6e1c78722e2c1c22e2cbacb 18 262143 8 255
def hc_58_2 : Nat → Nat := unpackHintV5 0xdf202f08ca418220708681a140685001fe167f801e8165d1d16a0a590195e064f08936064b821022c39870d01634000b020240809000240007a16120c83612078600c1203000000c 0x1c71c700001c71c74d34d300a2aa00aa0701c71c76e79db1c71c76e79dba280aaaa551c71c755000000a255aa001c71c700471d4c30d300a870aa99aeb1cae2eb1c2e1c71c700001c71c700a887aa000aaaaebac34d91aebaeb834c6b5e83ad9b2bab434c6b1e76eb8b0d38db6b1cae2d91c34c1aeb8badb9ebac8ba6c6b4eb 18 262143 8 255
def hc_58_3 : Nat → Nat := unpackHintV5 0xc245cc0410be80ebe800be800bdc06bd006bc406aa09286d1a82c207f41c7e4087d806788287700c7640671c24584cc58400558164f8304ec064e0064cc0a4802645c1245c003f43431c6c1010e00080 0x134d34c34340175d0d0e2e2d30d6b4caeb6c34c34d36db40575750d40304c30d36db5d570d30d34c00015d5d430d0dac0134c74c74d3540001300c30d30c34c01755d3932d3932e4f6bacbab833eadaeb1d3d8aeb8b2ebaeb1e3cf8ae2e3c71cfa8f83a000000003c71cf98f9a0087abaaaaa802aa3ebad1daeb4c30c75c3aeb6b472bae2d47ad30eb2b2e4c34c71c71da530c34c0071c71c0b2d2d2c71c71c000071c71c021eae871e2e2c0022e2ea1d31c31c31c700001c747471c72c70c30c300001c71c70c30c300a2aa00aa 20 1048575 9 511
def hc_58_4 : Nat → Nat := unpackHintV5 0x7a1519b9d7467837992c5a5b44b95d080532211380a44b01811b0883f73a8f70363c9098ee022327488bf45429c3088391c1ce2006606c1950186480619200061c161870005f0161441c03f88c0ce180238800263400004c 0xc31c30c30c30c30c70eb000000000d0c30d0c71c71c30c30c003830c3832c71c71c30c30c00f3cf3c30c71c31c3ac30c31c71c00000000171d71d75d30d70d34d3535d3534c00f1c73d30cf0cf3d38f2d38f2c0173d73d571c75d54d0d4000000011dad55555003c71cf54b655cf5cf00554f1d745ad530c34c0013e2e2c71c71c75c00011dad471d5d5c0151d31c31c31c700001c71c71c73cf3cf003d4f1e1cb1e1c70c30c300005155001c71c70c30c300551c71c7000054555001c71c73cf3cf00550701c71c75d75d75140551c71c73cf3cf3cf3cf55aaaa1c71c7000000555155001c71c70000544755001c71c72cb2cb005551d435554c71c71c40000000055551dad540165552c71c71cf3cf3c01553aeb7d53434c31d5eb4c35eb472cf8f1d71d75c0001471d1dad5d5c0155d37c30d74c000071c73c71cf5cf3c013d3cf7e3cb8f2d534c34c34c00155562e2c34c34d5475534000000001550dad555004c30d354b6500550c30c30d700005757436b50c3000d70c30c70c354000034c30c30c3005d570e0cb0e0c30c30c300005155000c30c31c71c700550c30c350c30c300000555558b8baeb0d31aeb4c310c30c30000054555000c30c300550c30c38db8db0305551400c30c36e38db55aa0c30c3aa000000555551000c30c300005551002cb2cb0c30c3005554755430c30d430010000000155555436b0059554b0c30c300554c351c70d30130c32cb 22 4194303 9 511
def hc_58_5 : Nat → Nat := unpackHintV5 0x83868599503d8e0115620008a 0xc35df0c34d53430d000c38b8b0d30c31c3ac30c30c30c30000000005c71c3430d0c30c30c30c00f1c73c3832c3830c30c30c33c00f5cf0c7031c700c4c01c71c74c30d35d75d71c71c73c30cf3cf3cf3cf3cf0c70eb0c31c70c30c74c70000000070071c71c75d30c34c7475c7471c0071c71cf0c33c7872c7871c00f3cf3c30c70eb1c70c30471d430d000c33cf8b8b 20 1048575 9 511
def nh_58 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_58_5 (Nat.sub p 160)) (hc_58_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_58_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_58_2 (Nat.sub p 64)) (hc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_58_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_58 : Nat → Nat × Nat := unpackForestF 0xa329202d3e851a00b4b9f2a202d1c05a18094f9b25c0252e55ae4ab50954b92a172542800947918bf2251e440b809438f6bc024fc049dc0c58818a50a0fe141dc424c8506f0c0d21419c0c508149902132042000937768bcec579dda73ba4b7a050f4091dd21bb82f77046ec4d00499b693f6d276e3181c526369376e2d8dc4d1b4998084f6b088c293d8525b3560666b8cc1718523b1a4463048c290d84170084b3b6b876d40ed2e1d95c3b2a2aa4fd549dac24c5526eac4d154999d950516d8a29b144b01d93f4e6d89c980ec9da2c60458a094d41153622a4c468a08c93114b01d9373c6d878980f0b6201503c2b87a940f4a81e1343b2660211ce4220ea4f1d49669580d1ae1a05c1d48e640f0c122180241d486448ec89199113f2227653140a5201113727278444cc88979194c232884448c741a0f24a1f8a03c9187417008431b6bc020fc64170083b172722114852b00a15c102a62294844af081410106e1c0d0041986154078be0e94c1caf04034070a40207c141a0081b034a40205c04098001f 8 11
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 4 15 bds_58 164 (dagTraceF m_58 s_58 8 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 4 15 164 bds_58 (dagTraceF m_58 s_58 8 f_58) (cur_58 0) (nh_58 0) s_58 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 32 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_1 : treeBlockF 32 64 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_2 : treeBlockF 64 96 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_3 : treeBlockF 96 128 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_4 : treeBlockF 128 160 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_5 : treeBlockF 160 164 ch_58 = true := by decide +kernel
theorem nj_58_1 : ∀ i, 0 ≤ i → i < 64 → ch_58 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_58_1 h1 h2)
theorem nj_58_2 : ∀ i, 0 ≤ i → i < 96 → ch_58 i = true := block_join nj_58_1 (fun _ h1 h2 => treeBlockF_at nb_58_2 h1 h2)
theorem nj_58_3 : ∀ i, 0 ≤ i → i < 128 → ch_58 i = true := block_join nj_58_2 (fun _ h1 h2 => treeBlockF_at nb_58_3 h1 h2)
theorem nj_58_4 : ∀ i, 0 ≤ i → i < 160 → ch_58 i = true := block_join nj_58_3 (fun _ h1 h2 => treeBlockF_at nb_58_4 h1 h2)
theorem nj_58_5 : ∀ i, 0 ≤ i → i < 164 → ch_58 i = true := block_join nj_58_4 (fun _ h1 h2 => treeBlockF_at nb_58_5 h1 h2)
theorem nc_58 : ∀ i, 0 ≤ i → i < 164 → ch_58 i = true := nj_58_5
theorem lb_58 : LowerBin m_58 s_58 g_58 9 :=
  lowerDagV5 (kn_cons lb_37 (kn_cons lb_34 (kn_cons lb_43 (kn_cons lb_30 (kn_cons lb_26 (kn_cons lb_22 (kn_cons lb_3 (kn_cons lb_31 (kn_cons lb_10 (kn_cons lb_49 (kn_cons lb_51 (kn_cons lb_6 (kn_cons lb_5 (kn_nil)))))))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x3333333333333333
def s_59 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_59 : Nat := 0x113111313133333
def ep_59 : Nat := 0x1200222000001000000020200012000200000000010200020202000000000000000000000110111010100000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 7, g_17)]
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def nh_59 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 0 bds_59 (dagTraceF m_59 s_59 6 f_59) (cur_59 0) (nh_59 0) s_59 6 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 0 (dagTraceF m_59 s_59 6 f_59) cur_59 nh_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 7 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xcccccccccccccccc
def s_60 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_60 : Nat := 0x40444000444cc
def ep_60 : Nat := 0x408800000440000044c80004004000040088000404000004000000000000000000000004044400044400
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_32, s_32, 5, g_32), (m_31, s_31, 5, g_31), (m_55, s_55, 5, g_55), (m_45, s_45, 5, g_45), (m_39, s_39, 4, g_39), (m_10, s_10, 4, g_10), (m_14, s_14, 4, g_14)]
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x292a429098e60981f7785e0691a0681a05cd705856054550505405014035cd0340c1288a006401 0x992b7123d9496921281eb15191396131c9294121c026181e5a40b3515232a93e41329c5e9352895e79445a505b50745e6b5e63525252495e4152394520242a4f1a43eb4ee342d24fba43a143812b3123101e0812001f 10 1023 4 15 11 2047 16 65535
def nh_60 : Nat → Nat := unpackHintV5 0x1df636b199a8876112580875f41d584a5443951004a54126854901520873df48f7803ca28f0053a830e28f36844d68733e38cc07285589e8527a00998a17dd42f60001780000 0x1000c631802346a0000004c00200aa001eccbd780004000f00862c070e0b8b055ac00039701605c5c31c02800070bdd009e205d186396b040002f70ef5d2dd582e18e556a70e5c77bdcbdeefbdc1d0c3de7d2ad6e13e18c72ab53872f738e613c218e415555381e18e39ce7000000218e0005555000000010610431c823650081870e1c4 18 262143 7 127
def f_60 : Nat → Nat × Nat := unpackForestF 0xb4e0b42d9490a4fc129c0260a43ab51a93e09438c5e8b52895e092b79443c5e3b5e3b525b503a52395e3952394509231a4f20241a43081e0812001f 5 11
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 3 7 bds_60 30 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 3 7 30 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 30 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 30 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_32 (kn_cons lb_31 (kn_cons lb_55 (kn_cons lb_45 (kn_cons lb_39 (kn_cons lb_10 (kn_cons lb_14 (kn_nil))))))))) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xff00ff00ff00ff
def s_61 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_61 : Nat := 0x170057001700ff
def ep_61 : Nat := 0xa800000040000000e80000000000000000000600020006000000120002001200000014005400140000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 5, g_21), (m_48, s_48, 4, g_48), (m_11, s_11, 4, g_11), (m_39, s_39, 4, g_39), (m_49, s_49, 4, g_49), (m_42, s_42, 5, g_42)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0x4080e5c3862c0681 0xd2e3d73e9f747927a91cc6e01f 7 127 3 7 10 1023 13 8191
def nh_61 : Nat → Nat := unpackHintV5 0x3e0a7c00e821a8535006210bc1002f0000 0x3cbf7f2cfcccddcdce66666402c0000100 15 32767 7 127
def f_61 : Nat → Nat × Nat := unpackForestF 0x3a7e970e8e64f7ae191cc6e01f 3 10
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 2 3 bds_61 8 (dagTraceF m_61 s_61 6 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 2 3 8 bds_61 (dagTraceF m_61 s_61 6 f_61) (cur_61 0) (nh_61 0) s_61 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 8 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 8 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 7 :=
  lowerDagV5 (kn_cons lb_21 (kn_cons lb_48 (kn_cons lb_11 (kn_cons lb_39 (kn_cons lb_49 (kn_cons lb_42 (kn_nil))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xf0f0f0f0f0f0f0f
def s_62 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_62 : Nat := 0x10705070307070f
def ep_62 : Nat := 0x200020800000400000004080006000200040008000000000000000001020002030202000104050400040400
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_35, s_35, 5, g_35), (m_54, s_54, 5, g_54), (m_50, s_50, 5, g_50), (m_23, s_23, 5, g_23), (m_38, s_38, 4, g_38), (m_9, s_9, 4, g_9), (m_12, s_12, 4, g_12)]
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b09d27090e408c63071dc0701936419060580601715c107401003c4d2340d0340c1288a006401 0xea5d8a55c24582357b46da46514a7234cb5d8b55c345aa3a6a36b952413aab56a256285a72447244945a8c5683567a5a6a56185a6042495c524b4247204c2a3b1a37e347d24bb2479a3b5a37393a3136104a0846001f 10 1023 4 15 11 2047 16 65535
def nh_62 : Nat → Nat := unpackHintV5 0x210807a341e5076f149b8876c045ac87607597f055ee1d574954e1d4c8e5163943054ee3d358c4c81d0d4a42a150a8041628d463285989e8527a00998a17dd42f60001780000 0x110175ae11a3017801001eaeb972c594f5468e8387465eefbab82a97577a8d18dea1c3d5d1ac2eb25c2c011a300003a30f5ee5ef7b97bdca1600b0ba34600001c2f7180500431c08c63184c000000055007824f7caa000f000040002f73c455033039af11a30039c39ce71a8c20000000aa0000066000468e0a046c0d11a30e4001c3883 18 262143 7 127
def f_62 : Nat → Nat × Nat := unpackForestF 0xea5d0b47da460a4bbb5dbb45b9520a47a356a2560a3b645a64566356625a7244625660420a37424b495c4247093a09361a3b204c1a37084a0846001f 5 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 30 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 30 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 30 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 30 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_35 (kn_cons lb_54 (kn_cons lb_50 (kn_cons lb_23 (kn_cons lb_38 (kn_cons lb_9 (kn_cons lb_12 (kn_nil))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xffffffff00000000
def s_63 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_63 : Nat := 0x117155700000000
def ep_63 : Nat := 0x1440000000000016004200000000010604020000000001121002000000000114155400000000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 7, g_19), (m_27, s_27, 7, g_27), (m_18, s_18, 5, g_18), (m_25, s_25, 5, g_25), (m_21, s_21, 5, g_21), (m_24, s_24, 5, g_24), (m_22, s_22, 5, g_22), (m_23, s_23, 5, g_23), (m_20, s_20, 6, g_20)]
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
  lowerDagV5 (kn_cons lb_19 (kn_cons lb_27 (kn_cons lb_18 (kn_cons lb_25 (kn_cons lb_21 (kn_cons lb_24 (kn_cons lb_22 (kn_cons lb_23 (kn_cons lb_20 (kn_nil)))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xffffffff
def s_64 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_64 : Nat := 0x131777ff
def ep_64 : Nat := 0x64e80000000000040088000000000206000000000000131222000000000010144400
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_40, s_40, 5, g_40), (m_42, s_42, 5, g_42), (m_41, s_41, 5, g_41), (m_4, s_4, 4, g_4), (m_46, s_46, 4, g_46), (m_1, s_1, 4, g_1)]
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b0a0e80a02177c9f07c1f07c1c3701c06c5b06c1a14dd304c12148111350d0340c1288a006401 0x8855e845282dda52d05d5055b04d80454835182da04f6847b355ab45a13a4034715c935d53558b4d83457952693a3836404442445c5a54564b563856225c2b4f1b47e34fcb47c13ab936984f60473037102d0825001f 10 1023 4 15 11 2047 16 65535
def nh_64 : Nat → Nat := unpackHintV5 0x20d077a325e5077861dbcca62d8d586655615520753e1526d248c1d208546a31170745c01120a39d58e70038038d90e3463cc911285409e8527a00998a17dd42f60001780000 0x10c026b1600043860b5a930382c58130003843860a0000000318c610028007001a36a800800002007af66401e0f009879aad601c3d4386f59ad5ab0e64e74c73500e1df43863a7ad5ab3543c36732739939bd6b10021c3027a021340273381ce7387390e1833cf21c3551401540000021c3000000550000554038700870c1c403510e08d9 18 262143 7 127
def f_64 : Nat → Nat × Nat := unpackForestF 0xe8450b4fd252d05d0b47093a0936a355a345a13a084f6b5d6b4d6b456952715c693a08473c5a3c563b564244385608371b4f225c1b47082d0825001f 5 11
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 3 7 bds_64 30 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 3 7 30 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 30 ch_64 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 30 → ch_64 i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_40 (kn_cons lb_42 (kn_cons lb_41 (kn_cons lb_4 (kn_cons lb_46 (kn_cons lb_1 (kn_nil)))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xffff0000ffff0000
def s_65 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_65 : Nat := 0x117000013170000
def ep_65 : Nat := 0x1200000000000000000000000016000000040000010600000206000001120000131200000114000010140000
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 7, g_19)]
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def nh_65 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 0 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 0 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_19 (kn_nil)) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffff0000ffff
def s_66 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_66 : Nat := 0x1557000077ff
def ep_66 : Nat := 0x62a800000000000000000000004200000088000004020000000000001002000022000000155400004400
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 6, g_20), (m_33, s_33, 5, g_33), (m_32, s_32, 5, g_32), (m_34, s_34, 5, g_34), (m_35, s_35, 5, g_35), (m_36, s_36, 5, g_36), (m_28, s_28, 5, g_28), (m_15, s_15, 4, g_15), (m_9, s_9, 4, g_9)]
def cur_66 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x10574c9ab35d226c9168dab1156768ea51c49b801f 6 63 2 3 11 2047 15 32767
def nh_66 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0x14b9756de738cef18e3af60000059f5ce719e631ad5abb53800003b1b6e1adeb94e338c7332a8d000005d1c671c33cb59469d000000000 16 65535 7 127
def f_66 : Nat → Nat × Nat := unpackForestF 0x415d168ecd744a3945a26ac455849b801f 4 11
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 3 7 bds_66 9 (dagTraceF m_66 s_66 7 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 3 7 9 bds_66 (dagTraceF m_66 s_66 7 f_66) (cur_66 0) (nh_66 0) s_66 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66 : treeBlockF 0 9 ch_66 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 9 → ch_66 i = true := fun _ h1 h2 => treeBlockF_at nb_66 h1 h2
theorem lb_66 : LowerBin m_66 s_66 g_66 8 :=
  lowerDagV5 (kn_cons lb_20 (kn_cons lb_33 (kn_cons lb_32 (kn_cons lb_34 (kn_cons lb_35 (kn_cons lb_36 (kn_cons lb_28 (kn_cons lb_15 (kn_cons lb_9 (kn_nil)))))))))) rc_66 nc_66 (by decide +kernel)

def g_67 : Nat := 0x1171557131777ff
def ep_67 : Nat := 0x120062a800001440000064e80016004200040088010604020206000001121002131222000114155410144400
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_63, s_63, 9, g_63), (m_57, s_57, 9, g_57), (m_65, s_65, 8, g_65), (m_36, s_36, 5, g_36), (m_35, s_35, 5, g_35), (m_58, s_58, 9, g_58), (m_64, s_64, 8, g_64), (m_7, s_7, 4, g_7), (m_27, s_27, 7, g_27), (m_32, s_32, 5, g_32), (m_14, s_14, 4, g_14), (m_19, s_19, 7, g_19), (m_9, s_9, 4, g_9), (m_60, s_60, 8, g_60), (m_42, s_42, 5, g_42), (m_62, s_62, 8, g_62), (m_59, s_59, 7, g_59), (m_20, s_20, 6, g_20), (m_61, s_61, 7, g_61), (m_8, s_8, 4, g_8), (m_66, s_66, 8, g_66), (m_13, s_13, 4, g_13), (m_1, s_1, 4, g_1), (m_53, s_53, 4, g_53), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6), (m_37, s_37, 7, g_37), (m_10, s_10, 4, g_10), (m_5, s_5, 4, g_5), (m_52, s_52, 5, g_52), (m_17, s_17, 7, g_17), (m_46, s_46, 4, g_46), (m_41, s_41, 5, g_41), (m_50, s_50, 5, g_50), (m_39, s_39, 4, g_39), (m_33, s_33, 5, g_33), (m_56, s_56, 5, g_56), (m_0, s_0, 4, g_0), (m_28, s_28, 5, g_28), (m_22, s_22, 5, g_22), (m_21, s_21, 5, g_21)]
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8a04406183081840400a0010008003e09f00f807813c01e00f00760bb01b88acc5602b01580ac05602b01580ac056022240c2001 0xf67204cab02e5f81ace40b17e05d2782c91c14ac409a6f03ebf02358c108de0745f035b10475bc22ac610c6f07e2f83b15c1c6de0db5f065ab830d1c152dc091560309b0155bc09ac60446f01e2f80d15c056de0235f00dab804d1e7b8bf3cc5b9da2bce714e696bf33357989a7cb6d1e4a4bf222578f527c2491e0d46ef595f774adb9055dad2a6ce14f634a5ae451d62286a293b3f49b9d64acd124e6305f2802b91613c7508e250370901381607c0102e0003f 13 8191 6 63 11 2047 21 2097151
def cc_67_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9ce709c2529425088e11842017c5f07c1d2741d05d9705c152541504c9304c112170501043108402 0x819c9fb60685fdea5f7895dd562729b9816f5e5bd9b7864de19c5f6515db5656b17da45762da1835a5e9596d7e58d61567252d813d724cd42456f8d58e246f8317df45776d89c35a6e959716f5657d41574a51c8936204d87936415f87136 10 1023 4 15 11 2047 18 262143
def cc_67_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x942328c2308c1d6741d0741d065190641725c17054950541321f07018460108400c4300c00300000 0x2fc72bd182e56fb758ed36eaa5be915f9e55ec565af1a2b45aaa9369c58a493684609e9366b6a98d439d6fe358f6462d316b2a6fc297eea57b2936a16fa257e71579649e4b6874da23b588ada21d7e84d61a97f 10 1023 4 15 11 2047 18 262143
def cc_67_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x98a519425090613842107c9785c1525412348111441012d4b02c0741c0701c043100310c01204001 0x80ad0fe975ed36bdc727d8e4f9181e936bc47f776c11358a1db7c2a6f824bb028ddf8b7bc9377624ee91a17126b5c68728b0b6935b91ab7366706beded5d8d2fafa576d46ed7589a9b73326f562ded15959e343345a646aac71c98a2c3036c 10 1023 4 15 11 2047 19 524287
def cc_67_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x841f27c1e1781e0691a0681a0609715c170585334c13044898240812005314041100400100000000 0x4f4649948b391926ab14cb6f952df204de5a324aa45914ab231ca4e3949458904ab1cdca35ac4fc6e9d6df369be6122cba37942df1e4de3093c524788ad106975e093c3568848dd06dbdfcb7bd137 10 1023 4 15 11 2047 19 524287
def cc_67_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9d67090e4084df27c1f07c1f07c1a5681a0681a068155541504c9304c112441103c8f03c0d203400 0xc069f7ed1eaca7d4147a526f7b1f2d8be58170bbae16a5f2bcb85a17cae2e1708fedd1bdb13fb526f6849ec9a7d8b47b049f5e91eb91bd647cab4fb535c2a13ed3470a54fb46dc289ad62c6dc369f82d1ef936de24fba48f728deccb656960aa29f4e51e909bd0927 10 1023 4 15 11 2047 19 524287
def cc_67_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xb4ad0b06c0ac6b0ac2b09d2709c2708592f481204812048120481204811122480200441000400000 0x1bedc351ad6eb58db6c1b35a762b0c705fd704fab1bf5233e9a6ec80df4419d3423f4d6fe7ad7c959f8ab1f046fde8cfb917f6a2beb362d26b58e1be8433c605f760ae9611f21ad6834fcf68f9c93f3523e6237cb29f9451f249be3927c48f9809f6e0be59170c2ae17e9f6dcbe58970 10 1023 4 15 11 2047 19 524287
def cc_67_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xb84ec5d0381700d85b0322640b89702e0544a81502a0540a0511947280484900e21c0380510a00c418001800 0x8026f7fa67a156f9fd6b9dd679bd6395c629445a91a6f8ea678c25f83a5780a4d7f15a6486f520674785f3c857128277e1547d1547c164779567b17c769567a57e79954775707856277b6f76b677dd6b7cd637bc6f7ac677945f7896e76156753686cb70743587347c72b706c37071b5870b686ab5a3c057 11 2047 5 31 11 2047 20 1048575
def cc_67_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x883d1e0f071381a4c9642e970b1582c1449948a2502803c9c4a82d140a05028140140000 0x9157d8fc708f45a7f95a8e3658db558d4728cc588947088c708b4588a36c8967a88e728737885b648747c8536085b6c8547487b6f86b6b8636784b638be7b8ae7389c7288462844608356f82d6b8256781d638136e 9 511 3 7 11 2047 20 1048575
def cc_67_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02719c243902408c5e5781c2701c070193641905c970584bb2c0b01d07018460180240802008002 0x9f23f9ec709e27d8224d9cc509a470954689d4589c25581a4d9b355982379926d8e25d97a359867997b6696a4d9ad699a56199b5f98b578d25f89a57972374985f3e85796037138279556294b6e9226f8f26793c709356592c689245a8015a90b5b90353 10 1023 4 15 11 2047 20 1048575
def cc_67_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x98660946509064088a207cdf0749d06c9b068591641816018060180511404c47c1c07010c4010004 0xaf954ae97cad954ac964a5956a8256ab97ca5156a4964aa954a717ea996ca8d70a8267a7247a6562a5a6fa5267a4a4da3b62b056faf56bae567ad563ac36fab367aa35fa9357a7a56a696ea4156a3136a2468a1a658324d9ac70a0c58a025582a4d 10 1023 4 15 11 2047 20 1048575
def cc_67_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0e80a028094e419024090240901f54b52040900400d3340c1300b12c0b02c0b02c08305c1000400 0xbfd70a813aba85cbec6ebe36fbdb67ba06cbc25fbba57bb15fba957ba127c4d62c2b6fc1367c026fbf267bd25dbca37a793a6506f53867b985c2703714027b8964b3136b7d7cb717cb2936b6164b517cb346fb2c67b2362b846fb6c67b5b6fb4b67b4347b396eb1936b0964 10 1023 4 15 11 2047 20 1048575
def cc_67_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8ee08ee3084a107c9f0749d06c9b06c1b06c1b060d08401003c4c3300c02c4741c0700d03004801 0xd0d62d036fcfb67d646ed4b6fd3367d226fd1267cf245cea376586f550672883715827cd964c8936cc97cc813680246cb9647fa46ca97cc8c6fc8467c7b62cd46fcc467cb36fca367c9b477f246c916ec7136c5a5dc6247c504715027c3d60c4568c3265be25dbc05cc2570c1a7dbda5dbb85cc0d68bb05ca893a 10 1023 4 15 11 2047 20 1048575
def cc_67_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x8421078de0781c2701c0701c0701c05d5705c17050c9b20480200531405008c20044100040000000 0xdf47fd9964de954dde70dd16cdbc62db36fdab4dda26fd9a4dd8d63d846fd7c5fe3d6fe3563e2c6fe1c5fe0457dfb6fde35fdcb57dc347d9156d713616827d5c64d5265d0245d447cd3a7dcfa45d2c64d1c7c 10 1023 4 15 11 2047 20 1048575
def cc_67_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xa445e211088425e6f071381c0d26832582c0602c960a949a40be58250cc601b0c0601401 0xf4c5ff3457f235ff0b57f0347ef956ef136ed470edc7ceaa7deca45ebd70ea27deab4fea347e947ce636de7b4fe7347e6680e8571e6d70e5b5fee46dec34feb347e9a6de8a4fe5247e4a37db964d8936df35fdb156d8136da964e2154d7936e1670e096cda156 9 511 3 7 11 2047 20 1048575
def cc_67_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x90e40902228822088220881d5741c16c5b06c1a1681555406f18051140500c830084200800200000 0x3ff5a1f64ca1a0277f632bf9155fa8befcc537e1afbeed3df668efa4647c1b6be19e1f2ad2f8d687bdafbdc5482f04b05c6f82631c0f156036df0034f7f9a3bf69bdf54aaf9a4f7b523bd88dc9409e3f0471501b85c09dea2a8f467079cb63ca551e3ce0f116c 10 1023 4 15 11 2047 21 2097151
def cc_67_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c08c08638608418408408028007657607414964804804804802522402022001a31a0105100100100084080080004000 0x21f4ad0f156874aa4379e219d010c18c873394351fe178eef727e858bf4299ca3cadd1d56b8deb1c6b58a326df14367899afbda5bde12d6e51676e4b1c4057e152a6a913b41c9b99a1bcba0cf0985f1741b86e0941903e01817846b7c215ae0facf075637b0b7bc05adc92cedc163674afb2656d792aeb41533303797219c970be408570600f80405dfa4cb06255822b23f29960a48b04452819afbfa97c5806e1b02781a32c0b155f84cb0225580a323ee9960148a1a827 12 4095 5 31 11 2047 21 2097151
def cc_67_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xf0aeeb46d0a52909ca25881e4709c061162545414c52148111404c42108014c50140411003100c00 0x240af91fc7c90e37482dbe3e6cef996f790b5ba259dbc2c6aa13b4609b99c1bcbc0ce3083706c0f80805e3badd1dc6c89db6c4a5b51726f0f57087cb8472d1e1c2c31c1474549bc281b5e32d2dd9618d82383407e242db0d9618d2b4c675a2232bf0d153888b6c325862f2b1161448bd2e4565022c29915a548c0a7c5c52e2d28f151438c6b8c535c2212bf0b95389f3d3de5fdcb2ef1267888b4044b9ea236ff10b77 10 1023 4 15 11 2047 21 2097151
def cc_67_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x7e67e07c160e6005e15e05e05e05645605605415405215205015005005001da1a11a0181180161049040040002000000 0x130a477a0b4b845865f08e200270780fcbb5ba5eac52726f91533cb8975fe2def316b758b3b8058cda24e6786f3043387c09c1d03e0301795ab24ad149fc2be931371a01bca71f6518c927d6896a37cb318e3c8bb2c45b95e2bcab156546df29357941a7c9cd1dfb2dedf963934adc9855da429ecb14b600a3ad650d582769193792c2b93613c8508e328370700f80a05d2226f2447c91ab84931b64769f22b47688a7b2852d7e28eb49435589da3a4de428c8df173 12 4095 5 31 11 2047 21 2097151
def cc_67_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xf20f20f20cd3ca1be6bc1ba1ac7ac0a6388f8808428407e37e07a27a07a07054944424022ca26326020302f020020001 0x138b6fa05abcb49be3c4bb402579fd2ac228de0b2dee39639f8adcfa55d60276a11373a493cf815c7306e2402708c0f81405d4026f3d2458411babc4ed3f26e7d92b39c939cc49d3c26f3ac6d9e1b64ee9b60f46eae13b4ec9b9c849e706df0516f4e09bceb1ba6f6df2ca6f9d122c1c8de092dee31635689da6e4dcf9256711271c41b88c09c2203e048179b132ce49566eac935a659c122cdd14a052bf3646f9ae31c085bdaa29ec31479c637cdf18e6d8ab2a26f9a92ac8293e3248f0196f714b1b5253d9a296c29475c0a19ee4ace024e4e84f21c2388809c2103e0401790126ade505a729ec19479a236cce9b63e49f14247698a7b3052d8228eb69433d4959bc49cf4256218270800fcc918a012deec967996374a09be474cf31a45800b7bd25add82cee19633c8959b849cd00de618671041383e07c0702f3025d 12 4095 5 31 11 2047 21 2097151
def cc_67_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc3 0x9cb6f8316f50d37 4 15 2 3 10 1023 20 1048575
def cur_67 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_67_20 (Nat.sub p 640)) (cc_67_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_67_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (Bool.rec (cc_67_17 (Nat.sub p 544)) (cc_67_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_67_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (cc_67_14 (Nat.sub p 448)) (cc_67_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_67_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (cc_67_11 (Nat.sub p 352)) (cc_67_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_67_9 (Nat.sub p 288)) (cc_67_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_67_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_67_6 (Nat.sub p 192)) (cc_67_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_67_4 (Nat.sub p 128)) (cc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_67_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_67_1 (Nat.sub p 32)) (cc_67_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def hc_67_0 : Nat → Nat := unpackHintV5 0x7f24a73cfaa61d5c484e18a566eb484350096995b494c5e93c604caa2e786b9667354adc95c5348e7282061135a2d89a282a49e4cc235a6610e631c82c11c3a61c01982eb8af9720498b901dc5c00bb6cb0445658156b30045d9600667200000cc000000 0x313030313030b030307130b030b0703034bdaaa0380e1384e0380ea038eea0b81e64b403c0003c26e201c4c4c5c1c4c4c4c4c4c4c2c2c2c1c2c1c2c1c4c2c1c4c2c2c2c2c2e6c9d1744cbd41c4d44d1342d076aaaaaaaaa9a627a85ea138eeaa078ceaa13a84ea0ba81e96a4b500000f03c00000f0000000f009b202150317170303132f1f2f13031f030b1703031f0b0b271f030b270b270b566d17545d5555aaaaaaaaaa5580ea17a80e3baa8be3baa8aeaa82ea27a5555000000000f0000004026c8081317131b1f4b171717171b1f547c2c5c2c6c2c4c2c6c7c2c2c7c7c2c2d5559b44d513556aaaaaaaaa956a85ea1ba87ea1b8aeaa1f8eeaa0ba87e9555400003c000f03c00000001009b20200c4c0c0c4d5030b0703555aaa0380e1384e0380ea038eea0b89e5500f000426e204c4c4c5c4c4c4c4c4c4c4d51f0b170b131f0b0b13130b0b130b130b5544d44d559b55aaaaaaaaaa55aa17a84e3baa84e37aa84ea13a82ea33a555500000f03c00000f000000103c026c8081f17171f071f171707171f5f071f1f1307131f1f070b070b070b070b5555550b50b5566eaaaaaaaaa95627a85ea1fa87ea1f8eeaa078ceaa0ba81e9555400003c0000000001009b202284c6c4c6c0c5c5c0c0c7c0c7c6c6cec7d0c0c6c0d47c2c7c2c7c2c7c2d5566c4d136822a800000280c5c4c0c0c4c0cec4d0c4c4c4c0c4c0c4c4c4c4d47c2c7c2c7c2c4c2d544d13566e822a80003c0f00002a0317170303373b2b3b37032b030b170303330b0b2733030b270b270b0345d033b53b3f550b49d2aa00a0aaaa690000000000000000030303031380c0c0c0c5eaa80c0c0c0c7c2c4c2c0c0c0c2c0c1c0c0c0d0347d1340c0d40cbd42d1f6aa8aaaaaa9a40000000000000140c5c5c0c0c4c0cbc7c7cbc4c4c0c7c0c4c6c4c6e87c2c7c2c9c2c9c2d66c5d17556aa028003c03000f26c04cdc5c5c4c5c7c4c5c4c7ea1f0b170b1f330b0b13330b0b1f0b130b45d1f3f5133751f44d0b47daaa000a8aaa690003c0f00000f26c00000000131717139b131317171f0b1f0b031717031b13131b031f031f3b4b1f2f2f031f030b1f1f0b551f4bd9aa1f8ee409000000b0b131f131f0b0b9b170b170b1f0b03171703031f031f3b4b1f2f2f031f031f1f1f1f0b07070b559aa40900000034b2f0303c5c5c7c2c2c7c2c2c2e6c4c2c4c2c9c5c5c9c6c4c4c6c1c7c1c7ced2c7cbcbc1c7c1c2c1c7c1c1c2c2c2d547d2f66a9024000000c0c0c0c0c0c0c0c9c2c9c2d55555540c0c0c0c6c0c0c0c4c0c0c0c2c0c0c0c1c0c0d5556aaaaa9456954000000000000300012c5c5c2c5c2c2d2c2cbcec5c5c5c5cecbcacecdcbcdcecac2c2cecccbccc2c2d5555559aaaaaa500058500000000000000017170b170b0b0b45d50b5aaaaaa69aa17a8aeaa82ea33a5a9400003c0000003c026c8080303030303139b03030303030313030303030303030b03070303130b130b0340d03035032f51344d0b47d03030303030303030303030f030303230303030f030303230303031303030313030303130303030b50313030350380e0303a0303a0380e0380e60340000000000000208009b030303030303139b030303031703030303031b0b130b0303030b030703030340d1b44d03035032f50b47d03030303030303030303031b0303031b0303030f030303230303030f030303230303031f0303030b50323030350380e0380e030380e80c0c0cee80e03980d0000000000303c00000820026c0c0c0c0c0c0c0c0c0c0c6c0c4c0c0c0c0c1e6c0c0c0c0c0c0c1c1c1c1c1c1c2c0d0340c0d40cbd47d1f41d0740c0c0c0c0c0c0c0c0c0c0c3c0c0c0c8c0c0c0c3c0c0c0c8c0c0c0c7c0c0c0c7c0c0c0c1c0c0c0c1d40c8c0c0d40e0380c0e80c0e80e0380e03980d00000000000000820026c4c5c4c6c1c0c1c1c1c5c1c0c1c2c1c1c1c1c1c1c2c1c2c1e6c1c1c1c1c1c1c1c9d1746d1341c1d41cbd41d0741c1c1c5c1c1c1c8c1c1c1c6c1c1c1c6c1c1c0c3c1c1c1c8c1c1c0c3c1c1c1c8c1c1c1c1c1c1c1c1d41c8c1c1d41e0781e0781c0e81c0e81e07981d00000000000000820026c1c0c1c5c1c1c1c0c4c4c4c4c1c1c2c1c1c1c1c1c1c1c1c1c1c1c1c2c1e6c9d1741cbd41c1d44d1341d0741c1c1c4c1c1c1c4c1c1c0c3c1c1c1c8c1c1c0c3c1c1c1c8c1c1c1c4c1c1c1c4c1c1c1c1c1c1c1c1d41c4c1c1d41e0781c0e81c0e81e0781e07981d00000000000000820026d5030303030303031b03130303030303030303030b03070303270b270b566d03540d555503030303030303030303030f030303230303030f030303230303032303030323030303230303030b55550380e0303a0303a0380e0380e5500000000000000820026c4c5c4c6c6c0c5c5c5c5c6c0d51f0b170b1b0b130b1b070b0b1b070b0b55566d13544d550f0f0f170f0f0f230f0f0f1b0f0f0f1b0f0f030f0f1b0f230f0f030f0f1b0f230b0b0f1f0f0f0b0b55551b85e1384e1b03a1b03a0b86e5500000000000000820026c4c0c4c5c4c4c4c0c4c4c4c4d51f0b170b13070b0b13070b0b130b130b5544d44d559b550f0f0f130f0f0f130f0f030f0f130f230f0f030f0f130f230f0f0f130f0f0f130b0b0f130f0f0b0b55551384e1303a1303a1384e0b84e55000000000000000820026c7c5c5c7c1c0c1c5c1c1c1c0c1c1c1c4c1c1c1c6c1c1c1c1c1c1c1c1d5555541d41d559b07070717070707230707071f0707071f0707030f070707230707030f07070723070707070707070755550781e0781e0703a0703a0781e5500000000000000820026c5c5c2c5c2c2c2d17542d43c3c3c5c3c3c3c8c3c3c3c8c3c3c3c8c2c2c3c8c3c3c2c2d43c8c3c3d48e1788e2382e23988d0000000000820026c2c2c2c2d542d42c2d4002c100 25 33554431 10 1023
def hc_67_1 : Nat → Nat := unpackHintV5 0xe8bb80e32964dd9964d58a04cf09a0c6fa04bf29f4b65236b0218cade090abc886aae838aa4828a339c49d79709821568ad3548451a07d01d46f636867c1e85fe9f6525b644b19d043b9d835cb7c2e79d423faa0199a980f4a940a314600028c 0x4c7c5c5c4c5c7c4c5c4c7c2c2c2c2c2c2c2c2c7c2c2c7c2c2c2c2c2e6c3c3c3c5c3c3c3c9c3c3c3c3c3c1c3ccc3c1c3c3c3c7c3c3c3c3c4c3c3c3c7c2c2c2c1c2c1c2c2d555555544d55004c5c4c4cec4e131f1384c4c4c4c2c2c2c2c3c1c3e0f070f954003c00000000104009b03c000c0c0c0c0c0c0c0c7c2c7c2d5540c0c0c0c0c7c0c0c0c7c0c4c2c0c7c0d000c0c0e0380c0c0c0c00c9b0001100c0c0c0c0c0c0c0c7c2c7c2d5540c0c7c0c6c7c0c0c0c0c0c0c2c0c7c0d000e0380c0c0c0c0c0c00c9b0001100c5c5c0c0c2c5c0c9c2c9c2d55155540c3c3cac0cdcdc0cac2c2c0ccc9ccc0c2d40000c0c0c0c0c8c0c8c0c8c0c2d540cec0e033b038000f26c000000000440004c4c4c5c2c5c2c7c2c7c2d55555543c4c5c5c5c4c7c7c7c2c4c7c2d005c4c5c4c7c4c7c4c2c4c7c2d544c4c4c4c00000000000000c0c0c0c0c0c0c4c0c0c0c0c5c0c3c0c0c0c0c0c0c0c0c0c2c0c1c0c0c7c2c4c2d55555515540c0c0c0c0c0c0e03030380c0c0c0c0c0c0c0d54000000000000004cdc5c4c7c7c2c5c2c7c2c4c2d55455547c4c5c5c5c4cdc3c3c3c2c2c4ccc7ccc2c2d40004c5c4c4c4c4c4c2c4c7c2d544cdc4e133b1380000000000000004c5c4cfc4c5c4c7d51f0b170b1f0b130b1f0b130b0f0f0f0f0f0f00003c3c3c3c0f2b0f2b0b0f0f0b13171313131313131313130b131f0b0f0f0f0f000f00f0009b0000100f001784e131313171f0b130b0f0f0f130f130f0f0f130f1b03170f030f130f130b07070b5544c04e1384c4c0e038000f4409b83b1f431f9b070f0707570f074fe6c1e03e6c1343133b9b070f070f0707579b0780f9b26c1d0d6c1c2c1e6d8c1c1d0c5c5c5c5c5c2c5c2c2c2d5555543e0f0f0f0fa431b43134313431b0b0b430743070b0b500021788e2382e239545c0e83c0e80000000000000284c5c4c4c4c4c7c2c7c2d5540c4c5c0c0c4c0c4c4c4cec4c7c0c4c0c3c3c2c1c1c2d004e9b1785c4c0e03800000284c4c4c4c4c4c4c4d47c2c7c2c3c3c3c3c3c003c3c4c3c6c4e9b1785c4c4c4c3c3c0f000f03c0f026d200a85c5c5c5cececec7cecec7c5c2c5c2cec7c2c2cec7c2c2c2c2c3c0c3c5c3c3c3c0c3c0c3c3c3cec3c3c3c3c3c3c0c3cec3c3c3c3c3c3c6c2c2c3c1c3c1c2c2d55555555550217a6c5c5e85c5c5c8e2382e2383c3c0cee83c0e0fa55000f00000f03c00000410026c8000171313131384e130b1f0b03170f03030f03130f570f0f0f030f030f130f130b07070b5544c04c4c4e1380e0380f000f03c4409b8131313131f0b170b130b130b55555513031313131713030f83c3c3c3e82c2c4c1c4c1c2c2d40004e13884e0b84e551303a0f03a000000000000001317131f13171713171f1fa87c2c5c2c7c2c4c2c7c7c2c2c4c7c2c2c3c0c3c5c3c3c3c0c3c3c3c4c3c3c3c6c3c0c3c3c3c4c3c3c3c3c3c3c0c3cac2c2c3c1c3c1c2c2d55544d55544d3f555008e17a1fa6c4c7e84c7c8c2e1f83c0e83c0e954003c0000003c0f000104009b2001313131317a170b0b1f0b1f0b03170f170f030f030f130f1b030f03730f570f0f0f030f030b07070b544d55cd2f408c5c7e1780e0380f000f03c4409b81317131f1f0b170b1f0b130b5555135555c0c5c5c5c5d5c0c3c3e83e0f0f0b0b1f071f070b0b50002385e13882e1f9547c0e83c0e8003c00001001000008004cec5c5c4c5cec4c5c4c7ea1f0b170b1f1f0b0b131f0b0b1f0b130b0f030f170f0f0f030f0f0f0f0f030f370f030f0f0f3b0f0f0f0f130f0f0f1b0b0b0f070f070b0b555555551355402385e131f1f131fa87e9b0b87c7c7e0f03a0f03a55000f00f03c00000000410026c8005c7c2c2c5c7c7c4c4c7c2e82c0c5c3c5c3c0c3c0c3c7c3c6c2c1c1c2c0c3c0dcc3d5c3c3c3c0c3c0d1f55023170b82e0380e03c003c0f11026e07c5c5c7c2c2c2c2c2c2c2c2d5555547c0c5c5c5c5c7c0c7c6c7c4c7c4c7c6c2c2e82e0b0b50002385e1f87e0b89542c0e82c0e80000000000000007c5c5c7c7c7c5c5c5c5c7c7c7c7c7c7c7c7c7c2c2c2c2c2c2c2c2ea0f030f170f0f0f030f0f0f1f0f0f0f1b0f0f0f0f0f030f330f030f0f0f1f0f0b0b0b070b070b0b55551f51f4fd55555402385e1f87c7c7e0b0b0b0b0ba82e9b0f03a0f03a55000f0000f03c0000000410026c8005c5c2c5c2c2c2c3c3c3c5c3c3c3c3c3c3c3c3c3cac2c2c3ccc3c3c2c2d555555005c5c8c8c8c2c8c2c3d1c3e0f0f0f954003c0000104009b03c000c5c4c4c5c4e6c4c4c0c4c4c4c4c0c2c5c0c0c4c2c2c4c7c0c2c4c2c4c2c0d1740c4d44cbd44d1342d1f6aaaaaaaaa9a603a85ea038deaa138eeaa13a84ea0ba89e96a4b500000000f03c00f0000000f009b20200c4c5c5c4c5c4e6c0c4c4c5c5c5c0c2c5c0c6c2c4c2c0c7c2c2c7c7c0c2c0d1746d1340c7d47cbd42d1f6aaaaaaa1f8eeaa9a603a85ea1ba87ea038aeaa1f8eeaa0ba87e96a500000f00000000000f009b20200c2c2c0c5c5c0c0c4c7c7c7c4c0c7c2c2c2e6c1c5c0c2c1c5c2c1c7c2c1c2c2c0d1740c7d47cbd47d1f42d076aaaaaaaaa9a603a85ea038ceaa1f8eeaa1fa87ea0ba81e96a5000000000f0000000f009b20200c0c5c0c0c2c4c0c0c1c0c2c1c0c0d2f6a80e0380e03a80e3ba86e1f82e07990000303c0f00f09b881317131b1f07171717071f0b0b0b071f0b070b0b0b0b0b9b07130b0b07130b2745d1b44d071f51f2f50b41daaaaaaaaaa6989ea17a86ea1fa81e2baa87e3baa82ea07a5a9400003c00000000003c026c808 24 16777215 10 1023
def hc_67_2 : Nat → Nat := unpackHintV5 0x92b8ec45bee7a21732109f9b08128f53eba769e80374ebfa0272f8c137f4621a2d734c9620261d0b82d70de159b474a639a84bd5d2245465914a3807d7b363ad4fa1b408a8bbe788559a16232de80f808585cc7d02799b20f8113041ce901153e400022a 0x1317131f0b0b0b0b0b0b0b0b2f03171717172f030f075550b0b00055515555554f131713131313130b0b0b0b2f03138bc0c4e550000000000000001327171713172f271317131f543c3c3c5c3c3c3c3c3c1c3c3c4c3cdc3c3c1c3c3cbc3c3c3c3c4c3c3c3cac2c2c2c2c2cbc1ccc2c2c2c1c2c2c2c2c2c2c2c2c05547d47d559b5555554f13171313071384c1c4e131313130f470f83c3c3e0b0b0b0b330b55000f00f03c0000000b00b0026c000005c7c5c5e6c5c7c5c5c1c2c1c2c0c5c5c0c0c9c0c9cbcbc9cfdac0c9c0c6c4c4c6d005d5542c3d0781e0380e03c003c0f00007c5c5c5e6c5c7c5c5c1c2c2c2c7c1ccc2c0c5c5c0c6c4c4c6c0c7c0c7cbcbc7cfddc0c7c0d005d5542c3d0781e0380e03c003c0f00000c0c0c0c0c0c0c0c0c0c6c0c4c0c0c0c0c0c0d540c1d42c2c2c2d555555554540c0c0c0c0c0c0e03030380c0c0c0c0c0c0c0d54000c00000c00000000017170b0b0b0b0b0b0b0b3f171717172f3f3f2b2f373f372f2b50004fd5554542d43d17172323230b0b0b0b2f3b238fcec8e55000f000000000000005e1381c1c4c5c1c1c1c4c1c4c1c1c1c4c1c6c0c5c1c0c1c4c1c4c1c1c1c1c1c2c1c2c0bd1356d0741e0781c1c0e0381c1c000f0701c09b1717171707070707070707070781c3c1c1e81c1c1c4c1c1c1c6c1c0c0005d1753d4f41d0741cbd41c1d481e0781e070781c1e0703a0703a60740000000000000284c5c1c4c4c1c1c1c1c1c1c1c0c4c5c0c0c1c0c1c4c4c1c4c7c0c1c0c1c1c1c0074bd134fd13a6c1e07070380e000000a071f5b070707070703171703030703072f2f073f430307031b13131b4017555070745e9b0781c1c0e0380f000703c0000a85c5c5c5c1c1c1c7c1c1c1c1c0c1c5c1c1c1c0c1c0c1c3c1c1c1c1c1c1c3c1c0c1cec1c1c1c1c1c1c6c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c01745d07075072f54f53d075070750741d85e9b0707a0707070781e0707033ba070381e81c1e0707981d000f00000703c000070070026c000004c4c4c4c1c1c1c1c1c1c1c1c1c0c1c4c1c1c1c0c1e070f0707a07030002745d1344d0741d07135070750781e20781c1e070781c0e81c0e981d0000000000000027071707a07070707031717031b13131b030703072f13073f130307034027555070747e9b0781c1c0e0380f000001317131f0727070707170707a81c0c1c5c1c1c1c0c1c1c1c4c1c1c1c6c1c0c1c3c1c1c1c1c1c1c3c1c0c1cac1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c02745d1f44d07075072f5075070750741d0781e87e9b0707a0707070703a0703a070781c1e6074003c00000001c01c009b00001317131f070707070707070707030717070707030707a0781c3c1c0c0009d1747d1341d0741cbd41c1d41e0781e2070781c1c1c1cce0703a0703a6074003c0001c00070000000001c5c1c9e81c1c1c1c0c5c5c0c1cfddc0c1c0c0c1c0c1cbcbc6c4c4c6d009d074bd5541c1d07070787e9b07070380e03c1c0f0000001c1c1c5c1c1c1c9c4c5c4c7ea07030717070707030707070f070307370703070f070707070707130707071b07070707070707070707070707070707009d1741cbd41c1d47d1341d41c1d41d0741e0781c1c1c1c1ea1fa6c1c0e81c0e81c1e0707070733981d000f00703c000000070070026c00000c5c1c0c1c4c1c4c1c4c1c6c15549c4c5c4c1c1c1c4c6c1c1c1c1c1c1c1c4c4c1c1c1c1d541c1c0e0381c1d940f0701c09b002717172707070707070707075555550703071707070703070707130707071b070300055550781e0781e070781c1e515a55000000000000002717172707030717070707030707074b0707071b0707070707070707001c1c1c5c1c1c1c9c1c1c1c1c1c1c7c1c1c0cec1c1c1c3c1c1c0c3c1c1c1c1c1c1c1c1c1c1c1d555555555590781e0781e0703a0703a070781c1e555959b000f000070070026c000000005c5c3c3c3c5c3c3c3c3c3c3c3c3c3cac2c2c2c2c2c2c2c2c045d50f50f0f50b42d17172323230f470f83c3c3e0b0b0b0b330b48d000f0000b00b0026c0000171317170b170b1f0b130b5555135543c0c3c3c3c3c5c0c3c3c4c4c3c3c3c3c2c2c7c1c7c1c2c2d40005c4c5c4c4c4c4c4c2c4c7c2d555c0c4e57031380000000000000f0017171f1717179b1317171f131717170b170b131f0b0b1f1f0b0b1f0b130b0f030f170f0f0f030f030f0f0f6b0f0f0f0f0f0f030f370f0f0f130f370f0f0f2b0f2b0b0b0f270f0f0b0b5555555513554017131713133b1384cec4e131313130b131f0b0f030f83c0c3e55000f00000f03c00000410026c0f0017171705c2c5c2c7c2c7c2d5555543c0c3c3c3c3c5c0c3c3c3c3c3c3c5c5c2c2c7c1c7c1c2c2d40005c5c5c5c7c7c7c7c2c7c7c2d547c0c7e1f031f8000000000000005c7c5c5c5c5c5e6c5c5c7c5c5c5c5c2c5c2c7c2c7c2c7c7c2c2c7c7c2c2c3c0c3c5c3c3c3c0c3c3c3c7c3c3c3c3c6c3cac3c0c3c3c3c7c3c3c3c3c3c3c0c3cac2c2c3c7c3c3c2c2d55547d55547d3f555005c5c5c5c7c7c7c7c7c7c7e1f3b1f82c7c7c2c3c0c3e0f030f954003c0000003c0f000104009b03c005c5c5c5c0b0b0b0b0b0b0b5555550b030b0b0f0f0b031f1b1f131f131f1b0b0b0b070b070b0b5000171717171f1f1f1f0b0b0b0b551f031f87c0c7e000000000000000b0b0b171717171f1f1f1f1f1f1f1f0b0b0b9b0b170b0b0b170b0b1f0b0b0b0b0f030f170f0f0f030f030f0f0f1f0f0f0f0f0f0f030f330f0f0f1f0f0f0f1f0b0b0b070f330b070b0b0b0b5555547d3f5551f5540171717171f1f1f87cec7e1f1f1f1f0b0b0b0b0f030f83c0c3e55000f00000f03c00000410026c0f00171f171f0b0b130b0b0b0b0b0b0b03170f03030f035b0f570f0f0f030f030f1f0f1b0b07070b5547c0ee3b80e0380f000f03c4409b0f07c5c5c7c2c7c2c2c2c2c0b0b0b5555551f03171717171f030b0b0b0b0f0f0b0b0b0b0b070b070b0b5000571717231f1f1f1f0b0b0b0b551f031f87c0c7e000000000000001f17171f1f171717171f1f0b0b0b0b1f0b0b0b0b0b0b0b9b0b1f0b0b0b1f0b0f0f0f170f0f0f270f0f0f1f0f0f0f1b0f070f0f0f1f0f0f0f0f0f0f070f2b0b0b0b070b070b0b55551f55551f4fd55401717231f1f1f1f1f1f1f87cec7e0b0b0b0b0f070f83c1c3e55000f000000000410026c0f0013131313170b0b0b0b0b1f0b0b0b0b0b03170f170f030f030f130f1f030f03730f570f0f0f030f030b07070b44d5404c4cee3b80e0380f000f03c4409b0f04c5c4c7c2c2c2c2c2c2c0b5555135547c0c5c5c5c5c7c0c3c3c2c2c2c2c2c2c2c2c2c1c2c1c2c2d40015c4c5c4c4c4c4c4c2c2c2c2d547c0c4e1f031380000000000000f00 25 33554431 10 1023
def hc_67_3 : Nat → Nat := unpackHintV5 0xed51be73306f3788421baa034d6b8d36488dab1bc1118011bab3998e55d87ea8b247525f3f489d1253cd1031ce6304da619a6c701833905517a6444ae81d64e292322e88590042e07181d43328b31248e9890c0303cd17216d8f204a0d981de0e40001de 0xa83c0c3c5c3c3c3c0c3c0c3c3c3cec3c3c3c3c3c3c0c3cec4c5c4c5c4c4c6c7c4c4c6c7c0170b170b1b1f0b0b3b1f0b0b0f070b0b0f070b0b1b0b130b1745d1b2f53b2f50f50f0f51b44d0b53d85e9b1717a1717170f0f033ba0f0383e84e1382e1b986d00000003c03c009b000000003170f170f030f03171b00b0b070b070b171b0f538b0f03030f0f0f0f03031b13131b0ba0b43d2f4bd1b170380e0b82e0f03c09b000f03c1317131b0b0b0b0b0b0b0b0b1f03171717171f031b030000b0ba0b82c2d3d1746d1342d0b47cbd47c7d46e1784e1f131f82e20b03a0b03a61b4000f00000000000002f034b032f40f03171703401f17171f13131f1f03033f1f4b1f03032f1f2f070b0b0b1f07070ba3f5130f47d2f5547c7c0e0382c2c2e0ba6c0000003c0c3c5c3c3c3c0c4c5c4c6c01b1f171717171f0f0f03330f0f0f0f0f0f030f0f0f1f1b1f131313131b1f0b0b0b0b0b070b0b0b070b0b0b0b0b0ba93d1743d43c3d46d1347cbd46c7d42d0b46e1783c0e83c0e84e1f131f82c2c2c2c2ea0ba6d86d0003c03c009b0000000000003670f039b070b1b4b1b1f030f038b9b9b1317131b8b0b170b1b0b130b5555552f03171717172f031b030000b0b2f072f070b0b55551b85e1384e0b86e515a550003c0000000000003c0c3c5c3c3c3c0c4c5c4c6c00b170b0f070b0b0f070b0b1b0b130b1b2f171717172f4b0f0f033b0f0f0f0f0f0f030f0f0f2f1b1f131313131b1f0b0b2f1f1b1f0b0b5555555555646e1783c0e83c0e84e1382e1b9556566c000f00f0026c00000000003c3c3c5c3c3c3cdc5c5cac00b170b0f330b0b0f0f0b0b2b0b370b45d0f50f0f52b4dd0b51717230f470f83c3c3e2b2337230b230b48d0003c03c009b00000005c4c5c2c2c2c2c2c2c2c2c3c0c3c3c3c1c5c0c3c1c4c4c3c3c3c3c2c0c0005d1747d1342d0b49cbd49c9d45c4c5c4c4c4c4c4c2c2c2c2c9c0c4e270313913274000000000000005c5c7c5c5c5e6c4c5c5c7c4c5c5c3c0c3c5c3c3c3c0c3c0c1c3c3c9c3c3c3c1c3c3c0c3cdc3c3c3c4c3cdc3c3c3cac3cac2c2c2c2c2c1c2c2c2c1c2c2c2c2c2c2c01745d13275272f51f44d0f50f0f50b42d1713171313071384c1c4e131313130f030f83c0c3e0b0b0b0b270b44c9d000f00000f03c0000b00b0026c00005c5c5c0b0b0b0b0b0b0b0b0f030f0f0f0717030f0f0f0f0f0717170b030001745d1f47d0b42d1f2f51f1f5171717171f1f1f1f0b0b0b0b1f0b1f031f87c0c7e48c9d00000000000000171f17171717179b17171f1717170f030f170f0f0f030f0f0f1f0f0f0f0f1b0f2b0f03070f0f1f0f0f0f070f0f030f2b0b0b0b0b0b0b0b0b0b070b0b0b0b0b1f07330b0b005d1747d1f47c7d47cbd43d43c3d42d0b45c5c5c5c7c7c7c7c7c1c7e1f071f83c0c3e0f030f82c2c2c2c7c2d23274003c0000003c0f002c02c009b00000303030303030303030b070b070b03030303031f0303031f03130b007d2f40d7f40c0c0e0380c0c0c0c00c9b00000c0b00c0c0c0c0c0c0c0c0c2c9c1c9c2c1c2c2c2c0c0c7c0c6c7c0c0c0c0c0c0c2c02f4bd0350380e03030303030300326c0000302c0b1b544c7cbd030b03547d4cbc7c2c1c1c2c0c0dfc0c0c2c0540d4bc2d0340d03550380e0303030340c00c9b00000302c03171703030b0b0b0b02c2c2c2c0c3c3cac0cdcdc0cac2c2c0000d17542d0b40cfd4fd40c0c0c0c0c8c0c8c0c2c0c2c0cec0e033b03923034000f26c00000000b02c000004c4c4c2c2c2c2c2c1c2c2c1c2c3c4c5c5c5c4c7c7c7c2c01745d1f47d0b42d1347d171317131f131f130b0b0b0b1313131344c9d000000000000003030303030303130303030317030f0303030303030303030b030703030b02c2c0d0340c0d40cbd47d1342d0b40c0c0c0c0c0c0e03030380c0c0c0c0c0c0c0d03034000000000000004cdc5c4c7c2c2c2c2c2c2c0b0b0b1f1317171713370f0f0f0b0b00045d1f44d0b42d133751f3f5131713131313130b0b0b0b13371384cec4e44d2d00000000000000017544c4c4c5c3c1c1c4c3c4c3c1c1c4c3e4c0c5c3c0c3c4c3c4c1c2c1c2c1555541e0780e0382c4c000f0b02c09b171717170b0b0b0b0b0b0b0b550f075271b27132713271b0b03000155555555517171717272327230b0b0b0b27032389c0c8e550000000000000051717131f131f070b070b0b0b03171703031f03271313271f1f0313030f0f0b0166c5d175541e0780e038000015171717172727271f27271f0f030f170f0f0f030f03070f0f270f0f0f070f0f030f3f0f0f0f0f0f0f2b0b0b0b0b0b070b0b0b0b0b2707330b0b0b0b0b0b0159b45d5175550f4fd5555545c5c5c5c9c1c8e27072389c8c9c8c3c0c3e0f030f82c2c2c2c9c2d54003c00003c0f00002c02c009b00001b9b0b0317170350b0b070b070b0f0f1b13131b1b1f1b1f03031f4b1b03030b0166c7d1f5540e0386e1b803c9b00002c0b07c5c5c7c2c2c2c2c2c2c2c2c7c0c5c5c5c5c7c0d543c1d42c2c00154555555552c5c5c8c7c7c7c7c2c2c2c2c7c2c7c0c7e1f031f954000000000000007c5c5c7c7c9c5c5c5c5c7c7d50f0f0f170f0f0f0f0f0f1f0f0f0f1b0f0f070f0f1f0f0f0f070f0f1b0f2b0b0b0b0b0b0b0b0b0b070b0b0b070b0b015559b47d51f55555553c5c5c8c7c7c7c7c7c1c7e1f071f83c6c3e0f0f0f82c2c2c2c7c2d54003c00000002c02c009b0000030f130303541c2c1c2d540e038000c5c5c5c5c0cbc0d42c2cbc1c9c2c1c2c2c2c3c3cbd4c4c0c0c4cbc4cbc0c0c6c4c4c6c2c01f47d59b552f4bd0380e1b86e00f26c3c0f00000b02c0 25 33554431 11 2047
def hc_67_4 : Nat → Nat := unpackHintV5 0x89252540d2f01f7f3a8ee835e7380f0383e609b2f3c0cbe366620cf92f8c5e95fb72ca941a650b4fb28300a93583008c539c4314c51fda6c0e4669c6a220432cc911748878a874744503ce1ed8ea0c04da05123c02289820d84f00366d700b53f800016a 0xf0f0b030b0b0b031303000131313130b070b0b0b070b0b02c2c2c2c4c2c2c2c2c4c7d44c4d45d1744d1342d0b44c0c4e13031384c4c4c4c4c4c4c4c2c2c2c2d13134000000000000002c2c2c5c5c5c5c7c4c7c6c7c4c7c6c3c0c3c3c3c5c3c0c3c0c3ccc3c3c3c3c3c7c3c3c0c3c3c00b0b0b9b0b170b0b0b170b0b1f0b0b0b0b0b070b0b0b070b0b1745d1f1f51f2f51f47d0f0f50f50b42d171717171f1b1f87c6c7e1f1f1f1f0f030f83c0c3e0b0b0b0b48d8d000000026c0f003c000003c003c3d5544c0c0004c4c4c4c4c1c2c2c4c1c2c2c5c2c5c2c4c2c4c2d55545555544c0c4e13031384c4c4c4c4c4c4c4c2c4c4c2d54000000000000015171717172b132b1b2b132b1b0f030f0f0f170f030f030f3f0f0f0f0f0f2f0f0f030f0f005c2c5c2cbc7c2c2cbc7c2c2cac2cac2c3c3c2c2c3c9c2c2d59b45d5175555555545c5c5c5cbc6c8e2f1b238ac8cac8c3c0c3e0f030f82c8d3c2d5400000009b03c00f000000f0003030303030303031755503030303270b130b0303030b0307030355551555555030303030303030303030380c0c0e0303030355000000000c00000000b0b031717030313031f3f671f1313031f03131b131b400b0b9b170b170b070b070b1f0b550f47d1b86e0380e000000f04cfc5c5c4c5cfc4c5c4cad40002c5c2cfccc2c2c4ccc2c2cac2c4c2d550f52b4555131713133b1384cec4e131313130b130b55000000000000003c007c5c5c7c3c9c3c3c3c5c3c3c01f1f171717171f5f1f1b1f131f131f1b0f0f070f0f0f1f5f0f0f07330f0f0f0f0b0b0b0b0b0b0b0b0b070b0b0b070b0b55555555550b50b5566d3c5c5c8c7c7c7c7c3c1c3e0f070f87c6c7e1f1b1f82c2c2c2d540009b03c00f0000000000f000f0fa0f0f0f84c0c0004c4c4c4c4c1c2c2c4c1c2c2c5c2c5c2c4c2c4c2c4c6d44c4d45d1744d1342d4f43c0e84c0e884e1384e0b84e61340000000000000280c5c4c0c0c4c0c6c4d0c4c4c4c0c4c0c4c4c4c4d006c2c7c2c1c2c1c2d543d1344e9b1785c4c0e038003c0f000200a84c5c4c5c4c4c6c6c4c4c6c6c3c0c3c3c3c5c3c0c3c0c3cec3c3c3c3c3c6c3c3c0c3c3c0170b170b1b1b0b0b1b1f0b0b1b0b130b0f070b0b0f070b0b1745d1b1b51b2f51b44d0f0f50f50b53d85e9b1717a1717171384e0f0383e83c3c0cee82e1b986d0000003c0f0026c0f003c0000200005c6c0c3c5c0c02c2c1c2c1c2c5c6c6c4c4c6c3c3c3c3c0c0c3dcc4c3c0c0c2e82c3d4bd2f46c5c0c3e83c0c0e0b82e09b0f03c008131313130b0b0b0b0b0b0b0b130313131317130300130300b0ba0b82c2d3d1744d1342d0b44c4d44c6d44e1384e1382e20b03a0b03a6134000000000000001dc0c4c0d2f03171303401b1717130303131313130303131b7713131313070b070ba0f44d550380e13130b0b0b82e9b000f03c000081317131b0f030f0f0f170f03006c6c5c5c5c5c6c6c6c4c4c4c4c6c6c3c3c0c3c3c3c6c3c3c0ccc3c3c3c3c2c2c2c2c2c2c2c2c2c1c2c2c2c1c2c2ea4f45d1b44d0f0f50f51b2f51b1b50b42d1b85e1386c4c6e0f0383e83c3c0cee82c2c2c2c2ea0ba6d86d00026c0f003c03c0f000000000200171b030f17030070b070b555171b1b13131b0f0f0f0f03030f4b130f03030b1f1f0b551b17030fa0f030399426c3c0f00204c4c4c4d8c2c5c2c4c2c4c2d5555544c0c4c4c4c5c4c0c004c0c02c2c4c1c4c1c2c2d55544e1384e1382e139456954000000000000004c5c4c6c3c0c3c3c3c5c3c0c0630b170b1b0b130b0f070b0b0f070b0b1b1b171717171b1b1b131313131b1b0f0f030f0f0f1b0f0f033b0f0f0f0f0b0b1b1f1b1b0b0b5555555555646e1784e1383c0e0fa0f0f033ba0b86e555959b00026c0f003c0003c0f0000002002b17172b0f0f0f0f170f0f002c5c2cac2cac2c3c3c2c2c3ccc2c2d174ad2b43c3d43d42d45c5c8cac8cac8c3c3c3e0f470f82c8c2d2340009b03c00f000000f00031703545c4c4c5c0c0c5c0547c2c7c2c0c2c9c0c0d0340d03550380e0303030340c000000cdc5c5c5c030f0f1717000030b1703270b270b03330b0b2733030b0345d2b4dd033f53f50b49d0303030303230323033b0380cec0e0323030b48c0d000000000000000171717170b030b0b0f0f0b031f0300002c2c2c2c2c2c2c2c1c2c2c2c1c2c2c5d1747d1f47cbd47c7d42d0b45c5c5c5c7c7c7c7c7c0c7e1f031f82c2c2c2d23674000000000000002c2c2c3c0c3c5c3c3c3c0c3c0c3c3c3c7c3c3c3c3c3c3c0c3ccc5c5c5c5c7c4c7c7c7c4c7c7c00b0b0b9b0b170b0b0b170b0b0f07330b0b0b070b0b0b0b0b1f0b0b0b0b1745d1f1f51f2f50f50f0f51f47d0b42d171717171f1f1f87cec7e0f030f83c0c3e1f1f1f1f0b0b0b0b48d00000003c03c009b00000017171717550f0f52b03000170b170b2b0b370b2f070b0b2f070b0b1555555555171717172b2337232f03238bc0c8e0b234f0b5500000000000000543c0c3c5c3c3c3c0c3c0c3c3c3cbc3c3c3c3c3c3c0c3cfc5c5c5c5cbc4cac7cbc4cac7c0170b170b2f1f0b0b2f1f0b0b0f270b0b0f0f0b0b2b0b370b566d17545d43d3f55555555171717172f2f238bcec8e0f030f83c0c3e2b2337230b234f0b5500000003c03c009b000000030303030303035503135030303030303030b03070303270b270b555555515550303030303030380c0c0e0303030303030303550000000c0000000000b0b131f131f03171703031f031f2f2f1f3f4b031f03400b0b9b170b170b1f0b070b070b175551f0f47e3b80e03800000dc5c5cacfc5c5c5c5cbcfd40002c5c2cac2cdc2cbccc2c2cfccc2c2d3f55153750f5545c5c8cac8cdc8cbcec8e3f3b2382c8c2d540000000000000003c3c3c5c3c3c3c9c7c5c5c7c01f1f171717171f5b0f0f07330f0f0f0f0f0f070f0f0f1f5f1f1f1f131f131f1f0b0b0b0b0b070b0b0b070b0b0b0b0b0b55555555550b50b5566d3c5c5c8c3c1c3e0f070f87c7c7c7c7cec7e1f1f1f82c2c2c2d54000f00f0026c00000000004c5c4c5c3e0f0f0f0fa1b03000170b170b1b0b130b43070b0b43070b0b1745d1b44d432f5432f50b53d21784e1385c0e83c0e82e1b986d0003c00000000000284c7c4c7c0c5c5c0c0cec0cecbcbcecfd0c0cbc0d007c2c7c2c1c2c1c2c5d5544c3d17a6c5e17170380e000000 25 33554431 10 1023
def hc_67_5 : Nat → Nat := unpackHintV5 0x87dcf14212771f4670cf1fa0e7201bf3572e3999a47cc41a2e5e34f62d2a7c159f3d8a900fe50d4eb26a072928931c8dd19e43ccc72120318f8143c764970340dc617b8938b083504983b02025270e7a6605697502451be0ee0d2042cd1011340c000226 0x5000171717172f373f2b3f372f2b170b170b2f330b0b3f330b0b0b0b151750f53f5542d545c5c5c5cbcec8e3f3b2388c8c2c8c2d540000000000000005c0c0005c5c5c5d543c3d45c2c5c2c7c1c2c2c7c1c2c2c7c2c7c2d555554555545c5c5c5c7c0c7e1f031f87c7c7c7c2c7c7c2d5400000000000100000f1f0f0f0f0f0f1b171717170f0f1f0f0f0f0f0f0f0f0f0f0f1b2b1717171717171717543c7c2c2c3c3c2c2c5c2c5c2c7c2c7c2c7c7c2c2c7c7c2c2d0f4fd55555559b47d51f5543c3c6c3e0f0f0f0f85c5c5c5c7c7c7c7c7c7c7e1f3b1f82c7c7c2d540f00f0026c000000003c004001317131713030000f0f555170b170b1f0b130b1f070b0b1f070b0b5547d4566d5555545c4c5c4c4c4c4c4cbc0c4e2f031382c4c7c2d540f00000000000f00040f00000f0f13370f0f0f0f0f0f0f0f0f0f2f13171717131717170f130f0f0f0f0f2b13171317543ccc2c2c3c3c2c2c5c2c5c2c7c7c2c2c4c7c2c2c7c2c4c2d5555551f51f5566d543c3d1c3e0f0f0f0f85c4c5c4c4cec4e132f1384c4c4c4c2c4c7c2d540f00f0026c000000003c00103c00003c7c3c3c3c3c3c7c5c5c5c5c3c3c1ccc3c3c3c3c3c3c1c3c3c3c7d7c5c5c5c5c5c5c5c5c7c7c7c7c7c7c7c7c2c1c2c2c2c1c2c2c2c2c2c2c2c2c2c2d55555555542d42d559b0f0f070f83c1c3c3e171717171f1f1f1f1f3b1f87c7c7e0b0b0b0b5503c03c009b0000003c0f0000b0010001c0171717170707070707030707071707030703070707070703070b0707070707070b07070707070b079b070707070707071745d0741d1b46d07075072f50741d0000000000000007001c0c1c5c1c1c1c0c1c0c1c1c1c1c1c0c4c5c4c5c1c1c1c1c1c1c2c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c2c1e6c5d1741d0741cbd41c1d46d1341d074000000000000005c0171717171b1b1b1b17031717171717031b031b1b1b1b1b03545c2c5c2c6c2c6c2c6c2c6c2c6c1c2c2c6c1c2c2d555559b46d51b554000000000000004c0130317171317170313032f43132f1b0313171317131b131b545c2c5c2c6c2c7c2c7c1c2c2c4c1c2c2c6c2c4c2d55551b51b5566d540000000000000001c01717171707070707070307170707070307030707070707030707071f0707071b07070707070707070707070755555555075075566c000000000000005c0171717173b47473b170b170b3b0b470b0b0b1745d3b51d50b500000000001317131717171717171717170b0b0b0b170b0b0b0b0b0b0b9b0b130b0b0b130b1745d1f44d1f1f51f2f50b42d80aaaaaaaa690000000000000f0004c4c4c5c4c4c4c5c4c4c4c4c2c2c2c2c2c2c2c2c4c2c2c4c2c2c2c2c2e6c5d1744cbd44c4d44d1342d0b602aaaaaaaa9a40000000000003c00131713171717171717171717545c2c5c2c7c2c4c2c7c7c2c2c7c7c2c2d5559b44d51355602aaaaaaaa9540000000000010004c4c4c5c4c4c4c5c4c4c4c4d5170b170b131f0b0b13130b0b130b130b5544d44d559b5580aaaaaaaaa559000000000000103c001717171717171717171717171f1f1f131f131f1f0b0b0b0b0b0b0b0b5555550b50b5566e02aaaaaaaa9540000000000010005c5c5c5c5c2c5c2c2c2c5d17542d602aaa9a4000000003c000303000031313030f0f0f83c3e80c2c5c0c4c1c2c2c4c1c2c2c4c2c4c2c0d1744c4d44c7d44d1342d1f40e0380c4c0e80c0e0fa213031380e03980d0000000000000f001004c6c4c6c5c5c5c5cbc4c4c7c0c0cfc4c4c7c0c0e81c2c1c2c7c2c7c2d170f47d550b40e0387e9b1f87c8c0000000f130f0f0f0f0f1b031713030f0f13030f030f0f0f0f0f030f032b0317031703170317a83c1c2c2c3c1c2c2c0c2c5c0c7c2c4c2c0c7c2c2c4c7c0c2c3d43c3d40d1747d1340c7d44cbd42d1f40c3c0cee80c0e0fa0380e87e9b031fa031f230380e6034030030026c000000003c000f0000c5c4c0c0c0c0003c3e83e0f0f030b17031f0b130b1f070b0b1f070b0b0345d1f44d4f2f54f2f50b47d0380e031f887c0c7c0e80c0e0fa0387c0c7e603403000000c0000000f0003c0040171717172f03033f3b573b03032f3b2f131b131ba070b070b1f0b1f0b45c3d3b4bd551f42d0380e1f1f1f87e9b1f1f000f03c000000c3c0cdc3c3c3c3c0c3c0c3c3c3cec0c5c0c5c0c5c0c5c3c4c3c3c3c3c3c6c0c5c4c0ea0f070b0b0f070b0b030b17031f1f030b031f0b0b1f0b130b0f50f0f50345d3b2f5032f51f44d0b47d030f033ba030383e80e0380c7c7c0c7ea1fa6c0e1f031f980d00c00c009b03c0f000000000f0003c0003171703030b0b030b0b0b0b03030001f1b1f131f131f1b0b0ba0b82c2c0d1747d1f42d0b47cbd47c7d40e0380e1f031f80c2e20b030b03a030382e980d00c0000000b26c0000000f001004c6c4c6c5c5c5c5c7c0c0cfc7d5c7c0c0cbc7cbc7c7c7c7c1c2c1c2e9170f47d1f4bd550b40e0387c7c2c2c2e0ba6c00000000f1f0f0f0f0f0f1b03171703030f03330f0f0f0f030f030f0f0f1f0317031703170317031f1f1f031f1f1f0b070b0b0b070b0b030b0b030b0b0b0ba83d43c3d40d1747d1f47cbd40c7d42d0b40c3c0cee80c0e0fa0380e0387c0c7e030b0b030ba82e9b6034030030026c000000000b03c000f0000c5c5c0c0c2c5c0c9c2c9c2d5555540c0c000bc6cbc4cbc4cbc6c2c2c9c1c9c1c2c2d55540e0380e0380e0395155a55500000000400000000f13130f0f0f131b070b070b5550f131b0f0f0f0f0f0f0f13130313170303030b131f0b550f031b80c3e80c0d940c03026c0f100003d2c3c3c3c3c3c6c0c5c5c0c3c1c2c2c3c1c2c2c0c2c5c0c9c2c9c2c0c3c0cec3c3c3c3c0c3c0c3c3c3cbc0c5c0c5c0c5c0c5c0c7cbc0cbcbc7c0c2c9c7c0c7c2c2d55555555559030f033ba030383e80e0380e0380e039556566c030030026c00003c000000400003c3c3c3c3c3cac5c5c5c5c3ccc2c2c3c3c2c2c5c2c5c2c2c2c3d43c3d45d17542d43c3d1c3e0f0f0f0f85c5c5c5c8c8c2c8c2d2340f00f0026c00003c000f0000c3c3c171713032b0013170030b170303330b0b2733030b270b130b0345d033f56b3f52b44d0b49d03030303033b0380cec0e031303130313030b44c0d000000000000000 25 33554431 10 1023
def hc_67_6 : Nat → Nat := unpackHintV5 0x9fbdb84dce8425097791fba2488edbc42d069a05c430fd81587adcf93bbe6c1d0f340e022166c6ce9349e66186c78cb48bb6538dae2652dd117b6b87e236e37edc91860e58b822b84f832423dcf90fb48e86b04a8259bfa0df5360330f280c8340000190 0x1c1c2c1d2c1c1c1c1c1c6c0c5c5c0c0c0c0c0c0c1c1c0c0c1e6c1c1c1c1c0c1c0cec1c1c1c5c0c1c0c5c1c1c1c0c1c0c5c0c1c0c5c0c1c1c0c1c1c7c0c1c1c1c0c1c1c1d555555555590303a0303a0380e0380e0380e555959b070f0070700305c1705c0701c070f0030704480306c6c6c6c1c1c1c1d07070755555507030717070707030707070b0703070b070307070707070755550781e0781e0781e555a552709c1b06c0701c44070f00707080706c6c6c6c1c0c1c1c1c5c1c0c1c2c1c1c1c1c1c1c2c1c2c1e6c1c1c1c1c1c1c1c1c1c1c5c1c1c1c9c1c1c1c6c1c1c1c6c1c1c0cac1c1c1c1c1c0cec1c1c1cac1c1c1c1c1ccc1c1c1c1c1c2d5555555074fd55590781e0781e0703a0703a0781e555959b2709c1b06c07070070f00701c070f0070704480704c6c4c6c1c1c1c1c1c1c1d070b55555507030717070707030703070b0707070b070307070707070755550781e0781e0781e5955a552709c1304c0701c44070f00707080701c0c1c5c1c1c1c0c4c6c4c6c1c1c2c1c1c1c1c1c1c1c1c1c1c1c1c2c1e6c1c1c1c5c1c1c1c9c1c1c0cec1c1c1ccc1c1c0ccc1c1c1c1c1c1c4c1c1c1c7c1c1c1c1c1c1c1c1d555555555590781e0703a0703a0781e0781e555959b2709c070f0070701304c0701c070f0070704480700c0c0c6c2c6c2c5c2c5c2d55555546c0c4c6c4c0c5c5d2c2c0c9c0d540e0380c0e030380e03955945c1705c1702c171100c17200c0317031b0b1b0b03030303555540d9b5540c0c0c0c0c4c0e6c0c0c0c0c0c0c0c0cdc0c0c0c0c0d540e0380c0e030303039b80e03955946c1b00c0302c271100c03200c1703503003d2c3c6c2c1c1c2d540c0c7c0d2c0c2c0c7c0d540030303030380c3e9940c03c0f10300c0300803171703030b1703270b270b5555555033b3b4b2b03374b37032b0b0b03332733030b5555033b80ced0380e0380e555a550305c12c0b09c44030f00f080300c0c0c6c4c0c0c1e6c0c0c0c1c1c2d5540c0c0c0c0c0c0c0c4c4c0c6c6c0c0c0c0c0c1c2c2c1c1c1c1c1d540e0380c0d940c0f03c0f01c2c1c4c4c1c1c1c6c6c0c0c0c1c0c1e6d5541c6c6c1c1c1c1c1c1c1c4c4c0c5c5c0c0c0c1c1c1c1d540e0380c0d943c0703c0f00c0c0c0c0c0c0c4c0c0c0c0c5c0c4c0c0c0c0c0c0c0c0c0c2c0c1c0c0c6c2c4c2d55555555540e0380c0e80c0e80d0380e039540c0300c0c00c3c04c1302c2711200c131b131b0b0b1b0b130b55555551b13171b1713371337370b0b13331b330b0b55551b86e133b44cde0b86e555a5501304c0b044130f0130f081302c2c2c2ced1d1c5cec5d1cecad1ced1d1cac2c2d1ccceccc2c2d55555593b8ee3b8ee0b8ee555959b000b03b0f03b0f04482300171717170f0f0f170f170f0f17031717171717030f030f0f0f0f07170f0f17170f03070f0b0b0b0b170b0b0b0b0b070b0b0b070b0b0b0b0b9b0b1f0b0b0b1f0b1745d0f0f50f1751f47d1f1f51f2f50b42d171717170f070f83c1c3e1f1f1f1f1f031f87c0c7e0b0b0b0b48c9d026c0f003c000000000000004c0c5c5c4c5c5c0c3c0c1c3c3c3c5c5c3c3c1c5c3c0c3c3c4c5c4c5c3c3c3c5c3c4c3c3c2c2c2c2c2c2c2c2c1c2c2c2c1c2c2c2c7c2c2c7c2c2c2c2c2e6c5d1743c3d43c5d47cbd44c7d47d1342d0b45c4c5c4c3c1c3e0f070f84c0c4e13031384c4c4c4c2c2c2c2d1327409b03c00f00000000000000171717170f0f0f170f170f0f17031717171717030f030f0f0f0f17170f0f17170f030f0f545c2c5c2c3c3c2c2c3c5c2c2c7c2c7c2c7c7c2c2c7c7c2c2d55555559b47d51f5545c5c5c5c3c3c3e0f170f87c7c7c7c7c0c7e1f031f82c7c7c2d5409b03c00f0000000000000013031717131717030f030f0f0f0f17170f0f13170f030f0f131713170f0f0f170f130f0f545c2c5c2c3c3c2c2c3c5c2c2c7c7c2c2c4c7c2c2c7c2c4c2d5555551f51f5566d545c4c5c4c3c3c3e0f170f84c0c4e13031384c4c4c4c2c4c7c2d5409b03c00f00f03c00000000000000171717170f0f0f170f170f0f17031717171717030f03070f0f0f17170f0f07170f030f0f1f1f1f1f1f1f1f1f0b0b0b0b0b070b0b0b070b0b0b0b0b0b55555555550b50b5566c5c5c5c5c3c1c3e0f070f87c7c7c7c7c0c7e1f031f82c2c2c2d5409b03c00f0000000000000003030303030303170313030303030303030303030303030f03030317030303170303030fa80c0c0c0c0c0c0c2c0c1c0c0c7c2c4c2c0c0c0c2c0c7c0c0c0d0340c0d40c5d47d1340c0d40cbd42d1f40e0380c0e80c0ea1fa6c0c0e80c0c0c0e03980d026c03000c000000000000000c0c0c0c0c0c0c0c0c0c0c3c0c0c0c5c0c0c0c5c0c0c0c3c0c0c0c0c0c0c0c5c0c4c0c0ea030303030303030b03070303031f03030303030b1f0b130b0340d0303503175032f5030351f44d0b47d0380e0303a0303a0303030303a87e9b0387c0c0e603409b00c00300303c000000000000003030303030303170317030303030303030303030303030f03030317030303170303030f0303031f0303031f030303030303030b030703030b0b0b0ba80d0340c0d40c5d47d1f40cbd40c0d42d0b40e0380c0e80c0e80e1f030380c0c0c0c0ea0ba6d80d026c03000c0000c0f00000000000003131303030b07035550303030303030303131303131703030303030b131f0b550380e03036509b0300c00000c0c0c0c0c0c0c5c0c5c0c0c0c0c0c0c0c0c0c2c0c1c0c0c9c2c9c2c0c0c0c0c0c0c0c0c0c0c0c3c0c0c0c5c0c0c0c5c0c0c0c3c0c0c0c0c0c0c7c0c0c0c7c0c0c0c2d555555555590380e0303a0303a0380e0380e555959b026c03000c000000000000005c5c5c5c3c3c3c5c3c5c3c3c5c2c5c2c3c3c2c2c3c5c2c2c2c2c5d1743c3d43c5d542d45c5c5c5c3c3c3e0f170f88c8c2c8c2d23409b03c00f0000000005c5c00017171317170f0f0f170b170b13330b0b1f330b0b1f0b0b130b0b1745d133751f3f51f51350b47d1713171313371384cec4e131313130b131f0b44d2d0000000000000001703000171717170b0b0b0b0f0f0b0b0b0b0b0b0b070b0b0b070b0b02c2c2c2c2c5d1747cbd47c7d47d1f42d0b45c5c5c5c7c0c7e1f031f87c7c7c7c2c2c2c2d2327400000000002c0000003c7c3c3c3c3c3c6c5c5c5c5c3c3c7c3c3c1c3c3c3c3c3c3c3c1cac5c5c5c5c5c5c5c5c2c2c2c2c3c1ccc2c2c2c1c2c2c2c2c2c5c2c2c2c2c2c2c2e6c2c7c2c2c2c7c2c3d43c3d45d1747d1f47c7d47cbd42d0b43c3c1c3e0f070f0f85c5c5c5c7c7c7c7c7c7c7e1f3b1f82c2c2c2d232740f00f0026c000000002c000f0004c5c4c5c4c0c0003c3c2c2c2c2c2c2c2c2c2c2c2c7c2c2c0b0b0b9b0b070b0b0b070b0b1745d1f44d1f2f51f1f50b42d17131713131313131f031387c0c4e0b0b0b0b44c9d00000000000b0000000f0f07330f0f0f0f0f0f070f0f0f1f13171717131717170f130f0f0f0f0f1f131713170b0b0b0b070b0b0b070b0b0b0b0b0b0b1f0b0b1f0b0b0b0b0b9b0f50f0f51745d1f2f5131f51f44d0b42d0f0f070f83c1c3c3e17131713133b1384c7c4e131313130b0b0b0b44c9d03c03c009b000000000b0003c0040131b131b171717172f1f2f1f07073f1f571f07070b0b170b070b070b0b0b9b1f0b1f0b45c3d1f5547d2f42d0781e1f8ee0000040171717171f07073f1f571f07072f1f2f131b131b0b0b070b070b1f0b1f0b0b0b9b45c3d1f4bd551f42d0781e3b87e00000 25 33554431 10 1023
def hc_67_7 : Nat → Nat := unpackHintV5 0x83e8d3401c761f3f33cf03a7074d8d137e8a11b2533ccefa8c6420d72f949f173724cb2b1c254693c287a6e936635c95018c496c45234e5a10d634481f1303cb9101ae4de0c6a420551390267505110a8c06bd7202daa100f59df058c88010a6f0000214 0xdc6cdc6c6ccc6ccc6cac2c6c6cac2c2c2c2c2c2c2c2ea51b4dd3346d0b42daa8ee8ce82ea9a47c1f06c1f07c1b02c2c0b23107c8833333317331733332b333333332b0b0b0b0b0b0b0b0ba954cd4cccd42d0b4ee3b8ee3b4782c2c2c2c2ea0ba6d8ed00330f0330f00b0b02ccc4208c1344c5ea84c4e86c0eaa85c2c5c2c6c2c4c2d0c1c2c2d0c1c2c2d5555555556aaaa9556a9545c1704c1305c3c05c3c02c17112204c5c4e6c4c4c5c5c4c4c4c5cac5c5c2c5c2c6c2c4c2c5c5c2c2c5ccc2c2d5555555556aaaaaaaaa959b6585ea17a86ea2ba85e17aa85eaa82ea1fa5951705c1304c170f0170f00b05c4488a083c00c5c4d0303aaa1717aaa030b17031b0b130b27070b0b27070b0b5555555555aaaaa555aa5590305c1304c230f0230f00b08c4488031317171317139b031313171717030b17031b0b130b032b0b0b2733030b5555555555aaaaaaa8ae47aaa566d9603a85ea1ba8aea038aeaa2baaa0ba87e96540c1704c1300c3c08c3c02c2311222820f00303aaa031717036713671b6713671b42c1c0ea81c1e81c2c1c2d5555555556aa9556aaa9540c1708c3c08c3c08c2302c07112200c2c2c0c5c5c0c0c4cccaccc4c0cac2c2c2e6c1c5c0c2c1c5c2c1ccc2c1c2c2d5555555556aaaaaaaaa959b6580ea17a80e33aa8ceaa87eaa82e0ba81e33a5950305c030f0230f02308c0b01c4488a083c02c2eaa90c4d0c6d0c4d0c6c5c5c5c5c1c0eaa81c5c2d0b0b070b070b555555555555a5aaaaaa55170f0170f01705c1705c0b01c44880b0b0b171307170713172b1717171707170b07170b0b0b0b0b9b070b070b45d3f5555555555aaaaaaaaaa566d9617aaa0785eaa17a85ea1faaa0ba81e96545c3c01c3c05c1705c1702c0711222820f003031b03030b13030307030b070355aa59b90380e0380ea039aea1b8ae0b81e650303c80f04c6c4c6c9c0d6c5d6c5c9c0c2c2eaa81ccc2c1c2c2d0b0b07130baa0707a5555555555aaaaa555aa5592308c1304c230f0230f00b01c4488131b131b2707172717072b0b0b0b07330b070b0b0b0b0b9b07130b0b07130b5555555555aaaaaaaaaa566d9627a85ea1ba8aea078aeaa2baaa0ba81e96548c2304c1301c3c08c3c02c0711222820f0a80c5c5c0c0cdd0cad0cdc0cac0c2c5c0c0ccc2c2c9ccc0c2c9c2c9c2d55555555555aa95696aaa9540c1700c3c08c3c08c2302c23112200c0c0c0c4e0303030317aaa03030303270b130b0303030b0307030355555555555aaa6aaaaaa550300c1304c03030030f00b08c44880b0b03171703031303333767331313033303131b131ba0b0b9b170b170b3307070b070b0b0b2b0b55555aa95a0f03c0f03c030b0b0307a85c2c0c2c0c2d556aa83c0f02c2c5c4c4c1c5c1c1c4c1c5cdc0c5c5c0c4c5c4c6e85c2c5c2c2c2e6c1c2c1c2c5d3f555556aa5683c0f03c0f04cdcdc5c4c5cdc4cac4caea0b0b37330b0b13330b0b2b0b130b55555555555aaa555a9aaa552308c130f0130f01304c0b08c44886f6f0b0b0b6f0b555555aaaaaa566d96a85ea2baaa0ba8ce96548c2308c2302c2311222820f040c6c0c0c0c0c0c0c0c6c2c4c2d5555540c0c0c0c0c0c0c0c0c0c0c4c0c0c0c6c0c0c0c1c0c0c0c2d55540e0380e0380e0395569540c0304c1302c271100c3c00c0c200c03030303031b9b03030303030317030303030303030b030703031b0b130b0303030303030303030303370303030303033b03030337030303130303032b030303270303030b5555555555640e0380c0e80c0e80e0380e039556566c0c0300c0c00c3c04c1302c2700c3c00c0c11200c0345c0c0c2c5c0c6c2c6c2d5555540c0c5c4c5c5c0c0c6c6c6c4c0c0c0c0c2c2c6c1c6c1c2c2d55540e0380e0380e0395569540c1705c1702c171105c3c05c3c200c03031b9b17170303171717030303030b17031b0b1b0b17070b0b17070b0b031703171717031703171b031b1b1b031b1b1b0317031717171b0317033b17171717030b1b1f031b0b0b5555555555640e0380e0380c0e80c0e80e039556566c0c1705c1705c3c05c3c02c1705c3c00c3c11200c0703070303070707031740c0c1c1c1c0c1c1c1c0c1c0c5c0c1c0c5c0c1c1c4c0c1c1c7d55555590380e0380e0380e555959b0701c0305c1304c070f0030704480300c5c5d031b030b17031b0b130b55555503031717171703030303030313131b1b0b0b270727070b0b55550380e0380e0380e56559b5a550305c1304c0b05c44170f0170f080305c5c5c0c0c0c0c0c5c5c0c0c6e6c5c5c1c2c2c4c1c2c5c2c2c0c2c5c0c6c2c4c2c0c5c0cec4c4c5c5c0c4c0c5c5c5d1c0c5c0c5c0c5c0c5c0cac4c4c0c4c6cac0c2c9ccc0ccc2c2d555555555590303a0303a0380e0380e0380e555959b130f0130f00305c1304c0b05c170f0030f04480300c0c0d030303031b0b1b0b55555503030303030303030303031303030317030303070303030b55550380e0380e0380e555a550300c1b06c0b09c44030f00303080300c0c0c0c0c0c6e6c0c0c0c0c5c0c0c0c0c0c6c2c6c2c0c0c0c2c0c1c0c0c0c0c0c0c0c5c0c0c0c0c0c0c0c0c6c0c0c0c6c0c0c0cac0c0c0c0c0c0cec0c0c0cac0c0c0c7c0c0c0c2d5555555034fd55590380e0380e030380e80c0c0cee80e039556566c0c0306c1b00c0c00c3c02c2700c3c00c0c11200c0303030340c0c0c1c1c1c1c1c2d5555540c0c0c0c0c0c0c0c0c0c0c4c0c0c0c6c0c0c0c1c0c0c0c1d55540e0380e0380e0395569540c0312c4b01c071100c3c00c0c200c030303030303030303031b034b03030303079b0303030303030707070707070b0303030303030303030303330303030303033b030303330303030303031f03030307030303075555555555640e0380c0e80c0e80e0380e039556566c0c0300c0c00c3c18c01c0700c3c00c0c11200c03171703030740c1c1c1c1d5555540c0c1c2c1c1c0c0c1c1c1c4c1c1c1c6c0c0c0c0c1c1c1c1d55540e0380e0380e03965569540c1705c1701c071101c3c01c1c200c 25 33554431 10 1023
def hc_67_8 : Nat → Nat := unpackHintV5 0x8dd9b07f3ba87ed8187eb8087839a07071f26143cc5f80705ee0285cd8825ae07e5349e65288305140524c513c4c10104c10004bd0104a984e4a98004a9800499042416a0a33ab702ce1b22619b21ed1d21721ec0fd1d40809f20458ec000116 0x145c4c4c5c4c5c6c6c0c0c1c2c1c2c2c2c5c6c6c5c4c4c5c5c5c5c4c4c0c5c5c0c0c0c2e82c0d03566d540e0380c0c0e0383c0f03c0f151717171717171b031717030317033317171717031703171717330317031703170317032b330333332b0b1707330b0b0b070b0b0b0b030b0b030b0b0b0ba9035035566d555555540c5c0cee80c0e17a0380e0380d1e030b0b030ba82e9b55170f0170f00305c1705c170f0030f00b0b02c5c4480306c0c0c6c6c6c0c5c5c0d42c2c1c2c1c2c6c6c6c6c6c4c4cdc6c6c6c6c6c0c0c6d2c6c0c0c2e82d66c6d1b5546c6c0e0382e0b83c0f03c0f06c6c6c6c2c2c2c2c2c2c2c2c6c0c6c5c6c5c6c0d546c0d42c2e82e0b0b55555555551b86e1b86e0b982c0e82c0e9547c1f06c1b02c0b06c3c06c3c11206c1b1b1b1b1b031b171b171b03546c6c6c5c6c5c6c6c6c6c6c6c6c6c6c6c6c0cac6c6c6c6c6c0ccc6c6c6cac2c2c2c2c2c2c2c2c2c1c2c2c2c2c2c6c1ccc2c2ea55566d1b546d46d3f5555551b86e1b86c6c6e1b0386e86c6c0cee82c2c2c2c2ea0ba6d547c1f06c1b06c3c06c3c06c3c06c3c02c2c0b1f11206c131303175333131317531b179b9b031303179b03131717530313031b1b530b1f9b86e6c0c4c4c0c0d5070b070b550380e0f03c03175317170353031b1b50b0b070b070b1b1b53531303031353135303031b532b131353131b0ba0b1b46d59b55534bd1b1b0380e0b82e0f03c0f03c47d4c5c0c0c6c5c2c7c0c5c0c5c6c0e6e1b131350b0b0b0b53171753131b0313542e82c4d1b13566d544e1384c4e82e0b84c1302c4c3c0f11303171703131b1f0b03173f46e1f00c6d0b85d1b82c1f131b131b0b0b0b0b0b0b0b0b031717031b035550b0ba0b82c2d551b555555551b86e138dc4cde0ba682c0e82c0e9547c1f04c1302c2c0b3307c3c07c3c1447c81304c0c5c4c5c0c4c6c4c6d51b3333171b17331b330333131333371313033333331b2b131313131b2b0b0b0b0b0b070b0b0b070b0b0b0b0b0ba9551b51b5566d5555546e1b84c0e84c0e84e37133782c2c2c2c2ea0ba6d547c1f04c3c04c3c04c1307c3c06c3c02c2c0b331447c81300c0c0c6e6c0c0c0c5c0c2c1c0c0c0c0c0c0c0c0c0cbcbc0cfdac0c0c0c6c4c4c6d940d55034bd1b50b0340e0380d540c0c0f03c0f11f031b9b170317170303070b070b031717031b13131b171717172f2f173f83171717650346d55174bd42c0d0380e0355030f03c0f03c45c5c5c0c0c0c5c0c6e6c5c1ccc2c1c2c2c2c5cfe0c4c5c4c4c5c4c5cbcbc0c5c5c0c6c4c4c6d945d2f5540d1b50b0340e0380d540c3c0f03c0f1170303031b9b0303170303030b0b03073303030303031b13131b030303032f2f033f83030303650346d0340d5542c0d0303a03033b80d540c0c0f03c0f11f030303030303030303031b031303030303030355030750b0b0b0b555555555550380e55030350380e0399540c0300c0c00c3c0bc2f02c0b11200c0b0b0b0b0b0b0b0b3f2f173f172f3f3f2b2f373f372f2b5a554fd553f55550b5334ee3b8ee3b82e60b0b555553b4bc2f0bc2f02c0b0bc3c0bc3c144fc823140c6c4c0c0c0c0c0c0cac0c2c1c0e966c0d0340daa0380e0b80c0f02c8d44c5c4c6c0c5c0cccacac5c1c7c2c1c2c2c2e80d03566c5e1baa80e3382e0f03c0b17 24 16777215 10 1023
def hc_67_9 : Nat → Nat := unpackHintV5 0xcc180e6098aeaea23555593f0a0f93a4f342925e23710d443a84c03c3e98791ce04d8d931ba6c380c3298709944010c7e0485ed8a32f48049624300a082144811061f4c978d5a49865b0a42c40d3121c80877e3201fe38208c0e604300601ec0580001ec 0x26c2d4bc0c0c5c5c2c0c0c6e6c0c2c2c0c2c2c2c2c0c0c5c5c5c5c0c0c0c0c0c0c4c4c6c6c2c2ea0b82c2c2c2c0d1746d1342d0b4bd63cbd40e0380e37033780e80e80c0e80c0e980d0305c1304c0b0b02c5c170f0170f0417200c17540d52f03033f334b3303032f332f171717172b13132b070b070ba1351744ccd2f5540e038dcdc2c2c2e0ba6e43c0f03c0f02c5c05c5c5c0c0c0c0c0c5c5c0c0c6e6c0c5c0ccc4c4c5c5c0c4c0c5c5c5ccc0c5c0c5c0c5c0c5c0cac4c4c0c4c6cac2c5c1ccc2c2c2c1c2c2c2c2c0c2c2c0c2c2c2c2ea175131750345d1b44d335033350b42d0303a0303a0380e038dc0cde030b0b030ba82e9b60344c3c04c3c00c1704c1305c3c00c3c02c2c0b17105c80300c0c0c0c0c0c0c0c2c2c2c2c0c0c0c0c0c0c0c0c0c0c0c4c0c0c0c5c0c0e80e030b0340d1b46d0b42d032f5030350380e0380e0380e0303a0303a60340c0306c1b02c2c0b1f00c3c00c0c107c80300d51b542e82c0d1b50b540d0340e039030f03c47c0d517540c0c0c0c0c6c0c6c0c0c0cbc0cbc0c0c0cfc0c1c2c1c2e80d1b40d550340d42c6c0c0e0380c0c0e0ba6d030f03c0f00c0b1f47c0c0c0c0c0c0c6e6c0c0c0c0c5c0c0c0c0c0c0c5c0c0c0c0c0c0c0c0c6c0c0c0c0c6c0cac0c0c0cac0c0c0c0c0c0ccc0c0c0cac0c0c0c0c2c2c2c2c0c0c0c0c2c2c0c0c1ccc0c0ea0340d1b46d03035035035030350b42d0380e0386c0c0e030380e80c0c0cee80c0c0c0c0ea0ba6d80d0300c1b06c03030030f0030f0030300b0b02c7c41f200c03031f0707070b1b030b03030303170303030b0b0b0b0b070b0b070b1b03131b130317170b82c0c6d1b45d1742d0b40d40e0380c0e030380e0380e03980d1705c1705c0b02c0305c417200c0317030b0b0b0b030303030303073303030303030313039b030303030303030333030380c0c6d1b40d0342d0b40d0340e0380c0e030303039b80e0380e03980d1b06c0300c0b02c0300c41f200c031b03030303031b17030303030303030b070b070b03030303031b0303031b03130b82c0c6d4c6d5340d7f40c0c0e0380e0383c0f00c1f06d54bc0c0c6c5c0c0c0c0c0c6c0c0c0c0c0c0c2c9c1c9c2c1c2c2c2c0c0c6c0c6c6c0c0c0c0c0c0c2e0b0354d5303503030380e0380e0f03c0307c9b039b0b1b544c6cbd5303030b03546d4d4c6c2c1c1c2c0c0dfc0c0c2e0b03540d54c0d0340d540c0c0e0380e0383c0f00c2f1012f1703030b03003c7c3c6c2c1c1c2c0c0c7c0c7c0c2e0b03010f40d2f40c0c0c0c0e030fa0380e0300f02c0c0300c000f803171703030b0b0b0b030b0b0b0b0333332b033737032b0b0ba0b80c2c0d17542d0b40cfd4fd40cee033b80e0380e0380c2e80c2e980d0305c00b02c030f00f04200c03030303030303030303030703030303139b0303030303031b0b82c2c0d0340d0342d0b44d1b40e0380c0e030380e0380e03980d0300c0300c0b02c1304c41f200c0303030303030313030303031703130303030303030303030b030703030b0b0b0b0340d03035032f51b44d0b42d0380e0303a0303a0380e0380e60340c0300c0c00c3c04c1302c0b107c80304cdc6c4c6c2c2c2c2c2c2c2c2c2c2c6c4c5c6c5c4cdc4ccccc2c2e82e0b0b51b44d0b42d133751b3f51b86e133b84cde0b82e0b0ba0b0ba61b47c1f04c1302c0b04c3c04c3c107c81300c0c0c0c0c0c0c0c0c0c2e82d544c0c0e0383c0f00d503030303030303130313030303130303030303031303131307070b070b0b0ba555550380e130303030382e9b0f03c0f00c0b1303030303030303030b0b0b0b5503035030303130303031b0303a0380c2d55555555540e0380e0380e60303a0303a550300c4f13c0b0b02c9c030f00303044803140c0c0c6c4c0c0c2c1c0c2c2c0c0c0c0c0c0c0c0c4c4c0c6c6c0c0c0c0c0c2e82d66c0d035540e0380c0c0e0380c0f03c0f15030303030303031b030303030303030303030303030333030303030303330303033f0303030303032b030303030303030b030703030b0b0b0ba959b40d503555034fd5555540e0380c0e80c0e80e030380c0c0c0c0ea0ba6d540c0300c0c00c3c13c4f00c3c00c0c02c2c0b2711200c03545c4c4c4c5c5c5c5c4c0c0c4ccdac4c0c0c4c4c4c4c4c4c4c4c4cccac1c2c1c2e9555544c0c0e0313a13130b0b0b82e9b0f03c00f03c0b1387131b1b871340e0303171703030b0b030b0b0b0b0303555871b1387131b0b0ba0b82c2d0355555555550380e0380e03980c0e80c0e9540c1705c1702c0b05c3c05c3c11200c 25 33554431 11 2047
def hc_67_10 : Nat → Nat := unpackHintV5 0x7dbcb59e6c20673ecb89c091e46a78b599c01bc62109e17a41c05988a1157d1ca50b4a8134a1c647a0b111c704245283e90731ae3ec0618eb020036c87f0d021603148580b9417c2a607e09c61a4237c73883e1421bf0a1060e1dc1058fc02dc27408046d8000402 0x1317139b13131717131313171f170b0b0b0b0b0b0b0b0b070b0b0b070b0b1745d1b44d17175174f50b42daaaa1faaaa1791ea0ba6ea9a617a85ea1ba87ea1785eaa17aaa0b96a635a85c1704c1305c3c05c3c02c0b105c88a083c04c5eaa84c0eaa84c4e130b13030b0b0b070b0b0b0b0b0b0b0b0b0b0b0b132f5131351745d1344d0b42daaaaaaaa13aaa9a44c3c04c3c04c1304c1302c0b104c88131317131313131313131317139b0b1307330b0b0b070b0b0b0b0b0b0b0b0b0b0b0b134b5131351745d1344d0b42daaaaaaaa13a0ba6ea9a613aaa1385eaa17a85ea13a84ea0b96a4b5a84c3c04c3c04c1304c1302c0b104c88a083c00c5c4e0303aaa1717aaa030b0b030b0b0b0b0b070b0b030303030345d1b44d1f1f51f2f50b42daaaaaaaaaaa690305c1304c1f0f01f0f00b02c41f2200c4c5c5c4c5c4e6c0c4c4c5c5c5c0c2c2c0c2c2c2c2c0c1c2c2c2c1c0c2c0d1746d1340c7d47d3d42d0b6aaa87eaaa87e47a82e9baa6980ea17a86ea1fa80e2baa87eaa80e5a98d6a0305c1304c030f01f0f00b02c41f222820f05a55031717032713271b2713271b030b0b030b070b0b030303030b0b0b0b5555555555aaaaaaaa9a550305c230f0230f02308c0b02c4488540c5c5c0c0c4c9c7c9c4c0c7c0c2c2c0c0c1c2c2c2c1c0c2c2c2c2c2d59b45d51755556aaaaaaa89e82e9baa5580ea17a80e3faa89eaa8aeaa80e5555a80c1700c3c08c3c08c2302c0b11222820f05a554313431b4313431b171717170b030b0b0b070b0b0b0b0b0b0b0b0b0b5555555555aaaaaaaaa6a55170f0170f01705c1705c0b02c4488545c4c5c5c5c4c5c7c5c5c5c5c2c1c2c2c2c1c2c2c2c2c2c2c2c2c2c2d175175566d55561791eaaaaaaaa82e9baa5585eaa85e17aa85ea17a8aeaa82e5555a85c3c05c3c05c1705c1702c0b11222820f0131b131b1f031f171f171f035a550b0b0b0b0b0b0b0b0b070b0b0b030b0b5555135555556aaaaaaaa9a9547c1f04c1307c3c07c3c02c0b112204c6c4c6c7c9c6c5c7c5c6c7d50b0b0b0b0b0b0b0b0b070b0b0b070b0b55566d13544d55aaaa1faaaa1f91ea0ba6ea95663a85ea1b8aea1faa1b8aeaa1faaa0b95556a1f07c1304c1b0f01f0f00b02c4488a083c04c0c4c5c4c4c4c0c4c4c4c4d69542c2c2c2c2c0c2c2c2c1c2c2c2c2c2c2d5555555556aaaaaaa84e9a551304c130f0130f01304c0b02c4488131313171313132713131313542c2c2c2c2c4c1ccc2c2c2c1c2c2c2c2c2c2c2c2d55135135566d56aaaaaaa84e82e9baa55aa17a84eaa84e37aa84e2ba84e37a82e55558fd6a1304c130f0130f01304c0b02c5113222820f0a0b0b03566caea03945c0c1c5c0c5c9c4c5c4c6e81c2c1c2c2c2c0d03566ea89e2b80e0f03c271707270727131f131fa81c2c1c2c1c1c2c1c1c2c1c2c1c2c9d51d0747d1342d076aa47a2baa82e691f07c134701c231304c0b01c41f22280c5c4c0c0c4c0d0c4d0c4c4c4c0c4c0c4c4c4c4d42c2c2c2c2c2c4c1c9c2c1c2c2c2d544d13566eaaaa83c0f03c0f113a80c5c5c0c0cdd0cad0cdc0cac0c2c2c2c2c0c0c2c2c2c2c2c0c2c2c2c2c2c0d1740cfd50cfd58d42d0b6aaaaaaaaaa9a40c1700c3c08c3c08c2302c0b108c88030303031380c0c0c0c5eaa80c0c2c0c0c0c2c2c2c2c0c0c0c2c0c1c0c0c0d0347d1340c0d40cbd42d0b6aaaaaaaaa9a40c0304c1300c0c00c3c02c0b107c88503171703031303271f1f271313031f03131b131ba070b070b030b030b0b0b59b1745d555aaaaa0f03c0f03c5171313171717171313171f1f031717031317131ba070b070b0b0b030b0b0b1745d59b555aaaaa0f03c0f03c131f131f1f1b1f1b1f1f1f0b0b0b0b0b0b0b0b0b070b0b070b5555544d55aaaaaaa9a551f07c1304c1b07c0b02c448813371f1713171f131f131fa82c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2d47cfd44cdd47d133742d0b6aaaaaaaaaa9a47c1f04c3c04c3c04c1302c0b107c8803030303030303030b0b0b0b5555555030303031b03030313030355030755555aaaa9a555a550300c2308c0b02c4403030030f0884b634b630b0b0b0b0b0b0b0b2f3f3f172f173f2f2b3f372f373f2b550b0b555553f5542d66aaaa6969556548c2308c2302c0b08c3c08c3c112202c2c2c2c2c2c2c2d542d0b6aaaa82e9baa69aa17a8aeaa82e5a96a2308c2308c0b02c423222820f003031b030303030303030b0b0b0b0303030303030303030303130303031b0303a0380c2c0d0346d1342d0b40cbd40c0d40e0380e37030380e0380c0e80c0e980d0300c1304c0b02c030f00303041f200c035544d030303030303032f032f0303033f034b0313032b2707070b070b0b0ba0340d44c0d2f5540c0c0e033fa370303030382e9b0f03c0f00c0b2703030303031b9b0303030303031703030303030303030303033303030303030333030303370303031303370303032b032b030303030303030b030703030b0b0b0ba80d0340c0d40d46d1340d40c0d42d0b40e0380c0e80c0e80e37030380c0c0c0c0ea0ba6d80d0300c03030030f01304c030f0030300b0b02c9c41f200c03030b170303030b0b030b0b0b0b03031713171703031b1b1b13030303030b0ba0b82c2c0d1746d1b42d0b46cbd46c6d40e0380e0380e0380c0e80c0e980d0305c1705c0b02c170f0170f0417200c51340d5171717171b1b1b1b1b03032f1b2f1b03033f1b57070b070ba45c6d1746d2f5542d1b1b0380e0b0b0b82e9b0f03c0f03c0b1745c0c0c6e6c5c5c0c0c5c5c5c0c0c0c0c5c0c5c5c5c0c5c0c5c6c0c6c6c6c0c6c6c6c0c5c0c5c5c5c6c0c5c0ccc5c5c5c5c0c2c2c0c2c2c2c2c2c1c2c2c2c1c2c2ea0345d1b46d171751751b5031b50b42d0380e0386c0c6e030385e80c5c0cee80c2c2c0c2ea0ba6d80d0305c1705c170f0170f0170f0030f00b0b02c5c417200c 26 67108863 11 2047
def hc_67_11 : Nat → Nat := unpackHintV5 0x8179c03ece7b9e8b370edb9a872ecfc35e6e419aa524c34a825d3d1a2c6a8d151b468a3f13a4df50124fa80111d5808369603df4f01c1eb70d2c38c5f8a762c4cde138ea608884fc3be2181a9cd50b946e84df3ac1fb1d20d18b004a27a80f05840001e0 0x540c5c0cdc5c5c5c5c0c5c0c5c5c5d1c0c5c0c5c0c5c0c5c5c4c5c5c5c4c5c6c0c5c5c0ea17070b0b17070b0b030b17032733030b03330b0b270b270b40d40d559b555555550303a0303a0380e032b2b032ba8ae9b0380d1e55170f0170f00305c17470f0030f05c05c1702c1711200c030303030303035503135030303030303030b03070303270b270b555555555550380e550303503980e039540c0300c0c03003030f0f02b0bc0b09c4480300c0c0c6c4c0c0c0c0c0c0c0c0c0cbcbc0cfd2c0c0c0d940c1e6c0c0c0c1c1c2c1c1c1c1c0d55034bd4dc0d0740e0380d540c0c0f03c0f01c2c4c1c1c6c1cfd2c1c1c1c1c1c1c1cbcbc0c5c5c0d940c0c0c1c0c1e6c1c1c1c1c1d2f5540d4dc0d0740e0380d540c3c0703c0f0dcacdcacfcbc5cfc5cbcfd69542c2cac2cdc2cbccc2c2cfccc2c2d3f55553753750b553b8ee2b98acad5542e3b954ed2f0bc2b0bc2f0f02f0f00b0bc4482301c1c1c5c1c1c1c9c9c7c9c7ea07030717070707030707073307030737070307330707075f070707130707071b070707070707070707070707070707075555555555075075566c1e0781c1c1c1c1ea1fa6c1c0e81c0e81e0707079547c1f01c1c3c01c1c0701f07c070f0070700701c4480700c0c0c0c0c0c0c0c0c0c3c0c3c0c0c0c0c0c0c0c0c0c6c0c4c0c0e03c3c0c0c1e6c0c0c0c0c0c0c1c1c1c1c1c1c1c1c1c1c2c0d0340c0d40cbd43d0f47d1f41d0740e0380c0e80c0e80c0380e0380e03980d07070b070f07070707070f030f0f03071307070707071b0317170380f0f030303030307070303079b0707070707070707072f5070750345d0f43d1f47d0741d0303a0303a0380e0300e0380e0380e60355030303030303030f030f0303030303030303031b0313030380f0f030303030303030b030703030f0b0f0b270b270b566d03540d5555550380e0303a0303a0300e03980e0395550f0f0f0f0f0f0f0f030f0f03171317171713171b0317170380f0f17070b0b17070b0b030b17030f0b0f0b270b270b40d40d559b5555550303a0303a0380e0300e03980e039543c3c3c3c7c7c7c7e03c3c1c0c1c5c1c1c1c0c1c1c1c3c1c1c1c3c1c1c1c4c1c1c1c6c1c1c1c1c1c1c1c1c1c1c1c1d555555541d41d559b0781e0701e07981c0e81c0e81e079543c3c3c3cdcacdcae03c3c2c2c3c2c3c2cac2cdc2d43d0f4ad3742d4ee3b83c0f8ae3782e3b98ed37474717371747372b372ba82c2d1ccc2c2cdccc2c2cac2cdc2d51d4dd1d4ad3742d4ee3b8acacacacaea2ba6c2e3b4798ed03b470f0370f11c0ac3702c1082300c0eaa80c5c5c0c0c0c0c0c7c4c7c6e0b0b071703aa0707a071f0b070b0b0345d1f1f51f2f51f47d0b41daaaaaaaaaa690305c1f0f01f0f01f07c0b01c41f2200c2c2c0c5c5c0c0c4c7c6c7c4c0c6c2c2c2e6c1c5c0c2c1c5c2c1c7c2c1c2c2c0d1740c7d47d3d47d1f42d076aaaaaaaa1fa6ea9a603a85ea038ceaa1faaa03a0ba81e96a5a80c1700c3c07c3c07c1f02c07107c88a083c04c2c2c2c1c2e0b070b070b1745d1344d0b41daaaaaaa69aa17a07aa81e6a4b6a1304c1304c0b01c4132220802c2eaa85c4c5c5c1c1c1c0c5c5c5c5c1c0eaa81c2e0b070b070b1f2f51f1f51745d1f47d0b41daaaaaaaaaa69170f0170f01705c1705c0b01c4172202c2c2c5c5c4c1c5c1c4c5c5c6cac5c5c5c5c1c5c2c1c5c2c2c2c2c2e6c1c2c1c2c5d3d41c5d45d1747d1f42d076aaaaaaaa1fa6ea9a617aaa0785eaa17a85ea07a0b82ea078ce96a5a85c3c01c3c05c1705c1702c07105c88a083c169540c5c5c0c0c0c0c0cac4cac6c0c2c5c0c9c1c2c2c9c1c2c2c9c2c9c2d545d55555555aaaaaaa9aa550305c230f0230f02308c0b08c4488540c5c5c0c0c4cac6cac4c0c6c0c2c5c0c0c7c2c2c9c7c0c2c9c2c9c2d59b45d51755556aaaaaaaa2ba6ea95603a85ea038feaa4faaa03a0ba89e95556a0305c030f0230f02308c0b08c4488a083c169545c4c5c5c5c4cac0c5c5c5c5d0c1c2c2d0c1c2c2c5c2c5c2cac2cac2d5555555556aaaaaaa6a9545c3c05c3c05c1705c1702c17112215171317171713171b17171717171f0b0b17170b0b170b170b2b0b2b0b45d45d559b555585e47aaaaaaaa8ae9baa5585eaa85e17aa85ea17a8ae82ea33a55558fd6a170f0170f01705c1705c0b05c4488a083c07c7c7c7c1c7c7c5c1c5c7d7c1c6c7c4c1c4c7c6c1c2c1c2c1c2c1c2d5555542d42d559baaaa87e9baaaaaa5589ea17a81e87e5faa81e33aa82ea07a5555a87c1f07c1f07c3c01c3c02c0711222820f0a80c5cac5c0cac0c5cacac5c5c0cac0c2c5c0c0ccc2c2c9ccc0c2c9c2c9c2c0d1740cfd50cfd4ad2b42d276aaaaaaaaaa9a40c8c172300c3c08c3c08c2302c23108c880b0b131b131b0b0b9b170b170b1f0b03171703031f031f3f4b1f2f2f031f0303542c1c1c2d17551f4bd1f42d9aa6590f03c0f03c47c2c2c5c4d2c5c4c5c6cac5c2c5c2c2c2e6c5cbcbc1c5c1c1c5c1c5cfd2c0c5c5c0c0d50b07070b174bd5545c7d0b66a99643c0f03c0f1170303030303030303270b270b5540d9b555540c0c0c0c6d5540c2c0c0c0c1c0c0d555a5aaa9aa555a550300c2308c0b08c44030300c00c0c3c3c220acacacac2c2cac2cac2cbcfcfc5cbc5cfcacad5542c2cfcccbccc2c2d54fd4ad550b5566aaa6a969556548c2308c2302c2308c3c08c3c1448c882b2b2b2b0b0b2b0b2b0b52b4ad0b5aaaa8ae9baa69aa17a8ae82ea33a5a96a2308c2308c0b08c423222820f00303aaa84c4c0ea84c4e80c2c2c0c2c1c2c2c0c0c0c0c2c2c2c2c0d1744c4d44cbd44d1342d0b6aaaaaaa84eaa690304c130f0130f01304c0b02c4132200c7c4c4c5c4e6c4c4c0c4c4c4c4c0c2c2c0c0c1c2c2c2c1c0c2c2c2c2c2c0d1740c4d44d2d44d1342d0b6aaaaaaa84e82e9baa6980ea17a80e37aa84eaa84ea13a80e5a92d6a0304c030f0130f01304c0b02c413222820f01384c5ea84c4e86c0eaa82c2c2c2c2c2c2c2c2c1c2c2c2c0c2c2c5d1746d1347c7d47cbd42d0b6aaaaaaaaa9a45c1704c1305c3c05c3c02c0b105c88 25 33554431 10 1023
def hc_67_12 : Nat → Nat := unpackHintV5 0x83687b9f2336e78bc7a1d3a1ea6f2cb79ace1fa6584b698831bc5d1c9e165f1d0548c9e13d529c4b4482121517845446210771b43e746d0eec16238d45b8e2701c35b05d8c402582bf8a10ac906a27c86b87f14021a84a805c21be0f64f482de1f60440e70000220 0x4cfcfc5c4c5cfc4cac4cad69542c2cfccc2c2c4ccc2c2cac2c4c2d552b52b55553b8ee551337561382e3b954ed2f0bc130f0130f01304c0b0bc513f204c1f1f1f1f0727070707170707a81c0c1c5c1c1c1c0c1c1c1c4c1c1c1c6c1c0c1cac1c1c1d7c1c1c1ccc1c0c1cac1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1d55555555541d41d559b0781e87e9b0707a0707070703a0703a0781e551f07c1f07c07070070f0070f0070700701c448070acacacacacac5cac5cacaea0b0b2b0b2b0b2b2b0b0b2b330b0b52b4ad2b2b52b50b53b8ee8ae9b2b2ba2b2b470b8ee63b40ac2b0ac3c0ac3c02c1082300c0eaa80c5c5c0c6c4c6c6c0c0c0c0e0b0703aa0707a070b070b0345d1b2f51b1b51b46d0b41daaaaaaaaaa0b9a40c1706c3c06c3c06c1b02c07107c88030b0b0317170303131f1b1f13031b0b0b0b9b0717030b07170b072b0b070b0b0345d03335334f51f4dd0b41daaaaaa87e9baaaa0b9a603a85ea038ceaa33aaa03a0b82ea078ce96a5a80c1700c3c07c3c07c1f02c07107c88a083c02c2eaa81c0c1c1c5c4c5c5c5c5c5c5c1c0eaa81c5c2e0b0b070b070b1b1b51b2f51745d1b46d0b41daaaaaaaaaa0b9a45c3c05c3c05c1705c1702c07105c880b0b0b171713370717071317171b2b1717171707170b07170b0b0b0b0b9b070b070b174f5071751745d1f4dd0b41daaaaaa87e9baaaa0b9a617aaa0785eaa17a85ea07a0ba81e96a5a85c3c01c3c05c1705c1702c07105c88a083c169540c5c5c0c6c4c6c6c0c0c0c0c0c2c5c0c6c1c2c2c6c1c2c2c6c2c6c2d5555555556aaaaaa6aa9540c1706c3c06c3c06c1b02c231122150317170303132b1b3713031b030b170303330b0b2733030b270b270b566d17545d5555aaaaaa8ae9baaaa95603a85ea038feaa4faaa03a0ba89e95556a0305c030f0230f02308c0b08c4488a083c169546c0c5c5c5c4c5c5c5c5c5c5c6c1c2c2c6c1c2c2c5c2c5c2c6c2c6c2d5555555556aaaaaa1b6aaa1b9545c3c05c3c05c1705c1702c17112215171317171713171b1717171717330b0b17170b0b170b170b2b0b370b45d45d559b5555aaaaaa8ae9baaaa95617aaa1785eaa17a85ea47a0ba8ce95556a170f0170f01705c1705c0b05c4488a083c09c7cdc7c1ccc9c5c1c5c9d6c1c6c7c4c1c4c7c6c1c2c1c2c1c2c1c2d5555542d42d559baa87e9baaaaaaaa0b95627a85ea07a3397eaa078ceaa0b82ea078ce95556a1f07c1f07c1f0f0070f00b01c4488a083c2a033717173703033717171b370317030b170303330b0b2733030b1b0b270b0345d033f5433f51b4dd0b49daaaaaaaaaaa690305c030f0230f01b08c0b08c4232202c2c4c6c4c6c2c2e6c5c2c5c2c6c2c0c5c5c0c0c6c0cccfd2ccc6c6c0ccc0d40d0b07070b554de6a99643c0f03c0f02c2c5c4cdc5c4c5c6c6c5c2c5c2c2c2e6c5c6c6c1c5c1c1c5c1c5cfd2c0c5c5c0d40d0b07070b554de6a99643c0f03c0f00c0c6c0c0c0c0c0c0c0c6c2c9c2d55555540c0c0d540c4d40c2c0c0c0c1c0c0d5556aa6aa95569540c0306c2302c231100c0c00c3c220dc6cdc6c2c2c6c2cdc2c6cfcfc5c6c5cfd546cdd42c2cfccc6ccc2c2d5554dd5566aa6aa969556548c2306c2302c2308c3c06c3c11220dcacdcac2c2cac2cdc2d4ad3742d6aa2ba6eaaaa69aa17a91e82ea33a5a96a2308c2308c0b08c423222820f003370355545c4c4c5c0c0c5e3703542c0c1c2c1c2c0c2c9c0c0d540d0340d552703030380e0380e0f03c030bc5cc0c404bc0c4c0c00f130f1703031784c0c00b03070b070b030b1f03543d034bd030303030380c3e80e0380c0300c030003c0f0337171737030337371717a3780c5c0c2c2c5c0c2c9c2c9c2c0ccc2c2c9ccc0c2c0d45d4ad3740cfd4fd42d2740cee033b80e0380cae80cae80e03980d0305c2b0dc030f00f00b09c4200c0303030303030303030303030303a0380c6c0c0c1c0c0c0c1c1c1c1c0c1c0c0c0c0c0c1c0d0347d3740cbd40c0d41d0740e0380e0380c0e80c0e80e070303980d0300c1f07c030f0030300701c41f200c03546e86d41d035540e0383c0f00d5030303030303032f032f0303033f03131b131ba50741c0c0c1c0d0340d2f555070380e03030387e9b07030f03c030f2f00c0c11f0303030303030303030303030303330303030303033703030333030303030303031b03130303a80c0c1e6c0c0c0c0c0c0c1c0c0c1ccc0c0c0c0c0c0c1c2c1c1c1c1c1c2c0d0340c0d40d40d40c0d47d3741d0740e0380c0e80c0e80c0c0c0c0ea1fa6c0e070303980d0300c03030030f003030f0030300c07c1f01c07107c80300c5c5c0c0c0c1c2c1c1c0c0c1c1e81e071703030707070303079b0707070703030303070707070345d1f4dd072f5070750741d0380e03a03a0303a0303a0381c0c1e60340c1705c1701c3c01c1c01c07105c80302d50703033f07570703032f072f07170717131b131ba03541c1c1c1c1d45c1d2f5553741c0e0381c1c1e1fa6c1c1e43c0f01c3cbc07070007070b0307033707070717030703170707070307031703070317071307070707071b03171703a80c0c0c0c0c1c1c0c0c1e6c1c1c0c1c0c1c1c1c1c1c1c1c1d41c1d40d1741d40c1d47d3741d0740c0e80c0e80e0380c1c1c0c1ea1fa6c0e070307980d070f0070700305c07070f0030701c05c1701c07105c80300c0c0c0d540c0d40c0e80e031b03030303270b270b030703030303030b555555555550380e03980c0e80c0e80e039540c030ac3700c3c00c0c02c2711200c540c0c0c0c0c0c0c0c0c0c0cdc0c0c0c0c0c0cdc0c0c0cfc0c0c0c0c0c0c0c6c0c4c0c0ea030303030303030b03070303032703030303030b270b270b566d03540d40d3f555555550380e0303a0303a0303030303a8ae9b0389c0c0e550300c03030030f003030f0030300c0ac3702c2711200c0317170303035551717a1785c5c0c2c5c0c9c2c9c2c9c1c2c2c9c1c2c2d035559b555555550380e032b98ac0c0e80c0e80e03479540c1705c1705c3c05c3c02c1711200c 26 67108863 11 2047
def hc_67_13 : Nat → Nat := unpackHintV5 0x8414454044719ee34fcf1c1567554e337d8b49a9a548cc82146231042f3c7716ce340b0019c53e108283070134335492f1ca45d4e921a6510fa94a8737a7436ccbc17a6f00a9f4d04ea9941ff5d80e087c85516cc22c1f20a61c003587600cf37400019e 0x31b4b039b9b9b86c6e0b87d6c7e5b82c7c4c5c4c6c6c0c5c5c5c5cac0d69556c2c5c2c6c2c4c2d2c1c2c2d2c1c2c2d55544d555555a9aaaaaaaa551705c1304c230f0230f00b08c44881317131b2b03171717171b03542c5c2c6c2c4c2c6c9c2c2cac9c2c2d5559b44d513556aa17a6eaaaaaaa9561ba1b8aea2baa1b8aeaa2baaa0ba87e95556a1705c1304c1b0f0230f00b08c44820a083c00d5130b130b03030303555555aaaa80e9baa956aa13a6eaa80e37aa95569b6a1304c0300c0b04c44820881303131713131303131313135a55530b170b13070b0b13070b0b130b130b5555555555a9aaaaaaaa551304c130f0130f01304c0b04c51132204c0c4c5c4c5c4c4c4c0c4c4c4c4c4d5530b170b13270b0b13130b0b130b130b5544d44d559b55aa85e9b84e47aaaaaaaa5591e84eaa84e37aa84e2ba84e37a82ea33a55558fd6a1304c130f0130f01304c0b04c51132082820f0271717270703171707172703072727130713272b070b070b070b070b5555550b50b5566eaa17a6eaaaaaaa95607a1fa96ea2797eaa078ceaa0b82ea078ce955563f5a85c1708c2308c3c01c3c02c07112082820f0039b030303039b9b80c0c0c0cdc0c0c0e6c0c0e6c9c2c4c2c0c0c0c0c9c0c0d9b0366cdd1340c0d034f42d2769ba9baaaaaaa9a40c0304c1300c0c030f02c17105c8803030303030303030303376303131303030303030303031b13030303a030b9b0303030b2707070b070b0b0b270727070b0353d3f4dd5b37aaaaa0303c0f03c17170717132727030717070327372707270b070b0b82c2c1c2c2c1c4c2c9d174dd1341c9d274f42d076aaaaaaaa9a45c1704c1301c3c230f02c07108c8850303030303030303375703131303030303030303031b13030303a030b2703270b270b272759b0340d555a9aaa0303c0f03c17171317132b2b0317171b032b372b5b0b170b370b130b1b270b2b270b5555544d55a9aaaaaaa551705c1304c1b0f08c3c0b08c44881337171713173747133717132ba82c5c2cdccc2c2c4ccc2c2cac2c4cdc2d174dcfd44cdd4ad133742d5b6aaaaaaaaaa9a45c1704c3c04c3c04c8c132302c23108c88030303139b03031703030b2703035551b13131b030303033f4b032f2f0303030b1f1f0b03566d1355034bd49e6a80e4799640c0f03c0f1170303032b1303030b9b0303030b270b03540c0c0c0cfd2c0cbcbc0c0c0c7cdcdc7c2c1c1c2c0d0340d554fd079aa6590303c0f03c45c0c5c5c0c2c2c9c2c2c2e6c4c2c4c2c1d51b13131b072707273f4b272f2f0727070b072707070b0b0b2751355274bd41e6a99643c0f03c0f1234b17170b170b0b4b0b2f3b5552f2b3f372f373f2b0b0b3f332f330b0b4fd5554fd553f59a9aaaa5a555951705c2308c0b08c230f0230f051232205c5c2c5c2c2c2d17542d6aa17a6eaaa9a647a2baaa0ba8ce96a5a85c1708c2302c23108c820a083c00cacac0c5cac4c0cac0c5c4e1317a030b170303330b0b2733030b270b130b0345d033f54b3f52b44d0b49d033b80cee0337a033ba0380e0380e60340c1700c3c04c3c04c1302c271080300c0c0c0c0c0c0c0c0c0e80c4c0e0303030303030307030703030303030307070707070b03035031350340d1344d0741d0303a0303a0380e0380e0380e60340c0c00c3c00c0304c1301c07104c80300d5131b131b030303033f03130303032f0313030303a50740c1c1c0c0d03555070380e1fa6c0e03030f03c0303c47c0c0c0c0c0c0c0c0c0c0c6c0c4c0c0c0c0c0c0c0c0c0c0c0c0c0ccc0c0c0cac0c0c0c0c0c0caea0303079b0303030303030707070707070b03030307030703030340d030350351f47d030350350741d0380e0303a0303a87e9b0303a0303030380e60340c0300c0c00c3c07c1f00c0c00c3c01c07107c80300c0c1c2c1c1c0c0c0c4c4c0c1c4c1e0707a030707030303030307070707070707070345d07135070751344d0741d0380e0303a0303a03a03a0380e60340c1301c3c01c1c04c1301c07104c80302d5131b131b2f07130703033f071307030317071707a03541c1c1c1c1d45d1f55074bd41c0e0387e9b0781c1e43c0f01c0f001c1c2c1c4c1c1c1c1c1c6c0c5c5c0c1c1c1c0c1c0c5c1c1c1c5c0c1c0cac0c5c0c1c0c5c0c1ea030303030307070303079b070707070307070707070307075070750345d1f47d030750750741d0303a0303a0380e87e9b0307a0307070380e60341c3c01c1c00c1705c1700c1c01c3c01c07105c80300c0d5540c0e80c4c0e030303030303030b0307030303030303130b130b55555555550303a0303a0380e60380e039540c0c00c3c00c0304c1302c1311200c540c0c0c0c0c0c0c6c0c4c0c0c0c0c0c0c0c0c0c0c0c0c0cfc0c0c0cac0c0c0c0c0c0caea030303030303030b03070303270b270b0303030b03270303566d03540d555555550380e0303a0303a8ae9b0303a0303030380e550300c03030030f02b0ac03030030f00b09c4480300c0d5540c4c4c0c4c4c4e1313a030b170313070b0b13070b0b130b130b55555555550380e0303a0303a60380e039540c1304c3c04c3c04c1302c1311200c545c4c5c5c5c4c5c6c0c5c5c0c5c5c4c0c5c0c5c5c5c4c5c0c5c0cac0c5c0c5c0c5c0c5ea17070b0b17070b0b030b1703270b270b032b0b0b2733030b40d40d559b555555550317033ba030385e80e03a2ba6c0cae80cad1c0e039545c3c05c3c00c1705c1700c3c05c3c02c1711200c03030303030303031b55503030303270b130b0303030b030703035555555555503a03a6039540c0d40e039540c0304c1300c0c00c3c02c2711200c030303030303030303033f67031313030303031b13036503079b0303030707070707070b070b070b550347d0380e5035030303c0f03c47c1c2c1c4c4c1c1c1c1c1c1c1cfe0c0c5c5c0c4c1c1c6d940c0c0c1c0c1e6c1c1c1c1c1d2f5540d1f40e03940d40c3c0703c0f117 25 33554431 10 1023
def hc_67_14 : Nat → Nat := unpackHintV5 0x8278e63fdc581eb84d8ebf27474dc4738d6661a7b7c0c99a905d5ddc2cec70959d364a4c20a4e7cf923c4de914427889a020445c1d201c848ff20707dd0703829b018a6db8b4f4104ecaec2185780ddeb905ef400243ad00ed8d1058c7801485f8000290 0x3171703030b1703270b270b5503175032b3f3703373f2b030b273303330b0b55175555599aaaaa5a555950305c1705c0b05c170f0030f0448817171717170b170b0b0b1745d50b585e9baaaaaa6985e8aeaa82ea33a5a96a1705c1705c0b05c417222820f01717a1784c5c4c5c5c4c5c5c4c5c5c5c2c5c2c4ccc2c2c6ccc2c2c6c2c2c4c2c2c5d1744cdd46cfd46d1342d5b45e1784cde84cee84cee133782e1b986d1705c130f0130f01304c0b05c417204c0703a0781c0c5c5c5c5c1c2c1c1c1c0c1c2c1c1c1c1c1c1c1c0c1c1c1c1c1c1c1c1c1c1c5d1741cbd41c1d46d1b41d0741e0781c0e81c0e81e0781e07981d1705c070f0070701705c0701c417201c03a031b5541d1b5541c5c0e039070f03c45e86c1c1c6c1cbcbc0c1c0c0c1c0c1cfc0c5c5c0c2d50707070750741d2f5545d1b41d41c1c1c1e17a6c0e039070f01c0f03c45ea071b07070707071b1717171707070707030717070307170707072b0703070707170703070b0707070733070707070707070b07070707070b070b079b07070707070707075070751745d1b46d070750750741d0707070707a85e9b0781e0703a0703a0781e60741c3c01c1c05c1705c1701c1c01c3c01c07105c80704c5c4c5c1c0e81e07030703070b0707070b070707070707070707070b079b07070703070707071745d1b44d072f5070750741d07a07a0781e0703a0703a0781e60745c1704c1301c3c01c1c01c07105c8072a0707073307030717070307170707070703071707070703071307070707071f1317131707070b07070707070707070707070707070707070707070b079b075070751745d07635070751b44d0741d0707070707a85e9b0703a0703a0781e0781e60741c3c01c1c05c1701c3c01c1c04c1301c07105c8071944c6c4c6c0c1c5c0cbc1cbc1c1c1cfc1d5c1c1c1c2c1c1c2c1c1c1c1c2c1e6c1c1c1c1d170746d55074bd0741d50380e41c3c0f01c0f11765031707030707073f07570707072f072f131b131b070b07070707070707070b079b45c1d074bd551b41d07540e039070f03c0f01c45d69545c5c5c5cbcdcfcacfcdcbcac5c2c5c2cbccc2c2cfccc2c2c2c2d545d45d4fd550b551798bced554ee3b82e3b954ed1705c170f0170f01705c0b05c5117205c1703a1785c0c5c5c5c5d545c0d45c2c5c2c6c1c2c2c6c1c2c2c6c2c6c2d55555555545e61b03a1b03a1b86e0b86e551705c170f0170f01705c0b05c448172a171b17171717171b1717171717171b170317171703171717171b2b1703171717171703545c7c2c2c5c5c2c2c5c2c5c2c6c2c6c2c6c1c2c2c6c1c2c2d174fd55555559b46d51b5545c5c6c5c5ea17a6c6e1b86c0e86c0e82e1b9545c3c05c3c05c1705c1705c3c05c3c02c1711205c13171317513a1313170313542c4c2c7c2c7c2c4d1b13566d545e13a6c4e1384e1384c1303c0f1130b0b079b13170b070b3f66c4c5c4c5c4c0e85e17031703555170b170b1b0b130b070b0b070b0b5546d555555545c5e985e9b1384e1b03a1b03a0b86e551705c1304c170f0170f00b05c5117204c030b0b070b079b1307075b17171f0b1f0b0b079b9ba84c5c4cdc5c0c5c5c4c0c4c5c5c5c4c0c5c5c4c5c5c0c4c4c5c5c4c4c5cac4c5c4c5d517330b0b17170b0b170b170b070b0b13070b0b1b0b130b55555546d46d559b551717471717a85e9b1303a1303a1384e0b86e55170f0170f01705c130f0130f01304c0b05c5117204ca81d6c1c1c1c1c1c7c5c5c5c5c1c1c1ccc1c0c1c5c1c0c1c5c1c1c1d7c1c0c1c5c1c1c1c0c1c1c1d7c1c1c1c6c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1d55555555541d41d559b0707070707a85e9b0781e0703a0703a0781e55070f0070701705c1705c070f0070700701c448072a1717171717172b1717171717330b0b17170b0b170b170b0b0b175171751745d50b51717471717a85e9b3b8ee0b8ee63b45c3c05c3c05c1705c1702c17105c81700c0c0c0c0c4e6c0c0c0c0c0c0c4c0c0c0c0c0c0c0c2c0c9c0c0c4c2c4c2c0d0340c0d40d2d44d1342d276aa03a6eaaa0391eaaaa9a603a038deaa038aeaa138aea138dea0ba89e96a4b5a80c0300c0c00c3c04c1302c13104c820a083c00c0c0c0c0c0c4e6c0c0c0c0c5c0c0c0c2c0c0c0c6c2c4c2c0c0c0c2c0c9c0c0c0d40d46d1340c0d40d3d42d276aa03a6eaaaaa0391eaa9a603a1b8aea2baa038aeaa0391eaa0ba87e96a5a80c0304c1300c0c00c3c02c17105c820a083c00c0c0c0c0c0c0c0c0c0cac0c4c0c0c0c0c2e6c0c0c0c0c0c0c2c1c9c2c1c2c2c0d0340c0d40d3d55342d076aa03a6eaaa0391eaaaa9a603a038ceaa0382eaa1faaa0b82ea078ce96a5a80c0300c0c00c3c05c1702c07105c820a083c04c5c4c6c1c0c1c1c5c5c9c0c2c2eaa81c9c2c1c2c2e0b0b07130baa0707a2745d1b44d27275272f50b41daaaaaaaaaa691705c1304c230f0230f00b01c4232204c5c4c6c9c0c1c5c5c5c1c0c2c2c2c1c9c2c1c2c2c2c2c2e6c1c4c2c2c1c4c2c9d1746d1341c9d49d3d42d076aa17a6eaaaaaaa9a607a1b8aea2baa078aeaa27aaa0ba81e96a5a85c1704c1301c3c08c3c02c07108c820a083c00c0c0c0c1c4c2e0b0b030303031344d0340d0b41daaaa80e9baa9a6aa13a6eaa80e33aaa07a6e69a84c1300c0302c07104c820881303131707070703131313130b0baaa070b070b0707aaa070b82c9d1744cbd44c4d44d1342d076aaaaaaaaa9a44c1304c3c04c3c04c1302c07104c880703131713170713130313131313130b0b0b070b070b07130b07130b0b0b0b0b9b2745d134b5071351344d0b41daa85e9baaaaaaaa6981e84eaa81e33aa84e2ba84e37a82e0ba81e33a5a92d6a1304c130f0070f01304c0b01c4132082820f0540c0c0c0c0c0c0cac0c4c0c0c0c0c0c0c0c0c0c2c0c9c0c0c9c2c9c2d59b40d50355556aa03a6eaaa0391d6aaa95603a038ed5555562baaa0ba89e955563f5a80c0300c0c00c3c05c1702c17112082820f0 25 33554431 10 1023
def hc_67_15 : Nat → Nat := unpackHintV5 0xecb3b4e71168e1e14cd51334cf596ec93988c3417ebd0190b6b194af61d4a799f299f36a95811c8da9f68ce8308ae88086d90479236e6b5b726429cc5ca9e0513adc4bb16243f1f038b2d031c1bc27ea762391161c79c6121a9808227e000208 0xa81c0c1c5c1c1c1c0c1c0c1ccc1c1c1c1c1c1ccc1c0c1cec4c5c4c6c1c1c1c7c1c4c1c1c1c1c2c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c2c1e6c9d1741c1d41d41d8d41c1d46d1341d07617a6c1c1e81c1c1c1c0e81c0e81e0781e07981d1705c07070070f0070f0070701304c0701c4200700380e1b031ba84c0c4c0c0c0d40c0c0c0c0c6c4c0c9c2c9c2c0c2c1c0d5566c0d0340e03980e03030f03c0303c03544c0d0d5555a0303030303131303070b070b030b2703555550380e03a6c0e03030f03c03130303c0a9555aa5555030303030303032b0303030303031b030303030303030303030b032703030303030b03070303270b270b566d03555540d3f540d555580e9b0303a030303580e80c0c0cee80e0380e039540c0c031700c0c00c3c00c0c00c3c05c1702c171120030653f036ba8bc0cbc0c0c0c0c0c4c6c4c6c0c5e6c0c0c0c5c7c2c7c2c0c2c1c0c0d0355540d0380e40c3c0f00c0f1944c6c4c6c0c0c0c5e6cfc0d2ea2f032f030303030317031f0b1f0b030b07030340d5550340c0e80c0cee40c3c0f00c0f194fc0d6ea2f032f0303030303371f371f031b4b030707070703079b03030307070b0340d5550340e039030f03c0303c65131b131b3f075b0707072f072f070707030717030b0707070707070b0b079b070707070749d5550740e039070f03c0703c650707072f072f0707073f076303170703131b131b070b07070707070707070b079b0749d074bd5550740e039070f03c0f01c5a553f372f2b2f373f2b17173f330b0b2f330b0b0b170b0b0b4ed4fd555555545c5d585e3b8ee0b8ee553b4bc3c0bc3c05c170bc2f02c2f11208c1717a17171b86c0d5546c5c5c6c6c1c2c2c6c1c2c2d0c2c5c2c6c2c6c2d55555555546c0e85c0e985e1b86e0b86e551b0f01b0f01705c1b06c0b10c4481b2a1b17171b1b1b1b1b1b1b1b1b1b03171717171b031b031b3b1b1b1b2b1b1b1b1b031b2b558c2c5c2c6c6c2c2c6c7c2c2c6c2c6c2c6c1c2c2c6c1c2c2d55555559b46d51b55617a6c5c5e85c5c5c6e1b86c0e86c0e82e1b9545c1706c3c06c3c06c1b06c3c06c3c02c4f11201b013171353584c4e131b0313542c4c2c7c2c7c2c4d13566d5684e1384e1384c1303c0f1131317131b4385c5c4c4e86c0d5550c2c5c2c6c2c4c2d0c1c2c2d0c1c2c2d5555555555a17a1384e1703a1b03a0b86e551705c1304c430f0430f00b10c4481300c2c2c1c2c1c1c4c1c6c7d6c6c2c2c7c2c1e6e6c1dee84c5c4d4c4c4c4d0c4c4c4c6c4c4d5ec2c4c2d44d13566e174784e031304c44c2a1303171713175303130313374743134313371b03473b1317131b13131b2b13131b2b554c2c5c2c6ccc2c2d1ccc2c2c1c2c2c4c1c2c2c6c2c4c2d5555551b51b5566d5617a6c5c5e85c5c5c4d1c0cee84c0ea1384e0b86e551705c1b0f03b0f0130f0130f01304c0b13c5120130a89c5c5c9c1c1c1c7c1d6c1c1c1c0c1c5c1c1c1c0c1c0c1ccc1c1c1d7c1c1c1ccc1c0c1cec1c1c1d7c1c1c1c6c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1d55555555541d41d559b85e9b0707a0707070781e0703a0703a0781e551705c07070070f04f13c070f0070700701c44801c2a17173b47472b473b2b0b170b3b330b0b47330b0b0b0b45d3b47547550b585e9b1717a1717173b8ee0b8ee63b45c170ec3c0ec3c002c10808c00c0c0c0c0c0c0c0c0c0c0c0c0c0eaa80c0c0c0e0b070baa0303a0340d1b44d032f5030350b41daaaaaaaaaa690300c1304c030f0030300b01c4172204c5c4c5c5c0c1c5c5c5c1c0c2c2c2c1c5c2c1c2c2c2c2c2e6c1c4c2c2c1c4c2c5d1746d1341c9d49d3d42d07617a6eaaaaaaaaa9a607a1ba89ea078aeaa27aaa0b82ea078ce96a275a85c1704c1301c3c05c3c02c07105c88a083c00c0c0c0c1c4c2e0b0b030303031344d0340d0b41daaaaaaa69aa03a03aa80e69a84c1300c0302c07104c88880303030303030303030303030303aaa030303030303aaa07130b82c2c0d0340c0d40c4d44d1342d076aaaaaaaaa9a40c0300c0c00c3c04c1302c07104c880703131713170713130313131313130b0b0b070b070b07130b07130b0b0b0b0b9b1745d134b5071351344d0b41d85e9baaaaaaaaaa6981e84eaa81e33aa84ea13a82ea07a5a89d6a1304c130f0070f01304c0b01c413222820f00303030303030303030303035a55030303031b0b130b030703030303030b55555555559aaaaaaaaa550300c1304c030f0030300b05c4488131713171703171717171703545c2c5c2c6c2c4c2c6c9c2c2cac9c2c2d5559b44d51355617a6eaaaaaaaaa95617a1ba8aea1b8aeaa2baaa0ba87e95556a1705c1304c170f0170f00b05c4488a083c00d5130b130b03030303555555aaaaaaa55aa03a03aa9556a1304c0300c0b04c4488880303030303030303030303035a55030303030303030b03070303130b130b555555555580daaaaaaaaa9540c0300c0c00c3c04c1302c13112204c0c4c5c4c5c4c4c4c0c4c4c4c4c4d5170b170b13270b0b13130b0b130b130b5544d44d559b5585e9baaaaaaaaaa5585e84eaa84e37aa84ea13a82ea33a5555a84c1304c3c04c3c04c1302c131444c88a083c05c5c5c5c1c0c5c5c1c5c5c0c1c9c9c4c1c4c9cac1c2c1c2c1c2c1c2d5555542d42d559b85e9baaaaaaaaaa5581e87ea27a89e5faa81e33aa82ea07a5555a85c1705c1705c3c01c3c02c0711222820f00317031703170317031717131703a80c2c5c0c9ccc0c2c0ccc2c2c9c2c4c2c0d174dcfd40cdd4ad1342d276aaaaaaaaaa9a40c1704c3c00c3c04c1302c17105c88 24 16777215 10 1023
def hc_67_16 : Nat → Nat := unpackHintV5 0x80cc073fdc229f52270fa181e7c502f3dee0e9ee3050f5307a778cc3396c969bfa2f0d2eb3a664cca2f70ed95dd76c9f93d647f5f522506a906730473b3e23690d2177ef28ab94184cfa3422f8e10fa47607142f8295bd20fc53a06246f8134778000268 0x3a80e903541c2c1c2c4d5517aa6ea43c0f113131313131354cc2ccc2d44d5553aa84eaa47940e0385e1780d50380eaaa0b89e55a0f03c44e03c86c0e1b84c4cce6ccc2e6e371f99e0366d86c0e1782c7c4c5c1c0e6c4c5c4c4cae6cbd9b47a3785e030b1fa03171343130313030313034313431313130313031313131351f0b1f0b270b130b551344d59baaaa913130f03c1304c44c4c4c4d0c4c4c4c4c4c4c4d50b0b137b0b0b13130b0b130b130b5544d44d559b55aaaaaa138dea84daa555aa17a84e3b84d5560ba8ce95556a1304c13130131301304c0b04c5113222820f0030f030f130f1304c4d004c4c3c3c3c000013543c2c4c2c7c2c7c2d501544c4c0e0384e1383c0f00f000f03c03c43c131313171313130f130f0f0f130f0f00131313135540007c2c5c2c4c7c2c2c4c4c2c2c3c3c2c2c3c4c2c2c4c2c4c2d551350f43c0001135566d544c4c4c4c4c4c4c4c4c4c4c4c3c3c3e0f130f84c4c4c4c2c4c4c2d540f000003c0f003c000f0003c00103c03c00dc5cdc5cdcacdcad50b0b330b0b37330b0b2b0b370b554ad4ad559b5547378dd1e2b37372b0b0b5500f0370f02b0dc0b051007c7c7c5c5c7e6c5c5c7c7c5c5c5c7c0c5c5c5c5c9c0c7c0c1ccc9c9c9d7c7c9c1ccc9c0c9cdc7c9c7c4c7c4c7cac2c2c2c2c2c1c2c2c2c1c2c2c2c2c2c2d55555555542d42d559b2717172727072789c1c9e1f27271f27031f87c0c9e0b0b0b0b551705c1f0f01f0f01f07c1f0f01f0f00b02c441f07c17171f9b17171717171717171f1717171717171717171f1b1f1f1f1f1f1b1717071717171f5f17170733171717170b0b0b0b0b0b0b0b0b070b0b0b070b0b55555555550b50b5566c5c5c5c5c7c7c7c7c5c1c5e17071787c6c7e1f1b1f82c2c2c2d545c1705c1705c3c05c3c05c3c05c3c02c0b1105c1705c5c5c5c5c9c5c5c5c5c5c5c7e6c5c5c1ccc5c4c5c5c5c4c1c5c5c5ccd7c5c5c5c5c5c5c5c5c7cac7c4c7c4c7cac2c5c1ccc2c2c2c1c2c2c2c2c2c2c2c2c2c2c2c2d55555555542d42d559b17071785c1c5e171717171f37271f27471f87ccc9e0b0b0b0b55170f0170f01705c1705c170f0170f00b02c441705c1f1f171717171f9b1f271f1717171f03171717171f031f1b1f1f1f1f1f1b1f03072b1f1f1f5f1f1f07331f031f2b0b0b0b0b0b0b0b0b0b070b0b0b0b0b1f07330b0b5555555551f4fd50b50b5566c9c5c5c9c7c7c7c7c7c1c7e1f071f87c0c7e1f031f82c2c2c2d545c1707c1f07c3c07c3c07c3c07c3c02c0b1107c1f0cccccc5ccc5ccd7cccaccd7cccccccac2c2c2c2c2c2c2c2d5555542d42d559b3347338ccccce0b0b0b0b5500330f0330f00b02c440a03540c0c0c0cfd0c0cbcbc0c0c0c0cac4c0d44d030b2703070b070b035540d44c0e9b0380c0c0e0380c5c0c0f03c0f02a0303030303032baa0380e030303370303179b03030303030303032b2b030313370303030317030303030303030b032703030303030b030703031b0b130b0340d03035035030350351b44d0b49d80e9b0303a030303030380e80c0c0cee80e0380e03980d030300c5c03030030f003030030f01304c0b05c41720030a031b1b0303540c0c0c0cfd0c0cbcbc0c0c0c5d5030b1f03070b070b0340d035546d0352703a6c0e03030380e40c0c0f03c0f1170a80c0c0c0c0c0c5e6c0c0c0c0c6cac0c0c6c0c0c0c0c0c0c0c0cdea80e0380c0c0cac0c5c0c0c0c0c0c0c0c0c2c0c7c0c0c6c2c6c2c0c0c0c2c0c1c0c0c0d0340c0d40d46d1b40c0d40d42d27603a6c0c0e80c0c0c0e0380c0e03a0303033ba0380e60340c0300c0c00c3c05c1700c0c00c3c02c17105c800c00c0e9b039b039b03031b030303031b0b130b03030303030303031b44d0340d0340d0b49d0380e03a6c0e9b030380c0e0380e60344c1300c0300c0302c17105c80305c5e84c5c6e133737133717131b1b330b0b13330b0b0b170b1b0b130b1b3f51337545d1b44d0b56d1317a1317a1b85e133b84cde0b86e61b44c3c04c3c05c1704c1302c1081300e0386c0c6ea130313030303030303030303031b130307070707070b070b03079b03030307070b3f4dd0356d0380e0380e03030f03c0303c0303030313031f0303030b030b030303a030303030313130307070707070b070307070307079b070b3f44d0352d0380e03a6c0e03030f03c0303c0a03540c0c0c0cfd0c0c2c2c0c0c0c0c7d6c0c4c6c4c6c0c1c1c0d41d035540d41c0e9b0380c0c0e0380c0f03c0f1170a80c0c0c0c0c0c2ea80e0380c0c0c2c0c0c0c0c0c0c0c7c0c0c0c0c0c0c6c0c0c0c0c0c1e6c0c0c0c0c0c0c0c0c1c2c0c0c1ccc0c0c0c0c1c1c1c1c1c1c2c0d0340c0d40d40c0d40d58d5341d07603a6c0c0e80c0c0c0c0e03a0303033ba0380e0380e60340c0300c0c00c3c00c0c00c3c05c1701c07105c800c01c1e81c5c1e0703070b070b07071b17171b070707070707070307070707070b0707070707075072f52745d1b46d0741d0703a0703a0781e0781e0781e60741c1c01c3c05c1706c1b01c07110c807281c6c6c1c0c5c5c0c0c1c0c1cfd0c1cbcbc0c1c0c2d50707070750749d0741d551b41d41c5e9b0781c1c1c0c0e033fa41c1c0f03c0f13f0a86c5c5c6c1c1c1c6c1c6c1c1c1c0c1c1c1c5c1c0c1c0c1cec1c1c1cac1c1c1c1c0c1cac1c2c1c1c1c1c1c1c2c1c1c1c1c1c1c1c1c1c2c1e6c1c1c1c1c1c1c1c9d1741c1d41d46d1b41c1d41d41d07617a6c1c1e81c1c1c1e0781c0e81c0e81e07981d1705c07070070f01b06c07070070f00701c4200701317131b0781c5c1c1e81c0c1c2c1c1c1c2c1c1c1c1c1c1c1c1c1c1c1c0c1c1c1c1c9d1746d1341cbd41c1d41d0741e81e81e0781c0e81c0e81e07981d1705c1304c070f0070700701c443201c 25 33554431 10 1023
def hc_67_17 : Nat → Nat := unpackHintV5 0xad8bc6a661ca9e5a0295ca2488535e86488284d05e777b5672514a69fa166559285c4a444d0bd047b95447900a47900047680a46304e46300046300045c81a3d222a2dd3d42641e4182b861149b810b8240f106a0e80240c887e005b0c000016 0xb0b0b17171f1717171717171b2b1717171717171f170717171707171717171b2b1717171717171717542c5c2c2c5c2c2c2c2c2e6c2c2c2c2c2c1c2c2c2c1c2c2d55555559b47d51f5545c6c5e17171785c5c5c5c7c7c7c7c7c1c7e1f071f82c2c2c2d545c3c05c3c05c1705c1705c3c05c3c02c0b1105c170acacacacacac5cac5cacad50b0b2b0b2b0b2b2b0b0b2b330b0b55566d2b54ad552b2b2b2b2b2b2b8ad1cae0b0b5502b0ac2b0f02b0f00b0440033745c4c0c4cdcdc0c2c5c0c0ccc2c2c9ccc0c2c9c2c4c2d5537555540c0c0c0c0cdc0e033b0380c4c0c4c0c4c0c2d540c1700c3c04c3c04c1302c271104c0300c0d031340c0c0d55540c0c0c0c9c2c4c2c0c0c0c2c0c1c0c0d555555555540c0c0c0c0c0c0c0c0c0c0c0c0e03030380c0c0c0d540c0304c1300c0c00c3c02c171100c0304c5c4cdc4c5c4c5c5c5c4c4d131317544c4c4c5cdc5c5cad5545c2c5c2cdc2c2c4cdc2c2cac2c4c2c5c5c2c2c5ccc2c2d5552b52b5566d5555545c4c4c5c4c4c4c4cdc4cdc4d0c4c4c4c4c5c5c4e17471382c4c2d545c1704c5c04c5c04c1305c3c05c3c02c171445c1304c0337170b0b0b1317170b270b1f0b9b2f40c4e130380c5e9b13031b1313031337171713171337131317131355131313171717171717555530b170b37270b0b13270b0b2b0b130b53330b0b330b0b5554ad4ad559b555555531313171313130313371303131313131353471391c4e0b130b551705c130133701304c2f0f02f0f00b0bc513f04c1300c4c0c00f130f17030317540270b0f0b030b1f035555503030380e030303030303c0300c030003c403033717173740cdcdc5c5d5540c2c5c0c9c2c9c2c0ccc2c2c9ccc0c2d555555555540c0c0c0c0cdc0cac0cec0e033b0380c9c0c2d540c170ac3700c3c03c02c27110030dc2c5d4d42c2c4c2c7c7c0c6d50b0b0b0b0b0b0b0b1f47d59b5537371b86e1f07c0f03c47cdc5c5c7c2c0c2c2c5c4c2c0c7c0d5550b0b0b0b0b0b0b0b070b0b0b070b0b5555555555531717531f37371f67035394c0d9e0b0b0b0b551705c1f07c1f0f01f0f00b02c511f07c1f02c2c2cdc0c5c5c5c5d4c0c7c0c4ccccccccccc4cdc7c0cccccdc5c5c7c7c4c7cac7c4c7cad50b0b0b9b0b170b0b0b170b0b3307330b0b0b070b0b0b0b0b2b0b0b0b0b55555547d47d559b55531717531f33338cd1c7e03378dc0e1f37371f0b0b0b0b551705c1f0f01f0f01f0f01f0f01f07c0b02c511f07c1f05c5c5c2d44c2c2c2c5c5c1c5d555170b0b0b0b0b0b0b0b0b1f47d59b1f46d5537371b86e1705c0f03c45e0380c5cdcdc5e1f0b3f40c7c80c2c7c5c5c5c5c5c0c2c2c2c2c2c0c5c1d5542c5c2d0b0b0b0b0b0b0b030b0b0b070b0b5555555555171717171f37371f0380e0b0b0b0b551705c1705c170f0170f00b02c441705c0b0b0b17171337170717171707131717171717171717171717171713371717171317172b2b17171717542c5c2c2c5c2c2c2c2c2e6c2c1c2c2c2c1c2c2c2c2c2c2d174fd5555551f51f5566d545d1c5e17171785c5c5c5c1cde370787cdcdc7c2c2c2c2d545c3c05c3c05c1705c3c05c3c05c1702c0b1445c1705c131317335b0b171717170b544c4c7d50717030b0b0b0b0b0b070b07170b0b13130b070b0b0b1707070b55555513133391e0781e130b0f03c0f03c0b1713273713373727131f131f54cd6c7c5ccc5c7ccc2c2c2c2c2c2d5542ccc2c2c2c2c2c2c2c2c2c4c1ccc2c2d0b0b0b130b0b130b5547d47d559b55555551313130713371307137b131313131f33138cd1c4e0b0b130b0b0b551f07c131f0131f01304c1f0f01f0f00b0b02cbc511f04c1304c4c4c5c4c4c4c5c4c4d944c4c0c5c0ea1313130317030354cc2c4c2c1c2c1c2d555545e1384c4c4c4c4c0c4e85c0c0e50f03c0f03c44c0e130380c0c4c0c4c6c4c6e9b070b9b37030384c0e031307071317131b84c6e6cbd9b1b8dc0c4c0c4c4c4c4c0c4c4c4c5c4c4c4d1ea84c4c4c4d55a550b0b13070b0b13070b0b13330b0b13130b0b130b130b5544d555544d559b55134784e1384e3713130337a131313613131382e1395544c1304c4c04c4c04c3c04c3c04c1302c131444c813280c0e 24 16777215 10 1023
def hc_67_18 : Nat → Nat := unpackHintV5 0xa6b94d516a7ca7a145134c2129315d345fce3a14c6c8fcd3647a98f43b46819bc876cd7b9a26505b630389296337a4a8b23a4cfdd724109b908361477e30e391cb51a6c888c14488512bde2401250e52eb86303e428ea260fe125043aed81223ec000244 0xcdc5c5cdc0c0ccccc5c5c0c2c2c2c0c2c0c2c2c2c2c0c2cac2c2c2c2c0c2c2c2c2c2c0c2c0d174ad3740cfd4fd42d0b40c0c0c0c0cdc0cac0cec0e033b0380c2c0c2d6f0340c170ac3700c3c03c02c0b1000c0303030303030355031350303030355030750b0b42d555555555540c0c0c0c0c0c0e03030380c0c0c0c0c0c0c0d540c0300c0c00c3c0ac2f02c0b1100c030fcbc5cfc5cbcfcdcacdcac2c2d5542c2c2c2c2c2d5542c2d0b554cd55375542d634b634b2f3b3f8fcecbe2b37372b0b0b0b0b53f54bc2f0bc3c0bc3c0ac2f02c0b110bc2f0cccccc5ccc5cccdcacdcac2c2c2c2c2c2c2c2cac2c2cac2c2c2c2c2e6d4cd4cccd4ad3742d0b4cd1cce3333338acdcdcac2c2c2c2d6f40cc3c0cc3c0ac3702c0b100540c0c0c0c0c0cad5555540c0c5e6c0c0c0c0d40c0cacac0c0c4cdc0c0c0c0c5c0c0c0c0c5c0c0c0c0c2c0c9c0c0c0c0c0c2c0c9c0c0c9c2c9c2d59b40d5035555034fd555540c0c0c0c0c0c0e03030380c0c0e03030380c0c0c0c0c0c0c0d540c0300c0c00c3c00c0c00c3c05c1702c171100c0315030303030303179b030303031b2b03032b503030303030337555555031703030303030303030b031f0303270b270b0303030b03270303566d03540d5555540d3f5550303030303030380c0c0e0303030303030380c0c0e03030303550300c03030030f01705c03030030f00b05c440300c540c0d17030303032b3f2b2b03031b2b55171752b3f2b37030303030b1703031f0b0b271f030b270b270b27270b0b27270b0b566d17545d55555555503030303031b0357031b033f032b032b03032b80c0cae0327030b550305c031f02f1f02b0ac2b0f02b0f00b09c442f00c17175552b2b2b2b540c0c0c0c0c5d0303030313372b2b03032b3f27270b0b27270b0b030b1703033f0b0b2757030b270b270b5555566d17545d5555503033780c0d2e03030303033f0313035703130337032b0327030b552f0f02f0f00305c033f02f5702b0bc0b09c442f00c030366d9b66d033703030303270b130b03030303030303035559b59b5555503030303030303030303030303030303551304c0300c0300c0b05c440300c17175551337371337174acdccc2c2c4ccc2c2d9c2c5c2cac2c4c2d555555555544cec4e13371384c5c4c4c4c4c4c2c4c2d544c3c04c3c05c1704c1302c1104c13150303030303030b5555550303030317030303031f036703030303032b0367030303030b9b03030303503030b0b03030733030303030b0b270b0b0b0b566d03540d55540d3f555550303030303030380c0c0e03030380c0c0e0303030303030303550300c03030030f003030030f01705c0b02c440300c5030b0b03031f030b0b0b0b0b0b030b030b271f1f2713131f2727070b42c0c2c0c2c2c2d66c5d175541c4c1c4c0e0387c1f03c0f02c2d5542c2c2c2d52727272727272b031717030327271f2757031f03030303030b40c0c0c0c1ccc2c2c0c0c2c2c2c2c2c2d555559b45d5175555540c0c9e03032780c0c0c0c0c1c0c9c0c1c0c9c0c9c0c9c0c2c0c2d549c3c09c3c00c1700c7c09c7c0bc2f02c2c0b271109c0305c1d5549c0c2c2c2c2c2c2c9c5c5c9c2c1c2c2c2c1c2c0c2c9c2c2c2c2d0b0b0b555555555527032789c0c9e27171727272727270b0b0b0b55270f0270f01705c2b0ac0b02c442709c549c5c5c9c9c9c9c6c9cac9c6c9c0c5c5c5c5c9c0c9c0c9cfc9c9c1cac9c9c9c9c0c1cac2c2c2c2c9c2c2c2c2c2c1c2c2c2c1c2c2c2c2c2e6c2c9c2c2c2c9c2d59b45d517555555274fd5549c5c5c9c9c1c9e27072789c9c9c9c9c0c9e27032782c2c2c2d545c1709c3c09c3c0ac2b09c3c09c3c02c0b1109c2709c5c5c9d545c1d49c0c2c2c2c2c2c2c2c2c2c2c2c2d0b0b070b030b070b0b5555555555271717272727272727032789c0c9e0b0b0b0b551705c2b0dc270f0270f00b02c442709c549c0c5c5c5c5c9c0c9c0c1ccc9c9c9c9c9c1ccc9c0c9cfc9c5c5c9c9c4c9c7c9c4c9c7c2c2c2c2c2c2c2c2c1c2c2c2c1c2c2c2c9c2c2c9c2c2c2c2c2e6d59b45d5175555555549c5c5c9c9c1c9e27072789c0c9e27032789c9c9c9c2c2c2c2d545c1709c3c09c3c09c3c09c3c0ac3702c0b1109c2715030303030303035703130303030303030303030b03270303270b270b566d03540d555580daa038feaaaaaa95555603580e3b80ea03a80ea03a5555a80c0300c0c00c8c08c2302c2311222820305a5556a80c0c0c0c0d3c0c0c0c0c0cac0c0c0c6c0d5c0c0c0c0c0c0c0c9c0c0c0c0c0c2c0c0c0c2c0c1c0c0c9c2c9c2d59b40d5555503555540c0e6030303030303033ba80e3f0380e0380e5550300c030f00303003030034f02f0bc0b09c4480314001500031717030f970f0f0f0f0f2b032f2f1f2f57031f030b17030f270b0b0f0f0b0b031f0b0b271f030b270b270b566d175005045d55550303030303030f80c0c3e032f0323034f0323032303230323030b5500c000300303c00000003c00400545c5cfcacfcac2c5c2cfccc2c2ccc2c2c2c2d59b45d517555545c5cfd1e473f82c2d545c170fc3c03c002c11005c5d5551717131717131717170b170b13330b0b37330b0b2b0b130b555555555551713171313371384cec4e131313130b130b551705c130f0130f01301300b05c441304c1703555171717170b0b0b0b17130b0b0b0b0b0b0b070b0b0b070b0b42c2c2d1755555555551717171727035b89c0d6e272b272b0b0b0b0b551705c170f0170f01705c0b02c441705c545cac5c5c5c5c5c6c5c5c5c5c5c5cac5c5c1c5c5c5c5c5c5c5c1cac5c5c5c5c5c5c5c5c2c2c2c2c5c1ccc2c2c2c1c2c2c2c2c2c5c2c2c2c2c2c2c2e6c2cac2c2c2cac2d175175566d555555545c1c5e17071785c5c5c5c9cac9cac9cac9e27472782c2c2c2d545c3c05c3c05c1705c1705c3c05c3c02c0b1105c1705c5c5c5c5c0d5545c5c2c2c2c2c2c2c2c2c2c2c2cac2d0b0b0b070b0b0b070b0b5555555555171717172737272b27034b89c0d2e0b0b0b0b551705c1705c170f0170f00b02c441705c545c5c1ccc5c5c5c5c5c5c1c5c5c5ccc5c5c5c5c5c5c5c5c5c4c5c5c5c4c5c7c5c5c5c5c2c2c2c2c1c2c2c2c1c2c2c2c2c2c2c2cac2c2cac2c2c2c2c2e6d175175566d555555545c1c5e17071785c5c5c5c9d1c9e27332789cdc9cac2c2c2c2d545c3c05c3c05c1705c3c05c3c05c1702c0b1105c17151717171717172b1717171717330b0b17170b0b170b170b0b0b45d45d559b555517471785c5c5e171717170b0b55170f0170f01705c1705c0b05c441705c032b2b45cac5c0cad545c5d40c2c5c0c0ccc2c2c9ccc0c2c9c2c9c2d555555555540c0c0c0c0cec0e033b0380cac0cac0c9c0c2d540c1700c3c1ac3c0ac2b02c271112c0305c5c2c0c2c2c2c0c7c0d5547c5c5c7c2c1c2c2c2c1c2c2d0b0b0b0b1f0b0b0b0b55555555551f031f87c0c7e4b17174b1f1f1f1f0b0b0b0b551f0f01f0f01705c1f07c0b02c441f07c0b0b0b1f17171f1f1f1f1b1f1f1f1b1f03171717171f031f031f331f1f1b2b1f1f1f1f031b2b542c2c2e6c2c5c2c2c2c5c2c2c7c2c2c2c2c2c1c2c2c2c1c2c2d55555559b47d51f5558c5c5c7c6c7e1f1b1f87c7c7c7c7c0c7e1f031f82c2c2c2d545c1707c3c07c3c07c1f07c3c07c3c02c0b1107c1f05c2c2c2c5c5c5c5c5c5c7c7c7c2c2d0b0b0b0b0b0b070b0b070b5555544d5517131713131313131f1387c4e0b0b0b0b551705c1304c1701700b02c441304c17030b0b0b0b0b031717171755170750b0b42c2c0c2c2c2c1c2c2c2c2c2c2d555555547d55171717171f031f87c0c7e1f1f1f1f0b0b0b0b551705c170f0170f01705c0b02c441705c 25 33554431 10 1023
def hc_67_19 : Nat → Nat := unpackHintV5 0x8afcaf20f838e7d0cda9e4e1ea74d48c9c0c2526d64599a4322c64389a97cd2825adc8b15b220a53b46292b24764730730fa544e39d8978d112ca313c610b7d1a429e48209801f22084af870a22e17c48c84a82920ebc7c829922c06308680d0178031c04800018e 0xc0c0c0c0c4e6c0c0c0c0c0c0c4c0c0c0c0c0c0c0c2c0c9c0c0c4c2c4c2c0d0340c0d40d2d44d1342d27603aa80e37aaaaa03aa9a603a80ea038ee03a80ea03a80e96a035a80c0300c0c00c4c04c1302c13104c88a080c00c0e80c0c0c0c0c0c0ea80c0c4e6c0c0c0c0c0c4c0c0c0c0e80c0c4c0c0c0c0c0c4c0c0c0c0c0c2c0c0c0c2c0c1c0c0c4c2c4c2c0d0340c4d40c0d40c0d40d2d44d1342d2740c0e0380c0c0c0c0c0c0cdea038dc0e13030380e03980d0300c030f00303003030031301304c0b04c413200c0303000031713001317139b13130313000f0f0131313030b17030f130b0b0f0f0b0b03130b0b131f030b130b130b0345d0f1350f0f503135132f51344d0b47d0303030303030f80c0c3e0313031303130313031303130313030b44c0d00c000300303c000003c000f0003c03c00acacac5c5cae6c5c5cacac5c5c5c2c5c2cdccc2c2ccc2c2cac2cdc2d174dd54ad3742d45c5cdd1e47378acdcdcac2c2d6f45c170dc3c03c0ac3702c1001745c5d545c5d4acad5545c2c5c2cac2cac2cfccc2c2cbccc2c2d545d4ad551750b55171717172b2b2b2b3f3b2f8bcecfe0b4f0b551705c1705c170f0170f00b05c511705c1705c5cae6c5c5c5c5c5c5c5c5cac5c5c2c5c2cac2cac2c5c5c2c2c5ccc2c2c5d174ad2b45c5d45d42d45c5c5c5cacacacac5c5c5e17471782c2d45c1705c1705c3c05c3c02c17105c1705c170b1717330b332b17171717334cd1745d2b4dd33333333171717172b37372b5bd1705c1705c1705c41705c1705c5d554bcdd5545c5d172f330b0b3f330b0b170b170b2b0b370b45d5517554dd552f3b3f8fcecbe171717172b37372b0b4b0b53f545c3c05c3c05c1705c1702c1710405c1705c5c5c5c5c5c5c5c5c5c5cae6c5c5ccc2c2c5c5c2c5c2c2c5c2c5c2cac2cdc2c5d45c5d45d174ad3742d45d1c5e17171785c5c5c5cacdcdcac2c2d6f45c3c05c3c05c1705c1702c17105c1705c03172b1717179b1317032b131717030b170303330b0b2733030b270b130b0345d03375373f52b44d0b49d0303030303370380cec0e031303130313030b44c0d0305c030f0130f01304c0b05c41704c030ac5c5d2f3755517175550b170b2b0b2b0b3f330b0b2f330b0b4fd552b554ad553f45c5d3cacacacacfcecbe2f3b3f82d3c2d54fd1705c2b0ac2f0f02f0f00b0bc513f0bc2f0acac5c5c5c5cae6cacac5c5c5c2c5c2cac2cac2cacac2c2caccc2c2d174ad2b4acad4ad42d45c5cacacacacacacae2b472b82c2d45c170ac2b0ac3c0ac3c02c100030303540c0c0c0cfd2c0cbcbc0c0c0c0cac4c0d45d030b9b0303030b070b070b270b035540d4dc0e0380e0380c0f03c0f00c0c0c0c0c0c0c0c0cac0c0c0c2c0c0c0c2c0c0c0c2c0c0c5e6c0c0c0c0c0c0c0c0cacac0c0c4cdc0c0c0c0c5c0c0c2e6c0c0c0c0c0c0c2c0c0c0c0c2c2c0c0c1ccc0c0c2c9c2c2c2c2c0c0d031740c0d40d40c0d40d47d3742d0b40c0c0c0c0c0c0e03030380c0c0e03030380c0c0c0c0c0c0c0d030340c0c031700c0c00c3c00c0c00c3c05c1702c0b105c0300c03030317031b1f0303540c0c0c0cfd6c0cbcbc0c0c0c5d5030b9b0303030b1f0b070b070b0340d035547d0350b0380e0380e40c0c0f03c0f117030303030303030303179b030303031b2b03031f0303030303030303330303030b0303030b0303030b03170303030b9b0303030303030b0b1f0b0b0b0b030303030b0b0303073303030340d030350351f47d030350350b42d0303030303030380c0c0e0303030303030380c0c0e0303030340c0d0300c03030030f01705c03030030f00b02c41700c0300c0c0e6c0e6c0e6c0c0c7c0c0c0c0c2c5c2c2c2c2c0c0e6c0c0e6c0c0c0c0c1c0c7d1340d0340d0342d0b40c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d030344c1300c0300c0302c0b105c0300c17170b0b0b0b0b0b1333331337170b1f0b330b170b0b0b0b0b0b0b0b0b0b0b0b2b0b9b0b0b0b0b0b1f3f5133756745d1f44d0b42d133b1384cdc4e131713131313130b0b0b0b44d2d130f0130f01705c1304c0b02c41f04c1300d503033f036b0303030b030b03030303179b0303131b131b031750b40c2c1c0c0d035550b0380e0380e0f03c0303c45c0d5030303179b131b131b03033f034b0303030b030b030303170350b40c0c2c2c0c1ccc0c0d035550b0380e0380e0f03c0303c45c2c2d5545c5cfcdcbcacbcdcfcad0b0b0b550b0b50b0b0b0b4fd5533555542d17174f3f3b2f8bcecfe4f4f0b0b0b0b551705c2f0f02f0f02f0bc0b02c513f0bc2f02c2c2c5c5cccccccacccccac2c2c2e6c2c5c2c2c2c5c2c2ccc2c2c2c2d174cccd4cd542d0b45c5cccccce33473382c2c2c2d45c170cc3c0cc3c002c0b10017170b0b0b0b0b0b0b17171317171317170b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b1745d133751f3f51f44cdd0b42d1713171313371384cec4e13133713130b0b0b0b44d2d1705c130f0130f01301300b02c41704c1302c2d554bcdcfcacfcdcbcac5c5c5c5c2c2d5542c2d0b0b0b0b0b45d5517554fd550b4bcecfe3f3b2f85c5c5c5d3d3c2c2c2c2d4fd5170f0170f01705c1705c0b02c4101705c0b0b0b1717171717172b171717170b170b0b170b0b0b0b0b9b0b0b0b0b175171751745d50b42d17471785c5c5e171717170b0b0b0b5170f0170f01705c1705c0b02c41705c1700cacac0c5cac5c0cac0c2c2c2c5c5c0c2c0c2c2c2c2c0c0c2c2c2c2c2c0c2c2c2c2c2c0d1740cfd56cfd4ad2b42d0b40c0c0c0c0cec0e033b0380cac0cac0c2c0c2d0340c1700c3c1ac3c0ac2b02c0b1000c03030303030303031b5550303030342c2c2d540c1d5555555555540c0c0c0c0c0c0c0c0c0c0e03030380c0c0c0d540c030ac2b00c0c00c3c02c0b1100c030acacacacbcfcfc5cbc5cfc2c2d5542c2c2c2d0b0b0b550b0b54fd552b554ad550b53d3cacacacacfcecbe2f3b3f82c2c2c2d54fd2f0bc2b0ac2f0f02f0f00b02c513f0bc2f0acacacacacac5cac5cacac2c2c2c2ccc2c2c2c2c2c2c2e6c2cac2c2c2cac2d4ad2b4acad4ad42d0b4acacacacacacae2b472b82c2c2c2d40ac2b0ac3c0ac3c02c0b100033703545c4c4c5c0c0c5c0c2c0d5030b270b070b070b030b0b030340d0340d540c0c0e0380c0c0c0d030f03c030bc404bc0c4c0c00f130f17030317030b03000c2c7c2c1c2c1c2c0c2c2c0d0f40d2f40c0c0e0380c0c0c0c0c0f00c0300c000b03c03 26 67108863 11 2047
def hc_67_20 : Nat → Nat := unpackHintV5 0x156bfa20ed300020e 0x3030b0b0b0b0303031f1f0b0b0b0b17171f9b1317031f0b0b0b0b13130b0b13171703030b0b0303030303030307330b0b03030b0b0b0b0b0b130b0345d275b51f27503275275b51f44d0b42d0303030303031380c0c4e030703270307032703130313030b030b44c0d0305c1f0f01f0f0031f0131f01304c0b02c41f04c0300c0d5540cacad545c5cae6c4c5c0cad544c4d44c5c5c0c2c5c0c9c9c2c2c9c9c2c2c0cdc2c2c9d6c0c2c9c2c4c2d035540d40d3755555135540c0c0c0c0c0c4e03031380cdc0d2c0d2c0cdc0c4c0c4c0c4c0c2d540c1712c3c0fc3c00cbc04cbc04c1302c271104c030acad55517172b55171750b170b3f330b0b2f330b0b2b0b370b4fd5537554dd5517174b3f3b2f8bcecfe2b37372b0b4b0b551705c2f0f02f0f02b0bc0b0bc442f0bc 22 4194303 10 1023
def nh_67 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_67_20 (Nat.sub p 640)) (hc_67_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_67_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (Bool.rec (hc_67_17 (Nat.sub p 544)) (hc_67_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_67_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (hc_67_14 (Nat.sub p 448)) (hc_67_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_67_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (hc_67_11 (Nat.sub p 352)) (hc_67_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_67_9 (Nat.sub p 288)) (hc_67_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_67_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (hc_67_6 (Nat.sub p 192)) (hc_67_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (hc_67_4 (Nat.sub p 128)) (hc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_67_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_67_1 (Nat.sub p 32)) (hc_67_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def f_67 : Nat → Nat × Nat := unpackForestF 0x27c6af3e2579f12acf856e7c2af3e0570062fcf4914018b73bb6c9dd3680315e748dd3a24500629ce49566a8df382459aa31cdd14a6a8ab35c6f9ae31cd4954016bf33c6d99d36802d5e638dd3246298d22802d3e5f48f3025d97c23cb958a5dadd2e25d005a3c971be4b8c725c5b92e2bcad14a4b8ab25b6f94e3ec96d5e518c925b4f93eb4496d1e4b2b72595792c2b80297e458db2447c915a7c8d5c24568e00a578fa374851923e6df1fd7c8fe3e47cd9c0149f09d6e8ee364275ae3868f1c14784eb1c6c11e13ac519d698ceb4426dbe29ae31514f8bd2e45452e2a28f1614c8ad2a45450e29ae109b6789f3d426d7e21cf512678885bfc45a02216ef0995f8752b43a55a1d2a90b67286f3c42d1fe18d010c18c85a3bc2c5fa132a70a67284c2f80291e0eadf0756b83ab3c1d58c0146f062557b237c14915ec8c7044527b22ac09196048ab022557b1b7c031920148af634f7feb43d8d1dfc8cafe4557b137bed17df68a6fb35f7d9a7becd1dec4aafa4647b127bdd5a5eead0f86787b9afbdc549ec48ef6237004afbd4551de8bef3e7079cb63bd15de52a8ef35f78b383c45b1de6aeef347778ab3bc4d8012b6e4c6d7663e3b51c1d948ae4b4f75eb8392d1dd469eea34772536ba51f1c949ee5d71739a7b9cd1dcbae0e668072dafb9291dc946e009576bab7b5d58dae8dee21546ba2fb839c1c12d8d74576b9b7b7b1fdbd2a8d735f6eb383745b1ae6aed73476ce31366dbdb369ad9a6f6cd26b5c559afac6d7c6f6be2fb5c4d8012a6cec6e6aa323549959d6ded3c7c69d3eb3ad9da58c8cea6f68e3e33a99d9fac4cfb6f67db3b3a9159d46e0094f66cb231d1bd992f8c746765cb231cdbd952f8c7367639a3b1c5b98f8dec7c6763db131c4d801296c524762d2eb1411d73ac4c356861eb030c995736dec1d7060d3eae6d9d81ad0b9a6f5feb82e699d7b8dcbdb6f5edb3ae69757346eba25f5d12bae857d742aeba1275cc2e00251d712c8b1c6f5babe2dc5f1638ceb616458db7ad45f1636ceb1b4758cb72c91bd648ceb236258c9b00250d612c8a356f57caa28d5ad5d2f8a356756caa28d58d592c8a336f55cbe28cd9d552a8a335f54cb628cd5d51ae0a82675192b29c91d462dca4d6252537a9299d4949aa315651db128c4d801276a1c6850d329fd5bd408b0a02553fab5a7c8fd3c8e09e27d3fab3a71161398a09c2553fab1a6cd552cad2965614b1afa649b52c6ae97e794bdb32588dd2d49a960373fa31253589296dc7f45a49e38249595248d09245a3f937a3d5f5206b69035347a3823d168fe4ce8db6546daaa331c9198b07f25f4233da2d16108ce68a36c422392239e911ce484462425b7a1d1f1096d684b6742db62151d1096c6844603f92ba055bd02ad68156740ab1a04db8fe49a7fa6f3fd339fc5680126e7e1543b2b59f4550ecac67c1643b2379ec5f0ec8ce79d7e3ccaa1d917cec2dc76d623b5b79dd5c0ed6ce76156004959d4da0d2ade7435834ab59cb1f0e56e06956738dac1a558ce16d06946f37db81a519cdd6b06945f36db01a515cd7ad26bd6135c139a4d88d38de69c6734d371a4d680124e63b4f31da398e93cc748e63a3731ca798e51cc726e6435a31c9380217ca18da6247c285a79855c0a168e5fb4f2fda39429b4bd8f850a4f2eeb814291ca146e5a23f2d11b9684fcb426e5a127284b615cd3cae68e5724f2b92395c8dca12c055c7c2ad3e94253ca8ae05427d284a394b1c0a54fa50937289b8144d68a124e008572323713d1908c6de4e46423137933588996de462452311b92b1909548a4616f24239121160918e4482552309b91adc88d6b0461270042791491c76ac4445681d9b790d5a0764de41c6e20db78ec9747646e3fd681fd2e8ec5bc7a8e43d4601ee390f49b47626e3bc7f1ddb00ec49c0108e3a46812eb78e51604bac636b5f1b5ab8dcd986d46e25c621aab10d4db84b8b43356519a340cd1684b4de3235518a390c51604b4be3036c17a390bd1804b4ae2d56f16ab18b4db84b49a2ad65156340ab1685549a2596f14a2c0a49344b2be27c6013d2689655c4c6d42635012c938020dc496d012d6f11dac04b58c456d012c6f10abf084d60258be1fe720fdb004b15c3c4be1e257095b1073588394dc12b5a0952b05f5942f8be17c570ca2f86515c2f6d017b5a0bd2b04a5bc2cafc16358094af8539c8296c01295709ab904cd402528e00827032b781958c0c8de1057e0322f83d9c80c8ae0636f031af8359c80c6ae063470592782c91c0c2dc09d6204d378185580dac606c6f03ebf01b17c0d6c4061360040f8055bc02ac60146f00a2f80515c026de0135f009ab804d1c0102e0003f 10 11
def ch_67 : Nat → Bool := dagCheckNodeV5 fullMask g_67 ep_67 6 63 bds_67 642 (dagTraceF fullMask rootStock 11 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 fullMask g_67 ep_67 6 63 642 bds_67 (dagTraceF fullMask rootStock 11 f_67) (cur_67 0) (nh_67 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 32 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_1 : treeBlockF 32 64 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_2 : treeBlockF 64 96 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_3 : treeBlockF 96 128 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_4 : treeBlockF 128 160 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_5 : treeBlockF 160 192 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_6 : treeBlockF 192 224 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_7 : treeBlockF 224 256 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_8 : treeBlockF 256 288 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_9 : treeBlockF 288 320 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_10 : treeBlockF 320 352 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_11 : treeBlockF 352 384 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_12 : treeBlockF 384 416 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_13 : treeBlockF 416 448 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_14 : treeBlockF 448 480 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_15 : treeBlockF 480 512 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_16 : treeBlockF 512 544 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_17 : treeBlockF 544 576 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_18 : treeBlockF 576 608 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_19 : treeBlockF 608 640 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_20 : treeBlockF 640 642 ch_67 = true := by decide +kernel
theorem nj_67_1 : ∀ i, 0 ≤ i → i < 64 → ch_67 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_67_1 h1 h2)
theorem nj_67_2 : ∀ i, 0 ≤ i → i < 96 → ch_67 i = true := block_join nj_67_1 (fun _ h1 h2 => treeBlockF_at nb_67_2 h1 h2)
theorem nj_67_3 : ∀ i, 0 ≤ i → i < 128 → ch_67 i = true := block_join nj_67_2 (fun _ h1 h2 => treeBlockF_at nb_67_3 h1 h2)
theorem nj_67_4 : ∀ i, 0 ≤ i → i < 160 → ch_67 i = true := block_join nj_67_3 (fun _ h1 h2 => treeBlockF_at nb_67_4 h1 h2)
theorem nj_67_5 : ∀ i, 0 ≤ i → i < 192 → ch_67 i = true := block_join nj_67_4 (fun _ h1 h2 => treeBlockF_at nb_67_5 h1 h2)
theorem nj_67_6 : ∀ i, 0 ≤ i → i < 224 → ch_67 i = true := block_join nj_67_5 (fun _ h1 h2 => treeBlockF_at nb_67_6 h1 h2)
theorem nj_67_7 : ∀ i, 0 ≤ i → i < 256 → ch_67 i = true := block_join nj_67_6 (fun _ h1 h2 => treeBlockF_at nb_67_7 h1 h2)
theorem nj_67_8 : ∀ i, 0 ≤ i → i < 288 → ch_67 i = true := block_join nj_67_7 (fun _ h1 h2 => treeBlockF_at nb_67_8 h1 h2)
theorem nj_67_9 : ∀ i, 0 ≤ i → i < 320 → ch_67 i = true := block_join nj_67_8 (fun _ h1 h2 => treeBlockF_at nb_67_9 h1 h2)
theorem nj_67_10 : ∀ i, 0 ≤ i → i < 352 → ch_67 i = true := block_join nj_67_9 (fun _ h1 h2 => treeBlockF_at nb_67_10 h1 h2)
theorem nj_67_11 : ∀ i, 0 ≤ i → i < 384 → ch_67 i = true := block_join nj_67_10 (fun _ h1 h2 => treeBlockF_at nb_67_11 h1 h2)
theorem nj_67_12 : ∀ i, 0 ≤ i → i < 416 → ch_67 i = true := block_join nj_67_11 (fun _ h1 h2 => treeBlockF_at nb_67_12 h1 h2)
theorem nj_67_13 : ∀ i, 0 ≤ i → i < 448 → ch_67 i = true := block_join nj_67_12 (fun _ h1 h2 => treeBlockF_at nb_67_13 h1 h2)
theorem nj_67_14 : ∀ i, 0 ≤ i → i < 480 → ch_67 i = true := block_join nj_67_13 (fun _ h1 h2 => treeBlockF_at nb_67_14 h1 h2)
theorem nj_67_15 : ∀ i, 0 ≤ i → i < 512 → ch_67 i = true := block_join nj_67_14 (fun _ h1 h2 => treeBlockF_at nb_67_15 h1 h2)
theorem nj_67_16 : ∀ i, 0 ≤ i → i < 544 → ch_67 i = true := block_join nj_67_15 (fun _ h1 h2 => treeBlockF_at nb_67_16 h1 h2)
theorem nj_67_17 : ∀ i, 0 ≤ i → i < 576 → ch_67 i = true := block_join nj_67_16 (fun _ h1 h2 => treeBlockF_at nb_67_17 h1 h2)
theorem nj_67_18 : ∀ i, 0 ≤ i → i < 608 → ch_67 i = true := block_join nj_67_17 (fun _ h1 h2 => treeBlockF_at nb_67_18 h1 h2)
theorem nj_67_19 : ∀ i, 0 ≤ i → i < 640 → ch_67 i = true := block_join nj_67_18 (fun _ h1 h2 => treeBlockF_at nb_67_19 h1 h2)
theorem nj_67_20 : ∀ i, 0 ≤ i → i < 642 → ch_67 i = true := block_join nj_67_19 (fun _ h1 h2 => treeBlockF_at nb_67_20 h1 h2)
theorem nc_67 : ∀ i, 0 ≤ i → i < 642 → ch_67 i = true := nj_67_20
theorem lb_67 : LowerBin fullMask rootStock g_67 12 :=
  lowerDagV5 (kn_cons lb_63 (kn_cons lb_57 (kn_cons lb_65 (kn_cons lb_36 (kn_cons lb_35 (kn_cons lb_58 (kn_cons lb_64 (kn_cons lb_7 (kn_cons lb_27 (kn_cons lb_32 (kn_cons lb_14 (kn_cons lb_19 (kn_cons lb_9 (kn_cons lb_60 (kn_cons lb_42 (kn_cons lb_62 (kn_cons lb_59 (kn_cons lb_20 (kn_cons lb_61 (kn_cons lb_8 (kn_cons lb_66 (kn_cons lb_13 (kn_cons lb_1 (kn_cons lb_53 (kn_cons lb_2 (kn_cons lb_6 (kn_cons lb_37 (kn_cons lb_10 (kn_cons lb_5 (kn_cons lb_52 (kn_cons lb_17 (kn_cons lb_46 (kn_cons lb_41 (kn_cons lb_50 (kn_cons lb_39 (kn_cons lb_33 (kn_cons lb_56 (kn_cons lb_0 (kn_cons lb_28 (kn_cons lb_22 (kn_cons lb_21 (kn_nil)))))))))))))))))))))))))))))))))))))))))) rc_67 nc_67 (by decide +kernel)

def wg : List Gate := [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974662144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677288 * 2 ^ 32 + 3974662144)) (13 - 1) := by
  rw [show canon fullMask (4276677288 * 2 ^ 32 + 3974662144) = g_67 by decide]
  exact lb_67

end PEqualNP.Outside.L_meta_48013

theorem PEqualNP.Outside.L_meta_48013 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3974662144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974662144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48013.table2_from_lowerBin (4276677288 * 2 ^ 32 + 3974662144) 13 PEqualNP.Outside.L_meta_48013.root_lb PEqualNP.Outside.L_meta_48013.wg 18 rfl PEqualNP.Outside.L_meta_48013.wfits PEqualNP.Outside.L_meta_48013.weval
