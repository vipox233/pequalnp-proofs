import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47681

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

def m_0 : Nat := 0xcccc
def s_0 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_0 : Nat := 0x44c
def ep_0 : Nat := 0x48000000000000040800000000000000000000000000000440
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

def m_1 : Nat := 0x3300000033000000
def s_1 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_1 : Nat := 0x100000013000000
def ep_1 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_2 : Nat := 0x5050505000000000
def s_2 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_2 : Nat := 0x10105000000000
def ep_2 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_3 : Nat := 0x5500550000000000
def s_3 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_3 : Nat := 0x100150000000000
def ep_3 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_5 : Nat := 0x3000300030003000
def s_5 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_5 : Nat := 0x100010003000
def ep_5 : Nat := 0x1000200000001000000020000000000000000000000000000000000000000000000000000000100010000000
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

def m_6 : Nat := 0x3333000000000000
def s_6 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_6 : Nat := 0x113000000000000
def ep_6 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_7 : Nat := 0x5555000000000000
def s_7 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_7 : Nat := 0x115000000000000
def ep_7 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_8 : Nat := 0xa0a00000a0a
def s_8 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_8 : Nat := 0x20000020a
def ep_8 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000000000000000
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

def m_9 : Nat := 0xaa000000aa
def s_9 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_9 : Nat := 0x20000002a
def ep_9 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
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

def m_10 : Nat := 0xff000000000000
def s_10 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_10 : Nat := 0x17000000000000
def ep_10 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_11 : Nat := 0xf000f0
def s_11 : List Nat := [0x500050, 0x300030, 0xf0]
def g_11 : Nat := 0x100070
def ep_11 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040
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

def m_13 : Nat := 0x44444444
def s_13 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_13 : Nat := 0x40444
def ep_13 : Nat := 0x4400000000000040040000000000004040000000000000000000000000000000000
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

def m_14 : Nat := 0xa0a00000a0a0000
def s_14 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_14 : Nat := 0x20000020a0000
def ep_14 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_15 : Nat := 0xf00f0000f00f
def s_15 : List Nat := [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f]
def g_15 : Nat := 0x10070000300f
def ep_15 : Nat := 0x200800000000000000000000000000000000000000000000000000001002000030000000100400000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xba5d37b3a7b2d4e80f 7 127 3 7 6 63 9 511
def nh_15 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_15 : Nat → Nat × Nat := unpackForestF 0x1f6e87a3b1d4e80f 3 6
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 7 (dagTraceF m_15 s_15 4 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 7 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) (nh_15 0) s_15 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 7 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 7 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0x3c003c003c003c00
def s_16 : List Nat := [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00]
def g_16 : Nat := 0x140010003400
def ep_16 : Nat := 0x1000200000001400000024000000000000000000000000000000000000000000000000000000140010000400
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_16 : Nat → List (Nat × Nat) := fun _ => []
def nh_16 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 0 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 0 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0x2828282828282828
def s_17 : List Nat := [0x808080808080808, 0x28002800280028, 0x282800002828, 0x28282828]
def g_17 : Nat := 0x82028
def ep_17 : Nat := 0x8202800000000000020200000000000080008000000000000000000000000000000000000000000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_17 : Nat → Nat := unpackHintV5 0x2802 0x0 8 255 4 15
def f_17 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) (nh_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0x3c3c00003c3c0000
def s_18 : List Nat := [0x1414000014140000, 0xc0c00000c0c0000, 0x3c0000003c0000, 0x3c3c0000]
def g_18 : Nat := 0x140000101c0000
def ep_18 : Nat := 0x10080000000000000000000000140000000c0000000000000000000000000000000000000014000010100000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_18 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_18 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 3 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 3 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 3 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 3 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x3c3c3c3c
def s_19 : List Nat := [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c]
def g_19 : Nat := 0x101c343c
def ep_19 : Nat := 0x242000000000000c0008000000000000000000000000000000000000000010100400
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8188710620c41806b2d60a8350290cc3981302604c0889102204407c6f81f03e07c0f81f03e07c0d901d001 0xf06868343ea21d0f0e0686c2c3212154b0ac685e4c2d22144f09098444420160f0906a78313016960513020880c3c041a498fe34770e378519c14fe0276fd377499b94bdaa5ccd2b6493ad48d1a44883f421da00dcc0664c2f1c158a09c4846201f0e0d8605c0826000f 11 2047 5 31 10 1023 17 131071
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x904824120823e5f0f17831980b958ac152a8509f4f06a341a0b4582c160941e0c0602202 0xf93cf534f018ec14a130e014de3ada36d12ea12d502d2c25d12ca93ca52c952ca23cc54cc144bc18b814a52c9814a53494149834942cb13dad35a92ea12d9c1a90167c30782c6814 9 511 3 7 10 1023 16 65535
def cc_19_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x162c58b0f1c313660c030000000 0x9b38993496389434702c6f3c90288e248b4c89406d2c 7 127 3 7 9 511 16 65535
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_19_2 (Nat.sub p 64)) (cc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_19_0 p) (Nat.blt p 32)
def hc_19_0 : Nat → Nat := unpackHintV5 0xec27223809b84d446432e21608ae15702b05488a024c225092048654111f88f82744352971c9523891a10b8c5822820f280b8002 0x0 13 8191 5 31
def hc_19_1 : Nat → Nat := unpackHintV5 0xb415812b094c69c54b1a581282921442a1850067a33b11d04e046e13419984cc06413201808bc25e02f0178099236b105832800c 0x0 13 8191 5 31
def hc_19_2 : Nat → Nat := unpackHintV5 0xf04e84e04d08bcaac8a8298890488478864a41224e012 0x0 12 4095 5 31
def nh_19 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_19_2 (Nat.sub p 64)) (hc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_19_0 p) (Nat.blt p 32)
def f_19 : Nat → Nat × Nat := unpackForestF 0x252712934941c4a0d00c7f1c288e12018ee22991140031b818cc0a7e053b029bbb4f1da68ec18760a014cc0a5ee0146d1d368d80a5cd12c02958149d7298b9445c0c2e0500a46913d489aa44b94a68912d480d250d1285890160291010fc0876043732a21e0d0c878643432161a0d0c8480433292614910ac68513c02178f13078883c2c1e12010ac5a782d3016960109c0846041f020d8105c10980844041e020d00826000f 7 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 78 (dagTraceF m_19 s_19 5 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 78 bds_19 (dagTraceF m_19 s_19 5 f_19) (cur_19 0) (nh_19 0) s_19 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 64 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_2 : treeBlockF 64 78 ch_19 = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 64 → ch_19 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nj_19_2 : ∀ i, 0 ≤ i → i < 78 → ch_19 i = true := block_join nj_19_1 (fun _ h1 h2 => treeBlockF_at nb_19_2 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 78 → ch_19 i = true := nj_19_2
theorem lb_19 : LowerBin m_19 s_19 g_19 6 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xf0000f00f0000f00
def s_20 : List Nat := [0x5000050050000500, 0x3000030030000300, 0xf0000000f00, 0xf0000f00]
def g_20 : Nat := 0x50010000700
def ep_20 : Nat := 0x1000020000000000000000000000000000000000000000000000000000000000100002000000050010000400
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def nh_20 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 7 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 7 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 7 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 7 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff00ff0000000000
def s_21 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_21 : Nat := 0x100150000000000
def ep_21 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xffff000000000000
def s_22 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_22 : Nat := 0x117000000000000
def ep_22 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_10, s_10, 4, g_10), (m_7, s_7, 4, g_7), (m_6, s_6, 4, g_6)]
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
  lowerDagV5 (kn_cons lb_12 (kn_cons lb_10 (kn_cons lb_7 (kn_cons lb_6 (kn_nil))))) rc_22 nc_22 (by decide +kernel)

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
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f0f0f000000000
def s_25 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_25 : Nat := 0x10105000000000
def ep_25 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xf0f0f0f00000000
def s_26 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_26 : Nat := 0x107050700000000
def ep_26 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_26 nc_26 (by decide +kernel)

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
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def nh_28 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xaa00aa00aa00aa
def s_29 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_29 : Nat := 0x20002000a002a
def ep_29 : Nat := 0x800280000000000000020000000000000000000020002000a000800020002000000200000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x5050505050505050
def s_30 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_30 : Nat := 0x10105010101050
def ep_30 : Nat := 0x1000000000001040000000400010004000000040000000000000000000101000101010000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x6666666600000000
def s_31 : List Nat := [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000]
def g_31 : Nat := 0x6044600000000
def ep_31 : Nat := 0x440000000000006004200000000000604020000000000000000000000000000000000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x66666666
def s_32 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_32 : Nat := 0x2062666
def ep_32 : Nat := 0x24600000000000040040000000000206040000000000000000000000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x5555555500000000
def s_33 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_33 : Nat := 0x115155500000000
def ep_33 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_7, s_7, 4, g_7), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4)]
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_33_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_33 : Nat → Nat := fun p => Bool.rec (hc_33_1 (Nat.sub p 32)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) (nh_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_7 (kn_cons lb_2 (kn_cons lb_4 (kn_nil))))) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x666600006666
def s_34 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_34 : Nat := 0x44600002666
def ep_34 : Nat := 0x222000000000000000000000004200000040000004020000040000000000000000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xd43a8340de5bc168ad05a0ac5582b0560a4519a304608c1182304608c0f91f03e07c0f81f03e07c0d901d001 0xb878503c32a61f0f0f068742c381217090a0285c3c260a140f09848683e321e980b4b04a541d240a8d13060882c2c14120513020880c3c041a4b8fe34770e378519bf4fdd276dd376c99b54bda256cd275691aa0fd187c843b401b9b0cc8864402f1e158e09c4846201f0e0d8605c0826000f 11 2047 5 31 10 1023 17 131071
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0e0e0e0c4c0c0aba8a8a8a1929089888888815d515049484841401610090100 0xf93cf534f018ec14e44ce040903cc920c53cb414c524b524ca34c14cbd44b818b0146440a42499248a3e663da13d9d35943d9035881c684c 8 255 3 7 10 1023 16 65535
def cc_34_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x1e38dbb162c5878e1c234080c83 0x290f26a71313450264a4a24a4920288e124513220809c3c4c16418e20468944c 7 127 3 7 10 1023 17 131071
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_34_2 (Nat.sub p 64)) (cc_34_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_34_0 p) (Nat.blt p 32)
def hc_34_0 : Nat → Nat := unpackHintV5 0xde16d13605a46d016613285940ca0640b201900c805b4a9252ce8494109f88f44743352962494e3891b08c885c42830f280b8002 0x0 13 8191 5 31
def hc_34_1 : Nat → Nat := unpackHintV5 0xe226d23589a44c856213009708ae54c5a0acdd46262f11590a444e22320e9855024312008844022000f0870424a101051810c004 0x0 13 8191 5 31
def hc_34_2 : Nat → Nat := unpackHintV5 0x1522914a88c8fa1d2364594a11221c82542a041008 0x0 11 2047 4 15
def nh_34 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_34_2 (Nat.sub p 64)) (hc_34_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0x262713134031fc74a23a491c288e12018ee20991040031b818ce04710234029fbb4f1da68ec18760a014edc098e040029b814cc0a5e052b0293ac8d18a48b14c58a22c0616a48b0140291810fd4848913d489aa6491207a9035021f2207008760437381e1c0d0e05870240219920f8907a482d2e1e12094903a4c3c2612120540864042f02158109c5098284414160a0900846041f020d8105c10980844041e020d00826000f 7 10
def ch_34 : Nat → Bool := dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 78 (dagTraceF m_34 s_34 5 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 78 bds_34 (dagTraceF m_34 s_34 5 f_34) (cur_34 0) (nh_34 0) s_34 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 ch_34 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 64 ch_34 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_2 : treeBlockF 64 78 ch_34 = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 64 → ch_34 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nj_34_2 : ∀ i, 0 ≤ i → i < 78 → ch_34 i = true := block_join nj_34_1 (fun _ h1 h2 => treeBlockF_at nb_34_2 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 78 → ch_34 i = true := nj_34_2
theorem lb_34 : LowerBin m_34 s_34 g_34 6 :=
  lowerDagV5 (kn_nil) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x6600660066006600
def s_35 : List Nat := [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600]
def g_35 : Nat := 0x40002002600
def ep_35 : Nat := 0x200220000000400000024000000000000000000000004000200040000000000000000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc3706d0da0b41606c0580ac3582b0560a4519a304608c1182304607c8f81f03e07c0f81f03e06c8d801d001 0x3e0e15130929869282e9e148e09a706e393318984e4b262543e241e8ed206e80313c1698069202c80123807184d8fe547716378519c14fdf276e5376c99b54bda256bd275691a60fd007c783b3a1b9c0cc8864402f1e158a09c4846201f0e0d8205c0826000f 11 2047 5 31 10 1023 17 131071
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x8dc6231188c3f1e2f06db61b0d868b4192a550281248940a00f2782a9088040190c00c00 0xc08100187e0a3d931e480ec4c7420170c1c278dd342c202e4c16a40cf4865a02c4818878c0305d182d0816468503026182a8e14c68a1384e9a12100a4788c28271e234a0fc7c4a3d4a952449910548426 9 511 3 7 10 1023 17 131071
def cc_35_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x162c5887020408090c980600000 0x364098289624934c91408e4c8c403430892887243240 7 127 3 7 9 511 16 65535
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_35_2 (Nat.sub p 64)) (cc_35_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_35_0 p) (Nat.blt p 32)
def hc_35_0 : Nat → Nat := unpackHintV5 0xda36a1b38d982cc0650b205900c61620b101880c025b2aa1d2d2922480a3090c67c5354971c95246222090087463050f480b8002 0x0 13 8191 5 31
def hc_35_1 : Nat → Nat := unpackHintV5 0xde46d134919c4ca2602af856c8ae44c5a0acfc47643911998ad05222520f9855428112108843c41830c005842c01600a080a4002 0x0 13 8191 5 31
def hc_35_2 : Nat → Nat := unpackHintV5 0x14aa724a4850f91b43245c8929111a825022822004 0x0 11 2047 4 15
def nh_35 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_35_2 (Nat.sub p 64)) (hc_35_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xc7f2c289612018ee329919408c26461000c6f0d288692018cc0a7efc187e0a014edd498ea4074263a1000a6edd3c6e9a014cc0a5e052b61a430d018078c0300293ad8c16840b2340291a78e13c689d384e9a010fd0a5485264694210a9084c043e3e0e010ec086e0433251c9a4a0946249392e9e124c4907c4e38269c120f40864042f02158bd205e802d3c16980109c0846041f020d839201c800e3807180105c0826000f 7 10
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 78 (dagTraceF m_35 s_35 5 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 78 bds_35 (dagTraceF m_35 s_35 5 f_35) (cur_35 0) (nh_35 0) s_35 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 ch_35 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 64 ch_35 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_2 : treeBlockF 64 78 ch_35 = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 64 → ch_35 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nj_35_2 : ∀ i, 0 ≤ i → i < 78 → ch_35 i = true := block_join nj_35_1 (fun _ h1 h2 => treeBlockF_at nb_35_2 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 78 → ch_35 i = true := nj_35_2
theorem lb_35 : LowerBin m_35 s_35 g_35 6 :=
  lowerDagV5 (kn_nil) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x3030303030303030
def s_36 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_36 : Nat := 0x10101010103030
def ep_36 : Nat := 0x1000202000001000000020200010000000000000000000000000000000000000000000000010101010100000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0x3333000033330000
def s_37 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_37 : Nat := 0x113000013130000
def ep_37 : Nat := 0x1200000000000000000000000012000000000000010200000202000000000000000000000110000010100000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xaaaa0000aaaa0000
def s_38 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_38 : Nat := 0x20000020a0000
def ep_38 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0x5555000055550000
def s_39 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_39 : Nat := 0x115000011150000
def ep_39 : Nat := 0x1000000000000000000000000014000000040000010400000004000001100000111000000000000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xff000000ff00
def s_40 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_40 : Nat := 0x150000003700
def ep_40 : Nat := 0x220000000000000000000000000000000000000004000000040000001000000032000000150000000400
def bds_40 : List (Nat × List Nat × Nat × Nat) := []
def cur_40 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_40 : Nat → Nat := fun _ => 0
def f_40 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_40 : Nat → Bool := dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 1 (dagTraceF m_40 s_40 3 f_40) cur_40 nh_40
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 1 bds_40 (dagTraceF m_40 s_40 3 f_40) (cur_40 0) (nh_40 0) s_40 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40 : treeBlockF 0 1 ch_40 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 1 → ch_40 i = true := fun _ h1 h2 => treeBlockF_at nb_40 h1 h2
theorem lb_40 : LowerBin m_40 s_40 g_40 4 :=
  lowerDagV5 (kn_nil) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xff000000ff
def s_41 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_41 : Nat := 0x570000007f
def ep_41 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf0f00000f0f0
def s_42 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_42 : Nat := 0x105000003070
def ep_42 : Nat := 0x202000000000000000000000004000000040000000000000000000001000000030200000105000000040
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_42 : Nat → Nat := fun _ => 0
def f_42 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 1 (dagTraceF m_42 s_42 3 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 1 bds_42 (dagTraceF m_42 s_42 3 f_42) (cur_42 0) (nh_42 0) s_42 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 1 ch_42 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 1 → ch_42 i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 4 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xf0f00000f0f
def s_43 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_43 : Nat := 0x5070000070f
def ep_43 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000050400000400
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xf000f000f000f000
def s_44 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_44 : Nat := 0x100010003000
def ep_44 : Nat := 0x1000200000001000000020000000000000000000000000000000000000001000100030000000100010000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xf000f000f000f00
def s_45 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_45 : Nat := 0x100050003000700
def ep_45 : Nat := 0x200020000000400000004000000000000000000000000000000000001000000030002000100050000000400
def bds_45 : List (Nat × List Nat × Nat × Nat) := []
def cur_45 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_45 : Nat → Nat := fun _ => 0
def f_45 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 1 (dagTraceF m_45 s_45 3 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 1 bds_45 (dagTraceF m_45 s_45 3 f_45) (cur_45 0) (nh_45 0) s_45 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45 : treeBlockF 0 1 ch_45 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 1 → ch_45 i = true := fun _ h1 h2 => treeBlockF_at nb_45 h1 h2
theorem lb_45 : LowerBin m_45 s_45 g_45 4 :=
  lowerDagV5 (kn_nil) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xcc00cc00cc00cc
def s_46 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_46 : Nat := 0x40044000c004c
def ep_46 : Nat := 0x800080000004000000040000000000000000000040000000c000800000000000000000004004400000040
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

def m_47 : Nat := 0xffff0000
def s_47 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_47 : Nat := 0x131f0000
def ep_47 : Nat := 0xc000000000000020e000000000000131000000000000010100000
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_47 : Nat → Nat := fun _ => 0
def f_47 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 1 (dagTraceF m_47 s_47 3 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 1 bds_47 (dagTraceF m_47 s_47 3 f_47) (cur_47 0) (nh_47 0) s_47 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 1 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 1 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 4 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xffff
def s_48 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_48 : Nat := 0x377f
def ep_48 : Nat := 0x48000000000000040800000000000032200000000000000440
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xff00ff00
def s_49 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_49 : Nat := 0x13003700
def ep_49 : Nat := 0x24000000000000000000000000000200040000000000130032000000000010000400
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_49_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_49_0 p) (Nat.blt p 32)
def hc_49_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70c952850a142240810203460c1220405080400000 0x0 7 127 2 3
def hc_49_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3870c983054a1120344881020405081020402 0x0 7 127 2 3
def hc_49_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_49 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_49_2 (Nat.sub p 64)) (hc_49_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 64 (dagTraceF m_49 s_49 5 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 64 bds_49 (dagTraceF m_49 s_49 5 f_49) (cur_49 0) (nh_49 0) s_49 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 ch_49 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 64 ch_49 = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 64 → ch_49 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 64 → ch_49 i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 6 :=
  lowerDagV5 (kn_nil) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xff00ff
def s_50 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_50 : Nat := 0x1f007f
def ep_50 : Nat := 0x60000000000000000000000000000e000800000000001000200000000000100040
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xf0f0f0f0
def s_51 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_51 : Nat := 0x10103070
def ep_51 : Nat := 0x20600000000000000040000000000000000000000000101030200000000010100040
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xcccccccc
def s_52 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_52 : Nat := 0xc044c
def ep_52 : Nat := 0x44000000000000c004800000000000c040800000000000000000000000000000440
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xaaaaaaaa
def s_53 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_53 : Nat := 0x20a222a
def ep_53 : Nat := 0x2020000000000008000800000000020a000800000000020022200000000000000000
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

def m_54 : Nat := 0x55555555
def s_54 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_54 : Nat := 0x11151555
def ep_54 : Nat := 0x4400000000000040040000000000004040000000000111010000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xff000000ff000000
def s_55 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_55 : Nat := 0x100000013000000
def ep_55 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xff000000ff0000
def s_56 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_56 : Nat := 0x170000001f0000
def ep_56 : Nat := 0x800000000000000000000000000000000000000060000000e000000120000001000000014000000100000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xf000f000f000f0
def s_57 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_57 : Nat := 0x10005000100070
def ep_57 : Nat := 0x2000000040000000600000000000000000000000000000000000100000001000200010005000100040
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xf0f00000f0f0000
def s_58 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_58 : Nat := 0x1070000030f0000
def ep_58 : Nat := 0x2080000000000000000000000060000000c0000000000000000000001020000030000000104000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xaaaa5555
def s_59 : List Nat := [0x5555, 0x22221111, 0xa0a0505, 0xaa0055]
def g_59 : Nat := 0x20a1555
def ep_59 : Nat := 0x8004000000000020a040000000000020010000000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb34b34d3d93a73653533400f 7 127 3 7 9 511 12 4095
def nh_59 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_59 : Nat → Nat × Nat := unpackForestF 0x33db3433a33633533400f 3 9
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 7 (dagTraceF m_59 s_59 4 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 7 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) (nh_59 0) s_59 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 7 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 7 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV5 (kn_nil) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0x2222222222222222
def s_60 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_60 : Nat := 0x2000202022222
def ep_60 : Nat := 0x200222000000000000020200002000200000000000200020202000000000000000000000000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := []
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_60 : Nat → Nat := fun _ => 0
def f_60 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 1 (dagTraceF m_60 s_60 3 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 1 bds_60 (dagTraceF m_60 s_60 3 f_60) (cur_60 0) (nh_60 0) s_60 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 1 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 1 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 4 :=
  lowerDagV5 (kn_nil) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0x5a5a00005a5a
def s_61 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_61 : Nat := 0x10520000125a
def ep_61 : Nat := 0x20800000000000000000000004200000048000000000000000000001002000012000000000000000000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 4 f_61) (cur_61 0) (nh_61 0) s_61 4 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 4 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xc0c0c0c0c0c0c0c
def s_62 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_62 : Nat := 0x40404000c040c
def ep_62 : Nat := 0x80008000004000000040000040000000c0008000000000000000000000000000000000004040400000400
def bds_62 : List (Nat × List Nat × Nat × Nat) := []
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_62 : Nat → Nat := fun _ => 0
def f_62 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 1 (dagTraceF m_62 s_62 3 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 1 bds_62 (dagTraceF m_62 s_62 3 f_62) (cur_62 0) (nh_62 0) s_62 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 1 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 1 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 4 :=
  lowerDagV5 (kn_nil) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0x5555555555555555
def s_63 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_63 : Nat := 0x115155511151555
def ep_63 : Nat := 0x1000000000001440000004400014004000040040010404000004040001101000111010000000000000000000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33)]
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def nh_63 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 0 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 0 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_nil)) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xff00ff00ff00ff00
def s_64 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_64 : Nat := 0x100150013003700
def ep_64 : Nat := 0x1200220000001400000024000000000000000000010004000200040001001000130032000100150010000400
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_44, s_44, 5, g_44), (m_49, s_49, 6, g_49), (m_5, s_5, 4, g_5), (m_40, s_40, 4, g_40), (m_45, s_45, 4, g_45), (m_35, s_35, 6, g_35), (m_20, s_20, 5, g_20)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c0450610708084041060810017a1b521a80d406613301980cc06212d11680b015802c01504a805402a0140490448023040c4001 0x3da007d3d0ca6a1d49435a8063400dc74198d82e9b0d34e19e8632d0861278b94f1024e1c09c2c0b83c3409848109081ea10524f09486111381c130302602888090d00da1016420569e08d0c0e27010360106d68d3ecba5d7f47ae6875493ea125d3247a4487468fe871dcea37954671b53e2ea5c394782a87014fdfc9dbd5376f266da4bdaa95ad127552467b12c9c218f43e1d876350cc2a190342b058460306c02098001f 13 8191 6 63 10 1023 19 524287
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa922888211842107c9f07c1c3701c06c5b060d8054d504c9304c13044910350d0304c02c4b002c00 0x8697a0a5280579f85e9ad2e6343788fa514f9051e304f8811df01778071d45072131c2376e0d9b0265849d594d625152125569357a454449953505ad215450520912b4e46538f035300552a30468c1645256d7943524ed05334048979115e420f4c8353a094b815 10 1023 4 15 11 2047 18 262143
def cc_64_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2618ce3088620791e0781e0781b36c1b06c18327c902409018c601445008c20044100400100000 0x2d920bd182d230ba132d83cb4d12a044a00d2c824acd0aaa4aa84869242a252a8132f4d3fc34be6d1f7b43dc93f624bce91f1a43c28fefa3bb88dec233ae13a98369e09a184d96116001592176194d8e515f8168a5761134 10 1023 4 15 11 2047 18 262143
def cc_64_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x986608cd4f501404892048120480e4380e0380b32c0b024890240902405414050140230801104001 0xfe4d201213f1427d27552d3e9da5d13479e6873a93e6d25cb24792487208fe391dc5a37874670c13a041b3e02655088f20d1deb03b25c754a0e8171c91c38a3470068a20d1b41235d606a6b8d2d41a02e3324c65488c8091881a30024 10 1023 4 15 11 2047 19 524287
def cc_64_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xccc8c8c1c0c0c0c0a4a099987c786a685a585843393831222020201918030000 0x50a38a0469061127c1a4e0249aac132d7261a84b85c7f0492a93251223f0349304904112441a3e8348f0491b18229184604c89049128d229a244024842490ad0a0d214112d 8 255 3 7 11 2047 19 524287
def cc_64_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0798730660b8b702e05c0ac75056a2a1540989301a6340680b1141188300600a1140280500a004808000800 0x17e8faecaf5c152230617a8caf0af5d9523f07c440cae52f5c252b727d608c34e2de8c53d06bd9cd6f31a9e3352c569d88d0f09a16025ebe4a57457ad8a9579208b0b6b814cf8271c043200856a0ceb8ae5695cb20516692ec521d614e8a096b410ec011d7149ad28358492bd1a5595e870b6b014ea01a53560a54b9489428c2e42034 11 2047 5 31 11 2047 19 524287
def cc_64_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xcab20c4710b16c0ac6b0a865594232885e46cdb064981589605455054141320c02c4b01945101400 0xf26bfdcd5fb12f7595eea279ce4db7c9a4905b630a6240ef75236e35edb4bdac496402db0853d928d9ed4b612f6b95ed626d1c16d7c29e5b60d46905a10329b061b50d2690581433e2f2183e2b0659e932cc9859120b12619a0a0a82864240cb8b395146342caf0514109c5010b241563826270a18714b05af5e95e3a0824c100941860a32bc2bd72549001f12032 10 1023 4 15 11 2047 19 524287
def cc_64_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9d27094a5094232849f27c1785c170549505415048d203ccf0348d0340b2284a0208802006218006 0x8015e4d85b360537f8184d059358517d83b7d0334c84b350434c04b348437ec587e4527cc507c24c7ba404b05b338537b0407a2547995478c607826c7796c7694674126709244a84b3304374b527415e7195c7115c7282871949711417324b722437094e4a04b3284370023 10 1023 4 15 11 2047 20 1048575
def cc_64_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xe01c03614b194128250443843081e1bc0780f01e036354ca81312603c8780f01a2340398700e01c001c00000 0x8f3548ea5494b539434b93b499325f92a536824d9224b91a47902458fa3f8e2338113e761326c12a5d1262303e170328d13c8c9368c134892418ab4988a322283e8946088b6c8826c8b3518a25d89a3f87a338495d2203e86a545ca345c24485a34841446793467b52842528635f853535b2368495e83936830188225f81a5762a3d8115e4e85b370530a02b 11 2047 5 31 11 2047 20 1048575
def cc_64_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0ae2b0ac09224084e107c9f07c1d26c9b0685a0681826012622880200801c452140501405001400 0xa003b9f8335284b3b0435204b3a843a1458a0c529f4509e94c9e1405105b398539d8409ca469a925991245084b390439ab5e9a252989499794198b5c97b5c970189924e9814b969435004b38843960139c35e9ba5e8e15f879579b12899925959244f05b378530401b5e12490b545d9349135190a428f2322383e17832 10 1023 4 15 11 2047 20 1048575
def cc_64_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x8008007087007007007007007006654514404404403e33c13c03632a62a02622601a61a00c70c00c0044040002000000 0xadcbf5e8d652afd753568a4e4c13866210c840ab6830d549e89912c3e188655bd4eb5a5d6749a3c7d388ca4cafc31536829b5852eaea3d55458227ef24cdb896b01252507c300caa69454925a8a48f15069dacbc1322487d4fd46972ed355d81a7eee4cc901f33e5285aa54b97a4aafc29535f26b4a496921451e5e8fabf1355d8a9eaa45b3d0a60a06e8b2f29c5b3c0a7440a14c2c9dc51 12 4095 5 31 10 1023 19 524287
def cc_64_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x16254890b142850a1405 0x169120681859e35b326ad349c9a275925cb1ca162572c2a858050 7 127 3 7 10 1023 19 524287
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_64_11 (Nat.sub p 352)) (cc_64_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_64_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_64_8 (Nat.sub p 256)) (cc_64_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_64_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_64_5 (Nat.sub p 160)) (cc_64_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_64_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_64_2 (Nat.sub p 64)) (cc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_64_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_64_0 : Nat → Nat := unpackHintV5 0xc3a0585c1ae328dc600b8c016f426dd815b506aec7f4716a800e4fe029ca3322572438148205862a2dfacd99a5a84af4ca3e98c09250ca004a3fc047e414d428901a718a780a274001400000 0xaaa8c06a73a81d46ccaed07322aa014202288086c4539c0e2001c1546319d44ded608b373f608aaaa738c18b1628d54608b23d555600c62adeb551a22aaaaaa78f2a9cf3df2aaa355676aaaaaaaaa22a3515455554e0782539e94688aaaaaad52a9ce73d52aa35555676aaaaaa9d115945515dede9d9e6c5ee95545f3e40005014000016aaf057aa8c18b5a8d445115505110058b1555182aa83b50555540159554680aa00a0080000aaa00aa002000000aa000aa000ec4040000080000418c6318c63 19 524287 8 255
def hc_64_1 : Nat → Nat := unpackHintV5 0xb6eb3519c67a294569e876370e40a0319ba066698a8a03311a261d4602c0e85800087a890f001a07e3400060080b9071680a2a8285084899080c46e180082b8485502098121141c002280000 0x6a00318c67018c000710000c6318c6739c0e318c60003061c00055400000001541550000155000000005507600aa0020200100700000101ef63d803d8d1aad9e2d54603539d562c3bd46c8a12bb55009eb8405a28000021b14555381d1000e0aaaa8d1803b46a8d415182aaaa35955054001154000000015415500010d80a7381cf1e00000515501553ccf33a084c98705555555514650e1d76ca7381d5546a8080506d10055514667099bd8c9a1079cc080039c630d85b60628001c00088001a9c 19 524287 8 255
def hc_64_2 : Nat → Nat := unpackHintV5 0xe142b8500db85f6e00d7c3f5f00d403f024ebd03af202bb416a548a5c3a9502a40164848722017c4c4955d250033560cd00248ec9200131184c0005cd4170005c001205024240009 0x6c6ec6ab77b5ee0454157cf962c51aa8c11768b56aaf057aac58f51aaabb9eab41584f5cab5aa8d115555555555768d55555555115955455150d88d1011a353b1d00010d8c6280a8c6739e3c00141c38c631ab6d94e718c0ea21c6a354eadb100006318c68368800c0001a8c56440d8f61b6 18 262143 8 255
def hc_64_3 : Nat → Nat := unpackHintV5 0x8ec023b007dd11698e544614f024d865280e48c15170c43824ee203a414e40537c14cf102e854b80227c64910e23014800c1dc245720148144d051201438100cc141c1705c140017 0xa2c27ae55ad4688aaaaaaaabb5546aaaa35546aaa22b2aa8aa2bbdbd3a6f68e1364fdee79b1dec6833f7bdef72ef6b04ded1826c17bd8b363bd8d045ef7bdec4def728bdef73c4 18 262143 8 255
def hc_64_4 : Nat → Nat := unpackHintV5 0xd719c5a3c482b917b685b405b185ad09a0999e059a879a808e198e00819981807519728571825f25590c590059005012225c2200220022002200004400000000 0x6f68e977b1ab0459bda3137bd9b1dec683bd9bda304ded1d2ef68c106bb46ad9e2f7b368c451457cf962c51aa8c1151a355782bd562c78d555 16 65535 7 127
def hc_64_5 : Nat → Nat := unpackHintV5 0xe8d3f950ee282f8109ced1b3209cb8132707bc0dee40c88b0a111183015f6167b0297d6f5f4017d0058c691d461f2845626150083d170e01433050b81425090306407050001c0000 0xe7539df0473d44073ad6ed86d36800af6ad965ae97002ec136028002c020005046305ab5600f9f1c020162c03872aa02063180c6b463678e16337b2fb5eee0f63005ac000000002e6c630001ac600017b8000053300000040d1a00154000000000040020000040031800550000830dec6bd3b3cded189bdecd8ef6341dee 18 262143 8 255
def hc_64_6 : Nat → Nat := unpackHintV5 0xb37656640ab09c4f1708499b08809fc94ba1586ac96a92c94e83a76274ec0091cbd091aa0b073e4327c800e7919cf0037c226e414dc801b7022cca244554798f0d91a0c2f014c3803a600007 0x73800000006c380002001000000c6000319c000418540b1e039e79ceb473870f488b5ac5873d0c63469ce1c3d550054cd4700a0162c0e01c8dd050c63381cf55530e458c002804058080000f7ad7a00000318d1a0b5007c00b0220001a3401f3e0000000008d8000200000000c60013c7000083047b55a79e0b368b5ccf3c162c98b5bd6b1a351ad7c2c96b7a4b81bf62c6bdeb5cc2682b5c40d46366ab16f3802c0390000d1ab0003c11f7b4d81ce06e6b316000001b800039000d1bb37502fdaf411ef07873d2ec 19 524287 8 255
def hc_64_7 : Nat → Nat := unpackHintV5 0xb3393515526c36cd30598e19139e5f0373825e65ca8977452c02a560246a42890450d05218023fa367e014ea1218e46270ac4a8388e0709e7e1241824800420708400108001c44c36028006c 0xe739c00000d80001c00400200e000c6000338ce000080c600000aa000000000aaaa0000000739ce78f000000718c068ddec580001ce7380000001c00018c6719c0000e739c000000006300019c670000aa000000000818c002a80001540000000154001540004000000e739c0e0010000000006c00e0c60318002000338ce00f366cef09fbdbbdbc366c49fb00a10000400007cf8000631a34002a80000000063000aa00788f67a7a803cef38000100041c0001a346f19f61df03003c1b007bc00000000e00318000de300 19 524287 8 255
def hc_64_8 : Nat → Nat := unpackHintV5 0xf580bea80bc60f6ddafd0ab18e532f0ac540a19ea973cc0a55a448c1f8f6231c42a37814541b77f2aed429c812b8b056de38ca5199202ae83c528a8786ccdb1599a1c2b084296cc2a2880054 0xb2daeb60b004005cd572e0136a0a802c58aa31a8c6a30468d1462000aa00000000aa000aa00aa00aa000800000aaaa00aa002000000aa000aa00000aa0026c00000040000200000550005500011040011f3e40d80000aaa2083d55eab162d6aaa9d5efb7bdbbded616d6d8b001411155595415404d802c58aaaaaa82aa8a6c7bd8b227a3da9408d18002e7c1b44016aa09b5a803c00000068d005500000000550005500000500001360000000000100002a8000d1a0800080c602c5edf0bd9c45ed66c0586c43620052c01000102601ce0000100006c0000e00318000300118ce000000739e3c00001c68d0005500000000550005500 19 524287 8 255
def hc_64_9 : Nat → Nat := unpackHintV5 0xc7ad576d8ab8b551d548b785158161496bd1586f6acdc02db1072f36f5ba2cb74016a04ad4005a800b18396082a40813117059090a58c905461c4462f494518d0891a10e041f42817278002e 0x1e3c000000000031c71c0000000078f00000c6000011c7001e3c000000000031800471c0000aa00000000aa000aa000200000078f01c002d8000000000000c603180020011c7006e8163c151ceb473870f488b160c63469ce0154000000003180055006c05c8e05a800000b16004040400d1a2c65001cfb8590f61c3d55004b59c0e054318ce073d50d630e1eaaa00b74cd4780000820a22806319c0e7aaa98720c37300362d059b5a130016f9f000000d1b02f73f62f72c2d8b46b9fb58cb58ed66c6883c5adef445ac68d18cef3ae7ef6b0 19 524287 8 255
def hc_64_10 : Nat → Nat := unpackHintV5 0xb6c7ab0d5fa32dba0b279ef1c9975897d1a9631a961029124f84bc77f3587926172b67675b66185d616025ce4852da14db5248d4e42a6334ddd2f95420aef1c842174540c9ab075540116400c050000c 0x643882f8f6ce779d62c3bce71a3463000001f2e581b0582c068d060a26c0553a739c0f399e99e04002730981c1546228c6a31a8d1a232dcc20fb9ec779b7b1e70477d1ce88b161ce346ede3d726e56f79042c445ad6b7ac68d18ea3a9c38f9adb5a54f1e578f0e79ef95463518d468d946a3468002a800000002a8002a8028a1c0f04aa739cf54a75555555556a954e739ea9553aaaaaaaaa75b6ab54aa74456554e739ea95454554eaaaaaaaaaaa28aadb39ce1c3ac587555511016b1e2aaadeb555554545555556d9e3ca2a2a9cf3df2aaaaaaaaaaaac1c3aed94f2c593d54eaac0e074159cf54738d1aaaab54aa739cf54aa9d555554e9d39e956dc7aaa8f114aa9ce73d555142a8ce8d3cb2d33431a8d1b43ce6cea7d8a140f39cea1c39ce74e9e751e3c70b61400001c0e7080e0318ce0738c674633b1c703000029980000068d000550000000055000550000aa0b600008004000000000000c6001540080c60000000aa000000000aaaa000000078f01d3a000003180d1bbdcf 20 1048575 8 255
def hc_64_11 : Nat → Nat := unpackHintV5 0x11e151dddeb5962612a097ea905aa1b3582bea841d6057ac000af 0x55000000005500055002609b0000ea7020e0000000000000aa0080c60000234680220c703aed8e7558b0ef3aaaa000003e5c1b404160aa826c14066aaa7381d595410005040e0aa82aaaaaa8a2a80000000002aaa800000002a800000002a8002a80000000002a80002a8002a8002a800000002a8002a80000aa800000002a8002a800200009b038004aa000000000000008c001550005500 19 524287 8 255
def nh_64 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_64_11 (Nat.sub p 352)) (hc_64_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_64_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_64_8 (Nat.sub p 256)) (hc_64_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_64_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_64_5 (Nat.sub p 160)) (hc_64_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_64_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_64_2 (Nat.sub p 64)) (hc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_64_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_64 : Nat → Nat × Nat := unpackForestF 0xb484800b4fb3235b313500b4bb025cb0250b015cb0150b005000b47aea35ae93500b43aab53aab4baab49aa94baa947ab341aa94500a4fa8928a8925a892400a4ba6b51a7359a695d00a47a4a5ea4925a482800a43a3a5e00a3fa225ea202800a3b9dc589dc529f83b9f8339dc509d94c9d9409d84000a379ca4695b5e95a5e959289a35e9a252959259624e98b5c9614b9735c9701896143960139592400a338e3538e34b8e3498e25f8e2538e24b8e24790b5190a428e2458e23f8eb548ea548e2330094f8c13c8c1368c1340094b87b518ab4987a5d87a3f884608836c8826c87a330094786a548335f85a34833538315e842528313683018009438125f812578115e0093f7f95e7f8180093b7b4587b4527d03b7d0337b4507b24c7b2407b0400093779a54799546fb5f77c6077a6c7796c6fb57769466fa5e6f95e6f93c743527415e6f9367024b728287024371149711417014e700236f934009336ea466db5e6da5e0092f6c9466b25e6b15e6b1360092b6a3485ac5b693485ac535ab5e67a4c5ab5b668285ab5363c5963c516382a64240638265ab525ab4e5ab4361c525ab4260a325aa5e5fa3e5aa525da325d95e5d9525a95e5ba5e5ba525b93e5a9525a833009275824b59028582435802355a345694956941561245595e009233e34f540343e34b51d6051a5c51a505185c3e3474fa384fa344f8343e3433e24f4e0243e24b4bd604bb5c4bb504b85c3e24749a4c49a44498243e243488343e23f478243e23b464604604c3e2374434444a34440243e2333e04e4134242124412424112d3e0363ea423f9343e9423e93a3e0260084b27b4f3c83427b4b3a5603a25c3a2503a05c27b4738238382343803427b4327a4f3682427a4b345603435c343503405c27a473224c322443202427a433103427a3f3002427a3b2ec602e84c27a372d83c2cb442c82427a332784e2a3422a24a2a12127836282422814a2813227826008431f34b1f343258451f14f2485d1f147239451f04f2295d1f0471fa5e211341fa521f95e1f85e1f0170083e1e01c0083b1cc501c84c1b2371b0361b026008330b34e0b3430b342189450b24f17a450b14f16b4810c5210b5e14c501482410b5210b4110b4012a3010a5e11a301095e1083d0b1270e93d0f3400e9250b0270ba3a0d3500ba360c3400b9360b017008320724f09824072430704e07a4207942070260082b06026008230234f04834023430204e02b4202a42020360081b01036008130001f 9 11
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 3 7 bds_64 362 (dagTraceF m_64 s_64 8 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 3 7 362 bds_64 (dagTraceF m_64 s_64 8 f_64) (cur_64 0) (nh_64 0) s_64 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 64 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_2 : treeBlockF 64 96 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_3 : treeBlockF 96 128 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_4 : treeBlockF 128 160 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_5 : treeBlockF 160 192 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_6 : treeBlockF 192 224 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_7 : treeBlockF 224 256 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_8 : treeBlockF 256 288 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_9 : treeBlockF 288 320 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_10 : treeBlockF 320 352 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_11 : treeBlockF 352 362 ch_64 = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 64 → ch_64 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nj_64_2 : ∀ i, 0 ≤ i → i < 96 → ch_64 i = true := block_join nj_64_1 (fun _ h1 h2 => treeBlockF_at nb_64_2 h1 h2)
theorem nj_64_3 : ∀ i, 0 ≤ i → i < 128 → ch_64 i = true := block_join nj_64_2 (fun _ h1 h2 => treeBlockF_at nb_64_3 h1 h2)
theorem nj_64_4 : ∀ i, 0 ≤ i → i < 160 → ch_64 i = true := block_join nj_64_3 (fun _ h1 h2 => treeBlockF_at nb_64_4 h1 h2)
theorem nj_64_5 : ∀ i, 0 ≤ i → i < 192 → ch_64 i = true := block_join nj_64_4 (fun _ h1 h2 => treeBlockF_at nb_64_5 h1 h2)
theorem nj_64_6 : ∀ i, 0 ≤ i → i < 224 → ch_64 i = true := block_join nj_64_5 (fun _ h1 h2 => treeBlockF_at nb_64_6 h1 h2)
theorem nj_64_7 : ∀ i, 0 ≤ i → i < 256 → ch_64 i = true := block_join nj_64_6 (fun _ h1 h2 => treeBlockF_at nb_64_7 h1 h2)
theorem nj_64_8 : ∀ i, 0 ≤ i → i < 288 → ch_64 i = true := block_join nj_64_7 (fun _ h1 h2 => treeBlockF_at nb_64_8 h1 h2)
theorem nj_64_9 : ∀ i, 0 ≤ i → i < 320 → ch_64 i = true := block_join nj_64_8 (fun _ h1 h2 => treeBlockF_at nb_64_9 h1 h2)
theorem nj_64_10 : ∀ i, 0 ≤ i → i < 352 → ch_64 i = true := block_join nj_64_9 (fun _ h1 h2 => treeBlockF_at nb_64_10 h1 h2)
theorem nj_64_11 : ∀ i, 0 ≤ i → i < 362 → ch_64 i = true := block_join nj_64_10 (fun _ h1 h2 => treeBlockF_at nb_64_11 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 362 → ch_64 i = true := nj_64_11
theorem lb_64 : LowerBin m_64 s_64 g_64 9 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_3 (kn_cons lb_44 (kn_cons lb_49 (kn_cons lb_5 (kn_cons lb_40 (kn_cons lb_45 (kn_cons lb_35 (kn_cons lb_20 (kn_nil)))))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xf0f0f0f0f0f0f0f0
def s_65 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_65 : Nat := 0x10105010103070
def ep_65 : Nat := 0x1000202000001040000020600010004000000040000000000000000000101000101030200010105010100040
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_36, s_36, 5, g_36), (m_25, s_25, 5, g_25), (m_44, s_44, 5, g_44), (m_57, s_57, 5, g_57), (m_51, s_51, 5, g_51), (m_42, s_42, 4, g_42), (m_5, s_5, 4, g_5), (m_11, s_11, 4, g_11)]
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b09d2529425088e118421069da0681a05cd615815154150505405014035cd0340c1288a006401 0xb9517941e9394131912f6923cb496132283e5a50bc518a4e5242b14e4142184ea8169b5e925e89525a5071445c507c526b5e625e5252495e415239352034284f1843e343da4ed242c14fa143813f3133103e0832001f 10 1023 4 15 11 2047 16 65535
def nh_65 : Nat → Nat := unpackHintV5 0x12700221acbdd666befcd54298327af80e5e20eba81d4d282930751c0aa241515af21a11434008402905829fc0f3e01879828ea889cb0a2ccca58414b0801570a1a7081b598003680000 0x40d8800399c6718bde800000c013a70039ce7500002e0000004c06351804d66318c6004c00006000ce3d5e0719c61b1e0f00037b459b00781b1ea339c600000b05ef60f5f338ce37aed7a8c6ab164f7b367def7bdec38c6717b1b37abb18c178e6339ce35558b37b5a0ac1601ee039aa9c67182aad6b58ce718000002a802a8ce7180080000081c06751828ce71802c4187162c 19 524287 8 255
def f_65 : Nat → Nat × Nat := unpackForestF 0xe9390b430a4e0a42cb49094fac51a94ea81609438b5e8a5e8952093f3c5271443b5e3a5e5c503a52395e395239350933184f20341843083e0832001f 5 11
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 3 7 bds_65 30 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 3 7 30 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 30 ch_65 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 30 → ch_65 i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_36 (kn_cons lb_25 (kn_cons lb_44 (kn_cons lb_57 (kn_cons lb_51 (kn_cons lb_42 (kn_cons lb_5 (kn_cons lb_11 (kn_nil)))))))))) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xff00ff00ff00ff
def s_66 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_66 : Nat := 0x170057001f007f
def ep_66 : Nat := 0x800280000004000000060000000000000000000060002000e000800120002001000200014005400100040
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_11, s_11, 4, g_11), (m_50, s_50, 5, g_50), (m_24, s_24, 5, g_24), (m_56, s_56, 5, g_56), (m_46, s_46, 4, g_46), (m_10, s_10, 4, g_10)]
def cur_66 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b0a0e80a021784201711c0701936419064181601715c107401003c4d2340d0340c1288a006401 0x8245ea35512ada5d8a55ba45aa3d7a35d152412a7234c35d8b55bb456a36ac56a356285a72447244945a8c56835a7b566a56185a6042495c534b4347204c2a3f1a37e34bcb47b2479a3f5a37392a3126104a0846001f 10 1023 4 15 11 2047 16 65535
def nh_66 : Nat → Nat := unpackHintV5 0x7a41f8993c107dec3e632b3101918eb723dae16d00f43c9a003ce43a6d0b308c9487c883a3d0ef9ca7b82bdc01e414c0e349ed2441522008c0a2d718b76800b60000 0x8c26b0582d6a000023461e62c0161350000e023460ce622d60084d00101540598758b1566b56870eaaaaa30e8e64e739cc9cd9a0aad5ab30e1d55551ace67014550e70e739c017a8aaaaaa000000000aa08002a8002ace63000050000078008c631a31a0022a802a8022a8008000020008a001c38710688d1aaa03 17 131071 7 127
def f_66 : Nat → Nat × Nat := unpackForestF 0xea350b4bd25dd1520b47bb5dbb450a47a456a3560a3f645a6456635a63567244625660420a37434b495c4347092a09261a3f204c1a37084a0846001f 5 11
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 3 7 bds_66 30 (dagTraceF m_66 s_66 7 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 3 7 30 bds_66 (dagTraceF m_66 s_66 7 f_66) (cur_66 0) (nh_66 0) s_66 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66 : treeBlockF 0 30 ch_66 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 30 → ch_66 i = true := fun _ h1 h2 => treeBlockF_at nb_66 h1 h2
theorem lb_66 : LowerBin m_66 s_66 g_66 8 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_11 (kn_cons lb_50 (kn_cons lb_24 (kn_cons lb_56 (kn_cons lb_46 (kn_cons lb_10 (kn_nil)))))))) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0x3c3c3c3c3c3c3c3c
def s_67 : List Nat := [0x1414141414141414, 0xc0c0c0c0c0c0c0c, 0x3c003c003c003c, 0x3c3c00003c3c, 0x3c3c3c3c]
def g_67 : Nat := 0x141414101c343c
def ep_67 : Nat := 0x10082028000014000000242000140000000c0008000000000000000000000000000000000014141410100400
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_19, s_19, 6, g_19), (m_18, s_18, 5, g_18), (m_17, s_17, 4, g_17), (m_62, s_62, 4, g_62)]
def cur_67 : Nat → List (Nat × Nat) := unpackCursorV5 0xe06c761b0c96430380a9d42653081c0200e270381a2d0682503001 0xb145a25c995d8945795d215519256a4541365a5d225511264c5a415e2850335a23561a561156ab4f9347824f7247614f514739370927001f 9 511 4 15 11 2047 16 65535
def nh_67 : Nat → Nat := unpackHintV5 0xbec31639a2aa1d53c189a4d52e8620f4e406186f914d9061634f2ae184411c80878f809188682e0305c000b0081461a25834202b0023e00004 0x2eeeeec02cecb32c02eeeceaeeed56db2eeeeeeecb7bb6cbbbbbb032cecb0b70002cb9e2ded56db2eeeeec2eeeecbb2ecbb2c2cc30bbbb2eceaeeed56db12eeeeec2cbb2ecbb2eeeecc302eeeeeaeeec55b6cbbbbbbabbbbb3bb2edeecb30bbbbab38ebaeeeed56db56eeeeeeadeecbb7bb2eeeec2eeece3aaeeeee55b6dbbbbbbb2cbbb373b1ee2c00b2e02ee0b055b6cbbbbbb7bb1bbaeeeeec3bbbbbbb332ecbb2ecbb0bbbb2ee2b2ecbbb020bb6c5545b2ecb02cb2cba2ebb2c8552d5b11455b 19 524287 8 255
def f_67 : Nat → Nat × Nat := unpackForestF 0xb1450b4f9a5c995d0b4789450a4f795d0a476a45094f5a5d0947445a415e0937135a28501356125611560927001f 5 11
def ch_67 : Nat → Bool := dagCheckNodeV5 m_67 g_67 ep_67 2 3 bds_67 23 (dagTraceF m_67 s_67 7 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 2 3 23 bds_67 (dagTraceF m_67 s_67 7 f_67) (cur_67 0) (nh_67 0) s_67 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67 : treeBlockF 0 23 ch_67 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 23 → ch_67 i = true := fun _ h1 h2 => treeBlockF_at nb_67 h1 h2
theorem lb_67 : LowerBin m_67 s_67 g_67 8 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_19 (kn_cons lb_18 (kn_cons lb_17 (kn_cons lb_62 (kn_nil)))))) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0x6666666666666666
def s_68 : List Nat := [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666]
def g_68 : Nat := 0x6044602062666
def ep_68 : Nat := 0x200222000000440000024600006004200040040000604020206040000000000000000000000000000000000
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 6, g_35), (m_34, s_34, 6, g_34), (m_13, s_13, 4, g_13), (m_31, s_31, 5, g_31), (m_32, s_32, 5, g_32), (m_60, s_60, 4, g_60)]
def cur_68 : Nat → List (Nat × Nat) := unpackCursorV5 0xa28a28301 0x134b7a3a13888401f 6 63 3 7 10 1023 13 8191
def nh_68 : Nat → Nat := unpackHintV5 0x88201a08047a089c82012600004 0xafbbfebfaffff00f7d55bfffeffae3aabbeaffbaf003cf55ffffaaae3bfffeffabefbefbea80f03c0001f7df7d6555402fbefbcf3cf3c01f57d55402afaa00855bffef3cf3cf007df7df5500bfefbeff8e30055f 18 262143 8 255
def f_68 : Nat → Nat × Nat := unpackForestF 0x74be8f13a2101f 1 10
def ch_68 : Nat → Bool := dagCheckNodeV5 m_68 g_68 ep_68 2 3 bds_68 5 (dagTraceF m_68 s_68 7 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 2 3 5 bds_68 (dagTraceF m_68 s_68 7 f_68) (cur_68 0) (nh_68 0) s_68 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68 : treeBlockF 0 5 ch_68 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 5 → ch_68 i = true := fun _ h1 h2 => treeBlockF_at nb_68 h1 h2
theorem lb_68 : LowerBin m_68 s_68 g_68 8 :=
  lowerDagV5 (kn_cons lb_35 (kn_cons lb_34 (kn_cons lb_13 (kn_cons lb_31 (kn_cons lb_32 (kn_cons lb_60 (kn_nil))))))) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xffffffff00000000
def s_69 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_69 : Nat := 0x117155700000000
def ep_69 : Nat := 0x1440000000000016004200000000010604020000000001121002000000000114155400000000
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_33, s_33, 7, g_33), (m_21, s_21, 5, g_21), (m_25, s_25, 5, g_25), (m_28, s_28, 5, g_28), (m_27, s_27, 5, g_27), (m_26, s_26, 5, g_26), (m_24, s_24, 5, g_24), (m_23, s_23, 6, g_23)]
def cur_69 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3230cd11d30791092028d3e3fe8ef637b8ce93f94ee13764cd52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_69 : Nat → Nat := unpackHintV5 0xab9f09c9f08e2e785f83762fd687db5d0b74fed24906e3cfc12f4db23db716bd20fd6e03cc10003c00000 0xaaaaaa318d554671ece718ce73aaace75ad6b9735c37bc62000000000000aaaaa338f6318c6aaaa338c631aa9ce738c6318c638731c2000000000000aaaaaa318d54e759ce318ce3553ccf1ce78e739c6f78c400000000000155554671ed54e739c6318c40000006002aaaaa8c6318ce355551ac6318d55673ac6318c631c398e1000000000065c001555556a5559ceb5ad635bd635558f6ce7a39cf3a708000000000002aaaa9ce73aac7b75554aaab1e8753eaa1000000000000555555a954ef38ce738ce739d54e759cf51e9d38400000000000155554e739d563dbaa10000000085555559ceb555aa8f552aaacba1d4faa84000000000008b82aaa8c631aaaa8d6318ce31d4aab3a743b631d0c6f10000000000005555578de355aa876ea955565d47a9f542000000000000aaaaaaf5bcef3bd6aaf1bc752ace9c318c63a8708000000000002aaaabdef7aad54fb62000000010aaaaa318c6aab55550e55559751ea1d50800000000001170555555100000000 20 1048575 8 255
def f_69 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
def ch_69 : Nat → Bool := dagCheckNodeV5 m_69 g_69 ep_69 3 7 bds_69 16 (dagTraceF m_69 s_69 8 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 3 7 16 bds_69 (dagTraceF m_69 s_69 8 f_69) (cur_69 0) (nh_69 0) s_69 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69 : treeBlockF 0 16 ch_69 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 16 → ch_69 i = true := fun _ h1 h2 => treeBlockF_at nb_69 h1 h2
theorem lb_69 : LowerBin m_69 s_69 g_69 9 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_33 (kn_cons lb_21 (kn_cons lb_25 (kn_cons lb_28 (kn_cons lb_27 (kn_cons lb_26 (kn_cons lb_24 (kn_cons lb_23 (kn_nil)))))))))) rc_69 nc_69 (by decide +kernel)

def m_70 : Nat := 0xffffffff
def s_70 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_70 : Nat := 0x131f377f
def ep_70 : Nat := 0x246000000000000c004800000000020e040800000000131032200000000010100440
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_48, s_48, 5, g_48), (m_52, s_52, 5, g_52), (m_0, s_0, 4, g_0), (m_49, s_49, 6, g_49), (m_54, s_54, 5, g_54), (m_13, s_13, 4, g_13), (m_53, s_53, 4, g_53), (m_47, s_47, 4, g_47), (m_19, s_19, 6, g_19), (m_59, s_59, 5, g_59)]
def cc_70_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e043121810c08604302006e867403a01b86d816c03601b00cc36603205900b065802c01504a80540280940090448023040c4001 0x103600fb500f0600d0500da5d0d2550c83d11b5210a5f0ea570623d0e13c0c0520a86c0905c070440805e0935508b450813a073560b45f0a45709a4a0785e068460601e0486c0385c03b55033450545f044570285e0204601252b4b4fb334bae347a9b43a2a4fa0a4b9f2479ca439ba3f9a23b98237952339314f921479193f8d93a8c137871367d12f739277004f6b04b67047470434303f3f83b30837270332502f1202b0b827058230181b008170001f 13 8191 6 63 11 2047 20 1048575
def cc_70_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4148280d009c31162044088110201400746e81d03a0740e81d0305600c01802a3540a804884208000800000 0x1d834764d1fb5d7cd55ea4a78919d0466c8e9aa366f149a4506613583555ed1572555a4e96136529294246400da4c5f8f15e335f8ad5e23478692a124680579c9527052991466217d585e5415d38524c11d28463ed550236361811058 11 2047 5 31 11 2047 18 262143
def cc_70_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c1f47c1f0749d0741b26c1b06c192641905c9703e0f03c0f030cc0300a2244721c04304c1000400 0x5b1b2c0c9784ca81a5c4beda4f652fb093d54b6a24b492fa293df8feec6f685cae2a560f2986d40349e124d97a64b92e54903630171fac0f9505c2e3d54968bca45278a92c17940a50445 10 1023 4 15 10 1023 17 131071
def cc_70_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4a909ca6198242901e6781e0709c0701c064d90641905c9705856058151451104411038c4a10004 0x3592fca49fea356e0a9b038f4531a828f68efca37f04df512fc849da02aed163a858e69739244e20a37458da1634028d11435d68d55834a5cce0a32d68c95831b50fd163e452ef143a25fe094f7a4dd857f312fc449d902ab81b2c864aa1130034 10 1023 4 15 11 2047 18 262143
def cc_70_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc05802f0de0b83702e0582b01602b0d60ac11a2304413a8700e01c0342680d01621c8380700e01c038070007 0xa29327d64984d26d3c99902613495512764a9c91a694a9751a593e944ca4d2d924964164cdd772f55c9d2f1f47c592b0e47ba91ae23fb68dec154394e861368012ab847a611a8c3f270ea7837910da3c278b9122748880c236358c4d2292f8749e175f84d4e0e5f828fe0637384ea0052 11 2047 5 31 10 1023 18 262143
def cc_70_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xb86e0b82d18ae207cde16cd92641816017145910404f13c0f03c0f03c0b419460144320842008002 0x1504d2f01261451c14bb7e8d6f8a11e12abd09d7610abc1ad3834280552e09accb249844b906964152c4b25b84c920694a0b68412da25cb20796a936cc97d8927a405f3e09e400bd7a44a926954d06a4a6d40323b0355a976b11ad5935a7268740aa95ae521642006940552852e5013c 10 1023 4 15 11 2047 19 524287
def cc_70_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8dc2e162b0566b15196c86330a8442210ec66295408b441e8e254280d060220c8442002 0x37c56dddb37034da1308036ded776e3fd98df6036d707ad450b4143526cb31434b60d1d42c450d00c3565dd34bf3d27b01031a4ac1918fd3a1b4dab4463e4e86936cc1767444ca0d30134bf913205cac1127034c6d74f53a290ea6836c4172ac44aa112a434c01326024 9 511 3 7 10 1023 18 262143
def cc_70_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0f80e03539be609824290240902138421084210751d0741a3681a05cc8f20080200621805101400 0x803557fb456e8597215e339467e04686c5f85c5b83c57814537f25e7ea467185f6d85b698575c0534504f4104b330472f8437d82976b607c3487b3607a86c7a0607934878a44780487784476c597624668855681564414e748467cc5f7bc5b79c577745375b527534a7085f6c85b678575b0534384f4084b310472e8437403172a5472028713586bc5e732457192f709272002a 10 1023 4 15 11 2047 20 1048575
def cc_70_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0280a02088020074dd068da05cd705c161581332e0b02c0a1280a02445414050140500501000400 0x90a4f8fa438f23b8ea378e136628432182b098238d452618538c841610518b8295d821608518a849140415f8435f1528805e5d8528b3438a14f8992d89127889255d043878332101b8624480a5c8526c8025c8486c840608334482a44820488184480850 10 1023 4 15 11 2047 20 1048575
def cc_70_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xa5a90a068094df67c1d2741d06519064190461104411044110314c0300a219060144411001304001 0x9ea5da015c9f851658412282b0e827390359024a389469d8469ea5e9e2468f94a4204b380479d029899449c1349b25e8f14a648539a82999c529925f8e93a891368893463853988412202b97a5c97254969249602895824369469404694b45938494183b36037928518e13463051910491484190029 10 1023 4 15 11 2047 20 1048575
def cc_70_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x80074660a6005c25c05c05825805425024084004004004004003c23633603603603602c52c00b10a00a00a0043040002 0xa6a4d8412f7a127b082faf827af017b2a5da624d8392f79927b205cb1051ae8502382b0a0230401b8312d78925ac92fac1278212f781278181f77817ada38ad235aba34ab1348112f77127aa838aa034a782da7025a8c5da8051a68509124a8aa463a94611136a4046a935da6355a5b47a5345992379093a8a1366f05966851a484ba3849a3047138414283b3a0372302b10827a2029a1828a10240f13610036 12 4095 5 31 11 2047 20 1048575
def cc_70_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x5f58583c382a281a111002 0x2a52ec352f7ca4e8010492158582305037688d6ce9a42d2f7ba4f0907dea0bd435db186d4fd729d2e5813c 8 255 3 7 10 1023 19 524287
def cur_70 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_70_11 (Nat.sub p 352)) (cc_70_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_70_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_70_8 (Nat.sub p 256)) (cc_70_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_70_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_70_5 (Nat.sub p 160)) (cc_70_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_70_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_70_2 (Nat.sub p 64)) (cc_70_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_70_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_70_0 : Nat → Nat := unpackHintV5 0xf100dd889b7d346f00add809b9023442e594f4ad8515a80aa213500449e8193c80a79004a44e92029089b9e031314ac5d850ba80963122c00657c0499960fd3613ac01d4a00c2e8001800000 0x234b4b01c1d030c30c00000000300155540001234630c34b55830d5c30d5430d000c30c354b5550d5803030c3141c1c0c3030c45051c70055543540050634018e34cb4c3c63578c2c2e0018c2c80c01c1c0c8d74134e80000005d357530238e34cb2d30c0000000c043430c3018c315c3423404cb2d3830e10000c3000000000015d5d0d0c0018c0000b020000000008e34cb4c3c63578c2c2d74134e800000070174d1d1c132cb4c0000c80030010d0c30c1030c00000007000015d5d0d0c00018c0000b020000000007030c003020c380001415430c30c000002c00030200000000c0000155540001000631c71c71c71c7 19 524287 8 255
def hc_70_1 : Nat → Nat := unpackHintV5 0x910151e83a3607466068a428fa9a1c23336c186d800db001a6103460661c70bb08973032e4025b018b60016c0027e5a4b844970012a042163e3ec40629b0527304c5808018038c8030400006 0x18c2e30b8c2d8cb8c30d72cb5cba555c5e35c02c0b030cb2e0e35e50d75038c302088cb2cf0c3a2cf58d543000c32cb695748d74cb5d8c74d34d3a4d1071c1c1d74d11178d32d79b4d3936e4c701d74c578e5c3532cb4d70d1036c1c1c30d1030d430c0300707070300575743430635040075cb2d70e5db0e5471c0071c00c34d60c384c0c307075111e32d34b538c1d8c1e3 19 524287 8 255
def hc_70_2 : Nat → Nat := unpackHintV5 0x8b4054480922280d108067f4483f7019f801ce80a06e42e36f019b3820c74946340331303961940a545c426821df1a0d48d85c470220610f10f87800435c3217e180a60c8480581686c054300290080308c0000c 0xa38e357081c8e3a93cf3cfaa3c73c7aaa1c7434366434343438e3579a2cb2cbaa2c72c7aaa1c7430d0cb69a43434343aa0000000800043436600008e8d5cf2cb3d04f3cf3eaaa81c1c71c33e80c0d0d0e38d5ea8f3cf3da8f1cf1eaa871d0c3433da690d0d0d0ea8000000200010d0d980002a8f3cf3ea8f1cf1eaa871d0c3433d6998d0d0d0d0e3ea8ba958aaa21e1e22a838030c30c383800000000315554030c30c00000003000155540000030c30c000030000300015554000030c30c000030002c02003000000300000001555418c001008c3578d32d33cf4d8d5c38cb2d72e35d8d32d2d4e307578d2d4cb8c578d0da6d00c30c6341c32cb830e51c71c7003000c030c2342cb00830e1057430d0c0030cb2da548c 21 2097151 9 511
def hc_70_3 : Nat → Nat := unpackHintV5 0x7b130f20418f553100e62000bf0517b03262944c00496819181522e024342883830f6111806c2fc045e018ac10152062941052800a50014a0025c384a018910311c062142409b900e050001c 0x830e830e2cb2cb830c30e2c72c71c75555555553070e0e5830e4cf3d34c131cf1c30c1c1d2d3d5592d55633d4c72d8e0c3a0c3934e0c30c3931c71c755653d5555554cb4d538cf6363238d38cb4e3128d4cb2d3030c0c350c307071c7445532d3123638e344078e3638e31238d52d550e0e50cf3d454830e1cf1d1511e0c30c3871d4f55555663555568e8e3081c 19 524287 8 255
def hc_70_4 : Nat → Nat := unpackHintV5 0xcc830cc800ca014ca000c9406c7c0cc7006c5c0ac5006c5000c4c02c4006c280cb6064b480cb2c0e8c5348046075c54758027241a7200271c026e41c52cdc4b03e46824420243c82c3901c2848600142 0x4b4c72d5c4d34e8d71e31e326c7071e3419b6e4d34d301c1c70b0b5d78c71c1cf0c32c30d32cb4c30d31cb1c31c31c752cb4b53c3433d5d5d5d1d50e4c384d3071d301c72cb2cf2cb3c88f3d681c1e93d125402a880000000154015401407238d011c8e36a93d52d593cf3cfaa5450f1cf1eaa91471d451c7554f6635555555633d7632d30d70d38e35d170c8d763170c8e35d170c078e30c17a4cf0c34b0d0e970c30c34c4db0701c33c3838f3e0c3873c7830c30e1c7433d0c36635a43430d0d0c30c32c30c3543036c30c3030c303031ea 20 1048575 9 511
def hc_70_5 : Nat → Nat := unpackHintV5 0xfd02bec08fb003e20ada9e36802ce8bb3a00c806af42cbd002e60eb9802d412872e20c10760d1c414678997a245e00976025c0191a5616308580011050202408000200006818001a 0x2c1e870fa1c33c34b0d0c3a0d420e0c38032c4cb8d741301e304c1ca50c37df0c3638e38d355655430c30d5430c30c30c71d5f8c30c30c30d34c74c70d8b90c34b3d930cb8d2e38c3e30e30e31c78c38d4b3e0c71cf6db4b0d0c38f0da90d3e0e8d30cf6c6c0c1c1c30c34b0d0e434f0cb83838c37d8e34d2d72d4c8df478d3 18 262143 8 255
def hc_70_6 : Nat → Nat := unpackHintV5 0xe0452e0400e0400dbc24db006d741ec4498b5478851827607876000738147380072c06720066f8144d114408643f808308782f8082883828800204421f00a0dc8a0d80205442048060340a034000001a 0xa2cb3cf53cf2cb3c0132cb8e30b07238e35702c523cf8b2cf3cb2cf3c1c1c71cb2cf3c4c5d75c30d32c30d2d5435d5830e130701d2cb0c32c30cb2cb2cb0cf3c32c72c70c73cf3c31c74b6352cb433d3c3575757475438b2cb3c38b0b2cb2c1c72c2c1c72cb0b2c0c30e0e2cb507070c352d440d5101e34d310b8d52d0d55830c30c30d4542cb2cb0c30c3454472c72c70c30c30c31c755552d50d55555a2cb534d4f3d044c4e34c02cb63a2d33cf2cb3cf4b2d4f3cb3cf002cb073e34cb0c35d04c2d33e30d5c34db4e123a3c71c31d2c343a0c70d60c38071c71c32c2d31e30d5c138701d048cf0c36c 20 1048575 9 511
def hc_70_7 : Nat → Nat := unpackHintV5 0xb404aa686ca68009c452898968601c85c0281c2081006804067f8067cc167b80a7901478406760127102870c026ec106504e5985c570144c4563b8862b8802b8002b8002801c274062381e00d1600006 0x134e800000071357534cb2d3000007072001c005757071c5d7004cb2d397800000000000b020000000701c002300000001000078c3c4e3a32c21c8e38e38c2c8c8e2d3a38cb4e38cb4c2072308d5d300938000700013575304cb2d300007000007257572d3231c05d7004cb2d39780000002c00008000000001c0000008c400000013130e0e0c354d30c307070c31c74455407238d8cb4c18e350c30c30c3564354cb2d3545030c30d31cb1d11d1430c30c30c71d2d8d555554355554b 20 1048575 9 511
def hc_70_8 : Nat → Nat := unpackHintV5 0xe38bda91e321315a0a2a50f12c1e1e1773c2006c4c0d880181302a65c4490465240ca0013460174f4228c0440106e1a0dc001a0182e06038240640c0a028110301c060003800000000000000 0x3e2303c2c80007071c030343cb2cf03cfa888c71c001c743430c300aa08000000030c30c02a800f8f8f3e871c71c71c71c71c33c3830e0c30c70c73cf0871e0000708c701c0003d357530c00d70c30408d32cb4d0c3400400000b00f8f8070000000000070070001c1c88c000033c310020c38000c001c2c233cf0700b871e000003d40000f3cf8f81c232c2c003d402a8200002030c30c02a800f2cb3c00f8f8083e0220234343830e036cf3db00000003c2000033c30db0db00000c03000d0230c302cb1430e0000f0f8f871c70f00200cf0c30830e03234cb4c3c078e8e01c8e32e38c2c2c1e38ea38e38c80723 19 524287 8 255
def hc_70_9 : Nat → Nat := unpackHintV5 0xe62b86fc1ab638d5b1802d3e276412f3078c9660eeabc3a5241d2601911d0988b01c40e251bea44d2c6462e342e31a1588c8a1458440651ec1a0f58046fc582ae681271805c1bc170b80b8000221d01100000044 0x2cf2e2cb2e2cf2cb2cb2cb2cb00b233c3cf3c0b071c072c71c0701c1cf0f1c00b4b2cb4b2cb2cb2cf3cf3c0701c0f2cf8f8232c2c0003c2d357533e8f3cf002c8c000003c057573d0134d7004d5397800000f2cb3c002c8c0008000000000000004cb2d33cf00004002a80020000000030c30ea80002aa3ea2e803c3c223a0a6c1c1c28882871c8a000c30c3aa9839a030c0c0303cf3e3e08cb000b00003c3d357530c0d70c308d0132cb4d0c340040003e3e003c22300002c06c0000000000000cf0e0c380030010003cf3d3824cb2cf8e2c3e81c73cf07073d357532d33e2e9b8cb8c0c30d70c3570d8c31d32cb4d0468381c070d76db3cb3cb6cf8f800f3cf2aa0223070701c701c701c2000cf0c35b6c35b830e030c30301ea80000002000030c30ea80002a800020002000030c30ea80002a800000002000030c30ea80002a80000002000030c30ea80002a800021555400002000002a8000088c3c00b008000020000001c000c30c3aa00000c1000878703cf00007200701c0057574070134d7001d47978000001c3cb2cf02000000000001c8c00001c00004cb2d30040f3c0000070b2cf3c011c763cf800000070f0022cb2cb00000000000001c8c0700004002cb2cb3cf3cf0000aa0f00b0200000000000088c000000c30c3aa00310000003cf3e3e2c8cb0b2c71c71c71c0f502c8cf20f0001c704 21 2097151 9 511
def hc_70_10 : Nat → Nat := unpackHintV5 0xd440363a342c12e154064a0c4a50301a7d025278b88d8324182a1ec100d291c6263731001984020c2000610002f609168098af0285043a271089380048fc6245c111a9428b490048c8c1d6380783981a11000068 0x232e8ba2cb2cb2e3cf8b1cb1e1cf3cf871c30e2cb2e3cf975c75c7a8b2cf2cba8ba32cb0b2cb0b2cb2cb8f3e2c1c72c1c72c72c7873cf3e1c70cb4b2c34b2c30cb0c32e0c3830c30c7aa000000080000c30c3aa0000a3c0f823cb2cfaaaa07071c70c343430c30c38cb4e3aaa3cb2cfaa3c72c7aaa1c70c30c30c3aa0c30c30c30c3aa000800000000c30c3aa0000aa3cb2cfaa3c72c7aaa1c70c30c3aa0c30c30c30c3aaa555553cb2cfaa553c72c7aaa551c7aa8ba38faa3cb2cfaaaa2a0f1cb1eaaa2871e8a1c70c30c30c3aa9a0e9a0c30c30c30c3820fa34e2cb2cb3c8cf00f3d4f4e350e3a2cb3cf432cb3e80b2c0f3cb2cb50b934cf8cb884cf3cf2c2c2cb3db07073cf57578d34d32c54d35d71c7149782cb0701d34cb178d35300f2cb3d36cf8f82c8cb2c0b2cb3c00701c071c071c1c1c0132cb4d354cf3c0701c0f0b2cb2cf3cf3c00012cb63cf800000b2cb2c00000000f0000b2cb2cf3cf3c000030c30c0000315554000003000000b2cb2c2c8c0000f02c200f000000f00000000b2cb2cf3cf3c0000100000003c2cb2cb000000002cb2cb3cf3cf003cf2cb3cf5d063cf84c1c072cb 21 2097151 9 511
def hc_70_11 : Nat → Nat := unpackHintV5 0x7e16a7086c640644191433074200981d81404cc6028120280000014 0x2a8ba32cba2cb2cf2cb3cf3db3c3cf3c8f3e3c72c73c1c73c1c7873cf3e1c70c32c30cf0d3cf0d3e0c3830c30c7a0b2c822cbaaa07070c343430c3aa000800000000c30c3aa00008ba3aa8baa2cb2cbaaa8a0b1cb1eaaa2871e8a1c70c30c30c3aa9839a0c30c30c30c3883c3c2cb2cb3cf07073cf1c7575755550e0e552cb2cb830e552c72c7830c30e1c7072d7a2c30c3432c3432e0c3835c35c35c31d6839430d170701c32c32e34b1d7 20 1048575 9 511
def nh_70 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_70_11 (Nat.sub p 352)) (hc_70_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_70_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_70_8 (Nat.sub p 256)) (hc_70_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_70_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_70_5 (Nat.sub p 160)) (hc_70_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_70_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_70_2 (Nat.sub p 64)) (hc_70_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_70_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_70 : Nat → Nat × Nat := unpackForestF 0xb4fb3a35b393400b4baea5dae85cb1836ae851af02fb013caf027af017ae85000b47aa238aa235ac12fac127aa234aa134aa038aa03400b43a335da6c5da6851a702da7025a6850a3355a3347a3345a304ba4046a3049a304700a4fa1029a1028a102400a4b9f95c9f85100a479d25e9d2469d8469d02900a439c13400a3f9aa5e9a82900a3b98c5298a5f9884100a3795a5c95a5495924958289582400a3393b4594046938490094f92851009470093f910498e24f900298e2438e23b8e2378e1360093a8cc528c841009378b82987b438a8498794f8792d87927879258805e87833009367dc5f862447dc5b8426c8406c840607dc5781b4481a4481848818447dc53808507fb557fb457da5e7da467e0467d8290092f7445f7c3487445b7a3607a06c7a0607445777b4877a447784877844744537645976246743527434a74846740310092770a4572254720287092f71358709270084f6f8566bb5d6e36c6e0346ba3f6d04c6ba376b8366b81e0084b67a5d6a26c6792f683606835068030679270084747b5d6605d47b556503447b4b6405c47b476335d47a4a6205c47a475dc515da5d6004c5da355d9425d84e5e0245d84247a465c83447a3f5b84c47a3758a4d5a25c5892f5903c589274795457a444784753a5d53a3553935543415414d54032539344784652b5c521644783f4fa4c5025c5013c4f964478374924a492464d93c4914a4c2404c134491464913e4a944491324912d491254783648164478270084343a354393445a444392f4434844030439270083f4035f403534025f4023f40237400520083b314583ea35314523c23b3d14c3c2373c137314503ac583a8583125f38a5c38a4438828312533124d36c58368583115f33d6833d6033a5c34450338283112f31d6831d6031b5031127008373003427a3f2f04c27a372d92f2d9272785c2c12f2c127278542783c2a12d2a125278362892f2892727834278240083325a5e25a5c25a540082f12c5f2406c12c5712b5f12b5712b4712a4a12a46208451295e1d35d1d3551d24a1d2461d9341d046129521294a19c521aa3a1aa3619c501984d129461285f1635516345162551613a161361285e128571424a142461285212847128460082b0c352110580c25f0f3600f3500f0600c2570c13c0ca5d0ca550c83d0c052008270645f0a86c064570624a08355083450813a0605e07356060460601e008230245f0486c0245703355033450205e020460081b01252008170001f 9 11
def ch_70 : Nat → Bool := dagCheckNodeV5 m_70 g_70 ep_70 4 15 bds_70 362 (dagTraceF m_70 s_70 8 f_70) cur_70 nh_70
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 m_70 g_70 ep_70 4 15 362 bds_70 (dagTraceF m_70 s_70 8 f_70) (cur_70 0) (nh_70 0) s_70 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_0 : treeBlockF 0 32 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_1 : treeBlockF 32 64 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_2 : treeBlockF 64 96 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_3 : treeBlockF 96 128 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_4 : treeBlockF 128 160 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_5 : treeBlockF 160 192 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_6 : treeBlockF 192 224 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_7 : treeBlockF 224 256 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_8 : treeBlockF 256 288 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_9 : treeBlockF 288 320 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_10 : treeBlockF 320 352 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_11 : treeBlockF 352 362 ch_70 = true := by decide +kernel
theorem nj_70_1 : ∀ i, 0 ≤ i → i < 64 → ch_70 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_70_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_70_1 h1 h2)
theorem nj_70_2 : ∀ i, 0 ≤ i → i < 96 → ch_70 i = true := block_join nj_70_1 (fun _ h1 h2 => treeBlockF_at nb_70_2 h1 h2)
theorem nj_70_3 : ∀ i, 0 ≤ i → i < 128 → ch_70 i = true := block_join nj_70_2 (fun _ h1 h2 => treeBlockF_at nb_70_3 h1 h2)
theorem nj_70_4 : ∀ i, 0 ≤ i → i < 160 → ch_70 i = true := block_join nj_70_3 (fun _ h1 h2 => treeBlockF_at nb_70_4 h1 h2)
theorem nj_70_5 : ∀ i, 0 ≤ i → i < 192 → ch_70 i = true := block_join nj_70_4 (fun _ h1 h2 => treeBlockF_at nb_70_5 h1 h2)
theorem nj_70_6 : ∀ i, 0 ≤ i → i < 224 → ch_70 i = true := block_join nj_70_5 (fun _ h1 h2 => treeBlockF_at nb_70_6 h1 h2)
theorem nj_70_7 : ∀ i, 0 ≤ i → i < 256 → ch_70 i = true := block_join nj_70_6 (fun _ h1 h2 => treeBlockF_at nb_70_7 h1 h2)
theorem nj_70_8 : ∀ i, 0 ≤ i → i < 288 → ch_70 i = true := block_join nj_70_7 (fun _ h1 h2 => treeBlockF_at nb_70_8 h1 h2)
theorem nj_70_9 : ∀ i, 0 ≤ i → i < 320 → ch_70 i = true := block_join nj_70_8 (fun _ h1 h2 => treeBlockF_at nb_70_9 h1 h2)
theorem nj_70_10 : ∀ i, 0 ≤ i → i < 352 → ch_70 i = true := block_join nj_70_9 (fun _ h1 h2 => treeBlockF_at nb_70_10 h1 h2)
theorem nj_70_11 : ∀ i, 0 ≤ i → i < 362 → ch_70 i = true := block_join nj_70_10 (fun _ h1 h2 => treeBlockF_at nb_70_11 h1 h2)
theorem nc_70 : ∀ i, 0 ≤ i → i < 362 → ch_70 i = true := nj_70_11
theorem lb_70 : LowerBin m_70 s_70 g_70 9 :=
  lowerDagV5 (kn_cons lb_11 (kn_cons lb_48 (kn_cons lb_52 (kn_cons lb_0 (kn_cons lb_49 (kn_cons lb_54 (kn_cons lb_13 (kn_cons lb_53 (kn_cons lb_47 (kn_cons lb_19 (kn_cons lb_59 (kn_nil)))))))))))) rc_70 nc_70 (by decide +kernel)

def m_71 : Nat := 0xffff0000ffff0000
def s_71 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_71 : Nat := 0x1170000131f0000
def ep_71 : Nat := 0x12080000000000000000000000160000000c000001060000020e000001120000131000000114000010100000
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_55, s_55, 5, g_55), (m_37, s_37, 5, g_37), (m_39, s_39, 5, g_39), (m_56, s_56, 5, g_56), (m_1, s_1, 4, g_1), (m_58, s_58, 5, g_58), (m_38, s_38, 5, g_38), (m_14, s_14, 4, g_14), (m_47, s_47, 4, g_47), (m_18, s_18, 5, g_18), (m_12, s_12, 4, g_12), (m_10, s_10, 4, g_10)]
def cc_71_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xe41c07616c0d81b0360682d0198730660cc198330622a1309e10401801002003e16c8d81a0b40642c801c001 0xf3501f6b43ad5865a80c0501605022170402a0da4f1a4962e91c55218412e140962610c481587823296be50d6c91ab903530747c384f8380a06244080281716c29a184a4e072840a0500da15134fa06973cd1e75a1cda4f9a4971a91e0921c0a3f7f476f28ddd519b994f71296d051d98a1ae93f51276564dc34998312f042560449c04918001f 11 2047 5 31 11 2047 19 524287
def cc_71_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0ac0a8a64982609826090a4090222791e0781e0745d0650fa3c0d22c89224090114401003100c00 0x70d41f85c6ad31e83482d7a035a7cd59e35270d41b85c6a931a0247493dca4b6c91d9a435e941894f6052d71475a50e84589f1426a5f9896e42578694e124c76905924058131515436050f94c34050f13c320513c604c5b0e93c4a1b0b814440b11934420d0a814 10 1023 4 15 11 2047 18 262143
def cc_71_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9141200f97c3e1f0f871b81c0d2682b550a85424d0480391a48a401c8e05405000000000 0xc0972f824ca97f225bc295ef253b8552cc60b05b2b86caa4d2a034b6d7ed35bacd5e9b53a44fa745882901884c80d41805c70901784c7e4c25c6094d81f240921b1704c6a901ea408a501e3508e972324c5a1722024 9 511 3 7 11 2047 18 262143
def cc_71_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8c8c8c8c8a5a0a0a07d78717069685a584a484848331b181110101010020000 0x3f458fb143e14cf6503d04cf116fba57d255c513fec49fa349e44fb6241e08e75b42dc93b6460d6d83526cded476a51d28cf3814c7183106c 8 255 3 7 11 2047 18 262143
def cc_71_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe87a0e8355c5310b52d0b42d0acab0a4a54942508517a585425014050140489204809909c1104001 0x13e94671a4b293f5b2769a4dca499b214f5a2969851ca0a1b194d59292945149ca09c240950983c4f24c0a4b93f96277284de4899b102f570569209c9411ccb5c986a322d4240ae479506127eac4ed209b921338e0b91409180a6a3145880310e05229a4c493b86266be0fd501da2037210670a07e1009c64598b49cbc53d4ca5a1947202870609201a74023e 10 1023 4 15 11 2047 19 524287
def cc_71_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x28860100 0x28c448c945e243a18e42d2f 6 63 3 7 10 1023 18 262143
def cur_71 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_71_5 (Nat.sub p 160)) (cc_71_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_71_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_71_2 (Nat.sub p 64)) (cc_71_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_71_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_71_0 : Nat → Nat := unpackHintV5 0x84c00422021fe098fd40e7e4033f2001f780cf90167c8003de031ed80cf60067a6053d3001e9800f4006736353402d9a0000c903861e152df1816d810b0c3045a961d72b0b01dc47c8211c910103f00004000000 0xad2cb4c30d31e87555500ad1ebaeac75badbadbad2b8b8b2e8b55558555b6c701b6d022e2cba2d55559ad5553543547554f5540000000000040ad30c31c32d1ebadf9947ad1d30c34c71cb7e6471c7475402969534753c7410b2d73d73d73cb2c74c70c70c71c71e1e1c75471d1d5c71d1d4f6b1c751c71c0000000000000b2cb2cf3cf3cb2cb2d55553c5575d75cb2cb2c07100b2cb2cf3cf3cb2cb2cb2d55553dad554d50d52d5951d5400000000000402d73cb4c30d31c7961c71d2dac7474000b5cb5c71c70c70c74c71c787873cf3cf3cb2cf547474747471c71c754f6b0000000000002cb2cb3d73d72cb2cb2cb57554b55554f6b5354354b5654755000000000000000000000 21 2097151 9 511
def hc_71_1 : Nat → Nat := unpackHintV5 0xe484b9200de8631664c401b0a06c28030a00be04af800be002e612a198280069e81a7a00978724c12741f110c044000e42c30090a020228587812108d82e140b800220c020680008 0xab1d2bae472a930c34e5aa87474747400002baeac74ad472aa6874769187474000000002bae76eac76b6e79db9dbaa406e79dbaa1d1d1c0911d1da83aa4eaa568faaaaa1d1da1e959ac747400800000000000ad1eb4c33d4aeb3c3574ad30c3ac83adb2b6e3ab1dad0d4c33c2bac6eb6ebad350ad 18 262143 8 255
def hc_71_2 : Nat → Nat := unpackHintV5 0xad0511b3f236004561685c510a01a0b09410067dc44fb801ee093b02c6d888b3a792f381ee703c8146e8a8c51816a202a0344b0907b1b0e4121b018348185a0f07e3601ce002018000400000 0xae1cb2c7ac8b8b1cb1c31c31c754ba2c71c72c72c71c74759ae96a1c7474b000000000000aeb3d6bad30c3576b0c3aebab1dad0d2b4c3aeb474c34d4a4c30d3aa59555000aaaa5566b55555354356554f55400000000000026aa830c30e4434347474000000026aa934d34e447474747400000002ae0d3a3eb3eb034eb3d7a0eb20ebab5b034cfac8db0d33eb83834eacf1dac2ae6c4ebac34cf6eb0d3acfa4ead1c2a8f3cf3e68747644747400000002bae 19 524287 8 255
def hc_71_3 : Nat → Nat := unpackHintV5 0xc14405c6222c310155064a045248d3aa36085164268940f3b9489c18d8bb12e5783024b3892580086464432001e31b0eb8307341439a001b00e892a2c324b809c7b0380b0130480880803e030070c00181000006 0xaaa20c30c3aa0c30c32cb2cb00000000aaa88f3cf3cfaa2cb2cb2cb2cb000000001c71c7aaaa3cf3cf1c71c7a200000000aa3cf3cfa8a555555000000005d75d7aa803cf3cf3c0a22cb2cb2cb2cbaa2cb2cba83aa4eaaa8f3cf3e8faaa3eb2cb2cba1e6a9aa2cb2cb00200000000002b4eb7cf4c30d33c38f5eb4c35eb64b1cb97975cf5cf5cf3ea8fad74df0c35d33cf3ea5cb2cba2cb2cf2cb7c72d1cb4000000000000b4da471cf5cf5d471c343472c0152c30d31e1c7871d30c34c71c75c73c71d72cb5d0dac30d430c31d1d1c747570000000000000cb0c30c30c32e8b50d555000c30c30cb0c30c32cb2cb436b5555554352d59554f55400000000000030e5830cb3cf7d471c747400030d70d43a7c30c30c71c7474002bac31eb0eae3eb0c37d30eb47543830c3830c30c30cf0c30c30c30c30d72cb0c31c30d50dac74747474000000000000b0cb0cb2d30c34cb2cb2d51555d54700b2cb2d75d75d00b0cb0cb2d30c34cb2cb2d550dad555d551d4b5655754f55400000000000402c72c7ad1ebac70cb0eb6bae2c30c7ac76b1aeb 21 2097151 9 511
def hc_71_4 : Nat → Nat := unpackHintV5 0xe8c6b69e543340d973d32a5ea04f11f2559192a00694a034a50024c035260009160d439291f1958e947c68e5e29d5513d8889345c4820c23a0391d0008e80046e032340191880c758b626e9f0a04b8378c4000de 0x283aaaa0eae3eaa0c30c3aa879a90c30c3aa2cb2cb000000000000a0c383aba830c34c35c34d35e5e5d74cf4d74cf4d34c32c32cb2e8b4c72d4c72d5cb5cb00000000000004d34e933cf3cf3cf0e0e1d1d0003d33d30c34cf8f3e3cf0c33eb0c33cf0c30cf3cf3d30c34cf1cf4f1cf4f3cf3c000000000000030c30c35c30cfac30c30cf5cf5c30c30d70e0e0c30d30c30c30d73cf5c30c3431c34000000000002a830c0ea830c30ea8b2cb2c0000000030c30e0c3830c33cf3cf3cf8f8747400002bac34cfacad30cf030c30c30c3033cf3cf3c30c30cf3cf3c00000000030c30c71c71c30c30c71c71c30c0cf3cf3c0000000030c30c30c0cb2cb2d55555400000000301b8e36c30c30cf0030c0cf3cf3db8e36c30c30cf3cf3c30c30c3830c3830c30c30c30cf0c30c30c33eb3cf3cf0c31c3430c30d0c30c33cf3cf030000000000000130c33e834c30d413134cfa3d34d75e0e0c74740130c33eb4caeb6d30c34d33cf0c33c3d73d73c06db0c04c30d35cf3d76db4c30d34cf3c30c30cfacf5cf5cf3cf4d393934c30c34c30d35cf3d74c74d4c74d0000000001300025e5cf4cf0cf0cf3cf3cf3cf3e8fae8f3ea5cb5cb2e8b3c72d3c72d3cb2cf2cb000000000000973caad30c34e3c0b2c747402aa5cf5cf5e8faeaa4ea0eaaa2cb2cbaa2cb2cba9879000000000000 21 2097151 9 511
def hc_71_5 : Nat → Nat := unpackHintV5 0x5d8a8809d4cd1a06e960006e 0x4c02aa084c30d35d75d7aa2c30cb2cb2cbaa2cb2cb93a0eaeaaa4c30d3a978faaa972c30cba9879aa2cb2cb0000020000000030c30d77c3a0d3a4c30c7474020eae830ea0d30c30c30c35e830c30cf0c30c30c30cb2e8b0c30d0c70d2d72c000000000000283ab0c3a0c30c3aaa2cb1d1d000 19 524287 9 511
def nh_71 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_71_5 (Nat.sub p 160)) (hc_71_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_71_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_71_2 (Nat.sub p 64)) (hc_71_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_71_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_71 : Nat → Nat × Nat := unpackForestF 0xa308802d3e851c80b4b9f4a202d1c05a1ce3490149e0292e39ae473519227f244ee54264913793029244ce39a84715c8e2a11c1700523c1c598349d08d26109dc381887029084ce100fc2013830480290c051fc023e01476f5161ea283d14c7a280f4130051bbb45b764aeec49c0519ba3490129ee44f804a5b8239696a2dc939a528b54606a6c0d49b1a51980947670280250d792faf25b628c0c41b1792bafa5c5f048bc94c049fae154526bea4d6d5e302b96c570d8a4d5d509a2a034526a6a44f8049d964582c8a09d160b12f9625b498c092d81243616257444b88893114a0220242c4a658930f1af1e35a3f0b878d58f41a1e3522c4826693ccd259bb50370b86691cd1261a0243348658900b4a79694b2f4a05a51cb4a19604c0126e5455039af8735b258c04a5b094360735721268440b0841a073531d6b43cd4075ab0713e0f49e1e92c61a80c0500f48e2c0a03d218784b0f0861e0ac402e080540f0461c050049986244078b60ed0c1d270401407284024bc140a0092b036840249c04918001f 8 11
def ch_71 : Nat → Bool := dagCheckNodeV5 m_71 g_71 ep_71 4 15 bds_71 164 (dagTraceF m_71 s_71 8 f_71) cur_71 nh_71
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV5 m_71 g_71 ep_71 4 15 164 bds_71 (dagTraceF m_71 s_71 8 f_71) (cur_71 0) (nh_71 0) s_71 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_0 : treeBlockF 0 32 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_1 : treeBlockF 32 64 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_2 : treeBlockF 64 96 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_3 : treeBlockF 96 128 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_4 : treeBlockF 128 160 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_5 : treeBlockF 160 164 ch_71 = true := by decide +kernel
theorem nj_71_1 : ∀ i, 0 ≤ i → i < 64 → ch_71 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_71_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_71_1 h1 h2)
theorem nj_71_2 : ∀ i, 0 ≤ i → i < 96 → ch_71 i = true := block_join nj_71_1 (fun _ h1 h2 => treeBlockF_at nb_71_2 h1 h2)
theorem nj_71_3 : ∀ i, 0 ≤ i → i < 128 → ch_71 i = true := block_join nj_71_2 (fun _ h1 h2 => treeBlockF_at nb_71_3 h1 h2)
theorem nj_71_4 : ∀ i, 0 ≤ i → i < 160 → ch_71 i = true := block_join nj_71_3 (fun _ h1 h2 => treeBlockF_at nb_71_4 h1 h2)
theorem nj_71_5 : ∀ i, 0 ≤ i → i < 164 → ch_71 i = true := block_join nj_71_4 (fun _ h1 h2 => treeBlockF_at nb_71_5 h1 h2)
theorem nc_71 : ∀ i, 0 ≤ i → i < 164 → ch_71 i = true := nj_71_5
theorem lb_71 : LowerBin m_71 s_71 g_71 9 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_55 (kn_cons lb_37 (kn_cons lb_39 (kn_cons lb_56 (kn_cons lb_1 (kn_cons lb_58 (kn_cons lb_38 (kn_cons lb_14 (kn_cons lb_47 (kn_cons lb_18 (kn_cons lb_12 (kn_cons lb_10 (kn_nil)))))))))))))) rc_71 nc_71 (by decide +kernel)

def m_72 : Nat := 0xffff0000ffff
def s_72 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_72 : Nat := 0x15570000377f
def ep_72 : Nat := 0x222800000000000000000000004200000048000004020000040800001002000032200000155400000440
def bds_72 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_0, s_0, 4, g_0), (m_43, s_43, 5, g_43), (m_23, s_23, 6, g_23), (m_8, s_8, 4, g_8), (m_42, s_42, 4, g_42), (m_40, s_40, 4, g_40), (m_34, s_34, 6, g_34), (m_15, s_15, 5, g_15)]
def cc_72_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a04d02681244900c8023831c0881b53da80d406a03309980cc06212d11680b015802c01504a805402a0140490448023040c4001 0xf3500ea500e1500d1200c94c0c9240d2340c15c0b94420c5a1fa5f1f25b1d2571aa53192411815f1795b1595713153119411092f0f92b0d9270b1230926c0812808256079560a2560995b0895707129061310496c0313c0335602a560535b04357039560213e01232b434fb2b4bb1347ae343aca4fac24ba7247a2a43a0a3f9923b97a37952339394f9214b89947851438313f7813b741376f1336d12f6a92b69927551235484f4b84a48847388462103f0a8370682f058270181f008170001f 13 8191 6 63 11 2047 20 1048575
def cc_72_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0c0c0c0aba8a8a8a88c8888737062606060604b484848482c28281310090801 0xf630785b3b2c1ca5ce1226e4a36249a35ecd2b3a4d718b12940ba305a9b2c4c1515ca4a2504f272692a5e711b4855a24b9015c 8 255 3 7 11 2047 17 131071
def cc_72_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4690a4290a06449024090240812007c5f070dc0701a2681a0609715495050540501130bc2008002 0xbed529938b8db2da6cb49829138b0552b944ac4f2a934a694292569c8fa89569e912714898d2259448e4c24b488c4823a388c8d22954885138356dc97f6a5bd295f2253c08e6f15fba56ec957a854e81399a4be512b9049e192381161a240 10 1023 4 15 11 2047 18 262143
def cc_72_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02719c2709c2709c2348c2308c2125ace8380e0344d0340d0304842008020080110400c43000c00 0x7e0d1ed327a4a9e432780a9d7507491213458394a0a3a8154a013a7f179f4527c115dc44760e9cc36908f63e378e8d631438a4ae2043860adc8136fd518e386cdb18a386b5b1a960689519e44664a19524635418b56619593139 10 1023 4 15 10 1023 18 262143
def cc_72_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x942509425090604801886018060180589334c130485203ccf030cc024c9018c60108310841100400 0x26c4c9ed2a764a9c52a6946a8d2e9f47a58ee8e33a14ee7d339948e6046945b24d549694655519248e10138308634197d04608218b065d8118148a242e7d08a0122870b9d82285171d0347b111e84479111e044 10 1023 4 15 10 1023 18 262143
def cc_72_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0399730641c05802d1da0ac5582a0d02a01386704e0982f21e03a12684048010020028c5008110008c10001 0x3c044c068b7e8eaf89d498457708978922ed1a5c944b928d38169d82b5ba38b50996a492d91a5a05c740895e152c9ad58b569a0b4e615ac027570424507a2e0d6b1a268c5bcf8af9cd2b31a364a4ac548d868d308ad60957bd2ad7453ee0a559947ad28d3216a482bb90564309e2c11eac0bcc0449e2634c4a67090d21299d465444fa70995013e 11 2047 5 31 11 2047 19 524287
def cc_72_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xcf6633191b6da2c360accd6530c843e9e2d456aa12690481b4d0683414c8416080241001 0x39f5be5d5f8d56e04fb7d2e9f16b7125dd91b5a3edb529344f2111f6536b951b634ad751b592e4a13c7c47c44c3534ac3481204f1b11ec954d25121444d05b30154b15121054cb92b2246bf55a785a8215b2a3ac78db354dcbd2b2b46be55a745a8015b223ac78db194dbc4f6dd35c48eaed3fb64dd183f1a0deb0177c151e844 9 511 3 7 10 1023 18 262143
def cc_72_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xc01803005c2b8158eb0560ac1582b056098b30158a624c088910220348680730e01c020c400610c018001800 0x7ea3d7e2357f2517da507d15d7ab567a34679a565105a4385682c578235b8135780b4b803477fa5a7ca566da3e64a327c1577b9567b13f7913e789375c1325085a43056763465ca4664130771285cc507624075950639206fb4d77a4176a3b75237629227484c7316c721547113c722457135670a565005a 11 2047 5 31 11 2047 20 1048575
def cc_72_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2d2b42769c27094a509425088d8a60162581605092240900220802008014c50140500c82100800 0xfc4e23c2647e3f8ec6efb4e8b41f8b0378e04f1a9b2329445e6c8b4a9154a247aec8a5c904a31b942311dc52337ca74590fc561b8442f2c07a290d6201fc3c372b07e280dcaa1f89c37892991151a1ca24353c862685413c4c23c2c1484c73088e20f1a40d6c7aa78cb90195183d13c 10 1023 4 15 10 1023 19 524287
def cc_72_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xf41e83d07a0ec5c0f80700e01c0332e608a300a00346642c81902c340c80100184300600538a00c418011001 0x9e13d9d9359f25d9e9519d1508ca56772469a9565305a45856a04579fb5a9cb569c2579ba569315b8c1578094b769476c139671319b12b9a129999275c1215285a4505675a465c94696b4d989418013b75137661219804c8b1458aa56961565205a9725696a3e9295b8a157959295185a94b45940442f03f180379334b92b437fa4a611322e84f178470983f2d82f1682790a467f14a7e948 11 2047 5 31 11 2047 20 1048575
def cc_72_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xe83a0d5750d4314a9ea0a0a8098a51942328c1d64e93044910440f2348b22c0380c0300c00300000 0x2c31c58234afa715e4d2ba1a56f45ad0886e0fc7e1bcff4a82296e750d84909b44f1f08e0a07cd6178f0279ee955551a79244ee38a90993a8eaa69fd45373507e3b0dea00bd5f5d9cc7556572a8a8d3d5081276e54ccd21f8e8370403e680f4701ad2c3fa506e660fc6e1b9943f1b06f4d932992352644a425147490c8278d447a3049444e6869c50934 10 1023 4 15 10 1023 19 524287
def cc_72_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0c2c0c084808008000000 0x1202a5a444b3c73664e5a291aa05ab24a3408eec6a8c153b67a46a71291e2323844 8 255 4 15 10 1023 19 524287
def cur_72 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_72_11 (Nat.sub p 352)) (cc_72_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_72_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_72_8 (Nat.sub p 256)) (cc_72_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_72_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_72_5 (Nat.sub p 160)) (cc_72_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_72_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_72_2 (Nat.sub p 64)) (cc_72_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_72_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_72_0 : Nat → Nat := unpackHintV5 0xbca0178016ed82dcc0fb7a1f6f402de805b30ab382f47202602e4a41c94405224664202c8202862a2dfacd99a5a84af4ca3e98c09250ca004a3f60a7e408d428901a718a780a274001400000 0xb5891b5ef63daadd8d45515556555551515551aaaaaabb5555555060ce751e3d18288d559dbc1e3b2583b36b15eab58f15460351aaa88ab1e3aaaa2a8aaaa8d39d5574b451546aaaab3b5555554e75a0e7154a146aa22aa27545555aa55558e739d55151aa51aaaaaaab3b55dae5a7766c7b36d1565cb00040000055078b5162aaabd60c18d551114055001451e3c150555555951a2351555541d82800a8000aa0000aaa0000aa00000202040000200000000aaaa08003b18c6318c63 19 524287 8 255
def hc_72_1 : Nat → Nat := unpackHintV5 0xf318f085ee05eb85e390df09d80ed585cf8cbfa0be82b78e93c8928286197b957905768574056c106789608e5e05580c48204702400e1c4819850e170b850017 0x36755ef7bdb3bd9b097bdcbdee588ec6aec7ad458aaab1e2c6aaaa826c1bbd88fdef7b437b3603f7b1fbd8f11d8d65bb7abc7828ba5a8d5544dcb137bd8fdadb 16 65535 7 127
def hc_72_2 : Nat → Nat := unpackHintV5 0x8c05e0d238340208058041de81978c15da0975415d0056dc65b7006dc01b7005cd1173005cc015a19568015a005046541004bc492f0048c311e0547008f7251a6381b4e064080019 0x9b1bbdbc1e3b47b360ec47bd86f7bda86c6bd5e3c415d2d46aa2206f636db3b1a0ed19bd8d5cf156ed1aaa2a8aaaaacaaa8a2a8d5576aaaaaa35546aa292e58f1e8d555118026e1bb 18 262143 8 255
def hc_72_3 : Nat → Nat := unpackHintV5 0x914047826341119028c0145c0a2c04fab77b83bc829df0aeb096462a6f68dbb86c82308b938989c004b8524038ee64720a348919028be1446322300118008c0002880002 0xd020a18e73039c381004f63da4c6070380100a000a04318d5443a87389d100010e288acb963c7a30511aaa8d1826c6ef6b959dda3ddb67723dec37bded436356a2c55558f1635554 17 131071 7 127
def hc_72_4 : Nat → Nat := unpackHintV5 0xaea135b026b60056c00ace0b439665e2944b717cacce4551c7813741b682669d73114a61c9602aae855400822890400166a22cc003a1f8740006a7e0d400128801f0602c1204018038480007 0xd96d181c02000140818c6306318c4550045500550000000000e70e70000e0c6318c6318c63019cea0c62aa9d63c58d565d9282023c015574b10540d80000f7b07b963c5583da346a35555154655439c5505040044380023460ed555551aa35004622a82aa00aa00000000aa880a021b8f1c39c4e00000aaa02aa9e679aaaa9d264c44104388d5657673ab0318aaa7046aaa73aee55439c6538228886c0400055a1451400d88aa00142709a21b25b68c 19 524287 8 255
def hc_72_5 : Nat → Nat := unpackHintV5 0x9581d0d1e21a00423118143300c1de71abce007702cecc15d9803902372000dfc45bd02b7a006f004c9d458e853110c49f846c678b2a610e5721c002d9605b0007b3b0f6000d5181a8000035 0xdee593668000070d9c00e401b080468c0b9bdac9f0b518b98b5adeb468ee2f63d92e1ead6336b78d27316b445ac89ef51a31ec6346007825cb0e01c78f0a20160ad6815030635d0de035a31a318000802200001c815400000000001d8002aaaa001b4104e9e400051a31a8021b8f1ce700018d4518ce76dc87394a70518c6318d5b62714e82a8c6806c4000a1118318c621b000644518d 19 524287 8 255
def hc_72_6 : Nat → Nat := unpackHintV5 0xd4d2b93963260162329ae3655bc0a9b9c4c7708f896ebf35b4a32c8a15820ea689d4d0026b2f43e988601ce4a79be0b36a125bd18b304962042b60e490dc850d09b6f08caa0a078070d0000e 0xa02a800289b1e3c1500156551515555055554000015ab5ac000011a318c0047801400800004b960000200000000046c00000018d7430062001051ce11d65c73a873873d08d1ce2c7bdf473a3463182e07840002b40811a30e70282aa0387078f23614151c26a902819ce7063aa780e61cd050003480040002346000000000800550400000000100003188003aa0047b3ae1e0ab772ce3c17358851ce2d60b57b5a28529b039e59ce501cf2d1cf4a6c4da000fa7cf5fb7a12ca9b04d800f0800050005000bdc000000000005ac2fb00018c0163182ce0f08016ae68070468c02382c277b3ec376c 19 524287 8 255
def hc_72_7 : Nat → Nat := unpackHintV5 0x9501d2a0025400495139200b1b092298cc0d467e634fb815f2053e2027269ede4696557a8e3c5081497c952d02a5505472387955099599131f222043d86c728889a4b1201423808232400046 0x3747008e1b010000a4047ec783c00272e5800023461b78bd73f6316b1620ad6f5888c68d1ec5eb9e2028009b051e3c1f3001f4f541a2aa346a08d463518c1600ad00000468f6397b817b11ef6448a34600000aa00aaaa0000000000000000004002800000026c00000040006355468c4037b5cb4e9b1fb649def680092e5800021b550176f16a2c14557ac78b555403623c00174b10455 19 524287 8 255
def hc_72_8 : Nat → Nat := unpackHintV5 0xecc01d603ba982ee76cdca05b80175f90ebd02d5823a882b438ddd5b2b02a9451b68782d030c914f3071b9df2f36a54533a293530faac19d581f9423609055170a8021143c19c8c211280042 0x1703d80002d60000001c000018d631800b97b05ece0ef7b5ee5ec1360000080040000073800006c0003802000c0006319c6000000aa000000000aaaa00000011e39ce7380000070468c63d8fd80001ce7380000000700018ce338c000000e739c0000000006338ce3000000aa0000000200018ea8000001540000000015554000000e739c000d8000070040000e010000000c6719c600003182000aa00aa0800000aaaa0000aa0008000000aaaa0000000aa000000000aaaa0000000002002a800400026c000000005501105500d8fd80131dec1eb9673acd8fd94fb7b78b885ec7ec85c8c36f02803623c4004 19 524287 8 255
def hc_72_9 : Nat → Nat := unpackHintV5 0x8d2058c70b8c7008c7008b1168842d8681c810587f61a7f4027a54f78b1a6c4c76764e61363536dd4d95d487524850243d4839ca134b512f75422ec92032b1e71c134b30ee460985608a0e00c7e0000c 0x6c360501cf1d60aa814e765ec59e59e20f31139e878f468ce7dad6b907bd6b1e1420ad631a347b97ac59d63c75b74a71733952a73aae96b05a346aab28d463518d1a339df41ce0b0528e7468d54eaaaad52aaa9ce73aaaad5447a83a739daa3d4aad2db39ce78a896aa4674e3669686355596468d445438739d5b63c79d553aa797721ce32cb1e2ceaaa8af55ac7882b05aaaaaab1e3aaadb45515539d5574b451555555555555500008f1ce700000e8d18000002a802aaa800000000000020000072039ce70360000000070000018c1018ce338c037b3bc963c5ef6f07880001ce06c000003800013010200000018c67180080030000972c00011a318c0002a8000000002a86300168c00eb3ac015a0010700200016338d1a3d9c 20 1048575 8 255
def hc_72_10 : Nat → Nat := unpackHintV5 0xb1d58ac558a16af9d442980548d5ab7e6ef78e587385672a0e6bb6f6b2096b2006a40e69f0561e81566b8512544ae644a90549d0c4336a3d1623676a31354251c21f061189671315807bb60542700054 0xaa00000aa00aa008000aa00aaaa00000000000ec010015400e10000000000000002a802304154000002642800011a3000000550055550000000000000400b60015500000000000000000c6080c754001ce05ba08f1cf51d3cce73a00000407039c0e0ce738319e8674633a3180c39c39e846878f39d1a318c0000000002a80000063aa9e8c2001e3c0808017a000103c068d196c9e3d8738141550738f78150339ce0c754f18e8f4d4873800505baa88a0a0000829a9860ce73831d500c0001540000000015554000000013a78f1c0000011a318f72f6000011e380000000000c67a1800000478e000000000319e8600000011e380000000000c67a18000002a8002aaa80000000000005b8f1c01000038000000000000000319e86003182000a739ceab541ce209429d555555aa55539ce755aa53aaaaaaaa000000000aa00000aa00aaaa75153a2b54b6d55639ce75545516a94eaaaaaaaaaaaee5ec3c1390fb59549f6745003ace75 20 1048575 8 255
def hc_72_11 : Nat → Nat := unpackHintV5 0x133552085ebae626bca0ad2a91d3d1db5f201b62b1502a2c00054 0xaa00aaaa00000000003b000980007204e74000000000000100063041551a30039d7721ce08b0a758f167555403623c000005d2c411541da833400e7154eaaca0008208287054555555554139e59ed8a301c4eb3ac78b39c63468c0786c7800000ba58f0068d1aa00283b3d399e987389ce7427309800021c518d46311a8aa8d1a030000550000000005555000000055000000000555500000055000000000555500 19 524287 8 255
def nh_72 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_72_11 (Nat.sub p 352)) (hc_72_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_72_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_72_8 (Nat.sub p 256)) (hc_72_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_72_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_72_5 (Nat.sub p 160)) (hc_72_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_72_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_72_2 (Nat.sub p 64)) (hc_72_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_72_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_72 : Nat → Nat × Nat := unpackForestF 0xb484400b4fb3239b313900b4bb1a51b195100b47aea38aea34ae938ae934ae83400b43ad345ad04400a4f00a4ba7b5da795caa946a7951a813fa904ca8137a8017a795000a47a324ca3246a503fa5037a3244a3128a3124a302400a43a1139a1138a113400a3f99c5799b5a9d25d9d1519d93d9d9359d15099b5699a5799a569992b9a956999299992700a3b981419804c00a3795a5695a3e961569592900a3394345940440094f92b4b92b430094b8a35d8a25c90a468a2518e23f8f04c8e2378e0278a2508ca6c8c9288a23b8aa6c8aa548a9288a233009478594c859468783f87837859448593c85934858140094383a3983a3883a340093f78c5778b5b8196c78b5778b4b78b4778a5a7d2517e23d7e2357d2507d15d78a5678957789567893f79b5679b4679a567893e789370093b74a417712874a3b75a407595074a377484c009376fb5b7316c6fb57722456f95670b5670a566f93e6f92e009336da466e1256d94a0092f6c9366b34a6b1466b12e0092b6a34a009276914455c5b6816c55c5755b4a6694d55b466534a6534655a4a6323a632366314d55a466223a55a345595a559575f3455f23a5f13a559565e2485da345594f5c9465594a5ba385a2345a9245a05c559475735a573565704e5785457042559465634455817009230084f4c34b4c347531294c23b521294c2335113e4c13b5013e4c1334d34a4d24a4d14a4d84c4d1464c1234c0460084a49251491514996c4995449123008473923d39237392354681939143458193912b4482e390434382e3902b4285c39b4539a5239a3a399523993a3985e3f03439852398453c1323c12a3c0323c02a398443983a3a3503a24439836390130084621b5637b5421a5f21a5b3536c3516c3516021a5732a5432a44329283292421a533195030b5630a5621a392fb542195f2195b2d36c2d26c2d260219572a9542a9442a93c2a9342195329a5028a56289562193927244271482192f25b48259442192b24b482192723a38222342215422144219230083f0b45a204580b25f0b25b1dc601d96c1d9600b2571b25c1b2441b1281b1240b25319b5e19a560b24118c580b15f0b15b164601626c162600b1571395c139441393c139340b1531225e121560b1411125c0b12f1015c0b12b0e3500e2500e1500b1270ba340c9240b95c0b9440b12300837072560715b0926c0715707a5607956071290082f06131008270235b0496c023570215602b5602a560213e0081f01232008170001f 9 11
def ch_72 : Nat → Bool := dagCheckNodeV5 m_72 g_72 ep_72 3 7 bds_72 362 (dagTraceF m_72 s_72 8 f_72) cur_72 nh_72
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV5 m_72 g_72 ep_72 3 7 362 bds_72 (dagTraceF m_72 s_72 8 f_72) (cur_72 0) (nh_72 0) s_72 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_0 : treeBlockF 0 32 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_1 : treeBlockF 32 64 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_2 : treeBlockF 64 96 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_3 : treeBlockF 96 128 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_4 : treeBlockF 128 160 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_5 : treeBlockF 160 192 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_6 : treeBlockF 192 224 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_7 : treeBlockF 224 256 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_8 : treeBlockF 256 288 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_9 : treeBlockF 288 320 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_10 : treeBlockF 320 352 ch_72 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_11 : treeBlockF 352 362 ch_72 = true := by decide +kernel
theorem nj_72_1 : ∀ i, 0 ≤ i → i < 64 → ch_72 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_72_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_72_1 h1 h2)
theorem nj_72_2 : ∀ i, 0 ≤ i → i < 96 → ch_72 i = true := block_join nj_72_1 (fun _ h1 h2 => treeBlockF_at nb_72_2 h1 h2)
theorem nj_72_3 : ∀ i, 0 ≤ i → i < 128 → ch_72 i = true := block_join nj_72_2 (fun _ h1 h2 => treeBlockF_at nb_72_3 h1 h2)
theorem nj_72_4 : ∀ i, 0 ≤ i → i < 160 → ch_72 i = true := block_join nj_72_3 (fun _ h1 h2 => treeBlockF_at nb_72_4 h1 h2)
theorem nj_72_5 : ∀ i, 0 ≤ i → i < 192 → ch_72 i = true := block_join nj_72_4 (fun _ h1 h2 => treeBlockF_at nb_72_5 h1 h2)
theorem nj_72_6 : ∀ i, 0 ≤ i → i < 224 → ch_72 i = true := block_join nj_72_5 (fun _ h1 h2 => treeBlockF_at nb_72_6 h1 h2)
theorem nj_72_7 : ∀ i, 0 ≤ i → i < 256 → ch_72 i = true := block_join nj_72_6 (fun _ h1 h2 => treeBlockF_at nb_72_7 h1 h2)
theorem nj_72_8 : ∀ i, 0 ≤ i → i < 288 → ch_72 i = true := block_join nj_72_7 (fun _ h1 h2 => treeBlockF_at nb_72_8 h1 h2)
theorem nj_72_9 : ∀ i, 0 ≤ i → i < 320 → ch_72 i = true := block_join nj_72_8 (fun _ h1 h2 => treeBlockF_at nb_72_9 h1 h2)
theorem nj_72_10 : ∀ i, 0 ≤ i → i < 352 → ch_72 i = true := block_join nj_72_9 (fun _ h1 h2 => treeBlockF_at nb_72_10 h1 h2)
theorem nj_72_11 : ∀ i, 0 ≤ i → i < 362 → ch_72 i = true := block_join nj_72_10 (fun _ h1 h2 => treeBlockF_at nb_72_11 h1 h2)
theorem nc_72 : ∀ i, 0 ≤ i → i < 362 → ch_72 i = true := nj_72_11
theorem lb_72 : LowerBin m_72 s_72 g_72 9 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_0 (kn_cons lb_43 (kn_cons lb_23 (kn_cons lb_8 (kn_cons lb_42 (kn_cons lb_40 (kn_cons lb_34 (kn_cons lb_15 (kn_nil)))))))))) rc_72 nc_72 (by decide +kernel)

def g_73 : Nat := 0x1171557131f377f
def ep_73 : Nat := 0x12082228000014400000246000160042000c004801060402020e040801121002131032200114155410100440
def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_64, s_64, 9, g_64), (m_69, s_69, 9, g_69), (m_72, s_72, 9, g_72), (m_71, s_71, 9, g_71), (m_70, s_70, 9, g_70), (m_8, s_8, 4, g_8), (m_65, s_65, 8, g_65), (m_66, s_66, 8, g_66), (m_4, s_4, 4, g_4), (m_63, s_63, 8, g_63), (m_67, s_67, 8, g_67), (m_68, s_68, 8, g_68), (m_30, s_30, 5, g_30), (m_29, s_29, 5, g_29), (m_33, s_33, 7, g_33), (m_35, s_35, 6, g_35), (m_57, s_57, 5, g_57), (m_62, s_62, 4, g_62), (m_60, s_60, 4, g_60)]
def cc_73_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8008008006e96e06e06c16c06c06c06c05a95a05245205205205204a44a04a04a04814234204203e23e03c126b032001 0x10d691056107c6d054650fb5e0a35a0f3560e83a0e0360cb540d56b0c5630746f044670345d0bb6f0b36e0ab670a36206c6f02c5d01c550936e0856907c700745a06c5204b7c05d71054600445a0346802c6001c5014d6f13d6b12d67115630dc6209c5a08c520636f03b670235f01357cc45fc9c5bc8c57c1c53b1b5fafb5bacb57a6b5396b4f8db4b76b476eb435a25f4b25738a4f20a4715a3f00a370003f 12 4095 5 31 11 2047 20 1048575
def cc_73_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x843e9f0f1783c1b6d86c30d80b95c2e170b85c2e11c5728108802b140844020020000000 0x17366f9aa78df3a8a96b66e5aa6517778b3b455d237655bb1ad78563beb15d1aed8c7fd6ff6b5f759f8ac7ab6ecdaf58d5aa8d0a4608638351aa88b134708238311aa48b11b54 9 511 3 7 11 2047 17 131071
def cc_73_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9ca709c26190a4090240901f57c1f07c1f07c196641905c97058560509404c530485204082e08002 0x30670bedb2e46cbb5c2dc71b39c2846cb0db2bb5cacd52a56ba71ba9462a2dba836292d6a757a9b1b25b54959ca4c6c8f1ea2b54899ca1b6cdf58b6c6fd51af4c67c918f0b6fbcdaed367aad8e7b5d98d3e434b8cd1e134364db20364 10 1023 4 15 11 2047 18 262143
def cc_73_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb06c0ac6b0ac292a0680a0280a02808d55e540e7380d1340d0214802008020062108401000400000 0x3a3547d6a8f75e9ea3639c5477adced589d635ba34e73685295be4ab5c85678eac7131ba1db7c2b6b836cefed8df9afbe35b796aef0d4dc9a2b756d606d2b2d8529ada23535269ae0d15bab83646c546da9cd751daab5b45678c2cd181a23632b4563ad0a55818a34a8b5c 10 1023 4 15 11 2047 19 524287
def cc_73_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x8844212ec743a1d0d34fa6122903a1c0d26830980c060300f4702a1408440190c0603003 0x276b8505719fae13d1c6702f4d47c996f930db2ca36d7461ab6db4ed3e85a5cdb47976872b19236be3db65756ab26d16463e47b458d8d2eed7631aac585a8a0acef1b2223243354848f904db205b240354 9 511 3 7 11 2047 19 524287
def cc_73_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0280a0253942508ca308c2125ad6054550541503d8f03c0a5280a02806418051140501041300400 0xbead37b17af1b25d568b98d36edf2d9b26e46fdb8c7ad1674e2ae6b6fc76c784d56fda7ddb4bb868f6ad0ecdaad2b5b9e6af52d36c5a5d8347af68b5b166b22ad4c51a869d34d0aaa3e54c70a86f944d1699aa51d70a5ae348df289ab4e86c 10 1023 4 15 11 2047 19 524287
def cc_73_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xb062a80a0080200802005e5705c14350140501404c4e5380d1340d03048420080200800d4300c003 0x6fc6eebadfd35af9eb3f1d63e06ddbcd7ad537cba67784be8495f6a346ac64daadda4dbf2db1df35bb96af82d3765a5ec347d768bab17b51b6e8b5fcfaf9a51a74632e8459ce8ab88d9331aa64d68cbad38719329af64356c68db831a71630e235ec36a5831a302325eb5a 10 1023 4 15 11 2047 19 524287
def cc_73_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4181700600c0168ed05a0b41606c058098d302604c08c665cc01612c040c800e11c03805108110020002000 0x81d708156080c717fc707f27c7d67a7986c778607b36c7c56a7bd627ab6b7a25d4e1677995d78d627835d77a5d8c56e8b56b8ad6389d6288c6f8746b85c6784c638236f7eb677e35f7db5e6f35d7e34f7db4e5c26f4da677ca5f3ca4f23247012377905e7705276364754547137c70b547437c7334e72a4f724547146970c595ba6d4c265 11 2047 5 31 11 2047 20 1048575
def cc_73_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02b1a0ddb741d068da05cd52540f63c0e1344d0214801c46118051140501044004c100401004001 0x8f46c8bd628ec6b5126795d6f94d6b93d6791d639145e8fb6e8e3565da6f50a673e25f242578bd6e8d4558cb558bc6c7d26d7c06c7b86c788608956d865658a4578436d8136581b45895707b06c8846e87c6c3da5d23a557a86e86c6d865608546c83c6c845708346982c6880247 10 1023 4 15 11 2047 20 1048575
def cc_73_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xf81e87d0743dc7b83706e0d07a0340680d01796d15a0b029e5302033c260cc0123202400708830c218030003 0x9f46c9ed749cc6c9e3446fc6e70c5e81b459cd689c5649bc7c9ad7c9a5708cc7c99c6c9927c02c6c3a34497c7aa656fa5d6ba5567a4d63a446fa246ea046b9fc679dc639d4629b36f98b679135a7e3577db567e3477db468e3455fa6f53a673f25f262579824f97247022379567e9646490b7c8f3549556e8eb66853549447c8d37c9036c92a4592b549335687b54922575ea6f90c6d904658d455 11 2047 5 31 11 2047 20 1048575
def cc_73_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x92524240c087c4d65a8314620b51592b04ca981302603d05a0a89142023c4708e01c0380430710e01c012802 0x8cb559ab4d803659a35d80b577fb55aeb4781b452da57ae24705a379923f7f237af46dadc61aa36d98b4f7eb47ad26c41a4f2d24703a37ac4646fb64a9b5ca8b54ab454a8366a7b648bb5470c598d455a9d6e6fc6e6526f4125d2ba558a5638bd62a8c6ea8463a7c626426f40a4d2b245abd6faad63aa36ea935ea735663a6f3fa5f2aa5774464a3d7c8eb55a1344272657647c9e344a1c78a3c699bb6d99b658cb55a305aa28569f464a1d7c9a46ca134497a55a0a446fc7c9ec60 11 2047 4 15 11 2047 20 1048575
def cc_73_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xf43e0782700e01822c2580b01586b04c598128650481901012004007c2f81f0326640c81710b214028040804 0xb9464b8454bf56dbed6c8d464b626dbdd6e9cb5d8335782b556826f31257bd2470823770d7cb8c51b7c50b525dbb47cbbc5ebac53ba4529c34d6725fb947cb846cb8d65b7d649bc7cb7344b5d7c07d7cb6469b5465b4c59b445562354b346db2c61c146fc0c63bfc5f8c45dbe45bbcc59bc457b9c55b6c539d4519b34f8234766a6fb3a5fb225743a4f30a4706237b085eb135eb035642a5f2f257 11 2047 5 31 11 2047 20 1048575
def cc_73_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xf40f21f20f01f00dcaa7ba60a41a0296580b7c268a6806806426406406025e15c15c058242b4203e21550e3083080004 0xcf25cce45cd1c6ec646dcbb69c6361d0a4dd0249cfa45cea41cd94dcd145c856fcad6ec5d6dcb469c8463c5c61c136fabb63dab5f8c35dd9b5bd9357d8b55d7353a634f95b4b88b4775b436e26fd6a5fd62574a24f36a471fa3f14a37d205acc856cb8669535b81b4570c52a135e7535249a5f35a57cb56dcac5ea5b5f94b5b8735774b53ca3454925f352571ea3f13a378d4659434ac746dc936da534f93b4b85b4773b434824f34a471da3f12a378cb55c7856c686ac606681b54c2a45c456272b628bc62aec53b736eab3629e35e7235247a5f32a57c3a4f1d23d11a359236bc2b45c856fc5d6dc846fc746ec5c6dc0b6faab63a4b5f91b5b84b5771b539d34dc534bc4b47c33456da6f4725f32257c22471c23f11237bdc68bbc64c0354bad65ba564b73448457cbf469bec68c0354 12 4095 5 31 11 2047 20 1048575
def cc_73_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x2458c5f470d8460171494e4308b12c0b0284a024490060100400100000 0x8957cbbc54da368d5868d0864d8354da46c8cb64d5068d0064d7b50d4858cf8546fd62c036eac3629634ad835cd7c6490b7ca8b54d4068ce8643757c6ac54d3068cd864d2858cd054cf054d1034d3854c6d6dc6c61d5b5dd5359d4b55d4351d325dd2a55d145c 10 1023 4 15 11 2047 20 1048575
def cur_73 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_73_13 (Nat.sub p 416)) (cc_73_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (cc_73_11 (Nat.sub p 352)) (cc_73_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Bool.rec (Bool.rec (cc_73_9 (Nat.sub p 288)) (cc_73_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_73_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 320)) (Bool.rec (Bool.rec (Bool.rec (cc_73_6 (Nat.sub p 192)) (cc_73_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_73_4 (Nat.sub p 128)) (cc_73_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_73_2 (Nat.sub p 64)) (cc_73_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_73_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def hc_73_0 : Nat → Nat := unpackHintV5 0x8bf9498800fe83911c7d997e7a88c47928587600ca7350ac6d11906a60ac661d1160c9555a619a5481785114db4ce50c49acce4664d23c5a833860fe3361403218522e90e2240ea12030f71c58f61585b51161090a05d7031dba0000c7000000 0x6c00785c000791c0000000000000000000061c1870060c000387018000000b85c0b0020000000f038000000001e00000000000000000000030e0c38000001c0600154000010b00aa00000000170b1600000f0000000008800000000000000187061c0000187061c00e030000f83c783c001e5cb802709888a8a0004c044444187061c180703830061c383060714170b858442c05d42c58b2140f0382383c01e0003c02e000f078000000030e0c381c182e1710b00000000000061c187170b81e11c01e0003c01e000f000000000e0c3830e070610b85c42c0000000007803c36000000000c3830e07060b85c42c000780f01e6c078f1e0f078f01e3c0011141400000187061c1830e1c1830e1c180703830505c2e162e858ba16110b0503c0e00000001e0f1e000000000000c3830e07060b85c42c0000000078000000000000000030e0c38000001c060002e17000000500b160001e0700008c0f9f02e5c26222882080022220c3830e0c0381c18030e1c183038a0b85c2c221602e858b2140f0380079b078f01e5c078f1e0f078f01e3c0011141400000187061c1830e1c1830e1c180703830505c2e162e858ba16110b0503c0e0d86c36001b0f9b3e270b9709888a2082000888830e0c38300e070600c387060c0e282e170b088580ba162c8503c0e078003d00780003c1e00f07800000000011c187061c0e0c170b88580000f000004400023800000f23800000000c3830e000000002e170000000000781c00011c783c01e0f1100786c000000000061c187038305c2e2160000471e0f00783c4401e2b00000000000187061c0e0c170b8858003c1e03c078f50787c78f078aa223c78f2e220f01e03c8e3c780f1e3c0054451147a5c0001e83c458e0c3830e0c1870e0c1870e0c0380c387060c0e07060a0b85c2c5d0b1742c205d0b16442c140f03878000f1e020000f07803c1e0004700783c00000040e0c3830e070610b85c42c00007811c8e03c00023811e383c2e0000011c08f1c00187061c008e11c0000170b80000000003c0e000000000061c187170b8000783c08e03c01100783c0001e17000000187061c0607060b85c42c00078f01e0f078f1e3cb88aa888f1e0f0fa83c0780f0d8f1e3c78f00791c0983c151e970511440007a0f115060c387060c387061c1870601c061c38306070187060c14162e858ba170b85840ba162c8858281e07000000000011c08f1c000002384700061c18700000000170b8000000003c0e000000000004023800000004700000187061c000000005c2e000000000f0380001e00f001e00f000000010100b8080011c00000000000402e000000830e0c38000c000e00701800000b85c000b0020205800000781c0011c8e00000011c08f1c000002384700061c18700000000170b80000000003c0e007803c00007803c002e02020200230000078000011c00000b8000800000047061c187018001c0000e0300000170b8058b000a000205800000781c5cb973e5cb972e5cb972e5c993264d5555549a935563830e0c3830e0c383061c383061c3830e0c3aa8b85c2e170b1742c5d0b85caa1e072aa830e0c3830e0c3830e0c3a1c1a2e170b85c2e1730b43c0e 24 16777215 10 1023
def hc_73_1 : Nat → Nat := unpackHintV5 0xb8319bad4abaa8d51da171d99b618494adad89babd82f1b27e811c76f5e372791f6c458d68110d6550b06290b05c4194592cc5562cc050856a4909df44951d3db9b739451d2e9eaa29ed2c22e1c31e7d1918099d0cc6d1091cea048526000121 0x87c98f264c0158f00264c984c00263c1411001414000187061c1807060c387060c38703830505c2e1610b1742c5d10b0503c0e0f91c0f9f00faf3e4c2600132604c98133e13266c261b09813266c99f0984c99f2613098a9711005114ba5c058e13109a0c3830e0c0383061c383061c381c18030e1c183038a0b85c2c2162e858ba21602e858b2140f03836000f0000000000000000000000000018001c187061c000000160042e170000000781c07c0000f91c000000000009807c0261f00d800000001700010b8000011c0000060c000387061c187000000380c000160042e1700000102c0003c0e0f880f1e3c098f1e130786c0264db9347888020803d061c1870601c187061c061c1830505c2e1610b85c0b858b0503c0e0f88013263c79f36004c98f078003c782823c4401414010780c3830e0c0383061c383061c381c18282e170b0858ba162e8858281e0701f3e1f23807cf9f1e0f0007930984c7af2603c784c99b0786c2604c78f269c261326bc983c262a3c4401414058e0f107a0c3830e0c0383061c383061c381c18030e1c183038a0b85c2c2162e858ba21602e858b2140f0381e4c1e3c78f264c0078f1e83c0780f078f01e3c11001414000187061c1807060c387060c38703830505c2e1610b1742c5d10b0503c0e0d8003c00007800000000000000000000c000e0c3830e0000000b002170b80000003c0e1e4c98f3e7c78f56ac7a747931e3c9aa8f26a3c98f26aaaaaaaaaaa0c3830e0c1870e0c1870e0c3830e0c3830eaa2e170b1742c5d0b85c2e172a8781c0f000000000000000000000000000187061c00e030000000170b8028058b00000000f038361b0d9f0f9b4e13264c260130262213144104111100061c1870601c1830380c38703830505c2e1610b1640ba2160a0781c0f0000000000000000000000061c18700380c00000005c2e00a0162c00000003c0e0003e0001f1e00000000000000c03830e0c38b085c2e00f800001f3600000000000000c03830e0c38b085c2e01e03c01e6c0078f1e0f00078f01e3c104001414000187061c1807060c387060c38703830505c2e1610b1742c5d10b0503c0e0983c2387c003ebc3e00000000000c03830187061c5842e1706c1e1f08e002b561f00000000000601c187061c58442e1707c3e013264c2604c4440981344111110400061c187060c0e030e1c180703830505c2e162c81742c22160a0781c4c993264c993264c993267c993264c993264d54baaaaab1d26a934187061c187061c187061c1830e1c1830e1d545c2e170b85c2e162e858ba550f03800000001e00f0000000000000000000061c187000000380c0005c2e000002058000781c0f01e4700001e00f000b8001700000000000000000000000000008e0c3830e00701800001c06000002e1700500b16000040b000000f0380000001e01700000000000000000000061c187000000380c0005c2e000002058000781c0f2380f1e00f1e3c7970d87c7970f81702e1b1e5c7970f83cb8f2e1b0f8f078003c780f1e02a200282804d0988b1c187061c1807060c387060c38701870e0c181c0e0c14170b85842c5d0b1740ba162c8858281e07000000003c02e000000000000000011c0000187061c000000e03000170b8000008160001e0701f00001e4700b807c02e005c02e000000000000000000000000000470060c000387061c1870000380c00000160042e17000102c000003c0e00000007803c0000000000000000000187061c000000e03000170b8000008160001e0703c4078f1e03c78f01e0f2383c0363c7822288008f0448e0f4187061c1807061c1870187060c14170b85842e1702e162c140f038078f0791c01e7c78f1e0f0f8f1e0f01e03c363c78f2e0f078f1e5c1e271e0f00078f0784c78f1e02a200288a3d2e00f41e22c7061c1870601c1830e1c1830e1c061c383060703830505c2e1610b1742c5d02e858b22160a0781c03c000000003e00000000000000030e0c3800000000b85c00000001e0700f00000791c000238000f0b80000000f23800000000c3830e000000002e1700000000781c000f00b803c0000000000000000000061c187018000c000e00002e170002c00800003c0e 24 16777215 10 1023
def hc_73_2 : Nat → Nat := unpackHintV5 0x9aade49369d191bc6b8e14ea82d2d17e4d2179b52675bcfe713d206951fb653d0560d11b5af577550d7a5124fa4b0d8648c492441d2a3d85a63c145c38b8d73495092d55d02b1091234df121e45a1df0fd19492a129dab0b89c50701220001c0 0x6c3e00f00000f91c000000003e0001300b804c0000000000008e0000000c3830e030003800000070e00c18000b85c02c5800500000102c000581e0706c36005c9971e6c78029f3e087c8e00bc78171e08817014ba0a22000c3830e0c0383061c383061c381c18282e170b0858ba162e88582a2c0f038000000002e0f0187061c5c2e0586c1e6c0000d86c000000023970b8000c0381c187061c162c0a2170b816005c2e5c7973e0f0b973e5c1e5cd85cb8f0367c0d86c3629f3ebcf9f00f91c1e130784c012e970511440ba1711638003061c383061c3830e0c383060701870e0c0381c18282c5d0b1742e170b2e2c5902e2f42c22160a8b03c0e0000000791c000238000f0b8000000000011c00061c1870000e000000b85c00000001e0700005c01e00000000000000000000000c3830e0003000380000b85c0002c5800500000781c000f0000000000000000008e000c3830e0300000000170b8000000000581e07000000f2380002000000011c000002380000c3830e0003000000170b8000000000581e07007c3e00f0000000f91c000009800bc00026017009800000000000011c0000402e00c3830e0300038000001c060002e1700b160014000001402c58000b03c0e08e0f0783c0001e0f1e0000f1e3c00001e0f000000180c03830e0c38705842e1703c0000000000000000000000000061c18700380c00000005c2e00a0162c00000003c0e0783c01e6c014780f0001e3c7a200282800030e0c38300e0c1870e0c1870e07060a0b85c2c2162e858ba2160a0781c003c1e03c0780f1e0f238f01e3c1e171e0088a2800000c3830e0c387061c38300e0c038a0b85c2e170b08584281e070000f23800003c00000000000000187061c00000380002e170000000000781c03c1e7c3e3c262223c1e008c0b9744001111104061c1870601c1830380c3870387060714170b85842c5902e8858281e0703c2386c00366c0000239b0000180c0162c1600000000f00d80000000000000000000030e0c38000001c060002e1700000102c000581e07006c01e000001f017800000000011c00000000004000000187061c06000700018001c00005c2e0162c002816000b0020000160781c00000000000030e0c38b85c0000011c0007803c004401e000000001c3830e0c381c182e1710b0000008e0478e0f000000008e11c00000187061c00000380002e17000000000781c01f000000000000260470017807c0040402e0200000000011c0000402e00c3830e0300038000001c060002e1700b1600140000040b000160781c1f0780201f0f800470008e000c06000b160b00f80bc03e00f009808080800000000008c00026000470000b8000800002000c3830e03000380c000e0000002e1700b16001402c5800502c000000581e0700000000000030e0c38b85c00000011c00783c1e1f00783c01e000000001c3830e0c38070e03060b85c42c0000d803c000000000000000000000000187061c000600070000170b8001600400002c0f038036000000000000004717807c0000000000008e0000000c3830e030003800000070e00c18000b85c02c5800500000102c000581e07172e5cf972e5d52e5c9972e5c9aaa5d4baab1d54187061c1830e1c1830e1c187061c187061d545c2e165c58ba162e2f42e170b85caa2d0f0381e013000000000000000078000000000030e0c3801c0600000002e170102c00000003c0e1781f238000000000000f00d800013000260000003c0000000008e000030e0c3801c0600000007018000b85c01402c5800000102c0003c0e 24 16777215 10 1023
def hc_73_3 : Nat → Nat := unpackHintV5 0xac69d3a7e521a1bd8a9f98899b1521948da28d41d3890d0d82959e7f14e07b18ff76ed0b70f17f6a5da562fdd85b71e357410c4fb1e449798e458cfb3b9e7c33a9fd2d718e2d440b2bb464273d1e1d6a7516ed9f1380db084ecd0488f1000122 0x6c000b803c000d806c000980808080011c000026000000047000000402e0000c3830e0003000380c000e00002e1702c00160040b00200000f03803600f00000000000000000000000000061c187018001c0000005c2e058010000000781c0001700b800004700000017806c000000002380000000000c3830e0003000380001c060002e170002c0080008160001e0706c2383c00363c000000023970180c0162c00000001e01b00000000000000000000061c187000000380c0005c2e000002058000781c01b0178000005c01e00000000011c000000000008e00000030e0c380c000e0003000380000b85c02c5800502c001600400001e0700005c02e00000011c00260006c03600005c0404040000238000000020170061c18700018001c00003870060c0005c2e0005801000102c0003c0e078000000000000000000000030e0c3801c0600000002e1700500b1600000001e0703c1e00f36003c78f1e0f1e000f1e03c7820800282800030e0c38300e0c1870e0c1870e07060a0b85c2c2162e858ba2160a0781c0f078470780006dd8000a0f0000000000601c180c3830e031610b85c0000047000000400000000000008e030e0c3800000c00005c2e000000000f038000008e4723800000000011c23800030e0c380000000306000b85c000000001e0703cf87c780f098888f078172e00882222002080c3830e0c181c061c38300e030e0c18282e170b1640ba16110b0503c0e2e5cb973e5cbaa5cb97265cb9355563a5d52eaa830e0c3830e0c383061c383061c3830e0c3aa8b85c2e170b1742c5d0b85caa1e0703c4001e3c78f1e5c78f001e6c78f01e0f23800f1e3d10011e828880030e0c38300e0c1870e0c1870e030e0c18282e170b0858ba162e8858281e070f3e7dba3cb973e7d55478f1e3c78f1e3c98f1e4d555555555541870e0c387061c187060c387060c387061c18755170b85c2e162e858ba170b9543c0e00001401f1c00000000000023800000001c000061c187000000000170b800003c0e17801b0f803c010100b8087c8e00000000000000000000020170000008e000c3830e00701800c000e0000002e1700500b16002c580050000000b03c0e041005550053e1b001b8f06e3c1102e02a0a0000c3830e0c0383061c383061c381c18282e170b0858ba162e88582a2c0f03841e0000f1e0002b56001b01e004c0d80011c001807061c187058b0285c2e0585d42e5cf87c8e06cf8a0172e7cdaf3e7c360130b84c00d9f03e0881742e22c7505000061c187060c0e030e1c1830061c1830e1c1830e1c0e0c14170b8597162c81717a1610b1742c5d10b054581e0701f00b808080806c3e01f1b80001f23800000000000000017000100000008e0000c1800070e0c3830e03000380c000000160042e1700b1600140000002c0f03810554014015786c005e3c178f0440b80a82800030e0c38300e0c1870e0c1870e07060a0b85c2c2162e858ba2160a8b03c0e0787c00005600000030e0c38b85c1b13e00003c7800000bc01e004c0d80011cb85c0000601c187061c060b16050b85c0b0583cb9b0ba81b3e1f238a0172ebcd9f3ebc3603c260f09801b5e0bc1102e85c458ea0a0000c3830e0c181c061c38300e0c1870e0c1870e07060a0b85c2cb8b1640b8bd0b0858ba162e88582a2c0f0383e2b2e3cb9700563c01503e0007c78171e08800a0a0000c3830e0c0383061c383061c381c18282e170b0858ba162e8858281e0706c1e1b0000db70d8000000047000601c180c3830e0b16050b85c0b001e5cf85cb8f0785cbab2e170b971e5c3e2f05e0bd78a1f239f3e07cf9f0b8f0983c2e4c98022282805d0b88b1c00187061c1830e1c1830e1c1830380c3870601c0e0c14170b858ba162e8597162c81717a16110b054581e07000000000003c0000000000000187061c0000e1c0000005c2e0000000f0380001e00f000007800000000000000000030e0c38000c000e00002e170002c00800003c0e 24 16777215 10 1023
def hc_73_4 : Nat → Nat := unpackHintV5 0xbba0cdb9f46bb698d7abaabca5b97c9f619699bd698d7712861dd681ad1c7b51977804d36d8a9f69191c6275a95e65045406984f81214af9224720f642d1143cc5833861192de69f2981192275c31de923130ab80f14fd0b7ce607091d0001c2 0x1b0d9b000036ac2e0011c00000001807061c187058b02885c2e00170b16000003c08e000c3830e00170b805c0783c58b162ca000000008e3c1e04700061c1870601c00b88cb972e5c2e172e5c3e3cd86c79f02e5c0b86c1e13263c780f1e03c1e06cd86c261b271d1ea3c048e222200000c1870e0c1870e0c3830e0c181c061c38300e07060a0b1742c5d0b85c2c58b205cce858442c140f03814360f02e03c784c99b09ab260f1e8888002080c3830e0c3830e0c0380c393064c1830505c2e170b858450b2140f0380154361b02e5c0d8f2613098f0263c0011141400000187061c1830e1c1830e1c180703830505c2e162e858ba16110b0503c0e002e5c2e6c360f1e03c0783c0047a8f0448e00000c3830e0c3830e0c0381c18282c5c2c5c2e170b08858281e070005cb817361b0d932e4c09930984c984c0984c364e3932e4c2613265c9970984c99b2613266c99f0986c984c9a5d4b8091c000045426971060c387060c387061c1870601c0e0c0187261c383260c181c5058ba162e85c2e16110b01742c590a0781ca972e5cb972e7cf9f3e5cb932e5cb933e7cf9f4ba975563aaaa83061c383061c3830e0c3830e0c3830e0c3aa8b1742c5d0b85c2e170b85caa1e0705c00400000000000000000000000000060007061c187000000058010b85c0000001e0706c0d91c00000b803c00000000000000000000008e00000030e0c3801c0600003000380000b85c01402c580002c00800003c0e1078000003c780005cb86c000d811c00001807061c1871610b85c1b2381b361b14361f2e5c500d9b365cb972e0a0aaa6c3606c00b84c099b3606c11058e1710baa22974b800030e0c3830600c383060701870e0c1870e0c1870e07060a0b85c2c2162c81742c5d0b17442c140f0381e020000000000000000000000000000c3830e0070180000000b85c040b00000000f0380d80001b238001700b80000000000000000000004700000001830000e1c187061c0600030003800002c0085c2e000580100000781c6c0b88000003c780005cb9b0007801336047000000601c187061c062c2170b81606cd86c8e0f13972e1b0fa8a01b366cb972e5c141554d86c000784c1e13366c0d8220b1c2e21754452e97000061c1870601c1830380c387060c387060c38703830505c2e1610b1640ba162e858ba2160a0781c4723804703603c008e11c000008e11c00000008e11c061c187000000000170b800003c0e07803c00000001e0000000000000200000c3830e0070180000000b85c040b00000000f0381e00000000000000000000000000030e0c3801c0600000015410b000000aa170b160f08800000000000000000000000000000000187061c187061c00e0300000001e5cb86c1e9c443e23c1e01302600a28222200000c3830e030e1c183038300e07060a0b85c0ba858b1642c22160a0781c17000780000000000000000000000000c000e0c3830e0000000b002170b80000003c0e00361b0366c0d9b07972e1f2e3c1e172e5cb8ac2e3cb97143647366c0d9b36000f0983c2688a0a02c70b885d00061c187060c387060c3870601c1830380c38703830505c2e162e858ba1610b1640ba2160a0781c00f007800000000000000000000000030e0c380c000e0000002e1702c0080000003c0e0000b803c00d91c00000000360000005c0260004c00002380000000000c3830e000300038000070e00c18000b85c000b0020002058000781c0f00980000000000000000000002000000c3830e0070180000000b85c040b00000000f03800366c0d9b0d86c36171e5cb83c3e5cb972e0f2e5c365c78a6cdaf366c03647000784c1e134ba5c14451058e1710ba000c1870e0c1870e0c3830e0c0383060701870e07060a0b1742c5d0b85c2c2162c817442c140f038001e00000200000000000011c0000187061c06000000002e17000000000781c00000f00000000000000000061c18700018000000b85c000000001e07005c01e00000000000000000000000000c3830e0300038000000b85c0b0020000000f0380002e00f000036470000001780000001700980013000008e000000000030e0c38000c000e00007018000b85c000b0020000a0162c0003c0e 24 16777215 10 1023
def hc_73_5 : Nat → Nat := unpackHintV5 0xbd9cbcb90526b2899fa7b6b5a14d9a9e04d29272e58c797e85d9a87a0af472fdc36eb11368818c655cc96149055ab9a45371d24ce1a4483d294069f53bf51d3615782fcd9224cac12380522078c219e9a418506614cce10a1eac06e0cf0001b8 0x3c001e11c000786c01e0f000000061c187038305c2e2160478f1e3c723c723c723c72380000002308e3c1e478f1e38030e0c3c78f1e38b85d1e3c78e00aa05cb80f1e1f078f1e03c780f07800a0a088001301060c387060c387061c1870601c0e0c14162e858ba170b858442c140f03800f83c0b80f2e3c1e0f2603c9803e383c263c784c99f078f1e4cb84c264cb930784c1e3c264c48e9704ba0013011111061c187060c387060c3870601c0e0c01870e0c181c505c2e162e858ba16110b01742c590a0781c0f07aa800f1e003cb8f078003c780f1e082000a0a0000c3830e0c0383061c383061c381c18282e170b0858ba162e8858281e0703c1e0f0000dbb078004700000000601c180c3830e0b16050b85c003c78f078f1e0f0b8f1e3c1e231e3c7970783c0780f1e0f263c1e0f1e03c7803c783c1e231f1c48e8f047a0f4b888a8003c04187061c1830e1c1830e1c1830380c3870601c0e0c14170b858ba162e858f162c8170fa16110b0503c0e005541e6c1e3c1e0f1e03c0783c0047a891d1e0000f01061c187061c1870601c0e0c14162e162e170b858442c140f0380154078f02e5c360f1e3c078f01e0f001414114b8001301060c387060c387061c1870601c0e0c14162e858ba170b858442c140f03800d83c0b9b01e5c783c1e4c079300784c463e38f1e4c264cf933e0f1e3c9970984c997260f0983c784c9891d2e097400260222220c3830e0c1870e0c1870e0c0381c18030e4c387064c183038a0b85c2c5d0b1742c221602e858b2140f03953e7cb972e5cb973e7cb972e4cb9726ac74baa5d554baa830e0c383061c383061c3830e0c3830e0c3aa8b85c2c5d0b1742e170b85caa1e0703c01e00000000000000000000000030e0c3801c0600000002e170102c00000003c0e367c544367c3e6c2e5cf86c1184c098022088888200030e0c380c387060c0e0c0381c18282e1702e858b2164510b0503c0e360005c0d86c00d86c00360f000000061c1870383085c2e2161b3606cd9702e0a5cb806cd9b366c78f0d86d51110187061c187061e85c2e170b81e2003c78f1e3c7800f2e3c1e03c0363c78f4400505000061c1870601c1830e1c1830e1c0e0c14170b85842c5d0b17442c140f038d9b3e6cfa6cfaaa972e5cf9b367cd9b364cd9355555555555061c187061c187060c387060c387061c18755170b85d0ba162e858ba170b9543c0e0d83c78f366c0078f1e83c0780f078f01e3c11001414000187061c1807060c387060c38703830505c2e1610b1742c5d10b0503c0e0d8003c00000b8000000470000000000000060007061c187000000058010b85c0000001e070f26aaa3cf9f1e3d1ab563d1e7c79f1e3cb971e4c79355555555555061c187060c387060c387061c187060c383061d545c2e162e858ba170b85d0ba550f0381e020000000000000000f0000000000061c18700380c00000005c2e020580000000781c0f07802a8f363c783c001e3c7a200282800030e0c38300e0c1870e0c1870e07060a0b85c2c2162e858ba2160a0781c0a0f0780f1e0f238f078f078f01e3c1e171e131e8888002080c3830e0c3830e0c03830600c38a0b85c2e170b085914281e070005cb817361b0785c1e5c7970b85c7971e1b1e6c363cd84c98f2e3c078f0b84c783c0d938e1b0986d1ea3c048e002222000c1870e0c1870e0c3830e0c0383060701870e07060a0b1742c5d0b85c2c2162c817442c140f038000000000187061c5c2e360005c238001b0d806c00000003830e0c381c1842e1710b00154361b02e5c0b972613098f0263c0360134450500000061c187060c387060c3870601c0e0c14170b858ba162e858442c140f03800000007811c00187061c5c2e000b85c02e03c1e000000011c783c08e000c3830e0c038b85c0b16050005cb8170d86c9930264c0984c0d938e1309932e4c2613265c9970984c99f099336130984c9a5d4b8091c000044441830e1c1830e1c187061c180703830061c383060714162e858ba170b858442c05d0b164281e0703c40002e5c000d8047001e04700000601c187061c1604cc5c2e0d83c0154b97002e5c783c0d806c78f01e3c11e0891c01414000187061c1807060c387060c38703830505c2e1610b1742c5d10b0503c0e 24 16777215 10 1023
def hc_73_6 : Nat → Nat := unpackHintV5 0xb81dbaafba19a432e296eb5290e5818dacce89710f82a9b27bc5b977b5047359176d717a69410c65d0dc60a14c5f345b5bccda4ea34b4d106449b0d845b1004418664024fd350ec630c1132a31a42351b81d617c158df50f6d880b1d140002c7 0x1b0783cf87c7a709931e0f0264e388c2623263c360005c42e2000c3830e0c0383060701870e070601c182e170b0858b205d10b08581e0713264c993264c993464e393264c99f264c993264c9aa9349a4c9a932ea0c3830e0c3830e0c3830e0c187261c383260c1870e87068b85c2e170b85c2c5d0b174c2d0f03801e3c78f1e3cb88aa888f1e7e383c78f01e3cd83c1e3c1e7c78f078f078f01e3c01e0f0783c0048e8f047a22a0f4b88003c04187061c1830e1c1830e1c061c38306070601c0e0c14170b858ba162e8170fa163c58b216110b0503c0e5478f1e3c78f3f1c78f1e3cda71e3dbb751e3c78f1e3cbaaaaaa8f3e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3d58e8f547aaaaaa8f4baa3d54187061c1830e1c1830e1c187061c1830e1c1830e1c187061d545c2e162e858ba170b858ba162e85c2e550f03878f1eac78e0471e3cd8f8e0f8e000f07891d238822200030e0c381c180c3830e07060a0b85c43c58f05c2e2160a0781c0f000786c0d86c00786c001e0f000000061c187038305c2e2160f1e3c780f02ea03c7803c78f363c78f1e3c361b54444061c187061c187170b85c2e1078f1e3c7800f1e003cb8f078f1e03c0363c78f4400505000061c1870601c1830e1c1830e1c0e0c14170b85842c5d0b17442c140f038da6cda755367d4b972e6cd9b366c99b26aaaaaaaaaaa0c3830e0c3830e0c1870e0c1870e0c3830eaa2e170b85c2c5d0b1742e172a8781c03e3800020003c000000000000023800000c3830e000000002e1700000000781c0f0007800000000000000000000000030003830e0c380000002c0085c2e0000000f038f9f1150b970f8ddb8131184c3e000888a20820003060701870e0c3830e0c0381c18282c5902e85c2e16110b0503c0e01e470786c1eaa02aa8000f1e3c8e3c1e3c783c44544061c187061c187170b85c2e1e083d58000a000f000008e3c1e000000300e0c3830e2c2162c5c2e01e470786c1e3c78f1e00f1e3c79b360003c7a0f078f1e0f1238f07a883d061c187061c187170b85c2e07800000000030e0c38b85c3c0783c0001e3c001e00000000011c783c00601c187061c5842e172a3c78f1e3c7935555551e3c78f3e3c78f1e3c78f1e3c78f1e3c78f1f1c78f1e3d478f1e4c78f1e3c78f1e3c78f1e3d58e8f547aaaa8f4baaaa3d54187061c1830e1c1830e1c1830e1c1830e1c187061c187061d5458b858b858ba162e858ba162e85c2e170b9543c0e07800003c00000187061c5c2e078003c0791c0078008806c000000000187061c0e0c170b828162c0078003c1e0f07803c3600f078000000471e0f00000187061c180c038b85c2c2078003c0000000061c187170b801e0f007800f0783c001e0f000000008e3c1e0000030e0c38300e0c170b8584003c1e03c078f1e3c1e3c78f8e3c783c263c78f0001e3c78f1e3cb88aa8880f01e0f1e24747823d00078088a83d2e20c3830e0c1870e0c1870e0c0381c18030e1c183038a0b85c2c5d0b1742c221602e1f42c78b164281e0703c02600000000000000000000000030e0c3801c0600000002e170102c00000003c0e0d83c00d931e3c78f1e3c40780f078f01e3c11001414000187061c1807060c387060c38703830505c2e1610b1742c5d10b0503c0e1e3c7c755555551e3c78f1e3c78f1e3c78f1e3c7a3d5555551ec7554187061c187061c187061c187061d545c2e170b85c2e170b9543c0e023b1d8e83c1e0f078f1e3c78f1e008f1148e91c00410187061c187061c180703830505c2e170b858443c58f0503c0e1e4d555d8f1e8dd8f3e7c78f2e5c78f478f263c9a5d2eaaaaaaaa4d8eaa83061c383061c3830e0c3830e0c3830e0c3aa8b1742c5d0b85c2e170b85caa1e0703c1eaa003cd8f1e0f00078f1e8800a223d2e0000c3830e0c0383061c383061c381c18282e170b0858ba162e8858281e0703c004000000000000000000000000060007061c187000000058010b85c0000001e07000f0780f3603c783c78f078f1e0f0b8f1e3c1e0f1e3cb84c78f0783c780f1e00f8e0f0783c7891d1e08f4004541e9710780830e0c383061c383061c38300e0c181c061c381c18282e170b1742c5d0b0858b205d10b0503c0e 24 16777215 10 1023
def hc_73_7 : Nat → Nat := unpackHintV5 0xc4e20fb7775bb065c4aae560a6f4fca051a99806138fba138e4c5b8b40c386852f8181417b099e73d5cd6fbd066b6d14657d7c5e99b95a1521533db64c81af3fcf2d3b01333449ae31b0a630e4332955e41c234d15a59f0e15e4047e6600011f 0xf1e0f1e5c1e3cb83c78f078f1e170b83c1e0f263c1e0f0780f1e0f0784c7c7061c187061c187060c0e030e1c1807038305c2e170b858f162c8170fa16110b03c0e001e231e3c79f0787c78f1e0f1e3c79f078f1e3c1e231e3c078f0783c1e4c78f1e3c7803c8e0f1e0f0784c7c71e3cb80f1e0f11e0f02e20f1000980f01830e1c1830e1c187061c1830380c3870601c061c18300e0c162e858ba170b858f162c8170fa16102e162c2160781c00f00780004c01e00f00983c01e00130098000000000000000030e0c380c000e00030003801c060002e1700b160014000b00202058000781c0f0786c1e13271c1e0f1509938e3c36000000030e0c38300e0c038300e07060b85c2d1848c5842c22160781c0200f0000078f00014000000078000000f07801c38300e0c3830e1c1610b85c000bc02e00f010000000000000000002383c000402e00000000030e0c380c000e0300038000007005c2e01600102c0080000003c0e162c58b162c0780f205802c5d0b162c58f1e003cf8f1e0f1e0b058003c780f1e03c0780b058003cb80f1e0000c387061c3830e0c38300e0c1870e0c1870e070601c182c58b162c580f01e40b0058ba162c58b1e7c0078f1e3c1e3c160b00078f01e3c0780f0160b00078f01e5c0001870e0c387061c1870601c1830e1c1830e1c0e0c038300005c2c58000000030e0c383c1e5047078007c5c2c583c002380000000300e0c061c187162c58b0000007803c08016000000b008e000000000000000030e0c3830e0c38000c000e00002c58b16017007810080000000000000000003c0000580000000030e0c3830e0c380c000e000001c0118f118f162c58baa01e132640b1e0f0462c1608c2623271c7802231160b00000187061c1830380c387061c1870601c0e0c038300780f0079b001e3c78f078f01e0f0363e38f1e03c780f01e0003c780f2e0000c387061c38300e0c1870e0c1870e070601c195550555545051540000f007800f00023800000000000000c3830e000300038000550010010040055005c01e000000000000000f0000000000187061c060007000000e055100080000045508c7b3118f1983c264c783c1188c2623271c78cc0446200000c3830e0c181c061c38300e070601c19550b85c1141455233e8cf93264c993264c9a3271d4baa32eaa4d4187061c1830e1c1830e1c187061c187061d0e0d170b858b1742c5d42e170b85cc2d0f0381e013000000000000000000000000000061c18700380c00000005c2e020580000000781c1b0364700000000000008e0f00d800000000000000000000c3830e0070180001c00003870060c0005c2e00a0162c00080008160001e0711c983e38f1e03e380478e4c784c99b01e3c9ab263c36002b078000c3830e0c03830e0c381c9832601c182e170b085c2e21610b03c0e0d91c0d9b00d9b364c2604c261b271c9930984c99b2604cd930993364cf84c364c99b267c2613266c984c2613266c36001b2e06cb80004c42e20c3830e0c0383061c383061c381c18030e4c387064c1830381c182e170b0858ba162e88580ba162c88581e0703c001e0000000000000000000000000000c1800070e0c3830e0000000b002170b80000003c0e03600006c8e00000000047003601b0000000000000000000060c000387061c1870000000e1c0183000058010b85c0000040b0000f03a3c7078f8f1e393078f8f1e38f02e5e3c7060e858b8f1e3972397061b8e471e03c78f8e011e3931e3c260f078f264c786c000781302e030e0c3832381e3830e0c380c393064c18300e0c170b859142e1702e162c2160781c06cd86c8e01b366c783c0784c363e38f2613098f364c078f269c264cd933e0f078f1e3c9a70984c99b267c1e1309931e1b0007970365c000262171061c18706070387060c387060c38703830061c9870e0c9830607038305c2e16450b1742c5d10b01742c5910b03c0e2391c980f8e00f1e3c783c238470780f01e1b000d970d97000187061c1807061c187038300e0c170b85842c5c2c5c42c2160781c0f260f1e3c79326003c78f1e0f01e03c1e3c078f01e1b000d970365c000187061c1807060c387060c387038300e0c170b85842c5d0b17442c2160781c3c9931e6cd8f4e3cf9b367c7a71e3c98f1e4c7931e4c7931e4c7931e4c7a6d1e5d4d97536af49a3d061c187060c387060c387061c187061c1874383458b858b858ba162e85c2e170b985a1e0703c00000000000000000000000000061c18700380c00000005c2e00a0162c00000003c0e 24 16777215 10 1023
def hc_73_8 : Nat → Nat := unpackHintV5 0xcc5456c90cd2c201c3ba29f6b5b91cb1491cab2589a3b1dd984ada8cc6e1892ce67ff64e7bc50c7409ef7060ea68bde95dc6be5bdc7a5739294f36014791e93c9abe35d1b233988e2f6d0b28b1af1c132813da0e0c9dcf07fd280798190001e6 0x30e0c38b85c0f07847078006c1e0011c0000000180706030e0c382c58142e1708c79f0f8f01e13263c1e08c988c2613271c7805c42e200000c3830e0c181c061c38300e070601c182e170b462c5902e4742c221610b03c0e264c993264e393264c993264c99f264c993264c9aa9349a4c9a932ea0c3830e0c3830e0c3830e0c1870e0c1870e87068b85c2e170b85c2c5d0b174c2d0f03836000f00001e0000000000000000000030003830e0c380000002c0085c2e0000000f0381e00f000000007800000000000000000c3830e0070180000000b85c040b00000000f0387a30f83c463c1e08c00787c0b885c40000187061c061c38306070601c0e0c038305c2e05c8e85a3162c858442c2160781c03c07803cd800f1e3c783c78003c780f1e03c078000f1e03cb800030e1c1870e0c0383061c383061c381c1807060b85c2c2162e858ba21610b03c0e0788c1e1f1e3c0780f07930078f1e3c7800f3e3c783c780f1e0f0786c7c71e3c078f01e03c01078800f2e03c7800030e1c1870e0c181c061c38300e0c1870e0c1870e070601c182e170b1e2c8170f998b0858ba162e885842c0f0381e231e3c1e2301e03c1e4c01e3c79f1e7c0078f1e3c1e3c078f0783c463e38f1e03c780f01e02f1078800f1e03cb800030e1c1870e0c181c061c38300e0c1870e0c1870e070601c182e170b1e2c8170f85842c5d0b17442c2160781c00f000078003cd8003c7800000000000070e0c03830187061c5842e170f3e7c78f468cf9f1e4c98f3e3c78f1e3c98f263d38f263c7931ea7d57abd1e5d57975268f41870e0c387061c187060c387060c387061c187438345c2e170b858ba162e85c2e6168781c00002803e380000047000000000000000380000c3830e0000000002e1700000781c0f001e1f0078023009807c0260f2380000000004c0460000011c00000000000000187061c00e030018001c0000005c2e00a0162c0058b000a0000000f0381e0f08e0f0000d9b000781b008e00000000c03830187061c1604cc5c2e03603c00d931e3cd9b001e3c783c0d806c78f01e3c0786c00865c1f97000061c1870601c1830e1c1830e1c0e0c038305c2e1610b1742c5d10b08581e0707c79b0d8f3e0f2380f1e132601f3e3c78f1e0f0366c36130d938e3c780f1e03c3605c42e2006cb81f2e0000c3830e0c181c061c3830600c383061c383061c381c1807060b85c2c58b205cce85842c5d0b17442c2160781c478e47023c7238478e011e3870f1e3800047023c700008e11c000008e11c00000000387238470187061c000000005c2e00000f0380f808c02601f009806c3e01f00000791c001180004c00000023800000000000000003060001c3830e0c380c000e03000000058010b85c02c580050000000781c03c078f1e3c7800f1e003cd8f0780f00d8f1e03c780f078003cb80f1e0000c3830e0c0383061c383061c381c1807060b85c2c2162e858ba21610b03c0e078f1e0f1e3c078f0791c1e4c01e3c78f3e3c783c078f0783c363e38f1e03c780f078171078800f1e03cb800030e0c383060701870e0c0383061c383061c381c1807060b85c2c78b1640b87d0b0858ba162e885842c0f038078f0791c7800f5478f01e3c78f001e0f238f1e03c078000f078000c387061c38300e0c3830e070601c182e170b085c2e21610b03c0e1e0003c001e11c001e00007061c1872170b81e0f0783c000360f07800f0238f0000000000601c1807061c187058b0285842e1703c783c78f1e03c7ab1e471f1c078f1f1c0791c8e3c1e001b158000c3830e0c03830e0c381c1807060b85c2c7843c5c2e21610b03c0e001e3c78f3e0f1e3c783c463c78f3e0f0f8f1e3d383c1e03c783c463c783c983c8e3c780f1e3c1e3c1e0f098f8e3c1e0f1e03cb805c41e200000c3830e0c1870e0c1870e0c181c061c38300e070601c182e170b1742c5d0b1e2c5902e1f42c221610b03c0e0783c0078f1e3c78f001e4c78f0783c1e0131e3c78f078003cb80f1e01301e030e0c38300e0c1870e0c1870e030e0c1807060b85c2c2162e858ba05c2c5842c0f0380780f00780f1e3c791c08e3e380f2391c78f01e0f1001e0f08e11c061c3830e1c1807061c1872387071c038305c2e1610b85c4785c708581e0703c1e0f0780006d583c78003c08e3c000000000018070601c187061c060b16050b085c2e05c78f1c81e3c1e3c078f1e3d58f8e0f2383c78f8e03c8e471e0f000d811c2380c3830e0c0e070e0c3830e470e0e3807060b85c2c7910fa170b88f0b8e10b03c0e 24 16777215 10 1023
def hc_73_9 : Nat → Nat := unpackHintV5 0xc01cc3bc1d00b4b9d9aa928aa2d5ef9c2daa97cd1893bd0487830f835d097c6dbc78350e7055f86417105e1d7e5ac8d55411ae4dc19449611841dde13ec8c534669930550428f1d924153723981f22dc2f1832ab1141bc0d44ff094500000251 0x23c78e4723800000030e0c38000000b85c0000001e070000f01e0011e3c72391c1e0000000000000030e0c3800000000b85c00001e0703c1e0f238f01e3c263c078f1e03e380f1e3c07a03c78f078000f05e0f0780c3830e0c03830600c3830e0c381c182e170b0858b0170b85c42c0f0381e0f0789c78f078131e00f363c78f1e7c783c0d8f8e0f0783c78f1e3c783c000788bc478f01e5c000187061c1807060c0e030e1c1830e1c1830e1c0e0c038305c2e1610b1640ba162e858ba21610b03c0e1e6cd8f1e9cda71e3c78f1e4c7931e9c7a6d36af479754e5d49a3d061c187061c187060c387060c387061c187438345c2e170b858ba162e85c2e6168781c0f238f01e3c78f01e3c01478f0780f1e3c26471e3c0783c00361b000187061c1807061c187038300e0c170b85842e1710b08581e070000000f08e47238047238000000004708e000c3830e000000002e170004708e001e070008803c8e00000f0023800000000000030e0c3800000000b85c0000000001e07000f0780f1e6c1e0f1e0f078f0787c78f0788c78f1e7c1e1f1e3c7a7098f0791c78f01e3c784c7c70783c1e3c783c1e3c079700007885c4104187061c1830e1c1830e1c1807060c0e030e1c0e0c038305c2e162e858ba1610b1640ba285910b03c0e0001e0004702391c02391c000000000061c18700000380000b85c0000400001e0700f1e0f238f01e3c78f0051e3c1e03c78f0991c78f01e0f000d86c00061c18706070387061c187038300e0c170b859142e1710b08581e0703c0000007847008e4708e4701e000000000c3830e000000002e170000000000781c03c785c2e0f0785c78f0b8f1e0f1e3c1e3c784c78f0783c1e04c7c70783c1e3c187061c187061c1807060c0e030e1c0e0c170b85c2e1610b1640ba2160781c003c1e3c078f360f0783c1e3c79f0787c78f1e9c1e0f1e0f0f8f1e131e3c78f1e3c01e47098f8e0f0783c78f1e5c078f0788f078000f10b88003061c383061c3830e0c38300e0c181c061c381c1807060b1742c5d0b85c2c2162c817442c2160781c0000f0078000f0078002000470000000000100b800000c3830e0003000380c000e00002e170002c0081600400001e07083c0001e0f6e0003c1e00000f0b800c03830e0c380c5842e1702c0003600f00000005e00080011c0000000078000000017001000061c18700018001c0600070000060b85c000b0020580100000b03c0e3e7c993264c993271c993552ea5d49a830e0c3830e0c383061c383061c3830e0c3a1c1a2e170b85c2c5d0b1742e1730b43c0e0008e4702391c8e00f0000000000000061c1870008e11c00005c2e0008e11c00003c0e00f91c0000000098000470007801b0f8008c02601f00980000000000000000030e0c3801c06000070000380c0005c2e00a0162c00080008160001e0703c23803c238000f07803c0000003830e0c381c1842e1710b03e470367c0367c984c0d938e1309932604c98133e13266c2613267c984c99f0d8006cb81f2e0001310b8830e0c38300e0c1870e0c1870e070600c387060c0e07060b85c2c2162e858ba21602e858b22160781c0047008e4723811c0003600000000000000c3830e000000002e1700040000781c07c0000f91c00000980011c000009807c0261f00361f0000000000000000000060c000387061c187000000380c000160042e1700000102c0003c0e078f2380f1e3c78f01e01b1e00f1f1c7931e0f0783c2e17078070e0c3830e0c3830f42e170b85d1c023972391d0b83c4b81b3e1f23806cf9f1e0f0363e383c263c980f2603c784c99b0783c7932613263c36000f2e05c000262171061c18706070387060c387060c38703830061c3830607038305c2e16450b1742c5d10b01742c5910b03c0e239b8e47371c361b099326130464c464d186c2391c8e470000061c187071c8e470f1c1807038300e0c170b85c72391e8e2c221610b03c0e001100791c00000008e0000000000000c3830e000000002e170000000000781c0ac0238047238000011c238000000000000c3830e000000002e170000000781c3c9931e7cf8f1e8cf9f563cf8f1e4c78f263c98f263c98f263c98f263d3e8f2eaacbaaf57a4d1e830e0c383061c383061c3830e0c3830e0c3a1c1a2e170b1742c5d0b85c2e1730b43c0e 24 16777215 10 1023
def hc_73_10 : Nat → Nat := unpackHintV5 0xd815d4d1d98fcd5d1fc45e40bef55ab68a1bb27505ab0ddaa31dfc96672e8d92358949128225c97de11179d50372c1c56bf1b4636a225d0d97509f1c49f9a93da7153711a5328d212eb4f62a65142385b81f610918a5af10d9f3068e930001a3 0x6cf84cd930f86cf87cd87cf9f0d8230981301187c3605c42e200000c3830e030e1c18303830381c381c1807060b85c0ba162c8591442c2160781c3c780f1e3c78f01e3c078f1e3c01e3c78f1e3c98f1e3c78f0984cb83c362f098f0e1c187061c187061c183a170b85c2e162cd9b02e3c78206cd9b3601b1e0f0d8bc2e974ba5c44387061c187061c187a170b85c2e459b367cd9f366cf93266c99b3e6cf9f3e4cd93364c99b4e4c993267d369b5365d4ba935061c187061c3830e1c1830e1c1830e1c187061d0e0d170b85d0ba162e858ba170b985a1e07134b972e5cb973e7cf9f2e97267c99f264c9830e0c3830e0c3830e0c3830e0c38b85c2e170b85c2e170781c4c9933e7cf9f3e7cf9f3e7cf9f3e7c993267c9c7264cf9f2ea7cba7d4fa7d526a0c1870e0c1870e0c3830e0c3830e0c3830e87068b1742c5d0b85c2e170b85cc2d0f0388e00f8f1c08e11c001e00000000000000c3830e000000002e170000000000781c0f01e470000001e470009800000f00460130002600000000000000000000030e0c3801c0600000007018000b85c01402c58000000500b160001e0711c791c791c078f8f1c78f01e3c78f0d803c78f1e3c8e3c8e003c1e03c0b80c387061c38300e0c3830e030e0c1807060b85c2c2170b8170f163c58b08581e0700f1e0f23803cf8f1e3c1e3c78f8e003c783c263c78f01e3c786c7a70783c1e3c78f4e0f098f1e3c1e13078f1e03c00078f01e5c0001e2171061c3830e1c1807060c387060c38703830061c3830607038305c2e1610b1742c5d10b0170fa163c58b22160781c3c9931e7cf8f1e8d5ab1e9c793271c79f1e4c79f263c98f263d3e8f2eaacbaaf57a4d1e830e0c383061c383061c3830e0c3830e0c3a1c1a2e170b1742c5d0b85c2e1730b43c0e07803e3c7023804708e00000000000000030e0c3800300000005c2e0000000000f038361b4e1b3e1f369c264c984c02604c26130984c360005c42e2000c3830e0c18030e0c181c061c381c1807060b85c2c2162c817442c2160781c0f00791c00010000008e00000000000000c3830e000c000000170b80000000003c0e01e00f0078470007ab0780000000000000070e0c038300e0c3830e2c21610b85c471e3c1f1e38f007ab1e3e383e38003c0780f238f23800f1e0f2e00030f1c1878e0c0383061c1830e070601c182e170b085c2e21610b03c0e119f3e1f0f813264c2604c2613098130261f02e21710000061c187060c0e030e1c1830061c0e0c038305c2e162c81742c221610b03c0e3e7c993264c99f271c993264c993264c993264c993269f549a4d264d49975061c187061c187061c187060c387060c387438345c2e170b85c2e162e2742c98b174c2d0f0381e03c8e000003c01e000000000047000000000000000000187061c00e03000018001c00005c2e00a0162c0001600400001e0703c8e03c786c1e6c361f1e6c264c01e3c78f1e6d38132606c98f1e6cf8f0781b271c36130d8f1e1b098f363c0786c0d801710b89b2e06cb800030e0c3830600c383060701870e0c1870e0c1870e070601c182e170b0858b205d0b1742c5d10b08581e0701b00001e470003601b0000000008e000000000000000000003060001c3830e0c380c000600070000058010b85c000b00200000f038078f0791c1e271e3c1e1f1e3c263c01e6c78f1e3cf80f2603c98f1e3d38f0781b1f1c1e0f078f1e3c1e131e3c780f078000f10b88f1e03cb800030e0c38300e0c181c061c383061c383061c381c1807060b85c2c2162c81742c5d0b17442c2160781c0f000000001e003c4e01f00000000008e00000000000000000030e0c3801c0600003000380000b85c01402c580002c00800003c0e2391c02381b01e0011c238000011c2380000004708e030e0c38000000000b85c00001e0703c00000000000000000000000000061c18700380c0000002a8216000001542e162c1e1100000000000000000000000000000000030e0c3830e0c3801c0600000003d3a70d83d387c261f098f0782309813001e1b02e21710000061c18701870e0c181c1807038300e0c170b81750b162c858442c2160781c0003c07800478f1c8e470780000003c000000061c187000000000170b800003c0e0783c078f0791c784c78f1e03c07c701e3c780f4078f1e0f00000783c061c1870601c1807061c187038305c2e1610b085c2e2160781c0f0783c78f078f1e131e3c781702e3c7885c78f1e0f0363e383c1e0f1e3c1e030e0c38300e0c181c061c3830e0c381c182e170b0858b205d0b85c42c0f0381e0f0780f0f8f1e131e00f363c78f1e9c783c0d8f8e0f0783c78f1e3c783c00078823c783c478f2e0000c3830e0c0383060701870e0c1870e0c1870e070601c182e170b0858b205d0b1742c5d10b08581e0700f00000000001e1f07800000000011c000000000000000000060c000387061c18700018001c0000160042e170002c00800003c0e 24 16777215 10 1023
def hc_73_11 : Nat → Nat := unpackHintV5 0xc3ccf2bd4da0af8772a859cba3c1269b0a2e9026b98c15048a0484865cea800197794dad7678b572bcef6df93168017e5e965b521f1e4e70eb4cf45f4a24b4457d2a41d8e936a2ce3344d72f2907236eef1c59c51519d0108d23090de0000243 0x3c0783c000360f08e3c00000000000038301807061c1870a058b05842e170f1e3c78f01e3d58f23c78e3e391c1e3c783c1e0f000d8ac00061c18703830187061c0e0c038305c2e21e2c782e1710b08581e070f264c78f366c78f1e3d5ab1e3cda71e3cd9f367c78f56ad58f1e3c79b271c79b1e4c79b363c7931e3c98f1e4c98f1e4c98f4da3d55ab536af4d975565d49a3d061c187060c387060c387061c187060c387060c387061c187438345c2e162e858ba170b858ba162e85c2e6168781c3c78f1e3c7c78e0471e3cd8f238f2383c0783c1e0f8e0f8e001b0d8000c3830e0706030e0c381c1807060b8f0b8f10f163c170b885842c0f038d9b1e6c07826cd81b3601b563c1e1b158972e974ba5c449a0c3830e0c3830e2e170b85c8b366cd9b4e6c99b3e6cf93266d3a7564cd93364c99b3e4c9ab3e4c9a6d36a6cba97526a0c3830e0c3830e0c1870e0c1870e0c3830e87068b85c2e170b1742c5d0b85cc2d0f038f9f0787c78f56ad5800f1e0f3e0f1e0f11ab563c783c260f0987c8e3cf80f3e7c1e03c0b885c4787c1e0ad58000003060701870e0c3830e0c1870e0c1870e0c0381c1807060b1640ba170b858ba162e858442c2160781c03e3800020003c000000023800000000000c3830e000000002e1700000000781c0000f0008e0f0000000061c187060b85c3c001e000f08e0f00780000000000000300e0c03830e0c38b085842e170f1e47238f8e3c7ab1e0000f238f238f1e0f1e000f0783c1e000300e0c3830e0c3830e070601c182c2170b85c2e21610b03c0e3e7c261f564c468c3e07c261f09ab0f802302e21710f800000c181c061c3830e0c38300e070601c182c5902e85c2e16110b08581e070000f00780f07800471e000000030e0c38300e2e170b08780f00783c1e00f0008e3c001e0000000300e0c03830e0c38b085842e170f1e03c1e0f23c78e3e391d78bc1e0f000187061c187061c0e0c038305c2e170b885842c0f038780f1eac780003c8f1e38f8e471e3c7800f0783c1e000300e0c3830e0c3830e070601c182c2170b85c2e21610b03c0e1e3c78f1e3c78f1e3cdc71e3c78f1e3c78f8e3c78f1e3c7a3d1e3c78f1e3c78f1e8f478f47af4dabd1e8f4187061c1830e0c187061c187061c187438345c2e162e162e170b85c2e6168781c3c78f1e3c78f1e3c78f369c78f1e3c78f1e3d18f563c78f1f1c78f1e3c78f1e3c78f1e3c78f1e8f478f51ebd4dabd1e3d479751e8f4187061c1830e1c1830e1c187061c1830e1c1830e1c187061d0e0d170b858ba162e85c2e162e858ba170b985a1e07003c7883c78f00078f1e3c78f1e0f07a883d061c187061c187170b85c2e078000000000030e0c38b85c3c0783c001e00000f1e0000f001807061c1871610b85c03c78f07a0f1e3c78f05550001e3c791c783c78f1e3c1e222a2030e0c3830e0c38b85c2e170f01e0f3600028003c001e0f0008e3c1e0000000300e0c3830e2c2170b878f1e3c78f551e3c78f1e3c78f1e3c78f1e3c78f1e3c7c71e3c78f1e3c78f1e3c78f1e3d55551e97547aaa8f55061c187060c387060c387060c387060c387061c187061c18755170b858ba162e858ba162e85c2e170b9543c0e01e20f07808802b158000473e1f00000000187061c0e0c170b885801b366d58ad00550005552e5cd91cd86cda0f111510187061c187061c5c2e170b878f5551e4c9aa8f3e7c7972e5cb972e3d7ab56ad58f5e3cf938e3cf8f26aa3c7a8f3e7c7931e4d1eaa8f51e9755555551e830e0c383061c383061c383061c383061c3830e0c3830e0c3aa8b85c2c5d0b1742c5d0b1742e170b85caa1e0713264cf9f267c9c73e7c9933e7cf93269f4ba975526a0c3830e0c1870e0c1870e0c3830e0c3830e87068b85c2c5d0b1742e170b85cc2d0f038367c3e3c3e3cf87c79f09931e0f0098130984c26131e1b0002e217100061c1870601c1830380c387038300e0c170b85842c5902e885842c0f03801e00f162c58b0a01e00000000000000000000000000000c3830e030003830e0c380000007c79f0f8f3e1b3e1f1e13263c1e04c2613098130263c3605c42e200000c3830e0c181c061c38300e070601c182e170b162c81733a16110b08581e071f3e7cf933e4e393264c993264c9933e4c993264c993264c99f4faa4d269326a4cba830e0c3830e0c3830e0c383061c9870e0c983061c3a1c1a2e170b85c2e170b1742c5d30b43c0e 24 16777215 10 1023
def hc_73_12 : Nat → Nat := unpackHintV5 0xe3d4afdfe8fbdd2cafd940fbd4992aceb978c8459dc2c161bbc1c0b2ee35a9e243a209f69ae1ca927e198736d282e5147bd1c578acc974b0ff6f7d4d639ef854dbb154701a4f2d514622433fe19033bb0a2cf9b01fff3f10afd40a5596000295 0x170b1e0000000000000000000c3830e0c3830e0000002e162c00000000001e02c000000000000000061c187061c187000000380c0000000000000005c2c7800000030e0c3800000030e0c38b858b0780b00000000000000000000000000187061c187061c00e030000000078080b858b02100000000000000000000780000b0000000061c18700380c0187061c0000005c2c58faa367e387c782c83e7c783c160b00000786c160b01040000187061c187061c061c38306070601c0e0c03830f9f8e7cf9f3e7cf9f264d3e9752eaaa0c3830e0c1870e0c1870e0c3830e0c3830e87068b85c2c5d42c58ba170b85c2e6168781c411c8e4723802c58b80da701e0000472391c8e000000472391c8e00000c3830e01c02391c8e47061c18700000f9f369cfa7369cf8011c8e47239b0f800472391c8e6c3e0001c180e391c8e1e3830e0c381c180706133160b8e4723d1c5c2e21610b03c0e1e9cd9f367cfc71e7d39b3e7c78f1e3c78f363d38f263c7931e9b4dabd1e5d539755e8f4187061c187061c1830e1c1830e1c187061d0e0d170b85c2e162e858ba170b985a1e070f3e7c78f263cf8f3e3c98f4e4c98f26ac78f3e3cf8f1e4c7931e7cf8f4faaacba8f2ea4d1e830e0c3830e0c383061c383061c3830e0c3a1c1a2e170b85c2c5d0b1742e1730b43c0e3e7e39f3e7cf9f3e7cf9f3e7cf9f3e7cf933e7c99f4faa7cba9f2eaa0c3830e0c3830e0c1870e0c1870e0c3830e87068b85c2e170b1742c5d0b85cc2d0f03879f0987c7931184c0987c1e1f3e3c3e3cf802302e21711e1f0001041830380c387061c1870601c0e0c0383058b205d0b85c2c2285910b03c0e3e7cf9f3e7cf9f3e7cfa78e7cf933e7cf933e7cf9f3e5d4f9753e9f55419f060c387060c39f0e1c187061c187061c187061d0e0d162e858ba170b85c2e170b985a1e070f1e6cf83c3e0f367c79b1e7c78f01e3c01e0f0783c0078f01e3c078f01e6c01e2171001e3c07af000060c387060c38701870e0c181c1807060c387060c387038300e0c162e858ba05c3e858f162c85842c5d0b17442c2160781c2e162c161103c8e000000000000000000000000000030e0c3830e0c3801c0600000003cfa7367cfc70f8f4e1f3e3c1e08c2604c00786c0b885c40000187061c061c38306070601c0e0c038305c2e05cce858b1642c221610b03c0e0238500f8e0000000000000000000c3830e0000100550000551000047162c5c02c580f8e0000000000000000000c3830e01c000061c18700000f9f8e3cfa9b3e7e380000f07800003c4e0001c180c03830e0c381c18070610b05842e1710b08581e0700f1e0f23803cf8f1e3c1e0f07804c78f1e9c78f0784c78f078f1e0f0784c1e131e3c783c78f078003c780f7601301e04c41e20c3830e0c0383061c383061c380c3830600c387060c0e07060b85c2c2162e858ba05c2c580ba162c88581e070f1e3c78f1e9e38f1e3c78f1e3c78f1e3c98f1e3cd8f1e3c79f1e3c78f263c78f1e3c78f1e3c78f363c78f1e3c7a71e3c78f1e9c7a3d36af479751e3d478f51ea3d7a3c7a0c3830e0c3830e0c1870e0c1870e0c1870e0c1870e0c187060c3a1c1a2e170b85c2c5d0b1742c5d0b1742c5c2c5cc2d0f038d8001701e3c7800f1e6c0b803c78f1e3c78f1e288f52e88f4783d51e8f061c187061c187060c3a2e170b85c2c58f3e7c78f463c98f263c79f264c7933e3c78f1e3c98f263d3a71e9f54ba8f2ea4d1e830e0c3830e0c383061c383061c383061c1830e87068b85c2e170b1742c5d0b170b1730b43c0e078f2380f1e3c0d82970400155478f1e6c78f1e3c7897098f4ba3d2e288f547a3c187061c187061c183418b85c2e170b168b1e9cd9f367d3c71e3d554b975551ebd39b3e7d5478f1e3c78f363c797263c797263d38f763c7a747aaa5d551ea3d2eaaaaa3d061c187061c187060c387060c387060c387060c387061c18755068b85c2e170b1742c5d0b1742c5d0b85caa2d0f038f9f3e7d3c73e7cf9f3e9c9a7269f5539752eaa0c3830e0c3830e0c1870e0c1870e0c3830e87068b85c2e170b1742c5d0b85cc2d0f03801e3c78f1e3d383c263c78f260f118f1e7e383c78f01e3cd83c1e3c1e7c1e471e3c078f1e0f078f260f1e0f001e3c1e7c1e3c0797007885c40000187061c1830e1c1830e1c061c38306070601c0e0c0383058b858b858ba162e8170fa163c58b216110b08581e070f1e3c78f1e3c78f3f1c78f1e3cda71e3c78f1e3c78f1e3d18f1e3c98f1e3c98f1e3d38f3e3c78f1f1c78f1e3c78f1e3c78f1e3c78f1e3c98f1e3c78f1e8f478f51e5d4dabd1e3d479751e8f4187061c1830e1c1830e1c187061c1830e1c1830e1c187061d0e0d170b858ba162e85c2e162e858ba170b985a1e07003c1e471e3c07888f1e00f0780f1e0f238f001e0f0783c0000061c187061c187038301807038305c2e170b88582c22160781c00f1e3c78f1e9c1e0f1e3c1e231e3c1eac1e471e3c078f1e0f1e003c1e0f1e03d7803c42e200000c3830e0c1870e0c1870e030e1c183038300e070601c182e170b1742c5d02e1f42c78b1642c221610b03c0e 24 16777215 10 1023
def hc_73_13 : Nat → Nat := unpackHintV5 0x34438dc93beaeedb1ae869a839b49acb0e4c6f686b635e998a6d76799b6d35e1465577074f434d286a543834cedd0230d550853f11bd2bc4fefb09a52c00134 0x1e03c00983c8e00000000008c000000000000000000061c18700380c000e030000000170b802016001402c580000000781c0f023c78e4723800000000000000030e0c38000000000b85c0000000001e0703c0791c000078000001300007803c0000000000000000000000187061c00e0300000000e1c0183000170b80201600000040b0000f0381e00f00780130791c000000007800002300000000000000000000187061c00e03000380c00000005c2e0205800402c00000003c0e1e9c263c981b0787c261f098f07823460230786c0b885c40000187061c061c38306070601c0e0c038305c2e05d0b1642c221610b03c0e0008f1e391c8e000000000c3830e0000002e170000000781c0011e3c72391c001e00000000000030e0c3800000000b85c0000000001e0703c0791c00000000980000f0046000000000000000000c3830e0070180000001c060002e1700402c00000028058b0000f0381e03c010791c00000000000000000000402e000000030e0c3801c0600070180000000b85c0100b000a0162c00000003c0e0780806c010d91c000000000000000000007800001700100000061c18700380c000e030000000170b8081600100b00000000f0381e0000000000000000000030e0c3801c060000001541000000550003c000001e00f00000000000000000187061c0000003870060c002a800020088002a81e00f000000007800000000000000000c3830e00701800000055011000004005500000003c0000000000000061c187000000380c002a80000200aa1f5000000000000000000030e0c3830e0c380000003c0000000000000000000061c18700380c0000002a82000000aa078080000000000000003c00000000061c18700380c0000002a804800000022a87b3367d9c70f8f0f9f1e0f00000786c0410000061c18701870e0c181c1807038300e0caa85c2e08a0a2a85d0b162c078f0791c16400b162c58ba879b1e3c1e0b058003c780f1e03c1e0b058003c780f2e0000c387061c3830e0c38300e0c1870e0c1870e070601c180000002e163c000000000000187061c0000187061c005c2c583c05800000000000000000000000000c3830e0c3830e0070180000000b858b0000078002c000001e00f005802c000000000000000000061c187061c1870000000e1c018300007803c05c2c58102c0000000001e00002c00000000000000000187061c00e030061c187000000 22 4194303 9 511
def nh_73 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_73_13 (Nat.sub p 416)) (hc_73_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (hc_73_11 (Nat.sub p 352)) (hc_73_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Bool.rec (Bool.rec (hc_73_9 (Nat.sub p 288)) (hc_73_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_73_7 (Nat.sub p 224)) (Nat.blt p 256)) (Nat.blt p 320)) (Bool.rec (Bool.rec (Bool.rec (hc_73_6 (Nat.sub p 192)) (hc_73_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (hc_73_4 (Nat.sub p 128)) (hc_73_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (hc_73_2 (Nat.sub p 64)) (hc_73_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_73_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 224)
def f_73 : Nat → Nat × Nat := unpackForestF 0xccb5fda46cccb5bccb57ccb55d835cd7c64ccb53cca5fcca57d2b5dd2b59d2b55d2b51d3854d2a5dd2a55cc85acd46ed145ccd24dcd249cd245cf25ccd241ce45ccd14dcd145cc85600c5fcb866ca56dca45eca34500c5bc936d00c57c246fc7856c246ec606ac6066c246dc234bc2347c4562c3a4fc2345c2b45c224700c53b246fb2463c0354b245fbed6dbed6cb245bbd56ebd247b2459b2457ba45ebb47cba453ba452b2455b947cb7565b846cb7564b7344b2453b4469b5d7cb4465b4459b4455b225fb2c6db2c61b225700b5fb035eb085eb035600b5bad46dae347ae247ad461ad26c00b57ac464a756fab454a7563a736ea9d6ea735ea7c6ea7c63a7c62a735600b539756f9756b97567975639746fa2c69a285aa28569746ea0d7ca0b44a0a449746b974679f46c9e5749e34497463974629bd689bd649bc7c9736f9957c995709946c9927c973679724f97c7a9724700b4f964648e56f9556e8e56b9447c8e5679235692b54922578e5638e45e9046d904658e36e8f46c8ec6b8e35600b4b8cc558cb557756e8bc6c7756b775638a45777562895707746f87c6e87c6c7746b86c6d86560774678546c7746382d7083c6c82c6982c687736f7f5707f5607f471802477f4707f27c773677734f7734e7d67a7725f79d6a79d627b36c79b6b79a5d7995d7705e77d6277b5d77a5d7705200b47763646f56f754546f56b7437c6f56772b4e72a4f724546f56370c6970c596f36e6fc6e6f35e00b435ac6f5ac636bd6e6bb4b6bb476bb455ac596a45e6a36d5ac5567469674656745967d7c674555ab6f66354645696435e64d68643565ab6361c6d61c6161b5e61b525ab5560468604645ab4f5e5695e45e5e3645ab4b5cd685cc695ab475b37c5b3645ab4300a5f59b554bc6d57b4b57b4757b454bc6156459564554bb6d5447c544705437c4bb4f53354515715137c51d70513564bb4b4e5714e5704e4714ed704e05e4bb474c47c4c37c4c36c4bb4300a574ac643956f49b453956b48c7c3956747b453956345469453554505a450563946e444643936f433543936b4247c393674036c4036440354393633935f3eb543935b3d57a3d46c393573935339d6e39d6239c6b39b4e39b423934500a4f3834521562375702146f35c6c35b452146b2146732c6c334613346032b452146331568314692136f2fe702fb6c2136b2dd702e46c2dc71213672b6702b36c2b35c2b354213632856b2846e284622836e283622135d26d7a26c6c2134f25b5424e7224c6c2134b23c7a2134722b5421e7221b6c2134300a47203641656f1f3541656b1e37c165671cc541cb54165631b4591b4551636e1a46e1635e16d6e16d6b16d6316d6216c6b16c631635600a3f154680156f144580156b134700156711c5811b54015630e5690e5610e35e0e3560e03a0e036014620a56b0cb540a5630a36f0a36e0a3670a3620145a0936e0145206d6906c7006c5a06c520136f045710446004b7c0445a0136702c6802c600135f01c500135700a370003f 9 11
def ch_73 : Nat → Bool := dagCheckNodeV5 fullMask g_73 ep_73 5 31 bds_73 438 (dagTraceF fullMask rootStock 11 f_73) cur_73 nh_73
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsV5 fullMask g_73 ep_73 5 31 438 bds_73 (dagTraceF fullMask rootStock 11 f_73) (cur_73 0) (nh_73 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_0 : treeBlockF 0 32 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_1 : treeBlockF 32 64 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_2 : treeBlockF 64 96 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_3 : treeBlockF 96 128 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_4 : treeBlockF 128 160 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_5 : treeBlockF 160 192 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_6 : treeBlockF 192 224 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_7 : treeBlockF 224 256 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_8 : treeBlockF 256 288 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_9 : treeBlockF 288 320 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_10 : treeBlockF 320 352 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_11 : treeBlockF 352 384 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_12 : treeBlockF 384 416 ch_73 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_13 : treeBlockF 416 438 ch_73 = true := by decide +kernel
theorem nj_73_1 : ∀ i, 0 ≤ i → i < 64 → ch_73 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_73_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_73_1 h1 h2)
theorem nj_73_2 : ∀ i, 0 ≤ i → i < 96 → ch_73 i = true := block_join nj_73_1 (fun _ h1 h2 => treeBlockF_at nb_73_2 h1 h2)
theorem nj_73_3 : ∀ i, 0 ≤ i → i < 128 → ch_73 i = true := block_join nj_73_2 (fun _ h1 h2 => treeBlockF_at nb_73_3 h1 h2)
theorem nj_73_4 : ∀ i, 0 ≤ i → i < 160 → ch_73 i = true := block_join nj_73_3 (fun _ h1 h2 => treeBlockF_at nb_73_4 h1 h2)
theorem nj_73_5 : ∀ i, 0 ≤ i → i < 192 → ch_73 i = true := block_join nj_73_4 (fun _ h1 h2 => treeBlockF_at nb_73_5 h1 h2)
theorem nj_73_6 : ∀ i, 0 ≤ i → i < 224 → ch_73 i = true := block_join nj_73_5 (fun _ h1 h2 => treeBlockF_at nb_73_6 h1 h2)
theorem nj_73_7 : ∀ i, 0 ≤ i → i < 256 → ch_73 i = true := block_join nj_73_6 (fun _ h1 h2 => treeBlockF_at nb_73_7 h1 h2)
theorem nj_73_8 : ∀ i, 0 ≤ i → i < 288 → ch_73 i = true := block_join nj_73_7 (fun _ h1 h2 => treeBlockF_at nb_73_8 h1 h2)
theorem nj_73_9 : ∀ i, 0 ≤ i → i < 320 → ch_73 i = true := block_join nj_73_8 (fun _ h1 h2 => treeBlockF_at nb_73_9 h1 h2)
theorem nj_73_10 : ∀ i, 0 ≤ i → i < 352 → ch_73 i = true := block_join nj_73_9 (fun _ h1 h2 => treeBlockF_at nb_73_10 h1 h2)
theorem nj_73_11 : ∀ i, 0 ≤ i → i < 384 → ch_73 i = true := block_join nj_73_10 (fun _ h1 h2 => treeBlockF_at nb_73_11 h1 h2)
theorem nj_73_12 : ∀ i, 0 ≤ i → i < 416 → ch_73 i = true := block_join nj_73_11 (fun _ h1 h2 => treeBlockF_at nb_73_12 h1 h2)
theorem nj_73_13 : ∀ i, 0 ≤ i → i < 438 → ch_73 i = true := block_join nj_73_12 (fun _ h1 h2 => treeBlockF_at nb_73_13 h1 h2)
theorem nc_73 : ∀ i, 0 ≤ i → i < 438 → ch_73 i = true := nj_73_13
theorem lb_73 : LowerBin fullMask rootStock g_73 12 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_64 (kn_cons lb_69 (kn_cons lb_72 (kn_cons lb_71 (kn_cons lb_70 (kn_cons lb_8 (kn_cons lb_65 (kn_cons lb_66 (kn_cons lb_4 (kn_cons lb_63 (kn_cons lb_67 (kn_cons lb_68 (kn_cons lb_30 (kn_cons lb_29 (kn_cons lb_33 (kn_cons lb_35 (kn_cons lb_57 (kn_cons lb_62 (kn_cons lb_60 (kn_nil))))))))))))))))))))) rc_73 nc_73 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.and, [2, 14]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.or, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974154368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677288 * 2 ^ 32 + 3974154368)) (13 - 1) := by
  rw [show canon fullMask (4276677288 * 2 ^ 32 + 3974154368) = g_73 by decide]
  exact lb_73

end PEqualNP.Outside.L_meta_47681

theorem PEqualNP.Outside.L_meta_47681 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3974154368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974154368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47681.table2_from_lowerBin (4276677288 * 2 ^ 32 + 3974154368) 13 PEqualNP.Outside.L_meta_47681.root_lb PEqualNP.Outside.L_meta_47681.wg 18 rfl PEqualNP.Outside.L_meta_47681.wfits PEqualNP.Outside.L_meta_47681.weval
