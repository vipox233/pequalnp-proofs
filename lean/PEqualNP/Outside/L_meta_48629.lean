import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48629

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

def m_0 : Nat := 0xff000000000000
def s_0 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_0 : Nat := 0x17000000000000
def ep_0 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_1 : Nat := 0xff00
def s_1 : List Nat := [0x5500, 0x3300, 0xf00]
def g_1 : Nat := 0x1700
def ep_1 : Nat := 0x60000000000000012000000000000001400
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

def m_2 : Nat := 0xf0f000000000000
def s_2 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_2 : Nat := 0x107000000000000
def ep_2 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_3 : Nat := 0xff0000000000
def s_3 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_3 : Nat := 0x170000000000
def ep_3 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_4 : Nat := 0xf000f000000000
def s_4 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_4 : Nat := 0x10007000000000
def ep_4 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_5 : Nat := 0x5500550000000000
def s_5 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_5 : Nat := 0x100150000000000
def ep_5 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_6 : Nat := 0x3300330000000000
def s_6 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_6 : Nat := 0x100130000000000
def ep_6 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_7 : Nat := 0xf000f0000000000
def s_7 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_7 : Nat := 0x100070000000000
def ep_7 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_8 : Nat := 0x2222222200000000
def s_8 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_8 : Nat := 0x2022200000000
def ep_8 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x4444444400000000
def s_9 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_9 : Nat := 0x4044400000000
def ep_9 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_10 : Nat := 0x5050505000000000
def s_10 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_10 : Nat := 0x10105000000000
def ep_10 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_11 : Nat := 0x3030303000000000
def s_11 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_11 : Nat := 0x10103000000000
def ep_11 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_12 : Nat := 0x50505050
def s_12 : List Nat := [0x10101010, 0x500050, 0x5050]
def g_12 : Nat := 0x101050
def ep_12 : Nat := 0x10400000000000100040000000000000000000000000001010000000000000000000
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

def m_14 : Nat := 0xf0f000000000
def s_14 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_14 : Nat := 0x107000000000
def ep_14 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_15 : Nat := 0xa0a0a0a
def s_15 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_15 : Nat := 0x2020a
def ep_15 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
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

def m_16 : Nat := 0xaaaa
def s_16 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_16 : Nat := 0x22a
def ep_16 : Nat := 0x28000000000000020800000000000002200000000000000000
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

def m_17 : Nat := 0xcccc
def s_17 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_17 : Nat := 0x44c
def ep_17 : Nat := 0x48000000000000040800000000000000000000000000000440
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

def m_18 : Nat := 0xf0f0
def s_18 : List Nat := [0x5050, 0x3030, 0xf0]
def g_18 : Nat := 0x1070
def ep_18 : Nat := 0x60000000000000000000000000000010200000000000001040
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_18 : Nat → Nat := fun _ => 0
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) (nh_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x5555000000000000
def s_19 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_19 : Nat := 0x115000000000000
def ep_19 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_19 : Nat → Nat := fun _ => 0
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) (nh_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0x3333000000000000
def s_20 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_20 : Nat := 0x113000000000000
def ep_20 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_20 : Nat → Nat := fun _ => 0
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) (nh_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff000000ff00000
def s_21 : List Nat := [0x550000005500000, 0x330000003300000, 0xf0000000f00000, 0xff00000]
def g_21 : Nat := 0x110000005300000
def ep_21 : Nat := 0x420000000000000000000000000000000000000000000000000000001100000003000000110000005000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_21 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_21 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 3 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 3 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 3 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 3 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0x3c003c003c003c
def s_22 : List Nat := [0x14001400140014, 0xc000c000c000c, 0x3c0000003c, 0x3c003c]
def g_22 : Nat := 0x1400340034003c
def ep_22 : Nat := 0x20000800000020000000080000000000000000000000000000000000000000000000000014000400040000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_22 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_22 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 10 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 10 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 10 ch_22 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 10 → ch_22 i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0x3c3c00003c3c0000
def s_23 : List Nat := [0x1414000014140000, 0xc0c00000c0c0000, 0x3c0000003c0000, 0x3c3c0000]
def g_23 : Nat := 0x14000004340000
def ep_23 : Nat := 0x420000000000000000000000014000000300000000000000000000000000000000000000014000004040000
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_23 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_23 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 3 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 3 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 3 ch_23 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 3 → ch_23 i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0x3300cc003300cc
def s_24 : List Nat := [0x11004400110044, 0xcc000000cc, 0x3000c0003000c, 0x3300cc]
def g_24 : Nat := 0x1300440033004c
def ep_24 : Nat := 0x20000800000000000000000000000000000000000200000000000800000000000000000010004400000040
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e3420d0d2420a263a88d993a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_24 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_24 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 10 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 10 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 10 ch_24 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 10 → ch_24 i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_nil) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x2222888822228888
def s_25 : List Nat := [0x888800008888, 0x202080802020808, 0x22008800220088, 0x22228888]
def g_25 : Nat := 0x2000000220008
def ep_25 : Nat := 0x20000800000000000000000002000000220008000200000000000800000000000000000000000000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := []
def cur_25 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d3c30c1e302080e3024b263988c592e548902e108800f 7 127 3 7 10 1023 14 16383
def nh_25 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_25 : Nat → Nat × Nat := unpackForestF 0xc72631f1814b8a4442e51824b084400f 3 10
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 10 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 10 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25 : treeBlockF 0 10 ch_25 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 10 → ch_25 i = true := fun _ h1 h2 => treeBlockF_at nb_25 h1 h2
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_nil) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xff00ff0000000000
def s_26 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_26 : Nat := 0x100170000000000
def ep_26 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def hc_26_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_26_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_26 : Nat → Nat := fun p => Bool.rec (hc_26_1 (Nat.sub p 32)) (hc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 43 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) (nh_26 0) s_26 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 43 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_3 (kn_cons lb_5 (kn_cons lb_6 (kn_nil))))) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xffff000000000000
def s_27 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_27 : Nat := 0x117000000000000
def ep_27 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_0, s_0, 4, g_0), (m_19, s_19, 4, g_19), (m_20, s_20, 4, g_20)]
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def hc_27_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_27_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_27 : Nat → Nat := fun p => Bool.rec (hc_27_1 (Nat.sub p 32)) (hc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_0 (kn_cons lb_19 (kn_cons lb_20 (kn_nil))))) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xff00ff00000000
def s_28 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_28 : Nat := 0x17007700000000
def ep_28 : Nat := 0x60000000000000000000000000000600000000000000120022000000000014004400000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def nh_28 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xf0f0f0f000000000
def s_29 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_29 : Nat := 0x10107000000000
def ep_29 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_14, s_14, 4, g_14), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def hc_29_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_29_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_29 : Nat → Nat := fun p => Bool.rec (hc_29_1 (Nat.sub p 32)) (hc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) (nh_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 ch_29 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 ch_29 = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_14 (kn_cons lb_10 (kn_cons lb_11 (kn_nil))))) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xf0f0f0f00000000
def s_30 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_30 : Nat := 0x107070700000000
def ep_30 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xcccccccc00000000
def s_31 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_31 : Nat := 0x4044400000000
def ep_31 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x3333333300000000
def s_32 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_32 : Nat := 0x113133300000000
def ep_32 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_20, s_20, 4, g_20), (m_11, s_11, 4, g_11), (m_8, s_8, 4, g_8)]
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_32_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_32 : Nat → Nat := fun p => Bool.rec (hc_32_1 (Nat.sub p 32)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) (nh_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 ch_32 = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV5 (kn_cons lb_6 (kn_cons lb_20 (kn_cons lb_11 (kn_cons lb_8 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xaa00aa00aa00aa
def s_33 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_33 : Nat := 0x200220022002a
def ep_33 : Nat := 0x20000800000020000000080000000000000000000200000000000800020022002200200000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := []
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_33_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_33_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_33_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_33 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_33_2 (Nat.sub p 64)) (hc_33_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 64 (dagTraceF m_33 s_33 5 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 64 bds_33 (dagTraceF m_33 s_33 5 f_33) (cur_33 0) (nh_33 0) s_33 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 64 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 64 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 64 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 6 :=
  lowerDagV5 (kn_nil) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xaaaaaaaa00000000
def s_34 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_34 : Nat := 0x2022200000000
def ep_34 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x5555555500000000
def s_35 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_35 : Nat := 0x115155500000000
def ep_35 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_19, s_19, 4, g_19), (m_10, s_10, 4, g_10), (m_9, s_9, 4, g_9)]
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def hc_35_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_35_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_35 : Nat → Nat := fun p => Bool.rec (hc_35_1 (Nat.sub p 32)) (hc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 43 bds_35 (dagTraceF m_35 s_35 6 f_35) (cur_35 0) (nh_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 ch_35 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 ch_35 = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → ch_35 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → ch_35 i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_19 (kn_cons lb_10 (kn_cons lb_9 (kn_nil))))) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x6666000066660000
def s_36 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_36 : Nat := 0x6000004260000
def ep_36 : Nat := 0x420000000000000000000000006000000220000000600000404000000000000000000000000000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
def cur_36 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_36 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_36 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 3 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 3 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36 : treeBlockF 0 3 ch_36 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 3 → ch_36 i = true := fun _ h1 h2 => treeBlockF_at nb_36 h1 h2
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_nil) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0x3030303030303030
def s_37 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_37 : Nat := 0x10103000301030
def ep_37 : Nat := 0x20000000001020000010000010002000300020000000000000000000000000000000000010100000001000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xcccc0000cccc
def s_38 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_38 : Nat := 0x4440000044c
def ep_38 : Nat := 0x800000000000000000000004000000048000004000000040800000000000000000000044400000440
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0x3333000033330000
def s_39 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_39 : Nat := 0x113000001330000
def ep_39 : Nat := 0x20000000000000000000000012000000320000010200000100000000000000000000000110000001000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_20 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0x5555000055550000
def s_40 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_40 : Nat := 0x115000005150000
def ep_40 : Nat := 0x400000000000000000000000014000000100000010400000504000001100000001000000000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_19 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0x5500550055005500
def s_41 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_41 : Nat := 0x100150005001500
def ep_41 : Nat := 0x400000000001400000010000000000000000000010004000500040001001000000010000000000000000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xaaaa0000aaaa
def s_42 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_42 : Nat := 0x2220000022a
def ep_42 : Nat := 0x800000000000000000000002000000028000002000000020800000222000002200000000000000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xf000f000f000f00
def s_43 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_43 : Nat := 0x100070005000700
def ep_43 : Nat := 0x400000000000600000002000000000000000000000000000000000001000200000002000100040005000400
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xcc00cc00cc00cc
def s_44 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_44 : Nat := 0x400440004004c
def ep_44 : Nat := 0x800000040000000480000000000000000000400000004000800000000000000000004004400040040
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xffff
def s_45 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_45 : Nat := 0x177f
def ep_45 : Nat := 0x68000000000000060800000000000012200000000000001440
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_18, s_18, 4, g_18), (m_17, s_17, 4, g_17), (m_16, s_16, 4, g_16)]
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_45_1 (Nat.sub p 32)) (cc_45_0 p) (Nat.blt p 32)
def hc_45_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_45_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_45 : Nat → Nat := fun p => Bool.rec (hc_45_1 (Nat.sub p 32)) (hc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 43 bds_45 (dagTraceF m_45 s_45 6 f_45) (cur_45 0) (nh_45 0) s_45 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 ch_45 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 43 ch_45 = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 43 → ch_45 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 43 → ch_45 i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_18 (kn_cons lb_17 (kn_cons lb_16 (kn_nil))))) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff00ff00
def s_46 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_46 : Nat := 0x5001700
def ep_46 : Nat := 0x12000000000000000000000000000500060000000000000012000000000005001400
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff00ff
def s_47 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_47 : Nat := 0x37007f
def ep_47 : Nat := 0x480000000000000000000000000004000800000000003200200000000000040040
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xf0f0f0f0
def s_48 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_48 : Nat := 0x301070
def ep_48 : Nat := 0x10400000000000300060000000000000000000000000003010200000000000001040
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf0f0f0f
def s_49 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_49 : Nat := 0x507070f
def ep_49 : Nat := 0x2080000000000020008000000000000000000000000000202000000000005040400
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xcccccccc
def s_50 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_50 : Nat := 0x404044c
def ep_50 : Nat := 0x480000000000000048000000000404040800000000000000000000000004040440
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xaaaaaaaa
def s_51 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_51 : Nat := 0x22022a
def ep_51 : Nat := 0x2080000000000220028000000000000020800000000002202200000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xff000000ff0000
def s_52 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_52 : Nat := 0x17000000370000
def ep_52 : Nat := 0x20000000000000000000000000000000000000000600000004000000120000003200000014000000040000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xf000f000f000f0
def s_53 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_53 : Nat := 0x10007000300070
def ep_53 : Nat := 0x20000000000060000000400000000000000000000000000000000000100020003000200010004000000040
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xf0f00000f0f0000
def s_54 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_54 : Nat := 0x107000005070000
def ep_54 : Nat := 0x400000000000000000000000006000000020000000000000000000001020000000200000104000005040000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x5050a0a05050a0a
def s_55 : List Nat := [0xa0a00000a0a, 0x101020201010202, 0x5000a0005000a, 0x5050a0a]
def g_55 : Nat := 0x10502020505020a
def ep_55 : Nat := 0x400000800000000000000000004000000000008000000000000000001000202000002000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e3420d0d2420a263a88d993a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_55 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_55 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 10 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 10 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 10 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 10 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x4444888844448888
def s_56 : List Nat := [0x888800008888, 0x404080804040808, 0x44008800440088, 0x44448888]
def g_56 : Nat := 0x4000004040008
def ep_56 : Nat := 0x400000800000000000000000004000000000008000400000404000800000000000000000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d3c30c1d3020c0e3024f263e88c993e54c903e10c800f 7 127 3 7 10 1023 14 16383
def nh_56 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_56 : Nat → Nat × Nat := unpackForestF 0xc7c632e9814f8a6443e51824f086400f 3 10
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 10 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 10 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 10 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 10 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x4444444444444444
def s_57 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_57 : Nat := 0x4044404040444
def ep_57 : Nat := 0x400000000000440000000400004004000000040000404000404040000000000000000000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x2222222222222222
def s_58 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_58 : Nat := 0x2022200220222
def ep_58 : Nat := 0x20000000000220000002000002002000220020000202000000020000000000000000000000000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xa0a0a0a0a0a0a0a
def s_59 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_59 : Nat := 0x202020002020a
def ep_59 : Nat := 0x800000200000002080002000000020008000000000000000000020202000202000000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def nh_59 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 0 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) (nh_59 0) s_59 4 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 0 (dagTraceF m_59 s_59 4 f_59) cur_59 nh_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xc0c0c0c0c0c0c0c
def s_60 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_60 : Nat := 0x404040404040c
def ep_60 : Nat := 0x400000800000400000000080004000000000008000000000000000000000000000000000004040404040400
def bds_60 : List (Nat × List Nat × Nat × Nat) := []
def cc_60_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_60_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_60 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_60_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_60_0 p) (Nat.blt p 32)
def hc_60_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_60_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_60_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_60 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_60_2 (Nat.sub p 64)) (hc_60_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_60_0 p) (Nat.blt p 32)
def f_60 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 64 (dagTraceF m_60 s_60 5 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 64 bds_60 (dagTraceF m_60 s_60 5 f_60) (cur_60 0) (nh_60 0) s_60 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 32 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_1 : treeBlockF 32 64 ch_60 = true := by decide +kernel
theorem nj_60_1 : ∀ i, 0 ≤ i → i < 64 → ch_60 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_60_1 h1 h2)
theorem nc_60 : ∀ i, 0 ≤ i → i < 64 → ch_60 i = true := nj_60_1
theorem lb_60 : LowerBin m_60 s_60 g_60 6 :=
  lowerDagV5 (kn_nil) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0x55aa000055aa0000
def s_61 : List Nat := [0xaa000000aa0000, 0x1122000011220000, 0x50a0000050a0000, 0x55aa0000]
def g_61 : Nat := 0x102000005220000
def ep_61 : Nat := 0x420000000000000000000000000000000000000010200000500000001020000002200000000000000000000
def bds_61 : List (Nat × List Nat × Nat × Nat) := []
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_61 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_61 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 3 (dagTraceF m_61 s_61 4 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 3 bds_61 (dagTraceF m_61 s_61 4 f_61) (cur_61 0) (nh_61 0) s_61 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 3 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 3 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 5 :=
  lowerDagV5 (kn_nil) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0x50a050a050a050a
def s_62 : List Nat := [0xa000a000a000a, 0x102010201020102, 0x50a0000050a, 0x50a050a]
def g_62 : Nat := 0x10205020502050a
def ep_62 : Nat := 0x400000800000400000000080000000000000000000000000000000001020002000200000000000000000000
def bds_62 : List (Nat × List Nat × Nat × Nat) := []
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_62 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_62 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 10 (dagTraceF m_62 s_62 4 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 10 bds_62 (dagTraceF m_62 s_62 4 f_62) (cur_62 0) (nh_62 0) s_62 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 10 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 10 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 5 :=
  lowerDagV5 (kn_nil) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0x4488448844884488
def s_63 : List Nat := [0x88008800880088, 0x408040804080408, 0x448800004488, 0x44884488]
def g_63 : Nat := 0x40004000408
def ep_63 : Nat := 0x400000800000400000000080000000000000000000004000400040800000000000000000000000000000000
def bds_63 : List (Nat × List Nat × Nat × Nat) := []
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193030c1a3c20c0e3c24c263e88c9d3e54c903e10c800f 7 127 3 7 10 1023 14 16383
def nh_63 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_63 : Nat → Nat × Nat := unpackForestF 0xc7c63229f68f0a6443e51e24c086400f 3 10
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 10 (dagTraceF m_63 s_63 4 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 10 bds_63 (dagTraceF m_63 s_63 4 f_63) (cur_63 0) (nh_63 0) s_63 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 10 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 10 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 5 :=
  lowerDagV5 (kn_nil) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xaaaaaaaaaaaaaaaa
def s_64 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_64 : Nat := 0x202220022022a
def ep_64 : Nat := 0x20000800000220000002080002002000220028000202000000020800020222002202200000000000000000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 6, g_33), (m_59, s_59, 5, g_59), (m_51, s_51, 5, g_51), (m_42, s_42, 5, g_42), (m_34, s_34, 5, g_34), (m_25, s_25, 5, g_25), (m_58, s_58, 5, g_58), (m_15, s_15, 4, g_15), (m_8, s_8, 4, g_8)]
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x850609c9a42629c9148d29115e7686a50c499801f 6 63 2 3 11 2047 15 32767
def nh_64 : Nat → Nat := unpackHintV5 0xdf00ac66ac0070786791620b62003658006c0000 0x17aed578000231ad3d739e747001ac63d8c06355800d6033cb39d7471ec73b640635507bd68c01642a3c75e80000de31a80478f29c0021c7 16 65535 7 127
def f_64 : Nat → Nat × Nat := unpackForestF 0x41391686c5384a1945224a44578499801f 4 11
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 3 7 bds_64 9 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 3 7 9 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 9 ch_64 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 9 → ch_64 i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_cons lb_59 (kn_cons lb_51 (kn_cons lb_42 (kn_cons lb_34 (kn_cons lb_25 (kn_cons lb_58 (kn_cons lb_15 (kn_cons lb_8 (kn_nil)))))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0x5555555555555555
def s_65 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_65 : Nat := 0x115155505151555
def ep_65 : Nat := 0x400000000001440000010400014004000100040010404000504040001101000001010000000000000000000
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35)]
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def nh_65 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 0 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 0 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_35 (kn_nil)) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xff00ff00ff00ff00
def s_66 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_66 : Nat := 0x100170005001700
def ep_66 : Nat := 0x400000000001600000012000000000000000000010006000500060001001200000012000100140005001400
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 7, g_26)]
def cur_66 : Nat → List (Nat × Nat) := fun _ => []
def nh_66 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_66 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 1 1 0 bds_66 (dagTraceF m_66 s_66 7 f_66) (cur_66 0) (nh_66 0) s_66 7 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_66 g_66 ep_66 1 1 bds_66 0 (dagTraceF m_66 s_66 7 f_66) cur_66 nh_66 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_66 : LowerBin m_66 s_66 g_66 8 :=
  lowerDagV5 (kn_cons lb_26 (kn_nil)) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xf0f0f0f0f0f0f0f0
def s_67 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_67 : Nat := 0x10107000301070
def ep_67 : Nat := 0x20000000001060000010400010006000300060000000000000000000101020003010200010104000001040
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
def cur_67 : Nat → List (Nat × Nat) := fun _ => []
def nh_67 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_67 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 1 1 0 bds_67 (dagTraceF m_67 s_67 7 f_67) (cur_67 0) (nh_67 0) s_67 7 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_67 g_67 ep_67 1 1 bds_67 0 (dagTraceF m_67 s_67 7 f_67) cur_67 nh_67 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_67 : LowerBin m_67 s_67 g_67 8 :=
  lowerDagV5 (kn_cons lb_29 (kn_nil)) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0x3333333333333333
def s_68 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_68 : Nat := 0x113133301331333
def ep_68 : Nat := 0x20000000001220000012000012002000320020010202000100020000000000000000000110100001001000
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32)]
def cur_68 : Nat → List (Nat × Nat) := fun _ => []
def nh_68 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_68 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 1 1 0 bds_68 (dagTraceF m_68 s_68 7 f_68) (cur_68 0) (nh_68 0) s_68 7 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_68 g_68 ep_68 1 1 bds_68 0 (dagTraceF m_68 s_68 7 f_68) cur_68 nh_68 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_68 : LowerBin m_68 s_68 g_68 8 :=
  lowerDagV5 (kn_cons lb_32 (kn_nil)) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xcccccccccccccccc
def s_69 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_69 : Nat := 0x404440404044c
def ep_69 : Nat := 0x400000800000440000000480004004000000048000404000404040800000000000000000004044404040440
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_60, s_60, 6, g_60), (m_44, s_44, 5, g_44), (m_50, s_50, 5, g_50), (m_38, s_38, 5, g_38), (m_31, s_31, 5, g_31), (m_63, s_63, 5, g_63), (m_57, s_57, 5, g_57), (m_17, s_17, 4, g_17), (m_9, s_9, 4, g_9)]
def cur_69 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x113184a4e3264f9352394895e790d543148c01f 6 63 2 3 10 1023 14 16383
def nh_69 : Nat → Nat := unpackHintV5 0xdf00ac66ac0070786791620b62003658006c0000 0x15aec14015a31ac13cb39d74701bc63d80c6300558de033d739e7471ec73b640603557bd6008d426a3c7005e800de3001ac78e00129e1c7 16 65535 7 127
def f_69 : Nat → Nat × Nat := unpackForestF 0x2129190d93e150cb52294895e148c01f 4 10
def ch_69 : Nat → Bool := dagCheckNodeV5 m_69 g_69 ep_69 3 7 bds_69 9 (dagTraceF m_69 s_69 7 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 3 7 9 bds_69 (dagTraceF m_69 s_69 7 f_69) (cur_69 0) (nh_69 0) s_69 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69 : treeBlockF 0 9 ch_69 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 9 → ch_69 i = true := fun _ h1 h2 => treeBlockF_at nb_69 h1 h2
theorem lb_69 : LowerBin m_69 s_69 g_69 8 :=
  lowerDagV5 (kn_cons lb_60 (kn_cons lb_44 (kn_cons lb_50 (kn_cons lb_38 (kn_cons lb_31 (kn_cons lb_63 (kn_cons lb_57 (kn_cons lb_17 (kn_cons lb_9 (kn_nil)))))))))) rc_69 nc_69 (by decide +kernel)

def m_70 : Nat := 0xff00ff00ff00ff
def s_70 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_70 : Nat := 0x1700770037007f
def ep_70 : Nat := 0x20000800000060000000480000000000000000000600000004000800120022003200200014004400040040
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 6, g_33), (m_52, s_52, 5, g_52), (m_28, s_28, 5, g_28), (m_53, s_53, 5, g_53), (m_47, s_47, 5, g_47), (m_44, s_44, 5, g_44), (m_24, s_24, 5, g_24), (m_4, s_4, 4, g_4), (m_13, s_13, 4, g_13)]
def cur_70 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x214d3495a4d249934a391894678dd537149c01f 6 63 2 3 10 1023 14 16383
def nh_70 : Nat → Nat := unpackHintV5 0xdf00a378a300706670006a8b62113658006c0000 0x63058d6318f6bd185ce78f3a19c00146f182d5abb41e73c77d2776c3d8e005bd60350468d540f1ea9000058c600b51a8001e3c38f31d 16 65535 7 127
def f_70 : Nat → Nat × Nat := unpackForestF 0x214d18dda4d14dcb4a2918946149c01f 4 10
def ch_70 : Nat → Bool := dagCheckNodeV5 m_70 g_70 ep_70 3 7 bds_70 9 (dagTraceF m_70 s_70 7 f_70) cur_70 nh_70
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 m_70 g_70 ep_70 3 7 9 bds_70 (dagTraceF m_70 s_70 7 f_70) (cur_70 0) (nh_70 0) s_70 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70 : treeBlockF 0 9 ch_70 = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 9 → ch_70 i = true := fun _ h1 h2 => treeBlockF_at nb_70 h1 h2
theorem lb_70 : LowerBin m_70 s_70 g_70 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_cons lb_52 (kn_cons lb_28 (kn_cons lb_53 (kn_cons lb_47 (kn_cons lb_44 (kn_cons lb_24 (kn_cons lb_4 (kn_cons lb_13 (kn_nil)))))))))) rc_70 nc_70 (by decide +kernel)

def m_71 : Nat := 0xf0f0f0f0f0f0f0f
def s_71 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_71 : Nat := 0x10707070507070f
def ep_71 : Nat := 0x400000800000600000002080006000000020008000000000000000001020202000202000104040405040400
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_60, s_60, 6, g_60), (m_43, s_43, 5, g_43), (m_30, s_30, 5, g_30), (m_54, s_54, 5, g_54), (m_49, s_49, 5, g_49), (m_59, s_59, 5, g_59), (m_55, s_55, 5, g_55), (m_7, s_7, 4, g_7), (m_15, s_15, 4, g_15)]
def cur_71 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x215d3495a5d249935a3958956791d547149c01f 6 63 2 3 10 1023 14 16383
def nh_71 : Nat → Nat := unpackHintV5 0xdf00ac66ac00707870006791620b3658006c0000 0x140016ad5d80de36e73c79d02718c0017ab1ac631ec06f39e3be80671ec73b65bd60080d182a3540f1e9a005a802c6300469e3c000c7471e 16 65535 7 127
def f_71 : Nat → Nat × Nat := unpackForestF 0x215d191da5d151cb5a2958956149c01f 4 10
def ch_71 : Nat → Bool := dagCheckNodeV5 m_71 g_71 ep_71 3 7 bds_71 9 (dagTraceF m_71 s_71 7 f_71) cur_71 nh_71
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV5 m_71 g_71 ep_71 3 7 9 bds_71 (dagTraceF m_71 s_71 7 f_71) (cur_71 0) (nh_71 0) s_71 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71 : treeBlockF 0 9 ch_71 = true := by decide +kernel
theorem nc_71 : ∀ i, 0 ≤ i → i < 9 → ch_71 i = true := fun _ h1 h2 => treeBlockF_at nb_71 h1 h2
theorem lb_71 : LowerBin m_71 s_71 g_71 8 :=
  lowerDagV5 (kn_cons lb_60 (kn_cons lb_43 (kn_cons lb_30 (kn_cons lb_54 (kn_cons lb_49 (kn_cons lb_59 (kn_cons lb_55 (kn_cons lb_7 (kn_cons lb_15 (kn_nil)))))))))) rc_71 nc_71 (by decide +kernel)

def m_72 : Nat := 0xffffffff
def s_72 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_72 : Nat := 0x537177f
def ep_72 : Nat := 0x12480000000000320068000000000504060800000000003212200000000005041440
def bds_72 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 7, g_45)]
def cur_72 : Nat → List (Nat × Nat) := fun _ => []
def nh_72 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_72 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV5 m_72 g_72 ep_72 1 1 0 bds_72 (dagTraceF m_72 s_72 7 f_72) (cur_72 0) (nh_72 0) s_72 7 = true := by decide +kernel
theorem nc_72 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_72 g_72 ep_72 1 1 bds_72 0 (dagTraceF m_72 s_72 7 f_72) cur_72 nh_72 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_72 : LowerBin m_72 s_72 g_72 8 :=
  lowerDagV5 (kn_cons lb_45 (kn_nil)) rc_72 nc_72 (by decide +kernel)

def m_73 : Nat := 0xffff0000ffff0000
def s_73 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_73 : Nat := 0x117000005370000
def ep_73 : Nat := 0x420000000000000000000000016000000320000010600000504000001120000003200000114000005040000
def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 7, g_27)]
def cur_73 : Nat → List (Nat × Nat) := fun _ => []
def nh_73 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_73 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsV5 m_73 g_73 ep_73 1 1 0 bds_73 (dagTraceF m_73 s_73 7 f_73) (cur_73 0) (nh_73 0) s_73 7 = true := by decide +kernel
theorem nc_73 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_73 g_73 ep_73 1 1 bds_73 0 (dagTraceF m_73 s_73 7 f_73) cur_73 nh_73 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_73 : LowerBin m_73 s_73 g_73 8 :=
  lowerDagV5 (kn_cons lb_27 (kn_nil)) rc_73 nc_73 (by decide +kernel)

def m_74 : Nat := 0xffff0000ffff
def s_74 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_74 : Nat := 0x17770000177f
def ep_74 : Nat := 0x800000000000000000000006000000068000006000000060800001222000012200000144400001440
def bds_74 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 7, g_45)]
def cur_74 : Nat → List (Nat × Nat) := fun _ => []
def nh_74 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_74 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_74 : dagCheckRootsV5 m_74 g_74 ep_74 1 1 0 bds_74 (dagTraceF m_74 s_74 7 f_74) (cur_74 0) (nh_74 0) s_74 7 = true := by decide +kernel
theorem nc_74 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_74 g_74 ep_74 1 1 bds_74 0 (dagTraceF m_74 s_74 7 f_74) cur_74 nh_74 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_74 : LowerBin m_74 s_74 g_74 8 :=
  lowerDagV5 (kn_cons lb_45 (kn_nil)) rc_74 nc_74 (by decide +kernel)

def g_75 : Nat := 0x11717770537177f
def ep_75 : Nat := 0x420000800001660000012480016006000320068010606000504060801121222003212200114144405041440
def bds_75 : List (Nat × List Nat × Nat × Nat) := [(m_73, s_73, 8, g_73), (m_70, s_70, 8, g_70), (m_71, s_71, 8, g_71), (m_74, s_74, 8, g_74), (m_68, s_68, 8, g_68), (m_66, s_66, 8, g_66), (m_29, s_29, 7, g_29), (m_65, s_65, 8, g_65), (m_67, s_67, 8, g_67), (m_69, s_69, 8, g_69), (m_72, s_72, 8, g_72), (m_64, s_64, 8, g_64), (m_32, s_32, 7, g_32), (m_35, s_35, 7, g_35), (m_27, s_27, 7, g_27), (m_45, s_45, 7, g_45), (m_15, s_15, 4, g_15), (m_33, s_33, 6, g_33), (m_60, s_60, 6, g_60), (m_41, s_41, 5, g_41), (m_43, s_43, 5, g_43), (m_54, s_54, 5, g_54), (m_57, s_57, 5, g_57), (m_26, s_26, 7, g_26), (m_39, s_39, 5, g_39), (m_44, s_44, 5, g_44), (m_52, s_52, 5, g_52), (m_58, s_58, 5, g_58), (m_21, s_21, 5, g_21), (m_40, s_40, 5, g_40), (m_22, s_22, 5, g_22), (m_37, s_37, 5, g_37), (m_61, s_61, 5, g_61), (m_23, s_23, 5, g_23), (m_24, s_24, 5, g_24), (m_55, s_55, 5, g_55), (m_63, s_63, 5, g_63), (m_53, s_53, 5, g_53), (m_36, s_36, 5, g_36), (m_48, s_48, 5, g_48), (m_46, s_46, 5, g_46), (m_62, s_62, 5, g_62), (m_25, s_25, 5, g_25), (m_56, s_56, 5, g_56)]
def cc_75_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa80d402983403a0050027833c09e04e067013419a04c066012c19604a0650124186343021810c086043021810c07a33d000f8001 0xfa640752a04158c1e8de0e45f0662f82c550142c809154040b201c5500c2b80ad6304e3782317c0f6de06b5f02da381158c078de0345f015b7808d7c0368f48c5fa422dd1f15e8c8a744b5fa21add0ed5e866a742b4fa11a5d02d1e7e6873a25f9b52dcb295e454a71fa4f8d525c4e91e194870a23f83d1dc048ddf1466f095f724adb4e55d882a6bc14f580a5a7c51d1f2868393f3b49d9a64dcb12664c92f1fc958ca49c432462085f1002d87215c380a61b04f0d42585c11c2d0861303f0941d8460dc220660d82f0681583009c170460501f0240d80405c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_75_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa3426cc92fde3c72e1c3568c582d468101d3864c1516204050810080 0x1fc7cf63e771c3e69fe24fe91bee9bf4ad19568c23066dbf14df7a37b1aa54d9286a95d63a537ce97e44df0a54 7 127 2 3 11 2047 17 131071
def cc_75_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x88211806007c5f0785e0745c16c5a164590605714d121481114411040500400e23441c0400100000 0xbcd2ee954b6592c944ae5f2a368a2d52a46ca0d428b5ca1192ab5fa6d6e93579ed4e714498552496c8edbe33678a5131d6fc35aefd67b958ed46fb11aeb4679b18e5c5f9516e44578914e134f 10 1023 4 15 11 2047 18 262143
def cc_75_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xf8787a3c1d8e874191c0d12633090c82410278bc1c2e07034582c0588e06021100442001 0x3f358f6963c244f6d73ba40f0933bb54f893fd24bf291fb243eadc39b48e296f8257dedc36b58d49af4b60ced23ed6be959f946bdd19f645fd716f4457cd14f2164c4553017c 9 511 4 15 11 2047 18 262143
def cc_75_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2f0b86e0b461c841f27c1d2741b26c19264172585605094048920481204812048120481202a00a 0x13a9b26d2257d6fadad75759ea6b1d3c6fa58d74719e8631cfc5f9e8b73915e6a29cc154880292c5f21c0a4a14486029245f2140a48154840290605234b6410148b28902052222dc3c57866b70ad5e11a7c1b4b8268f02d0e5eb5cad67938d72319e3e2fc745b8c8af1514e240c40014 10 1023 4 15 11 2047 19 524287
def cc_75_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x88211842017c5e1745c1701b1685645449c24081200711c0611805114041100310c0210801104001 0x2f89a5e16cb94f16c992e5be5aa60b64d96add2e937dc26bb74cf6898ecc9a68d6fcfad79b59f2ab1e436fc76d78ad9f05b1dfb5fbd6b776d5ec9a9d8264ae4a9589f2a92a54264a6489489f2892250254 10 1023 4 15 11 2047 19 524287
def cc_75_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xd06470380b8dc2c360b050a62b858285409148205007130980a250281048040110442001 0x379adeec70db4b9b29735db5eb367d58c1d75bf8ab3f026fdf4d7b899f6931ec25bd44afa459340aa6717ccc4979655324b26317cc44bf8695f089a60154 9 511 4 15 11 2047 19 524287
def cc_75_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a508ca3084a107c9f07c1f07c1f07c1f07c1f05e0da340c12c4a12448120071184240441000400 0x7f97c790147e934788147d934780147c96c778147b45f7ac577a25f79a5b7925778a537824b77a4782d6f81d6780b6f8036b7f3677e3637d35b7c3577b818770147646874a487323474b4c72a307323c72b447523f7423b73a377223371c7070c68 10 1023 4 15 11 2047 20 1048575
def cc_75_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xf0747a1c1e06c761a1d06472190c0e02e370b0d82a350a0d02627c38148a032180480200 0x8f3648e3548d37c8c3548b36489b7c88a4487b5486a4485b6c84a448ed6f8dd6b8cd678bd638aa6f8a26b89267882638725f8625b8525784253831647b0148217c7a814811647a01479814 9 511 4 15 11 2047 20 1048575
def cc_75_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9b26090a408c612841f2785e0709c0701a260980589605814248920481204812048120481202a00a 0xaf36fae36ba9b67a8b63a7a6fa726ba5267a4263a323fa223ba0a379fa339e944940149da3b9d144938149c16493014928149a97c9201499a4f990269893491814979449101496a6f9626795934908149435b93b539325f92a5b9225791a539123f90a339e46b9cc639bb6f9b36b9a367983639734f953439481890014 10 1023 4 15 11 2047 20 1048575
def cc_75_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xb9b8b1a9a199919089816459585150494848483a313029282120191811090801 0xafd68aeb6cad258aba44ad35cab240aba4cab354ada4faca4bac247aaa43aa570a936ca8568a6b4fa6343a5d70a4a6ca3b6ca2a6ca1b6ba1460a026c 8 255 3 7 11 2047 20 1048575
def cc_75_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x8821184201801f15e1705856054550505404c530485204811144101400f13c0e1380d1340c103000 0xbf254be354bd254c336bc2363c126fc0a6bbfa67bea63bda3fbca33bb964ba944b997cb8944b7964b617cb5134b4144b3134b215cb1134bb46fba46bb9467b8463b736fb6b6bb5b67b4b63b3b4fb2b4bb1b47b0b43 10 1023 4 15 11 2047 20 1048575
def cc_75_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x84a107c9f0785c2701a2681a06096258160581605816058160580e8128400c430084200441004001 0xcf944c7014ce934c6814cda4fcd134c6014cc134c5814cb25fcaa57ca134c5014c8b4fc834bc7b47c7343c6a4bc6243c5a3bc5233d2c5fd245bd1457cf453ce35bccb53cbb4bc9b43c9018c4814c3b54c2b54c1c64c047c 10 1023 4 15 11 2047 20 1048575
def cc_75_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x946509063188611806007c5e16919164181601715c16158151505404c47c1c052104400882008002 0xdfc7cdea7cdd358dbb44dd45cdb340dbb4cdb454ddb4fdcb4bdc347dab43da570d927cd837cd727cd635bd5c70d4a7ce3b4fe334be1347e0343df24fde24bd9a47d8a43d7a3fd6a3bd5237d4233d3154c8814c8014d196cc7814d0a3bd0036 10 1023 4 15 11 2047 20 1048575
def cc_75_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xd86c343a0c8e430380b8dc2c360a8d42834098cc2432088970a041201008022088400200 0xee96ced944ec954eb934ea96ce9934e8944e7934e695ce5934efc5fef45bee457ed453ec35feb35bea357e9353e834fe734be6347e5343e447ce2a4fe2243e1d70e0b7c 9 511 4 15 11 2047 20 1048575
def cc_75_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4690a067198651906408c621791e07090c400f13c0f0384e0344d0304c02c4b0284a02441804001 0x1ff4a8fea7c7e8ac3ee511fa4b8fb1407dca63ec951fb29efc94b7e0a3bea50df44a8f9854802b7bfd5adfcacef9563788b7b945ada82cec99635e4afac256d3f2ae951537c2323db5a1eb6c8f4a6479d323ca991e34c8f7b4f7b9a5bd8d1dea686f424b79921bc88ede2466f0154 10 1023 4 15 11 2047 21 2097151
def cc_75_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xf07c0e8b64d46d8b42c1b02b18e23088620845986057158551541414c4f4348d0304c006c1000400 0x10f93c8792243a0522427f1113b8809bc384ce1b48912c6b86a31bcc5bdd22d6d8967664b1a1053cb22870c354859be42f5ae15acee816b6bcb3af657d672b6a31574b8a9c26992114f90956f842b3bc85bdce2d6d696765cb1aca56d442af069488289a41a932092610513c8252241c4fe0c2770593782099c0f1c20509902c5781ab3b985adaa2ceb195b504ab87419c2f0af0204c80c2001607c0302f00a64 10 1023 4 15 11 2047 21 2097151
def cc_75_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42d0acab0a86a0a4690a05cc701b16c1926058058951541414c4f43846818051104310842000800 0x11f2648f432476912394f91ba448f237c751ae388cf1b4637a0b7bac5adbc2cece163430a79f452cd828e5e9438d1b646056232089161448c12e45e0522b2811614c8ad2a46253e2e297169478a8a1c535c2336d714367750b5b6659d0a27e7c13b3509b9764ce264891194887c9a4469321e2611084c 10 1023 4 15 11 2047 21 2097151
def cc_75_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x801002003c4780bb9702c2562ac1582834e29c1382614668c101a00400801002003883b8700c21803005880b 0x97d1fcbc8ee5d46f2e2339ada7cd4d2e6368f303435fca7ad652d4a28e9a1434489f9fc4ecdc26e6293396c364b4182584a925024924124aa9b2540d924024940224a00a6522772893793c1b49c9124d08923824929a7c92d2e4868f23b4395e2fcad16e538af264535f4afad256d482ae98153440a79f852cda28e6094392c1448c092446a9208549052dc86dadd82d6df1674389f97e4cc3c0cf210489002204e0fc0d03e02017 11 2047 4 15 11 2047 21 2097151
def cc_75_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x66e6606416406406406026006005c23923803803803613603411cc1c01821611601411401210c30c0063060060003000 0x13aa6f9b935cc099e4c4c6f516f768b5b8059d9e2c64d12f228958cc49c44247400389fc1a4fb1927aad13c85c9ddb24ec0d27c69f3db4b9e1a3cead0d8229eb714b53ca3a6e50d1527e8093b3809b9904cc3709e188470a41f8480dc0f03e028179c4364de112738bf3945b9c22bcdd14d812beb695b538aba6c54d1429e8014b37ca398e50e6c8f92f87c9783e4ce172670833494f9a0a1ccc13a65ae12e87c9902e4c4df25c0f930834 12 4095 5 31 11 2047 21 2097151
def cc_75_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x3e21d10d0c6803385716b805b0a82d11878834411485982441200238100004 0x84a3b802334753f4153b3ad37345332bd2f18d2385e3f7fa3346d3f33d332b52f25d2b1f527185238563f8423b81a377f2334653f40d3b38937335332ad2f2552b1d12717d237cd237ca3345d3f329332a52f17123a3848a34440ac3f0802f0541f020178f53b8f24b5d94b5794729d2f16923a2c58a28540cc470782f04c1f01c1790e5f8ea5b8ce57896536195f5d15b571574f1532952f24d2b1c927161238e24b8a2475c94b54d4728d2f2452b1b927159238da5b86a536115f5c15b545574e5532852f135239f26f9ce6b9ae6795e637bd6f77d6b71d676956327d2f23d2b1b12712d231086f0f8670702f064270441f018179ee6f9ca6b9aa6795a637b96f7796b71967691632792f2392b1ad27129239e55f9c55b99157951539e26f9c26b98e6794e637b16f7716b70967689632712f2312b1a12712123a0c5ca08509d95f9bd5b9855793553 13 8191 5 31 10 1023 20 1048575
def cur_75 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_75_20 (Nat.sub p 640)) (cc_75_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_75_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (Bool.rec (cc_75_17 (Nat.sub p 544)) (cc_75_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_75_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (cc_75_14 (Nat.sub p 448)) (cc_75_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_75_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (cc_75_11 (Nat.sub p 352)) (cc_75_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_75_9 (Nat.sub p 288)) (cc_75_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_75_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_75_6 (Nat.sub p 192)) (cc_75_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_75_4 (Nat.sub p 128)) (cc_75_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_75_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_75_1 (Nat.sub p 32)) (cc_75_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def hc_75_0 : Nat → Nat := unpackHintV5 0x9214cc236c2328750cc20612e67d80809e3d24675007e9bc12fe6a289b98e534a5fcc7916d224257987614cf22e4f8c7612cc22e47687910b92423fac670ee620a3814708c862fe289d2f888b3381bbcce05533380edcce02602ae03e4b380001f20000000000000 0x20f88c4c4c8ea1b81ea0fa9eaaaaa42d0b582d690b42d982c8c2c2c2c4c2c2eaa82c2e82ea82c6c2c1c2c1c2c2eaaa82c2c2c8c4c4c8ea20383327272faa0b50b0b030b02c0c2c0f1f0f0f0f0faa0f0fa0f1fa0f0f0f0f1f0faaa50fa750b0b543c3c3c3c7c3c1c6c1c6cdc8cac4cac4cdc8c3c3c1c1c1c1c2c2eaaaaaaa90b42d0742d42c2d6998ccacacbc6c1c1c6ccc0cbc33032f2a82d42c3c3c3c3c3c1c1c3e696aaa50b0f0f0f0f1f0f071b071b88ea13a83eaa81ea7aaa90b42d0742d60b5a660b230b0b0b130b0b0b1b070707070b0baaa0b0ba0baaaaaa0b0b0b332b2b2f1b07071ba880e2a82d42c2c0c2c0b030b03c7c3c3c3c3c3c1c1c1c1c3ea83c3e83c7eaaa943e9d42c2d50f0f0f0f1f0f272b270f2b0f0f270f42d0b42d0b42d0b0b230b0b0b130b0b0b1b0b070b070b0b0b0f0b82e0b0b0b0b0b332b2b2f3327272f0f2f330f0b50b0b030b02c0c2c1f1f0f1f0f531f0f531f1f0f0f1f0f0f0f5350fa750b0b547c3ccc7c7c3c9c9c9c9c3c3c3c3c3c3c3c3d555554acacacac9c9c9c9c3c3c3c3d543c3c3c3cac3c3c3c3c3c3c3c3c3d43e9d543c3c3c3d23544d51b541d50f565551503442d071b071b88ea13a83eaa81ea7aaa9513548d507546d5595355665656555555555554ccacacbc6c1c1c6ea2038aa40d151543c3c3c3c7c3c3c1c1c3ea0f83eaa942d5543e9c3c3c3c3c9cac9cecec3cac3c3c9c3d513548d507546d5950f55555554ccacacbccc9c9cbc3cbccc3d03454551f0f531f1f0f1f0f1f0f0f0f0f0f50b5550fa71f0f1f0f272727270f0f0f0f0f0f0f0f42d0b42d0b42d0b2b2b2b2b272727270f0f0f0f0b50b0f2b0f0f0f0f0f0f0f0f270f0f0f0f0f0f0f0b0b550fa70f0f0f0f2f0f0b230b0b0b130b0b0b1b0b070b070b0b0b0f0b82e0b0b0b0b0b0b02c0c2c0c2c541c4c1c07070001313000230f130f1b07070f3783c3cde0f0f231313231b07071b374dc2cdd370b0f37370f0000000000001f0f130f1b07070f1b030f1b0f0f0303030f0f0f0f0f0f1f0f1f0f00007071313071307a7070707131313230f130f1b07070f1b83c3c6e0f0f231313231b07071b1b46c2c6d1b0b0f37370f00000000000008c013006c007006c1b0006c0003c0800b010007c3c4c3c6c1c1c3c6c6c3c6c3c3c6c6c7c7c3c3c3c3c3c3c7c3c7c3c03e9c0000c3c3c0008c4c4c8c9c1cdc6c9c1cdc6ca80282a88c4c4c8cdd370b374dc2cec9c9cfea80000000000003c3c3c3eaa80c0c0e83c3c3c3ea83c3c3c3c0020f88c4c4c8ea1b81ea0fa9eaaaaa23131323982e68ec9c9cfea800000000000023004c0880080006c0070202002c04000f0f0f0faa0f0fa0f1fa0f0f0f0faa0f0f0f0f00fa700003071b071b37232b132b1337230f0f000aa2a00a0372b2b371b07071b374dc2cdd370baa0000000000000f0f0f0f0f07070faa0303aaa0f0f0f0f000071b071b88ea13a83eaa81ea7aaa8dcacacdc6c1c1c6e60b9aaa00000000000008c013006c00702200200080800b010003c3c3c3c3c1c1c3ea0f83eaa83c3c3c3c03e9c0000c2c2c0008c4c4c8c9c1cdc6c9c1cdc6c8c3c4c3cde0f0f3783c3cdc3c9c3c54014155540000000000007c3c4c3d540c0d47c3c7c3c3c3c3c3d540010b48c4c4c8d51b41d48c3c4c3d50f65370f270f44da75555555400000000000023004c0440040006c007003c080404001f0f130f543d1f51f0f1f0f0f0f0f0f5500fa700003071b071b3b232b132b133b230b0b0003b0f2b0f1b07070f3f83c3cfe0f0f55150050550000000000001f0f1f0f1b07070f55503030350f0f0f0f55000071b071b48d513542d3b0f2b0f1b07070f543d95550769d5555500000000000008c013006c0070110010000f0201010007c3c7c3c6c1c1c3d543c3d47c7d43c3c3c3d5403e9c0000c9cac9cdcdc8cac4cac4cdc8cdc6c9c1c9c1cdc6eaaaa800155554001440000000000003c3c3c3c3c3c3c3c0c0c0d5556a9540009cac9cdd513548d507546eaaa96555555559a700000000000008c013006c00701000440080f0220102c044000f0f0f0f0f0f0f0f50f1f5550f0faa5500fa700003272b270f2b0f0f270f2b2b532727530f530f0000000008c013006c007003c0800b010007c3c7c3c7c3c7c3c3c3c3c3c7c3c7c3c03e9c0000c9c9c9c9c3c3c3c3c3c3c3c3cacacacac9c9c9c9c3c3c3c3c0c0300c0300c0300c0303c3c3c3cac3c3c3c3c3c9c3c3c3c3c3c3c3c3ccc3c3c3c3c03e9c0c0c00c8c0c0c0c4c0c0c0c6c0c0c0c1c0c0c0c3c0e0380c0c0c2c0d0340c0c0c0c0c007071313071307a7070707131313230f130f1b07070f1b83c3c6e0f0f231313231b07071b1b46c2c6d1b0b0f37370f0303031303030323030303070303031b03030303031b032f03030303031b031b03030380e030f03030340d030b0300c0300c03030030300300c0300c0303031f0f1313130f1b070707070f1b1b0f1b0f0f1b1b1f1f0f0f0f1f0f0f0f271f1f0f1f0f270000c0c03e9e0f88c4c4c8ea1b81ea0fa9eaaaaa23131323982e68ec9c9cfea80c0c0c4c0c0c0c8eaa80cbe80c0ea80c0c0c1c0c0c0c6eaaa80c0c0d0340c2c0c032820300300c880300c0303030f0f0f0f130faa0f0fa0f1fa0f0f0f0f1f0faaa0f1f0f0f0f0f0000c0c03e9c1c6c1c6e23a84ea0faaa07a9eaaa372b2b371b07071b982e6aa80c0c0c4c0c0c0c8c0c0c0c1c0c0c0c6eaa80cbe80c0eaaaaa80c0c0d0340c2c0c0300c03282030880300c0303030f0f0f0f1f0f0f070707070faa0f0fa0f1faaaa0f1f0f0f0f0f0000c0c03e9d0b48c4c4c8d51b41d48c3c4c3d50f65370f270f44da7555555540c0c0c4c0c0c0c8d5540cbd40c0d540c0c0c1c0c0c0c6c0c0c0e0380c3d55540c031410300300c0300c440303031f0f1313130f550f0f51f1f51f0f2b1f1f0f0f1f0f0f0f2b5550000c0c03e9c1c6c1c6d23544d50b4ec3cac3c6c1c1c3d50f655541da75555540c0c0c4c0c0c0c8c0c0c0c1c0c0c0c6d5540cbd40c0d540c0c0e0380c3d55540c0300c031410300300c440303031f0f271f1f0f1b070707070f550f0f51f1f50f1f0f0f0f275550000c0c03e9c9cac9cdd513548d507546eaaa96555555559a70303031303030323030303070303031b5030355555032faaaa55550300c0300c40c14221100c0c0c3c3c3c3c7c3c3c3c3c3c7c3d43c7d5543c3eaa955400030300fa7272b270f2b0f0f270f2b2b532727530f530f0303031303030323030303070303031b03030380e030f03030340d030b0300c0300c0300c0300c0303031f0f2f1f1f0f1f0f2f1f1f0f0f1f0f0f0f2f1f1f0f1f0f2f0000c0c03e9c9c9c9c9c3c3c3c3c3c3c3c3cacacacac9c9c9c9c3c3c3c3c000000003c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c0003e9c23004c01b001c00f02002c040000c 26 67108863 11 2047
def hc_75_1 : Nat → Nat := unpackHintV5 0xb754e1ac842a2ab04e1a9b8212a128b726b03349488c7238134287dcc5205134c7c00a89d3d3867030989a4938665008497d22dc58e0cd14aa31c4c38ce10b34b63e688c8e023303348980b3a330271cb988c62021e8c9186a61fa149cbf838b33804c12d8000260 0xf0f0f070713130707131b0713071384eaa84e13aa84ea13a83eaaaa83e0faa81ea7aaa84d130b1344c2c4c4c4c4c6c1c1c6e60b9aaa13031304c0c4c131313131b07071ba880e2a8ccbcccbc3c4c3c3c4c3c3c3c3c3e9c3c1c1c1c1c3ea83c3e83c7eaaa83c3c3c3c7c3c3c3c3c3c7c3d43c3d541c4c1c4c1c1c4c2c1c1c2c2c4c3c4c3cfe0f0f3f83c3c6c1c1c3d55555555544c4c4c4ccc0cbc33032f06c1c1c6c3cbccc3d544c4c3d0f131f1f1f55551b070707070f0f1f0f0f0f275551f0f271f1f0f0f0f0f070713130707131b0713071344d5544d135544d513542d1383c3c4e0f0f130f130f1b07070f543d9555551342d550769d5555513031304c0c4c131313131b07071b5440d03cbccc3d544c4c7c4c4c3c3c3c4c3e9c6c1c1c1c1c3d543c3d47c7d43c7c3c3c3c9d5547c3c9c7c7c3c4c4c4c4eaaa943c3d54dc6c9c1c9c1cdc6eaaa955555555544c4c4c4ccc9c9cbea8cc0cbc33032f1543c4c3d0f0f0f0f0f0f1f0faaa0f1f0f55555550f0f0f0f1f0f0f0f0f130713131307131b131313135544d135544d544d513541d51baaaaaaaa5955555555555669c4c0c4c13031304c4c4c4ccc9c9cbd03454aa550f130f0f130f0f0f0f0fa70f0f0f0f1f0f50f1f5550f0faaa5550f0f0f0f1f0f0f0f0f130713131307131b131313131383c3c4e0f0f130f130f0f270f1344c2c4d130b131313132727530f530f13031304c0c4c131313133327272f0f2f330f332f332f13131f13130f0f0f130fa71f0f2b1f1f0f0f1f0f0f0f2b1f0f2b1f1f0f1f0f2b1f1f0f231313230f0f0f0f0f0f0f0f23131323272727270f0f0f0f23131323272727270f0f0f0f2f2f2f2f0f0f0f0f0f130fa70f0f0f0f0f0f0f0f0f530f0f0f0f0f0f0f0f0f1f0f0f1b0f070f070f0f0f0f0f83e0f0f0f0b0f43d0f0b0f03c0c3c0c3c0f0f0f42d0713071b546d0751b23131313131b1b5551b1b51b27550f0f0f230f130f543d946c1c1c3c6e0f0f1b83c3d1369d55555555555231313235440d06c1c1c6c6c0c6c1b031b03cbccc3d547c3c4c3d50f47d41c1c3e9c1c1c3c3c1c1c1c3c7c3c3c3c9d547c3c7c3c1c6c1c6c6c8c6c4c6c4c6c6c3c3c3cfc3cac3c6c1c1c3c6e0f0f1b83c3cacad4c6c1c1c6c6d1b0b1b46c2c3cfcfc3cccacacbc6c1c1c6c6c0c6c1b031b03cbccc3cccbcccbc7c3c7c3c1c1c3e9c1c1c3c3c1c1c1c3c7c3c3c3c9c7c3c7c3c7c3c7c3c1c1c1c1c3c3c3c3c1c1c1c1cacacacac1c1c1c1c3c3c3c3cacacacac1c1c1c1c3c3c3c3cbcbcbcbc3c3c3c3cac3c1c1c3e9c1c1c1c1c3c3c3c3c3c3c3d4c3c3c3c3c3c3c3c3cbc3c1c8c1c1c1c4c1c1c1c1c1c1c3c1e0781c1c1c2c1d0741c1c1c070307030701c3c1c1c1c1c1c1c1c1c1c1c1c3c3e81c1eaaaaaaaaa88c4c4c8c1c1c1c1cdd370b374dc2ea88c4c4c8c1c1c1c1ccc0cbc33032f2a8ccbcccbc3c3c3c3c4c3c1c1c1e07070f1b0faaaaaaa0f1f0f0f0f0f0f0f0f0f1f0f83e0707071307070723aaa07a0707aa07070707a81e07a07070783ea7aaaaaaaa0783ea88c4c4c8e60b9a0741c1c1d070b07070707aa23131323a880e01c0c1c07030701c1c1c1ea8ccbcccbc3c3c3c3c4c3ea83c3e83c7e81c1c3c1c1c1c1c1c1c3e9eaa83c7c3c3c3c3c3c3c3c3c7c3c1c1c1c1c1c1c1c1c1c1c2c2d41c1d548c3c4c3c1c1c1c1cde0f0f3783c3d55555555548c4c4c8c1c1c1c1ccc0cbc33032f03cbccc3d547c3c4c3c1c1d071b1b5550f0f0f0f551f0f271f1f0f42d070707130707072355507507075507070707541d075070707230f130f543d941e07070781c3c1c1c1c1d1369d555555541d0b5555231313235440d01c0c1c07030701c1c1c1c3cbccc3d547c3c4c4c4c3d543c3d47c7d41c1c6c1c1c1c1c1c1c3e9c3c3c9c3c7c3d5547c3c9c7c7c3c1c1c1c1eaaa8dc8cac4cac4cdc8d41c1d56aaa95555555554ccacacbc1c1c1c1ea8cc0cbc33032f1543c3c3c3c7c3c1c1c1d0707aaa0f1b0f55555550f0f0f0f1f0f070707130707072307070707070707544d5235541d075541d541d507aaaaaaaa5955555555555669cccacacbc1c0c1c07030701c1c1c1d03454aa550f0f0f0f1f0f07070f0707070707070fa750f1f5550f0faaa5550f0f0f0f1f0f0707071307070723070707070707070f2b0f0781c1c1e070f070707072b2b530741c1c1d070b070707070f530f332b2b2f07030701c0c1c070707070f2f330f332f332f1f0f271f1f0f07071b0707070707070fa70f0f270f1f0f1f1f0f1f0f271f0f271f1f0f071b071b0f0f0f0f0f07070f2b2b2b2b1b07071b0f0f0f0f2b2b2b2b1b07071b0f0f0f0f2f2f2f2f0f0f0f0f0f0f070707070fa70f0f0f0f0f0f0f0f0f0f0f0f0f0f0f230f0f0f130f0f0f1b0f0f0f0f83e0f0f0f0b0f43d0f0b0f03c0c3c0c3c0707070713070f07070f0f0f0f0f071313070707070f0f83e0f81e0fa0f0fa0f0f231313231b07071b374dc2cdd370b0fa0f231313231b07071b33032f0cc0cbc0fa0f332f332f0f0f0f0f130f0f1b07070f0f0f83c3c3c3ea0f0f0faa0f0f1f0f0f0f0f0f0f0f0f1f0f07071313071307a707070713131383e0f81e0fa0f0fa0f0f0f230f0f0f130f0f0f1b070707070f0f0f1b0f1b0f0f0f0f0f1b0f0f0f0f0f0f0f0f231313231b07071b1b46c2c6d1b0b0fa0f0f43c2c3d0f0b231313231b07071b1b031b06c0c6c0fa0f0f030f03c0c3c332f332f0f0f0f0f130f0f1b07070f0f0f0f0f0f0f0f0f1b0f1f0f0fa0fa7a0f0fa83c7c3c3c3c3c3c3c3c3c7c3c3c3c2c2c3c3c3c2c9c1cdc6c9c1cdc6c8c4c4c8d43c3d560f83e0f83d5555555554cc0cbc33032f08c4c4c8ccc9c9cbc3e83d5556943c3c3c3c3c3c3c3da0f550f0f0f0f1f0f42d23131323546d07583e0f543d960f83c3c8c3c3c3c4c3c3d5543c3d43d543c6c3c1c3c1c3c3c3c3c3d1369d55555555555231313235440d0cc9c9cbc3e83c3c0c3c0f030f1543c3c3c3c4c3d543c3d43c7d43c7c3c3c3c3e83e9e83c3ea5550f0f0f0f1f0f3b232b132b133b23071b071b07070b0b07070f0b83e0f50f0f5581e0f5555555555332b2b2f33032f0cc0cbc1b07071b0fa0f550f0f0f0f1f0f555a943c6c1c1c3c3daa0f5550f0f0f0f1f0f071b071b48d513542d83e0f81e0f543d943c8c3c3c3c4c3c3c3c6c1c1c1c1c3c3d5543c3d43d543c3c3d550769d555555555332b2b2f1b07071b5440d03e83c3c0c3c0f030f1543c3c3c3c7c3c3c6c1c1c3c3d543c3d43c7d683e9e83c3ea5550f0f0f0f1f0f272b2783e0f83e0f0f230f0f0f130f0f0f1b0f070f070f0f0f0f0f2b2b532727530fa0f0f43c2c3d0f0b332b2b2f3327272f0fa0f0f030f03c0c3c332f332f0f0f0f0f1f0f0f1f0f0f0f0fa0fa7a0f0fa83c7c3c3c3c3c3c3c3c3c7c3c9c9c9c9eaaa8acacacac9c9c9c9ea8acacacac9c9c9c9ea8bcbcbcbc3c3c3c3c3c3c3c3c9c3e83e9ea83c3c3c3c3c3c3c3e23a84ea1ba81eaa82e66a2a03883e42d23131323546d075a83ea0f55583d6956a07a83ea95996aaa44da75555555555548c4c4c8d510343327272f80e2a2a9543c3c3c3d50f43d43c3c3c3c7c3e83eaa83e9d543c3c3c3c9cac9cfea0fa83ea07a83eaaaaa2b2b533f27273f9a982ea8ccacacbccc9c9cbe038a8aa332f332f0f0f0f0f0f0f0f0f1f0fa0faaa0fa70f0f0f0f0f0f0f0f2727272783e0f83e0f2b2b2b2b272727270fa0f2b2b2b2b272727270fa0f2f2f2f2f0f0f0f0f2b0f0f270f0f0f0f0f0faa0fa70f530f0f0f0f0f0f0f0f2f0f0f230f0f0f130f0f0f1b0f070f070f0f0f0f0f0f0b0f43d0f0b0f03c0c3c0c3ca81c4c1c2c1c1c2c2c2c2c2c1c4c4c1c1c1c1c2c2c8c3c4c3c6c1c1c3cde0f0f3783c3d0b42d0742d42c2d42c2d0b42c8c4c4c8c6c1c1c6ccc0cbc33032f03cbccc3c2d42c7c7c3c4c3c8c6c1c1c1c1c3c6d0f1b0f0f543c3c3c7c3c3c3c9c2d542c7c3c9c7c7c3c1c1c4c4c1c4c1e9c1c1c1c4c4c4c8c3c4c3c6c1c1c3c6e0f0f1b83c3d0b42d0742d42c2d42c2d0b42c2c8c2c2c2c4c2c2c2c6c1c1c1c1c2c2c2c6c2c6c2c2c2c2c2c6c2c2c2c2c2c2c3c2e0b82c2c2c2c2c8c4c4c8c6c1c1c6c6c0c6c1b031b03cbccc3c2d42c2c0c2c0b030b07c7c3c4c3c8c6c1c1c1c1c3c6c6c3c6c3c3c6c6c7c7c3c3c3c7c3c3c3c9d43e9d42c2d51f0f271f1f0f0f0f0b0b0b0b0b0b231313232707371b2707371baaaaaaaa42d0b50b0b5a42d0b662313132333032f0cc0cbc3327272faa0b50b0f1f0f0f0f0f9aa5683c3c3c3c7c3eaaa550b0f0f0f0f1f0f 26 67108863 11 2047
def hc_75_2 : Nat → Nat := unpackHintV5 0xd1c022c8aa46bc730eb559c6ace21ea531ec9a32c09341bc8aaa268a48188a280889c8188888508868088848088708507f59ec7492b26d79c665520a5a32c85341bc4a224849a02048d03440e1fc359ad2301162230b4216bb14098b4c000262 0x29cfc3ea707071313071307a701c1c0004c4c0008c4c4c8c6c1c1c6cfe0f3fa3c3d0b42d0742d40c0d42c0d0b42c0000000000004a708c4c4c8c6c1c1c6cbc7c9c3cbc7c9c3cbc9cbc9c2d42c001c1c4c4c1c4c1e9c1c1c1c4c4c4c8c4c4c8c6c1c1c6c6e1b0f1b86c3d0b42d0742d42c2d42c2d0b42c0000000000004a708c013006c007006c1b0006c0003c0800300231313231b07071b1b1b1b1b0f2f1b1b1f331b0f2f272f270b50b00003c1f00f0f0002313132347073f1b47073f1b213a80282a90b42d40c0d690b42d980000000000008c3c4c3cbc7c3c3cbc7c3c3cbc3cbc3ea82d42c020f88c4c4c8ea1b81ea13a9eaaaaa42d0b582d690b42d980000000000004a708c0130220020001b001c080800300230f130faa0f2fa1f33a2f0f2f0faa0b50b00003c1f013131313883e0f83c0280dc6cdc1cdc1cdc6c3c3c0010b42d0b42d90b5030350b030000000000000f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f0b50b001313131384ea7a0f0f83e0fa83c6c3c1c3c1c3c3c3c3c3d0b42d0b42d90b50b0b50b0b000000000000129c13004c01b001c00f03c08800f03c000f00003000f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f0b50b00003c0f00f0f00043073f1b43073f1b13131313a000a2aa5a5030342d0b42d0b660000000000002b1f0f0f2b1f0f0f130f130f2b0f2b0faa0b50b00a0f81eaa1b13131313aaaa13a9ea96960b42d0b42d0b66200c0000000000004a72000880013004c01b001c080f022000c021faa83c4c3c4c3cac3cac3ea82d42c0000f07c06c1e9e9c1c6e9c4e83c6c1d030329ccc3e9e9c6c8c0f01c2d00e9c3ccc8c4c4c8e0f0f84c83e0fa0001b07071b0f0f00042d0b42d0b642d40c0d42c0c0000000000004a703c3c3c3c3c3c3c3c3e83c3c3c3c3c3c3c3c3c2d42c008c4c4c8e83c3e13a9e0f83ea0f1b0f070f070f0f0f0f0f42d0b42d0b642d42c2d42c2c0000000000004a708c013006c007003c0800f03c000f00003000f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f0b50b00003c0f0071b071b47234713471347230f0f000aa207a802810b42d0742d40c0d6998000000000000bc3cbc3c6c1c1c3cbc7c3c3cbc7c3c3ea82d42c001c6c1c6e23a84ea0faaa07a9eaaa42d0b41d0b582d69980000000000004a708c013006c007022002000808003002f0f2f0f1b07070fa83e1faaa0b50b00003c1f00707070783e0f81ea7a07070723070707130707a81c3c1d0b42d0741d90b5070b50707000000000000129c23004c007001c00f03c08800701c00070fc0003000f0f0f0f070707070fa0f0707070f070f07070b50b00003c0f04723471347134723070707070707000aaa000a242d0b5a5030341d0766000000000000270f270f271f0f0f271f0f0f07070707aa0b50b00a84ea2307070707a07aaaaaa07a9d0b42d969682c2d0741d98008030000000000129c23004c0800220001c0070203c08800300270f270fa1f33aaa0f2f07070707aa0b50b00003c1f07b2313a781c8c4dec0ca7071b071b83e0f81c1e0708dec4c4dec8e80001c1c0010b42d0742d90b5030350b03000000000000129c0f0f0f0f0f07070f0fa0f0f0f0f0f0f0f0f0f0b50b00071b071b83e0fa070781ea70f230f0f0f130f0fa81c1c1d0b42d0742d90b50b0b50b0b000000000000129c23004c01b001c00f02003c0f0003c0000c003c3c3c3c3c1c1c3c3e83c3c3c3c3c3cbc3c3c3ccc3c3c2d42c0000f03c10b42d0b42d0b42c000000004a708c013006c007003c08003002f2f2f2f2f2f2f2f2f2f2f2f0b50b00003c1f00f0f0f0713071b07071b1b07071b1b88ea13a87e1faa87e2baa83eaaaaaa81ea7aaa88c4c4c8c7d1f0b1f47c2c6c1c1c6e60b9aaa231313231f031f07c0c7c1b07071ba880e2a8ccbcccbc3c3c3e9c3c4c3c3c3c4c3c3c1c1c3ea0f83eaa83c7c3c3c3c3c3c3c3c3c3c3c3c8c4c4c8c7c1c7c6c7c1c7c6c8c3c4c3c7e0f0f1f83c3c3c9c3c8c4c4c8c7d1f0b1f47c2cec9c9d4c3d4cec3c8c4c4c8c7c0c7c1f031f0cc9c9cbc3cbccc3cccbcccbc3c4c3e9c4c4c3c3c4c4c4c7c3c7c3c3c3c3c3c7c7c3c7c3cac7c3c7c3c4c4c4c4c3c3c3c3c3c3c3c3c4c4c4c4c9c9c9c9c3c3c3c3c4c4c4c4c9c9c9c9c3c3c3c3cbcbcbcbc3c4c3e9c3c3c3c3c3c3c3c3c9c3c3c3c3c3c3c3c3c3c3c3d4c3c3c3c3c3cbc3c3c4c3c3c6c3c1c3c1c3c3c3c3c3e0f83c3c3c2c3d0f43c2c3c0f030f030f03c3c3e83c3ea81c4c1c4c1c1c3c3c1c1c3c3eaaaaaaa84c4c4c4cdd370b374dc2c6c1c1c6ea84c4c4c4ccc0cbc33032f06c1c1c6ea8ccbcccbc3c3e0f0f0faaa0f07070faa0f0f0f0f0f0f0f0f1f0f 24 16777215 10 1023
def hc_75_3 : Nat → Nat := unpackHintV5 0xc9e226be2aeebde012bdc008bd7812bc504abc3008bc1008bab856b26216a6aaee9eb9fc93a2c693202092682e8b51c6832a0a7c29c074020a68cace6848206129c858b21e5101ec44b3143ea9823612262a0b02217226156b020d1216000344 0x1c4d071313131313131b07071b55555550707555551b1b5b0f3f8fe5b0f50450300c0300c0300c440303003030131313131b07071b2b272b27552b1f270f2b1f270f00c0c071307a707071313070707131b13131313131b07071b1384c3c4e130f544d513541d51b5544d5544d1356543d555555555400300c0300c03030030300300c50350129c4c4c4c4c6c1c1c6c4c4c4c3c4c7c4c3cac9cac9d1f5543d54030303ea7a783e9c4d075070f80ca73327a7a70f23131b070b2a700c9ccc1c1c1d07131313131307070707555555513135550707550fa0f50450300c0300c0300c5044a7030300303013131313070707072727272755271f270f271f270f00c0c07071307070707070707071307a70781c1c1e070f13131313070707075541d075541d544d513541d50756543d5555555554003030030300300c0300c0300c50350129c1c7c1c1c1c1c1c3c4c4c4c4c1c1c1c1c9c9c9c9d1f5543d54030304c4c4c4e1360f0f83e0f5555555a55371b37073707371b5550f0f50450300c0300c0321100c0c00c0c03c3c3c3c3c3c3c3c3e83d543c3c3c3c3c3c3c3c030304c4c4c4e13a9e83c3e0f83ea0f1b0f070f070f0f0f0f0f544d13544d23541d51b56543d550f5550f43d555555555400300c0300c03200c0c00c0c140d404a70f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f43d550f5500c0ca73f071ba761b073f0304c4c4c4ea984ea7aa55555550f0f553f1b07073f1b5a5550450300c0300c8851103030a0130f130f2b0f2b0faa552b1f0f0f2b1f0f0f00c0ca0f81eaa1b13131313aaaa13a9ea95599559544d513541d51b5656555555555502030a00300c0300c8850350129e1faa83c4c3c4c3cac3cac3ea91f5543d54030301c6c1c6ea9aa9555554ec8d6c4d6c4cec8d5543c3d695541140c0300c03221100c0c280cc3ccc3c6c1c1c3ea954cc7c3c3ccc7c3c3c030301c6c1c6e23a84ea0faaa07a9eaaa544d523541d51b556555995959555555555400300c0300ca080c22140d404a7330f330f1b07070fa83e1faaa47d550f5500c0c0707070783e0f81ea7a07070723070707130707a81c3c1d513548d50741d50746d5950f5541d3f5541d075555555555000c0300c0300c8030300303050350129c3c3c3c3c1c1c1c1c3e83c1c1c1c3c1c3c1c1d0f5543d5403030ec4c8e9c1c1c1c1eaaa69555554ec8c4dbc4cec8d41c1d55695541140c0300c0322141129c0c0c2809c3c9c3c1c1c1c1ea9549c7c3c3c9c7c3c3c03032a13a88c1c1c1c1e81eaaaaa81ea7544d52355665565507541d5959555555555400300c80c2800c0322140d404a7270f270fa1f33aaa0f2f07070707aa47d550f5500c0c071b071b83e0f81e5555554ec8d6c4d6c4cec8d55695541c1d41140c0300c0300c84403030030300f0f0f0f0f07070f0fa0f550f0f0f0f0f0f0f0f00c0c071b071b83e0fa070781ea70f230f0f0f130f0fa81c1c1d513548d50741d51b46d5950f5543d5543d0f555555543d0b555000c0300c0300c8030303c00c0c0c0c140d404a70f0f0f0f0f07070f0fa0f0f0f0f0f0f2f0f0f0f330f0f43d550f5500c0c3b3b3b3b544d523541d51b56543d55555400300c0300c0300c50350129cccbcccbcccbcccbcccbcccbd1f5543d54030306c6c00007130707070007070231313234f93c3d3e4f0f0707070742d0b503035070341d0742d0b00000000000023131323271f270f271f270f07070707272727270b50b00071b07071307a707070707070707231313230781c3c1e07070707070742d0b5070b5070741d0742d0b000000000000129c2308c01304c00701c000700007001c00f02000c008c4c4c8c1c1c1c3c1c7c1c1c1c1c1c1c9c9c9c9c2d42c0000f07c01c1c07071300070701b1b000131313131b07071b3f90c3cfe430f42d0b41d0b5030350b0342d0b000000000000131313131b07071b2b1f270f2b1f270f2b272b270b50b00071307a707071313070707131b13131313131b07071b1384c3c4e130f42d0b41d0b50b0b50b0b42d0b000000000000129c13004c01b06c00701c01304c00130000f02000c004c4c4c4c6c1c1c6c4c4c4c3c4c7c4c3cac9cac9c2d42c0000f07c04c4c0001c1c0001c1c074390c3d0e430f1313131307070707507035030342d0b41d0742d0b000000000000271f270f271f270f1313131307070707272727270b50b0007071307070707070707071307a70781c1c1e070f131313130707070741d41c1d41c1c2c2d0b42d0741d0b42c0700c0000000000004a701c0001c070004c23004c13001c1b001c07003c0800300071f07070707070f1313131307070707272727270b50b00003c1f0 24 16777215 10 1023
def hc_75_4 : Nat → Nat := unpackHintV5 0xef73bce781fcdc4aced33a44c383eebb2a16b3f1cea942aca1f9d296fac09051aa867a7680399078a1e672718c6ad9e660e27e5a21b05202084ac9ce4022aa3c01083451ec2ca1ec25c9b620d13e1bd93e1501b60fb9520861d60540c8000150 0x707070783e0f81ea7a07070723070707130707a81c3c1d0b42d0741d90b5070b5070703230303031303030307030303070303030faa030303070307030303030307033f03030303000c0300c0300c80303003030129d4150f0f0f0f070707070fa0f0707070f070f07070b50b0303030f030f030300c0c4723471347134723070707070707030303030303aaaaaaaa42d0b585041d07660300c50900300c88810270f270f271f0f0f271f0f0f07070707aa0b50b00c0ca84ea2307070707a07aaaaaa07a9d0b42d6960b41d07660323030303130303a03aaaaa03030307030303070303aaaa000c03280c0c28800c032204a750549c3c9c3e87cceaa83cbc1c1c1c1ea82d42c0c0c0c3c0c7c0c0c030301c6c1c6e0f83e0780d7c8d7c4d7c4d7c8e80c0c0c0c0e0707aa030342d0b41d0b642d4142c0300c0300c03200d050031503c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c2d42c030301c6c1c6e0f83e81c1e07a9c3c8c3c3c3c4c3c3ea07070742d0b41d0b642d42c2c2c2d0f50b0b0323030303130303031b030303070303030faa0303030f030f03030303030f0303030303000c0300c0300c80303003030129d4150f0f0f0f0f07070f0fa0f0f0f0f0f0f2f0f0f0f330f0f0b50b0303030f030f030300c0c42d0b42d0b42d0b0323030303130303031b030303070303030f0380e0303000c0300c0300c0304a75054ccbcccbcccbcccbcccbcccbc2d42c0c0c0c3c0c7c0c0c030301c071300070701b1b000131313131b07071b3f96c3cfe5b0f5555555555000000000000131313131b07071b2b1f270f2b1f270f2b272b275500071307a707071313070707131b13131313131b07071b1384c3c4e130f55555555550000000000129c0013004c01b001c01304c00130000f020100131313131b07071b1313130f131f130f2b272b275500000f2701f013130000707000070701d5e570f5795c3c4c4c4c4c1c1c1c1d555555555400000000004009c7c9c3c9c7c9c3c4c4c4c4c1c1c1c1c9c9c9c9d54001c1c4c1c1c1c1c1c1c1c1c4c1e9c1e07070781c3c4c4c4c4c1c1c1c1d55550742d55555400000000004a70001c0001c070004c013001c007003c0804001c7c1c1c1c1c1c3c4c4c4c4c1c1c1c1c9c9c9c9d5400003c9c07c04c4c4c4e20f83e0f00a0371b37073707371b0f0f00055555555550000000000000f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f55001313131384ea7a0f0f83e0fa83c6c3c1c3c1c3c3c3c3c3d555555555400000000004a70004c013006c007003c0800f03c000f0004003c3c3c3c3c3c3c3c3e83c3c3c3c3c3c3c3c3d5400003c3c03c03c3c0012c1cfc6d2c1cfc6c4c4c4c4e80028aa955555555540000000000400ac7c3c3cac7c3c3c4c3c4c3cac3cac3ea9540283e07aa86c4c4c4c4eaaa84ea7aa55555555550000000000129c00800220004c013006c0070202010087eaa0f130f130f2b0f2b0faa5500000f0f01f0071b071b3b234b134b133b230f0f000aa2a00a055555555550000000000002f0f2f0f1b07070f2f1f0f0f2f1f0f0faa5500071b071b88ea13a83eaa81ea7aaa9555555555400000000004a70008c013006c0070220020008080400bc3cbc3c6c1c1c3ea0f87eaa95400003c3c07c01c1c1c1e0f83e07a9e81c1c1c8c1c1c1c4c1c1ea070f0755555555550000000000129c0023004c007001c00f02001c070001c3f001000f0f0f0f070707070fa0f0707070f070f07075500000f0f00f03b234b134b133b23070707070707000aaa000a255555555550000000000100270f270f274b1f1f0f0f271f0f270f0f07070707aa5500a84ea2307070707a07aaaaaa07a9d55555590b55550000000000129c0023004c0800220001c00702020100270f270fa1f33aaa0f2f07070707aa5500000f0f01f0071b071b83e0f81e0ec8d6c4d6c4cec8e80001c1c001555555555400000000000003c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3d6c3c7c3c3d54001c6c1c6e0f83e81c1e07a9c3c8c3c3c3c4c3c3ea070707555555555500000000003c030129c0023004c01b001c00f02003c0f0003c001000f0f0f0f0f07070f0fa0f0f0f0f0f0f2f0f0f0f330f0f5500000f0f00f0272727270f0f0f0f0f0f0f0f555555000000000f0f0f0f0f0f0f0f0f0f0f0f5500071307a707071313070707131b13131313131b07071b1384c3c4e130f5555555555000000000000131313131b07071b1313131f131f13131f1f1f1f550007071307070707070707071307a70781c1c1e070f13131313070707075555555555000000000000071f07070707071f13131313070707071f1f1f1f55001313131384ea7a0f0f83e0fa83c6c3c1c3c1c3c3c3c3c3d55555555540000000000004c4c4c4c7c7c7c7c3e83c3c3c3c7c3c7c3c3d540283e07aa86c4c4c4c4eaaa84ea7aa555555555500000000000087eaa1f131313131f1f1f1faa5500071b071b88ea13a83eaa81ea7aaa955555555540000000000007c7c7c7c6c1c1c6ea1f87eaa954001c1c1c1e0f83e07a9e81c1c1c8c1c1c1c4c1c1ea070f0755555555550000000000001f1f1f1f070707070fa0f0707071f071f07075500a84ea2307070707a07aaaaaa07a9d55555555540000000000007c7c7c7e87c7eaa87cbc1c1c1c1ea954001c6c1c6e0f83e81c1e07a9c3c8c3c3c3c4c3c3ea07070755555555550000000000001f1f1f1f1b07071b0fa0f0f0f0f0f1f2f0f0f1f1f0f0f55003b3b3b3b555555000000001f1f1f1f1f1f1f1f1f1f1f1f55003b3b3b3b555555000000129c0023004c01b001c00f0201002f2f2f2f2f2f2f2f2f2f2f2f5500000f01f0 24 16777215 10 1023
def hc_75_5 : Nat → Nat := unpackHintV5 0x84747b1fbd2c07b7c6f1dcc2267700061dbc00876c0061d880507610021d800087560141c621ec6c24ac9a581626444a397104025724a393c840249fca4907141c3ca0a48d0a43c30387e0aae2c026389007b43b41ae07e055b2ba10e49102523ce05587e00002ac 0x1c1c1c1e0f83e0781d0b42d107642d5c8d5c4d5c4d5c8c01400c0ea81c0c2c2c0000000000000003c3c3c3c1c1c1c1c3e83c2d42c3c3c3c3c3c3c3c3c001c1c1c1e0f83e0781d0b42d0769d41c1d90b0723070707130707541c3ea81c1c1c2c1c0000008a700000008c013001c007000c02c0b011001c070001c00003c3c3c3c1c1c1c1c3e83c2d42c1c1c1c3c1c3c1c1c0000f03c0ec8d5c4d5c4cec8c1c1c1c1c1c1c0020f83d5540c0e0781d55400145540000000000003c3c3c3c3c3c3c3c3c3c3c3c1c1c1c1c3e83d5401513548c1c1c1c1d41e0f83d9550f81e075555550769d540040300000000229c0023004c0400110001c007000c102c044000f0f0f0f43d550f070707070fa0f5500003c0f02313a7a71323a70760341c8c4c0ca7330fa7a7231b03e0b04e9c030f33071b071b83e0f81e0f42d0b41c1d07190b2313132350000303aa0b030707000000000229c0000000f0f0f0f0f07070f0fa0f0b50b0f0f0f0f0f0f0f0f00071b071b83e0f81e0f42d0b5070741da7642c2c8c2c2c2c4c2c2d50b0faa0b0b070707000000229c00000023004c01b001c00300b01002c0b0002c00003c3c3c3c3c1c1c3c3e83c2d42c2c2c2c3c2c3c2c2c0000f03c20f83e0f83c3e83c0000008a70008c013006c007000c02c04000f0f0f0f0f0f0f0f0fa0f0f0f0f0f00003c0f01b1b030303030303030707070303030307070303231313234f93c3d3e4f0f0707070742d0b5050710741d0b42c0c0300d0500300c0300c03108c4c4c8c9c7c9c3c9c7c9c3c1c1c1c1c9c9c9c9c2d42c030301c6c1c1c4c1e9c1c1c1c1c1c1c1c8c4c4c8c1e070f0781c1c1c1c1c1d0b42d41c2d41c1d0741d0b42c0c8c0c0c0c4c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c0c0c0c1c0c0c0c1c0c0c0c3c0e0380c0c00300c03030030300300c0300c129d415231313230707070f071f070707070707272727270b50b0303030f031f030300c0c0703071303030303070703031b1b030303030303131313131b07071b3f90c3cfe430f42d0b41d0b5050b10b42c0c0300c0300d0500300c03104c4c4c4c6c1c1c6cac7c9c3cac7c9c3cac9cac9c2d42c030301c4c1e9c1c1c4c4c1c1c1c4c6c4c4c4c4c4c6c1c1c6c4e130f1384c3d0b42d0742d42c2d42c2d0b42c0c4c0c0c0c4c0c0c0c6c0c0c0c1c0c0c0c4c0c4c0c0c0c0c0c4c0c0c0c0c0c0c3c0e0380c0c00300c0300c03030030300300c129d415131313131b07071b1313130f131f130f2b272b270b50b0303030f031f030300c0c13130303030303030707030303030303070703074390c3d0e430f13131313070707075071410b42d0741d0b42d400d00300c0300c0300c030409c7c9c3c9c7c9c3c4c4c4c4c1c1c1c1c9c9c9c9c2d42c030301c1c4c1c1c1c1c1c1c1c1c4c1e9c1e07070781c3c4c4c4c4c1c1c1c1d41c1d41c2d0b42d0741d0b42c0c1c0c0c0c0c0c0c1c0c1c0c0c0c0c0c4c0c0c0c4c0c0c0c1c0c0c0c1c0c0c0c3c0e0380c0c0030303030030301c00c0300c0300c0304a750541c7c1c1c1c1c1c3c4c4c4c4c1c1c1c1c9c9c9c9c2d42c0c0c0c3c0c7c0c0c030301c4c1c0c1c1c0c0c0c0c0c0c4c4c0c0c0c0c0c0c8c4c4c8c6c1c1c6cfe5f0f3f97c3d0b42d0742d4142c42d0b0300c0300c0341400c0300c54231313231b07071b331f270f331f270f332733270b50b00c0c07071313071307a7070707131313231313231b07071b1b86c3c6e1b0f42d0b41d0b50b0b0b0b46d42c2d0b42c0c8c0c0c0c4c0c0c0c6c0c0c0c1c0c0c0c6c0c6c0c0c0c0c0c6c0c0c0c0c0c0c3c0e0380c0c00300c0300c03030030300300c129d415231313231b07071b1b1b1b1b0f2f1b1b1f331b0f332733270b50b0303030f031f030300c0c0f0f0303030303032313132347073f1b47073f1baaaaaaaa42d0b505842d0b660300c90500300c8884230f130f331f0f0f331f0f0f330f330faa0b50b00c0c83e23131323a86e07a84ea7aaaaa90b42d60b5a42d0b660323030303130303aaa0303a03aa031b030303070303aaaa000c032820300300c88129d415230f130faa0f2fa1f33a330f330faa0b50b0303030f031f030300c0c1313131380e0f83e0f030303a80c0cdc6cdc1cdc1cdc6c3c3ea80c0d0b42d0b42d90b5050b00c0300c0300c80341400c40f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f0b50b00c0c1313131384ea7a0f0f83e0fa83c6c3c1c3c1c3c3c3c3c3d0b42d0b42d90b50b0b50b0b0313030303130303031b030303070303030faa0303030f030f03030303030f0303030303000c0300c0300c80303003030129d4150f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f0b50b0303030f030f030300c0c0f0f03030303030343073f1b43073f1b13131313aaaaaaaa585042d0b42d0b6650900300c0300c88842b1f0f0f2b1f0f0f130f130f2b0f2b0faa0b50b00c0ca0f81eaa1b13131313aaaa13a9ea96960b42d0b42d0b66a03aaaaa03030313030303130303031b030303070303aaaa0280c0c28800c0300c032204a750561faa83c4c3c4c3cac3cac3ea82d42c0c0c0c3c0c7c0c0c030308c4c4c8e0f80e0f83e80c0c0c0c0e5f1b5f075f075f1b0f0faa030342d0b42d0b642d4142c0300c0300c03200d050031503c3c3c3c3c3c3c3c3e83c3c3c3c3c3c3c3c3c2d42c030308c4c4c8e83c3e13a9e0f83ea0f1b0f070f070f0f0f0f0f42d0b42d0b642d42c2c2c2d0f50b0b0323030303130303031b030303070303030faa0303030f030f03030303030f0303030303000c0300c0300c80303003030129d4150f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f0b50b0303030f030f030300c0c071b071b47234713471347230f0f030303030303aaaaaaaa42d0b41d0b5058660300c0300c90508884330f330f1b07070f331f0f0f331f0f0faa0b50b00c0c071b071b88ea13a83eaa81ea7aaa90b42d0742d60b5a660323030303130303031b030303070303aaa0303a03aaaaaa000c0300c0328203088129d415330f330f1b07070fa83e1faaa0b50b0303030f031f030300c0c 26 67108863 11 2047
def hc_75_6 : Nat → Nat := unpackHintV5 0xf02820e909c8e0921ed8e1eccc9314c4a1fcb98ac6b90820b8502eb139c6a9120aa309829a72268e6b0285d22679cb0271721664634463d8225ac2464e8b0e4771c63f4a0a342ac82d39bc241a4823982022c8341ad9fc0f92d20879c600021e 0xfc1c6e9c4c4c4c4eaaaa82c2ea8fc6c1e6c1cfc6d4115555555555540c0300c03281229c0c0c141104c3c4c3cac3cac3ea8ac7c3c3cac7c3c3d540303142d075546c4c4c4c4d6955556a84ea13a81ea1b6556aaaa0155544da75555555540c1400c0300c03280e808a74451f335550f0f130f130f2b0f2b0f87eaa0faa5500c0c23131323aaaa9aa5371b37073707371ba08a42d90b42d996942c2c0c0300c032200c0c00c0c00c4230f130f330f330faa331f0f0f331f0f0f0b50b00c0c23131323a84e13a88e23a81ea1baaaa0142c2d1369d0b42d6960b66542c6c2c1c2c1c2c2e82eaaaa82c2e82c3eaaa82c2c2c0c0300c03280e808a703100c0c0b0030303030230f130f330f330f87eaa0faa0b50b0b0b0b0b0f0f0b0b1f330b0b00c0c07070707aaaa4723471347134723a59aa08a42d0b41e41c1d996942c2c0c0300c032200c0c00c0c00c4270f270f07070707aa271f0f0f271f0f0f0b50b00c0c07070707a84ea23a81e07a81e1baaaa010b42d0769d41c1d6960b6607230707071307075681eaaaa81c1eaaa81c2c1c0c0300c03280e808a703100c0c00c0c09c3c9c3c1c1c1c1e1faa83ea82d42c1c1c1c3c1c7c1c1c03030ec4c8e9e48c4cee9c0c07070707aaaa3b2313133b23a0707aa5045555550769d5555540c0300c0328480c0c141109c3c9c3c1c1c1c1ea89c7c3c3c9c7c3c3d5403031513548c1c1c1c1d41ea13a88d6955556a81ea07aa6556aa015555541da75555550300c40c1400c03280e808a744270f270f47d550f0707070787eaa0faa5500c0c3f3fa84ea23a81ea1baaaa00fcfe6a60baa0300c0300ca03a0229c0c030cc3ccc3ccc3ccc3e1faa83ea8cc3ccc3c030306c6c0000713070707000707083e0fa0303a070381e07231313233b53c2ced4f0b070707070fa0f0000000000000f0f0f0f0f0f0f0f0f0f0f0f070707070fa0f0f0f0f0f00071b07071307a70707070707070783e0fa070fa070781e07231313230741c2c1d0707070707070fa0f0000000000229c002308c01304c00701c000700007001c00300b010003c3c3c3c1c1c1c3c1c3c1c1c1c1c1c1c3e83c3c3c3c3c0000f03c01c1c07071300070701b1b00083e0f81e0fa0303a0f03131313131b07071b6358c2d8d630b0fa0f0000000000000f0f0f0f0f07070f0f0f0f0f0f0f0f0f0fa0f0f0f0f0f00071307a707071313070707131b1383e0f81e0fa0f0fa0f0f131313131b07071b1344c2c4d130b0fa0f0000000000229c0013004c01b06c00701c01304c00130000300b010003c3c3c3c3c1c1c3c3c3c3c3c3c3c3c3c3e83c3c3c3c3c0000f03c04c4c0001c1c0001c1c07a0703a030383e0f81e075755c2d5d570b13131313070707070fa0f0000000000000f0f0f0f0f0f0f0f0f0f0f0f070707070fa0f0f0f0f0f0007071307070707070707071307a781e81c1e81c1c3c3e0f83e0781c1d07070741c2c4c4c4c4c1c1c1c1c3e83c0700c00000000008a70001c0001c070004c23004c13001c1b001c07000c02c0400070f07070707070f0f0f0f0f070707070fa0f0f0f0f0f00003c0f0a73b0b69c1c1c4c4c1c4c1e9c0707000131300083e0f81e0fa0303a0f03231313231b07071b3b42ced8f0b0fa0f0000000000229c000f0f0f0f0f07070f0f0f0f0f0f0f0f0f0fa0f0f0f0f0f0007071313071307a707070713131383e0f81e0fa0f0fa0f0f231313231b07071b1b46c2c6d1b0b0fa0f0000000000229c0023004c01b001c01b06c001b0000300b010003c3c3c3c3c1c1c3c3c3c3c3c3c3c3c6c3ccc3c3c3e83c3c3c3c3c0000f03c02c2c0008c4c4c8d0c1d0c6d0c1d0c6e0f83d40c0d560f83c44d5005055550000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fa0f550042d23131323546d07583e0f543d960f83d1369d55555550000000000229c0023004c0440040006c007000c1010003c3c3c3d50f43d43c3c3c3c3e83d540000f03c04c4c4c4e0f83e0f83d1369d42c2d0b42d90b542c6c2c1c2c1c2c2c2c3ea82c2c2c2c2c0000008a700000004c013006c007000c02c0b011002c0b0002c3b00003c3c3c3c3c3c3c3c3e83c2d42c2c2c2c3c2c3c2c2c0000f03c02c2c0017c1d7c6d7c1d7c6c4c4c4c4d5540c0e0f83e0f83d40014555540000000000003c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3e83d540142d075546c4c4c4c4d695543c3e0f83e0f83d55544da75555100c00000000008a7001000440013004c01b001c003040b01100143ccd5543c3c3c3c3c3c3c3c3c3c3e83d540000f03c1dc6c1e9d0b1b07770329c8c4c4c8e0f83e0f83d0b0b44c42d0b642d40006ddc1c1ddc6c0c0ea82c0c2c2c0000000008a700000003c3c3c3c3c3c3c3c3e83c2d42c3c3c3c3c3c3c3c3c008c4c4c8e0f83e0f83d42c2d1369d0b42d90b542c6c2c1c2c1c2c2c2c3ea82c2c2c2c2c0000008a700000008c013006c007000c02c0400b02c000b00000f0f0f0f0f0f0f0f0fa0f0b50b0b0b0b0b0f0f0b0b0f330b0b00003c0f0071b071b3b235f135f133b230b0b00083e0f81e0f503035555107540141540000000000003c3c3c3c3c1c1c3c3c3c3c3c3c3c3c3c3e83d54001c6c1c6d23544d50b60f83e0783d50f655541da755555400000000008a70008c013006c007011001000030404000f0f0f0f0f07070f550f0f50f3350fa0f5500003c0f0 24 16777215 10 1023
def hc_75_7 : Nat → Nat := unpackHintV5 0xb68a08af51cea4aaaa9e01aa942a768de9908651e68231087a81ec72d1ec6dd93e6701b661b9525a61d65389b64e913e4b70c84631503d9a2631e2ee31981231780831301230084a2fe8082fc8082e7056261a161a62ee1361c00b3a0a0002ce 0x142d075546c4c4c4c4d695560faaaa55551369d5554000000008a700001000440013004c01b001c0810100147ccd5543c3c4c3c4c3cac3cac3ea95400003cac07c08c4c4c8eaaa90b442d0b665000371b37073707371baaaa0b0b0000000000000000230f130f2f0f2f0faa0b50b2f1f0f2f0f0f2f371f1f0f0f0023131323aaaa50b0b44da742d0b66542c6c2c1c2c1c2c2eaaa82c2c2c00008a7000000002c03008c013006c0070200b01002c0b0002c00008c3c4c3cbc3cbc3ea82d42c2c2c2c2c3c3c2c2c7ccc2c2c00003cac07c01c1c1c1eaaa90b42d1076647234713471347230050aaaa0b0b000000000000000270f270f07070707aa0b50b271f0f0f271f0f0f0007070707aaaa42d0b41da75070766072307070713070756aaa81c2c1c00008a70000000008c013001c0070200b01001c070001c00009c3c9c3c1c1c1c1ea82d42c1c1c1c3c1c7c1c1c00003c9c07c0ec8d5c4d5c4cec8c1c1c1c1c1c1c002aa9556a9554001455400000000800009c3c9c3c9c7c3c3c9c7c3c3c1c1c1c1ea95401513548c1c1c1c1d41ea9955aa95555541da75500000000229c000023004c0400110001c00702040400270f270f47d550f07070707aa5500000f2701f027272727aaaa2b2b2b2b27272727aa000000000f0f0f0f0f0f0f0faa0f0f0f0f00071b07071307a707070707070707aaaaaaaa231313230741c2c1d070707070707aa0000000000001f13131f0707071f071f070707070707aa1f1f1f1f0007071307070707070707071307a7aaaaaaaa0741c1c1d070b1313131307070707aa000000000000071f07070707071f1313131307070707aa1f1f1f1f0042d23131323546d075aa5665aa44da7555555540000000000007c4c4c7d51f47d47c7c7c7ea954004c4c4c4eaaa91369d42c2d0b42d9950b1b0b070b070b0baaaa0b0b0b000000000000131313131f1f1f1faa0b50b0b0b0b1f0b1f0b0b0050b41d551b131313136556aaaa55551369d555400000000000147c7d5547cbc4c4c4c4c7c7c7c7ea954008c4c4c8eaaa942c2d1369d0b42d9950b1b0b070b070b0baaaa0b0b0b0000000000001f13131f1f1f1f1faa0b50b0b0b0b0b1f2f0b0b1f1f0b0b0007070707aaaa42d0b41da75070766072307070713070756aaa81c2c1c0000000000007c7c7c7c1c1c1c1ea82d42c1c1c1c7c1c7c1c1c01513548c1c1c1c1d41ea9955aa95555541da7550000000000001f1f1f1f47d551f07070707aa55003f3faaaa3f3faa000000001f1f1f1f1f1f1f1faa1f1f1f1f003f3faaaa3f3faa0000229c000023004c01b001c0802c04002f0f2f0f2f0f2f0faa2f0f2f0f00000f01f081c1c1c1c1eaaaaaa86c6e81c1eaa82288c4c4c8c1c1c1c1ea8dd370b374dc2c0c0300c032200c0c00c0c00c0308c3c4c3c1c1c1c1ea89c7c3c3c9c7c3c3c9c3c9c3c030301c6c1c1c4c1e9c1c1c1c1c1c1c1ea13a88eaa07aaa0781ea07a81eaaaaaaa80231313230741c2c1d0707070707079a982ea80c0300c0c00c0c00c03280e808a70300c230f130f0707070f071f07070707070787eaa0faa270f270f00c0c0b69e9c2da71381e81c2da7030cc3e9e9c2c8c4c6c1c3c69c030f3307070781c1eaaaa84c4eaa81c1eaa82284c4c4c4c1c1c1c1ea90b42c0c0300c03282229c0c0c00c0c00c0304c3c4c3c1c1c1c1ea89c7c3c3c9c7c3c3c9c3c9c3c030301c1c4c1c1c1c1c1c1c1c1c4c1e9eaa0781eaa07aa13a84ea07a81eaaaaaaa800741c1c1d070b13131313070707079a982ea80c0c00c0c00c0300c03280e808a70300c071f07070707070f130f130f0707070787eaa0faa270f270f00c0c23131323aaaaaaa0b0b371b37073707371b5045555555555550300c0300c84030305044230f130f330f330faa331f0f0f331f0f0f5500c0c42d23131323546d075a84ea2355596956a07a86ea95996a8044da75555555555540c031410300300ca03a0229d108c3c4c3d50f47d4cc3ccc3e1faa83ea954030304c4c4c4ea1384ea1388ea07a86eaaa8044da750b0b42d0b5a582d9950b1b0b070b070b0ba0b3baaaaa0b0baaaa0b0b0b0300c0300ca03a0229c0c40303003030130f130f2b0f2b0f87eaa0faa0b50b0b0b0b0f0b1f0b0b00c0c 24 16777215 10 1023
def hc_75_8 : Nat → Nat := unpackHintV5 0xa738a3a7cd4029a18a3a4854028cf0a4a12e41c7f94a49dc743c732c7e1b752ac665cef18991fc5cc8b396102445064fb931d1f846f4b0109d2403b0ced0dc71f831a8ae8b482442584f388562161dbc7386192ac14c07483d02c00c286302171e603609f80001b0 0x6c6c0c0c0c0c0c0c0c1c1c1c0c0c0c0c1c1c0c0e0f83e8281c81e07231313233b52c2ced4b0b070707070fa0f0300c0382800c0300c80300c0f0f0f0f0f0f0f0f0f0f0f0f070707070fa0f0f0f0f0f00c0c071b07071307a70707070707070783e0fa070fa070781e0703230303031303030307030703030303030703030303030307030303070303008c4c4c8c1d070b0741c1c1c1c1c1c3e83c0d030b0340c0c0c0300c0c00c0c00c0308a7a0a80c0303c3c3c3c1c1c1c3c1c3c1c1c1c1c1c1c3e83c0c0c0c3c0c3c0c0c3c3c3c3c030301c0c1c4c0c0c0c0c1c1c0c0c6c6c0c0c0c0c0c0e0f83e0783e8283c131313131b07071b4b52c2d2d4b0b0fa0f0300c0300c0382800c80300c0f0f0f0f0f07070f0f0f0f0f0f0f0f0f0fa0f0f0f0f0f00c0c071307a707071313070707131b1383e0f81e0fa0f0fa0f0f0313030303130303031b030303070303031303130303030303130303030303004c4c4c4c6c1c1c6c4d130b1344c2c3e83c0d030b0340c0c0c0300c0300c0c00c0c08a7a0a80c0303c3c3c3c3c1c1c3c3c3c3c3c3c3c3c3c3e83c0c0c0c3c0c3c0c0c3c3c3c3c030304c4c0c0c0c0c0c0c1c1c0c0c0c0c0c0c1c1c0c1e81ca083e0f81e074b52c2d2d4b0b13131313070707070fa0fa003800c0300c0300c200300c0f0f0f0f0f0f0f0f0f0f0f0f070707070fa0f0f0f0f0f00c0c07071307070707070707071307a7a0707a070f83e0f81e0703070303030303030703070303030303130303031303030307030303070303001d07070741c2c4c4c4c4c1c1c1c1c3e83c0d030b0340c0c0c0c0c0c00c0c0700300c0300c229e82a0300c070f07070707070f0f0f0f0f070707070fa0f0303030f030f03030f0f0f0f00c0c071307030707030303030303131303030303030383e0f81e0fa0a0f08c4c4c8c6c1c1c6ced4b0b3b52c2c3e83c0c0300c0300e0a0032a00c0303c3c3c3c3c1c1c3c3c3c3c3c3c3c3c3c3e83c3c3c3c3c030301c1c4c4c1c4c1e9c1c1c1c4c4c4e0f83e0783e83c3c3c3e1ba0f0f0323030303130303031b030303070303031b031b03030303031b0303030303008c4c4c8c6c1c1c6c6d1b0b1b46c2c3e83c0d030b0340c0c0c0300c0300c0c00c0c08a7a0a80c0303c3c3c3c3c1c1c3c3c3c3c3c3c3c3c6c3ccc3c3c3e83c0c0c0c3c0c3c0c0c3c3c3c3c030300c0c2c2c0c0c0c0d0c1d0c6d0c1d0c6c8c4c4c8d41520f83e0f83d555555555542800c0300c03121103c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3e83d54030310b48c4c4c8d51b41d60f83d50f6583e0f0323030303130303555030350355031b030303070303011369d555555555550300c5040c00c0308a7a0a9103c3c3c3d50f43d43c3c3c3c3e83c0c0c0c3c0c3c0c0d54030304c4c4c4e0f83e0f83c0c4c0c0c0c4c0c0c0c6c0c0c0c1c0c0c044da750b0b42d0b642d40c2d40c0d50b1b0b070b070b0b0b0faa0b0b0303030303030b0b03030b3b030303030b0b0b0300c0300c229e82a03100c0c00c0c03c3c3c3c3c3c3c3c3e83c0c0c0c3c0c3c0c0c2d42c2c2c2c3c2c3c2c2c030300c0c2c2c0c0c0c0c4c4c4c4d2c1d2c6d2c1d2c6e0f83d51420f83d55555555540c03281400c031081103c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3e83d540303142d075546c4c4c4c4d9550f83e0f83e0f5035555503030313030303130303031b0303030703030155544da7555555555030305100300c0300c229e82a4450f335550f0f0f0f0f0f0f0f0f0f0fa0f0303030f030f03035500c0c231313235030303030352c6d2c1d2c1d2c6e0f83e0f83e8282c42d0342d0b50b0b50303642c0c0300c0300e0a0032a00c40f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fa0f0b50b00c0c2313132383e0f83e0f0323030303130303031b0303030703030142c2d1369d0b42d90b5030b50303542c6c2c1c2c1c2c2c2c3c2c3ea82e0b0b0303030303030b0b03030b030303030b0b0b0300c0300c229e82a03100c0c00c0c03c3c3c3c3c3c3c3c3e83c0c0c0c3c0c3c0c0c2d42c2c2c2c2c3c3c2c2c3ccc2c2c03030ec8d2c4d2c4cec8c1c6c1c6c0c0c2c2c0c0c0c0e0f83d41520783d55555555540c03142800c03121103c3c3c3c3c3c3c3c3c3c3c3c3c1c1c3c3e83d54030301c6c1c6d23544d50b60f83e0783d50f650323030303130303031b03030307030355503035035501550769d5555555550300c0300c5040c08a7a0a9103c3c3c3c3c1c1c3d543c3d43ccd43e83c0c0c0c3c0c3c0c0d54030301c1c1c1d2c8d2c4d2c4d2c8c0c0c0d5030383e0f81e07a0a0710b42d0341d42c2d40c0d90b0300c0300c0382800c803103c3c3c3c1c1c1c1c3c3c3c3c3c3c3c3c3e83c2d42c030301c1c1c1e0f83e0781c0c8c0c0c0c4c0c0c0c1c0c0c0c1c0c0c042d0b41da750707642d40c2d40c0c1c8c1c1c1c4c1c1d5070faa0707030303030303070703030703030303070b070300c0300c229e82a03100c0c00c0c03c3c3c3c1c1c1c1c3e83c0c0c0c3c0c3c0c0c2d42c1c1c1c3c1c3c1c1c030301c1c1c1cec8d2c4d2c4cec8c0c0c1c1c0c0c0c0e0f83e0781d514155555555540c0300c032814121103c3c3c3c1c1c1c1c3c3c3c3c3c3c3c3c3e83d5403031513548c1c1c1c1d41e0f83d9550f81e0703230303031303035035555503030307030303070303015555541da75555550300c5030305100300c229e82a440f0f0f0f43d550f070707070fa0f0303030f030f03035500c0c071b071b4b234b134b134b235030303030360f83e0783e8282c42d0b41d035070750303642c0c0300c0300e0a0032a00c40f0f0f0f0f07070f0f0f0f0f0f0f0f0f0fa0f0b50b00c0c071b071b83e0f81e0f0323030303130303031b030303070303010b42d41c1d0769d90b5030b503030b230b0b0b130b0b542c3c2c3ea82e0b0b0303030303030b0b03030b030303030707070300c0300c229e82a03100c0c00c0c03c3c3c3c3c1c1c3c3e83c0c0c0c3c0c3c0c0c2d42c2c2c2c3c2c3c2c2c030320f83e0f83c0c8c0c0c0c4c0c0c0c6c0c0c0c1c0c0c00fa0f0340c2c0d03030300c0300c229e82a0300c0f0f0f0f0f0f0f0f0fa0f0303030f030f03030f0f0f0f00c0c1b1b00001c1c1c001c1c2aaaaaaa88c4c4c8cdd370b374dc2c1c1c1c1ea80000000000008c3c4c3c9c7c3c3c9c7c3c3c1c1c1c1ea89c3c9c3c001c6c1c1c4c1e9c1c1c1c1c1c1c1eaaaaaaa88c4c4c8c1d070b0741c1c1c1c1c1ea8000000008a7000008c013001c070001c0001c0070200b010008c3c4c3c1c1c1c3c1c7c1c1c1c1c1c1ea89c3c9c3c00003c9c07c04c4c0001c1c0001c1c07aaaaaaaa5755c2d5d570b1313131307070707aa0000000020000271f0f0f271f0f0f130f130f07070707aa270f270f0007071307070707070707071307a7aaaa81e0faaaa0741c1c1d070b1313131307070707aa00000000229c0000070000701c0013004c007001c0802c0400071f07070707070f130f130f07070707aa270f270f00000f2701f00b0b000231313233707371b3707371baa55a5aa1500505555000000000000230f130f2f1f0f0f2f1f0f0f2f0f2f0faa550042d23131323546d075aa5665aa44da755555554000000008a7000008c0130110010001b001c081010008c3c4c3d50f47d4bc3cbc3ea95400003cac07c04c4c4c4eaaa91369d42c2d0b42d9950b1b0b070b070b0baaaa0b0b0b0000229c0000000013004c01b001c0802c0400b02c000b0ec000130f130f2b0f2b0faa0b50b0b0b0b0f0b1f0b0b00000f2b01f00b0b0005f073f1b5f073f1b13131313a555aaaa500051555500000000200002b5f1f1f0f0f2b1f0f2b0f0f130f130f2b0f2b0faa5500 26 67108863 11 2047
def hc_75_9 : Nat → Nat := unpackHintV5 0xe4a25edc0a26d00302cf7822c64a4cba7af4b301dea9ca4e9da30a95d1f48b8a928ac0328820a87e92647243146b41c062b22462302061782e5972024e92b848f168403a2e37822e31518c289a2e2219a018e24e1341680b79f206d9280001b6 0xc0c0c4c0c0c0c8c1c1c1c1c00380c0c0e030f070707070340c0c0d030b070707070300c0303030303001ca70300c0300c27272727031f03030303030f07070707272727272727272700c0c07130713a283e0783c02800c0c1c1c1c1c3c0c3c3c0004c4c4c4c6c1c1c6c3e83cdd370b374dc2c0000000000003c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c3c3c3c3c001c4c1c4e13a9e83c3e0783ea0f1b070707070f0f0f0f0f131313131b07071b0fa0f0f43c2c3d0f0b000001ca70000000004c013000c03c0f022003c0f0003c0002c04000f0f0f0f0f07070f0fa0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00f0a73b0b69c1c4c1c6e83c3e13a9c81e0fa0000303070707070f030f0f000231313231b07071b0fa0f3b42ced9f0b000001ca70000000003c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c3c3c3c3c001c4c1c6e83c3e13a9e0783ea0f1b070707070f0f0f0f0f231313231b07071b0fa0f0f43c2c3d0f0b000001ca70000000008c013000c03c0800f03c000f0000b010003c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c3c3c3c3c00003c3c03c02c2c0001c4c1c6d40c0d548c4c4c8cfe430f3f90c3c6c1c1c6c44d500505555000000000000231313232f1f270f2f1f270f1b07071b2f272f27550042d0713071b546d07523131323543d946c1c1c6d1369d55555550000000001ca7000008c23004c130110010000300f0201010008c4c4c8d50f47d46c1c1c6cbc9cbc9d5400003cac07c01c4c1c4c4c4c4c4c6c1c1c6d1369d42c2d0742d0b42d50b1b070707070b0b0b0f0b82e0b0b0b0b0b000001ca70000000004c013000c03c0800b02c04400b02c000b0ec000131313131b07071b2b272b270b50b0b0b0b0f0b1f0b0b00000f2b01f00b0b0005550303071307133f93c3cfe4f0f131313131b07071b50005155550000000000002b4f1f1f270f2b1f272b0f0f131313131b07071b2b272b27550050b507075551b1b0713071365543c4c4c4c4c6c1c1c6d55544da75555100c000000000729c0000400110004c23004c13000c03c08040b01100147ccd5543c9c4c4c4c4c6c1c1c6cac9cac9d5400003cac07c29cfc3ea70f9342c4da7400307070b933737770b009c9c3c01ca7000713071b231313231b07071b50b0b44da710742d0b42d40000c0c1c1c1c1c2c0c3cfe3f9dc3c2c2c00000000729c00000000231313231b07071b2f272f270b50b2f1f272f0f0f2f1f1f270f000713071b231313231b07071b50b0b44da741d0b42d0b542c6c1c1c1c1c2c2c2c3c2e0b82c2c2c2c2c00000729c0000000023004c00300f02002c0400b02c000b0000231313231b07071b2f272f270b50b0b0b0b0b0f270b0b1f330b0b00000f2b01f0071b071b83e0f81e0f3b23471347133b2303035550b0b000555519500500000000000000f0f0f0f0f07070f0fa0f0f0f0f0f0f0f0f0f5500071b071b83e0f81e0f48d513546d507542d5555669d555000001ca70000000008c013000c03c0f022011001000404000f0f0f0f0f07070f0fa0f543d0f55500000f0f00f0a76723139a72313670301c6c1c6e0f83e0783d0b42d0742d699a708d9c4c4d9c8c0c0c1c1c1c1c2c0d4002800000001c000000000f0f0f0f0f07070f0fa0f0b50b0f0f0f0f0f0f0f0f00071b071b83e0f81e0f42d0b41d0b5a669c2c8c2c2c2c4c2c2c2c6c1c1c1c1c2c2d5a800000729c0000000023004c00300f02002c0400b02c000b00000f0f0f0f0f07070f0fa0f0b50b0b0b0b0f0b0f0b0b00000f0f00f0071b071b0f0f0f0f0f07070f2b2b2b2b1b07071b0f0f0f0f000000000f0f0f0f0f0707030f0f0f0f0f0f0f0f000713071384ea7a0f0f81e0fa83c6c1c1c1c1c3c3c3c3c3c4c4c4c4c6c1c1c6c3e83c3d0f0b0f43c2c0000000000004c4c4c4c0c1c1c3c3e83c3c3c3c7c3c7c3c3c7c7c7c7c001c4c1c6e83c3e13a9e0783ea0f1b070707070f0f0f0f0f231313231b07071b0fa0f0f43c2c3d0f0b0000000000001f13131f0307070f0fa0f0f0f0f1f0f1f0f0f1f1f1f1f0042d0713071b546d07523131323543d946c1c1c6d1369d55555550000000000001f13131f547d1f50307071b1f1f1f1f550007130713131313131b07071b44da750b0b41d0b42d0b542c6c1c1c1c1c2c2c2c3c2e0b82c2c2c2c2c0000000000004c4c4c4c0c1c1c6c7c7c7c7c2d42c2c2c2c7c2c7c2c2c0142d075546c1c4c1c4d9550f131313131b07071b55551369d555400000000000147c7d5547cbc4c4c4c4c0c1c1c6c7c7c7c7d54001c4c1c6c8c4c4c8c6c1c1c6d42c2d1369d0742d0b42d50b1b070707070b0b0b0f0b82e0b0b0b0b0b0000000000001f13131f0307071b1f1f1f1f0b50b0b0b0b0b1f2f0b0b1f1f0b0b00071b071b83e0f81e0f48d513546d507542d5555669d5550000000000001f1f1f1f0307070f0fa0f547d1f55500071b071b83e0f81e0f42d0b41d0b5a669c2c8c2c2c2c4c2c2c2c6c1c1c1c1c2c2d5a80000000000007c7c7c7c0c1c1c3c3e83c2d42c2c2c2c7c2c7c2c2c001c6c1c6cfcfc6c1c1c6c6c1c1c6cfcfc000000007c7c7c7c0c1c1c6c7c7c7c7c7c7c7c7c001c6c1c6cfcfc6c1c1c6c6c1c1c6cfcfc00000729c000023004c00300f02002c04002f272f271b07071b2f272f272f272f2700000f01f0 24 16777215 10 1023
def hc_75_10 : Nat → Nat := unpackHintV5 0x79e0c41d2929e6c61089b070226c0c021afa0126b9c099ae30086b7c021acc02666e08a18442e85bf4a394c24764ec48892332fc40b902902101a40280b8eee23835c0bf0c2928e27b91d88f81ec1e54b1869d1f01510ac8534020114c70831427e07d09000003e8 0x83e0303031303030323aaa03a0303aa07070707a81e07a0213a9eaaaaaaa80e0faa23131323982e680d03030340c2c1c1c1c1ea80c032820300303030303001ca7880300c230f130faa0f27a1f33a031f03030303030f07070707aa270f270f00c0c070707070303a0380c0c1c1c01c070784c0e0f0f81e07a0303a0f0f1313131307070707374dc2cdd370b0fa0f0300c0300c030300303003200c0303c3c3c3c1c1c1c1c3c3c3c3c3c3c3c3c3e83c3c3c3c3c030300c0c0c4c0c4c0c0c0c4c0c8c1c1c1c1c084ea7a0f0fa0303a030f81e07a80c0c3c0c0c0c0c0c0c0c0c0c0c3c3c1c1c1c1c1c1c1c1c3c3c3c4c4c4c4c0d03030340c2c1c1c1c1c3e83c3d0f0b0f43c2c0c0300c0c0c0c0c00729c0c803030030300300c0f0f0f0f030f03030303030f070707070fa0f0f0f0f0f0f0f0f0f0f0f0f0f00c0c0ba743cce9e9c2d0782e9d0329e9e9c2d0f8030707070703030f0f03030303a08aaaa13a9eaaaaa84c4c4c4c1c1c1c1d0b42ea80c0300c0c80703030a0880300c130f130f07070707271f0f0f271f0f0faa270f270f00c0ca0fa0303aaaaa03030303130303031381eaa070707070702aaa84ea7aaaaaa9a982c4c4c4c4c0d03030340c2c1c1c1c1eaa030a00300c0303030303001ca7880300c87eaa0f130f130f031f03030303030f07070707aa270f270f00c0c070707070380c0c0c0e81c1c01c070783e0381e07a0303a0f0f23131323070707073b58c2ced630b0fa0f0300c0300c030300303003200c0303c3c3c3c1c1c1c1c3c3c3c3c3c3c3c3c3e83c3c3c3c3c030300c0c0c4c0c4c0c0c0c8c0c8c1c1c1c1c0a0f0f84ea780e80c0e80c0c3c3e0781ea03030f030303030303030303030f0f07070f1b07070707070707070f0f0f231313230340c0c0d030b070707070fa0f0f43c2c3d0f0b0300c0303030303001ca703200c0c0f00303030300300c0f0f0f0f030f03030303030f070707070fa0f0f0f0f0f0f0f0f0f0f0f0f0f00c0c070707070303030303030b0b504523131323070707074390c3d0e430f55555555550300c03100c0c1400c031108c4c4c8c1c1c1c1c9c7c9c3c9c7c9c3c9c9c9c9d54030310b40c0c0c4c0c0c0c8d5540d40c0d541c1c1c1d50741d4023131323543d940e03030380c3c1c1c1c1d1369d555555540d0b55550300c5040c00c0c0c0c0c00729c0c031108c4c4c8d50f47d40c7c0c0c0c0c0c3c1c1c1c1c9c9c9c9d54030300c0c0c4c0c0c0c4c1c1c1c1c0131313130380c0c0e030f0707070744da750b0b503035030b41d0742d0b540c0c2cec0c0c0c0c0c0c0c0c0c0c2c2c1c1c1c1c1c1c1c1c2c3c2e0b82c2c2c2c2c0c0300c0c0c0c0c00729c0c0300c4030300303013131313031f03030303030f07070707272727270b50b0b0b0b0f0b1f0b0b00c0c0f7fa9c3dfe0b69c030707070703030b0b03030303504513131313070707079fc3dfe0f5544d555555540c0300c0c101ca703030500300c441313131307070707271f270f271f270f272727275500c0c50b503035555503030303130303031341d550707070707019550f131313130380c0c0e030f0707070755551369d55555555030500300c0303030303001ca70300c4451f335550f2713131313031f03030303030f07070707272727275500c0c070707070340c0c0c0d41c1c01c070723131323070707076398c3d8e630f42d0341d075030350b0b42d0b0300c0300c03030030300300c03108c4c4c8c1c1c1c1c9c7c9c3c9c7c9c3c9c9c9c9c2d42c030300c0c0c4c0c0c0c8c1c1c1c1c0231313230380c0c0e030f0707070750b0b44da740d40c0d40c0c2c2d0741d0b42d503030b030303030303030303030b0b07070b1b07070707070707070b0f0b82e0b0b0b0b0b0300c0303030303001ca70300c03100c0c0b003030303023131323031f03030303030f07070707272727270b50b0b0b0b0b0f270b0b1f330b0b00c0c070707073b23471347133b23504583e0f81e07a0303a0b0b55555555550300c03100c0c1400c8440f0f0f0f070707070f0f0f0f0f0f0f0f0fa0f5500c0c030303130303032307070707020f83e80c0e80c3e0781d23544d5035550340d5507541d50b55555550342d559a755540c0300c0c0c0c0c00729c0c85040c1103c3c3c3c0c3c0c0c0c0c0c3c1c1c1c1c3e83d50f43d554030301c1c1c1e2c8e2c4e2c4e2c8e822aaaa96a690b42d0741d40c0d42c2da680c0300c803030a08803109c3c9c3c1c1c1c1c9c7c3c3c9c7c3c3ea82d42c030300c0c0c4c0c0c0c8c1c1c1c1c0aaaaaaaa42d0b503035030b41d07669d6a23a84ea03aaa0380eaa07a81e9582e0300c0303030303001ca788031282030270f270f031f03030303030f07070707aa0b50ba83e1fa00c0c3b1323a707070707aaaa3b23137f133b235045aaaa555555655550300c0303040729e200c0c141109c3c9c3c1c1c1c1ea89c7c3c3c9c7c3c3d54030300c0c0c4c0c0c0c8c1c1c1c1c0544d5235540d035540d541d507aaaaaaaa5955555555555669c0c0300c0c0c0c0c00729d030508844270f270f031f03030303030f0707070751f335550f27aa5500c0c070707077323731373137323070700701c1e0f83e0781e80da542d0b41d075039699030300c0300c030300303003200c40f0f0f0f070707070f0f0f0f0f0f0f0f0fa0f0b50b00c0c030303130303032307070707020f83e80c0e80c3e0781d0b42d0350303503030b0b41d075a669c2c8c2c2c2c4c2c2c0c0c2c0c0c0c0c0c0c0c0c0c0c2c2c1c1c1c1c1c1c1c1d5a80c0300c0c0c0c0c00729c0c803100c0c0b00303030300f0f0f0f030f03030303030f070707070fa0f0b50b0b0b0b0f0b0f0b0b00c0c 26 67108863 11 2047
def hc_75_11 : Nat → Nat := unpackHintV5 0x8f58a7a1b544282fc7b1f662b278f8941c643b46c949f9a3b1d464689098092225a54ba15a61de523c8b937c22647f8bf11141d43ff48b8e852f03658778c6b2562d608989ca31c23b06f07e720a1c246f060420a14e46584382020cf07e01dc2c0044c648000226 0x140c0c0c0c0d0713071b0707007070b08c4c4c8cfe570f3f95c3c6c1c1c6d0b40d42c2d40c0d0742d0b42c0c0300c0c00c0c00c07030300c0300c423131323331f270f331f270f1b07071b332733270b50b00c0c0713071b0323030303130303008c4c4c8c6c1c1c6c0e030f0380c0d42c2d1369d0742d40c2d40c0d0b42d50b1b0b1b070707070b070b0b0303030303030b0b03030b030303030b0f0b82e0b0b0b0b0b0300c01ca7030300303030300c03100c0c00c0c08c4c4c8c6c1c1c6c0c0c0c3c0c7c0c0ccc9ccc9c2d42c2c2c2c2c3c9c2c2c7ccc2c2c03030ec8d1c4d1c4cec8c1c6c1c6d41520f83e82c2e80c0e0783d55555555540c031400c0c100c0321103c3c3c3c3c3c3c3c3c3c3c3c3c1c1c3c3e83d54030301c6c1c6c0c8c0c0c0c4c0c0c083e0f81e0fa030fa030348d513546d507540d035540d5542d55555555669d5550300c01ca703030030303032141030440f0f0f0f0f07070f0303030f030f03030fa0f543d0f55500c0c5723571357135723071b071b0707007070b20f83e9680d81e0f42d0b5a50390742d9030300c03030030300301c0c0c03200c40f0f0f0f0f0f0f0f0f0f0f0f0f07070f0fa0f0b50b00c0c071b071b0323030303130303020f83e0783e80c3e80c0d0b42d0742d40c2d40c0d699a70b230b0b0b130b0b0b1b070707070b0b0303030303030b0b03030b0303030356a0300c01ca70303003030303200c403030030300f0f0f0f0f07070f0303030f030f03030fa0f0b50b0b0b0b0f0b0f0b0b00c0c071b071b032303030313030300fcfc6c1c1c6c0e030f0380c0c6c1c1c6c0d030b0340c0cfcfc0c0300729c0c0c00c0c0c0c0300c030cc9ccc9c6c1c1c6c0c0c0c3c0c7c0c0ccc9ccc9ccc9ccc9c030303c3c0001c1c1c1ea80c0e8a80282a88c4c4c8ced4b0b3b52c2c1c1c1c1ea80000000000008c3c4c3c9c7c3c3c9c7c3c3c1c1c1c1ea89c3c9c3c020f81c1c1c1ea0781ea13a9eaaaaa23131323982e681c1c1c1ea80000000729c00000023004c0880080000c202002c0400230f130faa0f27a1f33a07070707aa270f270f00003c1f007070707883e0781c02801c1c1c0c0c0c1c1c3c3c0004c4c4c4c1c1c1c1c3e83cdd370b374dc2c0000000000003c3c3c3c1c1c1c1c3e83c3c3c3c3c3c3c3c3c3c3c3c3c001c1c1c1e13a9e83c3e0781ea07070707070707070f0f0f13131313070707070fa0f0f43c2c3d0f0b0001ca7000000000004c013000c03c0800f03c000f0000b010003c3c3c3c1c1c1c1c3e83c3c3c3c3c3c3c3c3c3c3c3c3c0000f03c03c3c0000c0eaa81c1c1c1e80028aa92d4b0b4b52c2c4c4c4c4c1c1c1c1ea800000007000000271f0f0f271f0f0f130f130f07070707aa270f270f00a0f81eaa0707070707aaaa13a9eaa6a60b1313131307070707aa00000001ca70000002000880013004c003080800b010021faa83c4c3c4c3c1c1c1c1ea89c3c9c3c0000f07c01c1c1c1e0f881e07a00007070703030307070f0f00023131323070707070fa0f3b58c2ced630b00000000000000f0f0f0f070707070fa0f0f0f0f0f0f0f0f0f0f0f0f0f0007070707a0f0f84ea781e07a81c1c1c1c1c1c1c1c3c3c3c8c4c4c8c1c1c1c1c3e83c3d0f0b0f43c2c000729c00000000f00c00023004c00300f02003c0f0003c0002c04000f0f0f0f070707070fa0f0f0f0f0f0f0f0f0f0f0f0f0f00003c0f00b0b000070707075503035231313234390c3d0e430f07070707150050555500000000000023131323271f270f271f270f0707070727272727550042d07070707541d07523131323543d941c1c1c1d1369d555555500000001ca700000008c0130110010000300f0201010008c4c4c8d50f47d41c1c1c1c9c9c9c9d540000f07c01c1c1c1c4c4c4c4c1c1c1c1d1369d42c2d0741d0b42d507070707070707070b0f0b82e0b0b0b0b0b0001ca7000000000004c013000c03c0800b01002c0b0002c3b00004c4c4c4c1c1c1c1c9c9c9c9c2d42c2c2c2c3c2c7c2c2c0000f07c02c2c0000c0d5541c1c1c1d7e5f0f5f97c3c4c4c4c4c1c1c1c1d400145555400000007000000271f270f271f270f131313130707070727272727550050b50707555071b0707070765543c4c4c4c4c1c1c1c1d55544da7555500000001ca70000001000440013004c00300f02010100147ccd5543c9c4c4c4c4c1c1c1c1c9c9c9c9d540000f07c01c1c1c1c8c4c4c8c1c1c1c1d0b441d0742d0b50000707070303030707630f6398e630f0b0b00000000000000002313132307070707272727270b50b271f270f271f270f0007070707231313230707070750b0b44da741d0742d0b541c1c1c1c1c1c1c1c2c3c2e0b82c2c2c2c2c000729c0000000000b00c023004c00300f02002c0400b02c000b00002313132307070707272727270b50b0b0b0b0b0f270b0b1f330b0b00003c1f00707070783e0f81e073b23471347133b2355030350b0b00055551500500000000000000f0f0f0f070707070fa0f0f0f0f0f0f0f0f0f55000707070783e0f81e0748d513541d507542d5555669d5550001ca7000000000008c013000c03c08044004001010003c3c3c3c1c1c1c1c3e83d50f43d5540000f03c01c1c1c1eaaa90b42d0741d192c8d2c4d2c4d2c8ea80c0e801402c2c0000000000000009c3c9c3c1c1c1c1ea82d42c9c7c3c3c9c7c3c3c001c1c1c1eaaa90b42d0741d9a75a88ea13a81ea07a560b8000729c000000000023004c003080800b010220020000270f270f07070707aa0b50ba83e1fa00003c1f0070707073b234b134b133b235030355aaaaa00055555000510001c00000000009c3c9c3c1c1c1c1c9c7c3c3c9c7c3c3ea954001c1c1c1d513548d50741d50746eaaa96555555559a70001ca7000000000008c013000c10004400808040400270f270f0707070751f335550f27aa5500003c1f00707070783e0f81e0742d0b41d0764732367137313672307070703030307075000a0000000000000000f0f0f0f070707070fa0f0b50b0f0f0f0f0f0f0f0f000707070783e0f81e0742d0b41d075a669c2c8c2c2c2c4c2c2c1c1c1c1c1c1c1c1d5a8000729c0000000000b00c023004c00300f02002c0400b02c000b00000f0f0f0f070707070fa0f0b50b0b0b0b0f0b0f0b0b00003c0f00707070707070707070707070001ca700000008c013000c03c0800b010009c9c9c9c1c1c1c1c9c9c9c9c9c9c9c9c0000f07c01c1c1c1c0c0c0c0c0c0c3c3e822aaaaaaaaa88c4c4c8c1c1c1c1ced630b3b58c2ea80c0300c803030a0880300c230f130f07070707271f0f0f271f0f0faa270f270f00c0c 26 67108863 11 2047
def hc_75_12 : Nat → Nat := unpackHintV5 0x855cc520442267b0cc09eb20227630931c122f46cc8701a2022468400819f902e63e080979c2b85ba05a162218c542c8b943b1a04c509391fd22e43988b90321683ce47c8ea512837286d8c8328e2a0900893329e1c890886112221274ba029840a061489800030a 0x1c4c1c6e0f83e81c1e07a9c3c8c3c3c3c4c3c3ea070707231313231b07071b0fa0f0f43c2c3d0f0b0004ca7000000000000c06c007003c0800f03c000f0000b010003c3c3c3c3c1c1c3c3e83c3c3c3c3c3cac3c3c3ccc3c3c3c3c3c3c00003c3c03c01c1c1c1c8c4c4c8c1c1c1c1d0b42d450742d0b03030707070707030050570f5795e570f0b0b0000000000000002313132307070707272727270b50b271f270f271f270f0007070707231313230707070742d0b41da75070742d0b0723070707130707541c3c1e0781c1c1c2c1c001329c000000000003007001c00f02002c0b011001c070001c00008c4c4c8c1c1c1c1c9c9c9c9c2d42c1c1c1c3c1c7c1c1c00003c9c07c29cfc3ea70713071b231313231b07071b42d0b5070741da710b42c0c0c2c2c2c2c2c0d40003cfe3fa8c3c1c1c000001329c0000000000231313231b07071b2f272f270b50b2f1f270f2f1f270f000713071b231313231b07071b42d0b5070741da742d0b0b230b0b0b130b0b542c3c2e0b82c2c1c1c1c001329c00000000000301b001c00f02002c0400b02c000b0000231313231b07071b2f272f270b50b0b0b0b0f0b1f0b0b00000f2701f023131323aaaa42d0b42d0b5160303aaa371b37073707371b00500b0b000000000000000230f130f2f0f2f0faa0b50b2f1f0f0f2f1f0f0f0023131323aaaa42d0b42d0b669d6a23a84ea1ba81e9582e0004ca7000000000000c06c0070202002c0b0110220020000230f130f2f0f2f0faa0b50ba83e1fa00000f0f01f0a7671b076a71b07670308c4c4c8e0f83e0f83d0b42d0b42d699a700c0c2c2c2c2c2c0c6d9c1c1d9c6d40028000004c00000000000f0f0f0f0f0f0f0f0fa0f0b50b0f0f0f0f0f0f0f0f002313132383e0f83e0f42d0b42d0b5a669c2c8c2c2c2c4c2c2c2c6c2c1c2c1c2c2d5a8001329c00000000000301b001c00f02002c0400b02c000b00000f0f0f0f0f0f0f0f0fa0f0b50b0b0b0b0f0b0f0b0b00000f0f00f0231313230f0f0f0f0f0f0f0f23131323272727270f0f0f0f000000000f0f0f030f0f0f0f0f0f0f0f0f0f0f0f000713071b88ea13a83eaa81ea7aaa88c4c4c8c6c1c1c6e60b9aaa000000000000030f131f1b07071ba87e1faaa1f1f1f1f000707070783e0f81ea7a07070723070707130707a81c3c1c8c4c4c8c1c1c1c1c3e83c1d070b0741c1c0000000000000c3c3c3c1c1c1c1c3e83c1c1c1c7c1c7c1c1c7c7c7c7c02a13a88c1c1c1c1e81eaaaaa81ea7231313239a982c1c1c1c1ea80000000000000c3c4c7e87c7eaa87cbc1c1c1c1ea87c7c7c7c001c4c1c6e0f83e81c1e07a9c3c8c3c3c3c4c3c3ea070707231313231b07071b0fa0f0f43c2c3d0f0b000000000000030f0f0f1b07071b0fa0f0f0f0f0f1f2f0f0f1f1f0f0f1f1f1f1f0007070707231313230707070742d0b41da75070742d0b0723070707130707541c3c1e0781c1c1c2c1c0000000000000c4c4c7c1c1c1c1c7c7c7c7c2d42c1c1c1c7c1c7c1c1c001c4c1c6c8c4c4c8c6c1c1c6d0b42d41c1d0769d0b42c2c8c2c2c2c4c2c2d50b0f0b82e0b0b0707070000000000000313131f1b07071b1f1f1f1f0b50b0b0b0b1f0b1f0b0b0023131323aaaa42d0b42d0b669d6a23a84ea1ba81e9582e000000000000030f131f1f1f1f1faa0b50ba87e1fa002313132383e0f83e0f42d0b42d0b5a669c2c8c2c2c2c4c2c2c2c6c2c1c2c1c2c2d5a80000000000000c3c3c3c7c7c7c7c3e83c2d42c2c2c2c7c2c7c2c2c008c4c4c8c8c4c4c8c8c4c4c8cecececec000000000c4c4c7c7c7c7c7c7c7c7c7c7c7c7c7c008c4c4c8c8c4c4c8c8c4c4c8cecececec001329c0000000301b001c00f02002c0400231313232f2b2f2b2f2b2f2b2f2b2f2b00000f01f0030303a80c0c1c4c1c4c1c1c01c1c3c80e0fa0f0fa030381e0f13131313374dc2cdd370b1b07071b0fa0f0300c03030030300300c03200c0303c3c3c3c3c3c3c3c3c3c3c3c3c1c1c3c3e83c3c3c3c3c030301c4c1c4c0c4c0c0c0c4c0c0c084ea7a0f0f81e0fa030fa0303a83c6c1c1c1c1c3c3c0c0c0c0c0c0c3c3c0c0c3c0c0c0c0c3c3c3c4c4c4c4c6c1c1c6c0d030b0340c0c3e83c3d0f0b0f43c2c0c0300729c0c0c00c0c0c0c803030030300300c0f0f0f0f0f07070f0303030f030f03030fa0f0f0f0f0f0f0f0f0f0f0f0f0f00c0ca030303030381c4c1c6c1c1c01c1c3c83e03a0f0fa030381e0f231313233b55c2ced570b1b07071b0fa0f0300c03030030300301c0c0c03200c0303c3c3c3c3c3c3c3c3c3c3c3c3c1c1c3c3e83c3c3c3c3c030301c4c1c6c0c8c0c0c0c4c0c0c0a0f0f84ea781e0fa030fa0303a83c6c3c6c1c1c1c1c3c1c3c3c0c0c0c0c0c0c3c3c0c0c3c0c0c0c0c3c3c3c8c4c4c8c6c1c1c6c0d030b0340c0c3e83c3d0f0b0f43c2c0c0300729c0c0c00c0c0c0c803030030300300c0f0f0f0f0f07070f0303030f030f03030fa0f0f0f0f0f0f0f0f0f0f0f0f0f00c0c03030b0b0303030350540713071b3f90c3cfe430f231313231b07071b555555555550030300300c40300c03110cc7c9c3ccc7c9c3c8c4c4c8c6c1c1c6ccc9ccc9d54030310b41c4c1c6d51b41d40c8c0c0c0c4c0c0d5540c0d40d54023131323543d946c1c1c6c0e030f0380c0d1369d555555555550300c5040c00729c0c0c00c0c0c0c031108c4c4c8d50f47d46c1c1c6c0c0c0c3c0c7c0c0ccc9ccc9d54030301c4c1c4c0c4c0c0c0c4c0c0c0131313131b07071b0380c3c0e030344da750b0b41d0b5030b5030342d0b542c6c1c1c1c1c2c2c0c0c0c0c0c0c2c2c0c0c2cec0c0c0c0c2c3c2e0b82c2c2c2c2c0c0300729c0c0c00c0c0c0c0300c40303003030131313131b07071b0303030f031f03032b272b270b50b0b0b0b0f0b1f0b0b00c0c03030b0b03030303071307135450131313133f93c3cfe4f0f1b07071b55555555550300c0303050400c00c031104c4c4c4cac7c9c3cac7c9c3c6c1c1c6cac9cac9d540303142d075546c1c4c1c4d40d555540c0c0c4c0c0c0c4c0c0c065543c4c4c4c4c6c1c1c6c0e030f0380c0d55544da7555555555030305100300c01ca7030300303030300c4451f335550f27131313131b07071b0303030f031f03032b272b275500c0c 26 67108863 11 2047
def hc_75_13 : Nat → Nat := unpackHintV5 0xe281886c04a7b1e08458df022c6d804634804b17e04d8bb008c5b804629009af2045161c2e8a6a9474a691da3443e10492b27a98f637c0b19bc0040cff1c25e013f2a809011587d077d25e3470ef159c9387c46142e81f40cf94906180c8264150000264 0xc1c0c0c0c0c0c6c1c4c1c4d035550340d5513544d50b40e03030380c3c4c4c4c4c6c1c1c6d50f65555540d0b5541da75555540c0c0c0c0c01329c0c031410300300c44031f03030303030f131313131b07071b550f2b51f3352b272b275500c0c070700701c1c1c1c1c1d40c0c0d0303131313134390c3d0e430f0707070742d0b5030350b0b41c0d070742d0b0300c03030030300300c0300c03104c4c4c4c9c7c9c3c9c7c9c3c1c1c1c1c9c9c9c9c2d42c03030003030707030303030303071b070707070380c0c0e030f1313131307070707503035030b42d0b41da75070742d0b0303070303030303030303030307070713070707130707541c3c1e0781c1c1c2c1c0c0c0c0c0c01329c0c0300c0300c40303003030031f03030303030f1313131307070707272727270b50b0707070f071f070700c0c0fa9c9cce9c3ea71343ea70329e9c3ea70b4030707070750450303070703030303131313130707070783e0f555550769d5555540c0c4130300c03030500300c441313131307070707271f270f271f270f272727275500c0c01550340d55035513544c0c1c0c0c0c0c0c1c1c1c1c1d41c0e03030380c3c4c4c4c4d9550f0707070755555555550769d540c0c0c0c0c01329d030500300c0300c44031f03030303030f1313131347d550f07070707272727275500c0c0b0b00b02c2c1c4c1c4c0c0c0d03035131313133f90c3cfe430f1b07071b42d0b503035070741d0342d0b0300c03030030300300c0300c03104c4c4c4cac7c9c3cac7c9c3c6c1c1c6cac9cac9c2d42c030300030307070303030303031b1b071307130380c0c0e030f131313131b07071b40d40c0d40c0c2c2d0b42d41c1d0769d0b42c0c0c2c0c0c0c0c0c0c0c0c0c0c2c2c2c4c2c8c2c2c2c4c2c4c2c2d50b0f0b82e0b0b0707070303030303004ca70300c0300c03100c0c0b0030303030031f03030303030f131313131b07071b2b272b270b50b0b0b0b0f0b1f0b0b00c0c5045131313134707471b4707471b83e0fa0303a0b0b83e0f5555555555503100c0c1400c0300c8440f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fa0f5500c0c000c1c0c0c0c0c0c6c4c4c4c4e80c0e80c3e0f83e0f83d035550340d5513544d51b541d50b5555555559a755540c0c0c0c0c01329c0c0300c85040c1100c3c0c0c0c0c0c3c3c3c3c3c3c3c3c3c3e83d50f43d5540303282284c4c4c4d0c1cfc6d0c1cfc6ea96a6aa90b42d40c0d42c2d0b42d980c803030a00300c8803104c3c4c3cac7c3c3cac7c3c3cac3cac3ea82d42c030300030703030303031b13131313aaaa80e0faaaa503035030b42d0b42d0b669d6a03aaa0380eaa13a84ea1ba81e9582e0303030303004ca70300c88031282030031f03030303030f130f130f2b0f2b0faa0b50ba83e1fa00c0c3f071ba713131313aaaa50453f1b0783073f1baaaa555555555550303041329c0c032200c0c141104c3c4c3cac3cac3ea8ac7c3c3cac7c3c3d54030300030703030303031b131313135540d035540d544d513541d51baaaaaaaa5955555555555669c0c0c0c0c0c01329c0c031030508844031f03030303030f130f130f2b0f2b0f51f335550f2baa5500c0c0b0b00b02c2c4c4c4c4d0c1d0c6d0c1d0c6e0f83e80da583e0f42d0b5039690b42d9030300c03030030300300c03200c40f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fa0f0b50b00c0c000c1c0c0c0c0c0c6c4c4c4c4e03a0303a03030f0f83e0f83e0f503035030b42d0b42d0b5a669c0c0c2c0c0c0c0c0c0c0c0c0c0c2c2c2c4c2c2c2c4c2c2c2c6c2c1c2c1c2c2d5a80c0c0c0c0c01329c0c0300c803100c0c0b0030303030030f03030303030f0f0f0f0f0f0f0f0f0fa0f0b50b0b0b0b0f0b0f0b0b00c0c000c1c0c0c0c0c0c6c4c4c4c4c0e03030380c3c4c4c4c4c0d03030340c2c4c4c4c4c0c0c0c0c0c01329c0c0300c0300c0300c7c0c0c0c0c0c3c4c4c4c4cacacacacacacacacacacacac030301c4c1c6c0c0eaa83c3c002a881ea00a0231313231b07071b374dc2cdd370baa000000000000230f130f1b07070f2f1f0f0f2f1f0f0faa2f0f2f0f000713071b88ea13a83eaa81ea7aaa88c4c4c8c6c1c1c6e60b9aaa0004ca7000000000000c06c1b001c0702200200080800b010008c3c4c3c6c1c1c3ea0f87eaa8bc3cbc3c00003c3c07c01c1c1c1e0f83e07a9e81c1c1c8c1c1c1c4c1c1ea070f0723131323070707070fa0f0741c2c1d07070004ca7000000000000c01c007003c0f022001c070001c3f0002c04000f0f0f0f070707070fa0f0707070f070f07070f0f0f0f00000f0f00f0aaa0303070707070707000aaa000a223131323374dc2cdd370b07070707aa000000000000230f130f27371f1f0f0f271f0f270f0f07070707aa270f270f00a84e13a88e2307070707a07aaaaaa07a9c8c4c4c8e6a60b07070707aa0004ca7200c0000000000030800220001c1b001c070203c08800b010008c3c4c3e87cceaa83cac1c1c1c1ea89c3c9c3c00003c3c07c29cec2da70f9781c1ea7030f0f0f8007003c3c3cee5cedec04ca7000713071b83e0fa070781ea700c0c3c3c3c3c3c0e80001c1c0008c4c4c8c6c1c1c6c3e83ced0b3b5ec2c001329c00000000000f0f0f0f0f07070f0fa0f0f0f0f0f0f0f0f0f1f0f0f0f0f0f0f00 25 33554431 11 2047
def hc_75_14 : Nat → Nat := unpackHintV5 0x8a00bc21911de8198959f532267714c71cdb1d46ee8909aa922264d4ba18461de5cbc8b961c2265278bf13c01bc4aec8291dd1bc436082900d1963c30808e101f832c0b00be71922b588889582fc1d4d02874601a1cbc0b86132381254bf034e28e044d1d8000226 0x707070783e0f81ea7a07070713070707130707a81c3c1c4c4c4c4c1c1c1c1c3e83c1d070b0741c1c1329c00000000000003007001c00f02001c070001c3f0002c04000f0f0f0f070707070fa0f0707070f070f07070f0f0f0f00003c0f0a0303aa070707070707000aaa000a2131313134b52c2d2d4b0b07070707aa04c0000000000004c3c4c3c9c7c3c3c9c7c3c3c1c1c1c1ea89c3c9c3c02a1384ea1388c1c1c1c1e81eaaaaa81ea7131313139a982c1c1c1c1ea81329c000000000000030800220001c0070202002c0400130f130fa1f33aaa0f2b07070707aa270f270f00003c1f00713071383e0f81e03c3c3c0c0c0c3c3e80001c1c0004c4c4c4c6c1c1c6c3e83d3d4f0b4f53c2c00000000000003c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c3c3c3c3c001c4c1c4e0f83e81c1e07a9c3c4c3c3c3c4c3c3ea070707131313131b07071b0fa0f0f43c2c3d0f0b04ca700000000003c0300000c06c007003c0800f03c000f0000b010003c3c3c3c3c1c1c3c3e83c3c3c3c3c3cac3c3c3ccc3c3c3c3c3c3c0000f03c01c4c1c4d540c0d42c2c0004c4c4c4c6c1c1c6cfe4f0f3f93c3d54540141540000000000004c4c4c4c6c1c1c6cac7c9c3cac7c9c3cac9cac9d54001c4c1c4d13544d50b44c4c4c4c6c1c1c6d50f655541da75555541329c0000000000000301b001c0440040003c08040400131313131b07071b550f2b51f3352b272b275500003c1f007070707131313130707070742d0b441d0b42c1c1c1c0c0c0c1c1c01410c3d0e4390c3c2c2c0000000000000004c4c4c4c1c1c1c1c9c9c9c9c2d42c9c7c9c3c9c7c9c3c001c1c1c1c4c4c4c4c1c1c1c1d0b42d0769d41c1d0b42c1c4c1c1c1c4c1c1d5070f0781e0707070b0704ca700000000000000c01c007003c0800b01001c070001c00004c4c4c4c1c1c1c1c9c9c9c9c2d42c1c1c1c3c1c7c1c1c0000f07c140c0d541c1c1c1c1c1c0004c4c4c4d5e570f5795c3c1c1c1c1d55400145541300000000000013131313271f270f271f270f07070707272727275500544d513070707075071313131365543c1c1c1c1d5555541da75504ca700000000000000c1000440007001c00f0201010004c4c4c4d1f5543c1c1c1c1c9c9c9c9d540000f07c01c4c1c4c4c4c4c4c6c1c1c6d0b42d07442d0b0b0b0b0303030b0b5000430f3f8fe430f07070000000000000000131313131b07071b2b272b270b50b2b1f270f2b1f270f0007130713131313131b07071b42d0b5070741da742d0b0b130b0b0b130b0b542c3c2e0b82c2c1c1c1c1329c000000000000b00c00301b001c00f02002c0400b02c000b0000131313131b07071b2b272b270b50b0b0b0b0f0b1f0b0b00003c1f01313131383e0f83e0f5503035471b47074707471b0b0b00055551500500000000000000f0f0f0f0f0f0f0f0fa0f0f0f0f0f0f0f0f0f55001313131383e0f83e0f44d513546d507542d5555669d55504ca700000000000000c06c007003c08044004001010003c3c3c3c3c3c3c3c3e83d50f43d5540000f03c04c4c4c4eaaa90b42d0b42d1aa80c0e8fc6d0c1d0c1cfc6c01402c2c0000000000000004c3c4c3cac3cac3ea82d42cac7c3c3cac7c3c3c004c4c4c4eaaa90b42d0b42d9a75a84ea13a86ea07a560b81329c0000000000000301b001c080800b010220020000130f130f2b0f2b0faa0b50ba83e1fa00003c1f01313131350303553f1b4b074b073f1baaaaa000555550005104c0000000000004c3c4c3cac3cac3cac7c3c3cac7c3c3ea954004c4c4c4d51344d51348d507546eaaa96555555559a704ca700000000000000c06c007010004400808040400130f130f2b0f2b0f51f335550f2baa5500003c1f01313131383e0f83e0f42d0b42d0b640b0b0b0303030b0b431b43074307431b5000a0000000000000000f0f0f0f0f0f0f0f0fa0f0b50b0f0f0f0f0f0f0f0f001313131383e0f83e0f42d0b42d0b5a669c2c4c2c2c2c4c2c2c2c6c2c1c2c1c2c2d5a81329c000000000000b00c00301b001c00f02002c0400b02c000b00000f0f0f0f0f0f0f0f0fa0f0b50b0b0b0b0f0b0f0b0b00003c0f013131313131313131313131304ca70000000000c06c007003c0800b010004c4c4c4cacacacacacacacacacacacac0000f07c282281c4c1c4c0c0c0c0c0c0c3c3eaaaaaaa84c4c4c4d3d4f0b4f53c2c6c1c1c6ea80c803030a00300c880300c130f130f2b1f0f0f2b1f0f0f1b07070faa2b0f2b0f00c0c000c1c0c0c0c0c0c6c1c4c1c4e03aaa0380eaa13a84ea0faaaaa0383eaa07a9eaaa0340c0c0d030b131313131b07071b982e6aa80c0c0c0c0c01329c0c03282030880300c031f03030303030f130f130f1b07070fa83e1faaa2b0f2b0f00c0c000c1c0c0c0c0c0c1c1c1c1c1e80c0e80c3e0f83e07a9e81c1c0c0c1cfc0c0c0c0c0c0c0c0c0c0c1c1c1c4c1c1c1c4c1c1ea070f070340c0c0d030b13131313070707070fa0f0741c2c1d07070303030303004ca70300c03200c0c00c0c00c0300c3c0c0c0c0c0c3c3c3c3c3c1c1c1c1c3e83c1c1c1c3c1c3c1c1c3c3c3c3c030302e0da70b8343ea700c1c1c1c1e82280c0c1c1c0c0c0c0eaaaa07aaaa131313130707070760c2e0d0baa0303081329c0c0300c0c282200c0304c3c4c3c1c1c1c1c9c7c3c3c9c7c3c3ea89c3c9c3c030300aa80e03aa80ea84ea13030703030303030707070707a07aaaaaaaaaa07a9c0d03030340c2c4c4c4c4e6a60b07070707aa0303030303004ca780c2800c032200c0300c7c0c0c0c0c0c3c4c3c4c3e87cceaa83cac1c1c1c1ea89c3c9c3c030303c3c03c0f0f0713071303030380c0ea0f83e80c0e81c1e0780c4c4c4c4d3d4f0b4f53c2c6c1c1c6c3e83c0c0300c0c00c0c00c0300c80300c0f0f0f0f0f0f0f0f0f0f0f0f0f07070f0fa0f0f0f0f0f00c0c000c1c0c0c0c0c0c6c1c4c1c4e03a0303a03030f0f83e0fa070781ea703030f030303030303030303030f0f0f130f230f0f0f130f130f0fa81c1c1c0d03030340c2c4c4c4c4c6c1c1c6c3e83c3d0f0b0f43c2c0c0c0c0c0c01329c0c0300c8030303c00c0c0c0c00c0300c3c0c0c0c0c0c3c3c3c3c3c3c1c1c3c3e83c3c3c3c3c3cac3c3c3ccc3c3c3c3c3c3c0303141141c4c1c4c0c0c0c0c0c0c2c2c4c4c4c4cfe4f0f3f93c3c6c1c1c6d555555555540c403030500300c0300c44131313132b1f270f2b1f270f1b07071b2b272b275500c0c 26 67108863 11 2047
def hc_75_15 : Nat → Nat := unpackHintV5 0x8d6508a21228e7f5d1d9fc202a7ee8041fa502a7e60069f900107e20041f7102e7878a99ce32766b590699cb21662e88897462e8550502942e2264aa4c2915a29e3ce5108df228e2fc5008aa229e224508879b1ec1908ac851a2500d00ed020127e045c75000022e 0x71307a707071313070707131b1383e0f81e0fa0f0fa0f0f42d0b41d0b50b0b50b0b5a669c2c4c2c2c2c4c2c2c2c6c2c6c1c1c1c1c2c1c2c2c2c4c2c4c2c2c2c2c2c4c2c2c2c2c2d5a84c4c4c4c6c1c1c6c4c0c4c13031303e83c2d42c2c0c2c0b030b03c3c3c3c3c1c1c3c3c3c3c3c3c3c3c3c3e83c2d42c2c2c2c3c2c3c2c2c3c3c3c3c4c4c2c2c2c2c2c2c1c1c1c1c1c1c1c1c1c1c1c1e81da583e0f81e075079690b42d0741d90743034310c0d0c13131313070707070fa0f0b50b0f0f0f0f0f0f0f0f0f0f0f0f070707070fa0f0b50b0f0f0f0f07071307070707070707071307a781e81c1e81c1c3c3e0f83e0781d0750707507070b0b42d0b41d075a669c1c1c2c1c1c1c1c1c1c1c1c1c1c2c2c2c4c2c8c2c2c2c4c2c4c2c2c1c1c2c6c1c1c1c1c1c1c1c1d5a81c0c1c07030704c4c4c4c1c1c1c1c3e83c2d42c2c0c2c0b030b01c3c1c1c1c1c1c3c3c3c3c3c1c1c1c1c3e83c2d42c2c2c2c3c2c3c2c2c3c3c3c3e9ca7030f37a7a7a7a700c3cde9ca703a7a7a7a7a7a700c3e0b41c1c4c4c1c4c1e9c2c1c1c2c2c2c2c2c1c4c4c1c1c1c1c2c2e0f83e0783e9683d42d0b41d0b5a50b9699a70b231313231b07071b0300c0fa0f0b50b0f0f0f0f0f07070f0f0f0f0f0f0f0f0f0fa0f0b50b0f0f0f0f0713070b070f0f0f1307070f83e0f81e0f83e0f42d0b41d0b42d0b5a669c2c8c2c2c2c4c2c2c2c6c1c1c1c1c2c2c2c7c2c2c2c7c2c2d5a88c4c4c8c6c1c1c6c7c7c7c7c3e83c2d42c2c0c2c0b030b01c1c4c4c1c4c1e9c1c1c1c4c4c4e0f83e0783e83c3e83c3d0b42d0742d42c2d42c2d699a70b230b0b0b130b0b0b1b070707070b0b0b1b0b1b0b0b0b0b0b1b0b0b0b0b0b56a231313231b07071b1b031b06c0c6c0fa0f0b50b0b030b02c0c2c0f0f0f0f0f07070f0f0f0f0f0f0f0f1b0f0f0f0fa0f0b50b0b0b0b0f0b0f0b0b0f0f0f0f83e0f83e0f42d0b42d0b5a669c2c8c2c2c2c4c2c2c2c6c2c1c2c1c2c2d5a83e83c2d42c2c0c2c0b030b03c3c3c3c3c3c3c3c3e83c2d42c2c2c2c3c2c3c2c2c3c3c3c3e82a00c0c3c3c0c0c0c0c1c4c1c6eaaaaaaa8dd370b374dc2c8c4c4c8c6c1c1c6eaa800c0c200c0300c880300c331f0f0f331f0f0f230f130f1b07070faa330f330f00c0c001c4c1c6c0c0c0c6c0c1c0c0e23a84ea0380eaa03aaa0faaaaaaa07a9eaaa231313230340c2c0d03031b07071b982e6aa81329c0c0c00c0c0c0c03282030880300c230f130f0303030f031f03031b07070fa83e1faaa330f330f00c0c001c1c1c1c0c0c0c1c0c1c0c0e0f83e80c3e80c0e07a9e81c1c1c8c1c1c1c4c1c1c0c0c0c0c0c0c1c1c0c0c1cfc0c0c0c0ea070f07231313230340c2c0d0303070707070fa0f0741c2c1d070704ca7030300303030300c03200c0c00c0c00c0303c3c3c3c0c0c0c3c0c3c0c0c1c1c1c1c3e83c1c1c1c3c1c3c1c1c3c3c3c3c030301c1c1c1e2a800c0c1c1c0c0c0c0eaaaaaaa88c4c4c8c1c1c1c1cdd370b374dc2eaa00300300c03030a0880300c230f130f07070707271f0f0f271f0f0faa270f270f00c0c02a13a88eaa03aaa0380c1c1c1c1c0c0c0c1c0c1c0c0e81eaaaaaaaaa81ea7231313230340c2c0d03039a982c1c1c1c1ea81329c0c0c00c0c0e80c0c28800c032200c0308c3c4c3c0c0c0c3c0c7c0c0e87cceaa83cac1c1c1c1ea89c3c9c3c030303c3c03c3c3c0303a03030381c4c1c6e81c1e80c0e0f83e0780ced6b0b3b5ac2c8c4c4c8c6c1c1c6c3e83c0c0c00c0c00c13030300c0300c80300c0f0f0f0f0f0f0f0f0f0f0f0f0f07070f0fa0f0f0f0f0f00c0c001c4c1c6c0c0c0c6c0c1c0c0e0f83e80c3e80c0e81c1e07a9c3c8c3c8c3c3c3c4c3c4c3c3c0c0c0c0c0c0c3c3c0c0c3c0c0c0c0ea070707231313230340c2c0d03031b07071b0fa0f0f43c2c3d0f0b04ca7030300303030300c03200c0c00c0c00c0303c3c3c3c0c0c0c3c0c3c0c0c3c1c1c3c3e83c3c3c3c3c3cac3c3c3ccc3c3c3c3c3c3c030301c1c01c1c1c0340c0d40c0c1c1c1c1d6e5b0f5b96c3c8c4c4c8c1c1c1c1d42c2d40c0d0b42d0341d0b42c0c0c00c0c00c0300c0300c0300c4271f270f271f270f2313132307070707272727270b50b00c0c001c1c1c1c0c0c0c1c0c1c0c0c8c4c4c8c0e030f0380c0c1c1c1c1d0b42d40c2d40c0d0769d41c1d0b42c1c8c1c1c1c4c1c1c0c0c0c0c0c0c1c1c0c0c1c0c0c0c0d5070f0781e0707070b0704ca7030300303030300c0300c03100c0c00c0c08c4c4c8c0c0c0c3c0c7c0c0c1c1c1c1c9c9c9c9c2d42c1c1c1c3c1c7c1c1c030302c2c02c2c2c0303503030341c4c1c6cfe6b0f3f9ac3c8c4c4c8c6c1c1c6d41c1d40c0d0b42d0740d0b42c0c0c00c0c00c13030300c0300c0300c4331f270f331f270f231313231b07071b332733270b50b00c0c001c4c1c6c0c0c0c6c0c1c0c0c8c4c4c8c0e030f0380c0c6c1c1c6d0b42d40c2d40c0d41c1d0769d0b42c2c8c2c8c2c2c2c4c2c4c2c2c0c0c0c0c0c0c2c2c0c0c2c0c0c0c0d50b0f0b82e0b0b07070704ca7030300303030300c0300c03100c0c00c0c08c4c4c8c0c0c0c3c0c7c0c0c6c1c1c6ccc9ccc9c2d42c2c2c2c3c2c7c2c2c0303282a0dc1cdc6cdc1cdc6c8c4c4c8e696aaaa942c2d40c0d0b42d0b42d9a800c0c200c0300c880310cc7c3c3ccc7c3c3c8c3c4c3ccc3ccc3ea82d42c030300231313230303031b03070303aaaaaaaa42d0b5030b5030342d0b669d6a23a84ea0380eaa03aaa1ba81e9582e04ca7030300303030300c88031282030230f130f0303030f031f0303330f330faa0b50ba83e1fa00c0c0b0b00b0b0b1ac1dac6dac1dac6c8c4c4c8e9680d83e0f83e0f5a50390b42d0b42d90303030030300304c0c0c0300c03200c40f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fa0f0b50b00c0c008c4c4c8c0c0c0c6c0c1c0c0e0f83e80c3e80c0e0f83d0b42d40c2d40c0d0b42d699a70b230b0b0b130b0b0303030303030b0b03030b030303030b1b0b070b070b0b56a04ca7030300303030300c03200c403030030300f0f0f0f0303030f030f03030f0f0f0f0fa0f0b50b0b0b0b0f0b0f0b0b00c0c008c4c4c8c0c0c0c6c0c1c0c0c8c4c4c8c0e030f0380c0c8c4c4c8c0d030b0340c0cecececec1329c0c0c00c0c0c0c0300c0300c0308c4c4c8c0c0c0c3c0c7c0c0cccacccacccacccacccacccac030301c4c1c4ea80c0e83c3c002a8a802804c4c4c4c6c1c1c6d2d4b0b4b52c2ea80000000000004c3c4c3c6c1c1c3cac7c3c3cac7c3c3ea8ac3cac3c001c4c1c4e13a84ea0faaa07a9eaaa131313131b07071b982e6aa81329c0000000000000301b001c08800800202002c0400130f130f1b07070fa83e1faaa2b0f2b0f00003c1f0 26 67108863 11 2047
def hc_75_16 : Nat → Nat := unpackHintV5 0xd4680c6a0006b4aa0ad9022a6b80a0157089fa96e42d3402ee91990d42c8c09fe2304ee62166b797731888695c2604a2018250980d282c0413fc0349d50524e6808271404132c0bc8a31e63a6956195c7b0bae2005531082578a40d80a7829e84400029e 0x29e9cce9e9c33a7a708c2c6c1c3e030b43c1c4c1c6e83c3e13a9c2e0783e82c2c2c2c2e5070707070f43c3ea82c2d0b42d41c1d0769c2d90b5070750b07231313231b07071b0fa0f0300c0b50b0f0f0f0f0f07070f0fa0f0f0f0f0f0f0f0f0f0b50b0f0f0f0f0713071ba0f0f84ea781e0fa83c6c1c1c1c1c3c3c3c3c3d0b42d41c1d0769d90b50b0b50b0b0b230b0b0b130b0b542c3ea82c2c2c3c2c3c2c2c2c2c2c3c2c2c2c2c2c1c1c1c8c4c4c8c6c1c1c6c3e83c3c0c3c0f030f02d42c2c0c2c0b030b03c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c2d42c2c2c2c3c2c3c2c2c3c3c3c3c1c6c1c6cfcfc6c1c1c6d0b42d41c1d0769d0b42c2c8c2c2c2c4c2c2d50b0f0b82e0b0b0707071b07071b3f3f0b50b0b030b02c0c2c532753271b07071b53273f270b50b0b0b0b0f0b1f0b0b532753270741c4d541c1d46c6d5560f83e0783e82c2e83c2d55555555544c4c4c4c6c1c1c6d1c0d1c47034703e83d543c3c3c3c3c1c1c3c3c3c3c3c3c3c3c3c3e83d543c3c3c3c1c4c1e9c1c1c4c4c1c1c1c4c6c4e0f83e0783e83c3e83c3d13544d51b541d51344d55135550b5555555559a755544c4c4c4c6c1c1c6c4c0c4c13031303e83d51034550f0f0f0f0f07070f0f0f0f0f0f0f0f0f0fa0f543d0f5550f0f0f0f13135550707555070741e81c1e82c2e0f83e0781d555555555551c0d1c47034704c4c4c4c1c1c1c1c3e83d543c3c3c3c3c3c3c3c3c3c3c3c1c1c1c1c3e83d543c3c3c3c1c1c4c1c1c1c1c1c1c1c1c4c1e9e81c1e81c3e0f83e0781d075550741d5513544d507541d50b555550742d55559a755541c0c1c07030704c4c4c4c1c1c1c1c3e83d5103455070f07070707070f0f0f0f0f070707070fa0f543d0f5550f0f0f0f3b3b83e0f83e0f48d513546d507542d5555669d5553b3b0fa0f5440d1543c3c3c3c3c3c3c3c3e83d50f43d5543c3c3c3c6c6eaaa070707aa0707aaa9a5aaa42d0b50b0b5070741d0766231313233703370dc0cdc07070707aa0b50b230f130f271f0f0f271f0f0f07070707aa0b50b270f270f071b07071307a707070707070707aaaaaaaa42d0b5070b5070741d07669d6a23a84ea0781eaa07aaa07a81e9582e2313132307030701c0c1c07070707aa0b50ba880e08c3c4c3c1c1c1c3c1c7c1c1c1c1c1c1ea82d42ea0f87e89c3c9c3c4c4eaa81c1eaa81c1e075a9aaaaa5070750b0b42d0b41d0769a43034310c0d0c1313131307070707aa0b50b271f0f0f271f0f0f130f130f07070707aa0b50b270f270f07071307070707070707071307a7aaaa81e0faaaa507075070b42d0b41d07669d6a07aaa0781eaa13a84ea07a81e9582e07030701c0c1c1313131307070707aa0b50ba880e01c7c1c1c1c1c1c3c4c3c4c3c1c1c1c1ea82d42ea0f87e89c3c9c3cfcfeaaa90b42d0b42d9a75a88ea13a86ea07a560b8fcfea82d42ea2038530f530f3f0f530faa0b50ba83e1fa530f530fa729c0e9e9e9e9c03a71341d81ca741c0cdc3e9e9e9e9e9e9c23131b070f80c2d0f370707070741c4c1e9eaaa944c4d5541c1d56aaa9555555669d55544c4c4c4c1c1c1c1ea80c031544c3c4c3c1c1c1c1ea89c7c3c3c9c7c3c3d549c3c9c3c1c1c4c1c1c1c1c1c1c1c1c4c1e9d550741d55075513544d507541eaaaaaaa965555555555559a707030701c0c1c131313130707070740d152a9541c7c1c1c1c1c1c3c4c3c4c3c1c1c1c1d47d5543c9ea9549c3c9c3c1c1c4c1c1c1c1c1c1c1c1c4c1e9c1c7c1c1c1c1c1c7c4c4c4c4c1c1c1c1eaaaaaaaaa95555555555541c0c1c07030704c4c4c4c1c1c1c1c7c7c7c7ea954ecfcec7c7c7c7c7c7c7c7eaaaaa955555554cccccccccccccccc7c7c7c7ea9549c9c9c9eaaa9555554acacacac9c9c9c9ea9543c3c3c3c3c3c3c3ea9543c3c3c3cecfced513548d507546eaaa96555555559a73b3b3f3f40d152a954ec3c3cfc3c3d47d5543ea9543c3c6c6c2c2c2c2c2c2c1c1c4c1c1c1c1c1c1c1c1c1c1c1e0f83e9681d81e0742d0b5a50790741d907231313234f034f13c0d3c070707070fa0f0b50b0f0f0f0f0f0f0f0f0f0f0f0f070707070fa0f0b50b0f0f0f0f071b07071307a70707070707070783e0fa070fa070781e0742d0b5070b5070741d075a669c2c8c2c8c2c2c2c4c2c4c2c2c1c1c1c1c1c1c2c2c1c1c2c1c1c1c1c1c1c1c1c1c1c1c1d5a88c4c4c8c1c0c1c07030701c1c1c1c3e83c2d42c2c0c2c0b030b03c3c3c3c1c1c1c3c1c3c1c1c1c1c1c1c3e83c2d42c2c2c2c3c2c3c2c2c3c3c3c3c1c1c2c1c1c4c2c2c2c1c1c1c2c2c6c6c1c1c1c1c2c2e0f83e0783e9683d42d0b41d0b5a50b990b131313131b07071b43034310c0d0c0fa0f0b50b0f0f0f0f0f07070f0f0f0f0f0f0f0f0f0fa0f0b50b0f0f0f0f 25 33554431 11 2047
def hc_75_17 : Nat → Nat := unpackHintV5 0xb4911155ec8ba8025e92ba28e85ca013e808c9c445f8cd9292565a0e26709791064647052fc37e8081bb0088dc00306d301a3610111ad4068d5a0206a5010347017167878090e45c3ae1b2132949015d07009403404201001a80d00b4040010094000010 0x3c3c1c1c1c1c1c1c1c1c1c1e696aaaaaaaa90b42d42c2d69907662313132347034711c0d1c07070707aa0b50b230f130f271f0f0f271f0f0f07070707aa0b50b270f270f0f0f131f0707070707070707aaaaaa42d0b42d0b41da750707660723070707130707071f0707071f070756aaa81c2c1c8c4c4c8c7c7c7c7c1c1c1c1ea82d42c1c0c1c07030720f81c1c1c1ea0781ea13a9eaaaaa42d0b582d690769d41c1d981c8c1c1c1c4c1c1eaa81c1e81ea95aaaa070b0723131323a880e01c1c1c1ea82d42c1c0c1c07030708c3c4c3ea83c9e87e81c1c1c1ea82d42c1c1c1c3c1c7c1c1c9c3c9c3c1c1c1c1e0783e0781c1c1c1ea0707070707541c1c3c3ea81c1d0b42d0741d90b50b0b50b0b13131313070707070fa0f3703370dc0cdc0b50b0f0f0f0f070707070fa0f0f0f0f0f0f0f0f0f0b50b0f0f0f0f0707070784ea7a0f0f81e07a81c1c1c1c1c1c1c1c3c3c3d0b42d0769d41c1d90b50b0b50b0b0713070707130707541c3ea81c1c1c3c1c3c1c1c1c1c1c3c1c1c1c1c1c1c2c1c4c4c4c4c1c1c1c1c3e83c3c0c3c0f030f02d42c1c0c1c07030703c3c3c3c1c1c1c1c3e83c3c3c3c3c3c3c3c3c2d42c1c1c1c3c1c3c1c1c3c3c3c3c3c3c1c1c1c1c1c1d6a681c1c1c1eaaaaaaa96942c2d0b42d07907076643034310c0d0c1313131307070707aa0b50b271f0f0f271f0f0f130f130f07070707aa0b50b270f270fa0fa0707aaa071b07070707aaaa13a9ea96960b42d0b41da75070766a07aaaaa0707071307070713070756aaa81c2c1e038a81313131307070707aa0b50b07030701c0c1c87eaa0f130f130f07070707aa0b50b0707070f071f0707270f270f0707070783e0781e07a070707070781c1c1d507070f0faa070742d0b507507642d42c2d42c2c8c4c4c8c1c1c1c1c3e83d6c0d6c5b035b02d42c3c3c3c3c1c1c1c1c3e83c3c3c3c3c3c3c3c3c2d42c3c3c3c3c1c1c1c1e83c3e13a9e0781ea07070707070707070f0f0f42d0b41da750707642d42c2c2c2d0f50b0b0723070707130707541c3ea81c1c1c3c1c3c1c1c1c1c1c3c1c1c1c1c1c1c2c1c8c4c4c8c1c1c1c1c3e83c3c0c3c0f030f02d42c1c0c1c07030703c3c3c3c1c1c1c1c3e83c3c3c3c3c3c3c3c3c2d42c1c1c1c3c1c3c1c1c3c3c3c3c1c1c1c1c1c1c1c1d0b42d0769d41c1d0b42c1c8c1c1c1c4c1c1d5070f0781e0707070b07070707070b50b07030701c0c1c2727272707070707272727270b50b0707070f071f070727272727070707075a55070707070707070784d83c3e0781d5543c3d55555555544c4c4c4c1c1c1c1cdc0cdc37033703e83d543c3c3c3c1c1c1c1c3c3c3c3c3c3c3c3c3e83d543c3c3c3d51344d51348c1c1c1c1d41e13a9e83c3d9550f81e07a943d555543c3c1c1c1c1c1c1c1c1c3c3c3d5555541da75555551313131340d1501c1c1c1c3e83c3c0c3c0f030f1543c3c3c3d0f5543c1c1c1c1c3e83c3c3c3c3c3c3c3c3d543c3c3c3e9e9ca7a7030fa7a733a7a73329e9c030f29e9c0e9e9e9e9e9e9c030f82d0707070750f0f55a0707aaaa613a9eaa9555555541da755555513131313070707070300caa55130f130f07070707271f0f0f271f0f0faa55270f270fa0f55665565513544e07aa81c1c1c1c1d41eaaa84ea76556aa55555555550769d56038a81313131340d1501c1c1c1ea9561faa83c4c3c4c3d1f5543c1c1c1c1ea9549c3c9c3d513548c1c1c1c1d41ceced9550f070707075555550769d54eced0345407070707552727272747d550f0707070727272727552727272707130713a0ba0f81e0f0b0b0ba82c2d41c1c1c1c3d0f0faa0b0b42d0b41d0b642d41c1d42c1c4c4c4c4c6c1c1c6c3e83cdc0cdc37033702d42c3c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c2d42c3c3c3c3c1c4c1c4e13a9e83c3e0783ea0f1b070707070f0f0f0f0f42d0b5070741da7642d42c2d42c2c2c4c2c2c2c4c2c2d50b0f0b0faa0b82c2c2c3c2c3c2c2c2c2c2c3c2c2c2c2c2c1c1c1c4c4c4c4c6c1c1c6c3e83c3c0c3c0f030f02d42c2c0c2c0b030b03c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c2d42c2c2c2c3c2c3c2c2c3c3c3c3e9ca703a7a7a7a700e9e9e9c4e0760f29d07030fa7a7 25 33554431 11 2047
def hc_75_18 : Nat → Nat := unpackHintV5 0x7c688b9e4a1a0748c939c7f1486f2c5a1b0019667a88b185a32058f10f151b2424fd093924336248b80a921503248540011b30c44130b38f0129633a10c8c1919e2cf86d8a0327624787287d32961c505f85dd26e13308883522f40a785a018722e035c5800001ae 0x2c3c3c3c1c1c1c1c1c1c1c1e0f83e0f83e07a9e81c1c1c7c1c1c1c7c1c1c1c4c1c1c1c4c1c1ea070f075555555555551f1f1f1f13131313070707070fa0f07030701c0c1c550b0f1313a87e2ba87e1fa84ea130707070707070707a07aaaaaaaa07a9d5555555555547c7c7c7c4c4c4c4e038a807070707aa550b0f0f0f071b071b0713071383e0f83e0fa070781ea70f1f0f1f0f0f0f1f0f2b0f0f0f130f0f0f130f0fa81c1c1d5555555555547c7c7c7c4c4c4c4c6c1c1c6c3e83c3c0c3c0f030f1542c4c4c4c7c7c7c7c4c4c4c4c7c7c7c7c4c4c4c4d555555547c7c7c7c4c4c4c4ccccccccccccccccd544c4c4c4c3c3c3c3c3c3c3c3d5555544c4c4c4c9c9c9c9c3c3c3c3d543c2c3c3c3c3c3c3c3c3c3c3d543c3c3c3d42d075546c4c4c4c4d9550f1313131355551369d555503454131313135551f5550f131313132b2b2b2b2b2b2b2b552b2b2b2b0713071b5aa90f0f070707070b0baaa07aaaaa90b641d0b50b0b5a66231313231b07071b3703370dc0cdcaa0b50b230f130f1b07070f371f0f0f371f0f0faa0b50b370f370f0713071b88ea13a83eaa81ea7aaa942c2d1369d0742d60b5a66542c6c2c6c1c1c1c1c2c1c2c2eaa82c2e82eaaaaa82c2c2c8c4c4c8c6c1c1c6ea2038aa0b50b0b030b02c0c2c230f130f1b07070fa83e1faaa0b50b0b0b0b0b0f0f0b0b1f0b0b370f370f0707070783e0f81ea7a07070723070707130707a81c3c1d42c2d1369d0741d90b5070b50707541c1c1c1c1c1c1c1c2c3c2c3ea82e0b0b0707070707070b0b07070b3f070707070b0b0b23131323070707070fa0f07030701c0c1c0b50b0b030b02c0c2c0f0f0f0f070707070fa0f0707070f070f07070b50b0b0b0b0b0f0f0b0b0f0b0b0f0f0f0f9aa5070707070707070707070707aaaaaaaa42d96942c2d0741d988c4c4c8cdc0cdc37033701c1c1c1ea82d42c8c3c4c3c9cdc7c7c3c3c9c7c3c9c3c3c1c1c1c1ea82d42c9c3c9c3c7c4c4c7c1c1c1c1c1c1c1c1eaaaaa942c2d1369d0b42d0741d9950b1f0b1f0b0b0b1f0b270b0b0707070707070707aaaa0b0b0b231313231f1f1f1f07070707aa0b50b0b030b02c0c2ca84e13a88e2307070707a07aaaaaa07a9d42c2d1369d969682c2d0741d995a0baaaaa0b0b07070b1b0707070707070707a0b0faaaa0b0b0b2313132380e2a01c1c1c1ea82d42c2c0c2c0b030b08c3c4c3e87eaa83cac1c1c1c1ea82d42c2c2c2c2c3c3c2c2c7c2c2c9c3c9c3e9e9e1c030fa729c0e1c3cce0707a9d0f0f0f81c1c2c1e82c3c3c3d0b1369d0b42cccce1c1c4c1c6e0f83e81c1e07a9c2d43c3c3c3c3da070707070b81c1ea82c1d42c2d1369c2d0742d90b50b0b50b0b231313231b07071b0fa0f870300e1c0b50b0f0f0f0f0f07070f0fa0f0f0f0f0f0f0f0f0f1f0f0f0b50b0f0f0f0f0713071b83e0f81e0b0f0f0f0f81c1c3c1e83d42c2d1369d0742d90b42d0b542c6c1c1c1c1c2c2c2c3ea82c2c2c3c2c3c2c2c2c3c2c7c2c2c2c2c2c8c4c4c8c6c1c1c6c3e83c3c3c3c3c2d42c2c0c2c0b030b01c4c1c6e0f83e81c1e07a9c3c8c3c3c3c4c3c3ea07070750b0b44da741d0b642d42c2d42c2d50b1b070707070b0b0b0faa0b0b0b0f0b0f0b0b0b0b0b0f0b0b0b0b0b0b0b0b231313231b07071b0fa0f0f030f03c0c3c0b50b0b030b02c0c2c0f0f0f0f0f07070f0fa0f0f0f0f0f0f2b0f0f0f0f0f0b50b0b0b0b0b0f0f0b0b0f0b0b0f0f0f0f231313230f0f0f0f0f0f0f0f42d0b42d0b42d0b23131323272727270f0f0f0f0b50b0f0f0f43c3c3c3c3c3c3c3c2d42c3c3c3c3c1c4c1c6e23a84ea0faaa07a9eaaa42d90742d60b5a6643c4c7c6c1c1c6ea1f87eaa82d42c8c4c4c8c6c1c1c6ea2038aa0b50b1f1f1f1f0707070783e0f81ea7a07070723070707130707a81c3c1d0b41d0741d90b5070b5070743c3c3c1c1c1c1c3e83c1c1c1c7c1c7c1c1c2d42c8c4c4c8c1c1c1c1c3e83c1c0c1c07030702d42c7c7c7c7ea13a88c1c1c1c1e81eaaaaa81ea742d96960b41d076643c4c7e87c7eaa87d4c1c1c1c1ea82d42c8c4c4c8e038a807070707aa0b50b1f1f1f1f0713071b83e0fa070781ea70f230f0f0f130f0fa81c1c1d0b42d0742d90b50b0b50b0b43c3c3c6c1c1c6c3e83c3c3c3c3c7d4c3c3c7c7c3c3c2d42c8c4c4c8c6c1c1c6c3e83c3c0c3c0f030f02d42c7c7c7c7c8c4c4c8c8c4c4c8d0b42d0b42d0b42d13131f1f1f1f1f1f1f1f1f0b50b2313132333333333333333330b50b1f1f1f1f231313232313132350b0b44da742d0b42d0b542c6c2c1c2c1c2c2c2c3c2e0b82c2c2c2c2c8c4c4c8c2d42c2c0c2c0b030b08c4c4c8d4cad4cad4cad4cac2d42c2c2c2c2c3c2c2c7c2c2d4cad4cad56941c4c1c4c1c1c2c2c1c1c3c2e60f50f0f5581e0f5555555555131313133703370dc0cdc1b07071b0fa0f550f0f0f0f0f0f0f0f0f0f0f0f0f07070f0fa0f550f0f0f0f0713071344d513542d84ea7a0f0f81e0f543d96a0f1b070707070f0f5550f0f50f550f0f0f5541da755555555544c4c4c4c6c1c1c6d510340fa0f0f030f03c0c3c550f0f0f0f0f07070f550f0f50f50fa0f0f0f0f0f0f0f0f0f550f0f0f0f071b071b0f0f0f0f0f07070f5555552b2b2b2b1b07071b0f0f0f0f550f0f0f0f0f07070b0f0f0f0f550f0f0f0f07130713131313130b07070f84ea7a0f0f81e0f83e0fa83c6c1c1c1c1c3c3c3c7c3c3c3c7c3c3c3c3c3d5555555555544c4c4c4c6c1c1c6c7c7c7c7c3e83c3c0c3c0f030f1541c6c1c6c7c7c7c7c2c1c1c6cecfcec6c1c1c6c7c7c7c7d55555554cccccccc6c1c1c6c7c7c7c7ccccccccd541c6c1c6d23544d50b4ecfcec6c1c1c6d50f655541da7555554ecec6c1c1c6d510343f3f553b27271b07071b550f51f5273f27552727 26 67108863 11 2047
def hc_75_19 : Nat → Nat := unpackHintV5 0x82bc9b9fc51d47ab88b9d362f07128761b8418c698092194a22c61bc6d96df32058b85894b62f04ac502919a22e4048c40ed727632e50f0b8a25e2a7876097a2481fc8c407d90321ee80f87b80041dd0220670208168068047d2460d709082771ca0318d8800018c 0x71b071b83e0fa070781ea70f230f0f0f130f0fa81c1c1c6c1c1c6c3e83c3d0f0b0f43c2c6c1c1c6c3e83c3c0c3c0f030f03c3c3c3c3c1c1c3c3e83c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3e82c2ea943c3d541c4c1c6d5696a9a95555555554dc0cdc37033708c4c4c8c6c1c1c6ea954dc7c3c3cdc7c3c3c8c3c4c3c6c1c1c3ea954dc3cdc3d0b41c4c1c6d51b41d623a84e9556965583eaa566581ea7aaa91369d55555555555231313235440d06c1c1c6ea2038aa55230f130f543d1f51b07070fa83e1faaa55370f370f42d07070707541d07583e0f543d9607a9e81c1c1c8c1c1c1c4c1c1d5541c1d41cfd56a070f0744da75555555555548c4c4c8d51034070707070fa0f07030701c0c1c550f0f0f0f543d0f5070707070fa0f0707070f070f0707550f0f0f0f07070707aaa0b0b5070755aaa6a5555555555555523131323070707073703370dc0cdcaa55230f130f07070707271f0f0f271f0f0faa55270f270f42d1f13131f547d1f507070707541d07507070707aa5665aaa644da755555555548c4c4c8d510341f1f1f1f07070707aa5542da84ea23555969541c1c1c1d50741d681ea95996aaa81ea744da75555555590b5555231313235440d2038a807070707aa55230f130f543d1f5a1faaa0f2b07070707aa55270f270f0f0f0b0b0f0f0f0b5a550713071b507075583e0f81e5555544d5555543034310c0d0c231313231b07071b0fa0f550f0f0f0f0f0f0f0f0f0f0f0f0f07070f0fa0f550f0f0f0f42d0713071b546d07583e0f543d960790f0f0f0f543d0f581c1c3c1e83d1369d555555555231313235440d06c1c1c6c3e83c3c3c3c3d550b41c4c1c6d51b41d60f83d50f65a070781ea70f230f230f0f0f130f130f0f5550f0f50f55a81c1c1d1369d55555555555231313235440d06c1c1c6c3e83c3c0c3c0f030f1543c3c3c3d50f43d43c1c1c3c3e83c3c3c3c3c3cac3c3c3c3c3d543c3c3c3d0b48c4c4c8d51b41d48c4c4c8d50f6544da7555555548c4c4c8d510345523131323543d1f52b2b2b2b552b2b0713071384ea13a83eaa81ea7aaa91369d42c2d0742d60b5a66542c6c1c1c1c1c2c2eaa82c2e82ceeaaaaa82c2c2c4c4c4c4c6c1c1c6ea2038aa0b50b0b030b02c0c2c130f130f1b07070fa83e1faaa0b50b0b0b0b0f0b1f0b0b2b0f2b0f0707070783e0f81ea7a07070713070707130707a81c3c1d1369d42c2d0741d90b5070b50707541c1c1c1c1c1c1c1c2c3ea82c2c1c1c1c1c1c1c2c2c1c1c2cec1c1c1c1c2c2c2c4c4c4c4c1c1c1c1c3e83c1c0c1c07030702d42c2c0c2c0b030b03c3c3c3c1c1c1c1c3e83c1c1c1c3c1c3c1c1c2d42c2c2c2c3c2c3c2c2c3c3c3c3c4c4c4c4c1c1c1c1c1c1c1c1eaaaaa91369d42c2d0b42d0741d9950b1f0b0b0b1f0b0b0707070707070707aaaa0b0b0b131313131f1f1f1f07070707aa0b50b0b030b02c0c2ca84e13a84e2307070707a07aaaaaa07a9d1369d42c2d6960b41d07665682ceeaaaa82c2c1c1c1c1c1c1c1c1eaaa82c2c2c4c4c4c4e038a807070707aa0b50b0b030b02c0c2c130f130fa1faaa0f2b07070707aa0b50b0b0b0b0f0b1f0b0b270f270f0713071383e0f81e0b0f0f0f0f81c1c3c1e83d1369d42c2d0742d90b42d0b542c6c1c1c1c1c2c2c2c3ea82c2c2c3c2c2c2c3c2c2c2c2c2c4c4c4c4c6c1c1c6c3e83c3c3c3c3c2d42c2c0c2c0b030b01c4c1c4e0f83e81c1e07a9c3c4c3c3c3c4c3c3ea07070744da750b0b41d0b642d42c2c2c2d0f50b0b542c6c1c1c1c1c2c2c2c3ea82c2c2c3c2c3c2c2c2c2c2c3c2cec2c2c2c2c2c2c2c4c4c4c4c6c1c1c6c3e83c3c0c3c0f030f02d42c2c0c2c0b030b03c3c3c3c3c1c1c3c3e83c3c3c3c3c3cac3c3c3c3c3c2d42c2c2c2c3c2c3c2c2c3c3c3c3c4c4c4c4c4c4c4c4d1369d42c2d0b42d0b42d50b1b0b070b070b0b0b0f0b82e0b0b0b0b0b131313130b50b0b030b02c0c2c131313132b2b2b2b2b2b2b2b0b50b0b0b0b0f0b1f0b0b2b2b2b2ba0b0baa071307135550f0faaa5556aa5555555555131313134f034f13c0d3c1b07071baa55130f130f2b1f0f0f2b1f0f0f1b07070faa552b0f2b0f50b41d551b071307135955556a13a84ea0f9695560faa81ea7aaa955544da75555555540d1504c4c4c4c6c1c1c6ea2038aa5551f5550f0f130f130f1b07070fa83e1faaa552b0f2b0f50b50707555071b0707070765543e0f83e07a9e81c1d41cfd555541c1c1c4c1c1c1c4c1c1ea070f0755551369d555555550345413131313070707070fa0f07030701c0c1c5550f5550f0f0f0f0f0f070707070fa0f0707070f070f0707550f0f0f0f29e9dbc0ccc9e9e9c6f030f82d27982e90750f0f0fa07a9e5544da755336f3307070707a0b0baa5070755aaaa607a9e95555544da7555555551313131307070707036f1bc0caa55130f130f07070707271f1f0f0f271f0f270f0faa55270f270f50b51f275551f1f1313131341d550707070707070707076556aaaaa655551369d55555503454131313131f1f1f1f07070707aa5550b5a55555aa13a84d075541c1c1c1c1e81d955aaaaaa81ea755551369d55555555034541313131380e2a01c1c1c1ea95547d5543c3c4c3c4c3e87eaa83cac1c1c1c1ea9549c3c9c3c3c3c2c2c3c2c3c3c1c4c1c4d556a0f83d5541c1e0795555555555131313134f034f13c0d3c1b07071b0fa0f550f0f0f0f0f4f0f1f0f0f0f0f0f0f0f0f0f07070f0fa0f550f0f0f0f50b41d551b0713071365543e0f83e07950f1f5550f0f0f0f0f0f81c1c3c1e83d55544da755555540d1504c4c4c4c6c1c1c6c3e83c3c3c3c3d5542d41c1d5546c6c1c4c1c4d695543c3e0f83e81c1e07a9d43d555543c3c3c4c3c8c3c3c3c4c3c4c3c3ea07070755551369d555550f42d55503454131313131b07071b0fa0f0f030f03c0c3c5550f5550f0f0f0f0f0f0f07070f0fa0f0f0f0f0f0f2b0f0f0f0f0f550f0f0f0f0b0f1313071b071b0713071387ea1fa84ea13a83eaaaa81ea7aaa95555555555547c7c7c7c4c4c4c4c6c1c1c6ea2038aa55 26 67108863 11 2047
def hc_75_20 : Nat → Nat := unpackHintV5 0x88aacc7d7acc72caac6b49e063e9d8589ad452f9684d796046c1ae3d4a5e3681b22c8a7e2701621d8a5e18694812c9680c719605f99e00017e 0x1c6c1c1c4c1e9c1c1c1c1c1c1c1c8c4c4c8c1e070f0781c1c1c1c1c1c8c4c4c8c1d070b0741c1c1c1c1c1cecec8c4c4c8c1c0c1c07030701c1c1c1cecec8c4c4c8c1c1c1c3c1c7c1c1c1c1c1c1c9c9c9c9c9c9c9c9c9c9c9c9c1c4c1e9c1c1c4c4c1c1c1c4c6c4c4c4c4c4c6c1c1c6c4e130f1384c3c4c4c4c4c6c1c1c6c4d130b1344c2cfcfc4c4c4c4c6c1c1c6c4c0c4c1303130fcfc4c4c4c4c6c1c1c6c4c4c4c3c4c7c4c3cac9cac9cac9cac9cac9cac9c1c1c4c1c1c1c1c1c1c1c1c4c1e9c1e07070781c3c4c4c4c4c1c1c1c1c1d07070741c2c4c4c4c4c1c1c1c1c1c0c1c07030704c4c4c4c1c1c1c1c1c7c1c1c1c1c1c3c4c4c4c4c1c1c1c1c9c9c9c9c9c9c9c9c9c9c9c9c1c4c1c6c3c3c3c3c3c1c1c3c8c4c4c8c6c1c1c6c3c3c3c3c8c4c4c8c6c1c1c6c3c3c3c3cbcbcbcbc3c3c3c1c3c1c1c3c3c3c3c3c3c3c3c3c3c3c3c3c1c4c1c6c1c4c4c7c4c1c1c6c8c4c4c8c6c1c1c6c7c7c7c7c8c4c4c8c6c1c1c6c7c7c7c7cecfcec8c4c4c8c6c1c1c6c7c7c7c7ccccccccccccccccc1c1c4c4c1c4c1e9c1c1c1c4c4c4c8c4c4c8c6c1c1c6c6e1b0f1b86c3c8c4c4c8c6c1c1c6c6d1b0b1b46c2cecfcec8c4c4c8c6c1c1c6c6c0c6c1b031b0fcfcecec8c4c4c8c6c1c1c6c6c6c6c6c3c6c6c7c6c3c9cfc9c9cec9c9c9c8c4c4c8eaaa88c4c4c8c9c9c9c9ea88c4c4c8c9c9c9c9ea8bcbcbcbc3c3c3c3c3c3c3c3ea83c3c3c3c3c3c3c3c3c3c4c7c8c4c4c8c7c7c7c7eaaaaa88c4c4c8c7c7c7c7cececfea88c4c4c8c7c7c7c7ccccccccea8ccccccce0f88c4c4c8ea1b81ea13a9eaaaaa23131323982e68ececfea88c4c4c8ea20383f3faa3b3b230f130faa0fa1fa3f0f0faa0f3b0f0f0f1313131384ea7a0f0f83e0fa83c6c3c1c3c1c3c3c3c3c3c4c4c4c4c3e83c3d0f0b0f43c2c4c4c4c4c3e83c3c0c3c0f030f03c3c3c3c3c3c3c3c3e83c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3e83e07aa86c4c4c4c4eaaa84ea7aa9a982c4c4c4c4cfcfeaa038a8131313133f3faa87eaa0f130f130f2b0f2b0faa2b0f2b0f2b0f2b0f23131323a0f0f84ea783e0fa83c6c3c1c3c1c3c3c3c3c3c8c4c4c8cecec3e83c3d0f0b0f43c2c8c4c4c8c3e83c3c0c3c0f030f0ecec3c3c3c3c3c3c3c3c3e83c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c1c6c1c6e23a84ea0faaa07a9eaaa1b07071b982e6aa86c1c1c6ea2038aa0f0f1b07070fa83e1faaa0f0f0f0f0707070783e0f81ea7a07070723070707130707a81c3c1c1c1c1c1c3e83c1d070b0741c1c1c1c1c1c3e83c1c0c1c07030703c3c3c3c1c1c1c1c3e83c1c1c1c3c1c3c1c1c3c3c3c3c3c3c3c3c7c7c7c7c1c1c1c1c1c1c1c1eaaaaa87c7c7c7c1c1c1c1ea8cccccccc7c7c7c7c1c1c1c1ea8cccccccc1c1c1c1eaaa8acacacac1c1c1c1ea8acacacac1c1c1c1ea8bcbcbcbc3c3c3c3c1c1c1c1ea83c3c3c3c3c3c3c3ea13a88c1c1c1c1e81eaaaaa81ea79a982c1c1c1c1eaa038a807070707aa270f270fa1faaa0f07070707aa270f270f270f270f071b071b83e0f81e0f2b2b2b2b1b07071b0fa0f2b2b2b2b1b07071b0fa0f2f2f2f2f0f0f0f0f0f070783e81c3c3c3c3c3c3c3c3c1c6c1c6e0f83e0783c3c3c3c3e07070f07a0f1b07071b0fa0f0f0f0f0f333333331b07071b0fa0f0f0f0f0f33333333 24 16777215 10 1023
def nh_75 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_75_20 (Nat.sub p 640)) (hc_75_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_75_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (Bool.rec (hc_75_17 (Nat.sub p 544)) (hc_75_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_75_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (hc_75_14 (Nat.sub p 448)) (hc_75_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_75_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (hc_75_11 (Nat.sub p 352)) (hc_75_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_75_9 (Nat.sub p 288)) (hc_75_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_75_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (hc_75_6 (Nat.sub p 192)) (hc_75_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (hc_75_4 (Nat.sub p 128)) (hc_75_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_75_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_75_1 (Nat.sub p 32)) (hc_75_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def f_75 : Nat → Nat × Nat := unpackForestF 0x18be00c5b0062bd1a1228d08800c53a282c514150016be00b5b005ab802d4c0169e00b4ba082e5041400168f3f8389fc1a002d0e7d8c93ab4f9d5a5cf35a2790b93ab479d9b24ec0d27568600a5f9ba2fcdd16e710d9374579bc224dd14c014b73647c969a7cb4d2e6629f3314399c20ccc13a64ae13205c969a3cc2df2610692d3439711fcb88ee5c46f2e233968364b4180014af2c25491a2fc8d16e544d92a06c91a2bc9e4ee4f26f2802993c1b49a9124d089234539181448ed3e4769723b4791da1c8c090014a722354901b5c80122414b72004400527c7a9923d0c91b46f8ed2246d1ae394f91b4678dd2246d18c014971a36c8a1b5c641122a29f17a5c8bc0a45452e2a28f1614c8ad2a45450e29ae11436700523c4c9121a8d70e13f88d264384ee210990e13787c9e43a9121d0290e13386d2243518c014870c354856b5c2cdf215ace00a3f84d324215be114f9085670051dc104fe0d4990413b8209bc144f2094890413381e3840759e058af0184c80c200028de014c8f956f7fd2a3e55adfd4f8f95677d4a7bf4971f5296fa9477dca63ec951f5286f9a547cc2a3e558c01466f8464789a7bc4d2dedad0f13477adb23c4d0de94c8f124b79d323c490de54c8f123b78d323c48cc012bef015472a2fb9516ddd2d8e545776ca239514dd92a8e535f75c9a394d6dd52d8e535774c9a394d4dd1288e534f73c9a394d2dcd2b8e534772c9a394d0c012b6e447c6a1a7b50d2dc449ee224370eb8350d1dc16f8d43436fe3e35093dbd4f8d424b6d5a7b75171b5696dab476dda636d151b5686da5706a123b649f1a8486d837c6a11fb5c9f1a8476d635b6ae383508dda94f8d4233004abb4c551898bec4c5b68cb631315da0476d003667ca231314d9d268c4b5b66d27b344d1896a6cc134625a5b2a97d954aeca134625a1b120618a69ec534b629a3b14d0d8a496c52436291db148cd890280095361daa2f2dad856a8bcb6360e322f29bd794d6c047c5e533afc951794c6be3545e51faf4951794660094f5dcb22c31bd75288b0c6b5ccbe2c319d71288b0c635bcb22c2dbd616d6b617c585b3ad44d1616c6b4144585a7acc4d161696b215c585a3ac44d1616860094b57eb427edbd5d6d89fb6b55527ab4d7155496aaa4755d262acd5155486aa5704fdb3aa4db13f6c6a85684fd37a7e9ad4c69ea634352eb827e99d494d89fa6351db627e8fd454d89fa3b50db5a851813f46ea026c4fd1980251d3d2889046b4ed1da74511208c69c164481b7a40dad352f8903674c927a6409931268903634bca2240d3d2c4de962674ac9a240d0d2003090b5b485a9a4297d214b690a5748529a428fd2146690014004a1a3cd9108ade8e354422b5a34df108ace8c354422b1a2cd91084de8426b44dbe21099d114888426343daa21097d0d4888425b42db621095d09488842530049fa0c590eeade8217c3bab3a04590ee6de7736b3fcbe1dcd9cfd268773633ec9a1dcd6cf92d8773573b80c1df17cef8ae77a5f3bd2d9de95cef4a677a4b3bd239dc0500127676468352b79c88fce96987223b3911b9cc8f0e56887223338e381a959ce18d06a26f351359bcd6cdd8e06a26736d2e1a898cd94b86a25b359b59acd9cd58c06a2570049b9a4590b2ade681542cab599c5f0b2ace6624b32caa16558cc92c85936f2c9b598c5f0b26ce61a5f30d2b9844d0b26c6601542c9af97c4d0b26b65e16c2c9ab9689bcb96f85a26b2d13396c9b0b56e85a2632cc9a164d4c012665826426ab795c9509aad65627c26ab39549509aac65426426a3794c9109a8d65227c26a339449109a8c65025426a2f93516c9d4d84d45726d2213514c0125e4c154202b592c5f080ace4a144202359245f0808ce481542022f90116c8d2d84045722ca210114c8003040c5b2062b902d6c816ae40b4f205a5902d1c8168640014004958fcd6066ad63b24f1edae0ec92c7648e3c24c1ddaa0ec90c756e0335671cda40cd1ac704b6382571bdb80cd19c6d6b03345f19a2d8d49ac696c03345719da40cd14c0124e32164112b78c455044ad63017c112b38bcd2c5d2a82256316cb20891bc592882246b15cbe08919c4f6be2a46c13dad89ed5c516b82846413da989c510448c6261541122f88916c492d822457119b788cd9c452882245300491884d3c010be0085b0fe3e074d3c3d8f81d24f0ee380748dc010ae008530dd3780213c010961a5680bdb78655a02f4de184600bd1b80211c010861635409eb1854d90274de1435409d2f8020fc010761226f0041b8020cc214a80e56307d320391bc1d4a80e45f004178020ac198be008270041182c5500bac60a16402e378245500b8be0816402db781c5500b6be0615c02da380207c0103601d6300e3780717c036de01b5f00da380205c010260003f 10 11
def ch_75 : Nat → Bool := dagCheckNodeV5 fullMask g_75 ep_75 6 63 bds_75 658 (dagTraceF fullMask rootStock 11 f_75) cur_75 nh_75
set_option maxHeartbeats 0 in
theorem rc_75 : dagCheckRootsV5 fullMask g_75 ep_75 6 63 658 bds_75 (dagTraceF fullMask rootStock 11 f_75) (cur_75 0) (nh_75 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_0 : treeBlockF 0 32 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_1 : treeBlockF 32 64 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_2 : treeBlockF 64 96 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_3 : treeBlockF 96 128 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_4 : treeBlockF 128 160 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_5 : treeBlockF 160 192 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_6 : treeBlockF 192 224 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_7 : treeBlockF 224 256 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_8 : treeBlockF 256 288 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_9 : treeBlockF 288 320 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_10 : treeBlockF 320 352 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_11 : treeBlockF 352 384 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_12 : treeBlockF 384 416 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_13 : treeBlockF 416 448 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_14 : treeBlockF 448 480 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_15 : treeBlockF 480 512 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_16 : treeBlockF 512 544 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_17 : treeBlockF 544 576 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_18 : treeBlockF 576 608 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_19 : treeBlockF 608 640 ch_75 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_20 : treeBlockF 640 658 ch_75 = true := by decide +kernel
theorem nj_75_1 : ∀ i, 0 ≤ i → i < 64 → ch_75 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_75_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_75_1 h1 h2)
theorem nj_75_2 : ∀ i, 0 ≤ i → i < 96 → ch_75 i = true := block_join nj_75_1 (fun _ h1 h2 => treeBlockF_at nb_75_2 h1 h2)
theorem nj_75_3 : ∀ i, 0 ≤ i → i < 128 → ch_75 i = true := block_join nj_75_2 (fun _ h1 h2 => treeBlockF_at nb_75_3 h1 h2)
theorem nj_75_4 : ∀ i, 0 ≤ i → i < 160 → ch_75 i = true := block_join nj_75_3 (fun _ h1 h2 => treeBlockF_at nb_75_4 h1 h2)
theorem nj_75_5 : ∀ i, 0 ≤ i → i < 192 → ch_75 i = true := block_join nj_75_4 (fun _ h1 h2 => treeBlockF_at nb_75_5 h1 h2)
theorem nj_75_6 : ∀ i, 0 ≤ i → i < 224 → ch_75 i = true := block_join nj_75_5 (fun _ h1 h2 => treeBlockF_at nb_75_6 h1 h2)
theorem nj_75_7 : ∀ i, 0 ≤ i → i < 256 → ch_75 i = true := block_join nj_75_6 (fun _ h1 h2 => treeBlockF_at nb_75_7 h1 h2)
theorem nj_75_8 : ∀ i, 0 ≤ i → i < 288 → ch_75 i = true := block_join nj_75_7 (fun _ h1 h2 => treeBlockF_at nb_75_8 h1 h2)
theorem nj_75_9 : ∀ i, 0 ≤ i → i < 320 → ch_75 i = true := block_join nj_75_8 (fun _ h1 h2 => treeBlockF_at nb_75_9 h1 h2)
theorem nj_75_10 : ∀ i, 0 ≤ i → i < 352 → ch_75 i = true := block_join nj_75_9 (fun _ h1 h2 => treeBlockF_at nb_75_10 h1 h2)
theorem nj_75_11 : ∀ i, 0 ≤ i → i < 384 → ch_75 i = true := block_join nj_75_10 (fun _ h1 h2 => treeBlockF_at nb_75_11 h1 h2)
theorem nj_75_12 : ∀ i, 0 ≤ i → i < 416 → ch_75 i = true := block_join nj_75_11 (fun _ h1 h2 => treeBlockF_at nb_75_12 h1 h2)
theorem nj_75_13 : ∀ i, 0 ≤ i → i < 448 → ch_75 i = true := block_join nj_75_12 (fun _ h1 h2 => treeBlockF_at nb_75_13 h1 h2)
theorem nj_75_14 : ∀ i, 0 ≤ i → i < 480 → ch_75 i = true := block_join nj_75_13 (fun _ h1 h2 => treeBlockF_at nb_75_14 h1 h2)
theorem nj_75_15 : ∀ i, 0 ≤ i → i < 512 → ch_75 i = true := block_join nj_75_14 (fun _ h1 h2 => treeBlockF_at nb_75_15 h1 h2)
theorem nj_75_16 : ∀ i, 0 ≤ i → i < 544 → ch_75 i = true := block_join nj_75_15 (fun _ h1 h2 => treeBlockF_at nb_75_16 h1 h2)
theorem nj_75_17 : ∀ i, 0 ≤ i → i < 576 → ch_75 i = true := block_join nj_75_16 (fun _ h1 h2 => treeBlockF_at nb_75_17 h1 h2)
theorem nj_75_18 : ∀ i, 0 ≤ i → i < 608 → ch_75 i = true := block_join nj_75_17 (fun _ h1 h2 => treeBlockF_at nb_75_18 h1 h2)
theorem nj_75_19 : ∀ i, 0 ≤ i → i < 640 → ch_75 i = true := block_join nj_75_18 (fun _ h1 h2 => treeBlockF_at nb_75_19 h1 h2)
theorem nj_75_20 : ∀ i, 0 ≤ i → i < 658 → ch_75 i = true := block_join nj_75_19 (fun _ h1 h2 => treeBlockF_at nb_75_20 h1 h2)
theorem nc_75 : ∀ i, 0 ≤ i → i < 658 → ch_75 i = true := nj_75_20
theorem lb_75 : LowerBin fullMask rootStock g_75 12 :=
  lowerDagV5 (kn_cons lb_73 (kn_cons lb_70 (kn_cons lb_71 (kn_cons lb_74 (kn_cons lb_68 (kn_cons lb_66 (kn_cons lb_29 (kn_cons lb_65 (kn_cons lb_67 (kn_cons lb_69 (kn_cons lb_72 (kn_cons lb_64 (kn_cons lb_32 (kn_cons lb_35 (kn_cons lb_27 (kn_cons lb_45 (kn_cons lb_15 (kn_cons lb_33 (kn_cons lb_60 (kn_cons lb_41 (kn_cons lb_43 (kn_cons lb_54 (kn_cons lb_57 (kn_cons lb_26 (kn_cons lb_39 (kn_cons lb_44 (kn_cons lb_52 (kn_cons lb_58 (kn_cons lb_21 (kn_cons lb_40 (kn_cons lb_22 (kn_cons lb_37 (kn_cons lb_61 (kn_cons lb_23 (kn_cons lb_24 (kn_cons lb_55 (kn_cons lb_63 (kn_cons lb_53 (kn_cons lb_36 (kn_cons lb_48 (kn_cons lb_46 (kn_cons lb_62 (kn_cons lb_25 (kn_cons lb_56 (kn_nil))))))))))))))))))))))))))))))))))))))))))))) rc_75 nc_75 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.and, [5, 14]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.or, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4207470720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 4207470720)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 4207470720) = g_75 by decide]
  exact lb_75

end PEqualNP.Outside.L_meta_48629

theorem PEqualNP.Outside.L_meta_48629 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 4207470720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4207470720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48629.table2_from_lowerBin (4276676744 * 2 ^ 32 + 4207470720) 13 PEqualNP.Outside.L_meta_48629.root_lb PEqualNP.Outside.L_meta_48629.wg 18 rfl PEqualNP.Outside.L_meta_48629.wfits PEqualNP.Outside.L_meta_48629.weval
