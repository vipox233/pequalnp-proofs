import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49293

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
def m_0 : Nat := 0x4040404040404040
def s_0 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_0 : Nat := 0x4000404040
def ep_0 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cc_0_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_0 : Nat → List (Nat × Nat) := cc_0_0
def hc_0_0 : Nat → Nat := fun _ => 0
def nh_0 : Nat → Nat := hc_0_0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 0x4040404040404040 g_0 ep_0 1 1 bds_0 1 (dagTraceF 0x4040404040404040 [0x40004000400040, 0x404000004040, 0x40404040] 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 0x4040404040404040 g_0 ep_0 1 1 1 bds_0 (dagTraceF 0x4040404040404040 [0x40004000400040, 0x404000004040, 0x40404040] 3 f_0) (cur_0 0) (nh_0 0) [0x40004000400040, 0x404000004040, 0x40404040] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0_0 h1 h2
theorem lb_0 : LowerBin 0x4040404040404040 [0x40004000400040, 0x404000004040, 0x40404040] g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)
def m_1 : Nat := 0x4400440044004400
def s_1 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_1 : Nat := 0x40004004400
def ep_1 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cc_1_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_1 : Nat → List (Nat × Nat) := cc_1_0
def hc_1_0 : Nat → Nat := fun _ => 0
def nh_1 : Nat → Nat := hc_1_0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 0x4400440044004400 g_1 ep_1 1 1 bds_1 1 (dagTraceF 0x4400440044004400 [0x400040004000400, 0x440000004400, 0x44004400] 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 0x4400440044004400 g_1 ep_1 1 1 1 bds_1 (dagTraceF 0x4400440044004400 [0x400040004000400, 0x440000004400, 0x44004400] 3 f_1) (cur_1 0) (nh_1 0) [0x400040004000400, 0x440000004400, 0x44004400] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1_0 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1_0 h1 h2
theorem lb_1 : LowerBin 0x4400440044004400 [0x400040004000400, 0x440000004400, 0x44004400] g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)
def m_2 : Nat := 0x222200002222
def s_2 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_2 : Nat := 0x200000222
def ep_2 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cc_2_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_2 : Nat → List (Nat × Nat) := cc_2_0
def hc_2_0 : Nat → Nat := fun _ => 0
def nh_2 : Nat → Nat := hc_2_0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 0x222200002222 g_2 ep_2 1 1 bds_2 1 (dagTraceF 0x222200002222 [0x20200000202, 0x2200000022, 0x2222] 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 0x222200002222 g_2 ep_2 1 1 1 bds_2 (dagTraceF 0x222200002222 [0x20200000202, 0x2200000022, 0x2222] 3 f_2) (cur_2 0) (nh_2 0) [0x20200000202, 0x2200000022, 0x2222] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2_0 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2_0 h1 h2
theorem lb_2 : LowerBin 0x222200002222 [0x20200000202, 0x2200000022, 0x2222] g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)
def m_3 : Nat := 0x4444000044440000
def s_3 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_3 : Nat := 0x4000004440000
def ep_3 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cc_3_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_3 : Nat → List (Nat × Nat) := cc_3_0
def hc_3_0 : Nat → Nat := fun _ => 0
def nh_3 : Nat → Nat := hc_3_0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 0x4444000044440000 g_3 ep_3 1 1 bds_3 1 (dagTraceF 0x4444000044440000 [0x404000004040000, 0x44000000440000, 0x44440000] 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 0x4444000044440000 g_3 ep_3 1 1 1 bds_3 (dagTraceF 0x4444000044440000 [0x404000004040000, 0x44000000440000, 0x44440000] 3 f_3) (cur_3 0) (nh_3 0) [0x404000004040000, 0x44000000440000, 0x44440000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3_0 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3_0 h1 h2
theorem lb_3 : LowerBin 0x4444000044440000 [0x404000004040000, 0x44000000440000, 0x44440000] g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)
def m_4 : Nat := 0x22222222
def s_4 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_4 : Nat := 0x20222
def ep_4 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cc_4_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_4 : Nat → List (Nat × Nat) := cc_4_0
def hc_4_0 : Nat → Nat := fun _ => 0
def nh_4 : Nat → Nat := hc_4_0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 0x22222222 g_4 ep_4 1 1 bds_4 1 (dagTraceF 0x22222222 [0x2020202, 0x220022, 0x2222] 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 0x22222222 g_4 ep_4 1 1 1 bds_4 (dagTraceF 0x22222222 [0x2020202, 0x220022, 0x2222] 3 f_4) (cur_4 0) (nh_4 0) [0x2020202, 0x220022, 0x2222] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4_0 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4_0 h1 h2
theorem lb_4 : LowerBin 0x22222222 [0x2020202, 0x220022, 0x2222] g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)
def m_5 : Nat := 0x4444444400000000
def s_5 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_5 : Nat := 0x4044400000000
def ep_5 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cc_5_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_5 : Nat → List (Nat × Nat) := cc_5_0
def hc_5_0 : Nat → Nat := fun _ => 0
def nh_5 : Nat → Nat := hc_5_0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 0x4444444400000000 g_5 ep_5 1 1 bds_5 1 (dagTraceF 0x4444444400000000 [0x404040400000000, 0x44004400000000, 0x444400000000] 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 0x4444444400000000 g_5 ep_5 1 1 1 bds_5 (dagTraceF 0x4444444400000000 [0x404040400000000, 0x44004400000000, 0x444400000000] 3 f_5) (cur_5 0) (nh_5 0) [0x404040400000000, 0x44004400000000, 0x444400000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5_0 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5_0 h1 h2
theorem lb_5 : LowerBin 0x4444444400000000 [0x404040400000000, 0x44004400000000, 0x444400000000] g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)
def m_6 : Nat := 0xaaaa
def s_6 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_6 : Nat := 0x22a
def ep_6 : Nat := 0x28000000000000020800000000000002200000000000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
def cc_6_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_6 : Nat → List (Nat × Nat) := cc_6_0
def hc_6_0 : Nat → Nat := fun _ => 0
def nh_6 : Nat → Nat := hc_6_0
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_6 : Nat → Bool := dagCheckNodeV5 0xaaaa g_6 ep_6 1 1 bds_6 1 (dagTraceF 0xaaaa [0x2222, 0xa0a, 0xaa] 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV5 0xaaaa g_6 ep_6 1 1 1 bds_6 (dagTraceF 0xaaaa [0x2222, 0xa0a, 0xaa] 3 f_6) (cur_6 0) (nh_6 0) [0x2222, 0xa0a, 0xaa] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6_0 : treeBlockF 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => treeBlockF_at nb_6_0 h1 h2
theorem lb_6 : LowerBin 0xaaaa [0x2222, 0xa0a, 0xaa] g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)
def m_7 : Nat := 0xc0c00000c0c0000
def s_7 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_7 : Nat := 0x40000040c0000
def ep_7 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cc_7_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_7 : Nat → List (Nat × Nat) := cc_7_0
def hc_7_0 : Nat → Nat := fun _ => 0
def nh_7 : Nat → Nat := hc_7_0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 0xc0c00000c0c0000 g_7 ep_7 1 1 bds_7 1 (dagTraceF 0xc0c00000c0c0000 [0x404000004040000, 0xc0000000c0000, 0xc0c0000] 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 0xc0c00000c0c0000 g_7 ep_7 1 1 1 bds_7 (dagTraceF 0xc0c00000c0c0000 [0x404000004040000, 0xc0000000c0000, 0xc0c0000] 3 f_7) (cur_7 0) (nh_7 0) [0x404000004040000, 0xc0000000c0000, 0xc0c0000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7_0 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7_0 h1 h2
theorem lb_7 : LowerBin 0xc0c00000c0c0000 [0x404000004040000, 0xc0000000c0000, 0xc0c0000] g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)
def m_8 : Nat := 0xc0c0c0c00000000
def s_8 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_8 : Nat := 0x4040c00000000
def ep_8 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cc_8_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_8 : Nat → List (Nat × Nat) := cc_8_0
def hc_8_0 : Nat → Nat := fun _ => 0
def nh_8 : Nat → Nat := hc_8_0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 0xc0c0c0c00000000 g_8 ep_8 1 1 bds_8 1 (dagTraceF 0xc0c0c0c00000000 [0x404040400000000, 0xc000c00000000, 0xc0c00000000] 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 0xc0c0c0c00000000 g_8 ep_8 1 1 1 bds_8 (dagTraceF 0xc0c0c0c00000000 [0x404040400000000, 0xc000c00000000, 0xc0c00000000] 3 f_8) (cur_8 0) (nh_8 0) [0x404040400000000, 0xc000c00000000, 0xc0c00000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8_0 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8_0 h1 h2
theorem lb_8 : LowerBin 0xc0c0c0c00000000 [0x404040400000000, 0xc000c00000000, 0xc0c00000000] g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)
def m_9 : Nat := 0xcc000000cc0000
def s_9 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_9 : Nat := 0x40000004c0000
def ep_9 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cc_9_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_9 : Nat → List (Nat × Nat) := cc_9_0
def hc_9_0 : Nat → Nat := fun _ => 0
def nh_9 : Nat → Nat := hc_9_0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 0xcc000000cc0000 g_9 ep_9 1 1 bds_9 1 (dagTraceF 0xcc000000cc0000 [0x44000000440000, 0xc0000000c0000, 0xcc0000] 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 0xcc000000cc0000 g_9 ep_9 1 1 1 bds_9 (dagTraceF 0xcc000000cc0000 [0x44000000440000, 0xc0000000c0000, 0xcc0000] 3 f_9) (cur_9 0) (nh_9 0) [0x44000000440000, 0xc0000000c0000, 0xcc0000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9_0 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9_0 h1 h2
theorem lb_9 : LowerBin 0xcc000000cc0000 [0x44000000440000, 0xc0000000c0000, 0xcc0000] g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)
def m_10 : Nat := 0xcc00cc00000000
def s_10 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_10 : Nat := 0x4004c00000000
def ep_10 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cc_10_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_10 : Nat → List (Nat × Nat) := cc_10_0
def hc_10_0 : Nat → Nat := fun _ => 0
def nh_10 : Nat → Nat := hc_10_0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 0xcc00cc00000000 g_10 ep_10 1 1 bds_10 1 (dagTraceF 0xcc00cc00000000 [0x44004400000000, 0xc000c00000000, 0xcc00000000] 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 0xcc00cc00000000 g_10 ep_10 1 1 1 bds_10 (dagTraceF 0xcc00cc00000000 [0x44004400000000, 0xc000c00000000, 0xcc00000000] 3 f_10) (cur_10 0) (nh_10 0) [0x44004400000000, 0xc000c00000000, 0xcc00000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_0 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10_0 h1 h2
theorem lb_10 : LowerBin 0xcc00cc00000000 [0x44004400000000, 0xc000c00000000, 0xcc00000000] g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)
def m_11 : Nat := 0xcccc0000
def s_11 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_11 : Nat := 0x44c0000
def ep_11 : Nat := 0x480000000000000408000000000000000000000000000004400000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
def cc_11_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_11 : Nat → List (Nat × Nat) := cc_11_0
def hc_11_0 : Nat → Nat := fun _ => 0
def nh_11 : Nat → Nat := hc_11_0
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_11 : Nat → Bool := dagCheckNodeV5 0xcccc0000 g_11 ep_11 1 1 bds_11 1 (dagTraceF 0xcccc0000 [0x44440000, 0xc0c0000, 0xcc0000] 3 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV5 0xcccc0000 g_11 ep_11 1 1 1 bds_11 (dagTraceF 0xcccc0000 [0x44440000, 0xc0c0000, 0xcc0000] 3 f_11) (cur_11 0) (nh_11 0) [0x44440000, 0xc0c0000, 0xcc0000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 1 ch_11 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → ch_11 i = true := fun _ h1 h2 => treeBlockF_at nb_11_0 h1 h2
theorem lb_11 : LowerBin 0xcccc0000 [0x44440000, 0xc0c0000, 0xcc0000] g_11 4 :=
  lowerDagV5 (kn_nil) rc_11 nc_11 (by decide +kernel)
def m_12 : Nat := 0xcccc00000000
def s_12 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_12 : Nat := 0x44c00000000
def ep_12 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cc_12_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_12 : Nat → List (Nat × Nat) := cc_12_0
def hc_12_0 : Nat → Nat := fun _ => 0
def nh_12 : Nat → Nat := hc_12_0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 0xcccc00000000 g_12 ep_12 1 1 bds_12 1 (dagTraceF 0xcccc00000000 [0x444400000000, 0xc0c00000000, 0xcc00000000] 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 0xcccc00000000 g_12 ep_12 1 1 1 bds_12 (dagTraceF 0xcccc00000000 [0x444400000000, 0xc0c00000000, 0xcc00000000] 3 f_12) (cur_12 0) (nh_12 0) [0x444400000000, 0xc0c00000000, 0xcc00000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12_0 h1 h2
theorem lb_12 : LowerBin 0xcccc00000000 [0x444400000000, 0xc0c00000000, 0xcc00000000] g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)
def m_13 : Nat := 0xf0f000000000000
def s_13 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_13 : Nat := 0x107000000000000
def ep_13 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cc_13_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_13 : Nat → List (Nat × Nat) := cc_13_0
def hc_13_0 : Nat → Nat := fun _ => 0
def nh_13 : Nat → Nat := hc_13_0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 0xf0f000000000000 g_13 ep_13 1 1 bds_13 1 (dagTraceF 0xf0f000000000000 [0x505000000000000, 0x303000000000000, 0xf000000000000] 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 0xf0f000000000000 g_13 ep_13 1 1 1 bds_13 (dagTraceF 0xf0f000000000000 [0x505000000000000, 0x303000000000000, 0xf000000000000] 3 f_13) (cur_13 0) (nh_13 0) [0x505000000000000, 0x303000000000000, 0xf000000000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13_0 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13_0 h1 h2
theorem lb_13 : LowerBin 0xf0f000000000000 [0x505000000000000, 0x303000000000000, 0xf000000000000] g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)
def m_14 : Nat := 0xff000000000000
def s_14 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_14 : Nat := 0x17000000000000
def ep_14 : Nat := 0x600000000000000120000000000000014000000000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cc_14_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def cur_14 : Nat → List (Nat × Nat) := cc_14_0
def hc_14_0 : Nat → Nat := fun _ => 0
def nh_14 : Nat → Nat := hc_14_0
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_14 : Nat → Bool := dagCheckNodeV5 0xff000000000000 g_14 ep_14 1 1 bds_14 1 (dagTraceF 0xff000000000000 [0x55000000000000, 0x33000000000000, 0xf000000000000] 3 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 0xff000000000000 g_14 ep_14 1 1 1 bds_14 (dagTraceF 0xff000000000000 [0x55000000000000, 0x33000000000000, 0xf000000000000] 3 f_14) (cur_14 0) (nh_14 0) [0x55000000000000, 0x33000000000000, 0xf000000000000] 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_0 : treeBlockF 0 1 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14_0 h1 h2
theorem lb_14 : LowerBin 0xff000000000000 [0x55000000000000, 0x33000000000000, 0xf000000000000] g_14 4 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)
def m_15 : Nat := 0x2222222222222222
def s_15 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_15 : Nat := 0x2000200020222
def ep_15 : Nat := 0x22000000000000002200002000200020020000200020002020000000000000000000000000000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cc_15_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_15 : Nat → List (Nat × Nat) := cc_15_0
def hc_15_0 : Nat → Nat := fun _ => 0
def nh_15 : Nat → Nat := hc_15_0
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_15 : Nat → Bool := dagCheckNodeV5 0x2222222222222222 g_15 ep_15 1 1 bds_15 0 (dagTraceF 0x2222222222222222 [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222] 4 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 0x2222222222222222 g_15 ep_15 1 1 0 bds_15 (dagTraceF 0x2222222222222222 [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222] 4 f_15) (cur_15 0) (nh_15 0) [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222] 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x2222222222222222 g_15 ep_15 1 1 bds_15 0 (dagTraceF 0x2222222222222222 [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222] 4 f_15) cur_15 nh_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin 0x2222222222222222 [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222] g_15 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_15 nc_15 (by decide +kernel)
def m_16 : Nat := 0x4444444444444444
def s_16 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_16 : Nat := 0x4044404444444
def ep_16 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5)]
def cc_16_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_16_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_16 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_16_1 (Nat.sub p 32)) (cc_16_0 p) (Nat.blt p 32)
def hc_16_0 : Nat → Nat := unpackHintV5 0xe404000c57c000bf18000b81e4e50000000910a3c20002207831608161840000001801000000000017825819486500928645149210090000 0x1ccacab6d5d3c5280180ddd386da5aad57eb8296d69cdd4ea8432316ce 14 16383 6 63
def hc_16_1 : Nat → Nat := unpackHintV5 0x19460005a280004c80000000708284005 0x10040a16c6d0a0101365d0 13 8191 6 63
def nh_16 : Nat → Nat := fun p => Bool.rec (hc_16_1 (Nat.sub p 32)) (hc_16_0 p) (Nat.blt p 32)
def f_16 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_16 : Nat → Bool := dagCheckNodeV5 0x4444444444444444 g_16 ep_16 1 1 bds_16 43 (dagTraceF 0x4444444444444444 [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444] 6 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 0x4444444444444444 g_16 ep_16 1 1 43 bds_16 (dagTraceF 0x4444444444444444 [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444] 6 f_16) (cur_16 0) (nh_16 0) [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444] 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_0 : treeBlockF 0 32 ch_16 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_1 : treeBlockF 32 43 ch_16 = true := by decide +kernel
theorem nj_16_1 : ∀ i, 0 ≤ i → i < 43 → ch_16 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_16_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_16_1 h1 h2)
theorem nc_16 : ∀ i, 0 ≤ i → i < 43 → ch_16 i = true := nj_16_1
theorem lb_16 : LowerBin 0x4444444444444444 [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444] g_16 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_1 (kn_cons lb_3 (kn_cons lb_5 (kn_nil))))) rc_16 nc_16 (by decide +kernel)
def m_17 : Nat := 0xa0a0a0a0a0a0a0a
def s_17 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_17 : Nat := 0x2000a000a020a
def ep_17 : Nat := 0x8020000000008000002000002000a000a0008000000000000000000020000000002000000000000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cc_17_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_17_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cc_17_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_17 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_17_2 (Nat.sub p 64)) (cc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_17_0 p) (Nat.blt p 32)
def hc_17_0 : Nat → Nat := fun _ => 0
def hc_17_1 : Nat → Nat := fun _ => 0
def hc_17_2 : Nat → Nat := fun _ => 0
def nh_17 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_17_2 (Nat.sub p 64)) (hc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_17_0 p) (Nat.blt p 32)
def f_17 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_17 : Nat → Bool := dagCheckNodeV5 0xa0a0a0a0a0a0a0a g_17 ep_17 1 1 bds_17 64 (dagTraceF 0xa0a0a0a0a0a0a0a [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a] 5 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 0xa0a0a0a0a0a0a0a g_17 ep_17 1 1 64 bds_17 (dagTraceF 0xa0a0a0a0a0a0a0a [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a] 5 f_17) (cur_17 0) (nh_17 0) [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 32 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_1 : treeBlockF 32 64 ch_17 = true := by decide +kernel
theorem nj_17_1 : ∀ i, 0 ≤ i → i < 64 → ch_17 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_17_1 h1 h2)
theorem nc_17 : ∀ i, 0 ≤ i → i < 64 → ch_17 i = true := nj_17_1
theorem lb_17 : LowerBin 0xa0a0a0a0a0a0a0a [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a] g_17 6 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)
def m_18 : Nat := 0x5050505050505050
def s_18 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_18 : Nat := 0x1010105010505050
def ep_18 : Nat := 0x40400000000040000040000000004000400000000000000000000010101000100000000000000000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cc_18_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_18 : Nat → List (Nat × Nat) := cc_18_0
def hc_18_0 : Nat → Nat := fun _ => 0
def nh_18 : Nat → Nat := hc_18_0
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_18 : Nat → Bool := dagCheckNodeV5 0x5050505050505050 g_18 ep_18 1 1 bds_18 0 (dagTraceF 0x5050505050505050 [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 0x5050505050505050 g_18 ep_18 1 1 0 bds_18 (dagTraceF 0x5050505050505050 [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] 4 f_18) (cur_18 0) (nh_18 0) [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x5050505050505050 g_18 ep_18 1 1 bds_18 0 (dagTraceF 0x5050505050505050 [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] 4 f_18) cur_18 nh_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin 0x5050505050505050 [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050] g_18 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_18 nc_18 (by decide +kernel)
def m_19 : Nat := 0xaa00aa00aa00aa
def s_19 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_19 : Nat := 0x2000a000a002a
def ep_19 : Nat := 0x80020000000080000002000000000000000000002000a000a000800020000000000200000000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cc_19_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_19_2 (Nat.sub p 64)) (cc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_19_0 p) (Nat.blt p 32)
def hc_19_0 : Nat → Nat := fun _ => 0
def hc_19_1 : Nat → Nat := fun _ => 0
def hc_19_2 : Nat → Nat := fun _ => 0
def nh_19 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_19_2 (Nat.sub p 64)) (hc_19_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_19_0 p) (Nat.blt p 32)
def f_19 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_19 : Nat → Bool := dagCheckNodeV5 0xaa00aa00aa00aa g_19 ep_19 1 1 bds_19 64 (dagTraceF 0xaa00aa00aa00aa [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa] 5 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 0xaa00aa00aa00aa g_19 ep_19 1 1 64 bds_19 (dagTraceF 0xaa00aa00aa00aa [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa] 5 f_19) (cur_19 0) (nh_19 0) [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 64 ch_19 = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 64 → ch_19 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 64 → ch_19 i = true := nj_19_1
theorem lb_19 : LowerBin 0xaa00aa00aa00aa [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa] g_19 6 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)
def m_20 : Nat := 0x5500550055005500
def s_20 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_20 : Nat := 0x1100150015005500
def ep_20 : Nat := 0x400400000000400000040000000000000000000000004000400000011001000100000000000000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cc_20_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_20 : Nat → List (Nat × Nat) := cc_20_0
def hc_20_0 : Nat → Nat := fun _ => 0
def nh_20 : Nat → Nat := hc_20_0
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_20 : Nat → Bool := dagCheckNodeV5 0x5500550055005500 g_20 ep_20 1 1 bds_20 0 (dagTraceF 0x5500550055005500 [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 0x5500550055005500 g_20 ep_20 1 1 0 bds_20 (dagTraceF 0x5500550055005500 [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] 4 f_20) (cur_20 0) (nh_20 0) [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x5500550055005500 g_20 ep_20 1 1 bds_20 0 (dagTraceF 0x5500550055005500 [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] 4 f_20) cur_20 nh_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin 0x5500550055005500 [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500] g_20 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_20 nc_20 (by decide +kernel)
def m_21 : Nat := 0xaaaa0000aaaa
def s_21 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_21 : Nat := 0xa0000022a
def ep_21 : Nat := 0x22000000000000000000000000a000000280000000a0000020800000000000002200000000000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cc_21_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_21 : Nat → List (Nat × Nat) := cc_21_0
def hc_21_0 : Nat → Nat := fun _ => 0
def nh_21 : Nat → Nat := hc_21_0
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_21 : Nat → Bool := dagCheckNodeV5 0xaaaa0000aaaa g_21 ep_21 1 1 bds_21 0 (dagTraceF 0xaaaa0000aaaa [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa] 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 0xaaaa0000aaaa g_21 ep_21 1 1 0 bds_21 (dagTraceF 0xaaaa0000aaaa [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa] 4 f_21) (cur_21 0) (nh_21 0) [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa] 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xaaaa0000aaaa g_21 ep_21 1 1 bds_21 0 (dagTraceF 0xaaaa0000aaaa [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa] 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin 0xaaaa0000aaaa [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa] g_21 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_21 nc_21 (by decide +kernel)
def m_22 : Nat := 0xaaaaaaaa
def s_22 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_22 : Nat := 0xa022a
def ep_22 : Nat := 0x22000000000000a002800000000000a020800000000000002200000000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cc_22_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_22 : Nat → List (Nat × Nat) := cc_22_0
def hc_22_0 : Nat → Nat := fun _ => 0
def nh_22 : Nat → Nat := hc_22_0
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_22 : Nat → Bool := dagCheckNodeV5 0xaaaaaaaa g_22 ep_22 1 1 bds_22 0 (dagTraceF 0xaaaaaaaa [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa] 4 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 0xaaaaaaaa g_22 ep_22 1 1 0 bds_22 (dagTraceF 0xaaaaaaaa [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa] 4 f_22) (cur_22 0) (nh_22 0) [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa] 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xaaaaaaaa g_22 ep_22 1 1 bds_22 0 (dagTraceF 0xaaaaaaaa [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa] 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin 0xaaaaaaaa [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa] g_22 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_22 nc_22 (by decide +kernel)
def m_23 : Nat := 0xc0c0c0c0c0c0c0c
def s_23 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_23 : Nat := 0x4040c040c040c
def ep_23 : Nat := 0x408000000000408000000000004000800080008000000000000000000000000000000000004040004000400
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cc_23_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_23 : Nat → List (Nat × Nat) := cc_23_0
def hc_23_0 : Nat → Nat := fun _ => 0
def nh_23 : Nat → Nat := hc_23_0
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_23 : Nat → Bool := dagCheckNodeV5 0xc0c0c0c0c0c0c0c g_23 ep_23 1 1 bds_23 0 (dagTraceF 0xc0c0c0c0c0c0c0c [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c] 4 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 0xc0c0c0c0c0c0c0c g_23 ep_23 1 1 0 bds_23 (dagTraceF 0xc0c0c0c0c0c0c0c [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c] 4 f_23) (cur_23 0) (nh_23 0) [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c] 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xc0c0c0c0c0c0c0c g_23 ep_23 1 1 bds_23 0 (dagTraceF 0xc0c0c0c0c0c0c0c [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c] 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin 0xc0c0c0c0c0c0c0c [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c] g_23 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_23 nc_23 (by decide +kernel)
def m_24 : Nat := 0xc0c0c0c0c0c0c0c0
def s_24 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_24 : Nat := 0x4000404040
def ep_24 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000004000404040
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cc_24_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_24 : Nat → List (Nat × Nat) := cc_24_0
def hc_24_0 : Nat → Nat := fun _ => 0
def nh_24 : Nat → Nat := hc_24_0
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_24 : Nat → Bool := dagCheckNodeV5 0xc0c0c0c0c0c0c0c0 g_24 ep_24 1 1 bds_24 0 (dagTraceF 0xc0c0c0c0c0c0c0c0 [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0] 4 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 0xc0c0c0c0c0c0c0c0 g_24 ep_24 1 1 0 bds_24 (dagTraceF 0xc0c0c0c0c0c0c0c0 [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0] 4 f_24) (cur_24 0) (nh_24 0) [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0] 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xc0c0c0c0c0c0c0c0 g_24 ep_24 1 1 bds_24 0 (dagTraceF 0xc0c0c0c0c0c0c0c0 [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0] 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin 0xc0c0c0c0c0c0c0c0 [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0] g_24 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_24 nc_24 (by decide +kernel)
def m_25 : Nat := 0xcc00cc00cc00cc
def s_25 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_25 : Nat := 0x4004c004c004c
def ep_25 : Nat := 0x48000000000048000000000000000000000000000400080008000800000000000000000004004000400040
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cc_25_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_25 : Nat → List (Nat × Nat) := cc_25_0
def hc_25_0 : Nat → Nat := fun _ => 0
def nh_25 : Nat → Nat := hc_25_0
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_25 : Nat → Bool := dagCheckNodeV5 0xcc00cc00cc00cc g_25 ep_25 1 1 bds_25 0 (dagTraceF 0xcc00cc00cc00cc [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] 4 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 0xcc00cc00cc00cc g_25 ep_25 1 1 0 bds_25 (dagTraceF 0xcc00cc00cc00cc [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] 4 f_25) (cur_25 0) (nh_25 0) [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xcc00cc00cc00cc g_25 ep_25 1 1 bds_25 0 (dagTraceF 0xcc00cc00cc00cc [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin 0xcc00cc00cc00cc [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc] g_25 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_25 nc_25 (by decide +kernel)
def m_26 : Nat := 0x333300003333
def s_26 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_26 : Nat := 0x111300001333
def ep_26 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cc_26_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_26 : Nat → List (Nat × Nat) := cc_26_0
def hc_26_0 : Nat → Nat := fun _ => 0
def nh_26 : Nat → Nat := hc_26_0
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_26 : Nat → Bool := dagCheckNodeV5 0x333300003333 g_26 ep_26 1 1 bds_26 0 (dagTraceF 0x333300003333 [0x111100001111, 0x30300000303, 0x3300000033, 0x3333] 4 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 0x333300003333 g_26 ep_26 1 1 0 bds_26 (dagTraceF 0x333300003333 [0x111100001111, 0x30300000303, 0x3300000033, 0x3333] 4 f_26) (cur_26 0) (nh_26 0) [0x111100001111, 0x30300000303, 0x3300000033, 0x3333] 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x333300003333 g_26 ep_26 1 1 bds_26 0 (dagTraceF 0x333300003333 [0x111100001111, 0x30300000303, 0x3300000033, 0x3333] 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin 0x333300003333 [0x111100001111, 0x30300000303, 0x3300000033, 0x3333] g_26 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_26 nc_26 (by decide +kernel)
def m_27 : Nat := 0xcccc0000cccc
def s_27 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_27 : Nat := 0x44c0000444c
def ep_27 : Nat := 0x400000000000000000000000004800000008000004080000000800000000000000000000044000004440
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cc_27_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_27 : Nat → List (Nat × Nat) := cc_27_0
def hc_27_0 : Nat → Nat := fun _ => 0
def nh_27 : Nat → Nat := hc_27_0
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_27 : Nat → Bool := dagCheckNodeV5 0xcccc0000cccc g_27 ep_27 1 1 bds_27 0 (dagTraceF 0xcccc0000cccc [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] 4 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 0xcccc0000cccc g_27 ep_27 1 1 0 bds_27 (dagTraceF 0xcccc0000cccc [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] 4 f_27) (cur_27 0) (nh_27 0) [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xcccc0000cccc g_27 ep_27 1 1 bds_27 0 (dagTraceF 0xcccc0000cccc [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin 0xcccc0000cccc [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc] g_27 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_27 nc_27 (by decide +kernel)
def m_28 : Nat := 0xcccc0000cccc0000
def s_28 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_28 : Nat := 0x40000044c0000
def ep_28 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9), (m_11, s_11, 4, g_11)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x7f040001b71b546678c00000002ba1540ca2193a2a605000000012c1000038ca6b18ca317c62c8c53189a3000000004c040000000000026980130000 0xf4aa0cacdebd600d8d6830ea10ab6aac174b86b0412cba6dd502cea104ac1aba 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0x1c46c8600000008442860a28014000000 0x40040685b960089409b8210 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 0xcccc0000cccc0000 g_28 ep_28 1 1 bds_28 43 (dagTraceF 0xcccc0000cccc0000 [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000] 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 0xcccc0000cccc0000 g_28 ep_28 1 1 43 bds_28 (dagTraceF 0xcccc0000cccc0000 [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000] 6 f_28) (cur_28 0) (nh_28 0) [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000] 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin 0xcccc0000cccc0000 [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000] g_28 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_7 (kn_cons lb_9 (kn_cons lb_11 (kn_nil))))) rc_28 nc_28 (by decide +kernel)
def m_29 : Nat := 0x33333333
def s_29 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_29 : Nat := 0x11131333
def ep_29 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cc_29_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_29 : Nat → List (Nat × Nat) := cc_29_0
def hc_29_0 : Nat → Nat := fun _ => 0
def nh_29 : Nat → Nat := hc_29_0
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_29 : Nat → Bool := dagCheckNodeV5 0x33333333 g_29 ep_29 1 1 bds_29 0 (dagTraceF 0x33333333 [0x11111111, 0x3030303, 0x330033, 0x3333] 4 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 0x33333333 g_29 ep_29 1 1 0 bds_29 (dagTraceF 0x33333333 [0x11111111, 0x3030303, 0x330033, 0x3333] 4 f_29) (cur_29 0) (nh_29 0) [0x11111111, 0x3030303, 0x330033, 0x3333] 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x33333333 g_29 ep_29 1 1 bds_29 0 (dagTraceF 0x33333333 [0x11111111, 0x3030303, 0x330033, 0x3333] 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin 0x33333333 [0x11111111, 0x3030303, 0x330033, 0x3333] g_29 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_29 nc_29 (by decide +kernel)
def m_30 : Nat := 0xcccccccc
def s_30 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_30 : Nat := 0x44c444c
def ep_30 : Nat := 0x40000000000000480008000000000408000800000000000000000000000004404440
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cc_30_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_30 : Nat → List (Nat × Nat) := cc_30_0
def hc_30_0 : Nat → Nat := fun _ => 0
def nh_30 : Nat → Nat := hc_30_0
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_30 : Nat → Bool := dagCheckNodeV5 0xcccccccc g_30 ep_30 1 1 bds_30 0 (dagTraceF 0xcccccccc [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] 4 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 0xcccccccc g_30 ep_30 1 1 0 bds_30 (dagTraceF 0xcccccccc [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] 4 f_30) (cur_30 0) (nh_30 0) [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xcccccccc g_30 ep_30 1 1 bds_30 0 (dagTraceF 0xcccccccc [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin 0xcccccccc [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc] g_30 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_30 nc_30 (by decide +kernel)
def m_31 : Nat := 0xcccccccc00000000
def s_31 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_31 : Nat := 0x4044c00000000
def ep_31 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_8, s_8, 4, g_8), (m_10, s_10, 4, g_10), (m_12, s_12, 4, g_12)]
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def hc_31_0 : Nat → Nat := unpackHintV5 0x7f040001b71b546678c00000002ba1540ca2193a2a605000000012c1000038ca6b18ca317c62c8c53189a3000000004c040000000000026980130000 0xf4aa0cacdebd600d8d6830ea10ab6aac174b86b0412cba6dd502cea104ac1aba 15 32767 6 63
def hc_31_1 : Nat → Nat := unpackHintV5 0x1c46c8600000008442860a28014000000 0x40040685b960089409b8210 13 8191 6 63
def nh_31 : Nat → Nat := fun p => Bool.rec (hc_31_1 (Nat.sub p 32)) (hc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_31 : Nat → Bool := dagCheckNodeV5 0xcccccccc00000000 g_31 ep_31 1 1 bds_31 43 (dagTraceF 0xcccccccc00000000 [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000] 6 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 0xcccccccc00000000 g_31 ep_31 1 1 43 bds_31 (dagTraceF 0xcccccccc00000000 [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000] 6 f_31) (cur_31 0) (nh_31 0) [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000] 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 ch_31 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 ch_31 = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := nj_31_1
theorem lb_31 : LowerBin 0xcccccccc00000000 [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000] g_31 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_8 (kn_cons lb_10 (kn_cons lb_12 (kn_nil))))) rc_31 nc_31 (by decide +kernel)
def m_32 : Nat := 0xf000f000f000f0
def s_32 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_32 : Nat := 0x10005000500070
def ep_32 : Nat := 0x40002000000040000000200000000000000000000000000000000000100000000000200010005000500040
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cc_32_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_32_2 (Nat.sub p 64)) (cc_32_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := fun _ => 0
def hc_32_1 : Nat → Nat := fun _ => 0
def hc_32_2 : Nat → Nat := fun _ => 0
def nh_32 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_32_2 (Nat.sub p 64)) (hc_32_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_32 : Nat → Bool := dagCheckNodeV5 0xf000f000f000f0 g_32 ep_32 1 1 bds_32 64 (dagTraceF 0xf000f000f000f0 [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0] 5 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 0xf000f000f000f0 g_32 ep_32 1 1 64 bds_32 (dagTraceF 0xf000f000f000f0 [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0] 5 f_32) (cur_32 0) (nh_32 0) [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 64 ch_32 = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 64 → ch_32 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 64 → ch_32 i = true := nj_32_1
theorem lb_32 : LowerBin 0xf000f000f000f0 [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0] g_32 6 :=
  lowerDagV5 (kn_nil) rc_32 nc_32 (by decide +kernel)
def m_33 : Nat := 0xf000f000f000f00
def s_33 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_33 : Nat := 0x100050005000700
def ep_33 : Nat := 0x400020000000400000002000000000000000000000000000000000001000000000002000100050005000400
def bds_33 : List (Nat × List Nat × Nat × Nat) := []
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cc_33_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_33_2 (Nat.sub p 64)) (cc_33_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := fun _ => 0
def hc_33_1 : Nat → Nat := fun _ => 0
def hc_33_2 : Nat → Nat := fun _ => 0
def nh_33 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_33_2 (Nat.sub p 64)) (hc_33_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 0xf000f000f000f00 g_33 ep_33 1 1 bds_33 64 (dagTraceF 0xf000f000f000f00 [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00] 5 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 0xf000f000f000f00 g_33 ep_33 1 1 64 bds_33 (dagTraceF 0xf000f000f000f00 [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00] 5 f_33) (cur_33 0) (nh_33 0) [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 64 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 64 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 64 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin 0xf000f000f000f00 [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00] g_33 6 :=
  lowerDagV5 (kn_nil) rc_33 nc_33 (by decide +kernel)
def m_34 : Nat := 0xf0f00000f0f0
def s_34 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_34 : Nat := 0x105000005070
def ep_34 : Nat := 0x402000000000000000000000004000000020000000000000000000001000000000200000105000005040
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cc_34_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_34_2 (Nat.sub p 64)) (cc_34_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_34_0 p) (Nat.blt p 32)
def hc_34_0 : Nat → Nat := fun _ => 0
def hc_34_1 : Nat → Nat := fun _ => 0
def hc_34_2 : Nat → Nat := fun _ => 0
def nh_34 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_34_2 (Nat.sub p 64)) (hc_34_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_34 : Nat → Bool := dagCheckNodeV5 0xf0f00000f0f0 g_34 ep_34 1 1 bds_34 64 (dagTraceF 0xf0f00000f0f0 [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0] 5 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 0xf0f00000f0f0 g_34 ep_34 1 1 64 bds_34 (dagTraceF 0xf0f00000f0f0 [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0] 5 f_34) (cur_34 0) (nh_34 0) [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 ch_34 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 64 ch_34 = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 64 → ch_34 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 64 → ch_34 i = true := nj_34_1
theorem lb_34 : LowerBin 0xf0f00000f0f0 [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0] g_34 6 :=
  lowerDagV5 (kn_nil) rc_34 nc_34 (by decide +kernel)
def m_35 : Nat := 0xf0f00000f0f0000
def s_35 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_35 : Nat := 0x1070000050f0000
def ep_35 : Nat := 0x4080000000000000000000000060000000a0000000000000000000001020000000000000104000005000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cc_35_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_35 : Nat → List (Nat × Nat) := cc_35_0
def hc_35_0 : Nat → Nat := fun _ => 0
def nh_35 : Nat → Nat := hc_35_0
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_35 : Nat → Bool := dagCheckNodeV5 0xf0f00000f0f0000 g_35 ep_35 1 1 bds_35 0 (dagTraceF 0xf0f00000f0f0000 [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000] 4 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 0xf0f00000f0f0000 g_35 ep_35 1 1 0 bds_35 (dagTraceF 0xf0f00000f0f0000 [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000] 4 f_35) (cur_35 0) (nh_35 0) [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000] 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xf0f00000f0f0000 g_35 ep_35 1 1 bds_35 0 (dagTraceF 0xf0f00000f0f0000 [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000] 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin 0xf0f00000f0f0000 [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000] g_35 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_35 nc_35 (by decide +kernel)
def m_36 : Nat := 0xf0f0f0f0
def s_36 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_36 : Nat := 0x10505070
def ep_36 : Nat := 0x40200000000000400020000000000000000000000000100000200000000010505040
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cc_36_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_36_2 (Nat.sub p 64)) (cc_36_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_36_0 p) (Nat.blt p 32)
def hc_36_0 : Nat → Nat := fun _ => 0
def hc_36_1 : Nat → Nat := fun _ => 0
def hc_36_2 : Nat → Nat := fun _ => 0
def nh_36 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_36_2 (Nat.sub p 64)) (hc_36_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_36 : Nat → Bool := dagCheckNodeV5 0xf0f0f0f0 g_36 ep_36 1 1 bds_36 64 (dagTraceF 0xf0f0f0f0 [0x50505050, 0x30303030, 0xf000f0, 0xf0f0] 5 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 0xf0f0f0f0 g_36 ep_36 1 1 64 bds_36 (dagTraceF 0xf0f0f0f0 [0x50505050, 0x30303030, 0xf000f0, 0xf0f0] 5 f_36) (cur_36 0) (nh_36 0) [0x50505050, 0x30303030, 0xf000f0, 0xf0f0] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 ch_36 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 64 ch_36 = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 64 → ch_36 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 64 → ch_36 i = true := nj_36_1
theorem lb_36 : LowerBin 0xf0f0f0f0 [0x50505050, 0x30303030, 0xf000f0, 0xf0f0] g_36 6 :=
  lowerDagV5 (kn_nil) rc_36 nc_36 (by decide +kernel)
def m_37 : Nat := 0xff000000ff00
def s_37 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_37 : Nat := 0x150000005700
def ep_37 : Nat := 0x420000000000000000000000000000000000000004000000020000001000000002000000150000005400
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cc_37_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_37_2 (Nat.sub p 64)) (cc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_37_0 p) (Nat.blt p 32)
def hc_37_0 : Nat → Nat := fun _ => 0
def hc_37_1 : Nat → Nat := fun _ => 0
def hc_37_2 : Nat → Nat := fun _ => 0
def nh_37 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_37_2 (Nat.sub p 64)) (hc_37_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_37 : Nat → Bool := dagCheckNodeV5 0xff000000ff00 g_37 ep_37 1 1 bds_37 64 (dagTraceF 0xff000000ff00 [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00] 5 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 0xff000000ff00 g_37 ep_37 1 1 64 bds_37 (dagTraceF 0xff000000ff00 [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00] 5 f_37) (cur_37 0) (nh_37 0) [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 ch_37 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 64 ch_37 = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 64 → ch_37 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 64 → ch_37 i = true := nj_37_1
theorem lb_37 : LowerBin 0xff000000ff00 [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00] g_37 6 :=
  lowerDagV5 (kn_nil) rc_37 nc_37 (by decide +kernel)
def m_38 : Nat := 0xff000000ff0000
def s_38 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_38 : Nat := 0x170000005f0000
def ep_38 : Nat := 0x4800000000000000000000000000000000000000060000000a000000120000000000000014000000500000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cc_38_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_38 : Nat → List (Nat × Nat) := cc_38_0
def hc_38_0 : Nat → Nat := fun _ => 0
def nh_38 : Nat → Nat := hc_38_0
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_38 : Nat → Bool := dagCheckNodeV5 0xff000000ff0000 g_38 ep_38 1 1 bds_38 0 (dagTraceF 0xff000000ff0000 [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000] 4 f_38) cur_38 nh_38
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 0xff000000ff0000 g_38 ep_38 1 1 0 bds_38 (dagTraceF 0xff000000ff0000 [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000] 4 f_38) (cur_38 0) (nh_38 0) [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000] 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xff000000ff0000 g_38 ep_38 1 1 bds_38 0 (dagTraceF 0xff000000ff0000 [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000] 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin 0xff000000ff0000 [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000] g_38 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_38 nc_38 (by decide +kernel)
def m_39 : Nat := 0xff00ff00
def s_39 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_39 : Nat := 0x15005700
def ep_39 : Nat := 0x42000000000000000000000000000400020000000000100002000000000015005400
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cc_39_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_39_2 (Nat.sub p 64)) (cc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_39_0 p) (Nat.blt p 32)
def hc_39_0 : Nat → Nat := fun _ => 0
def hc_39_1 : Nat → Nat := fun _ => 0
def hc_39_2 : Nat → Nat := fun _ => 0
def nh_39 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_39_2 (Nat.sub p 64)) (hc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_39 : Nat → Bool := dagCheckNodeV5 0xff00ff00 g_39 ep_39 1 1 bds_39 64 (dagTraceF 0xff00ff00 [0x55005500, 0x33003300, 0xf000f00, 0xff00] 5 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 0xff00ff00 g_39 ep_39 1 1 64 bds_39 (dagTraceF 0xff00ff00 [0x55005500, 0x33003300, 0xf000f00, 0xff00] 5 f_39) (cur_39 0) (nh_39 0) [0x55005500, 0x33003300, 0xf000f00, 0xff00] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 ch_39 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 64 ch_39 = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 64 → ch_39 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 64 → ch_39 i = true := nj_39_1
theorem lb_39 : LowerBin 0xff00ff00 [0x55005500, 0x33003300, 0xf000f00, 0xff00] g_39 6 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)
def m_40 : Nat := 0xffff
def s_40 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_40 : Nat := 0x577f
def ep_40 : Nat := 0x28000000000000020800000000000002200000000000005440
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cc_40_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_40 : Nat → List (Nat × Nat) := cc_40_0
def hc_40_0 : Nat → Nat := fun _ => 0
def nh_40 : Nat → Nat := hc_40_0
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_40 : Nat → Bool := dagCheckNodeV5 0xffff g_40 ep_40 1 1 bds_40 0 (dagTraceF 0xffff [0x5555, 0x3333, 0xf0f, 0xff] 4 f_40) cur_40 nh_40
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 0xffff g_40 ep_40 1 1 0 bds_40 (dagTraceF 0xffff [0x5555, 0x3333, 0xf0f, 0xff] 4 f_40) (cur_40 0) (nh_40 0) [0x5555, 0x3333, 0xf0f, 0xff] 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xffff g_40 ep_40 1 1 bds_40 0 (dagTraceF 0xffff [0x5555, 0x3333, 0xf0f, 0xff] 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin 0xffff [0x5555, 0x3333, 0xf0f, 0xff] g_40 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_40 nc_40 (by decide +kernel)
def m_41 : Nat := 0xffff0000
def s_41 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_41 : Nat := 0x155f0000
def ep_41 : Nat := 0x4a000000000000040a000000000000100000000000000015500000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cc_41_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_41 : Nat → List (Nat × Nat) := cc_41_0
def hc_41_0 : Nat → Nat := fun _ => 0
def nh_41 : Nat → Nat := hc_41_0
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_41 : Nat → Bool := dagCheckNodeV5 0xffff0000 g_41 ep_41 1 1 bds_41 0 (dagTraceF 0xffff0000 [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] 4 f_41) cur_41 nh_41
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 0xffff0000 g_41 ep_41 1 1 0 bds_41 (dagTraceF 0xffff0000 [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] 4 f_41) (cur_41 0) (nh_41 0) [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xffff0000 g_41 ep_41 1 1 bds_41 0 (dagTraceF 0xffff0000 [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin 0xffff0000 [0x55550000, 0x33330000, 0xf0f0000, 0xff0000] g_41 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_41 nc_41 (by decide +kernel)
def m_42 : Nat := 0xffff00000000
def s_42 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_42 : Nat := 0x155f00000000
def ep_42 : Nat := 0x4a000000000000040a0000000000001000000000000000155000000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cc_42_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_42 : Nat → List (Nat × Nat) := cc_42_0
def hc_42_0 : Nat → Nat := fun _ => 0
def nh_42 : Nat → Nat := hc_42_0
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_42 : Nat → Bool := dagCheckNodeV5 0xffff00000000 g_42 ep_42 1 1 bds_42 0 (dagTraceF 0xffff00000000 [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000] 4 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 0xffff00000000 g_42 ep_42 1 1 0 bds_42 (dagTraceF 0xffff00000000 [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000] 4 f_42) (cur_42 0) (nh_42 0) [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000] 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xffff00000000 g_42 ep_42 1 1 bds_42 0 (dagTraceF 0xffff00000000 [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000] 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin 0xffff00000000 [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000] g_42 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_42 nc_42 (by decide +kernel)
def m_43 : Nat := 0xffff000000000000
def s_43 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_43 : Nat := 0x1117000000000000
def ep_43 : Nat := 0x6000000000000000600000000000011120000000000001114000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cc_43_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_43 : Nat → List (Nat × Nat) := cc_43_0
def hc_43_0 : Nat → Nat := fun _ => 0
def nh_43 : Nat → Nat := hc_43_0
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_43 : Nat → Bool := dagCheckNodeV5 0xffff000000000000 g_43 ep_43 1 1 bds_43 0 (dagTraceF 0xffff000000000000 [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] 4 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 0xffff000000000000 g_43 ep_43 1 1 0 bds_43 (dagTraceF 0xffff000000000000 [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] 4 f_43) (cur_43 0) (nh_43 0) [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xffff000000000000 g_43 ep_43 1 1 bds_43 0 (dagTraceF 0xffff000000000000 [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin 0xffff000000000000 [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000] g_43 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_43 nc_43 (by decide +kernel)
def m_44 : Nat := 0x4444111144441111
def s_44 : List Nat := [0x111100001111, 0x404010104040101, 0x44001100440011, 0x44441111]
def g_44 : Nat := 0x4111104441111
def ep_44 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cc_44_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_44 : Nat → List (Nat × Nat) := cc_44_0
def hc_44_0 : Nat → Nat := unpackHintV5 0x1 0x1 2 3 1 1
def nh_44 : Nat → Nat := hc_44_0
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_44 : Nat → Bool := dagCheckNodeV5 0x4444111144441111 g_44 ep_44 1 1 bds_44 0 (dagTraceF 0x4444111144441111 [0x111100001111, 0x404010104040101, 0x44001100440011, 0x44441111] 4 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 0x4444111144441111 g_44 ep_44 1 1 0 bds_44 (dagTraceF 0x4444111144441111 [0x111100001111, 0x404010104040101, 0x44001100440011, 0x44441111] 4 f_44) (cur_44 0) (nh_44 0) [0x111100001111, 0x404010104040101, 0x44001100440011, 0x44441111] 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x4444111144441111 g_44 ep_44 1 1 bds_44 0 (dagTraceF 0x4444111144441111 [0x111100001111, 0x404010104040101, 0x44001100440011, 0x44441111] 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin 0x4444111144441111 [0x111100001111, 0x404010104040101, 0x44001100440011, 0x44441111] g_44 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_44 nc_44 (by decide +kernel)
def m_45 : Nat := 0x4444444411111111
def s_45 : List Nat := [0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111]
def g_45 : Nat := 0x4044411111111
def ep_45 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cc_45_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_45 : Nat → List (Nat × Nat) := cc_45_0
def hc_45_0 : Nat → Nat := unpackHintV5 0x1 0x1 2 3 1 1
def nh_45 : Nat → Nat := hc_45_0
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_45 : Nat → Bool := dagCheckNodeV5 0x4444444411111111 g_45 ep_45 1 1 bds_45 0 (dagTraceF 0x4444444411111111 [0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111] 4 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 0x4444444411111111 g_45 ep_45 1 1 0 bds_45 (dagTraceF 0x4444444411111111 [0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111] 4 f_45) (cur_45 0) (nh_45 0) [0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111] 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x4444444411111111 g_45 ep_45 1 1 bds_45 0 (dagTraceF 0x4444444411111111 [0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111] 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin 0x4444444411111111 [0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111] g_45 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_45 nc_45 (by decide +kernel)
def m_46 : Nat := 0x8888222288882222
def s_46 : List Nat := [0x222200002222, 0x808020208080202, 0x88002200880022, 0x88882222]
def g_46 : Nat := 0x200080222
def ep_46 : Nat := 0x8022000000000000000000000000200080020000000020008020000000000000000000000000000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cc_46_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c6709862488220809f17c1f07c1e174594641905c96158160581515050440100388d107001 0xc46178c2d187140d899a1030985c30b688e0c1a184a4c8c8105018183a306a60c5108180c2046907d00c9808202460348049a7a3fec7798deb19d03f9876f0dd619a82f4856509c211800f 10 1023 4 15 10 1023 15 32767
def cur_46 : Nat → List (Nat × Nat) := cc_46_0
def hc_46_0 : Nat → Nat := unpackHintV5 0xa63664d000000000025830000000930e10f792db0d00000000001a430000000660d5cf4c2cfcd00000000000f030000000390ca8f01a4001 0x4456a232d5118ab54196aa0c55aa0cb55060202022003 14 16383 6 63
def nh_46 : Nat → Nat := hc_46_0
def f_46 : Nat → Nat × Nat := unpackForestF 0x18fc31de940d099a10031bdd30b8616d10319843f087709321204140086ed8c1a983144086610bc2159b48368064c02138e301a4024d0211800f 5 10
def ch_46 : Nat → Bool := dagCheckNodeV5 0x8888222288882222 g_46 ep_46 1 1 bds_46 31 (dagTraceF 0x8888222288882222 [0x222200002222, 0x808020208080202, 0x88002200880022, 0x88882222] 5 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 0x8888222288882222 g_46 ep_46 1 1 31 bds_46 (dagTraceF 0x8888222288882222 [0x222200002222, 0x808020208080202, 0x88002200880022, 0x88882222] 5 f_46) (cur_46 0) (nh_46 0) [0x222200002222, 0x808020208080202, 0x88002200880022, 0x88882222] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 31 ch_46 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 31 → ch_46 i = true := fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2
theorem lb_46 : LowerBin 0x8888222288882222 [0x222200002222, 0x808020208080202, 0x88002200880022, 0x88882222] g_46 6 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_46 nc_46 (by decide +kernel)
def m_47 : Nat := 0x8888888822222222
def s_47 : List Nat := [0x22222222, 0x808080802020202, 0x88008800220022, 0x888800002222]
def g_47 : Nat := 0x800020222
def ep_47 : Nat := 0x8000002200000000800020020000000080002020000000000000000000000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0280a02719862488220809f17c1f07c1e174594641905c96158160581515050440100388d107001 0xc46178c2d18714cda81a1030985c30b688e4c1a984a4c8c80c4c20203a306860c9108980d2046907d0049018302460308051a7a3fec7798deb19d13f9a76f4dd699a92f4a56549c291800f 10 1023 4 15 10 1023 15 32767
def cur_47 : Nat → List (Nat × Nat) := cc_47_0
def hc_47_0 : Nat → Nat := unpackHintV5 0xaa3674d000000000026830000000970e20f7b35b8d00000000001ac30000000680d64f4c34fcd00000000000f030000000390ca8f01a4001 0x4456a232d51188ad4465aa23115a88cb54460202020203 14 16383 6 63
def nh_47 : Nat → Nat := hc_47_0
def f_47 : Nat → Nat × Nat := unpackForestF 0x18fc31de94cd281a10031bdd30b8616d10319853f0a77093212040400a6ed8c1a1832440a6614bc2959b48368060c02938e30184028d0291800f 5 10
def ch_47 : Nat → Bool := dagCheckNodeV5 0x8888888822222222 g_47 ep_47 1 1 bds_47 31 (dagTraceF 0x8888888822222222 [0x22222222, 0x808080802020202, 0x88008800220022, 0x888800002222] 5 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 0x8888888822222222 g_47 ep_47 1 1 31 bds_47 (dagTraceF 0x8888888822222222 [0x22222222, 0x808080802020202, 0x88008800220022, 0x888800002222] 5 f_47) (cur_47 0) (nh_47 0) [0x22222222, 0x808080802020202, 0x88008800220022, 0x888800002222] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 31 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 31 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2
theorem lb_47 : LowerBin 0x8888888822222222 [0x22222222, 0x808080802020202, 0x88008800220022, 0x888800002222] g_47 6 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_47 nc_47 (by decide +kernel)
def m_48 : Nat := 0xaaaa00000000aaaa
def s_48 : List Nat := [0x2222000000002222, 0xa0a000000000a0a, 0xaa0000000000aa, 0xaaaa]
def g_48 : Nat := 0x200000000022a
def ep_48 : Nat := 0x2000000000028000200000000020800020000000002200000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0280a02719862488220809f17c1f07c1e174594641905c96158160581515050440100388d107001 0xc46178c2d18714cda81a1030985c30b688e4c1a984a4c8c80c4c20203a306860c9108980d2046907d0049018302460308051a7a3fec7798deb19d13f9a76f4dd699a92f4a56549c291800f 10 1023 4 15 10 1023 15 32767
def cur_48 : Nat → List (Nat × Nat) := cc_48_0
def hc_48_0 : Nat → Nat := unpackHintV5 0xaa3674d000000000026830000000970e20f7b35b8d00000000001ac30000000680d64f4c34fcd00000000000f030000000390ca8f01a4001 0x4456a232d51188ad4465aa23115a88cb54460202020203 14 16383 6 63
def nh_48 : Nat → Nat := hc_48_0
def f_48 : Nat → Nat × Nat := unpackForestF 0x18fc31de94cd281a10031bdd30b8616d10319853f0a77093212040400a6ed8c1a1832440a6614bc2959b48368060c02938e30184028d0291800f 5 10
def ch_48 : Nat → Bool := dagCheckNodeV5 0xaaaa00000000aaaa g_48 ep_48 1 1 bds_48 31 (dagTraceF 0xaaaa00000000aaaa [0x2222000000002222, 0xa0a000000000a0a, 0xaa0000000000aa, 0xaaaa] 5 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 0xaaaa00000000aaaa g_48 ep_48 1 1 31 bds_48 (dagTraceF 0xaaaa00000000aaaa [0x2222000000002222, 0xa0a000000000a0a, 0xaa0000000000aa, 0xaaaa] 5 f_48) (cur_48 0) (nh_48 0) [0x2222000000002222, 0xa0a000000000a0a, 0xaa0000000000aa, 0xaaaa] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 31 ch_48 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 31 → ch_48 i = true := fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2
theorem lb_48 : LowerBin 0xaaaa00000000aaaa [0x2222000000002222, 0xa0a000000000a0a, 0xaa0000000000aa, 0xaaaa] g_48 6 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_48 nc_48 (by decide +kernel)
def m_49 : Nat := 0x3333000000003333
def s_49 : List Nat := [0x1111000000001111, 0x303000000000303, 0x33000000000033, 0x3333]
def g_49 : Nat := 0x1113000000001333
def ep_49 : Nat := 0x2000000000020000200000000020000000000000000001110000000001000
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44890e8701 0x192430919242090d24209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def cur_49 : Nat → List (Nat × Nat) := cc_49_0
def hc_49_0 : Nat → Nat := fun _ => 0
def nh_49 : Nat → Nat := hc_49_0
def f_49 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6c43a492209086c00f 3 10
def ch_49 : Nat → Bool := dagCheckNodeV5 0x3333000000003333 g_49 ep_49 1 1 bds_49 10 (dagTraceF 0x3333000000003333 [0x1111000000001111, 0x303000000000303, 0x33000000000033, 0x3333] 4 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 0x3333000000003333 g_49 ep_49 1 1 10 bds_49 (dagTraceF 0x3333000000003333 [0x1111000000001111, 0x303000000000303, 0x33000000000033, 0x3333] 4 f_49) (cur_49 0) (nh_49 0) [0x1111000000001111, 0x303000000000303, 0x33000000000033, 0x3333] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 10 ch_49 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 10 → ch_49 i = true := fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2
theorem lb_49 : LowerBin 0x3333000000003333 [0x1111000000001111, 0x303000000000303, 0x33000000000033, 0x3333] g_49 5 :=
  lowerDagV5 (kn_nil) rc_49 nc_49 (by decide +kernel)
def m_50 : Nat := 0xc00cc00cc00cc00c
def s_50 : List Nat := [0x4004400440044004, 0xc000c000c000c, 0xc00c0000c00c, 0xc00cc00c]
def g_50 : Nat := 0x4000c000c400c
def ep_50 : Nat := 0x8400000000008000040000000000000000000000000000000000000000000000000000004000000004000
def bds_50 : List (Nat × List Nat × Nat × Nat) := []
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cc_50_2 : Nat → List (Nat × Nat) := fun _ => []
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_50_2 (Nat.sub p 64)) (cc_50_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_50_0 p) (Nat.blt p 32)
def hc_50_0 : Nat → Nat := fun _ => 0
def hc_50_1 : Nat → Nat := fun _ => 0
def hc_50_2 : Nat → Nat := fun _ => 0
def nh_50 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_50_2 (Nat.sub p 64)) (hc_50_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_50 : Nat → Bool := dagCheckNodeV5 0xc00cc00cc00cc00c g_50 ep_50 1 1 bds_50 64 (dagTraceF 0xc00cc00cc00cc00c [0x4004400440044004, 0xc000c000c000c, 0xc00c0000c00c, 0xc00cc00c] 5 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 0xc00cc00cc00cc00c g_50 ep_50 1 1 64 bds_50 (dagTraceF 0xc00cc00cc00cc00c [0x4004400440044004, 0xc000c000c000c, 0xc00c0000c00c, 0xc00cc00c] 5 f_50) (cur_50 0) (nh_50 0) [0x4004400440044004, 0xc000c000c000c, 0xc00c0000c00c, 0xc00cc00c] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 ch_50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 64 ch_50 = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 64 → ch_50 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 64 → ch_50 i = true := nj_50_1
theorem lb_50 : LowerBin 0xc00cc00cc00cc00c [0x4004400440044004, 0xc000c000c000c, 0xc00c0000c00c, 0xc00cc00c] g_50 6 :=
  lowerDagV5 (kn_nil) rc_50 nc_50 (by decide +kernel)
def m_51 : Nat := 0xcccc00000000cccc
def s_51 : List Nat := [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc]
def g_51 : Nat := 0x400000000444c
def ep_51 : Nat := 0x4000000000008000400000000000800000000000000000004000000004440
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cc_51_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def cur_51 : Nat → List (Nat × Nat) := cc_51_0
def hc_51_0 : Nat → Nat := fun _ => 0
def nh_51 : Nat → Nat := hc_51_0
def f_51 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_51 : Nat → Bool := dagCheckNodeV5 0xcccc00000000cccc g_51 ep_51 1 1 bds_51 7 (dagTraceF 0xcccc00000000cccc [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc] 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 0xcccc00000000cccc g_51 ep_51 1 1 7 bds_51 (dagTraceF 0xcccc00000000cccc [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc] 4 f_51) (cur_51 0) (nh_51 0) [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 7 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 7 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2
theorem lb_51 : LowerBin 0xcccc00000000cccc [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc] g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)
def m_52 : Nat := 0x606060606060606
def s_52 : List Nat := [0x202020202020202, 0x6000600060006, 0x60600000606, 0x6060606]
def g_52 : Nat := 0x6040604060606
def ep_52 : Nat := 0x400020000000400000002000006000200020000000000000000000000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cc_52_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def cur_52 : Nat → List (Nat × Nat) := cc_52_0
def hc_52_0 : Nat → Nat := fun _ => 0
def nh_52 : Nat → Nat := hc_52_0
def f_52 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_52 : Nat → Bool := dagCheckNodeV5 0x606060606060606 g_52 ep_52 1 1 bds_52 10 (dagTraceF 0x606060606060606 [0x202020202020202, 0x6000600060006, 0x60600000606, 0x6060606] 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 0x606060606060606 g_52 ep_52 1 1 10 bds_52 (dagTraceF 0x606060606060606 [0x202020202020202, 0x6000600060006, 0x60600000606, 0x6060606] 4 f_52) (cur_52 0) (nh_52 0) [0x202020202020202, 0x6000600060006, 0x60600000606, 0x6060606] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : treeBlockF 0 10 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 10 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52_0 h1 h2
theorem lb_52 : LowerBin 0x606060606060606 [0x202020202020202, 0x6000600060006, 0x60600000606, 0x6060606] g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)
def m_53 : Nat := 0xc0c03030c0c0303
def s_53 : List Nat := [0x404010104040101, 0x30300000303, 0xc0003000c0003, 0xc0c0303]
def g_53 : Nat := 0x40103040c0303
def ep_53 : Nat := 0x408020000000000000000000004000200080000000000000000000000000000000000000004010004000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cc_53_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294241902408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc61a492e126a34bc69bd132926028b04910c1e1234147868d0d22a2403c7068c090e101434182850906121d34309841104127a3fec77c8deb19d03f987720dd619a82f4856809c211800f 10 1023 4 15 10 1023 15 32767
def cur_53 : Nat → List (Nat × Nat) := cc_53_0
def hc_53_0 : Nat → Nat := unpackHintV5 0xb0368cd943e4430000000000000000023057f35c8d633d80300000000000000000174350350cd343cc43000000000000000000b8301b4001 0x1544aa24455b0a88d45222ad9511a8a4455b202020200221 14 16383 6 63
def nh_53 : Nat → Nat := hc_53_0
def f_53 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b689a8d2c925828bc696090319843f087610dd8a2303c7868c0d1a1a3024086610bc215842712682130a12084418482090211800f 5 10
def ch_53 : Nat → Bool := dagCheckNodeV5 0xc0c03030c0c0303 g_53 ep_53 1 1 bds_53 31 (dagTraceF 0xc0c03030c0c0303 [0x404010104040101, 0x30300000303, 0xc0003000c0003, 0xc0c0303] 5 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 0xc0c03030c0c0303 g_53 ep_53 1 1 31 bds_53 (dagTraceF 0xc0c03030c0c0303 [0x404010104040101, 0x30300000303, 0xc0003000c0003, 0xc0c0303] 5 f_53) (cur_53 0) (nh_53 0) [0x404010104040101, 0x30300000303, 0xc0003000c0003, 0xc0c0303] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 31 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 31 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2
theorem lb_53 : LowerBin 0xc0c03030c0c0303 [0x404010104040101, 0x30300000303, 0xc0003000c0003, 0xc0c0303] g_53 6 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_53 nc_53 (by decide +kernel)
def m_54 : Nat := 0xc0c0c0c03030303
def s_54 : List Nat := [0x404040401010101, 0x3030303, 0xc000c00030003, 0xc0c00000303]
def g_54 : Nat := 0x4040c01030303
def ep_54 : Nat := 0x408000002000004000800020000000000000000000000000000000000000004040001000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cc_54_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e126634bc69bd134946124b04914c1e9234147a68d4d2322413c7268c050e901534182854906921e343298451040a7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_54 : Nat → List (Nat × Nat) := cc_54_0
def hc_54_0 : Nat → Nat := unpackHintV5 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1544aa24455b0aa2551222ad85512a891156c202020202021 14 16383 6 63
def nh_54 : Nat → Nat := hc_54_0
def f_54 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b68964a331a5924bc696090319853f0a7614dd922313c7a68c4d1a9a30140a6614bc295852714682530a9209441a482050291800f 5 10
def ch_54 : Nat → Bool := dagCheckNodeV5 0xc0c0c0c03030303 g_54 ep_54 1 1 bds_54 31 (dagTraceF 0xc0c0c0c03030303 [0x404040401010101, 0x3030303, 0xc000c00030003, 0xc0c00000303] 5 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 0xc0c0c0c03030303 g_54 ep_54 1 1 31 bds_54 (dagTraceF 0xc0c0c0c03030303 [0x404040401010101, 0x3030303, 0xc000c00030003, 0xc0c00000303] 5 f_54) (cur_54 0) (nh_54 0) [0x404040401010101, 0x3030303, 0xc000c00030003, 0xc0c00000303] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 31 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 31 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2
theorem lb_54 : LowerBin 0xc0c0c0c03030303 [0x404040401010101, 0x3030303, 0xc000c00030003, 0xc0c00000303] g_54 6 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_54 nc_54 (by decide +kernel)
def m_55 : Nat := 0xf0f000000000f0f
def s_55 : List Nat := [0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f]
def g_55 : Nat := 0x10700000000070f
def ep_55 : Nat := 0x6000000000008000000000000000001020000000002000104000000000400
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e126634bc69bd134946124b04914c1e9234147a68d4d2322413c7268c050e901534182854906921e343298451040a7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_55 : Nat → List (Nat × Nat) := cc_55_0
def hc_55_0 : Nat → Nat := unpackHintV5 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1544aa24455b0aa2551222ad85512a891156c202020202021 14 16383 6 63
def nh_55 : Nat → Nat := hc_55_0
def f_55 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b68964a331a5924bc696090319853f0a7614dd922313c7a68c4d1a9a30140a6614bc295852714682530a9209441a482050291800f 5 10
def ch_55 : Nat → Bool := dagCheckNodeV5 0xf0f000000000f0f g_55 ep_55 1 1 bds_55 31 (dagTraceF 0xf0f000000000f0f [0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f] 5 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 0xf0f000000000f0f g_55 ep_55 1 1 31 bds_55 (dagTraceF 0xf0f000000000f0f [0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f] 5 f_55) (cur_55 0) (nh_55 0) [0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 31 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 31 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2
theorem lb_55 : LowerBin 0xf0f000000000f0f [0x505000000000505, 0x303000000000303, 0xf00000000000f, 0xf0f] g_55 6 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_55 nc_55 (by decide +kernel)
def m_56 : Nat := 0x6060606060606060
def s_56 : List Nat := [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060]
def g_56 : Nat := 0x4000404060
def ep_56 : Nat := 0x40402000000040000040200000004000400020000000000000000000000000000000000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c6709862488220809f17c1f0785e074594641905c96158160545505050440100388d107001 0xc26174839a45920d879a0c311c5c20b468e0c1a104b488a7904c18103a386a40c4d08100c20449078e0d18081022703480492792fea57949ea91d02f9856f09d611a81f4836505c209800f 10 1023 4 15 10 1023 15 32767
def cur_56 : Nat → List (Nat × Nat) := cc_56_0
def hc_56_0 : Nat → Nat := unpackHintV5 0xa62e64d000000000025830000000930e10f792db0d00000000001a430000000660d5cf4c2cfcd00000000000f030000000390ca8f01a4001 0x1456a292d514a2b51496a8a515a8a4b54522002200221 14 16383 6 63
def nh_56 : Nat → Nat := hc_56_0
def f_56 : Nat → Nat × Nat := unpackForestF 0x14bc295eb48d079a0c0293de38b84168d0291842f08570d2209e4130084ed8e1a9031340846107c20d9a48347068c020b8d381a402490209800f 5 10
def ch_56 : Nat → Bool := dagCheckNodeV5 0x6060606060606060 g_56 ep_56 1 1 bds_56 31 (dagTraceF 0x6060606060606060 [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060] 5 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 0x6060606060606060 g_56 ep_56 1 1 31 bds_56 (dagTraceF 0x6060606060606060 [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060] 5 f_56) (cur_56 0) (nh_56 0) [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 31 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 31 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2
theorem lb_56 : LowerBin 0x6060606060606060 [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060] g_56 6 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_56 nc_56 (by decide +kernel)
def m_57 : Nat := 0xc0c03030c0c03030
def s_57 : List Nat := [0x4040101040401010, 0x303000003030, 0xc0003000c00030, 0xc0c03030]
def g_57 : Nat := 0x101000401030
def ep_57 : Nat := 0x40002000000000000000000000000000400020000000000000000000000000000000000000101000401000
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def cur_57 : Nat → List (Nat × Nat) := cc_57_0
def hc_57_0 : Nat → Nat := fun _ => 0
def nh_57 : Nat → Nat := hc_57_0
def f_57 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_57 : Nat → Bool := dagCheckNodeV5 0xc0c03030c0c03030 g_57 ep_57 1 1 bds_57 7 (dagTraceF 0xc0c03030c0c03030 [0x4040101040401010, 0x303000003030, 0xc0003000c00030, 0xc0c03030] 4 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 0xc0c03030c0c03030 g_57 ep_57 1 1 7 bds_57 (dagTraceF 0xc0c03030c0c03030 [0x4040101040401010, 0x303000003030, 0xc0003000c00030, 0xc0c03030] 4 f_57) (cur_57 0) (nh_57 0) [0x4040101040401010, 0x303000003030, 0xc0003000c00030, 0xc0c03030] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 7 ch_57 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 7 → ch_57 i = true := fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2
theorem lb_57 : LowerBin 0xc0c03030c0c03030 [0x4040101040401010, 0x303000003030, 0xc0003000c00030, 0xc0c03030] g_57 5 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)
def m_58 : Nat := 0xc0c0c0c030303030
def s_58 : List Nat := [0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030]
def g_58 : Nat := 0x4010101030
def ep_58 : Nat := 0x40000000200000004000000020000000000000000000000000000000000000004010101000
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
def cc_58_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def cur_58 : Nat → List (Nat × Nat) := cc_58_0
def hc_58_0 : Nat → Nat := fun _ => 0
def nh_58 : Nat → Nat := hc_58_0
def f_58 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_58 : Nat → Bool := dagCheckNodeV5 0xc0c0c0c030303030 g_58 ep_58 1 1 bds_58 7 (dagTraceF 0xc0c0c0c030303030 [0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030] 4 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 0xc0c0c0c030303030 g_58 ep_58 1 1 7 bds_58 (dagTraceF 0xc0c0c0c030303030 [0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030] 4 f_58) (cur_58 0) (nh_58 0) [0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 7 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 7 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2
theorem lb_58 : LowerBin 0xc0c0c0c030303030 [0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030] g_58 5 :=
  lowerDagV5 (kn_nil) rc_58 nc_58 (by decide +kernel)
def m_59 : Nat := 0xf0f000000000f0f0
def s_59 : List Nat := [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0]
def g_59 : Nat := 0x1010000000005070
def ep_59 : Nat := 0x20000000000000000010100000000000201010000000005040
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
def cc_59_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb162c4a910604072e0701 0x4cc2060c1831654e9e6cb2e491106442200f 7 127 3 7 9 511 13 8191
def cur_59 : Nat → List (Nat × Nat) := cc_59_0
def hc_59_0 : Nat → Nat := fun _ => 0
def nh_59 : Nat → Nat := hc_59_0
def f_59 : Nat → Nat × Nat := unpackForestF 0xcea26103019b306065c322316086442200f 4 9
def ch_59 : Nat → Bool := dagCheckNodeV5 0xf0f000000000f0f0 g_59 ep_59 1 1 bds_59 11 (dagTraceF 0xf0f000000000f0f0 [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0] 4 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 0xf0f000000000f0f0 g_59 ep_59 1 1 11 bds_59 (dagTraceF 0xf0f000000000f0f0 [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0] 4 f_59) (cur_59 0) (nh_59 0) [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 11 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 11 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2
theorem lb_59 : LowerBin 0xf0f000000000f0f0 [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0] g_59 5 :=
  lowerDagV5 (kn_nil) rc_59 nc_59 (by decide +kernel)
def m_60 : Nat := 0x66006600660066
def s_60 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_60 : Nat := 0x6004600460066
def ep_60 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := []
def cc_60_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def cur_60 : Nat → List (Nat × Nat) := cc_60_0
def hc_60_0 : Nat → Nat := fun _ => 0
def nh_60 : Nat → Nat := hc_60_0
def f_60 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_60 : Nat → Bool := dagCheckNodeV5 0x66006600660066 g_60 ep_60 1 1 bds_60 10 (dagTraceF 0x66006600660066 [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066] 4 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 0x66006600660066 g_60 ep_60 1 1 10 bds_60 (dagTraceF 0x66006600660066 [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066] 4 f_60) (cur_60 0) (nh_60 0) [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 10 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 10 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2
theorem lb_60 : LowerBin 0x66006600660066 [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066] g_60 5 :=
  lowerDagV5 (kn_nil) rc_60 nc_60 (by decide +kernel)
def m_61 : Nat := 0xcc003300cc0033
def s_61 : List Nat := [0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033]
def g_61 : Nat := 0x40013004c0033
def ep_61 : Nat := 0x48002000000000000000000000000000000000000400020008000000000000000000000004001000400000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cc_61_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294241902408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc61a492e126a34bc69bd132926028b04910c1e1234147868d0d22a2403c7068c090e101434182850906121d34309841104127a3fec77c8deb19d03f987720dd619a82f4856809c211800f 10 1023 4 15 10 1023 15 32767
def cur_61 : Nat → List (Nat × Nat) := cc_61_0
def hc_61_0 : Nat → Nat := unpackHintV5 0xb0368cd943e4430000000000000000023057f35c8d633d80300000000000000000174350350cd343cc43000000000000000000b8301b4001 0x1544aa24455b0a88d45222ad9511a8a4455b202020200221 14 16383 6 63
def nh_61 : Nat → Nat := hc_61_0
def f_61 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b689a8d2c925828bc696090319843f087610dd8a2303c7868c0d1a1a3024086610bc215842712682130a12084418482090211800f 5 10
def ch_61 : Nat → Bool := dagCheckNodeV5 0xcc003300cc0033 g_61 ep_61 1 1 bds_61 31 (dagTraceF 0xcc003300cc0033 [0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033] 5 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 0xcc003300cc0033 g_61 ep_61 1 1 31 bds_61 (dagTraceF 0xcc003300cc0033 [0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033] 5 f_61) (cur_61 0) (nh_61 0) [0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_0 : treeBlockF 0 31 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 31 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61_0 h1 h2
theorem lb_61 : LowerBin 0xcc003300cc0033 [0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033] g_61 6 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_61 nc_61 (by decide +kernel)
def m_62 : Nat := 0xcc00cc00330033
def s_62 : List Nat := [0x44004400110011, 0x330033, 0xc000c00030003, 0xcc00000033]
def g_62 : Nat := 0x4004c00130033
def ep_62 : Nat := 0x48000000200000000000000000000400080002000000000000000000000004004000100000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e126634bc69bd134946124b04914c1e9234147a68d4d2322413c7268c050e901534182854906921e343298451040a7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_62 : Nat → List (Nat × Nat) := cc_62_0
def hc_62_0 : Nat → Nat := unpackHintV5 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1544aa24455b0aa2551222ad85512a891156c202020202021 14 16383 6 63
def nh_62 : Nat → Nat := hc_62_0
def f_62 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b68964a331a5924bc696090319853f0a7614dd922313c7a68c4d1a9a30140a6614bc295852714682530a9209441a482050291800f 5 10
def ch_62 : Nat → Bool := dagCheckNodeV5 0xcc00cc00330033 g_62 ep_62 1 1 bds_62 31 (dagTraceF 0xcc00cc00330033 [0x44004400110011, 0x330033, 0xc000c00030003, 0xcc00000033] 5 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 0xcc00cc00330033 g_62 ep_62 1 1 31 bds_62 (dagTraceF 0xcc00cc00330033 [0x44004400110011, 0x330033, 0xc000c00030003, 0xcc00000033] 5 f_62) (cur_62 0) (nh_62 0) [0x44004400110011, 0x330033, 0xc000c00030003, 0xcc00000033] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 31 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 31 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2
theorem lb_62 : LowerBin 0xcc00cc00330033 [0x44004400110011, 0x330033, 0xc000c00030003, 0xcc00000033] g_62 6 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_62 nc_62 (by decide +kernel)
def m_63 : Nat := 0xff0000000000ff
def s_63 : List Nat := [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff]
def g_63 : Nat := 0x1700000000007f
def ep_63 : Nat := 0x600000000000800120000000000200014000000000040
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e126634bc69bd134946124b04914c1e9234147a68d4d2322413c7268c050e901534182854906921e343298451040a7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_63 : Nat → List (Nat × Nat) := cc_63_0
def hc_63_0 : Nat → Nat := unpackHintV5 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1544aa24455b0aa2551222ad85512a891156c202020202021 14 16383 6 63
def nh_63 : Nat → Nat := hc_63_0
def f_63 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b68964a331a5924bc696090319853f0a7614dd922313c7a68c4d1a9a30140a6614bc295852714682530a9209441a482050291800f 5 10
def ch_63 : Nat → Bool := dagCheckNodeV5 0xff0000000000ff g_63 ep_63 1 1 bds_63 31 (dagTraceF 0xff0000000000ff [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff] 5 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 0xff0000000000ff g_63 ep_63 1 1 31 bds_63 (dagTraceF 0xff0000000000ff [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff] 5 f_63) (cur_63 0) (nh_63 0) [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 31 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 31 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2
theorem lb_63 : LowerBin 0xff0000000000ff [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff] g_63 6 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_63 nc_63 (by decide +kernel)
def m_64 : Nat := 0x6600660066006600
def s_64 : List Nat := [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600]
def g_64 : Nat := 0x40004004600
def ep_64 : Nat := 0x400420000000400000042000000000000000000000004000400020000000000000000000000000000000000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c6709862488220809f17c1f0785e074594641905c96158160545505050440100388d107001 0xc26174839a45920d879a0c311c5c20b468e0c1a104b488a7904c18103a386a40c4d08100c20449078e0d18081022703480492792fea57949ea91d02f9856f09d611a81f4836505c209800f 10 1023 4 15 10 1023 15 32767
def cur_64 : Nat → List (Nat × Nat) := cc_64_0
def hc_64_0 : Nat → Nat := unpackHintV5 0xa62e64d000000000025830000000930e10f792db0d00000000001a430000000660d5cf4c2cfcd00000000000f030000000390ca8f01a4001 0x1456a292d514a2b51496a8a515a8a4b54522002200221 14 16383 6 63
def nh_64 : Nat → Nat := hc_64_0
def f_64 : Nat → Nat × Nat := unpackForestF 0x14bc295eb48d079a0c0293de38b84168d0291842f08570d2209e4130084ed8e1a9031340846107c20d9a48347068c020b8d381a402490209800f 5 10
def ch_64 : Nat → Bool := dagCheckNodeV5 0x6600660066006600 g_64 ep_64 1 1 bds_64 31 (dagTraceF 0x6600660066006600 [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600] 5 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 0x6600660066006600 g_64 ep_64 1 1 31 bds_64 (dagTraceF 0x6600660066006600 [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600] 5 f_64) (cur_64 0) (nh_64 0) [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 31 ch_64 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 31 → ch_64 i = true := fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2
theorem lb_64 : LowerBin 0x6600660066006600 [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600] g_64 6 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_64 nc_64 (by decide +kernel)
def m_65 : Nat := 0xcc003300cc003300
def s_65 : List Nat := [0x4400110044001100, 0x330000003300, 0xc0003000c000300, 0xcc003300]
def g_65 : Nat := 0x110004001300
def ep_65 : Nat := 0x400020000000000000000000000000000000000000000000400020000000000000000000000110004001000
def bds_65 : List (Nat × List Nat × Nat × Nat) := []
def cc_65_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def cur_65 : Nat → List (Nat × Nat) := cc_65_0
def hc_65_0 : Nat → Nat := fun _ => 0
def nh_65 : Nat → Nat := hc_65_0
def f_65 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_65 : Nat → Bool := dagCheckNodeV5 0xcc003300cc003300 g_65 ep_65 1 1 bds_65 7 (dagTraceF 0xcc003300cc003300 [0x4400110044001100, 0x330000003300, 0xc0003000c000300, 0xcc003300] 4 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 0xcc003300cc003300 g_65 ep_65 1 1 7 bds_65 (dagTraceF 0xcc003300cc003300 [0x4400110044001100, 0x330000003300, 0xc0003000c000300, 0xcc003300] 4 f_65) (cur_65 0) (nh_65 0) [0x4400110044001100, 0x330000003300, 0xc0003000c000300, 0xcc003300] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_0 : treeBlockF 0 7 ch_65 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 7 → ch_65 i = true := fun _ h1 h2 => treeBlockF_at nb_65_0 h1 h2
theorem lb_65 : LowerBin 0xcc003300cc003300 [0x4400110044001100, 0x330000003300, 0xc0003000c000300, 0xcc003300] g_65 5 :=
  lowerDagV5 (kn_nil) rc_65 nc_65 (by decide +kernel)
def m_66 : Nat := 0xcc00cc0033003300
def s_66 : List Nat := [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300]
def g_66 : Nat := 0x40011001300
def ep_66 : Nat := 0x400000002000000000000000000000004000000020000000000000000000000040011001000
def bds_66 : List (Nat × List Nat × Nat × Nat) := []
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def cur_66 : Nat → List (Nat × Nat) := cc_66_0
def hc_66_0 : Nat → Nat := fun _ => 0
def nh_66 : Nat → Nat := hc_66_0
def f_66 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_66 : Nat → Bool := dagCheckNodeV5 0xcc00cc0033003300 g_66 ep_66 1 1 bds_66 7 (dagTraceF 0xcc00cc0033003300 [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300] 4 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 0xcc00cc0033003300 g_66 ep_66 1 1 7 bds_66 (dagTraceF 0xcc00cc0033003300 [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300] 4 f_66) (cur_66 0) (nh_66 0) [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 7 ch_66 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 7 → ch_66 i = true := fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2
theorem lb_66 : LowerBin 0xcc00cc0033003300 [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300] g_66 5 :=
  lowerDagV5 (kn_nil) rc_66 nc_66 (by decide +kernel)
def m_67 : Nat := 0xff0000000000ff00
def s_67 : List Nat := [0x5500000000005500, 0x3300000000003300, 0xf00000000000f00, 0xff00]
def g_67 : Nat := 0x1100000000005700
def ep_67 : Nat := 0x20011000000000002001100000000005400
def bds_67 : List (Nat × List Nat × Nat × Nat) := []
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb162c4a910604072e0701 0x4cc2060c1831654e9e6cb2e491106442200f 7 127 3 7 9 511 13 8191
def cur_67 : Nat → List (Nat × Nat) := cc_67_0
def hc_67_0 : Nat → Nat := fun _ => 0
def nh_67 : Nat → Nat := hc_67_0
def f_67 : Nat → Nat × Nat := unpackForestF 0xcea26103019b306065c322316086442200f 4 9
def ch_67 : Nat → Bool := dagCheckNodeV5 0xff0000000000ff00 g_67 ep_67 1 1 bds_67 11 (dagTraceF 0xff0000000000ff00 [0x5500000000005500, 0x3300000000003300, 0xf00000000000f00, 0xff00] 4 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 0xff0000000000ff00 g_67 ep_67 1 1 11 bds_67 (dagTraceF 0xff0000000000ff00 [0x5500000000005500, 0x3300000000003300, 0xf00000000000f00, 0xff00] 4 f_67) (cur_67 0) (nh_67 0) [0x5500000000005500, 0x3300000000003300, 0xf00000000000f00, 0xff00] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 11 ch_67 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 11 → ch_67 i = true := fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2
theorem lb_67 : LowerBin 0xff0000000000ff00 [0x5500000000005500, 0x3300000000003300, 0xf00000000000f00, 0xff00] g_67 5 :=
  lowerDagV5 (kn_nil) rc_67 nc_67 (by decide +kernel)
def m_68 : Nat := 0x666600006666
def s_68 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_68 : Nat := 0x44600004666
def ep_68 : Nat := 0x422000000000000000000000004200000020000004020000020000000000000000000000000000000000
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cc_68_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294241902408c5f47c1f0785c2701b16c1b06856458160545324c12148120444d407001 0xda41a4f2e0a6924ba49b8d32a66018b029108201e34148048d09229a3c4c7058c090e08183c1848605060a1d24289840f041a792fea57c49ea91d02f9857209d611a81f4836805c209800f 10 1023 4 15 10 1023 15 32767
def cur_68 : Nat → List (Nat × Nat) := cc_68_0
def hc_68_0 : Nat → Nat := unpackHintV5 0xa8366cd8c3e2430000000000000000022017b35b8d5f3d7030000000000000000016c14e3504d323cbc3000000000000000000b8101b4001 0x1505aa0c155ba82d5060aadd416a830556e00220022003 14 16383 6 63
def nh_68 : Nat → Nat := hc_68_0
def f_68 : Nat → Nat × Nat := unpackForestF 0x14bc2958527b469a492ca65818ba496050291842f0856109d89a40246098c0b1a1230240846107c20d841712486050426083c182820d0209800f 5 10
def ch_68 : Nat → Bool := dagCheckNodeV5 0x666600006666 g_68 ep_68 1 1 bds_68 31 (dagTraceF 0x666600006666 [0x222200002222, 0x60600000606, 0x6600000066, 0x6666] 5 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 0x666600006666 g_68 ep_68 1 1 31 bds_68 (dagTraceF 0x666600006666 [0x222200002222, 0x60600000606, 0x6600000066, 0x6666] 5 f_68) (cur_68 0) (nh_68 0) [0x222200002222, 0x60600000606, 0x6600000066, 0x6666] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_0 : treeBlockF 0 31 ch_68 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 31 → ch_68 i = true := fun _ h1 h2 => treeBlockF_at nb_68_0 h1 h2
theorem lb_68 : LowerBin 0x666600006666 [0x222200002222, 0x60600000606, 0x6600000066, 0x6666] g_68 6 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_68 nc_68 (by decide +kernel)
def m_69 : Nat := 0x55550000aaaa
def s_69 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_69 : Nat := 0x15550000022a
def ep_69 : Nat := 0x4000000028000004000000020800001000000002200000000000000000
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cc_69_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e146634bc69bd134946124b05114c1e9234187a68d4d2322413c7268c060e901534183054906921e343298451040c7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_69 : Nat → List (Nat × Nat) := cc_69_0
def hc_69_0 : Nat → Nat := unpackHintV5 0x9e3644d8436043000000000000000002001733598d59355830000000000000000015414834ecd2e34ac3000000000000000000a8101a4001 0x5446a23155ba88d4462ab7511a88c556e0202020203 14 16383 6 63
def nh_69 : Nat → Nat := hc_69_0
def f_69 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b68964a331a5924bc6960a0319853f0a7614dd922313c7a68c4d1a9a30180a6614bc295852714682530a9209441a482060291800f 5 10
def ch_69 : Nat → Bool := dagCheckNodeV5 0x55550000aaaa g_69 ep_69 1 1 bds_69 31 (dagTraceF 0x55550000aaaa [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa] 5 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 0x55550000aaaa g_69 ep_69 1 1 31 bds_69 (dagTraceF 0x55550000aaaa [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa] 5 f_69) (cur_69 0) (nh_69 0) [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_0 : treeBlockF 0 31 ch_69 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 31 → ch_69 i = true := fun _ h1 h2 => treeBlockF_at nb_69_0 h1 h2
theorem lb_69 : LowerBin 0x55550000aaaa [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa] g_69 6 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_69 nc_69 (by decide +kernel)
def m_70 : Nat := 0xcccc00003333
def s_70 : List Nat := [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033]
def g_70 : Nat := 0x44c00001333
def ep_70 : Nat := 0x4800000020000004080000020000000000000000000000044000001000
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cc_70_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e126634bc69bd134946124b04914c1e9234147a68d4d2322413c7268c050e901534182854906921e343298451040a7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_70 : Nat → List (Nat × Nat) := cc_70_0
def hc_70_0 : Nat → Nat := unpackHintV5 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1544aa24455b0aa2551222ad85512a891156c202020202021 14 16383 6 63
def nh_70 : Nat → Nat := hc_70_0
def f_70 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b68964a331a5924bc696090319853f0a7614dd922313c7a68c4d1a9a30140a6614bc295852714682530a9209441a482050291800f 5 10
def ch_70 : Nat → Bool := dagCheckNodeV5 0xcccc00003333 g_70 ep_70 1 1 bds_70 31 (dagTraceF 0xcccc00003333 [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033] 5 f_70) cur_70 nh_70
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 0xcccc00003333 g_70 ep_70 1 1 31 bds_70 (dagTraceF 0xcccc00003333 [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033] 5 f_70) (cur_70 0) (nh_70 0) [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_0 : treeBlockF 0 31 ch_70 = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 31 → ch_70 i = true := fun _ h1 h2 => treeBlockF_at nb_70_0 h1 h2
theorem lb_70 : LowerBin 0xcccc00003333 [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033] g_70 6 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_70 nc_70 (by decide +kernel)
def m_71 : Nat := 0x6666000066660000
def s_71 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_71 : Nat := 0x6000004460000
def ep_71 : Nat := 0x440000000000000000000000006000000420000000600000402000000000000000000000000000000000000
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cc_71_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_71 : Nat → List (Nat × Nat) := cc_71_0
def hc_71_0 : Nat → Nat := unpackHintV5 0x1 0x1 2 3 1 1
def nh_71 : Nat → Nat := hc_71_0
def f_71 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_71 : Nat → Bool := dagCheckNodeV5 0x6666000066660000 g_71 ep_71 1 1 bds_71 0 (dagTraceF 0x6666000066660000 [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] 4 f_71) cur_71 nh_71
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV5 0x6666000066660000 g_71 ep_71 1 1 0 bds_71 (dagTraceF 0x6666000066660000 [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] 4 f_71) (cur_71 0) (nh_71 0) [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] 4 = true := by decide +kernel
theorem nc_71 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x6666000066660000 g_71 ep_71 1 1 bds_71 0 (dagTraceF 0x6666000066660000 [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] 4 f_71) cur_71 nh_71 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_71 : LowerBin 0x6666000066660000 [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000] g_71 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_71 nc_71 (by decide +kernel)
def m_72 : Nat := 0xcccc000033330000
def s_72 : List Nat := [0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000]
def g_72 : Nat := 0x4000011130000
def ep_72 : Nat := 0x4000000020000000400000002000000000000000000000004000011100000
def bds_72 : List (Nat × List Nat × Nat × Nat) := []
def cc_72_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def cur_72 : Nat → List (Nat × Nat) := cc_72_0
def hc_72_0 : Nat → Nat := fun _ => 0
def nh_72 : Nat → Nat := hc_72_0
def f_72 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_72 : Nat → Bool := dagCheckNodeV5 0xcccc000033330000 g_72 ep_72 1 1 bds_72 7 (dagTraceF 0xcccc000033330000 [0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000] 4 f_72) cur_72 nh_72
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV5 0xcccc000033330000 g_72 ep_72 1 1 7 bds_72 (dagTraceF 0xcccc000033330000 [0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000] 4 f_72) (cur_72 0) (nh_72 0) [0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_0 : treeBlockF 0 7 ch_72 = true := by decide +kernel
theorem nc_72 : ∀ i, 0 ≤ i → i < 7 → ch_72 i = true := fun _ h1 h2 => treeBlockF_at nb_72_0 h1 h2
theorem lb_72 : LowerBin 0xcccc000033330000 [0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000] g_72 5 :=
  lowerDagV5 (kn_nil) rc_72 nc_72 (by decide +kernel)
def m_73 : Nat := 0x66666666
def s_73 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_73 : Nat := 0x4464666
def ep_73 : Nat := 0x42200000000000420020000000000402020000000000000000000000000000000000
def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cc_73_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294241902408c5f47c1f0785c2701b16c1b06856458160545324c12148120444d407001 0xda41a4f2e0a6924ba49b8d32a66018b029108201e34148048d09229a3c4c7058c090e08183c1848605060a1d24289840f041a792fea57c49ea91d02f9857209d611a81f4836805c209800f 10 1023 4 15 10 1023 15 32767
def cur_73 : Nat → List (Nat × Nat) := cc_73_0
def hc_73_0 : Nat → Nat := unpackHintV5 0xa8366cd8c3e2430000000000000000022017b35b8d5f3d7030000000000000000016c14e3504d323cbc3000000000000000000b8101b4001 0x1505aa0c155ba82d5060aadd416a830556e00220022003 14 16383 6 63
def nh_73 : Nat → Nat := hc_73_0
def f_73 : Nat → Nat × Nat := unpackForestF 0x14bc2958527b469a492ca65818ba496050291842f0856109d89a40246098c0b1a1230240846107c20d841712486050426083c182820d0209800f 5 10
def ch_73 : Nat → Bool := dagCheckNodeV5 0x66666666 g_73 ep_73 1 1 bds_73 31 (dagTraceF 0x66666666 [0x22222222, 0x6060606, 0x660066, 0x6666] 5 f_73) cur_73 nh_73
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsV5 0x66666666 g_73 ep_73 1 1 31 bds_73 (dagTraceF 0x66666666 [0x22222222, 0x6060606, 0x660066, 0x6666] 5 f_73) (cur_73 0) (nh_73 0) [0x22222222, 0x6060606, 0x660066, 0x6666] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_73_0 : treeBlockF 0 31 ch_73 = true := by decide +kernel
theorem nc_73 : ∀ i, 0 ≤ i → i < 31 → ch_73 i = true := fun _ h1 h2 => treeBlockF_at nb_73_0 h1 h2
theorem lb_73 : LowerBin 0x66666666 [0x22222222, 0x6060606, 0x660066, 0x6666] g_73 6 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_73 nc_73 (by decide +kernel)
def m_74 : Nat := 0x5555aaaa
def s_74 : List Nat := [0xaaaa, 0x11112222, 0x5050a0a, 0x5500aa]
def g_74 : Nat := 0x1555022a
def ep_74 : Nat := 0x400028000000000400020800000000100002200000000000000000
def bds_74 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cc_74_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e146634bc69bd134946124b05114c1e9234187a68d4d2322413c7268c060e901534183054906921e343298451040c7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_74 : Nat → List (Nat × Nat) := cc_74_0
def hc_74_0 : Nat → Nat := unpackHintV5 0x9e3644d8436043000000000000000002001733598d59355830000000000000000015414834ecd2e34ac3000000000000000000a8101a4001 0x5446a23155ba88d4462ab7511a88c556e0202020203 14 16383 6 63
def nh_74 : Nat → Nat := hc_74_0
def f_74 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b68964a331a5924bc6960a0319853f0a7614dd922313c7a68c4d1a9a30180a6614bc295852714682530a9209441a482060291800f 5 10
def ch_74 : Nat → Bool := dagCheckNodeV5 0x5555aaaa g_74 ep_74 1 1 bds_74 31 (dagTraceF 0x5555aaaa [0xaaaa, 0x11112222, 0x5050a0a, 0x5500aa] 5 f_74) cur_74 nh_74
set_option maxHeartbeats 0 in
theorem rc_74 : dagCheckRootsV5 0x5555aaaa g_74 ep_74 1 1 31 bds_74 (dagTraceF 0x5555aaaa [0xaaaa, 0x11112222, 0x5050a0a, 0x5500aa] 5 f_74) (cur_74 0) (nh_74 0) [0xaaaa, 0x11112222, 0x5050a0a, 0x5500aa] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_0 : treeBlockF 0 31 ch_74 = true := by decide +kernel
theorem nc_74 : ∀ i, 0 ≤ i → i < 31 → ch_74 i = true := fun _ h1 h2 => treeBlockF_at nb_74_0 h1 h2
theorem lb_74 : LowerBin 0x5555aaaa [0xaaaa, 0x11112222, 0x5050a0a, 0x5500aa] g_74 6 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_74 nc_74 (by decide +kernel)
def m_75 : Nat := 0xcccc3333
def s_75 : List Nat := [0x44441111, 0x3333, 0xc0c0303, 0xcc0033]
def g_75 : Nat := 0x44c1333
def ep_75 : Nat := 0x480020000000000408020000000000000000000000000004401000
def bds_75 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cc_75_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02809c65294250906408c5f47c1f0785c2701c06c5b06856458160545324c13048520444d407001 0xdc619492e126634bc69bd134946124b04914c1e9234147a68d4d2322413c7268c050e901534182854906921e343298451040a7a3fec77c8deb19d13f9a7724dd699a92f4a56849c291800f 10 1023 4 15 10 1023 15 32767
def cur_75 : Nat → List (Nat × Nat) := cc_75_0
def hc_75_0 : Nat → Nat := unpackHintV5 0xb4369cd983e5430000000000000000024058335d8d673d9030000000000000000017c5523514d363ccc3000000000000000000b8501b4001 0x1544aa24455b0aa2551222ad85512a891156c202020202021 14 16383 6 63
def nh_75 : Nat → Nat := hc_75_0
def f_75 : Nat → Nat × Nat := unpackForestF 0x18fc31d8637b68964a331a5924bc696090319853f0a7614dd922313c7a68c4d1a9a30140a6614bc295852714682530a9209441a482050291800f 5 10
def ch_75 : Nat → Bool := dagCheckNodeV5 0xcccc3333 g_75 ep_75 1 1 bds_75 31 (dagTraceF 0xcccc3333 [0x44441111, 0x3333, 0xc0c0303, 0xcc0033] 5 f_75) cur_75 nh_75
set_option maxHeartbeats 0 in
theorem rc_75 : dagCheckRootsV5 0xcccc3333 g_75 ep_75 1 1 31 bds_75 (dagTraceF 0xcccc3333 [0x44441111, 0x3333, 0xc0c0303, 0xcc0033] 5 f_75) (cur_75 0) (nh_75 0) [0x44441111, 0x3333, 0xc0c0303, 0xcc0033] 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75_0 : treeBlockF 0 31 ch_75 = true := by decide +kernel
theorem nc_75 : ∀ i, 0 ≤ i → i < 31 → ch_75 i = true := fun _ h1 h2 => treeBlockF_at nb_75_0 h1 h2
theorem lb_75 : LowerBin 0xcccc3333 [0x44441111, 0x3333, 0xc0c0303, 0xcc0033] g_75 6 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_75 nc_75 (by decide +kernel)
def m_76 : Nat := 0x6666666600000000
def s_76 : List Nat := [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000]
def g_76 : Nat := 0x6044600000000
def ep_76 : Nat := 0x440000000000006004200000000000604020000000000000000000000000000000000000000
def bds_76 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cc_76_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_76 : Nat → List (Nat × Nat) := cc_76_0
def hc_76_0 : Nat → Nat := unpackHintV5 0x1 0x1 2 3 1 1
def nh_76 : Nat → Nat := hc_76_0
def f_76 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_76 : Nat → Bool := dagCheckNodeV5 0x6666666600000000 g_76 ep_76 1 1 bds_76 0 (dagTraceF 0x6666666600000000 [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] 4 f_76) cur_76 nh_76
set_option maxHeartbeats 0 in
theorem rc_76 : dagCheckRootsV5 0x6666666600000000 g_76 ep_76 1 1 0 bds_76 (dagTraceF 0x6666666600000000 [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] 4 f_76) (cur_76 0) (nh_76 0) [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] 4 = true := by decide +kernel
theorem nc_76 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x6666666600000000 g_76 ep_76 1 1 bds_76 0 (dagTraceF 0x6666666600000000 [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] 4 f_76) cur_76 nh_76 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_76 : LowerBin 0x6666666600000000 [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000] g_76 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_76 nc_76 (by decide +kernel)
def m_77 : Nat := 0xcccc333300000000
def s_77 : List Nat := [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000]
def g_77 : Nat := 0x4111300000000
def ep_77 : Nat := 0x4000200000000000400020000000000000000000000000004111000000000
def bds_77 : List (Nat × List Nat × Nat × Nat) := []
def cc_77_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def cur_77 : Nat → List (Nat × Nat) := cc_77_0
def hc_77_0 : Nat → Nat := fun _ => 0
def nh_77 : Nat → Nat := hc_77_0
def f_77 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_77 : Nat → Bool := dagCheckNodeV5 0xcccc333300000000 g_77 ep_77 1 1 bds_77 7 (dagTraceF 0xcccc333300000000 [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000] 4 f_77) cur_77 nh_77
set_option maxHeartbeats 0 in
theorem rc_77 : dagCheckRootsV5 0xcccc333300000000 g_77 ep_77 1 1 7 bds_77 (dagTraceF 0xcccc333300000000 [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000] 4 f_77) (cur_77 0) (nh_77 0) [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000] 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_77_0 : treeBlockF 0 7 ch_77 = true := by decide +kernel
theorem nc_77 : ∀ i, 0 ≤ i → i < 7 → ch_77 i = true := fun _ h1 h2 => treeBlockF_at nb_77_0 h1 h2
theorem lb_77 : LowerBin 0xcccc333300000000 [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000] g_77 5 :=
  lowerDagV5 (kn_nil) rc_77 nc_77 (by decide +kernel)
def m_78 : Nat := 0x5555555555555555
def s_78 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_78 : Nat := 0x1115155515555555
def ep_78 : Nat := 0x440400000000440000040000004004000400000000404000400000011101000100000000000000000000000
def bds_78 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 7, g_16)]
def cc_78_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_78 : Nat → List (Nat × Nat) := cc_78_0
def hc_78_0 : Nat → Nat := fun _ => 0
def nh_78 : Nat → Nat := hc_78_0
def f_78 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_78 : Nat → Bool := dagCheckNodeV5 0x5555555555555555 g_78 ep_78 1 1 bds_78 0 (dagTraceF 0x5555555555555555 [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] 7 f_78) cur_78 nh_78
set_option maxHeartbeats 0 in
theorem rc_78 : dagCheckRootsV5 0x5555555555555555 g_78 ep_78 1 1 0 bds_78 (dagTraceF 0x5555555555555555 [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] 7 f_78) (cur_78 0) (nh_78 0) [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] 7 = true := by decide +kernel
theorem nc_78 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0x5555555555555555 g_78 ep_78 1 1 bds_78 0 (dagTraceF 0x5555555555555555 [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] 7 f_78) cur_78 nh_78 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_78 : LowerBin 0x5555555555555555 [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555] g_78 8 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_78 nc_78 (by decide +kernel)
def m_79 : Nat := 0xaaaaaaaaaaaaaaaa
def s_79 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_79 : Nat := 0x2000a000a022a
def ep_79 : Nat := 0x8022000000008000002200002000a000a00280002000a000a020800020000000002200000000000000000
def bds_79 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 6, g_17), (m_19, s_19, 6, g_19), (m_46, s_46, 6, g_46), (m_47, s_47, 6, g_47), (m_48, s_48, 6, g_48), (m_15, s_15, 5, g_15), (m_21, s_21, 5, g_21), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6)]
def cc_79_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_79 : Nat → List (Nat × Nat) := cc_79_0
def hc_79_0 : Nat → Nat := unpackHintV5 0x194000 0x15402973005518d77005539dfb 14 16383 7 127
def nh_79 : Nat → Nat := hc_79_0
def f_79 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_79 : Nat → Bool := dagCheckNodeV5 0xaaaaaaaaaaaaaaaa g_79 ep_79 3 7 bds_79 1 (dagTraceF 0xaaaaaaaaaaaaaaaa [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa] 7 f_79) cur_79 nh_79
set_option maxHeartbeats 0 in
theorem rc_79 : dagCheckRootsV5 0xaaaaaaaaaaaaaaaa g_79 ep_79 3 7 1 bds_79 (dagTraceF 0xaaaaaaaaaaaaaaaa [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa] 7 f_79) (cur_79 0) (nh_79 0) [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_79_0 : treeBlockF 0 1 ch_79 = true := by decide +kernel
theorem nc_79 : ∀ i, 0 ≤ i → i < 1 → ch_79 i = true := fun _ h1 h2 => treeBlockF_at nb_79_0 h1 h2
theorem lb_79 : LowerBin 0xaaaaaaaaaaaaaaaa [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa] g_79 8 :=
  lowerDagV5 (kn_cons lb_17 (kn_cons lb_19 (kn_cons lb_46 (kn_cons lb_47 (kn_cons lb_48 (kn_cons lb_15 (kn_cons lb_21 (kn_cons lb_2 (kn_cons lb_4 (kn_cons lb_6 (kn_nil))))))))))) rc_79 nc_79 (by decide +kernel)
def m_80 : Nat := 0xcccccccccccccccc
def s_80 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_80 : Nat := 0x4044c044c444c
def ep_80 : Nat := 0x448400000000448000040000004004800480008000404080408000800000000000000000004044004404440
def bds_80 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 7, g_16), (m_28, s_28, 7, g_28), (m_31, s_31, 7, g_31), (m_50, s_50, 6, g_50), (m_23, s_23, 5, g_23), (m_24, s_24, 5, g_24), (m_25, s_25, 5, g_25)]
def cc_80_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x38e31c29301 0x28c168963f91db8dcc6601f 6 63 3 7 10 1023 13 8191
def cur_80 : Nat → List (Nat × Nat) := cc_80_0
def hc_80_0 : Nat → Nat := unpackHintV5 0x267a76f2ad1e9e355242fa6000bc0000 0x358c000631cc6318c633802aaaaaaa80555555552ae31cc6318c00006718d63005555555500aaaaaaaa55c630018c6318c673bc015555555402aaaaaaa95718e600aaaa015554ab8c6339de0000318c631802aaaaaaa80555555552ad55500aaaa55 18 262143 8 255
def nh_80 : Nat → Nat := hc_80_0
def f_80 : Nat → Nat × Nat := unpackForestF 0x63f63b637b4463301f 2 10
def ch_80 : Nat → Bool := dagCheckNodeV5 0xcccccccccccccccc g_80 ep_80 3 7 bds_80 6 (dagTraceF 0xcccccccccccccccc [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc] 8 f_80) cur_80 nh_80
set_option maxHeartbeats 0 in
theorem rc_80 : dagCheckRootsV5 0xcccccccccccccccc g_80 ep_80 3 7 6 bds_80 (dagTraceF 0xcccccccccccccccc [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc] 8 f_80) (cur_80 0) (nh_80 0) [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_80_0 : treeBlockF 0 6 ch_80 = true := by decide +kernel
theorem nc_80 : ∀ i, 0 ≤ i → i < 6 → ch_80 i = true := fun _ h1 h2 => treeBlockF_at nb_80_0 h1 h2
theorem lb_80 : LowerBin 0xcccccccccccccccc [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc] g_80 9 :=
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_28 (kn_cons lb_31 (kn_cons lb_50 (kn_cons lb_23 (kn_cons lb_24 (kn_cons lb_25 (kn_nil)))))))) rc_80 nc_80 (by decide +kernel)
def m_81 : Nat := 0xf0f0f0f0f0f0f0f
def s_81 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_81 : Nat := 0x107050f050f070f
def ep_81 : Nat := 0x408020000000408000002000006000a000a0008000000000000000001020000000002000104050005000400
def bds_81 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 6, g_17), (m_33, s_33, 6, g_33), (m_53, s_53, 6, g_53), (m_54, s_54, 6, g_54), (m_55, s_55, 6, g_55), (m_23, s_23, 5, g_23), (m_35, s_35, 5, g_35), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8), (m_13, s_13, 4, g_13)]
def cc_81_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_81 : Nat → List (Nat × Nat) := cc_81_0
def hc_81_0 : Nat → Nat := unpackHintV5 0x174000 0x15402a6b550018eeb5539f6f 14 16383 7 127
def nh_81 : Nat → Nat := hc_81_0
def f_81 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_81 : Nat → Bool := dagCheckNodeV5 0xf0f0f0f0f0f0f0f g_81 ep_81 3 7 bds_81 1 (dagTraceF 0xf0f0f0f0f0f0f0f [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f] 7 f_81) cur_81 nh_81
set_option maxHeartbeats 0 in
theorem rc_81 : dagCheckRootsV5 0xf0f0f0f0f0f0f0f g_81 ep_81 3 7 1 bds_81 (dagTraceF 0xf0f0f0f0f0f0f0f [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f] 7 f_81) (cur_81 0) (nh_81 0) [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81_0 : treeBlockF 0 1 ch_81 = true := by decide +kernel
theorem nc_81 : ∀ i, 0 ≤ i → i < 1 → ch_81 i = true := fun _ h1 h2 => treeBlockF_at nb_81_0 h1 h2
theorem lb_81 : LowerBin 0xf0f0f0f0f0f0f0f [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f] g_81 8 :=
  lowerDagV5 (kn_cons lb_17 (kn_cons lb_33 (kn_cons lb_53 (kn_cons lb_54 (kn_cons lb_55 (kn_cons lb_23 (kn_cons lb_35 (kn_cons lb_7 (kn_cons lb_8 (kn_cons lb_13 (kn_nil))))))))))) rc_81 nc_81 (by decide +kernel)
def m_82 : Nat := 0xf0f0f0f0f0f0f0f0
def s_82 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_82 : Nat := 0x1010105010505070
def ep_82 : Nat := 0x40402000000040000040200000004000400020000000000000000010101000100000201010105010505040
def bds_82 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 6, g_32), (m_34, s_34, 6, g_34), (m_36, s_36, 6, g_36), (m_56, s_56, 6, g_56), (m_18, s_18, 5, g_18), (m_0, s_0, 4, g_0)]
def cc_82_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_82 : Nat → List (Nat × Nat) := cc_82_0
def hc_82_0 : Nat → Nat := unpackHintV5 0x160000 0xb7330000555500aaaa0055 14 16383 7 127
def nh_82 : Nat → Nat := hc_82_0
def f_82 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_82 : Nat → Bool := dagCheckNodeV5 0xf0f0f0f0f0f0f0f0 g_82 ep_82 2 3 bds_82 1 (dagTraceF 0xf0f0f0f0f0f0f0f0 [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0] 7 f_82) cur_82 nh_82
set_option maxHeartbeats 0 in
theorem rc_82 : dagCheckRootsV5 0xf0f0f0f0f0f0f0f0 g_82 ep_82 2 3 1 bds_82 (dagTraceF 0xf0f0f0f0f0f0f0f0 [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0] 7 f_82) (cur_82 0) (nh_82 0) [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_82_0 : treeBlockF 0 1 ch_82 = true := by decide +kernel
theorem nc_82 : ∀ i, 0 ≤ i → i < 1 → ch_82 i = true := fun _ h1 h2 => treeBlockF_at nb_82_0 h1 h2
theorem lb_82 : LowerBin 0xf0f0f0f0f0f0f0f0 [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0] g_82 8 :=
  lowerDagV5 (kn_cons lb_32 (kn_cons lb_34 (kn_cons lb_36 (kn_cons lb_56 (kn_cons lb_18 (kn_cons lb_0 (kn_nil))))))) rc_82 nc_82 (by decide +kernel)
def m_83 : Nat := 0xff00ff00ff00ff
def s_83 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_83 : Nat := 0x17005f005f007f
def ep_83 : Nat := 0x480020000000480000002000000000000000000006000a000a000800120000000000200014005000500040
def bds_83 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 6, g_19), (m_32, s_32, 6, g_32), (m_61, s_61, 6, g_61), (m_62, s_62, 6, g_62), (m_63, s_63, 6, g_63), (m_25, s_25, 5, g_25), (m_38, s_38, 5, g_38), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_14, s_14, 4, g_14)]
def cc_83_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_83 : Nat → List (Nat × Nat) := cc_83_0
def hc_83_0 : Nat → Nat := unpackHintV5 0x174000 0x15402a6b550018eeb5539f6f 14 16383 7 127
def nh_83 : Nat → Nat := hc_83_0
def f_83 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_83 : Nat → Bool := dagCheckNodeV5 0xff00ff00ff00ff g_83 ep_83 3 7 bds_83 1 (dagTraceF 0xff00ff00ff00ff [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff] 7 f_83) cur_83 nh_83
set_option maxHeartbeats 0 in
theorem rc_83 : dagCheckRootsV5 0xff00ff00ff00ff g_83 ep_83 3 7 1 bds_83 (dagTraceF 0xff00ff00ff00ff [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff] 7 f_83) (cur_83 0) (nh_83 0) [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_83_0 : treeBlockF 0 1 ch_83 = true := by decide +kernel
theorem nc_83 : ∀ i, 0 ≤ i → i < 1 → ch_83 i = true := fun _ h1 h2 => treeBlockF_at nb_83_0 h1 h2
theorem lb_83 : LowerBin 0xff00ff00ff00ff [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff] g_83 8 :=
  lowerDagV5 (kn_cons lb_19 (kn_cons lb_32 (kn_cons lb_61 (kn_cons lb_62 (kn_cons lb_63 (kn_cons lb_25 (kn_cons lb_38 (kn_cons lb_9 (kn_cons lb_10 (kn_cons lb_14 (kn_nil))))))))))) rc_83 nc_83 (by decide +kernel)
def m_84 : Nat := 0xff00ff00ff00ff00
def s_84 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_84 : Nat := 0x1100150015005700
def ep_84 : Nat := 0x400420000000400000042000000000000000000000004000400020011001000100002001100150015005400
def bds_84 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 6, g_33), (m_37, s_37, 6, g_37), (m_39, s_39, 6, g_39), (m_64, s_64, 6, g_64), (m_20, s_20, 5, g_20), (m_1, s_1, 4, g_1)]
def cc_84_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_84 : Nat → List (Nat × Nat) := cc_84_0
def hc_84_0 : Nat → Nat := unpackHintV5 0x160000 0xb7330000555500aaaa0055 14 16383 7 127
def nh_84 : Nat → Nat := hc_84_0
def f_84 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_84 : Nat → Bool := dagCheckNodeV5 0xff00ff00ff00ff00 g_84 ep_84 2 3 bds_84 1 (dagTraceF 0xff00ff00ff00ff00 [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00] 7 f_84) cur_84 nh_84
set_option maxHeartbeats 0 in
theorem rc_84 : dagCheckRootsV5 0xff00ff00ff00ff00 g_84 ep_84 2 3 1 bds_84 (dagTraceF 0xff00ff00ff00ff00 [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00] 7 f_84) (cur_84 0) (nh_84 0) [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_0 : treeBlockF 0 1 ch_84 = true := by decide +kernel
theorem nc_84 : ∀ i, 0 ≤ i → i < 1 → ch_84 i = true := fun _ h1 h2 => treeBlockF_at nb_84_0 h1 h2
theorem lb_84 : LowerBin 0xff00ff00ff00ff00 [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00] g_84 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_cons lb_37 (kn_cons lb_39 (kn_cons lb_64 (kn_cons lb_20 (kn_cons lb_1 (kn_nil))))))) rc_84 nc_84 (by decide +kernel)
def m_85 : Nat := 0xffff0000ffff
def s_85 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_85 : Nat := 0x155f0000577f
def ep_85 : Nat := 0x422000000000000000000000004a000000280000040a0000020800001000000002200000155000005440
def bds_85 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 6, g_34), (m_37, s_37, 6, g_37), (m_68, s_68, 6, g_68), (m_69, s_69, 6, g_69), (m_70, s_70, 6, g_70), (m_21, s_21, 5, g_21), (m_27, s_27, 5, g_27), (m_26, s_26, 5, g_26), (m_42, s_42, 5, g_42)]
def cc_85_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_85 : Nat → List (Nat × Nat) := cc_85_0
def hc_85_0 : Nat → Nat := unpackHintV5 0x1b4000 0x16fa00005555005dc6339e6f0055 14 16383 7 127
def nh_85 : Nat → Nat := hc_85_0
def f_85 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_85 : Nat → Bool := dagCheckNodeV5 0xffff0000ffff g_85 ep_85 3 7 bds_85 1 (dagTraceF 0xffff0000ffff [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff] 7 f_85) cur_85 nh_85
set_option maxHeartbeats 0 in
theorem rc_85 : dagCheckRootsV5 0xffff0000ffff g_85 ep_85 3 7 1 bds_85 (dagTraceF 0xffff0000ffff [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff] 7 f_85) (cur_85 0) (nh_85 0) [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_85_0 : treeBlockF 0 1 ch_85 = true := by decide +kernel
theorem nc_85 : ∀ i, 0 ≤ i → i < 1 → ch_85 i = true := fun _ h1 h2 => treeBlockF_at nb_85_0 h1 h2
theorem lb_85 : LowerBin 0xffff0000ffff [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff] g_85 8 :=
  lowerDagV5 (kn_cons lb_34 (kn_cons lb_37 (kn_cons lb_68 (kn_cons lb_69 (kn_cons lb_70 (kn_cons lb_21 (kn_cons lb_27 (kn_cons lb_26 (kn_cons lb_42 (kn_nil)))))))))) rc_85 nc_85 (by decide +kernel)
def m_86 : Nat := 0xffff0000ffff0000
def s_86 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_86 : Nat := 0x11170000155f0000
def ep_86 : Nat := 0x4480000000000000000000000060000004a000000060000040a000011120000100000001114000015500000
def bds_86 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cc_86_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_86 : Nat → List (Nat × Nat) := cc_86_0
def hc_86_0 : Nat → Nat := fun _ => 0
def nh_86 : Nat → Nat := hc_86_0
def f_86 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_86 : Nat → Bool := dagCheckNodeV5 0xffff0000ffff0000 g_86 ep_86 1 1 bds_86 0 (dagTraceF 0xffff0000ffff0000 [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] 7 f_86) cur_86 nh_86
set_option maxHeartbeats 0 in
theorem rc_86 : dagCheckRootsV5 0xffff0000ffff0000 g_86 ep_86 1 1 0 bds_86 (dagTraceF 0xffff0000ffff0000 [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] 7 f_86) (cur_86 0) (nh_86 0) [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] 7 = true := by decide +kernel
theorem nc_86 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xffff0000ffff0000 g_86 ep_86 1 1 bds_86 0 (dagTraceF 0xffff0000ffff0000 [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] 7 f_86) cur_86 nh_86 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_86 : LowerBin 0xffff0000ffff0000 [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000] g_86 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_86 nc_86 (by decide +kernel)
def m_87 : Nat := 0xffffffff
def s_87 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_87 : Nat := 0x155f577f
def ep_87 : Nat := 0x422000000000004a002800000000040a020800000000100002200000000015505440
def bds_87 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 6, g_36), (m_39, s_39, 6, g_39), (m_73, s_73, 6, g_73), (m_74, s_74, 6, g_74), (m_75, s_75, 6, g_75), (m_22, s_22, 5, g_22), (m_30, s_30, 5, g_30), (m_29, s_29, 5, g_29), (m_41, s_41, 5, g_41)]
def cc_87_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def cur_87 : Nat → List (Nat × Nat) := cc_87_0
def hc_87_0 : Nat → Nat := unpackHintV5 0x1b4000 0x16fa00005555005dc6339e6f0055 14 16383 7 127
def nh_87 : Nat → Nat := hc_87_0
def f_87 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_87 : Nat → Bool := dagCheckNodeV5 0xffffffff g_87 ep_87 3 7 bds_87 1 (dagTraceF 0xffffffff [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff] 7 f_87) cur_87 nh_87
set_option maxHeartbeats 0 in
theorem rc_87 : dagCheckRootsV5 0xffffffff g_87 ep_87 3 7 1 bds_87 (dagTraceF 0xffffffff [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff] 7 f_87) (cur_87 0) (nh_87 0) [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff] 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_87_0 : treeBlockF 0 1 ch_87 = true := by decide +kernel
theorem nc_87 : ∀ i, 0 ≤ i → i < 1 → ch_87 i = true := fun _ h1 h2 => treeBlockF_at nb_87_0 h1 h2
theorem lb_87 : LowerBin 0xffffffff [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff] g_87 8 :=
  lowerDagV5 (kn_cons lb_36 (kn_cons lb_39 (kn_cons lb_73 (kn_cons lb_74 (kn_cons lb_75 (kn_cons lb_22 (kn_cons lb_30 (kn_cons lb_29 (kn_cons lb_41 (kn_nil)))))))))) rc_87 nc_87 (by decide +kernel)
def m_88 : Nat := 0xffffffff00000000
def s_88 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_88 : Nat := 0x1117155f00000000
def ep_88 : Nat := 0x448000000000006004a000000000006040a0000000011121000000000001114155000000000
def bds_88 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31)]
def cc_88_0 : Nat → List (Nat × Nat) := fun _ => []
def cur_88 : Nat → List (Nat × Nat) := cc_88_0
def hc_88_0 : Nat → Nat := fun _ => 0
def nh_88 : Nat → Nat := hc_88_0
def f_88 : Nat → Nat × Nat := fun _ => (0, 0)
def ch_88 : Nat → Bool := dagCheckNodeV5 0xffffffff00000000 g_88 ep_88 1 1 bds_88 0 (dagTraceF 0xffffffff00000000 [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] 7 f_88) cur_88 nh_88
set_option maxHeartbeats 0 in
theorem rc_88 : dagCheckRootsV5 0xffffffff00000000 g_88 ep_88 1 1 0 bds_88 (dagTraceF 0xffffffff00000000 [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] 7 f_88) (cur_88 0) (nh_88 0) [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] 7 = true := by decide +kernel
theorem nc_88 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 0xffffffff00000000 g_88 ep_88 1 1 bds_88 0 (dagTraceF 0xffffffff00000000 [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] 7 f_88) cur_88 nh_88 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_88 : LowerBin 0xffffffff00000000 [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000] g_88 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_nil)) rc_88 nc_88 (by decide +kernel)
def m_89 : Nat := 0x6666666666666666
def s_89 : List Nat := [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666]
def g_89 : Nat := 0x6044604464666
def ep_89 : Nat := 0x440422000000440000042200006004200420020000604020402020000000000000000000000000000000000
def bds_89 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 7, g_16), (m_56, s_56, 6, g_56), (m_64, s_64, 6, g_64), (m_68, s_68, 6, g_68), (m_73, s_73, 6, g_73), (m_71, s_71, 5, g_71), (m_76, s_76, 5, g_76), (m_52, s_52, 5, g_52), (m_60, s_60, 5, g_60)]
def cc_89_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7971696861595851494841390e01 0x204d43b812e42488ed824592cc5c2d1f237b4ee92b70ed02b104c01f 8 255 3 7 10 1023 14 16383
def cur_89 : Nat → List (Nat × Nat) := cc_89_0
def hc_89_0 : Nat → Nat := unpackHintV5 0x1d3e0ec611f5118fa828313585e76f1f3ab061be8b897a3e47c201d833044d3c0150800005 0x37b0dec000441902205559540d9b018e6b18e6b55aa0366c0e79bce79bd56a8e31c4008d82a81b360aa8d61ac6380037b0dec01474b5aef4a81b360ab1e18c6339d6f39d6b9b00220690366c11ac636aa1d0006f61bd802ad6b9ad0ea0366c13b54318c673ade73ad7bd91bd89bd8b7ae20046c1540d9b0558701b360aa9d63bce78e319c0037b0dec014f4f7bef4f58c631bd6aef64dec8dec5bd73600440d206cd8236a80d9b04ef39daa8f4718ce001bd86f600af7be6b477ac6318debab7b37bdef7b1dec6bdecef19bd8b9ad9d79b002360c806f61bd8231b0c7006f61bd8273b1cf0ce318c6318006f61bd802ad6b9ad2d6bbd0c6718c7360046c190366c11b0e0366c13b1e38c7b 21 2097151 9 511
def nh_89 : Nat → Nat := hc_89_0
def f_89 : Nat → Nat × Nat := unpackForestF 0x63714ec52b909223b10ed824592c42b3170b47104c01f 4 10
def ch_89 : Nat → Bool := dagCheckNodeV5 0x6666666666666666 g_89 ep_89 3 7 bds_89 13 (dagTraceF 0x6666666666666666 [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666] 8 f_89) cur_89 nh_89
set_option maxHeartbeats 0 in
theorem rc_89 : dagCheckRootsV5 0x6666666666666666 g_89 ep_89 3 7 13 bds_89 (dagTraceF 0x6666666666666666 [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666] 8 f_89) (cur_89 0) (nh_89 0) [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_89_0 : treeBlockF 0 13 ch_89 = true := by decide +kernel
theorem nc_89 : ∀ i, 0 ≤ i → i < 13 → ch_89 i = true := fun _ h1 h2 => treeBlockF_at nb_89_0 h1 h2
theorem lb_89 : LowerBin 0x6666666666666666 [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666] g_89 9 :=
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_56 (kn_cons lb_64 (kn_cons lb_68 (kn_cons lb_73 (kn_cons lb_71 (kn_cons lb_76 (kn_cons lb_52 (kn_cons lb_60 (kn_nil)))))))))) rc_89 nc_89 (by decide +kernel)
def m_90 : Nat := 0xcccc3333cccc3333
def s_90 : List Nat := [0x4444111144441111, 0x333300003333, 0xc0c03030c0c0303, 0xcc003300cc0033, 0xcccc3333]
def g_90 : Nat := 0x41113044c1333
def ep_90 : Nat := 0x448022000000000000000000004000200480020000400020408020000000000000000000004111004401000
def bds_90 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28), (m_46, s_46, 6, g_46), (m_53, s_53, 6, g_53), (m_61, s_61, 6, g_61), (m_75, s_75, 6, g_75), (m_44, s_44, 5, g_44), (m_57, s_57, 5, g_57), (m_65, s_65, 5, g_65), (m_77, s_77, 5, g_77)]
def cc_90_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7971696861595851494841390e01 0x2046a10e02dc8348686c0d15ad984428b78d2ed25d233709680cc411801f 8 255 3 7 11 2047 15 32767
def cur_90 : Nat → List (Nat × Nat) := cc_90_0
def hc_90_0 : Nat → Nat := unpackHintV5 0x1e3e3accd2953a9629106137c8676d2939e0c1ae1088c258436151dc1f847d340151400005 0xaacab2aab5431ae631ad6202046c0880d9b00366c00d81b055aa39d7739d6b38c606cd8555546a3a1a8d6faa5ad51010360406cd81b3606cd801b3600aa7a18c6339d7739d6b0366c34a31b0eaa95eb7ad6875081b020203606c0d9b00366c013b553c6318c7339df739def0366c366cdeed9b1b9f7b7ad66f655551d08081b0203606c1553a9e8e718ce01bd86f60a75bea96b5cc6318d6b000dec37b00577bd9b3bdecd94c6b7acdecd28daa9e206c08080d81b04e763d551ce319ee06cd82bd6f5ad1df318c637bc0037b0dec02addb36776cd837cb9acdecca31a31d0e6206c0d8101b03609ce9cf47b8ce318c63181b360b35cd6b37d54de319c0037b0dec00631e51a3a103606c080d81b04e9e8e3181b361b 21 2097151 9 511
def nh_90 : Nat → Nat := hc_90_0
def f_90 : Nat → Nat × Nat := unpackForestF 0xb4b149628ce41a43431096c0d15ad88333088516c411801f 4 11
def ch_90 : Nat → Bool := dagCheckNodeV5 0xcccc3333cccc3333 g_90 ep_90 3 7 bds_90 13 (dagTraceF 0xcccc3333cccc3333 [0x4444111144441111, 0x333300003333, 0xc0c03030c0c0303, 0xcc003300cc0033, 0xcccc3333] 8 f_90) cur_90 nh_90
set_option maxHeartbeats 0 in
theorem rc_90 : dagCheckRootsV5 0xcccc3333cccc3333 g_90 ep_90 3 7 13 bds_90 (dagTraceF 0xcccc3333cccc3333 [0x4444111144441111, 0x333300003333, 0xc0c03030c0c0303, 0xcc003300cc0033, 0xcccc3333] 8 f_90) (cur_90 0) (nh_90 0) [0x4444111144441111, 0x333300003333, 0xc0c03030c0c0303, 0xcc003300cc0033, 0xcccc3333] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_90_0 : treeBlockF 0 13 ch_90 = true := by decide +kernel
theorem nc_90 : ∀ i, 0 ≤ i → i < 13 → ch_90 i = true := fun _ h1 h2 => treeBlockF_at nb_90_0 h1 h2
theorem lb_90 : LowerBin 0xcccc3333cccc3333 [0x4444111144441111, 0x333300003333, 0xc0c03030c0c0303, 0xcc003300cc0033, 0xcccc3333] g_90 9 :=
  lowerDagV5 (kn_cons lb_28 (kn_cons lb_46 (kn_cons lb_53 (kn_cons lb_61 (kn_cons lb_75 (kn_cons lb_44 (kn_cons lb_57 (kn_cons lb_65 (kn_cons lb_77 (kn_nil)))))))))) rc_90 nc_90 (by decide +kernel)
def m_91 : Nat := 0xcccccccc33333333
def s_91 : List Nat := [0x4444444411111111, 0x33333333, 0xc0c0c0c03030303, 0xcc00cc00330033, 0xcccc00003333]
def g_91 : Nat := 0x4044c11131333
def ep_91 : Nat := 0x448000002200004004800020020000404080002020000000000000000000004044011101000
def bds_91 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31), (m_47, s_47, 6, g_47), (m_54, s_54, 6, g_54), (m_62, s_62, 6, g_62), (m_70, s_70, 6, g_70), (m_45, s_45, 5, g_45), (m_58, s_58, 5, g_58), (m_66, s_66, 5, g_66), (m_72, s_72, 5, g_72)]
def cc_91_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7971696861595851494841390e01 0x2246a50e0adc9348686c4d15ad994428b78d2ed25d233729684cc491801f 8 255 3 7 11 2047 15 32767
def cur_91 : Nat → List (Nat × Nat) := cc_91_0
def hc_91_0 : Nat → Nat := unpackHintV5 0x1e3e3accd2953a9629106137c8676d2939e0c1ae1088c258436151dc1f847d340151400005 0xaacab2aab5431ae631ad6ab5473aee73ad6718c40408d81101b36006cd801b03606c0d8555546a3a1a8d6faa5ad5553d0c6319cebb9ceb588081b020366c0d9b0366c00d9b003606c34a31b0eaa95eb7ad6875276aa78c6318e673bee73bde206c08080d81b0366c00d9b003606c366cdee6e77ad7b366f7b3655551d2aa753d1ce319d4eb7d52d6b98c631ad6a88081b0203606c0d9b0366c0d9b00366c037bd9b34c6b7af7bd9b366cd28daa9e9cec7aaa39c633dd5eb7ad68ef98c631bdf5081b020203606c0d81b0366c00d9b00ddb3646f9735eed9b366cca31a31d0e69ce9cf47b8ce318c631acd735acdf55378c6718c6206c0d8101b03606c0d81b36006cd80651a3a4e9e8e31881b0360406c0d81b0361b 21 2097151 9 511
def nh_91 : Nat → Nat := hc_91_0
def f_91 : Nat → Nat × Nat := unpackForestF 0xb4b149628ce49a43431296c4d15ad89333288516c491801f 4 11
def ch_91 : Nat → Bool := dagCheckNodeV5 0xcccccccc33333333 g_91 ep_91 3 7 bds_91 13 (dagTraceF 0xcccccccc33333333 [0x4444444411111111, 0x33333333, 0xc0c0c0c03030303, 0xcc00cc00330033, 0xcccc00003333] 8 f_91) cur_91 nh_91
set_option maxHeartbeats 0 in
theorem rc_91 : dagCheckRootsV5 0xcccccccc33333333 g_91 ep_91 3 7 13 bds_91 (dagTraceF 0xcccccccc33333333 [0x4444444411111111, 0x33333333, 0xc0c0c0c03030303, 0xcc00cc00330033, 0xcccc00003333] 8 f_91) (cur_91 0) (nh_91 0) [0x4444444411111111, 0x33333333, 0xc0c0c0c03030303, 0xcc00cc00330033, 0xcccc00003333] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_91_0 : treeBlockF 0 13 ch_91 = true := by decide +kernel
theorem nc_91 : ∀ i, 0 ≤ i → i < 13 → ch_91 i = true := fun _ h1 h2 => treeBlockF_at nb_91_0 h1 h2
theorem lb_91 : LowerBin 0xcccccccc33333333 [0x4444444411111111, 0x33333333, 0xc0c0c0c03030303, 0xcc00cc00330033, 0xcccc00003333] g_91 9 :=
  lowerDagV5 (kn_cons lb_31 (kn_cons lb_47 (kn_cons lb_54 (kn_cons lb_62 (kn_cons lb_70 (kn_cons lb_45 (kn_cons lb_58 (kn_cons lb_66 (kn_cons lb_72 (kn_nil)))))))))) rc_91 nc_91 (by decide +kernel)
def m_92 : Nat := 0xffff00000000ffff
def s_92 : List Nat := [0x5555000000005555, 0x3333000000003333, 0xf0f000000000f0f, 0xff0000000000ff, 0xffff]
def g_92 : Nat := 0x111700000000577f
def ep_92 : Nat := 0x6000000000028000600000000020811120000000002201114000000005440
def bds_92 : List (Nat × List Nat × Nat × Nat) := [(m_48, s_48, 6, g_48), (m_55, s_55, 6, g_55), (m_63, s_63, 6, g_63), (m_40, s_40, 5, g_40), (m_51, s_51, 5, g_51), (m_43, s_43, 5, g_43), (m_49, s_49, 5, g_49), (m_59, s_59, 5, g_59), (m_67, s_67, 5, g_67), (m_6, s_6, 4, g_6), (m_13, s_13, 4, g_13), (m_14, s_14, 4, g_14)]
def cc_92_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb43682d0562ac150681500a0130a604c090520230c6084508200ba3740e81b1360682d01813005c2a0c19801 0x3e48ce95638158d15c3248cb8302e510b0562852c994322110786c1a1506b452116c745718158534b12d0c38440a1b0185406d14345b0915c105694d2e4b479092e323b888cdf94b764edb9336048d784b4211cf03f360ecc0372a0cc902f1608c401f0204c001f 11 2047 5 31 11 2047 18 262143
def cc_92_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x944864104803e5e2d46832590ba5c2a8fc783c1c4e07031180b2582c12890481d0381001 0x1f134f5adf855a80aea03fe89a4c11796b7c156942ba60ff6289a16cc8aa64d16308bac5bce2be255a20aef84f6423dc9b2c4d95a54a4b64e5b262a9216c8caa5a8eea467413b9499c448dd0750144 9 511 3 7 11 2047 17 131071
def cc_92_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x937b6a684c41242019181102 0xd52320118604d9a4638230809bd52dca871e5684adad15c503eac458b2b4056d50ae241f869a414d216970343 8 255 3 7 10 1023 17 131071
def cur_92 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_92_2 (Nat.sub p 64)) (cc_92_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_92_0 p) (Nat.blt p 32)
def hc_92_0 : Nat → Nat := unpackHintV5 0x89d5ee1787e7fd309d236973c861c206964f5c97f8a2599329393694c68f1292443ff52cfe40c3d3130f360b3a3154e2c3032f2e0a3b412710ec93e431aa52c6900c17e1305e00c14d1584d4300d92e00e3410031ac00006 0x1c71db0030c36c032c31b4474750d350c31b88787a0d7a0c394039c39c031c39c30c39c39c30c39c39d5439c39ea839f00e71d9d9e9e9c32e7000c39d679ea7b00303d4d4e5e5c09cb9c0000b9c0270e7270e79e759e7a9f9e0fa27a391c47c3caf816586018e1ce1ce1ce5961ceaa5ce1cf545ce059658061865a6aa5965af545965965cf3cf3cf4e5d0c34c73e79df67a79cb0e7db0c30076cf3c0c32c6d1430d434d3d1c6e2830e835e3e1e500db0c300c30e70c30e70e70c70c39d5439c39ea839f0c1b443431b8838395f0b2cb6c0c32e72d4b2e8bb00c0714d4c65e5c809cb9c0000b9c0270e72c70db2759e7a9f8e0fa23a391c43c3caf81738738073873965863861ceaa5ce1cf545ce059658061865a6aa5965af545965965cf067be1b3b3cf3cf26863be1b3b3cf3cfb6c14d45500c30db00c70c30cf0c350c6e2956835e830c039c39c039c39c39c39d555439d5439ea839e75679e79e79e7473c72cb6ced30e79cb9e79d2cf2c1cf6e79e72e79e76c3c73c704125e5c94c0540000b9c0279e79d0e75527a9e8aa4714746aaa605ce1ce01ce5ce1ce5cea1ceaaa1cf545ce059658163965967965a865af54596ab3c38c39e79e7a7abc3871873cf3cf4f6db06d1497a2aa58030c36c031c30c33c30c34d5430e8300e70e700e70e70e70e70e7550e7aaaa0e7aa9ea9e79e79e79e1cf1cb2ea9e970e79cb9e79e2cf2c1cfae79e72e79e7ac3c73c714d4c48225c0a80000b9c0279e79e759e0e7aa3e8bebe51554b2e05ce1ce01ce5ce1ce5ce1ceaa5cf41cf554059658163965967965969aa965d0755148a94279c279e79e7559e7aa9e7 22 4194303 9 511
def hc_92_1 : Nat → Nat := unpackHintV5 0xdc80c6ba153309656af6bb3212d6c16a8259f13d6b876143fd9edf1c68e947d71d16b312ed3870274141396051ab100d301465c1e2e42516d028a68805200a2720f114128878144001e1a92b840ca01a43000069 0x9e79e793d33cf9d9e79e79e79e7f0203d4d4c82270e79cb9e70e79cb9c0279e79e759eab9e089e8e4bd15550f2c079e78547a6aa79f438473ce03ce7ce7ce3cf3aac73d5551f38739f39739f38739f3973ce7679e79e4d3531c79d9e79e79e79e7e100e29a989040f4bce1cf3973ce1cf3973801393cf3cf3acf55c704474728a87aaa59701c71c2a1d3551c7a1c239e701e71e71e71e79d5639eaaa879c39c79cb9c79c39c79cb9e679e79e79e3c3a39e3a63cf3cf3cf3b3d3cf3cf3cf3cf3cf3b3d3d3974f3d3073e79e79e79d9e9e79e79fce9af3cf3cf30f1cf1c1041089c39e72e79c39e72e70027279e79d56aa9a8aaa64bd1552ecaaa09a698263a67a67a63aca83f3ce13bf3cefceaaaaa9cf55554bce9ce1ce9ce5ce9ce1ce9ce5cf7d7c028e8e57c00039c039cb2c36cb9c39d54b9c39ea8b9c032c72cb2cf2cb2d3552cb2d7aa2cb009c3c7430cf27279e79e70b1e79e73c753430c709c9cb0e79c3c7830cf27279e79e70b1e79e73c797830c709c9cb0e79c2d35e79ca72e861a6138cf4f3961cf819e18618618e00a186a1a600b418741ae0152800007380073861861ce1ceaa1ce1cf541cf3cf3cf35791cf0d30e79e767a79e79e7 21 2097151 9 511
def hc_92_2 : Nat → Nat := unpackHintV5 0x9a1bcc10605acedac02b2496b59e3b3c972d6488181ef2a8e50945bcb60016f 0x3800e00023a3a8e9a8e38043c3d0ebd0e3ca00003ce3ce3ce3cedce3ce3ce1ce3ce5ce3ce1ce3ce5cedceab3b73d54fc0001c014f3d4f4c013d1e8f3e8f5c023e1e53e70e73e72e73e70e73e72e700001e76e73e73e73e71e76e7559db9eaa782a6a8298e99e99e98e00052aa9d26bd2698000373bf3b73bf3aa73aaaaa73873a73973a73873a73973b73d53f3f8081e2092f2f3873ce5cf3873ce5ce013cf3ceab3d4fcf053515551c0f3cf05547223e1d568f5e8f3c1f9e701e73e73e71e755553e70e73e72e73e70e73e72e79ea9f9f820382083b2f2e4a73873ce5cf3873ce5ce004e4f3cf3aacf53f1c145475501c71c1551c887875553a1d7a1c707e79c079c79c79c79d555479c39c79cb9c79c39c79cb9e7aa7e79e79e791e7ae7cf3cf3cf4f3cf3ce79e79e7a26bc3ae3cf3cf3cf4f3cf3d0020a5eaa5970971d73d73d71d74d5574c000006e78e76e78e76e7558e7a5e7aaaa5e70e75e72e75e70e75e72e7 21 2097151 9 511
def nh_92 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_92_2 (Nat.sub p 64)) (hc_92_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_92_0 p) (Nat.blt p 32)
def f_92 : Nat → Nat × Nat := unpackForestF 0xb4b02d1c0a4b8e9580a3b8a9580a33864d2034b824d203430252df13478d6de156024edd13470d6dc156024cdb1446316da16c6315d93456255809230212d726c448ed5a6c569511233525b1113b4c5b13154444cd196c4655111230211d01443e48c083f38558e056020ecd15c3248c08372c510b056020cc994b2650c082f22110645b1e1b064571ad1460560208c4b4b12d0c081f0e110145b0a1b0145706d1410560204c001f 7 11
def ch_92 : Nat → Bool := dagCheckNodeV5 0xffff00000000ffff g_92 ep_92 4 15 bds_92 75 (dagTraceF 0xffff00000000ffff [0x5555000000005555, 0x3333000000003333, 0xf0f000000000f0f, 0xff0000000000ff, 0xffff] 8 f_92) cur_92 nh_92
set_option maxHeartbeats 0 in
theorem rc_92 : dagCheckRootsV5 0xffff00000000ffff g_92 ep_92 4 15 75 bds_92 (dagTraceF 0xffff00000000ffff [0x5555000000005555, 0x3333000000003333, 0xf0f000000000f0f, 0xff0000000000ff, 0xffff] 8 f_92) (cur_92 0) (nh_92 0) [0x5555000000005555, 0x3333000000003333, 0xf0f000000000f0f, 0xff0000000000ff, 0xffff] 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_92_0 : treeBlockF 0 32 ch_92 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_92_1 : treeBlockF 32 64 ch_92 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_92_2 : treeBlockF 64 75 ch_92 = true := by decide +kernel
theorem nj_92_1 : ∀ i, 0 ≤ i → i < 64 → ch_92 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_92_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_92_1 h1 h2)
theorem nj_92_2 : ∀ i, 0 ≤ i → i < 75 → ch_92 i = true := block_join nj_92_1 (fun _ h1 h2 => treeBlockF_at nb_92_2 h1 h2)
theorem nc_92 : ∀ i, 0 ≤ i → i < 75 → ch_92 i = true := nj_92_2
theorem lb_92 : LowerBin 0xffff00000000ffff [0x5555000000005555, 0x3333000000003333, 0xf0f000000000f0f, 0xff0000000000ff, 0xffff] g_92 9 :=
  lowerDagV5 (kn_cons lb_48 (kn_cons lb_55 (kn_cons lb_63 (kn_cons lb_40 (kn_cons lb_51 (kn_cons lb_43 (kn_cons lb_49 (kn_cons lb_59 (kn_cons lb_67 (kn_cons lb_6 (kn_cons lb_13 (kn_cons lb_14 (kn_nil))))))))))))) rc_92 nc_92 (by decide +kernel)
def g_93 : Nat := 0x1117155f155f577f
def ep_93 : Nat := 0x448422000000448000042200006004a004a00280006040a040a020811121000100002201114155015505440
def bds_93 : List (Nat × List Nat × Nat × Nat) := [(m_80, s_80, 9, g_80), (m_78, s_78, 8, g_78), (m_86, s_86, 8, g_86), (m_81, s_81, 8, g_81), (m_88, s_88, 8, g_88), (m_83, s_83, 8, g_83), (m_79, s_79, 8, g_79), (m_92, s_92, 9, g_92), (m_82, s_82, 8, g_82), (m_85, s_85, 8, g_85), (m_89, s_89, 9, g_89), (m_16, s_16, 7, g_16), (m_87, s_87, 8, g_87), (m_90, s_90, 9, g_90), (m_84, s_84, 8, g_84), (m_91, s_91, 9, g_91), (m_28, s_28, 7, g_28), (m_31, s_31, 7, g_31), (m_34, s_34, 6, g_34), (m_17, s_17, 6, g_17), (m_33, s_33, 6, g_33), (m_36, s_36, 6, g_36), (m_19, s_19, 6, g_19), (m_32, s_32, 6, g_32), (m_37, s_37, 6, g_37), (m_39, s_39, 6, g_39), (m_43, s_43, 5, g_43), (m_15, s_15, 5, g_15), (m_26, s_26, 5, g_26), (m_46, s_46, 6, g_46), (m_47, s_47, 6, g_47), (m_40, s_40, 5, g_40), (m_29, s_29, 5, g_29), (m_56, s_56, 6, g_56), (m_48, s_48, 6, g_48), (m_55, s_55, 6, g_55), (m_53, s_53, 6, g_53), (m_54, s_54, 6, g_54), (m_61, s_61, 6, g_61), (m_62, s_62, 6, g_62), (m_27, s_27, 5, g_27), (m_18, s_18, 5, g_18)]
def cc_93_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xaa15502a814c2a605206901402a0050027053809a0cd02681340941ca0250120290048023831c08e04606301141802b3340e4001 0x51240f864041240e07c0d044039240c064029240a87c0983406b40019240785c06c54060340496003160021400535f0435703a5f02a5701a370f46f0ec6b0dc670cc630bb6f0b36b0a3670936308b4f0834b0734705b4301124ea45fe9c57e8b5fe835be7b57e6353e5b4be5347e425fe3a5be3257e0a53df24bdea47dd23fdba3bd7a37d3233d215fca15bc5157c2153ba14bb8147b593fb493bad137aa133a792fa692b9f1279c1239985f8885b80857798536b04b678476203f5f03b4e837488334302f4002b2f827298232301f1c81b10017008130003f 13 8191 6 63 11 2047 20 1048575
def cc_93_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82c2ac6b0a86559424188a20809f1749d0705c0689915c97058560581334c121408c4300b102c00 0x7edbdf3677a1f1d85c891be146780dbde36774d1d43474ed1dba706a9a05010120819a70100418a605e9a038100c0816a700a0415a605360142804a941317c4b59c20204f9dd126a48940181044d1dc56f6d59da46f6519d84575cdbd636754d5d1b47429681010 10 1023 4 15 11 2047 18 262143
def cc_93_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0d0d0c2b9b8b1b0a9a8a17d7871706968616060524948411d18111009080100 0xba4eee133b6112c824ae092a824bd1aed463b09aeb263a890e9164a05f2716498dbe5b67945f2415ca31be7c679adbe4b678ed1e2864861f20864 8 255 3 7 11 2047 18 262143
def cc_93_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a418c62184610805f16d1a16819164181601805895154141501314c1304851138ce0344c12880a 0x3fb70c851fe138f2493e23cf0483c92cf08d3e92ff64afd127ee48fb370e8d839247e092f7a47dc5336370d45331b40c69433580cae031350c69c31567c99df0b50fd59fac67e715f8b5ada5af5967d256f4157ce52f0147 10 1023 4 15 11 2047 18 262143
def cc_93_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x949ba6c1b06c192605805c5705856054505401003c4f03c0e1380d1340c119860180601806005401 0x1459de7da85e567ba8b56299ebd2bd596ba92cf4e56e98abd292b9e24f364ae6891cc834970492a0924c124e36b986c72c9ae5131c92338f4f9184d2289a4413490adf1d59e352b4596b892c70e56e1633c226b834cf0492e0523b2947 10 1023 4 15 11 2047 19 524287
def cc_93_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x72b6594c860ae562a950a8132913a1a4d06130180a4492410480391c0e06229098401201 0x61b67c24d78299f011ddfa37a424f7b1c28893dda37b82916a4d2e1265a130b527968912e49fdb93bb626f664ceca3858460ae47f5a8deb0ae55470a82b942d02852852580a370140d42853850567 9 511 3 7 11 2047 19 524287
def cc_93_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x84201801f17c1e1781d1435004010040100400a6280a02449024081200711c061018000000000000 0x6f044dc0b9b40d3602678c6fef8c7dadbfadb1f534fe9697ced1f85a1efa6fdd49fb691f651feba37d56dfa89bf4d1be916fd126fa049f35be65144c82898c5133ab7e6567cb6ad925af1cb1e295b 10 1023 4 15 11 2047 19 524287
def cc_93_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xc1b2a9a8a1a0999891908965605958515049484140404032303030291a0a0801 0x7f9648012b7f1237e8347d8447c8247b8347a8247e3437d24f7c2437b23f7a23379064780447706476034733407405c7226472a6f71a63734547103470064 8 255 3 7 11 2047 20 1048575
def cc_93_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a41902318c22188220882027c5f07852c445013c4e1380d1304841c4701c061180601440500000 0x9024f8fa478f05c8e0248d0348bb4b8b3478a84c898249934f98b4b93b47923439124f90a4b8ea478da438ca3f8c23b8a23789233879488613487a4c859308613c85a448813f8713b869378513384c708347081b70842378393b829378212b81127 10 1023 4 15 11 2047 20 1048575
def cc_93_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x729c0701c06899151540501314c103401003c4e1344c1300b12c092150320c030048100040000000 0xa5d67a1467a04579fb5a8a06b810676b85b680575f84b4f0479e03b9d8339d1449ec6b9cc638906b7a063490439b1649bc559a94b9a147979589614497a5c959409614c95a54951649814f9714b9694794943933409405c934549283491844 10 1023 4 15 11 2047 20 1048575
def cc_93_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xbd2e1b82d18ea308c23084a016d5b06c1a168146500f5384c22c4a12448120071184240441000400 0xb283fb183bb1037af833af470ae460b3d67b345aaea67ada578e86b828676d85b688574082b30027ac02bab823ab134acb6baab638d86b7c0632a033a927ca9d6fa8d67a82568c86b7b0636c85ba74678c06b820676004b5284751847a637051047a4838a3024a493ca2820a302ca2934a502fa402ba3827a2023a1b70a0b60 10 1023 4 15 11 2047 20 1048575
def cc_93_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xb46d0b06c0b02c0a8aa0a82826f5b06c1b05595054141500e6380952046218051104310842004401 0xbf964be934bbb40bc95cbbc54bb134c146fc0463bf36fbe363bdb4fbd34bbc347bab439a86f6284f538474383f34837b9b6fb926fb8a379a06f5303734027b737cb7d6fb6d67b63569106b7d0636e85bb53679086b838674103b3383733027b447032027b2048b0834b214cb0030b083cb0144 10 1023 4 15 11 2047 20 1048575
def cc_93_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8720c4710bcab4a4a90a42726f1a1645815c57058551451012d4b02c0a120871094200441000400 0xce040ce84cce154cd864d084fcf84bcf047cd043cbb40cc95ccbc54cb134d1b4fd134bcc347cab436484f6104b558474b0434583f4203b368372c033c9048c7834c914cc7030c783cc7144c983fc883bc8037c6833c6470c5a376083b548374182b35827c4064c482bc3823c3134c2b436384f4a0434483f2b033c1964c0944 10 1023 4 15 11 2047 20 1048575
def cc_93_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x8a308e1042076eec1d8347680d01a03405ccacd581cf380700c9990302498901110d61801983006008408801 0xdfc63ad9375783715017de567ddb56d196bbd95b9906b7505b08813dcd67dc256d116bbd15b9886b7485b08013d5a40db13fda937da03fd983714817d9470d523013817d8d67d845ad4a30cc16bc5967bc15bb89579386b840677385b698572381f1d01b1181707013d5344d6a7cd4254d5b60d5457cb95bbb94b9305b7304b06813d4466d756fd6567d4b44d3a56ca96bc2963ba95b9206b7e0637085b05813d2c556f84b69047d0058ce844d015c 11 2047 4 15 11 2047 20 1048575
def cc_93_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x25b3ed7c0d6591aa8540a4513a113c6780ac9231502804889010205c08001 0xd7233b793fa992f6703f4802f1c017de23fdca3bd8a37d6233b693fb3937a892fa59276603f5e0374702f3f0271b017e9455c114bb99477884b6a8472881f2201b1a0170f0139e9232f0230e813a712ba11274282b3a8272781f2101b190170d813e7253e6b56dfa5bc015b9c9237785b2d0230c813e2263a01273982718017e4c55bf14bb91477684b6a0472681f2001b170170b813ac9434e0430b013b513bae9376183b588372481f1e01b160170a013e2a44e1b53e245be1256be15baa9437585b4c04309013e0244 11 2047 4 15 11 2047 20 1048575
def cur_93 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_93_14 (Nat.sub p 448)) (cc_93_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_93_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_93_11 (Nat.sub p 352)) (Nat.blt p 384)) (cc_93_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_93_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_93_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_93_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_93_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_93_5 (Nat.sub p 160)) (Nat.blt p 192)) (cc_93_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_93_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_93_2 (Nat.sub p 64)) (Nat.blt p 96)) (cc_93_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_93_0 p) (Nat.blt p 32)
def hc_93_0 : Nat → Nat := unpackHintV5 0x85197d3ffba45f1a38eee46a37297233647c11a11c48c49efc5d2d48accf71d5165469f9a4649c5822198d28f27694700a4c3139b3166c8c09ff4dc43133a1d550d0d8b47c5eb36a26ea1c11368f86e66d42ab3200b9272035c9b00006b8000000000000 0x30f030f100c0c00cdc140e7d40c0d500c0c0f50f0303032f030b03030dcdc0303030396aaaa2a372aaa81d41c1c1c1c1c1c1c1c1c0707073701c1c1c1c1c1c1c1c4c4c4c4e81e0f55a80e03aa80eaa08ae37080ea03a8bea0ba13131313131388a073eaa0b8b81918a823e91821eaa846460b81818baa5e85aaa9511954accb54aa0383839180e0e0e0ea83a0ea0e0e0e0e2626262740e7eaaaa115c4610bc2f501c074aab4b21aac5f505d098989898989d5552323023230440303aaa5500c0c730b472f730b472f5508c8c03030303544d44c4d54a2aaa9513513135501c1c070707070707070713139aa4608f822281aaa81cf806460606216aa97aa8464601818181ac36aab4aa5446555528393aaa8383aa80e0e0e46038383838383838389898989d03acaaaab4aaaa115c46101c2f501c07517d4174262626262627e201aac0b8180606ab406e6e6e6e0b5521ea1e1b9b82e06062e9e16e65e9e16e65f2c546e5550989d427540ea0e0383839b80e0e0e0e0e0e26260e0e0e260e0e0e0e2626262740e7f7880606aa073e0b81806060601e1e1e6e0a87a8786e6e0b81818b8785879787858787cb151b9555555540ea0e0383839b80e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e2626262740e7f07aad04571b842f501d41f07d541f5545f505d098989898989f87aad07886e6e06e6e01ea1e8606a62e8606a62e1b9b92a85cd2d0161605858585cb50989d426546e555503a83838389898383838980e0e0e6e03838383838383838989d58785878816160166e01ea1e1606162e160616161b9b8a173ea1616a8161605858585cb5555151b955540ea0e0e0e0e0e0e0e0e0e0383839b80e0e0e0e0e0e0e0e2626262740f07aad41705d54175504571b842f501d417505d098989898989c45508c8c50b9f550bcbc2c8c0b2f0b2f5411f48c117540d50f554a88caaaa56655501c1c1c8c0707070707070707541d07513131313a0757555508ae23085ea03a8be2fa82e0ba555a593d544c4c4c4c4c4eaaa9191811918223981a98bb981a98baa846460585d552a8161605858585aa26a2626aa515554a89a8989aa80e0e03838383838383838989cd523047c111035545d542323142d5542e7c0b230b0b02c2c2c2d61b555a552a232aaa941c9d5541c1d540707072301c1c1c1c1c1c1c1c4c4c4c4e81d655555a555508ae23085ea03a82e2fa82e0ba131313131313f103d43c373702d560bc2c0b2f0b2f0b0b55a037373737073174303430373175aa9962a372aaaa84c4ea130750701c1c1cdc0707070707070707070713130707071313131313a0757bc40f50f0dcdc0b0b550b9f0bc2c0b2f0b2f0b0b0b00f0f0f3700f170f030f030f0f5658a8dcaaaaaaaa0750701c1c1cdc0707070707070707070707070707070713131313a075783d56822b8dc217a80ea2fa82ea0f83eaa0faa84c4c4c4c4c4f70dc0317031705c0c0b0f0b42d0b0b00b0b0b3700b170b0b0b0b0b02c2c03030b9f03030b0b030303aa2a372aaaaaaa81c1c1c1c0707073701c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c4c4c4c4e81cfe0f99a08ae37085ea03a82e0baa82e47aa82ea0ba131313131313dc3700c0c0c0c030302cbc2cbc2f0b00c0c2e7c0c0c0c0c0c3c0d0340c0c00c0c0cdc00c0c0c0c5c0ea8a8dcaaaaaaaa0707070701c1c1cdc0707070707070707070707070707070713131313a075783e66822b8dc203a80ea2fa82ea0380eaa0394ea84c4c4c4c4c4f70dc430f735cd430f03737373700303030300c0c0303aaa0b0b0b0b02c2c0b0baaa030380ea8a8dca84e84c4eaaa81c1c1c1c0707073701c1c1c4c1c1c4c4c1c1c1c1c1c1c1c1c4c4eb70dc03030340d030f00337030300303030300c0c0303030b0b0b0b02c2c03030b0303030303030baa2a3720386eaaaaaaa81c1c1c1c0707073701c0c1c9c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c4c4c4c4e81e0f99a08ae37080eaa80e03aa80ea03a82ea0ba131313131313dc3700c0c0c0c030305c5c5c5c171700c0c5e7ea8a8dc80eaaa81c1c1c1c0707073701c0c1c1c1c1c1c1c1c1c4c4c4c4e81cfe0f99a08ae37080ea03a85ea17a131313131313dc3700c5c0c5c170302cbc2cbc2f0b02c0c0e730f735cd730f03737373700b0baaa0303aaaaa2a372aaaa84c4ea130707070701c1c1cdc0707070707070707070713130707071313131313a073fb70dc0317031705c0c0b2f0b2f0bc2c0b0b030303030b170f1745d170f01717173700b0b0b030303aa2a372aaaaaaa81c1c1c1c0707073701c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c4c4c4c4e81cfe0f99a08ae37085ea03a8bea0ba85e17aa85eaa131313131313c3c0c3c403030033705039f5030354030303d43c0c0c0cbc0c2c0c0c373700c0c0c0c3d43c0c0c0c6c0c6c0c0c1b371b1b00c0c0c0c6c6c6c6e5aaaa8a2aaa84c4c4e7e2289a01818aa1191806060606aa119191918060606068ebebe8eaa51555542626898989d523047c11140d5540e7c0323030310b554bd54232300c0c0c0d46c6d5546d541b231b1b00c0c0c0c6c6c6c6d955954a2aaaa84c4c4e7ec3c2c3c40b0b00b3700f50f0b030b170b030b0b0dcdc50b9f50b0b540b0b02c2c2c2c3d43c2c2c2c6c2c6c2c2c1b371b1b06c6c6c6c2c2c2c2e5aaaa8a2aaa84c4c4e7e22a84646289a0585816161616aa1191919187ebebe7e16161616aa51555542626898989d523047c111035545d542323142d5542e7c0b230b0b02c2c2c2d46c6d5546d541b231b1b06c6c6c6c2c2c2c2d955954a2aaaa84c4c4e7f70dc0303030300c0c0b0b0b0b02c2c030303031303030b3f435f5f430dcdcdcdc030303030b0b0b0baa28aaaa131384c4c4f70dc03030340d030f00337030300303030300c0c0303030b0b0b0b02c2c03030b0303030303030b3f1b1b1b1b06cdc6c6c03031b1b0303030303031b030303030b0b0b0baa28aaaaaaaa1313139fdc370fcfc373715d5c37370fd5cfc6c6c6c6c1b371b1b06c6c6c6c6c6c6c6ea8a2aaa84c4c4e7f70dc0dcdc0dcdcaa2a372aaa81c1c1c1c0707073701c1c1c1c1c1c1c1c4c4c4c4e81e0f99a08ae37085ea03a8bea0ba131313131313 25 33554431 10 1023
def hc_93_1 : Nat → Nat := unpackHintV5 0x96b20a64992278b9ed8e182aca7d57169e0fa8c711ce45b4d9f3661ce3585426659bcf2955da234fbcb752d023e4394f58fb22663730f30cbaa232d30b74a2aa4320faf6082782e20520987de86c1f6e0187b684a18f8bc4437c0d0d826b823026104488f0000224 0x2e067e36a0f44c4c4c4c4c4c8c8c08c8c1100cfc5c0cfc5d54232302c2c4c4c4c4c4c4d44d02c2c0b0b0b0b1b1b5555521b06e1b82e0b9556954070701c1c1c1c1c1c1c1c4c4c4c4c4c4ea91823e08881aaa2eaa11918a16aaa173e05918585816161616a3636aab4aa44636360dc3705c1720eaa83aa80e0e0383838383838383898989cf8989898989a26262626262689a2626262626898989a26260266626460262e26262606262626162626261626262636262709f61d9061f06c1b061e0767676760060606060181806062626262626261616161605858161626262626262606062606370dc47636360d8dd0181d01c0705c170383838380e0e038383c0e0f40e0e0e0e0e0e0e0e262626262627d876018181a0681878019d8181801818181806060181818585858581616018185818181818181859f8dc3711d8d8d8060636374060701d01c0705c170383838380e0e03838383838383838383838383838383898989cf898989898987898989a26260266626760260626262626262606260626262626260626262606262626162626261626262636262709f61d87e7e1d9d8aeae1d9d87eae7e370dc47636360dc370dc370383838380e0e0383838383838383898989cf898989898987898989a26260266626760262e262626062626265e2626261626262636262709fc01f03d43c3c0c3c5c3c0c3c3c003d43c3c2c3cbc3c2c3c3c00fd0d0cfc3c3d543c3c3c3c3c3c3c3c6c8c3c3c6c6c3c3c3c3c00006c5c6c0c6c0c6c5c6c6c6c2c6c2c6cbc3d60f0fa0f1b8ac006e1b86e1b84c4c4c3d41c3c3c1c1c3c9c1ccc009c1c9c1c9c1c9c1c4c4c4c4c4c4c4e81cdea802a801fab9faa800dc370dc37280000001f8baf81af819f8bab97af85af85ab978f8f89898f8f8f8faa8013839383938393838989909898f8f8f8f8f8ffc07c0007c0c7c7c7c7c7c5d54007c2c7c7c7c7c7cbd5400fd5cfc7c7c6c6c7c7c7c7c7c7c7c7c7c7c6d555400006c5c6c0c6c0c6c5c6c6c6c2c6c2c6cbc7c7c6c6c7c7c7c7c7c7e954006e1b86e1b84c4c4c7c7c9c9c7c7c7c7c7c7c1c1d54009c1c9c1c9c1c9c1c4c4c4c4c4c4c4e81cdfc40350300c0c0f50f11d3c030303030f5886c0380e1b86e0f0f550f0f05f7b5f630030350340c0d1cbd3c2d3c2d1cbe84c4c0c4e83d41c072700c1c0c1c9c1c9c1c4c4c0e1313070703130707c3c0c3c403030036705039f5030354030303d43c0c0c0cbc0c2c0c0c474f00c0c0c0c3c3d543c3c0c0c0c0c0c0c6c0c0c6c6c0c0c0c0c06d8c6c6c00c0c0c0c0c0c0c0c6c6c6c2c6c2c6cbc3d60303a031ba21b00e0386e1b84c4c4c3d41c0c0c1c1c0c9c1c1c072700c1c0c1c9c1c9c1c4c4c4c4c4c4c4e81e22a806062a8464601818181aa90d80701c370dcaaaa046464646006060606060606068e5ebe16be168e5ea262689aaa80e4e018381839383938389898989b40e2626a89ad523047c11140d5540e7c0323030310b554bd54232300c0c0c0d46c6d555546d555406c8c6c6c00c0c0c0c0c0c0c0c6c6c6c2c6c2c6cbd1b5565521b00e0386e1b84c4c4d275541d54072700c1c0c1c9c1c9c1c4c4c4c4c4c4c4e81f030303004323234300030303031b86e000380e1b86e430f2348d430f00000303000472f5f0b5f0b472f8ac4c4c0c4e2b27072707000307030727072707131321313073303130733c0c0d031f030f0000c030323030303000030043232343030b03030303032f00030303031b0f1b46d1b0f03031b1b030303030303030303031b000003030303030303031b1b1b0b1b0b1b2f1b86e031b8ac0c0e8000e0386e1b84c4c4c9c1c9c1c0c9c1ccc0c0c1c1c000c1c0c1c9c1c9c1c4c4c4c4c4c4c4e81cdfc40f50f0fd0c0b50b02c2c0b0b0b0b0f5886c1b86e0b82e0f0f550f0f05f635f6303f17430343033f170b0b50b42c2e84c4c2c4e83d41c072709c1c9c1c2c1c2c1c4c4c2e131307070b130707b0f0b0f102c2c02d9c03d43c2c0c2c5c2c0c2c2c3f43142e7d42c2d502c2c0b0b0b0b0f0f550f0f0b0b0b0b0b0b1b0b0b1b1b0b0b0b0b01b631b1b01b171b031b031b170b0b0b0b0b0b0b0b0f582c2e82c6e886c1b86e0b82e1313130f5070b0b07070b27070701c9c270727070b070b0713131313131313a0788aa11918aa0585816161616aa4360dc3705c172aaa81191919181f8baf81af819f8b8585858585858585a8989a26aaa039384e0e4e0e160e160e26262626d038989aa26b548c11f04440d55175508c8c50b5550b9f02c8c2c2c0b0b0b0b51b1b555551b555501b231b1b01b171b031b031b170b0b0b0b0b0b0b0b46d5595486c1b86e0b82e13131349d55075501c9c270727070b070b0713131313131313a079e46467e00161616160016161616370dc00370dc1705c9e1e4691a9e1e00007e2ebe06be067e2e16160011589898589c564e0e4e0e004e0e4e0e160e160e2626426260e6616260e6761616858f8587800162791919f858185858581858b800585918585858000580058585858d878da368d8785858d8d858585858585858585858d80000d8b8d818d818d8b85858585858585858dc37058dc561617400370dc1705c2626264e0e4e0e164e0e6616160e0e004e0e4e0e160e160e2626262626262740e6ff8daf8daf9bfece0606bf8f8f9f8d8f8f8d81818dc4e0e6fffe370f8faf8c64e0e6f0c00c0c0c0c030302c2c2c2c0b0b00c0c0c0c0c0c0c2cfc6e1b886c0380e0b82e430f5f57d430f05f635f63003030303030303030b0b0b0b0b0b0b0ba13130313a2707270701c9c030703070b070b071313131303a07131307070313070786006060681a061e006ce0606006060606018180606061616161605858060616060606060606167e361e368da361e0363636006063636060606060606060606063606060606060606061616161616161616370dc436018dd0181d01c0705c170989899383938380e4e0193838381818383818381838583858389898989898989d03ea1e0006060616060606167e0d8dc07078f8f87836072f2e06060606060606c6c6060606061616161619804e4e0e060e2627039b95818c8c8cfc018c8c8d5c00fd5cfc6e1b8006c1b86e1b86e630f231f231f630f01b3f17630397033f17572f630b970b572f013330027072707002709c1c9c1c9c1c9c1c4c4c4c4ca0737132b000fcfc3f15d5c570fd5cfc6c3c6d1b46c3c06c6c6c06c5c6c0c6c0c6c5c6c6c6c2c6c2c6cbc6e1b886c1b86e1b86e1313132707270701c9c270727072707270713131313131313a07f0f55a0f10dcdc0dcdc255039a5a00c0c0f50f4f0b472f4f0b472f0dcdc0303030396a1313a84ca8dcaaaa07507070713130707071301c1c1cdc07070707070707071313a 26 67108863 11 2047
def hc_93_2 : Nat → Nat := unpackHintV5 0x967acae58d82295b210a404ad0880b0121281b57f62a7dec8a207596b19c42a466b0ebf9976a9a611e979668bbe55708653b9b454a2a9790aabc0428005508e8233e28824de7b45326aa68a8bc1e256a988816a881866fe84fe2370d32d8c208a88002aff0000015 0x88a073eaa0b8b81918a823e91821eaa85e160581818baa5e85aaa846460b81818bab236a5e16165eaa038380e0e0e0ea83a0ea0e0e0e0e0e160f3e0e0e0e0eaaaa00e660e4600e2e0e2e0e0e0e060e060e0eaaa0e0ea0e86aa0e5e0e0f0389838d83c0e0e0f3e7f0dcfcfc7e365e173e0e1fe20181aa81cf8382e060181aa838381d9d9d9d828383838383a16a1e178581606062e16165e5e16161e1e1ea1e1d9d82e06062e7e371f8dc5e16165e0ea0e038380e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e160f3e0e0e0e0e0fe20181aa81cf82e0601818180787879d82a16a1e178581606062e16161e5e16161e1e1ea1e1d9d82e06062e1e1e1f078d87c5e16165e0ea0e038380e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e160f3e0e0e0e0e0e1eaa0e0e00e660e7600e2e0e0e0e060e0e0e1e0e1e0e0e0e0e0e1e0e0e0e0e0e0e5e0e0f0389838d83c0e0e0f115423231542f0b02cbc2cbd54a2aaa9555408c8c8c8c17c5d1c0d1c0d7c5cbcbd556a1384e954070701c1c1c1c1c1c1daa44c1c1d13588aa11918aa17858165e165eb4faa951195554a823e91822ea81aa5ea85ab2aa038380e0e0e0e0e0e0e0e0e160f3f5489a0e83aaaaa8039983918038b838383818383839783d542740e374aaa0e0ea0eaa0e0e0fe207a8786e6e05a8785e1605978597cab1455550787aa838381b9b9b9b82f8ba181a181af8b9797d552c2709c83a8380e0e0383838383838383838583cfd55098383c275e207a8786e6e05a8785e1605978597d2ad3e51555507c115c6e10bd407517d4174a83a8380e0e0383838383838383838583cfd542703c0f40e1eaa0e0e00e660e6e00e2e0e0e0e060e0e0e5e0f509d55550383d03d5038383ee1b8062e062e0b818165e165e178581606062f54515407552f87afabeaf8781b9b9b9b80b8b8383838383839797d55542709d0383838380e0e038383838383838385d55098383c275b86e018b818b82e060597859785e160581818bd514554074fd541f334115c6e10bd17d417550383838380e0e0383838383838383838583cfd542703c0f40e1e0e83a0e0e00e660e6e00e2e0e0e0e060e0e0e5e0f509d55550383d03d5038383f61d88e8e1d9d8165e165e17858165e165eaeae1d9d8ae8e8e5e16165e0e0e0e0e038380e0e0e0e0e0e0e0e0e160f3e0e0e0e0e0e1e0e83a0e0e00e660e7600e2e0e0e0e060e0e0e5e0e0f0389838d83c0e0e0fe1e2626262626261e21b9b81b9b809a8189898989a89898060607a87bf85bf97bf85bf9786e6e01818181cb555514555507a83818183838d8d838380e6e4e4e018381839383938389898989e1e061e201818019b8281cfa8181aa018181ea1e0606065e061606061b9b8060606072d5554515554261e262626898989818981898989898981898989898980995899b80981898989818989899789898985898989c261ea0e06060e0e064e0e0e039b93938060e060e4e0e4e0e2626273e2626262626263744c4c4c4c4c4c8c8c08c8c1100c0c4c4c4c4c4c4d44d00c0c830b832f830b832f5508c8c03030303555a5528aaaa1b1b5555501c9c0307030727072707131313131313aa4608f822281aaa81cf806460606216aa97aa8464601818181b2ab2a94555509a26262626262689a2626262626898989a262602656264602606262626062626265e2626261626262709a9393aaa8383aa80e464e4e0183818393839383898989cf8989898989898df8789898989898987886e6e06e6e01ea1efe06fe2efe06fe2e1b9b826a1626262626a262605858161616172d55545155541ea0e16160e0e36360e0e039b939384e0e4e0e160e160e2626262761e161e205858059b807a878581858b8581858586e6e285cfa8585aa05858161616172d5554515554261e262626898989858985898989898985898989898980995899b8098b898989818989898589898985898989c261ea0e16160e0e164e0e0e039b939384e0e4e0e160e160e2626273e2626262626263775303b81a9b13b44c4c4c4c4c4c8c8c08c8c1100d4c5c0d4c5d54232302c2c4c4c4c4c4c4d44d02c2c0b0b0b0b555a5528aaaa1b1b5555501c9c270727070b070b07131313131313aa4608f822206aa8baa84646285aaa85cf81646161605858585b2ab2a94555509a26262626262689a2626262626898989a26260265626460262e26262606262626162626261626262709a9393aaa8383aa80e464e4e1383938385838583898989cf8989898989898dee1b9061f06c1b061e06e6e6e6e00606060601818060626262626262616161616058581616262626262626060626075451555555544e0e4e0e039b9393836360e0e06060e0e060e060e160e160e262626262627b86e018181a0681878019b818180181818180606018181858585858161601818581818181818185a5d514555555550987898989a262602656266e02606262626262626062606262626262606262626062626261626262616262627099383938380e6e4e4e0181939383838181838183838183818385838583898989cf8989898989898dee1b896961b9b8b6b61b9b896b69754515554261e262626898980995899b8098b898989818989899789898985898989c264e0e4e0e039b939384e0e4e0e4e0e4e0e2626273e26262626262637e1e2626262626261e21d9d81d9d809a8189898989a89898060607a87bf85bf97bf85bf97876760181818187ac0607436374476363601c070dc3703a838383d038383c038380e0e0e0e0e0e0e0e26262627878187880606006760a073ea0606a8060607a878181819781858181876760181818187ac0607406374476363601c070dc3703a83838383838383838380e0e0383838383838383898989cf898989898987898989a262626062606262626262606262626262602666267602606262626062626265e2626261626262636262709d13131313131323230232304403031313131313135134030320c2e0cbe0c2e0cbd54232300c0c0c0c6c6d5555486c0380e1b86e555a5501c1c0707070707070707131313131313aa4608f822281aaa81cf806460606216aa97aa8464601818181a8d8daaad2a9118d8d80701c370dc83aaa0eaa038380e0e0e0e0e0e0e0e2626273e2626262626898989898989a268989898989a2626268989809998991809818989898189898997898989858989898d8989c27e1e2626262626261e21d9d81d9d807a87bf81bf8bbf81bf8b8767609a8589898989a8989816160585858587ac161743637447636360dc3705c1703a838383d038383c038380e0e0e0e0e0e0e0e2626262761e161e205858059d807a878581858b8581858587676285cfa8585aa05858161616161eb0585d058dd11d8d8d8370dc1705c0ea0e0e0e0e0e0e0e0e0e038380e0e0e0e0e0e0e0e2626273e26262626261e262626898989858985898989898985898989898980999899d8098b8989898189898985898989858989898d8989c2773f03 26 67108863 11 2047
def hc_93_3 : Nat → Nat := unpackHintV5 0xc2d1b8e14404b09a011844012c1601860a002304801180b032b79518d5b8c268744d122442c8c5499c1389e608502f03301f7b2ccdb85ca75a13436b9d2d954b506a2d4f0cd5f816513b38282c0e13d807c99a0a44cb0042594188cfcb9c27980a000279 0x1f01f0001f031f1f1f1f1f1755001f1f0b0b1f1f1f1f1f1f1f1f1f1f0b555500000b0b0b030b030b171f0b1f1f1f1f1f0b55000b0b0b0b0707071f1b1f1f1f1f1f954014cdcdc2c6c2c4c2c2c2e0b0b0b0b1f271f1f1f1f1f075500270727070b0b2f0b0b0707070b079f2707270786e7e7e1b9fc2c2d86e7c9d9f9f85c0c6e7c1cbe22aa8064606062a8161601818181aaaa81191919180181818181818181a8383aaaa8464601818181858585858dc372a80e4e0183818385858383a0e160f3e5e5eaaa4e0e4e0f548c11f044503555039f00c8c0c0c50b0b555550b555500b230b0b0030303030303030342d550b5502c2c0303030307070746d55954232300c0c0c0c2c6c2c4c2c2c2e0b0b0b0b49d55075501c9c030703070b0b2f0b0b0707070b079f27072707c0c0c0c002c2c2c2c000c0c0c0d0c3c8d2350c3c00000c0c0000c0c1c1c0c1c0c0d0c8c8cdc000c0c0c0c2c2c2c2ddc6cde771b3789c1c9c1c000c1c0c1c2c1c072f2f07330303073327072707c0c0d031f030f0000c03032303030300003000b0b0b42d0b0f03030b0b030303030303030303030b0000030303030303030303030b170b0b0b0b030b03030303030b000303030307070743232337031b032b0303038000c0c0c0c2c6c2c4c2c2c2e0b0b0b0b27072707032707330303070700030703070b0b2f0b0b0707070b079f270727078601a878000181816160219191a1816062e2e0606060606a6a60380dc07319bb39b84e4e017813c013c8c8d3c002c2c2c2c002c0b0b0b0b4f0f231f231f4f0f00b5317630303531700733004f23233700533767370b0b0b0b631b372b671b372b27072707002709c1c9c1c2c1c072f2f00027072707a6062f703530ba22a846462a8161605858585aaaa8119191918298b8181a98ba8383aaaaa9511955555554aa039384e0e4e0e160e839797aaad5445508c8c555500b230b0b00b0b0b030b030b175502c2c0b0b0b0b0707075a7d54a88caaa84eaaa95047d23045d503542d44c4c4d0b42d550b542d595501c9c270727070b0b2f0b0b0707070b079faa44d0749d622a846462a8161605858585aaaa81191919181f8bb981b9819f8ba8383aaaaa9118d8d8370dc1705c1e1f098585c26aa039384e0e4e0e16160e83859797a26a89c0e375523047c111035545d542323142c2d555542d555402c8c2c2c02c2c2c0c2c0c2c5d0b5542d540b0b02c2c2c2c1c1c1d43d5569f2231b1b06e1b82c6e130b0ba0b82e49d13541d54072709c1c9c1c2c2cbc2c2c1c1c1c2c1e7e071ba79191a780058585858005858585c78791a46c7878000478bc781c781c78b9595838395959595d50055550050138393838013839383858380e5e5e565656565657553c8c8d3c002c2c2d0b42c3c00002c2c2c0c2c0c2c5c2c2c2c2c002c2c2c2c1c1c1ea88e000ac2aa0b86e13aaaaa2b0f2b1f2b4acac0acac5cacacac0cacacac2cacacacacacac2cac2cacacacacac2cacacac2cacac02707270700270727070b0b2f0b0b0707070b079fa07a8acacacac1c1cacac9c9cacaf61e368d8f8d87800562791919f8d818d8b8d818d8b80058585a16858785858585858d858d85858585858d859b8000058585818581858b85858585858585858585858580058585858383838dc46363700015800dc3705858d8dc26161705d05c17138393838d9383998d8d8383801383938385859785858383838583cfc0e0e3703ee1b8060606060181816161685a161e0166e1616006060606060606060606162e1616161605858060606060e0e0f545101d3f55509d55541f334115c6e101d05c7f098989c1705d5417505d544e0e4e0e03938060e060e16165e16160e0e0e160f3f5509c0f13d5b385cff703039fc7c7c2c7c7c2c0c0e7e7ff98f8f8c73f3f0c00c0c0c0c030302c2c2c2c0b0b00c0c0c0d0c3dcd7350c3c1cd8dcd8c00c0e80e030303030707030703031b86e21b00c0e80e03a7c2e0b85c5e130b0b84c9c1c9c1c072700c1c0c1c2c2c1c1c0c1c2c1e7cbcbc1c4c0c0c1c4e071ba18018181a068187801bb8181801818181806065416161685a161e016ce16160060616160606060606060606060616060606060606060616161616058580616060606060616060606060e0e0e370dc43601818b8181d4074f858dc26161741705c4e0e4e0e03938064e0e2606060e0e060e060e16165e16160e0e0e160f3f038dd3c13d4d3c5302c2c2d0b42c3c02c2c2c02c2c2c0c2c0c2c5c2c2c2c2c0b0b02c2c2c2c1c1c1d3d3c14d4c2c6c2c4c2c2c2e0b0b0b0b2707270701c9c270727070b0b2f0b0b0707070b079f27072707 25 33554431 11 2047
def hc_93_4 : Nat → Nat := unpackHintV5 0x9fdd0166baa799494cae51402293cc10a38b2d086250120ae9b57d7ca7de4f22073b0b19bc92466928bf98fd29a5c72f05614211511ee65305a8448c869d0e3a9d3fb67b0e77aec359089cb92ba32920a548b8b1f1dbca4c5f8aed11d6c1825ec2e0446a68000223 0x43003030340d030f00367030300303030300c0c0707070b0b0b42d0b0f00b770b0b003030b0b030303030303030303030b03030303030303030b0b0b0b02c2c030b03030303030b03030303a86e1b886c031b84c0c0e80e0382c2c6c2c2ea0ba7c9c1c9c1c072700c0c5c0c0c1c1c1c0c1e7c2c9c1c4c2c2c1c1c2c1c2c1e071ba18018181a068187801818180181818180606038383a1a3a188e018581818181819781818181a1a18018d8189818181c060606068e8e4e0e4e0e0393806062e06060e0e0e060f3e4e0e4e0e4e0e4e0f11541703142e7d542f2f0b2302c0c0c5d5047d23045d503543d5508c8c170303172f0b0b2f5646d554070701c1c1c1c1c0c1e7c1c1c1c1d50741d41c1c1c1d555401ccc1c8c01c5c1c1cbc1cbc1c1c1c2c1c2c1c1d5541c1d41d3d541e0713071b0781c1c1e7cfe1b9f9f8fc5c0c6e7c1c3fc40350f05c0c0b0b550b9f070bc2c0b0303170b0b55070703b3b3b3b01717030303030f0f5070707070743d43c3b3b05c0c0c5cbc2c2cbcfc6e3f1b81d41c070701c1c1c1c1c0c1e7c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1fc40350f05c0c0b0b550b9f0bc2c0b0303170b0b0b00f0f0f3b00f17030303030f0f543d43c3b3b05c0c0c5cbc2c2cbc3c3c3e0f1b0f81d41c070701c1c1c1c1c0c1e7c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c3d541c1c01ccc1cec01c5c1c1cbc1c1c1c2c1c1c1c3c1c3c1c1c1c1c1c3c1c1c1c1c1c1e0713071b0781c1c1e22a82e062a846460b81818baa9455552aaa81191919180b8baaaaf97a985a985af97d42709d2a80e0e038383a0e0e0e0f54898383a26b11541703154232305c0c0c5d69f552a232aaa95047d23045d50354bd50b56554070701c1c1c1c1c0c1e7c1c1c1c1ea91341d07555550073307230071707072f0707070b0707aa84e81c6e95541c1d41d541c1c1fc40350f05c0c0f50f0dcdc1703031795628aaaa0f0f55070703737373701717aaa5f2f4f0b4f0b5f2f584e1390750701c1c070707070703079f81c1c1c1eaa13070784ebc40350f05c0c0f50f0dcdc17030317a55a7ca2aaaa0f822b8dc217a80ea2fa82e950750701c1c070707070703079f07070707aa84e0781e81c3d541c1c01ccc1cdc01c5c1c1cbc1c1c1c2c1c1ea13aaaaa0707a07aa070707dc3700c5c0c5c170302cbc2cbc2f0b02c0c0c5ea8a2aaa82e5f0f5f57d5f0f03737373701717aaa1b1b070707070707a84e13a0707070701c1c070707070381c1c1c1eaa13070784eb70dc0317031705c0c0b2f0b2f0bc2c0b030317aa28aaaa82e9f83e66822b8dc217a80ea1baa0707070701c1c070707070703079f07070707aa84e0781e81c3c1d0741c1c01ccc1cdc01c5c1c1cbc1c1c1c2c1c1ea13aaaaa0707a07aa070707ec3b00c5c0c5c170314d4c3b3b05c0c0c5cfcfc3b3b05c0c0c5cfd4cfc1c1c1c1c070701c1c1c1c1c0c1e7c1c1c1c1c1c1c1c1c1c3c1d0741c1c01ccc1cec01c5c1c1cbc1c1c1c2c1c1c1e0713071b0781c1c1fe00f81ea1e1e061e2e1e061e1e0016a1e16161e5e16161e1e00165e165e1e1eaa1e1e1e1e1e1e1e1e5e5e1e1e5e461e1e1e1e00005e2e5e065e065e2e0e0e0e1ea1e1e1e1f078d879580259ba19b97858597978d97c5e365e261ea0e1e1e0e0e1e4e0e66004e0e4e0e0e160f3e16160e0e1616164e0e4e0f4000000011c0d2c5d1c0d2c5d54007c7c7c7c7c7c1c1d54002cbc2cbd5c6cde571b37954012cdd1cdcbc2c2cbc2c2c7c7c7c7c7c7d54009c1c9c1c070b0727072707f80f8000f818f8f8f8f8f8baa800f858f8f8f8f8f97aa80059785978f8f978f8f8f8f8f8f8f8f8f8f9797aaaa8000178b97819781978b8383838f8d8f8f8f8f8fcaa00966e8e6e5e16165e5e365f178d97898f8f93938f8f8f8f8f8f8383aa8013839383838583cf8585838385858593839383c987918f918fb1878005e239191a5a381c98bc981a58b8005978597803998001780165e165eae46466eae366e5726366e5600ae259ba39b97858597938393838005858001384e0e4e0e03858393839383c45508c8c555502323232304b17470347034b17550bc2c0b2f0b2f5070755552a232aaaaaaa954072709c1c9c1d542c2d5070b07aa88aa11918aa17858165e165eaaaa05e5e5e4605e2e5e065e065e2e0e0e0eb4faa95119555555509aa08fa4608baa06a97aa16a97a5eaa97a898989b2aa039384e0e4e0e0e160f3e16160e0e1616175489a0e93af881ea1e1b9b81e1eaa1e1e06e6e6e6e0962e86068606962e16a1e17858165e165f40e0f552c51554b53541ea0e039384e0e4e0f54161750385858583d57881ea1e1b9b816a1e17858165e165e1e1eaa1e1e05e5e5e6e05e2e5e065e065e2e0e0e0f4ab4f94555555542707c115c6e10bd407517c5f505c17517c5f5517d098989aa1ea0e039384e0e4e0e0e160f3e16160e0e1616175509c0f13d4723234b00770f2348d770f00004b17470347034b170b2f0b2f000b2f0b2f2b2b07072b2b2b2baa002b2aa8002a89c1c9c1c009c1c9c1cacacacac2c2cacac070b0b0b07aa8e46469600165e165e00165e165e5e1e5e97a5e1e00005e2e5e065e065e2e0e0e0f5447000561555555517c37099587958f95a5656056562e565656065656565e565656165656565e565e56565656565e56565656560138393838013839383838583cf85858383858585d03d45656560e564e56571d2d1d2c4b4702cbc2cbc2f0b02cbc2cbcbc3cbd2f4bc3c0bcbcbc0bc5cbc0cbc0cbc5c1c1c1d5d5c5712d1d1d2cbc2c2cbcbc6cbe2f1b2f132707270701c9c27072707070b079f0b0b07070b0b0b27072707aa4608f822281aaa81cf80646060628585aaa8597aa8161601818181a36aacaa11918060606061616161683aaa0eaa038380e0e0e0e0e160f3e0e0e0e0e0e0e0e0ea0eb6aaaaa0e0eaaaa00e660e4600e060e0e0e060e0e0e160e0f0389838d83c0e0e0f115423231540b0b02c2c2c2d69f552a232aaa95047d23045d503542d50b56554070701c1c1c1c1c2c1e7c1c1c1c1ea91341d075555500733072300717070707030707070b07a84ea95541c1d41d6d541c1c1ea91823e08881aaa2eaa1191885aaa16aa0585816161616a1eaab4f9118d8d8370dc1705c83a26a83aa80e0e03838383838583cf83838383c0e0f283ada262626aaa0e0eaaaa00e660e4600e2e0e0e0e060e0e0e160f40e260e3740e0e0fb86e0181818180606058585858161601818181d5144074fd55541f334115c6e101d05d417550383838380e0e03838383838583cf83838383d542703c0f40e1e0e83a0e0e00e660e6e00e060e0e0e060e0e0e160f509d55550383d039fd5038383f61d806060681a061e0067606060060606060181950585858581616018185858181818181818597818181818dc3710d806062e0607501d3e1705c0e0e0e0e038380e0e0e260e0e0e0e0e0e0e0e0e160f3e0e0e0e0f0383c0e1e0e83a0e0e00e660e7600e060eb60e2626260e060e060e0e0e0e0e060e0e0e060e0e0e160f40e260e3740e0e0fd87627a9a787676058585858161605858585a7a78767629a9858585858383838380e0e03838383838583cf8383838383838383838783a0e838380399839d8038b83838381838383858383c0e260e360f038383fc01540154002c2c2c2d400000014c5ddc0ddc0d4c5c7c7c1c1c7c7c7c7d54014cdcdc2c2c2c2ddc6cde771b37954009c1c9c1c2c2c1c070b2f2f1f1f1f1f1f1f27072707 26 67108863 11 2047
def hc_93_5 : Nat → Nat := unpackHintV5 0xbf094d5b3e88ea2e6e347d9339a093ccce004a66801132b0129898184c3c0226160112f20328ecd18c154c25e424d0d0a42e67f80b33bc081843336ad329d4e2d0da164b64eaa4105763be1b86058752ce038d0381b701f0c702906300102e70620002e7 0xec3b00c0c0c0c030310d1d0c3b3b00c0c0c0d0d0c3b3b00c0c0c0d1d1c1c1c1c1c070701c0c1e7c1c1c1c1c1c1c1c1c1c1c1c1c1c3c1d0741c1c01ccc1cec01c0c1c1cbc1c1c1c2c1c1c1e0713071b0781c1c1fe00aa00a00000003e3e0e0e3e3e3e3eaa0006060606ee168e5eee168e5eaa0006060606ee366f3b8d9bc8e6e6eaa0006060e03818b8b8f8f8f8f8f8f9383938393839383fc07c0007c7c0c0c7c7c7c7c7c7c7c7c7c7c0d555400007c0c7c7c7c7c7c0d54001c1c1c7c2c7c7c7c7c7cbd54000c2c0c0c0c0c0cbc0c0c0c0c7c6c7c7c7c7c7e5500031b031303030380c0c0c0d1cdcdc7c9c7c7c7c7c7c1d54000c0c5c0c0c1c1c1c0c1e7c9c1c9c1c9c1c9c1e180185a87800060864646860180e0165e5e01616161616168e168e3705cc66ece6e1393802e0430003030303000310c3c8c7c8c7d0c3c00c01ccc010c8c8d0c000c0c0c0d8c2d1cbc2d1cbd0c8c8cdc000c0c0c0d8c6cdcad9c6cdcad1cdd9cdc9c1c9c1c009c030701c5c5c0009c1c9c1c9c1c9c1e1b9f9f86e7f60b031b9f2767e7e1b2f0b9f071788aa01818aaaa0464646460a0e0eaaaaa059185858060606061616060606060606aa1191806060606370dc16161616aa0393806060e0e838183cf8b8baaa8583858393839383d523047c11140c0d555540d555400c8c0c0c1035540d54030301c1c1d42d5542e7c0b230b0b00c2c0c0c0c0c0c2c0c0c0c0d1b5565508c8c031b031303030380c0c0c0c2c2c2c2d275541d54072700c0c5c0c0c1c1c1c0c1e7c2c1c2c1c9c1c9c1f03030300430f2348d430f000003030707030703030b0b0b0b00030303030030300432323370003030303771b379dc6cde0b0b0b0b2707270700030701c5c5c1ccc2c2c1ccc2c1c2c1c9c1c9c1ec2c2d0b1f0b0f0002c03030340d030f03030303030b030b03030303030b030000030303030303030303030303000707070b0b230b0b0b0000b0003030b0b0303030303030b2f03030303432323370b1b0b2b0b0b0b8000c6c0c4c0c0c0e030303030b0b0b0b270727070b2707330b0b070700030317030307070703079f0b070b0727072707bd1c2ef0b4703a22a806062aaa811919191828383aaaa846460181818185a39785a397aaa9511955555554aa03938060e838b8baaa93839383d544555500323030305500c0c0707075508c8c030b03030303032f030303035a7d54a88ca84eaaaaa95047d23040d44c4c4d0340d5503540d52f542d595501c9c030317030307070703079f27072707aa44d0749d622a806062aaa811919191828383aaaa8464601818181b985a397b985a397aaa9118d8d80701c1e1f098181c26370dcaa0393806060e83818b8ba26a8993839383c0e375523047c11140c0d555540d555400c8c0c0c1035540d54030301c1c1d0b554bd54232300c2c0c0c0c0c0cbc0c0c0c0d43d5569f2231b1b00c6e130303a0380e1b86e49d13541d54072700c0c5c0c0c1c1c1c0c1e7c9c1c9c1e071bb03030300870f2348d870f00002b2b07072b2b2b2b432323430003030303870b872f870b872faa00aa00a0aa2707270700030701c5c5cacacacacacac9c1c9c1eab030340d030f000003030303000707074323234300030b03030303032f03030303aa238002b080e1b84eaaaaaa8ac3cac7cad2b2b02b2b032b2b2b2b2b2b032b032b2b2b2b2b032b2b2b032b2b2b2f2b2b2b0b2b2b009c1c9c1c000c0c5c0c0c1c1c1c0c1e7c9c1c9c1e81ea2b2b2b2b07072b2b27272b2bd878da363e361e0015806060681a061e0606060606360636060606060636066e0000060606060606060606060606000e0e0e86464686361636363616365e00061606060606065e0606060637118d8dc000560006063637098181c0740701c370dc4e0e4e0e364e0e6636360e0e0006062e06060e0e0e060f3e4e0e4e0f03838dc0fb86e018181a0681878019b818180181818180606038383858585858161601818585818181818181859781818181d5145427555505d3f5507ccd04571b84072bc26262701c075501d407505d51383938380e4e01818b81818383838183cf85838583d542703c4f56ee173f9c0c0e7f1f1f0b1f1f0b03039f9ffe63e3e31cfcfc300303030300c0c0b0b0b0b02c2c03030303430f735cd430f073637363003030707030703030303a0380c0c6e1b886c0380e0b0ba0382e9f1b1b84c0c0e132707270701c9c03030707030703079f0b070b07171707130b0b071381c6e 25 33554431 11 2047
def hc_93_6 : Nat → Nat := unpackHintV5 0xbf9294adf4be0b3568faad8bfaa6b495e7babe59a708f649cbff8e1e8aa195be47e8af99d81c426edae599c2be85f3afa1699a6a52e4f053b0a114790e650a22843f3a69ce8029d36287b0c142ec2c0289c931b9e1fa6a4065a31f1442a4c39a2ed085cc1800042e 0x62e062e00ce1e4691ace1e00014666666666666a64646ae002e06062ea616ae5ea616ae5e370dc00406060719999995818199958dc3703838383801980e0e0e0e0e0e0000e0e0e0f0383d8b818b800b878ba2e8b87800054a64646ae002e06062e2e162e5e2e162e2e370dc0101d3e06074060606370dc0e0e0e0e460e0019803838383838383838383838b8393838983838383d0383d1987998f99a6666066662e666666066666662e662e66666666662e6666666666665e666666166666671999998d999581161e4691b161e00000606060601466666666666686464686011617165f1617165e06060606370dc002e2e6656666666560710dc37038383838000038380383838383838383c0e0f6060681a061e000006060606015219191a1800185818181818197818181818dc370001818b8181d4074f8dc370383838391838006600e060e4e0e260e0e0e0e0e0e0e0e0e0e0e0e0e0f40e0f4661e663e6699998199981999999999999819981999999999981999999819999999799999985999999c671999998d998d9995811c8c8cfc002cbc2cbc002cbc2cbd9c3c8d2359c3c0000fc5d1c0d1c0cfc5e8cccccccccccc6e1b8006e1b882c2c2e3333332b0b0b332b07070707003301c1c1c1c1c1c1c1c1c1c0020707a391919f800597859780059785978d878da368d8780000d8b8d818d818d8bd4370dc00370dd05d3e161741616160e0e0e0e460e001980383838383838383838383838383838d83938389d0383d1987998f99a6666066662e666666066666665e666666166666663666366666666666366666666666671999998d9995813c8c8cfc024c3c8d2364c3c00024c5e4c0e4c0e4c5c2c2c2c2c002c2c2c2e8cccccccccccc6e1b8006e1b86c6cccacccccccac2e207070707000707070700070700707070781c1e9e46467e0016161685a161e0000161616061606162e16161616001616161750dc37000dc3705858d8585d4174f8383838391838006600e0e0e0e0e160e4e0e260e0e0e0e0e0e0e0e0e0f40e0f4661e663e669999819998b999999819999998599999999999985998599999999998599999985999999c671999998d998d9995811918011918011919b801b9b9b9b8383838391838006600e0e0e0e0e0e0e0e0e6e0e0e0e0e661e663e669999819998b999999819999999799999985999999c666666366656061e061e1ea8f8787818181818181939d8181939381818181800000066281cfa8181aa0606060606060606001ea1e0606065e061606064e164e5e4e164e5e00060606061ea1e060607018d81c4e364e564e364f0001818181a39ba79b87aa838181838183838181939383838001980018381839383938393938393839bd87858787aa3e1e1e1616161616164e7616164e4e161616160000001981ea1e1606162e160616164e064e2e4e064e2e00a173ea1616a8585858585858585800585858587a87858585c163617138d9395938d93c00a66e866e161616161eaa0e16160e160e0e16164e4e0e0e00066004e0e4e0e160e160e4e4e0e4e0e6f38793a4e3e4e1e0019806060681a061e06060606064e064e06060606064e06760000060606060606060606060606000606061616161616161616161616160006061606060606060616968646466e4e364e564e364f00018d81c06060701818181858585859383919393838001980018193938383818183818383818381838583858393938393839bd41e1ea8f8787878787878787939d878793938787878780000006607a878781878b878187879381938b9381938b8007a8787858797878587879385939793859397801fa1a19fad3eb4a8d8dc563637400370dc370dc1eaa0e1e1e0e1e0e0e1e1e4e4e0e2600066004e0e4e0e4e0e4e0f40e37538793a4e3e4e1e0019806060681a061e06060606064e064e06060606064e06760000060606060606060606060606015219191a19385939793859397800185818181818197818181818dc370d8dc56363740006062e0607501d3e370dc4e0e464e4e0e000660006064e4e0e2606060e060e0e060e060e4e0e4e0f40e37538793a4e3e4e1e001989e46467e4e064e2e4e064e2e0016161685a161e16161616164e164e16161616164e16760000161616061606162e161616161616161616161616001616161750dc370d8dc563637400370dc1616361617505d3e4e0e464e4e0e00066004e0e4e0e16164e4e0e2616160e160e0e160e160f40e37538793a4e3e4e1e001984646964e064e2e4e064e2e004646b64e164e5e4e164e5e0096b69646466e4e364e564e364f00259b9bad9b9b9383919393838001980138393839383938393938393839bfc01f00d43c0c0c3c5c0c0c3c3c003c3d543c3c3c3c3c3c3c3c5c5c3c3c5c8c3c3c3c3c00001c1c1c3d43c3c2c3cbc3c2c3c3c005c0c0c5c5c2c5cbc5c2c5c5c3d43c3c3c3e0f1b0f2b001703031717171785c6c5c4cfcdcfcdc3d41c3c3c1c1c3c9c1ccc001c0c1e7c0c0c1c1c0c0c0c9c1c9c1c9c1c9c1e800000000f8f8f8f8f8f8383aa803d85bd97bd85bd97aa800b81818bbd8d9bcf6366f2a800b81818b9f9b9f9b81818f8f8f8f8f8faa8000e060e4e0e4e0e4e0e4e0ff01f0001f031f1f1f1f1f1755001f1f171f1f1f1f1f1f1f1f1f1f1717555500000707071f0b1f1f1f1f1f2f550017030317170b172f170b17171f1b1f1f1f1f1f954005c0c0c5c5c5c5e171b17133f373f371f1f27271f1f1f1f1f1f070755000703079f0303070703030327072707270727078b0f231f231f630f0005c031703170073300017014c8c8d6d4c2e2cbe2c2d6cbc005c0c0c5cfc8c8cdcfc6cdcae2c6cdcac00fc170303173f373f3727072707000303000270070307270727072707270788aaaa0464646460aa0b818a0e0eaaaa11918a616b65ea616b65e2e06062eaa5446555555552a80e4e2a8181aa0e060e4e0e4e0f55115417031555405c5c5c8c01c1c1d54232305c0c0c5c5c2c5cbc5c2c5c5d69f552a232aaaaa13aa5411f48c117540d51745d551751313134bd50b56554072701c0c1e7c0c0c1c1c0c0c0c9c1c9c1ea91341d275f103c3d543c3c0dcdcdcdc00d43c1703281c1ea83d43c373713c2d6cbd3c2d6cbc5c0c0c5e58a296a6aaa83d41c07272a80c0ea070303030727072707aaf100d43c170303c3d543c3c05c5c5cdc01c1c1c3d43c373705c0c0c5c5c2c5cbc5c2c5c5e9569f28aaaaa84eaa0f822b8dc21785ea0380ea1785eaa17a1313138bea0ba543d41c072701c0c1e7c0c0c1c1c0c0c0c9c1c9c1eaa1381e27aee1e4691aee1e0000062e062e0056560e0e56565656a64646b600a616b65ea616b65e2e06062f540056500055551383938380159595958181959580e0606060e4e0e4e0f558b818b800b878ba2e8b878000038383a99191ad800b81818b8b858b978b858b8bd511c001585555542f0dc2754561e563e569595815958b959595819595958b958b95959595958b95959595959597959595859595804e0e4e0e000e060f3e06060e0e0606064e0e4e0f40f51595958395939595e2e062e0b8182e1e2e8ba2e1e02e2e2e00e0e0ea6b6a6b62da982e06062e2e162e5e2e162e2e7e7e1f82e06062e2e2e2f0b8d8b899fa99fad9383938380e4e038183cf818183838181819383938393839383d523047c11140c0d5540c5d540303142d5542e7c0b230b0b00c0c0c0d1b5565508c8c030303030b0b0b0b41d55075501c1c0703079f0707070707070707070707075074b55555070755550073307230070307070b0707070b07070781c4c1c6c1e07070788aa01818aa1191806060606b4faa951195554a823e918206a81aa5ea85ab2aa038380e060f3e0e0e0e0e0e0e0e0f5489a0e83aaaaa80399839180381838397838383858383d42754aaa0e0ea0e96aa0e0e0f548c11f04440d55035500c0c42d552f5508c8c0303030350f555a7c88c6c6c0380e1b86e41d13541d54070701c0c1e7c1c1c1c1c1c1c1c1e0707941d2d131313555070755550073307230070307072f0707070b0707a0713071ba070707dc3700c0c0c0c030302c2c2c2c0b0b00c0c0c0ea8a2aa0ba7eaa0f99a08ae37080ea03a82ea81c1c1c1c070701c0c1e7c1c1c1c1c1c1c1c1eaa1381e07a070f0741d07070073307370070307070b0707070b0707a84eaaaa81c1e81d2ea81c1c1fb0ec0303030300c0c0b0b0b42d0b0f00b3b0b0b0030303030303030303030b170b0b0b0b02c2c03030303a86e1b886c0380e0b0b1b0b0ba82e9f0707070701c1c0703079f0707070707070713070707070707070781c1e070f0741d070700733073b0070307070b074b07131313070b070b07070707070b0707070b0707a0713071ba070707 26 67108863 11 2047
def hc_93_7 : Nat → Nat := unpackHintV5 0xac241769a12d09e7d01267025e9214f5a37821a8860b020e925e7bf8f59df121a7244b01b6925069209098543e85ccc9095433e0508890922d3ea442c910f1a3e2343d058b0441627149f87b2426196cab864e01a192802063a02014049c82ee42607808700003c0 0x438fc3d05c1cbc1c6e7c1c5fc40350f05c0c0b50f0bc2c0b0b030303030b43070f0f550f0f03b3b3b3b00b0b07070707070703030707070707070f50f0ecec170303172f0b0b2f3f1b8fc6e070755079f0701c1c07070707070707070707507070741c1c1c1fc40350f05c0c0b50f0bc2c0b0b030303030b430f0f550f0f01717173b00b0b0b0303030f50f0ecec170303172f0b0b2f17171785c6c5e070755079f01c1c0707070707070707070707070707070707070707070f0700733073b00717070707030707072f0707070b07070717071707070707071707070707070781c4c1c6c1e57c40350f05c0c0f0f550f0f03b3b3b3b0a070707070783d43c3b3b05c0c0c5d3c2d5cbd3c2d5cbc3d621b01e03030381c1e80c0e86e1b81d41c070701c1c1c1c1c1d41c1c1d0707070781c1ef100d43c170303c3d543c3c05c5c5cec2a0f50f0ecec17030317170b172f170b17170f5886c80e9f0303a0303031b86e070755079f01c1c0707070707070707070707130707070781c1e070f0700733073b0071707170707070307030707071707170707070707170707131313072f0707070b0707a0713071ba57c40350f05c0c0f50f0dcdc170303179628aa80e9faa83c3d5680dcdcdcdc05c5c1c1c1c1c1c1d7cbd3c2d3c2d7cbea1384e81d5601c1c0707070707070707aa84d6139f100d43c170303d43c373705c0c0c5e58a2aa03a7eaa0f55a08ae37085e8bea0baa81c1d541e7c070701c1c1c1c1c1c1c1eaa1381e07a070f0700733073700717070707030707072f0707070b0707a84eaaaa81c1e81ea95f103d43c3b3b02d43c2f0b02cbc2cbc3c3d543c3c0ecececec0fc5d0c0d0c0cfc5e81c1c1c1c1e0f5886c1b86e0782c2c2e0707a0b0ba0750701c1c07070707070707070707507070760707bc40f50f0ecec0b50f0bc2c0b2f0b2f0f0f550f0f01b1b1b3b01b171b031b031b17a83d621b06e1ba0ba7c2c2e82c2c2c1c1d541e7c070701c1c1c1c1c1c1c1c1c1c1c1c1c1c1c4e070781c3c1c01ccc1cec01c5c1c1c1c0c1c1c1cbc1cbc1c1c1c2c1c2c1c1c1c6c1c6c1c1c1c1c1c6c1c1c4c4c4e81c4c1c6e95f103d43c373702d43c2f0b02cbc2cbe58a2aaaa0ba7e0f0f55a03737373705f17430343035f171b1b070707070707a84e13a07558070701c1c1c1c1c1c1c1eaa13584e7c40f50f0dcdc0b50f0bc2c0b2f0b2f9628aaaa82e9f83d56822b8dc217a80ea1baa070755079f01c1c0707070707070707aa84e0781e81c3c1c01ccc1cdc01c5c1c1c1c0c1c1c1cbc1c1c1c2c1c1ea13aaaaa0707a07aa57c40f50f0ecec0f50f0ecec4f43430f50f0ecec43434f4f070755079f01c1c070707070707070707070707070f0700733073b00717070707030707072f0707070b07070781c4c1c6c1e57c3ccc7ccc7ccccc0000005033333333353333000f50f6f0b6f2f6f0b6f2f00030303030f50f6f1b379bc6cde000303030347374f3707507070700000070707070707070707070707c3c0c00000140e7d40c0d5000f50f0303032f030b030300030303030f50f03030380c6c0e000303030347374f37075507070707070707070307270707000cc01c1c1c1c1c1c1c1c1cdc1c1c1c1ccc3ccc7ccd33333303330333333333330333333333330333303333333033333332f3333330b3333338cccccc6cccac0d4000303331f331f3333000053333333333330f50f00170303176f0b6f2f6f0b6f2f0f50f00170303176f1b379bc6cde3f373f3707507003301c1c1c1c1c1c0001c1c1c1c1c1c1c1f0355039f000303030000543d43c005c0c0c5c3c2c3cbc3c2c3c3c3d43c005c0c0c5c3c3c3e0f1b0f8fcdcfcdc1d541c0033007070707070707070707070f0727070707070707073707070707330f331f334cccc0cccc5ccccccc0ccccccc3ccc3ccccccccccc3cccccccccccccbccccccc2cccccce3333331b332b03c3ccc7ccc7ccccc0000003d43dbc0dbc5dbc0dbc5c0050b3333333353333000b0b0b0b0f50f6f1b379bc6cde00533743370b0b0b0b07507070700000070707070707070707070707b0f0b0000000f50f0b030b170b030b0b0050b9f50b0b54002c2c2c2c3d43c2c2c2e0b1b0b8014cdd0cdc2c2c2c2c1d541c1c1c1c1c1c1c1c2c1c9c1c1c003300707070707070707073707070707330f331f334cccccc2ccc2ccccccccccc2ccccccccccc0cccc5ccccccc0ccccccc2ccccccc2cccccce3333331b332b03d43c002d4000b2f0b2f0b0b331f331f333300006f176f036f036f1753333333333330f50f00573743372f0b0b2f6f1b379bc6cde07507003301c1c1c1c1c1c1c1c1c1c0001c1c1c1fd43c002c2d542e7c002cbc2cbc2c2c2c00003c5c3c0c3c0c3c3d50f50f00573743372f0b0b2f0f0f0f83c6c3e075507000cc01c1c1c1c1c1c1c1c1c1c1c1c1c1c1c3c1c9c1c1c1cdc1c1c1c1ccc3ccc7ccd33330333317333333033333332f3333330b3333330f330f33333333330f3333333333338cccccc6cccac0c5c0c5c002c3c2d0b42c2c00002c5c2c2c2c2c2c000c0c2e7c0c0c2c2c0c0c0cfc8c8cdc005c0c0c5c2c2c2e0b1b0b82c2c2c2c1c1c1c1c8c1c0033007070707070707070707070707070707073707070707330f331f334cccc0cccc5ccccccc0ccccccc2ccc2ccccccccccc2ccd1ccccccccccc2ccccccc2cccccce3333331b332b03030303000b2f0b2f0003030b9f03030303030f0340d030300000303030317034323233700030303032f0b0b2f03030380c6c0e070707072307000cc01c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cdc1c1c1c1ccc3ccc7ccd33330333303333333033333332f3333330b333333033303333333333303335333333333338cccccc6cccac08b0f2348d8b0f0000030303030003033333333333330b0b0b0b000b0b333333333333030300d0c8c8cdc022c6cde8b1b3780c0c0c0c2c2c2c2c1c1c1c1c00001c1c01c1c1c1c1c1c1c1c1cdc1c1c1c1f030340d030f000003030303000303030b0b0b0b0003030b0303030303030b4323233700031b0380c0c0e030303030b0b0b0b070707072307000cc01c0c1c9c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1cdc1c1c1c1ccc3ccc7ccd33330333303333333333333033303333333333303333333033333330b3333330b3333338cccccc6cccac0c0c0c0c005c5c5c5c000c0c5e7d0c8c8cdc000c0c0c0c5c5c5c5c1c1c1c1c8c1c00330070307070707070707071707073707070707330f331f334cccc0cccc0ccccccc0ccccccc5ccccccc5cccccce3333331b332b0230f4279ff2310717c5c0c5c002cbc2cbc002c0c0c0f2348d0f00000b0b33333333333303033333333333333f23233700170303172f0b0b2f3f1b378fc6cde070707072307003301c1c1c1c1c1c1c1c1c1c0001c1c1c1f170317000b2f0b2f000b0b030303030b170f1745d170f00000b0b0b0303033f23233700170303172f0b0b2f17171785c6c5e070707072307000cc01c1c1c1c1c1c1c1c1c1c1c1c1c1c1c5c1c9c1c1c1cdc1c1c1c1ccc3ccc7ccd33330333317333333033333332f3333330b3333331733173333333333173333333333338cccccc6cccac0a331f331f33330000000f50f6f036f176f036f17000f50f6f0b6f2f6f0b6f2f003f43433f163333332b5332b001b86e1b86e07507070700000070707070707070781c1ea80000003d43c3c0c3c5c3c0c3c3c003d43c3c2c3cbc3c2c3c3c00fd0d0cfd69f5a54006e1b86e1b81d541c1c1c1c1c1c1c1c3c1c9c1c4c003300707070707070707a0707a330f331f334cccccc3ccc3ccccccccccc3ccccccccccc0cccc5ccccccc0cccccccbccccccc2cccccce338cccccc6ccc6cccac0 26 67108863 11 2047
def hc_93_8 : Nat → Nat := unpackHintV5 0xba0defae92dfa7a5bb9e924596a5fb8b2adf82463981ec16815825799def6e22df6735bb5e2245582d7d57e41257c40857801156f82256d80856c006563c214d7a31415709382a4b2fbe1b248acd1b5e4b12f21b07becd00e9b5006421000019 0x222aaa81191919182a8060652aaaa8464605a39785a39781818181aa90d82e2eaaa0730dc372aa80e0e0e4603838383838383838383838383838383c0e0f44555500323030305500c0ca954232300c2c0c0c0c0c0cbc0c0c0c0d5486c0303170303a80e9f1b86e5079f5501c1c1c8c0707071307070707070707070707070781c1e5411f48c103513131340d035540d50354bd50b5644d1b541d88aa0b818aa119182e06062eaa515354aaaa04646464602e2eaaabe5ea616a616be5f489a26aaa038380e0e0e0e0e0e0e0f55098383c27511541703154232305c0c0c5d54a2aa03a7ea9555422b88c217a2fa82eaa5079f5501c1c1c8c0707070707070707aa84e81c1e81c9e95047d23045d50354bd50b5644d95995595541d88aa11918aa17858165e165eaaaa04646464607e2e8e068e067e2f4aaaaa4360dc37305caa1616aaa0383839180e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0f0383d115423231542f0b02cbc2cbd555406c6c6c8c06c5c6c0c6c0c6c5ea5521b06e1ba0ba7c2c2e82c2c2d41e7d540707072301c1c1c1c1c1c1c1c1c1c1c1c1c1c1c4e070795047d23045d50354bd50b546d1b5546d44c4c4d91346d507622a846462a8161605858585aa94554174fd52aaa845711842f501d41754a0f3eaa0383839180e0e0e0e0e0e0e0f5509c0f03d2a08fa4608baa06a85aa16ac89b2b32ab2aeaa83bf818bdc0cfc2c1e22a846462aaa81191919181f8b81819f8baa8161605858585d2aaaa90d8370dc3636aaa1732aa80e0e0e4603838383838383838383838383838383c0e0f445508c8c555500b230b0b00b0b0b030b030b175502c2c0b0b0b0ba95486c1b86e0b0b1b0b0ba82e9f5079f5501c1c1c8c0707070707070713070707070707070781c1e5411f48c117540d50b513131342d0b5542d50b5644d1b541d88aa11918aa17858165e165eaa515552aaaa0464646460be2e8e068e06be2e3636aab489a26aaa038380e0e0e0e0e0e0e0f55098383c275115423231542f0b02cbc2cbd54a2aaaa0ba7d555422b88c217a80ea1baa5079f5501c1c1c8c0707070707070707aa84e81c1e81c9e95047d23045d50354bd50b5644d95995595541d88aa11918aa11918aa11918a0f3eaa0383839180e0e0e0e0e0e0e0e0e0e0e0ea823e91822ea81aa5ea85ab2268daa0ec7e373f2e1b8fc6c9c1e7ff970d8387c45500c0c5555023232323050303555502c2c0303030340c0c2d2c2c2d55554232300c0c0c0c6e1b82c2c2c2d5540723272700c1c0c1c3c3c1c1c0c0c1c1c2c1c2c1c9c1c9c1ea91823e088a0606aaaaa06aaaa006460606081aaa06aa0181806060685aaa16aa0585806061606060606060616968da26acaa11918063607018181c0606060616161616a1eaaa0f3e039193938064e0e0e06060e0e060e060e160e160e4e0e4e0f548c11f04440d55035500c0c42d552f5508c8c03030303644d5954a203a7eaaa963f44c4c4d5569555422b88c203a2fa82eaa50f555079f01c8c9c9c0307030727072707aa84e0789ea22a806062aaa81191919182d2aaa8464601818181b985a397b985a397aa90d806073018b8ba26a898dc372aa80e464e4e01838183878783898181838993839383c0e375523047c11140c0d555540d555400c8c0c0c1035540d5403032a42d552f5508c8c030b03030303032f0303030346d13565521b00c0c5c0c0ea03a7c6e1b943d5541e7c0723272700c9c1c4c0c0c1c1c0c1c0c1c9c1c9c1e071baa91823e08881aaa2eaa1191885aaa16aa0585816161616c89ab2a94554174fd52cae898989aaad2aaa845711842f501d41754a1eaaa0f3e0391939384e0e4e0e160e160f5509c0f13d445508c8c5502c2c0b0b0b0b555502323232303f17730373033f175a555521b06e1b82c2e60b1b1b44d51355501c8c9c9c270727070b070b070f0f07130b0b071381c6eaa4608f822206aa8baa8464628585aaaaa85aaaa8059185858058585818581858ba16aa85aa8161605858585d48da26acaa4360dc3705858d8585d4174fa87aaa83cf80e464e4e13839383859383898585838385838583c0e375523047c111035545d54232310b554bd54232312d6d2d1b44d5954232312d2d6d6d43d5541e7c0723272709c1c9c1c9c1c9c1c9c1c9c1e19fc373f0e3f9f 24 16777215 10 1023
def hc_93_9 : Nat → Nat := unpackHintV5 0xc4022bbae647ba4428b93c42b1160aa62eba9f9da496a23f8ee1f080b78b71e3b5684e655c0b114fc7114f9c0a0000004f740a4f0c1a0000004ef0074ec80a4e581c4636093a3301327ded29c22f1d3f211551fb09d6df00f239009816000026 0x4f04f3f3f0fc0b0b0b42d0b0f00b0b0b00b0b0b030b030b170b0b0b0b02c2c0b0b0b0ba86e1b886c1b86e0b0b1b0b0ba82e9f4f4f03f3f0b270b130b0b0b070b0b0b0b86c6e88a073eaa0b8b81918a823e91821eaa85e160581818baa5e85aaa94552b32d54174faaaa845711842f0bd40701d2aad2c86ab0dd52a846460b81818baa0e93a97858597d542703c4f53f3e960e4f3f3e0e964e5e1707f880606aa073f02e060181aad01b9b9b9b82d5485a8785e160581818b85858d8d85858787cb14555555554174fc1ea1e1b9b82e06062e964e0e964e0e5e16165f55e20181aa81cf82e0601818180787879b82a16a1e178581606062e16161e5e16161e1f2c515555555505d3f07aad04571b842f501d41f07d541f55437541ea1e1b9b82e06062e1e1e1e0e1e4e1e0e5e16165f5509c0f13d6e1b88e8e1b9b8165e165e17858165e165f5451555505d3f07ccd04571b842f501d43754b6b61b9b8b68e8e5e16165f5509c0f13d7330003c03c010c0d2c5d0c0d2c5c3d43c013c2d6cbd3c2d6cbc3d43c013d0d0d2d9c6cdcad8c6cdcac3d43c012cdd0cdd6cdd3cdc011f01541c009c270727072707270727072707ac7c1c1cac7cacac000001ac0dac5dac0dac5c3d43c01ac2dacbdac2dacbc3d43c013d0d0d2e80025802aaa8acacacad4acac507002707270727072707aae0e0e0000001ea1e1e061e2e1e061e1e001ea1e1e161e5e1e161e1e009e8686972ad55507c37098005615554561e563e569595958795879595959595879595959595815958b959595819595959795959585959580a0f3ea0e0ea801383938393839383d03d4565656560e0e56564e4e5657c1c1c3c3d51f0f0f0f0f0f0f0f0f1b370f0f1b1b0f0f0f0f0000000ac0f50f0f030f170f030f0f1b031b171b031b17000f50f0f0b0f2f0f0b0f0f1b0b1b1b1b0b1b2f003f43433f0f5583c3e0fa0f0f1b1b84c000ac006e1b86e1b941e7d41c1d51b2707331b1b070700270727072707270781c1c6e07e0e0e1e20787807807a878781878b878187878968607a8787858797878587878b69e27a1a1a587a87878787c1e361e26096868696b69e9eb6a0f3ea0e0ea80e4e138393839383938393839383c45505c0c555500b0b0b2300b170b5502c2c03030b9f03030b0b0303035508c8c170303170b0b0b82c6c2e0b0b0b0b5079f5501c1c1c8c07070707070707070707070707070707070707075411f48c117540d50b42d550b51d550b542d591346d507622a806062a85e16018185cf81818181aaaa8018181918018181818b81aa846460181818197858597818181c063607283cfaa80e0e0e460383838383838383838383838383838383838383aa08fa46081aa06a97aa16a81a06aa81aa6aac89a36a83b0dc370d8183e799e06c1c9e22aaa81191919182a806060181aaaaa816160585aaa8181a06aa11918370dc0606060616161616aaa0383839180e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0f11555400c8c0c0c154030300c0c0d540b0b00c0c2c0c0c0c0c0c0c2d54232300c6c0e03030380c0c0c0c2c2c2c2d41e7d540707072301c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1d5047d23040d5540d035540d503542d50b5644d1b541d88aa01818aa0b8b806062f3eaa11918060606062e2e2e2ea0f3eaa0383839180e0e0e0e0e0e0e0e2e0e0e0e0e0ea823e918206a81aa2ea8bab2268daa0ec45505c0c550bc2c0b03035555408c8c8c8c02c2d5540c0d55554232305c0c0c5cbc2c2cbcfc6e6e3f1b9b9075501c1c1c8c070707070707070707070707070707070707070788aa0b818aa1785816160606060616aaaa02e2e2e460161616060606aa119182e06062e5e16165e2e2e2f0b8d8bca0f3eaa0383839180e0e0e0e0e0e0e0e0e0e0e0e0e0e0e2e0e4e0e0e0e0e0e0ea823e91822ea81aa5ea85aa2e8baaa2eaab2268daa0ec45505c0c55550232323230a5555508c8c17030317530b572f530b572f5521b180e55030351b86e5501c1c1c8c0707070707070707070707070707070781c1e88aa0b818aaaa02e2e2e46152a846460b81818b8b858b978b858b8baa90d901d3e06074060606370dca0f3eaa0383839180e0e0e0e0e0e0e0e0e0e0e260e0e0e0f0383ca823e91822ea81aa2e8baaa2ea26262697aa16ac89a36a83b11540303154232300c0c0c0d54a203a7eaaa9555422b88c203a2fa82eaa5079f5501c1c1c8c0707070707070707aa84e0781e95047d23040d50354bd50b5644d95995593f5541dbd1c2ef0b470307 24 16777215 10 1023
def hc_93_10 : Nat → Nat := unpackHintV5 0xe0b1fbd596c7ccfe26bd97dab4ea2babce47ab2c28aa2442a1fe0a9716ba9085a482bb737b05ed6dab5764724e5b5647523a474ba9a443adff36db35368c13366c08360c1835343635140834f408342c322c41fb2126c7188e26092fd800024b 0x445500c0c555502323232305a5555502c8c2c2c030303030b0b0303030303035521b00c0e980e9f17175550b82e5508c8c03030303270727070b0b0b0b86c6eaa4608f82228181aaaaa81aaaa8019181818206aa81aa8060654a16aaa173e0591858580616060606060616060606068daab2a90d806062e0607501d3e1705c93aaa0eaa11918064e06260606060e06060606161616170d8dd81818180218791a46a18780000181d01c06061616161600060606060060600370dc000710b8bc5616171585c172191919d8001818181b3939d83b3939d8385858585c363758585a163e161e0005806060681a061e06060606061606160606060606160600000606060606060606060606060150585918585858000580018185858181818181818597818181818dc37058dc56161740006062e0607501d3e1705c86464676164e16661616160e00064e06260606060e06060606161616170d8dd0c00c0c0d0340c3c00c0c0c00c0c0c0c03032a43474311c030b03030303032f030303031b86e21b00c0c5c0c0ea03a7c6e1b90d0c00c9c0c4c0c0c0c1c0c0c0c0d1d1e1b1ba22a82e06285cfaa85e5e16460581818baa08fa4608baa06a87aaa515501d3f54accaaaaa115c4610bd17c5f505c174aab4b27aad4aa119182e06062e5e16165ea83a4eb5509c0f13d4fcfa58393cfcf83a58b8193c1fe201a8782e060585aa85cfc178581606062e1616ab406e6e6e6e02e2e060606061e1eb5532c515501d3f55555507a8786e6e0b81818b97858597a59383a59383d578806a1e0b8181616aa173e178581606062e16161601e1e1e6e01e2e060606061e1eacb14554074fd5555541eab4115c6e10bd17d417507c1f5507d55507a8786e6e0b81818b978585978787878387938783d542703c4f5b86e018b818b82e0629a986e6e0b81818bd514554074fd541f334115c6e10bd17d4175525a586e6e0b81818ba5a9a9d542703c4f5f007c0f50f0f030f170f030f0f000b50f0b0b0f2f0b0b0f0f000b2f0b2f0f0f550f0f0f0f0f0f0f0f1b1b0f0f1b230f0f0f0f00001b171b031b031b17a83d60f0fa0f1b8ac006e1ba0ba7c2c2e82c2c2c3d43c3c3c3c1c3c9c3ccc00fced0cecbc2c2cbc6c6c6c1c6c9c6c4e1b1ba8000000023819f8ba3819f8baa800f8f8f8f8f8fd2a800597859785858f8f8f8f8f8faa800dc37105cb64e760eb64e760eaa007e768e765e16165f0d8ddf01f0001f031f1f1f1f1f1755001f0b1f1f1f1f1f2f55000b2f0b2f1f1f1b1f1f1f1f1f1f1f1f1f1f1b1b555500001b171b031b031b17a87c7c6c6c7c7c7c7c7c7e954006e1ba0ba7c2c2e82c2c2c7c9c7c7c7c7c7c1d5400fced1cecbc2c2cbc6c6c6c1c6c9c6c4e1b1ba3c3c8c7c8c7d8c3c001b11c8c8cfd1c0e3c5e3c0cfc5c002cbc2cbc22b0002f002cbc2cbc6e1b8002c2c0006c1b86e20b96c8c8ced6c9cecce3c9ceccc016c3f3b473b2f0b0b2f86c6e8e7e8e7e1fa38165e165e17858165e165e361e368da361e03636360362e36063606362f50dc3710d8370dd05d3e16174161616b6b62d87e8e8e7e5e16165e3636360e364e36270d8dd548c11f044503555039f00c8c0c0c50b0b5550b2f5502c2c0303030365565528aa82e9faa595d555569555422b88c203a80ea0baa49d55075508c8c030303030b0b0b0baa84e0789eb70dc4f534f0dcdc0b0b0b0b02c2c0b0b0b0baa28aa82e9faa83e66822b8dc217a80ea0baa4f4f0dcdc53530b0b0b0baa84e0789ebe00aa00aa0016161616a00000007e2ece06ce067e2e3e3f43e3e3e3eaa00370dc16171058d8d8f8f8f8f8f8faa801f9d9d85858585b3939d83b3939d83c36377c07c0007c0c7c7c7c7c7c5d54007c7c2c2c7c7c7c7c7c7c7c7c7c7c2d555400002c2c2c0c2c0c2c5c7c2c7c7c7c7c7c2d54002c2c2c2ea1f1b1f1f1f1f1f954006e1b82c2c6c2c2ea0ba7c7c9c7c7c7c7c7c1d5400fcecec2c9c2c4c2c2c2c1c2c2c2c2e1b1bbcf93cfcf8393e161683cf8da4f3f3f3e0e2e064f0dc455500c8c0c0c5502c2c030303035555023232323003030303030303035a555521b00e0382c2e982e9f1b1b5555508c8c030303030b0b0b0b2707270786c6eaa4608f822281aaa81cf80646060628585aaaaa85aaaa80591858580181818181818181a16aa85aa8161601818181d48daab2a90d80701c1616361617505d3e93aaa0eaa1191806060606164e16261616160e161616170d8dd81818180058585858001818181a18791a46a187800001818000181d01c0606370dc000701c1710d8dc56060715a191919d800181818185858585b3939d83b3939d83c363760606818f8187800060181918181818000180058585a168587818185858181818181818181818185800001818181818181818181858b8585858581858181818181858001818181d4370dc0637158181d0001c0705858d8585d4174fa191919d81938199818181838001818181859385898585858385858585c36374f004f23233f000b0b0b0b000b02c2c2c2d3c3c8c7c8c7d3c3c02cfc5d8c0e5c0cfc5c22b001b86e001b06e1b82e21b1b0004f23233b003f3b773b0b0b0b0b63273b3377273b3386c6e 24 16777215 10 1023
def hc_93_11 : Nat → Nat := unpackHintV5 0x8570d9a0641f07ad4d79cef38c6ca4e31a1d2186154e4173723c58a48714613904dfc7111a83ae3f40ec0dcdc0532b88fcaf4b7327f87b4852b571cae93860aa42139c91c4151a40c567fc17b335015692c04c013012002003c01800840d801d0080064020000032 0x2c3c2c0000003d43c2c0c2c5c2c0c2c2c0142e7d42c2d5000b0b0b0b956aaa82e1ba000ac2aaa8ac3cac7cad2b2b2b0b2b0b2b2b2b2b2b0b2b2b2b2b2b02b2b172b2b2b032b2b2b0b2b2b2b0b2b2b003d43c2c2c2c1c2c9c2c1c014ced0cec2c2c2c2e8eea2b2b2b072b272b2bf50f000b50002cbc2cbc2c2cac7cac7cacac0001ac5dac0dac0dac5d4acacacacacae5800acaaaaa0000f50f005b3b433b2f0b0b2f6b273b076b273b07aaf50f000b0b550b9f000b2f0b2f0b0b0b00000f170f030f030f0f56558002b0aaaaaaa83e1ba2b0f2b1f2b4acac0acac5cacacac0cacacacbcacacac2cacacac3cac3cacacacacac3cacacacacac00f50f005b3b433b2f0b0b2f0f0f0f070f270f07a3ba8acacac1cac9cacaf170317000b0f0b42d0b0b00000b170b0b0b0b0b0003030b9f03030b0b030303aa238002b0aaaaaaaa2b0f2b1f2b4acac0acac5cacacac0cacacac2cac2cacacacacac2cad1cacacacacac2cacacac2cacac04f23233b00170303170b0b0b070b270b070b0b0b0ba3ba8acacac1cac9cacaf030303000b2f0b2f0003030b9f03030303030f0340d03030000030303031703aa238002b0aaaaaaaa2b0f2b1f2b4acac0acac0cacacac0cacacacbcacacac2cacacac0cac0cacacacacac0cad4cacacacac04323233b00030303032f0b0b2f0303030703270307a3ba8acacac1cac9cacae1c3c8d2361c3c00000c0c0c0c000c0cacacacacacac2c2c2c2c002c2cacacacacacac0c0c03aa0000a0aaaa4323233b0087273b0787273b07030303030b0b0b0ba3bab030340d030f000003030303000303030b0b0b0b0003030b0303030303030baa238002b080e1baaaaaaaa2b0f2b1f2b4acac0acac0cacacacacacac0cac0cacacacacac0cacacac0cacacac2cacacac2cacac04323233b000327030703030307030303030b0b0b0ba3ba8acacac1cac9cacaf0303030017171717000303179faa238002b080eaaa85e2b0f2b1f2b4acac0acac0cacacac0cacacac5cacacac5cacac04323233b000303030317171717a3ba8acacac1cac9cacaf170317000b2f0b2f000b030325c3c8d2365c3c00002c2cacacacacacac0c0cacacacacacaea88e002b2aaaa80012c8c8cec005c0c0c5cbc2c2cbd2c9cec1d2c9cec1eab170317000b2f0b2f000b0b030303030b170f1745d170f00000b0b0b030303aa238002b0aaaaaaa85e1ba2b0f2b1f2b4acac0acac5cacacac0cacacacbcacacac2cacacac5cac5cacacacacac5cacacacacac04b23233b00170303172f0b0b2f1717170717271707a3ba8acacac1cac9cacae32300232300aa238002b0aaaa2b0f2b1f2b4acac0acac5cacacac0cacacacbcacacac2cacac023233b003b3b3b3ba3ba8acacac1cac9cacaf0f030f0f547c3c3c0c0c0c0c0c0c6cdc0c0c6c6c0c0c0c0c0000002b140e7d40c0d50303030303030303000f50f0303032f030b03031b0b1b1b1b0b1b2f00030303030f5580c0e03a03031b1ba0002b000380e1b86e0f50f03030307032703071b271b331b1b1b070003030303473b4f3b86c6c6e37b0f0b0f0f547c3c3c2c2c2c2c2c2c6cdc2c2c6c6c2c2c2c2c0000002b03d43c2c0c2c5c2c0c2c2c6c0c6c5c6c0c6c5c0142e7d42c2d50b0b0b0b0b0b0b0b000b0b0b0b0f5582c2e0ba0b0b1b1ba0002b001b86e0b82e0f50f0b0b0b070b270b071b271b331b1b1b07003f3b433b0b0b0b0b86c6c6e37d878da363e361e0015806060681a061e0606060606360636060606060636066e00000606060606060606060606060006060616161616161616161616161600060616060606060606167e37118d8dc0005600060636374060701d01c0705c172191919d8d938d998d8d8d838001938183818181838181818185858585c3636371bec3c6d1b1f1b0f000ac23233f1b031b171b031b17002323571b0b1b1b1b0b1b2f003f573f1b88c6c6e0002b001b86e1b86e23233b1b271b331b1b1b07003f3b3b573b3b86c6c6e37f803e01a878181878b81818787800787aa87878787878787878b8b87878b91878787878000541ea1e1e161e5e1e161e1e002e06062e2e162e5e2e162e2e1eb0787d078dc560101d3e06074060606370dc1ea1e1e1e1e0e1e4e1e66002e06062e2e2e2e0e2e4e2e2696769e770d8dd4000000007c7c7c7c7c7e95401ec2decbdec2decbd54005c0c0c5c0c0c7c7c7c7c7c7d540080e1b86e7b273b077b273b075500170303174b3b533b86c6ef80f8000f818f8f8f8f8f8baa800f8f8b8f8f8f8f8f8f8f8f8f8f8b8baaaa8000543e163e3e3e3e3e5eaa002e06062e2e162e5e2e162e2e3e3e36363e3e3e3e3e3f4aa0101d3e06074060606370dc3e4e3e3e3e3e3e0eaa002e06062e2e2e2e0e2e4e2e269676a6770d8dd0e1e463e463ec61e000b8062e062e1158000b80a64646aea6170e5f0e16ae5e002e06062e370dc00060600036101c370dc96464676964e76670e4e766600960b81818ba59da99dc363762e062e0b8182e1e2e8ba2e1e02e2e2e1529aba9ab8aea60b81818b8b858b978b858b8b8dc3710d901d3e06074060606370dc96962582e06062e2e2e2e0e2e4e2e2696a6a6af0d8dd548c11f0445030355503175500c0c50b5550b9f02c8c2c2c030303036556552880e9faaaa58fd555569555422b88c203a0ba82eaa49d55075508c8c030303030b0b0b0baa84e0789eb70dc0303030300c0c4347430dcdc03030303aa2880e9faaaa83e66822b8dc203a2fa82eaa43430dcdc030303034747aa84e0789ebe00aa00a00000003e3f43e3e3e3eaa0006060606ce168e5ece168e5eaa0006071018b8b8f8f8f8f8f8f8dc372a8001818181b3939d83b3939d83a39d9dc36377c07c0007c7c0c0c7c7c7c7c7c7c7c7c7c7c0d555400007c0c7c7c7c7c7c0d5402a1f0b1f1f1f1f1f2f5500030b03030303032f030303031f1b1f1f1f1f1f954000c0c5c0c0ea03a7c6e1b87c9c7c7c7c7c7c1d54000c9c0c4c0c0c0c1c0c0c0c0d1cecee1b1ba1800181818180018861e463e463e861e00611580219191a18001818181b185a397cb85a3978dc37000d80710b8b8000dc372191919d8001818181b1939d99bb939d99a39dbb9dc363779f279f9f0727d070b039f1b49e7e7e7c1c9cbc2e17 26 67108863 11 2047
def hc_93_12 : Nat → Nat := unpackHintV5 0x950c1500000094f00794c40b9468178e3d8b844a7d7e2d877781ab6d3e9168c91d687c13685c0868041667901d67700867580666d8205eedfb53a2d34d758b4cd8274c5c1f4b1851430a04380ac03229782a71ee1ce3641529ee07bb5c0001ee 0xe0713f7eefc2786e22aaa81191919182a806060181aaaaa816160585aaa8181a06aaa5446555555552a84646138393838181818185858585d544555500323030305500c0c0303035502c2c03030b0303030303030b5a7d54a88caaaaaaaa5411f48c1035550340d5503540d50b542d595508c8c0327030703030307030303030b0b0b0baa44d0749d622a806062a82e2e01818bcfad3eaa544655550bca823e918206a81aa2ea8bab2aa11918060606062e2e2e2f5489a0e93ac45505c0c550bc2c0b03035555408c8c8c8c02c2d5540c0d555954a88caaaaaaaa5508c8c170303172f0b0b2f4b279b074b279b07aa88aa0b818aa1785816160606060616aaaa02e2e2e460161616060606b4faa9511955555550bc374a823e91822ea81aa5ea85aa2e8baaa2eaab2aa119182e06062e5e16165e2e2e2e0e2e4e2e0f5489a0e93ac45508c8c5508c8c5a7d54a88caaaa5411f48c117540d52f542d595508c8caa44d0749d79f93cffe0e4fcfc6e279ffff072783e22a806062aaa811919191828181aaaa8161601818181a0606167e1616aaaaaa446363601c070787d0181d05c172a84646018181819383938385858585c36375523047c11140c0d555540d555400c8c0c0c1035540d54030300c0c0d0b5542d540b0b00c0c2c0c0c0c0c0c0c2cfd43d5569f2231b1b00c6e80c0e80e0382e0b92744d5075508c8c0327030703030307030303030b0b0b0b86c6eaa4608f822206aa8baa84646216aa97aa846461fab9fa87aaad3e44636360dc370dc3724e89aa0eaa119187e7eaeaf0d8dd0e7d2c1c9e1cf83a5c39f074b0f4178be2785fc40350f05c0c0b50f0bc2c0b0b030303030b4383c3d543c3c0dcdcdcdc02c2eaa80c0eaaa9569f8a2aaaa96a43d43c373705c0c0c5cbc2c2cbd2c9c1d2c9c1eabc40350f05c0c0b50f0bc2c0b0b030303030b430f0f550f0f01717173700b0b0b030303a55a7ca2aaaaaaaa0f822b8dc217a80ea2fa82ea1785eaa17aa950f50f0dcdc170303172f0b0b2f1717170717271707aa84e0789ebc40f50f0dcdc0f50f0dcdc4f4343a55a7ca2aaaa0f822b8dc217a80ea2fa82e950f50f0dcdc43434f4faa84e0789ebc3cac7cac7cacac0000005032b2b2b2b52b2b000f50f6b0b6b2f6b0b6b2f000303030396a00000aaaa0f50f6b273b076b273b070003030303473b4f3baac3c0c00000140e7d40c0d5000f50f0303032f030b03030003030303956aaa80e1ba000ac2aaa8ac3cac7cad2b2b2b032b032b2b2b2b2b032b2b2b2b2b02b2b032b2b2b032b2b2b2f2b2b2b0b2b2b003d43c0c0c0c1c0c9c0c1c000c0c0c0d1ced3cee8eea2b2b2b072b272b2bd40003032b1f2b1f2b2b000052b2b2b2b2b2b0f50f00170303176b0b6b2f6b0b6b2f96002b2aa8002a83d43c005c0c0c5dac9cec1dac9cec1d2ced3ceeab0355039f000303030000543d43c005c0c0c5c3c2c3cbc3c2c3c3e558002b0aaaaa83e1baaa2b0f2b1f2b4acac0acac5cacacac0cacacac3cac3cacacacacac3cacacacacacacbcacacac2cacac00f50f00170303170f0f0f070f270f074b3b4f3ba3ba8acacac1cac9cacafc3cac7cac7cacac0000003d43dac0dac5dac0dac5c0050b2b2b2b2b52b2b000b0b0b0b96a00000aaaa0f50f6b273b076b273b0700533b433b0b0b0b0baa 24 16777215 10 1023
def hc_93_13 : Nat → Nat := unpackHintV5 0x7be13dbb809c1bf2f36d5b27965c345af46e6d666cf2a90a8b54500d2a0e0694f9836a7601b4f8b09a462d8d0f0d027e5a4b3783ea99b0844af2f9652d13124e32190fe5cc72bd4e2f228f12cd3107528502984440a8e8d002d46800b02c00000000000b 0x472323000b2f2f0b232f0002c02cbc2cbcbc3cbc7cbd2f0f00b2f172f032f032f17015c8c8cdc015cdd1cdcbc2c2cbcbc6cbe2f1b2f2b5b23233b005b3b473b2f0b0b2f2f2f2f072f272f33373b5737b0b0b42c7c2c3c000b13c8c8d3c2c0c2c2c2c0c2c5c002c2c8c2c2c2c0002c002c2c2c2d3c8c8cdc2c6c2cac2c2c2e005337370b0b0b0b4f23233b0b270b330b0b0b0700533b3b0b0b0b0b373b37f80f8000f818f8f8f8f8f8baa800f8f85a38f8f8f8f8f8f8f8f8f8f8585aaaa8000058b858f8f85858f8f8f8f8f8f8597aa80018185cf818185858181818f8d8f8f8f8f8fcaa002e06062e161617058d85c161616163e4e3e3e3e3e3e0eaa002e06062e1616160e164e160e161616166e767e6f3c3c8c7c8c7d3c3c000b00c5c0c5c05c5c0005c00b0b0b0b0003030000b003030b3f2323373f1b372b3f1b372b00170303170b0b0b0b4f23233b47273b3347273b3300170303170b0b0b0b373b3f379e0062e062e0b818161e1685a161601616160162e1616161616058580606173e060616160606067e7e9e1f82e06062e161617058d85c161616169e969e2582e06062e1616160e164e160e16161616967e7ff01f0001f1f03031f1f1f1f1f1f031755001f0b1f1f1f1f1f2f550003030b9f030303031f1f03531f1f1f1f1f1f1f1f1f1f0303555500000303030317031f1b1f1f1f1f1f954000c0c0c0cbc2c2cbc0c0c0e031b0387c9c7c7c7c7c7c1d54000c0c0c0cbc2c2cbc0c0c0c1c0c9c0c1cdced5cde187918f918fa1878000601818181800181800018165e165e02e2e0005e001806068646466ea6366e56a6366e5600060606065e16165e86464676a64e7666a64e766600060606065e16165e6e76ae6f0c00c0c0c0c030302cbc2cbc2f0b00c0c2e7c0c0c0c0c0c3c0d0340c0c00c0c0c00c0c0c0c5c0d0d5d0c5700c0c0c0cbc2c2cbc0c0c0e031b0390d6d0c5b00c0c0c0cbc2c2cbc0c0c0c1c0c9c0c1d6d5d5e3f371b8fc6cdfa59d93f4b273bf802a80280000000f8f81818f8f8f8faa8001818181806061616163e3e3e3e3e3eaa0006060606366f0d9bc16161616aa00060606064e760e4e760e161616166e766ff01f0001f1f03031f1f1f1f1f1f1f1f1f1f03555500001f031f1f1f1f1f0355000303031f0b1f1f1f1f1f0b550003030b0303030303030b1f1b1f1f1f1f1f954000c6c0e03030380c0c0c0c2c2c2c2c7c9c7c7c7c7c7c1d54000c9c0c1c0c0c0c1c0c0c0c0c2c2c2c2cdcecde1800181818180018861e463e463e861e0060060600161616160016018180616160008646466e0006060606c6366e56ce366e5616161616864646760006060606c64e7666ee4e7666161616166e76ce6f0c00c0c0d0340c3c00c0c0c00c0c0c0c030300c0c0c2c2c2c2c0b0b00c0c2c0c0c0c0c0c0c2d0d0c00c6c0e03030380c0c0c0c2c2c2c2d0d0c00c9c0c1c0c0c0c1c0c0c0c0c2c2c2c2fe00f806a1e06061e2e06061e1e0016a1e16161e5e16161e1e0016160606060616861e1e1e1eaa2e87878787878787878b8b87878b9187878787800005858581818187a87878787c1e361e56002e06062e5e16165e2e2e2f0b8d8bc1ea1e1e1e1e0e1e4e1e66002e06062e5e16165e2e2e2e0e2e4e2e0e6e767e6f4000000007c7c7c7c7c7c2c2d54007c7c7c7c7c7c0c0d54002c0c0c7b1b379ec6cde5500170303172f0b0b2f7b273b077b273b075500170303172f0b0b2f373b3f37f80f8000f8f81818f8f8f8f8f8f8b8baa800f8f85858f8f8f8f8f8f9797aa80058581818181858f8f8b8f8f8f8f8f8f8f8f8f8f8b8ba8b87aaaa80000b80585858181818f8d8f8f8f8f8fcaa002e06062e5e16165e2e2e2f0b8d8bc3e4e3e3e3e3e3e0eaa002e06062e5e16165e2e2e2e0e2e4e2e0e6e767e6ff00400045d54005c17171f1f1f1f55003f373f371717171755004b3b4b3b17171717373b3f37f80f8000f8f81818f8f8f8f8f8f81aa800f8b8f8f8f8f8f8ba2eaa002e01818bcf8f8d8f8f8f8f8fcaa00060606062e2e2e2e3e4e3e3e3e3e3e0eaa00060606062e2e2e2e6e767e6f0c00c0c0c0c030305c5c5c5c171700c0c5e7d0cfd0c3f00c0c0c0c5c5c5c5d0d2d0c4b00c0c0c0c5c5c5c5d2cfcffe3e3e3e3e3e3e2e1e3e3e3e3e3eaf73e3e3e3e3e3e3e3e2f3eaa0580f8f8f8f8f8f8f97cfaa80601606060f8d8f8f8f8faa9f9b9f9b8b81818b978585978f938f8f8f8faaa59da59d8b81818b978585979b9d9f9be30f231f231f630f0001700c5c0c5c02c2c0005c00b2f0b2f003030002f002c0c0c3f2323373f1b372b3f1b372b003f05c0c0c5cbc2c2cbd2c8c8ced2c9ceccd2c9ceccc012c170303172f0b0b2f373b3f37c5c0c5c170302cbc2cbc2f0b02c2c0c0c0c0c2c5c3c5d1745c3c05c5c5c02c2c2c0c0c0cfcfc3f05c0c0c5cbc2c2cbc5c5c5e171b1792d2c4b05c0c0c5cbc2c2cbc5c5c5c1c5c9c5c1d2cfcfe2b0003c03c010c0cfc5d0c0cfc5c3d43c013c2d5cbd3c2d5cbc3d43c00fd0d0cfc011f0156001b06e1b86e1b9dc9ceccd8c9ceccc3d43c00fced0ced5ced3cee1b1baa0f103c3c03c03d43c3c0c3c5c3c0c3c3c3f4303d43c3c2c3cbc3c2c3c3c574f0fd0d0cfd69f5a5486c1b86e1b86e0f50f0f0f0f070f270f1303f43433f574f4f5786c6e88aa0b818aaaa0161616460162e16aa058580606173e06061616060606b4faa9511955555554a823e91822ea81aa1685aaa16a3aaa16a85ab2aa119182e06062e1616160e164e160e161616175489a0e93ac45500c0c550bc2c03030b9f03030303555500303032300303030317035a7d54a88caaaaaaaa5411f48c103540d52f542d50340d550354d5595508c8c030303032f0b0b2f0303030703270307aa44d0749d793f27 25 33554431 10 1023
def hc_93_14 : Nat → Nat := unpackHintV5 0xb8260fb169afa86a409fb22e98b5bf9259978cb968835a587a5a4070827666ca6e5dca40550a304e0dbf47b1973ef2302fe3c42a396a20d25a17d2400f12300003c4 0xf803e07a878781878b878187878007a8787858797878587878027a1a187a87878787c1e361e56006e866e6e9e6e1ea1e1e1e1e0e1e4e1e6600768676769e766e766ff01f0001f031f1f1f1f1f1755001f0b1f1f1f1f1f2f55001f1b1f1f1f1f1f95400dcdcdcdc7c9c7c7c7c7c7c1d5400ececececdcecdfc3c000300f000047c05503000313c2decbdec2d1cbc3d43c000c0c0c0d9c6cdcadec6cdcac3d43c000c0c0c0d1cdd3cdddc9ceccdec9ceccc3d43c000c0c0c0d1ced3cecdced9cdf0f030f100c0c00c140e7d40c0d500c0c0f50f0303032f030b030311d3c030303030f50f03030380c6c0e003030303474f4f470f50f0303030703270307003030303474f4f4788a073eaa0b8b81918a823e91821eaa846460b81818baa5e85aaa846460b81818bab236a7ea67eaa119182e06062ea83a4ea96a6a6967e7f548c11f044503555039f00c8c0c0c42d552f5508c8c0303030346d55954232300c0c0c0d1d1d275541d54232300c0c0c0d1d1f003c0f14405c0b2f2f2f4f0b4f002d3c3c00b0b0b0003c3c1700bcbcfcdcfcdc3f1b86e4b3b4b3b12cbc1c9c1f0300003c000f00d54047c0005c00f50f4f0b632f4f0b2f004f05c0c0c5c3d43cfc6cdcacfc6cdcac00fc170303173f373f370f50f4b273b334b273b33004b05c0c0c5d2ced3cecdcecfcdfc4030355039f05c0c03030300f0f0f0543d43c4f05c0c0c5c3c2c3cbc3c2c3c3c3d43c3f05c0c0c5c3c3c3e0f1b0f8fd3cfc3d43c4b05c0c0c5c3c3c3c1c3c9c3c1d2d3d3d2cfcff17170323170000c05c3c5c7c5d170f003014c8c8c005c0c0c5c5c2c5cbc5c2c5c5cfc8c8cdc005c0c0c5c5c5c5e171b172b3f373f374b23233b001703031717171707172717334b3b533b373b3f37c0c0d031f030f0000c030323030303000030043232343030b03030303032f000303030343232337031b032b0303038000c0c0c0d1cdcdd0c8c8cec0c9c0ccc0c0c0c1c000c0c0c0d1cececdcecdfc3c000b00f0043035317430353170f50f000047c0550b000b02c2c2c2d9c6cdcad8c6cdcac3d43c014cdd0cdc2c2c2c2ddc9ceccd8c9ceccc3d43c014ced0cec2c2c2c2cdced9cdec3c2c3c40b0b00b00f50f0b030b170b030b0b14d0c50b9f50b0b540b0b02c2c2c2c3d43c2c2c2e0b1b0b814d0d0d4c2c2c2c2c3d43c2c2c2c1c2c9c2c1c14d0d0d4c2c2c2c2e22a84646285cfaa85e5e164605978597aa08fa4608baa06a87aaa11918ae8e8e5e16165eac8daaa846462da3a397858597aa0e93aadababd523047c111035545d542323142d5542e7c0b230b0b02c2c2c2d1b5565508c8c53530b0b0b0b49d55075508c8c53530b0b0b0bd43c000c0b0b47d1f0f0b000000303000b50002c0c0c5c2c2d42c2c5d0f50f00170303173f1b378fc6cde2f0b0b2f0f50f00170303174b273b074b273b072f0b0b2f373b3f37d543c000300f0f47d43c3c00c00b0b550b9f000b0303170b0b172f0b0b17170b0b0b00000f170f17030303030f030f0f0f170f170f0f0f0f0f170f0f0f0f0f543d43c005c0c0c5c5c5c5e171b172b2f0b0b2f0f0f0f83c6c3e0f50f001703031717171707172717332f0b0b2f0f0f0f070f270f07373b3f37b003c0f00c5c5c5d0c0d0c003430f000c0c0c000f0f05c5d440bc0bc0fcdcfcdc3f1786e4b3b4b3b12c5c1c9c1ec2c0000f0003c0f50f43036317430317004302d54047c000bc00b2f0b2f0f50f571b372b571b372b005715cdd0cdcbc2c2cbc3d43d6c9ceccd6c9ceccc016c5b3b433b2f0b0b2f373b5737f103d43c4302c2d542e7c2f0b02cbc2cbc2c2c2c03c3c3c03c5c3c0c3c0c3c3d50f50f15c5743432f0b0b2f0f0f0f83c6c3e0f50f16c5b43432f0b0b2f0f0f0f070f270f075b5757d400030347d1f0f0300005030303031742d43c002c0b0303170b0b0000f50f00170303173f1b378fc6cde2f0b0b2f0f50f00170303174b273b074b273b072f0b0b2f373b3f37c0d540e7c000c0c0c000150b550f0002c02c0c0c5c2c2c3c3cbcbc2c3c2c2c3c3c3c3d1f50f0f00b17170303030317170f0f0f0f0f0f2f2f0f0f2f0f0f0f0f003d43c005c0c0c5c3c3c3e0f1b0f8bc2c2cbcbc6cbe2f1b2f2b0f50f00170303170f0f0f070f270f072f0b0b2f2f2f2f072f272f33373b3f37 24 16777215 10 1023
def nh_93 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_93_14 (Nat.sub p 448)) (hc_93_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_93_12 (Nat.sub p 384)) (Nat.blt p 416)) (hc_93_11 (Nat.sub p 352)) (Nat.blt p 384)) (hc_93_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_93_9 (Nat.sub p 288)) (Nat.blt p 320)) (hc_93_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_93_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_93_6 (Nat.sub p 192)) (Nat.blt p 224)) (hc_93_5 (Nat.sub p 160)) (Nat.blt p 192)) (hc_93_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_93_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_93_2 (Nat.sub p 64)) (Nat.blt p 96)) (hc_93_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_93_0 p) (Nat.blt p 32)
def f_93 : Nat → Nat × Nat := unpackForestF 0xc5f00c57e945500b5f00b5b00b57e7253e6b5600b5300b4b00b47e4c5500a5f00a5b00a57e2a44e145be1b53e125600a53e0244dfc6300a4b00a47ddd67ddb5600a3fdc567dc25600a3bd993fd9937d983fd9837d9470d8567d845a00a37d3d6fd6a7cd3d67d5b60d5457d3b44d4466d3a5600a33d2c550095fcab4fcab4bcd04fd015ccd04bcd047ce84ccd954cd864cd043cc95ccab47cb454cb134cab430095bc683fc914cc683bc6837c783cc7144c6833c6470c5a3700957c382bc4064c3823c3134c2b4300953c1964bac6fc0944bac63bf964bab6fbe934bab63bab4fbab4bbc95cbab47bb454bb134bab430094bb8b6fb8a6fb8a3700947b656fb737cb6567b63560093fb53670093bb4470add67adc5aaf83fb214caf83baf837b083cb0144af833af470ada67ae460ada5700937aab6bab82bab823ab134aab6300933a856fa927ca8567a82560092fa74670092ba63709fd67a202fa493ca202ba2027a302ca2934a2023a1b709fc67a0b609fc579fb5a009279cc6b9d83b9d8339d1449cc63009239a4559b1649a14b9a1470085f8934f8934b9494f97a5c9494b949479614c9525495164949439405c8934792c549283489343918448924f8924b8fa4f8fa478f05c892478e024892438d0348923f8923b8b34b8b3478a84c8923789824892330085b8513f87a4c8513b851378613c85a448513384c70812378113b83470811378112b81b7081127008577f12b7f9647f1237e8347a3437d8447a24f7c8247a2437b8347a23f7a8247a23300853790646bc6f780446bc63770646bb6f760346bb636bb4f6bb4b7405c6bb477145471a6f7226471a63710346bb43700646ba6f6f0446ba4f6e05c6ba476d0346ba3f6c04c6ba370084b6836f6826f682376816f68137681270084762d6f66b7c62d6762b56651446296b6414462963631446295b0083f5fb675fa6b5fa675fa3b5fa370083b5ec704f5675da374f45a5993f5c24c5993b599375a93c5a24459933594704f267584604f25756a3f56a375615c4f16b554704f1675415c4f15b4f1574f12b51d8051b804fe7750a70505674fb504f127008374936b4d12b4d1234c834493634b8244926b4a8244926349824492330083343d6f47a7c43d6743a56461344396b4513443963441344395b0082f40c6740a6b40a6740a4b40a470082b3fb70305673b92f3e23c3b92b3b9273c92c3c2343b9233b370304673a36030457392473035a37a4b37a473714c3016b36370301673514c3015b301573014b32d8032b8030e7731a703156730b5030147008272a46b2e13b2e1332d8442a4632c8242a26b2b8242a2632a8242a243008232916423c6f2817c23c672716423b6f25b6f25b672517c23b672415c23b470081f228641d46f2187c1d467208641d36f1f36f1f3671e87c1d3671d85c1d3470081b10d6f1ba7010d671aa6810c6f19a7010c6718a6010c5717a6810b6f16a7010b6715a6010b571458014280126771317c12d671225010b471134710a5a008170f8640146f0146b0e07c014670d044014630c0640136f0136b0a87c0136709834013630134f0134b0785c0134706454060340134301b5f0496001b5701a5f0316001a570214001a3701124008130003f 9 11
def ch_93 : Nat → Bool := dagCheckNodeV5 fullMask g_93 ep_93 6 63 bds_93 469 (dagTraceF fullMask rootStock 11 f_93) cur_93 nh_93
set_option maxHeartbeats 0 in
theorem rc_93 : dagCheckRootsV5 fullMask g_93 ep_93 6 63 469 bds_93 (dagTraceF fullMask rootStock 11 f_93) (cur_93 0) (nh_93 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_0 : treeBlockF 0 32 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_1 : treeBlockF 32 64 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_2 : treeBlockF 64 96 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_3 : treeBlockF 96 128 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_4 : treeBlockF 128 160 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_5 : treeBlockF 160 192 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_6 : treeBlockF 192 224 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_7 : treeBlockF 224 256 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_8 : treeBlockF 256 288 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_9 : treeBlockF 288 320 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_10 : treeBlockF 320 352 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_11 : treeBlockF 352 384 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_12 : treeBlockF 384 416 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_13 : treeBlockF 416 448 ch_93 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_93_14 : treeBlockF 448 469 ch_93 = true := by decide +kernel
theorem nj_93_1 : ∀ i, 0 ≤ i → i < 64 → ch_93 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_93_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_93_1 h1 h2)
theorem nj_93_2 : ∀ i, 0 ≤ i → i < 96 → ch_93 i = true := block_join nj_93_1 (fun _ h1 h2 => treeBlockF_at nb_93_2 h1 h2)
theorem nj_93_3 : ∀ i, 0 ≤ i → i < 128 → ch_93 i = true := block_join nj_93_2 (fun _ h1 h2 => treeBlockF_at nb_93_3 h1 h2)
theorem nj_93_4 : ∀ i, 0 ≤ i → i < 160 → ch_93 i = true := block_join nj_93_3 (fun _ h1 h2 => treeBlockF_at nb_93_4 h1 h2)
theorem nj_93_5 : ∀ i, 0 ≤ i → i < 192 → ch_93 i = true := block_join nj_93_4 (fun _ h1 h2 => treeBlockF_at nb_93_5 h1 h2)
theorem nj_93_6 : ∀ i, 0 ≤ i → i < 224 → ch_93 i = true := block_join nj_93_5 (fun _ h1 h2 => treeBlockF_at nb_93_6 h1 h2)
theorem nj_93_7 : ∀ i, 0 ≤ i → i < 256 → ch_93 i = true := block_join nj_93_6 (fun _ h1 h2 => treeBlockF_at nb_93_7 h1 h2)
theorem nj_93_8 : ∀ i, 0 ≤ i → i < 288 → ch_93 i = true := block_join nj_93_7 (fun _ h1 h2 => treeBlockF_at nb_93_8 h1 h2)
theorem nj_93_9 : ∀ i, 0 ≤ i → i < 320 → ch_93 i = true := block_join nj_93_8 (fun _ h1 h2 => treeBlockF_at nb_93_9 h1 h2)
theorem nj_93_10 : ∀ i, 0 ≤ i → i < 352 → ch_93 i = true := block_join nj_93_9 (fun _ h1 h2 => treeBlockF_at nb_93_10 h1 h2)
theorem nj_93_11 : ∀ i, 0 ≤ i → i < 384 → ch_93 i = true := block_join nj_93_10 (fun _ h1 h2 => treeBlockF_at nb_93_11 h1 h2)
theorem nj_93_12 : ∀ i, 0 ≤ i → i < 416 → ch_93 i = true := block_join nj_93_11 (fun _ h1 h2 => treeBlockF_at nb_93_12 h1 h2)
theorem nj_93_13 : ∀ i, 0 ≤ i → i < 448 → ch_93 i = true := block_join nj_93_12 (fun _ h1 h2 => treeBlockF_at nb_93_13 h1 h2)
theorem nj_93_14 : ∀ i, 0 ≤ i → i < 469 → ch_93 i = true := block_join nj_93_13 (fun _ h1 h2 => treeBlockF_at nb_93_14 h1 h2)
theorem nc_93 : ∀ i, 0 ≤ i → i < 469 → ch_93 i = true := nj_93_14
theorem lb_93 : LowerBin fullMask rootStock g_93 12 :=
  lowerDagV5 (kn_cons lb_80 (kn_cons lb_78 (kn_cons lb_86 (kn_cons lb_81 (kn_cons lb_88 (kn_cons lb_83 (kn_cons lb_79 (kn_cons lb_92 (kn_cons lb_82 (kn_cons lb_85 (kn_cons lb_89 (kn_cons lb_16 (kn_cons lb_87 (kn_cons lb_90 (kn_cons lb_84 (kn_cons lb_91 (kn_cons lb_28 (kn_cons lb_31 (kn_cons lb_34 (kn_cons lb_17 (kn_cons lb_33 (kn_cons lb_36 (kn_cons lb_19 (kn_cons lb_32 (kn_cons lb_37 (kn_cons lb_39 (kn_cons lb_43 (kn_cons lb_15 (kn_cons lb_26 (kn_cons lb_46 (kn_cons lb_47 (kn_cons lb_40 (kn_cons lb_29 (kn_cons lb_56 (kn_cons lb_48 (kn_cons lb_55 (kn_cons lb_53 (kn_cons lb_54 (kn_cons lb_61 (kn_cons lb_62 (kn_cons lb_27 (kn_cons lb_18 (kn_nil))))))))))))))))))))))))))))))))))))))))))) rc_93 nc_93 (by decide +kernel)
def wg : List Gate := [⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [0, 15]⟩, ⟨GateOp.or, [16, 11]⟩, ⟨GateOp.and, [14, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241824 * 2 ^ 32 + 3936397440)) (13 - 1) := by
  rw [show canon fullMask (4008241824 * 2 ^ 32 + 3936397440) = g_93 by decide]
  exact lb_93
end PEqualNP.Outside.L_meta_49293
theorem PEqualNP.Outside.L_meta_49293 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241824 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241824 * 2 ^ 32 + 3936397440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49293.table2_from_lowerBin (4008241824 * 2 ^ 32 + 3936397440) 13 PEqualNP.Outside.L_meta_49293.root_lb PEqualNP.Outside.L_meta_49293.wg 18 rfl PEqualNP.Outside.L_meta_49293.wfits PEqualNP.Outside.L_meta_49293.weval
