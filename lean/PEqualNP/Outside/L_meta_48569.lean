import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48569

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

def m_0 : Nat := 0xf0f000000000000
def s_0 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_0 : Nat := 0x107000000000000
def ep_0 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_2 : Nat := 0x3030303000000000
def s_2 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_2 : Nat := 0x10103000000000
def ep_2 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_9 : Nat := 0xff000000
def s_9 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_9 : Nat := 0x17000000
def ep_9 : Nat := 0x600000000000000120000000000000014000000
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

def m_11 : Nat := 0x4444444400000000
def s_11 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_11 : Nat := 0x4044400000000
def ep_11 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_12 : Nat := 0x5500000055000000
def s_12 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_12 : Nat := 0x100000015000000
def ep_12 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_14 : Nat := 0xf0000000f000000
def s_14 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_14 : Nat := 0x100000007000000
def ep_14 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_15 : Nat := 0xc0c00000c0c0000
def s_15 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_15 : Nat := 0x40000040c0000
def ep_15 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_16 : Nat := 0xff0000000000
def s_16 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_16 : Nat := 0x170000000000
def ep_16 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_17 : Nat := 0xa0a00000a0a0000
def s_17 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_17 : Nat := 0x20000020a0000
def ep_17 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_18 : Nat := 0xf0f000000000
def s_18 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_18 : Nat := 0x107000000000
def ep_18 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_19 : Nat := 0x3333000000000000
def s_19 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_19 : Nat := 0x113000000000000
def ep_19 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_20 : Nat := 0x5555000000000000
def s_20 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_20 : Nat := 0x115000000000000
def ep_20 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_21 : Nat := 0xcc00cc00cc00cc0
def s_21 : List Nat := [0x440044004400440, 0xc000c000c000c0, 0xcc000000cc0, 0xcc00cc0]
def g_21 : Nat := 0x440040004c0
def ep_21 : Nat := 0x400008000000440000000c00000000000000000000000000000000000000000000000000000044004000400
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_21 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_21 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 3 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 3 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 3 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 3 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0x2288228822882288
def s_22 : List Nat := [0x88008800880088, 0x208020802080208, 0x228800002288, 0x22882288]
def g_22 : Nat := 0x20002080288
def ep_22 : Nat := 0x208008800000200000000800000000000000000000002000208020000000000000000000000000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14a59080f 4 15 2 3 9 511 11 2047
def nh_22 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_22 : Nat → Nat × Nat := unpackForestF 0x329c840f 1 9
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 3 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 3 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 3 ch_22 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 3 → ch_22 i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0x2222222288888888
def s_23 : List Nat := [0x88888888, 0x202020208080808, 0x22002200880088, 0x222200008888]
def g_23 : Nat := 0x2022200080088
def ep_23 : Nat := 0x220000000800002002000080088000202000008000000000000000000000000000000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xaa00aa00aa00aa0
def s_24 : List Nat := [0x220022002200220, 0xa000a000a000a0, 0xaa000000aa0, 0xaa00aa0]
def g_24 : Nat := 0x220020002a0
def ep_24 : Nat := 0x200008000000220000000a00000000000000000000000000000000000000220020002000000000000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_24 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_24 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 3 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 3 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 3 ch_24 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 3 → ch_24 i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_nil) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xffff00
def s_25 : List Nat := [0x555500, 0x333300, 0xf0f00, 0xff00]
def g_25 : Nat := 0x1f1700
def ep_25 : Nat := 0xe060000000000001012000000000000101400
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xff0000ff
def s_26 : List Nat := [0x55000055, 0x33000033, 0xf00000f, 0xff]
def g_26 : Nat := 0x170000ff
def ep_26 : Nat := 0x600000000000000120000000000000014000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xff00ff0000000000
def s_27 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_27 : Nat := 0x100170000000000
def ep_27 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_16, s_16, 4, g_16), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
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
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_16 (kn_cons lb_5 (kn_cons lb_6 (kn_nil))))) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xffff000000000000
def s_28 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_28 : Nat := 0x117000000000000
def ep_28 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_10, s_10, 4, g_10), (m_20, s_20, 4, g_20), (m_19, s_19, 4, g_19)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) (nh_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_10 (kn_cons lb_20 (kn_cons lb_19 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xff00ff00000000
def s_29 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_29 : Nat := 0x17007700000000
def ep_29 : Nat := 0x60000000000000000000000000000600000000000000120022000000000014004400000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xf0f0f0f000000000
def s_30 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_30 : Nat := 0x10107000000000
def ep_30 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_18, s_18, 4, g_18), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2)]
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def hc_30_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_30_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_30 : Nat → Nat := fun p => Bool.rec (hc_30_1 (Nat.sub p 32)) (hc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 43 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) (nh_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 43 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_18 (kn_cons lb_3 (kn_cons lb_2 (kn_nil))))) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xcccccccc00000000
def s_31 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_31 : Nat := 0x4044400000000
def ep_31 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x3333333300000000
def s_32 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_32 : Nat := 0x113133300000000
def ep_32 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_19, s_19, 4, g_19), (m_2, s_2, 4, g_2), (m_8, s_8, 4, g_8)]
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
  lowerDagV5 (kn_cons lb_6 (kn_cons lb_19 (kn_cons lb_2 (kn_cons lb_8 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xaaaaaaaa00000000
def s_33 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_33 : Nat := 0x2022200000000
def ep_33 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5050505050505050
def s_34 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_34 : Nat := 0x10105010101050
def ep_34 : Nat := 0x1000000000001040000000400010004000000040000000000000000000101000101010000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x5555555500000000
def s_35 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_35 : Nat := 0x115155500000000
def ep_35 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_20, s_20, 4, g_20), (m_3, s_3, 4, g_3), (m_11, s_11, 4, g_11)]
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
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_20 (kn_cons lb_3 (kn_cons lb_11 (kn_nil))))) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x3030303030303030
def s_36 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_36 : Nat := 0x10103010101030
def ep_36 : Nat := 0x1000000000001020000000200010002000000020000000000000000000000000000000000010100010101000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xcccc0000cccc
def s_37 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_37 : Nat := 0x444000004cc
def ep_37 : Nat := 0x88000000000000000000000040000000c8000004000000040000000000000000000000044400000400
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
def cur_37 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_37 : Nat → Nat := fun _ => 0
def f_37 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_37 : Nat → Bool := dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 1 (dagTraceF m_37 s_37 3 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 1 bds_37 (dagTraceF m_37 s_37 3 f_37) (cur_37 0) (nh_37 0) s_37 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37 : treeBlockF 0 1 ch_37 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 1 → ch_37 i = true := fun _ h1 h2 => treeBlockF_at nb_37 h1 h2
theorem lb_37 : LowerBin m_37 s_37 g_37 4 :=
  lowerDagV5 (kn_nil) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xaaaa0000aaaa0000
def s_38 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_38 : Nat := 0x20000020a0000
def ep_38 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x1070000010f0
def ep_39 : Nat := 0x80000000000000000000000060000000e0000000000000000000001020000010000000104000001000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xcccc0000cccc0000
def s_40 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_40 : Nat := 0x40000040c0000
def ep_40 : Nat := 0x40800000000000000000000000400000008000000040000040c000000000000000000000004000004000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xaaaa0000aaaa
def s_41 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_41 : Nat := 0x222000002aa
def ep_41 : Nat := 0x88000000000000000000000020000000a8000002000000020000000222000002000000000000000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := []
def cur_41 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_41 : Nat → Nat := fun _ => 0
def f_41 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_41 : Nat → Bool := dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 1 (dagTraceF m_41 s_41 3 f_41) cur_41 nh_41
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 1 bds_41 (dagTraceF m_41 s_41 3 f_41) (cur_41 0) (nh_41 0) s_41 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41 : treeBlockF 0 1 ch_41 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 1 → ch_41 i = true := fun _ h1 h2 => treeBlockF_at nb_41 h1 h2
theorem lb_41 : LowerBin m_41 s_41 g_41 4 :=
  lowerDagV5 (kn_nil) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf000f000f000f00
def s_42 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_42 : Nat := 0x100070007000700
def ep_42 : Nat := 0x600000000000600000000000000000000000000000000000000000001000200020002000100040004000400
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xffff0000
def s_43 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_43 : Nat := 0x171f0000
def ep_43 : Nat := 0x8000000000000060e000000000000121000000000000014100000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff
def s_44 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_44 : Nat := 0x17ff
def ep_44 : Nat := 0xe8000000000000060000000000000012000000000000001400
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xff00ff00
def s_45 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_45 : Nat := 0x17001700
def ep_45 : Nat := 0x600060000000000120012000000000014001400
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x4 0x0 6 63 3 7
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 3 f_45) (cur_45 0) (nh_45 0) s_45 3 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 3 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 4 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xcccccccc
def s_46 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_46 : Nat := 0x40c04cc
def ep_46 : Nat := 0xc000000000000800c800000000040c040000000000000000000000000004000400
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

def m_47 : Nat := 0xaaaaaaaa
def s_47 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_47 : Nat := 0x20a02aa
def ep_47 : Nat := 0xa000000000000800a800000000020a020000000000020002000000000000000000
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

def m_48 : Nat := 0xff000000ff000000
def s_48 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_48 : Nat := 0x100000017000000
def ep_48 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_9, s_9, 4, g_9), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13)]
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_48_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_48 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_48_1 (Nat.sub p 32)) (cc_48_0 p) (Nat.blt p 32)
def hc_48_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_48_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_48 : Nat → Nat := fun p => Bool.rec (hc_48_1 (Nat.sub p 32)) (hc_48_0 p) (Nat.blt p 32)
def f_48 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 43 bds_48 (dagTraceF m_48 s_48 6 f_48) (cur_48 0) (nh_48 0) s_48 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 ch_48 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 43 ch_48 = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 43 → ch_48 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 43 → ch_48 i = true := nj_48_1
theorem lb_48 : LowerBin m_48 s_48 g_48 7 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_9 (kn_cons lb_12 (kn_cons lb_13 (kn_nil))))) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xff000000ff0000
def s_49 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_49 : Nat := 0x170000001f0000
def ep_49 : Nat := 0x800000000000000000000000000000000000000060000000e000000120000001000000014000000100000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xf000f000f000f0
def s_50 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_50 : Nat := 0x100070001000f0
def ep_50 : Nat := 0x8000000060000000e00000000000000000000000000000000000100020001000000010004000100000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xf0f00000f0f0000
def s_51 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_51 : Nat := 0x1070000070f0000
def ep_51 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_14, s_14, 4, g_14), (m_15, s_15, 4, g_15), (m_17, s_17, 4, g_17)]
def cc_51_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_51_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_51 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_51_1 (Nat.sub p 32)) (cc_51_0 p) (Nat.blt p 32)
def hc_51_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_51_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_51 : Nat → Nat := fun p => Bool.rec (hc_51_1 (Nat.sub p 32)) (hc_51_0 p) (Nat.blt p 32)
def f_51 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 43 (dagTraceF m_51 s_51 6 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 43 bds_51 (dagTraceF m_51 s_51 6 f_51) (cur_51 0) (nh_51 0) s_51 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 ch_51 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 43 ch_51 = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 43 → ch_51 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 43 → ch_51 i = true := nj_51_1
theorem lb_51 : LowerBin m_51 s_51 g_51 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_14 (kn_cons lb_15 (kn_cons lb_17 (kn_nil))))) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x2222222222222222
def s_52 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_52 : Nat := 0x2022202020222
def ep_52 : Nat := 0x200000000000220000000200002002000000020000202000202020000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xa0a0a0a0a0a0a0a
def s_53 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_53 : Nat := 0x20202020a020a
def ep_53 : Nat := 0x208000800000200000000000002000000080008000000000000000000020202020002000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x4488448844884488
def s_54 : List Nat := [0x88008800880088, 0x408040804080408, 0x448800004488, 0x44884488]
def g_54 : Nat := 0x40004080488
def ep_54 : Nat := 0x408008800000400000000800000000000000000000004000408040000000000000000000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14a59080f 4 15 2 3 9 511 11 2047
def nh_54 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0x329c840f 1 9
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 3 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 3 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 3 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 3 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xaaaaaaaaaaaaaaaa
def s_55 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_55 : Nat := 0x20222020a02aa
def ep_55 : Nat := 0x208008800000220000000a000020020000800a800020200020a020000020222020002000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 5, g_38), (m_17, s_17, 4, g_17), (m_33, s_33, 5, g_33), (m_47, s_47, 4, g_47), (m_8, s_8, 4, g_8), (m_41, s_41, 4, g_41), (m_24, s_24, 5, g_24), (m_22, s_22, 5, g_22)]
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x886208821178de0781c26c5b06c1a15cd705c15254141501314c13044910405003c4f03c0d207001 0x38091c682f45175273609196bcc352509228d0968a4aa5e4c9222925048a725e31a9148e4946a3a4e15a1068e824650b437d27b490d747e92333ca79a4bcb24e403f18178809c102e001f 10 1023 4 15 11 2047 17 131071
def cc_55_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x38e15402 0x7a515a41623d8e398a3583496341 6 63 3 7 10 1023 16 65535
def cur_55 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_55_1 (Nat.sub p 32)) (cc_55_0 p) (Nat.blt p 32)
def hc_55_0 : Nat → Nat := unpackHintV5 0xfa867d403e50be796da33ec21f61018f43c3c7e1e030a0b7e8daba7d5c029d2329ca94c040349fa0edb446d80350395b9aad80402d9f21cac9a4f0e27800955000940000 0x2f76e799e19e6739ee79abce758b2867a98e8673af5baf554401c3af73dd7a2bd5b9cef5ea0a0f41c38f71c0aab585ce1c15838741ceb5505881758b070e170d673aa80ac58171c3963738ce3618d121add94701c671a8e862c1c3aae3874316338ce35a583218e1d57bd706719d546315910c70105d3a73a871100f1e5a88 17 131071 7 127
def hc_55_1 : Nat → Nat := unpackHintV5 0x6a00b53ec54d6c3805b 0x4f7bac1c9d6ea9cebc1510e761c3859e6a73dcf339d62c39c70ea 15 32767 7 127
def nh_55 : Nat → Nat := fun p => Bool.rec (hc_55_1 (Nat.sub p 32)) (hc_55_0 p) (Nat.blt p 32)
def f_55 : Nat → Nat × Nat := unpackForestF 0x891cc48d4168703490527b7145b49ce3416c120290d86bcc352051fa714934bca3424c92028cd0492824504a79c978125e63520493928e4946a083f1d27020bc56840827091d048c8102e001f 6 11
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 3 7 bds_55 36 (dagTraceF m_55 s_55 7 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 3 7 36 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) (nh_55 0) s_55 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 36 ch_55 = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 36 → ch_55 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 36 → ch_55 i = true := nj_55_1
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV5 (kn_cons lb_38 (kn_cons lb_17 (kn_cons lb_33 (kn_cons lb_47 (kn_cons lb_8 (kn_cons lb_41 (kn_cons lb_24 (kn_cons lb_22 (kn_nil))))))))) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x5555555555555555
def s_56 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_56 : Nat := 0x115155515151555
def ep_56 : Nat := 0x1400000000001440000000400014004000000040010404000404040001101000101010000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) (nh_56 0) s_56 7 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 7 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV5 (kn_cons lb_35 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xf0f0f0f0f0f0f0f0
def s_57 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_57 : Nat := 0x101070101010f0
def ep_57 : Nat := 0x1000008000001060000000e000100060000000e0000000000000000000101020101010000010104010101000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 7, g_30)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) (nh_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV5 (kn_cons lb_30 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x3333333333333333
def s_58 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_58 : Nat := 0x113133313131333
def ep_58 : Nat := 0x1200000000001220000000200012002000000020010202000202020000000000000000000110100010101000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_32 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xcccccccccccccccc
def s_59 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_59 : Nat := 0x40444040c04cc
def ep_59 : Nat := 0x408008800000440000000c000040040000800c800040400040c040000000000000000000004044404000400
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 5, g_31), (m_15, s_15, 4, g_15), (m_40, s_40, 5, g_40), (m_46, s_46, 4, g_46), (m_11, s_11, 4, g_11), (m_37, s_37, 4, g_37), (m_21, s_21, 5, g_21), (m_54, s_54, 5, g_54)]
def cc_59_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x886208821178de0781c26c5b06c1a15cd705c15254141501314c13044910405003c4f03c0d207001 0x38091c682f45175273609196bcc352509228d0968a4aa5e4c9222925048a725e31a9148e4946a3a4e15a1068e824650b437d27b490d747e92333ca79a4bcb24e403f18178809c102e001f 10 1023 4 15 11 2047 17 131071
def cc_59_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x38e15402 0x7a515a41623d8e398a3583496341 6 63 3 7 10 1023 16 65535
def cur_59 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_59_1 (Nat.sub p 32)) (cc_59_0 p) (Nat.blt p 32)
def hc_59_0 : Nat → Nat := unpackHintV5 0xfa867d403e50be796da33ec21f61018f43c3c7e1e030a0b7e8daba7d5c029d2329ca94c040349fa0edb446d80350395b9aad80402d9f21cac9a4f0e27800955000940000 0x2f76e799c19e6739ee79abce75ab4067098c0673af5baf555551832f73dd7aabd5b9cef5eaaaaf51830f718aaab5adce9d55a30601ceb5555aab75ab460c560d673aaaaad5ab718316b738ce3018d54185d10621c671a8c06ad18302e3060356338ce3505a3418c1817b9746719d546355a00c62205d3a73aa75554e1c1010 17 131071 7 127
def hc_59_1 : Nat → Nat := unpackHintV5 0x6a00b53ec54d6c3805b 0x4f7bad189d6ea9cebd5554e70183159e6a73dcf339d6ad39c60c0 15 32767 7 127
def nh_59 : Nat → Nat := fun p => Bool.rec (hc_59_1 (Nat.sub p 32)) (hc_59_0 p) (Nat.blt p 32)
def f_59 : Nat → Nat × Nat := unpackForestF 0x891cc48d4168703490527b7145b49ce3416c120290d86bcc352051fa714934bca3424c92028cd0492824504a79c978125e63520493928e4946a083f1d27020bc56840827091d048c8102e001f 6 11
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 3 7 bds_59 36 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 3 7 36 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 32 ch_59 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_1 : treeBlockF 32 36 ch_59 = true := by decide +kernel
theorem nj_59_1 : ∀ i, 0 ≤ i → i < 36 → ch_59 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_59_1 h1 h2)
theorem nc_59 : ∀ i, 0 ≤ i → i < 36 → ch_59 i = true := nj_59_1
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_31 (kn_cons lb_15 (kn_cons lb_40 (kn_cons lb_46 (kn_cons lb_11 (kn_cons lb_37 (kn_cons lb_21 (kn_cons lb_54 (kn_nil))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xf0f0f0f0f0f0f0f
def s_60 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_60 : Nat := 0x1070707070f070f
def ep_60 : Nat := 0x608000800000600000000000006000000080008000000000000000001020202020002000104040404000400
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 7, g_51)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_51 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xffffffff
def s_61 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_61 : Nat := 0x171f17ff
def ep_61 : Nat := 0xe000000000000800e800000000060e060000000000121012000000000014101400
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 5, g_43), (m_45, s_45, 4, g_45), (m_9, s_9, 4, g_9), (m_46, s_46, 4, g_46), (m_47, s_47, 4, g_47), (m_44, s_44, 5, g_44)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0x408101cb870c4681 0xad71458ed1f24b891da3b28dc01f 7 127 3 7 11 2047 14 16383
def nh_61 : Nat → Nat := unpackHintV5 0x41047814f001c04330a6600bc2002f0000 0xfcb3ff2dfdccddcce666664000002c100 15 32767 7 127
def f_61 : Nat → Nat × Nat := unpackForestF 0x2d1ca4bad70a4728ed45828dc01f 3 11
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 2 3 bds_61 8 (dagTraceF m_61 s_61 6 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 2 3 8 bds_61 (dagTraceF m_61 s_61 6 f_61) (cur_61 0) (nh_61 0) s_61 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 8 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 8 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 7 :=
  lowerDagV5 (kn_cons lb_43 (kn_cons lb_45 (kn_cons lb_9 (kn_cons lb_46 (kn_cons lb_47 (kn_cons lb_44 (kn_nil))))))) rc_61 nc_61 (by decide +kernel)

def g_62 : Nat := 0x1171777171f17ff
def ep_62 : Nat := 0x1608008800001660000000e000160060000800e801060600060e060001121222121012000114144414101400
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28), (m_48, s_48, 7, g_48), (m_60, s_60, 8, g_60), (m_58, s_58, 8, g_58), (m_59, s_59, 8, g_59), (m_57, s_57, 8, g_57), (m_56, s_56, 8, g_56), (m_55, s_55, 8, g_55), (m_1, s_1, 4, g_1), (m_32, s_32, 7, g_32), (m_35, s_35, 7, g_35), (m_51, s_51, 7, g_51), (m_27, s_27, 7, g_27), (m_49, s_49, 5, g_49), (m_30, s_30, 7, g_30), (m_61, s_61, 7, g_61), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13), (m_50, s_50, 5, g_50), (m_42, s_42, 5, g_42), (m_39, s_39, 5, g_39), (m_41, s_41, 4, g_41), (m_29, s_29, 5, g_29), (m_0, s_0, 4, g_0), (m_40, s_40, 5, g_40), (m_38, s_38, 5, g_38), (m_53, s_53, 5, g_53), (m_34, s_34, 5, g_34), (m_36, s_36, 5, g_36), (m_6, s_6, 4, g_6), (m_5, s_5, 4, g_5), (m_52, s_52, 5, g_52)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc40600af837c0bc0de02d09680ae1d702a07500a60d10a881440a00ce0a7013809c0481a4012008c146023011027a3bd000f8001 0x1f4a80f154076b181c5181a6aa09236064aa01a518172c8061460142b02a5500b28c0407604dac02558c0a28c07c500422c01c9540dac60626f02d2f814498070cc020560212780e0d8054de02036062b182cdbc146be08a36024a300c198030ad5dc5fada2dd6315ea88a75235fa7dadd3ad5e956a748b4fa31a5d14d1e826873925f99d2dcb495e4b4a71ca4f8b925c3e91e10486fe23f7c51dbba8ddc6466d995f6c8adb4455d9f2a6c514f624a5aee51d74286b413f5709da324dd0e2667c12f3949598849cab2465185f2882d91415c890a64084f200258d011c670862483f1201d8860dc400661c02f0d41584209c200460e01f06c0d80405c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c21284201801f170dc0701a2681735855154141501314c1124410134cd0304b12c0a12440900000 0x7ed53e4a9e264e92a7b58fb8dfcc5fdc166c09344a95947489ac615a60ed8264b92a595a2a4b95563af39d2970a2693c7c99a7c95a236df9d63ca37e317ef2df695fa0a3a24d650cd1056 10 1023 4 15 11 2047 17 131071
def cc_62_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8d23088620846107c9e1781d1741d0741c1521314c13048520390681806014450140230802000800 0x30563be536714598496eb64b6d52cc58a4936b562ad5ca9563b158ebc63ab14ea26fa697e8a4d9c91659269a9126d639f9ce7344989125944cb58f1a6fc297ef235b85bed15fa04d651278e95635638a9be225f840b20824 10 1023 4 15 11 2047 18 262143
def cc_62_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xac2749c2348c2308c1f47c1f0749c1701a2681a06816458142501312689024054140320c01200400 0x3fd68fc997d25d4609be568f2973815d0a05bd36ff29bb514df0517b36fead8fa460e55a3715ce09bf524dde917716ed91802014d4db3eb6ff69bfba5de68df896fda5775937d249d10260605b3354c08d6c1359e49f2364a84d71354a64d66925 10 1023 4 15 11 2047 18 262143
def cc_62_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9826089220881e4781e0709b16c1b05d1705c152541324c12122880200711c0701c0701c01604001 0x279a7cd24e8c2bb3a5566e3e4d27c932fa1005a61afcbb53968e118976512ac9a4f9029d231f240be474700702918df27da7ce26d9949f2a8de48b6c794f8d26f1649c941303016884cb0edbe1937c2a37842df064de089392026 10 1023 4 15 11 2047 19 524287
def cc_62_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xb04f647208cbf1f0f878bc1d2cc6432190ba5c2c5286630164b0582c160b02e140844004 0xbcac17e9f2f8be5b14caf28976552d4a657144bbac9799d2e8aa5a14cad2896b142d6b25c45fb78b76d15ed229d7450b02d95d592ca2fd8c5baf8af5b14f0ab7e056bbdacf7358ecca656144aa48b52d3ea127d3a37a629f4a4de909393826a18f93c9f6812293026 9 511 3 7 11 2047 19 524287
def cc_62_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc6f0bc2f0a1e80a026298260982338c23084a108421078de0781d1741d06c9651fc7010c4004c01 0xc828dbd9d375aa6e254db2a98c5193c2789035d9689b051359a26aa44d4289a4d1344a267b44ce4899a51322b064674c78b1975bf2ab5e4d67c6ac6140978eb7f0d6bdfacfb558f5e35e9c63d08b79914f14a35206f8b0cf0417da42ba504f1106b86592e0a659144c12a96e532c4a258134 10 1023 4 15 11 2047 19 524287
def cc_62_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0ac0ac6b0ac292862107c9f0749d068d916058051140501404c5304c112350761c052140320c003 0x803447fa447ea447db447d2448656f8556b83d6781d6380c6b7f4637e45b7cc537b964760147a9547581478d607997c75014748147401478e7478254779547381474c5074d64741447645f75c5b7545773c537b56f7a56b79567775637681873014723646594671354651466f5607037c64946 10 1023 4 15 11 2047 20 1048575
def cc_62_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xb01602c05619c8ac95028150098530222402800f09a2248480809001c2380700831002004002304000400000 0x8e5638fd638f26f8ea5f8da45acd6fab56ba7d67a3563a226f9da679ca5f982579424d90a3d629265286f468674185f358578d04d14027048158c1648b154895608a17c8895488d6489674881548bd6f8ad6b89d6787d6386a6485a548356084a7c8417c8367482b548225481244 11 2047 5 31 11 2047 20 1048575
def cc_62_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0ce63911883d1d2e16cb45a0c960a9132984c2452082402009e48241048040190502002 0x9fb5c9f464a1b5fa0b5ba03579eb539e4709d45894a4c8e84d058159bb789a3649bc7c99b609a36c99c749c36f9b36b9ab679936398c6096560966741502597d6f9756b96d6795d639526e94a5e14825925609267491c5893d6f9356b92d6791563902558e245 9 511 3 7 11 2047 20 1048575
def cc_62_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf83b3dd370dc325c8320b56c1b02a29ce709c20780200789a45915148d2022880110310841100400 0xb0674afa54af154b356fb256bb0d67aed63adc68ad26597a4d93a3d65926ac458aba559724d9323d65126a7670a6e70aa14ca6560aaa3fa9a37a5d60a9470a8a7d96a4d92a3da817c64926a723fa6a37a64609624d9223d6412691a4d63926160270801507815a4c509004d07015a5e74a5458a425595a4d9123da3954631268f84d1582706815a2c689524c8f04d06015a13689fb54a146c9f350 10 1023 4 15 11 2047 20 1048575
def cc_62_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xf0f47a1d0d96c36138984c225108840600f1783c1c2e070344b0502090062301800c0000 0xbfd70bda3ebe36cbda6cc336bc1363c026fbf267bea5dbd23fbc96fbc167bb018ba814b8560b8674b697cb516cb9d6fb956bb8d67b7d63b726fb6267b5a5fb4a57b3964b2954b0560b1a7cb117c 9 511 4 15 11 2047 20 1048575
def cc_62_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x80200801d3741d06c9b06499064172585605455054150541321b46018060108401004004c1000400 0xcf354cea35ce134cd354cca35cbc64c6845cac7cca17c17025c8b54c6a6fc624dcdb6bcc363cb26fc9a67c9245c823fc796fc71675306f47867c58452d03f16827c436cc3a35c2b6cc2235c1934c0d68 10 1023 4 15 11 2047 20 1048575
def cc_62_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xa068098a6098242902318c2308494d501405012248120480f3384e0344d0304c0300a20a02008002 0x18025dec64da865ddd68dd15cdc364db25ddaa4fe134bdfb43df255de24fdca47dba3fc794fbc947da0554204f388472e03f17827d8b7cd8235d737cd6a35d6134d223ed4c7cd3d70d2b7cd227cd7b4bd5b43d526dd424fd3247d1a3fc714fbc147d0818d0014 10 1023 4 15 11 2047 20 1048575
def cc_62_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xd869da4263982338c1f470dc06c5745c170585605451444110405003c4b4158501405008c2008002 0xefd63f7d6ff6d6bf5d67f2563f1a6ff1267f0a5ff02575386f4a8674285f39857ef04dee264e9128e6124ed254e8928e5924eb560ec27ce8128e5124eaa54e7928e4924ead64eb674ea254e7128e4124e7c50e7d64e945fe8c5be8457e7453e4c50e4d64e645fe5c5be5457e4453edd6fecd6bebd67e9d63e6928e3924e2b64e2235e1934e0b64e0235 10 1023 4 15 11 2047 20 1048575
def cc_62_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xa46545f97058560545504c9304c13040cc4300b12c0a1244721c0611806018051014000000000000 0x1ffce90156f806b5c0159dfeac70756f832b5c1559e07ac70326f81533c0897e034aedb96f68cb3b2057d7a2ae909457f49abf6991f94a8fad607dd3e3eb9d1f46a8f9a547eab7bf15adf6acef95637c2343dd161eaac0f4d607b2383d5181e68a0f4e747a22c3ce951e50aaef84d 10 1023 4 15 11 2047 21 2097151
def cc_62_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c42a10fa7c3a9d0da6c361b0d86c2f11c88399c0b6581e0a8500c040201008040200200 0x43c992150490e244850124349f2130490c2448481242ad7e146b709b57849a9c3b1be1b8d70cc6785e31c2c0a21104907b6449ca2c044d60d6a8931458049ac135820b6f8929458009aa48515ff26b04e74821aa244515fe26affd60 9 511 3 7 11 2047 21 2097151
def cc_62_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xd81a87506a0cc504e003e17c0f05e03a1740e05c0342588b0150aa054098930241480901201e33c0780d100d 0x1502b1e36f8eca6c90dbe456d721b67901b1c7e9be3e4cf0223f7851bb785bda82cf1e9455ac9fa724dca80de4c8678e8228c20fc4406e0a0178e13246c912344f91923e8c5a2460912378df1ac6b8ce33c5f18e2dad115b6c8a89ac515c2266d912a348909ab745b96a27d1636f8a5b5c4ed9e236c71126f88533c068fde046edc96f698b3c405756927e98137 11 2047 5 31 11 2047 21 2097151
def cc_62_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0a4e726b5a0609805896050940489204812048120390862008014c50140320c0210802000800 0x97dbe4bc8d25d26aca14e5b49f4cad3e6269730347971a1c7c93e2148f02a3f7891bcb65b59329ebf1475b09fa764de594a92802495d2249e092554d92702494d2249a0925069f27b4b939a3c9ad0e588bf2b45b9522bca514e510512602492a324921963c08b23b549189ac891f2426a920935 10 1023 4 15 11 2047 21 2097151
def cc_62_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xa41482714e0983302604828c3182304223a6700d09a0302600b0960282500810841001843006004408000800 0x13f3649f49acf75a2796c93c13505c0acead3e742bb3fb4f9f1a5cf4d1e776871fa4f88923c0c8fde346f3b155658a7b0051d6e27ea21379cc2a90c13c7b08e3183f1141b82c05e714a937a449b5364d68fa6a68934a449c22fcdd16e6c8af3445399a3e4c8df26326b30d70 11 2047 5 31 11 2047 21 2097151
def cc_62_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xca181700600be37c2ad5509ed16a19430824de9b8334660b591d2303ca780f01d13a04e8980d60740c018003 0x14f26d90d27c6692e2748f0ca43a6c1a538d6e9a6a718a5a8952b33257d842af4c93d3589aa004b4d524b20a5f8912bd2e8f4d646ac19563509348097e2f4b711a5785d29d308d5982bec1157a589a9fc4bcd324e5506f28033d009be9349b3fa6f9c135cca99e584c74a2452a43793e19e9208a1c82f0c413b885bdb02cf4813d3489acfa9be634cf4723d3491ab865b8d124d3e26f9b935cc499e564c747a35708b7b5e59e8d26a7e12f34093cf49be6c4d73026795131d169768806944b6ba1db1cd49aa5e4cce016f6b4b3d0c4f4cf26a7d92d33892cf09be5d4cf4223d33d1ab58598cd24d3ba6f9a135cb899e524c742a356fcb7b5659e8326a7c92f33093d03192750cb40045 11 2047 4 15 11 2047 21 2097151
def cc_62_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x951ca824c50ae850410e0810027273901bc6de06932d3d3989c0435a180ed07603b01c0c8ac4022000f08514280102080028c00a 0xafcae9c85555a26f5ea5d3912ad7c9560e47efd23b7bd1bbb68cebc2aab993f5989dab24dd172668612f3d8959c649cc22475d14d388a2aae4deb849a71245ae522c188fdf8476f6a3776519d6e5157227eb213b5589ba2a4cd0a25e7a12b3849398048ce02db5a9655449b9c09b6b34cab193a5409b2104b8bf24558450ad136c148fdf6476f5a3775d19d645b57127eb093b53c9ba264cd0725e7912b37c9397a48e0947efaa3b7a51bbac8cd7027eb013b52c9ba244cd0625e7892b3789397848df4474f3a36abca69ba5154826e8292d3709288e0dc3f05a1a0250680bd5a934dd48aaf93a51c9b1e04a8db24c0f81d0640ad56935e546f5514dac2b255c9160747ef923b7911bba68ceac28ab793f5749da8c4dd0f2668192f3b8959b449cb9247548451941f88c0dc3d05e198270740f83005c8809e3f047a992ec9293ea74ab2424f8dd25c5891e1d4875285521c278fa11c3b05e19027674afb0e55ea327a6c9359192fc5495ea147a6ca35670af1b049a454bf1aa5b8a52bc3694ea246acd95f618abd404d50125e6b927 13 8191 5 31 11 2047 21 2097151
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec ([]) (cc_62_21 (Nat.sub p 672)) (Nat.blt p 704)) (cc_62_20 (Nat.sub p 640)) (Nat.blt p 672)) (Bool.rec (Bool.rec (cc_62_19 (Nat.sub p 608)) (cc_62_18 (Nat.sub p 576)) (Nat.blt p 608)) (cc_62_17 (Nat.sub p 544)) (Nat.blt p 576)) (Nat.blt p 640)) (Bool.rec (Bool.rec (Bool.rec (cc_62_16 (Nat.sub p 512)) (cc_62_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_62_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (cc_62_13 (Nat.sub p 416)) (cc_62_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_62_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 448)) (Nat.blt p 544)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_62_10 (Nat.sub p 320)) (cc_62_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_62_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (cc_62_7 (Nat.sub p 224)) (cc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_62_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (cc_62_4 (Nat.sub p 128)) (cc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_62_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_62_1 (Nat.sub p 32)) (cc_62_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 352)
def hc_62_0 : Nat → Nat := unpackHintV5 0x8f614e87260f82752c7cf95f78113a7205836872656311585a3e3554dd584c0a354a5c6b43d5a23ddd7e3cac4c3c401b3b6c3537450a33f4d430a4d42bed2e2828f123d1161ef93618e1861489160fb136099986049940000126000000000000 0x1870603060001c3800131e3c987060c3a3918b472316aaaaaaaaaa00000000008c00000000000000000060c387063c19b060c1870e1c98f1e4c383061c3c1c5878387555555555500000000380008c10009803c00e00300381c000e0002c0804040000000000000003b80006cf9b467cfa3466cda35555550000004608004c01e007001802c080404000000000003b80006cd9b367cf9f3e6cd9b367d3e9b4da9d4680000000001f000d8002000770009803c00e0030058100809c00001aa1d585c2c9a1d0ea8c983c0e031585c0561700590888ac561700044e000f01ab0b8008800077061c180c00e0131e3c987060c3978b978b9347a1d069752ea5d2e84c000e0007000002000b8003c000605c003b80080000c1870e0c783360c1830e1c3931e3c987060c387838b0f070e4d1e8741a1c3a8755ea342600f003800c00e0700038cc0016040200000000001c00004e000000f000180000719800080000007740263c7932e5cb97263c7932f172f17466cdaf150105555098004c0000000004001e05c003b801700040005498f1e4c983261c983261c98f1e4c9c4c593898b466cdaf57ba3d51eaaaa84c01e013098004c660007001802c080404000000260000002000000f0000263300000040000003b830e0c3972e5cba0233e7d787060c3978b978baa8a8082a8001c000e0000000200170001817000ee002000030e0c387261c3871e1c3aa8cf9f5e1c1830e1e0e2c3c1c3aaabdd06a835542600f003800c00e0700038cc0016040202000000000700001000000000600001c6600020000001dc18f1e0c383061c5d0b40258000030e3c19b060c38785c1c98f3e3c793264c383360c1870e1c3870e1d9872e5c3870e2e85aa8755a0001c2e12d3880f0180070b8886cf9b467cfaf466cdaf2e4cf8f2e3d9932e1cd832e0d9872e2d1c5e5e2d555554000000004e0800033001980020800002f940960f01cb03ba01dc57dd85cc170565cee830e3c19b060c387aa83d550785d5007555f00070b9004004b0780c00385c80ee80a0c3830f13b7d55502f71e8f6555008020010780130b81780ee804c38f0eb07b5d55502f706836555008020010b80c00385c80ee806cf9b97555555540172e5cb972e5cbd5545c5d5545c5aaaab2aaaaaa00017000b84000020801b3e6eaaaaaaa804fa9b65965ed200004000100000000000100077001000001831e1dd871e1c7871e1c787585c1c7aaaf7068347800f03b8008f03b80070b81740007831e3c18f1e3c78faaa1f77aaaaaaaaaa007a8f51e8f4ba5d9658bb4800000000000000017001e0c78f063c78f1e3c78f1e3c78f1e3d19b36bc7a8f51e8f536af51a0f00001e001dc000001980f000ee00000009c00051e0c19306dc183060c183060c2170b5ee3d1e83550006000c0ee2004c2e0303b85d001831e0c183060c18302aaaa81ddeaaaaaaa802e9741a835068365962ed200000000000000005c060c783060c183060c0467cfaf060c183060c1834fa0d41a8341abd468000c00001800770000660000c003b80000270000d9f368cf9f5e8cd9b5e9f536af51a13007801c00600b0201000000000138000000000020000001dcd9b366cf9f3e7cd9b366d5555540000000000000000000ee13007801c00600b0201010000 24 16777215 10 1023
def hc_62_1 : Nat → Nat := unpackHintV5 0xb9ad7bb0ba3daba944a511a6a001449969a694893891b8b48e18e8889d5f7fde3072276e68ca575f6e5759398d4e2ec347f98d3ceec33bf43e396ca238504732f5572aca0b29b84425d4f91d8e121c7c441898f91052120939c604912a000124 0x187068306aaa1c3aaa931e3c987060c3cf978b9f2f16aaaaa0a8aa8888a0a088884c1e070181c381b2e06c3622a02203061c3831e0cd83060c3870e4c78f261c1830e1e0e2c3c1c3aaaaaaaa1d55549aa3d50ea83543a1d550eaaa2d59404444505044445050260f0380c0e1c03970361b04eea0a6c11058b555263c793360e187360e1876a55a5aa5550545555445050444444260f280f970361b22115011217131e3c9d41e0750fbbd55554aaaaaaaaaa93547ab32ab2aa87541ab2b28088a0a0888888a0a04c1e5045c0d86c8813ba829f044061c187864cf8f3e3e1930e1d556a9a956955555415155111141411110d86c0e03280d97088454044061c18789d43ea0f5540eef5552aaaaaaaaaa4d51ea87541ab32ab2aacaca022222828222228281b0d81c065045c2204eea0a6c110d9f367cfaf366d7aaaaaaa4d51ea87541aa2d59404444444450503e1f0d86c4e2704eea0a9c110d9b366cf9f3e7cd9b366d555554000000000000000000d9b366cf9f3e7cd9b366cfa7d369b53a9d00000000003e001b00040000d9b366cf9f3e7cd9b366cfa7d369b53a9d00000000003e001b0004ee000013007801c00600b020138000000030e0c38347930e830e4c78f261c1830ead5ab564c98f1e4c9870e0c1870e1c38070e1c13a793c9c983c0e03158ac562b13a713ab0983c78f0380c1830dab00e1b3b9b0d8a8003061c3831e0cd83060c3870e4c78f261c1830e1e0e2c3c1c393263c78f1e4c9870e0c183061c3870e1c3870e9d3870e5d9870e1c3a7169e4f27164d1e8741a1c3a1d43874ea9d4e804c1e070181c38072e0bc13a704e0884c1e3c781c060c181c381c03872ecc0d86c55404ee010b898f1e4ea0f03a87ddeaaaaa264c78f1e3c993aaa4e9e8bb3aa4e1cd83360d387aaaa268f6964ea9d36cc804c1e5045c1186c88468c11a3044260f1e3ca20a2ecc0d87cd910aa809dc00187061e2750fa83d5503bbd5549c99f1e7c7a7261c383060c1870f5549d3d17675555549d3e8741b4b2759901187c0e032822e1108d1823460886c366c0e03060ca20a2ecc22155013b8020172e5cb931e3c9972e5cb931e3c9a3366d7932600013263c264cb972e5cb972e5c000000000002e001dc0078005c0010000263c793260c987260c987263c7932713164e262d19b36bc9931e3c78f264c993264c9932e9c9932ecc993264cb872e0cb832e1cb8b2f178b8b5555549aaaaaa001dc1e00f00000000000007800013198001700041003b80172e5cb830e0c3a0233e7d7972e5cb87060c3972e5cb870e000070e0c0e1cb972e5c0000000000000b817000ee000c001000187061c3930e1c38f0e1c0467cfaf0e0c1870f07161e0e1cb932e3cb8f2e4c387060c1830e1c3870e1c3872e9c3872ecc3870e1cb8b2f178b8b555555543aaaa00001dc0600300000000000b8000c000038cc00041003b80174e5d3ab4965cee6c793061e838b83a72e1d9d2755a17ee4b0bb33b9b172b2e1c38170bf7367cdd555172e5cb972e5cba017265cb97265c3972e5c39550014000000000000005c002e0000770b808006cf9ba87d44ea07507aaaa00b932e3cb8f2e4cb872e0cb832e1e8bb3aaaaa2e9eaaa955559555555500000082003b80005c0004002e0017086600000020801dc00001831e3d3a750468c01831f43e1f0f87c1e8783bbd50f47a8f1e3d3f7939787a3def29d082e234600f063c7831e3c78f1e3c78f1e3c78f1e6cdaf1e3d478f1ea3c78f1e3c78f4fdcb9b2e9cba72e9c78f51e8f7b8f47a9d36a753a00f0783c1e170b85c2e174e176622030600c1a74ea08d18b8783a07030740c1c03eef5503939781a0d4183069fbca741a0dee105c468c1831e0c183060c18300f9f5e0c183060c183065cf974e0c1a83060d4183060c183069fb974e5d3a74fa0c1a8341bdc1a0d4ea7402e170180c06030b85c2e9c2ecc44367cd9f3ebcd9b5e9c99f1e7c7a7269c39b066c1a70e9c5a793c9c5a74fa9d36a753a007c0d8bc13a704e0887c4e7c36273627138aa809dc00d9b366cf9f3e7cd9b366d55555400000000000000004ee00013007801c00600b0201000000061c180c00e0131e3c987060c3978b978baaaaaaaaa84c000e00170020010000000000000 24 16777215 10 1023
def hc_62_2 : Nat → Nat := unpackHintV5 0x9f49d199cd5f8f86928a095f7fc2927df07478855b74590b73683c6f3d0b6ac91d66551d65783760055d5aad5658c07b53a94652c4394e392349912a41a5fb3acdb6363526319528275e8e1e763a158e3a1031570db0a00a68d205354d00014d 0x1b3e6d5932e3cf8f2e4d5872e0cd832e1e170b85c2d424589d3ea74da2c58b162d9165c2e170b85c0b80b214e2170b85c2e178280590a70ba700058b0002e0cb872e0cb87263c793a0008582e170b2e5d4b975268f4ba5d16c80000000000000000000000000004c78f264c1930e4c1930f0b85d0b1742c5c2e162c98b162c78b162c98b262c58b162c98b162c58b161c583160c587009a3d264d499752e9745b22c5a8b2ea07707803c00000000000000000003b901000005c9971e5c797260c3830e0c180042e1740010303974ba5cba972ea1d068b6400000000000000000000000000187061c3930e1c38f0e1c085c2e0707a0e2e8387164c58b163c58b0e1c183060c3870e1c3870e1c58b0e1c5870e1c3805d2e8741a1c3a872ea2d9162d459750003b80c006000000000000000001dc8080000063c7830e0c1871602b55a004b000061c783360c1870e4c78f261c1830e1c3870f2c3972e1c387838b161e8380075facb400385c160b096000004c9931e3cb972e6cb8013261c1830e3c78f160174ba4d2e80b05800170000261700383263c187361c0b9f2e1c387060cb9700261c7870e1c183062c02e9743a5d0160b0002e00001c2e02830e0c3931e3c993264c9976e4cb97264c987060c3c2e1600bdc7a3d5500160b04000009871e1d498f1e4c383061c3870e1cbbb0e5cb870e1e1707005ee0d06aa800b0582000006c5c1d5970e170d9f370b85c2e165c9971e5c797265c397065c1970e2c58002aaa8aa5d00000000000000000000000b8000006cf9b2e4cf8f2e3c9970e6c197061e170b85c2c00013ea6d2ea5d45b200000b01600000000000000000001b1707174c3874ba2d96afd0b92fbf7367cdcb2e4cb8f2e3cb932e1cb832e0cb8785c2e170b500055554baa20000170000000000000000000d97562e4b817ee6cf9b2e5cb972e5cb9785c2e170b4055554580008b4500000b80077008100000000000000d9f372cb972e5cb972e5e170b85c2c001555516aaaa2d5555552eaabdd5400000000000000367cdc2e170b858b262c58b1e2c58b0e2c18b062c38093547aa1d506a8b56545a2d5516aaaaaaaaaaaa2d50000000200001600820077000003b9010000000006cf9b85c2e170b164c58b163c58b161c583160c58700f9f4e6cda71742c58b168b1687c0d82c8162c0582703e1f0d86c23bd0549c4e001b366cdd5551f3e7cf9b366cdd500000000000011dc0000002600f003800c08101380000000d418750f0f89c0e0f52b95d4be5f5404c9870e1c3a796a68b85c46423465c2e42e23b9b360c1870e0c783360c1830e1c3d43ea27503a83d541e5f550783d555541e175540131e3c987060c3870e1d0e1d97cd4d5130781c06070e01cb848c28221188c260f0380c0e1c0e01c39766142e808ee6c36002a4c78f264c1930e4c1930f50fa89d544e5f551389d40ea0f55555554023dee3c7a8f1e3d3a6d93ad2cc930784c98132e05c2e48c2822110983c264c099702e17285d011dd0b8000c3830e1c9870e1c7870ead43ea27503a83d541e5f550783d5555555009d3ea0dee0c1a83060e4eb4b325c2e070181c38072e1230a088442e170380c0e1c03970a174047742e001b3e6ea1f513a81d41eaaa803e7d39b369e5f353548c3e230d9230a08846230f87c361b285d011dd389c00366cd9b85c2e170b555555000000000000000000366cd9b85c2e170b3e7cf9f366cd9b1742c000000000000000000d9b366e170b85c2cf9f3e7cd9b366c5d0b0000000000000023b800004c01e007001802c1013800000000c38341aa1d5263c7930e0c1877ead5af49aaa1d559eaaca222222228a130781c060703606c3629b044 24 16777215 10 1023
def hc_62_3 : Nat → Nat := unpackHintV5 0xe23953d85679cfea1bc2ab50be710eb61a16b08166a889fea83415a79827a1219e97c25891c180868ecd822d187c756e7535d06f318169bd5d61ba015c795054121a4c25fb4689673e6a083187392a79c31ebeef17b1c30bf6ef05a594000169 0x2d45831e0c983060d583560c183860e183060c184cd5132749d06d170b88c06170b80c383019dcda7368e1703060c783060c9d5503a060ea8183060ea0703a021f77aaaaaaaa070baa263c793a9a418341830683060c1d51307941170068c018300603221188c260f2822e00c187060c0067788361b3601b1180c183060d060c1835060c0180c1931e3c983060c1b7978b6f2f160d1e8341a3c7a8306a9d4e930780c06172e05cb8170b8884c1e030181c38130e05c2e21b2e9c0363715060c18f060c193060c183064c183060c183260c983060c183060c183060c1804c78f264e262c9c4c58381830703160c183068f7b8f1ea3c78f060d3a8306835068353a9d260f09930265c018030600c06170b8884c1e132604cb803061c1830019dcb85c4365d3806c05d0307131e3c9d52b57172f5208fbbd555132729d060c18382e2311905c0e070d9b54183060c183060c183264c78f1e3cbf7060c18f1e0c183060d0183263c793264c993060c183565cbab260f0984c06030b85c2e170983c264c265c06030385c2e17000183060cb932e3cb8f2e4d400119f3ebc183060cbc5c5978b8b551500505500018005c00004000000000000000060c1832e4cf8f2e3d5935006034f9f5e0c18306ae2e2cbcac5a74fa9c1a0c1834183069d4e970b80c061702e05c2e22170b80c06070e05c38170b89b0b9b000f931e4cf8f4581c183060eaaa899f1e7c793a08aa59a4e9f41a0d99162d418352e170180c882e5c0b970442e170183201c4070e14086cba700d88c060c18f060c193060c18302a1f513aa81c0eaa07540ea0755555554aa74fa0d3a8306a0d06d0ba567b970b80d18030600c0645c2822e50885c2e03061c1830019de2e1411086cba700d88c060306000c1803060004c78f260c183065e2e2cbc5c59347a0d06972ea5cba974ba0000000000000000000000005c00000183063c183064c183060c193060c183060c983260c183060c183060c183060131e3c993898b2713160e060c1c0c583060c19347a4c9a932ea0cba8306a0d06974ba07707803c018000000000000000003006007700002e000283060c1931e3c993264c9972e4cbb7264c98042e170b85af71e8f554980003060000017265c7971e5c983060c183060008cf9f5e5e2e2cbc5c583060c1aaa5d51550000000000000000b8000000000000003060c183060c183064c98f1e3c797ee0c1831e3c183060c180131e3c993264c983060c1972e5cb9347a4d268341a5d2e974ba00000000000000c18306ec9971e7c7972600008cf9f5e0c183065e5e2d1c5c5a7d06834ba9755ea3400000600c0000000000000000000060c183aaa82e4cb8f2e3cb93a000a0002e9741a0d992e5d4b97500000000000000018000000000170000ee03060c783060c983060c18150fa89d540e075503aa07503aaaaaaaa00ba5d065d41835068362eb4b17690000000020800ee005c0001803003b800000001700000183060cb932e3cb8f2e4d400119f3ebc183060cbc5c5978b8b55154baaa0000170000000000000000000183063c183064c183060c0467cfaf0703060e062c183060d26a8f541aaa8341aaa0d506a8b5655555555555000000000000b820801dc000600c00ee000002330004000060c18f060c193060c18300f9f5e0e060c1c0c583060c19f3e9c18341830683060c1af4e9c3e030060c0180c5e09c0d86c060c383060033b9b0d86c366c03600c3830e7cf9f3e1c1830e7cf9f3e1c1830e9d3a74e000000000000033b80000004c01e00701604020270000000187061c183162c58b160c387060c1830e1e170b81c1e828384c78f261c1830f4d5a769ab4e8ba164c1e070194cb8532e02c84e530983c0e0303c1401ca8361b0001830e1c18f066c183061c38785c2e0707a0e1c58b83d070e2c98b162c78b161c383060c1870e1c3870e1c38b161c38b0e1c3870098f1e4c383061c3870e877e1d1742c58b168b16930781c06070e01cb80b2058b01609c0983c0e03038700e5c08ef4151b0d8002c5a8b162d360db87360db87263c793a0a1642e170b858b16a3c7a8b47a9d368b64b9702e5c0983c2e170590884e0a0260f0b85c1642170015263c793260c987260c98785c2e858ba162e170b164c58b163c58b164c593162c58b164c58b162c58b0e2c18b062c3808f7b8f1ea3c78f4e9b45b22c5a8b4ea4c1e132604cb8170b82c8162c05822130784c98132e05c2e11de82a42e003b267c79f1eec9830e0c38306a0c1876170ba0a0e40e0e9d3e8b06a0c1a8741a2d92e170b9702e5c0380c16422170b81e0a00e03039085c00061c1870e4c3870e3c38756170b81c1e838ba0e1c593162c58f162c387060c1830e1c3870e1c387162c387161c3870e0274fa837b8306a0c18316c8b16a2d3a970b81c06070e01cb80b2058b0160885c2e070181c38072e0477a0a90b8000c38f066c1830e1c98f1e4c383061c3870e1cb970ead5870e1e0e2c587a0e881c3a874ead162c58b0e172592c4e1c2e441b366cf9b965c9971e5c797265c397065c1970f0b85c2e16a000aaaaa000a217000b8005c008004000000000000000 24 16777215 10 1023
def hc_62_4 : Nat → Nat := unpackHintV5 0xe28d0edcf566d4fdfecc921bc43a16b6fb50b6a415b60827af919ea63258a0796e9c191896158190158088d5d07da2cd782d5d702a016ae95062821a5a95fb54f967501d37466a6d3987393046502556bc1d360815060c0d19fb0749740001d2 0x820c3830e3e1f2b95d45e2f507aa81ddea878f1e3c38794ea311905c261320b86cda8000f1e3c797065c397065c38f1e3c7978b8b2f17168cd9b5e2a00a0aaaa0f000b80000008000000000000000a03c1e8f1e3c79b065c39706ac38f1e3c7ab8b8b2f2b166cdaf1e8f1e3d1e3c7a74da9d3a9d1e0f0b81702e170b85c441e0f099302e4c0b85c2e1713e173e00070e01c0e1c187061c1830e8306a3c78f1eee5e2ddcbc587060c38f47a0c1a8f06a1d06a753a3c1e172e05cb8070185c2e220f0384c98070e01c06170b886cba700d8ec41e3c187061c1830e1c19707dc3870e1c38f0e0c1870e1c783061d51e3c78f565cbab0e0c1870e1c3871e0f0b85c0e030381c2e170781c26170380c0e1c0e5c2e170000060c387060c387061c1870e3c3870e1c3871e1c7870e1c3871e1c3871e1c3aa3e1e2c7c3c58f1e3c787060c387838b0f070e3c7a751e3d1ea3d1ea0dee0c1a83060d3a9d1e03c780f0781c06070e01cb8170b8883c7931e3c01e770e03038700e5c0b85c4365d3806c0d87061cd834584c78f1e3eaaaa822839b066c187a59a1e8f53a6d99162d478b51e0f0b85c882e5c0b970441e3c81e5c2e44132614087cba700f88c007831e1c7831e1c78f1e3eaa1f0faa87d50fa87d40ea0f55555554a8f4ea3c7a8f47a9d36d0ba567b8f4603c780f0785c2e45c2822e50883c7931e3c01e772e1722e1411087cba700f88c1e3c000b832e1cb832e1c78f1e3cbc5c5978b8b1e3c78f466cdaf4baa2aaaa00000000000001700000000000000000187061c7871e1cb872e1c3872e1db870e1d6170b85c1d557b8341a0f1e0700000000000078f1e3cb836e1cd832e1c78f1e3cbcbc5a38b8b466cdaf1e8f4ba9754dabd46800f01e00000000000000000000001c380001c18700060c078f1e3cbc5c5978b8b0e0c1871e8f4b9752e5d43a0d2e974000000000000000000000000b8000000c3830e0c1870e0cb83ee1c3870e1c787060c3870e3c1830e00f1e3c7972e5cb87060c3870e1c38f47a5d2e8741a1d0e974ba0000000000000003061c383061c3830e0c3871e1c3870e1c38f0e3c3870e1c38f0e1c38f0e1c01f0f163e1e2c78f1e3c383061c3c1c58783871e5d478f51e8f43a0d0e1d439752e9741e00000001dc06003000001e03c00ee00000000005c0001e3c78fa8aaa0002e1cb832e0cb87a0001e8f4ba5d992e5d4b97500000000000007800000000000170000ee003c18f0e3c18f0e3c78f1f550f87d543ea87d43ea07507aaaaaaaa0079751e3d47a3d2e9762eb4b17690000000020800ee005c0780f003b80000000001700001400078f1e3cb832e1cb832e1c78f1e3cbc5c5978b8b466cdaf154baaaaa001700000000000000000000001e0c7871e0c7871e3c78f1f0f163e1e2c78f1e3d19b36bd1eaaa3d1eaa8f547aa1d506a8b5655555555555000000000000b820801dc1e03c00ee00000002330004000007831e1c7831e1c78f1e3c7c3c58f878b1e3c78f366d78f1e8f1e3d1e3c78f366d3af4e9c780f1e03c1e06c5e09c078f263c7803cee6c361f0f87c3e7c03e04c78f264c78f266cd9b364c78f266cd9b369d3a74e00000000000f3b8000000004c03800c016040202700000005a8b061c187261c787361cd870e1cd87361c387099aa264e83a6da2e170386c2e17019dc180c1c2e061c187a83c0e83930e1c38f0e1eaa8387a0e6ea8087ddeaaaaaaaaa263c793a9a4383061c3870e87361daa260f2822e01c06070e01cd844231184c1e510517660033b830600c18388361b0015061c187060c387060c3870e4c3870e3c3870e4c3930e1c3870e4c39b0e1c3870098f1e4c9c4c593898b0e0c1870f07161e0e1d1ef71e3d478f1e1d06870ea1cdaa753a4c1e132604cb8070181c38073605c2e22130784c98132e0033b830600c1832e1710b8000c3830e1c9870e1c7870e0543ea27503a83d541e37550783d55555552a9d3e8741a1c3a8736b42e959ee5c2e070181c3807361170a08b9422170b8033b830600c183a2ecc2882210b8000030e0c383061c383061c387261c3871e1c387261c9870e1c387261cd870e1c3804c78f264e262c9c4c587060c387838b0f070e4d1e9326a4cba8741a1c3a872ea5d2e81dc1e00f000000000000000000ee0300180000000c3830e1c9870e1c7870e0543ea27503a83d541e37550783d5555555005d2e8741a1c3a872eb175a58bb4800000001040077002e0001dc060030866000000000000c3830e1c9870e1c7870e0233e7d787060c387838b0f070e93547aa1d506a8743aaa1d36aa8b5655555555555000000000000b820801dc000ee03001800000000000c3830e1c9870e1c7870e01f3ebc383061c3c1c58783873e7d387060c3870e1d0e6c3abd3a70f81c06070e01cd82f04e06c3600cee0c1803060cd86c361b000183060cf9f3e7c183060cf9f3e7c183060d3a74e9c000000000006770000004e00004c01e00301604020270000000183060c183060c183162e822aaaaaaaa898f1e4c183060f1ab4ee3569daa260f0180c465c119708846230983c060c8061c3850441b0d9b00d88c 24 16777215 10 1023
def hc_62_5 : Nat → Nat := unpackHintV5 0xba9141b1f627aced42a9c4caa405709c25f8969d629115628ba95b88d8b4836d5b810c987c951e781d1e75b89971411e6ebca16a511b6870786429125f4d37559a6d48b7393f76503486bc2c660824360c1c49fb1679740f31d209e553000279 0x1c380003060000c180d1c8c5a3918b1e3c78f060c183555555555500000000000000000000000000060c383060c183060c18f060e060c1c0c58f1e3c783060c1aaaaaaaaaa80c00000000000013b80c000180c001e1300783c0060700180c016010020000000000000000000000c187ee0c183061c3870eaaaaaa030000000013b80c00600703801c00580400800000000000000000306000c183068d1a346aaaaaa030000000013b8000000000000c1870e0c78301830000e1c00098f1e4c383061d1c8c5a3918b555555555500000000000013b80000000000000000c1870e0c783060c1870e1c98f1e4c383061c3c1c5878387555555555500000000000013b84c01e007001801c0e000700016010020000000000000000000000c383063c1f7060c183060c18b162c583060c583160c183060c1aaaaaaaaaa80000000000000000000000000031e0fb83061c383060c3870e2c58b161c1830e1c387161c5870eaaaaaaaaaa000000000000000000000000000c187060c183060c1831e0c18b060c183062c58b162c183060d5555555554000000000000000000000000001830fdc183060c3870e1d5555540000000000000000001830e1c18f060c1830e1c38b162c587060c3870e1c587161c3aaaaaaaaaa800000000000000000000000000b162c58b162c5aaaaaa800000000000000000030e0c18f07dc183060c18307555555554aaaaaaaaaa00000000000080000000000000000c783ee0c1870e0c1830e1c3d555555552aaaaaaaaa800000000000200000000000000007001800c180eaaaaa9555555554000000000001830e0c183060c183063c1d55555552aaaaaaaaa80c0000000000004000000000000000060c3f7aaaaa555555018000000020000000000003061c3831e0c183061c387aaaaaaaaaa55555555550000000000004000000000000000aaaa55555500000000400000000000468d1a3468d1a35555550000000013b84c01e007001802c02004000000000000000000187061c98f1e4c993264cf9f267cf93264c3a87aa99269f4387aa261f0b85c1e771e0f1e5c2e000c3830e0c1870e0c1870f13a87d44e2755138fd541eaaaaaa81ddeaaa263c793264c9a4cf934383061ea69aa260f09930267c0380ca08b844231180f3b8f1e03c78f0e0328828bb3088361b0000061c187060c387060c3870e4c3870e3c3870e4c3930e1c3870e4c39f0e1c3875498f1e4c9c4c593898b0e0c1870f07161e0e1c9a3d264d499f541bdc1835060c1a753a4c1e132604cf8070181c38072e05c2e2203cee3c780f1e3c380c0e1c039702e1710b8000131e3c993064c393064c3d43ea2755138fd544e27503a83d55555552a4d1e9326a4cfaa74db42e959ee4c1e132604cf8170b9170a08b942203cee3c780f1e3cb85ca2ecc2882210b8000030e0c383061c383061c387261c3871e1c387261c9870e1c387261cf870e1c3804c78f264e262c9c4c587060c387838b0f070e4d1e9326a4cba8741a1c3a872ea5d2e80000001dc06003000000ee0f00780000000000000131e3c993064c393064c3d43ea2755138fd544e27503a83d5555555004d1e9326a4cba974bb175a58bb4800000001040077002e01dc1e00f000866000000000000131e3c993064c393064c3931e3c993898b2713168cd9b5e93547aa4d26aa934faaa1d506a8b5655555555555000000000000b820801dc0ee0f00780000000000000131e3c993064c393064c3931e3c993898b2713166cdaf263c793264c9a4cf934d9b4ebd3a7260f09930267c0362f04e00f3b8f1e03c78f361b0f87c3e1f00078f1e3c78f1e3cd9b366c78f1e3cd9b366d3a74e9c000000001e77000000004e00003c03800c016040202700000028228187061c1830e1c1830e1eaaaaaaa878f1e3f3ab4ee7569d0e0c187aa1e0f11970465c0380c884623078f20793261401c06441b0d9b00d88c0061c1871ead58f1e3c78f1e3e1c31e3c78f0ea1eaa653a3d0e1ea9183c2e1707931e0f3b970b86d39b46003061c383061c3830e0c3c3eaa87c3eaa1f50fa83d55550f85d540eef5550f1e8f1e3d1e3c78f0e0c187a9a6a87a301e3c0783c0e032822e1108c460f1e4c78f0079dc380ca08b8441b0d9b00d88c 24 16777215 10 1023
def hc_62_6 : Nat → Nat := unpackHintV5 0xa5695d9fa17299e96e9445698b823186415081154b78c2157381506e41506901506082205b415056154b4dc2154881504341503e015035822032ccad3018ad2d00c62ae4872a44282698eb2334d91f90e91a554f1212110cd54f049211000124 0x3061fb83060c1870e1c3a0d506a87543aa2d59555543aaa022228711455404ee0c06070386c362826c11000187068306aaa1c3aaa931e3c987060c3978b8b2f1716aaaa9755511112ea297110983c0e030b9702e5c0b85c4400061c1a0d50ea931e3c987060c3a3568d5a4d550eaa870541565111156089dd15f8a930781c062b158fc4628ab00018706831438a4c78f261c1830e5e2e5e2e935543aaa1d55555955554baaaf75500983c0e030b85c2e17144b8880c1870e0c783060c1870e1c98f1e4c383061c3c1c587838749aa3d50ea83543a1d550eaaa2d59555555550eaaa808888a2087411455404ee4c1e070181c38072e023141044001e3c78f985c2e16ab4a5c397065c1970e2c5aaaaaaaaaa5d4444444ba883c1e170b82c82e5c0b97044001e3c78f985c2e16b05cb972e2c11551ea1d5516aa8b55555555552eaaa803c1e170b82c82e17144b8883c78f1f0fbbd0b170b85d42c38b062c18b0e2c58b47aa3d50ea83545ab2a2d16aa8b55555555555540444445851045a0aa809dc783c3e1f05902c580b2e0a09f04400263c79385cc2e174aaa5c397065c1970e2c5aaaaaaaaaa5d4444444ba884c1e170b82c82e5c0b9704400263c79385cc2e172aad5ab562d549aaaa83516aa8b0541111116156089dd5260f178bc1642b158a2ac00263c79385cc2e170a5cb972e2c1149aaaa83516aa8b55555555552eaabdc0260f0b85c164170b8a25c44263c793a162e1f7785c2ea161c583160c587162c5a4d51ea87541aa2d595168b5545aaaaaaaaaaaa8b540444445851045a0aa809dc983c5e2f05902c580b2e0a0af04400060c18385c2e6065c9971e5c79726ab4a1c3aaaaaaaaaa5d4444444ba885c2e030182c82e5c0b9704400060c18385c2e6065cb972eb01c1149aaaa83516aa8355555555552eaaa805c2e030182c82e17144b8880c183070b85c0eef40c183260c1831e0c1d40c38349aa3d506a83545ab2a0d06aa8355555555555540444445851041a0aa809dcd86c060305900c18032e0a09b04400061c18785c2e0725c9971e5c797274aaa0c1aaaaaaaaaa5d4444444ba885c2e070182c82e5c0b9704400061c18785c2e072ad5ab572a0d5551ea1d5516aa870541111116156089dd55e2f0380c1642b158a2ac00061c18785c2e0725cb972f0a0c11551ea1d5516aa8755555555552eaabdc02e170380c164170b8a25c44061c18785c2e818381ddc3930e1c38f0e1ea060c1a4d51ea87541aa2d5950e875543aaaaaaaaaaaa87540444445851043a0aa809dd78bc0e0305901c38072e0a0af044000e0c783ee0c18307555540ab2acaf75595540185c4d8f07dc187060c387aaaaa05595657baacaaa01c2e27c187060c1831e0eaaaa070b006975565595eeab2aa8170189b061fbd07a061e006a1e5595ee8795541360ab2d541960c38f060c1870f5507aaa0f0baa0550e9765595eeaa1d7ecaaa01c2e32eaaaaaaa805555655559557baaaab2aaaaaa0170b85c2e4444288888d1a34693547aa1d506a8b5655555550111111455404ee0023141044000e1c000063c18306000c18131e3c9a3918b4723160c18306aaaaaaaaaa000000000000000000000000000c383063c1f7060c183060c1931e3c983818b0703060c18306aaaaaaaaaa0000000000002770984c01e0f00180c00060000c00600b00801000000000000000000000060c060c380030601c38000f1e3c787060c3a3918b472316aaaaaaaaaa000000000000000000000000000c783ee0c1870e0c1830e1c38f1e3c787060c387838b0f070eaaaaaaaaaa00000000000027707803c00e0700180c00e0700038000b008010000000000000000000000e0030018301972e5cb8f1e3c783060c1aaaaaaaaa85c001e000300080400000000000000 24 16777215 10 1023
def hc_62_7 : Nat → Nat := unpackHintV5 0xb5a61ab00967a7ce0fa2e9399d4d6794e61a907d1a8b7941834e0b7e4941761e0b70e54e68d60463c9435f39245a014e51c60f4ef4b449616543cd653e555e3b2cca37d8d53235692fa0a52b451725a1691ce230173d690e7e3008a576000229 0x131e3c9d0b170fbbc2e1750b0e2c18b062c38b162d55555555516aa4d51ea87541aa2d595168b5545aaa0222222282809dd415260f1389c1640b1602cb8222829c041380c183070b85cc0d593563d58f564d569438755555555550544444445050454361b0180c1641b2e06cb822081b0183060e170b81dde8183064c183063c183a818706aaaaaaaaaa93547aa0d506a8b56541a0d5506aa80888888a0a02775054d86c060305900c18032e088a09b01036030e0c3c2e1703956ad5ab9506aaa8f50eaa8b5555a888888820aa71381c060b21389c514e08270187061e170b81cab26ac7ab1eac9d2aa8306aaaaaaaaaa0a8888888a0a08a89c4e070182c84e5c1397044104e030e0c3c2e1740c1c0eee1c9870e1c7870f503060d5555555550eaa4d51ea87541aa2d5950e875543aaa0222222282809dd4154e270380c164070e01cb8222829c041388d1a346aaaaaa93547aa1d506a8b565011111104eea0aa71389c4e2711888a0a70104e070e00003060c001830263c7932f17165e2e2c183060d555555555400000000000000000000000000187060c783ee0c183060c183263c7930703160e060c183060d55555555540000000001182770009803c00603000180003001802c0804000000000000000000360003018700060c03870001e3c78f0e0c1872f17165e2e2d55555555540000000000000000000000000018f07dc1830e1c183061c3871e3c78f0e0c1870f07161e0e1d55555555540000000001182770007803c00e00300381c000e0002c08040000000000000000003600070e0000c18000306032f17165e2e2c78f1e3c183060d55555555540000000000b8200000000000000000c187060c183060c1831e0c1c0c183818b1e3c78f060c183555555555500000000004609dc00060000c06000f007800c00600b02010000000000000000000d8000c187ee0c183061c3870eaaaaaa00001c004609dc0006003003801c0160402000000000000001b0001870603003804c78f261c1830e5e2e5e2eaaaaaaaaa1300038005c00810000000000000001870603060001c3800131e3c987060c3978b8b2f1716aaaaaaaaaa00000000005c00000000000000000060c387063c183060c3870e4c78f261c1830e1e0e2c3c1c3aaaaaaaaaa800000001c0004609dc002600f003800c00e0700038000b02010000000000000000000d8006cd9b367cf9f3e6cd9b36aaaaaa0000000000000000000c383063c1f7060c183060c1931e3c983818b0703060c18306aaaaaaaaaa00000000008c10000000000000000063c1f7060c387060c1870e1c78f1e3c383061c3c1c587838755555555550000000000460800000000000000003061c183060c183060c7830703060e062c78f1e3c183060d5555555554000000000118200000000000000000c187ee0c183061c3870eaaaaaa00001c00460800000000000030e0c060070098f1e4c383061cbc5cbc5d55555555400000000001830e1c18f060c1830e1c3931e3c987060c387838b0f070eaaaaaaaaaa000000007000118200000000000000008d1a3468d1a346aaaaaa0000008c1000000000000468d1a3468d1a35555550000004609dc002600f003800c0160402000000000000000001c3aaaa0c18355060d498f1e4cbc5c5978b8b060c183554baaaaa88975111110983c2e5c0b97006030b85c4400061c1831e0fb83060c183060c98f1e4c1c0c5838183060c18349aa3d506835541aaa83541aa2d595555555555404450504445155013b930780c18032e00c061b0d8a09b0440006830eaa0c1a870eaaa3c78f1e1c1830e5e2e2cbc5c5aaaaa5d5544444ba88883c1e070185cb8172e05c2e2200031e0fb83061c383060c3870e3c78f1e1c1830e1e0e2c3c1c3a3d51ea87541aa1d0eaa8755516acaaaaaaaaaaa022222828228aa809dc783c0e03038700e5c0f87c504f82200070eaaa0c1aaa8306832f17165e2e2c78f1e3c183060d2eaaaaaaa5d4444452e288972e05cb80f0780c06170b888000c187060c183060c1831e0c1c0c183818b1e3c78f060c18341aaa8341aaa3d51ea83541aa2d595555555555405050444445155013b832e00c180f0780c061b0d8a09b04400 24 16777215 10 1023
def hc_62_8 : Nat → Nat := unpackHintV5 0xb4d52db0212daf2040aa253fa4a161a0e0f09c1d319471eb8fad318801eb8339327b61f676ed1d7448a96f114e67c9d263f0f65e2573554a374f7d7346a23740d5733b0973321e3b2c8d64274552214580185a3b12bd670a820f059d39000167 0x14187061c98f1e4c993264cb97265db93264c383061ea8017b8f47aaa00004c2613000b904204c38f0ea4c78f261c1830e1c3870e5cb872eec3870f5400bdc1a0d5500002e070381c008210361cbab0e2e5585c367cd97265c7971e5c9970e5c197065c3d55528002aaaa5d5100000b8000000000000000000000006cf9b664cb8f3e3cb93661cb83360cb87aaaa00004fa9b4bb352eb32000000000000330019801001000cc000a87d44ea07507aaaa01565a59a5188c4623285d011dd11a00414110808c00e1c000063c18306000c1842e1742c5d03070381aaaaaaaaaa80000000000000000000000000030e0c18f07dc183060c183070b85d031740c1c0e06aaaaaaaaaa0000000000477000984c01e0f00180c00060000c00600b040400000000000000000000060c060c380030601c380042e170383d0b1741c3aaaaaaaaaa80000000000000000000000000031e0fb83061c383060c3870f0b85c0e0f41c5d070eaaaaaaaaaa00000000004770007803c00e0700180c00e0700038000b0404000000000000000000000e1c000183000060c0740c1d0b170b85c0e06aaaaaaaaaa0000000000477000000000000000001830e0c183060c183063c1d030740c5c2e170381aaaaaaaaaa800000000011dc00060000c06000f09803c1e00303800c0600b040400000000000000000000060c3f781c0e0f0755555500000023b8000c00600703801c005820200000000000000000306010381c2e0eaaaaaa00000047700000000000001830e1c18f0603060001c380042e170383d0b1741c3aaaaaaaaaa800000000011dc0000000000000000060c387063c183060c3870f0b85c0e0f41c5d070eaaaaaaaaaa00000000004770009803c00e00300381c000e0002c101000000000000000000002170b85c2d5555540000008ee0013007801c00600b040400000000000000000e1d555060c1aa8306a4c78f268e562d1cac583060c1aaa82a2aaaa22828222222130786cb81b2e00c061b0d888000c383063c1f7060c183060c1931e3c983818b0703060c18306aaaaaaaaaa93547aa0d06aa8355506a83545ab28088a0a088882775054983c060c0197006030d86c44504d8081b01a0c3aa8306a1c3aaa8f1e3c787060c3a3958b472b16aaaaa0a8aa8888a0a088883c1e070187cb81f2e07c3e2200031e0fb83061c383060c3870e3c78f1e1c1830e1e0e2c3c1c3aaaaaaaaaaa3d51ea87541aa1d0eaa8755516aca0222228282209dd4151e0f0380c0e1c039703e1f111413e0207c0e1d554183555060d068e562d1cac58f1e3c783060c1aa282aaaaaa828222222221b2e06cb80f0780c061b0d888001c50628306832e5cb971e3c78f060c183554bbdd5555555541a0d551eaa83556402e5c2e5c1e0f0180c2e171110401830e0c183060c183063c18381830703163c78f1e0c18306aaaaaaaaaa8355506835547aa3d506a83545ab28083414411111104eea0a832e00c180f0780c061b0d888a09b0103603061fb83060c1870e1c3aaaa8755506a83543aa1d516aca020c4511104eea0a830181c0e1b0d888a09b01036030e0d06a875498f1e4c383061d1ab46ad26aa875555aab2888882088a930781c06271389c4628a7041380c38341835550e1d55498f1e4c383061d1cac5a3958b55555054554444505044454260f0380c4e5c139704e2311041380c1870e0c783060c1870e1c98f1e4c383061c3c1c5878387555555543aaaa93547aa1d506a8743aaa1d5545ab2808888a0a0882775054983c0e03038700e5c1388c44505380827078f1e3e6170b85aad2ab0eac1ab06ac38b16aaaaaaaaaa0a8888888a0a08a83c1e1f0f82c83e5c0f97044103e0f1e3c7c3eef42c5c2e1750b0e2c18b062c38b162d55555555551ea8f543aa0d516aca8b45aaa2d550111111141404eea0a8f0787c3e0b2058b0165c111413e0207c263c79385cc2e172aad5ab562d549aaaa83516aaab51111110415260f1389c16427138a29c104e131e3c9c2e6170ba555561d583560d587162d55555555541511111114141150983c4e2705909cb8272e088209c 24 16777215 10 1023
def hc_62_9 : Nat → Nat := unpackHintV5 0xd828035943bcc64faf3befb285368d3e7a2d83a8b600a2683a8243ba09002824009eb8ee5333e8557bdeb5507055419834960caa15676649fdd0f977433fd30b8aba285ae885cdd1d6a047201d1503c0337050b30d400166 0x1c9a2c06930585c78f1e3ea6aa9554383061e81151eaaaaaaaaaaa8888c22a0a08a83c1e170b9105cb8172e088207c547831e1c7831e1c78f1e3eaa1f0faa87d50fa87d40ea0f55555554023d47aabdd5555555554141111196013ba2a0f2e03c780f0785c2e47c282211040f80c3830f5534ec9bb1eec7bb26ab4b408aaaaaaaaaaaa888888a0a08a85c2e07019105cb8172e08821ac061c1870e4c3870e3c38756a1f513a81d41eaa0f5541e0f5555555402aabdd06a835955555554444505065804ee8a85c2e070181c38072e105044220804c78f260e81931ead2e1709874583d0e0b0b83060c1d554931e3c9d2aad022aaa0d55555555511118454141150b85c0603220b9702e5c11040d80c1831e0c183260c18306ad43ea27550381d540ea81d40eaaaaaaa805541a83557baaaaaaaa228282232c02774542e1701970060c0180c8d8504422081b03831e0fb83060c1d5131e3c983060c1ab560cb97060c183060c1a0935541aad06b4a2222830b86c3626c783ee0c383061c3d50f1e3c787060c3870e1c3ab561cb970e1c3a08f43aaa1d56b4a2222870b87c3e27c187060c1831e0ea81972e0c183060c18356ac78f1e3c183060d041aad551e835a511114b80c361b1360c3f70f03060c1870e1c3a08343ad287445361b1360c38f060c1870f0785d5131e3c987060c3870e1c3ab561cb970e1c3a09343a1d0eaab4a8074b888a1c2e33198aa4c78f264c987264c3d55555513263c78f1e5fbd43c7d545d597568a88a288888884c1e1326132e170b9105c2e00030e0c387261c3870ead55555517565d5870e0c183065fbd40c1d548a8888a2888885c2e070181c381cb9105c2e0055551726ac7971eac9970eac19706ac3a822aaaaaaacb2888888a0a0a285c2e170b9105d9817660a20007063c1f7060c183aaa062c5835555944916277506171363c1f7061c1830e1eaa838b161d55565124589dd4385c4f830e0c183063c1d503170c183062c5aaaac834b8a122c4eea5c0626c187ef41e060c38755906a1e4589dd536b2aaaaf061c783060c387aa83d541c38b161c5c30eaaab2a01d2e48b13ba870b8afaaaa162c58b162c58b555555555944446516089dd150b85c2e17220582c44105e532eacbaacb8ac1871e0cd83061c3931e3c987060c3870e1c3972e1d9d30e1c3c1e1754001d59a80070b8004c0e070380104330 22 4194303 9 511
def hc_62_10 : Nat → Nat := unpackHintV5 0x8049077969b875d4e56fbd866bf8f162ae535c958658d0f14f86534f580b4f3c074ef81148e186447d193e917b35225c35040734b4143174d02b2d922529812298a41e451517d99b0e2e6b08f94d015de701240e01240000ec0e00003b000000 0xc38301830000e1c002aaaaaaa95555555554000000000000100000000000000001830e1c18f060c1830e1c3d55555552aaaaaaaaa800000001c023b8000204c01e007001801c0e000700081010000000000000000000002aaa955555400008ee0000813007801c0060408080000000000000000103060c183aaaaaaa0e1e8183aaa08a268f41a0d99bead65ab5260f0180c88162c0183044260f0180c88365c0d97043600075541b0f89d4ae5752b9dc0e075404d06a0e55aaaa89309dd4b85c36426c187060c783ee0c183060c183a87d44eaa075540e0750381d40e0f5555555401347a0c1a835068365a59a4983c060c019700603285d011dd11a130780c18032e00c0646c282210d81b036031f030e1eaaaa8183aaaaa0e1e82287a3d0e836679ab5e6ad4783c0e0322058b00e1c110783c0e03220f9703e5c10f800a0d0eac3e1f0383d4ae5752b9bd5023c3a1d956aaaa24c27752e170f909f063c1f7060c387060c1870e1ea1f0fa87c4ea07507aa83d550783d5555555003d1e8741a1c3a8759696691e0f0380c0e1c03970a174047744683c1e070181c38072e11f0a08843e07c0f8aae5aaad0183060e063c1d5555070f5540c1d550450f47a0d06ccab556a3c1e03019102c5803060883c1e03019106cb81b2e086c000ea8356a5737a95cae1f0f81c0eaa570b006a3d072ad5555697142613ba970b86c804d87078f0603060c1c0e81c0eaa87d540eaa2f77aaaaaa00b974b9747a3d068365962ed25cb85cb83c1e030190411085c060c383060c183060c18f07550381d540ea87d43ea07503aaaa81c2eaaa8006a0c1a8f47a0d06cb4b3483065c01830180f0780c0650ba023ba234065c018301e0f0180c8d8504421b03606ceebde5941ea8387aa283a1d9950e070e1c881603110381c88361b10d8000c187ef50381d40ea83d41eaa0741ea001a0d0e8765a59a41830180c381c387285d011dd11a030181c0e46c282210d81b036030e0eaaaaaaa060eaa8387a08a268f43a0d9a6fab596ad4983c0e0322058b00e1c111a130781c06445f2e12cb82023009aa1d5958224d0eacf75666547e8b155f970b8ab41aa1d587c4e0707a95caea574ae175404d0e8755665665056972613baabf2e170855a0c3838183c9870187aaa2777aaa0f77aaa0f07aaaaaaa2f77009a3d0e834b974b9762ed31769260f0380c2e5c2e5c8b944421701830e1c18f060c1830e1c3d43e1f51389d40e0750783d541eaa83c1eaaaaa0f0baaa009a3d0e83438750eb2d2cd24c1e070181c381c03872e142e808ee88d0983c0e03038700e5c20a08840460131e3c9cd552ad2b70edc1b706dc3d022aaaaaaaaaaaa22222282822a130785c2e44172e05cb822086f15263c793260c987260c987a87d44eaa275544e27503a83d555555500af747aa3d556555555551141411196013ba2a130784c98132e05c2e414110882007060c38fa161c1ab4b85c 24 16777215 10 1023
def hc_62_11 : Nat → Nat := unpackHintV5 0xe66ab5e01196da8563d43993c9b6a1befeaeb402bfad29b6aa58b4a788b4a2e12a96a3108a63107de3207649e669cb205f569d5899af4dfaa843869d3cc9af322aa82be19227f4fb2125b41d38fb1669b412c8e80eccff07edb803a1130000e8 0x2a0c183060c7831e0c183060c783060c18f060c18f060c183060c183060c183007c3c58f878b1e3c78f0703060e062c183060d1ea3d55eeaaaaaaaaa0a08883506027744441e5c078f01e0f019b0060c0180c2e1711000183060cb93563cb8f564d41151bf46fc183060d1c5c597958b555506a0d5551111414111450b85c06030b9b02e6c0b85c4400060c183864e18f863e193060c116170b41c0d569555555555551111414145110b85c06030b9702e5c059088000c183065d597568b0b85c0e0742c5c5eee0c58b162c183060c183a060c183a06aa2222228a28a170b80c06170b82c8160b000183063c183064c183060c085c2e8183a062e0703164c58b163c58b060c583060c183060c183062c583060c183060c1aaaa8355555555eecaca220d41809dd451414110b85c066c01830060305902c580b2e08800003060c7831e0c183260c983060c1831e0c383060c1830e0c383060c183060c9830e0c183060c1804c78f264e262c9c4c58381830703160c18306aaaaaaaaaaaaaa07707803c01803003b8000000000000000000000000c183060c3830e0c183060c7830e0c1831e0c783060c783260c183060c183060c7830e0c1830600f878b1f0f163c78f1e0e060c1c0c583060c1aaaaaaaaaaaaaa83c07801dc0600c00ee005c0040000000000000000000060c18f060c193060c183011a30703060e062c183060d41a8306a0d06a8d0060c383060033ba3118886c36033600c18030186c3621b000187061cf9f3e7c383061d555554000000000000000000187061d1a3468c383061d555554000000000000000000187061d1a3468c383061d55555400000677000009803c00e02c08040400000000000000000061c1831e0fb83060c183060e170ba062e818381c0c593162c58f162c183060c183162c183168c183060c183060c183060c0268f4183506fd41a0d162d91a2c5a8b46a4c1e030600cb803018477a0a910983c060c01970060305902c580b36086c00063c1f7060c387060c1870e1e170b81c1e838ba0e1c58f162c58f162c387060c1830e1c3870e1c387162c387168c3870e1c01e8f43a0d0e1d43bf5162d91a2c5a8b46a3c1e070181c38072e0477a0a910783c0e03038700e5c05902c580b3e087c00060c383060c183060c18f0703a060e8183162e170b81c0c183168c183060c183060c183162c58f162c58f162c183060c183060c006fd418351e8f41a0d162d91a2c5a8b46a0cb8030603c1e03018477a0a9101970060c0783c060305902c580b36086c00060c3f78183818383878387060c183060c1830e1c3870e1c387001a0d0e87458b6468b16a2d1a830181c0e11de82a4406030381c1640b1602cd821b0001830e1c18f060c1830e1c3c2e170383d070e2c5c1e8387164c58b163c58b0e1c183060c3870e1c3870e1c58b0e1c5a30e1c387009a3d0e83438750efd458b6468b16a2d1a930781c06070e01cb811de82a44260f0380c0e1c039701640b1602d1822f0015263c793260c987260c98785c2e858ba162e170b164c58b163c58b164c593162c58b164c5a3162c58b161c583160c587015ee8f547aaaaaaaaaa88a0a088277606510983c264c099702e1705902c580b46088008a5cb972e3c78f1f42c5c5eee2e170b85c2e858b163e858b162c58f162c38b162c3808aaaaaaaaaaa5c2e0f0785c2e0b2058b059711151e0c7871e0c7871e3c78fa162e858b85c2e170b163c5a3162c58b163c58f162c58b163c58b163c58b161c583160c587011ea3d55eeaaaaaaaaa8f4144111104eec0ca20f2e03c780f0785c2e0b2058b0167c11000187061c3930e1c38f0e1d585c2e0707a0e2e8387164c58b163c58b0e1c183060c3870e1c3870e1c58b0e1c5a30e1c38701555ee83541aaaaaaaa8888a0a0277606510b85c0e03038700e5c05902c580b46088005cb972e0c183068b0b85d0b1717bb8381c0c593162c58ba060c183a060c183060c180aa8aaaaaaaaa5c2e170b80c060b2058b0597110183063c183064c183060d585c2e8183a062e0703164c58b163c58b060c5a3060c183060c183060c58b060c183060c183015506a0d55eeaaaaaaa888341441104eec0ca2170b80cb8030600c060b2058b0166c11002170b85c2c593162c58f162c587160c583161c055162d91a2c5a8b46a8c4623118477a0a91178bc5e2f05902c580b4608bc000e1c000060c1800306155555554aaaaaaaaaa000000000000000000000000000c383063c1f7060c183060c1d55555552aaaaaaaaa8000000011dc000102600f00180c00060000c0060408080000000000000000000000c061c0018300e1c002aaaaaaa955555555540000000000000000000000000018f07dc1830e1c183061c387aaaaaaaa55555555550000000023b8000203c01e007001801c0e0007000810100000000000000000000003800c0060c075555554aaaaaaaaa3700078000c2040000000000000000387000060c00018301d55555552aaaaaaaaa80000000000000000000000000003061c183060c183060c783aaaaaaaa555555555501800000000477000040180003018003c01e00300181020200000000000000000000003061fbd5552aaaaa80c0000384770000401800c00e00702040400000000000000000061c180c00e055555552aaaaaaaa84c000e00470800400000000000000 24 16777215 10 1023
def hc_62_12 : Nat → Nat := unpackHintV5 0xf279d2eded23e5da05d9cb04d249e0ccd55dc09710bac973b012aeaa4573a295ec9796c0913d968bb163815a96765ebf6ba6ae67591361c9645b8d8f55419350a9264929e0449d23385f103115d22be94b23821a16933c10c57305f2b500017c 0xe1c3d41c3830e0c3830600c18720f0ba162e838781c1c7a3d76ad5dab50e8345b23c1e0b0600c18070182c8441e0f0f9703e5c0380c16421f0007871e1c21707590e0c1870e1c38756dc3ab561c38716aa3d545a2d4ee0c06a2070f85c2e030e0c3870e1c38f0e041e170383c1c5c1c38f1f01c1832fdc1830e1c387062c183061c38b2163d1e8741a1c3a1cba2d92e974783c0e030387039705905c2e2170187061c38f0e1c38f0e1c087dde858b81c1e838ba0e1ea0e1c183060c3870e1c3870e1c58b0e1c5870e1c38b162c7a3d0e83438750efd45b22c5a8b51e0f00677060c0183062c8162c1602c5970441e0f0380c0e1c039f01640b1602cb821f00283870e1c3c0c3830e0c1803061c85c1e858ba0e1e0707268f5dab576ad43a0d16c930782c18030601c060c182c844260f179705e5c0380c16422f0009871e1c21707950e0c1870e1c38756ec3ab561c38716a93506aa1d568b45a9dc180d5697141438bc2e171560c3830e1c9870e1c7870e050b170fbbc0e0f41c5d070f5070e1c383060c18b061c3870e1c3870e2c5870e2c3870e1c58b164d1e8741a1c3a877ea2d9162d45a93078033b830600c1831640b1602cb822130781c06070e01d780b2058b0165c1178001c3aaa83060a80c3a1d1cdc5a39b8b263c7930e0c18755555555555050444444442e5c0b970260f0380c2e17110015061c187060c387060c3870e4c3870e3c3870e4c3930e1c3870e4c3870e1c3804c78f264e262c9c4c587060c387838b0f070eaf747aa3d5555555544505013ba0c106a222130784c98132e01c06070e01c0b85c44000e1d5550e0c3aa030603c78f1e8e762d1cec587060c3aaaaaaaaaaa228282222220f0785cb8172e01c06170b888008a0c1870e0cb83ee1c187061c1830e1c38f060c3870e1c38f0e0172e5cb8f1e3c787060c3870e2c3870e8aaaaaaaaaa5c2e0f0781c06070e072e170b888a83061c383061c3830e0c3871e1c3870e1c38f0e3c3870e1c38f0e1c38f0e1c01f0f163e1e2c78f1e3c383061c3c1c587838747a8f557baaaaaaaaa3d05104413ba0c106a2220f2e03c780f0781c06070e01cf8170b88800ac9971eac797260c3830ea0a88dfa37e5e562d1c5c587060c3aaa1d43aaaaa22828222228a170b85d98176601c06170b8a2003b26ec7bb1eec9830e0c383060a90b85d2aac0d0eaaaaaaaaaa88a0a088a28885c2e172e05cb8070182c84400061c1870e4c3870e3c38702170b81c1e838ba0e1c593162c58f162c387060c1830e1c3870e1c387162c387161c3870eaaaaaaaaaabdd9594413ba0c106a8a282822170b81c06070e01d780b2058b0165c110000061c187060c3870e1c193060c3870e4c3930e1c38f0e3c387060c1830e1c3870e3c1830e1c3870098f1e4c9c4c593898b0e0c1870f07161e0e1d555555555555540ee0f007807701800c002e0800000000000000000000000c783061c383061c3870e0c3830e1c783061c3870e0c183061c3870e1c787261c3871e1c7870e00f878b1f0f163c78f1e1c1830e1e0e2c3c1c3aaaaaaaaaaaaaa83c07801dc0ee0300180000000000000000000000a0c3830e4c78f264c993265db932e5c99326010b85c2e16bdc7a3d550000000e07040187061cb932e3cb8f2e4d400119f3ebc383061cbc5c5978b8b55154baaa000000017000000000000000000000187061cb933e3cb8f664c000119f3ebc383061d1c5c597978b4fa1d069752ecd57a8d00000000000000038001c000066000030e0c387261c3871e1c3808d187060c387838b0f070ea1d06870ea1d546800cee0c1803060d188c4400e03038700e0231000060c183468d1a3060c18355555500019dc0000002600f00180b02010100000000000000000183060c183a0703060c1803018381c2e0703a060e858b1e8f41a0d8ead63ab516c8f0780c180c061c380b0e02c8441e0f0180c365c0d97016421b00018f063c2070b5906ad583060c183060d5b7060c18316aa3d545a2d068313ba21b0185c2e03060c7831e0c1831e0c983060c1810fbbd0b1740c1d03170381d40c18b060c183060c183060c58b060c183060c183162c58f47a0dfa8306a0d068b6458b516a3c1e03061c1830019dc5902c580b2e0883c1e033600c18030182c8162c059704360003060c1838183060e818300603070b81c0e0740c1d0b164d1e8341b1d5ac756a2d9260f0180c0e1c0587016422130780c061b2e06cb80b210d8000c7832610385ca8356ac183060c18306aeb83060c18b549aaa0d06a0c5a2d068313ba229b0185c2e26c183060c183260fb83060c1810b81c0c1c0c5c0e0703c983060c183060c587060c183060c197ee2c859347a0cba0c1a0d068b64ba5d260f019701830180c164170b885c060c18f063c183064c193060c18302858b87dde8183a062e0703a8183160c183060c183060c18b160c18b0e0c183060c183062c58b268f41bf5060d41a0d16c8b16a2d4983c060c383060033b8b2058b0580b165c110983c066c01830060305902c580b2e086c00068306aa0c1a830608a4c78f260c183068e6e2d1cdc5aaaaaaaaaaa22228282222130780c06172e05cb8170b88800a83060c783060c983060c183260c183060c193064c183060c183060c183060c0263c7932713164e262c1c0c183818b060c18357ba3d51eaaaaaaaaa2282820d41809dd1110983c264c09970066c0183006030b85c4400060c1a0c1aaa830608a3c78f1e0c183068eae2d1d5c5aaaaaaaaaaa220c4541411110783c06030b9702e5c0b85c4400 24 16777215 10 1023
def hc_62_13 : Nat → Nat := unpackHintV5 0xdd3196d76573ccaeaec6e173bf31ecb432c0aea563a44e969ebd649a711394358f8de99389512681d1e07d452371071069bdd264914b5c2a1a4f3b3c48e1964315733842b532517c277eb521f1631ba5931122a10a49b60778b404a8b400012a 0x14150b83561d5832e1c98f1e4cbcac5a38b8b263c79346fd1bf49a9355555550504444445142ecc0bb30260f0b85c2e17144000e1c150183555061d0e8e6e2d1cdc5931e3c987060c3aaaaaaaaaaa82822222222172e05cb8130781c06170b888000030e0c383061c383061c387261c3871e1c387261c9870e1c387261c3870e1d5263c7932713164e262c383061c3c1c587838755555557ba0d506aa89dd1e08f51141411110983c264c098070181c38072e05c2e220003418345060c0183555263c793060c1834737168e6e2d5555555555111141411110983c06030b9702e5c0b85c4400009931e3c78f2fdc183063c783060c183060c183060c183060d1498f1e4c993164c98b2e5cb97060c18355555455555260f099309970b85c06030b85c4400183063c183064c183060c193060c183060c983260c183060c183060c18306a931e3c993898b2713160e060c1c0c583060c1aaaaaaa0d41aabdd544ee8f047a8341441111110983c264c099b0065c0183006030b85c4400162c151b836e1db836e1c98f1e4e9556168b85c2d55555555554141111145110b9702e5c0983c2e17059088000131e3c993064c393064c3c2e1742c5d0b170b858b262c58b1e2c58b262c98b162c58b262c58b162c587160c583161d55555555557bb2b227747823d44514505044260f0993026bc0b85c1640b1602cb822002800131e3c997065c397065c3931e3c9978b8b2f17168cd9b5e2a9755554000002e000000000000000000000000030e0c3930e3c3970eec3870e5c3970e1c3ac2e170b83aaaf7068340000984c00100000263c793360cb872e0d987263c7934717165e5e2d19b36bc9a3d2ea5d9aa6d5ea340000000000002600130000001980000131e3c993064c393064c3931e3c993898b2713168d19347a4c9a935551a0f3b8f1e03c78f04623110983c264c098008c400078f1e3c78f1e3d1a3468d5555541e770000000007807001802c0804040000000000000000060c0180c183060c1d03060e060e170ba161e838781c0c7a3d8ead63ab5068345b23c780c1e4c98030600c060b2110783c365c0d9700603059086c000060c18385c2c7ab563c78f1e3c78f56ec78f1e3d643aaaa83168347a3c4ee886c1e170b8003060c183060c1831e0c383060c1d0b1742c5c2e1703bbd03060c783060c183063c18f060c183063c183063c183a8187063dfa8f1ea3d1e8341a2d9060d41a8f1e4c78f0079dc180c164030600cb8220f3603c780f0780c060b201830065c10d8001c38070387061c187060c3c0c1d42e1742c1d030703838f47b1d5ac756a1d068b64781c264c038700e030590883c1e1f2e07cb8070182c843e000030e0c3c2e163d5ab1e3c78f1e3c7abb63c78f1f2a0d5551e8f51e1d168747a3c4ee88a7c1e170b89f0018f0e1c1870e1fb830e0c3c2c5c2c5c2e1703838f1e1c3870e1c3871e3c78f0e3c797ef00c3832163cba3c7a3d1e8741a2d92e974797078f0783c0e0305905c2e21700063c1830e1c1830e1c387061c187a162e858b85c2e818381ddc38f0e1c3870e1c7871e1c3870e1c787261c3871e1c7870f503060c7bf51e3d47a3d0e8345b21c3a8751e3c98f1e00f3b870182c80e1c0e01c3970441e7c078f01e0f0380c164070e01cb821f001411478f1e3d5832e1cb83561c78f1e3d1c5c597958b46fd1bf551ea3d555551141411111450783c2e7c0b9f02e170b85c44000e1c1150e0c3aa8306a3c78f1e8e762d1cec587060c3aaaaaaaaaaa228282222220f0785cb8172e01c06170b88800003061c383061c3830e0c3871e1c3870e1c38f0e3c3870e1c38f0e1c38f0e1d51f0f163e1e2c78f1e3c383061c3c1c587838755555557ba0d506aaa3d47809dd114141111079f01e3c0783c0e03038700e5c0b85c4400060c1a0c18228306aaa3c78f1e0c183068eb62d1d6c5aaaaaaaaaaa3c451141411110783c06030b9702e5c0b85c440000183060c18f063c183060c18f060c1831e0c1831e0c183060c183060c18306a8f878b1f0f163c78f1e0e060c1c0c583060c1aaaaaaa0d41aabdd551ea3c04eea0a08888883cd80f1e03c1e032e00c18030185c2e22000b1608a3c78f1f0c1c30f0c1c30e8b85aad2c2e16aaaaaaaaaa88a0a088a28883c1e172e05cb8170b82c84400451e3c78f565cbab85c2e858b8bddc5c2e162c58b163c5d0b162c7d0b162c58b55111111451450783c2e170b85c1640b0580000f063c38f063c38f1e3c7d0b1742c5c2e170b858b1e2c58b162c58f163c58b162c58f162c58f162c587160c583161d547aaaaaaaaaaf765651ea3c04ee88a28a0a0883cf80f1e03c1e170b82c8162c059704400007831e1c7831e1c78f1e3c7c3c58f878b1e3c78f468c7a8f1ea3d1eaa8d1e3c98f1e00f3b823118883cf80f1e03c1e1f0f87c3e21f00098f1e4c98f1e4cd9b366d55555400000000000000000098f1e4c98f1e4d1a3468d55555400000000000000000098f1e4c98f1e4d1a3468d555554001e7700000009807001802c08040400000000000000000 24 16777215 10 1023
def hc_62_14 : Nat → Nat := unpackHintV5 0xbfb9d0bb511ab54d81ac3e44a639819d2a44975d738dc666882d668488e97e119e75662b707d3a6b953a66c9336448a05f7d335d6c8457358e50fd8e4a859e46f4e440d9873df0ba392d3131e5d22d592325460519370411b5e00c415d000310 0xd9f36cc9971e7c79726cc397066c1970f5554a1309d3ea74da2c5817169325c2e170b85d181746110885d985c4e5d985c4f54542272e9c046232a1f513a81d41eaaa9555a174acf746a351a8d91a5248da5553a74e9e8a8aa53a75468d0e1d555063c18306aa0c1ac2e1742c5d03070381aaaaaaaaaaaaaa2a2aaaaa931e3c99b2e6c365cd80c183062e85aaaa830e0c18f07dc183060c183070b85d031740c1c0e06aaaaaaaaaacf749a4d51e8f541a0d5506aaa0d506a8b5555545455555555154263c793060c180cb830183060c5d0b55544da2a830683061d5418350e1d556170b81c1e858ba0e1d555555555555555151555478f1e3c383061cf97361f2e6c1742d555418f07dc1830e1c183061c38785c2e0707a0e2e8387555555555567ba3d51ea8743aa0d06a8743aaa1d5545aaaaaaaa2a2aaaaa8aa0f1e3c787060c3870e1c0e5c382e85aaaa27d154387555060d55418341d030742c5c2e170381aaaaaaaaaaaa2a2aaaaaaa9b2e6c365cd83c78f1e0c183062e85aaaa83061c183060c183060c78381d030740c18b170b85c0e06aaaaaaaaaacf741aaa8341aaa3d26a8f47aa0d0ea8341aa2d55515155555555545501970603060c1e3c78f060c1831742d5551368aa0c187ef030703070783aaaaaab3dd06a83543a1d50eaa2d555555555554550183060c3870e1c5d0b55544da2a8306ab030703070b83aaaaaab3dd55555555060c183366cd9b1742d55541830e1c18f068306aaa1c3aaac2e170383d0b1741c3aaaaaaaaaab3dd555554545555263c7930e0c1874e5cd89cb9b05d0b5555060c387063c183060c3870f0b85c0e0f41c5d070eaaaaaaaaaacf749aa3d50ea83543a1d550eaaa2d555555515155555455098f1e4c383061c3870e072e1c1742d55514e8aa0c383063c1f7060c183060c1c2e1740c5d03070381aaaaaaaaaa80000000000000000000000000031e0fb83061c383060c3870f0b85c0e0f41c5d070eaaaaaaaaaa000000000000000000000000000c187060c183060c1831e0e8183a062e170b81c0d5555555554000000000000000000000000001830fde070383c1d5555540000000000000000001830e1c18f060c1830e1c3c2e170383d071741c3aaaaaaaaaa8000000000000000000000000042e170b85aaaaaa800000000000000000030e0c18f07dc183060c183070b85d031740c1c0e06aaaaaaaaaaaaaaaaaaaaaaa4c78f260c18301970603060c18ba16aaaa0c783ee0c1870e0c1830e1c3c2e170383d071741c3aaaaaaaaaaaaaaaaaaaaaaa8f1e3c787060c3870e1c0e5c382e85aaaa83061c183060c183060c78381d030740c18b170b85c0e06aaaaaaaaaaaaaaaaaaaaaaa0cb830183060f1e3c783060c18ba16aaaa0c187ef030703070783aaaaaaaaaaaaaaa83060c1870e1c38ba16aaaa0c1870e0c783060c1870e1e170b81c1e838ba0e1d5555555555555555555555498f1e4c383061c3870e072e1c1742d5556170b85c2d5555555555555553a74e9d3a74e9c5d0b555585c2e170b55555567ba4d51ea87541aa2d5555555555545513a74e9d3a74e9c5d0b555453a2a830600c18301c0c1d03060c1830741c3d0b0f0b85c0e06dd5ab756a4d1e8341a2d9060c078f0060f0180c164221b2e06cb8130780c060b210d80000c183070b85931e3c993264c9ab6e4d5ab264c9ac875555062d06a771e0f510986c2e1700060c183060c183060e170b858b858b81c0c18f1e5fb8f1e4c983060c1831e3c183060e0390b268f4993499741a0d16c974ba4c1e1326132e030182c82e1710b8003060c183060c183060c1c2e1742c5d0b1703bbd03060c983060c783060c983260c183060c983060c183a8187064d1e9326a4dfa8341a2d9060d41a83cee3c780f1e3c180c1640306030060cb822130784c98133600c060b201830065c10d8001c38070e1c060e81830f030e0c3d030742c1c2e170383b756add5a9347a1d068b6438701e3c0383c78f0380c164222f2e0bcb8130781c060b211780000c3830f0b85931e3c993264c9ab6e4d5ab264c9ca83551eaa4d568745a1d4ee3c1eab4b8a0a4c5e170b8ab00187061c1830e1c1830e1e170ba162e858ba060e07770e4c3930e1c38f0e3c3870e4c3930e1c3870e4c3870e1c3d40c183268f4993526fd43a0d16c870ea1d41e771e3c078f1e1c060b2038700e5c110983c264c09af00e0305901c38072e08bc00 24 16777215 10 1023
def hc_62_15 : Nat → Nat := unpackHintV5 0xd39d62cdd572c76d9ac26941ba8df7b58941adadf7a8a941a0a2029bc138973d219229458a3dfb86150a7f49b3754a806e7db3647e805d45ce53aa674f710e491597425dae3bd5a239589f34b12a2a369f218a2b1886410fda2b06d6410001b5 0xc38f060c1870f07162c3d07263c7930e0c1870e1c38756ac3972e1c387415544500e9705a2d50e17178bc57c2e170b859726ac7971eac9970eac19706ac3a822aaaaaaaa28222222c4516a2a170b85c2e0b20baf02ebc11041790b85c2e162c98b162c78b162c38b062c18b0eaaab3de96a55162d9162d05a2aaf4ebd3af4ebd38ba162c58b05af1629d3aa75e870eaaa83060d541835aaaaaaaa5555555555555454555555263c793365cd86cb9b0183060ea95554187060c783ee0c183060c183aaaaaaaa5555555567baaa4d51ea8341aaa0d5541aa0d5955555151555555515098f1e4c18306032e0c060c183aa55544da2a83418755060d4387555aaaaaaaa55555555555555545455551e3c78f0e0c1873e5cd87cb9b2a9555418f07dc1830e1c183061c387aaaaaaaa5555555567baaa3d51ea87541aa1d0eaa87555955555551515555515078f1e3c383061c3870e072e1caa55544fa2a870eaaa0c1aaa830683aaaaaaaa5555555555545455555555365cd86cb9b078f1e3c183060ea955541830e0c183060c183063c1d55540e175554aaaaaaaacf75541aaa8341aaa3d51ea83541ab2aaa2a2aaaaaaaaa2a032e0c060c183c78f1e0c1830754aaa89b455060c3f7aa81d52aaa8759eeaa83541aa1d50eacaaaaaaaaaaa8a80c183061c3870f54aaa89b455061c1a0d50ead55555524d550eaabf5955555555555263c7930e0c1874e6d39baa554eaa830e0d060d554387555aaaaaaaa55555555555555554545555263c7930e0c1874e5cd89cb9b2a955541830e1c18f060c1830e1c3d55555552aaaaaaa1d567baaa4d51ea87541aa1d0eaa87555955555551515555515098f1e4c383061c3870e072e1caa555453a2ad5552aaab3dd5526a8f543aa0d59555555555551513a74e9d3a74e9ea955514e8ab03060c183aaaaaaa0e1e8183aaa59a268f41a0d99162d41835268f41a0d99465d1197455263c793060c183aa365cd86cb9b1366d4d9b4187060c783ee0c183060c183a87d44eaa075540e0750381d40e0f55555554a9347a0c1a8356a0d06d0ba567b9347a0c1a034680d06c8d29246d2aa4c78f260c183019b0603060c1c6e2a2a9366d4d9b418f81870f555540c1d5555070f4b343d1e8741b322c5a870ea3d1e8741b328cba232e8aa3c78f1e1c1830f547cb9b0f973626cfa9b3e831e0fb83061c383060c3870f50f87d43e27503a83d541eaa83c1eaaaaaaa951e8f43a0d0e1d43ab5a174acf71e8f43a0d0e1d03a3491a5248da55478f1e3c383061c3870e073e1c8fc545526cfa9b3e83060c1c0c783aaaaa0e1eaa8183aaa59a1e8f41a0d965162d418351e8f41a0d91b4a32e88cba2a8f1e3c783060c1d51b2e6c365cd89b36a6cda0c187060c183060c1831e0eaa0703aa81d50fa87d40ea0755555554a8356a0c1a8f47a0d06d0ba567b834680c1a0f47a0d06c8d29246d2aa0cd830183060f1e3c783060c1c6e2a2a9366d4d9b683d5070f54d0743870ecb28b41a1d0ec8da51a8d550e1c387aa366cd9b4d9b5366d060c3f7a81c0ea07541ea0f5541ea541a0d0e870e1da174acf7068343a1d91a5248da554183060c3870e1e37151549b36a6cda0c383aaaaaaa8183aaa0e1e96689a3d0e8366458b50e1d49a3d0e83646d28cba232e8aa4c78f261c1830f557cb9b2f973626d3a9b46830e0e068f261d061eaa89ddeaa83ddeaa83c1eaaaaaa95ddd5268f43a0d46a3646d32369263c7930e0c187566d59ba7d55526d1a4c098700f2c2d16970b84c9870f41e2a0b972e5c18030e01e1f1381c1ea2f17a8bd54a5d2ec2e67b970b85c82f13261c3870e5e0a8a2e5cb97060c387063c183060c3870f50f87d44e2750381d41e0f5507aaa0f07aaaaa83c2eaa95268f43a0d0e1d0ea1c3ab5a174acf7268f43a0d0e1d03a3491a5248da55498f1e4c383061c3870e070e5151549b4ea6d1aa931e3c993064c393064c3d43e1f51389d543e17550b85d40ea0f5551385d55552aaf747aa3d5565955eeaaa8a8aaa8a8aaaaa4c78f264c99309a726273e9cfc9e2a2a9555551e0c7871e0c7871e3c78faa85c2eaa1f0ba87c3ea1f13a81d41eaaaa1f0baaaa551ea3d55eeaaad65955eea8a8aaaaa8a8aaaaaa3cf8f078f1e0f1e3c79f3e7cfc7e2a2a954faaa0c3830e1c9870e1c7870ead43ea2750381d41e0f550381d541e0f555550785d552aaaaf741aa0d65955eeaaaaa8a8a8a8aaaaa9cda7361c1830e1c38703a70e49e2a2a95554183063c183064c183060d5a87d44eaa0703aa81c1ea0703a81c1eaaaaaa070baa55555a83506aaf765955eeaaa8a8aaa8a8aaaaaa6cd9b360cd8301830603060c1c6e2a2a954daaa0c38f066c1830e1c98f1e4c383061c3870e1cb970ece7870e1e0f0baa440e1d43a79e8b0581c2e231184c9870e1c3870b870aa369cda3 24 16777215 10 1023
def hc_62_16 : Nat → Nat := unpackHintV5 0xf0694fe91dd3e31981da1641d4fd46cd35f2c68daabdbe34baecb4b6412bb0058fab113da4d58fa184d49c494f943a04875f377f4e047273376a1a165d5b305569fc4d12163ff747346ae328eedf1d62e311e6df0ce54007e54002b94b0000ae 0x2c5aaa830e0c3d070f54c3ea55a5aa5555555555555454555555263c7934e5cd89cb9b0383061ea9555617030e0c3d41e0750fbbd55554aaaaaaaa837baaa4d26a8f47ab32ab2aa875959555554545555555454263c793a88bc07060c3d52aaa87d53a2a830e0c3d342e070755a50e1c183060c387162d555555555555555555551515478f1e3c383061c5d0b3e5cd87cb9b15554187061e1f77a162e0707a8387060c1830e1c58b16aaaa837baaaaaaa3d51ea875168b566545a2d5516aaaaaaaaaaa8a8aaa8a83c78f1e1c1830e2e858b162c165c58aaaa1f53e8aa2c5aaad55070e0c3830f4aab4d54aaaaaaaaaaa8a8aaaaaaaa7cb9b0f97360f1e3c787060c3d52aaad0ba060eaa8387061c187aaaa1f77aa5555555541bdd55955665547a4d51e8f543ac8b56655551515555555551522f1503c78f1e1c1830f54aaaa1f53e8aa0c3830f42c5c3eeec0e0f4aaa1c383060c1870e2c5aaaaaaaa0deeaaaaaaaaaaaaaa2a2a931e3c987060c38ba169cb9b1397362aaa830e0c3d0b170fbbc0e0f5070e0c183061c38b162d555506f755555549aa3d50ea2d595168b5545aaaaaaaaaaaa2a2aaa2a131e3c987060c38ba162c58b0597162aaa87d53a2a830e0c39f3e7cf87060c3aaaaaa80000000000000000042e061c187a83c0ea1f77aaaaa9555555555498f1e4ea4f17a0e0c187aa5555545455555555061c18787dde858b81c1ea0e1c183060c387162c5aaaaaaaaaa8f1e3c787060c38ba162c58b4e2cb8b16aaaaaaaaa8a8aaab42e8183aaa0e1c187061eaaa87ddea955555555562f55271e3c78f0e0c187aa5554545555555555061c187a162e1f7781c1ea0e1c183060c387162c5aaaaaaaaaa931e3c987060c38ba162c58b4e2cb8b16aaaaaaaaa8a8aaaa0c3830e1c1830eaaaaaa9d3a74e1c1830e9d3a74eaaaaaaaaaaaa0c3830e1c1830eaaaa837baaa4d51ea87516acaaaaaaaaaaaa2a27369cd87060c3a7369cdaaaa8a9d154387162c58b161c183060c183060c183060e170ba5a06c0e064d1e8396941a0d06c9347b0cba432e80d068b655498f1e4cd97361b2e6c060c1831742d366d4d9b4187060c783ee0c183060c18385c2e818ba060e0703164c58b163c58b060c183060c58b060c583060c183060c183060c1aa4d1e8306a0d5a8341acf7a5a89a3d060d01c740683458b6458b4168aa4c78f260c183019b0603060c18ba162c58b059b1626cda9b36830e0c38b162c183062c5870e0c183061c3c2e170383d2d0747a3d0e8343cb4a1d91e8f43a0d865d2197416caa8f1e3c787060c39f2e6c3e5cd82e85a6cfa9b3e831e0fb83061c383060c3870f0b85c0e0f41c5d070e2c78b162c78b161c383060c1870e1c3870e1c38b161c38b0e1c387547a3d0e83438750ead59ef4b50f47a1d06870e81e3a0b16c8b1682d15478f1e3c383061c3870e073e1c1742c58b160b3e2c4d9f5367d0e1c58b161c58b060c183060c183060c183a06d2c2e170381d283947a3d068341acb0cba432e83d1e8341a2c5b43554d97361b2e6c1e3c78f060c1831742d366d4d9b41830e0c183060c183063c1d030740c5c2e17038183062c183060c183060c183162c58f162c58f162c183060c183060d506ad418351e8f41a0d67bd2d40e3a030683d1e8341a2c5b22c5a0b455066c180c183078f1e3c183060c5d0b162c582cd8b1366d4d9b41830fde070383878387060c183060c1830e1c3870e1c387541a0d0e8759ef4b50341a1d0e8b16c8b1682d154183060c3870e1c5d0b162c582cd8b1366d4d9b4187061c183162c58b160c387060c1830e1e170b81c1e9683a4d1e8741a1e5a50ed49347a1d06c32e90cba0b16d0d55263c7930e0c1875e5cd8bcb9b05d0b4da7536bd060c387063c183060c3870f0b85c0e0f41c38b1707a0e1c593162c58f162c387060c1830e1c3870e1c387162c387161c3870ea9347a1d06870ea1d5ab3de96a268f43a0d0e1d03c74162d9162d05a2a931e3c987060c3870e1c0ebc382e858b162c16bc589b4ea6d7aa931e3c993064c393064c3c2e1742c58b1713a162e170b164c593162c58f163c58baa162c58b163e858b162c587160c583161d557ba3d51eaaabdd959555454555555454555263c793264c984d393139f4e7c5d0b162c582d38b1555551e0c7871e0c7871e3c78f87d0b1742c58b170b85c2e162c7d0b162c5d50b162c58b1e2c98b162c78b1e2c58b0e2c18b062c3aa8f51eaaf75557bb2b2a8a8aaaaaaaa8a8aa3cf8f078f1e0f1e3c79f3e7cf8ba162c58b059f162aaa830e0c387261c3871e1c3ab0b85c0e0f41c38b1707a0e1c593162c58f162c3870e1c183060c5830e1ea8183060c383a0e1c38755555ee83541aaf7656555555151555515155539b4e6c383061c3870e074e1c1742c58b160b4e2c5555060c18f060c193060c18356170b81d030740c18b1703818b262c58b1e2c5830740c18307540c1870e0c18b0e0c183060c18306aaaa0d41aabdd5eecacaaaa2a2aaaaaa2a2a9b366cd83360c060c180c183062e858b162c166c58aaaa1c18f07dc183060e1703263c793060c18356ac1972e0c183060c18341554444168b54185c361b1363c1f7061c1830e1e17071e3c78f0e0c1870e1c38756ac3972e1c38741554444168b54385c3e1f13e0c383060c18f070385832e5c183060c18306ad58f1e3c783060c1a0aaa2034b8a02d16a970186c3626c187ee1c383060c1870e1c3a0a20350e2d16a9b0d89b 24 16777215 10 1023
def hc_62_17 : Nat → Nat := unpackHintV5 0xe7d326e17996dd410ed7dd59cfae0cc92da0c41546bd3db6b7497daea629a98d46a26dc8a15c449c05569601818d323488054b8139b37772726f2a1269fd4b5ccf4c55b1c74c32604422043a9e6135714b27378f1a9f260daf3c0729a10001ca 0x15063c1830e1c1830e1c387061c1870e3c1830e1c387060c1830e1c3870e3c3930e1c38f0e3c387547c3c58f878b1e3c78f0e0c1870f07161e0e1d1ea3d55eeaf741aa0d5554545555545455551e7c783c78f078f1e3c383061c3870e073e1c3e6cf9b5555061c1872e4d58f2e3d5935045471d1c70e0c1874717165e562d5555514155110e2287511150b85c0e030bb302ecc0b85c441005d0707131e3c9d5339f172f5208fbbd5554a74180c82e2311905c0e1c387369cda3061c1872e4cb8f2e3cb935000467cfaf0e0c1872f17165e2e2d545401415400002e0000000000000000000030e0c397267c7971ecc9a80303a7cfaf0e0c1876717165e5e2d3a7d0e834b834060c13a9d2e170380c2e05d98170b8885c2e070e0303870e1cb85c4365d3806c66030e0c387261c3871e1c3aa1c1830e1e0e2c3c1c3aa0dee0c1a83060d543a0d0e1d03a2aa9b361c1830e1c38703870d9b4da75368b16aaa0c18307540c1d352ad2d52aaaaaaaaaaaaa2a2aaaaa931e3c99b2e6c365cd80c1830754aaab0b8183060ea0703a87ddeaaaaa55555541bdd555526a8f56655655506b2b2aaaaa8a8aaaaaaa8a84c78f2751178060c183aa55544da2a83060c1cc2e070355a5060c183060c183162d555555555555555555551515478f1e3c183060c5d0b365cd86cb9b15554183060e1f77a162e0703a8183060c183060c58b16aa837baaaaaaaaa3d51ea83516aca8b45aaa2d5555555555515155515078f1e3c183060c5d0b162c582cb8b15551368aa2c5aaa83075540c183074aab4d54aaaaaaaaaaa8a8aaaaaaaa6cb9b0d97360f1e3c783060c1d52aaad0ba060eaa8187060c183aaaa1f77aa55555541bdd5555955665547aa3d506b2b2aaa8a8aaaaaaaaa8a9178a81e3c78f060c183aa55544da2a83064d060c5aaa6cd83060c1c2e6070395060c183060c5aa935541a8b55555555555555263c793060c1831742cd9b366d54daaa0c183070b981c0e9554183060c183060c58b55555555555555555555545455263c793060c1831742cd97361b2e6c5555060c183a162e1f7781c0ea060c183060c183162c5aaa0deeaaaaaaa8b5526a8f541a8b56545a2d5516aaaaaaaaaaa8a8aaa8a84c78f260c183062e858b162c165c58aaa89b455060c183060c1835541bdd555526a8f541a8b56555555555555150d9b366c183060cd9b366d5551368aa0c183060c183060c18b174b355555555544d1e83643875a599268f41a0d465d119749955263c793060c183365cd86cb9b2a9366d4d9b61703060c783060c9d5503a060ea8183060ea0703a561f77aaaaaaaa070baa268f69656a0c187060d506f799268f6924680d1a030680d06ccaa931e3c9d446e019b0603060c060c183aa4d9b5366d060c183060e81c0c18306a0d060e1e0e162e0703a060e858b1e8f41a0d0e1d4587516c8f47a0d06bf2e8fcba0b655478f1e3c183060cd97361b2e6c1742d366d4d9b418f063d6070b18065cb83060c183060cbb7060c1831608341abdd551e0d2e280345a2d52e030b85c4b83060c7831e0c1831e0c983060c1ab0fbbd0b1740c1d03170381d40c18b060c183060c183060c58b060c183060c183162c58f47a0c187060d506f716c8b16a2d5a8f47a0e3a030680d068b6458b4168aa3c78f1e0cd8301830603060c18ba162c58b059b1626cda9b3683060c183062c583060c1d2cd5550fbbd555550f47a0d650e1d696647a3d068351974465d2655478f1e3c183060cd97361b2e6caa4d9b5366da1740c1d555503060c18f060c18f81d540c183060d5aaaa1f77aaaaaa95ad28f47a0c187060d506f79991a520f47a0d1a030680d06ccaac6e2a078f1e3c19b0603060c060c183aa4d9b5366d060c1830703060c1d0306a0d060e170381c0e8183a162c9a3d068343875161d45b24d1e8341afcba3f2e82d955263c793060c183365cd86cb9b05d0b4d9b5366d060c183060c983ee0c18306ac2e0703060e060c5f781c0e4793060c183060c18b0e0c183060c18357dc5b0b268f41ab418341a0d16cab55a4c78f260cd83060c183060c18ba166cd9b369b36831e0c9ac0e17020cb97060c183060c197b60c183062c1068357baa935401a0c418b45aa5c06170b897060c18f063c183064c193060c18356858b87dde0740c1d03062c5c0e07503062c183060c183060c183162c183161c183060c183060c58b164d1e83061c183541bdc5b22c5a2d458b56a4d1e838e80c1a0341a2d9162d05a2a931e3c983360c060c180c183062e858b162c166c589b36a6cdaa83060c7831e0c183260c983060c1831e0c383060c1830e0c383060c183060c9830e0c183060c1aa4c78f264e262c9c4c58381830703160c18306af747aa3d41a83557baaaaaa2a2a2a2aaaaa931e3c993264c266c980cd8301830603060c19b366cdaaaaaa0c183060c3830e0c183060c7830e0c1831e0c783060c783260c183060c183060c7830e0c18306a8f878b1f0f163c78f1e0e060c1c0c583060c1a3d47aabdd06a0d55eeaaad545455545455555551e6c783c78f078f1e3c19b0603060c060c183366cd9b5536aaab265c7ab1e5c983060c1a82a238e8e397958b4717160c18306aaa0a8aaaa88a0d45062228a85c2e173605cd8030185c2e22081b0183063c183064c183060d50703060e062c183060d41830e0c1aa0deeaa0d0183406835554d9b366c19b0603060c060c183366cd9b4d9b5366d 24 16777215 10 1023
def hc_62_18 : Nat → Nat := unpackHintV5 0xe1fe61dcd14bce978fc811a1c0e9cabbad4fb461d3ae5d81a55a41a041469879f291d1aa8902348630b481852b7b498f76553d70198f6cc8d4678d4f60d1af5af17851aa52499a04446d4b37af3030e1b32762601f1a1219ed4b0cbf4c00032f 0x5418f0e1c1870e1fb830e0c3c3c58b858b17de170b81c1c78f0e1c3870e1c38f1e3c7871e3d5f79061c1b0b1ead1e3d1e8f43a0d16cab55a3cf8f1e3c78f1e3c787060c38ba167cd9f369b3ea830e0c3c2e163cb971e3c78f1e3c797ae3c78f1f020c11e8f57baaa80f4788f0e8b43aa5c1e170b8975418f060c387060c3870e1c187061e1f42c5d0b162c5c2e1740c1c0eee1c7870e1c3870e3c38f0e1c3870e3c3930e1c38f0e3c387a8183063c7931e3d51ef70e8345b21c3a1d438756a3e3a0f1e83d1e8741a2d90e1d03a2a8f3e3c1e3c783c78f1e1c1830e2e85870e1c0e7c389b3ea6cfaa0a85c1ab0eac1970e3c78f1e5e562d1c5c58f1e3c7a38e8e3a82a2aaaaaa3d451e22288a2a173e05cf80f0785c2e170b888207c547831e1c7831e1c78f1e3c7c3c58f878b1e3c78f1e3c98f1ea8f7baa8f41e3d07a3d55551e7c783c78f078f1e3cf9f3e7cf9f3e7d3e7d4f9f4187061c993aaa0e1d556a981d4ab4aaaaaaaaaaaaaaaa8a8aaaa4c78f261c1830e9cb9b139736552aaa830e0c3c4ea1f507aaa0777aaa9551ef75555555549a8743aa0d06accaacaab2b2aaaaaaa8a8aaaaa8a84c78f261c1830f51178aa55550daa7455060c18385c2e9a064c983060c18306ab4a1c3aaaaaaaaaaaaaaaaaaaaa2a2a931e3c983060c18ba166cb9b0d97362aaa83060c1c2e1703bbd03060c983060c783075030e0d551ef75555555549a83541aa2d16acca8341aaa0d5555555555515155515098f1e4c183060c5d0b060c180cb831555436a6d156aa8993060c183060d556aa955699555555555555515155555498f1e4cd97361b2e6c060c183aa5555a87c3ea2713060c183a075555540eeeaa8f7baaaaaaaaa4d655599550687541a0d5916accaaaaaa2a2aaaaaaa2a131e3c9c5e2a0183060ea9555436a6d154187061e170ba060e077749930e1c3870e1e95541835555547bdd55555555555555545455263c7930e0c1871742d39736272e6c5555061c18785c2e818381ddc3930e1c38f0e1ea060c1aaa3deeaaaaaaaa9350ea83545ab2a1d0eaa8755555555555454555454263c7930e0c1871742c3870e072e1c55550daa7455263c793263c793366cd9b555555000000000000000000061c18789d43ea0f5540eef5552aaaaaaaaa931e3c987060c3d49e2f554aaaaaaa8a8aaaaaa0c183070b85c0eef40c183260c1831e0c1d40c3835555555555263c793060c1831742c183069c197060d5555555551515556a1f0fa89c4c183060e81d5555503bbaaaaaaaaaa931e3c9c5eaa4e0c1830754aaaaa8a8aaaaaaaa0c3830f0b85d030703bb87261c3871e1c3d40c1835555555555263c7930e0c1871742c3870e9c3970e1d555555555151555498f1e4c98f1e4d55555498f1e4d3a74e9d3a74e9d55555555555498f1e4c98f1e4d551ef7555549a87541aa2d5955555555555454263c7934e7d39f4e7d39f5555153a2a870e2c5870e1c3d2d4830e0c3d5555555528306a4d1ec836651974465d09a3d0e8366555d97363b2e6c263c7930e0c187aa4da75368d1602c187061c9871e1cb87761c3872e1cb870e1d622a8ba5d06f70683065c2e070b84c9d070e1c3870b870a2e5cb9785c0c3830f50781d07261c3871e1c3d55070f41ea9587ddeaaaaaaaaa268f69656a837b8306a0c18399268f6924681d06870e81d1a4caa931e3c9d4501c1830e1c38703872a9369d4da343870f5070e0c3830e0c1a83061d83c2e858ba0e1e07071e8f45835060d43a0d16c8f47aecba3b2e81d068b655478f1e3cf97361f2e6c0e0c1871742d367d4d9f47871e1d61707180e0c1870e1c3872edc3972e1c387160af706835551e1d0e871405a2d50e170b85c4b830e0c3871e1c3871e1c3ab0fbbd0b170383d071741c3d41c383060c1870e1c3870e1c38b161c38b0e1c387162c58f47a837b8306a0c18316c8b16a2d5a8f47a1d06870e81e3a0b6458b4168aa3c78f1e1c1830e1c387039f0e0ba162c58b059f1626cfa9b3e870e2c5870e1c3830e0c3d4d2d55555550f47a0c1ad2ca0d6647a3d465d119740e836655478f1e3cf97361f2e6c0e0c187aa4d9f5367da1703aa83830e0c3d07aaaaa0e1c38f0e1c38f0e1d5aaaa1f77aaaaaa95ad28f47a837b8306a0c1839991a520f47a1d06870e81d1a4caac7e2a078f1e3c383061c3870e073e1caa4d9f5367da0e1c3870f030e0c38306a0c18761707a162e838781c1c9a3d160d418350e83060d16c9347aecba3b2e81d068b655498f1e4d797362f2e6c0e0c1871742d369d4daf49871e1d61707810e0c1870e1c3872eec3972e1c387160af706835549a83500e9705a2d50e170b85c4b830e0c387261c3871e1c3ab42c5c3eef0383d071741c3d41c3870e0c183062c1870e1c3870e1c38b161c38b0e1c387162c59347a837b8306a0c18316c8b16a2d5a9347a1d06870e81e3a0b6458b4168aa4c78f261c1830e1c38703af0e0ba162c58b05af1626d3a9b5eaa0c3830e0c1870e1c383260c1870e1c987261c3871e1c7870e0c183061c3870e1c783061c3870ea931e3c993898b2713161c1830e1e0e2c3c1c3abdd1ea8f55ee83541aaaaaa8a8aaa8a8aaaa4c78f264c99309a72607060c3870e1c0e9c389cda736a6d555 24 16777215 10 1023
def hc_62_19 : Nat → Nat := unpackHintV5 0xe08e04db614bcea330c7d5b3be5660b60e12b0e14ba3b34c9d599699210e93bd598b8e0c850da07ff546791db673297d6a8629656d465e4dc85d3c4457e55651e18149123443e54b3d19b33352722b0a1225dd4b18af4c1191c7081260000204 0x306a0c18341c0c1d03060c1830741c3d0b0f0b85c0e060c1a8f1ea0d1e8341a2d96e5d1b974268f41a0d16caa9b2e6c365cd84c78f260c183062e85a6cda9b36a83060c1c2e164c78f264c993265db932e5c99326301c15ee3d1eaa9349a4c50418b41aa4c2e170b89754183060c183060c183060e170ba162e858b81dde8183064c183063c183064c193060c183064c183060c1d40c38347bdc78f51e3c78341a2d9060d41ab5268f49934271d01a0d16c830680d15498f1e4c9932613364c060c1831742c1830603360c4d9b5366d060c1839aa5060c183060c183aaaaaaaa947a8341a3c7ad2cc9347a0d06a32e88cba4caa931e3c983060c19b2e6c365cd9549b36a6cdaad43ea275513aaa2713060c183060c183060c183a0755555555540eee8f7b8f1ea3c78f95ad28341b324d1e932684d1a48d2901a0d9955263c793264c984cd932371500c18307549b36a6cda1c3a870e1d060e81830f030e0c3d030742c1c2e170383870ea3c7a87478f1e8741a2d96e5d1b974268f43a0d16caaaf2e6c5e5cd84c78f261c1830e2e85a6d3a9b5ea830e0c3c2e164c78f264c993265db932e5c99327020c15ee3d1eaaa3d409a5c0e8b43aa4c2e170b89754187061c1830e1c1830e1e170ba162e858ba060e07770e4c3930e1c38f0e3c3870e4c3930e1c3870e4c3870e1c3d40c18347bdc78f51e3c78741a2d90e1d43ab5268f49934271d03a0d16c870e81d15498f1e4c99326135e4c0e0c1871742c3870e075e1c4da7536bd5045263c793560cb872e0d587263c7934717165e562d1c7471d555141555526229351111150983c2ecc0bb302e170b85c4410104187061c9c3e674fa8bc5ea0f5503bbd50f07929d462320b84c9932705c369cda35000263c7932e0cb872e0cb87263c7932f17165e2e2d19b36bc5401415554002e000000000000000000000280f09a4c78f266c1970e5c1b30e4c78f26ce2e2cbcbc59b36bc9a3d2e3d078f04e9b53a9d260f0b8176605c2e170b8884c983c264c9932e170b85c43e5d3807c662a4c78f264c1930e4c1930e4c78f264e262c9c4c5a3dee3c7a8f1e3d549a3d264d09a2aaa931e3c993264c264c3e7cf9f4fa753e830e0c3d50f1f41c3aaad5352ad2aaaaaaaaaaaaaaaa2a2aaa8f1e3c787060c39f2e6c3e5cd954aaaa0c3830f0fa87d41eaa81ddeaaa47bdd55555555551ea1d506accaacaab2b2aaaaaaa8a8aaaaa8a83c78f1e1c1830f51178aa55544fa2a83060c1c2e17303060c1831e3c18355a50e1d555555555555555555551515478f1e3c183060c5d0b365cd86cb9b15554183060e170b81dde8183063c183063c183a8187068f7baaaaaaaaaaa3d41aa0d516aca8341aaa0d5555555555515155515078f1e3c183060c5d0b060c180cb8315551368ab43c7d503060c18306aab554aab4caaaaaaaaaaaaa8a8aaaaaa3c78f1e6cb9b0d973603060c1d52aaad43e1f50f8983060c1d03aaaaaa077747bdd55555555551eb2aaccaa83541ab2b2aaaaa8a8aaaaaaa8a83c78f1f178a8060c183aa55544da2a871e1c38745aaa7cf830e0c3c2e170391e3c38f1e3e541aa8f50eaa8b555555555555551e3c78f0e0c1871742cf9b3e6d54faaa0c3830f0b85c0e43870e1c78f0e1e9554183555555555555555555555454551e3c78f0e0c1871742cf97361f2e6c5555061c18785c2e818381ddc38f0e1c38f0e1ea060c1a3deeaaaaaaaaa87551ea1d506a8b56543a1d550eaaaaaaaaaaa8a8aaa8a83c78f1e1c1830e2e85870e1c0e5c38aaa89f4551e3c78f1e3c78f47bdd5555551ea1d506a8b5655555555555515078f1e3cf9f3e7cf9f3e7d55513e8ab4b340c3830e0c1870e0c1870f5555555543d9264d6943a0d991e8f51974465d03a0d99551e3c78f3e5cd87cb9b0383061ea9367d4d9f55060c387060c387061c18787d550f87d543ea1f507aaaaa1f0baa81ddeaaa1e3c98f1ea8f7b8741b4b2b5991e8d078f41e8f43a0da491a4caa8f3e3c1e3c783c78f1e1c1830f511f8aa4d9f5367d060d41a0c183060c1d03060e060e170ba161e8387818381831e8349935060d41a0d16c8f47afcba3f2e80d068b655478f1e3cd97361b2e6c060c1831742d366d4d9b54183060e170b1e5cb8f1e3c78f1e3cbbb1e3c78f180e08f47abdd547a5c501ea0c5a0d52e0f0b85c4baa0c183060c183060c7830e0c1830742c5d0b170b85c0eef40c1831e0c183060c18f063c183060c18f060c18f060ea061c18f1e4c78f547bdc1a0d16c8306a0d5a8f8e83c7a0f47a0d068b641834068aa3cd8f078f1e0f1e3c783060c18ba160c183019b0626cda9b3683060c1d2cd03060c183060c1d555503bbd5550f5941a0d264d696647a3d068351974465d2655478f1e3c183060cd97361b2e6caa4d9b5366d56aa1f0faa87d50fa8783060c183060c183060c1d03aaaaaaaaaa07771e3c98f1ea8f7bcad6941a0d991e8d078f41e8f6469480d06ccaa8f363c1e3c783c78f1f1b8a8060c183aa4d9b5366d0e1d43a1c3830e0c383061e060ea170ba160e818381c1c7a1d264d438750e8345b23d1ebf2e8fcba0741a2d9551e3c78f3e5cd87cb9b0383061c5d0b4d9f5367d 24 16777215 10 1023
def hc_62_20 : Nat → Nat := unpackHintV5 0xcd21d9c6bd99c0bd80bdb4c2b76195b18d75a9b9f5a42d639cb1df94461b8d51bd86fd957f61e779897673b5756be1f5660d755e91df56261b4ec1d9485d99425d803f54c2390195332d752b59f525cd631e51df15e61b0f29af094978000252 0x2c5a8f163d560db876e0d5871e3c78fa5a9aaaaa87a3c78f55aad9a9468d11a341e8f51a8d99546a8cf9f3e1f3e7c1e3c78f3e7cf9faa4f9f53e7da1703aa838f1e3c7d5550fbbd553523c78f1f55238a81e3c78f468d1a3aa468d1a38fc540f1e3c79f3e7cfd51f3e7cf9f3e7cfc8f260d5ab060c18316c2c9a83060c5a830e0c39326ac183060c58b162c183068b06aad5683158ad59b366cd830d86cdc8f261c1830e2d8583365d793260c18b162c583565d2eab5723c9870e1c18356ac5b0b26a1c38716a1c183064c987060d5ab162c58b0e0d438b16ab55a1c562b56bcdab361c387c3af17ab263c79385cc2e164c9aaa970e5c197065c38b16aaaaaaaaaa0a8889711444ba8a84c1e170b82c82e5c0b97044102e131e3c9c2e170b85d28f49cac383560c38b16b22c593268f49ab55a2c5b22c58b164d1ea8b655a2b455263c7935e7d79f1742d7af3e2b5e7c579f4ebd4faf498f1e4e1730b85932608a5c397065c1970e2c5822aaaaaaa5d4444445050514260f0b85c164172e05cb82200131e3c9c2e170b85d00f09c5c3db065c1db0e2c5840b164d1ea8b64ba975264c1e132e232e0b1640b162c5a234260f0b85c164175e05d782170460bc263c793a162e1f7785c2ea161c583160c587162c5931e3c98ba162c58b458b498f1e4d1a31742c58b160b1623464c78f26bcfaf3e2e858b162c16bc58bcfaf3e8cfaf3e0c3830eac9c31eac7c3261c3a834387aaaaa9a556ab438741a1ea9a946a343a0d468d11a349955366c383061e1b3362b666caa4da75368d061c1872e4cb8f2e3cb930e1c0181c3d5555450174ba1d06972e5e64b85c0e030b9702e5c22110b85c0e0328282212e172e00030e0c397267c7971ecc9870e00c0e1eaaaaa280b9f2e1c1830e5cba5d9976a8b85c0e030ba302e8c220b85c2ecc2e1b0e1c0607aa2a0b86cbb300d88c061c18789d43ea0f5540eef55507060c3d4d3548d1a3461c1830f51238aa468d1a3366c383061ea28aa366d19b466c183060e170b98197265c7971e5c9aa8306a2c5aaaaaaaaaa82a2220c45112ea2a170b80c060b20b9702e5c11040b80c183070b85c0e06ac9bb1eac7bb260d0752870eb22c3ab55a0d060c1a2c5b22c18306a0d068b655a2b455366cd9b060c1831742cd9b361b366c4d9b5366d060c18385c2e6065c9971e5c797268a0c180b1608aaa8355554ba888888a0a0a285c2e030182c82e5c0b970512e0003060c1c2e1703819726ec7971eec98301d401c3840b0ea0d068b64ba9752e1711830183060b1640b060c1a2342e170180c164173605cd821703606c060c18385c2e0777a060c193060c18f060ea061c183060c18ba160c183418351a3060c1831742c18306030623466cd9b360c183062e8583060c066c186cd9b366cd9b36ec9ab1eec7ab260c183060c1a83060daaa5a9aa56ab6a0683060d9a946a351a34468d01a0d99546a8cd9b366cd9b361b366c060c183aa4d9b5366da87d44c183060e81d5555503bbd3520c18307548d1a347238a8060c183aa468d1a3366cd9b8dc5403060c1d51b366cd9b366cd8f56ac78f1e3e418706c2c78f0ea1c5a8b263c9ab0e3c78f0e1c58b0e1c3870e870eaad568f158ad59f367cd8f0f87cf931e3c3c830e0d858f365d78f1e1c38b161c38f565d2eab564c9931e3d5ab9061c1b0b264c3a8716a2c78f1e4c78f56ac387162c3870e3d43870eab55a4c562b56bcdab364c986c9af17ab061c18785c2e0725c9971e5c797261c3aaa8b16aaaaaaaaaa0a8971144444ba8a85c2e070182c82e5c0b97044102e030e0c3c2e170383ab263d58f274a0d0f0306b22c1ab55a1c3a0d0e2c5b22c3870ea1d068b655a2b4555e6d79b0e0c1871742d7af362b5e6c579b4ebd4daf4187061e170b81c97265c7971e5c9870e08a2c5822aaaaaaa5d44444450505142e170380c164172e05cb82200030e0c3c2e17038397275c7971f5c9d00303c0c1840b06a1d068b64ba9752e232e070e03038b1640b0e1c3a2342e170380c164175e05d782170460bc061c18785c2e818381ddc3930e1c38f0e1ea060c187060c38ba161c387438751a30e0c1871742c3870e070e2346bcdaf361c1830e2e85870e1c0ebc38bcdaf368cdaf374b520c1870e0c1870e0c3830f555555554a3c7ac8f43a0d99465d11974268f43a0d99556e5cd8dcb9b098f1e4c383061ea9369d4da354187061c98f1e4c993264cbb7265cb93264c3807aa881ef71e8f1e5d2e930b85c2e13264c9930b9300e1ea8b972e5d5061c187060c387060c38789d43ea2713aa89d5507aaaaaaa0777aaa91ef71e3d478f1e1d06d2cad6649a3d264d09a340e8369246932aa4c78f264c99309930383061ea28aa4da75368d 24 16777215 10 1023
def hc_62_21 : Nat → Nat := unpackHintV5 0xe24a2edc8172d489fecb8a40c57984bcc22eb6f972af01fea60240a0157b97263c904db6881e0c7f3a3979f95073e9846b6a206559845d61fe5569fe4fa1724642583e2208372dbd30d995293de72365761d917515bdf50fe975086ddf00021b 0xe1d47a4c383060c183060d060d498f1e4ddcac5ab9d8b060c183264d1e93060c183418306ab55a4d1eab45680d06bf555263c793366cd86cd9b0183060cd9b366d366d4d9b4993045418306a80c18131e3c9978b8b2f17160c18306aa97555551141411111450983c2e5c0b97006030b85c44000e1c0784c383060c183060c060c098f1e4d1c5c5979d8b060c183268f4ba975068363a8d264c1e13060c183018306170b8884c1e173605cd8030185c2e217000187060c783ee0c183060c183263c7930703160e060c183060c98f1e4c18306830683060c1931e3c983060c060c060c183263c793060c180cd830183060cd9b366cd9b366cd9b366c1a0c3aa8f1ea1c3aaa8f1e3c787060c3978b8b2f1716aaaaa0a8aa8f11444ba888a83c1e070185cb8172e05c2e2208170187061c7a3c18306a1c3a8343871e3c78f0e0c1876f2b16ae6e2c7a3c78f438741a1c3870ead568f47a1d06ab4568fd55478f1e3c383061cf9f361f3e6c3e6cf9b4d9f5367d06830e8a3c78070e08a3c78f1e1c1830e5e2e2cbc5c5aaaaa5d5544445050445141e0f0380c2e5c0b9702e1711000187061c783c1830601c380303871e3c78f0e0c1874717165e6e2c7a3d0e834ba9758ea34783c78f03870181c3870e5c2e220f0781c06173e05cf8170b885c00063c1f7060c387060c1870e1c78f1e3c383061c3c1c58783871e3c78f0e0c1870e1c3a1c3a3c78f1e1c1830e1c3870387078f1e3c383061c3870e073e1c3e6cf9b3e6cf9b3e6cf9b1e3d554183555060d065e2e2cbc5c58f1e3c783060c1aa282aaaaaa5d4444444542e5c0b9701e0f0180c2e1711040b81c3a8f0e3d060d41830683060c1ab9b8b6f2b163c78f1e0c183060c1831e8f1e3d0683060d56ab55a2b41e8f41a0d7eaaa6cd9b0d9b360f1e3c783060c19b366cda6cd9b4da6cda3c782a03060a80c1a0cbc5c5978b8b1e3c78f060c1834baaaaaaa8341828888888a5c57b8a25cb976605cb85c0783c06030b85c512e00070e03c38f01830060c180c183065e6e2d1c5c58f1e3c783060c19752ea3d1e8341b1d4683060c783c78f0180c1830b85c442e6c0b9b01e0f0180c2e1710b806c0d83061c183060c183060c7830703060e062c78f1e3c183060c1834183068f1e3c783060c1830603060c1e3c78f060c183066c180c183078f1e3c183060cd9b366cd9b366cd9b366c1830fdc183060c3870e1c183060c3870e1c183060c3870e1c183060c3870e1cd9b366cd9b366cd9b366c187069326aaa1c3aaa931e3c987060c3978b8b2f1716aaaaa0a8aa88889752e228a84c1e070185cb8172e05c2e2208170187061c18351e93061c3a834387263c7930e0c1877f2b16ae7e2c99347a4c38741a1c3870ead569347a1d06ab4568fd55498f1e4c383061e7b3362b666c7e6cda6d3a9b418706932608a1c3822931e3c987060c3978b8b2f1716aaaa97556aa8888a0a08a5c514260f0380c2e5c0b9702e1711000187061c18301e13061c38030387263c7930e0c1874717165e8e2c9a3d0e834ba9758ea349930784c3870181c3870e5c2e22130781c06176605d98170b885c00061c187264c0784c9870e00c0e1c98f1e4c383061cbc5c5978b8b268f43a0d2e5cb974ba4c1e070185cb8172e05c2e22130781c06070e01c38170b8970b970001870613260001c3800131e3c987060c3978b8b2f17164d1e8741a5cba972ea5d2e800005c0000000000000000000061c187060c0784c1870e00c0e1c98f1e4c383061d9c5c597978b263c7930e0c1872e5d2eccbabcb97260f0380c2e05d98170b85c2e13260f09870e0303870e1cb86cbb30b86cbb300d8cc060c387063c183060c3870e4c78f261c1830e1e0e2c3c1c3931e3c987060c3870e1d0e1d263c7930e0c1870e1c381c384c78f261c1830e1c38703870d9b366cd9b162d47a4c5931e3c9c306ac3ab070c3d554d2d513268f49d4ad56cd49347a8d1a234688d46ccaa931e3c9c3667c56ccf87cfd527d3a9f46932603c264c98f1e4cb832e1cb832e1eaaa282a89a3d2e5cb974bb324c1e172e05cb8170b910884c1e5050170b910970b9700058b01e13164c78f266c1970e5c1b30f555141544c78f265cba5d9974b9b2f544c1e174605d18170b9105c2e13260f09d45d985c3f1505c3e5d9807c4642e263c793a83c0ea1f77aaaaa898f1e4ea69aa263c793a891c23468d1d523468d1931e3c9d4507cfd51f3e8cfa33e3c78f1f30b85c2d5478f52e1cb832e0cb87162d55555555541511e228888975150783c2e1705905cb8172e088205c1e3c78f85c2e170b1e8fa955876e0d5836e1c58b59162c7a3c78f55aad162d9162c58b1e8f545b2ad15a2a8f1e3c79f3e7cf8ba167cf9f0f9f3e27cfa9f3e8f1e3c7cc2e170b451e3c0b872e0cb832e1c58b04547aaaaaaa5d44444450505141e0f0b85c164172e05cb8289700078f1e3e170b85c2c783ea02e1db832e0db87162c2058b1e8f545b25d4ba8f078f1e170b88c58b2058b162d11a0f0785c2e0b20b9f02e7c10b81f03e0f1e3c7c3eef42c5c2e1750b0e2c18b062c38b162c78f1e3c5d0b162c5a2c5a3c78f1e8d18ba162c58b058b11a31e3c78f3e7cf9f1742c58b160b3e2c3e7cf9f3e7cf9f 24 16777215 10 1023
def hc_62_22 : Nat → Nat := unpackHintV5 0x184 0x264d555060c1aa8306a4c78f265e2e2cbc5c583060c1aaa82a2aaaa225d4188a222a130785cb8172e00c06170b888205c 18 262143 9 511
def nh_62 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_62_22 (Nat.sub p 704)) (hc_62_21 (Nat.sub p 672)) (Nat.blt p 704)) (hc_62_20 (Nat.sub p 640)) (Nat.blt p 672)) (Bool.rec (Bool.rec (hc_62_19 (Nat.sub p 608)) (hc_62_18 (Nat.sub p 576)) (Nat.blt p 608)) (hc_62_17 (Nat.sub p 544)) (Nat.blt p 576)) (Nat.blt p 640)) (Bool.rec (Bool.rec (Bool.rec (hc_62_16 (Nat.sub p 512)) (hc_62_15 (Nat.sub p 480)) (Nat.blt p 512)) (hc_62_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (hc_62_13 (Nat.sub p 416)) (hc_62_12 (Nat.sub p 384)) (Nat.blt p 416)) (hc_62_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 448)) (Nat.blt p 544)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_62_10 (Nat.sub p 320)) (hc_62_9 (Nat.sub p 288)) (Nat.blt p 320)) (hc_62_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (hc_62_7 (Nat.sub p 224)) (hc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (hc_62_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (hc_62_4 (Nat.sub p 128)) (hc_62_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_62_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_62_1 (Nat.sub p 32)) (hc_62_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 352)
def f_62 : Nat → Nat × Nat := unpackForestF 0xafcaed78956bd4bb5e1550062fd74536b748b5c24dadca280316eb52cb5926dacd32d645b4018af54d64abca6d52916ad49b54945aa926d54536a908a00c53a952ad4c976a50aa00b5fa8c9ed408d6a147b50135005add3c9b4016af4cb5ba6c1a532d4e9927b4b235a5d1ed2c4d4016a749245a4d26d241140169f4813da351ad1c8f68d26a00b4ba2d2e802d1e866d744034a19b1d0c4f68346b4223da0c9a802d0e808c9400459cda7cfad927d26b39b4b9eeb44e6d1e786c93c1359cda1ce65567469f3a15d9cc2a80297e714a93445f9bd224d116e6d4d9344579ad1f4d2d1269489344530052dccd1f25b69f31b7c98c9acb6d2e61ae12db47975be4ba8d25d26b2db4396cb680295e594a92645f95d2249916e554d92645794d2249914e4c05126b4f935a5c9ad1e4d6872602400529c93192490cb1d36f919aa48c4d63a6d72247c8e9b3c82d524126b1d3638e937c7499e3a28b1db6f8eca6c741140149f1c2648be37c6c9122f8d71a27c8be33c648fa30689182448be3180292e2dad11036f8a9b64544d6206d714570881b3c48db22446912135881b1c409be204cf1015d00523c3c992118df0e24484635c349f2118cf0c24484631c220a2126bf0935b849abc24d4e1104800a4383db23fb5be0d6a8fed6b82dbe3fb59e08ce9043547f6b1bfa9bdfd4cefea5f7f52bbfd5bdfead6ff5677ff3a3fd58dfd26a00a3f7ed323e55bdf94a8f956b7dd3e3e559df3ce8f9b547cd2a3e558c01476f846877ab7bdd161dead6f647077ab3bd5181e5ce8f2c587952a3cd141e50aaef56377937bbc99dde4beef25777eb1bbc1340146eee26471eb7bb4951c7ad6ec27c71eb3ba99d1d5ac8ea25471eb1b9d17dce8b6e745773eb239d14dc7250e445f7222db9115dc9ac8e445371c920028cdc36c8e1a3570c9a368d2dc06c8e02356d1a1b68955bd8c8da24f6eab4374571b448edc3646d11fb6a975b549eda055004af80256db06f8d823568da5b58df1ac46ad613468da1b469b5a98f8d1a4f69eb834691da46f8d227c68d1f80255da0030d0014004a9b38d519c46ace13462db5b32d519946ac5b6365e323169bd948f8ca17c62d33b16915916a8c5a3f62cb7b1659d8c4dec624d62c2280253c01296c3b6c61d1aaf0dad836d8c1a3560c9a2f0d8d81ad0bc26f5feb82f099d784babdb6c5ed362f08fd782debc167004a3aea06175028009435a6b7ad35ad69aceb86745a6b1ad29bd6d2f8b4a675a52fad45b1694ae0093f59cb22bb5bd652a8aed6b5893e2c45f15daceaf6745792a2bc5515dac60093b56a342b49951aadeabc5855d2aa355ad5347eaa14c54d1baa11c1504faa817c46ab3a9a8fd4d46ea646051f3a28f161498a0a3a5551caa23558d458d08d26f4f5afa851b13d6b69eb574fdae27d1913d6a69e47046933a751611a4be9936f4de3e264dad326ce9a36c4ce3a264d8d318c08d2574a6b7a535ad29ace966744a6b1a529b9294bc8d24d48ab7a455ad22ace91e7448e2c24558d1a47a9025546eb1a369bd1b4be8e56346d22a341340126e8c16443eb7a2c5510fad68a17c43eb3a219d111ac88815443eb18024cd0d4c87cd6f42d2a1f35ad084f88417c3e6b3a099d1046a8822543e6b1a04910f98d67fb443fd221f318cfd4887cc5b3e9a21f4910f98a60092f3dcb21cd5bcf52a87356b3ccbe1cd59cefce877a543bcaa1cd58ce603073c5f39e2d9cf15ce8ac87414439e299cc0500125672364316b79c4d50c5ad67037c316b39b79d0db6a86da5436caa18b58cd86886c144316359a8d10d44886a144316319a2d10d128862c5b335a219a910cd28862c5331ab798d5acc6ace63e7431e2c18d58cc528c0092730cb21595bcc12a85656b2f93e17c5f0acace5d6742eeb2174550acac65a45f2d22d96915cb5ac85a4532b0a615b17cad8b65816c2b62b95d590ad8a65614400491954914a469e5224f2911b94853ca426e521270042f80216ca08f85024522da793ad3c9d2aa45a6d26a3e1349f08b49e4bb5f25da992d1c08b46e49a5524d279165b4908f84817c22ca791d1c08b26e4637c22c9380215c010a644265209b79049bc8246e4116f2089b90449c0109e0084b1fab40fc994696de3e5681a5378f0dbc784dc3c1451a52e8eadbc756c63a4601a51b8e55a0692de3726f1b9228dc5b8692ba364601a49b8d4db06924e00847004218ccd504aac632364129378c4d504a4be2fd6317ca68948d45d6c82516f16daa09457c598b028d63146318ad5c8518a628a6f1452f8a558c5149a2513512f39896d104dac625a4412ca209449c0107e0083b11d2a88958c444de2225f0041b8820b041048008330f9aa07c95039ac61e2640e637874950398be0082f0d81606c090010561a25408ab18451bc228be18264088b785c950222be165680a73985558c294b81114709e3e04cd3c220cc1256808db78441580104e008230792a03c5501dac60081f0040d832d54192a801d6305cb2006dbc152a801b5f04dac02558c0346c0745803e2801c9540aac60526f0292f8144980328c03a4f01c1b006198044de0203600c2b00205c010260003f 10 11
def ch_62 : Nat → Bool := dagCheckNodeV5 fullMask g_62 ep_62 5 31 bds_62 704 (dagTraceF fullMask rootStock 11 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 fullMask g_62 ep_62 5 31 704 bds_62 (dagTraceF fullMask rootStock 11 f_62) (cur_62 0) (nh_62 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_2 : treeBlockF 64 96 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_3 : treeBlockF 96 128 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_4 : treeBlockF 128 160 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_5 : treeBlockF 160 192 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_6 : treeBlockF 192 224 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_7 : treeBlockF 224 256 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_8 : treeBlockF 256 288 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_9 : treeBlockF 288 320 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_10 : treeBlockF 320 352 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_11 : treeBlockF 352 384 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_12 : treeBlockF 384 416 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_13 : treeBlockF 416 448 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_14 : treeBlockF 448 480 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_15 : treeBlockF 480 512 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_16 : treeBlockF 512 544 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_17 : treeBlockF 544 576 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_18 : treeBlockF 576 608 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_19 : treeBlockF 608 640 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_20 : treeBlockF 640 672 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_21 : treeBlockF 672 704 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 96 → ch_62 i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nj_62_3 : ∀ i, 0 ≤ i → i < 128 → ch_62 i = true := block_join nj_62_2 (fun _ h1 h2 => treeBlockF_at nb_62_3 h1 h2)
theorem nj_62_4 : ∀ i, 0 ≤ i → i < 160 → ch_62 i = true := block_join nj_62_3 (fun _ h1 h2 => treeBlockF_at nb_62_4 h1 h2)
theorem nj_62_5 : ∀ i, 0 ≤ i → i < 192 → ch_62 i = true := block_join nj_62_4 (fun _ h1 h2 => treeBlockF_at nb_62_5 h1 h2)
theorem nj_62_6 : ∀ i, 0 ≤ i → i < 224 → ch_62 i = true := block_join nj_62_5 (fun _ h1 h2 => treeBlockF_at nb_62_6 h1 h2)
theorem nj_62_7 : ∀ i, 0 ≤ i → i < 256 → ch_62 i = true := block_join nj_62_6 (fun _ h1 h2 => treeBlockF_at nb_62_7 h1 h2)
theorem nj_62_8 : ∀ i, 0 ≤ i → i < 288 → ch_62 i = true := block_join nj_62_7 (fun _ h1 h2 => treeBlockF_at nb_62_8 h1 h2)
theorem nj_62_9 : ∀ i, 0 ≤ i → i < 320 → ch_62 i = true := block_join nj_62_8 (fun _ h1 h2 => treeBlockF_at nb_62_9 h1 h2)
theorem nj_62_10 : ∀ i, 0 ≤ i → i < 352 → ch_62 i = true := block_join nj_62_9 (fun _ h1 h2 => treeBlockF_at nb_62_10 h1 h2)
theorem nj_62_11 : ∀ i, 0 ≤ i → i < 384 → ch_62 i = true := block_join nj_62_10 (fun _ h1 h2 => treeBlockF_at nb_62_11 h1 h2)
theorem nj_62_12 : ∀ i, 0 ≤ i → i < 416 → ch_62 i = true := block_join nj_62_11 (fun _ h1 h2 => treeBlockF_at nb_62_12 h1 h2)
theorem nj_62_13 : ∀ i, 0 ≤ i → i < 448 → ch_62 i = true := block_join nj_62_12 (fun _ h1 h2 => treeBlockF_at nb_62_13 h1 h2)
theorem nj_62_14 : ∀ i, 0 ≤ i → i < 480 → ch_62 i = true := block_join nj_62_13 (fun _ h1 h2 => treeBlockF_at nb_62_14 h1 h2)
theorem nj_62_15 : ∀ i, 0 ≤ i → i < 512 → ch_62 i = true := block_join nj_62_14 (fun _ h1 h2 => treeBlockF_at nb_62_15 h1 h2)
theorem nj_62_16 : ∀ i, 0 ≤ i → i < 544 → ch_62 i = true := block_join nj_62_15 (fun _ h1 h2 => treeBlockF_at nb_62_16 h1 h2)
theorem nj_62_17 : ∀ i, 0 ≤ i → i < 576 → ch_62 i = true := block_join nj_62_16 (fun _ h1 h2 => treeBlockF_at nb_62_17 h1 h2)
theorem nj_62_18 : ∀ i, 0 ≤ i → i < 608 → ch_62 i = true := block_join nj_62_17 (fun _ h1 h2 => treeBlockF_at nb_62_18 h1 h2)
theorem nj_62_19 : ∀ i, 0 ≤ i → i < 640 → ch_62 i = true := block_join nj_62_18 (fun _ h1 h2 => treeBlockF_at nb_62_19 h1 h2)
theorem nj_62_20 : ∀ i, 0 ≤ i → i < 672 → ch_62 i = true := block_join nj_62_19 (fun _ h1 h2 => treeBlockF_at nb_62_20 h1 h2)
theorem nj_62_21 : ∀ i, 0 ≤ i → i < 704 → ch_62 i = true := block_join nj_62_20 (fun _ h1 h2 => treeBlockF_at nb_62_21 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 704 → ch_62 i = true := nj_62_21
theorem lb_62 : LowerBin fullMask rootStock g_62 12 :=
  lowerDagV5 (kn_cons lb_28 (kn_cons lb_48 (kn_cons lb_60 (kn_cons lb_58 (kn_cons lb_59 (kn_cons lb_57 (kn_cons lb_56 (kn_cons lb_55 (kn_cons lb_1 (kn_cons lb_32 (kn_cons lb_35 (kn_cons lb_51 (kn_cons lb_27 (kn_cons lb_49 (kn_cons lb_30 (kn_cons lb_61 (kn_cons lb_12 (kn_cons lb_13 (kn_cons lb_50 (kn_cons lb_42 (kn_cons lb_39 (kn_cons lb_41 (kn_cons lb_29 (kn_cons lb_0 (kn_cons lb_40 (kn_cons lb_38 (kn_cons lb_53 (kn_cons lb_34 (kn_cons lb_36 (kn_cons lb_6 (kn_cons lb_5 (kn_cons lb_52 (kn_nil))))))))))))))))))))))))))))))))) rc_62 nc_62 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [6, 14]⟩, ⟨GateOp.and, [5, 15]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3907053568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3907053568)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3907053568) = g_62 by decide]
  exact lb_62

end PEqualNP.Outside.L_meta_48569

theorem PEqualNP.Outside.L_meta_48569 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3907053568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3907053568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48569.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3907053568) 13 PEqualNP.Outside.L_meta_48569.root_lb PEqualNP.Outside.L_meta_48569.wg 18 rfl PEqualNP.Outside.L_meta_48569.wfits PEqualNP.Outside.L_meta_48569.weval
